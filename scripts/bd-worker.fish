#!/usr/bin/env fish
# One worker loop over the beads of an epic: claim the next ready bead whose
# label matches the role, run `claude -p` on the matching prompt, repeat.
#
#   scripts/bd-worker.fish plan      [--once] [--dry-run] [--poll SECONDS] [--model MODEL] [--epic ID]
#   scripts/bd-worker.fish review    [--once] [--dry-run] [--poll SECONDS] [--model MODEL] [--epic ID]
#   scripts/bd-worker.fish implement [--once] [--dry-run] [--poll SECONDS] [--model MODEL] [--epic ID]
#
# Run one review loop and one implement loop; run as many plan loops as the
# fan-out needs. Review is on the critical path (an implement closes and
# nothing moves until its review does), plans are prefetch, and implements
# are serialized so workers never share Lean files.
#
# The prompt for a bead is scripts/prompts/<label>.md with {{BEAD}} and
# {{ROOT}} substituted. Each run streams its full event log to
# .lakatos/workers/<bead>-<time>.jsonl (stderr beside it) and renders one
# terminal line per tool call and message through bd-worker-render.jq. The
# loop stops when the epic has no open beads left. While idle it prints
# scripts/bd-status.fish's account of why (a human gate, a worker on the
# other loop, an unclaimed bead) whenever that account changes. `bd` runs
# from the repo root, never from a worktree.
#
# A worker that exits with its bead still in progress has failed. What
# happens next depends on the label, and only this script decides it:
#   implement  -> one repair bead is created under the same molecule (label
#                 repair, discovered-from the implement bead, blocking it) and
#                 the loop goes on. An implement bead gets at most one repair
#                 bead, ever; a second failure escalates instead.
#   repair     -> the repair bead is closed as failed, the implement bead gets
#                 a human gate and the label needs-human, and the loop stops.
#   plan/review-> the bead is set back to open and the loop stops.
# Repair beads are never created by a worker, so a repair cannot beget a
# repair. Set BD_WORKER_CLAUDE to replace the claude command (tests).

argparse 'once' 'dry-run' 'poll=' 'model=' 'epic=' -- $argv
or exit 2

set -l role $argv[1]
set -l root (path resolve (status dirname)/..)
set -l epic (set -q _flag_epic; and echo $_flag_epic; or echo lakatos-vvi)
set -l poll (set -q _flag_poll; and echo $_flag_poll; or echo 120)

set -l default_model ''
set -l labels ''
switch "$role"
    case plan
        set default_model claude-fable-5-1
        set labels plan
    case review
        set default_model claude-fable-5-1
        set labels review
    case implement
        set default_model claude-opus-5
        set labels implement,repair
    case '*'
        echo "usage: bd-worker.fish plan|review|implement [--once] [--dry-run] [--poll SECONDS] [--model MODEL] [--epic ID]" >&2
        exit 2
end
set -l model (set -q _flag_model; and echo $_flag_model; or echo $default_model)

set -x BEADS_ACTOR "$role-worker"
mkdir -p $root/.lakatos/workers
set -l last_state ''

while true
    # `bd ready --label-any` does not filter (bd 1.2.2 returns unlabelled
    # beads too), so claim one label at a time with the AND filter.
    # `--claim` also skips a ready bead that still carries an assignee (a
    # bead a reviewer reopened keeps the old worker's name), so when the
    # claim finds nothing but a ready bead exists, clear its stale assignee
    # and claim again.
    set -l claimed ''
    for l in (string split , $labels)
        set claimed (bd -C $root ready --parent $epic --label $l --claim --json | jq -r '.[0].id // empty')
        if test -z "$claimed"
            set -l stale (bd -C $root ready --parent $epic --label $l --json | jq -r '.[0] | select(.assignee != null) | .id // empty')
            if test -n "$stale"
                bd -C $root update $stale --assignee "" -q
                set claimed (bd -C $root ready --parent $epic --label $l --claim --json | jq -r '.[0].id // empty')
            end
        end
        test -n "$claimed"; and break
    end

    if test -z "$claimed"
        # Steps live two levels down (epic -> molecule root -> steps), so count
        # the open steps under every molecule root rather than direct children.
        set -l open 0
        for mol in (bd -C $root list --parent $epic --json | jq -r '.[].id')
            set open (math $open + (bd -C $root list --parent $mol --status open,in_progress,blocked --json | jq 'length'))
        end
        if test "$open" = 0
            echo "[$role] nothing open under $epic; done"
            exit 0
        end
        # Say why nothing is ready, but only when the answer changes.
        set -l state (fish $root/scripts/bd-status.fish --epic $epic 2>&1 | string collect)
        # Elapsed minutes tick every poll; compare without them.
        set -l key (string replace -ra ', \d+ min so far' '' -- $state | string collect)
        if test "$key" != "$last_state"
            echo "[$role] "(date +%H:%M)" nothing ready for $labels:"
            printf '    %s\n' (string split \n -- $state)
            set last_state $key
        end
        if set -q _flag_once
            exit 0
        end
        sleep $poll
        continue
    end

    set last_state ''
    set -l label (bd -C $root show $claimed --json | jq -r '(.[0] // .) | .labels[]' | grep -E '^(plan|implement|review|repair)$' | head -1)
    set -l mol (bd -C $root show $claimed --json | jq -r '(.[0] // .) | .parent')
    set -l prompt_file $root/scripts/prompts/$label.md
    if not test -f $prompt_file
        echo "[$role] [$claimed] no prompt for label '$label'; unclaiming" >&2
        bd -C $root update $claimed --status open --assignee "" -q
        exit 1
    end

    set -l prompt (sed -e "s|{{BEAD}}|$claimed|g" -e "s|{{ROOT}}|$root|g" -e "s|{{EPIC}}|$epic|g" $prompt_file | string collect)
    set -l log $root/.lakatos/workers/$claimed-(date +%Y%m%dT%H%M%S).jsonl

    echo "[$role] [$claimed] ($label) -> $model, log $log"
    if set -q _flag_dry_run
        echo "--- would run: claude -p --model $model --dangerously-skip-permissions --output-format stream-json --verbose"
        echo "--- with prompt:"
        echo $prompt
        bd -C $root update $claimed --status open --assignee "" -q
        exit 0
    end

    # The full event stream goes to the .jsonl log as it happens; the
    # terminal gets one line per tool call, message, and the final result,
# each prefixed with the role and the bead.
    # stderr (MCP and hook noise) goes to a sibling .stderr file.
    set -l claude_cmd (set -q BD_WORKER_CLAUDE; and echo $BD_WORKER_CLAUDE; or echo claude)
    $claude_cmd -p --model $model --dangerously-skip-permissions --output-format stream-json --verbose $prompt 2>>$log.stderr \
        | tee $log | jq --unbuffered -R -r --arg prefix "[$role] [$claimed]" -f $root/scripts/bd-worker-render.jq
    set -l status_after (bd -C $root show $claimed --json | jq -r '(.[0] // .) | .status')

    if test "$status_after" = in_progress
        switch $label
            case implement
                set -l repairs (bd -C $root list --parent $mol --all --label repair --json | jq 'length')
                if test "$repairs" = 0
                    set -l title (bd -C $root show $claimed --json | jq -r '(.[0] // .) | .title')
                    set -l ref (bd -C $root show $claimed --json | jq -r '(.[0] // .) | .external_ref // empty')
                    set -l repair (bd -C $root create --parent $mol --labels repair --priority 2 --external-ref "$ref" \
                        --deps "discovered-from:$claimed" --title "Repair: $title" \
                        --description "The implement worker for $claimed stopped on a red gate; its last comment names the gate and the failure. Make the gates green on the branch and commit; do not open a PR." --json | jq -r '.id')
                    bd -C $root dep add $claimed --blocked-by $repair -q
                    bd -C $root update $claimed --status open --assignee "" -q
                    echo "[$role] [$claimed] failed; filed repair bead $repair, continuing"
                else
                    set -l gate (bd -C $root gate create --type human --blocks $claimed --reason "$claimed failed its gate again after a repair; needs the maintainer" --json | jq -r '.id // empty')
                    bd -C $root update $claimed --status open --assignee "" --add-label needs-human -q
                    echo "[$role] [$claimed] failed after a repair; human gate $gate added, stopping" >&2
                    exit 1
                end
            case repair
                set -l implement (bd -C $root list --parent $mol --label implement --json | jq -r '.[0].id')
                set -l why (bd -C $root comments $claimed --json 2>/dev/null | jq -r 'if type == "array" and length > 0 then .[-1].text else "no diagnosis left on the repair bead" end' | head -c 400 | string collect)
                bd -C $root close $claimed --reason "Repair failed; escalated to the maintainer" -q
                set -l gate (bd -C $root gate create --type human --blocks $implement --reason "Repair $claimed could not make the gate green: $why" --json | jq -r '.id // empty')
                bd -C $root update $implement --add-label needs-human -q
                echo "[$role] [$claimed] repair failed; human gate $gate on $implement, stopping" >&2
                exit 1
            case '*'
                echo "[$role] [$claimed] still in progress after the worker exited; set back to open, stopping" >&2
                bd -C $root update $claimed --status open --assignee "" -q
                exit 1
        end
    else
        echo "[$role] [$claimed] is now $status_after"
    end

    if set -q _flag_once
        exit 0
    end
end
