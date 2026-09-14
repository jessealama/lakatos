#!/usr/bin/env fish
# One line per thing worth knowing about the session epic's beads, most
# urgent first: who is waiting on a human, who is working, what is ready
# and unclaimed, what is blocked and by what, and whether the GitHub epic
# still has children to pour. The worker loops print this when idle; it is
# also the thing to run by hand (or from another agent) to see where the
# epic stands.
#
#   scripts/bd-status.fish [--epic ID] [--gh-epic N]

argparse 'epic=' 'gh-epic=' -- $argv
or exit 2

set -l root (path resolve (status dirname)/..)
set -l epic (set -q _flag_epic; and echo $_flag_epic; or echo lakatos-vvi)
set -l gh_epic (set -q _flag_gh_epic; and echo $_flag_gh_epic; or echo 376)
set -l repo lakatos-ts/lakatos

function describe --argument-names id
    bd show $id --json | jq -r '(.[0] // .) | "\(.labels // [] | join(",")) \(.external_ref // "-")"'
end

function minutes_since --argument-names ts
    set -l then (date -j -u -f '%Y-%m-%dT%H:%M:%SZ' $ts +%s 2>/dev/null)
    if test -z "$then"
        echo '?'
        return
    end
    math -s0 "("(date +%s)" - $then) / 60"
end

set -l human
set -l working
set -l ready
set -l blocked

# Open human gates. The blocked bead and the reason live in the description.
for g in (bd -C $root gate list --json | jq -c '(. // [])[] | select(.status != "closed")')
    set -l gid (echo $g | jq -r .id)
    set -l desc (echo $g | jq -r .description | string collect)
    set -l target (string match -r 'blocking (\S+)' -- $desc)[2]
    set -l reason (string match -r 'Reason: (.*)' -- $desc)[2]
    set -a human "waiting on human: $target ("(describe $target)") blocked by gate $gid. Resolve with: bd gate resolve $gid. Reason: $reason"
end

set -l ready_ids (bd -C $root ready --parent $epic --json | jq -r '.[].id')

for m in (bd -C $root list --parent $epic --json | jq -r '.[].id')
    for b in (bd -C $root list --parent $m --json | jq -c '.[]')
        set -l id (echo $b | jq -r .id)
        set -l st (echo $b | jq -r .status)
        set -l who (echo $b | jq -r '.assignee // "nobody"')
        set -l info (describe $id)
        switch $st
            case in_progress
                set -l started (echo $b | jq -r '.started_at // empty')
                set -l mins (test -n "$started"; and minutes_since $started; or echo '?')
                set -a working "working: $id ($info) claimed by $who, $mins min so far"
            case open blocked
                if contains -- $id $ready_ids
                    set -a ready "ready: $id ($info) is waiting for a free "(echo $info | string split ' ')[1]" loop"
                else
                    set -l by (bd -C $root show $id --json | jq -r '(.[0] // .) | .dependencies[] | select(.dependency_type == "blocks" or .issue_type == "gate") | select(.status != "closed") | "\(.id) [\(.status)]"' | string join ', ')
                    set -a blocked "blocked: $id ($info) waits on $by"
                end
        end
    end
end

set -l lines $human $working $ready $blocked

if test (count $lines) = 0
    set -l open_children (gh api repos/$repo/issues/$gh_epic/sub_issues --paginate --jq '[.[] | select(.state == "open")] | length')
    if test "$open_children" = 0
        set lines "epic complete: every child of #$gh_epic is closed; close $epic by hand"
    else
        set lines "nothing poured: every bead under $epic is closed and $open_children children of #$gh_epic are still open; run scripts/bd-pour-next.fish"
    end
end

printf '%s\n' $lines
