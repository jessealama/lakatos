#!/usr/bin/env fish
# Pour a planned-task molecule for every child of GitHub epic #376 that is
# open, labelled ready-for-agent, has no open GitHub blocker, and has no bead
# with external-ref gh-N yet. Each molecule is reparented under the session
# epic and every bead in it carries the gh-N ref.
#
#   scripts/bd-pour-next.fish [--dry-run] [--epic ID] [--gh-epic N]

argparse 'dry-run' 'epic=' 'gh-epic=' -- $argv
or exit 2

set -l root (path resolve (status dirname)/..)
set -l epic (set -q _flag_epic; and echo $_flag_epic; or echo lakatos-vvi)
set -l gh_epic (set -q _flag_gh_epic; and echo $_flag_gh_epic; or echo 376)
set -l repo jessealama/lakatos

set -l existing (bd -C $root list --all --json | jq -r '.[].external_ref // empty' | sort -u)
set -l poured 0

for n in (gh api repos/$repo/issues/$gh_epic/sub_issues --paginate --jq '.[] | select(.state == "open") | .number')
    set -l info (gh api repos/$repo/issues/$n --jq '[(.labels | map(.name) | index("ready-for-agent") != null), (.issue_dependencies_summary.blocked_by // 0), .title] | @tsv')
    set -l fields (string split \t -- $info)
    set -l ready $fields[1]
    set -l blocked $fields[2]
    set -l title $fields[3]

    if test "$ready" != true
        echo "#$n: not ready-for-agent, skipped"
        continue
    end
    if test "$blocked" != 0
        echo "#$n: $blocked open GitHub blocker(s), skipped"
        continue
    end
    if contains -- gh-$n $existing
        echo "#$n: already poured, skipped"
        continue
    end

    if set -q _flag_dry_run
        echo "#$n: would pour '$title'"
        continue
    end

    set -l out (bd -C $root mol pour planned-task --var "title=$title" --var "issue=$n" --json | string collect)
    set -l mol_root (echo $out | jq -r '.new_epic_id')
    if test -z "$mol_root" -o "$mol_root" = null
        echo "#$n: pour failed: $out" >&2
        exit 1
    end
    bd -C $root update $mol_root --parent $epic --external-ref gh-$n -q
    for id in (echo $out | jq -r '.id_mapping | to_entries[] | select(.key | contains(".")) | .value')
        bd -C $root update $id --external-ref gh-$n -q
    end
    echo "#$n: poured $mol_root ('$title')"
    set poured (math $poured + 1)
end

echo "poured $poured molecule(s) under $epic"
