#!/usr/bin/env bash
# Create a build-primed worktree lane under .claude/worktrees/<lane>
# (pattern: golean worktree-per-lane; cerberus new-worktree.sh).
#
#   scripts/new-worktree.sh <lane> [<base-ref>]
#
# - branch <lane> is created at <base-ref> (default: current HEAD) unless it
#   already exists, in which case it is checked out as-is.
# - worktrees live INSIDE the repo (sandbox path grants stop at the repo
#   folder; a worktree outside it would be unreadable).
# - untracked build state is SHARED from the primary checkout via symlinks:
#   deps/ (OCaml spectec checkout + mirrors, read-mostly), .opam/ and _opam/
#   (opam root + switch — shared: do not add/remove opam packages from a
#   lane). artifacts/ stays worktree-local (ci scratch must not collide).
# - .lake/ is copied (not symlinked) to prime the Lean build cache; lake
#   rebuilds anything stale. Concurrent capped builds: mind the cap budget
#   (SPECTEC_MEM_MAX) if running several heavy builds at once.
# - ONE WRITER PER WORKTREE. Landing goes through the merge protocol on the
#   primary checkout; prune retired lanes with:
#     git worktree remove .claude/worktrees/<lane>
set -euo pipefail
cd "$(dirname "$0")/.."
root=$(pwd -P)

lane=${1:?usage: scripts/new-worktree.sh <lane> [<base-ref>]}
base=${2:-HEAD}
dir=".claude/worktrees/$lane"

[ -e "$dir" ] && { echo "new-worktree: $dir already exists" >&2; exit 1; }
mkdir -p .claude/worktrees

if git show-ref --verify --quiet "refs/heads/$lane"; then
  git worktree add "$dir" "$lane"
else
  git worktree add -b "$lane" "$dir" "$base"
fi

for d in deps .opam _opam; do
  [ -e "$root/$d" ] && ln -s "$root/$d" "$dir/$d"
done
mkdir -p "$dir/artifacts"
if [ -d "$root/.lake" ]; then
  cp -a "$root/.lake" "$dir/.lake"
fi

echo "new-worktree: lane ready at $dir (branch $lane)"
echo "  cd $dir && source scripts/env.sh && scripts/capped lake build"
