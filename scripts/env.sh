# source this before working with the OCaml spectec tools — shell-scoped only.
# Everything lives inside the repo: opam root at .opam/, switch at _opam/.
# (Pattern from ../cerberus-lean-proj/scripts/env.sh; machine-global state is
# forbidden — see CLAUDE.md.)

_repo="$(cd "$(dirname "${BASH_SOURCE:-${(%):-%x}}")/.." && pwd)"

export OPAMROOT="$_repo/.opam"
export OPAMSWITCH="$_repo"
export OPAMYES=1
eval "$(opam env --root="$OPAMROOT" --switch="$_repo" --set-root --set-switch 2>/dev/null)"

unset _repo
