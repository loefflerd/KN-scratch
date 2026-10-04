#!/usr/bin/env zsh
# Source this file from the KN-scratch directory (or from anywhere):
#
#   source ./generation-vars.zsh
#   lake build $GEN1
#   lake build $GEN2
#
# GEN1, ..., GEN$n are zsh arrays of repository-relative Lean filenames, where
# GEN_COUNT is n. GEN_ALL contains every generation in order. The arrays are read from
# GENERATIONS.md each time this file is sourced, so there is no second long
# file list to maintain.

if [[ ${ZSH_EVAL_CONTEXT-} != *:file ]]; then
  print -u2 'generation-vars.zsh must be sourced, not executed.'
  print -u2 'Use: source ./generation-vars.zsh'
  exit 1
fi

function _p2m_load_generation_vars {
  emulate -L zsh
  setopt extendedglob

  local script_path=${${(%):-%N}:A}
  local generation_file=${script_path:h}/GENERATIONS.md
  local line path variable
  local -i generation=0
  local -i index

  if [[ ! -r $generation_file ]]; then
    print -u2 "Cannot read $generation_file"
    return 1
  fi

  # Clear arrays left by an earlier sourcing, including generations which may
  # no longer occur after the dependency graph is regenerated.
  for variable in ${(k)parameters}; do
    [[ $variable == GEN<-> ]] && unset "$variable"
  done
  typeset -gi GEN_COUNT=0
  typeset -ga GEN_ALL
  GEN_ALL=()

  while IFS= read -r line; do
    if [[ $line == '## Generation '<-> ]]; then
      generation=${line##* }
      variable=GEN$generation
      typeset -ga "$variable"
      set -A "$variable"
      (( generation > GEN_COUNT )) && GEN_COUNT=$generation
      continue
    fi

    # File entries in GENERATIONS.md have the form: - `path/to/File.lean`
    if (( generation == 0 )) || [[ $line != '- `'*'.lean`' ]]; then
      continue
    fi
    path=${line#'- `'}
    path=${path%'`'}

    if [[ ! -f ${generation_file:h}/$path ]]; then
      print -u2 "Generation list names a missing file: $path"
      return 1
    fi

    variable=GEN$generation
    set -A "$variable" "${(@P)variable}" "$path"
  done < "$generation_file"

  for (( index = 1; index <= GEN_COUNT; ++index )); do
    variable=GEN$index
    GEN_ALL+=("${(@P)variable}")
  done

  if (( ${#GEN_ALL} == 0 )); then
    print -u2 'No Lean files were parsed from GENERATIONS.md'
    return 1
  fi
}

_p2m_load_generation_vars || return $?
unfunction _p2m_load_generation_vars
