#!/usr/bin/env zsh
# Source this file from the KN-scratch directory (or from anywhere):
#
#   source ./generation-vars.zsh
#   lake build $GEN1
#   lake build $GEN2
#
# GEN1, ..., GEN14 are zsh arrays of Lean module names. GEN_ALL contains
# every generation in order. The arrays are read from GENERATIONS.md each
# time this file is sourced, so there is no second long file list to maintain.

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
  local line path module
  local -i generation=0

  if [[ ! -r $generation_file ]]; then
    print -u2 "Cannot read $generation_file"
    return 1
  fi

  typeset -ga GEN1 GEN2 GEN3 GEN4 GEN5 GEN6 GEN7
  typeset -ga GEN8 GEN9 GEN10 GEN11 GEN12 GEN13 GEN14 GEN_ALL
  GEN1=() GEN2=() GEN3=() GEN4=() GEN5=() GEN6=() GEN7=()
  GEN8=() GEN9=() GEN10=() GEN11=() GEN12=() GEN13=() GEN14=()

  while IFS= read -r line; do
    if [[ $line == '## Generation '<-> ]]; then
      generation=${line##* }
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

    module=${path%.lean}
    module=${module//\//.}
    case $generation in
      1)  GEN1+=("$module") ;;
      2)  GEN2+=("$module") ;;
      3)  GEN3+=("$module") ;;
      4)  GEN4+=("$module") ;;
      5)  GEN5+=("$module") ;;
      6)  GEN6+=("$module") ;;
      7)  GEN7+=("$module") ;;
      8)  GEN8+=("$module") ;;
      9)  GEN9+=("$module") ;;
      10) GEN10+=("$module") ;;
      11) GEN11+=("$module") ;;
      12) GEN12+=("$module") ;;
      13) GEN13+=("$module") ;;
      14) GEN14+=("$module") ;;
      *)
        print -u2 "Unsupported generation $generation in GENERATIONS.md"
        return 1
        ;;
    esac
  done < "$generation_file"

  GEN_ALL=(
    $GEN1 $GEN2 $GEN3 $GEN4 $GEN5 $GEN6 $GEN7
    $GEN8 $GEN9 $GEN10 $GEN11 $GEN12 $GEN13 $GEN14
  )

  if (( ${#GEN_ALL} == 0 )); then
    print -u2 'No Lean files were parsed from GENERATIONS.md'
    return 1
  fi
}

_p2m_load_generation_vars || return $?
unfunction _p2m_load_generation_vars
