#!/bin/zsh
# Apply exactly the substitutions in ../decruft.sh, in the same order.
# Edits files in place. Pass filenames as separate arguments, e.g.:
#   ./scripts/decruft.sh path/to/File.lean
#   ./scripts/decruft.sh $GEN_ALL

if (( $# == 0 )); then
  print -u2 'Usage: decruft.sh FILE [FILE ...] (edits in place)'
  exit 2
fi

typeset -a files
files=("$@")
for file in "${files[@]}"; do
  if [[ ! -f "$file" || ! -r "$file" || ! -w "$file" ]]; then
    print -u2 "Not a readable, writable file: $file"
    exit 1
  fi
done

# Count newline characters (for status message).
before=$(perl -ne '$count += tr/\n/\n/; END { print "$count\n" }' -- "${files[@]}") || exit

# Join a standalone focus dot to its tactic, allowing intervening blank lines.
perl -0pi -e 's/^([ \t]*)·[ \t]*\n(?:[ \t]*\n)*\1  /$1· /mg' -- "${files[@]}" || exit

# Collapse blank lines between indented lines; indentation excludes newlines.
perl -0pi -e 's/^([ \t]+.*)\n+([ \t]+)/$1\n$2/mg' -- "${files[@]}" || exit

# Remove scope-limited commands when they are at the end of their scope.
perl -0pi -e 's/^variable .*\n( .*\n)*\n*end/end/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^include .*\n( .*\n)*\n*end/end/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^open .*\n( .*\n)*\n*end/end/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^omit .*\n( .*\n)*\n*end/end/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^set_option .*\n+(end.*\n)/$1/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^p2m_reactivate.*\n+(end.*\n)/$1/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^p2m_open.*\n+(end.*\n)/$1/mg' -- "${files[@]}" || exit
perl -0pi -e 's/^universe .*\n+(end.*\n)/$1/mg' -- "${files[@]}" || exit

# Close up empty sections (named or unnamed)
perl -0pi -e 's/^(noncomputable )?section (.*)\n+end \2\n+//mg' -- "${files[@]}" || exit
perl -0pi -e 's/^(noncomputable )?section\n+end\n+//mg' -- "${files[@]}" || exit
perl -0pi -e 's/^namespace (.*)\n+end \1\n+//mg' -- "${files[@]}" || exit # dangerous



# Remove set_option lines which are on by default anyway
perl -0pi -e 's/^set_option autoImplicit false\n+//mg' -- "${files[@]}" || exit

# Print status message.
after=$(perl -ne '$count += tr/\n/\n/; END { print "$count\n" }' -- "${files[@]}") || exit
print "Lines: $before -> $after (removed $((before - after)))"
