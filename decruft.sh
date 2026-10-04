#!/bin/zsh

# set counter
before=$(cat "${GEN_ALL[@]}" | wc -l)

# kill "focus dot then newline"
perl -0pi -e 's/^(\s*)·\n^\1  /$1· /mg' $GEN_ALL

# kill newlines within indented blocks
perl -0pi -e 's/^(\s+.*)\n+(\s+)/$1\n$2/mg' $GEN_ALL

# remove scope-final `variable`, `omit` etc
perl -0pi -e 's/^variable .*\n( .*\n)*\n*end/end/mg' $GEN_ALL
perl -0pi -e 's/^include .*\n( .*\n)*\n*end/end/mg' $GEN_ALL
perl -0pi -e 's/^open .*\n( .*\n)*\n*end/end/mg' $GEN_ALL
perl -0pi -e 's/^omit .*\n( .*\n)*\n*end/end/mg' $GEN_ALL
perl -0pi -e 's/^p2m_reactivate.*\n+(end.*\n)/$1/mg' $GEN_ALL
perl -0pi -e 's/^p2m_open.*\n+(end.*\n)/$1/mg' $GEN_ALL

# remove empty sections
perl -0pi -e 's/^(noncomputable )?section (.*)\n+end \2\n+//mg' $GEN_ALL
perl -0pi -e 's/^(noncomputable )?section\n+end\n+//mg' $GEN_ALL

# remove pointless setOption lines
perl -0pi -e 's/^set_option autoImplicit false\n+//mg' $GEN_ALL

# echo counter
after=$(cat "${GEN_ALL[@]}" | wc -l)
echo "Lines: $before -> $after (removed $((before - after)))"