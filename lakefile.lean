import Lake
open Lake DSL

package «matroid» {
  -- add any package configuration options here
}

lean_lib «DMvPolynomial» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Matroid» {
  -- add any library configuration options here
}
