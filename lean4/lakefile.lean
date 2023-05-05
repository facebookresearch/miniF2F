import Lake
open Lake DSL

package «miniF2F» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MiniF2F» {
  -- add any library configuration options here
}
