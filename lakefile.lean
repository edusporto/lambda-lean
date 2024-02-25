import Lake
open Lake DSL

package «lambda» where
  -- add package configuration options here

lean_lib «Lambda» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «lambda» where
  root := `Main
