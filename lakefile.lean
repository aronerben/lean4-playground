import Lake
open Lake DSL

package «algebra» {
  -- add package configuration options here
}

lean_lib «Algebra» {
  -- add library configuration options here
}

@[default_target]
lean_exe «algebra» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require aesop from git "https://github.com/JLimperg/aesop"
