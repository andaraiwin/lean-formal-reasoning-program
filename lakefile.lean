import Lake
open Lake DSL

package «frap» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib «Frap» where
  -- add any library configuration options here
