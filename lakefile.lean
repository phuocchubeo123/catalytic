import Lake
open Lake DSL

package catalytic

-- Add mathlib as a dependency:
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- This folder defines a Lean library called MyCatLang
lean_lib Catalytic
