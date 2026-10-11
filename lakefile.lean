import Lake
open Lake DSL

/-! Lean 4.33.0-rc2. Select this toolchain before building. -/

package pretriangulated_v2 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "639923353ff2a58e9976a254e0d40f4bebae36bc"

@[default_target]
lean_lib PretriangulatedV2
