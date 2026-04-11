import Lake
open Lake DSL

package nzfc where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

-- Mathlib 버전을 Lean 버전과 일치하도록 @ "v4.11.0"을 추가합니다.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib Nzfc where
  srcDir := "."
