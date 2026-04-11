import Lake
open Lake DSL

-- 패키지 이름은 따옴표 없이 식별자로 작성해야 합니다.
package nzfc where
  version := "0.1.0"
  keywords := #["math", "physics", "riemann-hypothesis", "nzfc"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

-- Mathlib 의존성
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- 라이브러리 설정
@[default_target]
lean_lib Nzfc where
  srcDir := "."
