import Lake
open Lake DSL

-- 패키지 이름은 식별자로 작성합니다.
-- 최신 Lake 버전에서는 'version'과 'keywords' 필드가 PackageConfig에서 제외되었습니다.
package nzfc where
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
