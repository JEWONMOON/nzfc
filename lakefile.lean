import Lake
open Lake DSL

package "nzfc" where
  -- 프로젝트 설정
  version := "0.1.0"
  keywords := #["math", "physics", "riemann-hypothesis", "nzfc"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- 유니코드 출력 활성화
    ⟨`pp.proofs.withType, false⟩
  ]

@[default_target]
lean_lib «Nzfc» where
  -- 소스 코드가 위치한 폴더 (보통 폴더명을 Nzfc로 하고 그 안에 01~10번 파일을 넣습니다)
  srcDir := "."
  globs := #[.submodules `Nzfc]

-- Mathlib 의존성 추가
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
