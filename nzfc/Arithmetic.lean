import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace NZFC.Arithmetic

/-!
  # 🌌 N-ZFC Arithmetic: 최종 정화 완료 (Axiom-Zero)
  
  정화 결과:
  1. [Axiom 제거] 모든 근원(rad) 관련 공리를 Mathlib 정리로 대체 완료.
  2. [Linter 해결] 불필요한 simp 인자(prod_congr) 제거.
  3. [정직한 격리] FLT의 본체만 sorry로 남겨둔 무결성 상태.
-/

noncomputable def rad (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 
  else n.factorization.support.prod id

theorem rad_pos {n : ℕ} (h : 0 < n) : 0 < rad n := by
  unfold rad
  split_ifs with h0
  · exact absurd h (h0 ▸ Nat.lt_irrefl 0)
  · apply Finset.prod_pos
    intro p hp
    have hp' : p ∈ n.primeFactors := by rwa [← Nat.support_factorization]
    exact (Nat.prime_of_mem_primeFactors hp').pos

theorem rad_le (n : ℕ) (h : 0 < n) : rad n ≤ n := by
  unfold rad
  split_ifs with h0
  · omega
  · -- linter 반영: id_eq만으로 충분합니다.
    have heq : n.factorization.support.prod id = ∏ p ∈ n.primeFactors, p := by
      rw [Nat.support_factorization]
      simp only [id_eq]
    rw [heq]
    exact Nat.le_of_dvd h (Nat.prod_primeFactors_dvd n)

structure FermatsSpace where
  x : ℕ
  y : ℕ
  z : ℕ
  n : ℕ
  hn : 3 ≤ n
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  h_eq : x^n + y^n = z^n

theorem fermats_last_theorem : IsEmpty FermatsSpace := by
  sorry

end NZFC.Arithmetic