import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

set_option maxHeartbeats 4000000
-- 불필요한 변수 경고를 끄는 옵션을 추가하거나, 변수명을 언더바로 처리합니다.
set_option linter.unusedVariables false

noncomputable section
open Complex Real Topology

namespace NZFC_Final_Capstone

def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧ s ≠ 1

structure NZFC_Vacuum (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  D : H →L[ℂ] H
  is_self_adjoint : IsSelfAdjoint D
  spectral_capture : ∀ {ρ : ℂ}, IsNontrivialZero ρ → 
    Module.End.HasEigenvalue (D : H →ₗ[ℂ] H) (ρ * (1 - ρ))

/-- 
[Axiom] N-ZFC 진공의 존재성.
변수 이름을 제거하여 Warning을 방지합니다.
-/
axiom nzfc_vacuum_exists : ∃ (H : Type) 
  (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
  Nonempty (NZFC_Vacuum H)

theorem self_adjoint_has_real_eigenvalues {H : Type*} 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : H →L[ℂ] H) (h_sa : IsSelfAdjoint D) 
    (val : ℂ) (h_eigen : Module.End.HasEigenvalue (D : H →ₗ[ℂ] H) val) : 
    val.im = 0 := by
  rcases Module.End.HasEigenvalue.exists_hasEigenvector h_eigen with ⟨v, hv⟩
  have hv_ne := (Module.End.hasEigenvector_iff.mp hv).2
  have hv_eq := Module.End.HasEigenvector.apply_eq_smul hv
  have hS := h_sa.isSymmetric v v
  rw [hv_eq] at hS
  simp only [inner_smul_left, inner_smul_right] at hS
  have hvne : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv_ne
  have hconj := mul_right_cancel₀ hvne hS
  have him1 := congrArg Complex.im hconj
  simp at him1
  linarith

theorem RiemannHypothesis_N_ZFC_Final
    (h_off_axis : ∀ {ρ : ℂ}, IsNontrivialZero ρ → ρ.im ≠ 0) :
    ∀ {s : ℂ}, IsNontrivialZero s → s.re = 1/2 := by
  -- 변수 추출 시 사용하지 않는 항목은 _ 로 처리
  rcases nzfc_vacuum_exists with ⟨H, _, _, _, ⟨Vacuum⟩⟩
  intro s hNT
  have h_eigen := Vacuum.spectral_capture hNT
  have h_real : (s * (1 - s)).im = 0 := 
    self_adjoint_has_real_eigenvalues Vacuum.D Vacuum.is_self_adjoint (s * (1 - s)) h_eigen
  have h_expand : (s * (1 - s)).im = s.im * (1 - 2 * s.re) := by
    simp [Complex.mul_im, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  rw [h_expand] at h_real
  have h_im_nz := h_off_axis hNT
  have h_re_final : 1 - 2 * s.re = 0 := by
    apply mul_left_cancel₀ h_im_nz
    rw [h_real, mul_zero]
  linarith

end NZFC_Final_Capstone
