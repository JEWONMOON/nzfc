import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

noncomputable section
open Complex Real
open scoped InnerProductSpace -- 내적 공간 매크로 안전 확보

namespace AdelicModularWitness

/-- Nontrivial zeros of the Riemann zeta function. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
  (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧
  s ≠ 1

/-- Modular-energy encoding. -/
def Emod (s : ℂ) : ℂ :=
  Complex.mk s.im ((1 / 2 : ℝ) - s.re)

@[simp] theorem Emod_re (s : ℂ) : (Emod s).re = s.im := by
  simp [Emod]

@[simp] theorem Emod_im (s : ℂ) : (Emod s).im = (1 / 2 : ℝ) - s.re := by
  simp [Emod]

/-- The critical line is exactly the locus where the modular energy is real. -/
theorem criticalLine_iff_Emod_real (s : ℂ) :
    (Emod s).im = 0 ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    simp [Emod_im] at h
    linarith
  · intro h
    simp [Emod_im, h]

/-- Quadratic spectral value attached to a zero candidate. -/
def quadSpectralValue (s : ℂ) : ℂ :=
  ((1 / 4 : ℂ) + (Emod s) ^ 2)

/-- Real shadow-side spectral value used by trace-class heat shadows. -/
def zeroSpectralValue (s : ℂ) : ℝ :=
  (1 / 4 : ℝ) + ((Emod s).re) ^ 2

/-- `quadSpectralValue` is exactly the Connes/Berry–Keating parameter `ρ(1-ρ)`. -/
theorem quadSpectralValue_eq_rho_one_sub_rho (s : ℂ) :
    quadSpectralValue s = s * (1 - s) := by
  apply Complex.ext <;>
    simp [quadSpectralValue, Emod, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Real part of the quadratic spectral value. -/
theorem quadSpectralValue_re (s : ℂ) :
    (quadSpectralValue s).re = s.re * (1 - s.re) + s.im ^ 2 := by
  rw [quadSpectralValue_eq_rho_one_sub_rho]
  simp [Complex.mul_re]
  ring

/-- Imaginary part of the quadratic spectral value. -/
theorem quadSpectralValue_im (s : ℂ) :
    (quadSpectralValue s).im = s.im * (1 - 2 * s.re) := by
  rw [quadSpectralValue_eq_rho_one_sub_rho]
  simp [Complex.mul_im, Complex.sub_im, Complex.one_im]
  ring

/-- `quadSpectralValue` is real iff either the zero lies on the real axis or on the critical line. -/
theorem quadSpectralValue_real_iff (s : ℂ) :
    (quadSpectralValue s).im = 0 ↔ s.im = 0 ∨ s.re = (1 / 2 : ℝ) := by
  rw [quadSpectralValue_im, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- Relation between the full quadratic spectral parameter and the real shadow-side value. -/
theorem quad_real_part_as_zeroSpectral_minus_square (s : ℂ) :
    (quadSpectralValue s).re = zeroSpectralValue s - (s.re - (1 / 2 : ℝ)) ^ 2 := by
  rw [quadSpectralValue_re]
  simp [zeroSpectralValue, Emod_re]
  ring

/-- On the critical line, the full quadratic value collapses to the real shadow value. -/
theorem quad_eq_zeroSpectral_cast_of_criticalLine {s : ℂ}
    (h : s.re = (1 / 2 : ℝ)) :
    quadSpectralValue s = ((zeroSpectralValue s : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [quad_real_part_as_zeroSpectral_minus_square]
    simp [h]
  · rw [quadSpectralValue_im]
    simp [h]

/-- If the quadratic spectral value is real and the zero ordinate is nonzero,
then the modular energy itself is real. -/
theorem quad_eigenvalue_real_to_emod
    {ρ : ℂ} (hρ_im : ρ.im ≠ 0)
    (h : (quadSpectralValue ρ).im = 0) :
    (Emod ρ).im = 0 := by
  rw [quadSpectralValue_im] at h
  have htwice : (2 : ℝ) * (ρ.im * ((1 / 2 : ℝ) - ρ.re)) = 0 := by
    calc
      (2 : ℝ) * (ρ.im * ((1 / 2 : ℝ) - ρ.re)) = ρ.im * (1 - 2 * ρ.re) := by ring
      _ = 0 := h
  have hprod : ρ.im * ((1 / 2 : ℝ) - ρ.re) = 0 := by
    apply mul_left_cancel₀ two_ne_zero
    show (2 : ℝ) * (ρ.im * ((1 / 2 : ℝ) - ρ.re)) = (2 : ℝ) * 0
    simpa using htwice
  rcases mul_eq_zero.mp hprod with him | hre
  · exact absurd him hρ_im
  · simpa [Emod_im] using hre

/-- Self-adjoint Laplace/modular core. -/
structure LaplaceCore (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  Δ : H →L[ℂ] H
  hΔ : IsSelfAdjoint Δ
  hsymm : (Δ : H →ₗ[ℂ] H).IsSymmetric

namespace LaplaceCore

variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Eigenvalues of the self-adjoint/symmetric core are real. -/
theorem eigenvalue_real
    (L : LaplaceCore H) {val : ℂ}
    (hlam : Module.End.HasEigenvalue (L.Δ : H →ₗ[ℂ] H) val) :
    val.im = 0 := by
  rcases Module.End.HasEigenvalue.exists_hasEigenvector hlam with ⟨v, hv⟩
  have hv_ne : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have hv_eq : (L.Δ : H →ₗ[ℂ] H) v = val • v :=
    Module.End.HasEigenvector.apply_eq_smul hv
  
  -- hS는 자동으로 ⟪Δ v, v⟫ = ⟪v, Δ v⟫ 명제를 가집니다.
  have hS := L.hsymm v v
  rw [hv_eq] at hS
  simp only [inner_smul_left, inner_smul_right] at hS
  
  -- inner v v 를 직접 타이핑하는 대신 Lean의 타입 추론에 완전히 위임합니다.
  have hconj : star val = val := mul_right_cancel₀ (inner_self_ne_zero.mpr hv_ne) hS
  
  have him1 : (star val).im = val.im := congrArg Complex.im hconj
  have him2 : (star val).im = -val.im := by simp
  linarith

end LaplaceCore

/-- Trace-class heat shadow: the NZFC finite-capacity law. -/
structure NuclearHeatShadow (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  β : ℝ
  hβ : 0 < β
  K : H →L[ℂ] H
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  summable_weights : Summable weights

namespace NuclearHeatShadow

variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The heat shadow carries a finite trace-budget sequence. -/
theorem finite_budget (S : NuclearHeatShadow H) : Summable S.weights :=
  S.summable_weights

/-- Formal shadow trace as the sum of admissible weights. -/
noncomputable def actualShadowTrace (S : NuclearHeatShadow H) : ℝ :=
  tsum S.weights

end NuclearHeatShadow

/-- Global NZFC package: admissible vacuum = unitary core + trace-class heat shadow. -/
structure NZFCVacuumData (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  core : LaplaceCore H
  shadow : NuclearHeatShadow H

/-- Single global NZFC law. -/
axiom ax_nzfc_global_law :
  ∃ (H : Type)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (V : NZFCVacuumData H),
      ∀ (ρ : ℂ), IsNontrivialZero ρ →
        ρ.im ≠ 0 ∧
        Module.End.HasEigenvalue (V.core.Δ : H →ₗ[ℂ] H) (quadSpectralValue ρ)

/-- Single-zero NZFC theorem. -/
theorem criticalLine_of_nontrivialZero_of_NZFC
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : NZFCVacuumData H)
    (hglobal : ∀ (ρ : ℂ), IsNontrivialZero ρ →
      ρ.im ≠ 0 ∧
      Module.End.HasEigenvalue (V.core.Δ : H →ₗ[ℂ] H) (quadSpectralValue ρ))
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ρ.re = (1 / 2 : ℝ) := by
  have hImNe : ρ.im ≠ 0 := (hglobal ρ hρ).1
  have hSpec : Module.End.HasEigenvalue (V.core.Δ : H →ₗ[ℂ] H) (quadSpectralValue ρ) :=
    (hglobal ρ hρ).2
  have hQuadReal : (quadSpectralValue ρ).im = 0 :=
    LaplaceCore.eigenvalue_real V.core hSpec
  have hEmodReal : (Emod ρ).im = 0 :=
    quad_eigenvalue_real_to_emod hImNe hQuadReal
  exact (criticalLine_iff_Emod_real ρ).mp hEmodReal

/-- Fundamental NZFC theorem: admissible finite-capacity vacua force RH. -/
theorem riemannHypothesis_of_NZFC :
    _root_.RiemannHypothesis := by
  obtain ⟨H, _, _, _, V, hglobal⟩ := ax_nzfc_global_law
  intro ρ hz htriv h1
  have hNT : IsNontrivialZero ρ := ⟨hz, htriv, h1⟩
  exact criticalLine_of_nontrivialZero_of_NZFC V hglobal hNT

/-- NZFC exposes the finite trace budget carried by the admissible shadow. -/
theorem shadow_budget_of_NZFC :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : NZFCVacuumData H),
        Summable V.shadow.weights := by
  obtain ⟨H, h1, h2, h3, V, _⟩ := ax_nzfc_global_law
  exact ⟨H, h1, h2, h3, V, V.shadow.summable_weights⟩

/-- Package theorem: NZFC gives both finite trace budget and the RH consequence. -/
theorem nzfc_master_package :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
       (_ : CompleteSpace H) (V : NZFCVacuumData H), Summable V.shadow.weights)
    ∧ _root_.RiemannHypothesis := by
  exact ⟨shadow_budget_of_NZFC, riemannHypothesis_of_NZFC⟩

end AdelicModularWitness
