/-
  NZFC_Final_Integrated.lean

  Final integration layer for the NZFC repository.

  Purpose:
  1. Re-export the unconditional horizon-to-nuclearity chain (Phase 1).
  2. Repackage Burden A (real-axis exclusion) as a boundary predicate.
  3. State the terminal-path conditional rigidity theorem in the exact one-way
     form actually needed for RH deduction:

         nonrealness of nontrivial zeros
         + spectral capture of ρ(1-ρ) into a real spectrum
         -> Re(ρ) = 1/2.

  4. Re-export the two Selberg-facing Phase-6 milestones currently used as the
     realization-program capstones:
       - Green's identity -> self-adjointness   (file 18)
       - Z(s)=ζ(s)*L(s) -> Riemann ⊆ Selberg    (file 21)

  Notes on imports:
  -----------------
  If your project layout is
      nzfc/01_Cosmic_Horizon.lean
      nzfc/02_Nuclear_Budget.lean
      ...
  then keep the `Nzfc.` prefix below.

  If your files live flat at the package root, simply drop the `Nzfc.` prefix.

  If your local files still carry upload-style names like
      01_Cosmic_Horizon.lean.lean
  rename them back to
      01_Cosmic_Horizon.lean
  before using this integration file.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

import Nzfc.«01_Cosmic_Horizon»
import Nzfc.«02_Nuclear_Budget»
import Nzfc.«04_Adelic_Modular_Core»
import Nzfc.«05_Boundary_Zero_Off_Axis»
import Nzfc.«08_Spectral_Capture»
import Nzfc.«10_Main_Theorem_RH»
import Nzfc.«18_Green_Identity_Self_Adjoint»
import Nzfc.«21_Modular_Factorization_Selberg_Riemann»

noncomputable section
open Complex Real Topology

namespace NZFC.Final

/-! ## Phase 1: unconditional horizon-to-nuclearity re-exports -/

/--
Physical horizon -> mathematical horizon -> summability.
This is the unconditional finite-capacity layer coming from file 01.
-/
theorem three_horizons_nuclearity
    (P : SingularityPrinciple.ThreeHorizons.PhysicalHorizon)
    (σ : ℕ → ℝ)
    (h_pos : ∀ n, 0 ≤ σ n)
    (h_bound : ∀ n,
      σ n ≤ SingularityPrinciple.ThreeHorizons.PhysicalHorizon.suppressedEnergy P n) :
    Summable σ := by
  simpa [SingularityPrinciple.ThreeHorizons.IsMathematicalHorizon] using
    SingularityPrinciple.ThreeHorizons.mathematicalHorizon_of_physicalHorizon
      P σ h_pos h_bound

/--
Information horizon -> trace class.
This is the axiom-free summability theorem from file 02.
-/
theorem information_horizon_nuclearity
    (σ : ℕ → ℝ)
    [SingularityPrinciple.Horizon.HasInformationHorizon σ]
    (h_pos : ∀ n, 0 ≤ σ n) :
    SingularityPrinciple.Horizon.IsTraceClass σ :=
  SingularityPrinciple.Horizon.nuclearity_of_information_horizon σ h_pos

/-! ## Burden A: real-axis exclusion packaged as a boundary predicate -/

/--
Predicate-based boundary data.
This is the right abstraction for the RH terminal path, because `riemannZeta = 0`
alone also contains the trivial zeros; what we actually need is the nontrivial-zero
predicate closed by file 05.
-/
structure BoundaryPredicateData where
  IsZero : ℂ → Prop
  zero_off_axis : ∀ {ρ : ℂ}, IsZero ρ → ρ.im ≠ 0

/-- Real spectrum data on the bulk side. -/
structure BulkRealSpectrum where
  eigenvalues : ℕ → ℝ

/--
One-way holographic capture.
This is the exact interface needed for the RH deduction:
if `ρ` is a boundary zero, then `ρ(1-ρ)` is captured by the real spectrum.
No reverse direction is required for the terminal rigidity theorem.
-/
structure HolographicCapture (B : BoundaryPredicateData) (D : BulkRealSpectrum) where
  capture : ∀ {ρ : ℂ}, B.IsZero ρ → ∃ n, (D.eigenvalues n : ℂ) = ρ * (1 - ρ)

/--
Burden A is closed by file 05:
nontrivial zeta zeros cannot lie on the real axis.
-/
def riemannBoundary : BoundaryPredicateData where
  IsZero := SingularityPrinciple.IsNontrivialZero
  zero_off_axis := by
    intro ρ hρ
    exact SingularityPrinciple.zero_off_axis_riemannZeta_Final hρ

/--
The quadratic spectral value identity re-exported from file 04.
-/
theorem quadSpectralValue_im
    (s : ℂ) :
    (AdelicModularWitness.quadSpectralValue s).im = s.im * (1 - 2 * s.re) :=
  AdelicModularWitness.quadSpectralValue_im s

/--
Terminal-path conditional rigidity in the precise one-way form actually needed.

Mechanism:
- self-adjoint / real bulk spectrum kills `Im(ρ(1-ρ))`
- Burden A kills the `Im(ρ)=0` leakage branch
- therefore `Re(ρ)=1/2` is forced.

This theorem is local-`sorry`-free. Any unresolved burden is explicit in the inputs:
`BoundaryPredicateData.zero_off_axis` and `HolographicCapture.capture`.
-/
theorem terminal_path_conditional_rigidity
    (B : BoundaryPredicateData)
    (D : BulkRealSpectrum)
    (H : HolographicCapture B D) :
    ∀ {ρ : ℂ}, B.IsZero ρ → ρ.re = (1 / 2 : ℝ) := by
  intro ρ hρ
  rcases H.capture hρ with ⟨n, h_spec⟩

  have h_real : (ρ * (1 - ρ)).im = 0 := by
    rw [← h_spec]
    simp

  have h_expand : (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
    simp [Complex.mul_im, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring

  rw [h_expand] at h_real
  have h_im_nz : ρ.im ≠ 0 := B.zero_off_axis hρ

  have h_mul : ρ.im * (1 - 2 * ρ.re) = ρ.im * 0 := by
    rw [mul_zero]
    exact h_real

  have h_re : 1 - 2 * ρ.re = 0 := by
    exact mul_left_cancel₀ h_im_nz h_mul

  linarith

/--
The RH terminal path specialized to the actual nontrivial-zero predicate from file 05.
This is the clean integration point for the 10-file architecture.

To use this theorem, it is enough to provide a capture theorem of the shape

  ∀ {ρ}, IsNontrivialZero ρ -> ∃ n, eigenvalues n = ρ(1-ρ).

That keeps Burden A and Burden B explicitly separated.
-/
theorem riemann_terminal_path_conditional_rigidity
    (D : BulkRealSpectrum)
    (h_capture : ∀ {ρ : ℂ}, SingularityPrinciple.IsNontrivialZero ρ →
      ∃ n, (D.eigenvalues n : ℂ) = ρ * (1 - ρ)) :
    ∀ {ρ : ℂ}, SingularityPrinciple.IsNontrivialZero ρ → ρ.re = (1 / 2 : ℝ) := by
  intro ρ hρ
  let H : HolographicCapture riemannBoundary D := {
    capture := by
      intro z hz
      exact h_capture hz
  }
  exact terminal_path_conditional_rigidity riemannBoundary D H hρ

/--
Adapter theorem: this is the exact bridge needed to feed file 08 into the
predicate-based terminal path above.

Because file 08 currently uses its own opaque set `NontrivialZeros`, one still needs
a set-identification bridge

  SingularityPrinciple.IsNontrivialZero ρ  <->  ρ ∈ nZFC_Weil_Trace.NontrivialZeros

and an identification between the complex `eigenvalues` used in file 08 and the real
spectrum sequence used in the terminal path. Once those are provided, the capture theorem
of file 08 drops directly into `riemann_terminal_path_conditional_rigidity`.
-/
theorem file08_capture_adapter
    (eigs : ℕ → ℂ)
    (W : nZFC_Weil_Trace.AdmissibleFunction → ℂ)
    (D : BulkRealSpectrum)
    (h_eigs : ∀ n, eigs n = (D.eigenvalues n : ℂ))
    (h_bridge : ∀ {ρ : ℂ},
      SingularityPrinciple.IsNontrivialZero ρ ↔ ρ ∈ nZFC_Weil_Trace.NontrivialZeros) :
    ∀ {ρ : ℂ}, SingularityPrinciple.IsNontrivialZero ρ →
      ∃ n, (D.eigenvalues n : ℂ) = ρ * (1 - ρ) := by
  intro ρ hρ
  have hρ' : ρ ∈ nZFC_Weil_Trace.NontrivialZeros := (h_bridge).mp hρ
  rcases nZFC_Weil_Trace.spectral_capture eigs W ρ hρ' with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← h_eigs n]
  exact hn

/-! ## Direct re-export of the generic terminal theorem from file 10 -/

/--
This is the original terminal theorem of file 10, re-exported under a stable name.
It is useful when one wants the two-way structure-field packaging of the terminal file.
-/
theorem terminal_file_synthesis
    (B : SingularityPrinciple.BoundaryData)
    (D : SingularityPrinciple.BulkData)
    (M : SingularityPrinciple.HolographicMapping B D) :
    ∀ {ρ : ℂ}, B.L_function ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
  SingularityPrinciple.singularity_principle_victory B D M

/-! ## Phase 6 re-exports: explicit realization-program milestones -/

/-- Green's identity -> self-adjointness (file 18). -/
theorem green_to_selfAdjoint :
    IsSelfAdjoint NZFC_V2_7_Green.selbergLaplacian :=
  NZFC_V2_7_Green.selberg_is_self_adjoint

/-- Riemann-zero inclusion into the modular Selberg zero set (file 21). -/
theorem riemann_in_selberg_modular
    {s : ℂ} (hs : NZFC_V3_5_Modular.IsRiemannZero s) :
    NZFC_V3_5_Modular.selbergZetaModular s = 0 :=
  NZFC_V3_5_Modular.riemann_zeros_in_selberg_modular hs

/--
File-21 capstone:
Riemann zero -> Selberg eigenvalue.
This is the modular-factorization side of the realization program.
-/
theorem selberg_factorization_chain_closed
    {ρ : ℂ} (hρ : NZFC_V3_5_Modular.IsRiemannZero ρ) :
    Module.End.HasEigenvalue
      (NZFC_V3_5_Modular.selbergLaplacian :
        NZFC_V3_5_Modular.SelbergSpace →ₗ[ℂ] NZFC_V3_5_Modular.SelbergSpace)
      (ρ * (1 - ρ)) :=
  NZFC_V3_5_Modular.Final_Chain_Closed hρ

/-! ## Optional audit commands

Uncomment these locally when you want an explicit kernel audit.
They should show named axioms only, not hidden theorem-body `sorryAx`,
for the theorems proved in this integration layer itself.

#print axioms NZFC.Final.three_horizons_nuclearity
#print axioms NZFC.Final.terminal_path_conditional_rigidity
#print axioms NZFC.Final.riemann_terminal_path_conditional_rigidity
#print axioms NZFC.Final.green_to_selfAdjoint
#print axioms NZFC.Final.selberg_factorization_chain_closed
-/

end NZFC.Final
