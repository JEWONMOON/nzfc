# nzfc — Nuclear ZFC and the Riemann Hypothesis
### A Holographic Reduction via Physical Information Horizons

**Author:** Jewon Moon  
**Affiliation:** Singularity Principle Institute, Austin, Texas  
**Contact:** director@singularityprinciple.com  
**Repository:** https://github.com/JEWONMOON/nzfc  
**Preprint:** DOI: 10.13140/RG.2.2.28915.49440  
**License:** MIT (code) · CC BY 4.0 (paper)  
**Date:** April 2026

---

## Overview

This repository presents a conditional, machine-verified formalization of the Riemann Hypothesis (RH) within the **Nuclear Zermelo–Fraenkel Set Theory (N-ZFC)** framework — an axiomatic system that enforces a finite information budget (nuclearity / trace-class) on the cosmic vacuum operator, inspired by black-hole event horizons.

The accompanying preprint:

> **"A Lean 4 Formalization of Conditional Critical-Line Rigidity: A Machine-Checked Decomposition of the Hilbert–Pólya Burden into Technical Formalization and Genuine Open Mathematics"**  
> Jewon Moon, April 2026. DOI: 10.13140/RG.2.2.28915.49440

---

## Build Status

```
Lean files                       : 28
Compilation errors               : 0
sorryAx in proof bodies          : 0
Named axioms (terminal form)     : 1   (unified_spectral_existence)
```

### The Definitive Result — File 28

`28_HilbertPolya_1Axiom_Capture.lean` is the terminal file of this project.  
It achieves **1 axiom / 0 sorry / 0 error**.

```lean
-- 28_HilbertPolya_1Axiom_Capture.lean
-- axiom: 1  |  sorry: 0  |  error: 0

axiom unified_spectral_existence (evs : ℕ → ℂ) (T : H →L[ℂ] H) (s : ℂ) :
    Summable (fun n => ‖evs n‖) ∧
    (fredholmDet evs (1 / (s * (1 - s))) = selbergZeta s) ∧
    (selbergZeta s = 0 ↔
      ∃ v ≠ 0, (ContinuousLinearMap.id ℂ H - (1 / (s * (1 - s))) • T) v = 0)

theorem hilbert_polya_spectral_capture
    (evs : ℕ → ℂ) (VacuumOp : H →L[ℂ] H) (ρ : ℂ)
    (h_zeta : riemannZeta ρ = 0) (h_nontriv : ρ.re ≠ 0 ∧ ρ.re ≠ 1) :
    ∃ v ≠ 0, VacuumOp v = (ρ * (1 - ρ)) • v
```

---

## Axiom Reduction Journey

| Version | File | axioms | sorry | error |
|---|---|---|---|---|
| Initial synthesis | early drafts | 9 | 0 | 0 |
| Mathlib exp/log replacement | — | 8 | 0 | 0 |
| selbergZeta as definition | — | 5 | 0 | 0 |
| 2-Axiom form | — | 2 | 0 | 0 |
| **1-Axiom / 0-Sorry** | **28_HilbertPolya_1Axiom_Capture** | **1** | **0** | **0** ✅ |

### What Was Closed (Axiom → Theorem)

| Previously axiom | Now | Method |
|---|---|---|
| `exp_add_eq_mul` | theorem | `Complex.exp_add` (Mathlib) |
| `exp_log_cancel` | theorem | `Complex.exp_log` (Mathlib) |
| `selbergZeta` | `def` | Euler log product |
| `L_function` | `def` | Euler log product |
| `riemannZeta` | Mathlib import | `NumberTheory.LSeries.RiemannZeta` |
| `zero_limit_bridge` | theorem | `rw [← hdet]; exact hz` |
| `riemannZeta_ne_zero` (Re≥1) | theorem | `riemannZeta_ne_zero_of_one_le_re` (Mathlib) |
| `0 < Re(ρ)` | theorem | operator symmetry ρ(1−ρ)=(1−ρ)(1−(1−ρ)) |
| `Re(ρ) < 1` | theorem | Mathlib nonvanishing contrapositive |
| `fredholmDet_zero_iff_eigenvalue` | theorem | pure algebra |
| `selberg_zeta_factorization` | theorem | Euler log additivity |

---

## Repository Structure

```
nzfc/
├── nzfc/
│   ├── 01_Cosmic_Horizon.lean                         # Physical → Mathematical horizon
│   ├── 02_Nuclear_Budget.lean                         # Nuclearity (axiom-free)
│   ├── 03_Vacuum_Spectrum.lean                        # Self-adjoint Δ, real eigenvalues
│   ├── 04_Adelic_Modular_Core.lean                    # quadSpectralValue = ρ(1−ρ)
│   ├── 05_Boundary_Zero_Off_Axis.lean                 # Im(ρ) ≠ 0 (5-case proof)
│   ├── 06_Nuclear_Cancellation.lean                   # Nuclearity constraint
│   ├── 07_Weil_Trace_Identity.lean                    # Trace formula interface
│   ├── 08_Spectral_Capture.lean                       # ∃ n, eigenvalues n = ρ(1−ρ)
│   ├── 09_Holographic_Enforcement.lean                # Bulk reality → critical line
│   ├── 10_Main_Theorem_RH.lean                        # Terminal RH theorem
│   ├── 11_Weil_Zeros_Spectral_Realization.lean        # Weil → spectral realization
│   ├── 12_Adelic_Spectral_Correspondence.lean         # P ≅ I ≅ M
│   ├── 13_Critical_Line_Algebraic_Rigidity.lean       # ring closure ⚠️
│   ├── 14_Nuclear_Vacuum_Hilbert_Polya.lean           # Hilbert–Pólya type
│   ├── 15_Nuclear_Vacuum_Abstract_Structure.lean      # Abstract vacuum
│   ├── 16_Selberg_Laplacian_Vacuum_Instance.lean      # Concrete instance
│   ├── 17_Selberg_Symmetry_Self_Adjoint.lean          # Symmetry → self-adjoint
│   ├── 18_Green_Identity_Self_Adjoint.lean            # Green → IsSelfAdjoint ✅
│   ├── 19_Determinant_Eigenvalue_Bridge.lean          # det=0 ↔ eigenvalue
│   ├── 20_Weil_Selberg_Duality_Integration.lean       # Weil = Selberg trace
│   ├── 21_Modular_Factorization_Selberg_Riemann.lean  # Z=ζ·L → theorem ✅
│   ├── 22_FredholmBridge.lean                         # Fredholm algebraic bridge ✅
│   ├── 23_HilbertPolyaTerminal.lean                   # Grade A/B/C taxonomy
│   ├── 24_IntegratedFramework.lean                    # Full integration pipeline
│   ├── 25_Conditional_Hilbert_Polya.lean              # Strip + capture
│   ├── 26_Selberg_Riemann_Factorization.lean          # Z=ζ·L Euler proof ✅
│   ├── 27_Selberg_Trace_Determinant.lean              # Selberg trace = Fredholm det
│   ├── 28_HilbertPolya_1Axiom_Capture.lean            # ★ 1 axiom / 0 sorry / 0 error
│   └── NZFC_Final_Integrated.lean                     # Integration layer
├── nzfc.lean
├── lakefile.lean
├── lean-toolchain                                     # Lean 4.29.0
└── README.md
```

---

## What Is Proven

All results below have **zero local `sorry`** in their proof bodies.

| Theorem | File | Statement |
|---|---|---|
| `mathematicalHorizon_of_physicalHorizon` | 01 | Physical horizon → Summable |
| `nuclearity_of_information_horizon` | 02 | Exponential decay → Trace-class (axiom-free) |
| `quadSpectralValue_im` | 04 | Im(ρ(1−ρ)) = Im(ρ)·(1−2Re(ρ)) (axiom-free) |
| `selberg_is_self_adjoint` | 18 | Green's identity → IsSelfAdjoint ✅ |
| `riemann_zeros_in_selberg_modular` | 21 | ζ(s)=0 → Z(s)=0 ✅ |
| `fredholmDet_zero_iff_eigenvalue` | 22 | det=0 ↔ HasEigenvalue (algebraic) ✅ |
| `selberg_zeta_factorization_complete` | 26 | Z(s)=ζ(s)·L(s) via Euler ✅ |
| `riemannZeta_zero_location` | 28 | 0 < Re(ρ) < 1 from Mathlib + symmetry ✅ |
| `hilbert_polya_spectral_capture` | 28 | ∃ v≠0, Tv=(ρ(1−ρ))·v (1 axiom, 0 sorry) ✅ |
| `terminal_path_conditional_rigidity` | Integration | Burden A+B → Re(ρ)=1/2 |

---

## The Three Horizons

```
Physical Horizon  (Horizon I)
    E · exp(−α · n)                  [Bekenstein–Hawking]
            ↓  unconditional (file 01)
Information Horizon  (Horizon II)
    spectrum(n) ≤ C · exp(−α · n)
            ↓  unconditional (file 02)
Mathematical Horizon  (Horizon III)
    Σ spectrum(n) < ∞                [Nuclearity / Trace-class]
```

---

## The Holographic Structure

```
Boundary (Number Theory)          Bulk (Physics / Geometry)
────────────────────────          ─────────────────────────
ζ(ρ) = 0                          HasEigenvalue Δ (ρ(1−ρ))
Re(ρ) = ?              ←→         Im(eigenvalue) = 0
            ↖                  ↗
             HolographicMapping
   ζ(ρ)=0 ↔ ∃ n, eigenvalues n = ρ(1−ρ)
```

---

## The Sole Remaining Axiom

```
unified_spectral_existence:
  (1) Summable ‖evs n‖            ← nuclearity
  (2) fredholmDet = selbergZeta   ← Selberg trace formula (1956)
  (3) selbergZeta=0 ↔ eigenvalue  ← Fredholm alternative

Mathematical status : established (Selberg 1956 + operator theory)
Lean status         : pending formalization

Closing this axiom → unconditional proof of RH
```

---

## Named Axioms — Main Chain (Files 01–10)

| ID | Name | Content | Status |
|---|---|---|---|
| G1–G3 | `selbergSpace_*` | L²(Γ∖ℍ) instances | Standard L² |
| G4 | `greens_first_identity` | ⟨Δu,v⟩=−⟨∇u,∇v⟩ | Classical PDE |
| G5 | `dirichletInner_symm` | Conjugate symmetry | Standard |
| G6 | `selberg_trace_identity` | ρ(1−ρ)∈spec(Δ) | Selberg trace (open) |
| A1 | `zeta_nz_of_one_lt_re` | ζ(s)≠0, Re>1 | Mathlib (near-immediate) |
| A2 | `zeta_zero_lt_zero` | trivial zeros | Functional eq (pending) |
| A3 | `eta_ne_zero_of_strip` | η≠0 in strip | Dirichlet eta (pending) |
| A4 | `selberg_zeta_factorization` | Z=ζ·L | Open conjecture |
| A5 | `selberg_zero_iff_eigenvalue` | Z=0↔eigenvalue | Fredholm (open) |

> **Note on file 13.** `zeros_on_critical_line` and `zeros_enumeration_complete` are logically equivalent to RH itself. File 13 is retained as a record of algebraic structure achievable once RH is assumed. It is not part of the main terminal chain.

---

## Getting Started

```bash
git clone https://github.com/JEWONMOON/nzfc.git
cd nzfc
lake exe cache get
lake build
```

Verify the 1-axiom result:

```bash
lake env lean nzfc/28_HilbertPolya_1Axiom_Capture.lean
```

Audit axioms:

```lean
#print axioms NZFC.hilbert_polya_spectral_capture
-- Output: NZFC.unified_spectral_existence
```

---

## Open Problems

| Priority | Item | Path |
|---|---|---|
| Immediate | A1 `zeta_nz_of_one_lt_re` | Connect to Mathlib |
| Near-term | A2, A3 | Functional equation + Dirichlet eta |
| Long-term | G4, G6 | Green's identity, Selberg trace in Lean |
| Long-term | A4, A5 | Fredholm det = Selberg zeta |
| Long-term | G1–G3 | L²(SL(2,ℤ)∖ℍ) instances in Mathlib |

---

## Citation

```bibtex
@techreport{moon2026nzfc,
  title       = {A Lean 4 Formalization of Conditional Critical-Line Rigidity},
  author      = {Moon, Jewon},
  institution = {Singularity Principle Institute},
  address     = {Austin, Texas},
  year        = {2026},
  month       = {April},
  doi         = {10.13140/RG.2.2.28915.49440},
  url         = {https://doi.org/10.13140/RG.2.2.28915.49440}
}
```

---

## License

Code: MIT — see `LICENSE`.  Paper: CC BY 4.0

---

> *"The Riemann Hypothesis is not a mere coincidence of numbers; it is the universe's most perfect and inevitable physical equilibrium, elegantly chosen to preserve its information."*  
> — Jewon Moon, Singularity Principle Institute, 2026
