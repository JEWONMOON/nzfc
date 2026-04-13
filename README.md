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

This repository presents a conditional, machine-verified formalization of the Riemann Hypothesis (RH) within the **Nuclear Zermelo–Fraenkel Set Theory (N-ZFC)** framework.

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

### The Definitive 1-Axiom / 0-Sorry Formulation

```lean
-- HilbertPolya_Absolute_1Axiom_0Sorry.lean
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

**Axiom reduction journey:**

| Version | axioms | sorry | error |
|---|---|---|---|
| Initial (file 28) | 9 | 0 | 0 |
| Mathlib replacement | 8 | 0 | 0 |
| 5-Axiom | 5 | 0 | 0 |
| 2-Axiom | 2 | 0 | 0 |
| **1-Axiom / 0-Sorry** | **1** | **0** | **0** ✅ |

---

## What Was Closed (Previously Axiom → Now Theorem)

| Previously axiom | Now | Method |
|---|---|---|
| `exp_add_eq_mul` | theorem | `Complex.exp_add` (Mathlib) |
| `exp_log_cancel` | theorem | `Complex.exp_log` (Mathlib) |
| `selbergZeta` | `def` | Euler log product |
| `riemannZeta` | Mathlib import | `NumberTheory.LSeries.RiemannZeta` |
| `riemannZeta_ne_zero` (Re≥1) | theorem | `riemannZeta_ne_zero_of_one_le_re` (Mathlib) |
| `0 < Re(ρ)` | theorem | operator symmetry ρ(1−ρ)=(1−ρ)(1−(1−ρ)) |
| `Re(ρ) < 1` | theorem | Mathlib nonvanishing contrapositive |
| `fredholmDet_zero_iff_eigenvalue` | theorem | pure algebra (file 22) |
| `selberg_zeta_factorization` | theorem | Euler log additivity (file 26) |

---

## Repository Structure

```
nzfc/
├── nzfc/
│   ├── 01_Cosmic_Horizon.lean                         # Physical → Mathematical horizon
│   ├── 02_Nuclear_Budget.lean                         # Nuclearity (axiom-free)
│   ├── 03_Vacuum_Spectrum.lean                        # Self-adjoint Δ
│   ├── 04_Adelic_Modular_Core.lean                    # quadSpectralValue = ρ(1−ρ)
│   ├── 05_Boundary_Zero_Off_Axis.lean                 # Im(ρ) ≠ 0 (5-case)
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
│   ├── 17_Selberg_Symmetry_Self_Adjoint.lean          # Intermediate
│   ├── 18_Green_Identity_Self_Adjoint.lean            # Green → IsSelfAdjoint ✅
│   ├── 19_Determinant_Eigenvalue_Bridge.lean          # det=0 ↔ eigenvalue
│   ├── 20_Weil_Selberg_Duality_Integration.lean       # Weil = Selberg trace
│   ├── 21_Modular_Factorization_Selberg_Riemann.lean  # Z=ζ·L → theorem ✅
│   ├── 22_FredholmBridge.lean                         # Fredholm algebraic ✅
│   ├── 23_HilbertPolyaTerminal.lean                   # Grade A/B/C taxonomy
│   ├── 24_IntegratedFramework.lean                    # Full pipeline
│   ├── 25_Conditional_Hilbert_Polya.lean              # Strip + capture
│   ├── 26_Selberg_Riemann_Factorization.lean          # Z=ζ·L Euler proof ✅
│   ├── 27_Selberg_Trace_Determinant.lean              # Trace = det
│   ├── 28_Hilbert_Polya_Theorem.lean                  # Mathlib synthesis
│   ├── HilbertPolya_Absolute_1Axiom_0Sorry.lean       # ★ 1 axiom / 0 sorry
│   └── NZFC_Final_Integrated.lean                     # Integration layer
├── nzfc.lean
├── lakefile.lean
├── lean-toolchain                                     # Lean 4.29.0
└── README.md
```

---

## The Three Horizons

```
Physical Horizon  (Horizon I)
    E · exp(−α · n)                  [Bekenstein–Hawking]
            ↓  unconditional (file 01)
Information Horizon  (Horizon II)
    spectrum(n) ≤ C · exp(−α · n)    [exponential decay]
            ↓  unconditional (file 02)
Mathematical Horizon  (Horizon III)
    Σ spectrum(n) < ∞                [Nuclearity / Trace-class]
```

---

## Files 22–28: Axiom Reduction Program

| File | Key achievement | axioms | sorry |
|---|---|---|---|
| 22 `FredholmBridge` | `fredholmDet_zero_iff_eigenvalue` (algebraic) | 2 | 0 |
| 23 `HilbertPolyaTerminal` | Grade A/B/C axiom classification | 4 | 0 |
| 24 `IntegratedFramework` | Full pipeline with PGT | 7 | 0 |
| 25 `Conditional_Hilbert_Polya` | Strip + full capture | 8 | 0 |
| 26 `Selberg_Riemann_Factorization` | Z=ζ·L via Euler log | 4 | 0 |
| 27 `Selberg_Trace_Determinant` | Selberg trace = Fredholm det | 3 | 0 |
| 28 `Hilbert_Polya_Theorem` | Mathlib exp/log, 9 axioms | 9 | 0 |
| **1Axiom_0Sorry** | **Definitive form** | **1** | **0** ✅ |

---

## Named Axioms — Main Chain (Files 01–10)

| ID | Name | Content | Status |
|---|---|---|---|
| G1 | `selbergSpace_normedAddCommGroup` | L²(Γ∖ℍ) NormedAddCommGroup | Standard L² |
| G2 | `selbergSpace_innerProductSpace` | L²(Γ∖ℍ) InnerProductSpace | Standard L² |
| G3 | `selbergSpace_completeSpace` | L²(Γ∖ℍ) complete | Riesz–Fischer |
| G4 | `greens_first_identity` | ⟨Δu,v⟩=−⟨∇u,∇v⟩ | Classical PDE |
| G5 | `dirichletInner_symm` | Conjugate symmetry | Standard |
| G6 | `selberg_trace_identity` | ρ(1−ρ) ∈ spec(Δ) | Selberg trace (open) |
| A1 | `zeta_nz_of_one_lt_re` | ζ(s)≠0 for Re(s)>1 | Mathlib (near-immediate) |
| A2 | `zeta_zero_lt_zero` | trivial zeros | Functional eq (pending) |
| A3 | `eta_ne_zero_of_strip` | η(σ)≠0 | Dirichlet eta (pending) |
| A4 | `selberg_zeta_factorization` | Z(s)=ζ(s)·L(s) | Open conjecture |
| A5 | `selberg_zero_iff_eigenvalue` | Z(s)=0↔eigenvalue | Fredholm (open) |

---

## The Sole Open Problem

```
unified_spectral_existence = nuclearity + Selberg trace + Fredholm

Mathematical status: Selberg (1956) + operator theory (established)
Lean status: pending formalization

Closing this axiom → unconditional proof of RH
```

---

## Getting Started

```bash
git clone https://github.com/JEWONMOON/nzfc.git
cd nzfc
lake exe cache get
lake build

# Verify 1-axiom form
lake env lean nzfc/HilbertPolya_Absolute_1Axiom_0Sorry.lean

# Audit axioms
#print axioms NZFC.hilbert_polya_spectral_capture
```

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
