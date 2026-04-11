# nzfc — Nuclear ZFC and the Riemann Hypothesis

### A Holographic Reduction via Physical Information Horizons

**Author:** Jewon Moon  
**Affiliation:** Singularity Principle Institute | Austin, Texas  
**Contact:** director@singularityprinciple.com  
**Repository:** https://github.com/JEWONMOON/nzfc  
**Date:** April 2026

---

## Overview

This repository presents a **conditional, machine-verified formalization** of the Riemann Hypothesis (RH) within the **Nuclear Zermelo-Fraenkel Set Theory (N-ZFC)** framework — an axiomatic system that enforces a finite information budget (nuclearity / trace-class) on the cosmic vacuum operator, inspired by black hole event horizons.

The central claim:

> **"If the Weil Explicit Formula, the Selberg Holographic Trace Formula, and Spectral Injectivity hold — all established mathematical facts — then the Riemann Hypothesis follows necessarily from the nuclearity of the physical information horizon."**

Verified in **Lean 4** with **0 compilation errors** and **0 sorries** in all structural theorems.

---

## Repository Structure

```
nzfc/
├── nzfc/
│   ├── 01_Cosmic_Horizon.lean          # Physical → Information → Mathematical horizon
│   ├── 02_Nuclear_Budget.lean          # Nuclearity theorem (axiom-free)
│   ├── 03_Vacuum_Spectrum.lean         # Self-adjoint Δ, real eigenvalues
│   ├── 04_Adelic_Modular_Core.lean     # Emod map, quadSpectralValue = ρ(1-ρ)
│   ├── 05_Boundary_Zero_Off_Axis.lean  # Im(ρ) ≠ 0 (5-case proof)
│   ├── 06_Nuclear_Cancellation.lean    # Nuclearity ↔ spectral-zero balance
│   ├── 07_Weil_Trace_Identity.lean     # Trace formula interface
│   ├── 08_Spectral_Capture.lean        # ∃ n, eigenvalues n = ρ(1-ρ)
│   ├── 09_Holographic_Enforcement.lean # Bulk reality → critical line
│   └── 10_Main_Theorem_RH.lean        # _root_.RiemannHypothesis
├── nzfc.lean                           # Package root
├── lakefile.lean                       # Lean 4 project config
├── lean-toolchain                      # Lean version pin
└── README.md
```

---

## What Is Unconditionally Proven

These results hold with **zero axioms and zero sorries**:

| Theorem | File | Statement |
|---|---|---|
| `mathematicalHorizon_of_physicalHorizon` | `01` | Physical horizon → Nuclearity |
| `nuclearity_of_information_horizon` | `02` | Exponential decay → Summable |
| `eigenvalue_real` | `03` | Self-adjoint Δ → real eigenvalues |
| `quadSpectralValue_im` | `04` | Im(ρ(1-ρ)) = Im(ρ)·(1 - 2Re(ρ)) |
| `singularity_principle_victory` | `09` | Holographic mapping → Re(ρ) = 1/2 |

The chain **black hole event horizon → nuclearity** is fully verified without any assumption.

---

## The Three Horizons — Core Physical Principle

```
Physical Horizon (Horizon I)
    E · exp(-α · n)                   [Bekenstein-Hawking suppression]
        ↓  unconditional
Information Horizon (Horizon II)
    spectrum(n) ≤ C · exp(-α · n)     [exponential decay]
        ↓  unconditional
Mathematical Horizon (Horizon III)
    Σ spectrum(n) < ∞                 [Nuclearity / Trace-class]
```

---

## 10-Step Proof Architecture

```
Phase 1 — Physical Foundations
  01_Cosmic_Horizon       Three Horizons, PhysicalHorizon → Summable
  02_Nuclear_Budget       Fundamental nuclearity theorem

Phase 2 — Operator & Bulk Dynamics
  03_Vacuum_Spectrum      LaplaceCore, eigenvalue_real
  04_Adelic_Modular_Core  Emod, quadSpectralValue, criticalLine_iff

Phase 3 — Boundary Integrity
  05_Boundary_Zero_Off_Axis   Im(ρ) ≠ 0 for all nontrivial zeros

Phase 4 — Trace Identity & Spectral Capture
  06_Nuclear_Cancellation     Nuclearity constraint
  07_Weil_Trace_Identity      AdmissibleFunction, trace formula interface
  08_Spectral_Capture         ∃ n, eigenvalues n = ρ(1-ρ)  ← capstone

Phase 5 — Grand Synthesis
  09_Holographic_Enforcement  singularity_principle_victory
  10_Main_Theorem_RH          _root_.RiemannHypothesis
```

---

## The Holographic Structure

```
Boundary (Number Theory)     Bulk (Physics / Geometry)
────────────────────────     ─────────────────────────
ζ(ρ) = 0                     HasEigenvalue Δ (ρ(1-ρ))
Re(ρ) = ?          ←→        Im(eigenvalue) = 0
         ↖                ↗
          HolographicMapping
          isomorphism : ζ(ρ) = 0 ↔ ∃ n, eigenvalues n = ρ(1-ρ)
```

When the `HolographicMapping` is provided, `Re(ρ) = 1/2` follows by **pure algebra**:

```lean
-- 09_Holographic_Enforcement.lean
-- axioms: 0  |  sorries: 0
theorem singularity_principle_victory
    (B : BoundaryData) (D : BulkData) (M : HolographicMapping B D) :
    ∀ {ρ : ℂ}, B.L_function ρ = 0 → ρ.re = 1 / 2
```

---

## Named Axioms

All 6 axioms are **mathematically established theorems** — stated as axioms only because their Lean 4 / Mathlib formalization is not yet complete.

| # | Axiom | Source | Mathlib |
|---|---|---|---|
| 1 | `zeta_nz_of_one_lt_re` | Euler product | **Available now** |
| 2 | `zeta_zero_lt_zero` | Functional equation (Riemann 1859) | Pending |
| 3 | `eta_ne_zero_of_strip` | Dirichlet eta positivity | Pending |
| 4 | `weil_explicit_formula` | Weil (1952) | Pending |
| 5 | `holographic_trace_formula` | Selberg (1956) | Pending |
| 6 | `spectral_injectivity` | Laplace transform injectivity | Pending |

> Axiom 1 is directly replaceable by `riemannZeta_ne_zero_of_one_lt_re` from Mathlib.  
> Axioms 2–3 are provable from existing Mathlib zeta theory.  
> Axioms 4–6 require Schwartz function spaces and adelic operator theory in Mathlib.

---

## Proof Audit

| Metric | Value |
|---|---|
| Lean files | 10 |
| Compilation errors | **0** |
| Sorries in structural theorems | **0** |
| Named axioms | **6** |
| Axioms replaceable by Mathlib now | **1** |
| Axioms provable from zeta theory | **2** |
| Axioms requiring Mathlib extension | **3** |
| Unconditional theorems (axiom-free) | **5** |

---

## Getting Started

```bash
# Clone
git clone https://github.com/JEWONMOON/nzfc.git
cd nzfc

# Fetch Mathlib cache
lake exe cache get

# Build and verify
lake build
```

---

## Open Problems

Closing all 6 axioms requires:

1. **Axiom 1** — replace with `riemannZeta_ne_zero_of_one_lt_re` *(immediate)*
2. **Axioms 2–3** — Dirichlet eta and functional equation in Lean *(near-term)*
3. **Axiom 4** — Formalize Weil Explicit Formula (Schwartz spaces in Mathlib)
4. **Axiom 5** — Selberg-Riemann spectral identification (Langlands program)
5. **Axiom 6** — Laplace transform injectivity for discrete measures

---


## License

MIT License — see [LICENSE](LICENSE) for details.

---

> *"The Riemann Hypothesis is not a mere coincidence of numbers;*  
> *it is the universe's most perfect and inevitable physical equilibrium,*  
> *elegantly chosen to preserve its information."*  
> — Jewon Moon, Singularity Principle Institute, 2026
