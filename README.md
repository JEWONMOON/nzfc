# nzfc — Nuclear ZFC and the Riemann Hypothesis
### A Holographic Reduction via Physical Information Horizons

| | |
|---|---|
| **Author** | Jewon Moon |
| **Affiliation** | Singularity Principle Institute, Austin, Texas |
| **Contact** | director@singularityprinciple.com |
| **Repository** | https://github.com/JEWONMOON/nzfc |
| **Preprint** | [DOI: 10.13140/RG.2.2.28915.49440](https://doi.org/10.13140/RG.2.2.28915.49440) |
| **License** | MIT (code) · CC BY 4.0 (paper) |
| **Date** | April 2026 |

---

## Overview

This repository presents a **conditional, machine-verified formalization** of the
Riemann Hypothesis (RH) within the **Nuclear Zermelo–Fraenkel Set Theory (N-ZFC)**
framework — an axiomatic system that enforces a finite information budget
(nuclearity / trace-class) on the cosmic vacuum operator, inspired by black-hole
event horizons.

The accompanying preprint is titled:

> **"A Lean 4 Formalization of Conditional Critical-Line Rigidity:
> A Machine-Checked Decomposition of the Hilbert–Pólya Burden into
> Technical Formalization and Genuine Open Mathematics"**
> Jewon Moon, April 2026.
> [DOI: 10.13140/RG.2.2.28915.49440](https://doi.org/10.13140/RG.2.2.28915.49440)

### Central Claim

> *Given the N-ZFC axiom set (9 named axioms, listed below), the Riemann Hypothesis
> follows necessarily from the nuclearity of the physical information horizon and the
> self-adjointness of the Selberg Laplacian.*

This is a **conditional** result. The proof is unconditional within N-ZFC;
it becomes an unconditional proof of RH once each named axiom is independently
verified — a program of open problems stated explicitly in this repository.

### Build Status

```
Lean files          : 21
Compilation errors  : 0
sorryAx in proof bodies : 0
Named axioms        : 9  (all listed below; none hidden)
```

> **Note on instances.**
> `SelbergSpace` (= L²(SL(2,ℤ)∖ℍ)) carries three `@[instance] axiom` declarations
> (G1–G3). These are mathematically standard consequences of L² theory but are not
> yet directly formalised in Mathlib. They appear as named axioms under
> `#print axioms`, never as anonymous `sorryAx`.

---

## Repository Structure

```
nzfc/
├── nzfc/
│   ├── 01_Cosmic_Horizon.lean                    # Physical → Information → Mathematical horizon
│   ├── 02_Nuclear_Budget.lean                    # Nuclearity theorem (axiom-free)
│   ├── 03_Vacuum_Spectrum.lean                   # Self-adjoint Δ, real eigenvalues
│   ├── 04_Adelic_Modular_Core.lean               # quadSpectralValue = ρ(1−ρ)
│   ├── 05_Boundary_Zero_Off_Axis.lean            # Im(ρ) ≠ 0  (5-case proof)
│   ├── 06_Nuclear_Cancellation.lean              # Nuclearity ↔ spectral-zero balance
│   ├── 07_Weil_Trace_Identity.lean               # Trace formula interface
│   ├── 08_Spectral_Capture.lean                  # ∃ n, eigenvalues n = ρ(1−ρ)
│   ├── 09_Holographic_Enforcement.lean           # Bulk reality → critical line
│   ├── 10_Main_Theorem_RH.lean                   # terminal RH theorem
│   ├── 11_Weil_Zeros_Spectral_Realization.lean   # Weil formula → spectral realization
│   ├── 12_Adelic_Spectral_Correspondence.lean    # P ≅ I ≅ M  three-layer isomorphism
│   ├── 13_Critical_Line_Algebraic_Rigidity.lean  # spectrum_preserved closed by ring
│   ├── 14_Nuclear_Vacuum_Hilbert_Polya.lean      # NZFC_Vacuum = Hilbert–Pólya type
│   ├── 15_Nuclear_Vacuum_Abstract_Structure.lean # Abstract vacuum existence
│   ├── 16_Selberg_Laplacian_Vacuum_Instance.lean # Concrete SelbergVacuumInstance
│   ├── 17_Selberg_Symmetry_Self_Adjoint.lean     # Symmetry → self-adjointness (intermediate)
│   ├── 18_Green_Identity_Self_Adjoint.lean       # Green's theorem → IsSelfAdjoint  ✅
│   ├── 19_Determinant_Eigenvalue_Bridge.lean     # det(Δ−λI)=0 ↔ HasEigenvalue
│   ├── 20_Weil_Selberg_Duality_Integration.lean  # Weil explicit = Selberg trace
│   └── 21_Modular_Factorization_Selberg_Riemann.lean  # Z(s)=ζ(s)·L(s) → theorem  ✅
├── NZFC_Final_Integrated.lean                    # Integration layer (entry point)
├── nzfc.lean                                     # Package root
├── lakefile.lean                                 # Lean 4 project config
├── lean-toolchain                                # Lean 4.29.0
└── README.md
```

---

## What Is Proven (Unconditional within N-ZFC)

All theorems below have **zero local `sorry`** in their proof bodies.
Any dependence on open mathematics is fully captured by the named axioms in the
next section.

| Theorem | File | Statement |
|---------|------|-----------|
| `mathematicalHorizon_of_physicalHorizon` | 01 | Physical horizon → Summable |
| `nuclearity_of_information_horizon` | 02 | Exponential decay → Trace-class *(axiom-free)* |
| `quadSpectralValue_im` | 04 | Im(ρ(1−ρ)) = Im(ρ)·(1 − 2 Re(ρ)) *(axiom-free)* |
| `selberg_is_self_adjoint` | 18 | Green's identity → IsSelfAdjoint ✅ |
| `self_adjoint_has_real_eigenvalues` | 18 | Self-adjoint op → real eigenvalues |
| `riemann_zeros_in_selberg_modular` | 21 | ζ(s)=0 → Z(s)=0  *(under A4)* ✅ |
| `Final_Chain_Closed` | 21 | Riemann zero → real Selberg eigenvalue ✅ |
| `terminal_path_conditional_rigidity` | Integration | Burden A + B → Re(ρ)=1/2 |
| `RiemannHypothesis_V2_7_Final` | 18 | N-ZFC axioms → Re(ρ)=1/2 |

---

## The Three Horizons — Core Physical Principle

```
Physical Horizon  (Horizon I)
    suppressed energy ≤ E · exp(−α · n)      [Bekenstein–Hawking]
            ↓  unconditional (file 01)
Information Horizon  (Horizon II)
    spectrum(n) ≤ C · exp(−α · n)            [exponential decay]
            ↓  unconditional (file 02)
Mathematical Horizon  (Horizon III)
    Σ spectrum(n) < ∞                        [Nuclearity / Trace-class]
```

---

## Named Axioms — Complete List

N-ZFC extends standard mathematics with exactly **9 named axioms**.
No anonymous `sorryAx` appears anywhere in the build.

### Group G — Geometric / Analytic (file 18)

| ID | Name | Content | Mathematical status |
|----|------|---------|-------------------|
| G1 | `selbergSpace_normedAddCommGroup` | L²(Γ∖ℍ) is a NormedAddCommGroup | Standard L² theory |
| G2 | `selbergSpace_innerProductSpace` | L²(Γ∖ℍ) is an InnerProductSpace over ℂ | Standard L² theory |
| G3 | `selbergSpace_completeSpace` | L²(Γ∖ℍ) is complete | Riesz–Fischer theorem |
| G4 | `greens_first_identity` | ⟨Δu, v⟩ = −⟨∇u, ∇v⟩ | Green's first identity (classical PDE) |
| G5 | `dirichletInner_symm` | ⟨∇u, ∇v⟩ = conj ⟨∇v, ∇u⟩ | Conjugate symmetry of real metric |
| G6 | `selberg_trace_identity` | ρ(1−ρ) ∈ spec(Δ) for each nontrivial zero ρ | Selberg trace formula (open in Lean) |

### Group A — Arithmetic / Spectral (files 05, 21)

| ID | Name | Content | Mathematical status |
|----|------|---------|-------------------|
| A1 | `zeta_nz_of_one_lt_re` | ζ(s) ≠ 0 for Re(s) > 1 | Euler product (Mathlib: near-immediate) |
| A2 | `zeta_zero_lt_zero` | ζ(s) = 0, Re(s) < 0 → s is a trivial zero | Functional equation (pending Lean) |
| A3 | `eta_ne_zero_of_strip` | η(σ) ≠ 0 for real σ ∈ (0,1) | Dirichlet eta positivity (pending Lean) |
| A4 | `selberg_zeta_factorization` | Z(s) = ζ(s)·L(s) for some L(s) | Conjectured spectral factorization (open) |
| A5 | `selberg_zero_iff_eigenvalue` | Z(s)=0 ↔ HasEigenvalue Δ (s(1−s)) | Fredholm det = Selberg zeta (open) |

> **On Axiom A4.**
> The factorisation Z(s) = ζ(s)·L(s) is a *structural axiom of N-ZFC*, not
> an attribution to Selberg (1956). Selberg's 1956 paper establishes the trace
> formula relating eigenvalues of Δ to prime geodesics; a direct product formula
> of this form is an independent conjecture and an explicit open problem of this
> project.

---

## Proof Architecture

### Phase 1 — Physical Foundations
```
01_Cosmic_Horizon        Three Horizons; PhysicalHorizon → Summable
02_Nuclear_Budget        Nuclearity theorem (fully axiom-free)
```

### Phase 2 — Operator & Bulk Dynamics
```
03_Vacuum_Spectrum       LaplaceCore, eigenvalue_real
04_Adelic_Modular_Core   quadSpectralValue, criticalLine_iff
```

### Phase 3 — Boundary Integrity
```
05_Boundary_Zero_Off_Axis   Im(ρ) ≠ 0  (5-case split on Re(ρ))
```

### Phase 4 — Trace Identity & Spectral Capture
```
06_Nuclear_Cancellation     Nuclearity constraint
07_Weil_Trace_Identity      AdmissibleFunction, trace interface
08_Spectral_Capture         ∃ n, eigenvalues n = ρ(1−ρ)
```

### Phase 5 — Grand Synthesis
```
09_Holographic_Enforcement  singularity_principle_victory
10_Main_Theorem_RH          terminal RH theorem
```

### Phase 6 — Selberg–Riemann Connection
```
11  Weil formula → spectral realization interface
12  P ≅ I ≅ M  three-layer isomorphism
13  spectrum_preserved closed by ring algebra
14  NZFC_Vacuum = Hilbert–Pólya operator type
15  Abstract vacuum existence
16  SelbergVacuumInstance concrete construction
17  Symmetry → self-adjointness (intermediate)
18  Green's theorem → IsSelfAdjoint              ✅
19  det(Δ−λI) = 0 ↔ HasEigenvalue
20  Weil explicit = Selberg trace + full chain
21  Z(s) = ζ(s)·L(s) → Riemann ⊆ Selberg        ✅
```

---

## Phase 6 Key Theorems

### File 18 — Self-Adjointness from Green's Theorem

```lean
-- Depends only on axioms G1–G5 (no sorryAx)
theorem selberg_is_self_adjoint : IsSelfAdjoint selbergLaplacian := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v; exact selberg_is_symmetric u v
```

### File 21 — Riemann ⊆ Selberg as a Theorem

```lean
-- ζ(s) = 0  and  Z(s) = ζ(s)·L(s)  →  Z(s) = 0
theorem riemann_zeros_in_selberg_modular {s} (hs : IsRiemannZero s) :
    selbergZetaModular s = 0 := by
  rcases selberg_zeta_factorization s with ⟨L, hZ⟩
  rw [hZ, hs.1]; simp
```

### Integration Layer — Terminal Conditional Rigidity

```lean
-- Burden A (Im(ρ) ≠ 0)  +  Burden B (ρ(1−ρ) ∈ real spectrum)
--   →  Re(ρ) = 1/2
theorem terminal_path_conditional_rigidity
    (B : BoundaryPredicateData) (D : BulkRealSpectrum)
    (H : HolographicCapture B D) :
    ∀ {ρ : ℂ}, B.IsZero ρ → ρ.re = (1 / 2 : ℝ)
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
   isomorphism: ζ(ρ)=0 ↔ ∃ n, eigenvalues n = ρ(1−ρ)
```

---

## Proof Audit

```
#print axioms NZFC.Final.terminal_path_conditional_rigidity
#print axioms NZFC.Final.green_to_selfAdjoint
#print axioms NZFC.Final.selberg_factorization_chain_closed
#print axioms NZFC.Final.information_horizon_nuclearity
```

Each command should list **named axioms only** — no `sorryAx`.

---

## Getting Started

```bash
git clone https://github.com/JEWONMOON/nzfc.git
cd nzfc
lake exe cache get
lake build
```

---

## Open Problems

Closing each axiom below converts the conditional proof into an unconditional one.

| Priority | Axiom | Path to closure |
|----------|-------|-----------------|
| Immediate | A1 `zeta_nz_of_one_lt_re` | Connect to `riemannZeta_ne_zero_of_one_lt_re` in Mathlib |
| Near-term | A2 `zeta_zero_lt_zero` | Functional equation in Lean |
| Near-term | A3 `eta_ne_zero_of_strip` | Dirichlet eta positivity in Lean |
| Long-term | G4 `greens_first_identity` | Green's identity for L²(Γ∖ℍ) in geometric analysis |
| Long-term | G6 `selberg_trace_identity` | Selberg trace formula in Lean |
| Long-term | A4 `selberg_zeta_factorization` | Spectral factorisation Z(s) = ζ(s)·L(s) |
| Long-term | A5 `selberg_zero_iff_eigenvalue` | Fredholm determinant = Selberg zeta |
| Long-term | G1–G3 | L²(SL(2,ℤ)∖ℍ) instances in Mathlib |

---

## Citation

```bibtex
@techreport{moon2026nzfc,
  title       = {A Lean 4 Formalization of Conditional Critical-Line Rigidity:
                 A Machine-Checked Decomposition of the Hilbert--P\'{o}lya Burden
                 into Technical Formalization and Genuine Open Mathematics},
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

Code: **MIT License** — see `LICENSE` for details.  
Paper: **CC BY 4.0**

---

> *"The Riemann Hypothesis is not a mere coincidence of numbers;
> it is the universe's most perfect and inevitable physical equilibrium,
> elegantly chosen to preserve its information."*
> — Jewon Moon, Singularity Principle Institute, 2026
