/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_33

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section AttouchBrezisTheorem

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: this corollary is the textbook second-variable fiberwise infimal-convolution
  formula on the Hilbert product `H × K`, written with ordinary pair syntax.
- `core/canonical`: the owner abstractions are the Chapter 12 infimal postcomposition and
  infimal-convolution operators together with the Chapter 13 raw-product `ℓ²` Hilbert structure
  and the Chapter 15 Attouch--Brézis conjugation theorem.
- `bridge/view`: `WithLp 2 (H × K)` is only an internal model for the `ℓ²` product geometry, so
  the public statement should stay on raw pairs and let the local instances supply that geometry. -/

-- Proof sketch: write the function
-- `p ↦ ((z ↦ φ(x, z)) □ (z ↦ ψ(x, z))) y` with `p = (x, y)` in `H × K`
-- as the infimal postcomposition of the separable sum `(x, y₁, y₂) ↦ φ(x, y₁) + ψ(x, y₂)` along
-- `(x, y₁, y₂) ↦ (x, y₁ + y₂)`. Apply the Attouch--Brézis conjugation theorem on the product
-- Hilbert product `H × K` under the hypothesis
-- `0 ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))`, then evaluate the
-- resulting conjugate identity on slices with the second dual variable fixed.
/-- Corollary 15.8: if `φ, ψ ∈ Γ₀(H × K)` and
`0 ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))`, then the Fenchel
conjugate of the second-variable fiberwise infimal convolution
`p ↦ ((z ↦ φ(x, z)) □ (z ↦ ψ(x, z))) y`, where `p = (x, y)` in `H × K`,
is obtained by taking the infimal convolution in the first variable of the conjugate slices with
the second dual variable fixed. -/
theorem conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2)∗ =
      fun q : H × K ↦
        ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
          fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := sorry

/-- Evaluating Corollary 15.8 at `(x, y)` recovers the textbook raw-pair formula. -/
theorem
    conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices_apply
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)))
    (x : H) (y : K) :
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2)∗ (x, y) =
      ((fun u : H ↦ φ.asEReal∗ (u, y)) □
        fun u ↦ ψ.asEReal∗ (u, y)) x := by
  simpa using
    congrFun
      (conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices
        φ ψ hφ hψ hsri)
      (x, y)

end AttouchBrezisTheorem

end ERealFunction
