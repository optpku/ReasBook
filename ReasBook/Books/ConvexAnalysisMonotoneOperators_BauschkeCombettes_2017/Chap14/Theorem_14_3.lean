/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: combine Proposition 14.1 with Example 13.6 and apply the reciprocal-parameter
-- form of Moreau regularization to `f*`.
/-- Theorem 14.3 (1): for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, equation `(14.3)` states that the
quadratic kernel `γ⁻¹ q` is the sum of the `γ`-Moreau envelope of `f` and the
`γ⁻¹`-Moreau envelope of `f*` composed with `γ⁻¹ Id`. -/
theorem moreauQuadraticKernel_eq_moreauEnvelope_add_conjugateMoreauEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    (moreauQuadraticKernel γ).asEReal =
      {}^[γ] f + ({}^[(γ⁻¹ : PosReal)] (f.asEReal∗)) ∘
        fun x ↦ (γ : ℝ)⁻¹ • x := sorry

-- Proof sketch: differentiate the identity from clause `(1)` with Proposition 12.30, then rewrite
-- the two gradients in terms of `Prox_{γ f}` and `Prox_{f^* / γ}`.
/-- Theorem 14.3 (2): Moreau's decomposition gives the operator identity
`Id = Prox_{γ f} + γ Prox_{f^* / γ} ∘ γ⁻¹ Id`. -/
theorem id_eq_scaledProximityOperator_add_scaledProximityOperator_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    id =
      Prox[γ, f, hf] +
        (γ : ℝ) •
          (Prox⋆[(γ⁻¹ : PosReal), f, hf] ∘
            fun x ↦ (γ : ℝ)⁻¹ • x) := sorry

-- Proof sketch: apply Proposition 12.26 to points `p` and `pStar` satisfying
-- `p = Prox_{γ f} x` and `pStar = Prox_{f^* / γ} (γ⁻¹ x)`, then use Fenchel--Young equality for
-- the pair `(p, pStar)`.
/-- Theorem 14.3 (3): if `p = Prox_{γ f} x` and `p* = Prox_{f^* / γ} (x / γ)`, then equation
`(14.4)` gives `f p + f^*(p*) = ⟪p, p*⟫`. -/
theorem proxValue_add_conjugateProxValue_eq_inner
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x p pStar : H)
    (hp : p = Prox[γ, f, hf] x)
    (hpStar : pStar = Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) :
    (f p : EReal) + f.asEReal∗ pStar =
      ((⟪p, pStar⟫_ℝ : ℝ) : EReal) := sorry

end MoreauDecomposition

end ERealFunction
