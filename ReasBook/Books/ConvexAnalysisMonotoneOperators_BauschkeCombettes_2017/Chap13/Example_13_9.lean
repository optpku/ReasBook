/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] scalar_prod_pseudoMetricSpace_l2
attribute [local instance] scalar_prod_normedAddCommGroup_l2
attribute [local instance] scalar_prod_normedSpace_l2
attribute [local instance] scalar_prod_innerProductSpace_l2

/-- The set `C = {(μ, u) | μ + φ^*(u) ≤ 0}` appearing in the canonical conjugate of the
perspective of `φ`. -/
def perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) : Set (ℝ × H) :=
  {p | (p.1 : EReal) + (φ.asEReal∗ p.2) ≤ 0}

/- Membership in `perspectiveConjugateSet φ` is the scalar inequality
`μ + φ^*(u) ≤ 0`. -/
-- Proof sketch: unfold `perspectiveConjugateSet`.
@[simp] theorem mem_perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) {μ : ℝ} {u : H} :
    (μ, u) ∈ perspectiveConjugateSet φ ↔
      ((μ : EReal) + (φ.asEReal∗ u) ≤ 0) := sorry

/- Evaluating the canonical conjugate of the perspective on `ℝ × H` rewrites it as the supremum
of the affine functionals coming from the product pairing `(μ, u) · (ξ, x) = μξ + ⟪u, x⟫`. -/
@[simp] theorem conjugate_perspective_apply
    (φ : H → Set.Ioi (⊥ : EReal)) (p : ℝ × H) :
    (perspective φ.asEReal)∗ p =
      sSup (Set.range fun q : ℝ × H ↦
        (((p.1 * q.1 + ⟪p.2, q.2⟫_ℝ : ℝ) : EReal) -
          perspective φ.asEReal q)) := sorry

-- Proof sketch: expand the Fenchel conjugate of the perspective on `ℝ × H`, then separate the
-- supremum over the positive scalar variable `ξ`. The inner supremum is exactly `φ^*(u)`, so the
-- remaining one-dimensional supremum is exactly the textbook indicator of
-- `perspectiveConjugateSet φ`. For `φ : H → Set.Ioi (⊥ : EReal)`, the only remaining properness
-- content is that the effective domain is nonempty.
/-- Example 13.9: if `φ` attains at least one finite value, then the Fenchel conjugate of the
perspective is the textbook indicator `ι[C]` of the set `C = {(μ, u) | μ + φ^*(u) ≤ 0}`. -/
theorem conjugate_perspective_eq_indicator_perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    (perspective φ.asEReal)∗ =
      (ι[perspectiveConjugateSet φ]).asEReal := sorry

-- Proof sketch: if `φ` has empty effective domain, then `φ ≡ ⊤`; the perspective is identically
-- `⊤`, and its conjugate collapses to `⊥`.
/-- In the empty-domain degenerate case of Example 13.9, the perspective conjugate is identically
`⊥`. -/
theorem conjugate_perspective_eq_bot_of_effectiveDomain_eq_empty
    (φ : H → Set.Ioi (⊥ : EReal)) (hempty : effectiveDomain φ = ∅) :
    (perspective φ.asEReal)∗ = fun _ : ℝ × H ↦ (⊥ : EReal) := sorry

end

end ERealFunction
