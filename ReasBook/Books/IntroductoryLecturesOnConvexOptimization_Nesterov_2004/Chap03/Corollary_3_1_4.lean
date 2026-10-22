/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E]

/- Corollary 3.1.4 is source-facing in the chapter's nesterovHyperplane-separation domain.

Primary domain:
- affine hyperplanes and point/set separation in a real inner-product space.

Sampled owner declarations:
- `AffineHyperplane`
- `AreStronglySeparable`
- `areStronglySeparable_singleton_of_nonmem_closed_convex`
- `areStronglySeparable_empty_singleton`

Core/canonical owner:
- `AreStronglySeparable Q ({x} : Set E)`, built from the chapter's `AffineHyperplane` owner API.

Bridge/view:
- `areStronglySeparable_iff`, which converts the owner-level set separation statement into
  coordinate data `(g, γ)`.

Primitive data:
- the nonzero normal vector and offset from the owner nesterovHyperplane API.

Derived API:
- the retained point-versus-set bridge `SeparatesPointFromWith Q x g γ`;
- the strict upper-side inequality `γ < ⟪g, x⟫`.

This file keeps the source-facing coordinate conclusion, but it now reuses the owner theorem
`AreStronglySeparable.exists_separatesPointFromWith` for the singleton-right bridge instead of
rebuilding that conversion locally. The public statement therefore stays source-faithful while the
singleton bridge lives at the owner layer, with the textbook `ℝⁿ` statement recovered by
specializing to `E = EuclideanSpace ℝ (Fin n)` and `n > 0`.
-/

/-- Corollary 3.1.4: if `Q` is a closed convex set in a nontrivial real inner-product space and
`x ∉ Q`, then there exist a nonzero normal vector `g` and an offset `γ` such that
`Q` lies in the lower closed half-space `⟪g, y⟫ ≤ γ` and `x` lies strictly above it:
`γ < ⟪g, x⟫`. The lower-side half-space inclusion is packaged by
`SeparatesPointFromWith Q x g γ`. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)` with `n > 0`. -/
-- Proof sketch: if `Q` is nonempty, apply the owner-level strong-separation theorem to `Q` and
-- the singleton `{x}`. If `Q = ∅`, use the intrinsic empty-set separation companion. Then apply
-- the canonical singleton-right bridge
-- `AreStronglySeparable.exists_separatesPointFromWith`.
theorem exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
    (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x : E} (hx : x ∉ Q) :
    ∃ g : E, ∃ γ : ℝ, SeparatesPointFromWith Q x g γ ∧ γ < inner ℝ g x := by
  have hstrong : AreStronglySeparable Q ({x} : Set E) := by
    by_cases hQ_nonempty : Q.Nonempty
    · exact
        areStronglySeparable_singleton_of_nonmem_closed_convex
          Q hQ_nonempty hQ_closed hQ_convex hx
    · have hQ_empty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ_nonempty
      simpa [hQ_empty] using
        (show AreStronglySeparable (∅ : Set E) ({x} : Set E) from
          areStronglySeparable_empty_singleton x)
  exact hstrong.exists_separatesPointFromWith

end
