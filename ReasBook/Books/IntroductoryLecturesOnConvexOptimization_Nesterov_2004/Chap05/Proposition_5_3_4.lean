/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 5.3.4 lies in the Chapter 5 dual-barrier / Fenchel-conjugacy domain.

Sampled owner-style declarations in this domain:
* `fenchelDual` / notation `f⋆` in `Definition_5_0_27`, the chapter owner for the canonical
  dual object `F_*`;
* `extendedRealRealPart (f⋆)`, the real-valued owner surface of that dual object used throughout
  the chapter;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for barrier
  parameters on a standard self-concordant domain;
* `IsSelfConcordantOnWith.hessian_isPositive` in `Definition_5_1_1`, the canonical pointwise
  Hessian-positivity bridge on that owner surface;
* `fderiv_gradient_isSymmetric_of_contDiffAt` in `Chap01/Theorem_1_4_19`, the upstream symmetry
  owner behind the positive-Hessian quadratic-form argument.

Best owner abstraction:
* source-facing: the barrier criterion for the canonical dual object `F_*`, stated through the
  source relation `(5.1.34)` and the pairing `⟪s, ∇²F_*(s) s⟫`;
* core/canonical: `extendedRealRealPart (f⋆)` together with the barrier owner
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise completion-of-the-square argument on
  `⟪u - s, ∇²F_*(s) (u - s)⟫`, read through Hessian positivity and symmetry.

Primitive data:
* the primal extended-real owner `f : E → WithTop ℝ`;
* the source relation `(5.1.34)` on the canonical dual real part
  `∇ (extendedRealRealPart (f⋆)) s = ∇² (extendedRealRealPart (f⋆))(s) s`;
* standard self-concordance of `extendedRealRealPart (f⋆)` on `dom (f⋆)`;
* the source-facing bound `⟪s, ∇²F_*(s) s⟫ ≤ ν`.

Derived API:
* pointwise positivity and symmetry of the dual Hessian on `dom (f⋆)`;
* the completed-square estimate
  `2 ⟪∇F_*(s), u⟫ - ⟪u, ∇²F_*(s)u⟫ ≤ ⟪s, ∇²F_*(s)s⟫`;
* the `ν`-self-concordant barrier owner on `dom (f⋆)`.

This refinement keeps Proposition 5.3.4 source-facing on the canonical dual owner
`extendedRealRealPart (f⋆)`, but removes the bridge-level Fenchel maximizer branch and inverse-
Hessian machinery from the public statement. The barrier inequality is derived directly from
`(5.1.34)`, Hessian positivity, and the source bound `⟪s, ∇²F_*(s) s⟫ ≤ ν`. -/

section FenchelDualBarrier

variable {f : E → WithTop ℝ}

-- Proof sketch: for fixed `s ∈ dom (f⋆)` and direction `u`, positivity of
-- `hessian (extendedRealRealPart (f⋆)) s` gives
-- `0 ≤ ⟪u - s, ∇²F_*(s) (u - s)⟫`. Expanding this quadratic form and using the symmetry of a
-- positive Hessian shows
-- `2 ⟪∇²F_*(s) s, u⟫ - ⟪u, ∇²F_*(s) u⟫ ≤ ⟪s, ∇²F_*(s) s⟫`. Relation `(5.1.34)` rewrites the left
-- side as the barrier expression, so the assumed source bound is exactly the defining barrier
-- parameter inequality.
/-- Proposition 5.3.4: let `F_* = extendedRealRealPart (f⋆)`. Assume the canonical dual satisfies
relation `(5.1.34)`, namely `∇F_*(s) = ∇²F_*(s) s`, is standard self-concordant on `dom (f⋆)`,
and obeys `⟪s, ∇²F_*(s) s⟫ ≤ ν` on `dom (f⋆)`. Then `F_*` is a `ν`-self-concordant barrier on
its effective domain. -/
theorem fenchelConjugate_realPart_isSelfConcordantBarrierOnWith
    {ν : NNReal}
    (hdual_gradient_eq_hessian_apply_self :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        ∇ (extendedRealRealPart (f⋆)) s =
          hessian (extendedRealRealPart (f⋆)) s s)
    (hsc : IsStandardSelfConcordantOn (dom (f⋆)) (extendedRealRealPart (f⋆)))
    (hbound :
      ∀ s ∈ dom (f⋆),
        inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) ≤ (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith (dom (f⋆)) ν (extendedRealRealPart (f⋆)) := by
  refine ⟨hsc, ?_⟩
  intro s hs u
  have hPos : (hessian (extendedRealRealPart (f⋆)) s).IsPositive := hsc.hessian_isPositive hs
  have hnonneg :
      0 ≤
        inner ℝ (u - s)
          (hessian (extendedRealRealPart (f⋆)) s (u - s)) := by
    simpa [real_inner_comm] using hPos.inner_nonneg_right (u - s)
  have hsymm := hPos.isSymmetric
  have hcross :
      inner ℝ s (hessian (extendedRealRealPart (f⋆)) s u) =
        inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u := by
    calc
      inner ℝ s (hessian (extendedRealRealPart (f⋆)) s u) =
          inner ℝ (hessian (extendedRealRealPart (f⋆)) s u) s := by
            rw [real_inner_comm]
      _ = inner ℝ u (hessian (extendedRealRealPart (f⋆)) s s) := hsymm u s
      _ = inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u := by
            rw [real_inner_comm]
  have hexpand :
      inner ℝ (u - s) (hessian (extendedRealRealPart (f⋆)) s (u - s)) =
        inner ℝ u (hessian (extendedRealRealPart (f⋆)) s u) -
          2 * inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u +
          inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) := by
    simp [sub_eq_add_neg, map_add, map_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, hcross, real_inner_comm]
    ring
  rw [hdual_gradient_eq_hessian_apply_self hs]
  have hmajor :
      2 * inner ℝ (hessian (extendedRealRealPart (f⋆)) s s) u -
          inner ℝ u (hessian (extendedRealRealPart (f⋆)) s u) ≤
        inner ℝ s (hessian (extendedRealRealPart (f⋆)) s s) := by
    linarith [hnonneg, hexpand]
  linarith [hmajor, hbound s hs]

end FenchelDualBarrier

end
