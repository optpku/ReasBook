/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/- Theorem 5.3.9 lies in the Chapter 5 self-concordant-barrier / analytic-center / Dikin-ellipsoid
domain.

Sampled owner-style declarations in this domain:
* `IsMinOn` in `Definition_5_3_3`, the canonical analytic-center owner;
* `dikinEllipsoid`, `openDikinEllipsoid`, and the notation `W[f; x](r)`, `W⁰[f; x](r)` in
  `Definition_5_0_13`, the chapter owners for the closed and open local-norm balls;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith
    .hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg`
  in `Theorem_5_3_8`, the owner local-distance estimate;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Theorem_5_1_5`, the
  canonical open-Dikin-ball domain-inclusion theorem for standard self-concordant functions.

Best owner abstraction:
* source-facing: the analytic-center local-distance bound and its Dikin-ellipsoid corollaries from
  Theorem 5.3.9;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F` together with the Chapter 5 Dikin-ball
  owners `W[F; xStar : E] (r)` and `W⁰[F; xStar : E](1)`;
* bridge/view: the analytic-center stationarity consequence
  `∇ F (xStar : E) = 0`, obtained from `IsMinOn` via the Chapter 1 local-minimum owner theorem,
  and the standard-self-concordant unit-ball inclusion theorem.

Primitive data:
* the barrier owner witness `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* for clause `(1)`, the analytic-center witness `hcenter : IsMinOn F dom (xStar : E)`;
* for clause `(2)`, only the center point `xStar : dom`.

Derived API:
* the radius-`ν + 2 √ν` Dikin-ellipsoid containment of `dom`;
* the canonical-recall identification of clause `(2)` with the standard self-concordant
  open-Dikin-ball inclusion theorem.

Source/core/bridge triage:
* source-facing: clause `(1)` as an analytic-center containment statement;
* core/canonical: the barrier owner together with the Chapter 5 Dikin-ball owners;
* bridge/view: clause `(1)` is a closed-ball corollary of the owner local-distance bound, while
  clause `(2)` reuses the canonical open-ball owner theorem directly.

This item is therefore best expressed on the barrier and Dikin-ball owner layer. Clause `(1)`
remains a new barrier-specific theorem, while clause `(2)` should be handled by direct recall of
the canonical standard-self-concordant owner theorem rather than by a duplicate specialized
wrapper. The ambient space assumption stays aligned with the upstream owner graph, which lives on
complete real inner-product spaces rather than on a finite-dimensional bridge. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

/-- Theorem 5.3.9 (1): if `xStar` is an analytic center of a `ν`-self-concordant barrier `F`,
then the whole domain `dom` lies in the Dikin ellipsoid centered at `xStar` with radius
`ν + 2 √ν`. Equivalently, every `x ∈ dom` satisfies the local-distance bound `(5.3.17)`. -/
theorem subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E)) :
    dom ⊆ W[F; (xStar : E)]((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hstd : IsStandardSelfConcordantOn dom F := inferInstance
  intro x hx
  rw [mem_dikinEllipsoid_iff]
  have hlocal : IsLocalMin F (xStar : E) :=
    hcenter.isLocalMin (hstd.isOpen_domain.mem_nhds xStar.2)
  have hgrad0 : ∇ F (xStar : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  exact hF.hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
    xStar.2 hx (by simp [hgrad0])

end IsSelfConcordantBarrierOnWith

/- Theorem 5.3.9 (2) is the Chapter 5 owner theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`, specialized to the standard
self-concordant constant `1` inherited from a self-concordant barrier. It introduces no new
barrier-specific API, so this file reuses the canonical owner directly instead of keeping a
duplicate wrapper theorem. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

end
