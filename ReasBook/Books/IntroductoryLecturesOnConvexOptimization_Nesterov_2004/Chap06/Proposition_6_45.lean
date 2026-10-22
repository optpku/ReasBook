/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

noncomputable section

universe u v

/- Proposition 6.45 lies in the chapter's structured saddle-slice / attained weak-duality-gap
domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the Chapter 6 owner for
  the saddle map `Ψ`;
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical primal outer
  value `x ↦ sup_u Ψ(x, u)`;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the canonical dual
  outer value `u ↦ inf_x Ψ(x, u)`;
- mathlib `IsGreatest` and `IsLeast`, the canonical order-theoretic owners for attained maxima
  and minima of the two saddle slices.

Best owner abstraction:
- source-facing: the attained-extrema weak-duality-gap inequality from Proposition 6.45;
- core/canonical: `StructuredObjectiveModel.saddleFunction`;
- bridge/view: the order-theoretic comparison between an attained maximum of `u ↦ Ψ(x, u)` and an
  attained minimum of `y ↦ Ψ(y, u)`.

Primitive data:
- `problem : StructuredObjectiveModel E₁ E₂`;
- a primal point `x : problem.primalSet`;
- a dual point `u : problem.dualSet`.

Derived API:
- the fixed-`x` saddle slice `problem.saddleFunction x`;
- the fixed-`u` saddle slice `fun y : problem.primalSet ↦ problem.saddleFunction y u`;
- attained extrema of those slices, expressed canonically by `IsGreatest` and `IsLeast`.

Source/core/bridge triage:
- source-facing: the proposition below on attained slice extrema;
- core/canonical: the Chapter 6 owner `StructuredObjectiveModel`;
- bridge/view: this real-valued attained-extrema corollary of the saddle slices.

The previous version kept the concrete Hilbert-space formula
`ψ(x) + ⟪A x, u⟫ - g(u)` as the main theorem surface. The mathematical content here is only the
order relation between the two slices of a saddle map, so the refined theorem is stated directly
on the Chapter 6 owner `StructuredObjectiveModel.saddleFunction`; the concrete bilinear formula is
already recovered elsewhere by `StructuredObjectiveModel.saddleFunction_apply`.
-/

namespace StructuredObjectiveModel

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Proposition 6.45: if `f̄(x)` is the attained maximum of the fixed-`x` saddle slice
`u ↦ Ψ(x, u)` on `Q₂` and `ḡ(u)` is the attained minimum of the fixed-`u` saddle slice
`y ↦ Ψ(y, u)` on `Q₁`, then the weak-duality gap `f̄(x) - ḡ(u)` is nonnegative. -/
theorem weakDualityGap_nonneg_of_attainedExtrema
    {problem : StructuredObjectiveModel E₁ E₂}
    (x : problem.primalSet) (u : problem.dualSet) {fBar gBar : ℝ}
    (hprimal : IsGreatest (Set.range (problem.saddleFunction x)) fBar)
    (hdual :
      IsLeast
        (Set.range fun y : problem.primalSet ↦ problem.saddleFunction y u)
        gBar) :
    0 ≤ fBar - gBar := by
  exact sub_nonneg.mpr <|
    (hdual.2 <| Set.mem_range_self x).trans (hprimal.2 <| Set.mem_range_self u)

end StructuredObjectiveModel

end
