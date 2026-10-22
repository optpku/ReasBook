/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {Q : Type u}

/- Proposition 6.43 lies in the composite-minimization / global-optimality-gap domain.

Sampled owner-style declarations:
- mathlib `IsMinOn`, the canonical owner for minimizers on a set;
- mathlib `isMinOn_univ_iff`, the bridge from `IsMinOn f Set.univ xStar` to the pointwise
  inequality `∀ x, f xStar ≤ f x`;
- `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt` in
  `Chap03/Theorem_3_1_23`, a nearby project theorem that already treats real-valued composite
  objectives directly as `(f + Ψ)` rather than through a local wrapper;
- `totalVariation_ge_compositeObjective_gap_and_nonneg` in
  `Chap06/Text_6_4_1_Total_Variation_as_a_First_Order_Optimality_Measure`, the nearby Chapter 6
  gap theorem stated directly against the composite value `f x + Ψ x`.

Best owner abstraction:
- source-facing: Proposition 6.43 itself, comparing an abstract upper bound `δ` with the
  composite optimality gap;
- core/canonical: `IsMinOn (f + Ψ) Set.univ xStar`;
- bridge/view: `isMinOn_univ_iff`.

Primitive data:
- the functions `f`, `Ψ`, and `δ`;
- the minimizer `xStar`;
- the assumed pointwise upper bound on the composite gap.

Derived API:
- the gap upper bound at the chosen point `x`;
- the gap nonnegativity obtained from the canonical minimizer owner.

This file should not introduce a separate `compositeObjective` owner: in the
real-valued, whole-space setting, the canonical surface is already `(f + Ψ)`
together with `IsMinOn ... Set.univ`.
-/

-- Proof sketch: the first inequality is exactly the assumed lower bound on `delta`. The
-- minimizer hypothesis on `xStar` implies `(f xStar + Ψ xStar) ≤ (f x + Ψ x)`, so the composite
-- objective gap is nonnegative.
/-- Proposition 6.43: if `xStar` minimizes the composite objective `\bar f = f + Ψ` on `Q` and
`δ` dominates the gap `\bar f(x) - \bar f(xStar)` for every `x`, then for each `x` the same gap
is nonnegative and still bounded above by `δ x`. -/
theorem delta_ge_compositeObjective_gap_and_nonneg
    {f Ψ δ : Q → ℝ} {xStar x : Q}
    (hxStar : IsMinOn (f + Ψ) Set.univ xStar)
    (hdelta :
      ∀ y : Q, δ y ≥ (f y + Ψ y) - (f xStar + Ψ xStar)) :
    δ x ≥ (f x + Ψ x) - (f xStar + Ψ xStar) ∧
      0 ≤ (f x + Ψ x) - (f xStar + Ψ xStar) := by
  constructor
  · exact hdelta x
  · rw [isMinOn_univ_iff] at hxStar
    exact sub_nonneg.mpr (hxStar x)

end
