/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: unfold `satisfies_approximate_centering_condition` and then expand
-- `dualLocalNorm` via `dualLocalNorm_def`. Writing `s = ∇ f y`, the shifted covector becomes
-- `s - t ∇ f(y₀)`, so the condition is exactly the inverse-Hessian quadratic-neighborhood bound
-- around the straight line `t ↦ t ∇ f(y₀)` in dual coordinates.
/-- Remark 5.2.1: in dual coordinates `s = ∇ f(y)`, the central path is the straight line
`s(t) = t ∇ f(y₀)`, and the approximate centering condition `(5.2.13)` is exactly the statement
that `s` lies in the inverse-Hessian quadratic neighborhood of that line with radius `β / M_f`.
This is the project's library-facing form of the textbook dual interpretation using
`∇² f_* (s)`. -/
theorem approximateCenteringCondition_iff_dualCentralPathNeighborhood
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      let s := ∇ f y
      Real.sqrt
          (inner ℝ (s - (t : ℝ) • ∇ f (y0 : E))
            ((hessian f y).inverse (s - (t : ℝ) • ∇ f (y0 : E)))) ≤
        β / (Mf : ℝ) := by
  -- Expand the domain-membership Newton decrement before rewriting the tilted-objective data.
  have hdecr :
      NewtonDecrement.ofPosDefMem (auxiliaryCentralPathObjective f y0 t) y hy =
        Real.sqrt
          (inner ℝ (∇ f y - (t : ℝ) • ∇ f (y0 : E))
            ((hessian f y).inverse (∇ f y - (t : ℝ) • ∇ f (y0 : E)))) := by
    calc
      NewtonDecrement.ofPosDefMem (auxiliaryCentralPathObjective f y0 t) y hy =
          Real.sqrt
            (inner ℝ (∇ (auxiliaryCentralPathObjective f y0 t) y)
              ((hessian (auxiliaryCentralPathObjective f y0 t) y).inverse
                (∇ (auxiliaryCentralPathObjective f y0 t) y))) := by
        simpa using
          (NewtonDecrement.ofPosDefMem_def (auxiliaryCentralPathObjective f y0 t) y hy)
      _ =
          Real.sqrt
            (inner ℝ (∇ f y - (t : ℝ) • ∇ f (y0 : E))
              ((hessian f y).inverse (∇ f y - (t : ℝ) • ∇ f (y0 : E)))) := by
        simpa [auxiliaryCentralPathObjective_gradient_eq, auxiliaryCentralPathObjective_hessian_eq]
  -- Rewrite the source-facing predicate to the canonical Newton-decrement inequality.
  rw [satisfies_approximate_centering_condition_iff, hdecr]
  -- The `let s := ∇ f y` binder is definitionally the shifted gradient expression above.

end
