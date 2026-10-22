/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.65 is `source-facing`: it records the standing hypotheses for minimizing a
real-valued smooth convex objective with a uniform bound on the distance from each positive
sublevel set to the optimal set.

Domain sampling in the surrounding project points to the existing owners
`is_l_smooth_on`, `IsFastProximalGradientProblem`, and `IsSFISTAProblem`. The first provides the
canonical smoothness predicate, while the latter two show the project pattern for packaging
standing assumptions as small `Prop`-valued classes. Since the present item adds the extra
bounded-distance clause on top of the Chapter 10 fast proximal-gradient owner specialized to the
zero regularizer `g = 0`, the correct public surface is a stronger source-facing class extending
that owner rather than a parallel wrapper that repeats its primitive fields. -/

/-- Definition 10.65: clauses (A)-(C) mean that `f : E → ℝ` is convex and globally
`L_f`-smooth, `XStar = X^*` is the nonempty optimal set of `min_x f(x)` with optimal value
`fOpt = f_opt`, and for every `α > 0` there is `R_α > 0` such that every point `x` with
`f x ≤ α` lies within distance at most `R_α` of the optimal set `XStar`. The convexity,
smoothness, optimal-set, and optimal-value clauses are inherited from the canonical Chapter 10
owner `IsFastProximalGradientProblem` for the zero regularizer. -/
class IsSublevelDistanceBoundedSmoothConvexMinimizationProblem
    (f : E → ℝ) (XStar : outParam (Set E)) (fOpt : outParam ℝ) (Lf : outParam NNReal) : Prop
    extends IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf where
  bounded_sublevel_distance_to_optimal_set (α : PosReal) :
    ∃ Rα : PosReal, ∀ ⦃x : E⦄, f x ≤ α → infDist x XStar ≤ Rα

/-- In Definition 10.65, the real-valued objective is convex on the whole space. -/
instance instFactConvexOnUnivOfIsSublevelDistanceBoundedSmoothConvexMinimizationProblem
    {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h : IsSublevelDistanceBoundedSmoothConvexMinimizationProblem f XStar fOpt Lf) :
    Fact (ConvexOn ℝ Set.univ f) :=
  ⟨h.f_convex⟩

end
