/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable {n : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Example 2.1.1.4 is a source-facing recall in finite-dimensional convex analysis of log-sum-exp.

Sampled owner-style declarations in this domain:
* project `convexOn_log_sum_exp_of_convexOn`, the owner theorem for finite-family log-sum-exp on a
  common convex domain
* mathlib `EuclideanSpace.projₗ`, the canonical coordinate linear functional on Euclidean space
* mathlib `LinearMap.convexOn`, which derives convexity of linear maps on convex domains

Best owner abstraction:
* core/canonical: `convexOn_log_sum_exp_of_convexOn`
* source-facing bridge used here: the `Set.univ` specialization of
  `convexOn_log_sum_exp_of_convexOn`

Primitive data:
* the ambient Euclidean space `E`
* the coordinate functionals `EuclideanSpace.projₗ i`
* the positive arity `n : ℕ+`

Derived API:
* convexity of each coordinate map from `LinearMap.convexOn`
* the source-facing specialization `x ↦ log (∑ i = 1, …, n, exp (x⁽ⁱ⁾))`

Source/core/bridge triage:
* source-facing: Example 2.1.1.4 as the convexity statement for
  `x ↦ log (∑ i = 1, …, n, exp (x⁽ⁱ⁾))`
* core/canonical: `convexOn_log_sum_exp_of_convexOn`
* bridge/view: specialization of `convexOn_log_sum_exp_of_convexOn` to `Set.univ`, then to the
  canonical coordinate projections

The previous whole-space bridge theorem added no owner-level API beyond the `Set.univ`
specialization of `convexOn_log_sum_exp_of_convexOn`. This file therefore uses the owner theorem
directly and checks the coordinate-projection specialization instead of depending on a parallel
bridge name.
-/

#check
  (show ConvexOn ℝ Set.univ
      (fun x : E ↦ Real.log (∑ i : Fin n, Real.exp (x i))) from
    convexOn_log_sum_exp_of_convexOn Set.univ Finset.univ_nonempty
      (fun i _ ↦ (EuclideanSpace.projₗ i).convexOn convex_univ))

end
