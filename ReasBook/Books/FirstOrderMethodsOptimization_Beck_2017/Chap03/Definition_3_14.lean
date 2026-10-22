/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {m : ℕ} {α : Type*}
variable [PseudoMetricSpace α]

/- Definition 3.14 is a `source-facing` item: the public owner is the Fermat-Weber objective
itself. The ambient `core/canonical` notion underneath is the metric-space distance `dist`, so the
definition uses that owner directly and treats the Euclidean norm formula as a companion view. -/

/-- Definition 3.14: for weighted sites `a i` in a metric space, the Fermat-Weber objective is
the weighted finite sum of the distances from `x` to the sites. In the Euclidean specialization
this is the textbook formula `x ↦ ∑ i, ω i * ‖x - a i‖`. The textbook assumes positive weights;
positivity is imposed only in later results, since it does not affect the function definition
itself. -/
def fermatWeberObjective
    (ω : Fin m → ℝ) (a : Fin m → α) :
    α → ℝ :=
  fun x ↦ ∑ i, ω i * dist x (a i)

-- Proof sketch: unfold `fermatWeberObjective`; the statement is exactly its defining formula.
/-- Evaluating the Fermat-Weber objective at `x` gives the weighted sum of the distances from `x`
to the sites `a i`. -/
@[simp] theorem fermatWeberObjective_apply
    (ω : Fin m → ℝ) (a : Fin m → α) (x : α) :
    fermatWeberObjective ω a x = ∑ i, ω i * dist x (a i) :=
  rfl

section SeminormedAddCommGroup

variable {E : Type*} [SeminormedAddCommGroup E]

-- Proof sketch: evaluate the metric-space definition at `x` and rewrite each distance using
-- `dist_eq_norm`.
/-- In a seminormed additive commutative group, the Fermat-Weber objective is the weighted sum of
the norms `‖x - a i‖`. This is the Euclidean textbook formula specialized to the ambient norm. -/
@[simp] theorem fermatWeberObjective_apply_eq_sum_norm
    (ω : Fin m → ℝ) (a : Fin m → E) (x : E) :
    fermatWeberObjective ω a x = ∑ i, ω i * ‖x - a i‖ := by
  simp [fermatWeberObjective, dist_eq_norm]

end SeminormedAddCommGroup

section Real

-- Proof sketch: specialize the norm formula to `ℝ`, where `‖x - a i‖ = |x - a i|`, and simplify
-- the constant unit weights.
/-- On the real line with unit weights, the Fermat-Weber objective is the textbook absolute-
deviation sum `x ↦ ∑ i, |x - a_i|`. -/
@[simp] theorem fermatWeberObjective_one_apply_eq_sum_abs
    (a : Fin m → ℝ) (x : ℝ) :
    fermatWeberObjective (fun _ : Fin m ↦ (1 : ℝ)) a x = ∑ i, |x - a i| := by
  simpa using
    (fermatWeberObjective_apply_eq_sum_norm (fun _ : Fin m ↦ (1 : ℝ)) a x)

end Real

end
