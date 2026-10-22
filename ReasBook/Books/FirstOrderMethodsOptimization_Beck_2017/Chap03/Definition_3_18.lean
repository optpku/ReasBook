/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDual toDual_apply_apply)
open scoped Gradient RealInnerProductSpace

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 3.18 is `source-facing`, but its owner notions already exist upstream: the dual
normal cone `normal_cone` from Definition 3.3 and the composite stationary predicate
`is_stationary_point` from Definition 3.17. This file therefore keeps only the constrained
specialization together with the Euclidean `bridge/view` theorem that rewrites owner
normal-cone membership into the textbook variational inequality. -/

recall is_stationary_point
recall normal_cone

/-- Definition 3.18: constrained stationarity is the specialization of the composite stationary
predicate from Definition 3.17 to the indicator term `δ_C`. -/
def is_stationary_point_on (f : E → ℝ) (C : Set E) (x : E) : Prop :=
  is_stationary_point (fun y ↦ (f y : EReal)) (extendedIndicator C) x

private theorem neg_gradient_mem_normal_cone_iff (f : E → ℝ) (C : Set E) (x : E) :
    (-toDual ℝ E (∇ f x) : Module.Dual ℝ E) ∈ normal_cone C x ↔
      x ∈ C ∧ ∀ y ∈ C, ⟪∇ f x, y - x⟫ ≥ (0 : ℝ) := by
  constructor
  · intro h
    by_cases hx : x ∈ C
    · refine ⟨hx, fun y hy ↦ ?_⟩
      have hcone := (mem_normal_cone C hx _).1 h
      simpa [toDual_apply_apply, inner_neg_left, neg_nonpos] using hcone y hy
    · exfalso
      simp [normal_cone_eq_empty_of_not_mem C hx] at h
  · rintro ⟨hx, hcone⟩
    refine (mem_normal_cone C hx _).2 fun y hy ↦ ?_
    simpa [toDual_apply_apply, inner_neg_left, neg_nonpos] using hcone y hy

/-- Unfolding constrained stationarity gives differentiability of `f` at `x` together with
membership of `-∇ f(x)` in the owner normal cone of `C` at `x`, transported by
`toDual`. -/
@[simp] theorem is_stationary_point_on_iff
    (f : E → ℝ) (C : Set E) (x : E) :
    is_stationary_point_on f C x ↔
      DifferentiableAt ℝ f x ∧
        (-toDual ℝ E (∇ f x) : Module.Dual ℝ E) ∈ normal_cone C x := by
  simp [is_stationary_point_on, is_stationary_point_iff,
    subdifferential_extended_indicator_eq_normal_cone, is_differentiable_at, finite_domain]

-- Proof sketch: unfold `is_stationary_point_on` through the owner predicate from Definition 3.17,
-- then rewrite owner normal-cone membership using `normal_cone` and `toDual_apply_apply`. The
-- condition `⟪-gradient f x, y - x⟫ ≤ 0` is equivalent to `⟪gradient f x, y - x⟫ ≥ 0` by
-- `inner_neg_left`.
/-- A constrained stationary point is equivalently a feasible differentiable point satisfying the
first-order variational inequality on every feasible displacement. -/
theorem is_stationary_point_on_iff_forall_inner_nonneg (f : E → ℝ) (C : Set E) (x : E) :
    is_stationary_point_on f C x ↔
      DifferentiableAt ℝ f x ∧ x ∈ C ∧ ∀ y ∈ C, ⟪∇ f x, y - x⟫ ≥ (0 : ℝ) := by
  rw [is_stationary_point_on_iff, neg_gradient_mem_normal_cone_iff]

end
