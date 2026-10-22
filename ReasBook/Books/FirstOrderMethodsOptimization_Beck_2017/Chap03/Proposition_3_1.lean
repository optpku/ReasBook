/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 3.1 is `source-facing` for the norm example in the chapter subdifferential theory.
Its owner stack already lives upstream: `is_subgradient_at` is the primitive predicate,
`subdifferential` is the source-facing owner set, and `∂ₛ f(x)` is the continuous-dual
`bridge/view`. The proposition should therefore stay as a direct identification of that existing
owner object, not introduce a parallel wrapper API. -/

-- Proof sketch: unfold `∂ₛ`, simplify `‖0‖ = 0`, and identify the resulting inequality
-- `(‖y‖ : EReal) ≥ g y` for all `y` with the dual-unit-ball condition `‖g‖ ≤ 1`, equivalently
-- `g ∈ closedBall (0 : StrongDual ℝ E) 1`.
/-- Helper for Proposition 3.1: membership in the norm subdifferential at the origin is exactly
the pointwise support inequality `g y ≤ ‖y‖`. -/
private lemma mem_strongDualSubdifferential_norm_zero_iff_forall_apply_le_norm
    {g : StrongDual ℝ E} :
    g ∈ ∂ₛ(fun x : E ↦ (‖x‖ : EReal))((0 : E)) ↔ ∀ y : E, g y ≤ ‖y‖ := by
  -- Rewrite the bridge membership back to the owner predicate, then simplify the norm at `0`.
  rw [mem_strongDualSubdifferential, mem_subdifferential]
  simpa [ge_iff_le, norm_zero] using
    (is_subgradient_at_coe_iff
      (f := fun x : E ↦ ‖x‖) (x := (0 : E)) (g := (g : Module.Dual ℝ E)))

/-- Helper for Proposition 3.1: a subgradient of the norm at the origin satisfies the standard
pointwise dual estimate `|g y| ≤ ‖y‖`. -/
private lemma abs_apply_le_norm_of_mem_strongDualSubdifferential_norm_zero
    {g : StrongDual ℝ E}
    (hg : g ∈ ∂ₛ(fun x : E ↦ (‖x‖ : EReal))((0 : E))) :
    ∀ y : E, |g y| ≤ ‖y‖ := by
  intro y
  have hpos : g y ≤ ‖y‖ :=
    (mem_strongDualSubdifferential_norm_zero_iff_forall_apply_le_norm.mp hg) y
  have hneg : -g y ≤ ‖y‖ := by
    -- Evaluate the same support inequality at `-y` to recover the lower bound on `g y`.
    simpa using
      (mem_strongDualSubdifferential_norm_zero_iff_forall_apply_le_norm.mp hg) (-y)
  -- Combine the upper and lower bounds into the absolute-value estimate.
  refine abs_le.mpr ?_
  constructor
  · linarith
  · exact hpos

/-- Helper for Proposition 3.1: every dual vector with `‖g‖ ≤ 1` is a subgradient of the norm at
the origin. -/
private lemma mem_strongDualSubdifferential_norm_zero_of_norm_le_one
    {g : StrongDual ℝ E} (hg : ‖g‖ ≤ 1) :
    g ∈ ∂ₛ(fun x : E ↦ (‖x‖ : EReal))((0 : E)) := by
  rw [mem_strongDualSubdifferential_norm_zero_iff_forall_apply_le_norm]
  intro y
  have hopNorm : |g y| ≤ ‖g‖ * ‖y‖ := by
    -- The operator norm controls each evaluation of the continuous linear functional `g`.
    simpa [Real.norm_eq_abs] using (g.le_opNorm y)
  have habs : |g y| ≤ ‖y‖ := by
    calc
      |g y| ≤ ‖g‖ * ‖y‖ := hopNorm
      _ ≤ 1 * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right hg (norm_nonneg y)
      _ = ‖y‖ := by simp
  -- Drop from the absolute-value bound to the one-sided support inequality.
  exact (le_abs_self (g y)).trans habs

/-- Proposition 3.1: the subdifferential of the norm at the origin is the closed unit ball of the
dual norm on `E*`. -/
theorem strongDualSubdifferential_norm_zero_eq_closedBall :
    ∂ₛ(fun x : E ↦ (‖x‖ : EReal))((0 : E)) =
      closedBall (0 : StrongDual ℝ E) 1 := by
  ext g
  constructor
  · intro hg
    -- Convert subgradient membership into the pointwise absolute-value estimate and bound `‖g‖`.
    have habs : ∀ y : E, |g y| ≤ ‖y‖ :=
      abs_apply_le_norm_of_mem_strongDualSubdifferential_norm_zero hg
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using
      (g.opNorm_le_bound zero_le_one fun y ↦ by
        simpa [Real.norm_eq_abs] using habs y)
  · intro hg
    -- Rewrite closed-ball membership as the dual norm bound and rebuild the subgradient.
    have hnorm : ‖g‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    exact mem_strongDualSubdifferential_norm_zero_of_norm_le_one hnorm

/-- Membership in the norm subdifferential at the origin is equivalent to the dual norm bound
`‖g‖ ≤ 1`. -/
@[simp] theorem mem_strongDualSubdifferential_norm_zero_iff
    {g : StrongDual ℝ E} :
    g ∈ ∂ₛ(fun x : E ↦ (‖x‖ : EReal))((0 : E)) ↔ ‖g‖ ≤ 1 := by
  rw [strongDualSubdifferential_norm_zero_eq_closedBall]
  simp [Metric.mem_closedBall, dist_eq_norm]

end
