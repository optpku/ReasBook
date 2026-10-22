/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SeminormDualNorm

/- Primary domain: dual norms induced by the ambient norm on a real inner-product space, with the
source-facing specialization to the Euclidean closed unit ball in `ℝⁿ`.

Sampled owner-style declarations:
* `normSeminorm`
* `Seminorm.dualNorm`
* `Seminorm.dualNorm_apply`
* `InnerProductSpace.toDual`
* `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`

Source/core/bridge triage:
* source-facing: `unit_closed_ball_support_function_eq_norm`
* core/canonical: `Seminorm.dualNorm (normSeminorm ℝ E)`
* bridge/view: `Seminorm.dualNorm_normSeminorm_eq_norm`

Primitive data:
* the ambient seminorm `normSeminorm ℝ E`

Derived API:
* `Seminorm.dualNorm_apply` rewrites the owner object as a support function over `{x | ‖x‖ ≤ 1}`
* `unit_closed_ball_support_function_eq_norm` is the Euclidean closed-ball reformulation
-/

namespace Seminorm

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the symmetric norm closed unit ball of a real normed space, the supremum of a real
continuous linear functional is its operator norm. -/
-- Proof sketch: `ContinuousLinearMap.sSup_unitClosedBall_eq_norm` gives the supremum of the
-- absolute value. Since the unit ball is stable under negation, every absolute-value image point
-- is realized as an ordinary image point, so the two suprema agree.
private theorem ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E →L[ℝ] ℝ) :
    sSup (f '' Metric.closedBall (0 : E) 1) = ‖f‖ := by
  let S : Set ℝ := f '' Metric.closedBall (0 : E) 1
  let T : Set ℝ := (fun x : E ↦ |f x|) '' Metric.closedBall (0 : E) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖f‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hfx : |f x| ≤ ‖f‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using f.le_opNorm x
    calc
      f x ≤ |f x| := le_abs_self _
      _ ≤ ‖f‖ * ‖x‖ := hfx
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _)
      _ = ‖f‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖f‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hfx : 0 ≤ f x
    · exact ⟨x, hx, by simp [abs_of_nonneg hfx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hfx)]
  have hT_le : ∀ y ∈ T, y ≤ sSup S := fun y hy ↦ le_csSup hS_bdd (hT_subset hy)
  have hsSup_T_le : sSup T ≤ sSup S := csSup_le hT_nonempty hT_le
  have hT_eq : sSup T = ‖f‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm f
  have hsSup_S_le : sSup S ≤ ‖f‖ := csSup_le hS_nonempty hS_bound
  exact le_antisymm hsSup_S_le <| by
    rw [← hT_eq]
    exact hsSup_T_le

/-- Lemma 2.3 in owner form: on a finite-dimensional real inner-product space, the dual norm
induced by the ambient norm is the ambient norm. -/
-- Proof sketch: rewrite the dual norm through `Seminorm.dualNorm_apply`, identify the underlying
-- real functional with `InnerProductSpace.toDual ℝ E s`, and then use the operator-norm formula
-- for real functionals on the symmetric unit ball.
theorem dualNorm_normSeminorm_eq_norm [FiniteDimensional ℝ E] (s : E) :
    ‖s‖[normSeminorm ℝ E,*] = ‖s‖ := by
  rw [dualNorm_apply]
  have hball : {x : E | (normSeminorm ℝ E) x ≤ 1} = Metric.closedBall (0 : E) 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_eq_norm, coe_normSeminorm]
  rw [hball]
  simpa [InnerProductSpace.toDual_apply_apply] using
    ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real (InnerProductSpace.toDual ℝ E s)

end

end Seminorm

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Lemma 2.3: the support function of the Euclidean closed unit ball in `ℝ^n` at `s` equals the
Euclidean norm of `s`, i.e. `√(∑ i, (s i)^2)`. -/
-- Proof sketch: this is the Euclidean closed-ball reformulation of
-- `Seminorm.dualNorm_normSeminorm_eq_norm`.
theorem unit_closed_ball_support_function_eq_norm (s : E) :
    sSup ((fun x : E ↦ inner ℝ s x) '' Metric.closedBall (0 : E) 1) = ‖s‖ := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using
    Seminorm.dualNorm_normSeminorm_eq_norm s
