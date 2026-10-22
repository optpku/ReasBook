/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/- Domain review for this item: the dual norm already lives on the canonical owner
`StrongDual ℝ E₁`, so the main entry should recall that existing norm rather than introduce a
new wrapper.

Layer targeted by this refinement:
- source-facing recall of the canonical norm owner on `StrongDual ℝ E₁`, plus the textbook
  support-function bridge

Sampled owner-style declarations:
- mathlib `StrongDual`
- mathlib `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- mathlib `ContinuousLinearMap.le_opNorm_of_le`
- project `Seminorm.dualNorm_normSeminorm_eq_norm` in `Chap02/Lemma_2_3`
- project `LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual` in
  `Chap04/Definition_4_2_6`

Best owner abstraction:
- core/canonical: the existing norm `‖·‖ : StrongDual ℝ E₁ → ℝ`

Primitive data:
- a continuous linear functional `s : StrongDual ℝ E₁`

Derived API:
- mathlib's absolute-value support formula
  `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- the source-facing support-function formula on the symmetric closed unit ball, obtained by
  removing the absolute value using symmetry of the ball

Source/core/bridge triage:
- source-facing: the textbook dual-norm formula `sup_{‖x‖≤1} s x`
- core/canonical: the norm on `StrongDual ℝ E₁`
- bridge/view: passing from `sup_{‖x‖≤1} ‖s x‖` to `sup_{‖x‖≤1} s x` by replacing `x` with `-x`
  when needed
-/

/- Definition 4.4.4: the dual norm on `E₁⋆` is exactly the existing norm on the continuous dual
`StrongDual ℝ E₁`. -/
#check (‖·‖ : StrongDual ℝ E₁ → ℝ)

-- Proof sketch: start from the operator-norm formula
-- `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`, then use the symmetry of the closed unit
-- ball to replace `|s x|` by `s x`; in finite dimensions the resulting supremum is a maximum.
/-- Companion bridge for Definition 4.4.4: the canonical norm on the continuous dual is the
supremum of the evaluation pairing over the closed unit ball of `E₁`; in finite dimensions this
supremum is the textbook maximum. -/
theorem dual_norm_eq_sSup_closedUnitBall (s : StrongDual ℝ E₁) :
    ‖s‖ = sSup (s '' closedBall (0 : E₁) 1) := by
  let S : Set ℝ := s '' closedBall (0 : E₁) 1
  let T : Set ℝ := (fun x : E₁ ↦ ‖s x‖) '' closedBall (0 : E₁) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖s‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hsx : |s x| ≤ ‖s‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using s.le_opNorm x
    calc
      s x ≤ |s x| := le_abs_self _
      _ ≤ ‖s‖ * ‖x‖ := hsx
      _ ≤ ‖s‖ * 1 := mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _)
      _ = ‖s‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖s‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hsx : 0 ≤ s x
    · exact ⟨x, hx, by simp [abs_of_nonneg hsx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hsx)]
  have hsSup_T_le : sSup T ≤ sSup S := by
    refine csSup_le hT_nonempty ?_
    intro y hy
    exact le_csSup hS_bdd (hT_subset hy)
  have hT_eq : sSup T = ‖s‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm s
  have hsSup_S_le : sSup S ≤ ‖s‖ := csSup_le hS_nonempty hS_bound
  have hnorm_le : ‖s‖ ≤ sSup S := by
    rw [← hT_eq]
    exact hsSup_T_le
  have hS_eq : sSup S = ‖s‖ := le_antisymm hsSup_S_le hnorm_le
  simpa [S] using hS_eq.symm

end
