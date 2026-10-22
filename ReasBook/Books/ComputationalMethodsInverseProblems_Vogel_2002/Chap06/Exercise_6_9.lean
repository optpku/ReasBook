/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_24
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Exercise_6_9.WeakContinuity
public import Mathlib.Analysis.LocallyConvex.WeakSpace

public section

universe u v

variable {Q : Type u} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
variable {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Helper for Exercise 6.9: composing a weakly lower semicontinuous functional with a map
continuous for the weak topologies preserves weak lower semicontinuity. -/
theorem weakLowerSemicontinuous.comp_weakSpaceContinuous {J : Y → ℝ}
    (hJ : weakLowerSemicontinuous J) {F : Q → Y} (hF : Continuous (toWeakMap F)) :
    weakLowerSemicontinuous (fun q : Q ↦ J (F q)) := by
  rw [weakLowerSemicontinuous_iff] at hJ ⊢
  intro f q hf
  exact hJ (hF.weakSeqTendsto_toWeakMap hf)

/-- Helper for Exercise 6.9: the translated squared norm `y ↦ ‖y - d‖ ^ 2` is weakly lower
semicontinuous. -/
theorem norm_sub_sq_weakLowerSemicontinuous (d : Y) :
    weakLowerSemicontinuous (fun y : Y ↦ ‖y - d‖ ^ 2) := by
  let J : WeakSpace ℝ Y → ℝ := fun y ↦ ‖(toWeakSpace ℝ Y).symm y - d‖ ^ 2
  have hJ : LowerSemicontinuous J := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : c < 0
    · -- Negative sublevel sets are empty because squared norms are nonnegative.
      have hpreimage :
          J ⁻¹' Set.Iic c = ∅ := by
        ext y
        constructor
        · intro hy
          have hnonneg : 0 ≤ J y := sq_nonneg ‖(toWeakSpace ℝ Y).symm y - d‖
          exact False.elim ((not_le_of_gt hc) (le_trans hnonneg hy))
        · intro hy
          cases hy
      simp [hpreimage]
    · have hc' : 0 ≤ c := le_of_not_gt hc
      let s : Set Y := Metric.closedBall d (Real.sqrt c)
      have hsClosed : IsClosed s := by
        simpa [s] using Metric.isClosed_closedBall
      have hsConvex : Convex ℝ s := by
        simpa [s] using convex_closedBall d (Real.sqrt c)
      have hsImageClosed : IsClosed ((toWeakSpace ℝ Y) '' s) := by
        have hclosure : closure ((toWeakSpace ℝ Y) '' s) = (toWeakSpace ℝ Y) '' s := by
          rw [← hsConvex.toWeakSpace_closure (𝕜 := ℝ), hsClosed.closure_eq]
        simpa [hclosure] using
          (isClosed_closure : IsClosed (closure ((toWeakSpace ℝ Y) '' s)))
      have hpreimage :
          J ⁻¹' Set.Iic c = (toWeakSpace ℝ Y) '' s := by
        ext y
        constructor
        · intro hy
          refine ⟨(toWeakSpace ℝ Y).symm y, ?_, by simp⟩
          have hy' : ‖(toWeakSpace ℝ Y).symm y - d‖ ≤ Real.sqrt c := by
            have hySq : ‖(toWeakSpace ℝ Y).symm y - d‖ ^ 2 ≤ (Real.sqrt c) ^ 2 := by
              simpa [Real.sq_sqrt hc'] using hy
            exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 hySq
          unfold s
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact hy'
        · rintro ⟨x, hx, rfl⟩
          have hx' : ‖x - d‖ ≤ Real.sqrt c := by
            unfold s at hx
            rwa [Metric.mem_closedBall, dist_eq_norm] at hx
          change ‖x - d‖ ^ 2 ≤ c
          have hxSq : ‖x - d‖ ^ 2 ≤ (Real.sqrt c) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg (x - d)) (Real.sqrt_nonneg c)).2 hx'
          simpa [Real.sq_sqrt hc'] using hxSq
      simpa [hpreimage] using hsImageClosed
  exact weakLowerSemicontinuous_of_lowerSemicontinuousWeakSpace hJ

/-- Exercise 6.9. If `F : Q → Y` is weakly continuous, then the functional
`fun q ↦ ‖F q - d‖ ^ 2` is weakly lower semicontinuous. -/
theorem residualSq_weakLowerSemicontinuous_of_weakSpaceContinuous
    (F : Q → Y) (d : Y) (hF : Continuous (toWeakMap F)) :
    weakLowerSemicontinuous (fun q : Q ↦ ‖F q - d‖ ^ 2) :=
  (norm_sub_sq_weakLowerSemicontinuous d).comp_weakSpaceContinuous hF
