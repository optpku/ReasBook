/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import Mathlib.Analysis.LocallyConvex.WeakSpace

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_24
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_23

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 2.25 (1). The Hilbert-space norm functional `fun f : H ↦ ‖f‖` is weakly lower
semicontinuous in the sense of Definition 2.24. -/
theorem norm_weakLowerSemicontinuous :
    weakLowerSemicontinuous (fun f : H ↦ ‖f‖) := by
  refine weakLowerSemicontinuous_of_lowerSemicontinuousWeakSpace ?_
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c < 0
  · have hpreimage :
        (fun x : WeakSpace ℝ H ↦ ‖(toWeakSpace ℝ H).symm x‖) ⁻¹' Set.Iic c = ∅ := by
      ext x
      constructor
      · intro hx
        have hnonneg : 0 ≤ ‖(toWeakSpace ℝ H).symm x‖ := norm_nonneg _
        exact False.elim ((not_le_of_gt hc) (le_trans hnonneg hx))
      · intro hx
        cases hx
    simp [hpreimage]
  · have hc' : 0 ≤ c := le_of_not_gt hc
    let s : Set H := Metric.closedBall 0 c
    have hsClosed : IsClosed s := by
      simpa [s] using Metric.isClosed_closedBall
    have hsConvex : Convex ℝ s := by
      simpa [s] using convex_closedBall (0 : H) c
    have hsImageClosed : IsClosed ((toWeakSpace ℝ H) '' s) := by
      have hclosure : closure ((toWeakSpace ℝ H) '' s) = (toWeakSpace ℝ H) '' s := by
        rw [← hsConvex.toWeakSpace_closure ℝ, hsClosed.closure_eq]
      simpa [hclosure] using
        (isClosed_closure : IsClosed (closure ((toWeakSpace ℝ H) '' s)))
    have hpreimage :
        (fun x : WeakSpace ℝ H ↦ ‖(toWeakSpace ℝ H).symm x‖) ⁻¹' Set.Iic c =
          (toWeakSpace ℝ H) '' s := by
      ext x
      constructor
      · intro hx
        refine ⟨(toWeakSpace ℝ H).symm x, ?_, by simp⟩
        unfold s
        rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      · rintro ⟨x, hx, rfl⟩
        unfold s at hx
        rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    simpa [hpreimage] using hsImageClosed

/-- Example 2.25 (2). An orthonormal sequence witnesses that the norm functional is not weakly
sequentially continuous at `0`: the sequence converges weakly to `0`, but its norms do not
converge to `0`. This is the strictness phenomenon behind Example 2.25 (1). -/
theorem norm_not_weakSeqContinuous_zero_of_orthonormal [CompleteSpace H] {f : ℕ → H}
    (hf : Orthonormal ℝ f) :
    weakSeqTendsto f 0 ∧
      ¬ Filter.Tendsto (fun n ↦ ‖f n‖) Filter.atTop (nhds (0 : ℝ)) := by
  refine ⟨orthonormal_weakSeqTendsto_zero hf, ?_⟩
  intro hnorm
  exact orthonormal_not_tendsto_zero hf (tendsto_zero_iff_norm_tendsto_zero.2 hnorm)
