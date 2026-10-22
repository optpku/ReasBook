/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_22.WeakSeqTendsto
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

public section

universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Any fixed inner-product coefficient of an orthonormal sequence tends to `0`. -/
theorem orthonormal_tendsto_inner_right_zero {f : ℕ → H} (hf : Orthonormal ℝ f) (g : H) :
    Filter.Tendsto (fun n ↦ ⟪f n, g⟫_ℝ) Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun n ↦ ‖⟪f n, g⟫_ℝ‖ ^ 2) Filter.atTop (nhds 0) :=
    (hf.inner_products_summable g).tendsto_atTop_zero
  have hnorm : Filter.Tendsto (fun n ↦ ‖⟪f n, g⟫_ℝ‖) Filter.atTop (nhds 0) := by
    have hsqrt :
        Filter.Tendsto (fun n ↦ Real.sqrt (‖⟪f n, g⟫_ℝ‖ ^ 2)) Filter.atTop
          (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm

/-- Example 2.23 (1). Any orthonormal sequence in a real Hilbert space converges weakly to `0`;
the textbook sine family `f n x = sin (2 * n * π * x) / √2` in `L²(0,1)` is an illustrative
instance of this general fact. -/
theorem orthonormal_weakSeqTendsto_zero [CompleteSpace H] {f : ℕ → H} (hf : Orthonormal ℝ f) :
    weakSeqTendsto f 0 := by
  rw [weakSeqTendsto_iff_forall_inner_tendsto]
  intro g
  simpa using orthonormal_tendsto_inner_right_zero hf g

/-- Example 2.23 (2). An orthonormal sequence in a real Hilbert space does not converge strongly
to `0`. In the textbook example this is witnessed by the constant norm identity `‖f n‖ = 1`. -/
theorem orthonormal_not_tendsto_zero {f : ℕ → H} (hf : Orthonormal ℝ f) :
    ¬ Filter.Tendsto f Filter.atTop (nhds 0) := by
  intro hf_zero
  have hnorm : Filter.Tendsto (fun n ↦ ‖f n‖) Filter.atTop (nhds (0 : ℝ)) := by
    exact tendsto_zero_iff_norm_tendsto_zero.1 hf_zero
  simp [hf.norm_eq_one] at hnorm
