/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

-- Proof sketch: scale the owner fields directly. Openness is unchanged, `C³` regularity is
-- preserved by `ContDiffOn.const_smul`, convexity by `ConvexOn.smul`, the third directional
-- derivative scales linearly with `α`, and the Hessian local norm scales by `√α`.
/-- Corollary 5.1.3: if `f` is self-concordant on `dom` with constant `Mf`, then for every
positive scalar `α` the rescaled function `(α : ℝ) • f` is self-concordant on the same domain
with constant `Mf / √α`. -/
theorem pos_smul
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf f) (α : NNReal) (hα : 0 < α) :
    IsSelfConcordantOnWith dom (Mf / NNReal.sqrt α) ((α : ℝ) • f) := by
  have hα_real : 0 < (α : ℝ) := NNReal.coe_pos.mpr hα
  have hα_nonneg : 0 ≤ (α : ℝ) := le_of_lt hα_real
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := by
        simpa using h.contDiffOn.const_smul (α : ℝ)
      convexOn := by
        simpa using ConvexOn.smul hα_nonneg h.convexOn
      third_deriv_bound := ?_ }
  intro x hx u
  have hthird :
      thirdDirectionalDerivative (((α : ℝ) • f)) x u =
        (α : ℝ) * thirdDirectionalDerivative f x u := by
    rw [thirdDirectionalDerivative]
    have hs : directionalSlice (((α : ℝ) • f)) x u = (α : ℝ) • directionalSlice f x u := by
      funext t
      simp [directionalSlice]
    rw [hs, iteratedDeriv_const_smul_field]
    simp [thirdDirectionalDerivative, smul_eq_mul]
  have hnorm :
      hessianLocalNorm ((α : ℝ) • f) x u = Real.sqrt α * ‖u‖[f; x] := by
    have hhess : hessian (((α : ℝ) • f)) = (α : ℝ) • hessian f := by
      funext y
      unfold hessian
      rw [show ∇ (((α : ℝ) • f)) = (α : ℝ) • ∇ f by
        funext z
        unfold gradient
        rw [fderiv_const_smul_field]
        exact (InnerProductSpace.toDual ℝ E).symm.map_smul (α : ℝ) (fderiv ℝ f z)]
      rw [fderiv_const_smul_field]
    rw [hessianLocalNorm_def, hessianLocalNorm_def, hhess]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right]
    rw [Real.sqrt_mul hα_nonneg]
  calc
    |thirdDirectionalDerivative (((α : ℝ) • f)) x u|
        = (α : ℝ) * |thirdDirectionalDerivative f x u| := by
            rw [hthird, abs_mul, abs_of_nonneg hα_nonneg]
    _ ≤ (α : ℝ) * (2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) := by
      gcongr
      exact h.third_deriv_bound hx u
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) * (Real.sqrt α * ‖u‖[f; x]) ^ (3 : ℕ) := by
      rw [NNReal.coe_div, Real.coe_sqrt]
      have hsqrt_ne : Real.sqrt (α : ℝ) ≠ 0 := by
        exact Real.sqrt_ne_zero'.2 hα_real
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt hα_nonneg]
      ring
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) * hessianLocalNorm ((α : ℝ) • f) x u ^ (3 : ℕ) := by
      rw [hnorm]

end IsSelfConcordantOnWith

end
