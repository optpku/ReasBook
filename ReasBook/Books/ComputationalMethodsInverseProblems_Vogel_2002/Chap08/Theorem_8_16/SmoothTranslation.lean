/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace VariationalRegularization.BVCompactness

/-- The fundamental theorem of calculus and translation invariance of volume
bound the `L¹` displacement of a smooth function by its gradient integral. -/
lemma smooth_integral_norm_translate_sub_le {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (a : EuclideanSpace ℝ (Fin d)) :
    (∫ x, ‖g (x + a) - g x‖) ≤ (∫ x, ‖fderiv ℝ g x‖) * ‖a‖ := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let F : ℝ × (EuclideanSpace ℝ (Fin d)) → ℝ := fun p ↦ ‖fderiv ℝ g (p.2 + p.1 • a)‖ * ‖a‖
  have hd : Integrable (fun x ↦ ‖fderiv ℝ g x‖) :=
    (hg.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport (hc.fderiv ℝ).norm
  have hFcont : Continuous F := by
    exact (((hg.continuous_fderiv one_ne_zero).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).norm).mul continuous_const
  have hFi : Integrable F (ν.prod volume) := by
    apply (integrable_prod_iff hFcont.aestronglyMeasurable).2
    refine ⟨.of_forall (fun t ↦ (hd.comp_add_right (t • a)).mul_const ‖a‖), ?_⟩
    have heq : (fun t ↦ ∫ x, ‖F (t, x)‖) =
        fun _ : ℝ ↦ (∫ x, ‖fderiv ℝ g x‖) * ‖a‖ := by
      funext t
      simp only [F, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
        integral_mul_const]
      rw [integral_add_right_eq_self (fun x : (EuclideanSpace ℝ (Fin d)) ↦ ‖fderiv ℝ g x‖) (t • a)]
    rw [heq]
    exact integrable_const _
  have hpoint (x : (EuclideanSpace ℝ (Fin d))) : ‖g (x + a) - g x‖ ≤ ∫ t, F (t, x) ∂ν := by
    have hp : ContDiff ℝ 1 (fun t : ℝ ↦ g (x + t • a)) :=
      hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have hder (t : ℝ) : deriv (fun t : ℝ ↦ g (x + t • a)) t =
        fderiv ℝ g (x + t • a) a := by
      have hin := (hasDerivAt_id t).smul_const a
      simpa only [Function.comp_def, id_eq, one_smul] using
        ((hg.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
          (hin.const_add x)).deriv
    have hB : IntervalIntegrable (fun t : ℝ ↦ F (t, x)) volume 0 1 :=
      (hFcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun t : ℝ ↦ g (x + t • a))
      (B := fun t ↦ F (t, x)) (by norm_num : (0 : ℝ) ≤ 1) hp.continuous.continuousOn
      (hp.differentiable one_ne_zero).differentiableOn
      (.of_forall fun t _ ↦ by
        rw [hder]
        exact (fderiv ℝ g (x + t • a)).le_opNorm a) hB
    simpa only [zero_smul, add_zero, one_smul, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ν]
      using h
  have hgInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hmono := integral_mono ((hgInt.comp_add_right a).sub hgInt).norm
    hFi.integral_prod_right hpoint
  refine hmono.trans_eq ?_
  rw [integral_integral_swap (f := fun x t ↦ F (t, x)) hFi.swap]
  simp only [F, integral_mul_const]
  simp_rw [integral_add_right_eq_self (fun x : (EuclideanSpace ℝ (Fin d)) ↦ ‖fderiv ℝ g x‖)]
  simp [ν]

end VariationalRegularization.BVCompactness
