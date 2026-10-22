/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.Normed.Operator.NormedSpace
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 4.2.7: a real-valued function has Lipschitz-continuous Hessian with constant `L₃`
when it is twice continuously differentiable and its second Fréchet derivative
`x ↦ fderiv ℝ (fderiv ℝ f) x` is globally `L₃`-Lipschitz in operator norm. On real Hilbert
spaces, the usual Hessian-operator surface is recovered by the derived theorem
`HasLipschitzContinuousHessian.lipschitz`. -/
class HasLipschitzContinuousHessian (L3 : NNReal) (f : E → ℝ) : Prop where
  /-- The function is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 f
  /-- The second Fréchet derivative is globally `L₃`-Lipschitz in operator norm. -/
  sndFDeriv_lipschitz : LipschitzWith L3 (fun x ↦ fderiv ℝ (fderiv ℝ f) x)

/- The source-facing textbook surface for `HasLipschitzContinuousHessian M f` is the class
`C_M^{2,2}`. The owner file provides that notation directly so nearby theorem surfaces can use the
standard notation instead of a second downstream wrapper. -/
set_option quotPrecheck false in
notation "C22[" M "]" => {f | HasLipschitzContinuousHessian M f}

/-- The defining inequality for a Lipschitz-continuous Hessian is the operator-norm estimate
`‖D²f(x) - D²f(y)‖ ≤ L₃ ‖x - y‖` for the second Fréchet derivative. -/
theorem HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le
    {L3 : NNReal} {f : E → ℝ} (hf : f ∈ C22[L3]) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ (L3 : ℝ) * ‖x - y‖ := by
  simpa using hf.sndFDeriv_lipschitz.norm_sub_le x y

section Hilbert

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

namespace HasLipschitzContinuousHessian

private abbrev rieszToPrimal : StrongDual ℝ X →L[ℝ] X :=
  (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem hessian_eq_riesz_sndFDeriv
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ 2 f x) :
    hessian f x = rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) x) := by
  let D : StrongDual ℝ X →L[ℝ] X := rieszToPrimal
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  simpa [D, gradient, hessian] using fderiv_comp x D.differentiableAt hfdiff

/-- On a real Hilbert space, `f ∈ C22[L₃]` recovers the textbook global Hessian-Lipschitz bound
`LipschitzWith L₃ (hessian f)`. -/
theorem lipschitz
    {L3 : NNReal} {f : X → ℝ} (hf : f ∈ C22[L3]) :
    LipschitzWith L3 (hessian f) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [hessian_eq_riesz_sndFDeriv (hf.contDiff.contDiffAt (x := x)),
    hessian_eq_riesz_sndFDeriv (hf.contDiff.contDiffAt (x := y))]
  calc
    ‖(rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) x)) -
        (rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) y))‖
        =
          ‖rieszToPrimal.comp
            (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)‖ := by
          rw [ContinuousLinearMap.comp_sub]
    _ = ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
          simpa using LinearIsometry.norm_toContinuousLinearMap_comp
            (InnerProductSpace.toDual ℝ X).symm.toLinearIsometry
            (g := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)
    _ ≤ (L3 : ℝ) * ‖x - y‖ :=
      HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y

/-- On a real Hilbert space, the defining inequality for `f ∈ C22[L₃]` is the operator-norm
estimate `‖∇² f(x) - ∇² f(y)‖ ≤ L₃ ‖x - y‖`. -/
theorem norm_sub_le
    {L3 : NNReal} {f : X → ℝ} (hf : f ∈ C22[L3]) (x y : X) :
    ‖hessian f x - hessian f y‖ ≤ (L3 : ℝ) * ‖x - y‖ := by
  simpa using HasLipschitzContinuousHessian.lipschitz hf |>.norm_sub_le x y

end HasLipschitzContinuousHessian

end Hilbert
