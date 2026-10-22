/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.4.19 is source-facing at the Euclidean matrix view of the Hessian from
`Definition_1_4_16`, but its canonical operator owner is already intrinsic to real Hilbert spaces.

Sampled owner-style declarations:
* `hessian` from `Definition_1_4_16`
* `ContDiffAt.isSymmSndFDerivAt`
* `ContinuousLinearMap.IsSymmetric`
* `hessianMatrix` and `Matrix.IsSymm`

Core owner abstraction:
* `(hessian f x).IsSymmetric`

Bridge/view API:
* the Euclidean-coordinate Hessian matrix
-/

private theorem inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt
    {f : E → ℝ} {x v w : E} (hf : ContDiffAt ℝ 2 f x) :
    inner ℝ v (fderiv ℝ (∇ f) x w) = fderiv ℝ (fderiv ℝ f) x w v := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hgrad : fderiv ℝ (∇ f) x = D.comp (fderiv ℝ (fderiv ℝ f) x) := by
    simpa [D, gradient] using fderiv_comp x D.differentiableAt hfdiff
  have hdual (φ : StrongDual ℝ E) (v : E) : inner ℝ v (D φ) = φ v := by
    dsimp [D]
    rw [real_inner_comm]
    change ((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φ)) v = φ v
    simp
  calc
    inner ℝ v (fderiv ℝ (∇ f) x w) = inner ℝ v (D ((fderiv ℝ (fderiv ℝ f) x) w)) := by
      rw [hgrad]
      simp [D]
    _ = (fderiv ℝ (fderiv ℝ f) x w) v := hdual _ _

/-- Under a `C²` hypothesis, the intrinsic Hessian operator `hessian f x` is symmetric. -/
theorem fderiv_gradient_isSymmetric_of_contDiffAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    (hessian f x).IsSymmetric := by
  have hsymm := hf.isSymmSndFDerivAt (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  intro v w
  calc
    inner ℝ (hessian f x v) w = inner ℝ w (hessian f x v) := by
      rw [real_inner_comm]
    _ = fderiv ℝ (fderiv ℝ f) x v w := inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt hf
    _ = fderiv ℝ (fderiv ℝ f) x w v := hsymm.eq _ _
    _ = inner ℝ v (hessian f x w) :=
      (inner_fderiv_gradient_eq_sndFDeriv_of_contDiffAt hf).symm

section

variable {n : ℕ}

local notation "EFin" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Theorem 1.4.19: if `f : ℝⁿ → ℝ` is twice continuously differentiable at `x`, then the Hessian
matrix of `f` at `x` is symmetric. -/
theorem hessianMatrix_isSymm_of_contDiffAt {f : EFin → ℝ} {x : EFin}
    (hf : ContDiffAt ℝ 2 f x) :
    (∇² f x).IsSymm := by
  have hH := fderiv_gradient_isSymmetric_of_contDiffAt hf
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  calc
    ∇² f x j i = inner ℝ (hessian f x (e i)) (e j) := by
          rw [hessianMatrix_apply, real_inner_comm]
    _ = inner ℝ (e i) (hessian f x (e j)) := hH _ _
    _ = ∇² f x i j := by
          rw [hessianMatrix_apply]

end

end
