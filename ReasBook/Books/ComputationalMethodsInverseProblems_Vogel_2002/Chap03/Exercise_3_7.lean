/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_1

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exercise 3.7. If `s` minimizes the Newton quadratic model `(3.15)` and
`hessian J f_v` is self-adjoint strongly positive, then `(3.16)` holds: the
minimizer is the explicit Newton step `-Ring.inverse (hessian J f_v)
(gradient J f_v)`. -/
theorem eq_newtonStep_of_isMinOn_quadraticModel
    (J : H → ℝ) (f_v s : H)
    (hHess : ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J f_v))
    (hmin : IsMinOn (quadraticModel J f_v) Set.univ s) :
    s = -Ring.inverse (hessian J f_v) (gradient J f_v) := by
  let L := hessian J f_v
  let g := gradient J f_v
  have hLUnit : IsUnit L := hessianIsUnit_of_selfAdjointStronglyPositive hHess
  have hnormal : g + L s = 0 :=
    normalEq_of_isMinOn_quadraticModel J f_v s hHess.isSelfAdjoint hmin
  have hLs : L s = -g := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [g, L, add_comm] using hnormal
  calc
    s = (1 : H →L[ℝ] H) s := by simp
    _ = (Ring.inverse L * L) s := by rw [Ring.inverse_mul_cancel L hLUnit]
    _ = Ring.inverse L (L s) := rfl
    _ = Ring.inverse L (-g) := by rw [hLs]
    _ = -Ring.inverse L g := by simp [g]

end Newton
