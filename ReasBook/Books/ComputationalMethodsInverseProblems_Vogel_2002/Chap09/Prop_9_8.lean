/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_19.EuclideanQuadrant
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_21
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_38

public section

noncomputable section

variable {n : ℕ}
variable {J : EuclideanSpace ℝ (Fin n) → ℝ}
variable {fStar : EuclideanSpace ℝ (Fin n)}

namespace NonnegativeOrthant

private theorem mem_feasibleSet_apply
    (hf : fStar ∈ feasibleSet n)
    (i : Fin n) :
    0 ≤ fStar i :=
  (mem_feasibleSet.mp hf) i

/-- Proposition 9.8 (1). If `J` is continuously differentiable and `fStar` is a local
minimizer of `(9.16)` on the nonnegative orthant, then each coordinate of
`gradient J fStar` is nonnegative. -/
theorem gradient_nonneg
    (hJ : ContDiff ℝ 1 J)
    (hfStar : fStar ∈ feasibleSet n)
    (hmin : IsLocalMinOn J (feasibleSet n) fStar)
    (i : Fin n) :
    0 ≤ gradient J fStar i := by
  have hconvex : Convex ℝ (feasibleSet n) := by
    convert
      (EuclideanQuadrant.convex :
        Convex ℝ { x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i }) using 1
    ext f
    exact mem_feasibleSet
  have hstep_mem : fStar + EuclideanSpace.single i (1 : ℝ) ∈ feasibleSet n := by
    rw [mem_feasibleSet]
    intro j
    by_cases hji : j = i
    · simpa [EuclideanSpace.single, hji] using
        add_nonneg (mem_feasibleSet_apply hfStar j) zero_le_one
    · simpa [EuclideanSpace.single, hji] using mem_feasibleSet_apply hfStar j
  have hnonneg :=
    inner_gradient_sub_nonneg_of_isLocalMinOn J hconvex hfStar hmin
      (hJ.contDiffAt.differentiableAt one_ne_zero)
      hstep_mem
  simpa [gradient_apply_eq_fderiv_single J fStar i, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hnonneg

/-- Proposition 9.8 (2). The feasible-point hypothesis for `(9.16)` gives
coordinatewise nonnegativity of `fStar`. -/
theorem coordinate_nonneg
    (hfStar : fStar ∈ feasibleSet n)
    (i : Fin n) :
    0 ≤ fStar i :=
  mem_feasibleSet_apply hfStar i

/-- Proposition 9.8 (3). If `J` is continuously differentiable and `fStar` is a local
minimizer of `(9.16)` on the nonnegative orthant, then each coordinate satisfies the
complementarity relation `fStar i * gradient J fStar i = 0`. -/
theorem complementarity
    (hJ : ContDiff ℝ 1 J)
    (hfStar : fStar ∈ feasibleSet n)
    (hmin : IsLocalMinOn J (feasibleSet n) fStar)
    (i : Fin n) :
    fStar i * gradient J fStar i = 0 := by
  have hconvex : Convex ℝ (feasibleSet n) := by
    convert
      (EuclideanQuadrant.convex :
        Convex ℝ { x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i }) using 1
    ext f
    exact mem_feasibleSet
  have hzero_mem : fStar - EuclideanSpace.single i (fStar i) ∈ feasibleSet n := by
    rw [mem_feasibleSet]
    intro j
    by_cases hji : j = i
    · simp [EuclideanSpace.single, hji]
    · simpa [EuclideanSpace.single, hji] using mem_feasibleSet_apply hfStar j
  have hneg :=
    inner_gradient_sub_nonneg_of_isLocalMinOn J hconvex hfStar hmin
      (hJ.contDiffAt.differentiableAt one_ne_zero)
      hzero_mem
  have hnonpos : 0 ≤ -(fStar i * gradient J fStar i) := by
    rw [show fStar - EuclideanSpace.single i (fStar i) - fStar =
        -EuclideanSpace.single i (fStar i) by
          ext j
          by_cases hji : j = i <;> simp [EuclideanSpace.single, hji]] at hneg
    have hsingle :
        EuclideanSpace.single i (fStar i) =
          fStar i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i <;> simp [EuclideanSpace.single, hji]
    have hnonpos' : (fderiv ℝ J fStar) (EuclideanSpace.single i (fStar i)) ≤ 0 := by
      simpa [EuclideanSpace.inner_single_right, mul_comm, mul_left_comm, mul_assoc] using hneg
    rw [hsingle, map_smul] at hnonpos'
    simpa [neg_nonneg, gradient_apply_eq_fderiv_single J fStar i, smul_eq_mul, mul_comm] using
      hnonpos'
  have hle : fStar i * gradient J fStar i ≤ 0 := by
    exact neg_nonneg.mp hnonpos
  have hge : 0 ≤ fStar i * gradient J fStar i := by
    exact mul_nonneg
      (coordinate_nonneg hfStar i)
      (gradient_nonneg hJ hfStar hmin i)
  exact le_antisymm hle hge

end NonnegativeOrthant
