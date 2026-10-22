/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_16.Instances

public section

noncomputable section

namespace EuclideanSpace

universe u

/-- Exercise 9.16. The book's coordinatewise product `u. * v` is the canonical
pointwise multiplication `u * v` on `EuclideanSpace ℝ ι`, and the Euclidean
inner product satisfies `inner ℝ x (u * v) = inner ℝ (u * x) v`. -/
theorem inner_pointwiseMul_right {ι : Type u} [Fintype ι]
    (x u v : EuclideanSpace ℝ ι) :
    inner ℝ x (u * v) = inner ℝ (u * x) v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_assoc, mul_comm]

end EuclideanSpace
