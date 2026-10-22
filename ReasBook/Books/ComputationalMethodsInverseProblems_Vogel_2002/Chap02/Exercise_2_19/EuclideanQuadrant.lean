/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real

public section

namespace EuclideanQuadrant

/-- The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is closed. -/
theorem isClosed_nonnegativeOrthant (n : ℕ) :
    IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
  rw [← range_euclideanQuadrant]
  exact (modelWithCornersEuclideanQuadrant n).isClosed_range

end EuclideanQuadrant
