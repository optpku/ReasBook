module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import ReasLib.Optimization.DFP.Polar.Recurrence

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar.Parameters

/-- The even radius given by the tail product of both radius factors in each later cycle. -/
def evenRadius (p : Parameters) (j : ℕ) : ℝ :=
  ∏' n : ℕ, p.radiusRatio (2 * (j + n)) * p.radiusRatio (2 * (j + n) + 1)

/-- The shifted tail-product formula defining the even radius. -/
theorem evenRadius_def (p : Parameters) (j : ℕ) :
    p.evenRadius j =
      ∏' n : ℕ, p.radiusRatio (2 * (j + n)) * p.radiusRatio (2 * (j + n) + 1) := by
  -- Unfolding `evenRadius` exposes the prescribed tail product verbatim.
  rfl

/-- The odd radius obtained by dividing an even radius by its first-stage factor. -/
def oddRadius (p : Parameters) (j : ℕ) : ℝ :=
  p.evenRadius j / p.radiusRatio (2 * j)

/-- The quotient formula defining the odd radius. -/
theorem oddRadius_def (p : Parameters) (j : ℕ) :
    p.oddRadius j = p.evenRadius j / p.radiusRatio (2 * j) := by
  -- Unfolding `oddRadius` gives the prescribed quotient without side conditions.
  rfl

/-- The full radius sequence interleaving the prescribed even and odd radii. -/
def radius (p : Parameters) : ℕ → ℝ :=
  DFP.twoStepSequence p.evenRadius p.oddRadius

/-- The even terms of the radius sequence are the prescribed tail products. -/
@[simp]
theorem radius_even (p : Parameters) (j : ℕ) :
    p.radius (2 * j) = p.evenRadius j := by
  -- Project the even entry from the interleaved two-step radius sequence.
  simpa only [radius] using DFP.twoStepSequence_even p.evenRadius p.oddRadius j

/-- The odd terms of the radius sequence are the prescribed quotients. -/
@[simp]
theorem radius_odd (p : Parameters) (j : ℕ) :
    p.radius (2 * j + 1) = p.oddRadius j := by
  -- Project the odd entry from the interleaved two-step radius sequence.
  simpa only [radius] using DFP.twoStepSequence_odd p.evenRadius p.oddRadius j

/-- The planar point sequence in unreduced polar coordinates. -/
def point (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.radius k • DFP.Polar.polarUnit (p.angle k)

/-- The polar-coordinate formula defining the point sequence. -/
theorem point_def (p : Parameters) (k : ℕ) :
    p.point k = p.radius k • DFP.Polar.polarUnit (p.angle k) := by
  -- Unfolding `point` preserves the unreduced polar angle and radial scaling.
  rfl

/-- The gradient sequence obtained by applying the radial multiplier `ζ_k`. -/
def gradient (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.zeta k • p.point k

/-- The radial-multiplier formula defining the gradient sequence. -/
theorem gradient_def (p : Parameters) (k : ℕ) :
    p.gradient k = p.zeta k • p.point k := by
  -- Unfolding `gradient` exposes the prescribed radial multiplier.
  rfl

/-- The inverse-Hessian sequence obtained by rotating each inverse local matrix into fixed
coordinates. -/
def inverseHessian (p : Parameters) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.Polar.rotationMatrix (p.angle k) * (p.matrix k)⁻¹ *
    (DFP.Polar.rotationMatrix (p.angle k)).transpose

/-- The rotated inverse-local-matrix formula defining the inverse-Hessian sequence. -/
theorem inverseHessian_def (p : Parameters) (k : ℕ) :
    p.inverseHessian k =
      DFP.Polar.rotationMatrix (p.angle k) * (p.matrix k)⁻¹ *
        (DFP.Polar.rotationMatrix (p.angle k)).transpose := by
  -- Unfolding `inverseHessian` retains the stated rotation and multiplication order.
  rfl

end DFP.Polar.Parameters
