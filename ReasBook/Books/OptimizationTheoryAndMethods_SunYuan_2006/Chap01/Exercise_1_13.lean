/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Semantic recall hits verified for this item: `Convex.inter`, `Convex.linear_preimage`,
-- `convex_singleton`, `EuclideanQuadrant.convex`, and `Matrix.toEuclideanLin`.
-- The coordinatewise nonnegativity constraint is the standard Euclidean quadrant set in mathlib.

section Chapter01Exercise113

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter01 Exercise 1.13: for `A : Matrix (Fin m) (Fin n) ℝ` and
`b : EuclideanSpace ℝ (Fin m)`, the feasible set
`{x : EuclideanSpace ℝ (Fin n) | Matrix.toEuclideanLin A x = b ∧ ∀ i : Fin n, 0 ≤ x i}`
is convex. -/
theorem convex_linearEqNonnegativeSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ {x : Point | Matrix.toEuclideanLin A x = b ∧ ∀ i : Fin n, 0 ≤ x i} := by
  have hFiber :
      Convex ℝ ((Matrix.toEuclideanLin A) ⁻¹' ({b} : Set (EuclideanSpace ℝ (Fin m)))) :=
    (convex_singleton b).linear_preimage (Matrix.toEuclideanLin A)
  have hOrthant : Convex ℝ {x : Point | ∀ i : Fin n, 0 ≤ x i} := by
    simpa using (EuclideanQuadrant.convex : Convex ℝ {x : Point | ∀ i : Fin n, 0 ≤ x i})
  convert hFiber.inter hOrthant using 1
  ext x
  simp [Set.preimage]

end Chapter01Exercise113
