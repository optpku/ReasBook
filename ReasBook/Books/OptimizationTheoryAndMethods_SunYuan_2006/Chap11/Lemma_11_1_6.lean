/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Filter

section Chapter11Lemma1116

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- The source-facing layer here is the iterate-level convergence statement. The core reusable
-- owners are Chapter 1's `IsDescentDirectionAt` for descent directions and mathlib's canonical
-- angle owner `InnerProductGeometry.angle` for the angle between the search direction and the
-- negative gradient. The companion API
-- `IsDescentDirectionAt.direction_ne` / `IsDescentDirectionAt.gradient_ne` keeps the angle term
-- on its intended nondegenerate domain without duplicating separate public nonzero hypotheses.

/- Companion API for the source angle term: the descent-direction owner already keeps both
arguments of `InnerProductGeometry.angle` nonzero along the iterate sequence. -/
/-- The descent-direction hypothesis makes every search direction nonzero. -/
theorem searchDirection_ne_of_descent
    (f : Point → ℝ) (x d : ℕ → Point)
    (h_descent : ∀ k : ℕ, IsDescentDirectionAt f (x k) (d k)) :
    ∀ k : ℕ, d k ≠ 0 :=
  fun k ↦ (h_descent k).direction_ne

/-- The descent-direction hypothesis makes every iterate gradient nonzero. -/
theorem gradient_ne_of_descent
    (f : Point → ℝ) (x d : ℕ → Point)
    (h_descent : ∀ k : ℕ, IsDescentDirectionAt f (x k) (d k)) :
    ∀ k : ℕ, gradient f (x k) ≠ 0 :=
  fun k ↦ (h_descent k).gradient_ne

/-- Chapter11 Lemma 11.1.6: for an unconstrained optimization problem on `ℝ^n`, let
`f : Point → ℝ` be twice continuously differentiable and uniformly, equivalently strongly,
convex on `ℝ^n` with modulus `m > 0`. Let `x`, `d`, and `α` be the iterates, search
directions, and positive line-search step sizes of a method satisfying
`x (k + 1) = x k + α k • d k`, and assume every `d k` is a descent direction at `x k`,
formalized by the Chapter 1 owner `IsDescentDirectionAt f (x k) (d k)`. The companion lemmas
`searchDirection_ne_of_descent` and `gradient_ne_of_descent` record that this keeps both vectors
in the source angle formula nonzero. If

`∑' k, (Real.cos (InnerProductGeometry.angle (d k) (-gradient f (x k))))^2`

is finite, i.e. `∑_{k=1}^∞ cos^2 θ_k < ∞` in the source notation up to the harmless finite
initial-index convention difference between the source and Lean's `ℕ` indexing, then
`liminf ‖gradient f (x_k)‖ > 0`. -/
theorem liminf_gradientNorm_pos_of_summable_cos_angle_sq_of_strongConvex
    (f : Point → ℝ) (m : ℝ) (x d : ℕ → Point) (α : ℕ → ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m f)
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_alpha_pos : ∀ k : ℕ, 0 < α k)
    (h_descent : ∀ k : ℕ, IsDescentDirectionAt f (x k) (d k))
    (h_summable :
      Summable
        (fun k : ℕ ↦
          (Real.cos (InnerProductGeometry.angle (d k) (-gradient f (x k)))) ^ (2 : ℕ))) :
    0 < liminf (fun k : ℕ ↦ ‖gradient f (x k)‖) atTop := sorry

end Chapter11Lemma1116
