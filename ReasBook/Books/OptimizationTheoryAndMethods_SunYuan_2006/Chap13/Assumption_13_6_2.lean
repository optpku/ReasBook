/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

open scoped Matrix.Norms.L2Operator

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: bounded Euclidean trust-region stage data for Powell-Yuan Chapter 13;
-- * sampled owner declarations:
--   `Bornology.IsBounded`,
--   `Matrix.rank`,
--   `HasQuasiNewtonGlobalConvergenceAssumptions`;
-- * best owner abstraction here: the source-facing Chapter 13 assumption package itself, with
--   `Bornology.IsBounded` reused for the geometric set `omega`, `Matrix.rank` reused for the
--   full-rank clause, and the Hessian boundedness expressed through the bounded range of the
--   shifted finite-coordinate family `k ↦ (fun i j ↦ B (k + 1) i j)`.
-- Primitive data vs derived API:
-- * primitive data: the distinguished set `omega`, iterate/trial-point containment, Jacobian
--   full-column rank on `omega`, and the bounded range of the Hessian approximations along the
--   book indices `k ≥ 1`;
-- * derived API: membership in the distinguished set `omega`.

/-- Chapter13 Assumption 13.6.2: the Powell-Yuan iterates `x k`, trial points `x k + d k`,
the Jacobian models `A y`, and the Hessian approximations `B k` satisfy the source assumptions
that there is a bounded convex closed set `omega : Set Point` containing every stage iterate
`x k` and trial point `x k + d k` for book indices `k ≥ 1`, that `A y` has full column rank
for every `y ∈ omega`, and that the matrix sequence `B k` is uniformly bounded on book indices
`k ≥ 1`, expressed through the equivalent finite-coordinate family
`fun i j ↦ (B k) i j`. -/
structure PowellYuanAssumption1362
    (x : ℕ → Point) (d : ℕ → Point) (A : Point → ConstraintMatrix) (B : ℕ → MatrixN) where
  omega : Set Point
  omega_bounded : Bornology.IsBounded omega
  omega_convex : Convex ℝ omega
  omega_closed : IsClosed omega
  iterate_mem_omega (k : ℕ) (_ : 1 ≤ k) : x k ∈ omega
  trialPoint_mem_omega (k : ℕ) (_ : 1 ≤ k) : x k + d k ∈ omega
  jacobian_fullColumnRank (y : Point) (_ : y ∈ omega) : Matrix.rank (A y) = m
  matrix_bounded :
    Bornology.IsBounded
      (Set.range fun k : ℕ ↦ (fun i j ↦ B (k + 1) i j : Fin n → Fin n → ℝ))

/-- Membership in `PowellYuanAssumption1362 x d A B` is membership in the distinguished bounded
convex closed set `omega` from Chapter13 Assumption 13.6.2. -/
instance instMembershipPointPowellYuanAssumption1362
    {x : ℕ → Point} {d : ℕ → Point} {A : Point → ConstraintMatrix} {B : ℕ → MatrixN} :
    Membership Point (PowellYuanAssumption1362 x d A B) where
  mem h y := y ∈ h.omega

end
