/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

open scoped Matrix

namespace Landweber

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The Landweber iteration matrix `G = I - τ Kᵀ K`. -/
def iterationMatrix (K : Matrix n n ℝ) (τ : ℝ) : Matrix n n ℝ :=
  1 - τ • (Kᵀ * K)

/-- The zero-start finite-dimensional Landweber iterate for data `d`. -/
def iterate (K : Matrix n n ℝ) (τ : ℝ) (d : EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n
  | 0 => 0
  | v + 1 =>
      Matrix.toEuclideanLin (iterationMatrix K τ) (iterate K τ d v) +
        Matrix.toEuclideanLin (τ • Kᵀ) d

/-- The defining formula for `Landweber.iterationMatrix`. -/
theorem iterationMatrix_def (K : Matrix n n ℝ) (τ : ℝ) :
    iterationMatrix K τ = 1 - τ • (Kᵀ * K) := by
  -- This theorem restates the definition of `iterationMatrix`.
  rfl

/-- The zero-start initial condition for `Landweber.iterate`. -/
theorem iterate_zero (K : Matrix n n ℝ) (τ : ℝ) (d : EuclideanSpace ℝ n) :
    iterate K τ d 0 = 0 := by
  -- The recursive definition assigns the zero vector at step `0`.
  rfl

/-- The recursive step equation for `Landweber.iterate`. -/
theorem iterate_succ (K : Matrix n n ℝ) (τ : ℝ) (d : EuclideanSpace ℝ n) (v : ℕ) :
    iterate K τ d (v + 1) =
      Matrix.toEuclideanLin (iterationMatrix K τ) (iterate K τ d v) +
        Matrix.toEuclideanLin (τ • Kᵀ) d := by
  -- The successor case is the defining recursion for `iterate`.
  rfl

end Landweber
