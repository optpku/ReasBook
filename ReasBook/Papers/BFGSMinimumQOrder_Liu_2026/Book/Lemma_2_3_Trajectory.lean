/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import ReasLib.Optimization.BFGS.Trajectory

public section

universe u

#check (BFGS.IsTrajectory :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    (EuclideanSpace ℝ ι → ℝ) → Matrix ι ι ℝ →
      (ℕ → EuclideanSpace ℝ ι) → (ℕ → Matrix ι ι ℝ) → (ℕ → ℝ) → Prop)
