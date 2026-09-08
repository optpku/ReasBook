module

public import ReasLib.Optimization.BFGS.Trajectory

public section

universe u

#check (BFGS.IsTrajectory :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    (EuclideanSpace ℝ ι → ℝ) → Matrix ι ι ℝ →
      (ℕ → EuclideanSpace ℝ ι) → (ℕ → Matrix ι ι ℝ) → (ℕ → ℝ) → Prop)
