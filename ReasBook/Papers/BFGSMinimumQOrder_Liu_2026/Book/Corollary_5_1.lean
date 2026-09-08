module

public import ReasLib.Optimization.BFGS.MinimumQOrder.ConvexBroyden

public section

/- Corollary 5.1 (1) (Convex Broyden class). Every parameter sequence in `Set.Icc 0 1`
admits an identity-initialized exact-line-search convex Broyden trajectory on the point
sequence of the order-one BFGS example. -/
#check (BFGS.IsOrderOneExample.existsBroydenTrajectory :
  ∀ {n : ℕ} {ε R : ℝ}
      {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
      {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
      {α : ℕ → ℝ},
    BFGS.IsOrderOneExample ε R F x₀ x B α →
      ∀ (φ : ℕ → ℝ), (∀ k, φ k ∈ Set.Icc (0 : ℝ) 1) →
        ∃ (Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ) (αφ : ℕ → ℝ),
          Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) x Bφ αφ)

/- Corollary 5.1 (2). Every identity-initialized exact-line-search convex Broyden
trajectory starting at `x₀` has the same point sequence as the BFGS example. -/
#check (BFGS.IsOrderOneExample.broydenPoints_eq :
  ∀ {n : ℕ} {ε R : ℝ}
      {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
      {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
      {α : ℕ → ℝ},
    BFGS.IsOrderOneExample ε R F x₀ x B α →
      ∀ {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
          {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ},
        Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ →
          xφ 0 = x₀ → xφ = x)

/- Corollary 5.1 (3). An equally initialized exact-line-search convex Broyden
trajectory for the order-one example never reaches the origin. -/
#check (BFGS.IsOrderOneExample.broydenNonterminating :
  ∀ {n : ℕ} {ε R : ℝ}
      {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
      {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
      {α : ℕ → ℝ},
    BFGS.IsOrderOneExample ε R F x₀ x B α →
      ∀ {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
          {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ},
        Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ →
          xφ 0 = x₀ → ∀ k, xφ k ≠ 0)

/- Corollary 5.1 (4). An equally initialized exact-line-search convex Broyden
trajectory for the order-one example converges Q-superlinearly to the origin. -/
#check (BFGS.IsOrderOneExample.broydenSuperlinear :
  ∀ {n : ℕ} {ε R : ℝ}
      {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
      {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
      {α : ℕ → ℝ},
    BFGS.IsOrderOneExample ε R F x₀ x B α →
      ∀ {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
          {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ},
        Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ →
          xφ 0 = x₀ → QConvergence.IsSuperlinear xφ 0)

/- Corollary 5.1 (5). An equally initialized exact-line-search convex Broyden
trajectory for the order-one example has Q-order exactly one at the origin. -/
#check (BFGS.IsOrderOneExample.broydenOrder_eq_one :
  ∀ {n : ℕ} {ε R : ℝ}
      {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
      {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
      {α : ℕ → ℝ},
    BFGS.IsOrderOneExample ε R F x₀ x B α →
      ∀ {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
          {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ},
        Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ →
          xφ 0 = x₀ → QConvergence.order xφ 0 = (1 : ENNReal))
