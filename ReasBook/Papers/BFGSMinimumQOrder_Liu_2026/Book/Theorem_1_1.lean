module

public import ReasLib.Optimization.BFGS.MinimumQOrder

public section

open scoped EuclideanSpace Topology

/- Theorem 1.1 (1) (Main result). For every finite dimension `n ≥ 2`, every `ε > 0`,
and every `R > 0`, there exist an explicit smooth globally strongly convex objective and
an identity-initialized nonterminating exact-line-search BFGS run that is localized in
`Metric.ball 0 R`, is Q-superlinear, and has Q-order exactly one. -/
#check (BFGS.exists_orderOneExample :
  ∀ (n : ℕ), 2 ≤ n → ∀ (ε R : ℝ), 0 < ε → 0 < R →
    ∃ (F : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
      (x : ℕ → EuclideanSpace ℝ (Fin n)) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (α : ℕ → ℝ), BFGS.IsOrderOneExample ε R F x₀ x B α)

/- Theorem 1.1 (2). Every nonterminating convergent exact-line-search BFGS trajectory
for a smooth globally strongly convex objective at a nondegenerate minimizer has Q-order
at least one, so the construction in the first clause attains the minimum possible
adjacent-iterate Q-order. -/
#check (BFGS.IsTrajectory.one_le_order :
  ∀ {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (B₀ : Matrix (Fin n) (Fin n) ℝ) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (α : ℕ → ℝ) (m : ℝ), 0 < m → ContDiff ℝ ⊤ F →
      StrongConvexOn Set.univ m F → IsMinOn F Set.univ xStar →
      (ConvexAnalysis.hessian F xStar).PosDef → BFGS.IsTrajectory F B₀ x B α →
      (∀ k, x k ≠ xStar) → Filter.Tendsto x Filter.atTop (𝓝 xStar) →
      (1 : ENNReal) ≤ QConvergence.order x xStar)
