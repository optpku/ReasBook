module

public import Book.Lemma_3_2
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Convergence

public section

/- Remark 3.3 (1). The adjacent-radius decay in an alternating-scale construction
yields Q-superlinear convergence of its gradient sequence to zero. -/
#check (PlanarGradient.IsAlternatingScale.isSuperlinear :
  ∀ {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ},
    PlanarGradient.IsAlternatingScale σ g δ a b → QConvergence.IsSuperlinear g 0)

/- Remark 3.3 (2). The retained odd transitions have asymptotically equal
successive negative logarithms, forcing the alternating-scale gradient sequence
to have exact Q-order one. -/
#check (PlanarGradient.IsAlternatingScale.order_eq_one :
  ∀ {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ},
    PlanarGradient.IsAlternatingScale σ g δ a b → QConvergence.order g 0 = 1)
