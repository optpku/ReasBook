/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

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
