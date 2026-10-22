/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import ReasLib.Optimization.LineSearchConvergence

public section

open scoped Topology

/- Proposition 2.2 (Universal lower bound): every convergent, eventually nonstationary
sequence whose steps arise from exact nonnegative line searches near a critical point
with positive-definite Hessian has Q-order at least one. -/
#check (QConvergence.hasOrderAtLeast_one_of_exactLineSearch :
  ∀ {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (h_smooth : ContDiffAt ℝ 2 F xStar) (h_gradient : gradient F xStar = 0)
    (h_hessian : Matrix.PosDef
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (gradient F) xStar)))
    (h_tendsto : Filter.Tendsto x Filter.atTop (𝓝 xStar))
    (h_ne : ∀ᶠ k in Filter.atTop, x k ≠ xStar)
    (h_step : ∀ k, ∃ (d : EuclideanSpace ℝ (Fin n)) (α : ℝ),
      LineSearch.IsExact F (x k) d α ∧ x (k + 1) = x k + α • d),
    QConvergence.HasOrderAtLeast x xStar 1)
