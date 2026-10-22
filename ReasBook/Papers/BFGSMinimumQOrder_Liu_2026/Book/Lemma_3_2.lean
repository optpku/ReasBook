/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Construction

public section

/- Lemma 3.2 (Alternating scale construction). For every `σ ∈ Set.Ioo 0 1`,
there are planar gradients, scalar perturbations, and positive initial scales satisfying
the recurrence, all-order flatness, limiting, summability, initial-value, and
uniform-smallness conditions. -/
#check (PlanarGradient.exists_alternatingScale :
  ∀ (σ : ℝ), σ ∈ Set.Ioo 0 1 →
    ∃ (g : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (a b : ℝ),
      PlanarGradient.IsAlternatingScale σ g δ a b)
