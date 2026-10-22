/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_2_1_Classical_inverse_form_DFP_iteration.lean
-/

module

public import ReasLib.Optimization.DFP.Iteration

open scoped Matrix

universe u

/- Definition 2.1 (Classical inverse-form DFP iteration): the gradient, direction,
scaled step, point, gradient-change, and inverse-Hessian recurrences. -/
#check (DFP.InverseIteration.ofSequences :
  ∀ {n : Type u} [Fintype n], (f : EuclideanSpace ℝ n → ℝ) →
    (α : ℕ → ℝ) → (x : ℕ → EuclideanSpace ℝ n) → (H : ℕ → Matrix n n ℝ) →
    (∀ k, DifferentiableAt ℝ f (x k)) →
    (∀ k, (H k).PosDef) →
    (∀ k,
      WithLp.ofLp (DFP.steps α (DFP.directions H (DFP.gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges (DFP.gradients f x) k) ≠ 0) →
    (∀ k, x (k + 1) = x k +
      DFP.steps α (DFP.directions H (DFP.gradients f x)) k) →
    (∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (DFP.steps α (DFP.directions H (DFP.gradients f x)) k))
      (WithLp.ofLp (DFP.gradientChanges (DFP.gradients f x) k))) →
    DFP.InverseIteration n)

#check (Matrix.inverseDFPUpdate_apply :
  ∀ {n : Type u} [Fintype n] (H : Matrix n n ℝ) (s y : n → ℝ) (i j : n),
    Matrix.inverseDFPUpdate H s y i j =
      H i j - (y ⬝ᵥ (H *ᵥ y))⁻¹ * ((H *ᵥ y) i * (y ᵥ* H) j) +
        (s ⬝ᵥ y)⁻¹ * (s i * s j))
