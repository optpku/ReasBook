module

public import ReasLib.Optimization.BFGS.PlanarRealization

public section

/- Lemma 2.3: a pairwise-distinct sequence in a two-dimensional Euclidean subspace
satisfying the gradient membership, orthogonality, nonzero span, and positive initial-step
relations is exactly an identity-initialized exact-line-search BFGS trajectory, and every
Hessian approximation has block form `B|V ⊕ 1` on `V ⊕ Vᗮ`. -/
#check (BFGS.existsTrajectory_of_planarRelations :
  ∀ {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (m β₀ : ℝ) (h_dim : Module.finrank ℝ V = 2) (h_differentiable : Differentiable ℝ F)
    (h_m : 0 < m) (h_strongConvex : StrongConvexOn Set.univ m F)
    (h_distinct : Function.Injective x) (h_point_mem : ∀ k, x k ∈ V)
    (h_gradient_mem : ∀ k, gradient F (x k) ∈ V)
    (h_orthogonal : ∀ k,
      inner ℝ (gradient F (x (k + 1))) (x (k + 1) - x k) = 0)
    (h_gradient_span : ∀ k, gradient F (x (k + 2)) ∈
      Submodule.span ℝ {gradient F (x (k + 1)) - gradient F (x k)})
    (h_gradient_ne : ∀ k, gradient F (x (k + 2)) ≠ 0)
    (h_beta : 0 < β₀)
    (h_initial : x 1 - x 0 = (-β₀) • gradient F (x 0)),
    ∃ (B : ℕ → Matrix (Fin n) (Fin n) ℝ) (α : ℕ → ℝ),
      BFGS.IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) x B α ∧
        ∀ k, Matrix.IsBlockIdentityOn (B k) V)
