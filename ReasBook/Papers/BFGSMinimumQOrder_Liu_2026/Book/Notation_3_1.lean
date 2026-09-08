module

import ReasLib.Optimization.BFGS.PlanarGradient

noncomputable section

open scoped EuclideanSpace

section

variable (g : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (k : ℕ)

/- Notation 3.1 (1): the standard quarter-turn `J`, radial normalization, oriented tangent,
and tangential perturbation `δ k • q k`. -/
#check EuclideanPlane.quarterTurnMatrix
#check EuclideanPlane.quarterTurnMatrix_toEuclideanLin
#check EuclideanPlane.orientation
#check EuclideanPlane.perp_apply
#check (‖g k‖)
#check (NormedSpace.normalize (g k))
#check (PlanarGradient.tangent EuclideanPlane.orientation (g k))
#check (PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k))

section

variable (h_gk : g k ≠ 0)

/- Notation 3.1 (2): nonzero gradients give an orthonormal radial-tangential pair,
and the perturbation is orthogonal to the gradient with norm `|δ k|`. -/
#check (norm_pos_iff.mpr h_gk)
#check (PlanarGradient.orthonormal_tangent EuclideanPlane.orientation h_gk)
#check (PlanarGradient.span_tangent_eq_top EuclideanPlane.orientation h_gk)
#check (PlanarGradient.inner_perturbation EuclideanPlane.orientation (g k) (δ k))
#check (PlanarGradient.norm_perturbation EuclideanPlane.orientation (δ k) h_gk)

end

/- Notation 3.1 (3): the candidate iterate is the gradient plus its tangential
perturbation. -/
#check (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))
#check (PlanarGradient.candidate_apply EuclideanPlane.orientation (g k) (δ k))
#check (PlanarGradient.candidate_sub EuclideanPlane.orientation (g k) (δ k))

section

variable (hk : 0 < k) (h_prev : g (k - 1) ≠ 0) (h_gk : g k ≠ 0)
variable (h_step : g k ≠ g (k - 1))

/- Notation 3.1 (4): for `0 < k`, the gradient difference, its normalized direction,
the coefficients `P k` and `D k`, and the separation `S k ∈ Set.Icc 0 1`. -/
#check (g k - g (k - 1))
#check (PlanarGradient.stepDirection (g (k - 1)) (g k))
#check (PlanarGradient.norm_stepDirection h_step)
#check (PlanarGradient.parallelCoefficient (g (k - 1)) (g k))
#check (PlanarGradient.tangentCoefficient EuclideanPlane.orientation (g (k - 1)) (g k))
#check (PlanarGradient.angularSeparation EuclideanPlane.orientation (g (k - 1)) (g k))
#check (EuclideanPlane.standardAreaForm_apply
  (NormedSpace.normalize (g (k - 1))) (NormedSpace.normalize (g k)))
#check (PlanarGradient.angularSeparation_mem_Icc EuclideanPlane.orientation h_prev h_gk)

end


section

variable (hk : 0 < k)

/- Notation 3.1 (5): the parameterized scale and next-gradient recurrence; when that
gradient is nonzero, the same tangential-perturbation construction applies at the next step. -/
#check (PlanarGradient.scale EuclideanPlane.orientation (g (k - 1)) (g k) (δ k))
#check (PlanarGradient.next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k))
#check (PlanarGradient.next_apply EuclideanPlane.orientation
  (g (k - 1)) (g k) (δ k))
#check (PlanarGradient.perturbation EuclideanPlane.orientation
  (PlanarGradient.next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k)) (δ (k + 1)))

section

variable (h_next :
  PlanarGradient.next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k) ≠ 0)

#check (PlanarGradient.norm_perturbation EuclideanPlane.orientation (δ (k + 1)) h_next)

end

end

end
