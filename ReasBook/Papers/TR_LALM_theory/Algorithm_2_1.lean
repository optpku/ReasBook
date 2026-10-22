/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

/- Algorithm 2.1 (1): the fixed-penalty NR-LALM step minimizes the explicit quadratic
model in the primal step. -/

/- Algorithm 2.1 (2): a run stores positive parameters, the initial pair, global
step-model minimizers, and the point and multiplier updates. -/

/- Algorithm 2.1 (3): every other global minimizer of a step model equals the stored
step. -/

/- Algorithm 2.1 (4): the quadratic-model minimizer satisfies the equivalent
first-order linear system. -/

/- Algorithm 2.1 (5): the fixed-penalty augmented Lagrangian has its objective,
multiplier-pairing, and quadratic-penalty terms. -/

/- Algorithm 2.1 (6): the error is the nonlinear constraint increment minus its
linearization along the step. -/

/-- Algorithm 2.1 (7): model optimality and the classical multiplier update give the
perturbed multiplier identity. -/
theorem LALM.Run.perturbedMultiplierIdentity
    {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : LALM.Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    gradient f (run.point k) + EqualityConstrained.constraintGradient c (run.point k)
      (run.multiplier (k + 1)) + β • run.step k =
      ρ • EqualityConstrained.constraintGradient c (run.point k) (run.error k) := by
  -- Substitute the multiplier update and expose the linearization error once.
  rw [run.multiplier_succ k, run.error_def k]
  simp only [map_add, map_sub, map_smul]
  -- The remaining module identity is exactly the rearranged model optimality equation.
  have hoptimal := run.optimality k
  simp only [map_add, map_smul] at hoptimal
  linear_combination (norm := module) hoptimal

/- Algorithm 2.1 (8): the linearization constant is half the constraint-gradient
Lipschitz constant. -/

/- Algorithm 2.1 (9): a segment contained in the regularity region gives the
quadratic linearization-error bound. -/

/- Algorithm 2.1 (10): a finite prefix is admissible exactly when every completed
iteration segment lies in the regularity region. -/

end
