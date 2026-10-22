/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_3.Clauses
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_1_1.Iterates
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_1.Iterates

public section

universe u

/- Algorithm 3.2.3. Nonlinear CG Method.

The source pseudocode specifies a real Hilbert-space functional `J`, gradients
`gᵥ = grad J (fᵥ)`, search directions `pᵥ`, and line-search parameters `τᵥ`
chosen by minimizing the profile `τ ↦ J (fᵥ + τ • pᵥ)` on the positive ray.
However, the solution-update clause is internally inconsistent: after choosing
`τᵥ` from the profile built from `pᵥ`, it states `fᵥ₊₁ := fᵥ + τᵥ pᵥ₊₁` before
`pᵥ₊₁` has been defined. A faithful `NonlinearConjugateGradient.State`, `step`,
or `iterates` owner would therefore have to guess missing mathematics.

This file consequently remains a labeled blocker entry. The `#check` commands
below record the eight displayed source clauses through the reusable owners in
`Book.Ch3.Algorithm_3_2_3.Clauses`. They also record nearby backend iteration
owners that a later faithful nonlinear conjugate-gradient formalization should
reuse once the source update clause is repaired.
-/

/-
Algorithm 3.2.3. Main labeled source-facing blocker entry.

The source still determines eight displayed clauses even though it does not
determine a coherent nonlinear-CG state/update owner. The fifth clause, namely
the displayed solution update, is preserved exactly as written even though it
is the source inconsistency blocking a faithful owner declaration. The exact
clause owners live in `NonlinearConjugateGradient`.
-/

/- Algorithm 3.2.3 (1). The displayed gradient refresh `gᵥ = gradient J (fᵥ)`.
-/
#check NonlinearConjugateGradient.HasGradientFormula

/- Algorithm 3.2.3 (2). The displayed initialization `p₀ = -g₀`. -/
#check NonlinearConjugateGradient.HasInitialDirection

/- Algorithm 3.2.3 (3). The displayed initialization `δ₀ = ‖g₀‖²`. -/
#check NonlinearConjugateGradient.HasInitialDelta

/- Algorithm 3.2.3 (4). The exact line-search clause
`τᵥ := arg min_(τ > 0) J (fᵥ + τ • pᵥ)`. -/
#check NonlinearConjugateGradient.HasExactLineSearch

/- Algorithm 3.2.3 (5). The displayed solution update
`fᵥ₊₁ = fᵥ + τᵥ • pᵥ₊₁`, kept exactly as written even though it is the source
inconsistency blocking a faithful nonlinear-CG state/update owner. -/
#check NonlinearConjugateGradient.HasDisplayedSolutionUpdate

/- Algorithm 3.2.3 (6). The displayed recurrence `δᵥ₊₁ = ‖gᵥ₊₁‖²`. -/
#check NonlinearConjugateGradient.HasDeltaUpdate

/- Algorithm 3.2.3 (7). The Fletcher-Reeves scalar update
`βᵥ = δᵥ₊₁ / δᵥ`. -/
#check NonlinearConjugateGradient.HasBetaFormula

/- Algorithm 3.2.3 (8). The displayed search-direction recurrence
`pᵥ₊₁ = -gᵥ₊₁ + βᵥ • pᵥ`. -/
#check NonlinearConjugateGradient.HasDirectionUpdate

/- Reusable backend owners for the exact-line-search and linear conjugate-
gradient special cases that a repaired nonlinear-CG formalization should reuse.
-/

#check gradient
#check HasGradientAt
#check DifferentiableAt.hasGradientAt
#check SteepestDescent.iterates
#check SteepestDescent.IsExactLineSearch
#check ConjugateGradient.State
#check ConjugateGradient.delta
#check ConjugateGradient.beta
#check ConjugateGradient.nextDirection
#check ConjugateGradient.iterates
