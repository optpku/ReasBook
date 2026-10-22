/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

noncomputable section

namespace PoissonInverse

open scoped BigOperators

/-- The Chapter 9 negative log-likelihood objective `J(f) = -ℓ(f; d)` from
`(9.44)` for Poisson inverse data `d` and forward operator `K`. -/
def negLogLikelihood
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    ∑ i : Fin m,
      (Matrix.mulVec K f i - d i * Real.log (Matrix.mulVec K f i))

/-- The defining finite-sum formula for `PoissonInverse.negLogLikelihood`. -/
theorem negLogLikelihood_def
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n)) :
    negLogLikelihood K d f =
      ∑ i : Fin m,
        (Matrix.mulVec K f i - d i * Real.log (Matrix.mulVec K f i)) := by
  -- Expand the objective to its defining finite sum.
  rfl

end PoissonInverse
