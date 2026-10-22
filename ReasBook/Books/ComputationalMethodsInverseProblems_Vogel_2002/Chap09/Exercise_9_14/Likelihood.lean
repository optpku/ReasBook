/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_13.AdmissibleSet
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

noncomputable section

open scoped BigOperators

namespace PoissonInverse

/-- The Chapter 9 Poisson log-likelihood `(9.41)` for data `d` and forward
operator `K`. -/
def logLikelihood
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    ∑ i : Fin m, d i * Real.log (Matrix.mulVec K f i)

/-- The defining finite-sum formula for `PoissonInverse.logLikelihood`. -/
theorem logLikelihood_def
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n)) :
    logLikelihood K d f =
      ∑ i : Fin m, d i * Real.log (Matrix.mulVec K f i) := by
  -- Expand `logLikelihood` to its defining finite sum.
  rfl

/-- The Chapter 9 admissible set for maximizing `(9.41)`: nonnegative points
with positive forward data satisfying the mass constraint `(9.43)`. -/
def logLikelihoodConstraintSet
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {f : EuclideanSpace ℝ (Fin n) |
    f ∈ admissibleSet K ∧
      ∑ i : Fin m, Matrix.mulVec K f i = ∑ i : Fin m, d i}

/-- Membership in `PoissonInverse.logLikelihoodConstraintSet` is exactly
membership in `PoissonInverse.admissibleSet K` together with the mass identity
`(9.43)`. -/
@[simp] theorem mem_logLikelihoodConstraintSet_iff
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n)) :
    f ∈ logLikelihoodConstraintSet K d ↔
      f ∈ admissibleSet K ∧
        ∑ i : Fin m, Matrix.mulVec K f i = ∑ i : Fin m, d i :=
  Iff.rfl

/-- Any point in `PoissonInverse.logLikelihoodConstraintSet` is admissible for
the Chapter 9 Poisson inverse problem. -/
theorem admissible_of_mem_logLikelihoodConstraintSet
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m)}
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ logLikelihoodConstraintSet K d) :
    f ∈ admissibleSet K :=
  (mem_logLikelihoodConstraintSet_iff K d f).mp hf |>.1

/-- Any point in `PoissonInverse.logLikelihoodConstraintSet` satisfies the mass
identity `(9.43)`. -/
theorem sum_mulVec_eq_sum_data_of_mem_logLikelihoodConstraintSet
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m)}
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ logLikelihoodConstraintSet K d) :
    ∑ i : Fin m, Matrix.mulVec K f i = ∑ i : Fin m, d i :=
  (mem_logLikelihoodConstraintSet_iff K d f).mp hf |>.2

end PoissonInverse
