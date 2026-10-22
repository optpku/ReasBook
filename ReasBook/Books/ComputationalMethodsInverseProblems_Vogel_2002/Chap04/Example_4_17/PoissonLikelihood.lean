/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_15.Likelihood
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_14.PoissonVector
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

noncomputable section

open scoped BigOperators NNReal

namespace PoissonLikelihood

universe u

/-- The positive orthant in the finite-dimensional function space `ι → ℝ`. -/
def positiveOrthant (ι : Type u) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Ioi (0 : ℝ))

/-- Membership in `positiveOrthant ι` means that every coordinate is strictly positive. -/
theorem mem_positiveOrthant_iff {ι : Type u} (lambda : ι → ℝ) :
    lambda ∈ positiveOrthant ι ↔ ∀ i, 0 < lambda i := by
  simp [positiveOrthant]

section

variable {ι : Type u} [Fintype ι]

/-- The additive constant `∑ i, log ((d i)!)` in the Poisson negative log-likelihood. -/
@[expose]
def poissonNegLogLikelihoodConst (d : ι → ℕ) : ℝ :=
  ∑ i, Real.log ((Nat.factorial (d i)) : ℝ)

/-- The defining finite-sum formula for `poissonNegLogLikelihoodConst`. -/
theorem poissonNegLogLikelihoodConst_def (d : ι → ℕ) :
    poissonNegLogLikelihoodConst d = ∑ i, Real.log ((Nat.factorial (d i)) : ℝ) :=
  rfl

/-- The variable part `∑ i, (λ i - d i * log (λ i))` of the Poisson negative log-likelihood. -/
@[expose]
def poissonNegLogLikelihood (d : ι → ℕ) (lambda : ι → ℝ) : ℝ :=
  ∑ i, (lambda i - (d i : ℝ) * Real.log (lambda i))

/-- The defining finite-sum formula for `poissonNegLogLikelihood`. -/
theorem poissonNegLogLikelihood_def (d : ι → ℕ) (lambda : ι → ℝ) :
    poissonNegLogLikelihood d lambda =
      ∑ i, (lambda i - (d i : ℝ) * Real.log (lambda i)) :=
  rfl

/-- The singleton-mass likelihood of the canonical Poisson vector model is the usual finite
product formula. -/
theorem likelihood_poissonVector_eq (d : ι → ℕ) (rate : ι → ℝ≥0) :
    ProbabilityTheory.likelihood
        (fun rate x ↦ (ProbabilityTheory.poissonVector rate).real {x})
        (fun i ↦ (d i : ℝ))
        rate
      =
      ∏ i, Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ d i / ((Nat.factorial (d i)) : ℝ) := by
  -- Unfold the likelihood and evaluate the product measure on the observed singleton.
  rw [ProbabilityTheory.likelihood_apply, ProbabilityTheory.poissonVector_eq_pi,
    MeasureTheory.Measure.real_def, MeasureTheory.Measure.pi_singleton, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl ?_
  intro i hi
  rw [← MeasureTheory.Measure.real_def]
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) (by measurability)]
  have hpreimage : Nat.cast ⁻¹' ({(d i : ℝ)} : Set ℝ) = ({d i} : Set ℕ) := by
    ext n
    simp
  rw [hpreimage]
  exact ProbabilityTheory.poissonMeasure_real_singleton (rate i) (d i)

end

end PoissonLikelihood
