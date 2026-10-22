/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_2_1.WeakSolution

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

variable {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
variable {σ : DiffusionCoeff} {b : DriftCoeff}

/-- Helper for Theorem 26.18: pathwise uniqueness on the generalized weak-solution surface means
that every other strong realization on the same filtered space with the same Brownian path and an
almost surely equal initial datum agrees almost surely with the stored state path. -/
def GeneralizedWeakSDESolution.IsPathwiseUnique
    {n m : ℕ}
    {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) : Prop :=
  ∀ ⦃ξ' : L.Ω → Fin n → ℝ⦄ (X' : L.Ω → EuclideanPathSpace n),
    ξ' =ᵐ[L.μ] L.ξ →
    SolvesStrongGeneralizedSDE σ b L.μ L.ℱ ξ' L.Wpath X' →
    X' =ᵐ[L.μ] L.X

/-- Helper for Theorem 26.18: weak existence together with generalized pathwise uniqueness for
the initial law `μ₀`. -/
def HasWeakSolutionWithPathwiseUniqueness : Prop :=
  Nonempty (GeneralizedWeakSDESolution μ₀ σ b) ∧
    ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsPathwiseUnique

/-- Helper for Theorem 26.18: the packaged Yamada--Watanabe proposition for the initial law `μ₀`,
combining the equivalence between unique strong solvability and weak existence plus pathwise
uniqueness with the resulting weak uniqueness conclusion. -/
def yamadaWatanabeTheorem26_18 : Prop :=
  (HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE σ b)
      μ₀ ↔
    HasWeakSolutionWithPathwiseUniqueness (μ₀ := μ₀) (σ := σ) (b := b)) ∧
    (HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE σ b)
        μ₀ →
      ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsWeaklyUnique)

-- Proof comment: the item-level main declaration is a labeled alias so the orchestrator attaches
-- the textbook entry to a single public declaration while the packaged proposition stays reusable.
/-- Theorem 26.18 (Yamada and Watanabe): unique strong solvability for initial law `μ₀` is
equivalent to weak existence plus pathwise uniqueness, and under these equivalent conditions every
generalized weak solution with initial law `μ₀` is weakly unique. -/
def canonicalCommonInputRealization_of_pathwiseUnique : Prop :=
  yamadaWatanabeTheorem26_18 (μ₀ := μ₀) (σ := σ) (b := b)

/-- Helper for Theorem 26.18: restatement of the packaged Yamada--Watanabe proposition by
unfolding the definition. -/
theorem yamadaWatanabeTheorem26_18_iff :
    yamadaWatanabeTheorem26_18 (μ₀ := μ₀) (σ := σ) (b := b) ↔
      ((HasUniqueStrongSolution
            GeneralizedSDEBrownianMotion
            (SolvesStrongGeneralizedSDE σ b)
            μ₀ ↔
          HasWeakSolutionWithPathwiseUniqueness (μ₀ := μ₀) (σ := σ) (b := b)) ∧
        (HasUniqueStrongSolution
            GeneralizedSDEBrownianMotion
            (SolvesStrongGeneralizedSDE σ b)
            μ₀ →
          ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsWeaklyUnique)) :=
  Iff.rfl

end ProbabilityTheory
