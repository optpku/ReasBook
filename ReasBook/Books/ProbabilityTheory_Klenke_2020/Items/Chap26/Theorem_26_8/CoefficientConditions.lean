/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_4

noncomputable section

namespace ProbabilityTheory

variable {n m : ℕ}

/-- The `n`-dimensional Euclidean state space used in Theorem 26.8. -/
abbrev SDEState (n : ℕ) :=
  Fin n → ℝ

/-- The diffusion coefficient type for the `n`-dimensional state and `m`-dimensional driver. -/
abbrev SDEDiffusionCoeff (n m : ℕ) :=
  NNReal → SDEState n → Fin n → Fin m → ℝ

/-- The drift coefficient type for the `n`-dimensional state space. -/
abbrev SDEDriftCoeff (n : ℕ) :=
  NNReal → SDEState n → Fin n → ℝ

/-- The coefficients `b` and `σ` are globally Lipschitz in the spatial variable with constant
`K`, uniformly in time. -/
def SDESpaceLipschitzWith (K : ℝ) (b : SDEDriftCoeff n) (σ : SDEDiffusionCoeff n m) : Prop :=
  ∀ x x' : SDEState n, ∀ t : NNReal,
    ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖

/-- The coefficients `b` and `σ` satisfy the linear-growth estimate with constant `K`,
uniformly in time. -/
def SDELinearGrowthWith (K : ℝ) (b : SDEDriftCoeff n) (σ : SDEDiffusionCoeff n m) : Prop :=
  ∀ x : SDEState n, ∀ t : NNReal,
    ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2)

/-- The coefficient time sections are measurable for each spatial input, so the Chapter 26
generalized-diffusion clauses can state the required time-regularity explicitly. -/
def SDETimeMeasurable (b : SDEDriftCoeff n) (σ : SDEDiffusionCoeff n m) : Prop :=
  (∀ x : SDEState n, Measurable fun t : NNReal ↦ b t x) ∧
    ∀ x : SDEState n, Measurable fun t : NNReal ↦ σ t x

end ProbabilityTheory
