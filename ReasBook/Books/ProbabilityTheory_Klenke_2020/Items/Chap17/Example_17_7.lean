/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

/-- Example 17.7: for a rate `θ`, the laws `ν_t^θ = Poi_(θ t)` on `ℕ` form the Poisson
convolution semigroup; a Markov process on `ℕ` with these increment laws is called a Poisson
process with jump rate `θ`. -/
def poissonConvolutionSemigroup (θ : NNReal) : NNReal → ProbabilityMeasure ℕ :=
  fun t ↦ ⟨poissonMeasure (θ * t), inferInstance⟩

-- The primitive data is just the family `t ↦ Poi_(θ t)`; coercing it to a measure is definitional.
/-- The Poisson convolution semigroup at time `t` is the Poisson law with parameter `θ * t`. -/
@[simp] theorem poissonConvolutionSemigroup_toMeasure (θ t : NNReal) :
    (poissonConvolutionSemigroup θ t : Measure ℕ) = poissonMeasure (θ * t) :=
  rfl

instance instIsConvolutionSemigroup_poissonConvolutionSemigroup (θ : NNReal) :
    IsConvolutionSemigroup (poissonConvolutionSemigroup θ) where
  convolution_eq s t := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_mul, poissonConvolutionSemigroup_toMeasure,
      poissonConvolutionSemigroup_toMeasure, poissonConvolutionSemigroup_toMeasure,
      poissonMeasure_conv_poissonMeasure]
    simp [mul_add]

/-- The family `t ↦ Poi_(θ t)` is a convolution semigroup on `ℕ`. -/
theorem poissonConvolutionSemigroup_isConvolutionSemigroup (θ : NNReal) :
    IsConvolutionSemigroup (poissonConvolutionSemigroup θ) :=
  inferInstance

variable {Ω : Type u} [MeasurableSpace Ω]

-- The bridge is source-facing: the owner abstraction remains `IsPoissonProcess`, while the
-- semigroup-valued increment hypothesis is just rewritten to the canonical Poisson increment law.
/-- A nondecreasing `ℕ`-valued process whose increment laws are given by the Poisson convolution
semigroup with rate `θ` is a Poisson process with jump rate `θ`. -/
theorem isPoissonProcess_of_poissonConvolutionSemigroup
    {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : NNReal} {X : NNReal → Ω → ℕ}
    (hstochastic : IsStochasticProcess X) (hzero : X 0 = 0) (hmono : Monotone X)
    (hindep : HasIndepIncrements X μ)
    (hsemigroup : ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω ↦ X t ω - X s ω) (poissonConvolutionSemigroup θ (t - s)) μ) :
    IsPoissonProcess θ μ X := by
  refine isPoissonProcess_of_textbook hstochastic hzero hmono hindep ?_
  intro s t hst
  simpa using hsemigroup (le_of_lt hst)
