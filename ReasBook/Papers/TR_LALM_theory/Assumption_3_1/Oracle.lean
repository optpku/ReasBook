/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

public section

open MeasureTheory
open scoped Gradient NNReal

namespace EqualityConstrained

universe u

/-- A sampled objective together with its stochastic first-order bounds on a region. -/
structure StochasticOracle
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (region : Set (EuclideanSpace ℝ (Fin n))) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The sampled objective, evaluated at a point and a sample. -/
  sample : EuclideanSpace ℝ (Fin n) → Ω → ℝ
  /-- The uniform root-mean-square gradient error bound. -/
  noiseLevel : ℝ≥0
  /-- The mean-square Lipschitz constant for the sampled gradients. -/
  meanSquareLipschitz : ℝ≥0
  /-- Almost every sampled objective is differentiable on the chosen region. -/
  ae_differentiableOn_sample :
    ∀ᵐ ω ∂μ, DifferentiableOn ℝ (fun x ↦ sample x ω) region
  /-- Sampled gradients are jointly measurable in the point and sample. -/
  measurable_gradient :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ω ↦
      ∇ (fun y ↦ sample y z.2) z.1)
  /-- Every sampled objective value on the chosen region is integrable. -/
  integrable_sample (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ sample x ω) μ
  /-- On the chosen region, the mean sampled objective equals the deterministic
  objective. -/
  integral_sample_eq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    (∫ ω, sample x ω ∂μ) = f x
  /-- Sampled gradients are integrable at every point of the region. -/
  integrable_gradient (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ ∇ (fun y ↦ sample y ω) x) μ
  /-- The sampled gradient is unbiased on the region. -/
  integral_gradient_eq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    (∫ ω, ∇ (fun y ↦ sample y ω) x ∂μ) = ∇ f x
  /-- The squared sampled-gradient error is integrable on the region. -/
  integrable_gradientErrorSq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ ‖∇ (fun y ↦ sample y ω) x - ∇ f x‖ ^ 2) μ
  /-- The sampled-gradient second moment has the stated uniform bound. -/
  integral_gradientErrorSq_le (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    (∫ ω, ‖∇ (fun y ↦ sample y ω) x - ∇ f x‖ ^ 2 ∂μ) ≤
      noiseLevel ^ 2
  /-- Squared differences of sampled gradients are integrable on the region. -/
  integrable_gradientDiffSq
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region)
      (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ region) :
    Integrable (fun ω ↦
      ‖∇ (fun z ↦ sample z ω) x - ∇ (fun z ↦ sample z ω) y‖ ^ 2) μ
  /-- Sampled gradients satisfy the stated mean-square Lipschitz bound. -/
  integral_gradientDiffSq_le
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region)
      (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ region) :
    (∫ ω,
      ‖∇ (fun z ↦ sample z ω) x - ∇ (fun z ↦ sample z ω) y‖ ^ 2 ∂μ) ≤
      meanSquareLipschitz ^ 2 * ‖x - y‖ ^ 2

namespace StochasticOracle

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {region : Set (EuclideanSpace ℝ (Fin n))}
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Construct a stochastic oracle from a sampled objective and explicit witnesses for
its expectation, gradient, noise, and mean-square Lipschitz laws. -/
def ofBounds
    (sample : EuclideanSpace ℝ (Fin n) → Ω → ℝ)
    (noiseLevel meanSquareLipschitz : ℝ≥0)
    (ae_differentiableOn_sample :
      ∀ᵐ ω ∂μ, DifferentiableOn ℝ (fun x ↦ sample x ω) region)
    (measurable_gradient :
      Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ω ↦
        ∇ (fun y ↦ sample y z.2) z.1))
    (integrable_sample : ∀ x ∈ region, Integrable (fun ω ↦ sample x ω) μ)
    (integral_sample_eq : ∀ x ∈ region, (∫ ω, sample x ω ∂μ) = f x)
    (integrable_gradient : ∀ x ∈ region,
      Integrable (fun ω ↦ ∇ (fun y ↦ sample y ω) x) μ)
    (integral_gradient_eq : ∀ x ∈ region,
      (∫ ω, ∇ (fun y ↦ sample y ω) x ∂μ) = ∇ f x)
    (integrable_gradientErrorSq : ∀ x ∈ region,
      Integrable (fun ω ↦ ‖∇ (fun y ↦ sample y ω) x - ∇ f x‖ ^ 2) μ)
    (integral_gradientErrorSq_le : ∀ x ∈ region,
      (∫ ω, ‖∇ (fun y ↦ sample y ω) x - ∇ f x‖ ^ 2 ∂μ) ≤
        noiseLevel ^ 2)
    (integrable_gradientDiffSq : ∀ x ∈ region, ∀ y ∈ region,
      Integrable (fun ω ↦
        ‖∇ (fun z ↦ sample z ω) x - ∇ (fun z ↦ sample z ω) y‖ ^ 2) μ)
    (integral_gradientDiffSq_le : ∀ x ∈ region, ∀ y ∈ region,
      (∫ ω,
        ‖∇ (fun z ↦ sample z ω) x - ∇ (fun z ↦ sample z ω) y‖ ^ 2 ∂μ) ≤
        meanSquareLipschitz ^ 2 * ‖x - y‖ ^ 2) :
    StochasticOracle f region μ :=
  { sample
    noiseLevel
    meanSquareLipschitz
    ae_differentiableOn_sample
    measurable_gradient
    integrable_sample
    integral_sample_eq
    integrable_gradient
    integral_gradient_eq
    integrable_gradientErrorSq
    integral_gradientErrorSq_le
    integrable_gradientDiffSq
    integral_gradientDiffSq_le }

/-- The gradient of the sampled objective at a point and sample. -/
@[expose] noncomputable def sampleGradient (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  ∇ (fun y ↦ oracle.sample y ω) x

/-- The sampled-gradient definition agrees with the gradient of the sampled objective. -/
theorem sampleGradient_apply (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    oracle.sampleGradient x ω = ∇ (fun y ↦ oracle.sample y ω) x := rfl

/-- The sampled-gradient map is jointly measurable in its point and sample. -/
theorem measurable_sampleGradient (oracle : StochasticOracle f region μ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ω ↦
      oracle.sampleGradient z.1 z.2) := by
  simpa only [sampleGradient] using oracle.measurable_gradient

/-- On the chosen region, sample values are integrable and have mean equal to the
deterministic objective. -/
theorem sampleMean_spec (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ oracle.sample x ω) μ ∧
      (∫ ω, oracle.sample x ω ∂μ) = f x :=
  ⟨oracle.integrable_sample x hx, oracle.integral_sample_eq x hx⟩

/-- On the region, sampled gradients are integrable and unbiased. -/
theorem unbiased_spec (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ oracle.sampleGradient x ω) μ ∧
      (∫ ω, oracle.sampleGradient x ω ∂μ) = ∇ f x := by
  simpa only [sampleGradient] using
    And.intro (oracle.integrable_gradient x hx) (oracle.integral_gradient_eq x hx)

/-- On the region, the integrable squared gradient error obeys the noise bound. -/
theorem variance_spec (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region) :
    Integrable (fun ω ↦ ‖oracle.sampleGradient x ω - ∇ f x‖ ^ 2) μ ∧
      (∫ ω, ‖oracle.sampleGradient x ω - ∇ f x‖ ^ 2 ∂μ) ≤
        oracle.noiseLevel ^ 2 := by
  simpa only [sampleGradient] using
    And.intro (oracle.integrable_gradientErrorSq x hx)
      (oracle.integral_gradientErrorSq_le x hx)

/-- On the region, sampled gradients obey the integrable mean-square Lipschitz bound. -/
theorem meanSquareLipschitz_spec (oracle : StochasticOracle f region μ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ region)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ region) :
    Integrable (fun ω ↦ ‖oracle.sampleGradient x ω - oracle.sampleGradient y ω‖ ^ 2) μ ∧
      (∫ ω, ‖oracle.sampleGradient x ω - oracle.sampleGradient y ω‖ ^ 2 ∂μ) ≤
        oracle.meanSquareLipschitz ^ 2 * ‖x - y‖ ^ 2 := by
  simpa only [sampleGradient] using
    And.intro (oracle.integrable_gradientDiffSq x hx y hy)
      (oracle.integral_gradientDiffSq_le x hx y hy)

/-- A stochastic oracle exposes the joint measurability, differentiability,
expectation, unbiasedness, noise, and mean-square Lipschitz conditions of
Assumption 3.1. -/
theorem spec (oracle : StochasticOracle f region μ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ω ↦
        oracle.sampleGradient z.1 z.2) ∧
      (∀ᵐ ω ∂μ, DifferentiableOn ℝ (fun x ↦ oracle.sample x ω) region) ∧
      (∀ x ∈ region, Integrable (fun ω ↦ oracle.sample x ω) μ ∧
        (∫ ω, oracle.sample x ω ∂μ) = f x) ∧
      (∀ x ∈ region, Integrable (fun ω ↦ oracle.sampleGradient x ω) μ ∧
        (∫ ω, oracle.sampleGradient x ω ∂μ) = ∇ f x) ∧
      (∀ x ∈ region,
        Integrable (fun ω ↦ ‖oracle.sampleGradient x ω - ∇ f x‖ ^ 2) μ ∧
          (∫ ω, ‖oracle.sampleGradient x ω - ∇ f x‖ ^ 2 ∂μ) ≤
            oracle.noiseLevel ^ 2) ∧
      ∀ x ∈ region, ∀ y ∈ region,
        Integrable
          (fun ω ↦ ‖oracle.sampleGradient x ω - oracle.sampleGradient y ω‖ ^ 2) μ ∧
          (∫ ω, ‖oracle.sampleGradient x ω - oracle.sampleGradient y ω‖ ^ 2 ∂μ) ≤
            oracle.meanSquareLipschitz ^ 2 * ‖x - y‖ ^ 2 :=
  ⟨oracle.measurable_sampleGradient, oracle.ae_differentiableOn_sample,
    oracle.sampleMean_spec, oracle.unbiased_spec, oracle.variance_spec,
    oracle.meanSquareLipschitz_spec⟩

end StochasticOracle

end EqualityConstrained

end
