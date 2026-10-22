/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]

/-- The Laplace-transform formula appearing in Theorem 24.14. -/
def poissonPointProcessLaplaceFormula
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) : Prop :=
  ∀ f : NonnegativeMeasurableFunction E,
    ∫ ω, Real.exp (-((∫⁻ x, f x ∂X ω).toReal)) ∂(P : Measure Ω) =
      Real.exp
        (-((∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(f x).toReal)) ∂μ).toReal))

/-- The characteristic-function formula on the honest integrability domain appearing in
Theorem 24.14. -/
def poissonPointProcessCharacteristicFormulaOnHonestDomain
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) : Prop :=
  ∀ f : RealValuedBoundedMeasurableFunction E,
    (∀ᵐ ω ∂(P : Measure Ω), Integrable f (X ω)) →
    Integrable (fun x ↦ Complex.exp ((f x : ℂ) * Complex.I) - 1) μ →
      ∫ ω, Complex.exp ((((∫ x, f x ∂X ω : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) =
        Complex.exp (∫ x, (Complex.exp ((f x : ℂ) * Complex.I) - 1) ∂μ)

/-- Theorem 24.14: source-facing Laplace-transform statement for a Poisson point process. The
actual proof body was removed from this file upstream; this definition restores the labeled main
entry and records the intended theorem statement. -/
def poisson_point_process_laplaceTransform
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) : Prop :=
  IsPoissonPointProcess μ P X →
    poissonPointProcessLaplaceFormula P μ X

/-- Helper for Theorem 24.14: source-facing characteristic-function statement on the honest
integrability domain for bounded real test functions. -/
def poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) : Prop :=
  IsPoissonPointProcess μ P X →
    poissonPointProcessCharacteristicFormulaOnHonestDomain P μ X

/-- Helper for Theorem 24.14: package the Laplace and honest-domain characteristic transform
statements together. -/
def poissonPointProcessLaplaceAndCharacteristicStatement
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) : Prop :=
  poisson_point_process_laplaceTransform P μ X ∧
    poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction P μ X

-- Proof comment: this is the direct unfolding of the restored Laplace-transform statement.
/-- Unfolding `poisson_point_process_laplaceTransform` gives the source-facing implication from the
Poisson point-process hypothesis to the Laplace-transform formula. -/
theorem poisson_point_process_laplaceTransform_iff
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) :
    poisson_point_process_laplaceTransform P μ X ↔
      IsPoissonPointProcess μ P X →
        poissonPointProcessLaplaceFormula P μ X := by
  rfl

-- Proof comment: this is the direct unfolding of the restored characteristic statement.
/-- Unfolding
`poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction` gives the
source-facing implication from the Poisson point-process hypothesis to the honest-domain
characteristic-function formula. -/
theorem poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction_iff
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) :
    poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction P μ X ↔
      IsPoissonPointProcess μ P X →
        poissonPointProcessCharacteristicFormulaOnHonestDomain P μ X := by
  rfl

-- Proof comment: this is the direct unfolding of the source-facing statement package above.
/-- Unfolding `poissonPointProcessLaplaceAndCharacteristicStatement` gives the conjunction of the
Laplace and honest-domain characteristic formulas promised by Theorem 24.14. -/
theorem poissonPointProcessLaplaceAndCharacteristicStatement_iff
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) :
    poissonPointProcessLaplaceAndCharacteristicStatement P μ X ↔
      poisson_point_process_laplaceTransform P μ X ∧
        poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction
          P μ X := by
  rfl

end ProbabilityTheory
