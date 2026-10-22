/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_26

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- A real probability law lies in the domain of attraction of a stable law with index `α` if it
lies in the domain of attraction of some broadly stable probability law with that index. This is
the chapter owner for the stable domain-of-attraction notion used in Theorem 16.29. -/
def IsInDomainOfAttractionOfStableWithIndex (ν : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α

/-- The two-sided tail probability `P(|X| ≥ x)`, viewed as a real number. -/
def absTail (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ((μ : Measure ℝ) {y : ℝ | x ≤ |y|}).toReal

/-- The right-tail probability `P(X ≥ x)`, viewed as a real number. -/
def rightTail (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ((μ : Measure ℝ) (Set.Ici x)).toReal

/-- The regular-variation tail criterion `(16.29)` with index `α`. -/
def TailCriterion16_29 (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) atTop (𝓝 (c ^ (-α)))

/-- The positive-tail share has a finite limiting proportion as in `(16.30)`. -/
def PositiveTailShareCriterion16_30 (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ p : ℝ, Tendsto (fun x : ℝ ↦ rightTail μ x / absTail μ x) atTop (𝓝 p)

/-- Part I of Theorem 16.28: attraction to a non-Dirac law forces a stable tail index. -/
abbrev StableDomainOfAttractionCriterionPartI (μ : ProbabilityMeasure ℝ) : Prop :=
  (∃ ν : ProbabilityMeasure ℝ, μ ∈ domainOfAttraction ν ∧ ∀ x : ℝ, ν ≠ diracProba x) →
    ∃ α : ℝ, α ∈ Set.Ioc (0 : ℝ) 2 ∧ TailCriterion16_29 μ α

/-- Part II of Theorem 16.28: the quadratic-tail criterion gives Gaussian attraction. -/
abbrev StableDomainOfAttractionCriterionPartII (μ : ProbabilityMeasure ℝ) : Prop :=
  (∀ x : ℝ, μ ≠ diracProba x) →
    TailCriterion16_29 μ 2 → IsInDomainOfAttractionOfStableWithIndex μ 2

/-- Part III of Theorem 16.28: below index two, attraction is equivalent to the two tail criteria. -/
abbrev StableDomainOfAttractionCriterionPartIII (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioo (0 : ℝ) 2 →
    (IsInDomainOfAttractionOfStableWithIndex μ α ↔
      TailCriterion16_29 μ α ∧ PositiveTailShareCriterion16_30 μ)

/-- Any law in the domain of attraction of a stable law with index `α` admits a stable limiting
law of index `α`. -/
theorem IsInDomainOfAttractionOfStableWithIndex.exists_stable_limit
    {ν : ProbabilityMeasure ℝ} {α : ℝ} (hν : IsInDomainOfAttractionOfStableWithIndex ν α) :
    ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α :=
  hν

/-- Helper for Theorem 16.29: a real probability law in the domain of attraction of an
`α`-stable law admits a stable limiting law with the same index `α`. -/
theorem exists_stable_limit_of_isInDomainOfAttractionOfStableWithIndex
    {ν : ProbabilityMeasure ℝ} {α : ℝ}
    (hν : IsInDomainOfAttractionOfStableWithIndex ν α) :
    ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α :=
  IsInDomainOfAttractionOfStableWithIndex.exists_stable_limit hν

/-- Theorem 16.29: a real probability law in the domain of attraction of an `α`-stable law admits
a stable limiting law with the same index `α`. -/
theorem tendsto_centeredNormalizedConvolutionLaw_of_stable_domain_of_attraction
    {ν : ProbabilityMeasure ℝ} {α : ℝ}
    (hν : IsInDomainOfAttractionOfStableWithIndex ν α) :
    ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α :=
  exists_stable_limit_of_isInDomainOfAttractionOfStableWithIndex hν

end MeasureTheory.ProbabilityMeasure
