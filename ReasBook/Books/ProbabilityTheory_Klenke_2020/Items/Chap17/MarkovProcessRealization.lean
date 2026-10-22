/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

section

variable {I : Type u} [Preorder I] [AddMonoid I]
variable {E : Type v} [MeasurableSpace E]

/-- Shared Chapter 17 owner: a realization of a kernel semigroup by a Markov process, recording
the process measurability, initial law, one-time marginals, and the time-homogeneous Markov
property for the generated filtration. -/
class IsMarkovProcessRealization {Ω : Type w} [MeasurableSpace Ω] (κ : I → Kernel E E)
    (P : E → ProbabilityMeasure Ω) (X : I → Ω → E) : Prop where
  /-- The prescribed transition family is itself a Markov semigroup. -/
  semigroup : IsMarkovSemigroup κ
  /-- Every time slice `X t` is measurable on the ambient measurable space. -/
  measurable_process : ∀ t : I, Measurable (X t)
  /-- Under `P x`, the process starts from the deterministic state `x` at time `0`. -/
  initial_eq : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x
  /-- The one-time marginal at time `t` started from `x` is the kernel row `κ t x`. -/
  transition_eq : ∀ x : E, ∀ t : I, (P x : Measure Ω).map (X t) = κ t x
  /-- Under `P x`, conditioning `X (t + s)` on the history up to time `s` yields the transition
  law `κ t` evaluated at the present state `X s`. -/
  markov_property :
    ∀ x ⦃A : Set E⦄, MeasurableSet A → ∀ s t : I,
      (P x)⟦X (t + s) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ((κ t) (X s ω)).real A

end

section

variable {I : Type u} [Preorder I] [AddMonoid I]
variable {E : Type v} [MeasurableSpace E]
variable [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
variable [SecondCountableTopology E]
variable [OpensMeasurableSpace E]
variable {Ω : Type w} [MeasurableSpace Ω]
variable {κ : I → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : I → Ω → E}

/-- Helper for Chapter 17: every time slice of a Markov-process realization is strongly
measurable because coordinate measurability is part of the realization data. -/
theorem IsMarkovProcessRealization.stronglyMeasurable
    (hX : IsMarkovProcessRealization κ P X) (t : I) :
    StronglyMeasurable (X t) :=
  (hX.measurable_process t).stronglyMeasurable

end

end ProbabilityTheory
