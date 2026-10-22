/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : Type u} [Preorder I]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- The natural history filtration of a process inside the ambient measurable space. -/
def processFiltration (X : I → Ω → E) : Filtration I mΩ where
  seq s := mΩ ⊓ ⨆ r ≤ s, MeasurableSpace.comap (X r) mE
  mono' s t hst := inf_le_inf le_rfl <| by
    refine iSup₂_le fun r hrs ↦ ?_
    exact le_iSup_of_le r <| le_iSup_of_le (le_trans hrs hst) le_rfl
  le' s := inf_le_left

/-- The full path of the process `X` through a sample point `ω`. -/
def processPath {I : Type u} {Ω : Type v} {E : Type w} (X : I → Ω → E) (ω : Ω) : I → E :=
  fun t ↦ X t ω

-- Proof sketch: this is immediate from the definition of `processPath` as coordinate evaluation
-- along the sample point `ω`.
/-- Evaluating `processPath X ω` at time `t` recovers `X t ω`. -/
theorem processPath_apply {I : Type u} {Ω : Type v} {E : Type w}
    (X : I → Ω → E) (ω : Ω) (t : I) :
    processPath X ω t = X t ω :=
  rfl

section

variable [AddMonoid I]

/-- The post-`τ` future path `t ↦ X_{τ+t}` of the process `X`, viewed through the canonical
`WithTop I`-valued stopping-time API. On the event `{τ = ⊤}` this uses the default value built
into `stoppedValue`; under an almost-sure finiteness hypothesis, that exceptional set is
irrelevant. -/
def futurePathAfterStoppingTime (X : I → Ω → E) (τ : Ω → WithTop I) : Ω → I → E :=
  fun ω t ↦ stoppedValue (fun s ω' ↦ X (s + t) ω') τ ω

-- Proof sketch: unfold `futurePathAfterStoppingTime` and `stoppedValue`; away from `τ ω = ⊤`,
-- `WithTop.untopA` recovers the actual stopping time value.
/-- On the event `{τ ≠ ⊤}`, evaluating the future path after `τ` at time `t` gives the process
value at the shifted time `τ + t`. -/
theorem futurePathAfterStoppingTime_apply_of_ne_top
    (X : I → Ω → E) (τ : Ω → WithTop I) (ω : Ω) (t : I) (hτω : τ ω ≠ ⊤) :
    futurePathAfterStoppingTime X τ ω t = X ((τ ω).untop hτω + t) ω := by
  -- Unfold the stopped future path to the underlying `stoppedValue` evaluation.
  simp only [futurePathAfterStoppingTime, stoppedValue]
  -- Replace the default-valued `untopA` by the genuine finite stopping-time value.
  rw [WithTop.untopA_eq_untop hτω]

/-- Definition 17.12: a Markov process with distributions `P` and path kernel `κ` has the strong
Markov property if, for every almost surely finite stopping time `τ` of its natural history
filtration and every bounded measurable path functional `f`, the conditional expectation of the
shifted future path `t ↦ X_{τ+t}` given `𝓕_τ` agrees almost surely with the expectation of `f`
under the path law started from the stopped state `X_τ`. The stopping time itself is encoded
canonically as a map `τ : Ω → WithTop I`, while almost-sure finiteness is a separate hypothesis. -/
def HasStrongMarkovProperty
    (P : E → ProbabilityMeasure Ω) (X : I → Ω → E) (κ : Kernel E (I → E)) : Prop :=
  ∀ (x : E) (τ : Ω → WithTop I)
    (hτ : IsStoppingTime (processFiltration X) τ),
    (∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤) →
    ∀ (f : (I → E) → ℝ),
    Measurable f →
    (∃ C : ℝ, ∀ y, |f y| ≤ C) →
    (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, f y ∂ κ (stoppedValue X τ ω)

-- Proof sketch: unfold `HasStrongMarkovProperty`; this is exactly the defining conditional-
-- expectation identity for all finite stopping times and bounded measurable path functionals.
/-- Having the strong Markov property is equivalent to the explicit stopped-path conditional
expectation identity. -/
theorem hasStrongMarkovProperty_iff
    (P : E → ProbabilityMeasure Ω) (X : I → Ω → E) (κ : Kernel E (I → E)) :
    HasStrongMarkovProperty P X κ ↔
      ∀ (x : E) (τ : Ω → WithTop I)
        (hτ : IsStoppingTime (processFiltration X) τ),
        (∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤) →
        ∀ (f : (I → E) → ℝ),
        Measurable f →
        (∃ C : ℝ, ∀ y, |f y| ≤ C) →
        (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[
          (P x : Measure Ω)] fun ω ↦ ∫ y, f y ∂ κ (stoppedValue X τ ω) := by
  -- This theorem is the public expansion of the defining predicate.
  rfl

end

end ProbabilityTheory
