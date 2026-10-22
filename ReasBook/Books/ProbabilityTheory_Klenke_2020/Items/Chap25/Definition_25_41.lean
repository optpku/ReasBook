/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/-- Definition 25.41: a set `A ⊆ E` is polar for the family of laws `P x` and the `E`-valued
process `W` if, for every starting point `x`, the strictly positive hitting time of `A` is almost
surely infinite under `P x`. In the chapter's Brownian-motion applications, `E = ℝ^d`. -/
def IsPolarSet (P : E → ProbabilityMeasure Ω) (W : NNReal → Ω → E) (A : Set E) : Prop :=
  ∀ x : E, ∀ᵐ ω ∂(P x : Measure Ω), (τ_[W, A]) ω = ⊤

-- Proof sketch: `IsPolarSet` is defined through the canonical owner `strictHittingTime`; the
-- source-facing path-avoidance formulation is exactly `strictHittingTime_eq_top_iff` under each
-- starting law `P x`.
/-- A set is polar exactly when, under each starting law `P x`, the path avoids the set at every
strictly positive time almost surely. -/
theorem isPolarSet_iff
    (P : E → ProbabilityMeasure Ω) (W : NNReal → Ω → E) (A : Set E) :
    IsPolarSet P W A ↔
      ∀ x : E, ∀ᵐ ω ∂(P x : Measure Ω), ∀ t : NNReal, 0 < t → W t ω ∉ A := by
  constructor
  · intro h x
    filter_upwards [h x] with ω hω
    exact (strictHittingTime_eq_top_iff W A ω).1 hω
  · intro h x
    filter_upwards [h x] with ω hω
    exact (strictHittingTime_eq_top_iff W A ω).2 hω

/-- The empty set is polar for every family of starting laws and every state-valued process. -/
@[simp] theorem isPolarSet_empty
    (P : E → ProbabilityMeasure Ω) (W : NNReal → Ω → E) :
    IsPolarSet P W ∅ := by
  rw [isPolarSet_iff]
  intro x
  filter_upwards with ω t ht
  simp

/-- If the path-avoidance event is measurable for each starting point, then `IsPolarSet P W A`
is equivalent to the textbook probability-one formulation. -/
theorem isPolarSet_iff_prob_eq_one
    (P : E → ProbabilityMeasure Ω) (W : NNReal → Ω → E) (A : Set E)
    (hmeas : MeasurableSet {ω | (τ_[W, A]) ω = ⊤}) :
    IsPolarSet P W A ↔
      ∀ x : E, (P x : Measure Ω) {ω | (τ_[W, A]) ω = ⊤} = 1 := by
  constructor
  · intro h x
    exact (mem_ae_iff_prob_eq_one hmeas).1 (h x)
  · intro h x
    exact (mem_ae_iff_prob_eq_one hmeas).2 (h x)

end ProbabilityTheory
