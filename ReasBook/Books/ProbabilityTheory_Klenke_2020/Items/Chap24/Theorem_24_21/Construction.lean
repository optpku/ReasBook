/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_58.OrderedKernel
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_3.StoppingApprox
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The source jump-size space `(0, ∞)`, represented inside `NNReal`. -/
abbrev PositiveNNReal := Set.Ioi (0 : NNReal)

/-- The bounded-set truncated first-moment condition on a measure `ν` on `(0, ∞) × E`. It is the
local integrability hypothesis `∫ 𝟙_A(t) min (1, x) ν(d(x,t)) < ∞` from the textbook. -/
def HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
    ∫⁻ z, Set.indicator A
      (fun _ : E ↦ min (1 : ℝ≥0∞) ((z.1 : NNReal) : ℝ≥0∞)) z.2 ∂ν < ∞

/-- Unfolding `HasFiniteTruncatedFirstMomentOnBoundedSets` recovers the textbook hypothesis
`∫ 𝟙_A(t) min (1, x) ν(d(x,t)) < ∞` on every bounded measurable set `A ⊆ E`. -/
theorem hasFiniteTruncatedFirstMomentOnBoundedSets_iff
    (ν : Measure (PositiveNNReal × E)) :
    HasFiniteTruncatedFirstMomentOnBoundedSets ν ↔
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        ∫⁻ z, Set.indicator A
          (fun _ : E ↦ min (1 : ℝ≥0∞) ((z.1 : NNReal) : ℝ≥0∞)) z.2 ∂ν < ∞ := sorry

/-- The restriction of the canonical measure `ν` to jumps landing in `A`, viewed as a measure on
the jump-size coordinate. This is the textbook Lévy measure `ν(· × A)`. -/
def restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) (A : Set E) : Measure NNReal :=
  Measure.map (fun z : PositiveNNReal × E ↦ (z.1 : NNReal)) (ν.restrict (Prod.snd ⁻¹' A))

omit [PseudoMetricSpace E] in
/-- Unfolding `restrictedLevyMeasure ν A` gives the pushforward description of the slice
`ν(· × A)`. -/
theorem restrictedLevyMeasure_def (ν : Measure (PositiveNNReal × E)) (A : Set E) :
    restrictedLevyMeasure ν A =
      Measure.map (fun z : PositiveNNReal × E ↦ (z.1 : NNReal)) (ν.restrict (Prod.snd ⁻¹' A)) :=
  sorry

omit [PseudoMetricSpace E] in
/-- Helper for Theorem 24.21: the sliced Lévy measure has no atom at `0` because the jump-size
space is `(0, ∞)`. -/
lemma restrictedLevyMeasure_apply_zero
    (ν : Measure (PositiveNNReal × E)) (A : Set E) :
    restrictedLevyMeasure ν A {0} = 0 := sorry

/-- The random measure obtained from a Poisson point process on `(0, ∞) × E` by weighting each
point `(x,t)` with its jump size `x` and adding the deterministic measure `α`. -/
def poissonDrivenRandomMeasure
    (α : BoundedlyFiniteMeasure E) (X : Ω → Measure (PositiveNNReal × E)) (ω : Ω) : Measure E :=
  α + Measure.map Prod.snd ((X ω).withDensity fun z ↦ ((z.1 : NNReal) : ℝ≥0∞))

omit [MeasurableSpace Ω] in
/-- Unfolding `poissonDrivenRandomMeasure` gives the textbook formula
`Y(A) = α(A) + ∫ x 𝟙_A(t) X(d(x,t))`. -/
theorem poissonDrivenRandomMeasure_def
    (α : BoundedlyFiniteMeasure E) (X : Ω → Measure (PositiveNNReal × E)) (ω : Ω) :
    poissonDrivenRandomMeasure α X ω =
      α + Measure.map Prod.snd ((X ω).withDensity fun z ↦ ((z.1 : NNReal) : ℝ≥0∞)) := sorry

omit [MeasurableSpace Ω] [PseudoMetricSpace E] in
/-- Helper for Theorem 24.21: evaluating the sliced jump-size process on `B` is the same as
evaluating the original point process on the corresponding product slice in `(0, ∞) × E`. -/
lemma sliceJumpProcess_apply
    (X : Ω → Measure (PositiveNNReal × E)) (ω : Ω) (A : Set E) {B : Set NNReal}
    (hB : MeasurableSet B) :
    Measure.map (fun z : PositiveNNReal × E ↦ (z.1 : NNReal))
        ((X ω).restrict (Prod.snd ⁻¹' A)) B =
      X ω (((fun z : PositiveNNReal × E ↦ (z.1 : NNReal)) ⁻¹' B) ∩ Prod.snd ⁻¹' A) := sorry

/-- Helper for Theorem 24.21: the sliced Lévy measure inherits the subordinator side conditions
required by Theorem 24.17 from the bounded-set truncated first-moment hypothesis on `ν`. -/
lemma restrictedLevyMeasure_hasSubordinatorSideConditions
    {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A {0} = 0 ∧
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ))
        (restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A) := sorry

end ProbabilityTheory
