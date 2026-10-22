/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E]

/-- Source-facing definition for Definition 24.20: a random measure is infinitely divisible if, for
every positive integer `n`, it can be written as the sum of `n` iid random measures on the same
probability space. -/
def IsInfinitelyDivisibleRandomMeasure
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ n : ℕ+, ∃ Y : Fin n → Ω → Measure E,
    (∀ i, IsRandomMeasure P (Y i)) ∧
    IsIID Y (P : Measure Ω) ∧
    X = ∑ i, Y i

-- Proof sketch: apply the defining decomposition property with `n = 1`; then `X` is the singleton
-- sum of a random measure, so `X` itself is a random measure.
/-- An infinitely divisible random measure is, in particular, a random measure. -/
theorem IsInfinitelyDivisibleRandomMeasure.isRandomMeasure
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsInfinitelyDivisibleRandomMeasure P X) :
    IsRandomMeasure P X := by
  -- Use the defining decomposition at `n = 1`, where the sum reduces to a single coordinate.
  rcases hX 1 with ⟨Y, hYrm, _, hsum⟩
  have hsingle : X = Y 0 := by
    simpa [Fin.sum_univ_one] using hsum
  simpa [hsingle] using hYrm 0

-- Proof sketch: reinterpret the defining iid decompositions as the `Chap16` random-variable notion
-- on the measurable additive space `Measure E`, then apply the bridge theorem to the pushforward
-- law of `X`.
/-- Definition 24.20: the law of an infinitely divisible random measure is infinitely divisible in
the canonical sense of `ProbabilityMeasure.IsInfinitelyDivisible` on `Measure E`. -/
theorem IsInfinitelyDivisibleRandomMeasure.law_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsInfinitelyDivisibleRandomMeasure P X) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (ProbabilityMeasure.map P hX.isRandomMeasure.measurable.aemeasurable) := by
  have hXrv : IsInfinitelyDivisibleRandomVariable (P : Measure Ω) X := by
    intro n
    rcases hX n with ⟨Y, hYrm, hYiid, hsum⟩
    let ν : ProbabilityMeasure (Measure E) :=
      ProbabilityMeasure.map P (hYrm 0).measurable.aemeasurable
    let P' : ProbabilityMeasure (ULift.{v} Ω) :=
      ProbabilityMeasure.map P measurable_up.aemeasurable
    let Y' : Fin n → ULift.{v} Ω → Measure E := fun i ω ↦ Y i ω.down
    -- Package the reference coordinate's law directly from the pushforward definition.
    have hLaw0 : HasLaw (Y 0) ν P := by
      exact ⟨(hYrm 0).measurable.aemeasurable, rfl⟩
    -- Transport the reference law to every coordinate using identical distribution.
    have hLaw : ∀ i, HasLaw (Y i) ν P := by
      intro i
      simpa [ν] using (hYiid.identDistrib 0 i).hasLaw hLaw0
    have hY'_meas : ∀ i, Measurable (Y' i) := by
      intro i
      simpa [Y'] using (hYrm i).measurable.comp measurable_down
    have hY'_law : ∀ i, HasLaw (Y' i) ν P' := by
      intro i
      refine ⟨(hY'_meas i).aemeasurable, ?_⟩
      change Measure.map (Y' i) (P' : Measure (ULift.{v} Ω)) = ν
      rw [show (P' : Measure (ULift.{v} Ω)) = Measure.map ULift.up (P : Measure Ω) by rfl]
      rw [Measure.map_map (hY'_meas i) measurable_up]
      simpa [Y', ν] using (hLaw i).map_eq
    have hY'_indep : iIndepFun Y' (P' : Measure (ULift.{v} Ω)) := by
      rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hY'_meas i).aemeasurable)]
      calc
        Measure.map (fun ω i ↦ Y' i ω) (P' : Measure (ULift.{v} Ω))
            = Measure.map (fun ω i ↦ Y i ω) (P : Measure Ω) := by
                rw [show (P' : Measure (ULift.{v} Ω)) = Measure.map ULift.up (P : Measure Ω) by rfl]
                rw [Measure.map_map (by fun_prop) measurable_up]
                have hvec :
                    ((fun ω i ↦ Y' i ω) : ULift.{v} Ω → Fin n → Measure E) ∘ ULift.up =
                      (fun ω i ↦ Y i ω) := by
                  funext ω i
                  rfl
                rw [hvec]
        _ = Measure.pi (fun i ↦ Measure.map (Y i) (P : Measure Ω)) := by
              exact (iIndepFun_iff_map_fun_eq_pi_map
                (fun i ↦ (hYrm i).measurable.aemeasurable)).1
                hYiid.iIndepFun
        _ = Measure.pi (fun i ↦ Measure.map (Y' i) (P' : Measure (ULift.{v} Ω))) := by
              congr 1
              funext i
              rw [show (P' : Measure (ULift.{v} Ω)) = Measure.map ULift.up (P : Measure Ω) by rfl]
              rw [Measure.map_map (hY'_meas i) measurable_up]
              have hi :
                  (Y i : Ω → Measure E) = ((fun ω ↦ Y' i ω) : ULift.{v} Ω → Measure E) ∘ ULift.up := by
                funext ω
                rfl
              rw [hi]
    -- Rewrite the bundled finite sum equality into the pointwise function form required by Chap16.
    have hsum_pointwise : X = fun ω ↦ ∑ i, Y i ω := by
      funext ω
      simpa using congrFun hsum ω
    have hX_law :
        HasLaw X
          (ProbabilityMeasure.map P hX.isRandomMeasure.measurable.aemeasurable : Measure (Measure E))
          (P : Measure Ω) := by
      exact ⟨hX.isRandomMeasure.measurable.aemeasurable, rfl⟩
    have hSum_law :
        HasLaw (fun ω ↦ ∑ i, Y' i ω)
          (ProbabilityMeasure.map P hX.isRandomMeasure.measurable.aemeasurable : Measure (Measure E))
          (P' : Measure (ULift.{v} Ω)) := by
      refine ⟨(by fun_prop), ?_⟩
      rw [show (P' : Measure (ULift.{v} Ω)) = Measure.map ULift.up (P : Measure Ω) by rfl]
      rw [Measure.map_map (by fun_prop) measurable_up]
      calc
        Measure.map (((fun ω ↦ ∑ i, Y' i ω) : ULift.{v} Ω → Measure E) ∘ ULift.up) (P : Measure Ω)
            = Measure.map (fun ω ↦ ∑ i, Y i ω) (P : Measure Ω) := by
                have hsum' :
                    ((fun ω ↦ ∑ i, Y' i ω) : ULift.{v} Ω → Measure E) ∘ ULift.up =
                      (fun ω ↦ ∑ i, Y i ω) := by
                  funext ω
                  simp [Y']
                rw [hsum']
        _ = ProbabilityMeasure.map P hX.isRandomMeasure.measurable.aemeasurable := by
              simpa [hsum_pointwise]
    refine ⟨ULift.{v} Ω, inferInstance, P', ν, Y',
      hY'_meas, hY'_law, hY'_indep, ?_⟩
    exact ProbabilityTheory.HasLaw.identDistrib hX_law hSum_law
  exact (isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible
    (P := (P : Measure Ω)) (X := X) hX.isRandomMeasure.measurable).mp hXrv

end ProbabilityTheory
