/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u v w

variable {Ω : Type u} {ι : Type v} {S : Type w} {mΩ : MeasurableSpace Ω}
variable [PartialOrder ι] [Countable ι] {ℱ : Filtration ι mΩ}
variable [MeasurableSpace S] {X : ι → Ω → S} {τ : Ω → ι}

/-- Lemma 9.23: for a countable time index set, evaluating an adapted process at a finite
stopping time gives a random variable that is measurable with respect to the stopping-time
σ-algebra `𝓕_τ`. Here finiteness is encoded by taking `τ : Ω → ι` and viewing it as a
`WithTop ι`-valued stopping time. -/
-- Proof sketch: for a measurable set `A` and time `t`, rewrite
-- `{ω | X (τ ω) ω ∈ A} ∩ {ω | τ ω ≤ t}` as the countable union over `s ≤ t` of
-- `{ω | τ ω = s} ∩ X s ⁻¹' A`; adaptedness gives measurability of `X s ⁻¹' A` in `ℱ s`, and the
-- stopping-time property gives measurability of `{τ = s}` in `ℱ s`.
theorem adapted_measurable_eval_stopping_time
    (hX : Adapted ℱ X)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ι)) :
    Measurable[hτ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  classical
  intro s hs
  rw [hτ.measurableSet]
  constructor
  · have h_preimage :
        (fun ω ↦ X (τ ω) ω) ⁻¹' s =
          ⋃ i : ι, ({ω | (τ ω : WithTop ι) = i} ∩ X i ⁻¹' s) := by
      ext ω
      simp
    rw [h_preimage]
    refine MeasurableSet.iUnion fun i ↦ ?_
    exact ℱ.le i _ ((hτ.measurableSet_eq_of_countable i).inter ((hX i) hs))
  · intro t
    have h_preimage_inter :
        (fun ω ↦ X (τ ω) ω) ⁻¹' s ∩ {ω | (τ ω : WithTop ι) ≤ t} =
          ⋃ i : ι,
            ({ω | (τ ω : WithTop ι) = i} ∩ X i ⁻¹' s ∩ {ω | (i : WithTop ι) ≤ t}) := by
      ext ω
      simp [and_assoc]
    rw [h_preimage_inter]
    refine MeasurableSet.iUnion fun i ↦ ?_
    by_cases hit : i ≤ t
    · simpa [hit, Set.inter_assoc] using
        ℱ.mono hit _ ((hτ.measurableSet_eq_of_countable i).inter ((hX i) hs))
    · simp [hit]
