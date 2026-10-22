/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {Ω : Type v} [MeasurableSpace Ω]

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Definition 19.23:
- `source-facing`: `escapeToSetProbability`, `escapeProbability`, the finite-boundary effective
  conductance formula `conductance C x₁ * escapeToSetProbability P X x₁ A₀`, and the effective
  conductance to infinity defined from those escape probabilities.
- `core/canonical`: the Chapter 19 conductance owner `conductance` from Definition 19.11 and the
  canonical positive-time ever-hit owner `F[P, X]`.
- `bridge/view`: the Chapter 19 escape probability lives in `ℝ≥0∞`, so its complement formula uses
  `ENNReal.ofReal ((F[P, X]) x₁ x₁)` while the theorem statements below still restate the source
  events in textbook coordinate form and connect them to the earlier owner predicate
  `IsRecurrentState`. -/

/-- The probability that the trajectory started from `x₁` reaches the set `A₀` before making its
first positive-time return to `x₁`. -/
def escapeToSetProbability (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (x₁ : E) (A₀ : Set E) : ℝ≥0∞ :=
  (P x₁ : Measure Ω) {ω | hittingAfter X A₀ 1 ω < hittingAfter X ({x₁} : Set E) 1 ω}

omit [MeasurableSpace Ω] [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Helper for Definition 19.23: escaping to `A₀` before the first positive-time return to `x₁`
is equivalent to hitting `A₀` at some positive time with no positive-time visit to `x₁` up to that
time. -/
private theorem escapeBeforeReturn_iff_exists_positiveHit
    (X : ℕ → Ω → E) (x₁ : E) (A₀ : Set E) (ω : Ω) :
    hittingAfter X A₀ 1 ω < hittingAfter X ({x₁} : Set E) 1 ω ↔
      ∃ n : ℕ, 0 < n ∧ X n ω ∈ A₀ ∧ ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x₁ := by
  constructor
  · intro hlt
    have hhitA_ne_top : hittingAfter X A₀ 1 ω ≠ ⊤ := by
      intro htop
      simp [htop] at hlt
    have hhitA_ge : (1 : WithTop ℕ) ≤ hittingAfter X A₀ 1 ω :=
      le_hittingAfter ω
    have hhitA_mem : X (hittingAfter X A₀ 1 ω).untopA ω ∈ A₀ :=
      hittingAfter_mem_set_of_ne_top hhitA_ne_top
    -- Proof comment: the strict inequality forces the first hit of `A₀` to be finite, so we use
    -- that hitting time itself as the witness time.
    lift (hittingAfter X A₀ 1 ω) to ℕ using hhitA_ne_top with n
    norm_cast at hlt hhitA_ge
    refine ⟨n, by simpa using hhitA_ge, by simpa using hhitA_mem, ?_⟩
    intro m hm_pos hm_le hm_eq
    have hreturn_le : hittingAfter X ({x₁} : Set E) 1 ω ≤ m :=
      hittingAfter_le_of_mem (by simpa using hm_pos) (by simpa [Set.mem_singleton_iff] using hm_eq)
    -- Proof comment: a positive-time return to `x₁` on or before `n` would contradict that the
    -- return time is strictly larger than the first hit of `A₀`.
    exact (not_le_of_gt hlt) <| le_trans hreturn_le
      (show (m : WithTop ℕ) ≤ (n : WithTop ℕ) from by simpa using hm_le)
  · rintro ⟨n, hn_pos, hnA, hnoReturn⟩
    have hhitA_le : hittingAfter X A₀ 1 ω ≤ n :=
      hittingAfter_le_of_mem (by simpa using hn_pos) hnA
    have hnot_return_le : ¬ hittingAfter X ({x₁} : Set E) 1 ω ≤ n := by
      intro hreturn_le
      have hreturn_iff :
          hittingAfter X ({x₁} : Set E) 1 ω ≤ n ↔
            ∃ m ∈ Set.Icc 1 n, X m ω ∈ ({x₁} : Set E) :=
        hittingAfter_le_iff
      rcases hreturn_iff.1 hreturn_le with ⟨m, hm_mem, hm_eq⟩
      exact hnoReturn m (by simpa using hm_mem.1) hm_mem.2
        (by simpa [Set.mem_singleton_iff] using hm_eq)
    have hn_lt_return : (n : WithTop ℕ) < hittingAfter X ({x₁} : Set E) 1 ω :=
      lt_of_not_ge hnot_return_le
    -- Proof comment: the witness time bounds the first hit of `A₀`, while the no-return
    -- hypothesis rules out any positive-time hit of `{x₁}` up to that same time.
    exact lt_of_le_of_lt hhitA_le hn_lt_return

-- Proof sketch: unfold `escapeToSetProbability`; it is defined as the probability, under the law
-- started from `x₁`, that the first positive entrance time into `A₀` is strictly smaller than the
-- first positive return time to `x₁`. In coordinates, this means that some positive time `n`
-- lands in `A₀` and there is no positive-time return to `x₁` up to and including time `n`.
omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The escape-to-set probability is the probability of hitting `A₀` before the first positive-time
return to `x₁`. -/
theorem escapeToSetProbability_def
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) (A₀ : Set E) :
    escapeToSetProbability P X x₁ A₀ =
      (P x₁ : Measure Ω) {ω |
        ∃ n : ℕ, 0 < n ∧ X n ω ∈ A₀ ∧ ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x₁} := by
  -- Proof comment: rewrite the defining hitting-time comparison pointwise using the pathwise
  -- bridge `escapeBeforeReturn_iff_exists_positiveHit`.
  unfold escapeToSetProbability
  congr 1
  ext ω
  exact escapeBeforeReturn_iff_exists_positiveHit X x₁ A₀ ω

-- Proof sketch: if `A₀ ⊆ A₁`, then the event "hit `A₀` before the first positive return to `x₁`"
-- is contained in the corresponding event for `A₁`. Apply monotonicity of the probability measure
-- `P x₁` to those events.
omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The escape-to-set probability is monotone in the target set. -/
theorem escapeToSetProbability_mono
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    Monotone (escapeToSetProbability P X x₁) := by
  intro A₀ A₁ hA01
  rw [escapeToSetProbability_def, escapeToSetProbability_def]
  -- Proof comment: enlarging the target set only enlarges the explicit escape event, so measure
  -- monotonicity closes the argument.
  exact measure_mono fun ω hω ↦ by
    rcases hω with ⟨n, hn_pos, hnA₀, hnoReturn⟩
    exact ⟨n, hn_pos, hA01 hnA₀, hnoReturn⟩

/-- The first clause of Definition 19.23 introduces the escape probability from `x₁` as the
probability of never making a positive-time return to `x₁`, equivalently
`1 - F(x₁,x₁)` where `F(x₁,x₁)` is the return probability. -/
def escapeProbability (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) : ℝ≥0∞ :=
  1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)

/-- Helper for Definition 19.23: the positive-time return event of a fixed state is measurable
when all coordinate maps are measurable. -/
private theorem measurableSet_exists_positiveEq
    (X : ℕ → Ω → E) (hX_meas : ∀ n : ℕ, Measurable (X n)) (x : E) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | 0 < n ∧ X n ω = x} := by
    ext ω
    simp
  rw [hUnion]
  refine MeasurableSet.iUnion fun n ↦ ?_
  by_cases hn : 0 < n
  · have hset : {ω | 0 < n ∧ X n ω = x} = X n ⁻¹' ({x} : Set E) := by
      ext ω
      simp [hn]
    -- Proof comment: on the positive-time branch, the event is just a singleton preimage.
    rw [hset]
    exact (hX_meas n) (measurableSet_singleton x)
  · have hset : {ω | 0 < n ∧ X n ω = x} = (∅ : Set Ω) := by
      ext ω
      simp [hn]
    -- Proof comment: on the zero-time branch, the positivity constraint makes the slice empty.
    rw [hset]
    simp

-- Semantic search note: `MeasureTheory.probReal_compl_eq_one_sub` and
-- `MeasureTheory.prob_compl_eq_one_sub₀` are the relevant complement-probability lemmas for the
-- no-return event once measurability or null-measurability is available.
-- Source repair note: the book states the no-return identity inside the ambient Markov-chain
-- measurability context; in this standalone item file the needed coordinate measurability is
-- restored explicitly as the premise `hX_meas`.
-- Proof sketch: if all coordinate maps `X n` are measurable, then the positive-return event
-- `{ω | ∃ n > 0, X n ω = x₁}` is measurable, and the no-return event is its complement, so under
-- the probability measure `P x₁` its mass is
-- `1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)`.
/-- Definition 19.23: the escape probability is the probability that the trajectory never returns
to `x₁` at a strictly positive time, provided each coordinate map `X n` is measurable so that the
positive-time return event is measurable. -/
theorem escapeProbability_eq_prob_no_return
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E)
    (hX_meas : ∀ n : ℕ, Measurable (X n)) :
    escapeProbability P X x₁ =
      (P x₁ : Measure Ω) {ω | ∀ n : ℕ, 0 < n → X n ω ≠ x₁} := by
  let hitEvent : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x₁}
  have hHitMeas : MeasurableSet hitEvent := by
    exact measurableSet_exists_positiveEq X hX_meas x₁
  have hNoReturn :
      hitEventᶜ = {ω | ∀ n : ℕ, 0 < n → X n ω ≠ x₁} := by
    -- Proof comment: the complement of a positive-time return event is exactly the event that no
    -- positive time returns to `x₁`.
    ext ω
    simp [hitEvent]
  -- Proof comment: rewrite the escape probability through the positive-return event, convert the
  -- real-valued probability to measure mass, and then pass to the complement event.
  calc
    escapeProbability P X x₁ = 1 - ENNReal.ofReal ((P x₁ : Measure Ω).real hitEvent) := by
      rw [escapeProbability, everHitsProbability_def]
    _ = 1 - (P x₁ : Measure Ω) hitEvent := by
      simp [Measure.real_def]
    _ = (P x₁ : Measure Ω) hitEventᶜ := by
      exact
        (MeasureTheory.prob_compl_eq_one_sub (μ := (P x₁ : Measure Ω)) (s := hitEvent)
          hHitMeas).symm
    _ = (P x₁ : Measure Ω) {ω | ∀ n : ℕ, 0 < n → X n ω ≠ x₁} := by
      rw [hNoReturn]

-- Proof sketch: `IsRecurrentState P X x₁` is the Chapter 17 owner statement that the positive-time
-- return probability `(F[P, X]) x₁ x₁` is `1`. By Definition 19.23, the escape probability is the
-- complementary mass `1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)`, so it vanishes exactly in the
-- recurrent case.
omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- A state has return probability `(F[P, X]) x₁ x₁ = 1` exactly when its Chapter 19 escape
probability is `0`. -/
theorem isRecurrentState_iff_escapeProbability_eq_zero
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    (F[P, X]) x₁ x₁ = 1 ↔ escapeProbability P X x₁ = 0 := by
  have hreturn_le_one : (F[P, X]) x₁ x₁ ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  rw [escapeProbability]
  constructor
  · intro hrec
    -- Proof comment: in the recurrent case the return probability already equals `1`, so the
    -- complementary escape probability is zero.
    simp [hrec]
  · intro hescape
    have hreturn_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((F[P, X]) x₁ x₁) := by
      rw [tsub_eq_zero_iff_le] at hescape
      exact hescape
    have hreturn_enn_le_one : ENNReal.ofReal ((F[P, X]) x₁ x₁) ≤ 1 := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by simp]
      exact ENNReal.ofReal_le_ofReal hreturn_le_one
    have hreturn_enn_eq_one : ENNReal.ofReal ((F[P, X]) x₁ x₁) = 1 :=
      le_antisymm hreturn_enn_le_one hreturn_ge_one
    -- Proof comment: once the truncated subtraction vanishes, the bounded return probability
    -- must saturate the value `1`.
    exact ENNReal.ofReal_eq_one.mp hreturn_enn_eq_one

/-- Helper for Definition 19.23: the cofinite target sets used in the effective conductance to
infinity are exactly the sets with finite complement that avoid the starting point `x₁`. -/
private class IsEffectiveConductanceTarget (x₁ : E) (A₀ : Set E) : Prop where
  cofinite : A₀ᶜ.Finite
  avoids_start : x₁ ∉ A₀

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Helper for Definition 19.23: the set of escape probabilities entering the infimum can be
described either as an image over admissible target sets or via the equivalent existential
characterization used in the source-facing formula. -/
theorem mem_effectiveConductanceTargetValues_iff
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) (r : ℝ≥0∞) :
    r ∈ escapeToSetProbability P X x₁ '' {A₀ : Set E | IsEffectiveConductanceTarget x₁ A₀} ↔
      ∃ A₀ : Set E, A₀ᶜ.Finite ∧ x₁ ∉ A₀ ∧ r = escapeToSetProbability P X x₁ A₀ := by
  constructor
  · rintro ⟨A₀, hA₀, hrfl⟩
    exact ⟨A₀, hA₀.cofinite, hA₀.avoids_start, hrfl.symm⟩
  · rintro ⟨A₀, hfinite, hx₁, hrfl⟩
    exact ⟨A₀, ⟨hfinite, hx₁⟩, hrfl.symm⟩

/-- The second clause of Definition 19.23 defines the effective conductance from `x₁` to infinity
as `conductance C x₁` times the infimum of the escape probabilities to cofinite sets avoiding
`x₁`. -/
def effectiveConductanceToInfinity
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) : ℝ≥0∞ :=
  conductance C x₁ *
    sInf (escapeToSetProbability P X x₁ '' {A₀ : Set E | IsEffectiveConductanceTarget x₁ A₀})

end

-- Proof sketch: unfold `effectiveConductanceToInfinity`; it is defined exactly as `conductance C
-- x₁` multiplied by the infimum of the escape-to-set probabilities over all cofinite subsets
-- `A₀` avoiding `x₁`.
/-- The effective conductance to infinity is the conductance at `x₁` times the infimum of the
escape probabilities toward cofinite sets not containing `x₁`. -/
theorem effectiveConductanceToInfinity_def
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    effectiveConductanceToInfinity C P X x₁ =
      conductance C x₁ *
        sInf {r : ℝ≥0∞ |
          ∃ A₀ : Set E, A₀ᶜ.Finite ∧ x₁ ∉ A₀ ∧ r = escapeToSetProbability P X x₁ A₀} := by
  -- Proof comment: rewrite the infimum set from the internal admissible-target image back to the
  -- source-facing existential description.
  unfold effectiveConductanceToInfinity
  rw [show
      escapeToSetProbability P X x₁ '' {A₀ : Set E | IsEffectiveConductanceTarget x₁ A₀} =
        {r : ℝ≥0∞ |
          ∃ A₀ : Set E, A₀ᶜ.Finite ∧ x₁ ∉ A₀ ∧ r = escapeToSetProbability P X x₁ A₀} by
    ext r
    exact mem_effectiveConductanceTargetValues_iff P X x₁ r]

end ProbabilityTheory
