/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/- Layering for Definition 17.33:
- `totalVisitsFrom` is the primitive pathwise visit-count observable from time `N` onward.
- `greenFunctionFrom` is the owner abstraction for the expected visit count from time `N` onward.
- `totalVisits` and `greenFunction` are the `N = 0` source-facing specializations.
- Later positive-time variants should reuse `greenFunctionFrom P X 1` rather than introducing
  parallel Green-function owners. -/

/-- The total number of visits of the trajectory `X` to the state `y` from time `N` onward,
counted by the counting measure on the set of visit times. -/
def totalVisitsFrom (X : ℕ → Ω → E) (y : E) (N : ℕ) (ω : Ω) : ℝ≥0∞ :=
  Measure.count {n : ℕ | N ≤ n ∧ X n ω = y}

/-- The Green function counting visits to `y` from time `N` onward under the start law `P x`. -/
def greenFunctionFrom
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (N : ℕ) (x y : E) : ℝ≥0∞ :=
  ∫⁻ ω, totalVisitsFrom X y N ω ∂(P x : Measure Ω)

/-- The total number of visits of the trajectory `X` to the state `y`, counted by the counting
measure on the set of visit times. -/
def totalVisits (X : ℕ → Ω → E) (y : E) (ω : Ω) : ℝ≥0∞ :=
  totalVisitsFrom X y 0 ω

/-- The Green function `G(x, y)` is the expected total number of visits of the trajectory `X` to
the state `y` under the initial law `P x`; the pathwise visit count is `totalVisits X y`. -/
def greenFunction (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ≥0∞ :=
  greenFunctionFrom P X 0 x y

notation "G[" P ", " X "; " N "]" =>
  greenFunctionFrom P X N

notation "G[" P ", " X "]" =>
  greenFunction P X

-- Proof sketch: unfold `totalVisitsFrom`; it is defined to be the counting measure of the set of
-- visit times to `y` from time `N` onward.
omit [MeasurableSpace Ω] in
/-- Evaluating `totalVisitsFrom` counts the visit times of the trajectory at the state `y` from
time `N` onward. -/
theorem totalVisitsFrom_eq_count (X : ℕ → Ω → E) (y : E) (N : ℕ) (ω : Ω) :
    totalVisitsFrom X y N ω = Measure.count {n : ℕ | N ≤ n ∧ X n ω = y} := by
  -- Proof comment: `totalVisitsFrom` is defined as this counting measure.
  rfl

-- Proof sketch: unfold `greenFunctionFrom`; this is exactly the lower integral of
-- `totalVisitsFrom X y N` under the initial law `P x`.
/-- The Green function from time `N` onward is the expectation of the corresponding visit count. -/
theorem greenFunctionFrom_eq_lintegral_totalVisitsFrom
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (N : ℕ) (x y : E) :
    (G[P, X; N]) x y = ∫⁻ ω, totalVisitsFrom X y N ω ∂(P x : Measure Ω) := by
  -- Proof comment: `greenFunctionFrom` is defined as the lower integral of `totalVisitsFrom`.
  rfl

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Helper for Definition 17.33: pathwise, the visit count from time `N` onward is the sum of
the time-indexed visit indicators. -/
private lemma tsumVisitIndicators_eq_totalVisitsFrom
    (X : ℕ → Ω → E) (y : E) (N : ℕ) (ω : Ω) :
    totalVisitsFrom X y N ω =
      ∑' n : ℕ,
        Set.indicator {ω' | N ≤ n ∧ X n ω' = y} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  -- Proof comment: rewrite the counting measure as the encard of the visit-time set and then
  -- expand that encard as the sum of singleton indicators over `ℕ`.
  rw [totalVisitsFrom_eq_count, Measure.count_apply MeasurableSet.of_discrete]
  calc
    ({n : ℕ | N ≤ n ∧ X n ω = y}).encard =
        (↑(ENat.card {n : ℕ | N ≤ n ∧ X n ω = y}) : ℝ≥0∞) := by
          rw [ENat.card_coe_set_eq]
    _ =
        ∑' _ : {n : ℕ | N ≤ n ∧ X n ω = y}, (1 : ℝ≥0∞) := by
          exact
            (ENNReal.tsum_one :
              ∑' _ : {n : ℕ | N ≤ n ∧ X n ω = y}, (1 : ℝ≥0∞) =
                (↑(ENat.card {n : ℕ | N ≤ n ∧ X n ω = y}) : ℝ≥0∞)).symm
    _ = ∑' n : ℕ,
          Set.indicator {ω' | N ≤ n ∧ X n ω' = y} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
          simpa [Set.indicator_apply] using
            (tsum_subtype {n : ℕ | N ≤ n ∧ X n ω = y} (fun _ : ℕ ↦ (1 : ℝ≥0∞)))

-- Proof sketch: write `totalVisitsFrom X y N` as the counting measure of the set of visit times
-- from `N` onward, expand that counting measure as the sum of singleton indicators, and
-- interchange the lower integral with the countable sum.
/-- Definition 17.33: for a stochastic process on a measurable state space with measurable
singletons, the Green function from time `N` onward equals the series of the time-`n`
probabilities that the trajectory is at the state `y` for times `n ≥ N`. -/
theorem greenFunctionFrom_eq_tsum_visitProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X)
    (N : ℕ) (x y : E) :
    (G[P, X; N]) x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | N ≤ n ∧ X n ω = y} := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hEventMeas : ∀ n : ℕ, MeasurableSet {ω | N ≤ n ∧ X n ω = y} := by
    intro n
    by_cases hNn : N ≤ n
    · have hEq : {ω | N ≤ n ∧ X n ω = y} = X n ⁻¹' ({y} : Set E) := by
        ext ω
        simp [hNn]
      rw [hEq]
      exact (hX.measurable n) (measurableSet_singleton y)
    · have hEmpty : {ω | N ≤ n ∧ X n ω = y} = (∅ : Set Ω) := by
        ext ω
        simp [hNn]
      rw [hEmpty]
      simp
  -- Proof comment: normalize the visit count pathwise to an indicator series and then integrate
  -- term-by-term.
  calc
    (G[P, X; N]) x y = ∫⁻ ω, totalVisitsFrom X y N ω ∂μ := by
      rw [greenFunctionFrom_eq_lintegral_totalVisitsFrom]
    _ = ∫⁻ ω,
          ∑' n : ℕ,
            Set.indicator {ω' | N ≤ n ∧ X n ω' = y} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            rw [tsumVisitIndicators_eq_totalVisitsFrom]
    _ = ∑' n : ℕ,
          ∫⁻ ω,
            Set.indicator {ω' | N ≤ n ∧ X n ω' = y} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂μ := by
            rw [lintegral_tsum fun n ↦
              (measurable_const.indicator (hEventMeas n)).aemeasurable]
    _ = ∑' n : ℕ, μ {ω | N ≤ n ∧ X n ω = y} := by
          refine tsum_congr fun n ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := μ) (s := {ω | N ≤ n ∧ X n ω = y})
              (hEventMeas n))

-- Proof sketch: specialize `greenFunctionFrom_eq_tsum_visitProbabilities` to `N = 1` and rewrite
-- `1 ≤ n` as `0 < n`.
/-- For a stochastic process, the positive-time Green function `G[P, X; 1] x y` is the series of
the strictly positive-time visit probabilities. -/
theorem greenFunctionFrom_one_eq_tsum_positiveStateProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    (G[P, X; 1]) x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} := by
  simpa [Nat.succ_le_iff] using greenFunctionFrom_eq_tsum_visitProbabilities P X hX 1 x y

-- Proof sketch: combine
-- `greenFunctionFrom_one_eq_tsum_positiveStateProbabilities` with `everHitsProbability_def`; both
-- are built from the same strictly positive-time event `{ω | ∃ n > 0, X n ω = y}`.
/-- For a stochastic process on a measurable state space with measurable singletons, positivity of
the positive-time Green function is equivalent to positivity of the ever-hit probability. -/
theorem greenFunctionFrom_one_pos_iff_everHitsProbability_pos
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    0 < (G[P, X; 1]) x y ↔ 0 < (F[P, X]) x y := by
  let μ : Measure Ω := (P x : Measure Ω)
  let A : ℕ → Set Ω := fun n ↦ {ω | 0 < n ∧ X n ω = y}
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} = ⋃ n : ℕ, A n := by
    ext ω
    simp [A]
  constructor
  · intro hgreen
    have hExists : ∃ n : ℕ, 0 < μ (A n) := by
      by_contra hnone
      have hzero : ∀ n : ℕ, μ (A n) = 0 := by
        intro n
        exact le_antisymm (le_of_not_gt fun h ↦ hnone ⟨n, h⟩) bot_le
      have hsumZero : ∑' n : ℕ, μ (A n) = 0 := ENNReal.tsum_eq_zero.2 hzero
      rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x y] at hgreen
      rw [show (∑' n : ℕ, μ {ω | 0 < n ∧ X n ω = y}) = ∑' n : ℕ, μ (A n) by rfl] at hgreen
      rw [hsumZero] at hgreen
      exact lt_irrefl _ hgreen
    rcases hExists with ⟨n, hnpos⟩
    have hSubset : A n ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
      intro ω hω
      exact ⟨n, hω.1, hω.2⟩
    have hUnionPos : 0 < μ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} :=
      lt_of_lt_of_le hnpos (measure_mono hSubset)
    rw [everHitsProbability_def, Measure.real_def]
    exact ENNReal.toReal_pos (ne_of_gt hUnionPos) (measure_ne_top μ _)
  · intro hhit
    have hMeasureNeZero : μ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} ≠ 0 := by
      rw [everHitsProbability_def, Measure.real_def] at hhit
      intro hzero
      rw [hzero, ENNReal.toReal_zero] at hhit
      exact lt_irrefl _ hhit
    obtain ⟨n, hnpos⟩ :=
      exists_measure_pos_of_not_measure_iUnion_null
        (μ := μ) (s := A) (by simpa [hUnion, A] using hMeasureNeZero)
    have hn : 0 < n := by
      by_contra hn
      have hEmpty : A n = (∅ : Set Ω) := by
        ext ω
        simp [A, hn]
      have : μ (A n) = 0 := by simp [hEmpty]
      exact (ne_of_gt hnpos) this
    rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x y]
    have hle : μ (A n) ≤ ∑' m : ℕ, μ (A m) := ENNReal.le_tsum n
    exact lt_of_lt_of_le hnpos (by simpa [A] using hle)

end MeasurableState

-- Proof sketch: unfold `totalVisits`; it is defined to be the counting measure of the set of
-- times at which the trajectory is at `y`.
omit [MeasurableSpace Ω] in
/-- Evaluating `totalVisits` counts the visit times of the trajectory at the state `y`. -/
theorem totalVisits_eq_count (X : ℕ → Ω → E) (y : E) (ω : Ω) :
    totalVisits X y ω = Measure.count {n : ℕ | X n ω = y} := by
  -- Proof comment: `totalVisits` is the `N = 0` specialization of `totalVisitsFrom`.
  simpa [totalVisits] using totalVisitsFrom_eq_count X y 0 ω

-- Proof sketch: unfold `greenFunction`; this is exactly the lower integral of `totalVisits X y`
-- under the initial law `P x`.
/-- The Green function is the expectation of the total visit count. -/
theorem greenFunction_eq_lintegral_totalVisits
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) :
    (G[P, X]) x y = ∫⁻ ω, totalVisits X y ω ∂(P x : Measure Ω) := by
  -- Proof comment: `greenFunction` is the `N = 0` specialization of `greenFunctionFrom`.
  simpa [greenFunction, totalVisits] using
    greenFunctionFrom_eq_lintegral_totalVisitsFrom P X 0 x y

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

-- Proof sketch: write `totalVisits X y` as the counting measure of the set of visit times, expand
-- that counting measure as the sum of the singleton indicators, and interchange the lower integral
-- with the countable sum.
/-- For a stochastic process on a measurable state space with measurable singletons, the Green
function equals the series of the time-`n` probabilities that the trajectory is at the state `y`.
-/
theorem greenFunction_eq_tsum_stateProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    (G[P, X]) x y = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} := by
  -- Proof comment: this is the `N = 0` specialization of the general Green-series formula.
  simpa [greenFunction] using greenFunctionFrom_eq_tsum_visitProbabilities P X hX 0 x y

end MeasurableState

end ProbabilityTheory
