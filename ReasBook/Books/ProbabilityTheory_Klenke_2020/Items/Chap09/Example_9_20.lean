/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory TopologicalSpace

noncomputable section

universe u

variable {ι : Type u} [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι] [Countable ι]
variable {Ω : Type*} {m : MeasurableSpace Ω}
variable {ℱ : Filtration ι m} {X : ι → Ω → ℝ}

-- Proof sketch: apply `Adapted.isStoppingTime_hittingAfter` to the measurable half-line `[K, ∞)`,
-- with initial time `⊥`, and let the target `IsStoppingTime` type determine the implicit set and
-- starting index.
/-- The first entrance time of an adapted process into `[K, ∞)` is a stopping time. -/
theorem leastGE_isStoppingTime
    (hX : Adapted ℱ X) (K : ℝ) :
    IsStoppingTime ℱ (leastGE X K) := by
  simpa [leastGE] using Adapted.isStoppingTime_hittingAfter hX measurableSet_Ici

/-- Helper for Example 9.20: if an adapted real-valued process ever exceeds a level `c`, then the
corresponding event is globally measurable. -/
lemma measurableSet_exists_index_gt
    (hX : Adapted ℱ X) (c : ℝ) :
    MeasurableSet {ω | ∃ i, c < X i ω} := by
  -- Rewrite the existential event as a countable union of measurable coordinate events.
  have hUnion :
      {ω | ∃ i, c < X i ω} = ⋃ i, {ω | c < X i ω} := by
    ext ω
    simp
  rw [hUnion]
  refine MeasurableSet.iUnion fun i ↦ ?_
  -- Each coordinate map is measurable because the process is adapted.
  exact measurableSet_lt measurable_const
    (Adapted.measurable (f := ℱ) (u := X) (i := i) hX)

/-- Helper for Example 9.20: if the first entrance time into `[K, ∞)` is finite, then the
trajectory has reached at least the level `K` at that entrance time. -/
lemma exists_index_ge_of_leastGE_ne_top
    (K : ℝ) {ω : Ω} (hτne : leastGE X K ω ≠ ⊤) :
    ∃ j, K ≤ X j ω := by
  -- Evaluate the process at the concrete entrance index `untopA`.
  refine ⟨(leastGE X K ω).untopA, ?_⟩
  simpa [leastGE, Set.mem_Ici] using
    (hittingAfter_mem_set_of_ne_top
      (u := X) (s := Set.Ici K) (n := ⊥) (ω := ω) hτne)

-- Proof sketch: let `τ` be the first entrance time of `X` into `[K, ∞)`, which is a stopping
-- time by the discrete hitting-time theorem. The event `{ω | ∃ i, K - 5 < X i ω}` is globally
-- measurable as a countable union of measurable coordinate events, and on each slice `{τ ≤ t}` it
-- contains that slice because `X` has already reached the higher level `K`.
/-- Example 9.20: in the discrete/right-discrete setting formalized by mathlib's hitting-time API,
if `τ` is the first entrance time of an adapted real-valued process `X` into `[K, ∞)`, then the
event that `X` exceeds `K - 5` at some time belongs to the stopping-time `σ`-algebra `F_τ`. -/
theorem ever_above_sub_five_measurable_at_first_entrance
    (hX : Adapted ℱ X) (K : ℝ) :
    MeasurableSet[(leastGE_isStoppingTime hX K).measurableSpace]
      {ω | ∃ i, K - 5 < X i ω} := by
  let hτ : IsStoppingTime ℱ (leastGE X K) := leastGE_isStoppingTime hX K
  rw [hτ.measurableSet]
  refine ⟨measurableSet_exists_index_gt hX (K - 5), ?_⟩
  intro t
  -- On the slice `{τ ≤ t}`, the process has already hit `[K, ∞)`, hence also exceeds `K - 5`.
  have hSlice :
      {ω | leastGE X K ω ≤ t} ⊆ {ω | ∃ i, K - 5 < X i ω} := by
    intro ω hω
    have hτne : leastGE X K ω ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp) hω
    rcases exists_index_ge_of_leastGE_ne_top (X := X) K hτne with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    linarith
  -- The slice intersection therefore collapses to the stopping event itself.
  rw [Set.inter_eq_right.mpr hSlice]
  exact hτ.measurableSet_le t

/-- A concrete process that hits the level `0` immediately and only reveals a possible later jump
above `5` after time `0`. -/
def firstEntranceCounterexampleProcess : ℕ → ℝ → ℝ
  | 0, _ => 0
  | _ + 1, x => if x ≤ 0 then 0 else 10

/-- Helper for Example 9.20: the time-`0` coordinate of the counterexample process is the constant
zero function. -/
lemma firstEntranceCounterexampleProcess_zero_eq_const :
    firstEntranceCounterexampleProcess 0 = fun _ : ℝ ↦ (0 : ℝ) := by
  -- The process is defined to start at zero on every sample point.
  funext x
  simp [firstEntranceCounterexampleProcess]

-- Proof sketch: each time marginal is either constant or a two-valued measurable function defined
-- by the Borel half-line `(0, ∞)`.
/-- Every time slice of the counterexample process is strongly measurable. -/
theorem firstEntranceCounterexampleProcess_stronglyMeasurable :
    ∀ n, StronglyMeasurable (firstEntranceCounterexampleProcess n) := by
  intro n
  cases n with
  | zero =>
      -- At time `0`, the process is constant.
      simpa [firstEntranceCounterexampleProcess_zero_eq_const] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ)))
  | succ n =>
      -- For later times, the slice is a two-valued measurable `if`-function.
      rw [stronglyMeasurable_iff_measurable]
      simpa [firstEntranceCounterexampleProcess] using
        (Measurable.ite (p := fun x : ℝ ↦ x ≤ 0)
          (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const)

/-- Helper for Example 9.20: the natural filtration of the counterexample process is trivial at
time `0` because the only observed coordinate is constant. -/
lemma firstEntranceCounterexampleInitialFiltration_eq_bot :
    (Filtration.natural firstEntranceCounterexampleProcess
      firstEntranceCounterexampleProcess_stronglyMeasurable) 0 = ⊥ := by
  -- The time-`0` natural filtration is the comap of the constant initial coordinate.
  have hFiltration :
      (Filtration.natural firstEntranceCounterexampleProcess
        firstEntranceCounterexampleProcess_stronglyMeasurable) 0 =
        MeasurableSpace.comap (firstEntranceCounterexampleProcess 0) Real.measurableSpace := by
    simp [Filtration.natural]
  rw [hFiltration, firstEntranceCounterexampleProcess_zero_eq_const]
  exact MeasurableSpace.comap_const (m := Real.measurableSpace) (b := (0 : ℝ))

-- Proof sketch: apply the discrete hitting-time theorem to the adapted counterexample process and
-- the measurable closed half-line `[0, ∞)`.
/-- The counterexample first-entrance time is a stopping time. -/
theorem firstEntranceCounterexampleTime_isStoppingTime :
    IsStoppingTime
      (Filtration.natural firstEntranceCounterexampleProcess
        firstEntranceCounterexampleProcess_stronglyMeasurable)
      (leastGE firstEntranceCounterexampleProcess 0) := by
  simpa [leastGE] using Adapted.isStoppingTime_hittingAfter
    (Filtration.stronglyAdapted_natural firstEntranceCounterexampleProcess_stronglyMeasurable).adapted
    measurableSet_Ici

/-- Helper for Example 9.20: the counterexample process enters `[0, ∞)` immediately, so its first
entrance time is identically `0`. -/
lemma leastGE_firstEntranceCounterexampleProcess_eq_zero :
    leastGE firstEntranceCounterexampleProcess 0 = fun _ ↦ (0 : WithTop ℕ) := by
  -- The process starts in the target set, so the hitting time is at most `0` and hence exactly `0`.
  funext x
  apply le_antisymm
  · simpa [leastGE] using
      (hittingAfter_le_of_mem (u := firstEntranceCounterexampleProcess) (s := Set.Ici (0 : ℝ))
        (n := 0) (i := 0) (ω := x) le_rfl (by simp [firstEntranceCounterexampleProcess]))
  · simpa [leastGE] using
      (le_hittingAfter (u := firstEntranceCounterexampleProcess) (s := Set.Ici (0 : ℝ))
        (n := 0) (ω := x))

/-- Helper for Example 9.20: the event that the counterexample process ever exceeds `5` is exactly
the positive half-line `{x | 0 < x}`. -/
lemma firstEntranceCounterexampleProcess_exists_gt_five_iff (x : ℝ) :
    (∃ n, (5 : ℝ) < firstEntranceCounterexampleProcess n x) ↔ 0 < x := by
  constructor
  · intro hx
    rcases hx with ⟨n, hn⟩
    cases n with
    | zero =>
        -- At time `0`, the process value is `0`, so it cannot exceed `5`.
        simp [firstEntranceCounterexampleProcess] at hn
        linarith
    | succ n =>
        -- At later times, exceeding `5` forces the branch `x > 0`.
        by_cases hx0 : x ≤ 0
        · simp [firstEntranceCounterexampleProcess, hx0] at hn
          linarith
        · exact lt_of_not_ge hx0
  · intro hx
    -- For positive `x`, the process jumps to `10` at time `1`.
    refine ⟨1, ?_⟩
    have hx0 : ¬ x ≤ 0 := not_le.mpr hx
    simp [firstEntranceCounterexampleProcess, hx0]
    norm_num

-- Proof sketch: the stopping time is identically `0`, so `F_τ = F_0`, which is the trivial
-- `σ`-algebra because the time-`0` coordinate of the process is constant. The event that the
-- process ever exceeds `5` is `{x | 0 < x}`, which is not measurable in that trivial
-- `σ`-algebra.
/-- A concrete counterexample showing that the later event of ever exceeding `5` need not belong to
the stopping-time `σ`-algebra at the first entrance time. -/
theorem ever_above_five_not_measurable_at_first_entrance_counterexample :
    ¬ MeasurableSet[firstEntranceCounterexampleTime_isStoppingTime.measurableSpace]
      {x | ∃ n, (5 : ℝ) < firstEntranceCounterexampleProcess n x} := by
  intro hMeasurable
  -- The hitting time is always at most `0`, so the stopping-time σ-algebra is contained in `F₀`.
  have hτle : ∀ x : ℝ, leastGE firstEntranceCounterexampleProcess 0 x ≤ 0 := by
    intro x
    simpa [leastGE_firstEntranceCounterexampleProcess_eq_zero]
  have hSpaceLe :
      firstEntranceCounterexampleTime_isStoppingTime.measurableSpace ≤
        (Filtration.natural firstEntranceCounterexampleProcess
          firstEntranceCounterexampleProcess_stronglyMeasurable) 0 :=
    firstEntranceCounterexampleTime_isStoppingTime.measurableSpace_le_of_le_const hτle
  have hSpaceBot :
      firstEntranceCounterexampleTime_isStoppingTime.measurableSpace = ⊥ := by
    -- The initial natural filtration is trivial, so every measurable stopping-time event is trivial.
    rw [firstEntranceCounterexampleInitialFiltration_eq_bot] at hSpaceLe
    exact le_antisymm hSpaceLe bot_le
  have hEvent :
      {x | ∃ n, (5 : ℝ) < firstEntranceCounterexampleProcess n x} = {x : ℝ | 0 < x} := by
    -- Normalize the event pointwise using the explicit form of the process.
    ext x
    simp [firstEntranceCounterexampleProcess_exists_gt_five_iff]
  rw [hSpaceBot, hEvent, MeasurableSpace.measurableSet_bot_iff] at hMeasurable
  rcases hMeasurable with hEmpty | hUniv
  · -- The positive half-line is nonempty because it contains `1`.
    have hOne : (1 : ℝ) ∈ ({x : ℝ | 0 < x} : Set ℝ) := by
      norm_num
    rw [hEmpty] at hOne
    simp at hOne
  · -- The positive half-line is not all of `ℝ` because it omits `0`.
    have hZero : (0 : ℝ) ∈ (Set.univ : Set ℝ) := by
      simp
    have : (0 : ℝ) ∈ ({x : ℝ | 0 < x} : Set ℝ) := by
      simpa [hUniv] using hZero
    simp at this
