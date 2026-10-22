/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u v

variable {ι : Type u} [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι] [Countable ι]
variable {Ω : Type v} {m : MeasurableSpace Ω}
variable {E : Type*} [MeasurableSpace E]
variable {ℱ : Filtration ι m} {X : ι → Ω → E}

/-- Helper for Example 9.17: for a countable discrete time index with initial time `⊥`, the first
entrance time of an adapted process into a measurable set is a stopping time. -/
theorem hittingAfter_bot_isStoppingTime
    (hX : Adapted ℱ X) {K : Set E} (hK : MeasurableSet K) :
    IsStoppingTime ℱ (hittingAfter X K ⊥) := by
  simpa using Adapted.isStoppingTime_hittingAfter hX hK

/-- The last visit time of a discrete-time process to the set `K`, written as the supremum of the
visit times and taking values in `WithTop ℕ` so that infinitely many visits yield `⊤`. -/
def lastVisitTime (X : ℕ → Ω → E) (K : Set E) : Ω → WithTop ℕ :=
  fun ω ↦ sSup ((fun n : ℕ ↦ (n : WithTop ℕ)) '' {n | X n ω ∈ K})

namespace Example917

/-- Helper for Example 9.17: the two-point sample space used to separate the two branches of the
last-visit event. -/
abbrev twoPointSpace : Type u := ULift.{u} Bool

/-- Helper for Example 9.17: the ambient σ-algebra on the two-point space is the full one. -/
abbrev fullMeasurableSpace : MeasurableSpace twoPointSpace := ⊤

/-- Helper for Example 9.17: the filtration is trivial at time `0` and full after time `0`. -/
abbrev stepFiltrationSeq : ℕ → MeasurableSpace twoPointSpace
  | 0 => ⊥
  | _ + 1 => ⊤

/-- Helper for Example 9.17: the step filtration sequence is monotone. -/
theorem stepFiltrationSeq_mono : Monotone stepFiltrationSeq := by
  intro i j hij
  -- Only the transition from time `0` to later times changes the σ-algebra.
  cases i with
  | zero =>
      cases j with
      | zero =>
          simp [stepFiltrationSeq]
      | succ j =>
          simp [stepFiltrationSeq]
  | succ i =>
      cases j with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero _ hij)
      | succ j =>
          simp [stepFiltrationSeq]

/-- Helper for Example 9.17: every level of the step filtration is contained in the ambient
σ-algebra. -/
theorem stepFiltrationSeq_le (n : ℕ) : stepFiltrationSeq n ≤ fullMeasurableSpace := by
  -- The ambient measurable space is `⊤`, so containment is immediate.
  simp [stepFiltrationSeq, fullMeasurableSpace]

/-- Helper for Example 9.17: the step filtration used in the counterexample. -/
def stepFiltration : Filtration ℕ fullMeasurableSpace :=
  ⟨stepFiltrationSeq, stepFiltrationSeq_mono, stepFiltrationSeq_le⟩

/-- Helper for Example 9.17: the filtration is trivial at time `0`. -/
@[simp] theorem stepFiltration_zero : stepFiltration 0 = ⊥ := rfl

/-- Helper for Example 9.17: the filtration becomes full at every positive time. -/
@[simp] theorem stepFiltration_succ (n : ℕ) : stepFiltration (n + 1) = ⊤ := rfl

/-- Helper for Example 9.17: the process hits `0` at time `0` on both branches and once more at
time `1` only on the `true` branch. -/
def lastVisitProcess (n : ℕ) (ω : twoPointSpace) : ℝ :=
  if n = 0 then 0 else if n = 1 ∧ ω.down = true then 0 else 1

/-- Helper for Example 9.17: the explicit process is adapted to the step filtration. -/
theorem counterexampleAdapted : Adapted stepFiltration lastVisitProcess := by
  intro n
  cases n with
  | zero =>
      -- At time `0`, the process is constant, so measurability is immediate.
      have hconst : lastVisitProcess 0 = fun _ : twoPointSpace ↦ (0 : ℝ) := by
        ext ω
        simp [lastVisitProcess]
      rw [hconst]
      exact measurable_const
  | succ n =>
      -- After time `0`, the filtration is `⊤`, so every function is measurable.
      simpa [stepFiltration_succ, fullMeasurableSpace] using
        (measurable_from_top : Measurable[(⊤ : MeasurableSpace twoPointSpace)]
          (lastVisitProcess (n + 1)))

/-- Helper for Example 9.17: the last-visit time of the explicit process to the set `{0}`. -/
abbrev counterexampleLastVisitTime : twoPointSpace → WithTop ℕ :=
  lastVisitTime lastVisitProcess ({0} : Set ℝ)

/-- Helper for Example 9.17: the false branch visits `{0}` only at time `0`, while the true
branch visits `{0}` at times `0` and `1`. -/
theorem lastVisitTime_counterexample_values :
    counterexampleLastVisitTime (ULift.up false : twoPointSpace) = 0 ∧
      counterexampleLastVisitTime (ULift.up true : twoPointSpace) = 1 := by
  constructor
  · -- On the false branch, the visit set is exactly `{0}`.
    have hVisits :
        {n | lastVisitProcess n (ULift.up false) ∈ ({0} : Set ℝ)} = ({0} : Set ℕ) := by
      ext n
      cases n with
      | zero =>
          simp [lastVisitProcess]
      | succ n =>
          cases n with
          | zero =>
              simp [lastVisitProcess]
          | succ n =>
              simp [lastVisitProcess]
    unfold counterexampleLastVisitTime lastVisitTime
    rw [hVisits]
    simp
  · -- On the true branch, the visit set is exactly `{0, 1}`.
    have hVisits :
        {n | lastVisitProcess n (ULift.up true) ∈ ({0} : Set ℝ)} = ({0, 1} : Set ℕ) := by
      ext n
      cases n with
      | zero =>
          simp [lastVisitProcess]
      | succ n =>
          cases n with
          | zero =>
              simp [lastVisitProcess]
          | succ n =>
              simp [lastVisitProcess]
    have hImage :
        ((fun n : ℕ ↦ (n : WithTop ℕ)) '' ({0, 1} : Set ℕ)) =
          ({(0 : WithTop ℕ), 1} : Set (WithTop ℕ)) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        simpa using hn
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨1, by simp, rfl⟩
    unfold counterexampleLastVisitTime lastVisitTime
    rw [hVisits]
    rw [hImage]
    simp [sSup_insert, sSup_singleton]

/-- Helper for Example 9.17: the event `{ω | lastVisitTime X {0} ω ≤ 0}` is exactly the singleton
containing the branch that does not revisit `0` at time `1`. -/
theorem lastVisitTime_le_zero_eq_singleton :
    {ω : twoPointSpace | counterexampleLastVisitTime ω ≤ 0} =
      {(ULift.up false : twoPointSpace)} := by
  ext ω
  rcases ω with ⟨b⟩
  cases b
  · -- The false branch has last visit time `0`, so it belongs to the event.
    have hVisits :
        {n | lastVisitProcess n ({ down := false } : twoPointSpace) ∈ ({0} : Set ℝ)} =
          ({0} : Set ℕ) := by
      ext n
      cases n with
      | zero =>
          simp [lastVisitProcess]
      | succ n =>
          cases n with
          | zero =>
              simp [lastVisitProcess]
          | succ n =>
              simp [lastVisitProcess]
    have hfalse :
        counterexampleLastVisitTime ({ down := false } : twoPointSpace) = 0 := by
      unfold counterexampleLastVisitTime lastVisitTime
      rw [hVisits]
      simp
    constructor
    · intro _
      simp
    · intro _
      simpa [Set.mem_setOf_eq, hfalse]
  · -- The true branch has last visit time `1`, so it lies outside the event.
    have hVisits :
        {n | lastVisitProcess n ({ down := true } : twoPointSpace) ∈ ({0} : Set ℝ)} =
          ({0, 1} : Set ℕ) := by
      ext n
      cases n with
      | zero =>
          simp [lastVisitProcess]
      | succ n =>
          cases n with
          | zero =>
              simp [lastVisitProcess]
          | succ n =>
              simp [lastVisitProcess]
    have hImage :
        ((fun n : ℕ ↦ (n : WithTop ℕ)) '' ({0, 1} : Set ℕ)) =
          ({(0 : WithTop ℕ), 1} : Set (WithTop ℕ)) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        simpa using hn
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨1, by simp, rfl⟩
    have htrue :
        counterexampleLastVisitTime ({ down := true } : twoPointSpace) = 1 := by
      unfold counterexampleLastVisitTime lastVisitTime
      rw [hVisits]
      rw [hImage]
      simp [sSup_insert, sSup_singleton]
    constructor
    · intro hmem
      rw [Set.mem_setOf_eq, htrue] at hmem
      simp at hmem
    · intro hmem
      simp at hmem

end Example917

/-- Example 9.17: the last visit time `sup {t | X_t ∈ K}` of an adapted discrete-time process into
a measurable set need not be a stopping time in general. -/
theorem exists_lastVisitTime_not_isStoppingTime :
    ∃ (Ω : Type u) (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (K : Set ℝ),
      Adapted ℱ X ∧ MeasurableSet K ∧ ¬ IsStoppingTime ℱ (lastVisitTime X K) := by
  refine ⟨Example917.twoPointSpace, Example917.fullMeasurableSpace, Example917.stepFiltration,
    Example917.lastVisitProcess, ({0} : Set ℝ), Example917.counterexampleAdapted,
    measurableSet_singleton 0, ?_⟩
  intro hStopping
  -- The stopping-time criterion at time `0` forces the time-0 event to be measurable
  -- in the trivial σ-algebra.
  have hMeasurable :
      MeasurableSet[Example917.stepFiltration 0]
        {ω | lastVisitTime Example917.lastVisitProcess ({0} : Set ℝ) ω ≤ 0} :=
    hStopping.measurableSet_le 0
  -- Rewriting identifies this event with a nontrivial singleton.
  rw [Example917.lastVisitTime_le_zero_eq_singleton, Example917.stepFiltration_zero,
    MeasurableSpace.measurableSet_bot_iff] at hMeasurable
  rcases hMeasurable with hEmpty | hUniv
  · have :
        (ULift.up false : Example917.twoPointSpace) ∈
          ({ULift.up false} : Set Example917.twoPointSpace) := by
      simp
    rw [hEmpty] at this
    simp at this
  · have :
        (ULift.up true : Example917.twoPointSpace) ∈
          (Set.univ : Set Example917.twoPointSpace) := by
      simp
    rw [← hUniv] at this
    simp at this
