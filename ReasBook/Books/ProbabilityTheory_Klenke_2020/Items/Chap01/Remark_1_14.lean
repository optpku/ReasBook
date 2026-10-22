/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {Ω : Type u}

/-- Remark 1.14 (1): The set-theoretic `liminf` of a sequence of sets is the event that only
finitely many complements occur. -/
-- Proof sketch: Rewrite `liminf` along `atTop` using the standard `iSup`-`iInf` description for
-- sequences, unfold set membership, and identify eventual membership with finiteness of the set of
-- indices where `ω ∉ A n`.
theorem set_liminf_eq_finite_notMem (A : ℕ → Set Ω) :
    liminf A atTop = {ω : Ω | {n : ℕ | ω ∉ A n}.Finite} := by
  -- Transport the standard cofinite characterization along `Nat.cofinite_eq_atTop`.
  simpa [Nat.cofinite_eq_atTop] using (Filter.cofinite.liminf_set_eq (s := A))

/-- Remark 1.14 (2): The set-theoretic `limsup` of a sequence of sets is the event that infinitely
many of the sets occur. -/
-- Proof sketch: Use the standard description of `limsup` along `atTop`, unfold membership, and
-- identify frequent membership with infinitude of the set of indices where `ω ∈ A n`.
theorem set_limsup_eq_infinite_mem (A : ℕ → Set Ω) :
    limsup A atTop = {ω : Ω | {n : ℕ | ω ∈ A n}.Infinite} := by
  -- Transport the standard cofinite characterization along `Nat.cofinite_eq_atTop`.
  simpa [Nat.cofinite_eq_atTop] using (Filter.cofinite.limsup_set_eq (s := A))

/-- Remark 1.14 (3): The set-theoretic `liminf` of a sequence of sets is contained in its
set-theoretic `limsup`. -/
-- Proof sketch: If only finitely many complements occur, then membership holds for all large
-- indices, hence in particular for infinitely many indices; combine the characterizations from the
-- previous two statements.
theorem set_liminf_subset_limsup (A : ℕ → Set Ω) :
    liminf A atTop ⊆ limsup A atTop := by
  intro ω hω
  -- Eventual membership immediately implies frequent membership.
  rw [mem_liminf_iff_eventually_mem] at hω
  rw [mem_limsup_iff_frequently_mem]
  exact hω.frequently

/-- Remark 1.14 (4): The indicator of the set-theoretic `liminf` is the pointwise `liminf` of the
real-valued indicator functions. -/
-- Proof sketch: Evaluate both sides at `ω`, split on whether `ω` belongs to `liminf A atTop`, and
-- use that the resulting indicator sequence is eventually `1` or has infinitely many `0`s.
theorem indicator_liminf_eq_liminf_indicator (A : ℕ → Set Ω) :
    (liminf A atTop).indicator (1 : Ω → ℝ) =
      fun ω : Ω ↦ liminf (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop := by
  classical
  ext ω
  by_cases hω : ω ∈ liminf A atTop
  · -- On the liminf event, the indicator sequence is eventually constant equal to `1`.
    have h_eventually : ∀ᶠ n in atTop, ω ∈ A n ↔ ω ∈ liminf A atTop := by
      have h_mem : ∀ᶠ n in atTop, ω ∈ A n := by
        simpa [mem_liminf_iff_eventually_mem] using hω
      exact h_mem.mono fun n hn ↦ by simp [hω, hn]
    have h_tendsto :
        Tendsto (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop
          (nhds ((liminf A atTop).indicator (1 : Ω → ℝ) ω)) := by
      exact (tendsto_indicator_const_apply_iff_eventually
        (L := atTop) (A := liminf A atTop) (As := A) (b := (1 : ℝ)) ω).2 h_eventually
    -- A convergent eventually-`1` sequence has liminf equal to `1`.
    simpa [Set.indicator_of_mem, hω] using h_tendsto.liminf_eq.symm
  · -- Outside the liminf event, zeros occur infinitely often, while all values stay nonnegative.
    have h_finite : ¬ {n : ℕ | ω ∉ A n}.Finite := by
      simpa [set_liminf_eq_finite_notMem (A := A)] using hω
    have h_infinite : {n : ℕ | ω ∉ A n}.Infinite :=
      (Set.finite_or_infinite {n : ℕ | ω ∉ A n}).elim
        (fun hs ↦ False.elim (h_finite hs))
        id
    have h_nonneg : ∀ᶠ n in atTop, 0 ≤ (A n).indicator (1 : Ω → ℝ) ω :=
      Filter.Eventually.of_forall fun n ↦
        Set.indicator_apply_nonneg fun _ ↦ zero_le_one
    have h_le_one : ∀ᶠ n in atTop, (A n).indicator (1 : Ω → ℝ) ω ≤ 1 :=
      Filter.Eventually.of_forall fun n ↦
        Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
    have h_freq_zero : ∃ᶠ n in atTop, (A n).indicator (1 : Ω → ℝ) ω ≤ 0 := by
      rw [Nat.frequently_atTop_iff_infinite]
      refine h_infinite.mono ?_
      intro n hn
      have h_eq : (A n).indicator (1 : Ω → ℝ) ω = 0 :=
        Set.indicator_of_notMem hn _
      simp [h_eq]
    have h_cobdd_ge :
        atTop.IsCoboundedUnder (· ≥ ·)
          (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) := by
      exact (Filter.isBoundedUnder_of_eventually_le h_le_one).isCoboundedUnder_ge
    have h_liminf :
        liminf (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop = 0 := by
      apply le_antisymm
      · exact Filter.liminf_le_of_frequently_le h_freq_zero
          (Filter.isBoundedUnder_of_eventually_ge h_nonneg)
      · exact Filter.le_liminf_of_le h_cobdd_ge h_nonneg
    simpa [Set.indicator_of_notMem, hω] using h_liminf.symm

/-- Remark 1.14 (5): The indicator of the set-theoretic `limsup` is the pointwise `limsup` of the
real-valued indicator functions. -/
-- Proof sketch: Evaluate both sides at `ω`, distinguish whether `ω` lies in `limsup A atTop`, and
-- use that the indicator sequence takes the value `1` infinitely often exactly in that case.
theorem indicator_limsup_eq_limsup_indicator (A : ℕ → Set Ω) :
    (limsup A atTop).indicator (1 : Ω → ℝ) =
      fun ω : Ω ↦ limsup (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop := by
  classical
  ext ω
  by_cases hω : ω ∈ limsup A atTop
  · -- On the limsup event, the indicator sequence hits `1` infinitely often and never exceeds `1`.
    have h_infinite : {n : ℕ | ω ∈ A n}.Infinite := by
      simpa [set_limsup_eq_infinite_mem (A := A)] using hω
    have h_nonneg : ∀ᶠ n in atTop, 0 ≤ (A n).indicator (1 : Ω → ℝ) ω :=
      Filter.Eventually.of_forall fun n ↦
        Set.indicator_apply_nonneg fun _ ↦ zero_le_one
    have h_le_one : ∀ᶠ n in atTop, (A n).indicator (1 : Ω → ℝ) ω ≤ 1 :=
      Filter.Eventually.of_forall fun n ↦
        Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
    have h_freq_one : ∃ᶠ n in atTop, 1 ≤ (A n).indicator (1 : Ω → ℝ) ω := by
      rw [Nat.frequently_atTop_iff_infinite]
      refine h_infinite.mono ?_
      intro n hn
      have hnA : ω ∈ A n := hn
      have h_eq : (A n).indicator (1 : Ω → ℝ) ω = 1 :=
        Set.indicator_of_mem hnA _
      simp [h_eq]
    have h_cobdd_le :
        atTop.IsCoboundedUnder (· ≤ ·)
          (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) := by
      exact (Filter.isBoundedUnder_of_eventually_ge h_nonneg).isCoboundedUnder_le
    have h_limsup :
        limsup (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop = 1 := by
      apply le_antisymm
      · exact Filter.limsup_le_of_le h_cobdd_le h_le_one
      · exact Filter.le_limsup_of_frequently_le h_freq_one
          (Filter.isBoundedUnder_of_eventually_le h_le_one)
    simpa [Set.indicator_of_mem, hω] using h_limsup.symm
  · -- Outside the limsup event, the indicator sequence is eventually constant equal to `0`.
    have h_eventually : ∀ᶠ n in atTop, ω ∈ A n ↔ ω ∈ (∅ : Set Ω) := by
      have h_notfreq : ¬ ∃ᶠ n in atTop, ω ∈ A n := by
        rw [← mem_limsup_iff_frequently_mem]
        exact hω
      have h_notmem : ∀ᶠ n in atTop, ω ∉ A n := by
        rw [Filter.Frequently, not_not] at h_notfreq
        exact h_notfreq
      exact h_notmem.mono fun n hn ↦ by simp [hn]
    have h_tendsto :
        Tendsto (fun n : ℕ ↦ (A n).indicator (1 : Ω → ℝ) ω) atTop
          (nhds (((∅ : Set Ω)).indicator (1 : Ω → ℝ) ω)) := by
      exact (tendsto_indicator_const_apply_iff_eventually
        (L := atTop) (A := (∅ : Set Ω)) (As := A) (b := (1 : ℝ)) ω).2 h_eventually
    -- A convergent eventually-`0` sequence has limsup equal to `0`.
    simpa [Set.indicator_of_notMem, hω] using h_tendsto.limsup_eq.symm

variable [MeasurableSpace Ω]

/-- Remark 1.14 (6): A set-theoretic `liminf` of measurable sets is measurable. -/
-- Proof sketch: Expand `liminf` as a countable union of countable intersections along `atTop` and
-- apply closure of measurable sets under countable unions and intersections.
theorem measurableSet_set_liminf (A : ℕ → Set Ω) (hA : ∀ n : ℕ, MeasurableSet (A n)) :
    MeasurableSet (liminf A atTop) := by
  -- The standard measurable-set theorem for liminf along `atTop` applies directly.
  exact MeasurableSet.measurableSet_liminf hA

/-- Remark 1.14 (7): A set-theoretic `limsup` of measurable sets is measurable. -/
-- Proof sketch: Expand `limsup` as a countable intersection of countable unions along `atTop` and
-- apply closure of measurable sets under countable intersections and unions.
theorem measurableSet_set_limsup (A : ℕ → Set Ω) (hA : ∀ n : ℕ, MeasurableSet (A n)) :
    MeasurableSet (limsup A atTop) := by
  -- The standard measurable-set theorem for limsup along `atTop` applies directly.
  exact MeasurableSet.measurableSet_limsup hA
