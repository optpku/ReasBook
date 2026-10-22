/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_5

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-
Layering for Theorem 19.6:
- `source-facing`: `F_A` and `S_A`, the textbook first-hit probability of the killed chain and the
  corresponding positive-probability reachability set.
- `core/canonical`: `hittingAfter` for the first time the trajectory enters `insert y A`,
  `stoppedValue` for the state reached at that time, `IsHarmonicOutside` for the source
  harmonicity assumption on `E \ A`, and `discreteMatrixKernel p` for the transition kernel of
  the discrete chain.
- `auxiliary`: `IsHarmonicForKilledChain`, the one-step killed-kernel equation used later as a
  derived helper, not as the main hypothesis of Theorem 19.6.
  - `bridge/view`: the internal event that the first hit of `insert y A` occurs at the state `y`.
  For `y ∉ A` this is exactly the usual event `τ_y < τ_A`; for `y ∈ A` it is the
  boundary-inclusive first-hit event `X_{τ_A} = y`.
-/

/-- The event that the trajectory `X` first hits `insert y A` at the state `y`, where the first
hit may occur at time `0`. For `y ∉ A`, this is the usual event `τ_y < τ_A`; for `y ∈ A`, it is
the event that the first hit of `A` occurs at `y`. -/
private def firstHitAtStateEvent (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- The quantity `F_A x y` is the probability under `P x` that the first hit of `insert y A`
occurs at the state `y`, where the hit may occur at time `0`. Equivalently, for `y ∉ A` it is the
probability of the event `τ_y < τ_A`, while for `y ∈ A` it is the first-hit distribution of `A`
at the point `y`. -/
def F_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

/-- The set `S_A x` consists of states that can be reached from `x` with positive probability
as the first point where the trajectory enters `insert y A`; in particular it contains the
boundary points of `A` that occur with positive first-hit probability. -/
def S_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x : E) : Set E :=
  {y | 0 < F_A P X A x y}

/-- Membership in `S_A x` is equivalent to strict positivity of the first-hit probability
`F_A x y`. -/
theorem mem_S_A_iff
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) :
    y ∈ S_A P X A x ↔ 0 < F_A P X A x y :=
  Iff.rfl

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- A real-valued function is harmonic for the chain killed on entering `A` if, at each
state outside `A`, its value equals the average over the next-step mass that stays outside `A`.
This auxiliary owner is weaker than the source hypothesis of Theorem 19.6, which uses
`IsHarmonicOutside (discreteMatrixKernel p) A f`. -/
def IsHarmonicForKilledChain (p : E → E → ℝ≥0∞) (A : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x : E⦄, x ∉ A →
    Integrable f ((discreteMatrixKernel p x).restrict Aᶜ) ∧
      f x = ∫ y, f y ∂((discreteMatrixKernel p x).restrict Aᶜ)

/-- Unfolded form of `IsHarmonicForKilledChain`. -/
theorem isHarmonicForKilledChain_iff
    (p : E → E → ℝ≥0∞) (A : Set E) (f : E → ℝ) :
    IsHarmonicForKilledChain p A f ↔
      ∀ ⦃x : E⦄, x ∉ A →
        Integrable f ((discreteMatrixKernel p x).restrict Aᶜ) ∧
          f x = ∫ y, f y ∂((discreteMatrixKernel p x).restrict Aᶜ) :=
  Iff.rfl

end

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable {A : Set E} {f : E → ℝ} {x₀ : E}

include p in
/-- Helper for Theorem 19.6: every state belongs to its own first-hit positivity set `S_A x₀`
because the process starts from `x₀` at time `0`. -/
private theorem self_mem_S_A_of_realization {x₀ : E} :
    x₀ ∈ S_A P X A x₀ := by
  -- Proof comment: the event defining `F_A x₀ x₀` already occurs at time `0` on the sure event
  -- `X 0 = x₀`.
  have hstart_one : (P x₀ : Measure Ω) (X 0 ⁻¹' ({x₀} : Set E)) = 1 := by
    have hmap : (P x₀ : Measure Ω).map (X 0) = Measure.dirac x₀ := by
      simpa using (inferInstance : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).initial_eq x₀
    calc
      (P x₀ : Measure Ω) (X 0 ⁻¹' ({x₀} : Set E))
          = ((P x₀ : Measure Ω).map (X 0)) ({x₀} : Set E) := by
              simpa using
                (Measure.map_apply
                  ((inferInstance : IsMarkovProcessRealization
                    (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
                  (measurableSet_singleton x₀)).symm
      _ = 1 := by simp [hmap]
  let hitNow : Set Ω :=
    {ω | hittingAfter X (insert x₀ A) 0 ω < ⊤ ∧
        stoppedValue X (hittingAfter X (insert x₀ A) 0) ω = x₀}
  have hsubset : X 0 ⁻¹' ({x₀} : Set E) ⊆ hitNow := by
    -- Proof comment: on `X 0 = x₀`, the first hit of `insert x₀ A` happens immediately at `x₀`.
    intro ω hω
    have hx0 : X 0 ω = x₀ := by simpa using hω
    have hτ0 : hittingAfter X (insert x₀ A) 0 ω = 0 := by
      refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert x₀ A) (n := 0) ω)
      exact hittingAfter_le_of_mem (by simp) (by simp [hx0])
    constructor
    · simp [hτ0]
    · simpa [hitNow, stoppedValue, hτ0] using hω
  have hhitNow : (P x₀ : Measure Ω) hitNow = 1 := by
    refine le_antisymm ?_ ?_
    · calc
        (P x₀ : Measure Ω) hitNow ≤ (P x₀ : Measure Ω) Set.univ := measure_mono (by simp)
        _ = 1 := by simp
    · calc
        1 = (P x₀ : Measure Ω) (X 0 ⁻¹' ({x₀} : Set E)) := hstart_one.symm
        _ ≤ (P x₀ : Measure Ω) hitNow := measure_mono hsubset
  have hreal_pos : 0 < (P x₀ : Measure Ω).real hitNow := by
    rw [Measure.real_def, hhitNow]
    norm_num
  rw [mem_S_A_iff]
  exact hreal_pos

include p in
/-- Helper for Theorem 19.6: a global greatest value of `f` restricts to a greatest value on
the first-hit positivity set `S_A(x₀)`. -/
private theorem isGreatest_image_S_A_of_isGreatest_range
    (hmax : IsGreatest (Set.range f) (f x₀)) :
    IsGreatest (f '' S_A P X A x₀) (f x₀) := by
  refine ⟨⟨x₀, self_mem_S_A_of_realization (p := p) (P := P) (X := X) (A := A), rfl⟩, ?_⟩
  -- Proof comment: every value coming from `S_A(x₀)` is in the global range of `f`.
  rintro _ ⟨z, _, rfl⟩
  exact hmax.2 ⟨z, rfl⟩

include p in
/-- Helper for Theorem 19.6: if `y ∈ S_A(x₀)`, then one deterministic exact-time slice of the
first-hit event for `insert y A` already has positive `P x₀`-measure. -/
private theorem existsPosMeasureExactFirstHitSliceOfMemSA
    {y : E} (hy : y ∈ S_A P X A x₀) :
    ∃ n : ℕ,
      0 <
        (P x₀ : Measure Ω)
          {ω | hittingAfter X (insert y A) 0 ω = n ∧
              stoppedValue X (hittingAfter X (insert y A) 0) ω = y} := by
  let event : Set Ω := firstHitAtStateEvent X A y
  let slice : ℕ → Set Ω := fun n ↦
    {ω | hittingAfter X (insert y A) 0 ω = n ∧
        stoppedValue X (hittingAfter X (insert y A) 0) ω = y}
  have hEvent_pos : 0 < (P x₀ : Measure Ω) event := by
    -- Proof comment: `y ∈ S_A(x₀)` is exactly the positivity of the defining first-hit event.
    rw [mem_S_A_iff, F_A, Measure.real_def] at hy
    by_contra hEvent_pos
    have hzero : (P x₀ : Measure Ω) event = 0 := le_antisymm (le_of_not_gt hEvent_pos) bot_le
    rw [hzero, ENNReal.toReal_zero] at hy
    exact lt_irrefl _ hy
  have hEvent_ne_zero : (P x₀ : Measure Ω) event ≠ 0 := by
    exact ne_of_gt hEvent_pos
  have hEvent_union : event = ⋃ n : ℕ, slice n := by
    ext ω
    constructor
    · intro hω
      have hτ_ne_top : hittingAfter X (insert y A) 0 ω ≠ ⊤ := ne_of_lt hω.1
      lift hittingAfter X (insert y A) 0 ω to ℕ using hτ_ne_top with n hn
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      constructor
      · exact hn.symm
      · exact hω.2
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      refine ⟨?_, hn.2⟩
      rw [hn.1]
      simp
  obtain ⟨n, hn_pos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null
      (μ := (P x₀ : Measure Ω)) (s := slice) (by
        simpa [hEvent_union] using hEvent_ne_zero)
  exact ⟨n, by exact_mod_cast hn_pos⟩

include p in
/-- Helper for Theorem 19.6: the deterministic truncation at time `n` of the chain stopped on the
first entrance into `A`. -/
private abbrev truncatedStoppedValueOnA (n : ℕ) : Ω → E :=
  fun ω ↦ stoppedValue X (fun ω' ↦ min (hittingAfter X A 0 ω') (n : ℕ∞)) ω

include p in
/-- Helper for Theorem 19.6: an exact-time slice of the first hit of `insert y A` at `y`
forces the deterministically truncated stopped value at time `n` to equal `y`. -/
private theorem exactFirstHitSlice_subset_truncatedStoppedValueEq
    (n : ℕ) (y : E) :
    {ω | hittingAfter X (insert y A) 0 ω = n ∧
        stoppedValue X (hittingAfter X (insert y A) 0) ω = y} ⊆
      {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} := by
  intro ω hω
  have hXn : X n ω = y := by
    simpa [stoppedValue, hω.1] using hω.2
  by_cases hyA : y ∈ A
  · -- Proof comment: if `y ∈ A`, then `insert y A = A`, so both stopping surfaces coincide.
    have hτA_eq : hittingAfter X A 0 ω = n := by
      simpa [hyA, Set.insert_eq_of_mem] using hω.1
    have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = (n : ℕ∞) := by
      rw [hτA_eq]
      exact min_self _
    simpa [truncatedStoppedValueOnA, stoppedValue, hmin] using hXn
  · -- Proof comment: otherwise no `A`-hit can occur by time `n`, so the deterministic
    -- truncation still reads the raw time-`n` state `y`.
    by_cases hτA_top : hittingAfter X A 0 ω = ⊤
    · simpa [truncatedStoppedValueOnA, stoppedValue, hτA_top] using hXn
    · have hτA_ne_top : hittingAfter X A 0 ω ≠ ⊤ := hτA_top
      lift hittingAfter X A 0 ω to ℕ using hτA_ne_top with m hm
      have hm_memA : X m ω ∈ A := by
        have hτA_ne_top' : hittingAfter X A 0 ω ≠ ⊤ := by
          rw [← hm]
          simp
        have hmem :
            X (hittingAfter X A 0 ω).untopA ω ∈ A := by
          simpa [stoppedValue] using
            hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hτA_ne_top'
        have hm_idx : (hittingAfter X A 0 ω).untopA = m := by
          rw [← hm, WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        simpa [hm_idx] using hmem
      have hm_gt : n < m := by
        by_contra hm_not_gt
        have hm_le : m ≤ n := le_of_not_gt hm_not_gt
        have hinsert_le :
            hittingAfter X (insert y A) 0 ω ≤ m := by
          exact
            hittingAfter_le_of_mem (u := X) (s := insert y A) (n := 0) (ω := ω)
              (Nat.zero_le m) (by simp [hm_memA])
        have hn_le_m : (n : ℕ∞) ≤ m := by
          simpa [hω.1] using hinsert_le
        have hmn : m = n := by
          exact le_antisymm (by exact_mod_cast hm_le) (by exact_mod_cast hn_le_m)
        have hXnA : X n ω ∈ A := by simpa [hmn] using hm_memA
        exact hyA (by simpa [hXn] using hXnA)
      have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = (n : ℕ∞) := by
        have hm_gt' : (n : ℕ∞) < m := by exact_mod_cast hm_gt
        have hle : (n : ℕ∞) ≤ hittingAfter X A 0 ω := by
          rw [← hm]
          exact le_of_lt hm_gt'
        exact min_eq_right hle
      simpa [truncatedStoppedValueOnA, stoppedValue, hmin] using hXn

include p in
/-- Helper for Theorem 19.6: on an exact-time first-hit slice for `insert y A`, the raw time-`n`
state is already `y`. -/
private theorem exactFirstHitSlice_subset_timeStateEq
    (n : ℕ) (y : E) :
    {ω | hittingAfter X (insert y A) 0 ω = n ∧
        stoppedValue X (hittingAfter X (insert y A) 0) ω = y} ⊆
      {ω | X n ω = y} := by
  intro ω hω
  -- Proof comment: once the hitting time is known to be exactly `n`, `stoppedValue` is just the
  -- value of the path at time `n`.
  simpa [stoppedValue, hω.1] using hω.2

include p in
/-- Helper for Theorem 19.6: if `z ∉ A` and the first hit of `insert z A` occurs exactly at time
`n`, then the chain has not hit `A` by time `n`. -/
private theorem exactFirstHitOutside_lt_hittingAfter
    {n : ℕ} {z : E} (hzA : z ∉ A) {ω : Ω}
    (hω : hittingAfter X (insert z A) 0 ω = n ∧
      stoppedValue X (hittingAfter X (insert z A) 0) ω = z) :
    (n : ℕ∞) < hittingAfter X A 0 ω := by
  have hXn : X n ω = z := by
    -- Proof comment: on the exact-time slice, the stopped value is just the raw time-`n` state.
    exact exactFirstHitSlice_subset_timeStateEq (p := p) (X := X) (A := A) n z hω
  by_contra hnot_lt
  have hτA_le : hittingAfter X A 0 ω ≤ (n : ℕ∞) := le_of_not_gt hnot_lt
  have hτA_lt_top : hittingAfter X A 0 ω < ⊤ := by
    exact lt_of_le_of_lt hτA_le (by simp : (n : ℕ∞) < ⊤)
  lift hittingAfter X A 0 ω to ℕ using hτA_lt_top.ne with m hm
  have hm_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
    simpa [hm] using hτA_lt_top.ne
  have hm_memA' :
      X (hittingAfter X A 0 ω).untopA ω ∈ A := by
    simpa [stoppedValue] using
      hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hm_ne_top
  have hm_idx : (hittingAfter X A 0 ω).untopA = m := by
    rw [← hm, WithTop.untopA_eq_untop (by simp)]
    exact (WithTop.untop_eq_iff (by simp)).2 rfl
  have hm_memA : X m ω ∈ A := by
    simpa [hm_idx] using hm_memA'
  have hm_le_n' : (m : ℕ∞) ≤ (n : ℕ∞) := by
    exact hτA_le
  have hinsert_le : hittingAfter X (insert z A) 0 ω ≤ m := by
    -- Proof comment: any realized hit of `A` is already a hit of `insert z A`.
    exact
      hittingAfter_le_of_mem (u := X) (s := insert z A) (n := 0) (ω := ω)
        (Nat.zero_le m) (by simp [hm_memA])
  have hn_le_m' : (n : ℕ∞) ≤ (m : ℕ∞) := by
    simpa [hω.1] using hinsert_le
  have hmn : m = n := by
    exact ENat.coe_inj.mp <| le_antisymm hm_le_n' hn_le_m'
  have hXnA : X n ω ∈ A := by
    simpa [hmn] using hm_memA
  exact hzA (by simpa [hXn] using hXnA)

/-- Helper for Theorem 19.6: if the chain is still strictly before the first entrance time of
`A` at time `n`, then the deterministic truncation at time `n + 1` has not stopped yet either. -/
private theorem truncatedStoppedValueOnA_succ_eq_time_on_preHit
    (n : ℕ) :
    Set.EqOn
      (truncatedStoppedValueOnA (X := X) (A := A) (n + 1))
      (X (n + 1))
      {ω | (n : ℕ∞) < hittingAfter X A 0 ω} := by
  intro ω hω
  -- Route correction: earlier attempts unfolded `hittingAfter` too aggressively here. The only
  -- needed fact is the order normalization `n < τ_A ⇒ n + 1 ≤ τ_A`.
  have hsucc_le :
      (((n + 1 : ℕ) : ℕ∞)) ≤ hittingAfter X A 0 ω := by
    refine le_of_not_gt ?_
    intro hlt
    exact (not_lt_of_ge (ENat.lt_coe_add_one_iff.mp hlt)) hω
  -- Proof comment: once the truncation index `n + 1` is still before `τ_A`, the `min` selects
  -- that deterministic time, so `stoppedValue` is simply `X (n + 1)`.
  have hmin :
      min (hittingAfter X A 0 ω) (((n + 1 : ℕ) : ℕ∞)) = (((n + 1 : ℕ) : ℕ∞)) :=
    min_eq_right hsucc_le
  have hidx :
      (min (hittingAfter X A 0 ω) (((n + 1 : ℕ) : ℕ∞))).untopA = n + 1 := by
    rw [hmin]
    rfl
  rw [truncatedStoppedValueOnA, stoppedValue, hidx]

include p in
/-- Helper for Theorem 19.6: if an exact first-hit slice for `insert z A` is extended by one
step to the state `w`, then the stopped-on-`A` deterministic truncation at time `n + 1` also
lands at `w`. -/
private theorem exactFirstHitSlice_stepEvent_subset_truncatedStoppedValueSucc
    {n : ℕ} {z w : E} (hzA : z ∉ A) :
    ({ω | hittingAfter X (insert z A) 0 ω = n ∧
        stoppedValue X (hittingAfter X (insert z A) 0) ω = z} ∩ {ω | X (n + 1) ω = w}) ⊆
      {ω | truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = w} := by
  intro ω hω
  rcases hω with ⟨hslice, hstep⟩
  have hpre :
      (n : ℕ∞) < hittingAfter X A 0 ω :=
    exactFirstHitOutside_lt_hittingAfter
      (p := p) (X := X) (A := A) hzA hslice
  have htrunc :
      truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = X (n + 1) ω :=
    truncatedStoppedValueOnA_succ_eq_time_on_preHit
      (X := X) (A := A) n hpre
  have hstep' : X (n + 1) ω = w := by
    simpa using hstep
  simpa [htrunc] using hstep'

include p in
/-- Helper for Theorem 19.6: before the first entrance into `A`, the deterministic truncation
still reads the raw time-`n` state. -/
private theorem truncatedStoppedValueOnA_eq_time_on_preHit
    (n : ℕ) :
    Set.EqOn (truncatedStoppedValueOnA (X := X) (A := A) n) (X n)
      {ω | (n : ℕ∞) < hittingAfter X A 0 ω} := by
  intro ω hω
  -- Proof comment: on `{n < τ_A}`, the minimum in the truncation is the deterministic time `n`.
  have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hω)
  simpa [truncatedStoppedValueOnA, stoppedValue, hmin]

include p in
/-- Helper for Theorem 19.6: once the first entrance time is at most `n`, the `n` and `n + 1`
deterministic truncations agree. -/
private theorem truncatedStoppedValueOnA_succ_eqOn_postHit
    (n : ℕ) :
    Set.EqOn
      (truncatedStoppedValueOnA (X := X) (A := A) (n + 1))
      (truncatedStoppedValueOnA (X := X) (A := A) n)
      {ω | hittingAfter X A 0 ω ≤ n} := by
  intro ω hω
  -- Proof comment: once `τ_A ≤ n`, both deterministic cutoffs reduce to the same stopped index.
  have hmin_n : min (hittingAfter X A 0 ω) (n : ℕ∞) = hittingAfter X A 0 ω := min_eq_left hω
  have hτ_le_succ : hittingAfter X A 0 ω ≤ ((n + 1 : ℕ) : ℕ∞) := by
    exact le_trans hω (show (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) by simp)
  have hmin_succ :
      min (hittingAfter X A 0 ω) (((n + 1 : ℕ) : ℕ∞)) = hittingAfter X A 0 ω :=
    min_eq_left hτ_le_succ
  rw [truncatedStoppedValueOnA, truncatedStoppedValueOnA, stoppedValue, stoppedValue,
    hmin_n, hmin_succ]

include p in
/-- Helper for Theorem 19.6: if the deterministic truncation of the chain stopped on `A`
equals `z`, then the trajectory has already realized the first-hit event defining `F_A x₀ z`. -/
private theorem truncatedStoppedOnAValueEvent_subset_firstHitAtStateEvent
    (n : ℕ) (z : E) :
    {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = z} ⊆
      firstHitAtStateEvent X A z := by
  intro ω hω
  by_cases hzA : z ∈ A
  · have hnot_pre : ¬ (n : ℕ∞) < hittingAfter X A 0 ω := by
      intro hlt
      have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hlt)
      have hXn : X n ω = z := by
        simpa [stoppedValue, hmin] using hω
      have hnotA :
          X n ω ∉ A :=
        notMem_of_lt_hittingAfter (u := X) (s := A) (n := 0) (ω := ω) (k := n) hlt (by simp)
      exact hnotA (by simpa [hXn] using hzA)
    have hτA_le : hittingAfter X A 0 ω ≤ n := by
      exact le_of_not_gt hnot_pre
    have hτ_event :
        hittingAfter X (insert z A) 0 ω < ⊤ := by
      simpa [hzA, Set.insert_eq_of_mem] using lt_of_le_of_lt hτA_le (by simp)
    have hvalue :
        stoppedValue X (hittingAfter X (insert z A) 0) ω = z := by
        have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = hittingAfter X A 0 ω :=
          min_eq_left hτA_le
        simpa [truncatedStoppedValueOnA, hzA, Set.insert_eq_of_mem, stoppedValue, hmin] using hω
    exact ⟨hτ_event, hvalue⟩
  · have hpre : (n : ℕ∞) < hittingAfter X A 0 ω := by
      by_contra hnot_pre
      have hτA_le : hittingAfter X A 0 ω ≤ n := le_of_not_gt hnot_pre
      have hτ_event :
          hittingAfter X A 0 ω < ⊤ := lt_of_le_of_lt hτA_le (by simp)
      have hmemA :
          stoppedValue X (hittingAfter X A 0) ω ∈ A := by
        simpa [stoppedValue] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hτ_event.ne
      have hvalueA :
          stoppedValue X (fun ω' ↦ min (hittingAfter X A 0 ω') (n : ℕ∞)) ω ∈ A := by
        have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = hittingAfter X A 0 ω :=
          min_eq_left hτA_le
        simpa [stoppedValue, hmin] using hmemA
      exact hzA (hω ▸ hvalueA)
    have hτ_insert_le :
        hittingAfter X (insert z A) 0 ω ≤ n := by
      exact
        hittingAfter_le_of_mem (u := X) (s := insert z A) (n := 0) (ω := ω)
          (by simp) (by
            have hmin : min (hittingAfter X A 0 ω) (n : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hpre)
            have hXn : X n ω = z := by
              simpa [truncatedStoppedValueOnA, stoppedValue, hmin] using hω
            simp [hXn])
    have hτ_insert_lt : hittingAfter X (insert z A) 0 ω < ⊤ :=
      lt_of_le_of_lt hτ_insert_le (by simp)
    have hinsert_mem :
        stoppedValue X (hittingAfter X (insert z A) 0) ω ∈ insert z A := by
      simpa [stoppedValue] using
        hittingAfter_mem_set_of_ne_top
          (u := X) (s := insert z A) (n := 0) (ω := ω) hτ_insert_lt.ne
    have hnotA :
        stoppedValue X (hittingAfter X (insert z A) 0) ω ∉ A := by
      intro hA
      lift hittingAfter X (insert z A) 0 ω to ℕ using hτ_insert_lt.ne with m hm
      have hm_memA : X m ω ∈ A := by
        have hmem :
            X (hittingAfter X (insert z A) 0 ω).untopA ω ∈ A := by
          simpa [stoppedValue] using hA
        have hm_idx : (hittingAfter X (insert z A) 0 ω).untopA = m := by
          rw [← hm, WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        simpa [hm_idx] using hmem
      have hτA_le : hittingAfter X A 0 ω ≤ m := by
        exact
          hittingAfter_le_of_mem (u := X) (s := A) (n := 0) (ω := ω)
            (Nat.zero_le m) hm_memA
      have hm_le_n' : (m : ℕ∞) ≤ (n : ℕ∞) := by
        exact hτ_insert_le
      have hτA_le_n : hittingAfter X A 0 ω ≤ (n : ℕ∞) := by
        exact le_trans hτA_le hm_le_n'
      exact (not_lt_of_ge hτA_le_n) hpre
    rcases hinsert_mem with hEq | hA
    · exact ⟨hτ_insert_lt, by simpa [hEq]⟩
    · exact False.elim (hnotA hA)

include p in
/-- Helper for Theorem 19.6: a positive atom of the deterministic truncation law already lies in
the first-hit positivity set `S_A(x₀)`. -/
private theorem mem_S_A_of_truncatedStoppedValueEvent
    (n : ℕ) {z : E}
    (hz :
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = z}) :
    z ∈ S_A P X A x₀ := by
  rw [mem_S_A_iff, F_A, Measure.real_def]
  have hmono :
      (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = z}
        ≤
      (P x₀ : Measure Ω) (firstHitAtStateEvent X A z) := by
    exact measure_mono <|
      truncatedStoppedOnAValueEvent_subset_firstHitAtStateEvent
        (p := p) (X := X) (A := A) n z
  have hpos_event : 0 < (P x₀ : Measure Ω) (firstHitAtStateEvent X A z) :=
    lt_of_lt_of_le hz hmono
  exact ENNReal.toReal_pos hpos_event.ne' (measure_ne_top _ _)

include p in
/-- Helper for Theorem 19.6: every state in `S_A(x₀)` already carries positive singleton mass in
some deterministic-time law of the realized chain. -/
private theorem existsPosTimeStateMassOfMemSA
    {y : E} (hy : y ∈ S_A P X A x₀) :
    ∃ n : ℕ, 0 < ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E) := by
  obtain ⟨n, hn_pos⟩ :=
    existsPosMeasureExactFirstHitSliceOfMemSA
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) hy
  have htime_pos : 0 < (P x₀ : Measure Ω) {ω | X n ω = y} := by
    -- Proof comment: the exact first-hit slice is contained in the ordinary time-`n` singleton
    -- event, so its positive mass survives after forgetting the earlier path constraints.
    refine lt_of_lt_of_le hn_pos ?_
    exact measure_mono <|
      exactFirstHitSlice_subset_timeStateEq
        (p := p) (X := X) (A := A) n y
  refine ⟨n, ?_⟩
  -- Proof comment: identify the time-`n` singleton event with the singleton mass of the pushed
  -- forward law, then use the realization axiom for the `n`-step kernel row.
  calc
    0 < (P x₀ : Measure Ω) {ω | X n ω = y} := htime_pos
    _ = ((P x₀ : Measure Ω).map (X n)) ({y} : Set E) := by
          symm
          simpa using
            (Measure.map_apply
              ((inferInstance : IsMarkovProcessRealization
                (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process n)
              (measurableSet_singleton y))
    _ = ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E) := by
          exact congrArg (fun ν : Measure E ↦ ν ({y} : Set E))
            ((inferInstance : IsMarkovProcessRealization
              (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).transition_eq x₀ n)

include p P X in
/-- Helper for Theorem 19.6: a realized one-step transition matrix is stochastic. -/
private theorem stochasticMatrix_of_realization :
    IsStochasticMatrix p := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) :=
    hReal.semigroup.isMarkovKernel 1
  intro x
  -- Proof comment: the realized time-`1` kernel is Markov, so its row mass is `1`.
  calc
    ∑' y : E, p x y = discreteMatrixKernel p x Set.univ := by
      symm
      rw [discreteMatrixKernel_univ]
    _ = ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ := by
      simp
    _ = 1 := by
      simpa using
        (measure_univ :
          ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ = 1)

include p P X in
/-- Helper for Theorem 19.6: the realized chain is adapted to its natural filtration. -/
private theorem adapted_processFiltration
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X) :
    Adapted (processFiltration X) X := by
  intro n
  -- Proof comment: the time-`n` coordinate is one of the generators of `processFiltration X n`.
  have hX_meas : ∀ k : ℕ, Measurable (X k) := by
    intro k
    simpa using hReal.measurable_process k
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
    refine le_iSup_of_le n ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

include p P X in
/-- Helper for Theorem 19.6: the first entrance time `hittingAfter X A 0` is a stopping time for
the natural filtration of the realized chain. -/
private theorem hittingAfter_zero_isStoppingTime
    (A : Set E) :
    IsStoppingTime (processFiltration X) (hittingAfter X A 0) := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: hitting times of measurable sets are stopping times for the natural history.
  simpa using
    Adapted.isStoppingTime_hittingAfter
      (u := X) (s := A) (n := 0) (adapted_processFiltration (p := p) (P := P) (X := X) hReal)
      MeasurableSet.of_discrete

include p P X in
/-- Helper for Theorem 19.6: exact first-hit slices are measurable at the corresponding
deterministic time. -/
private theorem measurableSet_exactFirstHitSlice_processFiltration
    (n : ℕ) (y : E) :
    MeasurableSet[processFiltration X n]
      {ω | hittingAfter X (insert y A) 0 ω = n ∧
          stoppedValue X (hittingAfter X (insert y A) 0) ω = y} := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let τ : Ω → ℕ∞ := hittingAfter X (insert y A) 0
  have hτ_stop : IsStoppingTime (processFiltration X) τ := by
    -- Proof comment: hitting times of measurable sets are stopping times for adapted processes.
    simpa [τ] using
      Adapted.isStoppingTime_hittingAfter
        (u := X) (s := insert y A) (n := 0) (adapted_processFiltration (p := p) (P := P)
          (X := X) hReal) MeasurableSet.of_discrete
  have hτ_slice :
      MeasurableSet[processFiltration X n] {ω | τ ω = n} :=
    hτ_stop.measurableSet_eq n
  have hXn_meas :
      Measurable[processFiltration X n] (X n) :=
    adapted_processFiltration (p := p) (P := P) (X := X) hReal n
  have hstate :
      MeasurableSet[processFiltration X n] (X n ⁻¹' ({y} : Set E)) := by
    simpa using hXn_meas (MeasurableSet.singleton y)
  -- Proof comment: on the slice `{τ = n}`, the stopped value is exactly `X n`.
  have hslice_eq :
      {ω | hittingAfter X (insert y A) 0 ω = n ∧
          stoppedValue X (hittingAfter X (insert y A) 0) ω = y} =
        ({ω | τ ω = n} ∩ X n ⁻¹' ({y} : Set E)) := by
    ext ω
    constructor
    · intro hω
      refine ⟨hω.1, ?_⟩
      have hτ_untop : (τ ω).untopA = n := by
        simpa using congrArg WithTop.untopA hω.1
      simpa [τ, stoppedValue, hτ_untop] using hω.2
    · intro hω
      refine ⟨hω.1, ?_⟩
      have hXn : X n ω = y := by
        simpa using hω.2
      have hτ_untop : (τ ω).untopA = n := by
        simpa using congrArg WithTop.untopA hω.1
      simpa [τ, stoppedValue, hτ_untop] using hXn
  rw [hslice_eq]
  exact hτ_slice.inter hstate

/-- Helper for Theorem 19.6: if a time-`n` history event already forces the current state to be
`y`, then intersecting it with a deterministic future singleton event factors through the
corresponding step mass from `y`. -/
private theorem measure_inter_prefix_stepEvent_eq_mul
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: generated histories live inside the ambient measurable space.
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel p) ^ m) (X n ω)).real ({z} : Set E) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set E)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the deterministic-time Markov identity over `A`, then freeze the
  -- transition row because `A` already fixes the state at time `n`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, (((discreteMatrixKernel p) ^ m) (X n ω)).real ({z} : Set E) ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          rfl
    _ = (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

include p P X in
/-- Helper for Theorem 19.6: the deterministic-time prefix factorization is most convenient in
raw `Measure` form when positivity arguments stay in `ℝ≥0∞`. -/
private theorem measure_inter_prefix_stepEvent_eq_mul_ennreal
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)) * (P x : Measure Ω) A := by
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mul (p := p) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
    (inferInstance :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).semigroup.isMarkovKernel m
  have hright_ne_top :
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)) * (P x : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  -- Proof comment: both event masses are finite, so equality of their `toReal` values upgrades
  -- back to equality in `ℝ≥0∞`.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _]
      using hstep

include p P X in
/-- Helper for Theorem 19.6: restricting to a time-`n` history event and then pushing forward by
`X (n + 1)` agrees with first pushing forward by `X n` and then composing with the one-step
kernel. -/
private theorem restrictMap_succ_eq_discreteKernelComp_local
    (x : E) (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ((P x : Measure Ω).restrict s).map (X (n + 1)) =
      (discreteMatrixKernel p) ∘ₘ (((P x : Measure Ω).restrict s).map (X n)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hX_meas : ∀ k : ℕ, Measurable (X k) := hReal.measurable_process
  have hs_meas : MeasurableSet s := hs.1
  have hs_generated : MeasurableSet[generatedFiltrationSpace X n] s := hs.2
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hX_meas k).comap_le
  refine Measure.ext fun t ht ↦ ?_
  have hleft_real :
      ((((μ.restrict s).map (X (n + 1))).real) t) =
        ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
    let B : Set Ω := X (n + 1) ⁻¹' t
    have hB_meas : MeasurableSet B := by
      simpa [B] using (hX_meas (n + 1)) ht
    have hIndicatorInt : Integrable (Set.indicator B (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hB_meas
    have hmarkov :
        μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel p) (X n ω)).real t := by
      -- Proof comment: the Markov property converts the future singleton event into a one-step
      -- transition mass from the current state.
      simpa [B, add_comm] using hReal.markov_property x (A := t) ht n 1
    have hmass :
        μ.real (s ∩ B) =
          ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
      calc
        μ.real (s ∩ B)
            = ∫ ω in s, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hs_generated,
                  ← MeasureTheory.integral_indicator hs_meas]
                simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                  Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hs_meas.inter hB_meas)).symm
        _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    calc
      ((((μ.restrict s).map (X (n + 1))).real) t)
          = (μ.restrict s).real ((X (n + 1)) ⁻¹' t) := by
              simpa using MeasureTheory.map_measureReal_apply
                (μ := μ.restrict s) (f := X (n + 1)) (hX_meas (n + 1)) ht
      _ = μ.real (((X (n + 1)) ⁻¹' t) ∩ s) := by
            simpa [B] using
              (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := s) (t := B) hB_meas)
      _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
            simpa [B, Set.inter_comm] using hmass
  have hright_real :
      ((((discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n)))).real) t) =
        ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
    let ν : Measure E := ((μ.restrict s).map (X n))
    have hkernel_int :
        Integrable (fun y : E ↦ ((discreteMatrixKernel p) y).real t) ν := by
      simpa [ν] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := ν) (κ := discreteMatrixKernel p) ht)
    have hkernel_nonneg :
        0 ≤ᵐ[ν] fun y : E ↦ ((discreteMatrixKernel p) y).real t :=
      Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
    have hcomp_real :
        ((((discreteMatrixKernel p) ∘ₘ ν).real) t) =
          ∫ y, ((discreteMatrixKernel p) y).real t ∂ν := by
      rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply ht
        (ProbabilityTheory.Kernel.aemeasurable _)]
      have hlintegral :
          ∫⁻ y, ((discreteMatrixKernel p) y) t ∂ν =
            ENNReal.ofReal (∫ y, ((discreteMatrixKernel p) y).real t ∂ν) := by
        calc
          ∫⁻ y, ((discreteMatrixKernel p) y) t ∂ν
              = ∫⁻ y, ENNReal.ofReal (((discreteMatrixKernel p) y).real t) ∂ν := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with y
                  rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                  exact measure_ne_top _ _
          _ = ENNReal.ofReal (∫ y, ((discreteMatrixKernel p) y).real t ∂ν) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  hkernel_int hkernel_nonneg
      rw [hlintegral, ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae hkernel_nonneg
    have hmap_real :
        ∫ y, ((discreteMatrixKernel p) y).real t ∂ν =
          ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
      -- Proof comment: push the kernel mass function back through the restricted current law.
      change ∫ y, ((discreteMatrixKernel p) y).real t ∂((μ.restrict s).map (X n)) =
        ∫ ω, ((discreteMatrixKernel p) (X n ω)).real t ∂(μ.restrict s)
      rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
        hkernel_int.aestronglyMeasurable]
    calc
      ((((discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n)))).real) t)
          = ∫ y, ((discreteMatrixKernel p) y).real t ∂ν := by
              simpa [ν] using hcomp_real
      _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real t ∂μ := by
            simpa [ν] using hmap_real
  have hleft_ne_top : (((μ.restrict s).map (X (n + 1))) t) ≠ ∞ := by
    finiteness
  have hright_ne_top :
      (((discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n)))) t) ≠ ∞ := by
    finiteness
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict s).map (X (n + 1))))
      (ν := (discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n))))
      (s := t) (t := t) hleft_ne_top hright_ne_top).mp
      (hleft_real.trans hright_real.symm)

include p P X in
/-- Helper for Theorem 19.6: a positive one-step transition from a state in `S_A(x₀)` that still
lies outside `A` stays inside `S_A(x₀)`. -/
private theorem mem_S_A_of_mem_S_A_of_positiveTransition
    {z w : E} (hzA : z ∉ A) (hzS : z ∈ S_A P X A x₀)
    (hzw : 0 < (discreteMatrixKernel p) z ({w} : Set E)) :
    w ∈ S_A P X A x₀ := by
  obtain ⟨n, hn_pos⟩ :=
    existsPosMeasureExactFirstHitSliceOfMemSA
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) hzS
  let slice : Set Ω :=
    {ω | hittingAfter X (insert z A) 0 ω = n ∧
        stoppedValue X (hittingAfter X (insert z A) 0) ω = z}
  have hslice_meas :
      MeasurableSet[generatedFiltrationSpace X n] slice := by
    -- Proof comment: the exact first-hit slice is already measurable at deterministic time `n`.
    have hslice_proc :
        MeasurableSet[processFiltration X n] slice := by
      simpa [slice] using
        measurableSet_exactFirstHitSlice_processFiltration
          (p := p) (P := P) (X := X) (A := A) n z
    exact (show processFiltration X n ≤ generatedFiltrationSpace X n from inf_le_right) slice hslice_proc
  have hslice_sub : slice ⊆ {ω | X n ω = z} := by
    -- Proof comment: on the exact slice, the stopped value at time `n` is the raw time-`n`
    -- coordinate.
    simpa [slice] using
      exactFirstHitSlice_subset_timeStateEq
        (p := p) (X := X) (A := A) n z
  have hstep :
      (P x₀ : Measure Ω) (slice ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel p z ({w} : Set E)) * (P x₀ : Measure Ω) slice := by
    simpa [slice] using
      measure_inter_prefix_stepEvent_eq_mul_ennreal
        (p := p) (P := P) (X := X) (x := x₀) (y := z) (z := w) (A := slice) (n := n) (m := 1)
        hslice_meas hslice_sub
  have hstep_pos :
      0 < (P x₀ : Measure Ω) (slice ∩ {ω | X (n + 1) ω = w}) := by
    rw [hstep]
    exact ENNReal.mul_pos hzw.ne' (ne_of_gt hn_pos)
  have htrunc_pos :
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = w} := by
    refine lt_of_lt_of_le hstep_pos ?_
    exact measure_mono <|
      exactFirstHitSlice_stepEvent_subset_truncatedStoppedValueSucc
        (p := p) (X := X) (A := A) hzA
  exact
    mem_S_A_of_truncatedStoppedValueEvent
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) (n + 1) htrunc_pos

include p in
/-- Helper for Theorem 19.6: a positive atom of the pre-hit current-state law already lies outside
`A` and gives a positive atom of the deterministically truncated stopped chain. -/
private theorem preHitStateAtom_yieldsTruncAtom
    (n : ℕ) {y : E}
    (hy :
      0 <
        (P x₀ : Measure Ω)
          ({ω | (n : ℕ∞) < hittingAfter X A 0 ω} ∩ {ω | X n ω = y})) :
    y ∉ A ∧
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} := by
  let μ : Measure Ω := (P x₀ : Measure Ω)
  let pre : Set Ω := {ω | (n : ℕ∞) < hittingAfter X A 0 ω}
  have hyA : y ∉ A := by
    -- Proof comment: on the pre-hit slice the time-`n` state is still outside `A`, so a positive
    -- atom at `y` rules out `y ∈ A`.
    intro hyA
    have hsubset_empty : pre ∩ {ω | X n ω = y} ⊆ (∅ : Set Ω) := by
      intro ω hω
      have hpreω : (n : ℕ∞) < hittingAfter X A 0 ω := by
        simpa [pre] using hω.1
      have hnotA :
          X n ω ∉ A :=
        notMem_of_lt_hittingAfter (u := X) (s := A) (n := 0) (ω := ω) (k := n) hpreω (by simp)
      have hXn : X n ω = y := by
        simpa using hω.2
      exact False.elim (hnotA (hXn ▸ hyA))
    have hzero : μ (pre ∩ {ω | X n ω = y}) = 0 := by
      refine le_antisymm ?_ bot_le
      have hmono : μ (pre ∩ {ω | X n ω = y}) ≤ μ ∅ := measure_mono hsubset_empty
      simpa using hmono
    exact (not_lt_of_ge (by simpa [μ, pre] using hzero)) hy
  have hsubset :
      pre ∩ {ω | X n ω = y} ⊆
        {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} := by
    intro ω hω
    have hEq :
        truncatedStoppedValueOnA (X := X) (A := A) n ω = X n ω :=
      truncatedStoppedValueOnA_eq_time_on_preHit
        (p := p) (X := X) (A := A) n hω.1
    have hXn : X n ω = y := by
      simpa using hω.2
    simpa [hEq] using hXn
  refine ⟨hyA, ?_⟩
  exact lt_of_lt_of_le hy (measure_mono hsubset)

include p P X in
/-- Helper for Theorem 19.6: if every positive one-step successor of `y` has value at most
`f y`, then any successor reached with positive transition mass must actually have value `f y`. -/
private theorem valueEq_of_positiveTransition_fromLocalMaximum
    {y w : E}
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hyA : y ∉ A)
    (hymax : ∀ ⦃t : E⦄, 0 < (discreteMatrixKernel p) y ({t} : Set E) → f t ≤ f y)
    (hyw : 0 < (discreteMatrixKernel p) y ({w} : Set E)) :
    f w = f y := by
  let hp : IsStochasticMatrix p :=
    stochasticMatrix_of_realization (p := p) (P := P) (X := X)
  letI : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp
  rcases hf hyA with ⟨hfInt, hharmonic⟩
  let g : E → ℝ := fun z ↦ f y - f z
  have hconstInt : Integrable (fun _ : E ↦ f y) (discreteMatrixKernel p y) :=
    integrable_const (f y)
  have hgInt : Integrable g (discreteMatrixKernel p y) := by
    -- Proof comment: the gap function `g = f y - f` is integrable because both summands are.
    simpa [g] using hconstInt.sub hfInt
  have hgNormSummable : Summable (fun z : E ↦ (p y z).toReal * ‖g z‖) := by
    -- Proof comment: on a discrete row measure, integrability is exactly absolute summability of
    -- the weighted singleton values.
    simpa [g, discreteMatrixKernel_apply] using hgInt.summable_of_dirac
  have hgSummable : Summable (fun z : E ↦ (p y z).toReal * g z) := by
    have hnorm : Summable (fun z : E ↦ ‖(p y z).toReal * g z‖) := by
      simpa [Real.norm_eq_abs, g, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
        hgNormSummable
    exact hnorm.of_norm
  have hgap_tsum : ∑' z : E, (p y z).toReal * g z = 0 := by
    have hgap_int : ∫ z, g z ∂discreteMatrixKernel p y = 0 := by
      have hconst :
          ∫ z, (fun _ : E ↦ f y) z ∂discreteMatrixKernel p y = f y := by
        calc
          ∫ z, (fun _ : E ↦ f y) z ∂discreteMatrixKernel p y
              = ((discreteMatrixKernel p y).real Set.univ) * f y := by
                  simp [smul_eq_mul]
          _ = (((discreteMatrixKernel p) y) Set.univ).toReal * f y := by
                simp [MeasureTheory.Measure.real_def]
          _ = f y := by
                rw [measure_univ, ENNReal.toReal_one]
                ring
      -- Proof comment: harmonicity at `y` makes the average gap `f y - f z` vanish.
      calc
        ∫ z, g z ∂discreteMatrixKernel p y
            = ∫ z, ((fun _ : E ↦ f y) z - f z) ∂discreteMatrixKernel p y := by
                rfl
        _ = (∫ z, (fun _ : E ↦ f y) z ∂discreteMatrixKernel p y) -
              ∫ z, f z ∂discreteMatrixKernel p y := by
                rw [integral_sub hconstInt hfInt]
        _ = f y - f y := by
              rw [hconst, hharmonic]
        _ = 0 := by ring
    rw [integral_discreteMatrixKernel_eq_tsum p hp g y hgNormSummable] at hgap_int
    simpa [g] using hgap_int
  have hterm_nonneg : ∀ z : E, 0 ≤ (p y z).toReal * g z := by
    intro z
    by_cases hz : 0 < (discreteMatrixKernel p) y ({z} : Set E)
    · -- Proof comment: on positive singleton atoms, the local-maximum hypothesis bounds `f z`
      -- above by `f y`, so the weighted gap is nonnegative.
      exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hymax hz))
    · -- Proof comment: if the singleton mass is zero, the corresponding weighted term vanishes.
      have hpz_zero : p y z = 0 := by
        have hzero : (discreteMatrixKernel p) y ({z} : Set E) = 0 := by
          exact le_antisymm (le_of_not_gt hz) bot_le
        rw [discreteMatrixKernel_apply_singleton] at hzero
        exact hzero
      simp [g, hpz_zero]
  have hy_not_lt : ¬ f w < f y := by
    intro hlt
    have hpyw_pos : 0 < (p y w).toReal := by
      have hrow_pos : 0 < (((discreteMatrixKernel p) y) ({w} : Set E)).toReal := by
        exact ENNReal.toReal_pos hyw.ne' (measure_ne_top _ _)
      rw [discreteMatrixKernel_apply_singleton] at hrow_pos
      exact hrow_pos
    have hterm_pos : 0 < (p y w).toReal * g w := by
      -- Proof comment: a strict drop at a positive atom would create a strictly positive gap term.
      exact mul_pos hpyw_pos (sub_pos.mpr hlt)
    have hterm_le :
        (p y w).toReal * g w ≤ ∑' z : E, (p y z).toReal * g z := by
      simpa using hgSummable.sum_le_tsum ({w} : Finset E) (fun z _ ↦ hterm_nonneg z)
    have hsum_pos : 0 < ∑' z : E, (p y z).toReal * g z :=
      lt_of_lt_of_le hterm_pos hterm_le
    rw [hgap_tsum] at hsum_pos
    exact lt_irrefl _ hsum_pos
  exact le_antisymm (hymax hyw) (not_lt.mp hy_not_lt)

include p in
/-- Helper for Theorem 19.6: the singleton mass of the pre-hit current law at time `n` is exactly
the pre-hit current-state event mass. -/
private theorem preHitCurrentLaw_apply_singleton
    (n : ℕ) (x₀ y : E) :
    (((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))
        ({y} : Set E) =
      (P x₀ : Measure Ω)
        ({ω | (n : ℕ∞) < hittingAfter X A 0 ω} ∩ {ω | X n ω = y}) := by
  let pre : Set Ω := {ω | (n : ℕ∞) < hittingAfter X A 0 ω}
  have hpre_meas : MeasurableSet pre := by
    -- Proof comment: the pre-hit slice is a stopping-time event, hence measurable.
    exact (hittingAfter_zero_isStoppingTime (p := p) (P := P) (X := X) A).measurableSet_gt n |>.1
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: expand the pushforward of the restricted law and rewrite the preimage of the
  -- singleton `{y}` as the current-state event `{X n = y}`.
  rw [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
  simpa [pre, Set.inter_comm] using
    (Measure.restrict_apply
      (μ := (P x₀ : Measure Ω))
      (s := pre)
      (t := X n ⁻¹' ({y} : Set E))
      ((hReal.measurable_process n) (measurableSet_singleton y)))

include p P X in
/-- Helper for Theorem 19.6: a support point of the restricted pre-hit current law already lies
outside `A`, belongs to `S_A(x₀)`, and has value `f x₀`. -/
private theorem preHitCurrentLawSupportPointData
    [TopologicalSpace E] [DiscreteTopology E] [BorelSpace E]
    {n : ℕ} (ih :
      ∀ ⦃y : E⦄,
        0 <
          (P x₀ : Measure Ω)
            {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} →
        f y = f x₀)
    {y : E}
    (hySupport :
      y ∈
        ((((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))).support) :
    y ∉ A ∧ y ∈ S_A P X A x₀ ∧ f y = f x₀ := by
  let ν : Measure E :=
    (((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))
  have hy_singleton_pos : 0 < ν ({y} : Set E) := by
    have hy_support_forall := (Measure.mem_support_iff_forall y).mp hySupport
    have hy_singleton_nhds : ({y} : Set E) ∈ nhds y := by
      simp
    -- Proof comment: in the discrete topology, the singleton `{y}` is an open neighborhood, so a
    -- support point must assign it positive mass.
    exact hy_support_forall ({y} : Set E) hy_singleton_nhds
  have hy_pre_atom :
      0 <
        (P x₀ : Measure Ω)
          ({ω | (n : ℕ∞) < hittingAfter X A 0 ω} ∩ {ω | X n ω = y}) := by
    have hy_singleton_pos' := hy_singleton_pos
    rw [preHitCurrentLaw_apply_singleton (p := p) (P := P) (X := X) (A := A) n x₀ y] at hy_singleton_pos'
    exact hy_singleton_pos'
  obtain ⟨hyA, hy_trunc_atom⟩ :=
    preHitStateAtom_yieldsTruncAtom (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) n hy_pre_atom
  have hyS :
      y ∈ S_A P X A x₀ :=
    mem_S_A_of_truncatedStoppedValueEvent
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) n hy_trunc_atom
  -- Proof comment: the induction hypothesis now upgrades the positive truncation atom to the
  -- maximal-value identity `f y = f x₀`.
  exact ⟨hyA, hyS, ih hy_trunc_atom⟩

include p P X in
/-- Helper for Theorem 19.6: once a pre-hit current state `y` already has value `f x₀`, its
whole one-step row is almost surely supported on the level set `{f = f x₀}`. -/
private theorem kernelRowAeEqFx0OfStateData
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀))
    {y : E}
    (hyA : y ∉ A) (hyS : y ∈ S_A P X A x₀) (hfy : f y = f x₀) :
    ∀ᵐ w ∂(discreteMatrixKernel p y), f w = f x₀ := by
  let hp : IsStochasticMatrix p :=
    stochasticMatrix_of_realization (p := p) (P := P) (X := X)
  let q : PMF E := ⟨fun t : E ↦ p y t, ENNReal.summable.hasSum_iff.2 (hp y)⟩
  have hrow_eq : discreteMatrixKernel p y = q.toMeasure := by
    -- Proof comment: package the discrete row as a PMF once, then do all support reasoning on the
    -- PMF side.
    ext s hs
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ hs]
    change ∑' i : E, (p y i • Measure.dirac i) s = q.toMeasure s
    calc
      ∑' i : E, (p y i • Measure.dirac i) s
          = ∑' i : E, s.indicator (fun t : E ↦ p y t) i := by
              refine tsum_congr fun i ↦ ?_
              by_cases hi : i ∈ s <;> simp [Measure.smul_apply, hi]
      _ = q.toMeasure s := by
          simpa [q] using (q.toMeasure_apply hs).symm
  have hbad_support_empty : ({w : E | f w ≠ f x₀} ∩ q.support) = ∅ := by
    ext t
    constructor
    · intro ht
      have hyt_pos : 0 < (discreteMatrixKernel p) y ({t} : Set E) := by
        have hqt_pos : 0 < q t := (q.apply_pos_iff t).2 ht.2
        have hqtm_pos : 0 < q.toMeasure ({t} : Set E) := by
          rw [q.toMeasure_apply_singleton t (measurableSet_singleton t)]
          exact hqt_pos
        simpa [hrow_eq] using hqtm_pos
      have hlocal_max : ∀ ⦃u : E⦄, 0 < (discreteMatrixKernel p) y ({u} : Set E) → f u ≤ f y := by
        intro u hu
        have huS :
            u ∈ S_A P X A x₀ :=
          mem_S_A_of_mem_S_A_of_positiveTransition
            (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) hyA hyS hu
        have hu_le : f u ≤ f x₀ := hmax.2 ⟨u, huS, rfl⟩
        simpa [hfy] using hu_le
      have hft_eq_fy : f t = f y :=
        valueEq_of_positiveTransition_fromLocalMaximum
          (p := p) (P := P) (X := X) (A := A) (f := f) hf hyA hlocal_max hyt_pos
      have hft_eq_fx0 : f t = f x₀ := hft_eq_fy.trans hfy
      exact False.elim (ht.1 hft_eq_fx0)
    · simp
  rw [ae_iff]
  calc
    (discreteMatrixKernel p y) {w : E | ¬ f w = f x₀}
        = q.toMeasure {w : E | f w ≠ f x₀} := by
            simpa [hrow_eq]
    _ = q.toMeasure ({w : E | f w ≠ f x₀} ∩ q.support) := by
          symm
          exact q.toMeasure_apply_inter_support MeasurableSet.of_discrete
    _ = 0 := by simp [hbad_support_empty]

include p P X in
/-- Helper for Theorem 19.6: a positive atom of the restricted pre-hit current law already gives
the one-step almost-sure level-set identity at that state. -/
private theorem kernelRowAeEqFx0_of_positivePreHitCurrentAtom
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀))
    {n : ℕ}
    (ih :
      ∀ ⦃y : E⦄,
        0 <
          (P x₀ : Measure Ω)
            {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} →
        f y = f x₀)
    {y : E}
    (hy :
      0 <
        ((((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n)))
          ({y} : Set E)) :
    ∀ᵐ w ∂(discreteMatrixKernel p y), f w = f x₀ := by
  have hy_pre_atom :
      0 <
        (P x₀ : Measure Ω)
          ({ω | (n : ℕ∞) < hittingAfter X A 0 ω} ∩ {ω | X n ω = y}) := by
    -- Proof comment: rewrite the singleton atom of the pushed-forward current law back to the
    -- corresponding path event at time `n`.
    rw [preHitCurrentLaw_apply_singleton (p := p) (P := P) (X := X) (A := A) n x₀ y] at hy
    exact hy
  obtain ⟨hyA, hy_trunc_atom⟩ :=
    preHitStateAtom_yieldsTruncAtom
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) n hy_pre_atom
  have hyS :
      y ∈ S_A P X A x₀ :=
    mem_S_A_of_truncatedStoppedValueEvent
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) n hy_trunc_atom
  have hfy : f y = f x₀ := ih hy_trunc_atom
  -- Proof comment: the positive pre-hit atom now supplies exactly the state data needed by the
  -- one-step row lemma.
  exact
    kernelRowAeEqFx0OfStateData
      (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hmax hyA hyS hfy

/-- Helper for Theorem 19.6: positive singleton masses compose across powers of a kernel. -/
private theorem positiveSingletonComp
    {κ : Kernel E E} {m n : ℕ} {x y z : E}
    (hxy : 0 < (κ ^ m) x ({y} : Set E))
    (hyz : 0 < (κ ^ n) y ({z} : Set E)) :
    0 < (κ ^ (m + n)) x ({z} : Set E) := by
  -- Proof comment: the Chapman-Kolmogorov integral contains the positive contribution coming from
  -- the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton :
      0 < ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

include p in
/-- Helper for Theorem 19.6: if every singleton in `A` has zero `n`-step mass from `x`, then the
whole `n`-step law of `A` vanishes. -/
private theorem kernelPow_apply_eq_zero_of_singleton_zero
    (n : ℕ) (x : E) {A : Set E}
    (hA : ∀ y ∈ A, ((discreteMatrixKernel p ^ n) x) ({y} : Set E) = 0) :
    ((discreteMatrixKernel p ^ n) x) A = 0 := by
  induction n generalizing x with
  | zero =>
      by_cases hxA : x ∈ A
      · have hx_zero : ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) = 0 := hA x hxA
        have hx_one : ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) = 1 := by
          change (Measure.dirac x) ({x} : Set E) = 1
          rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
          simp
        exact False.elim (zero_ne_one (hx_zero.symm.trans hx_one))
      · -- Proof comment: at time `0` the law is the Dirac mass at `x`, so avoiding `x` already
        -- forces the whole set mass to vanish.
        change (Measure.dirac x) A = 0
        rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp [hxA]
  | succ n ih =>
      rw [show n + 1 = 1 + n by simp [Nat.add_comm]]
      rw [Kernel.pow_add_apply_eq_lintegral (discreteMatrixKernel p) 1 n x
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [pow_one, discreteMatrixKernel_apply, lintegral_sum_measure]
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro y
      rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      by_cases hxy : p x y = 0
      · simp [hxy]
      · have hyA :
            ∀ z ∈ A, ((discreteMatrixKernel p ^ n) y) ({z} : Set E) = 0 := by
          intro z hzA
          by_contra hzy
          have hxy_pos : 0 < ((discreteMatrixKernel p ^ 1) x) ({y} : Set E) := by
            refine bot_lt_iff_ne_bot.mpr ?_
            rw [pow_one, discreteMatrixKernel_apply_singleton]
            exact hxy
          have hzy_pos : 0 < ((discreteMatrixKernel p ^ n) y) ({z} : Set E) :=
            bot_lt_iff_ne_bot.mpr hzy
          have hcomp :
              0 < ((discreteMatrixKernel p ^ (1 + n)) x) ({z} : Set E) :=
            positiveSingletonComp
              (κ := discreteMatrixKernel p) (m := 1) (n := n) hxy_pos hzy_pos
          have hz_zero :
              ((discreteMatrixKernel p ^ (Nat.succ n)) x) ({z} : Set E) = 0 :=
            hA z hzA
          exact hcomp.ne' (by simpa [Nat.add_comm] using hz_zero)
        have hy_zero : ((discreteMatrixKernel p ^ n) y) A = 0 :=
          ih y hyA
        -- Proof comment: any positive first step from `x` to `y` would transport positive
        -- `n`-step mass from `y` into `A`, so only rows with zero contribution remain.
        simp [hxy, hy_zero]

include p P X in
/-- Helper for Theorem 19.6: the restricted pre-hit current law is almost surely supported on
states whose one-step rows stay on the level set `{f = f x₀}`. -/
private theorem aeKernelRowEqFx0OfRestrictedPreHitCurrentLaw
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀))
    {n : ℕ}
    (ih :
      ∀ ⦃y : E⦄,
        0 <
          (P x₀ : Measure Ω)
            {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} →
        f y = f x₀) :
    ∀ᵐ y
        ∂((((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))),
      ∀ᵐ w ∂(discreteMatrixKernel p y), f w = f x₀ := by
  let μ : Measure Ω := (P x₀ : Measure Ω)
  let pre : Set Ω := {ω | (n : ℕ∞) < hittingAfter X A 0 ω}
  let ν : Measure E := ((μ.restrict pre).map (X n))
  let μn : Measure E := μ.map (X n)
  let support : Set E := {y : E | ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E) ≠ 0}
  let bad : Set E := {y : E | ¬ ∀ᵐ w ∂(discreteMatrixKernel p y), f w = f x₀}
  have hν_le : ν ≤ μn := by
    -- Proof comment: restricting the path law before pushing forward can only decrease the
    -- resulting current-state law.
    simpa [ν, μn, μ] using
      (Measure.map_mono_of_aemeasurable
        (f := X n)
        (μ := μ.restrict pre)
        (ν := μ)
        Measure.restrict_le_self
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).measurable_process n).aemeasurable)
  have hμn_eq :
      μn = ((discreteMatrixKernel p ^ n) x₀) := by
    simpa [μn, μ] using
      ((inferInstance : IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).transition_eq x₀ n)
  have hsupport_countable : support.Countable := by
    let row : Measure E := ((discreteMatrixKernel p ^ n) x₀)
    letI : IsMarkovKernel ((fun m : ℕ ↦ discreteMatrixKernel p ^ m) n) :=
      (inferInstance : IsMarkovProcessRealization
        (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X).semigroup.isMarkovKernel n
    have hiUnion_singletons : (⋃ y : E, ({y} : Set E)) = Set.univ := by
      ext y
      simp
    have hrow_ne_top_iUnion : row (⋃ y : E, ({y} : Set E)) ≠ ⊤ := by
      have hrow_univ : row Set.univ = 1 := by
        simpa [row] using
          ((inferInstance : IsMarkovKernel ((fun m : ℕ ↦ discreteMatrixKernel p ^ m) n))
            .isProbabilityMeasure x₀).measure_univ
      simpa [hiUnion_singletons, hrow_univ]
    have hcount :
        {y : E | 0 < row ({y} : Set E)}.Countable :=
      Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top row
        (As_mble := fun y : E ↦ MeasurableSet.singleton y)
        (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz)
        hrow_ne_top_iUnion
    refine hcount.mono ?_
    intro y hy
    dsimp [support, row] at hy ⊢
    exact bot_lt_iff_ne_bot.mpr hy
  have hsupport_compl_zero :
      ν (supportᶜ) = 0 := by
    have hrow_support_compl_zero :
        ((discreteMatrixKernel p ^ n) x₀) (supportᶜ) = 0 := by
      refine kernelPow_apply_eq_zero_of_singleton_zero (p := p) n x₀ ?_
      intro y hy
      simpa [support] using hy
    have hν_le_row :
        ν ≤ ((discreteMatrixKernel p ^ n) x₀) := by
      simpa [hμn_eq] using hν_le
    exact le_antisymm (by simpa [hrow_support_compl_zero] using hν_le_row supportᶜ) bot_le
  have hbad_support_zero :
      ν (bad ∩ support) = 0 := by
    have hcount : (bad ∩ support).Countable :=
      hsupport_countable.mono Set.inter_subset_right
    rw [MeasureTheory.measure_null_iff_singleton hcount]
    intro y hy
    by_cases hy_pos : 0 < ν ({y} : Set E)
    · have hyrow :
        ∀ᵐ w ∂(discreteMatrixKernel p y), f w = f x₀ :=
          kernelRowAeEqFx0_of_positivePreHitCurrentAtom
            (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hmax ih hy_pos
      exact False.elim (hy.1 hyrow)
    · exact le_antisymm (le_of_not_gt hy_pos) bot_le
  have hbad_off_support_zero :
      ν (bad ∩ supportᶜ) = 0 := by
    exact measure_mono_null Set.inter_subset_right hsupport_compl_zero
  rw [ae_iff]
  change ν bad = 0
  refine le_antisymm ?_ bot_le
  -- Proof comment: split the bad set into its part on the countable law support and the
  -- off-support remainder, both of which are null for `ν`.
  have hsplit : bad = (bad ∩ support) ∪ (bad ∩ supportᶜ) := by
    ext y
    by_cases hy : y ∈ support <;> simp [hy]
  have hbad_le :
      ν bad ≤ ν (bad ∩ support) + ν (bad ∩ supportᶜ) := by
    calc
      ν bad = ν ((bad ∩ support) ∪ (bad ∩ supportᶜ)) := congrArg ν hsplit
      _ ≤ ν (bad ∩ support) + ν (bad ∩ supportᶜ) := measure_union_le _ _
  exact le_trans hbad_le (by rw [hbad_support_zero, hbad_off_support_zero, zero_add])

include p P X in
/-- Helper for Theorem 19.6: the composed one-step law from the restricted pre-hit current slice
assigns zero mass to the bad set `{w | f w ≠ f x₀}`. -/
private theorem restrictedPreHitNextLaw_badSet_zero
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀))
    {n : ℕ}
    (ih :
    ∀ ⦃y : E⦄,
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} →
      f y = f x₀) :
    ((discreteMatrixKernel p) ∘ₘ
      (((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n)))
        ({w : E | f w ≠ f x₀}) = 0 := by
  let ν : Measure E :=
    (((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))
  let bad : Set E := {w : E | f w ≠ f x₀}
  have hbad_meas : MeasurableSet bad := MeasurableSet.of_discrete
  have hzero_row :
      ∀ᵐ y ∂ν, (discreteMatrixKernel p y) bad = 0 := by
    -- Proof comment: on almost every pre-hit current state, the whole one-step row already lives
    -- on the level set `{f = f x₀}`.
    filter_upwards
      [aeKernelRowEqFx0OfRestrictedPreHitCurrentLaw
        (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hmax ih] with y hy
    rw [ae_iff] at hy
    simpa [bad] using hy
  -- Proof comment: rewrite the composed law as the integral of row masses and collapse the
  -- integrand to zero almost everywhere.
  rw [Measure.bind_apply hbad_meas (Kernel.aemeasurable _)]
  calc
    ∫⁻ a, (discreteMatrixKernel p a) bad ∂ν = ∫⁻ a, 0 ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hzero_row] with a ha
      simpa [discreteMatrixKernel_apply] using ha
    _ = 0 := by simp

include p P X in
/-- Helper for Theorem 19.6: the one-step law from the pre-hit current slice is almost surely
supported on states with value `f x₀`. -/
private theorem ae_eq_fx0_of_restrictedPreHitNextLaw
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀))
    {n : ℕ}
    (ih :
      ∀ ⦃y : E⦄,
        0 <
          (P x₀ : Measure Ω)
            {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} →
        f y = f x₀) :
    ∀ᵐ w
        ∂((discreteMatrixKernel p) ∘ₘ
          (((P x₀ : Measure Ω).restrict {ω | (n : ℕ∞) < hittingAfter X A 0 ω}).map (X n))),
      f w = f x₀ := by
  -- Proof comment: `ae_iff` turns the desired almost-everywhere equality into the vanishing of
  -- the bad set `{w | f w ≠ f x₀}` for the composed next-law.
  rw [ae_iff]
  simpa using
    restrictedPreHitNextLaw_badSet_zero
      (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hmax ih

include p P X in
/-- Helper for Theorem 19.6: every positive atom of a deterministic truncation of the chain
stopped on `A` already has the maximal value `f x₀`. -/
private theorem eq_of_positiveAtom_truncatedStoppedValue
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hx₀ : x₀ ∉ A)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀)) :
    ∀ ⦃n : ℕ⦄ ⦃z : E⦄,
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = z} →
      f z = f x₀ := by
  intro n
  induction n with
  | zero =>
      intro z hz
      have hzero_event :
          {ω | truncatedStoppedValueOnA (X := X) (A := A) 0 ω = z} =
            X 0 ⁻¹' ({z} : Set E) := by
        ext ω
        change X (min (hittingAfter X A 0 ω) (0 : ℕ∞)).untopA ω = z ↔ X 0 ω = z
        have hmin : min (hittingAfter X A 0 ω) (0 : ℕ∞) = 0 := by
          exact min_eq_right bot_le
        have hidx : (min (hittingAfter X A 0 ω) (0 : ℕ∞)).untopA = 0 := by
          rw [hmin]
          rfl
        rw [hidx]
      have hpos_state : 0 < (P x₀ : Measure Ω) (X 0 ⁻¹' ({z} : Set E)) := by
        simpa [hzero_event] using hz
      have hpos_dirac : 0 < (Measure.dirac x₀) ({z} : Set E) := by
        calc
          0 < (P x₀ : Measure Ω) (X 0 ⁻¹' ({z} : Set E)) := hpos_state
          _ = ((P x₀ : Measure Ω).map (X 0)) ({z} : Set E) := by
                symm
                simpa using
                  (Measure.map_apply
                    ((inferInstance : IsMarkovProcessRealization
                      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
                    (measurableSet_singleton z))
          _ = (Measure.dirac x₀) ({z} : Set E) := by
                simpa using
                  congrArg (fun ν : Measure E ↦ ν ({z} : Set E))
                    ((inferInstance : IsMarkovProcessRealization
                      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).initial_eq x₀)
      have hz_eq : z = x₀ := by
        by_cases hzx : z = x₀
        · exact hzx
        · have hzero : (Measure.dirac x₀) ({z} : Set E) = 0 := by
            have hzx' : x₀ ≠ z := by
              exact fun hx => hzx hx.symm
            simp [hzx']
          exact False.elim ((not_lt_of_ge (by simpa [hzero])) hpos_dirac)
      simpa [hz_eq]
  | succ n ih =>
      intro z hz
      let μ : Measure Ω := (P x₀ : Measure Ω)
      let event : Set Ω :=
        {ω | truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = z}
      let post : Set Ω := {ω | hittingAfter X A 0 ω ≤ n}
      let pre : Set Ω := {ω | (n : ℕ∞) < hittingAfter X A 0 ω}
      have hτ_stop :
          IsStoppingTime (processFiltration X) (hittingAfter X A 0) :=
        hittingAfter_zero_isStoppingTime (p := p) (P := P) (X := X) A
      have hpost_meas : MeasurableSet post := by
        simpa [post] using hτ_stop.measurableSpace_le _ (hτ_stop.measurableSet_le' n)
      have hpre_fil : MeasurableSet[processFiltration X n] pre := by
        simpa [pre] using hτ_stop.measurableSet_gt n
      have hpre_meas : MeasurableSet pre := hpre_fil.1
      have hsplit :
          event = (event ∩ post) ∪ (event ∩ pre) := by
        ext ω
        constructor
        · intro hEvent
          by_cases hω : hittingAfter X A 0 ω ≤ n
          · exact Or.inl ⟨hEvent, by simpa [post] using hω⟩
          · exact Or.inr ⟨hEvent, by simpa [pre] using lt_of_not_ge hω⟩
        · intro hω
          rcases hω with hω | hω
          · exact hω.1
          · exact hω.1
      have hnot_both_zero :
          ¬ (μ (event ∩ post) = 0 ∧ μ (event ∩ pre) = 0) := by
        intro hzero
        have hzero_union : μ ((event ∩ post) ∪ (event ∩ pre)) = 0 := by
          refine le_antisymm ?_ bot_le
          calc
            μ ((event ∩ post) ∪ (event ∩ pre))
                ≤ μ (event ∩ post) + μ (event ∩ pre) := measure_union_le _ _
            _ = 0 := by rw [hzero.1, hzero.2, zero_add]
        have hzero_event : μ event = 0 := by
          rw [hsplit]
          exact hzero_union
        exact (not_lt_of_ge (by simpa [μ, event] using hzero_event)) hz
      have hbranch :
          0 < μ (event ∩ post) ∨ 0 < μ (event ∩ pre) := by
        by_cases hpost_pos : 0 < μ (event ∩ post)
        · exact Or.inl hpost_pos
        · by_cases hpre_pos : 0 < μ (event ∩ pre)
          · exact Or.inr hpre_pos
          · exfalso
            exact hnot_both_zero
              ⟨le_antisymm (le_of_not_gt hpost_pos) bot_le,
                le_antisymm (le_of_not_gt hpre_pos) bot_le⟩
      rcases hbranch with hpost_pos | hpre_pos
      · have hpost_subset :
            event ∩ post ⊆
              {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = z} := by
          intro ω hω
          have hEq :
              truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω =
                truncatedStoppedValueOnA (X := X) (A := A) n ω :=
            truncatedStoppedValueOnA_succ_eqOn_postHit
              (p := p) (X := X) (A := A) n hω.2
          have hEvent :
              truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = z := by
            simpa [event] using hω.1
          rw [hEq] at hEvent
          exact hEvent
        exact ih (z := z) <| lt_of_lt_of_le hpost_pos (measure_mono hpost_subset)
      · have hpre_subset :
            event ∩ pre ⊆ pre ∩ {ω | X (n + 1) ω = z} := by
          intro ω hω
          have hEq :
              truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = X (n + 1) ω :=
            truncatedStoppedValueOnA_succ_eq_time_on_preHit
              (X := X) (A := A) n hω.2
          have hEvent :
              truncatedStoppedValueOnA (X := X) (A := A) (n + 1) ω = z := by
            simpa [event] using hω.1
          refine ⟨hω.2, ?_⟩
          rw [hEq] at hEvent
          exact hEvent
        have hnext_state_pos : 0 < μ (pre ∩ {ω | X (n + 1) ω = z}) := by
          exact lt_of_lt_of_le hpre_pos (measure_mono hpre_subset)
        let ν : Measure E := ((μ.restrict pre).map (X (n + 1)))
        have hν_singleton :
            0 < ν ({z} : Set E) := by
          rw [Measure.map_apply
            ((inferInstance : IsMarkovProcessRealization
              (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).measurable_process (n + 1))
            (measurableSet_singleton z)]
          have hrestrict :
              (μ.restrict pre) (X (n + 1) ⁻¹' ({z} : Set E)) =
                μ (pre ∩ {ω | X (n + 1) ω = z}) := by
            rw [Measure.restrict_apply
              (μ := μ)
              (s := pre)
              (t := X (n + 1) ⁻¹' ({z} : Set E))
              (((inferInstance : IsMarkovProcessRealization
                (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).measurable_process (n + 1))
                (measurableSet_singleton z))]
            change μ ({ω | X (n + 1) ω = z} ∩ pre) =
              μ (pre ∩ {ω | X (n + 1) ω = z})
            rw [Set.inter_comm]
          rw [hrestrict]
          exact hnext_state_pos
        have hν_comp :
            ν =
              (discreteMatrixKernel p) ∘ₘ (((μ.restrict pre).map (X n))) := by
          simpa [ν, μ] using
            restrictMap_succ_eq_discreteKernelComp_local
              (P := P) (X := X) (p := p) x₀ n hpre_fil
        have hae :
            ∀ᵐ w ∂ν, f w = f x₀ := by
          rw [hν_comp]
          exact ae_eq_fx0_of_restrictedPreHitNextLaw
            (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hmax ih
        rw [ae_iff] at hae
        by_contra hne
        have hsingleton_mono :
            ν ({z} : Set E) ≤ ν {w : E | f w ≠ f x₀} := by
          refine measure_mono ?_
          intro w hw
          have hwz : w = z := by
            simpa using hw
          rw [hwz]
          exact hne
        have hν_zero : ν ({z} : Set E) = 0 := by
          exact le_antisymm (le_trans hsingleton_mono (by simpa using hae)) bot_le
        exact (not_lt_of_ge (by simpa [hν_zero])) hν_singleton

-- Proof sketch: from harmonicity on `Aᶜ`, the source promotes `f` to a fixed point of the
-- stopped-chain operator `p_A`; iterating that probability kernel expresses `f x₀` as an average
-- of the values of `f` on states in
-- `S_A x₀`. If `f x₀` is already the greatest value attained on `S_A x₀`, every state with
-- positive first-hit probability from `x₀` must share the same value.
/-- Theorem 19.6 (1): (i) if a function harmonic on `E \ A` attains the supremum of its values on
`S_A(x₀)` at some `x₀ ∉ A`, then it is constant on `S_A(x₀)`. -/
theorem harmonicOn_compl_eq_on_S_A_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hx₀ : x₀ ∉ A)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀)) :
    ∀ ⦃y : E⦄, y ∈ S_A P X A x₀ → f y = f x₀ := by
  intro y hy
  obtain ⟨n, hslice_pos⟩ :=
    existsPosMeasureExactFirstHitSliceOfMemSA
      (p := p) (P := P) (X := X) (A := A) (x₀ := x₀) hy
  have hy_atom :
      0 <
        (P x₀ : Measure Ω)
          {ω | truncatedStoppedValueOnA (X := X) (A := A) n ω = y} := by
    -- Proof comment: the exact first-hit slice survives as a positive atom of the stopped-on-`A`
    -- deterministic truncation.
    refine lt_of_lt_of_le hslice_pos ?_
    exact measure_mono <|
      exactFirstHitSlice_subset_truncatedStoppedValueEq
        (p := p) (X := X) (A := A) n y
  -- Proof comment: once the closing positive-atom lemma is available, the main theorem is the
  -- exact-slice front end followed by the stopped-on-`A` atom argument.
  exact eq_of_positiveAtom_truncatedStoppedValue
    (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hx₀ hmax hy_atom

-- Proof sketch: the positivity assumption on `F_A` says that every `y ∉ A` belongs to
-- `S_A x₀`. Apply part (i) at the point where `f` attains its global supremum; since the global
-- supremum also bounds `f` on `S_A x₀`, the local maximum principle forces equality on all of
-- `E \ A`.
/-- Theorem 19.6 (2): (ii) if `F_A(x,y) > 0` for all `x, y ∈ E \ A` and `f`, harmonic on
`E \ A`, attains its global supremum at some `x₀ ∉ A`, then `f` is constant on `E \ A`. -/
theorem harmonicOn_compl_eq_on_compl_of_F_A_pos_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hFA : ∀ ⦃x y : E⦄, x ∉ A → y ∉ A → 0 < F_A P X A x y)
    (hx₀ : x₀ ∉ A) (hmax : IsGreatest (Set.range f) (f x₀)) :
    ∀ ⦃y : E⦄, y ∉ A → f x₀ = f y := by
  intro y hy
  have hyS : y ∈ S_A P X A x₀ := by
    rw [mem_S_A_iff]
    exact hFA hx₀ hy
  have hmaxS : IsGreatest (f '' S_A P X A x₀) (f x₀) :=
    isGreatest_image_S_A_of_isGreatest_range
      (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hmax
  -- Proof comment: once `y` is known to lie in `S_A(x₀)`, part (i) applies directly.
  symm
  exact harmonicOn_compl_eq_on_S_A_of_isGreatest
    (p := p) (P := P) (X := X) (A := A) (f := f) (x₀ := x₀) hf hx₀ hmaxS hyS

end

end ProbabilityTheory
