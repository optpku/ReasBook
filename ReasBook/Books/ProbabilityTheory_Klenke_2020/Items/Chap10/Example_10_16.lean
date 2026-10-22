/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_3_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_15

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 10.16: the walk position `X n` is the partial sum of its increment process
`ω ↦ X (k + 1) ω - X k ω`. -/
lemma symmetricSimpleRandomWalk_position_eq_partialSum
    {X : ℕ → Ω → ℤ} (hX_zero : X 0 = 0) :
    ∀ n ω,
      random_walk_partial_sum (fun k ω' ↦ X (k + 1) ω' - X k ω') n ω = X n ω := by
  intro n ω
  induction n with
  | zero =>
      -- Proof comment: the length-`0` partial sum is empty, so it matches the prescribed start.
      simp [random_walk_partial_sum, hX_zero]
  | succ n ih =>
      -- Proof comment: split off the last increment and telescope to recover the next position.
      rw [random_walk_partial_sum, Finset.sum_range_succ]
      have hsum : ∑ x ∈ Finset.range n, (X (x + 1) ω - X x ω) = X n ω := by
        simpa [random_walk_partial_sum] using ih
      rw [hsum]
      omega

/-- Helper for Example 10.16: a nearest-neighbor path started at `0` that never hits the right
boundary `b > 0` stays strictly below `b` at every time. -/
lemma strictRightBoundary_of_hittingAfter_eq_top
    (x : ℕ → ℤ) {b : ℤ} (hx_zero : x 0 = 0)
    (hx_step : ∀ n, x (n + 1) - x n = (-1 : ℤ) ∨ x (n + 1) - x n = 1)
    (hb : 0 < b) (hτb : hittingAfter (fun k (_ : Unit) ↦ x k) ({b} : Set ℤ) 0 () = ⊤) :
    ∀ n, x n < b := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial position is `0`, hence strictly below the positive boundary.
      simpa [hx_zero] using hb
  | succ n ih =>
      -- Proof comment: the next step differs by `±1`; the no-hit hypothesis rules out landing
      -- exactly on `b`, so the successor still lies strictly below `b`.
      have hne : x (n + 1) ≠ b := by
        have htop := (hittingAfter_eq_top_iff).1 hτb
        exact fun hEq ↦ htop (n + 1) (by simp) (by simpa [Set.mem_singleton_iff, hEq])
      rcases hx_step n with hstep | hstep
      · have hEq : x (n + 1) = x n - 1 := by omega
        omega
      · have hle : x (n + 1) ≤ b := by omega
        exact lt_of_le_of_ne hle hne

/-- Helper for Example 10.16: a nearest-neighbor path started at `0` that never hits the left
boundary `a < 0` stays strictly above `a` at every time. -/
lemma strictLeftBoundary_of_hittingAfter_eq_top
    (x : ℕ → ℤ) {a : ℤ} (hx_zero : x 0 = 0)
    (hx_step : ∀ n, x (n + 1) - x n = (-1 : ℤ) ∨ x (n + 1) - x n = 1)
    (ha : a < 0) (hτa : hittingAfter (fun k (_ : Unit) ↦ x k) ({a} : Set ℤ) 0 () = ⊤) :
    ∀ n, a < x n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial position is `0`, hence strictly above the negative boundary.
      simpa [hx_zero] using ha
  | succ n ih =>
      -- Proof comment: the next step differs by `±1`; the no-hit hypothesis rules out landing
      -- exactly on `a`, so the successor stays strictly above `a`.
      have hne : x (n + 1) ≠ a := by
        have htop := (hittingAfter_eq_top_iff).1 hτa
        exact fun hEq ↦ htop (n + 1) (by simp) (by simpa [Set.mem_singleton_iff, hEq])
      rcases hx_step n with hstep | hstep
      · have hge : a ≤ x (n + 1) := by omega
        exact lt_of_le_of_ne hge hne.symm
      · have hEq : x (n + 1) = x n + 1 := by omega
        omega

/-- Helper for Example 10.16: if a nearest-neighbor path started at `0` has not yet hit the right
boundary `b` by time `n`, then its position at time `n` is still strictly below `b`. -/
lemma strictRightBoundary_before_hitting
    (x : ℕ → ℤ) {b : ℤ} (hx_zero : x 0 = 0)
    (hx_step : ∀ n, x (n + 1) - x n = (-1 : ℤ) ∨ x (n + 1) - x n = 1)
    (hb : 0 < b) :
    ∀ n : ℕ,
      ((n : ℕ∞) < hittingAfter (fun k (_ : Unit) ↦ x k) ({b} : Set ℤ) 0 ()) →
        x n < b := by
  intro n
  induction n with
  | zero =>
      intro _
      -- Proof comment: the initial position is `0`, so it is strictly below the positive boundary.
      simpa [hx_zero] using hb
  | succ n ih =>
      intro hlt
      -- Proof comment: the successor still has not hit `b`, so the step can be only `-1` or `+1`
      -- without landing exactly on the boundary.
      have hprev : ((n : ℕ∞) < hittingAfter (fun k (_ : Unit) ↦ x k) ({b} : Set ℤ) 0 ()) := by
        exact lt_of_le_of_lt (by exact_mod_cast Nat.le_succ n) hlt
      have hne : x (n + 1) ≠ b := by
        have hnot := notMem_of_lt_hittingAfter hlt (by simp)
        simpa [Set.mem_singleton_iff] using hnot
      have hxn : x n < b := ih hprev
      rcases hx_step n with hstep | hstep
      · have hEq : x (n + 1) = x n - 1 := by omega
        omega
      · have hle : x (n + 1) ≤ b := by omega
        exact lt_of_le_of_ne hle hne

/-- Helper for Example 10.16: if a nearest-neighbor path started at `0` has not yet hit the left
boundary `a` by time `n`, then its position at time `n` is still strictly above `a`. -/
lemma strictLeftBoundary_before_hitting
    (x : ℕ → ℤ) {a : ℤ} (hx_zero : x 0 = 0)
    (hx_step : ∀ n, x (n + 1) - x n = (-1 : ℤ) ∨ x (n + 1) - x n = 1)
    (ha : a < 0) :
    ∀ n : ℕ,
      ((n : ℕ∞) < hittingAfter (fun k (_ : Unit) ↦ x k) ({a} : Set ℤ) 0 ()) →
        a < x n := by
  intro n
  induction n with
  | zero =>
      intro _
      -- Proof comment: the initial position is `0`, so it is strictly above the negative boundary.
      simpa [hx_zero] using ha
  | succ n ih =>
      intro hlt
      -- Proof comment: the successor still has not hit `a`, so the `±1` step cannot land on `a`.
      have hprev : ((n : ℕ∞) < hittingAfter (fun k (_ : Unit) ↦ x k) ({a} : Set ℤ) 0 ()) := by
        exact lt_of_le_of_lt (by exact_mod_cast Nat.le_succ n) hlt
      have hne : x (n + 1) ≠ a := by
        have hnot := notMem_of_lt_hittingAfter hlt (by simp)
        simpa [Set.mem_singleton_iff] using hnot
      have hxn : a < x n := ih hprev
      rcases hx_step n with hstep | hstep
      · have hge : a ≤ x (n + 1) := by omega
        exact lt_of_le_of_ne hge hne.symm
      · have hEq : x (n + 1) = x n + 1 := by omega
        omega

/-- Helper for Example 10.16: casting the integer-valued partial-sum walk to `ℝ` agrees with the
real partial sums of the cast increment family. -/
lemma partialSum_intCast_eq_randomWalkProcess
    (Y : ℕ → Ω → ℤ) :
    ∀ n ω, partialSum (fun k ω' ↦ (Y k ω' : ℝ)) n ω = (randomWalkProcess Y n ω : ℝ) := by
  intro n ω
  -- Proof comment: both sides are the same finite sum; the right-hand side is just written in
  -- the integer walk notation before casting to `ℝ`.
  rw [partialSum_apply, randomWalkProcess_apply]
  exact_mod_cast rfl

/-- Helper for Example 10.16: a variable with the symmetric Rademacher law gives mass `1 / 2`
to both singleton atoms `{-1}` and `{1}`. -/
lemma hasLaw_symmetricRademacher_preimage_singletons
    (P : Measure Ω) (Y : Ω → ℤ) (hY : HasLaw Y symmetricRademacherLaw P) :
    P (Y ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ ∧
      P (Y ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
  constructor
  · -- Proof comment: rewrite the preimage mass through the pushforward law and evaluate the
    -- singleton `{-1}` under `symmetricRademacherLaw`.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (-1 : ℤ))]
    rw [hY.map_eq]
    simp [symmetricRademacherLaw, one_div]
  · -- Proof comment: the singleton `{1}` mass is the owner theorem for the symmetric
    -- Rademacher law, transported back through `HasLaw`.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (1 : ℤ))]
    rw [hY.map_eq]
    simpa [one_div] using symmetricRademacherLaw_apply_singleton_one

/-- Helper for Example 10.16: pathwise-equal walks have the same first hitting time after `0`. -/
lemma hittingAfter_zero_eq_of_forall_eq
    {β : Type*} {u v : ℕ → Ω → β} {s : Set β} {ω : Ω}
    (hω : ∀ n, u n ω = v n ω) :
    hittingAfter u s 0 ω = hittingAfter v s 0 ω := by
  -- Proof comment: the defining existential and the infimum set in `hittingAfter` depend only on
  -- the path values, so pointwise path equality identifies the two hitting times.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ u j ω ∈ s) ↔ ∃ j, 0 ≤ j ∧ v j ω ∈ s := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ u i ω ∈ s} = {i : ℕ | 0 ≤ i ∧ v i ω ∈ s} := by
    ext i
    simp [hω i]
  by_cases hu : ∃ j, 0 ≤ j ∧ u j ω ∈ s
  · have hv : ∃ j, 0 ≤ j ∧ v j ω ∈ s := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ v j ω ∈ s := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.16: hitting a real boundary with the real-cast walk is the same as
hitting the corresponding integer boundary with the original walk. -/
lemma hittingAfter_intCast_pair_eq
    {u : ℕ → Ω → ℤ} {ω : Ω} {a b : ℤ} :
    hittingAfter (fun n ω' ↦ (u n ω' : ℝ)) ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω =
      hittingAfter u ({a, b} : Set ℤ) 0 ω := by
  -- Proof comment: membership in the real two-point set is equivalent to membership in the
  -- integer two-point set because integer casts into `ℝ` are injective.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ (u j ω : ℝ) ∈ ({(a : ℝ), (b : ℝ)} : Set ℝ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, Int.cast_inj] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, Int.cast_inj] using hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ (u i ω : ℝ) ∈ ({(a : ℝ), (b : ℝ)} : Set ℝ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({a, b} : Set ℤ)} := by
    ext i
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, Int.cast_inj]
  by_cases hu : ∃ j, 0 ≤ j ∧ (u j ω : ℝ) ∈ ({(a : ℝ), (b : ℝ)} : Set ℝ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.16: the same cast normalization works for a singleton boundary. -/
lemma hittingAfter_intCast_singleton_eq
    {u : ℕ → Ω → ℤ} {ω : Ω} {a : ℤ} :
    hittingAfter (fun n ω' ↦ (u n ω' : ℝ)) ({(a : ℝ)} : Set ℝ) 0 ω =
      hittingAfter u ({a} : Set ℤ) 0 ω := by
  -- Proof comment: the real singleton `{a}` cuts out exactly the same hitting event as the
  -- integer singleton `{a}` after casting the walk values.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ (u j ω : ℝ) ∈ ({(a : ℝ)} : Set ℝ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_singleton_iff, Int.cast_inj] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_singleton_iff, Int.cast_inj] using hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ (u i ω : ℝ) ∈ ({(a : ℝ)} : Set ℝ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({a} : Set ℤ)} := by
    ext i
    simp [Set.mem_singleton_iff, Int.cast_inj]
  by_cases hu : ∃ j, 0 ≤ j ∧ (u j ω : ℝ) ∈ ({(a : ℝ)} : Set ℝ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Example 10.16: for a one-dimensional symmetric simple random walk starting at `0`, the
probability of hitting the negative level `a` before the positive level `b` is `b / (b - a)`. -/
theorem symmetricSimpleRandomWalk_prob_hitLeftBeforeRight
    (P : Measure Ω) (X : ℕ → Ω → ℤ)
    (hX_zero : X 0 = 0)
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
    (hX_law : ∀ n,
      HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)
    {a b : ℤ} (ha : a < 0) (hb : 0 < b) :
    P {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} =
      ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := by
  -- Route correction: the original plan tried to reuse
  -- `symmetricSimpleRandomWalk_squareIntegrable_martingale`, but its owner file currently fails to
  -- compile in this workspace because it builds `Filtration.natural` from only
  -- `AEStronglyMeasurable` data. The surviving pathwise helpers above already isolate the
  -- recurrence-to-hitting-time part, so the remaining proof should pivot to a measurable
  -- modification of the increment process and rebuild the martingale on that canonical walk.
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := randomWalkProcess Ym
  have hYm_eq : ∀ n, Δ n =ᵐ[P] Ym n := by
    intro n
    simpa [Δ, Ym] using (hX_law n).aemeasurable.ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    simpa [Ym] using (hX_law n).aemeasurable.measurable_mk
  have hYm_indep : iIndepFun Ym P := hX_indep.congr hYm_eq
  have hYm_law : ∀ n, HasLaw (Ym n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hYm_eq n).symm
  have hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω := by
    have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Ym n ω := by
      simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
    filter_upwards [h_all] with ω hω n
    calc
      W n ω = random_walk_partial_sum Ym n ω := by
        simpa [W] using randomWalkProcess_apply Ym n ω
      _ = random_walk_partial_sum Δ n ω := by
        unfold random_walk_partial_sum
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact (hω j).symm
      _ = X n ω := by
        simpa [Δ] using symmetricSimpleRandomWalk_position_eq_partialSum hX_zero n ω
  -- Proof comment: first extract the exact fair-sign singleton masses from the law of `Ym`; these
  -- are the inputs needed by Exercise 2.3.1 on the measurable increment family itself.
  have hYm_neg : ∀ n : ℕ, P ((Ym n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).1
  have hYm_pos : ∀ n : ℕ, P ((Ym n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).2
  have hYm_signs : ∀ᵐ ω ∂P, ∀ n, Ym n ω = (-1 : ℤ) ∨ Ym n ω = 1 := by
    exact ae_all_iff.2 fun n ↦
      ae_eq_negOne_or_eq_one_of_fairSigns P Ym hYm_meas hYm_neg hYm_pos n
  -- Proof comment: Exercise 2.3.1 forces the measurable walk to cross every right-hand level
  -- infinitely often, so the right hitting time cannot be `⊤`.
  have hτb_lt_top : ∀ᵐ ω ∂P, hittingAfter W ({b} : Set ℤ) 0 ω < ⊤ := by
    filter_upwards
      [ae_infinite_partial_sum_ge_of_independent_fair_signs
          P Ym hYm_meas hYm_indep hYm_neg hYm_pos,
        hYm_signs] with ω hωInf hωSigns
    have hne : hittingAfter W ({b} : Set ℤ) 0 ω ≠ ⊤ := by
      intro htop
      have hW_zero : W 0 ω = 0 := by
        simpa [W] using congrFun (randomWalkProcess_zero Ym) ω
      have hW_step :
          ∀ n, W (n + 1) ω - W n ω = (-1 : ℤ) ∨ W (n + 1) ω - W n ω = 1 := by
        intro n
        have hinc : W (n + 1) ω - W n ω = Ym n ω := by
          simpa [W] using randomWalkProcess_increment Ym n ω
        simpa [hinc] using hωSigns n
      have hstrict :=
        strictRightBoundary_of_hittingAfter_eq_top
          (fun n ↦ W n ω) hW_zero hW_step hb htop
      rcases (hωInf b).nonempty with ⟨n, hn⟩
      have hge : b ≤ W n ω := by
        simpa [W, random_walk_partial_sum, randomWalkProcess_apply] using hn
      exact not_lt_of_ge hge (hstrict n)
    simpa [lt_top_iff_ne_top] using hne
  -- Proof comment: applying the same recurrence statement to the reflected increment family `-Ym`
  -- gives the almost-sure finiteness of the left hitting time.
  have hNegYm_meas : ∀ n, Measurable (fun ω ↦ -Ym n ω) := by
    intro n
    exact measurable_neg.comp (hYm_meas n)
  have hNegYm_indep : iIndepFun (fun n ω ↦ -Ym n ω) P := by
    simpa using hYm_indep.comp (fun _ z ↦ (-z : ℤ)) (fun _ ↦ measurable_neg)
  have hNegYm_neg : ∀ n : ℕ, P ((fun ω ↦ -Ym n ω) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    have hset : (fun ω ↦ -Ym n ω) ⁻¹' {(-1 : ℤ)} = (Ym n) ⁻¹' {(1 : ℤ)} := by
      ext ω
      simp
    rw [hset]
    exact hYm_pos n
  have hNegYm_pos : ∀ n : ℕ, P ((fun ω ↦ -Ym n ω) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    have hset : (fun ω ↦ -Ym n ω) ⁻¹' {(1 : ℤ)} = (Ym n) ⁻¹' {(-1 : ℤ)} := by
      ext ω
      constructor <;> intro h <;> simp at h ⊢ <;> omega
    rw [hset]
    exact hYm_neg n
  have hτa_lt_top : ∀ᵐ ω ∂P, hittingAfter W ({a} : Set ℤ) 0 ω < ⊤ := by
    filter_upwards
      [ae_infinite_partial_sum_ge_of_independent_fair_signs
          P (fun n ω ↦ -Ym n ω) hNegYm_meas hNegYm_indep hNegYm_neg hNegYm_pos,
        hYm_signs] with ω hωInf hωSigns
    have hne : hittingAfter W ({a} : Set ℤ) 0 ω ≠ ⊤ := by
      intro htop
      have hW_zero : W 0 ω = 0 := by
        simpa [W] using congrFun (randomWalkProcess_zero Ym) ω
      have hW_step :
          ∀ n, W (n + 1) ω - W n ω = (-1 : ℤ) ∨ W (n + 1) ω - W n ω = 1 := by
        intro n
        have hinc : W (n + 1) ω - W n ω = Ym n ω := by
          simpa [W] using randomWalkProcess_increment Ym n ω
        simpa [hinc] using hωSigns n
      have hstrict :=
        strictLeftBoundary_of_hittingAfter_eq_top
          (fun n ↦ W n ω) hW_zero hW_step ha htop
      rcases (hωInf (-a)).nonempty with ⟨n, hn⟩
      have hle : W n ω ≤ a := by
        have hneg_ge : -a ≤ -W n ω := by
          simpa [W, random_walk_partial_sum, randomWalkProcess_apply, Finset.sum_neg_distrib] using hn
        omega
      exact not_le_of_gt (hstrict n) hle
    simpa [lt_top_iff_ne_top] using hne
  -- Proof comment: once the left boundary is hit at a finite time, the two-sided hitting time is
  -- bounded above by that same index and is therefore finite as well.
  have hτab_lt_top : ∀ᵐ ω ∂P, hittingAfter W ({a, b} : Set ℤ) 0 ω < ⊤ := by
    filter_upwards [hτa_lt_top] with ω hωa
    have hτa_ne : hittingAfter W ({a} : Set ℤ) 0 ω ≠ ⊤ := by
      exact ne_of_lt hωa
    let ia : ℕ := (hittingAfter W ({a} : Set ℤ) 0 ω).untop hτa_ne
    have hia : ia = (hittingAfter W ({a} : Set ℤ) 0 ω).untopA := by
      dsimp [ia]
      rw [WithTop.untopA_eq_untop hτa_ne]
    have hmem_a : W ia ω ∈ ({a} : Set ℤ) := by
      simpa [Set.mem_singleton_iff, hia] using hittingAfter_mem_set_of_ne_top hτa_ne
    have hmem_ab : W ia ω ∈ ({a, b} : Set ℤ) := by
      have hEq : W ia ω = a := by simpa [Set.mem_singleton_iff] using hmem_a
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, hEq]
    have hle_ab : hittingAfter W ({a, b} : Set ℤ) 0 ω ≤ ia := by
      exact hittingAfter_le_of_mem (by simp [ia]) hmem_ab
    exact lt_of_le_of_lt hle_ab (by simp [ia])
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Ym n ω : ℝ)
  let Wℝ : ℕ → Ω → ℝ := partialSum stepReal
  let hWℝ_strMeas :
      ∀ n, StronglyMeasurable (Wℝ n) :=
    fun n ↦ (partialSum_measurable stepReal
      (fun k ↦ measurable_stepReal Ym hYm_meas k) n).stronglyMeasurable
  let ℱW : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural Wℝ hWℝ_strMeas
  let τa : Ω → ℕ∞ := hittingAfter W ({a} : Set ℤ) 0
  let τab : Ω → ℕ∞ := hittingAfter W ({a, b} : Set ℤ) 0
  let A : Set Ω := {ω | τab ω = τa ω}
  -- Proof comment: cast the measurable integer walk to `ℝ`, identify it with the real partial-sum
  -- martingale from Example 10.6, and then work with bounded stopping-time truncations.
  have hstepReal_meas : ∀ n, Measurable (stepReal n) := by
    intro n
    simpa [stepReal] using measurable_stepReal Ym hYm_meas n
  have hstepReal_indep : iIndepFun stepReal P := by
    have hcast_meas : Measurable (fun z : ℤ ↦ (z : ℝ)) := measurable_of_countable _
    simpa [stepReal] using hYm_indep.comp (fun _ z ↦ (z : ℝ)) (fun _ ↦ hcast_meas)
  have hstepReal_int : ∀ n, Integrable (stepReal n) P := by
    intro n
    simpa [stepReal] using
      integrable_stepReal_of_fairSigns P Ym hYm_meas hYm_neg hYm_pos n
  have hstepReal_mean_zero : ∀ n, P[stepReal n] = 0 := by
    intro n
    simpa [stepReal] using
      integral_stepReal_eq_zero_of_fairSigns P Ym hYm_meas hYm_neg hYm_pos n
  have hWℝ_eq : ∀ n ω, Wℝ n ω = (W n ω : ℝ) := by
    intro n ω
    simpa [Wℝ, stepReal, W] using partialSum_intCast_eq_randomWalkProcess Ym n ω
  have hWℝ_martingale : Martingale Wℝ ℱW P := by
    simpa [Wℝ, ℱW, hWℝ_strMeas] using
      (independentCenteredPartialSums_martingale
        (Y := stepReal) (μ := P) (hY_meas := hstepReal_meas)
        hstepReal_int hstepReal_mean_zero hstepReal_indep)
  have hτa_eq :
      hittingAfter Wℝ ({(a : ℝ)} : Set ℝ) 0 = τa := by
    funext ω
    calc
      hittingAfter Wℝ ({(a : ℝ)} : Set ℝ) 0 ω =
          hittingAfter (fun n ω' ↦ (W n ω' : ℝ)) ({(a : ℝ)} : Set ℝ) 0 ω := by
            exact hittingAfter_zero_eq_of_forall_eq
              (u := Wℝ) (v := fun n ω' ↦ (W n ω' : ℝ))
              (s := ({(a : ℝ)} : Set ℝ)) (ω := ω) (fun n ↦ hWℝ_eq n ω)
      _ = τa ω := by
        simpa [τa] using hittingAfter_intCast_singleton_eq (u := W) (ω := ω) (a := a)
  have hτab_eq :
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 = τab := by
    funext ω
    calc
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω =
          hittingAfter (fun n ω' ↦ (W n ω' : ℝ))
            ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω := by
              exact hittingAfter_zero_eq_of_forall_eq
                (u := Wℝ) (v := fun n ω' ↦ (W n ω' : ℝ))
                (s := ({(a : ℝ), (b : ℝ)} : Set ℝ))
                (ω := ω) (fun n ↦ hWℝ_eq n ω)
      _ = τab ω := by
        simpa [τab] using hittingAfter_intCast_pair_eq (u := W) (ω := ω) (a := a) (b := b)
  -- Proof comment: the integer hitting times become stopping times once rewritten as real hitting
  -- times for the adapted martingale `Wℝ`.
  have hτa_stop : IsStoppingTime ℱW τa := by
    rw [← hτa_eq]
    simpa using
      Adapted.isStoppingTime_hittingAfter
        (u := Wℝ) (s := ({(a : ℝ)} : Set ℝ)) (n := 0)
        hWℝ_martingale.stronglyAdapted.adapted (measurableSet_singleton (a : ℝ))
  have hτab_stop : IsStoppingTime ℱW τab := by
    rw [← hτab_eq]
    simpa [Set.insert_comm] using
      Adapted.isStoppingTime_hittingAfter
        (u := Wℝ) (s := ({(a : ℝ), (b : ℝ)} : Set ℝ)) (n := 0)
        hWℝ_martingale.stronglyAdapted.adapted
        ((measurableSet_singleton (b : ℝ)).insert (a : ℝ))
  have hτab_ae_ne_top : ∀ᵐ ω ∂P, τab ω ≠ ⊤ := by
    simpa [τab, lt_top_iff_ne_top] using hτab_lt_top
  have hτab_le_τa : ∀ ω, τab ω ≤ τa ω := by
    intro ω
    by_cases hτa_top : τa ω = ⊤
    · simp [hτa_top]
    · let ia : ℕ := (τa ω).untop hτa_top
      have hia : ia = (τa ω).untopA := by
        dsimp [ia]
        rw [WithTop.untopA_eq_untop hτa_top]
      have hmem_a : W ia ω ∈ ({a} : Set ℤ) := by
        simpa [τa, Set.mem_singleton_iff, hia] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω) hτa_top)
      have hmem_ab : W ia ω ∈ ({a, b} : Set ℤ) := by
        have hEq : W ia ω = a := by
          simpa [Set.mem_singleton_iff] using hmem_a
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hEq]
      have hia_eq : ((ia : ℕ) : ℕ∞) = τa ω := by
        dsimp [ia]
        exact WithTop.coe_untop _ _
      exact le_trans
        (hittingAfter_le_of_mem
          (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω)
          (i := ia) (by simp [ia]) hmem_ab)
        hia_eq.le
  have hτab_le_τb : ∀ ω, τab ω ≤ hittingAfter W ({b} : Set ℤ) 0 ω := by
    intro ω
    by_cases hτb_top : hittingAfter W ({b} : Set ℤ) 0 ω = ⊤
    · rw [hτb_top]
      exact le_top
    · let ib : ℕ := (hittingAfter W ({b} : Set ℤ) 0 ω).untop hτb_top
      have hib : ib = (hittingAfter W ({b} : Set ℤ) 0 ω).untopA := by
        dsimp [ib]
        rw [WithTop.untopA_eq_untop hτb_top]
      have hmem_b : W ib ω ∈ ({b} : Set ℤ) := by
        simpa [Set.mem_singleton_iff, hib] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({b} : Set ℤ)) (n := 0) (ω := ω) hτb_top)
      have hmem_ab : W ib ω ∈ ({a, b} : Set ℤ) := by
        have hEq : W ib ω = b := by
          simpa [Set.mem_singleton_iff] using hmem_b
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hEq]
      have hib_eq : ((ib : ℕ) : ℕ∞) = hittingAfter W ({b} : Set ℤ) 0 ω := by
        dsimp [ib]
        exact WithTop.coe_untop _ _
      exact le_trans
        (hittingAfter_le_of_mem
          (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω)
          (i := ib) (by simp [ib]) hmem_ab)
        hib_eq.le
  let F : ℕ → Ω → ℝ := fun n ω ↦
    stoppedValue Wℝ (fun ω' ↦ min (τab ω') (n : ℕ∞)) ω
  have hF_int : ∀ n, Integrable (F n) P := by
    intro n
    exact integrable_stoppedValue ℕ (hτab_stop.min_const n)
      hWℝ_martingale.integrable fun ω ↦ min_le_right _ _
  have hF_expectation : ∀ n, ∫ ω, F n ω ∂P = 0 := by
    intro n
    have hEq :
        P[stoppedValue Wℝ (fun ω ↦ min (τab ω) (n : ℕ∞))] =
          P[stoppedValue Wℝ (fun _ ↦ (0 : ℕ∞))] :=
      martingale_expected_stoppedValue_eq_of_le_of_bounded
        (X := Wℝ) (μ := P) (ℱ := ℱW)
        hWℝ_martingale
        (isStoppingTime_const ℱW 0) (hτab_stop.min_const n)
        (fun ω ↦ by simp) (fun ω ↦ min_le_right _ _)
    calc
      ∫ ω, F n ω ∂P = ∫ ω, stoppedValue Wℝ (fun _ ↦ (0 : ℕ∞)) ω ∂P := by
        simpa [F] using hEq
      _ = 0 := by
        change ∫ ω, Wℝ 0 ω ∂P = 0
        simp [Wℝ, partialSum_apply]
  -- Proof comment: before hitting, the walk stays inside `(a, b)`; after hitting, the stopped
  -- value is exactly one of the two boundary points. This yields the uniform `L¹` dominator.
  have hF_bound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (b - a : ℝ) := by
    intro n
    filter_upwards [hYm_signs] with ω hωSigns
    have hW_zero : W 0 ω = 0 := by
      simpa [W] using congrFun (randomWalkProcess_zero Ym) ω
    have hW_step :
        ∀ k, W (k + 1) ω - W k ω = (-1 : ℤ) ∨ W (k + 1) ω - W k ω = 1 := by
      intro k
      have hinc : W (k + 1) ω - W k ω = Ym k ω := by
        simpa [W] using randomWalkProcess_increment Ym k ω
      simpa [hinc] using hωSigns k
    have hstopEq : F n ω = stoppedProcess Wℝ τab n ω := by
      simpa [F, min_comm] using
        (stoppedProcess_eq_stoppedValue_apply (u := Wℝ) (τ := τab) n ω).symm
    by_cases hτ : τab ω ≤ n
    · have hτ_ne : τab ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hτ
      have hmem : W (τab ω).untopA ω ∈ ({a, b} : Set ℤ) := by
        simpa [τab] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω) hτ_ne)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hproc : stoppedProcess Wℝ τab n ω = Wℝ (τab ω).untopA ω := by
        exact stoppedProcess_eq_of_ge hτ
      rw [hstopEq, hproc, hcast]
      rcases (by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
          W (τab ω).untopA ω = a ∨ W (τab ω).untopA ω = b) with hval | hval
      · rw [hval, Real.norm_eq_abs, abs_of_nonpos (show (a : ℝ) ≤ 0 by exact_mod_cast ha.le)]
        nlinarith [show (a : ℝ) < 0 by exact_mod_cast ha, show (0 : ℝ) < b by exact_mod_cast hb]
      · rw [hval, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ b by exact_mod_cast hb.le)]
        nlinarith [show (a : ℝ) < 0 by exact_mod_cast ha, show (0 : ℝ) < b by exact_mod_cast hb]
    · have hlt : (n : ℕ∞) < τab ω := lt_of_not_ge hτ
      have hlt_a : (n : ℕ∞) < τa ω := lt_of_lt_of_le hlt (hτab_le_τa ω)
      have hlt_b : (n : ℕ∞) < hittingAfter W ({b} : Set ℤ) 0 ω :=
        lt_of_lt_of_le hlt (hτab_le_τb ω)
      have ha_lt : a < W n ω := by
        exact strictLeftBoundary_before_hitting
          (fun k ↦ W k ω) hW_zero hW_step ha n hlt_a
      have hb_gt : W n ω < b := by
        exact strictRightBoundary_before_hitting
          (fun k ↦ W k ω) hW_zero hW_step hb n hlt_b
      have hcast : Wℝ n ω = (W n ω : ℝ) := hWℝ_eq n ω
      have hproc : stoppedProcess Wℝ τab n ω = Wℝ n ω := by
        exact stoppedProcess_eq_of_le (le_of_lt hlt)
      have ha_lt_real : (a : ℝ) < (W n ω : ℝ) := by exact_mod_cast ha_lt
      have hb_gt_real : (W n ω : ℝ) < (b : ℝ) := by exact_mod_cast hb_gt
      rw [hstopEq, hproc, hcast, Real.norm_eq_abs]
      refine abs_le.2 ?_
      constructor <;> nlinarith [ha_lt_real, hb_gt_real,
        show (a : ℝ) < 0 by exact_mod_cast ha,
        show (0 : ℝ) < b by exact_mod_cast hb]
  have hF_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun n ↦ F n ω) Filter.atTop (nhds (stoppedValue Wℝ τab ω)) := by
    filter_upwards
      [stoppedValue_truncation_ae_eventuallyEq
        (X := Wℝ) (μ := P) (τ := τab) hτab_ae_ne_top] with ω hω
    have hEq : (fun n ↦ F n ω) =ᶠ[Filter.atTop] fun _ ↦ stoppedValue Wℝ τab ω := by
      simpa [Filter.EventuallyEq, F] using hω
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  have hF_integral_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂P) Filter.atTop
        (nhds (∫ ω, stoppedValue Wℝ τab ω ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ ↦ (b - a : ℝ))
      (fun n ↦ (hF_int n).aestronglyMeasurable)
      (integrable_const (b - a : ℝ))
      hF_bound hF_tendsto
  have hzero_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂P) Filter.atTop (nhds (0 : ℝ)) := by
    have hEq : (fun n ↦ ∫ ω, F n ω ∂P) = fun _ : ℕ ↦ (0 : ℝ) := by
      funext n
      exact hF_expectation n
    simpa [hEq] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)))
  have hterminal_zero : ∫ ω, stoppedValue Wℝ τab ω ∂P = 0 := by
    exact tendsto_nhds_unique hF_integral_tendsto hzero_tendsto
  have hA_meas : MeasurableSet A := by
    have hτab_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τab ω = n} := by
      intro n
      exact ℱW.le n _ (hτab_stop.measurableSet_eq n)
    have hτa_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τa ω = n} := by
      intro n
      exact ℱW.le n _ (hτa_stop.measurableSet_eq n)
    have hτab_top_meas : MeasurableSet {ω | τab ω = ⊤} := by
      have hEq : {ω | τab ω = ⊤} = (⋃ n : ℕ, {ω | τab ω = n})ᶜ := by
        ext ω
        cases hτ : τab ω with
        | top =>
            simpa [hτ]
        | coe n =>
            simpa [hτ]
      rw [hEq]
      exact (MeasurableSet.iUnion hτab_eq_meas).compl
    have hτa_top_meas : MeasurableSet {ω | τa ω = ⊤} := by
      have hEq : {ω | τa ω = ⊤} = (⋃ n : ℕ, {ω | τa ω = n})ᶜ := by
        ext ω
        cases hτ : τa ω with
        | top =>
            simpa [hτ]
        | coe n =>
            simpa [hτ]
      rw [hEq]
      exact (MeasurableSet.iUnion hτa_eq_meas).compl
    have hEq :
        A =
          (⋃ n : ℕ, {ω | τab ω = n} ∩ {ω | τa ω = n}) ∪
            ({ω | τab ω = ⊤} ∩ {ω | τa ω = ⊤}) := by
      ext ω
      cases hτabω : τab ω with
      | top =>
          cases hτaω : τa ω with
          | top =>
              simpa [A, hτabω, hτaω]
          | coe m =>
              simpa [A, hτabω, hτaω]
      | coe n =>
          cases hτaω : τa ω with
          | top =>
              simpa [A, hτabω, hτaω]
          | coe m =>
              simpa [A, hτabω, hτaω, eq_comm]
    rw [hEq]
    exact
      (MeasurableSet.iUnion fun n ↦ (hτab_eq_meas n).inter (hτa_eq_meas n)).union
        (hτab_top_meas.inter hτa_top_meas)
  -- Proof comment: on the almost-sure finite-hit event, the terminal stopped value is `a` exactly
  -- on `{τab = τa}` and otherwise it is `b`.
  have hterminal_repr :
      stoppedValue Wℝ τab =ᵐ[P]
        fun ω ↦ A.indicator (fun _ ↦ (a : ℝ)) ω +
          Aᶜ.indicator (fun _ ↦ (b : ℝ)) ω := by
    filter_upwards [hτab_ae_ne_top] with ω hω
    by_cases hAω : ω ∈ A
    · have hEqτ : τab ω = τa ω := by simpa [A] using hAω
      have hτa_ne : τa ω ≠ ⊤ := by simpa [hEqτ] using hω
      have hval : W (τab ω).untopA ω = a := by
        simpa [τa, hEqτ, Set.mem_singleton_iff] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω) hτa_ne)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hterm : stoppedValue Wℝ τab ω = (a : ℝ) := by
        rw [stoppedValue, hcast, hval]
      simp [A, hAω, hterm]
    · have hmem : W (τab ω).untopA ω ∈ ({a, b} : Set ℤ) := by
        simpa [τab] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω) hω)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hval_b : W (τab ω).untopA ω = b := by
        rcases (by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
            W (τab ω).untopA ω = a ∨ W (τab ω).untopA ω = b) with hval_a | hval_b
        · have hidx_eq : (((τab ω).untopA : ℕ) : ℕ∞) = τab ω := by
            rw [WithTop.untopA_eq_untop hω]
            exact WithTop.coe_untop _ _
          have hτa_le : τa ω ≤ τab ω := by
            have hmem_a : W (τab ω).untopA ω ∈ ({a} : Set ℤ) := by
              simpa [Set.mem_singleton_iff, hval_a]
            calc
              τa ω ≤ (τab ω).untopA := by
                exact hittingAfter_le_of_mem
                  (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω)
                  (i := (τab ω).untopA) (by simp) hmem_a
              _ = τab ω := hidx_eq
          have hEqτ : τab ω = τa ω := le_antisymm (hτab_le_τa ω) hτa_le
          exact False.elim (hAω (by simpa [A] using hEqτ))
        · exact hval_b
      have hterm : stoppedValue Wℝ τab ω = (b : ℝ) := by
        rw [stoppedValue, hcast, hval_b]
      simp [A, hAω, hterm]
  have hterminal_integral :
      ∫ ω, stoppedValue Wℝ τab ω ∂P =
        P.real A * (a : ℝ) + P.real Aᶜ * (b : ℝ) := by
    calc
      ∫ ω, stoppedValue Wℝ τab ω ∂P =
          ∫ ω,
            (A.indicator (fun _ ↦ (a : ℝ)) ω +
              Aᶜ.indicator (fun _ ↦ (b : ℝ)) ω) ∂P := by
                exact integral_congr_ae hterminal_repr
      _ = ∫ ω, A.indicator (fun _ ↦ (a : ℝ)) ω ∂P
            + ∫ ω, Aᶜ.indicator (fun _ ↦ (b : ℝ)) ω ∂P := by
              rw [integral_add]
              · exact (integrable_const (a : ℝ)).indicator hA_meas
              · exact (integrable_const (b : ℝ)).indicator hA_meas.compl
      _ = P.real A * (a : ℝ) + P.real Aᶜ * (b : ℝ) := by
        rw [integral_indicator_const (a : ℝ) hA_meas,
          integral_indicator_const (b : ℝ) hA_meas.compl]
        simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hA_le_one : P A ≤ 1 := by
    calc
      P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
      _ = 1 := by simp
  have hA_ne_top : P A ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hA_le_one (by simp))
  have hA_compl_real : P.real Aᶜ = 1 - P.real A := by
    rw [Measure.real_def, measure_compl hA_meas hA_ne_top, measure_univ]
    rw [ENNReal.toReal_sub_of_le hA_le_one (by simp)]
    simp [Measure.real_def]
  have hA_real : P.real A = (b : ℝ) / (b - a : ℝ) := by
    have ha_real : (a : ℝ) < 0 := by exact_mod_cast ha
    have hb_real : (0 : ℝ) < b := by exact_mod_cast hb
    have haff :
        0 = P.real A * (a : ℝ) + (1 - P.real A) * (b : ℝ) := by
      calc
        0 = ∫ ω, stoppedValue Wℝ τab ω ∂P := hterminal_zero.symm
        _ = P.real A * (a : ℝ) + P.real Aᶜ * (b : ℝ) := hterminal_integral
        _ = P.real A * (a : ℝ) + (1 - P.real A) * (b : ℝ) := by
          rw [hA_compl_real]
    have hden : (b : ℝ) - a ≠ 0 := by
      nlinarith
    apply (eq_div_iff hden).2
    nlinarith
  have hA_measure :
      P A = ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := by
    calc
      P A = ENNReal.ofReal (P.real A) := by
        symm
        exact ENNReal.ofReal_toReal hA_ne_top
      _ = ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := by
        rw [hA_real]
  -- Proof comment: the measurable modification `W` agrees with the original walk `X` almost
  -- surely at every time, so the left-before-right event has the same probability for both walks.
  have hAeq_X :
      A =ᵐ[P]
        {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} := by
    filter_upwards [hW_eq_X] with ω hω
    have hpair :
        hittingAfter W ({a, b} : Set ℤ) 0 ω =
          hittingAfter X ({a, b} : Set ℤ) 0 ω := by
      exact hittingAfter_zero_eq_of_forall_eq
        (u := W) (v := X) (s := ({a, b} : Set ℤ)) (ω := ω) hω
    have hsingle :
        hittingAfter W ({a} : Set ℤ) 0 ω =
          hittingAfter X ({a} : Set ℤ) 0 ω := by
      exact hittingAfter_zero_eq_of_forall_eq
        (u := W) (v := X) (s := ({a} : Set ℤ)) (ω := ω) hω
    apply propext
    constructor <;> intro h
    · change hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω
      rw [← hpair, ← hsingle]
      simpa [A, τab, τa] using h
    · change hittingAfter W ({a, b} : Set ℤ) 0 ω = hittingAfter W ({a} : Set ℤ) 0 ω
      rw [hpair, hsingle]
      simpa [A, τab, τa] using h
  calc
    P {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} = P A := by
      exact (measure_congr hAeq_X).symm
    _ = ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := hA_measure
