/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- A finite predictable-step representation of a real-valued process on `Ω × [0, ∞)`. -/
structure PredictableStepRepresentation (ℱ : ContinuousFiltration) where
  /-- The number of stochastic time intervals. -/
  n : ℕ
  /-- The time partition `0 = t₀ < t₁ < ⋯ < tₙ` indexed by `Fin (n + 1)`. -/
  times : Fin (n + 1) → NNReal
  /-- The coefficient functions `h₀, …, hₙ₋₁` used on the successive time intervals. -/
  coeff : Fin n → Ω → ℝ
  /-- The partition starts at time `0`. -/
  times_zero : times 0 = 0
  /-- The partition times are strictly increasing. -/
  times_strictMono : StrictMono times
  /-- Each coefficient is bounded. -/
  coeff_bounded : ∀ i, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C
  /-- Each coefficient is measurable with respect to the previous filtration time. -/
  coeff_measurable : ∀ i, Measurable[ℱ (times i.castSucc)] (coeff i)

/-- The piecewise-constant process associated to a predictable-step representation. -/
noncomputable def PredictableStepRepresentation.toProcess {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) : Process :=
  fun t ω ↦
    ∑ i,
      data.coeff i ω *
        Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
          (fun _ : NNReal ↦ (1 : ℝ)) t

-- Proof sketch: unfold `PredictableStepRepresentation.toProcess`; the process is defined by this
-- finite sum of coefficient functions times interval indicators.
/-- The process attached to a predictable-step datum is exactly the advertised finite sum over the
partition intervals. -/
theorem PredictableStepRepresentation.toProcess_apply {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) (t : NNReal) (ω : Ω) :
    data.toProcess t ω =
      ∑ i,
        data.coeff i ω *
          Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
            (fun _ : NNReal ↦ (1 : ℝ)) t :=
  rfl

/-- Helper for Definition 25.2: the partition strips of a predictable-step representation are
pairwise disjoint. -/
theorem PredictableStepRepresentation.not_mem_interval_of_ne
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) {i j : Fin data.n}
    (hji : j ≠ i) {t : NNReal}
    (ht : t ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ)) :
    t ∉ Set.Ioc (data.times j.castSucc) (data.times j.succ) := by
  -- Compare the order of the two strips to see that their half-open intervals cannot overlap.
  rcases lt_or_gt_of_ne hji with hij | hij
  · have hji_le : j.succ ≤ i.castSucc := (Fin.succ_le_castSucc_iff).2 hij
    have hj_upper : data.times j.succ ≤ data.times i.castSucc :=
      data.times_strictMono.monotone hji_le
    exact fun hj_mem ↦ (not_lt_of_ge hj_mem.2) (lt_of_le_of_lt hj_upper ht.1)
  · have hij_le : i.succ ≤ j.castSucc := (Fin.succ_le_castSucc_iff).2 hij
    have hij_lower : data.times i.succ ≤ data.times j.castSucc :=
      data.times_strictMono.monotone hij_le
    exact fun hj_mem ↦ (not_lt_of_ge ht.2) (lt_of_le_of_lt hij_lower hj_mem.1)

/-- Helper for Definition 25.2: on any point of the `i`-th partition interval, the step process
attached to `data` takes the coefficient `data.coeff i`. -/
theorem PredictableStepRepresentation.toProcess_eq_coeff_of_mem_interval
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (i : Fin data.n)
    {t : NNReal} (ht : t ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ)) (ω : Ω) :
    data.toProcess t ω = data.coeff i ω := by
  -- Only the `i`-th strip can contain `t`, so every other indicator vanishes.
  rw [PredictableStepRepresentation.toProcess_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Set.indicator_of_mem ht, mul_one]
  · intro j _ hji
    have hj_not_mem : t ∉ Set.Ioc (data.times j.castSucc) (data.times j.succ) := by
      rcases lt_or_gt_of_ne hji with hij | hij
      · -- Earlier strips end no later than the left endpoint of the `i`-th strip.
        have hji_le : j.succ ≤ i.castSucc := (Fin.succ_le_castSucc_iff).2 hij
        have hj_upper : data.times j.succ ≤ data.times i.castSucc :=
          data.times_strictMono.monotone hji_le
        exact fun hj_mem ↦ (not_lt_of_ge hj_mem.2) (lt_of_le_of_lt hj_upper ht.1)
      · -- Later strips start no earlier than the right endpoint of the `i`-th strip.
        have hij_le : i.succ ≤ j.castSucc := (Fin.succ_le_castSucc_iff).2 hij
        have hij_lower : data.times i.succ ≤ data.times j.castSucc :=
          data.times_strictMono.monotone hij_le
        exact fun hj_mem ↦ (not_lt_of_ge ht.2) (lt_of_le_of_lt hij_lower hj_mem.1)
    simp only [Set.indicator_of_notMem hj_not_mem, mul_zero]
  · simp

/-- Helper for Definition 25.2: evaluating the process at the right endpoint of one partition strip
recovers the corresponding coefficient. -/
theorem PredictableStepRepresentation.toProcess_rightEndpoint_eq_coeff
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (i : Fin data.n) (ω : Ω) :
    data.toProcess (data.times i.succ) ω = data.coeff i ω := by
  -- The right endpoint still belongs to the half-open strip `(tᵢ, tᵢ₊₁]`.
  have hi_mem : data.times i.succ ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
    exact ⟨data.times_strictMono i.castSucc_lt_succ, le_rfl⟩
  exact data.toProcess_eq_coeff_of_mem_interval i hi_mem ω

/-- Helper for Definition 25.2: after the final partition time, the represented process vanishes. -/
theorem PredictableStepRepresentation.toProcess_eq_zero_of_last_lt
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) {t : NNReal}
    (ht : data.times (Fin.last data.n) < t) (ω : Ω) :
    data.toProcess t ω = 0 := by
  -- Every strip ends before `t`, so all indicators are zero.
  rw [PredictableStepRepresentation.toProcess_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi_upper : data.times i.succ ≤ data.times (Fin.last data.n) :=
    data.times_strictMono.monotone (Fin.le_last i.succ)
  have hi_not_mem : t ∉ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
    exact fun hi_mem ↦ (not_le_of_gt ht) (le_trans hi_mem.2 hi_upper)
  simp only [Set.indicator_of_notMem hi_not_mem, mul_zero]

/-- Helper for Definition 25.2: every positive time up to the terminal partition point lies in one
of the strips of `data`. -/
theorem PredictableStepRepresentation.exists_mem_interval_of_pos_le_last
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) {t : NNReal}
    (ht_pos : 0 < t) (ht_last : t ≤ data.times (Fin.last data.n)) :
    ∃ i : Fin data.n, t ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
  -- Pick the first partition index whose right endpoint is at least `t`.
  let P : ℕ → Prop := fun k ↦
    ∃ hk : k ≤ data.n, t ≤ data.times ⟨k, Nat.lt_succ_of_le hk⟩
  have h_exists : ∃ k, P k := ⟨data.n, ⟨le_rfl, by simpa using ht_last⟩⟩
  let m := Nat.find h_exists
  rcases Nat.find_spec h_exists with ⟨hm_le, hm_upper⟩
  have hm_pos : 0 < m := by
    by_contra hm_not_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not_pos
    have ht_zero : t ≤ 0 := by
      simpa [m, hm_zero, data.times_zero] using hm_upper
    exact (not_le_of_gt ht_pos) ht_zero
  have hm_pred_lt : m - 1 < data.n := by
    exact lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hm_pos)) hm_le
  let i : Fin data.n := ⟨m - 1, hm_pred_lt⟩
  have hprev_not : ¬ t ≤ data.times i.castSucc := by
    intro hprev
    have hprev_mem : P (m - 1) := by
      refine ⟨le_trans (Nat.pred_le _) hm_le, ?_⟩
      simpa [i]
        using hprev
    exact Nat.not_lt_of_ge (Nat.find_min' h_exists hprev_mem) (Nat.pred_lt (Nat.ne_of_gt hm_pos))
  have hlower : data.times i.castSucc < t := lt_of_not_ge hprev_not
  have hupper : t ≤ data.times i.succ := by
    have hi_succ : i.succ = ⟨m, Nat.lt_succ_of_le hm_le⟩ := by
      ext
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    simpa [hi_succ] using hm_upper
  exact ⟨i, ⟨hlower, hupper⟩⟩

/-- Helper for Definition 25.2: if `(u, v]` is contained in one original strip, then the
represented process is constant there with value `data.coeff i`. -/
theorem PredictableStepRepresentation.toProcess_eq_coeff_of_subinterval
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (i : Fin data.n)
    {u v t : NNReal} (hu : data.times i.castSucc ≤ u) (hv : v ≤ data.times i.succ)
    (ht : t ∈ Set.Ioc u v) (ω : Ω) :
    data.toProcess t ω = data.coeff i ω := by
  -- The point `t` still lies in the original strip `(tᵢ, tᵢ₊₁]`.
  refine data.toProcess_eq_coeff_of_mem_interval i ?_ ω
  exact ⟨lt_of_le_of_lt hu ht.1, le_trans ht.2 hv⟩

/-- Helper for Definition 25.2: on an interval that contains no partition boundary of `data` in
its interior, the represented process is a single bounded `ℱ u`-measurable coefficient. -/
theorem PredictableStepRepresentation.exists_bddMeasurable_eq_on_Ioc_of_no_boundary
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) {u v : NNReal}
    (huv : u < v) (hboundary : ∀ i : Fin data.n, data.times i.succ ∉ Set.Ioo u v) :
    ∃ g : Ω → ℝ,
      Measurable[ℱ u] g ∧
      (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
      ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc u v → data.toProcess t = g := by
  by_cases h_last : v ≤ data.times (Fin.last data.n)
  · -- Route correction: package the active strip itself rather than evaluating at the right
    -- endpoint, so the measurability lives at the left endpoint `u`.
    have hv_pos : 0 < v := lt_of_le_of_lt bot_le huv
    obtain ⟨i, hvi⟩ := data.exists_mem_interval_of_pos_le_last hv_pos h_last
    have hleft : data.times i.castSucc ≤ u := by
      by_contra hleft_not
      have hu_left : u < data.times i.castSucc := lt_of_not_ge hleft_not
      have hleft_not_mem : data.times i.castSucc ∉ Set.Ioo u v := by
        by_cases hi_zero : (i : ℕ) = 0
        · have hcast : i.castSucc = 0 := by
            ext
            simp [hi_zero]
          exact fun hi_mem ↦
            (not_lt_of_ge (show (0 : NNReal) ≤ u from bot_le))
              (by simpa [hcast, data.times_zero] using hi_mem.1)
        · have hi_val_ne_zero : (i : ℕ) ≠ 0 := by
            exact hi_zero
          have hi_pos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi_val_ne_zero
          let j : Fin data.n :=
            ⟨i.1 - 1, lt_of_lt_of_le (Nat.pred_lt hi_val_ne_zero) (Nat.le_of_lt i.2)⟩
          have hj : j.succ = i.castSucc := by
            ext
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt hi_pos)
          simpa [hj] using hboundary j
      exact hleft_not_mem ⟨hu_left, hvi.1⟩
    refine ⟨data.coeff i, ?_, ?_, ?_⟩
    · -- Transport measurability from the old left endpoint to the new one via filtration
      -- monotonicity.
      exact (data.coeff_measurable i).mono (ℱ.mono hleft) le_rfl
    · exact data.coeff_bounded i
    · intro t ht
      funext ω
      exact data.toProcess_eq_coeff_of_subinterval i hleft hvi.2 ht ω
  · have hlast_lt_v : data.times (Fin.last data.n) < v := lt_of_not_ge h_last
    refine ⟨0, ?_, ⟨0, fun _ ↦ by simp⟩, ?_⟩
    · exact measurable_const
    intro t ht
    funext ω
    -- If `t` were not past the final boundary, some strip right endpoint would lie in `(u, v)`.
    have ht_last : data.times (Fin.last data.n) < t := by
      by_contra ht_not
      have ht_le_last : t ≤ data.times (Fin.last data.n) := le_of_not_gt ht_not
      have ht_pos : 0 < t := lt_of_le_of_lt bot_le ht.1
      obtain ⟨i, hti⟩ := data.exists_mem_interval_of_pos_le_last ht_pos ht_le_last
      have hi_upper : data.times i.succ < v := by
        exact lt_of_le_of_lt (data.times_strictMono.monotone (Fin.le_last i.succ)) hlast_lt_v
      exact (hboundary i) ⟨lt_of_lt_of_le ht.1 hti.2, hi_upper⟩
    exact data.toProcess_eq_zero_of_last_lt ht_last ω

private def zeroPredictableStepRepresentation (ℱ : ContinuousFiltration) :
    PredictableStepRepresentation ℱ where
  n := 0
  times := fun _ ↦ 0
  coeff := fun i ↦ Fin.elim0 i
  times_zero := rfl
  times_strictMono := by
    intro i j hij
    fin_cases i
    fin_cases j
    cases hij
  coeff_bounded := by
    intro i
    exact Fin.elim0 i
  coeff_measurable := by
    intro i
    exact Fin.elim0 i

private theorem zeroPredictableStepRepresentation_toProcess (ℱ : ContinuousFiltration) :
    (zeroPredictableStepRepresentation ℱ).toProcess = 0 := by
  funext t ω
  simp [zeroPredictableStepRepresentation, PredictableStepRepresentation.toProcess]

private def smulPredictableStepRepresentation {ℱ : ContinuousFiltration} (a : ℝ)
    (data : PredictableStepRepresentation ℱ) : PredictableStepRepresentation ℱ where
  n := data.n
  times := data.times
  coeff := fun i ω ↦ a * data.coeff i ω
  times_zero := data.times_zero
  times_strictMono := data.times_strictMono
  coeff_bounded := by
    intro i
    rcases data.coeff_bounded i with ⟨C, hC⟩
    refine ⟨|a| * C, ?_⟩
    intro ω
    calc
      |a * data.coeff i ω| = |a| * |data.coeff i ω| := by simp [abs_mul]
      _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg a)
  coeff_measurable := by
    intro i
    exact Measurable.const_mul (data.coeff_measurable i) a

private theorem smulPredictableStepRepresentation_toProcess {ℱ : ContinuousFiltration} (a : ℝ)
    (data : PredictableStepRepresentation ℱ) :
    (smulPredictableStepRepresentation a data).toProcess = a • data.toProcess := by
  funext t ω
  change
    ∑ i,
      (a * data.coeff i ω) *
        Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
          (fun _ : NNReal ↦ (1 : ℝ)) t =
      a *
        ∑ i,
          data.coeff i ω *
            Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
              (fun _ : NNReal ↦ (1 : ℝ)) t
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- Helper for Definition 25.2: no element of a finite ordered set lies strictly between two
consecutive values of its increasing `orderEmbOfFin` enumeration. -/
private theorem not_mem_Ioo_between_orderEmbOfFin_consecutive
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) (i : Fin n) {x : NNReal} (hx : x ∈ B) :
    x ∉ Set.Ioo (B.orderEmbOfFin hB i.castSucc) (B.orderEmbOfFin hB i.succ) := by
  -- Pull `x` back to its index in the increasing enumeration, then compare indices.
  intro hxIoo
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  have hij_left : i.castSucc < j := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.1)
  have hij_right : j < i.succ := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.2)
  have hij_left_nat : (i : ℕ) < (j : ℕ) := by
    change ((i.castSucc : Fin (n + 1)) : ℕ) < (j : ℕ)
    exact hij_left
  have hij_right_nat : (j : ℕ) < (i : ℕ) + 1 := by
    change (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ)
    exact hij_right
  omega

/-- Helper for Definition 25.2: every element of a finite ordered set is bounded above by the
last value of its increasing `orderEmbOfFin` enumeration. -/
private theorem le_orderEmbOfFin_last_of_mem
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) {x : NNReal} (hx : x ∈ B) :
    x ≤ B.orderEmbOfFin hB (Fin.last n) := by
  -- Compare the index of `x` with the last index of the enumeration.
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  have hj_last : j ≤ Fin.last n := Fin.le_last j
  simpa [hjx] using (B.orderEmbOfFin hB).monotone hj_last

private theorem add_mem_predictableSimpleProcesses {ℱ : ContinuousFiltration} {H K : Process}
    (hH : ∃ representation : PredictableStepRepresentation ℱ, H = representation.toProcess)
    (hK : ∃ representation : PredictableStepRepresentation ℱ, K = representation.toProcess) :
    ∃ representation : PredictableStepRepresentation ℱ,
      H + K = representation.toProcess := by
  classical
  rcases hH with ⟨dataH, rfl⟩
  rcases hK with ⟨dataK, rfl⟩
  let B : Finset NNReal :=
    Finset.image dataH.times Finset.univ ∪ Finset.image dataK.times Finset.univ
  have hB0 : (0 : NNReal) ∈ B := by
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, dataH.times_zero⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hB0⟩
  let nRef : ℕ := B.card - 1
  have hBcard : B.card = nRef + 1 := by
    have hcard : B.card = (B.card - 1) + 1 := by
      omega
    simpa [nRef] using hcard
  let times : Fin (nRef + 1) → NNReal := B.orderEmbOfFin hBcard
  have hTimesZero : times 0 = 0 := by
    have hBmin : B.min' (Finset.card_pos.mp hBpos) = 0 := by
      refine (Finset.min'_eq_iff (s := B) (H := Finset.card_pos.mp hBpos) 0).2 ?_
      constructor
      · exact hB0
      · intro b hb
        exact bot_le
    calc
      times 0 = B.min' (Finset.card_pos.mp hBpos) := by
        have hzero :=
          Finset.orderEmbOfFin_zero (s := B) hBcard (by simpa [hBcard] using hBpos)
        simpa [times] using hzero
      _ = 0 := hBmin
  have hTimesStrictMono : StrictMono times := (B.orderEmbOfFin hBcard).strictMono
  have hStripH :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) → dataH.toProcess t = g :=
      by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin dataH.n, dataH.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i)
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- The existing no-boundary lemma gives the strip coefficient directly.
    exact dataH.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  have hStripK :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) → dataK.toProcess t = g :=
      by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin dataK.n, dataK.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i)
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- The same stripwise argument applies to the second process.
    exact dataK.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  let coeffH : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripH i)
  let coeffK : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripK i)
  have hCoeffH_meas : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffH i) := by
    intro i
    exact (Classical.choose_spec (hStripH i)).1
  have hCoeffK_meas : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffK i) := by
    intro i
    exact (Classical.choose_spec (hStripK i)).1
  have hCoeffH_bounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffH i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStripH i)).2.1
  have hCoeffK_bounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffK i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStripK i)).2.1
  have hCoeffH_eq :
      ∀ i : Fin nRef, ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        dataH.toProcess t = coeffH i := by
    intro i t ht
    exact (Classical.choose_spec (hStripH i)).2.2 ht
  have hCoeffK_eq :
      ∀ i : Fin nRef, ∀ ⦃t : NNReal⦄, t ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        dataK.toProcess t = coeffK i := by
    intro i t ht
    exact (Classical.choose_spec (hStripK i)).2.2 ht
  let coeff : Fin nRef → Ω → ℝ := fun i ω ↦ coeffH i ω + coeffK i ω
  have hCoeffBounded : ∀ i, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C := by
    intro i
    rcases hCoeffH_bounded i with ⟨CH, hCH⟩
    rcases hCoeffK_bounded i with ⟨CK, hCK⟩
    refine ⟨|CH| + |CK|, ?_⟩
    intro ω
    have hHle : |coeffH i ω| ≤ |CH| := le_trans (hCH ω) (le_abs_self CH)
    have hKle : |coeffK i ω| ≤ |CK| := le_trans (hCK ω) (le_abs_self CK)
    have htriangle : |coeffH i ω + coeffK i ω| ≤ |coeffH i ω| + |coeffK i ω| := by
      simpa [Real.norm_eq_abs] using norm_add_le (coeffH i ω) (coeffK i ω)
    calc
      |coeff i ω| = |coeffH i ω + coeffK i ω| := rfl
      _ ≤ |coeffH i ω| + |coeffK i ω| := htriangle
      _ ≤ |CH| + |CK| := add_le_add hHle hKle
  have hCoeffMeasurable : ∀ i, Measurable[ℱ (times i.castSucc)] (coeff i) := by
    intro i
    exact (hCoeffH_meas i).add (hCoeffK_meas i)
  let refined : PredictableStepRepresentation ℱ :=
    { n := nRef
      times := times
      coeff := coeff
      times_zero := hTimesZero
      times_strictMono := hTimesStrictMono
      coeff_bounded := hCoeffBounded
      coeff_measurable := hCoeffMeasurable }
  have hLastH_le : dataH.times (Fin.last dataH.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem (B := B) (hB := hBcard)
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨Fin.last dataH.n, Finset.mem_univ _, rfl⟩
  have hLastK_le : dataK.times (Fin.last dataK.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem (B := B) (hB := hBcard)
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨Fin.last dataK.n, Finset.mem_univ _, rfl⟩
  refine ⟨refined, ?_⟩
  funext t ω
  by_cases hAfter : times (Fin.last nRef) < t
  · -- After the last refined boundary, every old and new strip indicator vanishes.
    have hHzero : dataH.toProcess t ω = 0 := by
      exact dataH.toProcess_eq_zero_of_last_lt (lt_of_le_of_lt hLastH_le hAfter) ω
    have hKzero : dataK.toProcess t ω = 0 := by
      exact dataK.toProcess_eq_zero_of_last_lt (lt_of_le_of_lt hLastK_le hAfter) ω
    have hRefZero : refined.toProcess t ω = 0 := by
      exact refined.toProcess_eq_zero_of_last_lt hAfter ω
    simp [hHzero, hKzero, hRefZero]
  · by_cases ht0 : t = 0
    · -- At time `0`, all half-open interval indicators vanish.
      subst ht0
      simp [PredictableStepRepresentation.toProcess_apply, refined, times, coeff]
    · -- On an active refined strip, both old processes are constant and add to the new
      -- coefficient by construction.
      have ht_pos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht0)
      have ht_le_last : t ≤ times (Fin.last nRef) := le_of_not_gt hAfter
      obtain ⟨i, hti⟩ := refined.exists_mem_interval_of_pos_le_last ht_pos ht_le_last
      have hH_eq : dataH.toProcess t ω = coeffH i ω := by
        exact congrFun (hCoeffH_eq i hti) ω
      have hK_eq : dataK.toProcess t ω = coeffK i ω := by
        exact congrFun (hCoeffK_eq i hti) ω
      calc
        dataH.toProcess t ω + dataK.toProcess t ω = coeff i ω := by
          simp [coeff, hH_eq, hK_eq]
        _ = refined.toProcess t ω := by
          symm
          exact refined.toProcess_eq_coeff_of_mem_interval i hti ω

/-- Definition 25.2: the vector space `𝓔` of predictable simple processes is the subspace of
real-valued processes on `Ω × [0, ∞)` that admit a finite piecewise-constant representation
`H_t(ω) = ∑ i h_i(ω) 1_(tᵢ,tᵢ₊₁](t)` with bounded coefficients `h_i` that are measurable with
respect to the preceding filtration time. -/
def predictableSimpleProcesses (ℱ : ContinuousFiltration) : Submodule ℝ Process where
  carrier := {H | ∃ representation : PredictableStepRepresentation ℱ, H = representation.toProcess}
  zero_mem' := by
    refine ⟨zeroPredictableStepRepresentation ℱ, ?_⟩
    exact zeroPredictableStepRepresentation_toProcess ℱ
  add_mem' := by
    intro H K hH hK
    exact add_mem_predictableSimpleProcesses hH hK
  smul_mem' := by
    intro a H hH
    rcases hH with ⟨data, rfl⟩
    refine ⟨smulPredictableStepRepresentation a data, ?_⟩
    symm
    exact smulPredictableStepRepresentation_toProcess a data

/-- A short chapter-wide name for the canonical subtype of the textbook vector space `𝓔`. -/
abbrev PredictableSimpleProcess (ℱ : ContinuousFiltration) :=
  predictableSimpleProcesses ℱ

namespace PredictableSimpleProcess

/-- Every predictable simple process admits a finite predictable-step representation. -/
theorem exists_representation {ℱ : ContinuousFiltration} (H : PredictableSimpleProcess ℱ) :
    ∃ representation : PredictableStepRepresentation ℱ, (H : Process) = representation.toProcess :=
  H.2

end PredictableSimpleProcess

/-- Every predictable-step datum defines an element of `predictableSimpleProcesses ℱ`. -/
theorem PredictableStepRepresentation.mem_predictableSimpleProcesses {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) :
    data.toProcess ∈ predictableSimpleProcesses ℱ :=
  ⟨data, rfl⟩

/-- Every predictable-step datum defines a canonical predictable simple process. -/
noncomputable def PredictableStepRepresentation.toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) :
    PredictableSimpleProcess ℱ :=
  ⟨data.toProcess, data.mem_predictableSimpleProcesses⟩

/-- Coercing the canonical predictable simple process attached to a representation recovers the
underlying process. -/
@[simp] theorem PredictableStepRepresentation.toPredictableSimpleProcess_coe
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) :
    (data.toPredictableSimpleProcess : Process) = data.toProcess :=
  rfl

/-- The product measure `μ ⊗ dt` on `Ω × [0, ∞)` used for the `L²` theory of processes. -/
noncomputable abbrev processMeasure (μ : Measure Ω) : Measure (Ω × ℝ) :=
  μ.prod ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Regard a nonnegative-time process as a function on `Ω × ℝ`, with negative times clamped to
`0`. On `processMeasure μ`, this agrees almost everywhere with the usual restriction to
`Ω × [0, ∞)`. -/
abbrev processToTimeSpaceFun (H : Process) : Ω × ℝ → ℝ :=
  Function.uncurry fun ω (t : ℝ) ↦ H t.toNNReal ω

/-- The canonical `L²(μ ⊗ dt)` image of the globally square-integrable predictable simple
processes from Definition 25.2. -/
def predictableSimpleProcessL2 (ℱ : ContinuousFiltration) (μ : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 (processMeasure μ)) where
  carrier := {f | ∃ H : PredictableSimpleProcess ℱ,
    ∃ hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ),
      f = hH.toLp (processToTimeSpaceFun (H : Process))}
  zero_mem' := by
    have h0 : MemLp (processToTimeSpaceFun ((0 : PredictableSimpleProcess ℱ) : Process))
        (2 : ℝ≥0∞) (processMeasure μ) := by
      change MemLp (0 : Ω × ℝ → ℝ) (2 : ℝ≥0∞) (processMeasure μ)
      exact (MemLp.zero : MemLp (0 : Ω × ℝ → ℝ) (2 : ℝ≥0∞) (processMeasure μ))
    refine ⟨0, h0, ?_⟩
    change h0.toLp (0 : Ω × ℝ → ℝ) = 0
    exact MemLp.toLp_zero h0
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨H, hH, rfl⟩
    rcases hg with ⟨G, hG, rfl⟩
    refine ⟨H + G, by
      simpa [processToTimeSpaceFun] using hH.add hG, ?_⟩
    simpa [processToTimeSpaceFun] using MemLp.toLp_add hH hG
  smul_mem' := by
    intro a f hf
    rcases hf with ⟨H, hH, rfl⟩
    refine ⟨a • H, by
      simpa [processToTimeSpaceFun] using hH.const_smul a, ?_⟩
    simpa [processToTimeSpaceFun] using MemLp.toLp_const_smul a hH

/-- A globally square-integrable predictable simple process defines an element of the canonical
`L²(μ ⊗ dt)` space of predictable simple integrands. -/
theorem toLp_mem_predictableSimpleProcessL2
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    hH.toLp (processToTimeSpaceFun (H : Process)) ∈ predictableSimpleProcessL2 ℱ μ :=
  ⟨H, hH, rfl⟩

/-- The canonical `L²(μ ⊗ dt)` element represented by a globally square-integrable predictable
simple process. -/
noncomputable def predictableSimpleProcessToL2
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    predictableSimpleProcessL2 ℱ μ :=
  ⟨hH.toLp (processToTimeSpaceFun (H : Process)),
    toLp_mem_predictableSimpleProcessL2 H hH⟩

/-- Coercing `predictableSimpleProcessToL2 H hH` to the ambient `L²(μ ⊗ dt)` space recovers the
represented `Lp` class. -/
@[simp] theorem predictableSimpleProcessToL2_coe
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    ((predictableSimpleProcessToL2 H hH : predictableSimpleProcessL2 ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      hH.toLp (processToTimeSpaceFun (H : Process)) :=
  rfl

/-- The pseudonorm from Definition 25.2 on the vector space of predictable simple processes. -/
noncomputable def predictableSimpleProcessNorm {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) : ℝ :=
  Real.sqrt
    (∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
      ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ)

/-- The square of the pseudonorm from Definition 25.2, written directly in the integral form
`E[∫₀^∞ H_s^2 ds]`. -/
noncomputable def predictableSimpleProcessNormSq {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) : ℝ :=
  ∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
    ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ

/-- Unfolding `predictableSimpleProcessNormSq` gives the defining integral formula on the
underlying process. -/
theorem predictableSimpleProcessNormSq_def {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) :
    predictableSimpleProcessNormSq μ H =
      ∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
        ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ :=
  rfl

/-- Helper for Definition 25.2: a coefficient that is `ℱ a`-measurable stays predictable when it
is supported on the strip `(a, b]`. -/
private theorem measurable_uncurry_mul_indicator_Ioc {ℱ : ContinuousFiltration}
    {a b : NNReal} {f : Ω → ℝ} (hf : Measurable[ℱ a] f) :
    Measurable[ℱ.predictable]
      (Function.uncurry fun t ω ↦
        f ω * Set.indicator (Set.Ioc a b) (fun _ : NNReal ↦ (1 : ℝ)) t) := by
  intro s hs
  by_cases h0 : (0 : ℝ) ∈ s
  · -- When `0 ∈ s`, points outside the strip belong to the preimage automatically.
    have hpreimage :
        (Function.uncurry
            (fun t ω ↦ f ω * Set.indicator (Set.Ioc a b) (fun _ : NNReal ↦ (1 : ℝ)) t)) ⁻¹' s =
          (Set.Ioc a b ×ˢ (f ⁻¹' s)) ∪ (Set.Ioc a b ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      rcases p with ⟨t, ω⟩
      by_cases ht : t ∈ Set.Ioc a b
      · simp [Function.uncurry, ht]
      · simp [Function.uncurry, ht, h0]
    rw [hpreimage]
    refine (measurableSet_predictable_Ioc_prod a b (hf hs)).union ?_
    exact (measurableSet_predictable_Ioc_prod a b
      (MeasurableSet.univ : MeasurableSet[ℱ a] (Set.univ : Set Ω))).compl
  · -- When `0 ∉ s`, the preimage is exactly the strip paired with the coefficient preimage.
    have hpreimage :
        (Function.uncurry
            (fun t ω ↦ f ω * Set.indicator (Set.Ioc a b) (fun _ : NNReal ↦ (1 : ℝ)) t)) ⁻¹' s =
          Set.Ioc a b ×ˢ (f ⁻¹' s) := by
      ext p
      rcases p with ⟨t, ω⟩
      by_cases ht : t ∈ Set.Ioc a b
      · simp [Function.uncurry, ht]
      · simp [Function.uncurry, ht, h0]
    rw [hpreimage]
    exact measurableSet_predictable_Ioc_prod a b (hf hs)

/-- Helper for Definition 25.2: the process encoded by a predictable-step representation is
predictable. -/
theorem PredictableStepRepresentation.isPredictable_toProcess {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) :
    IsPredictable ℱ data.toProcess := by
  -- Reduce the claim to measurable preimages of the finite strip decomposition on `Ω × [0, ∞)`.
  have hmeas :
      Measurable[ℱ.predictable] (Function.uncurry data.toProcess) := by
    change
      Measurable[ℱ.predictable]
        (fun p : NNReal × Ω ↦
          ∑ i,
            data.coeff i p.2 *
              Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
                (fun _ : NNReal ↦ (1 : ℝ)) p.1)
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin data.n))) ?_ ?_
    · simp
    · intro i s hi hs
      -- Add one strip at a time; each strip is predictable by the generator lemma above.
      have hstrip :
          Measurable[ℱ.predictable]
            (Function.uncurry fun t ω ↦
              data.coeff i ω *
                Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
                  (fun _ : NNReal ↦ (1 : ℝ)) t) :=
        measurable_uncurry_mul_indicator_Ioc (a := data.times i.castSucc)
          (b := data.times i.succ) (f := data.coeff i) (data.coeff_measurable i)
      simpa [Finset.sum_insert hi, Function.uncurry] using hstrip.add hs
  exact hmeas.stronglyMeasurable

-- Proof sketch: a predictable-step representation is measurable with respect to the predictable
-- σ-algebra because each rectangle `(t_i, t_{i+1}] × A` with `A ∈ ℱ t_i` is predictable, and
-- finite linear combinations preserve predictability.
/-- Every element of `predictableSimpleProcesses ℱ` is predictable in mathlib's canonical
sense. -/
theorem isPredictable_of_mem_predictableSimpleProcesses {ℱ : ContinuousFiltration} {H : Process}
    (hH : H ∈ predictableSimpleProcesses ℱ) :
    IsPredictable ℱ H := by
  rcases hH with ⟨data, rfl⟩
  -- Use the chosen step representation directly; predictability was proved at the representation
  -- level to keep the outer theorem a short wrapper.
  simpa using data.isPredictable_toProcess

/-- Every predictable simple process is predictable in mathlib's canonical sense. -/
theorem PredictableSimpleProcess.isPredictable {ℱ : ContinuousFiltration}
    (H : PredictableSimpleProcess ℱ) :
    IsPredictable ℱ (H : Process) :=
  isPredictable_of_mem_predictableSimpleProcesses H.2

/-- Helper for Definition 25.2: on an active strip, squaring the step process leaves exactly the
corresponding squared coefficient term. -/
private theorem PredictableStepRepresentation.sq_toProcess_eq_indicatorSum_of_mem_interval
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω)
    (i : Fin data.n) {t : ℝ} (ht0 : 0 ≤ t)
    (hti : t.toNNReal ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ)) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  have hti_real :
      t ∈ Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ) := by
    simpa [Real.toNNReal_of_nonneg ht0] using hti
  have hproc : data.toProcess t.toNNReal ω = data.coeff i ω :=
    data.toProcess_eq_coeff_of_mem_interval i hti ω
  calc
    (data.toProcess t.toNNReal ω) ^ 2 = (data.coeff i ω) ^ 2 := by rw [hproc]
    _ =
        ∑ j,
          (data.coeff j ω) ^ 2 *
            Set.indicator
              (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
              (fun _ : ℝ ↦ (1 : ℝ)) t := by
          symm
          rw [Finset.sum_eq_single i]
          · simp [hti_real]
          · intro j _ hji
            have hj_not :
                t ∉ Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ) := by
              intro htj
              have htj_nn :
                  t.toNNReal ∈ Set.Ioc (data.times j.castSucc) (data.times j.succ) := by
                simpa [Real.toNNReal_of_nonneg ht0] using htj
              exact data.not_mem_interval_of_ne hji hti htj_nn
            simp [hj_not]
          · simp

/-- Helper for Definition 25.2: once time is past the last partition point, every strip
indicator vanishes. -/
private theorem PredictableStepRepresentation.sq_toProcess_eq_indicatorSum_of_last_lt
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) {t : ℝ}
    (ht0 : 0 ≤ t) (hAfter : data.times (Fin.last data.n) < t.toNNReal) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  have hAfterReal : (data.times (Fin.last data.n) : ℝ) < t := by
    simpa [Real.toNNReal_of_nonneg ht0] using hAfter
  have hproc : data.toProcess t.toNNReal ω = 0 := by
    exact data.toProcess_eq_zero_of_last_lt hAfter ω
  calc
    (data.toProcess t.toNNReal ω) ^ 2 = 0 := by simp [hproc]
    _ =
        ∑ j,
          (data.coeff j ω) ^ 2 *
            Set.indicator
              (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
              (fun _ : ℝ ↦ (1 : ℝ)) t := by
          symm
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hj_upper :
              ((data.times j.succ : NNReal) : ℝ) ≤ data.times (Fin.last data.n) := by
            exact_mod_cast data.times_strictMono.monotone (Fin.le_last j.succ)
          have hj_not :
              t ∉ Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ) := by
            exact fun htj ↦ (not_le_of_gt hAfterReal) (le_trans htj.2 hj_upper)
          simp [hj_not]

/-- Helper for Definition 25.2: at a nonnegative time, squaring the step process produces the
corresponding sum of squared coefficients times strip indicators. -/
private theorem PredictableStepRepresentation.sq_toProcess_eq_indicatorSum_of_nonneg
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) {t : ℝ}
    (ht0 : 0 ≤ t) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  by_cases ht_eq : t = 0
  · subst ht_eq
    simp [PredictableStepRepresentation.toProcess_apply]
  · by_cases ht_le_last : t.toNNReal ≤ data.times (Fin.last data.n)
    · have ht_pos : 0 < t.toNNReal := by
        have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
        simpa [Real.toNNReal_of_nonneg ht0] using this
      obtain ⟨i, hti⟩ := data.exists_mem_interval_of_pos_le_last ht_pos ht_le_last
      exact data.sq_toProcess_eq_indicatorSum_of_mem_interval ω i ht0 hti
    · exact data.sq_toProcess_eq_indicatorSum_of_last_lt ω ht0 (lt_of_not_ge ht_le_last)

/-- Helper for Definition 25.2: the indicator of a nonnegative strip is integrable on `[0, ∞)`. -/
private theorem integrable_indicator_Ioc_on_Ici
    (a b : NNReal) :
    Integrable
      (Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)))
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  have hsubset : Set.Ioc (a : ℝ) b ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact le_of_lt <| lt_of_le_of_lt (show (0 : ℝ) ≤ a by exact_mod_cast bot_le) ht.1
  have hfinite :
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) (Set.Ioc (a : ℝ) b) ≠ ∞ := by
    rw [Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.2 hsubset]
    exact ne_of_lt measure_Ioc_lt_top
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const hfinite

/-- Helper for Definition 25.2: integrating a constant multiple of a strip indicator over
`[0, ∞)` returns the interval length. -/
private theorem integral_const_mul_indicator_Ioc_on_Ici
    (a b : NNReal) (c : ℝ) (hab : a ≤ b) :
    ∫ t in Set.Ici (0 : ℝ), c * Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)) t =
      c * ((b - a : NNReal) : ℝ) := by
  have hsubset : Set.Ioc (a : ℝ) b ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact le_of_lt <| lt_of_le_of_lt (show (0 : ℝ) ≤ a by exact_mod_cast bot_le) ht.1
  have hlength :
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).real (Set.Ioc (a : ℝ) b) =
        ((b - a : NNReal) : ℝ) := by
    rw [measureReal_def, Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.2 hsubset,
      Real.volume_Ioc]
    simpa [NNReal.coe_sub hab]
  rw [integral_const_mul]
  have hindicator :
      ∫ t in Set.Ici (0 : ℝ),
          Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)) t ∂ (volume : Measure ℝ) =
        ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).real (Set.Ioc (a : ℝ) b) := by
    have hindicator' :=
      integral_indicator_one
        (μ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) (s := Set.Ioc (a : ℝ) b)
        measurableSet_Ioc
    simpa using hindicator'
  rw [hindicator, hlength]

/-- Helper for Definition 25.2: for fixed `ω`, integrating the squared step process over time
produces the textbook finite sum of coefficient squares times interval lengths. -/
private theorem PredictableStepRepresentation.timeIntegralSq_eq_sum
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) :
    ∫ t in Set.Ici (0 : ℝ), (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  have hpoint :
      (fun t : ℝ ↦ (data.toProcess t.toNNReal ω) ^ 2) =ᵐ[
          (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))]
        fun t ↦
          ∑ i,
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
    -- Work pointwise on nonnegative times, where `t.toNNReal` agrees with `t`.
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
    exact data.sq_toProcess_eq_indicatorSum_of_nonneg ω ht0
  calc
    ∫ t in Set.Ici (0 : ℝ), (data.toProcess t.toNNReal ω) ^ 2 =
        ∫ t in Set.Ici (0 : ℝ),
          ∑ i,
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
      exact integral_congr_ae hpoint
    _ =
        ∑ i,
          ∫ t in Set.Ici (0 : ℝ),
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
      rw [integral_finset_sum]
      intro i hi
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (integrable_indicator_Ioc_on_Ici (data.times i.castSucc) (data.times i.succ)).const_mul
          ((data.coeff i ω) ^ 2)
    _ =
        ∑ i,
          (data.coeff i ω) ^ 2 *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- Each strip contributes its coefficient square times the length of that interval.
      exact integral_const_mul_indicator_Ioc_on_Ici
        (data.times i.castSucc) (data.times i.succ) ((data.coeff i ω) ^ 2)
        (le_of_lt (data.times_strictMono i.castSucc_lt_succ))

-- Proof sketch: integrate the square of the step representation interval by interval. The
-- indicator functions have disjoint supports and contribute exactly the interval lengths
-- `tᵢ₊₁ - tᵢ`, yielding the textbook sum formula.
/-- For a chosen predictable-step representation, the square of the Definition 25.2 pseudonorm of
the associated predictable simple process agrees with the textbook sum
`∑ E[h_i^2] (t_{i+1} - t_i)`. -/
theorem predictableSimpleProcessNormSq_eq_sum {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (data : PredictableStepRepresentation ℱ) :
    predictableSimpleProcessNormSq μ data.toPredictableSimpleProcess =
      ∑ i,
        (∫ ω, (data.coeff i ω) ^ 2 ∂ μ) *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  have hCoeffSq_integrable : ∀ i : Fin data.n, Integrable (fun ω ↦ (data.coeff i ω) ^ 2) μ := by
    intro i
    rcases data.coeff_bounded i with ⟨C, hC⟩
    have hmeas : AEStronglyMeasurable (fun ω ↦ (data.coeff i ω) ^ 2) μ := by
      exact (((data.coeff_measurable i).mono (ℱ.le _) le_rfl).pow_const 2).aestronglyMeasurable
    refine Integrable.of_bound hmeas (|C| ^ 2) ?_
    filter_upwards with ω
    have hle : |data.coeff i ω| ≤ |C| := le_trans (hC ω) (le_abs_self C)
    simpa [Real.norm_eq_abs, abs_pow] using sq_le_sq.mpr hle
  calc
    predictableSimpleProcessNormSq μ data.toPredictableSimpleProcess =
        ∫ ω, ∑ i,
          (data.coeff i ω) ^ 2 *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) ∂ μ := by
      -- Replace the inner time integral by the fixed-`ω` step-function computation.
      simp [predictableSimpleProcessNormSq_def, PredictableStepRepresentation.timeIntegralSq_eq_sum]
    _ =
        ∑ i, ∫ ω, (data.coeff i ω) ^ 2 *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) ∂ μ := by
      rw [integral_finset_sum]
      intro i hi
      exact (hCoeffSq_integrable i).mul_const _
    _ =
        ∑ i,
          (∫ ω, (data.coeff i ω) ^ 2 ∂ μ) *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [integral_mul_const]

end MeasureTheory
