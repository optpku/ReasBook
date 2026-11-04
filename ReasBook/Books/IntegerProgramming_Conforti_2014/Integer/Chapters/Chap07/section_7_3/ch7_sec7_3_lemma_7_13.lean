/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13.OrderedCover
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13.LiftingFunction

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma713

open scoped BigOperators
open OrderedFlowCover

variable {n : ℕ}
variable (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
variable (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
variable (z : ℝ)

/-- Helper for Lemma 7.13: every entry of an enumerating order belongs to the cover it
enumerates. -/
theorem enumeratedCover_mem_cover
    (hcoverOrder : enumerates C coverOrder)
    (h : Fin C.card) :
    coverOrder h ∈ C := by
  -- Rewrite the set-range enumeration statement at the concrete ordered cover entry.
  have hmem : coverOrder h ∈ Set.range coverOrder := ⟨h, rfl⟩
  rw [enumerates] at hcoverOrder
  rw [hcoverOrder] at hmem
  exact hmem

/-- Helper for Lemma 7.13: `μ_h` is the sum of the first `h` ordered cover weights. -/
theorem partialSum_eq_sum_range_weights
    (h : ℕ) :
    partialSum C a coverOrder h =
      Finset.sum (Finset.range h) (fun i ↦ weight C a coverOrder (i + 1)) := by
  induction h with
  | zero =>
      -- The empty prefix has zero partial sum and zero range sum.
      simp [partialSum]
  | succ h ih =>
      -- Unfold the next ordered coefficient and append the last range term.
      rw [partialSum_succ, ih, Finset.sum_range_succ]

/-- When `coverOrder` enumerates the flow cover `C`, the final ordered partial sum satisfies the
canonical cover-sum identity `μ_|C| = ∑ j ∈ C, a j`. -/
theorem partialSum_card_eq_cover_sum
    (hcoverOrder : enumerates C coverOrder) :
    partialSum C a coverOrder C.card = ∑ j ∈ C, a j := by
  let g : ℕ → ℝ := fun i ↦
    if hi : i < C.card then a (coverOrder ⟨i, hi⟩) else 0
  have hmap : Finset.univ.map coverOrder = C := by
    -- Turn the set-range enumeration hypothesis into the corresponding finite-map identity.
    rw [enumerates] at hcoverOrder
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, -, rfl⟩
      exact enumeratedCover_mem_cover (C := C) (coverOrder := coverOrder) hcoverOrder i
    · intro hj
      have hmem : j ∈ Set.range coverOrder := by
        rw [hcoverOrder]
        exact hj
      rcases hmem with ⟨i, rfl⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc
    partialSum C a coverOrder C.card = ∑ i ∈ Finset.range C.card, g i := by
      -- Rewrite the ordered partial sum as the range sum of the ordered coefficients.
      rw [partialSum_eq_sum_range_weights (C := C) (a := a) (coverOrder := coverOrder) C.card]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt : i < C.card := Finset.mem_range.mp hi
      dsimp [g]
      simp [weight_succ, hi_lt]
    _ = ∑ i : Fin C.card, g i := by
      -- Convert the natural-indexed range sum back to the canonical `Fin` sum.
      symm
      simpa using (Fin.sum_univ_eq_sum_range g C.card)
    _ = ∑ i : Fin C.card, a (coverOrder i) := by
      -- Each `g i` is exactly the ordered coefficient because `i` already lies in the cover range.
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [g]
      have hi_eq : (⟨↑i, i.isLt⟩ : Fin C.card) = i := Fin.ext rfl
      simp [i.isLt, hi_eq]
    _ = ∑ j ∈ Finset.univ.map coverOrder, a j := by
      -- Reindex the full ordered sum by the finite image of `coverOrder`.
      symm
      rw [Finset.sum_map]
    _ = ∑ j ∈ C, a j := by
      simpa [hmap]

/-- When `coverOrder` enumerates the flow cover `C`, the final ordered partial sum satisfies the
source identity `μ_|C| = b + flow_cover_excess a b C`. -/
theorem partialSum_card_eq_rhs_add_excess
    (hcoverOrder : enumerates C coverOrder) :
    partialSum C a coverOrder C.card = b + flow_cover_excess a b C := by
  -- Rewrite `μ_|C|` as the cover sum and then expand the excess parameter.
  rw [partialSum_card_eq_cover_sum (a := a) (C := C) (coverOrder := coverOrder) hcoverOrder]
  rw [flow_cover_excess_eq_sum_sub]
  ring

/-- Helper for Lemma 7.13: every ordered coefficient before the cut index still exceeds the
excess parameter `flow_cover_excess a b C`. -/
theorem coverWeight_gt_excess_before_cutIndex
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh : h < r) :
    flow_cover_excess a b C < weight C a coverOrder (h + 1) := by
  rcases hr with ⟨hr_pos, hr_le_card, hr_gt, _⟩
  have hh_lt_card : h < C.card := lt_of_lt_of_le hh hr_le_card
  have hpred_lt_card : r - 1 < C.card := by
    exact lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hr_pos)) hr_le_card
  have hr_gt' : flow_cover_excess a b C < a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
    -- Rewrite the cut-index witness `weight r` into the underlying ordered coefficient.
    have hweight_r :
        weight C a coverOrder r = a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
      have htmp := weight_succ C a coverOrder (h := r - 1) hpred_lt_card
      have hr_eq : (r - 1) + 1 = r := Nat.sub_add_cancel hr_pos
      simpa [hr_eq] using htmp
    rw [hweight_r] at hr_gt
    exact hr_gt
  have hmono :
      a (coverOrder ⟨r - 1, hpred_lt_card⟩) ≤ a (coverOrder ⟨h, hh_lt_card⟩) := by
    -- Antitonicity moves the strict cut-index inequality backward along the order.
    exact hordered (Nat.le_pred_of_lt hh)
  rw [weight_succ _ _ _ hh_lt_card]
  linarith

/-- Helper for Lemma 7.13: a nonnegative finite weight vector with total at least `d` contains a
bounded nonnegative subvector summing exactly to `d`. -/
theorem boundedSum_exists
    {t : ℕ} (w : Fin t → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) {d : ℝ}
    (hd_nonneg : 0 ≤ d) (hd_le : d ≤ ∑ i, w i) :
    ∃ y : Fin t → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, y i ≤ w i) ∧ ∑ i, y i = d := by
  revert d
  induction t with
  | zero =>
      intro d hd_nonneg hd_le
      -- In the empty case the only possible target sum is `0`.
      have hd_le_zero : d ≤ 0 := by
        simpa using hd_le
      have hd_zero : d = 0 := by
        linarith
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simpa [hd_zero]
  | succ t ih =>
      intro d hd_nonneg hd_le
      let front : Fin t → ℝ := fun i ↦ w i.castSucc
      let frontSum : ℝ := ∑ i : Fin t, front i
      have htotal :
          ∑ i : Fin (t + 1), w i = frontSum + w (Fin.last t) := by
        -- Split the sum into the first `t` coordinates and the last coordinate.
        simp [front, frontSum, Fin.sum_univ_castSucc]
      by_cases hfront : d ≤ frontSum
      · obtain ⟨yFront, hyFront_nonneg, hyFront_le, hyFront_sum⟩ :=
          ih
            (fun i ↦ w i.castSucc)
            (by
              intro i
              exact hw_nonneg i.castSucc)
            hd_nonneg
            hfront
        refine ⟨Fin.snoc yFront 0, ?_, ?_, ?_⟩
        · -- Keep the recursive fill on the front coordinates and set the last coordinate to `0`.
          intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simp
          · simpa [Fin.snoc_castSucc] using hyFront_nonneg j
        · -- The front coordinates stay bounded by the recursion, and the last one is trivial.
          intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · have hw_last_nonneg : 0 ≤ w (Fin.last t) := hw_nonneg (Fin.last t)
            simpa [Fin.snoc_last] using hw_last_nonneg
          · simpa [Fin.snoc_castSucc] using hyFront_le j
        · -- The sum is unchanged because the new last coordinate is zero.
          simp [Fin.sum_univ_castSucc, hyFront_sum]
      · have hfront_lt : frontSum < d := lt_of_not_ge hfront
        have hres_nonneg : 0 ≤ d - frontSum := by
          linarith
        have hres_le_last : d - frontSum ≤ w (Fin.last t) := by
          rw [htotal] at hd_le
          linarith
        refine ⟨Fin.snoc (fun i ↦ w i.castSucc) (d - frontSum), ?_, ?_, ?_⟩
        · -- Use the original front weights and put the residual demand on the last coordinate.
          intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simpa using hres_nonneg
          · simpa [Fin.snoc_castSucc] using hw_nonneg j.castSucc
        · -- The front coordinates are tight, and the last coordinate is bounded by the tail weight.
          intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simpa [Fin.snoc_last, frontSum] using hres_le_last
          · simp [Fin.snoc_castSucc]
        · -- The front sum plus the residual last coordinate adds back up to `d`.
          simp [front, frontSum, Fin.sum_univ_castSucc]

/-- Helper for Lemma 7.13: the penalty contribution of the first `k` ordered cover positions is
`μ_k - k λ`. -/
theorem prefixPenaltySum_eq
    (lam : ℝ) {k : ℕ} (hk : k ≤ C.card) :
    (∑ i : Fin C.card, if i.1 < k then a (coverOrder i) - lam else 0) =
      partialSum C a coverOrder k - (k : ℝ) * lam := by
  let guarded : ℕ → ℝ := fun i ↦
    if hi : i < C.card then
      if i < k then a (coverOrder ⟨i, hi⟩) - lam else 0
    else 0
  let orderedCoeff : ℕ → ℝ := fun i ↦
    if hi : i < C.card then a (coverOrder ⟨i, hi⟩) else 0
  have hprefix :
      ∑ i ∈ Finset.range k, orderedCoeff i = partialSum C a coverOrder k := by
    -- The first `k` ordered coefficients sum to `μ_k`.
    rw [partialSum_eq_sum_range_weights (C := C) (a := a) (coverOrder := coverOrder) k]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have hi_card : i < C.card := lt_of_lt_of_le hi_lt hk
    dsimp [orderedCoeff]
    simp [weight_succ, hi_lt, hi_card]
  calc
    (∑ i : Fin C.card, if i.1 < k then a (coverOrder i) - lam else 0) =
        ∑ i ∈ Finset.range C.card, guarded i := by
      -- Expand the `Fin` sum into a guarded range sum over natural indices.
      trans ∑ i : Fin C.card, guarded i
      · apply Finset.sum_congr rfl
        intro i hi
        dsimp [guarded]
        have hi_eq : (⟨↑i, i.isLt⟩ : Fin C.card) = i := Fin.ext rfl
        simp [i.isLt, hi_eq]
      · simpa using (Fin.sum_univ_eq_sum_range guarded C.card)
    _ = ∑ i ∈ Finset.range k, guarded i := by
      -- Outside the prefix `range k` every guarded summand is zero.
      rw [← Finset.sum_subset
        (s₁ := Finset.range k)
        (s₂ := Finset.range C.card)
        (by
          intro i hi
          exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))]
      intro i _ hi_not_mem
      dsimp [guarded]
      have hnotlt : ¬ i < k := by
        intro hik
        exact hi_not_mem (Finset.mem_range.mpr hik)
      by_cases hi_card : i < C.card
      · simp [hi_card, hnotlt]
      · simp [hi_card]
    _ = ∑ i ∈ Finset.range k, (orderedCoeff i - lam) := by
      -- Inside `range k` the outer guard and the prefix guard are both active.
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt : i < k := Finset.mem_range.mp hi
      have hi_card : i < C.card := lt_of_lt_of_le hi_lt hk
      dsimp [guarded, orderedCoeff]
      simp [hi_lt, hi_card]
    _ = ∑ i ∈ Finset.range k, orderedCoeff i - ∑ i ∈ Finset.range k, lam := by
      -- Separate the coefficient sum from the constant penalty contribution.
      rw [Finset.sum_sub_distrib]
    _ = partialSum C a coverOrder k - (k : ℝ) * lam := by
      -- The first part is `μ_k`, and the second is exactly `k` copies of `λ`.
      rw [hprefix]
      simp

/-- Helper for Lemma 7.13: zeroing the first `k` ordered positions leaves exactly the tail
capacity `μ_|C| - μ_k`. -/
theorem suffixCapacity_eq_partialSum_sub
    {k : ℕ} (hk : k ≤ C.card) :
    (∑ i : Fin C.card, if k ≤ i.1 then a (coverOrder i) else 0) =
      partialSum C a coverOrder C.card - partialSum C a coverOrder k := by
  have hfull :
      (∑ i : Fin C.card, a (coverOrder i)) = partialSum C a coverOrder C.card := by
    -- Specializing the prefix identity to `λ = 0` and `k = |C|` recovers the full ordered sum.
    simpa using
      (prefixPenaltySum_eq
        (a := a) (C := C) (coverOrder := coverOrder) (lam := (0 : ℝ))
        (k := C.card) (hk := le_rfl))
  have hprefix :
      (∑ i : Fin C.card, if i.1 < k then a (coverOrder i) else 0) =
        partialSum C a coverOrder k := by
    -- The same `λ = 0` specialization gives the prefix capacity sum `μ_k`.
    simpa using
      (prefixPenaltySum_eq
        (a := a) (C := C) (coverOrder := coverOrder) (lam := (0 : ℝ))
        (k := k) (hk := hk))
  calc
    (∑ i : Fin C.card, if k ≤ i.1 then a (coverOrder i) else 0) =
        ∑ i : Fin C.card, (a (coverOrder i) - if i.1 < k then a (coverOrder i) else 0) := by
      -- Each ordered coefficient splits into its prefix part and its tail part.
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : i.1 < k
      · simp [hik, Nat.not_le_of_lt hik]
      · have hk_le_i : k ≤ i.1 := Nat.le_of_not_gt hik
        simp [hik, hk_le_i]
    _ = (∑ i : Fin C.card, a (coverOrder i)) -
          (∑ i : Fin C.card, if i.1 < k then a (coverOrder i) else 0) := by
      -- Sum the pointwise decomposition over the full ordered cover.
      rw [Finset.sum_sub_distrib]
    _ = partialSum C a coverOrder C.card - partialSum C a coverOrder k := by
      -- Replace the full and prefix ordered sums by their `μ`-formulas.
      rw [hfull, hprefix]

/-- Helper for Lemma 7.13: the capacity captured by a Boolean selector after fixing the ordered
cover coefficients. -/
def selectorCapacity
    {t : ℕ} (a : Fin t → ℝ) (x : Fin t → Bool) : ℝ :=
  ∑ i, a i * (if x i then (1 : ℝ) else 0)

/-- Helper for Lemma 7.13: the flow-cover penalty paid by the coordinates a selector leaves off. -/
def selectorPenalty
    {t : ℕ} (lam : ℝ) (a : Fin t → ℝ) (x : Fin t → Bool) : ℝ :=
  ∑ i, max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0)

/-- Helper for Lemma 7.13: the selector-only objective obtained after maximizing over feasible
`y` for a fixed Boolean selector `x`. -/
def selectorObjective
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) (x : Fin t → Bool) : ℝ :=
  min (b - z) (selectorCapacity a x) + selectorPenalty lam a x

/-- Helper for Lemma 7.13: the threshold selector with cutoff `k` turns off the first `k`
ordered positions and turns on every later one. -/
def thresholdSelector
    {t : ℕ} (k : ℕ) : Fin t → Bool :=
  fun i ↦ decide (k ≤ i.1)

/-- Helper for Lemma 7.13: every feasible witness value is bounded above by the selector-only
objective attached to the same Boolean selector. -/
theorem objectiveValue_le_selectorObjective
    {t : ℕ} {b lam z v : ℝ} {a : Fin t → ℝ}
    (hv : v ∈ flow_cover_lifting_objective_values b lam a z) :
    ∃ x, v ≤ selectorObjective b lam a z x := by
  rcases (mem_flow_cover_lifting_objective_values_iff b lam a z v).1 hv with
    ⟨x, y, hy_nonneg, hy_sum, hy_cap, hv_eq⟩
  refine ⟨x, ?_⟩
  have hy_sum_le_capacity : ∑ i : Fin t, y i ≤ selectorCapacity a x := by
    -- Summing the coordinate bounds compares the feasible fill with the selected capacity.
    unfold selectorCapacity
    exact Finset.sum_le_sum fun i _ ↦ hy_cap i
  have hy_sum_le_min :
      ∑ i : Fin t, y i ≤ min (b - z) (selectorCapacity a x) :=
    le_min hy_sum hy_sum_le_capacity
  -- Replace the original objective by the selector-only value using the two sum bounds.
  calc
    v = (∑ i : Fin t, y i) +
          ∑ i : Fin t,
            max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0) := by
          rw [hv_eq, Finset.sum_add_distrib]
    _ ≤ min (b - z) (selectorCapacity a x) +
          ∑ i : Fin t,
            max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0) := by
          gcongr
    _ = selectorObjective b lam a z x := by
          rw [selectorObjective, selectorPenalty]

/-- Helper for Lemma 7.13: every selector objective is realized by some feasible `y` whose total
fill is exactly the corresponding clipped capacity. -/
theorem selectorObjective_mem
    {t : ℕ} {b lam z : ℝ} {a : Fin t → ℝ}
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hd_nonneg : 0 ≤ b - z)
    (x : Fin t → Bool) :
    selectorObjective b lam a z x ∈ flow_cover_lifting_objective_values b lam a z := by
  let w : Fin t → ℝ := fun i ↦ a i * (if x i then (1 : ℝ) else 0)
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    by_cases hxi : x i
    · simp [w, hxi, ha_nonneg i]
    · simp [w, hxi]
  have hcapacity_nonneg : 0 ≤ ∑ i : Fin t, w i :=
    Finset.sum_nonneg fun i _ ↦ hw_nonneg i
  have htarget_nonneg :
      0 ≤ min (b - z) (∑ i : Fin t, w i) :=
    le_min hd_nonneg hcapacity_nonneg
  obtain ⟨y, hy_nonneg, hy_le, hy_sum⟩ :=
    boundedSum_exists
      (w := w)
      hw_nonneg
      htarget_nonneg
      (min_le_right _ _)
  have hy_sum_le_rhs : (∑ i : Fin t, y i) ≤ b - z := by
    rw [hy_sum]
    exact min_le_left _ _
  refine (mem_flow_cover_lifting_objective_values_iff b lam a z
      (selectorObjective b lam a z x)).2 ?_
  refine ⟨x, y, hy_nonneg, hy_sum_le_rhs, ?_, ?_⟩
  · -- Each constructed fill stays below the selected capacity on its coordinate.
    intro i
    simpa [w] using hy_le i
  · have hy_sum' :
        ∑ i : Fin t, y i = min (b - z) (selectorCapacity a x) := by
      simpa [selectorCapacity, w] using hy_sum
    -- Substitute the exact clipped fill sum back into the objective formula.
    calc
      selectorObjective b lam a z x
          = (∑ i : Fin t, y i) + selectorPenalty lam a x := by
              rw [selectorObjective, hy_sum']
      _ =
          ∑ i : Fin t,
            (y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0)) := by
              rw [selectorPenalty, Finset.sum_add_distrib]

/-- Helper for Lemma 7.13: the objective-value set is always bounded above by the residual demand
plus the total positive-part penalty. -/
theorem flow_cover_lifting_objective_values_bddAbove
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) :
    BddAbove (flow_cover_lifting_objective_values b lam a z) := by
  refine ⟨(b - z) + ∑ i : Fin t, max (a i - lam) 0, ?_⟩
  intro v hv
  rcases (mem_flow_cover_lifting_objective_values_iff b lam a z v).1 hv with
    ⟨x, y, hy_nonneg, hy_sum, hy_cap, hv_eq⟩
  have hpenalty_le :
      (∑ i : Fin t,
          max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0)) ≤
        ∑ i : Fin t, max (a i - lam) 0 := by
    -- Each selector factor is either `0` or `1`, so the penalty never exceeds the full sum.
    refine Finset.sum_le_sum ?_
    intro i hi
    cases hxi : x i <;> simp [hxi]
  -- Bound the feasible fill by `b - z` and the penalty by the total positive-part sum.
  rw [hv_eq, Finset.sum_add_distrib]
  linarith

/-- Helper for Lemma 7.13: evaluating the selector objective on a threshold selector rewrites the
capacity part to a tail sum and the penalty part to the prefix formula `μ_k - k λ`. -/
theorem thresholdSelector_objective_eq
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {k : ℕ} (hk : k ≤ r) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) k) =
      min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder k) +
        (partialSum C a coverOrder k - (k : ℝ) * flow_cover_excess a b C) := by
  have hk_card : k ≤ C.card := le_trans hk hr.2.1
  have hcapacity :
      selectorCapacity (a ∘ coverOrder) (thresholdSelector (t := C.card) k) =
        ∑ i : Fin C.card, if k ≤ i.1 then a (coverOrder i) else 0 := by
    -- The threshold selector keeps exactly the tail coordinates from `k` onward.
    unfold selectorCapacity thresholdSelector
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hik : k ≤ i.1
    · simp [hik, Function.comp]
    · simp [hik, Function.comp]
  have hpenalty :
      selectorPenalty (flow_cover_excess a b C) (a ∘ coverOrder)
          (thresholdSelector (t := C.card) k) =
        ∑ i : Fin C.card,
          if i.1 < k then a (coverOrder i) - flow_cover_excess a b C else 0 := by
    -- Because `k ≤ r`, every penalized threshold coordinate still lies before the cut index.
    unfold selectorPenalty thresholdSelector
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hik : i.1 < k
    · have hir : i.1 < r := lt_of_lt_of_le hik hk
      have hlt :
          flow_cover_excess a b C < a (coverOrder i) := by
        simpa [weight_succ C a coverOrder i.isLt] using
          coverWeight_gt_excess_before_cutIndex
            (a := a)
            (b := b)
            (C := C)
            (coverOrder := coverOrder)
            (r := r)
            hordered
            hr
            (h := i.1)
            hir
      have hmax :
          max (a (coverOrder i) - flow_cover_excess a b C) 0 =
            a (coverOrder i) - flow_cover_excess a b C := by
        rw [max_eq_left]
        linarith
      have hnotle : ¬ k ≤ i.1 := Nat.not_le_of_lt hik
      simp [Function.comp, hik, hnotle, hmax]
    · have hk_le_i : k ≤ i.1 := Nat.le_of_not_gt hik
      simp [Function.comp, hik, hk_le_i]
  -- Replace the threshold capacity and penalty by the ordered partial-sum identities.
  rw [selectorObjective, hcapacity, hpenalty]
  rw [suffixCapacity_eq_partialSum_sub
    (a := a) (C := C) (coverOrder := coverOrder) (k := k) hk_card]
  rw [prefixPenaltySum_eq
    (a := a)
    (C := C)
    (coverOrder := coverOrder)
    (lam := flow_cover_excess a b C)
    (k := k)
    hk_card]

/-- Helper for Lemma 7.13: the source witness with cutoff `h + 1` realizes the constant-piece
objective value `b - h λ`. -/
theorem constantInterval_thresholdSelector_objective_eq
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h' : Fin C.card ↦ a (coverOrder h'))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C)) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) (h + 1)) =
      b - (h : ℝ) * flow_cover_excess a b C := by
  have hk : h + 1 ≤ r := Nat.succ_le_of_lt hh
  have hcard :
      partialSum C a coverOrder C.card = b + flow_cover_excess a b C := by
    -- Rewrite the full ordered sum to the source identity `μ_|C| = b + λ`.
    simpa using
      partialSum_card_eq_rhs_add_excess
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        hcoverOrder
  have htail_le_demand :
      partialSum C a coverOrder C.card - partialSum C a coverOrder (h + 1) ≤ b - z := by
    -- On a constant interval the residual demand dominates the threshold tail capacity.
    rw [hcard]
    linarith [hzpiece.2]
  -- Evaluate the threshold selector and force the `min` onto the tail-capacity branch.
  rw [thresholdSelector_objective_eq
    (a := a)
    (b := b)
    (C := C)
    (coverOrder := coverOrder)
    (r := r)
    (z := z)
    hordered
    hr
    hk]
  rw [min_eq_right htail_le_demand, hcard]
  calc
    b + flow_cover_excess a b C - partialSum C a coverOrder (h + 1) +
        (partialSum C a coverOrder (h + 1) - ↑(h + 1) * flow_cover_excess a b C)
        = b + flow_cover_excess a b C - ↑(h + 1) * flow_cover_excess a b C := by ring
    _ = b - (h : ℝ) * flow_cover_excess a b C := by
          have hsucc : ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by
            exact_mod_cast Nat.succ_eq_add_one h
          rw [hsucc]
          ring

/-- Helper for Lemma 7.13: the source witness with cutoff `h` realizes the gap-piece objective
value `b - z + μ_h - h λ`. -/
theorem gapInterval_thresholdSelector_objective_eq
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h' : Fin C.card ↦ a (coverOrder h'))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh₂ : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h - flow_cover_excess a b C)
        (partialSum C a coverOrder h)) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) h) =
      b - z + partialSum C a coverOrder h - (h : ℝ) * flow_cover_excess a b C := by
  have hk : h ≤ r := Nat.le_of_lt hh₂
  have hcard :
      partialSum C a coverOrder C.card = b + flow_cover_excess a b C := by
    simpa using
      partialSum_card_eq_rhs_add_excess
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        hcoverOrder
  have hdemand_le_tail :
      b - z ≤ partialSum C a coverOrder C.card - partialSum C a coverOrder h := by
    rw [hcard]
    linarith [hzpiece.1]
  -- On a gap interval the residual demand fits inside the threshold tail capacity.
  rw [thresholdSelector_objective_eq
    (a := a)
    (b := b)
    (C := C)
    (coverOrder := coverOrder)
    (r := r)
    (z := z)
    hordered
    hr
    hk]
  rw [min_eq_left hdemand_le_tail]
  ring

/-- Helper for Lemma 7.13: a finite set of ordered cover positions with values all below `m`
contains at most `m` elements. -/
theorem card_le_of_val_lt
    {m : ℕ} (K : Finset (Fin C.card))
    (hK : ∀ i ∈ K, i.1 < m) :
    K.card ≤ m := by
  classical
  let f : ↥K → Fin m := fun i ↦ ⟨i.1.1, hK i.1 i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun x : Fin m ↦ x.1) hij
  -- Inject the subtype of `K` into `Fin m` and compare cardinalities.
  simpa [f, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Helper for Lemma 7.13: among the ordered cover coefficients, the sum over any finite subset is
at most the sum of the first `|K|` ordered coefficients. -/
theorem orderedSubsetSum_le_partialSum_card
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (K : Finset (Fin C.card)) :
    Finset.sum K (fun i ↦ a (coverOrder i)) ≤ partialSum C a coverOrder K.card := by
  classical
  refine Finset.strongInductionOn K ?_
  intro K ih
  by_cases hK : K.Nonempty
  · let m : Fin C.card := K.max' hK
    let K' : Finset (Fin C.card) := K.erase m
    have hm_mem : m ∈ K := by
      -- Record the maximal selected index so the induction can peel it off.
      exact Finset.max'_mem K hK
    have hK'_ssub : K' ⊂ K := by
      simpa [K'] using Finset.erase_ssubset hm_mem
    have hsum_split :
        Finset.sum K (fun i ↦ a (coverOrder i)) =
          Finset.sum K' (fun i ↦ a (coverOrder i)) + a (coverOrder m) := by
      -- Split the subset sum into the erased remainder plus the maximal term.
      simp [K', hm_mem, Finset.sum_erase_add]
    have hK'_bound :
        Finset.sum K' (fun i ↦ a (coverOrder i)) ≤ partialSum C a coverOrder K'.card := by
      exact ih K' hK'_ssub
    have hcard_le_card : K.card ≤ C.card := by
      simpa using Finset.card_le_univ K
    have hKcard_pos : 0 < K.card := Finset.card_pos.mpr hK
    have hK'_card : K'.card = K.card - 1 := by
      simp [K', hm_mem]
    have hK'_card_succ : K'.card + 1 = K.card := by
      rw [hK'_card]
      omega
    have hK'_lt_card : K'.card < C.card := by
      have hsucc_le : K'.card + 1 ≤ C.card := by
        simpa [hK'_card_succ] using hcard_le_card
      exact lt_of_lt_of_le (Nat.lt_succ_self K'.card) hsucc_le
    have hall_lt_succ : ∀ i ∈ K, i.1 < m.1 + 1 := by
      intro i hi
      exact Nat.lt_succ_of_le <| show i.1 ≤ m.1 from by
        exact Fin.val_le_of_le (Finset.le_max' K i hi)
    have hcard_le_succ : K.card ≤ m.1 + 1 := by
      -- A subset of values below `m + 1` has at most `m + 1` elements.
      exact card_le_of_val_lt (C := C) (K := K) hall_lt_succ
    have hK'_le_m : K'.card ≤ m.1 := by
      have hsucc_le : K'.card + 1 ≤ m.1 + 1 := by
        simpa [hK'_card_succ] using hcard_le_succ
      exact Nat.succ_le_succ_iff.mp hsucc_le
    let i0 : Fin C.card := ⟨K'.card, hK'_lt_card⟩
    have hmono :
        a (coverOrder m) ≤ a (coverOrder i0) := by
      -- The maximal selected index lies at or after the last index of the initial segment.
      exact hordered (show i0 ≤ m from hK'_le_m)
    have hstep :
        partialSum C a coverOrder K.card =
          partialSum C a coverOrder K'.card + a (coverOrder i0) := by
      -- The next partial sum adds exactly the ordered coefficient at position `K'.card + 1`.
      rw [← hK'_card_succ, partialSum_succ, weight_succ C a coverOrder hK'_lt_card]
    calc
      Finset.sum K (fun i ↦ a (coverOrder i))
          = Finset.sum K' (fun i ↦ a (coverOrder i)) + a (coverOrder m) := hsum_split
      _ ≤ partialSum C a coverOrder K'.card + a (coverOrder i0) := by
            linarith
      _ = partialSum C a coverOrder K.card := by
            rw [hstep]
  · have hK_empty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    -- The empty subset contributes zero on both sides.
    simp [hK_empty, partialSum]

/-- Helper for Lemma 7.13: increasing omitted ordered mass can only increase the clipped
profile `min d (T - O) + O`. -/
theorem min_sub_add_monotone
    {d T u v : ℝ} (huv : u ≤ v) :
    min d (T - u) + u ≤ min d (T - v) + v := by
  by_cases hv : d ≤ T - v
  · have hu : d ≤ T - u := by
      linarith
    -- When both clips are inactive, the profile grows exactly with the omitted mass.
    rw [min_eq_left hu, min_eq_left hv]
    linarith
  · have hv' : T - v < d := lt_of_not_ge hv
    calc
      min d (T - u) + u ≤ (T - u) + u := by
            gcongr
            exact min_le_right _ _
      _ = T := by ring
      _ = min d (T - v) + v := by
            rw [min_eq_right (le_of_lt hv')]
            ring

/-- Helper for Lemma 7.13: the capacity part of the ordered prefix sums is monotone when the
ordered coefficients are nonnegative. -/
theorem partialSum_mono_of_nonneg
    (ha_nonneg : ∀ j, 0 ≤ a j)
    {k h : ℕ} (hkh : k ≤ h) (hh_card : h ≤ C.card) :
    partialSum C a coverOrder k ≤ partialSum C a coverOrder h := by
  have hk_card : k ≤ C.card := le_trans hkh hh_card
  have hk_sum :
      partialSum C a coverOrder k =
        ∑ i : Fin C.card, if i.1 < k then a (coverOrder i) else 0 := by
    -- Specialize the guarded prefix identity to `λ = 0` at the shorter prefix.
    simpa using
      (prefixPenaltySum_eq
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        (lam := (0 : ℝ))
        (k := k)
        hk_card).symm
  have hh_sum :
      partialSum C a coverOrder h =
        ∑ i : Fin C.card, if i.1 < h then a (coverOrder i) else 0 := by
    -- Do the same for the longer prefix and compare the two guarded sums pointwise.
    simpa using
      (prefixPenaltySum_eq
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        (lam := (0 : ℝ))
        (k := h)
        hh_card).symm
  rw [hk_sum, hh_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hik : i.1 < k
  · have hih : i.1 < h := lt_of_lt_of_le hik hkh
    simp [hik, hih]
  · by_cases hih : i.1 < h
    · simp [hik, hih, ha_nonneg (coverOrder i)]
    · simp [hik, hih]

/-- Helper for Lemma 7.13: before the cut index, the source expression `μ_k - k λ` is monotone in
`k`. -/
theorem partialSum_sub_card_mul_excess_mono_before_cutIndex
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {k h : ℕ} (hkh : k ≤ h) (hh : h < r) :
    partialSum C a coverOrder k - (k : ℝ) * flow_cover_excess a b C ≤
      partialSum C a coverOrder h - (h : ℝ) * flow_cover_excess a b C := by
  have hh_card : h ≤ C.card := le_trans (Nat.le_of_lt hh) hr.2.1
  have hk_card : k ≤ C.card := le_trans hkh hh_card
  rw [← prefixPenaltySum_eq
    (a := a)
    (C := C)
    (coverOrder := coverOrder)
    (lam := flow_cover_excess a b C)
    (k := k)
    hk_card]
  rw [← prefixPenaltySum_eq
    (a := a)
    (C := C)
    (coverOrder := coverOrder)
    (lam := flow_cover_excess a b C)
    (k := h)
    hh_card]
  -- Compare the guarded prefix sums pointwise before the cut index.
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hik : i.1 < k
  · have hih : i.1 < h := lt_of_lt_of_le hik hkh
    simp [hik, hih]
  · by_cases hih : i.1 < h
    · have hir : i.1 < r := lt_of_lt_of_le hih (Nat.le_of_lt hh)
      have hlt :
          flow_cover_excess a b C < a (coverOrder i) := by
        simpa [weight_succ C a coverOrder i.isLt] using
          coverWeight_gt_excess_before_cutIndex
            (a := a)
            (b := b)
            (C := C)
            (coverOrder := coverOrder)
            (r := r)
            hordered
            hr
            (h := i.1)
            hir
      have hnonneg : 0 ≤ a (coverOrder i) - flow_cover_excess a b C := by
        linarith
      simp [hik, hih, hnonneg]
    · simp [hik, hih]

/-- Helper for Lemma 7.13: every selector objective is bounded above by the omitted-prefix profile
that records only the false positions before the cut index. -/
theorem selectorObjective_le_falsePrefixProfile
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (x : Fin C.card → Bool) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z x ≤
      let K : Finset (Fin C.card) :=
        Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
      let O : ℝ := Finset.sum K (fun i ↦ a (coverOrder i))
      min (b - z) (partialSum C a coverOrder C.card - O) +
        (O - (K.card : ℝ) * flow_cover_excess a b C) := by
  let lam := flow_cover_excess a b C
  let K : Finset (Fin C.card) :=
    Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
  let O : ℝ := Finset.sum K (fun i ↦ a (coverOrder i))
  have hfull :
      partialSum C a coverOrder C.card = ∑ i : Fin C.card, a (coverOrder i) := by
    -- The full ordered partial sum is the sum of all ordered cover coefficients.
    simpa using
      (prefixPenaltySum_eq
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        (lam := (0 : ℝ))
        (k := C.card)
        (hk := le_rfl)).symm
  have hO_sum :
      O = ∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) else 0 := by
    -- Rewrite the omitted-prefix mass as a full guarded sum over the ordered cover.
    dsimp [O, K]
    simp [Finset.sum_filter]
  have hcapacity_le :
      selectorCapacity (a ∘ coverOrder) x ≤ partialSum C a coverOrder C.card - O := by
    have hcap_guarded :
        selectorCapacity (a ∘ coverOrder) x ≤
          ∑ i : Fin C.card,
            (a (coverOrder i) -
              if i.1 < r ∧ x i = false then a (coverOrder i) else 0) := by
      -- A selected coordinate contributes at most the full coefficient minus the omitted-prefix loss.
      unfold selectorCapacity
      refine Finset.sum_le_sum ?_
      intro i hi
      by_cases hir : i.1 < r <;> cases hxi : x i <;>
        simp [Function.comp, hir, hxi, ha_nonneg (coverOrder i)]
    calc
      selectorCapacity (a ∘ coverOrder) x
          ≤ ∑ i : Fin C.card,
              (a (coverOrder i) -
                if i.1 < r ∧ x i = false then a (coverOrder i) else 0) := hcap_guarded
      _ = (∑ i : Fin C.card, a (coverOrder i)) -
            ∑ i : Fin C.card,
              if i.1 < r ∧ x i = false then a (coverOrder i) else 0 := by
            rw [Finset.sum_sub_distrib]
      _ = partialSum C a coverOrder C.card - O := by
            rw [← hfull, ← hO_sum]
  have hpenalty_eq :
      selectorPenalty lam (a ∘ coverOrder) x = O - (K.card : ℝ) * lam := by
    have hpenalty_split :
        (∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) - lam else 0) =
          (∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) else 0) -
            ∑ i : Fin C.card, if i.1 < r ∧ x i = false then lam else 0 := by
      calc
        (∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) - lam else 0)
            = ∑ i : Fin C.card,
                ((if i.1 < r ∧ x i = false then a (coverOrder i) else 0) -
                  (if i.1 < r ∧ x i = false then lam else 0)) := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hix : i.1 < r ∧ x i = false <;> simp [hix]
        _ = (∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) else 0) -
              ∑ i : Fin C.card, if i.1 < r ∧ x i = false then lam else 0 := by
                rw [Finset.sum_sub_distrib]
    have hlam_sum :
        (∑ i : Fin C.card, if i.1 < r ∧ x i = false then lam else 0) =
          (K.card : ℝ) * lam := by
      calc
        (∑ i : Fin C.card, if i.1 < r ∧ x i = false then lam else 0)
            = Finset.sum K (fun _ ↦ lam) := by
                dsimp [K]
                simpa using
                  (Finset.sum_filter
                    (s := Finset.univ)
                    (f := fun _ : Fin C.card ↦ lam)
                    (p := fun i : Fin C.card ↦ i.1 < r ∧ x i = false)).symm
        _ = (K.card : ℝ) * lam := by
              simp
    have hpenalty_guarded :
        selectorPenalty lam (a ∘ coverOrder) x =
          ∑ i : Fin C.card,
            if i.1 < r ∧ x i = false then a (coverOrder i) - lam else 0 := by
      -- Before the cut index a false selector pays `a_i - λ`, and after the cut index the penalty vanishes.
      unfold selectorPenalty
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hir : i.1 < r
      · have hlt :
          lam < a (coverOrder i) := by
          simpa [lam, weight_succ C a coverOrder i.isLt] using
            coverWeight_gt_excess_before_cutIndex
              (a := a)
              (b := b)
              (C := C)
              (coverOrder := coverOrder)
              (r := r)
              hordered
              hr
              (h := i.1)
              hir
        have hmax :
            max (a (coverOrder i) - lam) 0 = a (coverOrder i) - lam := by
          rw [max_eq_left]
          linarith
        cases hxi : x i <;> simp [Function.comp, hir, hxi, hmax]
      · have hir' : r ≤ i.1 := Nat.le_of_not_gt hir
        have htail :
            weight C a coverOrder (i.1 + 1) ≤ lam := by
          exact hr.2.2.2 (i.1 + 1) (lt_of_le_of_lt hir' (Nat.lt_succ_self _))
            (Nat.succ_le_of_lt i.isLt)
        have hmax :
            max (a (coverOrder i) - lam) 0 = 0 := by
          rw [max_eq_right]
          have hle : a (coverOrder i) ≤ lam := by
            simpa [lam, weight_succ C a coverOrder i.isLt] using htail
          linarith
        cases hxi : x i <;> simp [Function.comp, hir, hxi, hmax]
    calc
      selectorPenalty lam (a ∘ coverOrder) x
          = ∑ i : Fin C.card,
              if i.1 < r ∧ x i = false then a (coverOrder i) - lam else 0 := hpenalty_guarded
      _ = (∑ i : Fin C.card, if i.1 < r ∧ x i = false then a (coverOrder i) else 0) -
            ∑ i : Fin C.card, if i.1 < r ∧ x i = false then lam else 0 := hpenalty_split
      _ = O - (K.card : ℝ) * lam := by
            rw [← hO_sum, hlam_sum]
  have hprofile :
      selectorObjective b lam (a ∘ coverOrder) z x ≤
        min (b - z) (partialSum C a coverOrder C.card - O) +
          (O - (K.card : ℝ) * lam) := by
    -- Replace the selector capacity and penalty by the scalar omitted-prefix profile.
    calc
      selectorObjective b lam (a ∘ coverOrder) z x
          = min (b - z) (selectorCapacity (a ∘ coverOrder) x) +
              selectorPenalty lam (a ∘ coverOrder) x := by
                rw [selectorObjective]
      _ ≤ min (b - z) (partialSum C a coverOrder C.card - O) +
            selectorPenalty lam (a ∘ coverOrder) x := by
              gcongr
      _ = min (b - z) (partialSum C a coverOrder C.card - O) +
            (O - (K.card : ℝ) * lam) := by
              rw [hpenalty_eq]
  dsimp [lam, K, O] at hprofile ⊢
  exact hprofile

/-- Helper for Lemma 7.13: every selector is dominated by the threshold selector with the same
number of false before-cut positions. -/
theorem selectorObjective_le_thresholdByFalsePrefixCount
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (x : Fin C.card → Bool) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z x ≤
      let K : Finset (Fin C.card) :=
        Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
      selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) K.card) := by
  let lam := flow_cover_excess a b C
  let K : Finset (Fin C.card) :=
    Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
  let O : ℝ := Finset.sum K (fun i ↦ a (coverOrder i))
  have hK_lt : ∀ i ∈ K, i.1 < r := by
    intro i hi
    simpa [K] using (Finset.mem_filter.mp hi).2.1
  have hK_card : K.card ≤ r := by
    exact card_le_of_val_lt (C := C) (K := K) hK_lt
  have hO_le : O ≤ partialSum C a coverOrder K.card := by
    -- The omitted-prefix mass is dominated by the first `|K|` ordered coefficients.
    simpa [O] using
      orderedSubsetSum_le_partialSum_card
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        hordered
        K
  have hprofile_le :
      min (b - z) (partialSum C a coverOrder C.card - O) +
          (O - (K.card : ℝ) * lam) ≤
        min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder K.card) +
          (partialSum C a coverOrder K.card - (K.card : ℝ) * lam) := by
    -- Increasing the omitted mass can only increase the scalar profile.
    have hbase :=
      min_sub_add_monotone
        (d := b - z)
        (T := partialSum C a coverOrder C.card)
        (u := O)
        (v := partialSum C a coverOrder K.card)
        hO_le
    linarith
  -- Route correction: the selector-to-threshold comparison is now a corollary of the scalar
  -- profile bound instead of the primary normalization theorem.
  calc
    selectorObjective b lam (a ∘ coverOrder) z x
        ≤ min (b - z) (partialSum C a coverOrder C.card - O) +
            (O - (K.card : ℝ) * lam) := by
              simpa [lam, K, O] using
                selectorObjective_le_falsePrefixProfile
                  (a := a)
                  (b := b)
                  (C := C)
                  (coverOrder := coverOrder)
                  (r := r)
                  (z := z)
                  ha_nonneg
                  hordered
                  hr
                  x
    _ ≤ min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder K.card) +
          (partialSum C a coverOrder K.card - (K.card : ℝ) * lam) := hprofile_le
    _ = selectorObjective b lam (a ∘ coverOrder) z
          (thresholdSelector (t := C.card) K.card) := by
          symm
          simpa [lam] using
            thresholdSelector_objective_eq
              (a := a)
              (b := b)
              (C := C)
              (coverOrder := coverOrder)
              (r := r)
              (z := z)
              hordered
              hr
              hK_card

/-- Helper for Lemma 7.13: every threshold selector on a constant interval is bounded by the
constant branch target. -/
theorem thresholdObjective_le_constantIntervalTarget
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h k : ℕ} (hh : h < r) (hk : k ≤ r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C)) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) k) ≤
      b - (h : ℝ) * flow_cover_excess a b C := by
  let lam := flow_cover_excess a b C
  have hlam_pos : 0 < lam := by
    -- Flow-cover excess is positive on a genuine flow cover.
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hcard :
      partialSum C a coverOrder C.card = b + lam := by
    -- Normalize the full ordered sum once before the scalar case split.
    simpa [lam] using
      partialSum_card_eq_rhs_add_excess
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        hcoverOrder
  rw [thresholdSelector_objective_eq
    (a := a)
    (b := b)
    (C := C)
    (coverOrder := coverOrder)
    (r := r)
    (z := z)
    hordered
    hr
    hk]
  by_cases hkh : k ≤ h
  · have hprefix_mono :
        partialSum C a coverOrder k - (k : ℝ) * lam ≤
          partialSum C a coverOrder h - (h : ℝ) * lam := by
      -- Before the cut index the scalar profile `μ_k - k λ` is monotone.
      simpa [lam] using
        partialSum_sub_card_mul_excess_mono_before_cutIndex
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          hordered
          hr
          hkh
          hh
    have hmin_le : min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder k) ≤
        b - z := min_le_left _ _
    -- If `k ≤ h`, clip by the demand and compare the prefix profile at `k` to the one at `h`.
    calc
      min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder k) +
          (partialSum C a coverOrder k - (k : ℝ) * lam)
          ≤ (b - z) + (partialSum C a coverOrder h - (h : ℝ) * lam) := by
              exact add_le_add hmin_le hprefix_mono
      _ ≤ b - (h : ℝ) * lam := by
            linarith [hzpiece.1]
  · have hhk : h < k := lt_of_not_ge hkh
    have hsucc_le_k : h + 1 ≤ k := Nat.succ_le_of_lt hhk
    have hk_card : k ≤ C.card := le_trans hk hr.2.1
    have hsucc_mono :
        partialSum C a coverOrder (h + 1) ≤ partialSum C a coverOrder k := by
      -- Later thresholds have at least as much ordered capacity as the first one past `h`.
      exact partialSum_mono_of_nonneg
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        ha_nonneg
        hsucc_le_k
        hk_card
    have htail_le_demand :
        partialSum C a coverOrder C.card - partialSum C a coverOrder k ≤ b - z := by
      -- Once `k > h`, the interval upper bound already forces the tail-capacity branch of the `min`.
      rw [hcard]
      linarith [hzpiece.2, hsucc_mono]
    have hk_real : (h + 1 : ℝ) ≤ k := by
      exact_mod_cast hsucc_le_k
    -- If `k > h`, the exact threshold value is `b - (k - 1) λ`, which is at most `b - h λ`.
    rw [min_eq_right htail_le_demand, hcard]
    ring_nf
    nlinarith

/-- Helper for Lemma 7.13: every threshold selector on a gap interval is bounded by the affine
gap branch target. -/
theorem thresholdObjective_le_gapIntervalTarget
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h k : ℕ} (hh₁ : 1 ≤ h) (hh₂ : h < r) (hk : k ≤ r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h - flow_cover_excess a b C)
        (partialSum C a coverOrder h)) :
    selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
        (thresholdSelector (t := C.card) k) ≤
      b - z + partialSum C a coverOrder h - (h : ℝ) * flow_cover_excess a b C := by
  let lam := flow_cover_excess a b C
  have hlam_pos : 0 < lam := by
    -- The affine gap comparison also relies on positivity of the excess parameter.
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hcard :
      partialSum C a coverOrder C.card = b + lam := by
    -- Normalize the terminal ordered sum before splitting on the threshold index.
    simpa [lam] using
      partialSum_card_eq_rhs_add_excess
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        hcoverOrder
  rw [thresholdSelector_objective_eq
    (a := a)
    (b := b)
    (C := C)
    (coverOrder := coverOrder)
    (r := r)
    (z := z)
    hordered
    hr
    hk]
  by_cases hkh : k ≤ h
  · have hprefix_mono :
        partialSum C a coverOrder k - (k : ℝ) * lam ≤
          partialSum C a coverOrder h - (h : ℝ) * lam := by
      -- Before the cut index the same monotone prefix profile controls the gap branch.
      simpa [lam] using
        partialSum_sub_card_mul_excess_mono_before_cutIndex
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          hordered
          hr
          hkh
          hh₂
    have hmin_le : min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder k) ≤
        b - z := min_le_left _ _
    calc
      min (b - z) (partialSum C a coverOrder C.card - partialSum C a coverOrder k) +
          (partialSum C a coverOrder k - (k : ℝ) * lam)
          ≤ (b - z) + (partialSum C a coverOrder h - (h : ℝ) * lam) := by
              exact add_le_add hmin_le hprefix_mono
      _ = b - z + partialSum C a coverOrder h - (h : ℝ) * lam := by
            ring
  · have hhk : h < k := lt_of_not_ge hkh
    have hsucc_le_k : h + 1 ≤ k := Nat.succ_le_of_lt hhk
    have hk_card : k ≤ C.card := le_trans hk hr.2.1
    have hsucc_mono :
        partialSum C a coverOrder (h + 1) ≤ partialSum C a coverOrder k := by
      -- Any later threshold has at least the `(h + 1)`-tail capacity.
      exact partialSum_mono_of_nonneg
        (a := a)
        (C := C)
        (coverOrder := coverOrder)
        ha_nonneg
        hsucc_le_k
        hk_card
    have hweight_gt :
        lam < weight C a coverOrder (h + 1) := by
      -- The first coefficient after `h` still lies before the cut, so it exceeds `λ`.
      simpa [lam] using
        coverWeight_gt_excess_before_cutIndex
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          hordered
          hr
          (h := h)
          hh₂
    have hnext_gap :
        partialSum C a coverOrder h <
          partialSum C a coverOrder (h + 1) - lam := by
      -- The gap upper endpoint sits strictly before the next shifted breakpoint.
      have hweight_gt' :
          lam < a (coverOrder ⟨h, lt_of_lt_of_le hh₂ hr.2.1⟩) := by
        simpa [weight_succ C a coverOrder (lt_of_lt_of_le hh₂ hr.2.1)] using hweight_gt
      rw [partialSum_succ, weight_succ C a coverOrder (lt_of_lt_of_le hh₂ hr.2.1)]
      linarith
    have htail_le_demand :
        partialSum C a coverOrder C.card - partialSum C a coverOrder k ≤ b - z := by
      -- Since `z < μ_h < μ_{h+1} - λ ≤ μ_k - λ`, the `min` again takes the tail-capacity branch.
      rw [hcard]
      linarith [hzpiece.2, hnext_gap, hsucc_mono]
    have hk_real : (h + 1 : ℝ) ≤ k := by
      exact_mod_cast hsucc_le_k
    have hbase :
        b + lam - (k : ℝ) * lam ≤ b - (h : ℝ) * lam := by
      -- The exact threshold value decays once the cutoff moves beyond `h`.
      nlinarith
    have htarget_ge :
        b - (h : ℝ) * lam ≤ b - lam * ↑h - z + partialSum C a coverOrder h := by
      -- The affine target dominates the constant level because `z < μ_h`.
      linarith [hzpiece.2]
    rw [min_eq_right htail_le_demand, hcard]
    ring_nf
    exact le_trans hbase htarget_ge

/-- Lemma 7.13 (1). Let `T = single_node_flow_set a b` with nonnegative capacities `a`, and let
`coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let
`lam = flow_cover_excess a b C` be the source excess parameter, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`, with
`μ_|C| = b + λ`. For
`z ∈ [0, b]`, if `μ_h ≤ z < μ_{h+1} - λ` with `h = 0, …, r-1`, then the lifting function for
`C` evaluated at `z` is `h λ`. -/
theorem flow_cover_lifting_function_eq_constant_on_cover_intervals
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    {h : ℕ} (hh : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C)) :
    flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
      (h : ℝ) * flow_cover_excess a b C := by
  let lam := flow_cover_excess a b C
  let S := flow_cover_lifting_objective_values b lam (a ∘ coverOrder) z
  let targetSup : ℝ := b - (h : ℝ) * lam
  have hdemand_nonneg : 0 ≤ b - z := by
    -- The global interval hypothesis places `z` inside `[0,b]`.
    linarith [hz.2]
  have hS_bdd : BddAbove S := by
    -- A coarse demand-plus-penalty bound already controls the objective set.
    simpa [S, lam] using
      flow_cover_lifting_objective_values_bddAbove b lam (a ∘ coverOrder) z
  have hthreshold_value :
      selectorObjective b lam (a ∘ coverOrder) z
          (thresholdSelector (t := C.card) (h + 1)) = targetSup := by
    -- The source threshold witness with cutoff `h + 1` realizes the constant-piece value.
    simpa [lam, targetSup] using
      constantInterval_thresholdSelector_objective_eq
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        (r := r)
        (z := z)
        hcoverOrder
        hordered
        hr
        hh
        hzpiece
  have hthreshold_mem :
      selectorObjective b lam (a ∘ coverOrder) z
          (thresholdSelector (t := C.card) (h + 1)) ∈ S := by
    -- Realize the threshold objective by a feasible bounded fill.
    simpa [S, lam] using
      selectorObjective_mem
        (a := a ∘ coverOrder)
        (b := b)
        (lam := lam)
        (z := z)
        (ha_nonneg := fun i ↦ ha_nonneg (coverOrder i))
        hdemand_nonneg
        (thresholdSelector (t := C.card) (h + 1))
  have htarget_mem : targetSup ∈ S := by
    -- Rewrite the threshold witness value to the target objective level.
    simpa [hthreshold_value] using hthreshold_mem
  have hfun_le :
      flow_cover_lifting_function b lam (a ∘ coverOrder) z ≤ (h : ℝ) * lam := by
    -- The explicit threshold witness gives the textbook lower bound on the supremum.
    have hsSup_ge : targetSup ≤ sSup S := le_csSup hS_bdd htarget_mem
    change b - sSup S ≤ (h : ℝ) * lam
    linarith
  have hobjective_upper :
      ∀ {v : ℝ}, v ∈ S → v ≤ targetSup := by
    intro v hv
    rcases objectiveValue_le_selectorObjective hv with ⟨x, hxv⟩
    let K : Finset (Fin C.card) :=
      Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
    have hK_lt : ∀ i ∈ K, i.1 < r := by
      intro i hi
      simpa [K] using (Finset.mem_filter.mp hi).2.1
    have hK_card : K.card ≤ r := by
      exact card_le_of_val_lt (C := C) (K := K) hK_lt
    have hnormalize :
        selectorObjective b lam (a ∘ coverOrder) z x ≤
          selectorObjective b lam (a ∘ coverOrder) z
            (thresholdSelector (t := C.card) K.card) := by
      -- Normalize the arbitrary selector by the number of false before-cut positions.
      simpa [lam, K] using
        selectorObjective_le_thresholdByFalsePrefixCount
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          (z := z)
          ha_nonneg
          hordered
          hr
          x
    have hthreshold_upper :
        selectorObjective b lam (a ∘ coverOrder) z
            (thresholdSelector (t := C.card) K.card) ≤ targetSup := by
      -- Every threshold selector on this interval is bounded by the constant branch target.
      simpa [lam, targetSup] using
        thresholdObjective_le_constantIntervalTarget
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          (z := z)
          ha_nonneg
          hC
          hcoverOrder
          hordered
          hr
          (h := h)
          (k := K.card)
          hh
          hK_card
          hzpiece
    exact le_trans hxv (le_trans hnormalize hthreshold_upper)
  have hS_nonempty : S.Nonempty := ⟨targetSup, htarget_mem⟩
  have hfun_ge :
      (h : ℝ) * lam ≤ flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    -- Bounding every feasible value by the same target closes the reverse inequality.
    have hsSup_le : sSup S ≤ targetSup := csSup_le hS_nonempty (by
      intro v hv
      exact hobjective_upper hv)
    change (h : ℝ) * lam ≤ b - sSup S
    linarith
  -- The two bounds pin down the constant piece of the lifting function.
  simpa [lam] using le_antisymm hfun_le hfun_ge

/-- Lemma 7.13 (2). Let `T = single_node_flow_set a b` with nonnegative capacities `a`, and let
`coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let
`lam = flow_cover_excess a b C` be the source excess parameter, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`, with
`μ_|C| = b + λ`. For
`z ∈ [0, b]`, if `μ_h - λ ≤ z < μ_h` with `h = 1, …, r-1`, then the lifting function for `C`
evaluated at `z` is `z - μ_h + h λ`. -/
theorem flow_cover_lifting_function_eq_affine_on_gap_intervals
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    {h : ℕ} (hh₁ : 1 ≤ h) (hh₂ : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h - flow_cover_excess a b C)
        (partialSum C a coverOrder h)) :
    flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
      z - partialSum C a coverOrder h + (h : ℝ) * flow_cover_excess a b C := by
  let lam := flow_cover_excess a b C
  let S := flow_cover_lifting_objective_values b lam (a ∘ coverOrder) z
  let targetSup : ℝ := b - z + partialSum C a coverOrder h - (h : ℝ) * lam
  have hdemand_nonneg : 0 ≤ b - z := by
    -- The global interval hypothesis places `z` inside `[0,b]`.
    linarith [hz.2]
  have hS_bdd : BddAbove S := by
    -- A coarse demand-plus-penalty bound already controls the objective set.
    simpa [S, lam] using
      flow_cover_lifting_objective_values_bddAbove b lam (a ∘ coverOrder) z
  have hthreshold_value :
      selectorObjective b lam (a ∘ coverOrder) z
          (thresholdSelector (t := C.card) h) = targetSup := by
    -- The source threshold witness with cutoff `h` realizes the affine gap value.
    simpa [lam, targetSup] using
      gapInterval_thresholdSelector_objective_eq
        (a := a)
        (b := b)
        (C := C)
        (coverOrder := coverOrder)
        (r := r)
        (z := z)
        hcoverOrder
        hordered
        hr
        hh₂
        hzpiece
  have hthreshold_mem :
      selectorObjective b lam (a ∘ coverOrder) z
          (thresholdSelector (t := C.card) h) ∈ S := by
    -- Realize the threshold objective by a feasible bounded fill.
    simpa [S, lam] using
      selectorObjective_mem
        (a := a ∘ coverOrder)
        (b := b)
        (lam := lam)
        (z := z)
        (ha_nonneg := fun i ↦ ha_nonneg (coverOrder i))
        hdemand_nonneg
        (thresholdSelector (t := C.card) h)
  have htarget_mem : targetSup ∈ S := by
    -- Rewrite the threshold witness value to the target objective level.
    simpa [hthreshold_value] using hthreshold_mem
  have hfun_le :
      flow_cover_lifting_function b lam (a ∘ coverOrder) z ≤
        z - partialSum C a coverOrder h + (h : ℝ) * lam := by
    -- The explicit threshold witness gives the textbook lower bound on the supremum.
    have hsSup_ge : targetSup ≤ sSup S := le_csSup hS_bdd htarget_mem
    change b - sSup S ≤ z - partialSum C a coverOrder h + (h : ℝ) * lam
    linarith
  have hobjective_upper :
      ∀ {v : ℝ}, v ∈ S → v ≤ targetSup := by
    intro v hv
    rcases objectiveValue_le_selectorObjective hv with ⟨x, hxv⟩
    let K : Finset (Fin C.card) :=
      Finset.univ.filter (fun i : Fin C.card ↦ i.1 < r ∧ x i = false)
    have hK_lt : ∀ i ∈ K, i.1 < r := by
      intro i hi
      simpa [K] using (Finset.mem_filter.mp hi).2.1
    have hK_card : K.card ≤ r := by
      exact card_le_of_val_lt (C := C) (K := K) hK_lt
    have hnormalize :
        selectorObjective b lam (a ∘ coverOrder) z x ≤
          selectorObjective b lam (a ∘ coverOrder) z
            (thresholdSelector (t := C.card) K.card) := by
      -- Normalize the arbitrary selector by the same false-prefix count used in the constant case.
      simpa [lam, K] using
        selectorObjective_le_thresholdByFalsePrefixCount
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          (z := z)
          ha_nonneg
          hordered
          hr
          x
    have hthreshold_upper :
        selectorObjective b lam (a ∘ coverOrder) z
            (thresholdSelector (t := C.card) K.card) ≤ targetSup := by
      -- The branch-specific threshold bound now matches the affine gap target.
      simpa [lam, targetSup] using
        thresholdObjective_le_gapIntervalTarget
          (a := a)
          (b := b)
          (C := C)
          (coverOrder := coverOrder)
          (r := r)
          (z := z)
          ha_nonneg
          hC
          hcoverOrder
          hordered
          hr
          (h := h)
          (k := K.card)
          hh₁
          hh₂
          hK_card
          hzpiece
    exact le_trans hxv (le_trans hnormalize hthreshold_upper)
  have hS_nonempty : S.Nonempty := ⟨targetSup, htarget_mem⟩
  have hfun_ge :
      z - partialSum C a coverOrder h + (h : ℝ) * lam ≤
        flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    -- The selector normalization and threshold comparison control every feasible value.
    have hsSup_le : sSup S ≤ targetSup := csSup_le hS_nonempty (by
      intro v hv
      exact hobjective_upper hv)
    change z - partialSum C a coverOrder h + (h : ℝ) * lam ≤ b - sSup S
    linarith
  -- The matching inequalities force the affine gap formula.
  simpa [lam] using le_antisymm hfun_le hfun_ge

/-- Lemma 7.13 (3). Let `T = single_node_flow_set a b` with nonnegative capacities `a`, and let
`coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let
`lam = flow_cover_excess a b C` be the source excess parameter, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`, with
`μ_|C| = b + λ`. For
`z ∈ [0, b]`, if `μ_r - λ ≤ z ≤ b`, then the lifting function for `C` evaluated at `z` is
`z - μ_r + r λ`. -/
theorem flow_cover_lifting_function_eq_affine_on_final_interval
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hzpiece :
      z ∈ Set.Icc (partialSum C a coverOrder r - flow_cover_excess a b C) b) :
    flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
      z - partialSum C a coverOrder r + (r : ℝ) * flow_cover_excess a b C := by
  let lam := flow_cover_excess a b C
  let S := flow_cover_lifting_objective_values b lam (a ∘ coverOrder) z
  let targetSup : ℝ := b - z + (partialSum C a coverOrder r - (r : ℝ) * lam)
  have hk : r ≤ C.card := hr.2.1
  let tailCapacity : Fin C.card → ℝ := fun i ↦
    if r ≤ i.1 then a (coverOrder i) else 0
  have htailCapacity_nonneg : ∀ i, 0 ≤ tailCapacity i := by
    intro i
    by_cases hir : r ≤ i.1
    · simp [tailCapacity, hir]
      exact ha_nonneg (coverOrder i)
    · simp [tailCapacity, hir]
  have hdemand_nonneg : 0 ≤ b - z := by
    -- The global interval hypothesis places `z` inside `[0,b]`.
    linarith [hz.2]
  have hdemand_le_tail :
      b - z ≤ ∑ i : Fin C.card, tailCapacity i := by
    -- The terminal interval starts exactly when the tail capacity from `r + 1` onward
    -- becomes large enough to absorb the residual demand `b - z`.
    have htailSum :
        (∑ i : Fin C.card, tailCapacity i) =
          partialSum C a coverOrder C.card - partialSum C a coverOrder r := by
      simpa [tailCapacity] using
        suffixCapacity_eq_partialSum_sub
          (a := a) (C := C) (coverOrder := coverOrder) (k := r) hk
    have hcard :
        partialSum C a coverOrder C.card = b + lam := by
      simpa [lam] using
        partialSum_card_eq_rhs_add_excess
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) hcoverOrder
    rw [htailSum, hcard]
    linarith [hzpiece.1]
  obtain ⟨yWitness, hyWitness_nonneg, hyWitness_le, hyWitness_sum⟩ :=
    boundedSum_exists
      (w := tailCapacity)
      htailCapacity_nonneg
      hdemand_nonneg
      hdemand_le_tail
  let xWitness : Fin C.card → Bool := fun i ↦ if r ≤ i.1 then true else false
  have hprefixPenalty :
      (∑ i : Fin C.card, if i.1 < r then a (coverOrder i) - lam else 0) =
        partialSum C a coverOrder r - (r : ℝ) * lam := by
    simpa [lam] using
      prefixPenaltySum_eq
        (a := a) (C := C) (coverOrder := coverOrder) (lam := lam)
        (k := r) hk
  have htarget_mem : targetSup ∈ S := by
    -- The source witness turns every after-cut selector on, fills exactly `b - z` tail capacity,
    -- and keeps all earlier selectors off.
    refine (mem_flow_cover_lifting_objective_values_iff b lam (a ∘ coverOrder) z targetSup).2 ?_
    refine ⟨xWitness, yWitness, hyWitness_nonneg, ?_, ?_, ?_⟩
    · simpa [targetSup] using hyWitness_sum.le
    · intro i
      by_cases hir : r ≤ i.1
      · simpa [tailCapacity, xWitness, hir] using hyWitness_le i
      · simpa [tailCapacity, xWitness, hir] using hyWitness_le i
    · have hpenalty_eval :
          (∑ i : Fin C.card,
              max (a (coverOrder i) - lam) 0 *
                (1 - if xWitness i then (1 : ℝ) else 0)) =
            ∑ i : Fin C.card, if i.1 < r then a (coverOrder i) - lam else 0 := by
        -- The witness leaves the first `r` selectors off and turns all later selectors on.
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hik : i.1 < r
        · have hlt :
              lam < a (coverOrder i) := by
            simpa [lam, weight_succ C a coverOrder i.isLt] using
              coverWeight_gt_excess_before_cutIndex
                (a := a) (b := b) (C := C) (coverOrder := coverOrder)
                (r := r) hordered hr (h := i.1) hik
          have hpenalty_eq : max (a (coverOrder i) - lam) 0 = a (coverOrder i) - lam := by
            rw [max_eq_left]
            linarith
          have hx_false : xWitness i = false := by
            simp [xWitness, Nat.not_le_of_lt hik]
          simp [hik, hx_false, hpenalty_eq]
        · have hx_true : xWitness i = true := by
            simp [xWitness, Nat.le_of_not_gt hik]
          simp [hik, hx_true]
      calc
        targetSup
            = (∑ i : Fin C.card, yWitness i) +
                ∑ i : Fin C.card,
                  max (a (coverOrder i) - lam) 0 *
                    (1 - if xWitness i then (1 : ℝ) else 0) := by
              rw [hyWitness_sum, hpenalty_eval, hprefixPenalty]
        _ =
            ∑ i : Fin C.card,
              (yWitness i +
                max (a (coverOrder i) - lam) 0 *
                  (1 - if xWitness i then (1 : ℝ) else 0)) := by
              rw [Finset.sum_add_distrib]
  have hobjective_upper :
      ∀ {v : ℝ}, v ∈ S → v ≤ targetSup := by
    intro v hv
    rcases (mem_flow_cover_lifting_objective_values_iff b lam (a ∘ coverOrder) z v).1 hv with
      ⟨x, y, hy_nonneg, hy_sum, hy_cap, hv_eq⟩
    have hpenalty_le :
        (∑ i : Fin C.card,
            max (a (coverOrder i) - lam) 0 *
              (1 - if x i then (1 : ℝ) else 0)) ≤
          ∑ i : Fin C.card, if i.1 < r then a (coverOrder i) - lam else 0 := by
      -- Before the cut the penalty factor is at most the exact difference `a_i - λ`,
      -- while after the cut the penalty itself vanishes.
      refine Finset.sum_le_sum ?_
      intro i hi
      by_cases hik : i.1 < r
      · have hlt :
            lam < a (coverOrder i) := by
          simpa [lam, weight_succ C a coverOrder i.isLt] using
            coverWeight_gt_excess_before_cutIndex
              (a := a) (b := b) (C := C) (coverOrder := coverOrder)
              (r := r) hordered hr (h := i.1) hik
        have hpenalty_eq : max (a (coverOrder i) - lam) 0 = a (coverOrder i) - lam := by
          rw [max_eq_left]
          linarith
        cases hxi : x i
        · simp [hik, hxi, hpenalty_eq]
        · have hnonneg : 0 ≤ a (coverOrder i) - lam := by
            linarith
          simp [hik, hxi, hpenalty_eq, hnonneg]
      · have hir : r ≤ i.1 := Nat.le_of_not_gt hik
        have htail :
            weight C a coverOrder (i.1 + 1) ≤ lam := by
          exact hr.2.2.2 (i.1 + 1) (lt_of_le_of_lt hir (Nat.lt_succ_self _))
            (Nat.succ_le_of_lt i.isLt)
        have hpenalty_zero : max (a (coverOrder i) - lam) 0 = 0 := by
          rw [max_eq_right]
          have hle : a (coverOrder i) ≤ lam := by
            simpa [lam, weight_succ C a coverOrder i.isLt] using htail
          linarith
        simp [hik, hpenalty_zero]
    have hv_split :
        v =
          (∑ i : Fin C.card, y i) +
            ∑ i : Fin C.card,
              max (a (coverOrder i) - lam) 0 *
                (1 - if x i then (1 : ℝ) else 0) := by
      rw [hv_eq, Finset.sum_add_distrib]
      simp [Function.comp]
    calc
      v ≤ (b - z) +
            ∑ i : Fin C.card, if i.1 < r then a (coverOrder i) - lam else 0 := by
            rw [hv_split]
            linarith
      _ = targetSup := by
            rw [hprefixPenalty]
  have hS_bdd : BddAbove S := ⟨targetSup, by
    intro v hv
    exact hobjective_upper hv⟩
  have hS_nonempty : S.Nonempty := ⟨targetSup, htarget_mem⟩
  have hfun_upper :
      flow_cover_lifting_function b lam (a ∘ coverOrder) z ≤
        z - partialSum C a coverOrder r + (r : ℝ) * lam := by
    -- The explicit textbook witness gives a lower bound on the supremum.
    have hsSup_ge : targetSup ≤ sSup S := le_csSup hS_bdd htarget_mem
    change b - sSup S ≤ z - partialSum C a coverOrder r + (r : ℝ) * lam
    linarith
  have hfun_lower :
      z - partialSum C a coverOrder r + (r : ℝ) * lam ≤
        flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    -- Any feasible witness has objective at most the same textbook value.
    have hsSup_le : sSup S ≤ targetSup := csSup_le hS_nonempty (by
      intro v hv
      exact hobjective_upper hv)
    change z - partialSum C a coverOrder r + (r : ℝ) * lam ≤ b - sSup S
    linarith
  -- The matching upper and lower bounds force the final affine formula.
  simpa [lam] using le_antisymm hfun_upper hfun_lower

/-- ch7_sec7_3_lemma_7_13

Lemma 7.13. Let `C` be a flow cover, let `coverOrder` enumerate the elements of `C` in
nonincreasing order of their coefficients, let `lam = flow_cover_excess a b C`, and let `r` be
the source cut index `max {i ∈ C : a_{j_i} > λ}`. For `z ∈ [0, b]`, the lifting function for `C`
has the three source pieces stated below on the ordered cover intervals, the gap intervals, and
the final interval. -/
theorem ch7_sec7_3_lemma_7_13
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hz : z ∈ Set.Icc (0 : ℝ) b) :
    (∀ {h : ℕ}, h < r →
      z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) →
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
        (h : ℝ) * flow_cover_excess a b C) ∧
    (∀ {h : ℕ}, 1 ≤ h → h < r →
      z ∈ Set.Ico
        (partialSum C a coverOrder h - flow_cover_excess a b C)
        (partialSum C a coverOrder h) →
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
        z - partialSum C a coverOrder h + (h : ℝ) * flow_cover_excess a b C) ∧
    (z ∈ Set.Icc (partialSum C a coverOrder r - flow_cover_excess a b C) b →
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
        z - partialSum C a coverOrder r + (r : ℝ) * flow_cover_excess a b C) := by
  -- Route correction: the wrapper theorem should only assemble the three companion formulas,
  -- not reopen the optimization argument inside the conjunction.
  constructor
  · intro h hh hzpiece
    -- Reuse the constant-piece companion theorem on the current interval.
    exact flow_cover_lifting_function_eq_constant_on_cover_intervals
      (a := a)
      (b := b)
      (C := C)
      (coverOrder := coverOrder)
      (r := r)
      (z := z)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hh
      hzpiece
  constructor
  · intro h hh₁ hh₂ hzpiece
    -- Reuse the gap-piece companion theorem on the current interval.
    exact flow_cover_lifting_function_eq_affine_on_gap_intervals
      (a := a)
      (b := b)
      (C := C)
      (coverOrder := coverOrder)
      (r := r)
      (z := z)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hh₁
      hh₂
      hzpiece
  · intro hzpiece
    -- Reuse the final affine companion theorem on the terminal interval.
    exact flow_cover_lifting_function_eq_affine_on_final_interval
      (a := a)
      (b := b)
      (C := C)
      (coverOrder := coverOrder)
      (r := r)
      (z := z)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hzpiece

end Lemma713
