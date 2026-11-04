/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_definition_4_8_1_extra_1

section Proposition433

variable {n : ℕ}

/-- The candidate vertex `v^t` of `P^mix`, with first coordinate given by the extended
fractional-part vector at `t`, lower integer parts up to index `t`, and upper integer parts
afterwards. -/
noncomputable def mixingVertexCandidate
    (b : Fin n → ℚ) (t : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  Fin.cases (extendedMixingFractionalPart b t)
    fun i ↦ if i.succ ≤ t then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ)

/-- The `0`th coordinate of the candidate vertex `v^t` is the `t`-th extended fractional part. -/
@[simp] theorem mixingVertexCandidate_apply_zero
    {b : Fin n → ℚ} {t : Fin (n + 1)} :
    mixingVertexCandidate b t 0 = extendedMixingFractionalPart b t := by
  rfl

/-- For `i = 1, ..., n`, the `i`th coordinate of `v^t` is `⌊b_i⌋` up to `t` and `⌈b_i⌉`
afterwards. -/
@[simp] theorem mixingVertexCandidate_apply_succ
    {b : Fin n → ℚ} {t : Fin (n + 1)} (i : Fin n) :
    mixingVertexCandidate b t i.succ =
      if i.succ ≤ t then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) := by
  rfl

/-- Helper for Proposition 4.33: a vertex of `P^mix` has first coordinate strictly below `1`. -/
lemma extreme_point_zero_lt_one
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ (mixingHull b).extremePoints ℝ) :
    x 0 < 1 := by
  -- Place the extreme point back in the generating mixing set.
  have hxmix : x ∈ mixingSet b := extremePoints_convexHull_subset hx
  rw [mem_mixingSet_iff] at hxmix
  rcases hxmix with ⟨hx0_nonneg, htail, hineq⟩
  by_contra hx0
  have hx0_ge : 1 ≤ x 0 := le_of_not_gt hx0
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray 0
  let y : Fin (n + 1) → ℝ := x - r
  let z : Fin (n + 1) → ℝ := x + r
  have hy_mix : y ∈ mixingSet b := by
    -- Subtracting `r⁰` lowers `x₀` by `1` and raises each integer tail entry by `1`.
    rw [mem_mixingSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hy0 : y 0 = x 0 - 1 := by
        simp [y, r, exercise_3_29_ray_apply]
      linarith
    · rw [mem_integerVectors_iff_forall] at htail ⊢
      intro t
      obtain ⟨m, hm⟩ := htail t
      refine ⟨m + 1, ?_⟩
      simpa [y, r, hm, exercise_3_29_ray_apply, sub_eq_add_neg]
    · intro t
      have ht := hineq t
      simp [y, r, exercise_3_29_ray_apply]
      linarith
  have hz_mix : z ∈ mixingSet b := by
    -- Adding `r⁰` raises `x₀` by `1` and lowers each integer tail entry by `1`.
    rw [mem_mixingSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hz0 : z 0 = x 0 + 1 := by
        simp [z, r, exercise_3_29_ray_apply]
      linarith
    · rw [mem_integerVectors_iff_forall] at htail ⊢
      intro t
      obtain ⟨m, hm⟩ := htail t
      refine ⟨m - 1, ?_⟩
      simpa [z, r, hm, exercise_3_29_ray_apply, sub_eq_add_neg]
    · intro t
      have ht := hineq t
      simp [z, r, exercise_3_29_ray_apply]
      linarith
  have hy_hull : y ∈ mixingHull b := by
    change y ∈ convexHull ℝ (mixingSet b)
    exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hy_mix
  have hz_hull : z ∈ mixingHull b := by
    change z ∈ convexHull ℝ (mixingSet b)
    exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hz_mix
  have hseg : x ∈ openSegment ℝ y z := by
    -- The point `x` is the midpoint of the symmetric perturbation `x ± r⁰`.
    simpa [y, z, r] using (mem_openSegment_sub_add (𝕜 := ℝ) x r)
  have hy_eq : y = x := (mem_extremePoints_iff_left.mp hx).2 y hy_hull z hz_hull hseg
  have hy0 : y 0 = x 0 - 1 := by
    simp [y, r, exercise_3_29_ray_apply]
  have hy0_eq : y 0 = x 0 := congrArg (fun p ↦ p 0) hy_eq
  linarith

/-- Helper for Proposition 4.33: increasing a successor coordinate by the corresponding Exercise
3.29 ray preserves the mixing-set constraints. -/
lemma mixingSet_add_successor_ray_mem
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) (i : Fin n) :
    x + exercise_3_29_ray i.succ ∈ mixingSet b := by
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hineq⟩
  have hneq : (0 : Fin (n + 1)) ≠ i.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero i)
  have hzero : exercise_3_29_ray i.succ 0 = 0 := by
    rw [exercise_3_29_ray_apply]
    simp [hneq]
  refine ⟨?_, ?_, ?_⟩
  · -- The successor ray leaves the zeroth coordinate unchanged.
    simpa [hzero] using hx0_nonneg
  · -- The tail stays integral because only the `i`th successor coordinate increases by `1`.
    rw [mem_integerVectors_iff_forall] at htail ⊢
    intro t
    rcases htail t with ⟨m, hm⟩
    by_cases ht : t = i
    · subst ht
      refine ⟨m + 1, ?_⟩
      simp [exercise_3_29_ray_apply, hm]
    · refine ⟨m, ?_⟩
      simp [exercise_3_29_ray_apply, ht, hm]
  · -- Only the `i`th covering inequality changes, and there it becomes easier.
    intro t
    by_cases ht : t = i
    · subst t
      have hi := hineq i
      simp [exercise_3_29_ray_apply, hneq]
      linarith
    · have ht' := hineq t
      simpa [exercise_3_29_ray_apply, hneq, ht] using ht'

/-- Helper for Proposition 4.33: decreasing a successor coordinate by the corresponding Exercise
3.29 ray preserves the mixing-set constraints as soon as the affected covering inequality remains
valid. -/
lemma mixingSet_sub_successor_ray_of_sub_le
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) (i : Fin n)
    (hsub : (b i : ℝ) - x 0 ≤ x i.succ - 1) :
    x - exercise_3_29_ray i.succ ∈ mixingSet b := by
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hineq⟩
  have hneq : (0 : Fin (n + 1)) ≠ i.succ := by
    simpa [eq_comm] using (Fin.succ_ne_zero i)
  have hzero : exercise_3_29_ray i.succ 0 = 0 := by
    rw [exercise_3_29_ray_apply]
    simp [hneq]
  refine ⟨?_, ?_, ?_⟩
  · -- The successor ray also leaves the zeroth coordinate unchanged under subtraction.
    simpa [hzero, sub_eq_add_neg] using hx0_nonneg
  · -- The tail stays integral because only the `i`th successor coordinate decreases by `1`.
    rw [mem_integerVectors_iff_forall] at htail ⊢
    intro t
    rcases htail t with ⟨m, hm⟩
    by_cases ht : t = i
    · subst ht
      refine ⟨m - 1, ?_⟩
      simp [exercise_3_29_ray_apply, hm, sub_eq_add_neg]
    · refine ⟨m, ?_⟩
      simp [exercise_3_29_ray_apply, ht, hm, sub_eq_add_neg]
  · -- The hypothesis `hsub` is exactly the updated `i`th covering inequality.
    intro t
    by_cases ht : t = i
    · subst t
      simp [exercise_3_29_ray_apply, hneq, sub_eq_add_neg]
      linarith
    · have ht' := hineq t
      simpa [exercise_3_29_ray_apply, hneq, ht, sub_eq_add_neg] using ht'

/-- Helper for Proposition 4.33: at a vertex of `P^mix`, every successor coordinate is the
smallest integer allowed by the covering inequality. -/
lemma extreme_point_succ_eq_ceil_sub_zero
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ (mixingHull b).extremePoints ℝ) (i : Fin n) :
    x i.succ = (⌈(b i : ℝ) - x 0⌉ : ℝ) := by
  -- Route correction: isolate the successor-ray feasibility checks before using extremality.
  have hxmix_mem : x ∈ mixingSet b := extremePoints_convexHull_subset hx
  have hxmix := hxmix_mem
  rw [mem_mixingSet_iff_forall] at hxmix
  rcases hxmix with ⟨hx0_nonneg, htail, hineq⟩
  rcases htail i with ⟨m, hm⟩
  have hm' : x i.succ = (m : ℝ) := by
    simpa using hm.symm
  have hceil_le : ⌈(b i : ℝ) - x 0⌉ ≤ m := by
    -- Feasibility gives the lower bound on the least admissible integer.
    apply Int.ceil_le.mpr
    have hi := hineq i
    have hsub : (b i : ℝ) - x 0 ≤ x i.succ := by
      linarith
    simpa [hm'] using hsub
  have hceil_eq : ⌈(b i : ℝ) - x 0⌉ = m := by
    apply le_antisymm hceil_le
    by_contra hm_lt
    have hceil_lt_m : ⌈(b i : ℝ) - x 0⌉ < m := lt_of_not_ge hm_lt
    have hceil_le_pred : ⌈(b i : ℝ) - x 0⌉ ≤ m - 1 := by
      omega
    have hsub_le_int : (b i : ℝ) - x 0 ≤ (m - 1 : ℤ) := by
      exact Int.ceil_le.mp hceil_le_pred
    have hsub_le : (b i : ℝ) - x 0 ≤ x i.succ - 1 := by
      simpa [hm'] using hsub_le_int
    let r : Fin (n + 1) → ℝ := exercise_3_29_ray i.succ
    let y : Fin (n + 1) → ℝ := x - r
    let z : Fin (n + 1) → ℝ := x + r
    have hy_mix : y ∈ mixingSet b :=
      mixingSet_sub_successor_ray_of_sub_le hxmix_mem i hsub_le
    have hz_mix : z ∈ mixingSet b :=
      mixingSet_add_successor_ray_mem hxmix_mem i
    have hy_hull : y ∈ mixingHull b := by
      change y ∈ convexHull ℝ (mixingSet b)
      exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hy_mix
    have hz_hull : z ∈ mixingHull b := by
      change z ∈ convexHull ℝ (mixingSet b)
      exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hz_mix
    have hseg : x ∈ openSegment ℝ y z := by
      -- The point `x` is again the midpoint of the symmetric perturbation `x ± r^(i+1)`.
      simpa [y, z, r] using (mem_openSegment_sub_add (𝕜 := ℝ) x r)
    have hy_eq : y = x := (mem_extremePoints_iff_left.mp hx).2 y hy_hull z hz_hull hseg
    have hyi : y i.succ = x i.succ - 1 := by
      simp [y, r, exercise_3_29_ray_apply, sub_eq_add_neg]
    have hyi_eq : y i.succ = x i.succ := congrArg (fun p ↦ p i.succ) hy_eq
    linarith
  -- Cast the integer equality back to the ambient real coordinates.
  rw [hm']
  exact congrArg (fun z : ℤ ↦ (z : ℝ)) hceil_eq.symm

/-- Helper for Proposition 4.33: subtracting a value `c ∈ [0, 1)` from `bᵢ` turns the ceiling into
either the floor or the ceiling of `bᵢ`, depending on whether the fractional part of `bᵢ` is at
most `c`. -/
lemma ceil_sub_eq_floor_or_ceil_by_fract
    {b : Fin n → ℚ} {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt : c < 1) (i : Fin n) :
    (⌈(b i : ℝ) - c⌉ : ℝ) =
      if mixingFractionalPart b i ≤ c then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) := by
  let a : ℝ := b i
  have hfract : mixingFractionalPart b i = Int.fract a := by
    simpa [a] using mixingFractionalPart_eq_fract b i
  have hrewrite : a - c = (⌊a⌋ : ℝ) + (Int.fract a - c) := by
    calc
      a - c = ((⌊a⌋ : ℝ) + Int.fract a) - c := by rw [Int.floor_add_fract a]
      _ = (⌊a⌋ : ℝ) + (Int.fract a - c) := by ring
  by_cases hle : mixingFractionalPart b i ≤ c
  · have hfract_le : Int.fract a ≤ c := by
      simpa [hfract] using hle
    have hmem : a - c ∈ Set.Ioc ((⌊a⌋ : ℝ) - 1) ⌊a⌋ := by
      constructor
      · rw [hrewrite]
        linarith [Int.fract_nonneg a, Int.fract_lt_one a, hc_lt]
      · rw [hrewrite]
        linarith
    have hceil : (⌈a - c⌉ : ℝ) = ⌊a⌋ := Int.ceil_eq_on_Ioc' ⌊a⌋ (a - c) hmem
    rw [if_pos hle]
    simpa [a] using hceil
  · have hfract_gt : c < Int.fract a := by
      have hnot : ¬ Int.fract a ≤ c := by
        simpa [hfract] using hle
      exact lt_of_not_ge hnot
    have hfract_ne : Int.fract a ≠ 0 := by
      linarith
    have hceil_eq : ⌈a⌉ = ⌊a⌋ + 1 := by
      exact (Int.ceil_eq_floor_add_one_iff_notMem a).2 ((Int.fract_ne_zero_iff).1 hfract_ne)
    have hmem : a - c ∈ Set.Ioc ((⌈a⌉ : ℝ) - 1) ⌈a⌉ := by
      constructor
      · rw [hrewrite, hceil_eq]
        norm_num
        linarith
      · have hsub_le : a - c ≤ a := sub_le_self _ hc_nonneg
        exact hsub_le.trans (Int.le_ceil a)
    have hceil : (⌈a - c⌉ : ℝ) = ⌈a⌉ := Int.ceil_eq_on_Ioc' ⌈a⌉ (a - c) hmem
    rw [if_neg hle]
    simpa [a] using hceil

/-- Helper for Proposition 4.33: every extended fractional value lies in `[0, 1)`. -/
lemma extendedMixingFractionalPart_nonneg
    {b : Fin n → ℚ} (t : Fin (n + 1)) :
    0 ≤ extendedMixingFractionalPart b t := by
  -- Split between `f₀ = 0` and the genuine fractional-part coordinates.
  refine Fin.cases ?_ ?_ t
  · simp
  · intro i
    simpa [extendedMixingFractionalPart, mixingFractionalPart] using
      (Int.fract_nonneg ((b i : ℚ) : ℝ))

/-- Helper for Proposition 4.33: every extended fractional value is strictly below `1`. -/
lemma extendedMixingFractionalPart_lt_one
    {b : Fin n → ℚ} (t : Fin (n + 1)) :
    extendedMixingFractionalPart b t < 1 := by
  -- The successor coordinates are ordinary fractional parts, so the same bound applies.
  refine Fin.cases ?_ ?_ t
  · simp
  · intro i
    simpa [extendedMixingFractionalPart, mixingFractionalPart] using
      (Int.fract_lt_one ((b i : ℚ) : ℝ))

/-- Helper for Proposition 4.33: if `c` avoids the finite threshold set
`Set.range (extendedMixingFractionalPart b)`, then there is a positive margin around `c` that also
stays inside `(0, 1)`. -/
lemma exists_positive_margin_away_from_extended_fractional_values
    {b : Fin n → ℚ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hc_not_mem : c ∉ Set.range (extendedMixingFractionalPart b)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < c ∧
        c + ε < 1 ∧
        ∀ s : Fin (n + 1), ε < |c - extendedMixingFractionalPart b s| := by
  let values : Finset ℝ := Finset.univ.image fun s : Fin (n + 1) ↦
    |c - extendedMixingFractionalPart b s|
  have hvalues_nonempty : values.Nonempty := by
    exact Finset.univ_nonempty.image fun s : Fin (n + 1) ↦
      |c - extendedMixingFractionalPart b s|
  let lower : ℝ := values.min' hvalues_nonempty
  have hlower_pos : 0 < lower := by
    -- The minimum distance is positive because `c` is not itself a threshold value.
    change 0 < values.min' hvalues_nonempty
    rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨s, -, hs⟩
    rw [← hs]
    have hneq : c ≠ extendedMixingFractionalPart b s := by
      intro hcs
      exact hc_not_mem ⟨s, hcs.symm⟩
    have habs_ne_zero : |c - extendedMixingFractionalPart b s| ≠ 0 := by
      simpa using sub_ne_zero.mpr hneq
    exact lt_of_le_of_ne (abs_nonneg _) habs_ne_zero.symm
  have hc_ne_zero : c ≠ 0 := by
    intro hc_zero
    apply hc_not_mem
    exact ⟨0, by simpa [hc_zero] using (extendedMixingFractionalPart_zero b)⟩
  have hc_pos : 0 < c := by
    exact lt_of_le_of_ne hc_nonneg hc_ne_zero.symm
  have hone_sub_pos : 0 < 1 - c := by
    linarith
  let ε : ℝ := min (c / 2) (min ((1 - c) / 2) (lower / 2))
  refine ⟨ε, ?_, ?_, ?_, ?_⟩
  · -- The chosen minimum keeps only positive quantities.
    have hc_half_pos : 0 < c / 2 := by linarith
    have hone_half_pos : 0 < (1 - c) / 2 := by linarith
    have hlower_half_pos : 0 < lower / 2 := by linarith
    dsimp [ε]
    exact lt_min hc_half_pos (lt_min hone_half_pos hlower_half_pos)
  · -- The first bound keeps the left perturbation nonnegative.
    have hε_le : ε ≤ c / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    linarith
  · -- The second bound keeps the right perturbation strictly below `1`.
    have hε_le : ε ≤ (1 - c) / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · intro s
    -- The minimum distance controls the gap to every threshold value.
    have hlower_le :
        lower ≤ |c - extendedMixingFractionalPart b s| := by
      exact Finset.min'_le values _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    have hε_le : ε ≤ lower / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hhalf_lt : lower / 2 < |c - extendedMixingFractionalPart b s| := by
      linarith
    exact lt_of_le_of_lt hε_le hhalf_lt

/-- Helper for Proposition 4.33: two vertices of `P^mix` with the same first coordinate agree in
every coordinate. -/
lemma extreme_point_eq_of_zero_eq
    {b : Fin n → ℚ} {x y : Fin (n + 1) → ℝ}
    (hx : x ∈ (mixingHull b).extremePoints ℝ)
    (hy : y ∈ (mixingHull b).extremePoints ℝ)
    (hzero : x 0 = y 0) :
    x = y := by
  -- Compare the zeroth coordinate directly and all successor coordinates via the rigidity lemma.
  ext j
  refine Fin.cases hzero ?_ j
  intro i
  rw [extreme_point_succ_eq_ceil_sub_zero hx i, extreme_point_succ_eq_ceil_sub_zero hy i, hzero]

/-- Helper for Proposition 4.33: every value in the finite range of `f` has a last index where it
occurs. -/
lemma exists_last_index_of_mem_range
    {f : Fin (n + 1) → ℝ} {c : ℝ} (hc : c ∈ Set.range f) :
    ∃ t : Fin (n + 1), f t = c ∧ ∀ s : Fin (n + 1), f s = c → s ≤ t := by
  let s : Set (Fin (n + 1)) := {t | f t = c}
  have hs_nonempty : s.Nonempty := by
    rcases hc with ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image s id s.toFinite hs_nonempty
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact hmax u hu

/-- Helper for Proposition 4.33: at the last occurrence of a fractional value, the corresponding
candidate point satisfies the same ceiling formula as an actual vertex. -/
lemma mixingVertexCandidate_succ_eq_ceil_sub_of_last_occurrence
    {b : Fin n → ℚ} {t : Fin (n + 1)}
    (hmono : Monotone (extendedMixingFractionalPart b))
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (i : Fin n) :
    mixingVertexCandidate b t i.succ =
      (⌈(b i : ℝ) - extendedMixingFractionalPart b t⌉ : ℝ) := by
  -- The monotone last-occurrence hypothesis tells us exactly which branch of the ceiling formula
  -- is active at the fractional value `f_t`.
  have ht_nonneg : 0 ≤ extendedMixingFractionalPart b t :=
    extendedMixingFractionalPart_nonneg t
  have ht_lt_one : extendedMixingFractionalPart b t < 1 :=
    extendedMixingFractionalPart_lt_one t
  rw [mixingVertexCandidate_apply_succ, ceil_sub_eq_floor_or_ceil_by_fract ht_nonneg ht_lt_one i]
  by_cases hle : i.succ ≤ t
  · have hfrac_le :
        mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
      simpa using hmono hle
    rw [if_pos hle, if_pos hfrac_le]
  · have hlt : t < i.succ := lt_of_not_ge hle
    have hfrac_not_le :
        ¬ mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
      intro hfrac_le
      have ht_le :
          extendedMixingFractionalPart b t ≤ extendedMixingFractionalPart b i.succ := by
        exact hmono (le_of_lt hlt)
      have hi_le :
          extendedMixingFractionalPart b i.succ ≤ extendedMixingFractionalPart b t := by
        simpa using hfrac_le
      have heq :
          extendedMixingFractionalPart b i.succ = extendedMixingFractionalPart b t :=
        le_antisymm hi_le ht_le
      have : i.succ ≤ t := hlast i.succ heq
      exact hle this
    rw [if_neg hle, if_neg hfrac_not_le]

/-- Helper for Proposition 4.33: every point of `mixingHull b` satisfies the linear relaxation
obtained by dropping the tail-integrality constraints from `mixingSet b`. -/
lemma mixingHull_mem_relaxation
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b) :
    0 ≤ x 0 ∧ ∀ i : Fin n, (b i : ℝ) ≤ x 0 + x i.succ := by
  let P : Set (Fin (n + 1) → ℝ) := exercise_3_29_polyhedron fun i : Fin n ↦ (b i : ℝ)
  have hsubset : mixingSet b ⊆ P := by
    intro y hy
    rw [mem_mixingSet_iff] at hy
    rw [mem_exercise_3_29_polyhedron_iff]
    exact ⟨hy.1, hy.2.2⟩
  have hconv : Convex ℝ P := by
    -- The relaxation is convex because each defining inequality is preserved by convex
    -- combinations.
    intro y hy z hz a c ha hc hac
    rw [mem_exercise_3_29_polyhedron_iff] at hy hz ⊢
    refine ⟨?_, ?_⟩
    · have hy0 := hy.1
      have hz0 := hz.1
      have hcoord : (a • y + c • z) 0 = a * y 0 + c * z 0 := by
        simp
      rw [hcoord]
      exact add_nonneg (mul_nonneg ha hy0) (mul_nonneg hc hz0)
    · intro i
      have hyi := hy.2 i
      have hzi := hz.2 i
      have hcoord0 : (a • y + c • z) 0 = a * y 0 + c * z 0 := by
        simp
      have hcoordi : (a • y + c • z) i.succ = a * y i.succ + c * z i.succ := by
        simp
      rw [hcoord0, hcoordi]
      have hweighted :
          a * (b i : ℝ) + c * (b i : ℝ) ≤
            a * (y 0 + y i.succ) + c * (z 0 + z i.succ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hyi ha) (mul_le_mul_of_nonneg_left hzi hc)
      have htarget :
          (b i : ℝ) ≤ a * y 0 + c * z 0 + (a * y i.succ + c * z i.succ) := by
        have hleft : a * (b i : ℝ) + c * (b i : ℝ) = (b i : ℝ) := by
          calc
            a * (b i : ℝ) + c * (b i : ℝ) = (a + c) * (b i : ℝ) := by ring
            _ = (b i : ℝ) := by rw [hac, one_mul]
        have hright :
            a * (y 0 + y i.succ) + c * (z 0 + z i.succ) =
              a * y 0 + c * z 0 + (a * y i.succ + c * z i.succ) := by
          ring
        rw [hleft, hright] at hweighted
        exact hweighted
      exact htarget
  have hxP : x ∈ P := by
    -- Pass from the generators to their convex hull inside the convex relaxation.
    change x ∈ convexHull ℝ (mixingSet b) at hx
    exact convexHull_min hsubset hconv hx
  simpa [P, mem_exercise_3_29_polyhedron_iff] using hxP

/-- Helper for Proposition 4.33: the last-occurrence candidate is itself a feasible mixed-integer
point. -/
lemma mixingVertexCandidate_mem_mixingSet_of_last_occurrence
    {b : Fin n → ℚ} {t : Fin (n + 1)}
    (hmono : Monotone (extendedMixingFractionalPart b))
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) :
    mixingVertexCandidate b t ∈ mixingSet b := by
  -- The zeroth coordinate is `f_t`, the tail coordinates are integral floors/ceilings, and the
  -- covering inequalities reduce to the defining ceiling bound.
  rw [mem_mixingSet_iff_forall]
  refine ⟨extendedMixingFractionalPart_nonneg t, ?_, ?_⟩
  · intro i
    rw [mixingVertexCandidate_apply_succ]
    by_cases hi : i.succ ≤ t
    · exact ⟨⌊b i⌋, by simp [hi]⟩
    · exact ⟨⌈b i⌉, by simp [hi]⟩
  · intro i
    rw [mixingVertexCandidate_apply_zero,
      mixingVertexCandidate_succ_eq_ceil_sub_of_last_occurrence hmono hlast i]
    have hceil : (b i : ℝ) - extendedMixingFractionalPart b t ≤
        (⌈(b i : ℝ) - extendedMixingFractionalPart b t⌉ : ℝ) := Int.le_ceil _
    linarith

/-- Helper for Proposition 4.33: on the active face indexed by `t`, a mixed-integer feasible point
has zeroth coordinate at least the fractional value `f_t`. -/
lemma mixingSet_zero_ge_fractional_of_active_face
    {b : Fin n → ℚ} {t : Fin (n + 1)} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b)
    (hface : Fin.cases (x 0 = 0) (fun k : Fin n ↦ x 0 + x k.succ = b k) t) :
    extendedMixingFractionalPart b t ≤ x 0 := by
  -- Split between the face `x₀ = 0` and the covering face `x₀ + x_t = b_t`.
  cases t using Fin.cases with
  | zero =>
      have hx0_eq : x 0 = 0 := by
        simpa using hface
      rw [extendedMixingFractionalPart_zero, hx0_eq]
  | succ k =>
    rw [mem_mixingSet_iff_forall] at hx
    rcases hx with ⟨hx0_nonneg, htail, _⟩
    rcases htail k with ⟨m, hm⟩
    have hface' : x 0 + x k.succ = (b k : ℝ) := by
      simpa using hface
    have hxk_le : x k.succ ≤ (b k : ℝ) := by
      linarith
    have hm_le_floor : m ≤ ⌊(b k : ℝ)⌋ := by
      apply Int.le_floor.mpr
      simpa [hm] using hxk_le
    have hfrac_eq :
        Int.fract (b k : ℝ) = (b k : ℝ) - (⌊(b k : ℝ)⌋ : ℝ) := by
      linarith [Int.floor_add_fract (b k : ℝ)]
    have hx0_eq : x 0 = (b k : ℝ) - (m : ℝ) := by
      linarith [hface', hm]
    have hm_le_floor_real : (m : ℝ) ≤ (⌊(b k : ℝ)⌋ : ℝ) := by
      exact_mod_cast hm_le_floor
    rw [extendedMixingFractionalPart_succ, mixingFractionalPart_eq_fract, hfrac_eq]
    linarith

/-- Helper for Proposition 4.33: once a mixed-integer feasible point has zeroth coordinate `f_t`,
every successor coordinate dominates the corresponding candidate coordinate. -/
lemma mixingSet_succ_ge_candidate_of_zero_eq_last_occurrence
    {b : Fin n → ℚ} {t : Fin (n + 1)} {x : Fin (n + 1) → ℝ}
    (hmono : Monotone (extendedMixingFractionalPart b))
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hx : x ∈ mixingSet b)
    (hzero : x 0 = extendedMixingFractionalPart b t) :
    ∀ i : Fin n, mixingVertexCandidate b t i.succ ≤ x i.succ := by
  -- The covering inequality bounds each integral successor coordinate below by the relevant
  -- ceiling, which is exactly the candidate value at the last occurrence.
  rw [mem_mixingSet_iff_forall] at hx
  rcases hx with ⟨_, htail, hineq⟩
  intro i
  rcases htail i with ⟨m, hm⟩
  have hceil_le : ⌈(b i : ℝ) - extendedMixingFractionalPart b t⌉ ≤ m := by
    apply Int.ceil_le.mpr
    have hi := hineq i
    have hsub : (b i : ℝ) - extendedMixingFractionalPart b t ≤ x i.succ := by
      rw [← hzero]
      linarith
    simpa [hm] using hsub
  have hceil_le_real :
      (⌈(b i : ℝ) - extendedMixingFractionalPart b t⌉ : ℝ) ≤ x i.succ := by
    have hceil_le_real' : (⌈(b i : ℝ) - extendedMixingFractionalPart b t⌉ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hceil_le
    simpa [hm] using hceil_le_real'
  rw [mixingVertexCandidate_succ_eq_ceil_sub_of_last_occurrence hmono hlast i]
  exact hceil_le_real

/-- Helper for Proposition 4.33: the candidate point `v^t` lies on the active face indexed by
`t`. -/
lemma mixingVertexCandidate_active_face
    {b : Fin n → ℚ} {t : Fin (n + 1)} :
    Fin.cases (mixingVertexCandidate b t 0 = 0)
      (fun k : Fin n ↦ mixingVertexCandidate b t 0 + mixingVertexCandidate b t k.succ = b k) t := by
  -- Split between the face `x₀ = 0` and the covering face `x₀ + x_t = b_t`.
  cases t using Fin.cases with
  | zero =>
      simp [extendedMixingFractionalPart_zero]
  | succ k =>
      simpa [mixingVertexCandidate_apply_zero, mixingVertexCandidate_apply_succ,
        extendedMixingFractionalPart_succ, mixingFractionalPart_eq_fract, add_comm] using
        (Int.floor_add_fract (b k : ℝ))

/-- Helper for Proposition 4.33: if a convex combination lies on the active face indexed by `t`,
then every positive-weight support point lies on the same face. -/
lemma positive_weight_support_on_active_face
    {b : Fin n → ℚ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} {z : ι → Fin (n + 1) → ℝ} {x : Fin (n + 1) → ℝ} {t : Fin (n + 1)}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ mixingSet b)
    (hsum : ∑ i, w i • z i = x)
    (hface : Fin.cases (x 0 = 0) (fun k : Fin n ↦ x 0 + x k.succ = b k) t) :
    ∀ i, 0 < w i →
      Fin.cases (z i 0 = 0) (fun k : Fin n ↦ z i 0 + z i k.succ = b k) t := by
  -- Compare the active-face equality of the barycenter with the nonnegative supportwise slacks.
  have hsum0 : ∑ i, w i * z i 0 = x 0 := by
    have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hsum
    simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
  cases t using Fin.cases with
  | zero =>
      have hx0_eq : x 0 = 0 := by
        simpa using hface
      have hsum_zero : ∑ i, w i * z i 0 = 0 := by
        rw [hsum0, hx0_eq]
      have hterm_zero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _hi ↦ by
            have hzi := hz i
            rw [mem_mixingSet_iff] at hzi
            exact mul_nonneg (hw₀ i) hzi.1)).1 hsum_zero
      intro i hwi
      have hzi := hz i
      rw [mem_mixingSet_iff] at hzi
      have hterm : w i * z i 0 = 0 := hterm_zero i (Finset.mem_univ i)
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hwi)
  | succ k =>
      have hsumk : ∑ i, w i * z i k.succ = x k.succ := by
        have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p k.succ) hsum
        simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
      have hxface : x 0 + x k.succ = (b k : ℝ) := by
        simpa using hface
      have hgap_sum : ∑ i, w i * (z i 0 + z i k.succ - (b k : ℝ)) = 0 := by
        calc
          ∑ i, w i * (z i 0 + z i k.succ - (b k : ℝ))
              = ∑ i, (w i * z i 0 + w i * z i k.succ - w i * (b k : ℝ)) := by
                  refine Finset.sum_congr rfl fun i _hi ↦ ?_
                  ring
          _ = ∑ i, (w i * z i 0 + w i * z i k.succ) - ∑ i, w i * (b k : ℝ) := by
                rw [Finset.sum_sub_distrib]
          _ = (∑ i, w i * z i 0) + (∑ i, w i * z i k.succ) - ∑ i, w i * (b k : ℝ) := by
                rw [Finset.sum_add_distrib]
          _ = x 0 + x k.succ - (∑ i, w i) * (b k : ℝ) := by
                rw [hsum0, hsumk, Finset.sum_mul]
          _ = 0 := by
                rw [hw₁]
                linarith
      have hterm_zero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _hi ↦ by
            have hzi := hz i
            rw [mem_mixingSet_iff] at hzi
            apply mul_nonneg (hw₀ i)
            linarith [hzi.2.2 k])).1 hgap_sum
      intro i hwi
      have hzi := hz i
      rw [mem_mixingSet_iff] at hzi
      have hterm : w i * (z i 0 + z i k.succ - (b k : ℝ)) = 0 := hterm_zero i (Finset.mem_univ i)
      have hslack_nonneg : 0 ≤ z i 0 + z i k.succ - (b k : ℝ) := by
        linarith [hzi.2.2 k]
      have hslack_eq : z i 0 + z i k.succ - (b k : ℝ) = 0 := by
        exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hwi)
      exact sub_eq_zero.mp hslack_eq

/-- Helper for Proposition 4.33: a segment decomposition of the candidate keeps both endpoints on
the same active face. -/
lemma segment_endpoints_on_candidate_active_face
    {b : Fin n → ℚ} {t : Fin (n + 1)}
    {y z : Fin (n + 1) → ℝ}
    (hy : y ∈ mixingHull b) (hz : z ∈ mixingHull b)
    (hseg : mixingVertexCandidate b t ∈ openSegment ℝ y z) :
    Fin.cases (y 0 = 0) (fun k : Fin n ↦ y 0 + y k.succ = b k) t ∧
      Fin.cases (z 0 = 0) (fun k : Fin n ↦ z 0 + z k.succ = b k) t := by
  -- The candidate already lies on the active face, and the endpoint slacks are nonnegative.
  rcases mem_openSegment_iff_div.mp hseg with ⟨a, c, ha, hc, hcomb⟩
  let α : ℝ := a / (a + c)
  let β : ℝ := c / (a + c)
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hβ_pos : 0 < β := by
    dsimp [β]
    positivity
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    have hsum_pos : 0 < a + c := add_pos ha hc
    rw [← add_div, div_self hsum_pos.ne']
  have hyrel := mixingHull_mem_relaxation hy
  have hzrel := mixingHull_mem_relaxation hz
  cases t using Fin.cases with
  | zero =>
      have hcoord0 :
          α * y 0 + β * z 0 = mixingVertexCandidate b 0 0 := by
        have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hcomb
        simpa [α, β, Pi.smul_apply] using hcoord
      have hcand0 : mixingVertexCandidate b 0 0 = 0 := by
        simp [extendedMixingFractionalPart_zero]
      have hy0_eq : y 0 = 0 := by
        rw [hcand0] at hcoord0
        have hαy_nonpos : α * y 0 ≤ 0 := by
          nlinarith [hcoord0, mul_nonneg hβ_pos.le hzrel.1]
        have hαy_eq : α * y 0 = 0 := by
          exact le_antisymm hαy_nonpos (mul_nonneg hα_pos.le hyrel.1)
        nlinarith [hα_pos, hαy_eq]
      have hz0_eq : z 0 = 0 := by
        rw [hcand0] at hcoord0
        have hβz_nonpos : β * z 0 ≤ 0 := by
          nlinarith [hcoord0, mul_nonneg hα_pos.le hyrel.1]
        have hβz_eq : β * z 0 = 0 := by
          exact le_antisymm hβz_nonpos (mul_nonneg hβ_pos.le hzrel.1)
        nlinarith [hβ_pos, hβz_eq]
      exact ⟨hy0_eq, hz0_eq⟩
  | succ k =>
      have hcoord0 :
          α * y 0 + β * z 0 = mixingVertexCandidate b k.succ 0 := by
        have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hcomb
        simpa [α, β, Pi.smul_apply] using hcoord
      have hcoordk :
          α * y k.succ + β * z k.succ = mixingVertexCandidate b k.succ k.succ := by
        have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p k.succ) hcomb
        simpa [α, β, Pi.smul_apply] using hcoord
      have hcand_face :
          mixingVertexCandidate b k.succ 0 + mixingVertexCandidate b k.succ k.succ = (b k : ℝ) := by
        simpa using (mixingVertexCandidate_active_face (b := b) (t := k.succ))
      have hface_sum :
          α * (y 0 + y k.succ) + β * (z 0 + z k.succ) = (b k : ℝ) := by
        calc
          α * (y 0 + y k.succ) + β * (z 0 + z k.succ)
              = (α * y 0 + β * z 0) + (α * y k.succ + β * z k.succ) := by ring
          _ = mixingVertexCandidate b k.succ 0 + mixingVertexCandidate b k.succ k.succ := by
                rw [hcoord0, hcoordk]
          _ = (b k : ℝ) := hcand_face
      have hyface : y 0 + y k.succ = (b k : ℝ) := by
        have hygap_nonneg : 0 ≤ y 0 + y k.succ - (b k : ℝ) := by
          linarith [hyrel.2 k]
        have hzgap_nonneg : 0 ≤ z 0 + z k.succ - (b k : ℝ) := by
          linarith [hzrel.2 k]
        have hgap_eq :
            α * (y 0 + y k.succ - (b k : ℝ)) +
              β * (z 0 + z k.succ - (b k : ℝ)) = 0 := by
          calc
            α * (y 0 + y k.succ - (b k : ℝ)) +
                β * (z 0 + z k.succ - (b k : ℝ))
                = α * (y 0 + y k.succ) + β * (z 0 + z k.succ) - (α + β) * (b k : ℝ) := by ring
            _ = (b k : ℝ) - (α + β) * (b k : ℝ) := by rw [hface_sum]
            _ = 0 := by rw [hαβ]; ring
        have hαgap_nonpos : α * (y 0 + y k.succ - (b k : ℝ)) ≤ 0 := by
          nlinarith [hgap_eq, mul_nonneg hβ_pos.le hzgap_nonneg]
        have hαgap_eq : α * (y 0 + y k.succ - (b k : ℝ)) = 0 := by
          exact le_antisymm hαgap_nonpos (mul_nonneg hα_pos.le hygap_nonneg)
        have hygap_eq' : y 0 + y k.succ - (b k : ℝ) = 0 := by
          exact (mul_eq_zero.mp hαgap_eq).resolve_left (ne_of_gt hα_pos)
        linarith
      have hzface : z 0 + z k.succ = (b k : ℝ) := by
        have hygap_nonneg : 0 ≤ y 0 + y k.succ - (b k : ℝ) := by
          linarith [hyrel.2 k]
        have hzgap_nonneg : 0 ≤ z 0 + z k.succ - (b k : ℝ) := by
          linarith [hzrel.2 k]
        have hgap_eq :
            α * (y 0 + y k.succ - (b k : ℝ)) +
              β * (z 0 + z k.succ - (b k : ℝ)) = 0 := by
          calc
            α * (y 0 + y k.succ - (b k : ℝ)) +
                β * (z 0 + z k.succ - (b k : ℝ))
                = α * (y 0 + y k.succ) + β * (z 0 + z k.succ) - (α + β) * (b k : ℝ) := by ring
            _ = (b k : ℝ) - (α + β) * (b k : ℝ) := by rw [hface_sum]
            _ = 0 := by rw [hαβ]; ring
        have hβgap_nonpos : β * (z 0 + z k.succ - (b k : ℝ)) ≤ 0 := by
          nlinarith [hgap_eq, mul_nonneg hα_pos.le hygap_nonneg]
        have hβgap_eq : β * (z 0 + z k.succ - (b k : ℝ)) = 0 := by
          exact le_antisymm hβgap_nonpos (mul_nonneg hβ_pos.le hzgap_nonneg)
        have hzgap_eq' : z 0 + z k.succ - (b k : ℝ) = 0 := by
          exact (mul_eq_zero.mp hβgap_eq).resolve_left (ne_of_gt hβ_pos)
        linarith
      exact ⟨hyface, hzface⟩

/-- Helper for Proposition 4.33: on the hull, the active face indexed by `t` still forces the
zeroth coordinate to be at least `f_t`. -/
lemma mixingHull_zero_ge_fractional_of_active_face
    {b : Fin n → ℚ} {t : Fin (n + 1)} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b)
    (hface : Fin.cases (x 0 = 0) (fun k : Fin n ↦ x 0 + x k.succ = b k) t) :
    extendedMixingFractionalPart b t ≤ x 0 := by
  classical
  -- Unpack the hull point into a finite convex combination and push the face equality to the
  -- positive-weight support points.
  cases t using Fin.cases with
  | zero =>
      have hx0_eq : x 0 = 0 := by
        simpa using hface
      rw [extendedMixingFractionalPart_zero, hx0_eq]
  | succ k =>
      rw [mixingHull, mem_convexHull_iff_exists_fintype] at hx
      rcases hx with ⟨ι, _, w, z, hw₀, hw₁, hz, hsum⟩
      have hsupport_face :=
        positive_weight_support_on_active_face (b := b) hw₀ hw₁ hz hsum hface
      have hsum0 : ∑ i, w i * z i 0 = x 0 := by
        have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hsum
        simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
      have hsum_le :
          ∑ i, w i * extendedMixingFractionalPart b k.succ ≤ ∑ i, w i * z i 0 := by
        apply Finset.sum_le_sum
        intro i _hi
        by_cases hwi : w i = 0
        · simp [hwi]
        · have hwi_ne : 0 ≠ w i := by
            exact fun h0 ↦ hwi h0.symm
          have hwi_pos : 0 < w i := lt_of_le_of_ne (hw₀ i) hwi_ne
          have hfrac_le :
              extendedMixingFractionalPart b k.succ ≤ z i 0 := by
            exact
              mixingSet_zero_ge_fractional_of_active_face (hx := hz i)
                (hface := by simpa using hsupport_face i hwi_pos)
          exact mul_le_mul_of_nonneg_left hfrac_le (hw₀ i)
      have hsum_frac :
          ∑ i, w i * extendedMixingFractionalPart b k.succ =
            extendedMixingFractionalPart b k.succ := by
        calc
          ∑ i, w i * extendedMixingFractionalPart b k.succ =
              (∑ i, w i) * extendedMixingFractionalPart b k.succ := by
                rw [Finset.sum_mul]
          _ = extendedMixingFractionalPart b k.succ := by
                rw [hw₁, one_mul]
      calc
        extendedMixingFractionalPart b k.succ = ∑ i, w i * extendedMixingFractionalPart b k.succ :=
          hsum_frac.symm
        _ ≤ ∑ i, w i * z i 0 := hsum_le
        _ = x 0 := hsum0

/-- Helper for Proposition 4.33: on the hull, once the zeroth coordinate equals `f_t`, every
successor coordinate dominates the candidate coordinate. -/
lemma mixingHull_succ_ge_candidate_of_active_face_and_zero_eq
    {b : Fin n → ℚ} {t : Fin (n + 1)} {x : Fin (n + 1) → ℝ}
    (hmono : Monotone (extendedMixingFractionalPart b))
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hx : x ∈ mixingHull b)
    (hface : Fin.cases (x 0 = 0) (fun k : Fin n ↦ x 0 + x k.succ = b k) t)
    (hzero : x 0 = extendedMixingFractionalPart b t) :
    ∀ i : Fin n, mixingVertexCandidate b t i.succ ≤ x i.succ := by
  classical
  -- First pin every positive-weight support point to zeroth coordinate `f_t`, then compare the
  -- successor coordinates supportwise and sum back up.
  rw [mixingHull, mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, _, w, z, hw₀, hw₁, hz, hsum⟩
  have hsupport_face :=
    positive_weight_support_on_active_face (b := b) hw₀ hw₁ hz hsum hface
  have hsum0 : ∑ j, w j * z j 0 = x 0 := by
    have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hsum
    simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
  have hterm_nonneg :
      ∀ j, 0 ≤ w j * (z j 0 - extendedMixingFractionalPart b t) := by
    intro j
    by_cases hwj : w j = 0
    · simp [hwj]
    · have hwj_ne : 0 ≠ w j := by
        exact fun h0 ↦ hwj h0.symm
      have hwj_pos : 0 < w j := lt_of_le_of_ne (hw₀ j) hwj_ne
      have hfrac_le :
          extendedMixingFractionalPart b t ≤ z j 0 := by
        exact
          mixingSet_zero_ge_fractional_of_active_face (hx := hz j)
            (hface := by simpa using hsupport_face j hwj_pos)
      exact mul_nonneg (hw₀ j) (sub_nonneg.mpr hfrac_le)
  have hterm_sum :
      ∑ j, w j * (z j 0 - extendedMixingFractionalPart b t) = 0 := by
    calc
      ∑ j, w j * (z j 0 - extendedMixingFractionalPart b t)
          = ∑ j, (w j * z j 0 - w j * extendedMixingFractionalPart b t) := by
              refine Finset.sum_congr rfl fun j _hj ↦ ?_
              ring
      _ = (∑ j, w j * z j 0) - ∑ j, w j * extendedMixingFractionalPart b t := by
            rw [Finset.sum_sub_distrib]
      _ = x 0 - (∑ j, w j) * extendedMixingFractionalPart b t := by
            rw [hsum0, Finset.sum_mul]
      _ = 0 := by
            rw [hw₁, hzero]
            ring
  have hterm_zero :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _hj ↦ hterm_nonneg j)).1 hterm_sum
  have hsupport_zero :
      ∀ j, 0 < w j → z j 0 = extendedMixingFractionalPart b t := by
    intro j hwj_pos
    have hfrac_le :
        extendedMixingFractionalPart b t ≤ z j 0 := by
      exact
        mixingSet_zero_ge_fractional_of_active_face (hx := hz j)
          (hface := by simpa using hsupport_face j hwj_pos)
    have hterm : w j * (z j 0 - extendedMixingFractionalPart b t) = 0 := hterm_zero j (Finset.mem_univ j)
    have hdiff_nonneg : 0 ≤ z j 0 - extendedMixingFractionalPart b t := by
      exact sub_nonneg.mpr hfrac_le
    have hdiff_eq : z j 0 - extendedMixingFractionalPart b t = 0 := by
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hwj_pos)
    linarith
  intro i
  have hsumi : ∑ j, w j * z j i.succ = x i.succ := by
    have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p i.succ) hsum
    simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
  have hsum_le :
      ∑ j, w j * mixingVertexCandidate b t i.succ ≤ ∑ j, w j * z j i.succ := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hwj : w j = 0
    · simp [hwj]
    · have hwj_ne : 0 ≠ w j := by
        exact fun h0 ↦ hwj h0.symm
      have hwj_pos : 0 < w j := lt_of_le_of_ne (hw₀ j) hwj_ne
      have hcoord_le :
          mixingVertexCandidate b t i.succ ≤ z j i.succ := by
        exact
          mixingSet_succ_ge_candidate_of_zero_eq_last_occurrence hmono hlast (hz j)
            (hsupport_zero j hwj_pos) i
      exact mul_le_mul_of_nonneg_left hcoord_le (hw₀ j)
  have hsum_candidate :
      ∑ j, w j * mixingVertexCandidate b t i.succ = mixingVertexCandidate b t i.succ := by
    calc
      ∑ j, w j * mixingVertexCandidate b t i.succ =
          (∑ j, w j) * mixingVertexCandidate b t i.succ := by
            rw [Finset.sum_mul]
      _ = mixingVertexCandidate b t i.succ := by
            rw [hw₁, one_mul]
  calc
    mixingVertexCandidate b t i.succ = ∑ j, w j * mixingVertexCandidate b t i.succ :=
      hsum_candidate.symm
    _ ≤ ∑ j, w j * z j i.succ := hsum_le
    _ = x i.succ := hsumi

/-- Helper for Proposition 4.33: a vertex of `P^mix` can only occur at one of the prescribed
fractional values. -/
lemma extreme_point_zero_mem_range_extendedMixingFractionalPart
    {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ (mixingHull b).extremePoints ℝ) :
    x 0 ∈ Set.range (extendedMixingFractionalPart b) := by
  by_contra hx0_not_mem
  have hxmix : x ∈ mixingSet b := extremePoints_convexHull_subset hx
  rw [mem_mixingSet_iff] at hxmix
  rcases hxmix with ⟨hx0_nonneg, htail, _hineq⟩
  have hx0_lt_one : x 0 < 1 := extreme_point_zero_lt_one hx
  obtain ⟨ε, hε_pos, hε_lt_x0, hx0_add_ε_lt_one, hmargin⟩ :=
    exists_positive_margin_away_from_extended_fractional_values
      hx0_nonneg hx0_lt_one hx0_not_mem
  let r : Fin (n + 1) → ℝ := Fin.cases ε fun _ : Fin n ↦ 0
  let y : Fin (n + 1) → ℝ := x - r
  let z : Fin (n + 1) → ℝ := x + r
  have hy_mix : y ∈ mixingSet b := by
    -- Perturb only `x₀` downward; the tail stays fixed and the ceiling branch does not change.
    rw [mem_mixingSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hy0 : y 0 = x 0 - ε := by
        simp [y, r]
      linarith
    · rw [mem_integerVectors_iff_forall] at htail ⊢
      intro i
      rcases htail i with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      simp [y, r, hm, sub_eq_add_neg]
    · intro i
      have hy0 : y 0 = x 0 - ε := by
        simp [y, r]
      have hyi : y i.succ = x i.succ := by
        simp [y, r, sub_eq_add_neg]
      have hdist :
          ε < |x 0 - mixingFractionalPart b i| := by
        simpa [extendedMixingFractionalPart_succ] using hmargin i.succ
      have hbranch :
          mixingFractionalPart b i ≤ x 0 - ε ↔ mixingFractionalPart b i ≤ x 0 := by
        by_cases hle : mixingFractionalPart b i ≤ x 0
        · have hleft : mixingFractionalPart b i ≤ x 0 - ε := by
            have habs :
                |x 0 - mixingFractionalPart b i| = x 0 - mixingFractionalPart b i := by
              exact abs_of_nonneg (sub_nonneg.mpr hle)
            rw [habs] at hdist
            linarith
          constructor
          · intro h
            linarith
          · intro _
            exact hleft
        · have hgt : x 0 < mixingFractionalPart b i := lt_of_not_ge hle
          have hnot_left : ¬ mixingFractionalPart b i ≤ x 0 - ε := by
            intro hleft
            linarith
          constructor
          · intro hleft
            exact False.elim (hnot_left hleft)
          · intro hright
            exact False.elim (hle hright)
      have hyceil :
          y i.succ = (⌈(b i : ℝ) - y 0⌉ : ℝ) := by
        rw [hyi, extreme_point_succ_eq_ceil_sub_zero hx i, hy0]
        have hy0_nonneg : 0 ≤ x 0 - ε := by
          linarith
        have hy0_lt_one : x 0 - ε < 1 := by
          linarith
        rw [ceil_sub_eq_floor_or_ceil_by_fract hy0_nonneg hy0_lt_one i,
          ceil_sub_eq_floor_or_ceil_by_fract hx0_nonneg hx0_lt_one i]
        by_cases hif : mixingFractionalPart b i ≤ x 0
        · rw [if_pos hif, if_pos (hbranch.2 hif)]
        · have hif' : ¬ mixingFractionalPart b i ≤ x 0 - ε := by
            intro hs
            exact hif (hbranch.1 hs)
          rw [if_neg hif, if_neg hif']
      have hle : (b i : ℝ) - y 0 ≤ y i.succ := by
        rw [hyceil]
        exact Int.le_ceil _
      linarith
  have hz_mix : z ∈ mixingSet b := by
    -- The same branch stability shows that the upward perturbation stays feasible.
    rw [mem_mixingSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hz0 : z 0 = x 0 + ε := by
        simp [z, r]
      linarith
    · rw [mem_integerVectors_iff_forall] at htail ⊢
      intro i
      rcases htail i with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      simp [z, r, hm]
    · intro i
      have hz0 : z 0 = x 0 + ε := by
        simp [z, r]
      have hzi : z i.succ = x i.succ := by
        simp [z, r]
      have hdist :
          ε < |x 0 - mixingFractionalPart b i| := by
        simpa [extendedMixingFractionalPart_succ] using hmargin i.succ
      have hbranch :
          mixingFractionalPart b i ≤ x 0 + ε ↔ mixingFractionalPart b i ≤ x 0 := by
        by_cases hle : mixingFractionalPart b i ≤ x 0
        · constructor
          · intro _
            exact hle
          · intro hright
            linarith
        · have hgt : x 0 < mixingFractionalPart b i := lt_of_not_ge hle
          have hnot_left : ¬ mixingFractionalPart b i ≤ x 0 + ε := by
            have habs :
                |x 0 - mixingFractionalPart b i| = -(x 0 - mixingFractionalPart b i) := by
              exact abs_of_nonpos (sub_nonpos.mpr (le_of_lt hgt))
            rw [habs] at hdist
            intro hleft
            linarith
          constructor
          · intro hleft
            exact False.elim (hnot_left hleft)
          · intro hright
            exact False.elim (hle hright)
      have hzceil :
          z i.succ = (⌈(b i : ℝ) - z 0⌉ : ℝ) := by
        rw [hzi, extreme_point_succ_eq_ceil_sub_zero hx i, hz0]
        have hz0_nonneg : 0 ≤ x 0 + ε := by
          linarith
        rw [ceil_sub_eq_floor_or_ceil_by_fract hz0_nonneg hx0_add_ε_lt_one i,
          ceil_sub_eq_floor_or_ceil_by_fract hx0_nonneg hx0_lt_one i]
        by_cases hif : mixingFractionalPart b i ≤ x 0
        · rw [if_pos hif, if_pos (hbranch.2 hif)]
        · have hif' : ¬ mixingFractionalPart b i ≤ x 0 + ε := by
            intro hs
            exact hif (hbranch.1 hs)
          rw [if_neg hif, if_neg hif']
      have hle : (b i : ℝ) - z 0 ≤ z i.succ := by
        rw [hzceil]
        exact Int.le_ceil _
      linarith
  have hy_hull : y ∈ mixingHull b := by
    change y ∈ convexHull ℝ (mixingSet b)
    exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hy_mix
  have hz_hull : z ∈ mixingHull b := by
    change z ∈ convexHull ℝ (mixingSet b)
    exact (subset_convexHull (𝕜 := ℝ) (s := mixingSet b)) hz_mix
  have hseg : x ∈ openSegment ℝ y z := by
    -- The original point is the midpoint of the two zeroth-coordinate perturbations.
    simpa [y, z, r] using (mem_openSegment_sub_add (𝕜 := ℝ) x r)
  have hy_eq : y = x := (mem_extremePoints_iff_left.mp hx).2 y hy_hull z hz_hull hseg
  have hy0 : y 0 = x 0 - ε := by
    simp [y, r]
  have hy0_eq : y 0 = x 0 := congrArg (fun p ↦ p 0) hy_eq
  linarith

/-- Helper for Proposition 4.33: the candidate attached to the last occurrence of a fractional
value is a vertex of `P^mix`. -/
lemma mixing_vertex_candidate_mem_extreme_points_of_last_occurrence
    {b : Fin n → ℚ} {t : Fin (n + 1)}
    (hmono : Monotone (extendedMixingFractionalPart b))
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) :
    mixingVertexCandidate b t ∈ (mixingHull b).extremePoints ℝ := by
  -- Route correction: the generator-level face analysis only yields the lower bound `f_t ≤ x₀`
  -- on the active face. The hull step must therefore first force every segment endpoint back down
  -- to `x₀ = f_t`, and only then upgrade to the coordinatewise candidate bounds.
  have hxmix : mixingVertexCandidate b t ∈ mixingSet b :=
    mixingVertexCandidate_mem_mixingSet_of_last_occurrence hmono hlast
  have hxhull : mixingVertexCandidate b t ∈ mixingHull b := by
    change mixingVertexCandidate b t ∈ convexHull ℝ (mixingSet b)
    exact subset_convexHull (𝕜 := ℝ) (s := mixingSet b) hxmix
  rw [mem_extremePoints_iff_left]
  refine ⟨hxhull, ?_⟩
  intro y hy z hz hseg
  -- Push the candidate active-face equality to the endpoints, then collapse each coordinate using
  -- the hull lower bounds and the strict convex-combination identity.
  have hfaces := segment_endpoints_on_candidate_active_face hy hz hseg
  rcases hfaces with ⟨hyface, hzface⟩
  have hy0_ge :
      extendedMixingFractionalPart b t ≤ y 0 := by
    exact mixingHull_zero_ge_fractional_of_active_face hy hyface
  have hz0_ge :
      extendedMixingFractionalPart b t ≤ z 0 := by
    exact mixingHull_zero_ge_fractional_of_active_face hz hzface
  rcases mem_openSegment_iff_div.mp hseg with ⟨a, c, ha, hc, hcomb⟩
  let α : ℝ := a / (a + c)
  let β : ℝ := c / (a + c)
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hβ_pos : 0 < β := by
    dsimp [β]
    positivity
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    have hsum_pos : 0 < a + c := add_pos ha hc
    rw [← add_div, div_self hsum_pos.ne']
  have hcoord0 :
      α * y 0 + β * z 0 = extendedMixingFractionalPart b t := by
    have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p 0) hcomb
    simpa [α, β, mixingVertexCandidate_apply_zero, Pi.smul_apply] using hcoord
  have hy0_eq : y 0 = extendedMixingFractionalPart b t := by
    have hygap_nonneg : 0 ≤ y 0 - extendedMixingFractionalPart b t := by
      exact sub_nonneg.mpr hy0_ge
    have hzgap_nonneg : 0 ≤ z 0 - extendedMixingFractionalPart b t := by
      exact sub_nonneg.mpr hz0_ge
    have hgap_eq :
        α * (y 0 - extendedMixingFractionalPart b t) +
          β * (z 0 - extendedMixingFractionalPart b t) = 0 := by
      calc
        α * (y 0 - extendedMixingFractionalPart b t) +
            β * (z 0 - extendedMixingFractionalPart b t)
            = α * y 0 + β * z 0 - (α + β) * extendedMixingFractionalPart b t := by ring
        _ = extendedMixingFractionalPart b t -
              (α + β) * extendedMixingFractionalPart b t := by rw [hcoord0]
        _ = 0 := by rw [hαβ]; ring
    have hαgap_nonpos : α * (y 0 - extendedMixingFractionalPart b t) ≤ 0 := by
      nlinarith [hgap_eq, mul_nonneg hβ_pos.le hzgap_nonneg]
    have hαgap_eq : α * (y 0 - extendedMixingFractionalPart b t) = 0 := by
      exact le_antisymm hαgap_nonpos (mul_nonneg hα_pos.le hygap_nonneg)
    have hygap_eq' : y 0 - extendedMixingFractionalPart b t = 0 := by
      exact (mul_eq_zero.mp hαgap_eq).resolve_left (ne_of_gt hα_pos)
    linarith
  have hz0_eq : z 0 = extendedMixingFractionalPart b t := by
    have hygap_nonneg : 0 ≤ y 0 - extendedMixingFractionalPart b t := by
      exact sub_nonneg.mpr hy0_ge
    have hzgap_nonneg : 0 ≤ z 0 - extendedMixingFractionalPart b t := by
      exact sub_nonneg.mpr hz0_ge
    have hgap_eq :
        α * (y 0 - extendedMixingFractionalPart b t) +
          β * (z 0 - extendedMixingFractionalPart b t) = 0 := by
      calc
        α * (y 0 - extendedMixingFractionalPart b t) +
            β * (z 0 - extendedMixingFractionalPart b t)
            = α * y 0 + β * z 0 - (α + β) * extendedMixingFractionalPart b t := by ring
        _ = extendedMixingFractionalPart b t -
              (α + β) * extendedMixingFractionalPart b t := by rw [hcoord0]
        _ = 0 := by rw [hαβ]; ring
    have hβgap_nonpos : β * (z 0 - extendedMixingFractionalPart b t) ≤ 0 := by
      nlinarith [hgap_eq, mul_nonneg hα_pos.le hygap_nonneg]
    have hβgap_eq : β * (z 0 - extendedMixingFractionalPart b t) = 0 := by
      exact le_antisymm hβgap_nonpos (mul_nonneg hβ_pos.le hzgap_nonneg)
    have hzgap_eq' : z 0 - extendedMixingFractionalPart b t = 0 := by
      exact (mul_eq_zero.mp hβgap_eq).resolve_left (ne_of_gt hβ_pos)
    linarith
  have hy_succ_ge :
      ∀ i : Fin n, mixingVertexCandidate b t i.succ ≤ y i.succ := by
    exact mixingHull_succ_ge_candidate_of_active_face_and_zero_eq hmono hlast hy hyface hy0_eq
  have hz_succ_ge :
      ∀ i : Fin n, mixingVertexCandidate b t i.succ ≤ z i.succ := by
    exact mixingHull_succ_ge_candidate_of_active_face_and_zero_eq hmono hlast hz hzface hz0_eq
  ext j
  refine Fin.cases hy0_eq ?_ j
  intro i
  have hcoordi :
      α * y i.succ + β * z i.succ = mixingVertexCandidate b t i.succ := by
    have hcoord := congrArg (fun p : Fin (n + 1) → ℝ ↦ p i.succ) hcomb
    simpa [α, β, Pi.smul_apply] using hcoord
  have hyi_eq : y i.succ = mixingVertexCandidate b t i.succ := by
    have hygap_nonneg : 0 ≤ y i.succ - mixingVertexCandidate b t i.succ := by
      exact sub_nonneg.mpr (hy_succ_ge i)
    have hzgap_nonneg : 0 ≤ z i.succ - mixingVertexCandidate b t i.succ := by
      exact sub_nonneg.mpr (hz_succ_ge i)
    have hgap_eq :
        α * (y i.succ - mixingVertexCandidate b t i.succ) +
          β * (z i.succ - mixingVertexCandidate b t i.succ) = 0 := by
      calc
        α * (y i.succ - mixingVertexCandidate b t i.succ) +
            β * (z i.succ - mixingVertexCandidate b t i.succ)
            = α * y i.succ + β * z i.succ - (α + β) * mixingVertexCandidate b t i.succ := by ring
        _ = mixingVertexCandidate b t i.succ -
              (α + β) * mixingVertexCandidate b t i.succ := by rw [hcoordi]
        _ = 0 := by rw [hαβ]; ring
    have hαgap_nonpos : α * (y i.succ - mixingVertexCandidate b t i.succ) ≤ 0 := by
      nlinarith [hgap_eq, mul_nonneg hβ_pos.le hzgap_nonneg]
    have hαgap_eq : α * (y i.succ - mixingVertexCandidate b t i.succ) = 0 := by
      exact le_antisymm hαgap_nonpos (mul_nonneg hα_pos.le hygap_nonneg)
    have hygap_eq' : y i.succ - mixingVertexCandidate b t i.succ = 0 := by
      exact (mul_eq_zero.mp hαgap_eq).resolve_left (ne_of_gt hα_pos)
    linarith
  exact hyi_eq

/-- Helper for Proposition 4.33: sending a vertex to its zeroth coordinate gives the upper-bound
count on the number of vertices. -/
lemma mixingHull_extremePoints_ncard_le_fractional_values_ncard
    (b : Fin n → ℚ) :
    ((mixingHull b).extremePoints ℝ).ncard ≤
      (Set.range (extendedMixingFractionalPart b)).ncard := by
  -- Distinct extreme points have distinct zeroth coordinates, and every such coordinate is one of
  -- the finitely many threshold values.
  refine Set.ncard_le_ncard_of_injOn
      (s := (mixingHull b).extremePoints ℝ)
      (t := Set.range (extendedMixingFractionalPart b))
      (f := fun x : Fin (n + 1) → ℝ ↦ x 0)
      (fun x hx ↦ ?_) ?_
  · exact extreme_point_zero_mem_range_extendedMixingFractionalPart hx
  · intro x hx y hy hxy
    exact extreme_point_eq_of_zero_eq hx hy hxy

/-- Proposition 4.33 (1). If the extended fractional-part vector
`(extendedMixingFractionalPart b 0, ..., extendedMixingFractionalPart b n)` is nondecreasing, then
the number of vertices of `P^mix` equals the number of distinct values in that sequence. -/
theorem mixingHull_extremePoints_ncard_eq_fractional_values_ncard
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b)) :
    ((mixingHull b).extremePoints ℝ).ncard =
      (Set.range (extendedMixingFractionalPart b)).ncard := by
  classical
  refine le_antisymm
    (mixingHull_extremePoints_ncard_le_fractional_values_ncard b) ?_
  -- Choose the last occurrence of each fractional value and send it to the corresponding
  -- candidate vertex; the zeroth coordinate recovers the original value.
  let lastIndex : ℝ → Fin (n + 1) := fun c ↦
    if hc : c ∈ Set.range (extendedMixingFractionalPart b) then
      Classical.choose (exists_last_index_of_mem_range
        (f := extendedMixingFractionalPart b) hc)
    else 0
  have hlastIndex_spec :
      ∀ {c : ℝ} (hc : c ∈ Set.range (extendedMixingFractionalPart b)),
        extendedMixingFractionalPart b (lastIndex c) = c ∧
          ∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s =
              extendedMixingFractionalPart b (lastIndex c) → s ≤ lastIndex c := by
    intro c hc
    dsimp [lastIndex]
    rw [dif_pos hc]
    exact
      let hchoose :=
        Classical.choose_spec
          (exists_last_index_of_mem_range (f := extendedMixingFractionalPart b) hc)
      ⟨hchoose.1, fun s hs ↦ hchoose.2 s (by simpa [hchoose.1] using hs)⟩
  have hsubset :
      (fun c : ℝ ↦ mixingVertexCandidate b (lastIndex c)) ''
          Set.range (extendedMixingFractionalPart b) ⊆
        (mixingHull b).extremePoints ℝ := by
    intro v hv
    rcases hv with ⟨c, hc, rfl⟩
    exact mixing_vertex_candidate_mem_extreme_points_of_last_occurrence hmono (hlastIndex_spec hc).2
  have hinj :
      Set.InjOn (fun c : ℝ ↦ mixingVertexCandidate b (lastIndex c))
        (Set.range (extendedMixingFractionalPart b)) := by
    intro c hc d hd hcd
    have hc0 : mixingVertexCandidate b (lastIndex c) 0 = c := by
      rw [mixingVertexCandidate_apply_zero, (hlastIndex_spec hc).1]
    have hd0 : mixingVertexCandidate b (lastIndex d) 0 = d := by
      rw [mixingVertexCandidate_apply_zero, (hlastIndex_spec hd).1]
    calc
      c = mixingVertexCandidate b (lastIndex c) 0 := hc0.symm
      _ = mixingVertexCandidate b (lastIndex d) 0 := congrArg (fun x : Fin (n + 1) → ℝ ↦ x 0) hcd
      _ = d := hd0
  have hfinite_extreme : ((mixingHull b).extremePoints ℝ).Finite := by
    refine Set.Finite.of_injOn
      (hm := fun x hx ↦ extreme_point_zero_mem_range_extendedMixingFractionalPart hx)
      (hi := ?_)
      (ht := Set.finite_range (extendedMixingFractionalPart b))
    intro x hx y hy hxy
    exact extreme_point_eq_of_zero_eq hx hy hxy
  calc
    (Set.range (extendedMixingFractionalPart b)).ncard =
        ((fun c : ℝ ↦ mixingVertexCandidate b (lastIndex c)) ''
          Set.range (extendedMixingFractionalPart b)).ncard := by
            symm
            exact hinj.ncard_image
    _ ≤ ((mixingHull b).extremePoints ℝ).ncard := Set.ncard_le_ncard hsubset hfinite_extreme

/-- Proposition 4.33 (2). Under the same ordered-fractional-part setup, every vertex of `P^mix`
is one of the `n + 1` candidate points `v^0, ..., v^n`. -/
theorem mixingHull_extremePoints_subset_range_mixingVertexCandidate
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b)) :
    (mixingHull b).extremePoints ℝ ⊆ Set.range (mixingVertexCandidate b) := by
  intro x hx
  rcases exists_last_index_of_mem_range
      (extreme_point_zero_mem_range_extendedMixingFractionalPart hx) with
    ⟨t, ht, hlast⟩
  have hlast' :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t := by
    intro s hs
    exact hlast s (by simpa [ht] using hs)
  refine ⟨t, ?_⟩
  -- Match the zeroth coordinate by construction and the tail via the common ceiling formula.
  ext j
  refine Fin.cases ?_ ?_ j
  · simpa using ht
  · intro i
    rw [extreme_point_succ_eq_ceil_sub_zero hx i,
      mixingVertexCandidate_succ_eq_ceil_sub_of_last_occurrence hmono hlast' i]
    simpa [ht]

end Proposition433
