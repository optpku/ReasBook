/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped Topology

section Chap03
section Section03

/-- Lemma 3.3.1. A continuous function `f : [a, b] → ℝ` is bounded. -/
lemma lemma_3_3_1 {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, by exact ⟨le_rfl, hle⟩⟩
  have hcompact_image : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hf
  have hnonempty_image : (f '' Set.Icc a b).Nonempty := hnonempty.image _
  have hcont_abs : ContinuousOn (fun y : ℝ => |y|) (f '' Set.Icc a b) :=
    continuous_abs.continuousOn
  obtain ⟨y, _, hy_max⟩ :=
    hcompact_image.exists_isMaxOn hnonempty_image hcont_abs
  have hy_max' :
      ∀ z ∈ f '' Set.Icc a b, |z| ≤ |y| := by
    -- eventually filter on a principal set corresponds to pointwise membership
    simpa [IsMaxOn, IsMaxFilter, Filter.eventually_principal] using hy_max
  refine ⟨|y|, ?_⟩
  intro x hx
  have hx_image : f x ∈ f '' Set.Icc a b := ⟨x, hx, rfl⟩
  exact hy_max' (f x) hx_image

/-- Helper lemma for Theorem 3.3.2: a continuous function reaches its minimum on `[a, b]`. -/
lemma theorem_3_3_2_min_helper {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x := by
  classical
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hle⟩⟩
  obtain ⟨c, hc, hc_min⟩ := hcompact.exists_isMinOn hnonempty hf
  exact ⟨c, hc, by simpa [isMinOn_iff] using hc_min⟩

/-- Helper lemma for Theorem 3.3.2: a continuous function reaches its maximum on `[a, b]`. -/
lemma theorem_3_3_2_max_helper {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d := by
  classical
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hle⟩⟩
  obtain ⟨d, hd, hd_max⟩ := hcompact.exists_isMaxOn hnonempty hf
  exact ⟨d, hd, by simpa [isMaxOn_iff] using hd_max⟩

/-- Theorem 3.3.2 (Minimum-maximum theorem / Extreme value theorem). A continuous function
`f : [a, b] → ℝ` attains an absolute minimum and an absolute maximum on `[a, b]`. -/
theorem theorem_3_3_2 {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x) ∧
      (∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d) := by
  refine ⟨theorem_3_3_2_min_helper hle hf, theorem_3_3_2_max_helper hle hf⟩

lemma example_3_3_3_min_bound (x : ℝ) :
    (fun x : ℝ => x ^ 2 + 1) 0 ≤ (fun x : ℝ => x ^ 2 + 1) x := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  simpa using add_le_add_right hx 1

lemma example_3_3_3_sq_le_4 {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) : x ^ 2 ≤ 4 := by
  have hmul : (x - 2) * (x + 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (by linarith [hx.1])
  have hsq : x ^ 2 - 4 ≤ 0 := by
    have hx_eq : (x - 2) * (x + 2) = x ^ 2 - 4 := by ring
    simpa [hx_eq] using hmul
  exact sub_nonpos.mp hsq

lemma example_3_3_3_sq_le_100 {x : ℝ} (hx : x ∈ Set.Icc (-10 : ℝ) 10) : x ^ 2 ≤ 100 := by
  have hmul : (x - 10) * (x + 10) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (by linarith [hx.1])
  have hsq : x ^ 2 - 100 ≤ 0 := by
    have hx_eq : (x - 10) * (x + 10) = x ^ 2 - 100 := by ring
    simpa [hx_eq] using hmul
  exact sub_nonpos.mp hsq

/-- Example 3.3.3. For `f x = x ^ 2 + 1` on `[-1, 2]`, the minimum is achieved at `x = 0`
with value `f 0 = 1` and the maximum at `x = 2` with value `f 2 = 5`. On the larger interval
`[-10, 10]`, the maximum occurs at the endpoints `x = 10` or `x = -10`. -/
lemma example_3_3_3 :
    (∀ x ∈ Set.Icc (-1 : ℝ) 2,
        (fun x : ℝ => x ^ 2 + 1) 0 ≤ (fun x : ℝ => x ^ 2 + 1) x) ∧
      (fun x : ℝ => x ^ 2 + 1) 0 = 1 ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 2,
        (fun x : ℝ => x ^ 2 + 1) x ≤ (fun x : ℝ => x ^ 2 + 1) 2) ∧
      (fun x : ℝ => x ^ 2 + 1) 2 = 5 ∧
      (∀ x ∈ Set.Icc (-10 : ℝ) 10,
        (fun x : ℝ => x ^ 2 + 1) x ≤ (fun x : ℝ => x ^ 2 + 1) 10) ∧
      (∀ x ∈ Set.Icc (-10 : ℝ) 10,
        (fun x : ℝ => x ^ 2 + 1) x ≤ (fun x : ℝ => x ^ 2 + 1) (-10)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa using example_3_3_3_min_bound x
  refine ⟨by simp, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx_sq : x ^ 2 ≤ 4 := example_3_3_3_sq_le_4 hx
    have hx_sq' : x ^ 2 + 1 ≤ 4 + 1 := by
      simpa [add_comm] using add_le_add_right hx_sq 1
    have hx_sq'' : x ^ 2 + 1 ≤ (2 : ℝ) ^ 2 + 1 := by
      convert hx_sq' using 1; norm_num
    simpa using hx_sq''
  refine ⟨by norm_num, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx_sq : x ^ 2 ≤ 100 := example_3_3_3_sq_le_100 hx
    have hx_sq' : x ^ 2 + 1 ≤ 100 + 1 := by
      simpa [add_comm] using add_le_add_right hx_sq 1
    have hx_sq'' : x ^ 2 + 1 ≤ (10 : ℝ) ^ 2 + 1 := by
      convert hx_sq' using 1; norm_num
    simpa using hx_sq''
  · intro x hx
    have hx_sq : x ^ 2 ≤ 100 := example_3_3_3_sq_le_100 hx
    have hx_sq' : x ^ 2 + 1 ≤ 100 + 1 := by
      simpa [add_comm] using add_le_add_right hx_sq 1
    have hx_sq'' : x ^ 2 + 1 ≤ (-10 : ℝ) ^ 2 + 1 := by
      convert hx_sq' using 1; norm_num
    simpa using hx_sq''

/-- Example 3.3.4. The identity function `f : ℝ → ℝ`, given by `f x = x`, achieves neither
a minimum nor a maximum on `ℝ`, illustrating that bounded intervals are required to guarantee
extrema. -/
lemma example_3_3_4 :
    (¬ ∃ c : ℝ, ∀ x : ℝ, (fun x : ℝ => x) c ≤ (fun x : ℝ => x) x) ∧
      (¬ ∃ d : ℝ, ∀ x : ℝ, (fun x : ℝ => x) x ≤ (fun x : ℝ => x) d) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨c, hc⟩
    have hc_le : c ≤ c - 1 := by
      simpa using hc (c - 1)
    have hcontr : c < c := lt_of_le_of_lt hc_le (sub_lt_self c zero_lt_one)
    exact lt_irrefl _ hcontr
  · intro h
    rcases h with ⟨d, hd⟩
    have hd_le : d + 1 ≤ d := by
      simpa using hd (d + 1)
    have hcontr : d < d := lt_of_lt_of_le (lt_add_one d) hd_le
    exact lt_irrefl _ hcontr

/-- Example 3.3.5. The function `f : (0, 1) → ℝ` given by `f x = 1 / x` is continuous on the
open interval but achieves neither a minimum nor a maximum. The values are unbounded as `x`
approaches `0`, while as `x → 1` the values tend to `1` with `f x > 1` for all `x ∈ (0, 1)`, so
no point of the domain yields the value `1`. This shows the need for a closed interval in the
extreme value theorem. -/
lemma example_3_3_5 :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / x) (Set.Ioo 0 1) ∧
      (¬ ∃ c ∈ Set.Ioo 0 1, ∀ x ∈ Set.Ioo 0 1,
        (fun x : ℝ => (1 : ℝ) / x) c ≤ (fun x : ℝ => (1 : ℝ) / x) x) ∧
      (¬ ∃ d ∈ Set.Ioo 0 1, ∀ x ∈ Set.Ioo 0 1,
        (fun x : ℝ => (1 : ℝ) / x) x ≤ (fun x : ℝ => (1 : ℝ) / x) d) ∧
      (∀ M : ℝ, ∃ x ∈ Set.Ioo 0 1, M ≤ (fun x : ℝ => (1 : ℝ) / x) x) ∧
      (∀ x ∈ Set.Ioo 0 1, 1 < (fun x : ℝ => (1 : ℝ) / x) x) ∧
      (∀ ε > 0, ∃ x ∈ Set.Ioo 0 1,
        |(fun x : ℝ => (1 : ℝ) / x) x - 1| < ε) := by
  have hcont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / x) (Set.Ioi (0 : ℝ)) := by
    have h :=
        (continuousOn_id : ContinuousOn (fun x : ℝ => x) (Set.Ioi (0 : ℝ)))
    have hne : ∀ x ∈ Set.Ioi (0 : ℝ), x ≠ 0 := fun x hx => ne_of_gt hx
    simpa [one_div] using h.inv₀ hne
  have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hx.1
  refine ⟨hcont.mono hsubset, ?_⟩
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨c, hc_mem, hc_le⟩
    have hc_pos : 0 < c := hc_mem.1
    have hc_lt_one : c < 1 := hc_mem.2
    let y : ℝ := (c + 1) / 2
    have hy_pos : 0 < y := by
      have hsum_pos : 0 < c + 1 := by linarith [hc_pos]
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      simpa [y] using div_pos hsum_pos htwo_pos
    have hy_lt_one : y < 1 := by
      have hsum_lt : c + 1 < (1 : ℝ) + 1 := by
        simpa [add_comm] using add_lt_add_right hc_lt_one 1
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      have hy :=
          div_lt_div_of_pos_right hsum_lt htwo_pos
      simpa [y] using hy
    have hy_gt_c : c < y := by
      have hlt : 2 * c < c + 1 := by
        have := add_lt_add_left hc_lt_one c
        simpa [add_comm, add_left_comm, add_assoc, two_mul] using this
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      have hy := div_lt_div_of_pos_right hlt htwo_pos
      simpa [y, two_mul, add_comm, add_left_comm, add_assoc] using hy
    have hy_mem : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy_pos, hy_lt_one⟩
    have hy_lt_value :
        (fun x : ℝ => (1 : ℝ) / x) y < (fun x : ℝ => (1 : ℝ) / x) c := by
      have hy_lt := one_div_lt_one_div_of_lt hc_pos hy_gt_c
      simpa [y] using hy_lt
    exact (not_le_of_gt hy_lt_value) (hc_le y hy_mem)
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨d, hd_mem, hd_le⟩
    have hd_pos : 0 < d := hd_mem.1
    have hd_lt_one : d < 1 := hd_mem.2
    let y : ℝ := d / 2
    have hy_pos : 0 < y := by
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      simpa [y] using div_pos hd_pos htwo_pos
    have hy_lt_one : y < 1 := by
      have hy_lt_half :
          y < (1 : ℝ) / 2 := by
        have htwo_pos : 0 < (2 : ℝ) := by norm_num
        have hy' := div_lt_div_of_pos_right hd_lt_one htwo_pos
        simpa [y] using hy'
      have hhalf_lt_one : (1 : ℝ) / 2 < 1 := by norm_num
      exact lt_of_lt_of_le hy_lt_half (le_of_lt hhalf_lt_one)
    have hy_lt_d : y < d := by
      simpa [y] using half_lt_self hd_pos
    have hy_mem : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy_pos, hy_lt_one⟩
    have hy_gt :
        (fun x : ℝ => (1 : ℝ) / x) d < (fun x : ℝ => (1 : ℝ) / x) y := by
      have hy_lt := one_div_lt_one_div_of_lt hy_pos hy_lt_d
      simpa [y] using hy_lt
    exact (not_le_of_gt hy_gt) (hd_le y hy_mem)
  refine ⟨?_, ?_⟩
  · intro M
    by_cases hM : M ≤ 0
    · refine ⟨(1 : ℝ) / 2, ?_, ?_⟩
      · exact ⟨by norm_num, by norm_num⟩
      · have hpos : 0 < (fun x : ℝ => (1 : ℝ) / x) ((1 : ℝ) / 2) := by norm_num
        exact hM.trans (le_of_lt hpos)
    · have hM_pos : 0 < M := lt_of_not_ge hM
      refine ⟨(1 : ℝ) / (M + 1), ?_, ?_⟩
      · have hden_pos : 0 < M + 1 := by linarith [hM_pos]
        have hx_pos : 0 < (1 : ℝ) / (M + 1) :=
          by simpa [one_div] using inv_pos.mpr hden_pos
        have hx_lt_one :
            (1 : ℝ) / (M + 1) < 1 := by
          have : (1 : ℝ) < M + 1 := by linarith [hM_pos]
          simpa [one_div] using
            (one_div_lt_one_div_of_lt zero_lt_one this)
        exact ⟨hx_pos, hx_lt_one⟩
      · have hval :
            (fun x : ℝ => (1 : ℝ) / x) ((1 : ℝ) / (M + 1)) = M + 1 := by
          simp [one_div]
        have hbound :
            M ≤ (fun x : ℝ => (1 : ℝ) / x) ((1 : ℝ) / (M + 1)) := by
          have hle : M ≤ M + 1 := by linarith [hM_pos]
          calc
            M ≤ M + 1 := hle
            _ = (fun x : ℝ => (1 : ℝ) / x) ((1 : ℝ) / (M + 1)) := hval.symm
        exact hbound
  refine ⟨?_, ?_⟩
  · intro x hx
    have hpos : 0 < x := hx.1
    have hlt : x < 1 := hx.2
    have hmult :
        x * ((1 : ℝ) / x) < 1 * ((1 : ℝ) / x) :=
      mul_lt_mul_of_pos_right hlt (by simpa [one_div] using inv_pos.mpr hpos)
    simpa [one_div, hpos.ne', mul_comm, mul_left_comm, mul_assoc] using hmult
  · have hcontAt :
        ContinuousAt (fun x : ℝ => (1 : ℝ) / x) 1 := by
      have h := (continuous_id : Continuous fun x : ℝ => x)
      have hne : ((fun x : ℝ => x) 1) ≠ 0 := by simp
      have hcont := h.continuousAt.inv₀ hne
      convert hcont using 1
      · simp [one_div]
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ :=
        (Metric.continuousAt_iff).1 hcontAt ε hε
    set δ' := min (δ / 2) ((1 : ℝ) / 2)
    have hδ'_pos : 0 < δ' := by
      have hδ_half_pos : 0 < δ / 2 := half_pos hδ_pos
      have hhalf_pos : 0 < (1 : ℝ) / 2 := by norm_num
      unfold δ'
      exact lt_min_iff.2 ⟨hδ_half_pos, hhalf_pos⟩
    have hδ'_le_halfδ : δ' ≤ δ / 2 := by
      unfold δ'
      exact min_le_left _ _
    have hδ'_lt_δ : δ' < δ := by
      have hlt : δ / 2 < δ := half_lt_self hδ_pos
      exact lt_of_le_of_lt hδ'_le_halfδ hlt
    have hδ'_le_half : δ' ≤ (1 : ℝ) / 2 := by
      unfold δ'
      exact min_le_right _ _
    set x := 1 - δ'
    have hx_lt_one : x < 1 := by
      simpa [x] using sub_lt_self (1 : ℝ) hδ'_pos
    have hx_pos : 0 < x := by
      have hδ_lt_one :
          δ' < 1 := lt_of_le_of_lt hδ'_le_half (by norm_num : (1 : ℝ) / 2 < 1)
      simpa [x] using sub_pos.mpr hδ_lt_one
    have hx_mem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx_pos, hx_lt_one⟩
    have hx_abs_one : |1 - x| = δ' := by
      have hx1 : 1 - x = δ' := by simp [x]
      simpa [hx1] using abs_of_nonneg (show 0 ≤ δ' from le_of_lt hδ'_pos)
    have hx_abs : |x - 1| = δ' := by
      simpa [abs_sub_comm] using hx_abs_one
    have hdist_lt :
        dist x 1 < δ := by
      simpa [Real.dist_eq, hx_abs] using hδ'_lt_δ
    have hbound :
        dist ((fun x : ℝ => (1 : ℝ) / x) x)
            ((fun x : ℝ => (1 : ℝ) / x) 1) < ε :=
      hδ hdist_lt
    refine ⟨x, hx_mem, ?_⟩
    have hf1 :
        (fun x : ℝ => (1 : ℝ) / x) 1 = (1 : ℝ) := by simp
    simpa [Real.dist_eq, one_div, hf1] using hbound

/-- Example 3.3.6. On the closed, bounded interval `[0, 1]`, consider
`f : [0, 1] → ℝ` given by `f x = 1 / x` for `x > 0` and `f 0 = 0`. The function is not
continuous at `0`, and because the values blow up near `0`, it fails to attain a maximum
on `[0, 1]` despite the domain being compact. -/
noncomputable def example_3_3_6_function (x : ℝ) : ℝ := if x = 0 then 0 else (1 : ℝ) / x

lemma example_3_3_6_function_pos {x : ℝ} (hx : 0 < x) :
    example_3_3_6_function x = (1 : ℝ) / x := by
  classical
  have hx_ne : x ≠ 0 := ne_of_gt hx
  simp [example_3_3_6_function, hx_ne]

lemma example_3_3_6_not_cont :
    ¬ ContinuousAt example_3_3_6_function 0 := by
  classical
  intro hcont
  have h :=
      (Metric.continuousAt_iff).1 hcont (1 : ℝ) (by norm_num : (0 : ℝ) < 1)
  rcases h with ⟨δ, hδ_pos, hδ⟩
  set δ' := min (δ / 2) ((1 : ℝ) / 2)
  have hδ'_pos : 0 < δ' := by
    have hhalf_pos : 0 < (1 : ℝ) / 2 := by norm_num
    have hδ_half_pos : 0 < δ / 2 := half_pos hδ_pos
    exact lt_min_iff.2 ⟨hδ_half_pos, hhalf_pos⟩
  have hδ'_le_halfδ : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'_lt_δ : δ' < δ :=
    lt_of_le_of_lt hδ'_le_halfδ (half_lt_self hδ_pos)
  have hδ'_le_half : δ' ≤ (1 : ℝ) / 2 := min_le_right _ _
  set x := δ'
  have hx_pos : 0 < x := hδ'_pos
  have hx_lt_one :
      x < 1 := lt_of_le_of_lt hδ'_le_half (by norm_num : (1 : ℝ) / 2 < 1)
  have hx_lt_δ : x < δ := by
    simpa [x] using hδ'_lt_δ
  have hx_dist_lt :
      dist x 0 < δ := by
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    simpa [Real.dist_eq, abs_of_nonneg hx_nonneg] using hx_lt_δ
  have hbound :=
      hδ hx_dist_lt
  have hf0 : example_3_3_6_function 0 = 0 := by
    simp [example_3_3_6_function]
  have hx_eval :
      example_3_3_6_function x = (1 : ℝ) / x :=
    example_3_3_6_function_pos hx_pos
  have hx_inv_pos : 0 < (1 : ℝ) / x := by
    simpa [one_div] using inv_pos.mpr hx_pos
  have hx_inv_gt_one :
      1 < (1 : ℝ) / x := by
    have := one_div_lt_one_div_of_lt hx_pos hx_lt_one
    simpa [one_div] using this
  have hx_dist_eq :
      dist (example_3_3_6_function x) (example_3_3_6_function 0) =
        (1 : ℝ) / x := by
    have hx_abs :
        |example_3_3_6_function x - example_3_3_6_function 0| =
          (1 : ℝ) / x := by
      simpa [hx_eval, hf0] using abs_of_pos hx_inv_pos
    simp [Real.dist_eq, hx_abs]
  have hx_contr :
      dist (example_3_3_6_function x) (example_3_3_6_function 0) < 1 :=
    hbound
  have hx_gt :
      1 < dist (example_3_3_6_function x) (example_3_3_6_function 0) := by
    simpa [hx_dist_eq] using hx_inv_gt_one
  exact (lt_irrefl _ (lt_of_lt_of_le hx_gt hx_contr.le))

lemma example_3_3_6_no_max_point :
    ∀ {d : ℝ}, d ∈ Set.Icc (0 : ℝ) 1 →
      ∃ x ∈ Set.Icc (0 : ℝ) 1,
        example_3_3_6_function d < example_3_3_6_function x := by
  classical
  intro d hd
  by_cases hzero : d = 0
  · refine ⟨(2 : ℝ)⁻¹, ?_, ?_⟩
    · exact ⟨by norm_num, by norm_num⟩
    · have hf_d : example_3_3_6_function d = 0 := by
        simp [example_3_3_6_function, hzero]
      have hx_pos : 0 < (2 : ℝ)⁻¹ := by norm_num
      have hf_half :
          example_3_3_6_function (2 : ℝ)⁻¹ = 2 := by
        simpa using
          example_3_3_6_function_pos (x := (2 : ℝ)⁻¹) hx_pos
      have hrewrite :
          example_3_3_6_function d < example_3_3_6_function (2 : ℝ)⁻¹ ↔
            (0 : ℝ) < 2 := by
        simp [hf_d, hf_half]
      exact hrewrite.mpr (by norm_num)
  · have hzero' : 0 ≠ d := by simpa [eq_comm] using hzero
    have hd_pos : 0 < d := lt_of_le_of_ne hd.1 hzero'
    let x := d / 2
    have hx_nonneg : 0 ≤ x := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      simpa [x] using div_nonneg hd.1 this
    have hx_le_half : x ≤ (1 : ℝ) / 2 := by
      have hx :=
          mul_le_mul_of_nonneg_right hd.2 (by norm_num : 0 ≤ (1 : ℝ) / 2)
      have hx' : d / 2 ≤ (1 : ℝ) / 2 := by
        simpa [div_eq_mul_inv] using hx
      simpa [x] using hx'
    have hx_le_one : x ≤ 1 := by
      have hhalf_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num
      exact hx_le_half.trans hhalf_le_one
    have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_nonneg, hx_le_one⟩
    have hx_pos : 0 < x := by
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      simpa [x] using div_pos hd_pos htwo_pos
    have hf_d :
        example_3_3_6_function d = (1 : ℝ) / d :=
      example_3_3_6_function_pos hd_pos
    have hf_x :
        example_3_3_6_function x = (1 : ℝ) / x :=
      example_3_3_6_function_pos hx_pos
    have hx_lt_d : x < d := by
      simpa [x] using half_lt_self hd_pos
    have hlt : example_3_3_6_function d <
        example_3_3_6_function x := by
      have h := one_div_lt_one_div_of_lt hx_pos hx_lt_d
      simpa [hf_d, hf_x, x, one_div] using h
    exact ⟨x, hx_mem, hlt⟩

lemma example_3_3_6_unbounded :
    ∀ M : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, M ≤ example_3_3_6_function x := by
  classical
  intro M
  obtain ⟨_, _, _, hbound, _, _⟩ := example_3_3_5
  obtain ⟨x, hx_mem, hMx⟩ := hbound M
  have hx_pos : 0 < x := hx_mem.1
  refine ⟨x, ?_, ?_⟩
  · exact ⟨le_of_lt hx_mem.1, le_of_lt hx_mem.2⟩
  · simpa [example_3_3_6_function_pos hx_pos] using hMx

lemma example_3_3_6 :
    (¬ ContinuousAt example_3_3_6_function 0) ∧
      (¬ ∃ d ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        example_3_3_6_function x ≤ example_3_3_6_function d) ∧
      (∀ M : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, M ≤ example_3_3_6_function x) := by
  refine ⟨example_3_3_6_not_cont, ?_, example_3_3_6_unbounded⟩
  intro hmax
  rcases hmax with ⟨d, hd, hle⟩
  obtain ⟨x, hx_mem, hlt⟩ := example_3_3_6_no_max_point hd
  exact (not_le_of_gt hlt) (hle x hx_mem)

/-- Lemma 3.3.7 (Bolzano's intermediate value theorem). For a continuous function
`f : [a, b] → ℝ` with `f a < 0` and `0 < f b`, there exists a point `c` strictly between
`a` and `b` such that `f c = 0`. -/
lemma lemma_3_3_7 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hsubset :=
    intermediate_value_Icc (α := ℝ) (δ := ℝ) (f := f) hab.le hf
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  rcases hsubset hzero_mem with ⟨c, hc_mem, hfc⟩
  have hca : c ≠ a := by
    intro hca
    have : f a = 0 := by simpa [hca] using hfc
    exact (ne_of_lt ha) this
  have hcb : c ≠ b := by
    intro hcb
    have : f b = 0 := by simpa [hcb] using hfc
    exact (ne_of_gt hb) this
  have hltac : a < c := lt_of_le_of_ne hc_mem.1 (by simpa [eq_comm] using hca)
  have hltcb : c < b := lt_of_le_of_ne hc_mem.2 hcb
  exact ⟨c, ⟨hltac, hltcb⟩, hfc⟩

/-- Theorem 3.3.8 (Bolzano's intermediate value theorem). Let `f : [a, b] → ℝ` be
continuous. If a real number `y` satisfies `f a < y < f b` or `f a > y > f b`, then there is
some `c` strictly between `a` and `b` such that `f c = y`. -/
theorem theorem_3_3_8 {a b y : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hy : (f a < y ∧ y < f b) ∨ (f a > y ∧ y > f b)) :
    ∃ c ∈ Set.Ioo a b, f c = y := by
  classical
  have hconst : ContinuousOn (fun _ : ℝ => y) (Set.Icc a b) := continuousOn_const
  refine hy.elim ?_ ?_
  · intro hy'
    let g := fun x : ℝ => f x - y
    have hg_cont : ContinuousOn g (Set.Icc a b) := hf.sub hconst
    have hga : g a < 0 := by
      have hyfa : f a < y := hy'.1
      simpa [g] using sub_lt_zero.mpr hyfa
    have hgb : 0 < g b := by
      have hyfb : y < f b := hy'.2
      simpa [g] using sub_pos.mpr hyfb
    obtain ⟨c, hc, hgc⟩ := lemma_3_3_7 hab hg_cont hga hgb
    refine ⟨c, hc, ?_⟩
    have hgc0 : f c - y = 0 := by simpa [g] using hgc
    exact sub_eq_zero.mp hgc0
  · intro hy'
    let g := fun x : ℝ => y - f x
    have hg_cont : ContinuousOn g (Set.Icc a b) := hconst.sub hf
    have hga : g a < 0 := by
      have hyfa : y < f a := hy'.1
      simpa [g] using sub_lt_zero.mpr hyfa
    have hgb : 0 < g b := by
      have hyfb : f b < y := hy'.2
      simpa [g] using sub_pos.mpr hyfb
    obtain ⟨c, hc, hgc⟩ := lemma_3_3_7 hab hg_cont hga hgb
    refine ⟨c, hc, ?_⟩
    have hgc0 : y - f c = 0 := by simpa [g] using hgc
    have hfc : y = f c := sub_eq_zero.mp hgc0
    simpa [eq_comm] using hfc

/-- Example 3.3.9 (Bisection method). For `f x = x ^ 3 - 2 x ^ 2 + x - 1`, we have
`f 1 = -1` and `f 2 = 1`, so by the intermediate value theorem there is a root
`c ∈ (1, 2)`. Evaluating at midpoints shows sign changes on nested intervals:
`f (3/2) < 0`, `f (7/4) < 0`, and `0 < f (15/8)`, so the root lies in
`(7/4, 15/8)`, numerically near `1.7549`. -/
lemma example_3_3_9 :
    (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) 1 = -1 ∧
      (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) 2 = 1 ∧
      (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) ((3 : ℝ) / 2) < 0 ∧
      (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) ((7 : ℝ) / 4) < 0 ∧
      0 < (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) ((15 : ℝ) / 8) ∧
      ContinuousOn (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) (Set.Icc (1 : ℝ) 2) ∧
      ∃ c ∈ Set.Ioo (1 : ℝ) 2, (fun x : ℝ => x ^ 3 - 2 * x ^ 2 + x - 1) c = 0 := by
  classical
  let f : ℝ → ℝ := fun x => x ^ 3 - 2 * x ^ 2 + x - 1
  have hf1 : f 1 = -1 := by norm_num [f]
  have hf2 : f 2 = 1 := by norm_num [f]
  have hf_three_half_val : f ((3 : ℝ) / 2) = (-5 : ℝ) / 8 := by norm_num [f]
  have hf_three_half : f ((3 : ℝ) / 2) < 0 := by
    have : (-5 : ℝ) / 8 < 0 := by norm_num
    simpa [hf_three_half_val] using this
  have hf_seven_fourths_val : f ((7 : ℝ) / 4) = (-1 : ℝ) / 64 := by norm_num [f]
  have hf_seven_fourths : f ((7 : ℝ) / 4) < 0 := by
    have : (-1 : ℝ) / 64 < 0 := by norm_num
    simpa [hf_seven_fourths_val] using this
  have hf_fifteen_eighths_val : f ((15 : ℝ) / 8) = (223 : ℝ) / 512 := by norm_num [f]
  have hf_fifteen_eighths : 0 < f ((15 : ℝ) / 8) := by
    have : 0 < (223 : ℝ) / 512 := by norm_num
    simp [hf_fifteen_eighths_val]
  have hcont_fun : Continuous fun x : ℝ => f x := by
    have h₁ : Continuous fun x : ℝ => x ^ 3 := by simpa using (continuous_id.pow 3)
    have h₂ : Continuous fun x : ℝ => x ^ 2 := by simpa using (continuous_id.pow 2)
    have hterm : Continuous fun x : ℝ => 2 * x ^ 2 := continuous_const.mul h₂
    have hsub : Continuous fun x : ℝ => x ^ 3 - 2 * x ^ 2 := h₁.sub hterm
    have hadd : Continuous fun x : ℝ => (x ^ 3 - 2 * x ^ 2) + x := hsub.add continuous_id
    have hfinal : Continuous fun x : ℝ => (x ^ 3 - 2 * x ^ 2 + x) - 1 :=
      hadd.sub continuous_const
    simpa [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal
  have hcont : ContinuousOn f (Set.Icc (1 : ℝ) 2) := hcont_fun.continuousOn
  have hroot : ∃ c ∈ Set.Ioo (1 : ℝ) 2, f c = 0 := by
    have hlt : f 1 < (0 : ℝ) := by
      have : (-1 : ℝ) < 0 := by norm_num
      simp [hf1]
    have hgt : (0 : ℝ) < f 2 := by
      have : (0 : ℝ) < 1 := by norm_num
      simp [hf2]
    have hy :
        (f 1 < (0 : ℝ) ∧ (0 : ℝ) < f 2) ∨ (f 1 > (0 : ℝ) ∧ (0 : ℝ) > f 2) :=
      Or.inl ⟨hlt, hgt⟩
    have hab : (1 : ℝ) < 2 := by norm_num
    simpa [f] using
      theorem_3_3_8 (a := (1 : ℝ)) (b := 2) (y := 0) (f := f) hab hcont hy
  refine ⟨by simpa [f] using hf1, ?_⟩
  refine ⟨by simpa [f] using hf2, ?_⟩
  refine ⟨by simpa [f] using hf_three_half, ?_⟩
  refine ⟨by simpa [f] using hf_seven_fourths, ?_⟩
  refine ⟨by simpa [f] using hf_fifteen_eighths, ?_⟩
  refine ⟨by simpa [f] using hcont, ?_⟩
  simpa [f] using hroot

/-- Proposition 3.3.10. A real polynomial of odd degree has a real root. -/
theorem proposition_3_3_10 {p : Polynomial ℝ} (hodd : Odd p.natDegree)
    (h₀ : p.leadingCoeff ≠ 0) : ∃ x : ℝ, p.eval x = 0 := by
  classical
  have hdeg_nat : 0 < p.natDegree := hodd.pos
  have hdeg : 0 < p.degree := (Polynomial.natDegree_pos_iff_degree_pos).1 hdeg_nat
  set q : Polynomial ℝ := p.comp (-Polynomial.X)
  have hq_eval : ∀ x : ℝ, q.eval x = p.eval (-x) := by
    intro x
    simp [q, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  have hq_nat : q.natDegree = p.natDegree := by
    simp [q, Polynomial.natDegree_comp]
  have hq_deg : 0 < q.degree := by
    have : 0 < q.natDegree := by simpa [hq_nat] using hdeg_nat
    exact (Polynomial.natDegree_pos_iff_degree_pos).1 this
  have hq_leadingCoeff : q.leadingCoeff = -p.leadingCoeff := by
    have hpow : (-1 : ℝ) ^ p.natDegree = -1 := by simpa using hodd.neg_one_pow (α := ℝ)
    simp [q, hpow]
  have hcont : Continuous fun x : ℝ => p.eval x := p.continuous
  have hsign := lt_or_gt_of_ne (a := p.leadingCoeff) (b := 0) h₀
  cases hsign with
  | inl hneg =>
      have hto_neg := p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le
      have hq_nonneg : 0 ≤ q.leadingCoeff := by
        have hpos : 0 < q.leadingCoeff := by
          simpa [hq_leadingCoeff] using neg_pos_of_neg hneg
        exact hpos.le
      have hto_pos := q.tendsto_atTop_of_leadingCoeff_nonneg hq_deg hq_nonneg
      obtain ⟨R₁, hR₁⟩ :=
        Filter.eventually_atTop.1 (Filter.tendsto_atBot.1 hto_neg (-1))
      obtain ⟨R₂, hR₂⟩ :=
        Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hto_pos 1)
      set R : ℝ := max (max R₁ R₂) 1
      have hmax_le : max R₁ R₂ ≤ R := le_max_left _ _
      have hR₁_le : R₁ ≤ R := le_trans (le_max_left _ _) hmax_le
      have hR₂_le : R₂ ≤ R := le_trans (le_max_right _ _) hmax_le
      have hR_pos : 0 < R :=
        lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (le_max_right _ _)
      have hneg_eval : p.eval R < 0 := by
        have hle : p.eval R ≤ -1 := hR₁ _ hR₁_le
        exact lt_of_le_of_lt hle (by norm_num)
      have hpos_eval : 0 < p.eval (-R) := by
        have hge : 1 ≤ q.eval R := hR₂ _ hR₂_le
        have hge' : 1 ≤ p.eval (-R) := by simpa [hq_eval] using hge
        exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hge'
      have hy :
          (p.eval (-R) < 0 ∧ 0 < p.eval R) ∨ (p.eval (-R) > 0 ∧ 0 > p.eval R) :=
        Or.inr ⟨hpos_eval, by simpa [gt_iff_lt] using hneg_eval⟩
      have hab : -R < R := neg_lt_self hR_pos
      have hcont_on :
          ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc (-R) R) := hcont.continuousOn
      obtain ⟨c, _, hc⟩ :=
        theorem_3_3_8 (a := -R) (b := R) (y := 0) (f := fun x => p.eval x) hab hcont_on hy
      exact ⟨c, hc⟩
  | inr hpos =>
      have hto_pos := p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hpos.le
      have hq_nonpos : q.leadingCoeff ≤ 0 := by
        have hneg' : q.leadingCoeff < 0 := by
          simpa [hq_leadingCoeff] using neg_neg_of_pos hpos
        exact hneg'.le
      have hto_neg := q.tendsto_atBot_of_leadingCoeff_nonpos hq_deg hq_nonpos
      obtain ⟨R₁, hR₁⟩ :=
        Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hto_pos 1)
      obtain ⟨R₂, hR₂⟩ :=
        Filter.eventually_atTop.1 (Filter.tendsto_atBot.1 hto_neg (-1))
      set R : ℝ := max (max R₁ R₂) 1
      have hmax_le : max R₁ R₂ ≤ R := le_max_left _ _
      have hR₁_le : R₁ ≤ R := le_trans (le_max_left _ _) hmax_le
      have hR₂_le : R₂ ≤ R := le_trans (le_max_right _ _) hmax_le
      have hR_pos : 0 < R :=
        lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (le_max_right _ _)
      have hpos_eval : 0 < p.eval R := by
        have hge : 1 ≤ p.eval R := hR₁ _ hR₁_le
        exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hge
      have hneg_eval : p.eval (-R) < 0 := by
        have hle : p.eval (-R) ≤ -1 := by
          have : q.eval R ≤ -1 := hR₂ _ hR₂_le
          simpa [hq_eval] using this
        exact lt_of_le_of_lt hle (by norm_num)
      have hy :
          (p.eval (-R) < 0 ∧ 0 < p.eval R) ∨ (p.eval (-R) > 0 ∧ 0 > p.eval R) :=
        Or.inl ⟨hneg_eval, hpos_eval⟩
      have hab : -R < R := neg_lt_self hR_pos
      have hcont_on :
          ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc (-R) R) := hcont.continuousOn
      obtain ⟨c, _, hc⟩ :=
        theorem_3_3_8 (a := -R) (b := R) (y := 0) (f := fun x => p.eval x) hab hcont_on hy
      exact ⟨c, hc⟩

lemma example_3_3_11_pow_pos {k : ℕ} (hk : 1 < k) {y : ℝ} (hy : 1 < y) :
    0 < y ^ k - y := by
  have hy_pos : 0 < y := lt_trans zero_lt_one hy
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hy_ge_one : 1 ≤ y := le_of_lt hy
  have hk_le : 1 ≤ k := le_of_lt hk
  have hy_pow_ge_one :
      ∀ n : ℕ, 1 ≤ y ^ n := by
    intro n
    induction' n with n ih
    · simp
    · have hy_pow_nonneg : 0 ≤ y ^ n := pow_nonneg hy_nonneg n
      have hmul : (1 : ℝ) * 1 ≤ y ^ n * y :=
        mul_le_mul ih hy_ge_one (by norm_num) hy_pow_nonneg
      simpa [pow_succ] using hmul
  have hk_sub_pos : 0 < k - 1 := Nat.sub_pos_of_lt hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk_sub_pos.ne'
  have hy_mul_le : y ≤ y ^ m * y := by
    have := mul_le_mul_of_nonneg_right (hy_pow_ge_one m) hy_nonneg
    simpa [one_mul] using this
  have hpow_gt : 1 < y ^ (k - 1) := by
    have : 1 < y ^ m * y := lt_of_lt_of_le hy hy_mul_le
    have hsucc : y ^ (m + 1) = y ^ m * y := by simp [pow_succ]
    simpa [hm, hsucc] using this
  have hsub_pos : 0 < y ^ (k - 1) - 1 := sub_pos.mpr hpow_gt
  have hfactor : y ^ k - y = y * (y ^ (k - 1) - 1) := by
    have hpow_succ : y ^ k = y ^ (k - 1) * y := by
      have hk_sub : (k - 1) + 1 = k := Nat.sub_add_cancel hk_le
      simpa [hk_sub] using (pow_succ y (k - 1))
    calc
      y ^ k - y = y ^ (k - 1) * y - y := by simp [hpow_succ]
      _ = y * (y ^ (k - 1) - 1) := by ring
  have hmul_pos : 0 < y * (y ^ (k - 1) - 1) := mul_pos hy_pos hsub_pos
  simpa [hfactor] using hmul_pos

/-- Example 3.3.11. For any natural number `k > 0` and any `y > 0`, there exists `x > 0`
such that `x ^ k = y`, which follows from Bolzano's intermediate value theorem applied to
`x ↦ x ^ k - y`. -/
lemma example_3_3_11 {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    ∃ x : ℝ, 0 < x ∧ x ^ k = y := by
  classical
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hf_cont : Continuous fun x : ℝ => x ^ k - y :=
    (continuous_pow k).sub continuous_const
  let f : ℝ → ℝ := fun x => x ^ k - y
  have hf_zero_neg : f 0 < 0 := by
    have hneg : -y < 0 := by linarith
    simpa [f, zero_pow hk0] using hneg
  by_cases hk1 : k = 1
  · refine ⟨y, hy, ?_⟩
    simp [hk1]
  have hk_le : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk_gt_one : 1 < k := lt_of_le_of_ne hk_le (by simpa [eq_comm] using hk1)
  by_cases hy1 : y = 1
  · subst hy1
    refine ⟨1, by norm_num, ?_⟩
    simp
  have hy_ne_one : y ≠ 1 := hy1
  cases lt_or_gt_of_ne hy_ne_one with
  | inl hy_lt_one =>
      have hf_small :
          ContinuousOn f (Set.Icc (0 : ℝ) 1) := hf_cont.continuousOn
      have hpos : 0 < f 1 := by
        have hpos' : 0 < 1 - y := by linarith
        simpa [f, one_pow] using hpos'
      obtain ⟨c, hc, hfc⟩ :=
        lemma_3_3_7 (a := 0) (b := 1) (f := f) (hab := by norm_num)
          hf_small hf_zero_neg hpos
      refine ⟨c, hc.1, ?_⟩
      have hpow := hfc
      simp [f] at hpow
      exact sub_eq_zero.mp hpow
  | inr hy_gt_one =>
      have hf_large :
          ContinuousOn f (Set.Icc (0 : ℝ) y) := hf_cont.continuousOn
      have hpos : 0 < f y := by
        have hpow_pos : 0 < y ^ k - y := example_3_3_11_pow_pos hk_gt_one hy_gt_one
        simpa [f] using hpow_pos
      obtain ⟨c, hc, hfc⟩ :=
        lemma_3_3_7 (a := 0) (b := y) (f := f) hy hf_large hf_zero_neg hpos
      refine ⟨c, hc.1, ?_⟩
      have hpow := hfc
      simp [f] at hpow
      exact sub_eq_zero.mp hpow

/-- Example 3.3.12. The function
`f x = sin (1 / x)` for `x ≠ 0` and `f 0 = 0` is discontinuous at `0`, yet it still
has the intermediate value property: whenever `a < b` and `y` lies strictly between
`f a` and `f b` (in either order), there exists some `c ∈ (a, b)` with `f c = y`. -/
noncomputable def example_3_3_12_function (x : ℝ) : ℝ := if x = 0 then 0 else Real.sin (1 / x)

lemma example_3_3_12_function_of_ne {x : ℝ} (hx : x ≠ 0) :
    example_3_3_12_function x = Real.sin (1 / x) := by
  simp [example_3_3_12_function, hx]

lemma example_3_3_12_function_neg (x : ℝ) :
    example_3_3_12_function (-x) = -example_3_3_12_function x := by
  by_cases hx : x = 0
  · simp [example_3_3_12_function, hx]
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    simp [example_3_3_12_function, hx, hneg]

lemma example_3_3_12_abs_le_one (x : ℝ) :
    |example_3_3_12_function x| ≤ 1 := by
  classical
  by_cases hx : x = 0
  · simp [example_3_3_12_function, hx]
  · simpa [example_3_3_12_function_of_ne hx] using Real.abs_sin_le_one (1 / x)

lemma example_3_3_12_continuous_on_nonzero {a b : ℝ}
    (hzero : 0 ∉ Set.Icc a b) :
    ContinuousOn example_3_3_12_function (Set.Icc a b) := by
  classical
  have hx_ne : ∀ x ∈ Set.Icc a b, x ≠ 0 := by
    intro x hx hx0
    exact hzero (by simpa [Set.mem_Icc, hx0] using hx)
  have hsin : ContinuousOn (fun x : ℝ => Real.sin (1 / x)) (Set.Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := hx_ne x hx
    have hcont :=
        (Real.continuous_sin.continuousAt).comp (continuousAt_inv₀ hx0)
    simpa [example_3_3_12_function_of_ne hx0] using hcont.continuousWithinAt
  have hEq :
      Set.EqOn (fun x : ℝ => Real.sin (1 / x)) example_3_3_12_function
        (Set.Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := hx_ne x hx
    simp [example_3_3_12_function_of_ne hx0]
  simpa using hsin.congr hEq.symm

lemma example_3_3_12_hits_pm_one :
    ∀ ε > 0, ∃ t₁ t₂,
        0 < t₁ ∧ t₁ < t₂ ∧ t₂ < ε ∧
          example_3_3_12_function t₁ = -1 ∧
            example_3_3_12_function t₂ = 1 := by
  classical
  intro ε hε
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have htwopi_pos : 0 < 2 * Real.pi := by
    have : 0 < (2 : ℝ) := by norm_num
    exact mul_pos this hpi_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
  have hn_pos : 0 < (n : ℝ) := by
    have : 0 < 1 / (2 * Real.pi * ε) := by
      have : 0 < 2 * Real.pi * ε := mul_pos htwopi_pos hε
      simpa [one_div] using inv_pos.mpr this
    exact lt_trans this hn
  set d₂ := Real.pi / 2 + 2 * Real.pi * (n : ℝ)
  set d₁ := 3 * Real.pi / 2 + 2 * Real.pi * (n : ℝ)
  have hd₁_eq : d₁ = d₂ + Real.pi := by
    have : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    simp [d₁, d₂, this, add_comm, add_assoc]
  have htwo_pi_n_nonneg :
      0 ≤ 2 * Real.pi * (n : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hpi_pos))
      (by exact_mod_cast (Nat.zero_le n))
  have hd₂_pos : 0 < d₂ :=
    add_pos_of_pos_of_nonneg (half_pos hpi_pos) htwo_pi_n_nonneg
  have hthree_pi_pos : 0 < 3 * Real.pi / 2 := by
    have hnum : 0 < (3 : ℝ) * Real.pi := mul_pos (by norm_num : 0 < (3 : ℝ)) hpi_pos
    have hden : 0 < (2 : ℝ) := by norm_num
    simpa using div_pos hnum hden
  have hd₁_pos : 0 < d₁ :=
    add_pos_of_pos_of_nonneg hthree_pi_pos htwo_pi_n_nonneg
  set t₁ := 1 / d₁
  set t₂ := 1 / d₂
  have ht₁_pos : 0 < t₁ := by simpa [t₁] using inv_pos.mpr hd₁_pos
  have ht₂_pos : 0 < t₂ := by simpa [t₂] using inv_pos.mpr hd₂_pos
  have hd₂_lt_hd₁ : d₂ < d₁ := by
    have := add_lt_add_left hpi_pos d₂
    simpa [hd₁_eq] using this
  have ht₁_lt_ht₂ : t₁ < t₂ := by
    have := one_div_lt_one_div_of_lt hd₂_pos hd₂_lt_hd₁
    simpa [t₁, t₂] using this
  have htwopi_lt_d₂ : 2 * Real.pi * (n : ℝ) < d₂ := by
    have := add_lt_add_left (half_pos hpi_pos) (2 * Real.pi * (n : ℝ))
    simpa [d₂, add_comm, add_left_comm, add_assoc, two_mul] using this
  have ht₂_lt_inv :
      t₂ < 1 / (2 * Real.pi * (n : ℝ)) := by
    have := one_div_lt_one_div_of_lt (mul_pos htwopi_pos hn_pos) htwopi_lt_d₂
    simpa [t₂] using this
  have h_inv_lt :
      ε⁻¹ < 2 * Real.pi * (n : ℝ) := by
    have := mul_lt_mul_of_pos_left hn htwopi_pos
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have ht_inv_lt_eps :
      1 / (2 * Real.pi * (n : ℝ)) < ε := by
    have := one_div_lt_one_div_of_lt (inv_pos.mpr hε) h_inv_lt
    simpa [one_div] using this
  have ht₂_lt_eps : t₂ < ε := lt_trans ht₂_lt_inv ht_inv_lt_eps
  have htwo_pi_nat :
      2 * Real.pi * (n : ℝ) = ((2 * n : ℕ) : ℝ) * Real.pi := by
    simp [mul_comm, mul_left_comm, Nat.cast_mul]
  have hsin_two_pi :
      Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
    simpa [htwo_pi_nat] using Real.sin_nat_mul_pi (2 * n)
  have hcos_two_pi :
      Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
    simpa [htwo_pi_nat] using Real.cos_nat_mul_pi (2 * n)
  have hsin_d₂ :
      Real.sin d₂ = 1 := by
    have hcos :
        Real.sin d₂ = Real.cos (2 * Real.pi * (n : ℝ)) := by
      have := Real.sin_add (Real.pi / 2) (2 * Real.pi * (n : ℝ))
      have hsum :
          Real.pi / 2 + 2 * Real.pi * (n : ℝ) = d₂ := by
        simp [d₂]
      simpa [hsum, Real.sin_pi_div_two, Real.cos_pi_div_two, hsin_two_pi] using this
    simpa [hcos_two_pi] using hcos
  have hsin_d₁ :
      Real.sin d₁ = -1 := by
    have := Real.sin_add d₂ Real.pi
    simpa [hd₁_eq, Real.sin_pi, Real.cos_pi, hsin_d₂, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using this
  have ht₁_ne : t₁ ≠ 0 := ne_of_gt ht₁_pos
  have ht₂_ne : t₂ ≠ 0 := ne_of_gt ht₂_pos
  refine ⟨t₁, t₂, ht₁_pos, ht₁_lt_ht₂, ht₂_lt_eps, ?_, ?_⟩
  · have : Real.sin (1 / t₁) = -1 := by simpa [t₁, d₁] using hsin_d₁
    simpa [example_3_3_12_function, ht₁_ne] using this
  · have : Real.sin (1 / t₂) = 1 := by simpa [t₂, d₂] using hsin_d₂
    simpa [example_3_3_12_function, ht₂_ne] using this

lemma example_3_3_12_between_bounds {a b y : ℝ}
    (hy :
      (example_3_3_12_function a < y ∧ y < example_3_3_12_function b) ∨
        (example_3_3_12_function a > y ∧ y > example_3_3_12_function b)) :
    -1 < y ∧ y < 1 := by
  rcases hy with hy | hy
  · have hfa := abs_le.mp (example_3_3_12_abs_le_one a)
    have hfb := abs_le.mp (example_3_3_12_abs_le_one b)
    refine ⟨lt_of_le_of_lt hfa.1 hy.1, lt_of_lt_of_le hy.2 hfb.2⟩
  · have hfa := abs_le.mp (example_3_3_12_abs_le_one a)
    have hfb := abs_le.mp (example_3_3_12_abs_le_one b)
    refine ⟨lt_of_le_of_lt hfb.1 hy.2, lt_of_lt_of_le hy.1 hfa.2⟩

lemma example_3_3_12_not_cont :
    ¬ ContinuousAt example_3_3_12_function 0 := by
  classical
  intro hcont
  rcases (Metric.continuousAt_iff.mp hcont) (1 / 2) (by norm_num) with ⟨δ, hδ_pos, hδ⟩
  obtain ⟨t₁, t₂, ht₁_pos, ht₁_lt, ht₂_lt, _, hft₂⟩ :=
    example_3_3_12_hits_pm_one δ hδ_pos
  have hf0 : example_3_3_12_function 0 = 0 := by simp [example_3_3_12_function]
  have ht₂_pos : 0 < t₂ := lt_trans ht₁_pos ht₁_lt
  have hdist : dist t₂ 0 < δ := by
    have : |t₂| = t₂ := abs_of_pos ht₂_pos
    simpa [Real.dist_eq, this, sub_eq_add_neg] using ht₂_lt
  have hlt := hδ hdist
  have : dist (example_3_3_12_function t₂) (example_3_3_12_function 0) =
      (1 : ℝ) := by
    simp [hft₂, hf0]
  have : (1 : ℝ) < 1 / 2 := by simpa [this] using hlt
  norm_num at this

lemma example_3_3_12_IVT_cross_zero {a b y : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hy :
      (example_3_3_12_function a < y ∧ y < example_3_3_12_function b) ∨
        (example_3_3_12_function a > y ∧ y > example_3_3_12_function b)) :
    ∃ c ∈ Set.Ioo a b, example_3_3_12_function c = y := by
  classical
  have hεpos :
      0 < min (-a) b := lt_min (neg_pos.mpr ha) hb
  obtain ⟨t₁, t₂, ht₁_pos, ht₁_lt, ht₂_lt, hft₁, hft₂⟩ :=
    example_3_3_12_hits_pm_one (min (-a) b) hεpos
  have ht₂_lt_b : t₂ < b := lt_of_lt_of_le ht₂_lt (min_le_right (-a) b)
  have ha_lt_t₁ : a < t₁ := lt_trans ha ht₁_pos
  have hzero_not_mem : 0 ∉ Set.Icc t₁ t₂ := by
    intro h
    exact (not_lt_of_ge h.1) ht₁_pos
  have hcont :=
    example_3_3_12_continuous_on_nonzero (a := t₁) (b := t₂) hzero_not_mem
  have hy_bounds := example_3_3_12_between_bounds hy
  obtain ⟨c, hc, hfc⟩ :=
    theorem_3_3_8 ht₁_lt
      hcont
      (Or.inl
        ⟨by simpa [hft₁] using hy_bounds.1,
          by simpa [hft₂] using hy_bounds.2⟩)
  refine ⟨c, ?_, hfc⟩
  exact ⟨lt_trans ha_lt_t₁ hc.1, lt_trans hc.2 ht₂_lt_b⟩

lemma example_3_3_12 :
    (¬ ContinuousAt example_3_3_12_function 0) ∧
      (∀ {a b y : ℝ}, a < b →
        ((example_3_3_12_function a < y ∧ y < example_3_3_12_function b) ∨
          (example_3_3_12_function a > y ∧ y > example_3_3_12_function b)) →
          ∃ c ∈ Set.Ioo a b, example_3_3_12_function c = y) := by
  classical
  refine ⟨example_3_3_12_not_cont, ?_⟩
  intro a b y hab hy
  by_cases hzero : 0 ∈ Set.Icc a b
  · have ha_le : a ≤ 0 := hzero.1
    have hb_ge : 0 ≤ b := hzero.2
    by_cases ha_lt : a < 0
    · by_cases hb_gt : 0 < b
      · exact example_3_3_12_IVT_cross_zero ha_lt hb_gt hy
      · have hb0 : b = 0 := le_antisymm (le_of_not_gt hb_gt) hb_ge
        have hεpos : 0 < min (-a) (1 : ℝ) :=
          lt_min (neg_pos.mpr ha_lt) (by norm_num)
        obtain ⟨t₁, t₂, ht₁_pos, ht₁_lt, ht₂_lt, hft₁, hft₂⟩ :=
          example_3_3_12_hits_pm_one (min (-a) 1) hεpos
        set u := -t₂
        set v := -t₁
        have huv : u < v := by simpa [u, v] using neg_lt_neg ht₁_lt
        have hau : a < u := by
          have : t₂ < -a := lt_of_lt_of_le ht₂_lt (min_le_left (-a) (1 : ℝ))
          simpa [u] using neg_lt_neg this
        have hvb : v < b := by simpa [v, hb0] using neg_lt_zero.mpr ht₁_pos
        have hzero' : 0 ∉ Set.Icc u v := by
          intro h
          have hv_nonneg : 0 ≤ v := h.2
          have hv_neg : v < 0 := by simpa [v, hb0] using neg_lt_zero.mpr ht₁_pos
          exact (lt_irrefl _ (lt_of_le_of_lt hv_nonneg hv_neg))
        have hcont :=
          example_3_3_12_continuous_on_nonzero (a := u) (b := v) hzero'
        have hy_bounds := example_3_3_12_between_bounds hy
        obtain ⟨c, hc, hfc⟩ :=
          theorem_3_3_8 huv hcont
            (Or.inl
              ⟨by
                  simpa [example_3_3_12_function_neg, u, hft₂] using hy_bounds.1,
                by
                  simpa [example_3_3_12_function_neg, v, hft₁] using hy_bounds.2⟩)
        have hac : a < c := lt_trans hau hc.1
        have hcb : c < b := lt_trans hc.2 hvb
        exact ⟨c, ⟨hac, hcb⟩, hfc⟩
    · have ha0 : a = 0 := le_antisymm ha_le (le_of_not_gt ha_lt)
      have hb_gt : 0 < b := by simpa [ha0] using hab
      have hεpos : 0 < min b (1 : ℝ) := lt_min hb_gt (by norm_num)
      obtain ⟨t₁, t₂, ht₁_pos, ht₁_lt, ht₂_lt, hft₁, hft₂⟩ :=
        example_3_3_12_hits_pm_one (min b 1) hεpos
      have ht₂_lt_b : t₂ < b := lt_of_lt_of_le ht₂_lt (min_le_left b (1 : ℝ))
      have hzero' : 0 ∉ Set.Icc t₁ t₂ := by
        intro h
        exact (not_lt_of_ge h.1) ht₁_pos
      have hcont :=
        example_3_3_12_continuous_on_nonzero (a := t₁) (b := t₂) hzero'
      have hy_bounds := example_3_3_12_between_bounds hy
      obtain ⟨c, hc, hfc⟩ :=
        theorem_3_3_8 ht₁_lt hcont
          (Or.inl
            ⟨by simpa [hft₁] using hy_bounds.1,
              by simpa [hft₂] using hy_bounds.2⟩)
      have hac : a < c := by simpa [ha0] using lt_trans ht₁_pos hc.1
      have hcb : c < b := lt_trans hc.2 ht₂_lt_b
      exact ⟨c, ⟨hac, hcb⟩, hfc⟩
  · have hcont := example_3_3_12_continuous_on_nonzero (a := a) (b := b) hzero
    exact theorem_3_3_8 hab hcont hy

/-- If `f` has a minimum at `xmin` and a maximum at `xmax` on `[a, b]`, then the image lies
between the endpoint values. -/
lemma corollary_3_3_13_image_subset {a b : ℝ} {f : ℝ → ℝ} {xmin xmax : ℝ}
    (_hxmin : xmin ∈ Set.Icc a b) (_hxmax : xmax ∈ Set.Icc a b)
    (hmin : ∀ x ∈ Set.Icc a b, f xmin ≤ f x)
    (hmax : ∀ x ∈ Set.Icc a b, f x ≤ f xmax) :
    f '' Set.Icc a b ⊆ Set.Icc (f xmin) (f xmax) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨hmin x hx, hmax x hx⟩

/-- If the minimum and maximum values are distinct, then every value between them is
achieved on `[a, b]`. -/
lemma corollary_3_3_13_Icc_subset_image {a b : ℝ} {f : ℝ → ℝ} {xmin xmax : ℝ}
    (hxmin : xmin ∈ Set.Icc a b) (hxmax : xmax ∈ Set.Icc a b)
    (hf : ContinuousOn f (Set.Icc a b))
    (_hmin : ∀ x ∈ Set.Icc a b, f xmin ≤ f x)
    (_hmax : ∀ x ∈ Set.Icc a b, f x ≤ f xmax)
    (hcd : f xmin < f xmax) :
    Set.Icc (f xmin) (f xmax) ⊆ f '' Set.Icc a b := by
  classical
  intro y hy
  by_cases hyl : y = f xmin
  · exact ⟨xmin, hxmin, hyl.symm⟩
  by_cases hyr : y = f xmax
  · exact ⟨xmax, hxmax, hyr.symm⟩
  have hy_left : f xmin < y :=
    lt_of_le_of_ne hy.1 (by exact ne_comm.mp hyl)
  have hy_right : y < f xmax := lt_of_le_of_ne hy.2 hyr
  have hxne : xmin ≠ xmax := by
    intro h
    have : f xmin = f xmax := by simp [h]
    exact (ne_of_lt hcd) this
  cases lt_or_gt_of_ne hxne with
  | inl hlt =>
      have hsubset : Set.Icc xmin xmax ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨le_trans hxmin.1 hx.1, le_trans hx.2 hxmax.2⟩
      have hcont : ContinuousOn f (Set.Icc xmin xmax) := hf.mono hsubset
      obtain ⟨c, hc, hfc⟩ :=
        theorem_3_3_8 (a := xmin) (b := xmax) (y := y) hlt hcont
          (Or.inl ⟨hy_left, hy_right⟩)
      have hc' : c ∈ Set.Icc a b := by
        exact ⟨le_trans hxmin.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hxmax.2⟩
      exact ⟨c, hc', hfc⟩
  | inr hgt =>
      have hsubset : Set.Icc xmax xmin ⊆ Set.Icc a b := by
        intro x hx
        exact ⟨le_trans hxmax.1 hx.1, le_trans hx.2 hxmin.2⟩
      have hcont : ContinuousOn f (Set.Icc xmax xmin) := hf.mono hsubset
      obtain ⟨c, hc, hfc⟩ :=
        theorem_3_3_8 (a := xmax) (b := xmin) (y := y) hgt hcont
          (Or.inr ⟨by simpa using hy_right, by simpa using hy_left⟩)
      have hc' : c ∈ Set.Icc a b := by
        exact ⟨le_trans hxmax.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hxmin.2⟩
      exact ⟨c, hc', hfc⟩

/-- Corollary 3.3.13. If `f : [a, b] → ℝ` is continuous, then the image `f '' [a, b]` is
either a closed and bounded interval or a single point. -/
lemma corollary_3_3_13 {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ c d : ℝ, c ≤ d ∧ f '' Set.Icc a b = Set.Icc c d) ∨
      ∃ c : ℝ, f '' Set.Icc a b = {c} := by
  classical
  obtain ⟨⟨xmin, hxmin, hmin⟩, ⟨xmax, hxmax, hmax⟩⟩ := theorem_3_3_2 hle hf
  have hle_vals : f xmin ≤ f xmax := hmin xmax hxmax
  by_cases hcd : f xmin = f xmax
  · right
    refine ⟨f xmin, ?_⟩
    apply Set.ext
    intro y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      have h1 : f xmin ≤ f x := hmin x hx
      have h2 : f x ≤ f xmax := hmax x hx
      have h2' : f x ≤ f xmin := by simpa [hcd] using h2
      have hfx : f x = f xmin := le_antisymm h2' h1
      simp [hfx]
    · intro hy
      rcases (Set.mem_singleton_iff.mp hy) with rfl
      exact ⟨xmin, hxmin, rfl⟩
  · left
    have hlt : f xmin < f xmax := lt_of_le_of_ne hle_vals hcd
    refine ⟨f xmin, f xmax, le_of_lt hlt, ?_⟩
    have himage_subset :
        f '' Set.Icc a b ⊆ Set.Icc (f xmin) (f xmax) :=
      corollary_3_3_13_image_subset hxmin hxmax hmin hmax
    have hsubset_image :
        Set.Icc (f xmin) (f xmax) ⊆ f '' Set.Icc a b :=
      corollary_3_3_13_Icc_subset_image hxmin hxmax hf hmin hmax hlt
    exact subset_antisymm himage_subset hsubset_image

end Section03
end Chap03
