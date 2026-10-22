/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Filter Topology

section Chap03
section Section04

/-- Definition 3.4.1. A function `f : S → ℝ` is uniformly continuous if for every `ε > 0`
there exists `δ > 0` such that whenever `x, c ∈ S` with `|x - c| < δ`, then
`|f x - f c| < ε`. -/
def book_uniformContinuous (S : Set ℝ) (f : S → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x c : S, |(x : ℝ) - (c : ℝ)| < δ → |f x - f c| < ε

/-- The book definition of uniform continuity on a subset of `ℝ` is equivalent to the standard
`UniformContinuous` predicate for functions on the subtype. -/
lemma book_uniformContinuous_iff_uniformContinuous {S : Set ℝ} {f : S → ℝ} :
    book_uniformContinuous S f ↔ UniformContinuous f := by
  constructor
  · intro h
    refine (Metric.uniformContinuous_iff).2 ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := h ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro x c hdist
    have hxc : |(x : ℝ) - (c : ℝ)| < δ := by
      simpa [Real.dist_eq] using hdist
    have hres : |f x - f c| < ε := hδ x c hxc
    simpa [Real.dist_eq] using hres
  · intro h ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuous_iff).1 h ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro x c hxc
    have hdist : dist x c < δ := by
      simpa [Real.dist_eq] using hxc
    have hres : dist (f x) (f c) < ε := hδ hdist
    simpa [Real.dist_eq] using hres

/-- Helper lemma for Example 3.4.2: on `[0, 1]`, the square function has Lipschitz constant `2`. -/
lemma abs_sq_sub_sq_le_two_abs_sub
    {x y : {t // t ∈ Set.Icc (0 : ℝ) 1}} :
    |(x : ℝ) ^ 2 - (y : ℝ) ^ 2| ≤ 2 * |(x : ℝ) - (y : ℝ)| := by
  have hxn0 : 0 ≤ (x : ℝ) := (x.property.1)
  have hyn0 : 0 ≤ (y : ℝ) := (y.property.1)
  have hsum_nonneg : 0 ≤ (x : ℝ) + (y : ℝ) := add_nonneg hxn0 hyn0
  have hx_le : (x : ℝ) ≤ 1 := x.property.2
  have hy_le : (y : ℝ) ≤ 1 := y.property.2
  have hsum_le : (x : ℝ) + (y : ℝ) ≤ (2 : ℝ) := by
    have := add_le_add hx_le hy_le
    simpa [one_add_one_eq_two] using this
  have habs_add : |(x : ℝ) + (y : ℝ)| ≤ 2 := by
    have : |(x : ℝ) + (y : ℝ)| = (x : ℝ) + (y : ℝ) :=
      abs_of_nonneg hsum_nonneg
    simpa [this] using hsum_le
  have hnonneg : 0 ≤ |(x : ℝ) - (y : ℝ)| := abs_nonneg _
  calc
    |(x : ℝ) ^ 2 - (y : ℝ) ^ 2|
        = |(x : ℝ) - (y : ℝ)| * |(x : ℝ) + (y : ℝ)| := by
          simp [sq_sub_sq, abs_mul, mul_comm]
    _ ≤ |(x : ℝ) - (y : ℝ)| * 2 :=
      mul_le_mul_of_nonneg_left habs_add hnonneg
    _ = 2 * |(x : ℝ) - (y : ℝ)| := by simp [mul_comm]

/-- Example 3.4.2. The square function is uniformly continuous on the closed interval `[0, 1]`,
but it is not uniformly continuous on the whole real line. -/
lemma uniformContinuous_sq_on_Icc :
    UniformContinuous (fun x : {x // x ∈ Set.Icc (0 : ℝ) 1} => (x : ℝ) ^ 2) := by
  classical
  refine (Metric.uniformContinuous_iff).2 ?_
  intro ε hε
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro x y hxy
  have hxy' : |(x : ℝ) - (y : ℝ)| < ε / 2 := by
    have : dist (x : ℝ) (y : ℝ) < ε / 2 := by simpa using hxy
    simpa [Real.dist_eq] using this
  have hbound :=
    abs_sq_sub_sq_le_two_abs_sub (x := x) (y := y)
  have hlt : 2 * |(x : ℝ) - (y : ℝ)| < ε := by
    have htemp :
        2 * |(x : ℝ) - (y : ℝ)| < 2 * (ε / 2) :=
      mul_lt_mul_of_pos_left hxy' (by norm_num : (0 : ℝ) < 2)
    simpa [two_mul] using htemp
  have : |(x : ℝ) ^ 2 - (y : ℝ) ^ 2| < ε :=
    lt_of_le_of_lt hbound hlt
  have hdist :
      dist ((fun z : {x // x ∈ Set.Icc (0 : ℝ) 1} => (z : ℝ) ^ 2) x)
        ((fun z : {x // x ∈ Set.Icc (0 : ℝ) 1} => (z : ℝ) ^ 2) y)
        = |(x : ℝ) ^ 2 - (y : ℝ) ^ 2| := by
    simp [Real.dist_eq]
  simpa [hdist] using this

/-- Example 3.4.2. The square function `ℝ → ℝ` is not uniformly continuous on the entire real
line. -/
lemma not_uniformContinuous_sq : ¬ UniformContinuous (fun x : ℝ => x ^ 2) := by
  classical
  intro h
  obtain ⟨δ, δpos, hδ⟩ :=
    (Metric.uniformContinuous_iff).1 h 1 (by norm_num : (0 : ℝ) < 1)
  set x : ℝ := 2 / δ
  set y : ℝ := x + δ / 2
  have hxpos : 0 < x := by
    simpa [x] using div_pos (show (0 : ℝ) < 2 by norm_num) δpos
  have hypos : 0 < y := add_pos hxpos (half_pos δpos)
  have hyx : y - x = δ / 2 := by
    simp [y, sub_eq_add_neg]
  have hyx_pos : 0 < y - x := by
    simpa [hyx] using (half_pos δpos)
  have hyx_abs : |y - x| = δ / 2 := by
    simpa [hyx] using abs_of_pos hyx_pos
  have hxabs_xy : |x - y| = δ / 2 := by
    simpa [abs_sub_comm] using hyx_abs
  have hxydist : dist x y = δ / 2 := by
    simp [Real.dist_eq, hxabs_xy]
  have hxy_lt : dist x y < δ := by
    have : δ / 2 < δ := half_lt_self δpos
    simpa [hxydist] using this
  have hsq_lt : |x ^ 2 - y ^ 2| < 1 := by
    simpa [Real.dist_eq] using hδ hxy_lt
  have hsum_pos : 0 < x + y := add_pos hxpos hypos
  have hprod' : |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by
    simp [sq_sub_sq, abs_mul, mul_comm]
  have hprod :
      |x ^ 2 - y ^ 2| = (δ / 2) * (x + y) := by
    simpa [hxabs_xy, abs_of_pos hsum_pos] using hprod'
  have hδ2_nonneg : 0 ≤ δ / 2 :=
    div_nonneg (le_of_lt δpos) (by norm_num)
  have hxplus_le : 2 * x ≤ x + y := by
    have hxsum : x + y = x + x + δ / 2 := by
      simp [y, add_assoc]
    have hxplus : x + x ≤ x + x + δ / 2 :=
      le_add_of_nonneg_right hδ2_nonneg
    simpa [two_mul, hxsum] using hxplus
  have hxge' :
      (δ / 2) * (2 * x) ≤ (δ / 2) * (x + y) :=
    mul_le_mul_of_nonneg_left hxplus_le hδ2_nonneg
  have hxge : δ * x ≤ |x ^ 2 - y ^ 2| := by
    have hlhs : (δ / 2) * (2 * x) = δ * x := by
      ring
    simpa [hlhs, hprod.symm] using hxge'
  have hxvalue : δ * x = 2 := by
    have hδne : δ ≠ 0 := ne_of_gt δpos
    calc
      δ * x = δ * (2 / δ) := rfl
      _ = δ * (2 * δ⁻¹) := by simp [div_eq_mul_inv]
      _ = 2 * (δ * δ⁻¹) := by simp [mul_comm, mul_assoc]
      _ = 2 := by simp [hδne]
  have hxge2 : (2 : ℝ) ≤ |x ^ 2 - y ^ 2| := by
    simpa [hxvalue] using hxge
  have hxgt : (1 : ℝ) < |x ^ 2 - y ^ 2| :=
    lt_of_lt_of_le (by norm_num) hxge2
  exact (lt_irrefl (1 : ℝ)) (lt_trans hxgt hsq_lt)

/-- Example 3.4.3 helper: the point `min (δ/2) (1/3)` lies in `(0,1)`. -/
lemma min_half_delta_mem_Ioo {δ : ℝ} (hδ : 0 < δ) :
    min (δ / 2) (1 / 3) ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · have hhalf : 0 < δ / 2 := half_pos hδ
    have hthird : 0 < (1 : ℝ) / 3 := by norm_num
    exact lt_min hhalf hthird
  · have hthird_lt_one : (1 / 3 : ℝ) < 1 := by norm_num
    exact lt_of_le_of_lt (min_le_right _ _) hthird_lt_one

lemma inv_gap_for_double {t : ℝ} (ht : 0 < t) (hle : t ≤ 1 / 3) :
    |t⁻¹ - (2 * t)⁻¹| ≥ (3 : ℝ) / 2 := by
  have h2t_pos : 0 < 2 * t := mul_pos (by norm_num) ht
  have hdiff : |t⁻¹ - (2 * t)⁻¹| = 1 / (2 * t) := by
    have hpos : 0 < 1 / (2 * t) := one_div_pos.mpr h2t_pos
    have hneg : t⁻¹ - (2 * t)⁻¹ = 1 / (2 * t) := by
      have htne : t ≠ 0 := ne_of_gt ht
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have hcalc : t⁻¹ - (2 * t)⁻¹ = ((2 : ℝ) - 1) / (2 * t) := by
        field_simp [htne, htwo]
      have : ((2 : ℝ) - 1) = 1 := by norm_num
      simpa [this] using hcalc
    have hpos' : 0 < t⁻¹ - (2 * t)⁻¹ := hneg.symm ▸ hpos
    have habs : |t⁻¹ - (2 * t)⁻¹| = t⁻¹ - (2 * t)⁻¹ := abs_of_pos hpos'
    calc
      |t⁻¹ - (2 * t)⁻¹| = t⁻¹ - (2 * t)⁻¹ := habs
      _ = 1 / (2 * t) := hneg
  have htwo_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have h2t_le : 2 * t ≤ 2 / 3 := by
    have := mul_le_mul_of_nonneg_left hle htwo_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hbound :
      (3 : ℝ) / 2 ≤ 1 / (2 * t) := by
    have haux : 1 / (2 / 3 : ℝ) ≤ 1 / (2 * t) :=
      one_div_le_one_div_of_le h2t_pos h2t_le
    have : 1 / (2 / 3 : ℝ) = (3 : ℝ) / 2 := by norm_num
    simpa [this] using haux
  exact hdiff.symm ▸ hbound

lemma not_uniformContinuous_inv_on_Ioo :
    ¬ UniformContinuous (fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) := by
  classical
  intro h
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.uniformContinuous_iff).1 h 1 (by norm_num : (0 : ℝ) < 1)
  set t : ℝ := min (δ / 2) (1 / 3)
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [t] using min_half_delta_mem_Ioo hδpos
  have ht_pos : 0 < t := ht_mem.1
  have ht_le_third : t ≤ 1 / 3 := by
    dsimp [t]
    exact min_le_right _ _
  have ht_le_half : t ≤ δ / 2 := by
    dsimp [t]
    exact min_le_left _ _
  have hy_mem : 2 * t ∈ Set.Ioo (0 : ℝ) 1 := by
    have hy_pos : 0 < 2 * t := mul_pos (by norm_num) ht_pos
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have hle' : 2 * t ≤ 2 / 3 := by
      have := mul_le_mul_of_nonneg_left ht_le_third htwo_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hy_lt_one : 2 * t < 1 := lt_of_le_of_lt hle' (by norm_num : (2 : ℝ) / 3 < 1)
    exact ⟨hy_pos, hy_lt_one⟩
  let x0 : {x // x ∈ Set.Ioo (0 : ℝ) 1} := ⟨t, ht_mem⟩
  let y0 : {x // x ∈ Set.Ioo (0 : ℝ) 1} := ⟨2 * t, hy_mem⟩
  have hdist : dist x0 y0 = t := by
    change dist (x0 : ℝ) (y0 : ℝ) = t
    have : |(x0 : ℝ) - (y0 : ℝ)| = |-t| := by
      have hdiff : (x0 : ℝ) - (y0 : ℝ) = -t := by
        simp [x0, y0, t, sub_eq_add_neg, two_mul]
      simp [hdiff]
    simp [Real.dist_eq, this, abs_neg, abs_of_pos ht_pos]
  have hdist_le : dist x0 y0 ≤ δ / 2 := by
    simpa [hdist] using ht_le_half
  have hdist_lt : dist x0 y0 < δ :=
    lt_of_le_of_lt hdist_le (half_lt_self hδpos)
  have hdist_inv_lt :
      dist ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) x0)
        ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) y0) < 1 := by
    simpa using hδ hdist_lt
  have hdist_inv :
      dist ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) x0)
        ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) y0)
        = |t⁻¹ - (2 * t)⁻¹| := by
    simp [Real.dist_eq, x0, y0, t]
  have hge : (3 : ℝ) / 2 ≤
      dist ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) x0)
        ((fun x : {x // x ∈ Set.Ioo (0 : ℝ) 1} => (x : ℝ)⁻¹) y0) := by
    have := inv_gap_for_double ht_pos ht_le_third
    simpa [hdist_inv] using this
  have hlt : (3 : ℝ) / 2 < 1 :=
    lt_of_le_of_lt hge (by simpa [hdist_inv] using hdist_inv_lt)
  have : ¬ ((3 : ℝ) / 2 < 1) := by norm_num
  exact this hlt

/-- Theorem 3.4.4. If `f : ℝ → ℝ` is continuous on the closed interval `[a, b]`, then `f` is
uniformly continuous on `[a, b]`. -/
lemma uniformContinuousOn_Icc_of_continuous {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : UniformContinuousOn f (Set.Icc a b) := by
  simpa using (isCompact_Icc.uniformContinuousOn_of_continuous hf)

/-- Lemma 3.4.5. If `f : S → ℝ` is uniformly continuous and `(x_n)` is a Cauchy sequence in `S`,
then `(f x_n)` is also Cauchy. -/
lemma uniformContinuous.cauchySeq_image {S : Set ℝ} {f : S → ℝ} (hf : UniformContinuous f)
    {x : ℕ → S} (hx : CauchySeq x) : CauchySeq fun n => f (x n) := by
  classical
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuous_iff).1 hf ε hε
  obtain ⟨M, hM⟩ := (Metric.cauchySeq_iff.1 hx) δ hδpos
  refine ⟨M, ?_⟩
  intro n hn k hk
  exact hδ (hM n hn k hk)

lemma uniformContinuousOn.cauchySeq_image {S : Set ℝ} {f : ℝ → ℝ}
    (hf : UniformContinuousOn f S) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ S) (hxC : CauchySeq x) :
    CauchySeq fun n => f (x n) := by
  classical
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.1 hf) ε hε
  obtain ⟨M, hM⟩ := (Metric.cauchySeq_iff.1 hxC) δ hδpos
  refine ⟨M, ?_⟩
  intro n hn k hk
  have hmemn : x n ∈ S := hx n
  have hmemk : x k ∈ S := hx k
  have hdist : dist (x n) (x k) < δ := hM n hn k hk
  simpa using hδ (x n) hmemn (x k) hmemk hdist

lemma cauchySeq_of_tendsto {x : ℕ → ℝ} {l : ℝ}
    (hx : Tendsto x atTop (nhds l)) : CauchySeq x := by
  classical
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := half_pos hε
  have hball :
      {y : ℝ | dist y l < ε / 2} ∈ nhds l :=
    Metric.ball_mem_nhds _ hhalf
  have heventually : ∀ᶠ n in atTop, dist (x n) l < ε / 2 :=
    (Filter.Tendsto.eventually hx) hball
  rcases eventually_atTop.1 heventually with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hdm : dist (x m) l < ε / 2 := hN m hm
  have hdn : dist (x n) l < ε / 2 := hN n hn
  have htri : dist (x m) (x n) ≤ dist (x m) l + dist (x n) l := by
    simpa [dist_comm] using dist_triangle_left (x m) (x n) l
  have hsum : dist (x m) l + dist (x n) l < ε := by
    have : dist (x m) l + dist (x n) l < ε / 2 + ε / 2 :=
      add_lt_add hdm hdn
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
  exact lt_of_le_of_lt htri hsum

private lemma inclusion_Ioo_Icc_subset {a b : ℝ} :
    Set.Ioo a b ⊆ Set.Icc a b := by
  intro x hx
  exact ⟨(le_of_lt hx.1), (le_of_lt hx.2)⟩

lemma denseInducing_subtype_Ioo_Icc {a b : ℝ} (h : a < b) :
    IsDenseInducing
      (Set.inclusion (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)) := by
  classical
  set i :=
    Set.inclusion (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)
  have hi_comp :
      IsInducing
        ((fun x : Set.Icc a b => (x : ℝ)) ∘ i) := by
    simpa [i, Set.val_comp_inclusion] using
      (IsInducing.subtypeVal :
          IsInducing (Subtype.val : Set.Ioo a b → ℝ))
  have hi_ind :
      IsInducing i :=
    (IsInducing.of_comp_iff
        (f := i)
        (g := fun x : Set.Icc a b => (x : ℝ))
        (IsInducing.subtypeVal :
            IsInducing (Subtype.val : Set.Icc a b → ℝ))).1 hi_comp
  have hclosureIoo : closure (Set.Ioo a b) = Set.Icc a b :=
    closure_Ioo h.ne
  have hclosure :
      Set.Icc a b ⊆ closure (Set.Ioo a b) := by
    intro x hx
    simpa [hclosureIoo] using hx
  have hdense :
      DenseRange i :=
    (denseRange_inclusion_iff
        (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)).2 hclosure
  exact ⟨hi_ind, hdense⟩

lemma uniformInducing_subtype_Ioo_Icc {a b : ℝ} :
    IsUniformInducing
      (Set.inclusion (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)) := by
  classical
  set i :=
    Set.inclusion (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)
  have hi_comp :
      IsUniformInducing
        ((fun x : Set.Icc a b => (x : ℝ)) ∘ i) := by
    simpa [i, Set.val_comp_inclusion] using
      (isUniformInducing_val (Set.Ioo a b) :
          IsUniformInducing (Subtype.val : Set.Ioo a b → ℝ))
  exact
    (IsUniformInducing.of_comp_iff
        (f := i)
        (g := fun x : Set.Icc a b => (x : ℝ))
        (isUniformInducing_val (Set.Icc a b))).1 hi_comp

lemma uniformContinuousOn_extend_to_Icc {a b : ℝ} {f : ℝ → ℝ}
    (h : a < b) (hf : UniformContinuousOn f (Set.Ioo a b)) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Set.Icc a b) ∧
      Set.EqOn g f (Set.Ioo a b) ∧
      Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (g a)) ∧
      Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (g b)) := by
  classical
  let i :=
    Set.inclusion (inclusion_Ioo_Icc_subset : Set.Ioo a b ⊆ Set.Icc a b)
  have hi_dense : DenseRange i :=
    (denseInducing_subtype_Ioo_Icc h).dense
  have hi_uniform : IsUniformInducing i :=
    uniformInducing_subtype_Ioo_Icc
  have hf_subtype :
      UniformContinuous fun x : Set.Ioo a b => f x := by
    refine (Metric.uniformContinuous_iff).2 ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.uniformContinuousOn_iff).1 hf ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro x y hxy
    exact hδ (x := (x : ℝ)) (y := (y : ℝ)) x.property y.property hxy
  let ψ :=
    IsDenseInducing.extend
      ((IsUniformInducing.isDenseInducing hi_uniform hi_dense))
      (fun x : Set.Ioo a b => f x)
  have hψ_uniform :
      UniformContinuous ψ :=
    uniformContinuous_uniformly_extend hi_uniform hi_dense hf_subtype
  let g : ℝ → ℝ :=
    fun x => if hx : x ∈ Set.Icc a b then ψ ⟨x, hx⟩ else f x
  have hrestrict :
      (Set.Icc a b).restrict g = ψ := by
    classical
    funext x
    have hx : (x : ℝ) ∈ Set.Icc a b := x.property
    dsimp [Set.restrict, g]
    by_cases hx_mem : (x : ℝ) ∈ Set.Icc a b
    · have hx_eq :
          (⟨(x : ℝ), hx_mem⟩ : Set.Icc a b) = x := by
        ext
        rfl
      simp [hx_mem, hx_eq]
    · exact (hx_mem hx).elim
  have hg_cont :
      ContinuousOn g (Set.Icc a b) := by
    refine (continuousOn_iff_continuous_restrict).2 ?_
    simpa [hrestrict] using hψ_uniform.continuous
  have hg_eq :
      Set.EqOn g f (Set.Ioo a b) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b :=
      inclusion_Ioo_Icc_subset hx
    have hψ_val :
        ψ ⟨x, hxIcc⟩ = f x := by
      simpa [i] using
        uniformly_extend_of_ind hi_uniform hi_dense hf_subtype ⟨x, hx⟩
    have hgx : g x = ψ ⟨x, hxIcc⟩ := by
      dsimp [g]
      by_cases hx_mem : x ∈ Set.Icc a b
      · have hx_eq :
            (⟨x, hx_mem⟩ : Set.Icc a b) = ⟨x, hxIcc⟩ := by
          ext
          rfl
        simp [hx_mem, hx_eq]
      · exact (hx_mem hxIcc).elim
    exact hgx.trans hψ_val
  have ha_mem : a ∈ Set.Icc a b :=
    ⟨le_rfl, le_of_lt h⟩
  have hb_mem : b ∈ Set.Icc a b :=
    ⟨le_of_lt h, le_rfl⟩
  have hcont_a :
      ContinuousWithinAt g (Set.Icc a b) a :=
    hg_cont.continuousWithinAt ha_mem
  have hcont_b :
      ContinuousWithinAt g (Set.Icc a b) b :=
    hg_cont.continuousWithinAt hb_mem
  have hIcc_mem_left :
      Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) := by
    refine mem_nhdsWithin.2 ?_
    refine ⟨Set.Ioo (a - 1) b, isOpen_Ioo, ?_, ?_⟩
    · exact ⟨by linarith, h⟩
    · intro x hx
      have hx₁ : a < x := hx.2
      have hx₂ : x < b := hx.1.2
      exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩
  have hIcc_mem_right :
      Set.Icc a b ∈ nhdsWithin b (Set.Iio b) := by
    refine mem_nhdsWithin.2 ?_
    refine ⟨Set.Ioo a (b + 1), isOpen_Ioo, ?_, ?_⟩
    · exact ⟨h, by linarith⟩
    · intro x hx
      have hx₁ : a < x := hx.1.1
      have hx₂ : x < b := hx.2
      exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩
  have hcont_Ioi :
      ContinuousWithinAt g (Set.Ioi a) a :=
    hcont_a.mono_of_mem_nhdsWithin hIcc_mem_left
  have hcont_Iio :
      ContinuousWithinAt g (Set.Iio b) b :=
    hcont_b.mono_of_mem_nhdsWithin hIcc_mem_right
  have hIoo_mem_left :
      Set.Ioo a b ∈ nhdsWithin a (Set.Ioi a) := by
    refine mem_nhdsWithin.2 ?_
    refine ⟨Set.Ioo (a - (b - a)/2) (a + (b - a)/2), isOpen_Ioo, ?_, ?_⟩
    · constructor <;> linarith
    · intro x hx
      have hx₁ : a < x := hx.2
      have hx₂ : x < a + (b - a) / 2 := hx.1.2
      have hx₂' : x < b := by
        have hxsum : a + (b - a) / 2 < b := by linarith
        exact lt_of_lt_of_le hx₂ (le_of_lt hxsum)
      exact ⟨hx₁, hx₂'⟩
  have hIoo_mem_right :
      Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
    refine mem_nhdsWithin.2 ?_
    refine ⟨Set.Ioo (b - (b - a)/2) (b + (b - a)/2), isOpen_Ioo, ?_, ?_⟩
    · constructor <;> linarith
    · intro x hx
      have hx₁ : b - (b - a) / 2 < x := hx.1.1
      have hx₂ : x < b := hx.2
      have hx₁' : a < x := by
        have hxaux : b - (b - a) / 2 = (a + b) / 2 := by ring
        have hmid_lt : (a + b) / 2 < x := by simpa [hxaux] using hx₁
        have ha_mid : a < (a + b) / 2 := by linarith
        exact lt_trans ha_mid hmid_lt
      exact ⟨hx₁', hx₂⟩
  have h_eventually_left :
      g =ᶠ[nhdsWithin a (Set.Ioi a)] f := by
    refine Filter.eventually_of_mem hIoo_mem_left ?_
    intro x hx
    simpa using hg_eq hx
  have h_eventually_right :
      g =ᶠ[nhdsWithin b (Set.Iio b)] f := by
    refine Filter.eventually_of_mem hIoo_mem_right ?_
    intro x hx
    simpa using hg_eq hx
  refine ⟨g, hg_cont, hg_eq, ?_, ?_⟩
  · have hmaps_left : Set.MapsTo g (Set.Ioi a) Set.univ :=
      fun _ _ => Set.mem_univ _
    have hleft :
        Tendsto g (nhdsWithin a (Set.Ioi a)) (nhds (g a)) := by
      simpa [nhdsWithin_univ] using
        hcont_Ioi.tendsto_nhdsWithin (t := Set.univ) hmaps_left
    exact hleft.congr' h_eventually_left
  · have hmaps_right : Set.MapsTo g (Set.Iio b) Set.univ :=
      fun _ _ => Set.mem_univ _
    have hright :
        Tendsto g (nhdsWithin b (Set.Iio b)) (nhds (g b)) := by
      simpa [nhdsWithin_univ] using
        hcont_Iio.tendsto_nhdsWithin (t := Set.univ) hmaps_right
    exact hright.congr' h_eventually_right

/-- Proposition 3.4.6. Suppose `a < b`. A function `f : (a, b) → ℝ` is uniformly continuous if
and only if the limits `L_a = lim_{x → a} f x`, `L_b = lim_{x → b} f x` exist and an extension to
the closed interval sending `a` to `L_a`, `b` to `L_b`, and agreeing with `f` on `(a, b)` is
continuous. -/
lemma uniformContinuousOn_Ioo_iff_limits_extend {a b : ℝ} (h : a < b) (f : ℝ → ℝ) :
    UniformContinuousOn f (Set.Ioo a b) ↔
      ∃ L_a L_b : ℝ,
        Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds L_a) ∧
        Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L_b) ∧
        ∃ g : ℝ → ℝ,
          ContinuousOn g (Set.Icc a b) ∧
          (∀ x ∈ Set.Ioo a b, g x = f x) ∧
          g a = L_a ∧ g b = L_b := by
  classical
  constructor
  · intro hf
    obtain ⟨g, hg_cont, hg_eq, ha, hb⟩ :=
      uniformContinuousOn_extend_to_Icc h hf
    refine ⟨g a, g b, ha, hb, g, hg_cont, ?_, rfl, rfl⟩
    exact fun x hx => hg_eq hx
  · rintro ⟨L_a, L_b, hta, htb, g, hg, hgf, hga, hgb⟩
    have hUC : UniformContinuousOn g (Set.Icc a b) :=
      uniformContinuousOn_Icc_of_continuous hg
    have hsubset : Set.Ioo a b ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨(le_of_lt hx.1), (le_of_lt hx.2)⟩
    exact
      (hUC.mono hsubset).congr fun x hx => hgf x hx

/-- Definition 3.4.7. A function `f : S → ℝ` is Lipschitz continuous if there exists
`K ∈ ℝ` such that `|f x - f y| ≤ K * |x - y|` for all `x, y ∈ S`. -/
def book_lipschitzOn (S : Set ℝ) (f : S → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : S, |f x - f y| ≤ K * |(x : ℝ) - (y : ℝ)|

/-- The book definition of Lipschitz continuity on a subset of `ℝ` coincides with the
existence of some `ℝ≥0` Lipschitz constant for the subtype. -/
lemma book_lipschitzOn_iff_lipschitzWith {S : Set ℝ} {f : S → ℝ} :
    book_lipschitzOn S f ↔ ∃ K : NNReal, LipschitzWith K f := by
  constructor
  · rintro ⟨K, hK0, hK⟩
    refine ⟨⟨K, hK0⟩, ?_⟩
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Real.dist_eq] using hK x y
  · rintro ⟨K, hK⟩
    refine ⟨(K : ℝ), K.property, ?_⟩
    intro x y
    have h' := (LipschitzWith.dist_le_mul hK x y)
    simpa [Real.dist_eq] using h'

/-- Proposition 3.4.8. A Lipschitz continuous function is uniformly continuous. -/
lemma uniformContinuous_of_book_lipschitzOn {S : Set ℝ} {f : S → ℝ}
    (hf : book_lipschitzOn S f) : UniformContinuous f := by
  obtain ⟨K, hK⟩ := (book_lipschitzOn_iff_lipschitzWith).1 hf
  exact hK.uniformContinuous

/-- Example 3.4.9. The sine function `ℝ → ℝ` is Lipschitz continuous with constant `1`, as
`|sin x - sin y| ≤ |x - y|` for all real `x, y`. -/
lemma lipschitzWith_one_real_sin :
    LipschitzWith (1 : NNReal) fun x : ℝ => Real.sin x := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [Real.dist_eq, NNReal.coe_one, one_mul] using Real.abs_sin_sub_sin_le x y

/-- Example 3.4.9. The cosine function `ℝ → ℝ` is Lipschitz continuous with constant `1`, since
`|cos x - cos y| ≤ |x - y|` for all real `x, y`. -/
lemma lipschitzWith_one_real_cos :
    LipschitzWith (1 : NNReal) fun x : ℝ => Real.cos x := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [Real.dist_eq, NNReal.coe_one, one_mul] using Real.abs_cos_sub_cos_le x y

lemma sqrt_sub_le_sqrt_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sqrt y - Real.sqrt x ≤ Real.sqrt (y - x) := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hyx_nonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hx_le : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hmul : x ≤ Real.sqrt y * Real.sqrt x := by
    have hx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hmul' := mul_le_mul_of_nonneg_right hx_le hx_nonneg
    have hx_sq : Real.sqrt x * Real.sqrt x = x := by
      simpa using Real.mul_self_sqrt hx
    simpa [hx_sq] using hmul'
  have hx_sub_nonpos : x - Real.sqrt y * Real.sqrt x ≤ 0 :=
    sub_nonpos.mpr hmul
  have hsq :
      (Real.sqrt y - Real.sqrt x) ^ 2 =
        (y - x) + 2 * (x - Real.sqrt y * Real.sqrt x) := by
    have hpow :
        (Real.sqrt y - Real.sqrt x) ^ 2 =
          Real.sqrt y ^ 2 - 2 * Real.sqrt y * Real.sqrt x + Real.sqrt x ^ 2 := by
      ring
    have hsqy : Real.sqrt y ^ 2 = y := by
      simpa [pow_two] using Real.mul_self_sqrt hy
    have hsqx : Real.sqrt x ^ 2 = x := by
      simpa [pow_two] using Real.mul_self_sqrt hx
    have hpow' :
        (Real.sqrt y - Real.sqrt x) ^ 2 =
          y - 2 * Real.sqrt y * Real.sqrt x + x := by
      simpa [hsqy, hsqx] using hpow
    have hcalc :
        y - 2 * Real.sqrt y * Real.sqrt x + x =
          (y - x) + 2 * (x - Real.sqrt y * Real.sqrt x) := by ring
    simpa [hcalc] using hpow'
  have hsq_le :
      (Real.sqrt y - Real.sqrt x) ^ 2 ≤ (Real.sqrt (y - x)) ^ 2 := by
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have htwo_mul :
        2 * (x - Real.sqrt y * Real.sqrt x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos htwo_nonneg hx_sub_nonpos
    have hsum_le :
        (y - x) + 2 * (x - Real.sqrt y * Real.sqrt x) ≤ y - x := by
      have := add_le_add_left htwo_mul (y - x)
      simpa using this
    have hsq' :
        (Real.sqrt y - Real.sqrt x) ^ 2 ≤ y - x := by
      simpa [hsq] using hsum_le
    have hsqrt_sq :
        (Real.sqrt (y - x)) ^ 2 = y - x := by
      simpa [pow_two] using Real.mul_self_sqrt hyx_nonneg
    simpa [hsqrt_sq] using hsq'
  have hnonneg_sq :
      0 ≤ Real.sqrt y - Real.sqrt x :=
    sub_nonneg.mpr hx_le
  have hnonneg :
      0 ≤ Real.sqrt (y - x) :=
    Real.sqrt_nonneg _
  have habs :
      |Real.sqrt y - Real.sqrt x| ≤ |Real.sqrt (y - x)| :=
    (sq_le_sq).1 hsq_le
  have hleft :
      |Real.sqrt y - Real.sqrt x| = Real.sqrt y - Real.sqrt x :=
    abs_of_nonneg hnonneg_sq
  have hright :
      |Real.sqrt (y - x)| = Real.sqrt (y - x) :=
    abs_of_nonneg hnonneg
  simpa [hleft, hright] using habs

lemma abs_sqrt_sub_le_sqrt_abs {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  classical
  cases le_total x y with
  | inl hxy =>
      have hle : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
      have hxabs :
          |Real.sqrt x - Real.sqrt y| = Real.sqrt y - Real.sqrt x := by
        have hnonpos : Real.sqrt x - Real.sqrt y ≤ 0 := sub_nonpos.mpr hle
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using (abs_of_nonpos hnonpos)
      have habs_xy :
          |x - y| = y - x := by
        have hnonpos : x - y ≤ 0 := sub_nonpos.mpr hxy
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using (abs_of_nonpos hnonpos)
      have hle := sqrt_sub_le_sqrt_sub hx hxy
      simpa [hxabs, habs_xy] using hle
  | inr hyx =>
      have hle : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
      have hxabs :
          |Real.sqrt x - Real.sqrt y| = Real.sqrt x - Real.sqrt y := by
        have hnonneg : 0 ≤ Real.sqrt x - Real.sqrt y := sub_nonneg.mpr hle
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using (abs_of_nonneg hnonneg)
      have habs_xy :
          |x - y| = x - y := by
        have hnonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using (abs_of_nonneg hnonneg)
      have hle := sqrt_sub_le_sqrt_sub hy hyx
      simpa [hxabs, habs_xy] using hle

/-- Example 3.4.10. The square root function `f(x) = √x` is Lipschitz continuous on
`[1, ∞)` with constant `1/2`, as `|√x - √y| ≤ (1/2) |x - y|` for `x, y ≥ 1`. -/
lemma book_lipschitzOn_sqrt_Ici_one :
    book_lipschitzOn (Set.Ici (1 : ℝ)) (fun x : Set.Ici (1 : ℝ) => Real.sqrt x) := by
  classical
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro x y
  set sx : ℝ := Real.sqrt (x : ℝ)
  set sy : ℝ := Real.sqrt (y : ℝ)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := x.property
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := y.property
  have hx_nonneg : 0 ≤ (x : ℝ) := le_trans (by norm_num) hx1
  have hy_nonneg : 0 ≤ (y : ℝ) := le_trans (by norm_num) hy1
  have hx_pos : 0 < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx1
  have hy_pos : 0 < (y : ℝ) := lt_of_lt_of_le (by norm_num) hy1
  have hxcalc :
      (sx - sy) * (sx + sy) = (x : ℝ) - (y : ℝ) := by
    have hsq :
        (Real.sqrt (x : ℝ)) ^ 2 = (x : ℝ) := by
      simpa [pow_two, sx] using Real.mul_self_sqrt hx_nonneg
    have hsq' :
        (Real.sqrt (y : ℝ)) ^ 2 = (y : ℝ) := by
      simpa [pow_two, sy] using Real.mul_self_sqrt hy_nonneg
    have h :=
        (sq_sub_sq (Real.sqrt (x : ℝ)) (Real.sqrt (y : ℝ))).symm
    simpa [sx, sy, hsq, hsq', mul_comm, mul_left_comm, mul_assoc] using h
  have hsum_nonneg :
      0 ≤ sx + sy :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod :
      |sx - sy| * (sx + sy) = |(x : ℝ) - (y : ℝ)| := by
    have hleft :
        |sx - sy| * (sx + sy) = |(sx - sy) * (sx + sy)| := by
      calc
        |sx - sy| * (sx + sy)
            = |sx - sy| * |sx + sy| := by simp [abs_of_nonneg hsum_nonneg]
        _ = |(sx - sy) * (sx + sy)| := by
          exact (abs_mul (sx - sy) (sx + sy)).symm
    have hright :
        |(sx - sy) * (sx + sy)| = |(x : ℝ) - (y : ℝ)| := by
      exact congrArg abs hxcalc
    exact hleft.trans hright
  have hsum_pos : 0 < sx + sy :=
    add_pos (Real.sqrt_pos.mpr hx_pos) (Real.sqrt_pos.mpr hy_pos)
  have hratio :
      |sx - sy| = |(x : ℝ) - (y : ℝ)| / (sx + sy) := by
    have hsum_ne : sx + sy ≠ 0 := ne_of_gt hsum_pos
    exact (eq_div_iff_mul_eq hsum_ne).2 hprod
  have hxge_one :
      (1 : ℝ) ≤ sx := by
    have := Real.sqrt_le_sqrt hx1
    simpa [sx] using this
  have hyge_one :
      (1 : ℝ) ≤ sy := by
    have := Real.sqrt_le_sqrt hy1
    simpa [sy] using this
  have hsum_ge_two :
      (2 : ℝ) ≤ sx + sy := by
    have h := add_le_add hxge_one hyge_one
    simpa [sx, sy, one_add_one_eq_two, add_comm, add_left_comm, add_assoc] using h
  have hrec_le :
      1 / (sx + sy) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hsum_ge_two
  have hratio' :
      |sx - sy| ≤ (1 / 2) * |(x : ℝ) - (y : ℝ)| := by
    have hxratio' :
        |sx - sy|
          = |(x : ℝ) - (y : ℝ)| * (1 / (sx + sy)) := by
      simpa [div_eq_mul_inv] using hratio
    have h :=
        mul_le_mul_of_nonneg_left hrec_le
          (abs_nonneg ((x : ℝ) - (y : ℝ)))
    simpa [hxratio', mul_comm, mul_left_comm, mul_assoc] using h
  simpa [sx, sy] using hratio'

/-- Example 3.4.10. The square root function `g(x) = √x` on `[0, ∞)` is not Lipschitz
continuous; no global constant `K` can satisfy `|√x - √y| ≤ K |x - y|` on the whole domain. -/
lemma not_book_lipschitzOn_sqrt_Ici_zero :
    ¬ book_lipschitzOn (Set.Ici (0 : ℝ)) (fun x : Set.Ici (0 : ℝ) => Real.sqrt x) := by
  classical
  intro h
  rcases h with ⟨K, hK0, hK⟩
  by_cases hKzero : K = 0
  · have hx := hK ⟨1, by simp⟩ ⟨0, by simp⟩
    have hleft :
        |Real.sqrt (1 : ℝ) - Real.sqrt (0 : ℝ)| = 1 := by simp
    have hright : |(1 : ℝ) - (0 : ℝ)| = 1 := by simp
    have : (1 : ℝ) ≤ 0 := by
      simpa [hleft, hright, hKzero] using hx
    exact (show ¬ ((1 : ℝ) ≤ 0) by norm_num) this
  · have hKpos : 0 < K := lt_of_le_of_ne hK0 (by simpa [eq_comm] using hKzero)
    set t : ℝ := 1 / (2 * K)
    have ht_pos : 0 < t :=
      one_div_pos.mpr (mul_pos (by norm_num) hKpos)
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    let x0 : Set.Ici (0 : ℝ) := ⟨t ^ 2, by simpa using sq_nonneg t⟩
    let y0 : Set.Ici (0 : ℝ) := ⟨0, by simp⟩
    have hsqrt_x :
        Real.sqrt (x0 : ℝ) = t := by
      have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
      simpa [x0, t, pow_two, abs_of_pos ht_pos] using Real.sqrt_sq ht_nonneg
    have hsqrt_y :
        Real.sqrt (y0 : ℝ) = 0 := by
      simp [y0]
    have hineq :
        t ≤ K * t ^ 2 := by
      simpa [x0, y0, hsqrt_x, hsqrt_y, abs_of_pos ht_pos,
        abs_of_nonneg (sq_nonneg t)] using hK x0 y0
    have hcontr :
        1 ≤ K * t := by
      have hinv_nonneg : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht_pos)
      have hmult :=
        mul_le_mul_of_nonneg_left hineq hinv_nonneg
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, ht_ne] using hmult
    have hcalc : K * t * 2 = 1 := by
      have hKne : K ≠ 0 := hKzero
      have hden : 2 * K ≠ 0 := mul_ne_zero (by norm_num) hKne
      simpa [t, mul_comm, mul_left_comm, mul_assoc, hden] using
        (mul_inv_cancel₀ hden)
    have hKt : K * t = 1 / 2 := by
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have hcalc' : (K * t) * 2 = (1 / 2) * 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcalc
      exact (mul_right_cancel₀ htwo hcalc')
    have : (1 : ℝ) ≤ 1 / 2 := by simpa [hKt] using hcontr
    exact (show ¬ ((1 : ℝ) ≤ (1 / 2 : ℝ)) by norm_num) this

/-- Example 3.4.10. Although not Lipschitz on `[0, ∞)`, the square root function is uniformly
continuous on that domain. -/
lemma uniformContinuous_sqrt_Ici_zero :
    UniformContinuous (fun x : Set.Ici (0 : ℝ) => Real.sqrt x) := by
  classical
  refine (Metric.uniformContinuous_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hδpos : 0 < (ε / 2) ^ 2 := by
    simpa [pow_two] using mul_pos hε2 hε2
  refine ⟨(ε / 2) ^ 2, hδpos, ?_⟩
  intro x y hxy
  have hxy' :
      |(x : ℝ) - (y : ℝ)| < (ε / 2) ^ 2 := by
    have : dist (x : ℝ) (y : ℝ) < (ε / 2) ^ 2 := by
      simpa [Real.dist_eq] using hxy
    simpa [Real.dist_eq] using this
  have hx0 : 0 ≤ (x : ℝ) := x.property
  have hy0 : 0 ≤ (y : ℝ) := y.property
  have hineq :=
    abs_sqrt_sub_le_sqrt_abs (x := (x : ℝ)) (y := (y : ℝ)) hx0 hy0
  have hsqrt_le :
      Real.sqrt |(x : ℝ) - (y : ℝ)| ≤ Real.sqrt ((ε / 2) ^ 2) :=
    Real.sqrt_le_sqrt (le_of_lt hxy')
  have hroot_eq :
      Real.sqrt ((ε / 2) ^ 2) = ε / 2 := by
    have hnonneg : 0 ≤ ε / 2 := le_of_lt hε2
    simpa [pow_two, abs_of_nonneg hnonneg] using (Real.sqrt_sq hnonneg)
  have hfinal :
      |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| ≤ ε / 2 :=
    by
      have := le_trans hineq hsqrt_le
      simpa [hroot_eq] using this
  have hstrict :
      |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| < ε :=
    lt_of_le_of_lt hfinal (half_lt_self hε)
  have hdist :
      dist
          (Real.sqrt (x : ℝ))
          (Real.sqrt (y : ℝ)) =
        |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| := by
    simp [Real.dist_eq]
  simpa [hdist] using hstrict

end Section04
end Chap03
