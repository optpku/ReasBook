/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open scoped BigOperators

open IntersectionCut

-- This source-facing file keeps the tableau-row data from Example 6.10 explicit, while reusing
-- the Section 6.2 intersection-cut owner and the Chapter 5 mixed-integer-cut owner.

noncomputable section

section Example610

variable {n p : ℕ}

/-- The fractional part `f = b - floor b` of the tableau right-hand side. -/
def gomory_row_fraction
    (b : ℝ) : ℝ :=
  Int.fract b

/-- `gomory_row_fraction b` is the fractional part of `b`. -/
theorem gomory_row_fraction_def
    (b : ℝ) :
    gomory_row_fraction b = Int.fract b :=
  rfl

/-- The integral split normal `π` from (6.13), attached to one tableau row
`x_i = b - ∑ j, a j * x j`. The coefficient vector `a` is understood to be extended by zero
outside the nonbasic index set. -/
def gomory_tableau_split_normal
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Fin n → ℤ :=
  fun j ↦
    if j = Fin.castLE hpn i then
      1
    else if j.1 < p then
      if Int.fract (a j) ≤ gomory_row_fraction b then
        Int.floor (a j)
      else
        Int.ceil (a j)
    else
      0

/-- The split normal from Example 6.10 is given by the displayed case distinction (6.13). -/
theorem gomory_tableau_split_normal_apply
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) :
    gomory_tableau_split_normal hpn a i b j =
      if j = Fin.castLE hpn i then
        1
      else if j.1 < p then
        if Int.fract (a j) ≤ gomory_row_fraction b then
          Int.floor (a j)
        else
          Int.ceil (a j)
      else
        0 :=
  rfl

/-- The split set `C = {x : R^n | pi0 <= pi x <= pi0 + 1}` determined by the tableau row
of Example 6.10. -/
def gomory_tableau_split_set
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x |
    (Int.floor b : ℝ) ≤
        ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h ∧
      (∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h) ≤
        (Int.floor b : ℝ) + 1}

/-- Membership in `gomory_tableau_split_set hpn a i b` is exactly the displayed split
inequality `pi0 <= pi x <= pi0 + 1`. -/
theorem mem_gomory_tableau_split_set_iff
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ gomory_tableau_split_set hpn a i b ↔
      (Int.floor b : ℝ) ≤
          ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h ∧
        (∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * x h) ≤
          (Int.floor b : ℝ) + 1 :=
  Iff.rfl

/-- The basic feasible point attached to the tableau row `x_i = b - ∑ j, a_j x_j`, with
basic coordinate `x_i = b` and all other coordinates equal to `0`. -/
def gomory_tableau_row_vertex
    (hpn : p ≤ n)
    (i : Fin p)
    (b : ℝ) : Fin n → ℝ :=
  fun h ↦
    if h = Fin.castLE hpn i then
      b
    else
      0

/-- The tableau-row vertex from Example 6.10 has `b` in the basic coordinate `i` and `0`
elsewhere. -/
theorem gomory_tableau_row_vertex_apply
    (hpn : p ≤ n)
    (i : Fin p)
    (b : ℝ)
    (h : Fin n) :
    gomory_tableau_row_vertex hpn i b h =
      if h = Fin.castLE hpn i then
        b
      else
        0 :=
  rfl

/-- The tableau ray `r^j` used in Example 6.10: the `j`th nonbasic variable increases by one,
and the basic variable `x_i` changes by `-a_j`. -/
def gomory_tableau_row_ray
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (j : Fin n) : Fin n → ℝ :=
  fun h ↦
    if h = j then
      1
    else if h = Fin.castLE hpn i then
      -a j
    else
      0

/-- The tableau ray from Example 6.10 has unit `j`th coordinate, `-a_j` in the basic
coordinate `i`, and zero elsewhere. -/
theorem gomory_tableau_row_ray_apply
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (j h : Fin n) :
    gomory_tableau_row_ray hpn a i j h =
      if h = j then
        1
      else if h = Fin.castLE hpn i then
        -a j
      else
        0 :=
  rfl

/-- The nonbasic indices of the tableau row from Example 6.10, modeled as all ambient indices
other than the distinguished basic index `i`. -/
abbrev gomory_tableau_nonbasic_index
    (hpn : p ≤ n)
    (i : Fin p) :=
  {j : Fin n // j ≠ Fin.castLE hpn i}

/-- The value `pi r^j` of the split normal on the tableau ray indexed by `j`. -/
def gomory_tableau_split_direction_value
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ℝ :=
  ∑ h : Fin n, (gomory_tableau_split_normal hpn a i b h : ℝ) * gomory_tableau_row_ray hpn a i j h

/-- The ray-intersection parameter `alpha_j` computed in Example 6.10 from the split set of the
tableau row. -/
def gomory_tableau_split_ray_parameter
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ENNReal :=
  ray_intersection_parameter
    (gomory_tableau_split_set hpn a i b)
    (gomory_tableau_row_vertex hpn i b)
    (gomory_tableau_row_ray hpn a i)
    j

/-- The split-intersection-cut coefficient `1 / alpha_j` obtained from Example 6.10. -/
def gomory_tableau_split_intersection_coefficient
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n) : ℝ :=
  intersection_cut_coeff
    (gomory_tableau_split_set hpn a i b)
    (gomory_tableau_row_vertex hpn i b)
    (gomory_tableau_row_ray hpn a i)
    j

/-- The split-intersection cut attached to the split set from Example 6.10. -/
def gomory_tableau_split_intersection_cut
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x |
    1 ≤ ∑ j : gomory_tableau_nonbasic_index hpn i,
      gomory_tableau_split_intersection_coefficient hpn a i b j * x j}

/-- Membership in `gomory_tableau_split_intersection_cut hpn a i b` is exactly the normalized
intersection-cut inequality generated from the split set of Example 6.10. -/
theorem mem_gomory_tableau_split_intersection_cut_iff
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ gomory_tableau_split_intersection_cut hpn a i b ↔
      1 ≤ ∑ j : gomory_tableau_nonbasic_index hpn i,
        gomory_tableau_split_intersection_coefficient hpn a i b j * x j :=
  Iff.rfl

/-- The direct Gomory mixed-integer coefficient from the tableau row formula (6.15), again with
`a` extended by zero outside the nonbasic index set. -/
def gomory_mixed_integer_cut_coefficient
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b)
    (j : Fin n) : ℝ :=
  gomory_mixed_integer_inequality_coefficient
    (Finset.univ.filter fun h : Fin n ↦ h.1 < p)
    a
    b
    hfrac
    j

/-- The Gomory mixed-integer cut generated by the tableau row. -/
def gomory_mixed_integer_cut
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_inequality
    (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
    a
    b
    hfrac

/-- Membership in `gomory_mixed_integer_cut p a b` is exactly the normalized Gomory mixed
integer inequality of (6.15). -/
theorem mem_gomory_mixed_integer_cut_iff
    (p : ℕ)
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b)
    (x : Fin n → ℝ) :
    x ∈ gomory_mixed_integer_cut p a b hfrac ↔
      1 ≤ ∑ j : Fin n, gomory_mixed_integer_cut_coefficient p a b hfrac j * x j := by
  rw [gomory_mixed_integer_cut, mem_gomory_mixed_integer_inequality_iff]
  rfl

/-- The integer-variable coefficient function `pi` from (6.16). -/
def gomory_integer_function
    (f : ℝ)
    (r : ℝ) : ℝ :=
  min
    ((r - (Int.floor r : ℝ)) / (1 - f))
    ((((Int.floor r : ℝ) + 1) - r) / f)

/-- `gomory_integer_function f r` is the minimum of the two affine expressions from (6.16). -/
theorem gomory_integer_function_def
    (f : ℝ)
    (r : ℝ) :
    gomory_integer_function f r =
      min
        ((r - (Int.floor r : ℝ)) / (1 - f))
        ((((Int.floor r : ℝ) + 1) - r) / f) :=
  rfl

/-- The continuous-variable coefficient function `psi` from (6.16). -/
def gomory_continuous_function
    (f : ℝ)
    (r : ℝ) : ℝ :=
  max (r / (1 - f)) ((-r) / f)

/-- `gomory_continuous_function f r` is the maximum of the two affine expressions from (6.16). -/
theorem gomory_continuous_function_def
    (f : ℝ)
    (r : ℝ) :
    gomory_continuous_function f r = max (r / (1 - f)) ((-r) / f) :=
  rfl

/-- Example 6.10 (1). For a tableau row
`x_i = b - ∑ j, a j * x j` with `a` extended by zero outside the nonbasic indices, the split
normal (6.13) evaluates on the tableau ray `r^j` by the displayed formula (6.14). -/
theorem example_6_10_split_direction_value_eq_piecewise
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n)
    (hj : j ≠ Fin.castLE hpn i) :
    gomory_tableau_split_direction_value hpn a i b j =
      if j.1 < p then
        if Int.fract (a j) ≤ gomory_row_fraction b then
          -Int.fract (a j)
        else
          1 - Int.fract (a j)
      else
        -a j := by
  classical
  -- Isolate the ray's unit coordinate and its distinguished basic coordinate in the sum.
  rw [gomory_tableau_split_direction_value]
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hbasic_mem :
      Fin.castLE hpn i ∈ (Finset.univ.erase j : Finset (Fin n)) := by
    simp [hj.symm]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hj_mem,
    Finset.sdiff_singleton_eq_erase,
    Finset.sum_eq_add_sum_diff_singleton_of_mem hbasic_mem,
    Finset.sdiff_singleton_eq_erase]
  have hrest :
      ∑ h ∈ (Finset.univ.erase j).erase (Fin.castLE hpn i),
          (gomory_tableau_split_normal hpn a i b h : ℝ) *
            gomory_tableau_row_ray hpn a i j h = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    have hh_basic : h ≠ Fin.castLE hpn i := (Finset.mem_erase.mp hh).1
    have hh_j : h ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hh).2).1
    simp [gomory_tableau_row_ray, hh_j, hh_basic]
  rw [hrest, add_zero]
  have hray_j : gomory_tableau_row_ray hpn a i j j = 1 := by
    simp [gomory_tableau_row_ray]
  have hnormal_basic :
      gomory_tableau_split_normal hpn a i b (Fin.castLE hpn i) = 1 := by
    simp [gomory_tableau_split_normal]
  have hray_basic :
      gomory_tableau_row_ray hpn a i j (Fin.castLE hpn i) = -a j := by
    simp [gomory_tableau_row_ray, hj.symm]
  rw [hray_j, hnormal_basic, hray_basic, mul_one, Int.cast_one, one_mul]
  by_cases hlt : j.1 < p
  · by_cases hle : Int.fract (a j) ≤ gomory_row_fraction b
    · have hnormal_j :
          gomory_tableau_split_normal hpn a i b j = Int.floor (a j) := by
        simp [gomory_tableau_split_normal, hj, hlt, hle]
      rw [hnormal_j, if_pos hlt, if_pos hle]
      linarith [Int.floor_add_fract (a j)]
    · have hfract_ne : Int.fract (a j) ≠ 0 := by
        intro hzero
        apply hle
        simpa [hzero, gomory_row_fraction] using Int.fract_nonneg b
      have hnotint : a j ∉ Set.range (Int.cast : ℤ → ℝ) :=
        (Int.fract_ne_zero_iff).1 hfract_ne
      have hceil : Int.ceil (a j) = Int.floor (a j) + 1 :=
        (Int.ceil_eq_floor_add_one_iff_notMem _).2 hnotint
      have hnormal_j :
          gomory_tableau_split_normal hpn a i b j = Int.ceil (a j) := by
        simp [gomory_tableau_split_normal, hj, hlt, hle]
      rw [hnormal_j, if_pos hlt, if_neg hle]
      rw [hceil, Int.cast_add, Int.cast_one]
      linarith [Int.floor_add_fract (a j)]
  · have hnormal_j : gomory_tableau_split_normal hpn a i b j = 0 := by
      simp [gomory_tableau_split_normal, hj, hlt]
    rw [hnormal_j, Int.cast_zero, zero_add, if_neg hlt]

/-- Helper for Example 6.10: along a tableau ray, the split normal has the affine value
`b + t * π r^j`, with the row vertex contributing exactly `b`. -/
lemma gomory_tableau_split_linear_form_add_smul
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (j : Fin n)
    (t : ℝ) :
    (∑ h : Fin n,
        (gomory_tableau_split_normal hpn a i b h : ℝ) *
          (gomory_tableau_row_vertex hpn i b h + t * gomory_tableau_row_ray hpn a i j h)) =
      b + t * gomory_tableau_split_direction_value hpn a i b j := by
  classical
  -- Split the affine expression into its vertex and ray contributions.
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hvertex :
      ∑ h : Fin n,
          (gomory_tableau_split_normal hpn a i b h : ℝ) *
            gomory_tableau_row_vertex hpn i b h = b := by
    rw [Finset.sum_eq_single (Fin.castLE hpn i)]
    · simp [gomory_tableau_split_normal, gomory_tableau_row_vertex]
    · intro h _ hh
      simp [gomory_tableau_row_vertex, hh]
    · simp
  have hray :
      ∑ h : Fin n,
          (gomory_tableau_split_normal hpn a i b h : ℝ) *
            (t * gomory_tableau_row_ray hpn a i j h) =
        t * gomory_tableau_split_direction_value hpn a i b j := by
    calc
      ∑ h : Fin n,
          (gomory_tableau_split_normal hpn a i b h : ℝ) *
            (t * gomory_tableau_row_ray hpn a i j h) =
          ∑ h : Fin n, t *
            ((gomory_tableau_split_normal hpn a i b h : ℝ) *
              gomory_tableau_row_ray hpn a i j h) := by
            apply Finset.sum_congr rfl
            intro h _
            ring
      _ = t * (∑ h : Fin n,
          (gomory_tableau_split_normal hpn a i b h : ℝ) *
            gomory_tableau_row_ray hpn a i j h) := by
        rw [Finset.mul_sum]
      _ = t * gomory_tableau_split_direction_value hpn a i b j := rfl
  -- Substitute the two computed contributions into the split sum.
  rw [hvertex, hray]

/-- Helper for Example 6.10: the nonnegative parameters for which `f + t * d` stays in
`[0, 1]` form the expected bounded interval, or all of `Set.Ici 0` when `d = 0`. -/
lemma nonnegativeAffineUnitIntervalParameters_eq_piecewise
    (f d : ℝ)
    (hf : f ∈ Set.Ioo (0 : ℝ) 1) :
    {t : ℝ | 0 ≤ t ∧ 0 ≤ f + t * d ∧ f + t * d ≤ 1} =
      if d < 0 then
        Set.Icc 0 (f / (-d))
      else if 0 < d then
        Set.Icc 0 ((1 - f) / d)
      else
        Set.Ici 0 := by
  ext t
  by_cases hneg : d < 0
  · -- A negative slope first meets the lower endpoint of the unit interval.
    rw [if_pos hneg, Set.mem_setOf_eq, Set.mem_Icc]
    have hdpos : 0 < -d := neg_pos.mpr hneg
    constructor
    · rintro ⟨ht0, hlower, _⟩
      have hmul : t * (-d) ≤ f := by
        linarith
      exact ⟨ht0, (le_div_iff₀ hdpos).2 hmul⟩
    · rintro ⟨ht0, htbound⟩
      have hmul : t * (-d) ≤ f := (le_div_iff₀ hdpos).1 htbound
      have htd_nonpos : t * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hneg.le
      exact ⟨ht0, by linarith, by linarith [hf.2]⟩
  · by_cases hpos : 0 < d
    · -- A positive slope first meets the upper endpoint of the unit interval.
      rw [if_neg hneg, if_pos hpos, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨ht0, _, hupper⟩
        have hmul : t * d ≤ 1 - f := by
          linarith
        exact ⟨ht0, (le_div_iff₀ hpos).2 hmul⟩
      · rintro ⟨ht0, htbound⟩
        have hmul : t * d ≤ 1 - f := (le_div_iff₀ hpos).1 htbound
        have htd_nonneg : 0 ≤ t * d := mul_nonneg ht0 hpos.le
        exact ⟨ht0, by linarith [hf.1], by linarith⟩
    · -- With zero slope, membership is independent of the nonnegative parameter.
      have hzero : d = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hzero, hf.1.le, hf.2.le]

/-- Helper for Example 6.10: the admissible parameters of a tableau ray are the interval
determined by its split-normal direction value. -/
lemma gomoryTableauRayAdmissibleParameters_eq_piecewise
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : gomory_row_fraction b ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin n) :
    ray_admissible_parameters
        (gomory_tableau_split_set hpn a i b)
        (gomory_tableau_row_vertex hpn i b)
        (gomory_tableau_row_ray hpn a i)
        j =
      if gomory_tableau_split_direction_value hpn a i b j < 0 then
        Set.Icc 0
          (gomory_row_fraction b /
            (-gomory_tableau_split_direction_value hpn a i b j))
      else if 0 < gomory_tableau_split_direction_value hpn a i b j then
        Set.Icc 0
          ((1 - gomory_row_fraction b) /
            gomory_tableau_split_direction_value hpn a i b j)
      else
        Set.Ici 0 := by
  -- First replace the interval description by its normalized affine form.
  rw [← nonnegativeAffineUnitIntervalParameters_eq_piecewise
    (gomory_row_fraction b)
    (gomory_tableau_split_direction_value hpn a i b j)
    hfrac]
  ext t
  rw [mem_ray_admissible_parameters_iff, Set.mem_setOf_eq,
    mem_gomory_tableau_split_set_iff]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [gomory_tableau_split_linear_form_add_smul]
  -- Subtracting `floor b` turns the split inequalities into the unit-interval inequalities.
  have hb : (Int.floor b : ℝ) + gomory_row_fraction b = b := by
    simpa [gomory_row_fraction] using Int.floor_add_fract b
  constructor
  · rintro ⟨ht0, hlower, hupper⟩
    exact ⟨ht0, by linarith, by linarith⟩
  · rintro ⟨ht0, hlower, hupper⟩
    exact ⟨ht0, by linarith, by linarith⟩

/-- Helper for Example 6.10: the ENNReal image of a nonnegative closed interval has supremum
equal to the image of its right endpoint. -/
lemma sSupOfRealImageIcc
    {c : ℝ}
    (hc : 0 ≤ c) :
    sSup (ENNReal.ofReal '' Set.Icc (0 : ℝ) c) = ENNReal.ofReal c := by
  -- The endpoint belongs to the image and bounds every other image point.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ENNReal.ofReal_le_ofReal ht.2
  · exact le_sSup ⟨c, ⟨hc, le_rfl⟩, rfl⟩

/-- Helper for Example 6.10: the ENNReal image of the nonnegative real ray has supremum `⊤`. -/
lemma sSupOfRealImageIci :
    sSup (ENNReal.ofReal '' Set.Ici (0 : ℝ)) = (⊤ : ENNReal) := by
  -- Every finite ENNReal value lies below the image of its real value plus one.
  rw [sSup_eq_top]
  intro c hc
  have hctop : c ≠ ⊤ := lt_top_iff_ne_top.mp hc
  have hreal_nonneg : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hreal_pos : 0 < c.toReal + 1 := by
    linarith
  refine ⟨ENNReal.ofReal (c.toReal + 1), ?_, ?_⟩
  · exact ⟨c.toReal + 1, add_nonneg hreal_nonneg zero_le_one, rfl⟩
  · have hc_eq : c = ENNReal.ofReal c.toReal := by
      symm
      exact ENNReal.ofReal_toReal hctop
    calc
      c = ENNReal.ofReal c.toReal := hc_eq
      _ < ENNReal.ofReal (c.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff hreal_pos).2 (by linarith)

/-- Helper for Example 6.10: the tableau ray-intersection parameter is the boundary distance
divided by the absolute split-normal slope, and is infinite for zero slope. -/
lemma gomoryTableauSplitRayParameter_eq_piecewise
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : gomory_row_fraction b ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin n) :
    ray_intersection_parameter
        (gomory_tableau_split_set hpn a i b)
        (gomory_tableau_row_vertex hpn i b)
        (gomory_tableau_row_ray hpn a i)
        j =
      if gomory_tableau_split_direction_value hpn a i b j < 0 then
        ENNReal.ofReal
          (gomory_row_fraction b /
            (-gomory_tableau_split_direction_value hpn a i b j))
      else if 0 < gomory_tableau_split_direction_value hpn a i b j then
        ENNReal.ofReal
          ((1 - gomory_row_fraction b) /
            gomory_tableau_split_direction_value hpn a i b j)
      else
        ⊤ := by
  -- Rewrite the supremum through the explicit admissible-parameter intervals.
  rw [ray_intersection_parameter_def,
    gomoryTableauRayAdmissibleParameters_eq_piecewise hpn a i b hfrac j]
  by_cases hneg : gomory_tableau_split_direction_value hpn a i b j < 0
  · simpa [hneg] using sSupOfRealImageIcc
      (div_nonneg hfrac.1.le (neg_nonneg.mpr hneg.le))
  · by_cases hpos : 0 < gomory_tableau_split_direction_value hpn a i b j
    · simpa [hneg, hpos] using sSupOfRealImageIcc
        (div_nonneg (sub_nonneg.mpr hfrac.2.le) hpos.le)
    · simpa [hneg, hpos] using sSupOfRealImageIci

/-- Helper for Example 6.10: taking the reciprocal of the piecewise ray parameter yields the
normalized split coefficient. -/
lemma inversePiecewiseRayParameter
    (f d : ℝ)
    (hf : f ∈ Set.Ioo (0 : ℝ) 1) :
    ((if d < 0 then
          ENNReal.ofReal (f / (-d))
        else if 0 < d then
          ENNReal.ofReal ((1 - f) / d)
        else
          ⊤ : ENNReal).toReal)⁻¹ =
      if d < 0 then
        (-d) / f
      else if 0 < d then
        d / (1 - f)
      else
        0 := by
  by_cases hneg : d < 0
  · -- The lower-boundary distance is positive, so `toReal` cancels `ofReal`.
    have hendpoint : 0 ≤ f / (-d) :=
      div_nonneg hf.1.le (neg_nonneg.mpr hneg.le)
    have hfne : f ≠ 0 := ne_of_gt hf.1
    have hdne : d ≠ 0 := ne_of_lt hneg
    simp only [if_pos hneg, ENNReal.toReal_ofReal hendpoint]
    field_simp
  · by_cases hpos : 0 < d
    · -- The upper-boundary distance is positive in the positive-slope branch.
      have hendpoint : 0 ≤ (1 - f) / d :=
        div_nonneg (sub_nonneg.mpr hf.2.le) hpos.le
      have hgapne : 1 - f ≠ 0 := ne_of_gt (sub_pos.mpr hf.2)
      have hdne : d ≠ 0 := ne_of_gt hpos
      simp only [if_neg hneg, if_pos hpos, ENNReal.toReal_ofReal hendpoint]
      field_simp
    · -- The infinite parameter in the zero-slope branch has reciprocal coefficient zero.
      simp [hneg, hpos]

/-- Example 6.10 (2). If the tableau right-hand side `b` is fractional, then the coefficient
`1 / alpha_j` of the split-intersection cut derived from the split set equals the corresponding
coefficient of Gomory's mixed integer cut. -/
theorem example_6_10_split_intersection_coefficient_eq_gomory_coefficient
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1)
    (ha_basic : a (Fin.castLE hpn i) = 0)
    (j : gomory_tableau_nonbasic_index hpn i) :
    gomory_tableau_split_intersection_coefficient hpn a i b j =
      gomory_mixed_integer_cut_coefficient p a b hfrac.1 j := by
  classical
  -- Convert the geometric ray supremum into its normalized slope coefficient.
  rw [gomory_tableau_split_intersection_coefficient,
    intersection_cut_coeff_eq_inv_ray_intersection_parameter,
    gomoryTableauSplitRayParameter_eq_piecewise hpn a i b hfrac j,
    inversePiecewiseRayParameter
      (gomory_row_fraction b)
      (gomory_tableau_split_direction_value hpn a i b j)
      hfrac]
  -- Expand both the split slope and the Chapter 5 mixed-integer coefficient by index type.
  rw [gomory_mixed_integer_cut_coefficient,
    gomory_mixed_integer_inequality_coefficient_eq,
    example_6_10_split_direction_value_eq_piecewise hpn a i b j j.property]
  simp only [gomory_row_fraction]
  by_cases hj_int : j.1.1 < p
  · have hj_mem : j.1 ∈ Finset.univ.filter (fun h : Fin n ↦ h.1 < p) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_int⟩
    simp only [if_pos hj_mem, if_pos hj_int]
    by_cases hle : Int.fract (a j) ≤ Int.fract b
    · simp only [if_pos hle]
      by_cases hzero : Int.fract (a j) = 0
      · simp [hzero]
      · have hfract_pos : 0 < Int.fract (a j) :=
          lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hzero)
        simp [hfract_pos]
    · have hdirection_pos : 0 < 1 - Int.fract (a j) :=
        sub_pos.mpr (Int.fract_lt_one _)
      have hnot_gt : ¬1 < Int.fract (a j) :=
        not_lt_of_ge (Int.fract_lt_one _).le
      simp [hle, hdirection_pos, hnot_gt]
  · have hj_notmem : j.1 ∉ Finset.univ.filter (fun h : Fin n ↦ h.1 < p) := by
      intro hj_mem
      exact hj_int (Finset.mem_filter.mp hj_mem).2
    simp only [if_neg hj_notmem, if_neg hj_int]
    by_cases ha_nonneg : 0 ≤ a j
    · by_cases ha_zero : a j = 0
      · simp [ha_zero]
      · have ha_pos : 0 < a j := lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
        simp [ha_nonneg, ha_pos]
    · have ha_neg : a j < 0 := lt_of_not_ge ha_nonneg
      have ha_not_pos : ¬0 < a j := not_lt_of_ge ha_neg.le
      simp [ha_nonneg, ha_neg, ha_not_pos]

/-- Example 6.10 (3). The intersection cut derived from the split set defined by (6.13) is
exactly the Gomory mixed integer cut generated by the same tableau row. -/
theorem example_6_10_split_intersection_cut_eq_gomory_mixed_integer_cut
    (hpn : p ≤ n)
    (a : Fin n → ℝ)
    (i : Fin p)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1)
    (ha_basic : a (Fin.castLE hpn i) = 0) :
    gomory_tableau_split_intersection_cut hpn a i b =
      gomory_mixed_integer_cut p a b hfrac.1 := by
  classical
  ext x
  rw [mem_gomory_tableau_split_intersection_cut_iff,
    mem_gomory_mixed_integer_cut_iff]
  -- On the nonbasic subtype, the geometric coefficients agree term by term with Gomory's.
  have hrestricted :
      (∑ j : gomory_tableau_nonbasic_index hpn i,
          gomory_tableau_split_intersection_coefficient hpn a i b j * x j) =
        ∑ j : gomory_tableau_nonbasic_index hpn i,
          gomory_mixed_integer_cut_coefficient p a b hfrac.1 j * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [example_6_10_split_intersection_coefficient_eq_gomory_coefficient
      hpn a i b hfrac ha_basic j]
  have hbasic_coeff :
      gomory_mixed_integer_cut_coefficient p a b hfrac.1 (Fin.castLE hpn i) = 0 := by
    rw [gomory_mixed_integer_cut_coefficient,
      gomory_mixed_integer_inequality_coefficient_eq]
    simp [ha_basic]
  -- The omitted basic summand is zero, so the restricted and full Gomory sums coincide.
  have hfull :
      (∑ j : Fin n, gomory_mixed_integer_cut_coefficient p a b hfrac.1 j * x j) =
        ∑ j : gomory_tableau_nonbasic_index hpn i,
          gomory_mixed_integer_cut_coefficient p a b hfrac.1 j * x j := by
    simpa [gomory_tableau_nonbasic_index, hbasic_coeff] using
      (Fintype.sum_eq_add_sum_subtype_ne
        (f := fun j : Fin n ↦
          gomory_mixed_integer_cut_coefficient p a b hfrac.1 j * x j)
        (Fin.castLE hpn i))
  rw [hrestricted, ← hfull]

/-- Helper for Example 6.10: `gomory_integer_function` can be expressed directly through the
fractional part of its second argument. -/
lemma gomoryIntegerFunction_eq_fract
    (f r : ℝ) :
    gomory_integer_function f r =
      min (Int.fract r / (1 - f)) ((1 - Int.fract r) / f) := by
  -- The two numerators are the lower and upper fractional gaps of `r`.
  have hlower : r - (Int.floor r : ℝ) = Int.fract r := by
    linarith [Int.floor_add_fract r]
  have hupper : (Int.floor r : ℝ) + 1 - r = 1 - Int.fract r := by
    linarith [Int.floor_add_fract r]
  rw [gomory_integer_function, hlower, hupper]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_example_6_10.lean

Example 6.10 (4). The Gomory mixed integer cut coefficients may equivalently be written with
the two functions `pi` and `psi` from (6.16), applied to `-a_j` on the integer and continuous
blocks respectively. -/
theorem example_6_10_gomory_coefficient_eq_function_form
    (a : Fin n → ℝ)
    (b : ℝ)
    (hfrac : 0 < gomory_row_fraction b ∧ gomory_row_fraction b < 1)
    (j : Fin n) :
    gomory_mixed_integer_cut_coefficient p a b hfrac.1 j =
      if j.1 < p then
        gomory_integer_function (gomory_row_fraction b) (-a j)
      else
        gomory_continuous_function (gomory_row_fraction b) (-a j) := by
  classical
  have hfpos : 0 < Int.fract b := by
    simpa [gomory_row_fraction] using hfrac.1
  have hflt : Int.fract b < 1 := by
    simpa [gomory_row_fraction] using hfrac.2
  rw [gomory_mixed_integer_cut_coefficient,
    gomory_mixed_integer_inequality_coefficient_eq]
  simp only [gomory_row_fraction]
  by_cases hj : j.1 < p
  · have hj_mem : j ∈ Finset.univ.filter (fun h : Fin n ↦ h.1 < p) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    simp only [if_pos hj_mem, if_pos hj]
    by_cases hfract : Int.fract (a j) = 0
    · -- Integral `a_j` gives zero on both sides.
      have hnegzero : Int.fract (-a j) = 0 := Int.fract_neg_eq_zero.mpr hfract
      rw [gomoryIntegerFunction_eq_fract, hnegzero]
      simp [hfract, hfpos.le]
    · have hneg : Int.fract (-a j) = 1 - Int.fract (a j) := Int.fract_neg hfract
      have hfunction :
          gomory_integer_function (Int.fract b) (-a j) =
            min
              ((1 - Int.fract (a j)) / (1 - Int.fract b))
              (Int.fract (a j) / Int.fract b) := by
        rw [gomoryIntegerFunction_eq_fract, hneg]
        congr 1
        ring
      rw [hfunction]
      by_cases hle : Int.fract (a j) ≤ Int.fract b
      · -- For `fract a_j ≤ fract b`, the lower-gap normalized ratio is the minimum.
        have hratio :
            Int.fract (a j) / Int.fract b ≤
              (1 - Int.fract (a j)) / (1 - Int.fract b) := by
          apply (div_le_div_iff₀ hfpos (sub_pos.mpr hflt)).2
          nlinarith
        rw [if_pos hle, min_eq_right hratio]
      · -- Above `fract b`, the complementary normalized ratio is the minimum.
        have hratio :
            (1 - Int.fract (a j)) / (1 - Int.fract b) ≤
              Int.fract (a j) / Int.fract b := by
          apply (div_le_div_iff₀ (sub_pos.mpr hflt) hfpos).2
          nlinarith [lt_of_not_ge hle]
        rw [if_neg hle, min_eq_left hratio]
  · have hj_notmem : j ∉ Finset.univ.filter (fun h : Fin n ↦ h.1 < p) := by
      intro hj_mem
      exact hj (Finset.mem_filter.mp hj_mem).2
    simp only [if_neg hj_notmem, if_neg hj]
    have hfunction :
        gomory_continuous_function (Int.fract b) (-a j) =
          max ((-a j) / (1 - Int.fract b)) (a j / Int.fract b) := by
      rw [gomory_continuous_function]
      congr 1
      ring
    rw [hfunction]
    by_cases ha_nonneg : 0 ≤ a j
    · -- For a nonnegative tableau coefficient, the `a_j / f` branch is maximal.
      have hratio :
          (-a j) / (1 - Int.fract b) ≤ a j / Int.fract b :=
        le_trans
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg)
            (sub_pos.mpr hflt).le)
          (div_nonneg ha_nonneg hfpos.le)
      rw [if_pos ha_nonneg, max_eq_right hratio]
    · -- For a negative tableau coefficient, the complementary branch is maximal.
      have ha_neg : a j < 0 := lt_of_not_ge ha_nonneg
      have hratio :
          a j / Int.fract b ≤ (-a j) / (1 - Int.fract b) :=
        le_trans
          (div_nonpos_of_nonpos_of_nonneg ha_neg.le hfpos.le)
          (div_nonneg (neg_nonneg.mpr ha_neg.le) (sub_pos.mpr hflt).le)
      rw [if_neg ha_nonneg, max_eq_left hratio]

end Example610
