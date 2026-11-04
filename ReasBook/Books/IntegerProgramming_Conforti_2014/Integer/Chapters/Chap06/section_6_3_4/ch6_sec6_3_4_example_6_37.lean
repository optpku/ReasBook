/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_3.ch6_sec6_3_3_theorem_6_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: this file keeps the source-facing one-dimensional formulas on `ℝ` and
-- uses the Section 6.3.1 and Section 6.3.4 one-dimensional `...OnR` owners directly rather than
-- exposing the underlying `q = 1` bridge inline.

noncomputable section

section Example637

/-- The translated interval `B - f = [-f, 1 - f]` from Example 6.37, viewed on `ℝ`. -/
def example_6_37_shifted_interval (f : ℚ) : Set ℝ :=
  Set.Icc (-(f : ℝ)) (1 - (f : ℝ))

/-- `example_6_37_shifted_interval f` is the translate of `B = [0,1]` by `-f`, written as the
displayed interval condition on `ℝ`. -/
theorem example_6_37_shifted_interval_eq
    (f : ℚ) :
    example_6_37_shifted_interval f =
      {r : ℝ | 0 ≤ r + (f : ℝ) ∧ r + (f : ℝ) ≤ 1} := by
  ext r
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · linarith
    · linarith
  · rintro ⟨hleft, hright⟩
    constructor
    · linarith
    · linarith

/-- The gauge formula `ψ(r) = max {r / (1 - f), -r / f}` from Example 6.37, written on `ℝ`. -/
def example_6_37_psi (f : ℚ) : ℝ → ℝ :=
  fun r ↦ max (r / (1 - (f : ℝ))) (-r / (f : ℝ))

/-- Expanding `example_6_37_psi f` recovers the displayed maximum formula from Example 6.37. -/
@[simp] theorem example_6_37_psi_apply
    (f : ℚ)
    (r : ℝ) :
    example_6_37_psi f r = max (r / (1 - (f : ℝ))) (-r / (f : ℝ)) :=
  rfl

/-- The trivial lifting `π̄` from Example 6.37, written as the displayed piecewise formula on the
fractional part of a real argument. -/
def example_6_37_bar_pi (f : ℚ) : ℝ → ℝ :=
  fun r ↦
    let u : ℝ := r - (Int.floor r : ℝ)
    if u ≤ 1 - (f : ℝ) then
      u / (1 - (f : ℝ))
    else
      ((Int.ceil r : ℝ) - r) / (f : ℝ)

/-- Expanding `example_6_37_bar_pi f` recovers the displayed floor/ceiling formula for the
trivial lifting `π̄` in Example 6.37. -/
@[simp] theorem example_6_37_bar_pi_apply
    (f : ℚ)
    (r : ℝ) :
    example_6_37_bar_pi f r =
      let u : ℝ := r - (Int.floor r : ℝ)
      if u ≤ 1 - (f : ℝ) then
        u / (1 - (f : ℝ))
      else
        ((Int.ceil r : ℝ) - r) / (f : ℝ) :=
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the displayed
maximum defining `example_6_37_psi` is sublinear. -/
lemma example_6_37_psi_sublinear
    {f : ℚ} :
    (example_6_37_psi f).Sublinear := by
  have hleft : (fun r : ℝ ↦ r / (1 - (f : ℝ))).Subadditive := by
    intro r s
    dsimp
    ring_nf
    exact le_rfl
  have hright : (fun r : ℝ ↦ -r / (f : ℝ)).Subadditive := by
    intro r s
    dsimp
    ring_nf
    exact le_rfl
  refine ⟨hleft.max hright, ?_⟩
  intro r c hc
  -- Positive scalar multiplication distributes through both slopes and their maximum.
  rw [example_6_37_psi_apply, example_6_37_psi_apply]
  simp only [smul_eq_mul]
  have hleft_scale : c * r / (1 - (f : ℝ)) = c * (r / (1 - (f : ℝ))) := by
    ring
  have hright_scale : -(c * r) / (f : ℝ) = c * (-r / (f : ℝ)) := by
    ring
  rw [hleft_scale, hright_scale, ← mul_max_of_nonneg _ _ hc.le]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the displayed
gauge formula is pointwise nonnegative. -/
lemma example_6_37_psi_nonneg
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    (r : ℝ) :
    0 ≤ example_6_37_psi f r := by
  have hf0_real : 0 < (f : ℝ) := by exact_mod_cast hf0
  have hgap : 0 < 1 - (f : ℝ) := by
    have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
    linarith
  rw [example_6_37_psi_apply]
  by_cases hr : 0 ≤ r
  · exact le_max_of_le_left (div_nonneg hr hgap.le)
  · exact le_max_of_le_right (div_nonneg (neg_nonneg.2 (le_of_not_ge hr)) hf0_real.le)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: a nonnegative
sublinear scalar function is the gauge of its unit sublevel set. -/
lemma scalarSublinearGaugeUnitSublevelSet_eq
    {g : ℝ → ℝ}
    (hg : g.Sublinear)
    (hg_nonneg : ∀ r, 0 ≤ g r)
    (r : ℝ) :
    gauge {x : ℝ | g x ≤ 1} r = g r := by
  let K : Set ℝ := {x : ℝ | g x ≤ 1}
  have hK_zero : (0 : ℝ) ∈ interior K := by
    have hcont0 : ContinuousAt g 0 := hg.continuous.continuousAt
    have hg_zero_lt_one : g 0 < 1 := by
      simp [hg.map_zero]
    have hlt : g ⁻¹' Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := by
      exact hcont0.preimage_mem_nhds (isOpen_Iio.mem_nhds hg_zero_lt_one)
    have hsubset : g ⁻¹' Set.Iio (1 : ℝ) ⊆ K := by
      intro x hx
      change g x < 1 at hx
      change g x ≤ 1
      exact hx.le
    exact mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hlt hsubset)
  have hK_absorbent : Absorbent ℝ K :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hK_zero)
  have hK_nonempty :
      {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ t⁻¹ • r ∈ K}.Nonempty := by
    rcases hK_absorbent.gauge_set_nonempty (x := r) with ⟨t, ht_pos, ht_mem⟩
    exact ⟨t, ht_pos,
      (Set.mem_smul_set_iff_inv_smul_mem₀ ht_pos.ne' K r).mp ht_mem⟩
  have hK_lower : g r ≤ gauge K r := by
    rw [gauge_def']
    refine le_csInf hK_nonempty ?_
    intro t ht
    have ht_mem : g (t⁻¹ • r) ≤ 1 := ht.2
    calc
      g r = g (t • (t⁻¹ • r)) := by rw [smul_inv_smul₀ ht.1.ne']
      _ = t * g (t⁻¹ • r) := hg.positivelyHomogeneous _ t ht.1
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left ht_mem ht.1.le
      _ = t := by ring
  have hK_upper : gauge K r ≤ g r := by
    by_cases hgr_zero : g r = 0
    · have hgauge_le_zero : gauge K r ≤ 0 := by
        refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
        have hhalf_pos : 0 < ε / 2 := half_pos hε
        have hhalf : gauge K r ≤ ε / 2 := by
          refine gauge_le_of_mem hhalf_pos.le ?_
          rw [Set.mem_smul_set_iff_inv_smul_mem₀ hhalf_pos.ne']
          change g (((ε / 2 : ℝ)⁻¹) • r) ≤ 1
          rw [hg.positivelyHomogeneous _ _ (inv_pos.2 hhalf_pos), hgr_zero, mul_zero]
          norm_num
        linarith
      simpa [hgr_zero] using hgauge_le_zero
    · have hgr_pos : 0 < g r := lt_of_le_of_ne (hg_nonneg r) (Ne.symm hgr_zero)
      have hr_inv_mem : (g r)⁻¹ • r ∈ K := by
        change g ((g r)⁻¹ • r) ≤ 1
        rw [hg.positivelyHomogeneous _ _ (inv_pos.2 hgr_pos), inv_mul_cancel₀ hgr_pos.ne']
      exact gauge_le_of_mem (s := K) (hg_nonneg r)
        ((Set.mem_smul_set_iff_inv_smul_mem₀ hgr_pos.ne' K r).mpr hr_inv_mem)
  exact le_antisymm hK_upper hK_lower

/-- Example 6.37 (1). For `q = 1`, `0 < f < 1`, and `B = [0,1]`, if `ψ` is the gauge of `B - f`,
then the explicit function `example_6_37_psi f` agrees with that gauge. -/
theorem example_6_37_psi_eq_gauge
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_37_psi f = gauge (example_6_37_shifted_interval f) := by
  have hf0_real : 0 < (f : ℝ) := by exact_mod_cast hf0
  have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
  have hgap : 0 < 1 - (f : ℝ) := by linarith
  have hsublevel :
      {r : ℝ | example_6_37_psi f r ≤ 1} = example_6_37_shifted_interval f := by
    ext r
    rw [Set.mem_setOf_eq]
    change max (r / (1 - (f : ℝ))) (-r / (f : ℝ)) ≤ 1 ↔
      r ∈ Set.Icc (-(f : ℝ)) (1 - (f : ℝ))
    rw [max_le_iff]
    constructor
    · rintro ⟨hright, hleft⟩
      rw [div_le_iff₀ hgap] at hright
      rw [div_le_iff₀ hf0_real] at hleft
      constructor
      · linarith
      · linarith
    · rintro ⟨hleft, hright⟩
      constructor
      · rw [div_le_iff₀ hgap]
        linarith
      · rw [div_le_iff₀ hf0_real]
        linarith
  funext r
  -- Identify the interval with the unit sublevel set, then invoke the scalar gauge interface.
  rw [← hsublevel]
  exact (scalarSublinearGaugeUnitSublevelSet_eq
    example_6_37_psi_sublinear
    (example_6_37_psi_nonneg hf0 hf1) r).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the
floor/ceiling formula for `example_6_37_bar_pi` has the canonical fractional-part form. -/
lemma example_6_37_bar_pi_eq_fract
    {f : ℚ}
    (hf1 : f < 1)
    (r : ℝ) :
    example_6_37_bar_pi f r =
      if Int.fract r ≤ 1 - (f : ℝ) then
        Int.fract r / (1 - (f : ℝ))
      else
        (1 - Int.fract r) / (f : ℝ) := by
  rw [example_6_37_bar_pi_apply]
  change (if Int.fract r ≤ 1 - (f : ℝ) then
      Int.fract r / (1 - (f : ℝ))
    else ((Int.ceil r : ℝ) - r) / (f : ℝ)) = _
  by_cases hu : Int.fract r ≤ 1 - (f : ℝ)
  · rw [if_pos hu, if_pos hu]
  · have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
    have hzero_le_gap : 0 ≤ 1 - (f : ℝ) := by linarith
    have hu_ne : Int.fract r ≠ 0 := by
      intro hu_zero
      rw [hu_zero] at hu
      exact hu hzero_le_gap
    -- In the right branch, the ceiling gap is the complement of the fractional part.
    rw [if_neg hu, if_neg hu, Int.ceil_sub_self_eq hu_ne]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the value
`example_6_37_bar_pi f r` is the attained least value of `example_6_37_psi f` on the
integer-translation orbit of `r`. -/
lemma example_6_37_bar_pi_isLeast_integerTranslate
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    (r : ℝ) :
    IsLeast
      (Set.range (fun z : ℤ ↦ example_6_37_psi f (r + (z : ℝ))))
      (example_6_37_bar_pi f r) := by
  have hf0_real : 0 < (f : ℝ) := by exact_mod_cast hf0
  have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
  have hgap : 0 < 1 - (f : ℝ) := by linarith
  have hu0 : 0 ≤ Int.fract r := Int.fract_nonneg r
  have hu1 : Int.fract r < 1 := Int.fract_lt_one r
  constructor
  · by_cases hu : Int.fract r ≤ 1 - (f : ℝ)
    · refine ⟨-Int.floor r, ?_⟩
      change example_6_37_psi f (r + ((-Int.floor r : ℤ) : ℝ)) =
        example_6_37_bar_pi f r
      have htranslate : r + ((-Int.floor r : ℤ) : ℝ) = Int.fract r := by
        rw [Int.cast_neg]
        rfl
      rw [htranslate, example_6_37_psi_apply,
        example_6_37_bar_pi_eq_fract hf1, if_pos hu]
      apply max_eq_left
      exact (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu0) hf0_real.le).trans
        (div_nonneg hu0 hgap.le)
    · refine ⟨-Int.floor r - 1, ?_⟩
      change example_6_37_psi f (r + ((-Int.floor r - 1 : ℤ) : ℝ)) =
        example_6_37_bar_pi f r
      have htranslate :
          r + ((-Int.floor r - 1 : ℤ) : ℝ) = Int.fract r - 1 := by
        rw [Int.cast_sub, Int.cast_neg, Int.cast_one]
        unfold Int.fract
        ring
      rw [htranslate, example_6_37_psi_apply,
        example_6_37_bar_pi_eq_fract hf1, if_neg hu]
      have hleft_nonpos : (Int.fract r - 1) / (1 - (f : ℝ)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu1.le) hgap.le
      have hright_nonneg : 0 ≤ -(Int.fract r - 1) / (f : ℝ) :=
        div_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hu1.le)) hf0_real.le
      rw [max_eq_right (hleft_nonpos.trans hright_nonneg)]
      ring
  · intro t ht
    rcases ht with ⟨z, rfl⟩
    change example_6_37_bar_pi f r ≤ example_6_37_psi f (r + (z : ℝ))
    have hyfract : Int.fract (r + (z : ℝ)) = Int.fract r :=
      Int.fract_add_intCast r z
    have hydecomp :
        r + (z : ℝ) = Int.fract r + (Int.floor (r + (z : ℝ)) : ℝ) := by
      nth_rewrite 1 [← Int.fract_add_floor (r + (z : ℝ))]
      rw [hyfract]
    rw [example_6_37_bar_pi_eq_fract hf1, example_6_37_psi_apply]
    by_cases hu : Int.fract r ≤ 1 - (f : ℝ)
    · rw [if_pos hu]
      by_cases hy : 0 ≤ r + (z : ℝ)
      · have hfloor_nonneg : 0 ≤ Int.floor (r + (z : ℝ)) :=
          Int.floor_nonneg.mpr hy
        have hfloor_nonneg_real :
            0 ≤ (Int.floor (r + (z : ℝ)) : ℝ) := by
          exact_mod_cast hfloor_nonneg
        have hu_le_y : Int.fract r ≤ r + (z : ℝ) := by linarith
        calc
          Int.fract r / (1 - (f : ℝ)) ≤
              (r + (z : ℝ)) / (1 - (f : ℝ)) :=
            (div_le_div_iff_of_pos_right hgap).2 hu_le_y
          _ ≤ max ((r + (z : ℝ)) / (1 - (f : ℝ)))
              (-(r + (z : ℝ)) / (f : ℝ)) := le_max_left _ _
      · have hy_neg : r + (z : ℝ) < 0 := lt_of_not_ge hy
        have hfloor_le : Int.floor (r + (z : ℝ)) ≤ -1 :=
          Int.floor_le_neg_one_iff.mpr hy_neg
        have hfloor_le_real :
            (Int.floor (r + (z : ℝ)) : ℝ) ≤ -1 := by
          exact_mod_cast hfloor_le
        have hcomp_le : 1 - Int.fract r ≤ -(r + (z : ℝ)) := by linarith
        have hbranch_le :
            Int.fract r / (1 - (f : ℝ)) ≤ (1 - Int.fract r) / (f : ℝ) := by
          rw [div_le_div_iff₀ hgap hf0_real]
          nlinarith
        calc
          Int.fract r / (1 - (f : ℝ)) ≤
              (1 - Int.fract r) / (f : ℝ) := hbranch_le
          _ ≤ -(r + (z : ℝ)) / (f : ℝ) := by
            rw [div_le_div_iff_of_pos_right hf0_real]
            exact hcomp_le
          _ ≤ max ((r + (z : ℝ)) / (1 - (f : ℝ)))
              (-(r + (z : ℝ)) / (f : ℝ)) := le_max_right _ _
    · rw [if_neg hu]
      by_cases hy : 0 ≤ r + (z : ℝ)
      · have hfloor_nonneg : 0 ≤ Int.floor (r + (z : ℝ)) :=
          Int.floor_nonneg.mpr hy
        have hfloor_nonneg_real :
            0 ≤ (Int.floor (r + (z : ℝ)) : ℝ) := by
          exact_mod_cast hfloor_nonneg
        have hu_le_y : Int.fract r ≤ r + (z : ℝ) := by linarith
        have hbranch_le :
            (1 - Int.fract r) / (f : ℝ) ≤
              Int.fract r / (1 - (f : ℝ)) := by
          rw [div_le_div_iff₀ hf0_real hgap]
          nlinarith [lt_of_not_ge hu]
        calc
          (1 - Int.fract r) / (f : ℝ) ≤
              Int.fract r / (1 - (f : ℝ)) := hbranch_le
          _ ≤ (r + (z : ℝ)) / (1 - (f : ℝ)) :=
            (div_le_div_iff_of_pos_right hgap).2 hu_le_y
          _ ≤ max ((r + (z : ℝ)) / (1 - (f : ℝ)))
              (-(r + (z : ℝ)) / (f : ℝ)) := le_max_left _ _
      · have hy_neg : r + (z : ℝ) < 0 := lt_of_not_ge hy
        have hfloor_le : Int.floor (r + (z : ℝ)) ≤ -1 :=
          Int.floor_le_neg_one_iff.mpr hy_neg
        have hfloor_le_real :
            (Int.floor (r + (z : ℝ)) : ℝ) ≤ -1 := by
          exact_mod_cast hfloor_le
        have hcomp_le : 1 - Int.fract r ≤ -(r + (z : ℝ)) := by linarith
        calc
          (1 - Int.fract r) / (f : ℝ) ≤ -(r + (z : ℝ)) / (f : ℝ) := by
            rw [div_le_div_iff_of_pos_right hf0_real]
            exact hcomp_le
          _ ≤ max ((r + (z : ℝ)) / (1 - (f : ℝ)))
              (-(r + (z : ℝ)) / (f : ℝ)) := le_max_right _ _

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the trivial lifting is
pointwise bounded above by the gauge formula. -/
lemma example_6_37_bar_pi_le_psi
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    (r : ℝ) :
    example_6_37_bar_pi f r ≤ example_6_37_psi f r := by
  -- Specialize the least-value property to the zero integer translate.
  apply (example_6_37_bar_pi_isLeast_integerTranslate hf0 hf1 r).2
  refine ⟨0, ?_⟩
  norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the attained
integer translates and sublinearity of `example_6_37_psi` make `example_6_37_bar_pi`
subadditive. -/
lemma example_6_37_bar_pi_subadditive
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    (example_6_37_bar_pi f).Subadditive := by
  intro r s
  rcases (example_6_37_bar_pi_isLeast_integerTranslate hf0 hf1 r).1 with ⟨zr, hzr⟩
  rcases (example_6_37_bar_pi_isLeast_integerTranslate hf0 hf1 s).1 with ⟨zs, hzs⟩
  change example_6_37_psi f (r + (zr : ℝ)) = example_6_37_bar_pi f r at hzr
  change example_6_37_psi f (s + (zs : ℝ)) = example_6_37_bar_pi f s at hzs
  have hsum_mem :
      example_6_37_psi f ((r + s) + ((zr + zs : ℤ) : ℝ)) ∈
        Set.range (fun z : ℤ ↦ example_6_37_psi f ((r + s) + (z : ℝ))) :=
    ⟨zr + zs, rfl⟩
  have hleast :=
    (example_6_37_bar_pi_isLeast_integerTranslate hf0 hf1 (r + s)).2 hsum_mem
  have harg :
      (r + s) + ((zr + zs : ℤ) : ℝ) = (r + (zr : ℝ)) + (s + (zs : ℝ)) := by
    push_cast
    ring
  calc
    example_6_37_bar_pi f (r + s) ≤
        example_6_37_psi f ((r + s) + ((zr + zs : ℤ) : ℝ)) := hleast
    _ = example_6_37_psi f ((r + (zr : ℝ)) + (s + (zs : ℝ))) := congrArg _ harg
    _ ≤ example_6_37_psi f (r + (zr : ℝ)) +
        example_6_37_psi f (s + (zs : ℝ)) :=
      example_6_37_psi_sublinear.1 _ _
    _ = example_6_37_bar_pi f r + example_6_37_bar_pi f s := by rw [hzr, hzs]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the fractional-part
formula makes `example_6_37_bar_pi` invariant under integer translation. -/
lemma example_6_37_bar_pi_add_intCast
    {f : ℚ}
    (hf1 : f < 1)
    (r : ℝ)
    (z : ℤ) :
    example_6_37_bar_pi f (r + (z : ℝ)) = example_6_37_bar_pi f r := by
  -- Both sides reduce to the same branch because integer translation preserves fractional part.
  rw [example_6_37_bar_pi_eq_fract hf1, example_6_37_bar_pi_eq_fract hf1,
    Int.fract_add_intCast]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean`: the two branches of
`example_6_37_bar_pi` add to one at symmetry mates. -/
lemma example_6_37_bar_pi_symmetry
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    (r : ℝ) :
    example_6_37_bar_pi f r + example_6_37_bar_pi f (-(f : ℝ) - r) = 1 := by
  have hf0_real : 0 < (f : ℝ) := by exact_mod_cast hf0
  have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
  have hgap : 0 < 1 - (f : ℝ) := by linarith
  have hu0 : 0 ≤ Int.fract r := Int.fract_nonneg r
  have hu1 : Int.fract r < 1 := Int.fract_lt_one r
  rw [example_6_37_bar_pi_eq_fract hf1, example_6_37_bar_pi_eq_fract hf1]
  by_cases hu : Int.fract r ≤ 1 - (f : ℝ)
  · have hmate_nonneg : 0 ≤ 1 - (f : ℝ) - Int.fract r := by linarith
    have hmate_lt_one : 1 - (f : ℝ) - Int.fract r < 1 := by linarith
    have hfract_mate :
        Int.fract (-(f : ℝ) - r) = 1 - (f : ℝ) - Int.fract r := by
      rw [Int.fract_eq_iff]
      refine ⟨hmate_nonneg, hmate_lt_one, -Int.floor r - 1, ?_⟩
      rw [Int.cast_sub, Int.cast_neg, Int.cast_one]
      linarith [Int.fract_add_floor r]
    have hmate_left : 1 - (f : ℝ) - Int.fract r ≤ 1 - (f : ℝ) := by
      linarith
    rw [if_pos hu, hfract_mate, if_pos hmate_left]
    field_simp [hgap.ne']
    ring
  · have hu_strict : 1 - (f : ℝ) < Int.fract r := lt_of_not_ge hu
    have hmate_nonneg : 0 ≤ 2 - (f : ℝ) - Int.fract r := by linarith
    have hmate_lt_one : 2 - (f : ℝ) - Int.fract r < 1 := by linarith
    have hfract_mate :
        Int.fract (-(f : ℝ) - r) = 2 - (f : ℝ) - Int.fract r := by
      rw [Int.fract_eq_iff]
      refine ⟨hmate_nonneg, hmate_lt_one, -Int.floor r - 2, ?_⟩
      rw [Int.cast_sub, Int.cast_neg, Int.cast_ofNat]
      linarith [Int.fract_add_floor r]
    have hmate_not_left : ¬2 - (f : ℝ) - Int.fract r ≤ 1 - (f : ℝ) := by
      linarith
    rw [if_neg hu, hfract_mate, if_neg hmate_not_left]
    field_simp [hf0_real.ne']
    ring

/-- Example 6.37 (2). For the same one-dimensional set, the trivial lifting `π̄` is the
displayed piecewise floor/ceiling formula, viewed through the canonical one-dimensional lifting
owner on `ℝ`. -/
theorem example_6_37_bar_pi_eq_trivial_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_37_bar_pi f = trivial_lifting_on_R (example_6_37_psi f) := by
  funext r
  rw [trivial_lifting_on_R_apply, trivial_lifting_apply]
  have hrange :
      Set.range (fun w : Fin 1 → ℤ ↦
        (fun s : Fin 1 → ℝ ↦ example_6_37_psi f (s 0))
          (fun i ↦ (fun _ : Fin 1 ↦ r) i + (w i : ℝ))) =
        Set.range (fun z : ℤ ↦ example_6_37_psi f (r + (z : ℝ))) := by
    ext a
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w 0, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨fun _ ↦ z, rfl⟩
  -- The vector translate range is the scalar orbit whose least element was computed above.
  rw [hrange]
  exact (example_6_37_bar_pi_isLeast_integerTranslate hf0 hf1 r).csInf_eq.symm

/-- Example 6.37 (3). The one-dimensional trivial lifting `π̄` is a minimal valid function for
the pure-integer infinite relaxation `G_f`, stated in the repository's canonical `q = 1` owner
on `ℝ`. -/
theorem example_6_37_bar_pi_is_minimal_valid_pure_integer_function
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    pure_integer_minimal_valid_function_on_R (f : ℝ) (example_6_37_bar_pi f) := by
  have hf0_real : 0 < (f : ℝ) := by exact_mod_cast hf0
  have hf1_real : (f : ℝ) < 1 := by exact_mod_cast hf1
  have hgap : 0 < 1 - (f : ℝ) := by linarith
  change pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ (f : ℝ))
    (fun r : Fin 1 → ℝ ↦ example_6_37_bar_pi f (r 0))
  refine pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry
    ?_ ?_ ?_ ?_ ?_
  · intro r
    rw [example_6_37_bar_pi_eq_fract hf1]
    by_cases hu : Int.fract (r 0) ≤ 1 - (f : ℝ)
    · rw [if_pos hu]
      exact div_nonneg (Int.fract_nonneg _) hgap.le
    · rw [if_neg hu]
      exact div_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le) hf0_real.le
  · -- The origin is in the first branch and has value zero.
    rw [example_6_37_bar_pi_eq_fract hf1]
    simp [hgap.le]
  · intro r s
    simpa using example_6_37_bar_pi_subadditive hf0 hf1 (r 0) (s 0)
  · intro r w
    simp
  · intro r
    simpa using example_6_37_bar_pi_symmetry hf0 hf1 (r 0)

/-- Under the source hypotheses of Example 6.37, `example_6_37_bar_pi f` is available through the
canonical one-dimensional pure-integer minimal-valid-function instance. -/
instance instExample637BarPiMinimalValidPureIntegerFunction
    {f : ℚ} [Fact (0 < f)] [Fact (f < 1)] :
    pure_integer_minimal_valid_function_on_R (f : ℝ) (example_6_37_bar_pi f) :=
  example_6_37_bar_pi_is_minimal_valid_pure_integer_function
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- Example 6.37 (4). The same function `π̄` is a minimal lifting of `ψ`, viewed through the
canonical one-dimensional lifting owner on `ℝ`. -/
theorem example_6_37_bar_pi_is_minimal_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    IsMinimalLiftingOfOnR (f : ℝ) (example_6_37_bar_pi f) (example_6_37_psi f) := by
  have hbar_min := example_6_37_bar_pi_is_minimal_valid_pure_integer_function hf0 hf1
  have hbar_valid :
      pure_integer_valid_function (fun _ : Fin 1 ↦ (f : ℝ))
        (fun r : Fin 1 → ℝ ↦ example_6_37_bar_pi f (r 0)) :=
    { nonneg := hbar_min.nonneg
      one_le_sum := hbar_min.one_le_sum }
  have hpsi_sublinear :
      (fun r : Fin 1 → ℝ ↦ example_6_37_psi f (r 0)).Sublinear := by
    refine ⟨?_, ?_⟩
    · intro r s
      simpa using example_6_37_psi_sublinear.1 (r 0) (s 0)
    · intro r c hc
      simpa using example_6_37_psi_sublinear.2 (r 0) c hc
  have hvalid :
      IsValidGomoryJohnsonPair (fun _ : Fin 1 ↦ (f : ℝ))
        (fun r : Fin 1 → ℝ ↦ example_6_37_bar_pi f (r 0))
        (fun r : Fin 1 → ℝ ↦ example_6_37_psi f (r 0)) :=
    mixedIntegerValidPair_of_pureIntegerValid_sublinear_le
      hbar_valid hpsi_sublinear (fun r ↦ example_6_37_bar_pi_le_psi hf0 hf1 (r 0))
  refine
    { toIsValidGomoryJohnsonPair := hvalid
      eq_of_le := ?_ }
  intro π' hπ' hle
  -- Pure minimality identifies any valid competitor lying below `bar_pi`.
  exact hbar_min.eq_of_le hπ'.toPureIntegerValidFunction hle

/-- Under the source hypotheses of Example 6.37, `example_6_37_bar_pi f` is available through the
canonical minimal-lifting instance on `ℝ`. -/
instance instExample637BarPiMinimalLifting
    {f : ℚ} [Fact (0 < f)] [Fact (f < 1)] :
    IsMinimalLiftingOfOnR (f : ℝ) (example_6_37_bar_pi f) (example_6_37_psi f) :=
  example_6_37_bar_pi_is_minimal_lifting
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_37.lean

Example 6.37 (5). In this one-dimensional case, `π̄` is the unique minimal lifting of `ψ`;
equivalently, every minimal lifting of `ψ` on `ℝ` is equal to `π̄`. -/
theorem example_6_37_eq_bar_pi_of_minimal_lifting
    {f : ℚ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {π : ℝ → ℝ}
    (hπ : IsMinimalLiftingOfOnR (f : ℝ) π (example_6_37_psi f)) :
    π = example_6_37_bar_pi f := by
  have hvector_le :=
    minimal_lifting_le_trivial_lifting
      (fun _ : Fin 1 ↦ (f : ℝ))
      (fun r : Fin 1 → ℝ ↦ example_6_37_psi f (r 0))
      (fun r : Fin 1 → ℝ ↦ π (r 0)) hπ
  have hle : ∀ r : ℝ, π r ≤ example_6_37_bar_pi f r := by
    intro r
    have hr := hvector_le (fun _ : Fin 1 ↦ r)
    rw [← trivial_lifting_on_R_apply] at hr
    -- Route correction: transport the normalized bound to `bar_pi` in the forward equality
    -- direction, rather than rewriting the goal backward.
    calc
      π r ≤ trivial_lifting_on_R (example_6_37_psi f) r := hr
      _ = example_6_37_bar_pi f r := by
        exact congrFun (example_6_37_bar_pi_eq_trivial_lifting hf0 hf1).symm r
  -- Minimality of `bar_pi` turns the universal trivial-lifting upper bound into equality.
  exact isMinimalLiftingOfOnR_eq_of_le
    (example_6_37_bar_pi_is_minimal_lifting hf0 hf1)
    hπ.toIsValidGomoryJohnsonPair hle

end Example637

#print axioms example_6_37_eq_bar_pi_of_minimal_lifting
