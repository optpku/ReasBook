/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54

noncomputable section

open MeasureTheory

/-- Helper for Lemma 3.2.6: a centered interval on the real line keeps at most half of its volume
on the nonpositive side, hence certainly at most `1 - exp (-1)`. -/
theorem centeredInterval_leftHalf_ratio_le_one_sub_exp_neg_one
    {a b : ℝ} (hab : a ≤ b) (hcenter : (⨍ x in Set.Icc a b, x) = 0) :
    (volume (Set.Icc a b ∩ Set.Iic 0)).toReal / (volume (Set.Icc a b)).toReal ≤
      1 - Real.exp (-1) := by
  by_cases hdeg : a = b
  · -- A degenerate interval has zero numerator and denominator, so the ratio is `0`.
    subst hdeg
    simp
  have hvol : (volume (Set.Icc a b)).toReal = b - a := by
    -- Convert the interval volume to its length.
    simp [Real.volume_Icc, hab]
  have hInt :
      ∫ x in Set.Icc a b, x ∂volume = ∫ x in a..b, x := by
    -- Replace the set integral on `Icc` by the usual interval integral.
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
  have hvolReal : volume.real (Set.Icc a b) = b - a := by
    -- The real-valued measure normalization agrees with the interval length.
    simpa [measureReal_def] using hvol
  have havg : (b - a)⁻¹ * (∫ x in a..b, x) = 0 := by
    -- Expand the set average into the normalized interval integral.
    have hcenter' := hcenter
    rw [MeasureTheory.setAverage_eq, hvolReal, hInt] at hcenter'
    simpa [smul_eq_mul] using hcenter'
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hdeg)
  have hIntZero : ∫ x in a..b, x = 0 := by
    -- Clear the nonzero interval length from the normalized average.
    have hmul := congrArg (fun t : ℝ => (b - a) * t) havg
    simpa [hba] using hmul
  have hsum : a + b = 0 := by
    -- The integral formula identifies the midpoint of the interval as `0`.
    have hsq : b ^ 2 - a ^ 2 = 0 := by
      have hsq' : (b ^ 2 - a ^ 2) / 2 = 0 := by
        simpa [integral_id] using hIntZero
      linarith
    have hfac : (b - a) * (b + a) = 0 := by
      nlinarith [hsq]
    simpa [add_comm] using (mul_eq_zero.mp hfac).resolve_left hba
  have hzero : a ≤ 0 ∧ 0 ≤ b := by
    -- Once the midpoint is `0`, the interval straddles the origin.
    constructor <;> linarith
  have hInter : Set.Icc a b ∩ Set.Iic 0 = Set.Icc a 0 := by
    -- Intersecting with the nonpositive half-line just truncates the right endpoint to `0`.
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, le_trans hx.2 hzero.2⟩, hx.2⟩
  have hnum : (volume (Set.Icc a b ∩ Set.Iic 0)).toReal = -a := by
    -- The left-half volume is the length of `[a, 0]`.
    rw [hInter]
    simp [Real.volume_Icc, hzero.1]
  calc
    (volume (Set.Icc a b ∩ Set.Iic 0)).toReal / (volume (Set.Icc a b)).toReal
        = (-a) / (b - a) := by
          rw [hnum, hvol]
    _ = (1 : ℝ) / 2 := by
      -- The centered interval contributes exactly half of its length on the left side.
      field_simp [hba]
      nlinarith [hsum]
    _ ≤ 1 - Real.exp (-1) := by
      -- The textbook constant is weaker than `1 / 2` because `exp 1 > 2`.
      rw [Real.exp_neg]
      have hexp : 0 < Real.exp 1 := Real.exp_pos 1
      have htwo : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      field_simp [hexp.ne']
      nlinarith

/-- Helper for Lemma 3.2.6: a convex subset of `ℝ` with finite positive volume and zero set
average satisfies the sharp left-half volume bound after replacing it almost everywhere by its
bounding interval. -/
theorem convexReal_leftHalf_ratio_le_one_sub_exp_neg_one_of_setAverage_zero
    (A : Set ℝ) (hA_convex : Convex ℝ A) (hA_finite : volume A ≠ ⊤) (hA_pos : volume A ≠ 0)
    (hA_center : (⨍ t in A, t) = 0) :
    (volume (A ∩ Set.Iic 0)).toReal / (volume A).toReal ≤ 1 - Real.exp (-1) := by
  have hA_nonempty : A.Nonempty := by
    -- Positive volume rules out the empty set.
    by_contra hA_empty
    apply hA_pos
    rw [Set.not_nonempty_iff_eq_empty.mp hA_empty, measure_empty]
  have hA_bddAbove : BddAbove A := by
    -- An unbounded-above convex subset of `ℝ` contains a whole right half-line, forcing infinite
    -- volume.
    by_contra hA_unbounded
    rcases hA_nonempty with ⟨a, ha⟩
    have hIci_subset : Set.Ici a ⊆ A := by
      intro x hx
      rcases (not_bddAbove_iff.mp hA_unbounded) x with ⟨y, hyA, hxy⟩
      exact hA_convex.ordConnected.out ha hyA ⟨hx, hxy.le⟩
    have hIci_le : volume (Set.Ici a) ≤ volume A :=
      MeasureTheory.measure_mono (μ := volume) hIci_subset
    have hA_top : volume A = ⊤ := by
      exact top_unique <| by
        simpa [Real.volume_Ici] using hIci_le
    exact hA_finite hA_top
  have hA_bddBelow : BddBelow A := by
    -- The same argument on the left gives lower boundedness.
    by_contra hA_unbounded
    rcases hA_nonempty with ⟨a, ha⟩
    have hIic_subset : Set.Iic a ⊆ A := by
      intro x hx
      rcases (not_bddBelow_iff.mp hA_unbounded) x with ⟨y, hyA, hyx⟩
      exact hA_convex.ordConnected.out hyA ha ⟨hyx.le, hx⟩
    have hIic_le : volume (Set.Iic a) ≤ volume A :=
      MeasureTheory.measure_mono (μ := volume) hIic_subset
    have hA_top : volume A = ⊤ := by
      exact top_unique <| by
        simpa [Real.volume_Iic] using hIic_le
    exact hA_finite hA_top
  have hIoo_subset :
      Set.Ioo (sInf A) (sSup A) ⊆ A :=
    (hA_convex.isConnected hA_nonempty).Ioo_csInf_csSup_subset hA_bddBelow hA_bddAbove
  have hIcc_subset : A ⊆ Set.Icc (sInf A) (sSup A) :=
    subset_Icc_csInf_csSup hA_bddBelow hA_bddAbove
  have hIcc_le : volume (Set.Icc (sInf A) (sSup A)) ≤ volume A := by
    -- The open interval already lies in `A`, and the two interval endpoints are null.
    calc
      volume (Set.Icc (sInf A) (sSup A)) = volume (Set.Ioo (sInf A) (sSup A)) := by
        exact MeasureTheory.measure_congr MeasureTheory.Ioo_ae_eq_Icc.symm
      _ ≤ volume A := MeasureTheory.measure_mono hIoo_subset
  have hIcc_finite : volume (Set.Icc (sInf A) (sSup A)) ≠ ⊤ := by
    exact (lt_of_le_of_lt hIcc_le (lt_top_iff_ne_top.mpr hA_finite)).ne
  have hA_ae :
      A =ᵐ[volume] Set.Icc (sInf A) (sSup A) := by
    -- The convex set can differ from its bounding interval only on the null endpoints.
    refine MeasureTheory.ae_eq_of_ae_subset_of_measure_ge
      (Filter.Eventually.of_forall hIcc_subset) hIcc_le (hA_convex.nullMeasurableSet volume)
      hIcc_finite
  have hInter_ae :
      Set.inter A (Set.Iic 0) =ᵐ[volume] Set.inter (Set.Icc (sInf A) (sSup A)) (Set.Iic 0) := by
    filter_upwards [hA_ae] with x hx
    apply propext
    constructor
    · intro hx'
      exact ⟨hx.mp hx'.1, hx'.2⟩
    · intro hx'
      exact ⟨hx.mpr hx'.1, hx'.2⟩
  have hCenterInterval : (⨍ t in Set.Icc (sInf A) (sSup A), t) = 0 := by
    -- Transport the zero average to the almost-everywhere equal interval.
    rw [← MeasureTheory.setAverage_congr hA_ae]
    exact hA_center
  have hsInf_le_sSup : sInf A ≤ sSup A := by
    -- Any point of `A` lies between the infimum and the supremum.
    rcases hA_nonempty with ⟨x, hxA⟩
    exact (csInf_le hA_bddBelow hxA).trans (le_csSup hA_bddAbove hxA)
  have hIntervalRatio :
      (volume (Set.Icc (sInf A) (sSup A) ∩ Set.Iic 0)).toReal /
          (volume (Set.Icc (sInf A) (sSup A))).toReal ≤
        1 - Real.exp (-1) :=
    centeredInterval_leftHalf_ratio_le_one_sub_exp_neg_one hsInf_le_sSup hCenterInterval
  have hNum :
      (volume (A ∩ Set.Iic 0)).toReal =
        (volume (Set.Icc (sInf A) (sSup A) ∩ Set.Iic 0)).toReal := by
    exact congrArg ENNReal.toReal (MeasureTheory.measure_congr hInter_ae)
  have hDen :
      (volume A).toReal = (volume (Set.Icc (sInf A) (sSup A))).toReal := by
    exact congrArg ENNReal.toReal (MeasureTheory.measure_congr hA_ae)
  -- Rewrite the ratio through the interval representative and close with the interval lemma.
  rw [hNum, hDen]
  exact hIntervalRatio
