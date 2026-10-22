/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_59
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_3_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10Core

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory Topology

noncomputable section

universe u

private def exercise1623DistributionFormula (x : ℝ) : ℝ :=
  if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0

private theorem exercise1623DistributionFormula_monotone :
    Monotone exercise1623DistributionFormula := by
  intro x y hxy
  by_cases hy : y ≤ 0
  · -- Proof comment: on `(-∞, 0]` the source formula is identically `0`.
    have hx : x ≤ 0 := le_trans hxy hy
    simp [exercise1623DistributionFormula, not_lt.mpr hx, not_lt.mpr hy]
  · have hy0 : 0 < y := lt_of_not_ge hy
    by_cases hx : x ≤ 0
    · -- Proof comment: crossing the branch point only requires nonnegativity of the positive
      -- branch, which follows from `cdf ≤ 1`.
      have hnonneg :
          0 ≤ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt y)) := by
        have hcdf : cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt y) ≤ 1 :=
          cdf_le_one (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt y)
        nlinarith
      simpa [exercise1623DistributionFormula, not_lt.mpr hx, hy0] using hnonneg
    · have hx0 : 0 < x := lt_of_not_ge hx
      -- Proof comment: on `(0, ∞)`, the Gaussian tail is monotone because `x ↦ 1 / √x` is
      -- antitone and the Gaussian cdf is monotone.
      have hdiv :
          1 / Real.sqrt y ≤ 1 / Real.sqrt x := by
        have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
        exact one_div_le_one_div_of_le (by positivity) hsqrt
      have hcdf :
          cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt y)⁻¹) ≤
            cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹) := by
        simpa [one_div] using monotone_cdf (gaussianReal (0 : ℝ) 1) hdiv
      have htail :
          1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹) ≤
            1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt y)⁻¹) := by
        linarith
      simpa [exercise1623DistributionFormula, hx0, hy0, one_div] using
        mul_le_mul_of_nonneg_left htail (show 0 ≤ (2 : ℝ) by positivity)

/-- Helper for Exercise 16.2.3: the standard Gaussian cdf is continuous on `ℝ`. -/
private lemma standardGaussianCdfContinuous :
    Continuous (cdf (gaussianReal (0 : ℝ) 1)) := by
  -- Proof comment: Exercise 8.3.1 upgrades atom-freeness of the Gaussian law to continuity of
  -- its cdf.
  letI : NoAtoms (gaussianReal (0 : ℝ) 1) :=
    noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  exact cdfContinuousOfNoAtoms (gaussianReal (0 : ℝ) 1)

/-- Helper for Exercise 16.2.3: the standard Gaussian cdf takes the value `1 / 2` at `0`. -/
private lemma standardGaussianCdf_zero :
    cdf (gaussianReal (0 : ℝ) 1) 0 = (1 / 2 : ℝ) := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  have hsymm : ν.map (fun x : ℝ ↦ -x) = ν := by
    simpa [ν] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hnoAtoms : NoAtoms ν :=
    noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  have hIci :
      ν (Set.Ici 0) = ν (Set.Iic 0) := by
    -- Proof comment: symmetry under `x ↦ -x` swaps the two half-lines.
    calc
      ν (Set.Ici 0) = ν.map (fun x : ℝ ↦ -x) (Set.Ici 0) := by
        rw [hsymm]
      _ = ν (Set.Iic 0) := by
        rw [Measure.map_apply measurable_neg measurableSet_Ici]
        congr 1
        ext x
        simp
  have hIci_eq_Ioi :
      ν (Set.Ici 0) = ν (Set.Ioi 0) := by
    -- Proof comment: atom-freeness removes the singleton mass at `0`.
    have hunion : Set.Ioi (0 : ℝ) ∪ ({(0 : ℝ)} : Set ℝ) = Set.Ici 0 := by
      ext x
      simp
    have hdisj : Disjoint (Set.Ioi (0 : ℝ)) ({(0 : ℝ)} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      simp
    calc
      ν (Set.Ici 0) = ν (Set.Ioi 0 ∪ ({(0 : ℝ)} : Set ℝ)) := by
        rw [hunion]
      _ = ν (Set.Ioi 0) + ν ({(0 : ℝ)} : Set ℝ) := by
        rw [measure_union hdisj (measurableSet_singleton (x := (0 : ℝ)))]
      _ = ν (Set.Ioi 0) := by
        simp [hnoAtoms.measure_singleton]
  have hsum :
      ν (Set.Iic 0) + ν (Set.Ioi 0) = 1 := by
    simpa [Set.compl_Iic] using prob_add_prob_compl (μ := ν) measurableSet_Iic
  have htwice :
      ν (Set.Iic 0) + ν (Set.Iic 0) = 1 := by
    calc
      ν (Set.Iic 0) + ν (Set.Iic 0)
          = ν (Set.Ici 0) + ν (Set.Iic 0) := by
              rw [hIci]
      _ = ν (Set.Ioi 0) + ν (Set.Iic 0) := by
            rw [hIci_eq_Ioi]
      _ = 1 := by
            simpa [add_comm] using hsum
  have htwice_real :
      2 * (ν (Set.Iic 0)).toReal = 1 := by
    -- Proof comment: convert the ENNReal identity to `ℝ` to solve the scalar equation.
    have htmp := congrArg ENNReal.toReal htwice
    simpa [ν, ENNReal.toReal_add, measure_ne_top ν _, two_mul] using htmp
  have hreal : (ν (Set.Iic 0)).toReal = (1 / 2 : ℝ) := by
    linarith
  -- Proof comment: `cdf μ 0` is just the mass of `(-∞, 0]`.
  rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def]
  simpa [ν] using hreal

private theorem exercise1623DistributionFormula_rightContinuous (x : ℝ) :
    ContinuousWithinAt exercise1623DistributionFormula (Set.Ici x) x := by
  by_cases hx_neg : x < 0
  · -- Proof comment: on a right neighborhood of a negative point, the formula stays on its zero
    -- branch.
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have hEq :
        exercise1623DistributionFormula =ᶠ[𝓝[>] x] fun _ : ℝ ↦ 0 := by
      filter_upwards [Ioo_mem_nhdsGT hx_neg] with t ht
      simp [exercise1623DistributionFormula, not_lt.mpr ht.2.le]
    exact
      continuousWithinAt_const.congr_of_eventuallyEq hEq
        (by simp [exercise1623DistributionFormula, not_lt.mpr hx_neg.le])
  by_cases hx_zero : x = 0
  · subst hx_zero
    -- Proof comment: after rewriting to the positive branch on `𝓝[>] 0`, the Gaussian cdf tail
    -- tends to `1` because `(√t)⁻¹ → +∞`.
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have hsqrt_zero :
        Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using
        ((Real.continuous_sqrt.continuousAt.continuousWithinAt :
          ContinuousWithinAt Real.sqrt (Set.Ioi (0 : ℝ)) (0 : ℝ))).tendsto
    have hsqrt_pos :
        Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓟 (Set.Ioi (0 : ℝ))) := by
      rw [Filter.tendsto_principal]
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.2 ht
    have hsqrt :
        Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      simpa [nhdsWithin] using hsqrt_zero.inf hsqrt_pos
    have hinv :
        Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsqrt
    have hcdf :
        Tendsto (fun t : ℝ ↦ cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt t)⁻¹))
          (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      (tendsto_cdf_atTop (gaussianReal (0 : ℝ) 1)).comp hinv
    have hbranch :
        Tendsto
          (fun t : ℝ ↦ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt t)⁻¹)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have htail :
          Tendsto
            (fun t : ℝ ↦ 1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt t)⁻¹))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have htail' :
            Tendsto
              (fun t : ℝ ↦ (1 : ℝ) - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt t)⁻¹))
              (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
          tendsto_const_nhds.sub hcdf
        simpa using htail'
      simpa using htail.const_mul 2
    have hEq :
        (fun t : ℝ ↦ exercise1623DistributionFormula t) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun t : ℝ ↦ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt t)⁻¹))) := by
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      rw [exercise1623DistributionFormula, if_pos ht0]
      simp [one_div]
    have hzero : exercise1623DistributionFormula 0 = 0 := by
      simp [exercise1623DistributionFormula]
    rw [hzero]
    exact (tendsto_congr' hEq).2 hbranch
  · have hx_pos : 0 < x := by
      exact lt_of_le_of_ne (le_of_not_gt hx_neg) (Ne.symm hx_zero)
    -- Proof comment: on the positive branch, the formula is a continuous composition of the
    -- Gaussian cdf with `x ↦ (√x)⁻¹`.
    rw [← continuousWithinAt_Ioi_iff_Ici]
    let G : ℝ → ℝ := fun y ↦
      2 * (1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt y)⁻¹))
    have hG : ContinuousAt G x := by
      have hsqrt_ne : Real.sqrt x ≠ 0 := by
        exact Real.sqrt_ne_zero'.2 hx_pos
      have hinv : ContinuousAt (fun y : ℝ ↦ (Real.sqrt y)⁻¹) x :=
        (Real.continuous_sqrt.continuousAt.inv₀ hsqrt_ne)
      have hcdf :
          ContinuousAt
            (fun y : ℝ ↦ cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt y)⁻¹)) x :=
        (standardGaussianCdfContinuous.continuousAt.comp hinv)
      exact (continuousAt_const.sub hcdf).const_mul 2
    have hEq : exercise1623DistributionFormula =ᶠ[𝓝[>] x] G := by
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      have ht_pos : 0 < t := lt_trans hx_pos ht
      simp [exercise1623DistributionFormula, G, ht_pos, one_div]
    exact
      hG.continuousWithinAt.congr_of_eventuallyEq hEq
        (by simp [exercise1623DistributionFormula, G, hx_pos, one_div])

/-- The textbook distribution function `F` from Exercise 16.2.3, viewed as the canonical Chapter 1
distribution-function owner object. -/
def exercise1623DistributionFunction : StieltjesFunction ℝ where
  toFun := exercise1623DistributionFormula
  mono' := exercise1623DistributionFormula_monotone
  right_continuous' := exercise1623DistributionFormula_rightContinuous

/-- The textbook formula for the distribution function in Exercise 16.2.3. -/
@[simp] theorem exercise1623DistributionFunction_apply (x : ℝ) :
    exercise1623DistributionFunction x =
      if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0 := rfl

/-- The textbook function in Exercise 16.2.3 is a distribution function in the Chapter 1 sense. -/
instance : IsDistributionFunction exercise1623DistributionFunction := by
  -- Proof comment: the Stieltjes structure was already provided above; here we only check the
  -- range constraints and the endpoint limits.
  refine
    { toIsDefectiveDistributionFunction :=
        { nonneg := ?_
          le_one := ?_
          tendsto_atBot_zero := ?_ }
      tendsto_atTop_one := ?_ }
  · intro x
    by_cases hx : x ≤ 0
    · simp [exercise1623DistributionFunction_apply, not_lt.mpr hx]
    · have hx_pos : 0 < x := lt_of_not_ge hx
      have hnonneg :
          0 ≤ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) := by
        have hcdf : cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x) ≤ 1 :=
          cdf_le_one (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)
        nlinarith
      simpa [exercise1623DistributionFunction_apply, hx_pos] using hnonneg
  · intro x
    by_cases hx : x ≤ 0
    · simp [exercise1623DistributionFunction_apply, not_lt.mpr hx]
    · have hx_pos : 0 < x := lt_of_not_ge hx
      have hhalf :
          (1 / 2 : ℝ) ≤ cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x) := by
        calc
          (1 / 2 : ℝ) = cdf (gaussianReal (0 : ℝ) 1) 0 := by
            rw [standardGaussianCdf_zero]
          _ ≤ cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x) := by
            exact monotone_cdf (gaussianReal (0 : ℝ) 1) (by positivity)
      have hle :
          2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) ≤ 1 := by
        nlinarith
      simpa [exercise1623DistributionFunction_apply, hx_pos] using hle
  · -- Proof comment: sufficiently negative points stay on the zero branch identically.
    have hEq :
        (fun x : ℝ ↦ exercise1623DistributionFunction x) =ᶠ[atBot] fun _ : ℝ ↦ 0 := by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
      simp [exercise1623DistributionFunction_apply, not_lt.mpr hx.le]
    exact (tendsto_congr' hEq).2 tendsto_const_nhds
  · -- Proof comment: at `+∞`, the reciprocal square-root tends to `0`, so continuity of the
    -- Gaussian cdf at `0` turns the branch limit into `2 * (1 - 1 / 2) = 1`.
    have hEq :
        (fun x : ℝ ↦ exercise1623DistributionFunction x) =ᶠ[atTop]
          (fun x : ℝ ↦ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp [exercise1623DistributionFunction_apply, hx, one_div]
    have hinv :
        Tendsto (fun x : ℝ ↦ (Real.sqrt x)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)
    have hcdf :
        Tendsto (fun x : ℝ ↦ cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹))
          atTop (𝓝 ((1 / 2 : ℝ))) := by
      simpa [standardGaussianCdf_zero] using
        (standardGaussianCdfContinuous.continuousAt.tendsto.comp hinv)
    have hbranch :
        Tendsto
          (fun x : ℝ ↦ 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹)))
          atTop (𝓝 (1 : ℝ)) := by
      have htail :
          Tendsto
            (fun x : ℝ ↦ 1 - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹))
            atTop (𝓝 (1 / 2 : ℝ)) := by
        have htail' :
            Tendsto
              (fun x : ℝ ↦ (1 : ℝ) - cdf (gaussianReal (0 : ℝ) 1) ((Real.sqrt x)⁻¹))
              atTop (𝓝 ((1 : ℝ) - (1 / 2 : ℝ))) :=
          tendsto_const_nhds.sub hcdf
        convert htail' using 2
        norm_num
      simpa using htail.const_mul 2
    exact (tendsto_congr' hEq).2 hbranch

-- Proof sketch: unfold `exercise1623DistributionFunction`; on the nonpositive branch the defining
-- `if` returns `0`.
/-- The textbook function `F` vanishes on `(-∞, 0]`. -/
theorem exercise1623DistributionFunction_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    exercise1623DistributionFunction x = 0 := by
  -- Proof comment: the defining branch condition `0 < x` is false on `(-∞, 0]`.
  simp [exercise1623DistributionFunction_apply, not_lt.mpr hx]

/-- Helper for Exercise 16.2.3: the canonical probability law attached to the textbook
distribution function is its Stieltjes measure. -/
private def exercise1623ProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨exercise1623DistributionFunction.measure, inferInstance⟩

/-- Helper for Exercise 16.2.3: the canonical Stieltjes measure has the prescribed cdf. -/
private lemma exercise1623ProbabilityMeasure_cdf_eq :
    cdf (exercise1623ProbabilityMeasure : Measure ℝ) = exercise1623DistributionFunction := by
  let hF : IsDistributionFunction exercise1623DistributionFunction := inferInstance
  -- Proof comment: this is the Chapter 1 cdf/Stieltjes inversion for distribution functions.
  simpa [exercise1623ProbabilityMeasure] using
    ProbabilityTheory.cdf_measure_stieltjesFunction exercise1623DistributionFunction
      hF.toIsDefectiveDistributionFunction.tendsto_atBot_zero
      hF.tendsto_atTop_one

/-- Helper for Exercise 16.2.3: any probability law with the textbook cdf equals the canonical
Stieltjes law. -/
private lemma measure_eq_exercise1623ProbabilityMeasure
    (μ : ProbabilityMeasure ℝ)
    (hμ : cdf (μ : Measure ℝ) = exercise1623DistributionFunction) :
    (μ : Measure ℝ) = (exercise1623ProbabilityMeasure : Measure ℝ) := by
  -- Proof comment: probability measures on `ℝ` are determined by their cdfs.
  apply (MeasureTheory.Measure.cdf_eq_iff (μ : Measure ℝ)
    (exercise1623ProbabilityMeasure : Measure ℝ)).1
  simpa [exercise1623ProbabilityMeasure_cdf_eq] using hμ

/-- Helper for Exercise 16.2.3: the canonical law attached to the textbook cdf is supported on
`[0, ∞)`. -/
private lemma exercise1623ProbabilityMeasure_nonneg_ae :
    ∀ᵐ x ∂(exercise1623ProbabilityMeasure : Measure ℝ), 0 ≤ x := by
  have hmass_zero :
      (exercise1623ProbabilityMeasure : Measure ℝ) (Set.Iic 0) = 0 := by
    -- Proof comment: the cdf value at `0` is `0`, so the canonical law gives no mass to
    -- `(-∞, 0]`.
    have hcdf0 :
        cdf (exercise1623ProbabilityMeasure : Measure ℝ) 0 =
          exercise1623DistributionFunction 0 := by
      simpa using congrArg (fun F : StieltjesFunction ℝ ↦ F 0) exercise1623ProbabilityMeasure_cdf_eq
    rw [exercise1623DistributionFunction_of_nonpos (x := 0) le_rfl] at hcdf0
    rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def] at hcdf0
    rcases (ENNReal.toReal_eq_zero_iff _).mp hcdf0 with hzero | htop
    · exact hzero
    · exact (measure_ne_top _ _ htop).elim
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hmass_zero
  intro x hx
  exact (lt_of_not_ge hx).le

/-- Helper for Exercise 16.2.3: the positive heavy-tail constant extracted from the Gaussian lower
bound on `[0, 1]`. -/
private def exercise1623TailConstant : ℝ :=
  2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ)))

/-- Helper for Exercise 16.2.3: the heavy-tail constant is strictly positive. -/
private lemma exercise1623TailConstant_pos : 0 < exercise1623TailConstant := by
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hinv_pos : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := inv_pos.mpr hsqrt_pos
  have hexp_pos : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  have hmul_pos : 0 < (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ)) :=
    mul_pos hinv_pos hexp_pos
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
  simpa [exercise1623TailConstant] using mul_pos htwo_pos hmul_pos

/-- Helper for Exercise 16.2.3: on `[1, ∞)`, the canonical tail dominates a positive multiple of
`1 / √x`. -/
private lemma exercise1623Tail_eq_twoGaussianMass {x : ℝ} (hx : x ∈ Set.Ici (1 : ℝ)) :
    (exercise1623ProbabilityMeasure : Measure ℝ) (Set.Ioi x) =
      (2 : ENNReal) * (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 (1 / Real.sqrt x)) := by
  let μ : Measure ℝ := exercise1623ProbabilityMeasure
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  let a : ℝ := 1 / Real.sqrt x
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hμcdf :
      cdf μ x = 2 * (1 - cdf ν a) := by
    have hEq :=
      congrArg (fun F : StieltjesFunction ℝ ↦ F x) exercise1623ProbabilityMeasure_cdf_eq
    simpa [μ, ν, a, exercise1623DistributionFunction_apply, hx_pos] using hEq
  have hμsplit :
      μ (Set.Iic x) + μ (Set.Ioi x) = 1 := by
    simpa [μ, Set.compl_Iic] using prob_add_prob_compl (μ := μ) measurableSet_Iic
  have hμtail_real :
      (μ (Set.Ioi x)).toReal = 1 - cdf μ x := by
    have htmp := congrArg ENNReal.toReal hμsplit
    have hreal :
        cdf μ x + (μ (Set.Ioi x)).toReal = 1 := by
      simpa [μ, ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def,
        ENNReal.toReal_add, measure_ne_top μ _] using htmp
    linarith
  have hunion :
      Set.Iic a = Set.Iic 0 ∪ Set.Ioc 0 a := by
    ext y
    by_cases hy0 : y ≤ 0
    · have hya : y ≤ a := le_trans hy0 ha_nonneg
      simp [Set.mem_Iic, Set.mem_Ioc, hy0, hya]
    · have hy_pos : 0 < y := lt_of_not_ge hy0
      simp [Set.mem_Iic, Set.mem_Ioc, hy0, hy_pos]
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioc 0 a) := by
    refine Set.disjoint_left.2 ?_
    intro y hy1 hy2
    exact not_lt_of_ge hy1 hy2.1
  have hνsplit :
      ν (Set.Iic a) = ν (Set.Iic 0) + ν (Set.Ioc 0 a) := by
    rw [hunion, measure_union hdisj measurableSet_Ioc]
  have hνmass_real :
      (ν (Set.Ioc 0 a)).toReal = cdf ν a - (1 / 2 : ℝ) := by
    have htmp := congrArg ENNReal.toReal hνsplit
    have hreal :
        cdf ν a = cdf ν 0 + (ν (Set.Ioc 0 a)).toReal := by
      simpa [ν, ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def,
        ENNReal.toReal_add, measure_ne_top ν _] using htmp
    rw [standardGaussianCdf_zero] at hreal
    linarith
  have hmain_real :
      (μ (Set.Ioi x)).toReal = 2 * (ν (Set.Ioc 0 a)).toReal := by
    rw [hμtail_real, hμcdf, hνmass_real]
    ring
  have hμ_ne_top : μ (Set.Ioi x) ≠ ⊤ := measure_ne_top μ _
  have hrhs_ne_top : (2 : ENNReal) * ν (Set.Ioc 0 a) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top ν _)
  rw [← ENNReal.ofReal_toReal hμ_ne_top, ← ENNReal.ofReal_toReal hrhs_ne_top]
  exact congrArg ENNReal.ofReal <|
    by simpa [ν, a, ENNReal.toReal_mul] using hmain_real

/-- Helper for Exercise 16.2.3: the standard Gaussian mass on `(0, a]` dominates the interval
length times the density at `1` whenever `0 ≤ a ≤ 1`. -/
private lemma exercise1623GaussianIntervalMassLower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))) * a) ≤
      (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 a) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))
  have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ c) volume 0 a := by
    exact continuous_const.intervalIntegrable _ _
  have hgauss_int : IntervalIntegrable (fun y : ℝ ↦ gaussianPDFReal (0 : ℝ) 1 y) volume 0 a := by
    exact (integrable_gaussianPDFReal (0 : ℝ) (1 : NNReal)).intervalIntegrable
  have hpointwise :
      ∀ y ∈ Set.Icc (0 : ℝ) a, c ≤ gaussianPDFReal (0 : ℝ) 1 y := by
    intro y hy
    have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans ha1⟩
    have hy_sq_le : y ^ (2 : ℕ) ≤ 1 := by
      nlinarith [sq_nonneg y, hy01.1, hy01.2]
    have hexp :
        Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(y ^ (2 : ℕ)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hpref_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hexp hpref_nonneg
    simpa [c, ProbabilityTheory.gaussianPDFReal, pow_two, sub_eq_add_neg, mul_comm, mul_left_comm,
      mul_assoc] using hmul
  have hreal :
      c * a ≤ ∫ y in 0..a, gaussianPDFReal (0 : ℝ) 1 y := by
    calc
      c * a = ∫ y in 0..a, c := by
        rw [intervalIntegral.integral_const, sub_zero]
        simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ y in 0..a, gaussianPDFReal (0 : ℝ) 1 y := by
            exact intervalIntegral.integral_mono_on ha0 hconst_int hgauss_int hpointwise
  have hgauss_eq :
      (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 a) =
        ENNReal.ofReal (∫ y in 0..a, gaussianPDFReal (0 : ℝ) 1 y) := by
    rw [ProbabilityTheory.gaussianReal_apply_eq_integral (μ := (0 : ℝ)) (v := (1 : NNReal))
      (by norm_num) (Set.Ioc 0 a)]
    rw [intervalIntegral.integral_of_le ha0]
  rw [hgauss_eq]
  exact ENNReal.ofReal_le_ofReal hreal

private lemma exercise1623ProbabilityMeasure_tail_lower {x : ℝ} (hx : x ∈ Set.Ici (1 : ℝ)) :
    ENNReal.ofReal
        (exercise1623TailConstant * (1 / Real.sqrt x)) ≤
      (exercise1623ProbabilityMeasure : Measure ℝ) (Set.Ioi x) := by
  let a : ℝ := 1 / Real.sqrt x
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hsqrt_one_le : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have ha1 : a ≤ 1 := by
    dsimp [a]
    simpa using one_div_le_one_div_of_le (by positivity : 0 < (1 : ℝ)) hsqrt_one_le
  have hgauss :
      ENNReal.ofReal
          (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))) * a) ≤
        (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 a) :=
    exercise1623GaussianIntervalMassLower ha0 ha1
  have hdouble :
      (2 : ENNReal) *
          ENNReal.ofReal
            (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))) * a) ≤
        (2 : ENNReal) * (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 a) :=
    mul_le_mul_left' hgauss (2 : ENNReal)
  calc
    ENNReal.ofReal (exercise1623TailConstant * (1 / Real.sqrt x))
        = (2 : ENNReal) *
            ENNReal.ofReal
              (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))) * a) := by
              simp [exercise1623TailConstant, a, ENNReal.ofReal_mul, mul_left_comm, mul_comm]
    _ ≤ (2 : ENNReal) * (gaussianReal (0 : ℝ) 1) (Set.Ioc 0 a) := hdouble
    _ = (exercise1623ProbabilityMeasure : Measure ℝ) (Set.Ioi x) := by
          simpa [a] using (exercise1623Tail_eq_twoGaussianMass hx).symm

/-- Helper for Exercise 16.2.3: the benchmark tail sequence `n ↦ c / √(n + 1)` is not summable.
-/
private lemma exercise1623_tailLower_not_summable :
    ¬ Summable (fun n : ℕ ↦ exercise1623TailConstant * (1 / Real.sqrt (n + 1 : ℝ))) := by
  intro hsum
  have hsqrt :
      Summable (fun n : ℕ ↦ 1 / Real.sqrt (n + 1 : ℝ)) := by
    have hconst_ne : exercise1623TailConstant ≠ 0 := ne_of_gt exercise1623TailConstant_pos
    exact (summable_mul_left_iff hconst_ne).mp hsum
  have hrpow :
      Summable (fun n : ℕ ↦ ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    apply (_root_.summable_nat_add_iff 1).1
    refine hsqrt.congr ?_
    intro n
    rw [Real.sqrt_eq_rpow]
    simp [one_div]
  have hhalf : (1 : ℝ) < 1 / 2 := by
    exact (Real.summable_nat_rpow_inv.mp hrpow)
  linarith

/-- Helper for Exercise 16.2.3: the canonical law has infinite first moment. -/
private lemma exercise1623FirstMomentInfinite :
    ¬ Integrable id (exercise1623ProbabilityMeasure : Measure ℝ) := by
  intro hInt
  let μ : Measure ℝ := exercise1623ProbabilityMeasure
  have hnonneg : 0 ≤ᵐ[μ] id := by
    simpa [μ] using exercise1623ProbabilityMeasure_nonneg_ae
  have hlin_ne_top :
      ∫⁻ x, ENNReal.ofReal (id x) ∂μ ≠ ⊤ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable aestronglyMeasurable_id hnonneg).2 hInt
  have hseries_le :
      (∑' n : ℕ, μ {x | (n + 1 : ℝ) ≤ x}) ≤ ∫⁻ x, ENNReal.ofReal (id x) ∂μ := by
    simpa [μ] using tsum_measure_superlevel_nat_le_lintegral
      (μ := μ) (f := id) measurable_id hnonneg
  have hseries_ne_top :
      (∑' n : ℕ, μ {x | (n + 1 : ℝ) ≤ x}) ≠ ⊤ :=
    ne_top_of_le_ne_top hlin_ne_top hseries_le
  have hclosed_summable :
      Summable (fun n : ℕ ↦ (μ {x | (n + 1 : ℝ) ≤ x}).toReal) :=
    ENNReal.summable_toReal hseries_ne_top
  have hbound :
      ∀ n : ℕ,
        exercise1623TailConstant * (1 / Real.sqrt (n + 1 : ℝ)) ≤
          (μ {x | (n + 1 : ℝ) ≤ x}).toReal := by
    intro n
    have hn_mem : ((n + 1 : ℝ)) ∈ Set.Ici (1 : ℝ) := by
      have hn_mem_real : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact hn_mem_real
    have htail :
        ENNReal.ofReal (exercise1623TailConstant * (1 / Real.sqrt (n + 1 : ℝ))) ≤
          μ (Set.Ioi (n + 1 : ℝ)) :=
      exercise1623ProbabilityMeasure_tail_lower (x := (n + 1 : ℝ)) hn_mem
    have hmono :
        μ (Set.Ioi (n + 1 : ℝ)) ≤ μ {x | (n + 1 : ℝ) ≤ x} :=
      measure_mono fun x hx ↦ show (n + 1 : ℝ) ≤ x from hx.le
    have hclosed :
        ENNReal.ofReal (exercise1623TailConstant * (1 / Real.sqrt (n + 1 : ℝ))) ≤
          μ {x | (n + 1 : ℝ) ≤ x} :=
      htail.trans hmono
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hclosed
  have hsummable :
      Summable (fun n : ℕ ↦ exercise1623TailConstant * (1 / Real.sqrt (n + 1 : ℝ))) := by
    refine Summable.of_nonneg_of_le ?_ hbound hclosed_summable
    intro n
    have hconst_nonneg : 0 ≤ exercise1623TailConstant := le_of_lt exercise1623TailConstant_pos
    have hsqrt_nonneg : 0 ≤ 1 / Real.sqrt (n + 1 : ℝ) := by positivity
    exact mul_nonneg hconst_nonneg hsqrt_nonneg
  exact exercise1623_tailLower_not_summable hsummable

/-- Helper for Exercise 16.2.3: after applying `ENNReal.ofReal`, truncating `id` at level `n`
simply keeps the nonnegative window `(0, n]`. -/
private lemma ofReal_truncation_id_eq_indicator (n : ℕ) :
    (fun x : ℝ ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)) =
      Set.indicator (Set.Ioc (0 : ℝ) (n : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) := by
  funext x
  by_cases hx_pos : 0 < x
  · by_cases hx_le : x ≤ n
    · have hmem : x ∈ Set.Ioc (-(n : ℝ)) (n : ℝ) := by
        constructor
        · linarith
        · exact_mod_cast hx_le
      have hmem' : x ∈ Set.Ioc (0 : ℝ) (n : ℝ) := ⟨hx_pos, by exact_mod_cast hx_le⟩
      simp [ProbabilityTheory.truncation, hmem, hmem']
    · have hnotmem : x ∉ Set.Ioc (-(n : ℝ)) (n : ℝ) := by
        simp [hx_le]
      have hnotmem' : x ∉ Set.Ioc (0 : ℝ) (n : ℝ) := by
        simp [hx_le]
      simp [ProbabilityTheory.truncation, hnotmem, hnotmem']
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx_pos
    have hnotmem' : x ∉ Set.Ioc (0 : ℝ) (n : ℝ) := by
      simp [hx_pos]
    by_cases hmem : x ∈ Set.Ioc (-(n : ℝ)) (n : ℝ)
    · simp [ProbabilityTheory.truncation, hmem, hnotmem', hx_nonpos]
    · simp [ProbabilityTheory.truncation, hmem, hnotmem']

/-- Helper for Exercise 16.2.3: the `ENNReal.ofReal` truncation sequence is monotone in the cutoff
level. -/
private lemma monotone_ofReal_truncation_id :
    Monotone (fun n : ℕ ↦ fun x : ℝ ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)) := by
  intro n k hnk x
  change
    ENNReal.ofReal (ProbabilityTheory.truncation id n x) ≤
      ENNReal.ofReal (ProbabilityTheory.truncation id k x)
  have hleft := congrArg (fun f : ℝ → ENNReal ↦ f x) (ofReal_truncation_id_eq_indicator n)
  have hright := congrArg (fun f : ℝ → ENNReal ↦ f x) (ofReal_truncation_id_eq_indicator k)
  have hleft' :
      ENNReal.ofReal (ProbabilityTheory.truncation id n x) =
        Set.indicator (Set.Ioc (0 : ℝ) (n : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) x := by
    simpa using hleft
  have hright' :
      ENNReal.ofReal (ProbabilityTheory.truncation id k x) =
        Set.indicator (Set.Ioc (0 : ℝ) (k : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) x := by
    simpa using hright
  rw [hleft', hright']
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) (n : ℝ)
  · have hx' : x ∈ Set.Ioc (0 : ℝ) (k : ℝ) := by
      refine ⟨hx.1, ?_⟩
      exact le_trans hx.2 (by exact_mod_cast hnk)
    simp [hx, hx']
  · by_cases hx' : x ∈ Set.Ioc (0 : ℝ) (k : ℝ)
    · simp [hx, hx']
    · simp [hx, hx']

/-- Helper for Exercise 16.2.3: for `x ≥ 0`, the nonnegative truncations
`ENNReal.ofReal (ProbabilityTheory.truncation id n x)` increase to `ENNReal.ofReal x`. -/
private lemma iSup_ofReal_truncation_id_nat_eq {x : ℝ} (hx : 0 ≤ x) :
    (⨆ n : ℕ, ENNReal.ofReal (ProbabilityTheory.truncation id n x)) = ENNReal.ofReal x := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every truncation is bounded above by the original nonnegative value.
    refine iSup_le fun n ↦ ?_
    apply ENNReal.ofReal_le_ofReal
    calc
      ProbabilityTheory.truncation id n x ≤ |ProbabilityTheory.truncation id n x| := le_abs_self _
      _ ≤ |x| := ProbabilityTheory.abs_truncation_le_abs_self _ _ _
      _ = x := abs_of_nonneg hx
  · -- Proof comment: once the cutoff exceeds `x`, the truncation agrees exactly with `x`.
    refine le_iSup_of_le (Nat.ceil x + 1) ?_
    have hx_lt : |x| < ((Nat.ceil x + 1 : ℕ) : ℝ) := by
      rw [abs_of_nonneg hx]
      exact lt_of_le_of_lt (Nat.le_ceil x) (by exact_mod_cast Nat.lt_succ_self (Nat.ceil x))
    rw [ProbabilityTheory.truncation_eq_self hx_lt]
    simp

/-- Helper for Exercise 16.2.3: if a nonnegative law has uniformly bounded truncation
expectations, then its first moment is finite. -/
private lemma integrable_id_of_nonneg_of_boundedTruncationIntegrals
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) (m : ℝ)
    (hbound : ∀ n : ℕ, ∫ x, ProbabilityTheory.truncation id n x ∂μ ≤ m) :
    Integrable id μ := by
  have hm_nonneg : 0 ≤ m := by
    have hzero := hbound 0
    simpa [ProbabilityTheory.truncation_zero] using hzero
  let f : ℕ → ℝ → ENNReal := fun n x ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)
  have hf_meas (n : ℕ) : AEMeasurable (f n) μ := by
    exact (aestronglyMeasurable_id.truncation.aemeasurable.ennreal_ofReal)
  have hf_mono : ∀ᵐ x ∂μ, Monotone (fun n ↦ f n x) := by
    filter_upwards [hnonneg] with x hx
    intro n k hnk
    exact monotone_ofReal_truncation_id hnk x
  have hlin_bound (n : ℕ) : ∫⁻ x, f n x ∂μ ≤ ENNReal.ofReal m := by
    have htrunc_nonneg : 0 ≤ᵐ[μ] fun x ↦ ProbabilityTheory.truncation id n x := by
      filter_upwards [hnonneg] with x hx
      exact ProbabilityTheory.truncation_nonneg (n : ℝ) hx
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (aestronglyMeasurable_id.integrable_truncation) htrunc_nonneg]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlin_top :
      ∫⁻ x, ENNReal.ofReal x ∂μ ≤ ENNReal.ofReal m := by
    have hiSup_eq :
        (fun x ↦ ENNReal.ofReal x) =ᵐ[μ] fun x ↦ ⨆ n : ℕ, f n x := by
      filter_upwards [hnonneg] with x hx
      simpa [f] using (iSup_ofReal_truncation_id_nat_eq hx).symm
    calc
      ∫⁻ x, ENNReal.ofReal x ∂μ = ∫⁻ x, ⨆ n : ℕ, f n x ∂μ := by
        exact lintegral_congr_ae hiSup_eq
      _ = ⨆ n : ℕ, ∫⁻ x, f n x ∂μ := by
        rw [MeasureTheory.lintegral_iSup' hf_meas hf_mono]
      _ ≤ ENNReal.ofReal m := by
        exact iSup_le hlin_bound
  have hne_top : ∫⁻ x, ENNReal.ofReal (id x) ∂μ ≠ (⊤ : ENNReal) := by
    exact ne_of_lt (lt_of_le_of_lt hlin_top ENNReal.ofReal_lt_top)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    aestronglyMeasurable_id hnonneg).1 hne_top

/-- Helper for Exercise 16.2.3: the reciprocal-square map on `ℝ` is measurable. -/
private lemma measurable_realInvSq :
    Measurable (fun z : ℝ ↦ (z⁻¹) ^ (2 : ℕ)) := by
  -- Proof comment: the map is a composition of the measurable inversion map with a polynomial.
  fun_prop

/-- Helper for Exercise 16.2.3: the `NNReal`-valued reciprocal-square map is measurable. -/
private lemma measurable_realToNNRealInvSq :
    Measurable (fun z : ℝ ↦ Real.toNNReal ((z⁻¹) ^ (2 : ℕ))) := by
  -- Proof comment: `Real.toNNReal` preserves measurability of the real reciprocal-square map.
  exact measurable_real_toNNReal.comp measurable_realInvSq

/-- Helper for Exercise 16.2.3: the explicit Gaussian reciprocal-square witness on `ℝ`. -/
private def gaussianReciprocalSquareLaw : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨gaussianReal (0 : ℝ) 1, inferInstance⟩ : ProbabilityMeasure ℝ)
    measurable_realInvSq.aemeasurable

/-- Helper for Exercise 16.2.3: the same witness, but kept on `[0, ∞)` for Laplace-transform
arguments. -/
private def gaussianReciprocalSquareLawNN : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map
    (⟨gaussianReal (0 : ℝ) 1, inferInstance⟩ : ProbabilityMeasure ℝ)
    measurable_realToNNRealInvSq.aemeasurable

/-- Helper for Exercise 16.2.3: coercing `Real.toNNReal (z⁻²)` back to `ℝ` recovers `z⁻²`
because reciprocal squares are nonnegative. -/
private lemma coe_realToNNReal_invSq (z : ℝ) :
    ((Real.toNNReal ((z⁻¹) ^ (2 : ℕ)) : NNReal) : ℝ) = (z⁻¹) ^ (2 : ℕ) := by
  -- Proof comment: reciprocal squares lie in `[0, ∞)`, so `Real.toNNReal` is a two-sided
  -- inverse after coercing back to `ℝ`.
  have hnonneg : 0 ≤ (z⁻¹) ^ (2 : ℕ) := by positivity
  exact Real.coe_toNNReal _ hnonneg

/-- Helper for Exercise 16.2.3: for `x > 0`, the reciprocal-square inequality is equivalent to the
tail event `1 / √x ≤ |z|`, up to the zero atom where reciprocal inversion is defined as `0`. -/
private lemma invSq_le_iff_zero_or_le_abs {x z : ℝ} (hx : 0 < x) :
    (z⁻¹) ^ (2 : ℕ) ≤ x ↔ z = 0 ∨ 1 / Real.sqrt x ≤ |z| := by
  by_cases hz : z = 0
  · -- Proof comment: at `z = 0`, the reciprocal-square convention gives the value `0`.
    simp [hz, hx.le]
  · constructor
    · intro h
      right
      have hz2_nonneg : 0 ≤ z ^ 2 := by positivity
      have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      have h1 : 1 ≤ x * z ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right h hz2_nonneg
        have hleft : (z⁻¹) ^ (2 : ℕ) * z ^ 2 = 1 := by
          field_simp [pow_two, hz]
        rwa [hleft] at hmul
      have hsq : 1 ≤ x * |z| ^ (2 : ℕ) := by
        simpa [sq_abs] using h1
      have h2 : 1 ≤ Real.sqrt x * |z| := by
        have hsq' : 1 ≤ (Real.sqrt x * |z|) ^ (2 : ℕ) := by
          calc
            1 ≤ x * |z| ^ (2 : ℕ) := hsq
            _ = (Real.sqrt x * |z|) ^ (2 : ℕ) := by
                  nlinarith [Real.sq_sqrt (le_of_lt hx)]
        have hnonneg : 0 ≤ Real.sqrt x * |z| := by positivity
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (Real.sqrt x)⁻¹ by positivity)
      simpa [div_eq_mul_inv, hsqrt_pos.ne', pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
    · intro h
      rcases h with hzero | habs
      · exact (hz hzero).elim
      · have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
        have h2 := mul_le_mul_of_nonneg_left habs hsqrt_pos.le
        have h2' : 1 ≤ Real.sqrt x * |z| := by
          simpa [div_eq_mul_inv, hsqrt_pos.ne', pow_two, mul_assoc, mul_left_comm, mul_comm] using h2
        have hsq' : 1 ≤ (Real.sqrt x * |z|) ^ (2 : ℕ) := by
          have hnonneg : 0 ≤ Real.sqrt x * |z| := by positivity
          nlinarith
        have h1 : 1 ≤ x * z ^ (2 : ℕ) := by
          have hsq : 1 ≤ x * |z| ^ (2 : ℕ) := by
            calc
              1 ≤ (Real.sqrt x * |z|) ^ (2 : ℕ) := hsq'
              _ = x * |z| ^ (2 : ℕ) := by
                    nlinarith [Real.sq_sqrt (le_of_lt hx)]
          simpa [sq_abs] using hsq
        have hmul := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (z ^ (2 : ℕ))⁻¹ by positivity)
        have hright : x * z ^ (2 : ℕ) * (z ^ (2 : ℕ))⁻¹ = x := by
          field_simp [pow_two, hz]
        have hleft : 1 * (z ^ (2 : ℕ))⁻¹ = (z⁻¹) ^ (2 : ℕ) := by
          simp [pow_two, mul_comm]
        rwa [hleft, hright] at hmul

/-- Helper for Exercise 16.2.3: the centered standard Gaussian satisfies the textbook tail
identity `P(a ≤ |Z|) = 2 (1 - Φ(a))` for every `a > 0`. -/
private lemma gaussianAbsTail_real {a : ℝ} (ha : 0 < a) :
    ((gaussianReal (0 : ℝ) 1) {z : ℝ | a ≤ |z|}).toReal =
      2 * (1 - cdf (gaussianReal (0 : ℝ) 1) a) := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  have hsymm : ν.map (fun x : ℝ ↦ -x) = ν := by
    simpa [ν] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hnoAtoms : NoAtoms ν :=
    noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  have hset : ({z : ℝ | a ≤ |z|} : Set ℝ) = Set.Iic (-a) ∪ Set.Ici a := by
    -- Proof comment: the event `a ≤ |z|` splits into the two outer Gaussian tails.
    ext z
    simpa [le_abs']
  have hdisj : Disjoint (Set.Iic (-a)) (Set.Ici a) := by
    refine Set.disjoint_left.2 ?_
    intro z hz1 hz2
    have hcontra : a ≤ -a := le_trans hz2 hz1
    linarith
  have hneg : ν (Set.Iic (-a)) = ν (Set.Ici a) := by
    -- Proof comment: Gaussian symmetry identifies the left tail at `-a` with the right tail at
    -- `a`.
    calc
      ν (Set.Iic (-a)) = ν.map (fun x : ℝ ↦ -x) (Set.Iic (-a)) := by
        rw [hsymm]
      _ = ν (Set.Ici a) := by
        rw [Measure.map_apply measurable_neg measurableSet_Iic]
        congr 1
        ext z
        simp
  have hIci_eq_Ioi : ν (Set.Ici a) = ν (Set.Ioi a) := by
    -- Proof comment: atom-freeness removes the singleton at the boundary point `a`.
    have hunion : Set.Ioi a ∪ ({a} : Set ℝ) = Set.Ici a := by
      ext z
      simp
    have hdisj' : Disjoint (Set.Ioi a) ({a} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      simp
    calc
      ν (Set.Ici a) = ν (Set.Ioi a ∪ ({a} : Set ℝ)) := by
        rw [hunion]
      _ = ν (Set.Ioi a) + ν ({a} : Set ℝ) := by
        rw [measure_union hdisj' (measurableSet_singleton (x := a))]
      _ = ν (Set.Ioi a) := by
        simp [hnoAtoms.measure_singleton]
  have htail_real : (ν (Set.Ioi a)).toReal = 1 - cdf ν a := by
    -- Proof comment: the right tail is the complement of `(-∞, a]`.
    have hsum : ν (Set.Iic a) + ν (Set.Ioi a) = 1 := by
      simpa [Set.compl_Iic] using prob_add_prob_compl (μ := ν) measurableSet_Iic
    have htmp := congrArg ENNReal.toReal hsum
    have hreal : cdf ν a + (ν (Set.Ioi a)).toReal = 1 := by
      simpa [ν, ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def, ENNReal.toReal_add,
        measure_ne_top ν _] using htmp
    linarith
  have htail_eq : ((ν {z : ℝ | a ≤ |z|}).toReal) = 2 * (ν (Set.Ioi a)).toReal := by
    rw [hset, measure_union hdisj measurableSet_Ici]
    rw [hneg, hIci_eq_Ioi]
    have htmp :
        (ν (Set.Ioi a) + ν (Set.Ioi a)).toReal =
          (ν (Set.Ioi a)).toReal + (ν (Set.Ioi a)).toReal := by
      simpa using ENNReal.toReal_add (measure_ne_top ν (Set.Ioi a)) (measure_ne_top ν (Set.Ioi a))
    simpa [two_mul] using htmp
  calc
    ((gaussianReal (0 : ℝ) 1) {z : ℝ | a ≤ |z|}).toReal = 2 * (ν (Set.Ioi a)).toReal := by
      simpa [ν] using htail_eq
    _ = 2 * (1 - cdf ν a) := by
      rw [htail_real]
    _ = 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) a) := by
      rfl

/-- Helper for Exercise 16.2.3: the explicit reciprocal-square witness puts zero mass at `0`. -/
private lemma gaussianReciprocalSquareLaw_cdf_zero :
    cdf (gaussianReciprocalSquareLaw : Measure ℝ) 0 = 0 := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  have hnoAtoms : NoAtoms ν :=
    noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def, gaussianReciprocalSquareLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_realInvSq measurableSet_Iic]
  have hpre : (fun z : ℝ ↦ (z⁻¹) ^ (2 : ℕ)) ⁻¹' Set.Iic 0 = ({0} : Set ℝ) := by
    ext z
    constructor
    · intro hz
      have hnonneg : 0 ≤ (z⁻¹) ^ (2 : ℕ) := by positivity
      have heq : (z⁻¹) ^ (2 : ℕ) = 0 := le_antisymm hz hnonneg
      exact inv_eq_zero.mp (eq_zero_of_pow_eq_zero heq)
    · intro hz
      simpa using hz
  rw [hpre]
  simp [ν, hnoAtoms.measure_singleton]

/-- Helper for Exercise 16.2.3: the explicit Gaussian reciprocal-square witness has exactly the
textbook distribution function `F`. -/
private lemma gaussianReciprocalSquareLaw_cdf_eq :
    cdf (gaussianReciprocalSquareLaw : Measure ℝ) = exercise1623DistributionFunction := by
  ext x
  by_cases hx : x ≤ 0
  · -- Proof comment: the reciprocal-square witness is nonnegative and has no atom at `0`, so
    -- its cdf vanishes on `(-∞, 0]`.
    have hnonneg : 0 ≤ cdf (gaussianReciprocalSquareLaw : Measure ℝ) x := cdf_nonneg _ _
    have hupper :
        cdf (gaussianReciprocalSquareLaw : Measure ℝ) x ≤
          cdf (gaussianReciprocalSquareLaw : Measure ℝ) 0 :=
      monotone_cdf (gaussianReciprocalSquareLaw : Measure ℝ) hx
    rw [gaussianReciprocalSquareLaw_cdf_zero] at hupper
    rw [exercise1623DistributionFunction_of_nonpos hx]
    linarith
  · let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
    have hx_pos : 0 < x := lt_of_not_ge hx
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    rw [exercise1623DistributionFunction_apply, if_pos hx_pos]
    rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def, gaussianReciprocalSquareLaw,
      ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_apply measurable_realInvSq measurableSet_Iic]
    have hpre :
        (fun z : ℝ ↦ (z⁻¹) ^ (2 : ℕ)) ⁻¹' Set.Iic x =
          ({0} : Set ℝ) ∪ {z : ℝ | 1 / Real.sqrt x ≤ |z|} := by
      -- Proof comment: away from `0`, the reciprocal-square inequality is exactly the two-sided
      -- Gaussian tail event at level `1 / √x`.
      ext z
      by_cases hz : z = 0
      · simp [hz, hx_pos.le]
      · simpa [hz] using (invSq_le_iff_zero_or_le_abs (x := x) (z := z) hx_pos)
    have hdisj :
        Disjoint ({0} : Set ℝ) {z : ℝ | 1 / Real.sqrt x ≤ |z|} := by
      rw [Set.disjoint_singleton_left]
      intro hmem
      have : 1 / Real.sqrt x ≤ (0 : ℝ) := by simpa using hmem
      have hpos : 0 < 1 / Real.sqrt x := by positivity
      linarith
    have hnoAtoms : NoAtoms ν :=
      noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
    rw [hpre, measure_union hdisj (measurableSet_le measurable_const measurable_abs)]
    have hsum :
        (ν ({0} : Set ℝ) + ν {z : ℝ | 1 / Real.sqrt x ≤ |z|}).toReal =
          (ν ({0} : Set ℝ)).toReal + (ν {z : ℝ | 1 / Real.sqrt x ≤ |z|}).toReal := by
      simpa using
        ENNReal.toReal_add (measure_ne_top ν ({0} : Set ℝ))
          (measure_ne_top ν {z : ℝ | 1 / Real.sqrt x ≤ |z|})
    change (ν ({0} : Set ℝ) + ν {z : ℝ | 1 / Real.sqrt x ≤ |z|}).toReal =
      2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x))
    rw [hsum]
    have htail : (ν {z : ℝ | 1 / Real.sqrt x ≤ |z|}).toReal =
        2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) :=
      gaussianAbsTail_real (a := 1 / Real.sqrt x) (by positivity)
    simpa [ν, hnoAtoms.measure_singleton] using htail

/-- Helper for Exercise 16.2.3: mapping additive convolution on `[0, ∞)` along the canonical
inclusion `NNReal → ℝ` commutes with convolution. -/
private lemma map_coeNNRealReal_conv
    (μ ν : ProbabilityMeasure NNReal) :
    ProbabilityMeasure.map (μ * ν) measurable_coe_nnreal_real.aemeasurable =
      ProbabilityMeasure.map μ measurable_coe_nnreal_real.aemeasurable *
        ProbabilityMeasure.map ν measurable_coe_nnreal_real.aemeasurable := by
  -- Proof comment: convert to measures and push convolution through the additive monoid hom
  -- `NNReal.toRealHom`.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [ProbabilityMeasure.toMeasure_mul, ProbabilityMeasure.toMeasure_map] using
    (Measure.map_conv_addMonoidHom
      (μ := (μ : Measure NNReal)) (ν := (ν : Measure NNReal))
      (NNReal.toRealHom : NNReal →+ ℝ) measurable_coe_nnreal_real)

/-- Helper for Exercise 16.2.3: mapping convolution powers on `[0, ∞)` along the canonical
inclusion `NNReal → ℝ` commutes with additive convolution powers. -/
private lemma map_coeNNRealReal_pow
    (μ : ProbabilityMeasure NNReal) :
    ∀ n : ℕ,
      ProbabilityMeasure.map (μ ^ n) measurable_coe_nnreal_real.aemeasurable =
        (ProbabilityMeasure.map μ measurable_coe_nnreal_real.aemeasurable) ^ n
  | 0 => by
      -- Proof comment: the convolution unit `δ₀` is preserved by the canonical inclusion.
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map ((↑) : NNReal → ℝ) (Measure.dirac (0 : NNReal)) = Measure.dirac (0 : ℝ)
      simpa using (Measure.map_dirac' measurable_coe_nnreal_real (0 : NNReal))
  | n + 1 => by
      -- Proof comment: rewrite the successor power as one more convolution and apply the
      -- pushforward-through-convolution bridge from `map_coeNNRealReal_conv`.
      rw [pow_succ, map_coeNNRealReal_conv (μ := μ ^ n) (ν := μ),
        map_coeNNRealReal_pow μ n, pow_succ]

/-- Helper for Exercise 16.2.3: realizing the `NNReal` witness in `ℝ` recovers the explicit
reciprocal-square law. -/
private lemma gaussianReciprocalSquareLaw_eq_map_coeNNRealReal :
    ProbabilityMeasure.map gaussianReciprocalSquareLawNN measurable_coe_nnreal_real.aemeasurable =
      gaussianReciprocalSquareLaw := by
  -- Proof comment: composing `Real.toNNReal` with the inclusion `NNReal → ℝ` collapses back to
  -- the original reciprocal-square map because reciprocal squares are nonnegative.
  apply ProbabilityMeasure.toMeasure_injective
  rw [gaussianReciprocalSquareLawNN, gaussianReciprocalSquareLaw]
  repeat rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_coe_nnreal_real measurable_realToNNRealInvSq]
  congr 1
  ext z
  simpa [Function.comp] using coe_realToNNReal_invSq z

/-- Helper for Exercise 16.2.3: every standard Gaussian upper tail has strictly positive mass. -/
private lemma standardGaussianUpperTail_pos (a : ℝ) :
    0 < (gaussianReal (0 : ℝ) 1) (Set.Ioi a) := by
  -- Proof comment: the nonempty interval `(a, a + 1)` sits inside the upper tail, and Gaussian
  -- measure is absolutely continuous with respect to Lebesgue measure.
  have hgauss_ne : gaussianReal (0 : ℝ) 1 (Set.Ioi a) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo a (a + 1)) = 0 := by
      exact measure_mono_null (by
        intro x hx
        exact hx.1) (gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero)
    have hvol_pos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Ioo a (a + 1)) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol_pos.ne' hvol_zero
  exact bot_lt_iff_ne_bot.mpr hgauss_ne

/-- Helper for Exercise 16.2.3: the standard Gaussian cdf is strictly below `1` at every finite
point. -/
private lemma standardGaussianCdf_lt_one (a : ℝ) :
    cdf (gaussianReal (0 : ℝ) 1) a < 1 := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  have htail_pos : 0 < ν (Set.Ioi a) := by
    simpa [ν] using standardGaussianUpperTail_pos a
  have hsum : ν (Set.Iic a) + ν (Set.Ioi a) = 1 := by
    simpa [ν, Set.compl_Iic] using prob_add_prob_compl (μ := ν) measurableSet_Iic
  have htmp := congrArg ENNReal.toReal hsum
  have hreal : cdf ν a + (ν (Set.Ioi a)).toReal = 1 := by
    simpa [ν, ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def,
      ENNReal.toReal_add, measure_ne_top ν _] using htmp
  have htail_real_pos : 0 < (ν (Set.Ioi a)).toReal := by
    exact ENNReal.toReal_pos htail_pos.ne' (measure_ne_top ν _)
  linarith

/-- Helper for Exercise 16.2.3: the explicit reciprocal-square witness is not a Dirac mass. -/
private lemma gaussianReciprocalSquareLaw_ne_dirac (x : ℝ) :
    gaussianReciprocalSquareLaw ≠ diracProba x := by
  by_cases hx_nonpos : x ≤ 0
  · -- Proof comment: the reciprocal-square law has cdf `0` at `0`, whereas a Dirac mass at a
    -- nonpositive point already has full mass below `0`.
    intro hdirac
    have hdirac_cdf :
        cdf ((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ) 0 = 1 := by
      rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def]
      simpa using congrArg ENNReal.toReal
        (MeasureTheory.diracProba_toMeasure_apply_of_mem
          (x := x) (A := Set.Iic 0) hx_nonpos)
    rw [← hdirac, gaussianReciprocalSquareLaw_cdf_zero] at hdirac_cdf
    norm_num at hdirac_cdf
  · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
    -- Proof comment: below any positive Dirac atom, the Dirac cdf is still `0`, while the
    -- reciprocal-square law has strictly positive mass because the Gaussian tail above the
    -- corresponding threshold is nontrivial.
    intro hdirac
    have hx_half_pos : 0 < x / 2 := by positivity
    have hx_half_lt : x / 2 < x := by linarith
    have hdirac_cdf :
        cdf ((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ) (x / 2) = 0 := by
      rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def]
      have hx_not_mem : x ∉ Set.Iic (x / 2) := by
        simp [not_le.mpr hx_half_lt]
      simpa [hx_not_mem] using
        (MeasureTheory.diracProba_toMeasure_apply'
          x (A := Set.Iic (x / 2)) measurableSet_Iic)
    have hmu_cdf :
        cdf (gaussianReciprocalSquareLaw : Measure ℝ) (x / 2) =
          2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt (x / 2))) := by
      have hEval :=
        congrArg (fun F : StieltjesFunction ℝ ↦ F (x / 2)) gaussianReciprocalSquareLaw_cdf_eq
      simpa [exercise1623DistributionFunction_apply, hx_half_pos] using hEval
    have hmu_pos : 0 < cdf (gaussianReciprocalSquareLaw : Measure ℝ) (x / 2) := by
      rw [hmu_cdf]
      have hcdf_lt :
          cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt (x / 2)) < 1 :=
        standardGaussianCdf_lt_one (1 / Real.sqrt (x / 2))
      linarith
    rw [hdirac] at hmu_pos
    rw [hdirac_cdf] at hmu_pos
    linarith

/-- Helper for Exercise 16.2.3: the Laplace kernel on `[0, ∞)` is integrable against every
probability law. -/
private lemma integrableLaplaceKernel (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    Integrable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ)))) (μ : Measure NNReal) := by
  -- Proof comment: the exponential kernel is bounded by the constant function `1`.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  have hnonneg : 0 ≤ Real.exp (-((t : ℝ) * (x : ℝ))) := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  refine Real.exp_le_one_iff.mpr ?_
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hx : 0 ≤ (x : ℝ) := by exact_mod_cast x.2
  nlinarith

/-- Helper for Exercise 16.2.3: the Laplace integral of a probability law on `[0, ∞)` is strictly
positive. -/
private lemma laplaceIntegral_pos (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    0 < ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) := by
  -- Proof comment: the integrand is everywhere positive and integrable.
  simpa using
    (MeasureTheory.integral_exp_pos
      (μ := (μ : Measure NNReal))
      (f := fun x : NNReal ↦ -((t : ℝ) * (x : ℝ)))
      (integrableLaplaceKernel μ t))

/-- Helper for Exercise 16.2.3: additive convolution on `[0, ∞)` turns the Laplace kernel into a
product. -/
private lemma laplaceIntegral_mul
    (μ ν : ProbabilityMeasure NNReal) (t : NNReal) :
    ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂((μ * ν : ProbabilityMeasure NNReal) : Measure NNReal) =
      (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
        ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
  -- Proof comment: convolution is the pushforward of the product measure under addition, and the
  -- Laplace kernel factorizes across sums.
  rw [ProbabilityMeasure.toMeasure_mul, Measure.conv]
  rw [integral_map_of_stronglyMeasurable measurable_add]
  · calc
      ∫ z : NNReal × NNReal, Real.exp (-((t : ℝ) * ((z.1 + z.2 : NNReal) : ℝ)))
          ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) =
        ∫ z : NNReal × NNReal,
            Real.exp (-((t : ℝ) * (z.1 : ℝ))) * Real.exp (-((t : ℝ) * (z.2 : ℝ)))
            ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
              rcases z with ⟨x, y⟩
              change
                Real.exp (-((t : ℝ) * (((x + y : NNReal) : ℝ)))) =
                  Real.exp (-((t : ℝ) * (x : ℝ))) * Real.exp (-((t : ℝ) * (y : ℝ)))
              rw [show (((x + y : NNReal) : ℝ)) = (x : ℝ) + (y : ℝ) by rfl]
              rw [mul_add, neg_add, Real.exp_add]
      _ = (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
            ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
              simpa using
                (integral_prod_mul
                  (μ := (μ : Measure NNReal))
                  (ν := (ν : Measure NNReal))
                  (f := fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))))
                  (g := fun y : NNReal ↦ Real.exp (-((t : ℝ) * (y : ℝ)))))
  · fun_prop

/-- Helper for Exercise 16.2.3: the canonical `n²` scaling map on `[0, ∞)`. -/
private def nnrealSquareScaleMap (n : ℕ+) : NNReal → NNReal :=
  fun x ↦ ((n : NNReal) ^ (2 : ℕ)) * x

/-- Helper for Exercise 16.2.3: the canonical `n²` scaling map on `[0, ∞)` is measurable. -/
private lemma measurable_nnrealSquareScaleMap (n : ℕ+) :
    Measurable (nnrealSquareScaleMap n) := by
  -- Proof comment: multiplication by the constant `((n : NNReal)^2)` is measurable.
  simpa [nnrealSquareScaleMap] using
    (measurable_const.mul measurable_id)

/-- Helper for Exercise 16.2.3: the scaled `NNReal` witness. -/
private def gaussianReciprocalSquareLawNNScaled (n : ℕ+) : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map gaussianReciprocalSquareLawNN
    (measurable_nnrealSquareScaleMap n).aemeasurable

/-- Helper for Exercise 16.2.3: coercing the `NNReal` square-scaling map to `ℝ` gives real
multiplication by `n²`. -/
private lemma coe_nnrealSquareScaleMap (n : ℕ+) (x : NNReal) :
    ((nnrealSquareScaleMap n x : NNReal) : ℝ) = ((n : ℝ) ^ (2 : ℕ)) * (x : ℝ) := by
  -- Proof comment: all coercions are compatible with multiplication and natural powers.
  simp [nnrealSquareScaleMap]

/-- Helper for Exercise 16.2.3: the square-root normalization for the `n²` scaling parameter. -/
private lemma sqrt_two_mul_nnrealSquareScale (n : ℕ+) (t : NNReal) :
    Real.sqrt (2 * (((nnrealSquareScaleMap n t : NNReal) : ℝ))) =
      (n : ℝ) * Real.sqrt (2 * (t : ℝ)) := by
  -- Proof comment: rewrite the scaled argument as `n² * (2t)` and pull the square root through
  -- the product.
  have hn : 0 ≤ (n : ℝ) := by positivity
  calc
    Real.sqrt (2 * (((nnrealSquareScaleMap n t : NNReal) : ℝ))) =
        Real.sqrt (((n : ℝ) ^ (2 : ℕ)) * (2 * (t : ℝ))) := by
          simp [nnrealSquareScaleMap, pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = Real.sqrt ((n : ℝ) ^ (2 : ℕ)) * Real.sqrt (2 * (t : ℝ)) := by
          simpa using
            Real.sqrt_mul
              (show 0 ≤ ((n : ℝ) ^ (2 : ℕ)) by positivity)
              (show 0 ≤ 2 * (t : ℝ) by positivity)
    _ = (n : ℝ) * Real.sqrt (2 * (t : ℝ)) := by
          rw [show ((n : ℝ) ^ (2 : ℕ)) = (n : ℝ) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
            abs_of_nonneg hn]

/-- Helper for Exercise 16.2.3: rewriting the Laplace integral of the reciprocal-square witness on
`[0, ∞)` reduces it to the positive half-line Gaussian integral. -/
private lemma gaussianReciprocalSquareLawNN_laplaceIntegral_eq_positiveGaussianIntegral
    (t : NNReal) :
    ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(gaussianReciprocalSquareLawNN : Measure NNReal) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        gaussianPDFReal (0 : ℝ) 1 u * Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ))) := by
  -- Proof comment: pull the pushforward integral back to the standard Gaussian, then rewrite the
  -- resulting scalar kernel as a function of `|z|` and fold the even integral to `(0, ∞)`.
  rw [gaussianReciprocalSquareLawNN, ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map measurable_realToNNRealInvSq.aemeasurable (by fun_prop)]
  have hkernel :
      (fun z : ℝ ↦
        Real.exp
          (-((t : ℝ) * (((Real.toNNReal ((z⁻¹) ^ (2 : ℕ)) : NNReal) : ℝ))))) =
        fun z : ℝ ↦ Real.exp (-((t : ℝ) * (z⁻¹) ^ (2 : ℕ))) := by
    funext z
    rw [coe_realToNNReal_invSq]
  rw [hkernel]
  calc
    ∫ z : ℝ, Real.exp (-((t : ℝ) * (z⁻¹) ^ (2 : ℕ))) ∂(gaussianReal (0 : ℝ) 1)
      = ∫ z : ℝ,
          gaussianPDFReal (0 : ℝ) 1 z *
            Real.exp (-((t : ℝ) * (z⁻¹) ^ (2 : ℕ))) := by
          simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
            (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
              (μ := (0 : ℝ)) (v := (1 : NNReal))
              (f := fun z : ℝ ↦ Real.exp (-((t : ℝ) * (z⁻¹) ^ (2 : ℕ))))
              one_ne_zero)
    _ =
        ∫ z : ℝ,
          gaussianPDFReal (0 : ℝ) 1 |z| *
            Real.exp (-((t : ℝ) * (|z|⁻¹) ^ (2 : ℕ))) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
          have hpdf : gaussianPDFReal (0 : ℝ) 1 |z| = gaussianPDFReal (0 : ℝ) 1 z := by
            simp [ProbabilityTheory.gaussianPDFReal_def, pow_two]
          have hinv : (|z|⁻¹) ^ (2 : ℕ) = (z⁻¹) ^ (2 : ℕ) := by
            simpa using (sq_abs (z⁻¹))
          change
            gaussianPDFReal (0 : ℝ) 1 z * Real.exp (-((t : ℝ) * (z⁻¹) ^ (2 : ℕ))) =
              gaussianPDFReal (0 : ℝ) 1 |z| * Real.exp (-((t : ℝ) * (|z|⁻¹) ^ (2 : ℕ)))
          rw [hpdf.symm, hinv]
    _ =
        2 * ∫ u in Set.Ioi (0 : ℝ),
          gaussianPDFReal (0 : ℝ) 1 u * Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ))) := by
          simpa using
            (integral_comp_abs
              (f := fun u : ℝ ↦
                gaussianPDFReal (0 : ℝ) 1 u *
                  Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ)))))

/-- Helper for Exercise 16.2.3: completing the square on the positive kernel extracts the factor
`exp (-c)` and leaves the self-reciprocal Gaussian core. -/
private lemma reciprocalGaussianKernel_completeSquare {u c : ℝ} (hu : 0 < u) :
    Real.exp (-((u ^ (2 : ℕ) + (c / u) ^ (2 : ℕ)) / 2)) =
      Real.exp (-c) * Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
  -- Proof comment: the elementary identity
  -- `u^2 + (c/u)^2 = (u - c/u)^2 + 2c` turns the exponent into a sum, which then splits under
  -- `Real.exp`.
  rw [← Real.exp_add]
  congr 1
  have hu0 : u ≠ 0 := ne_of_gt hu
  field_simp [pow_two, hu0]
  ring

/-- Helper for Exercise 16.2.3: the reciprocal involution `u ↦ c / u` preserves the
self-reciprocal Gaussian kernel on `(0, ∞)`. -/
private lemma reciprocalPositiveKernel_integral_eq_self {c : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi (0 : ℝ),
      (c / u ^ (2 : ℕ)) * Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) =
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
  -- Proof comment: the reciprocal map `u ↦ c / u` is antitone on `(0, ∞)` with Jacobian
  -- `c / u²`, and the Gaussian core is invariant under this involution.
  have hderiv :
      ∀ u ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun x : ℝ ↦ c / x) (-(c / u ^ (2 : ℕ))) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_inv hu0).const_mul c).hasDerivWithinAt :
        HasDerivWithinAt (fun x : ℝ ↦ c * x⁻¹) (c * -(u ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) u)
  have hanti : AntitoneOn (fun u : ℝ ↦ c / u) (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hinv : y⁻¹ ≤ x⁻¹ := inv_antitoneOn_Ioi hx hy hxy
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hinv hc.le)
  have himage : (fun u : ℝ ↦ c / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hc hu
    · intro hy
      have hy0 : 0 < y := hy
      refine ⟨c / y, div_pos hc hy0, ?_⟩
      field_simp [hc.ne', (ne_of_gt hy0)]
  have hsymm :
      ∀ u ∈ Set.Ioi (0 : ℝ),
        Real.exp (-((((c / u) - c / (c / u)) ^ (2 : ℕ)) / 2)) =
          Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hcore : (c / u) - c / (c / u) = -(u - c / u) := by
      have hquot : c / (c / u) = u := by
        field_simp [hc.ne', hu0]
      rw [hquot]
      ring
    rw [hcore, neg_sq]
  calc
    ∫ u in Set.Ioi (0 : ℝ),
        (c / u ^ (2 : ℕ)) * Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) =
      ∫ u in Set.Ioi (0 : ℝ),
        (c / u ^ (2 : ℕ)) * Real.exp (-((((c / u) - c / (c / u)) ^ (2 : ℕ)) / 2)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro u hu
          simpa [mul_assoc] using
            congrArg (fun r : ℝ ↦ (c / u ^ (2 : ℕ)) * r) ((hsymm u hu).symm)
    _ = ∫ x in (fun u : ℝ ↦ c / u) '' Set.Ioi (0 : ℝ),
          Real.exp (-(((x - c / x) ^ (2 : ℕ)) / 2)) := by
            symm
            simpa [smul_eq_mul] using
              (MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitoneOn
                (f := fun u : ℝ ↦ c / u) (f' := fun u ↦ -(c / u ^ (2 : ℕ)))
                (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hderiv hanti
                (fun x : ℝ ↦ Real.exp (-(((x - c / x) ^ (2 : ℕ)) / 2))))
    _ = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
          rw [himage]

/-- Helper for Exercise 16.2.3: the positive quadratic root inverts `u ↦ u - c / u` on
`(0, ∞)`. -/
private lemma subReciprocalPositiveInverse {c y : ℝ} (hc : 0 < c) :
    0 < (y + Real.sqrt (y ^ (2 : ℕ) + 4 * c)) / 2 ∧
      (y + Real.sqrt (y ^ (2 : ℕ) + 4 * c)) / 2 -
          c / ((y + Real.sqrt (y ^ (2 : ℕ) + 4 * c)) / 2) = y := by
  -- Proof comment: the positive root of `u² - yu - c = 0` gives an explicit inverse candidate,
  -- and the quadratic relation recovers `u - c / u = y`.
  let u : ℝ := (y + Real.sqrt (y ^ (2 : ℕ) + 4 * c)) / 2
  have hsqrt_sq :
      (Real.sqrt (y ^ (2 : ℕ) + 4 * c)) ^ (2 : ℕ) = y ^ (2 : ℕ) + 4 * c := by
    rw [Real.sq_sqrt]
    positivity
  have hu_pos : 0 < u := by
    have hsqrt_gt : -y < Real.sqrt (y ^ (2 : ℕ) + 4 * c) := by
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [hc]
    dsimp [u]
    nlinarith
  have hu_quad : u ^ (2 : ℕ) - y * u - c = 0 := by
    dsimp [u]
    nlinarith [hsqrt_sq]
  have hu0 : u ≠ 0 := ne_of_gt hu_pos
  refine ⟨by simpa [u] using hu_pos, ?_⟩
  have hmain : u - c / u = y := by
    field_simp [hu0]
    nlinarith [hu_quad]
  simpa [u] using hmain

/-- Helper for Exercise 16.2.3: the map `u ↦ u - c / u` has derivative `1 + c / u²` on
`(0, ∞)`. -/
private lemma subReciprocal_hasDerivWithinAt {c u : ℝ} (hu : 0 < u) :
    HasDerivWithinAt (fun x : ℝ ↦ x - c / x) (1 + c / u ^ (2 : ℕ)) (Set.Ioi (0 : ℝ)) u := by
  -- Proof comment: differentiate `x ↦ x` and `x ↦ c / x` separately, then simplify the scalar
  -- coefficient.
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hbase :
      HasDerivWithinAt (fun x : ℝ ↦ x - c / x) (1 - c * -(u ^ (2 : ℕ))⁻¹) (Set.Ioi (0 : ℝ)) u := by
    simpa [div_eq_mul_inv] using
      (hasDerivWithinAt_id (s := Set.Ioi (0 : ℝ)) (x := u)).sub
        ((((hasDerivAt_inv hu0).const_mul c).hasDerivWithinAt) :
          HasDerivWithinAt (fun x : ℝ ↦ c * x⁻¹) (c * -(u ^ (2 : ℕ))⁻¹) (Set.Ioi (0 : ℝ)) u)
  have hcoeff : 1 - c * -(u ^ (2 : ℕ))⁻¹ = 1 + c / u ^ (2 : ℕ) := by
    field_simp [pow_two, hu0]
    ring
  exact hcoeff ▸ hbase

/-- Helper for Exercise 16.2.3: the map `u ↦ u - c / u` is strictly increasing on `(0, ∞)`. -/
private lemma subReciprocal_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun u : ℝ ↦ u - c / u) (Set.Ioi (0 : ℝ)) := by
  -- Proof comment: the derivative is strictly positive on the positive half-line, so the map is
  -- strictly monotone there.
  refine
    strictMonoOn_of_hasDerivWithinAt_pos (D := Set.Ioi (0 : ℝ))
      (f := fun u : ℝ ↦ u - c / u) (f' := fun u : ℝ ↦ 1 + c / u ^ (2 : ℕ))
      (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · intro u hu
    exact (subReciprocal_hasDerivWithinAt (c := c) hu).continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by
      simpa using hu
    simpa using subReciprocal_hasDerivWithinAt (c := c) hu'
  · intro u hu
    positivity

/-- Helper for Exercise 16.2.3: the map `u ↦ u - c / u` sends `(0, ∞)` onto all of `ℝ`. -/
private lemma subReciprocal_image_univ {c : ℝ} (hc : 0 < c) :
    (fun u : ℝ ↦ u - c / u) '' Set.Ioi (0 : ℝ) = Set.univ := by
  -- Proof comment: every real target value is hit by the explicit positive inverse from the
  -- quadratic formula.
  ext y
  constructor
  · intro _
    simp
  · intro _
    rcases subReciprocalPositiveInverse (c := c) (y := y) hc with ⟨hypos, hyeq⟩
    exact ⟨(y + Real.sqrt (y ^ (2 : ℕ) + 4 * c)) / 2, hypos, hyeq⟩

/-- Helper for Exercise 16.2.3: the monotone substitution `u ↦ u - c / u` turns the
self-reciprocal kernel into the full Gaussian integral. -/
private lemma subReciprocalGaussian_integral_eq_fullGaussian {c : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi (0 : ℝ),
      (1 + c / u ^ (2 : ℕ)) * Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) =
        Real.sqrt (2 * Real.pi) := by
  -- Route correction: replace the earlier surjectivity-by-limits route with the explicit positive
  -- inverse from `subReciprocalPositiveInverse`, then apply the monotone Jacobian theorem once.
  let core : ℝ → ℝ := fun u ↦ Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2))
  have hgauss :
      ∫ x : ℝ, Real.exp (-((x ^ (2 : ℕ)) / 2)) = Real.sqrt (2 * Real.pi) := by
    calc
      ∫ x : ℝ, Real.exp (-((x ^ (2 : ℕ)) / 2))
          = ∫ x : ℝ, Real.exp (-((1 / 2 : ℝ) * x ^ (2 : ℕ))) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
              congr 1
              ring
      _ = Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
            simpa using integral_gaussian (1 / 2 : ℝ)
      _ = Real.sqrt (2 * Real.pi) := by
            congr 1
            field_simp
  calc
    ∫ u in Set.Ioi (0 : ℝ), (1 + c / u ^ (2 : ℕ)) * core u
        = ∫ x in (fun u : ℝ ↦ u - c / u) '' Set.Ioi (0 : ℝ), Real.exp (-((x ^ (2 : ℕ)) / 2)) := by
            symm
            simpa [core, smul_eq_mul] using
              (MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
                (f := fun u : ℝ ↦ u - c / u) (f' := fun u ↦ 1 + c / u ^ (2 : ℕ))
                (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
                (fun u hu ↦ subReciprocal_hasDerivWithinAt (c := c) hu)
                (subReciprocal_strictMonoOn (c := c) hc).monotoneOn
                (fun x : ℝ ↦ Real.exp (-((x ^ (2 : ℕ)) / 2))))
    _ = ∫ x : ℝ, Real.exp (-((x ^ (2 : ℕ)) / 2)) := by
          simp [subReciprocal_image_univ (c := c) hc]
    _ = Real.sqrt (2 * Real.pi) := hgauss

/-- Helper for Exercise 16.2.3: the self-reciprocal Gaussian core integrates to the positive
half of the full Gaussian mass. -/
private lemma selfReciprocalGaussianKernel_integral_eq_halfGaussian {c : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) =
      Real.sqrt (2 * Real.pi) / 2 := by
  -- Route correction: first prove the full Jacobian kernel is integrable by monotone transport,
  -- then dominate the two summands by it so the linear split is justified.
  let core : ℝ → ℝ := fun u ↦ Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2))
  let reciprocalPart : ℝ → ℝ := fun u ↦ (c / u ^ (2 : ℕ)) * core u
  let weighted : ℝ → ℝ := fun u ↦ (1 + c / u ^ (2 : ℕ)) * core u
  have hgaussInt :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-((x ^ (2 : ℕ)) / 2))) Set.univ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by positivity))
  have hweightedInt : IntegrableOn weighted (Set.Ioi (0 : ℝ)) := by
    have himageInt :
        IntegrableOn (fun x : ℝ ↦ Real.exp (-((x ^ (2 : ℕ)) / 2)))
          ((fun u : ℝ ↦ u - c / u) '' Set.Ioi (0 : ℝ)) := by
      simpa [subReciprocal_image_univ (c := c) hc] using hgaussInt
    exact
      (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        (f := fun u : ℝ ↦ u - c / u) (f' := fun u ↦ 1 + c / u ^ (2 : ℕ))
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
        (fun u hu ↦ subReciprocal_hasDerivWithinAt (c := c) hu)
        (subReciprocal_strictMonoOn (c := c) hc).monotoneOn
        (fun x : ℝ ↦ Real.exp (-((x ^ (2 : ℕ)) / 2)))).1 himageInt
  have hcoreInt : IntegrableOn core (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hweightedInt ?_ ?_
    · fun_prop
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hfactor_nonneg : 0 ≤ c / u ^ (2 : ℕ) := by
        positivity
      have hcore_nonneg : 0 ≤ core u := by
        dsimp [core]
        positivity
      rw [Real.norm_of_nonneg hcore_nonneg]
      dsimp [weighted]
      calc
        core u ≤ (1 + c / u ^ (2 : ℕ)) * core u := by
          nlinarith
        _ = weighted u := by rfl
  have hreciprocalInt : IntegrableOn reciprocalPart (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hweightedInt ?_ ?_
    · fun_prop
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hfactor_nonneg : 0 ≤ c / u ^ (2 : ℕ) := by
        positivity
      have hone_factor : c / u ^ (2 : ℕ) ≤ 1 + c / u ^ (2 : ℕ) := by
        linarith
      have hreciprocal_nonneg : 0 ≤ reciprocalPart u := by
        dsimp [reciprocalPart, core]
        positivity
      have hcore_nonneg : 0 ≤ core u := by
        dsimp [core]
        positivity
      rw [Real.norm_of_nonneg hreciprocal_nonneg]
      dsimp [reciprocalPart, weighted]
      exact mul_le_mul_of_nonneg_right hone_factor hcore_nonneg
  have hsplit :
      ∫ u in Set.Ioi (0 : ℝ), weighted u =
        (∫ u in Set.Ioi (0 : ℝ), core u) + ∫ u in Set.Ioi (0 : ℝ), reciprocalPart u := by
    calc
      ∫ u in Set.Ioi (0 : ℝ), weighted u
          = ∫ u in Set.Ioi (0 : ℝ), core u + reciprocalPart u := by
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro u hu
              dsimp [weighted, reciprocalPart]
              ring
      _ = (∫ u in Set.Ioi (0 : ℝ), core u) + ∫ u in Set.Ioi (0 : ℝ), reciprocalPart u := by
            simpa using integral_add hcoreInt hreciprocalInt
  let I : ℝ := ∫ u in Set.Ioi (0 : ℝ), core u
  have hreciprocalEq :
      ∫ u in Set.Ioi (0 : ℝ), reciprocalPart u = I := by
    simpa [I, reciprocalPart, core] using reciprocalPositiveKernel_integral_eq_self (c := c) hc
  have hweightedEq : ∫ u in Set.Ioi (0 : ℝ), weighted u = 2 * I := by
    calc
      ∫ u in Set.Ioi (0 : ℝ), weighted u
          = I + ∫ u in Set.Ioi (0 : ℝ), reciprocalPart u := by
              simpa [I] using hsplit
      _ = I + I := by rw [hreciprocalEq]
      _ = 2 * I := by ring
  have hfull :
      ∫ u in Set.Ioi (0 : ℝ), weighted u = Real.sqrt (2 * Real.pi) := by
    simpa [weighted, core] using subReciprocalGaussian_integral_eq_fullGaussian (c := c) hc
  have htwo : 2 * I = Real.sqrt (2 * Real.pi) := by
    calc
      2 * I = ∫ u in Set.Ioi (0 : ℝ), weighted u := hweightedEq.symm
      _ = Real.sqrt (2 * Real.pi) := hfull
  have hI : I = Real.sqrt (2 * Real.pi) / 2 := by
    nlinarith
  simpa [I, core] using hI

/-- Helper for Exercise 16.2.3: the `NNReal` witness has Laplace transform `t ↦ exp (-sqrt (2t))`.
-/
private lemma gaussianReciprocalSquareLawNN_laplaceTransform (t : NNReal) :
    ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(gaussianReciprocalSquareLawNN : Measure NNReal) =
      Real.exp (-Real.sqrt (2 * (t : ℝ))) := by
  by_cases ht : t = 0
  · -- Proof comment: at `t = 0`, the Laplace kernel is constantly `1`, so the integral is `1`.
    subst ht
    simp
  · -- Route correction: normalize the Laplace integral to the positive half-line first, then use
    -- the completed-square kernel identity and the half-Gaussian integral value.
    have ht_pos_nn : 0 < t := by
      exact lt_of_le_of_ne t.2 (by
        intro h0
        apply ht
        exact h0.symm)
    have ht_pos : 0 < (t : ℝ) := by
      exact_mod_cast ht_pos_nn
    let c : ℝ := Real.sqrt (2 * (t : ℝ))
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hc_sq : c ^ (2 : ℕ) = 2 * (t : ℝ) := by
      dsimp [c]
      rw [Real.sq_sqrt]
      positivity
    have hkernel :
        ∀ u ∈ Set.Ioi (0 : ℝ),
          gaussianPDFReal (0 : ℝ) 1 u * Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ))) =
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c) *
              Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
      intro u hu
      have hu0 : u ≠ 0 := ne_of_gt hu
      have hsub :
          (t : ℝ) * (u⁻¹) ^ (2 : ℕ) = ((c / u) ^ (2 : ℕ)) / 2 := by
        field_simp [pow_two, hu0]
        nlinarith [hc_sq]
      have hpdf :
          gaussianPDFReal (0 : ℝ) 1 u =
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((u ^ (2 : ℕ)) / 2)) := by
        rw [ProbabilityTheory.gaussianPDFReal_def]
        simp only [sub_zero, NNReal.coe_one, mul_one]
        congr 1
        ring
      calc
        gaussianPDFReal (0 : ℝ) 1 u * Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ)))
            = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((u ^ (2 : ℕ)) / 2))) *
                Real.exp (-(((c / u) ^ (2 : ℕ)) / 2)) := by
                  rw [hpdf]
                  rw [show (Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ)))) =
                    Real.exp (-(((c / u) ^ (2 : ℕ)) / 2)) by rw [hsub]]
        _ = (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-((u ^ (2 : ℕ) + (c / u) ^ (2 : ℕ)) / 2)) := by
                rw [mul_assoc, ← Real.exp_add]
                congr 1
                ring
        _ = (Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.exp (-c) * Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2))) := by
                rw [reciprocalGaussianKernel_completeSquare (c := c) hu]
        _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c) *
              Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
                ring
    calc
      ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(gaussianReciprocalSquareLawNN : Measure NNReal)
          = 2 * ∫ u in Set.Ioi (0 : ℝ),
              gaussianPDFReal (0 : ℝ) 1 u * Real.exp (-((t : ℝ) * (u⁻¹) ^ (2 : ℕ))) := by
                rw [gaussianReciprocalSquareLawNN_laplaceIntegral_eq_positiveGaussianIntegral]
      _ = 2 * ∫ u in Set.Ioi (0 : ℝ),
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c) *
              Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2)) := by
              congr 1
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro u hu
              exact hkernel u hu
      _ = 2 *
            (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c)) *
              ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(((u - c / u) ^ (2 : ℕ)) / 2))) := by
              congr 1
              rw [integral_const_mul]
      _ = 2 * (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c)) *
            (Real.sqrt (2 * Real.pi) / 2)) := by
              rw [selfReciprocalGaussianKernel_integral_eq_halfGaussian (c := c) hc]
      _ = Real.exp (-c) := by
            have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
            field_simp [hsqrt_ne]
      _ = Real.exp (-Real.sqrt (2 * (t : ℝ))) := by
            rfl

/-- Helper for Exercise 16.2.3: convolution powers of the `NNReal` witness scale the Laplace
transform linearly in the exponent. -/
private lemma gaussianReciprocalSquareLawNN_pow_laplaceTransform
    (t : NNReal) :
    ∀ m : ℕ,
      ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ)))
          ∂((gaussianReciprocalSquareLawNN ^ m : ProbabilityMeasure NNReal) : Measure NNReal) =
        Real.exp (-((m : ℝ) * Real.sqrt (2 * (t : ℝ))))
  | 0 => by
      -- Proof comment: the zeroth convolution power is `δ₀`, so the Laplace integral is `1`.
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | m + 1 => by
      -- Proof comment: one more convolution factor multiplies the Laplace transform by the base
      -- transform value, so the exponents add.
      rw [pow_succ, laplaceIntegral_mul, gaussianReciprocalSquareLawNN_pow_laplaceTransform t m,
        gaussianReciprocalSquareLawNN_laplaceTransform]
      rw [← Real.exp_add]
      congr 1
      let r : ℝ := Real.sqrt (2 * (t : ℝ))
      have hsum : -r + -((m : ℝ) * r) = -(r * (m + 1)) := by
        ring
      simpa [r, Nat.cast_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hsum

/-- Helper for Exercise 16.2.3: the `n²`-scaled pushforward of the `NNReal` witness has the same
Laplace transform as the `n`th convolution power. -/
private lemma gaussianReciprocalSquareLawNN_scaled_laplaceTransform
    (n : ℕ+) (t : NNReal) :
    ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ)))
        ∂((gaussianReciprocalSquareLawNNScaled n : ProbabilityMeasure NNReal) : Measure NNReal) =
      Real.exp (-((n : ℝ) * Real.sqrt (2 * (t : ℝ)))) := by
  -- Proof comment: transport the Laplace integral across the `n²` pushforward and normalize the
  -- resulting square root.
  rw [gaussianReciprocalSquareLawNNScaled, ProbabilityMeasure.toMeasure_map]
  rw [integral_map (measurable_nnrealSquareScaleMap n).aemeasurable]
  · -- Proof comment: normalize the scaled exponent so the base Laplace lemma applies.
    have hrewrite :
        (fun x : NNReal ↦ Real.exp (-((t : ℝ) * ((nnrealSquareScaleMap n x : NNReal) : ℝ)))) =
          fun x : NNReal ↦
            Real.exp (-((((nnrealSquareScaleMap n t : NNReal) : ℝ)) * (x : ℝ))) := by
      funext x
      rw [coe_nnrealSquareScaleMap, coe_nnrealSquareScaleMap]
      ring_nf
    rw [hrewrite]
    rw [gaussianReciprocalSquareLawNN_laplaceTransform (nnrealSquareScaleMap n t)]
    rw [sqrt_two_mul_nnrealSquareScale]
  · fun_prop

/-- Helper for Exercise 16.2.3: on `[0, ∞)`, the `n`th convolution power of the witness is the
`n²`-scaled pushforward. -/
private lemma gaussianReciprocalSquareLawNN_pow_eq_map_mulSq
    (n : ℕ+) :
    gaussianReciprocalSquareLawNN ^ (n : ℕ) = gaussianReciprocalSquareLawNNScaled n := by
  -- Proof comment: finite measures on `[0, ∞)` are determined by their Laplace transforms.
  apply ProbabilityMeasure.toMeasure_injective
  have hfinite :
      (gaussianReciprocalSquareLawNN ^ (n : ℕ)).toFiniteMeasure =
        (gaussianReciprocalSquareLawNNScaled n).toFiniteMeasure := by
    refine (MeasureTheory.FiniteMeasure.ext_iff_laplaceTransform_eq _ _).2 ?_
    intro t
    rw [MeasureTheory.FiniteMeasure.laplaceTransform_def,
      MeasureTheory.FiniteMeasure.laplaceTransform_def]
    exact (gaussianReciprocalSquareLawNN_pow_laplaceTransform (t := t) (m := (n : ℕ))).trans
      (gaussianReciprocalSquareLawNN_scaled_laplaceTransform (n := n) (t := t)).symm
  exact congrArg MeasureTheory.FiniteMeasure.toMeasure hfinite

/-- Helper for Exercise 16.2.3: the explicit Gaussian reciprocal-square witness is the correct
stability candidate; the only remaining input is the NNReal Laplace/scaling argument. -/
private lemma gaussianReciprocalSquareLaw_isStableWithIndexHalf :
    IsStableWithIndex gaussianReciprocalSquareLaw (1 / 2 : ℝ) := by
  -- Route correction: the existential theorem is now reduced to the explicit Gaussian witness
  -- `z ↦ z⁻²`, rather than the canonical Stieltjes owner from the cdf.
  refine ⟨gaussianReciprocalSquareLaw_ne_dirac, by norm_num, ?_⟩
  intro n
  -- Proof comment: first close the scaling law on `[0, ∞)` by Laplace-transform uniqueness, then
  -- transport it to `ℝ` through the canonical inclusion `NNReal → ℝ`.
  calc
    gaussianReciprocalSquareLaw ^ (n : ℕ) =
        (ProbabilityMeasure.map gaussianReciprocalSquareLawNN
          measurable_coe_nnreal_real.aemeasurable) ^ (n : ℕ) := by
            rw [gaussianReciprocalSquareLaw_eq_map_coeNNRealReal]
    _ = ProbabilityMeasure.map (gaussianReciprocalSquareLawNN ^ (n : ℕ))
          measurable_coe_nnreal_real.aemeasurable := by
            symm
            exact map_coeNNRealReal_pow gaussianReciprocalSquareLawNN (n : ℕ)
    _ = ProbabilityMeasure.map (gaussianReciprocalSquareLawNNScaled n)
          measurable_coe_nnreal_real.aemeasurable := by
            rw [gaussianReciprocalSquareLawNN_pow_eq_map_mulSq]
    _ = ProbabilityMeasure.map
          (ProbabilityMeasure.map gaussianReciprocalSquareLawNN
            measurable_coe_nnreal_real.aemeasurable)
          (measurable_affineMap ((n : ℝ) ^ (2 : ℕ)) 0).aemeasurable := by
            rw [gaussianReciprocalSquareLawNNScaled]
            apply ProbabilityMeasure.toMeasure_injective
            repeat rw [ProbabilityMeasure.toMeasure_map]
            rw [Measure.map_map measurable_coe_nnreal_real (measurable_nnrealSquareScaleMap n),
              Measure.map_map (measurable_affineMap ((n : ℝ) ^ (2 : ℕ)) 0)
                measurable_coe_nnreal_real]
            congr 1
            ext x
            simp [coe_nnrealSquareScaleMap, mul_assoc, mul_left_comm, mul_comm]
    _ = ProbabilityMeasure.map gaussianReciprocalSquareLaw
          (measurable_affineMap ((n : ℝ) ^ (2 : ℕ)) 0).aemeasurable := by
            rw [gaussianReciprocalSquareLaw_eq_map_coeNNRealReal]
    _ = ProbabilityMeasure.map gaussianReciprocalSquareLaw
          (measurable_affineMap ((n : ℝ) ^ (1 / (1 / 2 : ℝ))) 0).aemeasurable := by
            congr 1
            have hscale : ((n : ℝ) ^ (1 / (1 / 2 : ℝ))) = ((n : ℝ) ^ (2 : ℕ)) := by
              have htwo : (1 / (1 / 2 : ℝ)) = 2 := by
                norm_num
              rw [htwo]
              simpa using (Real.rpow_natCast (n : ℝ) 2)
            ext x
            simp [hscale]

-- Proof sketch: use the hint to identify the law with the positive `1 / 2`-stable law having
-- Laplace transform `λ ↦ exp (-√(2λ))`, then translate strict stability into the displayed
-- convolution-scaling relation.
/-- Exercise 16.2.3 (1): the textbook function
`F(x) = 2 (1 - cdf (gaussianReal 0 1) (x^{-1/2}))` for `x > 0` and `F(x) = 0` for `x ≤ 0`
is the cumulative distribution function of a `1 / 2`-stable probability law on `ℝ`. -/
theorem exists_halfStable_measure_with_exercise1623_distributionFunction
    :
    ∃ μ : ProbabilityMeasure ℝ,
      cdf (μ : Measure ℝ) = exercise1623DistributionFunction ∧
        IsStableWithIndex μ (1 / 2 : ℝ) := by
  -- Proof comment: the theorem now packages the explicit Gaussian reciprocal-square witness, whose
  -- cdf has already been identified with the textbook function `F`.
  refine ⟨gaussianReciprocalSquareLaw, gaussianReciprocalSquareLaw_cdf_eq, ?_⟩
  exact gaussianReciprocalSquareLaw_isStableWithIndexHalf

-- Proof sketch: for the positive `1 / 2`-stable law the first moment is infinite, and the
-- classical heavy-tail law of large numbers implies that the Cesàro averages of an i.i.d.
-- sequence with this law fail to converge almost surely.
/-- Exercise 16.2.3 (2): if `μ` has the distribution function from Exercise 16.2.3 and
`X₀, X₁, …` are i.i.d. with law `μ`, then their Cesàro averages diverge almost surely. -/
theorem iid_exercise1623_partialAverage_ae_diverges
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure ℝ)
    (hμ : cdf (μ : Measure ℝ) = exercise1623DistributionFunction)
    (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_law : ∀ n : ℕ, HasLaw (X n) (μ : Measure ℝ) P) :
    ∀ᵐ ω ∂P, ¬ ∃ x : ℝ,
      Tendsto (fun n : ℕ+ ↦ partialRealSum X n ω / (n : ℝ)) atTop (nhds x) := by
  have hEqμ : (μ : Measure ℝ) = (exercise1623ProbabilityMeasure : Measure ℝ) :=
    measure_eq_exercise1623ProbabilityMeasure μ hμ
  have hμ_nonneg : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    simpa [hEqμ] using exercise1623ProbabilityMeasure_nonneg_ae
  have hμ_notInt : ¬ Integrable id (μ : Measure ℝ) := by
    simpa [hEqμ] using exercise1623FirstMomentInfinite
  have hX_nonneg : ∀ᵐ ω ∂P, ∀ n, 0 ≤ X n ω := by
    rw [ae_all_iff]
    intro n
    exact ((h_law n).ae_iff (p := fun x : ℝ ↦ 0 ≤ x) (by fun_prop)).2 hμ_nonneg
  have htrunc_slln :
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        Tendsto
          (fun n : ℕ+ ↦
            (∑ i ∈ Finset.range (n : ℕ), ProbabilityTheory.truncation (X i) m ω) / (n : ℝ))
          atTop
          (𝓝 (∫ x, ProbabilityTheory.truncation id m x ∂(μ : Measure ℝ))) := by
    intro m
    have htrunc_int :
        Integrable (ProbabilityTheory.truncation (X 0) m) P :=
      (h_law 0).aemeasurable.aestronglyMeasurable.integrable_truncation
    have htrunc_pairwise :
        Pairwise
          (fun i j ↦
            ProbabilityTheory.truncation (X i) m ⟂ᵢ[P] ProbabilityTheory.truncation (X j) m) := by
      intro i j hij
      exact
        (h_indep.indepFun hij).comp
          (measurable_id.indicator measurableSet_Ioc)
          (measurable_id.indicator measurableSet_Ioc)
    have htrunc_ident :
        ∀ i, IdentDistrib (ProbabilityTheory.truncation (X i) m)
          (ProbabilityTheory.truncation (X 0) m) P P := by
      intro i
      exact (HasLaw.identDistrib (h_law i) (h_law 0)).truncation
    have htrunc_integral_eq :
        ∫ ω, ProbabilityTheory.truncation (X 0) m ω ∂P =
          ∫ x, ProbabilityTheory.truncation id m x ∂(μ : Measure ℝ) := by
      simpa [ProbabilityTheory.truncation, Function.comp_def] using
        (h_law 0).integral_comp
          (f := ProbabilityTheory.truncation id m)
          (aestronglyMeasurable_id.truncation)
    have hnat :
        ∀ᵐ ω ∂P,
          Tendsto
            (fun n : ℕ ↦
              (∑ i ∈ Finset.range n, ProbabilityTheory.truncation (X i) m ω) / n)
            atTop
            (𝓝 (∫ x, ProbabilityTheory.truncation id m x ∂(μ : Measure ℝ))) := by
      -- Proof comment: bounded truncations are integrable, so the strong law applies to them.
      simpa [htrunc_integral_eq] using
        ProbabilityTheory.strong_law_ae_real
          (fun i ↦ ProbabilityTheory.truncation (X i) m) htrunc_int htrunc_pairwise htrunc_ident
    filter_upwards [hnat] with ω hω
    exact (PNat.tendsto_comp_val_iff).2 hω
  have hall_trunc :
      ∀ᵐ ω ∂P, ∀ m : ℕ,
        Tendsto
          (fun n : ℕ+ ↦
            (∑ i ∈ Finset.range (n : ℕ), ProbabilityTheory.truncation (X i) m ω) / (n : ℝ))
          atTop
          (𝓝 (∫ x, ProbabilityTheory.truncation id m x ∂(μ : Measure ℝ))) := by
    rw [ae_all_iff]
    intro m
    exact htrunc_slln m
  filter_upwards [hall_trunc, hX_nonneg] with ω hωtrunc hωnonneg
  intro hconv
  rcases hconv with ⟨x, hx⟩
  have hseq_nonneg :
      ∀ n : ℕ+, 0 ≤ partialRealSum X n ω / (n : ℝ) := by
    intro n
    have hsum_nonneg : 0 ≤ partialRealSum X n ω := by
      -- Proof comment: on the chosen full-measure event, every summand is nonnegative.
      unfold partialRealSum
      exact Finset.sum_nonneg fun i hi ↦ hωnonneg i
    exact div_nonneg hsum_nonneg (by positivity)
  have hx_nonneg : 0 ≤ x := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hx (Filter.Eventually.of_forall hseq_nonneg)
  have hbound :
      ∀ m : ℕ, ∫ y, ProbabilityTheory.truncation id m y ∂(μ : Measure ℝ) ≤ x := by
    intro m
    have hpointwise :
        ∀ n : ℕ+,
          (∑ i ∈ Finset.range (n : ℕ), ProbabilityTheory.truncation (X i) m ω) / (n : ℝ) ≤
            partialRealSum X n ω / (n : ℝ) := by
      intro n
      have hsum_le :
          ∑ i ∈ Finset.range (n : ℕ), ProbabilityTheory.truncation (X i) m ω ≤
            partialRealSum X n ω := by
        unfold partialRealSum
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hXi_nonneg : 0 ≤ X i ω := hωnonneg i
        calc
          ProbabilityTheory.truncation (X i) m ω ≤
              |ProbabilityTheory.truncation (X i) m ω| := le_abs_self _
          _ ≤ |X i ω| := ProbabilityTheory.abs_truncation_le_abs_self _ _ _
          _ = X i ω := abs_of_nonneg hXi_nonneg
      exact div_le_div_of_nonneg_right hsum_le (by positivity : 0 ≤ (n : ℝ))
    exact le_of_tendsto_of_tendsto (hωtrunc m) hx (Filter.Eventually.of_forall hpointwise)
  have hInt :
      Integrable id (μ : Measure ℝ) :=
    integrable_id_of_nonneg_of_boundedTruncationIntegrals hμ_nonneg x hbound
  exact hμ_notInt hInt
