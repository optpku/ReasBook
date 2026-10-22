/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_59

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology

/-- A real sub-probability measure is a Borel measure on `ℝ` with total mass at most `1`. -/
class IsSubProbabilityMeasure (μ : Measure ℝ) : Prop where
  measure_univ_le_one : μ Set.univ ≤ 1

/-- A real measure is sub-probability exactly when its total mass is at most `1`. -/
theorem isSubProbabilityMeasure_iff (μ : Measure ℝ) :
    IsSubProbabilityMeasure μ ↔ μ Set.univ ≤ 1 := by
  constructor
  · intro hμ
    exact hμ.measure_univ_le_one
  · intro hμ
    exact ⟨hμ⟩

instance (μ : Measure ℝ) [IsSubProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt IsSubProbabilityMeasure.measure_univ_le_one ENNReal.one_lt_top⟩

/-- For a finite real measure, the cumulative mass function `x ↦ μ.real (Set.Iic x)` is monotone.
-/
theorem measureDistributionFunction_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (fun x : ℝ ↦ μ.real (Set.Iic x)) := by
  intro a b hab
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hab)

/-- The distribution function attached to a finite real measure, viewed as a Stieltjes function.
-/
noncomputable def measureDistributionFunction (μ : Measure ℝ) [IsFiniteMeasure μ] :
    StieltjesFunction ℝ :=
  (measureDistributionFunction_monotone μ).stieltjesFunction

/-- Helper for Theorem 1.60: the cumulative mass function of a finite real measure is
right-continuous on `ℝ`. -/
theorem tendsto_measureReal_Iic_nhdsGT (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Tendsto (fun y : ℝ ↦ μ.real (Set.Iic y)) (𝓝[>] x) (𝓝 (μ.real (Set.Iic x))) := by
  -- Re-index the right neighborhood by the subtype `Ioi x`, so continuity from above applies
  -- directly to the decreasing family of rays `Iic y`.
  have h_measure_sub :
      Tendsto (fun y : Set.Ioi x => μ (Set.Iic (y : ℝ))) atBot
        (𝓝 (μ (⋂ y : Set.Ioi x, Set.Iic (y : ℝ)))) := by
    refine tendsto_measure_iInter_atBot (μ := μ)
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Set.Iic_subset_Iic.mpr hab
    · refine ⟨⟨x + 1, lt_add_of_pos_right x zero_lt_one⟩, measure_ne_top μ _⟩
  have h_inter : (⋂ y : Set.Ioi x, Set.Iic (y : ℝ)) = Set.Iic x := by
    -- Intersecting all right-shifted rays recovers the original closed ray.
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iInter, Set.mem_Iic] at hz ⊢
      by_contra hzx
      have hzx' : x < z := lt_of_not_ge hzx
      obtain ⟨y, hxy, hyz⟩ := exists_between hzx'
      exact not_le_of_gt hyz (hz ⟨y, hxy⟩)
    · intro hz
      simp only [Set.mem_iInter, Set.mem_Iic] at hz ⊢
      intro y
      exact hz.trans y.2.le
  have h_real_sub :
      Tendsto (fun y : Set.Ioi x => μ.real (Set.Iic (y : ℝ))) atBot
        (𝓝 (μ.real (Set.Iic x))) := by
    -- After identifying the intersection, pass from `μ` to `μ.real` via `ENNReal.toReal`.
    rw [h_inter] at h_measure_sub
    simpa [measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top μ (Set.Iic x))).comp h_measure_sub
  simpa using
    (tendsto_comp_coe_Ioi_atBot (f := fun y : ℝ ↦ μ.real (Set.Iic y)) (a := x)).1 h_real_sub

/-- Helper for Theorem 1.60: the cumulative mass function of a finite real measure tends to `0`
at `-∞`. -/
theorem tendsto_measureReal_Iic_atBot (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun x : ℝ ↦ μ.real (Set.Iic x)) atBot (𝓝 0) := by
  -- Continuity from above identifies the limit with the measure of the total intersection.
  have h_measure :
      Tendsto (fun x : ℝ ↦ μ (Set.Iic x)) atBot (𝓝 (μ (⋂ y : ℝ, Set.Iic y))) := by
    refine tendsto_measure_iInter_atBot (μ := μ)
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Set.Iic_subset_Iic.mpr hab
    · exact ⟨0, measure_ne_top μ _⟩
  have h_inter : (⋂ y : ℝ, Set.Iic y) = (∅ : Set ℝ) := by
    -- No real number lies below every real number.
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iInter, Set.mem_Iic] at hz
      have h_not : ¬ z ≤ z - 1 := by linarith
      exact h_not (hz (z - 1))
    · intro hz
      simp at hz
  rw [h_inter, measure_empty] at h_measure
  -- Passing to `μ.real` turns the `ENNReal` limit `0` into the real limit `0`.
  simpa [measureReal_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_measure

-- Proof sketch: identify the right-limit regularization defining `measureDistributionFunction`
-- with the actual cumulative mass function `x ↦ μ.real (Set.Iic x)` using right-continuity from
-- above for the finite measure of the rays `Set.Iic x`.
/-- The distribution function attached to a finite real measure evaluates to the cumulative mass
`μ (-∞, x]`, encoded as `μ.real (Set.Iic x)`. -/
theorem measureDistributionFunction_apply (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    measureDistributionFunction μ x = μ.real (Set.Iic x) := by
  -- The Stieltjes regularization agrees with the original cumulative mass function because that
  -- function is already right-continuous.
  rw [measureDistributionFunction, Monotone.stieltjesFunction_eq]
  have h_neBot : (𝓝[>] x) ≠ ⊥ := (show (𝓝[>] x).NeBot from inferInstance).ne
  exact rightLim_eq_of_tendsto h_neBot (tendsto_measureReal_Iic_nhdsGT μ x)

/-- For a real probability measure, the finite-measure distribution function agrees with the
canonical cdf. -/
theorem cdf_eq_measureDistributionFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityTheory.cdf μ = measureDistributionFunction μ := by
  ext x
  rw [measureDistributionFunction_apply, ProbabilityTheory.cdf_eq_real]

/-- The distribution function attached to a real probability measure is a distribution function. -/
instance instIsDistributionFunction_measureDistributionFunction (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsDistributionFunction (measureDistributionFunction μ) := by
  rw [← cdf_eq_measureDistributionFunction μ]
  infer_instance

/-- The distribution function attached to a real sub-probability measure is defective. -/
instance instIsDefectiveDistributionFunction_measureDistributionFunction (μ : Measure ℝ)
    [IsSubProbabilityMeasure μ] :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) := by
  constructor
  · intro x
    -- The cumulative mass of a measurable set is nonnegative.
    rw [measureDistributionFunction_apply]
    exact measureReal_nonneg
  · intro x
    -- Every ray `Iic x` sits inside `univ`, so its mass is bounded by the total mass.
    rw [measureDistributionFunction_apply]
    calc
      μ.real (Set.Iic x) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ 1 := by
        rw [measureReal_def]
        have hμ_le : μ Set.univ ≤ ENNReal.ofReal (1 : ℝ) := by
          simpa using (IsSubProbabilityMeasure.measure_univ_le_one (μ := μ))
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one hμ_le
  · -- The mass of `Iic x` vanishes as `x → -∞`.
    convert tendsto_measureReal_Iic_atBot μ using 1
    ext x
    exact measureDistributionFunction_apply μ x

/-- A real sub-probability measure gives rise to a defective distribution function. -/
theorem isDefectiveDistributionFunction_measureDistributionFunction
    (μ : Measure ℝ) (hμ : IsSubProbabilityMeasure μ) :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) := by
  letI : IsSubProbabilityMeasure μ := hμ
  infer_instance

/-- Helper for Theorem 1.60: a sub-probability measure on `ℝ` is finite. -/
theorem isFiniteMeasure_of_subProbabilityMeasure (μ : Measure ℝ) (hμ : IsSubProbabilityMeasure μ) :
    IsFiniteMeasure μ := by
  letI : IsSubProbabilityMeasure μ := hμ
  infer_instance

/-- Helper for Theorem 1.60: the Lebesgue--Stieltjes measure of a defective distribution function
is finite. -/
theorem isFiniteMeasure_measure_of_defectiveDistributionFunction
    (F : StieltjesFunction ℝ) (hF : IsDefectiveDistributionFunction F) :
    IsFiniteMeasure F.measure := by
  letI : IsDefectiveDistributionFunction F := hF
  infer_instance

/-- Helper for Theorem 1.60: the distribution function attached to a sub-probability measure,
with finiteness supplied explicitly. -/
noncomputable abbrev subProbabilityMeasureDistributionFunction
    (μ : {μ : Measure ℝ // IsSubProbabilityMeasure μ}) : StieltjesFunction ℝ :=
  @measureDistributionFunction μ.1 (isFiniteMeasure_of_subProbabilityMeasure μ.1 μ.2)

/-- Helper for Theorem 1.60: the distribution function attached to the
Lebesgue--Stieltjes measure of a defective distribution function. -/
noncomputable abbrev defectiveDistributionMeasureDistributionFunction
    (F : {F : StieltjesFunction ℝ // IsDefectiveDistributionFunction F}) : StieltjesFunction ℝ :=
  @measureDistributionFunction F.1.measure
    (isFiniteMeasure_measure_of_defectiveDistributionFunction F.1 F.2)

/-- Helper for Theorem 1.60: the distribution function attached to a sub-probability measure is
defective. -/
theorem isDefectiveDistributionFunction_subProbabilityMeasureDistributionFunction
    (μ : {μ : Measure ℝ // IsSubProbabilityMeasure μ}) :
    IsDefectiveDistributionFunction (subProbabilityMeasureDistributionFunction μ) := by
  simpa [subProbabilityMeasureDistributionFunction] using
    (isDefectiveDistributionFunction_measureDistributionFunction μ.1 μ.2)

/-- Helper for Theorem 1.60: the Lebesgue--Stieltjes measure of a defective distribution function
has total mass at most `1`. -/
theorem measure_isSubProbabilityMeasure_of_defectiveDistributionFunction
    {F : StieltjesFunction ℝ} (hF : IsDefectiveDistributionFunction F) :
    IsSubProbabilityMeasure F.measure := by
  -- The total mass is the increment between the limits at `+∞` and `-∞`.
  let s : Set ℝ := Set.range fun x : ℝ ↦ (F x : ℝ)
  have h_bdd : BddAbove s := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hF.le_one x
  have hs_nonempty : s.Nonempty := ⟨F 0, ⟨0, rfl⟩⟩
  have h_top : Tendsto F atTop (𝓝 (sSup s)) :=
    tendsto_atTop_ciSup F.mono h_bdd
  have hsSup_le_one : sSup s ≤ 1 := by
    exact csSup_le hs_nonempty fun _ h ↦ by
      rcases h with ⟨x, rfl⟩
      exact hF.le_one x
  refine ⟨?_⟩
  calc
    F.measure Set.univ = ENNReal.ofReal (sSup s) := by
      simpa using StieltjesFunction.measure_univ F hF.tendsto_atBot_zero h_top
    _ ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hsSup_le_one
    _ = 1 := by simp

/-- Helper for Theorem 1.60: the distribution function attached to the
Lebesgue--Stieltjes measure of a defective distribution function is defective. -/
theorem isDefectiveDistributionFunction_defectiveDistributionMeasureDistributionFunction
    (F : {F : StieltjesFunction ℝ // IsDefectiveDistributionFunction F}) :
    IsDefectiveDistributionFunction (defectiveDistributionMeasureDistributionFunction F) := by
  simpa [defectiveDistributionMeasureDistributionFunction] using
    (isDefectiveDistributionFunction_measureDistributionFunction F.1.measure
      (measure_isSubProbabilityMeasure_of_defectiveDistributionFunction F.2))

/-- Probability measures on `ℝ` are in bijection with distribution functions via the canonical
cdf and Lebesgue--Stieltjes measure. -/
noncomputable def probabilityMeasureEquivDistributionFunction :
    ProbabilityMeasure ℝ ≃ {F : StieltjesFunction ℝ // IsDistributionFunction F} where
  toFun μ := ⟨cdf μ, inferInstance⟩
  invFun F := ⟨F.1.measure,
    F.1.isProbabilityMeasure
      F.2.toIsDefectiveDistributionFunction.tendsto_atBot_zero
      F.2.tendsto_atTop_one⟩
  left_inv μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa using measure_cdf (μ : Measure ℝ)
  right_inv F := by
    apply Subtype.ext
    simpa using
      cdf_measure_stieltjesFunction F.1
        F.2.toIsDefectiveDistributionFunction.tendsto_atBot_zero
        F.2.tendsto_atTop_one

/-- Helper for Theorem 1.60: reconstructing the Lebesgue--Stieltjes measure of
`measureDistributionFunction μ` gives back the original sub-probability measure `μ`. -/
theorem subProbabilityMeasureEquivDefectiveDistributionFunction_left_inv
    (μ : {μ : Measure ℝ // IsSubProbabilityMeasure μ}) :
    ⟨(subProbabilityMeasureDistributionFunction μ).measure,
      measure_isSubProbabilityMeasure_of_defectiveDistributionFunction
        (isDefectiveDistributionFunction_subProbabilityMeasureDistributionFunction μ)⟩ = μ := by
  let ν : Measure ℝ :=
    (@measureDistributionFunction μ.1
      (isFiniteMeasure_of_subProbabilityMeasure μ.1 μ.2)).measure
  have hμF : IsDefectiveDistributionFunction (subProbabilityMeasureDistributionFunction μ) :=
    isDefectiveDistributionFunction_subProbabilityMeasureDistributionFunction μ
  letI : IsFiniteMeasure μ.1 := isFiniteMeasure_of_subProbabilityMeasure μ.1 μ.2
  letI : IsFiniteMeasure ν := by
    simpa [ν, subProbabilityMeasureDistributionFunction] using
      isFiniteMeasure_measure_of_defectiveDistributionFunction
        (subProbabilityMeasureDistributionFunction μ) hμF
  apply Subtype.ext
  -- Equality of finite measures is reduced to equality on all rays `Iic a`.
  refine Measure.ext_of_Iic ν μ.1 ?_
  intro a
  change (@measureDistributionFunction μ.1
      (isFiniteMeasure_of_subProbabilityMeasure μ.1 μ.2)).measure (Set.Iic a) = μ.1 (Set.Iic a)
  rw [StieltjesFunction.measure_Iic _ hμF.tendsto_atBot_zero, sub_zero,
    @measureDistributionFunction_apply μ.1
      (isFiniteMeasure_of_subProbabilityMeasure μ.1 μ.2) a]
  rw [measureReal_def]
  exact ENNReal.ofReal_toReal (measure_ne_top μ.1 (Set.Iic a))

/-- Helper for Theorem 1.60: applying `measureDistributionFunction` to the
Lebesgue--Stieltjes measure of a defective distribution function recovers that function. -/
theorem subProbabilityMeasureEquivDefectiveDistributionFunction_right_inv
    (F : {F : StieltjesFunction ℝ // IsDefectiveDistributionFunction F}) :
    ⟨defectiveDistributionMeasureDistributionFunction F,
      isDefectiveDistributionFunction_defectiveDistributionMeasureDistributionFunction F⟩ = F := by
  apply Subtype.ext
  ext x
  -- Compute the reconstructed cumulative mass on `Iic x` and simplify it back to `F x`.
  simpa [defectiveDistributionMeasureDistributionFunction, measureReal_def] using
    (show @measureDistributionFunction F.1.measure
        (isFiniteMeasure_measure_of_defectiveDistributionFunction F.1 F.2) x = F.1 x by
      rw [measureDistributionFunction_apply, measureReal_def,
        StieltjesFunction.measure_Iic _ F.2.tendsto_atBot_zero, sub_zero,
        ENNReal.toReal_ofReal (F.2.nonneg x)])

/-- Real sub-probability measures are in bijection with defective distribution functions via the
finite-measure cdf and Lebesgue--Stieltjes measure. -/
noncomputable def subProbabilityMeasureEquivDefectiveDistributionFunction :
    {μ : Measure ℝ // IsSubProbabilityMeasure μ} ≃
      {F : StieltjesFunction ℝ // IsDefectiveDistributionFunction F} where
  toFun μ := ⟨subProbabilityMeasureDistributionFunction μ,
    isDefectiveDistributionFunction_subProbabilityMeasureDistributionFunction μ⟩
  invFun F := ⟨F.1.measure, measure_isSubProbabilityMeasure_of_defectiveDistributionFunction F.2⟩
  left_inv := subProbabilityMeasureEquivDefectiveDistributionFunction_left_inv
  right_inv := subProbabilityMeasureEquivDefectiveDistributionFunction_right_inv

-- Proof sketch: for probability measures, use the canonical cdf/Stieltjes correspondence in
-- mathlib together with `cdf_eq_measureDistributionFunction`; for sub-probability measures, the
-- same cumulative-mass construction lands in `IsDefectiveDistributionFunction`, and
-- `StieltjesFunction.measure` reconstructs the original measure.
/-- Theorem 1.60: The assignment `μ ↦ F_μ` is a bijection from probability measures on
`(ℝ, 𝓑(ℝ))` to distribution functions, and from sub-probability measures to defective
distribution functions. -/
theorem measureDistributionFunction_bijective :
    Function.Bijective probabilityMeasureEquivDistributionFunction ∧
      Function.Bijective subProbabilityMeasureEquivDefectiveDistributionFunction := by
  exact ⟨probabilityMeasureEquivDistributionFunction.bijective,
    subProbabilityMeasureEquivDefectiveDistributionFunction.bijective⟩
