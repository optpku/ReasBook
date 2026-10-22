/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Order.Basic
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_44
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_53

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityMeasure Set
open MeasurableEquiv

open scoped Topology ENNReal

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ`, viewed as a
map to `[0,1]`. -/
noncomputable def bivariateMeasureDistributionFunction
    (μ : ProbabilityMeasure (ℝ × ℝ)) : ℝ × ℝ → Icc (0 : ℝ) 1 :=
  fun x ↦ ⟨μ.toMeasure.real (Iic x), measureReal_nonneg, measureReal_le_one⟩

/-- The coercion of the bivariate distribution function back to `ℝ` is the lower-orthant mass
`μ (-∞, x₁] × (-∞, x₂]`. -/
@[simp] theorem bivariateMeasureDistributionFunction_apply
    (μ : ProbabilityMeasure (ℝ × ℝ)) (x : ℝ × ℝ) :
    (bivariateMeasureDistributionFunction μ x : ℝ) = μ (Iic x) := by
  -- This is just the coercion of the subtype-valued definition back to `ℝ`.
  rfl

/-- The source-facing conditions in Exercise 1.5.4 for a bivariate distribution function on
`ℝ²`: monotonicity, right continuity from the upper-right orthant, the diagonal limits
`F (-x) → 0` and `F x → 1` as `x → ∞` in the product order on `ℝ²`, and nonnegative rectangle
increments. -/
class IsBivariateDistributionFunctionCore (F : ℝ × ℝ → Icc (0 : ℝ) 1) : Prop where
  monotone : Monotone F
  right_continuous : ∀ x : ℝ × ℝ, ContinuousWithinAt (fun y ↦ (F y : ℝ)) (Ici x) x
  tendsto_neg_atTop_zero :
    Tendsto (fun x : ℝ × ℝ ↦ (F (-x.1, -x.2) : ℝ)) atTop (𝓝 0)
  tendsto_atTop_one : Tendsto (fun x : ℝ × ℝ ↦ (F x : ℝ)) atTop (𝓝 1)
  rectangle_nonneg : ∀ ⦃x1 y1 x2 y2 : ℝ⦄, x1 ≤ y1 → x2 ≤ y2 →
    0 ≤ (F (y1, y2) : ℝ) - F (y1, x2) - F (x1, y2) + F (x1, x2)

/-- A strengthened helper package for bivariate distribution functions on `ℝ²`: besides the
source-facing conditions from `IsBivariateDistributionFunctionCore`, it also records the two
fixed-coordinate lower-tail limits used by the internal construction API. -/
class IsBivariateDistributionFunction (F : ℝ × ℝ → Icc (0 : ℝ) 1) : Prop
    extends IsBivariateDistributionFunctionCore F where
  tendsto_fst_atBot_zero : ∀ y : ℝ, Tendsto (fun x : ℝ ↦ (F (x, y) : ℝ)) atBot (𝓝 0)
  tendsto_snd_atBot_zero : ∀ x : ℝ, Tendsto (fun y : ℝ ↦ (F (x, y) : ℝ)) atBot (𝓝 0)

/-- Helper for Exercise 1.5.4: intersecting the diagonal family of lower orthants above `x`
recovers the original lower orthant `Set.Iic x`. -/
private theorem iInter_diagonalLowerOrthants_eq (x : ℝ × ℝ) :
    (⋂ r > (0 : ℝ), Set.Iic (x.1 + r, x.2 + r)) = Set.Iic x := by
  -- Membership in every larger diagonal lower orthant is equivalent to staying below `x`
  -- coordinatewise.
  ext y
  constructor
  · intro hy
    simp only [Set.mem_iInter, Set.mem_Iic] at hy ⊢
    constructor
    · by_contra hxy
      have hpos : 0 < y.1 - x.1 := sub_pos.mpr <| lt_of_not_ge hxy
      have hhalf : 0 < (y.1 - x.1) / 2 := by linarith
      have hy' : y.1 ≤ x.1 + (y.1 - x.1) / 2 := (hy _ hhalf).1
      linarith
    · by_contra hxy
      have hpos : 0 < y.2 - x.2 := sub_pos.mpr <| lt_of_not_ge hxy
      have hhalf : 0 < (y.2 - x.2) / 2 := by linarith
      have hy' : y.2 ≤ x.2 + (y.2 - x.2) / 2 := (hy _ hhalf).2
      linarith
  · intro hy
    simp only [Set.mem_iInter, Set.mem_Iic] at hy ⊢
    intro r hr
    exact ⟨le_trans hy.1 <| le_add_of_nonneg_right hr.le,
      le_trans hy.2 <| le_add_of_nonneg_right hr.le⟩

/-- Helper for Exercise 1.5.4: the diagonal lower-orthant masses of a probability measure are
right-continuous. -/
private theorem tendsto_measureReal_diagonalLowerOrthant_nhdsGT
    (μ : ProbabilityMeasure (ℝ × ℝ)) (x : ℝ × ℝ) :
    Tendsto (fun t : ℝ ↦ μ.toMeasure.real (Set.Iic (x.1 + t, x.2 + t))) (𝓝[>] 0)
      (𝓝 (μ.toMeasure.real (Set.Iic x))) := by
  -- Apply continuity from above to the exact diagonal family `r ↦ Set.Iic (x + (r, r))`.
  have hμ :
      Tendsto (fun t : ℝ ↦ μ.toMeasure (Set.Iic (x.1 + t, x.2 + t))) (𝓝[>] 0)
        (𝓝 (μ.toMeasure (⋂ r > (0 : ℝ), Set.Iic (x.1 + r, x.2 + r)))) := by
    refine tendsto_measure_biInter_gt
      (fun _ _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro r s hr hrs
      exact Set.Iic_subset_Iic.mpr ⟨by linarith, by linarith⟩
    · exact ⟨1, zero_lt_one, measure_ne_top _ _⟩
  -- Identify the intersection with the target lower orthant and pass from `ENNReal` to `ℝ`.
  rw [iInter_diagonalLowerOrthants_eq] at hμ
  simpa [measureReal_def] using
    (ENNReal.tendsto_toReal (measure_ne_top μ.toMeasure (Set.Iic x))).comp hμ

/-- Helper for Exercise 1.5.4: for a probability measure on `ℝ × ℝ`, the lower-orthant mass
vanishes when the first coordinate tends to `-∞` and the second coordinate is fixed. -/
private theorem tendsto_measureReal_fstNegLowerOrthant_atTop
    (μ : ProbabilityMeasure (ℝ × ℝ)) (y : ℝ) :
    Tendsto (fun x : ℝ ↦ μ.toMeasure.real (Set.Iic (-x, y))) atTop (𝓝 0) := by
  -- These lower orthants decrease to the empty set as the first coordinate goes to `-∞`.
  have hempty : (⋂ x : ℝ, Set.Iic (-x, y)) = (∅ : Set (ℝ × ℝ)) := by
    ext z
    simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hz' : z.1 ≤ -(-z.1 + 1) := (hz (-z.1 + 1)).1
    linarith
  have hμ :
      Tendsto (fun x : ℝ ↦ μ.toMeasure (Set.Iic (-x, y))) atTop
        (𝓝 (μ.toMeasure (⋂ x : ℝ, Set.Iic (-x, y)))) := by
    refine tendsto_measure_iInter_atTop
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Iic_subset_Iic.mpr ⟨neg_le_neg hab, le_rfl⟩
    · exact ⟨0, measure_ne_top _ _⟩
  have hμ0 : Tendsto (fun x : ℝ ↦ μ.toMeasure (Set.Iic (-x, y))) atTop (𝓝 0) := by
    simpa [hempty] using hμ
  -- Convert the limit from `ENNReal` to the real-valued mass.
  exact ((ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hμ0).congr' <| by
    filter_upwards with x
    rfl

/-- Helper for Exercise 1.5.4: for a probability measure on `ℝ × ℝ`, the lower-orthant mass
vanishes when the second coordinate tends to `-∞` and the first coordinate is fixed. -/
private theorem tendsto_measureReal_sndNegLowerOrthant_atTop
    (μ : ProbabilityMeasure (ℝ × ℝ)) (x : ℝ) :
    Tendsto (fun y : ℝ ↦ μ.toMeasure.real (Set.Iic (x, -y))) atTop (𝓝 0) := by
  -- This is the same continuity-from-above argument in the second coordinate.
  have hempty : (⋂ y : ℝ, Set.Iic (x, -y)) = (∅ : Set (ℝ × ℝ)) := by
    ext z
    simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hz' : z.2 ≤ -(-z.2 + 1) := (hz (-z.2 + 1)).2
    linarith
  have hμ :
      Tendsto (fun y : ℝ ↦ μ.toMeasure (Set.Iic (x, -y))) atTop
        (𝓝 (μ.toMeasure (⋂ y : ℝ, Set.Iic (x, -y)))) := by
    refine tendsto_measure_iInter_atTop
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ?_ ?_
    · intro a b hab
      exact Iic_subset_Iic.mpr ⟨le_rfl, neg_le_neg hab⟩
    · exact ⟨0, measure_ne_top _ _⟩
  have hμ0 : Tendsto (fun y : ℝ ↦ μ.toMeasure (Set.Iic (x, -y))) atTop (𝓝 0) := by
    simpa [hempty] using hμ
  -- Convert the limit from `ENNReal` to the real-valued mass.
  exact ((ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hμ0).congr' <| by
    filter_upwards with y
    rfl

/-- Helper for Exercise 1.5.4: `finTwoArrow.symm` is almost everywhere measurable. -/
private theorem aemeasurable_finTwoArrow_symm (μ : ProbabilityMeasure (ℝ × ℝ)) :
    AEMeasurable (finTwoArrow.symm : ℝ × ℝ → Fin 2 → ℝ) μ :=
  Measurable.aemeasurable finTwoArrow.symm.measurable

/-- Helper for Exercise 1.5.4: pushing a bivariate law through
`MeasurableEquiv.finTwoArrow.symm` rewrites the `Fin 2` lower orthant as the corresponding pair
lower orthant. -/
theorem finTwoLowerOrthantMap_apply (μ : ProbabilityMeasure (ℝ × ℝ)) (z : Fin 2 → ℝ) :
    (map μ (aemeasurable_finTwoArrow_symm μ)) (Iic z) = μ (Iic (z 0, z 1)) := by
  -- The preimage of a `Fin 2` lower orthant under `finTwoArrow.symm` is the corresponding pair
  -- lower orthant.
  rw [ProbabilityMeasure.map_apply _ (aemeasurable_finTwoArrow_symm μ) measurableSet_Iic]
  have hpre :
      (finTwoArrow.symm : ℝ × ℝ → Fin 2 → ℝ) ⁻¹' Set.Iic z = Set.Iic (z 0, z 1) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hp
      exact ⟨hp 0, hp 1⟩
    · intro hp i
      fin_cases i
      · exact hp.1
      · exact hp.2
  rw [hpre]

/-- Helper for Exercise 1.5.4: a probability measure on `ℝ × ℝ` is uniquely determined by its
closed lower orthants. -/
private theorem probabilityMeasure_eq_of_bivariateDistributionFunction
    {μ ν : ProbabilityMeasure (ℝ × ℝ)}
    (h : ∀ x : ℝ × ℝ, μ (Set.Iic x) = ν (Set.Iic x)) :
    μ = ν := by
  -- Transport the two measures to `Fin 2 → ℝ`, where Example 1.44 gives uniqueness.
  have hmap :
      ProbabilityMeasure.map μ (aemeasurable_finTwoArrow_symm μ) =
        ProbabilityMeasure.map ν (aemeasurable_finTwoArrow_symm ν) := by
    apply ProbabilityMeasure.toMeasure_injective
    refine probabilityMeasure_eq_of_closedLowerOrthants fun z ↦ ?_
    -- The mapped lower orthants are exactly the pairwise lower orthants on `ℝ × ℝ`.
    have hz :
        (ProbabilityMeasure.map μ (aemeasurable_finTwoArrow_symm μ)) (Set.Iic z) =
          (ProbabilityMeasure.map ν (aemeasurable_finTwoArrow_symm ν)) (Set.Iic z) := by
      exact (finTwoLowerOrthantMap_apply μ z).trans <|
        (h (z 0, z 1)).trans (finTwoLowerOrthantMap_apply ν z).symm
    have hz' :
        ((ProbabilityMeasure.map μ (aemeasurable_finTwoArrow_symm μ)) (Set.Iic z) : ENNReal) =
          (ProbabilityMeasure.map ν (aemeasurable_finTwoArrow_symm ν)) (Set.Iic z) := by
      exact_mod_cast hz
    simpa using hz'
  -- A measurable equivalence induces an injective pushforward on measures.
  apply ProbabilityMeasure.toMeasure_injective
  let e : MeasurableEmbedding (finTwoArrow.symm : ℝ × ℝ → Fin 2 → ℝ) :=
    finTwoArrow.symm.measurableEmbedding
  exact e.map_injective (by simpa using congrArg ProbabilityMeasure.toMeasure hmap)

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ` satisfies the
standard bivariate distribution-function axioms. -/
instance (μ : ProbabilityMeasure (ℝ × ℝ)) :
    IsBivariateDistributionFunction (bivariateMeasureDistributionFunction μ) := by
  refine
    { monotone := ?_
      right_continuous := ?_
      tendsto_neg_atTop_zero := ?_
      tendsto_atTop_one := ?_
      rectangle_nonneg := ?_
      tendsto_fst_atBot_zero := ?_
      tendsto_snd_atBot_zero := ?_ }
  · intro x y hxy
    -- Monotonicity follows from inclusion of lower orthants.
    exact measureReal_mono (Set.Iic_subset_Iic.mpr hxy)
  · intro x
    change Tendsto (fun y : ℝ × ℝ ↦ μ.toMeasure.real (Set.Iic y)) (𝓝[Set.Ici x] x)
      (𝓝 (μ.toMeasure.real (Set.Iic x)))
    -- Route correction: diagonal continuity only gives the upper envelope, so we squeeze every
    -- orthant `Set.Iic y` between `Set.Iic x` and the diagonal orthant at radius
    -- `max (y₁ - x₁) (y₂ - x₂)`.
    let δ : ℝ × ℝ → ℝ := fun y ↦ max (y.1 - x.1) (y.2 - x.2)
    let G : ℝ → ℝ := fun t ↦ μ.toMeasure.real (Set.Iic (x.1 + t, x.2 + t))
    let H : ℝ × ℝ → ℝ := fun y ↦ G (δ y)
    have hdiag_ge :
        Tendsto G (𝓝[≥] (0 : ℝ)) (𝓝 (μ.toMeasure.real (Set.Iic x))) := by
      rw [← nhdsGT_sup_nhdsWithin_singleton, nhdsWithin_singleton, tendsto_sup]
      constructor
      · exact tendsto_measureReal_diagonalLowerOrthant_nhdsGT μ x
      · intro s hs
        simpa [G] using mem_of_mem_nhds hs
    have hδ0 : Tendsto δ (𝓝[Set.Ici x] x) (𝓝 0) := by
      have hδ' : Tendsto δ (𝓝 x) (𝓝 0) := by
        have hcont : Continuous fun y : ℝ × ℝ ↦ max (y.1 - x.1) (y.2 - x.2) :=
          (continuous_fst.sub continuous_const).max (continuous_snd.sub continuous_const)
        simpa [δ] using (hcont.continuousAt : ContinuousAt (fun y : ℝ × ℝ ↦
          max (y.1 - x.1) (y.2 - x.2)) x).tendsto
      exact tendsto_nhdsWithin_of_tendsto_nhds hδ'
    have hδ_ge : Tendsto δ (𝓝[Set.Ici x] x) (𝓝[≥] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ0 ?_
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      exact le_trans (sub_nonneg.mpr hy.1) (le_max_left _ _)
    have hH : Tendsto H (𝓝[Set.Ici x] x) (𝓝 (μ.toMeasure.real (Set.Iic x))) :=
      hdiag_ge.comp hδ_ge
    have hlower :
        ∀ᶠ y in 𝓝[Set.Ici x] x,
          μ.toMeasure.real (Set.Iic x) ≤ μ.toMeasure.real (Set.Iic y) := by
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      exact measureReal_mono (Set.Iic_subset_Iic.mpr hy)
    have hupper :
        ∀ᶠ y in 𝓝[Set.Ici x] x,
          μ.toMeasure.real (Set.Iic y) ≤ H y := by
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      have hyδ : y ≤ (x.1 + δ y, x.2 + δ y) := by
        exact ⟨by
            dsimp [δ]
            linarith [le_max_left (y.1 - x.1) (y.2 - x.2)],
          by
            dsimp [δ]
            linarith [le_max_right (y.1 - x.1) (y.2 - x.2)]⟩
      exact measureReal_mono (Set.Iic_subset_Iic.mpr hyδ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hH hlower hupper
  · -- Control the lower orthants by the first-coordinate negative tail.
    change Tendsto (fun z : ℝ × ℝ ↦ μ.toMeasure.real (Set.Iic (-z.1, -z.2))) atTop (𝓝 0)
    have hfst : Tendsto Prod.fst (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_fst
    have hsnd : Tendsto Prod.snd (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_snd
    have hupper :
        Tendsto (fun z : ℝ × ℝ ↦ μ.toMeasure.real (Set.Iic (-z.1, 0))) atTop (𝓝 0) := by
      simpa [Function.comp] using
        (tendsto_measureReal_fstNegLowerOrthant_atTop μ 0).comp hfst
    have hle :
        ∀ᶠ z in (atTop : Filter (ℝ × ℝ)),
          μ.toMeasure.real (Set.Iic (-z.1, -z.2)) ≤ μ.toMeasure.real (Set.Iic (-z.1, 0)) := by
      filter_upwards [(tendsto_atTop.1 hsnd 0)] with z hz
      exact measureReal_mono (Set.Iic_subset_Iic.mpr ⟨le_rfl, by linarith⟩)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ ↦ measureReal_nonneg) hle
  · -- Compare `Set.Iic x` from below with the diagonal orthant at `min (x₁, x₂)`.
    change Tendsto (fun z : ℝ × ℝ ↦ μ.toMeasure.real (Set.Iic z)) atTop (𝓝 1)
    have hdiag :
        Tendsto (fun q : ℝ ↦ μ.toMeasure.real (Set.Iic (q, q))) atTop (𝓝 1) := by
      have hμ :
          Tendsto (fun q : ℝ ↦ μ.toMeasure (Set.Iic (q, q))) atTop
            (𝓝 (μ.toMeasure (⋃ q : ℝ, Set.Iic (q, q)))) := by
        apply tendsto_measure_iUnion_atTop
        intro a b hab
        exact Set.Iic_subset_Iic.mpr ⟨hab, hab⟩
      have huniv : (⋃ q : ℝ, Set.Iic (q, q)) = Set.univ := by
        ext z
        constructor
        · intro _
          simp
        · intro _
          refine Set.mem_iUnion.2 ⟨max z.1 z.2, ?_⟩
          exact ⟨le_max_left _ _, le_max_right _ _⟩
      have hμ1 :
          Tendsto (fun q : ℝ ↦ μ.toMeasure (Set.Iic (q, q))) atTop (𝓝 1) := by
        simpa [huniv] using hμ
      have h1ne : (1 : ENNReal) ≠ ⊤ := by simp
      simpa [measureReal_def] using
        ((ENNReal.continuousAt_toReal h1ne).tendsto).comp hμ1
    have hmin : Tendsto (fun z : ℝ × ℝ ↦ min z.1 z.2) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(b, b), fun z hz ↦ ?_⟩
      exact le_min hz.1 hz.2
    have hlower :
        Tendsto (fun z : ℝ × ℝ ↦ μ.toMeasure.real (Set.Iic (min z.1 z.2, min z.1 z.2)))
          atTop (𝓝 1) := hdiag.comp hmin
    have hle :
        ∀ z : ℝ × ℝ,
          μ.toMeasure.real (Set.Iic (min z.1 z.2, min z.1 z.2)) ≤ μ.toMeasure.real (Set.Iic z) := by
      intro z
      exact measureReal_mono (Set.Iic_subset_Iic.mpr ⟨min_le_left _ _, min_le_right _ _⟩)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      hle (fun _ ↦ measureReal_le_one)
  · intro x1 y1 x2 y2 hx hy
    change 0 ≤
      μ.toMeasure.real (Set.Iic (y1, y2)) - μ.toMeasure.real (Set.Iic (y1, x2)) -
        μ.toMeasure.real (Set.Iic (x1, y2)) + μ.toMeasure.real (Set.Iic (x1, x2))
    -- Rewrite the rectangle increment as the measure of the half-open rectangle
    -- `Set.Ioc x1 y1 ×ˢ Set.Ioc x2 y2`.
    let A : Set (ℝ × ℝ) := Set.Iic (y1, y2)
    let B : Set (ℝ × ℝ) := Set.Iic (y1, x2)
    let C : Set (ℝ × ℝ) := Set.Iic (x1, y2)
    have hBCsubset : B ∪ C ⊆ A := by
      intro z hz
      rcases hz with hzB | hzC
      · exact ⟨hzB.1, le_trans hzB.2 hy⟩
      · exact ⟨le_trans hzC.1 hx, hzC.2⟩
    have hinter : B ∩ C = Set.Iic (x1, x2) := by
      ext z
      simp only [B, C, Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · intro hz
        exact ⟨hz.2.1, hz.1.2⟩
      · intro hz
        exact ⟨⟨le_trans hz.1 hx, hz.2⟩, ⟨hz.1, le_trans hz.2 hy⟩⟩
    have hbox :
        A \ (B ∪ C) = Set.Ioc x1 y1 ×ˢ Set.Ioc x2 y2 := by
      ext z
      constructor
      · intro hz
        have hzA : z ≤ (y1, y2) := hz.1
        have hz_not_B : ¬ z ≤ (y1, x2) := by
          intro hzB
          exact hz.2 (Or.inl hzB)
        have hz_not_C : ¬ z ≤ (x1, y2) := by
          intro hzC
          exact hz.2 (Or.inr hzC)
        have hxlt : x1 < z.1 := by
          by_contra hzx
          exact hz_not_C ⟨not_lt.mp hzx, hzA.2⟩
        have hylt : x2 < z.2 := by
          by_contra hzx
          exact hz_not_B ⟨hzA.1, not_lt.mp hzx⟩
        exact ⟨⟨hxlt, hzA.1⟩, ⟨hylt, hzA.2⟩⟩
      · intro hz
        refine ⟨⟨hz.1.2, hz.2.2⟩, ?_⟩
        intro hzBC
        rcases hzBC with hzB | hzC
        · exact (not_le.mpr hz.2.1) hzB.2
        · exact (not_le.mpr hz.1.1) hzC.1
    have hunion :
        μ.toMeasure.real (B ∪ C) =
          μ.toMeasure.real B + μ.toMeasure.real C - μ.toMeasure.real (B ∩ C) := by
      have hu :
          μ.toMeasure.real (B ∪ C) + μ.toMeasure.real (B ∩ C) =
            μ.toMeasure.real B + μ.toMeasure.real C :=
        measureReal_union_add_inter measurableSet_Iic
      linarith
    have hdiff :
        μ.toMeasure.real (A \ (B ∪ C)) =
          μ.toMeasure.real A - μ.toMeasure.real (B ∪ C) := by
      simpa [A, B, C] using
        (measureReal_diff hBCsubset (measurableSet_Iic.union measurableSet_Iic) :
          μ.toMeasure.real (A \ (B ∪ C)) =
            μ.toMeasure.real A - μ.toMeasure.real (B ∪ C))
    have hnonneg : 0 ≤ μ.toMeasure.real (A \ (B ∪ C)) := by
      rw [hbox]
      exact measureReal_nonneg
    rw [hdiff, hunion, hinter] at hnonneg
    simpa [A, B, C, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnonneg
  · intro y
    refine
      ((tendsto_measureReal_fstNegLowerOrthant_atTop μ y).comp tendsto_neg_atBot_atTop).congr' ?_
    filter_upwards with x
    simp
  · intro x
    refine
      ((tendsto_measureReal_sndNegLowerOrthant_atTop μ x).comp tendsto_neg_atBot_atTop).congr' ?_
    filter_upwards with y
    simp

/-- Helper for Exercise 1.5.4: fixing a rational second coordinate leaves a monotone section in
the first coordinate. -/
private theorem ratSectionMonotone
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) :
    Monotone (fun x : ℝ ↦ (F (x, (q : ℝ)) : ℝ)) := by
  -- Monotonicity of `F` in the product order specializes to the first coordinate section.
  intro a b hab
  exact hF.monotone ⟨hab, le_rfl⟩

/-- Helper for Exercise 1.5.4: fixing a rational second coordinate preserves right continuity in
the first coordinate. -/
private theorem ratSectionRightContinuous
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) :
    ∀ x : ℝ, ContinuousWithinAt (fun y : ℝ ↦ (F (y, (q : ℝ)) : ℝ)) (Set.Ici x) x := by
  intro x
  -- Compose the bivariate right-continuity with the coordinate embedding `y ↦ (y, q)`.
  have hmaps : MapsTo (fun y : ℝ ↦ (y, (q : ℝ))) (Set.Ici x) (Set.Ici (x, (q : ℝ))) := by
    intro y hy
    exact ⟨hy, le_rfl⟩
  change
    ContinuousWithinAt
      ((fun z : ℝ × ℝ ↦ (F z : ℝ)) ∘ fun y : ℝ ↦ (y, (q : ℝ)))
      (Set.Ici x) x
  exact ContinuousWithinAt.comp (hF.right_continuous (x, (q : ℝ)))
    ((Continuous.prodMk_left (q : ℝ)).continuousWithinAt) hmaps

/-- Helper for Exercise 1.5.4: the rational vertical section is a Stieltjes function in the first
coordinate. -/
private noncomputable def ratSectionStieltjesFunction
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) :
    StieltjesFunction ℝ :=
  { toFun := fun x ↦ (F (x, (q : ℝ)) : ℝ)
    mono' := ratSectionMonotone F hF q
    right_continuous' := ratSectionRightContinuous F hF q }

/-- Helper for Exercise 1.5.4: the rational vertical section evaluates pointwise to the original
function value. -/
@[simp] private theorem ratSectionStieltjesFunction_apply
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) (x : ℝ) :
    ratSectionStieltjesFunction F hF q x = (F (x, (q : ℝ)) : ℝ) :=
  rfl

/-- Helper for Exercise 1.5.4: the rational vertical section still takes values in `[0, 1]`. -/
private theorem ratSectionBounds
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) (x : ℝ) :
    0 ≤ ratSectionStieltjesFunction F hF q x ∧ ratSectionStieltjesFunction F hF q x ≤ 1 := by
  -- The bounds come directly from the codomain of `F`.
  constructor
  · simpa [ratSectionStieltjesFunction_apply] using (F (x, (q : ℝ))).2.1
  · simpa [ratSectionStieltjesFunction_apply] using (F (x, (q : ℝ))).2.2

/-- Helper for Exercise 1.5.4: the candidate measure attached to a rational vertical section. -/
private noncomputable def ratSectionMeasure
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ) :
    Measure ℝ :=
  (ratSectionStieltjesFunction F hF q).measure

/-- Helper for Exercise 1.5.4: once the missing `x → -∞` limit is supplied for a rational
section, its Stieltjes measure evaluates on `Set.Iic x` as expected. -/
private theorem ratSectionMeasure_apply_Iic_of_tendsto_atBot_zero
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (q : ℚ)
    (hbot : Tendsto (fun x : ℝ ↦ (F (x, (q : ℝ)) : ℝ)) atBot (𝓝 0)) (x : ℝ) :
    ratSectionMeasure F hF q (Set.Iic x) = ENNReal.ofReal (F (x, (q : ℝ)) : ℝ) := by
  -- The only missing input is the section limit at `-∞`; once available, `measure_Iic`
  -- gives the desired evaluation with `l = 0`.
  simpa [ratSectionMeasure, ratSectionStieltjesFunction_apply, sub_zero] using
    StieltjesFunction.measure_Iic (ratSectionStieltjesFunction F hF q) hbot x

/-- Helper for Exercise 1.5.4: for a fixed vertical strip `c ≤ d`, the section
`x ↦ F (x, d) - F (x, c)` is monotone. -/
private theorem verticalStripSectionMonotone
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (hcd : c ≤ d) :
    Monotone (fun x : ℝ ↦ (F (x, d) : ℝ) - F (x, c)) := by
  intro a b hab
  -- The rectangle increment on `[a, b] × [c, d]` is exactly the strip difference.
  have hrect : 0 ≤ (F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c) :=
    hF.rectangle_nonneg hab hcd
  linarith

/-- Helper for Exercise 1.5.4: fixing the second coordinate preserves right continuity in the
first coordinate. -/
private theorem realSectionRightContinuous
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (y : ℝ) :
    ∀ x : ℝ, ContinuousWithinAt (fun z : ℝ ↦ (F (z, y) : ℝ)) (Set.Ici x) x := by
  intro x
  -- Compose the bivariate right-continuity with the coordinate embedding `z ↦ (z, y)`.
  have hmaps : MapsTo (fun z : ℝ ↦ (z, y)) (Set.Ici x) (Set.Ici (x, y)) := by
    intro z hz
    exact ⟨hz, le_rfl⟩
  change
    ContinuousWithinAt
      ((fun p : ℝ × ℝ ↦ (F p : ℝ)) ∘ fun z : ℝ ↦ (z, y))
      (Set.Ici x) x
  exact ContinuousWithinAt.comp (hF.right_continuous (x, y))
    (Continuous.prodMk_left y).continuousWithinAt hmaps

/-- Helper for Exercise 1.5.4: for a fixed vertical strip `c ≤ d`, the section
`x ↦ F (x, d) - F (x, c)` is right-continuous. -/
private theorem verticalStripSectionRightContinuous
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (_hcd : c ≤ d) :
    ∀ x : ℝ, ContinuousWithinAt (fun z : ℝ ↦ (F (z, d) : ℝ) - F (z, c)) (Set.Ici x) x := by
  intro x
  -- Right continuity is stable under subtraction of the two coordinate sections.
  exact (realSectionRightContinuous F hF d x).sub (realSectionRightContinuous F hF c x)

/-- Helper for Exercise 1.5.4: the strip section `x ↦ F (x, d) - F (x, c)` tends to `0` at
`-∞`. -/
private theorem verticalStripSection_tendsto_atBot_zero
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} :
    Tendsto (fun x : ℝ ↦ (F (x, d) : ℝ) - F (x, c)) atBot (𝓝 0) := by
  -- Both fixed-coordinate tails vanish at `-∞`, so their difference does as well.
  simpa using (hF.tendsto_fst_atBot_zero d).sub (hF.tendsto_fst_atBot_zero c)

/-- Helper for Exercise 1.5.4: the fixed vertical strip `c ≤ d` defines a Stieltjes function in
the first coordinate. -/
private noncomputable def verticalStripStieltjesFunction
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (hcd : c ≤ d) :
    StieltjesFunction ℝ :=
  { toFun := fun x ↦ (F (x, d) : ℝ) - F (x, c)
    mono' := verticalStripSectionMonotone F hF hcd
    right_continuous' := verticalStripSectionRightContinuous F hF hcd }

/-- Helper for Exercise 1.5.4: the measure attached to the fixed vertical strip `c ≤ d`. -/
private noncomputable def verticalStripMeasure
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (hcd : c ≤ d) :
    Measure ℝ :=
  (verticalStripStieltjesFunction F hF hcd).measure

/-- Helper for Exercise 1.5.4: the strip measure evaluates lower rays by the expected vertical
increment of `F`. -/
private theorem verticalStripMeasure_apply_Iic
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (hcd : c ≤ d) (x : ℝ) :
    verticalStripMeasure F hF hcd (Set.Iic x) =
      ENNReal.ofReal ((F (x, d) : ℝ) - F (x, c)) := by
  -- The tail condition at `-∞` lets us apply the standard `measure_Iic` formula.
  simpa [verticalStripMeasure, verticalStripStieltjesFunction] using
    StieltjesFunction.measure_Iic (verticalStripStieltjesFunction F hF hcd)
      (verticalStripSection_tendsto_atBot_zero F hF) x

/-- Helper for Exercise 1.5.4: the strip measure of `Set.Ioc a b` is exactly the rectangle
increment of `F` over `(a, b] × (c, d]`. -/
private theorem verticalStripMeasure_apply_Ioc
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {c d : ℝ} (hcd : c ≤ d) (a b : ℝ) :
    verticalStripMeasure F hF hcd (Set.Ioc a b) =
      ENNReal.ofReal ((F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c)) := by
  -- Unfold the strip Stieltjes function only at the stable `measure_Ioc` interface.
  rw [verticalStripMeasure, StieltjesFunction.measure_Ioc]
  simp only [verticalStripStieltjesFunction]
  ring_nf

/-- Helper for Exercise 1.5.4: the explicit rectangle increment can be read as the mass of the
corresponding vertical-strip measure on `Set.Ioc a b`. -/
private theorem rectangleIncrement_eq_verticalStripMeasure_apply_Ioc
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {a b c d : ℝ} (hcd : c ≤ d) :
    ENNReal.ofReal ((F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c)) =
      verticalStripMeasure F hF hcd (Set.Ioc a b) := by
  -- Reorient the strip-measure formula into the rectangle-increment form used later.
  simpa using (verticalStripMeasure_apply_Ioc F hF hcd a b).symm

/-- Helper for Exercise 1.5.4: every rectangle increment of a bivariate distribution function is
nonnegative. -/
private theorem rectangleIncrement_nonneg
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ (F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c) :=
  hF.rectangle_nonneg hab hcd

/-- Helper for Exercise 1.5.4: splitting a rectangle once in the first coordinate adds the two
sub-rectangle increments. -/
private theorem rectangleIncrement_split_fst
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {a b c d e : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hde : d ≤ e) :
    ENNReal.ofReal ((F (c, e) : ℝ) - F (c, d) - F (a, e) + F (a, d)) =
      ENNReal.ofReal ((F (b, e) : ℝ) - F (b, d) - F (a, e) + F (a, d)) +
        ENNReal.ofReal ((F (c, e) : ℝ) - F (c, d) - F (b, e) + F (b, d)) := by
  -- Proof comment: the real-valued increment telescopes exactly across the intermediate cut `b`,
  -- and both summands are nonnegative by the rectangle-monotonicity axiom.
  have hleft :
      0 ≤ (F (b, e) : ℝ) - F (b, d) - F (a, e) + F (a, d) :=
    rectangleIncrement_nonneg F hF hab hde
  have hright :
      0 ≤ (F (c, e) : ℝ) - F (c, d) - F (b, e) + F (b, d) :=
    rectangleIncrement_nonneg F hF hbc hde
  rw [← ENNReal.ofReal_add hleft hright]
  ring_nf

/-- Helper for Exercise 1.5.4: splitting a rectangle once in the second coordinate adds the two
sub-rectangle increments. -/
private theorem rectangleIncrement_split_snd
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    {a b c d e : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e) :
    ENNReal.ofReal ((F (b, e) : ℝ) - F (b, c) - F (a, e) + F (a, c)) =
      ENNReal.ofReal ((F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c)) +
        ENNReal.ofReal ((F (b, e) : ℝ) - F (b, d) - F (a, e) + F (a, d)) := by
  -- Proof comment: this is the same telescoping identity along the second coordinate cut `d`.
  have hlower :
      0 ≤ (F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c) :=
    rectangleIncrement_nonneg F hF hab hcd
  have hupper :
      0 ≤ (F (b, e) : ℝ) - F (b, d) - F (a, e) + F (a, d) :=
    rectangleIncrement_nonneg F hF hab hde
  rw [← ENNReal.ofReal_add hlower hupper]
  ring_nf

/-- Helper for Exercise 1.5.4: shifting a real coordinate by `-(n + 1)` drives it to `-∞`. -/
private theorem tendsto_sub_natCast_add_one_atTop_atBot (x : ℝ) :
    Tendsto (fun n : ℕ ↦ x - (n + 1 : ℝ)) atTop atBot := by
  -- Rewrite the sequence as a translate of `n ↦ -(n : ℝ)`, whose limit is `-∞`.
  have hneg : Tendsto (fun n : ℕ ↦ -((n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  simpa [sub_eq_add_neg, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
    (tendsto_atBot_add_const_right _ (x - 1) hneg)

/-- Helper for Exercise 1.5.4: the lower-left corner term in the expanding rectangle approximation
of `Set.Iic x` tends to `0`. -/
private theorem tendsto_expandingLowerLeftCorner_zero
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (x : ℝ × ℝ) :
    Tendsto (fun n : ℕ ↦
      (F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ)) : ℝ)) atTop (𝓝 0) := by
  -- Squeeze the diagonal lower-left corner by the first-coordinate tail with fixed second
  -- coordinate `x.2`.
  have hupper :
      Tendsto (fun n : ℕ ↦ (F (x.1 - (n + 1 : ℝ), x.2) : ℝ)) atTop (𝓝 0) :=
    (hF.tendsto_fst_atBot_zero x.2).comp (tendsto_sub_natCast_add_one_atTop_atBot x.1)
  have hnonneg :
      ∀ n : ℕ, 0 ≤ (F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ)) : ℝ) := by
    intro n
    exact (F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ))).2.1
  have hle :
      ∀ n : ℕ,
        (F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ)) : ℝ) ≤
          (F (x.1 - (n + 1 : ℝ), x.2) : ℝ) := by
    intro n
    exact hF.monotone ⟨le_rfl, sub_le_self _ (by positivity)⟩
  exact squeeze_zero hnonneg hle hupper

/-- Helper for Exercise 1.5.4: the explicit rectangle increments of the expanding lower-left
rectangles converge to `F x`. -/
private theorem tendsto_expandingRectangleIncrement
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (x : ℝ × ℝ) :
    Tendsto (fun n : ℕ ↦
      (F (x.1, x.2) : ℝ) - F (x.1, x.2 - (n + 1 : ℝ))
        - F (x.1 - (n + 1 : ℝ), x.2)
        + F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ))) atTop (𝓝 (F x : ℝ)) := by
  -- Each boundary term tends to `0`, so only the target corner `F x` survives in the limit.
  have hsnd :
      Tendsto (fun n : ℕ ↦ (F (x.1, x.2 - (n + 1 : ℝ)) : ℝ)) atTop (𝓝 0) :=
    (hF.tendsto_snd_atBot_zero x.1).comp (tendsto_sub_natCast_add_one_atTop_atBot x.2)
  have hfst :
      Tendsto (fun n : ℕ ↦ (F (x.1 - (n + 1 : ℝ), x.2) : ℝ)) atTop (𝓝 0) :=
    (hF.tendsto_fst_atBot_zero x.2).comp (tendsto_sub_natCast_add_one_atTop_atBot x.1)
  have hcorner :
      Tendsto (fun n : ℕ ↦
        (F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ)) : ℝ)) atTop (𝓝 0) :=
    tendsto_expandingLowerLeftCorner_zero F hF x
  have hcorrection :
      Tendsto (fun n : ℕ ↦
        -(F (x.1, x.2 - (n + 1 : ℝ)) : ℝ) - F (x.1 - (n + 1 : ℝ), x.2)
          + F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hsnd.neg.add hfst.neg).add hcorner
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    tendsto_const_nhds.add hcorrection

/-- Helper for Exercise 1.5.4: the same expanding-rectangle limit is available directly in
`ℝ≥0∞`, matching the measure-valued formulas used later. -/
private theorem tendsto_expandingRectangleIncrement_ennreal
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) (x : ℝ × ℝ) :
    Tendsto (fun n : ℕ ↦
      ENNReal.ofReal ((F (x.1, x.2) : ℝ) - F (x.1, x.2 - (n + 1 : ℝ))
        - F (x.1 - (n + 1 : ℝ), x.2)
        + F (x.1 - (n + 1 : ℝ), x.2 - (n + 1 : ℝ)))) atTop
      (𝓝 (ENNReal.ofReal (F x : ℝ))) := by
  -- Proof comment: transport the already-proved real convergence through `ENNReal.ofReal`.
  exact ENNReal.tendsto_ofReal (tendsto_expandingRectangleIncrement F hF x)

/-- Helper for Exercise 1.5.4: rational `Ioc ×ˢ Ioc` rectangles generate
`borel (ℝ × ℝ)`. -/
private theorem rationalIocSet_isCountablySpanning :
    IsCountablySpanning {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S} := by
  -- The intervals `(-(n+1), n+1]` already cover the whole line.
  refine ⟨fun n ↦ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    refine ⟨-(n + 1 : ℚ), n + 1, by linarith, ?_⟩
    congr 1 <;> norm_num
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : x ∈ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        constructor
        · linarith
        · linarith
      exact Set.mem_iUnion.2 ⟨n, hmem⟩

/-- Helper for Exercise 1.5.4: the weak rational `Ioc` family keeps the degenerate intervals that
collapse to `∅`, which is convenient for semiring arguments. -/
private def rationalIocSetLe : Set (Set ℝ) :=
  {S : Set ℝ | ∃ a b : ℚ, a ≤ b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}

/-- Helper for Exercise 1.5.4: every rational half-open interval represents a member of the weak
semiring family, with reversed endpoints collapsing to `∅`. -/
private theorem rationalIocSetLe_interval_mem (a b : ℚ) :
    Set.Ioc (a : ℝ) (b : ℝ) ∈ rationalIocSetLe := by
  rcases le_total a b with hab | hba
  · exact ⟨a, b, hab, rfl⟩
  · refine ⟨a, a, le_rfl, ?_⟩
    have hba' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    have hEmpty : Set.Ioc (a : ℝ) (b : ℝ) = ∅ := Set.Ioc_eq_empty (not_lt.mpr hba')
    have hEmpty' : Set.Ioc (a : ℝ) (a : ℝ) = ∅ := Set.Ioc_eq_empty (lt_irrefl _)
    rw [hEmpty', hEmpty]

/-- Helper for Exercise 1.5.4: subtracting one `Ioc` interval from another splits into the left
and right boundary pieces. -/
private theorem ioc_diff_ioc_eq_union {a b c d : ℝ} :
    Set.Ioc a b \ Set.Ioc c d = Set.Ioc a (min b c) ∪ Set.Ioc (max a d) b := by
  -- Proof comment: outside `(c, d]`, a point of `(a, b]` must lie either to the left of `c`
  -- or to the right of `d`, which yields the two boundary pieces.
  ext x
  constructor
  · intro hx
    have hxIoc : x ∈ Set.Ioc a b := hx.1
    have hxNot : x ∉ Set.Ioc c d := hx.2
    simp only [Set.mem_Ioc, not_and_or] at hxIoc hxNot ⊢
    rcases hxNot with hxc | hdx
    · left
      exact ⟨hxIoc.1, le_min hxIoc.2 (not_lt.mp hxc)⟩
    · right
      exact ⟨max_lt_iff.mpr ⟨hxIoc.1, lt_of_not_ge hdx⟩, hxIoc.2⟩
  · intro hx
    rcases hx with hx | hx
    · refine ⟨⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩, ?_⟩
      simp only [Set.mem_Ioc, not_and_or]
      exact Or.inl (not_lt_of_ge (le_trans hx.2 (min_le_right _ _)))
    · refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩, ?_⟩
      simp only [Set.mem_Ioc, not_and_or]
      exact Or.inr (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hx.1))

/-- Helper for Exercise 1.5.4: the two boundary pieces in the `Ioc` difference decomposition are
disjoint once the subtracted interval has ordered endpoints. -/
private theorem disjoint_ioc_diff_ioc_union_parts {a b c d : ℚ} (hcd : c ≤ d) :
    Disjoint (Set.Ioc (a : ℝ) ((min b c : ℚ) : ℝ))
      (Set.Ioc (((max a d : ℚ) : ℝ)) (b : ℝ)) := by
  -- Proof comment: points in the left piece satisfy `x ≤ c`, while points in the right piece
  -- satisfy `d < x`; the ordered endpoints force these inequalities to be incompatible.
  rw [Set.disjoint_left]
  intro x hxLeft hxRight
  have hxc : x ≤ (c : ℝ) := by
    exact le_trans hxLeft.2 (show ((min b c : ℚ) : ℝ) ≤ (c : ℝ) by exact_mod_cast min_le_right b c)
  have hcmax : (c : ℝ) ≤ ((max a d : ℚ) : ℝ) := by
    exact_mod_cast le_trans hcd (le_max_right a d)
  have hcgt : (c : ℝ) < x := lt_of_le_of_lt hcmax hxRight.1
  exact (not_lt_of_ge hxc) hcgt

/-- Helper for Exercise 1.5.4: the weak rational `Ioc` family is a semiring of sets on `ℝ`. -/
private theorem rationalIocSetLe_isSetSemiring :
    IsSetSemiring rationalIocSetLe := by
  refine
    { empty_mem := ?_
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- Proof comment: the degenerate rational interval `(0, 0]` realizes the empty set.
    exact ⟨0, 0, le_rfl, by simp⟩
  · rintro s ⟨a, b, hab, rfl⟩ t ⟨c, d, hcd, rfl⟩
    -- Proof comment: intersections of half-open intervals remain half-open, possibly empty.
    simpa [Set.Ioc_inter_Ioc] using
      rationalIocSetLe_interval_mem (max a c) (min b d)
  · intro s hs t ht
    rcases hs with ⟨a, b, hab, rfl⟩
    rcases ht with ⟨c, d, hcd, rfl⟩
    -- Proof comment: `(a, b] \ (c, d]` splits into the two disjoint boundary intervals from the
    -- explicit interval identity above.
    refine
      ⟨{Set.Ioc (a : ℝ) (((min b c : ℚ) : ℝ)),
          Set.Ioc (((max a d : ℚ) : ℝ)) (b : ℝ)}, ?_, ?_, ?_⟩
    · intro u hu
      have hu' : u ∈ ({Set.Ioc (a : ℝ) (((min b c : ℚ) : ℝ)),
          Set.Ioc (((max a d : ℚ) : ℝ)) (b : ℝ)} : Finset (Set ℝ)) := hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu'
      rcases hu' with rfl | rfl
      · exact rationalIocSetLe_interval_mem a (min b c)
      · exact rationalIocSetLe_interval_mem (max a d) b
    · intro u hu v hv huv
      have hu' : u ∈ ({Set.Ioc (a : ℝ) (((min b c : ℚ) : ℝ)),
          Set.Ioc (((max a d : ℚ) : ℝ)) (b : ℝ)} : Finset (Set ℝ)) := hu
      have hv' : v ∈ ({Set.Ioc (a : ℝ) (((min b c : ℚ) : ℝ)),
          Set.Ioc (((max a d : ℚ) : ℝ)) (b : ℝ)} : Finset (Set ℝ)) := hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hu' hv'
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact False.elim (huv rfl)
      · exact disjoint_ioc_diff_ioc_union_parts hcd
      · exact (disjoint_ioc_diff_ioc_union_parts hcd).symm
      · exact False.elim (huv rfl)
    · simpa [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_pair] using
        (ioc_diff_ioc_eq_union (a := (a : ℝ)) (b := (b : ℝ))
          (c := (c : ℝ)) (d := (d : ℝ)))

/-- Helper for Exercise 1.5.4: the product of two semirings is again a semiring, realized here as
rectangles in `Set.image2 (· ×ˢ ·)`. -/
private theorem image2_prod_isSetSemiring {α β : Type*} {C : Set (Set α)} {D : Set (Set β)}
    (hC : IsSetSemiring C) (hD : IsSetSemiring D) :
    IsSetSemiring (Set.image2 (· ×ˢ ·) C D) := by
  classical
  refine
    { empty_mem := ?_
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- Proof comment: the empty rectangle is the product of the two empty generators.
    exact ⟨∅, hC.empty_mem, ∅, hD.empty_mem, by simp⟩
  · rintro s ⟨u, hu, v, hv, rfl⟩ t ⟨u', hu', v', hv', rfl⟩
    -- Proof comment: rectangle intersections are coordinatewise intersections.
    exact ⟨u ∩ u', hC.inter_mem _ hu _ hu', v ∩ v', hD.inter_mem _ hv _ hv', by
      ext x
      simp [and_left_comm, and_assoc]⟩
  · rintro s ⟨u, hu, v, hv, rfl⟩ t ⟨u', hu', v', hv', rfl⟩
    let Iu := hC.disjointOfDiff hu hu'
    let Iv := hD.disjointOfDiff hv hv'
    let J₁ : Finset (Set (α × β)) := Iu.image fun a ↦ a ×ˢ v
    let J₂ : Finset (Set (α × β)) := Iv.image fun b ↦ (u ∩ u') ×ˢ b
    have hJ₁ :
        ⋃₀ (J₁ : Set (Set (α × β))) = (⋃₀ (Iu : Set (Set α))) ×ˢ v := by
      -- Proof comment: every left boundary rectangle is indexed by one `u \ u'` piece and the
      -- common vertical side `v`.
      ext x
      constructor
      · intro hx
        rcases Set.mem_sUnion.1 hx with ⟨r, hr, hxmem⟩
        rcases Finset.mem_image.1 hr with ⟨a, ha, rfl⟩
        exact ⟨Set.mem_sUnion.2 ⟨a, ha, hxmem.1⟩, hxmem.2⟩
      · intro hx
        rcases Set.mem_sUnion.1 hx.1 with ⟨a, ha, hxa⟩
        exact Set.mem_sUnion.2 ⟨a ×ˢ v, Finset.mem_image.2 ⟨a, ha, rfl⟩, ⟨hxa, hx.2⟩⟩
    have hJ₂ :
        ⋃₀ (J₂ : Set (Set (α × β))) = (u ∩ u') ×ˢ ⋃₀ (Iv : Set (Set β)) := by
      -- Proof comment: every top boundary rectangle is indexed by one `v \ v'` piece and the
      -- common horizontal side `u ∩ u'`.
      ext x
      constructor
      · intro hx
        rcases Set.mem_sUnion.1 hx with ⟨r, hr, hxmem⟩
        rcases Finset.mem_image.1 hr with ⟨b, hb, rfl⟩
        exact ⟨hxmem.1, Set.mem_sUnion.2 ⟨b, hb, hxmem.2⟩⟩
      · intro hx
        rcases Set.mem_sUnion.1 hx.2 with ⟨b, hb, hxb⟩
        exact Set.mem_sUnion.2 ⟨(u ∩ u') ×ˢ b, Finset.mem_image.2 ⟨b, hb, rfl⟩, ⟨hx.1, hxb⟩⟩
    have hpairJ :
        PairwiseDisjoint ((J₁ ∪ J₂ : Finset (Set (α × β))) : Set (Set (α × β))) id := by
      intro A hA B hB hAB
      have hA' : A ∈ J₁ ∪ J₂ := hA
      have hB' : B ∈ J₁ ∪ J₂ := hB
      rw [Finset.mem_union] at hA' hB'
      rcases hA' with hA | hA <;> rcases hB' with hB | hB
      · rcases Finset.mem_image.1 hA with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.1 hB with ⟨b, hb, rfl⟩
        by_cases hab : a = b
        · exact False.elim (hAB (by simp [hab]))
        · exact ((hC.pairwiseDisjoint_disjointOfDiff hu hu') ha hb hab).set_prod_left v v
      · rcases Finset.mem_image.1 hA with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.1 hB with ⟨b, hb, rfl⟩
        have ha_sub : a ⊆ u \ u' := by
          rw [← hC.sUnion_disjointOfDiff hu hu']
          exact subset_sUnion_of_mem ha
        have hleft : Disjoint a (u ∩ u') := by
          rw [Set.disjoint_left]
          intro x hxa hxu
          exact (ha_sub hxa).2 hxu.2
        exact hleft.set_prod_left v b
      · rcases Finset.mem_image.1 hA with ⟨b, hb, rfl⟩
        rcases Finset.mem_image.1 hB with ⟨a, ha, rfl⟩
        have ha_sub : a ⊆ u \ u' := by
          rw [← hC.sUnion_disjointOfDiff hu hu']
          exact subset_sUnion_of_mem ha
        have hleft : Disjoint a (u ∩ u') := by
          rw [Set.disjoint_left]
          intro x hxa hxu
          exact (ha_sub hxa).2 hxu.2
        exact (hleft.set_prod_left v b).symm
      · rcases Finset.mem_image.1 hA with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.1 hB with ⟨b, hb, rfl⟩
        by_cases hab : a = b
        · exact False.elim (hAB (by simp [hab]))
        · exact
            ((hD.pairwiseDisjoint_disjointOfDiff hv hv') ha hb hab).set_prod_right
              (u ∩ u') (u ∩ u')
    have hdiff :
        (u ×ˢ v) \ (u' ×ˢ v') = ((u \ u') ×ˢ v) ∪ ((u ∩ u') ×ˢ (v \ v')) := by
      -- Proof comment: a point leaves the big rectangle either because the first coordinate
      -- leaves `u'` or, once the first coordinate stays in `u'`, because the second leaves `v'`.
      ext x
      constructor
      · intro hx
        have hxuv : x ∈ u ×ˢ v := hx.1
        have hxnot : x ∉ u' ×ˢ v' := hx.2
        by_cases hx' : x.1 ∈ u'
        · right
          refine ⟨⟨hxuv.1, hx'⟩, ⟨hxuv.2, ?_⟩⟩
          intro hxv'
          exact hxnot ⟨hx', hxv'⟩
        · left
          exact ⟨⟨hxuv.1, hx'⟩, hxuv.2⟩
      · intro hx
        rcases hx with hx | hx
        · refine ⟨⟨hx.1.1, hx.2⟩, ?_⟩
          intro hxt
          exact hx.1.2 hxt.1
        · refine ⟨⟨hx.1.1, hx.2.1⟩, ?_⟩
          intro hxt
          exact hx.2.2 hxt.2
    refine ⟨J₁ ∪ J₂, ?_, hpairJ, ?_⟩
    · intro r hr
      have hr' : r ∈ J₁ ∪ J₂ := hr
      rw [Finset.mem_union] at hr'
      rcases hr' with hr | hr
      · rcases Finset.mem_image.1 hr with ⟨a, ha, rfl⟩
        exact ⟨a, hC.subset_disjointOfDiff hu hu' ha, v, hv, rfl⟩
      · rcases Finset.mem_image.1 hr with ⟨b, hb, rfl⟩
        exact ⟨u ∩ u', hC.inter_mem _ hu _ hu', b, hD.subset_disjointOfDiff hv hv' hb, rfl⟩
    · calc
        (u ×ˢ v) \ (u' ×ˢ v') = ((u \ u') ×ˢ v) ∪ ((u ∩ u') ×ˢ (v \ v')) := hdiff
        _ = ⋃₀ (J₁ : Set (Set (α × β))) ∪ ⋃₀ (J₂ : Set (Set (α × β))) := by
          rw [hJ₁, hJ₂, hC.sUnion_disjointOfDiff hu hu', hD.sUnion_disjointOfDiff hv hv']
        _ = ⋃₀ (((J₁ ∪ J₂ : Finset (Set (α × β))) : Set (Set (α × β)))) := by
          rw [Finset.coe_union, Set.sUnion_union]

/-- Helper for Exercise 1.5.4: the weak rational `Ioc ×ˢ Ioc` rectangle family is a semiring of
sets on `ℝ × ℝ`. -/
private theorem rationalIocRectangleFamily_isSetSemiring :
    IsSetSemiring (Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe) :=
  image2_prod_isSetSemiring rationalIocSetLe_isSetSemiring rationalIocSetLe_isSetSemiring

/-- Helper for Exercise 1.5.4: membership in the weak rational rectangle family is exactly a
four-endpoint rational `Ioc ×ˢ Ioc` description. -/
private theorem mem_rationalIocRectangleFamily_iff {s : Set (ℝ × ℝ)} :
    s ∈ Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe ↔
      ∃ a b c d : ℚ, a ≤ b ∧ c ≤ d ∧
        Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.Ioc (c : ℝ) (d : ℝ) = s := by
  constructor
  · intro hs
    -- Unpack the two one-dimensional interval witnesses carried by `Set.image2`.
    simp only [Set.mem_image2, rationalIocSetLe] at hs
    rcases hs with ⟨u, ⟨a, b, hab, hu⟩, v, ⟨c, d, hcd, hv⟩, huv⟩
    refine ⟨a, b, c, d, hab, hcd, ?_⟩
    calc
      Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.Ioc (c : ℝ) (d : ℝ) = u ×ˢ v := by rw [hu, hv]
      _ = s := huv
  · rintro ⟨a, b, c, d, hab, hcd, rfl⟩
    -- Package the two rational interval witnesses back into `Set.image2`.
    simp only [Set.mem_image2, rationalIocSetLe]
    exact ⟨Set.Ioc (a : ℝ) (b : ℝ), ⟨a, b, hab, rfl⟩,
      Set.Ioc (c : ℝ) (d : ℝ), ⟨c, d, hcd, rfl⟩, rfl⟩

/-- Helper for Exercise 1.5.4: the weak rational `Ioc` family still spans `ℝ` countably. -/
private theorem rationalIocSetLe_isCountablySpanning :
    IsCountablySpanning rationalIocSetLe := by
  -- The same symmetric interval cover works for the weak-endpoint family.
  refine ⟨fun n ↦ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    refine ⟨-(n + 1 : ℚ), n + 1, by linarith, ?_⟩
    congr 1 <;> norm_num
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : x ∈ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        constructor
        · linarith
        · linarith
      exact Set.mem_iUnion.2 ⟨n, hmem⟩

/-- Helper for Exercise 1.5.4: allowing degenerate rational `Ioc` intervals does not change the
generated Borel `σ`-algebra on `ℝ`. -/
private theorem borel_real_eq_generateFrom_rationalIocLe :
    borel ℝ = MeasurableSpace.generateFrom rationalIocSetLe := by
  -- The only new weak-endpoint intervals are empty, so the generated `σ`-algebra is unchanged.
  refine le_antisymm ?_ ?_
  · rw [borel_real_eq_generateFrom_rational_ioc]
    exact MeasurableSpace.generateFrom_mono fun s hs ↦ by
      rcases hs with ⟨a, b, hab, rfl⟩
      exact ⟨a, b, hab.le, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases hs with ⟨a, b, hab, rfl⟩
    rcases lt_or_eq_of_le hab with hab' | rfl
    · exact measurableSet_Ioc
    · simp

/-- Helper for Exercise 1.5.4: rational `Ioc ×ˢ Ioc` rectangles generate
`borel (ℝ × ℝ)`. -/
private theorem borel_prod_eq_generateFrom_rationalIocRectangles :
    borel (ℝ × ℝ) =
      MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·)
          {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}
          {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}) := by
  -- Combine the one-dimensional rational `Ioc` generators through the product `σ`-algebra API.
  have hgen :
      MeasurableSpace.generateFrom
          (Set.image2 (· ×ˢ ·)
            {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}
            {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}) =
        Prod.instMeasurableSpace := by
    exact generateFrom_eq_prod
      borel_real_eq_generateFrom_rational_ioc.symm
      borel_real_eq_generateFrom_rational_ioc.symm
      rationalIocSet_isCountablySpanning rationalIocSet_isCountablySpanning
  have hborel : Prod.instMeasurableSpace = borel (ℝ × ℝ) := by
    exact le_antisymm prod_le_borel_prod OpensMeasurableSpace.borel_le
  calc
    borel (ℝ × ℝ) = Prod.instMeasurableSpace := by simpa using hborel.symm
    _ = MeasurableSpace.generateFrom
          (Set.image2 (· ×ˢ ·)
            {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}
            {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Set.Ioc (a : ℝ) (b : ℝ) = S}) := hgen.symm

/-- Helper for Exercise 1.5.4: the weak rational `Ioc ×ˢ Ioc` rectangles also generate
`borel (ℝ × ℝ)`. -/
private theorem borel_prod_eq_generateFrom_rationalIocRectanglesLe :
    borel (ℝ × ℝ) =
      MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe) := by
  -- First replace each one-dimensional strict generator by the semiring-friendly weak family.
  have hgen :
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe) =
        Prod.instMeasurableSpace := by
    exact generateFrom_eq_prod
      borel_real_eq_generateFrom_rationalIocLe.symm
      borel_real_eq_generateFrom_rationalIocLe.symm
      rationalIocSetLe_isCountablySpanning
      rationalIocSetLe_isCountablySpanning
  have hborel : Prod.instMeasurableSpace = borel (ℝ × ℝ) := by
    exact le_antisymm prod_le_borel_prod OpensMeasurableSpace.borel_le
  calc
    borel (ℝ × ℝ) = Prod.instMeasurableSpace := by simpa using hborel.symm
    _ = MeasurableSpace.generateFrom
          (Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe) := hgen.symm

/-- Helper for Exercise 1.5.4: the symmetric rational rectangles used later for the spanning
cover do belong to the weak rational rectangle family. -/
private theorem rationalIocRectangleCover_mem (n : ℕ) :
    Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ∈
      Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe := by
  -- Rewrite the symmetric box through rational endpoints and use the membership characterization.
  rw [mem_rationalIocRectangleFamily_iff]
  refine ⟨-(n + 1 : ℚ), n + 1, -(n + 1 : ℚ), n + 1, by linarith, by linarith, ?_⟩
  have hbox : Set.Ioc ((-(n + 1 : ℚ) : ℝ)) (n + 1 : ℝ) = Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
    congr 1
    norm_num
  simpa using congrArg (fun t : Set ℝ ↦ t ×ˢ t) hbox

/-- Helper for Exercise 1.5.4: when the upper corner is rational, every rectangle in the
expanding lower-orthant approximation already lies in the weak rational rectangle semiring. -/
private theorem rationalExpandingIocRectangle_mem
    (q₁ q₂ : ℚ) (n : ℕ) :
    Set.Ioc ((q₁ : ℝ) - (n + 1 : ℝ)) (q₁ : ℝ) ×ˢ
        Set.Ioc ((q₂ : ℝ) - (n + 1 : ℝ)) (q₂ : ℝ) ∈
      Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe := by
  -- Proof comment: subtracting an integer from a rational endpoint stays rational, so each
  -- approximating box is still one of the semiring generators.
  rw [mem_rationalIocRectangleFamily_iff]
  refine ⟨q₁ - (n + 1 : ℚ), q₁, q₂ - (n + 1 : ℚ), q₂, by linarith, by linarith, ?_⟩
  have hq₁ :
      Set.Ioc (((q₁ - (n + 1 : ℚ)) : ℚ) : ℝ) (q₁ : ℝ) =
        Set.Ioc ((q₁ : ℝ) - (n + 1 : ℝ)) (q₁ : ℝ) := by
    congr 1
    norm_num
  have hq₂ :
      Set.Ioc (((q₂ - (n + 1 : ℚ)) : ℚ) : ℝ) (q₂ : ℝ) =
        Set.Ioc ((q₂ : ℝ) - (n + 1 : ℝ)) (q₂ : ℝ) := by
    congr 1
    norm_num
  rw [hq₁, hq₂]

/-- Helper for Exercise 1.5.4: the symmetric rational rectangles already cover `ℝ × ℝ`. -/
private theorem rationalIocRectangleCover_spanning :
    (⋃ n : ℕ, Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ
      Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ)) = Set.univ := by
  -- Choose one symmetric box large enough to contain both coordinates.
  ext x
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨n, hn⟩ := exists_nat_gt (max |x.1| |x.2|)
    have hx₁' : -(n : ℝ) < x.1 ∧ x.1 < (n : ℝ) := by
      have h₁ : |x.1| < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      simpa [abs_lt] using h₁
    have hx₂' : -(n : ℝ) < x.2 ∧ x.2 < (n : ℝ) := by
      have h₂ : |x.2| < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      simpa [abs_lt] using h₂
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    constructor
    · constructor
      · linarith
      · linarith
    · constructor
      · linarith
      · linarith

/-- Helper for Exercise 1.5.4: a lower orthant in `ℝ × ℝ` is the union of expanding
half-open rectangles with fixed upper corner. -/
private theorem iic_eq_iUnion_prodIoc_expanding (x : ℝ × ℝ) :
    Set.Iic x =
      ⋃ n : ℕ, Set.Ioc (x.1 - (n + 1 : ℝ)) x.1 ×ˢ Set.Ioc (x.2 - (n + 1 : ℝ)) x.2 := by
  -- Expand each one-dimensional lower orthant and then synchronize the two indices with `max`.
  ext y
  constructor
  · intro hy
    have hy₁ : y.1 ∈ ⋃ n : ℕ, Set.Ioc (x.1 - (n + 1 : ℝ)) x.1 := by
      rw [← iic_eq_iUnion_ioc_expanding x.1]
      exact hy.1
    have hy₂ : y.2 ∈ ⋃ n : ℕ, Set.Ioc (x.2 - (n + 1 : ℝ)) x.2 := by
      rw [← iic_eq_iUnion_ioc_expanding x.2]
      exact hy.2
    rcases Set.mem_iUnion.1 hy₁ with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.1 hy₂ with ⟨n₂, hn₂⟩
    refine Set.mem_iUnion.2 ⟨max n₁ n₂, ?_⟩
    refine ⟨?_, ?_⟩
    · constructor
      · have hle : (n₁ : ℝ) ≤ max n₁ n₂ := by exact_mod_cast le_max_left n₁ n₂
        linarith [hn₁.1, hle]
      · exact hn₁.2
    · constructor
      · have hle : (n₂ : ℝ) ≤ max n₁ n₂ := by exact_mod_cast le_max_right n₁ n₂
        linarith [hn₂.1, hle]
      · exact hn₂.2
  · intro hy
    rcases Set.mem_iUnion.1 hy with ⟨n, hn⟩
    exact ⟨hn.1.2, hn.2.2⟩

/-- Helper for Exercise 1.5.4: for every real `x` and accuracy scale `1 / (n + 1)`, one can pick
a rational number strictly above `x` but within that distance. -/
private theorem exists_rat_gt_lt_add_inv_natAddOne (x : ℝ) (n : ℕ) :
    ∃ q : ℚ, x < q ∧ (q : ℝ) < x + (n + 1 : ℝ)⁻¹ := by
  have hpos : 0 < (n + 1 : ℝ)⁻¹ := by positivity
  rcases exists_rat_btwn (show x < x + (n + 1 : ℝ)⁻¹ by linarith) with ⟨q, hq₁, hq₂⟩
  exact ⟨q, hq₁, hq₂⟩

/-- Helper for Exercise 1.5.4: a canonical rational approximation of `x` from above. -/
private noncomputable def rationalUpperApprox (x : ℝ) (n : ℕ) : ℚ :=
  Classical.choose (exists_rat_gt_lt_add_inv_natAddOne x n)

/-- Helper for Exercise 1.5.4: the chosen rational approximation stays above `x`. -/
private theorem lt_rationalUpperApprox (x : ℝ) (n : ℕ) :
    x < (rationalUpperApprox x n : ℝ) :=
  (Classical.choose_spec (exists_rat_gt_lt_add_inv_natAddOne x n)).1

/-- Helper for Exercise 1.5.4: the chosen rational approximation lies within `1 / (n + 1)` of
`x` from above. -/
private theorem rationalUpperApprox_lt_add_inv_natAddOne (x : ℝ) (n : ℕ) :
    (rationalUpperApprox x n : ℝ) < x + (n + 1 : ℝ)⁻¹ :=
  (Classical.choose_spec (exists_rat_gt_lt_add_inv_natAddOne x n)).2

/-- Helper for Exercise 1.5.4: the rational approximations converge to `x` from the right. -/
private theorem tendsto_rationalUpperApprox (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (rationalUpperApprox x n : ℝ)) atTop (𝓝 x) := by
  have hnonneg :
      ∀ n : ℕ, 0 ≤ (rationalUpperApprox x n : ℝ) - x := by
    intro n
    exact sub_nonneg.mpr (lt_rationalUpperApprox x n).le
  have hle :
      ∀ n : ℕ, (rationalUpperApprox x n : ℝ) - x ≤ 1 / (n + 1 : ℝ) := by
    intro n
    have haux :
        (rationalUpperApprox x n : ℝ) < 1 / (n + 1 : ℝ) + x := by
      simpa [add_comm] using rationalUpperApprox_lt_add_inv_natAddOne x n
    have hlt : (rationalUpperApprox x n : ℝ) - x < 1 / (n + 1 : ℝ) :=
      (sub_lt_iff_lt_add).2 haux
    exact hlt.le
  have hdiff :
      Tendsto (fun n : ℕ ↦ (rationalUpperApprox x n : ℝ) - x) atTop (𝓝 0) :=
    squeeze_zero hnonneg hle tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff.const_add x

/-- Helper for Exercise 1.5.4: once the rectangle increment is bundled as a sigma-subadditive
content on the weak rational rectangle semiring, the Carathéodory extension and the right
continuity of cdfs produce the desired probability measure. -/
private theorem existsProbabilityMeasure_of_rectangleAddContent
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F)
    (m : AddContent ℝ≥0∞ (Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe))
    (hm_sigma : m.IsSigmaSubadditive)
    (hm_apply : ∀ ⦃a b c d : ℚ⦄, a ≤ b → c ≤ d →
      m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.Ioc (c : ℝ) (d : ℝ)) =
        ENNReal.ofReal ((F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c))) :
    ∃ μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Set.Iic x) := by
  -- TODO: once the rectangle premeasure is available, apply Theorem 1.53 on the weak rational
  -- rectangle semiring, prove the lower-orthant formula first on rational upper corners via the
  -- expanding `Ioc ×ˢ Ioc` approximation, and then transport it to arbitrary corners using
  -- right continuity and rational upper approximations.
  sorry

/-- Helper for Exercise 1.5.4: a bivariate distribution function is realized by some
probability measure on `ℝ × ℝ`. -/
private theorem existsProbabilityMeasure_of_isBivariateDistributionFunctionCore
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) (hF : IsBivariateDistributionFunction F) :
    ∃ μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Set.Iic x) := by
  let rectangleFamily :=
    Set.image2 (· ×ˢ ·) rationalIocSetLe rationalIocSetLe
  have hRectangleFamily : IsSetSemiring rectangleFamily :=
    rationalIocRectangleFamily_isSetSemiring
  have hCoverMem : ∀ n : ℕ,
      Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ∈
        rectangleFamily :=
    rationalIocRectangleCover_mem
  have hCoverSpanning : (⋃ n : ℕ,
      Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ)) = Set.univ :=
    rationalIocRectangleCover_spanning
  have hGenerate :
      borel (ℝ × ℝ) = MeasurableSpace.generateFrom rectangleFamily :=
    borel_prod_eq_generateFrom_rationalIocRectanglesLe
  have hPackageFromMeasure :
      (∃ μ0 : Measure (ℝ × ℝ), ∀ x : ℝ × ℝ, μ0 (Set.Iic x) = ENNReal.ofReal (F x : ℝ)) →
        ∃ μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Set.Iic x) := by
    rintro ⟨μ0, hμ0⟩
    -- The diagonal lower orthants exhaust the whole space, so the given lower-orthant formula
    -- already forces the total mass to be `1`.
    have hdiagMap : Tendsto (fun q : ℝ ↦ (q, q)) atTop (atTop : Filter (ℝ × ℝ)) := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_id.prodMk tendsto_id
    have hFdiag : Tendsto (fun q : ℝ ↦ (F (q, q) : ℝ)) atTop (𝓝 1) :=
      hF.tendsto_atTop_one.comp hdiagMap
    have hdiagMass : Tendsto (fun q : ℝ ↦ μ0 (Set.Iic (q, q))) atTop (𝓝 (1 : ENNReal)) := by
      -- Rewrite the diagonal lower-orthant masses through the assumed cdf identity.
      have hdiagMass' :
          Tendsto (fun q : ℝ ↦ ENNReal.ofReal (F (q, q) : ℝ)) atTop
            (𝓝 (1 : ENNReal)) := by
          simpa using
            (ENNReal.tendsto_ofReal hFdiag :
              Tendsto (fun q : ℝ ↦ ENNReal.ofReal (F (q, q) : ℝ)) atTop
                (𝓝 (ENNReal.ofReal (1 : ℝ))))
      simpa [hμ0] using hdiagMass'
    have hunivDiag : (⋃ q : ℝ, Set.Iic (q, q)) = Set.univ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        refine Set.mem_iUnion.2 ⟨max z.1 z.2, ?_⟩
        exact ⟨le_max_left _ _, le_max_right _ _⟩
    have hdiagUnion :
        Tendsto (fun q : ℝ ↦ μ0 (Set.Iic (q, q))) atTop
          (𝓝 (μ0 (⋃ q : ℝ, Set.Iic (q, q)))) := by
      -- Continuity from below identifies the total mass with the diagonal exhaustion.
      apply tendsto_measure_iUnion_atTop
      intro a b hab
      exact Set.Iic_subset_Iic.mpr ⟨hab, hab⟩
    have hμ0_univ : μ0 Set.univ = 1 := by
      rw [hunivDiag] at hdiagUnion
      exact tendsto_nhds_unique hdiagUnion hdiagMass
    let μ : ProbabilityMeasure (ℝ × ℝ) := ⟨μ0, ⟨by simpa using hμ0_univ⟩⟩
    refine ⟨μ, ?_⟩
    intro x
    -- Convert the `ENNReal` lower-orthant identity back to the real-valued cdf convention of
    -- `ProbabilityMeasure`.
    change (F x : ℝ) = μ0.real (Set.Iic x)
    rw [measureReal_def, hμ0 x, ENNReal.toReal_ofReal]
    exact (F x).2.1
  have hRectangleContent :
      ∃ m : AddContent ℝ≥0∞ rectangleFamily,
        m.IsSigmaSubadditive ∧
          (∀ ⦃a b c d : ℚ⦄, a ≤ b → c ≤ d →
            m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.Ioc (c : ℝ) (d : ℝ)) =
              ENNReal.ofReal ((F (b, d) : ℝ) - F (b, c) - F (a, d) + F (a, c))) := by
    -- Route correction: the extension-and-transport block is now factored into
    -- `existsProbabilityMeasure_of_rectangleAddContent`.
    -- TODO: use `rectangleIncrement_split_fst` and `rectangleIncrement_split_snd` inside a boxed
    -- common-strip partition theorem for finite disjoint rational rectangle families; after that,
    -- package the resulting finitely additive content and prove sigma-subadditivity via
    -- `supClosure` on the ring closure.
    have _hRectangleFamily_use : IsSetSemiring rectangleFamily := hRectangleFamily
    have _hCoverMem_use : ∀ n : ℕ,
        Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ∈
          rectangleFamily := hCoverMem
    have _hCoverSpanning_use : (⋃ n : ℕ,
        Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) ×ˢ Set.Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ)) = Set.univ :=
      hCoverSpanning
    have _hGenerate_use :
        borel (ℝ × ℝ) = MeasurableSpace.generateFrom rectangleFamily := hGenerate
    sorry
  rcases hRectangleContent with ⟨m, hm_sigma, hm_apply⟩
  exact existsProbabilityMeasure_of_rectangleAddContent F hF m hm_sigma hm_apply

-- Proof sketch: for the forward implication, use monotonicity and right-continuity of lower-orthant
-- masses and compute rectangle increments by inclusion-exclusion. For the reverse implication,
-- transport uniqueness through `Fin 2 → ℝ`; `Measure.ext_of_Iic` is only the one-dimensional API.
/-- Exercise 1.5.4: a function `F : ℝ² → [0,1]` is the distribution function of a uniquely
determined probability measure on `(ℝ², 𝓑(ℝ²))` if and only if it is monotone increasing,
right-continuous, satisfies `F (-x) → 0` and `F x → 1` as `x → ∞` in the product order on
`ℝ²`, and is 2-increasing on rectangles. -/
theorem existsUnique_probabilityMeasure_with_bivariateDistributionFunction_iff
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) :
    (∃! μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Iic x)) ↔
      IsBivariateDistributionFunction F := by
  constructor
  · rintro ⟨μ, hμ, -⟩
    -- Identify `F` with the lower-orthant cdf of `μ`, then reuse the already-proved instance.
    have hF_eq :
        F = bivariateMeasureDistributionFunction μ := by
      funext x
      apply Subtype.ext
      simpa [bivariateMeasureDistributionFunction_apply] using hμ x
    rw [hF_eq]
    infer_instance
  · intro hF
    -- Reduce the reverse implication to the existence lemma and the lower-orthant
    -- uniqueness theorem proved above.
    obtain ⟨μ, hμ⟩ := existsProbabilityMeasure_of_isBivariateDistributionFunctionCore F hF
    refine ⟨μ, hμ, ?_⟩
    intro ν hν
    symm
    apply probabilityMeasure_eq_of_bivariateDistributionFunction
    intro x
    have hμx : μ (Set.Iic x) = (F x : ℝ) := (hμ x).symm
    have hνx : ν (Set.Iic x) = (F x : ℝ) := (hν x).symm
    exact_mod_cast hμx.trans hνx.symm
