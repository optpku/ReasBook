/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {F : Type v}
variable [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
variable [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]

/-- The rate function obtained by contracting `I` along `m`, defined by taking the infimum of `I`
on each fiber of `m`. -/
def contractedRateFunction (m : E → F) (I : E → ENNReal) : F → ENNReal :=
  fun y ↦ sInf (I '' (m ⁻¹' {y}))

-- Proof sketch: unfold `contractedRateFunction`; the right-hand side is exactly the infimum of
-- `I` over the singleton fiber `m ⁻¹' {y}`.
/-- Expanding `contractedRateFunction m I` gives the infimum of `I` over the fiber of `m` above
`y`. -/
theorem contractedRateFunction_def (m : E → F) (I : E → ENNReal) (y : F) :
    contractedRateFunction m I y = sInf (I '' (m ⁻¹' {y})) := by
  -- Proof comment: this is just the defining equation of `contractedRateFunction`.
  rfl

-- Proof sketch: this is the pushforward family `μ_ε ∘ m⁻¹`, written with `ProbabilityMeasure.map`.
/-- The image family `μ_ε ∘ m⁻¹` of a positive-parameter family of probability measures under a
continuous map `m`. -/
def mappedPositiveProbabilityFamily
    (μ : PositiveProbabilityFamily E) (m : E → F) (hm : Continuous m) :
    PositiveProbabilityFamily F :=
  fun ε ↦ ProbabilityMeasure.map (μ ε) hm.measurable.aemeasurable

-- Proof sketch: unfold `mappedPositiveProbabilityFamily`; the value at `ε` is the pushforward
-- probability measure of `μ ε` along `m`.
/-- Evaluating `mappedPositiveProbabilityFamily μ m hm` at `ε > 0` gives the image measure
`μ_ε ∘ m⁻¹`. -/
theorem mappedPositiveProbabilityFamily_apply
    (μ : PositiveProbabilityFamily E) (m : E → F) (hm : Continuous m)
    (ε : PositiveParameter) :
    mappedPositiveProbabilityFamily μ m hm ε =
      ProbabilityMeasure.map (μ ε) hm.measurable.aemeasurable := by
  -- Proof comment: evaluating the family at `ε` unfolds the pushforward definition.
  rfl

/-- Helper for the contraction principle: coercing an `sInf` of `ℝ≥0∞` values to `EReal`
agrees with taking the `sInf` after coercion. -/
private theorem ereal_sInf_coe_ennreal_image (S : Set ENNReal) :
    sInf (((↑) : ENNReal → EReal) '' S) = ((sInf S : ENNReal) : EReal) := by
  -- Proof comment: show that the coerced `sInf` is the greatest lower bound of the coerced set.
  have hImage :
      IsGLB (((↑) : ENNReal → EReal) '' S) ((sInf S : ENNReal) : EReal) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact_mod_cast (isGLB_sInf S).1 hx
    · intro z hz
      have hzENNReal : z.toENNReal ≤ sInf S := by
        refine (isGLB_sInf S).2 ?_
        intro x hx
        simpa using EReal.toENNReal_le_toENNReal (hz ⟨x, hx, rfl⟩)
      calc
        z ≤ (z.toENNReal : EReal) := by
          rw [EReal.coe_toENNReal_eq_max]
          exact le_max_right _ _
        _ ≤ ((sInf S : ENNReal) : EReal) := by
          exact_mod_cast hzENNReal
  exact hImage.sInf_eq

/-- The open-set lower bound and closed-set upper bound for the `ε ↓ 0` large deviations
asymptotics of a positive-parameter family of probability measures with rate function `I`. -/
def HasLargeDeviationsBounds
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) : Prop :=
  (∀ ⦃U : Set E⦄, IsOpen U →
      -sInf ((fun x ↦ (I x : EReal)) '' U) ≤
        Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U)
          positiveParameterFilter) ∧
    ∀ ⦃C : Set E⦄, IsClosed C →
      Filter.limsup (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id C)
          positiveParameterFilter ≤
        -sInf ((fun x ↦ (I x : EReal)) '' C)

/-- Helper for the contraction principle: the mapped family assigns to a measurable set
exactly the original mass of its preimage. -/
private theorem mappedPositiveProbabilityFamily_apply_set
    (μ : PositiveProbabilityFamily E) (m : E → F) (hm : Continuous m)
    (ε : PositiveParameter) {s : Set F} (hs : MeasurableSet s) :
    (((mappedPositiveProbabilityFamily μ m hm) ε : ProbabilityMeasure F) : Measure F) s =
      (μ ε : Measure E) (m ⁻¹' s) := by
  -- Proof comment: evaluate the pushed-forward probability measure on a measurable target set.
  rw [mappedPositiveProbabilityFamily_apply, ProbabilityMeasure.map_apply' _ _ hs]

/-- Helper for the contraction principle: the contracted rate at a point is bounded above
by the original rate at every point in the corresponding fiber. -/
private theorem contractedRateFunction_le_of_memFiber
    (m : E → F) (I : E → ENNReal) (x : E) :
    contractedRateFunction m I (m x) ≤ I x := by
  -- Proof comment: the point `x` itself belongs to the fiber over `m x`.
  rw [contractedRateFunction_def]
  exact sInf_le ⟨x, by simp, rfl⟩

/-- Helper for the contraction principle: pushing forward the scaled logarithmic mass along
`m` simply replaces a target set by its preimage. -/
private theorem scaledLogMassAlong_mapped_eq
    (μ : PositiveProbabilityFamily E) (m : E → F) (hm : Continuous m)
    {s : Set F} (hs : MeasurableSet s) :
    scaledLogMassAlong
        (fun ε ↦ (((mappedPositiveProbabilityFamily μ m hm) ε : ProbabilityMeasure F) : Measure F))
        id s =
      scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (m ⁻¹' s) := by
  -- Proof comment: pointwise, the logarithmic mass only sees the target set through its preimage.
  funext ε
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def,
    mappedPositiveProbabilityFamily_apply_set μ m hm ε hs]

/-- Helper for the contraction principle: the infimum of the contracted rate over a set
agrees with the infimum of the original rate over its preimage. -/
private theorem sInf_contractedRateFunction_image_eq_preimage
    (m : E → F) (I : E → ENNReal) (s : Set F) :
    sInf ((fun y ↦ (contractedRateFunction m I y : EReal)) '' s) =
      sInf ((fun x ↦ (I x : EReal)) '' (m ⁻¹' s)) := by
  -- Proof comment: compare the two infima in `ℝ≥0∞` first, then coerce back to `EReal`.
  have hCore :
      sInf (contractedRateFunction m I '' s) = sInf (I '' (m ⁻¹' s)) := by
    refine le_antisymm ?_ ?_
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact
        (sInf_le (show contractedRateFunction m I (m x) ∈ contractedRateFunction m I '' s from
          ⟨m x, hx, rfl⟩)).trans
          (contractedRateFunction_le_of_memFiber m I x)
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rw [contractedRateFunction_def]
      refine le_sInf ?_
      intro w hw
      rcases hw with ⟨x, hx, rfl⟩
      have hxy : m x = y := by simpa using hx
      exact sInf_le ⟨x, by simpa [Set.mem_preimage, hxy] using hy, rfl⟩
  -- Proof comment: the coercion helper turns the `ℝ≥0∞` infimum identity into the desired
  -- `EReal` equality.
  have hLeftImage :
      (fun y ↦ (contractedRateFunction m I y : EReal)) '' s =
        ((↑) : ENNReal → EReal) '' (contractedRateFunction m I '' s) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨contractedRateFunction m I y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hRightImage :
      (fun x ↦ (I x : EReal)) '' (m ⁻¹' s) =
        ((↑) : ENNReal → EReal) '' (I '' (m ⁻¹' s)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨I x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hLeftImage, hRightImage, ereal_sInf_coe_ennreal_image, ereal_sInf_coe_ennreal_image, hCore]

/-- Helper for the contraction principle: the open-set lower bound transfers to the mapped
family after rewriting along preimages. -/
private theorem mappedFamily_openLowerBound
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) {U : Set F} (hU : IsOpen U) :
    -sInf ((fun y ↦ (contractedRateFunction m I y : EReal)) '' U) ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun ε ↦
            (((mappedPositiveProbabilityFamily μ m hm) ε : ProbabilityMeasure F) : Measure F))
          id U)
        positiveParameterFilter := by
  -- Proof comment: rewrite both the logarithmic mass and the rate infimum to the source-space
  -- preimage, then apply the source open-set lower bound.
  have hPreimageOpen : IsOpen (m ⁻¹' U) := IsOpen.preimage hm hU
  simpa [scaledLogMassAlong_mapped_eq μ m hm hU.measurableSet,
    sInf_contractedRateFunction_image_eq_preimage m I U] using
    hμ.open_lower_bound hPreimageOpen

/-- Helper for the contraction principle: the closed-set upper bound transfers to the mapped
family after rewriting along preimages. -/
private theorem mappedFamily_closedUpperBound
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) {C : Set F} (hC : IsClosed C) :
    Filter.limsup
        (scaledLogMassAlong
          (fun ε ↦
            (((mappedPositiveProbabilityFamily μ m hm) ε : ProbabilityMeasure F) : Measure F))
          id C)
        positiveParameterFilter ≤
      -sInf ((fun y ↦ (contractedRateFunction m I y : EReal)) '' C) := by
  -- Proof comment: the closed-set upper bound transports in the same way as the open-set lower
  -- bound, but with limsup and the reversed inequality.
  have hPreimageClosed : IsClosed (m ⁻¹' C) := IsClosed.preimage hm hC
  simpa [scaledLogMassAlong_mapped_eq μ m hm hC.measurableSet,
    sInf_contractedRateFunction_image_eq_preimage m I C] using
    hμ.closed_upper_bound hPreimageClosed

/-- Helper for the contraction principle: for every finite level `a`, the contracted sublevel set
`{y | contractedRateFunction m I y ≤ a}` is exactly the image of the source sublevel
`{x | I x ≤ a}`. -/
private theorem contractedRateFunction_preimage_Iic_eq_image_sublevel
    [T2Space F]
    (m : E → F) (I : E → ENNReal)
    (hI_good : IsGoodRateFunction I) (hm : Continuous m) (a : ENNReal) (ha : a ≠ ⊤) :
    contractedRateFunction m I ⁻¹' Set.Iic a = m '' (I ⁻¹' Set.Iic a) := by
  ext y
  constructor
  · intro hy
    change contractedRateFunction m I y ≤ a at hy
    let b : NNReal := (a + 1).toNNReal
    have hFiniteSucc : a + 1 ≠ ⊤ := by
      exact ENNReal.add_ne_top.2 ⟨ha, by simp⟩
    have hb_coe : (b : ENNReal) = a + 1 := by
      exact ENNReal.coe_toNNReal hFiniteSucc
    have hy_lt_b : contractedRateFunction m I y < (b : ENNReal) := by
      have ha_ne_add_one : a ≠ a + 1 := by
        intro hEq
        have hEqReal : a.toReal = (a + 1).toReal := congrArg ENNReal.toReal hEq
        rw [ENNReal.toReal_add ha (by simp)] at hEqReal
        norm_num at hEqReal
      have ha_lt : a < a + 1 := by
        exact lt_of_le_of_ne le_self_add ha_ne_add_one
      exact lt_of_le_of_lt hy (by simpa [hb_coe] using ha_lt)
    have hWitness :
        ∃ x ∈ m ⁻¹' ({y} : Set F), I x < (b : ENNReal) := by
      rw [contractedRateFunction_def] at hy_lt_b
      rcases sInf_lt_iff.mp hy_lt_b with ⟨z, hz, hzlt⟩
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hx, hzlt⟩
    let K : Set E := (I ⁻¹' Set.Iic (b : ENNReal)) ∩ (m ⁻¹' ({y} : Set F))
    have hK_nonempty : K.Nonempty := by
      rcases hWitness with ⟨x, hxFiber, hxlt⟩
      exact ⟨x, ⟨hxlt.le, hxFiber⟩⟩
    have hFiberClosed : IsClosed (m ⁻¹' ({y} : Set F)) :=
      IsClosed.preimage hm isClosed_singleton
    have hK_compact : IsCompact K := by
      exact (hI_good.isCompact_sublevel b).inter_right hFiberClosed
    have hK_lsc : LowerSemicontinuousOn I K :=
      hI_good.lowerSemicontinuous.lowerSemicontinuousOn K
    obtain ⟨x₀, hx₀K, hx₀Min⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hK_nonempty hK_compact hK_lsc
    have hx₀Fiber : x₀ ∈ m ⁻¹' ({y} : Set F) := hx₀K.2
    have hx₀Eq : m x₀ = y := by
      simpa using hx₀Fiber
    have hx₀LeB : I x₀ ≤ (b : ENNReal) := hx₀K.1
    have hx₀LeA : I x₀ ≤ a := by
      by_contra hx₀_not
      have hx₀_gt : a < I x₀ := lt_of_not_ge hx₀_not
      have hContr_lt : contractedRateFunction m I y < I x₀ := lt_of_le_of_lt hy hx₀_gt
      rw [contractedRateFunction_def] at hContr_lt
      rcases sInf_lt_iff.mp hContr_lt with ⟨z, hz, hzlt⟩
      rcases hz with ⟨x, hxFiber, rfl⟩
      have hxLeB : I x ≤ (b : ENNReal) := hzlt.le.trans hx₀LeB
      have hxK : x ∈ K := ⟨hxLeB, hxFiber⟩
      have hx₀_le_x : I x₀ ≤ I x := (isMinOn_iff.mp hx₀Min) x hxK
      exact (not_le_of_gt hzlt) hx₀_le_x
    exact ⟨x₀, by simpa [Set.mem_preimage] using hx₀LeA, hx₀Eq⟩
  · rintro ⟨x, hx, rfl⟩
    change contractedRateFunction m I (m x) ≤ a
    exact (contractedRateFunction_le_of_memFiber m I x).trans <|
      by simpa [Set.mem_preimage] using hx

-- Proof sketch: the finite sublevel sets of the contracted rate are continuous images of the
-- corresponding compact sublevel sets of the good rate `I`; in a Hausdorff target space this
-- makes the contracted rate a good rate function, hence in particular lower semicontinuous.
/-- If `I` is a good rate function, then its contraction along a continuous map is again a good
rate function. -/
theorem isGoodRateFunction_contractedRateFunction
    [T2Space F]
    (m : E → F) (I : E → ENNReal)
    (hI_good : IsGoodRateFunction I)
    (hm : Continuous m) :
    IsGoodRateFunction (contractedRateFunction m I) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: finite sublevels are compact images, hence closed in the Hausdorff target;
    -- the infinite sublevel is all of `F`.
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    by_cases ha : a = ⊤
    · simp [ha]
    · have hCompact :
          IsCompact ((contractedRateFunction m I) ⁻¹' Set.Iic a) := by
        rw [contractedRateFunction_preimage_Iic_eq_image_sublevel m I hI_good hm a ha]
        simpa [ENNReal.coe_toNNReal ha] using (hI_good.isCompact_sublevel a.toNNReal).image hm
      exact hCompact.isClosed
  · -- Proof comment: for finite levels coming from `ℝ≥0`, the sublevel identity directly
    -- identifies the contracted sublevel with a compact image.
    intro a
    rw [contractedRateFunction_preimage_Iic_eq_image_sublevel
      m I hI_good hm (a : ENNReal) (by simp)]
    exact (hI_good.isCompact_sublevel a).image hm

-- The direct preimage transport argument yields the open/closed LDP bounds for the mapped family.
/-- Helper for the contraction principle: continuity of `m` transports the large-deviations bounds
to the image family with the contracted rate function. -/
private theorem hasLargeDeviationsBounds_map_of_continuous
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) :
    HasLargeDeviationsBounds
      (mappedPositiveProbabilityFamily μ m hm)
      (contractedRateFunction m I) := by
  -- Proof comment: package the transported open and closed bounds into the bundled conjunction.
  constructor
  · intro U hU
    exact mappedFamily_openLowerBound μ I hμ m hm hU
  · intro C hC
    exact mappedFamily_closedUpperBound μ I hμ m hm hC

/-- Theorem 23.16: contraction principle. If `μ_ε` satisfies the chapter's large-deviations
principle with rate function `I` and `m : E → F` is continuous, then the image family
`μ_ε ∘ m⁻¹` satisfies the chapter's large-deviations principle with contracted rate function
`y ↦ inf_{x ∈ m⁻¹({y})} I x`. -/
theorem contractionPrinciple
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) :
    HasLargeDeviationsPrinciple
      (mappedPositiveProbabilityFamily μ m hm)
      (contractedRateFunction m I) := sorry

/-- Auxiliary unlabeled bridge: large-deviations bounds plus lower semicontinuity of the
contracted rate function give the chapter's bundled `HasLargeDeviationsPrinciple`. -/
theorem hasLargeDeviationsPrinciple_map_of_continuous
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (m : E → F) (hm : Continuous m)
    (hbounds : HasLargeDeviationsBounds
      (mappedPositiveProbabilityFamily μ m hm)
      (contractedRateFunction m I))
    (hcontracted_lsc : LowerSemicontinuous (contractedRateFunction m I)) :
    HasLargeDeviationsPrinciple
      (mappedPositiveProbabilityFamily μ m hm)
      (contractedRateFunction m I) := by
  -- Proof comment: `HasLargeDeviationsPrinciple` adds lower semicontinuity to the two bounds
  -- already bundled in `hbounds`.
  exact
    { lowerSemicontinuous := hcontracted_lsc
      open_lower_bound := hbounds.1
      closed_upper_bound := hbounds.2 }

/-- Auxiliary unlabeled good/Hausdorff specialization: if `I` is a good rate function and
`m : E → F` is continuous into a Hausdorff target space, then the image measures `μ_ε ∘ m⁻¹`
satisfy the chapter's bundled `HasLargeDeviationsPrinciple` with contracted rate function
`y ↦ inf_{x ∈ m⁻¹({y})} I x`; goodness of `I` supplies the needed lower semicontinuity of the
contracted rate. -/
theorem hasLargeDeviationsPrinciple_map_of_continuous_of_goodRateFunction
    [T2Space F]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hI_good : IsGoodRateFunction I)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) :
    HasLargeDeviationsPrinciple
      (mappedPositiveProbabilityFamily μ m hm)
      (contractedRateFunction m I) := by
  -- Proof comment: the mapped family already satisfies the transported bounds, and the good-rate
  -- hypothesis supplies the missing lower semicontinuity of the contracted rate.
  refine hasLargeDeviationsPrinciple_map_of_continuous μ I m hm ?_ ?_
  · exact hasLargeDeviationsBounds_map_of_continuous μ I hμ m hm
  · exact (isGoodRateFunction_contractedRateFunction m I hI_good hm).lowerSemicontinuous

end ProbabilityTheory
