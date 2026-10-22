/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6.Profile
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6.RealLine

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local instance instMeasurableSpaceLemma326 : MeasurableSpace E := borel E
local instance instBorelSpaceLemma326 : BorelSpace E := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: along the scalar parametrization `t ↦ t • g` of a one-dimensional
ambient space, the origin cut is exactly the nonpositive half-line. -/
private lemma smul_mem_cuttingHalfspace_origin_iff
    {g : E} (hg : g ≠ 0) {t : ℝ} :
    t • g ∈ cuttingHalfspace (0 : E) g ↔ t ≤ 0 := by
  -- Collapse the owner halfspace inequality to the sign of the scalar parameter `t`.
  rw [mem_cuttingHalfspace_iff]
  rw [sub_eq_add_neg, zero_add, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
  constructor
  · intro ht
    have hg_sq : 0 < ‖g‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
    nlinarith
  · intro ht
    have hg_sq : 0 ≤ ‖g‖ ^ 2 := sq_nonneg ‖g‖
    nlinarith

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: the scalar preimage of the origin cut is `(-∞, 0]`. -/
private lemma preimage_cuttingHalfspace_origin_eq_Iic
    {g : E} (hg : g ≠ 0) :
    (fun t : ℝ ↦ t • g) ⁻¹' cuttingHalfspace (0 : E) g = Set.Iic 0 := by
  -- Rewrite membership pointwise using the scalar halfspace description.
  ext t
  simpa using smul_mem_cuttingHalfspace_origin_iff (g := g) hg (t := t)

/-- Helper for Lemma 3.2.6: in a one-dimensional ambient space, Lebesgue volume is the scaled
pushforward of real-line volume along the scalar parametrization `t ↦ t • g`. -/
private lemma volume_eq_enorm_mul_volume_preimage_smul_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) {g : E} (hg : g ≠ 0) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ‖g‖ₑ * volume ((fun t : ℝ ↦ t • g) ⁻¹' s) := by
  -- Use the one-dimensional Haar-measure description and then evaluate the pushed-forward set.
  have hs_map_smul :
      NullMeasurableSet s (‖g‖ₑ • (Measure.map (fun t : ℝ ↦ t • g) volume)) := by
    simpa [MeasureTheory.volume_eq_of_finrank_eq_one (E := E) hdim (v := g) hg] using hs
  have hs_map :
      NullMeasurableSet s (Measure.map (fun t : ℝ ↦ t • g) volume) := by
    exact
      (nullMeasurableSet_smul_measure_iff
        (μ := Measure.map (fun t : ℝ ↦ t • g) volume)
        (s := s) (c := ‖g‖ₑ) (enorm_ne_zero.mpr hg)).mp hs_map_smul
  rw [MeasureTheory.volume_eq_of_finrank_eq_one (E := E) hdim (v := g) hg]
  rw [Measure.smul_apply, Measure.map_apply₀ (by fun_prop) hs_map]
  simp [smul_eq_mul]

/-- Helper for Lemma 3.2.6: the same one-dimensional pushforward description applies to the origin
cut, whose scalar preimage is the truncated set `A ∩ (-∞, 0]`. -/
private lemma originCut_volume_eq_enorm_mul_volume_preimage_inter_Iic_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) {g : E} (hg : g ≠ 0) {T : Set E}
    (hT : NullMeasurableSet T volume) :
    volume (T ∩ cuttingHalfspace (0 : E) g) =
      ‖g‖ₑ * volume (((fun t : ℝ ↦ t • g) ⁻¹' T) ∩ Set.Iic 0) := by
  have hpre :
      (fun t : ℝ ↦ t • g) ⁻¹' (T ∩ cuttingHalfspace (0 : E) g) =
        ((fun t : ℝ ↦ t • g) ⁻¹' T) ∩ Set.Iic 0 := by
    -- Rewrite the cut preimage pointwise using the scalar halfspace description.
    ext t
    simp [preimage_cuttingHalfspace_origin_eq_Iic (E := E) (g := g) hg]
  have hCutMeas : NullMeasurableSet (T ∩ cuttingHalfspace (0 : E) g) volume := by
    -- Intersect the null-measurable convex body with the closed origin cut.
    exact hT.inter (cuttingHalfspace_closed (xBar := (0 : E)) g).measurableSet.nullMeasurableSet
  rw [volume_eq_enorm_mul_volume_preimage_smul_of_finrank_eq_one
    (E := E) hdim hg hCutMeas]
  simp [hpre]

/-- Helper for Lemma 3.2.6: in the one-dimensional scalar parametrization `t ↦ t • g`, an origin-
centered convex body has scalar set average `0`. -/
private lemma scalarPreimage_setAverage_eq_zero_of_originCentered
    (hdim : Module.finrank ℝ E = 1) {T : Set E} {g : E} (hg : g ≠ 0)
    (hT_convex : Convex ℝ T) (hT_finite : volume T ≠ ⊤) (hT_pos : volume T ≠ 0)
    (hT_center : (⨍ z in T, z) = 0) :
    let A : Set ℝ := (fun t : ℝ ↦ t • g) ⁻¹' T
    (⨍ t in A, t) = 0 := by
  let A : Set ℝ := (fun t : ℝ ↦ t • g) ⁻¹' T
  have hT_meas : NullMeasurableSet T volume := hT_convex.nullMeasurableSet volume
  have hVolumeTransport :
      volume T = ‖g‖ₑ * volume A := by
    -- Transport the total mass of `T` to the scalar model cut out by `t ↦ t • g`.
    simpa [A] using
      volume_eq_enorm_mul_volume_preimage_smul_of_finrank_eq_one
        (E := E) hdim hg hT_meas
  have hA_finite : volume A ≠ ⊤ := by
    -- Finite mass on `T` forces finite mass on the scalar preimage as well.
    intro hA_top
    apply hT_finite
    rw [hVolumeTransport, hA_top]
    simp [enorm_ne_zero.mpr hg]
  have hA_pos : volume A ≠ 0 := by
    -- Positive mass on `T` also transports back to the scalar preimage.
    intro hA_zero
    apply hT_pos
    rw [hVolumeTransport, hA_zero, mul_zero]
  have hIntegralZero : ∫ z in T, z ∂(volume : Measure E) = 0 := by
    -- Convert the centered set average into a vanishing set integral on `T`.
    have hSetAverage :=
      MeasureTheory.measure_smul_setAverage
        (μ := (volume : Measure E)) (f := fun z : E ↦ z) (s := T) hT_finite
    rw [hT_center, smul_zero] at hSetAverage
    simpa using hSetAverage.symm
  have hIntegralTransport :
      ∫ z in T, z ∂(volume : Measure E) = ‖g‖ • ∫ t in A, t • g ∂(volume : Measure ℝ) := by
    -- Rewrite Lebesgue volume in dimension one as the pushforward of real-line volume.
    change ∫ z, z ∂((volume : Measure E).restrict T) =
        ‖g‖ • ∫ t in A, t • g ∂(volume : Measure ℝ)
    rw [MeasureTheory.volume_eq_of_finrank_eq_one (E := E) hdim (v := g) hg]
    rw [Measure.restrict_smul]
    rw [integral_smul_measure]
    have hMap :
        ∫ z in T, z ∂Measure.map (fun t : ℝ ↦ t • g) volume =
          ∫ t in A, t • g ∂(volume : Measure ℝ) := by
      -- Pull the set integral back through the closed embedding `t ↦ t • g`.
      simpa [A] using
        (isClosedEmbedding_smul_left (c := g) hg).setIntegral_map
          (μ := (volume : Measure ℝ)) (f := fun z : E ↦ z) (s := T)
    simpa using congrArg (fun x : E ↦ ‖g‖ • x) hMap
  have hVectorIntegralZero :
      ∫ t in A, t • g ∂(volume : Measure ℝ) = 0 := by
    -- The transported vector integral must vanish because the original integral does.
    have hScaledZero : ‖g‖ • ∫ t in A, t • g ∂(volume : Measure ℝ) = 0 := by
      rw [← hIntegralTransport]
      exact hIntegralZero
    exact (smul_eq_zero.mp hScaledZero).resolve_left (norm_ne_zero_iff.mpr hg)
  have hScalarIntegralZero :
      ∫ t in A, t ∂(volume : Measure ℝ) = 0 := by
    -- Pull the fixed vector `g` out of the integral and then cancel it.
    have hIntegralSmulConst :
        ∫ t in A, t • g ∂(volume : Measure ℝ) =
          (∫ t in A, t ∂(volume : Measure ℝ)) • g := by
      simpa using
        (integral_smul_const (μ := volume.restrict A) (f := fun t : ℝ ↦ t) g)
    rw [hIntegralSmulConst] at hVectorIntegralZero
    exact (smul_eq_zero.mp hVectorIntegralZero).resolve_right hg
  have hA_real_ne_zero : volume.real A ≠ 0 := by
    -- The scalar preimage has positive finite real-valued volume.
    exact ENNReal.toReal_ne_zero.mpr ⟨hA_pos, hA_finite⟩
  have hAverageSmul :=
    MeasureTheory.measure_smul_setAverage
      (μ := (volume : Measure ℝ)) (f := fun t : ℝ ↦ t) (s := A) hA_finite
  -- Clear the nonzero scalar volume factor to recover the scalar set average.
  rw [hScalarIntegralZero] at hAverageSmul
  exact (smul_eq_zero.mp hAverageSmul).resolve_left hA_real_ne_zero

/-- Helper for Lemma 3.2.6: translating a set by `-xBar` preserves its volume. -/
private lemma translatedSet_volume_eq (S : Set E) (xBar : E) :
    volume (((fun x : E ↦ x - xBar) '' S)) = volume S := by
  -- Use translation invariance of Lebesgue volume through the measurable equivalence
  -- `x ↦ x + xBar`.
  let e : E ≃ᵐ E := MeasurableEquiv.addRight (-xBar)
  have hmap : Measure.map e.symm volume = volume := by
    simpa [e] using (measurePreserving_add_right volume xBar).map_eq
  have hS := congrArg (fun μ : Measure E => μ S) hmap
  -- The inverse-image of `S` under the inverse translation is exactly the translated image.
  simp [e, sub_eq_add_neg] at hS ⊢

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: translating the retained halfspace cut by `-xBar` turns the affine
cut into the centered inequality `0 ≤ ⟪g, -z⟫`. -/
private lemma image_nonnegInnerCut_eq_centeredCut
    (S : Set E) (xBar g : E) :
    ((fun x : E ↦ x - xBar) '' (S ∩ {x | 0 ≤ inner ℝ g (xBar - x)})) =
      (((fun x : E ↦ x - xBar) '' S) ∩ {z | 0 ≤ inner ℝ g (-z)}) := by
  -- Rewrite membership in the translated image by unpacking the witness and simplifying the
  -- translated inner-product inequality.
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxCut⟩, rfl⟩
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    change 0 ≤ inner ℝ g (-(x - xBar))
    simpa [neg_sub, sub_eq_add_neg] using hxCut
  · rintro ⟨⟨x, hxS, rfl⟩, hzCut⟩
    refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
    change 0 ≤ inner ℝ g (-(x - xBar)) at hzCut
    simpa [neg_sub, sub_eq_add_neg] using hzCut

/-- Helper for Lemma 3.2.6: the centroid cut and its translated centered cut have the same
volume. -/
private lemma volume_centroidCut_eq_volume_centeredCut
    (S : Set E) (xBar g : E) :
    volume (S ∩ {x | 0 ≤ inner ℝ g (xBar - x)}) =
      volume (((fun x : E ↦ x - xBar) '' S) ∩ {z | 0 ≤ inner ℝ g (-z)}) := by
  -- Translate the whole cut by `-xBar`, then identify the image with the centered halfspace cut.
  calc
    volume (S ∩ {x | 0 ≤ inner ℝ g (xBar - x)}) =
        volume (((fun x : E ↦ x - xBar) '' (S ∩ {x | 0 ≤ inner ℝ g (xBar - x)}))) := by
      simpa using
        (translatedSet_volume_eq (S := S ∩ {x | 0 ≤ inner ℝ g (xBar - x)}) xBar).symm
    _ =
        volume (((fun x : E ↦ x - xBar) '' S) ∩ {z | 0 ≤ inner ℝ g (-z)}) := by
      rw [image_nonnegInnerCut_eq_centeredCut]

/-- Helper for Lemma 3.2.6: translating a set by `-xBar` transports its set average to the
average of `x ↦ x - xBar` on the original set. -/
private lemma setAverage_translated_image_eq_setAverage_sub
    (S : Set E) (xBar : E) :
    (⨍ z in ((fun x : E ↦ x - xBar) '' S), z) = (⨍ x in S, x - xBar) := by
  let e : E ≃ᵐ E := MeasurableEquiv.addRight (-xBar)
  let T : Set E := e '' S
  have hmap : Measure.map e volume = volume := by
    simpa [e, sub_eq_add_neg] using (measurePreserving_add_right volume (-xBar)).map_eq
  have hrestrict : volume.restrict T = (volume.restrict S).map e := by
    -- Rewrite the restricted translated measure as the pushforward of the restricted original
    -- measure along the translation equivalence.
    calc
      volume.restrict T = (Measure.map e volume).restrict T := by
        rw [hmap]
      _ = (volume.restrict (e ⁻¹' T)).map e := by
        exact MeasurableEquiv.restrict_map e volume T
      _ = (volume.restrict S).map e := by
        congr 1
        ext x
        simp [T]
  have hvol :
      (volume T).toReal = (volume S).toReal := by
    have hvolRaw :
        (volume (((fun x : E ↦ x - xBar) '' S))).toReal = (volume S).toReal :=
      congrArg ENNReal.toReal (translatedSet_volume_eq (S := S) xBar)
    simpa [T, e] using hvolRaw
  have hMain : (⨍ z in T, z) = (⨍ x in S, x - xBar) := by
    -- Compare the two set averages via the transported restricted measure and `integral_map_equiv`.
    rw [setAverage_eq volume (fun z : E ↦ z) T, setAverage_eq volume (fun x : E ↦ x - xBar) S]
    change
      (volume T).toReal⁻¹ • ∫ z, z ∂volume.restrict T =
        (volume S).toReal⁻¹ • ∫ x, x - xBar ∂volume.restrict S
    rw [hvol, hrestrict]
    simpa [e, sub_eq_add_neg] using
      congrArg (fun v : E => (volume S).toReal⁻¹ • v)
        (integral_map_equiv e (μ := volume.restrict S) (f := fun z : E ↦ z))
  simpa [T, e, sub_eq_add_neg] using hMain

/-- Helper for Lemma 3.2.6: translating a set by minus its centroid centers the resulting set at
the origin. -/
private theorem setAverage_translated_image_eq_zero
    (S : Set E) (hS_finite : volume S ≠ ⊤) :
    (⨍ z in ((fun x : E ↦ x - (⨍ x in S, x)) '' S), z) = 0 := by
  -- First transport the set average to the original set, then use the vanishing average of
  -- `x - setAverage S`.
  rw [setAverage_translated_image_eq_setAverage_sub]
  rw [setAverage_eq volume (fun x : E ↦ x - (⨍ y in S, y)) S]
  have hCenteredIntegral :
      ∫ x in S, x - (⨍ y in S, y) ∂volume = 0 :=
    MeasureTheory.setAverage_sub_setAverage (μ := volume) (s := S) hS_finite (f := fun x : E ↦ x)
  -- The centered integrand has zero set integral, so the normalized average is zero as well.
  simp [hCenteredIntegral]

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: once the centroid has been translated to the origin, the centered cut
is exactly the chapter owner `cuttingHalfspace 0 g`. -/
private lemma inter_centeredCut_eq_inter_cuttingHalfspace_origin
    (T : Set E) (g : E) :
    T ∩ {z | 0 ≤ inner ℝ g (-z)} = T ∩ cuttingHalfspace (0 : E) g := by
  -- Re-express the centered halfspace through the chapter owner at the origin.
  ext z
  simp [mem_cuttingHalfspace_iff]

/-- Helper for Lemma 3.2.6: the centered-cut ratio is exactly the origin-cut ratio owned by
`cuttingHalfspace (0 : E) g`. -/
private lemma centeredCut_volumeRatio_eq_originCut
    (T : Set E) (g : E) :
    (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal / (volume T).toReal =
      (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal := by
  -- Rewrite the centered region through the chapter owner before comparing the ratios.
  rw [inter_centeredCut_eq_inter_cuttingHalfspace_origin]

/-- Helper for Lemma 3.2.6: any sharp origin-cut bound immediately gives the centered formulation
used by the transport layer. -/
private lemma centeredCut_bound_of_originCut_bound
    (T : Set E) (g : E)
    (hOrigin :
      (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal ≤
        1 - Real.exp (-1)) :
    (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal / (volume T).toReal ≤
      1 - Real.exp (-1) := by
  -- Transfer the owner-form origin-cut inequality back to the centered-cut surface.
  rw [centeredCut_volumeRatio_eq_originCut (T := T) (g := g)]
  exact hOrigin

/-- Helper for Lemma 3.2.6: a linear isometry preserves Lebesgue volume on arbitrary images. -/
private lemma linearIsometryEquiv_volume_image_eq
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) (s : Set E) :
    volume (f '' s) = volume s := by
  -- Apply measure preservation to the image set and simplify the inverse image.
  have hImage :
      volume (f ⁻¹' (f '' s)) = volume (f '' s) :=
    (LinearIsometryEquiv.measurePreserving f).measure_preimage_equiv
      (f := f.toMeasurableEquiv) (f '' s)
  simpa [f.injective.preimage_image] using hImage.symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: a linear isometry transports the origin cut by `g` to the origin cut by
its image direction. -/
private lemma linearIsometryEquiv_image_inter_cuttingHalfspace_origin
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) (T : Set E) (g : E) :
    f '' (T ∩ cuttingHalfspace (0 : E) g) = (f '' T) ∩ cuttingHalfspace (0 : F) (f g) := by
  -- Rewrite cut membership through preservation of the inner product.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    have hxCut : 0 ≤ inner ℝ g (0 - x) := by
      simpa [mem_cuttingHalfspace_iff] using hx.2
    simpa [LinearIsometryEquiv.inner_map_map, map_sub] using hxCut
  · rintro ⟨⟨x, hxT, rfl⟩, hy⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    have hyCut : 0 ≤ inner ℝ g (0 - x) := by
      simpa [LinearIsometryEquiv.inner_map_map, map_sub] using hy
    simpa [mem_cuttingHalfspace_iff] using hyCut

/-- Helper for Lemma 3.2.6: linear isometries preserve the relative volume of origin cuts. -/
private lemma linearIsometryEquiv_originCut_volumeRatio_eq
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) (T : Set E) (g : E) :
    (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal =
      (volume ((f '' T) ∩ cuttingHalfspace (0 : F) (f g))).toReal / (volume (f '' T)).toReal := by
  -- Separate the transport into the cut-image identity and the ambient volume identity.
  have hCutImage :
      f '' (T ∩ cuttingHalfspace (0 : E) g) = (f '' T) ∩ cuttingHalfspace (0 : F) (f g) :=
    linearIsometryEquiv_image_inter_cuttingHalfspace_origin (f := f) T g
  have hVolume :
      volume (f '' T) = volume T :=
    linearIsometryEquiv_volume_image_eq (f := f) T
  have hCutVolume :
      volume ((f '' T) ∩ cuttingHalfspace (0 : F) (f g)) =
        volume (T ∩ cuttingHalfspace (0 : E) g) := by
    -- Apply the ambient volume preservation to the cut and then rewrite the image set.
    rw [← hCutImage]
    exact linearIsometryEquiv_volume_image_eq (f := f) (T ∩ cuttingHalfspace (0 : E) g)
  rw [hCutVolume, hVolume]

/-- Helper for Lemma 3.2.6: one can choose orthonormal coordinates whose first basis vector is the
normalized direction `g / ‖g‖`. -/
private lemma exists_axisAlignedOrthonormalBasis
    (hn : 0 < Module.finrank ℝ E) {g : E} (hg : g ≠ 0) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, b ⟨0, hn⟩ = ‖g‖⁻¹ • g := by
  let i0 : Fin (Module.finrank ℝ E) := ⟨0, hn⟩
  let v : Fin (Module.finrank ℝ E) → E := fun _ ↦ ‖g‖⁻¹ • g
  have hv :
      Orthonormal ℝ
        (Set.restrict ({i0} : Set (Fin (Module.finrank ℝ E))) v) := by
    -- On the singleton index set, orthonormality is exactly the unit-norm calculation.
    classical
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    have hnorm : ‖(Set.restrict ({i0} : Set (Fin (Module.finrank ℝ E))) v i : E)‖ = 1 := by
      simpa [v] using norm_smul_inv_norm hg
    simpa [if_pos rfl] using inner_self_eq_one_of_norm_eq_one (𝕜 := ℝ) hnorm
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := E) (ι := Fin (Module.finrank ℝ E))
      (s := ({i0} : Set (Fin (Module.finrank ℝ E)))) (v := v) (by simp) hv
  refine ⟨b, ?_⟩
  simpa [i0, v] using hb i0 (by simp [i0])

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: in coordinates aligned with `g`, the vector `g` itself becomes the
first coordinate axis scaled by `‖g‖`. -/
private lemma axisAlignedOrthonormalBasis_repr_direction
    (hn : 0 < Module.finrank ℝ E) {g : E} (hg : g ≠ 0)
    {b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E}
    (hb0 : b ⟨0, hn⟩ = ‖g‖⁻¹ • g) :
    b.repr g = EuclideanSpace.single ⟨0, hn⟩ ‖g‖ := by
  let i0 : Fin (Module.finrank ℝ E) := ⟨0, hn⟩
  -- Express `g` as `‖g‖` times the chosen first basis vector and then apply `repr`.
  have hg_eq : ‖g‖ • b i0 = g := by
    calc
      ‖g‖ • b i0 = ‖g‖ • (‖g‖⁻¹ • g) := by rw [hb0]
      _ = (‖g‖ * ‖g‖⁻¹) • g := by rw [smul_smul]
      _ = (1 : ℝ) • g := by
        congr 1
        field_simp [norm_ne_zero_iff.mpr hg]
      _ = g := by simp
  calc
    b.repr g = b.repr (‖g‖ • b i0) := by rw [hg_eq]
    _ = ‖g‖ • b.repr (b i0) := by rw [map_smul]
    _ = EuclideanSpace.single i0 ‖g‖ := by
      ext i
      by_cases hi : i = i0
      · subst hi
        simp
      · simp [hi]

/-- Helper for Lemma 3.2.6: the origin cut by a positive multiple of the first coordinate vector
is exactly the nonpositive first-coordinate halfspace. -/
private lemma cuttingHalfspace_origin_single_eq_firstCoordinate_nonpos
    {n : ℕ} (i0 : Fin n) {c : ℝ} (hc : 0 < c) :
    cuttingHalfspace (0 : EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i0 c) =
      {u | u.ofLp i0 ≤ 0} := by
  -- Rewrite the owner halfspace inequality in coordinates and cancel the positive scalar `c`.
  ext u
  constructor
  · intro hu
    have huInner : inner ℝ (EuclideanSpace.single i0 c) u ≤ 0 := by
      simpa [mem_cuttingHalfspace_iff] using hu
    have hu' : c * u.ofLp i0 ≤ 0 := by
      have hsingle :
          inner ℝ (EuclideanSpace.single i0 c) u = c * u.ofLp i0 := by
        simpa using EuclideanSpace.inner_single_left i0 c u
      rw [hsingle] at huInner
      exact huInner
    have hcoord : u.ofLp i0 ≤ 0 := by
      nlinarith
    simpa using hcoord
  · intro hu
    have hu' : c * u.ofLp i0 ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hu
    have huInner : inner ℝ (EuclideanSpace.single i0 c) u ≤ 0 := by
      have hsingle :
          inner ℝ (EuclideanSpace.single i0 c) u = c * u.ofLp i0 := by
        simpa using EuclideanSpace.inner_single_left i0 c u
      rw [hsingle]
      exact hu'
    simpa [mem_cuttingHalfspace_iff] using huInner

/-- Helper for Lemma 3.2.6: a linear isometry sends a centered convex body to another centered
convex body. -/
private lemma linearIsometryEquiv_setAverage_image_eq_zero
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) (S : Set E)
    (hS_finite : volume S ≠ ⊤) (hS_pos : volume S ≠ 0) (hS_center : (⨍ x in S, x) = 0) :
    (⨍ y in f '' S, y) = 0 := by
  let e : E ≃ᵐ F := f.toMeasurableEquiv
  have hImageVolume : volume (f '' S) = volume S :=
    linearIsometryEquiv_volume_image_eq (f := f) S
  have hImage_finite : volume (f '' S) ≠ ⊤ := by
    rw [hImageVolume]
    exact hS_finite
  have hImage_real_ne_zero : volume.real (f '' S) ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨by rwa [hImageVolume], hImage_finite⟩
  have hIntegralZero : ∫ x in S, x ∂(volume : Measure E) = 0 := by
    -- Convert the vanishing set average on `S` into a vanishing set integral.
    have hAverage :=
      MeasureTheory.measure_smul_setAverage
        (μ := (volume : Measure E)) (f := fun x : E ↦ x) (s := S) hS_finite
    rw [hS_center, smul_zero] at hAverage
    simpa using hAverage.symm
  have hrestrict : volume.restrict (f '' S) = (volume.restrict S).map e := by
    -- Rewrite the restricted image measure by transporting the restricted source measure across
    -- the measure-preserving equivalence.
    ext t ht
    rw [Measure.restrict_apply ht, Measure.map_apply e.measurable ht,
      Measure.restrict_apply (e.measurable ht)]
    have hImage :
        f '' (S ∩ e ⁻¹' t) = (f '' S) ∩ t := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxS, hxt⟩, rfl⟩
        exact ⟨⟨x, hxS, rfl⟩, hxt⟩
      · rintro ⟨⟨x, hxS, rfl⟩, hyt⟩
        exact ⟨x, ⟨hxS, hyt⟩, rfl⟩
    rw [Set.inter_comm, ← hImage, Set.inter_comm]
    simpa [Set.inter_comm] using
      linearIsometryEquiv_volume_image_eq (f := f) (S ∩ e ⁻¹' t)
  have hIntegralImage : ∫ y in f '' S, y ∂(volume : Measure F) = 0 := by
    -- Pull the image integral back through the measurable equivalence and then use linearity.
    calc
      ∫ y in f '' S, y ∂(volume : Measure F)
          = ∫ y, y ∂volume.restrict (f '' S) := by rfl
      _ = ∫ x, f x ∂volume.restrict S := by
        rw [hrestrict]
        simpa [e] using
          (integral_map_equiv e (μ := volume.restrict S) (f := fun y : F ↦ y))
      _ = f (∫ x, x ∂volume.restrict S) := by
        simpa using
          (f.toLinearIsometry.integral_comp_comm (μ := volume.restrict S) (φ := fun x : E ↦ x))
      _ = 0 := by simp [hIntegralZero]
  have hAverage :=
    MeasureTheory.measure_smul_setAverage
      (μ := (volume : Measure F)) (f := fun y : F ↦ y) (s := f '' S) hImage_finite
  -- Clear the positive real-valued volume factor on the image set average.
  rw [hIntegralImage] at hAverage
  exact (smul_eq_zero.mp hAverage).resolve_left hImage_real_ne_zero

/-- Helper for Lemma 3.2.6: the first-coordinate pushforward records the total mass and the
retained left-half mass of the coordinate cut. -/
private lemma firstCoordinatePushforward_massLeftMassMean
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    μ Set.univ = volume U ∧
      μ (Set.Iic 0) = volume (U ∩ {u | u.ofLp i0 ≤ 0}) := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  have hμ_univ : μ Set.univ = volume U := by
    -- Evaluate the pushforward on the whole line and then remove the restriction.
    simpa [μ] using
      (Measure.map_apply (μ := volume.restrict U)
        (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0)
        (by fun_prop) MeasurableSet.univ)
  have hμ_left : μ (Set.Iic 0) = volume (U ∩ {u | u.ofLp i0 ≤ 0}) := by
    -- The retained halfspace is exactly the preimage of `(-∞, 0]` under the chosen coordinate.
    calc
      μ (Set.Iic 0)
          = (volume.restrict U) ((fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) ⁻¹' Set.Iic 0) := by
              simpa [μ] using
                (Measure.map_apply (μ := volume.restrict U)
                  (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0)
                  (by fun_prop) measurableSet_Iic)
      _ = volume (U ∩ {u | u.ofLp i0 ≤ 0}) := by
            have hpre :
                ((fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) ⁻¹' Set.Iic 0) =
                  {u | u.ofLp i0 ≤ 0} := by
              ext u
              simp
            rw [Measure.restrict_apply]
            · rw [hpre, Set.inter_comm]
            · have hm : Measurable (fun u : EuclideanSpace ℝ (Fin n) ↦ u i0) := by
                fun_prop
              exact hm measurableSet_Iic
  exact ⟨hμ_univ, hμ_left⟩

/-- Helper for Lemma 3.2.6: the coordinate-cut ratio is exactly the left-mass ratio of the
first-coordinate pushforward, and this pushforward has finite positive total mass. -/
private lemma firstCoordinatePushforward_ratio_eq
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal =
        (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ∧
      μ Set.univ ≠ ⊤ ∧
      μ Set.univ ≠ 0 := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  obtain ⟨hμ_univ, hμ_left⟩ :=
    firstCoordinatePushforward_massLeftMassMean i0 U
  refine ⟨?_, ?_, ?_⟩
  · -- Rewrite the target ratio entirely in the pushforward spelling.
    rw [hμ_left, hμ_univ]
  · -- Finite mass is inherited from the ambient convex body.
    rwa [hμ_univ]
  · -- Positive mass is inherited from the ambient convex body as well.
    rwa [hμ_univ]

/-- Helper for Lemma 3.2.6: once the first-coordinate pushforward satisfies the sharp one-
dimensional left-mass estimate, the coordinate theorem follows by the already-proved ratio rewrite.
-/
private lemma centeredConvexCoordinate_bound_of_pushforward_bound
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hμ_bound :
      let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1)) :
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  have hμ_ratio :
      (volume (U ∩ {u | u i0 ≤ 0})).toReal / (volume U).toReal =
        (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal :=
    (firstCoordinatePushforward_ratio_eq i0 U hU_finite hU_pos).1
  have hμ_bound' :
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
    -- Unfold the frozen pushforward measure exactly once before applying the sharp 1D bound.
    simpa [μ] using hμ_bound
  -- The remaining coordinate-model theorem is now a direct rewrite from the pushforward ratio.
  rw [hμ_ratio]
  exact hμ_bound'

/-- Helper for Lemma 3.2.6: the same ratio rewrite also transports a coordinate-cut estimate back
to the frozen first-coordinate pushforward formulation. -/
private lemma firstCoordinatePushforward_bound_of_coordinateBound
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hcoord_bound :
      (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1)) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  have hμ_ratio :
      (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal =
        (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal :=
    (firstCoordinatePushforward_ratio_eq i0 U hU_finite hU_pos).1
  -- Rewrite the coordinate-model estimate into the frozen pushforward spelling exactly once.
  have hμ_bound :
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
    rw [← hμ_ratio]
    exact hcoord_bound
  simpa [μ] using hμ_bound

/-- Helper for Lemma 3.2.6: the coordinate-cut theorem and the frozen first-coordinate pushforward
theorem are equivalent because both sides are the same normalized ratio. -/
private lemma firstCoordinateCoordinateBound_iff_pushforwardBound
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) ↔
      let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
  constructor
  · intro hcoord_bound
    -- The forward implication is the reverse normalized-ratio transport.
    exact
      firstCoordinatePushforward_bound_of_coordinateBound
        i0 U hU_finite hU_pos hcoord_bound
  · intro hμ_bound
    -- The reverse implication is the already-assembled coordinate rewrite.
    exact
      centeredConvexCoordinate_bound_of_pushforward_bound
        i0 U hU_finite hU_pos hμ_bound

/-- Helper for Lemma 3.2.6: the remaining analytic owner is the sharp left-half bound for the
first-coordinate pushforward of a centered convex body. -/
private theorem firstCoordinatePushforward_leftHalfRatio_fromProfile
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hU_center : (⨍ u in U, u) = 0) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
  -- Route correction: `Profile.lean` now owns the sharp slice-profile and pushforward argument, so
  -- this target file no longer duplicates that analytic proof surface.
  simpa using
    firstCoordinatePushforward_leftHalfRatio_le_one_sub_exp_neg_one
      (hn := hn) (i0 := i0) (U := U) hU_convex hU_finite hU_pos hU_center

/-- Helper for Lemma 3.2.6: the only remaining higher-dimensional input is the sharp left-half
estimate in an axis-aligned Euclidean coordinate model. -/
private theorem centeredConvexCoordinate_leftHalf_ratio_le_one_sub_exp_neg_one
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hU_center : (⨍ u in U, u) = 0) :
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) := by
  -- Route correction: the target file now reads the sharp first-coordinate pushforward estimate
  -- directly from the theorem-local profile support file instead of reproving the analytic owner.
  have hμ_bound :
      let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) :=
    firstCoordinatePushforward_leftHalfRatio_fromProfile
      hn i0 U hU_convex hU_finite hU_pos hU_center
  -- The higher-dimensional coordinate theorem is now a direct assembly from the frozen
  -- pushforward ratio rewrite and the theorem-local support result.
  exact
    centeredConvexCoordinate_bound_of_pushforward_bound
      i0 U hU_finite hU_pos hμ_bound

/-- Helper for Lemma 3.2.6: the sharp Grünbaum inequality for the origin cut of a centered convex
body. -/
private theorem grunbaumOriginCut_volumeRatio_le_one_sub_exp_neg_one
    (T : Set E) (g : E) (hT_convex : Convex ℝ T) (hT_finite : volume T ≠ ⊤)
    (hT_pos : volume T ≠ 0) (hT_center : (⨍ z in T, z) = 0) (hg : g ≠ 0) :
    (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal ≤
      1 - Real.exp (-1) := by
  by_cases hdim : Module.finrank ℝ E = 1
  · let A : Set ℝ := (fun t : ℝ ↦ t • g) ⁻¹' T
    have hT_meas : NullMeasurableSet T volume := hT_convex.nullMeasurableSet volume
    have hA_convex : Convex ℝ A := by
      -- The scalar model inherits convexity from `T` through the linear parametrization.
      simpa [A] using
        hT_convex.linear_preimage ((1 : ℝ →ₗ[ℝ] ℝ).smulRight g)
    have hVolumeTransport :
        volume T = ‖g‖ₑ * volume A := by
      -- Transport the total mass of `T` to the scalar preimage model.
      simpa [A] using
        volume_eq_enorm_mul_volume_preimage_smul_of_finrank_eq_one
          (E := E) hdim hg hT_meas
    have hCutVolumeTransport :
        volume (T ∩ cuttingHalfspace (0 : E) g) = ‖g‖ₑ * volume (A ∩ Set.Iic 0) := by
      -- Transport the cut mass to the same scalar model and use the explicit cut preimage.
      simpa [A] using
        originCut_volume_eq_enorm_mul_volume_preimage_inter_Iic_of_finrank_eq_one
          (E := E) hdim hg hT_meas
    have hA_finite : volume A ≠ ⊤ := by
      -- Finite mass transports back to the scalar preimage because `‖g‖ ≠ 0`.
      intro hA_top
      apply hT_finite
      rw [hVolumeTransport, hA_top]
      simp [enorm_ne_zero.mpr hg]
    have hA_pos : volume A ≠ 0 := by
      -- Positive mass transports back to the scalar preimage as well.
      intro hA_zero
      apply hT_pos
      rw [hVolumeTransport, hA_zero, mul_zero]
    have hA_center : (⨍ t in A, t) = 0 := by
      -- The vector centroid condition becomes the scalar set-average condition in dimension one.
      simpa [A] using
        scalarPreimage_setAverage_eq_zero_of_originCentered
          (E := E) hdim hg hT_convex hT_finite hT_pos hT_center
    have hA_ratio :
        (volume (A ∩ Set.Iic 0)).toReal / (volume A).toReal ≤ 1 - Real.exp (-1) :=
      convexReal_leftHalf_ratio_le_one_sub_exp_neg_one_of_setAverage_zero
        A hA_convex hA_finite hA_pos hA_center
    have hCutToReal :
        (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal =
          ‖g‖ * (volume (A ∩ Set.Iic 0)).toReal := by
      -- Convert the cut-mass transport identity to real-valued volumes.
      rw [hCutVolumeTransport, ENNReal.toReal_mul]
      simp
    have hVolumeToReal :
        (volume T).toReal = ‖g‖ * (volume A).toReal := by
      -- Convert the total-mass transport identity to real-valued volumes.
      rw [hVolumeTransport, ENNReal.toReal_mul]
      simp
    have hA_toReal_ne_zero : (volume A).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hA_pos, hA_finite⟩
    have hnorm_ne_zero : (‖g‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hg
    rw [hCutToReal, hVolumeToReal]
    have hcancel :
        (‖g‖ * (volume (A ∩ Set.Iic 0)).toReal) / (‖g‖ * (volume A).toReal) =
          (volume (A ∩ Set.Iic 0)).toReal / (volume A).toReal := by
      field_simp [hnorm_ne_zero, hA_toReal_ne_zero]
    rw [hcancel]
    exact hA_ratio
  · have hdim_ne_zero : Module.finrank ℝ E ≠ 0 := by
      -- A zero-dimensional ambient space would force `g = 0`, contradicting the chosen direction.
      intro hzero
      have hsub : Subsingleton E := Module.finrank_zero_iff.mp hzero
      exact hg (hsub.elim g 0)
    have hdim_ge_two : 2 ≤ Module.finrank ℝ E := by
      -- Excluding dimensions `0` and `1` leaves only the higher-dimensional case needed here.
      omega
    let i0 : Fin (Module.finrank ℝ E) := ⟨0, Nat.zero_lt_of_ne_zero hdim_ne_zero⟩
    obtain ⟨b, hb0⟩ := exists_axisAlignedOrthonormalBasis (E := E)
      (Nat.zero_lt_of_ne_zero hdim_ne_zero) hg
    let U : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := b.repr '' T
    have hU_convex : Convex ℝ U := by
      -- The coordinate image of a convex body under a linear isometry is convex.
      simpa [U] using hT_convex.linear_image b.repr.toLinearMap
    have hU_finite : volume U ≠ ⊤ := by
      -- Volume preservation transports finite measure to the coordinate model.
      simpa [U, linearIsometryEquiv_volume_image_eq (f := b.repr) T] using hT_finite
    have hU_pos : volume U ≠ 0 := by
      -- The same transport preserves positive measure.
      simpa [U, linearIsometryEquiv_volume_image_eq (f := b.repr) T] using hT_pos
    have hU_center : (⨍ u in U, u) = 0 := by
      -- The origin-centering hypothesis is invariant under the linear isometry `b.repr`.
      simpa [U] using
        linearIsometryEquiv_setAverage_image_eq_zero
          (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
          (f := b.repr) T hT_finite hT_pos hT_center
    have hreprg : b.repr g = EuclideanSpace.single i0 ‖g‖ := by
      -- The chosen basis aligns the first coordinate axis with the original direction `g`.
      simpa [i0] using
        axisAlignedOrthonormalBasis_repr_direction
          (E := E) (Nat.zero_lt_of_ne_zero hdim_ne_zero) hg hb0
    have hratio :
        (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal =
          (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal := by
      -- Route correction: the higher-dimensional step is just coordinate transport plus the
      -- normalized first-coordinate halfspace rewrite.
      calc
        (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal
            = (volume (U ∩ cuttingHalfspace
                  (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (b.repr g))).toReal /
                (volume U).toReal := by
                  simpa [U] using
                    linearIsometryEquiv_originCut_volumeRatio_eq
                      (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                      (f := b.repr) T g
        _ = (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal := by
          rw [hreprg, cuttingHalfspace_origin_single_eq_firstCoordinate_nonpos
            i0 (c := ‖g‖) (norm_pos_iff.mpr hg)]
    have hCoordinate :
        (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤
          1 - Real.exp (-1) :=
      centeredConvexCoordinate_leftHalf_ratio_le_one_sub_exp_neg_one
        hdim_ge_two i0 U hU_convex hU_finite hU_pos hU_center
    rw [hratio]
    exact hCoordinate

/-- Helper for Lemma 3.2.6: the centered Grünbaum bound follows once the origin-cut theorem is in
place. -/
private theorem grunbaumCenteredHalfspace_volumeRatio_le_one_sub_exp_neg_one
    (T : Set E) (g : E) (hT_convex : Convex ℝ T) (hT_finite : volume T ≠ ⊤)
    (hT_pos : volume T ≠ 0) (hT_center : (⨍ z in T, z) = 0) (hg : g ≠ 0) :
    (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal / (volume T).toReal ≤
      1 - Real.exp (-1) := by
  have hOrigin :
      (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal ≤
        1 - Real.exp (-1) :=
    grunbaumOriginCut_volumeRatio_le_one_sub_exp_neg_one
      T g hT_convex hT_finite hT_pos hT_center hg
  -- Transport the owner-form origin-cut inequality back to the centered-cut surface.
  exact centeredCut_bound_of_originCut_bound T g hOrigin

/-- Helper for Lemma 3.2.6: the uncentered centroid-halfspace bound follows from the centered
transport lemmas and the centered Grünbaum inequality. -/
private theorem grunbaumCentroidHalfspace_volumeRatio_le_one_sub_exp_neg_one
    (S : Set E) (g : E) (hS_convex : Convex ℝ S) (hS_finite : volume S ≠ ⊤)
    (hS_pos : volume S ≠ 0) (hg : g ≠ 0) :
    (volume (S ∩ {x | 0 ≤ inner ℝ g ((⨍ x in S, x) - x)})).toReal / (volume S).toReal ≤
      1 - Real.exp (-1) := by
  let xBar : E := ⨍ x in S, x
  let T : Set E := ((fun x : E ↦ x - xBar) '' S)
  have hT_convex : Convex ℝ T := by
    -- Convexity is preserved by translation.
    let U : Set E := ((fun x : E ↦ -xBar + x) '' S)
    have hU : Convex ℝ U := hS_convex.translate (-xBar)
    simpa [T, U, sub_eq_add_neg, add_comm, xBar] using hU
  have hT_finite : volume T ≠ ⊤ := by
    -- Translation preserves finite volume.
    rw [translatedSet_volume_eq (S := S) xBar]
    exact hS_finite
  have hT_pos : volume T ≠ 0 := by
    -- Translation preserves positive volume as well.
    rw [translatedSet_volume_eq (S := S) xBar]
    exact hS_pos
  have hT_center : (⨍ z in T, z) = 0 := by
    -- The translated set is centered at the origin by construction.
    simpa [T, xBar] using
      setAverage_translated_image_eq_zero (S := S) hS_finite
  have hCentered :
      (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal / (volume T).toReal ≤
        1 - Real.exp (-1) :=
    grunbaumCenteredHalfspace_volumeRatio_le_one_sub_exp_neg_one
      T g hT_convex hT_finite hT_pos hT_center hg
  have hCutToReal :
      (volume (S ∩ {x | 0 ≤ inner ℝ g (xBar - x)})).toReal =
        (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal := by
    exact congrArg ENNReal.toReal
      (volume_centroidCut_eq_volume_centeredCut (S := S) xBar g)
  have hVolumeToReal :
      (volume T).toReal = (volume S).toReal := by
    exact congrArg ENNReal.toReal (translatedSet_volume_eq (S := S) xBar)
  -- Rewrite the centered estimate back to the original centroid-cut normalization.
  rw [← hCutToReal, hVolumeToReal] at hCentered
  simpa [xBar] using hCentered

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: rewrite the retained cut by its standard nonnegative-inner-product
description so the centroid theorem applies directly. -/
private lemma inter_cuttingHalfspace_eq_nonnegInnerCut
    (S : Set E) (xBar g : E) :
    S ∩ cuttingHalfspace xBar g = S ∩ {x | 0 ≤ inner ℝ g (xBar - x)} := by
  -- Unfold the chapter owner `cuttingHalfspace` into the equivalent inner-product inequality.
  ext x
  simp [mem_cuttingHalfspace_iff]

/-- Helper for Lemma 3.2.6: the sharp Grünbaum constant `1 - exp (-1)` is the textbook quantity
`1 - 1 / e`. -/
private lemma one_sub_exp_neg_one_eq_one_sub_inv_e :
    1 - Real.exp (-1) = 1 - 1 / Real.exp 1 := by
  -- Normalize the exponential term to the reciprocal form used in the statement.
  rw [Real.exp_neg]
  ring

/-- Lemma 3.2.6: let `g` be a direction in a finite-dimensional real inner-product space, and
define
`S₊ = S ∩ cuttingHalfspace (⨍ x in S, x) g = {x ∈ S | ⟪g, (⨍ x in S, x) - x⟫_ℝ ≥ 0}`.
Then `vol S₊ / vol S ≤ 1 - 1 / e` for convex `S` of finite positive volume. -/
theorem centerOfGravityCut_volumeRatio_le_one_sub_inv_e
    (S : Set E) (g : E) (hS_convex : Convex ℝ S) (hS_finite : volume S ≠ ⊤)
    (hS_pos : volume S ≠ 0) (hg : g ≠ 0) :
    (volume (S ∩ cuttingHalfspace (⨍ x in S, x) g)).toReal / (volume S).toReal ≤
      1 - 1 / Real.exp 1 := by
  -- Rewrite the retained region to the explicit centroid-halfspace surface owned by the local
  -- centroid transport theorem.
  rw [inter_cuttingHalfspace_eq_nonnegInnerCut]
  -- The remaining inequality is exactly the local centroid estimate, up to the textbook scalar
  -- normalization `exp (-1) = 1 / e`.
  simpa [one_sub_exp_neg_one_eq_one_sub_inv_e] using
    grunbaumCentroidHalfspace_volumeRatio_le_one_sub_exp_neg_one
      S g hS_convex hS_finite hS_pos hg

end
