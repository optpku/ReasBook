/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6.Coordinate

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local instance instMeasurableSpaceLemma326Core : MeasurableSpace E := borel E
local instance instBorelSpaceLemma326Core : BorelSpace E := ⟨rfl⟩

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
theorem volume_centroidCut_eq_volume_centeredCut
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
  -- Compare the two set averages via the transported restricted measure and `integral_map_equiv`.
  have hMain : (⨍ z in T, z) = (⨍ x in S, x - xBar) := by
    rw [setAverage_eq volume (fun z : E ↦ z) T, setAverage_eq volume (fun x : E ↦ x - xBar) S]
    change
      (volume T).toReal⁻¹ • ∫ z, z ∂volume.restrict T =
        (volume S).toReal⁻¹ • ∫ x, x - xBar ∂volume.restrict S
    rw [hvol, hrestrict]
    -- The integral over the translated set is the integral of the translated integrand over `S`.
    simpa [e, sub_eq_add_neg] using
      congrArg (fun v : E => (volume S).toReal⁻¹ • v)
        (integral_map_equiv e (μ := volume.restrict S) (f := fun z : E ↦ z))
  simpa [T, e, sub_eq_add_neg] using hMain

/-- Helper for Lemma 3.2.6: translating a set by minus its centroid centers the resulting set at
the origin. -/
theorem setAverage_translated_image_eq_zero
    (S : Set E) (hS_finite : volume S ≠ ⊤) :
    (⨍ z in ((fun x : E ↦ x - (⨍ x in S, x)) '' S), z) = 0 := by
  -- First transport the set average to the original set, then use the vanishing average of
  -- `x - setAverage S`.
  rw [setAverage_translated_image_eq_setAverage_sub]
  rw [setAverage_eq volume (fun x : E ↦ x - (⨍ y in S, y)) S]
  -- The integral of `x - setAverage S` over `S` is exactly the centered-average identity.
  have hCenteredIntegral :
      ∫ x in S, x - (⨍ y in S, y) ∂volume = 0 :=
    MeasureTheory.setAverage_sub_setAverage (μ := volume) (s := S) hS_finite (f := fun x : E ↦ x)
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

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 3.2.6: the centered cut can also be viewed with the opposite orientation
vector `-g` and the non-negated point `z`. -/
private lemma inter_centeredCut_eq_inter_negDirectionCut
    (T : Set E) (g : E) :
    T ∩ {z | 0 ≤ inner ℝ g (-z)} = T ∩ {z | 0 ≤ inner ℝ (-g) z} := by
  -- This is the `g ↦ -g` bridge suggested by the source-side centered formulation.
  ext z
  simp

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

/-- Helper for Lemma 3.2.6: the centered Grünbaum bound is the only remaining geometric core after
transporting by the centroid. -/
theorem grunbaumCenteredHalfspace_volumeRatio_le_one_sub_exp_neg_one
    (T : Set E) (g : E) (hT_convex : Convex ℝ T) (hT_finite : volume T ≠ ⊤)
    (hT_pos : volume T ≠ 0) (hT_center : (⨍ z in T, z) = 0) (hg : g ≠ 0) :
    (volume (T ∩ {z | 0 ≤ inner ℝ g (-z)})).toReal / (volume T).toReal ≤
      1 - Real.exp (-1) := by
  -- Route correction: the uncentered theorem has been reduced to the centered canonical form, and
  -- the cut is now explicitly bridged both to `cuttingHalfspace 0 g` and to the `g ↦ -g`
  -- orientation used by some equivalent formulations.
  -- Reduce the centered cut to the dedicated origin-cut theorem-local support declaration.
  have hOrigin :
      (volume (T ∩ cuttingHalfspace (0 : E) g)).toReal / (volume T).toReal ≤
        1 - Real.exp (-1) :=
    grunbaumOriginCut_volumeRatio_le_one_sub_exp_neg_one
      T g hT_convex hT_finite hT_pos hT_center hg
  exact centeredCut_bound_of_originCut_bound T g hOrigin

/-- Helper for Lemma 3.2.6: the uncentered centroid-halfspace bound follows from the centered
transport lemmas and the centered Grünbaum inequality. -/
theorem grunbaumCentroidHalfspace_volumeRatio_le_one_sub_exp_neg_one
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
