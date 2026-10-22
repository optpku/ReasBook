/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6.RealLine
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6.Slice

noncomputable section

open MeasureTheory
open scoped Pointwise

/-- Helper for Lemma 3.2.6: the explicit section profile at coordinate value `t`. -/
private def firstCoordinateSectionProfile
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ :=
  (volume {y : EuclideanSpace ℝ (Fin n) | coordinateReplace i0 y t ∈ U}).toReal

/-- Helper for Lemma 3.2.6: the support interval of admissible `i0`-coordinates. -/
private def firstCoordinateSupport
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) : Set ℝ :=
  {t : ℝ | ∃ y : EuclideanSpace ℝ (Fin n), coordinateReplace i0 y t ∈ U}

/-- Helper for Profile: rebuild the ambient point from a frozen `i0`-coordinate `t` and the
remaining free coordinates. -/
private def firstCoordinateSlicePoint
    {n : ℕ} (i0 : Fin n) (t : ℝ) (y : Fin (n - 1) → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  let z : Fin ((n - 1) + 1) → ℝ := i0'.insertNth t y
  WithLp.toLp 2 (fun j : Fin n => z (Fin.cast h.symm j))

/-- Helper for Profile: the repaired codimension-one slice support keeps only the free coordinates
away from `i0`. -/
private def firstCoordinateSliceSupport
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) : Set ℝ :=
  {t : ℝ | ∃ y : Fin (n - 1) → ℝ, firstCoordinateSlicePoint i0 t y ∈ U}

/-- Helper for Profile: delete the distinguished coordinate from an ambient point using the same
cast-stable `Fin.succAbove` normalization as `firstCoordinateSlicePoint`. -/
private def firstCoordinateDeletedCoords
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n)) : Fin (n - 1) → ℝ :=
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  fun j : Fin (n - 1) => y.ofLp (Fin.cast h (i0'.succAbove j))

/-- Helper for Profile: the repaired codimension-one slice profile measures the `(n - 1)`-
dimensional fiber cut out by fixing the `i0`-coordinate to `t`. -/
private def firstCoordinateSliceProfile
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ :=
  (volume {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U}).toReal

/-- Helper for Profile: the repaired slice profile is nonnegative because it is the real-valued
volume of a codimension-one fiber. -/
private lemma firstCoordinateSliceProfile_nonneg
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    0 ≤ firstCoordinateSliceProfile i0 U t := by
  -- `ENNReal.toReal` of a slice volume is automatically nonnegative.
  simp [firstCoordinateSliceProfile]

/-- Helper for Profile: the repaired slice profile vanishes whenever the codimension-one support
set has no witness at `t`. -/
private lemma firstCoordinateSliceProfile_eq_zero_of_not_mem_support
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) {t : ℝ}
    (ht : t ∉ firstCoordinateSliceSupport i0 U) :
    firstCoordinateSliceProfile i0 U t = 0 := by
  have hEmpty :
      {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U} = ∅ := by
    -- Outside the repaired support there are no codimension-one slice witnesses.
    ext y
    constructor
    · intro hy
      exact (ht ⟨y, hy⟩).elim
    · intro hy
      simp at hy
  -- An empty slice has zero volume, hence zero profile.
  simp [firstCoordinateSliceProfile, hEmpty]

/-- Helper for Profile: the repaired slice-point parametrization is measurable in the frozen
coordinate and the free coordinates. -/
private lemma measurable_firstCoordinateSlicePoint
    {n : ℕ} (i0 : Fin n) :
    Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) ↦ firstCoordinateSlicePoint i0 p.1 p.2) := by
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  have hinsert :
      Measurable
        (fun p : ℝ × (Fin (n - 1) → ℝ) ↦
          (i0'.insertNth p.1 p.2 : Fin ((n - 1) + 1) → ℝ)) := by
    -- Check measurability coordinatewise after splitting at the inserted index.
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = i0'
    · subst hj
      simpa using measurable_fst
    · rcases Fin.exists_succAbove_eq (x := j) (y := i0') hj with ⟨k, hk⟩
      rw [show (fun p : ℝ × (Fin (n - 1) → ℝ) ↦
            ((i0'.insertNth p.1 p.2 : Fin ((n - 1) + 1) → ℝ) j)) =
          fun p : ℝ × (Fin (n - 1) → ℝ) ↦ p.2 k by
            funext p
            rw [← hk, Fin.insertNth_apply_succAbove]]
      simpa using (measurable_pi_apply k).comp measurable_snd
  have hcoords :
      Measurable
        (fun p : ℝ × (Fin (n - 1) → ℝ) ↦
          fun j : Fin n ↦
            ((i0'.insertNth p.1 p.2 : Fin ((n - 1) + 1) → ℝ) (Fin.cast h.symm j))) := by
    -- Reindex the measurable inserted tuple back to the original `Fin n` coordinates.
    rw [measurable_pi_iff]
    intro j
    simpa using (measurable_pi_apply (Fin.cast h.symm j)).comp hinsert
  -- Compose the measurable coordinate tuple with the canonical `toLp` measurable equivalence.
  simpa [firstCoordinateSlicePoint, hn, h, i0'] using
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp hcoords

/-- Helper for Lemma 3.2.6: the repaired slice-point parametrization really freezes the
distinguished coordinate to the scalar parameter `t`. -/
private lemma firstCoordinateSlicePoint_apply_self
    {n : ℕ} (i0 : Fin n) (t : ℝ) (y : Fin (n - 1) → ℝ) :
    firstCoordinateSlicePoint i0 t y i0 = t := by
  -- Evaluate the repaired slice point at the distinguished coordinate and unfold the inserted
  -- tuple only at that coordinate.
  simp [firstCoordinateSlicePoint]

/-- Helper for Lemma 3.2.6: under the repaired slice parametrization, the first-coordinate cut
`u i0 ≤ 0` is exactly the scalar half-line `t ≤ 0`. -/
private lemma firstCoordinateSlicePoint_mem_firstCoordinate_nonpos_iff
    {n : ℕ} (i0 : Fin n) (t : ℝ) (y : Fin (n - 1) → ℝ) :
    firstCoordinateSlicePoint i0 t y ∈ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0} ↔
      t ≤ 0 := by
  -- Normalize the ambient first-coordinate condition using the frozen-coordinate identity.
  change firstCoordinateSlicePoint i0 t y i0 ≤ 0 ↔ t ≤ 0
  simp [firstCoordinateSlicePoint_apply_self (i0 := i0) (t := t) (y := y)]

/-- Helper for Lemma 3.2.6: the repaired slice-point map pulls the nonpositive first-coordinate
halfspace back to `(-∞, 0] × univ`. -/
private lemma preimage_firstCoordinate_nonpos_under_slicePoint
    {n : ℕ} (i0 : Fin n) :
    (fun p : ℝ × (Fin (n - 1) → ℝ) ↦ firstCoordinateSlicePoint i0 p.1 p.2) ⁻¹'
        ({u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0}) =
      Set.Iic 0 ×ˢ (Set.univ : Set (Fin (n - 1) → ℝ)) := by
  -- Rewrite the ambient cut pointwise through the scalar parameter of the repaired slice point.
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_prod, Set.mem_univ,
    and_true]
  exact
    firstCoordinateSlicePoint_mem_firstCoordinate_nonpos_iff
      (i0 := i0) (t := p.1) (y := p.2)

/-- Helper for Profile: the product-coordinate slice region is measurable whenever the ambient set
is measurable. -/
  private lemma measurableSet_firstCoordinateSliceRegion
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_meas : MeasurableSet U) :
    MeasurableSet {p : ℝ × (Fin (n - 1) → ℝ) | firstCoordinateSlicePoint i0 p.1 p.2 ∈ U} := by
  -- The slice region is the preimage of `U` under the measurable slice-point parametrization.
  change MeasurableSet
    ((fun p : ℝ × (Fin (n - 1) → ℝ) ↦ firstCoordinateSlicePoint i0 p.1 p.2) ⁻¹' U)
  exact hU_meas.preimage (measurable_firstCoordinateSlicePoint (i0 := i0))

/-- Helper for Profile: once the ambient set is measurable, the repaired slice profile is the
measurable fiber-volume function of the associated product-coordinate slice region. -/
private lemma measurable_firstCoordinateSliceProfile
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_meas : MeasurableSet U) :
    Measurable (firstCoordinateSliceProfile i0 U) := by
  let S : Set (ℝ × (Fin (n - 1) → ℝ)) :=
    {p : ℝ × (Fin (n - 1) → ℝ) | firstCoordinateSlicePoint i0 p.1 p.2 ∈ U}
  have hS_meas : MeasurableSet S :=
    measurableSet_firstCoordinateSliceRegion (i0 := i0) hU_meas
  have hfiber :
      ∀ t : ℝ,
        (volume (Prod.mk t ⁻¹' S)).toReal = firstCoordinateSliceProfile i0 U t := by
    intro t
    -- The `t`-fiber of the product slice region is exactly the repaired slice profile definition.
    simp [S, firstCoordinateSliceProfile]
  have hmeas :
      Measurable fun t : ℝ ↦ (volume (Prod.mk t ⁻¹' S)).toReal :=
    (measurable_measure_prodMk_left hS_meas).ennreal_toReal
  -- Rewrite the measurable fiber-volume function back to the repaired slice profile spelling.
  have hEq :
      (fun t : ℝ ↦ (volume (Prod.mk t ⁻¹' S)).toReal) = firstCoordinateSliceProfile i0 U := by
    funext t
    exact hfiber t
  exact hEq ▸ hmeas

/-- Helper for Lemma 3.2.6: the repaired slice-point parametrization is assembled from the
volume-preserving `piFinSuccAbove`, `piCongrLeft`, and `toLp` equivalences, so it preserves
Lebesgue volume. -/
private lemma firstCoordinateSlicePoint_measurePreserving
    {n : ℕ} (i0 : Fin n) :
    MeasurePreserving (fun p : ℝ × (Fin (n - 1) → ℝ) ↦ firstCoordinateSlicePoint i0 p.1 p.2)
      volume volume := by
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  let eInsert : (ℝ × (Fin (n - 1) → ℝ)) ≃ᵐ (Fin ((n - 1) + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin ((n - 1) + 1) ↦ ℝ) i0').symm
  let eCast : (Fin ((n - 1) + 1) → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) (finCongr h)
  let eToLp : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have hInsert : MeasurePreserving eInsert volume volume := by
    simpa [eInsert] using
      (volume_preserving_piFinSuccAbove (fun _ : Fin ((n - 1) + 1) ↦ ℝ) i0').symm
  have hCast : MeasurePreserving eCast volume volume := by
    simpa [eCast] using
      volume_measurePreserving_piCongrLeft (fun _ : Fin n ↦ ℝ) (finCongr h)
  have hToLp : MeasurePreserving eToLp volume volume := by
    simpa [eToLp] using
      (PiLp.volume_preserving_toLp (ι := Fin n))
  -- Compose the canonical coordinate equivalences to recover the repaired slice-point spelling.
  simpa [firstCoordinateSlicePoint, hn, h, i0', eInsert, eCast, eToLp] using
    hToLp.comp (hCast.comp hInsert)

/-- Helper for Lemma 3.2.6: the first-coordinate pushforward is exactly the measure with density
given by the repaired slice profile on every measurable set. -/
private lemma firstCoordinatePushforward_apply_eq_lintegral_sliceProfile
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_meas : MeasurableSet U) (hU_finite : volume U ≠ ⊤)
    {s : Set ℝ} (hs : MeasurableSet s) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    μ s = ∫⁻ t in s, ENNReal.ofReal (firstCoordinateSliceProfile i0 U t) ∂volume := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  let slice : ℝ × (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun p ↦ firstCoordinateSlicePoint i0 p.1 p.2
  let S : Set (ℝ × (Fin (n - 1) → ℝ)) := {p | slice p ∈ U}
  let Ss : Set (ℝ × (Fin (n - 1) → ℝ)) := S ∩ (s ×ˢ (Set.univ : Set (Fin (n - 1) → ℝ)))
  have hSlicePres : MeasurePreserving slice volume volume := by
    -- The repaired slice-point map transports product volume back to the ambient body.
    simpa [slice] using firstCoordinateSlicePoint_measurePreserving (i0 := i0)
  have hS_meas : MeasurableSet S := by
    -- The ambient measurability hypothesis pulls back to the slice region.
    simpa [S, slice] using measurableSet_firstCoordinateSliceRegion (i0 := i0) hU_meas
  have hS_volume : volume S = volume U := by
    -- The full slice region has the same volume as `U` by measure preservation.
    have hmap := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin n)) => ν U) hSlicePres.map_eq
    simpa [S, slice, Measure.map_apply hSlicePres.measurable hU_meas] using hmap
  have hS_finite : volume S ≠ ⊤ := by
    rwa [hS_volume]
  have hTargetMeas : MeasurableSet (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s}) := by
    -- The measurable coordinate projection cuts out the target measurable slice family.
    have hcoord : Measurable (fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) := by
      fun_prop
    exact hU_meas.inter (hcoord hs)
  have hSs_meas : MeasurableSet Ss := by
    -- The truncated slice region is measurable in the product space.
    exact hS_meas.inter (hs.prod MeasurableSet.univ)
  have hSs_eq :
      Ss = slice ⁻¹' (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s}) := by
    -- Freezing the distinguished coordinate identifies the scalar-side cutoff with the ambient
    -- first-coordinate cutoff.
    ext p
    simp [Ss, S, slice, firstCoordinateSlicePoint_apply_self (i0 := i0) (t := p.1) (y := p.2)]
  have hSs_volume :
      volume Ss = μ s := by
    -- Push the ambient coordinate cutoff through the same volume-preserving slice map.
    have hmap := congrArg
      (fun ν : Measure (EuclideanSpace ℝ (Fin n)) =>
        ν (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s})) hSlicePres.map_eq
    have hμ_apply :
        μ s = volume (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s}) := by
      -- The first-coordinate pushforward evaluates on `s` as the restricted ambient preimage.
      calc
        μ s
            = (volume.restrict U) ((fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) ⁻¹' s) := by
                simpa [μ] using
                  (Measure.map_apply (μ := volume.restrict U)
                    (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0)
                    (by fun_prop) hs)
        _ = volume (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s}) := by
              rw [Measure.restrict_apply]
              · have hpre :
                    ((fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) ⁻¹' s) ∩ U =
                      U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ∈ s} := by
                    ext u
                    constructor
                    · intro hu
                      exact ⟨hu.2, hu.1⟩
                    · intro hu
                      exact ⟨hu.2, hu.1⟩
                rw [hpre]
              · have hcoord : Measurable (fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0) := by
                  fun_prop
                exact hcoord hs
    rw [hμ_apply]
    simpa [hSs_eq, slice, Measure.map_apply hSlicePres.measurable hTargetMeas] using hmap
  have hS_fiber_finite :
      ∀ᵐ t ∂(volume : Measure ℝ), volume (Prod.mk t ⁻¹' S) < ⊤ := by
    -- Finite total mass forces almost every vertical fiber of the slice region to have finite
    -- volume.
    have hS_prod_lt_top :
        (∫⁻ t, volume (Prod.mk t ⁻¹' S) ∂(volume : Measure ℝ)) < ⊤ := by
      rw [← Measure.prod_apply hS_meas]
      exact lt_top_iff_ne_top.mpr hS_finite
    exact ae_lt_top (measurable_measure_prodMk_left hS_meas) hS_prod_lt_top.ne
  have hFiberEq :
      ∀ᵐ t ∂(volume : Measure ℝ),
        volume (Prod.mk t ⁻¹' S) = ENNReal.ofReal (firstCoordinateSliceProfile i0 U t) := by
    -- Almost every fiber has finite volume, so the slice profile is exactly its real-valued
    -- representative.
    filter_upwards [hS_fiber_finite] with t ht
    simpa [S, slice, firstCoordinateSliceProfile] using (ENNReal.ofReal_toReal ht.ne).symm
  have hSs_fiber :
      (fun t : ℝ ↦ volume (Prod.mk t ⁻¹' Ss)) =
        Set.indicator s (fun t ↦ volume (Prod.mk t ⁻¹' S)) := by
    -- Truncating to `s ×ˢ univ` keeps the original fiber over `t ∈ s` and kills the rest.
    funext t
    by_cases ht : t ∈ s
    · simp [Ss, S, ht]
    · simp [Ss, S, ht]
  calc
    μ s = volume Ss := hSs_volume.symm
    _ = ∫⁻ t, volume (Prod.mk t ⁻¹' Ss) ∂(volume : Measure ℝ) := by
          rw [Measure.volume_eq_prod, Measure.prod_apply hSs_meas]
    _ = ∫⁻ t, Set.indicator s (fun t ↦ volume (Prod.mk t ⁻¹' S)) t ∂(volume : Measure ℝ) := by
          rw [hSs_fiber]
    _ = ∫⁻ t in s, volume (Prod.mk t ⁻¹' S) ∂(volume : Measure ℝ) := by
          rw [lintegral_indicator hs]
    _ = ∫⁻ t in s, ENNReal.ofReal (firstCoordinateSliceProfile i0 U t) ∂volume := by
          refine lintegral_congr_ae (ae_restrict_of_ae hFiberEq)

/-- Helper for Profile: the centroid condition forces the ambient set integral to vanish. -/
private lemma centeredSetIntegral_eq_zero
    {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_center : (⨍ u in U, u) = 0) :
    ∫ u in U, u ∂volume = 0 := by
  -- Multiply the vector-valued set average by the total mass to recover the ambient integral.
  have hAverage :=
    MeasureTheory.measure_smul_setAverage
      (μ := volume) (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u) (s := U) hU_finite
  rw [hU_center, smul_zero] at hAverage
  simpa using hAverage.symm

/-- Helper for Profile: evaluating the centered ambient integral at the distinguished coordinate
forces that coordinate moment to vanish. -/
private lemma firstCoordinateIntegralEval_eq_zero_of_centered
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_center : (⨍ u in U, u) = 0) :
    (∫ u in U, u ∂volume) i0 = 0 := by
  -- Apply the coordinate projection to the ambient zero-integral identity.
  have hIntegralZero :
      ∫ u in U, u ∂volume = 0 :=
    centeredSetIntegral_eq_zero U hU_finite hU_center
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v i0) hIntegralZero

/-- Helper for Profile: once the ambient identity is integrable on `U`, coordinate evaluation
commutes with the restricted set integral. -/
private lemma firstCoordinateSetIntegral_eq_integralEval_of_integrable
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_integrable :
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) ↦ u) (volume.restrict U)) :
    ∫ u in U, u i0 ∂volume = (∫ u in U, u ∂volume) i0 := by
  -- Commute coordinate evaluation with the restricted ambient integral exactly once.
  simpa using
    (MeasureTheory.eval_integral_piLp
      (μ := volume.restrict U)
      (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u)
      (fun j ↦ hU_integrable.eval_piLp j) i0).symm

/-- Helper for Profile: the first moment of the first-coordinate pushforward is exactly the
set integral of the distinguished coordinate. -/
private lemma firstCoordinatePushforward_integral_id_eq_setIntegral_coordinate
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    ∫ t, t ∂μ = ∫ u in U, u i0 ∂volume := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  have hMap :
      ∫ t, t ∂μ = ∫ u, u i0 ∂volume.restrict U := by
    -- Push the scalar identity back through the first-coordinate map exactly once.
    simpa [μ] using
      (MeasureTheory.integral_map
        (μ := volume.restrict U)
        (φ := fun u : EuclideanSpace ℝ (Fin n) ↦ u i0)
        (f := fun t : ℝ ↦ t)
        (by fun_prop)
        (by simpa using continuous_id.aestronglyMeasurable))
  calc
    ∫ t, t ∂μ = ∫ u, u i0 ∂volume.restrict U := hMap
    _ = ∫ u in U, u i0 ∂volume := by rfl

/-- Helper for Profile: once the ambient identity function is known to be integrable on `U`,
centering forces the first moment of the first-coordinate pushforward to vanish. -/
private lemma firstCoordinatePushforward_integral_id_eq_zero_of_centered_of_integrable
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_center : (⨍ u in U, u) = 0)
    (hU_integrable :
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) ↦ u) (volume.restrict U)) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    ∫ t, t ∂μ = 0 := by
  -- Rewrite the pushforward moment back to the centered distinguished-coordinate integral.
  calc
    (let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
      ∫ t, t ∂μ) = ∫ u in U, u i0 ∂volume :=
        firstCoordinatePushforward_integral_id_eq_setIntegral_coordinate i0 U
    _ = (∫ u in U, u ∂volume) i0 :=
      firstCoordinateSetIntegral_eq_integralEval_of_integrable i0 U hU_integrable
    _ = 0 :=
      firstCoordinateIntegralEval_eq_zero_of_centered i0 U hU_finite hU_center

/-- Helper for Lemma 3.2.6: a convex body with positive Lebesgue volume cannot be trapped in a
proper affine subspace, so its interior is nonempty. -/
private lemma convex_nonemptyInterior_of_volume_ne_zero
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_pos : volume U ≠ 0) :
    (interior U).Nonempty := by
  by_contra hU_empty
  have hSpan_ne_top : affineSpan ℝ U ≠ ⊤ := by
    -- A convex set has nonempty interior exactly when its affine span fills the ambient space.
    intro hSpan_top
    apply hU_empty
    rw [hU_convex.interior_nonempty_iff_affineSpan_eq_top]
    exact hSpan_top
  have hSpan_null :
      volume (affineSpan ℝ U : Set (EuclideanSpace ℝ (Fin n))) = 0 := by
    -- Proper affine subspaces have zero Lebesgue volume in finite-dimensional Euclidean space.
    simpa using
      (Measure.addHaar_affineSubspace volume (affineSpan ℝ U) hSpan_ne_top)
  have hU_null : volume U = 0 :=
    measure_mono_null (subset_affineSpan ℝ U) hSpan_null
  exact hU_pos hU_null

/-- Helper for Lemma 3.2.6: if a convex set contains an open ball around `x`, then every midpoint
between a point of that ball and a point of the set stays in the set, so the whole midpoint ball
is contained in the convex set. -/
private lemma midpointBall_subset_of_convex_mem_ball
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU_convex : Convex ℝ U)
    {x y : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hy : y ∈ U) (hball : Metric.ball x r ⊆ U) :
    Metric.ball (midpoint ℝ x y) (r / 2) ⊆ U := by
  intro w hw
  let z : EuclideanSpace ℝ (Fin n) := (2 : ℝ) • w - y
  have hz_mid : midpoint ℝ z y = w := by
    -- Rebuild `w` as the midpoint of `y` and the reflected point `z`.
    ext i
    simp [z, midpoint_eq_smul_add]
  have hz_ball : z ∈ Metric.ball x r := by
    -- The reflected point `z` lies in the original radius-`r` ball around `x`.
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have hz_sub :
        z - x = (2 : ℝ) • (w - midpoint ℝ x y) := by
      ext i
      simp [z, midpoint_eq_smul_add]
      ring
    rw [hz_sub, norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  -- Apply convexity to the midpoint of the interior-ball point `z` and the ambient point `y`.
  rw [← hz_mid]
  exact hU_convex.midpoint_mem (hball hz_ball) hy

/-- Helper for Profile: balls of the same radius have the same Lebesgue volume, by translating one
center to the other. -/
private lemma volume_ball_eq_of_same_radius
    {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume (Metric.ball x r) = volume (Metric.ball y r) := by
  let c : EuclideanSpace ℝ (Fin n) := y - x
  have hmap :
      (Measure.map (fun z : EuclideanSpace ℝ (Fin n) ↦ z + c) volume) (Metric.ball y r) =
        volume (Metric.ball y r) := by
    -- Translate the ambient measure by the center difference once and evaluate it on the target
    -- ball.
    simpa [c] using
      congrArg
        (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ (Metric.ball y r))
        (map_add_right_eq_self volume c)
  have hpre :
      (fun z : EuclideanSpace ℝ (Fin n) ↦ z + c) ⁻¹' Metric.ball y r =
        Metric.ball x r := by
    -- Translating the target ball back by `c = y - x` recovers the source ball.
    ext z
    change ‖(z + c) - y‖ < r ↔ ‖z - x‖ < r
    have hshift : (z + c) - y = z - x := by
      dsimp [c]
      abel
    rw [hshift]
  calc
    volume (Metric.ball x r)
        = volume ((fun z : EuclideanSpace ℝ (Fin n) ↦ z + c) ⁻¹' Metric.ball y r) := by
            rw [hpre]
    _ = (Measure.map (fun z : EuclideanSpace ℝ (Fin n) ↦ z + c) volume) (Metric.ball y r) := by
          symm
          exact
            Measure.map_apply (μ := volume)
              (f := fun z : EuclideanSpace ℝ (Fin n) ↦ z + c)
              (by fun_prop) measurableSet_ball
    _ = volume (Metric.ball y r) := hmap

/-- Helper for Lemma 3.2.6: a convex body of finite positive volume is bounded. -/
private lemma convexFiniteVolume_isBounded
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    Bornology.IsBounded U := by
  by_contra hU_unbounded
  obtain ⟨x, hxInterior⟩ :=
    convex_nonemptyInterior_of_volume_ne_zero hU_convex hU_pos
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball x r ⊆ U := by
    exact Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxInterior)
  have hOutside : ∀ R : ℝ, ∃ y, y ∈ U ∧ R < dist x y := by
    rw [Metric.isBounded_iff_subset_closedBall x] at hU_unbounded
    intro R
    have hNotSubset : ¬ U ⊆ Metric.closedBall x R := by
      intro hSubset
      exact hU_unbounded ⟨R, hSubset⟩
    rw [Set.not_subset] at hNotSubset
    rcases hNotSubset with ⟨y, hyU, hyOutside⟩
    refine ⟨y, hyU, ?_⟩
    have hyFar : ¬ dist x y ≤ R := by
      simpa [Metric.mem_closedBall, dist_comm] using hyOutside
    exact lt_of_not_ge hyFar
  choose farPoint hfar_mem hfar_dist using hOutside
  let seq : ℕ → EuclideanSpace ℝ (Fin n) :=
    Nat.rec (farPoint 0) (fun _ yn ↦ farPoint (dist x yn + 2 * r))
  have hseq_mem : ∀ n, seq n ∈ U := by
    intro n
    induction n with
    | zero =>
        -- The recursion starts from a point of `U`.
        simpa [seq] using hfar_mem 0
    | succ n ih =>
        -- Each recursive far point is chosen inside `U`.
        simpa [seq] using hfar_mem (dist x (seq n) + 2 * r)
  have hseq_step : ∀ n, dist x (seq n) + 2 * r < dist x (seq (n + 1)) := by
    intro n
    -- Each new far point is chosen at least `2r` farther from `x` than the previous one.
    simpa [seq] using hfar_dist (dist x (seq n) + 2 * r)
  have hseq_pair_separated : ∀ {m n : ℕ}, m < n → 2 * r < dist (seq m) (seq n) := by
    intro m n hmn
    have hgap₁ : dist x (seq m) + 2 * r < dist x (seq (m + 1)) :=
      hseq_step m
    have hgap₂ : dist x (seq (m + 1)) ≤ dist x (seq n) := by
      have hmn' : m + 1 ≤ n := Nat.succ_le_of_lt hmn
      refine Nat.le_induction ?_ ?_ n hmn'
      · exact le_rfl
      · intro k hk ih
        exact
          le_trans ih <|
            le_of_lt <|
              lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) (hseq_step k)
    have hgap : dist x (seq m) + 2 * r < dist x (seq n) :=
      lt_of_lt_of_le hgap₁ hgap₂
    have htri : dist x (seq n) ≤ dist x (seq m) + dist (seq m) (seq n) := by
      simpa [dist_comm] using dist_triangle_right x (seq n) (seq m)
    linarith
  let midCenter : ℕ → EuclideanSpace ℝ (Fin n) := fun n ↦ midpoint ℝ x (seq n)
  have hmid_subset : ∀ n, Metric.ball (midCenter n) (r / 2) ⊆ U := by
    intro n
    -- Each far witness creates a fixed-radius midpoint ball inside `U`.
    exact midpointBall_subset_of_convex_mem_ball hU_convex (hseq_mem n) hball
  have hmid_disjoint_of_lt :
      ∀ {m n : ℕ}, m < n →
        Disjoint (Metric.ball (midCenter m) (r / 2)) (Metric.ball (midCenter n) (r / 2)) := by
    intro m n hlt
    have hdist_seq : 2 * r < dist (seq m) (seq n) :=
      hseq_pair_separated hlt
    have hdist_mid :
        dist (midCenter m) (midCenter n) = dist (seq m) (seq n) / 2 := by
      -- Midpoints on the same segment halve the distance between the endpoints.
      rw [show midCenter m = midpoint ℝ x (seq m) by rfl,
        show midCenter n = midpoint ℝ x (seq n) by rfl]
      rw [dist_eq_norm]
      have hsub :
          midpoint ℝ x (seq m) - midpoint ℝ x (seq n) = (1 / 2 : ℝ) • (seq m - seq n) := by
        simpa [vsub_eq_sub, one_div, invOf_eq_inv] using
          (midpoint_vsub_midpoint_same_left (R := ℝ) x (seq m) (seq n))
      rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), dist_eq_norm, div_eq_mul_inv]
      ring
    refine Set.disjoint_left.mpr ?_
    intro z hzM hzN
    have hzM' : dist (midCenter m) z < r / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hzM
    have hzN' : dist (midCenter n) z < r / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hzN
    have hclose : dist (midCenter m) (midCenter n) < r := by
      -- Any point lying in both balls would force the centers to be too close.
      have htri :
          dist (midCenter m) (midCenter n) ≤
            dist (midCenter m) z + dist (midCenter n) z := by
        simpa [dist_comm] using dist_triangle_right (midCenter m) (midCenter n) z
      linarith
    have hfar : r < dist (midCenter m) (midCenter n) := by
      -- But the recursive separation makes the midpoint centers farther apart than `r`.
      rw [hdist_mid]
      linarith
    linarith
  have hmid_disjoint :
      Pairwise fun m n : ℕ =>
        Disjoint (Metric.ball (midCenter m) (r / 2)) (Metric.ball (midCenter n) (r / 2)) := by
    intro m n hmn
    rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
    · exact hmid_disjoint_of_lt hlt
    · exact (hmid_disjoint_of_lt hgt).symm
  have hUnion_subset : (⋃ n : ℕ, Metric.ball (midCenter n) (r / 2)) ⊆ U := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨n, hzn⟩
    exact hmid_subset n hzn
  have hBall_ne_zero : volume (Metric.ball x (r / 2)) ≠ 0 := by
    -- Euclidean balls of positive radius have positive volume.
    exact (Metric.measure_ball_pos volume x (half_pos hr)).ne'
  have hUnion_top :
      volume (⋃ n : ℕ, Metric.ball (midCenter n) (r / 2)) = ⊤ := by
    calc
      volume (⋃ n : ℕ, Metric.ball (midCenter n) (r / 2))
          = ∑' n : ℕ, volume (Metric.ball (midCenter n) (r / 2)) := by
              rw [MeasureTheory.measure_iUnion hmid_disjoint fun _ ↦ measurableSet_ball]
      _ = ∑' _n : ℕ, volume (Metric.ball x (r / 2)) := by
            refine tsum_congr fun n ↦ ?_
            exact volume_ball_eq_of_same_radius (midCenter n) x (r / 2)
      _ = ⊤ := by
            simpa using ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hBall_ne_zero
  have hUnion_le : volume (⋃ n : ℕ, Metric.ball (midCenter n) (r / 2)) ≤ volume U :=
    measure_mono hUnion_subset
  -- The infinite disjoint union of positive-volume midpoint balls contradicts finite ambient
  -- volume.
  exact hU_finite (top_unique (hUnion_top ▸ hUnion_le))

/-- Helper for Profile: once the ambient convex body is known to be bounded, the identity function
is integrable on its restricted volume measure. -/
private lemma integrable_id_restrict_of_bounded
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_meas : NullMeasurableSet U volume) (hU_finite : volume U ≠ ⊤)
    (hU_bounded : Bornology.IsBounded U) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) ↦ u) (volume.restrict U) := by
  rcases hU_bounded.exists_norm_le with ⟨C, hC⟩
  have hbound : ∀ᵐ u ∂volume.restrict U, ‖u‖ ≤ C := by
    -- Restricting to `U` turns the pointwise norm bound into the required AE estimate.
    filter_upwards [ae_restrict_mem₀ hU_meas] with u hu
    exact hC u hu
  refine ⟨continuous_id.aestronglyMeasurable.restrict, ?_⟩
  -- Finite mass plus a uniform norm bound gives finite integral on the restricted measure.
  exact
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := C)
      (lt_top_iff_ne_top.mpr hU_finite) hbound

/-- Helper for Lemma 3.2.6: bounded centered convex bodies already satisfy the vanishing first
moment condition needed for the frozen first-coordinate pushforward. -/
private lemma firstCoordinatePushforward_integral_id_eq_zero_of_centered_of_bounded
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤)
    (hU_center : (⨍ u in U, u) = 0) (hU_bounded : Bornology.IsBounded U) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    ∫ t, t ∂μ = 0 := by
  have hU_meas : NullMeasurableSet U volume := hU_convex.nullMeasurableSet volume
  have hU_integrable :
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) ↦ u) (volume.restrict U) :=
    integrable_id_restrict_of_bounded hU_meas hU_finite hU_bounded
  -- Reuse the already-established transport from the centered ambient integral to the one-
  -- dimensional pushforward moment.
  simpa using
    firstCoordinatePushforward_integral_id_eq_zero_of_centered_of_integrable
      i0 U hU_finite hU_center hU_integrable

/-- Helper for Lemma 3.2.6: integrating the repaired slice profile over the whole line and over
`(-∞, 0]` recovers the ambient volume and the retained first-coordinate-cut volume. -/
private lemma firstCoordinateSliceProfile_totalMass_leftMass
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_meas : MeasurableSet U) (hU_finite : volume U ≠ ⊤) :
    (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) = (volume U).toReal ∧
      (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) =
        (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal := by
  let slice : ℝ × (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun p ↦ firstCoordinateSlicePoint i0 p.1 p.2
  let S : Set (ℝ × (Fin (n - 1) → ℝ)) := {p | slice p ∈ U}
  let Sleft : Set (ℝ × (Fin (n - 1) → ℝ)) :=
    S ∩ (Set.Iic 0 ×ˢ (Set.univ : Set (Fin (n - 1) → ℝ)))
  have hSlicePres : MeasurePreserving slice volume volume := by
    simpa [slice] using firstCoordinateSlicePoint_measurePreserving (i0 := i0)
  have hS_meas : MeasurableSet S := by
    simpa [S, slice] using measurableSet_firstCoordinateSliceRegion (i0 := i0) hU_meas
  have hS_volume : volume S = volume U := by
    -- Transport the whole slice region through the volume-preserving slice-point map.
    have hmap := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ U) hSlicePres.map_eq
    simpa [S, slice, Measure.map_apply hSlicePres.measurable hU_meas] using hmap
  have hS_finite : volume S ≠ ⊤ := by
    rwa [hS_volume]
  have hS_fiber_finite :
      ∀ᵐ t ∂(volume : Measure ℝ), volume (Prod.mk t ⁻¹' S) < ⊤ := by
    -- Finite total mass forces almost every fiber of the measurable slice region to have finite
    -- volume.
    have hS_prod_lt_top :
        (∫⁻ t, volume (Prod.mk t ⁻¹' S) ∂(volume : Measure ℝ)) < ⊤ := by
      rw [← Measure.prod_apply hS_meas]
      exact lt_top_iff_ne_top.mpr hS_finite
    exact ae_lt_top (measurable_measure_prodMk_left hS_meas) hS_prod_lt_top.ne
  have hTotalAux :
      ∫ t, (volume (Prod.mk t ⁻¹' S)).toReal ∂(volume : Measure ℝ) = (volume S).toReal := by
    -- Apply Tonelli to the measurable slice region and convert the fiber masses to real values.
    rw [integral_toReal (measurable_measure_prodMk_left hS_meas).aemeasurable hS_fiber_finite,
      Measure.volume_eq_prod, Measure.prod_apply hS_meas]
  have hFiberEq :
      (fun t : ℝ => (volume (Prod.mk t ⁻¹' S)).toReal) = firstCoordinateSliceProfile i0 U := by
    -- Each vertical fiber of the slice region is exactly the repaired slice profile definition.
    funext t
    simp [S, slice, firstCoordinateSliceProfile]
  have hTotal :
      (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) = (volume U).toReal := by
    -- Rewrite the total profile mass through the measurable slice region and then transport it
    -- back to `U`.
    rw [← hFiberEq, hTotalAux, hS_volume]
  have hLeftCut_meas :
      MeasurableSet (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0}) := by
    -- The retained halfspace is a measurable coordinate cut.
    have hcoord : Measurable (fun u : EuclideanSpace ℝ (Fin n) ↦ u i0) := by
      fun_prop
    exact hU_meas.inter (hcoord measurableSet_Iic)
  have hSleft_meas : MeasurableSet Sleft := by
    -- The truncated slice region is the measurable slice region intersected with
    -- `(-∞, 0] × univ`.
    exact hS_meas.inter (measurableSet_Iic.prod MeasurableSet.univ)
  have hSleft_eq :
      Sleft = slice ⁻¹' (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0}) := by
    -- After the coordinate normalization already proved for `slice`, the truncated product region
    -- is exactly the preimage of the ambient first-coordinate cut.
    ext p
    simp [Sleft, S, slice, preimage_firstCoordinate_nonpos_under_slicePoint (i0 := i0)]
  have hLeftCut_finite : volume (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0}) ≠ ⊤ := by
    exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_top_iff_ne_top.mpr hU_finite)).ne
  have hSleft_volume :
      volume Sleft = volume (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0}) := by
    -- Transport the truncated slice region through the same volume-preserving slice-point map.
    have hmap := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin n)) =>
        μ (U ∩ {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0})) hSlicePres.map_eq
    simpa [hSleft_eq, slice, Measure.map_apply hSlicePres.measurable hLeftCut_meas] using hmap
  have hSleft_finite : volume Sleft ≠ ⊤ := by
    rwa [hSleft_volume]
  have hSleft_fiber_finite :
      ∀ᵐ t ∂(volume : Measure ℝ), volume (Prod.mk t ⁻¹' Sleft) < ⊤ := by
    -- The same a.e.-finite-fiber argument applies to the truncated slice region.
    have hSleft_prod_lt_top :
        (∫⁻ t, volume (Prod.mk t ⁻¹' Sleft) ∂(volume : Measure ℝ)) < ⊤ := by
      rw [← Measure.prod_apply hSleft_meas]
      exact lt_top_iff_ne_top.mpr hSleft_finite
    exact ae_lt_top (measurable_measure_prodMk_left hSleft_meas) hSleft_prod_lt_top.ne
  have hLeftAux :
      ∫ t, (volume (Prod.mk t ⁻¹' Sleft)).toReal ∂(volume : Measure ℝ) = (volume Sleft).toReal := by
    -- Tonelli on the truncated slice region produces the left-half mass identity.
    rw [integral_toReal (measurable_measure_prodMk_left hSleft_meas).aemeasurable
      hSleft_fiber_finite, Measure.volume_eq_prod, Measure.prod_apply hSleft_meas]
  have hLeftFiberEq :
      (fun t : ℝ => (volume (Prod.mk t ⁻¹' Sleft)).toReal) =
        Set.indicator (Set.Iic 0) (firstCoordinateSliceProfile i0 U) := by
    -- Fiberwise, the truncated region keeps the original slice only on `(-∞, 0]`.
    funext t
    by_cases ht : t ∈ Set.Iic 0
    · simp [Sleft, S, slice, firstCoordinateSliceProfile, ht]
    · simp [Sleft, S, slice, firstCoordinateSliceProfile, ht]
  have hLeft :
      (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) = (volume Sleft).toReal := by
    -- Rewrite the restricted integral as the whole-space integral of the indicator, then replace
    -- that indicator by the truncated slice fibers.
    calc
      ∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume
          = ∫ t, Set.indicator (Set.Iic 0) (firstCoordinateSliceProfile i0 U) t
              ∂(volume : Measure ℝ) := by
                rw [integral_indicator measurableSet_Iic]
      _ = ∫ t, (volume (Prod.mk t ⁻¹' Sleft)).toReal ∂(volume : Measure ℝ) := by
            rw [← hLeftFiberEq]
      _ = (volume Sleft).toReal := hLeftAux
  exact ⟨hTotal, by rw [hLeft, hSleft_volume]⟩

/-- Helper for Lemma 3.2.6: the final owner theorem should consume the specialized slice-profile
mass identities directly from convexity plus finite volume, without rebuilding measurability
plumbing in the assembly proof. -/
private lemma firstCoordinateSliceProfile_ae_eq_toMeasurable
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_null : NullMeasurableSet U volume) :
    firstCoordinateSliceProfile i0 U =ᵐ[volume]
      firstCoordinateSliceProfile i0 (toMeasurable volume U) := by
  let slice : ℝ × (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun p ↦ firstCoordinateSlicePoint i0 p.1 p.2
  have hSlicePres : MeasurePreserving slice volume volume := by
    -- The repaired slice-point map preserves product volume, so ambient a.e. equal sets pull back
    -- to a.e. equal slice regions.
    simpa [slice] using firstCoordinateSlicePoint_measurePreserving (i0 := i0)
  have hRegionAE :
      slice ⁻¹' U =ᵐ[volume] slice ⁻¹' toMeasurable volume U := by
    -- Pull back the null-measurable representative equality through the measure-preserving slice
    -- parametrization.
    exact
      (hSlicePres.quasiMeasurePreserving.preimage_ae_eq hU_null.toMeasurable_ae_eq).symm
  have hFiberAE :
      ∀ᵐ t ∂(volume : Measure ℝ),
        {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U} =ᵐ[volume]
          {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ toMeasurable volume U} := by
    -- Fubini turns the product a.e. equality into a.e. equality of almost every vertical fiber.
    filter_upwards [Measure.ae_ae_of_ae_prod hRegionAE] with t ht
    simpa [Filter.EventuallyEq, slice, Set.preimage] using ht
  filter_upwards [hFiberAE] with t ht
  have hFiberVolume :
      volume {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U} =
        volume {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ toMeasurable volume U} :=
    measure_congr ht
  -- Convert the almost-everywhere equality of slice-region volumes to the repaired profile.
  simpa [firstCoordinateSliceProfile] using congrArg ENNReal.toReal hFiberVolume

/-- Helper for Lemma 3.2.6: convexity supplies only a null-measurable ambient set, so the mass
identities are obtained by passing to `toMeasurable volume U` and transporting the slice profile
back almost everywhere. -/
private theorem firstCoordinateSliceProfile_totalMass_leftMass_of_convex
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) :
    (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) = (volume U).toReal ∧
      (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) =
        (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal := by
  let Um : Set (EuclideanSpace ℝ (Fin n)) := toMeasurable volume U
  have hU_null : NullMeasurableSet U volume := hU_convex.nullMeasurableSet volume
  have hProfileAE :
      firstCoordinateSliceProfile i0 U =ᵐ[volume] firstCoordinateSliceProfile i0 Um := by
    -- Route correction: use the explicit `toMeasurable` transport instead of trying to coerce
    -- convexity directly into a `MeasurableSet` hypothesis for the slice-mass theorem.
    simpa [Um] using firstCoordinateSliceProfile_ae_eq_toMeasurable (i0 := i0) U hU_null
  have hUm_finite : volume Um ≠ ⊤ := by
    -- Passing to the measurable representative preserves the total ambient volume.
    simpa [Um, measure_toMeasurable] using hU_finite
  have hUm_mass :
      (∫ t, firstCoordinateSliceProfile i0 Um t ∂volume) = (volume Um).toReal ∧
        (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 Um t ∂volume) =
          (volume (Um ∩ {u | u.ofLp i0 ≤ 0})).toReal := by
    -- Apply the already-proved measurable-set mass theorem to the measurable representative.
    exact
      firstCoordinateSliceProfile_totalMass_leftMass
        (i0 := i0) (U := Um) (measurableSet_toMeasurable volume U) hUm_finite
  have hCut_meas : MeasurableSet {u : EuclideanSpace ℝ (Fin n) | u.ofLp i0 ≤ 0} := by
    -- The retained first-coordinate halfspace is measurable.
    have hcoord : Measurable (fun u : EuclideanSpace ℝ (Fin n) ↦ u i0) := by
      fun_prop
    exact hcoord measurableSet_Iic
  rcases hUm_mass with ⟨hTotalUm, hLeftUm⟩
  refine ⟨?_, ?_⟩
  · -- Rewrite the measurable-representative identity back to the original convex body.
    calc
      ∫ t, firstCoordinateSliceProfile i0 U t ∂volume =
          ∫ t, firstCoordinateSliceProfile i0 Um t ∂volume := by
            exact integral_congr_ae hProfileAE
      _ = (volume Um).toReal := hTotalUm
      _ = (volume U).toReal := by simp [Um, measure_toMeasurable]
  · -- The same transport works for the left-half restricted integral.
    calc
      ∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume =
          ∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 Um t ∂volume := by
            apply setIntegral_congr_ae measurableSet_Iic
            filter_upwards [hProfileAE] with t ht _ using ht
      _ = (volume (Um ∩ {u | u.ofLp i0 ≤ 0})).toReal := hLeftUm
      _ = (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal := by
            simpa [Um] using
              congrArg ENNReal.toReal
                (Measure.measure_toMeasurable_inter_of_sFinite hCut_meas U)

/-- Helper for Lemma 3.2.6: the repaired slice profile is almost everywhere measurable for convex
ambient bodies because it agrees almost everywhere with the measurable representative profile. -/
private lemma aemeasurable_firstCoordinateSliceProfile
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) :
    AEMeasurable (firstCoordinateSliceProfile i0 U) volume := by
  let Um : Set (EuclideanSpace ℝ (Fin n)) := toMeasurable volume U
  have hProfileAE :
      firstCoordinateSliceProfile i0 U =ᵐ[volume] firstCoordinateSliceProfile i0 Um := by
    -- Route correction: record the measurable representative once, then reuse it for all
    -- subsequent `withDensity` and moment calculations.
    simpa [Um] using
      firstCoordinateSliceProfile_ae_eq_toMeasurable
        (i0 := i0) U (hU_convex.nullMeasurableSet volume)
  -- The measurable representative profile supplies the desired `AEMeasurable` owner.
  exact
    (measurable_firstCoordinateSliceProfile
      (i0 := i0) (U := Um) (measurableSet_toMeasurable volume U)).aemeasurable.congr hProfileAE.symm

/-- Helper for Lemma 3.2.6: the frozen first-coordinate pushforward is exactly Lebesgue measure on
`ℝ` with density given by the repaired slice profile. -/
private lemma firstCoordinatePushforward_eq_withDensity_sliceProfile
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) :
    (volume.restrict U).map (fun u ↦ u.ofLp i0) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 U t)) := by
  let Um : Set (EuclideanSpace ℝ (Fin n)) := toMeasurable volume U
  have hRestrict :
      volume.restrict Um = volume.restrict U := by
    -- Replace the null-measurable convex body by its measurable representative before comparing
    -- the pushforward to the `withDensity` normal form.
    simpa [Um] using
      (Measure.restrict_toMeasurable (μ := volume) (s := U) hU_finite)
  have hProfileAE :
      firstCoordinateSliceProfile i0 U =ᵐ[volume] firstCoordinateSliceProfile i0 Um := by
    -- The repaired slice profile is unaffected almost everywhere by the same measurable
    -- representative replacement.
    simpa [Um] using
      firstCoordinateSliceProfile_ae_eq_toMeasurable
        (i0 := i0) U (hU_convex.nullMeasurableSet volume)
  have hUm_finite : volume Um ≠ ⊤ := by
    -- The measurable representative has the same total mass as `U`.
    simpa [Um, measure_toMeasurable] using hU_finite
  have hPushUm :
      (volume.restrict Um).map (fun u ↦ u.ofLp i0) =
        volume.withDensity (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 Um t)) := by
    -- On the measurable representative, the pushforward/set-integral identity upgrades directly to
    -- equality of measures.
    refine Measure.ext fun s hs ↦ ?_
    simpa [withDensity_apply _ hs] using
      firstCoordinatePushforward_apply_eq_lintegral_sliceProfile
        (i0 := i0) (U := Um) (measurableSet_toMeasurable volume U) hUm_finite hs
  -- Transport both the restricted measure and the density back from the measurable
  -- representative to the original convex body.
  calc
    (volume.restrict U).map (fun u ↦ u.ofLp i0)
        = (volume.restrict Um).map (fun u ↦ u.ofLp i0) := by
            rw [hRestrict]
    _ = volume.withDensity (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 Um t)) := hPushUm
    _ = volume.withDensity (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 U t)) := by
          have hDensityAE :
              (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 Um t)) =ᵐ[volume]
                (fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 U t)) := by
            filter_upwards [hProfileAE.symm] with t ht
            simp [ht]
          exact withDensity_congr_ae hDensityAE

/-- Helper for Lemma 3.2.6: once the ambient convex body is bounded, the centered first-coordinate
pushforward moment rewrites directly as the vanishing weighted first moment of the repaired slice
profile. -/
private lemma firstCoordinateSliceProfile_integral_mul_id_eq_zero_of_centered_of_bounded
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤)
    (hU_center : (⨍ u in U, u) = 0) (hU_bounded : Bornology.IsBounded U) :
    ∫ t, t * firstCoordinateSliceProfile i0 U t ∂volume = 0 := by
  have hPushZero :
      ∫ t, t ∂((volume.restrict U).map (fun u ↦ u.ofLp i0)) = 0 := by
    -- The already-established bounded pushforward theorem packages the centered ambient integral
    -- as a zero first moment for the frozen one-dimensional marginal.
    simpa using
      firstCoordinatePushforward_integral_id_eq_zero_of_centered_of_bounded
        (i0 := i0) hU_convex hU_finite hU_center hU_bounded
  have hDensityEq :
      ∫ t, t ∂((volume.restrict U).map (fun u ↦ u.ofLp i0)) =
        ∫ t, firstCoordinateSliceProfile i0 U t * t ∂volume := by
    -- Rewrite the pushforward in the canonical `withDensity` normal form, then evaluate the
    -- resulting Bochner integral through the density.
    rw [firstCoordinatePushforward_eq_withDensity_sliceProfile
      (i0 := i0) hU_convex hU_finite]
    simpa [smul_eq_mul, mul_comm, ENNReal.toReal_ofReal, firstCoordinateSliceProfile_nonneg] using
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := volume)
        (f := fun t ↦ ENNReal.ofReal (firstCoordinateSliceProfile i0 U t))
        (aemeasurable_firstCoordinateSliceProfile (i0 := i0) hU_convex).ennreal_ofReal
        (by
          filter_upwards with t
          simp)
        (fun t : ℝ ↦ t)
  -- Replace the pushforward first moment by the weighted profile moment and read off the
  -- vanishing value.
  have hProfileZero : ∫ t, firstCoordinateSliceProfile i0 U t * t ∂volume = 0 := by
    rw [← hDensityEq]
    exact hPushZero
  simpa [mul_comm] using hProfileZero

/-- Helper for Lemma 3.2.6: finite positive volume supplies the boundedness needed to transport
the centroid condition to the vanishing first moment of the repaired slice profile. -/
private lemma firstCoordinateSliceProfile_integral_mul_id_eq_zero
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hU_center : (⨍ u in U, u) = 0) :
    ∫ t, t * firstCoordinateSliceProfile i0 U t ∂volume = 0 := by
  -- Package the new boundedness theorem into the existing bounded centroid-to-moment bridge.
  exact
    firstCoordinateSliceProfile_integral_mul_id_eq_zero_of_centered_of_bounded
      (i0 := i0) hU_convex hU_finite hU_center
      (convexFiniteVolume_isBounded hU_convex hU_finite hU_pos)

/-- Helper for Lemma 3.2.6: finite positive ambient volume gives strictly positive total mass for
the repaired slice profile. -/
private lemma firstCoordinateSliceProfile_integral_pos_of_convex
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    0 < ∫ t, firstCoordinateSliceProfile i0 U t ∂volume := by
  have hTotal :
      (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) = (volume U).toReal := by
    -- Read the total slice mass from the convex-body mass bridge proved earlier in the file.
    exact
      (firstCoordinateSliceProfile_totalMass_leftMass_of_convex
        (i0 := i0) U hU_convex hU_finite).1
  -- Rewrite the total slice mass to the ambient volume and use finite positive volume.
  rw [hTotal]
  exact ENNReal.toReal_pos hU_pos hU_finite

/-- Helper for Lemma 3.2.6: inserting the deleted coordinates back into the repaired slice model
recovers the original coordinate-update map. -/
private lemma firstCoordinateSlicePoint_eq_coordinateReplace_removeNth
    {n : ℕ} (i0 : Fin n) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    firstCoordinateSlicePoint i0 t (firstCoordinateDeletedCoords i0 y) =
      coordinateReplace i0 y t := by
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  -- Compare the repaired slice point and the original coordinate update coordinatewise.
  ext j
  by_cases hj : j = i0
  · -- At the frozen coordinate, the repaired slice point was constructed to equal `t`.
    subst hj
    simp [firstCoordinateSlicePoint, firstCoordinateDeletedCoords, coordinateReplace_apply]
  · -- Away from `i0`, rewrite the queried coordinate through the deleted-index parametrization.
    have hj' : Fin.cast h.symm j ≠ i0' := by
      intro hji
      apply hj
      apply Fin.ext
      simpa [i0'] using congrArg Fin.val hji
    rcases Fin.exists_succAbove_eq (x := Fin.cast h.symm j) (y := i0') hj' with ⟨k, hk⟩
    have hcast : Fin.cast h (i0'.succAbove k) = j := by
      apply Fin.ext
      simpa using congrArg Fin.val hk
    rw [← hcast]
    have hne : Fin.cast h (i0'.succAbove k) ≠ i0 := by
      simpa [hcast] using hj
    simpa only [firstCoordinateSlicePoint, firstCoordinateDeletedCoords, coordinateReplace_apply,
      hne] using
      @Fin.insertNth_apply_succAbove (n - 1) (fun _ ↦ ℝ) (Fin.cast h.symm i0) t
        (fun j => y.ofLp (Fin.cast h ((Fin.cast h.symm i0).succAbove j))) k

/-- Helper for Profile: deleting the free coordinates from a repaired slice point recovers the
original codimension-one parameter. -/
private lemma firstCoordinateDeletedCoords_slicePoint
    {n : ℕ} (i0 : Fin n) (t : ℝ) (y : Fin (n - 1) → ℝ) :
    firstCoordinateDeletedCoords i0 (firstCoordinateSlicePoint i0 t y) = y := by
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  -- Evaluate the deleted-coordinate tuple at an arbitrary free index and unfold the inserted
  -- coordinate tuple only once.
  funext j
  simpa [firstCoordinateDeletedCoords, firstCoordinateSlicePoint, hn, h, i0'] using
    @Fin.insertNth_apply_succAbove (n - 1) (fun _ ↦ ℝ) i0' t y j

/-- Helper for Profile: the repaired slice-point parametrization commutes with affine
combinations of the frozen coordinate and the free coordinates. -/
private lemma firstCoordinateSlicePoint_affineCombination
    {n : ℕ} (i0 : Fin n) (s t a b : ℝ) (y z : Fin (n - 1) → ℝ) :
    firstCoordinateSlicePoint i0 (a * s + b * t) (a • y + b • z) =
      a • firstCoordinateSlicePoint i0 s y + b • firstCoordinateSlicePoint i0 t z := by
  -- Compare the repaired slice points coordinatewise, splitting at the frozen coordinate `i0`.
  ext j
  by_cases hj : j = i0
  · subst hj
    -- At `i0`, both sides are the same scalar affine combination.
    simp [firstCoordinateSlicePoint_apply_self]
  · let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
    let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
    let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
    have hj' : Fin.cast h.symm j ≠ i0' := by
      intro hji
      apply hj
      apply Fin.ext
      simpa [i0'] using congrArg Fin.val hji
    rcases Fin.exists_succAbove_eq (x := Fin.cast h.symm j) (y := i0') hj' with ⟨k, hk⟩
    have hcast : Fin.cast h (i0'.succAbove k) = j := by
      apply Fin.ext
      simpa using congrArg Fin.val hk
    have hLeft :
        firstCoordinateSlicePoint i0 (a * s + b * t) (a • y + b • z) j =
          a * y k + b * z k := by
      rw [← hcast]
      simp [firstCoordinateSlicePoint, i0', Pi.smul_apply]
    have hFirst :
        firstCoordinateSlicePoint i0 s y j = y k := by
      rw [← hcast]
      simpa [firstCoordinateSlicePoint, hn, h, i0'] using
        @Fin.insertNth_apply_succAbove (n - 1) (fun _ ↦ ℝ) i0' s y k
    have hSecond :
        firstCoordinateSlicePoint i0 t z j = z k := by
      rw [← hcast]
      simpa [firstCoordinateSlicePoint, hn, h, i0'] using
        @Fin.insertNth_apply_succAbove (n - 1) (fun _ ↦ ℝ) i0' t z k
    -- Away from `i0`, the repaired slice point just records the affine combination of the free
    -- coordinates.
    calc
      firstCoordinateSlicePoint i0 (a * s + b * t) (a • y + b • z) j
          = a * y k + b * z k := hLeft
      _ = a * firstCoordinateSlicePoint i0 s y j + b * firstCoordinateSlicePoint i0 t z j := by
            rw [hFirst, hSecond]
      _ = (a • firstCoordinateSlicePoint i0 s y + b • firstCoordinateSlicePoint i0 t z) j := by
            simp

/-- Helper for Profile: convexity of the ambient body transports slice-fiber witnesses across
affine combinations once the repaired slice-point map is normalized. -/
private lemma mem_firstCoordinateSliceFiber_affineCombination
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) {s t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {y z : Fin (n - 1) → ℝ}
    (hy : firstCoordinateSlicePoint i0 s y ∈ U)
    (hz : firstCoordinateSlicePoint i0 t z ∈ U) :
    firstCoordinateSlicePoint i0 (a * s + b * t) (a • y + b • z) ∈ U := by
  -- Rewrite the repaired slice point as the convex combination of the endpoint witnesses.
  rw [firstCoordinateSlicePoint_affineCombination]
  exact hU_convex hy hz ha hb hab

/-- Helper for Profile: if the ambient body is bounded, then every repaired codimension-one slice
fiber is bounded as well. -/
private lemma firstCoordinateSliceFiber_bounded_of_bodyBounded
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_bounded : Bornology.IsBounded U) (t : ℝ) :
    Bornology.IsBounded {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U} := by
  rcases hU_bounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n)) with ⟨R, hR⟩
  refine
    (Bornology.forall_isBounded_image_eval_iff
      (s := {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U})).1 ?_
  intro j
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
  refine ⟨R, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  let hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i0.1) (Nat.succ_le_of_lt i0.is_lt)
  let h : (n - 1) + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hn)
  let i0' : Fin ((n - 1) + 1) := Fin.cast h.symm i0
  let u : EuclideanSpace ℝ (Fin n) := firstCoordinateSlicePoint i0 t y
  have hu_mem : u ∈ U := hy
  have hu_memBall : u ∈ Metric.closedBall 0 R := hR hu_mem
  have hu_bound : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hu_memBall
  have hcoord :
      u.ofLp (Fin.cast h (i0'.succAbove j)) = y j := by
    -- Read the chosen free coordinate back through the deleted-coordinate round trip.
    have hround :=
      congrArg (fun f : Fin (n - 1) → ℝ => f j)
        (firstCoordinateDeletedCoords_slicePoint (i0 := i0) (t := t) (y := y))
    simpa [u, firstCoordinateDeletedCoords, hn, h, i0'] using hround
  have hy_norm : ‖y j‖ ≤ ‖u‖ := by
    rw [← hcoord]
    exact PiLp.norm_apply_le u (Fin.cast h (i0'.succAbove j))
  -- Each free coordinate stays inside the same scalar closed ball as the ambient bounded body.
  simpa [Metric.mem_closedBall, Real.dist_eq] using le_trans hy_norm hu_bound

/-- Helper for Profile: each repaired codimension-one slice fiber is convex when the ambient body
is convex. -/
private lemma convex_firstCoordinateSliceFiber
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (t : ℝ) :
    Convex ℝ {y : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 t y ∈ U} := by
  intro y hy z hz a b ha hb hab
  -- Transport the two slice witnesses across the affine combination in the repaired fiber model.
  have hcomb : a * t + b * t = t := by
    calc
      a * t + b * t = (a + b) * t := by ring
      _ = t := by simp [hab]
  simpa [hcomb] using
    mem_firstCoordinateSliceFiber_affineCombination
      (i0 := i0) (s := t) (t := t) hU_convex ha hb hab hy hz

/-- Helper for Profile: a weighted combination of witnesses from two repaired slice fibers lands in
the repaired fiber over the weighted-average first coordinate. -/
private lemma smul_add_mem_firstCoordinateSliceFiber
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) {x y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u v : Fin (n - 1) → ℝ}
    (hu : firstCoordinateSlicePoint i0 x u ∈ U)
    (hv : firstCoordinateSlicePoint i0 y v ∈ U) :
    a • u + b • v ∈
      {w : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 (a * x + b * y) w ∈ U} := by
  -- Repackage the affine-combination witness in the codimension-one fiber language.
  exact
    mem_firstCoordinateSliceFiber_affineCombination
      (i0 := i0) hU_convex ha hb hab hu hv

/-- Helper for Profile: the weighted Minkowski sum of two repaired slice fibers sits inside the
repaired fiber over the weighted-average first coordinate. -/
private lemma smul_add_firstCoordinateSliceFiber_subset
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) {x y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • {u : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 x u ∈ U} +
        b • {v : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 y v ∈ U} ⊆
      {w : Fin (n - 1) → ℝ | firstCoordinateSlicePoint i0 (a * x + b * y) w ∈ U} := by
  intro w hw
  rcases Set.mem_add.mp hw with ⟨u, hu, v, hv, rfl⟩
  rcases Set.mem_smul_set.mp hu with ⟨u', hu', rfl⟩
  rcases Set.mem_smul_set.mp hv with ⟨v', hv', rfl⟩
  -- Unpack the pointwise Minkowski-sum witness and repackage it as a repaired fiber witness.
  exact
    smul_add_mem_firstCoordinateSliceFiber
      (i0 := i0) hU_convex ha hb hab hu' hv'

/-- Helper for Lemma 3.2.6: updating a coordinate by the value it already has does not change the
ambient point. -/
private lemma coordinateReplace_eq_self_of_coordinate_eq
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) (hy : y i0 = t) :
    coordinateReplace i0 y t = y := by
  -- Compare the updated point with the original one coordinatewise.
  ext j
  by_cases hj : j = i0
  · subst hj
    simp [coordinateReplace_apply, hy]
  · simp [coordinateReplace_apply, hj]

/-- Helper for Lemma 3.2.6: the repaired slice support agrees with the original support interval
for attainable first-coordinate values. -/
private lemma firstCoordinateSliceSupport_eq_firstCoordinateSupport
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) :
    firstCoordinateSliceSupport i0 U = firstCoordinateSupport i0 U := by
  -- Translate witnesses back and forth using the coordinate-update description of slice points.
  ext t
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨firstCoordinateSlicePoint i0 t y, ?_⟩
    have hy_coord : firstCoordinateSlicePoint i0 t y i0 = t := by
      simp [firstCoordinateSlicePoint]
    simpa [coordinateReplace_eq_self_of_coordinate_eq i0 (firstCoordinateSlicePoint i0 t y) t
      hy_coord] using hy
  · rintro ⟨y, hy⟩
    refine ⟨firstCoordinateDeletedCoords i0 y, ?_⟩
    simpa [firstCoordinateSlicePoint_eq_coordinateReplace_removeNth] using hy

/-- Helper for Profile: the repaired slice support is convex because it is the same first-coordinate
support interval seen through the cast-stable slice parametrization. -/
private lemma convex_firstCoordinateSliceSupport
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) :
    Convex ℝ (firstCoordinateSliceSupport i0 U) := by
  -- Rewrite the repaired support back to the original first-coordinate support and reuse its
  -- convexity owner.
  rw [firstCoordinateSliceSupport_eq_firstCoordinateSupport]
  simpa [firstCoordinateSupport] using convex_firstCoordinateSupport i0 hU_convex

/-- Helper for Profile: any point of `U` contributes its distinguished coordinate to the repaired
slice support. -/
private lemma mem_firstCoordinateSliceSupport_of_mem
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ U) :
    u.ofLp i0 ∈ firstCoordinateSliceSupport i0 U := by
  -- Pass to the original support spelling, where the ambient point itself is the required witness.
  rw [firstCoordinateSliceSupport_eq_firstCoordinateSupport]
  refine ⟨u, ?_⟩
  simpa [coordinateReplace_eq_self_of_coordinate_eq i0 u (u.ofLp i0) rfl] using hu

/-- Helper for Lemma 3.2.6: the explicit support of admissible first-coordinate values is convex
whenever `U` is convex. -/
private lemma firstCoordinateSupport_convex
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) :
    Convex ℝ (firstCoordinateSupport i0 U) := by
  -- Rewrite the frozen support spelling to the slice-level convexity owner.
  simpa [firstCoordinateSupport] using convex_firstCoordinateSupport i0 hU_convex

/-- Helper for Lemma 3.2.6: every coordinate fiber through a point `y` stays convex when the ambient
set `U` is convex. -/
private lemma firstCoordinateFiber_convex
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU_convex : Convex ℝ U) :
    Convex ℝ {t : ℝ | coordinateReplace i0 y t ∈ U} := by
  -- Keep the fiber spelling aligned with the slice API instead of reproving convexity locally.
  simpa using convex_coordinateFiber i0 y hU_convex

/-- Helper for Lemma 3.2.6: the explicit section profile is everywhere nonnegative because it is
defined as the real-valued volume of a fiber. -/
private lemma firstCoordinateSectionProfile_nonneg
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    0 ≤ firstCoordinateSectionProfile i0 U t := by
  -- `ENNReal.toReal` of a volume is automatically nonnegative.
  simp [firstCoordinateSectionProfile]

/-- Helper for Lemma 3.2.6: the section profile vanishes off the admissible support interval. -/
private lemma firstCoordinateSectionProfile_eq_zero_of_not_mem_support
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) {t : ℝ}
    (ht : t ∉ firstCoordinateSupport i0 U) :
    firstCoordinateSectionProfile i0 U t = 0 := by
  have hEmpty : {y : EuclideanSpace ℝ (Fin n) | coordinateReplace i0 y t ∈ U} = ∅ := by
    -- Outside the support there are no fiber witnesses, so the fiber set is empty.
    ext y
    constructor
    · intro hy
      exact (ht ⟨y, hy⟩).elim
    · intro hy
      simp at hy
  -- An empty fiber has zero volume, hence zero explicit profile.
  simp [firstCoordinateSectionProfile, hEmpty]

/-- Helper for Lemma 3.2.6: the first-coordinate pushforward records the total mass and the
retained left-half mass of the coordinate cut. -/
private lemma firstCoordinatePushforward_massLeftMass
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    μ Set.univ = volume U ∧
      μ (Set.Iic 0) = volume (U ∩ {u | u.ofLp i0 ≤ 0}) := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  have hμ_univ : μ Set.univ = volume U := by
    -- Evaluate the pushforward on the whole line.
    simpa [μ] using
      (Measure.map_apply (μ := volume.restrict U)
        (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u.ofLp i0)
        (by fun_prop) MeasurableSet.univ)
  have hμ_left : μ (Set.Iic 0) = volume (U ∩ {u | u.ofLp i0 ≤ 0}) := by
    -- The retained cut is the coordinate preimage of `(-∞, 0]`.
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

/-- Helper for Lemma 3.2.6: after freezing the first-coordinate pushforward, the remaining
measure-side conditions already available in the support file are finite and positive total mass. -/
private lemma firstCoordinatePushforward_sideConditions
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    μ Set.univ ≠ ⊤ ∧
      μ Set.univ ≠ 0 := by
  let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
  obtain ⟨hμ_univ, _hμ_left⟩ :=
    firstCoordinatePushforward_massLeftMass i0 U
  -- Read the side conditions from the normalized pushforward identities.
  exact ⟨by rwa [hμ_univ], by rwa [hμ_univ]⟩

/-- Helper for Profile: the coordinate-cut ratio is exactly the left-mass ratio of the
first-coordinate pushforward. -/
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
    firstCoordinatePushforward_massLeftMass i0 U
  refine ⟨?_, ?_, ?_⟩
  · -- Rewrite the target ratio entirely in the pushforward spelling.
    rw [hμ_left, hμ_univ]
  · -- Finite mass is inherited from the ambient convex body.
    rwa [hμ_univ]
  · -- Positive mass is inherited from the ambient convex body as well.
    rwa [hμ_univ]

/-- Helper for Profile: once the geometric coordinate-cut estimate is available, the pushforward
theorem is just the normalized ratio rewrite. -/
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
  -- The remaining pushforward theorem is just the coordinate-model ratio under its canonical
  -- normalized spelling.
  have hμ_bound :
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
    rw [← hμ_ratio]
    exact hcoord_bound
  simpa [μ] using hμ_bound

/-- Helper for Lemma 3.2.6: once the repaired slice profile itself satisfies the sharp left-half
ratio bound, the specialized slice-mass identities turn it into the ambient coordinate-cut bound.
-/
private lemma firstCoordinateCoordinateBound_of_sliceProfileRatioBound
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hMass :
      (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) = (volume U).toReal ∧
        (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) =
          (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal)
    (hRatio :
      (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) /
          (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) ≤
        1 - Real.exp (-1)) :
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) := by
  rcases hMass with ⟨hTotal, hLeft⟩
  -- Rewrite the ambient ratio through the repaired slice-profile masses before applying the sharp
  -- one-dimensional ratio input.
  rw [← hLeft, ← hTotal]
  exact hRatio

/-- Helper for Profile: the coordinate-cut bound and the frozen first-coordinate pushforward bound
are equivalent because both ratios are the same after the canonical pushforward rewrite. -/
private lemma firstCoordinateCoordinateBound_iff_pushforwardBound
    {n : ℕ} (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) ↔
      let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
      (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
  constructor
  · intro hcoord_bound
    -- Read the pushforward formulation directly from the already-proved ratio rewrite.
    exact
      firstCoordinatePushforward_bound_of_coordinateBound
        i0 U hU_finite hU_pos hcoord_bound
  · intro hμ_bound
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    have hμ_ratio :
        (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal =
          (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal :=
      (firstCoordinatePushforward_ratio_eq i0 U hU_finite hU_pos).1
    have hμ_bound' :
        (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
      -- Unfold the frozen pushforward measure exactly once before comparing the two surfaces.
      simpa [μ] using hμ_bound
    -- The coordinate spelling is just the same ratio viewed before freezing the pushforward.
    rw [hμ_ratio]
    exact hμ_bound'

/-- Helper for Profile: the origin cut by the first coordinate vector is exactly the nonpositive
first-coordinate halfspace. -/
private lemma cuttingHalfspace_origin_single_eq_firstCoordinate_nonpos
    {n : ℕ} (i0 : Fin n) :
    cuttingHalfspace (0 : EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i0 (1 : ℝ)) =
      {u | u.ofLp i0 ≤ 0} := by
  -- Rewrite the owner halfspace inequality in coordinates and collapse the unit scalar.
  ext u
  constructor
  · intro hu
    have huInner : inner ℝ (EuclideanSpace.single i0 (1 : ℝ)) u ≤ 0 := by
      simpa [mem_cuttingHalfspace_iff] using hu
    have hu' : (1 : ℝ) * u.ofLp i0 ≤ 0 := by
      have hsingle :
          inner ℝ (EuclideanSpace.single i0 (1 : ℝ)) u = (1 : ℝ) * u.ofLp i0 := by
        simpa using EuclideanSpace.inner_single_left i0 (1 : ℝ) u
      rw [hsingle] at huInner
      exact huInner
    simpa using hu'
  · intro hu
    have hu' : (1 : ℝ) * u.ofLp i0 ≤ 0 := by
      simpa using hu
    have huInner : inner ℝ (EuclideanSpace.single i0 (1 : ℝ)) u ≤ 0 := by
      have hsingle :
          inner ℝ (EuclideanSpace.single i0 (1 : ℝ)) u = (1 : ℝ) * u.ofLp i0 := by
        simpa using EuclideanSpace.inner_single_left i0 (1 : ℝ) u
      rw [hsingle]
      exact hu'
    simpa [mem_cuttingHalfspace_iff] using huInner

/-- Helper for Lemma 3.2.6: finite positive volume bounds the first-coordinate support because the
support values come from actual points of the bounded convex body. -/
private lemma firstCoordinateSliceSupport_bounded_of_convex_finite_pos
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0) :
    Bornology.IsBounded (firstCoordinateSliceSupport i0 U) := by
  have hU_bounded : Bornology.IsBounded U :=
    convexFiniteVolume_isBounded hU_convex hU_finite hU_pos
  rcases hU_bounded.exists_norm_le with ⟨R, hR⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
  refine ⟨R, ?_⟩
  intro t ht
  rcases ht with ⟨y, hy⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  have ht_norm :
      ‖t‖ ≤ ‖firstCoordinateSlicePoint i0 t y‖ := by
    -- The distinguished coordinate is controlled by the ambient Euclidean norm.
    simpa [firstCoordinateSlicePoint_apply_self] using
      (PiLp.norm_apply_le (firstCoordinateSlicePoint i0 t y) i0)
  have hBound : ‖t‖ ≤ R := le_trans ht_norm (hR _ hy)
  simpa [Metric.mem_closedBall, Real.dist_eq] using hBound

/-- Helper for Lemma 3.2.6: positive total slice mass forces the repaired first-coordinate support
to be nonempty. -/
private lemma firstCoordinateSliceSupport_nonempty_of_integral_pos
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hMassPos : 0 < ∫ t, firstCoordinateSliceProfile i0 U t ∂volume) :
    (firstCoordinateSliceSupport i0 U).Nonempty := by
  by_contra hSupportEmpty
  have hSupportEq : firstCoordinateSliceSupport i0 U = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hSupportEmpty
  have hProfileZero : ∀ t : ℝ, firstCoordinateSliceProfile i0 U t = 0 := by
    intro t
    apply firstCoordinateSliceProfile_eq_zero_of_not_mem_support (i0 := i0) (U := U)
    simp [hSupportEq]
  have hMassZero : ∫ t, firstCoordinateSliceProfile i0 U t ∂volume = 0 := by
    simp [hProfileZero]
  linarith

/-- Helper for Lemma 3.2.6: a bounded repaired first-coordinate support is contained in the
interval from its infimum to its supremum. -/
private lemma firstCoordinateSliceSupport_subset_Icc_sInf_sSup_of_bounded
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U)) :
    firstCoordinateSliceSupport i0 U ⊆
      Set.Icc (sInf (firstCoordinateSliceSupport i0 U)) (sSup (firstCoordinateSliceSupport i0 U)) :=
  hSupportBound.subset_Icc_sInf_sSup

/-- Helper for Profile: a bounded nonempty convex slice support contains the open interval between
its infimum and supremum. -/
private lemma firstCoordinateSliceSupport_Ioo_sInf_sSup_subset_of_convex_bounded_nonempty
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U))
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U))
    (hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty) :
    Set.Ioo (sInf (firstCoordinateSliceSupport i0 U))
        (sSup (firstCoordinateSliceSupport i0 U)) ⊆
      firstCoordinateSliceSupport i0 U := by
  let S : Set ℝ := firstCoordinateSliceSupport i0 U
  have hConnected : IsConnected S := by
    -- A nonempty convex subset of `ℝ` is connected, so it contains the open interval between its
    -- extremal points.
    exact ⟨hSupportNonempty, hSupportConvex.ordConnected.isPreconnected⟩
  -- Connected bounded subsets of `ℝ` contain the interval core between `sInf` and `sSup`.
  simpa [S] using
    hConnected.Ioo_csInf_csSup_subset hSupportBound.bddBelow hSupportBound.bddAbove

/-- Helper for Profile: a bounded nonempty convex slice support agrees almost everywhere with the
closed interval between its infimum and supremum; only the two endpoints can differ. -/
private lemma firstCoordinateSliceSupport_ae_eq_Icc_sInf_sSup_of_convex_bounded_nonempty
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U))
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U))
    (hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty) :
    firstCoordinateSliceSupport i0 U =ᵐ[volume]
      Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
        (sSup (firstCoordinateSliceSupport i0 U)) := by
  let S : Set ℝ := firstCoordinateSliceSupport i0 U
  let a : ℝ := sInf S
  let b : ℝ := sSup S
  have hSubset : S ⊆ Set.Icc a b := by
    -- Every support point already lies in the closed interval cut out by `sInf` and `sSup`.
    simpa [S, a, b] using
      firstCoordinateSliceSupport_subset_Icc_sInf_sSup_of_bounded
        (i0 := i0) (U := U) hSupportBound
  have hIooSubset : Set.Ioo a b ⊆ S := by
    -- The only possible gap between the support and the closed interval lies at the endpoints.
    simpa [S, a, b] using
      firstCoordinateSliceSupport_Ioo_sInf_sSup_subset_of_convex_bounded_nonempty
        (i0 := i0) (U := U) hSupportConvex hSupportBound hSupportNonempty
  have hIooAe : Set.Ioo a b =ᵐ[volume] Set.Icc a b := Ioo_ae_eq_Icc
  refine MeasureTheory.ae_eq_set.2 ?_
  constructor
  · have hDiffEmpty : S \ Set.Icc a b = ∅ := Set.diff_eq_empty.2 hSubset
    -- The support-to-interval direction holds pointwise, hence certainly almost everywhere.
    simpa [S, a, b, hDiffEmpty]
  · have hIccDiffIoo : volume (Set.Icc a b \ Set.Ioo a b) = 0 :=
      (MeasureTheory.ae_eq_set.mp hIooAe).2
    -- Any interval point missing from the support must sit on the null boundary endpoints.
    refine measure_mono_null ?_ hIccDiffIoo
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxIoo
    exact hx.2 (hIooSubset hxIoo)

/-- Helper for Lemma 3.2.6: once the repaired first-coordinate support is bounded, the slice
profile vanishes outside the interval between its infimum and supremum. -/
private lemma firstCoordinateSliceProfile_eq_zero_of_not_mem_supportInterval
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U)) {t : ℝ}
    (ht :
      t ∉ Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
        (sSup (firstCoordinateSliceSupport i0 U))) :
    firstCoordinateSliceProfile i0 U t = 0 := by
  apply firstCoordinateSliceProfile_eq_zero_of_not_mem_support (i0 := i0) (U := U)
  intro htSupport
  exact ht
    (firstCoordinateSliceSupport_subset_Icc_sInf_sSup_of_bounded
      (i0 := i0) (U := U) hSupportBound htSupport)

/-- Helper for Profile: the natural `1 / (n - 1)`-root of the repaired slice profile raises back
to the original density. -/
private lemma firstCoordinateSliceProfileRootPow_eq
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    ((firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) ^ (n - 1 : ℕ) =
      firstCoordinateSliceProfile i0 U t := by
  have hProfileNonneg :
      0 ≤ firstCoordinateSliceProfile i0 U t :=
    firstCoordinateSliceProfile_nonneg i0 U t
  have hp_ne_zero : n - 1 ≠ 0 := by
    omega
  -- Normalize the root-power expression with the standard nonnegative `Real.rpow` identity.
  simpa [one_div] using Real.rpow_inv_natCast_pow hProfileNonneg hp_ne_zero

/-- Helper for Profile: after bounded-support, positive-mass, and zero-moment transport are in
place, the remaining frontier is the one-dimensional slice-profile inequality on the canonical
support interval. -/
private lemma firstCoordinateSliceProfileRoot_eq_zero_of_not_mem_support
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) {t : ℝ}
    (ht : t ∉ firstCoordinateSliceSupport i0 U) :
    (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0 := by
  have hExponentPos : 0 < (((n - 1 : ℕ)⁻¹ : ℝ)) := by
    have hNat : 0 < n - 1 := by
      omega
    have hReal : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    simpa using inv_pos.mpr hReal
  -- Rewrite the profile to zero off support, then evaluate the positive root of zero.
  rw [firstCoordinateSliceProfile_eq_zero_of_not_mem_support (i0 := i0) (U := U) ht]
  exact Real.zero_rpow (ne_of_gt hExponentPos)

/-- Helper for Profile: once the repaired slice support is normalized to its canonical interval,
the rooted slice profile vanishes off that interval as well. -/
private lemma firstCoordinateSliceProfileRoot_eq_zero_of_not_mem_supportInterval
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U)) {t : ℝ}
    (ht :
      t ∉ Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
        (sSup (firstCoordinateSliceSupport i0 U))) :
    (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0 := by
  have hExponentPos : 0 < (((n - 1 : ℕ)⁻¹ : ℝ)) := by
    have hNat : 0 < n - 1 := by
      omega
    have hReal : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    simpa using inv_pos.mpr hReal
  -- Rewrite the interval-outside point to zero through the canonical support normalization.
  rw [firstCoordinateSliceProfile_eq_zero_of_not_mem_supportInterval
    (i0 := i0) (U := U) hSupportBound ht]
  exact Real.zero_rpow (ne_of_gt hExponentPos)

/-- Helper for Profile: a nonnegative concave function on a closed interval that vanishes at an
interior point must vanish on the whole interval. -/
private lemma concaveOn_eq_zero_of_mem_Ioo_of_nonneg
    {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_concave : ConcaveOn ℝ (Set.Icc a b) ψ)
    (hψ_nonneg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → 0 ≤ ψ t)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (ht_zero : ψ t = 0) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Icc a b → ψ x = 0 := by
  intro x hx
  have hab : a ≤ b := le_of_lt (lt_trans ht.1 ht.2)
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  by_cases hxt : x = t
  · subst hxt
    exact ht_zero
  by_cases hxt_lt : x < t
  · let α : ℝ := (b - t) / (b - x)
    let β : ℝ := (t - x) / (b - x)
    have hbx_pos : 0 < b - x := by
      linarith [hx.2, ht.2]
    have hα_pos : 0 < α := by
      have hbt_pos : 0 < b - t := by
        linarith [ht.2]
      dsimp [α]
      exact div_pos hbt_pos hbx_pos
    have hβ_pos : 0 < β := by
      have htx_pos : 0 < t - x := by
        linarith
      dsimp [β]
      exact div_pos htx_pos hbx_pos
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      field_simp [hbx_pos.ne']
      ring
    have ht_combo : α * x + β * b = t := by
      dsimp [α, β]
      field_simp [hbx_pos.ne']
      ring_nf
    have hconc :
        α * ψ x + β * ψ b ≤ 0 := by
      simpa [smul_eq_mul, ht_combo, ht_zero] using
        hψ_concave.2 hx hb_mem hα_pos.le hβ_pos.le hαβ
    have hx_nonneg : 0 ≤ ψ x := hψ_nonneg hx
    have hb_nonneg : 0 ≤ ψ b := hψ_nonneg hb_mem
    have hαx_zero : α * ψ x = 0 := by
      nlinarith [hconc, mul_nonneg hα_pos.le hx_nonneg, mul_nonneg hβ_pos.le hb_nonneg]
    exact (mul_eq_zero.mp hαx_zero).resolve_left hα_pos.ne'
  · have htx_lt : t < x := lt_of_le_of_ne (le_of_not_gt hxt_lt) (Ne.symm hxt)
    let α : ℝ := (x - t) / (x - a)
    let β : ℝ := (t - a) / (x - a)
    have hxa_pos : 0 < x - a := by
      linarith [hx.1, ht.1]
    have hα_pos : 0 < α := by
      have hxt_pos : 0 < x - t := by
        linarith
      dsimp [α]
      exact div_pos hxt_pos hxa_pos
    have hβ_pos : 0 < β := by
      have hta_pos : 0 < t - a := by
        linarith [ht.1]
      dsimp [β]
      exact div_pos hta_pos hxa_pos
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      field_simp [hxa_pos.ne']
      ring
    have ht_combo : α * a + β * x = t := by
      dsimp [α, β]
      field_simp [hxa_pos.ne']
      ring_nf
    have hconc :
        α * ψ a + β * ψ x ≤ 0 := by
      simpa [smul_eq_mul, ht_combo, ht_zero] using
        hψ_concave.2 ha_mem hx hα_pos.le hβ_pos.le hαβ
    have ha_nonneg : 0 ≤ ψ a := hψ_nonneg ha_mem
    have hx_nonneg : 0 ≤ ψ x := hψ_nonneg hx
    have hβx_zero : β * ψ x = 0 := by
      nlinarith [hconc, mul_nonneg hα_pos.le ha_nonneg, mul_nonneg hβ_pos.le hx_nonneg]
    exact (mul_eq_zero.mp hβx_zero).resolve_left hβ_pos.ne'

/-- Helper for Profile: positive powered mass forces a nonnegative concave interval function to be
strictly positive on the interior. -/
private lemma intervalPow_pos_on_interior_of_concave_nonneg_of_integral_pos
    {m : ℕ} (hm : 0 < m) {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_concave : ConcaveOn ℝ (Set.Icc a b) ψ)
    (hψ_nonneg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → 0 ≤ ψ t)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m := by
  intro t ht
  have ht_mem : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hpow_nonneg : 0 ≤ (ψ t) ^ m := by
    exact pow_nonneg (hψ_nonneg ht_mem) m
  have hpow_ne_zero : (ψ t) ^ m ≠ 0 := by
    intro hpow_zero
    have hψ_zero : ψ t = 0 := by
      exact eq_zero_of_pow_eq_zero hpow_zero
    have hzero_on :
        ∀ ⦃x : ℝ⦄, x ∈ Set.Icc a b → ψ x = 0 :=
      concaveOn_eq_zero_of_mem_Ioo_of_nonneg hψ_concave hψ_nonneg ht hψ_zero
    have hzero_all : ∀ x : ℝ, ψ x = 0 := by
      intro x
      by_cases hx : x ∈ Set.Icc a b
      · exact hzero_on hx
      · exact hψ_off hx
    have hMassZero : ∫ t, (ψ t) ^ m ∂volume = 0 := by
      simp [hzero_all, hm.ne']
    linarith
  exact lt_of_le_of_ne hpow_nonneg (Ne.symm hpow_ne_zero)

/-- Helper for Profile: the unresolved geometric input is the rooted-volume Brunn-Minkowski
inequality for bounded convex fibers in `Fin (n - 1) → ℝ`. -/
private theorem sliceFiber_rooted_volume_brunn_minkowski_sumset_fin
    {n : ℕ} (hn : 2 ≤ n) {A B : Set (Fin (n - 1) → ℝ)} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hA_bounded : Bornology.IsBounded A) (hB_bounded : Bornology.IsBounded B)
    (hA_convex : Convex ℝ A) (hB_convex : Convex ℝ B) :
    a * (volume A).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) +
        b * (volume B).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) ≤
      (volume (a • A + b • B)).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) := by
  -- Route correction: the canonical geometric owner is the weighted Minkowski sum itself, before
  -- any monotonicity step into a larger ambient comparison set.
  -- TODO: package the bounded convex sets as the finite-dimensional Brunn-Minkowski input on
  -- `Fin (n - 1) → ℝ`, prove the rooted-volume bound for `a • A + b • B`, and keep the wrapper
  -- theorem below for the later `measure_mono` transport only.
  sorry

/-- Helper for Profile: once the canonical weighted-sum Brunn-Minkowski owner is available, any
bounded convex comparison set containing that sum inherits the same rooted-volume lower bound. -/
private theorem sliceFiber_rooted_volume_brunn_minkowski_fin
    {n : ℕ} (hn : 2 ≤ n) {A B C : Set (Fin (n - 1) → ℝ)} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hA_bounded : Bornology.IsBounded A) (hB_bounded : Bornology.IsBounded B)
    (hA_convex : Convex ℝ A) (hB_convex : Convex ℝ B)
    (hC_bounded : Bornology.IsBounded C)
    (hsubset : a • A + b • B ⊆ C) :
    a * (volume A).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) +
        b * (volume B).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) ≤
      (volume C).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) := by
  have hSumset :
      a * (volume A).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) +
          b * (volume B).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) ≤
        (volume (a • A + b • B)).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) :=
    sliceFiber_rooted_volume_brunn_minkowski_sumset_fin
      (hn := hn) ha hb hab hA_bounded hB_bounded hA_convex hB_convex
  have hVolumeMono : volume (a • A + b • B) ≤ volume C := measure_mono hsubset
  have hC_finite : volume C ≠ ⊤ := hC_bounded.measure_lt_top.ne
  have hToRealMono :
      (volume (a • A + b • B)).toReal ≤ (volume C).toReal :=
    ENNReal.toReal_mono hC_finite hVolumeMono
  have hRootMono :
      (volume (a • A + b • B)).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) ≤
        (volume C).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) := by
    -- The rooted-volume exponent is nonnegative, so the real-valued volume comparison can be
    -- passed through the power directly.
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg hToRealMono (by positivity)
  exact le_trans hSumset hRootMono

/-- Helper for Profile: the Brunn-Minkowski owner should show that the rooted slice profile is
concave on the canonical support interval cut out by `sInf` and `sSup`. -/
private theorem firstCoordinateSliceProfileRoot_pairwise_brunn_minkowski
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U)
    (hU_bounded : Bornology.IsBounded U)
    (hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty)
    (hSupportSubset :
      firstCoordinateSliceSupport i0 U ⊆
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)))
    (hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U))
    (hOffSupportRoot :
      ∀ ⦃t : ℝ⦄, t ∉ firstCoordinateSliceSupport i0 U →
        (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0)
    (hNonnegRoot :
      ∀ ⦃t : ℝ⦄, t ∈ firstCoordinateSliceSupport i0 U →
        0 ≤ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)))
    {x y a b : ℝ}
    (hx :
      x ∈
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)))
    (hy :
      y ∈
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    let φ : ℝ → ℝ :=
      fun t ↦ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))
    a * φ x + b * φ y ≤ φ (a * x + b * y) := by
  -- Route correction: the support interval packaging is already stable. The remaining geometric
  -- blocker is exactly the Brunn-Minkowski inequality for the repaired slice fibers.
  let Fx : Set (Fin (n - 1) → ℝ) := {u | firstCoordinateSlicePoint i0 x u ∈ U}
  let Fy : Set (Fin (n - 1) → ℝ) := {v | firstCoordinateSlicePoint i0 y v ∈ U}
  let Fxy : Set (Fin (n - 1) → ℝ) := {w | firstCoordinateSlicePoint i0 (a * x + b * y) w ∈ U}
  have hFiberSubset : a • Fx + b • Fy ⊆ Fxy := by
    -- The repaired slice parametrization already transports affine combinations to fiber
    -- witnesses; this leaves only the exact rooted-volume inequality to import.
    simpa [Fx, Fy, Fxy] using
      smul_add_firstCoordinateSliceFiber_subset
        (i0 := i0) (U := U) hU_convex ha.le hb.le hab
  have hFx_bounded : Bornology.IsBounded Fx := by
    -- Read boundedness of the repaired `x`-fiber directly from the ambient bounded body.
    simpa [Fx] using
      firstCoordinateSliceFiber_bounded_of_bodyBounded
        (i0 := i0) (U := U) hU_bounded x
  have hFy_bounded : Bornology.IsBounded Fy := by
    -- The same bounded-fiber owner applies at the `y`-slice.
    simpa [Fy] using
      firstCoordinateSliceFiber_bounded_of_bodyBounded
        (i0 := i0) (U := U) hU_bounded y
  have hFx_convex : Convex ℝ Fx := by
    -- Convexity of the ambient body descends to each repaired slice fiber.
    simpa [Fx] using
      convex_firstCoordinateSliceFiber
        (i0 := i0) (U := U) hU_convex x
  have hFy_convex : Convex ℝ Fy := by
    -- The same slice-fiber convexity owner applies at `y`.
    simpa [Fy] using
      convex_firstCoordinateSliceFiber
        (i0 := i0) (U := U) hU_convex y
  have hFxy_bounded : Bornology.IsBounded Fxy := by
    -- The target fiber inherits boundedness from the ambient bounded body as well.
    simpa [Fxy] using
      firstCoordinateSliceFiber_bounded_of_bodyBounded
        (i0 := i0) (U := U) hU_bounded (a * x + b * y)
  have hRooted :
      a * (volume Fx).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) +
          b * (volume Fy).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) ≤
        (volume Fxy).toReal ^ (((n - 1 : ℕ)⁻¹ : ℝ)) := by
    -- The remaining geometric work is now exactly the packaged rooted-volume owner.
    exact
      sliceFiber_rooted_volume_brunn_minkowski_fin
        (hn := hn) ha hb hab hFx_bounded hFy_bounded hFx_convex hFy_convex hFxy_bounded
        hFiberSubset
  -- Rewrite the three repaired fiber volumes back to the slice-profile notation.
  simpa [Fx, Fy, Fxy, firstCoordinateSliceProfile] using hRooted

/-- Helper for Profile: the Brunn-Minkowski owner should show that the rooted slice profile is
concave on the canonical support interval cut out by `sInf` and `sSup`. -/
-- TODO: the bounded-fiber side condition is now isolated by
-- `firstCoordinateSliceFiber_bounded_of_bodyBounded`; the remaining blocker is the pairwise
-- Brunn-Minkowski inequality for the repaired slice fibers, which should then be packaged into
-- this interval statement without adding another support-vs-interval wrapper.
private theorem firstCoordinateSliceProfileRoot_concaveOnInterval
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U)
    (hU_bounded : Bornology.IsBounded U)
    (hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty)
    (hSupportSubset :
      firstCoordinateSliceSupport i0 U ⊆
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)))
    (hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U))
    (hOffSupportRoot :
      ∀ ⦃t : ℝ⦄, t ∉ firstCoordinateSliceSupport i0 U →
        (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0)
    (hNonnegRoot :
      ∀ ⦃t : ℝ⦄, t ∈ firstCoordinateSliceSupport i0 U →
        0 ≤ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) :
    ConcaveOn ℝ
      (Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
        (sSup (firstCoordinateSliceSupport i0 U)))
      (fun t ↦ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) := by
  let I : Set ℝ :=
    Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
      (sSup (firstCoordinateSliceSupport i0 U))
  let φ : ℝ → ℝ :=
    fun t ↦ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))
  -- Route correction: the interval packaging is no longer the geometric blocker. The only
  -- missing input is the Brunn-Minkowski pairwise inequality for the repaired slice fibers,
  -- with ambient boundedness threaded explicitly so the slice fibers have finite volume.
  have hPairwise :
      ∀ ⦃x : ℝ⦄, x ∈ I → ∀ ⦃y : ℝ⦄, y ∈ I → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
        a * φ x + b * φ y ≤ φ (a * x + b * y) := by
    intro x hx y hy a b ha hb hab
    -- Read the interval-level pairwise inequality from the dedicated Brunn-Minkowski owner.
    simpa [φ] using
      firstCoordinateSliceProfileRoot_pairwise_brunn_minkowski
        (hn := hn) (i0 := i0) (U := U) hU_convex hU_bounded
        hSupportNonempty hSupportSubset hSupportConvex hOffSupportRoot hNonnegRoot
        hx hy ha hb hab
  -- Once the pairwise Brunn-Minkowski inequality is available, `ConcaveOn` is the standard
  -- interval-level reformulation.
  refine (concaveOn_iff_forall_pos).2 ?_
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa [I, φ, smul_eq_mul] using hPairwise hx hy ha hb hab

/-- Helper for Profile: positive powered mass forces the powered density `(ψ t) ^ m` to stay
strictly positive on the interval interior. -/
private lemma powDensity_posOnInterior
    {m : ℕ} (hm : 0 < m) {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_concave : ConcaveOn ℝ (Set.Icc a b) ψ)
    (hψ_nonneg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → 0 ≤ ψ t)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m := by
  -- Reuse the already-isolated positivity owner instead of reproving the vanishing contradiction.
  exact
    intervalPow_pos_on_interior_of_concave_nonneg_of_integral_pos
      hm hψ_concave hψ_nonneg hψ_off hMassPos

/-- Helper for Profile: once `(ψ t) ^ m` is strictly positive on the interval interior, the
logarithm of that powered density is concave there as well. -/
private lemma powDensity_logConcaveOnInterior
    {m : ℕ} (hm : 0 < m) {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_concave : ConcaveOn ℝ (Set.Icc a b) ψ)
    (hψ_nonneg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → 0 ≤ ψ t)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume) :
    ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)) := by
  have hψ_concaveIoo : ConcaveOn ℝ (Set.Ioo a b) ψ := by
    -- Restrict the original closed-interval concavity to the open interval where positivity holds.
    refine hψ_concave.subset ?_ (convex_Ioo a b)
    intro t ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hpow_pos :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m :=
    powDensity_posOnInterior hm hψ_concave hψ_nonneg hψ_off hMassPos
  have hψ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ψ t := by
    intro t ht
    have hpow_ne_zero : (ψ t) ^ m ≠ 0 := (hpow_pos ht).ne'
    have hψ_ne_zero : ψ t ≠ 0 := by
      intro hψ_zero
      exact hpow_ne_zero (by simp [hψ_zero, hm.ne'])
    have ht_mem : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact lt_of_le_of_ne (hψ_nonneg ht_mem) (Ne.symm hψ_ne_zero)
  have hlogPsi : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ψ t)) := by
    refine LinearOrder.concaveOn_of_lt (convex_Ioo a b) ?_
    intro x hx y hy hxy u v hu hv huv
    have huv_mem : u • x + v • y ∈ Set.Ioo a b := by
      exact (convex_Ioo a b) hx hy hu.le hv.le huv
    have hψ_avg :
        u • ψ x + v • ψ y ≤ ψ (u • x + v • y) := by
      exact hψ_concaveIoo.2 hx hy hu.le hv.le huv
    have havg_pos : 0 < u * ψ x + v * ψ y := by
      exact add_pos (mul_pos hu (hψ_pos hx)) (mul_pos hv (hψ_pos hy))
    calc
      u • Real.log (ψ x) + v • Real.log (ψ y)
          ≤ Real.log (u * ψ x + v * ψ y) := by
              simpa [smul_eq_mul] using
                (strictConcaveOn_log_Ioi.concaveOn.2
                  (show ψ x ∈ Set.Ioi (0 : ℝ) from hψ_pos hx)
                  (show ψ y ∈ Set.Ioi (0 : ℝ) from hψ_pos hy)
                  hu.le hv.le huv)
      _ ≤ Real.log (ψ (u • x + v • y)) := by
            exact
              Real.strictMonoOn_log.monotoneOn
                (show u * ψ x + v * ψ y ∈ Set.Ioi (0 : ℝ) from havg_pos)
                (show ψ (u • x + v • y) ∈ Set.Ioi (0 : ℝ) from hψ_pos huv_mem)
                (by simpa [smul_eq_mul] using hψ_avg)
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hscaled :
      ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ (m : ℝ) • Real.log (ψ t)) :=
    hlogPsi.smul hm_nonneg
  -- Rewrite the powered logarithm once to the scalar multiple of `log ∘ ψ`.
  refine hscaled.congr ?_
  intro t ht
  simpa [smul_eq_mul] using (Real.log_pow (ψ t) m).symm

/-- Helper for Profile: off-interval vanishing and interior positivity force the powered density
to be nonnegative almost everywhere. -/
private lemma powDensity_nonnegAE_of_offIntervalZero_of_interiorPos
    {m : ℕ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m) :
    ∀ᵐ t ∂volume, 0 ≤ (ψ t) ^ m := by
  have ha_ae : ∀ᵐ t ∂volume, t ≠ a := by
    simp [ae_iff, measure_singleton]
  have hb_ae : ∀ᵐ t ∂volume, t ≠ b := by
    simp [ae_iff, measure_singleton]
  -- Away from the two endpoints, points are either in the open core where positivity is known or
  -- outside the closed support interval where the density vanishes.
  filter_upwards [ha_ae, hb_ae] with t hta htb
  by_cases htIoo : t ∈ Set.Ioo a b
  · exact le_of_lt (hPowPos htIoo)
  · have htIcc : t ∉ Set.Icc a b := by
      intro htIcc
      have ht_side : t ≤ a ∨ b ≤ t := by
        by_cases hat : a < t
        · right
          exact not_lt.mp (fun htb' ↦ htIoo ⟨hat, htb'⟩)
        · left
          exact not_lt.mp hat
      cases ht_side with
      | inl hleft =>
          exact hta (le_antisymm hleft htIcc.1)
      | inr hright =>
          exact htb (le_antisymm htIcc.2 hright)
    have hψ_zero : ψ t = 0 := hψ_off htIcc
    simp [hψ_zero]

/-- Helper for Profile: positive total mass together with vanishing outside `[a, b]` and zero
first moment forces the support interval of the powered density to straddle the origin. -/
private lemma centeredLogConcaveDensity_supportStraddlesZero
    {m : ℕ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hρ_nonnegAE : ∀ᵐ t ∂volume, 0 ≤ (ψ t) ^ m)
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0) :
    a ≤ 0 ∧ 0 ≤ b := by
  let I : Set ℝ := Set.Icc a b
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  have hm_ne : m ≠ 0 := by
    intro hm
    subst hm
    have hVolumeZero : volume.real (Set.univ : Set ℝ) = 0 := by
      change ENNReal.toReal (volume (Set.univ : Set ℝ)) = 0
      simp
    have hMassPosZero : 0 < volume.real (Set.univ : Set ℝ) := by
      simpa using hMassPos
    have hNotPos : ¬ 0 < volume.real (Set.univ : Set ℝ) := by
      simpa [hVolumeZero]
    exact hNotPos hMassPosZero
  have hMassPosρ : 0 < ∫ t, ρ t ∂volume := by
    simpa [ρ] using hMassPos
  have hMomentZeroρ : ∫ t, t * ρ t ∂volume = 0 := by
    simpa [ρ] using hMomentZero
  have hρ_integrable : Integrable ρ volume := by
    by_contra hρ_int
    have hMassZero : ∫ t, ρ t ∂volume = 0 := by
      simp [ρ, integral_undef hρ_int]
    linarith
  have hρ_integrableOn : IntegrableOn ρ I volume := hρ_integrable.integrableOn
  have hMomentIntegrableOn : IntegrableOn (fun t ↦ t * ρ t) I volume := by
    -- The bounded support interval lets us multiply the integrable density by the continuous
    -- coordinate function without introducing a new integrability blocker.
    simpa [I, ρ] using
      IntegrableOn.continuousOn_mul
        (g := fun t : ℝ ↦ t) (g' := ρ) (K := I) continuousOn_id hρ_integrableOn
        (isCompact_Icc : IsCompact (Set.Icc a b))
  have hMassEq :
      ∫ t in I, ρ t ∂volume = ∫ t, ρ t ∂volume := by
    -- Off the interval, the powered density vanishes identically.
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro t ht
    have hψ_zero : ψ t = 0 := hψ_off (by simpa [I] using ht)
    simp [ρ, hψ_zero, hm_ne]
  have hMomentEq :
      ∫ t in I, t * ρ t ∂volume = ∫ t, t * ρ t ∂volume := by
    -- The weighted density also vanishes off the interval because the density factor is zero.
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro t ht
    have hψ_zero : ψ t = 0 := hψ_off (by simpa [I] using ht)
    simp [ρ, hψ_zero, hm_ne]
  have hMassPosOn : 0 < ∫ t in I, ρ t ∂volume := by
    rw [hMassEq]
    exact hMassPosρ
  constructor
  · by_contra ha_pos
    have ha_pos' : 0 < a := lt_of_not_ge ha_pos
    have hScaledIntegrable : IntegrableOn (fun t ↦ a * ρ t) I volume :=
      hρ_integrableOn.const_mul a
    have hLower :
        ∫ t in I, a * ρ t ∂volume ≤ ∫ t in I, t * ρ t ∂volume := by
      -- On `[a, b]`, the coordinate lower bound `a ≤ t` upgrades to an integral lower bound
      -- once the density is known to be nonnegative almost everywhere.
      refine
        setIntegral_mono_on_ae hScaledIntegrable hMomentIntegrableOn measurableSet_Icc ?_
      filter_upwards [hρ_nonnegAE] with t hρ ht
      exact mul_le_mul_of_nonneg_right ht.1 hρ
    have hLeftPos : 0 < ∫ t in I, a * ρ t ∂volume := by
      rw [integral_const_mul]
      exact mul_pos ha_pos' hMassPosOn
    have hMomentPos : 0 < ∫ t, t * ρ t ∂volume := by
      rw [← hMomentEq]
      exact lt_of_lt_of_le hLeftPos hLower
    linarith [hMomentZeroρ]
  · by_contra hb_neg
    have hb_neg' : b < 0 := lt_of_not_ge hb_neg
    have hScaledIntegrable : IntegrableOn (fun t ↦ b * ρ t) I volume :=
      hρ_integrableOn.const_mul b
    have hUpper :
        ∫ t in I, t * ρ t ∂volume ≤ ∫ t in I, b * ρ t ∂volume := by
      -- The upper interval bound `t ≤ b` gives the matching integral upper bound.
      refine
        setIntegral_mono_on_ae hMomentIntegrableOn hScaledIntegrable measurableSet_Icc ?_
      filter_upwards [hρ_nonnegAE] with t hρ ht
      exact mul_le_mul_of_nonneg_right ht.2 hρ
    have hRightNeg : ∫ t in I, b * ρ t ∂volume < 0 := by
      rw [integral_const_mul]
      exact mul_neg_of_neg_of_pos hb_neg' hMassPosOn
    have hMomentNeg : ∫ t, t * ρ t ∂volume < 0 := by
      rw [← hMomentEq]
      exact lt_of_le_of_lt hUpper hRightNeg
    linarith [hMomentZeroρ]

/-- Helper for Profile: once a real density vanishes outside a compact interval and has positive
total mass, its first moment is integrable. -/
private lemma centeredLogConcaveDensity_momentIntegrable_ofOffSupport
    {a b : ℝ} {ρ : ℝ → ℝ}
    (hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0)
    (hMassPos : 0 < ∫ t, ρ t ∂volume) :
    Integrable (fun t ↦ t * ρ t) volume := by
  have hρ_integrable : Integrable ρ volume := by
    by_contra hρ_int
    have hMassZero : ∫ t, ρ t ∂volume = 0 := by
      simp [integral_undef hρ_int]
    linarith
  have hMomentIntegrableOn : IntegrableOn (fun t ↦ t * ρ t) (Set.Icc a b) volume := by
    -- On the compact support interval, multiplying by the continuous coordinate preserves
    -- integrability.
    simpa using
      IntegrableOn.continuousOn_mul
        (g := fun t : ℝ ↦ t) (g' := ρ) (K := Set.Icc a b) continuousOn_id
        hρ_integrable.integrableOn (isCompact_Icc : IsCompact (Set.Icc a b))
  have hIndicator :
      (fun t ↦ t * ρ t) = Set.indicator (Set.Icc a b) (fun t ↦ t * ρ t) := by
    -- Outside the support interval, the weighted density vanishes because the density factor does.
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp [Set.indicator, ht]
    · have hρ_zero : ρ t = 0 := hρ_off ht
      simp [Set.indicator, ht, hρ_zero]
  rw [hIndicator]
  exact hMomentIntegrableOn.integrable_indicator measurableSet_Icc

/-- Helper for Profile: split an integrable real function into its nonpositive and positive
half-line integrals. -/
private lemma integral_eq_integral_Iic_add_integral_Ioi
    {f : ℝ → ℝ} (hf : Integrable f volume) :
    ∫ t, f t ∂volume = ∫ t in Set.Iic 0, f t ∂volume + ∫ t in Set.Ioi 0, f t ∂volume := by
  -- The two half-lines partition `ℝ` into a measurable set and its complement.
  simpa [Set.compl_Iic] using (integral_add_compl (s := Set.Iic 0) measurableSet_Iic hf).symm

/-- Helper for Profile: the exponential envelope `exp (-(r * t))` has total mass `1 / r` on
`(0, ∞)`. -/
private lemma integral_exp_neg_mul_Ioi_zero
    {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-(r * t)) = 1 / r := by
  -- Rewrite to the standard improper integral formula for `exp (a * t)` with `a = -r`.
  simpa [div_eq_mul_inv] using
    (integral_exp_mul_Ioi (a := -r) (by linarith) 0)

/-- Helper for Profile: the first moment of the positive half-line exponential envelope is
`(1 / r)^2`. -/
private lemma integral_mul_exp_neg_mul_Ioi_zero
    {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t)) = (1 / r) ^ (2 : ℝ) := by
  have hGamma :
      ∫ t : ℝ in Set.Ioi 0, t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)) =
        (1 / r) ^ (2 : ℝ) * Real.Gamma 2 :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  calc
    ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t))
        = ∫ t : ℝ in Set.Ioi 0, t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)) := by
            -- On `(0, ∞)`, the linear factor is exactly the `rpow` with exponent `1`.
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t ht
            simp [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one]
    _ = (1 / r) ^ (2 : ℝ) * Real.Gamma 2 := hGamma
    _ = (1 / r) ^ (2 : ℝ) := by simp [Real.Gamma_two]

/-- Helper for Profile: after flipping the variable `t ↦ -t`, the negative half-line exponential
envelope has the same total mass `1 / r`. -/
private lemma integral_exp_mul_Iic_zero
    {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Iic 0, Real.exp (r * t) = 1 / r := by
  have hFlip :
      ∫ t : ℝ in Set.Ioi 0, Real.exp (r * (-t)) =
        ∫ t : ℝ in Set.Iic 0, Real.exp (r * t) :=
    by simpa using (integral_comp_neg_Ioi 0 (fun t : ℝ ↦ Real.exp (r * t)))
  -- The flipped integral is the same positive half-line exponential integral as above.
  calc
    ∫ t : ℝ in Set.Iic 0, Real.exp (r * t)
        = ∫ t : ℝ in Set.Ioi 0, Real.exp (r * (-t)) := by
            simpa using hFlip.symm
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-(r * t)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t _ht
          simp [neg_mul, mul_comm]
    _ = 1 / r := integral_exp_neg_mul_Ioi_zero hr

/-- Helper for Profile: after flipping the variable `t ↦ -t`, the negative half-line exponential
envelope has first moment `(1 / r)^2`. -/
private lemma integral_neg_mul_exp_mul_Iic_zero
    {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Iic 0, (-t) * Real.exp (r * t) = (1 / r) ^ (2 : ℝ) := by
  have hFlip :
      ∫ t : ℝ in Set.Ioi 0, ((-(-t)) * Real.exp (r * (-t))) =
        ∫ t : ℝ in Set.Iic 0, (-t) * Real.exp (r * t) :=
    by simpa using (integral_comp_neg_Ioi 0 (fun t : ℝ ↦ (-t) * Real.exp (r * t)))
  -- The flipped first moment is exactly the positive half-line exponential first moment.
  calc
    ∫ t : ℝ in Set.Iic 0, (-t) * Real.exp (r * t)
        = ∫ t : ℝ in Set.Ioi 0, ((-(-t)) * Real.exp (r * (-t))) := by
            simpa using hFlip.symm
    _ = ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t _ht
          simp [neg_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = (1 / r) ^ (2 : ℝ) := integral_mul_exp_neg_mul_Ioi_zero hr

/-- Helper for Profile: a zero first moment means the left and right first moments agree after
sign-normalizing the left side. -/
private lemma integral_neg_left_eq_right_of_integral_zero
    {ρ : ℝ → ℝ}
    (hMomentIntegrable : Integrable (fun t ↦ t * ρ t) volume)
    (hMomentZero : ∫ t, t * ρ t ∂volume = 0) :
    ∫ t in Set.Iic 0, (-t) * ρ t ∂volume = ∫ t in Set.Ioi 0, t * ρ t ∂volume := by
  have hSplit :
      ∫ t, t * ρ t ∂volume =
        ∫ t in Set.Iic 0, t * ρ t ∂volume + ∫ t in Set.Ioi 0, t * ρ t ∂volume := by
    -- Split the global first moment at the origin before rewriting the left piece.
    simpa using
      (integral_eq_integral_Iic_add_integral_Ioi
        (f := fun t ↦ t * ρ t) hMomentIntegrable)
  have hLeft :
      ∫ t in Set.Iic 0, t * ρ t ∂volume =
        - ∫ t in Set.Iic 0, (-t) * ρ t ∂volume := by
    -- On `(-∞, 0]`, the signed first moment is the negative of the absolute first moment.
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t _ht
    ring
  rw [hMomentZero, hLeft] at hSplit
  linarith

/-- Helper for Profile: a powered density with concave logarithm has strictly positive mass on every
closed subinterval of the open support core. -/
private lemma powDensity_integral_pos_on_subinterval
    {m : ℕ} {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c < d)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m) :
    0 < ∫ t in Set.Icc c d, (ψ t) ^ m ∂volume := by
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  let f : ℝ → ℝ := fun t ↦ Real.log (ρ t)
  have hlog_cont : ContinuousOn f (Set.Ioo a b) := by
    -- Concavity on the open interval makes the logarithm continuous there.
    simpa [f, ρ] using hLogConcave.continuousOn isOpen_Ioo
  have hρ_cont_open : ContinuousOn ρ (Set.Ioo a b) := by
    have hMaps : Set.MapsTo f (Set.Ioo a b) (Set.range f) := by
      intro x hx
      exact ⟨x, rfl⟩
    have hcomp : ContinuousOn (fun t ↦ Real.exp (f t)) (Set.Ioo a b) :=
      Real.continuous_exp.continuousOn.comp hlog_cont hMaps
    -- Rewrite `exp (log ρ)` back to `ρ` using interior positivity.
    refine hcomp.congr ?_
    intro t ht
    dsimp [f, ρ]
    rw [Real.exp_log (hPowPos ht)]
  have hρ_cont_closed : ContinuousOn ρ (Set.Icc c d) := by
    -- Restrict the interior continuity to the compact subinterval.
    exact hρ_cont_open.mono fun x hx => ⟨lt_of_lt_of_le hc.1 hx.1, lt_of_le_of_lt hx.2 hd.2⟩
  have hρ_integrable : IntegrableOn ρ (Set.Icc c d) volume :=
    hρ_cont_closed.integrableOn_compact isCompact_Icc
  have hρ_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc c d)] ρ := by
    -- The density is strictly positive on the whole subinterval because it lies inside the open
    -- support core.
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact le_of_lt (hPowPos ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩)
  have hSupportPos : 0 < volume (Function.support ρ ∩ Set.Icc c d) := by
    have hEq : Function.support ρ ∩ Set.Icc c d = Set.Icc c d := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro ht
        refine ⟨?_, ht⟩
        simp [Function.mem_support, ρ,
          (hPowPos ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩).ne']
    -- The support on the subinterval is the whole interval, which has positive Lebesgue measure.
    rw [hEq, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)
  exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hρ_nonneg hρ_integrable).2 hSupportPos

/-- Helper for Profile: on any compact subinterval strictly inside the support core, a powered
log-concave density attains a maximum. -/
private lemma powDensity_exists_maximizer_on_subinterval
    {m : ℕ} {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c ≤ d)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m) :
    ∃ x ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, (ψ t) ^ m ≤ (ψ x) ^ m := by
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  let J : Set ℝ := Set.Icc c d
  have hlog_cont_open :
      ContinuousOn (fun t ↦ Real.log (ρ t)) (Set.Ioo a b) := by
    -- Concavity gives continuity of the logarithmic profile on the open support core.
    simpa [ρ] using hLogConcave.continuousOn isOpen_Ioo
  have hρ_cont_open : ContinuousOn ρ (Set.Ioo a b) := by
    have hMaps :
        Set.MapsTo (fun t ↦ Real.log (ρ t)) (Set.Ioo a b) Set.univ := by
      intro t ht
      simp
    have hExpCont :
        ContinuousOn (fun t ↦ Real.exp (Real.log (ρ t))) (Set.Ioo a b) := by
      exact Real.continuous_exp.continuousOn.comp hlog_cont_open hMaps
    -- Rewrite `exp (log ρ)` back to `ρ` using strict positivity on the open support core.
    refine hExpCont.congr ?_
    intro t ht
    dsimp [ρ]
    rw [Real.exp_log (hPowPos ht)]
  have hJ_subset : J ⊆ Set.Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩
  have hρ_cont_J : ContinuousOn ρ J := hρ_cont_open.mono hJ_subset
  obtain ⟨x, hxJ, _hSup, hmax⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge
      (s := J) (ne_s := Set.nonempty_Icc.2 hcd) (f := ρ) hρ_cont_J
  refine ⟨x, hxJ, ?_⟩
  intro t ht
  exact hmax t ht

/-- Helper for Profile: if a powered density vanishes away from a single point, then its total mass
is zero because the remaining support has Lebesgue measure zero. -/
private lemma powDensity_integral_eq_zero_of_off_singleton
    {m : ℕ} (hm : m ≠ 0) {c : ℝ} {ψ : ℝ → ℝ}
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ ({c} : Set ℝ) → ψ t = 0) :
    ∫ t, (ψ t) ^ m ∂volume = 0 := by
  have hMassEq :
      ∫ t, (ψ t) ^ m ∂volume = ∫ t in ({c} : Set ℝ), (ψ t) ^ m ∂volume := by
    -- Outside the singleton, the powered density vanishes identically.
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro t ht
    have hψ_zero : ψ t = 0 := hψ_off ht
    simp [hψ_zero, hm]
  rw [hMassEq]
  simpa using
    (MeasureTheory.integral_zero_measure
      (f := fun t : ℝ ↦ (ψ t) ^ m) (μ := volume.restrict ({c} : Set ℝ)))

/-- Helper for Profile: a centered positive log-concave density must have support strictly on both
sides of the origin, not merely touch it. -/
private lemma centeredLogConcaveDensity_zero_mem_interior_support
    {m : ℕ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0) :
    a < 0 ∧ 0 < b := by
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  have hm_ne : m ≠ 0 := by
    intro hm
    subst hm
    have hVolumeZero : volume.real (Set.univ : Set ℝ) = 0 := by
      change ENNReal.toReal (volume (Set.univ : Set ℝ)) = 0
      simp
    have hMassPosZero : 0 < volume.real (Set.univ : Set ℝ) := by
      simpa using hMassPos
    have hNotPos : ¬ 0 < volume.real (Set.univ : Set ℝ) := by
      simpa [hVolumeZero]
    exact hNotPos hMassPosZero
  have hρ_nonnegAE : ∀ᵐ t ∂volume, 0 ≤ ρ t := by
    -- Interior positivity and off-support vanishing reduce nonnegativity to the null endpoint set.
    simpa [ρ] using
      powDensity_nonnegAE_of_offIntervalZero_of_interiorPos
        (m := m) (a := a) (b := b) (ψ := ψ) hψ_off hPowPos
  have ⟨ha_nonpos, hb_nonneg⟩ :=
    centeredLogConcaveDensity_supportStraddlesZero
      (m := m) (a := a) (b := b) (ψ := ψ) hψ_off hρ_nonnegAE hMassPos hMomentZero
  have hρ_integrable : Integrable ρ volume := by
    by_contra hρ_int
    have hMassZero : ∫ t, ρ t ∂volume = 0 := by
      simp [ρ, integral_undef hρ_int]
    linarith
  have hMomentIntegrableOn : IntegrableOn (fun t ↦ t * ρ t) (Set.Icc a b) volume := by
    -- The bounded support interval lets the coordinate factor preserve integrability.
    simpa [ρ] using
      IntegrableOn.continuousOn_mul
        (g := fun t : ℝ ↦ t) (g' := ρ) (K := Set.Icc a b) continuousOn_id
        hρ_integrable.integrableOn (isCompact_Icc : IsCompact (Set.Icc a b))
  have hMomentIntegrable : Integrable (fun t ↦ t * ρ t) volume := by
    have hIndicator :
        (fun t ↦ t * ρ t) = Set.indicator (Set.Icc a b) (fun t ↦ t * ρ t) := by
      -- Outside `[a, b]`, the density factor vanishes, so the weighted density is supported on
      -- the closed interval as well.
      funext t
      by_cases ht : t ∈ Set.Icc a b
      · simp [Set.indicator, ht]
      · have hψ_zero : ψ t = 0 := hψ_off ht
        simp [Set.indicator, ht, ρ, hψ_zero, hm_ne]
    rw [hIndicator]
    exact hMomentIntegrableOn.integrable_indicator measurableSet_Icc
  have hMomentZeroρ : ∫ t, t * ρ t ∂volume = 0 := by
    simpa [ρ] using hMomentZero
  constructor
  · by_contra h_not_left
    have ha_zero : a = 0 := le_antisymm ha_nonpos (not_lt.mp h_not_left)
    subst ha_zero
    by_cases hb_zero : b = 0
    · subst hb_zero
      have hMassZero :
          ∫ t, (ψ t) ^ m ∂volume = 0 :=
        powDensity_integral_eq_zero_of_off_singleton
          (m := m) hm_ne (c := 0) (ψ := ψ) (by
            intro t ht
            exact hψ_off (by simpa using ht))
      linarith
    · have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb_zero)
      let c : ℝ := b / 4
      let d : ℝ := b / 2
      have hc : c ∈ Set.Ioo 0 b := by
        -- Choose a compact subinterval strictly inside the positive side of the support.
        dsimp [c]
        constructor <;> linarith
      have hd : d ∈ Set.Ioo 0 b := by
        dsimp [d]
        constructor <;> linarith
      have hcd : c < d := by
        dsimp [c, d]
        linarith
      have hSubMassPos : 0 < ∫ t in Set.Icc c d, ρ t ∂volume := by
        -- The positive-side interior subinterval has strictly positive mass.
        simpa [ρ] using
          powDensity_integral_pos_on_subinterval
            (m := m) (a := 0) (b := b) (c := c) (d := d)
            (ψ := ψ) hLogConcave hc hd hcd hPowPos
      have hc_pos : 0 < c := hc.1
      have hIndicatorPos :
          0 < ∫ t, Set.indicator (Set.Icc c d) (fun t ↦ c * ρ t) t ∂volume := by
        -- The indicator lower bound keeps a fixed positive fraction of the subinterval mass.
        rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_const_mul]
        exact mul_pos hc_pos hSubMassPos
      have hIndicatorIntegrable :
          Integrable (Set.indicator (Set.Icc c d) (fun t ↦ c * ρ t)) volume := by
        exact (hρ_integrable.const_mul c).indicator measurableSet_Icc
      have hIndicatorLe :
          Set.indicator (Set.Icc c d) (fun t ↦ c * ρ t) ≤ᵐ[volume] fun t ↦ t * ρ t := by
        -- On the chosen subinterval, `c ≤ t`; outside it, the indicator vanishes, and the
        -- weighted density is still nonnegative on `[0, b]` and zero off that support interval.
        filter_upwards [hρ_nonnegAE] with t hρ
        by_cases htJ : t ∈ Set.Icc c d
        · simp [Set.indicator_of_mem, htJ]
          exact mul_le_mul_of_nonneg_right htJ.1 hρ
        · by_cases htI : t ∈ Set.Icc 0 b
          · have ht_nonneg : 0 ≤ t := htI.1
            have hrhs_nonneg : 0 ≤ t * ρ t := mul_nonneg ht_nonneg hρ
            simp [Set.indicator, htJ, hrhs_nonneg]
          · have hψ_zero : ψ t = 0 := hψ_off htI
            simp [Set.indicator, htJ, ρ, hψ_zero, hm_ne]
      have hMomentPosρ : 0 < ∫ t, t * ρ t ∂volume := by
        exact lt_of_lt_of_le hIndicatorPos <|
          integral_mono_ae hIndicatorIntegrable hMomentIntegrable hIndicatorLe
      linarith [hMomentZeroρ]
  · by_contra h_not_right
    have hb_zero : b = 0 := le_antisymm (not_lt.mp h_not_right) hb_nonneg
    subst hb_zero
    by_cases ha_zero : a = 0
    · subst ha_zero
      have hMassZero :
          ∫ t, (ψ t) ^ m ∂volume = 0 :=
        powDensity_integral_eq_zero_of_off_singleton
          (m := m) hm_ne (c := 0) (ψ := ψ) (by
            intro t ht
            exact hψ_off (by simpa using ht))
      linarith
    · have ha_neg : a < 0 := lt_of_le_of_ne ha_nonpos ha_zero
      let c : ℝ := a / 2
      let d : ℝ := a / 4
      have hc : c ∈ Set.Ioo a 0 := by
        -- Choose a compact subinterval strictly inside the negative side of the support.
        dsimp [c]
        constructor <;> linarith
      have hd : d ∈ Set.Ioo a 0 := by
        dsimp [d]
        constructor <;> linarith
      have hcd : c < d := by
        dsimp [c, d]
        linarith
      have hSubMassPos : 0 < ∫ t in Set.Icc c d, ρ t ∂volume := by
        -- The negative-side interior subinterval also has strictly positive mass.
        simpa [ρ] using
          powDensity_integral_pos_on_subinterval
            (m := m) (a := a) (b := 0) (c := c) (d := d)
            (ψ := ψ) hLogConcave hc hd hcd hPowPos
      have hd_neg : d < 0 := hd.2
      have hIndicatorPos :
          0 < ∫ t, Set.indicator (Set.Icc c d) (fun t ↦ (-d) * ρ t) t ∂volume := by
        -- The negative-side interval contributes a fixed positive amount to `(-t) * ρ t`.
        rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_const_mul]
        exact mul_pos (by linarith) hSubMassPos
      have hIndicatorIntegrable :
          Integrable (Set.indicator (Set.Icc c d) (fun t ↦ (-d) * ρ t)) volume := by
        exact (hρ_integrable.const_mul (-d)).indicator measurableSet_Icc
      have hNegMomentIntegrable : Integrable (fun t ↦ (-t) * ρ t) volume := by
        -- Rewrite `(-t) * ρ t` as the negation of `t * ρ t`.
        simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          hMomentIntegrable.neg
      have hIndicatorLe :
          Set.indicator (Set.Icc c d) (fun t ↦ (-d) * ρ t) ≤ᵐ[volume] fun t ↦ (-t) * ρ t := by
        -- On the chosen negative interval, `t ≤ d`, hence `-d ≤ -t`; outside it, the indicator
        -- vanishes, and the sign-normalized moment is still nonnegative on `[a, 0]`.
        filter_upwards [hρ_nonnegAE] with t hρ
        by_cases htJ : t ∈ Set.Icc c d
        · have hdt : -d ≤ -t := by linarith [htJ.2]
          have hmain : (-d) * ρ t ≤ (-t) * ρ t := mul_le_mul_of_nonneg_right hdt hρ
          simpa [Set.indicator, htJ] using hmain
        · by_cases htI : t ∈ Set.Icc a 0
          · have ht_nonneg : 0 ≤ -t := by linarith [htI.2]
            have hrhs_nonneg : 0 ≤ (-t) * ρ t := mul_nonneg ht_nonneg hρ
            simp [Set.indicator, htJ]
            nlinarith
          · have hψ_zero : ψ t = 0 := hψ_off htI
            simp [Set.indicator, htJ, ρ, hψ_zero, hm_ne]
      have hNegMomentZero :
          ∫ t, (-t) * ρ t ∂volume = 0 := by
        calc
          ∫ t, (-t) * ρ t ∂volume = ∫ t, -(t * ρ t) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with t
              ring
          _ = -∫ t, t * ρ t ∂volume := by
              simpa using (integral_neg (f := fun t : ℝ ↦ t * ρ t))
          _ = 0 := by simp [hMomentZeroρ]
      have hNegMomentPos : 0 < ∫ t, (-t) * ρ t ∂volume := by
        exact lt_of_lt_of_le hIndicatorPos <|
          integral_mono_ae hIndicatorIntegrable hNegMomentIntegrable hIndicatorLe
      linarith [hNegMomentZero]

-- Helper for Profile: the remaining analytic blocker is the one-dimensional tail estimate for a
-- log-concave density on the canonical support interval.
-- Route correction: a two-sided supporting-exponential argument based at `0` is false in general
-- for centered log-concave densities; for example, `ρ(t) = exp t` on `(-∞, 1]` has mean `0` but
-- is still increasing at `0`. The remaining analytic owner therefore has to be a mode-based 1D
-- log-concave inequality, or an equivalent existing theorem, rather than the discarded `0`-based
-- secant route.
/-- Helper for Profile: a positive density and its logarithm have the same compact maximizers on
subintervals strictly inside the support core. -/
private lemma compact_mode_transfers_to_log
    {a b c d : ℝ} {ρ : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hCompactMode : ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, ρ t ≤ ρ x0) :
    ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, Real.log (ρ t) ≤ Real.log (ρ x0) := by
  rcases hCompactMode with ⟨x0, hx0, hmax⟩
  refine ⟨x0, hx0, ?_⟩
  intro t ht
  have ht_core : t ∈ Set.Ioo a b := by
    -- Any point of the compact subinterval stays strictly inside the support core.
    exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩
  have hx0_core : x0 ∈ Set.Ioo a b := by
    -- The maximizer itself also lies in the same strict support core.
    exact ⟨lt_of_lt_of_le hc.1 hx0.1, lt_of_le_of_lt hx0.2 hd.2⟩
  -- On positive reals, `log` is monotone, so the order of the compact maximizers is unchanged.
  exact
    Real.strictMonoOn_log.monotoneOn
      (show ρ t ∈ Set.Ioi (0 : ℝ) from hρ_pos ht_core)
      (show ρ x0 ∈ Set.Ioi (0 : ℝ) from hρ_pos hx0_core)
      (hmax t ht)

/-- Helper for Profile: on the left of a compact maximizer, every secant slope of the logarithmic
profile is nonnegative. -/
private lemma compact_maximizer_left_slope_nonneg
    {c d x0 : ℝ} {f : ℝ → ℝ}
    (hx0 : x0 ∈ Set.Icc c d)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f x0) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope f t x0 := by
  intro t ht
  have ht_cd : t ∈ Set.Icc c d := ⟨ht.1, le_trans ht.2 hx0.2⟩
  have hNotNeg : ¬ slope f t x0 < 0 := by
    intro hslope
    have hfx : f x0 < f t := (slope_neg_iff_of_le ht.2).1 hslope
    exact not_lt_of_ge (hmax t ht_cd) hfx
  -- A strict left maximizer can only force nonnegative left secant slopes.
  exact le_of_not_gt hNotNeg

/-- Helper for Profile: on the right of a compact maximizer, every secant slope of the logarithmic
profile is nonpositive. -/
private lemma compact_maximizer_right_slope_nonpos
    {c d x0 : ℝ} {f : ℝ → ℝ}
    (hx0 : x0 ∈ Set.Icc c d)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f x0) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope f x0 t ≤ 0 := by
  intro t ht
  have ht_cd : t ∈ Set.Icc c d := ⟨le_trans hx0.1 ht.1, ht.2⟩
  have hNotPos : ¬ 0 < slope f x0 t := by
    intro hslope
    have hfx : f x0 < f t := (slope_pos_iff_of_le ht.1).1 hslope
    exact not_lt_of_ge (hmax t ht_cd) hfx
  -- Dually, a compact maximizer forces every right secant slope to be nonpositive.
  exact le_of_not_gt hNotPos

/-- Helper for Profile: once a compact logarithmic maximizer sits strictly inside the compact
subinterval, slope monotonicity upgrades it to a global mode on the whole support core. -/
private lemma compact_log_mode_global_of_strict_interior
    {a b c d x0 : ℝ} {f : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b)
    (hx0 : x0 ∈ Set.Icc c d) (hx0_left : c < x0) (hx0_right : x0 < d)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    (hLeftSlope : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope f t x0)
    (hRightSlope : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope f x0 t ≤ 0) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → f t ≤ f x0 := by
  intro t ht
  have hx0_core : x0 ∈ Set.Ioo a b := by
    -- The compact maximizer itself lies strictly inside the support core.
    exact ⟨lt_of_lt_of_le hc.1 hx0.1, lt_of_le_of_lt hx0.2 hd.2⟩
  by_cases htx0 : t ≤ x0
  · by_cases hct : c ≤ t
    · have ht_cx0 : t ∈ Set.Icc c x0 := ⟨hct, htx0⟩
      -- Inside the compact interval, the stored left-slope sign already gives the mode inequality.
      exact (slope_nonneg_iff_of_le htx0).1 (hLeftSlope ht_cx0)
    · have htc : t < c := lt_of_not_ge hct
      have hc_dom : c ∈ {y ∈ Set.Ioo a b | y < x0} := ⟨hc, hx0_left⟩
      have ht_dom : t ∈ {y ∈ Set.Ioo a b | y < x0} := ⟨ht, lt_of_lt_of_le htc hx0.1⟩
      have hSlope_c_nonneg : 0 ≤ slope f x0 c := by
        -- The compact left-slope sign at the left endpoint is the comparison anchor.
        simpa [slope_comm] using hLeftSlope (show c ∈ Set.Icc c x0 from ⟨le_rfl, hx0_left.le⟩)
      have hSlope_cmp : slope f x0 c ≤ slope f x0 t := by
        -- Concavity pushes all farther-left secant slopes above the endpoint slope.
        exact hLogConcave.antitoneOn_slope_lt hx0_core ht_dom hc_dom htc.le
      have hSlope_t_nonneg : 0 ≤ slope f t x0 := by
        -- Convert the slope comparison back to the left-to-right orientation.
        simpa [slope_comm] using le_trans hSlope_c_nonneg hSlope_cmp
      exact (slope_nonneg_iff_of_le htx0).1 hSlope_t_nonneg
  · have hx0t : x0 < t := lt_of_not_ge htx0
    by_cases htd : t ≤ d
    · have ht_x0d : t ∈ Set.Icc x0 d := ⟨hx0t.le, htd⟩
      -- Inside the compact interval, the stored right-slope sign gives the mode inequality.
      exact (slope_nonpos_iff_of_le hx0t.le).1 (hRightSlope ht_x0d)
    · have hdt : d < t := lt_of_not_ge htd
      have hd_dom : d ∈ {y ∈ Set.Ioo a b | x0 < y} := ⟨hd, hx0_right⟩
      have ht_dom : t ∈ {y ∈ Set.Ioo a b | x0 < y} := ⟨ht, hx0t⟩
      have hSlope_d_nonpos : slope f x0 d ≤ 0 := by
        -- The compact right-slope sign at the right endpoint is the comparison anchor.
        exact hRightSlope (show d ∈ Set.Icc x0 d from ⟨hx0_right.le, le_rfl⟩)
      have hSlope_cmp : slope f x0 t ≤ slope f x0 d := by
        -- Concavity pushes all farther-right secant slopes below the endpoint slope.
        exact hLogConcave.antitoneOn_slope_gt hx0_core hd_dom ht_dom hdt.le
      have hSlope_t_nonpos : slope f x0 t ≤ 0 := le_trans hSlope_cmp hSlope_d_nonpos
      exact (slope_nonpos_iff_of_le hx0t.le).1 hSlope_t_nonpos

/-- Helper for Profile: if a concave function is maximized at the left endpoint of a strict
compact interval and the two endpoint values agree, then the function is flat on that interval. -/
private lemma concave_eq_of_left_endpoint_maximizer
    {c d : ℝ} {f : ℝ → ℝ}
    (hcd : c < d) (hConcave : ConcaveOn ℝ (Set.Icc c d) f)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f c) (hendpoints : f d = f c) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c d → f t = f c := by
  intro t ht
  have hUpper : f t ≤ f c := hmax t ht
  have hLower : f c ≤ f t := by
    let α : ℝ := (d - t) / (d - c)
    let β : ℝ := (t - c) / (d - c)
    have hdc_pos : 0 < d - c := sub_pos.mpr hcd
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (sub_nonneg.mpr ht.2) hdc_pos.le
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      exact div_nonneg (sub_nonneg.mpr ht.1) hdc_pos.le
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      field_simp [hdc_pos.ne']
      ring
    have ht_combo : α * c + β * d = t := by
      dsimp [α, β]
      field_simp [hdc_pos.ne']
      ring_nf
    have hconc :
        α * f c + β * f d ≤ f t := by
      simpa [smul_eq_mul, ht_combo] using
        hConcave.2
          (show c ∈ Set.Icc c d from ⟨le_rfl, hcd.le⟩)
          (show d ∈ Set.Icc c d from ⟨hcd.le, le_rfl⟩)
          hα_nonneg hβ_nonneg hαβ
    rw [hendpoints] at hconc
    calc
      f c = (α + β) * f c := by rw [hαβ, one_mul]
      _ = α * f c + β * f c := by ring
      _ ≤ f t := hconc
  exact le_antisymm hUpper hLower

/-- Helper for Profile: the symmetric endpoint-equality case is also flat when the compact
maximizer sits at the right endpoint. -/
private lemma concave_eq_of_right_endpoint_maximizer
    {c d : ℝ} {f : ℝ → ℝ}
    (hcd : c < d) (hConcave : ConcaveOn ℝ (Set.Icc c d) f)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f d) (hendpoints : f c = f d) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c d → f t = f d := by
  intro t ht
  have hUpper : f t ≤ f d := hmax t ht
  have hLower : f d ≤ f t := by
    let α : ℝ := (d - t) / (d - c)
    let β : ℝ := (t - c) / (d - c)
    have hdc_pos : 0 < d - c := sub_pos.mpr hcd
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (sub_nonneg.mpr ht.2) hdc_pos.le
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      exact div_nonneg (sub_nonneg.mpr ht.1) hdc_pos.le
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      field_simp [hdc_pos.ne']
      ring
    have ht_combo : α * c + β * d = t := by
      dsimp [α, β]
      field_simp [hdc_pos.ne']
      ring_nf
    have hconc :
        α * f c + β * f d ≤ f t := by
      simpa [smul_eq_mul, ht_combo] using
        hConcave.2
          (show c ∈ Set.Icc c d from ⟨le_rfl, hcd.le⟩)
          (show d ∈ Set.Icc c d from ⟨hcd.le, le_rfl⟩)
          hα_nonneg hβ_nonneg hαβ
    rw [hendpoints] at hconc
    calc
      f d = (α + β) * f d := by rw [hαβ, one_mul]
      _ = α * f d + β * f d := by ring
      _ ≤ f t := hconc
  exact le_antisymm hUpper hLower

/-- Helper for Profile: if the compact logarithmic maximizer sits at the left endpoint and the
two endpoint values agree, then the plateau midpoint is a strict interior global mode. -/
private lemma compact_log_mode_global_of_left_endpoint_plateau
    {a b c d : ℝ} {f : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c < d)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f c) (hendpoints : f d = f c) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → f t ≤ f ((c + d) / 2) := by
  let xMid : ℝ := (c + d) / 2
  have hConcaveIcc : ConcaveOn ℝ (Set.Icc c d) f := by
    -- Restrict the open-core concavity to the compact plateau interval.
    refine hLogConcave.subset ?_ (convex_Icc _ _)
    intro t ht
    exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩
  have hPlateau : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c d → f t = f c :=
    concave_eq_of_left_endpoint_maximizer hcd hConcaveIcc hmax hendpoints
  have hxMid : xMid ∈ Set.Icc c d := by
    -- The plateau midpoint lies strictly inside the compact interval.
    dsimp [xMid]
    constructor <;> linarith
  have hxMid_left : c < xMid := by
    dsimp [xMid]
    linarith
  have hxMid_right : xMid < d := by
    dsimp [xMid]
    linarith
  have hmaxMid : ∀ t ∈ Set.Icc c d, f t ≤ f xMid := by
    -- Flatness on `[c, d]` lets us recenter the compact maximizer at the midpoint.
    intro t ht
    rw [hPlateau ht, hPlateau hxMid]
  have hLeftSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c xMid → 0 ≤ slope f t xMid :=
    compact_maximizer_left_slope_nonneg hxMid hmaxMid
  have hRightSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc xMid d → slope f xMid t ≤ 0 :=
    compact_maximizer_right_slope_nonpos hxMid hmaxMid
  -- Once the plateau provides an interior maximizer, the global mode upgrade is the packaged
  -- strict-interior argument.
  intro t ht
  exact
    compact_log_mode_global_of_strict_interior
      hc hd hxMid hxMid_left hxMid_right hLogConcave hLeftSlope hRightSlope ht

/-- Helper for Profile: if the compact logarithmic maximizer sits at the right endpoint and the
two endpoint values agree, then the plateau midpoint is a strict interior global mode. -/
private lemma compact_log_mode_global_of_right_endpoint_plateau
    {a b c d : ℝ} {f : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c < d)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f d) (hendpoints : f c = f d) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → f t ≤ f ((c + d) / 2) := by
  let xMid : ℝ := (c + d) / 2
  have hConcaveIcc : ConcaveOn ℝ (Set.Icc c d) f := by
    -- Restrict the open-core concavity to the compact plateau interval.
    refine hLogConcave.subset ?_ (convex_Icc _ _)
    intro t ht
    exact ⟨lt_of_lt_of_le hc.1 ht.1, lt_of_le_of_lt ht.2 hd.2⟩
  have hPlateau : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c d → f t = f d :=
    concave_eq_of_right_endpoint_maximizer hcd hConcaveIcc hmax hendpoints
  have hxMid : xMid ∈ Set.Icc c d := by
    -- The plateau midpoint lies strictly inside the compact interval.
    dsimp [xMid]
    constructor <;> linarith
  have hxMid_left : c < xMid := by
    dsimp [xMid]
    linarith
  have hxMid_right : xMid < d := by
    dsimp [xMid]
    linarith
  have hmaxMid : ∀ t ∈ Set.Icc c d, f t ≤ f xMid := by
    -- Flatness on `[c, d]` lets us recenter the compact maximizer at the midpoint.
    intro t ht
    rw [hPlateau ht, hPlateau hxMid]
  have hLeftSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c xMid → 0 ≤ slope f t xMid :=
    compact_maximizer_left_slope_nonneg hxMid hmaxMid
  have hRightSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc xMid d → slope f xMid t ≤ 0 :=
    compact_maximizer_right_slope_nonpos hxMid hmaxMid
  -- Once the plateau provides an interior maximizer, the global mode upgrade is the packaged
  -- strict-interior argument.
  intro t ht
  exact
    compact_log_mode_global_of_strict_interior
      hc hd hxMid hxMid_left hxMid_right hLogConcave hLeftSlope hRightSlope ht

/-- Helper for Profile: after transferring a compact maximizer to the logarithmic profile, the
remaining geometry is either a genuine global mode or one of the two strict endpoint branches. -/
private lemma compact_log_mode_geometry
    {a b c d x0 : ℝ} {f : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c ≤ d)
    (hx0 : x0 ∈ Set.Icc c d)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    (hmax : ∀ t ∈ Set.Icc c d, f t ≤ f x0)
    (hLeftSlope : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope f t x0)
    (hRightSlope : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope f x0 t ≤ 0) :
    (∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, f t ≤ f y0) ∨
      c = d ∨
      (c < d ∧ x0 = c ∧ f d < f c) ∨
      (c < d ∧ x0 = d ∧ f c < f d) := by
  rcases lt_or_eq_of_le hcd with hcd_strict | hcd_eq
  · by_cases hx0_left : x0 = c
    · subst x0
      by_cases hendpoints : f d = f c
      · left
        refine ⟨(c + d) / 2, ?_, ?_⟩
        · -- The plateau midpoint stays strictly inside the support core.
          constructor <;> linarith [hc.1, hc.2, hd.1, hd.2, hcd_strict]
        · intro t ht
          -- The endpoint-equality branch is already upgraded to a global midpoint mode.
          exact
            compact_log_mode_global_of_left_endpoint_plateau
              hc hd hcd_strict hLogConcave hmax hendpoints ht
      · right
        right
        left
        refine ⟨hcd_strict, rfl, ?_⟩
        have hfd_le_fc : f d ≤ f c := hmax d (show d ∈ Set.Icc c d from ⟨hcd_strict.le, le_rfl⟩)
        exact lt_of_le_of_ne hfd_le_fc (by simpa [eq_comm] using hendpoints)
    · by_cases hx0_right : x0 = d
      · subst x0
        by_cases hendpoints : f c = f d
        · left
          refine ⟨(c + d) / 2, ?_, ?_⟩
          · -- The plateau midpoint stays strictly inside the support core.
            constructor <;> linarith [hc.1, hc.2, hd.1, hd.2, hcd_strict]
          · intro t ht
            -- The symmetric endpoint-equality branch is also upgraded to a midpoint mode.
            exact
              compact_log_mode_global_of_right_endpoint_plateau
                hc hd hcd_strict hLogConcave hmax hendpoints ht
        · right
          right
          right
          refine ⟨hcd_strict, rfl, ?_⟩
          have hfc_le_fd : f c ≤ f d := hmax c (show c ∈ Set.Icc c d from ⟨le_rfl, hcd_strict.le⟩)
          exact lt_of_le_of_ne hfc_le_fd (by simpa [eq_comm] using hendpoints)
      · left
        refine ⟨x0, ?_, ?_⟩
        · -- If the compact maximizer is not an endpoint, it lies strictly inside the interval.
          constructor
          · exact lt_of_le_of_ne hx0.1 fun h => hx0_left h.symm
          · exact lt_of_le_of_ne hx0.2 hx0_right
        · intro t ht
          -- The strict-interior branch is already packaged as a global mode upgrade.
          exact
            compact_log_mode_global_of_strict_interior
              hc hd hx0
              (lt_of_le_of_ne hx0.1 fun h => hx0_left h.symm)
              (lt_of_le_of_ne hx0.2 hx0_right)
              hLogConcave hLeftSlope hRightSlope ht
  · right
    left
    exact hcd_eq

/-- Helper for Profile: for a concave profile on an interval straddling `0`, the right tail lies
below the secant line through any anchor point `y0 < 0` and the origin. -/
private lemma concaveOn_le_secantLine_right_of_zero
    {a b y0 : ℝ} {f : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hy0 : y0 ∈ Set.Ioo a b) (hy0_lt : y0 < 0)
    (hConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 b) :
    f t ≤ f 0 + slope f y0 0 * t := by
  have hzero : (0 : ℝ) ∈ Set.Ioo a b := ⟨hInteriorSupport.1, hInteriorSupport.2⟩
  have hzero_dom : (0 : ℝ) ∈ {u ∈ Set.Ioo a b | y0 < u} := ⟨hzero, hy0_lt⟩
  have ht_core : t ∈ Set.Ioo a b := ⟨lt_trans hInteriorSupport.1 ht.1, ht.2⟩
  have ht_dom : t ∈ {u ∈ Set.Ioo a b | y0 < u} := ⟨ht_core, lt_trans hy0_lt ht.1⟩
  have hslope_cmp : slope f y0 t ≤ slope f y0 0 := by
    -- Concavity makes farther-right secant slopes no larger than the secant slope through `0`.
    exact hConcave.antitoneOn_slope_gt hy0 hzero_dom ht_dom ht.1.le
  have hfactor_nonneg : 0 ≤ t - y0 := by
    exact sub_nonneg.mpr (le_trans hy0_lt.le ht.1.le)
  have hmul :
      (t - y0) * slope f y0 t ≤ (t - y0) * slope f y0 0 := by
    exact mul_le_mul_of_nonneg_left hslope_cmp hfactor_nonneg
  have hslope_t :
      (t - y0) * slope f y0 t = f t - f y0 := by
    -- Expand the secant slope at `(y0, t)` back to the difference quotient numerator.
    simpa [smul_eq_mul] using (sub_smul_slope f y0 t)
  have hslope_zero :
      (-y0) * slope f y0 0 = f 0 - f y0 := by
    -- The same secant identity at `(y0, 0)` records the intercept at the origin.
    simpa [smul_eq_mul] using (sub_smul_slope f y0 (0 : ℝ))
  have hmain : f t - f y0 ≤ slope f y0 0 * t + (f 0 - f y0) := by
    calc
      f t - f y0 = (t - y0) * slope f y0 t := hslope_t.symm
      _ ≤ (t - y0) * slope f y0 0 := hmul
      _ = (t + (-y0)) * slope f y0 0 := by ring
      _ = slope f y0 0 * t + (f 0 - f y0) := by
            rw [add_mul, hslope_zero]
            ring
  linarith

/-- Helper for Profile: for a concave profile on an interval straddling `0`, the left tail lies
below the secant line through the origin and any anchor point `y0 > 0`. -/
private lemma concaveOn_le_secantLine_left_of_zero
    {a b y0 : ℝ} {f : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hy0 : y0 ∈ Set.Ioo a b) (hy0_pos : 0 < y0)
    (hConcave : ConcaveOn ℝ (Set.Ioo a b) f)
    {t : ℝ} (ht : t ∈ Set.Ioo a 0) :
    f t ≤ f 0 + slope f y0 0 * t := by
  have hzero : (0 : ℝ) ∈ Set.Ioo a b := ⟨hInteriorSupport.1, hInteriorSupport.2⟩
  have hzero_dom : (0 : ℝ) ∈ {u ∈ Set.Ioo a b | u < y0} := ⟨hzero, hy0_pos⟩
  have ht_core : t ∈ Set.Ioo a b := ⟨ht.1, lt_trans ht.2 hInteriorSupport.2⟩
  have ht_dom : t ∈ {u ∈ Set.Ioo a b | u < y0} := ⟨ht_core, lt_trans ht.2 hy0_pos⟩
  have hslope_cmp : slope f y0 0 ≤ slope f y0 t := by
    -- On the left of the mode, secant slopes increase as the second point moves farther left.
    exact hConcave.antitoneOn_slope_lt hy0 ht_dom hzero_dom ht.2.le
  have hfactor_nonpos : t - y0 ≤ 0 := by
    exact sub_nonpos.mpr (le_trans ht.2.le hy0_pos.le)
  have hmul :
      (t - y0) * slope f y0 t ≤ (t - y0) * slope f y0 0 := by
    exact mul_le_mul_of_nonpos_left hslope_cmp hfactor_nonpos
  have hslope_t :
      (t - y0) * slope f y0 t = f t - f y0 := by
    -- Expand the secant slope at `(y0, t)` back to the numerator of the quotient.
    simpa [smul_eq_mul] using (sub_smul_slope f y0 t)
  have hslope_zero :
      (-y0) * slope f y0 0 = f 0 - f y0 := by
    -- The secant identity through `0` provides the common affine intercept.
    simpa [smul_eq_mul] using (sub_smul_slope f y0 (0 : ℝ))
  have hmain : f t - f y0 ≤ slope f y0 0 * t + (f 0 - f y0) := by
    calc
      f t - f y0 = (t - y0) * slope f y0 t := hslope_t.symm
      _ ≤ (t - y0) * slope f y0 0 := hmul
      _ = (t + (-y0)) * slope f y0 0 := by ring
      _ = slope f y0 0 * t + (f 0 - f y0) := by
            rw [add_mul, hslope_zero]
            ring
  linarith

/-- Helper for Profile: a left anchor for the logarithmic profile gives an exponential upper
envelope on the positive tail. -/
private lemma logConcaveDensity_rightTail_le_expSecant
    {a b y0 : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hy0 : y0 ∈ Set.Ioo a b) (hy0_lt : y0 < 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 b) :
    ρ t ≤ ρ 0 * Real.exp (slope (fun t ↦ Real.log (ρ t)) y0 0 * t) := by
  have hzero : (0 : ℝ) ∈ Set.Ioo a b := ⟨hInteriorSupport.1, hInteriorSupport.2⟩
  have ht_core : t ∈ Set.Ioo a b := ⟨lt_trans hInteriorSupport.1 ht.1, ht.2⟩
  have hρ0_pos : 0 < ρ 0 := hρ_pos hzero
  have hρt_pos : 0 < ρ t := hρ_pos ht_core
  have hlog :
      Real.log (ρ t) ≤
        Real.log (ρ 0) + slope (fun t ↦ Real.log (ρ t)) y0 0 * t :=
    concaveOn_le_secantLine_right_of_zero
      hInteriorSupport hy0 hy0_lt hLogConcave ht
  -- Exponentiating the secant-line inequality converts the logarithmic comparison back into
  -- the density-level exponential envelope used in the tail estimates.
  calc
    ρ t = Real.exp (Real.log (ρ t)) := by rw [Real.exp_log hρt_pos]
    _ ≤ Real.exp
          (Real.log (ρ 0) + slope (fun t ↦ Real.log (ρ t)) y0 0 * t) := by
            exact Real.exp_le_exp.mpr hlog
    _ = ρ 0 * Real.exp (slope (fun t ↦ Real.log (ρ t)) y0 0 * t) := by
          rw [Real.exp_add, Real.exp_log hρ0_pos]

/-- Helper for Profile: on the segment from a left anchor to the origin, concavity forces the
logarithmic profile above the corresponding secant line. -/
private lemma logConcaveDensity_segment_ge_expSecant
    {a b y0 : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hy0 : y0 ∈ Set.Ioo a b) (hy0_lt : y0 < 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    {t : ℝ} (ht : t ∈ Set.Icc y0 0) :
    ρ 0 * Real.exp (slope (fun t ↦ Real.log (ρ t)) y0 0 * t) ≤ ρ t := by
  let α : ℝ := (-t) / (-y0)
  let β : ℝ := (t - y0) / (-y0)
  have hy0_neg : 0 < -y0 := by linarith
  have hy0_ne : y0 ≠ 0 := ne_of_lt hy0_lt
  have hzero : (0 : ℝ) ∈ Set.Ioo a b := ⟨hInteriorSupport.1, hInteriorSupport.2⟩
  have ht_core : t ∈ Set.Ioo a b := by
    constructor
    · exact lt_of_lt_of_le hy0.1 ht.1
    · exact lt_of_le_of_lt ht.2 hy0.2
  have hρ0_pos : 0 < ρ 0 := hρ_pos hzero
  have hρt_pos : 0 < ρ t := hρ_pos ht_core
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (by linarith [ht.2]) hy0_neg.le
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg (sub_nonneg.mpr ht.1) hy0_neg.le
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    field_simp [hy0_neg.ne']
    ring
  have ht_combo : α * y0 + β * 0 = t := by
    dsimp [α, β]
    field_simp [hy0_neg.ne']
    ring_nf
  have hconc :
      α * Real.log (ρ y0) + β * Real.log (ρ 0) ≤ Real.log (ρ t) := by
    -- Along the segment `[y0, 0]`, concavity dominates the affine interpolation of the endpoint
    -- logarithms.
    simpa [smul_eq_mul, ht_combo] using
      hLogConcave.2 hy0 hzero hα_nonneg hβ_nonneg hαβ
  have hline :
      Real.log (ρ 0) + slope (fun t ↦ Real.log (ρ t)) y0 0 * t =
        α * Real.log (ρ y0) + β * Real.log (ρ 0) := by
    dsimp [α, β]
    rw [slope_def_field]
    field_simp [hy0_ne]
    ring
  -- Rewrite the secant line through `(y0, log ρ y0)` and `(0, log ρ 0)` into barycentric form,
  -- then exponentiate back to the density.
  calc
    ρ 0 * Real.exp (slope (fun t ↦ Real.log (ρ t)) y0 0 * t)
        = Real.exp
            (Real.log (ρ 0) + slope (fun t ↦ Real.log (ρ t)) y0 0 * t) := by
              rw [Real.exp_add, Real.exp_log hρ0_pos]
    _ ≤ Real.exp (Real.log (ρ t)) := by
          rw [hline]
          exact Real.exp_le_exp.mpr hconc
    _ = ρ t := by rw [Real.exp_log hρt_pos]

/-- Helper for Profile: once the logarithmic profile has a genuine global mode on the normalized
support interval, the remaining one-dimensional work is the sharp left-half ratio inequality. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_ofModeGeometry
    {a b : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    (hMassPos : 0 < ∫ t, ρ t ∂volume)
    (hMomentZero : ∫ t, t * ρ t ∂volume = 0)
    (hModeData :
      (∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, Real.log (ρ t) ≤ Real.log (ρ y0)) ∨
        ∃ c d x0 : ℝ,
          c ∈ Set.Ioo a b ∧
            d ∈ Set.Ioo a b ∧
              x0 ∈ Set.Icc c d ∧
                (∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 →
                  0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0) ∧
                  (∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d →
                    slope (fun t ↦ Real.log (ρ t)) x0 t ≤ 0) ∧
                    ((c < d ∧ x0 = c ∧ Real.log (ρ d) < Real.log (ρ c)) ∨
                      (c < d ∧ x0 = d ∧ Real.log (ρ c) < Real.log (ρ d)))) :
    (∫ t in Set.Iic 0, ρ t ∂volume) / (∫ t, ρ t ∂volume) ≤ 1 - Real.exp (-1) := by
  have hMomentIntegrable :
      Integrable (fun t ↦ t * ρ t) volume :=
    centeredLogConcaveDensity_momentIntegrable_ofOffSupport hρ_off hMassPos
  -- Route correction: the three analytic branches now share one owner, so the unresolved work is
  -- a single secant-tail/exponential-comparison theorem rather than three near-duplicate scripts.
  -- TODO: split on `hModeData`, derive the shared tail-secant hypotheses from the global-mode or
  -- strict-endpoint geometry, and finish with `integral_neg_left_eq_right_of_integral_zero`
  -- together with the explicit exponential half-line integrals.
  sorry

/-- Helper for Profile: once the logarithmic profile has a genuine global mode on the normalized
support interval, the remaining one-dimensional work is the sharp left-half ratio inequality. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_ofGlobalMode
    {a b : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    (hMassPos : 0 < ∫ t, ρ t ∂volume)
    (hMomentZero : ∫ t, t * ρ t ∂volume = 0)
    (hGlobalMode :
      ∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, Real.log (ρ t) ≤ Real.log (ρ y0)) :
    (∫ t in Set.Iic 0, ρ t ∂volume) / (∫ t, ρ t ∂volume) ≤ 1 - Real.exp (-1) := by
  -- Route correction: the genuine global-mode case is now a thin wrapper into the shared analytic
  -- owner, so the unresolved work is localized to one combined mode-geometry theorem.
  exact
    centeredLogConcaveDensity_leftHalfRatio_ofModeGeometry
      hInteriorSupport hρ_off hρ_pos hLogConcave hMassPos hMomentZero (Or.inl hGlobalMode)

/-- Helper for Profile: the strict left-endpoint branch of the packaged compact-mode geometry still
forces the sharp left-half ratio bound for the normalized density. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_ofLeftEndpointGeometry
    {a b c d x0 : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b)
    (hx0 : x0 ∈ Set.Icc c d)
    (hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    (hMassPos : 0 < ∫ t, ρ t ∂volume)
    (hMomentZero : ∫ t, t * ρ t ∂volume = 0)
    (hLeftSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0)
    (hRightSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope (fun t ↦ Real.log (ρ t)) x0 t ≤ 0)
    (hBranch : c < d ∧ x0 = c ∧ Real.log (ρ d) < Real.log (ρ c)) :
    (∫ t in Set.Iic 0, ρ t ∂volume) / (∫ t, ρ t ∂volume) ≤ 1 - Real.exp (-1) := by
  have hModeData :
      (∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, Real.log (ρ t) ≤ Real.log (ρ y0)) ∨
        ∃ c' d' x0' : ℝ,
          c' ∈ Set.Ioo a b ∧
            d' ∈ Set.Ioo a b ∧
              x0' ∈ Set.Icc c' d' ∧
                (∀ ⦃t : ℝ⦄, t ∈ Set.Icc c' x0' →
                  0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0') ∧
                  (∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0' d' →
                    slope (fun t ↦ Real.log (ρ t)) x0' t ≤ 0) ∧
                    ((c' < d' ∧ x0' = c' ∧ Real.log (ρ d') < Real.log (ρ c')) ∨
                      (c' < d' ∧ x0' = d' ∧ Real.log (ρ c') < Real.log (ρ d'))) := by
    -- Package the strict left-endpoint branch into the shared analytic geometry interface.
    exact Or.inr ⟨c, d, x0, hc, hd, hx0, hLeftSlope, hRightSlope, Or.inl hBranch⟩
  -- Route correction: the endpoint branch now reuses the shared analytic owner rather than
  -- carrying a second copy of the final exponential-comparison algebra.
  exact
    centeredLogConcaveDensity_leftHalfRatio_ofModeGeometry
      hInteriorSupport hρ_off hρ_pos hLogConcave hMassPos hMomentZero hModeData

/-- Helper for Profile: the strict right-endpoint branch of the packaged compact-mode geometry is
the symmetric remaining one-dimensional extremal case. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_ofRightEndpointGeometry
    {a b c d x0 : ℝ} {ρ : ℝ → ℝ}
    (hInteriorSupport : a < 0 ∧ 0 < b)
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b)
    (hx0 : x0 ∈ Set.Icc c d)
    (hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0)
    (hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log (ρ t)))
    (hMassPos : 0 < ∫ t, ρ t ∂volume)
    (hMomentZero : ∫ t, t * ρ t ∂volume = 0)
    (hLeftSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0)
    (hRightSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope (fun t ↦ Real.log (ρ t)) x0 t ≤ 0)
    (hBranch : c < d ∧ x0 = d ∧ Real.log (ρ c) < Real.log (ρ d)) :
    (∫ t in Set.Iic 0, ρ t ∂volume) / (∫ t, ρ t ∂volume) ≤ 1 - Real.exp (-1) := by
  have hModeData :
      (∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, Real.log (ρ t) ≤ Real.log (ρ y0)) ∨
        ∃ c' d' x0' : ℝ,
          c' ∈ Set.Ioo a b ∧
            d' ∈ Set.Ioo a b ∧
              x0' ∈ Set.Icc c' d' ∧
                (∀ ⦃t : ℝ⦄, t ∈ Set.Icc c' x0' →
                  0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0') ∧
                  (∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0' d' →
                    slope (fun t ↦ Real.log (ρ t)) x0' t ≤ 0) ∧
                    ((c' < d' ∧ x0' = c' ∧ Real.log (ρ d') < Real.log (ρ c')) ∨
                      (c' < d' ∧ x0' = d' ∧ Real.log (ρ c') < Real.log (ρ d'))) := by
    -- Package the strict right-endpoint branch into the shared analytic geometry interface.
    exact Or.inr ⟨c, d, x0, hc, hd, hx0, hLeftSlope, hRightSlope, Or.inr hBranch⟩
  -- Route correction: the symmetric endpoint branch now reuses the same shared analytic owner.
  exact
    centeredLogConcaveDensity_leftHalfRatio_ofModeGeometry
      hInteriorSupport hρ_off hρ_pos hLogConcave hMassPos hMomentZero hModeData

/-- Helper for Profile: once the compact interval is genuinely nondegenerate, the packaged
geometry disjunction reduces to the global-mode and strict-endpoint owners. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_from_strict_compact_mode
    {m : ℕ} {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c < d)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0)
    (hCompactMode :
      ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, (ψ t) ^ m ≤ (ψ x0) ^ m) :
    (∫ t in Set.Iic 0, (ψ t) ^ m ∂volume) / (∫ t, (ψ t) ^ m ∂volume) ≤
      1 - Real.exp (-1) := by
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  have hm_ne : m ≠ 0 := by
    intro hm
    subst hm
    have hVolumeZero : volume.real (Set.univ : Set ℝ) = 0 := by
      change ENNReal.toReal (volume (Set.univ : Set ℝ)) = 0
      simp
    have hMassPosZero : 0 < volume.real (Set.univ : Set ℝ) := by
      simpa using hMassPos
    have hNotPos : ¬ 0 < volume.real (Set.univ : Set ℝ) := by
      simpa [hVolumeZero]
    exact hNotPos hMassPosZero
  have hρ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ρ t = 0 := by
    intro t ht
    have hψ_zero : ψ t = 0 := hψ_off ht
    simp [ρ, hψ_zero, hm_ne]
  have hρ_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < ρ t := by
    intro t ht
    simpa [ρ] using hPowPos ht
  have hCompactLogMode :
      ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, Real.log (ρ t) ≤ Real.log (ρ x0) := by
    -- Before using slope monotonicity, move the compact maximizer to the logarithmic surface.
    exact compact_mode_transfers_to_log hc hd hρ_pos hCompactMode
  rcases hCompactLogMode with ⟨x0, hx0, hlogMax⟩
  have hLeftSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc c x0 → 0 ≤ slope (fun t ↦ Real.log (ρ t)) t x0 :=
    compact_maximizer_left_slope_nonneg hx0 hlogMax
  have hRightSlope :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc x0 d → slope (fun t ↦ Real.log (ρ t)) x0 t ≤ 0 :=
    compact_maximizer_right_slope_nonpos hx0 hlogMax
  have hModeGeometry :
      (∃ y0 ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, Real.log (ρ t) ≤ Real.log (ρ y0)) ∨
        c = d ∨
        (c < d ∧ x0 = c ∧ Real.log (ρ d) < Real.log (ρ c)) ∨
        (c < d ∧ x0 = d ∧ Real.log (ρ c) < Real.log (ρ d)) := by
    -- Package the already-verified compact-mode geometry before tackling the final 1D ratio
    -- argument.
    exact
      compact_log_mode_geometry
        hc hd hcd.le hx0 hLogConcave hlogMax hLeftSlope hRightSlope
  have hInteriorSupport : a < 0 ∧ 0 < b :=
    centeredLogConcaveDensity_zero_mem_interior_support
      (m := m) (a := a) (b := b) (ψ := ψ)
      hψ_off hPowPos hLogConcave hMassPos hMomentZero
  -- Route correction: the compact-mode theorem is now only a dispatcher from the packaged
  -- geometry disjunction to the dedicated one-dimensional branch owners. The strict-interval
  -- hypothesis removes the degenerate branch before any analytic work starts.
  rcases hModeGeometry with hGlobal | hDegenerate | hLeft | hRight
  · -- The genuine global-mode branch is now isolated in its own one-dimensional owner.
    exact
      centeredLogConcaveDensity_leftHalfRatio_ofGlobalMode
        hInteriorSupport hρ_off hρ_pos hLogConcave hMassPos hMomentZero hGlobal
  · -- The strict compact interval cannot collapse, so the dead branch is discharged immediately.
    exact (hcd.ne hDegenerate).elim
  · -- The strict left-endpoint branch is the first genuine extremal one-sided comparison case.
    exact
      centeredLogConcaveDensity_leftHalfRatio_ofLeftEndpointGeometry
        hInteriorSupport hc hd hx0 hρ_off hρ_pos hLogConcave hMassPos hMomentZero
        hLeftSlope hRightSlope hLeft
  · -- The strict right-endpoint branch is the symmetric extremal comparison case.
    exact
      centeredLogConcaveDensity_leftHalfRatio_ofRightEndpointGeometry
        hInteriorSupport hc hd hx0 hρ_off hρ_pos hLogConcave hMassPos hMomentZero
        hLeftSlope hRightSlope hRight

/-- Helper for Profile: if the original compact interval degenerates, replace it by a strict
interior subinterval before invoking the active compact-mode dispatcher. -/
private theorem centeredLogConcaveDensity_leftHalfRatio_from_compact_mode
    {m : ℕ} {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) (hcd : c ≤ d)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0)
    (hCompactMode :
      ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, (ψ t) ^ m ≤ (ψ x0) ^ m) :
    (∫ t in Set.Iic 0, (ψ t) ^ m ∂volume) / (∫ t, (ψ t) ^ m ∂volume) ≤
      1 - Real.exp (-1) := by
  have hInteriorSupport : a < 0 ∧ 0 < b :=
    centeredLogConcaveDensity_zero_mem_interior_support
      (m := m) (a := a) (b := b) (ψ := ψ)
      hψ_off hPowPos hLogConcave hMassPos hMomentZero
  by_cases hcd_strict : c < d
  · -- The genuine compact interval case is handled by the strict dispatcher.
    exact
      centeredLogConcaveDensity_leftHalfRatio_from_strict_compact_mode
        (m := m) (a := a) (b := b) (c := c) (d := d) (ψ := ψ)
        hc hd hcd_strict hψ_off hPowPos hLogConcave hMassPos hMomentZero hCompactMode
  · have hdeg : c = d := le_antisymm hcd (le_of_not_gt hcd_strict)
    subst hdeg
    let c' : ℝ := (a + c) / 2
    let d' : ℝ := (c + b) / 2
    have hc' : c' ∈ Set.Ioo a b := by
      -- The midpoint of `a` and the collapsed mode stays strictly inside the support core.
      dsimp [c']
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d' ∈ Set.Ioo a b := by
      -- The midpoint of the collapsed mode and `b` also stays strictly inside the support core.
      dsimp [d']
      constructor <;> linarith [hc.1, hc.2]
    have hc'd' : c' < d' := by
      -- The repaired subinterval is strict because the support core straddles the collapsed mode.
      dsimp [c', d']
      linarith [hc.1, hc.2, hInteriorSupport.1, hInteriorSupport.2]
    have hCompactMode' :
        ∃ x0 ∈ Set.Icc c' d', ∀ t ∈ Set.Icc c' d', (ψ t) ^ m ≤ (ψ x0) ^ m := by
      -- Rebuild a compact maximizer on the strict replacement interval before dispatching.
      exact
        powDensity_exists_maximizer_on_subinterval
          (m := m) (a := a) (b := b) (c := c') (d := d') (ψ := ψ)
          hLogConcave hc' hd' hc'd'.le hPowPos
    exact
      centeredLogConcaveDensity_leftHalfRatio_from_strict_compact_mode
        (m := m) (a := a) (b := b) (c := c') (d := d') (ψ := ψ)
        hc' hd' hc'd' hψ_off hPowPos hLogConcave hMassPos hMomentZero hCompactMode'

private theorem centeredLogConcaveDensity_leftHalfRatio_aux
    {m : ℕ} {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hPowPos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m)
    (hLogConcave : ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)))
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0) :
    (∫ t in Set.Iic 0, (ψ t) ^ m ∂volume) / (∫ t, (ψ t) ^ m ∂volume) ≤
      1 - Real.exp (-1) := by
  let ρ : ℝ → ℝ := fun t ↦ (ψ t) ^ m
  have hInteriorSupport : a < 0 ∧ 0 < b :=
    centeredLogConcaveDensity_zero_mem_interior_support
      (m := m) (a := a) (b := b) (ψ := ψ)
      hψ_off hPowPos hLogConcave hMassPos hMomentZero
  -- Route correction: the support normalization is now sharpened to `a < 0 < b`. The only
  -- remaining missing owner is the mode-based half-line envelope on this already normalized
  -- interval.
  have hHalflineEnvelope :
      (∫ t in Set.Iic 0, (ψ t) ^ m ∂volume) / (∫ t, (ψ t) ^ m ∂volume) ≤
        1 - Real.exp (-1) := by
    let c : ℝ := a / 2
    let d : ℝ := b / 2
    have hc : c ∈ Set.Ioo a b := by
      -- The normalized support interval already straddles `0`, so its midpoint subinterval stays
      -- strictly inside the support core.
      dsimp [c]
      constructor <;> linarith [hInteriorSupport.1, hInteriorSupport.2]
    have hd : d ∈ Set.Ioo a b := by
      dsimp [d]
      constructor <;> linarith [hInteriorSupport.1, hInteriorSupport.2]
    have hcd : c ≤ d := by
      dsimp [c, d]
      linarith [hInteriorSupport.1, hInteriorSupport.2]
    have hCompactMode :
        ∃ x0 ∈ Set.Icc c d, ∀ t ∈ Set.Icc c d, ρ t ≤ ρ x0 := by
      -- The powered density already attains a maximum on any compact interval strictly inside the
      -- support core; the remaining missing step is to upgrade this local maximizer to the global
      -- mode required by the source proof.
      simpa [ρ] using
        powDensity_exists_maximizer_on_subinterval
          (m := m) (a := a) (b := b) (c := c) (d := d)
          (ψ := ψ) hLogConcave hc hd hcd hPowPos
    -- Delegate the remaining one-dimensional work to the dedicated compact-mode owner.
    exact
      centeredLogConcaveDensity_leftHalfRatio_from_compact_mode
        (m := m) (a := a) (b := b) (c := c) (d := d) (ψ := ψ)
        hc hd hcd hψ_off hPowPos hLogConcave hMassPos hMomentZero hCompactMode
  simpa [ρ] using hHalflineEnvelope

/-- Helper for Profile: a one-dimensional density whose integer power comes from a centered
concave root on its support interval satisfies the sharp left-half ratio bound. -/
private theorem centeredConcavePowDensity_leftHalfRatio_le_one_sub_exp_neg_one
    {m : ℕ} (hm : 0 < m) {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_concave : ConcaveOn ℝ (Set.Icc a b) ψ)
    (hψ_nonneg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → 0 ≤ ψ t)
    (hψ_off : ∀ ⦃t : ℝ⦄, t ∉ Set.Icc a b → ψ t = 0)
    (hMassPos : 0 < ∫ t, (ψ t) ^ m ∂volume)
    (hMomentZero : ∫ t, t * (ψ t) ^ m ∂volume = 0) :
    (∫ t in Set.Iic 0, (ψ t) ^ m ∂volume) / (∫ t, (ψ t) ^ m ∂volume) ≤
      1 - Real.exp (-1) := by
  have hPowPos :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo a b → 0 < (ψ t) ^ m :=
    powDensity_posOnInterior hm hψ_concave hψ_nonneg hψ_off hMassPos
  have hLogConcave :
      ConcaveOn ℝ (Set.Ioo a b) (fun t ↦ Real.log ((ψ t) ^ m)) :=
    powDensity_logConcaveOnInterior hm hψ_concave hψ_nonneg hψ_off hMassPos
  -- Route correction: the concave-root owner now only has to call the pure log-concave density
  -- endgame, with positivity and logarithmic concavity already packaged separately.
  exact
    centeredLogConcaveDensity_leftHalfRatio_aux
      hψ_off hPowPos hLogConcave hMassPos hMomentZero

/-- Helper for Profile: after the support and moment data are normalized, the only remaining owner
is the one-dimensional root-density estimate for the repaired slice profile. -/
private theorem firstCoordinateSliceProfileRoot_leftHalfRatio_of_supportAENormalization
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U)
    (hU_bounded : Bornology.IsBounded U)
    (hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty)
    (hSupportSubset :
      firstCoordinateSliceSupport i0 U ⊆
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)))
    (hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U))
    (hOffIntervalRoot :
      ∀ ⦃t : ℝ⦄,
        t ∉ Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
            (sSup (firstCoordinateSliceSupport i0 U)) →
          (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0)
    (hOffSupportRoot :
      ∀ ⦃t : ℝ⦄, t ∉ firstCoordinateSliceSupport i0 U →
        (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)) = 0)
    (hNonnegRoot :
      ∀ ⦃t : ℝ⦄, t ∈ firstCoordinateSliceSupport i0 U →
        0 ≤ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ)))
    (hMassPosRoot :
      0 <
        ∫ t,
          (((firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) ^ (n - 1 : ℕ)) ∂volume)
    (hMomentZeroRoot :
      ∫ t,
          t *
            (((firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) ^ (n - 1 : ℕ)) ∂volume =
        0) :
    (∫ t in Set.Iic 0,
        (((firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) ^ (n - 1 : ℕ)) ∂volume) /
        (∫ t,
          (((firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))) ^ (n - 1 : ℕ)) ∂volume) ≤
      1 - Real.exp (-1) := by
  -- Route correction: the assembly theorem below has already reduced the problem to the rooted
  -- one-dimensional density on the normalized support interval.
  let I : Set ℝ :=
    Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
      (sSup (firstCoordinateSliceSupport i0 U))
  let ψ : ℝ → ℝ :=
    fun t ↦ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))
  have hRootConcave : ConcaveOn ℝ I ψ := by
    -- Read the missing Brunn-Minkowski owner through the canonical interval normalization.
    simpa [I, ψ] using
      firstCoordinateSliceProfileRoot_concaveOnInterval
        (hn := hn) (i0 := i0) (U := U) hU_convex hU_bounded
        hSupportNonempty hSupportSubset
        hSupportConvex hOffSupportRoot hNonnegRoot
  have hNonnegInterval :
      ∀ ⦃t : ℝ⦄, t ∈ I → 0 ≤ ψ t := by
    intro t ht
    by_cases hts : t ∈ firstCoordinateSliceSupport i0 U
    · exact hNonnegRoot hts
    · have hψ_zero : ψ t = 0 := by
        simpa [ψ] using hOffSupportRoot hts
      rw [hψ_zero]
  have hIntervalRatio :
      (∫ t in Set.Iic 0, (ψ t) ^ (n - 1 : ℕ) ∂volume) /
          (∫ t, (ψ t) ^ (n - 1 : ℕ) ∂volume) ≤
        1 - Real.exp (-1) := by
    -- The analytic owner is now isolated as a centered concave-density theorem on `I`.
    exact
      centeredConcavePowDensity_leftHalfRatio_le_one_sub_exp_neg_one
        (m := n - 1) (by omega) (a := sInf (firstCoordinateSliceSupport i0 U))
        (b := sSup (firstCoordinateSliceSupport i0 U)) hRootConcave hNonnegInterval
        hOffIntervalRoot hMassPosRoot hMomentZeroRoot
  -- Once the two owner lemmas above are available, the target is just the rooted density ratio
  -- written in the local notation.
  simpa [I, ψ] using hIntervalRatio

/-- Helper for Profile: after bounded-support, positive-mass, and zero-moment transport are in
place, the remaining frontier is the one-dimensional slice-profile inequality on the canonical
support interval. -/
private theorem firstCoordinateSliceProfile_leftHalfRatio_of_intervalCore
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U)
    (hU_bounded : Bornology.IsBounded U)
    (hSupportBound : Bornology.IsBounded (firstCoordinateSliceSupport i0 U))
    (hMomentZero : ∫ t, t * firstCoordinateSliceProfile i0 U t ∂volume = 0)
    (hMassPos : 0 < ∫ t, firstCoordinateSliceProfile i0 U t ∂volume) :
    (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) /
        (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) ≤
      1 - Real.exp (-1) := by
  let ψ : ℝ → ℝ := fun t ↦ (firstCoordinateSliceProfile i0 U t) ^ (((n - 1 : ℕ)⁻¹ : ℝ))
  have hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty := by
    -- Positive total mass ensures that the slice support has endpoints for interval normalization.
    exact
      firstCoordinateSliceSupport_nonempty_of_integral_pos
        (i0 := i0) (U := U) hMassPos
  have hSupportSubset :
      firstCoordinateSliceSupport i0 U ⊆
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)) := by
    -- The bounded support sits inside its canonical `sInf`/`sSup` interval.
    exact
      firstCoordinateSliceSupport_subset_Icc_sInf_sSup_of_bounded
        (i0 := i0) (U := U) hSupportBound
  have hOffInterval :
      ∀ ⦃t : ℝ⦄,
        t ∉ Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
            (sSup (firstCoordinateSliceSupport i0 U)) →
          firstCoordinateSliceProfile i0 U t = 0 := by
    intro t ht
    -- Outside the canonical interval, the slice profile vanishes by support normalization.
    exact
      firstCoordinateSliceProfile_eq_zero_of_not_mem_supportInterval
        (i0 := i0) (U := U) hSupportBound ht
  have hMassPosRoot :
      0 < ∫ t, (ψ t) ^ (n - 1 : ℕ) ∂volume := by
    -- Rewrite the total mass through the `1 / (n - 1)`-root spelling once.
    simpa [ψ, firstCoordinateSliceProfileRootPow_eq (hn := hn) (i0 := i0) (U := U)]
      using hMassPos
  have hMomentZeroRoot :
      ∫ t, t * (ψ t) ^ (n - 1 : ℕ) ∂volume = 0 := by
    -- The centered first moment rewrites through the same root-power normalization.
    simpa [ψ, firstCoordinateSliceProfileRootPow_eq (hn := hn) (i0 := i0) (U := U)]
      using hMomentZero
  have hNonnegRoot :
      ∀ ⦃t : ℝ⦄, t ∈ firstCoordinateSliceSupport i0 U → 0 ≤ ψ t := by
    intro t _ht
    -- The root is nonnegative because the slice profile itself is nonnegative.
    simpa [ψ] using
      Real.rpow_nonneg (firstCoordinateSliceProfile_nonneg i0 U t) (((n - 1 : ℕ)⁻¹ : ℝ))
  have hSupportConvex : Convex ℝ (firstCoordinateSliceSupport i0 U) := by
    -- Route correction: keep the canonical support set as the main surface before any interval
    -- replacement inside the remaining one-dimensional theorem.
    exact convex_firstCoordinateSliceSupport (i0 := i0) hU_convex
  have hOffSupportRoot :
      ∀ ⦃t : ℝ⦄, t ∉ firstCoordinateSliceSupport i0 U → ψ t = 0 := by
    intro t ht
    -- Off the canonical support set, the root-density spelling vanishes directly.
    simpa [ψ] using
      firstCoordinateSliceProfileRoot_eq_zero_of_not_mem_support
        (hn := hn) (i0 := i0) (U := U) ht
  have hOffIntervalRoot :
      ∀ ⦃t : ℝ⦄,
        t ∉ Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
            (sSup (firstCoordinateSliceSupport i0 U)) →
          ψ t = 0 := by
    intro t ht
    -- Switch the interval-off-support vanishing to the rooted profile spelling used below.
    simpa [ψ] using
      firstCoordinateSliceProfileRoot_eq_zero_of_not_mem_supportInterval
        (hn := hn) (i0 := i0) (U := U) hSupportBound ht
  have hRootRatio :
      (∫ t in Set.Iic 0, (ψ t) ^ (n - 1 : ℕ) ∂volume) /
          (∫ t, (ψ t) ^ (n - 1 : ℕ) ∂volume) ≤
        1 - Real.exp (-1) := by
    -- The remaining owner is now isolated as a theorem over the normalized support frontier.
    exact
      firstCoordinateSliceProfileRoot_leftHalfRatio_of_supportAENormalization
        (hn := hn) (i0 := i0) (U := U) hU_convex hU_bounded
        hSupportNonempty hSupportSubset
        hSupportConvex hOffIntervalRoot hOffSupportRoot hNonnegRoot
        hMassPosRoot hMomentZeroRoot
  -- Rewrite the original slice profile back through the rooted-density ratio owner.
  simpa [ψ, firstCoordinateSliceProfileRootPow_eq (hn := hn) (i0 := i0) (U := U)] using
    hRootRatio

/-- Helper for Lemma 3.2.6: after the slice-profile mass identities are in place, the only
remaining frontier is the sharp one-dimensional density ratio bound for the repaired slice profile.
-/
private theorem firstCoordinateSliceProfile_leftHalfRatio_le_one_sub_exp_neg_one
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hU_center : (⨍ u in U, u) = 0) :
    (∫ t in Set.Iic 0, firstCoordinateSliceProfile i0 U t ∂volume) /
        (∫ t, firstCoordinateSliceProfile i0 U t ∂volume) ≤
      1 - Real.exp (-1) := by
  -- Route correction: the mass-transport assembly is complete, and this pass also closes the
  -- bounded-support and zero-first-moment side conditions. The remaining blocker is now only the
  -- Brunn-Minkowski concavity package plus the final one-dimensional density theorem.
  have hSupportBound :
      Bornology.IsBounded (firstCoordinateSliceSupport i0 U) := by
    -- The support interval is bounded because it comes from the bounded convex body `U`.
    exact
      firstCoordinateSliceSupport_bounded_of_convex_finite_pos
        (i0 := i0) hU_convex hU_finite hU_pos
  have hMomentZero :
      ∫ t, t * firstCoordinateSliceProfile i0 U t ∂volume = 0 := by
    -- The centeredness-to-first-moment transport is now closed using ambient boundedness.
    exact
      firstCoordinateSliceProfile_integral_mul_id_eq_zero
        (i0 := i0) hU_convex hU_finite hU_pos hU_center
  have hMassPos :
      0 < ∫ t, firstCoordinateSliceProfile i0 U t ∂volume := by
    -- The denominator in the target ratio is positive because the slice profile integrates to the
    -- ambient volume.
    exact
      firstCoordinateSliceProfile_integral_pos_of_convex
        (i0 := i0) hU_convex hU_finite hU_pos
  have hSupportNonempty : (firstCoordinateSliceSupport i0 U).Nonempty := by
    -- Positive total mass ensures that the support interval really has endpoints to normalize to.
    exact
      firstCoordinateSliceSupport_nonempty_of_integral_pos
        (i0 := i0) (U := U) hMassPos
  have hSupportSubset :
      firstCoordinateSliceSupport i0 U ⊆
        Set.Icc (sInf (firstCoordinateSliceSupport i0 U))
          (sSup (firstCoordinateSliceSupport i0 U)) := by
    -- The bounded support now sits inside the canonical `sInf`/`sSup` interval used by the
    -- one-dimensional reduction.
    exact
      firstCoordinateSliceSupport_subset_Icc_sInf_sSup_of_bounded
        (i0 := i0) (U := U) hSupportBound
  -- Route correction: the public slice-profile theorem now delegates the last one-dimensional step
  -- to the interval-core helper, while the remaining explicit blockers stay isolated earlier in
  -- the theorem-local profile route.
  exact
    firstCoordinateSliceProfile_leftHalfRatio_of_intervalCore
      (hn := hn) (i0 := i0) (U := U) hU_convex
      (convexFiniteVolume_isBounded hU_convex hU_finite hU_pos)
      hSupportBound hMomentZero hMassPos

/-- Helper for Lemma 3.2.6: this theorem-local support declaration isolates the remaining sharp
first-coordinate marginal estimate in the coordinate model. -/
theorem firstCoordinatePushforward_leftHalfRatio_le_one_sub_exp_neg_one
    {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU_convex : Convex ℝ U) (hU_finite : volume U ≠ ⊤) (hU_pos : volume U ≠ 0)
    (hU_center : (⨍ u in U, u) = 0) :
    let μ : Measure ℝ := (volume.restrict U).map (fun u ↦ u.ofLp i0)
    (μ (Set.Iic 0)).toReal / (μ Set.univ).toReal ≤ 1 - Real.exp (-1) := by
  let φ : ℝ → ℝ := firstCoordinateSliceProfile i0 U
  have hMass :
      (∫ t, φ t ∂volume) = (volume U).toReal ∧
        (∫ t in Set.Iic 0, φ t ∂volume) =
          (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal := by
    -- Route correction: the pushforward assembly now reads the slice-mass package from a
    -- dedicated convex-body bridge instead of rebuilding measurability locally.
    simpa [φ] using
      firstCoordinateSliceProfile_totalMass_leftMass_of_convex
        (i0 := i0) U hU_convex hU_finite
  have hcoord_bound :
      (volume (U ∩ {u | u.ofLp i0 ≤ 0})).toReal / (volume U).toReal ≤ 1 - Real.exp (-1) := by
    -- Route correction: the owner theorem is now only the assembly layer. The unresolved work has
    -- been shrunk to the dedicated slice-profile ratio theorem above.
    have hRatio :
        (∫ t in Set.Iic 0, φ t ∂volume) / (∫ t, φ t ∂volume) ≤ 1 - Real.exp (-1) := by
      -- Invoke the isolated slice-profile theorem under the frozen profile name.
      simpa [φ] using
        firstCoordinateSliceProfile_leftHalfRatio_le_one_sub_exp_neg_one
          hn i0 U hU_convex hU_finite hU_pos hU_center
    -- The specialized mass identities convert the slice-profile ratio bound into the coordinate
    -- cut ratio needed by the pushforward rewrite.
    simpa [φ] using
      firstCoordinateCoordinateBound_of_sliceProfileRatioBound
        (i0 := i0) (U := U) hMass hRatio
  -- Assemble the pushforward statement from the now-isolated coordinate-cut estimate.
  exact
    (firstCoordinateCoordinateBound_iff_pushforwardBound
      i0 U hU_finite hU_pos).1 hcoord_bound
