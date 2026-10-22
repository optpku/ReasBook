/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral
open Set Cardinal
open scoped Cardinal
open scoped Pointwise

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

/-- Helper for Exercise 4.3.2: the coordinatewise strict inequality needed to build the
one-dimensional box attached to `[a, b]`. -/
private theorem realIntervalBox_lower_lt_upper (a b : ℝ) (hab : a < b) :
    ∀ i : Fin 1, (![a] : Fin 1 → ℝ) i < (![b] : Fin 1 → ℝ) i := by
  -- `Fin 1` has a single coordinate, so the componentwise inequality is just `hab`.
  intro i
  fin_cases i
  simpa using hab

/-- Helper for Exercise 4.3.2: the one-dimensional `Box` whose closed hull is the interval
`[a, b]`. -/
def realIntervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  Box.mk ![a] ![b] (realIntervalBox_lower_lt_upper a b hab)

/-- Helper for Exercise 4.3.2: Riemann integrability on `[0,1]`, encoded via the canonical
one-dimensional box model. -/
abbrev RiemannIntegrableOnUnitInterval (f : ℝ → ℝ) : Prop :=
  Integrable (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul

local notation "unitIntervalBox" => realIntervalBox 0 1 zero_lt_one
local notation "unitIntervalBoxSet" => Box.Icc unitIntervalBox

/-- Helper for Exercise 4.3.2: the distortion parameter of the canonical one-dimensional box for
`[0,1]`. -/
private noncomputable abbrev unitIntervalBoxDistortion : NNReal :=
  (realIntervalBox 0 1 zero_lt_one).distortion

/-- Helper for Exercise 4.3.2: continuity of the lifted function on the one-dimensional box model
is equivalent to continuity of the original function on `[0,1]` at the transported point. -/
private lemma continuousWithinAt_funUnique_iff {f : ℝ → ℝ} {y : Fin 1 → ℝ}
    (hy : y ∈ unitIntervalBoxSet) :
    ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y ↔
      ContinuousWithinAt f unitIntervalSet (y 0) := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hmem : ∀ z : Fin 1 → ℝ, z ∈ unitIntervalBoxSet ↔ e z ∈ unitIntervalSet := by
    intro z
    -- The unique coordinate records exactly the interval-membership constraints.
    rw [Box.Icc_def]
    simp [e, realIntervalBox, Set.mem_Icc, Pi.le_def]
  let eSub : unitIntervalBoxSet ≃ₜ unitIntervalSet := e.subtype hmem
  have hy' : y 0 ∈ unitIntervalSet := by
    rw [Box.Icc_def] at hy
    simpa [realIntervalBox, Set.mem_Icc, Pi.le_def] using hy
  have heSub : eSub ⟨y, hy⟩ = ⟨y 0, hy'⟩ := by
    rfl
  -- Pass to the subtype restrictions so both continuity statements live on homeomorphic spaces.
  rw [continuousWithinAt_iff_continuousAt_restrict _ hy]
  rw [continuousWithinAt_iff_continuousAt_restrict _ hy']
  have hcomp :
      (Box.Icc unitIntervalBox).restrict (fun z : Fin 1 → ℝ ↦ f (z 0)) =
        (Set.Icc (0 : ℝ) 1).restrict f ∘ eSub := by
    funext x
    rfl
  simpa [hcomp] using
    (eSub.comp_continuousAt_iff' ((Set.Icc (0 : ℝ) 1).restrict f) ⟨y, hy⟩).trans
      (by simp [heSub])

/-- Helper for Exercise 4.3.2: almost-everywhere continuity on `[0,1]` is equivalent to
almost-everywhere continuity of the lifted function on the one-dimensional box model. -/
private lemma aeContinuousWithinAtFunUniqueIff {f : ℝ → ℝ} :
    (∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
      ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y) ↔
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hpreimage : e ⁻¹' unitIntervalSet = unitIntervalBoxSet := by
    ext y
    constructor
    · intro hy
      rw [Box.Icc_def]
      simpa [e, realIntervalBox, Set.mem_Icc, Pi.le_def] using hy
    · intro hy
      rw [Box.Icc_def] at hy
      simpa [e, realIntervalBox, Set.mem_Icc, Pi.le_def] using hy
  have hmap : Measure.map e (volume.restrict unitIntervalBoxSet) = unitIntervalVolume := by
    calc
      Measure.map e (volume.restrict unitIntervalBoxSet) =
          Measure.map e (volume.restrict (e ⁻¹' unitIntervalSet)) := by
            rw [hpreimage]
      _ = (Measure.map e volume).restrict unitIntervalSet := by
            simpa using (e.restrict_map volume unitIntervalSet).symm
      _ = volume.restrict unitIntervalSet := by
            exact congrArg (fun μ => μ.restrict unitIntervalSet)
              ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).map_eq)
      _ = unitIntervalVolume := by
            rfl
  constructor
  · intro hc
    rw [← hmap]
    have hbox : ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet), y ∈ unitIntervalBoxSet :=
      self_mem_ae_restrict (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc
    -- Push the box-side continuity statement through the measurable equivalence.
    refine (e.measurableEmbedding.ae_map_iff).2 ?_
    filter_upwards [hbox, hc] with y hy hyc
    exact (continuousWithinAt_funUnique_iff (f := f) hy).1 hyc
  · intro hc
    rw [← hmap] at hc
    have hbox : ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet), y ∈ unitIntervalBoxSet :=
      self_mem_ae_restrict (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc
    have hpull :
        ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
          ContinuousWithinAt f unitIntervalSet (e y) :=
      (e.measurableEmbedding.ae_map_iff).1 hc
    -- Pull the interval-side continuity statement back to the box model.
    filter_upwards [hbox, hpull] with y hy hyc
    exact (continuousWithinAt_funUnique_iff (f := f) hy).2 hyc

/-- Helper for Exercise 4.3.2: retagging a partition boxwise keeps every new tag in the ambient
unit box. -/
private lemma retaggedWith_tag_mem_Icc
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) :
    ∀ J : Box (Fin 1), (if J ∈ π.boxes then τ J else π.tag J) ∈ Box.Icc unitIntervalBox := by
  intro J
  by_cases hJ : J ∈ π.boxes
  · -- On partition boxes, transport the new tag from `J` to the ambient unit box.
    simpa [hJ] using Box.le_iff_Icc.1 (π.le_of_mem' J hJ) (hτ J hJ)
  · -- Off the partition, keep the original tag.
    simpa [hJ] using π.tag_mem_Icc J

/-- Helper for Exercise 4.3.2: retag a tagged partition without changing its underlying
prepartition. -/
private def retaggedWith
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) :
    TaggedPrepartition unitIntervalBox :=
  { toPrepartition := π.toPrepartition
    tag := fun J ↦ if J ∈ π.boxes then τ J else π.tag J
    tag_mem_Icc := retaggedWith_tag_mem_Icc π τ hτ }

/-- Helper for Exercise 4.3.2: on partition boxes, `retaggedWith` uses the prescribed new tag. -/
private lemma retaggedWith_tag_of_mem
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J)
    {J : Box (Fin 1)} (hJ : J ∈ π) :
    (retaggedWith π τ hτ).tag J = τ J := by
  -- On partition boxes, the defining `if` selects the replacement tag.
  simp [retaggedWith, hJ]

/-- Helper for Exercise 4.3.2: if a tagged partition is subordinate to the constant radius
`r / 2`, then any boxwise retagging stays in the Riemann base set for the doubled radius `r`. -/
private lemma retaggedWith_memBaseSetRiemannOfConst
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox) {c : NNReal}
    {r : ℝ} (hr : 0 < r) (hr2 : 0 < r / 2)
    (hπ :
      IntegrationParams.Riemann.MemBaseSet unitIntervalBox c
        (fun _ : Fin 1 → ℝ ↦ ⟨r / 2, hr2⟩) π)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) :
    IntegrationParams.Riemann.MemBaseSet unitIntervalBox c (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩)
      (retaggedWith π τ hτ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The old and new tags lie in the same box, so every point stays within distance `r`.
    intro J hJ y hy
    rw [retaggedWith_tag_of_mem π τ hτ hJ, Metric.mem_closedBall]
    have hyOld : dist y (π.tag J) ≤ r / 2 := by
      exact Metric.mem_closedBall.1 (hπ.isSubordinate J hJ hy)
    have hnewOld : dist (π.tag J) (τ J) ≤ r / 2 := by
      simpa [dist_comm] using Metric.mem_closedBall.1 (hπ.isSubordinate J hJ (hτ J hJ))
    calc
      dist y (τ J) ≤ dist y (π.tag J) + dist (π.tag J) (τ J) := dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hyOld hnewOld
      _ = r := by ring
  · -- In the Riemann case, the new tags remain Henstock because they stay in their own boxes.
    intro _ J hJ
    simpa [retaggedWith_tag_of_mem π τ hτ hJ] using hτ J hJ
  · intro hD
    cases hD
  · intro hD
    cases hD

/-- Helper for Exercise 4.3.2: one common fine Riemann partition controls the integral sums from
two arbitrary boxwise retaggings of that partition. -/
private lemma integralSum_twoRetaggings_le_of_riemannIntegrable
    {g : (Fin 1 → ℝ) → ℝ}
    (hf : Integrable unitIntervalBox IntegrationParams.Riemann g volume.toBoxAdditive.toSMul)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π : TaggedPrepartition unitIntervalBox,
      π.IsPartition ∧
      IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
        (hf.convergenceR (ε / 2) unitIntervalBoxDistortion) π ∧
      ∀ τ₁ τ₂ : Box (Fin 1) → Fin 1 → ℝ,
        (∀ J ∈ π, τ₁ J ∈ Box.Icc J) →
        (∀ J ∈ π, τ₂ J ∈ Box.Icc J) →
        ‖∑ J ∈ π.boxes, volume.toBoxAdditive.toSMul J (g (τ₁ J) - g (τ₂ J))‖ ≤ ε := by
  classical
  let r : ℝ := hf.convergenceR (ε / 2) unitIntervalBoxDistortion 0
  have hr : 0 < r := (hf.convergenceR (ε / 2) unitIntervalBoxDistortion 0).2
  have hr2 : 0 < r / 2 := half_pos hr
  let rhalf : (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ ↦ ⟨r / 2, hr2⟩
  -- Choose one partition subordinate to the half-radius gauge.
  obtain ⟨π, hπhalf, hπp⟩ :=
    IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann
      unitIntervalBox le_rfl rhalf
  have hconst :
      ∀ x : Fin 1 → ℝ,
        hf.convergenceR (ε / 2) unitIntervalBoxDistortion x =
          hf.convergenceR (ε / 2) unitIntervalBoxDistortion 0 := by
    -- For the Riemann filter, the convergence gauge is constant in the tag.
    intro x
    exact hf.convergenceR_cond (ε / 2) unitIntervalBoxDistortion rfl x
  refine ⟨π, hπp, ?_, ?_⟩
  · -- The half-radius partition is automatically subordinate to the larger convergence radius.
    refine hπhalf.mono (I := unitIntervalBox) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
    change (r / 2 : ℝ) ≤ r
    linarith
  · intro τ₁ τ₂ hτ₁ hτ₂
    let π₁ : TaggedPrepartition unitIntervalBox := retaggedWith π τ₁ hτ₁
    let π₂ : TaggedPrepartition unitIntervalBox := retaggedWith π τ₂ hτ₂
    have hπ₁_const :
        IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) π₁ := by
      -- Retagging inside each box preserves the base-set condition after doubling the radius.
      simpa [π₁] using
        retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf τ₁ hτ₁
    have hπ₂_const :
        IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) π₂ := by
      -- The same transport argument applies to the second retagging.
      simpa [π₂] using
        retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf τ₂ hτ₂
    have hπ₁ :
        IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
          (hf.convergenceR (ε / 2) unitIntervalBoxDistortion) π₁ := by
      refine hπ₁_const.mono (I := unitIntervalBox) le_rfl le_rfl ?_
      intro x hx
      rw [hconst x]
    have hπ₂ :
        IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
          (hf.convergenceR (ε / 2) unitIntervalBoxDistortion) π₂ := by
      refine hπ₂_const.mono (I := unitIntervalBox) le_rfl le_rfl ?_
      intro x hx
      rw [hconst x]
    have hUnion : π₁.iUnion = π₂.iUnion := by
      -- Retagging does not change the underlying prepartition, hence the covered set is unchanged.
      simp [π₁, π₂, retaggedWith]
    have hdist :
        dist (integralSum g volume.toBoxAdditive.toSMul π₁)
          (integralSum g volume.toBoxAdditive.toSMul π₂) ≤ ε := by
      have hhalf : 0 < ε / 2 := half_pos hε
      have :=
        hf.dist_integralSum_le_of_memBaseSet hhalf hhalf hπ₁ hπ₂ hUnion
      simpa [add_halves] using this
    rw [dist_eq_norm] at hdist
    have hsum :
        integralSum g volume.toBoxAdditive.toSMul π₁ -
            integralSum g volume.toBoxAdditive.toSMul π₂ =
          ∑ J ∈ π.boxes, volume.toBoxAdditive.toSMul J (g (τ₁ J) - g (τ₂ J)) := by
      -- Expand both integral sums over the same boxes and rewrite each term with `map_sub`.
      unfold integralSum
      rw [show π₁.boxes = π.boxes by rfl, show π₂.boxes = π.boxes by rfl,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro J hJ
      rw [retaggedWith_tag_of_mem (π := π) (τ := τ₁) (hτ := hτ₁) hJ,
        retaggedWith_tag_of_mem (π := π) (τ := τ₂) (hτ := hτ₂) hJ]
      simpa using ((volume.toBoxAdditive.toSMul J).map_sub (g (τ₁ J)) (g (τ₂ J))).symm
    rw [← hsum]
    exact hdist

/-- Helper for Exercise 4.3.2: a point with positive oscillation inside `unitIntervalBoxSet`
forces every `nhdsWithin` neighborhood to contain a pair of points with a comparably large value
gap. -/
private lemma highOscillation_exists_pair_of_mem_nhdsWithin {g : (Fin 1 → ℝ) → ℝ} {η : ℝ}
    (hη : 0 < η) {x : Fin 1 → ℝ}
    (hx : ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet x) {s : Set (Fin 1 → ℝ)}
    (hs : s ∈ nhdsWithin x unitIntervalBoxSet) :
    ∃ u ∈ s, ∃ v ∈ s, η / 2 ≤ |g u - g v| := by
  by_contra hpair
  push Not at hpair
  have hsImage : g '' s ∈ (nhdsWithin x unitIntervalBoxSet).map g := by
    -- The chosen neighborhood contributes one admissible image set in the infimum defining
    -- `oscillationWithin`.
    rw [Filter.mem_map]
    exact Filter.mem_of_superset hs (fun y hy ↦ Set.mem_image_of_mem g hy)
  have hdiam_le : Metric.ediam (g '' s) ≤ ENNReal.ofReal (η / 2) := by
    -- If every pair in `s` has gap `< η / 2`, then the diameter of `g '' s` is at most `η / 2`.
    rw [Metric.ediam_image_le_iff]
    intro u hu v hv
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_lt <| by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hpair u hu v hv)
  have hosc_le : oscillationWithin g unitIntervalBoxSet x ≤ ENNReal.ofReal (η / 2) :=
    (biInf_le Metric.ediam hsImage).trans hdiam_le
  have hhalf_lt : ENNReal.ofReal (η / 2) < ENNReal.ofReal η := by
    rw [ENNReal.ofReal_lt_ofReal_iff hη]
    linarith
  -- This contradicts the assumed lower bound on the oscillation at `x`.
  exact (not_lt_of_ge hx) (lt_of_le_of_lt hosc_le hhalf_lt)

/-- Helper for Exercise 4.3.2: the union of all partition-box boundaries, together with the outer
boundary of the ambient unit box, is null for `volume.restrict unitIntervalBoxSet`. -/
private lemma measure_partitionBoundary_eq_zero (π : TaggedPrepartition unitIntervalBox) :
    (volume.restrict unitIntervalBoxSet)
      ((⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪
        (unitIntervalBoxSet \ Box.Ioo unitIntervalBox)) = 0 := by
  have hbox_zero :
      ∀ J ∈ π.boxes, (volume.restrict unitIntervalBoxSet) (Box.Icc J \ Box.Ioo J) = 0 := by
    intro J hJ
    have hsubset : Box.Icc J \ Box.Ioo J ⊆ unitIntervalBoxSet := by
      intro x hx
      exact Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx.1
    have hdiff_ae :
        Box.Icc J \ Box.Ioo J =ᵐ[volume] Box.Ioo J \ Box.Ioo J :=
      ae_eq_set_diff (μ := volume) (s := Box.Icc J) (t := Box.Ioo J)
        (s' := Box.Ioo J) (t' := Box.Ioo J) (Box.Ioo_ae_eq_Icc J).symm Filter.EventuallyEq.rfl
    calc
      (volume.restrict unitIntervalBoxSet) (Box.Icc J \ Box.Ioo J) =
          volume (Box.Icc J \ Box.Ioo J) := Measure.restrict_eq_self volume hsubset
      _ = 0 := by
            have hself : Box.Ioo J \ Box.Ioo J = (∅ : Set (Fin 1 → ℝ)) := by
              ext x
              simp
            calc
              volume (Box.Icc J \ Box.Ioo J) =
                  volume (Box.Ioo J \ Box.Ioo J) := measure_congr hdiff_ae
              _ = volume (∅ : Set (Fin 1 → ℝ)) := by rw [hself]
              _ = 0 := measure_empty
  have hboxes_zero :
      (volume.restrict unitIntervalBoxSet) (⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) = 0 := by
    have hcount : ((↑π.boxes : Set (Box (Fin 1)))).Countable := Set.to_countable _
    exact (measure_biUnion_null_iff (μ := volume.restrict unitIntervalBoxSet) hcount).2 hbox_zero
  have hambient_zero :
      (volume.restrict unitIntervalBoxSet) (unitIntervalBoxSet \ Box.Ioo unitIntervalBox) = 0 := by
    have hdiff_ae :
        unitIntervalBoxSet \ Box.Ioo unitIntervalBox =ᵐ[volume]
          Box.Ioo unitIntervalBox \ Box.Ioo unitIntervalBox :=
      ae_eq_set_diff (μ := volume) (s := unitIntervalBoxSet) (t := Box.Ioo unitIntervalBox)
        (s' := Box.Ioo unitIntervalBox) (t' := Box.Ioo unitIntervalBox)
        (Box.Ioo_ae_eq_Icc unitIntervalBox).symm Filter.EventuallyEq.rfl
    calc
      (volume.restrict unitIntervalBoxSet) (unitIntervalBoxSet \ Box.Ioo unitIntervalBox) =
          volume (unitIntervalBoxSet \ Box.Ioo unitIntervalBox) :=
            Measure.restrict_eq_self volume (by intro x hx; exact hx.1)
      _ = 0 := by
            have hself :
                Box.Ioo unitIntervalBox \ Box.Ioo unitIntervalBox = (∅ : Set (Fin 1 → ℝ)) := by
              ext x
              simp
            calc
              volume (unitIntervalBoxSet \ Box.Ioo unitIntervalBox) =
                  volume (Box.Ioo unitIntervalBox \ Box.Ioo unitIntervalBox) :=
                    measure_congr hdiff_ae
              _ = volume (∅ : Set (Fin 1 → ℝ)) := by rw [hself]
              _ = 0 := measure_empty
  -- The total exceptional set is the union of two null pieces.
  exact measure_union_null hboxes_zero hambient_zero

/-- Helper for Exercise 4.3.2: the strict low-oscillation locus on the unit box is open. -/
private lemma isOpen_lowOscillationSet {g : (Fin 1 → ℝ) → ℝ} {η : ℝ} :
    IsOpen {y | oscillationWithin g unitIntervalBoxSet y < ENNReal.ofReal η} := by
  refine EMetric.isOpen_iff.mpr ?_
  intro x hx
  have hx' : oscillationWithin g unitIntervalBoxSet x < ENNReal.ofReal η := by
    simpa using hx
  obtain ⟨ε, hxε, hεη⟩ := exists_between hx'
  have hsingle :
      ∀ z ∈ ({x} : Set (Fin 1 → ℝ)), oscillationWithin g unitIntervalBoxSet z < ε := by
    intro z hz
    simpa [Set.mem_singleton_iff.mp hz] using hxε
  have hcompact : IsCompact ({x} : Set (Fin 1 → ℝ)) := isCompact_singleton
  rcases hcompact.uniform_oscillationWithin (D := unitIntervalBoxSet) hsingle with
    ⟨δ, hδ, hδosc⟩
  refine ⟨ENNReal.ofReal (δ / 2), by simpa using ENNReal.ofReal_pos.2 (half_pos hδ), ?_⟩
  intro y hy
  have hy' : edist y x < ENNReal.ofReal (δ / 2) := by
    simpa using hy
  have hball :
      g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ unitIntervalBoxSet) ∈
        (nhdsWithin y unitIntervalBoxSet).map g := by
    rw [Filter.mem_map]
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _
        (Metric.eball_mem_nhds _ (ENNReal.ofReal_pos.2 (half_pos hδ)))) ?_
    intro z hz
    exact Set.mem_image_of_mem g ⟨hz.2, hz.1⟩
  have hsubset :
      Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ unitIntervalBoxSet ⊆
        Metric.eball x (ENNReal.ofReal δ) ∩ unitIntervalBoxSet := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have htriangle : edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
    have hsum :
        edist z y + edist y x < ENNReal.ofReal δ := by
      have hsum' := ENNReal.add_lt_add hz.1 hy'
      have hadd :
          ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr
        ring
      exact hadd ▸ hsum'
    exact lt_of_le_of_lt htriangle hsum
  have hosc_le :
      oscillationWithin g unitIntervalBoxSet y ≤
        Metric.ediam (g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ unitIntervalBoxSet)) :=
    biInf_le Metric.ediam hball
  have hdiam_le :
      Metric.ediam (g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ unitIntervalBoxSet)) ≤ ε := by
    have himage :
        g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ unitIntervalBoxSet) ⊆
          g '' (Metric.eball x (ENNReal.ofReal δ) ∩ unitIntervalBoxSet) := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact Set.mem_image_of_mem g (hsubset hz)
    exact (Metric.ediam_mono himage).trans (hδosc x (by simp))
  simpa using lt_of_le_of_lt (hosc_le.trans hdiam_le) hεη

/-- Helper for Exercise 4.3.2: the fixed-threshold high-oscillation set on the unit box is
compact. -/
private lemma isCompact_highOscillationSet {g : (Fin 1 → ℝ) → ℝ} {η : ℝ} :
    IsCompact {y | y ∈ unitIntervalBoxSet ∧
      ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet y} := by
  have hopen : IsOpen {y | oscillationWithin g unitIntervalBoxSet y < ENNReal.ofReal η} :=
    isOpen_lowOscillationSet (g := g)
  have hrepr :
      {y | y ∈ unitIntervalBoxSet ∧ ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet y} =
        unitIntervalBoxSet \ {y | oscillationWithin g unitIntervalBoxSet y < ENNReal.ofReal η} := by
    ext y
    simp [not_lt]
  rw [hrepr]
  exact (realIntervalBox 0 1 zero_lt_one).isCompact_Icc.of_isClosed_subset
    ((realIntervalBox 0 1 zero_lt_one).isCompact_Icc.isClosed.sdiff hopen) Set.diff_subset

/-- Helper for Exercise 4.3.2: the fixed-threshold bad set records where the oscillation of `g`
on the unit box is at least `η`. -/
private def highOscillationSet (g : (Fin 1 → ℝ) → ℝ) (η : ℝ) : Set (Fin 1 → ℝ) :=
  {y | y ∈ unitIntervalBoxSet ∧ ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet y}

/-- Helper for Exercise 4.3.2: if a bad point lies in the interior of a box, then that box admits
an ordered pair of tags whose value gap is at least `η / 2`. -/
private lemma existsOrderedPairInBox_of_mem_highOscillationSet {g : (Fin 1 → ℝ) → ℝ} {η : ℝ}
    (hη : 0 < η) {J : Box (Fin 1)} {x : Fin 1 → ℝ}
    (hx : x ∈ highOscillationSet g η ∩ Box.Ioo J) :
    ∃ u ∈ Box.Icc J, ∃ v ∈ Box.Icc J, η / 2 ≤ g u - g v := by
  have hopen : IsOpen (Box.Ioo J) := by
    -- The box interior is a product of open intervals.
    simpa [Box.Ioo] using
      isOpen_set_pi (i := (Set.univ : Set (Fin 1)))
        (s := fun i : Fin 1 => Set.Ioo (J.lower i) (J.upper i))
        Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hnhds : Box.Ioo J ∈ nhdsWithin x unitIntervalBoxSet :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hx.2)
  -- Apply the oscillation witness lemma on the box interior around the bad point.
  obtain ⟨u, hu, v, hv, huv⟩ :=
    highOscillation_exists_pair_of_mem_nhdsWithin (g := g) hη hx.1.2 hnhds
  by_cases hvu : g v ≤ g u
  · -- If `g u` is the larger value, keep the pair in this order.
    refine ⟨u, (Box.Ioo_subset_Icc J) hu, v, (Box.Ioo_subset_Icc J) hv, ?_⟩
    simpa [abs_of_nonneg (sub_nonneg.mpr hvu)] using huv
  · -- Otherwise swap the witnesses so the difference is nonnegative.
    have huv_lt : g u < g v := lt_of_not_ge hvu
    refine ⟨v, (Box.Ioo_subset_Icc J) hv, u, (Box.Ioo_subset_Icc J) hu, ?_⟩
    simpa [abs_of_neg (sub_neg.mpr huv_lt)] using huv

/-- Helper for Exercise 4.3.2: the interior of a one-dimensional box is open. -/
private lemma isOpen_boxIoo (J : Box (Fin 1)) : IsOpen (Box.Ioo J) := by
  -- `Box.Ioo J` is a finite-coordinate product of open intervals.
  simpa [BoxIntegral.Box.Ioo] using
    (isOpen_set_pi (i := Set.univ)
      (s := fun i : Fin 1 => Set.Ioo (J.lower i) (J.upper i))
      (Set.toFinite (s := (Set.univ : Set (Fin 1)))) (fun _ _ => isOpen_Ioo))

/-- Helper for Exercise 4.3.2: for each fixed threshold `η > 0`, the set where the oscillation of
an integrable box-side function is at least `η` has zero restricted volume. -/
private lemma measureHighOscillationSet_eq_zero_of_riemannIntegrable
    {g : (Fin 1 → ℝ) → ℝ}
    (hg : Integrable unitIntervalBox IntegrationParams.Riemann g volume.toBoxAdditive.toSMul)
    {η : ℝ} (hη : 0 < η) :
    (volume.restrict unitIntervalBoxSet) (highOscillationSet g η) = 0 := by
  classical
  let μI : Measure (Fin 1 → ℝ) := volume.restrict unitIntervalBoxSet
  let K : Set (Fin 1 → ℝ) := highOscillationSet g η
  have hKcompact : IsCompact K := by
    simpa [K, highOscillationSet] using isCompact_highOscillationSet (g := g) (η := η)
  haveI : IsFiniteMeasure μI :=
    { measure_univ_lt_top := by
        simpa [μI, Measure.restrict_apply, (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc]
          using (realIntervalBox 0 1 zero_lt_one).isCompact_Icc.measure_lt_top (μ := volume) }
  by_cases hK : μI K = 0
  · simpa [μI, K] using hK
  · have hKpos : 0 < μI K := pos_iff_ne_zero.mpr hK
    exfalso
    have hKreal_pos : 0 < μI.real K := ENNReal.toReal_pos hK (measure_lt_top μI K).ne
    obtain ⟨ε, hεpos, hεlt⟩ := exists_between (mul_pos (half_pos hη) hKreal_pos)
    obtain ⟨π, hπp, hπmem, hretag⟩ :=
      integralSum_twoRetaggings_le_of_riemannIntegrable (g := g) hg hεpos
    have hπhen : π.IsHenstock := hπmem.isHenstock rfl
    let boundary : Set (Fin 1 → ℝ) :=
      (⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪ (unitIntervalBoxSet \ Box.Ioo unitIntervalBox)
    have hboundary_zero : μI boundary = 0 := by
      simpa [μI, boundary] using measure_partitionBoundary_eq_zero π
    let πBad : TaggedPrepartition unitIntervalBox :=
      π.filter fun J => ((K \ boundary) ∩ Box.Ioo J).Nonempty
    have hKdiff_subset : K \ boundary ⊆ πBad.iUnion := by
      -- Remove the null boundary set so each remaining bad point lies in the interior of one box.
      intro x hx
      have hxK : x ∈ K := hx.1
      have hxIcc : x ∈ unitIntervalBoxSet := hxK.1
      have hxNotBoundary : x ∉ boundary := hx.2
      have hxIooI : x ∈ Box.Ioo unitIntervalBox := by
        by_contra hxNotIooI
        exact hxNotBoundary (Or.inr ⟨hxIcc, hxNotIooI⟩)
      have hxI : x ∈ unitIntervalBox := (realIntervalBox 0 1 zero_lt_one).Ioo_subset_coe hxIooI
      have hπp' : π.toPrepartition.IsPartition := hπp
      rcases ExistsUnique.exists (hπp'.existsUnique hxI) with ⟨J, hJπ, hxJ⟩
      have hxIooJ : x ∈ Box.Ioo J := by
        have hxIccJ : x ∈ Box.Icc J := Box.coe_subset_Icc hxJ
        by_contra hxNotIooJ
        apply hxNotBoundary
        left
        refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨hJπ, ?_⟩⟩
        exact ⟨hxIccJ, hxNotIooJ⟩
      have hJbad : J ∈ πBad := by
        exact π.mem_filter.2 ⟨hJπ, ⟨x, ⟨hx, hxIooJ⟩⟩⟩
      exact πBad.subset_iUnion hJbad hxJ
    have hKdiff_pos : 0 < μI (K \ boundary) := by
      rw [measure_diff_null hboundary_zero]
      exact hKpos
    have hKdiff_real : μI.real (K \ boundary) = μI.real K := by
      exact congrArg ENNReal.toReal
        (measure_diff_null (μ := μI) (s := K) (t := boundary) hboundary_zero)
    have hwitness :
        ∀ J ∈ πBad, ∃ u v, u ∈ Box.Ioo J ∧ v ∈ Box.Ioo J ∧ η / 2 ≤ |g u - g v| := by
      intro J hJbad
      rcases (π.mem_filter.1 hJbad).2 with ⟨x, hxKdiff, hxIooJ⟩
      have hsIoo : Box.Ioo J ∈ nhds x := (isOpen_boxIoo J).mem_nhds hxIooJ
      have hs : Box.Ioo J ∈ nhdsWithin x unitIntervalBoxSet := by
        exact Filter.mem_of_superset (inter_mem_nhdsWithin _ hsIoo) (fun y hy ↦ hy.2)
      have hxOsc : ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet x := hxKdiff.1.2
      rcases
        highOscillation_exists_pair_of_mem_nhdsWithin (g := g) hη hxOsc hs with
          ⟨u, hu, v, hv, huv⟩
      exact ⟨u, v, hu, hv, huv⟩
    choose u₀ v₀ hu₀ hv₀ hgap using hwitness
    let τLo : Box (Fin 1) → Fin 1 → ℝ := fun J ↦
      if hJ : J ∈ πBad then
        if hle : g (u₀ J hJ) ≤ g (v₀ J hJ) then u₀ J hJ else v₀ J hJ
      else π.tag J
    let τHi : Box (Fin 1) → Fin 1 → ℝ := fun J ↦
      if hJ : J ∈ πBad then
        if hle : g (u₀ J hJ) ≤ g (v₀ J hJ) then v₀ J hJ else u₀ J hJ
      else π.tag J
    have hτLo_box : ∀ J ∈ π, τLo J ∈ Box.Icc J := by
      -- On bad boxes use the chosen witness; elsewhere keep the old Henstock tag.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
        · have hmem : u₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hu₀ J hJbad)
          simpa [τLo, hJbad, hle] using hmem
        · have hmem : v₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hv₀ J hJbad)
          simpa [τLo, hJbad, hle] using hmem
      · simpa [τLo, hJbad] using hπhen J hJπ
    have hτHi_box : ∀ J ∈ π, τHi J ∈ Box.Icc J := by
      -- The second retagging uses the larger-value witness on bad boxes.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
        · have hmem : v₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hv₀ J hJbad)
          simpa [τHi, hJbad, hle] using hmem
        · have hmem : u₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hu₀ J hJbad)
          simpa [τHi, hJbad, hle] using hmem
      · simpa [τHi, hJbad] using hπhen J hJπ
    have hgap_oriented : ∀ J ∈ πBad, η / 2 ≤ g (τHi J) - g (τLo J) := by
      -- Orient the witness pair by value so every bad-box contribution is nonnegative.
      intro J hJbad
      by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
      · have hnonpos : g (u₀ J hJbad) - g (v₀ J hJbad) ≤ 0 := sub_nonpos.mpr hle
        simpa [τLo, τHi, hJbad, hle, abs_of_nonpos hnonpos] using hgap J hJbad
      · have hge : g (v₀ J hJbad) ≤ g (u₀ J hJbad) := le_of_not_ge hle
        simpa [τLo, τHi, hJbad, hle, abs_of_nonneg (sub_nonneg.mpr hge)] using hgap J hJbad
    let term : Box (Fin 1) → ℝ :=
      fun J ↦ volume.toBoxAdditive.toSMul J (g (τHi J) - g (τLo J))
    have hterm_nonneg : ∀ J ∈ π.boxes, 0 ≤ term J := by
      -- Every box contributes a nonnegative amount, and non-bad boxes contribute exactly `0`.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
          rw [MeasureTheory.Measure.toBoxAdditive_apply]
          exact measureReal_nonneg
        have hgap_nonneg : 0 ≤ g (τHi J) - g (τLo J) := by
          exact le_trans (le_of_lt (half_pos hη)) (hgap_oriented J hJbad)
        simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul] using
          mul_nonneg hvol_nonneg hgap_nonneg
      · simp [term, τLo, τHi, hJbad]
    have hmeasure_selected :
        μI.real πBad.iUnion = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
      -- On every selected box the restricted measure agrees with the ambient volume.
      calc
        μI.real πBad.iUnion = ∑ J ∈ πBad.boxes, μI.real J := by
          simpa [μI] using πBad.toPrepartition.measure_iUnion_toReal (μ := μI)
        _ = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
          refine Finset.sum_congr rfl ?_
          intro J hJ
          have hsubsetJ : (J : Set (Fin 1 → ℝ)) ⊆ unitIntervalBoxSet := by
            intro x hx
            exact Box.le_iff_Icc.1 (πBad.toPrepartition.le_of_mem' J hJ) (Box.coe_subset_Icc hx)
          calc
            μI.real J = volume.real (J : Set (Fin 1 → ℝ)) := by
              simp [μI, measureReal_def, Measure.restrict_eq_self volume hsubsetJ]
            _ = volume.toBoxAdditive J := by
              simp [MeasureTheory.Measure.toBoxAdditive_apply]
    have hKdiff_real_le :
        μI.real (K \ boundary) ≤ μI.real πBad.iUnion := by
      exact ENNReal.toReal_mono (measure_lt_top μI _).ne (measure_mono hKdiff_subset)
    have hterm_lower :
        ∀ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J ≤ term J := by
      -- Each selected box contributes at least `(η / 2) * volume(J)`.
      intro J hJ
      have hJbad : J ∈ πBad := hJ
      have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
        rw [MeasureTheory.Measure.toBoxAdditive_apply]
        exact measureReal_nonneg
      have hmul := mul_le_mul_of_nonneg_left (hgap_oriented J hJbad) hvol_nonneg
      simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        using hmul
    have hsum_selected_le_all :
        ∑ J ∈ πBad.boxes, term J ≤ ∑ J ∈ π.boxes, term J := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun J hJ ↦ (π.mem_filter.1 hJ).1)
        (fun J hJπ hJnot ↦ hterm_nonneg J hJπ)
    have hsum_lower :
        (η / 2) * μI.real K ≤ ∑ J ∈ π.boxes, term J := by
      calc
        (η / 2) * μI.real K = (η / 2) * μI.real (K \ boundary) := by rw [hKdiff_real]
        _ ≤ (η / 2) * μI.real πBad.iUnion := by
          exact mul_le_mul_of_nonneg_left hKdiff_real_le (le_of_lt (half_pos hη))
        _ = ∑ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J := by
          rw [hmeasure_selected, Finset.mul_sum]
        _ ≤ ∑ J ∈ πBad.boxes, term J := Finset.sum_le_sum hterm_lower
        _ ≤ ∑ J ∈ π.boxes, term J := hsum_selected_le_all
    have hsum_bound :
        ‖∑ J ∈ π.boxes, term J‖ ≤ ε := by
      exact hretag τHi τLo hτHi_box hτLo_box
    have hsum_nonneg : 0 ≤ ∑ J ∈ π.boxes, term J := Finset.sum_nonneg hterm_nonneg
    rw [Real.norm_of_nonneg hsum_nonneg] at hsum_bound
    have hstrict : ε < ∑ J ∈ π.boxes, term J := lt_of_lt_of_le hεlt hsum_lower
    exact (not_lt_of_ge hsum_bound) hstrict

/-- Helper for Exercise 4.3.2: the box-side lifted map is almost everywhere continuous whenever
the original function is Riemann integrable on `[0,1]`. -/
private lemma aeContinuousWithinAtLift_of_riemannIntegrable {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f) :
    ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
      ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y := by
  -- Route correction: work directly with threshold oscillation sets on the box model, then pass
  -- from vanishing oscillation to `ContinuousWithinAt` at the end.
  let g : (Fin 1 → ℝ) → ℝ := fun z ↦ f (z 0)
  have hmem : ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet), y ∈ unitIntervalBoxSet :=
    self_mem_ae_restrict (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc
  have hthreshold :
      ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
        y ∉ highOscillationSet g (1 / (n + 1 : ℝ)) := by
    intro n
    -- Each reciprocal threshold bad set has measure zero by the fixed-threshold lemma.
    exact MeasureTheory.compl_mem_ae_iff.2 <|
      measureHighOscillationSet_eq_zero_of_riemannIntegrable (g := g) hf (by positivity)
  have hall :
      ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
        ∀ n : ℕ, y ∉ highOscillationSet g (1 / (n + 1 : ℝ)) :=
    eventually_countable_forall.2 hthreshold
  filter_upwards [hmem, hall] with y hyBox hyAll
  have hoscZero : oscillationWithin g unitIntervalBoxSet y = 0 := by
    by_contra hoscZero
    set ω := oscillationWithin g unitIntervalBoxSet y with hω
    have hωne : ω ≠ 0 := by simpa [ω] using hoscZero
    by_cases htop : ω = ⊤
    · -- Infinite oscillation already puts `y` in the first threshold bad set.
      have hyBad : y ∈ highOscillationSet g (1 / ((0 : ℕ) + 1 : ℝ)) := by
        refine ⟨hyBox, ?_⟩
        have hone : (1 : ENNReal) ≤ oscillationWithin g unitIntervalBoxSet y := by
          rw [← hω, htop]
          exact le_top
        simpa using hone
      exact hyAll 0 hyBad
    · have hωtoRealPos : 0 < ω.toReal := ENNReal.toReal_pos hωne htop
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hωtoRealPos
      have hyBad : y ∈ highOscillationSet g (1 / (n + 1 : ℝ)) := by
        refine ⟨hyBox, ?_⟩
        rw [← hω, ENNReal.ofReal_le_iff_le_toReal htop]
        exact le_of_lt hn
      exact hyAll n hyBad
  -- Zero oscillation is exactly the box-side continuity criterion.
  simpa [g] using (OscillationWithin.eq_zero_iff_continuousWithinAt g hyBox).1 hoscZero

/-- Helper for Exercise 4.3.2: almost-everywhere continuity on `[0,1]` implies almost-everywhere
measurability on the restricted Lebesgue measure. -/
private lemma aemeasurable_of_aeContinuousWithinAt_unitInterval {f : ℝ → ℝ}
    (hf :
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x) :
    AEMeasurable f unitIntervalVolume := by
  let bad : Set ℝ := {x | ¬ ContinuousWithinAt f unitIntervalSet x}
  have hbad_zero : unitIntervalVolume bad = 0 := by
    -- Convert the almost-everywhere continuity statement into a null exceptional set.
    simpa [bad] using (ae_iff.1 hf)
  obtain ⟨U, hbadU, hU_meas, hU_zero⟩ := exists_measurable_superset_of_null hbad_zero
  let good : Set ℝ := unitIntervalSet \ U
  have hUnit_meas : MeasurableSet unitIntervalSet := isClosed_Icc.measurableSet
  have hgood_meas : MeasurableSet good := by
    -- The good set is the measurable full-measure continuity locus inside `[0,1]`.
    simp [good, hUnit_meas, hU_meas]
  have hgood_cont : ContinuousOn f good := by
    intro x hx
    have hxcont : ContinuousWithinAt f unitIntervalSet x := by
      by_contra hxnot
      exact hx.2 (hbadU hxnot)
    -- Restrict continuity within `[0,1]` to the smaller good set.
    exact hxcont.mono <| by
      intro y hy
      exact hy.1
  have hgood_ae : good =ᵐ[unitIntervalVolume] unitIntervalSet := by
    have hunit_ae : ∀ᵐ x ∂unitIntervalVolume, x ∈ unitIntervalSet :=
      self_mem_ae_restrict hUnit_meas
    have hU_ae : ∀ᵐ x ∂unitIntervalVolume, x ∉ U := by
      rw [ae_iff]
      simpa using hU_zero
    -- Outside the null exceptional set `U`, the good set is exactly `[0,1]`.
    filter_upwards [hunit_ae, hU_ae] with x hxUnit hxU
    apply propext
    constructor
    · intro hx
      exact hx.1
    · intro _
      exact ⟨hxUnit, hxU⟩
  have hgood_aemeasurable :
      AEMeasurable f ((volume.restrict unitIntervalSet).restrict good) :=
    hgood_cont.aemeasurable (μ := volume.restrict unitIntervalSet) hgood_meas
  have hrestrict :
      (volume.restrict unitIntervalSet).restrict good =
        (volume.restrict unitIntervalSet).restrict unitIntervalSet :=
    Measure.restrict_congr_set hgood_ae
  rw [hrestrict] at hgood_aemeasurable
  -- Rewrite away the redundant second restriction to recover the target measure.
  simpa [Measure.restrict_restrict, hUnit_meas] using hgood_aemeasurable

-- Proof sketch: transport Riemann box integrability to box-side a.e. continuity, move that
-- statement back to `[0,1]`, and then pass from full-measure continuity to measurability.
/-- Exercise 4.3.2: if `f` is Riemann integrable on `[0,1]`, then `f` is Lebesgue measurable on
`[0,1]`. -/
theorem aemeasurable_restrict_unitInterval_of_riemannIntegrable
    {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f) :
    AEMeasurable f unitIntervalVolume := by
  have hboxc :
      ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
        ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y :=
    aeContinuousWithinAtLift_of_riemannIntegrable hf
  have hinterval :
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x :=
    (aeContinuousWithinAtFunUniqueIff (f := f)).1 hboxc
  -- The interval-side almost-everywhere continuity statement is exactly the measurable endgame.
  exact aemeasurable_of_aeContinuousWithinAt_unitInterval hinterval

/-- Helper for Exercise 4.3.2: a countably generated measurable space with at least continuum many
points has a nonmeasurable subset. -/
private theorem exists_nonmeasurableSet_of_countablyGenerated
    (α : Type*) [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α] (hα : 𝔠 ≤ #α) :
    ∃ s : Set α, ¬ MeasurableSet s := by
  classical
  -- The countable generating family yields at most continuum many measurable sets.
  have hcount : Set.Countable (MeasurableSpace.countableGeneratingSet α) :=
    MeasurableSpace.countable_countableGeneratingSet
  have hgen : #(MeasurableSpace.countableGeneratingSet α) ≤ 𝔠 := by
    haveI : Countable (MeasurableSpace.countableGeneratingSet α) := hcount.to_subtype
    exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  have hmeas : #{s : Set α // MeasurableSet s} ≤ 𝔠 := by
    have hm : ‹MeasurableSpace α› = MeasurableSpace.generateFrom
        (MeasurableSpace.countableGeneratingSet α) := by
      symm
      exact MeasurableSpace.generateFrom_countableGeneratingSet
    rw [hm]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum hgen
  -- If every subset were measurable, then the full powerset would also have size at most continuum.
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (Subtype.val : {s : Set α // MeasurableSet s} → Set α) := by
    intro s
    exact ⟨⟨s, h s⟩, rfl⟩
  have hset : #(Set α) ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective hsurj).trans hmeas
  rw [Cardinal.mk_set] at hset
  exact not_lt_of_ge (hset.trans hα) (Cardinal.cantor #α)

/-- Helper for Exercise 4.3.2: the Cantor subtype has a nonmeasurable subset. -/
private theorem exists_nonmeasurableSet_cantorSet : ∃ A : Set cantorSet, ¬ MeasurableSet A := by
  -- The Cantor subtype is countably generated and has continuum many points via its binary coding.
  have hcard : 𝔠 ≤ #(cantorSet) := by
    have hEq : #(cantorSet) = 𝔠 := by
      calc
        #(cantorSet) = #(ℕ → Bool) := cantorSetEquivNatToBool.cardinal_eq
        _ = 𝔠 := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
    simp [hEq]
  exact exists_nonmeasurableSet_of_countablyGenerated cantorSet hcard

/-- Helper for Exercise 4.3.2: dividing a set of reals by `3` is the same as scaling it by
`(1 / 3 : ℝ)`. -/
private lemma image_div_three_eq_smul (s : Set ℝ) :
    (· / 3) '' s = ((1 / 3 : ℝ) • s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [div_eq_mul_inv, smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [div_eq_mul_inv, smul_eq_mul, mul_comm]⟩

/-- Helper for Exercise 4.3.2: translating a set of reals preserves Lebesgue measure. -/
private lemma volume_image_add_const (c : ℝ) (s : Set ℝ) :
    volume ((fun x : ℝ ↦ x + c) '' s) = volume s := by
  -- The translation map is bijective and preserves volume.
  calc
    volume ((fun x : ℝ ↦ x + c) '' s) =
        volume ((fun x : ℝ ↦ x + c) ⁻¹' ((fun x : ℝ ↦ x + c) '' s)) := by
          symm
          exact measure_preimage_add_right volume c ((fun x : ℝ ↦ x + c) '' s)
    _ = volume s := by
      simp

/-- Helper for Exercise 4.3.2: the `n`-th pre-Cantor set has measure at most `(2 / 3)^n`. -/
private theorem preCantorSet_volume_le_pow (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
  induction n with
  | zero =>
      -- The zeroth pre-Cantor set is the unit interval.
      simp [preCantorSet_zero, Real.volume_Icc]
  | succ n ihn =>
      have hthird_nonneg : 0 ≤ (1 / 3 : ℝ) := by positivity
      have hscale :
          volume ((· / 3) '' preCantorSet n) =
            ENNReal.ofReal (1 / 3 : ℝ) * volume (preCantorSet n) := by
        -- Scaling by `1 / 3` rescales volume by the same factor in dimension one.
        rw [image_div_three_eq_smul, volume.addHaar_smul_of_nonneg hthird_nonneg]
        simp
      have hshift :
          volume ((fun x : ℝ ↦ x + 2 / 3) '' ((· / 3) '' preCantorSet n)) =
            volume ((· / 3) '' preCantorSet n) :=
        volume_image_add_const (2 / 3 : ℝ) ((· / 3) '' preCantorSet n)
      have hsucc_le :
          volume (preCantorSet (n + 1)) ≤ ENNReal.ofReal (2 / 3 : ℝ) * volume (preCantorSet n) := by
        -- The next-stage set is the union of two translated `1/3`-scaled copies.
        rw [preCantorSet_succ]
        have hunion :
            volume (((· / 3) '' preCantorSet n) ∪ ((fun x : ℝ ↦ (2 + x) / 3) '' preCantorSet n)) ≤
              volume ((· / 3) '' preCantorSet n) +
                volume (((fun x : ℝ ↦ (2 + x) / 3) '' preCantorSet n) : Set ℝ) := by
          exact measure_union_le ((· / 3) '' preCantorSet n)
            (((fun x : ℝ ↦ (2 + x) / 3) '' preCantorSet n) : Set ℝ)
        refine hunion.trans ?_
        exact le_of_eq <| by
          have htranslate :
              ((fun x ↦ (2 + x) / 3) '' preCantorSet n) =
                (fun x : ℝ ↦ x + 2 / 3) '' ((· / 3) '' preCantorSet n) := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              exact ⟨y / 3, ⟨y, hy, by ring_nf⟩, by ring_nf⟩
            · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
              exact ⟨z, hz, by ring_nf⟩
          calc
            volume ((· / 3) '' preCantorSet n) +
                volume (((fun x ↦ (2 + x) / 3) '' preCantorSet n)) =
                volume ((· / 3) '' preCantorSet n) +
                  volume ((fun x : ℝ ↦ x + 2 / 3) '' ((· / 3) '' preCantorSet n)) := by
                    rw [htranslate]
            _ = volume ((· / 3) '' preCantorSet n) + volume ((· / 3) '' preCantorSet n) := by
              rw [hshift]
            _ = ENNReal.ofReal (2 / 3 : ℝ) * volume (preCantorSet n) := by
              rw [hscale]
              calc
                ENNReal.ofReal (1 / 3 : ℝ) * volume (preCantorSet n) +
                    ENNReal.ofReal (1 / 3 : ℝ) * volume (preCantorSet n) =
                    (ENNReal.ofReal (1 / 3 : ℝ) + ENNReal.ofReal (1 / 3 : ℝ)) *
                      volume (preCantorSet n) := by
                        rw [add_mul]
                _ = ENNReal.ofReal (2 / 3 : ℝ) * volume (preCantorSet n) := by
                  have hconst :
                      ENNReal.ofReal (1 / 3 : ℝ) + ENNReal.ofReal (1 / 3 : ℝ) =
                        ENNReal.ofReal (2 / 3 : ℝ) := by
                    rw [← ENNReal.ofReal_add]
                    · norm_num
                    · positivity
                    · positivity
                  rw [hconst]
      calc
        volume (preCantorSet (n + 1)) ≤ ENNReal.ofReal (2 / 3 : ℝ) * volume (preCantorSet n) :=
          hsucc_le
        _ ≤ ENNReal.ofReal (2 / 3 : ℝ) * ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
          gcongr
        _ = ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1)) := by
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
            (ENNReal.ofReal_mul (p := (2 / 3 : ℝ)) (q := ((2 / 3 : ℝ) ^ n))
              (show 0 ≤ (2 / 3 : ℝ) by positivity)).symm

/-- Helper for Exercise 4.3.2: the Cantor set has Lebesgue measure zero. -/
private theorem volume_cantorSet_zero : volume cantorSet = 0 := by
  -- Every pre-Cantor approximation bounds the Cantor set, and these bounds tend to zero.
  by_contra hCantor
  have hCantor_ne_top : volume cantorSet ≠ ⊤ := by
    have hInterval : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
      exact (measure_Icc_lt_top (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))).ne
    exact ne_top_of_le_ne_top hInterval (measure_mono cantorSet_subset_unitInterval)
  have hCantor_pos_toReal : 0 < (volume cantorSet).toReal :=
    ENNReal.toReal_pos hCantor hCantor_ne_top
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hCantor_pos_toReal (by norm_num : (2 / 3 : ℝ) < 1)
  have hsubset_bound : volume cantorSet ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
    exact (measure_mono (by
      intro x hx
      exact Set.mem_iInter.mp hx n)).trans (preCantorSet_volume_le_pow n)
  have htoReal_bound :
      (volume cantorSet).toReal ≤ ((2 / 3 : ℝ) ^ n) := by
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsubset_bound
  exact not_lt_of_ge htoReal_bound hn

/-- Helper for Exercise 4.3.2: the indicator of a set is continuous away from the closure of that
set. -/
private lemma continuousAt_indicator_one_of_notMem_closure {T : Set ℝ} {x : ℝ}
    (hx : x ∉ closure T) :
    ContinuousAt (T.indicator (fun _ ↦ (1 : ℝ))) x := by
  -- Outside the closure, the indicator is locally constant with value `0`.
  have hopen : IsOpen (closure T)ᶜ := isClosed_closure.isOpen_compl
  rcases Metric.isOpen_iff.mp hopen x hx with ⟨ε, hεpos, hball⟩
  have hEventually :
      (T.indicator (fun _ ↦ (1 : ℝ))) =ᶠ[nhds x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x hεpos] with y hy
    have hyClosure : y ∉ closure T := hball hy
    have hyT : y ∉ T := fun hyT => hyClosure (subset_closure hyT)
    simp [Set.indicator_of_notMem, hyT]
  simpa using continuousAt_const.congr hEventually.symm

/-- Helper for Exercise 4.3.2: if the closure of `T` has measure zero, then the indicator of `T`
is Riemann integrable on `[0,1]`. -/
private theorem riemannIntegrableOnUnitInterval_indicator_of_closure_null
    {T : Set ℝ} (hT : volume (closure T) = 0) :
    RiemannIntegrableOnUnitInterval (T.indicator (fun _ ↦ (1 : ℝ))) := by
  let I := realIntervalBox 0 1 zero_lt_one
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ T.indicator (fun _ ↦ (1 : ℝ)) (x 0)
  -- Boundedness is immediate because the indicator takes only the values `0` and `1`.
  have hbounded : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖g x‖ ≤ C := by
    refine ⟨1, ?_⟩
    intro x hx
    by_cases hxT : x 0 ∈ T
    · simp [g, Set.indicator_of_mem, hxT]
    · simp [g, Set.indicator_of_notMem, hxT]
  -- The only possible discontinuities occur above the closed null set `closure T`.
  have hcont :
      ∀ᵐ x ∂(volume.restrict (Box.Icc I)), ContinuousWithinAt g (Box.Icc I) x := by
    let bad : Set (Fin 1 → ℝ) := (fun x : Fin 1 → ℝ ↦ x 0) ⁻¹' closure T
    have hbad_meas : MeasurableSet bad := by
      exact isClosed_closure.measurableSet.preimage (measurable_pi_apply 0)
    have hbad_zero : volume bad = 0 := by
      -- The unique-coordinate projection preserves volume.
      have hmap :
          Measure.map (fun x : Fin 1 → ℝ ↦ x 0) volume = volume :=
        (volume_preserving_funUnique (Fin 1) ℝ).map_eq
      calc
        volume bad = (Measure.map (fun x : Fin 1 → ℝ ↦ x 0) volume) (closure T) := by
          simpa [bad] using
            (Measure.map_apply (measurable_pi_apply 0) isClosed_closure.measurableSet).symm
        _ = volume (closure T) := by
          exact congrArg (fun μ : Measure ℝ => μ (closure T)) hmap
        _ = 0 := hT
    have hOutside :
        ∀ᵐ x ∂volume, x ∉ bad := by
      change badᶜ ∈ ae volume
      rw [mem_ae_iff]
      simpa [hbad_meas] using hbad_zero
    have hOutsideCont :
        ∀ᵐ x ∂volume, x ∈ Box.Icc I → ContinuousWithinAt g (Box.Icc I) x := by
      filter_upwards [hOutside] with x hxOutside hxI
      have hcoord : x 0 ∉ closure T := hxOutside
      have hcontAt : ContinuousAt g x := by
        simpa [g] using
          (ContinuousAt.comp' (f := fun z : Fin 1 → ℝ ↦ z 0)
            (g := T.indicator (fun _ ↦ (1 : ℝ))) (x := x)
            (continuousAt_indicator_one_of_notMem_closure (T := T) hcoord)
            (continuous_apply 0).continuousAt)
      exact hcontAt.continuousWithinAt
    exact (ae_restrict_iff' I.measurableSet_Icc).2 hOutsideCont
  -- Apply the box-integrability criterion to the lifted one-dimensional box model.
  exact BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt
    (l := IntegrationParams.Riemann) hbounded volume hcont

/-- Helper for Exercise 4.3.2: nonmeasurability on the Cantor subtype remains nonmeasurability
after inserting the set into the unit interval subtype. -/
private theorem cantorImage_not_measurableInUnitInterval
    {A : Set cantorSet} (hA : ¬ MeasurableSet A) :
    ¬ MeasurableSet
      ((fun x : cantorSet ↦
          (⟨x.1, cantorSet_subset_unitInterval x.2⟩ : unitIntervalSet)) '' A) := by
  intro hImage
  let i : cantorSet → unitIntervalSet := fun x ↦ ⟨x.1, cantorSet_subset_unitInterval x.2⟩
  have hi : Measurable i := by
    fun_prop
  -- Pulling back a measurable image along the canonical inclusion recovers the original set.
  have hpre :
      i ⁻¹' (i '' A) = A := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := by
        apply Subtype.ext
        simpa [i] using congrArg Subtype.val hxy
      simpa [hyx] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hA_meas : MeasurableSet A := by
    have hpre_meas : MeasurableSet (i ⁻¹' (i '' A)) := hi hImage
    rw [hpre] at hpre_meas
    exact hpre_meas
  exact hA hA_meas

-- Proof sketch: choose a non-Borel subset of a closed null subset of `[0,1]`, take its indicator
-- function, note that it vanishes almost everywhere on `[0,1]` and hence is Riemann integrable,
-- but its restriction to `[0,1]` cannot be Borel measurable because the level set `{1}` recovers
-- the chosen non-Borel subset.
/-- There exists a function on `[0,1]` that is Riemann integrable but whose restriction to the
interval subtype is not Borel measurable. -/
theorem exists_riemannIntegrable_unitInterval_not_borelMeasurable :
    ∃ f : ℝ → ℝ,
      RiemannIntegrableOnUnitInterval f ∧
      ¬ Measurable (f ∘ Subtype.val : unitIntervalSet → ℝ) := by
  classical
  obtain ⟨A, hA⟩ := exists_nonmeasurableSet_cantorSet
  let i : cantorSet → unitIntervalSet := fun x ↦ ⟨x.1, cantorSet_subset_unitInterval x.2⟩
  let B : Set unitIntervalSet := i '' A
  let T : Set ℝ := Subtype.val '' A
  let f : ℝ → ℝ := T.indicator (fun _ ↦ (1 : ℝ))
  have hB_not_meas : ¬ MeasurableSet B := by
    simpa [B, i] using cantorImage_not_measurableInUnitInterval hA
  have hT_subset : T ⊆ cantorSet := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hclosure_subset : closure T ⊆ cantorSet := by
    exact isClosed_cantorSet.closure_subset_iff.2 hT_subset
  have hclosure_zero : volume (closure T) = 0 := by
    exact measure_mono_null hclosure_subset volume_cantorSet_zero
  refine ⟨f, riemannIntegrableOnUnitInterval_indicator_of_closure_null hclosure_zero, ?_⟩
  intro hf_meas
  -- The `{1}`-level set of the restricted indicator recovers the transported Cantor subset.
  have hB_level :
      (f ∘ Subtype.val : unitIntervalSet → ℝ) ⁻¹' ({1} : Set ℝ) = B := by
    ext x
    constructor
    · intro hx
      have hxT : x.1 ∈ T := by
        by_contra hxT
        simp [f, Set.indicator_of_notMem, hxT] at hx
      rcases hxT with ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, rfl⟩
      have hyT : y.1 ∈ T := ⟨y, hy, rfl⟩
      simp [i, f, hyT]
  have hB_meas : MeasurableSet B := by
    simpa [hB_level] using hf_meas (MeasurableSet.singleton (1 : ℝ))
  exact hB_not_meas hB_meas
