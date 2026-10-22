/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

-- Route correction: the imported `Theorem_4_23` item is currently broken in this workspace, so
-- this file carries the minimal one-dimensional box API it needs locally.
/-- The coordinatewise strict inequality needed to build the one-dimensional box attached to
`[a, b]`. -/
private theorem realIntervalBox_lower_lt_upper (a b : ℝ) (hab : a < b) :
    ∀ i : Fin 1, (![a] : Fin 1 → ℝ) i < (![b] : Fin 1 → ℝ) i := by
  -- `Fin 1` has a single coordinate, so the componentwise inequality is just `hab`.
  intro i
  fin_cases i
  simpa using hab

/-- The one-dimensional `Box` whose closed hull is the interval `[a, b]`. -/
def realIntervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  Box.mk ![a] ![b] (realIntervalBox_lower_lt_upper a b hab)

/-- Riemann integrability on `[0,1]`, encoded via the canonical one-dimensional box model. -/
abbrev RiemannIntegrableOnUnitInterval (f : ℝ → ℝ) : Prop :=
  Integrable (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul

local notation "unitIntervalBox" => realIntervalBox 0 1 zero_lt_one
local notation "unitIntervalBoxSet" => Box.Icc unitIntervalBox
/-- The distortion parameter of the canonical one-dimensional box for `[0,1]`. -/
private noncomputable abbrev unitIntervalBoxDistortion : NNReal :=
  (realIntervalBox 0 1 zero_lt_one).distortion

-- Proof sketch: use the chapter's canonical notion `RiemannIntegrableOnUnitInterval`. For the
-- forward direction, use the classical criterion that a bounded Riemann integrable function is
-- a.e. continuous on `[0,1]`. For the reverse direction, apply
-- `BoxIntegral.integrable_of_bounded_and_ae_continuous` to the lifted function `fun x ↦ f (x 0)`
-- and transport the boundedness and a.e.-continuity hypotheses from `[0,1]` to the canonical
-- one-dimensional box model.
private theorem exists_norm_bound_on_unitInterval {f : ℝ → ℝ}
    (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C := by
  rcases hb.exists_norm_le with ⟨C, hC⟩
  exact ⟨C, fun x hx ↦ hC (f x) (Set.mem_image_of_mem f hx)⟩

/-- Helper for Exercise 4.3.1: a uniform norm bound on `f` over `[0,1]` transports to the
corresponding bound on the lifted function `y ↦ f (y 0)` over the one-dimensional box model. -/
private lemma liftedNormBoundOnRealIntervalBox {f : ℝ → ℝ}
    (hb : ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C) :
    ∃ C : ℝ, ∀ y ∈ unitIntervalBoxSet, ‖f (y 0)‖ ≤ C := by
  rcases hb with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro y hy
  -- A point of the box model has its unique coordinate in `[0,1]`.
  apply hC (y 0)
  rw [Box.Icc_def] at hy
  simpa [realIntervalBox, Set.mem_Icc, Pi.le_def] using hy

/-- Helper for Exercise 4.3.1: `MeasurableEquiv.funUnique (Fin 1) ℝ` sends the one-dimensional
box model for `[0,1]` onto the interval `[0,1]`. -/
private lemma funUnique_image_unitIntervalBox :
    (MeasurableEquiv.funUnique (Fin 1) ℝ) '' unitIntervalBoxSet = unitIntervalSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Evaluating the unique coordinate converts the box membership conditions into interval ones.
    rw [Box.Icc_def] at hy
    simpa [realIntervalBox, Set.mem_Icc, Pi.le_def] using hy
  · intro hx
    refine ⟨fun _ ↦ x, ?_, by simp⟩
    -- The constant `Fin 1 → ℝ` function with value `x` lies in the box exactly when `x ∈ [0,1]`.
    rw [Box.Icc_def]
    simpa [realIntervalBox, Set.mem_Icc, Pi.le_def] using hx

/-- Helper for Exercise 4.3.1: continuity of the lifted function on the one-dimensional box model
is equivalent to continuity of the original function on `[0,1]` at the transported point. -/
private lemma continuousWithinAt_funUnique_iff {f : ℝ → ℝ} {y : Fin 1 → ℝ}
    (hy : y ∈ unitIntervalBoxSet) :
    ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y ↔
      ContinuousWithinAt f unitIntervalSet (y 0) := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hmem : ∀ z : Fin 1 → ℝ, z ∈ unitIntervalBoxSet ↔ e z ∈ unitIntervalSet := by
    intro z
    -- The homeomorphism `e` is evaluation at the unique coordinate, so the set conditions match.
    rw [Box.Icc_def]
    simp [e, realIntervalBox, Set.mem_Icc, Pi.le_def]
  let eSub : unitIntervalBoxSet ≃ₜ unitIntervalSet := e.subtype hmem
  have hy' : y 0 ∈ unitIntervalSet := by
    rw [Box.Icc_def] at hy
    simpa [realIntervalBox, Set.mem_Icc, Pi.le_def] using hy
  have heSub : eSub ⟨y, hy⟩ = ⟨y 0, hy'⟩ := by
    rfl
  -- Pass to the subtype restrictions so continuity is compared across a homeomorphism.
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

/-- Helper for Exercise 4.3.1: almost-everywhere continuity on `[0,1]` is equivalent to
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
            simpa using
              (e.restrict_map volume unitIntervalSet).symm
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
    -- Transport the pointwise continuity statement through the measurable equivalence.
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
    -- Pull the interval continuity statement back to the box side.
    filter_upwards [hbox, hpull] with y hy hyc
    exact (continuousWithinAt_funUnique_iff (f := f) hy).2 hyc

/-- Helper for Exercise 4.3.1: retagging a partition boxwise keeps every new tag in the ambient
unit box. -/
private lemma retaggedWith_tag_mem_Icc
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) :
    ∀ J : Box (Fin 1), (if J ∈ π.boxes then τ J else π.tag J) ∈ Box.Icc unitIntervalBox := by
  intro J
  by_cases hJ : J ∈ π.boxes
  · -- On boxes of the partition, transport the new tag from `J` to the ambient box.
    simpa [hJ] using Box.le_iff_Icc.1 (π.le_of_mem' J hJ) (hτ J hJ)
  · -- Off the partition, keep the original tag.
    simpa [hJ] using π.tag_mem_Icc J

/-- Helper for Exercise 4.3.1: retag a tagged partition without changing its underlying
prepartition. -/
private def retaggedWith
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) :
    TaggedPrepartition unitIntervalBox :=
  { toPrepartition := π.toPrepartition
    tag := fun J ↦ if J ∈ π.boxes then τ J else π.tag J
    tag_mem_Icc := retaggedWith_tag_mem_Icc π τ hτ }

/-- Helper for Exercise 4.3.1: on boxes of the underlying partition, `retaggedWith` uses the new
prescribed tag. -/
private lemma retaggedWith_tag_of_mem
    [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition unitIntervalBox)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J)
    {J : Box (Fin 1)} (hJ : J ∈ π) :
    (retaggedWith π τ hτ).tag J = τ J := by
  -- On partition boxes, the defining `if` selects the replacement tag.
  simp [retaggedWith, hJ]

/-- Helper for Exercise 4.3.1: if a tagged partition is subordinate to the constant radius `r / 2`,
then any boxwise retagging stays in the Riemann base set for the doubled radius `r`. -/
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

/-- Helper for Exercise 4.3.1: one common fine Riemann partition controls the integral sums from
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
      simpa [π₁] using retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf τ₁ hτ₁
    have hπ₂_const :
        IntegrationParams.Riemann.MemBaseSet unitIntervalBox unitIntervalBoxDistortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) π₂ := by
      -- The same transport argument applies to the second retagging.
      simpa [π₂] using retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf τ₂ hτ₂
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

/-- Helper for Exercise 4.3.1: a point with positive oscillation inside `unitIntervalBoxSet`
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

/-- Helper for Exercise 4.3.1: the union of all partition-box boundaries, together with the outer
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

/-- Helper for Exercise 4.3.1: the strict low-oscillation locus on the unit box is open. -/
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

/-- Helper for Exercise 4.3.1: the fixed-threshold high-oscillation set on the unit box is
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

/-- Helper for Exercise 4.3.1: the fixed-threshold bad set records where the oscillation of `g`
on the unit box is at least `η`. -/
private def highOscillationSet (g : (Fin 1 → ℝ) → ℝ) (η : ℝ) : Set (Fin 1 → ℝ) :=
  {y | y ∈ unitIntervalBoxSet ∧ ENNReal.ofReal η ≤ oscillationWithin g unitIntervalBoxSet y}

/-- Helper for Exercise 4.3.1: if a bad point lies in the interior of a box, then that box admits
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

/-- Helper for Exercise 4.3.1: for any oscillation threshold `η > 0` and target volume tolerance
`δ > 0`, one can choose a common fine tagged partition whose boxes meeting the threshold bad set
cover that bad set up to the null boundary exceptional set and whose total volume is at most `δ`. -/
private lemma existsFilteredPartition_covering_highOscillation {g : (Fin 1 → ℝ) → ℝ}
    (hg : Integrable unitIntervalBox IntegrationParams.Riemann g volume.toBoxAdditive.toSMul)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ π : TaggedPrepartition unitIntervalBox,
      π.IsPartition ∧
        highOscillationSet g η ⊆
          (π.filter fun J => (highOscillationSet g η ∩ Box.Ioo J).Nonempty).iUnion ∪
            ((⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪
              (unitIntervalBoxSet \ Box.Ioo unitIntervalBox)) ∧
        volume.real
            (π.filter fun J => (highOscillationSet g η ∩ Box.Ioo J).Nonempty).iUnion ≤ δ := by
  classical
  -- Route correction: keep the cover step and the retagging-volume estimate separate. We first
  -- pick one common fine partition, then filter the boxes meeting the bad set in their interior.
  obtain ⟨π, hπp, hπmem, hretag⟩ :=
    integralSum_twoRetaggings_le_of_riemannIntegrable
      (g := g) hg (mul_pos (half_pos hη) hδ)
  have hπhen : π.IsHenstock := hπmem.isHenstock rfl
  let boundary : Set (Fin 1 → ℝ) :=
    (⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪ (unitIntervalBoxSet \ Box.Ioo unitIntervalBox)
  let πBad : TaggedPrepartition unitIntervalBox :=
    π.filter fun J => (highOscillationSet g η ∩ Box.Ioo J).Nonempty
  have hcover :
      highOscillationSet g η ⊆ πBad.iUnion ∪ boundary := by
    -- Every bad point is either on the isolated boundary exceptional set or lies in the interior
    -- of its unique partition box, hence in the filtered union.
    intro x hx
    by_cases hxBoundary : x ∈ boundary
    · exact Or.inr hxBoundary
    · have hxIooI : x ∈ Box.Ioo unitIntervalBox := by
        have hxIcc : x ∈ unitIntervalBoxSet := hx.1
        by_contra hxNotIooI
        exact hxBoundary (Or.inr ⟨hxIcc, hxNotIooI⟩)
      have hxI : x ∈ unitIntervalBox := (realIntervalBox 0 1 zero_lt_one).Ioo_subset_coe hxIooI
      have hπp' : π.toPrepartition.IsPartition := hπp
      rcases ExistsUnique.exists (hπp'.existsUnique hxI) with ⟨J, hJπ, hxJ⟩
      have hxIooJ : x ∈ Box.Ioo J := by
        have hxIccJ : x ∈ Box.Icc J := Box.coe_subset_Icc hxJ
        by_contra hxNotIooJ
        apply hxBoundary
        left
        refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨hJπ, ?_⟩⟩
        exact ⟨hxIccJ, hxNotIooJ⟩
      have hJbad : J ∈ πBad := by
        exact π.mem_filter.2 ⟨hJπ, ⟨x, ⟨hx, hxIooJ⟩⟩⟩
      exact Or.inl (πBad.subset_iUnion hJbad hxJ)
  have hwitness :
      ∀ J ∈ πBad, ∃ u v, u ∈ Box.Icc J ∧ v ∈ Box.Icc J ∧ η / 2 ≤ g u - g v := by
    -- On every filtered box, use the bad point inside that box to obtain a large oscillation pair.
    intro J hJbad
    rcases (π.mem_filter.1 hJbad).2 with ⟨x, hxBad, hxIooJ⟩
    rcases existsOrderedPairInBox_of_mem_highOscillationSet (g := g) hη ⟨hxBad, hxIooJ⟩ with
      ⟨u, hu, v, hv, hgap⟩
    exact ⟨u, v, hu, hv, hgap⟩
  choose u₀ v₀ hu₀ hv₀ hgap using hwitness
  let τHi : Box (Fin 1) → Fin 1 → ℝ := fun J ↦ if hJ : J ∈ πBad then u₀ J hJ else π.tag J
  let τLo : Box (Fin 1) → Fin 1 → ℝ := fun J ↦ if hJ : J ∈ πBad then v₀ J hJ else π.tag J
  have hτHi_box : ∀ J ∈ π, τHi J ∈ Box.Icc J := by
    -- On filtered boxes we use the selected high-value witness; elsewhere we keep the old tag.
    intro J hJπ
    by_cases hJbad : J ∈ πBad
    · simpa [τHi, hJbad] using hu₀ J hJbad
    · simpa [τHi, hJbad] using hπhen J hJπ
  have hτLo_box : ∀ J ∈ π, τLo J ∈ Box.Icc J := by
    -- The second retagging uses the selected low-value witness on filtered boxes.
    intro J hJπ
    by_cases hJbad : J ∈ πBad
    · simpa [τLo, hJbad] using hv₀ J hJbad
    · simpa [τLo, hJbad] using hπhen J hJπ
  have hgap_selected : ∀ J ∈ πBad, η / 2 ≤ g (τHi J) - g (τLo J) := by
    -- The chosen witness pair already has the correct orientation, so the filtered gap is direct.
    intro J hJbad
    simpa [τHi, τLo, hJbad] using hgap J hJbad
  let term : Box (Fin 1) → ℝ :=
    fun J ↦ volume.toBoxAdditive.toSMul J (g (τHi J) - g (τLo J))
  have hterm_nonneg : ∀ J ∈ π.boxes, 0 ≤ term J := by
    -- Every filtered box contributes a nonnegative amount, and boxes outside the filter
    -- contribute `0` because both retaggings equal the original tag there.
    intro J hJπ
    by_cases hJbad : J ∈ πBad
    · have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
        rw [MeasureTheory.Measure.toBoxAdditive_apply]
        exact measureReal_nonneg
      have hgap_nonneg : 0 ≤ g (τHi J) - g (τLo J) := by
        exact le_trans (le_of_lt (half_pos hη)) (hgap_selected J hJbad)
      simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul] using
        mul_nonneg hvol_nonneg hgap_nonneg
    · have hJπ' : J ∈ π := hJπ
      simp [term, τHi, τLo, hJbad]
  have hmeasure_selected :
      volume.real πBad.iUnion = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
    -- The volume of the filtered union is the sum of the filtered box volumes.
    calc
      volume.real πBad.iUnion = ∑ J ∈ πBad.boxes, volume.real (J : Set (Fin 1 → ℝ)) := by
        simpa using πBad.toPrepartition.measure_iUnion_toReal (μ := volume)
      _ = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
        refine Finset.sum_congr rfl ?_
        intro J hJ
        simp [MeasureTheory.Measure.toBoxAdditive_apply]
  have hterm_lower :
      ∀ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J ≤ term J := by
    -- Each filtered box contributes at least `(η / 2) * volume(J)`.
    intro J hJ
    have hJbad : J ∈ πBad := hJ
    have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
      rw [MeasureTheory.Measure.toBoxAdditive_apply]
      exact measureReal_nonneg
    have hmul := mul_le_mul_of_nonneg_left (hgap_selected J hJbad) hvol_nonneg
    simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hsum_selected_le_all :
      ∑ J ∈ πBad.boxes, term J ≤ ∑ J ∈ π.boxes, term J := by
    -- The filtered sum is a sub-sum of the full partition sum, and the omitted terms are
    -- nonnegative.
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun J hJ ↦ (π.mem_filter.1 hJ).1)
      (fun J hJπ hJnot ↦ hterm_nonneg J hJπ)
  have hsum_lower :
      (η / 2) * volume.real πBad.iUnion ≤ ∑ J ∈ π.boxes, term J := by
    -- Translate the filtered-volume objective into the retagging sum lower bound.
    calc
      (η / 2) * volume.real πBad.iUnion =
          ∑ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J := by
            rw [hmeasure_selected, Finset.mul_sum]
      _ ≤ ∑ J ∈ πBad.boxes, term J := Finset.sum_le_sum hterm_lower
      _ ≤ ∑ J ∈ π.boxes, term J := hsum_selected_le_all
  have hsum_bound :
      ‖∑ J ∈ π.boxes, term J‖ ≤ (η / 2) * δ := by
    -- The common fine partition controls both retaggings simultaneously.
    simpa [term] using hretag τHi τLo hτHi_box hτLo_box
  have hsum_nonneg : 0 ≤ ∑ J ∈ π.boxes, term J := Finset.sum_nonneg hterm_nonneg
  rw [Real.norm_of_nonneg hsum_nonneg] at hsum_bound
  have hvolume_le : volume.real πBad.iUnion ≤ δ := by
    have hscaled : (η / 2) * volume.real πBad.iUnion ≤ (η / 2) * δ :=
      le_trans hsum_lower hsum_bound
    have hvol_nonneg : 0 ≤ volume.real πBad.iUnion := measureReal_nonneg
    nlinarith
  exact ⟨π, hπp, by simpa [πBad, boundary] using hcover, by simpa [πBad] using hvolume_le⟩

/-- Helper for Exercise 4.3.1: for each fixed threshold `η > 0`, the set where the oscillation of
an integrable box-side function is at least `η` has zero restricted volume. -/
private lemma measureHighOscillationSet_eq_zero_of_riemannIntegrable
    {g : (Fin 1 → ℝ) → ℝ}
    (hg : Integrable unitIntervalBox IntegrationParams.Riemann g volume.toBoxAdditive.toSMul) :
    ∀ η > 0, (volume.restrict unitIntervalBoxSet) (highOscillationSet g η) = 0 := by
  intro η hη
  have hBadCompact : IsCompact (highOscillationSet g η) := by
    simpa [highOscillationSet] using isCompact_highOscillationSet (g := g) (η := η)
  have hBad_lt_top :
      (volume.restrict unitIntervalBoxSet) (highOscillationSet g η) < ⊤ :=
    hBadCompact.measure_lt_top (μ := volume.restrict unitIntervalBoxSet)
  have hBad_ne_top :
      (volume.restrict unitIntervalBoxSet) (highOscillationSet g η) ≠ ⊤ :=
    hBad_lt_top.ne
  by_contra hBad
  have hBadRealPos : 0 < (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) := by
    have hBadRealNe :
        (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) ≠ 0 := by
      exact (MeasureTheory.measureReal_ne_zero_iff hBad_ne_top).2 hBad
    exact lt_of_le_of_ne ENNReal.toReal_nonneg hBadRealNe.symm
  let δ : ℝ := (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact half_pos hBadRealPos
  obtain ⟨π, _, hcover, hvol⟩ :=
    existsFilteredPartition_covering_highOscillation (g := g) hg hη hδ
  let p : Box (Fin 1) → Prop := fun J => (highOscillationSet g η ∩ Box.Ioo J).Nonempty
  let E :=
    ((⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪ (unitIntervalBoxSet \ Box.Ioo unitIntervalBox))
  have hboundaryZero : (volume.restrict unitIntervalBoxSet) E = 0 := by
    simpa [E] using measure_partitionBoundary_eq_zero π
  have hfiltered_subset : (π.filter p).iUnion ⊆ unitIntervalBoxSet := by
    intro y hy
    exact Box.coe_subset_Icc ((π.filter p).iUnion_subset hy)
  have hfiltered_real :
      (volume.restrict unitIntervalBoxSet).real (π.filter p).iUnion =
        volume.real (π.filter p).iUnion := by
    -- The filtered union lies in the ambient closed box, so restriction does not change its volume.
    simp [Measure.real, Measure.restrict_eq_self volume hfiltered_subset]
  have hboundary_real_zero : (volume.restrict unitIntervalBoxSet).real E = 0 := by
    simp [Measure.real, hboundaryZero]
  have hunion_subset : (π.filter p).iUnion ∪ E ⊆ unitIntervalBoxSet := by
    intro y hy
    rcases hy with hyFiltered | hyExceptional
    · exact hfiltered_subset hyFiltered
    · rcases hyExceptional with hyBoundary | hyAmbient
      · rcases Set.mem_iUnion.1 hyBoundary with ⟨J, hyBoundary⟩
        rcases Set.mem_iUnion.1 hyBoundary with ⟨hJ, hyBoundaryJ⟩
        exact Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hyBoundaryJ.1
      · exact hyAmbient.1
  have hunion_lt_top : (volume.restrict unitIntervalBoxSet) ((π.filter p).iUnion ∪ E) < ⊤ := by
    have hbox_lt_top : volume unitIntervalBoxSet < ⊤ :=
      (realIntervalBox 0 1 zero_lt_one).isCompact_Icc.measure_lt_top (μ := volume)
    calc
      (volume.restrict unitIntervalBoxSet) ((π.filter p).iUnion ∪ E) ≤
          (volume.restrict unitIntervalBoxSet) unitIntervalBoxSet :=
            measure_mono hunion_subset
      _ = volume unitIntervalBoxSet := by
            rw [Measure.restrict_apply (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc]
            simp
      _ < ⊤ := hbox_lt_top
  have hunion_ne_top : (volume.restrict unitIntervalBoxSet) ((π.filter p).iUnion ∪ E) ≠ ⊤ :=
    hunion_lt_top.ne
  have hBad_le_half :
      (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) ≤
        (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) / 2 := by
    -- The cover plus the null boundary set forces the bad-set volume below an arbitrary half.
    calc
      (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) ≤
          (volume.restrict unitIntervalBoxSet).real ((π.filter p).iUnion ∪ E) :=
            MeasureTheory.measureReal_mono hcover hunion_ne_top
      _ ≤ (volume.restrict unitIntervalBoxSet).real (π.filter p).iUnion +
            (volume.restrict unitIntervalBoxSet).real E :=
            MeasureTheory.measureReal_union_le _ _
      _ = volume.real (π.filter p).iUnion + 0 := by rw [hfiltered_real, hboundary_real_zero]
      _ ≤ δ + 0 := add_le_add hvol le_rfl
      _ = (volume.restrict unitIntervalBoxSet).real (highOscillationSet g η) / 2 := by
            simp [δ]
  linarith

/-- Helper for Exercise 4.3.1: Riemann integrability on the unit box implies almost-everywhere
continuity of the lifted function on that box. -/
private lemma aeContinuousWithinAtLift_of_riemannIntegrable {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f) :
    ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
      ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y := by
  let g : (Fin 1 → ℝ) → ℝ := fun z ↦ f (z 0)
  have hmem : ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet), y ∈ unitIntervalBoxSet :=
    self_mem_ae_restrict (realIntervalBox 0 1 zero_lt_one).measurableSet_Icc
  have hthreshold :
      ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
        y ∉ highOscillationSet g (1 / (n + 1 : ℝ)) := by
    intro n
    -- Each reciprocal threshold bad set has measure zero by the fixed-threshold lemma.
    exact MeasureTheory.compl_mem_ae_iff.2 <|
      measureHighOscillationSet_eq_zero_of_riemannIntegrable (g := g) hf
        (1 / (n + 1 : ℝ)) (by positivity)
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
        simp [ω, htop]
      exact hyAll 0 hyBad
    · have htoRealPos :
          0 < ω.toReal :=
        ENNReal.toReal_pos hωne htop
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt htoRealPos
      have hyBad : y ∈ highOscillationSet g (1 / (n + 1 : ℝ)) := by
        refine ⟨hyBox, ?_⟩
        simpa [ω] using
          (le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop).2 hn))
      exact hyAll n hyBad
  -- Vanishing oscillation is the pointwise criterion for continuity within the box.
  simpa [g] using (OscillationWithin.eq_zero_iff_continuousWithinAt g hyBox).1 hoscZero

/-- Exercise 4.3.1: for a bounded function on `[0,1]`, Riemann integrability on `[0,1]` in the
chapter's canonical one-dimensional box model is equivalent to `volume`-almost everywhere
continuity on `[0,1]`. -/
theorem riemannIntegrableOn_unitInterval_iff_aeContinuousWithinAt
    {f : ℝ → ℝ} (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    RiemannIntegrableOnUnitInterval f ↔
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x := by
  constructor
  · intro hf
    have hboxc :
        ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
          ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y :=
      aeContinuousWithinAtLift_of_riemannIntegrable hf
    -- Once the box-side statement is available, transport it back to `[0,1]`.
    exact (aeContinuousWithinAtFunUniqueIff (f := f)).1 hboxc
  · intro hc
    have hb' : ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C :=
      exists_norm_bound_on_unitInterval hb
    have hboxb : ∃ C : ℝ, ∀ y ∈ unitIntervalBoxSet, ‖f (y 0)‖ ≤ C :=
      liftedNormBoundOnRealIntervalBox hb'
    have hboxc :
        ∀ᵐ y ∂(volume.restrict unitIntervalBoxSet),
          ContinuousWithinAt (fun z : Fin 1 → ℝ ↦ f (z 0)) unitIntervalBoxSet y :=
      (aeContinuousWithinAtFunUniqueIff (f := f)).2 hc
    -- Apply the box-integral criterion to the lifted function on the canonical one-dimensional box.
    simpa [RiemannIntegrableOnUnitInterval] using
      (BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt
        IntegrationParams.Riemann hboxb volume hboxc)
