/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral

/-- Helper for Example 4.24: in the one-dimensional box model, the coordinatewise strict
inequality is exactly the scalar inequality `a < b`. -/
private theorem realIntervalBox_lower_lt_upper (a b : ℝ) (hab : a < b) :
    ∀ i : Fin 1, (![a] : Fin 1 → ℝ) i < (![b] : Fin 1 → ℝ) i := by
  -- `Fin 1` has one coordinate, so there is only one inequality to check.
  intro i
  fin_cases i
  simpa using hab

/-- Helper for Example 4.24: the one-dimensional box whose closed hull is `[a, b]`. -/
def realIntervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  Box.mk ![a] ![b] (realIntervalBox_lower_lt_upper a b hab)

/-- Helper for Example 4.24: the chapter's canonical notion of Riemann integrability on `[0,1]`
in the one-dimensional box model. -/
abbrev RiemannIntegrableOnUnitInterval (f : ℝ → ℝ) : Prop :=
  Integrable (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul

/-- The Dirichlet function on `ℝ`, viewed as the indicator of the rational numbers. -/
noncomputable def dirichletFunction : ℝ → ℝ :=
  (Set.range ((↑) : ℚ → ℝ)).indicator 1

private theorem dirichletFunction_ae_eq_zero_on_unitInterval :
    dirichletFunction =ᵐ[volume.restrict (Set.Icc 0 1)] 0 := by
  have h_countable : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h_zero :
      (volume.restrict (Set.Icc 0 1)) (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    h_countable.measure_zero _
  simpa [dirichletFunction] using
    (indicator_meas_zero h_zero : dirichletFunction =ᵐ[volume.restrict (Set.Icc 0 1)] 0)

-- Proof sketch: use that `Set.range ((↑) : ℚ → ℝ)` is countable, hence null for `volume`, so the
-- indicator is integrable on `Set.Icc 0 1` and its set integral vanishes.
/-- For Example 4.24, the Dirichlet function on `[0,1]`, equal to `1` on rational points and `0`
elsewhere, is Lebesgue integrable on `[0,1]` and has integral `0`. -/
theorem dirichletFunction_integrableOn_unitInterval_and_integral_zero :
    IntegrableOn dirichletFunction (Set.Icc 0 1) volume ∧
      ∫ x in Set.Icc 0 1, dirichletFunction x ∂volume = 0 := by
  refine ⟨?_, ?_⟩
  · exact integrableOn_zero.congr_fun_ae dirichletFunction_ae_eq_zero_on_unitInterval.symm
  · calc
      ∫ x in Set.Icc 0 1, dirichletFunction x ∂volume =
          ∫ x in Set.Icc 0 1, (0 : ℝ) ∂volume :=
        integral_congr_ae dirichletFunction_ae_eq_zero_on_unitInterval
      _ = 0 := by simp

/-- Helper for Example 4.24: the Dirichlet function takes the value `1` at every rational point. -/
private lemma dirichletFunction_eq_one_of_rational {x : ℝ}
    (hx : x ∈ Set.range ((↑) : ℚ → ℝ)) :
    dirichletFunction x = 1 := by
  -- At rational points the indicator of the rational range is equal to its marked value.
  simp [dirichletFunction, hx]

/-- Helper for Example 4.24: every one-dimensional box contains a rational point of its closed
hull. -/
private lemma existsRationalPointInIcc (J : Box (Fin 1)) :
    ∃ x : Fin 1 → ℝ, x ∈ Box.Icc J ∧ (x 0) ∈ Set.range ((↑) : ℚ → ℝ) := by
  -- Choose a rational strictly between the box endpoints and view it as the unique-coordinate tag.
  obtain ⟨q, hqlower, hqupper⟩ := exists_rat_btwn (J.lower_lt_upper 0)
  refine ⟨fun _ ↦ q, ?_, ⟨q, rfl⟩⟩
  refine ⟨?_, ?_⟩ <;> intro i <;> fin_cases i
  · exact hqlower.le
  · exact hqupper.le

/-- Helper for Example 4.24: the Dirichlet function vanishes at every irrational point. -/
private lemma dirichletFunction_eq_zero_of_irrational {x : ℝ}
    (hx : Irrational x) :
    dirichletFunction x = 0 := by
  -- At irrational points the indicator of the rational range vanishes.
  simpa [dirichletFunction, Irrational] using hx

/-- Helper for Example 4.24: every one-dimensional box contains an irrational point of its closed
hull. -/
private lemma existsIrrationalPointInIcc (J : Box (Fin 1)) :
    ∃ x : Fin 1 → ℝ, x ∈ Box.Icc J ∧ Irrational (x 0) := by
  -- Choose an irrational strictly between the box endpoints and use it as the unique coordinate.
  obtain ⟨x, hxirr, hqlower, hqupper⟩ := exists_irrational_btwn (J.lower_lt_upper 0)
  refine ⟨fun _ ↦ x, ?_, hxirr⟩
  refine ⟨?_, ?_⟩ <;> intro i <;> fin_cases i
  · exact hqlower.le
  · exact hqupper.le

/-- Helper for Example 4.24: replacing the tags on the boxes of `π` keeps every tag inside the
ambient box `I` as soon as the new tag for each box lies in that box. -/
private lemma retaggedWith_tag_mem_Icc {I : Box (Fin 1)} [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition I)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J, τ J ∈ Box.Icc J) :
    ∀ J : Box (Fin 1), (if J ∈ π.boxes then τ J else π.tag J) ∈ Box.Icc I := by
  -- On partition boxes, transport membership along `J ≤ I`; elsewhere keep the original tag.
  intro J
  by_cases hJ : J ∈ π.boxes
  · simpa [hJ] using Box.le_iff_Icc.1 (π.le_of_mem' J hJ) (hτ J)
  · simpa [hJ] using π.tag_mem_Icc J

/-- Helper for Example 4.24: retag a tagged partition without changing its underlying
prepartition. -/
private def retaggedWith {I : Box (Fin 1)} [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition I)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J, τ J ∈ Box.Icc J) :
    TaggedPrepartition I :=
  { toPrepartition := π.toPrepartition
    tag := fun J ↦ if J ∈ π.boxes then τ J else π.tag J
    tag_mem_Icc := retaggedWith_tag_mem_Icc π τ hτ }

/-- Helper for Example 4.24: on a box of the partition, `retaggedWith` uses the prescribed new
tag. -/
private lemma retaggedWith_tag_of_mem {I : Box (Fin 1)} [DecidableEq (Box (Fin 1))]
    (π : TaggedPrepartition I)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J, τ J ∈ Box.Icc J) {J : Box (Fin 1)}
    (hJ : J ∈ π.boxes) :
    (retaggedWith π τ hτ).tag J = τ J := by
  -- On boxes of `π`, the defining `if` of `retaggedWith` chooses the replacement tag.
  simp [retaggedWith, hJ]

/-- Helper for Example 4.24: if a tagged partition is subordinate to the constant radius `r / 2`,
then any retagging by points of the same boxes is subordinate to the constant radius `r`. -/
private lemma retaggedWith_memBaseSetRiemannOfConst {I : Box (Fin 1)}
    [DecidableEq (Box (Fin 1))] {c : NNReal}
    (π : TaggedPrepartition I) {r : ℝ} (hr : 0 < r) (hr2 : 0 < r / 2)
    (hπ :
      IntegrationParams.Riemann.MemBaseSet I c (fun _ : Fin 1 → ℝ ↦ ⟨r / 2, hr2⟩) π)
    (τ : Box (Fin 1) → Fin 1 → ℝ) (hτ : ∀ J, τ J ∈ Box.Icc J) :
    IntegrationParams.Riemann.MemBaseSet I c (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩)
      (retaggedWith π τ hτ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The old and new tags both lie in the same box, so every point stays within distance `r`.
    intro J hJ y hy
    rw [retaggedWith_tag_of_mem π τ hτ hJ, Metric.mem_closedBall]
    have hy_old : dist y (π.tag J) ≤ r / 2 := by
      exact Metric.mem_closedBall.1 (hπ.isSubordinate J hJ hy)
    have hnew_old : dist (π.tag J) (τ J) ≤ r / 2 := by
      simpa [dist_comm] using Metric.mem_closedBall.1 (hπ.isSubordinate J hJ (hτ J))
    calc
      dist y (τ J) ≤ dist y (π.tag J) + dist (π.tag J) (τ J) := dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hy_old hnew_old
      _ = r := by ring
  · -- In the Riemann case the new tags remain Henstock because they stay inside their own boxes.
    intro _ J hJ
    simpa [retaggedWith_tag_of_mem π τ hτ hJ] using hτ J
  · -- The Riemann filter has no distortion side condition.
    intro hD
    cases hD
  · -- The Riemann filter has no complementary distortion side condition.
    intro hD
    cases hD

/-- Helper for Example 4.24: if every tag of a partition of `[0,1]` is rational, then the
Dirichlet integral sum is exactly `1`. -/
private lemma integralSum_dirichlet_eq_one_of_rationalTags
    (π : TaggedPrepartition (realIntervalBox 0 1 zero_lt_one)) (hπp : π.IsPartition)
    (hRat : ∀ J ∈ π, (π.tag J 0) ∈ Set.range ((↑) : ℚ → ℝ)) :
    integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul π = 1 := by
  -- Every summand is the box volume, so the sum is the volume of the whole unit box.
  calc
    integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul π =
        ∑ J ∈ π.boxes, volume.toBoxAdditive.toSMul J (1 : ℝ) := by
      unfold integralSum
      refine Finset.sum_congr rfl ?_
      intro J hJ
      have hvalue : dirichletFunction (π.tag J 0) = 1 :=
        dirichletFunction_eq_one_of_rational (hRat J hJ)
      simpa using congrArg (volume.toBoxAdditive.toSMul J) hvalue
    _ = ∑ J ∈ π.toPrepartition.boxes, (volume : Measure (Fin 1 → ℝ)).toBoxAdditive J := by
      simp [BoxAdditiveMap.toSMul_apply]
    _ = (volume : Measure (Fin 1 → ℝ)).toBoxAdditive (realIntervalBox 0 1 zero_lt_one) := by
      simpa using
        ((volume : Measure (Fin 1 → ℝ)).toBoxAdditive.sum_partition_boxes
          (I := realIntervalBox 0 1 zero_lt_one) le_top (π := π.toPrepartition) hπp)
    _ = 1 := by
      simpa [realIntervalBox] using
        (BoxIntegral.Box.volume_apply (I := realIntervalBox 0 1 zero_lt_one))

/-- Helper for Example 4.24: if every tag is irrational, then the Dirichlet integral sum is
exactly `0`. -/
private lemma integralSum_dirichlet_eq_zero_of_irrationalTags
    (π : TaggedPrepartition (realIntervalBox 0 1 zero_lt_one))
    (hIrr : ∀ J ∈ π, Irrational (π.tag J 0)) :
    integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul π = 0 := by
  -- Irrational tags make every summand vanish.
  unfold integralSum
  refine Finset.sum_eq_zero ?_
  intro J hJ
  have hvalue : dirichletFunction (π.tag J 0) = 0 :=
    dirichletFunction_eq_zero_of_irrational (hIrr J hJ)
  simpa using congrArg (volume.toBoxAdditive.toSMul J) hvalue

-- Proof sketch: show that every tagged Riemann partition of the unit box has upper sums `1` and
-- lower sums `0`, using density of rational and irrational points in every subinterval.
/-- Example 4.24: the Dirichlet function on `[0,1]` is not Riemann integrable. -/
theorem dirichletFunction_not_riemannIntegrableOn_unitInterval :
    ¬ RiemannIntegrableOnUnitInterval dirichletFunction := by
  intro hf
  classical
  let I := realIntervalBox 0 1 zero_lt_one
  -- Route correction: use one common fine partition and retag it once by rational points and once
  -- by irrational points; integrability would force the two resulting sums to be close.
  let ε : ℝ := 1 / 4
  have hε : 0 < ε := by
    norm_num [ε]
  let r : ℝ := hf.convergenceR ε I.distortion 0
  have hr : 0 < r := (hf.convergenceR ε I.distortion 0).2
  have hr2 : 0 < r / 2 := half_pos hr
  let rhalf : (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ ↦ ⟨r / 2, hr2⟩
  -- Start from one common fine partition subordinate to the half-radius gauge.
  obtain ⟨π, hπhalf, hπp⟩ :=
    IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann I le_rfl rhalf
  have hconst :
      ∀ x : Fin 1 → ℝ,
        hf.convergenceR ε I.distortion x = hf.convergenceR ε I.distortion 0 := by
    -- For the Riemann filter, the convergence gauge is constant in the tag.
    intro x
    exact hf.convergenceR_cond ε I.distortion rfl x
  -- Choose one rational tag and one irrational tag in each box.
  choose rationalTag hRationalTag_mem hRationalTag using existsRationalPointInIcc
  choose irrationalTag hIrrationalTag_mem hIrrationalTag using existsIrrationalPointInIcc
  let πq : TaggedPrepartition I := retaggedWith π rationalTag hRationalTag_mem
  let πi : TaggedPrepartition I := retaggedWith π irrationalTag hIrrationalTag_mem
  have hπq_mem_const :
      IntegrationParams.Riemann.MemBaseSet I I.distortion (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) πq := by
    -- Retagging inside each box preserves the Riemann base-set condition after doubling the radius.
    simpa [πq] using
      retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf rationalTag hRationalTag_mem
  have hπi_mem_const :
      IntegrationParams.Riemann.MemBaseSet I I.distortion (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) πi := by
    -- The same transport argument applies to the irrational retagging.
    simpa [πi] using
      retaggedWith_memBaseSetRiemannOfConst (π := π) hr hr2 hπhalf irrationalTag
        hIrrationalTag_mem
  have hπq_mem :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR ε I.distortion) πq := by
    -- The full convergence gauge is the same constant radius `r`.
    refine hπq_mem_const.mono (I := I) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
  have hπi_mem :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR ε I.distortion) πi := by
    -- The full convergence gauge is the same constant radius `r`.
    refine hπi_mem_const.mono (I := I) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
  have hπq_partition : πq.IsPartition := by
    -- Retagging does not change the underlying prepartition.
    simpa [πq, retaggedWith] using hπp
  have hπi_partition : πi.IsPartition := by
    -- Retagging does not change the underlying prepartition.
    simpa [πi, retaggedWith] using hπp
  have hπq_rational :
      ∀ J ∈ πq, (πq.tag J 0) ∈ Set.range ((↑) : ℚ → ℝ) := by
    -- On boxes of `π`, the retagged partition uses exactly the chosen rational tags.
    intro J hJ
    simpa [πq, retaggedWith_tag_of_mem (π := π) (τ := rationalTag)
      (hτ := hRationalTag_mem) hJ] using hRationalTag J
  have hπi_irrational :
      ∀ J ∈ πi, Irrational (πi.tag J 0) := by
    -- On boxes of `π`, the retagged partition uses exactly the chosen irrational tags.
    intro J hJ
    simpa [πi, retaggedWith_tag_of_mem (π := π) (τ := irrationalTag)
      (hτ := hIrrationalTag_mem) hJ] using hIrrationalTag J
  have hsum_q :
      integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul πq = 1 := by
    -- Rational tags force every summand to equal the corresponding box volume.
    exact integralSum_dirichlet_eq_one_of_rationalTags πq hπq_partition hπq_rational
  have hsum_i :
      integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul πi = 0 := by
    -- Irrational tags make every summand vanish.
    exact integralSum_dirichlet_eq_zero_of_irrationalTags πi hπi_irrational
  have hdist :
      dist (integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul πq)
        (integralSum (fun x ↦ dirichletFunction (x 0)) volume.toBoxAdditive.toSMul πi) ≤
        ε + ε := by
    -- The two retagged partitions cover the same set, so integrability forces their sums together.
    have hUnion : πq.iUnion = πi.iUnion := by
      simp [πq, πi, retaggedWith]
    exact hf.dist_integralSum_le_of_memBaseSet hε hε hπq_mem hπi_mem hUnion
  have : dist (1 : ℝ) 0 ≤ ε + ε := by
    simpa [hsum_q, hsum_i] using hdist
  norm_num [ε] at this
