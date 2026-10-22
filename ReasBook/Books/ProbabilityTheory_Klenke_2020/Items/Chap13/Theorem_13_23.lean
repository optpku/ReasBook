/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_60
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory MeasureTheory.FiniteMeasure
open scoped Topology

noncomputable section

private theorem isSubProbabilityMeasure_of_mass_le_one (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) : IsSubProbabilityMeasure (μ : Measure ℝ) := by
  refine ⟨?_⟩
  have hmass : (μ.mass : ENNReal) ≤ 1 := by
    exact_mod_cast hμ
  simpa [FiniteMeasure.ennreal_mass] using hmass

private theorem isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) :=
  isDefectiveDistributionFunction_measureDistributionFunction μ
    (isSubProbabilityMeasure_of_mass_le_one μ hμ)

/-- Helper for Theorem 13.23: the Lebesgue--Stieltjes measure of
`measureDistributionFunction μ` recovers the original sub-probability finite measure `μ`. -/
private theorem measureDistributionFunction_measure_eq_self_of_mass_le_one
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    (measureDistributionFunction μ).measure = (μ : Measure ℝ) := by
  let μsub : {ν : Measure ℝ // IsSubProbabilityMeasure ν} :=
    ⟨(μ : Measure ℝ), isSubProbabilityMeasure_of_mass_le_one μ hμ⟩
  exact congrArg Subtype.val
    (subProbabilityMeasureEquivDefectiveDistributionFunction_left_inv μsub)

/-- Helper for Theorem 13.23: evaluating `measureDistributionFunction μ` at `x` gives the
`μ`-mass of the ray `Set.Iic x`. -/
private theorem measureDistributionFunction_apply_eq_mass_Iic
    (μ : FiniteMeasure ℝ) (x : ℝ) :
    measureDistributionFunction μ x = μ (Set.Iic x) := by
  simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using
    (measureDistributionFunction_apply (μ := (μ : Measure ℝ)) x)

/-- Helper for Theorem 13.23: the endpoint value of `measureDistributionFunction μ` is the total
mass `μ.mass`. -/
private theorem measureDistributionFunction_measure_univ_toReal_eq_mass
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    ((measureDistributionFunction μ).measure Set.univ).toReal = μ.mass := by
  rw [measureDistributionFunction_measure_eq_self_of_mass_le_one μ hμ]
  change ENNReal.toReal ((μ : Measure ℝ) Set.univ) = μ Set.univ
  exact ENNReal.coe_toReal (μ Set.univ)

/-- Helper for Theorem 13.23: if `measureDistributionFunction μ` is continuous at `x`, then the
ray `Set.Iic x` is a `μ`-continuity set. -/
private theorem measureFrontier_Iic_eq_zero_of_continuousAt_measureDistributionFunction
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) {x : ℝ}
    (hx : ContinuousAt (measureDistributionFunction μ) x) :
    μ (frontier (Set.Iic x)) = 0 := by
  rw [frontier_Iic]
  rw [FiniteMeasure.null_iff_toMeasure_null]
  rw [← measureDistributionFunction_measure_eq_self_of_mass_le_one μ hμ]
  rw [StieltjesFunction.measure_singleton]
  have hmono := (measureDistributionFunction μ).mono
  -- Proof comment: continuity identifies the left limit with the right-continuous Stieltjes
  -- value, so the singleton jump vanishes.
  have hleftRight :
      Function.leftLim (measureDistributionFunction μ) x =
        Function.rightLim (measureDistributionFunction μ) x :=
    (hmono.continuousAt_iff_leftLim_eq_rightLim).1 hx
  have hleft :
      Function.leftLim (measureDistributionFunction μ) x =
        measureDistributionFunction μ x := by
    simpa [StieltjesFunction.rightLim_eq] using hleftRight
  rw [hleft]
  simp

/-- Helper for Theorem 13.23: weak convergence of the defective distribution functions forces
convergence of the total masses. -/
private theorem massTendsto_of_distributionFunctionWeakConverges
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdf :
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ)) :
    Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
  -- Proof comment: upgrade the endpoint limsup condition in Definition 13.21 to an actual limit,
  -- then rewrite those endpoint values as total masses.
  have htop :=
    tendsto_distribution_function_at_top_value_of_weak_convergence
      (fun n ↦ measureDistributionFunction (μs n))
      (measureDistributionFunction μ) hdf
  have hSeq :
      (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal) =
        fun n ↦ ((μs n).mass : ℝ) := by
    funext n
    exact measureDistributionFunction_measure_univ_toReal_eq_mass (μs n) (hμs n)
  have hLim : ((measureDistributionFunction μ).measure Set.univ).toReal = (μ.mass : ℝ) :=
    measureDistributionFunction_measure_univ_toReal_eq_mass μ hμ
  have hmassReal : Tendsto (fun n ↦ ((μs n).mass : ℝ)) atTop (𝓝 (μ.mass : ℝ)) := by
    rw [← hLim]
    simpa [hSeq] using htop
  exact (NNReal.tendsto_coe).1 hmassReal

/-- Helper for Theorem 13.23: continuity-point convergence of the defective distribution
functions gives convergence of the `Ioc` masses of the underlying finite measures. -/
private theorem tendsto_apply_Ioc_of_distributionFunctionWeakConverges
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdf :
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ))
    {a b : ℝ}
    (ha : ContinuousAt (measureDistributionFunction μ) a)
    (hb : ContinuousAt (measureDistributionFunction μ) b) :
    Tendsto (fun n ↦ μs n (Set.Ioc a b)) atTop (𝓝 (μ (Set.Ioc a b))) := by
  rcases hdf with ⟨_, _, hpointwise, _⟩
  have ha_tendsto :
      Tendsto (fun n ↦ measureDistributionFunction (μs n) a) atTop
        (𝓝 (measureDistributionFunction μ a)) :=
    hpointwise ha
  have hb_tendsto :
      Tendsto (fun n ↦ measureDistributionFunction (μs n) b) atTop
        (𝓝 (measureDistributionFunction μ b)) :=
    hpointwise hb
  -- Proof comment: rewrite the interval masses as Stieltjes increments, so the convergence
  -- follows from subtraction of the endpoint limits.
  have hdiff :
      Tendsto
        (fun n ↦ measureDistributionFunction (μs n) b - measureDistributionFunction (μs n) a)
        atTop
        (𝓝 (measureDistributionFunction μ b - measureDistributionFunction μ a)) :=
    hb_tendsto.sub ha_tendsto
  let νs : ℕ → ENNReal := fun n ↦ (measureDistributionFunction (μs n)).measure (Set.Ioc a b)
  have hEqF :
      (measureDistributionFunction μ).measure (Set.Ioc a b) =
        ENNReal.ofReal (measureDistributionFunction μ b - measureDistributionFunction μ a) := by
    rw [StieltjesFunction.measure_Ioc]
  have hEq :
      ∀ n,
        νs n =
          ENNReal.ofReal
            (measureDistributionFunction (μs n) b - measureDistributionFunction (μs n) a) := by
    intro n
    dsimp [νs]
    rw [StieltjesFunction.measure_Ioc]
  have hIoc :
      Tendsto
        (fun n ↦
          ENNReal.ofReal
            (measureDistributionFunction (μs n) b - measureDistributionFunction (μs n) a))
        atTop
        (𝓝
          (ENNReal.ofReal
            (measureDistributionFunction μ b - measureDistributionFunction μ a))) := by
    simpa using ENNReal.tendsto_ofReal hdiff
  have hνs :
      Tendsto νs atTop (𝓝 ((measureDistributionFunction μ).measure (Set.Ioc a b))) := by
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hEq n).symm) <| by
      simpa [hEqF] using hIoc
  have hνsNNReal :
      Tendsto (fun n ↦ (νs n).toNNReal) atTop
        (𝓝 (((measureDistributionFunction μ).measure (Set.Ioc a b)).toNNReal)) := by
    have hfinite :
        (measureDistributionFunction μ).measure (Set.Ioc a b) ≠ ⊤ := by
      rw [measureDistributionFunction_measure_eq_self_of_mass_le_one μ hμ]
      exact measure_ne_top (μ := (μ : Measure ℝ)) (Set.Ioc a b)
    exact (ENNReal.tendsto_toNNReal hfinite).comp hνs
  have hSeq :
      (fun n ↦ (νs n).toNNReal) = fun n ↦ μs n (Set.Ioc a b) := by
    funext n
    dsimp [νs]
    rw [measureDistributionFunction_measure_eq_self_of_mass_le_one (μs n) (hμs n)]
    rfl
  have hLim :
      ((measureDistributionFunction μ).measure (Set.Ioc a b)).toNNReal = μ (Set.Ioc a b) := by
    rw [measureDistributionFunction_measure_eq_self_of_mass_le_one μ hμ]
    rfl
  rw [← hLim]
  simpa [hSeq] using hνsNNReal

/-- Helper for Theorem 13.23: every open neighborhood contains an `Ioc` interval whose endpoints
are continuity points of `measureDistributionFunction μ`. -/
private theorem existsContinuityIocMemNhdsSubset
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) {G : Set ℝ}
    (hG : IsOpen G) {x : ℝ} (hx : x ∈ G) :
    ∃ a b : ℝ,
      ContinuousAt (measureDistributionFunction μ) a ∧
        ContinuousAt (measureDistributionFunction μ) b ∧
        a < b ∧ Set.Ioc a b ∈ 𝓝 x ∧ Set.Ioc a b ⊆ G := by
  let F := measureDistributionFunction μ
  let C : Set ℝ := {y | ContinuousAt F y}
  have hDefective : IsDefectiveDistributionFunction F :=
    isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one μ hμ
  letI : IsDefectiveDistributionFunction F := hDefective
  have hC_dense : Dense C := by
    let D : Set ℝ := {y | ¬ ContinuousAt F y}
    have hD_countable : D.Countable := F.mono.countable_not_continuousAt
    have hD_dense : Dense Dᶜ := hD_countable.dense_compl ℝ
    simpa [C, D, Set.compl_setOf] using hD_dense
  -- Proof comment: shrink the neighborhood to an open interval around `x`, then pick
  -- continuity points on both sides using density of the continuity set.
  rcases mem_nhds_iff_exists_Ioo_subset.1 (hG.mem_nhds hx) with ⟨l, r, hxIoo, hsubset⟩
  obtain ⟨a, haC, ha_between⟩ := hC_dense.exists_between hxIoo.1
  obtain ⟨b, hbC, hb_between⟩ := hC_dense.exists_between hxIoo.2
  refine ⟨a, b, ?_, ?_, ha_between.2.trans hb_between.1,
    Ioc_mem_nhds ha_between.2 hb_between.1, ?_⟩
  · simpa [C, F] using haC
  · simpa [C, F] using hbC
  · intro y hy
    have hy_left : l < y := lt_trans ha_between.1 hy.1
    have hy_right : y < r := lt_of_le_of_lt hy.2 hb_between.2
    exact hsubset ⟨hy_left, hy_right⟩

/-- Helper for Theorem 13.23: after normalizing a nonzero limiting finite measure, the source
weak convergence hypothesis gives weak convergence of the normalized probability measures. -/
private theorem tendstoNormalize_of_distributionFunctionWeakConverges
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdf :
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ))
    (hμ_ne : μ ≠ 0) :
    Tendsto (fun n ↦ (μs n).normalize) atTop (𝓝 μ.normalize) := by
  let C : Set ℝ := {x | ContinuousAt (measureDistributionFunction μ) x}
  let S : Set (Set ℝ) := {s | ∃ a ∈ C, ∃ b ∈ C, a < b ∧ Set.Ioc a b = s}
  have hmass :=
    massTendsto_of_distributionFunctionWeakConverges μs μ hμ hμs hdf
  have hne :
      ∀ᶠ n in atTop, μs n ≠ 0 :=
    MeasureTheory.FiniteMeasure.eventually_ne_zero_of_tendsto_mass_nonzero
      (μs := μs) (μ := μ) hmass hμ_ne
  have hmassInv :
      Tendsto (fun n ↦ ((μs n).mass)⁻¹) atTop (𝓝 (μ.mass⁻¹)) :=
    Tendsto.inv₀ hmass (μ.mass_nonzero_iff.mpr hμ_ne)
  have hS : IsPiSystem S := by
    simpa [S] using isPiSystem_Ioc_mem C C
  -- Proof comment: the continuity-endpoint `Ioc` intervals form a generating π-system, and both
  -- the normalized sequence and the limit agree there by the interval-mass convergence helper.
  refine hS.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · intro s hs
    rcases hs with ⟨a, _, b, _, _, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a, b, ha, hb, hab, hnhds, hsub⟩ :=
      existsContinuityIocMemNhdsSubset μ hμ hu hx
    refine ⟨Set.Ioc a b, ?_, hnhds, hsub⟩
    exact ⟨a, by simpa [C] using ha, b, by simpa [C] using hb, hab, rfl⟩
  · intro s hs
    rcases hs with ⟨a, haC, b, hbC, _hab, rfl⟩
    have hIoc :
        Tendsto (fun n ↦ μs n (Set.Ioc a b)) atTop (𝓝 (μ (Set.Ioc a b))) :=
      tendsto_apply_Ioc_of_distributionFunctionWeakConverges μs μ hμ hμs hdf
        (by simpa [C] using haC) (by simpa [C] using hbC)
    have hMul :
        Tendsto (fun n ↦ ((μs n).mass)⁻¹ * μs n (Set.Ioc a b)) atTop
          (𝓝 (μ.mass⁻¹ * μ (Set.Ioc a b))) :=
      hmassInv.mul hIoc
    have hEventually :
        ∀ᶠ n in atTop,
          (μs n).normalize (Set.Ioc a b) = ((μs n).mass)⁻¹ * μs n (Set.Ioc a b) := by
      filter_upwards [hne] with n hn
      exact (μs n).normalize_eq_of_nonzero hn (Set.Ioc a b)
    -- Proof comment: after eventual nonzeroness, normalization is just multiplication by the
    -- inverse mass on each fixed interval.
    refine (tendsto_congr' hEventually).2 ?_
    rw [μ.normalize_eq_of_nonzero hμ_ne (Set.Ioc a b)]
    exact hMul

-- Proof sketch: specialize the Portmanteau characterization of weak convergence to the rays
-- `(-∞, x]`, whose boundaries are the singletons `{x}`. This identifies weak convergence of
-- sub-probability finite measures with weak convergence of their associated defective
-- distribution functions in the sense of Definition 13.21; the companion theorem
-- `measureDistributionFunction_weakly_converges_to_iff` unfolds that owner predicate into mass
-- convergence plus pointwise convergence at the continuity points of the limit distribution
-- function.
/-- Theorem 13.23: for sub-probability finite measures on `ℝ`, weak convergence is equivalent to
weak convergence of the corresponding defective distribution functions. The companion theorem
`measureDistributionFunction_weakly_converges_to_iff` unfolds this into convergence of the total
masses and pointwise convergence at every continuity point of the limiting distribution
function. -/
theorem tendsto_iff_measureDistributionFunction_tendsto
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    Tendsto μs atTop (𝓝 μ) ↔
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ) := by
  constructor
  · intro hweak
    have hnullBoundary :
        ∀ A : Set ℝ, MeasurableSet A → μ (frontier A) = 0 →
          Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A)) :=
      ((FiniteMeasure.portmanteau_subprobability_tfae μs μ hμ hμs).1.out 0 5).mp hweak
    have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
      -- Proof comment: the continuity-set clause applied to `Set.univ` gives convergence of the
      -- total masses.
      change Tendsto (fun n ↦ μs n Set.univ) atTop (𝓝 (μ Set.univ))
      exact hnullBoundary Set.univ MeasurableSet.univ (by simp [frontier_univ])
    have hpoint :
        ∀ ⦃x : ℝ⦄, ContinuousAt (measureDistributionFunction μ) x →
          Tendsto (fun n ↦ measureDistributionFunction (μs n) x) atTop
            (𝓝 (measureDistributionFunction μ x)) := by
      intro x hx
      have hIic : Tendsto (fun n ↦ μs n (Set.Iic x)) atTop (𝓝 (μ (Set.Iic x))) :=
        hnullBoundary (Set.Iic x) measurableSet_Iic
          (measureFrontier_Iic_eq_zero_of_continuousAt_measureDistributionFunction μ hμ hx)
      -- Proof comment: rewrite the ray masses as distribution-function values.
      have hIicReal :
          Tendsto (fun n ↦ ((μs n (Set.Iic x) : NNReal) : ℝ)) atTop
            (𝓝 ((μ (Set.Iic x) : NNReal) : ℝ)) :=
        (NNReal.tendsto_coe).2 hIic
      simpa [measureDistributionFunction_apply_eq_mass_Iic] using hIicReal
    refine ⟨?_, ?_, hpoint, ?_⟩
    · exact isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one μ hμ
    · intro n
      exact
        isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one
          (μs n) (hμs n)
    have hmassReal : Tendsto (fun n ↦ ((μs n).mass : ℝ)) atTop (𝓝 (μ.mass : ℝ)) :=
      (NNReal.tendsto_coe).2 hmass
    have hSeq :
        (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal) =
          fun n ↦ ((μs n).mass : ℝ) := by
      funext n
      exact measureDistributionFunction_measure_univ_toReal_eq_mass (μs n) (hμs n)
    have hLim : ((measureDistributionFunction μ).measure Set.univ).toReal = (μ.mass : ℝ) :=
      measureDistributionFunction_measure_univ_toReal_eq_mass μ hμ
    have hmassTop :
        Tendsto (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal)
          atTop (𝓝 (((measureDistributionFunction μ).measure Set.univ).toReal)) := by
      -- Proof comment: the endpoint value of the defective distribution function is exactly the
      -- total mass of the underlying finite measure.
      rw [hLim]
      simpa [hSeq] using hmassReal
    simp [hmassTop.limsup_eq]
  · intro hdf
    have hmass :=
      massTendsto_of_distributionFunctionWeakConverges μs μ hμ hμs hdf
    by_cases hμ_zero : μ = 0
    · -- Proof comment: if the limit mass is zero, mass convergence already forces weak
      -- convergence to the zero finite measure.
      simpa [hμ_zero] using
        (FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa [hμ_zero] using hmass))
    · -- Route correction: replace the earlier bounded-Lipschitz partition attempt by the
      -- normalized probability/Ioc π-system route suggested by the source proof structure.
      have hnorm :=
        tendstoNormalize_of_distributionFunctionWeakConverges μs μ hμ hμs hdf hμ_zero
      exact (FiniteMeasure.tendsto_normalize_iff_tendsto hμ_zero).mp ⟨hnorm, hmass⟩

-- Proof sketch: for the associated defective distribution functions, Definition 13.21 records
-- continuity-point convergence together with the endpoint limsup inequality; the endpoint values
-- are exactly the total masses by `sSup_range_eq_measure_univ_toReal`, and the auxiliary theorem
-- `tendsto_distribution_function_at_top_value_of_weak_convergence` upgrades the limsup condition
-- to actual convergence of the endpoint values, hence of the masses.
/-- For sub-probability finite measures on `ℝ`, weak convergence of the associated defective
distribution functions is exactly convergence of the total masses together with pointwise
convergence at every continuity point of the limiting distribution function. -/
theorem measureDistributionFunction_weakly_converges_to_iff
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    distribution_function_weakly_converges_to
      (fun n ↦ measureDistributionFunction (μs n))
      (measureDistributionFunction μ) ↔
      Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) ∧
        ∀ ⦃x : ℝ⦄, ContinuousAt (measureDistributionFunction μ) x →
          Tendsto (fun n ↦ measureDistributionFunction (μs n) x) atTop
            (𝓝 (measureDistributionFunction μ x)) := by
  constructor
  · intro hdf
    have htop :=
      tendsto_distribution_function_at_top_value_of_weak_convergence
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ) hdf
    refine ⟨?_, hdf.2.2.1⟩
    -- Proof comment: Definition 13.21 already contains the continuity-point convergence, so only
    -- the endpoint condition has to be upgraded to actual mass convergence.
    have hSeq :
        (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal) =
          fun n ↦ ((μs n).mass : ℝ) := by
      funext n
      exact measureDistributionFunction_measure_univ_toReal_eq_mass (μs n) (hμs n)
    have hLim : ((measureDistributionFunction μ).measure Set.univ).toReal = (μ.mass : ℝ) :=
      measureDistributionFunction_measure_univ_toReal_eq_mass μ hμ
    have hmassReal : Tendsto (fun n ↦ ((μs n).mass : ℝ)) atTop (𝓝 (μ.mass : ℝ)) := by
      rw [← hLim]
      simpa [hSeq] using htop
    exact (NNReal.tendsto_coe).1 hmassReal
  · intro h
    rcases h with ⟨hmass, hcont⟩
    have hmassReal : Tendsto (fun n ↦ ((μs n).mass : ℝ)) atTop (𝓝 (μ.mass : ℝ)) :=
      (NNReal.tendsto_coe).2 hmass
    have hSeq :
        (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal) =
          fun n ↦ ((μs n).mass : ℝ) := by
      funext n
      exact measureDistributionFunction_measure_univ_toReal_eq_mass (μs n) (hμs n)
    have hLim : ((measureDistributionFunction μ).measure Set.univ).toReal = (μ.mass : ℝ) :=
      measureDistributionFunction_measure_univ_toReal_eq_mass μ hμ
    have hmassTop :
        Tendsto (fun n ↦ ((measureDistributionFunction (μs n)).measure Set.univ).toReal)
          atTop (𝓝 (((measureDistributionFunction μ).measure Set.univ).toReal)) := by
      -- Proof comment: convert total-mass convergence into endpoint-value convergence.
      rw [hLim]
      simpa [hSeq] using hmassReal
    refine ⟨?_, ?_, hcont, ?_⟩
    · exact isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one μ hμ
    · intro n
      exact
        isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one
          (μs n) (hμs n)
    simp [hmassTop.limsup_eq]
