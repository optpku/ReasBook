/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

private noncomputable def boolProbabilityParameter (ξ : ProbabilityMeasure Bool) : unitInterval :=
  ⟨(ξ : Measure Bool).real {true}, ⟨measureReal_nonneg, measureReal_le_one⟩⟩

/-- Helper for Example 12.28: the `NNReal` Bernoulli parameter attached to a `unitInterval`
parameter is bounded by `1`, so the Bernoulli pmf is well-formed. -/
private theorem unitInterval_toNNReal_le_one (y : unitInterval) : toNNReal y ≤ 1 := by
  -- Proof comment: unwrap the `unitInterval` bound and rewrite the coercion to `NNReal`.
  simpa [unitInterval.toNNReal] using y.2.2

/-- Helper for Example 12.28: the Bernoulli law on `Bool` associated with the parameter `y`. -/
private noncomputable def boolBernoulliProbabilityMeasure (y : unitInterval) :
    ProbabilityMeasure Bool :=
  ⟨(PMF.bernoulli (toNNReal y) (unitInterval_toNNReal_le_one y)).toMeasure, inferInstance⟩

/-- Helper for Example 12.28: taking the `{true}` mass of a `Bool`-valued probability law is a
measurable map into `unitInterval`. -/
private theorem measurable_boolProbabilityParameter : Measurable boolProbabilityParameter := by
  -- Proof comment: measurability of the parameter is just measurability of the singleton-mass
  -- evaluation map, followed by the `ENNReal.toReal` projection into `[0,1]`.
  refine Measurable.subtype_mk ?_
  exact (((Measure.measurable_coe (measurableSet_singleton true)).ennreal_toReal).comp
    measurable_subtype_coe)

/-- Helper for Example 12.28: the real singleton masses of the Bernoulli law have the expected
`y`/`1 - y` form. -/
private theorem boolBernoulliProbabilityMeasure_real_singleton (y : unitInterval) (b : Bool) :
    (boolBernoulliProbabilityMeasure y : Measure Bool).real ({b} : Set Bool) =
      if b then (y : ℝ) else 1 - (y : ℝ) := by
  -- Proof comment: on `Bool`, the Bernoulli pmf is explicit on the two singleton atoms.
  have hy : unitInterval.toNNReal y ≤ 1 := by
    simpa [unitInterval.toNNReal] using y.2.2
  cases b
  · simp [boolBernoulliProbabilityMeasure, Measure.real_def, hy]
  · simp [boolBernoulliProbabilityMeasure, Measure.real_def]

/-- Helper for Example 12.28: every subset of `Bool` is one of the four canonical measurable
sets. -/
private theorem boolSet_cases (s : Set Bool) :
    s = ∅ ∨ s = {false} ∨ s = {true} ∨ s = Set.univ := by
  by_cases hfalse : false ∈ s
  · by_cases htrue : true ∈ s
    · right
      right
      right
      ext b <;> cases b <;> simp [hfalse, htrue]
    · right
      left
      ext b <;> cases b <;> simp [hfalse, htrue]
  · by_cases htrue : true ∈ s
    · right
      right
      left
      ext b <;> cases b <;> simp [hfalse, htrue]
    · left
      ext b <;> cases b <;> simp [hfalse, htrue]

/-- Helper for Example 12.28: the Bernoulli law map from `[0,1]` into `ProbabilityMeasure Bool`
is measurable. -/
private theorem measurable_boolBernoulliProbabilityMeasure :
    Measurable boolBernoulliProbabilityMeasure := by
  -- Proof comment: on the finite space `Bool`, every measurable set is one of four cases, so the
  -- evaluation maps reduce to constant maps or the explicit singleton-mass formulas.
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s _ ↦ ?_
  rcases boolSet_cases s with rfl | rfl | rfl | rfl
  · change Measurable fun y : unitInterval ↦ (boolBernoulliProbabilityMeasure y : Measure Bool) ∅
    convert measurable_const using 1
    funext y
    exact measure_empty
  · change Measurable fun y : unitInterval ↦
      (boolBernoulliProbabilityMeasure y : Measure Bool) ({false} : Set Bool)
    have hfalse :
        (fun y : unitInterval ↦
          (boolBernoulliProbabilityMeasure y : Measure Bool) ({false} : Set Bool)) =
          fun y : unitInterval ↦ ENNReal.ofReal (1 - (y : ℝ)) := by
      funext y
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [← Measure.real_def, boolBernoulliProbabilityMeasure_real_singleton]
      simp
    rw [hfalse]
    exact (measurable_const.sub measurable_subtype_coe).ennreal_ofReal
  · change Measurable fun y : unitInterval ↦
      (boolBernoulliProbabilityMeasure y : Measure Bool) ({true} : Set Bool)
    have htrue :
        (fun y : unitInterval ↦
          (boolBernoulliProbabilityMeasure y : Measure Bool) ({true} : Set Bool)) =
          fun y : unitInterval ↦ ENNReal.ofReal (y : ℝ) := by
      funext y
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [← Measure.real_def, boolBernoulliProbabilityMeasure_real_singleton]
      simp
    rw [htrue]
    exact measurable_subtype_coe.ennreal_ofReal
  · change Measurable fun y : unitInterval ↦ (boolBernoulliProbabilityMeasure y : Measure Bool) Set.univ
    convert measurable_const using 1
    funext y
    exact measure_univ

/-- Helper for Example 12.28: a probability measure on `Bool` is exactly the Bernoulli law with
parameter equal to its `{true}` mass. -/
private theorem boolBernoulliProbabilityMeasure_boolProbabilityParameter
    (ξ : ProbabilityMeasure Bool) :
    boolBernoulliProbabilityMeasure (boolProbabilityParameter ξ) = ξ := by
  -- Proof comment: two probability laws on `Bool` are determined by the masses of `{true}` and
  -- `{false}`; the second one is forced by the complement identity.
  apply Subtype.ext
  apply (MeasureTheory.ext_iff_measureReal_singleton
    (μ1 := (boolBernoulliProbabilityMeasure (boolProbabilityParameter ξ) : Measure Bool))
    (μ2 := (ξ : Measure Bool))).2
  intro b
  cases b
  · have hcompl : ({true} : Set Bool)ᶜ = ({false} : Set Bool) := by
      ext x
      cases x <;> simp
    have hprob :
        (ξ : Measure Bool).real ({true} : Set Bool) +
          (ξ : Measure Bool).real ({false} : Set Bool) = 1 := by
      simpa [hcompl] using
        (probReal_add_probReal_compl (μ := (ξ : Measure Bool))
          (s := ({true} : Set Bool)) (measurableSet_singleton true))
    have hfalse :
        (ξ : Measure Bool).real ({false} : Set Bool) =
          1 - (ξ : Measure Bool).real ({true} : Set Bool) := by
      linarith
    -- Proof comment: the `{false}` mass is the complement of the `{true}` mass.
    simpa [boolProbabilityParameter, hfalse] using
      (boolBernoulliProbabilityMeasure_real_singleton (boolProbabilityParameter ξ) false)
  · -- Proof comment: the parameter was defined to be the `{true}` mass itself.
    simpa [boolProbabilityParameter] using
      (boolBernoulliProbabilityMeasure_real_singleton (boolProbabilityParameter ξ) true)

/-- Helper for Example 12.28: the random Bernoulli parameter and the directing `Bool` law induce
the same conditioning `σ`-algebra. -/
private theorem comap_boolProbabilityParameter_eq
    {xiInf : Ω → ProbabilityMeasure Bool} :
    MeasurableSpace.comap (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance =
      MeasurableSpace.comap xiInf inferInstance := by
  apply le_antisymm
  · -- Proof comment: `ξ ↦ ξ{true}` is measurable, so `Y` is measurable with respect to `ξ∞`.
    have hparam :
        Measurable[MeasurableSpace.comap xiInf inferInstance]
          (fun ω ↦ boolProbabilityParameter (xiInf ω)) :=
      measurable_boolProbabilityParameter.comp (Measurable.of_comap_le le_rfl)
    exact hparam.comap_le
  · have hback :
        Measurable[MeasurableSpace.comap (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance]
          (fun ω ↦ boolBernoulliProbabilityMeasure (boolProbabilityParameter (xiInf ω))) :=
      measurable_boolBernoulliProbabilityMeasure.comp (Measurable.of_comap_le le_rfl)
    have hrepr :
        (fun ω ↦ boolBernoulliProbabilityMeasure (boolProbabilityParameter (xiInf ω))) = xiInf := by
      funext ω
      exact boolBernoulliProbabilityMeasure_boolProbabilityParameter (xiInf ω)
    -- Proof comment: conversely, the directing law is recovered measurably from the parameter.
    have hxi :
        Measurable[MeasurableSpace.comap (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance]
          xiInf := by
      simpa [hrepr] using hback
    exact hxi.comap_le

-- Proof sketch: apply the chapter-owner de Finetti theorem to the `Bool`-valued exchangeable
-- sequence `X`, then convert the resulting directing `Bool`-valued probability measure into its
-- canonical Bernoulli parameter `ξ ↦ ξ{true} ∈ [0,1]`; this is exactly the bridge encoded by
-- `IsConditionallyBernoulliIID`.
/-- Example 12.28: every exchangeable `{0,1}`-valued sequence is conditionally i.i.d. Bernoulli
with a random parameter `Y : Ω → [0,1]`; equivalently, for each finite set of coordinates, the
conditional probability that all selected coordinates equal `1` is the corresponding power of
`Y`. -/
theorem exists_conditionalBernoulliParameter_of_isExchangeable
    {X : ℕ → Ω → Bool} (hX : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n)) :
    ∃ Y : Ω → unitInterval,
      IsConditionallyBernoulliIID Y X μ := by
  have hXi :=
    (isExchangeable_iff_exists_directingProbabilityMeasure hX_meas).mp hX
  rcases hXi with ⟨xiInf, hxiInf_meas_exchangeable, hxiInf⟩
  have hswap : Measurable (Function.swap X) := by
    -- Proof comment: measurability into the countable product `Bool^ℕ` is coordinatewise.
    rw [measurable_pi_iff]
    intro n
    simpa [Function.swap] using hX_meas n
  have hxiInf_meas : Measurable xiInf :=
    hxiInf_meas_exchangeable.mono (exchangeableSigmaAlgebra_le hswap) le_rfl
  let Y : Ω → unitInterval := fun ω ↦ boolProbabilityParameter (xiInf ω)
  have hY_meas : Measurable Y := measurable_boolProbabilityParameter.comp hxiInf_meas
  have hcomap : MeasurableSpace.comap Y inferInstance = MeasurableSpace.comap xiInf inferInstance := by
    simpa [Y] using (comap_boolProbabilityParameter_eq (xiInf := xiInf))
  have hIIDxiInf : IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ := hxiInf.1
  have hIdentXiInf : IsConditionallyIdentDistrib (MeasurableSpace.comap xiInf inferInstance) X μ :=
    hIIDxiInf.2
  have hCondZero :
      ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X 0) xiInf μ ξ = (ξ : Measure Bool) := hxiInf.2
  rcases hIdentXiInf with ⟨_, hXiMeas, hCondEqXiInf⟩
  refine ⟨Y, ?_⟩
  refine ⟨hY_meas, ?_, ?_⟩
  · -- Proof comment: once the conditioning `σ`-algebra is identified, the conditional i.i.d.
    -- structure from the directing law transfers unchanged to `Y`.
    rw [hcomap]
    exact hIIDxiInf
  · intro i
    -- Route correction: previous attempts tried to transport the full `ProbabilityMeasure Bool`
    -- statement at once; on `Bool`, comparing the two singleton masses is the stable route.
    have hcondComp :
        (fun ω ↦ condDistrib (X i) Y μ (Y ω)) =ᵐ[μ]
          fun ω ↦ condDistrib (X i) xiInf μ (xiInf ω) := by
      have hmass (b : Bool) :
          (fun ω ↦ (condDistrib (X i) Y μ (Y ω)).real ({b} : Set Bool)) =ᵐ[μ]
            fun ω ↦ (condDistrib (X i) xiInf μ (xiInf ω)).real ({b} : Set Bool) := by
        calc
          (fun ω ↦ (condDistrib (X i) Y μ (Y ω)).real ({b} : Set Bool))
              =ᵐ[μ] μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Y inferInstance⟧ := by
                -- Proof comment: rewrite the `Y`-conditional law through the corresponding
                -- conditional expectation of the singleton event.
                simpa using
                  (condDistrib_ae_eq_condExp (μ := μ) (X := Y) (Y := X i)
                    hY_meas (hX_meas i) (measurableSet_singleton b))
          _ =ᵐ[μ] μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap xiInf inferInstance⟧ := by
                -- Proof comment: the two conditioning `σ`-algebras coincide by the Bernoulli
                -- reparametrization bridge.
                simpa [hcomap]
          _ =ᵐ[μ] (fun ω ↦ (condDistrib (X i) xiInf μ (xiInf ω)).real ({b} : Set Bool)) := by
                -- Proof comment: now rewrite back through the conditional distribution given the
                -- original directing random measure.
                simpa using
                  (condDistrib_ae_eq_condExp (μ := μ) (X := xiInf) (Y := X i)
                    hxiInf_meas (hX_meas i) (measurableSet_singleton b)).symm
      filter_upwards [hmass false, hmass true] with ω hfalse htrue
      apply (MeasureTheory.ext_iff_measureReal_singleton
        (μ1 := condDistrib (X i) Y μ (Y ω))
        (μ2 := condDistrib (X i) xiInf μ (xiInf ω))).2
      intro b
      cases b
      · simpa using hfalse
      · simpa using htrue
    have hcoordZeroComp :
        (fun ω ↦ condDistrib (X i) xiInf μ (xiInf ω)) =ᵐ[μ]
          fun ω ↦ condDistrib (X 0) xiInf μ (xiInf ω) := by
      have hmass (b : Bool) :
          (fun ω ↦ (condDistrib (X i) xiInf μ (xiInf ω)).real ({b} : Set Bool)) =ᵐ[μ]
            fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool) := by
        calc
          (fun ω ↦ (condDistrib (X i) xiInf μ (xiInf ω)).real ({b} : Set Bool))
              =ᵐ[μ] μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap xiInf inferInstance⟧ := by
                simpa using
                  (condDistrib_ae_eq_condExp (μ := μ) (X := xiInf) (Y := X i)
                    hxiInf_meas (hX_meas i) (measurableSet_singleton b))
          _ =ᵐ[μ] μ⟦X 0 ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap xiInf inferInstance⟧ := by
                -- Proof comment: conditional identical distribution lets us replace coordinate `i`
                -- by coordinate `0` before invoking the directing-law clause.
                exact hCondEqXiInf i 0 ({b} : Set Bool) (measurableSet_singleton b)
          _ =ᵐ[μ] (fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool)) := by
                simpa using
                  (condDistrib_ae_eq_condExp (μ := μ) (X := xiInf) (Y := X 0)
                    hxiInf_meas (hX_meas 0) (measurableSet_singleton b)).symm
      filter_upwards [hmass false, hmass true] with ω hfalse htrue
      apply (MeasureTheory.ext_iff_measureReal_singleton
        (μ1 := condDistrib (X i) xiInf μ (xiInf ω))
        (μ2 := condDistrib (X 0) xiInf μ (xiInf ω))).2
      intro b
      cases b
      · simpa using hfalse
      · simpa using htrue
    have hxiInfComp :
        (fun ω ↦ condDistrib (X 0) xiInf μ (xiInf ω)) =ᵐ[μ]
          fun ω ↦ boolBernoulliProbabilityMeasure (Y ω) := by
      have hmap :
          ∀ᵐ ξ ∂μ.map xiInf,
            condDistrib (X 0) xiInf μ ξ =
              boolBernoulliProbabilityMeasure (boolProbabilityParameter ξ) := by
        filter_upwards [hCondZero] with ξ hξ
        rw [hξ, boolBernoulliProbabilityMeasure_boolProbabilityParameter]
      -- Proof comment: along the pushforward by `xiInf`, the conditional law is the sampled
      -- directing measure itself, hence the Bernoulli law with parameter `ξ{true}`.
      simpa [Y] using MeasureTheory.ae_of_ae_map hxiInf_meas.aemeasurable hmap
    have hbernoulliComp :
        (fun ω ↦ condDistrib (X i) Y μ (Y ω)) =ᵐ[μ]
          fun ω ↦ (boolBernoulliProbabilityMeasure (Y ω) : Measure Bool) :=
      hcondComp.trans (hcoordZeroComp.trans hxiInfComp)
    have hbernoulli_meas :
        Measurable fun y : unitInterval ↦ (boolBernoulliProbabilityMeasure y : Measure Bool) :=
      measurable_subtype_coe.comp measurable_boolBernoulliProbabilityMeasure
    have hmapMass (b : Bool) :
        ∀ᵐ y ∂μ.map Y,
          (condDistrib (X i) Y μ y).real ({b} : Set Bool) =
            (boolBernoulliProbabilityMeasure y : Measure Bool).real ({b} : Set Bool) := by
      have hcompMass :
          (fun ω ↦ (condDistrib (X i) Y μ (Y ω)).real ({b} : Set Bool)) =ᵐ[μ]
            fun ω ↦ (boolBernoulliProbabilityMeasure (Y ω) : Measure Bool).real ({b} : Set Bool) := by
        filter_upwards [hbernoulliComp] with ω hω
        simpa [hω]
      have hEqSet :
          MeasurableSet
            {y |
              (condDistrib (X i) Y μ y).real ({b} : Set Bool) =
                (boolBernoulliProbabilityMeasure y : Measure Bool).real ({b} : Set Bool)} :=
        measurableSet_eq_fun
          ((Kernel.measurable_coe _ (measurableSet_singleton b)).ennreal_toReal)
          (((Measure.measurable_coe (measurableSet_singleton b)).comp hbernoulli_meas).ennreal_toReal)
      exact (ae_map_iff hY_meas.aemeasurable hEqSet).2 (by simpa [Y] using hcompMass)
    have hmapY :
        ∀ᵐ y ∂μ.map Y,
          condDistrib (X i) Y μ y = (boolBernoulliProbabilityMeasure y : Measure Bool) := by
      filter_upwards [hmapMass false, hmapMass true] with y hfalse htrue
      apply (MeasureTheory.ext_iff_measureReal_singleton
        (μ1 := condDistrib (X i) Y μ y)
        (μ2 := (boolBernoulliProbabilityMeasure y : Measure Bool))).2
      intro b
      cases b
      · simpa using hfalse
      · simpa using htrue
    simpa [boolBernoulliProbabilityMeasure] using hmapY
