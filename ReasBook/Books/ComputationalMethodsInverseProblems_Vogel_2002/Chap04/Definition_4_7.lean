/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.CDF

public section

namespace ProbabilityTheory

universe u v w

/-- def_4_7 (1). Definition 4.7 (1). Random variables `X` and `Y` are jointly
distributed when they are measurable maps on the same probability space
`(Ω, μ)`. -/
structure JointlyDistributed
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) : Prop where
  /-- The first random variable is measurable. -/
  measurable_fst : Measurable X
  /-- The second random variable is measurable. -/
  measurable_snd : Measurable Y

/-- Constructor for `JointlyDistributed` from measurability of both random variables. -/
theorem JointlyDistributed.ofMeasurable
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) : JointlyDistributed μ X Y :=
  ⟨hX, hY⟩

/-- The defining common-probability-space characterization of
`JointlyDistributed`. -/
theorem jointlyDistributed_iff
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} :
    JointlyDistributed μ X Y ↔ Measurable X ∧ Measurable Y := by
  constructor
  · intro hXY
    -- Unpack the structure into the two measurability fields it stores.
    exact ⟨hXY.measurable_fst, hXY.measurable_snd⟩
  · intro hXY
    -- Repackage the measurable components into the source-facing structure.
    exact JointlyDistributed.ofMeasurable hXY.1 hXY.2

/-- Auxiliary bridge: jointly distributed random variables induce the canonical
law of their paired map. -/
theorem jointDistrib_hasLaw_map
    {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} (hXY : JointlyDistributed μ X Y) :
    ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω))
      (MeasureTheory.Measure.map (fun ω ↦ (X ω, Y ω)) μ) μ := by
  -- The paired random variable is measurable because each coordinate is measurable.
  refine
    { aemeasurable := (Measurable.prodMk hXY.measurable_fst hXY.measurable_snd).aemeasurable
      map_eq := ?_ }
  -- Its law is definitionally the pushforward measure by the paired map.
  rfl

/-- def_4_7 (2). Definition 4.7 (2). Random variables on a common probability space
are almost everywhere equal exactly when `μ {ω | X ω = Y ω} = 1`; the event
`{ω | X ω = Y ω}` is measurable under `[MeasurableEq S]`. -/
theorem aeEq_iff_prob_eq_one
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableEq S] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X Y : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) :
    X =ᵐ[μ] Y ↔ μ {ω | X ω = Y ω} = 1 := by
  -- The equality event is measurable because equality in the codomain is measurable.
  have hEq : Measurable fun ω ↦ X ω = Y ω := by
    fun_prop
  -- Reduce almost-everywhere equality to the probability-one characterization.
  simpa [Filter.EventuallyEq] using
    (MeasureTheory.ae_iff_prob_eq_one (μ := μ) (p := fun ω ↦ X ω = Y ω) hEq)

/-- Definition 4.7 (3). `X ∼ Y` means that `X` and `Y` have the same cumulative distribution
function. -/
theorem identDistrib_iff_cdf_eq
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : MeasureTheory.Measure Ω} {ν : MeasureTheory.Measure Ω'}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    IdentDistrib X Y μ ν ↔
      cdf (MeasureTheory.Measure.map X μ) = cdf (MeasureTheory.Measure.map Y ν) := by
  constructor
  · intro hXY
    -- Equality in distribution is equality of the two pushforward laws, so their CDFs agree.
    exact congrArg cdf hXY.map_eq
  · intro hCDF
    -- Rebuild `IdentDistrib` from the measurable random variables and equality of pushforwards.
    refine
      { aemeasurable_fst := hX.aemeasurable
        aemeasurable_snd := hY.aemeasurable
        map_eq := ?_ }
    exact
      ((@MeasureTheory.Measure.cdf_eq_iff (MeasureTheory.Measure.map X μ)
          (MeasureTheory.Measure.map Y ν)
          (MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable)
          (MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable)).mp hCDF)

/-- Helper for Definition 4.7: collect the three source-facing characterizations of joint
distribution, almost-everywhere equality, and equality in distribution into a single conjunction. -/
theorem jointlyDistributedAeEqIdentDistrib_iff
    {Ω : Type u} {Ω' : Type v} {S : Type w} {T : Type w} {U : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableEq U]
    {μ : MeasureTheory.Measure Ω} {ν : MeasureTheory.Measure Ω'}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    {X : Ω → S} {Y : Ω → T} {Xeq Yeq : Ω → U} {Xd : Ω → ℝ} {Yd : Ω' → ℝ}
    (hXeq : Measurable Xeq) (hYeq : Measurable Yeq) (hXd : Measurable Xd)
    (hYd : Measurable Yd) :
    (JointlyDistributed μ X Y ↔ Measurable X ∧ Measurable Y) ∧
      (Xeq =ᵐ[μ] Yeq ↔ μ {ω | Xeq ω = Yeq ω} = 1) ∧
      (IdentDistrib Xd Yd μ ν ↔
        cdf (MeasureTheory.Measure.map Xd μ) = cdf (MeasureTheory.Measure.map Yd ν)) := by
  -- Combine the three source-facing characterizations already proved in this file.
  refine ⟨jointlyDistributed_iff, ?_⟩
  exact ⟨aeEq_iff_prob_eq_one hXeq hYeq, identDistrib_iff_cdf_eq hXd hYd⟩

end ProbabilityTheory
