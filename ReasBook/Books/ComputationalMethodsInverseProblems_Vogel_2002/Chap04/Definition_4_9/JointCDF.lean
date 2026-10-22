/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

public section

noncomputable section

open scoped BigOperators

namespace ProbabilityTheory

universe u v

/-- The joint distribution function of a finite real law is the lower-orthant probability
`x ↦ ν.real (Set.univ.pi fun i ↦ Set.Iic (x i))`. -/
def jointCdf
    {ι : Type v} [Fintype ι] (ν : MeasureTheory.Measure (ι → ℝ)) :
    (ι → ℝ) → ℝ :=
  fun x ↦ ν.real (Set.univ.pi fun i ↦ Set.Iic (x i))

/-- The defining lower-orthant formula for `jointCdf`. -/
theorem jointCdf_apply
    {ι : Type v} [Fintype ι] (ν : MeasureTheory.Measure (ι → ℝ)) (x : ι → ℝ) :
    jointCdf ν x = ν.real (Set.univ.pi fun i ↦ Set.Iic (x i)) := by
  -- This is exactly the defining equation of `jointCdf`.
  rfl

/-- A joint law identifies `jointCdf` with the probability of the event
`{ω | ∀ i, Y ω i ≤ x i}`. -/
theorem HasLaw.jointCdf_eq
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {ι : Type v} [Fintype ι] {Y : Ω → ι → ℝ} {ν : MeasureTheory.Measure (ι → ℝ)}
    (hY : HasLaw Y ν μ) (x : ι → ℝ) :
    jointCdf ν x = μ.real {ω | ∀ i, Y ω i ≤ x i} := by
  -- Identify the product lower orthant with the order interval `Set.Iic x`.
  have hOrthant : Set.univ.pi (fun i ↦ Set.Iic (x i)) = (Set.Iic x : Set (ι → ℝ)) := by
    ext y
    simp
  -- Rewrite the source-space event as the pointwise order relation `Y ω ≤ x`.
  have hEvent : {ω | Y ω ≤ x} = {ω | ∀ i, Y ω i ≤ x i} := by
    ext ω
    rfl
  -- Rewrite the joint cdf as the lower-orthant law of `ν`.
  rw [jointCdf_apply, hOrthant]
  -- Transfer that lower-orthant probability back to the source space using `HasLaw`.
  rw [← hEvent]
  exact (hY.measureReal_eq (p := fun y : ι → ℝ => y ≤ x) measurableSet_Iic).symm

/-- The joint distribution function of a finite product law is the product of the coordinate
cumulative distribution functions. -/
theorem jointCdf_pi
    {ι : Type v} [Fintype ι] (ν : ι → MeasureTheory.Measure ℝ)
    [∀ i, MeasureTheory.IsProbabilityMeasure (ν i)] (x : ι → ℝ) :
    jointCdf (MeasureTheory.Measure.pi ν) x = ∏ i, cdf (ν i) (x i) := by
  -- Expand the joint cdf to the lower-orthant probability under the product law.
  rw [jointCdf_apply, MeasureTheory.Measure.real_def, MeasureTheory.Measure.pi_pi,
    ENNReal.toReal_prod]
  -- Convert each one-dimensional lower-orthant probability to the corresponding cdf value.
  refine Finset.prod_congr rfl ?_
  intro i hi
  simpa [MeasureTheory.Measure.real_def] using (cdf_eq_real (μ := ν i) (x := x i)).symm

/-- Independent finite real components have joint distribution function equal to the product of
their marginal cumulative distribution functions. -/
theorem iIndepFun.jointCdf_eq_prod
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (hX : iIndepFun X μ) (x : ι → ℝ) :
    jointCdf (MeasureTheory.Measure.map (fun ω i ↦ X i ω) μ) x =
      ∏ i, cdf (MeasureTheory.Measure.map (X i) μ) (x i) := by
  -- Independence identifies the joint pushforward law with the product of the marginals.
  rw [hX.map_fun_eq_pi_map hXm]
  -- Each marginal pushforward is a probability measure, so the product-law formula applies.
  have hProb :
      ∀ i, MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map (X i) μ) :=
    fun i ↦ MeasureTheory.Measure.isProbabilityMeasure_map (hXm i)
  simpa using
    (@jointCdf_pi ι _ (fun i ↦ MeasureTheory.Measure.map (X i) μ) hProb x)

end ProbabilityTheory
