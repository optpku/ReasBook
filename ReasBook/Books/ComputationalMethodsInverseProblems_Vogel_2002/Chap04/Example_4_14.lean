/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_14.PoissonVector

public section

noncomputable section

open scoped ProbabilityTheory NNReal

namespace ProbabilityTheory

universe u v

/-- Helper for Example 4.14: rewrite the bundled Poisson vector law as the explicit finite
product of scalar Poisson laws. -/
private lemma jointLawPiForm
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {rate : ι → ℝ≥0}
    (h_joint : HasLaw (fun ω i ↦ X i ω) (poissonVector rate) μ) :
    HasLaw (fun ω i ↦ X i ω) (MeasureTheory.Measure.pi fun i ↦ Po(ℝ, rate i)) μ := by
  -- Normalize the target law into the product form expected by the independence API.
  simpa [poissonVector_eq_pi rate] using h_joint

/-- Helper for Example 4.14: a joint product Poisson law gives the corresponding scalar
Poisson law on each coordinate. -/
private lemma coordinateHasLaw_of_jointPoissonLaw
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {rate : ι → ℝ≥0}
    (h_joint_pi :
      HasLaw (fun ω i ↦ X i ω) (MeasureTheory.Measure.pi fun i ↦ Po(ℝ, rate i)) μ) :
    ∀ i, HasLaw (X i) Po(ℝ, rate i) μ := by
  intro i
  -- Project the joint law to the `i`-th coordinate by the measure-preserving evaluation map.
  have h_eval :
      MeasureTheory.MeasurePreserving
        (Function.eval i)
        (MeasureTheory.Measure.pi fun j ↦ Po(ℝ, rate j))
        Po(ℝ, rate i) :=
    MeasureTheory.measurePreserving_eval (fun j ↦ Po(ℝ, rate j)) i
  have h_eval_law : HasLaw ((Function.eval i) ∘ fun ω j ↦ X j ω) Po(ℝ, rate i) μ :=
    h_eval.hasLaw.comp h_joint_pi
  -- The composed evaluation map is definitionally the `i`-th scalar coordinate.
  change HasLaw (X i) Po(ℝ, rate i) μ at h_eval_law
  exact h_eval_law

/-- Helper for Example 4.14: independence together with scalar Poisson coordinate laws recovers
the joint product Poisson law. -/
private lemma jointPoissonLaw_of_iIndep_and_coordinates
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {rate : ι → ℝ≥0}
    (h_indep : iIndepFun X μ)
    (h_poisson : ∀ i, HasLaw (X i) Po(ℝ, rate i) μ) :
    HasLaw (fun ω i ↦ X i ω) (MeasureTheory.Measure.pi fun i ↦ Po(ℝ, rate i)) μ := by
  -- Use the standard product-law characterization of independent coordinates.
  exact (iIndepFun_iff_hasLaw_pi_pi h_poisson).1 h_indep

/-- Example 4.14 (1). A finite real random vector has Poisson distribution with independent
components and rate vector `rate` exactly when its joint law is `poissonVector rate`. -/
theorem hasLaw_poissonVector_iff
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {rate : ι → ℝ≥0} :
    HasLaw (fun ω i ↦ X i ω) (poissonVector rate) μ ↔
      iIndepFun X μ ∧ ∀ i, HasLaw (X i) Po(ℝ, rate i) μ := by
  constructor
  · intro h_joint
    -- First move the bundled law into explicit product form.
    have h_joint_pi := jointLawPiForm h_joint
    -- Then read off the scalar Poisson law on each coordinate.
    have h_poisson := coordinateHasLaw_of_jointPoissonLaw h_joint_pi
    -- The product-law characterization now returns independence.
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi h_poisson).2 h_joint_pi, h_poisson⟩
  · rintro ⟨h_indep, h_poisson⟩
    -- Reassemble the joint product law from independent Poisson coordinates.
    have h_joint_pi := jointPoissonLaw_of_iIndep_and_coordinates h_indep h_poisson
    simpa [poissonVector_eq_pi rate] using h_joint_pi

/- Example 4.14 (2). The source's mean identity is formalized separately in Exercise 4.4. -/

/- Example 4.14 (3). The source's covariance identity is formalized separately in
Exercise 4.4. -/

/- Example 4.14 (4). The rate vector `rate` characterizes the Poisson distribution with
independent components. -/
#check ProbabilityTheory.poissonVector_eq_iff

end ProbabilityTheory
