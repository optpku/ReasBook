/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic

public section

noncomputable section

open scoped BigOperators ProbabilityTheory NNReal

namespace ProbabilityTheory

universe v

/-- The finite product law of scalar Poisson measures with rate vector `rate`. -/
@[expose] def poissonVector {ι : Type v} [Fintype ι] (rate : ι → ℝ≥0) :
    MeasureTheory.Measure (ι → ℝ) :=
  MeasureTheory.Measure.pi (fun i ↦ Po(ℝ, rate i))

/-- `poissonVector rate` is the finite product of the coordinate Poisson laws. -/
theorem poissonVector_eq_pi {ι : Type v} [Fintype ι] (rate : ι → ℝ≥0) :
    poissonVector rate = MeasureTheory.Measure.pi (fun i ↦ Po(ℝ, rate i)) :=
  rfl

/-- The singleton mass of `poissonVector rate` factors into the coordinatewise Poisson masses. -/
theorem poissonVector_apply_singleton {ι : Type v} [Fintype ι]
    (rate : ι → ℝ≥0) (x : ι → ℝ) :
    poissonVector rate {x} = ∏ i, Po(ℝ, rate i) {x i} := by
  rw [poissonVector_eq_pi rate]
  exact MeasureTheory.Measure.pi_singleton (μ := fun i ↦ Po(ℝ, rate i)) x

/-- The rate vector of a finite Poisson product law is determined by the law itself. -/
theorem poissonVector_eq_iff {ι : Type v} [Fintype ι]
    {rate₁ rate₂ : ι → ℝ≥0} :
    poissonVector rate₁ = poissonVector rate₂ ↔ rate₁ = rate₂ := by
  constructor
  · intro h
    funext i
    have hcoord :
        Po(ℝ, rate₁ i) = Po(ℝ, rate₂ i) := by
      have hmap := congrArg (MeasureTheory.Measure.map (Function.eval i)) h
      rw [poissonVector_eq_pi, poissonVector_eq_pi,
        (MeasureTheory.measurePreserving_eval (fun j ↦ Po(ℝ, rate₁ j)) i).map_eq,
        (MeasureTheory.measurePreserving_eval (fun j ↦ Po(ℝ, rate₂ j)) i).map_eq] at hmap
      exact hmap
    have hnat : Po(rate₁ i) = Po(rate₂ i) :=
      (MeasurableEmbedding.natCast (α := ℝ)).map_injective hcoord
    have hzero : Po(rate₁ i) {0} = Po(rate₂ i) {0} :=
      congrArg (fun ν : MeasureTheory.Measure ℕ ↦ ν {0}) hnat
    have hexp : Real.exp (-(rate₁ i : ℝ)) = Real.exp (-(rate₂ i : ℝ)) := by
      have hzeroReal := congrArg ENNReal.toReal hzero
      rw [poissonMeasure_singleton, poissonMeasure_singleton] at hzeroReal
      rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hzeroReal
      simpa using hzeroReal
    have hcoe : (rate₁ i : ℝ) = (rate₂ i : ℝ) := by
      exact neg_injective (Real.exp_injective hexp)
    exact NNReal.coe_injective hcoe
  · rintro rfl
    rfl

end ProbabilityTheory
