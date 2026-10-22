/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic

public section

noncomputable section

open scoped BigOperators

namespace ProbabilityTheory

universe u

/-- A real random variable is discrete when its law is the measure associated to a probability
mass function on `ℝ`. -/
def IsDiscreteRandomVariable
    {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (X : Ω → ℝ) : Prop :=
  ∃ p : PMF ℝ, HasLaw X p.toMeasure μ

/-- The defining law-based characterization of `IsDiscreteRandomVariable`. -/
theorem isDiscreteRandomVariable_iff
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ} :
    IsDiscreteRandomVariable μ X ↔
      ∃ p : PMF ℝ, HasLaw X p.toMeasure μ :=
  Iff.rfl

/-- The canonical probability mass function attached to a discrete real random variable, recovered
from its point probabilities. -/
noncomputable def discretePmf
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) : PMF ℝ :=
  ⟨fun x ↦ μ {ω | X ω = x}, by
    classical
    rcases hX with ⟨p, hp⟩
    convert p.hasSum_coe_one using 1
    ext x
    calc
      μ {ω | X ω = x} = p.toMeasure {y | y = x} :=
        hp.measure_eq (measurableSet_singleton x)
      _ = p x := by simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)⟩

/-- The chosen `discretePmf` has the law specified by `IsDiscreteRandomVariable`. -/
theorem discretePmf_spec
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) :
    HasLaw X (discretePmf hX).toMeasure μ := by
  classical
  rcases hX with ⟨p, hp⟩
  have h_discretePmf : discretePmf ⟨p, hp⟩ = p := by
    ext x
    calc
      discretePmf ⟨p, hp⟩ x = μ {ω | X ω = x} := by
        change μ {ω | X ω = x} = μ {ω | X ω = x}
        rfl
      _ = p.toMeasure {y | y = x} :=
        hp.measure_eq (measurableSet_singleton x)
      _ = p x := by simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)
  simpa [h_discretePmf] using hp

/-- The mass of `discretePmf` at `x` equals the probability that `X = x`. -/
theorem discretePmf_apply_eq_prob
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) (x : ℝ) :
    (discretePmf hX) x = μ {ω | X ω = x} := by
  have h_measure : μ {ω | X ω = x} = (discretePmf hX).toMeasure {y | y = x} :=
    (discretePmf_spec hX).measure_eq (measurableSet_singleton x)
  calc
    (discretePmf hX) x = (discretePmf hX).toMeasure {x} := by
      simpa using ((discretePmf hX).toMeasure_apply_singleton x (measurableSet_singleton x)).symm
    _ = μ {ω | X ω = x} := by
      simpa using h_measure.symm

/-- Helper for Definition 4.2: the cdf of the measure associated to a PMF is the sum of its masses
on `Set.Iic x`. -/
lemma cdf_toMeasure_eq_tsum_indicator (p : PMF ℝ) (x : ℝ) :
    ProbabilityTheory.cdf p.toMeasure x =
      ∑' y, {t | t ≤ x}.indicator (fun t ↦ (p t).toReal) y := by
  have hfinite : ∀ y, Set.indicator (Set.Iic x) (fun t ↦ p t) y ≠ ⊤ := by
    intro y
    by_cases hy : y ≤ x
    · simpa [Set.indicator, hy]
        using p.apply_ne_top y
    · simp [Set.indicator, hy]
  -- Rewrite the cdf as the real mass of `Set.Iic x` for the PMF law.
  rw [ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def, PMF.toMeasure_apply_eq_tsum]
  -- Move `toReal` through the summation once each summand is finite.
  rw [ENNReal.tsum_toReal_eq hfinite]
  congr with y
  by_cases hy : y ≤ x <;> simp [Set.Iic, hy]

/-- The cumulative distribution function of a discrete real random variable is the sum of the
point masses below `x`. -/
theorem cdf_eq_tsum_indicator
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) (x : ℝ) :
    ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ) x =
      ∑' y, {t | t ≤ x}.indicator (fun t ↦ ((discretePmf hX) t).toReal) y := by
  -- Transport the law of `X` to the canonical PMF, then use the PMF-level cdf formula.
  simpa [(discretePmf_spec hX).map_eq] using cdf_toMeasure_eq_tsum_indicator (discretePmf hX) x

/-- Helper for Definition 4.2: the jump of the cdf of a PMF law at `x` is the mass of `{x}`. -/
lemma cdf_toMeasure_jump_eq_apply (p : PMF ℝ) (x : ℝ) :
    ProbabilityTheory.cdf p.toMeasure x -
        Function.leftLim (ProbabilityTheory.cdf p.toMeasure) x =
      (p x).toReal := by
  have hnonneg :
      0 ≤ ProbabilityTheory.cdf p.toMeasure x -
        Function.leftLim (ProbabilityTheory.cdf p.toMeasure) x := by
    -- Monotonicity of the cdf identifies the jump as a nonnegative difference.
    exact sub_nonneg.mpr (Monotone.leftLim_le (ProbabilityTheory.monotone_cdf p.toMeasure) le_rfl)
  have hmass :
      ENNReal.ofReal
          (ProbabilityTheory.cdf p.toMeasure x -
            Function.leftLim (ProbabilityTheory.cdf p.toMeasure) x) =
        p x := by
    -- The Stieltjes measure of a cdf records its jump at a singleton.
    calc
      ENNReal.ofReal
          (ProbabilityTheory.cdf p.toMeasure x -
            Function.leftLim (ProbabilityTheory.cdf p.toMeasure) x) =
          (ProbabilityTheory.cdf p.toMeasure).measure {x} := by
            simp [StieltjesFunction.measure_singleton]
      _ = p.toMeasure {x} := by rw [ProbabilityTheory.measure_cdf]
      _ = p x := by simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)
  -- Convert the singleton-mass equality back to an equality in `ℝ`.
  exact (ENNReal.ofReal_eq_ofReal_iff hnonneg ENNReal.toReal_nonneg).mp (by
    simpa [ENNReal.ofReal_toReal (p.apply_ne_top x)] using hmass)

/-- The jump of the cumulative distribution function at `x` equals the point mass at `x`. -/
theorem cdf_jump_eq_discretePmf
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) (x : ℝ) :
    ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ) x -
        Function.leftLim (ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ)) x =
      ((discretePmf hX) x).toReal := by
  -- Transport the law of `X` to the canonical PMF, then read off the cdf jump as singleton mass.
  simpa [(discretePmf_spec hX).map_eq] using cdf_toMeasure_jump_eq_apply (discretePmf hX) x

end ProbabilityTheory
