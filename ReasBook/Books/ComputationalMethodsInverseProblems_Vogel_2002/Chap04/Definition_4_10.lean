/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_9.JointCDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic

public section

noncomputable section

open scoped BigOperators

namespace ProbabilityTheory

universe u v

/- Definition 4.10 (1). A finite real random vector is discrete exactly when it has a `PMF`
law. -/

/-- A finite real random vector is discrete when its law is the measure associated to some
probability mass function on `ι → ℝ`. -/
def IsDiscreteRandomVector
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    (μ : MeasureTheory.Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∃ p : PMF (ι → ℝ), HasLaw (fun ω i ↦ X i ω) p.toMeasure μ

/-- The defining law-based characterization of `IsDiscreteRandomVector`. -/
theorem isDiscreteRandomVector_iff
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ} :
    IsDiscreteRandomVector μ X ↔
      ∃ p : PMF (ι → ℝ), HasLaw (fun ω i ↦ X i ω) p.toMeasure μ :=
  Iff.rfl

/- Definition 4.10 (2). The joint probability mass function is recovered from point
probabilities. -/

/-- The canonical joint probability mass function attached to a discrete random vector, recovered
from its point probabilities. -/
noncomputable def jointPmf
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ}
    (hX : IsDiscreteRandomVector μ X) : PMF (ι → ℝ) :=
  ⟨fun x ↦ μ {ω | ∀ i, X i ω = x i}, by
    classical
    rcases hX with ⟨p, hp⟩
    convert p.hasSum_coe_one using 1
    ext x
    have h_measure :
        μ {ω | (fun i ↦ X i ω) = x} = p.toMeasure {y | y = x} :=
      hp.measure_eq (measurableSet_singleton x)
    calc
      μ {ω | ∀ i, X i ω = x i} = μ {ω | (fun i ↦ X i ω) = x} := by
        congr 1
        ext ω
        simp [funext_iff]
      _ = p.toMeasure {y | y = x} := h_measure
      _ = p x := by
        simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)⟩

/-- The canonical `jointPmf` has the law specified by `IsDiscreteRandomVector`. -/
theorem jointPmf_spec
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ}
    (hX : IsDiscreteRandomVector μ X) :
    HasLaw (fun ω i ↦ X i ω) (jointPmf hX).toMeasure μ := by
  classical
  rcases hX with ⟨p, hp⟩
  have h_jointPmf : jointPmf (μ := μ) (X := X) ⟨p, hp⟩ = p := by
    ext x
    have h_measure :
        μ {ω | (fun i ↦ X i ω) = x} = p.toMeasure {y | y = x} :=
      hp.measure_eq (measurableSet_singleton x)
    calc
      jointPmf (μ := μ) (X := X) ⟨p, hp⟩ x = μ {ω | ∀ i, X i ω = x i} := by
        change μ {ω | ∀ i, X i ω = x i} = μ {ω | ∀ i, X i ω = x i}
        rfl
      _ = μ {ω | (fun i ↦ X i ω) = x} := by
        congr 1
        ext ω
        simp [funext_iff]
      _ = p.toMeasure {y | y = x} := h_measure
      _ = p x := by
        simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)
  simpa [h_jointPmf] using hp

/-- The mass of `jointPmf` at `x` equals the probability that every coordinate of `X` takes the
corresponding value of `x`. -/
theorem jointPmf_apply_eq
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ}
    (hX : IsDiscreteRandomVector μ X) (x : ι → ℝ) :
    jointPmf hX x = μ {ω | ∀ i, X i ω = x i} := by
  have h_measure :
      μ {ω | ∀ i, X i ω = x i} = (jointPmf hX).toMeasure {y | y = x} := by
    have h_measure' :
        μ {ω | (fun i ↦ X i ω) = x} = (jointPmf hX).toMeasure {y | y = x} :=
      (jointPmf_spec hX).measure_eq (measurableSet_singleton x)
    calc
      μ {ω | ∀ i, X i ω = x i} = μ {ω | (fun i ↦ X i ω) = x} := by
        congr 1
        ext ω
        simp [funext_iff]
      _ = (jointPmf hX).toMeasure {y | y = x} := h_measure'
  calc
    jointPmf hX x = (jointPmf hX).toMeasure {x} := by
      simpa using ((jointPmf hX).toMeasure_apply_singleton x (measurableSet_singleton x)).symm
    _ = μ {ω | ∀ i, X i ω = x i} := by
      simpa using h_measure.symm

/- Definition 4.10 (3). The joint distribution function is the sum of the masses below `x`.
-/

/-- Helper for Definition 4.10: the pushforward law of a discrete random vector coincides with the
measure attached to its canonical joint PMF. -/
lemma jointPmf_map_eq
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ}
    (hX : IsDiscreteRandomVector μ X) :
    MeasureTheory.Measure.map (fun ω i ↦ X i ω) μ = (jointPmf hX).toMeasure := by
  -- This is exactly the law recorded by `jointPmf_spec`.
  simpa using (jointPmf_spec hX).map_eq

/-- Helper for Definition 4.10: the real mass of a PMF on the lower orthant at `x` is the sum of
the point masses whose coordinates all lie below `x`. -/
lemma pmfReal_lowerOrthant_eq_tsum_indicator
    {ι : Type v} [MeasurableSingletonClass (ι → ℝ)] (p : PMF (ι → ℝ)) (x : ι → ℝ) :
    p.toMeasure.real (Set.univ.pi fun i ↦ Set.Iic (x i)) =
      ∑' y, {y | ∀ i, y i ≤ x i}.indicator (fun y ↦ (p y).toReal) y := by
  -- Convert the PMF measure of the lower orthant into a sum over singleton masses.
  rw [MeasureTheory.Measure.real, PMF.toMeasure_apply_eq_tsum, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun y ↦ ?_
    -- The indicator is either the mass `p y` on the orthant or `0` outside it.
    by_cases hy : ∀ i, y i ≤ x i
    · have hy' : y ∈ Set.univ.pi fun i ↦ Set.Iic (x i) := by
        have hy_le : y ≤ x := by
          simpa [Pi.le_def] using hy
        simpa [Set.mem_pi] using hy_le
      rw [Set.indicator_of_mem hy']
      simp [hy]
    · have hy' : y ∉ Set.univ.pi fun i ↦ Set.Iic (x i) := by
        have hy_not_le : ¬ y ≤ x := by
          simpa [Pi.le_def] using hy
        simpa [Set.mem_pi] using hy_not_le
      rw [Set.indicator_of_notMem hy']
      simp [hy]
  · intro y
    -- Each PMF atom is finite, and the off-orthant branch is zero.
    by_cases hy : ∀ i, y i ≤ x i
    · have hy' : y ∈ Set.univ.pi fun i ↦ Set.Iic (x i) := by
        have hy_le : y ≤ x := by
          simpa [Pi.le_def] using hy
        simpa [Set.mem_pi] using hy_le
      rw [Set.indicator_of_mem hy']
      exact p.apply_ne_top y
    · have hy' : y ∉ Set.univ.pi fun i ↦ Set.Iic (x i) := by
        have hy_not_le : ¬ y ≤ x := by
          simpa [Pi.le_def] using hy
        simpa [Set.mem_pi] using hy_not_le
      rw [Set.indicator_of_notMem hy']
      simp

/-- Helper for Definition 4.10: the joint CDF of a PMF law is the sum of its masses on the lower
orthant below `x`. -/
lemma jointCdf_toMeasure_eq_tsum_indicator
    {ι : Type v} [Fintype ι] (p : PMF (ι → ℝ)) (x : ι → ℝ) :
    jointCdf p.toMeasure x =
      ∑' y, {y | ∀ i, y i ≤ x i}.indicator (fun y ↦ (p y).toReal) y := by
  -- Rewrite `jointCdf` to the lower-orthant real mass and reuse the PMF computation.
  rw [jointCdf_apply]
  exact pmfReal_lowerOrthant_eq_tsum_indicator (p := p) (x := x)

/-- Definition 4.10. The lower-orthant distribution function of a discrete random vector is the
sum of the joint masses over the atoms `y` satisfying `∀ i, y i ≤ x i`. -/
theorem jointCdf_eq_tsum_indicator
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ}
    (hX : IsDiscreteRandomVector μ X) (x : ι → ℝ) :
    jointCdf (MeasureTheory.Measure.map (fun ω i ↦ X i ω) μ) x =
      ∑' y, {y | ∀ i, y i ≤ x i}.indicator (fun y ↦ (jointPmf hX y).toReal) y := by
  -- First replace the pushforward law by the canonical PMF law from `hX`.
  rw [jointPmf_map_eq hX]
  -- Then compute the lower-orthant mass of that PMF law as a real-valued series.
  exact jointCdf_toMeasure_eq_tsum_indicator (p := jointPmf hX) (x := x)

end ProbabilityTheory
