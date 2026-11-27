/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.LpDual.IndicatorMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace VariationalRegularization.LpDual

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (p : ENNReal) [Fact (1 ≤ p)]

/-- Indicator representation extends algebraically to every simple function. -/
lemma functional_eq_integral_simple (ℓ : StrongDual ℝ (Lp ℝ p μ))
    {g : α → ℝ} (hg : Integrable g μ)
    (hrep : ∀ s, MeasurableSet s → ℓ (indicator μ p s) = ∫ x in s, g x ∂μ)
    (f : SimpleFunc α ℝ) :
    ℓ ((f.memLp_of_isFiniteMeasure p μ).toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    let f := SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)
    have hfun : (f : α → ℝ) = c • (s.indicator fun _ ↦ (1 : ℝ)) := by
      ext x
      by_cases hx : x ∈ s <;> simp [f, hx]
    have hLp : (f.memLp_of_isFiniteMeasure p μ).toLp f = c • indicator μ p s := by
      rw [indicator_of_measurable μ p hs, indicatorConstLp, ← MemLp.toLp_const_smul]
      apply MemLp.toLp_congr
      exact Filter.EventuallyEq.of_eq hfun
    change ℓ ((f.memLp_of_isFiniteMeasure p μ).toLp f) = _
    rw [hLp, map_smul, smul_eq_mul, hrep s hs]
    have hint : (fun x ↦ f x * g x) = s.indicator (fun x ↦ c * g x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [f, hx]
    rw [hint, integral_indicator hs, integral_const_mul]
  | @add f k hd ihf ihk =>
    have hLp : ((f + k).memLp_of_isFiniteMeasure p μ).toLp (f + k) =
        (f.memLp_of_isFiniteMeasure p μ).toLp f + (k.memLp_of_isFiniteMeasure p μ).toLp k := by
      exact MemLp.toLp_add (f.memLp_of_isFiniteMeasure p μ) (k.memLp_of_isFiniteMeasure p μ)
    obtain ⟨C, hC⟩ := f.exists_forall_norm_le
    obtain ⟨D, hD⟩ := k.exists_forall_norm_le
    have hfi := hg.bdd_mul f.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have hki := hg.bdd_mul k.aestronglyMeasurable (Filter.Eventually.of_forall hD)
    rw [hLp, map_add, ihf, ihk, ← integral_add hfi hki]
    congr 1
    funext x
    exact (add_mul (f x) (k x) (g x)).symm

/-- Extend the Radon--Nikodym representation to bounded measurable tests.
Both limits use the same uniformly bounded simple approximants. -/
theorem functional_eq_integral_bounded (hp : p ≠ ∞) (ℓ : StrongDual ℝ (Lp ℝ p μ))
    {g : α → ℝ} (hg : Integrable g μ)
    (hrep : ∀ s, MeasurableSet s → ℓ (indicator μ p s) = ∫ x in s, g x ∂μ)
    {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    ℓ ((MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)).toLp f) =
      ∫ x, f x * g x ∂μ := by
  let hfLp : MemLp f p μ :=
    MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  let F : ℕ → SimpleFunc α ℝ :=
    fun n ↦ SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n
  have hFn : ∀ n x, ‖F n x‖ ≤ 2 * C := by
    intro n x
    have h := SimpleFunc.norm_approxOn_zero_le hf
      (s := range f ∪ {0}) (by simp) x n
    exact h.trans (by nlinarith [hbound x])
  have hpoint : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf
    exact subset_closure (Or.inl (mem_range_self x))
  have hLp : Tendsto (fun n ↦ ((F n).memLp_of_isFiniteMeasure p μ).toLp (F n))
      atTop (𝓝 (hfLp.toLp f)) :=
    SimpleFunc.tendsto_approxOn_range_Lp hp hf hfLp
  have hℓ := ℓ.continuous.tendsto (hfLp.toLp f) |>.comp hLp
  have hint : Tendsto (fun n ↦ ∫ x, F n x * g x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ (2 * C) * ‖g x‖)
    · exact fun n ↦ (F n).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · exact hg.norm.const_mul (2 * C)
    · intro n
      exact Filter.Eventually.of_forall (fun x ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hFn n x) (norm_nonneg _))
    · exact Filter.Eventually.of_forall (fun x ↦ (hpoint x).mul_const (g x))
  have heq : (fun n ↦ ℓ (((F n).memLp_of_isFiniteMeasure p μ).toLp (F n))) =
      (fun n ↦ ∫ x, F n x * g x ∂μ) := by
    funext n
    exact functional_eq_integral_simple μ p ℓ hg hrep (F n)
  simp only [Function.comp_def] at hℓ
  rw [heq] at hℓ
  exact tendsto_nhds_unique hℓ hint

end VariationalRegularization.LpDual
