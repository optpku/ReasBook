/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap08
section Section04

/-- Tao's book-level predicate asserting that `f` is Riemann integrable on a bounded interval `I`. -/
def TaoRiemannIntegrableOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn f I MeasureTheory.volume

/-- The Riemann integral of `f` over a bounded interval `I`. -/
noncomputable def riemannIntegralOn (I : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in I, f x ∂ MeasureTheory.volume

/-- Helper for Proposition 8.13: unpacking `TaoRiemannIntegrableOn` yields `IntegrableOn`. -/
lemma helperForProposition_8_13_integrableOn_of_riemann
    {I : Set ℝ} {f : ℝ → ℝ} (hriemann : TaoRiemannIntegrableOn I f) :
    MeasureTheory.IntegrableOn f I MeasureTheory.volume := by
  simpa [TaoRiemannIntegrableOn] using hriemann

/-- Helper for Proposition 8.13: a Riemann-integrable function is a.e.-measurable on `I`. -/
lemma helperForProposition_8_13_aemeasurable_of_riemann
    {I : Set ℝ} {f : ℝ → ℝ} (hriemann : TaoRiemannIntegrableOn I f) :
    AEMeasurable f (MeasureTheory.volume.restrict I) := by
  exact
    (MeasureTheory.IntegrableOn.integrable
      (helperForProposition_8_13_integrableOn_of_riemann hriemann)).aemeasurable

/-- Proposition 8.13: Let `I ⊆ ℝ` be a bounded interval, and let `f : I → ℝ` be Riemann
integrable. Then `f` is Lebesgue measurable and Lebesgue integrable on `I`, and the Lebesgue
integral on `I` equals the Riemann integral on `I`. -/
theorem proposition_8_13
    {I : Set ℝ} (hinterval : Set.OrdConnected I) (hbounded : Bornology.IsBounded I)
    {f : ℝ → ℝ} (hriemann : TaoRiemannIntegrableOn I f) :
    AEMeasurable f (MeasureTheory.volume.restrict I) ∧
      MeasureTheory.IntegrableOn f I MeasureTheory.volume ∧
      (∫ x in I, f x ∂ MeasureTheory.volume) = riemannIntegralOn I f := by
  refine ⟨helperForProposition_8_13_aemeasurable_of_riemann hriemann, ?_⟩
  refine ⟨helperForProposition_8_13_integrableOn_of_riemann hriemann, ?_⟩
  simp [riemannIntegralOn]

/-- Helper for Proposition 8.14: the set of rational real numbers has Lebesgue measure zero. -/
lemma helperForProposition_8_14_rationalRange_measure_zero :
    MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ)) = 0 := by
  exact Set.Countable.measure_zero (Set.countable_range ((↑) : ℚ → ℝ)) MeasureTheory.volume

/-- Helper for Proposition 8.14: the Dirichlet function is almost everywhere zero on `[0,1]`. -/
lemma helperForProposition_8_14_ae_zero_on_interval :
    (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ)) =ᵐ[MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) 1)] (fun _ => (0 : ℝ)) := by
  let R : Set ℝ := Set.range ((↑) : ℚ → ℝ)
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hR_measurable : MeasurableSet R := by
    exact Set.Countable.measurableSet (Set.countable_range ((↑) : ℚ → ℝ))
  have hR_zero : MeasureTheory.volume R = 0 := by
    simpa [R] using helperForProposition_8_14_rationalRange_measure_zero
  have hR_restrict_zero : (MeasureTheory.volume.restrict I) R = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hR_measurable]
    refine MeasureTheory.measure_mono_null ?_ hR_zero
    intro x hx
    exact hx.1
  have hR_ae_empty : R =ᵐ[MeasureTheory.volume.restrict I] (∅ : Set ℝ) := by
    exact MeasureTheory.ae_eq_empty.2 hR_restrict_zero
  have hindicator :
      R.indicator (fun _ => (1 : ℝ)) =ᵐ[MeasureTheory.volume.restrict I]
        (∅ : Set ℝ).indicator (fun _ => (1 : ℝ)) := by
    exact indicator_ae_eq_of_ae_eq_set hR_ae_empty
  simpa [R, I] using hindicator

/-- Helper for Proposition 8.14: the Dirichlet function is integrable on `[0,1]`. -/
lemma helperForProposition_8_14_integrableOn :
    MeasureTheory.IntegrableOn ((Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ)))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
  have hae : (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ)) =ᵐ[MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) 1)] (fun _ => (0 : ℝ)) :=
    helperForProposition_8_14_ae_zero_on_interval
  have hzero : MeasureTheory.IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) 1)
      MeasureTheory.volume := by
    simpa using MeasureTheory.integrableOn_zero
  exact
    (MeasureTheory.integrableOn_congr_fun_ae (s := Set.Icc (0 : ℝ) 1)
      (μ := MeasureTheory.volume)
      (f := (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ)))
      (g := fun _ : ℝ => (0 : ℝ)) hae).2 hzero

/-- Helper for Proposition 8.14: the integral of the Dirichlet function over `[0,1]` is zero. -/
lemma helperForProposition_8_14_integral_eq_zero :
    (∫ x in Set.Icc (0 : ℝ) 1, ((Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ))) x
      ∂ MeasureTheory.volume) = 0 := by
  have hae : (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ)) =ᵐ[MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) 1)] (fun _ => (0 : ℝ)) :=
    helperForProposition_8_14_ae_zero_on_interval
  calc
    ∫ x in Set.Icc (0 : ℝ) 1, ((Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ))) x
      ∂ MeasureTheory.volume =
      ∫ x in Set.Icc (0 : ℝ) 1, (0 : ℝ) ∂ MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae hae
    _ = 0 := by simp

/-- Proposition 8.14: Define `f : [0,1] → ℝ` by `f(x) = 1` for rational `x` and `f(x) = 0`
for irrational `x`. Then `f` is Lebesgue integrable on `[0,1]` and
`∫_[0,1] f dμ = 0`, where `μ` is Lebesgue measure. -/
theorem proposition_8_14 :
    let f : ℝ → ℝ := (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ => (1 : ℝ))
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      (∫ x in Set.Icc (0 : ℝ) 1, f x ∂ MeasureTheory.volume) = 0 := by
  dsimp
  exact ⟨helperForProposition_8_14_integrableOn, helperForProposition_8_14_integral_eq_zero⟩

end Section04
end Chap08
