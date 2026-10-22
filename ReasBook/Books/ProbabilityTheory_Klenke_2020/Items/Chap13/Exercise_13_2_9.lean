/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set Topology

universe u

namespace MeasureTheory
namespace FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

-- Proof sketch: apply the null-boundary convergence hypothesis to `univ` to get convergence of the
-- total masses. For a closed set `F`, approximate `F` from outside by the closed `r`-neighborhoods
-- and choose radii whose boundaries are `μ`-null; then pass to the limit and let `r ↓ 0`.
/-- Exercise 13.2.9: the null-boundary setwise convergence condition in Theorem 13.16 directly
implies the closed-set Portmanteau condition. -/
theorem closedSetPortmanteauCondition_of_nullBoundarySetwiseTendsto
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h :
      ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
        Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))) :
    μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
      ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F := by
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
    simpa [FiniteMeasure.mass] using h univ MeasurableSet.univ (by simp)
  refine ⟨(hmass.liminf_eq).symm.le, ?_⟩
  have h' : ∀ {A : Set E}, MeasurableSet A → (μ : Measure E) (frontier A) = 0 →
      Tendsto (fun n ↦ ((μs n : Measure E) A)) atTop (𝓝 ((μ : Measure E) A)) := by
    intro A hA hA0
    have hA0' : μ (frontier A) = 0 := by
      exact ENNReal.coe_eq_zero.mp (by simpa using hA0)
    have hA' : Tendsto (fun n ↦ ENNReal.ofNNReal ((μs n) A)) atTop
        (𝓝 (ENNReal.ofNNReal (μ A))) :=
      (ENNReal.continuous_coe.tendsto (μ A)).comp (h A hA hA0')
    simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hA'
  intro F hF
  have hF' : limsup (fun n ↦ ((μs n : Measure E) F)) atTop ≤ (μ : Measure E) F := by
    exact limsup_measure_closed_le_of_forall_tendsto_measure h' F hF
  have hbounded : atTop.IsBoundedUnder (· ≤ ·) (μs · F) := by
    refine ⟨μ.mass + 1, ?_⟩
    show ∀ᶠ n in atTop, μs n F ≤ μ.mass + 1
    filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
    exact le_trans ((μs n).apply_le_mass F) hn.le
  have aux : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop :=
    ENNReal.coe_mono.map_limsup_of_continuousAt (μs · F) ENNReal.continuous_coe.continuousAt
      hbounded ⟨0, by simp⟩
  have hfun : (fun n ↦ ((μs n : Measure E) F)) = ENNReal.ofNNReal ∘ fun n ↦ μs n F := by
    funext n
    simp [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply]
  have hF'' : limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop ≤ ENNReal.ofNNReal (μ F) := by
    simpa [hfun, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hF'
  have obs : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) ≤ ENNReal.ofNNReal (μ F) := by
    rw [aux]
    exact hF''
  exact_mod_cast obs

end

end FiniteMeasure
end MeasureTheory
