/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {ι : Type v} [mΩ : MeasurableSpace Ω]

/-- Example 12.21: if each `A i` is a sub-`σ`-algebra of `𝓕`, then for every finite family of
`A i`-measurable events the conditional probability of the intersection given `𝓕` equals the
product of the conditional probabilities. -/
theorem condProb_biInter_eq_prod_of_subalgebras_le
    {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ)
    (A : ι → MeasurableSpace Ω) (hA : ∀ i, A i ≤ 𝓕)
    (P : @Measure Ω mΩ) [IsFiniteMeasure P] (s : Finset ι) {E : ι → Set Ω}
    (hE : ∀ i, i ∈ s → MeasurableSet[A i] (E i)) :
    P⟦⋂ i ∈ s, E i | 𝓕⟧ =ᵐ[P] ∏ i ∈ s, P⟦E i | 𝓕⟧ := by
  let oneFun : Ω → ℝ := fun _ ↦ 1
  have hE𝓕 : ∀ i, i ∈ s → MeasurableSet[𝓕] (E i) :=
    fun i hi ↦ hA i _ (hE i hi)
  have h_one_int : Integrable oneFun P := by
    simp [oneFun]
  have h_condExp_one : P[oneFun | 𝓕] = oneFun := by
    simpa [oneFun] using
      (condExp_of_stronglyMeasurable h𝓕 stronglyMeasurable_const h_one_int : P[oneFun | 𝓕] = oneFun)
  have hcond :
      ∀ i, i ∈ s → P[(E i).indicator oneFun | 𝓕] =ᵐ[P] (E i).indicator oneFun := by
    intro i hi
    have hEi𝓕 : MeasurableSet[𝓕] (E i) := hE𝓕 i hi
    calc
      P[(E i).indicator oneFun | 𝓕] =ᵐ[P] (E i).indicator (P[oneFun | 𝓕]) := by
        simpa [oneFun] using
          (condExp_indicator h_one_int hEi𝓕 :
            P[(E i).indicator oneFun | 𝓕] =ᵐ[P] (E i).indicator (P[oneFun | 𝓕]))
      _ = (E i).indicator oneFun := by
        exact congrArg ((E i).indicator) h_condExp_one
  have hbiInter𝓕 : MeasurableSet[𝓕] (⋂ i ∈ s, E i) :=
    s.measurableSet_biInter fun i hi ↦ hE𝓕 i hi
  have hbiInter :
      P[(⋂ i ∈ s, E i).indicator oneFun | 𝓕] =ᵐ[P] (⋂ i ∈ s, E i).indicator oneFun := by
    calc
      P[(⋂ i ∈ s, E i).indicator oneFun | 𝓕] =ᵐ[P]
          (⋂ i ∈ s, E i).indicator (P[oneFun | 𝓕]) := by
        simpa [oneFun] using
          (condExp_indicator h_one_int hbiInter𝓕 :
            P[(⋂ i ∈ s, E i).indicator oneFun | 𝓕] =ᵐ[P]
              (⋂ i ∈ s, E i).indicator (P[oneFun | 𝓕]))
      _ = (⋂ i ∈ s, E i).indicator oneFun := by
        exact congrArg ((⋂ i ∈ s, E i).indicator) h_condExp_one
  have hprod :
      (∏ i ∈ s, P[(E i).indicator oneFun | 𝓕]) =ᵐ[P] (⋂ i ∈ s, E i).indicator oneFun := by
    have hcond_all :
        ∀ᵐ ω ∂P, ∀ i ∈ s, (P[(E i).indicator oneFun | 𝓕]) ω = (E i).indicator oneFun ω := by
      simp_rw [← Finset.mem_coe]
      rw [ae_ball_iff (Finset.countable_toSet s)]
      exact hcond
    filter_upwards [hcond_all] with ω hω
    calc
      (∏ i ∈ s, P[(E i).indicator oneFun | 𝓕]) ω = ∏ i ∈ s, (E i).indicator oneFun ω := by
        rw [Finset.prod_apply]
        exact Finset.prod_congr rfl fun i hi ↦ hω i hi
      _ = (⋂ i ∈ s, E i).indicator (∏ i ∈ s, oneFun) ω := by
        simpa [Finset.prod_apply] using congrFun (prod_indicator s E (fun _ ↦ oneFun)) ω
      _ = (⋂ i ∈ s, E i).indicator oneFun ω := by
        by_cases hω' : ω ∈ ⋂ i ∈ s, E i <;> simp [oneFun, hω']
  change P[(⋂ i ∈ s, E i).indicator (fun _ ↦ (1 : ℝ)) | 𝓕] =ᵐ[P]
      ∏ i ∈ s, P[(E i).indicator (fun _ ↦ (1 : ℝ)) | 𝓕]
  exact hbiInter.trans hprod.symm

/- Source/core/bridge triage:
the theorem above is the source-facing event-factorization statement. The owner abstraction is
`ProbabilityTheory.iCondIndep`, but the public bridge to `ProbabilityTheory.iCondIndep_iff`
requires `[StandardBorelSpace Ω]`, so the source-facing theorem remains primary at the original
hypothesis level. The companion bridge below exposes the canonical owner object exactly when that
extra owner-side hypothesis is available. -/

theorem iCondIndep_of_subalgebras_le [StandardBorelSpace Ω]
    {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ)
    (A : ι → MeasurableSpace Ω) (hA : ∀ i, A i ≤ 𝓕)
    (P : @Measure Ω mΩ) [IsFiniteMeasure P] :
    iCondIndep 𝓕 h𝓕 A P := by
  let hAmΩ : ∀ i, A i ≤ mΩ := fun i ↦ (hA i).trans h𝓕
  rw [iCondIndep_iff 𝓕 h𝓕 A hAmΩ P]
  intro s E hE
  letI : MeasurableSpace Ω := mΩ
  exact condProb_biInter_eq_prod_of_subalgebras_le h𝓕 A hA P s hE
