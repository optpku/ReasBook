/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open Finset

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ}
variable {X : ℕ → Ω → ℝ}

/- Lemma 11.1 lies in the discrete maximal-inequality part of the submartingale API. The owner
abstraction is `MeasureTheory.maximal_ineq`, whose source-facing input is a nonnegative
submartingale. This file stays at the `bridge/view` layer: the textbook lemma is for an arbitrary
real-valued submartingale, so its public statement is recovered from the stopping-time bridge
behind the owner theorem rather than by promoting the owner's nonnegativity hypothesis into the
main API. -/
recall MeasureTheory.maximal_ineq

/-- Lemma 11.1: if `X` is a discrete real-valued submartingale and `A = {X_n^* ≥ λ}` is the event
that the running maximum of `X` up to time `n` reaches the positive threshold `λ`, then
`λ P[A] ≤ E[X_n 1_A] ≤ E[|X_n| 1_A]`. -/
theorem submartingale_maximal_event_expectation_bounds
    (hX : Submartingale X ℱ μ) (n : ℕ) {threshold : ℝ}
    (hthreshold : 0 < threshold) :
    threshold *
        μ.real {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω} ≤
      ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        X n ω ∂μ ∧
    ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        X n ω ∂μ ≤
      ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        |X n ω| ∂μ := by
  let A : Set Ω := {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω}
  let τ : Ω → ℕ := fun ω ↦ hittingBtwn X {y : ℝ | threshold ≤ y} 0 n ω
  let τs : Ω → ℕ∞ := fun ω ↦ (τ ω : ℕ∞)
  have hX_adapted : Adapted ℱ X := hX.stronglyAdapted.adapted
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const <|
      measurable_range_sup'' fun k _ ↦ (hX.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hτ : IsStoppingTime ℱ τs := by
    simpa [τs, τ] using hX_adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ_le : ∀ ω, τs ω ≤ n := by
    intro ω
    have hω : hittingBtwn X {y : ℝ | threshold ≤ y} 0 n ω ≤ n := hittingBtwn_le ω
    change ((τ ω : ℕ∞) ≤ n)
    exact_mod_cast hω
  have hleft_stopped :
      threshold * μ.real A ≤ ∫ ω in A, stoppedValue X τs ω ∂μ := by
    let ε : NNReal := ⟨threshold, hthreshold.le⟩
    have hsmul :
        (ε : ENNReal) * μ A ≤ ENNReal.ofReal (∫ ω in A, stoppedValue X τs ω ∂μ) := by
      simpa [A, τs, τ, ε, Real.toNNReal_of_nonneg hthreshold.le, smul_eq_mul] using
        MeasureTheory.smul_le_stoppedValue_hittingBtwn hX n
    have hε_ne_top : (ε : ENNReal) ≠ ⊤ := by
      simp
    have htoReal :
        ((ε : ENNReal) * μ A).toReal ≤ (ENNReal.ofReal (∫ ω in A, stoppedValue X τs ω ∂μ)).toReal :=
      (ENNReal.toReal_le_toReal
        (by
          simpa [smul_eq_mul] using
            ENNReal.mul_ne_top hε_ne_top (measure_ne_top μ A))
        ENNReal.ofReal_ne_top
      ).2 hsmul
    have hstopped_nonneg : 0 ≤ ∫ ω in A, stoppedValue X τs ω ∂μ := by
      refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
      refine (ae_restrict_iff' hA).2 ?_
      filter_upwards with ω hω
      have hω' :
          threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω := by
        simpa [A] using hω
      have hhit : threshold ≤ stoppedValue X τs ω := by
        simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hω'
        refine stoppedValue_hittingBtwn_mem ?_
        simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
        exact hω'
      exact le_trans hthreshold.le hhit
    rw [ENNReal.toReal_ofReal hstopped_nonneg] at htoReal
    simpa [measureReal_def, ε, A] using htoReal
  have hcomplement_eq :
      ∫ ω in Aᶜ, stoppedValue X τs ω ∂μ = ∫ ω in Aᶜ, X n ω ∂μ := by
    apply integral_congr_ae
    refine (ae_restrict_iff' hA.compl).2 ?_
    filter_upwards with ω hω
    have hω' : ¬ threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω := by
      simpa [A] using hω
    have hτ_eq_nat : τ ω = n := by
      simp only [τ, hittingBtwn, Set.mem_setOf_eq, ite_eq_right_iff, forall_exists_index, and_imp]
      intro m hm hmthreshold
      exact False.elim <| hω' <|
        (le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hmthreshold⟩
    have hτ_eq : τs ω = n := by
      change ((τ ω : ℕ∞) = n)
      exact_mod_cast hτ_eq_nat
    simp [stoppedValue, τs, hτ_eq]
  have hstopped_split :
      μ[stoppedValue X τs] =
        ∫ ω in A, stoppedValue X τs ω ∂μ + ∫ ω in Aᶜ, stoppedValue X τs ω ∂μ := by
    rw [← setIntegral_union disjoint_compl_right hA.compl]
    · simp [A]
    · exact Integrable.integrableOn <| hX.integrable_stoppedValue hτ hτ_le
    · exact Integrable.integrableOn <| hX.integrable_stoppedValue hτ hτ_le
  have hterminal_split :
      μ[X n] = ∫ ω in A, X n ω ∂μ + ∫ ω in Aᶜ, X n ω ∂μ := by
    rw [← setIntegral_union disjoint_compl_right hA.compl]
    · simp [A]
    · exact Integrable.integrableOn <| hX.integrable n
    · exact Integrable.integrableOn <| hX.integrable n
  have hstopped_le_terminal :
      ∫ ω in A, stoppedValue X τs ω ∂μ ≤ ∫ ω in A, X n ω ∂μ := by
    have hmono : μ[stoppedValue X τs] ≤ μ[X n] := by
      simpa [τs, stoppedValue_const] using
        hX.expected_stoppedValue_mono hτ (isStoppingTime_const ℱ n)
          (fun ω ↦ by exact_mod_cast hτ_le ω) (fun _ ↦ by exact_mod_cast le_rfl)
    rw [hstopped_split, hterminal_split, hcomplement_eq] at hmono
    exact le_of_add_le_add_right hmono
  constructor
  · exact hleft_stopped.trans hstopped_le_terminal
  · refine MeasureTheory.setIntegral_mono_on
      (hX.integrable n).integrableOn (hX.integrable n).norm.integrableOn hA ?_
    intro ω hω
    exact le_abs_self (X n ω)
