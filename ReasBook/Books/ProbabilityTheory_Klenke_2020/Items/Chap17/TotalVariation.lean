/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_45
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

section TotalVariation

variable {E : Type u} [MeasurableSpace E]

/-- The total variation distance between two probability measures is half of the canonical
signed-measure total-variation norm of their difference. -/
def totalVariationDistance (P Q : ProbabilityMeasure E) : ℝ :=
  SignedMeasure.totalVariationNorm E
      ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2

/-- The probability total variation distance is the normalized signed-measure total-variation
norm of `P - Q`. -/
theorem totalVariationDistance_eq_half_totalVariationNorm
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2 := rfl

/-- A measurable real test function bounded by `1` is integrable against any finite measure. -/
private theorem integrable_of_bound_one {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ := by
  -- Proof comment: finite mass and the uniform `L∞` bound give integrability directly.
  refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
  exact ae_of_all _ hf_bound

/-- The Hahn positive set computes the total variation distance as the excess mass of `P`
over `Q` on that set. -/
private theorem hahnExcess_eq_totalVariationDistance
    (P Q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A)
    (hA_le : (Q : Measure E).restrict A ≤ (P : Measure E).restrict A)
    (hAc_le : (P : Measure E).restrict Aᶜ ≤ (Q : Measure E).restrict Aᶜ) :
    totalVariationDistance P Q = (P : Measure E).real A - (Q : Measure E).real A := by
  have hposA :
      (((P : Measure E) - (Q : Measure E)).real A) =
        (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: on the Hahn positive set, the restricted residual is the pointwise
    -- difference of the restricted masses.
    calc
      (((P : Measure E) - (Q : Measure E)).real A)
        = ((((P : Measure E) - (Q : Measure E)).restrict A).real Set.univ) := by
            simp [Measure.real_def]
      _ = ((((P : Measure E).restrict A) - ((Q : Measure E).restrict A)).real Set.univ) := by
            rw [Measure.restrict_sub_eq_restrict_sub_restrict hA]
      _ = ((P : Measure E).restrict A).real Set.univ -
            ((Q : Measure E).restrict A).real Set.univ := by
            rw [Measure.real_def, Measure.real_def, Measure.real_def,
              Measure.sub_apply MeasurableSet.univ hA_le,
              ENNReal.toReal_sub_of_le (hA_le Set.univ) (measure_ne_top _ _)]
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
            simp
  have hnegAc :
      (((Q : Measure E) - (P : Measure E)).real Aᶜ) =
        (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ := by
    -- Proof comment: the complement is the Hahn positive set for the reversed pair.
    calc
      (((Q : Measure E) - (P : Measure E)).real Aᶜ)
        = ((((Q : Measure E) - (P : Measure E)).restrict Aᶜ).real Set.univ) := by
            simp [Measure.real_def]
      _ = ((((Q : Measure E).restrict Aᶜ) - ((P : Measure E).restrict Aᶜ)).real Set.univ) := by
            rw [Measure.restrict_sub_eq_restrict_sub_restrict hA.compl]
      _ = ((Q : Measure E).restrict Aᶜ).real Set.univ -
            ((P : Measure E).restrict Aᶜ).real Set.univ := by
            rw [Measure.real_def, Measure.real_def, Measure.real_def,
              Measure.sub_apply MeasurableSet.univ hAc_le,
              ENNReal.toReal_sub_of_le (hAc_le Set.univ) (measure_ne_top _ _)]
      _ = (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ := by
            simp
  have hposAc_zero : (((P : Measure E) - (Q : Measure E)).real Aᶜ) = 0 := by
    -- Proof comment: there is no positive residual of `P - Q` on the negative part.
    rw [measureReal_eq_zero_iff]
    exact Measure.sub_apply_eq_zero_of_restrict_le_restrict hAc_le hA.compl
  have hnegA_zero : (((Q : Measure E) - (P : Measure E)).real A) = 0 := by
    -- Proof comment: symmetrically, `Q - P` has no positive residual on `A`.
    rw [measureReal_eq_zero_iff]
    exact Measure.sub_apply_eq_zero_of_restrict_le_restrict hA_le hA
  have hposUniv :
      (((P : Measure E) - (Q : Measure E)).real Set.univ) =
        (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the whole positive variation is concentrated on `A`.
    have hcompl := measureReal_compl (μ := (P : Measure E) - (Q : Measure E)) hA
    linarith
  have hnegCompl :
      (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ =
        (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: both probability measures have total mass `1`, so complement deficit equals
    -- positive-part excess.
    rw [measureReal_compl (μ := (P : Measure E)) hA,
      measureReal_compl (μ := (Q : Measure E)) hA]
    simp
  have hnegUniv :
      (((Q : Measure E) - (P : Measure E)).real Set.univ) =
        (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the reversed residual is concentrated on the complement piece.
    have hcompl := measureReal_compl (μ := (Q : Measure E) - (P : Measure E)) hA
    linarith [hcompl, hnegA_zero, hnegAc, hnegCompl]
  have htvNorm :
      SignedMeasure.totalVariationNorm E
          ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
        (((P : Measure E) - (Q : Measure E)).real Set.univ) +
          (((Q : Measure E) - (P : Measure E)).real Set.univ) := by
    -- Proof comment: the Jordan decomposition of `P - Q` is the pair `(P - Q, Q - P)`.
    simpa [SignedMeasure.totalVariationNorm,
      Measure.toJordanDecomposition_toSignedMeasure_sub] using
      (SignedMeasure.totalVariation_real_univ_eq_jordan
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure))
  calc
    totalVariationDistance P Q
      = SignedMeasure.totalVariationNorm E
          ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2 := by
          rw [totalVariationDistance_eq_half_totalVariationNorm]
    _ = ((((P : Measure E) - (Q : Measure E)).real Set.univ) +
          (((Q : Measure E) - (P : Measure E)).real Set.univ)) / 2 := by
          rw [htvNorm]
    _ = (((P : Measure E).real A - (Q : Measure E).real A) +
          ((P : Measure E).real A - (Q : Measure E).real A)) / 2 := by
          rw [hposUniv, hnegUniv]
    _ = (P : Measure E).real A - (Q : Measure E).real A := by ring

/-- The Hahn sign test realizes exactly twice the excess mass on the positive part. -/
private theorem hahnSignIntegral_eq_doubleExcess
    (P Q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A) :
    ∫ x, (A.indicator (fun _ : E ↦ (1 : ℝ)) x - Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x)
        ∂(P : Measure E)
      - ∫ x, (A.indicator (fun _ : E ↦ (1 : ℝ)) x - Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x)
        ∂(Q : Measure E)
      = 2 * ((P : Measure E).real A - (Q : Measure E).real A) := by
  have hPA :
      Integrable (A.indicator (fun _ : E ↦ (1 : ℝ))) (P : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hPAc :
      Integrable (Aᶜ.indicator (fun _ : E ↦ (1 : ℝ))) (P : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  have hQA :
      Integrable (A.indicator (fun _ : E ↦ (1 : ℝ))) (Q : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hQAc :
      Integrable (Aᶜ.indicator (fun _ : E ↦ (1 : ℝ))) (Q : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  -- Proof comment: the sign test splits into two indicator integrals, which evaluate to the set
  -- masses of `A` and `Aᶜ`.
  rw [integral_sub hPA hPAc, integral_sub hQA hQAc]
  simp [measureReal_compl, hA]
  ring

/-- Every measurable real test function bounded by `1` is controlled by twice the Hahn excess
mass. -/
private theorem integral_sub_le_doubleHahnExcess
    (P Q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A)
    (hA_le : (Q : Measure E).restrict A ≤ (P : Measure E).restrict A)
    (hAc_le : (P : Measure E).restrict Aᶜ ≤ (Q : Measure E).restrict Aᶜ)
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) ≤
      2 * ((P : Measure E).real A - (Q : Measure E).real A) := by
  let ρ : Measure E := ((P : Measure E).restrict A) - (Q : Measure E).restrict A
  let σ : Measure E := ((Q : Measure E).restrict Aᶜ) - (P : Measure E).restrict Aᶜ
  have hIntP : Integrable f (P : Measure E) := integrable_of_bound_one hf_meas hf_bound
  have hIntQ : Integrable f (Q : Measure E) := integrable_of_bound_one hf_meas hf_bound
  have hIntQA : Integrable f ((Q : Measure E).restrict A) := integrable_of_bound_one hf_meas hf_bound
  have hIntPAc :
      Integrable f ((P : Measure E).restrict Aᶜ) := integrable_of_bound_one hf_meas hf_bound
  have hIntρ : Integrable f ρ := integrable_of_bound_one hf_meas hf_bound
  have hIntσ : Integrable f σ := integrable_of_bound_one hf_meas hf_bound
  have hsplitA :
      ∫ x in A, f x ∂(P : Measure E) - ∫ x in A, f x ∂(Q : Measure E) = ∫ x, f x ∂ρ := by
    -- Proof comment: on `A`, `P` is the sum of `Q` and the positive residual `ρ`.
    have hsum :
        ∫ x, f x ∂((P : Measure E).restrict A) =
          ∫ x, f x ∂ρ + ∫ x, f x ∂((Q : Measure E).restrict A) := by
      simpa [ρ, Measure.sub_add_cancel_of_le hA_le] using
        (integral_add_measure (μ := ρ) (ν := (Q : Measure E).restrict A) hIntρ hIntQA)
    rw [show ∫ x in A, f x ∂(P : Measure E) = ∫ x, f x ∂((P : Measure E).restrict A) by rfl,
      show ∫ x in A, f x ∂(Q : Measure E) = ∫ x, f x ∂((Q : Measure E).restrict A) by rfl,
      hsum]
    ring
  have hsplitAc :
      ∫ x in Aᶜ, f x ∂(P : Measure E) - ∫ x in Aᶜ, f x ∂(Q : Measure E) =
        -∫ x, f x ∂σ := by
    -- Proof comment: on `Aᶜ`, the reversed residual `σ` enters with a minus sign.
    have hsum :
        ∫ x, f x ∂((Q : Measure E).restrict Aᶜ) =
          ∫ x, f x ∂σ + ∫ x, f x ∂((P : Measure E).restrict Aᶜ) := by
      simpa [σ, Measure.sub_add_cancel_of_le hAc_le] using
        (integral_add_measure (μ := σ) (ν := (P : Measure E).restrict Aᶜ) hIntσ hIntPAc)
    rw [show ∫ x in Aᶜ, f x ∂(P : Measure E) = ∫ x, f x ∂((P : Measure E).restrict Aᶜ) by rfl,
      show ∫ x in Aᶜ, f x ∂(Q : Measure E) = ∫ x, f x ∂((Q : Measure E).restrict Aᶜ) by rfl,
      hsum]
    ring
  have hρ_mass : ρ.real Set.univ = (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the total mass of the positive residual on `A` is exactly the Hahn excess.
    calc
      ρ.real Set.univ
        = (((P : Measure E).restrict A) Set.univ - ((Q : Measure E).restrict A) Set.univ).toReal := by
            simp [ρ, Measure.real_def, Measure.sub_apply MeasurableSet.univ hA_le]
      _ = ((P : Measure E).restrict A).real Set.univ - ((Q : Measure E).restrict A).real Set.univ := by
            rw [ENNReal.toReal_sub_of_le (hA_le Set.univ) (measure_ne_top _ _),
              Measure.real_def, Measure.real_def]
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
            simp
  have hσ_mass : σ.real Set.univ = (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the complement residual has the same mass by probability normalization.
    calc
      σ.real Set.univ
        = (((Q : Measure E).restrict Aᶜ) Set.univ - ((P : Measure E).restrict Aᶜ) Set.univ).toReal := by
            simp [σ, Measure.real_def, Measure.sub_apply MeasurableSet.univ hAc_le]
      _ = (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ := by
            rw [ENNReal.toReal_sub_of_le (hAc_le Set.univ) (measure_ne_top _ _),
              Measure.real_def, Measure.real_def]
            simp [Measure.restrict_apply]
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
            rw [measureReal_compl (μ := (P : Measure E)) hA,
              measureReal_compl (μ := (Q : Measure E)) hA]
            simp
  have hρ_bound : ∫ x, f x ∂ρ ≤ (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the residual integral is bounded by the residual total mass.
    calc
      ∫ x, f x ∂ρ ≤ ‖∫ x, f x ∂ρ‖ := le_abs_self _
      _ ≤ 1 * ρ.real Set.univ := by
            simpa using
              (norm_integral_le_of_norm_le_const (μ := ρ) (C := 1) (ae_of_all _ hf_bound))
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
            rw [hρ_mass]
            ring
  have hσ_bound : -∫ x, f x ∂σ ≤ (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the complement residual is controlled by the same mass bound.
    calc
      -∫ x, f x ∂σ ≤ ‖∫ x, f x ∂σ‖ := by simpa using (neg_le_abs (∫ x, f x ∂σ))
      _ ≤ 1 * σ.real Set.univ := by
            simpa using
              (norm_integral_le_of_norm_le_const (μ := σ) (C := 1) (ae_of_all _ hf_bound))
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
            rw [hσ_mass]
            ring
  -- Proof comment: split the integral difference over `A` and `Aᶜ`, then bound the two residual
  -- pieces separately.
  calc
    ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)
      = (∫ x in A, f x ∂(P : Measure E) - ∫ x in A, f x ∂(Q : Measure E)) +
          (∫ x in Aᶜ, f x ∂(P : Measure E) - ∫ x in Aᶜ, f x ∂(Q : Measure E)) := by
            rw [← integral_add_compl hA hIntP, ← integral_add_compl hA hIntQ]
            ring
    _ = ∫ x, f x ∂ρ + (-∫ x, f x ∂σ) := by rw [hsplitA, hsplitAc]
    _ ≤ ((P : Measure E).real A - (Q : Measure E).real A) +
          ((P : Measure E).real A - (Q : Measure E).real A) := by
            linarith
    _ = 2 * ((P : Measure E).real A - (Q : Measure E).real A) := by ring

/-- The total variation distance is half of the supremum of the signed integral difference over
measurable real-valued test functions bounded in absolute value by `1`. -/
theorem totalVariationDistance_eq_sSup_bounded_measurable
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      sSup {r : ℝ | ∃ f : E → ℝ,
        Measurable f ∧
          (∀ x, ‖f x‖ ≤ 1) ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} / 2 := by
  let S : Set ℝ := {r : ℝ | ∃ f : E → ℝ,
    Measurable f ∧
      (∀ x, ‖f x‖ ≤ 1) ∧
      r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}
  obtain ⟨A, hA⟩ := MeasureTheory.exists_isHahnDecomposition (Q : Measure E) (P : Measure E)
  have htv :
      totalVariationDistance P Q = (P : Measure E).real A - (Q : Measure E).real A :=
    hahnExcess_eq_totalVariationDistance P Q hA.measurableSet hA.le_on hA.ge_on_compl
  have hupper : ∀ {r : ℝ}, r ∈ S → r ≤ 2 * ((P : Measure E).real A - (Q : Measure E).real A) := by
    intro r hr
    rcases hr with ⟨f, hf_meas, hf_bound, rfl⟩
    exact integral_sub_le_doubleHahnExcess P Q hA.measurableSet hA.le_on hA.ge_on_compl hf_meas hf_bound
  have hS_bddAbove : BddAbove S := ⟨2 * ((P : Measure E).real A - (Q : Measure E).real A),
    fun r hr ↦ hupper hr⟩
  have hsign_meas :
      Measurable
        (fun x : E ↦
          A.indicator (fun _ : E ↦ (1 : ℝ)) x - Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x) := by
    -- Proof comment: both indicator constants are measurable on the Hahn partition.
    exact (Measurable.indicator measurable_const hA.measurableSet).sub
      (Measurable.indicator measurable_const hA.measurableSet.compl)
  have hsign_bound :
      ∀ x : E,
        ‖A.indicator (fun _ : E ↦ (1 : ℝ)) x - Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x‖ ≤ 1 := by
    -- Proof comment: the sign test only takes the values `1` and `-1`.
    intro x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx]
  have hsign_mem : 2 * ((P : Measure E).real A - (Q : Measure E).real A) ∈ S := by
    -- Proof comment: the Hahn sign test attains the upper bound exactly.
    refine ⟨fun x : E ↦
      A.indicator (fun _ : E ↦ (1 : ℝ)) x - Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x,
      hsign_meas, hsign_bound, ?_⟩
    exact (hahnSignIntegral_eq_doubleExcess P Q hA.measurableSet).symm
  have hS_nonempty : S.Nonempty := ⟨2 * ((P : Measure E).real A - (Q : Measure E).real A), hsign_mem⟩
  have hlower : totalVariationDistance P Q ≤ sSup S / 2 := by
    -- Proof comment: the sign witness shows that the supremum is at least `2 * TV`.
    rw [htv]
    have hsSup_ge : 2 * ((P : Measure E).real A - (Q : Measure E).real A) ≤ sSup S :=
      le_csSup hS_bddAbove hsign_mem
    linarith
  have hupper' : sSup S / 2 ≤ totalVariationDistance P Q := by
    -- Proof comment: every bounded measurable witness is controlled by the same Hahn excess.
    rw [htv]
    have hsSup_le : sSup S ≤ 2 * ((P : Measure E).real A - (Q : Measure E).real A) := by
      exact csSup_le hS_nonempty fun r hr ↦ hupper hr
    linarith
  exact le_antisymm hlower hupper'

end TotalVariation

end ProbabilityTheory
