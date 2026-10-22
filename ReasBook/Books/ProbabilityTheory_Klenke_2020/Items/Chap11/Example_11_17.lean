/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Equation_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasurableSpace

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
variable {μ ν : Measure Ω}

/-- The textbook finite-atom approximation process for the Radon-Nikodym density: at stage `n`,
the value at `x` is the quotient of the `ν`-mass and `μ`-mass of the atom `Zₙ(x)` of the finite
partition underlying `countableFiltration Ω n`. -/
noncomputable
def countable_filtration_rn_deriv_process (μ ν : Measure Ω) : ℕ → Ω → ℝ :=
  fun n x ↦ (ν (countablePartitionSet n x) / μ (countablePartitionSet n x)).toReal

private theorem countable_filtration_rn_deriv_process_eq_on_atom
    (μ ν : Measure Ω) (n : ℕ) {s : Set Ω} (hs : s ∈ countablePartition Ω n) {x : Ω} (hx : x ∈ s) :
    countable_filtration_rn_deriv_process μ ν n x = (ν s / μ s).toReal := by
  simp [countable_filtration_rn_deriv_process, countablePartitionSet_of_mem hs hx]

private theorem countable_filtration_rn_deriv_process_eq_partition_formula
    (μ ν : Measure Ω) (n : ℕ) :
    countable_filtration_rn_deriv_process μ ν n =
      fun x ↦
        ∑' s : countablePartition Ω n,
          (s : Set Ω).indicator (fun _ ↦ (ν (s : Set Ω) / μ (s : Set Ω)).toReal) x := by
  classical
  funext x
  let sx : countablePartition Ω n := ⟨countablePartitionSet n x, countablePartitionSet_mem n x⟩
  letI := Fintype.ofFinite (countablePartition Ω n)
  rw [tsum_fintype, Finset.sum_eq_single sx]
  · simp [sx, countable_filtration_rn_deriv_process, mem_countablePartitionSet]
  · intro s hs hs_ne
    have hdisj :
        Disjoint (s : Set Ω) (sx : Set Ω) :=
      disjoint_countablePartition s.prop sx.prop fun h ↦ hs_ne (Subtype.ext h)
    have hx_not_mem : x ∉ (s : Set Ω) := by
      intro hx_mem
      exact hdisj.le_bot ⟨hx_mem, mem_countablePartitionSet n x⟩
    simp [hx_not_mem]
  · intro hsx_not_mem
    exact (hsx_not_mem (Finset.mem_univ sx)).elim

private theorem atom_coeff_eq_setAverage_toReal_rnDeriv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (n : ℕ)
    (s : countablePartition Ω n) :
    (ν (s : Set Ω) / μ (s : Set Ω)).toReal =
      ⨍ x in (s : Set Ω), (ν.rnDeriv μ x).toReal ∂μ := by
  have hs_meas : MeasurableSet (s : Set Ω) := measurableSet_countablePartition n s.prop
  have h_integral :
      ∫ x in (s : Set Ω), (ν.rnDeriv μ x).toReal ∂μ = ν.real (s : Set Ω) := by
    simpa using Measure.setIntegral_toReal_rnDeriv hνμ (s : Set Ω)
  calc
    (ν (s : Set Ω) / μ (s : Set Ω)).toReal = ν.real (s : Set Ω) / μ.real (s : Set Ω) := by
      simp [measureReal_def, ENNReal.toReal_div]
    _ = (μ.real (s : Set Ω))⁻¹ * ν.real (s : Set Ω) := by
      rw [div_eq_mul_inv, mul_comm]
    _ = ⨍ x in (s : Set Ω), (ν.rnDeriv μ x).toReal ∂μ := by
      rw [setAverage_eq, h_integral, smul_eq_mul, mul_comm]

private theorem countable_filtration_rn_deriv_process_eq_partition_average_formula
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (n : ℕ) :
    countable_filtration_rn_deriv_process μ ν n =
      fun x ↦
        ∑' s : countablePartition Ω n,
          (s : Set Ω).indicator
            (fun _ ↦ ⨍ y in (s : Set Ω), (ν.rnDeriv μ y).toReal ∂μ) x := by
  simpa [atom_coeff_eq_setAverage_toReal_rnDeriv hνμ n] using
    countable_filtration_rn_deriv_process_eq_partition_formula μ ν n

/-- The finite-atom approximation process agrees almost everywhere with the canonical conditional
expectation of the Radon-Nikodym density onto the finite stage `countableFiltration Ω n`. -/
theorem countable_filtration_rn_deriv_process_ae_eq_condExp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (n : ℕ) :
    countable_filtration_rn_deriv_process μ ν n =ᵐ[μ]
      μ[fun x ↦ (ν.rnDeriv μ x).toReal | countableFiltration Ω n] := by
  let g : Ω → ℝ := fun x ↦ (ν.rnDeriv μ x).toReal
  have h_partition :
      μ[g | countableFiltration Ω n] =ᵐ[μ]
        fun x ↦
          ∑' s : countablePartition Ω n,
            (s : Set Ω).indicator (fun _ ↦ ⨍ y in (s : Set Ω), g y ∂μ) x := by
    simpa [countableFiltration, g] using
      (condExp_generateFrom_ae_eq_countable_partition_formula
        μ (fun s : countablePartition Ω n ↦ (s : Set Ω))
        (fun s ↦ measurableSet_countablePartition n s.prop)
        (fun s t hst ↦ disjoint_countablePartition s.prop t.prop fun h ↦ hst (Subtype.ext h))
        (by
          ext x
          constructor
          · intro _
            simp
          · intro _
            exact Set.mem_iUnion.2
              ⟨⟨countablePartitionSet n x, countablePartitionSet_mem n x⟩,
                mem_countablePartitionSet n x⟩)
        Measure.integrable_toReal_rnDeriv)
  simpa [g, countable_filtration_rn_deriv_process_eq_partition_average_formula hνμ n] using
    h_partition.symm

/-- The canonical conditional-expectation description of the finite-atom approximants agrees
almost everywhere with the trimmed Radon-Nikodym derivatives on the finite stage. -/
theorem countable_filtration_rn_deriv_process_ae_eq_trimmed_rnDeriv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (n : ℕ) :
    countable_filtration_rn_deriv_process μ ν n =ᵐ[μ]
      fun x ↦
        (((ν.trim ((countableFiltration Ω).le n)).rnDeriv
          (μ.trim ((countableFiltration Ω).le n)) x).toReal) := by
  exact
    (countable_filtration_rn_deriv_process_ae_eq_condExp hνμ n).trans
      (ae_eq_of_ae_eq_trim
        (toReal_rnDeriv_trim ((countableFiltration Ω).le n) hνμ)).symm

/-- Example 11.17: on a countably generated probability space, the finite-partition density process
associated with `ν` and `μ` converges `μ`-almost surely to the Radon-Nikodym density `dν/dμ`. -/
theorem ae_tendsto_countable_filtration_rn_deriv_process
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ countable_filtration_rn_deriv_process μ ν n x) atTop
        (nhds ((ν.rnDeriv μ x).toReal)) := by
  have h_int : Integrable (fun x ↦ (ν.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv
  have h_meas :
      StronglyMeasurable[⨆ n, countableFiltration Ω n] fun x ↦ (ν.rnDeriv μ x).toReal := by
    rw [iSup_countableFiltration Ω]
    exact (Measure.measurable_rnDeriv ν μ).ennreal_toReal.stronglyMeasurable
  have h_eq :
      ∀ᵐ x ∂μ, ∀ n,
        countable_filtration_rn_deriv_process μ ν n x =
          μ[fun x ↦ (ν.rnDeriv μ x).toReal | countableFiltration Ω n] x := by
    rw [ae_all_iff]
    intro n
    exact countable_filtration_rn_deriv_process_ae_eq_condExp hνμ n
  filter_upwards [h_eq, h_int.tendsto_ae_condExp h_meas] with x hx hcond
  simpa [hx] using hcond

/-- The finite-partition density process converges in `L¹(μ)` to the Radon-Nikodym density. -/
theorem tendsto_eLpNorm_one_countable_filtration_rn_deriv_process
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    Tendsto
      (fun n ↦
        eLpNorm
          (countable_filtration_rn_deriv_process μ ν n - fun x ↦ (ν.rnDeriv μ x).toReal)
          1 μ)
      atTop (nhds 0) := by
  have h_int : Integrable (fun x ↦ (ν.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv
  have h_meas :
      StronglyMeasurable[⨆ n, countableFiltration Ω n] fun x ↦ (ν.rnDeriv μ x).toReal := by
    rw [iSup_countableFiltration Ω]
    exact (Measure.measurable_rnDeriv ν μ).ennreal_toReal.stronglyMeasurable
  have h_norm :
      ∀ n,
        eLpNorm
            (countable_filtration_rn_deriv_process μ ν n - fun x ↦ (ν.rnDeriv μ x).toReal)
            1 μ =
          eLpNorm
            (μ[fun x ↦ (ν.rnDeriv μ x).toReal | countableFiltration Ω n] -
              fun x ↦ (ν.rnDeriv μ x).toReal)
            1 μ := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards
      [countable_filtration_rn_deriv_process_ae_eq_condExp hνμ n] with x hx
    simp [hx]
  simpa [h_norm] using h_int.tendsto_eLpNorm_condExp h_meas

end MeasureTheory
