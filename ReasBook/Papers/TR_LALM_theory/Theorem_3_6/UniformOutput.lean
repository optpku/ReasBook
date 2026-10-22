/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Uniform
public import TR_LALM_theory.Definition_3_2
public import TR_LALM_theory.Lemma_3_3.Iteration

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.StochasticRun

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

namespace UniformOutput

variable {Q B b : ℕ+}

/-- The uniform law on the output indices `1, …, K - 1`. -/
@[expose] noncomputable def indexLaw (K : ℕ) (hK : 2 ≤ K) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.Icc 1 (K - 1))
    (Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK))

/-- The output-index law is the canonical uniform law on `Finset.Icc 1 (K - 1)`. -/
theorem indexLaw_def (K : ℕ) (hK : 2 ≤ K) :
    indexLaw K hK =
      PMF.uniformOfFinset (Finset.Icc 1 (K - 1))
        (Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK)) := rfl

/-- The product probability measure realizing an independent selector uniform
on `Finset.Icc 1 (K - 1)` and an original stochastic-run sample. -/
@[expose] noncomputable def measure (K : ℕ) (hK : 2 ≤ K) (ℙ : Measure Ω) :
    Measure (ℕ × Ω) :=
  (indexLaw K hK).toMeasure.prod ℙ

/-- The uniform-output measure is the product of the finite uniform law and `ℙ`. -/
theorem measure_def (K : ℕ) (hK : 2 ≤ K) (ℙ : Measure Ω) :
    measure K hK ℙ =
      (PMF.uniformOfFinset (Finset.Icc 1 (K - 1))
        (Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK))).toMeasure.prod ℙ := rfl

/-- The uniform-output product measure is a probability measure. -/
noncomputable instance isProbabilityMeasure (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (measure K hK ℙ) := by
  change IsProbabilityMeasure ((indexLaw K hK).toMeasure.prod ℙ)
  infer_instance

/-- The selected stochastic primal point at the successor of the uniform index. -/
@[expose] def point (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) :
    ℕ × Ω → EuclideanSpace ℝ (Fin n) :=
  fun output ↦ run.point (output.1 + 1) output.2

/-- The selected stochastic multiplier at the successor of the uniform index. -/
@[expose] def multiplier (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) :
    ℕ × Ω → EuclideanSpace ℝ (Fin m) :=
  fun output ↦ run.multiplier (output.1 + 1) output.2

/-- The output point is the run point at the successor of the selected index. -/
theorem point_apply
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (output : ℕ × Ω) :
    point run output = run.point (output.1 + 1) output.2 := rfl

/-- The output multiplier is the run multiplier at the successor of the selected index. -/
theorem multiplier_apply
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (output : ℕ × Ω) :
    multiplier run output = run.multiplier (output.1 + 1) output.2 := rfl

/-- The output-law support condition for Theorem 3.6: every primal point that
can be selected by the finite uniform index lies in the regularity region almost
surely. -/
def HasRegularOutputPoints
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ᵐ ω ∂ℙ, ∀ k ∈ Finset.Icc 1 (K - 1), run.point (k + 1) ω ∈ h.region

/-- Almost-sure prefix admissibility supplies the output support condition used
in Theorem 3.6. -/
theorem hasRegularOutputPoints_of_isAEAdmissiblePrefix
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAEAdmissiblePrefix K) :
    HasRegularOutputPoints run K := by
  have hAdmissibleAE := (run.isAEAdmissiblePrefix_iff K).mp h_admissible
  filter_upwards [hAdmissibleAE] with ω hω
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  have hkLt : k < K := by
    omega
  exact hω k hkLt (right_mem_segment ℝ (run.point k ω) (run.point (k + 1) ω))

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Theorem 3.6: countably many almost-everywhere measurable
sections assemble into an almost-everywhere measurable function on a product
space. -/
private lemma aemeasurableIndexedProduct
    {E : Type*} [MeasurableSpace E] (μ : Measure ℕ)
    (g : ℕ → Ω → E) (hg : ∀ k, AEMeasurable (g k) ℙ) :
    AEMeasurable (fun output : ℕ × Ω ↦ g output.1 output.2) (μ.prod ℙ) := by
  let g' : ℕ → Ω → E := fun k ↦ (hg k).mk (g k)
  have hg'Measurable (k : ℕ) : Measurable (g' k) :=
    (hg k).measurable_mk
  have hglobalMeasurable :
      Measurable (fun output : ℕ × Ω ↦ g' output.1 output.2) :=
    measurable_from_prod_countable_right hg'Measurable
  have hsections : ∀ᵐ ω ∂ℙ, ∀ k, g' k ω = g k ω := by
    apply ae_all_iff.mpr
    intro k
    exact (hg k).ae_eq_mk.symm
  have hlifted :
      ∀ᵐ output ∂μ.prod ℙ, ∀ k, g' k output.2 = g k output.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ℙ)).ae hsections
  have hglobalAE :
      (fun output : ℕ × Ω ↦ g' output.1 output.2) =ᵐ[μ.prod ℙ]
        fun output ↦ g output.1 output.2 := by
    filter_upwards [hlifted] with output houtput
    exact houtput output.1
  exact hglobalMeasurable.aemeasurable.congr hglobalAE

/-- The first product coordinate has the finite uniform law on the output range. -/
theorem index_hasLaw (K : ℕ) (hK : 2 ≤ K) :
    ProbabilityTheory.HasLaw (fun output : ℕ × Ω ↦ output.1)
      (indexLaw K hK).toMeasure (measure K hK ℙ) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [measure, Measure.map_fst_prod, measure_univ, one_smul]

/-- The uniform selector is independent of the entire lifted oracle-sample family. -/
theorem index_indep_sample
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) :
    ProbabilityTheory.IndepFun
      (fun output : ℕ × Ω ↦ output.1)
      (fun output : ℕ × Ω ↦ fun ki : ℕ × ℕ ↦ run.sample ki.1 ki.2 output.2)
      (measure K hK ℙ) := by
  have hfamily :
      AEMeasurable
        (fun ω ↦ fun ki : ℕ × ℕ ↦ run.sample ki.1 ki.2 ω) ℙ :=
    aemeasurable_pi_lambda _ fun ki ↦
      (run.hasLaw_sample ki.1 ki.2).aemeasurable
  change ProbabilityTheory.IndepFun
    (fun output : ℕ × Ω ↦ id output.1)
    (fun output : ℕ × Ω ↦
      (fun ω ↦ fun ki : ℕ × ℕ ↦ run.sample ki.1 ki.2 ω) output.2)
    ((indexLaw K hK).toMeasure.prod ℙ)
  exact ProbabilityTheory.indepFun_prod₀ measurable_id.aemeasurable hfamily

/-- The expected squared KKT residual of the uniform independent output pair. -/
@[expose] noncomputable def residualMeanSquare
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) : ℝ≥0∞ :=
  KKT.Stochastic.residualMeanSquare (measure K hK ℙ) f c
    (point run) (multiplier run)

/-- The output residual mean square is the canonical stochastic KKT residual mean square. -/
theorem residualMeanSquare_def
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) :
    residualMeanSquare run K hK =
      KKT.Stochastic.residualMeanSquare (measure K hK ℙ) f c
        (point run) (multiplier run) := rfl

/-- The product-law residual mean square equals the uniform finite expectation
of the fixed-index residual mean squares. -/
theorem residualMeanSquare_eq_expect
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_support : HasRegularOutputPoints run K) :
    residualMeanSquare run K hK =
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1))) /
        (Finset.Icc 1 (K - 1)).card := by
  let s := Finset.Icc 1 (K - 1)
  let p := indexLaw K hK
  let residualSquare : ℕ → Ω → ℝ≥0∞ := fun k ω ↦
    ENNReal.ofReal
      (KKT.residualExtension h
        (run.point (k + 1) ω, run.multiplier (k + 1) ω) ^ 2)
  have hResidualSquare (k : ℕ) : AEMeasurable (residualSquare k) ℙ := by
    have hpair :
        AEMeasurable
          (fun ω ↦ (run.point (k + 1) ω, run.multiplier (k + 1) ω)) ℙ :=
      (run.aemeasurable_point (k + 1)).prodMk
        (run.aemeasurable_multiplier (k + 1))
    have hresidual :=
      (KKT.measurable_residualExtension h).comp_aemeasurable hpair
    exact hresidual.pow_const 2 |>.ennreal_ofReal
  have hglobal :
      AEMeasurable
        (fun output : ℕ × Ω ↦ residualSquare output.1 output.2)
        (p.toMeasure.prod ℙ) :=
    aemeasurableIndexedProduct p.toMeasure residualSquare hResidualSquare
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ s := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hk' : k ∉ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hpZero : p k = 0 := by
      simp only [p, indexLaw, PMF.uniformOfFinset_apply, if_neg hk']
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ, output.1 ∈ s :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := ℙ)).ae hpSupport
  have hrunSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ,
        ∀ k ∈ Finset.Icc 1 (K - 1),
          run.point (k + 1) output.2 ∈ h.region :=
    (Measure.quasiMeasurePreserving_snd (μ := p.toMeasure) (ν := ℙ)).ae h_support
  have hresidualEq :
      (fun output : ℕ × Ω ↦ ENNReal.ofReal
        (KKT.residual f c (run.point (output.1 + 1) output.2)
          (run.multiplier (output.1 + 1) output.2) ^ 2)) =ᵐ[p.toMeasure.prod ℙ]
        fun output ↦ residualSquare output.1 output.2 := by
    filter_upwards [hpSupportLifted, hrunSupportLifted] with output hk houtput
    have hk' : output.1 ∈ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hextension :
        KKT.residualExtension h
            (run.point (output.1 + 1) output.2,
              run.multiplier (output.1 + 1) output.2) =
          KKT.residual f c (run.point (output.1 + 1) output.2)
            (run.multiplier (output.1 + 1) output.2) :=
      KKT.residualExtension_eq h (houtput output.1 hk')
    simp only [residualSquare, hextension]
  rw [residualMeanSquare_def, KKT.Stochastic.residualMeanSquare_def]
  change (∫⁻ output : ℕ × Ω,
    ENNReal.ofReal
      (KKT.residual f c (run.point (output.1 + 1) output.2)
        (run.multiplier (output.1 + 1) output.2) ^ 2)
      ∂p.toMeasure.prod ℙ) = _
  rw [lintegral_congr_ae hresidualEq]
  change (∫⁻ output : ℕ × Ω,
    residualSquare output.1 output.2 ∂p.toMeasure.prod ℙ) = _
  rw [lintegral_prod _ hglobal, lintegral_countable']
  simp_rw [PMF.toMeasure_apply_singleton p _ (MeasurableSet.singleton _)]
  have hp (k : ℕ) :
      p k = if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
    change (PMF.uniformOfFinset s _) k = _
    by_cases hk : k ∈ s
    · simp only [PMF.uniformOfFinset_apply, if_pos hk]
    · simp only [PMF.uniformOfFinset_apply, if_neg hk]
  have hsectionEq (k : ℕ) (hk : k ∈ s) :
      (∫⁻ ω, residualSquare k ω ∂ℙ) =
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1)) := by
    have hk' : k ∈ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    rw [KKT.Stochastic.residualMeanSquare_def]
    apply lintegral_congr_ae
    filter_upwards [h_support] with ω hω
    have hextension :
        KKT.residualExtension h
            (run.point (k + 1) ω, run.multiplier (k + 1) ω) =
          KKT.residual f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω) :=
      KKT.residualExtension_eq h (hω k hk')
    simp only [residualSquare, hextension]
  have hsumResidual :
      (∑ k ∈ s, ∫⁻ ω, residualSquare k ω ∂ℙ) =
        ∑ k ∈ s, KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hsectionEq k hk
  simp_rw [hp]
  rw [tsum_eq_sum (s := s)]
  · have hsum :
        (∑ k ∈ s, (∫⁻ ω, residualSquare k ω ∂ℙ) *
          (if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0)) =
          ∑ k ∈ s,
            (∫⁻ ω, residualSquare k ω ∂ℙ) *
              (s.card : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos hk]
    rw [hsum, ← Finset.sum_mul, hsumResidual]
    simp only [ENNReal.div_eq_inv_mul, mul_comm]
    dsimp only [s]
  · intro k hk
    rw [if_neg hk, mul_zero]

end UniformOutput

end LALM.StochasticRun

end

open LALM.StochasticRun
