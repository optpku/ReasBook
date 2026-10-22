/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticMoments
public import Mathlib.Probability.Independence.Integration

public section

open MeasureTheory

namespace LALM.Correction.StochasticRun.EstimatorProbability

universe u v w x

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}

theorem independentPair_integrable_integral_le
    {A : Type w} {D : Type x} [MeasurableSpace A] [MeasurableSpace D]
    (X : Ω → A) (Y : Ω → D) (φ : A × D → ℝ) (C : A → ℝ)
    (h_independent : ProbabilityTheory.IndepFun X Y P)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hφ : AEMeasurable φ ((P.map X).prod (P.map Y)))
    (hφ_nonnegative : ∀ z, 0 ≤ φ z)
    (hsection : ∀ᵐ a ∂P.map X, Integrable (fun d ↦ φ (a, d)) (P.map Y))
    (hC : Integrable C (P.map X))
    (hbound : ∀ᵐ a ∂P.map X, (∫ d, φ (a, d) ∂P.map Y) ≤ C a) :
    Integrable (fun ω ↦ φ (X ω, Y ω)) P ∧
      (∫ ω, φ (X ω, Y ω) ∂P) ≤ ∫ a, C a ∂P.map X := by
  have hφStrong := hφ.aestronglyMeasurable
  have hinnerMeasurable : AEStronglyMeasurable
      (fun a ↦ ∫ d, ‖φ (a, d)‖ ∂P.map Y) (P.map X) :=
    hφStrong.norm.integral_prod_right'
  have hinnerIntegrable : Integrable
      (fun a ↦ ∫ d, ‖φ (a, d)‖ ∂P.map Y) (P.map X) := by
    apply Integrable.mono' hC hinnerMeasurable
    exact hbound.mono fun a ha ↦ by
      have hinnerNonnegative : 0 ≤ ∫ d, ‖φ (a, d)‖ ∂P.map Y :=
        integral_nonneg fun d ↦ norm_nonneg _
      have hnormIntegral :
          (∫ d, ‖φ (a, d)‖ ∂P.map Y) = ∫ d, φ (a, d) ∂P.map Y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun d ↦ by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hφ_nonnegative (a, d))]
      rw [Real.norm_eq_abs, abs_of_nonneg hinnerNonnegative, hnormIntegral]
      exact ha
  have hprod : Integrable φ ((P.map X).prod (P.map Y)) := by
    exact (integrable_prod_iff hφStrong).2
      ⟨hsection, hinnerIntegrable⟩
  have hpairMeasurable : AEMeasurable (fun ω ↦ (X ω, Y ω)) P := hX.prodMk hY
  have hmap :
      P.map (fun ω ↦ (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    h_independent.map_prod_eq_prod_map_map hX hY
  have hφMap : AEStronglyMeasurable φ (P.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hφStrong
  have hprodMap : Integrable φ (P.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hprod
  have hcomp : Integrable (fun ω ↦ φ (X ω, Y ω)) P :=
    (integrable_map_measure hφMap hpairMeasurable).1 hprodMap
  refine ⟨hcomp, ?_⟩
  calc
    (∫ ω, φ (X ω, Y ω) ∂P) =
        ∫ z, φ z ∂P.map (fun ω ↦ (X ω, Y ω)) := by
      exact (integral_map hpairMeasurable hφMap).symm
    _ = ∫ z, φ z ∂(P.map X).prod (P.map Y) := by rw [hmap]
    _ = ∫ a, ∫ d, φ (a, d) ∂P.map Y ∂P.map X := integral_prod φ hprod
    _ ≤ ∫ a, C a ∂P.map X :=
      integral_mono_ae hprod.integral_prod_left hC
        hbound

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure P] in
/-- Helper for Corollary 4.2: the mean square of an average of independent,
identically distributed centered Euclidean vectors is at most the common
second-moment bound divided by the batch size. -/
theorem independentBatchMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν P)
    (hindependent : ProbabilityTheory.iIndepFun sample P)
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = 0)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) P ∧
      (∫ ω, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂P) ≤
          secondMoment / (batch : ℝ) := by
  classical
  have hvalueRandom (i : ℕ) : Integrable (fun ω ↦ value (sample i ω)) P := by
    have hmap : Integrable value (P.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hsquareRandom (i : ℕ) :
      Integrable (fun ω ↦ ‖value (sample i ω)‖ ^ 2) P := by
    have hmap : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) (P.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) : (∫ ω, value (sample i ω) ∂P) = 0 := by
    -- Transport the centering identity along the common sample law.
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsecondRandom (i : ℕ) :
      (∫ ω, ‖value (sample i ω)‖ ^ 2 ∂P) ≤ secondMoment := by
    calc
      (∫ ω, ‖value (sample i ω)‖ ^ 2 ∂P) =
          ∫ ξ, ‖value ξ‖ ^ 2 ∂ν := by
        simpa only [Function.comp_apply] using
          (hlaw i).integral_comp hsquare.aestronglyMeasurable
      _ ≤ secondMoment := hsecond
  have hindependentValue :
      ProbabilityTheory.iIndepFun (fun i ω ↦ value (sample i ω)) P := by
    apply hindependent.comp₀ (fun _ ↦ value)
    · exact fun i ↦ (hlaw i).aemeasurable
    · intro i
      rw [(hlaw i).map_eq]
      exact hvalue.aemeasurable
  have hcrossIntegrable (i j : ℕ) :
      Integrable (fun ω ↦ inner ℝ (value (sample i ω)) (value (sample j ω))) P := by
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hsquareRandom i
    · have hbilinear := (hindependentValue.indepFun hij).integrable_bilin
        (hvalueRandom i) (hvalueRandom j)
        (innerSL ℝ)
      exact hbilinear.congr (Filter.Eventually.of_forall fun ω ↦
        innerSL_apply_apply ℝ (value (sample i ω)) (value (sample j ω)))
  have hcrossIntegral (i j : ℕ) (hij : i ≠ j) :
      (∫ ω, inner ℝ (value (sample i ω)) (value (sample j ω)) ∂P) = 0 := by
    have hbilinear := (hindependentValue.indepFun hij).integral_bilin
      (hvalueRandom i) (hvalueRandom j)
      (innerSL ℝ)
    calc
      (∫ ω, inner ℝ (value (sample i ω)) (value (sample j ω)) ∂P) =
          ∫ ω, innerSL ℝ (value (sample i ω)) (value (sample j ω)) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦
          (innerSL_apply_apply ℝ
            (value (sample i ω)) (value (sample j ω))).symm
      _ = innerSL ℝ (∫ ω, value (sample i ω) ∂P)
            (∫ ω, value (sample j ω) ∂P) := hbilinear
      _ =
          inner ℝ (∫ ω, value (sample i ω) ∂P)
            (∫ ω, value (sample j ω) ∂P) := by
        exact innerSL_apply_apply ℝ _ _
      _ = 0 := by rw [hmeanRandom i, hmeanRandom j, inner_zero_left]
  have havgIdentity (ω : Ω) :
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) := by
    -- Bilinearity expands the squared norm into diagonal and cross terms.
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_smul_left, inner_smul_right, inner_sum, sum_inner,
      starRingEnd_apply, star_trivial]
    calc
      (batch : ℝ)⁻¹ * ∑ i ∈ Finset.range batch,
          (batch : ℝ)⁻¹ * ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) =
          ∑ i ∈ Finset.range batch,
            (batch : ℝ)⁻¹ * ((batch : ℝ)⁻¹ *
              ∑ j ∈ Finset.range batch,
                inner ℝ (value (sample j ω)) (value (sample i ω))) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range batch, (batch : ℝ)⁻¹ ^ 2 *
            ∑ j ∈ Finset.range batch,
              inner ℝ (value (sample j ω)) (value (sample i ω)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) := by
        symm
        rw [Finset.mul_sum]
  have hdoubleIntegrable : Integrable (fun ω ↦
      ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
        inner ℝ (value (sample j ω)) (value (sample i ω))) P := by
    exact integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i
  have havgIntegrable : Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) P := by
    exact ((hdoubleIntegrable.const_mul ((batch : ℝ)⁻¹ ^ 2)).congr
      (Filter.Eventually.of_forall fun ω ↦ (havgIdentity ω).symm))
  refine ⟨havgIntegrable, ?_⟩
  -- Cross terms vanish by independence and centering; only one second moment
  -- remains for each of the `batch` diagonal terms.
  calc
    (∫ ω, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂P) =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            ∫ ω, inner ℝ (value (sample j ω)) (value (sample i ω)) ∂P := by
      rw [integral_congr_ae (Filter.Eventually.of_forall havgIdentity),
        integral_const_mul, integral_finsetSum _ (fun i _ ↦
          integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i)]
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ ↦ hcrossIntegrable j i)]
    _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch,
            ∫ ω, ‖value (sample i ω)‖ ^ 2 ∂P := by
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦
          real_inner_self_eq_norm_sq (value (sample i ω))
      · intro j hj hji
        exact hcrossIntegral j i hji
      · exact fun hiMissing ↦ (hiMissing hi).elim
    _ ≤ (batch : ℝ)⁻¹ ^ 2 *
          ∑ _i ∈ Finset.range batch, secondMoment := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ hsecondRandom i) (sq_nonneg _)
    _ = secondMoment / (batch : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hbatch : (batch : ℝ) ≠ 0 := by positivity
      field_simp

omit [IsProbabilityMeasure ν] in
/-- Helper for Corollary 4.2: adding a deterministic vector to a centered batch
average adds exactly its squared norm to the batch mean square. -/
theorem independentBatchShiftedMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν P)
    (hindependent : ProbabilityTheory.iIndepFun sample P)
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = 0)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment)
    (a : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ω ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) P ∧
      (∫ ω, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂P) ≤
          ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
  classical
  let average : Ω → EuclideanSpace ℝ (Fin n) := fun ω ↦
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)
  have hvalueRandom (i : ℕ) : Integrable (fun ω ↦ value (sample i ω)) P := by
    have hmap : Integrable value (P.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) : (∫ ω, value (sample i ω) ∂P) = 0 := by
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsum : Integrable
      (fun ω ↦ ∑ i ∈ Finset.range batch, value (sample i ω)) P :=
    integrable_finsetSum _ fun i _ ↦ hvalueRandom i
  have haverage : Integrable average P := by
    unfold average
    change Integrable
      ((batch : ℝ)⁻¹ •
        (fun ω ↦ ∑ i ∈ Finset.range batch, value (sample i ω))) P
    exact hsum.smul ((batch : ℝ)⁻¹)
  have haverageMean : (∫ ω, average ω ∂P) = 0 := by
    simp only [average]
    rw [integral_smul, integral_finsetSum _ (fun i _ ↦ hvalueRandom i)]
    simp only [hmeanRandom, Finset.sum_const_zero, smul_zero]
  have hbatch := independentBatchMeanSquare_le value sample batch hlaw hindependent
    hvalue hmean hsquare secondMoment hsecond
  have haverageSquare : Integrable (fun ω ↦ ‖average ω‖ ^ 2) P := by
    simpa only [average] using hbatch.1
  have hinner : Integrable (fun ω ↦ inner ℝ a (average ω)) P :=
    haverage.const_inner a
  have hexpanded : Integrable (fun ω ↦
      ‖a‖ ^ 2 + 2 * inner ℝ a (average ω) + ‖average ω‖ ^ 2) P :=
    ((integrable_const _).add (hinner.const_mul 2)).add haverageSquare
  have hshifted : Integrable (fun ω ↦ ‖a + average ω‖ ^ 2) P := by
    exact hexpanded.congr (Filter.Eventually.of_forall fun ω ↦
      (norm_add_sq_real a (average ω)).symm)
  refine ⟨by simpa only [average] using hshifted, ?_⟩
  calc
    (∫ ω, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂P) =
        ∫ ω, (‖a‖ ^ 2 + 2 * inner ℝ a (average ω)) +
          ‖average ω‖ ^ 2 ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp only [average, norm_add_sq_real]
    _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ ω, average ω ∂P) +
          ∫ ω, ‖average ω‖ ^ 2 ∂P := by
      calc
        (∫ ω, (‖a‖ ^ 2 + 2 * inner ℝ a (average ω)) +
            ‖average ω‖ ^ 2 ∂P) =
            (∫ ω, ‖a‖ ^ 2 + 2 * inner ℝ a (average ω) ∂P) +
              ∫ ω, ‖average ω‖ ^ 2 ∂P :=
          integral_add ((integrable_const _).add (hinner.const_mul 2)) haverageSquare
        _ = ((∫ _ω, ‖a‖ ^ 2 ∂P) +
              ∫ ω, 2 * inner ℝ a (average ω) ∂P) +
              ∫ ω, ‖average ω‖ ^ 2 ∂P := by
          rw [integral_add (integrable_const _) (hinner.const_mul 2)]
        _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ ω, average ω ∂P) +
              ∫ ω, ‖average ω‖ ^ 2 ∂P := by
          rw [integral_const, integral_const_mul, integral_inner haverage a]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ = ‖a‖ ^ 2 + ∫ ω, ‖average ω‖ ^ 2 ∂P := by rw [haverageMean]; simp
    _ ≤ ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
      exact add_le_add le_rfl (by simpa only [average] using hbatch.2)

/-- Helper for Corollary 4.2: centering an integrable square-integrable Euclidean
random vector cannot increase its second moment. -/
theorem centeredMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (mean : EuclideanSpace ℝ (Fin n))
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = mean)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun ξ ↦ ‖value ξ - mean‖ ^ 2) ν ∧
      (∫ ξ, ‖value ξ - mean‖ ^ 2 ∂ν) ≤ secondMoment := by
  have hinner : Integrable (fun ξ ↦ inner ℝ (value ξ) mean) ν :=
    hvalue.inner_const mean
  have hexpanded : Integrable (fun ξ ↦
      ‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean + ‖mean‖ ^ 2) ν :=
    (hsquare.sub (hinner.const_mul 2)).add (integrable_const _)
  have hcentered : Integrable (fun ξ ↦ ‖value ξ - mean‖ ^ 2) ν := by
    exact hexpanded.congr (Filter.Eventually.of_forall fun ξ ↦
      (norm_sub_sq_real (value ξ) mean).symm)
  refine ⟨hcentered, ?_⟩
  have hinnerIntegral :
      (∫ ξ, inner ℝ (value ξ) mean ∂ν) = ‖mean‖ ^ 2 := by
    calc
      (∫ ξ, inner ℝ (value ξ) mean ∂ν) =
          ∫ ξ, inner ℝ mean (value ξ) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ξ ↦ real_inner_comm _ _
      _ = inner ℝ mean (∫ ξ, value ξ ∂ν) := integral_inner hvalue mean
      _ = ‖mean‖ ^ 2 := by rw [hmean, real_inner_self_eq_norm_sq]
  calc
    (∫ ξ, ‖value ξ - mean‖ ^ 2 ∂ν) =
        (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦
          norm_sub_sq_real (value ξ) mean)]
      calc
        (∫ ξ, (‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean) +
            ‖mean‖ ^ 2 ∂ν) =
            (∫ ξ, ‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean ∂ν) +
              ∫ _ξ, ‖mean‖ ^ 2 ∂ν :=
          integral_add (hsquare.sub (hinner.const_mul 2)) (integrable_const _)
        _ = ((∫ ξ, ‖value ξ‖ ^ 2 ∂ν) -
              ∫ ξ, 2 * inner ℝ (value ξ) mean ∂ν) +
              ∫ _ξ, ‖mean‖ ^ 2 ∂ν := by
          rw [integral_sub hsquare (hinner.const_mul 2)]
        _ = (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
          rw [integral_const_mul, hinnerIntegral, integral_const]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
          ring
    _ ≤ ∫ ξ, ‖value ξ‖ ^ 2 ∂ν := sub_le_self _ (sq_nonneg _)
    _ ≤ secondMoment := hsecond

/-- Helper for Corollary 4.2: subtracting a constant inside a positive-size batch
average is the same as subtracting it from the average. -/
theorem batchAverage_sub
    (batch : ℕ+) (value : ℕ → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) :
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, (value i - a) =
      (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value i - a := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub]
  have hbatch : (batch : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul, inv_mul_cancel₀ hbatch, one_smul]

omit [IsProbabilityMeasure P] in
/-- Helper for Corollary 4.2: at a fixed point in the regularity region, an
independent refresh batch has integrable squared centered error bounded by the
oracle noise variance divided by the batch size. -/
theorem fixedPointRefreshBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν P)
    (hindependent : ProbabilityTheory.iIndepFun sample P) :
    Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i ω) - gradient f x)‖ ^ 2) P ∧
      (∫ ω, ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i ω) - gradient f x)‖ ^ 2 ∂P) ≤
          (oracle.noiseLevel : ℝ) ^ 2 / (batch : ℝ) := by
  have hunbiased := oracle.unbiased_spec x hx
  have hvariance := oracle.variance_spec x hx
  have hcentered : Integrable
      (fun ξ ↦ oracle.sampleGradient x ξ - gradient f x) ν :=
    hunbiased.1.sub (integrable_const _)
  have hcenteredMean :
      (∫ ξ, oracle.sampleGradient x ξ - gradient f x ∂ν) = 0 := by
    -- Unbiasedness centers each sample-gradient error.
    rw [integral_sub hunbiased.1 (integrable_const _), hunbiased.2, integral_const]
    simp
  -- The abstract batch calculation supplies both integrability and the sharp
  -- inverse-batch second-moment bound.
  exact independentBatchMeanSquare_le
    (fun ξ ↦ oracle.sampleGradient x ξ - gradient f x) sample batch
      hlaw hindependent hcentered hcenteredMean hvariance.1
        ((oracle.noiseLevel : ℝ) ^ 2) hvariance.2

/-- Helper for Corollary 4.2: at two fixed points in the regularity region, a
fresh update batch adds a centered innovation whose mean square is controlled
by the oracle mean-square Lipschitz constant. -/
theorem fixedPointUpdateBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ h.region)
    (a : EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν P)
    (hindependent : ProbabilityTheory.iIndepFun sample P) :
    Integrable (fun ω ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2) P ∧
      (∫ ω, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂P) ≤
        ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by
  let difference : Ξ → EuclideanSpace ℝ (Fin n) := fun ξ ↦
    oracle.sampleGradient x ξ - oracle.sampleGradient y ξ
  let meanDifference : EuclideanSpace ℝ (Fin n) := gradient f x - gradient f y
  let centered : Ξ → EuclideanSpace ℝ (Fin n) := fun ξ ↦
    difference ξ - meanDifference
  have hxUnbiased := oracle.unbiased_spec x hx
  have hyUnbiased := oracle.unbiased_spec y hy
  have hdifference : Integrable difference ν := by
    exact hxUnbiased.1.sub hyUnbiased.1
  have hdifferenceMean : (∫ ξ, difference ξ ∂ν) = meanDifference := by
    simp only [difference, meanDifference]
    rw [integral_sub hxUnbiased.1 hyUnbiased.1, hxUnbiased.2, hyUnbiased.2]
  have hlipschitz := oracle.meanSquareLipschitz_spec x hx y hy
  have hcenteredSquare := centeredMeanSquare_le difference meanDifference
    hdifference hdifferenceMean hlipschitz.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) hlipschitz.2
  have hcentered : Integrable centered ν := by
    exact hdifference.sub (integrable_const _)
  have hcenteredMean : (∫ ξ, centered ξ ∂ν) = 0 := by
    simp only [centered]
    rw [integral_sub hdifference (integrable_const _), hdifferenceMean, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, sub_self]
  have hshifted := independentBatchShiftedMeanSquare_le centered sample batch hlaw
    hindependent hcentered hcenteredMean hcenteredSquare.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2)
      hcenteredSquare.2 a
  refine ⟨by simpa only [centered, difference, meanDifference] using hshifted.1, ?_⟩
  calc
    (∫ ω, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂P) ≤
        ‖a‖ ^ 2 + ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) /
          (batch : ℝ) := by
      simpa only [centered, difference, meanDifference] using hshifted.2
    _ = ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by ring

end LALM.Correction.StochasticRun.EstimatorProbability

end
