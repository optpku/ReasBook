/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Lemma_11_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Corollary_11_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Corollary_6_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
variable (hZ_sm : ∀ n, StronglyMeasurable (Z n))

local notation "m" => ENNReal.toReal (galtonWatsonOffspringMean p)
local notation "ℱZ" => Filtration.natural Z hZ_sm
local notation "W" => branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) m
local notation "W∞" => Filtration.limitProcess W ℱZ μ

/-- Helper for Theorem 11.19: positive offspring variance forces the offspring mean to be
strictly positive and gives `L²` integrability for the casted identity under `p.toMeasure`. -/
private lemma offspringMeanPos_memLpTwo_of_variancePos
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    0 < m ∧ MemLp (fun k : ℕ ↦ (k : ℝ)) 2 p.toMeasure := by
  have hmem :
      MemLp (fun k : ℕ ↦ (k : ℝ)) 2 p.toMeasure := by
    refine ProbabilityTheory.memLp_two_of_variance_ne_zero
      MeasurableEmbedding.natCast.measurable.aestronglyMeasurable ?_
    exact ne_of_gt hvar_pos
  have hm_nonneg : 0 ≤ m := ENNReal.toReal_nonneg
  have hm_pos : 0 < m := by
    by_contra hm_not_pos
    have hm_zero : m = 0 := le_antisymm (not_lt.mp hm_not_pos) hm_nonneg
    have hid_int : Integrable (fun k : ℕ ↦ (k : ℝ)) p.toMeasure :=
      hmem.integrable one_le_two
    have hnonneg : 0 ≤ᵐ[p.toMeasure] fun k : ℕ ↦ (k : ℝ) :=
      Filter.Eventually.of_forall fun k ↦ Nat.cast_nonneg k
    have hint_zero : ∫ k, (k : ℝ) ∂p.toMeasure = 0 := by
      calc
        ∫ k, (k : ℝ) ∂p.toMeasure = ∑' k : ℕ, (p k).toReal * (k : ℝ) := by
          simpa [smul_eq_mul] using PMF.integral_eq_tsum p (fun k : ℕ ↦ (k : ℝ)) hid_int
        _ = ∑' k : ℕ, (k : ℝ) * (p k).toReal := by
          refine tsum_congr fun k ↦ ?_
          ring
        _ = ∑' k : ℕ, (((k : ENNReal) * p k).toReal) := by
          refine tsum_congr fun k ↦ ?_
          simp [ENNReal.toReal_mul]
        _ = (∑' k : ℕ, (k : ENNReal) * p k).toReal := by
          symm
          rw [ENNReal.tsum_toReal_eq]
          intro k
          exact ENNReal.mul_ne_top (by simp) (p.apply_ne_top k)
        _ = m := by
          change ENNReal.toReal (galtonWatsonOffspringMean p) = ENNReal.toReal (galtonWatsonOffspringMean p)
          simp [galtonWatsonOffspringMean_eq_tsum]
        _ = 0 := hm_zero
    have hae_zero : (fun k : ℕ ↦ (k : ℝ)) =ᵐ[p.toMeasure] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hid_int).1 hint_zero
    have hvar_zero : Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure] = 0 := by
      rw [ProbabilityTheory.variance_congr hae_zero]
      simp
    exact (ne_of_gt hvar_pos) hvar_zero
  exact ⟨hm_pos, hmem⟩

/-- Helper for Theorem 11.19: a positive real offspring mean rules out an infinite
`galtonWatsonOffspringMean p`. -/
private lemma offspringMean_ne_top_of_pos
    (hm : 0 < m) :
    galtonWatsonOffspringMean p ≠ ⊤ := by
  intro htop
  have hm_zero : m = 0 := by
    change ENNReal.toReal (galtonWatsonOffspringMean p) = 0
    simp [htop]
  linarith

/-- Helper for Theorem 11.19: the defining real offspring-moment series sums to the real offspring
mean `m`. -/
private lemma galtonWatsonOffspringMean_eq_tsumReal
    :
    ∑' k : ℕ, (k : ℝ) * (p k).toReal = m := by
  calc
    ∑' k : ℕ, (k : ℝ) * (p k).toReal = ∑' k : ℕ, (((k : ENNReal) * p k).toReal) := by
      refine tsum_congr fun k ↦ ?_
      simp [ENNReal.toReal_mul]
    _ = (∑' k : ℕ, (k : ENNReal) * p k).toReal := by
      symm
      rw [ENNReal.tsum_toReal_eq]
      intro k
      exact ENNReal.mul_ne_top (by simp) (p.apply_ne_top k)
    _ = m := by
      change ENNReal.toReal (galtonWatsonOffspringMean p) = ENNReal.toReal (galtonWatsonOffspringMean p)
      simp [galtonWatsonOffspringMean_eq_tsum]

/-- Helper for Theorem 11.19: positive offspring variance implies integrability of the casted
offspring identity under the offspring law. -/
private lemma galtonWatsonOffspringIdIntegrableReal_ofVariancePos
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) p.toMeasure := by
  -- Proof comment: the `L²` control extracted from the positive-variance hypothesis implies
  -- the needed `L¹` integrability.
  exact (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).2.integrable one_le_two

/-- Helper for Theorem 11.19: every offspring variable is integrable after casting from `ℕ` to
`ℝ`. -/
private lemma galtonWatsonOffspringIntegrableReal_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n i : ℕ) :
    Integrable (fun ω ↦ (offspring n i ω : ℝ)) μ := by
  have hIdentNat : IdentDistrib (offspring n i) id μ p.toMeasure :=
    (hoffspring_law n i).identDistrib ProbabilityTheory.HasLaw.id
  have hIdentReal :
      IdentDistrib (fun ω ↦ (offspring n i ω : ℝ)) (fun k : ℕ ↦ (k : ℝ)) μ p.toMeasure :=
    -- Proof comment: transport the common offspring law through the measurable embedding `ℕ ↪ ℝ`.
    hIdentNat.comp MeasurableEmbedding.natCast.measurable
  -- Proof comment: identical distribution transfers the discrete `L¹` bound to each realized
  -- offspring variable.
  exact (hIdentReal.integrable_iff).2 <|
    galtonWatsonOffspringIdIntegrableReal_ofVariancePos (p := p) hvar_pos

/-- Helper for Theorem 11.19: finite sums of relatively measurable `ℕ`-valued functions remain
relatively measurable. -/
private lemma measurable_sum_natFamilyRel
    {mΩ : MeasurableSpace Ω} {n : ℕ} (X : Fin n → Ω → ℕ)
    (hX : ∀ i, Measurable[mΩ] (X i)) :
    Measurable[mΩ] (fun ω ↦ ∑ i : Fin n, X i ω) := by
  -- Proof comment: relative measurability is stable under finite sums over a finite index set.
  fun_prop

/-- Helper for Theorem 11.19: a random finite sum of relatively measurable offspring counts is
again relatively measurable. -/
private lemma measurable_randomNatSum
    {mΩ : MeasurableSpace Ω} (T : Ω → ℕ) (hT : Measurable[mΩ] T) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, Measurable[mΩ] (X n)) :
    Measurable[mΩ] (fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)) := by
  -- Proof comment: each fiber of the random sum splits over the realized value of `T`, reducing
  -- measurability to countably many finite-sum pieces.
  refine measurable_to_countable' ?_
  intro k
  have hpreimage :
      (fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)) ⁻¹' {k} =
        ⋃ n : ℕ, ({ω | T ω = n} ∩ {ω | ∑ i : Fin n, X i ω = k}) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨T ω, ?_⟩
      constructor
      · simp
      · simpa [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) (T ω)] using hω
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hnT, hnk⟩
      have hnT' : T ω = n := by simpa using hnT
      have hnk' : ∑ i : Fin n, X i ω = k := by simpa using hnk
      simpa [hnT', ← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n] using hnk'
  rw [hpreimage]
  refine MeasurableSet.iUnion ?_
  intro n
  have hsum_meas : Measurable[mΩ] (fun ω ↦ ∑ i : Fin n, X i ω) :=
    measurable_sum_natFamilyRel (X := fun i : Fin n ↦ X i) (fun i ↦ hX i)
  exact (hT (measurableSet_singleton n)).inter (hsum_meas (measurableSet_singleton k))

/-- Helper for Theorem 11.19: the next generation is a random finite sum of the fresh offspring
row indexed by the current population size. -/
private def natRandomSum (T : Ω → ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)

/-- Helper for Theorem 11.19: `natRandomSum` unfolds to the expected finite prefix sum. -/
private lemma natRandomSum_apply (T : Ω → ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) :
    natRandomSum T X ω = Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω) := by
  -- Proof comment: this is the defining equation of the random finite sum.
  rfl

/-- Helper for Theorem 11.19: a measurable counting variable and measurable summands yield a
measurable random finite sum. -/
private lemma measurable_natRandomSum (T : Ω → ℕ) (hT : Measurable T) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, Measurable (X n)) :
    Measurable (natRandomSum T X) := by
  -- Proof comment: specialize the relative measurability lemma to the ambient sigma-algebra.
  simpa [natRandomSum] using measurable_randomNatSum (mΩ := inferInstance) T hT X hX

/-- Helper for Theorem 11.19: on the slice `{T = n}`, the random finite sum agrees with the
deterministic prefix sum of length `n`. -/
private lemma pow_natRandomSum_eq_partial_sum_on_counting_fiber
    (T : Ω → ℕ) (X : ℕ → Ω → ℕ) (z : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Set.EqOn (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω)
      (fun ω ↦ (z : ℝ) ^ ∑ i : Fin n, X i ω) {ω | T ω = n} := by
  intro ω hω
  -- Proof comment: once `T ω = n`, the random finite sum is literally the `n`-term prefix sum.
  calc
    (z : ℝ) ^ natRandomSum T X ω =
        (z : ℝ) ^ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω) := by
          rw [natRandomSum_apply]
    _ = (z : ℝ) ^ Finset.sum (Finset.range n) (fun i ↦ X i ω) := by
          have hω' : T ω = n := hω
          simpa [hω']
    _ = (z : ℝ) ^ (∑ i : Fin n, X i ω) := by
          rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n]

/-- Helper for Theorem 11.19: a power of a finite sum can be rewritten as the corresponding
finite product of powers. -/
private lemma partialSumPower_eq_finsetProd
    (X : ℕ → Ω → ℕ) (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (fun ω ↦ (z : ℝ) ^ ∑ i : Fin n, X i ω) = fun ω ↦ ∏ i : Fin n, (z : ℝ) ^ X i ω := by
  -- Proof comment: `Finset.prod_pow_eq_pow_sum` is the exact normalization bridge between the
  -- textbook power-of-sum expression and the finite-product independence API.
  funext ω
  simpa using
    (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin n ↦ X i ω) (z : ℝ)).symm

/-- Helper for Theorem 11.19: the pgf of a finite partial sum of iid `ℕ`-valued random variables
is the corresponding power of the common pgf. -/
private lemma integral_pow_partial_sum_eq_pow_common_pgf
    (X : ℕ → Ω → ℕ) (hX : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ) (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂μ =
      ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
  have hXn_indep : iIndepFun (fun i : Fin n ↦ X i) μ := by
    -- Proof comment: restrict the iid sequence to the finite prefix indexed by `Fin n`.
    simpa using hX_indep.precomp (g := ((↑) : Fin n → ℕ)) Fin.val_injective
  have hsum_meas : Measurable (fun ω ↦ ∑ i : Fin n, X i ω) := by
    -- Proof comment: the finite partial sum is measurable as a finite sum of measurable
    -- `ℕ`-valued coordinates.
    exact measurable_sum_natFamily (fun i : Fin n ↦ X i) (fun i ↦ hX i)
  have hpgf_sum :
      (probabilityGeneratingFunction
          (natRandomVariableLaw μ (fun ω ↦ ∑ i : Fin n, X i ω) hsum_meas) z : ℝ) =
        ∏ i : Fin n, (probabilityGeneratingFunction (natRandomVariableLaw μ (X i) (hX i)) z : ℝ) := by
    -- Proof comment: reuse the Chapter 3 finite-sum pgf factorization directly instead of
    -- rebuilding the powered-independence argument locally.
    simpa using
      probabilityGeneratingFunction_sum_eq_prod_of_iIndepFun
        (P := μ) (X := fun i : Fin n ↦ X i) (hX_meas := fun i ↦ hX i) hXn_indep z
  calc
    ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂μ
        = (probabilityGeneratingFunction
            (natRandomVariableLaw μ (fun ω ↦ ∑ i : Fin n, X i ω) hsum_meas) z : ℝ) := by
              symm
              rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral μ
                (fun ω ↦ ∑ i : Fin n, X i ω) hsum_meas z]
    _ = ∏ i : Fin n, (probabilityGeneratingFunction (natRandomVariableLaw μ (X i) (hX i)) z : ℝ) := by
          exact hpgf_sum
    _ = ∏ i : Fin n, (probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          -- Proof comment: identical distribution identifies every marginal law with the `i = 0`
          -- law, so each pgf factor agrees after rewriting both sides as the corresponding
          -- expectation of the power map.
          calc
            (probabilityGeneratingFunction (natRandomVariableLaw μ (X i) (hX i)) z : ℝ)
                = ∫ ω, (z : ℝ) ^ X i ω ∂μ := by
                    rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral μ
                      (X i) (hX i) z]
            _ = ∫ ω, (z : ℝ) ^ X 0 ω ∂μ := by
                  simpa using ((hX_ident i).comp (by fun_prop)).integral_eq
            _ = (probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ) := by
                  rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral μ
                    (X 0) (hX 0) z]
    _ = ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
          simp

/-- Helper for Theorem 11.19: the contribution of the fiber `{T = n}` factors into the fiber
probability and the `n`th power of the common offspring pgf. -/
private lemma setIntegral_pow_natRandomSum_fiber_eq_countingLaw_mul_common_pgf_pow
    (T : Ω → ℕ) (hT : Measurable T) (X : ℕ → Ω → ℕ) (hX : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) μ) (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ) (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω in {ω | T ω = n}, (z : ℝ) ^ natRandomSum T X ω ∂μ =
      ((natRandomVariableLaw μ T hT) n).toReal *
        ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
  let A : Set Ω := {ω | T ω = n}
  have hA_meas : MeasurableSet A := hT (measurableSet_singleton n)
  have hseq_meas : Measurable (fun ω ↦ fun k ↦ X k ω) := by
    -- Proof comment: the whole offspring row is measurable coordinatewise.
    exact measurable_pi_lambda _ hX
  have hindicator_meas :
      Measurable (Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ))) := by
    -- Proof comment: the singleton indicator on `ℕ` is measurable.
    classical
    simpa using measurable_const.indicator (measurableSet_singleton n)
  have hpartial_sum_meas : Measurable (fun x : ℕ → ℕ ↦ ∑ i : Fin n, x i) := by
    -- Proof comment: the partial-sum functional depends on finitely many coordinates.
    fun_prop
  have hpartial_pow_meas :
      Measurable (fun x : ℕ → ℕ ↦ (z : ℝ) ^ ∑ i : Fin n, x i) := by
    -- Proof comment: composing the partial sum with the power map preserves measurability.
    exact hpartial_sum_meas.const_pow (z : ℝ)
  have hindicator_eq :
      Set.indicator A (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) =
        fun ω ↦ Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) *
          ((z : ℝ) ^ ∑ i : Fin n, X i ω) := by
    funext ω
    by_cases hω : T ω = n
    · have hpow :
          (z : ℝ) ^ natRandomSum T X ω = (z : ℝ) ^ ∑ i : Fin n, X i ω :=
        (pow_natRandomSum_eq_partial_sum_on_counting_fiber T X z n) hω
      -- Proof comment: on the fiber, the indicator is `1` and only the partial-sum term remains.
      simp [A, hω, hpow]
    · -- Proof comment: off the fiber, both indicator terms vanish.
      simp [A, hω]
  have hT_factor :
      ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂μ =
        ((natRandomVariableLaw μ T hT) n).toReal := by
    -- Proof comment: push the singleton indicator integral to the law of `T`.
    calc
      ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂μ
          = ∫ k, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) k ∂(μ.map T) := by
              rw [← integral_map hT.aemeasurable hindicator_meas.aestronglyMeasurable]
      _ = ∫ k in ({n} : Set ℕ), (1 : ℝ) ∂(μ.map T) := by
            rw [integral_indicator (measurableSet_singleton n)]
      _ = ((natRandomVariableLaw μ T hT) n).toReal := by
            rw [setIntegral_one_eq_measureReal, Measure.real,
              ← PMF.toMeasure_apply_singleton (natRandomVariableLaw μ T hT) n
                (measurableSet_singleton n), natRandomVariableLaw_toMeasure μ T hT]
  have hX_factor :
      ∫ x, (z : ℝ) ^ ∑ i : Fin n, x i ∂(μ.map (fun ω ↦ fun k ↦ X k ω)) =
        ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
    -- Proof comment: push the partial-sum functional back to `μ` and use the iid partial-sum formula.
    rw [integral_map hseq_meas.aemeasurable hpartial_pow_meas.aestronglyMeasurable]
    simpa using integral_pow_partial_sum_eq_pow_common_pgf
      (μ := μ) X hX hX_indep hX_ident n z
  -- Proof comment: rewrite the fiber integral as an indicator product, factor by independence,
  -- and evaluate the two factors separately.
  calc
    ∫ ω in {ω | T ω = n}, (z : ℝ) ^ natRandomSum T X ω ∂μ
        = ∫ ω, Set.indicator A (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) ω ∂μ := by
            symm
            rw [integral_indicator hA_meas]
    _ = ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) *
          ((z : ℝ) ^ ∑ i : Fin n, X i ω) ∂μ := by
            rw [hindicator_eq]
    _ = (∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂μ) *
          ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂μ := by
            simpa using
              hTX_indep.integral_fun_comp_mul_comp hT.aemeasurable hseq_meas.aemeasurable
                hindicator_meas.aestronglyMeasurable hpartial_pow_meas.aestronglyMeasurable
    _ = ((natRandomVariableLaw μ T hT) n).toReal *
          ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂μ := by
            rw [hT_factor]
    _ = ((natRandomVariableLaw μ T hT) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
            rw [integral_pow_partial_sum_eq_pow_common_pgf
              (μ := μ) X hX hX_indep hX_ident n z]

/-- Helper for Theorem 11.19: integrating the power of the random finite sum over the partition
given by `T` produces the scalar series indexed by the law of `T`. -/
private lemma integral_pow_natRandomSum_eq_tsum_countingLaw_mul_common_pgf_pow
    (T : Ω → ℕ) (hT : Measurable T) (X : ℕ → Ω → ℕ) (hX : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) μ) (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂μ =
      ∑' n : ℕ, ((natRandomVariableLaw μ T hT) n).toReal *
        ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
  let A : ℕ → Set Ω := fun n ↦ {ω | T ω = n}
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact hT (measurableSet_singleton n)
  have hA_disjoint : Pairwise fun i j ↦ Disjoint (A i) (A j) := by
    -- Proof comment: distinct singleton fibers of the counting variable are pairwise disjoint.
    intro i j hij
    simpa [A] using (pairwise_disjoint_fiber T hij)
  have hA_union : ⋃ n, A n = Set.univ := by
    ext ω
    simp [A]
  have hPow_integrable : Integrable (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) μ := by
    -- Proof comment: the integrand is measurable and bounded by `1` because `z ∈ [0,1]`.
    refine Integrable.of_bound
      ((measurable_natRandomSum T hT X hX).const_pow (z : ℝ)).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 _)]
    exact pow_le_one₀ z.2.1 z.2.2
  have hPow_integrableOn :
      IntegrableOn (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) (⋃ n, A n) μ := by
    simpa [hA_union] using hPow_integrable
  -- Proof comment: decompose the expectation over the measurable partition given by the values
  -- of `T` and evaluate each fiber with the factorization lemma above.
  calc
    ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂μ
        = ∫ ω in ⋃ n, A n, (z : ℝ) ^ natRandomSum T X ω ∂μ := by
            rw [hA_union, setIntegral_univ]
    _ = ∑' n, ∫ ω in A n, (z : ℝ) ^ natRandomSum T X ω ∂μ := by
          exact integral_iUnion hA_meas hA_disjoint hPow_integrableOn
    _ = ∑' n : ℕ, ((natRandomVariableLaw μ T hT) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
            refine tsum_congr fun n ↦ ?_
            simpa [A] using
              setIntegral_pow_natRandomSum_fiber_eq_countingLaw_mul_common_pgf_pow
                (μ := μ) T hT X hX hTX_indep hX_indep hX_ident n z

/-- Helper for Theorem 11.19: the pgf of a random finite sum is obtained by evaluating the pgf of
the counting variable at the common pgf of the summands. -/
private lemma probabilityGeneratingFunction_natRandomSum_eq_comp_of_indepFun_of_iIndepFun_of_identDistrib
    (T : Ω → ℕ) (hT : Measurable T) (X : ℕ → Ω → ℕ) (hX : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) μ) (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw μ (natRandomSum T X) (measurable_natRandomSum T hT X hX)) z : ℝ) =
      (probabilityGeneratingFunction (natRandomVariableLaw μ T hT)
        (probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z) : ℝ) := by
  -- Route correction: rewrite the pgf of the random sum as one integral and then reuse the
  -- fiberwise scalar series, exactly as in the Chapter 3 owner theorem.
  calc
    (probabilityGeneratingFunction
        (natRandomVariableLaw μ (natRandomSum T X) (measurable_natRandomSum T hT X hX)) z : ℝ)
        = ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂μ := by
            rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral μ (natRandomSum T X)
              (measurable_natRandomSum T hT X hX) z]
    _ = ∑' n : ℕ, ((natRandomVariableLaw μ T hT) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z : ℝ)) ^ n := by
            rw [integral_pow_natRandomSum_eq_tsum_countingLaw_mul_common_pgf_pow
              (μ := μ) T hT X hX hTX_indep hX_indep hX_ident z]
    _ = (probabilityGeneratingFunction (natRandomVariableLaw μ T hT)
          (probabilityGeneratingFunction (natRandomVariableLaw μ (X 0) (hX 0)) z) : ℝ) := by
            symm
            rw [probabilityGeneratingFunction_apply]

/-- Helper for Theorem 11.19: the sigma-algebra generated by offspring rows strictly before
generation `n`. -/
@[reducible] private def offspringPast
    (offspring : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 < n},
    MeasurableSpace.comap (fun ω ↦ offspring ij.1 ij.2 ω) Nat.instMeasurableSpace

/-- Helper for Theorem 11.19: the sigma-algebra generated by the whole offspring row at
generation `n`. -/
@[reducible] private def offspringRowSpace
    (offspring : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 = n},
    MeasurableSpace.comap (fun ω ↦ offspring ij.1 ij.2 ω) Nat.instMeasurableSpace

/-- Helper for Theorem 11.19: enlarging the row cutoff enlarges the past offspring sigma-algebra.
-/
private lemma offspringPast_mono
    {offspring : ℕ → ℕ → Ω → ℕ} :
    Monotone (offspringPast (Ω := Ω) offspring) := by
  intro n k hnk
  refine iSup_le ?_
  intro ij
  refine iSup_le ?_
  intro hij
  exact le_iSup_of_le ij <| le_iSup_of_le (lt_of_lt_of_le hij hnk) le_rfl

/-- Helper for Theorem 11.19: each generation size is measurable with respect to the offspring
rows that have already appeared by that generation. -/
-- TODO: prove this by induction on `n`, using `hZ.initial` in the base case and
-- `measurable_randomNatSum` for the successor step after transporting along `hsucc`.
private lemma galtonWatsonGeneration_measurable_offspringPast_self
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω)) :
    ∀ n, Measurable[offspringPast (Ω := Ω) offspring n] (Z n) := by
  -- Route correction: port the proven Theorem 11.20 offspring-past owner chain, but repair the
  -- zero-generation step to use the Galton--Watson initial condition `Z₀ = 1`.
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial generation is deterministically the single ancestor.
      have hZ0 : Z 0 = fun _ : Ω ↦ (1 : ℕ) := by
        funext ω
        exact hZ.initial ω
      simpa [hZ0] using
        (measurable_const :
          Measurable[offspringPast (Ω := Ω) offspring 0] (fun _ : Ω ↦ (1 : ℕ)))
  | succ n ih =>
      -- Proof comment: the next generation is the measurable random sum of the fresh offspring
      -- row over the measurable current population size.
      have hT :
          Measurable[offspringPast (Ω := Ω) offspring (n + 1)] (Z n) :=
        ih.mono
          (offspringPast_mono (Ω := Ω) (offspring := offspring) (show n ≤ n + 1 by omega))
          le_rfl
      have hX :
          ∀ i, Measurable[offspringPast (Ω := Ω) offspring (n + 1)] (offspring n i) := by
        intro i
        refine measurable_iff_comap_le.mpr ?_
        exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
      have hsucc_fun :
          Z (n + 1) =
            fun ω ↦ Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω) := by
        funext ω
        exact hsucc n ω
      simpa [hsucc_fun] using
        (measurable_randomNatSum
          (mΩ := offspringPast (Ω := Ω) offspring (n + 1))
          (T := Z n) hT (X := fun i ↦ offspring n i) hX)

/-- Helper for Theorem 11.19: every earlier generation is measurable with respect to any later
offspring-past sigma-algebra. -/
-- TODO: obtain this by monotonicity of `offspringPast` from the self-measurability lemma above.
private lemma galtonWatsonGeneration_measurable_offspringPast
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω)) :
    ∀ {k n}, k ≤ n → Measurable[offspringPast (Ω := Ω) offspring n] (Z k) := by
  intro k n hkn
  exact (galtonWatsonGeneration_measurable_offspringPast_self
    (Z := Z) (p := p) (offspring := offspring) hZ hsucc k).mono
      (offspringPast_mono (Ω := Ω) (offspring := offspring) hkn)
      le_rfl

/-- Helper for Theorem 11.19: the natural filtration of `Z` is contained in the sigma-algebra
generated by offspring rows strictly before the current generation. -/
-- TODO: rewrite `Filtration.natural` as the join of the `Z k` comaps and discharge each
-- generator with `galtonWatsonGeneration_measurable_offspringPast`.
private lemma galtonWatsonNaturalFiltration_le_offspringPast
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω)) :
    ∀ n, ℱZ n ≤ offspringPast (Ω := Ω) offspring n := by
  intro n
  -- Proof comment: each generator `Z k` of the natural filtration with `k ≤ n` is measurable
  -- with respect to the offspring rows that have already appeared by generation `n`.
  rw [Filtration.natural]
  refine iSup_le ?_
  intro k
  refine iSup_le ?_
  intro hkn
  exact (measurable_iff_comap_le.mp <|
    galtonWatsonGeneration_measurable_offspringPast
      (Z := Z) (p := p) (offspring := offspring) hZ hsucc hkn)

-- Helper for Theorem 11.19: each fresh offspring variable is independent of the natural
-- filtration up to the current generation.
/-- Helper for Theorem 11.19: the common offspring witness yields independence of the coordinate
comap sigma-algebras. -/
private lemma galtonWatsonOffspringComap_iIndep
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ) :
    iIndep
      (fun ij : ℕ × ℕ ↦
        MeasurableSpace.comap (fun ω ↦ offspring ij.1 ij.2 ω) Nat.instMeasurableSpace) μ := by
  -- Proof comment: `iIndepFun` is exactly independence of the coordinate comap sigma-algebras.
  simpa using hoffspring_indep.iIndep

-- TODO: first apply `indep_iSup_of_disjoint` against the past offspring sigma-algebra, then
-- descend the result along `galtonWatsonNaturalFiltration_le_offspringPast`.
private lemma galtonWatsonOffspring_indep_natural
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (n i : ℕ) :
    Indep (MeasurableSpace.comap (offspring n i) Nat.instMeasurableSpace) (ℱZ n) μ := by
  let mOff : ℕ × ℕ → MeasurableSpace Ω := fun ij ↦
    MeasurableSpace.comap (fun ω ↦ offspring ij.1 ij.2 ω) Nat.instMeasurableSpace
  have hPastIndep :
      Indep (mOff (n, i)) (offspringPast (Ω := Ω) offspring n) μ := by
    have hDisjoint :
        Disjoint ({(n, i)} : Set (ℕ × ℕ)) {ij : ℕ × ℕ | ij.1 < n} := by
      refine Set.disjoint_left.2 ?_
      intro ij hij hlt
      have hij' : ij = (n, i) := by simpa using hij
      have : n < n := by simpa [hij'] using hlt
      exact lt_irrefl _ this
    -- Proof comment: the fresh coordinate `(n,i)` is disjoint from the sigma-algebra generated
    -- by all earlier offspring rows, so `indep_iSup_of_disjoint` applies directly.
    simpa [mOff, offspringPast] using
      (@ProbabilityTheory.indep_iSup_of_disjoint Ω (ℕ × ℕ) mOff _ μ
        (fun ij ↦ (hoffspring_meas ij.1 ij.2).comap_le)
        (galtonWatsonOffspringComap_iIndep (μ := μ) hoffspring_indep)
        {(n, i)} {ij : ℕ × ℕ | ij.1 < n} hDisjoint)
  -- Proof comment: descend from the larger offspring-past sigma-algebra to the natural filtration.
  simpa [mOff] using
    (ProbabilityTheory.indep_of_indep_of_le_right hPastIndep <|
      galtonWatsonNaturalFiltration_le_offspringPast
        (Z := Z) (p := p) hZ_sm (offspring := offspring) hZ hsucc n)

/-- Helper for Theorem 11.19: each real-cast offspring coordinate has expectation equal to the
offspring mean `m`. -/
private lemma galtonWatsonOffspringIntegralReal_eq_mean_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n i : ℕ) :
    ∫ ω, (offspring n i ω : ℝ) ∂μ = m := by
  -- Proof comment: transport the discrete first moment of the offspring law through the common
  -- law of each offspring coordinate.
  calc
    ∫ ω, (offspring n i ω : ℝ) ∂μ = ∫ k, (k : ℝ) ∂p.toMeasure := by
      simpa [Function.comp] using
        (hoffspring_law n i).integral_comp
          MeasurableEmbedding.natCast.measurable.aestronglyMeasurable
    _ = ∑' k : ℕ, (p k).toReal * (k : ℝ) := by
      simpa [smul_eq_mul] using
        (PMF.integral_eq_tsum p (fun k : ℕ ↦ (k : ℝ))
          (galtonWatsonOffspringIdIntegrableReal_ofVariancePos (p := p) hvar_pos))
    _ = ∑' k : ℕ, (k : ℝ) * (p k).toReal := by
      refine tsum_congr ?_
      intro k
      ring
    _ = m := by
      exact galtonWatsonOffspringMean_eq_tsumReal (p := p)

/-- Helper for Theorem 11.19: a fallback offspring row with only the first coordinate nonzero
still sums to that first coordinate over any nonempty prefix. -/
private lemma sum_range_fallbackRow_eq {a : ℕ} :
    ∀ k : ℕ, Finset.sum (Finset.range (k + 1)) (fun i ↦ if i = 0 then a else 0) = a
  | 0 => by simp
  | k + 1 => by
      -- Proof comment: peel off the last term until only the `i = 0` contribution remains.
      rw [Finset.sum_range_succ, sum_range_fallbackRow_eq k]
      simp

/-- Helper for Theorem 11.19: every `ℕ`-valued offspring coordinate law admits a measurable
representative without changing the law. -/
private lemma hasLaw_nat_measurableRepresentative
    {X : Ω → ℕ} (hX : HasLaw X p.toMeasure μ) :
    ∃ X' : Ω → ℕ, Measurable X' ∧ X' =ᵐ[μ] X ∧ HasLaw X' p.toMeasure μ := by
  -- Proof comment: replace the almost-everywhere measurable random variable by its canonical
  -- measurable modification and transport the law across the a.e. equality.
  refine ⟨hX.aemeasurable.mk X, hX.aemeasurable.measurable_mk, ?_, ?_⟩
  · exact hX.aemeasurable.ae_eq_mk.symm
  · exact hX.congr hX.aemeasurable.ae_eq_mk.symm

/-- Helper for Theorem 11.19: every offspring witness admits a coordinatewise measurable
modification that preserves the recursion, independence, and laws. -/
private lemma measurableOffspringModification
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ_meas : ∀ n, StronglyMeasurable (Z n))
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ) :
    ∃ offspringMeas : ℕ → ℕ → Ω → ℕ,
      (∀ n i, Measurable (offspringMeas n i)) ∧
      (∀ n ω,
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω)) ∧
      iIndepFun (fun ij : ℕ × ℕ ↦ offspringMeas ij.1 ij.2) μ ∧
      (∀ n i, HasLaw (offspringMeas n i) p.toMeasure μ) ∧
      (∀ᵐ ω ∂μ, ∀ n i, offspringMeas n i ω = offspring n i ω) := by
  classical
  let offspringAe : ℕ × ℕ → Ω → ℕ := fun ij ω ↦ offspring ij.1 ij.2 ω
  let hf : ∀ ij : ℕ × ℕ, AEMeasurable (offspringAe ij) μ := by
    intro ij
    exact (hoffspring_law ij.1 ij.2).aemeasurable
  let offspringSeq : ℕ × ℕ → Ω → ℕ := aeSeq hf (fun _ _ ↦ True)
  let goodSet : Set Ω := aeSeqSet hf (fun _ _ ↦ True)
  let offspringMeas : ℕ → ℕ → Ω → ℕ :=
    fun n i ω ↦
      if hω : ω ∈ goodSet then offspringSeq (n, i) ω else if i = 0 then Z (n + 1) ω else 0
  have hgood_meas : MeasurableSet goodSet := aeSeq.aeSeqSet_measurableSet
  have hgood_ae : ∀ᵐ ω ∂μ, ω ∈ goodSet := by
    -- Proof comment: `aeSeq` repairs the whole offspring array simultaneously outside one null
    -- set, so a single good set controls every coordinate.
    exact ae_iff.2 <|
      aeSeq.measure_compl_aeSeqSet_eq_zero hf (Filter.Eventually.of_forall fun _ ↦ trivial)
  have hoffspringSeq_meas : ∀ n i, Measurable (fun ω ↦ offspringSeq (n, i) ω) := by
    intro n i
    simpa [offspringSeq] using aeSeq.measurable hf (fun _ _ ↦ True) (n, i)
  have hoffspringMeas_meas : ∀ n i, Measurable (offspringMeas n i) := by
    intro n i
    -- Proof comment: on the null complement we replace the row by the deterministic fallback
    -- row, and both branches remain measurable.
    refine Measurable.ite hgood_meas (hoffspringSeq_meas n i) ?_
    by_cases hi : i = 0
    · simpa [offspringMeas, hi] using (hZ_meas (n + 1)).measurable
    · simpa [offspringMeas, hi] using measurable_const
  have hsucc_meas :
      ∀ n ω,
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω) := by
    intro n ω
    by_cases hω : ω ∈ goodSet
    · -- Proof comment: on the full-measure good set, the measurable repair agrees pointwise with
      -- the original offspring array.
      have hEq : ∀ i : ℕ, offspringMeas n i ω = offspring n i ω := by
        intro i
        simp [offspringMeas, hω, offspringSeq, offspringAe,
          aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hω (n, i)]
      calc
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω) := hsucc n ω
        _ = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact (hEq i).symm
    · -- Proof comment: off the good set, the fallback row stores the whole next generation in the
      -- first coordinate and zeros elsewhere, so the recursion is forced exactly.
      by_cases hZn : Z n ω = 0
      · have hnext_zero : Z (n + 1) ω = 0 := by
          simpa [hZn] using hsucc n ω
        simp [offspringMeas, hω, hZn, hnext_zero]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hZn
        simp [offspringMeas, hω, hk, sum_range_fallbackRow_eq]
  have hagree :
      ∀ᵐ ω ∂μ, ∀ n i, offspringMeas n i ω = offspring n i ω := by
    filter_upwards [hgood_ae] with ω hω n i
    simp [offspringMeas, hω, offspringSeq, offspringAe,
      aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hω (n, i)]
  have hoffspringMeas_indep :
      iIndepFun (fun ij : ℕ × ℕ ↦ offspringMeas ij.1 ij.2) μ := by
    refine hoffspring_indep.congr ?_
    intro ij
    filter_upwards [hagree] with ω hω
    exact (hω ij.1 ij.2).symm
  have hoffspringMeas_law : ∀ n i, HasLaw (offspringMeas n i) p.toMeasure μ := by
    intro n i
    refine (hoffspring_law n i).congr ?_
    filter_upwards [hagree] with ω hω
    exact hω n i
  exact ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
    hoffspringMeas_law, hagree⟩

/-- Helper for Theorem 11.19: conditioning a single fresh offspring variable on the current
natural filtration returns the offspring mean. -/
private lemma galtonWatsonOffspringRealIndepNatural_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (n i : ℕ) :
    Indep
      (MeasurableSpace.comap (fun ω ↦ (offspring n i ω : ℝ)) Real.measurableSpace)
      (ℱZ n) μ := by
  -- Route correction: descend the already-proved nat-valued independence owner along the
  -- measurable embedding `ℕ ↪ ℝ` instead of creating a separate transport tower.
  have hNatIndep :
      Indep (MeasurableSpace.comap (offspring n i) Nat.instMeasurableSpace) (ℱZ n) μ :=
    galtonWatsonOffspring_indep_natural
      (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
      hZ hsucc hoffspring_indep hoffspring_meas n i
  have hcomap_le :
      MeasurableSpace.comap (fun ω ↦ (offspring n i ω : ℝ)) Real.measurableSpace ≤
        MeasurableSpace.comap (offspring n i) Nat.instMeasurableSpace := by
    -- Proof comment: composing `offspring n i` with `Nat.cast` only shrinks the generated
    -- sigma-algebra to the already-controlled nat-valued one.
    exact
      (MeasurableEmbedding.natCast.measurable.comp
        (comap_measurable (offspring n i))).comap_le
  exact ProbabilityTheory.indep_of_indep_of_le_left hNatIndep hcomap_le

/-- Helper for Theorem 11.19: conditioning a single fresh offspring variable on the current
natural filtration returns the offspring mean. -/
private lemma galtonWatsonOffspring_condExp_real_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n i : ℕ) :
    μ[(fun ω ↦ (offspring n i ω : ℝ)) | ℱZ n] =ᵐ[μ] fun _ ↦ m := by
  -- Route correction: apply `condExp_indep_eq` directly over the nat-generated sigma-algebra and
  -- use the cast only as the measurable observable on that sigma-algebra.
  have hcast_sm :
      StronglyMeasurable[MeasurableSpace.comap (offspring n i) Nat.instMeasurableSpace]
        (fun ω ↦ (offspring n i ω : ℝ)) := by
    -- Proof comment: the real-valued coordinate is a measurable transform of the nat-valued
    -- coordinate that generates the left sigma-algebra.
    exact Measurable.stronglyMeasurable <|
      MeasurableEmbedding.natCast.measurable.comp (comap_measurable (offspring n i))
  have hcond :
      μ[(fun ω ↦ (offspring n i ω : ℝ)) | ℱZ n] =ᵐ[μ]
        fun _ ↦ ∫ ω, (offspring n i ω : ℝ) ∂μ := by
    exact MeasureTheory.condExp_indep_eq
      ((hoffspring_meas n i).comap_le)
      (Filtration.le _ _)
      hcast_sm
      (galtonWatsonOffspring_indep_natural
        (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
        hZ hsucc hoffspring_indep hoffspring_meas n i)
  -- Proof comment: replace the deterministic conditional expectation by the common offspring mean.
  exact hcond.trans <| Filter.Eventually.of_forall fun _ ↦
    galtonWatsonOffspringIntegralReal_eq_mean_ofVariancePos
      (p := p) (offspring := offspring) hoffspring_law hvar_pos n i

/-- Helper for Theorem 11.19: for a fixed prefix length, the conditional expectation of the fresh
offspring-row sum is the deterministic prefix length times the offspring mean. -/
private lemma galtonWatsonGenerationCondExpFixedPrefixReal_ofMeasurable_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n r : ℕ) :
    μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n] =ᵐ[μ]
      fun _ ↦ (r : ℝ) * m := by
  -- Route correction: use the stable finite-sum conditional-expectation API after exposing
  -- coordinate measurability, instead of rebuilding the sum induction directly.
  let prefixRow : Ω → ℝ :=
    fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))
  have hsum :
      prefixRow =
        Finset.sum (Finset.range r) (fun i ↦ fun ω ↦ (offspring n i ω : ℝ)) := by
    funext ω
    simp [prefixRow, Finset.sum_apply]
  have hcond_sum :
      μ[prefixRow | ℱZ n] =ᵐ[μ]
        Finset.sum (Finset.range r)
          (fun i ↦ μ[(fun ω ↦ (offspring n i ω : ℝ)) | ℱZ n]) := by
    exact
      (condExp_congr_ae (Filter.EventuallyEq.of_eq hsum)).trans <|
        condExp_finset_sum (μ := μ) (s := Finset.range r)
          (f := fun i ω ↦ (offspring n i ω : ℝ))
          (fun i _ ↦
            galtonWatsonOffspringIntegrableReal_ofVariancePos
              (p := p) (μ := μ) (offspring := offspring) hoffspring_law hvar_pos n i)
          (ℱZ n)
  calc
    μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n]
        =ᵐ[μ] μ[prefixRow | ℱZ n] := by
          exact condExp_congr_ae <| Filter.EventuallyEq.of_eq <| by
            funext ω
            simp [prefixRow]
    _ =ᵐ[μ]
          Finset.sum (Finset.range r)
            (fun i ↦ μ[(fun ω ↦ (offspring n i ω : ℝ)) | ℱZ n]) := by
          exact hcond_sum
    _ =ᵐ[μ] Finset.sum (Finset.range r) (fun _ ↦ fun _ ↦ m) := by
          exact eventuallyEq_sum fun i _ ↦
            galtonWatsonOffspring_condExp_real_ofVariancePos
              (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
              hZ hsucc hoffspring_indep hoffspring_meas hoffspring_law hvar_pos n i
    _ =ᵐ[μ] fun _ ↦ (r : ℝ) * m := by
          exact Filter.Eventually.of_forall fun _ ↦ by simp

/-- Helper for Theorem 11.19: for a fixed prefix length, the conditional expectation of the fresh
offspring-row sum is the deterministic prefix length times the offspring mean. -/
private lemma galtonWatsonGenerationCondExpFixedPrefixReal_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n r : ℕ) :
    μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n] =ᵐ[μ]
      fun _ ↦ (r : ℝ) * m := by
  rcases measurableOffspringModification
      (Z := Z) (p := p) (offspring := offspring) hZ_sm hsucc hoffspring_indep hoffspring_law with
    ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
      hoffspringMeas_law, hagree⟩
  have hprefix_eq :
      (fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) =ᵐ[μ]
        fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspringMeas n i ω : ℝ)) := by
    filter_upwards [hagree] with ω hω
    simp [hω]
  calc
    μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n]
        =ᵐ[μ]
          μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspringMeas n i ω : ℝ))) | ℱZ n] := by
            exact condExp_congr_ae hprefix_eq
    _ =ᵐ[μ] fun _ ↦ (r : ℝ) * m := by
          exact galtonWatsonGenerationCondExpFixedPrefixReal_ofMeasurable_ofVariancePos
            (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspringMeas)
            hZ hsucc_meas hoffspringMeas_indep hoffspringMeas_meas hoffspringMeas_law hvar_pos n r

/-- Helper for Theorem 11.19: on each generation slice `{Z n = r}`, the next-generation integral
agrees with the integral of the mean offspring count times the current population. -/
private lemma galtonWatsonGenerationSliceIntegral_eq_meanMul_ofMeasurable_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[ℱZ n] s) (r : ℕ) :
    ∫ ω in s ∩ {ω | Z n ω = r}, (Z (n + 1) ω : ℝ) ∂μ
      = ∫ ω in s ∩ {ω | Z n ω = r}, m * (Z n ω : ℝ) ∂μ := by
  have hslice :
      MeasurableSet[ℱZ n] ((Z n) ⁻¹' {r}) :=
    (Filtration.stronglyAdapted_natural hZ_sm n).measurable (measurableSet_singleton r)
  have hA_rel : MeasurableSet[ℱZ n] (s ∩ {ω | Z n ω = r}) := by
    simpa [Set.preimage] using hs.inter hslice
  have hA : MeasurableSet (s ∩ {ω | Z n ω = r}) :=
    Filtration.le _ _ _ hA_rel
  have hprefix_int :
      Integrable (fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) μ := by
    -- Proof comment: the deterministic prefix is a finite sum of integrable offspring variables.
    simpa using
      (integrable_finset_sum (Finset.range r) fun i _ ↦
        galtonWatsonOffspringIntegrableReal_ofVariancePos
          (p := p) (μ := μ) (offspring := offspring) hoffspring_law hvar_pos n i)
  have hprefix_condExp :
      μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n] =ᵐ[μ]
        fun _ ↦ (r : ℝ) * m := by
    simpa using
      galtonWatsonGenerationCondExpFixedPrefixReal_ofMeasurable_ofVariancePos
        (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
        hZ hsucc hoffspring_indep hoffspring_meas hoffspring_law hvar_pos n r
  calc
    ∫ ω in s ∩ {ω | Z n ω = r}, (Z (n + 1) ω : ℝ) ∂μ
        =
          ∫ ω in s ∩ {ω | Z n ω = r},
            Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ)) ∂μ := by
              -- Proof comment: on the fiber `{Z n = r}`, the next generation collapses to the
              -- deterministic prefix sum of that length.
              refine setIntegral_congr_ae hA ?_
              exact Filter.Eventually.of_forall fun ω hω ↦ by
                rcases hω with ⟨_, hz⟩
                have hz' : Z n ω = r := by simpa using hz
                simp [hsucc n ω, hz']
    _ =
          ∫ ω in s ∩ {ω | Z n ω = r},
            μ[(fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))) | ℱZ n] ω ∂μ := by
              symm
              exact setIntegral_condExp (Filtration.le _ _) hprefix_int hA_rel
    _ = ∫ ω in s ∩ {ω | Z n ω = r}, (r : ℝ) * m ∂μ := by
          -- Proof comment: the fixed-prefix conditional expectation is the constant
          -- `(r : ℝ) * m` on the entire slice.
          refine setIntegral_congr_ae hA ?_
          exact hprefix_condExp.mono fun ω hω _ ↦ hω
    _ = ∫ ω in s ∩ {ω | Z n ω = r}, m * (Z n ω : ℝ) ∂μ := by
          -- Proof comment: the right-hand side is also constant on the same fiber.
          symm
          refine setIntegral_congr_ae hA ?_
          exact Filter.Eventually.of_forall fun ω hω ↦ by
            rcases hω with ⟨_, hz⟩
            have hz' : Z n ω = r := by simpa using hz
            simp [hz', mul_comm]

/-- Helper for Theorem 11.19: on each generation slice `{Z n = r}`, the next-generation integral
agrees with the integral of the mean offspring count times the current population. -/
private lemma galtonWatsonGenerationSliceIntegral_eq_meanMul_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[ℱZ n] s) (r : ℕ) :
    ∫ ω in s ∩ {ω | Z n ω = r}, (Z (n + 1) ω : ℝ) ∂μ
      = ∫ ω in s ∩ {ω | Z n ω = r}, m * (Z n ω : ℝ) ∂μ := by
  rcases measurableOffspringModification
      (Z := Z) (p := p) (offspring := offspring) hZ_sm hsucc hoffspring_indep hoffspring_law with
    ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
      hoffspringMeas_law, _hagree⟩
  exact galtonWatsonGenerationSliceIntegral_eq_meanMul_ofMeasurable_ofVariancePos
    (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspringMeas)
    hZ hsucc_meas hoffspringMeas_indep hoffspringMeas_meas hoffspringMeas_law hvar_pos n hs r

/-- Helper for Theorem 11.19: the real cast of the current generation is relatively measurable
for the natural filtration at time `n`. -/
private lemma galtonWatsonGenerationReal_measurable_natural
    (n : ℕ) :
    Measurable[ℱZ n] (fun ω ↦ (Z n ω : ℝ)) := by
  -- Proof comment: compose the natural-filtration measurability of `Z n` with the measurable
  -- embedding `ℕ ↪ ℝ`.
  exact MeasurableEmbedding.natCast.measurable.comp
    (Filtration.stronglyAdapted_natural hZ_sm n).measurable

/-- Helper for Theorem 11.19: an integrable set integral can be decomposed over the fibers of a
measurable `ℕ`-valued map. -/
private lemma galtonWatsonSetIntegral_eq_tsum_fibers
    {T : Ω → ℕ} (hT : Measurable T) {s : Set Ω} (hs : MeasurableSet s)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω in s, f ω ∂μ = ∑' r : ℕ, ∫ ω in s ∩ {ω | T ω = r}, f ω ∂μ := by
  let A : ℕ → Set Ω := fun r ↦ s ∩ {ω | T ω = r}
  have hA_meas : ∀ r : ℕ, MeasurableSet (A r) := by
    intro r
    exact hs.inter (hT (measurableSet_singleton r))
  have hA_disjoint : Pairwise (fun r r' ↦ Disjoint (A r) (A r')) := by
    intro r r' hrr'
    refine Set.disjoint_left.2 ?_
    intro ω hω hω'
    have hr : T ω = r := hω.2
    have hr' : T ω = r' := hω'.2
    exact hrr' (hr.symm.trans hr')
  have hA_cover : s = ⋃ r : ℕ, A r := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨T ω, ?_⟩
      simp [A, hω]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨r, hr⟩
      exact hr.1
  have hf_on_union : IntegrableOn f (⋃ r : ℕ, A r) μ := by
    simpa [hA_cover] using hf.integrableOn
  -- Proof comment: the fibers `s ∩ {T = r}` form a measurable disjoint partition of `s`, so the
  -- set integral is the countable sum of the fiberwise integrals.
  calc
    ∫ ω in s, f ω ∂μ = ∫ ω in ⋃ r : ℕ, A r, f ω ∂μ := by rw [hA_cover]
    _ = ∑' r : ℕ, ∫ ω in A r, f ω ∂μ := by
      rw [integral_iUnion hA_meas hA_disjoint hf_on_union]
    _ = ∑' r : ℕ, ∫ ω in s ∩ {ω | T ω = r}, f ω ∂μ := by rfl

/-- Helper for Theorem 11.19: on a fiber `{Z n = r}`, the next generation equals a fixed
offspring-row prefix and is therefore integrable. -/
private lemma galtonWatsonGenerationIntegrableOnFiber_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n r : ℕ) :
    IntegrableOn (fun ω ↦ (Z (n + 1) ω : ℝ)) {ω | Z n ω = r} μ := by
  let prefixRow : Ω → ℝ :=
    fun ω ↦ Finset.sum (Finset.range r) (fun i ↦ (offspring n i ω : ℝ))
  have hprefix_int : Integrable prefixRow μ := by
    -- Proof comment: the fixed prefix is a finite sum of integrable offspring coordinates.
    simpa [prefixRow] using
      (integrable_finset_sum (Finset.range r) fun i _ ↦
        galtonWatsonOffspringIntegrableReal_ofVariancePos
          (p := p) (μ := μ) (offspring := offspring) hoffspring_law hvar_pos n i)
  have hfiber_meas : MeasurableSet {ω | Z n ω = r} := by
    exact (hZ_sm n).measurable (measurableSet_singleton r)
  refine (hprefix_int.integrableOn).congr_fun ?_ hfiber_meas
  intro ω hω
  have hz : Z n ω = r := by simpa using hω
  simp [prefixRow, hsucc n ω, hz]

/-- Helper for Theorem 11.19: each generation size is integrable after casting from `ℕ` to `ℝ`.
-/
private lemma galtonWatsonGenerationIntegrableReal_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    ∀ n, Integrable (fun ω ↦ (Z n ω : ℝ)) μ := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: a Galton--Watson process starts from one ancestor, so `Z₀ = 1`.
      simpa [IsGaltonWatsonProcess.initial hZ] using
        (integrable_const : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ)
  | succ n ih =>
      let f : Ω → ℝ := fun ω ↦ (Z (n + 1) ω : ℝ)
      let g : Ω → ℝ := fun ω ↦ m * (Z n ω : ℝ)
      let A : ℕ → Set Ω := fun r ↦ {ω | Z n ω = r}
      have hm0 : 0 < m := (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).1
      have hg_int : Integrable g μ := by
        -- Proof comment: the induction hypothesis transfers integrability to the mean-scaled
        -- current generation.
        simpa [g] using ih.const_mul m
      have hf_nonneg : 0 ≤ᵐ[μ] f := by
        -- Proof comment: generation sizes are nonnegative after casting to `ℝ`.
        filter_upwards with ω
        exact Nat.cast_nonneg (Z (n + 1) ω)
      have hg_nonneg : 0 ≤ᵐ[μ] g := by
        -- Proof comment: the offspring mean is positive and `Z n` is nonnegative.
        filter_upwards with ω
        exact mul_nonneg hm0.le (Nat.cast_nonneg (Z n ω))
      have hf_aesm : AEStronglyMeasurable f μ := by
        -- Proof comment: `Z (n + 1)` is strongly measurable and the cast `ℕ → ℝ` is measurable.
        simpa [f] using
          (MeasurableEmbedding.natCast.measurable.comp
            (hZ_sm (n + 1)).measurable).aestronglyMeasurable
      have hA_meas : ∀ r : ℕ, MeasurableSet (A r) := by
        intro r
        exact (hZ_sm n).measurable (measurableSet_singleton r)
      have hA_disjoint : Pairwise (fun r r' ↦ Disjoint (A r) (A r')) := by
        intro r r' hrr'
        refine Set.disjoint_left.2 ?_
        intro ω hω hω'
        exact hrr' (hω.symm.trans hω')
      have hA_union : Set.univ = ⋃ r : ℕ, A r := by
        ext ω
        simp [A]
      have hfiber_lintegral :
          ∀ r : ℕ,
            ∫⁻ ω in A r, ENNReal.ofReal (f ω) ∂μ =
              ∫⁻ ω in A r, ENNReal.ofReal (g ω) ∂μ := by
        intro r
        have hslice_int :
            ∫ ω in A r, f ω ∂μ = ∫ ω in A r, g ω ∂μ := by
          -- Proof comment: the slice identity is the only transport step from the offspring
          -- prefix computation to the generation-level integral.
          simpa [A, f, g] using
            galtonWatsonGenerationSliceIntegral_eq_meanMul_ofVariancePos
              (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
              hZ hsucc hoffspring_indep hoffspring_law hvar_pos n
              (s := Set.univ) (hs := by simp) r
        have hfiber_int : IntegrableOn f (A r) μ := by
          simpa [f, A] using
            galtonWatsonGenerationIntegrableOnFiber_ofVariancePos
              (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
              hsucc hoffspring_law hvar_pos n r
        have hgfiber_int : IntegrableOn g (A r) μ := hg_int.integrableOn
        have hfiber_nonneg : 0 ≤ᵐ[μ.restrict (A r)] f := by
          filter_upwards with ω
          exact Nat.cast_nonneg (Z (n + 1) ω)
        have hgfiber_nonneg : 0 ≤ᵐ[μ.restrict (A r)] g := by
          filter_upwards with ω
          exact mul_nonneg hm0.le (Nat.cast_nonneg (Z n ω))
        have hleft :
            ENNReal.ofReal (∫ ω in A r, f ω ∂μ) =
              ∫⁻ ω in A r, ENNReal.ofReal (f ω) ∂μ := by
          simpa [A, f] using
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (μ := μ.restrict (A r)) hfiber_int hfiber_nonneg)
        have hright :
            ENNReal.ofReal (∫ ω in A r, g ω ∂μ) =
              ∫⁻ ω in A r, ENNReal.ofReal (g ω) ∂μ := by
          simpa [A, g] using
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (μ := μ.restrict (A r)) hgfiber_int hgfiber_nonneg)
        calc
          ∫⁻ ω in A r, ENNReal.ofReal (f ω) ∂μ = ENNReal.ofReal (∫ ω in A r, f ω ∂μ) := by
            exact hleft.symm
          _ = ENNReal.ofReal (∫ ω in A r, g ω ∂μ) := by rw [hslice_int]
          _ = ∫⁻ ω in A r, ENNReal.ofReal (g ω) ∂μ := hright
      have hlintegral_eq :
          ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
        -- Proof comment: sum the fiberwise lower-integral identities over the measurable
        -- partition `{Z n = r}`.
        calc
          ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ ω in Set.univ, ENNReal.ofReal (f ω) ∂μ := by
            rw [Measure.restrict_univ]
          _ = ∫⁻ ω in ⋃ r : ℕ, A r, ENNReal.ofReal (f ω) ∂μ := by rw [hA_union]
          _ = ∑' r : ℕ, ∫⁻ ω in A r, ENNReal.ofReal (f ω) ∂μ := by
            exact lintegral_iUnion hA_meas hA_disjoint (fun ω ↦ ENNReal.ofReal (f ω))
          _ = ∑' r : ℕ, ∫⁻ ω in A r, ENNReal.ofReal (g ω) ∂μ := by
            exact tsum_congr hfiber_lintegral
          _ = ∫⁻ ω in ⋃ r : ℕ, A r, ENNReal.ofReal (g ω) ∂μ := by
            symm
            exact lintegral_iUnion hA_meas hA_disjoint (fun ω ↦ ENNReal.ofReal (g ω))
          _ = ∫⁻ ω in Set.univ, ENNReal.ofReal (g ω) ∂μ := by rw [hA_union]
          _ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by rw [Measure.restrict_univ]
      have hg_lintegral_ne_top : ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ ≠ ∞ := by
        have hright :
            ENNReal.ofReal (∫ ω, g ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
          simpa [g] using MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg
        rw [← hright]
        exact ENNReal.ofReal_ne_top
      refine (lintegral_ofReal_ne_top_iff_integrable hf_aesm hf_nonneg).1 ?_
      rw [hlintegral_eq]
      exact hg_lintegral_ne_top

/-- Helper for Theorem 11.19: conditioning the next generation on the current natural filtration
returns the offspring mean times the current generation size. -/
private lemma galtonWatsonGeneration_condExp_real_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n : ℕ) :
    μ[(fun ω ↦ (Z (n + 1) ω : ℝ)) | ℱZ n] =ᵐ[μ] fun ω ↦ m * (Z n ω : ℝ) := by
  let f : Ω → ℝ := fun ω ↦ (Z (n + 1) ω : ℝ)
  let g : Ω → ℝ := fun ω ↦ m * (Z n ω : ℝ)
  have hf_int : Integrable f μ :=
    galtonWatsonGenerationIntegrableReal_ofVariancePos
      (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
      hZ hsucc hoffspring_indep hoffspring_law hvar_pos (n + 1)
  have hg_int : Integrable g μ := by
    simpa [g] using
      (galtonWatsonGenerationIntegrableReal_ofVariancePos
        (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
        hZ hsucc hoffspring_indep hoffspring_law hvar_pos n).const_mul m
  have hZn_meas : Measurable (Z n) := (hZ_sm n).measurable
  have hZn_rel_meas : Measurable[ℱZ n] (fun ω ↦ (Z n ω : ℝ)) :=
    galtonWatsonGenerationReal_measurable_natural (Z := Z) (hZ_sm := hZ_sm) n
  have hg_meas : AEStronglyMeasurable[ℱZ n] g μ := by
    simpa [g] using (hZn_rel_meas.const_mul m).aestronglyMeasurable
  -- Route correction: normalize the test-set integrals once by the fiber partition, rather than
  -- reopening the slice decomposition inside the uniqueness proof.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) (f := f) (g := g)
    (hm := Filtration.le _ _) hf_int
    (fun s _ _ ↦ hg_int.integrableOn) ?_ hg_meas).symm
  intro s hs hμs
  have hs_meas : MeasurableSet s := Filtration.le _ _ s hs
  calc
    ∫ ω in s, g ω ∂μ
        = ∑' r : ℕ, ∫ ω in s ∩ {ω | Z n ω = r}, g ω ∂μ := by
            simpa [g] using
              galtonWatsonSetIntegral_eq_tsum_fibers
                (μ := μ) (T := Z n) hZn_meas hs_meas (f := g) hg_int
    _ = ∑' r : ℕ, ∫ ω in s ∩ {ω | Z n ω = r}, f ω ∂μ := by
          refine tsum_congr fun r ↦ ?_
          simpa [f, g] using
            (galtonWatsonGenerationSliceIntegral_eq_meanMul_ofVariancePos
              (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
              hZ hsucc hoffspring_indep hoffspring_law hvar_pos n
              (s := s) (hs := hs) r).symm
    _ = ∫ ω in s, f ω ∂μ := by
          simpa [f] using
            (galtonWatsonSetIntegral_eq_tsum_fibers
              (μ := μ) (T := Z n) hZn_meas hs_meas (f := f) hf_int).symm

/-- Helper for Theorem 11.19: the real-cast generation process has the integrability and
one-step conditional-expectation owners needed for Lemma 11.18. -/
private lemma galtonWatsonGenerationRealOwner_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    (∀ n, Integrable (fun ω ↦ (Z n ω : ℝ)) μ) ∧
      (∀ n, μ[(fun ω ↦ (Z (n + 1) ω : ℝ)) | ℱZ n] =ᵐ[μ] fun ω ↦ m * (Z n ω : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact galtonWatsonGenerationIntegrableReal_ofVariancePos
      (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
      hZ hsucc hoffspring_indep hoffspring_law hvar_pos n
  · intro n
    exact galtonWatsonGeneration_condExp_real_ofVariancePos
      (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
      hZ hsucc hoffspring_indep hoffspring_law hvar_pos n

/-- Helper for Theorem 11.19: the normalized Galton--Watson process should be a martingale for the
natural filtration of `Z`. -/
private lemma galtonWatsonNormalizedProcess_martingale
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    Martingale W ℱZ μ := by
  let Zℝ : ℕ → Ω → ℝ := fun n ω ↦ (Z n ω : ℝ)
  have hZℝ_sm : ∀ n, StronglyMeasurable (Zℝ n) := by
    intro n
    exact (MeasurableEmbedding.natCast.measurable.comp (hZ_sm n).measurable).stronglyMeasurable
  have hℱ_eq : Filtration.natural Zℝ hZℝ_sm = ℱZ := by
    have hNatCast :
        MeasurableSpace.comap (Nat.cast : ℕ → ℝ) Real.measurableSpace =
          Nat.instMeasurableSpace :=
      MeasurableEmbedding.natCast.comap_eq
    -- Proof comment: composing `Z` with the measurable embedding `ℕ ↪ ℝ` does not change the
    -- natural filtration.
    apply Filtration.ext
    funext n
    have hcomap :
        ∀ j, MeasurableSpace.comap (Zℝ j) Real.measurableSpace =
          MeasurableSpace.comap (Z j) Nat.instMeasurableSpace := by
      intro j
      calc
        MeasurableSpace.comap (Zℝ j) Real.measurableSpace
            = MeasurableSpace.comap ((Nat.cast : ℕ → ℝ) ∘ Z j) Real.measurableSpace := by
                rfl
        _ = MeasurableSpace.comap (Z j)
              (MeasurableSpace.comap (Nat.cast : ℕ → ℝ) Real.measurableSpace) := by
                rw [MeasurableSpace.comap_comp]
        _ = MeasurableSpace.comap (Z j) Nat.instMeasurableSpace := by
                rw [hNatCast]
    simp [Filtration.natural, hcomap]
  have hm_pos : 0 < m := (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).1
  rcases hZ.exists_offspring with ⟨offspring, hsucc, hoffspring_indep, hoffspring_law⟩
  have howner :
      (∀ n, Integrable (fun ω ↦ (Z n ω : ℝ)) μ) ∧
        (∀ n, μ[(fun ω ↦ (Z (n + 1) ω : ℝ)) | ℱZ n] =ᵐ[μ] fun ω ↦ m * (Z n ω : ℝ)) :=
    galtonWatsonGenerationRealOwner_ofVariancePos
      (Z := Z) (p := p) (hZ_sm := hZ_sm) (offspring := offspring)
      hZ hsucc hoffspring_indep hoffspring_law hvar_pos
  have hZ_int : ∀ n, Integrable (Zℝ n) μ := by
    intro n
    simpa [Zℝ] using howner.1 n
  have h_step :
      ∀ n, μ[Zℝ (n + 1) | (Filtration.natural Zℝ hZℝ_sm) n] =ᵐ[μ] fun ω ↦ m * Zℝ n ω := by
    intro n
    -- Proof comment: the branching-step conditional expectation is already proved for the
    -- nat-generated filtration.
    rw [hℱ_eq]
    simpa [Zℝ] using howner.2 n
  -- Proof comment: Lemma 11.18 now applies directly to the casted generation process `Zℝ`.
  simpa [branchingNormalizedProcess, Zℝ, hℱ_eq] using
    branchingNormalizedProcess_martingale hm_pos hZℝ_sm hZ_int h_step

/-- Helper for Theorem 11.19: the normalized branching process is pointwise nonnegative. -/
private lemma branchingNormalizedProcess_nonneg
    (hm : 0 < m) :
    0 ≤ W := by
  intro n ω
  have hm_nonneg : 0 ≤ m := le_of_lt hm
  -- Proof comment: both the normalization factor `(m^n)⁻¹` and the population size are nonnegative.
  simpa [branchingNormalizedProcess] using
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg hm_nonneg n))
      (Nat.cast_nonneg (Z n ω))

/-- Helper for Theorem 11.19: the normalized process starts from the constant random variable
`1`. -/
private lemma branchingNormalizedProcess_zero_eq_one
    (hZ : IsGaltonWatsonProcess Z μ p) :
    W 0 = fun _ ↦ (1 : ℝ) := by
  -- Proof comment: the initial generation is one ancestor, and the time-zero normalization is trivial.
  funext ω
  simp [branchingNormalizedProcess, IsGaltonWatsonProcess.initial hZ ω]

/-- Helper for Theorem 11.19: the normalized Galton--Watson process converges almost surely to
its canonical limit process. -/
private lemma branchingNormalizedProcess_ae_tendsto_limitProcess
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ W n ω) atTop (𝓝 (W∞ ω)) := by
  have hm_pos : 0 < m := (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).1
  have hW_mart :
      Martingale W ℱZ μ :=
    galtonWatsonNormalizedProcess_martingale (Z := Z) (p := p) hZ_sm hZ hvar_pos
  have hW_nonneg : 0 ≤ W :=
    branchingNormalizedProcess_nonneg (Z := Z) (p := p) hm_pos
  have hW0 : ∫ ω, W 0 ω ∂μ = (1 : ℝ) := by
    -- Proof comment: the normalized process starts from the constant random variable `1`.
    rw [show W 0 = fun _ ↦ (1 : ℝ) by
      exact branchingNormalizedProcess_zero_eq_one (Z := Z) (p := p) hZ]
    simp
  have hExpectationEq : ∀ n, ∫ ω, W n ω ∂μ = (1 : ℝ) := by
    intro n
    calc
      ∫ ω, W n ω ∂μ = ∫ ω, W 0 ω ∂μ := by
        simpa [setIntegral_univ] using
          (hW_mart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
      _ = 1 := hW0
  have hBound : ∀ n, eLpNorm (W n) 1 μ ≤ ENNReal.ofReal (1 : ℝ) := by
    intro n
    exact le_of_eq <| by
      calc
        eLpNorm (W n) 1 μ = ENNReal.ofReal (∫ ω, ‖W n ω‖ ∂μ) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          exact (ofReal_integral_norm_eq_lintegral_enorm (hW_mart.integrable n)).symm
        _ = ENNReal.ofReal (∫ ω, W n ω ∂μ) := by
          refine congrArg ENNReal.ofReal ?_
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall fun ω ↦ hW_nonneg n ω] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg hω]
        _ = ENNReal.ofReal 1 := by rw [hExpectationEq n]
  -- Proof comment: the constant `L¹` bound yields the standard almost-sure convergence to the
  -- canonical limit process.
  exact hW_mart.submartingale.ae_tendsto_limitProcess hBound

/-- Helper for Theorem 11.19: a common `HasLaw` witness identifies the induced `PMF` exactly. -/
private lemma natRandomVariableLaw_eq_of_hasLaw
    {X : Ω → ℕ} (hXm : Measurable X) (hX : HasLaw X p.toMeasure μ) :
    natRandomVariableLaw μ X hXm = p := by
  -- Proof comment: compare singleton masses after rewriting the pushforward measure using the
  -- `HasLaw` witness.
  ext k
  rw [← PMF.toMeasure_apply_singleton
    (natRandomVariableLaw μ X hXm) k (measurableSet_singleton k)]
  rw [natRandomVariableLaw_toMeasure, hX.map_eq]
  exact PMF.toMeasure_apply_singleton p k (measurableSet_singleton k)

/-- Helper for Theorem 11.19: equal `ℕ`-valued random variables induce the same pushed-forward
law. -/
private lemma natRandomVariableLaw_congr
    {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y) (hXY : X = Y) :
    natRandomVariableLaw μ X hX = natRandomVariableLaw μ Y hY := by
  -- Proof comment: the induced law depends only on the underlying random variable.
  subst hXY
  rfl

/-- Helper for Theorem 11.19: the fresh offspring row at generation `n` is independent of all
earlier offspring rows. -/
private lemma offspringRowSpace_indep_offspringPast
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hoffspring_meas : ∀ k i, Measurable (offspring k i))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (n : ℕ) :
    Indep (offspringRowSpace (Ω := Ω) offspring n)
      (offspringPast (Ω := Ω) offspring n) μ := by
  let mOff : ℕ × ℕ → MeasurableSpace Ω := fun ij ↦
    MeasurableSpace.comap (fun ω ↦ offspring ij.1 ij.2 ω) Nat.instMeasurableSpace
  have hDisjoint :
      Disjoint {ij : ℕ × ℕ | ij.1 = n} {ij : ℕ × ℕ | ij.1 < n} := by
    refine Set.disjoint_left.2 ?_
    intro ij hij hpast
    exact lt_irrefl n (hij ▸ hpast)
  -- Proof comment: the whole row at time `n` and the strict past use disjoint coordinates of the
  -- offspring array, so sigma-algebra independence comes from `indep_iSup_of_disjoint`.
  simpa [mOff, offspringRowSpace, offspringPast] using
    (@ProbabilityTheory.indep_iSup_of_disjoint Ω (ℕ × ℕ) mOff _ μ
      (fun ij ↦ (hoffspring_meas ij.1 ij.2).comap_le)
      (galtonWatsonOffspringComap_iIndep (μ := μ) hoffspring_indep)
      {ij : ℕ × ℕ | ij.1 = n} {ij : ℕ × ℕ | ij.1 < n} hDisjoint)

/-- Helper for Theorem 11.19: the full current offspring row is measurable with respect to the
sigma-algebra generated by that row. -/
private lemma rowSequence_comap_le_offspringRowSpace
    {offspring : ℕ → ℕ → Ω → ℕ} (n : ℕ) :
    MeasurableSpace.comap (fun ω ↦ fun i : ℕ ↦ offspring n i ω) inferInstance ≤
      offspringRowSpace (Ω := Ω) offspring n := by
  let _ : MeasurableSpace Ω := offspringRowSpace (Ω := Ω) offspring n
  have hrow_meas :
      Measurable (fun ω ↦ fun i : ℕ ↦ offspring n i ω) := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_iff_comap_le.mpr <|
      le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
  simpa using hrow_meas.comap_le

/-- Helper for Theorem 11.19: the initial generation has probability generating function `z`,
because the process starts from one ancestor. -/
private lemma galtonWatsonGenerationProbabilityGeneratingFunction_zero
    (hZ : IsGaltonWatsonProcess Z μ p) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw μ (Z 0) (hZ_sm 0).measurable) z : ℝ) =
      (z : ℝ) := by
  have hZ0 : Z 0 = fun _ : Ω ↦ (1 : ℕ) := by
    funext ω
    exact hZ.initial ω
  -- Proof comment: the time-zero generation is the deterministic singleton population, so its
  -- pgf is just `z ↦ z`.
  rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral μ (Z 0)
    (hZ_sm 0).measurable z]
  simp [hZ0]

/-- Helper for Theorem 11.19: evaluating the pgf of a law on `ℕ` at `0` isolates the mass at
`0`. -/
private lemma probabilityGeneratingFunction_zero_eq_zeroMass (p : PMF ℕ) :
    (probabilityGeneratingFunction p ⟨0, by simp⟩ : ℝ) = (p 0).toReal := by
  -- Proof comment: in the defining pgf series, only the zeroth term survives at `z = 0`.
  rw [probabilityGeneratingFunction_apply, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- Helper for Theorem 11.19: the current generation size is independent of the fresh offspring
row used to build the next generation. -/
private lemma galtonWatsonGeneration_indep_offspringRow
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_meas : ∀ n i, Measurable (offspring n i))
    (n : ℕ) :
    IndepFun (Z n) (fun ω ↦ fun k : ℕ ↦ offspring n k ω) μ := by
  -- Route correction: prove independence from the whole fresh row via the row-generated
  -- sigma-algebra, instead of trying to assemble it coordinate by coordinate.
  have hbase :
      Indep (offspringRowSpace (Ω := Ω) offspring n)
        (offspringPast (Ω := Ω) offspring n) μ :=
    offspringRowSpace_indep_offspringPast (Ω := Ω) (μ := μ) (offspring := offspring)
      hoffspring_meas hoffspring_indep n
  have hgen :
      MeasurableSpace.comap (Z n) inferInstance ≤ offspringPast (Ω := Ω) offspring n :=
    (galtonWatsonGeneration_measurable_offspringPast_self
      (Z := Z) (p := p) (offspring := offspring) hZ hsucc n).comap_le
  have hrow :
      MeasurableSpace.comap (fun ω ↦ fun k : ℕ ↦ offspring n k ω) inferInstance ≤
        offspringRowSpace (Ω := Ω) offspring n :=
    rowSequence_comap_le_offspringRowSpace (Ω := Ω) (offspring := offspring) n
  have hIndep :
      Indep (MeasurableSpace.comap (Z n) inferInstance)
        (MeasurableSpace.comap (fun ω ↦ fun k : ℕ ↦ offspring n k ω) inferInstance) μ := by
    have hgen_row :
        Indep (MeasurableSpace.comap (Z n) inferInstance)
          (offspringRowSpace (Ω := Ω) offspring n) μ := by
      exact (ProbabilityTheory.indep_of_indep_of_le_right hbase hgen).symm
    -- Proof comment: `Z n` is measurable with respect to the strict past, while the row map is
    -- measurable with respect to the sigma-algebra generated by the fresh row.
    exact ProbabilityTheory.indep_of_indep_of_le_right hgen_row hrow
  exact (ProbabilityTheory.IndepFun_iff_Indep _ _ _).2 hIndep

/-- Helper for Theorem 11.19: the next-generation pgf is obtained by composing the current
generation pgf with the offspring pgf. -/
private lemma galtonWatsonGenerationProbabilityGeneratingFunction_succ
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw μ (Z (n + 1)) (hZ_sm (n + 1)).measurable) z : ℝ) =
      (probabilityGeneratingFunction
        (natRandomVariableLaw μ (Z n) (hZ_sm n).measurable)
        (probabilityGeneratingFunction p z) : ℝ) := by
  -- Route correction: replace the failed coordinatewise-independence route by one measurable
  -- offspring modification, then invoke the generic random-sum pgf theorem on the whole row.
  obtain ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
      hoffspringMeas_law, _⟩ :=
    measurableOffspringModification (Z := Z) (p := p) (μ := μ) (hZ_meas := hZ_sm)
      hsucc hoffspring_indep hoffspring_law
  have hgen_indep :
      IndepFun (Z n) (fun ω ↦ fun i : ℕ ↦ offspringMeas n i ω) μ :=
    galtonWatsonGeneration_indep_offspringRow
      (Z := Z) (p := p) (μ := μ) (offspring := offspringMeas)
      hZ hsucc_meas hoffspringMeas_indep hoffspringMeas_meas n
  have hrow_indep : iIndepFun (fun i : ℕ ↦ offspringMeas n i) μ := by
    exact hoffspringMeas_indep.precomp (g := fun i : ℕ ↦ (n, i)) <| by
      intro i j hij
      simpa using congrArg Prod.snd hij
  have hrow_ident :
      ∀ i, IdentDistrib (offspringMeas n i) (offspringMeas n 0) μ μ := by
    intro i
    exact (hoffspringMeas_law n i).identDistrib (hoffspringMeas_law n 0)
  have hrow_law :
      natRandomVariableLaw μ (offspringMeas n 0) (hoffspringMeas_meas n 0) = p := by
    simpa using natRandomVariableLaw_eq_of_hasLaw
      (μ := μ) (p := p) (hXm := hoffspringMeas_meas n 0) (hX := hoffspringMeas_law n 0)
  have hpgf_comp :
      (probabilityGeneratingFunction
          (natRandomVariableLaw μ
            (natRandomSum (Z n) (fun i : ℕ ↦ offspringMeas n i))
            (measurable_natRandomSum (Z n) (hZ_sm n).measurable
              (fun i : ℕ ↦ offspringMeas n i) (hoffspringMeas_meas n))) z : ℝ) =
        (probabilityGeneratingFunction
          (natRandomVariableLaw μ (Z n) (hZ_sm n).measurable)
          (probabilityGeneratingFunction
            (natRandomVariableLaw μ (offspringMeas n 0) (hoffspringMeas_meas n 0)) z) : ℝ) := by
    exact
      probabilityGeneratingFunction_natRandomSum_eq_comp_of_indepFun_of_iIndepFun_of_identDistrib
        (μ := μ) (T := Z n) (hT := (hZ_sm n).measurable)
        (X := fun i : ℕ ↦ offspringMeas n i) (hX := hoffspringMeas_meas n)
        hgen_indep hrow_indep hrow_ident z
  have hsucc_fun :
      Z (n + 1) = natRandomSum (Z n) (fun i : ℕ ↦ offspringMeas n i) := by
    funext ω
    simp [natRandomSum_apply, hsucc_meas]
  -- Proof comment: rewrite the successor generation as the random sum over the repaired fresh
  -- row, then collapse the common offspring law back to `p`.
  calc
    (probabilityGeneratingFunction
        (natRandomVariableLaw μ (Z (n + 1)) (hZ_sm (n + 1)).measurable) z : ℝ)
        =
          (probabilityGeneratingFunction
            (natRandomVariableLaw μ
              (natRandomSum (Z n) (fun i : ℕ ↦ offspringMeas n i))
              (measurable_natRandomSum (Z n) (hZ_sm n).measurable
                (fun i : ℕ ↦ offspringMeas n i) (hoffspringMeas_meas n))) z : ℝ) := by
            rw [natRandomVariableLaw_congr (μ := μ) (hX := (hZ_sm (n + 1)).measurable)
              (hY := measurable_natRandomSum (Z n) (hZ_sm n).measurable
                (fun i : ℕ ↦ offspringMeas n i) (hoffspringMeas_meas n)) hsucc_fun]
    _ = (probabilityGeneratingFunction
          (natRandomVariableLaw μ (Z n) (hZ_sm n).measurable)
          (probabilityGeneratingFunction
            (natRandomVariableLaw μ (offspringMeas n 0) (hoffspringMeas_meas n 0)) z) : ℝ) := by
          exact hpgf_comp
    _ = (probabilityGeneratingFunction
          (natRandomVariableLaw μ (Z n) (hZ_sm n).measurable)
          (probabilityGeneratingFunction p z) : ℝ) := by
          rw [hrow_law]

/-- Helper for Theorem 11.19: iterating the offspring pgf gives the pgf of each later
generation. -/
private lemma galtonWatsonGenerationProbabilityGeneratingFunction_eq_iterate
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ) :
    ∀ n (z : Set.Icc (0 : ℝ) 1),
      (probabilityGeneratingFunction
          (natRandomVariableLaw μ (Z (n + 1)) (hZ_sm (n + 1)).measurable) z : ℝ) =
        (((probabilityGeneratingFunction p)^[n + 1]) z : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro z
      calc
        (probabilityGeneratingFunction
            (natRandomVariableLaw μ (Z (0 + 1)) (hZ_sm (0 + 1)).measurable) z : ℝ)
            =
              (probabilityGeneratingFunction
                (natRandomVariableLaw μ (Z 0) (hZ_sm 0).measurable)
                (probabilityGeneratingFunction p z) : ℝ) := by
                  exact galtonWatsonGenerationProbabilityGeneratingFunction_succ
                    (Z := Z) (p := p) (μ := μ) hZ_sm (offspring := offspring)
                    hZ hsucc hoffspring_indep hoffspring_law 0 z
        _ = (probabilityGeneratingFunction p z : ℝ) := by
              exact galtonWatsonGenerationProbabilityGeneratingFunction_zero
                (Z := Z) (p := p) (μ := μ) hZ_sm hZ (probabilityGeneratingFunction p z)
        _ = (((probabilityGeneratingFunction p)^[0 + 1]) z : ℝ) := by
              simp [Function.iterate_succ_apply]
  | succ n ih =>
      intro z
      calc
        (probabilityGeneratingFunction
            (natRandomVariableLaw μ (Z ((n + 1) + 1)) (hZ_sm ((n + 1) + 1)).measurable) z : ℝ)
            =
              (probabilityGeneratingFunction
                (natRandomVariableLaw μ (Z (n + 1)) (hZ_sm (n + 1)).measurable)
                (probabilityGeneratingFunction p z) : ℝ) := by
                  exact galtonWatsonGenerationProbabilityGeneratingFunction_succ
                    (Z := Z) (p := p) (μ := μ) hZ_sm (offspring := offspring)
                    hZ hsucc hoffspring_indep hoffspring_law (n + 1) z
        _ = (((probabilityGeneratingFunction p)^[n + 1]) (probabilityGeneratingFunction p z) : ℝ) :=
              ih (probabilityGeneratingFunction p z)
        _ = (((probabilityGeneratingFunction p)^[(n + 1) + 1]) z : ℝ) := by
              simpa [Function.iterate_succ_apply]

/-- Helper for Theorem 11.19: the subtype-valued iterates of the offspring pgf coincide with the
real-valued iterates after coercion to `ℝ`. -/
private lemma probabilityGeneratingFunctionIterate_coe_eq_realIterate
    (z : Set.Icc (0 : ℝ) 1) :
    ∀ n, (((probabilityGeneratingFunction p)^[n]) z : ℝ) =
      Nat.iterate (probabilityGeneratingFunctionReal p) n z := by
  intro n
  induction n generalizing z with
  | zero =>
      rfl
  | succ n ih =>
      -- Proof comment: one more subtype-valued pgf step matches one more real-valued pgf step
      -- because the two versions agree on the unit interval.
      simpa [Function.iterate_succ_apply, probabilityGeneratingFunction_coe_eq_real] using
        ih (probabilityGeneratingFunction p z)

/-- Helper for Theorem 11.19: the probability that the `n`th generation is already extinct is the
standard extinction approximation `q_n`. -/
private lemma galtonWatsonGenerationZeroProb_eq_extinctionApproximation
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ_meas : ∀ n, StronglyMeasurable (Z n))
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ) :
    ∀ n, (μ {ω | Z n ω = 0}).toReal = galtonWatsonExtinctionApproximation p n := by
  intro n
  cases n with
  | zero =>
      have hZ0 : Z 0 = fun _ : Ω ↦ (1 : ℕ) := by
        funext ω
        exact hZ.initial ω
      -- Proof comment: the process starts from one ancestor, so extinction at time `0` has
      -- probability `0`, matching the zeroth extinction approximation.
      simp [hZ0, galtonWatsonExtinctionApproximation_zero]
  | succ n =>
      let z0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
      have hpgf :=
        galtonWatsonGenerationProbabilityGeneratingFunction_eq_iterate
          (Z := Z) (p := p) (μ := μ) hZ_meas (offspring := offspring)
          hZ hsucc hoffspring_indep hoffspring_law n z0
      have hzero_mass :
          (probabilityGeneratingFunction
              (natRandomVariableLaw μ (Z (n + 1)) (hZ_meas (n + 1)).measurable) z0 : ℝ) =
            (μ {ω | Z (n + 1) ω = 0}).toReal := by
        rw [probabilityGeneratingFunction_zero_eq_zeroMass]
        rw [← PMF.toMeasure_apply_singleton
          (natRandomVariableLaw μ (Z (n + 1)) (hZ_meas (n + 1)).measurable) 0
          (measurableSet_singleton 0)]
        rw [natRandomVariableLaw_toMeasure]
        have hmap_zero :
            ((Measure.map (Z (n + 1)) μ) {0}).toReal =
              (μ {ω | Z (n + 1) ω = 0}).toReal := by
          rw [Measure.map_apply (hZ_meas (n + 1)).measurable (measurableSet_singleton 0)]
          rfl
        exact hmap_zero
      -- Proof comment: evaluate the pgf identity at `0`; the left side becomes the zero-mass
      -- of the `n + 1` generation, and the right side is the extinction approximation iterate.
      rw [hzero_mass] at hpgf
      simpa [galtonWatsonExtinctionApproximation, z0] using
        hpgf.trans (probabilityGeneratingFunctionIterate_coe_eq_realIterate
          (p := p) (z := z0) (n := n + 1))

/-- Helper for Theorem 11.19: extinction probability `1` forces almost-sure extinction of the
Galton--Watson process at some finite generation. -/
private lemma galtonWatsonExtinctionAE_of_extinctionProbability_one
    (hZ_meas : ∀ n, StronglyMeasurable (Z n))
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hq : galtonWatsonExtinctionProbability p = 1) :
    ∀ᵐ ω ∂μ, ∃ n, Z n ω = 0 := by
  rcases hZ.exists_offspring with ⟨offspring, hsucc, hoffspring_indep, hoffspring_law⟩
  let A : ℕ → Set Ω := fun n ↦ {ω | Z n ω = 0}
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact (hZ_meas n).measurable (measurableSet_singleton 0)
  have hA_mono : Monotone A := by
    refine monotone_nat_of_le_succ ?_
    intro n ω hω
    -- Proof comment: once a generation is extinct, the next generation is the empty offspring
    -- sum and therefore also zero.
    calc
      Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω) := hsucc n ω
      _ = Finset.sum (Finset.range 0) (fun i ↦ offspring n i ω) := by rw [hω]
      _ = 0 := by simp
  have hApprox_tendsto :
      Tendsto (galtonWatsonExtinctionApproximation p) atTop
        (𝓝 (galtonWatsonExtinctionProbability p)) := by
    have hMono := galtonWatsonExtinctionApproximation_monotone p
    have hBddIci : BddAbove ((galtonWatsonExtinctionApproximation p) '' Set.Ici 0) := by
      refine ⟨1, ?_⟩
      intro x hx
      rcases hx with ⟨n, -, rfl⟩
      exact (galtonWatsonExtinctionApproximation_mem_unitInterval p n).2
    have hRangeEq :
        (galtonWatsonExtinctionApproximation p) '' Set.Ici 0 =
          Set.range (galtonWatsonExtinctionApproximation p) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨n, -, rfl⟩
        exact Set.mem_range_self n
      · intro hx
        rcases hx with ⟨n, rfl⟩
        exact ⟨n, Nat.zero_le n, rfl⟩
    -- Proof comment: the extinction approximations are an increasing bounded real sequence, so
    -- they converge to the supremum defining `q`.
    rw [galtonWatsonExtinctionProbability_def, ← hRangeEq]
    exact Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
      (fun k hk n hn hkn ↦ hMono hkn) hBddIci
  have hApprox_tendsto_one :
      Tendsto (galtonWatsonExtinctionApproximation p) atTop (𝓝 (1 : ℝ)) := by
    simpa [hq] using hApprox_tendsto
  have hMeasure_tendsto_one :
      Tendsto (fun n ↦ (μ (A n)).toReal) atTop (𝓝 (1 : ℝ)) := by
    refine Tendsto.congr' ?_ hApprox_tendsto_one
    exact Filter.Eventually.of_forall fun n ↦
      (galtonWatsonGenerationZeroProb_eq_extinctionApproximation
        (Z := Z) (p := p) (μ := μ) hZ_meas hZ hsucc hoffspring_indep hoffspring_law n).symm
  have hUnion_tendsto :
      Tendsto (fun n ↦ (μ (A n)).toReal) atTop (𝓝 ((μ (⋃ n, A n)).toReal)) := by
    -- Proof comment: continuity from below identifies the limit of the extinction-event
    -- probabilities with the probability of their increasing union.
    simpa [Function.comp, A] using
      ((ENNReal.tendsto_toReal (measure_ne_top μ (⋃ n, A n))).comp
        (tendsto_measure_iUnion_atTop (μ := μ) hA_mono))
  have hUnion_prob_one : μ (⋃ n, A n) = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).mp <|
      tendsto_nhds_unique hUnion_tendsto hMeasure_tendsto_one
  have hUnion_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, A n := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hA_meas)).2 hUnion_prob_one
  filter_upwards [hUnion_ae] with ω hω
  simpa [A] using hω

/-- Helper for Theorem 11.19: if the branching process hits zero almost surely, then the
canonical normalized limit vanishes almost everywhere. -/
private lemma branchingNormalizedLimit_ae_eq_zero_of_extinctionAE
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure])
    (hExt : ∀ᵐ ω ∂μ, ∃ n, Z n ω = 0) :
    W∞ =ᵐ[μ] fun _ ↦ 0 := by
  have hm_pos : 0 < m := (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).1
  rcases hZ.exists_offspring with ⟨offspring, hsucc, _hoffspring_indep, _hoffspring_law⟩
  filter_upwards
    [hExt, branchingNormalizedProcess_ae_tendsto_limitProcess
      (Z := Z) (p := p) hZ_sm hZ hvar_pos] with ω hω_ext hω_tendsto
  rcases hω_ext with ⟨n, hn⟩
  have hzero_tail : ∀ k : ℕ, Z (n + k) ω = 0 := by
    intro k
    induction k with
    | zero =>
        simpa using hn
    | succ k hk =>
        -- Proof comment: once a generation is zero, the recursion forces every later generation
        -- to stay zero because the offspring sum runs over an empty range.
        simpa [hk] using hsucc (n + k) ω
  have hW_eventually_zero :
      (fun k ↦ W k ω) =ᶠ[atTop] fun _ ↦ (0 : ℝ) := by
    refine Filter.eventually_atTop.2 ⟨n, ?_⟩
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    -- Proof comment: every normalized population value beyond the extinction time is exactly zero.
    simp [branchingNormalizedProcess, hzero_tail j]
  have hW_tendsto_zero : Tendsto (fun k ↦ W k ω) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_const_nhds.congr' hW_eventually_zero.symm
  exact tendsto_nhds_unique hω_tendsto hW_tendsto_zero

/-- Helper for Theorem 11.19: positive offspring variance rules out the degenerate law
`P[X₁,₁ = 1] = 1`. -/
private lemma offspringMassOne_ne_one_ofVariancePos
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    p 1 ≠ 1 := by
  intro hp1
  have hmem : MemLp (fun k : ℕ ↦ (k : ℝ)) 2 p.toMeasure :=
    (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).2
  have hid_int : Integrable (fun k : ℕ ↦ (k : ℝ)) p.toMeasure :=
    hmem.integrable one_le_two
  have hsq_int : Integrable (fun k : ℕ ↦ (k : ℝ) ^ 2) p.toMeasure := by
    exact (MeasureTheory.memLp_two_iff_integrable_sq
      MeasurableEmbedding.natCast.measurable.aestronglyMeasurable).1 hmem
  have hsupport : p.support = {1} := (PMF.apply_eq_one_iff p 1).1 hp1
  have hp_zero : ∀ k : ℕ, k ≠ 1 → p k = 0 := by
    intro k hk
    by_contra hpk
    have hk_mem : k ∈ p.support := (PMF.mem_support_iff p k).2 hpk
    have : k = 1 := by simpa [hsupport] using hk_mem
    exact hk this
  have hid_eq_one : ∫ k, (k : ℝ) ∂p.toMeasure = 1 := by
    calc
      ∫ k, (k : ℝ) ∂p.toMeasure = ∑' k : ℕ, (p k).toReal * (k : ℝ) := by
        simpa [smul_eq_mul] using PMF.integral_eq_tsum p (fun k : ℕ ↦ (k : ℝ)) hid_int
      _ = (p 1).toReal * (1 : ℝ) := by
        rw [tsum_eq_single 1]
        · simp
        · intro k hk
          simp [hp_zero k hk]
      _ = 1 := by simp [hp1]
  have hsq_eq_one : ∫ k, (k : ℝ) ^ 2 ∂p.toMeasure = 1 := by
    calc
      ∫ k, (k : ℝ) ^ 2 ∂p.toMeasure = ∑' k : ℕ, (p k).toReal * ((k : ℝ) ^ 2) := by
        simpa [smul_eq_mul] using PMF.integral_eq_tsum p (fun k : ℕ ↦ (k : ℝ) ^ 2) hsq_int
      _ = (p 1).toReal * ((1 : ℝ) ^ 2) := by
        rw [tsum_eq_single 1]
        · simp
        · intro k hk
          simp [hp_zero k hk]
      _ = 1 := by simp [hp1]
  have hvar_zero : Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure] = 0 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    rw [show ∫ x, ((fun k : ℕ ↦ (k : ℝ)) ^ 2) x ∂p.toMeasure =
        ∫ k, (k : ℝ) ^ 2 ∂p.toMeasure by rfl]
    rw [hsq_eq_one, hid_eq_one]
    norm_num
  exact (ne_of_gt hvar_pos) hvar_zero

/-- Helper for Theorem 11.19: every real-cast offspring variable has the same `L²` integrability
as the offspring law under the positive-variance hypothesis. -/
private lemma galtonWatsonOffspringMemLpTwoReal_ofVariancePos
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (n i : ℕ) :
    MemLp (fun ω ↦ (offspring n i ω : ℝ)) 2 μ := by
  have hIdentNat : IdentDistrib (offspring n i) id μ p.toMeasure :=
    (hoffspring_law n i).identDistrib ProbabilityTheory.HasLaw.id
  have hIdentReal :
      IdentDistrib (fun ω ↦ (offspring n i ω : ℝ)) (fun k : ℕ ↦ (k : ℝ)) μ p.toMeasure :=
    -- Proof comment: transport the common offspring law through the measurable embedding `ℕ ↪ ℝ`.
    hIdentNat.comp MeasurableEmbedding.natCast.measurable
  exact (hIdentReal.memLp_iff).2 <|
    (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).2

/-- Helper for Theorem 11.19: for a real-valued `L²` random variable, the exponent-`2`
`eLpNorm` is the square root of its second moment. -/
private lemma eLpNormTwo_eq_ofReal_sqrt_secondMoment
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
  -- Proof comment: pass from `eLpNorm` to `lpNorm`, then use the standard `p = 2` norm formula.
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (ENNReal.toReal (eLpNorm f 2 μ)) := by
      exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
    _ = ENNReal.ofReal (lpNorm f 2 μ) := by
      rw [toReal_eLpNorm hf.aestronglyMeasurable]
    _ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
      rw [lpNorm_two_eq_sqrt_integral_sq hf]

/-- Helper for Theorem 11.19: after freezing the fresh offspring row at generation `n`, the
textbook stopped partial sum is exactly the next generation. -/
private lemma generationSucc_eq_stoppedTextbookPartialSum
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (n : ℕ) :
    stoppedValue (partialSum (fun k ω ↦ (offspring n k ω : ℝ)))
      (fun ω ↦ (Z n ω : WithTop ℕ)) =
        fun ω ↦ (Z (n + 1) ω : ℝ) := by
  -- Proof comment: the stopped partial sum at time `Z n` is the finite prefix sum defining
  -- `Z (n + 1)`, now viewed in `ℝ`.
  funext ω
  change partialSum (fun k ω ↦ (offspring n k ω : ℝ)) (Z n ω) ω = (Z (n + 1) ω : ℝ)
  rw [partialSum_apply]
  calc
    ∑ i ∈ Finset.range (Z n ω), (offspring n i ω : ℝ)
        = (↑(∑ i ∈ Finset.range (Z n ω), offspring n i ω) : ℝ) := by
            simp
    _ = (Z (n + 1) ω : ℝ) := by
          symm
          simpa using congrArg (fun t : ℕ ↦ (t : ℝ)) (hsucc n ω)

/-- Helper for Theorem 11.19: one Blackwell--Girshick step upgrades the current generation from
`L²` to the next generation and gives the one-step variance recursion. -/
private lemma galtonWatsonGenerationSucc_memLpTwo_and_varianceFormula
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hsucc : ∀ n ω, Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) μ)
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) p.toMeasure μ)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure])
    {n : ℕ} (hZn_memLp : MemLp (fun ω ↦ (Z n ω : ℝ)) 2 μ) :
    MemLp (fun ω ↦ (Z (n + 1) ω : ℝ)) 2 μ ∧
      Var[fun ω ↦ (Z (n + 1) ω : ℝ); μ] =
        m ^ 2 * Var[fun ω ↦ (Z n ω : ℝ); μ] +
          μ[fun ω ↦ (Z n ω : ℝ)] * Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure] := by
  obtain ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
      hoffspringMeas_law, _⟩ :=
    measurableOffspringModification (Z := Z) (p := p) (μ := μ) hZ_sm
      hsucc hoffspring_indep hoffspring_law
  let X : ℕ → Ω → ℝ := fun k ω ↦ (offspringMeas n (k - 1) ω : ℝ)
  have hX_shift :
      (fun k ↦ X (k + 1)) = fun k ω ↦ (offspringMeas n k ω : ℝ) := by
    -- Proof comment: the Chapter 5 indexing `X (k + 1)` matches the generation-`n` offspring row
    -- exactly after the single shift `k ↦ k - 1`.
    funext k ω
    simp [X]
  have hrow_cast_meas : Measurable (fun x : ℕ → ℕ ↦ fun k : ℕ ↦ (x k : ℝ)) := by
    -- Proof comment: the rowwise cast `ℕ^ℕ → ℝ^ℕ` is coordinatewise measurable.
    fun_prop
  have hTX_indep_nat :
      IndepFun (Z n) (fun ω ↦ fun k : ℕ ↦ offspringMeas n k ω) μ :=
    galtonWatsonGeneration_indep_offspringRow
      (Z := Z) (p := p) (μ := μ) (offspring := offspringMeas)
      hZ hsucc_meas hoffspringMeas_indep hoffspringMeas_meas n
  have hTX_indep :
      IndepFun (Z n) (fun ω ↦ fun k : ℕ ↦ X (k + 1) ω) μ := by
    have hcast :
        IndepFun (Z n) (fun ω ↦ fun k : ℕ ↦ (offspringMeas n k ω : ℝ)) μ := by
      simpa [Function.comp] using
        hTX_indep_nat.comp measurable_id hrow_cast_meas
    simpa [hX_shift] using hcast
  have hX_indep_nat : iIndepFun (fun k : ℕ ↦ offspringMeas n k) μ := by
    exact hoffspringMeas_indep.precomp (g := fun k : ℕ ↦ (n, k)) <| by
      intro i j hij
      simpa using congrArg Prod.snd hij
  have hX_indep : iIndepFun (fun k ↦ X (k + 1)) μ := by
    have hcast :
        iIndepFun (fun k : ℕ ↦ fun ω ↦ (offspringMeas n k ω : ℝ)) μ := by
      simpa [Function.comp] using
        hX_indep_nat.comp (fun _ x : ℕ ↦ (x : ℝ))
          (fun _ ↦ MeasurableEmbedding.natCast.measurable)
    simpa [hX_shift] using hcast
  have hX_ident : ∀ k, IdentDistrib (X (k + 1)) (X 1) μ μ := by
    intro k
    have hNat :
        IdentDistrib (offspringMeas n k) (offspringMeas n 0) μ μ :=
      (hoffspringMeas_law n k).identDistrib (hoffspringMeas_law n 0)
    have hReal :
        IdentDistrib (fun ω ↦ (offspringMeas n k ω : ℝ))
          (fun ω ↦ (offspringMeas n 0 ω : ℝ)) μ μ :=
      hNat.comp MeasurableEmbedding.natCast.measurable
    simpa [X] using hReal
  have hX1_memLp : MemLp (X 1) 2 μ := by
    -- Proof comment: every repaired offspring coordinate inherits the common `L²` bound from the
    -- finite offspring variance.
    simpa [X] using
      galtonWatsonOffspringMemLpTwoReal_ofVariancePos
        (p := p) (μ := μ) (offspring := offspringMeas) hoffspringMeas_law hvar_pos n 0
  have hstopped_eq :
      stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (Z n ω : WithTop ℕ)) =
        fun ω ↦ (Z (n + 1) ω : ℝ) := by
    -- Proof comment: the repaired successor recursion now lives in the exact Chapter 5 normal
    -- form expected by Blackwell--Girshick.
    rw [hX_shift]
    exact generationSucc_eq_stoppedTextbookPartialSum
      (Z := Z) (offspring := offspringMeas) hsucc_meas n
  have hX1_mean : μ[X 1] = m := by
    -- Proof comment: the first textbook increment has the common offspring mean.
    simpa [X] using
      galtonWatsonOffspringIntegralReal_eq_mean_ofVariancePos
        (p := p) (μ := μ) (offspring := offspringMeas) hoffspringMeas_law hvar_pos n 0
  have hX1_ident :
      IdentDistrib (X 1) (fun k : ℕ ↦ (k : ℝ)) μ p.toMeasure := by
    have hNat :
        IdentDistrib (offspringMeas n 0) id μ p.toMeasure :=
      (hoffspringMeas_law n 0).identDistrib ProbabilityTheory.HasLaw.id
    simpa [X] using hNat.comp MeasurableEmbedding.natCast.measurable
  have hX1_var :
      Var[X 1; μ] = Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure] := by
    exact hX1_ident.variance_eq
  obtain ⟨hStopped_memLp, hStopped_var⟩ :=
    blackwell_girshick_variance_formula μ (Z n) X hTX_indep hX_indep hX_ident hZn_memLp hX1_memLp
  -- Proof comment: rewrite the Blackwell--Girshick stopped sum back to `Z (n + 1)` and collapse
  -- the common first and second moments of `X 1` to the offspring mean and offspring variance.
  refine ⟨?_, ?_⟩
  · simpa [hstopped_eq] using hStopped_memLp
  · have hvar_eq :
        Var[fun ω ↦ (Z (n + 1) ω : ℝ); μ] =
          (μ[X 1]) ^ 2 * Var[fun ω ↦ (Z n ω : ℝ); μ] +
            μ[fun ω ↦ (Z n ω : ℝ)] * Var[X 1; μ] := by
      simpa [hstopped_eq] using hStopped_var
    simpa [hX1_mean, hX1_var] using hvar_eq

/-- Helper for Theorem 11.19: in the supercritical finite-variance case, the normalized
Galton--Watson martingale has a uniform `L²` bound. -/
private lemma galtonWatsonNormalizedProcess_lpTwoBound_of_supercritical
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure])
    (hm : 1 < m) :
    ∃ C : NNReal, ∀ n, eLpNorm (W n) 2 μ ≤ C := by
  rcases hZ.exists_offspring with ⟨offspring, hsucc, hoffspring_indep, hoffspring_law⟩
  let sigmaSq : ℝ := Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]
  have hsigmaSq_nonneg : 0 ≤ sigmaSq := by
    simpa [sigmaSq] using
      (ProbabilityTheory.variance_nonneg (fun k : ℕ ↦ (k : ℝ)) p.toMeasure)
  have hm_pos : 0 < m := lt_trans zero_lt_one hm
  have hm_ne_zero : m ≠ 0 := hm_pos.ne'
  have hm_inv_nonneg : 0 ≤ (m⁻¹ : ℝ) := inv_nonneg.mpr hm_pos.le
  have hm_inv_lt_one : (m⁻¹ : ℝ) < 1 := by
    exact inv_lt_one_of_one_lt₀ hm
  have hW_mart : Martingale W (Filtration.natural Z hZ_sm) μ :=
    galtonWatsonNormalizedProcess_martingale (Z := Z) (p := p) hZ_sm hZ hvar_pos
  have hZ0_ae : ∀ᵐ ω ∂μ, (Z 0 ω : ℝ) = 1 := by
    filter_upwards with ω
    simpa using congrArg (fun t : ℕ ↦ (t : ℝ)) (hZ.initial ω)
  have hEZ : ∀ n, μ[fun ω ↦ (Z n ω : ℝ)] = m ^ n :=
    branchingProcess_expectation_eq_pow_mean hm_pos hW_mart hZ0_ae
  have hW_eq : ∀ n, W n = fun ω ↦ (m ^ n)⁻¹ * (Z n ω : ℝ) := by
    intro n
    funext ω
    simp [branchingNormalizedProcess, Pi.smul_apply, smul_eq_mul]
  have hZ_memLp : ∀ n, MemLp (fun ω ↦ (Z n ω : ℝ)) 2 μ := by
    intro n
    induction n with
    | zero =>
        have hZ0 :
            (fun ω ↦ (Z 0 ω : ℝ)) = fun _ : Ω ↦ (1 : ℝ) := by
          funext ω
          simpa using congrArg (fun t : ℕ ↦ (t : ℝ)) (hZ.initial ω)
        simpa [hZ0] using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ)
    | succ n ih =>
        exact
          (galtonWatsonGenerationSucc_memLpTwo_and_varianceFormula
            (Z := Z) (p := p) (μ := μ) hZ_sm hZ
            hsucc hoffspring_indep hoffspring_law hvar_pos ih).1
  have hW_memLp : ∀ n, MemLp (W n) 2 μ := by
    intro n
    simpa [hW_eq n] using (hZ_memLp n).const_mul ((m ^ n)⁻¹)
  have hVarW_succ :
      ∀ n, Var[W (n + 1); μ] = Var[W n; μ] + sigmaSq * (m ^ (n + 2))⁻¹ := by
    intro n
    have hstep :
        Var[fun ω ↦ (Z (n + 1) ω : ℝ); μ] =
          m ^ 2 * Var[fun ω ↦ (Z n ω : ℝ); μ] +
            μ[fun ω ↦ (Z n ω : ℝ)] * sigmaSq := by
      simpa [sigmaSq] using
        (galtonWatsonGenerationSucc_memLpTwo_and_varianceFormula
          (Z := Z) (p := p) (μ := μ) hZ_sm hZ
          hsucc hoffspring_indep hoffspring_law hvar_pos (hZ_memLp n)).2
    -- Proof comment: transport the generation-level variance recursion through the deterministic
    -- normalization `Z n ↦ W n`.
    calc
      Var[W (n + 1); μ]
          = ((m ^ (n + 1))⁻¹) ^ 2 * Var[fun ω ↦ (Z (n + 1) ω : ℝ); μ] := by
              rw [hW_eq (n + 1), ProbabilityTheory.variance_const_mul]
      _ = ((m ^ (n + 1))⁻¹) ^ 2 *
            (m ^ 2 * Var[fun ω ↦ (Z n ω : ℝ); μ] + μ[fun ω ↦ (Z n ω : ℝ)] * sigmaSq) := by
              rw [hstep]
      _ = ((m ^ n)⁻¹) ^ 2 * Var[fun ω ↦ (Z n ω : ℝ); μ] + sigmaSq * (m ^ (n + 2))⁻¹ := by
            rw [hEZ n]
            field_simp [pow_succ, hm_ne_zero]
            ring
      _ = Var[W n; μ] + sigmaSq * (m ^ (n + 2))⁻¹ := by
            rw [hW_eq n, ProbabilityTheory.variance_const_mul]
  have hVarW_formula :
      ∀ n, Var[W n; μ] = sigmaSq * ∑ i ∈ Finset.range n, (m ^ (i + 2))⁻¹ := by
    intro n
    induction n with
    | zero =>
        rw [branchingNormalizedProcess_zero_eq_one (Z := Z) (p := p) hZ]
        simpa [sigmaSq] using (ProbabilityTheory.variance_add_const (X := (0 : Ω → ℝ)) (μ := μ)
          (by fun_prop) 1)
    | succ n ih =>
        -- Proof comment: unfold one normalized variance step and absorb the new summand into the
        -- finite geometric prefix.
        rw [hVarW_succ n, ih, Finset.sum_range_succ]
        ring
  have hgeom_range :
      ∀ n, ∑ i ∈ Finset.range n, (m ^ (i + 2))⁻¹ =
        ∑ i ∈ Finset.Ico 2 (n + 2), (m⁻¹ : ℝ) ^ i := by
    intro n
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, inv_pow]
  have hVarW_bound :
      ∀ n, Var[W n; μ] ≤ sigmaSq * (((m⁻¹ : ℝ) ^ 2) / (1 - m⁻¹)) := by
    intro n
    have hgeom_le :
        ∑ i ∈ Finset.Ico 2 (n + 2), (m⁻¹ : ℝ) ^ i ≤ ((m⁻¹ : ℝ) ^ 2) / (1 - m⁻¹) :=
      geom_sum_Ico_le_of_lt_one hm_inv_nonneg hm_inv_lt_one
    rw [hVarW_formula n]
    gcongr
    calc
      ∑ i ∈ Finset.range n, (m ^ (i + 2))⁻¹
          = ∑ i ∈ Finset.Ico 2 (n + 2), (m⁻¹ : ℝ) ^ i := hgeom_range n
      _ ≤ ((m⁻¹ : ℝ) ^ 2) / (1 - m⁻¹) := hgeom_le
  have hW_expect : ∀ n, μ[W n] = (1 : ℝ) := by
    intro n
    calc
      μ[W n] = ∫ ω, (m ^ n)⁻¹ * (Z n ω : ℝ) ∂μ := by
        rw [hW_eq n]
      _ = (m ^ n)⁻¹ * μ[fun ω ↦ (Z n ω : ℝ)] := by
            simpa using
              MeasureTheory.integral_const_mul ((m ^ n)⁻¹) (fun ω ↦ (Z n ω : ℝ))
      _ = (m ^ n)⁻¹ * m ^ n := by rw [hEZ n]
      _ = 1 := by
            field_simp [pow_ne_zero n hm_ne_zero]
  have hSecondBound :
      ∀ n, μ[fun ω ↦ W n ω ^ 2] ≤ sigmaSq * (((m⁻¹ : ℝ) ^ 2) / (1 - m⁻¹)) + 1 := by
    intro n
    have hvar_sub :
        Var[W n; μ] = μ[fun ω ↦ W n ω ^ 2] - μ[W n] ^ 2 := by
      simpa [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub (hW_memLp n)
    rw [hW_expect n] at hvar_sub
    nlinarith [hvar_sub, hVarW_bound n]
  let C : NNReal :=
    ⟨Real.sqrt (sigmaSq * (((m⁻¹ : ℝ) ^ 2) / (1 - m⁻¹)) + 1), Real.sqrt_nonneg _⟩
  refine ⟨C, ?_⟩
  intro n
  -- Proof comment: convert the uniform second-moment estimate into the exponent-`2` seminorm
  -- bound via the canonical `eLpNorm` formula.
  rw [eLpNormTwo_eq_ofReal_sqrt_secondMoment (hW_memLp n)]
  simpa [C] using
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hSecondBound n))

/-- Helper for Theorem 11.19: in the supercritical finite-variance case, the canonical limit of
the normalized branching martingale should still have expectation `1`. -/
private lemma branchingProcess_limitExpectation_eq_one_of_supercritical
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure])
    (hm : 1 < m) :
    μ[W∞] = (1 : ℝ) := by
  have hW_mart : Martingale W ℱZ μ :=
    galtonWatsonNormalizedProcess_martingale (Z := Z) (p := p) hZ_sm hZ hvar_pos
  have hW_nonneg : 0 ≤ W :=
    branchingNormalizedProcess_nonneg (Z := Z) (p := p) (lt_trans zero_lt_one hm)
  obtain ⟨C, hC⟩ :=
    galtonWatsonNormalizedProcess_lpTwoBound_of_supercritical
      (Z := Z) (p := p) hZ_sm hZ hvar_pos hm
  have hC' : ∀ n, eLpNorm (W n) (ENNReal.ofReal (2 : ℝ)) μ ≤ C := by
    intro n
    simpa using hC n
  have hW_memLp : ∀ n, MemLp (W n) (ENNReal.ofReal (2 : ℝ)) μ := by
    intro n
    refine ⟨((hW_mart.stronglyMeasurable n).mono ((Filtration.natural Z hZ_sm).le n)).aestronglyMeasurable,
      ?_⟩
    exact lt_of_le_of_lt (hC' n) ENNReal.coe_lt_top
  let F : Set (Lp ℝ (ENNReal.ofReal (2 : ℝ)) μ) :=
    Set.range fun n ↦ (hW_memLp n).toLp (W n)
  have hF_bdd : by
      letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 : ℝ)) := Fact.mk (by norm_num)
      exact Bornology.IsBounded F := by
    letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 : ℝ)) := Fact.mk (by norm_num)
    refine isBounded_iff_forall_norm_le.2 ⟨(C : ℝ), ?_⟩
    intro f hfF
    rcases hfF with ⟨n, rfl⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (hC' n)
  have hUI_F : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ :=
    uniformIntegrable_of_bounded_memLp_of_one_lt
      (μ := μ) (p := 2) (F := F) (by norm_num) hF_bdd
  let Wsub : ℕ → F := fun n ↦ ⟨(hW_memLp n).toLp (W n), ⟨n, rfl⟩⟩
  have hUI_W' : UniformIntegrable (fun n ↦ ((Wsub n : F) : Ω → ℝ)) 1 μ := by
    refine ⟨fun n ↦ hUI_F.1 (Wsub n), ?_, ?_⟩
    · intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := hUI_F.2.1 hε
      exact ⟨δ, hδpos, fun n s hs hμs ↦ hδ (Wsub n) s hs hμs⟩
    · obtain ⟨B, hB⟩ := hUI_F.2.2
      exact ⟨B, fun n ↦ hB (Wsub n)⟩
  have hUI_W : UniformIntegrable W 1 μ := by
    refine hUI_W'.ae_eq ?_
    intro n
    simpa [Wsub] using MemLp.coeFn_toLp (hW_memLp n)
  have hW0 : μ[W 0] = (1 : ℝ) := by
    rw [show W 0 = fun _ ↦ (1 : ℝ) by
      exact branchingNormalizedProcess_zero_eq_one (Z := Z) (p := p) hZ]
    simp
  -- Proof comment: the `L²` bound yields uniform integrability, so Corollary 11.9 identifies the
  -- terminal expectation with the initial expectation `μ[W₀] = 1`.
  have hEq :
      μ[W∞] = μ[W 0] := by
    exact
      (nonnegative_martingale_limitProcess_expectation_eq_iff_uniformIntegrable
        (μ := μ) (ℱ := ℱZ) (X := W) hW_mart hW_nonneg).2 hUI_W
  exact hEq.trans hW0

/-- Helper for Theorem 11.19: outside the supercritical regime, the canonical normalized limit
should have expectation `0`. -/
private lemma branchingProcess_limitExpectation_eq_zero_of_not_supercritical
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure])
    (hm_le : m ≤ 1) :
    μ[W∞] = (0 : ℝ) := by
  -- Route correction: close the non-supercritical branch through the Chapter 3 extinction
  -- criterion, then use the already-stable limit-vanishing lemma on the extinction event.
  have hm_pos : 0 < m := (offspringMeanPos_memLpTwo_of_variancePos (p := p) hvar_pos).1
  have hmean_ne_top : galtonWatsonOffspringMean p ≠ ⊤ :=
    offspringMean_ne_top_of_pos (p := p) hm_pos
  have hp1_ne : p 1 ≠ 1 := offspringMassOne_ne_one_ofVariancePos (p := p) hvar_pos
  rcases galtonWatson_extinctionProbability_fixedPoints_and_supercriticality p hp1_ne with
    ⟨_, hq_lt_iff, hmean_gt_iff⟩
  have hnot_mean_gt : ¬ 1 < galtonWatsonOffspringMean p := by
    intro hmean_gt
    have hm_gt : 1 < m := by
      simpa using
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hmean_ne_top).2 hmean_gt
    linarith
  have hnot_q_lt : ¬ galtonWatsonExtinctionProbability p < 1 := by
    intro hq_lt
    exact hnot_mean_gt <| hmean_gt_iff.mp <| hq_lt_iff.mp hq_lt
  have hq_eq_one : galtonWatsonExtinctionProbability p = 1 := by
    have hq_mem : galtonWatsonExtinctionProbability p ∈ Set.Icc (0 : ℝ) 1 :=
      galtonWatsonExtinctionProbability_mem_unitInterval p
    exact le_antisymm hq_mem.2 (le_of_not_gt hnot_q_lt)
  have hExt_ae :
      ∀ᵐ ω ∂μ, ∃ n, Z n ω = 0 :=
    galtonWatsonExtinctionAE_of_extinctionProbability_one
      (Z := Z) (p := p) (μ := μ) hZ_sm hZ hq_eq_one
  have hLimit_zero :
      W∞ =ᵐ[μ] fun _ ↦ (0 : ℝ) :=
    branchingNormalizedLimit_ae_eq_zero_of_extinctionAE
      (Z := Z) (p := p) (μ := μ) hZ_sm hZ hvar_pos hExt_ae
  -- Proof comment: once the limit process vanishes almost surely, its expectation is the
  -- expectation of the zero function.
  rw [integral_congr_ae hLimit_zero]
  simp

-- Proof sketch: derive the normalized-process martingale from the Galton--Watson owner structure,
-- apply the almost-sure martingale convergence theorem to the normalized population for the
-- natural filtration of `Z`, and combine the finite-variance `L²` bound with Theorem 11.10 and
-- the Chapter 3 supercriticality/extinction criterion for the offspring law `p`.
/- Theorem 11.19 is `source-facing`: it concerns the normalized branching-process population and
the supercriticality criterion expressed through its canonical terminal random variable. Its
`core/canonical` owner layer is the Chapter 3 Galton--Watson owner `IsGaltonWatsonProcess Z μ p`,
the offspring-law mean `galtonWatsonOffspringMean p`, and the normalized process
`branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) (galtonWatsonOffspringMean p).toReal` for the
natural filtration of `Z`. Any auxiliary offspring array is part of the internal `bridge/view`
layer via `IsGaltonWatsonProcess.exists_offspring`, not the public theorem interface. -/
/-- Theorem 11.19: for a Galton--Watson process `Z` with offspring law `p`, if the offspring
variance is strictly positive, then the normalized population
`W_n = Z_n / (galtonWatsonOffspringMean p)^n` converges almost surely to its canonical limit
process for the natural filtration of `Z`, and the following are equivalent: the offspring mean is
strictly greater than `1`; the expectation of the limit equals `1`; the expectation of the limit
is strictly positive. -/
theorem branchingProcess_normalizedPopulation_limitProcess_and_supercriticality_tfae
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ W n ω) atTop (𝓝 (W∞ ω))) ∧
      List.TFAE [1 < m, μ[W∞] = 1, 0 < μ[W∞]] := by
  refine ⟨branchingNormalizedProcess_ae_tendsto_limitProcess
    (Z := Z) (p := p) hZ_sm hZ hvar_pos, ?_⟩
  -- Proof comment: the finite-variance supercritical branch gives `μ[W∞] = 1`, the implication
  -- `1 = μ[W∞] → 0 < μ[W∞]` is immediate, and the converse to supercriticality follows from the
  -- already-proved expectation-zero branch.
  tfae_have 1 → 2 := by
    intro hm
    exact branchingProcess_limitExpectation_eq_one_of_supercritical
      (Z := Z) (p := p) (hZ_sm := hZ_sm) hZ hvar_pos hm
  tfae_have 2 → 3 := by
    intro hEqOne
    linarith
  tfae_have 3 → 1 := by
    intro hPos
    by_contra hm_not
    have hm_le : m ≤ 1 := le_of_not_gt hm_not
    have hEqZero :
        μ[W∞] = (0 : ℝ) :=
      branchingProcess_limitExpectation_eq_zero_of_not_supercritical
        (Z := Z) (p := p) (hZ_sm := hZ_sm) hZ hvar_pos hm_le
    linarith
  tfae_finish

end
