/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.CharacteristicFunction
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: verified use of
-- `ProbabilityTheory.iIndepFun.charFun_map_fun_finset_sum_eq_prod` and
-- `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

/-- The complex-valued analogue of Chapter 3's `probabilityGeneratingSeries`, evaluated at `z`. -/
noncomputable def probabilityGeneratingSeriesComplex (μ : Measure ℕ) (z : ℂ) : ℂ :=
  tsum (fun n : ℕ ↦ (μ {n}).toReal * z ^ n)

/-- The random sum `ω ↦ ∑_{i=1}^{N(ω)} X_i(ω)` for a textbook-style sequence `X 1, X 2, …`. -/
noncomputable def randomFiniteSum {Ω : Type u} {d : ℕ}
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Ω → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ Finset.sum (Finset.Icc 1 (N ω)) (fun i ↦ X i ω)

/-- Theorem 15.14 (1): item (i). A countable nonnegative weighted sum of finite measures on
`ℝ^d` has characteristic function equal to the corresponding weighted sum of the individual
characteristic functions. -/
-- Proof sketch: treat `Measure.sum (fun n ↦ (p n : ENNReal) • μ n)` as the canonical countable
-- weighted measure sum, use linearity of the integral on finite partial sums, and pass to the
-- limit through the weighted total-mass finiteness assumption.
theorem charFun_weighted_measure_sum_eq_tsum {d : ℕ}
    (p : ℕ → NNReal) (μ : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (hμfin : ∀ n, (μ n) Set.univ ≠ ⊤)
    (hfin : tsum (fun n : ℕ ↦ ((p n : ENNReal) * ((μ n) Set.univ))) ≠ ⊤)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (Measure.sum (fun n ↦ ((p n : ENNReal) • μ n))) t =
      tsum (fun n : ℕ ↦ (((p n : ℝ) : ℂ) * charFun (μ n) t)) := by
  let ν : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n ↦ ((p n : ENNReal) • μ n)
  have hν_univ : (Measure.sum ν) Set.univ < ⊤ := by
    -- Proof comment: the total mass of the weighted sum is exactly the hypothesis `hfin`.
    simpa [ν, Measure.sum_apply _ MeasurableSet.univ, lt_top_iff_ne_top] using hfin
  let _ : IsFiniteMeasure (Measure.sum ν) := ⟨hν_univ⟩
  have hkernel :
      Integrable (fun x ↦ BoundedContinuousFunction.innerProbChar t x) (Measure.sum ν) := by
    -- Proof comment: the Fourier kernel is bounded and continuous, hence integrable on any finite
    -- measure.
    simpa using
      (BoundedContinuousFunction.innerProbChar t).integrable (Measure.sum ν)
  rw [charFun_eq_integral_innerProbChar, integral_sum_measure hkernel]
  refine tsum_congr fun n ↦ ?_
  have hνn_univ : (ν n) Set.univ < ⊤ := by
    -- Proof comment: each weighted component remains finite because `p n < ∞` and `μ n` is
    -- finite.
    simpa [ν, Measure.smul_apply, lt_top_iff_ne_top, mul_comm] using
      ENNReal.mul_ne_top (by simp) (hμfin n)
  let _ : IsFiniteMeasure (ν n) := ⟨hνn_univ⟩
  have hkernel_n :
      Integrable (fun x ↦ BoundedContinuousFunction.innerProbChar t x) (ν n) := by
    -- Proof comment: the same bounded-kernel argument applies termwise.
    simpa using
      (BoundedContinuousFunction.innerProbChar t).integrable (ν n)
  have hνn : ν n = ((p n : ENNReal) • μ n) := rfl
  rw [charFun_eq_integral_innerProbChar, hνn, integral_smul_measure]
  change ((((p n : ENNReal).toReal : ℂ) *
      ∫ x, BoundedContinuousFunction.innerProbChar t x ∂μ n)) =
    (((p n : ℝ) : ℂ) * ∫ x, BoundedContinuousFunction.innerProbChar t x ∂μ n)
  simp

/-- Auxiliary lemma: the textbook sum over `Finset.Icc 1 n` is the standard shifted
`Finset.range n` sum. -/
private theorem randomFiniteSum_fixedCount_eq_rangeSum {Ω : Type u} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (fun ω ↦ Finset.sum (Finset.Icc 1 n) (fun i ↦ X i ω)) =
      fun ω ↦ ∑ k ∈ Finset.range n, X (k + 1) ω := by
  -- Proof comment: rewrite `Icc 1 n` as `Ico 1 (n + 1)` and then reindex that interval by
  -- `Finset.range n`.
  funext ω
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Auxiliary lemma: the fixed-count random sum has characteristic function
`charFun (P.map (X 1)) t ^ n`. -/
private theorem charFun_randomFiniteSum_fixedCount_eq_pow
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (n : ℕ) (t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (fun ω ↦ Finset.sum (Finset.Icc 1 n) (fun i ↦ X i ω))) t =
      (charFun (P.map (X 1)) t) ^ n := by
  -- Proof comment: normalize the finite sum to `Finset.range n` and then apply the standard iid
  -- characteristic-function factorization for a finite sum.
  rw [randomFiniteSum_fixedCount_eq_rangeSum]
  rw [(hX_indep.restrict (Finset.range n)).charFun_map_fun_finset_sum_eq_prod
    (fun i _ ↦ (hX_ident i).aemeasurable_fst)]
  simp [fun i ↦ (hX_ident i).map_eq]

/-- Auxiliary definition: the prefix-sum map on `ℕ × (ℕ → ℝ^d)` sends `(n, s)` to
`∑ k ∈ Finset.range n, s k`. -/
private def prefixSumNatSequence {d : ℕ} :
    ℕ × (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
  fun p ↦ ∑ k ∈ Finset.range p.1, p.2 k

/-- Auxiliary lemma: the prefix-sum map on `ℕ × (ℕ → ℝ^d)` is measurable. -/
private theorem measurablePrefixSumNatSequence {d : ℕ} :
    Measurable
      (prefixSumNatSequence :
        ℕ × (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) := by
  -- Proof comment: measurability is checked one countable fiber `n : ℕ` at a time, where the
  -- map is just a finite sum of coordinate evaluations.
  refine measurable_from_prod_countable_right ?_
  intro n
  exact Finset.measurable_sum (Finset.range n) fun k _ ↦ measurable_pi_apply k

/-- Auxiliary definition: the shifted tail sequence `ω ↦ (n ↦ X (n + 1) ω)`. -/
private def natTailSequence {Ω : Type u} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) :
    Ω → ℕ → EuclideanSpace ℝ (Fin d) :=
  fun ω n ↦ X (n + 1) ω

/-- Auxiliary lemma: the joint law of `N` and the tail sequence
`ω ↦ fun n ↦ X (n + 1) ω` is the product of their marginal laws. -/
private theorem jointLaw_natTailSequence_eq_prod
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hN_aemeas : AEMeasurable N P)
    (hTail_aemeas : AEMeasurable (natTailSequence X) P)
    (hN_seq_indep : IndepFun N (natTailSequence X) P) :
    P.map (fun ω ↦ (N ω, natTailSequence X ω)) =
      (P.map N).prod (P.map (natTailSequence X)) := by
  -- Proof comment: this is exactly the standard map-to-product characterization of independence.
  exact (indepFun_iff_map_prod_eq_prod_map_map hN_aemeas hTail_aemeas).1 hN_seq_indep

/-- Auxiliary lemma: pushing `((Measure.dirac n).prod ν)` through the prefix-sum map
collapses to pushing `ν` through the fixed `Finset.range n` sum. -/
private theorem mapPrefixSum_diracProd_eq_mapRangeSum
    {d : ℕ} (ν : Measure (ℕ → EuclideanSpace ℝ (Fin d))) [SFinite ν] (n : ℕ) :
    (((Measure.dirac n).prod ν).map
        (prefixSumNatSequence :
          ℕ × (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))) =
      ν.map (fun s ↦ ∑ k ∈ Finset.range n, s k) := by
  -- Route correction: collapse the pure `dirac_prod` transport before introducing any
  -- `AEMeasurable` pushforward rewrites.
  rw [Measure.dirac_prod]
  -- Proof comment: once the left factor is a Dirac mass, the prefix-sum map only sees the fixed
  -- count `n`, so the double pushforward is a single pushforward by the `range` sum.
  rw [Measure.map_map measurablePrefixSumNatSequence measurable_prodMk_left]
  rfl

/-- Auxiliary lemma: pushing a single nat atom through the prefix-sum map gives the law
of the fixed-count textbook sum. -/
private theorem natAtomComponent_eq_fixedCountLaw
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hTail_aemeas : AEMeasurable (natTailSequence X) P)
    (n : ℕ) :
    (((Measure.dirac n).prod (P.map (natTailSequence X))).map
        (prefixSumNatSequence :
          ℕ × (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))) =
      P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω) := by
  let rangeSum : (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun s ↦ ∑ k ∈ Finset.range n, s k
  have hRange_meas : Measurable rangeSum := by
    -- Proof comment: a fixed finite coordinate sum is measurable on the sequence space.
    exact Finset.measurable_sum (Finset.range n) fun k _ ↦ measurable_pi_apply k
  let _ : IsProbabilityMeasure (P.map (natTailSequence X)) :=
    Measure.isProbabilityMeasure_map hTail_aemeas
  -- Proof comment: first collapse the pure `dirac` transport, then rewrite the remaining map
  -- through the tail sequence using one `AEMeasurable.map_map_of_aemeasurable`.
  rw [mapPrefixSum_diracProd_eq_mapRangeSum]
  rw [AEMeasurable.map_map_of_aemeasurable hRange_meas.aemeasurable hTail_aemeas]
  congr 1
  funext ω
  simpa [rangeSum, natTailSequence] using
    (congrFun (randomFiniteSum_fixedCount_eq_rangeSum X n) ω).symm

/-- Auxiliary lemma: the law of `randomFiniteSum N X` is the countable weighted sum of
the fixed-count sum laws indexed by the law of `N`. -/
private theorem randomFiniteSumLaw_eq_measureSum
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hN_aemeas : AEMeasurable N P)
    (hTail_aemeas : AEMeasurable (natTailSequence X) P)
    (hN_seq_indep : IndepFun N (natTailSequence X) P) :
    P.map (randomFiniteSum N X) =
      Measure.sum (fun n : ℕ ↦
        (P.map N) {n} • P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω)) := by
  have hrepr :
      randomFiniteSum N X =
        prefixSumNatSequence ∘ fun ω ↦ (N ω, natTailSequence X ω) := by
    -- Proof comment: rewrite the textbook `Icc` sum as the prefix-sum map applied to the pair
    -- consisting of the count and the tail sequence.
    funext ω
    simpa [randomFiniteSum, Function.comp] using
      congrFun (randomFiniteSum_fixedCount_eq_rangeSum X (N ω)) ω
  have hPair_aemeas :
      AEMeasurable (fun ω ↦ (N ω, natTailSequence X ω)) P := by
    -- Proof comment: both components are already a.e.-measurable, so the pair map is too.
    exact hN_aemeas.prodMk hTail_aemeas
  -- Proof comment: move the random sum to the joint law of `(N, tail)`, then expand the counting
  -- law as a sum of weighted Dirac masses and rewrite each atom by the fixed-count law.
  rw [hrepr,
    ← AEMeasurable.map_map_of_aemeasurable measurablePrefixSumNatSequence.aemeasurable
      hPair_aemeas]
  rw [jointLaw_natTailSequence_eq_prod P N X hN_aemeas hTail_aemeas hN_seq_indep]
  rw [← Measure.sum_smul_dirac (P.map N), Measure.prod_sum_left,
    Measure.map_sum measurablePrefixSumNatSequence.aemeasurable]
  refine congrArg Measure.sum ?_
  funext n
  rw [Measure.sum_smul_dirac_singleton, Measure.prod_smul_left, Measure.map_smul,
    natAtomComponent_eq_fixedCountLaw P X hTail_aemeas n]

/-- Auxiliary lemma: the singleton masses of `poissonMeasure lam` are the explicit
Poisson masses `poissonPMFReal lam n`. -/
private lemma poissonMeasure_apply_singleton (lam : NNReal) (n : ℕ) :
    poissonMeasure lam ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal lam n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure attached to the standard Poisson PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF lam) n (measurableSet_singleton n))

/-- Auxiliary lemma: the complex-valued Poisson probability generating series is the
exponential `exp (λ (z - 1))`. -/
private theorem probabilityGeneratingSeriesComplex_poissonMeasure_eq_exp
    (lam : NNReal) (z : ℂ) :
    probabilityGeneratingSeriesComplex (poissonMeasure lam) z =
      Complex.exp (((lam : ℝ) : ℂ) * (z - 1)) := by
  rw [Complex.exp_eq_exp_ℂ]
  have hseries :
      HasSum
        (fun n : ℕ ↦
          NormedSpace.exp (-((lam : ℝ) : ℂ)) * ((((lam : ℝ) : ℂ) * z) ^ n / ↑n.factorial))
        (NormedSpace.exp (-((lam : ℝ) : ℂ)) * NormedSpace.exp (((lam : ℝ) : ℂ) * z)) := by
    -- Proof comment: this is the standard exponential power series, scaled by `exp (-λ)`.
    simpa using
      (NormedSpace.expSeries_div_hasSum_exp (((lam : ℝ) : ℂ) * z)).mul_left
        (NormedSpace.exp (-((lam : ℝ) : ℂ)))
  -- Proof comment: rewrite each Poisson coefficient into the exponential-series term and then
  -- combine the two exponentials.
  rw [probabilityGeneratingSeriesComplex]
  calc
    ∑' n : ℕ, (poissonMeasure lam {n}).toReal * z ^ n
      = ∑' n : ℕ,
          NormedSpace.exp (-((lam : ℝ) : ℂ)) * ((((lam : ℝ) : ℂ) * z) ^ n / ↑n.factorial) := by
            refine tsum_congr fun n ↦ ?_
            rw [poissonMeasure_apply_singleton, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
            rw [poissonPMFReal]
            have hfac : ((n.factorial : ℝ) : ℂ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero n
            rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
            rw [mul_pow]
            rw [Complex.exp_eq_exp_ℂ]
            field_simp [hfac]
            have hfac_cancel : ((((n.factorial : ℝ) : ℂ) * (↑n.factorial)⁻¹ : ℂ)) = 1 := by
              simpa [div_eq_mul_inv] using (div_self hfac)
            have hmain :
              NormedSpace.exp (-((lam : ℝ) : ℂ)) * (((lam : ℝ) : ℂ) ^ n) * z ^ n
                  = (((lam : ℝ) : ℂ) ^ n) * z ^ n *
                      ((((n.factorial : ℝ) : ℂ) * NormedSpace.exp (-((lam : ℝ) : ℂ)) *
                        (↑n.factorial)⁻¹)) := by
                calc
                  NormedSpace.exp (-((lam : ℝ) : ℂ)) * (((lam : ℝ) : ℂ) ^ n) * z ^ n
                      = NormedSpace.exp (-((lam : ℝ) : ℂ)) * (((lam : ℝ) : ℂ) ^ n) *
                          z ^ n * 1 := by
                            simp
                  _ = NormedSpace.exp (-((lam : ℝ) : ℂ)) * (((lam : ℝ) : ℂ) ^ n) *
                        z ^ n * ((((n.factorial : ℝ) : ℂ) * (↑n.factorial)⁻¹ : ℂ)) := by
                            rw [hfac_cancel]
                  _ = (((lam : ℝ) : ℂ) ^ n) * z ^ n *
                        ((((n.factorial : ℝ) : ℂ) * NormedSpace.exp (-((lam : ℝ) : ℂ)) *
                          (↑n.factorial)⁻¹)) := by
                            ring
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmain
    _ = NormedSpace.exp (-((lam : ℝ) : ℂ)) * NormedSpace.exp (((lam : ℝ) : ℂ) * z) := by
          exact hseries.tsum_eq
    _ = NormedSpace.exp (((lam : ℝ) : ℂ) * (z - 1)) := by
          rw [← NormedSpace.exp_add]
          congr 1
          ring

/-- Auxiliary lemma: the fixed-count textbook sum is a.e. measurable once all
positive-index summands are. -/
private theorem aemeasurable_fixedCountRandomFiniteSum
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX_ae : ∀ n, AEMeasurable (X (n + 1)) P)
    (n : ℕ) :
    AEMeasurable (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω) P := by
  -- Proof comment: finite sums preserve a.e. measurability, and each `i ∈ Icc 1 n` is
  -- uniquely of the form `k + 1`.
  simpa [Finset.sum_fn] using
    (Finset.aemeasurable_sum (Finset.Icc 1 n) fun i hi ↦ by
      have hi_mem := Finset.mem_Icc.mp hi
      have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one hi_mem.1
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi_pos)
      simpa using hX_ae k)

/-- Auxiliary lemma: every fixed-count sum law has total mass `1`. -/
private theorem fixedCountSumLaw_univ_eq_one
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX_ae : ∀ n, AEMeasurable (X (n + 1)) P)
    (n : ℕ) :
    (P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω)) Set.univ = 1 := by
  -- Proof comment: push forward the probability measure `P` along the a.e. measurable
  -- fixed-count sum map.
  letI : IsProbabilityMeasure (P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω)) :=
    Measure.isProbabilityMeasure_map (aemeasurable_fixedCountRandomFiniteSum P X hX_ae n)
  simp

/-- Auxiliary lemma: the singleton masses of the counting law sum to `1`. -/
private theorem natLaw_singleton_tsum_eq_one
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ)
    (hN_aemeas : AEMeasurable N P) :
    tsum (fun n : ℕ ↦ (P.map N) {n}) = 1 := by
  letI : IsProbabilityMeasure (P.map N) := Measure.isProbabilityMeasure_map hN_aemeas
  -- Proof comment: evaluate the canonical singleton decomposition of a countable measure on
  -- `Set.univ`.
  calc
    tsum (fun n : ℕ ↦ (P.map N) {n})
        = (Measure.sum (fun n : ℕ ↦ (P.map N) {n} • Measure.dirac n)) Set.univ := by
            rw [Measure.sum_apply _ MeasurableSet.univ]
            refine tsum_congr fun n ↦ ?_
            simp
    _ = (P.map N) Set.univ := by rw [Measure.sum_smul_dirac]
    _ = 1 := by simp

/-- Auxiliary lemma: the characteristic function of the count-law-weighted sum of
fixed-count random-sum laws is the corresponding power series. -/
private theorem charFun_countLawWeightedFixedCount_eq_series
    {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hN_aemeas : AEMeasurable N P)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (Measure.sum (fun n : ℕ ↦
        (P.map N) {n} • P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω))) t =
      tsum (fun n : ℕ ↦ ((P.map N) {n}).toReal * (charFun (P.map (X 1)) t) ^ n) := by
  let ν : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n ↦
    (P.map N) {n} • P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω)
  have hX_ae : ∀ n, AEMeasurable (X (n + 1)) P := fun n ↦ (hX_ident n).aemeasurable_fst
  have hν_univ : (Measure.sum ν) Set.univ < ⊤ := by
    -- Proof comment: the total mass is the singleton-mass series of `P.map N`, because each
    -- fixed-count pushforward is a probability measure.
    calc
      (Measure.sum ν) Set.univ = tsum (fun n : ℕ ↦ (ν n) Set.univ) := by
        rw [Measure.sum_apply _ MeasurableSet.univ]
      _ = tsum (fun n : ℕ ↦ (P.map N) {n}) := by
        refine tsum_congr fun n ↦ ?_
        simp [ν, Measure.smul_apply, fixedCountSumLaw_univ_eq_one P X hX_ae n]
      _ = 1 := natLaw_singleton_tsum_eq_one P N hN_aemeas
      _ < ⊤ := by simp
  let _ : IsFiniteMeasure (Measure.sum ν) := ⟨hν_univ⟩
  have hkernel :
      Integrable (fun x ↦ BoundedContinuousFunction.innerProbChar t x) (Measure.sum ν) := by
    -- Proof comment: the Fourier kernel is bounded, so it is integrable against the finite total
    -- measure.
    simpa using
      (BoundedContinuousFunction.innerProbChar t).integrable (Measure.sum ν)
  -- Route correction: expand the characteristic function directly over the measure sum, keeping
  -- the nat-law weights in `ENNReal` until `integral_smul_measure` turns them into `.toReal`.
  rw [show Measure.sum (fun n : ℕ ↦
      (P.map N) {n} • P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω)) = Measure.sum ν by rfl]
  rw [charFun_eq_integral_innerProbChar, integral_sum_measure hkernel]
  refine tsum_congr fun n ↦ ?_
  rw [integral_smul_measure, ← charFun_eq_integral_innerProbChar,
    charFun_randomFiniteSum_fixedCount_eq_pow P X hX_indep hX_ident n t]
  exact Algebra.smul_def ((P.map N) {n}).toReal (charFun (P.map (X 1)) t ^ n)

/-! The source theorem is formalized below as the three clauses `(i)`, `(ii)`, and `(iii)`. -/

/-- Theorem 15.14 (2): item (ii). If `N` is independent of the whole sequence `X₁, X₂, …`, the sequence is
independent and identically distributed on `ℝ^d`, and `Y = ∑_{i=1}^N X_i`, then the characteristic
function of `Y` is the complex probability generating series of the counting law `P.map N`
evaluated at the common characteristic function of `X₁`. -/
-- Proof sketch: for the measurable counting variable `N`, condition on the event `{N = n}`,
-- identify the conditional characteristic
-- function with that of the finite sum `∑_{i=1}^n X_i`, use independence and identical
-- distribution to rewrite it as `charFun (P.map (X 1)) t ^ n`, and sum over `n`.
theorem charFun_randomFiniteSum_eq_complex_pgf {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hN_aemeas : AEMeasurable N P)
    (hN_seq_indep : IndepFun N (fun ω n ↦ X (n + 1) ω) P)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (randomFiniteSum N X)) t =
      probabilityGeneratingSeriesComplex (P.map N) (charFun (P.map (X 1)) t) := by
  have hTail_aemeas : AEMeasurable (natTailSequence X) P := by
    -- Proof comment: the tail sequence is a.e. measurable coordinatewise, so it is
    -- a.e. measurable as a product-space valued map.
    refine aemeasurable_pi_lambda _ fun n ↦ (hX_ident n).aemeasurable_fst
  calc
    charFun (P.map (randomFiniteSum N X)) t
      = charFun (Measure.sum (fun n : ℕ ↦
          (P.map N) {n} • P.map (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω))) t := by
          rw [randomFiniteSumLaw_eq_measureSum P N X hN_aemeas hTail_aemeas hN_seq_indep]
    _ = tsum (fun n : ℕ ↦ ((P.map N) {n}).toReal * (charFun (P.map (X 1)) t) ^ n) := by
          rw [charFun_countLawWeightedFixedCount_eq_series P N X hN_aemeas hX_indep hX_ident t]
    _ = probabilityGeneratingSeriesComplex (P.map N) (charFun (P.map (X 1)) t) := by
          rw [probabilityGeneratingSeriesComplex]

/-- Theorem 15.14 (3): item (iii). If the counting variable in part (ii) has Poisson law `Poi_λ`,
then the characteristic function of the random finite sum is `exp (λ (φ_X(t) - 1))`. -/
-- Proof sketch: use `hN.aemeasurable` to supply the measurability premise in
-- `charFun_randomFiniteSum_eq_complex_pgf`, then combine that theorem with the closed formula for
-- the Poisson probability generating series and rewrite `P.map N` using the `HasLaw` hypothesis.
theorem charFun_randomFiniteSum_eq_poisson_exponential {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : NNReal)
    (hN : HasLaw N (poissonMeasure lam) P)
    (hN_seq_indep : IndepFun N (fun ω n ↦ X (n + 1) ω) P)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (randomFiniteSum N X)) t =
      Complex.exp (((lam : ℝ) : ℂ) * (charFun (P.map (X 1)) t - (1 : ℂ))) := by
  -- Proof comment: substitute the Poisson law into the general random-sum identity and then use
  -- the closed formula for the complex Poisson pgf.
  rw [charFun_randomFiniteSum_eq_complex_pgf P N X hN.aemeasurable hN_seq_indep hX_indep hX_ident t,
    hN.map_eq]
  simpa using
    probabilityGeneratingSeriesComplex_poissonMeasure_eq_exp lam (charFun (P.map (X 1)) t)
