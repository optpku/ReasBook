/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

noncomputable section

/-!
Theorem 7.21 (Minimizer of Estimation Error for Tikhonov Regularization).

The source theorem gives two displayed asymptotic formulas: the parameter
asymptotics `(7.80)` and the expected estimation-error asymptotics `(7.81)`.
In Lean these are recorded as six regime-specific theorem skeletons using the
existing Chapter 7 owners for the expected estimation objective, admissible
parameter families, the critical benchmark sequence, and the nullspace/error
benchmark terms. The source-side noise/objective setup from the preceding
Chapter 7 analysis is retained through an explicit spectral decomposition
hypothesis for the expected estimation-error objective.
-/

namespace TikhonovEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (alphaE betaE : ℕ → ℝ)

variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_expectedObjective_decomposition :
  ∀ n α,
    expectedObjective μ K Rtikh fTrue η n α =
      tsum (fun i : ℕ+ ↦
        (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
          ((S n).generalizedFourierCoefficientSequence (h_length n)
            (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2) +
        nullspaceErrorFloor K fTrue n +
        σ ^ 2 * tsum (fun i : ℕ+ ↦
          SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
            ((S n).singularValueSequence (h_length n) i ^ 2)))
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierCoefficientSquareDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_vanishingNullspaceComponent :
  FilterRegularization.HasVanishingNullspaceComponent K fTrue)
variable (h_tikhonov : IsTikhonovReconstructionFamily K S Rtikh)

/-- Helper for Theorem 7.21: reindexing the Chapter 7 quadrature series from
`ℕ` to `ℕ+` matches the positive-mode singular-system indexing used in the
expected-objective decomposition. -/
lemma quadratureSeries_eq_tsum_pnat
    (p : ℝ) (j : ℕ) (s h : ℝ) :
    KernelMoment.quadratureSeries p j s h =
      ∑' i : ℕ+, h * KernelMoment.integrand p j s ((i : ℝ) * h) := by
  -- Rewrite the `ℕ`-indexed series through the canonical `ℕ+ ≃ ℕ`
  -- equivalence before matching it with the positive singular-mode indexing.
  rw [KernelMoment.quadratureSeries_def]
  symm
  simpa using
    (Equiv.pnatEquivNat.tsum_eq
      (fun k : ℕ ↦ h * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)))

/-- Helper for Theorem 7.21: the kernel moment `I_{p,3}^s` is strictly
positive under the Proposition 7.20 integrability inequalities. -/
lemma kernelMomentIntegralPos_j3
    {p s : ℝ}
    (h_p0 : 0 < p) (h_s : 0 < s + 1) (h_decay : 0 < 3 * p - s - 1) :
    0 < KernelMoment.integral p 3 s := by
  -- Rewrite the moment by the gamma-ratio formula and check positivity of each factor.
  rw [KernelMoment.integral_eq_gamma_mul_gamma_div_factorial
    h_s h_decay]
  refine div_pos ?_ ?_
  · refine mul_pos ?_ ?_
    · exact Real.Gamma_pos_of_pos (div_pos h_decay h_p0)
    · exact Real.Gamma_pos_of_pos (div_pos h_s h_p0)
  · positivity

/-- Helper for Theorem 7.21: the nonsaturated benchmark constant `C₁` from
`(7.80)` is positive in the nonsaturated regime. -/
lemma parameterConstantC1_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : 2 * p - q > -1) :
    0 < parameterConstantC1 b c p q := by
  -- Route correction: use the earlier gamma-ratio positivity owner from Prop. 7.20.
  have h_p0 : 0 < p := by
    linarith [h_p]
  have hIntegralMain : 0 < KernelMoment.integral p 3 (2 * p) := by
    -- The `s = 2 * p` kernel moment is integrable because `p > 1`.
    exact
      kernelMomentIntegralPos_j3 h_p0
        (by nlinarith [h_p]) (by nlinarith [h_p])
  have hIntegralTail : 0 < KernelMoment.integral p 3 (2 * p - q) := by
    -- The nonsaturated condition gives the source-side decay inequality at `s = 2 * p - q`.
    exact
      kernelMomentIntegralPos_j3 h_p0
        (by nlinarith [h_nonsaturated]) (by nlinarith [h_p, h_q])
  rw [parameterConstantC1_def]
  have hBasePos :
      0 <
        (c ^ (q / p) * KernelMoment.integral p 3 (2 * p)) /
          (b * KernelMoment.integral p 3 (2 * p - q)) := by
    -- The ratio inside the outer real power has positive numerator and denominator.
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos h_c (q / p)) hIntegralMain)
      (mul_pos h_b hIntegralTail)
  exact Real.rpow_pos_of_pos hBasePos (p / (p + q))

/-- Helper for Theorem 7.21: the saturated benchmark constant `C₂` from
`(7.80)` is positive once the source-condition norm term is positive. -/
lemma parameterConstantC2_pos
    {sourceNormSq : ℝ}
    (h_c : 0 < c) (h_p : 1 < p)
    (h_sourceNormSq_pos : 0 < sourceNormSq) :
    0 < parameterConstantC2 c p sourceNormSq := by
  have h_p0 : 0 < p := by
    linarith [h_p]
  have hIntegralMain : 0 < KernelMoment.integral p 3 (2 * p) := by
    -- The same `s = 2 * p` positivity input drives the saturated benchmark constant.
    exact
      kernelMomentIntegralPos_j3 h_p0
        (by nlinarith [h_p]) (by nlinarith [h_p])
  rw [parameterConstantC2_def]
  have hBasePos :
      0 < (c ^ (1 / p) * KernelMoment.integral p 3 (2 * p)) / sourceNormSq := by
    -- The source-condition norm term only appears as a positive denominator.
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos h_c (1 / p)) hIntegralMain)
      h_sourceNormSq_pos
  exact Real.rpow_pos_of_pos hBasePos (p / (3 * p + 1))

/-- Helper for Theorem 7.21: the nonsaturated benchmark is eventually positive,
so the ratio-to-one asymptotic-equivalence criterion applies. -/
lemma nonsaturatedBenchmark_eventuallyPos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : 2 * p - q > -1) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < nonsaturatedParameterBenchmark b c p q σ n := by
  have hC1_pos : 0 < parameterConstantC1 b c p q :=
    parameterConstantC1_pos (b := b) (c := c) (p := p) (q := q)
      h_b h_c h_p h_q h_nonsaturated
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hRatioPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSqPos : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSqPos hn_pos
  -- Expand the source benchmark and prove positivity factor by factor.
  rw [nonsaturatedParameterBenchmark_apply]
  exact mul_pos hC1_pos (Real.rpow_pos_of_pos hRatioPos (p / (p + q)))

/-- Helper for Theorem 7.21: on the nonsaturated benchmark scale
`α_n = t_n * nonsaturatedParameterBenchmark ... n`, the quadrature step
`h_n = (α_n / c) ^ (1 / p)` tends to `0+` and the product `(n : ℝ) * h_n`
still diverges to `+∞` whenever `t_n → τ > 0`. -/
lemma nonsaturatedScaledStep_tendsto
    {tN : ℕ → ℝ} {τ : ℝ}
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_tN : Filter.Tendsto tN Filter.atTop (nhds τ))
    (hτ : 0 < τ) (h_nonsaturated : 2 * p - q > -1) :
    let hN : ℕ → ℝ :=
      fun n ↦ (((tN n * nonsaturatedParameterBenchmark b c p q σ n) / c) ^ (1 / p));
    Filter.Tendsto hN Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ∧
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * hN n) Filter.atTop Filter.atTop := by
  let hN : ℕ → ℝ :=
    fun n ↦ (((tN n * nonsaturatedParameterBenchmark b c p q σ n) / c) ^ (1 / p))
  change
    Filter.Tendsto hN Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ∧
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * hN n) Filter.atTop Filter.atTop
  let γ : ℝ := 1 / (p + q)
  let δ : ℝ := (p + q - 1) / (p + q)
  have hp0 : 0 < p := by
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hpq_pos : 0 < p + q := by
    linarith
  have hpq_ne : p + q ≠ 0 := ne_of_gt hpq_pos
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    exact one_div_pos.mpr hpq_pos
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : 0 < p + q - 1 := by
      linarith
    exact div_pos this hpq_pos
  have hσsq_pos : 0 < σ ^ 2 := by
    nlinarith [sq_pos_of_pos h_σ]
  have hC1_pos : 0 < parameterConstantC1 b c p q :=
    parameterConstantC1_pos (b := b) (c := c) (p := p) (q := q)
      h_b h_c h_p h_q h_nonsaturated
  have h_tN_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < tN n := by
    exact h_tN.eventually (Ioi_mem_nhds hτ)
  have h_hN_eq :
      ∀ᶠ n : ℕ in Filter.atTop,
        hN n =
          (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
            (σ ^ 2) ^ γ * (n : ℝ) ^ (-γ) := by
    filter_upwards [h_tN_pos, Filter.Ici_mem_atTop 1] with n ht hn
    have hn_pos : 0 < (n : ℝ) := by
      exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hratio_pos : 0 < (σ ^ 2) / (n : ℝ) := by
      exact div_pos hσsq_pos hn_pos
    have hmain_pos :
        0 < (tN n * parameterConstantC1 b c p q) / c := by
      exact div_pos (mul_pos ht hC1_pos) h_c
    have hsplit :
        (tN n * (parameterConstantC1 b c p q *
            (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))))) / c =
          ((tN n * parameterConstantC1 b c p q) / c) *
            (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
      field_simp [h_c.ne']
    -- Rewrite the benchmark step into a positive scalar factor times the pure
    -- sample-size power `n ^ (-1 / (p + q))`.
    dsimp [hN]
    rw [hsplit]
    calc
      ((((tN n * parameterConstantC1 b c p q) / c) *
          (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))) ^ (1 / p))
          =
        (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          ((((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) ^ (1 / p)) := by
            rw [Real.mul_rpow hmain_pos.le (le_of_lt (Real.rpow_pos_of_pos hratio_pos _))]
      _ =
        (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          (((σ ^ 2) / (n : ℝ)) ^ γ) := by
            congr 1
            rw [← Real.rpow_mul hratio_pos.le (p / (p + q)) (1 / p)]
            congr 1
            dsimp [γ]
            field_simp [hp_ne, hpq_ne]
      _ =
        (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          ((σ ^ 2) ^ γ * (n : ℝ) ^ (-γ)) := by
            rw [Real.div_rpow hσsq_pos.le hn_pos.le]
            have hdiv :
                (σ ^ 2) ^ γ / (n : ℝ) ^ γ =
                  (σ ^ 2) ^ γ * (n : ℝ) ^ (-γ) := by
              rw [div_eq_mul_inv]
              rw [show ((n : ℝ) ^ γ)⁻¹ = (n : ℝ) ^ (-γ) by
                rw [← Real.rpow_neg hn_pos.le]]
            rw [hdiv]
      _ =
        (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          (σ ^ 2) ^ γ * (n : ℝ) ^ (-γ) := by
            ring
  have h_base_tendsto :
      Filter.Tendsto
        (fun n ↦ (tN n * parameterConstantC1 b c p q) / c)
        Filter.atTop
        (nhds ((τ * parameterConstantC1 b c p q) / c)) := by
    -- The benchmark prefactor has a finite positive limit because `tN → τ`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (h_tN.mul_const (parameterConstantC1 b c p q * c⁻¹))
  have h_base_pow_tendsto :
      Filter.Tendsto
        (fun n ↦ ((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p))
        Filter.atTop
        (nhds (((τ * parameterConstantC1 b c p q) / c) ^ (1 / p))) := by
    exact h_base_tendsto.rpow_const (Or.inr (by positivity : 0 ≤ 1 / p))
  have h_scale_tendsto :
      Filter.Tendsto
        (fun n ↦
          (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
            (σ ^ 2) ^ γ)
        Filter.atTop
        (nhds
          ((((τ * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
            (σ ^ 2) ^ γ)) := by
    -- The finite prefactor converges to a strictly positive constant.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Filter.Tendsto.const_mul ((σ ^ 2) ^ γ) h_base_pow_tendsto)
  have h_scale_pos :
      0 <
        (((τ * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          (σ ^ 2) ^ γ := by
    refine mul_pos ?_ ?_
    · exact Real.rpow_pos_of_pos (div_pos (mul_pos hτ hC1_pos) h_c) (1 / p)
    · exact Real.rpow_pos_of_pos hσsq_pos γ
  have h_pow_tendsto_zero :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-γ)) Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop hγ_pos).comp tendsto_natCast_atTop_atTop
  have h_hN_tendsto_zero :
      Filter.Tendsto hN Filter.atTop (nhds 0) := by
    have h_rhs :
        Filter.Tendsto
          (fun n ↦
            (((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
              (σ ^ 2) ^ γ * (n : ℝ) ^ (-γ))
          Filter.atTop (nhds 0) := by
      simpa using h_scale_tendsto.mul h_pow_tendsto_zero
    exact h_rhs.congr' (Filter.EventuallyEq.symm h_hN_eq)
  have h_hN_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < hN n := by
    filter_upwards [h_tN_pos, Filter.Ici_mem_atTop 1] with n ht hn
    have hn_pos : 0 < (n : ℝ) := by
      exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hratio_pos : 0 < (σ ^ 2) / (n : ℝ) := by
      exact div_pos hσsq_pos hn_pos
    have hbenchmark_pos : 0 < nonsaturatedParameterBenchmark b c p q σ n := by
      rw [nonsaturatedParameterBenchmark_apply]
      exact mul_pos hC1_pos (Real.rpow_pos_of_pos hratio_pos (p / (p + q)))
    -- The step remains on the positive branch because both `tN n` and the
    -- benchmark are eventually positive.
    dsimp [hN]
    exact Real.rpow_pos_of_pos (div_pos (mul_pos ht hbenchmark_pos) h_c) (1 / p)
  have h_hN_within :
      Filter.Tendsto hN Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨h_hN_tendsto_zero, h_hN_pos⟩
  have h_nmul_eq :
      ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) * hN n =
          ((((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
            (σ ^ 2) ^ γ) *
            (n : ℝ) ^ δ := by
    filter_upwards [h_hN_eq, Filter.Ici_mem_atTop 1] with n hn_eq hn
    have hn_pos : 0 < (n : ℝ) := by
      exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    -- Multiply the normalized step by `n` and collapse the remaining
    -- sample-size powers to the growing exponent `δ`.
    calc
      (n : ℝ) * hN n
          = (n : ℝ) *
              ((((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
                (σ ^ 2) ^ γ * (n : ℝ) ^ (-γ)) := by
              rw [hn_eq]
      _ =
        ((((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          (σ ^ 2) ^ γ) *
          ((n : ℝ) * (n : ℝ) ^ (-γ)) := by
            ring
      _ =
        ((((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
          (σ ^ 2) ^ γ) *
          (n : ℝ) ^ δ := by
            congr 1
            calc
              (n : ℝ) * (n : ℝ) ^ (-γ)
                  = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-γ) := by
                      rw [Real.rpow_one]
              _ = (n : ℝ) ^ (1 - γ) := by
                    have hexp : (1 : ℝ) + -γ = 1 - γ := by ring
                    rw [← Real.rpow_add hn_pos 1 (-γ), hexp]
              _ = (n : ℝ) ^ δ := by
                    have hδ_eq : 1 - γ = δ := by
                      dsimp [γ, δ]
                      field_simp [hpq_ne]
                    rw [hδ_eq]
  have h_pow_tendsto_atTop :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ δ) Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop hδ_pos).comp tendsto_natCast_atTop_atTop
  have h_nmul_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * hN n) Filter.atTop Filter.atTop := by
    have h_rhs :
        Filter.Tendsto
          (fun n ↦
            ((((tN n * parameterConstantC1 b c p q) / c) ^ (1 / p)) *
              (σ ^ 2) ^ γ) *
              (n : ℝ) ^ δ)
          Filter.atTop Filter.atTop := by
      exact h_scale_tendsto.pos_mul_atTop h_scale_pos h_pow_tendsto_atTop
    exact h_rhs.congr' (Filter.EventuallyEq.symm h_nmul_eq)
  exact ⟨h_hN_within, h_nmul_tendsto⟩

/-- Helper for Theorem 7.21: the saturated benchmark is eventually positive,
so the ratio-to-one asymptotic-equivalence criterion applies. -/
lemma saturatedBenchmark_eventuallyPos
    (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ)
    (h_sourceNormSq_pos :
      ∀ n, 0 < adjointCompSourceNormSq (S n) (h_length n) fTrue) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 <
        saturatedParameterBenchmark c p σ
          (adjointCompSourceNormSq (S n) (h_length n) fTrue) n := by
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hRatioPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSqPos : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSqPos hn_pos
  have hC2_pos :
      0 <
        parameterConstantC2 c p
          (adjointCompSourceNormSq (S n) (h_length n) fTrue) := by
    -- The pointwise source-condition norm is the only denominator in `C₂`.
    exact parameterConstantC2_pos (c := c) (p := p) h_c h_p (h_sourceNormSq_pos n)
  -- Expand the source benchmark and prove positivity factor by factor.
  rw [saturatedParameterBenchmark_apply]
  exact mul_pos hC2_pos (Real.rpow_pos_of_pos hRatioPos (p / (3 * p + 1)))

/-- Helper for Theorem 7.21: the right-hand side of the critical benchmark root
equation is positive at every positive data size. -/
lemma criticalRootRhs_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ)
    (n : ℕ+) : 0 < criticalRootRhs b c p σ n := by
  have h_p0 : 0 < p := by
    linarith [h_p]
  have hIntegralMain : 0 < KernelMoment.integral p 3 (2 * p) := by
    -- The critical root equation uses the same positive `j = 3`, `s = 2 * p` moment.
    exact
      kernelMomentIntegralPos_j3 h_p0
        (by nlinarith [h_p]) (by nlinarith [h_p])
  have hScalePos : 0 < (σ ^ 2) / (n : ℝ) := by
    exact div_pos (by nlinarith [sq_pos_of_pos h_σ]) (show 0 < (n : ℝ) by exact_mod_cast n.2)
  have hRestPos : 0 < b ^ (-1 : ℝ) * c ^ 2 * p * KernelMoment.integral p 3 (2 * p) := by
    have hLeftPos : 0 < b ^ (-1 : ℝ) * c ^ 2 := by
      exact mul_pos (Real.rpow_pos_of_pos h_b (-1 : ℝ)) (sq_pos_of_pos h_c)
    have hRightPos : 0 < p * KernelMoment.integral p 3 (2 * p) := by
      exact mul_pos h_p0 hIntegralMain
    simpa [mul_assoc] using mul_pos hLeftPos hRightPos
  -- Every factor in the explicit root-equation right-hand side is positive.
  unfold criticalRootRhs
  simpa [mul_assoc] using mul_pos hScalePos hRestPos

/-- Helper for Theorem 7.21: the critical logarithmic carrier at `t * β`
splits exactly into the scaled `β` carrier and the extra `log t` term. -/
lemma criticalProfile_scaleExact
    {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) :
    -((t * β) ^ ((3 * p + 1) / p) * Real.log (t * β)) =
      t ^ ((3 * p + 1) / p) * (-(β ^ ((3 * p + 1) / p) * Real.log β)) -
        t ^ ((3 * p + 1) / p) * β ^ ((3 * p + 1) / p) * Real.log t := by
  -- Expand the power and logarithm of the positive product before regrouping.
  rw [Real.mul_rpow ht.le hβ.le, Real.log_mul ht.ne' hβ.ne']
  ring

/-- Helper for Theorem 7.21: a balanced weighted power profile is bounded
below by its value at `t = 1`. -/
lemma weightedPowerProfile_ge
    {A B a b t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b)
    (h_balance : A * a = B * b) (ht : 0 < t) :
    A + B ≤ A * t ^ a + B * t ^ (-b) := by
  have hAB_pos : 0 < A + B := add_pos hA hB
  have hAB_ne : A + B ≠ 0 := ne_of_gt hAB_pos
  have hw :
      A / (A + B) + B / (A + B) = 1 := by
    field_simp [hAB_ne]
  have hgeom_one :
      (t ^ a) ^ (A / (A + B)) * (t ^ (-b)) ^ (B / (A + B)) = 1 := by
    rw [← Real.rpow_mul ht.le a (A / (A + B))]
    rw [← Real.rpow_mul ht.le (-b) (B / (A + B))]
    rw [← Real.rpow_add ht]
    have hexp :
        a * (A / (A + B)) + (-b) * (B / (A + B)) = 0 := by
      field_simp [hAB_ne]
      linarith
    rw [hexp, Real.rpow_zero]
  have hweighted :
      1 ≤
        (A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b) := by
    have hgm :
        (t ^ a) ^ (A / (A + B)) * (t ^ (-b)) ^ (B / (A + B)) ≤
          (A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b) :=
      Real.geom_mean_le_arith_mean2_weighted
        (show 0 ≤ A / (A + B) by positivity)
        (show 0 ≤ B / (A + B) by positivity)
        (show 0 ≤ t ^ a by positivity)
        (show 0 ≤ t ^ (-b) by positivity)
        hw
    calc
      1 = (t ^ a) ^ (A / (A + B)) * (t ^ (-b)) ^ (B / (A + B)) := by
            exact hgeom_one.symm
      _ ≤
          (A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b) := hgm
  -- Multiply the weighted-AM-GM lower bound by the common positive denominator.
  calc
    A + B = (A + B) * 1 := by ring
    _ ≤
        (A + B) *
          ((A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b)) :=
      mul_le_mul_of_nonneg_left hweighted hAB_pos.le
    _ = A * t ^ a + B * t ^ (-b) := by
      field_simp [hAB_ne]

/-- Helper for Theorem 7.21: the balanced weighted power profile attains its
minimum only at the unscaled point `t = 1`. -/
lemma weightedPowerProfile_eq_iff
    {A B a b t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b)
    (h_balance : A * a = B * b) (ht : 0 < t) :
    A * t ^ a + B * t ^ (-b) = A + B ↔ t = 1 := by
  have hAB_pos : 0 < A + B := add_pos hA hB
  have hAB_ne : A + B ≠ 0 := ne_of_gt hAB_pos
  have hw1 : 0 < A / (A + B) := div_pos hA hAB_pos
  have hw2 : 0 < B / (A + B) := div_pos hB hAB_pos
  have hw :
      A / (A + B) + B / (A + B) = 1 := by
    field_simp [hAB_ne]
  have hgeom_one :
      (t ^ a) ^ (A / (A + B)) * (t ^ (-b)) ^ (B / (A + B)) = 1 := by
    rw [← Real.rpow_mul ht.le a (A / (A + B))]
    rw [← Real.rpow_mul ht.le (-b) (B / (A + B))]
    rw [← Real.rpow_add ht]
    have hexp :
        a * (A / (A + B)) + (-b) * (B / (A + B)) = 0 := by
      field_simp [hAB_ne]
      linarith
    rw [hexp, Real.rpow_zero]
  have hab_ne : a + b ≠ 0 := by
    linarith
  constructor
  · intro h_eq
    -- Convert equality of the source profile to equality in weighted AM-GM.
    have hweighted_eq :
        (A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b) = 1 := by
      calc
        (A / (A + B)) * t ^ a + (B / (A + B)) * t ^ (-b)
            = (A * t ^ a + B * t ^ (-b)) / (A + B) := by
                field_simp [hAB_ne]
        _ = (A + B) / (A + B) := by rw [h_eq]
        _ = 1 := by field_simp [hAB_ne]
    have hpow_eq :
        t ^ a = t ^ (-b) := by
      refine
        (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
          hw1 hw2 (by positivity) (by positivity) hw).mp ?_
      rw [hgeom_one, hweighted_eq]
    have hpow_one :
        t ^ (a + b) = 1 := by
      calc
        t ^ (a + b) = t ^ a * t ^ b := by
          rw [← Real.rpow_add ht]
        _ = t ^ (-b) * t ^ b := by rw [hpow_eq]
        _ = t ^ (-b + b) := by rw [← Real.rpow_add ht]
        _ = 1 := by rw [neg_add_cancel, Real.rpow_zero]
    exact
      (Real.rpow_left_inj ht.le (show 0 ≤ (1 : ℝ) by positivity) hab_ne).mp
        (by simpa using hpow_one)
  · intro ht_eq
    -- Substituting `t = 1` collapses both powers in the profile.
    simp [ht_eq]

/-- Helper for Theorem 7.21: a pointwise optimal parameter family compares
below every admissible competitor at the same data size. -/
lemma optimalFamily_le_of_mem
    {τ : Type*}
    {objective : ℕ → τ → ℝ}
    {admissible : ℕ → Set τ}
    {α : ℕ → τ}
    (hα :
      ParameterChoice.IsOptimalParameterFamily
        objective admissible α)
    {n : ℕ} {x : τ}
    (hx : x ∈ admissible n) :
    objective n (α n) ≤ objective n x := by
  -- Unpack the owner definition to the pointwise `IsMinOn` comparison.
  have hmin_n : IsMinOn (objective n) (admissible n) (α n) :=
    (ParameterChoice.isOptimalParameterFamily_iff objective admissible α).1 hα n
  rw [isMinOn_iff] at hmin_n
  exact hmin_n x hx

/-- Helper for Theorem 7.21: removing the nullspace component does not change
the positive-mode generalized Fourier coefficients, because the right singular
vectors lie in `(K n).kerᗮ`. -/
lemma fourierCoeffSq_sub_nullspaceComponent_eq
    (n : ℕ) (i : ℕ+) :
    ((S n).generalizedFourierCoefficientSequence (h_length n)
      (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2 =
      ((S n).generalizedFourierCoefficientSequence (h_length n) fTrue i) ^ 2 := by
  let u : H := ((S n).rightBasis ((S n).natIndex (h_length n) i.natPred) : H)
  have hu_mem : u ∈ (K n).kerᗮ := by
    -- The right singular basis already lands in the orthogonal complement bundle.
    exact Submodule.coe_mem _
  have hnull_inner :
      inner ℝ u (FilterRegularization.nullspaceComponent (K n) fTrue) = 0 := by
    -- Rewrite the nullspace component through the orthogonal projection onto `(K n).kerᗮ`.
    rw [FilterRegularization.nullspaceComponent_eq_sub_orthogonalProjection, inner_eq_zero_symm]
    simpa [u] using
      (Submodule.starProjection_inner_eq_zero
        (K := (K n).kerᗮ) fTrue u hu_mem)
  have hcoeff :
      (S n).generalizedFourierCoefficientSequence (h_length n)
          (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i =
        (S n).generalizedFourierCoefficientSequence (h_length n) fTrue i := by
    -- Expand the coefficient once and eliminate the nullspace term by orthogonality.
    rw [ContinuousLinearMap.SingularSystem.generalizedFourierCoefficientSequence_apply,
      ContinuousLinearMap.SingularSystem.generalizedFourierCoefficientSequence_apply]
    change inner ℝ u (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) =
      inner ℝ u fTrue
    rw [inner_sub_right, hnull_inner, sub_zero]
  rw [hcoeff]

/-- Helper for Theorem 7.21: for positive reals, the Chapter 7 quotient power
splits into a numerator power and an inverse denominator power. -/
lemma div_rpow_eq_mul_rpow_neg
    {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x / y) ^ a = x ^ a * y ^ (-a) := by
  rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hx) (inv_nonneg.mpr hy.le), Real.inv_rpow hy.le]
  rw [show (y ^ a)⁻¹ = y ^ (-a) by rw [← Real.rpow_neg hy.le]]

/-- Helper for Theorem 7.21: the quadrature step `h = (α / c) ^ (1 / p)`
recovers the base ratio `α / c` after taking the `p`-th real power. -/
lemma rescaledStep_rpow_eq_ratio
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) :
    (((α / c) ^ (1 / p)) ^ p) = α / c := by
  have hp_ne : p ≠ 0 := by
    linarith [hp]
  have hαc_pos : 0 < α / c := by
    exact div_pos hα hc
  calc
    ((α / c) ^ (1 / p)) ^ p = (α / c) ^ ((1 / p) * p) := by
      rw [← Real.rpow_mul (le_of_lt hαc_pos)]
    _ = (α / c) ^ (1 : ℝ) := by
      congr 2
      field_simp [hp_ne]
    _ = α / c := by
      rw [Real.rpow_one]

/-- Helper for Theorem 7.21: after rescaling by `h = (α / c) ^ (1 / p)`, the
mode variable `(i * h)^p` matches the algebraic ratio `(i ^ p) * (α / c)`. -/
lemma rescaledMode_rpow_eq_ratio
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) = (i : ℝ) ^ p * (α / c) := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  -- Rewrite the rescaled mode power with `Real.mul_rpow`, then substitute the
  -- base ratio recovered by the `p`-th power of the step.
  calc
    (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)
        = (i : ℝ) ^ p * (((α / c) ^ (1 / p)) ^ p) := by
            rw [Real.mul_rpow hi_pos.le hstep_pos.le]
    _ = (i : ℝ) ^ p * (α / c) := by
          rw [rescaledStep_rpow_eq_ratio (c := c) (p := p) (α := α) hα hc hp]

/-- Helper for Theorem 7.21: the Tikhonov denominator `α + c i^{-p}` factors
through the rescaled mode variable `((i : ℝ) * (α / c) ^ (1 / p)) ^ p`. -/
lemma tikhonovDenominator_eq_rescaledMode
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    α + c * (i : ℝ) ^ (-p) =
      c * (i : ℝ) ^ (-p) *
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hi_cancel : (i : ℝ) ^ (-p) * (i : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add hi_pos, neg_add_cancel, Real.rpow_zero]
  have hscale_cancel : c * (α / c) = α := by
    field_simp [hc.ne']
  have hfirst :
      c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c)) = α := by
    calc
      c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c))
          = (c * (α / c)) * ((i : ℝ) ^ (-p) * (i : ℝ) ^ p) := by ring
      _ = α := by rw [hscale_cancel, hi_cancel, mul_one]
  -- First rewrite the `α` term through the same `i`-mode factor, then replace
  -- the mode power by the rescaled expression `((i : ℝ) * h)^p`.
  calc
    α + c * (i : ℝ) ^ (-p)
        = c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c)) +
            c * (i : ℝ) ^ (-p) := by
              rw [hfirst]
    _ = c * (i : ℝ) ^ (-p) * (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) +
          c * (i : ℝ) ^ (-p) := by
            rw [rescaledMode_rpow_eq_ratio (c := c) (p := p) (α := α) hα hc hp i]
    _ = c * (i : ℝ) ^ (-p) *
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) := by
            ring

/-- Helper for Theorem 7.21: after introducing the rescaled step
`h = (α / c) ^ (1 / p)`, the remaining coefficient in the variance summand
collapses to the stable factor `c⁻¹`. -/
lemma rescaledVarianceCoefficient_eq_inv
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) :
    c ^ (1 / p) * α ^ (-(p + 1) / p) * ((((α / c) ^ (1 / p))) ^ (p + 1)) =
      c ^ (-(1 : ℝ)) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hαc_pos : 0 < α / c := by
    exact div_pos hα hc
  have hmul : (1 / p) * (p + 1) = (p + 1) / p := by
    field_simp [hp_ne]
  have hdiv :
      (α / c) ^ ((p + 1) / p) = α ^ ((p + 1) / p) * c ^ (-((p + 1) / p)) := by
    -- Rewrite the quotient power into separate numerator and denominator powers.
    rw [div_eq_mul_inv, Real.mul_rpow hα.le (inv_nonneg.mpr hc.le), Real.inv_rpow hc.le]
    rw [show (c ^ ((p + 1) / p))⁻¹ = c ^ (-((p + 1) / p)) by
      rw [← Real.rpow_neg hc.le]]
  have hcexp : (1 / p) + -((p + 1) / p) = (-1 : ℝ) := by
    field_simp [hp_ne]
    ring
  have hαexp : (-(p + 1) / p) + (p + 1) / p = (0 : ℝ) := by
    ring
  -- First package the rescaled step as a single quotient power, then cancel the
  -- `α` and `c` exponents separately.
  calc
    c ^ (1 / p) * α ^ (-(p + 1) / p) * ((((α / c) ^ (1 / p))) ^ (p + 1))
        = c ^ (1 / p) * α ^ (-(p + 1) / p) * ((α / c) ^ ((p + 1) / p)) := by
            rw [← Real.rpow_mul (le_of_lt hαc_pos)]
            rw [hmul]
    _ = c ^ (1 / p) * α ^ (-(p + 1) / p) *
          (α ^ ((p + 1) / p) * c ^ (-((p + 1) / p))) := by
            rw [hdiv]
    _ = (c ^ (1 / p) * c ^ (-((p + 1) / p))) *
          (α ^ (-(p + 1) / p) * α ^ ((p + 1) / p)) := by
            ring
    _ = c ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hc (1 / p) (-((p + 1) / p))]
          rw [← Real.rpow_add hα (-(p + 1) / p) ((p + 1) / p)]
          rw [hcexp, hαexp, Real.rpow_neg_one, Real.rpow_zero, mul_one]

/-- Helper for Theorem 7.21: after factoring the Tikhonov denominator through
the rescaled mode `((i : ℝ) * (α / c) ^ (1 / p)) ^ p`, the variance summand
reduces to the stable spectral core `c⁻¹ * i^p / (1 + ((i h)^p))^2`. -/
lemma tikhonovVarianceDenominator_normalForm
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    (c * (i : ℝ) ^ (-p) / (α + c * (i : ℝ) ^ (-p))) ^ 2 / (c * (i : ℝ) ^ (-p)) =
      c ^ (-(1 : ℝ)) * (i : ℝ) ^ p /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
  let A : ℝ := c * (i : ℝ) ^ (-p)
  let B : ℝ := 1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hc (Real.rpow_pos_of_pos hi_pos (-p))
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  have hB_pos : 0 < B := by
    dsimp [B]
    have hmode_pos : 0 < (i : ℝ) * ((α / c) ^ (1 / p)) := by
      exact mul_pos hi_pos hstep_pos
    have hpow_pos :
        0 < (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) := by
          exact Real.rpow_pos_of_pos hmode_pos p
    linarith
  have hi_cancel : (i : ℝ) ^ (-p) * (i : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add hi_pos (-p) p, neg_add_cancel, Real.rpow_zero]
  have hAinv : A⁻¹ = c ^ (-(1 : ℝ)) * (i : ℝ) ^ p := by
    -- Convert the reciprocal of `c * i^{-p}` to the cheaper product `c⁻¹ * i^p`.
    dsimp [A]
    rw [Real.rpow_neg_one]
    field_simp [hc.ne', hi_pos.ne']
    exact hi_cancel.symm
  have hfrac :
      (c * (i : ℝ) ^ (-p) /
        (c * (i : ℝ) ^ (-p) * (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)))) =
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p))⁻¹ := by
    -- Cancel the common factor `c * i^{-p}` before squaring.
    field_simp [hA_pos.ne', hB_pos.ne']
  -- After the one-time denominator factorization, only the reciprocal of `A`
  -- remains, and that reciprocal is exactly the desired `c⁻¹ * i^p`.
  rw [tikhonovDenominator_eq_rescaledMode (c := c) (p := p) (α := α) hα hc hp i]
  rw [hfrac]
  calc
    ((1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p))⁻¹) ^ 2 / (c * (i : ℝ) ^ (-p))
        = (c * (i : ℝ) ^ (-p))⁻¹ /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
              field_simp [hA_pos.ne', hB_pos.ne']
    _ = c ^ (-(1 : ℝ)) * (i : ℝ) ^ p /
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
            rw [hAinv]

/-- Helper for Theorem 7.21: the Tikhonov variance summand rewrites exactly to
the `j = 2`, `s = p` kernel-moment integrand after the step rescaling
`h = (α / c) ^ (1 / p)`. -/
lemma tikhonovVarianceSummand_eq_quadratureIntegrand
    {n : ℕ} {α : ℝ}
    (hc : 0 < c) (hp : 1 < p)
    (h_singular : (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (hα : 0 < α) (i : ℕ+) :
    SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
        ((S n).singularValueSequence (h_length n) i ^ 2) =
      c ^ (1 / p) * α ^ (-(p + 1) / p) *
        (((α / c) ^ (1 / p)) *
          KernelMoment.integrand p 2 p ((i : ℝ) * ((α / c) ^ (1 / p)))) := by
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  have hstep_pow_succ :
      (((α / c) ^ (1 / p)) ^ (p + 1)) = ((α / c) ^ (1 / p)) * (α / c) := by
    -- Split the `(p + 1)`-power into the already normalized `p`-power and one
    -- extra factor of the rescaled step.
    calc
      (((α / c) ^ (1 / p)) ^ (p + 1))
          = (((α / c) ^ (1 / p)) ^ p) * (((α / c) ^ (1 / p)) ^ (1 : ℝ)) := by
              rw [Real.rpow_add hstep_pos p 1]
      _ = (α / c) * ((α / c) ^ (1 / p)) := by
            rw [rescaledStep_rpow_eq_ratio (c := c) (p := p) (α := α) hα hc hp, Real.rpow_one]
      _ = ((α / c) ^ (1 / p)) * (α / c) := by
            ring
  -- Route correction: pass through the denominator-normal-form lemma first,
  -- then repackage the remaining core as `h * KernelMoment.integrand`.
  calc
    SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
        ((S n).singularValueSequence (h_length n) i ^ 2)
        = (c * (i : ℝ) ^ (-p) / (α + c * (i : ℝ) ^ (-p))) ^ 2 /
            (c * (i : ℝ) ^ (-p)) := by
              rw [h_singular i, SpectralFilter.tikhonov]
    _ = c ^ (-(1 : ℝ)) * (i : ℝ) ^ p /
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
            exact tikhonovVarianceDenominator_normalForm (c := c) (p := p) (α := α) hα hc hp i
    _ = (c ^ (1 / p) * α ^ (-(p + 1) / p) * (((α / c) ^ (1 / p)) ^ (p + 1))) *
          ((i : ℝ) ^ p /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2) := by
              rw [rescaledVarianceCoefficient_eq_inv (c := c) (p := p) (α := α) hα hc hp]
              ring
    _ = c ^ (1 / p) * α ^ (-(p + 1) / p) *
          ((((α / c) ^ (1 / p)) ^ (p + 1)) *
            ((i : ℝ) ^ p /
              (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2)) := by
            ring
    _ = c ^ (1 / p) * α ^ (-(p + 1) / p) *
          (((α / c) ^ (1 / p)) *
            KernelMoment.integrand p 2 p ((i : ℝ) * ((α / c) ^ (1 / p)))) := by
              rw [KernelMoment.integrand_def]
              rw [rescaledMode_rpow_eq_ratio (c := c) (p := p) (α := α) hα hc hp i]
              rw [hstep_pow_succ]
              ring

/-- Helper for Theorem 7.21: after factoring the Tikhonov denominator through
the rescaled mode `((i : ℝ) * (α / c) ^ (1 / p)) ^ p`, the bias core reduces
to the stable spectral expression `α² c⁻² i^(2p-q) / (1 + ((i h)^p))²`. -/
lemma tikhonovBiasCore_normalForm
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    α ^ 2 * (i : ℝ) ^ (-q) / (α + c * (i : ℝ) ^ (-p)) ^ 2 =
      α ^ 2 * c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p - q) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
  let A : ℝ := c * (i : ℝ) ^ (-p)
  let B : ℝ := 1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hc (Real.rpow_pos_of_pos hi_pos (-p))
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  have hB_pos : 0 < B := by
    dsimp [B]
    have hmode_pos : 0 < (i : ℝ) * ((α / c) ^ (1 / p)) := by
      exact mul_pos hi_pos hstep_pos
    have hpow_pos :
        0 < (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) := by
          exact Real.rpow_pos_of_pos hmode_pos p
    linarith
  have hAinvSq :
      (((c * (i : ℝ) ^ (-p)) ^ (2 : ℕ)) : ℝ)⁻¹ =
        c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p) := by
    have hApow2 :
        (((c * (i : ℝ) ^ (-p)) ^ (2 : ℕ)) : ℝ) =
          (c * (i : ℝ) ^ (-p)) ^ (2 : ℝ) := by
      simpa [Real.rpow_natCast]
    have hpowi :
        ((i : ℝ) ^ (-p)) ^ (-(2 : ℝ)) = (i : ℝ) ^ (2 * p) := by
      calc
        ((i : ℝ) ^ (-p)) ^ (-(2 : ℝ)) = (i : ℝ) ^ ((-p) * (-(2 : ℝ))) := by
          rw [← Real.rpow_mul hi_pos.le (-p) (-(2 : ℝ))]
        _ = (i : ℝ) ^ (2 * p) := by
          congr 1
          ring
    -- Convert the reciprocal square of `c * i^{-p}` into separated `c` and `i`
    -- powers before recombining the `i`-exponents.
    calc
      (((c * (i : ℝ) ^ (-p)) ^ (2 : ℕ)) : ℝ)⁻¹
          = ((c * (i : ℝ) ^ (-p)) ^ (2 : ℝ))⁻¹ := by
              rw [hApow2]
      _ = (c * (i : ℝ) ^ (-p)) ^ (-(2 : ℝ)) := by
              simpa using (Real.rpow_neg hA_pos.le (2 : ℝ)).symm
      _ = c ^ (-(2 : ℝ)) * ((i : ℝ) ^ (-p)) ^ (-(2 : ℝ)) := by
            rw [Real.mul_rpow hc.le (Real.rpow_nonneg hi_pos.le (-p))]
      _ = c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p) := by
            rw [hpowi]
  have hi_exp :
      (i : ℝ) ^ (-q) * (i : ℝ) ^ (2 * p) = (i : ℝ) ^ (2 * p - q) := by
    rw [← Real.rpow_add hi_pos (-q) (2 * p)]
    congr 1
    ring
  -- Route correction: factor the denominator first, then collapse the
  -- remaining `c` and `i` powers in one algebraic step.
  rw [tikhonovDenominator_eq_rescaledMode (c := c) (p := p) (α := α) hα hc hp i, mul_pow]
  calc
    α ^ 2 * (i : ℝ) ^ (-q) /
        ((c * (i : ℝ) ^ (-p)) ^ 2 *
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2)
        =
      α ^ 2 * ((i : ℝ) ^ (-q) *
          (((c * (i : ℝ) ^ (-p)) ^ (2 : ℕ) : ℝ)⁻¹)) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          field_simp [hA_pos.ne', hB_pos.ne']
    _ =
      α ^ 2 * ((i : ℝ) ^ (-q) *
          (c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p))) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          rw [hAinvSq]
    _ =
      α ^ 2 * c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p - q) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          have hmix :
              (i : ℝ) ^ (-q) * (c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p)) =
                c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p - q) := by
            calc
              (i : ℝ) ^ (-q) * (c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p))
                  = c ^ (-(2 : ℝ)) * ((i : ℝ) ^ (-q) * (i : ℝ) ^ (2 * p)) := by
                      ring
              _ = c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p - q) := by
                    rw [hi_exp]
          rw [hmix]
          ring

/-- Helper for Theorem 7.21: after rescaling by `h = (α / c) ^ (1 / p)`, the
bias coefficient collapses to the stable factor `α² c⁻²`. -/
lemma rescaledBiasCoefficient_eq_sqInv
    {α : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) :
    c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        ((((α / c) ^ (1 / p))) ^ (2 * p - q + 1)) =
      α ^ 2 * c ^ (-(2 : ℝ)) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hαc_pos : 0 < α / c := by
    exact div_pos hα hc
  have hmul : (1 / p) * (2 * p - q + 1) = (2 * p - q + 1) / p := by
    field_simp [hp_ne]
  have hdiv :
      (α / c) ^ ((2 * p - q + 1) / p) =
        α ^ ((2 * p - q + 1) / p) * c ^ (-((2 * p - q + 1) / p)) := by
    -- Rewrite the quotient power into separate numerator and denominator powers.
    rw [div_eq_mul_inv, Real.mul_rpow hα.le (inv_nonneg.mpr hc.le), Real.inv_rpow hc.le]
    rw [show (c ^ ((2 * p - q + 1) / p))⁻¹ = c ^ (-((2 * p - q + 1) / p)) by
      rw [← Real.rpow_neg hc.le]]
  have hαexp :
      ((q - 1) / p) + (2 * p - q + 1) / p = (2 : ℝ) := by
    field_simp [hp_ne]
    ring
  have hcexp :
      (-(q - 1) / p) + -((2 * p - q + 1) / p) = (-2 : ℝ) := by
    field_simp [hp_ne]
    ring
  -- Package the rescaled step as one quotient power, then cancel the `α` and
  -- `c` exponents separately.
  calc
    c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        ((((α / c) ^ (1 / p))) ^ (2 * p - q + 1))
        =
      c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        ((α / c) ^ ((2 * p - q + 1) / p)) := by
          rw [← Real.rpow_mul (le_of_lt hαc_pos)]
          rw [hmul]
    _ =
      c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        (α ^ ((2 * p - q + 1) / p) * c ^ (-((2 * p - q + 1) / p))) := by
          rw [hdiv]
    _ =
      (c ^ (-(q - 1) / p) * c ^ (-((2 * p - q + 1) / p))) *
        (α ^ ((q - 1) / p) * α ^ ((2 * p - q + 1) / p)) := by
          ring
    _ = α ^ 2 * c ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add hc (-(q - 1) / p) (-((2 * p - q + 1) / p))]
          rw [← Real.rpow_add hα ((q - 1) / p) ((2 * p - q + 1) / p)]
          rw [hcexp, hαexp]
          simpa [Real.rpow_natCast] using mul_comm (c ^ (-(2 : ℝ))) (α ^ (2 : ℝ))

/-- Helper for Theorem 7.21: the Tikhonov bias summand rewrites exactly to the
`j = 2`, `s = 2p - q` kernel-moment integrand after the step rescaling
`h = (α / c) ^ (1 / p)`. -/
lemma tikhonovBiasSummand_eq_quadratureIntegrand
    {n : ℕ} {α : ℝ}
    (hc : 0 < c) (hp : 1 < p)
    (h_singular : (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourier : (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (hα : 0 < α) (i : ℕ+) :
    (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
        ((S n).generalizedFourierCoefficientSequence (h_length n)
          (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2 =
      b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        (((α / c) ^ (1 / p)) *
          KernelMoment.integrand p 2 (2 * p - q) ((i : ℝ) * ((α / c) ^ (1 / p)))) := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  have hfilter :
      1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) =
        α / (α + c * (i : ℝ) ^ (-p)) := by
    -- Rewrite the Tikhonov complement through the algebraic singular-value law.
    rw [h_singular i, SpectralFilter.tikhonov]
    field_simp [hα.ne', hc.ne', hi_pos.ne']
    ring
  have hstep_core :
      (((α / c) ^ (1 / p)) ^ (2 * p - q + 1)) *
          ((i : ℝ) ^ (2 * p - q) /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2) =
        ((α / c) ^ (1 / p)) *
          ((((i : ℝ) * ((α / c) ^ (1 / p))) ^ (2 * p - q)) /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2) := by
    have hmode_split :
        (((i : ℝ) * ((α / c) ^ (1 / p))) ^ (2 * p - q)) =
          (i : ℝ) ^ (2 * p - q) * (((α / c) ^ (1 / p)) ^ (2 * p - q)) := by
      rw [Real.mul_rpow hi_pos.le hstep_pos.le]
    have hstep_pow_succ :
        (((α / c) ^ (1 / p)) ^ (2 * p - q + 1)) =
          ((α / c) ^ (1 / p)) * (((α / c) ^ (1 / p)) ^ (2 * p - q)) := by
      calc
        (((α / c) ^ (1 / p)) ^ (2 * p - q + 1))
            = (((α / c) ^ (1 / p)) ^ (2 * p - q)) *
                (((α / c) ^ (1 / p)) ^ (1 : ℝ)) := by
                  rw [Real.rpow_add hstep_pos (2 * p - q) 1]
        _ = (((α / c) ^ (1 / p)) ^ (2 * p - q)) * ((α / c) ^ (1 / p)) := by
              rw [Real.rpow_one]
        _ = ((α / c) ^ (1 / p)) * (((α / c) ^ (1 / p)) ^ (2 * p - q)) := by
              ring
    -- Split `((i h)^(2p-q))` into its `i` and `h` factors once, then absorb
    -- the extra copy of `h` into the outside multiplier.
    calc
      (((α / c) ^ (1 / p)) ^ (2 * p - q + 1)) *
          ((i : ℝ) ^ (2 * p - q) /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2)
          =
        ((α / c) ^ (1 / p)) *
          ((((α / c) ^ (1 / p)) ^ (2 * p - q)) *
            ((i : ℝ) ^ (2 * p - q) /
              (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2)) := by
              rw [hstep_pow_succ]
              ring
      _ =
        ((α / c) ^ (1 / p)) *
          ((((i : ℝ) * ((α / c) ^ (1 / p))) ^ (2 * p - q)) /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2) := by
              rw [hmode_split]
              ring
  -- Route correction: normalize the filter complement and decay laws first,
  -- land in the stable bias core, and only then package the result as
  -- `h * KernelMoment.integrand`.
  calc
    (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
        ((S n).generalizedFourierCoefficientSequence (h_length n)
          (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2
        =
      (α / (α + c * (i : ℝ) ^ (-p))) ^ 2 * (b * (i : ℝ) ^ (-q)) := by
          rw [hfilter, fourierCoeffSq_sub_nullspaceComponent_eq
            (K := K) (S := S) (h_length := h_length) (fTrue := fTrue) n i, h_fourier i]
    _ = b * (α ^ 2 * (i : ℝ) ^ (-q) / (α + c * (i : ℝ) ^ (-p)) ^ 2) := by
          field_simp [hα.ne', hc.ne', hi_pos.ne']
    _ =
      b *
        (α ^ 2 * c ^ (-(2 : ℝ)) * (i : ℝ) ^ (2 * p - q) /
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2) := by
            rw [tikhonovBiasCore_normalForm (c := c) (p := p) (q := q) (α := α) hα hc hp i]
    _ =
      b *
        ((c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
            ((((α / c) ^ (1 / p))) ^ (2 * p - q + 1))) *
          ((i : ℝ) ^ (2 * p - q) /
            (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2)) := by
              rw [rescaledBiasCoefficient_eq_sqInv (c := c) (p := p) (q := q) (α := α) hα hc hp]
              ring
    _ =
      b *
        (c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          ((((α / c) ^ (1 / p)) ^ (2 * p - q + 1)) *
            ((i : ℝ) ^ (2 * p - q) /
              (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2))) := by
            ring
    _ =
      b *
        (c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          (((α / c) ^ (1 / p)) *
            ((((i : ℝ) * ((α / c) ^ (1 / p))) ^ (2 * p - q)) /
              (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2))) := by
            rw [hstep_core]
    _ =
      b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
        (((α / c) ^ (1 / p)) *
          KernelMoment.integrand p 2 (2 * p - q) ((i : ℝ) * ((α / c) ^ (1 / p)))) := by
            rw [KernelMoment.integrand_def]
            ring

/-- Helper for Theorem 7.21: the Tikhonov bias summand can also be rewritten
exactly through the source-series owner `adjointCompSourceSeries`, which is the
right interface for the saturated branch. -/
lemma tikhonovBiasSummand_eq_sourceSeriesWeight
    {n : ℕ} {α : ℝ}
    (hc : 0 < c) (hp : 1 < p)
    (h_singular : (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (hα : 0 < α) (i : ℕ+) :
    (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
        ((S n).generalizedFourierCoefficientSequence (h_length n)
          (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2 =
      α ^ 2 * adjointCompSourceSeries (S n) (h_length n) fTrue i /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  have hfilter :
      1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) =
        α / (α + c * (i : ℝ) ^ (-p)) := by
    -- Rewrite the Tikhonov complement through the algebraic singular-value law.
    rw [h_singular i, SpectralFilter.tikhonov]
    field_simp [hα.ne', hc.ne', hi_pos.ne']
    ring
  have hden_pos : 0 < 1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) := by
    have hmode_pos : 0 < (i : ℝ) * ((α / c) ^ (1 / p)) := by
      exact mul_pos hi_pos hstep_pos
    have hpow_pos : 0 < (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) := by
      exact Real.rpow_pos_of_pos hmode_pos p
    linarith
  have hsv_pow_four :
      (S n).singularValueSequence (h_length n) i ^ 4 =
        (c * (i : ℝ) ^ (-p)) ^ (2 : ℕ) := by
    -- Square the singular-value decay law one more time to match the source series.
    calc
      (S n).singularValueSequence (h_length n) i ^ 4 =
          ((S n).singularValueSequence (h_length n) i ^ 2) ^ (2 : ℕ) := by
            ring_nf
      _ = (c * (i : ℝ) ^ (-p)) ^ (2 : ℕ) := by
            rw [h_singular i]
  -- Route correction: rewrite the filter complement and denominator first,
  -- then identify the remaining coefficient quotient with `adjointCompSourceSeries`.
  calc
    (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
        ((S n).generalizedFourierCoefficientSequence (h_length n)
          (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2
        =
      (α / (α + c * (i : ℝ) ^ (-p))) ^ 2 *
        ((S n).generalizedFourierCoefficientSequence (h_length n) fTrue i) ^ 2 := by
          rw [hfilter,
            fourierCoeffSq_sub_nullspaceComponent_eq
              (K := K) (S := S) (h_length := h_length) (fTrue := fTrue) n i]
    _ =
      α ^ 2 *
        (((S n).generalizedFourierCoefficientSequence (h_length n) fTrue i) ^ 2 /
          (c * (i : ℝ) ^ (-p)) ^ (2 : ℕ)) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          rw [tikhonovDenominator_eq_rescaledMode (c := c) (p := p) (α := α) hα hc hp i]
          field_simp [hα.ne', hc.ne', hi_pos.ne', hden_pos.ne']
    _ =
      α ^ 2 *
        (((S n).generalizedFourierCoefficientSequence (h_length n) fTrue i) ^ 2 /
          ((S n).singularValueSequence (h_length n) i ^ 4)) /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          rw [hsv_pow_four]
    _ =
      α ^ 2 * adjointCompSourceSeries (S n) (h_length n) fTrue i /
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) ^ 2 := by
          rw [adjointCompSourceSeries_apply]

/-- Helper for Theorem 7.21: positivity of the source-condition norm series
forces actual summability of the defining `K* K`-weighted coefficients. -/
lemma adjointCompSourceSeries_summable_of_normSq_pos
    {n : ℕ}
    (h_norm_pos : 0 < adjointCompSourceNormSq (S n) (h_length n) fTrue) :
    Summable (adjointCompSourceSeries (S n) (h_length n) fTrue) := by
  by_contra h_not_summable
  have h_norm_zero :
      adjointCompSourceNormSq (S n) (h_length n) fTrue = 0 := by
    rw [adjointCompSourceNormSq_def]
    exact tsum_eq_zero_of_not_summable h_not_summable
  -- A positive series sum cannot coincide with the nonsummable fallback value `0`.
  linarith

/-- Helper for Theorem 7.21: the Chapter 7 expected estimation objective has an
exact quadrature-profile decomposition once the Tikhonov bias and variance
terms are rewritten through `h = (α / c) ^ (1 / p)`. -/
lemma expectedObjective_eq_estimationQuadratureProfile
    {n : ℕ} {α : ℝ}
    (hc : 0 < c) (hp : 1 < p) (hα : 0 < α)
    (h_decomposition :
      expectedObjective μ K Rtikh fTrue η n α =
        tsum (fun i : ℕ+ ↦
          (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
            ((S n).generalizedFourierCoefficientSequence (h_length n)
              (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2) +
          nullspaceErrorFloor K fTrue n +
          σ ^ 2 * tsum (fun i : ℕ+ ↦
            SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
              ((S n).singularValueSequence (h_length n) i ^ 2)))
    (h_singular : (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourier : (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q) :
    expectedObjective μ K Rtikh fTrue η n α =
      nullspaceErrorFloor K fTrue n +
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          KernelMoment.quadratureSeries p 2 (2 * p - q) ((α / c) ^ (1 / p)) +
        σ ^ 2 * c ^ (1 / p) * α ^ (-(p + 1) / p) *
          KernelMoment.quadratureSeries p 2 p ((α / c) ^ (1 / p)) := by
  let h : ℝ := (α / c) ^ (1 / p)
  have hbias :
      (∑' i : ℕ+,
        (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
          ((S n).generalizedFourierCoefficientSequence (h_length n)
            (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2) =
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          KernelMoment.quadratureSeries p 2 (2 * p - q) h := by
    -- Rewrite the bias series pointwise to the kernel-moment integrand and
    -- only then factor the constant through `tsum`.
    calc
      (∑' i : ℕ+,
        (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
          ((S n).generalizedFourierCoefficientSequence (h_length n)
            (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2)
          =
        ∑' i : ℕ+, b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          (h * KernelMoment.integrand p 2 (2 * p - q) ((i : ℝ) * h)) := by
            refine tsum_congr ?_
            intro i
            simpa [h] using
              tikhonovBiasSummand_eq_quadratureIntegrand
                (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
                (b := b) (c := c) (p := p) (q := q)
                (hc := hc) (hp := hp)
                (h_singular := h_singular)
                (h_fourier := h_fourier)
                (hα := hα) (i := i)
      _ =
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          (∑' i : ℕ+, h * KernelMoment.integrand p 2 (2 * p - q) ((i : ℝ) * h)) := by
            rw [tsum_mul_left]
      _ =
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          KernelMoment.quadratureSeries p 2 (2 * p - q) h := by
            rw [quadratureSeries_eq_tsum_pnat]
  have hvariance :
      (∑' i : ℕ+,
        SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
          ((S n).singularValueSequence (h_length n) i ^ 2)) =
        c ^ (1 / p) * α ^ (-(p + 1) / p) *
          KernelMoment.quadratureSeries p 2 p h := by
    -- The variance-side bridge is already isolated above; assemble it by the
    -- same `tsum_congr` then `quadratureSeries` route.
    calc
      (∑' i : ℕ+,
        SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
          ((S n).singularValueSequence (h_length n) i ^ 2))
          =
        ∑' i : ℕ+, c ^ (1 / p) * α ^ (-(p + 1) / p) *
          (h * KernelMoment.integrand p 2 p ((i : ℝ) * h)) := by
            refine tsum_congr ?_
            intro i
            simpa [h] using
              tikhonovVarianceSummand_eq_quadratureIntegrand
                (S := S) (h_length := h_length) (c := c) (p := p)
                (hc := hc) (hp := hp)
                (h_singular := h_singular)
                (hα := hα) (i := i)
      _ =
        c ^ (1 / p) * α ^ (-(p + 1) / p) *
          (∑' i : ℕ+, h * KernelMoment.integrand p 2 p ((i : ℝ) * h)) := by
            rw [tsum_mul_left]
      _ =
        c ^ (1 / p) * α ^ (-(p + 1) / p) *
          KernelMoment.quadratureSeries p 2 p h := by
            rw [quadratureSeries_eq_tsum_pnat]
  -- Route correction: rewrite the decomposition's bias and variance series
  -- separately, then put the three terms back in the source-facing order.
  calc
    expectedObjective μ K Rtikh fTrue η n α
        =
      (∑' i : ℕ+,
        (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
          ((S n).generalizedFourierCoefficientSequence (h_length n)
            (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2) +
        nullspaceErrorFloor K fTrue n +
        σ ^ 2 *
          (∑' i : ℕ+,
            SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
              ((S n).singularValueSequence (h_length n) i ^ 2)) := by
            simpa using h_decomposition
    _ =
      nullspaceErrorFloor K fTrue n +
        (∑' i : ℕ+,
        (1 - SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2)) ^ 2 *
          ((S n).generalizedFourierCoefficientSequence (h_length n)
              (fTrue - FilterRegularization.nullspaceComponent (K n) fTrue) i) ^ 2) +
        σ ^ 2 *
          (∑' i : ℕ+,
            SpectralFilter.tikhonov α ((S n).singularValueSequence (h_length n) i ^ 2) ^ 2 /
              ((S n).singularValueSequence (h_length n) i ^ 2)) := by
            ring
    _ =
      nullspaceErrorFloor K fTrue n +
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          KernelMoment.quadratureSeries p 2 (2 * p - q) h +
        σ ^ 2 *
          (c ^ (1 / p) * α ^ (-(p + 1) / p) *
            KernelMoment.quadratureSeries p 2 p h) := by
            rw [hbias, hvariance]
    _ =
      nullspaceErrorFloor K fTrue n +
        b * c ^ (-(q - 1) / p) * α ^ ((q - 1) / p) *
          KernelMoment.quadratureSeries p 2 (2 * p - q) ((α / c) ^ (1 / p)) +
        σ ^ 2 * c ^ (1 / p) * α ^ (-(p + 1) / p) *
          KernelMoment.quadratureSeries p 2 p ((α / c) ^ (1 / p)) := by
            simp [h, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 7.21: once a positive benchmark `β` has a uniform
off-neighborhood objective gap, any optimal family has ratio `alphaE / β`
tending to `1`. -/
lemma ratioTendstoOne_of_optimality_gap
    {β : ℕ → ℝ}
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_beta_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < β n)
    (h_gap :
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 →
            expectedObjective μ K Rtikh fTrue η n (β n) <
              expectedObjective μ K Rtikh fTrue η n (t * β n)) :
    Filter.Tendsto (fun n ↦ alphaE n / β n) Filter.atTop (nhds 1) := by
  let tN : ℕ → ℝ := fun n ↦ alphaE n / β n
  have h_alphaE_le_beta :
      ∀ᶠ n : ℕ in Filter.atTop,
        expectedObjective μ K Rtikh fTrue η n (alphaE n) ≤
          expectedObjective μ K Rtikh fTrue η n (β n) := by
    filter_upwards [h_beta_pos] with n hn_beta
    -- Compare the optimal family against the positive benchmark, which lies in `α ≥ 0`.
    exact
      optimalFamily_le_of_mem
        (hα := h_alphaE) (n := n) (x := β n) (by simpa using le_of_lt hn_beta)
  -- Route correction: the branch-specific work is now isolated in the
  -- eventual strict gap `h_gap`; the metric convergence is generic.
  refine Metric.tendsto_nhds.2 ?_
  intro ε h_ε
  let δ : ℝ := min ε (1 / 2 : ℝ)
  have h_δ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min h_ε (by norm_num)
  have h_δ_lt_one : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  filter_upwards [h_beta_pos, h_alphaE_le_beta, h_gap δ h_δ_pos h_δ_lt_one] with
    n hn_beta hn_le hn_gap
  have h_tN_nonneg : 0 ≤ tN n := by
    -- Both the minimizing family and the benchmark stay in the admissible half-line.
    dsimp [tN]
    exact div_nonneg (by simpa using h_alphaE_admissible n) hn_beta.le
  have h_alphaE_eq : alphaE n = tN n * β n := by
    -- Rewrite the minimizing parameter on the benchmark scale.
    dsimp [tN]
    field_simp [ne_of_gt hn_beta]
  have h_not_far : ¬ δ ≤ dist (tN n) 1 := by
    intro h_far
    have h_gap' :
        expectedObjective μ K Rtikh fTrue η n (β n) <
          expectedObjective μ K Rtikh fTrue η n (tN n * β n) :=
      hn_gap (tN n) h_tN_nonneg h_far
    have h_le' :
        expectedObjective μ K Rtikh fTrue η n (tN n * β n) ≤
          expectedObjective μ K Rtikh fTrue η n (β n) := by
      simpa [h_alphaE_eq] using hn_le
    linarith
  have h_dist_lt_δ : dist (tN n) 1 < δ :=
    lt_of_not_ge h_not_far
  have h_δ_le_ε : δ ≤ ε := by
    dsimp [δ]
    exact min_le_left _ _
  exact lt_of_lt_of_le h_dist_lt_δ h_δ_le_ε

/-- Helper for Theorem 7.21: the generic ratio-to-one bridge packages the
eventual gap argument into `Asymptotics.IsEquivalent`. -/
lemma isEquivalent_of_optimality_gap
    {β : ℕ → ℝ}
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_beta_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < β n)
    (h_gap :
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 →
            expectedObjective μ K Rtikh fTrue η n (β n) <
              expectedObjective μ K Rtikh fTrue η n (t * β n)) :
    Asymptotics.IsEquivalent Filter.atTop alphaE β := by
  have h_beta_ne : ∀ᶠ n : ℕ in Filter.atTop, β n ≠ 0 :=
    h_beta_pos.mono fun _ hn ↦ ne_of_gt hn
  -- Reuse the benchmark-gap criterion to control the normalized ratio directly.
  exact
    (Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne).2
      (ratioTendstoOne_of_optimality_gap
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaE := alphaE)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_beta_pos := h_beta_pos)
        (h_gap := h_gap))

/-- Helper for Theorem 7.21: package an asymptotic equivalence as the owner
wrapper `ParameterChoice.IsAsymptoticallyOptimal`. -/
lemma isAsymptoticallyOptimal_of_isEquivalent_local
    {α αopt : ℕ → ℝ}
    (h : Asymptotics.IsEquivalent Filter.atTop α αopt) :
    ParameterChoice.IsAsymptoticallyOptimal α αopt := by
  -- TODO: this `module` file cannot access the non-`module` bridge import, and
  -- the exposed equation theorem for `IsAsymptoticallyOptimal` is not usable
  -- here. Restore the canonical owner bridge once the wrapper is exported to a
  -- `module`-safe dependency.
  let _ := h
  sorry

/-- The regime-split parameter asymptotics from Theorem 7.21 `(7.80)`. -/
def OptimalFamilyParameterAsymptotics : Prop :=
  (2 * p - q > -1 →
    ParameterChoice.IsAsymptoticallyOptimal alphaE
      (nonsaturatedParameterBenchmark b c p q σ)) ∧
    (2 * p - q = -1 →
      ParameterChoice.IsAsymptoticallyOptimal alphaE betaE) ∧
    (2 * p - q < -1 →
      ParameterChoice.IsAsymptoticallyOptimal alphaE
        (fun n ↦
          saturatedParameterBenchmark c p σ
            (adjointCompSourceNormSq (S n) (h_length n) fTrue) n))

/-- The regime-split expected-error asymptotics from Theorem 7.21 `(7.81)`. -/
def OptimalFamilyExpectedErrorAsymptotics : Prop :=
  (2 * p - q > -1 →
    Asymptotics.IsEquivalent Filter.atTop
      (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
      (fun n ↦
        nullspaceErrorFloor K fTrue n +
          nonsaturatedErrorBenchmark b c p q σ n)) ∧
    (2 * p - q = -1 →
      Asymptotics.IsEquivalent Filter.atTop
        (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
        (fun n ↦
          nullspaceErrorFloor K fTrue n +
            criticalErrorBenchmark c p betaE n)) ∧
    (2 * p - q < -1 →
      Asymptotics.IsEquivalent Filter.atTop
        (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
        (fun n ↦
          nullspaceErrorFloor K fTrue n +
            saturatedErrorBenchmark p σ n))

/-- Theorem 7.21 `(7.80)`, nonsaturated branch. In the regime `2 * p - q > -1`,
any Chapter 7 Tikhonov estimation-error minimizing family `alphaE` is
asymptotically equivalent to the explicit nonsaturated benchmark sequence. -/
-- TODO: Rewrite `expectedObjective` into the quadrature-profile normal form,
-- normalize at `α = t * nonsaturatedParameterBenchmark ... n`, and use the
-- positive-`s` quadrature asymptotics to show the limiting scalar profile is
-- uniquely minimized at `t = 1`.
theorem optimalFamily_nonsaturated_isAsymptoticallyOptimal
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_nonsaturated : 2 * p - q > -1) :
    ParameterChoice.IsAsymptoticallyOptimal alphaE
      (nonsaturatedParameterBenchmark b c p q σ) := by
  have h_beta_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < nonsaturatedParameterBenchmark b c p q σ n :=
    by
      -- TODO: this branch needs the standing positivity hypotheses
      -- `h_b`, `h_c`, `h_p`, `h_q`, `h_σ`, but they are not present in the
      -- theorem-local context, so the benchmark positivity lemma cannot be
      -- instantiated here.
      sorry
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop alphaE
        (nonsaturatedParameterBenchmark b c p q σ) := by
    -- Route correction: once positivity and the fixed-scale gap are available,
    -- the generic equivalence bridge closes the branch after one gap estimate.
    exact
      isEquivalent_of_optimality_gap
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaE := alphaE)
        (β := nonsaturatedParameterBenchmark b c p q σ)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_beta_pos := h_beta_pos) (by
          intro ε h_ε h_ε_lt_one
          -- TODO: rewrite `expectedObjective` at `α = t * α_ns n`, use the exact
          -- quadrature profile and the Proposition 7.19 asymptotics in the regime
          -- `2 * p - q > -1`, and show the limiting carrier is strictly larger than
          -- its value at `t = 1` whenever `ε ≤ dist t 1`.
          sorry)
  -- The remaining branch-specific content is exactly the off-neighborhood gap.
  exact isAsymptoticallyOptimal_of_isEquivalent_local h_equiv

/-- Theorem 7.21 `(7.80)`, critical branch. In the regime `2 * p - q = -1`,
any Chapter 7 Tikhonov estimation-error minimizing family `alphaE` is
asymptotically equivalent to the benchmark sequence `betaE` satisfying the
displayed critical root equation and converging to `0`, which selects the
source-side small-root branch `β_e`. -/
-- TODO: Normalize the objective along `α = t * betaE n`, combine the
-- logarithmic quadrature asymptotics with the critical root equation, and
-- show the normalized limiting bracket has unique minimizer `t = 1`.
theorem optimalFamily_critical_isAsymptoticallyOptimal
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_critical : 2 * p - q = -1)
    (h_betaE : IsCriticalBenchmark b c p σ betaE)
    (h_betaE_pos : ∀ n, 0 < betaE n)
    (h_betaE_tendsto_zero : Filter.Tendsto betaE Filter.atTop (nhds 0)) :
    ParameterChoice.IsAsymptoticallyOptimal alphaE betaE := by
  have h_beta_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < betaE n :=
    Filter.Eventually.of_forall h_betaE_pos
  have h_equiv : Asymptotics.IsEquivalent Filter.atTop alphaE betaE := by
    -- Route correction: the generic ratio lemma leaves only the critical
    -- fixed-scale gap as the real analytic content.
    exact
      isEquivalent_of_optimality_gap
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaE := alphaE) (β := betaE)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_beta_pos := h_beta_pos) (by
          intro ε h_ε h_ε_lt_one
          -- TODO: normalize `expectedObjective` on the `betaE` scale, combine the
          -- critical root equation with the logarithmic quadrature asymptotic, and
          -- show the resulting scalar carrier has its unique minimum at `t = 1`.
          let _ := h_betaE_tendsto_zero
          let _ := h_betaE
          sorry)
  -- The remaining branch-specific content is exactly the critical gap estimate.
  exact isAsymptoticallyOptimal_of_isEquivalent_local h_equiv

/-- Theorem 7.21 `(7.80)`, saturated branch. In the regime `2 * p - q < -1`,
any Chapter 7 Tikhonov estimation-error minimizing family `alphaE` is
asymptotically equivalent to the saturated benchmark built from the pointwise
source term `‖f_true‖_{K_n^* K_n}^2`. -/
-- TODO: After the exact quadrature rewrite, compare the objective at
-- `α = t * saturatedParameterBenchmark ... n`; the source-condition term and
-- variance term are dominant, while the `q`-dependent bias is lower order in
-- the saturated regime.
theorem optimalFamily_saturated_isAsymptoticallyOptimal
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_saturated : 2 * p - q < -1)
    (h_sourceNormSq_pos :
      ∀ n, 0 < adjointCompSourceNormSq (S n) (h_length n) fTrue) :
    ParameterChoice.IsAsymptoticallyOptimal alphaE
      (fun n ↦
        saturatedParameterBenchmark c p σ
          (adjointCompSourceNormSq (S n) (h_length n) fTrue) n) := by
  have h_beta_pos :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 <
          saturatedParameterBenchmark c p σ
            (adjointCompSourceNormSq (S n) (h_length n) fTrue) n :=
    by
      -- TODO: this branch needs the standing positivity hypotheses
      -- `h_c`, `h_p`, `h_σ`, but they are not present in the theorem-local
      -- context, so the benchmark positivity lemma cannot be instantiated here.
      sorry
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop alphaE
        (fun n ↦
          saturatedParameterBenchmark c p σ
            (adjointCompSourceNormSq (S n) (h_length n) fTrue) n) := by
    -- Route correction: after the positivity step, the generic ratio bridge
    -- leaves only the saturated fixed-scale gap to prove.
    exact
      isEquivalent_of_optimality_gap
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaE := alphaE)
        (β := fun n ↦
          saturatedParameterBenchmark c p σ
            (adjointCompSourceNormSq (S n) (h_length n) fTrue) n)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_beta_pos := h_beta_pos) (by
          intro ε h_ε h_ε_lt_one
          -- TODO: isolate the dominant `adjointCompSourceNormSq * α^2` bias term and
          -- the variance asymptotic on the saturated benchmark scale, then show the
          -- normalized carrier is strictly larger away from `t = 1`.
          let _ := h_saturated
          sorry)
  -- The remaining branch-specific content is exactly the saturated gap estimate.
  exact isAsymptoticallyOptimal_of_isEquivalent_local h_equiv

/-- Theorem 7.21 `(7.81)`, nonsaturated branch. In the regime `2 * p - q > -1`,
the expected estimation error evaluated along an optimal family `alphaE` is
asymptotically equivalent to the nullspace floor plus the explicit
nonsaturated benchmark term. -/
-- TODO: Combine the nonsaturated parameter asymptotic with the exact
-- quadrature-profile rewrite of `expectedObjective`, then identify the leading
-- `j = 2` bias/variance bracket with `nonsaturatedErrorBenchmark`.
theorem expectedObjectiveAlongOptimalFamily_nonsaturated_isEquivalent
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_nonsaturated : 2 * p - q > -1) :
    Asymptotics.IsEquivalent Filter.atTop
      (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
      (fun n ↦
        nullspaceErrorFloor K fTrue n +
          nonsaturatedErrorBenchmark b c p q σ n) := by
  have h_alpha_equiv :
      ParameterChoice.IsAsymptoticallyOptimal alphaE
        (nonsaturatedParameterBenchmark b c p q σ) :=
    optimalFamily_nonsaturated_isAsymptoticallyOptimal
      (b := b) (c := c) (σ := σ)
      (h_alphaE := h_alphaE)
      (h_alphaE_admissible := h_alphaE_admissible)
      (h_nonsaturated := h_nonsaturated)
  -- Route correction: the parameter asymptotic is now available as the only input from `(7.80)`.
  -- TODO: combine `h_alpha_equiv` with the exact objective quadrature profile and identify
  -- the leading normalized bias-variance bracket as `nonsaturatedErrorBenchmark`.
  sorry

/-- Theorem 7.21 `(7.81)`, critical branch. In the regime `2 * p - q = -1`,
the expected estimation error evaluated along an optimal family `alphaE` is
asymptotically equivalent to the nullspace floor plus the critical benchmark
term defined by the positive sequence `betaE`, with `betaE → 0` selecting the
source-side small-root branch. -/
-- TODO: Use the critical parameter asymptotic and the logarithmic
-- `j = 2` quadrature expansion to rewrite `objectiveAlong` into the nullspace
-- floor plus the critical benchmark profile.
theorem expectedObjectiveAlongOptimalFamily_critical_isEquivalent
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_critical : 2 * p - q = -1)
    (h_betaE : IsCriticalBenchmark b c p σ betaE)
    (h_betaE_pos : ∀ n, 0 < betaE n)
    (h_betaE_tendsto_zero : Filter.Tendsto betaE Filter.atTop (nhds 0)) :
    Asymptotics.IsEquivalent Filter.atTop
      (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
      (fun n ↦
        nullspaceErrorFloor K fTrue n +
          criticalErrorBenchmark c p betaE n) := by
  have h_alpha_equiv :
      ParameterChoice.IsAsymptoticallyOptimal alphaE betaE :=
    optimalFamily_critical_isAsymptoticallyOptimal
      (h_alphaE := h_alphaE)
      (h_alphaE_admissible := h_alphaE_admissible)
      (h_critical := h_critical)
      (h_betaE := h_betaE)
      (h_betaE_pos := h_betaE_pos)
      (h_betaE_tendsto_zero := h_betaE_tendsto_zero)
  -- Route correction: the critical parameter comparison is factored out; the remaining gap is
  -- the logarithmic expected-objective normalization on the `betaE` scale.
  -- TODO: rewrite `objectiveAlong` with the exact profile and transport along `h_alpha_equiv`.
  sorry

/-- Theorem 7.21 `(7.81)`, saturated branch. In the regime `2 * p - q < -1`,
the expected estimation error evaluated along an optimal family `alphaE` is
asymptotically equivalent to the nullspace floor plus the explicit saturated
benchmark term. -/
-- TODO: Use the saturated parameter asymptotic together with the exact
-- objective decomposition to isolate the dominant variance/source-condition
-- contribution and match it with `saturatedErrorBenchmark`.
theorem expectedObjectiveAlongOptimalFamily_saturated_isEquivalent
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_saturated : 2 * p - q < -1)
    (h_sourceNormSq_pos :
      ∀ n, 0 < adjointCompSourceNormSq (S n) (h_length n) fTrue) :
    Asymptotics.IsEquivalent Filter.atTop
      (objectiveAlong (expectedObjective μ K Rtikh fTrue η) alphaE)
      (fun n ↦
        nullspaceErrorFloor K fTrue n +
          saturatedErrorBenchmark p σ n) := by
  -- Route correction: unlike the `(7.80)` saturated parameter theorem, the `(7.81)` saturated
  -- expected-error statement does not retain the benchmark parameter family itself. The remaining
  -- proof therefore has to work directly from the exact objective decomposition and isolate the
  -- dominant source-condition/variance terms without reintroducing the hidden `c`-dependent scale.
  -- TODO: rewrite `objectiveAlong` via the exact profile and identify the saturated leading term
  -- directly at the objective level.
  sorry

/-- thm_7_21. Theorem 7.21 `(7.80)` and `(7.81)`. Main labeled source-facing
entry.

The source theorem is recorded as the pair of regime-split asymptotic clauses
`OptimalFamilyParameterAsymptotics` and `OptimalFamilyExpectedErrorAsymptotics`.
The critical benchmark sequence `betaE` keeps the displayed root equation and
the source-side positive branch, and additionally tends to `0` so that it
selects the small-root branch intended by `β_e`. The six theorem skeletons
above expose the corresponding atomic regime-specific components for later
proof stages and downstream reuse. -/
theorem optimalFamilyParameterAndExpectedErrorAsymptotics
    (h_alphaE :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K Rtikh fTrue η)
        admissibleParameters
        alphaE)
    -- `IsMinOn` only stores the comparison inequality on the admissible set,
    -- so the source-side `arg min_{α ≥ 0}` also requires explicit admissibility.
    (h_alphaE_admissible : ∀ n, alphaE n ∈ admissibleParameters n)
    (h_betaE : IsCriticalBenchmark b c p σ betaE)
    (h_betaE_pos : ∀ n, 0 < betaE n)
    (h_betaE_tendsto_zero : Filter.Tendsto betaE Filter.atTop (nhds 0))
    (h_sourceNormSq_pos :
      ∀ n, 0 < adjointCompSourceNormSq (S n) (h_length n) fTrue) :
    OptimalFamilyParameterAsymptotics
      K S h_length fTrue b c p q σ alphaE betaE ∧
      OptimalFamilyExpectedErrorAsymptotics
        μ K fTrue b c p q σ η Rtikh alphaE betaE := by
  -- Package the six regime-specific branches without reopening the asymptotic analysis here.
  constructor
  · constructor
    · intro h_nonsaturated
      exact optimalFamily_nonsaturated_isAsymptoticallyOptimal
        (b := b) (c := c) (σ := σ)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_nonsaturated := h_nonsaturated)
    · constructor
      · intro h_critical
        exact optimalFamily_critical_isAsymptoticallyOptimal
          (h_alphaE := h_alphaE)
          (h_alphaE_admissible := h_alphaE_admissible)
          (h_critical := h_critical)
          (h_betaE := h_betaE)
          (h_betaE_pos := h_betaE_pos)
          (h_betaE_tendsto_zero := h_betaE_tendsto_zero)
      · intro h_saturated
        exact optimalFamily_saturated_isAsymptoticallyOptimal
          (c := c) (σ := σ)
          (h_alphaE := h_alphaE)
          (h_alphaE_admissible := h_alphaE_admissible)
          (h_saturated := h_saturated)
          (h_sourceNormSq_pos := h_sourceNormSq_pos)
  · constructor
    · intro h_nonsaturated
      exact expectedObjectiveAlongOptimalFamily_nonsaturated_isEquivalent
        (b := b) (c := c) (σ := σ)
        (h_alphaE := h_alphaE)
        (h_alphaE_admissible := h_alphaE_admissible)
        (h_nonsaturated := h_nonsaturated)
    · constructor
      · intro h_critical
        exact expectedObjectiveAlongOptimalFamily_critical_isEquivalent
          (h_alphaE := h_alphaE)
          (h_alphaE_admissible := h_alphaE_admissible)
          (h_critical := h_critical)
          (h_betaE := h_betaE)
          (h_betaE_pos := h_betaE_pos)
          (h_betaE_tendsto_zero := h_betaE_tendsto_zero)
      · intro h_saturated
        exact expectedObjectiveAlongOptimalFamily_saturated_isEquivalent
          (σ := σ)
          (h_alphaE := h_alphaE)
          (h_alphaE_admissible := h_alphaE_admissible)
          (h_saturated := h_saturated)
          (h_sourceNormSq_pos := h_sourceNormSq_pos)

end

end TikhonovEstimation
