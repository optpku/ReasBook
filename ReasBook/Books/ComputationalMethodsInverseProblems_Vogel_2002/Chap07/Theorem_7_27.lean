/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Benchmark
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Profile
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

public section

/-!
Theorem 7.27 (Regularization Parameter Choice for the Discrepancy Principle
Applied to Tikhonov Regularization).

This source theorem is recorded as three regime-specific source-facing theorem
skeletons over `Asymptotics.IsEquivalent Filter.atTop`. The discrepancy-side
benchmark layer lives in `Book.Ch7.Theorem_7_27.Benchmark`, which exposes the
critical root equation, the large-index critical benchmark owner, the
nonsaturated and saturated parameter benchmarks, the `‖f_true‖_{K*}^2`
source scalar, and the explicit owner that packages the pointwise discrepancy
equation `(7.90)` into a parameter family.
-/

noncomputable section

namespace TikhonovDiscrepancy

universe u v w

section

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (d η : ℕ → F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (alphaDiscrep : ℕ → ℝ)
variable (normKStarSq : ℝ)

omit [CompleteSpace H] [CompleteSpace F] in
/-- Helper for Theorem 7.27: unpack the pointwise discrepancy-parameter family
owner at a positive index. -/
lemma discrepancyParameterFamily_spec
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (n : ℕ+) :
    0 ≤ alphaDiscrep n ∧
      IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
  -- The family owner is definitionally the conjunction of nonnegativity and
  -- the pointwise discrepancy equation.
  simpa [IsTikhonovDiscrepancyParameterFamily] using h_alphaDiscrep n

/-- Helper for Theorem 7.27: a fixed scalar `normKStarSq` really is the
source-condition term when the source-condition owner is available. -/
lemma sourceConditionNormSq_spec
    (h_sourceConditionNormSq :
      HasSourceConditionNormSq S h_length fTrue normKStarSq)
    (n : ℕ) :
    sourceConditionNormSq (S n) (h_length n) fTrue = normKStarSq := by
  -- The source-condition owner is definitionally pointwise.
  simpa [HasSourceConditionNormSq] using h_sourceConditionNormSq n

/-- Helper for Theorem 7.27: each exact-signal left singular coefficient
`⟪u_i, K n fTrue⟫` is the singular value times the matching generalized
Fourier coefficient of `fTrue`. -/
lemma signalModeCoefficient_eq
    (n : ℕ) (i : ℕ+) :
    inner ℝ ((S n).leftBasis ((S n).positiveIndex (h_length n) i) : F) ((K n) fTrue) =
      (S n).singularValueSequence (h_length n) i *
        (S n).generalizedFourierCoefficientSequence (h_length n) fTrue i := by
  let j : (S n).Index := (S n).positiveIndex (h_length n) i
  -- Move `K n` across the inner product and then apply the singular-system
  -- left/right basis identities at the chosen mode.
  calc
    inner ℝ ((S n).leftBasis j : F) ((K n) fTrue)
        = inner ℝ ((K n).adjoint ((S n).leftBasis j : F)) fTrue := by
            rw [← ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℝ ((S n).singularValue j • ((S n).rightBasis j : H)) fTrue := by
          simpa using congrArg (fun x : H ↦ inner ℝ x fTrue) ((S n).adjoint_map_left j)
    _ = (S n).singularValue j * inner ℝ ((S n).rightBasis j : H) fTrue := by
          rw [real_inner_smul_left]
    _ = (S n).singularValueSequence (h_length n) i *
          (S n).generalizedFourierCoefficientSequence (h_length n) fTrue i := by
          simp [ContinuousLinearMap.SingularSystem.singularValueSequence,
            ContinuousLinearMap.SingularSystem.generalizedFourierCoefficientSequence, j]

/-- Helper for Theorem 7.27: the actual datum `d n` expands through the
Tikhonov filter series of `Rtikh n α`, which is the starting point for any
mode-by-mode discrepancy rewrite. -/
lemma tikhonovApplyData_hasSum
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (n : ℕ) (α : ℝ) :
    HasSum
      ((S n).filterSeries (SpectralFilter.tikhonov α) (d n))
      (Rtikh n α (d n)) := by
  -- Evaluate the reconstruction-family owner at the concrete datum `d n`.
  exact (h_tikhonov n α).hasSum (d n)

/-- Helper for Theorem 7.27: after expanding the semistochastic data model, the
datum coefficient in one left singular mode splits into the exact-signal term
controlled by `fTrue` and the unresolved noise coefficient from `η n`. -/
lemma dataModeCoefficient_eq_signal_add_noise
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (n : ℕ) (i : ℕ+) :
    inner ℝ ((S n).leftBasis ((S n).positiveIndex (h_length n) i) : F) (d n) =
      (S n).singularValueSequence (h_length n) i *
        (S n).generalizedFourierCoefficientSequence (h_length n) fTrue i +
      inner ℝ ((S n).leftBasis ((S n).positiveIndex (h_length n) i) : F) (η n) := by
  -- Rewrite `d n` as `K n fTrue + η n`, then isolate the exact-signal mode and
  -- leave the noise coefficient explicit.
  rw [h_standing.semistochasticDataModel n, inner_add_right]
  rw [signalModeCoefficient_eq
    (K := K) (S := S) (h_length := h_length) (fTrue := fTrue) n i]

/-- Helper for Theorem 7.27: the kernel moment `KernelMoment.integral p 2 s`
is strictly positive under the Proposition 7.20 admissibility inequalities. -/
lemma kernelMomentIntegralPos_j2
    {p s : ℝ}
    (h_p : 0 < p) (h_s : 0 < s + 1) (h_decay : 0 < 2 * p - s - 1) :
    0 < KernelMoment.integral p 2 s := by
  -- Rewrite the moment by the gamma-ratio formula and check each factor is positive.
  rw [KernelMoment.integral_eq_gamma_mul_gamma_div_factorial
    (p := p) (s := s) (j := 2) h_s h_decay]
  refine div_pos ?_ ?_
  · refine mul_pos ?_ ?_
    · exact Real.Gamma_pos_of_pos (div_pos h_decay h_p)
    · exact Real.Gamma_pos_of_pos (div_pos h_s h_p)
  · positivity

/-- Helper for Theorem 7.27: the nonsaturated discrepancy benchmark constant
`C₁^discrep` is positive in the regime `p - q > -1`. -/
lemma parameterConstant1_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : p - q > -1) :
    0 < parameterConstant1 b c p q := by
  have h_p0 : 0 < p := by
    linarith
  have hIntegralMain : 0 < KernelMoment.integral p 2 p := by
    -- The `s = p` moment is integrable because `p > 1`.
    exact kernelMomentIntegralPos_j2 h_p0 (by linarith) (by linarith)
  have hIntegralZero : 0 < KernelMoment.integral p 2 0 := by
    -- The `s = 0` moment uses the same decay inequality `2 * p - 1 > 0`.
    exact kernelMomentIntegralPos_j2 h_p0 (by norm_num) (by linarith)
  have hIntegralTail : 0 < KernelMoment.integral p 2 (p - q) := by
    -- The nonsaturated regime supplies the lower-end integrability inequality.
    exact kernelMomentIntegralPos_j2 h_p0 (by linarith) (by linarith)
  rw [parameterConstant1_def]
  have hMomentSumPos :
      0 < 2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0 := by
    nlinarith
  have hBasePos :
      0 <
        ((2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) /
            KernelMoment.integral p 2 (p - q)) *
          (c ^ (q / p) / b) := by
    refine mul_pos ?_ ?_
    · exact div_pos hMomentSumPos hIntegralTail
    · exact div_pos (Real.rpow_pos_of_pos h_c (q / p)) h_b
  -- Positive bases stay positive under the outer real power.
  exact Real.rpow_pos_of_pos hBasePos (p / (p + q))

/-- Helper for Theorem 7.27: the saturated discrepancy benchmark constant
`C₂^discrep` is positive once the source scalar `‖f_true‖_{K*}^2` is positive.
-/
lemma parameterConstant2_pos
    (h_c : 0 < c) (h_p : 1 < p) (h_normKStarSq_pos : 0 < normKStarSq) :
    0 < parameterConstant2 c p normKStarSq := by
  have h_p0 : 0 < p := by
    linarith
  have hIntegralMain : 0 < KernelMoment.integral p 2 p := by
    -- The `s = p` moment is positive exactly as in the nonsaturated constant.
    exact kernelMomentIntegralPos_j2 h_p0 (by linarith) (by linarith)
  have hIntegralZero : 0 < KernelMoment.integral p 2 0 := by
    -- The zero-order moment contributes the second positive summand.
    exact kernelMomentIntegralPos_j2 h_p0 (by norm_num) (by linarith)
  rw [parameterConstant2_def]
  have hMomentSumPos :
      0 < 2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0 := by
    nlinarith
  have hBasePos :
      0 <
        (c ^ (1 / p) * (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)) /
          normKStarSq := by
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos h_c (1 / p)) hMomentSumPos)
      h_normKStarSq_pos
  -- The saturated benchmark is again a positive real power of a positive base.
  exact Real.rpow_pos_of_pos hBasePos (p / (2 * p + 1))

/-- Helper for Theorem 7.27: the explicit nonsaturated benchmark is eventually
positive, so the ratio-to-`1` asymptotic-equivalence bridge applies. -/
lemma nonsaturatedParameterBenchmark_eventually_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < nonsaturatedParameterBenchmark b c p q σ n := by
  have hC1_pos : 0 < parameterConstant1 b c p q :=
    parameterConstant1_pos b c p q h_b h_c h_p h_q h_nonsaturated
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hRatioPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSqPos : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSqPos hn_pos
  -- Expand the benchmark and prove positivity factor by factor.
  rw [nonsaturatedParameterBenchmark_def]
  exact mul_pos hC1_pos (Real.rpow_pos_of_pos hRatioPos (p / (p + q)))

/-- Helper for Theorem 7.27: the explicit saturated benchmark is eventually
positive, so the ratio-to-`1` asymptotic-equivalence bridge applies. -/
lemma saturatedParameterBenchmark_eventually_pos
    (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ)
    (h_normKStarSq_pos : 0 < normKStarSq) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < saturatedParameterBenchmark c p σ normKStarSq n := by
  have hC2_pos : 0 < parameterConstant2 c p normKStarSq :=
    parameterConstant2_pos c p normKStarSq h_c h_p h_normKStarSq_pos
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hRatioPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSqPos : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSqPos hn_pos
  -- Expand the benchmark and prove positivity factor by factor.
  rw [saturatedParameterBenchmark_def]
  exact mul_pos hC2_pos (Real.rpow_pos_of_pos hRatioPos (p / (2 * p + 1)))

omit [CompleteSpace H] [CompleteSpace F] in
/-- Helper for Theorem 7.27: a discrepancy-principle parameter family is
eventually nonnegative on the nat-indexed tail. -/
lemma discrepancyParameterFamily_eventually_nonneg
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ alphaDiscrep n := by
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  -- Convert the eventual nat-index tail to the positive-index owner exported by
  -- `IsTikhonovDiscrepancyParameterFamily`.
  exact
    (discrepancyParameterFamily_spec K σ d Rtikh alphaDiscrep h_alphaDiscrep
      ⟨n, lt_of_lt_of_le Nat.zero_lt_one hn⟩).1

/-- Helper for Theorem 7.27: the critical logarithmic profile written in the
same source shape as the discrepancy-side root equation. -/
private def criticalDiscrepancyProfile (p β : ℝ) : ℝ :=
  -(β ^ ((2 * p + 1) / p) * Real.log β)

/-- Helper for Theorem 7.27: unfold the theorem-local critical discrepancy
profile to the displayed logarithmic expression. -/
@[simp] private theorem criticalDiscrepancyProfile_def (p β : ℝ) :
    criticalDiscrepancyProfile p β =
      -(β ^ ((2 * p + 1) / p) * Real.log β) :=
  rfl

/-- Helper for Theorem 7.27: rescaling the critical discrepancy profile by a
fixed positive factor produces one exact logarithmic correction term. -/
private theorem criticalDiscrepancyProfileScaleExact
    {p t β : ℝ} (ht : 0 < t) (hβ : 0 < β) :
    criticalDiscrepancyProfile p (t * β) =
      t ^ ((2 * p + 1) / p) * criticalDiscrepancyProfile p β -
        t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t := by
  -- Expand the scaled logarithm once and factor the shared powered benchmark
  -- term before regrouping the two contributions.
  calc
    criticalDiscrepancyProfile p (t * β)
        = -((t * β) ^ ((2 * p + 1) / p) * Real.log (t * β)) := by
            rw [criticalDiscrepancyProfile]
    _ = -((t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p)) *
          (Real.log t + Real.log β)) := by
            rw [Real.mul_rpow (le_of_lt ht) (le_of_lt hβ), Real.log_mul ht.ne' hβ.ne']
    _ = -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t) +
          -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log β) := by
            ring
    _ = -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t) +
          t ^ ((2 * p + 1) / p) * criticalDiscrepancyProfile p β := by
            rw [criticalDiscrepancyProfile]
            ring
    _ = t ^ ((2 * p + 1) / p) * criticalDiscrepancyProfile p β -
          t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t := by
            ring

/-- Helper for Theorem 7.27: beyond a finite prefix, the canonical benchmark
`β_discrep` lies on the small branch and satisfies the theorem-local critical
profile equation. -/
private theorem betaDiscrepEventuallySmallBranchAndProfile
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < betaDiscrep b c p σ n ∧
        betaDiscrep b c p σ n ≤ Real.exp (-(p / (2 * p + 1))) ∧
        criticalDiscrepancyProfile p (betaDiscrep b c p σ n) =
          ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
            (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
  rcases betaDiscrep_spec_largeIndex b c p σ h_b h_c h_p h_σ with ⟨N, hN⟩
  filter_upwards [Filter.Ici_mem_atTop (max N 1)] with n hn
  have hN_bound : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right N 1) hn)
  rcases hN ⟨n, hn_pos⟩ hN_bound with ⟨hbeta_pos, hbeta_upper, hbeta_root⟩
  refine ⟨hbeta_pos, hbeta_upper, ?_⟩
  -- Re-express the public root equation using the theorem-local profile name
  -- so the critical branch can consume one stable interface.
  simpa [criticalDiscrepancyProfile, BetaDiscrepRootEquation] using hbeta_root

/-- Helper for Theorem 7.27: once the actual ratio makes a normalized scalar
balance vanish and every fixed off-neighborhood has the sign of `t - 1`, the
ratio `alphaDiscrep / β` tends to `1`. -/
lemma ratioTendstoOne_of_eventualSignGap
    {β : ℕ → ℝ} {B : ℕ → ℝ → ℝ}
    (h_alpha_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ alphaDiscrep n)
    (h_beta_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < β n)
    (h_balance_zero :
      ∀ᶠ n : ℕ in Filter.atTop, B n (alphaDiscrep n / β n) = 0)
    (h_sign_gap :
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 → 0 < (t - 1) * B n t) :
    Filter.Tendsto (fun n ↦ alphaDiscrep n / β n) Filter.atTop (nhds 1) := by
  let tN : ℕ → ℝ := fun n ↦ alphaDiscrep n / β n
  -- Route correction: after the branch-specific balance is normalized, the
  -- remaining argument is the same metric contradiction in every regime.
  refine Metric.tendsto_nhds.2 ?_
  intro ε h_ε
  let δ : ℝ := min ε (1 / 2 : ℝ)
  have h_δ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min h_ε (by norm_num)
  have h_δ_lt_one : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  filter_upwards
    [h_alpha_nonneg, h_beta_pos, h_balance_zero, h_sign_gap δ h_δ_pos h_δ_lt_one] with
    n h_alpha_nonneg_n h_beta_pos_n h_balance_zero_n h_sign_gap_n
  have h_tN_nonneg : 0 ≤ tN n := by
    -- The normalized ratio stays in the nonnegative half-line because both the
    -- discrepancy parameter and the benchmark do.
    dsimp [tN]
    exact div_nonneg h_alpha_nonneg_n h_beta_pos_n.le
  have h_not_far : ¬ δ ≤ dist (tN n) 1 := by
    intro h_far
    have h_strict :
        0 < (tN n - 1) * B n (tN n) :=
      h_sign_gap_n (tN n) h_tN_nonneg h_far
    -- The actual ratio is a zero of the normalized balance, contradicting the
    -- strict sign gap away from `t = 1`.
    simp [tN, h_balance_zero_n] at h_strict
  have h_dist_lt_δ : dist (tN n) 1 < δ := by
    exact lt_of_not_ge h_not_far
  have h_δ_le_ε : δ ≤ ε := by
    dsimp [δ]
    exact min_le_left _ _
  exact lt_of_lt_of_le h_dist_lt_δ h_δ_le_ε

/-- Theorem 7.27 (1). In the regime `p - q > -1`, a Chapter 7 Tikhonov
discrepancy-principle parameter family is asymptotically equivalent to the
explicit nonsaturated benchmark sequence from Theorem 7.27. The source setup
is retained through the standing-assumption bundle, the Tikhonov
reconstruction family, and the source-owned discrepancy-equation owner for
`(7.90)`. -/
theorem isEquivalent_nonsaturated
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1) :
    Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
      (nonsaturatedParameterBenchmark b c p q σ) := by
  -- First isolate the pointwise discrepancy equation carried by the family
  -- owner; the remaining work is the shared quadrature-profile normalization.
  have h_alphaSpec :
      ∀ n : ℕ+, 0 ≤ alphaDiscrep n ∧
        IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
    intro n
    exact discrepancyParameterFamily_spec K σ d Rtikh alphaDiscrep h_alphaDiscrep n
  have h_benchmark_ne :
      ∀ᶠ n : ℕ in Filter.atTop,
        nonsaturatedParameterBenchmark b c p q σ n ≠ 0 :=
    (nonsaturatedParameterBenchmark_eventually_pos b c p q σ
      h_b h_c h_p h_q h_σ h_nonsaturated).mono
      (fun _ hn ↦ ne_of_gt hn)
  have h_alpha_nonneg :
      ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ alphaDiscrep n :=
    discrepancyParameterFamily_eventually_nonneg K σ d Rtikh alphaDiscrep h_alphaDiscrep
  have h_benchmark_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < nonsaturatedParameterBenchmark b c p q σ n :=
    nonsaturatedParameterBenchmark_eventually_pos b c p q σ
      h_b h_c h_p h_q h_σ h_nonsaturated
  -- Convert asymptotic equivalence to the normalized ratio limit.
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_benchmark_ne]
  let tN : ℕ → ℝ := fun n ↦ alphaDiscrep n / nonsaturatedParameterBenchmark b c p q σ n
  have h_tN_tendsto_one : Filter.Tendsto tN Filter.atTop (nhds 1) := by
    have h_balance_package :
        ∃ B : ℕ → ℝ → ℝ,
          (∀ᶠ n : ℕ in Filter.atTop, B n (tN n) = 0) ∧
            (∀ ε : ℝ, 0 < ε → ε < 1 →
              ∀ᶠ n : ℕ in Filter.atTop,
                ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 → 0 < (t - 1) * B n t) := by
      -- Route correction: the remaining branch-specific work is exactly the
      -- normalized discrepancy balance on the nonsaturated benchmark scale.
      let _ := h_alphaSpec
      -- TODO: rewrite `(7.90)` at `α = t_n * α_ns n`, factor the benchmark
      -- scale, and use the Proposition 7.19 nonsaturated quadrature asymptotic
      -- to build a balance `B` with zero at `t_n` and the stated sign gap.
      sorry
    rcases h_balance_package with ⟨B, h_balance_zero, h_sign_gap⟩
    exact
      ratioTendstoOne_of_eventualSignGap
        (alphaDiscrep := alphaDiscrep)
        (β := nonsaturatedParameterBenchmark b c p q σ) (B := B)
        h_alpha_nonneg h_benchmark_pos (by simpa [tN] using h_balance_zero) h_sign_gap
  -- Repackage the normalized ratio back into mathlib's asymptotic-equivalence bridge.
  change Filter.Tendsto tN Filter.atTop (nhds 1)
  exact h_tN_tendsto_one

/-- Theorem 7.27 (2). In the critical regime `p - q = -1`, a Chapter 7
Tikhonov discrepancy-principle parameter family is asymptotically equivalent
to the canonical same-index benchmark `betaDiscrep b c p σ` determined by the
displayed logarithmic root equation. -/
theorem isEquivalent_critical
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    Asymptotics.IsEquivalent Filter.atTop alphaDiscrep (betaDiscrep b c p σ) := by
  -- First unpack the pointwise discrepancy equation and the canonical
  -- benchmark root equation into reusable local interfaces.
  have h_alphaSpec :
      ∀ n : ℕ+, 0 ≤ alphaDiscrep n ∧
        IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
    intro n
    exact discrepancyParameterFamily_spec K σ d Rtikh alphaDiscrep h_alphaDiscrep n
  have h_betaTendstoZero :
      Filter.Tendsto (betaDiscrep b c p σ) Filter.atTop (nhds 0) := by
    -- The benchmark support file already exposes the small-root branch limit.
    exact betaDiscrep_tendsto_zero b c p σ h_b h_c h_p h_σ
  have h_betaProfile :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 < betaDiscrep b c p σ n ∧
          betaDiscrep b c p σ n ≤ Real.exp (-(p / (2 * p + 1))) ∧
          criticalDiscrepancyProfile p (betaDiscrep b c p σ n) =
            ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
              (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
    -- Export the benchmark-side root equation through the theorem-local
    -- critical profile before the discrepancy balance is normalized.
    exact betaDiscrepEventuallySmallBranchAndProfile b c p σ h_b h_c h_p h_σ
  have h_beta_ne :
      ∀ᶠ n : ℕ in Filter.atTop, betaDiscrep b c p σ n ≠ 0 :=
    (betaDiscrep_eventually_pos b c p σ h_b h_c h_p h_σ).mono
      (fun _ hn ↦ ne_of_gt hn)
  have h_alpha_nonneg :
      ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ alphaDiscrep n :=
    discrepancyParameterFamily_eventually_nonneg K σ d Rtikh alphaDiscrep h_alphaDiscrep
  have h_beta_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < betaDiscrep b c p σ n :=
    betaDiscrep_eventually_pos b c p σ h_b h_c h_p h_σ
  -- Convert asymptotic equivalence to the normalized ratio limit.
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne]
  let tN : ℕ → ℝ := fun n ↦ alphaDiscrep n / betaDiscrep b c p σ n
  have h_tN_tendsto_one : Filter.Tendsto tN Filter.atTop (nhds 1) := by
    have h_balance_package :
        ∃ B : ℕ → ℝ → ℝ,
          (∀ᶠ n : ℕ in Filter.atTop, B n (tN n) = 0) ∧
            (∀ ε : ℝ, 0 < ε → ε < 1 →
              ∀ᶠ n : ℕ in Filter.atTop,
                ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 → 0 < (t - 1) * B n t) := by
      -- Route correction: the remaining branch-specific work is the critical
      -- logarithmic balance on the `β_discrep` scale.
      let _ := h_alphaSpec
      let _ := h_betaTendstoZero
      let _ := h_betaProfile
      -- TODO: rewrite the discrepancy equation at `α = t_n * β_discrep n` into
      -- the same profile as `criticalDiscrepancyProfile`, transport that
      -- profile with `criticalDiscrepancyProfileScaleExact`, and compare
      -- against the exported benchmark-side root equation in `h_betaProfile`.
      sorry
    rcases h_balance_package with ⟨B, h_balance_zero, h_sign_gap⟩
    exact
      ratioTendstoOne_of_eventualSignGap
        (alphaDiscrep := alphaDiscrep) (β := betaDiscrep b c p σ) (B := B)
        h_alpha_nonneg h_beta_pos (by simpa [tN] using h_balance_zero) h_sign_gap
  -- Repackage the normalized ratio back into mathlib's asymptotic-equivalence bridge.
  change Filter.Tendsto tN Filter.atTop (nhds 1)
  exact h_tN_tendsto_one

/-- Theorem 7.27 (3). In the regime `p - q < -1`, a Chapter 7 Tikhonov
discrepancy-principle parameter family is asymptotically equivalent to the
explicit saturated benchmark sequence built from the fixed source term
`‖f_true‖_{K*}^2`. -/
theorem isEquivalent_saturated
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_saturated : p - q < -1)
    (h_sourceConditionNormSq :
      HasSourceConditionNormSq S h_length fTrue normKStarSq)
    (h_normKStarSq_pos : 0 < normKStarSq) :
    Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
      (saturatedParameterBenchmark c p σ normKStarSq) := by
  -- First isolate the pointwise discrepancy equation and the fixed source-term
  -- scalar that must survive the saturated normalization.
  have h_alphaSpec :
      ∀ n : ℕ+, 0 ≤ alphaDiscrep n ∧
        IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
    intro n
    exact discrepancyParameterFamily_spec K σ d Rtikh alphaDiscrep h_alphaDiscrep n
  have h_sourceFixed :
      ∀ n : ℕ, sourceConditionNormSq (S n) (h_length n) fTrue = normKStarSq := by
    intro n
    -- Reuse the pointwise source-condition owner through the local helper.
    exact
      sourceConditionNormSq_spec
        (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (normKStarSq := normKStarSq) h_sourceConditionNormSq n
  have h_benchmark_ne :
      ∀ᶠ n : ℕ in Filter.atTop,
        saturatedParameterBenchmark c p σ normKStarSq n ≠ 0 :=
    (saturatedParameterBenchmark_eventually_pos c p σ normKStarSq
      h_c h_p h_σ h_normKStarSq_pos).mono
      (fun _ hn ↦ ne_of_gt hn)
  have h_alpha_nonneg :
      ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ alphaDiscrep n :=
    discrepancyParameterFamily_eventually_nonneg K σ d Rtikh alphaDiscrep h_alphaDiscrep
  have h_benchmark_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < saturatedParameterBenchmark c p σ normKStarSq n :=
    saturatedParameterBenchmark_eventually_pos c p σ normKStarSq
      h_c h_p h_σ h_normKStarSq_pos
  -- Convert asymptotic equivalence to the normalized ratio limit.
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_benchmark_ne]
  let tN : ℕ → ℝ := fun n ↦ alphaDiscrep n / saturatedParameterBenchmark c p σ normKStarSq n
  have h_tN_tendsto_one : Filter.Tendsto tN Filter.atTop (nhds 1) := by
    have h_balance_package :
        ∃ B : ℕ → ℝ → ℝ,
          (∀ᶠ n : ℕ in Filter.atTop, B n (tN n) = 0) ∧
            (∀ ε : ℝ, 0 < ε → ε < 1 →
              ∀ᶠ n : ℕ in Filter.atTop,
                ∀ t : ℝ, 0 ≤ t → ε ≤ dist t 1 → 0 < (t - 1) * B n t) := by
      -- Route correction: the remaining branch-specific work is the saturated
      -- balance after freezing the source-condition scalar `‖f_true‖_{K*}^2`.
      let _ := h_alphaSpec
      let _ := h_sourceFixed
      -- TODO: rewrite `(7.90)` at `α = t_n * α_sat n`, replace the source term
      -- by `normKStarSq`, and use the saturated Proposition 7.19 asymptotic to
      -- build the normalized balance with the required sign gap.
      sorry
    rcases h_balance_package with ⟨B, h_balance_zero, h_sign_gap⟩
    exact
      ratioTendstoOne_of_eventualSignGap
        (alphaDiscrep := alphaDiscrep)
        (β := saturatedParameterBenchmark c p σ normKStarSq) (B := B)
        h_alpha_nonneg h_benchmark_pos (by simpa [tN] using h_balance_zero) h_sign_gap
  -- Repackage the normalized ratio back into mathlib's asymptotic-equivalence bridge.
  change Filter.Tendsto tN Filter.atTop (nhds 1)
  exact h_tN_tendsto_one

/-- The regime-split asymptotic clauses from Theorem 7.27, packaged as one
source-facing Chapter 7 owner while retaining the explicit critical benchmark
and the source-term scalar `‖f_true‖_{K*}^2` in the saturated branch. -/
def ParameterAsymptotics : Prop :=
  (p - q > -1 →
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
        (nonsaturatedParameterBenchmark b c p q σ)) ∧
    (p - q = -1 →
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
        (betaDiscrep b c p σ)) ∧
    (p - q < -1 →
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep
        (saturatedParameterBenchmark c p σ normKStarSq))

/-- thm_7_27. Theorem 7.27 (Regularization Parameter Choice for the
Discrepancy Principle Applied to Tikhonov Regularization). Main labeled
source-facing entry.

The source theorem is recorded as the three regime-specific asymptotic clauses
from `(7.91)`: the nonsaturated power-law benchmark, the critical logarithmic
benchmark `β_discrep`, and the saturated power-law benchmark carrying the
fixed source-term scalar `‖f_true‖_{K*}^2`. The preceding theorem skeletons
expose these branches separately for downstream proof stages and reuse. -/
theorem parameterAsymptotics
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_sourceConditionNormSq :
      HasSourceConditionNormSq S h_length fTrue normKStarSq)
    (h_normKStarSq_pos : 0 < normKStarSq) :
    ParameterAsymptotics
      b c p q σ alphaDiscrep normKStarSq := by
  -- Package the three regime-specific asymptotic owners proved above.
  constructor
  · intro h_nonsaturated
    -- The nonsaturated clause is exactly `isEquivalent_nonsaturated`.
    exact isEquivalent_nonsaturated
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_nonsaturated
  constructor
  · intro h_critical
    -- The critical clause is exactly `isEquivalent_critical`.
    exact isEquivalent_critical
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_critical
  · intro h_saturated
    -- The saturated clause is exactly `isEquivalent_saturated`.
    exact isEquivalent_saturated
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep normKStarSq
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_saturated
      h_sourceConditionNormSq h_normKStarSq_pos

end

end TikhonovDiscrepancy
