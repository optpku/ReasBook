/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRisk
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exercise 7.14: exclude the two TSVD predictive-risk endpoints

For the normalized noise model, each of the first `n` left singular modes has
second moment `σ² / n`. The predictive-risk backward step at mode `m` is
`(σ² / n - b * c * m ^ (-(p + q))) / n`. At `m = 1` this is eventually
negative, whereas at `m = n` it is eventually positive. The admissible
neighbours `1` and `n - 1` therefore exclude the endpoints `0` and `n`.

The moment hypothesis is restricted to the observed modes `i < n`; it places
no white-noise condition on the remaining infinite singular system. The
single-mode step below only needs square-integrability and that mode's
second moment.
-/

public section

noncomputable section

open scoped TsvdEstimation.Notation BigOperators Topology
open Filter MeasureTheory

namespace TsvdEstimation

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)

include h_tsvd in
/-- Adding one TSVD mode replaces its squared signal coefficient in the
predictive error by its squared noise coefficient. -/
private lemma predictiveRiskStep_pointwise_of_reconstruction
    {n m : ℕ} (hm : 0 < m) (noise : F) :
    ‖K n (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue noise)‖ ^ 2 -
      ‖K n (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue noise)‖ ^ 2 =
    (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) noise) ^ 2 -
      (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (K n fTrue)) ^ 2 := by
  let j := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let s := (S n).singularValue j
  let a := inner ℝ v (K n fTrue)
  let ξ := inner ℝ v noise
  let e := K n (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue noise)
  have hs : s ≠ 0 := (S n).singularValue_pos j |>.ne'
  have hstep (g : F) : Rtsvd n m g = Rtsvd n (m - 1) g +
      ((1 / s) * inner ℝ v g) • u := by
    rw [h_tsvd n m g, ← Nat.succ_pred_eq_of_pos hm, Finset.sum_range_succ]
    simpa [u, v, s, j] using congrArg
      (fun x : H ↦ x + ((1 / s) * inner ℝ v g) • u) (h_tsvd n (m - 1) g).symm
  have hprev (g : F) : inner ℝ u (Rtsvd n (m - 1) g) = 0 := by
    rw [h_tsvd n (m - 1) g, inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : j ≠ (S n).natIndex (h_length n) i := by
      intro heq
      exact (ne_of_lt ((S n).natIndex_strictMono (h_length n)
        (Finset.mem_range.1 hi))) heq.symm
    have horth : inner ℝ u ((S n).rightBasis ((S n).natIndex (h_length n) i) : H) = 0 :=
      (S n).rightBasis.orthonormal.2 hij
    rw [inner_smul_right, horth, mul_zero]
  have hinner : inner ℝ v e = -a := by
    dsimp [e]
    rw [FilterRegularization.estimationError_def, map_sub, inner_sub_right]
    change inner ℝ ((S n).leftBasis j : F)
      (K n (Rtsvd n (m - 1) (K n fTrue + noise))) - a = -a
    rw [← ContinuousLinearMap.adjoint_inner_left, (S n).adjoint_map_left,
      real_inner_smul_left]
    change s * inner ℝ u (Rtsvd n (m - 1) (K n fTrue + noise)) - a = -a
    rw [hprev]
    ring
  have herror : FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue noise =
      FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue noise +
        ((1 / s) * inner ℝ v (K n fTrue + noise)) • u := by
    rw [FilterRegularization.estimationError_def, hstep,
      FilterRegularization.estimationError_def]
    abel
  have hcurr : K n (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue noise) =
      e + (a + ξ) • v := by
    rw [herror, map_add, map_smul]
    have hKu : K n u = s • v := (S n).map_right j
    rw [hKu, smul_smul]
    have hscalar : ((1 / s) * inner ℝ v (K n fTrue + noise)) * s = a + ξ := by
      dsimp [a, ξ]
      rw [inner_add_right]
      field_simp
    rw [hscalar]
  change ‖K n (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue noise)‖ ^ 2 -
    ‖e‖ ^ 2 = ξ ^ 2 - a ^ 2
  have hinner' : inner ℝ e v = -a := by rw [real_inner_comm]; exact hinner
  have hvnorm : ‖v‖ = 1 := by
    simpa [v] using (S n).leftBasis.orthonormal.norm_eq_one j
  rw [hcurr, norm_add_sq_real, inner_smul_right, hinner',
    norm_smul, hvnorm, mul_one, Real.norm_eq_abs, sq_abs]
  ring

variable (h_noise_memLp : ∀ n, MemLp (η n) 2 μ)
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)

include h_noise_memLp h_singularDecay h_fourierDecay h_tsvd in
/-- The predictive-risk step depends only on the second moment `τ` of the
newly included mode. In particular, moments of unobserved modes are unnecessary. -/
theorem expectedPredictiveRiskObjective_backwardStep_eq_of_modeSecondMoment
    {n m : ℕ} (hm : 0 < m) {τ : ℝ}
    (h_variance : ∫ ω,
      (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (η n ω)) ^ 2 ∂μ = τ) :
    expectedPredictiveRiskObjective μ K Rtsvd fTrue η n m -
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (m - 1) =
    (τ - b * c * (m : ℝ) ^ (-(p + q))) / (n : ℝ) := by
  let j := (S n).natIndex (h_length n) (m - 1)
  let v : F := ((S n).leftBasis j : F)
  have hLp (k : ℕ) : MemLp (fun ω ↦
      FilterRegularization.estimationError (Rtsvd n k) (K n) fTrue (η n ω)) 2 μ := by
    have hconst : MemLp (fun _ : Ω ↦ Rtsvd n k (K n fTrue) - fTrue) 2 μ := memLp_const _
    convert hconst.add ((h_noise_memLp n).continuousLinearMap_comp (Rtsvd n k)) using 1
    funext ω
    simp [FilterRegularization.estimationError_def, map_add, sub_eq_add_neg,
      add_comm, add_left_comm]
  have hi (k : ℕ) : Integrable (fun ω ↦
      ‖K n (FilterRegularization.estimationError (Rtsvd n k) (K n) fTrue (η n ω))‖ ^ 2) μ :=
    ((hLp k).continuousLinearMap_comp (K n)).integrable_norm_pow (by decide)
  have hnoise : Integrable (fun ω ↦ (inner ℝ v (η n ω)) ^ 2) μ :=
    (MemLp.const_inner v (h_noise_memLp n)).integrable_sq
  have hsignal : (inner ℝ v (K n fTrue)) ^ 2 = b * c * (m : ℝ) ^ (-(p + q)) := by
    have hs : (S n).singularValue j ^ 2 = c * (m : ℝ) ^ (-p) := by
      simpa [j] using h_singularDecay n ⟨m, hm⟩
    have hf : (inner ℝ ((S n).rightBasis j : H) fTrue) ^ 2 = b * (m : ℝ) ^ (-q) := by
      simpa [j] using h_fourierDecay n ⟨m, hm⟩
    change (inner ℝ ((S n).leftBasis j : F) (K n fTrue)) ^ 2 = _
    rw [← ContinuousLinearMap.adjoint_inner_left, (S n).adjoint_map_left,
      real_inner_smul_left]
    simp only [RCLike.ofReal_real_eq_id, id_eq, mul_pow]
    rw [hs, hf, show -(p + q) = -p + -q by ring,
      Real.rpow_add (by positivity : (0 : ℝ) < m)]
    ring
  have hpw : (fun ω ↦
      ‖K n (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω))‖ ^ 2 -
        ‖K n (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω))‖ ^ 2) =
      fun ω ↦ (inner ℝ v (η n ω)) ^ 2 - (inner ℝ v (K n fTrue)) ^ 2 := by
    funext ω
    exact predictiveRiskStep_pointwise_of_reconstruction K S h_length fTrue Rtsvd h_tsvd hm (η n ω)
  rw [expectedPredictiveRiskObjective_apply, expectedPredictiveRiskObjective_apply,
    integral_div, integral_div, ← sub_div, ← integral_sub (hi m) (hi (m - 1)), hpw,
    integral_sub hnoise (integrable_const _)]
  simp only [v, j, h_variance, integral_const, probReal_univ, one_smul, hsignal]

variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
/- The normalized noise second moment is prescribed only in the `n`
observed modes. -/
variable (h_noise_modeVariance : ∀ n i, i < n → ∫ ω,
  (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
    σ ^ 2 / (n : ℝ))

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

omit h_p h_q h_σ in
/-- Exercise 7.14 (1). Eventually the admissible truncation `1` has smaller
expected predictive risk than the lower endpoint `0`, because
`σ² / n < b * c` for all sufficiently large `n`. -/
theorem lowerEndpoint_not_minimizer_eventually :
    ∀ᶠ n in atTop, ¬ IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (𝒵(n)) 0 := by
  have hthr : ∀ᶠ n : ℕ in atTop, σ ^ 2 / (b * c) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (σ ^ 2 / (b * c)))
  filter_upwards [hthr, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro hmin
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn1
  have hstep := expectedPredictiveRiskObjective_backwardStep_eq_of_modeSecondMoment
    μ K S h_length fTrue b c p q η Rtsvd h_tsvd h_noise_memLp
    h_singularDecay h_fourierDecay (m := 1) (by decide)
    (by simpa using h_noise_modeVariance n 0 (by omega))
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hstep
  have hquot : σ ^ 2 / (n : ℝ) < b * c := by
    rw [div_lt_iff₀ hnreal]
    simpa only [mul_comm] using (div_lt_iff₀ (mul_pos h_b h_c)).1 hn
  have hneg : (σ ^ 2 / (n : ℝ) - b * c) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.2 hquot) hnreal
  have hone : 1 ∈ 𝒵(n) := ⟨Nat.zero_le _, hn1⟩
  have hle := (isMinOn_iff.1 hmin) 1 hone
  simp only [Nat.sub_self] at hstep
  linarith

omit h_b h_c in
/-- Exercise 7.14 (2). Eventually the admissible truncation `n - 1` has smaller
expected predictive risk than the upper endpoint `n`: the last-mode signal
term decays faster than its noise second moment. -/
theorem upperEndpoint_not_minimizer_eventually :
    ∀ᶠ n in atTop, ¬ IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (𝒵(n)) n := by
  have hpq : 0 < p + q - 1 := by linarith
  have hlim : Tendsto (fun n : ℕ ↦ b * c * (n : ℝ) ^ (-(p + q - 1))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hpq).comp tendsto_natCast_atTop_atTop).const_mul (b * c)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      b * c * (n : ℝ) ^ (-(p + q - 1)) < σ ^ 2 :=
    hlim.eventually (gt_mem_nhds (pow_pos h_σ 2))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro hmin
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsplit : (n : ℝ) ^ (-(p + q - 1)) = (n : ℝ) ^ (-(p + q)) * n := by
    convert Real.rpow_add_one hnreal.ne' (-(p + q)) using 1
    congr 1
    ring
  rw [hsplit] at hn
  have hquot : b * c * (n : ℝ) ^ (-(p + q)) < σ ^ 2 / (n : ℝ) := by
    rw [lt_div_iff₀ hnreal]
    nlinarith
  have hpos : 0 < (σ ^ 2 / (n : ℝ) - b * c * (n : ℝ) ^ (-(p + q))) / (n : ℝ) :=
    div_pos (sub_pos.2 hquot) hnreal
  have hstep := expectedPredictiveRiskObjective_backwardStep_eq_of_modeSecondMoment
    μ K S h_length fTrue b c p q η Rtsvd h_tsvd h_noise_memLp
    h_singularDecay h_fourierDecay (m := n) hn1
    (h_noise_modeVariance n (n - 1) (by omega))
  have hprev : n - 1 ∈ 𝒵(n) := ⟨Nat.zero_le _, Nat.sub_le _ _⟩
  have hle := (isMinOn_iff.1 hmin) (n - 1) hprev
  linarith

/-- For all sufficiently large data sizes, neither boundary point of `𝒵(n)`
minimizes the expected predictive risk. -/
theorem endpoints_not_minimizers_eventually :
    ∀ᶠ n in atTop,
      ¬ IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (𝒵(n)) 0 ∧
        ¬ IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (𝒵(n)) n := by
  exact (lowerEndpoint_not_minimizer_eventually
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_tsvd := h_tsvd) (h_noise_memLp := h_noise_memLp)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_b := h_b) (h_c := h_c) (h_noise_modeVariance := h_noise_modeVariance)).and
      (upperEndpoint_not_minimizer_eventually
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
        (h_tsvd := h_tsvd) (h_noise_memLp := h_noise_memLp)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_modeVariance := h_noise_modeVariance))

end TsvdEstimation
