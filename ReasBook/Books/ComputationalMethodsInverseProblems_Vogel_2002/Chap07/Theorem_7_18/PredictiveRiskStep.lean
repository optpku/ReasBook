/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRisk

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section PredictiveRiskStep

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
variable (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
variable
  (h_noise_modeVariance :
    ∀ n i,
      ∫ ω,
        (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
          σ ^ 2 / (n : ℝ))
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

/-- Helper for Theorem 7.18: pointwise, the predictive-risk backward step of a
TSVD truncation replaces the signal contribution
`σ_m ^ 2 * ⟨u_m, fTrue⟩ ^ 2` of the new mode by its noise contribution
`⟨v_m, noise⟩ ^ 2`. The two contributions are single-mode quantities, so no
cross-mode noise correlation hypothesis is needed. -/
theorem expectedPredictiveRiskStep_pointwise
    {n m : ℕ} (hm : 0 < m) (ω : Ω) :
    ‖(K n) (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω))‖ ^ 2 -
        ‖(K n) (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω))‖ ^
            2 =
      -((S n).singularValue ((S n).natIndex (h_length n) (m - 1)) ^ 2 *
          (inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue) ^ 2) +
        (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (η n ω)) ^ 2 := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let s : ℝ := (S n).singularValue j
  let a : ℝ := inner ℝ u fTrue
  let ξ : ℝ := (1 / s) * inner ℝ v (η n ω)
  obtain ⟨r, hr_orth, hPrev, hCurr⟩ :=
    backwardErrors_commonRemainder
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hm ω
  have hu_norm : ‖u‖ = 1 := by
    simpa [u] using (S n).rightBasis.orthonormal.norm_eq_one j
  have hv_norm : ‖v‖ = 1 := by
    simpa [v] using (S n).leftBasis.orthonormal.norm_eq_one j
  have hKu : (K n) u = s • v := by
    simpa [u, v, s] using (S n).map_right j
  have hKadj : (K n).adjoint v = s • u := by
    simpa [u, v, s] using (S n).adjoint_map_left j
  -- The image of the common remainder is orthogonal to the new left singular mode.
  -- The image of the common remainder is orthogonal to the new left singular mode.
  have hKr_orth : inner ℝ ((K n) r) v = 0 := by
    have h1 : inner ℝ ((K n) r) v = inner ℝ ((K n).adjoint v) r := by
      rw [real_inner_comm]
      exact (ContinuousLinearMap.adjoint_inner_left (K n) r v).symm
    have hu_r : inner ℝ u r = 0 := by simpa [u, j] using hr_orth
    rw [h1, hKadj, inner_smul_left, hu_r, mul_zero]
  -- Push both one-step errors through `K n`.
  have hCurrEq :
      FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω) = r + ξ • u := by
    simpa only [ξ, u, s, j] using hCurr
  have hPrevEq :
      FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω) =
        r + (-a) • u := by
    simpa only [a, u, j] using hPrev
  have hCurrK :
      (K n) (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)) =
        (K n) r + (ξ * s) • v := by
    rw [hCurrEq, map_add, map_smul, hKu, smul_smul]
  have hPrevK :
      (K n) (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)) =
        (K n) r + (-a * s) • v := by
    rw [hPrevEq, map_add, map_smul, hKu, smul_smul]
  -- Orthogonality of the two summands turns the norms into single-mode squares.
  have hscalar : ∀ c : ℝ, ‖c • v‖ ^ 2 = c ^ 2 := by
    intro c
    rw [norm_smul, hv_norm, mul_one, Real.norm_eq_abs, sq_abs]
  have hCurrNorm :
      ‖(K n) r + (ξ * s) • v‖ ^ 2 = ‖(K n) r‖ ^ 2 + (ξ * s) ^ 2 := by
    have horth : inner ℝ ((K n) r) ((ξ * s) • v) = 0 := by
      rw [inner_smul_right, hKr_orth, mul_zero]
    have hsum :
        ‖(K n) r + (ξ * s) • v‖ ^ 2 = ‖(K n) r‖ ^ 2 + ‖(ξ * s) • v‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((K n) r) ((ξ * s) • v) horth
    rw [hsum, hscalar]
  have hPrevNorm :
      ‖(K n) r + (-a * s) • v‖ ^ 2 = ‖(K n) r‖ ^ 2 + (-a * s) ^ 2 := by
    have horth : inner ℝ ((K n) r) ((-a * s) • v) = 0 := by
      rw [inner_smul_right, hKr_orth, mul_zero]
    have hsum :
        ‖(K n) r + (-a * s) • v‖ ^ 2 = ‖(K n) r‖ ^ 2 + ‖(-a * s) • v‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((K n) r) ((-a * s) • v) horth
    rw [hsum, hscalar]
  rw [hCurrK, hPrevK, hCurrNorm, hPrevNorm]
  -- The scalar difference is the noise square minus the scaled signal square.
  have hs_ne : s ≠ 0 := ne_of_gt (by simpa [s] using (S n).singularValue_pos j)
  have hξ : (ξ * s) ^ 2 = (inner ℝ v (η n ω)) ^ 2 := by
    simp only [ξ]
    field_simp
  have ha : (-a * s) ^ 2 = s ^ 2 * a ^ 2 := by ring
  rw [hξ, ha]
  ring

/-- Helper for Theorem 7.18: the expected predictive-risk backward step is
`σ ^ 2 / n ^ 2 - (b * c / n) * m ^ (-(p + q))`, i.e. the noise level `σ ^ 2 / n`
of a single mode minus the signal cross term `b * c * m ^ (-(p + q))`. -/
theorem expectedPredictiveRiskObjective_backwardStep_eq
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    expectedPredictiveRiskObjective μ K Rtsvd fTrue η n m -
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (m - 1) =
      (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (m : ℝ) ^ (-(p + q)) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let v : F := ((S n).leftBasis j : F)
  let s : ℝ := (S n).singularValue j
  let a : ℝ := inner ℝ ((S n).rightBasis j : H) fTrue
  have hErrorMemLp (k : ℕ) :
      MeasureTheory.MemLp
        (fun ω ↦ FilterRegularization.estimationError (Rtsvd n k) (K n) fTrue (η n ω)) 2 μ := by
    have hNoiseImage : MeasureTheory.MemLp (fun ω ↦ Rtsvd n k (η n ω)) 2 μ := by
      simpa using (h_noise_memLp n).continuousLinearMap_comp (Rtsvd n k)
    have hConst :
        MeasureTheory.MemLp (fun _ : Ω ↦ Rtsvd n k ((K n) fTrue) - fTrue) 2 μ := by
      simpa using
        (MeasureTheory.memLp_const
          (α := Ω) (μ := μ) (p := (2 : ENNReal))
          (c := Rtsvd n k ((K n) fTrue) - fTrue))
    convert hConst.add hNoiseImage using 1
    funext ω
    simp [FilterRegularization.estimationError_def, sub_eq_add_neg, add_left_comm,
      add_comm, map_add]
  have hCurrInt :
      MeasureTheory.Integrable
        (fun ω ↦ ‖(K n)
          (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω))‖ ^ 2) μ :=
    MeasureTheory.MemLp.integrable_norm_pow (p := 2)
      ((hErrorMemLp m).continuousLinearMap_comp (K n)) (by decide)
  have hPrevInt :
      MeasureTheory.Integrable
        (fun ω ↦ ‖(K n)
          (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω))‖ ^ 2) μ :=
    MeasureTheory.MemLp.integrable_norm_pow (p := 2)
      ((hErrorMemLp (m - 1)).continuousLinearMap_comp (K n)) (by decide)
  have hConstInt : MeasureTheory.Integrable (fun _ : Ω ↦ -(s ^ 2 * a ^ 2)) μ :=
    MeasureTheory.integrable_const _
  have hNoiseModeLp : MeasureTheory.MemLp (fun ω ↦ inner ℝ v (η n ω)) 2 μ := by
    simpa [v] using MeasureTheory.MemLp.const_inner v (h_noise_memLp n)
  have hNoiseModeSqInt :
      MeasureTheory.Integrable (fun ω ↦ (inner ℝ v (η n ω)) ^ 2) μ :=
    MeasureTheory.MemLp.integrable_sq hNoiseModeLp
  have hSplitIntegral :
      ∫ ω, (-(s ^ 2 * a ^ 2) : ℝ) + (inner ℝ v (η n ω)) ^ 2 ∂μ =
        ∫ _ : Ω, (-(s ^ 2 * a ^ 2) : ℝ) ∂μ +
          ∫ ω, (inner ℝ v (η n ω)) ^ 2 ∂μ := by
    simpa using
      (MeasureTheory.integral_add
        (μ := μ)
        (f := fun _ : Ω ↦ (-(s ^ 2 * a ^ 2) : ℝ))
        (g := fun ω ↦ (inner ℝ v (η n ω)) ^ 2)
        hConstInt hNoiseModeSqInt)
  have hVariance : ∫ ω, (inner ℝ v (η n ω)) ^ 2 ∂μ = σ ^ 2 / (n : ℝ) := by
    simpa [v, j] using h_noise_modeVariance n (m - 1)
  have hConstEval : ∫ _ : Ω, (-(s ^ 2 * a ^ 2) : ℝ) ∂μ = -(s ^ 2 * a ^ 2) := by
    simp [MeasureTheory.integral_const]
  have ha_sq : a ^ 2 = b * (m : ℝ) ^ (-q) := by
    simpa [a, j] using (h_fourierDecay n ⟨m, hm⟩)
  have hs_sq : s ^ 2 = c * (m : ℝ) ^ (-p) := by
    simpa [s, j] using (h_singularDecay n ⟨m, hm⟩)
  have hprod : s ^ 2 * a ^ 2 = b * c * (m : ℝ) ^ (-(p + q)) := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsplit : (m : ℝ) ^ (-(p + q)) = (m : ℝ) ^ (-p) * (m : ℝ) ^ (-q) := by
      rw [show -(p + q) = -p + -q by ring, Real.rpow_add hm0]
    rw [hs_sq, ha_sq, hsplit]
    ring
  have hPointwise :
      (fun ω ↦
        ‖(K n) (FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω))‖ ^ 2 -
          ‖(K n)
              (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω))‖ ^
            2) =
        fun ω ↦ -(s ^ 2 * a ^ 2) + (inner ℝ v (η n ω)) ^ 2 := by
    funext ω
    simpa [a, s, v, j] using
      (expectedPredictiveRiskStep_pointwise
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := m)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hm ω)
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  rw [expectedPredictiveRiskObjective_apply, expectedPredictiveRiskObjective_apply,
    MeasureTheory.integral_div, MeasureTheory.integral_div, ← sub_div,
    ← MeasureTheory.integral_sub hCurrInt hPrevInt, hPointwise]
  rw [hSplitIntegral, hVariance, hConstEval, hprod]
  field_simp
  ring

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

end PredictiveRiskStep

end TsvdEstimation
