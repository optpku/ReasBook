/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Constants
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_11.WeightedSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

public section

noncomputable section

namespace TikhonovDiscrepancy

universe u v

section DiscrepancyEquation

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise Tikhonov discrepancy equation `(7.90)` for data size
`n : ℕ+`. -/
@[expose]
def IsTikhonovDiscrepancyParameter
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (σ : ℝ) (n : ℕ+) (α : ℝ) : Prop :=
  ‖K n (Rtikh n α (d n)) - d n‖ ^ 2 / (n : ℝ) = σ ^ 2

/-- The defining characterization of `IsTikhonovDiscrepancyParameter`. -/
theorem isTikhonovDiscrepancyParameter_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (σ : ℝ) (n : ℕ+) (α : ℝ) :
    IsTikhonovDiscrepancyParameter K d Rtikh σ n α ↔
      ‖K n (Rtikh n α (d n)) - d n‖ ^ 2 / (n : ℝ) = σ ^ 2 := by
  -- The exposed owner is definitionally the displayed discrepancy equation.
  rfl

/-- A Chapter 7 discrepancy-principle Tikhonov parameter family solves the
displayed discrepancy equation `(7.90)` at each positive data size and stays
nonnegative. -/
@[expose]
def IsTikhonovDiscrepancyParameterFamily
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (σ : ℝ) (alphaDiscrep : ℕ → ℝ) : Prop :=
  ∀ n : ℕ+, 0 ≤ alphaDiscrep n ∧
    IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n)

/-- The defining pointwise characterization of
`IsTikhonovDiscrepancyParameterFamily`. -/
theorem isTikhonovDiscrepancyParameterFamily_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (σ : ℝ) (alphaDiscrep : ℕ → ℝ) :
    IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep ↔
      ∀ n : ℕ+, 0 ≤ alphaDiscrep n ∧
        IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
  -- The family owner is definitionally pointwise.
  rfl

end DiscrepancyEquation

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : H →L[ℝ] F}

/-- The squared `‖f_true‖_{K*}^2` source term from Theorem 7.27, encoded using
the weighted source series from Remark 7.11. -/
@[expose]
def sourceConditionNormSq
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) : ℝ :=
  tsum (S.weightedSourceSeries h_length fTrue)

/-- The defining formula for `sourceConditionNormSq`. -/
theorem sourceConditionNormSq_def
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) :
    sourceConditionNormSq S h_length fTrue =
      tsum (S.weightedSourceSeries h_length fTrue) := by
  -- Unfold the source-condition scalar.
  rfl

/-- A fixed scalar `normKStarSq` represents the Chapter 7 source term
`‖f_true‖_{K*}^2` when it agrees with the singular-system source expression at
every data size. -/
@[expose]
def HasSourceConditionNormSq
    {Kseq : ℕ → H →L[ℝ] F}
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (Kseq n))
    (h_length : ∀ n, (S n).length = ⊤) (fTrue : H) (normKStarSq : ℝ) : Prop :=
  ∀ n, sourceConditionNormSq (S n) (h_length n) fTrue = normKStarSq

/-- The defining pointwise characterization of `HasSourceConditionNormSq`. -/
theorem hasSourceConditionNormSq_iff
    {Kseq : ℕ → H →L[ℝ] F}
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (Kseq n))
    (h_length : ∀ n, (S n).length = ⊤) (fTrue : H) (normKStarSq : ℝ) :
    HasSourceConditionNormSq S h_length fTrue normKStarSq ↔
      ∀ n, sourceConditionNormSq (S n) (h_length n) fTrue = normKStarSq := by
  -- The fixed-source scalar owner is definitionally pointwise.
  rfl

/-- The explicit nonsaturated benchmark sequence from Theorem 7.27(1). -/
@[expose]
def nonsaturatedParameterBenchmark (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ parameterConstant1 b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))

/-- The defining closed form of the nonsaturated benchmark sequence. -/
theorem nonsaturatedParameterBenchmark_def
    (b c p q σ : ℝ) (n : ℕ) :
    nonsaturatedParameterBenchmark b c p q σ n =
      parameterConstant1 b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) :=
  rfl

/-- The explicit saturated benchmark sequence from Theorem 7.27(3). The scalar
`normKStarSq` represents the source term `‖f_true‖_{K*}^2`. -/
@[expose]
def saturatedParameterBenchmark (c p σ normKStarSq : ℝ) : ℕ → ℝ :=
  fun n ↦
    parameterConstant2 c p normKStarSq * (((σ ^ 2) / (n : ℝ)) ^ (p / (2 * p + 1)))

/-- The defining closed form of the saturated benchmark sequence. -/
theorem saturatedParameterBenchmark_def
    (c p σ normKStarSq : ℝ) (n : ℕ) :
    saturatedParameterBenchmark c p σ normKStarSq n =
      parameterConstant2 c p normKStarSq * (((σ ^ 2) / (n : ℝ)) ^ (p / (2 * p + 1))) :=
  rfl

/-- The critical logarithmic root equation defining the benchmark
`β_discrep` in the middle branch of Theorem 7.27. -/
@[expose]
def BetaDiscrepRootEquation (b c p σ : ℝ) (n : ℕ+) (β : ℝ) : Prop :=
  -(β ^ ((2 * p + 1) / p)) * Real.log β =
    ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
      (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)

/-- The defining equation for `BetaDiscrepRootEquation`. -/
theorem betaDiscrepRootEquation_iff
    (b c p σ : ℝ) (n : ℕ+) (β : ℝ) :
    BetaDiscrepRootEquation b c p σ n β ↔
      -(β ^ ((2 * p + 1) / p)) * Real.log β =
        ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
          (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
  -- The exposed root-equation owner is definitionally the displayed equation.
  rfl

/-- The positive-index owner for the canonical critical benchmark
`β_discrep` from Theorem 7.27, chosen as the infimum of the positive
solutions of the logarithmic root equation at the same data size `n`. -/
@[expose]
def betaDiscrepAt (b c p σ : ℝ) : ℕ+ → ℝ :=
  fun n ↦ sInf {β : ℝ | 0 < β ∧ BetaDiscrepRootEquation b c p σ n β}

/-- The defining formula for `betaDiscrepAt`. -/
theorem betaDiscrepAt_def (b c p σ : ℝ) (n : ℕ+) :
    betaDiscrepAt b c p σ n =
      sInf {β : ℝ | 0 < β ∧ BetaDiscrepRootEquation b c p σ n β} := by
  -- Unfold the positive-index benchmark owner.
  rfl

/-- The canonical nat-indexed critical benchmark `β_discrep` from Theorem
7.27. On positive data sizes it agrees with `betaDiscrepAt`; the value at
`n = 0` is filled by the first positive index so the asymptotic sequence stays
nat-indexed without introducing a spurious `n + 1` shift. -/
@[expose]
def betaDiscrep (b c p σ : ℝ) : ℕ → ℝ :=
  fun n ↦
    if h : 0 < n then
      betaDiscrepAt b c p σ ⟨n, h⟩
    else
      betaDiscrepAt b c p σ ⟨1, by decide⟩

/-- The defining formula for `betaDiscrep`. -/
theorem betaDiscrep_def (b c p σ : ℝ) (n : ℕ) :
    betaDiscrep b c p σ n =
      if h : 0 < n then
        betaDiscrepAt b c p σ ⟨n, h⟩
      else
        betaDiscrepAt b c p σ ⟨1, by decide⟩ := by
  -- Unfold the nat-indexed benchmark owner.
  rfl

/-- On positive data sizes, the nat-indexed benchmark `betaDiscrep` agrees
with the same-index positive owner `betaDiscrepAt`. -/
theorem betaDiscrep_eq_betaDiscrepAt
    (b c p σ : ℝ) (n : ℕ+) :
    betaDiscrep b c p σ n = betaDiscrepAt b c p σ n := by
  -- Positive indices always take the same-index branch of `betaDiscrep`.
  have hpos : 0 < (n : ℕ) := n.2
  dsimp [betaDiscrep]
  rw [dif_pos hpos]
  -- The two positive-index constructors have the same underlying natural number.
  congr

/-- Helper for Theorem 7.27: the right-hand side of the critical benchmark
root equation is strictly positive under the admissibility hypotheses. -/
lemma betaDiscrepRootEquation_rhs_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ)
    (n : ℕ+) :
    0 <
      ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
        (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
  have h_p0 : 0 < p := by
    linarith
  have h_decayMain : 0 < 2 * p - p - 1 := by
    nlinarith [h_p]
  have h_sMain : 0 < p + 1 := by
    nlinarith [h_p]
  have h_integralMain : 0 < KernelMoment.integral p 2 p := by
    -- The `s = p` moment is positive in the admissible regime `p > 1`.
    rw [KernelMoment.integral_eq_gamma_mul_gamma_div_factorial
      (p := p) (s := p) (j := 2) h_sMain h_decayMain]
    refine div_pos ?_ ?_
    · refine mul_pos ?_ ?_
      · exact Real.Gamma_pos_of_pos (div_pos h_decayMain h_p0)
      · exact Real.Gamma_pos_of_pos (div_pos h_sMain h_p0)
    · positivity
  have h_decayZero : 0 < 2 * p - 0 - 1 := by
    nlinarith [h_p]
  have h_sZero : (0 : ℝ) < 0 + 1 := by
    norm_num
  have h_integralZero : 0 < KernelMoment.integral p 2 0 := by
    -- The `s = 0` moment uses the same positivity route.
    rw [KernelMoment.integral_eq_gamma_mul_gamma_div_factorial
      (p := p) (s := 0) (j := 2) h_sZero h_decayZero]
    refine div_pos ?_ ?_
    · refine mul_pos ?_ ?_
      · exact Real.Gamma_pos_of_pos (div_pos h_decayZero h_p0)
      · exact Real.Gamma_pos_of_pos (div_pos h_sZero h_p0)
    · positivity
  have h_scalePos : 0 < (σ ^ 2) / (n : ℝ) := by
    exact div_pos (by nlinarith [sq_pos_of_pos h_σ]) (show 0 < (n : ℝ) by exact_mod_cast n.2)
  have h_restPos :
      0 < b⁻¹ * c ^ ((p + 1) / p) * p *
        (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
    have h_momentSumPos :
        0 < 2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0 := by
      nlinarith
    refine mul_pos ?_ h_momentSumPos
    refine mul_pos ?_ h_p0
    refine mul_pos ?_ (Real.rpow_pos_of_pos h_c ((p + 1) / p))
    simpa using inv_pos.mpr h_b
  -- Every factor in the displayed right-hand side is strictly positive.
  simpa [mul_assoc] using mul_pos h_scalePos h_restPos

/-- Helper for Theorem 7.27: the critical logarithmic profile exponent is
strictly positive in the admissible regime `p > 1`. -/
private lemma criticalProfileExponent_pos
    (h_p : 1 < p) :
    0 < ((2 * p + 1) / p : ℝ) := by
  have h_p0 : 0 < p := by
    linarith
  have h_num : 0 < 2 * p + 1 := by
    linarith
  exact div_pos h_num h_p0

/-- Helper for Theorem 7.27: the small-branch cutoff for the critical
logarithmic profile is strictly positive. -/
private lemma criticalProfileUpper_pos
    (p : ℝ) :
    0 < Real.exp (-(p / (2 * p + 1))) :=
  Real.exp_pos _

/-- Helper for Theorem 7.27: the small-branch cutoff lies below `1` once
`p > 1`. -/
private lemma criticalProfileUpper_lt_one
    (h_p : 1 < p) :
    Real.exp (-(p / (2 * p + 1))) < 1 := by
  have h_p0 : 0 < p := by
    linarith
  have h_den : 0 < 2 * p + 1 := by
    linarith
  have h_frac : 0 < p / (2 * p + 1) := by
    exact div_pos h_p0 h_den
  exact Real.exp_lt_one_iff.2 (by linarith)

/-- Helper for Theorem 7.27: the critical profile written in the source shape
of the logarithmic root equation. -/
private def criticalProfile (p β : ℝ) : ℝ :=
  -(β ^ ((2 * p + 1) / p) * Real.log β)

/-- Helper for Theorem 7.27: the nat-indexed right-hand side of the critical
benchmark root equation. -/
private def betaDiscrepRootRhsNat (b c p σ : ℝ) (n : ℕ) : ℝ :=
  ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
    (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)

/-- Helper for Theorem 7.27: the critical profile equals a positive scalar
multiple of `Real.negMulLog` along the positive branch. -/
private lemma criticalProfile_eq_scaled_negMulLog
    (h_p : 1 < p) {β : ℝ} (hβ : 0 < β) :
    criticalProfile p β =
      (p / (2 * p + 1)) * Real.negMulLog (β ^ ((2 * p + 1) / p)) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hden_ne : 2 * p + 1 ≠ 0 := by
    linarith
  -- Rewrite the logarithm of the powered branch and cancel the scalar factor once.
  calc
    criticalProfile p β
        = -(β ^ ((2 * p + 1) / p) * Real.log β) := by
            rw [criticalProfile]
    _ = -(β ^ ((2 * p + 1) / p)) * Real.log β := by
          ring
    _ = (p / (2 * p + 1)) *
          (-(β ^ ((2 * p + 1) / p)) * Real.log (β ^ ((2 * p + 1) / p))) := by
            rw [Real.log_rpow hβ]
            field_simp [hp_ne, hden_ne]
    _ = (p / (2 * p + 1)) * Real.negMulLog (β ^ ((2 * p + 1) / p)) := by
          rfl

/-- Helper for Theorem 7.27: the small-branch cutoff is sent to `exp (-1)` by
the critical profile exponent. -/
private lemma criticalProfileUpper_rpow_eq
    (h_p : 1 < p) :
    Real.exp (-(p / (2 * p + 1))) ^ ((2 * p + 1) / p) = Real.exp (-1) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hden_ne : 2 * p + 1 ≠ 0 := by
    linarith
  have hmul :
      (-(p / (2 * p + 1)) : ℝ) * ((2 * p + 1) / p) = -1 := by
    field_simp [hp_ne, hden_ne]
  rw [← Real.exp_mul, hmul]

/-- Helper for Theorem 7.27: the critical profile endpoint value on the small
branch is explicit and strictly positive. -/
private lemma criticalProfileUpper_value
    (h_p : 1 < p) :
    criticalProfile p (Real.exp (-(p / (2 * p + 1)))) =
      (p / (2 * p + 1)) * Real.exp (-1) := by
  rw [criticalProfile_eq_scaled_negMulLog h_p (criticalProfileUpper_pos p)]
  rw [criticalProfileUpper_rpow_eq h_p]
  simp [Real.negMulLog_def]

/-- Helper for Theorem 7.27: the explicit endpoint value of the critical
profile is strictly positive. -/
private lemma criticalProfileUpper_value_pos
    (h_p : 1 < p) :
    0 < criticalProfile p (Real.exp (-(p / (2 * p + 1)))) := by
  have h_p0 : 0 < p := by
    linarith
  have h_den : 0 < 2 * p + 1 := by
    linarith
  rw [criticalProfileUpper_value h_p]
  exact mul_pos (div_pos h_p0 h_den) (Real.exp_pos _)

/-- Helper for Theorem 7.27: on the positive small branch, the critical
logarithmic profile is strictly increasing. -/
private lemma criticalProfile_strictMonoOn_smallBranch
    (h_p : 1 < p) :
    StrictMonoOn (criticalProfile p) (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) := by
  have h_exp_pos : 0 < ((2 * p + 1) / p : ℝ) :=
    criticalProfileExponent_pos h_p
  have h_scale_pos : 0 < p / (2 * p + 1) := by
    have h_p0 : 0 < p := by
      linarith
    have h_den : 0 < 2 * p + 1 := by
      linarith
    exact div_pos h_p0 h_den
  have h_negMulLog_mono :
      StrictMonoOn Real.negMulLog (Set.Icc (0 : ℝ) (Real.exp (-1))) := by
    refine strictMonoOn_of_deriv_pos (D := Set.Icc (0 : ℝ) (Real.exp (-1)))
      (convex_Icc _ _) Real.continuous_negMulLog.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx_pos : 0 < x := hx.1
    have hx_lt : x < Real.exp (-1) := hx.2
    -- The derivative is `-log x - 1`, which is positive exactly before `exp (-1)`.
    rw [Real.deriv_negMulLog hx_pos.ne']
    have hlog_lt : Real.log x < -1 :=
      (Real.log_lt_iff_lt_exp hx_pos).2 hx_lt
    linarith
  have h_rpow_mono :
      StrictMonoOn (fun β : ℝ ↦ β ^ ((2 * p + 1) / p))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) := by
    intro x hx y hy hxy
    exact Real.rpow_lt_rpow hx.1.le hxy h_exp_pos
  have h_rpow_maps :
      Set.MapsTo
        (fun β : ℝ ↦ β ^ ((2 * p + 1) / p))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1)))))
        (Set.Icc (0 : ℝ) (Real.exp (-1))) := by
    intro β hβ
    refine ⟨le_of_lt (Real.rpow_pos_of_pos hβ.1 _), ?_⟩
    have hβ_le :
        β ^ ((2 * p + 1) / p) ≤
          Real.exp (-(p / (2 * p + 1))) ^ ((2 * p + 1) / p) := by
      exact Real.rpow_le_rpow hβ.1.le hβ.2 h_exp_pos.le
    simpa [criticalProfileUpper_rpow_eq h_p] using hβ_le
  have h_comp :
      StrictMonoOn
        (fun β : ℝ ↦ Real.negMulLog (β ^ ((2 * p + 1) / p)))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) :=
    h_negMulLog_mono.comp h_rpow_mono h_rpow_maps
  intro x hx y hy hxy
  -- Rewrite the critical profile through `negMulLog`, then use the positive scalar factor.
  rw [criticalProfile_eq_scaled_negMulLog h_p hx.1,
    criticalProfile_eq_scaled_negMulLog h_p hy.1]
  exact mul_lt_mul_of_pos_left (h_comp hx hy hxy) h_scale_pos

/-- Helper for Theorem 7.27: the critical profile is positive on the positive
small branch. -/
private lemma criticalProfile_pos_of_mem_smallBranch
    (h_p : 1 < p) {β : ℝ}
    (hβ_pos : 0 < β)
    (hβ_le : β ≤ Real.exp (-(p / (2 * p + 1)))) :
    0 < criticalProfile p β := by
  have hβ_lt_one : β < 1 := by
    exact lt_of_le_of_lt hβ_le (criticalProfileUpper_lt_one h_p)
  have hpow_pos : 0 < β ^ ((2 * p + 1) / p) := by
    exact Real.rpow_pos_of_pos hβ_pos _
  have hlog_neg : Real.log β < 0 := by
    exact Real.log_neg hβ_pos hβ_lt_one
  have hprod_neg : β ^ ((2 * p + 1) / p) * Real.log β < 0 :=
    mul_neg_of_pos_of_neg hpow_pos hlog_neg
  simpa [criticalProfile] using neg_pos.mpr hprod_neg

/-- Helper for Theorem 7.27: the critical profile is continuous on every
closed interval bounded away from `0`. -/
private lemma criticalProfile_continuousOn_Icc
    {p l u : ℝ} (hl : 0 < l) :
    ContinuousOn (criticalProfile p) (Set.Icc l u) := by
  have hpow :
      ContinuousOn (fun x : ℝ ↦ x ^ ((2 * p + 1) / p)) (Set.Icc l u) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hl hx.1
    exact (continuousAt_id.rpow_const (Or.inl hx_pos.ne')).continuousWithinAt
  have hlog : ContinuousOn Real.log (Set.Icc l u) := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    exact (lt_of_lt_of_le hl hx.1).ne'
  have hmul :
      ContinuousOn (fun x : ℝ ↦ -(x ^ ((2 * p + 1) / p) * Real.log x)) (Set.Icc l u) :=
    (hpow.mul hlog).neg
  intro x hx
  change ContinuousWithinAt (fun x : ℝ ↦ -(x ^ ((2 * p + 1) / p) * Real.log x))
    (Set.Icc l u) x
  simpa using hmul x hx

/-- Helper for Theorem 7.27: dividing the critical profile by the input leaves
the vanishing positive-branch factor `-log x * x^((p + 1) / p)`. -/
private lemma criticalProfile_div_self_tendsto_zero
    (h_p : 1 < p) :
    Filter.Tendsto
      (fun x : ℝ ↦ criticalProfile p x / x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- Route correction: the remaining critical support proof needs this
  -- normalized small-branch asymptotic to show `criticalProfile (rhs_n) < rhs_n`
  -- for large `n`.
  have h_exp_pos : 0 < ((p + 1) / p : ℝ) := by
    have h_p0 : 0 < p := by
      linarith
    exact div_pos (by linarith) h_p0
  have h_log :
      Filter.Tendsto
        (fun x : ℝ ↦ Real.log x * x ^ ((p + 1) / p))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero h_exp_pos
  have h_rewrite :
      (fun x : ℝ ↦ criticalProfile p x / x) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun x : ℝ ↦ -(Real.log x * x ^ ((p + 1) / p))) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hp_ne : p ≠ 0 := by
      linarith
    have h_exp :
        (((2 * p + 1) / p : ℝ) - 1) = (p + 1) / p := by
      field_simp [hp_ne]
      ring
    -- Rewrite the normalized profile to the exact logarithmic-power shape
    -- used by the mathlib limit theorem.
    calc
      criticalProfile p x / x
          = -(x ^ ((2 * p + 1) / p) * Real.log x) / x := by
              rw [criticalProfile]
      _ = -((x ^ ((2 * p + 1) / p) * Real.log x) / x) := by
            rw [neg_div]
      _ = -((x ^ ((2 * p + 1) / p) / x) * Real.log x) := by
            congr 1
            field_simp [hx_ne]
      _ = -(x ^ (((2 * p + 1) / p : ℝ) - 1) * Real.log x) := by
            rw [← Real.rpow_sub_one hx_ne ((2 * p + 1) / p)]
      _ = -(Real.log x * x ^ (((2 * p + 1) / p : ℝ) - 1)) := by
            congr 1
            ac_rfl
      _ = -(Real.log x * x ^ ((p + 1) / p)) := by
            rw [h_exp]
  -- After the normalization, the desired limit is exactly the negated
  -- logarithmic-power asymptotic.
  refine Filter.Tendsto.congr' h_rewrite.symm ?_
  simpa using h_log.neg

/-- Helper for Theorem 7.27: on the positive branch close to `0`, the critical
profile lies strictly below the identity. -/
private lemma criticalProfile_lt_self_eventually_small
    (h_p : 1 < p) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), criticalProfile p x < x := by
  have h_ratio_lt_one :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), criticalProfile p x / x < 1 := by
    exact (criticalProfile_div_self_tendsto_zero h_p).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h_ratio_lt_one, eventually_mem_nhdsWithin] with x hx_ratio hx_pos
  -- Multiply the normalized inequality by the positive input to recover the
  -- pointwise small-branch estimate.
  have hx : criticalProfile p x < 1 * x := by
    exact (div_lt_iff₀ hx_pos).mp hx_ratio
  simpa using hx

/-- Helper for Theorem 7.27: a right-hand side value on the small branch has a
least positive critical-profile root, found by IVT and then identified by
small-branch strict monotonicity. -/
private lemma smallBranchRoot_exists_and_least
    (h_p : 1 < p) {r : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_upper : r < Real.exp (-(p / (2 * p + 1))))
    (hleft : criticalProfile p r < r)
    (hright : r < criticalProfile p (Real.exp (-(p / (2 * p + 1))))) :
    ∃ β, r ≤ β ∧
      β ≤ Real.exp (-(p / (2 * p + 1))) ∧
      criticalProfile p β = r ∧
      ∀ z > 0, criticalProfile p z = r → β ≤ z := by
  have h_interval :
      r ≤ Real.exp (-(p / (2 * p + 1))) :=
    le_of_lt hr_lt_upper
  have h_cont :
      ContinuousOn (criticalProfile p)
        (Set.Icc r (Real.exp (-(p / (2 * p + 1))))) :=
    criticalProfile_continuousOn_Icc (p := p)
      (u := Real.exp (-(p / (2 * p + 1)))) hr_pos
  have h_target :
      r ∈ Set.Icc
        (criticalProfile p r)
        (criticalProfile p (Real.exp (-(p / (2 * p + 1))))) := by
    exact ⟨le_of_lt hleft, le_of_lt hright⟩
  -- Use IVT on the closed interval `[r, upper]` to construct a same-index root.
  rcases intermediate_value_Icc h_interval h_cont h_target with ⟨β, hβIcc, hβeq⟩
  have hβ_pos : 0 < β := lt_of_lt_of_le hr_pos hβIcc.1
  have hβ_lt_upper : β < Real.exp (-(p / (2 * p + 1))) := by
    have hβ_ne :
        β ≠ Real.exp (-(p / (2 * p + 1))) := by
      intro h_eq
      rw [h_eq] at hβeq
      linarith
    exact lt_of_le_of_ne hβIcc.2 hβ_ne
  refine ⟨β, hβIcc.1, hβIcc.2, hβeq, ?_⟩
  intro z hz_pos hz_eq
  by_cases hz_upper : z ≤ Real.exp (-(p / (2 * p + 1)))
  · have hz_lt_upper : z < Real.exp (-(p / (2 * p + 1))) := by
      have hz_ne :
          z ≠ Real.exp (-(p / (2 * p + 1))) := by
        intro h_eq
        rw [h_eq] at hz_eq
        linarith
      exact lt_of_le_of_ne hz_upper hz_ne
    have hβ_mem :
        β ∈ Set.Ioc 0 (Real.exp (-(p / (2 * p + 1)))) :=
      ⟨hβ_pos, hβIcc.2⟩
    have hz_mem :
        z ∈ Set.Ioc 0 (Real.exp (-(p / (2 * p + 1)))) :=
      ⟨hz_pos, hz_upper⟩
    by_contra hβz
    have hz_lt_β : z < β := lt_of_not_ge hβz
    have hlt :
        criticalProfile p z < criticalProfile p β :=
      criticalProfile_strictMonoOn_smallBranch h_p hz_mem hβ_mem hz_lt_β
    rw [hz_eq, hβeq] at hlt
    exact lt_irrefl _ hlt
  · exact le_of_lt (lt_of_le_of_lt hβIcc.2 (lt_of_not_ge hz_upper))

/-- Helper for Theorem 7.27: the nat-indexed critical root-equation right-hand
side tends to `0`. -/
private lemma betaDiscrepRootRhsNat_tendsto_zero
    (b c p σ : ℝ) :
    Filter.Tendsto (betaDiscrepRootRhsNat b c p σ) Filter.atTop (nhds 0) := by
  let coeff : ℝ :=
    σ ^ 2 * (b⁻¹ * c ^ ((p + 1) / p) * p *
      (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0))
  have hcoeff :
      betaDiscrepRootRhsNat b c p σ =
        fun n : ℕ ↦ coeff / (n : ℝ) := by
    funext n
    simp [betaDiscrepRootRhsNat, coeff, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- The benchmark right-hand side is a fixed constant divided by `n`.
  rw [hcoeff]
  exact tendsto_const_div_atTop_nhds_zero_nat coeff

/-- Helper for Theorem 7.27: the positive-index owner `betaDiscrepAt` enters
the source logarithmic root set beyond a finite prefix of data sizes. This is
the benchmark API actually needed by the critical asymptotic branch, which may
discard finitely many small indices. -/
theorem betaDiscrepAt_spec_largeIndex
    (b c p σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∃ N : ℕ, ∀ n : ℕ+, N ≤ (n : ℕ) →
      0 < betaDiscrepAt b c p σ n ∧
        betaDiscrepAt b c p σ n ≤ Real.exp (-(p / (2 * p + 1))) ∧
        BetaDiscrepRootEquation b c p σ n (betaDiscrepAt b c p σ n) := by
  -- Route correction: the support layer now owns the small-branch profile API
  -- (`criticalProfile_strictMonoOn_smallBranch`, endpoint positivity, and the
  -- normalized profile shape). The remaining blocker is the witness-to-`sInf`
  -- transport: construct the large-index IVT witness on `[rhs_n, upper]`,
  -- then use small-branch minimality to identify it with `betaDiscrepAt`.
  let rhs : ℕ → ℝ := betaDiscrepRootRhsNat b c p σ
  have h_rhs_tendsto : Filter.Tendsto rhs Filter.atTop (nhds 0) := by
    simpa [rhs] using betaDiscrepRootRhsNat_tendsto_zero b c p σ
  have h_rhs_pos :
      ∀ᶠ m : ℕ in Filter.atTop, 0 < rhs m := by
    filter_upwards [Filter.Ici_mem_atTop 1] with m hm
    have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    simpa [rhs, betaDiscrepRootRhsNat] using
      (betaDiscrepRootEquation_rhs_pos h_b h_c h_p h_σ ⟨m, hm_pos⟩)
  have h_rhs_within :
      Filter.Tendsto rhs Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    refine (tendsto_nhdsWithin_iff).2 ?_
    exact ⟨h_rhs_tendsto, h_rhs_pos⟩
  have h_rhs_lt_upper :
      ∀ᶠ m : ℕ in Filter.atTop,
        rhs m < Real.exp (-(p / (2 * p + 1))) := by
    exact h_rhs_tendsto.eventually
      (Iio_mem_nhds (criticalProfileUpper_pos p))
  have h_rhs_lt_self :
      ∀ᶠ m : ℕ in Filter.atTop, criticalProfile p (rhs m) < rhs m := by
    exact h_rhs_within.eventually (criticalProfile_lt_self_eventually_small h_p)
  have h_rhs_lt_upperValue :
      ∀ᶠ m : ℕ in Filter.atTop,
        rhs m < criticalProfile p (Real.exp (-(p / (2 * p + 1)))) := by
    exact h_rhs_tendsto.eventually
      (Iio_mem_nhds (criticalProfileUpper_value_pos h_p))
  have h_all :
      ∀ᶠ m : ℕ in Filter.atTop,
        0 < rhs m ∧
          rhs m < Real.exp (-(p / (2 * p + 1))) ∧
          criticalProfile p (rhs m) < rhs m ∧
          rhs m < criticalProfile p (Real.exp (-(p / (2 * p + 1)))) := by
    filter_upwards [h_rhs_pos, h_rhs_lt_upper, h_rhs_lt_self, h_rhs_lt_upperValue] with
      m hpos hupper hself hvalue
    exact ⟨hpos, hupper, hself, hvalue⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_all
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN (n : ℕ) hn with ⟨hr_pos, hr_lt_upper, hleft, hright⟩
  rcases smallBranchRoot_exists_and_least h_p hr_pos hr_lt_upper hleft hright with
    ⟨β, hβ_lower, hβ_upper, hβeq, hβ_least⟩
  let rootSet : Set ℝ := {z : ℝ | 0 < z ∧ BetaDiscrepRootEquation b c p σ n z}
  have hβ_root : BetaDiscrepRootEquation b c p σ n β := by
    -- Repackage the IVT witness as a point of the displayed root equation.
    simpa [criticalProfile, rhs, betaDiscrepRootRhsNat, BetaDiscrepRootEquation] using hβeq
  have hβ_pos : 0 < β := lt_of_lt_of_le hr_pos hβ_lower
  have hβ_mem : β ∈ rootSet := by
    exact ⟨hβ_pos, hβ_root⟩
  have hroot_nonempty : rootSet.Nonempty := ⟨β, hβ_mem⟩
  have hroot_bddBelow : BddBelow rootSet := ⟨0, fun z hz ↦ hz.1.le⟩
  have hβ_lowerBound : ∀ z ∈ rootSet, β ≤ z := by
    intro z hz
    exact hβ_least z hz.1 (by
      simpa [criticalProfile, rhs, betaDiscrepRootRhsNat, BetaDiscrepRootEquation] using hz.2)
  have hsInf_eq : sInf rootSet = β := by
    apply le_antisymm
    · exact csInf_le hroot_bddBelow hβ_mem
    · exact le_csInf hroot_nonempty hβ_lowerBound
  refine ⟨?_, ?_, ?_⟩
  · -- The least positive root inherits positivity from the constructed witness.
    rw [betaDiscrepAt_def, hsInf_eq]
    exact hβ_pos
  · -- The least positive root remains on the small branch.
    rw [betaDiscrepAt_def, hsInf_eq]
    exact hβ_upper
  · -- Finally identify `betaDiscrepAt` with the same-index IVT witness.
    rw [betaDiscrepAt_def, hsInf_eq]
    exact hβ_root

/-- Helper for Theorem 7.27: the nat-indexed benchmark `betaDiscrep` agrees
with the positive root equation beyond a finite prefix. -/
theorem betaDiscrep_spec_largeIndex
    (b c p σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∃ N : ℕ, ∀ n : ℕ+, N ≤ (n : ℕ) →
      0 < betaDiscrep b c p σ n ∧
        betaDiscrep b c p σ n ≤ Real.exp (-(p / (2 * p + 1))) ∧
        BetaDiscrepRootEquation b c p σ n (betaDiscrep b c p σ n) := by
  rcases betaDiscrepAt_spec_largeIndex b c p σ h_b h_c h_p h_σ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  -- Repackage the positive-index owner through `betaDiscrep_eq_betaDiscrepAt`.
  have hEq : betaDiscrep b c p σ n = betaDiscrepAt b c p σ n :=
    betaDiscrep_eq_betaDiscrepAt b c p σ n
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq] using (hN n hn).1
  · simpa [hEq] using (hN n hn).2.1
  · simpa [hEq] using (hN n hn).2.2

/-- Helper for Theorem 7.27: the canonical benchmark `betaDiscrep` is
eventually positive, which is the only positivity input needed by the critical
asymptotic comparison. -/
theorem betaDiscrep_eventually_pos
    (b c p σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < betaDiscrep b c p σ n := by
  rcases betaDiscrep_spec_largeIndex b c p σ h_b h_c h_p h_σ with ⟨N, hN⟩
  filter_upwards [Filter.Ici_mem_atTop (max N 1)] with n hn
  have hbound : max N 1 ≤ n := by
    simpa using hn
  have hn_pos : 0 < n := by
    exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right N 1) hbound)
  exact (hN ⟨n, hn_pos⟩ (le_trans (Nat.le_max_left N 1) hbound)).1

/-- The canonical benchmark `betaDiscrep` tends to `0` as `n → ∞`. -/
theorem betaDiscrep_tendsto_zero
    (b c p σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    Filter.Tendsto (betaDiscrep b c p σ) Filter.atTop (nhds 0) := by
  -- Route correction: once `betaDiscrepAt_spec_largeIndex` exports the same-index
  -- small-branch root owner, the zero-limit proof reduces to a fixed `ε` barrier:
  -- compare `criticalProfile ε₀` against the vanishing right-hand side and use
  -- small-branch monotonicity to force `betaDiscrep n < ε₀`.
  let upper : ℝ := Real.exp (-(p / (2 * p + 1)))
  let rhs : ℕ → ℝ := betaDiscrepRootRhsNat b c p σ
  have h_rhs_tendsto : Filter.Tendsto rhs Filter.atTop (nhds 0) := by
    simpa [rhs] using betaDiscrepRootRhsNat_tendsto_zero b c p σ
  rcases betaDiscrep_spec_largeIndex b c p σ h_b h_c h_p h_σ with ⟨N, hN⟩
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let ε₀ : ℝ := min (ε / 2) (upper / 2)
  have hupper_pos : 0 < upper := by
    simpa [upper] using criticalProfileUpper_pos p
  have hε₀_pos : 0 < ε₀ := by
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hε₀_lt_ε : ε₀ < ε := by
    have hhalf_lt : ε / 2 < ε := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have hε₀_le_upper : ε₀ ≤ upper := by
    have hε₀_le_half : ε₀ ≤ upper / 2 := min_le_right _ _
    linarith
  have hε₀_lt_upper : ε₀ < upper := by
    have hhalf_lt_upper : upper / 2 < upper := by
      linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt_upper
  have hε₀_profile_pos : 0 < criticalProfile p ε₀ :=
    criticalProfile_pos_of_mem_smallBranch h_p hε₀_pos hε₀_le_upper
  have h_rhs_lt_target :
      ∀ᶠ m : ℕ in Filter.atTop, rhs m < criticalProfile p ε₀ := by
    exact h_rhs_tendsto.eventually (Iio_mem_nhds hε₀_profile_pos)
  have h_rhs_lt_upperValue :
      ∀ᶠ m : ℕ in Filter.atTop, rhs m < criticalProfile p upper := by
    exact h_rhs_tendsto.eventually
      (Iio_mem_nhds (by simpa [upper] using criticalProfileUpper_value_pos h_p))
  filter_upwards [Filter.Ici_mem_atTop (max N 1), h_rhs_lt_target, h_rhs_lt_upperValue] with
    m hm htarget hupperVal
  have hmN : N ≤ m := le_trans (Nat.le_max_left N 1) hm
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right N 1) hm)
  have hspec := hN ⟨m, hm_pos⟩ hmN
  rcases hspec with ⟨hβ_pos, hβ_le_upper, hβ_root⟩
  have hβ_root_rhs :
      criticalProfile p (betaDiscrep b c p σ m) = rhs m := by
    -- Rewrite the public root equation back to the private profile notation.
    simpa [rhs, upper, betaDiscrepRootRhsNat, criticalProfile, BetaDiscrepRootEquation] using hβ_root
  have hβ_lt_upper : betaDiscrep b c p σ m < upper := by
    have hβ_ne_upper : betaDiscrep b c p σ m ≠ upper := by
      intro h_eq
      rw [h_eq] at hβ_root_rhs
      exact (lt_irrefl _) (hupperVal.trans_eq hβ_root_rhs)
    exact lt_of_le_of_ne hβ_le_upper hβ_ne_upper
  have hβ_le_target : betaDiscrep b c p σ m ≤ ε₀ := by
    by_contra h_not_le
    have htarget_lt_beta : ε₀ < betaDiscrep b c p σ m := lt_of_not_ge h_not_le
    have hlt :
        criticalProfile p ε₀ < criticalProfile p (betaDiscrep b c p σ m) :=
      criticalProfile_strictMonoOn_smallBranch h_p
        ⟨hε₀_pos, hε₀_le_upper⟩
        ⟨hβ_pos, hβ_le_upper⟩
        htarget_lt_beta
    rw [hβ_root_rhs] at hlt
    exact (lt_irrefl _) (hlt.trans htarget)
  have hβ_lt_ε : betaDiscrep b c p σ m < ε := lt_of_le_of_lt hβ_le_target hε₀_lt_ε
  -- Convert the positive upper bound into the metric neighborhood inequality.
  have hβ_nonneg : 0 ≤ betaDiscrep b c p σ m := le_of_lt hβ_pos
  have hdist :
      dist (betaDiscrep b c p σ m) 0 = betaDiscrep b c p σ m := by
    calc
      dist (betaDiscrep b c p σ m) 0 = |betaDiscrep b c p σ m - 0| := by
        rw [Real.dist_eq]
      _ = |betaDiscrep b c p σ m| := by simp
      _ = betaDiscrep b c p σ m := abs_of_nonneg hβ_nonneg
  rw [hdist]
  exact hβ_lt_ε

/-- A benchmark sequence is a discrepancy-side critical benchmark when it
satisfies the displayed logarithmic root equation from Theorem 7.27 at every
positive data size. -/
@[expose]
def IsCriticalBenchmark (b c p σ : ℝ) (betaDiscrep : ℕ → ℝ) : Prop :=
  ∀ n : ℕ+, BetaDiscrepRootEquation b c p σ n (betaDiscrep n)

/-- The defining pointwise characterization of `IsCriticalBenchmark`. -/
theorem isCriticalBenchmark_iff
    (b c p σ : ℝ) (betaDiscrep : ℕ → ℝ) :
    IsCriticalBenchmark b c p σ betaDiscrep ↔
      ∀ n : ℕ+, BetaDiscrepRootEquation b c p σ n (betaDiscrep n) := by
  -- The benchmark owner is definitionally pointwise.
  rfl

end TikhonovDiscrepancy
