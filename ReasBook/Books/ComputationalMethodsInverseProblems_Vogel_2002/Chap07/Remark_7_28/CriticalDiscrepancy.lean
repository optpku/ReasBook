/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_28.CriticalProfile
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Benchmark

public section

open scoped Asymptotics

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

omit [CompleteSpace H] [CompleteSpace F] in
/-- Helper for Remark 7.28: unpack the discrepancy-family owner at a positive
index so the critical argument can work pointwise with `(7.90)`. -/
lemma discrepancyParameterFamilySpec_local
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (n : ℕ+) :
    0 ≤ alphaDiscrep n ∧
      IsTikhonovDiscrepancyParameter K d Rtikh σ n (alphaDiscrep n) := by
  -- The family owner is definitionally the pointwise nonnegativity and
  -- discrepancy equation pair.
  simpa [IsTikhonovDiscrepancyParameterFamily] using h_alphaDiscrep n

/-- Helper for Remark 7.28: the canonical critical benchmark is eventually
nonzero, so the ratio-to-one equivalence bridge is available. -/
lemma betaDiscrep_eventually_ne
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∀ᶠ n : ℕ in Filter.atTop, betaDiscrep b c p σ n ≠ 0 := by
  -- Convert the public eventual-positivity result into the nonzero hypothesis
  -- required by `Asymptotics.isEquivalent_iff_tendsto_one`.
  exact
    (betaDiscrep_eventually_pos b c p σ h_b h_c h_p h_σ).mono
      (fun _ hn ↦ ne_of_gt hn)

/-- Helper for Remark 7.28: beyond a finite prefix, the public critical
benchmark lies on the theorem-local small branch and satisfies the local
critical-profile equation. -/
lemma betaDiscrep_eventually_smallBranch_and_profile_local
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_σ : 0 < σ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < betaDiscrep b c p σ n ∧
        betaDiscrep b c p σ n ≤ Real.exp (-(p / (2 * p + 1))) ∧
        criticalProfileLocal p (betaDiscrep b c p σ n) =
          ((σ ^ 2) / (n : ℝ)) * b⁻¹ * c ^ ((p + 1) / p) * p *
            (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) := by
  rcases betaDiscrep_spec_largeIndex b c p σ h_b h_c h_p h_σ with ⟨N, hN⟩
  filter_upwards [Filter.Ici_mem_atTop (max N 1)] with n hn
  have hN_bound : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right N 1) hn)
  rcases hN ⟨n, hn_pos⟩ hN_bound with ⟨hbeta_pos, hbeta_upper, hbeta_root⟩
  refine ⟨hbeta_pos, hbeta_upper, ?_⟩
  simpa [criticalProfileLocal_def, BetaDiscrepRootEquation] using hbeta_root

/-- Helper for Remark 7.28: reduce the critical discrepancy comparison to the
normalized ratio `alphaDiscrep / betaDiscrep`. -/
lemma criticalRatio_tendsto_one_of_isEquivalent_local
    (h_beta_ne :
      ∀ᶠ n : ℕ in Filter.atTop, betaDiscrep b c p σ n ≠ 0)
    (h_equiv :
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep (betaDiscrep b c p σ)) :
    Filter.Tendsto
      (fun n ↦ alphaDiscrep n / betaDiscrep b c p σ n)
      Filter.atTop
      (nhds 1) := by
  -- Rewrite the asymptotic equivalence through mathlib's ratio criterion.
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne] at h_equiv
  -- The criterion already produces the exact ratio map used in this local file.
  simpa [Pi.div_apply] using
    (show
      Filter.Tendsto
        (fun n ↦ (alphaDiscrep / betaDiscrep b c p σ) n)
        Filter.atTop
        (nhds 1) from h_equiv)

/-- Helper for Remark 7.28: reduce the critical discrepancy comparison to the
normalized ratio `alphaDiscrep / betaDiscrep`. -/
theorem criticalRatio_tendsto_one_local
    (h_standing :
      FilterRegularization.StandingAssumptions
        K S h_length fTrue c p b q d η
        (fun n ↦ Rtikh n (alphaDiscrep n)) alphaDiscrep)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_alphaDiscrep :
      IsTikhonovDiscrepancyParameterFamily K d Rtikh σ alphaDiscrep)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_critical : p - q = -1) :
    Filter.Tendsto
      (fun n ↦ alphaDiscrep n / betaDiscrep b c p σ n)
      Filter.atTop
      (nhds 1) := by
  have h_beta_ne :
      ∀ᶠ n : ℕ in Filter.atTop, betaDiscrep b c p σ n ≠ 0 :=
    -- The final ratio criterion requires only eventual benchmark nonvanishing.
    betaDiscrep_eventually_ne b c p σ h_b h_c h_p h_σ
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop alphaDiscrep (betaDiscrep b c p σ) := by
    -- Route correction: reuse the already formalized critical discrepancy
    -- benchmark theorem, then repackage that equivalence as the local ratio
    -- limit needed by Remark 7.28.
    exact
      TikhonovDiscrepancy.isEquivalent_critical
        K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
        h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_critical
  -- Once the asymptotic equivalence is available, repackage it as the ratio limit.
  exact
    criticalRatio_tendsto_one_of_isEquivalent_local
      (b := b) (c := c) (p := p) (σ := σ) (alphaDiscrep := alphaDiscrep)
      h_beta_ne h_equiv

/-- Helper for Remark 7.28: once the normalized critical ratio tends to `1`,
the discrepancy family is asymptotically equivalent to the canonical critical
benchmark. -/
theorem discrepancyFamily_isEquivalent_criticalBenchmark_local
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
  have h_beta_ne :
      ∀ᶠ n : ℕ in Filter.atTop, betaDiscrep b c p σ n ≠ 0 :=
    -- The benchmark is eventually positive, hence suitable for the ratio criterion.
    betaDiscrep_eventually_ne b c p σ h_b h_c h_p h_σ
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne]
  -- Switch the pointwise division produced by the criterion to the explicit
  -- ratio function used by the local support theorem.
  change
    Filter.Tendsto
      (fun n ↦ alphaDiscrep n / betaDiscrep b c p σ n)
      Filter.atTop
      (nhds 1)
  -- Delegate the remaining work to the theorem-local ratio limit interface.
  exact
    criticalRatio_tendsto_one_local
      K S h_length fTrue b c p q σ d η Rtikh alphaDiscrep
      h_standing h_tikhonov h_alphaDiscrep h_b h_c h_p h_q h_σ h_critical

end

end TikhonovDiscrepancy
