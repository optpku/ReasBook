/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_1
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5.SpectralRepresentation
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7.OptimalFamily
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_8
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_4
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.WhiteNoise
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_10.Filters
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.AsymptoticOptimalBridge
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_23.PredictiveRisk
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_29.ExpectedObjective
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_29.QuadratureProfile
import Mathlib.Analysis.MeanInequalities

section

open scoped Matrix

universe u

noncomputable section

namespace TikhonovGcv

private lemma sum_Icc_one_eq_sumRangeShift_local
    {α : Type _} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1)
  | n => by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

private lemma quadratureSum_eq_sumRangeSeries_local
    (p : ℝ) (j : ℕ) (s : ℝ) (n : ℕ) (h : ℝ) :
    KernelMoment.quadratureSum p j s n h =
      ∑ k ∈ Finset.range n, h * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h) := by
  rw [KernelMoment.quadratureSum_def, Finset.mul_sum, sum_Icc_one_eq_sumRangeShift_local]

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ∀ n : ℕ, Matrix (Fin n.succ) (Fin n.succ) ℝ)
variable (U V : ∀ n : ℕ, Matrix (Fin n.succ) (Fin n.succ) ℝ)
variable (s : ∀ n : ℕ, Fin n.succ → ℝ)
variable (R : ∀ n : ℕ, ℝ → Matrix (Fin n.succ) (Fin n.succ) ℝ)
variable (fTrue : ∀ n : ℕ, EuclideanSpace ℝ (Fin n.succ))
variable (η : ∀ n : ℕ, Ω → EuclideanSpace ℝ (Fin n.succ))
variable (b c p q σ : ℝ)

/-- Helper for Theorem 7.29: reuse the earlier Chapter 7 bridge from
`Asymptotics.IsEquivalent` to `ParameterChoice.IsAsymptoticallyOptimal`. -/
lemma parameterChoiceIsAsymptoticallyOptimalOfIsEquivalentLocal
    {α αopt : ℕ → ℝ}
    (h : Asymptotics.IsEquivalent Filter.atTop α αopt) :
    ParameterChoice.IsAsymptoticallyOptimal α αopt := by
  -- Route correction: reuse the existing owner-level bridge instead of
  -- fighting the hidden wrapper inside a `module` file.
  exact parameterChoiceIsAsymptoticallyOptimalOfIsEquivalent h

/-- Helper for Theorem 7.29: the kernel moment `I_{p,3}^s` is positive under
the Proposition 7.20 admissibility inequalities used by the predictive-risk
benchmark. -/
lemma kernelMomentIntegralPos_j3
    {p s : ℝ}
    (h_p : 0 < p) (h_s : 0 < s + 1) (h_decay : 0 < 3 * p - s - 1) :
    0 < KernelMoment.integral p 3 s := by
  -- Rewrite the kernel moment to the gamma-ratio formula and check each factor
  -- is positive.
  rw [@KernelMoment.integral_eq_gamma_mul_gamma_div_factorial p s 3 h_s h_decay]
  refine div_pos ?_ ?_
  · refine mul_pos ?_ ?_
    · exact Real.Gamma_pos_of_pos (div_pos h_decay h_p)
    · exact Real.Gamma_pos_of_pos (div_pos h_s h_p)
  · positivity

/-- Helper for Theorem 7.29: the weighted predictive-risk bracket is bounded
below by `q`. -/
lemma predictiveObjectiveBracket_ge
    {p q t : ℝ}
    (h_p : 0 < p) (h_q : 1 < q) (h_t : 0 < t) :
    q ≤ t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) := by
  have hq_pos : 0 < q := by
    linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hp_ne : p ≠ 0 := ne_of_gt h_p
  have hw :
      (1 / q) + ((q - 1) / q) = 1 := by
    field_simp [hq_ne]
    linarith
  have hgeom_one :
      (t ^ ((q - 1) / p)) ^ (1 / q) * (t ^ (-(1 / p))) ^ ((q - 1) / q) = 1 := by
    rw [← Real.rpow_mul h_t.le ((q - 1) / p) (1 / q)]
    rw [← Real.rpow_mul h_t.le (-(1 / p)) ((q - 1) / q)]
    rw [← Real.rpow_add h_t]
    have hexp :
        ((q - 1) / p) * (1 / q) + (-(1 / p)) * ((q - 1) / q) = 0 := by
      field_simp [hp_ne, hq_ne]
      ring
    rw [hexp, Real.rpow_zero]
  have hweighted :
      1 ≤
        (1 / q) * t ^ ((q - 1) / p) +
          ((q - 1) / q) * t ^ (-(1 / p)) := by
    have hgm :
        (t ^ ((q - 1) / p)) ^ (1 / q) * (t ^ (-(1 / p))) ^ ((q - 1) / q) ≤
          (1 / q) * t ^ ((q - 1) / p) + ((q - 1) / q) * t ^ (-(1 / p)) :=
      Real.geom_mean_le_arith_mean2_weighted
        (show 0 ≤ 1 / q by positivity)
        (show 0 ≤ (q - 1) / q by positivity)
        (show 0 ≤ t ^ ((q - 1) / p) by positivity)
        (show 0 ≤ t ^ (-(1 / p)) by positivity)
        hw
    calc
      1
          = (t ^ ((q - 1) / p)) ^ (1 / q) * (t ^ (-(1 / p))) ^ ((q - 1) / q) := by
              exact hgeom_one.symm
      _ ≤
          (1 / q) * t ^ ((q - 1) / p) +
            ((q - 1) / q) * t ^ (-(1 / p)) := hgm
  -- Multiply the weighted inequality by `q` to recover the Chapter 7 bracket.
  calc
    q = q * 1 := by ring
    _ ≤
        q *
          ((1 / q) * t ^ ((q - 1) / p) +
            ((q - 1) / q) * t ^ (-(1 / p))) :=
      mul_le_mul_of_nonneg_left hweighted (le_of_lt hq_pos)
    _ = t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) := by
      field_simp [hq_ne]

/-- Helper for Theorem 7.29: equality in the predictive-risk bracket occurs
exactly at the normalized ratio `t = 1`. -/
lemma predictiveObjectiveBracket_eq_iff
    {p q t : ℝ}
    (h_p : 0 < p) (h_q : 1 < q) (h_t : 0 < t) :
    t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) = q ↔ t = 1 := by
  have hq_pos : 0 < q := by
    linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hp_ne : p ≠ 0 := ne_of_gt h_p
  have hqp_ne : q / p ≠ 0 := div_ne_zero hq_ne hp_ne
  have hw1 : 0 < 1 / q := one_div_pos.mpr hq_pos
  have hw2 : 0 < (q - 1) / q := by
    exact div_pos (by linarith) hq_pos
  have hw :
      (1 / q) + ((q - 1) / q) = 1 := by
    field_simp [hq_ne]
    linarith
  have hgeom_one :
      (t ^ ((q - 1) / p)) ^ (1 / q) * (t ^ (-(1 / p))) ^ ((q - 1) / q) = 1 := by
    rw [← Real.rpow_mul h_t.le ((q - 1) / p) (1 / q)]
    rw [← Real.rpow_mul h_t.le (-(1 / p)) ((q - 1) / q)]
    rw [← Real.rpow_add h_t]
    have hexp :
        ((q - 1) / p) * (1 / q) + (-(1 / p)) * ((q - 1) / q) = 0 := by
      field_simp [hp_ne, hq_ne]
      ring
    rw [hexp, Real.rpow_zero]
  constructor
  · intro h_eq
    -- Convert the source bracket equality to the weighted-AM-GM equality case.
    have hweighted_eq :
        (1 / q) * t ^ ((q - 1) / p) +
            ((q - 1) / q) * t ^ (-(1 / p)) = 1 := by
      calc
        (1 / q) * t ^ ((q - 1) / p) + ((q - 1) / q) * t ^ (-(1 / p))
            = (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) / q := by
                field_simp [hq_ne]
        _ = q / q := by rw [h_eq]
        _ = 1 := by field_simp [hq_ne]
    have hab :
        t ^ ((q - 1) / p) = t ^ (-(1 / p)) := by
      refine
        (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
          hw1 hw2 (by positivity) (by positivity) hw).mp ?_
      rw [hgeom_one, hweighted_eq]
    -- Collapse the two powers to `t ^ (q / p) = 1`, then use injectivity.
    have hpow_qp :
        t ^ (q / p) = 1 := by
      calc
        t ^ (q / p)
            = t ^ ((q - 1) / p) * t ^ (1 / p) := by
                rw [← Real.rpow_add h_t]
                congr 1
                ring
        _ = t ^ (-(1 / p)) * t ^ (1 / p) := by rw [hab]
        _ = t ^ (-(1 / p) + 1 / p) := by rw [← Real.rpow_add h_t]
        _ = 1 := by
              have hsum_zero : -(1 / p) + 1 / p = (0 : ℝ) := by ring_nf
              rw [hsum_zero, Real.rpow_zero]
    exact
      (Real.rpow_left_inj h_t.le (show 0 ≤ (1 : ℝ) by positivity) hqp_ne).mp
        (by simpa using hpow_qp)
  · intro h_t_eq
    -- Substituting `t = 1` collapses both powers in the bracket.
    simp [h_t_eq]

/-- Helper for Theorem 7.29: the predictive-risk coefficient `C₁` is positive
in the nonsaturated regime. -/
lemma predictiveRiskC1_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : p - q > -1) :
    0 < TikhonovPredictiveRisk.predictiveRiskC1 b c p q := by
  -- Expand `C₁` and check the kernel moment lies in the positive regime.
  have hp_pos : 0 < p := by
    linarith
  have h_s : 0 < (p - q) + 1 := by
    linarith
  have h_decay : 0 < 3 * p - (p - q) - 1 := by
    linarith
  rw [TikhonovPredictiveRisk.predictiveRiskC1_def]
  refine mul_pos (mul_pos h_b ?_) ?_
  · exact Real.rpow_pos_of_pos h_c _
  · exact kernelMomentIntegralPos_j3 hp_pos h_s h_decay

/-- Helper for Theorem 7.29: the predictive-risk coefficient `C₂` is positive.
-/
lemma predictiveRiskC2_pos
    (h_c : 0 < c) (h_p : 1 < p) :
    0 < TikhonovPredictiveRisk.predictiveRiskC2 c p := by
  -- The variance coefficient uses the same positive kernel moment at `s = p`.
  have hp_pos : 0 < p := by
    linarith
  have h_s : 0 < p + 1 := by
    linarith
  have h_decay : 0 < 3 * p - p - 1 := by
    linarith
  rw [TikhonovPredictiveRisk.predictiveRiskC2_def]
  refine mul_pos ?_ ?_
  · exact Real.rpow_pos_of_pos h_c _
  · exact kernelMomentIntegralPos_j3 hp_pos h_s h_decay

/-- Helper for Theorem 7.29: the shifted predictive benchmark `β_pred` is
positive at every positive data size. -/
lemma betaPred_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) :
    0 < TikhonovPredictiveRisk.betaPred b c p q σ n := by
  -- Expand the closed form of `β_pred` and prove positivity of both factors.
  rw [TikhonovPredictiveRisk.betaPred_def, TikhonovPredictiveRisk.betaPredConstant_def]
  have hq1 : 0 < q - 1 := by
    linarith
  have hRatioPos :
    0 <
        TikhonovPredictiveRisk.predictiveRiskC2 c p /
          ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q) := by
    exact div_pos
      (predictiveRiskC2_pos c p h_c h_p)
      (mul_pos hq1 (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated))
  have hSigmaDivPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSq : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSq (by exact_mod_cast n.2)
  exact mul_pos (Real.rpow_pos_of_pos hRatioPos _) (Real.rpow_pos_of_pos hSigmaDivPos _)

/-- Helper for Theorem 7.29: every positive root of the predictive benchmark
equation minimizes the predictive objective on `Set.Ioi (0 : ℝ)`. -/
lemma objective_le_of_rootEquation
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (_h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) {β α : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hroot : TikhonovPredictiveRisk.BetaPredRootEquation b c p q σ n β) :
    TikhonovPredictiveRisk.objective b c p q σ n β <=
      TikhonovPredictiveRisk.objective b c p q σ n α := by
  have hp_pos : 0 < p := by
    linarith
  have hpref_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    exact mul_pos
      (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated)
      (Real.rpow_pos_of_pos hβ _)
  set t : ℝ := α / β
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hα hβ
  have hα_eq : α = β * t := by
    dsimp [t]
    field_simp [hβ.ne']
  have hroot_scaled :
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p)) =
        (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    rw [TikhonovPredictiveRisk.betaPredRootEquation_iff] at hroot
    calc
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ (q / p)) *
              β ^ (-(1 / p)) := by
                rw [← hroot]
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              (β ^ (q / p) * β ^ (-(1 / p))) := by
                ring
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              β ^ ((q - 1) / p) := by
                rw [← Real.rpow_add hβ]
                congr 2
                ring
  have hobj_beta :
      TikhonovPredictiveRisk.objective b c p q σ n β =
        q * (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Rewrite the benchmark objective using the root equation.
    rw [TikhonovPredictiveRisk.objective_def]
    calc
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
          TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
              (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                β ^ ((q - 1) / p) := by
                  rw [hroot_scaled]
      _ = q * (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
            ring
  have hobj_alpha :
      TikhonovPredictiveRisk.objective b c p q σ n α =
        (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
          (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Normalize `α = β * t` and factor out the common positive scalar.
    rw [TikhonovPredictiveRisk.objective_def, hα_eq]
    calc
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * (β * t) ^ ((q - 1) / p) +
          TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
            (β * t) ^ (-(1 / p))
          =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                (β ^ ((q - 1) / p) * t ^ ((q - 1) / p)) +
              TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                (β ^ (-(1 / p)) * t ^ (-(1 / p))) := by
                rw [Real.mul_rpow hβ.le ht_pos.le]
                rw [Real.mul_rpow hβ.le ht_pos.le]
      _ =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
                t ^ ((q - 1) / p) +
              (TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                β ^ (-(1 / p))) * t ^ (-(1 / p)) := by
                  ring
      _ =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
                t ^ ((q - 1) / p) +
              ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                β ^ ((q - 1) / p)) * t ^ (-(1 / p)) := by
                  rw [hroot_scaled]
      _ =
            (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
              (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
                ring
  -- The remaining scalar inequality is exactly the weighted-AM-GM lower bound.
  rw [hobj_beta, hobj_alpha]
  exact mul_le_mul_of_nonneg_right
    (predictiveObjectiveBracket_ge hp_pos h_q ht_pos)
    (le_of_lt hpref_pos)

/-- Helper for Theorem 7.29: equality in the predictive objective at a
positive root occurs only at that root. -/
lemma objective_eq_of_rootEquation_iff
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (_h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) {β α : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hroot : TikhonovPredictiveRisk.BetaPredRootEquation b c p q σ n β) :
    TikhonovPredictiveRisk.objective b c p q σ n α =
        TikhonovPredictiveRisk.objective b c p q σ n β ↔
      α = β := by
  have hp_pos : 0 < p := by
    linarith
  have hpref_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    exact mul_pos
      (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated)
      (Real.rpow_pos_of_pos hβ _)
  set t : ℝ := α / β
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hα hβ
  have hα_eq : α = β * t := by
    dsimp [t]
    field_simp [hβ.ne']
  have hroot_scaled :
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p)) =
        (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    rw [TikhonovPredictiveRisk.betaPredRootEquation_iff] at hroot
    calc
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ (q / p)) *
              β ^ (-(1 / p)) := by
                rw [← hroot]
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              (β ^ (q / p) * β ^ (-(1 / p))) := by
                ring
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              β ^ ((q - 1) / p) := by
                rw [← Real.rpow_add hβ]
                congr 2
                ring
  have hobj_beta :
      TikhonovPredictiveRisk.objective b c p q σ n β =
        q * (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Reuse the root equation to simplify the benchmark objective value.
    rw [TikhonovPredictiveRisk.objective_def]
    calc
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
          TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
              (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                β ^ ((q - 1) / p) := by
                  rw [hroot_scaled]
      _ = q * (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
            ring
  have hobj_alpha :
      TikhonovPredictiveRisk.objective b c p q σ n α =
        (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
          (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Normalize `α = β * t` exactly as in the minimizer inequality proof.
    rw [TikhonovPredictiveRisk.objective_def, hα_eq]
    calc
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * (β * t) ^ ((q - 1) / p) +
          TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
            (β * t) ^ (-(1 / p))
          =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                (β ^ ((q - 1) / p) * t ^ ((q - 1) / p)) +
              TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                (β ^ (-(1 / p)) * t ^ (-(1 / p))) := by
                rw [Real.mul_rpow hβ.le ht_pos.le]
                rw [Real.mul_rpow hβ.le ht_pos.le]
      _ =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
                t ^ ((q - 1) / p) +
              (TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                β ^ (-(1 / p))) * t ^ (-(1 / p)) := by
                  ring
      _ =
            TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
                t ^ ((q - 1) / p) +
              ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
                β ^ ((q - 1) / p)) * t ^ (-(1 / p)) := by
                  rw [hroot_scaled]
      _ =
            (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
              (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
                ring
  constructor
  · intro h_eq
    -- Cancel the positive common factor and invoke the equality case of the
    -- predictive bracket.
    rw [hobj_alpha, hobj_beta] at h_eq
    have hbracket :
        t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) = q := by
      exact mul_right_cancel₀ hpref_pos.ne' h_eq
    have ht_eq_one :
        t = 1 := (predictiveObjectiveBracket_eq_iff hp_pos h_q ht_pos).mp hbracket
    calc
      α = β * t := hα_eq
      _ = β := by simp [ht_eq_one]
  · intro h_alpha_beta
    -- Substituting the unique minimizer back into the objective gives equality.
    simp [h_alpha_beta]

/-- Helper for Theorem 7.29: any positive predictive-risk minimizing family for
the shifted Chapter 7 objective agrees pointwise with the shifted benchmark
`β_pred`. -/
lemma predictiveOptimalFamily_eq_betaPredSucc
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {alphaPred : ℕ → ℝ}
    (h_alphaPred_pos : ∀ n, alphaPred n ∈ Set.Ioi (0 : ℝ))
    (h_alphaPred :
      ParameterChoice.IsOptimalParameterFamily
        (fun n ↦ TikhonovPredictiveRisk.objective b c p q σ n.succ)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        alphaPred) :
    ∀ n, alphaPred n = TikhonovPredictiveRisk.betaPred b c p q σ n.succ := by
  -- Route correction: prove predictive uniqueness locally from the explicit
  -- predictive benchmark equation instead of importing the broken aggregate
  -- `Book.Ch7.Theorem_7_23` file.
  have hC1_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC1 b c p q :=
    predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated
  have hC2_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC2 c p :=
    predictiveRiskC2_pos c p h_c h_p
  have h_alphaPred_min :=
    (ParameterChoice.isOptimalParameterFamily_iff
      (fun n ↦ TikhonovPredictiveRisk.objective b c p q σ n.succ)
      (fun _ ↦ Set.Ioi (0 : ℝ))
      alphaPred).1 h_alphaPred
  intro n
  let npos : ℕ+ := ⟨n.succ, Nat.succ_pos n⟩
  have h_alpha_mem : 0 < alphaPred n := h_alphaPred_pos n
  have h_beta_mem :
      0 < TikhonovPredictiveRisk.betaPred b c p q σ npos :=
    betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos
  have hp_pos : 0 < p := by
    linarith
  have h_beta_root :
      TikhonovPredictiveRisk.BetaPredRootEquation b c p q σ npos
        (TikhonovPredictiveRisk.betaPred b c p q σ npos) :=
    TikhonovPredictiveRisk.betaPred_rootEquation
      b c p q σ hC1_pos hC2_pos hp_pos h_q h_σ npos
  have h_beta_min :
      IsMinOn
        (TikhonovPredictiveRisk.objective b c p q σ n.succ)
        (Set.Ioi (0 : ℝ))
        (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
    -- The benchmark is admissible and satisfies the predictive root equation.
    intro α hα
    exact
      objective_le_of_rootEquation
        b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos h_beta_mem hα h_beta_root
  have h_eq_obj :
      TikhonovPredictiveRisk.objective b c p q σ n.succ (alphaPred n) =
        TikhonovPredictiveRisk.objective b c p q σ n.succ
          (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
    have h_alpha_min_n := h_alphaPred_min n
    rw [isMinOn_iff] at h_alpha_min_n h_beta_min
    apply le_antisymm
    · exact h_alpha_min_n _ h_beta_mem
    · exact h_beta_min _ h_alpha_mem
  have h_eq_point :
      alphaPred n = TikhonovPredictiveRisk.betaPred b c p q σ npos := by
    exact
      (objective_eq_of_rootEquation_iff
        b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos h_beta_mem h_alpha_mem
        h_beta_root).mp
        h_eq_obj
  simpa [npos] using h_eq_point

/-- Helper for Theorem 7.29: after rewriting the expected GCV objective into
its spectral ratio form, any minimizing family is asymptotically equivalent to
the shifted predictive benchmark `β_pred`. -/
lemma expectedObjective_eq_spectralQuotient
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (n : ℕ) (α : ℝ) :
    expectedObjective μ K R fTrue η n α =
      ((1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
              s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 +
        (σ ^ 2 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2) /
        ((((n.succ : ℝ) - ∑ i : Fin n.succ,
            SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
          (n.succ : ℝ)) ^ 2) := by
  -- Expand the expected GCV objective and rewrite the pointwise integrand using
  -- the available spectral formula for `gcvValue`.
  calc
    expectedObjective μ K R fTrue η n α
        =
          ∫ ω,
            predictiveRisk
                (FilterRegularization.rα (K n) (R n α) (fTrue n) (η n) ω) /
              ((((n.succ : ℝ) - ∑ i : Fin n.succ,
                  SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
                (n.succ : ℝ)) ^ 2) ∂μ := by
            unfold expectedObjective
            refine MeasureTheory.integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro ω
            have hA :
                influenceMatrix (K n) (R n α) =
                  U n *
                    Matrix.diagonal
                      (fun i ↦ SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) *
                    (U n)ᵀ := by
              simpa using
                (influenceMatrix_eq_spectralRep
                  (K n) (U n) (V n) (R n α)
                  (SpectralFilter.discreteTikhonov n.succ α) (s n)
                  (h_svd n) (h_tikhonov n α))
            -- This is the exact Exercise 7.3 denominator rewrite specialized to
            -- the discrete Tikhonov filter family, proved here through the
            -- stable Remark 7.4 denominator API.
            calc
              (fun ω ↦
                  gcv
                    (fun β ↦ influenceMatrix (K n) (R n β))
                    ((K n).toEuclideanLin (fTrue n) + η n ω)
                    α) ω
                  =
                gcvValue
                  (influenceMatrix (K n) (R n α))
                  ((K n).toEuclideanLin (fTrue n) + η n ω) := by
                    exact
                      gcv_eq_gcvValue
                        (fun β ↦ influenceMatrix (K n) (R n β))
                        ((K n).toEuclideanLin (fTrue n) + η n ω)
                        α
              _ =
                predictiveRisk
                    (FilterRegularization.rα (K n) (R n α) (fTrue n) (η n) ω) /
                  ((((n.succ : ℝ) - ∑ i : Fin n.succ,
                      SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
                    (n.succ : ℝ)) ^ 2) := by
                    simpa using
                      (gcvValue_eq_of_spectralRep
                        (influenceMatrix (K n) (R n α))
                        (U n)
                        (SpectralFilter.discreteTikhonov n.succ α)
                        (s n)
                        ((K n).toEuclideanLin (fTrue n) + η n ω)
                        (h_tikhonov n α).orthogonalU hA)
    _ =
          (∫ ω,
            predictiveRisk
              (FilterRegularization.rα (K n) (R n α) (fTrue n) (η n) ω) ∂μ) /
            ((((n.succ : ℝ) - ∑ i : Fin n.succ,
                SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
              (n.succ : ℝ)) ^ 2) := by
            -- The denominator is deterministic in `ω`, so it can be pulled out
            -- of the expectation as a scalar division.
            rw [MeasureTheory.integral_div]
    _ =
          ((1 / (n.succ : ℝ)) *
              ∑ i : Fin n.succ,
                (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
                  s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 +
            (σ ^ 2 / (n.succ : ℝ)) *
              ∑ i : Fin n.succ,
                (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2) /
            ((((n.succ : ℝ) - ∑ i : Fin n.succ,
                SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
              (n.succ : ℝ)) ^ 2) := by
            -- Proposition 7.8 supplies the exact spectral numerator for the
            -- expected residual risk in the same discrete Tikhonov coordinates.
            have hResidual :
                (∫ ω,
                  predictiveRisk
                    (FilterRegularization.rα (K n) (R n α) (fTrue n) (η n) ω) ∂μ) =
                  (1 / (n.succ : ℝ)) *
                      ∑ i : Fin n.succ,
                        (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
                          s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 +
                    (σ ^ 2 / (n.succ : ℝ)) *
                      ∑ i : Fin n.succ,
                        (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 := by
              simpa using
                (FilterRegularization.expectedResidualRisk_rα_eq_spectralSum
                  (h_white n) (h_svd n) (h_tikhonov n α))
            rw [hResidual]

/-- Helper for Theorem 7.29: on the algebraic singular-value mode, the
complement of the discrete Tikhonov filter is the rational profile that drives
the GCV denominator trace. -/
lemma oneSubDiscreteTikhonov_eq_modeProfile
    {n : ℕ} {α c p : ℝ} (h_c : 0 < c) (h_alpha : 0 < α) (k : ℕ+) :
    1 - SpectralFilter.discreteTikhonov n α (c * (k : ℝ) ^ (-p)) =
      ((((n : ℝ) * α) / c) * (k : ℝ) ^ p) /
        (1 + (((n : ℝ) * α) / c) * (k : ℝ) ^ p) := by
  set A : ℝ := (((n : ℝ) * α) / c) * (k : ℝ) ^ p
  have hden_ne : 1 + A ≠ 0 := by
    -- Positivity of `α`, `c`, and the mode index keeps the rational profile
    -- denominator away from zero.
    dsimp [A]
    positivity
  -- Rewrite the filter itself to the exact mode profile before simplifying
  -- its complement.
  rw [@discreteTikhonov_eq_modeProfile n α c p h_c k]
  change 1 - 1 / (1 + A) = A / (1 + A)
  field_simp [hden_ne]
  ring

/-- Helper for Theorem 7.29: the normalized GCV trace gap is the square of the
average pointwise complement trace. -/
lemma normalizedTraceGap_sq_eq_averageComplement_sq
    (n : ℕ) (w : Fin n.succ → ℝ) :
    ((((n.succ : ℝ) - ∑ i : Fin n.succ, w i) / (n.succ : ℝ)) ^ 2) =
      ((((1 / (n.succ : ℝ)) * ∑ i : Fin n.succ, (1 - w i))) ^ 2) := by
  have hsum_one : (∑ i : Fin n.succ, (1 : ℝ)) = (n.succ : ℝ) := by
    simp
  have hsum_complement :
      (∑ i : Fin n.succ, (1 : ℝ)) - ∑ i : Fin n.succ, w i =
        ∑ i : Fin n.succ, (1 - w i) := by
    simp [Finset.sum_sub_distrib]
  -- Replace the scalar trace gap by the average of the modewise complements.
  calc
    ((((n.succ : ℝ) - ∑ i : Fin n.succ, w i) / (n.succ : ℝ)) ^ 2)
        =
          ((((∑ i : Fin n.succ, (1 : ℝ)) - ∑ i : Fin n.succ, w i) /
              (n.succ : ℝ)) ^ 2) := by
            rw [hsum_one]
    _ = ((((∑ i : Fin n.succ, (1 - w i)) / (n.succ : ℝ)) ^ 2)) := by
          rw [hsum_complement]
    _ = ((((1 / (n.succ : ℝ)) * ∑ i : Fin n.succ, (1 - w i))) ^ 2) := by
          congr 1
          rw [div_eq_mul_inv]
          ring

/-- Helper for Theorem 7.29: after imposing the algebraic singular-value law,
the GCV trace denominator is the square of the average mode-profile
complement. -/
lemma normalizedTraceGap_sq_eq_modeProfile
    (h_c : 0 < c) {n : ℕ} {α : ℝ} (h_alpha : 0 < α)
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p)) :
    ((((n.succ : ℝ) - ∑ i : Fin n.succ,
        SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
        (n.succ : ℝ)) ^ 2) =
      ((((1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            ((((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p) /
              (1 + (((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p)) ^ 2)) := by
  -- First convert the normalized trace gap into an average complement trace.
  rw [normalizedTraceGap_sq_eq_averageComplement_sq]
  -- Then rewrite each complement term by the exact algebraic mode profile.
  congr 1
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [h_singularValueSquareDecay n i]
  simpa using
    @oneSubDiscreteTikhonov_eq_modeProfile n.succ α c p h_c h_alpha
      ⟨i.1.succ, Nat.succ_pos i.1⟩

/-- Helper for Theorem 7.29: the average complement profile in the GCV
denominator is `1 - ((n * h)⁻¹ * S_{p,1}^{0}(n, h))`, the `KernelMoment`
normal form needed for Proposition 7.19. -/
lemma averageComplement_eq_one_sub_kernelMoment
    {n : ℕ} {h p : ℝ} (h_h : 0 < h) :
    (1 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          (((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
            (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p)) =
      1 -
        (1 / (((n.succ : ℝ) * h))) *
          KernelMoment.quadratureSum p 1 0 n.succ h := by
  have h_nsucc_ne : (n.succ : ℝ) ≠ 0 := by
    positivity
  have h_nsucc_h_ne : ((n.succ : ℝ) * h) ≠ 0 := by
    positivity
  have h_pointwise :
      ∀ i : Fin n.succ,
        (((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
            (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p)) =
          1 - 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) := by
    intro i
    have h_den_ne : 1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p ≠ 0 := by
      positivity
    -- Rewrite each complement term as `1` minus its reciprocal to expose the
    -- average reciprocal sum handled by the quadrature notation.
    field_simp [h_den_ne]
    ring
  have h_average_split :
      (1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            (((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
              (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p)) =
        1 -
          (1 / (n.succ : ℝ)) *
            ∑ i : Fin n.succ, 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) := by
    -- Average the pointwise identity from `h_pointwise`.
    rw [Finset.mul_sum]
    simp_rw [h_pointwise]
    rw [show
      (∑ x : Fin n.succ, (1 / (n.succ : ℝ)) * (1 - 1 / (1 + (h ^ p) * ((x.1.succ : ℕ) : ℝ) ^ p))) =
        ∑ x : Fin n.succ,
          ((1 / (n.succ : ℝ)) * 1 -
            (1 / (n.succ : ℝ)) * (1 / (1 + (h ^ p) * ((x.1.succ : ℕ) : ℝ) ^ p))) by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    have h_unit' : (((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹)) = 1 := by
      have h_one_ne : ((n : ℝ) + 1) ≠ 0 := by
        positivity
      field_simp [h_one_ne]
    rw [← Finset.mul_sum]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_unit'
  have h_quadrature :
      (1 / (((n.succ : ℝ) * h))) * KernelMoment.quadratureSum p 1 0 n.succ h =
        (1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ, 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) := by
    -- Convert `S_{p,1}^{0}` to the shifted finite sum and simplify the
    -- integrand on the positive grid `((k + 1) * h)`.
    rw [quadratureSum_eq_sumRangeSeries_local]
    rw [Finset.mul_sum]
    have h_fin_sum :
        ∑ i : Fin n.succ, 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) =
          ∑ k ∈ Finset.range n.succ, 1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p) := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [h_fin_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_pos : 0 < (((k + 1 : ℕ) : ℝ) * h) := by
      positivity
    calc
      (1 / (((n.succ : ℝ) * h))) * (h * KernelMoment.integrand p 1 0 (((k + 1 : ℕ) : ℝ) * h))
          = (1 / (n.succ : ℝ)) * KernelMoment.integrand p 1 0 (((k + 1 : ℕ) : ℝ) * h) := by
              field_simp [h_nsucc_h_ne, h_h.ne', h_nsucc_ne]
      _ = (1 / (n.succ : ℝ)) * (1 / (1 + ((((k + 1 : ℕ) : ℝ) * h) ^ p)) ) := by
            rw [KernelMoment.integrand_def, Real.rpow_zero, pow_one, one_div]
      _ = (1 / (n.succ : ℝ)) * (1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p)) := by
            congr 2
            rw [Real.mul_rpow (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity) h_h.le]
            ring
  -- Combine the averaged pointwise identity with the quadrature rewrite.
  rw [h_average_split, ← h_quadrature]

/-- Helper for Theorem 7.29: the averaged reciprocal-square profile in the GCV
denominator is the `KernelMoment` quadrature sum `S_{p,2}^{0}` at the same
mesh scale. -/
lemma averageReciprocalSq_eq_kernelMoment
    {n : ℕ} {h p : ℝ} (h_h : 0 < h) :
    (1 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) ^ 2 =
      (1 / (((n.succ : ℝ) * h))) *
        KernelMoment.quadratureSum p 2 0 n.succ h := by
  have h_nsucc_ne : (n.succ : ℝ) ≠ 0 := by
    positivity
  have h_nsucc_h_ne : ((n.succ : ℝ) * h) ≠ 0 := by
    positivity
  -- Convert `S_{p,2}^{0}` to the shifted finite sum and simplify the
  -- squared reciprocal profile on the positive grid `((k + 1) * h)`.
  have h_fin_sum :
      ∑ i : Fin n.succ, 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) ^ 2 =
        ∑ k ∈ Finset.range n.succ, 1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
  calc
    (1 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ, 1 / (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) ^ 2
        =
          (1 / (n.succ : ℝ)) *
            ∑ k ∈ Finset.range n.succ, 1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p) ^ 2 := by
              exact congrArg (fun z : ℝ ↦ (1 / (n.succ : ℝ)) * z) h_fin_sum
    _ =
          ∑ k ∈ Finset.range n.succ,
            (1 / (n.succ : ℝ)) * (1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p) ^ 2) := by
              rw [Finset.mul_sum]
    _ =
          ∑ k ∈ Finset.range n.succ,
            (1 / (((n.succ : ℝ) * h))) *
              (h * KernelMoment.integrand p 2 0 (((k + 1 : ℕ) : ℝ) * h)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              calc
                (1 / (n.succ : ℝ)) * (1 / (1 + (h ^ p) * ((k + 1 : ℕ) : ℝ) ^ p) ^ 2)
                    = (1 / (n.succ : ℝ)) *
                        KernelMoment.integrand p 2 0 (((k + 1 : ℕ) : ℝ) * h) := by
                          rw [KernelMoment.integrand_def, Real.rpow_zero]
                          congr 2
                          rw [Real.mul_rpow (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity) h_h.le]
                          ring
                _ =
                      (1 / (((n.succ : ℝ) * h))) *
                        (h * KernelMoment.integrand p 2 0 (((k + 1 : ℕ) : ℝ) * h)) := by
                            field_simp [h_nsucc_h_ne, h_h.ne', h_nsucc_ne]
    _ =
          (1 / (((n.succ : ℝ) * h))) *
            KernelMoment.quadratureSum p 2 0 n.succ h := by
              rw [quadratureSum_eq_sumRangeSeries_local, Finset.mul_sum]

/-- Helper for Theorem 7.29: after imposing the algebraic decay laws, the bias
part of the expected GCV numerator is an exact finite mode-profile sum. -/
lemma expectedObjectiveBias_eq_modeProfileSum
    (h_c : 0 < c) {n : ℕ} {α : ℝ} (h_alpha : 0 < α)
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q)) :
    (1 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
            s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
      (1 / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          (b * (((n.succ : ℝ) * α) ^ 2) / c) *
            (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
  -- Convert the finite `Fin` sum to a `range` sum, then rewrite each summand
  -- through the exact algebraic mode profile.
  have h_range :
      (∑ i : Fin n.succ,
          (fun k : ℕ ↦
            (b * (((n.succ : ℝ) * α) ^ 2) / c) *
              (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i) =
        ∑ k ∈ Finset.range n.succ,
          (b * (((n.succ : ℝ) * α) ^ 2) / c) *
            (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦
          (b * (((n.succ : ℝ) * α) ^ 2) / c) *
            (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2)
        n.succ)
  have h_sum :
      ∑ i : Fin n.succ,
        (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
          s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
        ∑ i : Fin n.succ,
          (fun k : ℕ ↦
            (b * (((n.succ : ℝ) * α) ^ 2) / c) *
              (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    -- The decay hypotheses put the spectral bias summand into the rational
    -- profile used later by the quadrature analysis.
    rw [h_singularValueSquareDecay n i, h_fourierCoefficientSquareDecay n i]
    simpa using
      (discreteTikhonov_sub_one_sq_mul_decay_eq_modeProfile
        (n := n.succ) (α := α) (b := b) (c := c) (p := p) (q := q)
        h_c h_alpha ⟨i.1.succ, Nat.succ_pos i.1⟩)
  calc
    (1 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 *
            s n i ^ 2 * (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2
        =
          (1 / (n.succ : ℝ)) *
            ∑ i : Fin n.succ,
              (fun k : ℕ ↦
                (b * (((n.succ : ℝ) * α) ^ 2) / c) *
                  (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                    (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i := by
              exact congrArg (fun z : ℝ ↦ (1 / (n.succ : ℝ)) * z) h_sum
    _ =
          (1 / (n.succ : ℝ)) *
            ∑ k ∈ Finset.range n.succ,
              (b * (((n.succ : ℝ) * α) ^ 2) / c) *
                (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                  (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
            rw [h_range]

/-- Helper for Theorem 7.29: after imposing the algebraic singular-value law,
the variance part of the expected GCV numerator is an exact finite
mode-profile sum. -/
lemma expectedObjectiveVariance_eq_modeProfileSum
    (h_c : 0 < c) {n : ℕ} {α : ℝ} (h_alpha : 0 < α)
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p)) :
    (σ ^ 2 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 =
      (σ ^ 2 / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
            (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
  -- The variance-side summand uses the same `range` indexing and exact filter
  -- profile, but without the source-condition decay factor.
  have h_range :
      (∑ i : Fin n.succ,
          (fun k : ℕ ↦
            ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i) =
        ∑ k ∈ Finset.range n.succ,
          ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
            (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦
          ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
            (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2)
        n.succ)
  have h_sum :
      ∑ i : Fin n.succ,
        (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2 =
        ∑ i : Fin n.succ,
          (fun k : ℕ ↦
            ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    -- Rewrite the discrete Tikhonov deviation on the algebraic singular-value
    -- grid to the exact rational mode profile.
    rw [h_singularValueSquareDecay n i]
    simpa using
      (discreteTikhonov_sub_one_sq_eq_modeProfile
        (n := n.succ) (α := α) (c := c) (p := p) h_c h_alpha
        ⟨i.1.succ, Nat.succ_pos i.1⟩)
  calc
    (σ ^ 2 / (n.succ : ℝ)) *
        ∑ i : Fin n.succ,
          (SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2) - 1) ^ 2
        =
          (σ ^ 2 / (n.succ : ℝ)) *
            ∑ i : Fin n.succ,
              (fun k : ℕ ↦
                ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
                  (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) i := by
              exact congrArg (fun z : ℝ ↦ (σ ^ 2 / (n.succ : ℝ)) * z) h_sum
    _ =
          (σ ^ 2 / (n.succ : ℝ)) *
            ∑ k ∈ Finset.range n.succ,
              ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
                (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 := by
            rw [h_range]

/-- Helper for Theorem 7.29: the expected GCV denominator equals the square of
`1` minus the kernel-moment trace defect at the scaled mesh
`(((n.succ : ℝ) * α) / c) ^ (1 / p)`. -/
lemma expectedObjectiveDenominator_eq_kernelMomentDefect
    (h_c : 0 < c) (h_p : 1 < p) {n : ℕ} {α : ℝ} (h_alpha : 0 < α)
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p)) :
    ((((n.succ : ℝ) - ∑ i : Fin n.succ,
        SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
        (n.succ : ℝ)) ^ 2) =
      (1 -
          (1 / (((n.succ : ℝ) * ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) *
            KernelMoment.quadratureSum p 1 0 n.succ
              ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) ^ 2 := by
  let h : ℝ := ((((n.succ : ℝ) * α) / c)) ^ (1 / p)
  have h_hpos : 0 < h := by
    -- The scaled mesh is positive because `α`, `c`, and `n.succ` are all positive.
    dsimp [h]
    positivity
  have h_hp : h ^ p = (((n.succ : ℝ) * α) / c) := by
    -- By construction, `h` is the positive `p`-th root of the Tikhonov mode scale.
    dsimp [h]
    have hscale_pos : 0 < (((n.succ : ℝ) * α) / c) := by
      positivity
    have hp_ne : p ≠ 0 := by
      linarith
    calc
      ((((n.succ : ℝ) * α) / c) ^ (1 / p)) ^ p
          = (((n.succ : ℝ) * α) / c) ^ ((1 / p) * p) := by
              rw [Real.rpow_mul hscale_pos.le (1 / p) p]
      _ = (((n.succ : ℝ) * α) / c) ^ (1 : ℝ) := by
            congr 1
            field_simp [hp_ne]
      _ = (((n.succ : ℝ) * α) / c) := by
            rw [Real.rpow_one]
  have h_average' :
      (1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            ((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
              (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) =
        1 -
          (1 / (((n.succ : ℝ) * h))) *
            KernelMoment.quadratureSum p 1 0 n.succ h := by
    -- Rewrite the average complement trace through the kernel-moment notation.
    exact averageComplement_eq_one_sub_kernelMoment (n := n) (p := p) (h := h) h_hpos
  have h_average :
      (1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ,
            ((((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p) /
              (1 + (((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p) =
        1 -
          (1 / (((n.succ : ℝ) * h))) *
            KernelMoment.quadratureSum p 1 0 n.succ h := by
    -- Substitute the explicit scale `h ^ p = ((n.succ : ℝ) * α) / c`.
    simpa [h_hp] using h_average'
  -- Combine the exact trace-gap profile with the averaged kernel-moment defect.
  calc
    ((((n.succ : ℝ) - ∑ i : Fin n.succ,
        SpectralFilter.discreteTikhonov n.succ α (s n i ^ 2)) /
        (n.succ : ℝ)) ^ 2)
        =
          ((((1 / (n.succ : ℝ)) *
              ∑ i : Fin n.succ,
                ((((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p) /
                  (1 + (((n.succ : ℝ) * α) / c) * ((i.1.succ : ℕ) : ℝ) ^ p)) ^ 2)) := by
            simpa using
              (normalizedTraceGap_sq_eq_modeProfile
                (s := s) (c := c) (p := p) h_c (n := n) (α := α) h_alpha
                h_singularValueSquareDecay)
    _ = (1 - (1 / (((n.succ : ℝ) * h))) *
          KernelMoment.quadratureSum p 1 0 n.succ h) ^ 2 := by
          rw [h_average]
    _ =
          (1 -
            (1 / (((n.succ : ℝ) * ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) *
              KernelMoment.quadratureSum p 1 0 n.succ
                ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) ^ 2 := by
          rfl

/-- Helper for Theorem 7.29: the expected GCV objective has an exact
finite-mode quotient formula once the spectral numerator and denominator are
rewritten through the Chapter 7 algebraic mode profiles. -/
lemma expectedObjective_eq_modeProfileQuotient
    (h_c : 0 < c) (h_p : 1 < p) {n : ℕ} {α : ℝ} (h_alpha : 0 < α)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q)) :
    expectedObjective μ K R fTrue η n α =
      ((1 / (n.succ : ℝ)) *
          ∑ k ∈ Finset.range n.succ,
            (b * (((n.succ : ℝ) * α) ^ 2) / c) *
              (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 +
        (σ ^ 2 / (n.succ : ℝ)) *
          ∑ k ∈ Finset.range n.succ,
            ((((n.succ : ℝ) * α) / c) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
              (1 + (((n.succ : ℝ) * α) / c) * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) /
        ((1 -
          (1 / (((n.succ : ℝ) * ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) *
            KernelMoment.quadratureSum p 1 0 n.succ
              ((((n.succ : ℝ) * α) / c) ^ (1 / p)))) ^ 2) := by
  -- Rewrite the full expected GCV objective into its exact spectral quotient,
  -- then convert each piece to the algebraic mode-profile normal form.
  rw [expectedObjective_eq_spectralQuotient
    (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
    (fTrue := fTrue) (η := η) (σ := σ) h_white h_svd h_tikhonov n α]
  rw [expectedObjectiveBias_eq_modeProfileSum
    (V := V) (s := s) (fTrue := fTrue) (b := b) (c := c) (p := p) (q := q)
    h_c h_alpha h_singularValueSquareDecay h_fourierCoefficientSquareDecay]
  rw [expectedObjectiveVariance_eq_modeProfileSum
    (s := s) (c := c) (p := p) (σ := σ)
    h_c h_alpha h_singularValueSquareDecay]
  rw [expectedObjectiveDenominator_eq_kernelMomentDefect
    (s := s) (c := c) (p := p) h_c h_p h_alpha h_singularValueSquareDecay]

/-- Helper for Theorem 7.29: on the predictive benchmark scale, the mesh
parameter `(((n * (t * β_pred n)) / c) ^ (1 / p))` is an explicit positive
constant times `(n : ℝ) ^ (1 / p - 1 / q)`. -/
lemma betaPredScaleMesh_eq_constant_mul_power
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    ((((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c) ^
        (1 / p)) =
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (n.succ : ℝ) ^ (1 / p - 1 / q) := by
  have hp_pos : 0 < p := by
    linarith
  have hq_pos : 0 < q := by
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq1_pos : 0 < q - 1 := by
    linarith
  have h_betaConst_pos : 0 < TikhonovPredictiveRisk.betaPredConstant b c p q := by
    -- Expand the predictive benchmark constant and check the coefficient ratio
    -- is positive before taking the real power.
    rw [TikhonovPredictiveRisk.betaPredConstant_def]
    have h_ratio_pos :
        0 <
          TikhonovPredictiveRisk.predictiveRiskC2 c p /
            ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q) := by
      exact
        div_pos
          (predictiveRiskC2_pos c p h_c h_p)
          (mul_pos hq1_pos
            (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated))
    exact Real.rpow_pos_of_pos h_ratio_pos _
  have h_sigma_sq_pos : 0 < σ ^ 2 := by
    nlinarith [sq_pos_of_pos h_σ]
  have hn_pos : 0 < (n.succ : ℝ) := by
    positivity
  have h_n_factor :
      (n.succ : ℝ) * (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q)) =
        (σ ^ 2) ^ (p / q) * (n.succ : ℝ) ^ (1 - p / q) := by
    have h_div_rpow :
        (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q)) =
          (σ ^ 2) ^ (p / q) / (n.succ : ℝ) ^ (p / q) := by
      rw [Real.div_rpow (show 0 ≤ σ ^ 2 by positivity) hn_pos.le]
    calc
      (n.succ : ℝ) * (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q))
          = (n.succ : ℝ) * ((σ ^ 2) ^ (p / q) / (n.succ : ℝ) ^ (p / q)) := by
              rw [h_div_rpow]
      _ = (σ ^ 2) ^ (p / q) * ((n.succ : ℝ) / (n.succ : ℝ) ^ (p / q)) := by
            ring
      _ = (σ ^ 2) ^ (p / q) * (n.succ : ℝ) ^ (1 - p / q) := by
            congr 1
            calc
              (n.succ : ℝ) / (n.succ : ℝ) ^ (p / q)
                  = (n.succ : ℝ) ^ (1 : ℝ) / (n.succ : ℝ) ^ (p / q) := by
                      rw [Real.rpow_one]
              _ = (n.succ : ℝ) ^ (1 + -(p / q)) := by
                    rw [div_eq_mul_inv, ← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]
              _ = (n.succ : ℝ) ^ (1 - p / q) := by
                    simp [sub_eq_add_neg]
  have h_scale :
      ((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPredConstant b c p q *
          (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q))) / c) =
        ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            (σ ^ 2) ^ (p / q)) *
          (n.succ : ℝ) ^ (1 - p / q)) := by
    -- Separate the `n`-dependent factor from the benchmark constant, then use
    -- the exact `n * ((σ² / n) ^ (p / q))` power law.
    have h_split :
        ((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPredConstant b c p q *
            (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q))) / c) =
          (((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            ((n.succ : ℝ) * (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q)))) := by
      field_simp [h_c.ne']
    calc
      ((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPredConstant b c p q *
          (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q))) / c)
          =
        (((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          ((n.succ : ℝ) * (((σ ^ 2) / (n.succ : ℝ)) ^ (p / q)))) := h_split
      _ =
        (((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          ((σ ^ 2) ^ (p / q) * (n.succ : ℝ) ^ (1 - p / q))) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              congrArg
                (fun x ↦
                  ((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) * x)
                h_n_factor
      _ =
        ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            (σ ^ 2) ^ (p / q)) *
          (n.succ : ℝ) ^ (1 - p / q)) := by
            ring
  have h_const_nonneg :
      0 ≤
        (((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) := by
    positivity
  have h_beta_expand :
      ((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) / c) =
        ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            (σ ^ 2) ^ (p / q)) *
          (n.succ : ℝ) ^ (1 - p / q)) := by
    -- Rewrite `β_pred` to its explicit closed form before reusing the scale
    -- normalization from `h_scale`.
    rw [TikhonovPredictiveRisk.betaPred_def]
    simpa [mul_assoc] using h_scale
  -- Normalize the predictive benchmark scale, then split the final real power
  -- into its constant factor and its `n`-power.
  calc
    (((((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c) ^
        (1 / p)))
        =
      (((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) *
        (n.succ : ℝ) ^ (1 - p / q)) ^ (1 / p)) := by
          rw [h_beta_expand]
    _ =
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (((n.succ : ℝ) ^ (1 - p / q)) ^ (1 / p)) := by
          rw [Real.mul_rpow h_const_nonneg (show 0 ≤ (n.succ : ℝ) ^ (1 - p / q) by positivity)]
    _ =
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (n.succ : ℝ) ^ ((1 - p / q) * (1 / p)) := by
          rw [Real.rpow_mul hn_pos.le]
    _ =
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (n.succ : ℝ) ^ (1 / p - 1 / q) := by
          congr 2
          field_simp [hp_ne, hq_ne]

/-- Helper for Theorem 7.29: the sign of the `β_pred` mesh exponent is exactly
the sign of `q - p`, so the Proposition 7.19 requirement `h_n → 0+` is
equivalent to the extra side condition `q < p`. -/
lemma betaPredScaleMeshExponent_neg_iff
    (h_p : 1 < p) (h_q : 1 < q) :
    1 / p - 1 / q < 0 ↔ q < p := by
  have hp_pos : 0 < p := by
    linarith
  have hq_pos : 0 < q := by
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hpq_pos : 0 < p * q := mul_pos hp_pos hq_pos
  have hrewrite : 1 / p - 1 / q = (q - p) / (p * q) := by
    field_simp [hp_ne, hq_ne]
  rw [hrewrite]
  constructor
  · intro hneg
    by_contra hqp
    have hnonneg : 0 ≤ (q - p) / (p * q) := by
      refine div_nonneg ?_ hpq_pos.le
      exact sub_nonneg.mpr (le_of_not_gt hqp)
    linarith
  · intro hqp
    exact div_neg_of_neg_of_pos (sub_neg.mpr hqp) hpq_pos

/-- Helper for Theorem 7.29: the exponent governing `(n.succ : ℝ) * h_n` on
the `β_pred` scale is always positive under the standing Chapter 7 positivity
assumptions. -/
lemma betaPredScaleMeshMulExponent_pos
    (h_p : 1 < p) (h_q : 1 < q) :
    0 < 1 + (1 / p - 1 / q) := by
  have hp_inv_pos : 0 < 1 / p := by
    positivity
  have hq_inv_lt_one : 1 / q < 1 := by
    have hq_pos : 0 < q := by
      linarith
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    field_simp [hq_ne]
    linarith
  linarith

/-- Helper for Theorem 7.29: on the fixed `t * β_pred` scale, the predictive
objective factors into the Chapter 7 weighted bracket times the positive root
value at `β_pred`. -/
lemma predictiveObjective_atScaledBeta_eq_bracket_mul_rootValue
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    TikhonovPredictiveRisk.objective b c p q σ n.succ
        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) =
      (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
        (TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
          (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) ^ ((q - 1) / p)) := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  have hp_pos : 0 < p := by
    linarith
  have hβ_pos : 0 < β := by
    -- The predictive benchmark stays in the positive admissible region.
    dsimp [β]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have hC1_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC1 b c p q :=
    predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated
  have hC2_pos :
      0 < TikhonovPredictiveRisk.predictiveRiskC2 c p :=
    predictiveRiskC2_pos c p h_c h_p
  let npos : ℕ+ := ⟨n.succ, Nat.succ_pos n⟩
  have hroot :
      TikhonovPredictiveRisk.BetaPredRootEquation b c p q σ n.succ β := by
    -- Use the earlier benchmark root equation at the shifted positive size `n.succ`.
    dsimp [β, npos]
    exact
      TikhonovPredictiveRisk.betaPred_rootEquation
        b c p q σ hC1_pos hC2_pos hp_pos h_q h_σ npos
  have hroot_scaled :
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n.succ : ℝ)) * β ^ (-(1 / p)) =
        (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    -- Rewrite the benchmark root equation so the variance term is ready to factor.
    rw [TikhonovPredictiveRisk.betaPredRootEquation_iff] at hroot
    calc
      TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n.succ : ℝ)) * β ^ (-(1 / p))
          =
            ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ (q / p)) *
              β ^ (-(1 / p)) := by
                rw [← hroot]
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              (β ^ (q / p) * β ^ (-(1 / p))) := by
                ring
      _ =
            (q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
              β ^ ((q - 1) / p) := by
                rw [← Real.rpow_add hβ_pos]
                congr 2
                ring
  -- Rewrite the scaled objective at `α = t * β_pred` and factor out the positive root value.
  rw [TikhonovPredictiveRisk.objective_def]
  calc
    TikhonovPredictiveRisk.predictiveRiskC1 b c p q * (t * β) ^ ((q - 1) / p) +
        TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n.succ : ℝ)) *
          (t * β) ^ (-(1 / p))
        =
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
          (β ^ ((q - 1) / p) * t ^ ((q - 1) / p)) +
        TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n.succ : ℝ)) *
          (β ^ (-(1 / p)) * t ^ (-(1 / p))) := by
            rw [show t * β = β * t by ring]
            rw [Real.mul_rpow hβ_pos.le h_t.le]
            rw [Real.mul_rpow hβ_pos.le h_t.le]
    _ =
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
          t ^ ((q - 1) / p) +
        (TikhonovPredictiveRisk.predictiveRiskC2 c p * ((σ ^ 2) / (n.succ : ℝ)) *
          β ^ (-(1 / p))) * t ^ (-(1 / p)) := by
            ring
    _ =
      TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p) *
          t ^ ((q - 1) / p) +
        ((q - 1) * TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
          β ^ ((q - 1) / p)) * t ^ (-(1 / p)) := by
            rw [hroot_scaled]
    _ =
      (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
        (TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
            ring

/-- Helper for Theorem 7.29: at the predictive benchmark itself, the weighted
bracket collapses to `q`. -/
lemma predictiveObjective_atBetaPred_eq_q_mul_rootValue
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ) :
    TikhonovPredictiveRisk.objective b c p q σ n.succ
        (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) =
      q *
        (TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
          (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) ^ ((q - 1) / p)) := by
  -- Specialize the fixed-scale factorization to `t = 1`.
  simpa using
    predictiveObjective_atScaledBeta_eq_bracket_mul_rootValue
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated (t := 1) (by positivity) n

/-- Helper for Theorem 7.29: every fixed positive scale `t ≠ 1` is strictly
worse than `β_pred` for the predictive objective. -/
lemma predictiveObjective_atBetaPred_lt_atScaledBeta
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (h_t_ne : t ≠ 1) (n : ℕ) :
    TikhonovPredictiveRisk.objective b c p q σ n.succ
        (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) <
      TikhonovPredictiveRisk.objective b c p q σ n.succ
        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  let pref :=
    TikhonovPredictiveRisk.predictiveRiskC1 b c p q * β ^ ((q - 1) / p)
  have hp_pos : 0 < p := by
    linarith
  have hβ_pos : 0 < β := by
    -- The predictive benchmark remains positive at every shifted size `n.succ`.
    dsimp [β]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have hpref_pos : 0 < pref := by
    -- The common factor in both fixed-scale objective values is strictly positive.
    dsimp [pref]
    exact mul_pos
      (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated)
      (Real.rpow_pos_of_pos hβ_pos _)
  have hbracket_ge :
      q ≤ t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) :=
    predictiveObjectiveBracket_ge hp_pos h_q h_t
  have hbracket_ne :
      t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) ≠ q := by
    -- Equality of the Chapter 7 bracket would force the excluded scale `t = 1`.
    intro h_eq
    exact h_t_ne ((predictiveObjectiveBracket_eq_iff hp_pos h_q h_t).mp h_eq)
  have hbracket_gt :
      q < t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p)) :=
    lt_of_le_of_ne hbracket_ge (by
      intro h_eq
      exact hbracket_ne h_eq.symm)
  -- Compare the benchmark value and the fixed-scale value after factoring out
  -- the same positive root term.
  rw [predictiveObjective_atBetaPred_eq_q_mul_rootValue
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated n]
  rw [predictiveObjective_atScaledBeta_eq_bracket_mul_rootValue
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
  exact mul_lt_mul_of_pos_right hbracket_gt hpref_pos

/-- Helper for Theorem 7.29: a positive minimizing family for the expected GCV
objective has zero derivative at each minimizer. -/
lemma expectedObjectiveDeriv_zero_of_optimalFamily
    {alphaV : ℕ → ℝ}
    (h_alphaV_pos : ∀ n, alphaV n ∈ Set.Ioi (0 : ℝ))
    (h_alphaV :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K R fTrue η)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        alphaV) :
    ∀ n, deriv (expectedObjective μ K R fTrue η n) (alphaV n) = 0 := by
  have h_alphaV_min :=
    (ParameterChoice.isOptimalParameterFamily_iff
      (expectedObjective μ K R fTrue η)
      (fun _ ↦ Set.Ioi (0 : ℝ))
      alphaV).1 h_alphaV
  intro n
  have h_localMinOn :
      IsLocalMinOn
        (expectedObjective μ K R fTrue η n)
        (Set.Ioi (0 : ℝ))
        (alphaV n) := by
    -- Localize the global minimizer on the admissible positive half-line.
    exact (h_alphaV_min n).localize
  have h_localMin :
      IsLocalMin (expectedObjective μ K R fTrue η n) (alphaV n) := by
    -- The positivity hypothesis places the minimizer in the interior of `Ioi 0`.
    exact h_localMinOn.isLocalMin (isOpen_Ioi.mem_nhds (h_alphaV_pos n))
  -- Fermat's theorem turns the interior local minimizer into the vanishing derivative.
  exact h_localMin.deriv_eq_zero

/-- Helper for Theorem 7.29: rescaling the expected GCV objective by the
predictive benchmark `β_pred` only contributes the constant chain-rule factor
`β_pred`. -/
lemma scaledExpectedObjective_deriv_eq_betaPred_mul
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ) (t : ℝ) :
    deriv
        (fun u : ℝ ↦
          expectedObjective μ K R fTrue η n
            (u * TikhonovPredictiveRisk.betaPred b c p q σ n.succ))
        t =
      TikhonovPredictiveRisk.betaPred b c p q σ n.succ *
        deriv (expectedObjective μ K R fTrue η n)
          (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  have hβ_pos : 0 < β := by
    -- The predictive benchmark stays strictly positive at every shifted size.
    dsimp [β]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hgoal :
      deriv (fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β)) t =
        deriv (expectedObjective μ K R fTrue η n) (t * β) * β := by
    have hcomp_eq :
        (fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β)) =
          expectedObjective μ K R fTrue η n ∘ fun u : ℝ ↦ u * β := by
      -- Record the scaled objective as an actual composition before using the chain rule.
      funext u
      rfl
    rw [hcomp_eq]
    by_cases hf : DifferentiableAt ℝ (expectedObjective μ K R fTrue η n) (t * β)
    · have hlin : DifferentiableAt ℝ (fun u : ℝ ↦ u * β) t := by
        -- The rescaling map is affine-linear, hence differentiable everywhere.
        simpa [mul_comm] using (hasDerivAt_const_mul (x := t) β).differentiableAt
      -- Differentiate the exact composition once the inner scaling map is explicit.
      simpa using deriv_comp t hf hlin
    · have hcomp_not :
        ¬ DifferentiableAt ℝ
          (expectedObjective μ K R fTrue η n ∘ fun u : ℝ ↦ u * β)
          t := by
        intro hcomp
        have hcomp_lambda :
            DifferentiableAt ℝ
              (fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β))
              t := by
          -- Rewrite back to the direct scaled family before composing with the inverse map.
          simpa only [hcomp_eq] using hcomp
        have hdiv : DifferentiableAt ℝ (fun u : ℝ ↦ u / β) (t * β) := by
          -- The inverse scaling map is differentiable because `β_pred ≠ 0`.
          simpa [div_eq_mul_inv] using
            (hasDerivAt_mul_const (x := t * β) β⁻¹).differentiableAt
        have hcomp' :
            DifferentiableAt ℝ
                (fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β))
                ((t * β) / β) := by
          have hpoint : (t * β) / β = t := by
            field_simp [hβ_ne]
          -- Rewrite the evaluation point so the inverse rescaling can be composed back.
          simpa [hpoint] using hcomp_lambda
        have hback :
            DifferentiableAt ℝ
                (((fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β)) ∘
                    fun u : ℝ ↦ u / β))
                (t * β) := by
          -- Composing with the inverse scaling recovers the unscaled objective.
          exact hcomp'.comp (t * β) hdiv
        have heq :
              ((fun u : ℝ ↦ expectedObjective μ K R fTrue η n (u * β)) ∘
                  fun u : ℝ ↦ u / β) =
                expectedObjective μ K R fTrue η n := by
          -- The two rescalings cancel pointwise because `β_pred ≠ 0`.
          funext u
          apply congrArg (expectedObjective μ K R fTrue η n)
          field_simp [hβ_ne]
        have hback' : DifferentiableAt ℝ (expectedObjective μ K R fTrue η n) (t * β) := by
          simpa only [heq] using hback
        exact hf hback'
      -- If the outer objective is not differentiable, both derivatives are `0` by definition.
      rw [deriv_zero_of_not_differentiableAt hcomp_not, deriv_zero_of_not_differentiableAt hf]
      ring
  simpa [β, mul_comm] using hgoal

/-- Helper for Theorem 7.29: the predictive benchmark scale
`t * β_pred(n.succ)` is always a positive admissible parameter. -/
lemma expectedObjective_scaledBeta_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 <
      t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ := by
  -- The scaled parameter is a product of the positive scale `t` and the
  -- positive predictive benchmark `β_pred`.
  exact mul_pos h_t
    (betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
      ⟨n.succ, Nat.succ_pos n⟩)

/-- Helper for Theorem 7.29: specializing the exact mode-profile quotient to
the `t * β_pred` scale only substitutes the scaled parameter into the existing
finite-sum formula. -/
lemma expectedObjective_atScaledBeta_eq_modeProfileQuotient
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    expectedObjective μ K R fTrue η n
        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) =
      ((1 / (n.succ : ℝ)) *
          ∑ k ∈ Finset.range n.succ,
            (b *
                (((n.succ : ℝ) *
                    (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) ^ 2) /
              c) *
              (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
                (1 +
                    (((n.succ : ℝ) *
                          (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                        c) *
                      (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2 +
        (σ ^ 2 / (n.succ : ℝ)) *
          ∑ k ∈ Finset.range n.succ,
            (((((n.succ : ℝ) *
                    (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                  c) ^ 2) *
                (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
              (1 +
                  (((n.succ : ℝ) *
                        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                      c) *
                    (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2) /
        ((1 -
          (1 /
              (((n.succ : ℝ) *
                    ((((n.succ : ℝ) *
                            (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                          c) ^
                        (1 / p)))) *
            KernelMoment.quadratureSum p 1 0 n.succ
              ((((n.succ : ℝ) *
                        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                      c) ^
                    (1 / p)))) ^ 2) := by
  -- Specialize the already-proved exact quotient formula to the scaled
  -- parameter `α = t * β_pred`.
  exact
    expectedObjective_eq_modeProfileQuotient
      (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
      (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_c h_p
      (α := t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)
      (expectedObjective_scaledBeta_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t n)
      h_white h_svd h_tikhonov h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay

/-- Helper for Theorem 7.29: the exact denominator defect in the scaled
mode-profile quotient stays strictly positive, so the differentiated quotient
never crosses a singular denominator on the positive `β_pred` scale. -/
lemma expectedObjectiveScaledDefect_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 <
      1 -
        (1 /
            (((n.succ : ℝ) *
                  ((((n.succ : ℝ) *
                          (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                        c) ^
                      (1 / p)))) *
          KernelMoment.quadratureSum p 1 0 n.succ
            ((((n.succ : ℝ) *
                      (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                    c) ^
                  (1 / p))) := by
  let h : ℝ :=
    ((((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c) ^
      (1 / p))
  let term : Fin n.succ → ℝ := fun i ↦
    ((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
      (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p)
  have h_hpos : 0 < h := by
    -- The scaled mesh inherits positivity from the positive scaled parameter.
    dsimp [h]
    positivity [expectedObjective_scaledBeta_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
  have h_average :
      (1 / (n.succ : ℝ)) * ∑ i : Fin n.succ, term i =
        1 - (1 / (((n.succ : ℝ) * h))) * KernelMoment.quadratureSum p 1 0 n.succ h := by
    -- Rewrite the defect as the averaged positive complement profile.
    simpa [term] using
      (averageComplement_eq_one_sub_kernelMoment (n := n) (p := p) (h := h) h_hpos)
  have hterm_zero_pos : 0 < term 0 := by
    -- The first complement term is already strictly positive.
    dsimp [term]
    positivity
  have hsum_ge : term 0 ≤ ∑ i : Fin n.succ, term i := by
    -- The positive first term is bounded by the whole finite sum.
    exact
      Finset.single_le_sum
        (fun i hi ↦ by
          show 0 ≤ term i
          dsimp [term]
          positivity)
        (by simp : (0 : Fin n.succ) ∈ (Finset.univ : Finset (Fin n.succ)))
  have hsum_pos : 0 < ∑ i : Fin n.succ, term i := by
    -- A finite sum of nonnegative terms is positive once one explicit term is.
    exact lt_of_lt_of_le hterm_zero_pos hsum_ge
  have h_average_pos :
      0 < (1 / (n.succ : ℝ)) * ∑ i : Fin n.succ, term i := by
    -- The averaging factor over `Fin n.succ` is also positive.
    exact mul_pos (by positivity) hsum_pos
  have htarget :
      0 < 1 - (1 / (((n.succ : ℝ) * h))) * KernelMoment.quadratureSum p 1 0 n.succ h := by
    -- Replace the defect by the positive averaged complement expression.
    rw [← h_average]
    exact h_average_pos
  simpa [h] using htarget

/-- Helper for Theorem 7.29: the scaled mesh parameter attached to the
normalized family `α = t * β_pred(n.succ)`. -/
abbrev scaledMesh
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c) ^
    (1 / p))

/-- Helper for Theorem 7.29: the exact denominator defect in the scaled
mode-profile quotient. -/
abbrev scaledExpectedObjectiveDefect
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  1 -
    (1 / (((n.succ : ℝ) * scaledMesh b c p q σ n t))) *
      KernelMoment.quadratureSum p 1 0 n.succ
        (scaledMesh b c p q σ n t)

/-- Helper for Theorem 7.29: the bias-side numerator in the exact scaled
mode-profile quotient. -/
abbrev scaledExpectedObjectiveBias
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 / (n.succ : ℝ)) *
    ∑ k ∈ Finset.range n.succ,
      (b * (((n.succ : ℝ) *
          (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) ^ 2) / c) *
        (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
          (1 +
              (((n.succ : ℝ) *
                    (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                  c) *
                (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2

/-- Helper for Theorem 7.29: the variance-side numerator in the exact scaled
mode-profile quotient. -/
abbrev scaledExpectedObjectiveVariance
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (σ ^ 2 / (n.succ : ℝ)) *
    ∑ k ∈ Finset.range n.succ,
      (((((n.succ : ℝ) *
              (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
            c) ^ 2) *
          (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
        (1 +
            (((n.succ : ℝ) *
                  (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) /
                c) *
              (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2

/-- Helper for Theorem 7.29: the exact scaled mode-profile quotient obtained
after substituting `α = t * β_pred(n.succ)`. -/
abbrev scaledExpectedObjectiveQuotient
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (scaledExpectedObjectiveBias b c p q σ n t +
      scaledExpectedObjectiveVariance b c p q σ n t) /
    (scaledExpectedObjectiveDefect b c p q σ n t) ^ 2

/-- Helper for Theorem 7.29: the mesh-only denominator defect used by the
`h`-variable quotient route. -/
abbrev meshProfileDefect
    (p : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  1 -
    (1 / (((n.succ : ℝ) * h))) *
      KernelMoment.quadratureSum p 1 0 n.succ h

/-- Helper for Theorem 7.29: the bias-side numerator written entirely in the
mesh variable `h`. -/
abbrev meshProfileBias
    (b c p q : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  (1 / (n.succ : ℝ)) *
    ∑ k ∈ Finset.range n.succ,
      (b * c * h ^ (2 * p)) *
        (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
          (1 + h ^ p * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2

/-- Helper for Theorem 7.29: the variance-side numerator written entirely in
the mesh variable `h`. -/
abbrev meshProfileVariance
    (p σ : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  (σ ^ 2 / (n.succ : ℝ)) *
    ∑ k ∈ Finset.range n.succ,
      (h ^ (2 * p) * (((k + 1 : ℕ) : ℝ) ^ (2 * p))) /
        (1 + h ^ p * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2

/-- Helper for Theorem 7.29: the exact scaled expected-GCV quotient expressed
only through the mesh variable `h`. -/
abbrev meshProfileQuotient
    (b c p q σ : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  (meshProfileBias b c p q n h + meshProfileVariance p σ n h) /
    (meshProfileDefect p n h) ^ 2

/-- Helper for Theorem 7.29: at positive mesh scale `h`, the bias-side
mesh profile is a fixed power prefactor times a finite sum of
`KernelMoment.integrand`. -/
lemma meshProfileBias_eq_integrandSum
    (b c p q : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    meshProfileBias b c p q n h =
      (b * c * h ^ (p + q) / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          KernelMoment.integrand p 2 (p - q) (((k + 1 : ℕ) : ℝ) * h) := by
  -- Rewrite the bias-side mode profile in the same `KernelMoment.integrand`
  -- spelling used by the asymptotic quadrature API.
  rw [meshProfileBias]
  calc
    (1 / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          b * c * h ^ (2 * p) * (((k + 1 : ℕ) : ℝ) ^ (p - q)) /
            (1 + h ^ p * (((k + 1 : ℕ) : ℝ) ^ p)) ^ 2
        =
      (1 / (n.succ : ℝ)) *
        ((b * c * h ^ (p + q)) *
          ∑ k ∈ Finset.range n.succ,
            KernelMoment.integrand p 2 (p - q) (((k + 1 : ℕ) : ℝ) * h)) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_nonneg : 0 ≤ (((k + 1 : ℕ) : ℝ)) := by
            positivity
          have hmul_s :
              ((((k + 1 : ℕ) : ℝ) * h) ^ (p - q)) =
                (((k + 1 : ℕ) : ℝ) ^ (p - q)) * h ^ (p - q) := by
            rw [Real.mul_rpow hk_nonneg h_h.le]
          have hmul_p :
              ((((k + 1 : ℕ) : ℝ) * h) ^ p) =
                (((k + 1 : ℕ) : ℝ) ^ p) * h ^ p := by
            rw [Real.mul_rpow hk_nonneg h_h.le]
          -- Match the pointwise mode profile with the kernel integrand.
          rw [KernelMoment.integrand_def, hmul_s, hmul_p]
          have hpow :
              h ^ (2 * p) = h ^ (p + q) * h ^ (p - q) := by
            rw [← Real.rpow_add h_h]
            congr 1
            ring
          rw [hpow]
          ring
    _ =
      (b * c * h ^ (p + q) / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          KernelMoment.integrand p 2 (p - q) (((k + 1 : ℕ) : ℝ) * h) := by
            ring

/-- Helper for Theorem 7.29: at positive mesh scale `h`, the variance-side
mesh profile is a finite sum of `KernelMoment.integrand` with exponent `2p`. -/
lemma meshProfileVariance_eq_integrandSum
    (p σ : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    meshProfileVariance p σ n h =
      (σ ^ 2 / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          KernelMoment.integrand p 2 (2 * p) (((k + 1 : ℕ) : ℝ) * h) := by
  -- Rewrite the variance profile into the same integrand language used by the
  -- Proposition 7.19 asymptotic API.
  rw [meshProfileVariance]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_nonneg : 0 ≤ (((k + 1 : ℕ) : ℝ)) := by
    positivity
  have hmul_two_p :
      ((((k + 1 : ℕ) : ℝ) * h) ^ (2 * p)) =
        (((k + 1 : ℕ) : ℝ) ^ (2 * p)) * h ^ (2 * p) := by
    rw [Real.mul_rpow hk_nonneg h_h.le]
  have hmul_p :
      ((((k + 1 : ℕ) : ℝ) * h) ^ p) =
        (((k + 1 : ℕ) : ℝ) ^ p) * h ^ p := by
    rw [Real.mul_rpow hk_nonneg h_h.le]
  -- Normalize the shifted mesh profile pointwise.
  rw [KernelMoment.integrand_def, hmul_two_p, hmul_p]
  ring

/-- Helper for Theorem 7.29: the defect profile is `1` minus the average of
the `KernelMoment.integrand` terms with `(j, s) = (1, 0)`. -/
lemma meshProfileDefect_eq_one_sub_integrandSum
    (p : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    meshProfileDefect p n h =
      1 - (1 / (n.succ : ℝ)) *
        ∑ k ∈ Finset.range n.succ,
          KernelMoment.integrand p 1 0 (((k + 1 : ℕ) : ℝ) * h) := by
  have h_nsucc_ne : (n.succ : ℝ) ≠ 0 := by
    positivity
  have h_nsucc_h_ne : ((n.succ : ℝ) * h) ≠ 0 := by
    positivity
  -- Expand the quadrature sum once, then cancel the common `h` factor in
  -- front of each integrand term.
  rw [meshProfileDefect, quadratureSum_eq_sumRangeSeries_local]
  rw [Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  field_simp [h_nsucc_ne, h_h.ne', h_nsucc_h_ne]

/-- Helper for Theorem 7.29: the mesh-profile defect is strictly positive at
every positive mesh scale. -/
lemma meshProfileDefect_pos
    (p : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    0 < meshProfileDefect p n h := by
  let term : Fin n.succ → ℝ := fun i ↦
    (((h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p) /
      (1 + (h ^ p) * ((i.1.succ : ℕ) : ℝ) ^ p))
  have h_eq :
      meshProfileDefect p n h =
        (1 / (n.succ : ℝ)) *
          ∑ i : Fin n.succ, term i := by
    -- Reuse the earlier average-complement identity as the positivity normal form.
    simpa [meshProfileDefect, term] using
      (averageComplement_eq_one_sub_kernelMoment (n := n) (p := p) (h := h) h_h).symm
  have hterm_zero_pos : 0 < term 0 := by
    -- The first averaged complement term is already strictly positive.
    dsimp [term]
    positivity
  have hsum_ge : term 0 ≤ ∑ i : Fin n.succ, term i := by
    -- One positive term is bounded by the whole nonnegative finite sum.
    exact
      Finset.single_le_sum
        (fun i hi ↦ by
          show 0 ≤ term i
          dsimp [term]
          positivity)
        (by
          simp : (0 : Fin n.succ) ∈ (Finset.univ : Finset (Fin n.succ)))
  have hsum_pos : 0 < ∑ i : Fin n.succ, term i := by
    -- Positivity of one explicit term propagates to the whole average sum.
    exact lt_of_lt_of_le hterm_zero_pos hsum_ge
  have havg_pos : 0 < (1 / (n.succ : ℝ)) * ∑ i : Fin n.succ, term i := by
    -- The averaging coefficient over `Fin n.succ` is positive.
    exact mul_pos (by positivity) hsum_pos
  rw [h_eq]
  exact havg_pos

/-- Helper for Theorem 7.29: the scaled mesh stays strictly positive on the
positive `β_pred` scale. -/
lemma scaledMesh_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 < scaledMesh b c p q σ n t := by
  -- Expand the mesh and use positivity of the scaled benchmark parameter.
  dsimp [scaledMesh]
  positivity [expectedObjective_scaledBeta_pos
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]

/-- Helper for Theorem 7.29: raising the scaled mesh back to the power `p`
recovers the exact finite-dimensional Tikhonov scale `((n * α) / c)`. -/
lemma scaledMesh_rpow_p_eq
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    (scaledMesh b c p q σ n t) ^ p =
      ((n.succ : ℝ) *
          (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c := by
  let scale : ℝ :=
    ((n.succ : ℝ) * (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) / c
  have hscale_pos : 0 < scale := by
    -- The scaled finite-dimensional Tikhonov parameter is positive.
    dsimp [scale]
    positivity [betaPred_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated ⟨n.succ, Nat.succ_pos n⟩]
  have hp_ne : p ≠ 0 := by
    linarith
  -- Expand the mesh definition and cancel the reciprocal exponent `1 / p`.
  calc
    (scaledMesh b c p q σ n t) ^ p = (scale ^ (1 / p)) ^ p := by
      rfl
    _ = scale ^ ((1 / p) * p) := by
      rw [Real.rpow_mul hscale_pos.le]
    _ = scale ^ (1 : ℝ) := by
      congr 1
      field_simp [hp_ne]
    _ = scale := by
      rw [Real.rpow_one]

/-- Helper for Theorem 7.29: the exact scaled denominator defect is already
the mesh-profile defect evaluated at `h = scaledMesh`. -/
lemma scaledExpectedObjectiveDefect_eq_meshProfileDefect
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) :
    scaledExpectedObjectiveDefect b c p q σ n t =
      meshProfileDefect p n (scaledMesh b c p q σ n t) := by
  -- The denominator defect depends on `t` only through the mesh parameter.
  rfl

/-- Helper for Theorem 7.29: the exact scaled bias numerator can be rewritten
as a mesh-only profile evaluated at `h = scaledMesh`. -/
lemma scaledExpectedObjectiveBias_eq_meshProfileBias
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    scaledExpectedObjectiveBias b c p q σ n t =
      meshProfileBias b c p q n (scaledMesh b c p q σ n t) := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  let scale : ℝ := ((n.succ : ℝ) * (t * β)) / c
  have hmesh_pos :
      0 < scaledMesh b c p q σ n t :=
    scaledMesh_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have hmesh_p :
      (scaledMesh b c p q σ n t) ^ p = scale := by
    -- Replace the mesh power by the exact Tikhonov scale before comparing terms.
    simpa [β, scale] using
      scaledMesh_rpow_p_eq
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have hmesh_two_p :
      (scaledMesh b c p q σ n t) ^ (2 * p) = scale ^ 2 := by
    -- The `2p`-power is just the square of the recovered scale.
    calc
      (scaledMesh b c p q σ n t) ^ (2 * p)
          = (scaledMesh b c p q σ n t) ^ (p + p) := by
              congr 1
              ring
      _ =
          (scaledMesh b c p q σ n t) ^ p *
            (scaledMesh b c p q σ n t) ^ p := by
              rw [Real.rpow_add hmesh_pos]
      _ = scale * scale := by rw [hmesh_p]
      _ = scale ^ 2 := by ring
  have hcoeff :
      (b * (((n.succ : ℝ) * (t * β)) ^ 2) / c) =
        b * c * scale ^ 2 := by
    -- Match the old coefficient with the mesh-only coefficient through `scale = (nα)/c`.
    dsimp [scale]
    field_simp [h_c.ne']
  -- Rewrite the full numerator term-by-term in the mesh variable.
  rw [scaledExpectedObjectiveBias, meshProfileBias]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [hmesh_p, hmesh_two_p, hcoeff]

/-- Helper for Theorem 7.29: the exact scaled variance numerator can be
rewritten as a mesh-only profile evaluated at `h = scaledMesh`. -/
lemma scaledExpectedObjectiveVariance_eq_meshProfileVariance
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    scaledExpectedObjectiveVariance b c p q σ n t =
      meshProfileVariance p σ n (scaledMesh b c p q σ n t) := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  let scale : ℝ := ((n.succ : ℝ) * (t * β)) / c
  have hmesh_pos :
      0 < scaledMesh b c p q σ n t :=
    scaledMesh_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have hmesh_p :
      (scaledMesh b c p q σ n t) ^ p = scale := by
    -- Replace the mesh power by the exact Tikhonov scale before comparing terms.
    simpa [β, scale] using
      scaledMesh_rpow_p_eq
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have hmesh_two_p :
      (scaledMesh b c p q σ n t) ^ (2 * p) = scale ^ 2 := by
    -- The `2p`-power is the square of the same recovered scale.
    calc
      (scaledMesh b c p q σ n t) ^ (2 * p)
          = (scaledMesh b c p q σ n t) ^ (p + p) := by
              congr 1
              ring
      _ =
          (scaledMesh b c p q σ n t) ^ p *
            (scaledMesh b c p q σ n t) ^ p := by
              rw [Real.rpow_add hmesh_pos]
      _ = scale * scale := by rw [hmesh_p]
      _ = scale ^ 2 := by ring
  -- Rewrite the full numerator term-by-term in the mesh variable.
  rw [scaledExpectedObjectiveVariance, meshProfileVariance]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [hmesh_p, hmesh_two_p]

/-- Helper for Theorem 7.29: the exact scaled expected-GCV quotient can be
rewritten as a mesh-only quotient evaluated at `h = scaledMesh`. -/
lemma scaledExpectedObjectiveQuotient_eq_meshProfileQuotient
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    scaledExpectedObjectiveQuotient b c p q σ n t =
      meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n t) := by
  -- Route correction: move the exact scaled quotient into one stable spelling
  -- world before differentiating or analyzing signs.
  rw [scaledExpectedObjectiveQuotient, meshProfileQuotient]
  rw [scaledExpectedObjectiveBias_eq_meshProfileBias
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
  rw [scaledExpectedObjectiveVariance_eq_meshProfileVariance
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]

/-- Helper for Theorem 7.29: the scaled mesh is exactly the explicit
constant-power law already isolated from `β_pred`. -/
lemma scaledMesh_eq_constant_mul_power
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    scaledMesh b c p q σ n t =
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
          (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (n.succ : ℝ) ^ (1 / p - 1 / q) := by
  -- This is just the earlier explicit benchmark-scale mesh normalization
  -- rewritten through the local `scaledMesh` abbreviation.
  simpa [scaledMesh] using
    betaPredScaleMesh_eq_constant_mul_power
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n

/-- Helper for Theorem 7.29: differentiating the scaled mesh contributes the
simple prefactor `h_n(t) / (p * t)`. -/
lemma scaledMesh_hasDerivAt
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    HasDerivAt (fun u : ℝ ↦ scaledMesh b c p q σ n u)
      (scaledMesh b c p q σ n t / (p * t)) t := by
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  let A : ℝ := ((n.succ : ℝ) * β) / c
  have hβ_pos : 0 < β := by
    -- The predictive benchmark stays positive at every shifted data size.
    dsimp [β]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have hA_pos : 0 < A := by
    -- The affine scale inside the mesh is positive as well.
    dsimp [A]
    positivity
  have hp_ne : p ≠ 0 := by
    linarith
  have ht_ne : t ≠ 0 := h_t.ne'
  have hAt_pos : 0 < A * t := mul_pos hA_pos h_t
  have hlin : HasDerivAt (fun u : ℝ ↦ A * u) A t := by
    -- The inner scaling map is affine-linear.
    simpa [A] using (hasDerivAt_const_mul (x := t) A)
  have hrpow :
      HasDerivAt (fun u : ℝ ↦ (A * u) ^ (1 / p))
        (A * (1 / p) * (A * t) ^ (1 / p - 1)) t := by
    -- Differentiate the positive real power once the affine scale is explicit.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hlin.rpow_const (p := 1 / p) (Or.inl (mul_ne_zero hA_pos.ne' ht_ne))
  have hderiv :
      A * (1 / p) * (A * t) ^ (1 / p - 1) =
        scaledMesh b c p q σ n t / (p * t) := by
    -- Rewrite the derivative into the normalized mesh form used later by the
    -- quotient-rule interface.
    have hpow :
        (A * t) * (A * t) ^ (1 / p - 1) = (A * t) ^ (1 / p) := by
      calc
        (A * t) * (A * t) ^ (1 / p - 1)
            = (A * t) ^ (1 : ℝ) * (A * t) ^ (1 / p - 1) := by
                rw [Real.rpow_one]
        _ = (A * t) ^ (1 + (1 / p - 1)) := by
              rw [← Real.rpow_add hAt_pos]
        _ = (A * t) ^ (1 / p) := by
              congr 1
              ring
    calc
      A * (1 / p) * (A * t) ^ (1 / p - 1)
          = (1 / (p * t)) * ((A * t) * (A * t) ^ (1 / p - 1)) := by
              field_simp [hp_ne, ht_ne]
      _ = (1 / (p * t)) * (A * t) ^ (1 / p) := by
            rw [hpow]
      _ = scaledMesh b c p q σ n t / (p * t) := by
            simp [scaledMesh, A, β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Convert the affine-power derivative back to the local mesh notation.
  convert hrpow using 1
  · ext u
    dsimp [scaledMesh, A, β]
    congr 1
    ring
  · exact hderiv.symm

/-- Helper for Theorem 7.29: dividing a quadrature sum by a positive mesh
factor recovers the bare range-sum of kernel integrands. -/
private lemma sumRangeIntegrand_eq_quadratureSum_div
    {p s h : ℝ} {j m : ℕ} (h_h : 0 < h) :
    (∑ k ∈ Finset.range m,
        KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)) =
      KernelMoment.quadratureSum p j s m h / h := by
  -- Expand the quadrature sum once and cancel the common positive factor `h`
  -- term by term.
  rw [quadratureSum_eq_sumRangeSeries_local, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  field_simp [h_h.ne']

/-- Helper for Theorem 7.29: multiplying `h^(a - 1)` by `h` recovers `h^a`
on the positive half-line. -/
private lemma rpow_sub_one_mul
    {h a : ℝ} (h_h : 0 < h) :
    h ^ (a - 1) * h = h ^ a := by
  -- Rewrite the trailing `h` as `h^1`, then merge the exponents once.
  calc
    h ^ (a - 1) * h = h ^ (a - 1) * h ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = h ^ ((a - 1) + 1) := by rw [← Real.rpow_add h_h]
    _ = h ^ a := by
          congr 1
          ring

/-- Helper for Theorem 7.29: the `j = 2` and `j = 3` kernel profiles satisfy
the one-step cancellation used in the bias and variance derivative formulas. -/
private lemma integrand_two_sub_three_eq_three
    {p s u : ℝ} (h_u : 0 < u) :
    KernelMoment.integrand p 2 s u -
        KernelMoment.integrand p 3 (s + p) u =
      KernelMoment.integrand p 3 s u := by
  have hden : 1 + u ^ p ≠ 0 := by
    positivity
  have hpow : u ^ (s + p) = u ^ s * u ^ p := by
    rw [← Real.rpow_add h_u]
  -- Clear the common denominator `(1 + u^p)^3` and collapse the numerator.
  rw [KernelMoment.integrand_def, KernelMoment.integrand_def, KernelMoment.integrand_def]
  field_simp [hden]
  rw [hpow]
  ring

/-- Helper for Theorem 7.29: summing the pointwise `j = 2` versus `j = 3`
cancellation yields the corresponding quadrature identity. -/
private lemma quadratureSum_two_sub_three_eq_three
    (p s : ℝ) (m : ℕ) {h : ℝ} (h_h : 0 < h) :
    KernelMoment.quadratureSum p 2 s m h -
        KernelMoment.quadratureSum p 3 (s + p) m h =
      KernelMoment.quadratureSum p 3 s m h := by
  -- Rewrite all three quadrature sums in the same finite-sum spelling before
  -- applying the pointwise integrand identity.
  rw [quadratureSum_eq_sumRangeSeries_local, quadratureSum_eq_sumRangeSeries_local,
    quadratureSum_eq_sumRangeSeries_local]
  calc
    ∑ k ∈ Finset.range m,
        h * KernelMoment.integrand p 2 s (((k + 1 : ℕ) : ℝ) * h) -
        ∑ k ∈ Finset.range m,
          h * KernelMoment.integrand p 3 (s + p) (((k + 1 : ℕ) : ℝ) * h)
        =
          ∑ k ∈ Finset.range m,
            (h * KernelMoment.integrand p 2 s (((k + 1 : ℕ) : ℝ) * h) -
              h * KernelMoment.integrand p 3 (s + p) (((k + 1 : ℕ) : ℝ) * h)) := by
            rw [← Finset.sum_sub_distrib]
    _ =
          ∑ k ∈ Finset.range m,
            h * KernelMoment.integrand p 3 s (((k + 1 : ℕ) : ℝ) * h) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk_pos : 0 < (((k + 1 : ℕ) : ℝ) * h) := by
                positivity
              calc
                h * KernelMoment.integrand p 2 s (((k + 1 : ℕ) : ℝ) * h) -
                    h * KernelMoment.integrand p 3 (s + p) (((k + 1 : ℕ) : ℝ) * h)
                    =
                      h *
                        (KernelMoment.integrand p 2 s (((k + 1 : ℕ) : ℝ) * h) -
                          KernelMoment.integrand p 3 (s + p) (((k + 1 : ℕ) : ℝ) * h)) := by
                            ring
                _ =
                      h * KernelMoment.integrand p 3 s (((k + 1 : ℕ) : ℝ) * h) := by
                            rw [integrand_two_sub_three_eq_three
                              (p := p) (s := s) (u := (((k + 1 : ℕ) : ℝ) * h)) hk_pos]

/-- Helper for Theorem 7.29: once the scaled kernel derivative is expanded at a
positive input, the product-rule numerator collapses to the clean balance
expression used throughout the derivative formulas. -/
private lemma scaledIntegrandSummand_balance_eq
    {p s a h : ℝ} {j : ℕ} (h_a : 0 < a) (h_h : 0 < h) :
    KernelMoment.integrand p j s (a * h) +
        h * a * KernelMoment.integrandDeriv p j s (a * h) =
      ((s + 1) * KernelMoment.integrand p j s (a * h)) -
        ((j : ℝ) * p) *
          KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
  have h_ah : 0 < a * h := by
    positivity
  have hsplit :=
    KernelMoment.integrandDeriv_eq_split (p := p) (j := j) (s := s) h_ah
  have hpow_s :
      (a * h) ^ (s - 1) * (h * a) = (a * h) ^ s := by
    rw [mul_comm h a, rpow_sub_one_mul (h := a * h) (a := s) h_ah]
  have hpow_sp :
      (a * h) ^ (s + p - 1) * (h * a) = (a * h) ^ (s + p) := by
    rw [mul_comm h a, rpow_sub_one_mul (h := a * h) (a := s + p) h_ah]
  have hmul_s :
      h * a * (s * (a * h) ^ (s - 1) / (1 + (a * h) ^ p) ^ j) =
        s * KernelMoment.integrand p j s (a * h) := by
    calc
      h * a * (s * (a * h) ^ (s - 1) / (1 + (a * h) ^ p) ^ j)
          = s * (((a * h) ^ (s - 1) * (h * a)) / (1 + (a * h) ^ p) ^ j) := by
              ring
      _ = s * ((a * h) ^ s / (1 + (a * h) ^ p) ^ j) := by
            rw [hpow_s]
      _ = s * KernelMoment.integrand p j s (a * h) := by
            rw [KernelMoment.integrand_def]
  have hmul_sp :
      h * a *
          (((j : ℝ) * p) * (a * h) ^ (s + p - 1) / (1 + (a * h) ^ p) ^ (j + 1)) =
        ((j : ℝ) * p) * KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
    calc
      h * a *
          (((j : ℝ) * p) * (a * h) ^ (s + p - 1) / (1 + (a * h) ^ p) ^ (j + 1))
          =
        ((j : ℝ) * p) * (((a * h) ^ (s + p - 1) * (h * a)) / (1 + (a * h) ^ p) ^ (j + 1)) := by
              ring
      _ = ((j : ℝ) * p) * ((a * h) ^ (s + p) / (1 + (a * h) ^ p) ^ (j + 1)) := by
            rw [hpow_sp]
      _ = ((j : ℝ) * p) * KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
            rw [KernelMoment.integrand_def]
  -- Expand the split derivative once, then rewrite the chain factor `h * a`
  -- back to the base point `a * h`.
  rw [hsplit]
  calc
    KernelMoment.integrand p j s (a * h) +
        h * a *
          (s * (a * h) ^ (s - 1) / (1 + (a * h) ^ p) ^ j -
            ((j : ℝ) * p) * (a * h) ^ (s + p - 1) / (1 + (a * h) ^ p) ^ (j + 1))
        =
      KernelMoment.integrand p j s (a * h) +
        s * KernelMoment.integrand p j s (a * h) -
          ((j : ℝ) * p) *
            KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
              rw [mul_sub, hmul_s, hmul_sp]
              ring
    _ =
      ((s + 1) * KernelMoment.integrand p j s (a * h)) -
        ((j : ℝ) * p) *
          KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
            ring

/-- Helper for Theorem 7.29: on the positive branch, the unstable product
`u * KernelMoment.integrand ... (a * u)` can be rewritten as a constant
multiple of the shifted kernel integrand. -/
private lemma scaledIntegrandSummand_eq_inv_mul_shiftedIntegrand
    {p s a u : ℝ} {j : ℕ} (h_a : 0 < a) (h_u : 0 < u) :
    u * KernelMoment.integrand p j s (a * u) =
      (1 / a) * KernelMoment.integrand p j (s + 1) (a * u) := by
  have h_au : 0 < a * u := by
    positivity
  have hpow :
      (a * u) ^ (s + 1) = (a * u) ^ s * (a * u) := by
    calc
      (a * u) ^ (s + 1) = (a * u) ^ (s + (1 : ℝ)) := by ring_nf
      _ = (a * u) ^ s * (a * u) ^ (1 : ℝ) := by rw [Real.rpow_add h_au]
      _ = (a * u) ^ s * (a * u) := by rw [Real.rpow_one]
  -- Route correction: rewrite the product summand before differentiating so
  -- the derivative stays in the stable `KernelMoment.integrand` spelling.
  rw [KernelMoment.integrand_def, KernelMoment.integrand_def]
  calc
    u * ((a * u) ^ s / (1 + (a * u) ^ p) ^ j)
        = (u * (a * u) ^ s) / (1 + (a * u) ^ p) ^ j := by
            ring
    _ =
        ((1 / a) * (a * u) ^ (s + 1)) / (1 + (a * u) ^ p) ^ j := by
          congr 1
          calc
            u * (a * u) ^ s = (1 / a) * (a * (u * (a * u) ^ s)) := by
              field_simp [h_a.ne']
            _ = (1 / a) * ((a * u) ^ s * (a * u)) := by
                  ring
            _ = (1 / a) * (a * u) ^ (s + 1) := by
                  rw [hpow]
    _ =
        (1 / a) * ((a * u) ^ (s + 1) / (1 + (a * u) ^ p) ^ j) := by
          ring

/-- Helper for Theorem 7.29: the bias-side raw derivative of
`h^r * Q(2, s)` collapses to the clean `Q(3, s)` normal form once the
quadrature cancellation is used. -/
private lemma quadraturePowMul_rawDeriv_eq
    {p r s h : ℝ} {m : ℕ} (h_h : 0 < h) (h_relation : r + s + 1 = 2 * p) :
    r * h ^ (r - 1) * KernelMoment.quadratureSum p 2 s m h +
        h ^ r *
          ((((s + 1) * KernelMoment.quadratureSum p 2 s m h) -
              (2 * p) * KernelMoment.quadratureSum p 3 (s + p) m h) / h) =
      (2 * p) * h ^ (r - 1) * KernelMoment.quadratureSum p 3 s m h := by
  let Q2 := KernelMoment.quadratureSum p 2 s m h
  let Q3 := KernelMoment.quadratureSum p 3 (s + p) m h
  have h_div : h ^ r / h = h ^ (r - 1) := by
    calc
      h ^ r / h = h ^ r * h⁻¹ := by rw [div_eq_mul_inv]
      _ = h ^ (r + -1) := by
            rw [← Real.rpow_neg_one h, ← Real.rpow_add h_h]
      _ = h ^ (r - 1) := by
            congr 1
  -- Pull the common factor `h^(r-1)` out of the raw product derivative first.
  calc
    r * h ^ (r - 1) * Q2 + h ^ r * ((((s + 1) * Q2) - (2 * p) * Q3) / h)
        = r * h ^ (r - 1) * Q2 + (h ^ r / h) * (((s + 1) * Q2) - (2 * p) * Q3) := by
            congr 1
            ring
    _ =
        r * h ^ (r - 1) * Q2 + h ^ (r - 1) * (((s + 1) * Q2) - (2 * p) * Q3) := by
          rw [h_div]
    _ =
        h ^ (r - 1) * (r * Q2 + (((s + 1) * Q2) - (2 * p) * Q3)) := by
          ring
    _ =
        h ^ (r - 1) * (((r + s + 1) * Q2) - (2 * p) * Q3) := by
          ring
    _ = h ^ (r - 1) * (((2 * p) * Q2) - (2 * p) * Q3) := by
          rw [h_relation]
    _ =
        h ^ (r - 1) * ((2 * p) *
          (KernelMoment.quadratureSum p 2 s m h -
            KernelMoment.quadratureSum p 3 (s + p) m h)) := by
          dsimp [Q2, Q3]
          ring
    _ =
        h ^ (r - 1) * ((2 * p) * KernelMoment.quadratureSum p 3 s m h) := by
          rw [quadratureSum_two_sub_three_eq_three (p := p) (s := s) (m := m) h_h]
    _ = (2 * p) * h ^ (r - 1) * KernelMoment.quadratureSum p 3 s m h := by
          ring

/-- Helper for Theorem 7.29: the raw quotient-rule derivative of `Q(j, s, h) / h`
has the stable numerator shape used in the variance and defect derivatives. -/
private lemma quadratureQuotientRawDeriv_eq
    {p s h : ℝ} {j m : ℕ} (h_h : 0 < h) :
    ((((((s + 1) * KernelMoment.quadratureSum p j s m h) -
            ((j : ℝ) * p) * KernelMoment.quadratureSum p (j + 1) (s + p) m h) / h) *
          h -
        KernelMoment.quadratureSum p j s m h) / h ^ 2) =
      (s * KernelMoment.quadratureSum p j s m h -
          ((j : ℝ) * p) * KernelMoment.quadratureSum p (j + 1) (s + p) m h) /
        h ^ 2 := by
  have h_hsq_ne : h ^ 2 ≠ 0 := by
    positivity
  -- Clear the stable denominator `h^2` once and simplify the remaining linear
  -- numerator exactly.
  field_simp [h_h.ne', h_hsq_ne]
  ring

/-- Helper for Theorem 7.29: each scaled kernel summand has the clean
balance derivative needed by the whole-quadrature recurrence. -/
private lemma integrandConstMul_hasDerivAt_owner
    {p s a h : ℝ} {j : ℕ} (h_a : 0 < a) (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ KernelMoment.integrand p j s (a * u))
      (a * KernelMoment.integrandDeriv p j s (a * h))
      h := by
  have h_ah : 0 < a * h := by
    positivity
  have h_mul : HasDerivAt (fun u : ℝ ↦ a * u) a h := by
    simpa using (hasDerivAt_const_mul (x := h) a)
  -- Route correction: cross the affine precomposition boundary once so the
  -- downstream mesh-profile derivatives stay in the owner spelling.
  have h_comp :
      HasDerivAt
        (((fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j) ∘ fun u : ℝ ↦ a * u))
        (KernelMoment.integrandDeriv p j s (a * h) * a)
        h := by
    simpa [Function.comp] using
      (KernelMoment.integrand_hasDerivAt_pos (p := p) (j := j) (s := s) (u := a * h) h_ah).comp h
        h_mul
  change HasDerivAt
      (((fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j) ∘ fun u : ℝ ↦ a * u))
      (a * KernelMoment.integrandDeriv p j s (a * h))
      h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_comp

/-- Helper for Theorem 7.29: each scaled kernel summand has the clean
balance derivative needed by the whole-quadrature recurrence. -/
private lemma scaledIntegrandSummand_hasDerivAt_pos
    {p s a h : ℝ} {j : ℕ} (h_a : 0 < a) (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ u * KernelMoment.integrand p j s (a * u))
      (((s + 1) * KernelMoment.integrand p j s (a * h)) -
        ((j : ℝ) * p) *
          KernelMoment.integrand p (j + 1) (s + p) (a * h))
      h := by
  have h_integrand :=
    integrandConstMul_hasDerivAt_owner
      (p := p) (j := j) (s := s) (a := a) (h := h) h_a h_h
  have h_prod : HasDerivAt
      (fun u : ℝ ↦ u * KernelMoment.integrand p j s (a * u))
      (KernelMoment.integrand p j s (a * h) +
        h * (a * KernelMoment.integrandDeriv p j s (a * h)))
      h := by
    -- Differentiate the product in owner spelling, leaving only the raw
    -- balance identity to normalize afterwards.
    change HasDerivAt
        (id * fun u : ℝ ↦ KernelMoment.integrand p j s (a * u))
        (KernelMoment.integrand p j s (a * h) +
          h * (a * KernelMoment.integrandDeriv p j s (a * h)))
        h
    simpa [id, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id h).mul h_integrand
  have h_value :
      KernelMoment.integrand p j s (a * h) + h * (a * KernelMoment.integrandDeriv p j s (a * h)) =
        ((s + 1) * KernelMoment.integrand p j s (a * h)) -
          ((j : ℝ) * p) *
            KernelMoment.integrand p (j + 1) (s + p) (a * h) := by
    simpa [mul_assoc] using
      scaledIntegrandSummand_balance_eq
        (p := p) (j := j) (s := s) (a := a) (h := h) h_a h_h
  exact h_value ▸ h_prod

/-- Helper for Theorem 7.29: differentiating `KernelMoment.quadratureSum` as a
whole yields the clean recurrence used by the mesh-profile derivative formulas. -/
lemma quadratureSum_hasDerivAt_pos
    {p s h : ℝ} {j m : ℕ} (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ KernelMoment.quadratureSum p j s m u)
      ((((s + 1) * KernelMoment.quadratureSum p j s m h) -
          ((j : ℝ) * p) * KernelMoment.quadratureSum p (j + 1) (s + p) m h) / h)
      h := by
  have hsum :
      HasDerivAt
        (fun u : ℝ ↦
          ∑ k ∈ Finset.range m,
            u * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * u))
        (∑ k ∈ Finset.range m,
          (((s + 1) * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)) -
            ((j : ℝ) * p) *
              KernelMoment.integrand p (j + 1) (s + p) (((k + 1 : ℕ) : ℝ) * h)))
        h := by
    -- Differentiate the `range m` spelling termwise.
    refine HasDerivAt.fun_sum ?_
    intro k hk
    have hk_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
      positivity
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (scaledIntegrandSummand_hasDerivAt_pos
        (p := p) (j := j) (s := s) (a := ((k + 1 : ℕ) : ℝ)) hk_pos h_h)
  have h_sum_main :
      (∑ k ∈ Finset.range m,
        KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)) =
      KernelMoment.quadratureSum p j s m h / h :=
    sumRangeIntegrand_eq_quadratureSum_div
      (p := p) (j := j) (s := s) (m := m) h_h
  have h_sum_shift :
      (∑ k ∈ Finset.range m,
        KernelMoment.integrand p (j + 1) (s + p) (((k + 1 : ℕ) : ℝ) * h)) =
      KernelMoment.quadratureSum p (j + 1) (s + p) m h / h :=
    sumRangeIntegrand_eq_quadratureSum_div
      (p := p) (j := j + 1) (s := s + p) (m := m) h_h
  convert hsum using 1
  · ext u
    rw [quadratureSum_eq_sumRangeSeries_local]
  · symm
    calc
      ∑ k ∈ Finset.range m,
          ((s + 1) * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h) -
            ((j : ℝ) * p) *
              KernelMoment.integrand p (j + 1) (s + p) (((k + 1 : ℕ) : ℝ) * h))
          =
        (∑ k ∈ Finset.range m,
            (s + 1) * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)) -
          ∑ k ∈ Finset.range m,
            ((j : ℝ) * p) *
              KernelMoment.integrand p (j + 1) (s + p) (((k + 1 : ℕ) : ℝ) * h) := by
              rw [Finset.sum_sub_distrib]
      _ =
        (s + 1) *
            (∑ k ∈ Finset.range m,
              KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h)) -
          ((j : ℝ) * p) *
            (∑ k ∈ Finset.range m,
              KernelMoment.integrand p (j + 1) (s + p) (((k + 1 : ℕ) : ℝ) * h)) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ =
        (s + 1) * (KernelMoment.quadratureSum p j s m h / h) -
          ((j : ℝ) * p) * (KernelMoment.quadratureSum p (j + 1) (s + p) m h / h) := by
                rw [h_sum_main, h_sum_shift]
      _ =
        (((s + 1) * KernelMoment.quadratureSum p j s m h) -
            ((j : ℝ) * p) * KernelMoment.quadratureSum p (j + 1) (s + p) m h) / h := by
              field_simp [h_h.ne']

/-- Helper for Theorem 7.29: the bias mesh profile is a fixed prefactor times
the Chapter 7 quadrature family `Q(2, p - q)`. -/
lemma meshProfileBias_eq_quadratureSum
    (b c p q : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    meshProfileBias b c p q n h =
      (b * c * h ^ (p + q - 1) / (n.succ : ℝ)) *
        KernelMoment.quadratureSum p 2 (p - q) n.succ h := by
  have h_sum :
      ∑ k ∈ Finset.range n.succ,
        KernelMoment.integrand p 2 (p - q) (((k + 1 : ℕ) : ℝ) * h) =
          KernelMoment.quadratureSum p 2 (p - q) n.succ h / h :=
    sumRangeIntegrand_eq_quadratureSum_div
      (p := p) (j := 2) (s := p - q) (m := n.succ) h_h
  have hpow :
      h ^ (p + q) / h = h ^ (p + q - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one h, ← Real.rpow_add h_h]
    congr 1
  -- Replace the raw integrand sum by the normalized quadrature sum.
  rw [meshProfileBias_eq_integrandSum (b := b) (c := c) (p := p) (q := q) (n := n) h_h]
  rw [h_sum]
  calc
    (b * c * h ^ (p + q) / (n.succ : ℝ)) *
        (KernelMoment.quadratureSum p 2 (p - q) n.succ h / h)
        =
          (b * c / (n.succ : ℝ)) *
            (h ^ (p + q) / h) *
              KernelMoment.quadratureSum p 2 (p - q) n.succ h := by
                ring
    _ =
          (b * c / (n.succ : ℝ)) *
            h ^ (p + q - 1) *
              KernelMoment.quadratureSum p 2 (p - q) n.succ h := by
                rw [hpow]
    _ =
          (b * c * h ^ (p + q - 1) / (n.succ : ℝ)) *
            KernelMoment.quadratureSum p 2 (p - q) n.succ h := by
                ring

/-- Helper for Theorem 7.29: the variance mesh profile is the Chapter 7
quadrature family `Q(2, 2p)` with the explicit prefactor `σ² / (n h)`. -/
lemma meshProfileVariance_eq_quadratureSum
    (p σ : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    meshProfileVariance p σ n h =
      (σ ^ 2 / ((n.succ : ℝ) * h)) *
        KernelMoment.quadratureSum p 2 (2 * p) n.succ h := by
  have h_sum :
      ∑ k ∈ Finset.range n.succ,
        KernelMoment.integrand p 2 (2 * p) (((k + 1 : ℕ) : ℝ) * h) =
          KernelMoment.quadratureSum p 2 (2 * p) n.succ h / h :=
    sumRangeIntegrand_eq_quadratureSum_div
      (p := p) (j := 2) (s := 2 * p) (m := n.succ) h_h
  have h_nsucc_ne : (n.succ : ℝ) ≠ 0 := by
    positivity
  -- Rewrite the raw integrand sum using the same quadrature normalization.
  rw [meshProfileVariance_eq_integrandSum (p := p) (σ := σ) (n := n) h_h]
  rw [h_sum]
  field_simp [h_h.ne', h_nsucc_ne]

/-- Helper for Theorem 7.29: dividing a positive real power by the base point
lowers the exponent by one. -/
private lemma rpow_div_self_of_pos
    {h a : ℝ} (h_h : 0 < h) :
    h ^ a / h = h ^ (a - 1) := by
  calc
    h ^ a / h = h ^ a * h⁻¹ := by
      rw [div_eq_mul_inv]
    _ = h ^ (a + -1) := by
          rw [← Real.rpow_neg_one h, ← Real.rpow_add h_h]
    _ = h ^ (a - 1) := by
          congr 1

/-- Helper for Theorem 7.29: near a positive mesh scale, the bias profile
agrees with the quadrature normal form used in the derivative computation. -/
private lemma meshProfileBias_eventuallyEq_quadratureForm
    (b c p q : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    (fun u : ℝ ↦ meshProfileBias b c p q n u) =ᶠ[nhds h]
      (fun u : ℝ ↦
        (b * c / (n.succ : ℝ)) *
          (u ^ (p + q - 1) *
            KernelMoment.quadratureSum p 2 (p - q) n.succ u)) := by
  have h_positive : Set.Ioi (0 : ℝ) ∈ nhds h := isOpen_Ioi.mem_nhds h_h
  -- Rewrite the bias profile on the positive side where the quadrature API applies.
  filter_upwards [h_positive] with u hu
  rw [meshProfileBias_eq_quadratureSum (b := b) (c := c) (p := p) (q := q) (n := n) hu]
  ring

/-- Helper for Theorem 7.29: near a positive mesh scale, the variance profile
agrees with the quotient `Q(2, 2p) / h` used in the derivative computation. -/
private lemma meshProfileVariance_eventuallyEq_quadratureForm
    (p σ : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    (fun u : ℝ ↦ meshProfileVariance p σ n u) =ᶠ[nhds h]
      (fun u : ℝ ↦
        (σ ^ 2 / (n.succ : ℝ)) *
          (KernelMoment.quadratureSum p 2 (2 * p) n.succ u / u)) := by
  have h_positive : Set.Ioi (0 : ℝ) ∈ nhds h := isOpen_Ioi.mem_nhds h_h
  -- Rewrite the variance profile on the positive side where the quadrature API applies.
  filter_upwards [h_positive] with u hu
  rw [meshProfileVariance_eq_quadratureSum (p := p) (σ := σ) (n := n) hu]
  field_simp [(show 0 < u from hu).ne']

/-- Helper for Theorem 7.29: near a positive mesh scale, the defect profile
agrees with the quotient `1 - Q(1, 0) / ((n + 1) h)` used in the derivative
computation. -/
private lemma meshProfileDefect_eventuallyEq_quotientForm
    (p : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    (fun u : ℝ ↦ meshProfileDefect p n u) =ᶠ[nhds h]
      (fun u : ℝ ↦
        1 - (1 / (n.succ : ℝ)) *
          (KernelMoment.quadratureSum p 1 0 n.succ u / u)) := by
  have h_positive : Set.Ioi (0 : ℝ) ∈ nhds h := isOpen_Ioi.mem_nhds h_h
  -- Rewrite the defect profile on the positive side where the denominator quotient is defined.
  filter_upwards [h_positive] with u hu
  rw [meshProfileDefect]
  field_simp [(show 0 < u from hu).ne']

/-- Helper for Theorem 7.29: differentiating the bias mesh profile at positive
mesh scale produces the clean `Q(3, p - q)` formula. -/
lemma meshProfileBias_hasDerivAt_pos
    (b c p q : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ meshProfileBias b c p q n u)
      ((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
        KernelMoment.quadratureSum p 3 (p - q) n.succ h)
      h := by
  have h_eventually :=
    meshProfileBias_eventuallyEq_quadratureForm
      (b := b) (c := c) (p := p) (q := q) (n := n) h_h
  refine (Filter.EventuallyEq.hasDerivAt_iff h_eventually).2 ?_
  have hpow :
      HasDerivAt
        (fun u : ℝ ↦ u ^ (p + q - 1))
        ((p + q - 1) * h ^ (p + q - 2))
        h := by
    -- Differentiate the explicit power factor before combining it with the
    -- quadrature recurrence.
    convert (Real.hasDerivAt_rpow_const (x := h) (p := p + q - 1) (Or.inl h_h.ne')) using 1
    ring
  have hquad :=
    quadratureSum_hasDerivAt_pos
      (p := p) (j := 2) (s := p - q) (m := n.succ) h_h
  have h_prod :
      HasDerivAt
        (fun u : ℝ ↦
          (b * c / (n.succ : ℝ)) *
            (u ^ (p + q - 1) *
              KernelMoment.quadratureSum p 2 (p - q) n.succ u))
        ((b * c / (n.succ : ℝ)) *
          (((p + q - 1) * h ^ (p + q - 2) *
                KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
            h ^ (p + q - 1) *
              ((((p - q + 1) * KernelMoment.quadratureSum p 2 (p - q) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((p - q) + p) n.succ h) / h)))
        h := by
    -- Keep the proof in the stable quadrature spelling, then normalize the
    -- resulting raw product derivative once.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hpow.mul hquad).const_mul (b * c / (n.succ : ℝ))
  have h_value :
      (b * c / (n.succ : ℝ)) *
          (((p + q - 1) * h ^ (p + q - 2) *
                KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
            h ^ (p + q - 1) *
              ((((p - q + 1) * KernelMoment.quadratureSum p 2 (p - q) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((p - q) + p) n.succ h) / h)) =
        ((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
          KernelMoment.quadratureSum p 3 (p - q) n.succ h) := by
    have h_inner :
        ((p + q - 1) * h ^ (p + q - 2) *
              KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
            h ^ (p + q - 1) *
              ((((p - q + 1) * KernelMoment.quadratureSum p 2 (p - q) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((p - q) + p) n.succ h) / h) =
          (2 * p) * h ^ (p + q - 2) * KernelMoment.quadratureSum p 3 (p - q) n.succ h := by
      have h_raw :=
        quadraturePowMul_rawDeriv_eq
          (p := p) (r := p + q - 1) (s := p - q) (m := n.succ) h_h (by ring)
      have h_exp : p + q - 1 - 1 = p + q - 2 := by
        ring
      simpa [h_exp] using h_raw
    calc
      (b * c / (n.succ : ℝ)) *
          (((p + q - 1) * h ^ (p + q - 2) *
                KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
            h ^ (p + q - 1) *
              ((((p - q + 1) * KernelMoment.quadratureSum p 2 (p - q) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((p - q) + p) n.succ h) / h))
          =
        (b * c / (n.succ : ℝ)) *
          ((2 * p) * h ^ (p + q - 2) * KernelMoment.quadratureSum p 3 (p - q) n.succ h) := by
            rw [h_inner]
      _ =
        ((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
          KernelMoment.quadratureSum p 3 (p - q) n.succ h) := by
            ring
  exact h_value ▸ h_prod

/-- Helper for Theorem 7.29: differentiating the variance mesh profile at a
positive mesh scale produces the clean `Q(3, 2p)` formula. -/
lemma meshProfileVariance_hasDerivAt_pos
    (p σ : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ meshProfileVariance p σ n u)
      ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
        KernelMoment.quadratureSum p 3 (2 * p) n.succ h)
      h := by
  have h_eventually :=
    meshProfileVariance_eventuallyEq_quadratureForm
      (p := p) (σ := σ) (n := n) h_h
  refine (Filter.EventuallyEq.hasDerivAt_iff h_eventually).2 ?_
  have hquad :=
    quadratureSum_hasDerivAt_pos
      (p := p) (j := 2) (s := 2 * p) (m := n.succ) h_h
  have h_quot :
      HasDerivAt
        (fun u : ℝ ↦
          (σ ^ 2 / (n.succ : ℝ)) *
            (KernelMoment.quadratureSum p 2 (2 * p) n.succ u / u))
        ((σ ^ 2 / (n.succ : ℝ)) *
          ((((((2 * p + 1) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h) / h ^ 2))
        h := by
    -- Differentiate the stable quotient form `Q(2, 2p, u) / u` first, then
    -- collapse the numerator by the named quadrature identities.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((hquad.div (hasDerivAt_id h) h_h.ne').const_mul (σ ^ 2 / (n.succ : ℝ)))
  have h_value :
      (σ ^ 2 / (n.succ : ℝ)) *
          ((((((2 * p + 1) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h) / h ^ 2) =
        ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 3 (2 * p) n.succ h) := by
    have h_inner :
        ((((((2 * p + 1) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h) / h ^ 2) =
          (2 * p * KernelMoment.quadratureSum p 3 (2 * p) n.succ h) / h ^ 2 := by
      calc
        ((((((2 * p + 1) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h) / h ^ 2)
            =
          ((2 * p) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h -
              (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h ^ 2 := by
                simpa using
                  quadratureQuotientRawDeriv_eq
                    (p := p) (j := 2) (s := 2 * p) (m := n.succ) h_h
        _ =
          ((2 * p) *
              (KernelMoment.quadratureSum p 2 (2 * p) n.succ h -
                KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h)) / h ^ 2 := by
                  ring
        _ = (2 * p * KernelMoment.quadratureSum p 3 (2 * p) n.succ h) / h ^ 2 := by
              rw [quadratureSum_two_sub_three_eq_three
                (p := p) (s := 2 * p) (m := n.succ) h_h]
    calc
      (σ ^ 2 / (n.succ : ℝ)) *
          ((((((2 * p + 1) * KernelMoment.quadratureSum p 2 (2 * p) n.succ h) -
                    (2 * p) * KernelMoment.quadratureSum p 3 ((2 * p) + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h) / h ^ 2)
          =
        (σ ^ 2 / (n.succ : ℝ)) *
          ((2 * p * KernelMoment.quadratureSum p 3 (2 * p) n.succ h) / h ^ 2) := by
            rw [h_inner]
      _ =
        ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 3 (2 * p) n.succ h) := by
            ring
  exact h_value ▸ h_quot

/-- Helper for Theorem 7.29: differentiating the denominator defect at a
positive mesh scale yields the positive `Q(2, p)` contribution. -/
lemma meshProfileDefect_hasDerivAt_pos
    (p : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ meshProfileDefect p n u)
      ((p / ((n.succ : ℝ) * h ^ 2)) *
        KernelMoment.quadratureSum p 2 p n.succ h)
      h := by
  have h_eventually :=
    meshProfileDefect_eventuallyEq_quotientForm
      (p := p) (n := n) h_h
  refine (Filter.EventuallyEq.hasDerivAt_iff h_eventually).2 ?_
  have hquad :=
    quadratureSum_hasDerivAt_pos
      (p := p) (j := 1) (s := 0) (m := n.succ) h_h
  have h_defect :
      HasDerivAt
        (fun u : ℝ ↦
          1 - (1 / (n.succ : ℝ)) *
            (KernelMoment.quadratureSum p 1 0 n.succ u / u))
        (-((1 / (n.succ : ℝ)) *
            ((((((0 + 1) * KernelMoment.quadratureSum p 1 0 n.succ h) -
                      ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h) *
                  h -
                KernelMoment.quadratureSum p 1 0 n.succ h) / h ^ 2)))
        h := by
    -- Differentiate the defect quotient under `const_sub`, so the final sign
    -- flip is handled once and the remaining numerator simplification is local.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (((hquad.div (hasDerivAt_id h) h_h.ne').const_mul (1 / (n.succ : ℝ))).const_sub 1)
  have h_value :
      -((1 / (n.succ : ℝ)) *
          ((((((0 + 1) * KernelMoment.quadratureSum p 1 0 n.succ h) -
                    ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 1 0 n.succ h) / h ^ 2)) =
        ((p / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 2 p n.succ h) := by
    have h_inner :
        ((((((0 + 1) * KernelMoment.quadratureSum p 1 0 n.succ h) -
                    ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 1 0 n.succ h) / h ^ 2) =
          (-(p * KernelMoment.quadratureSum p 2 p n.succ h)) / h ^ 2 := by
      calc
        ((((((0 + 1) * KernelMoment.quadratureSum p 1 0 n.succ h) -
                    ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 1 0 n.succ h) / h ^ 2)
            = (0 * KernelMoment.quadratureSum p 1 0 n.succ h -
                ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h ^ 2 := by
                  simpa using
                    quadratureQuotientRawDeriv_eq
                      (p := p) (j := 1) (s := 0) (m := n.succ) h_h
        _ = (-(p * KernelMoment.quadratureSum p 2 p n.succ h)) / h ^ 2 := by
              ring
    calc
      -((1 / (n.succ : ℝ)) *
          ((((((0 + 1) * KernelMoment.quadratureSum p 1 0 n.succ h) -
                    ((1 : ℝ) * p) * KernelMoment.quadratureSum p 2 (0 + p) n.succ h) / h) *
                h -
              KernelMoment.quadratureSum p 1 0 n.succ h) / h ^ 2))
          =
        -((1 / (n.succ : ℝ)) * ((-(p * KernelMoment.quadratureSum p 2 p n.succ h)) / h ^ 2)) := by
            rw [h_inner]
      _ =
        ((p / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 2 p n.succ h) := by
            ring
  exact h_value ▸ h_defect

/-- Helper for Theorem 7.29: the exact scaled quotient can now be referred to
through named numerator and defect pieces instead of the raw substituted term. -/
lemma expectedObjective_atScaledBeta_eq_scaledQuotient
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    expectedObjective μ K R fTrue η n
        (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) =
      scaledExpectedObjectiveQuotient b c p q σ n t := by
  -- Route correction: freeze the exact substituted quotient behind named
  -- pieces before attempting any derivative or sign analysis.
  simpa [scaledExpectedObjectiveQuotient, scaledExpectedObjectiveBias,
    scaledExpectedObjectiveVariance, scaledExpectedObjectiveDefect, scaledMesh] using
    expectedObjective_atScaledBeta_eq_modeProfileQuotient
      (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
      (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated
      h_white h_svd h_tikhonov h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay h_t n

/-- Helper for Theorem 7.29: the named scaled denominator defect is positive
everywhere on the positive `β_pred` scale. -/
lemma scaledExpectedObjectiveDefect_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 < scaledExpectedObjectiveDefect b c p q σ n t := by
  -- This is exactly the earlier positivity theorem, rewritten through the
  -- local defect abbreviation.
  simpa [scaledExpectedObjectiveDefect, scaledMesh] using
    expectedObjectiveScaledDefect_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n

/-- Helper for Theorem 7.29: near any positive normalized scale `t`, the
expected GCV family on the `t * β_pred` scale agrees with the mesh-profile
quotient composed with `scaledMesh`. -/
lemma scaledExpectedObjective_eventuallyEq_meshProfileComposite
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    (fun u : ℝ ↦
        expectedObjective μ K R fTrue η n
          (u * TikhonovPredictiveRisk.betaPred b c p q σ n.succ)) =ᶠ[nhds t]
      (fun u : ℝ ↦
        meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n u)) := by
  have h_positive : Set.Ioi (0 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds h_t
  -- On the positive half-line, both spellings are exactly the same quotient.
  filter_upwards [h_positive] with u hu
  rw [expectedObjective_atScaledBeta_eq_scaledQuotient
    (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
    (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated
    h_white h_svd h_tikhonov h_singularValueSquareDecay
    h_fourierCoefficientSquareDecay hu n]
  rw [scaledExpectedObjectiveQuotient_eq_meshProfileQuotient
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated hu n]

/-- Helper for Theorem 7.29: the derivative on the normalized `t * β_pred`
scale may be computed in the mesh-profile spelling because the two families
agree on a neighborhood of every positive `t`. -/
lemma scaledExpectedObjective_deriv_eq_meshProfileCompositeDeriv
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    deriv
        (fun u : ℝ ↦
          expectedObjective μ K R fTrue η n
            (u * TikhonovPredictiveRisk.betaPred b c p q σ n.succ))
        t =
      deriv
        (fun u : ℝ ↦
          meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n u))
        t := by
  -- Replace the scaled expected objective by the equal mesh-profile composite
  -- in a neighborhood of the positive point `t`.
  exact Filter.EventuallyEq.deriv_eq
    (scaledExpectedObjective_eventuallyEq_meshProfileComposite
      (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
      (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated
      h_white h_svd h_tikhonov h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay h_t n)

/-- Helper for Theorem 7.29: a lower bound on `dist t 1` forces `t` to lie on
one side of the gap around `1`. -/
lemma le_one_sub_or_one_add_le_of_le_dist
    {ε t : ℝ} (h_dist : ε ≤ dist t 1) :
    t ≤ 1 - ε ∨ 1 + ε ≤ t := by
  -- Rewrite the distance to `1` as an absolute value and split by the sign of
  -- `t - 1`.
  rw [Real.dist_eq, abs_sub_comm] at h_dist
  by_cases h_le : t ≤ 1
  · left
    have h_abs : |1 - t| = 1 - t := abs_of_nonneg (sub_nonneg.mpr h_le)
    rw [h_abs] at h_dist
    linarith
  · right
    have h_lt : 1 < t := lt_of_not_ge h_le
    have h_abs : |1 - t| = t - 1 := by
      rw [abs_of_neg (sub_neg.mpr h_lt)]
      ring
    rw [h_abs] at h_dist
    linarith

/-- Helper for Theorem 7.29: the chain-rule prefactor contributed by
`scaledMesh` is strictly positive on the positive benchmark scale. -/
lemma scaledMesh_hasDerivAt_factor_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 < scaledMesh b c p q σ n t / (p * t) := by
  -- Both the mesh and the denominator factors are positive under the standing
  -- admissibility assumptions.
  have h_mesh_pos :=
    scaledMesh_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have h_p_pos : 0 < p := by
    linarith
  positivity

/-- Helper for Theorem 7.29: the quotient-rule numerator controlling the
derivative of `meshProfileQuotient` at a positive mesh scale `h`. -/
abbrev meshProfileQuotientBalance
    (b c p q σ : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ((((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
        KernelMoment.quadratureSum p 3 (p - q) n.succ h) +
      ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
        KernelMoment.quadratureSum p 3 (2 * p) n.succ h)) *
      meshProfileDefect p n h) -
    (2 : ℝ) * (meshProfileBias b c p q n h + meshProfileVariance p σ n h) *
      ((p / ((n.succ : ℝ) * h ^ 2)) *
        KernelMoment.quadratureSum p 2 p n.succ h)

/-- Helper for Theorem 7.29: differentiating `meshProfileQuotient` at a
positive mesh scale reduces to the named quotient-rule balance. -/
lemma meshProfileQuotient_hasDerivAt_pos
    (b c p q σ : ℝ) (n : ℕ) {h : ℝ} (h_h : 0 < h) :
    HasDerivAt
      (fun u : ℝ ↦ meshProfileQuotient b c p q σ n u)
      (meshProfileQuotientBalance b c p q σ n h / (meshProfileDefect p n h) ^ 3)
      h := by
  let numeratorDeriv :=
    ((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
        KernelMoment.quadratureSum p 3 (p - q) n.succ h) +
      ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
        KernelMoment.quadratureSum p 3 (2 * p) n.succ h)
  let defectDeriv :=
    (p / ((n.succ : ℝ) * h ^ 2)) *
      KernelMoment.quadratureSum p 2 p n.succ h
  have h_num :=
    (meshProfileBias_hasDerivAt_pos (b := b) (c := c) (p := p) (q := q) (n := n) h_h).add
      (meshProfileVariance_hasDerivAt_pos (p := p) (σ := σ) (n := n) h_h)
  have h_defect :
      HasDerivAt (fun u : ℝ ↦ meshProfileDefect p n u) defectDeriv h :=
    meshProfileDefect_hasDerivAt_pos (p := p) (n := n) h_h
  have h_den := h_defect.mul h_defect
  have h_defect_ne : meshProfileDefect p n h ≠ 0 := by
    exact ne_of_gt (meshProfileDefect_pos (p := p) (n := n) h_h)
  have h_quot :=
    h_num.div h_den (mul_ne_zero h_defect_ne h_defect_ne)
  have h_quot_mesh_eq :
      (fun u : ℝ ↦
          (meshProfileBias b c p q n u + meshProfileVariance p σ n u) /
            (meshProfileDefect p n u * meshProfileDefect p n u)) =ᶠ[nhds h]
        (((fun u : ℝ ↦ meshProfileBias b c p q n u) + fun u ↦ meshProfileVariance p σ n u) /
          ((fun u : ℝ ↦ meshProfileDefect p n u) * fun u ↦ meshProfileDefect p n u)) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simp [Pi.add_apply, Pi.mul_apply, Pi.div_apply]
  have h_quot_mesh :
      HasDerivAt
        (fun u : ℝ ↦ meshProfileQuotient b c p q σ n u)
        ((numeratorDeriv * (meshProfileDefect p n h * meshProfileDefect p n h) -
            (meshProfileBias b c p q n h + meshProfileVariance p σ n h) *
              (defectDeriv * meshProfileDefect p n h +
                meshProfileDefect p n h * defectDeriv)) /
          (meshProfileDefect p n h * meshProfileDefect p n h) ^ 2)
        h := by
    have h_quot_mesh_raw :
        HasDerivAt
          (fun u : ℝ ↦
            (meshProfileBias b c p q n u + meshProfileVariance p σ n u) /
              (meshProfileDefect p n u * meshProfileDefect p n u))
          ((numeratorDeriv * (meshProfileDefect p n h * meshProfileDefect p n h) -
              (meshProfileBias b c p q n h + meshProfileVariance p σ n h) *
                (defectDeriv * meshProfileDefect p n h +
                  meshProfileDefect p n h * defectDeriv)) /
            (meshProfileDefect p n h * meshProfileDefect p n h) ^ 2)
          h :=
      (Filter.EventuallyEq.hasDerivAt_iff h_quot_mesh_eq).2 h_quot
    have h_profile_eq :
        (fun u : ℝ ↦ meshProfileQuotient b c p q σ n u) =ᶠ[nhds h]
          (fun u : ℝ ↦
            (meshProfileBias b c p q n u + meshProfileVariance p σ n u) /
              (meshProfileDefect p n u * meshProfileDefect p n u)) := by
      refine Filter.Eventually.of_forall ?_
      intro u
      simp [meshProfileQuotient, pow_two]
    -- Assemble the quotient derivative before rewriting the raw denominator
    -- product into the named square and balance forms.
    exact (Filter.EventuallyEq.hasDerivAt_iff h_profile_eq).2 h_quot_mesh_raw
  have h_value :
      ((numeratorDeriv * (meshProfileDefect p n h * meshProfileDefect p n h) -
          (meshProfileBias b c p q n h + meshProfileVariance p σ n h) *
            (defectDeriv * meshProfileDefect p n h +
              meshProfileDefect p n h * defectDeriv)) /
        (meshProfileDefect p n h * meshProfileDefect p n h) ^ 2) =
      meshProfileQuotientBalance b c p q σ n h / (meshProfileDefect p n h) ^ 3 := by
    -- Cancel one positive defect factor so the derivative lands in the named
    -- balance spelling used by the downstream chain-rule argument.
    dsimp [meshProfileQuotientBalance, numeratorDeriv, defectDeriv]
    field_simp [h_defect_ne]
    ring
  -- Rewrite the assembled quotient-rule derivative to the owner-level balance
  -- expression expected by the rest of the file.
  exact h_value ▸ h_quot_mesh

/-- Helper for Theorem 7.29: after composing with `scaledMesh`, all positive
chain-rule and denominator terms can be isolated from the remaining balance. -/
abbrev scaledExpectedObjectivePositiveFactor
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (scaledMesh b c p q σ n t / (p * t)) /
    (meshProfileDefect p n (scaledMesh b c p q σ n t)) ^ 3

/-- Helper for Theorem 7.29: after the positive factor is extracted, the
remaining sign problem is the explicit mesh-profile quotient balance evaluated
at `scaledMesh`. -/
abbrev scaledExpectedObjectiveBalance
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  meshProfileQuotientBalance b c p q σ n (scaledMesh b c p q σ n t)

/-- Helper for Theorem 7.29: the factor isolated from the scaled derivative is
strictly positive on the positive benchmark scale. -/
lemma scaledExpectedObjectivePositiveFactor_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    0 < scaledExpectedObjectivePositiveFactor b c p q σ n t := by
  have h_mesh_pos :=
    scaledMesh_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have h_factor_pos :=
    scaledMesh_hasDerivAt_factor_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have h_defect_pos :
      0 < meshProfileDefect p n (scaledMesh b c p q σ n t) :=
    meshProfileDefect_pos (p := p) (n := n) h_mesh_pos
  -- Every factor in the isolated prefactor is positive, so only the balance
  -- can affect the derivative sign.
  dsimp [scaledExpectedObjectivePositiveFactor]
  positivity

/-- Helper for Theorem 7.29: differentiating the scaled mesh-profile quotient
splits into one positive prefactor times the explicit balance term. -/
lemma scaledExpectedObjectiveDeriv_eq_positiveFactor_mulBalance
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    deriv
        (fun u : ℝ ↦ meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n u))
        t =
      scaledExpectedObjectivePositiveFactor b c p q σ n t *
        scaledExpectedObjectiveBalance b c p q σ n t := by
  let hmesh := scaledMesh b c p q σ n t
  have h_mesh_pos :=
    scaledMesh_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  have h_comp :
      HasDerivAt
        (fun u : ℝ ↦ meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n u))
        ((meshProfileQuotientBalance b c p q σ n hmesh /
              (meshProfileDefect p n hmesh) ^ 3) *
          (hmesh / (p * t)))
        t := by
    -- Compose the mesh-profile quotient derivative with the explicit
    -- derivative of `scaledMesh`.
    exact
      (meshProfileQuotient_hasDerivAt_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n)
        (by simpa [hmesh] using h_mesh_pos)).comp t
        (scaledMesh_hasDerivAt
          (b := b) (c := c) (p := p) (q := q) (σ := σ)
          h_b h_c h_p h_q h_σ h_nonsaturated h_t n)
  -- Rewrite the composite derivative into the positive-factor spelling used by
  -- the final sign argument.
  calc
    deriv
        (fun u : ℝ ↦ meshProfileQuotient b c p q σ n (scaledMesh b c p q σ n u))
        t =
      (meshProfileQuotientBalance b c p q σ n hmesh / (meshProfileDefect p n hmesh) ^ 3) *
        (hmesh / (p * t)) := by
          simpa [hmesh] using h_comp.deriv
    _ =
      scaledExpectedObjectivePositiveFactor b c p q σ n t *
        scaledExpectedObjectiveBalance b c p q σ n t := by
          dsimp [scaledExpectedObjectivePositiveFactor, scaledExpectedObjectiveBalance, hmesh]
          ring

/-- Helper for Theorem 7.29: evaluating the remaining balance term at the
scaled mesh rewrites the bias and variance pieces into the common Chapter 7
quadrature normal form. -/
lemma scaledExpectedObjectiveBalance_eq_quadratureBalance
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    let h := scaledMesh b c p q σ n t
    scaledExpectedObjectiveBalance b c p q σ n t =
      ((((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
            KernelMoment.quadratureSum p 3 (p - q) n.succ h) +
          ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
            KernelMoment.quadratureSum p 3 (2 * p) n.succ h)) *
        meshProfileDefect p n h) -
      (2 : ℝ) *
        (((b * c * h ^ (p + q - 1) / (n.succ : ℝ)) *
            KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
          ((σ ^ 2 / ((n.succ : ℝ) * h)) *
            KernelMoment.quadratureSum p 2 (2 * p) n.succ h)) *
        ((p / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 2 p n.succ h) := by
  let h := scaledMesh b c p q σ n t
  have h_pos : 0 < h := by
    -- The scaled mesh stays positive, so the quadrature-profile rewrites apply
    -- without reopening the denominator side conditions.
    simpa [h] using
      scaledMesh_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  -- Rewrite the bias and variance pieces once so every regime starts from the
  -- same quadrature-balance spelling.
  dsimp [scaledExpectedObjectiveBalance, h, meshProfileQuotientBalance]
  rw [meshProfileBias_eq_quadratureSum (b := b) (c := c) (p := p) (q := q) (n := n) h_pos]
  rw [meshProfileVariance_eq_quadratureSum (p := p) (σ := σ) (n := n) h_pos]
  simpa [h]

/-- Helper for Theorem 7.29: in the small-mesh regime `q < p`, the normalized
mesh on the `t * β_pred` scale tends to `0` through positive values. -/
lemma scaledMesh_tendsto_zero_of_q_lt_p
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q < p) {t : ℝ} (h_t : 0 < t) :
    Filter.Tendsto (fun n : ℕ ↦ scaledMesh b c p q σ n t) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  let a : ℝ := 1 / p - 1 / q
  let pref : ℝ :=
    ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
        (σ ^ 2) ^ (p / q)) ^ (1 / p))
  have h_succ_tendsto_atTop :
      Filter.Tendsto (fun n : ℕ ↦ (n.succ : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have h_a_neg : a < 0 := by
    -- The sign of the mesh exponent is exactly the sign of `q - p`.
    simpa [a] using (betaPredScaleMeshExponent_neg_iff (p := p) (q := q) h_p h_q).2 h_qp
  have h_power_zero :
      Filter.Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ a) Filter.atTop (nhds 0) := by
    let y : ℝ := -a
    have h_neg_a_pos : 0 < y := by
      linarith
    -- The `n`-power decays because the exponent is negative in the regime `q < p`.
    have hyexp : -y = a := by
      dsimp [y]
      ring
    simpa [Function.comp_def, hyexp] using
      ((tendsto_rpow_neg_atTop h_neg_a_pos).comp h_succ_tendsto_atTop)
  have h_limit_zero :
      Filter.Tendsto (fun n : ℕ ↦ pref * (n.succ : ℝ) ^ a) Filter.atTop (nhds 0) := by
    -- The fixed positive prefactor does not change the vanishing power-law limit.
    simpa using Filter.Tendsto.const_mul pref h_power_zero
  have h_pos_eventually :
      ∀ᶠ n in Filter.atTop, scaledMesh b c p q σ n t ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [] with n
    -- The scaled mesh is positive for every `n`, so the limit lands in `Ioi 0`.
    exact
      scaledMesh_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t n
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, h_pos_eventually⟩
  -- Replace the mesh by its explicit constant-times-power law before taking the limit.
  refine Filter.Tendsto.congr' ?_ h_limit_zero
  refine Filter.Eventually.of_forall ?_
  intro n
  dsimp
  symm
  rw [scaledMesh_eq_constant_mul_power
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]

/-- Helper for Theorem 7.29: regardless of the regime, the product
`(n.succ : ℝ) * scaledMesh` tends to `+∞` on the normalized benchmark scale. -/
lemma scaledMesh_mul_tendsto_atTop
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) :
    Filter.Tendsto
      (fun n : ℕ ↦ (n.succ : ℝ) * scaledMesh b c p q σ n t)
      Filter.atTop Filter.atTop := by
  let a : ℝ := 1 / p - 1 / q
  let pref : ℝ :=
    ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
        (σ ^ 2) ^ (p / q)) ^ (1 / p))
  have h_succ_tendsto_atTop :
      Filter.Tendsto (fun n : ℕ ↦ (n.succ : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have h_pref_pos : 0 < pref := by
    -- The fixed mesh prefactor is positive because every coefficient in the
    -- predictive benchmark constant is positive.
    have h_betaConst_pos : 0 < TikhonovPredictiveRisk.betaPredConstant b c p q := by
      rw [TikhonovPredictiveRisk.betaPredConstant_def]
      refine Real.rpow_pos_of_pos ?_ _
      exact
        div_pos
          (predictiveRiskC2_pos c p h_c h_p)
          (mul_pos (by linarith)
            (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated))
    positivity
  have h_exp_pos : 0 < 1 + a := by
    -- The extra `n` factor turns the benchmark mesh exponent positive in every regime.
    simpa [a] using betaPredScaleMeshMulExponent_pos (p := p) (q := q) h_p h_q
  have h_power_atTop :
      Filter.Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ (1 + a)) Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop h_exp_pos).comp h_succ_tendsto_atTop
  have h_rewrite :
      (fun n : ℕ ↦ (n.succ : ℝ) * scaledMesh b c p q σ n t) =ᶠ[Filter.atTop]
        fun n : ℕ ↦ pref * (n.succ : ℝ) ^ (1 + a) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    dsimp
    rw [scaledMesh_eq_constant_mul_power
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
    have h_nsucc_pos : 0 < (n.succ : ℝ) := by
      positivity
    have h_mul_rpow :
        (n.succ : ℝ) * (n.succ : ℝ) ^ a = (n.succ : ℝ) ^ (1 + a) := by
      calc
        (n.succ : ℝ) * (n.succ : ℝ) ^ a
            = (n.succ : ℝ) ^ (1 : ℝ) * (n.succ : ℝ) ^ a := by simp
        _ = (n.succ : ℝ) ^ ((1 : ℝ) + a) := by rw [← Real.rpow_add h_nsucc_pos]
        _ = (n.succ : ℝ) ^ (1 + a) := by rfl
    calc
      (n.succ : ℝ) * (pref * (n.succ : ℝ) ^ a)
          = pref * ((n.succ : ℝ) * (n.succ : ℝ) ^ a) := by ring
      _ = pref * ((n.succ : ℝ) ^ (1 + a)) := by rw [h_mul_rpow]
  -- After rewriting to a positive constant times a positive power, the product
  -- diverges by the standard real-power asymptotic.
  refine Filter.Tendsto.congr' h_rewrite.symm ?_
  exact Filter.Tendsto.const_mul_atTop h_pref_pos h_power_atTop

/-- Helper for Theorem 7.29: away from the normalized benchmark `t = 1`, the
scalar carrier produced by the small-mesh asymptotic has the same sign as
`t - 1`. -/
lemma balanceCarrier_sign_offNeighborhood
    (h_p : 1 < p) (h_q : 1 < q)
    {ε t : ℝ} (h_t : 0 < t) (h_ε : 0 < ε) (h_ε_lt_one : ε < 1)
    (h_dist : ε ≤ dist t 1) :
    (t - 1) *
        (t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1)) >
      0 := by
  have h_p_pos : 0 < p := by
    linarith
  have h_q_pos : 0 < q := by
    linarith
  have h_q_div_p_pos : 0 < q / p := div_pos h_q_pos h_p_pos
  have hsplit :
      t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1) =
        t ^ (-(1 / p) - 1) * (t ^ (q / p) - 1) := by
    -- Rewrite the carrier so the sign is controlled only by `t ^ (q / p) - 1`.
    have hexp :
        (-(1 / p) - 1) + q / p = ((q - 1) / p) - 1 := by
      field_simp [ne_of_gt h_p_pos]
      ring
    calc
      t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1)
          = t ^ ((-(1 / p) - 1) + q / p) - t ^ (-(1 / p) - 1) := by rw [hexp]
      _ = t ^ (-(1 / p) - 1) * t ^ (q / p) - t ^ (-(1 / p) - 1) := by
            rw [Real.rpow_add h_t]
      _ = t ^ (-(1 / p) - 1) * (t ^ (q / p) - 1) := by ring
  rcases le_one_sub_or_one_add_le_of_le_dist h_dist with h_left | h_right
  · -- On the left of the `ε`-gap, both factors are negative.
    have h_t_lt_one : t < 1 := lt_of_le_of_lt h_left (by linarith)
    have h_rpow_lt_one : t ^ (q / p) < 1 := by
      simpa using Real.rpow_lt_rpow h_t.le h_t_lt_one h_q_div_p_pos
    have h_pref_pos : 0 < t ^ (-(1 / p) - 1) := Real.rpow_pos_of_pos h_t _
    have h_carrier_neg :
        t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1) < 0 := by
      rw [hsplit]
      have h_inner_neg : t ^ (q / p) - 1 < 0 := by
        linarith
      exact mul_neg_of_pos_of_neg h_pref_pos h_inner_neg
    have h_t_minus_one_neg : t - 1 < 0 := by
      linarith
    exact mul_pos_of_neg_of_neg h_t_minus_one_neg h_carrier_neg
  · -- On the right of the `ε`-gap, both factors are positive.
    have h_one_lt_t : 1 < t := by
      linarith
    have h_one_lt_rpow : 1 < t ^ (q / p) := by
      simpa using
        Real.rpow_lt_rpow (show 0 ≤ (1 : ℝ) by positivity) h_one_lt_t h_q_div_p_pos
    have h_pref_pos : 0 < t ^ (-(1 / p) - 1) := Real.rpow_pos_of_pos h_t _
    have h_carrier_pos :
        0 < t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1) := by
      rw [hsplit]
      have h_inner_pos : 0 < t ^ (q / p) - 1 := by
        linarith
      exact mul_pos h_pref_pos h_inner_pos
    have h_t_minus_one_pos : 0 < t - 1 := by
      linarith
    exact mul_pos h_t_minus_one_pos h_carrier_pos

/-- Helper for Theorem 7.29: in the balanced regime `q = p`, the normalized
mesh profile no longer depends on `n`. -/
lemma scaledMesh_eq_fixedMesh_of_q_eq_p
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q = p) {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    scaledMesh b c p q σ n t =
      (((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            (σ ^ 2) ^ (p / q)) ^ (1 / p))) := by
  -- Specialize the explicit mesh power law to the zero exponent `1 / p - 1 / q = 0`.
  rw [scaledMesh_eq_constant_mul_power
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
  rw [h_qp, sub_self, Real.rpow_zero]
  ring

/-- Helper for Theorem 7.29: in the balanced regime, the benchmark mesh freezes
to a single positive scale depending only on `t`. -/
abbrev scaledExpectedObjectiveBalance_qEqPFixedMesh
    (b c p q σ : ℝ) (t : ℝ) : ℝ :=
  ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
        (σ ^ 2) ^ (p / q)) ^ (1 / p))

/-- Helper for Theorem 7.29: the fixed mesh used in the `q = p` branch is
strictly positive on the positive normalized scale. -/
lemma scaledExpectedObjectiveBalance_qEqPFixedMesh_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q = p) {t : ℝ} (h_t : 0 < t) :
    0 < scaledExpectedObjectiveBalance_qEqPFixedMesh b c p q σ t := by
  -- Reuse the positive `scaledMesh` formula once, then freeze the balanced
  -- branch mesh with the `q = p` normalization.
  have h_mesh_pos :
      0 < scaledMesh b c p q σ 0 t := by
    exact
      scaledMesh_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_t 0
  rw [scaledMesh_eq_fixedMesh_of_q_eq_p
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_t 0] at h_mesh_pos
  simpa [scaledExpectedObjectiveBalance_qEqPFixedMesh] using h_mesh_pos

/-- Helper for Theorem 7.29: the `q < p` branch is driven by the same scalar
carrier as the predictive-risk derivative on the normalized `β_pred` scale. -/
abbrev scaledExpectedObjectiveBalance_qLtPCarrier
    (p q t : ℝ) : ℝ :=
  t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1)

/-- Helper for Theorem 7.29: away from `t = 1`, the small-mesh carrier admits a
uniform positive gap constant depending only on `ε`. -/
abbrev balanceCarrierGapConstant
    (p q ε : ℝ) : ℝ :=
  min (1 - (1 - ε) ^ (q / p)) ((1 + ε) ^ (q / p) - 1)

/-- Helper for Theorem 7.29: the away-from-`1` gap constant in the carrier
lower bound is strictly positive. -/
lemma balanceCarrierGapConstant_pos
    (h_p : 1 < p) (h_q : 1 < q)
    {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    0 < balanceCarrierGapConstant p q ε := by
  let a : ℝ := q / p
  have h_p_pos : 0 < p := by
    linarith
  have h_q_pos : 0 < q := by
    linarith
  have h_a_pos : 0 < a := by
    dsimp [a]
    exact div_pos h_q_pos h_p_pos
  have h_left_pos : 0 < 1 - (1 - ε) ^ a := by
    -- The left gap is positive because `0 < 1 - ε < 1` and the exponent `q / p` is positive.
    have h_base_nonneg : 0 ≤ 1 - ε := by
      linarith
    have h_base_lt_one : 1 - ε < 1 := by
      linarith
    have h_pow_lt_one : (1 - ε) ^ a < 1 := by
      simpa [Real.rpow_one] using Real.rpow_lt_rpow h_base_nonneg h_base_lt_one h_a_pos
    linarith
  have h_right_pos : 0 < (1 + ε) ^ a - 1 := by
    -- The right gap is positive because `1 + ε > 1` and positive powers preserve that inequality.
    have h_pow_gt_one : 1 < (1 + ε) ^ a := by
      simpa [Real.rpow_one] using
        Real.rpow_lt_rpow (show 0 ≤ (1 : ℝ) by positivity) (by linarith) h_a_pos
    linarith
  -- The minimum of two positive gap constants is still positive.
  exact lt_min h_left_pos h_right_pos

/-- Helper for Theorem 7.29: away from `t = 1`, the absolute value of the
small-mesh carrier dominates its positive prefactor by a uniform `ε`-gap. -/
lemma balanceCarrier_abs_lowerBound_offNeighborhood
    (h_p : 1 < p) (h_q : 1 < q)
    {ε t : ℝ} (h_t : 0 < t) (h_ε : 0 < ε) (h_ε_lt_one : ε < 1)
    (h_dist : ε ≤ dist t 1) :
    balanceCarrierGapConstant p q ε * t ^ (-(1 / p) - 1) ≤
      |scaledExpectedObjectiveBalance_qLtPCarrier p q t| := by
  let a : ℝ := q / p
  let pref : ℝ := t ^ (-(1 / p) - 1)
  have h_p_pos : 0 < p := by
    linarith
  have h_q_pos : 0 < q := by
    linarith
  have h_a_pos : 0 < a := by
    dsimp [a]
    exact div_pos h_q_pos h_p_pos
  have h_pref_pos : 0 < pref := by
    -- The explicit prefactor is positive on the positive half-line.
    dsimp [pref]
    exact Real.rpow_pos_of_pos h_t _
  have hsplit :
      scaledExpectedObjectiveBalance_qLtPCarrier p q t =
        pref * (t ^ a - 1) := by
    -- Factor the carrier so only the scalar gap `t ^ (q / p) - 1` controls the sign.
    dsimp [scaledExpectedObjectiveBalance_qLtPCarrier, pref, a]
    have hexp :
        (-(1 / p) - 1) + q / p = ((q - 1) / p) - 1 := by
      field_simp [ne_of_gt h_p_pos]
      ring
    calc
      t ^ (((q - 1) / p) - 1) - t ^ (-(1 / p) - 1)
          = t ^ ((-(1 / p) - 1) + q / p) - t ^ (-(1 / p) - 1) := by rw [hexp]
      _ = t ^ (-(1 / p) - 1) * t ^ (q / p) - t ^ (-(1 / p) - 1) := by
            rw [Real.rpow_add h_t]
      _ = pref * (t ^ a - 1) := by
            dsimp [pref, a]
            ring
  rcases le_one_sub_or_one_add_le_of_le_dist h_dist with h_left | h_right
  · have h_one_sub_pos : 0 < 1 - ε := by
      linarith
    have h_one_sub_nonneg : 0 ≤ 1 - ε := by
      linarith
    have h_pow_le : t ^ a ≤ (1 - ε) ^ a := by
      exact Real.rpow_le_rpow h_t.le h_left h_a_pos.le
    have h_pow_lt_one : (1 - ε) ^ a < 1 := by
      simpa [Real.rpow_one] using
        Real.rpow_lt_rpow h_one_sub_nonneg
          (show 1 - ε < (1 : ℝ) by linarith) h_a_pos
    have h_inner_neg : t ^ a - 1 < 0 := by
      linarith
    have h_abs :
        |scaledExpectedObjectiveBalance_qLtPCarrier p q t| =
          pref * (1 - t ^ a) := by
      -- On the left of the gap, the scalar carrier is negative, so the absolute value flips the sign.
      rw [hsplit, abs_of_neg]
      · ring
      · exact mul_neg_of_pos_of_neg h_pref_pos h_inner_neg
    have h_gap_le :
        balanceCarrierGapConstant p q ε ≤ 1 - t ^ a := by
      -- The uniform left-side gap is controlled by `1 - (1 - ε)^(q / p)`.
      calc
        balanceCarrierGapConstant p q ε ≤ 1 - (1 - ε) ^ a := by
          dsimp [balanceCarrierGapConstant, a]
          exact min_le_left _ _
        _ ≤ 1 - t ^ a := by
          linarith
    have h_mul_le :
        balanceCarrierGapConstant p q ε * pref ≤ pref * (1 - t ^ a) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right h_gap_le (le_of_lt h_pref_pos))
    simpa [pref] using h_mul_le.trans_eq h_abs.symm
  · have h_pow_ge : (1 + ε) ^ a ≤ t ^ a := by
      exact Real.rpow_le_rpow (show 0 ≤ 1 + ε by linarith) h_right h_a_pos.le
    have h_inner_pos : 0 < t ^ a - 1 := by
      have h_pow_gt_one : 1 < (1 + ε) ^ a := by
        simpa [Real.rpow_one] using
          Real.rpow_lt_rpow (show 0 ≤ (1 : ℝ) by positivity)
            (show (1 : ℝ) < 1 + ε by linarith) h_a_pos
      linarith
    have h_abs :
        |scaledExpectedObjectiveBalance_qLtPCarrier p q t| =
          pref * (t ^ a - 1) := by
      -- On the right of the gap, the scalar carrier is already positive.
      rw [hsplit, abs_of_pos]
      exact mul_pos h_pref_pos h_inner_pos
    have h_gap_le :
        balanceCarrierGapConstant p q ε ≤ t ^ a - 1 := by
      -- The uniform right-side gap is controlled by `(1 + ε)^(q / p) - 1`.
      calc
        balanceCarrierGapConstant p q ε ≤ (1 + ε) ^ a - 1 := by
          dsimp [balanceCarrierGapConstant, a]
          exact min_le_right _ _
        _ ≤ t ^ a - 1 := by
          linarith
    have h_mul_le :
        balanceCarrierGapConstant p q ε * pref ≤ pref * (t ^ a - 1) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right h_gap_le (le_of_lt h_pref_pos))
    simpa [pref] using h_mul_le.trans_eq h_abs.symm

/-- Helper for Theorem 7.29: the leading positive scalar in the `q < p`
small-mesh balance comparison is the predictive derivative prefactor evaluated
at `β_pred(n.succ)`. -/
abbrev scaledExpectedObjectiveBalance_qLtPMainPrefactor
    (b c p q σ : ℝ) (n : ℕ) : ℝ :=
  ((q - 1) / p) *
    TikhonovPredictiveRisk.predictiveRiskC1 b c p q *
      (TikhonovPredictiveRisk.betaPred b c p q σ n.succ) ^ ((q - 1) / p)

/-- Helper for Theorem 7.29: after isolating the predictive derivative carrier,
the remaining `q < p` balance error is recorded as a named remainder. -/
abbrev scaledExpectedObjectiveBalance_qLtPRemainder
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  scaledExpectedObjectiveBalance b c p q σ n t -
    scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n *
      scaledExpectedObjectiveBalance_qLtPCarrier p q t

/-- Helper for Theorem 7.29: the `q < p` main prefactor is strictly positive
at every positive data size. -/
lemma scaledExpectedObjectiveBalance_qLtPMainPrefactor_pos
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ) :
    0 < scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n := by
  have h_p_pos : 0 < p := by
    linarith
  have h_qm1_pos : 0 < q - 1 := by
    linarith
  have h_beta_pos :
      0 < TikhonovPredictiveRisk.betaPred b c p q σ n.succ := by
    -- The predictive benchmark stays positive on the shifted data-size scale.
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  -- Every factor in the normalized predictive derivative prefactor is positive.
  dsimp [scaledExpectedObjectiveBalance_qLtPMainPrefactor]
  exact mul_pos
    (mul_pos
      (div_pos h_qm1_pos h_p_pos)
      (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated)
      )
    (Real.rpow_pos_of_pos h_beta_pos _)

/-- Helper for Theorem 7.29: the `q < p` branch is exactly the predictive
derivative carrier times its positive main prefactor plus a named remainder. -/
lemma scaledExpectedObjectiveBalance_qLtP_eq_mainPrefactor_mulCarrier_addRemainder
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) :
    scaledExpectedObjectiveBalance b c p q σ n t =
      scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n *
          scaledExpectedObjectiveBalance_qLtPCarrier p q t +
        scaledExpectedObjectiveBalance_qLtPRemainder b c p q σ n t := by
  -- Package the exact normalization so the eventual sign proof only needs a
  -- separate domination estimate for the named remainder.
  dsimp [scaledExpectedObjectiveBalance_qLtPRemainder]
  ring

/-- Helper for Theorem 7.29: in the small-mesh regime `q < p`, Proposition
7.19 should dominate the named remainder by half of the main carrier away from
the normalized benchmark `t = 1`. -/
lemma scaledExpectedObjectiveBalance_qLtP_remainder_lt_halfGapProfile_offNeighborhood
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q < p) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          |scaledExpectedObjectiveBalance_qLtPRemainder b c p q σ n t| ≤
            (scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2) *
              (balanceCarrierGapConstant p q ε * t ^ (-(1 / p) - 1)) := by
  -- Route correction: isolate the Proposition 7.19 output at the explicit
  -- gap profile before transporting it to the carrier lower bound.
  -- TODO: specialize the `quadratureApprox*_isBigO` bounds along the mapped
  -- filter `n ↦ (n.succ, scaledMesh ... n t)`, extract a uniform pointwise
  -- scalar estimate against the gap model
  -- `balanceCarrierGapConstant p q ε * t ^ (-(1 / p) - 1)`, and then pass the
  -- resulting bound to the carrier comparison theorem below.
  sorry

/-- Helper for Theorem 7.29: in the small-mesh regime `q < p`, Proposition
7.19 dominates the named remainder by half of the carrier once the explicit
gap profile is transported through the carrier lower bound. -/
lemma scaledExpectedObjectiveBalance_qLtP_remainder_lt_halfCarrier_offNeighborhood
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q < p) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          |scaledExpectedObjectiveBalance_qLtPRemainder b c p q σ n t| ≤
            (scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2) *
              |scaledExpectedObjectiveBalance_qLtPCarrier p q t| := by
  filter_upwards
    [scaledExpectedObjectiveBalance_qLtP_remainder_lt_halfGapProfile_offNeighborhood
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_ε h_ε_lt_one] with n hn
  intro t h_t h_dist
  have h_pref_nonneg :
      0 ≤ scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2 := by
    have h_pref_pos :
        0 < scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n :=
      scaledExpectedObjectiveBalance_qLtPMainPrefactor_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated n
    positivity
  have h_gap_le_carrier :
      balanceCarrierGapConstant p q ε * t ^ (-(1 / p) - 1) ≤
        |scaledExpectedObjectiveBalance_qLtPCarrier p q t| := by
    -- Transport the explicit gap model to the carrier itself away from `t = 1`.
    exact
      balanceCarrier_abs_lowerBound_offNeighborhood
        (p := p) (q := q) h_p h_q h_t h_ε h_ε_lt_one h_dist
  -- Finish the carrier bound by one monotone multiplication step.
  calc
    |scaledExpectedObjectiveBalance_qLtPRemainder b c p q σ n t| ≤
        (scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2) *
          (balanceCarrierGapConstant p q ε * t ^ (-(1 / p) - 1)) := by
            exact hn t h_t h_dist
    _ ≤
        (scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2) *
          |scaledExpectedObjectiveBalance_qLtPCarrier p q t| := by
            exact mul_le_mul_of_nonneg_left h_gap_le_carrier h_pref_nonneg

/-- Helper for Theorem 7.29: once the positive chain-rule factor has been
split by the three Chapter 7 mesh regimes, the small-mesh branch `q < p`
reduces to a pure sign statement for the normalized balance term. -/
lemma scaledExpectedObjectiveBalance_qLtP_eventually_sign
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q < p) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) * scaledExpectedObjectiveBalance b c p q σ n t > 0 := by
  filter_upwards
    [scaledExpectedObjectiveBalance_qLtP_remainder_lt_halfCarrier_offNeighborhood
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_ε h_ε_lt_one] with n hn
  intro t h_t h_dist
  let pref := scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n
  let carrier := scaledExpectedObjectiveBalance_qLtPCarrier p q t
  let remainder := scaledExpectedObjectiveBalance_qLtPRemainder b c p q σ n t
  have h_pref_pos : 0 < pref := by
    -- The dominant predictive derivative prefactor never changes sign.
    dsimp [pref]
    exact
      scaledExpectedObjectiveBalance_qLtPMainPrefactor_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated n
  have h_main :
      scaledExpectedObjectiveBalance b c p q σ n t =
        pref * carrier + remainder := by
    -- Rewrite the balance once into the main carrier plus the named remainder.
    simpa [pref, carrier, remainder] using
      scaledExpectedObjectiveBalance_qLtP_eq_mainPrefactor_mulCarrier_addRemainder
        b c p q σ n t
  have h_dom :
      |remainder| ≤ (pref / 2) * |carrier| := by
    -- The remaining work from Proposition 7.19 is packaged as a single
    -- quantitative domination estimate.
    simpa [pref, carrier, remainder] using hn t h_t h_dist
  have h_sign :
      (t - 1) * carrier > 0 := by
    -- The scalar carrier already has the sign of `t - 1` away from `1`.
    simpa [carrier, scaledExpectedObjectiveBalance_qLtPCarrier] using
      balanceCarrier_sign_offNeighborhood
        (p := p) (q := q) h_p h_q h_t h_ε h_ε_lt_one h_dist
  rcases le_one_sub_or_one_add_le_of_le_dist h_dist with h_left | h_right
  · have h_t_minus_one_neg : t - 1 < 0 := by
      linarith
    have h_carrier_neg : carrier < 0 := by
      by_contra h_nonneg
      have h_mul_nonpos :
          (t - 1) * carrier ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_t_minus_one_neg) (le_of_not_gt h_nonneg)
      linarith
    have h_remainder_le_abs : remainder ≤ |remainder| := le_abs_self remainder
    have h_abs_carrier : |carrier| = -carrier := abs_of_neg h_carrier_neg
    have h_balance_neg :
        scaledExpectedObjectiveBalance b c p q σ n t < 0 := by
      -- On the left side of the gap, the carrier is negative and the
      -- remainder is too small to flip the sign.
      rw [h_main]
      calc
        pref * carrier + remainder ≤ pref * carrier + |remainder| := by
          linarith
        _ ≤ pref * carrier + (pref / 2) * |carrier| := by
          linarith
        _ = (pref / 2) * carrier := by
          rw [h_abs_carrier]
          ring
        _ < 0 := by
          nlinarith
    exact mul_pos_of_neg_of_neg h_t_minus_one_neg h_balance_neg
  · have h_t_minus_one_pos : 0 < t - 1 := by
      linarith
    have h_carrier_pos : 0 < carrier := by
      by_contra h_nonpos
      have h_mul_nonpos :
          (t - 1) * carrier ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_t_minus_one_pos) (le_of_not_gt h_nonpos)
      linarith
    have h_abs_carrier : |carrier| = carrier := abs_of_pos h_carrier_pos
    have h_balance_pos :
        0 < scaledExpectedObjectiveBalance b c p q σ n t := by
      -- On the right side of the gap, the same domination estimate keeps the
      -- corrected balance positive.
      rw [h_main]
      have h_lower :
          pref * carrier - |remainder| ≤ pref * carrier + remainder := by
        linarith [neg_abs_le remainder]
      have h_strict_lower :
          0 < pref * carrier - |remainder| := by
        calc
          0 < (pref / 2) * carrier := by
            positivity
          _ = pref * carrier - (pref / 2) * |carrier| := by
            rw [h_abs_carrier]
            ring
          _ ≤ pref * carrier - |remainder| := by
            linarith
      exact lt_of_lt_of_le h_strict_lower h_lower
    exact mul_pos h_t_minus_one_pos h_balance_pos

/-- Helper for Theorem 7.29: in the balanced regime `q = p`, the sign problem
for the normalized balance term should be handled by the fixed-mesh profile. -/
lemma scaledExpectedObjectiveBalance_qEqP_eq_fixedQuadratureBalance
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q = p) {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    let h := scaledExpectedObjectiveBalance_qEqPFixedMesh b c p q σ t
    scaledExpectedObjectiveBalance b c p q σ n t =
      ((((2 * p * b * c / (n.succ : ℝ)) * h ^ (2 * p - 2) *
            KernelMoment.quadratureSum p 3 0 n.succ h) +
          ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
            KernelMoment.quadratureSum p 3 (2 * p) n.succ h)) *
        meshProfileDefect p n h) -
      (2 : ℝ) *
        (((b * c * h ^ (2 * p - 1) / (n.succ : ℝ)) *
            KernelMoment.quadratureSum p 2 0 n.succ h) +
          ((σ ^ 2 / ((n.succ : ℝ) * h)) *
            KernelMoment.quadratureSum p 2 (2 * p) n.succ h)) *
        ((p / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 2 p n.succ h) := by
  -- Rewrite the exact balance once, then freeze the mesh and the `p - q`
  -- exponent so the balanced branch can work with a fixed-step profile.
  rw [scaledExpectedObjectiveBalance_eq_quadratureBalance
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n]
  rw [scaledMesh_eq_fixedMesh_of_q_eq_p
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_t n]
  have h_exp_two : p + p - 2 = 2 * p - 2 := by ring
  have h_exp_one : p + p - 1 = 2 * p - 1 := by ring
  have h_sub : p - p = (0 : ℝ) := by ring
  simp only [scaledExpectedObjectiveBalance_qEqPFixedMesh, h_qp, h_exp_two, h_exp_one, h_sub]

/-- Helper for Theorem 7.29: rewriting the balance with the explicit
power-law mesh isolates the exact large-mesh spelling used in the `p < q`
branch. -/
lemma scaledExpectedObjectiveBalance_eq_explicitMeshQuadratureBalance
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {t : ℝ} (h_t : 0 < t) (n : ℕ) :
    let h :=
      ((((t * TikhonovPredictiveRisk.betaPredConstant b c p q) / c) *
            (σ ^ 2) ^ (p / q)) ^ (1 / p)) *
        (n.succ : ℝ) ^ (1 / p - 1 / q)
    scaledExpectedObjectiveBalance b c p q σ n t =
      ((((2 * p * b * c / (n.succ : ℝ)) * h ^ (p + q - 2) *
            KernelMoment.quadratureSum p 3 (p - q) n.succ h) +
          ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
            KernelMoment.quadratureSum p 3 (2 * p) n.succ h)) *
        meshProfileDefect p n h) -
      (2 : ℝ) *
        (((b * c * h ^ (p + q - 1) / (n.succ : ℝ)) *
            KernelMoment.quadratureSum p 2 (p - q) n.succ h) +
          ((σ ^ 2 / ((n.succ : ℝ) * h)) *
            KernelMoment.quadratureSum p 2 (2 * p) n.succ h)) *
        ((p / ((n.succ : ℝ) * h ^ 2)) *
          KernelMoment.quadratureSum p 2 p n.succ h) := by
  -- Normalize the mesh with the explicit constant-times-power law before the
  -- large-mesh branch factors out its dominant scale.
  simpa [scaledMesh_eq_constant_mul_power
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated h_t n] using
    (scaledExpectedObjectiveBalance_eq_quadratureBalance
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_t n)

/-- Helper for Theorem 7.29: in the large-mesh regime `p < q`, the balance is
split against the same scalar carrier and predictive prefactor, with the
remaining comparison error packaged as a named remainder. -/
abbrev scaledExpectedObjectiveBalance_qGtPRemainder
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  scaledExpectedObjectiveBalance b c p q σ n t -
    scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n *
      scaledExpectedObjectiveBalance_qLtPCarrier p q t

/-- Helper for Theorem 7.29: the large-mesh branch is rewritten as the common
predictive comparison term plus its named remainder. -/
lemma scaledExpectedObjectiveBalance_qGtP_eq_mainPrefactor_mulCarrier_addRemainder
    (b c p q σ : ℝ) (n : ℕ) (t : ℝ) :
    scaledExpectedObjectiveBalance b c p q σ n t =
      scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n *
          scaledExpectedObjectiveBalance_qLtPCarrier p q t +
        scaledExpectedObjectiveBalance_qGtPRemainder b c p q σ n t := by
  -- Package the comparison splitting once so the large-mesh sign proof only
  -- needs a separate remainder domination theorem.
  dsimp [scaledExpectedObjectiveBalance_qGtPRemainder]
  ring

/-- Helper for Theorem 7.29: for a positive large-mesh variable `x`, the first
reciprocal kernel differs from its leading `x⁻¹` term by at most the square
tail `x⁻²`. -/
lemma largeMeshReciprocal_error_abs_le_invSq
    {x : ℝ} (h_x : 0 < x) :
    |1 / (1 + x) - 1 / x| ≤ 1 / x ^ (2 : ℕ) := by
  have h_one_add_pos : 0 < 1 + x := by
    linarith
  have h_diff_nonpos : 1 / (1 + x) - 1 / x ≤ 0 := by
    -- The larger denominator `1 + x` makes the first reciprocal smaller.
    exact sub_nonpos.mpr (one_div_le_one_div_of_le h_x (by linarith : x ≤ 1 + x))
  have h_prod_le : x ^ (2 : ℕ) ≤ x * (1 + x) := by
    nlinarith
  have h_prod_pos : 0 < x ^ (2 : ℕ) := by
    positivity
  have h_recip_bound : 1 / (x * (1 + x)) ≤ 1 / x ^ (2 : ℕ) := by
    -- Bounding the exact error reduces to comparing the two positive denominators.
    simpa [pow_two] using one_div_le_one_div_of_le h_prod_pos h_prod_le
  calc
    |1 / (1 + x) - 1 / x|
        = -(1 / (1 + x) - 1 / x) := by
            exact abs_of_nonpos h_diff_nonpos
    _ = 1 / x - 1 / (1 + x) := by
          ring
    _ = 1 / (x * (1 + x)) := by
          field_simp [h_x.ne', h_one_add_pos.ne']
          ring
    _ ≤ 1 / x ^ (2 : ℕ) := h_recip_bound

/-- Helper for Theorem 7.29: the fixed-mesh variance profile satisfies the
algebraic decomposition `x² / (1 + x)² = 1 - 2 / (1 + x) + 1 / (1 + x)²`
used in the balanced branch. -/
lemma modeProfileSquare_eq_one_sub_twoDiv_add_invSq
    {x : ℝ} (h_x : 0 < x) :
    x ^ (2 : ℕ) / (1 + x) ^ (2 : ℕ) =
      1 - 2 / (1 + x) + 1 / (1 + x) ^ (2 : ℕ) := by
  have h_den_ne : (1 + x) ^ (2 : ℕ) ≠ 0 := by
    positivity
  -- Clear the positive square denominator and normalize the numerator once.
  field_simp [h_den_ne, h_x.ne', h_x.ne'.symm]
  ring

/-- Helper for Theorem 7.29: in the large-mesh regime `p < q`, the remaining
comparison error should be dominated by half of the common carrier away from
the normalized benchmark `t = 1`. -/
lemma scaledExpectedObjectiveBalance_qGtP_remainder_lt_halfCarrier_offNeighborhood
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_pq : p < q) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          |scaledExpectedObjectiveBalance_qGtPRemainder b c p q σ n t| ≤
            (scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n / 2) *
              |scaledExpectedObjectiveBalance_qLtPCarrier p q t| := by
  -- Route correction: keep the explicit-mesh branch on the same
  -- carrier-plus-remainder interface as `q < p`, and postpone only the final
  -- uniform domination estimate.
  -- TODO: factor the explicit power-law mesh normal form by the common
  -- predictive prefactor, bound the resulting remainder against the same
  -- off-neighborhood carrier profile, and then reuse the sign assembly below.
  sorry

/-- Helper for Theorem 7.29: in the balanced regime `q = p`, the sign problem
for the normalized balance term should be handled by the fixed-mesh profile. -/
lemma scaledExpectedObjectiveBalance_qEqP_eventually_sign
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_qp : q = p) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) * scaledExpectedObjectiveBalance b c p q σ n t > 0 := by
  -- Route correction: this branch is not small-mesh. Freeze the mesh with
  -- `scaledMesh_eq_fixedMesh_of_q_eq_p`, pass the finite quadrature sums to the
  -- fixed-step series profile, and prove that profile has the sign of `t - 1`.
  filter_upwards [] with n
  intro t h_t h_dist
  let h := scaledExpectedObjectiveBalance_qEqPFixedMesh b c p q σ t
  have h_h_pos : 0 < h := by
    -- Record the fixed balanced-branch mesh positivity once before passing to
    -- the fixed-step quadrature profile.
    dsimp [h]
    exact
      scaledExpectedObjectiveBalance_qEqPFixedMesh_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_t
  have h_main :
      scaledExpectedObjectiveBalance b c p q σ n t =
        ((((2 * p * b * c / (n.succ : ℝ)) * h ^ (2 * p - 2) *
              KernelMoment.quadratureSum p 3 0 n.succ h) +
            ((2 * p * σ ^ 2 / ((n.succ : ℝ) * h ^ 2)) *
              KernelMoment.quadratureSum p 3 (2 * p) n.succ h)) *
          meshProfileDefect p n h) -
        (2 : ℝ) *
          (((b * c * h ^ (2 * p - 1) / (n.succ : ℝ)) *
              KernelMoment.quadratureSum p 2 0 n.succ h) +
            ((σ ^ 2 / ((n.succ : ℝ) * h)) *
              KernelMoment.quadratureSum p 2 (2 * p) n.succ h)) *
          ((p / ((n.succ : ℝ) * h ^ 2)) *
            KernelMoment.quadratureSum p 2 p n.succ h) := by
    -- Rewrite the exact balance into the fixed-step quadrature normal form.
    simpa [h] using
      scaledExpectedObjectiveBalance_qEqP_eq_fixedQuadratureBalance
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_t n
  -- Route correction: the previous fixed-profile sign plan is blocked by a
  -- balanced-regime mismatch. The exact `q = p` quotient normal form above,
  -- evaluated on concrete positive data such as `p = q = 2`, `b = c = σ = 1`,
  -- and `t = 2`, gives a negative balance value instead of the required
  -- positive one, so the current benchmark/sign claim needs statement repair
  -- or a different balanced benchmark rather than more of the same limit proof.
  sorry

/-- Helper for Theorem 7.29: in the large-mesh regime `p < q`, the normalized
balance term should be analyzed after factoring a common positive mesh power. -/
lemma scaledExpectedObjectiveBalance_qGtP_eventually_sign
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_pq : p < q) {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) * scaledExpectedObjectiveBalance b c p q σ n t > 0 := by
  filter_upwards
    [scaledExpectedObjectiveBalance_qGtP_remainder_lt_halfCarrier_offNeighborhood
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_pq h_ε h_ε_lt_one] with n hn
  intro t h_t h_dist
  let pref := scaledExpectedObjectiveBalance_qLtPMainPrefactor b c p q σ n
  let carrier := scaledExpectedObjectiveBalance_qLtPCarrier p q t
  let remainder := scaledExpectedObjectiveBalance_qGtPRemainder b c p q σ n t
  have h_pref_pos : 0 < pref := by
    -- The common predictive comparison prefactor stays positive in every regime.
    dsimp [pref]
    exact
      scaledExpectedObjectiveBalance_qLtPMainPrefactor_pos
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated n
  have h_main :
      scaledExpectedObjectiveBalance b c p q σ n t =
        pref * carrier + remainder := by
    -- Rewrite the large-mesh branch into the common carrier plus the named
    -- comparison remainder.
    simpa [pref, carrier, remainder] using
      scaledExpectedObjectiveBalance_qGtP_eq_mainPrefactor_mulCarrier_addRemainder
        b c p q σ n t
  have h_dom :
      |remainder| ≤ (pref / 2) * |carrier| := by
    -- The explicit-mesh asymptotic work is packaged as a single domination estimate.
    simpa [pref, carrier, remainder] using hn t h_t h_dist
  have h_sign :
      (t - 1) * carrier > 0 := by
    -- The same scalar carrier already has the sign of `t - 1` away from `1`.
    simpa [carrier, scaledExpectedObjectiveBalance_qLtPCarrier] using
      balanceCarrier_sign_offNeighborhood
        (p := p) (q := q) h_p h_q h_t h_ε h_ε_lt_one h_dist
  rcases le_one_sub_or_one_add_le_of_le_dist h_dist with h_left | h_right
  · have h_t_minus_one_neg : t - 1 < 0 := by
      linarith
    have h_carrier_neg : carrier < 0 := by
      by_contra h_nonneg
      have h_mul_nonpos :
          (t - 1) * carrier ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_t_minus_one_neg) (le_of_not_gt h_nonneg)
      linarith
    have h_remainder_le_abs : remainder ≤ |remainder| := le_abs_self remainder
    have h_abs_carrier : |carrier| = -carrier := abs_of_neg h_carrier_neg
    have h_balance_neg :
        scaledExpectedObjectiveBalance b c p q σ n t < 0 := by
      -- On the left side of the gap, the carrier is negative and the
      -- remainder is too small to flip the sign.
      rw [h_main]
      calc
        pref * carrier + remainder ≤ pref * carrier + |remainder| := by
          linarith
        _ ≤ pref * carrier + (pref / 2) * |carrier| := by
          linarith
        _ = (pref / 2) * carrier := by
          rw [h_abs_carrier]
          ring
        _ < 0 := by
          nlinarith
    exact mul_pos_of_neg_of_neg h_t_minus_one_neg h_balance_neg
  · have h_t_minus_one_pos : 0 < t - 1 := by
      linarith
    have h_carrier_pos : 0 < carrier := by
      by_contra h_nonpos
      have h_mul_nonpos :
          (t - 1) * carrier ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_t_minus_one_pos) (le_of_not_gt h_nonpos)
      linarith
    have h_abs_carrier : |carrier| = carrier := abs_of_pos h_carrier_pos
    have h_balance_pos :
        0 < scaledExpectedObjectiveBalance b c p q σ n t := by
      -- On the right side of the gap, the same domination estimate keeps the
      -- corrected balance positive.
      rw [h_main]
      have h_lower :
          pref * carrier - |remainder| ≤ pref * carrier + remainder := by
        linarith [neg_abs_le remainder]
      have h_strict_lower :
          0 < pref * carrier - |remainder| := by
        calc
          0 < (pref / 2) * carrier := by
            positivity
          _ = pref * carrier - (pref / 2) * |carrier| := by
            rw [h_abs_carrier]
            ring
          _ ≤ pref * carrier - |remainder| := by
            linarith
      exact lt_of_lt_of_le h_strict_lower h_lower
    exact mul_pos h_t_minus_one_pos h_balance_pos

/-- Helper for Theorem 7.29: once the positive chain-rule factor has been
removed, the remaining frontier is the eventual sign of the explicit balance
term. -/
lemma scaledExpectedObjectiveBalance_sign_offNeighborhood_eventually
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) * scaledExpectedObjectiveBalance b c p q σ n t > 0 := by
  -- Route correction: the remaining sign theorem should no longer be attacked
  -- monolithically. Dispatch to the three regime-local balance lemmas and keep
  -- the downstream derivative-sign pipeline unchanged.
  rcases lt_trichotomy q p with h_qp | h_qp | h_pq
  · -- In the small-mesh regime, reuse the dedicated Proposition 7.19 branch.
    exact
      scaledExpectedObjectiveBalance_qLtP_eventually_sign
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_ε h_ε_lt_one
  · -- In the balanced regime, the mesh is fixed and the fixed-profile branch applies.
    exact
      scaledExpectedObjectiveBalance_qEqP_eventually_sign
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_qp h_ε h_ε_lt_one
  · -- In the large-mesh regime, reuse the dedicated residual-profile branch.
    exact
      scaledExpectedObjectiveBalance_qGtP_eventually_sign
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated h_pq h_ε h_ε_lt_one

/-- Helper for Theorem 7.29: on the normalized `β_pred` scale, the remaining
frontier is the eventual sign of the derivative of the exact scaled expected
GCV family itself. -/
lemma scaledExpectedObjectiveDeriv_sign_offNeighborhood_eventually
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) *
            deriv
                (fun u : ℝ ↦
                  expectedObjective μ K R fTrue η n
                    (u * TikhonovPredictiveRisk.betaPred b c p q σ n.succ))
                t >
            0 := by
  have h_balance :=
    scaledExpectedObjectiveBalance_sign_offNeighborhood_eventually
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated h_ε h_ε_lt_one
  filter_upwards [h_balance] with n hn
  intro t ht hdist
  -- Route correction: the spelling transport and derivative normalization are
  -- now isolated, so only the balance sign remains as the asymptotic input.
  rw [scaledExpectedObjective_deriv_eq_meshProfileCompositeDeriv
    (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
    (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated
    h_white h_svd h_tikhonov h_singularValueSquareDecay
    h_fourierCoefficientSquareDecay ht n]
  rw [scaledExpectedObjectiveDeriv_eq_positiveFactor_mulBalance
    (b := b) (c := c) (p := p) (q := q) (σ := σ)
    h_b h_c h_p h_q h_σ h_nonsaturated ht n]
  have h_factor_pos :
      0 < scaledExpectedObjectivePositiveFactor b c p q σ n t :=
    scaledExpectedObjectivePositiveFactor_pos
      (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated ht n
  have h_balance_pos :
      (t - 1) * scaledExpectedObjectiveBalance b c p q σ n t > 0 :=
    hn t ht hdist
  -- Pull the positive factor out to the left so the sign reduces to the
  -- explicit balance statement proved upstream.
  have h_rearrange :
      (t - 1) *
          (scaledExpectedObjectivePositiveFactor b c p q σ n t *
            scaledExpectedObjectiveBalance b c p q σ n t) =
        scaledExpectedObjectivePositiveFactor b c p q σ n t *
          ((t - 1) * scaledExpectedObjectiveBalance b c p q σ n t) := by
    ring
  rw [h_rearrange]
  exact mul_pos h_factor_pos h_balance_pos

/-- Helper for Theorem 7.29: uniformly away from the normalized benchmark
scale `t = 1`, the derivative of the expected GCV objective on the
`t * β_pred` scale eventually has the same sign as `t - 1`. -/
lemma expectedObjectiveDeriv_scaledBeta_sign_offNeighborhood_eventually
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {ε : ℝ} (h_ε : 0 < ε) (h_ε_lt_one : ε < 1) :
    ∀ᶠ n in Filter.atTop,
      ∀ t > 0,
        ε ≤ dist t 1 →
          (t - 1) *
              deriv (expectedObjective μ K R fTrue η n)
                (t * TikhonovPredictiveRisk.betaPred b c p q σ n.succ) >
            0 := by
  have h_scaled :=
    scaledExpectedObjectiveDeriv_sign_offNeighborhood_eventually
      (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
      (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated
      h_white h_svd h_tikhonov h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay h_ε h_ε_lt_one
  filter_upwards [h_scaled] with n hn
  intro t ht hdist
  let β := TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  have hβ_pos : 0 < β := by
    -- The predictive root factor stays positive, so the chain-rule rescaling
    -- preserves the sign of the derivative.
    dsimp [β]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have h_scaled_pos :
      β *
          ((t - 1) *
            deriv (expectedObjective μ K R fTrue η n) (t * β)) >
        0 := by
    -- Rewrite the scaled derivative through the chain rule and factor out the
    -- positive constant `β_pred`.
    have hchain :=
      scaledExpectedObjective_deriv_eq_betaPred_mul
        (μ := μ) (K := K) (R := R) (fTrue := fTrue) (η := η)
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated n t
    have hraw :
        (t - 1) *
            deriv
              (fun u : ℝ ↦
                expectedObjective μ K R fTrue η n (u * β))
              t >
          0 := by
      simpa [β] using hn t ht hdist
    rw [hchain] at hraw
    simpa [β, mul_assoc, mul_left_comm, mul_comm] using hraw
  exact (mul_pos_iff_of_pos_left hβ_pos).mp h_scaled_pos

/-- Helper for Theorem 7.29: after rewriting the expected GCV objective into
its spectral ratio form, any minimizing family is asymptotically equivalent to
the shifted predictive benchmark `β_pred`. -/
lemma gcvOptimalFamily_isAsymptoticallyOptimal_betaPredSucc
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {alphaV : ℕ → ℝ}
    (h_alphaV_pos : ∀ n, alphaV n ∈ Set.Ioi (0 : ℝ))
    (h_alphaV :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K R fTrue η)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        alphaV) :
    Asymptotics.IsEquivalent Filter.atTop
      alphaV
      (fun n ↦ TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
  let betaN : ℕ → ℝ := fun n ↦ TikhonovPredictiveRisk.betaPred b c p q σ n.succ
  let tN : ℕ → ℝ := fun n ↦ alphaV n / betaN n
  have h_alphaV_min :=
    (ParameterChoice.isOptimalParameterFamily_iff
      (expectedObjective μ K R fTrue η)
      (fun _ ↦ Set.Ioi (0 : ℝ))
      alphaV).1 h_alphaV
  have h_alphaV_min' : ∀ n x, x ∈ Set.Ioi (0 : ℝ) →
      expectedObjective μ K R fTrue η n (alphaV n) ≤
        expectedObjective μ K R fTrue η n x := by
    intro n x hx
    -- Unpack the `IsMinOn` witness to a pointwise comparison on the
    -- admissible positive half-line.
    have hmin_n : ∀ y ∈ Set.Ioi (0 : ℝ),
        expectedObjective μ K R fTrue η n (alphaV n) ≤
          expectedObjective μ K R fTrue η n y := by
      simpa [isMinOn_iff] using h_alphaV_min n
    exact hmin_n x hx
  have h_betaN_pos : ∀ n, 0 < betaN n := by
    intro n
    -- The predictive benchmark stays in the positive admissible region.
    dsimp [betaN]
    exact
      betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated
        ⟨n.succ, Nat.succ_pos n⟩
  have h_tN_pos : ∀ n, 0 < tN n := by
    intro n
    -- The ratio `t_n = α_V / β_pred` is positive because both factors are.
    dsimp [tN]
    exact div_pos (h_alphaV_pos n) (h_betaN_pos n)
  have h_min_le_beta : ∀ n,
      expectedObjective μ K R fTrue η n (alphaV n) ≤
        expectedObjective μ K R fTrue η n (betaN n) := by
    intro n
    -- Compare the GCV minimizer against the positive predictive benchmark.
    exact h_alphaV_min' n (betaN n) (h_betaN_pos n)
  have h_alphaV_eq : ∀ n, alphaV n = tN n * betaN n := by
    intro n
    -- Re-express `α_V` on the `β_pred` scale so the ratio is ready for the
    -- asymptotic normalization step.
    dsimp [tN]
    field_simp [ne_of_gt (h_betaN_pos n)]
  have h_deriv_zero : ∀ n, deriv (expectedObjective μ K R fTrue η n) (alphaV n) = 0 :=
    expectedObjectiveDeriv_zero_of_optimalFamily
      (μ := μ) (K := K) (R := R) (fTrue := fTrue) (η := η)
      h_alphaV_pos h_alphaV
  have h_tN_tendsto_one : Filter.Tendsto tN Filter.atTop (nhds 1) := by
    -- Use the eventual derivative sign away from `t = 1` to force the
    -- minimizing ratio `t_n = α_V / β_pred` into every small metric ball.
    refine Metric.tendsto_nhds.2 ?_
    intro ε h_ε
    let δ : ℝ := min ε (1 / 2 : ℝ)
    have h_δ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min h_ε (by norm_num)
    have h_δ_lt_one : δ < 1 := by
      dsimp [δ]
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have h_sign :=
      expectedObjectiveDeriv_scaledBeta_sign_offNeighborhood_eventually
        (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
        (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated
        h_white h_svd h_tikhonov h_singularValueSquareDecay
        h_fourierCoefficientSquareDecay h_δ_pos h_δ_lt_one
    filter_upwards [h_sign] with n hn
    have h_not_far : ¬ δ ≤ dist (tN n) 1 := by
      intro h_far
      have h_deriv_sign :
          (tN n - 1) * deriv (expectedObjective μ K R fTrue η n) (tN n * betaN n) > 0 := by
        simpa [betaN] using hn (tN n) (h_tN_pos n) h_far
      have h_deriv_alphaV :
          (tN n - 1) * deriv (expectedObjective μ K R fTrue η n) (alphaV n) > 0 := by
        simpa [h_alphaV_eq n] using h_deriv_sign
      have h_zero_not_pos :
          ¬ (0 : ℝ) > 0 := by
        linarith
      have h_zero_pos : (0 : ℝ) > 0 := by
        simpa [h_deriv_zero n] using h_deriv_alphaV
      exact h_zero_not_pos h_zero_pos
    have h_dist_lt_δ : dist (tN n) 1 < δ :=
      lt_of_not_ge h_not_far
    have h_delta_le_eps : δ ≤ ε := by
      simp [δ]
    exact lt_of_lt_of_le h_dist_lt_δ h_delta_le_eps
  have h_betaN_ne : ∀ᶠ n in Filter.atTop, betaN n ≠ 0 :=
    Filter.Eventually.of_forall fun n ↦ ne_of_gt (h_betaN_pos n)
  -- Convert the ratio limit `α_V / β_pred → 1` into asymptotic equivalence.
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_betaN_ne]
  change Filter.Tendsto (fun n ↦ alphaV n / betaN n) Filter.atTop (nhds 1)
  exact h_tN_tendsto_one

/-- thm_7_29. Theorem 7.29 (GCV for Tikhonov Regularization). Main labeled
source-facing entry.

For a concrete discrete Tikhonov family whose expected GCV objective
`expectedObjective` is minimized by a positive parameter family `α_V` on
`Set.Ioi (0 : ℝ)`, any positive predictive-risk minimizing family `α_pred` for
the Chapter 7 objective `(7.86)` is asymptotically equivalent to `α_V` in the
nonsaturated regime `p - q > -1`. The previous Chapter 7 setup is recorded
explicitly through the white-noise, SVD, Tikhonov-filter, and decay
hypotheses. -/
theorem isAsymptoticallyOptimal_of_optimalFamily
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (h_white :
      ∀ n, FilterRegularization.HasSemidiscreteWhiteNoiseModel μ (η n) σ)
    (h_svd :
      ∀ n, K n = U n * Matrix.diagonal (s n) * (V n)ᵀ)
    (h_tikhonov :
      ∀ n α,
        HasReconstructionSpectralRep
          (R n α)
          (U n)
          (V n)
          (SpectralFilter.discreteTikhonov n.succ α)
          (s n))
    (h_singularValueSquareDecay :
      ∀ n (i : Fin n.succ),
        s n i ^ 2 = c * ((i.1.succ : ℕ) : ℝ) ^ (-p))
    (h_fourierCoefficientSquareDecay :
      ∀ n (i : Fin n.succ),
        (((V n)ᵀ).toEuclideanLin (fTrue n) i) ^ 2 =
          b * ((i.1.succ : ℕ) : ℝ) ^ (-q))
    {alphaV alphaPred : ℕ → ℝ}
    (h_alphaV_pos : ∀ n, alphaV n ∈ Set.Ioi (0 : ℝ))
    (h_alphaV :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K R fTrue η)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        alphaV)
    (h_alphaPred_pos : ∀ n, alphaPred n ∈ Set.Ioi (0 : ℝ))
    (h_alphaPred :
      ParameterChoice.IsOptimalParameterFamily
        (fun n ↦ TikhonovPredictiveRisk.objective b c p q σ n.succ)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        alphaPred) :
    ParameterChoice.IsAsymptoticallyOptimal alphaV alphaPred := by
  -- Route correction: reduce both parameter families to the common benchmark
  -- `β_pred`, then use asymptotic-equivalence transport along eventual equality.
  have h_alphaV_beta :
      Asymptotics.IsEquivalent Filter.atTop
        alphaV
        (fun n ↦ TikhonovPredictiveRisk.betaPred b c p q σ n.succ) :=
    gcvOptimalFamily_isAsymptoticallyOptimal_betaPredSucc
      (μ := μ) (K := K) (U := U) (V := V) (s := s) (R := R)
      (fTrue := fTrue) (η := η) (b := b) (c := c) (p := p) (q := q) (σ := σ)
      h_b h_c h_p h_q h_σ h_nonsaturated
      h_white h_svd h_tikhonov h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay h_alphaV_pos h_alphaV
  have h_alphaPred_eq :
      alphaPred =ᶠ[Filter.atTop]
        (fun n ↦ TikhonovPredictiveRisk.betaPred b c p q σ n.succ) := by
    -- The predictive minimizer already agrees pointwise with the predictive benchmark.
    exact Filter.Eventually.of_forall
      (predictiveOptimalFamily_eq_betaPredSucc
        (b := b) (c := c) (p := p) (q := q) (σ := σ)
        h_b h_c h_p h_q h_σ h_nonsaturated
        h_alphaPred_pos h_alphaPred)
  have h_alphaV_alphaPred :
      Asymptotics.IsEquivalent Filter.atTop alphaV alphaPred := by
    -- Replace the benchmark by the predictive minimizer via eventual equality.
    exact h_alphaV_beta.trans_eventuallyEq h_alphaPred_eq.symm
  exact parameterChoiceIsAsymptoticallyOptimalOfIsEquivalentLocal h_alphaV_alphaPred

end

end TikhonovGcv

end

end
