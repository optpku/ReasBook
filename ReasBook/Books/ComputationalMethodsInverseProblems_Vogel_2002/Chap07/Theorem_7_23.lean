/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.AsymptoticOptimalBridge
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_23.PredictiveRisk
import Mathlib.Analysis.MeanInequalities

namespace TikhonovPredictiveRisk

/-- Helper for Theorem 7.23: the kernel moment `I_{p,3}^s` is positive under
the Chapter 7 integrability-side inequalities. -/
lemma kernelMomentIntegralPos_j3
    {p s : ℝ}
    (h_p : 0 < p) (h_s : 0 < s + 1) (h_decay : 0 < 3 * p - s - 1) :
    0 < KernelMoment.integral p 3 s := by
  -- Rewrite the moment using the earlier gamma-ratio formula and check that
  -- every factor in that closed form is positive.
  rw [KernelMoment.integral_eq_gamma_mul_gamma_div_factorial
    (p := p) (s := s) (j := 3) h_s h_decay]
  refine div_pos ?_ ?_
  · refine mul_pos ?_ ?_
    · exact Real.Gamma_pos_of_pos (div_pos h_decay h_p)
    · exact Real.Gamma_pos_of_pos (div_pos h_s h_p)
  · positivity

/-- Helper for Theorem 7.23: the weighted-AM-GM bracket controlling the
normalized predictive objective is bounded below by `q`. -/
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

/-- Helper for Theorem 7.23: equality in the normalized predictive objective
bracket occurs exactly at `t = 1`. -/
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
    -- Convert the Chapter 7 equality to the weighted-AM-GM equality case.
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
    have ht_eq_one :
        t = (1 : ℝ) := by
      exact
        (Real.rpow_left_inj h_t.le (show 0 ≤ (1 : ℝ) by positivity) hqp_ne).mp
          (by simpa using hpow_qp)
    exact ht_eq_one
  · intro h_t_eq
    -- Substituting `t = 1` collapses both powers in the bracket.
    simp [h_t_eq]

/-- Helper for Theorem 7.23: the predictive-risk coefficient `C₁` is positive
in the nonsaturated regime. -/
lemma predictiveRiskC1_pos
    (b c p q : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : p - q > -1) :
    0 < predictiveRiskC1 b c p q := by
  -- Route correction: `Prop_7_20` is available in the current workspace, so
  -- use its earlier gamma-ratio positivity bridge directly.
  have hpp : 0 < p := by
    linarith
  have h_s : 0 < (p - q) + 1 := by
    linarith
  have h_decay : 0 < 3 * p - (p - q) - 1 := by
    linarith
  rw [predictiveRiskC1_def]
  refine mul_pos (mul_pos h_b ?_) ?_
  · exact Real.rpow_pos_of_pos h_c _
  · exact kernelMomentIntegralPos_j3 hpp h_s h_decay

/-- Helper for Theorem 7.23: the predictive-risk coefficient `C₂` is positive.
-/
lemma predictiveRiskC2_pos
    (c p : ℝ)
    (h_c : 0 < c) (h_p : 1 < p) :
    0 < predictiveRiskC2 c p := by
  -- The variance coefficient uses the same positive `j = 3` kernel moment with
  -- the special exponent `s = p`.
  have hpp : 0 < p := by
    linarith
  have h_s : 0 < p + 1 := by
    linarith
  have h_decay : 0 < 3 * p - p - 1 := by
    linarith
  rw [predictiveRiskC2_def]
  refine mul_pos ?_ ?_
  · exact Real.rpow_pos_of_pos h_c _
  · exact kernelMomentIntegralPos_j3 hpp h_s h_decay

/-- Helper for Theorem 7.23: the benchmark `β_pred` is positive for every
positive data size. -/
lemma betaPred_pos
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) :
    0 < betaPred b c p q σ n := by
  -- Expand the closed form of `β_pred` and prove each positive factor
  -- separately.
  rw [betaPred_def, betaPredConstant_def]
  have hq1 : 0 < q - 1 := by
    linarith
  have hRatioPos :
      0 <
        predictiveRiskC2 c p / ((q - 1) * predictiveRiskC1 b c p q) := by
    exact div_pos
      (predictiveRiskC2_pos c p h_c h_p)
      (mul_pos hq1 (predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated))
  have hSigmaDivPos : 0 < (σ ^ 2) / (n : ℝ) := by
    have hSigmaSq : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hSigmaSq (by exact_mod_cast n.2)
  exact mul_pos (Real.rpow_pos_of_pos hRatioPos _) (Real.rpow_pos_of_pos hSigmaDivPos _)

/-- Helper for Theorem 7.23: the explicit benchmark `β_pred` satisfies the
displayed predictive root equation. -/
lemma betaPred_satisfiesRootEquation
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) :
    BetaPredRootEquation b c p q σ n (betaPred b c p q σ n) := by
  have hp_pos : 0 < p := by
    linarith
  have hq_pos : 0 < q := by
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq1 : 0 < q - 1 := by
    linarith
  set ratio : ℝ :=
    predictiveRiskC2 c p / ((q - 1) * predictiveRiskC1 b c p q)
  set scale : ℝ := (σ ^ 2) / (n : ℝ)
  have hC1_pos :
      0 < predictiveRiskC1 b c p q :=
    predictiveRiskC1_pos b c p q h_b h_c h_p h_q h_nonsaturated
  have hC2_pos :
      0 < predictiveRiskC2 c p :=
    predictiveRiskC2_pos c p h_c h_p
  have hden_pos :
      0 < (q - 1) * predictiveRiskC1 b c p q := by
    exact mul_pos hq1 hC1_pos
  have hratio_pos : 0 < ratio := by
    exact div_pos hC2_pos hden_pos
  have hscale_pos : 0 < scale := by
    have hσ_sq : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hσ_sq (by exact_mod_cast n.2)
  have hexp : (p / q) * (q / p) = (1 : ℝ) := by
    field_simp [hp_ne, hq_ne]
  have hratio_cancel :
      (q - 1) * predictiveRiskC1 b c p q * ratio = predictiveRiskC2 c p := by
    dsimp [ratio]
    field_simp [hden_pos.ne']
  -- Normalize the positive closed form of `β_pred` and cancel the ratio
  -- hidden inside `betaPredConstant`.
  rw [betaPredRootEquation_iff, betaPred_def, betaPredConstant_def]
  calc
    (q - 1) * predictiveRiskC1 b c p q *
        ((ratio ^ (p / q) * scale ^ (p / q)) ^ (q / p))
        =
          (q - 1) * predictiveRiskC1 b c p q *
            ((ratio ^ (p / q)) ^ (q / p) * (scale ^ (p / q)) ^ (q / p)) := by
              congr 1
              exact
                Real.mul_rpow
                  (show 0 ≤ ratio ^ (p / q) by positivity)
                  (show 0 ≤ scale ^ (p / q) by positivity)
    _ =
          (q - 1) * predictiveRiskC1 b c p q *
            (ratio ^ ((p / q) * (q / p)) * scale ^ ((p / q) * (q / p))) := by
              congr 1
              rw [← Real.rpow_mul hratio_pos.le (p / q) (q / p)]
              rw [← Real.rpow_mul hscale_pos.le (p / q) (q / p)]
    _ = (q - 1) * predictiveRiskC1 b c p q * (ratio * scale) := by
          simp [hexp]
    _ = ((q - 1) * predictiveRiskC1 b c p q * ratio) * scale := by ring
    _ = predictiveRiskC2 c p * scale := by rw [hratio_cancel]
    _ = predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) := by rfl

/-- Helper for Theorem 7.23: every positive solution of the predictive root
equation minimizes the predictive-risk objective on `Set.Ioi (0 : ℝ)`. -/
lemma objective_le_of_rootEquation
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : p - q > -1)
    (n : ℕ+) {β α : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hroot : BetaPredRootEquation b c p q σ n β) :
    objective b c p q σ n β <= objective b c p q σ n α := by
  have hp_pos : 0 < p := by
    linarith
  have hq_pos : 0 < q := by
    linarith
  have hpref_pos :
      0 < predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
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
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p)) =
        (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    rw [betaPredRootEquation_iff] at hroot
    calc
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          = ((q - 1) * predictiveRiskC1 b c p q * β ^ (q / p)) * β ^ (-(1 / p)) := by
              rw [← hroot]
      _ = (q - 1) * predictiveRiskC1 b c p q * (β ^ (q / p) * β ^ (-(1 / p))) := by
            ring
      _ = (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
            rw [← Real.rpow_add hβ]
            congr 2
            ring
  have hobj_beta :
      objective b c p q σ n β =
        q * (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Rewrite the benchmark objective using the root equation.
    rw [objective_def]
    calc
      predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
          predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
              (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
                rw [hroot_scaled]
      _ = q * (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
            ring
  have hobj_alpha :
      objective b c p q σ n α =
        (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
          (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Normalize `α` as `β * t` and factor out the same positive scalar.
    rw [objective_def, hα_eq]
    calc
      predictiveRiskC1 b c p q * (β * t) ^ ((q - 1) / p) +
          predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * (β * t) ^ (-(1 / p))
          =
            predictiveRiskC1 b c p q *
                (β ^ ((q - 1) / p) * t ^ ((q - 1) / p)) +
              predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                (β ^ (-(1 / p)) * t ^ (-(1 / p))) := by
                rw [Real.mul_rpow hβ.le ht_pos.le]
                rw [Real.mul_rpow hβ.le ht_pos.le]
      _ =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) * t ^ ((q - 1) / p) +
              (predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))) *
                t ^ (-(1 / p)) := by
                  ring
      _ =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) * t ^ ((q - 1) / p) +
              ((q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) *
                t ^ (-(1 / p)) := by
                  rw [hroot_scaled]
      _ =
            (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
              (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
                ring
  -- The remaining scalar inequality is exactly the weighted-AM-GM lower bound.
  rw [hobj_beta, hobj_alpha]
  exact mul_le_mul_of_nonneg_right
    (predictiveObjectiveBracket_ge hp_pos h_q ht_pos)
    (le_of_lt hpref_pos)

/-- Helper for Theorem 7.23: equality in the predictive-risk objective occurs
at a positive root of the benchmark equation only at that root. -/
lemma objective_eq_of_rootEquation_iff
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_nonsaturated : p - q > -1)
    (n : ℕ+) {β α : ℝ}
    (hβ : 0 < β) (hα : 0 < α)
    (hroot : BetaPredRootEquation b c p q σ n β) :
    objective b c p q σ n α = objective b c p q σ n β ↔ α = β := by
  have hp_pos : 0 < p := by
    linarith
  have hpref_pos :
      0 < predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
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
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p)) =
        (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
    rw [betaPredRootEquation_iff] at hroot
    calc
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          = ((q - 1) * predictiveRiskC1 b c p q * β ^ (q / p)) * β ^ (-(1 / p)) := by
              rw [← hroot]
      _ = (q - 1) * predictiveRiskC1 b c p q * (β ^ (q / p) * β ^ (-(1 / p))) := by
            ring
      _ = (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
            rw [← Real.rpow_add hβ]
            congr 2
            ring
  have hobj_beta :
      objective b c p q σ n β =
        q * (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Reuse the root equation to simplify the benchmark value of the objective.
    rw [objective_def]
    calc
      predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
          predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))
          =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) +
              (q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p) := by
                rw [hroot_scaled]
      _ = q * (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
            ring
  have hobj_alpha :
      objective b c p q σ n α =
        (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
          (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
    -- Normalize `α = β * t` exactly as in the minimizer inequality proof.
    rw [objective_def, hα_eq]
    calc
      predictiveRiskC1 b c p q * (β * t) ^ ((q - 1) / p) +
          predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * (β * t) ^ (-(1 / p))
          =
            predictiveRiskC1 b c p q *
                (β ^ ((q - 1) / p) * t ^ ((q - 1) / p)) +
              predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) *
                (β ^ (-(1 / p)) * t ^ (-(1 / p))) := by
                rw [Real.mul_rpow hβ.le ht_pos.le]
                rw [Real.mul_rpow hβ.le ht_pos.le]
      _ =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) * t ^ ((q - 1) / p) +
              (predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * β ^ (-(1 / p))) *
                t ^ (-(1 / p)) := by
                  ring
      _ =
            predictiveRiskC1 b c p q * β ^ ((q - 1) / p) * t ^ ((q - 1) / p) +
              ((q - 1) * predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) *
                t ^ (-(1 / p)) := by
                  rw [hroot_scaled]
      _ =
            (t ^ ((q - 1) / p) + (q - 1) * t ^ (-(1 / p))) *
              (predictiveRiskC1 b c p q * β ^ ((q - 1) / p)) := by
                ring
  constructor
  · intro h_eq
    -- Cancel the shared positive factor and invoke the equality case of the
    -- weighted-AM-GM bracket.
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

/-- Theorem 7.23 (1) (Minimizer of Predictive Risk for Tikhonov
Regularization).
For the concrete `α`-indexed predictive-risk objective from `(7.86)`, the
benchmark family `β_pred` is itself a prediction-optimal parameter family on
the admissible set `Set.Ioi (0 : ℝ)` for every positive data size `n : ℕ+`
under the predictive-side nonsaturated regime hypotheses on `b`, `c`, `p`,
`q`, and `σ`. -/
theorem betaPred_isOptimalFamily
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1) :
    ∀ n : ℕ+, betaPred b c p q σ n ∈ Set.Ioi (0 : ℝ) ∧
      IsMinOn (objective b c p q σ n) (Set.Ioi (0 : ℝ)) (betaPred b c p q σ n) := by
  intro n
  refine ⟨betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated n, ?_⟩
  -- The benchmark is admissible and the generic root-equation minimizer lemma
  -- handles every positive comparison point.
  intro α hα
  exact
    objective_le_of_rootEquation
      b c p q σ h_b h_c h_p h_q h_nonsaturated n
      (betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated n)
      hα
      (betaPred_satisfiesRootEquation b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated n)

/-- The companion admissibility statement for the positive-index benchmark
family `β_pred`. -/
theorem betaPred_mem_admissible
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) :
    betaPred b c p q σ n ∈ Set.Ioi (0 : ℝ) :=
  (betaPred_isOptimalFamily b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated n).1

/-- The companion pointwise minimality statement for the positive-index
benchmark family `β_pred`. -/
theorem betaPred_isMinOn
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    (n : ℕ+) :
    IsMinOn (objective b c p q σ n) (Set.Ioi (0 : ℝ)) (betaPred b c p q σ n) :=
  (betaPred_isOptimalFamily b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated n).2

/-- Reindexing a positive-index predictive-risk minimizing family by `Nat.succ`
matches the Chapter 7 backend `ParameterChoice.IsOptimalParameterFamily` owner
together with the explicit positivity side condition from Theorem 7.23. -/
theorem isOptimalParameterFamily_succ_iff
    (b c p q σ : ℝ) {alphaP : ℕ → ℝ} :
    ((∀ n : ℕ, alphaP n.succ ∈ Set.Ioi (0 : ℝ)) ∧
      ParameterChoice.IsOptimalParameterFamily
        (fun n ↦ objective b c p q σ n.succ)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        (fun n ↦ alphaP n.succ)) ↔
    ∀ n : ℕ+, alphaP n ∈ Set.Ioi (0 : ℝ) ∧
      IsMinOn (objective b c p q σ n) (Set.Ioi (0 : ℝ)) (alphaP n) := by
  constructor
  · rintro ⟨h_mem, h_optimal⟩ n
    refine ⟨?_, ?_⟩
    · simpa [Nat.succ_eq_add_one, PNat.natPred_add_one] using h_mem n.natPred
    have h' :=
      (ParameterChoice.isOptimalParameterFamily_iff
        (fun m ↦ objective b c p q σ m.succ)
        (fun _ ↦ Set.Ioi (0 : ℝ))
        (fun m ↦ alphaP m.succ)).1 h_optimal n.natPred
    simpa [Nat.succ_eq_add_one, PNat.natPred_add_one] using h'
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      simpa [Nat.succPNat_coe] using (h n.succPNat).1
    · refine
        (ParameterChoice.isOptimalParameterFamily_iff
          (fun m ↦ objective b c p q σ m.succ)
          (fun _ ↦ Set.Ioi (0 : ℝ))
          (fun m ↦ alphaP m.succ)).2 ?_
      intro n
      simpa [Nat.succPNat_coe] using (h n.succPNat).2

/-- The `Nat.succ`-reindexed benchmark family `β_pred` stays in the admissible
positive parameter set. -/
theorem betaPred_mem_admissible_succ
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1) :
    ∀ n : ℕ, betaPred b c p q σ n.succ ∈ Set.Ioi (0 : ℝ) :=
  ((isOptimalParameterFamily_succ_iff b c p q σ).2
    (betaPred_isOptimalFamily b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated)).1

/-- Reindexing positive data sizes by `Nat.succ` packages Theorem 7.23 into the
backend `ParameterChoice.IsOptimalParameterFamily` owner. -/
theorem betaPred_isOptimalFamily_succ
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1) :
    ParameterChoice.IsOptimalParameterFamily
      (fun n ↦ objective b c p q σ n.succ)
      (fun _ ↦ Set.Ioi (0 : ℝ))
      (fun n ↦ betaPred b c p q σ n.succ) :=
  ((isOptimalParameterFamily_succ_iff b c p q σ).2
    (betaPred_isOptimalFamily b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated)).2

/-- Helper for Theorem 7.23: package an asymptotic equivalence as the owner
wrapper `ParameterChoice.IsAsymptoticallyOptimal`. -/
lemma isAsymptoticallyOptimalOfIsEquivalentLocal
    {α αopt : ℕ → ℝ}
    (h : Asymptotics.IsEquivalent Filter.atTop α αopt) :
    ParameterChoice.IsAsymptoticallyOptimal α αopt := by
  -- Route correction: reuse the earlier Chapter 7 bridge instead of reopening
  -- the owner wrapper inside this theorem-local file.
  exact parameterChoiceIsAsymptoticallyOptimalOfIsEquivalent h

/-- Theorem 7.23 (2). Any parameter family minimizing the concrete
predictive-risk objective `(7.86)` in the predictive-side nonsaturated regime
is asymptotically optimal relative to the root-equation benchmark `β_pred`.
The source-facing minimizer-family hypothesis retains both admissibility on
`Set.Ioi (0 : ℝ)` and pointwise minimality for each positive data size `n : ℕ+`;
the backend `ParameterChoice.IsOptimalParameterFamily` owner is recovered from
`isOptimalParameterFamily_succ_iff`. -/
theorem isAsymptoticallyOptimal_of_optimalFamily
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (h_σ : 0 < σ) (h_nonsaturated : p - q > -1)
    {alphaP : ℕ → ℝ}
    (h_alphaP :
      ∀ n : ℕ+, alphaP n ∈ Set.Ioi (0 : ℝ) ∧
        IsMinOn (objective b c p q σ n) (Set.Ioi (0 : ℝ)) (alphaP n)) :
    ParameterChoice.IsAsymptoticallyOptimal alphaP (betaPred b c p q σ) := by
  have h_eventually_eq :
      alphaP =ᶠ[Filter.atTop] betaPred b c p q σ := by
    -- Compare the two positive minimizers at each sufficiently large natural
    -- number, then use the root-equation uniqueness lemma.
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hn_pos : 0 < n := by
      exact lt_of_lt_of_le Nat.zero_lt_one hn
    let npos : ℕ+ := ⟨n, hn_pos⟩
    have h_alpha_mem : alphaP npos ∈ Set.Ioi (0 : ℝ) := (h_alphaP npos).1
    have h_beta_mem :
        betaPred b c p q σ npos ∈ Set.Ioi (0 : ℝ) :=
      betaPred_mem_admissible b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos
    have h_eq_obj :
        objective b c p q σ npos (alphaP npos) =
          objective b c p q σ npos (betaPred b c p q σ npos) := by
      have hAlphaMin := (h_alphaP npos).2
      rw [isMinOn_iff] at hAlphaMin
      have hBetaMin :=
        betaPred_isMinOn b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos
      rw [isMinOn_iff] at hBetaMin
      apply le_antisymm
      · exact hAlphaMin (betaPred b c p q σ npos) h_beta_mem
      · exact hBetaMin (alphaP npos) h_alpha_mem
    have h_eq_point :
        alphaP npos = betaPred b c p q σ npos := by
      exact
        (objective_eq_of_rootEquation_iff
          b c p q σ h_b h_c h_p h_q h_nonsaturated npos
          (betaPred_pos b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos)
          h_alpha_mem
          (betaPred_satisfiesRootEquation
            b c p q σ h_b h_c h_p h_q h_σ h_nonsaturated npos)).mp
          h_eq_obj
    simpa [npos] using h_eq_point
  -- Eventual equality is stronger than the asymptotic equivalence required by
  -- `ParameterChoice.IsAsymptoticallyOptimal`.
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop alphaP (betaPred b c p q σ) := by
    exact
      Asymptotics.IsEquivalent.trans_eventuallyEq
        (Asymptotics.IsEquivalent.refl : Asymptotics.IsEquivalent Filter.atTop alphaP alphaP)
        h_eventually_eq
  -- Route correction: the final step is only wrapper normalization, not a new
  -- predictive-risk argument.
  exact isAsymptoticallyOptimalOfIsEquivalentLocal h_equiv

end TikhonovPredictiveRisk
