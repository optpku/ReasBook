/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "dim" => Module.finrank ℝ E
local notation "δ" => 1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))

/- Proposition 3.44 lies in the intrinsic finite-dimensional real normed-space
volume-ratio / interior-ball comparison domain.

Sampled owner-style declarations:
- `Set.SatisfiesInteriorBallCondition` in `Definition_3_59`, the chapter owner of the
  radius-`ρ` interior-ball hypothesis;
- `MeasureTheory.Measure.addHaar_real_closedBall` in mathlib, the canonical closed-ball
  Haar-measure scaling formula in finite-dimensional real normed spaces;
- `inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex` in `Theorem_3_51`, the
  chapter owner radius/volume comparison surface for an inner ball inside an outer ball;
- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` in `Theorem_3_2_9`, the intrinsic
  localization-radius specialization of that owner surface to cutting-plane localization sets;
- the closed-ball-infimum best-value decay theorem in `Theorem_3_54`, a downstream user of the
  same closed-ball volume-ratio decay term stated relative to the direct ball infimum
  `sInf (f '' Metric.closedBall xStar R)`.

Best owner abstraction:
- source-facing: the bridge from an abstract geometric volume-decay hypothesis on `E_k` to the
  normalized `dim`-th-root volume-ratio and exponential bounds;
- core/canonical: the ambient Haar/Lebesgue closed-ball scaling owner together with the chapter's
  ball-radius/volume-ratio surface;
- bridge/view: the explicit decay inequality below.

Primitive data:
- the finite-dimensional real normed space `E`, the set `Q`, the interior-ball radius `ρ`, the
  center `x0`, the outer radius `R`, the stage index `k`, and the comparison set `Ek`;
- the source-facing owner hypothesis `Q.SatisfiesInteriorBallCondition ρ`;
- the positive dimension hypothesis `0 < Module.finrank ℝ E`;
- the natural outer-radius sign condition `0 ≤ R`, needed because
  `Metric.closedBall x0 R = ∅` for `R < 0`;
- the direct stagewise decay hypothesis on the Haar/Lebesgue measure `μ Ek`.

Derived API:
- the normalized `dim`-th-root volume ratio
  `Real.rpow (Measure.real μ Ek / Measure.real μ Q) (1 / (dim : ℝ))`;
- the closed-ball comparison factor
  `Real.rpow (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q) (1 / (dim : ℝ))`;
- the exponential upper bound `(R / ρ) * Real.exp (-k / (2 (dim + 1)^2))`.

Source/core/bridge triage:
- source-facing: Proposition 3.44's two quantitative inequalities;
- core/canonical: the standard closed-ball Haar/Lebesgue scaling formula and the chapter's
  radius/volume owner surface;
- bridge/view: passage from the raw volume-decay hypothesis to the displayed ratio and
  exponential bounds.

The earlier measurable-set and ambient-ball-subset hypotheses on `Q` and `E_k` were redundant for
this bridge theorem once the stagewise Haar-measure decay bound itself is taken as primitive
input, so the refined statement keeps only the data that actually changes the displayed
inequalities.
-/

/-- Proposition 3.44 at the intrinsic owner level: if `Q ⊆ E` satisfies the radius-`ρ`
interior-ball condition in a finite-dimensional real normed space `E`, if
`0 < Module.finrank ℝ E`, if `R ≥ 0`, and if a stage set `E_k` has Haar/Lebesgue measure bounded
by `δ^(k * Module.finrank ℝ E / 2) * vol(B₂(x0, R))`, then the normalized
`Module.finrank ℝ E`-th-root volume ratio of `E_k` satisfies the corresponding geometric-decay
estimate and the resulting exponential upper bound
`(R / ρ) * exp (-k / (2 (Module.finrank ℝ E + 1)^2))`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: first convert the assumed finite `ENNReal` measure decay bound for `E_k` into the
-- corresponding real-volume inequality, then take the `dim`-th root to obtain the first
-- inequality. For the second inequality, extract a center `xBar` and a contained radius-`ρ`
-- ball from `Q.SatisfiesInteriorBallCondition ρ`, use monotonicity of volume to bound `vol(Q)`
-- below by the volume of that radius-`ρ` ball, rewrite the closed-ball volumes using the
-- standard finite-dimensional Haar/Lebesgue ball-scaling formula, and then bound
-- `(1 - u)^(k / 2)` by
-- `exp (-u k / 2)` with `u = 1 / (dim + 1)^2`.
theorem volume_ratio_rpow_decay_under_interior_ball_condition
    (hdim : 0 < dim) {μ : Measure E} [μ.IsAddHaarMeasure]
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {x0 : E} {R : ℝ} (hR : 0 ≤ R) (k : ℕ) {Ek : Set E}
    (hvol_decay :
      μ Ek ≤
        ENNReal.ofReal (Real.rpow δ (((k * dim : ℕ) : ℝ) / 2)) *
          μ (Metric.closedBall x0 R)) :
    Real.rpow (μ.real Ek / μ.real Q) (1 / (dim : ℝ)) ≤
        Real.rpow δ ((k : ℝ) / 2) *
          Real.rpow
            (μ.real (Metric.closedBall x0 R) / μ.real Q)
            (1 / (dim : ℝ)) ∧
      Real.rpow δ ((k : ℝ) / 2) *
          Real.rpow
            (μ.real (Metric.closedBall x0 R) / μ.real Q)
            (1 / (dim : ℝ)) ≤
        (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
  rcases hQ with ⟨hρ, xBar, hball⟩
  set z : ℝ := 1 / (dim : ℝ)
  set a : ℝ := (((k * dim : ℕ) : ℝ) / 2)
  set ballR : Set E := Metric.closedBall x0 R
  have hdim_ne : (dim : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdim
  have hz_nonneg : 0 ≤ z := by
    positivity
  have hz_ne : z ≠ 0 := by
    dsimp [z]
    positivity
  have hs_ge_one : (1 : ℝ) ≤ (((dim : ℝ) + 1) ^ (2 : ℕ)) := by
    have hdim_nonneg : 0 ≤ (dim : ℝ) := by
      exact_mod_cast Nat.zero_le dim
    nlinarith
  have hfrac_le_one : 1 / (((dim : ℝ) + 1) ^ (2 : ℕ)) ≤ 1 := by
    simpa using (one_div_le_one_div_of_le zero_lt_one hs_ge_one)
  have hδ_nonneg : 0 ≤ δ := by
    linarith
  have hballR_lt_top : μ ballR < ⊤ := by
    simpa [ballR] using (measure_closedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤)
  have hdecay_finite :
      ENNReal.ofReal (Real.rpow δ a) * μ ballR ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hballR_lt_top.ne
  have hEk_finite : μ Ek ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hvol_decay hdecay_finite.lt_top)
  have hvol_decay_real :
      μ.real Ek ≤ Real.rpow δ a * μ.real ballR := by
    have htoReal := ENNReal.toReal_mono hdecay_finite hvol_decay
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal] at htoReal
    · simpa [Measure.real] using htoReal
    · exact Real.rpow_nonneg hδ_nonneg a
  have hδ_le_exp :
      δ ≤ Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))) := by
    change 1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ)) ≤
      Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))
    simpa using Real.one_sub_le_exp_neg (1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))
  by_cases hQ_zero : μ.real Q = 0
  · constructor
    · have hzeroEk : Real.rpow (μ.real Ek / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      have hzeroBall : Real.rpow (μ.real ballR / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      rw [hzeroEk, hzeroBall, mul_zero]
    · have hzero : Real.rpow (μ.real ballR / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      rw [hzero, mul_zero]
      positivity
  · have hQ_pos : 0 < μ.real Q := by
      exact lt_of_le_of_ne (by positivity) (by simpa [eq_comm] using hQ_zero)
    have hQ_finite : μ Q ≠ ⊤ := by
      have hQ_pos_toReal : 0 < (μ Q).toReal := by
        simpa [Measure.real] using hQ_pos
      rw [ENNReal.toReal_pos_iff] at hQ_pos_toReal
      exact hQ_pos_toReal.2.ne
    have hratio_le :
        μ.real Ek / μ.real Q ≤
          (Real.rpow δ a * μ.real ballR) / μ.real Q := by
      exact (div_le_div_iff_of_pos_right hQ_pos).2 hvol_decay_real
    have ha_mul : a * z = (k : ℝ) / 2 := by
      dsimp [a, z]
      rw [Nat.cast_mul]
      field_simp [hdim_ne]
    have hfirst :
        Real.rpow (μ.real Ek / μ.real Q) z ≤
          Real.rpow δ ((k : ℝ) / 2) * Real.rpow (μ.real ballR / μ.real Q) z := by
      have hmul_rpow :
          Real.rpow (Real.rpow δ a * (μ.real ballR / μ.real Q)) z =
            Real.rpow (Real.rpow δ a) z * Real.rpow (μ.real ballR / μ.real Q) z := by
        simpa using
          (Real.mul_rpow
            (Real.rpow_nonneg hδ_nonneg a)
            (by positivity : 0 ≤ μ.real ballR / μ.real Q))
      have hrpow_mul :
          Real.rpow (Real.rpow δ a) z = Real.rpow δ (a * z) := by
        simpa using (Real.rpow_mul hδ_nonneg a z).symm
      calc
        Real.rpow (μ.real Ek / μ.real Q) z ≤
            Real.rpow ((Real.rpow δ a * μ.real ballR) / μ.real Q) z := by
          exact Real.rpow_le_rpow (by positivity) hratio_le hz_nonneg
        _ = Real.rpow (Real.rpow δ a * (μ.real ballR / μ.real Q)) z := by
          rw [mul_div_assoc]
        _ = Real.rpow (Real.rpow δ a) z * Real.rpow (μ.real ballR / μ.real Q) z := hmul_rpow
        _ = Real.rpow δ (a * z) * Real.rpow (μ.real ballR / μ.real Q) z := by
          rw [hrpow_mul]
        _ = Real.rpow δ ((k : ℝ) / 2) * Real.rpow (μ.real ballR / μ.real Q) z := by
          rw [ha_mul]
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hdim
    have hunit_pos : 0 < μ.real (Metric.ball (0 : E) 1) := by
      have hball_pos : 0 < μ (Metric.ball (0 : E) 1) :=
        Metric.measure_ball_pos μ 0 zero_lt_one
      have hball_lt_top : μ (Metric.ball (0 : E) 1) < ⊤ := by
        simpa using (measure_ball_lt_top : μ (Metric.ball (0 : E) 1) < ⊤)
      simpa using ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
    have hinner_pos : 0 < μ.real (Metric.ball xBar ρ) := by
      have hball_pos : 0 < μ (Metric.ball xBar ρ) :=
        Metric.measure_ball_pos μ xBar hρ
      have hball_lt_top : μ (Metric.ball xBar ρ) < ⊤ := by
        simpa using (measure_ball_lt_top : μ (Metric.ball xBar ρ) < ⊤)
      simpa using ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
    have hQ_lower : μ.real (Metric.ball xBar ρ) ≤ μ.real Q :=
      measureReal_mono hball hQ_finite
    have hratio_ball_le :
        μ.real ballR / μ.real Q ≤
          μ.real ballR / μ.real (Metric.ball xBar ρ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left (inv_anti₀ hinner_pos hQ_lower) (by positivity)
    have hclosed_eq :
        μ.real ballR = R ^ dim * μ.real (Metric.ball (0 : E) 1) := by
      simpa [ballR] using Measure.addHaar_real_closedBall μ x0 hR
    have hinner_eq :
        μ.real (Metric.ball xBar ρ) = ρ ^ dim * μ.real (Metric.ball (0 : E) 1) := by
      rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball μ xBar ρ]
      rw [Measure.addHaar_real_closedBall μ xBar hρ.le]
    have hratio_pow_le :
        μ.real ballR / μ.real Q ≤ (R / ρ) ^ (dim : ℝ) := by
      calc
        μ.real ballR / μ.real Q ≤ μ.real ballR / μ.real (Metric.ball xBar ρ) := hratio_ball_le
        _ = (R / ρ) ^ (dim : ℝ) := by
          rw [hclosed_eq, hinner_eq, Real.rpow_natCast, div_pow]
          field_simp [hunit_pos.ne', pow_ne_zero dim hρ.ne']
    have hz_mul : (dim : ℝ) * z = 1 := by
      dsimp [z]
      field_simp [hdim_ne]
    have hratio_root_le :
        Real.rpow (μ.real ballR / μ.real Q) z ≤ R / ρ := by
      have hrpow_pow :
          Real.rpow ((R / ρ) ^ (dim : ℝ)) z = Real.rpow (R / ρ) ((dim : ℝ) * z) := by
        simpa using
          (Real.rpow_mul (by positivity : 0 ≤ R / ρ) (dim : ℝ) z).symm
      calc
        Real.rpow (μ.real ballR / μ.real Q) z ≤ Real.rpow ((R / ρ) ^ (dim : ℝ)) z := by
          exact Real.rpow_le_rpow (by positivity) hratio_pow_le hz_nonneg
        _ = R / ρ := by
          rw [hrpow_pow, hz_mul]
          exact Real.rpow_one (R / ρ)
    have hgeom_le_exp :
        Real.rpow δ ((k : ℝ) / 2) ≤
          Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
      have hexp_rpow :
          Real.rpow (Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))) ((k : ℝ) / 2) =
            Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) * ((k : ℝ) / 2)) := by
        simpa using
          (Real.exp_mul (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))) ((k : ℝ) / 2)).symm
      calc
        Real.rpow δ ((k : ℝ) / 2) ≤
            Real.rpow (Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))) ((k : ℝ) / 2) := by
          exact Real.rpow_le_rpow hδ_nonneg hδ_le_exp (by positivity)
        _ = Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
          rw [hexp_rpow]
          have hs_ne : (((dim : ℝ) + 1) ^ (2 : ℕ)) ≠ 0 := by
            positivity
          field_simp [hs_ne]
    refine ⟨hfirst, ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul hratio_root_le hgeom_le_exp
        (Real.rpow_nonneg hδ_nonneg _)
        (by positivity : 0 ≤ R / ρ))

end
