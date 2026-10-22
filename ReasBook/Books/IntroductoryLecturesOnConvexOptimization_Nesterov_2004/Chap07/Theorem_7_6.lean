/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open MeasureTheory
open scoped EllipsoidNotation MatrixOrder

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 7.6 lies in Chapter 7's centrally symmetric ellipsoid-rounding / stopping-index domain.

Sampled owner-style declarations:
- `CentralSymmetricRoundingMethod.stoppingCriterion` and
  `CentralSymmetricRoundingMethod.stoppingIndex` in `Algorithm_7_5`, the canonical first-hit
  stopping API for Algorithm 7.5;
- `CentralSymmetricRoundingMethod.threshold_lt_radius_of_lt_stoppingIndex` in `Algorithm_7_5`,
  the owner-level continuation inequality `γ √n < rₖ` before the first stopping index;
- `IsBetaRounding` in `Definition_7_27` and `IsInitialApproximation` in `Definition_7_29`, the
  chapter owners for centered initial ellipsoid data.

Best owner abstraction:
- source-facing: the iteration bound for the actual Algorithm 7.5 run, measured at its canonical
  first stopping index;
- core/canonical: `CentralSymmetricRoundingMethod`, its stopping API, and the centered
  ellipsoid-rounding owner `IsBetaRounding`;
- bridge/view: theorem-level invariance and log-determinant growth hypotheses attached only to
  genuinely continuing steps.

Primitive data:
- the centrally symmetric rounding method itself;
- the canonical termination witness for that method;
- the initial outer radius `R` appearing in the centered rounding datum.

Derived API:
- the stopping index `method.stoppingIndex hTerminate`;
- the continuation inequality `γ √n < rₖ` before stopping;
- the initial centered rounding data packaged by `IsBetaRounding`;
- the lower bound `1 ≤ R`, derived internally from the initial rounding data together with
  `method.one_le_dim`;
- the determinant-growth lower bound used in the complexity estimate.

The previous statement was organized around an arbitrary `N` and separate proof-bridge hypotheses
for `σₖ` and `log det`. This refinement moves the main theorem back to the owner layer of
Algorithm 7.5: the bound is stated for the canonical first stopping index, the lower bound on
`σₖ` is derived from the continuation inequality, the lower bound `1 ≤ R` is recovered internally
from the initial rounding datum, and the initial containment data are packaged by the chapter
rounding owner.
-/

namespace CentralSymmetricRoundingMethod

section StoppingBounds

variable (method : CentralSymmetricRoundingMethod n)
variable (hTerminate : method.Terminates)

local notation "s" => method.stoppingIndex hTerminate

/-- Helper for Theorem 7.6: telescoping a uniform lower bound on the logarithmic determinant
increments gives a linear lower bound on the total growth up to time `T`. -/
lemma logdet_growth_lower_bound_upto
    {T : ℕ} {c : ℝ}
    (hstep :
      ∀ k : ℕ, k < T →
        c ≤ Real.log (Matrix.det (method (k + 1))) -
          Real.log (Matrix.det (method k))) :
    c * (T : ℝ) ≤
      Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0)) := by
  induction T with
  | zero =>
      -- The empty prefix contributes no logarithmic determinant growth.
      norm_num
  | succ T ih =>
      have hstep_last :
          c ≤ Real.log (Matrix.det (method (T + 1))) -
            Real.log (Matrix.det (method T)) :=
        hstep T (Nat.lt_succ_self T)
      have hstep_prefix :
          ∀ k : ℕ, k < T →
            c ≤ Real.log (Matrix.det (method (k + 1))) -
              Real.log (Matrix.det (method k)) := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self T))
      have hprefix := ih hstep_prefix
      -- Add the final increment to the already-telescoped prefix.
      have hcast : c * ((T + 1 : ℕ) : ℝ) = c * (T : ℝ) + c := by
        norm_num [left_distrib, right_distrib]
      rw [hcast]
      have hshape :
          Real.log (Matrix.det (method (T + 1))) - Real.log (Matrix.det (method 0)) =
            (Real.log (Matrix.det (method (T + 1))) -
              Real.log (Matrix.det (method T))) +
            (Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0))) := by
        ring
      rw [hshape]
      linarith

/-- Helper for Theorem 7.6: a factorization `A = Bᴴ B` rewrites the quadratic form of `A`
as the Euclidean norm of `B x`. -/
private theorem sqrt_inner_eq_euclidean_image_norm
    (A B : Matrix (Fin n) (Fin n) ℝ) (hAeq : A = Bᴴ * B) (x : E) :
    Real.sqrt (inner ℝ (A.toEuclideanLin x) x) = ‖B.toEuclideanLin x‖ := by
  -- Rewrite the quadratic form in coordinates and collapse it to a Euclidean square norm.
  have hquad : inner ℝ (A.toEuclideanLin x) x = ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A *ᵥ x.ofLp) := by
        simpa only [Matrix.ofLp_toLpLin] using
          (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x)
      _ = dotProduct x.ofLp ((Bᴴ * B) *ᵥ x.ofLp) := by
        rw [hAeq]
      _ = dotProduct (B *ᵥ x.ofLp) (B *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
        rw [dotProduct_comm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
        simp
      _ = ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
        have hraw :=
          EuclideanSpace.inner_eq_star_dotProduct (B.toEuclideanLin x) (B.toEuclideanLin x)
        simp only [Matrix.ofLp_toLpLin] at hraw
        have hnorm :
            inner ℝ (B.toEuclideanLin x) (B.toEuclideanLin x) =
              ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
          simp
        exact hraw.symm.trans hnorm
  rw [hquad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Helper for Theorem 7.6: the terminal iterate still contains the unit centered ellipsoid at
the canonical stopping index. -/
lemma unit_ellipsoid_subset_at_stoppingIndex
    {R : ℝ}
    (hInitial : IsBetaRounding (method.body : Set E) R (method 0) (0 : E))
    (hinner :
      ∀ k : ℕ, k < s →
        W[1]((method (k + 1))) ⊆ (method.body : Set E)) :
    W[1]((method s)) ⊆ (method.body : Set E) := by
  rcases Nat.eq_zero_or_pos s with hs_zero | hs_pos
  · -- If the stopping index is zero, the initial centered rounding already gives the containment.
    rw [hs_zero]
    simpa using hInitial.unit_matrixEllipsoid_subset
  · -- Otherwise the stopping index is a successor, so the continuing-step hypothesis applies.
    rcases Nat.exists_eq_succ_of_ne_zero hs_pos.ne' with ⟨k, hk⟩
    rw [hk]
    simpa [hk] using hinner k (hk ▸ Nat.lt_succ_self k)

/-- Helper for Theorem 7.6: centered matrix ellipsoids have volume
`√det(G)` times the Euclidean closed-ball volume of the same radius. -/
private theorem centered_matrixEllipsoid_volume
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    volume (W[r](G)) =
      ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : E) r) := by
  obtain ⟨B, hBunit, hBself, hfactor⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hG.isStrictlyPositive
  have hInvFactor : G⁻¹ = B⁻¹ᴴ * B⁻¹ := by
    -- Inverting `G = Bᴴ B` gives the quadratic form needed for the ball preimage description.
    calc
      G⁻¹ = (B * B)⁻¹ := by
        rw [hfactor]
      _ = B⁻¹ * B⁻¹ := by
        rw [Matrix.mul_inv_rev]
      _ = B⁻¹ᴴ * B⁻¹ := by
        congr 1
        rw [Matrix.conjTranspose_nonsing_inv]
        simpa using congrArg Inv.inv hBself.symm
  have hzero :
      W[r](G) = ((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : E) r := by
    -- The centered ellipsoid is exactly the inverse image of the Euclidean closed ball of radius
    -- `r` under `B⁻¹`.
    ext y
    rw [mem_centeredMatrixEllipsoid_iff]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hsqrt := sqrt_inner_eq_euclidean_image_norm G⁻¹ B⁻¹ hInvFactor y
    simpa [hsqrt]
  have hdetLinInv :
      LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) = (B.det)⁻¹ := by
    -- Identify the determinant of the Euclidean linear map with the determinant of its matrix.
    calc
      LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) = (B⁻¹).det := by
        simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
          (LinearMap.det_toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
            ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E)).symm
      _ = (B.det)⁻¹ := by
        simpa using (Matrix.det_nonsing_inv B)
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hdetLinInv_ne :
      LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdetLinInv]
    exact inv_ne_zero hBdet.ne_zero
  have hdet_abs :
      |(LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E))⁻¹| = |B.det| := by
    rw [hdetLinInv]
    simp
  have hBdet_abs : |B.det| = Real.sqrt G.det := by
    rw [hfactor, Matrix.det_mul]
    simpa [pow_two, mul_comm] using (Real.sqrt_sq_eq_abs B.det).symm
  calc
    volume (W[r](G))
        = volume (((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : E) r) := by
            rw [hzero]
    _ =
        ENNReal.ofReal |(LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E))⁻¹| *
          volume (Metric.closedBall (0 : E) r) := by
            rw [MeasureTheory.Measure.addHaar_preimage_linearMap volume hdetLinInv_ne]
    _ = ENNReal.ofReal |B.det| * volume (Metric.closedBall (0 : E) r) := by
          rw [hdet_abs]
    _ = ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : E) r) := by
          rw [hBdet_abs]

/-- Helper for Theorem 7.6: the centered ellipsoid volume identity in real-valued form. -/
lemma centered_matrixEllipsoid_volume_toReal
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    (volume (W[r](G))).toReal =
      Real.sqrt G.det * (volume (Metric.closedBall (0 : E) r)).toReal := by
  rw [centered_matrixEllipsoid_volume G hG hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  simp [measure_closedBall_lt_top.ne]

/-- Helper for Theorem 7.6: Euclidean closed-ball volumes scale by `r ^ n` in `R^n`. -/
private lemma closedBall_volume_toReal_eq_pow
    (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : E) r)).toReal =
      r ^ n * (volume (Metric.closedBall (0 : E) 1)).toReal := by
  -- Compare the explicit mathlib formulas for the radius-`r` and radius-`1` closed balls.
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hn)
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall]
  simp [hr, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 7.6: the initial centered rounding and the terminal inner containment bound
the total logarithmic determinant growth by `2 n log R`. -/
lemma terminal_logdet_upper_bound_of_rounding_containment
    {R : ℝ} {T : ℕ}
    (hInitial : IsBetaRounding (method.body : Set E) R (method 0) (0 : E))
    (hFinal : W[1]((method T)) ⊆ (method.body : Set E)) :
    Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0)) ≤
      2 * (n : ℝ) * Real.log R := by
  have hcontain : W[1]((method T)) ⊆ W[R]((method 0)) :=
    Set.Subset.trans hFinal hInitial.subset_beta_ellipsoid
  have hzero_mem : (0 : E) ∈ W[1]((method 0)) := by
    simpa [mem_centeredMatrixEllipsoid_iff]
  have hzero_body : (0 : E) ∈ (method.body : Set E) :=
    hInitial.unit_matrixEllipsoid_subset hzero_mem
  have hzero_outer : (0 : E) ∈ W[R]((method 0)) :=
    hInitial.subset_beta_ellipsoid hzero_body
  have hR_nonneg : 0 ≤ R := by
    simpa [mem_centeredMatrixEllipsoid_iff] using hzero_outer
  have hvol_right_lt_top : volume (W[R]((method 0))) < ⊤ := by
    rw [centered_matrixEllipsoid_volume (method 0) (method.matrix_posDef 0) hR_nonneg]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have hvol_mono : volume (W[1]((method T))) ≤ volume (W[R]((method 0))) :=
    measure_mono hcontain
  have hvol_mono_toReal :
      (volume (W[1]((method T)))).toReal ≤
        (volume (W[R]((method 0)))).toReal :=
    ENNReal.toReal_mono hvol_right_lt_top.ne hvol_mono
  rw [centered_matrixEllipsoid_volume_toReal (method T) (method.matrix_posDef T)
      (show (0 : ℝ) ≤ 1 by positivity),
    centered_matrixEllipsoid_volume_toReal (method 0) (method.matrix_posDef 0) hR_nonneg] at hvol_mono_toReal
  rw [closedBall_volume_toReal_eq_pow method.one_le_dim hR_nonneg] at hvol_mono_toReal
  have hball_one_pos : 0 < (volume (Metric.closedBall (0 : E) 1)).toReal := by
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  have hsqrt_le :
      Real.sqrt (Matrix.det (method T)) ≤
        R ^ n * Real.sqrt (Matrix.det (method 0)) := by
    have hcancel :
        Real.sqrt (Matrix.det (method T)) *
            (volume (Metric.closedBall (0 : E) 1)).toReal ≤
          (R ^ n * Real.sqrt (Matrix.det (method 0))) *
            (volume (Metric.closedBall (0 : E) 1)).toReal := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hvol_mono_toReal
    exact le_of_mul_le_mul_right hcancel hball_one_pos
  have hdetT_pos : 0 < Matrix.det (method T) := (method.matrix_posDef T).det_pos
  have hdet0_pos : 0 < Matrix.det (method 0) := (method.matrix_posDef 0).det_pos
  have hsqrtT_pos : 0 < Real.sqrt (Matrix.det (method T)) := by
    exact Real.sqrt_pos.mpr hdetT_pos
  have hsqrt0_pos : 0 < Real.sqrt (Matrix.det (method 0)) := by
    exact Real.sqrt_pos.mpr hdet0_pos
  have hR_pos : 0 < R := by
    have hrhs_pos : 0 < R ^ n * Real.sqrt (Matrix.det (method 0)) :=
      lt_of_lt_of_le hsqrtT_pos hsqrt_le
    by_cases hR0 : R = 0
    · have hn_pos : 0 < n := by
        exact_mod_cast method.one_le_dim
      simp [hR0, hn_pos.ne'] at hrhs_pos
    · exact lt_of_le_of_ne hR_nonneg (Ne.symm hR0)
  have hlog_sqrt_le :
      Real.log (Real.sqrt (Matrix.det (method T))) ≤
        Real.log (R ^ n * Real.sqrt (Matrix.det (method 0))) := by
    exact Real.log_le_log hsqrtT_pos hsqrt_le
  have hlog_expand :
      Real.log (R ^ n * Real.sqrt (Matrix.det (method 0))) =
        (n : ℝ) * Real.log R + Real.log (Real.sqrt (Matrix.det (method 0))) := by
    rw [Real.log_mul (show R ^ n ≠ 0 by positivity) hsqrt0_pos.ne', Real.log_pow]
  have hhalf :
      Real.log (Matrix.det (method T)) / 2 ≤
        (n : ℝ) * Real.log R + Real.log (Matrix.det (method 0)) / 2 := by
    rw [hlog_expand, Real.log_sqrt hdetT_pos.le, Real.log_sqrt hdet0_pos.le] at hlog_sqrt_le
    simpa using hlog_sqrt_le
  linarith

/-- Helper for Theorem 7.6: the simpler coefficient `(γ - 1)^2 / γ^2` is bounded by the exact
per-step logarithmic determinant gain. -/
lemma gamma_step_gain_lower_bound
    {γ : ℝ} (hγ : 1 < γ) :
    (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ) ≤
      2 * Real.log γ - (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hlog : 1 - 1 / γ ≤ Real.log γ :=
    by simpa [one_div] using (Real.one_sub_inv_le_log_of_pos hγ_pos)
  have hγ_ne : γ ≠ 0 := hγ_pos.ne'
  have hleft :
      (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ) = 1 - 2 / γ + 1 / γ ^ (2 : ℕ) := by
    field_simp [hγ_ne]
    ring
  have hright :
      2 * Real.log γ - (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) =
        2 * Real.log γ - 1 + 1 / γ ^ (2 : ℕ) := by
    field_simp [hγ_ne]
    ring
  have hlog_two : 2 - 2 / γ ≤ 2 * Real.log γ := by
    have hscaled : 2 * (1 - 1 / γ) ≤ 2 * Real.log γ :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have hrewrite : 2 * (1 - 1 / γ) = 2 - 2 / γ := by ring
    rw [hrewrite] at hscaled
    exact hscaled
  rw [hleft, hright]
  nlinarith

-- Route correction: the earlier blocker for this item was the upstream
-- `Algorithm_7_5 -> Proposition_7_8` import chain. With that prerequisite repaired enough to
-- elaborate, the stopping-index proof below now closes by the intended telescoping-plus-volume
-- comparison route.
-- Proof sketch: derive `1 ≤ R` from the initial centered rounding data and `method.one_le_dim`.
-- Sum the lower bound for `log det Gₖ₊₁ - log det Gₖ` over the genuinely continuing steps
-- `k < s`; for each such `k`, the continuation inequality `γ √n < rₖ` is supplied canonically by
-- `threshold_lt_radius_of_lt_stoppingIndex`. Compare the resulting lower bound for
-- `log det G_s - log det G₀` with the upper bound coming from the initial centered rounding
-- `W₁(G₀) ⊆ C ⊆ W_R(G₀)` and the persistent inner containments `W₁(Gₖ) ⊆ C`.
/-- Theorem 7.6: if an Algorithm 7.5 run starts from the centered `R`-rounding
`W₁(G₀) ⊆ C ⊆ W_R(G₀)`, if every post-update iterate before the first stopping index still
satisfies `W₁(Gₖ) ⊆ C`, and if every genuinely continuing step `k < s` gains at least
`2 log γ - (γ² - 1) / γ²` in `log det Gₖ`, then the canonical first stopping index `s` is
bounded by `2 n γ² / (γ - 1)² * log R`. -/
theorem stoppingIndex_le
    {R : ℝ}
    (hInitial : IsBetaRounding (method.body : Set E) R (method 0) (0 : E))
    (hinner :
      ∀ k : ℕ, k < s →
        W[1]((method (k + 1))) ⊆ (method.body : Set E))
    (hlogDet :
      ∀ k : ℕ, k < s →
        Real.log (Matrix.det (method (k + 1))) ≥
          Real.log (Matrix.det (method k)) +
            (2 * Real.log method.gamma -
              (method.gamma ^ (2 : ℕ) - 1) / method.gamma ^ (2 : ℕ))) :
    (s : ℝ) ≤
      2 * (n : ℝ) * method.gamma ^ (2 : ℕ) / (method.gamma - 1) ^ (2 : ℕ) * Real.log R := by
  let c : ℝ := (method.gamma - 1) ^ (2 : ℕ) / method.gamma ^ (2 : ℕ)
  have huniform :
      ∀ k : ℕ, k < s →
        c ≤ Real.log (Matrix.det (method (k + 1))) -
          Real.log (Matrix.det (method k)) := by
    intro k hk
    -- Replace the exact step gain by the simpler uniform coefficient used in the final bound.
    have hgain : c ≤
        2 * Real.log method.gamma -
          (method.gamma ^ (2 : ℕ) - 1) / method.gamma ^ (2 : ℕ) := by
      dsimp [c]
      exact gamma_step_gain_lower_bound method.one_lt_gamma
    have hstep := hlogDet k hk
    linarith
  have hlower := logdet_growth_lower_bound_upto method huniform
  have hfinal :=
    unit_ellipsoid_subset_at_stoppingIndex method hTerminate hInitial hinner
  have hupper :=
    terminal_logdet_upper_bound_of_rounding_containment method hInitial hfinal
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (pow_pos (sub_pos.mpr method.one_lt_gamma) _) (pow_pos (lt_trans zero_lt_one method.one_lt_gamma) _)
  have hbudget : c * (s : ℝ) ≤ 2 * (n : ℝ) * Real.log R := by
    linarith
  have hdiv :
      (s : ℝ) ≤ (2 * (n : ℝ) * Real.log R) / c := by
    exact (le_div_iff₀ hc_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget)
  have hcoeff :
      (2 * (n : ℝ) * Real.log R) / c =
        2 * (n : ℝ) * method.gamma ^ (2 : ℕ) /
          (method.gamma - 1) ^ (2 : ℕ) * Real.log R := by
    dsimp [c]
    have hgamma_ne : method.gamma ≠ 0 := by
      linarith [method.one_lt_gamma]
    have hgamma_sub_ne : method.gamma - 1 ≠ 0 := by
      linarith [method.one_lt_gamma]
    field_simp [hgamma_ne, hgamma_sub_ne]
  rw [hcoeff] at hdiv
  exact hdiv

end StoppingBounds

end CentralSymmetricRoundingMethod

end
