/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open MeasureTheory
open scoped EllipsoidNotation MatrixOrder

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.7 lies in Chapter 7's translated ellipsoid-rounding / determinant-growth domain.

Sampled owner-style declarations:
- `GeneralConvexRoundingAlgorithm.radius` and
  `GeneralConvexRoundingAlgorithm.oneSidedRoundingSigma` in `Algorithm_7_7`, the owner-level run
  API for Algorithm 7.7;
- `matrixEllipsoid` and the notation `W[r](v, G)` in `Definition_7_26`, the source-facing owner of
  translated ellipsoids;
- `_root_.oneSidedRoundingSigma` in `Lemma_7_5`, the chapter owner of the per-step scalar
  quantity `σ = (r - n) / (n + 1)`;
- `IsBetaRounding` in `Definition_7_27`, the chapter owner for the initial translated inner/outer
  ellipsoid containment data;
- `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6`, the nearby owner-style
  iteration bound organized as initial rounding data plus continuing-step hypotheses.

Best owner abstraction:
- source-facing: the iteration bound for a run of Algorithm 7.7 up to a terminal iterate `T`;
- core/canonical: `GeneralConvexRoundingAlgorithm` for the run data and `IsBetaRounding` for the
  initial translated ellipsoid containment;
- bridge/view: the terminal unit-ellipsoid containment and the theorem-level logarithmic
  determinant-growth inequalities.

Primitive data:
- the algorithm run;
- the initial outer radius `R`;
- the total number of performed updates `T`.

Derived API:
- the center sequence `vₖ = algorithm k` and the shape sequence `Gₖ = algorithm.shape k`;
- the initial translated rounding datum, packaged canonically by `IsBetaRounding`;
- the canonical per-step scalar `σₖ = algorithm.oneSidedRoundingSigma k`, derived from the current
  shape and maximizer displacement through the Chapter 7 owner `_root_.oneSidedRoundingSigma`;
- the initial and terminal positive-definiteness, derived from `algorithm.initial_shape_posDef`
  and `algorithm.shape_posDef` rather than stored as extra theorem inputs;
- the per-step logarithmic determinant increment estimate.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: `GeneralConvexRoundingAlgorithm`, `IsBetaRounding`;
- bridge/view: the terminal comparison data and the stepwise logarithmic determinant inequalities.

Semantic search note:
- `lean_leansearch` on the sigma/log-determinant iteration-bound phrasing returned no relevant
  Chapter 7 owner candidates, so the owner names used below were verified directly in the local
  `Algorithm_7_7` and `Lemma_7_5` APIs.

The previous statement still left the source-defined per-step scalar `σₖ` as a primitive theorem
parameter. This refinement moves the theorem back to the owner layer of
`GeneralConvexRoundingAlgorithm`, reuses `IsBetaRounding` for the initial containment data, and
states both the continuation lower bound and the determinant-growth estimate directly in terms of
the canonical owner-side step quantity `algorithm.oneSidedRoundingSigma k`.
-/

-- Proof sketch: sum the lower bound
-- `2 σₖ² / ((1 + σₖ) (2 + σₖ))` over all continuing iterations, with
-- `σₖ = algorithm.oneSidedRoundingSigma k`, use
-- `σₖ ≥ (n / (n + 1)) (γ - 1)` to replace each increment by the uniform constant
-- `4 (γ - 1)² / ((1 + 2γ) (2 + γ))`, and compare the resulting lower bound for
-- `log det G_T - log det G₀` with the upper bound coming from the initial translated rounding
-- `W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`. The lower bound `1 ≤ R` is recovered internally from
-- `algorithm.initial_shape_posDef`, `hInitial`, and `n ≥ 1`, while the terminal inner
-- containment is supplied in the source-facing form `W₁(v_T,G_T) ⊆ C`.

namespace GeneralConvexRoundingAlgorithm

section IterationBounds

variable {C : Set E} {gamma R : ℝ} {v0 : E} {G0 : Mat}

/-- Helper for Theorem 7.7: once `n ≥ 2`, the dimension ratio `n / (n + 1)` is at least `2 / 3`.
-/
lemma two_thirds_le_dim_ratio
    (hn : 2 ≤ n) :
    (2 / 3 : ℝ) ≤ (n : ℝ) / (n + 1 : ℝ) := by
  have hn_real : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hden_pos : 0 < (n : ℝ) + 1 := by
    positivity
  rw [le_div_iff₀ hden_pos]
  nlinarith

/-- Helper for Theorem 7.7: in the `n ≥ 2` regime, the continuation lower bound on
`σₖ = algorithm.oneSidedRoundingSigma k` yields the uniform rational drop used in the source proof.
-/
lemma uniform_gamma_drop_le_oneSided_increment_of_two_le
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : 2 ≤ n)
    {T k : ℕ}
    (hsigma :
      ∀ j : ℕ, j < T →
        ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) ≤ algorithm.oneSidedRoundingSigma j)
    (hk : k < T) :
    4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma)) ≤
      (2 * (algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ)) /
        ((1 + algorithm.oneSidedRoundingSigma k) *
          (2 + algorithm.oneSidedRoundingSigma k)) := by
  let σ := algorithm.oneSidedRoundingSigma k
  let b : ℝ := (2 / 3 : ℝ) * (gamma - 1)
  have hgamma : 1 < gamma := algorithm.gamma_one_lt
  have hgamma_sub_nonneg : 0 ≤ gamma - 1 := by
    linarith
  have hratio : (2 / 3 : ℝ) ≤ (n : ℝ) / (n + 1 : ℝ) :=
    two_thirds_le_dim_ratio hn
  have hσ_lower :
      b ≤ σ := by
    have hmul :
        (2 / 3 : ℝ) * (gamma - 1) ≤ ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) := by
      gcongr
    exact le_trans hmul (hsigma k hk)
  have hb_nonneg : 0 ≤ b := by
    positivity
  have hσ_nonneg : 0 ≤ σ := by
    exact le_trans hb_nonneg hσ_lower
  have hb_den_pos : 0 < ((1 + b) * (2 + b)) := by
    positivity
  have hσ_den_pos : 0 < ((1 + σ) * (2 + σ)) := by
    positivity
  have htarget_eq :
      4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma)) =
        2 * b ^ (2 : ℕ) / ((1 + b) * (2 + b)) := by
    dsimp [b]
    field_simp
    ring
  have hmono_cross :
      b ^ (2 : ℕ) * ((1 + σ) * (2 + σ)) ≤
        σ ^ (2 : ℕ) * ((1 + b) * (2 + b)) := by
    have hfactor_nonneg : 0 ≤ 3 * b * σ + 2 * b + 2 * σ := by
      positivity
    nlinarith [hσ_lower, hfactor_nonneg]
  have hmono :
      2 * b ^ (2 : ℕ) / ((1 + b) * (2 + b)) ≤
        2 * σ ^ (2 : ℕ) / ((1 + σ) * (2 + σ)) := by
    field_simp [hb_den_pos.ne', hσ_den_pos.ne']
    nlinarith [hmono_cross]
  rw [htarget_eq]
  simpa [σ] using hmono

/-- Helper for Theorem 7.7: in dimension `1`, the theorem's target uniform constant is strictly
larger than the generic rational determinant gain at the boundary value
`σ = (γ - 1) / 2`. -/
lemma dim_one_target_constant_gt_generic_gain
    (hgamma : 1 < gamma) :
    2 * (((gamma - 1) / 2) ^ (2 : ℕ)) /
        ((1 + (gamma - 1) / 2) * (2 + (gamma - 1) / 2)) <
      4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma)) := by
  have hden_left_pos : 0 < ((1 + (gamma - 1) / 2) * (2 + (gamma - 1) / 2)) := by
    nlinarith
  have hden_right_pos : 0 < ((1 + 2 * gamma) * (2 + gamma)) := by
    nlinarith
  -- Cross-multiplication reduces the comparison to a scalar polynomial inequality.
  have hcross :
      2 * (((gamma - 1) / 2) ^ (2 : ℕ)) * ((1 + 2 * gamma) * (2 + gamma)) <
        4 * (gamma - 1) ^ (2 : ℕ) * ((1 + (gamma - 1) / 2) * (2 + (gamma - 1) / 2)) := by
    nlinarith
  exact (div_lt_div_iff₀ hden_left_pos hden_right_pos).2 hcross

/-- Helper for Theorem 7.7: the chosen maximizer realizes the current dual radius. -/
lemma maximizer_dualDistance_eq_radius
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) :
    generalConvexRoundingDualDistance (algorithm.currentShape k) (algorithm.center k)
      (algorithm.maximizer k) = algorithm.radius k := by
  rcases algorithm.maximizer_mem_and_isMaxOn k with ⟨hgC, hmax⟩
  have hisLUB :
      IsLUB
        {y : ℝ | ∃ x ∈ C,
            generalConvexRoundingDualDistance (algorithm.currentShape k) (algorithm.center k) x =
              y}
        (generalConvexRoundingDualDistance (algorithm.currentShape k) (algorithm.center k)
          (algorithm.maximizer k)) := by
    -- The selected point is an actual maximizer, so it gives the least upper bound of the image.
    simpa [isMaxOn_iff] using hmax.isLUB hgC
  -- Rewrite the radius as the supremum of the same image set and identify it with the maximizer.
  rw [radius, generalConvexRoundingRadius_eq_sSup]
  symm
  exact hisLUB.csSup_eq ⟨algorithm.maximizer k, hgC, rfl⟩

/-- Helper for Theorem 7.7: in dimension `1`, the source quantity `σₖ` is exactly
`(rₖ - 1) / 2`. -/
lemma one_sided_sigma_eq_half_radius_sub_one_of_dim_one
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : n = 1) (k : ℕ) :
    algorithm.oneSidedRoundingSigma k = (algorithm.radius k - 1) / 2 := by
  -- Rewrite `σₖ` to the source formula `(rₖ - n) / (n + 1)` for the chosen maximizer.
  rw [_root_.oneSidedRoundingSigma_def]
  have hradius :
      generalConvexRoundingDualDistance (algorithm.currentShape k) (algorithm.center k)
        (algorithm.maximizer k) =
        algorithm.radius k := by
    exact maximizer_dualDistance_eq_radius algorithm k
  have hn_real : (n : ℝ) = 1 := by
    exact_mod_cast hn
  -- In dimension `1`, the owner-side formula simplifies to `(rₖ - 1) / 2`.
  rw [generalConvexRoundingDualDistance, hradius, hn_real]
  ring

/-- Helper for Theorem 7.7: in dimension `1`, the stopping inequality plus the theorem's
continuation lower bound force the boundary case `rₖ = γ`. -/
lemma stopping_radius_eq_gamma_of_sigma_lower_bound_dim_one
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : n = 1) {k : ℕ}
    (hsigma :
      ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) ≤ algorithm.oneSidedRoundingSigma k)
    (hstop : algorithm.stoppingCriterion k) :
    algorithm.radius k = gamma ∧
      algorithm.oneSidedRoundingSigma k = (gamma - 1) / 2 := by
  have hsigma_eq := one_sided_sigma_eq_half_radius_sub_one_of_dim_one algorithm hn k
  have hn_real : (n : ℝ) = 1 := by
    exact_mod_cast hn
  have hratio :
      ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) = (gamma - 1) / 2 := by
    rw [hn_real]
    ring
  have hradius_ge : gamma ≤ algorithm.radius k := by
    -- Converting the theorem hypothesis into the radius form gives the missing reverse inequality.
    rw [hsigma_eq, hratio] at hsigma
    nlinarith
  have hradius_le : algorithm.radius k ≤ gamma := by
    -- In dimension `1`, the stopping predicate is exactly `rₖ ≤ γ`.
    rw [GeneralConvexRoundingAlgorithm.stoppingCriterion, generalConvexRoundingShouldStop,
      hn_real] at hstop
    simpa using hstop
  have hradius_eq : algorithm.radius k = gamma := le_antisymm hradius_le hradius_ge
  refine ⟨hradius_eq, ?_⟩
  -- Substituting the boundary radius gives the announced boundary value for `σₖ`.
  rw [hsigma_eq, hradius_eq]

/-- Helper for Theorem 7.7: in dimension `1`, the exact logarithmic gain `2 log (1 + σ)` already
dominates the theorem's target constant once `σ ≥ (γ - 1) / 2`. -/
lemma uniform_gamma_drop_le_dim_one_exact_gain
    (hgamma : 1 < gamma) {σ : ℝ}
    (hσ : (gamma - 1) / 2 ≤ σ) :
    4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma)) ≤
      2 * Real.log (1 + σ) := by
  let σ0 : ℝ := (gamma - 1) / 2
  have hσ0_nonneg : 0 ≤ σ0 := by
    dsimp [σ0]
    linarith
  have hσ0_pos : 0 < 1 + σ0 := by
    dsimp [σ0]
    linarith
  have hconst_le_boundary :
      4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma)) ≤
        4 * σ0 / (σ0 + 2) := by
    -- The theorem coefficient is already dominated by the exact boundary gain at
    -- `σ = (gamma - 1) / 2`.
    dsimp [σ0]
    have hden1 : 0 < (1 + 2 * gamma) * (2 + gamma) := by
      nlinarith
    have hden2 : 0 < (gamma - 1) / 2 + 2 := by
      nlinarith
    have hcross :
        4 * (gamma - 1) ^ (2 : ℕ) * ((gamma - 1) / 2 + 2) ≤
          (4 * ((gamma - 1) / 2)) * ((1 + 2 * gamma) * (2 + gamma)) := by
      nlinarith
    exact (div_le_div_iff₀ hden1 hden2).2 hcross
  have hboundary_log :
      4 * σ0 / (σ0 + 2) ≤ 2 * Real.log (1 + σ0) := by
    -- Apply the scalar logarithm lower bound exactly at the boundary value.
    have hlog := Real.le_log_one_add_of_nonneg hσ0_nonneg
    have hscaled : 2 * (2 * σ0 / (σ0 + 2)) ≤ 2 * Real.log (1 + σ0) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have hrewrite : 4 * σ0 / (σ0 + 2) = 2 * (2 * σ0 / (σ0 + 2)) := by ring
    rw [hrewrite]
    exact hscaled
  have hσ0_le : 1 + σ0 ≤ 1 + σ := by
    dsimp [σ0]
    simpa [add_comm] using add_le_add_left hσ 1
  have hlog_mono :
      2 * Real.log (1 + σ0) ≤ 2 * Real.log (1 + σ) := by
    -- The logarithm is monotone on positive reals, so the boundary gain extends to every
    -- larger `σ`.
    have hmono : Real.log (1 + σ0) ≤ Real.log (1 + σ) :=
      Real.log_le_log hσ0_pos hσ0_le
    linarith
  exact le_trans hconst_le_boundary (le_trans hboundary_log hlog_mono)

/-- Helper for Theorem 7.7: telescoping a uniform lower bound on the logarithmic determinant
increments gives a linear lower bound on the total growth up to time `T`.
-/
lemma logdet_growth_lower_bound_upto
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    {T : ℕ} {c : ℝ}
    (hstep :
      ∀ k : ℕ, k < T →
        c ≤ Real.log (Matrix.det (algorithm.shape (k + 1))) -
          Real.log (Matrix.det (algorithm.shape k))) :
    c * (T : ℝ) ≤
      Real.log (Matrix.det (algorithm.shape T)) - Real.log (Matrix.det G0) := by
  induction T with
  | zero =>
      -- At time `0`, the telescoping sum is empty and `shape 0 = G0`.
      rw [algorithm.shape_zero]
      ring_nf
  | succ T ih =>
      have hstep_last :
          c ≤ Real.log (Matrix.det (algorithm.shape (T + 1))) -
            Real.log (Matrix.det (algorithm.shape T)) :=
        hstep T (Nat.lt_succ_self T)
      have hstep_prefix :
          ∀ k : ℕ, k < T →
            c ≤ Real.log (Matrix.det (algorithm.shape (k + 1))) -
              Real.log (Matrix.det (algorithm.shape k)) := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self T))
      have hprefix := ih hstep_prefix
      -- Add the last increment to the already-telescoped prefix.
      have hcast : c * ((T + 1 : ℕ) : ℝ) = c * (T : ℝ) + c := by
        norm_num [left_distrib, right_distrib]
      rw [hcast]
      have hshape :
          Real.log (Matrix.det (algorithm.shape (T + 1))) - Real.log (Matrix.det G0) =
            (Real.log (Matrix.det (algorithm.shape (T + 1))) -
              Real.log (Matrix.det (algorithm.shape T))) +
            (Real.log (Matrix.det (algorithm.shape T)) - Real.log (Matrix.det G0)) := by
        ring
      rw [hshape]
      linarith

/-- Helper for Theorem 7.7: a factorization `A = Bᴴ B` rewrites the quadratic form of `A`
as the Euclidean norm of `B x`. -/
private theorem sqrt_inner_eq_euclidean_image_norm
    (A B : Mat) (hAeq : A = Bᴴ * B) (x : E) :
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

/-- Helper for Theorem 7.7: translated matrix ellipsoids have volume
`√det(G)` times the Euclidean closed-ball volume of the same radius. -/
private theorem matrixEllipsoid_volume
    (G : Mat) (v : E) (hG : G.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    volume (W[r](v, G)) =
      ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : E) r) := by
  have htranslate :
      (fun x : E ↦ v + x) ⁻¹' W[r](v, G) = W[r](G) := by
    -- Translate the ellipsoid back to the centered owner before applying the linear-volume proof.
    ext x
    rw [Set.mem_preimage, mem_matrixEllipsoid_iff, mem_centeredMatrixEllipsoid_iff]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  obtain ⟨B, hBunit, hBself, hfactor⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hG.isStrictlyPositive
  have hInvFactor : G⁻¹ = B⁻¹ᴴ * B⁻¹ := by
    -- Inverting `G = Bᴴ B` gives the centered quadratic form needed for the ball preimage.
    calc
      G⁻¹ = (B * B)⁻¹ := by
        rw [hfactor]
      _ = B⁻¹ * B⁻¹ := by
        rw [Matrix.mul_inv_rev]
      _ = B⁻¹ᴴ * B⁻¹ := by
        congr 1
        rw [Matrix.conjTranspose_nonsing_inv]
        simpa using congrArg Inv.inv hBself.symm
  have hcentered :
      volume (W[r](G)) =
        ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : E) r) := by
    have hzero :
        W[r](G) = ((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : E) r := by
      -- The centered ellipsoid is exactly the inverse image of the Euclidean radius-`r` ball.
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
  calc
    volume (W[r](v, G))
        = volume ((fun x : E ↦ v + x) ⁻¹' W[r](v, G)) := by
            symm
            exact measure_preimage_add volume v (W[r](v, G))
    _ = volume (W[r](G)) := by
          rw [htranslate]
    _ = ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : E) r) := hcentered

/-- Helper for Theorem 7.7: the volume identity for translated matrix ellipsoids in real-valued
form. -/
lemma matrixEllipsoid_volume_toReal
    (G : Mat) (v : E) (hG : G.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    (volume (W[r](v, G))).toReal =
      Real.sqrt G.det * (volume (Metric.closedBall (0 : E) r)).toReal := by
  rw [matrixEllipsoid_volume G v hG hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  simp [measure_closedBall_lt_top.ne]

/-- Helper for Theorem 7.7: Euclidean closed-ball volumes scale by `r ^ n` in `ℝⁿ`. -/
private lemma closedBall_volume_toReal_eq_pow
    (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : E) r)).toReal =
      r ^ n * (volume (Metric.closedBall (0 : E) 1)).toReal := by
  -- Compare the explicit mathlib formulas for the radius-`r` and radius-`1` closed balls.
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hn)
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall]
  simp [hr, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 7.7: the initial and terminal containment chain bounds the total
log-determinant growth by `2 n log R`. -/
lemma terminal_logdet_upper_bound_of_rounding_containment
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : 1 ≤ n)
    {T : ℕ}
    (hInitial : IsBetaRounding C R G0 v0)
    (hFinal : W[1]((algorithm.center T), (algorithm.shape T)) ⊆ C) :
    Real.log (Matrix.det (algorithm.shape T)) - Real.log (Matrix.det G0) ≤
      2 * (n : ℝ) * Real.log R := by
  have hcontain : W[1]((algorithm.center T), (algorithm.shape T)) ⊆ W[R](v0, G0) :=
    Set.Subset.trans hFinal hInitial.subset_beta_ellipsoid
  have hv0_mem : v0 ∈ W[1](v0, G0) := by
    -- The ellipsoid center belongs to every translated ellipsoid of nonnegative radius.
    simpa [mem_matrixEllipsoid_iff]
  have hv0_body : v0 ∈ C :=
    hInitial.unit_matrixEllipsoid_subset hv0_mem
  have hv0_outer : v0 ∈ W[R](v0, G0) :=
    hInitial.subset_beta_ellipsoid hv0_body
  have hR_nonneg : 0 ≤ R := by
    simpa [mem_matrixEllipsoid_iff] using hv0_outer
  have hvol_right_lt_top : volume (W[R](v0, G0)) < ⊤ := by
    rw [matrixEllipsoid_volume G0 v0 (algorithm.initial_shape_posDef) hR_nonneg]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have hvol_mono :
      volume (W[1]((algorithm.center T), (algorithm.shape T))) ≤ volume (W[R](v0, G0)) :=
    measure_mono hcontain
  have hvol_mono_toReal :
      (volume (W[1]((algorithm.center T), (algorithm.shape T)))).toReal ≤
        (volume (W[R](v0, G0))).toReal :=
    ENNReal.toReal_mono hvol_right_lt_top.ne hvol_mono
  rw [matrixEllipsoid_volume_toReal (algorithm.shape T) (algorithm.center T)
      (algorithm.shape_posDef T) (show (0 : ℝ) ≤ 1 by positivity),
    matrixEllipsoid_volume_toReal G0 v0 (algorithm.initial_shape_posDef) hR_nonneg] at hvol_mono_toReal
  rw [closedBall_volume_toReal_eq_pow hn hR_nonneg] at hvol_mono_toReal
  have hball_one_pos : 0 < (volume (Metric.closedBall (0 : E) 1)).toReal := by
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  have hsqrt_le :
      Real.sqrt (Matrix.det (algorithm.shape T)) ≤
        R ^ n * Real.sqrt (Matrix.det G0) := by
    have hcancel :
        Real.sqrt (Matrix.det (algorithm.shape T)) *
            (volume (Metric.closedBall (0 : E) 1)).toReal ≤
          (R ^ n * Real.sqrt (Matrix.det G0)) *
            (volume (Metric.closedBall (0 : E) 1)).toReal := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hvol_mono_toReal
    exact le_of_mul_le_mul_right hcancel hball_one_pos
  have hdetT_pos : 0 < Matrix.det (algorithm.shape T) :=
    (algorithm.shape_posDef T).det_pos
  have hdet0_pos : 0 < Matrix.det G0 :=
    algorithm.initial_shape_posDef.det_pos
  have hsqrtT_pos : 0 < Real.sqrt (Matrix.det (algorithm.shape T)) := by
    exact Real.sqrt_pos.mpr hdetT_pos
  have hsqrt0_pos : 0 < Real.sqrt (Matrix.det G0) := by
    exact Real.sqrt_pos.mpr hdet0_pos
  have hR_pos : 0 < R := by
    have hrhs_pos : 0 < R ^ n * Real.sqrt (Matrix.det G0) :=
      lt_of_lt_of_le hsqrtT_pos hsqrt_le
    by_cases hR0 : R = 0
    · have hn_pos : 0 < n := by
        exact_mod_cast hn
      simp [hR0, hn_pos.ne'] at hrhs_pos
    · exact lt_of_le_of_ne hR_nonneg (Ne.symm hR0)
  have hlog_sqrt_le :
      Real.log (Real.sqrt (Matrix.det (algorithm.shape T))) ≤
        Real.log (R ^ n * Real.sqrt (Matrix.det G0)) := by
    exact Real.log_le_log hsqrtT_pos hsqrt_le
  have hlog_expand :
      Real.log (R ^ n * Real.sqrt (Matrix.det G0)) =
        (n : ℝ) * Real.log R + Real.log (Real.sqrt (Matrix.det G0)) := by
    rw [Real.log_mul (show R ^ n ≠ 0 by positivity) hsqrt0_pos.ne', Real.log_pow]
  have hhalf :
      Real.log (Matrix.det (algorithm.shape T)) / 2 ≤
        (n : ℝ) * Real.log R + Real.log (Matrix.det G0) / 2 := by
    rw [hlog_expand, Real.log_sqrt hdetT_pos.le, Real.log_sqrt hdet0_pos.le] at hlog_sqrt_le
    simpa using hlog_sqrt_le
  have hdouble :
      Real.log (Matrix.det (algorithm.shape T)) ≤
        2 * ((n : ℝ) * Real.log R + Real.log (Matrix.det G0) / 2) := by
    nlinarith
  linarith

/-- Helper for Theorem 7.7: in dimension `1`, the single coordinate of the maximizer displacement
has square `rₖ² det Gₖ`. -/
private lemma maximizer_coordinate_sq_eq_radius_sq_mul_det_of_dim_one
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : n = 1) (k : ℕ) :
    ((algorithm.maximizer k - algorithm.center k).ofLp 0) ^ (2 : ℕ) =
      (algorithm.radius k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k) := by
  subst hn
  let d : EuclideanSpace ℝ (Fin 1) := algorithm.maximizer k - algorithm.center k
  have hdet_pos : 0 < Matrix.det (algorithm.shape k) :=
    (algorithm.shape_posDef k).det_pos
  have hquad_nonneg :
      0 ≤ inner ℝ d ((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d) := by
    have hPosLin : (Matrix.toEuclideanLin (algorithm.shape k)⁻¹).IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr (algorithm.shape_posDef k).inv.posSemidef
    simpa [d, real_inner_comm] using hPosLin.inner_nonneg_right d
  have hr_sq :
      (algorithm.radius k) ^ (2 : ℕ) =
        inner ℝ d ((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d) := by
    -- Square the dual-radius formula at the chosen maximizer to remove the outer square root.
    rw [← maximizer_dualDistance_eq_radius (algorithm := algorithm) k,
      generalConvexRoundingDualDistance_eq_sqrt_inner_inv, Real.sq_sqrt hquad_nonneg]
  have hlin :
      (((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d).ofLp 0) =
        (Matrix.det (algorithm.shape k))⁻¹ * d.ofLp 0 := by
    -- In `Fin 1`, the inverse matrix acts by scaling with the reciprocal determinant.
    change (((algorithm.shape k)⁻¹ *ᵥ d.ofLp) 0) =
      (Matrix.det (algorithm.shape k))⁻¹ * d.ofLp 0
    rw [Matrix.inv_subsingleton, Matrix.det_fin_one]
    simp [Ring.inverse_eq_inv]
  have hinner :
      inner ℝ d ((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d) =
        ((d.ofLp 0) ^ (2 : ℕ)) / Matrix.det (algorithm.shape k) := by
    calc
      inner ℝ d ((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d) =
          dotProduct d.ofLp (((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d).ofLp) := by
            simpa using
              (EuclideanSpace.inner_eq_star_dotProduct d
                ((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d)).symm
      _ = d.ofLp 0 * (((Matrix.toEuclideanLin (algorithm.shape k)⁻¹) d).ofLp 0) := by
            simp [dotProduct]
      _ = d.ofLp 0 * ((Matrix.det (algorithm.shape k))⁻¹ * d.ofLp 0) := by
            rw [hlin]
      _ = ((d.ofLp 0) ^ (2 : ℕ)) / Matrix.det (algorithm.shape k) := by
            field_simp [hdet_pos.ne']
            ring
  have hcoord :
      (d.ofLp 0) ^ (2 : ℕ) = (algorithm.radius k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k) := by
    -- Move the determinant to the right-hand side after rewriting the quadratic form.
    rw [hr_sq, hinner]
    field_simp [hdet_pos.ne']
    ring
  simpa [d] using hcoord

/-- Helper for Theorem 7.7: in dimension `1`, a genuinely continuing step multiplies the shape
determinant by `(1 + σₖ)^2`. -/
lemma det_shape_succ_eq_sq_one_add_sigma_mul_det_shape_of_dim_one
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : n = 1) {k : ℕ}
    (hk : ¬ algorithm.stoppingCriterion k) :
    Matrix.det (algorithm.shape (k + 1)) =
      (1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k) := by
  subst hn
  have hradius_lt : gamma < algorithm.radius k := by
    -- A genuinely continuing step in dimension `1` has radius strictly above the threshold `γ`.
    rw [GeneralConvexRoundingAlgorithm.stoppingCriterion, generalConvexRoundingShouldStop] at hk
    simpa using not_le.mp hk
  have hradius_ne_zero : algorithm.radius k ≠ 0 := by
    linarith [algorithm.gamma_one_lt, hradius_lt]
  have hradius_ne_one : algorithm.radius k - 1 ≠ 0 := by
    linarith [algorithm.gamma_one_lt, hradius_lt]
  have halpha :
      generalConvexRoundingAlpha 1 (algorithm.radius k) = 1 := by
    -- The source update coefficient collapses to `1` in the one-dimensional continuing regime.
    unfold generalConvexRoundingAlpha
    field_simp [hradius_ne_one]
    ring
  have hdet_step :
      Matrix.det (algorithm.shape (k + 1)) =
        generalConvexRoundingBeta 1 (algorithm.radius k) *
          ((algorithm.maximizer k - algorithm.center k).ofLp 0) ^ (2 : ℕ) := by
    -- With `α = 1`, the next shape is just the rank-one update term.
    rw [algorithm.shape_succ_of_not_stopping hk, generalConvexRoundingNextShape, halpha]
    simp [Matrix.det_fin_one, Matrix.vecMulVec_eq (Fin 1), pow_two, mul_assoc, mul_left_comm,
      mul_comm]
  have hcoord :
      ((algorithm.maximizer k - algorithm.center k).ofLp 0) ^ (2 : ℕ) =
        (algorithm.radius k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k) :=
    maximizer_coordinate_sq_eq_radius_sq_mul_det_of_dim_one algorithm rfl k
  have hsigma :
      algorithm.oneSidedRoundingSigma k = (algorithm.radius k - 1) / 2 :=
    one_sided_sigma_eq_half_radius_sub_one_of_dim_one algorithm rfl k
  have hbeta :
      generalConvexRoundingBeta 1 (algorithm.radius k) * (algorithm.radius k) ^ (2 : ℕ) =
        (1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) := by
    -- Rewrite the remaining scalar coefficient entirely through `σₖ = (rₖ - 1) / 2`.
    rw [hsigma]
    unfold generalConvexRoundingBeta generalConvexRoundingAlpha
    field_simp [hradius_ne_zero, hradius_ne_one]
    ring
  calc
    Matrix.det (algorithm.shape (k + 1)) =
        generalConvexRoundingBeta 1 (algorithm.radius k) *
          ((algorithm.maximizer k - algorithm.center k).ofLp 0) ^ (2 : ℕ) := hdet_step
    _ =
        generalConvexRoundingBeta 1 (algorithm.radius k) *
          ((algorithm.radius k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k)) := by
            rw [hcoord]
    _ =
        (generalConvexRoundingBeta 1 (algorithm.radius k) * (algorithm.radius k) ^ (2 : ℕ)) *
          Matrix.det (algorithm.shape k) := by ring
    _ = (1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k) := by
          rw [hbeta]

/-- Helper for Theorem 7.7: in dimension `1`, a genuinely continuing step gains exactly
`2 log (1 + σₖ)` in logarithmic determinant. -/
lemma logdet_increment_eq_two_log_one_add_sigma_of_dim_one
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : n = 1) {k : ℕ}
    (hk : ¬ algorithm.stoppingCriterion k) :
    Real.log (Matrix.det (algorithm.shape (k + 1))) -
      Real.log (Matrix.det (algorithm.shape k)) =
        2 * Real.log (1 + algorithm.oneSidedRoundingSigma k) := by
  have hdet_step :=
    det_shape_succ_eq_sq_one_add_sigma_mul_det_shape_of_dim_one algorithm hn hk
  have hsigma :
      algorithm.oneSidedRoundingSigma k = (algorithm.radius k - 1) / 2 :=
    one_sided_sigma_eq_half_radius_sub_one_of_dim_one algorithm hn k
  have hn_real : (n : ℝ) = 1 := by
    exact_mod_cast hn
  have hradius_lt : gamma < algorithm.radius k := by
    -- In dimension `1`, a continuing step means the current radius is strictly above `γ`.
    rw [GeneralConvexRoundingAlgorithm.stoppingCriterion, generalConvexRoundingShouldStop,
      hn_real] at hk
    simpa using not_le.mp hk
  have hone_sigma_pos : 0 < 1 + algorithm.oneSidedRoundingSigma k := by
    -- Rewriting `σₖ` through the radius makes positivity immediate from `rₖ > γ > 1`.
    rw [hsigma]
    linarith [algorithm.gamma_one_lt, hradius_lt]
  have hdetk_pos : 0 < Matrix.det (algorithm.shape k) :=
    (algorithm.shape_posDef k).det_pos
  calc
    Real.log (Matrix.det (algorithm.shape (k + 1))) -
        Real.log (Matrix.det (algorithm.shape k)) =
      Real.log ((1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) *
          Matrix.det (algorithm.shape k)) -
        Real.log (Matrix.det (algorithm.shape k)) := by
          rw [hdet_step]
    _ = Real.log
          (((1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) * Matrix.det (algorithm.shape k)) /
            Matrix.det (algorithm.shape k)) := by
          simpa using
            (Real.log_div (mul_ne_zero (pow_ne_zero 2 hone_sigma_pos.ne') hdetk_pos.ne')
              hdetk_pos.ne').symm
    _ = Real.log ((1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ)) := by
          have hcancel :
              ((1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) *
                  Matrix.det (algorithm.shape k)) /
                Matrix.det (algorithm.shape k) =
                (1 + algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) := by
            field_simp [hdetk_pos.ne']
          rw [hcancel]
    _ = 2 * Real.log (1 + algorithm.oneSidedRoundingSigma k) := by
          rw [Real.log_pow]
          ring

/-- Helper for Theorem 7.7: a genuinely continuing step rewrites to the canonical translated
one-sided center update at the maximizer displacement. -/
lemma center_succ_eq_oneSidedShift_of_not_stopping
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    {k : ℕ} (hk : ¬ algorithm.stoppingCriterion k) :
    algorithm.center (k + 1) =
      algorithm.center k +
        ((((algorithm.radius k - 1) / (2 * algorithm.radius k)) *
          oneSidedRoundingAlphaStar (algorithm.currentShape k)
            (algorithm.maximizer k - algorithm.center k)) •
          (algorithm.maximizer k - algorithm.center k)) := by
  set G : {A : Mat // A.PosDef} := algorithm.currentShape k
  set g : E := algorithm.maximizer k - algorithm.center k
  set r : ℝ := Seminorm.dualNorm (positiveDefMatrixNorm G.1 G.2) g
  have hradius :
      algorithm.radius k = r := by
    -- Repackage the chosen maximizer's dual distance as the current radius.
    symm
    simpa [r, g, G, generalConvexRoundingDualDistance] using
      maximizer_dualDistance_eq_radius (algorithm := algorithm) k
  have halpha :
      oneSidedRoundingAlphaStar G g = generalConvexRoundingAlpha n (algorithm.radius k) := by
    rw [oneSidedRoundingAlphaStar, generalConvexRoundingAlpha, hradius, r]
  -- Unfold the algorithmic center update and rewrite it onto the owner-side `α*` surface.
  rw [algorithm.center_succ_of_not_stopping hk, generalConvexRoundingNextCenter, halpha]
  simp [g, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 7.7: a genuinely continuing step rewrites to the canonical one-sided
updated matrix at the maximizer displacement and `α*`. -/
lemma shape_succ_eq_oneSidedUpdatedMatrix_of_not_stopping
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    {k : ℕ} (hk : ¬ algorithm.stoppingCriterion k) :
    algorithm.shape (k + 1) =
      oneSidedRoundingUpdatedMatrix (algorithm.currentShape k)
        (algorithm.maximizer k - algorithm.center k)
        (oneSidedRoundingAlphaStar (algorithm.currentShape k)
          (algorithm.maximizer k - algorithm.center k)) := by
  set G : {A : Mat // A.PosDef} := algorithm.currentShape k
  set g : E := algorithm.maximizer k - algorithm.center k
  set r : ℝ := Seminorm.dualNorm (positiveDefMatrixNorm G.1 G.2) g
  have hradius :
      algorithm.radius k = r := by
    -- Repackage the chosen maximizer's dual distance as the current radius.
    symm
    simpa [r, g, G, generalConvexRoundingDualDistance] using
      maximizer_dualDistance_eq_radius (algorithm := algorithm) k
  have halpha :
      oneSidedRoundingAlphaStar G g = generalConvexRoundingAlpha n (algorithm.radius k) := by
    rw [oneSidedRoundingAlphaStar, generalConvexRoundingAlpha, hradius, r]
  -- Unfold the shape update and rewrite it as the owner-side one-sided matrix interpolation.
  rw [algorithm.shape_succ_of_not_stopping hk, generalConvexRoundingNextShape,
    oneSidedRoundingUpdatedMatrix_def, halpha, hradius, r]
  simp [g, G, generalConvexRoundingBeta, generalConvexRoundingAlpha]

/-- Helper for Theorem 7.7: every genuinely continuing prefix iterate still contains the unit
translated ellipsoid inside `C`. -/
lemma unitEllipsoid_subset_upto
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    {T : ℕ}
    (hInitial : IsBetaRounding C R G0 v0)
    (hContinueStrict :
      ∀ k : ℕ, k < T →
        ¬ algorithm.stoppingCriterion k) :
    ∀ k : ℕ, k ≤ T → W[1]((algorithm.center k), (algorithm.shape k)) ⊆ C := by
  intro k hk
  induction k with
  | zero =>
      -- At time `0`, the initial translated rounding already gives the required containment.
      simpa [algorithm.center_zero, algorithm.shape_zero] using hInitial.unit_matrixEllipsoid_subset
  | succ k ih =>
      have hk_prev : k ≤ T := Nat.le_of_succ_le hk
      have hk_lt : k < T := Nat.lt_of_succ_le hk
      have hk_continue : ¬ algorithm.stoppingCriterion k := hContinueStrict k hk_lt
      have hprev : W[1]((algorithm.center k), (algorithm.shape k)) ⊆ C := ih hk_prev
      intro y hy
      set G : {A : Mat // A.PosDef} := algorithm.currentShape k
      set g : E := algorithm.maximizer k - algorithm.center k
      set r : ℝ := Seminorm.dualNorm (positiveDefMatrixNorm G.1 G.2) g
      set α : ℝ := oneSidedRoundingAlphaStar G g
      set shift : E := ((((algorithm.radius k - 1) / (2 * algorithm.radius k)) * α) • g)
      have hradius :
          algorithm.radius k = r := by
        -- Repackage the chosen maximizer's dual distance as the current radius.
        symm
        simpa [r, g, G, generalConvexRoundingDualDistance] using
          maximizer_dualDistance_eq_radius (algorithm := algorithm) k
      have hr :
          (n : ℝ) ≤ r := by
        have hstop_lt :
            gamma * (n : ℝ) < algorithm.radius k := by
          -- A genuinely continuing step lies strictly above the stopping threshold `γ n`.
          rw [GeneralConvexRoundingAlgorithm.stoppingCriterion, generalConvexRoundingShouldStop] at
            hk_continue
          exact lt_of_not_ge hk_continue
        have hgamma_mul :
            (n : ℝ) ≤ gamma * (n : ℝ) := by
          have hgamma_one_le : 1 ≤ gamma := by
            linarith [algorithm.gamma_one_lt]
          have hn_nonneg : 0 ≤ (n : ℝ) := by
            positivity
          nlinarith
        rw [← hradius]
        exact le_trans hgamma_mul hstop_lt.le
      have hα : α ∈ Set.Ico (0 : ℝ) 1 :=
        oneSidedRoundingAlphaStar_mem_Ico G g hr
      have hy_shifted :
          y - algorithm.center k ∈
            W[1](shift, oneSidedRoundingUpdatedMatrix G g α) := by
        -- Rewrite the translated next ellipsoid back to the centered one-step inclusion surface.
        rw [center_succ_eq_oneSidedShift_of_not_stopping (algorithm := algorithm) hk_continue,
          shape_succ_eq_oneSidedUpdatedMatrix_of_not_stopping (algorithm := algorithm)
            hk_continue] at hy
        rw [mem_matrixEllipsoid_iff] at hy ⊢
        simpa [shift, α, hradius, r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
      have hy_hull :
          y - algorithm.center k ∈
            convexHull ℝ (W[1](G.1) ∪ ({g} : Set E)) :=
        oneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint G g hα
          (by simpa [shift, α, hradius, r] using hy_shifted)
      have hpreimage_convex :
          Convex ℝ {z : E | algorithm.center k + z ∈ C} := by
        -- Pull the ambient convex body back along translation by the current center.
        simpa [Set.preimage, vadd_eq_add] using
          (algorithm.convexSet.affine_preimage
            ((AffineEquiv.constVAdd ℝ E (algorithm.center k)).toAffineMap))
      have hy_preimage :
          y - algorithm.center k ∈ {z : E | algorithm.center k + z ∈ C} := by
        refine (convexHull_min ?_ hpreimage_convex) hy_hull
        intro z hz
        rcases hz with hz | hz
        · have hz_translated :
            algorithm.center k + z ∈ W[1]((algorithm.center k), (algorithm.shape k)) := by
            rw [mem_matrixEllipsoid_iff, mem_centeredMatrixEllipsoid_iff]
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
          exact hprev hz_translated
        · have hmax_mem : algorithm.maximizer k ∈ C :=
            (algorithm.maximizer_mem_and_isMaxOn k).1
          simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmax_mem
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_preimage

/-- Theorem 7.7: if `n ≥ 1`, an Algorithm 7.7 run starts from an `R`-rounding
`W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`, every `k < T` is a genuine continuing step in the current
owner API and satisfies the source continuation threshold
`(n / (n + 1)) (γ - 1) ≤ σₖ`, and the first post-continuation iterate `T` falls below that
threshold, then
`T ≤ ((1 + 2γ) (2 + γ) / (2 (γ - 1)²)) n log R`. -/
theorem iterations_le
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : 1 ≤ n)
    {T : ℕ}
    (hInitial : IsBetaRounding C R G0 v0)
    (hContinueStrict :
      ∀ k : ℕ, k < T →
        ¬ algorithm.stoppingCriterion k)
    (hContinue :
      ∀ k : ℕ, k < T →
        ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) ≤ algorithm.oneSidedRoundingSigma k)
    (hStop :
      algorithm.oneSidedRoundingSigma T <
        ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1)) :
    (T : ℝ) ≤
      ((1 + 2 * gamma) * (2 + gamma)) / (2 * (gamma - 1) ^ (2 : ℕ)) *
        (n : ℝ) * Real.log R := by
  let c : ℝ :=
    4 * (gamma - 1) ^ (2 : ℕ) / ((1 + 2 * gamma) * (2 + gamma))
  -- Route correction: the earlier blocker was the transport from the centered one-step
  -- ellipsoid inclusion to the translated iterate surface. The proof now closes by making that
  -- bridge once, then reusing the owner-side determinant-growth lemmas.
  have hfinal :
      W[1]((algorithm.center T), (algorithm.shape T)) ⊆ C :=
    unitEllipsoid_subset_upto (algorithm := algorithm) hInitial hContinueStrict T le_rfl
  have hupper :=
    terminal_logdet_upper_bound_of_rounding_containment algorithm hn hInitial hfinal
  have huniform :
      ∀ k : ℕ, k < T →
        c ≤ Real.log (Matrix.det (algorithm.shape (k + 1))) -
          Real.log (Matrix.det (algorithm.shape k)) := by
    intro k hk
    by_cases hdim1 : n = 1
    · have hsigma_half :
          (gamma - 1) / 2 ≤ algorithm.oneSidedRoundingSigma k := by
        have hratio :
            ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) = (gamma - 1) / 2 := by
          have hdim1_real : (n : ℝ) = 1 := by
            exact_mod_cast hdim1
          rw [hdim1_real]
          ring
        simpa [c, hratio] using hContinue k hk
      have hstep :
          Real.log (Matrix.det (algorithm.shape (k + 1))) -
            Real.log (Matrix.det (algorithm.shape k)) =
              2 * Real.log (1 + algorithm.oneSidedRoundingSigma k) :=
        logdet_increment_eq_two_log_one_add_sigma_of_dim_one algorithm hdim1
          (hContinueStrict k hk)
      -- In dimension `1`, the exact logarithmic increment already dominates the target constant.
      rw [hstep]
      exact uniform_gamma_drop_le_dim_one_exact_gain (gamma := gamma) algorithm.gamma_one_lt
        hsigma_half
    · have hn_two : 2 ≤ n := by
        omega
      have huniform_rational :=
        uniform_gamma_drop_le_oneSided_increment_of_two_le algorithm hn_two
          (T := T) hContinue hk
      set G : {A : Mat // A.PosDef} := algorithm.currentShape k
      set g : E := algorithm.maximizer k - algorithm.center k
      set r : ℝ := Seminorm.dualNorm (positiveDefMatrixNorm G.1 G.2) g
      have hratio_nonneg :
          0 ≤ ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) := by
        have hgamma_nonneg : 0 ≤ gamma - 1 := by
          linarith [algorithm.gamma_one_lt]
        exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hgamma_nonneg
      have hsigma_nonneg : 0 ≤ algorithm.oneSidedRoundingSigma k := by
        exact le_trans hratio_nonneg (hContinue k hk)
      have hsigma_nonneg' : 0 ≤ _root_.oneSidedRoundingSigma G g := by
        simpa [G, g] using hsigma_nonneg
      have hr :
          (n : ℝ) ≤ r := by
        -- Rewrite the source quantity `σₖ = (rₖ - n) / (n + 1)` back to the current dual radius.
        rw [_root_.oneSidedRoundingSigma_def] at hsigma_nonneg'
        have hsigma_nonneg_r : 0 ≤ (r - (n : ℝ)) / ((n : ℝ) + 1) := by
          simpa [r] using hsigma_nonneg'
        nlinarith
      have hα :
          oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 :=
        oneSidedRoundingAlphaStar_mem_Ico G g hr
      have hr0 : r ≠ 0 := by
        have hn_real : (2 : ℝ) ≤ n := by
          exact_mod_cast hn_two
        have htwo : (2 : ℝ) ≤ r := le_trans hn_real hr
        linarith
      have hpotential_lower :
          2 * (algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ) /
              ((1 + algorithm.oneSidedRoundingSigma k) *
                (2 + algorithm.oneSidedRoundingSigma k)) ≤
            oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := by
        rcases oneSidedRoundingPotential_alphaStar_lower_bound_rational G g hr with hbad | hgood
        · omega
        · simpa [G, g] using hgood
      have hshape :
          algorithm.shape (k + 1) =
            oneSidedRoundingUpdatedMatrix G g (oneSidedRoundingAlphaStar G g) :=
        shape_succ_eq_oneSidedUpdatedMatrix_of_not_stopping (algorithm := algorithm)
          (k := k) (hContinueStrict k hk)
      have hpotential_eq :
          oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
            Real.log (Matrix.det (algorithm.shape (k + 1)) / Matrix.det (algorithm.shape k)) := by
        calc
          oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
              Real.log
                (Matrix.det
                    (oneSidedRoundingUpdatedMatrix G g (oneSidedRoundingAlphaStar G g)) /
                  Matrix.det G.1) := by
                    simpa [r] using
                      oneSidedRoundingPotential_eq_log_det_ratio G g (by simpa [r] using hr0) hα
          _ =
              Real.log
                (Matrix.det (algorithm.shape (k + 1)) / Matrix.det (algorithm.shape k)) := by
                  rw [← hshape]
                  simp [G, GeneralConvexRoundingAlgorithm.currentShape]
      have hlog_div :
          Real.log (Matrix.det (algorithm.shape (k + 1)) / Matrix.det (algorithm.shape k)) =
            Real.log (Matrix.det (algorithm.shape (k + 1))) -
              Real.log (Matrix.det (algorithm.shape k)) := by
        rw [Real.log_div ((algorithm.shape_posDef (k + 1)).det_pos.ne')
          ((algorithm.shape_posDef k).det_pos.ne')]
      -- In dimension `n ≥ 2`, bridge the one-step matrix update to Lemma 7.5's potential bound.
      calc
        c ≤
            (2 * (algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ)) /
              ((1 + algorithm.oneSidedRoundingSigma k) *
                (2 + algorithm.oneSidedRoundingSigma k)) := huniform_rational
        _ ≤ oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := hpotential_lower
        _ =
            Real.log (Matrix.det (algorithm.shape (k + 1)) / Matrix.det (algorithm.shape k)) :=
              hpotential_eq
        _ =
            Real.log (Matrix.det (algorithm.shape (k + 1))) -
              Real.log (Matrix.det (algorithm.shape k)) := hlog_div
  have hlower := logdet_growth_lower_bound_upto algorithm huniform
  have hc_pos : 0 < c := by
    dsimp [c]
    have hden_pos : 0 < (1 + 2 * gamma) * (2 + gamma) := by
      nlinarith [algorithm.gamma_one_lt]
    exact div_pos (by
      have hgamma_sub_pos : 0 < gamma - 1 := by
        linarith [algorithm.gamma_one_lt]
      positivity) hden_pos
  have hbudget : c * (T : ℝ) ≤ 2 * (n : ℝ) * Real.log R := by
    linarith
  have hdiv :
      (T : ℝ) ≤ (2 * (n : ℝ) * Real.log R) / c := by
    exact (le_div_iff₀ hc_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget)
  have hcoeff :
      (2 * (n : ℝ) * Real.log R) / c =
        ((1 + 2 * gamma) * (2 + gamma)) / (2 * (gamma - 1) ^ (2 : ℕ)) *
          (n : ℝ) * Real.log R := by
    dsimp [c]
    have hgamma_sub_ne : gamma - 1 ≠ 0 := by
      linarith [algorithm.gamma_one_lt]
    have hden_ne : (1 + 2 * gamma) * (2 + gamma) ≠ 0 := by
      nlinarith [algorithm.gamma_one_lt]
    field_simp [hgamma_sub_ne, hden_ne]
    ring
  rw [hcoeff] at hdiv
  exact hdiv

end IterationBounds

end GeneralConvexRoundingAlgorithm

end
