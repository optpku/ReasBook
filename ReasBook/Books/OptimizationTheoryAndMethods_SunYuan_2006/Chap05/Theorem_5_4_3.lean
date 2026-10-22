/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_28
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_25
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section

open Filter

section QuasiNewtonSecantErrorRatio

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quasi-Newton secant-error ratio
`‖(B k - fderiv ℝ F xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖`. -/
def quasiNewtonSecantErrorRatio
    (F : E → E)
    (xStar : E)
    (B : ℕ → E →L[ℝ] E)
    (x : ℕ → E) : ℕ → ℝ :=
  fun k ↦
    ‖(B k - fderiv ℝ F xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖

/-- Evaluating `quasiNewtonSecantErrorRatio F xStar B x` at `k` returns the textbook secant
error quotient. -/
theorem quasiNewtonSecantErrorRatio_apply
    (F : E → E)
    (xStar : E)
    (B : ℕ → E →L[ℝ] E)
    (x : ℕ → E)
    (k : ℕ) :
    quasiNewtonSecantErrorRatio F xStar B x k =
      ‖(B k - fderiv ℝ F xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖ :=
  rfl

end QuasiNewtonSecantErrorRatio

section Chapter05Theorem543

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * primary domain: convergence rates of sequences in normed spaces.
-- * core/canonical owners sampled for this file: `qErrorRatio` and
--   `HasQSuperlinearConvergenceTo` from `Chapter01.Definition_1_5_extra_1`,
--   `HasSuperlinearConvergenceTo` from `Chapter03.Theorem_3_4_4`, mathlib's
--   `Asymptotics.IsLittleO` / `=o` API, `HasFDerivAt` / `fderiv`, and
--   `ContinuousLinearMap.IsInvertible` with `.inverse`.
-- * source/core/bridge triage: the only new source-facing owner here is the secant-error ratio
--   `(5.4.4)`; the superlinear convergence notion itself is already owned upstream, and the
--   theorem below is a Chapter 5 bridge from that canonical owner to the secant-error criterion.

/-- Helper for Chapter05 Theorem 5.4.3: once a quasi-Newton iterate hits `hF.xStar`, every later
iterate remains equal to `hF.xStar`. -/
lemma tailEq_xStar_of_hit_xStar
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (B : ℕ → Point →L[ℝ] Point)
    (x : ℕ → Point)
    (h_update : ∀ k : ℕ, x (k + 1) = x k - (B k).inverse (F (x k)))
    {k0 : ℕ}
    (hk0 : x k0 = hF.xStar) :
    ∀ m : ℕ, x (k0 + m) = hF.xStar := by
  intro m
  induction m with
  | zero =>
      simpa using hk0
  | succ m hm =>
      -- The fixed-point equation at `xStar` makes the next quasi-Newton update trivial.
      simpa [Nat.add_assoc, hm, hF.map_xStar] using h_update (k0 + m)

/-- Helper for Chapter05 Theorem 5.4.3: the Chapter 5 derivative deviation hypothesis controls
the linearization remainder between two domain points by their current errors and step length. -/
lemma linearizationRemainder_le_errorControl
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {u v : Point}
    (hu : u ∈ D)
    (hv : v ∈ D) :
    ‖F u - F v - (fderiv ℝ F hF.xStar) (u - v)‖ ≤
      max hF.gamma 0 * (‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖) * ‖u - v‖ := by
  let γ0 : ℝ := max hF.gamma 0
  have hGateaux :
      ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D F z (fderiv ℝ F z) := by
    intro z hz e
    simpa [fderivWithin_of_isOpen hF.open_domain hz] using
      ((hF.contDiffOn.differentiableOn_one z hz).hasFDerivWithinAt.hasLineDerivWithinAt e)
  have hsSup_le :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F hF.xStar‖ ≤
          γ0 * (‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖) := by
    intro t ht
    have hseg_mem : v + t • (u - v) ∈ D :=
      hF.convex_domain.add_smul_sub_mem hv hu ht
    have hdev :
        ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F hF.xStar‖ ≤
          hF.gamma * ‖(v + t • (u - v)) - hF.xStar‖ :=
      hF.lipschitz_fderiv _ hseg_mem
    have ht_abs_le : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    have hsegment_dist :
        ‖(v + t • (u - v)) - hF.xStar‖ ≤
          ‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖ := by
      calc
        ‖(v + t • (u - v)) - hF.xStar‖
            ≤ ‖v - hF.xStar‖ + ‖t • (u - v)‖ := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                norm_add_le (v - hF.xStar) (t • (u - v))
        _ = ‖v - hF.xStar‖ + |t| * ‖u - v‖ := by simp [norm_smul]
        _ ≤ ‖v - hF.xStar‖ + ‖u - v‖ := by
              have hmul_le : |t| * ‖u - v‖ ≤ ‖u - v‖ := by
                nlinarith [norm_nonneg (u - v)]
              linarith
        _ ≤ ‖v - hF.xStar‖ + (‖u - hF.xStar‖ + ‖v - hF.xStar‖) := by
              gcongr
              have huv :
                  u - v = (u - hF.xStar) - (v - hF.xStar) := by
                abel
              rw [huv]
              exact norm_sub_le _ _
        _ = ‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖ := by ring
    calc
      ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F hF.xStar‖
          ≤ hF.gamma * ‖(v + t • (u - v)) - hF.xStar‖ := hdev
      _ ≤ γ0 * ‖(v + t • (u - v)) - hF.xStar‖ := by
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ γ0 * (‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖) := by
            gcongr
  -- Plug the segmentwise derivative bound into the Chapter 1 Gateaux-derivative estimate.
  exact norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
    (F := F) (F' := fun z ↦ fderiv ℝ F z) (x := hF.xStar) (y := u) (z := v)
    (C := γ0 * (‖u - hF.xStar‖ + 2 * ‖v - hF.xStar‖))
    hF.convex_domain hGateaux hsSup_le hu hv

/-- Helper for Chapter05 Theorem 5.4.3: the quasi-Newton secant defect is the linearization
remainder minus the residual `F (x (k + 1))`. -/
lemma secantErrorDecomposition
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (B : ℕ → Point →L[ℝ] Point)
    (x : ℕ → Point)
    (hB_invertible : ∀ k : ℕ, (B k).IsInvertible)
    (h_update : ∀ k : ℕ, x (k + 1) = x k - (B k).inverse (F (x k)))
    (k : ℕ) :
    (B k - fderiv ℝ F hF.xStar) (x (k + 1) - x k) =
      (F (x (k + 1)) - F (x k) - (fderiv ℝ F hF.xStar) (x (k + 1) - x k)) -
        F (x (k + 1)) := by
  -- Rewrite the step by the quasi-Newton update, then isolate the residual term.
  have hBapply :
      (B k) ((B k).inverse (F (x k))) = F (x k) := by
    simpa using (hB_invertible k).self_apply_inverse (F (x k))
  calc
    (B k - fderiv ℝ F hF.xStar) (x (k + 1) - x k)
        = (B k) (x (k + 1) - x k) - (fderiv ℝ F hF.xStar) (x (k + 1) - x k) := by
            rfl
    _ = -F (x k) - (fderiv ℝ F hF.xStar) (x (k + 1) - x k) := by
          rw [h_update]
          have hstep :
              x k - (B k).inverse (F (x k)) - x k = -((B k).inverse (F (x k))) := by
            abel
          rw [hstep, ContinuousLinearMap.map_neg, hBapply]
    _ =
        (F (x (k + 1)) - F (x k) - (fderiv ℝ F hF.xStar) (x (k + 1) - x k)) -
          F (x (k + 1)) := by
          abel

/-- Helper for Chapter05 Theorem 5.4.3: the normalized first-order linearization remainder along
the quasi-Newton iterates tends to `0`. -/
lemma normalizedLinearizationRemainder_tendstoZero
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (x : ℕ → Point)
    (h_iterates_mem : ∀ k : ℕ, x k ∈ D)
    (hx : Tendsto x atTop (nhds hF.xStar)) :
    Tendsto
      (fun k ↦
        ‖F (x (k + 1)) - F (x k) -
            (fderiv ℝ F hF.xStar) (x (k + 1) - x k)‖ /
          ‖x (k + 1) - x k‖)
      atTop
      (nhds 0) := by
  let γ0 : ℝ := max hF.gamma 0
  have hγ0_nonneg : 0 ≤ γ0 := by
    simp [γ0]
  have hErrTendsto :
      Tendsto (fun k ↦ ‖x k - hF.xStar‖) atTop (nhds 0) := by
    -- The iterate errors are the norms of the translated sequence converging to `0`.
    have hSubTendsto :
        Tendsto (fun k ↦ x k - hF.xStar) atTop (nhds (hF.xStar - hF.xStar)) := by
      exact hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ hF.xStar) atTop (nhds hF.xStar))
    simpa using hSubTendsto.norm
  have hErrNextTendsto :
      Tendsto (fun k ↦ ‖x (k + 1) - hF.xStar‖) atTop (nhds 0) := by
    convert hErrTendsto.comp (tendsto_add_atTop_nat 1) using 1
    ext k
    simp [Function.comp]
  have hTwoErrTendsto :
      Tendsto (fun k ↦ (2 : ℝ) * ‖x k - hF.xStar‖) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2)).mul hErrTendsto
  have hMajorTendsto :
      Tendsto
        (fun k ↦ γ0 * (‖x (k + 1) - hF.xStar‖ + 2 * ‖x k - hF.xStar‖))
        atTop
        (nhds 0) := by
    -- The explicit error majorant vanishes because both current and next errors vanish.
    simpa [two_mul, γ0, mul_add, mul_assoc, add_comm, add_left_comm, add_assoc] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ γ0) atTop (nhds γ0)).mul (hErrNextTendsto.add hTwoErrTendsto)
  have hNonneg :
      ∀ᶠ k in atTop,
        0 ≤
          ‖F (x (k + 1)) - F (x k) -
              (fderiv ℝ F hF.xStar) (x (k + 1) - x k)‖ /
            ‖x (k + 1) - x k‖ := by
    exact Eventually.of_forall fun k ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hBound :
      ∀ᶠ k in atTop,
        ‖F (x (k + 1)) - F (x k) -
            (fderiv ℝ F hF.xStar) (x (k + 1) - x k)‖ /
            ‖x (k + 1) - x k‖ ≤
          γ0 * (‖x (k + 1) - hF.xStar‖ + 2 * ‖x k - hF.xStar‖) := by
    refine Eventually.of_forall ?_
    intro k
    by_cases hstep : x (k + 1) = x k
    · -- If the step vanishes, the normalized remainder is definitionally zero.
      have hnonneg :
          0 ≤ γ0 * (‖x k - hF.xStar‖ + 2 * ‖x k - hF.xStar‖) := by
        positivity
      simpa [hstep, γ0] using hnonneg
    · have hstep_pos : 0 < ‖x (k + 1) - x k‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hstep)
      -- Otherwise divide the pointwise remainder estimate by the positive step norm.
      exact
        (div_le_iff₀ hstep_pos).2 <|
          linearizationRemainder_le_errorControl F hF
            (hu := h_iterates_mem (k + 1)) (hv := h_iterates_mem k)
  exact squeeze_zero' hNonneg hBound hMajorTendsto

/-- Helper for Chapter05 Theorem 5.4.3: near `hF.xStar`, the residual norm `‖F y‖` is bounded
above and below by positive multiples of the error norm `‖y - hF.xStar‖`. -/
lemma normImageNearRoot_bounds
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ε cLower cUpper : ℝ,
      0 < ε ∧
      0 < cLower ∧
      0 < cUpper ∧
      ∀ ⦃y : Point⦄, y ∈ D → ‖y - hF.xStar‖ ≤ ε →
        cLower * ‖y - hF.xStar‖ ≤ ‖F y‖ ∧
          ‖F y‖ ≤ cUpper * ‖y - hF.xStar‖ := by
  rcases hF.fderiv_isInvertible with ⟨A, hA⟩
  rcases A.subsingleton_or_norm_symm_pos with hsub | hsymm_pos
  · refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one, ?_⟩
    intro y hy hyε
    -- In the subsingleton branch, every point is `xStar`, so both estimates are trivial.
    have hyx : y = hF.xStar := hsub.elim y hF.xStar
    subst hyx
    simpa [hF.map_xStar]
  · let γ0 : ℝ := max hF.gamma 0
    let μ : ℝ := ‖(A.symm : Point →L[ℝ] Point)‖
    let cLower : ℝ := 1 / (2 * μ)
    let ε : ℝ := 1 / (2 * μ * (γ0 + 1))
    let cUpper : ℝ := ‖(A : Point →L[ℝ] Point)‖ + cLower
    have hγ0_nonneg : 0 ≤ γ0 := by
      simp [γ0]
    have hμ_pos : 0 < μ := by
      simpa [μ] using hsymm_pos
    have hcLower_pos : 0 < cLower := by
      dsimp [cLower]
      positivity
    have hε_pos : 0 < ε := by
      dsimp [ε]
      have hγ0_add_one_pos : 0 < γ0 + 1 := by
        linarith
      positivity
    have hcUpper_pos : 0 < cUpper := by
      dsimp [cUpper]
      positivity
    have hγε_le_cLower : γ0 * ε ≤ cLower := by
      have hγ0_add_one_pos : 0 < γ0 + 1 := by
        linarith
      calc
        γ0 * ε = (1 / (2 * μ)) * (γ0 / (γ0 + 1)) := by
          dsimp [ε, cLower, μ]
          field_simp [hμ_pos.ne', hγ0_add_one_pos.ne']
        _ ≤ (1 / (2 * μ)) * 1 := by
          gcongr
          exact (div_le_iff₀ hγ0_add_one_pos).2 (by linarith)
        _ = cLower := by
          dsimp [cLower]
          ring
    refine ⟨ε, cLower, cUpper, hε_pos, hcLower_pos, hcUpper_pos, ?_⟩
    intro y hy hyε
    have herr :
        ‖F y - (A : Point →L[ℝ] Point) (y - hF.xStar)‖ ≤
          γ0 * ‖y - hF.xStar‖ * ‖y - hF.xStar‖ := by
      -- Specialize the linearization remainder estimate at `v = hF.xStar`.
      simpa [γ0, hA, hF.map_xStar, mul_assoc] using
        linearizationRemainder_le_errorControl F hF
          (u := y) (v := hF.xStar) hy hF.xStar_mem
    have herr' :
        ‖F y - (A : Point →L[ℝ] Point) (y - hF.xStar)‖ ≤
          (γ0 * ε) * ‖y - hF.xStar‖ := by
      calc
        ‖F y - (A : Point →L[ℝ] Point) (y - hF.xStar)‖
            ≤ γ0 * ‖y - hF.xStar‖ * ‖y - hF.xStar‖ := herr
        _ ≤ γ0 * ε * ‖y - hF.xStar‖ := by
            gcongr
        _ = (γ0 * ε) * ‖y - hF.xStar‖ := by ring
    have hlinear_lower :
        (1 / μ) * ‖y - hF.xStar‖ ≤ ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ := by
      simpa [μ] using invOpNorm_mul_norm_le_norm_apply A (y - hF.xStar)
    have hlinear_le_image :
        ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ ≤
          ‖F y‖ + (γ0 * ε) * ‖y - hF.xStar‖ := by
      -- Pull the linear term out of `F y` and absorb the remainder by the triangle inequality.
      calc
        ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ =
            ‖F y - (F y - (A : Point →L[ℝ] Point) (y - hF.xStar))‖ := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ ≤ ‖F y‖ + ‖F y - (A : Point →L[ℝ] Point) (y - hF.xStar)‖ := norm_sub_le _ _
        _ ≤ ‖F y‖ + (γ0 * ε) * ‖y - hF.xStar‖ := by
          gcongr
    have hlower_main :
        (1 / μ) * ‖y - hF.xStar‖ ≤ ‖F y‖ + cLower * ‖y - hF.xStar‖ := by
      calc
        (1 / μ) * ‖y - hF.xStar‖ ≤ ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ := hlinear_lower
        _ ≤ ‖F y‖ + (γ0 * ε) * ‖y - hF.xStar‖ := hlinear_le_image
        _ ≤ ‖F y‖ + cLower * ‖y - hF.xStar‖ := by
          gcongr
    have hhalf :
        cLower * ‖y - hF.xStar‖ =
          ((1 / μ) * ‖y - hF.xStar‖) / 2 := by
      dsimp [cLower]
      field_simp [hμ_pos.ne']
    have hlower :
        cLower * ‖y - hF.xStar‖ ≤ ‖F y‖ := by
      rw [hhalf] at hlower_main
      nlinarith [hlower_main, norm_nonneg (F y)]
    have hupper_core :
        ‖F y‖ ≤
          ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ + (γ0 * ε) * ‖y - hF.xStar‖ := by
      -- The same remainder estimate controls the image norm from above.
      calc
        ‖F y‖ =
            ‖(F y - (A : Point →L[ℝ] Point) (y - hF.xStar)) +
                (A : Point →L[ℝ] Point) (y - hF.xStar)‖ := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm]
        _ ≤ ‖F y - (A : Point →L[ℝ] Point) (y - hF.xStar)‖ +
              ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ := norm_add_le _ _
        _ ≤ (γ0 * ε) * ‖y - hF.xStar‖ +
              ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ := by
              gcongr
        _ = ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ +
              (γ0 * ε) * ‖y - hF.xStar‖ := by
              ring
    have hupper :
        ‖F y‖ ≤ cUpper * ‖y - hF.xStar‖ := by
      calc
        ‖F y‖ ≤
            ‖(A : Point →L[ℝ] Point) (y - hF.xStar)‖ + (γ0 * ε) * ‖y - hF.xStar‖ :=
          hupper_core
        _ ≤ ‖(A : Point →L[ℝ] Point)‖ * ‖y - hF.xStar‖ + cLower * ‖y - hF.xStar‖ := by
          gcongr
          · exact (A : Point →L[ℝ] Point).le_opNorm (y - hF.xStar)
        _ = cUpper * ‖y - hF.xStar‖ := by
          dsimp [cUpper]
          ring
    exact ⟨hlower, hupper⟩

/-- Helper for Chapter05 Theorem 5.4.3: on a tail where no iterate equals `hF.xStar`, the
Chapter 1 `Q`-superlinear ratio tends to `0` exactly when the normalized residual
`‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖` does. -/
lemma residualRatio_tendstoZero_iff_hasQSuperlinear
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (B : ℕ → Point →L[ℝ] Point)
    (x : ℕ → Point)
    (hB_invertible : ∀ k : ℕ, (B k).IsInvertible)
    (h_update : ∀ k : ℕ, x (k + 1) = x k - (B k).inverse (F (x k)))
    (h_iterates_mem : ∀ k : ℕ, x k ∈ D)
    (hx : Tendsto x atTop (nhds hF.xStar))
    (h_ne : ∀ k : ℕ, x k ≠ hF.xStar) :
    HasQSuperlinearConvergenceTo x hF.xStar ↔
      Tendsto (fun k ↦ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) atTop (nhds 0) := by
  rcases normImageNearRoot_bounds F hF with
    ⟨ε, cLower, cUpper, hε_pos, hcLower_pos, hcUpper_pos, hBounds⟩
  have hErrTendsto :
      Tendsto (fun k ↦ ‖x k - hF.xStar‖) atTop (nhds 0) := by
    -- The iterate errors are the norms of the translated sequence converging to `0`.
    have hSubTendsto :
        Tendsto (fun k ↦ x k - hF.xStar) atTop (nhds (hF.xStar - hF.xStar)) := by
      exact hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ hF.xStar) atTop (nhds hF.xStar))
    simpa using hSubTendsto.norm
  have hErrNextTendsto :
      Tendsto (fun k ↦ ‖x (k + 1) - hF.xStar‖) atTop (nhds 0) := by
    convert hErrTendsto.comp (tendsto_add_atTop_nat 1) using 1
    ext k
    simp [Function.comp]
  constructor
  · intro hq
    have hStepRatio :
        Tendsto
          (fun k ↦ ‖x (k + 1) - x k‖ / ‖x k - hF.xStar‖)
          atTop
          (nhds 1) :=
      hasQSuperlinearConvergenceTo_stepRatio_tendsto_one
        x hF.xStar hq (Eventually.of_forall h_ne)
    have hNearNext :
        ∀ᶠ k in atTop, ‖x (k + 1) - hF.xStar‖ < ε := by
      exact hErrNextTendsto.eventually (Iio_mem_nhds hε_pos)
    have hHalfStep :
        ∀ᶠ k in atTop, (1 / 2 : ℝ) < ‖x (k + 1) - x k‖ / ‖x k - hF.xStar‖ := by
      exact hStepRatio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hResidualNonneg :
        ∀ᶠ k in atTop, 0 ≤ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ := by
      exact Eventually.of_forall fun k ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hResidualBound :
        ∀ᶠ k in atTop,
          ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ ≤
            (2 * cUpper) * qErrorRatio x hF.xStar 1 k := by
      filter_upwards [hNearNext, hHalfStep] with k hkNear hkHalf
      have hkErrPos : 0 < ‖x k - hF.xStar‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (h_ne k))
      have hkStepLower :
          (1 / 2 : ℝ) * ‖x k - hF.xStar‖ < ‖x (k + 1) - x k‖ := by
        exact (lt_div_iff₀ hkErrPos).1 hkHalf
      have hkStepPos : 0 < ‖x (k + 1) - x k‖ := by
        nlinarith [hkStepLower]
      have hkCurrentOverStep :
          ‖x k - hF.xStar‖ / ‖x (k + 1) - x k‖ ≤ 2 := by
        refine (div_le_iff₀ hkStepPos).2 ?_
        nlinarith [hkStepLower.le]
      have hkUpperImage :
          ‖F (x (k + 1))‖ ≤ cUpper * ‖x (k + 1) - hF.xStar‖ :=
        (hBounds (y := x (k + 1)) (h_iterates_mem (k + 1)) (le_of_lt hkNear)).2
      have hkQEq :
          qErrorRatio x hF.xStar 1 k =
            ‖x (k + 1) - hF.xStar‖ / ‖x k - hF.xStar‖ := by
        simp [qErrorRatio]
      calc
        ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖
            ≤ (cUpper * ‖x (k + 1) - hF.xStar‖) / ‖x (k + 1) - x k‖ := by
              exact div_le_div_of_nonneg_right hkUpperImage (le_of_lt hkStepPos)
        _ = cUpper * (‖x (k + 1) - hF.xStar‖ / ‖x (k + 1) - x k‖) := by
              rw [mul_div_assoc]
        _ = cUpper *
              (qErrorRatio x hF.xStar 1 k *
                (‖x k - hF.xStar‖ / ‖x (k + 1) - x k‖)) := by
              rw [hkQEq]
              field_simp [hkErrPos.ne', hkStepPos.ne']
        _ ≤ cUpper * (qErrorRatio x hF.xStar 1 k * 2) := by
              gcongr
              · rw [hkQEq]
                exact div_nonneg (norm_nonneg _) (norm_nonneg _)
        _ = (2 * cUpper) * qErrorRatio x hF.xStar 1 k := by
              ring
    have hMajorTendsto :
        Tendsto (fun k ↦ (2 * cUpper) * qErrorRatio x hF.xStar 1 k) atTop (nhds 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 2 * cUpper) atTop (nhds (2 * cUpper))).mul
          hq.ratio_tendsto
    exact squeeze_zero' hResidualNonneg hResidualBound hMajorTendsto
  · intro hResidual
    have hNearCurrent :
        ∀ᶠ k in atTop, ‖x k - hF.xStar‖ < ε := by
      exact hErrTendsto.eventually (Iio_mem_nhds hε_pos)
    have hNearNext :
        ∀ᶠ k in atTop, ‖x (k + 1) - hF.xStar‖ < ε := by
      exact hErrNextTendsto.eventually (Iio_mem_nhds hε_pos)
    have hResidualSmall :
        ∀ᶠ k in atTop, ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ < cLower / 2 := by
      exact hResidual.eventually (Iio_mem_nhds (by positivity : 0 < cLower / 2))
    have hRatioNonneg :
        ∀ᶠ k in atTop, 0 ≤ qErrorRatio x hF.xStar 1 k := by
      exact Eventually.of_forall fun k ↦ by
        simp [qErrorRatio]
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hRatioBound :
        ∀ᶠ k in atTop,
          qErrorRatio x hF.xStar 1 k ≤
            (2 / cLower) * (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) := by
      filter_upwards [hNearCurrent, hNearNext, hResidualSmall] with k hkNear hkNearNext hkSmall
      have hkErrPos : 0 < ‖x k - hF.xStar‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (h_ne k))
      have hkLowerCurrent :
          cLower * ‖x k - hF.xStar‖ ≤ ‖F (x k)‖ :=
        (hBounds (y := x k) (h_iterates_mem k) (le_of_lt hkNear)).1
      have hkFCurrentNe : F (x k) ≠ 0 := by
        intro hkFZero
        have hkMulPos : 0 < cLower * ‖x k - hF.xStar‖ := mul_pos hcLower_pos hkErrPos
        have : cLower * ‖x k - hF.xStar‖ ≤ 0 := by
          simpa [hkFZero] using hkLowerCurrent
        linarith
      have hkStepNe : x (k + 1) ≠ x k := by
        intro hkStep
        have hStepEq :
            x (k + 1) - x k = -((B k).inverse (F (x k))) := by
          rw [h_update]
          abel
        have hInvZero : (B k).inverse (F (x k)) = 0 := by
          have : 0 = -((B k).inverse (F (x k))) := by
            simpa [hkStep] using hStepEq
          simpa using this
        have hkFZero : F (x k) = 0 := by
          simpa [(hB_invertible k).self_apply_inverse] using congrArg (B k) hInvZero
        exact hkFCurrentNe hkFZero
      have hkStepPos : 0 < ‖x (k + 1) - x k‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hkStepNe)
      have hkResidualLe :
          ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ ≤ cLower / 2 := le_of_lt hkSmall
      have hkLowerNext :
          cLower * ‖x (k + 1) - hF.xStar‖ ≤ ‖F (x (k + 1))‖ :=
        (hBounds (y := x (k + 1)) (h_iterates_mem (k + 1)) (le_of_lt hkNearNext)).1
      have hkStepLeSum :
          ‖x (k + 1) - x k‖ ≤
            ‖x (k + 1) - hF.xStar‖ + ‖x k - hF.xStar‖ := by
        have hstepRewrite :
            x (k + 1) - x k = (x (k + 1) - hF.xStar) - (x k - hF.xStar) := by
          abel
        rw [hstepRewrite]
        exact norm_sub_le _ _
      have hkMain :
          cLower * ‖x (k + 1) - hF.xStar‖ ≤
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) *
              (‖x (k + 1) - hF.xStar‖ + ‖x k - hF.xStar‖) := by
        calc
          cLower * ‖x (k + 1) - hF.xStar‖ ≤ ‖F (x (k + 1))‖ := hkLowerNext
          _ = (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) * ‖x (k + 1) - x k‖ := by
                field_simp [hkStepPos.ne']
          _ ≤ (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) *
                (‖x (k + 1) - hF.xStar‖ + ‖x k - hF.xStar‖) := by
                gcongr
      have hkResidualNonneg :
          0 ≤ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ := by
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hkScaled :
          (cLower / 2) * ‖x (k + 1) - hF.xStar‖ ≤
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) * ‖x k - hF.xStar‖ := by
        have hkExpand :
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) *
                (‖x (k + 1) - hF.xStar‖ + ‖x k - hF.xStar‖) =
              (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) * ‖x (k + 1) - hF.xStar‖ +
                (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) * ‖x k - hF.xStar‖ := by
          ring
        rw [hkExpand] at hkMain
        have hkAbsorb :
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) * ‖x (k + 1) - hF.xStar‖ ≤
              (cLower / 2) * ‖x (k + 1) - hF.xStar‖ := by
          gcongr
        nlinarith
      have hkQEq :
          qErrorRatio x hF.xStar 1 k =
            ‖x (k + 1) - hF.xStar‖ / ‖x k - hF.xStar‖ := by
        simp [qErrorRatio]
      have hkRatioScaled :
          (cLower / 2) * qErrorRatio x hF.xStar 1 k ≤
            ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ := by
        rw [hkQEq]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (div_le_iff₀ hkErrPos).2 hkScaled
      have hkRatioScaled' :
          qErrorRatio x hF.xStar 1 k * (cLower / 2) ≤
            ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ := by
        simpa [mul_comm] using hkRatioScaled
      have hkDiv :
          qErrorRatio x hF.xStar 1 k ≤
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) / (cLower / 2) :=
        (le_div_iff₀ (by positivity : 0 < cLower / 2)).2 hkRatioScaled'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hkDiv
    have hMajorTendsto :
        Tendsto
          (fun k ↦ (2 / cLower) * (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖))
          atTop
          (nhds 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 2 / cLower) atTop (nhds (2 / cLower))).mul
          hResidual
    refine ⟨hx, ?_⟩
    exact squeeze_zero' hRatioNonneg hRatioBound hMajorTendsto

/-- Helper for Chapter05 Theorem 5.4.3: after normalizing by the step length, the secant-error
criterion is equivalent to the residual criterion because the linearization remainder already
tends to `0`. -/
lemma secantRatio_tendstoZero_iff_residualRatio_tendstoZero
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (B : ℕ → Point →L[ℝ] Point)
    (x : ℕ → Point)
    (hB_invertible : ∀ k : ℕ, (B k).IsInvertible)
    (h_update : ∀ k : ℕ, x (k + 1) = x k - (B k).inverse (F (x k)))
    (h_iterates_mem : ∀ k : ℕ, x k ∈ D)
    (hx : Tendsto x atTop (nhds hF.xStar)) :
    Tendsto (quasiNewtonSecantErrorRatio F hF.xStar B x) atTop (nhds 0) ↔
      Tendsto (fun k ↦ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) atTop (nhds 0) := by
  let remainderRatio : ℕ → ℝ := fun k ↦
    ‖F (x (k + 1)) - F (x k) -
        (fderiv ℝ F hF.xStar) (x (k + 1) - x k)‖ /
      ‖x (k + 1) - x k‖
  have hRemainder :
      Tendsto remainderRatio atTop (nhds 0) := by
    simpa [remainderRatio] using
      normalizedLinearizationRemainder_tendstoZero F hF x h_iterates_mem hx
  constructor
  · intro hSecant
    have hResidualNonneg :
        ∀ᶠ k in atTop, 0 ≤ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ := by
      exact Eventually.of_forall fun k ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hResidualBound :
        ∀ᶠ k in atTop,
          ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ ≤
            quasiNewtonSecantErrorRatio F hF.xStar B x k + remainderRatio k := by
      refine Eventually.of_forall ?_
      intro k
      by_cases hStep : x (k + 1) = x k
      · -- On a zero step, all three normalized quantities are definitionally zero.
        simp [quasiNewtonSecantErrorRatio_apply, remainderRatio, hStep]
      · have hStepPos : 0 < ‖x (k + 1) - x k‖ := by
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hStep)
        let secantVec : Point := (B k - fderiv ℝ F hF.xStar) (x (k + 1) - x k)
        let remainderVec : Point :=
          F (x (k + 1)) - F (x k) -
            (fderiv ℝ F hF.xStar) (x (k + 1) - x k)
        have hDecomp :
            secantVec = remainderVec - F (x (k + 1)) := by
          simpa [secantVec, remainderVec] using
            secantErrorDecomposition F hF B x hB_invertible h_update k
        have hResidualEq :
            remainderVec - secantVec = F (x (k + 1)) := by
          calc
            remainderVec - secantVec = remainderVec - (remainderVec - F (x (k + 1))) := by
              rw [hDecomp]
            _ = F (x (k + 1)) := by
              abel
        have hNumLe :
            ‖F (x (k + 1))‖ ≤ ‖secantVec‖ + ‖remainderVec‖ := by
          calc
            ‖F (x (k + 1))‖ = ‖remainderVec - secantVec‖ := by
              rw [← hResidualEq]
          _ ≤ ‖remainderVec‖ + ‖secantVec‖ := norm_sub_le _ _
          _ = ‖secantVec‖ + ‖remainderVec‖ := by ring
        have hDivLe :
            ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖ ≤
              (‖secantVec‖ + ‖remainderVec‖) / ‖x (k + 1) - x k‖ :=
          div_le_div_of_nonneg_right hNumLe (le_of_lt hStepPos)
        simpa [quasiNewtonSecantErrorRatio_apply, remainderRatio, secantVec, remainderVec,
          add_div] using hDivLe
    have hMajorTendsto :
        Tendsto (fun k ↦ quasiNewtonSecantErrorRatio F hF.xStar B x k + remainderRatio k)
          atTop (nhds 0) := by
      simpa [remainderRatio] using hSecant.add hRemainder
    exact squeeze_zero' hResidualNonneg hResidualBound hMajorTendsto
  · intro hResidual
    have hSecantNonneg :
        ∀ᶠ k in atTop, 0 ≤ quasiNewtonSecantErrorRatio F hF.xStar B x k := by
      exact Eventually.of_forall fun k ↦ by
        rw [quasiNewtonSecantErrorRatio_apply]
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hSecantBound :
        ∀ᶠ k in atTop,
          quasiNewtonSecantErrorRatio F hF.xStar B x k ≤
            (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) + remainderRatio k := by
      refine Eventually.of_forall ?_
      intro k
      by_cases hStep : x (k + 1) = x k
      · -- The zero-step branch again collapses all normalized quantities to `0`.
        simp [quasiNewtonSecantErrorRatio_apply, remainderRatio, hStep]
      · have hStepPos : 0 < ‖x (k + 1) - x k‖ := by
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hStep)
        let secantVec : Point := (B k - fderiv ℝ F hF.xStar) (x (k + 1) - x k)
        let remainderVec : Point :=
          F (x (k + 1)) - F (x k) -
            (fderiv ℝ F hF.xStar) (x (k + 1) - x k)
        have hDecomp :
            secantVec = remainderVec - F (x (k + 1)) := by
          simpa [secantVec, remainderVec] using
            secantErrorDecomposition F hF B x hB_invertible h_update k
        have hNumLe :
            ‖secantVec‖ ≤ ‖F (x (k + 1))‖ + ‖remainderVec‖ := by
          calc
            ‖secantVec‖ = ‖remainderVec - F (x (k + 1))‖ := by
              rw [hDecomp]
            _ ≤ ‖remainderVec‖ + ‖F (x (k + 1))‖ := norm_sub_le _ _
            _ = ‖F (x (k + 1))‖ + ‖remainderVec‖ := by ring
        have hDivLe :
            ‖secantVec‖ / ‖x (k + 1) - x k‖ ≤
              (‖F (x (k + 1))‖ + ‖remainderVec‖) / ‖x (k + 1) - x k‖ :=
          div_le_div_of_nonneg_right hNumLe (le_of_lt hStepPos)
        simpa [quasiNewtonSecantErrorRatio_apply, remainderRatio, secantVec, remainderVec,
          add_div] using hDivLe
    have hMajorTendsto :
        Tendsto (fun k ↦ (‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) + remainderRatio k)
          atTop (nhds 0) := by
      simpa [remainderRatio] using hResidual.add hRemainder
    exact squeeze_zero' hSecantNonneg hSecantBound hMajorTendsto

/-- Chapter05 Theorem 5.4.3: let `F : ℝ^n → ℝ^n` satisfy
`HasQuasiNewtonLocalConvergenceAssumptions D F`. Let `B k` be a sequence of nonsingular linear
maps, written with their canonical inverses `(B k).inverse`, and let
`x (k + 1) = x k - (B k).inverse (F (x k))` be a quasi-Newton iterate sequence that stays in `D`
and converges to `hF.xStar`. Then `x` converges to `hF.xStar` `Q`-superlinearly, in the
canonical Chapter 1 sense, exactly when the secant-error ratio
`‖(B k - fderiv ℝ F hF.xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖` tends to `0`. -/
-- TODO: split into the hit-root and no-hit branches; on the no-hit branch compare the secant
-- ratio with the residual ratio via `secantErrorDecomposition` and
-- `normalizedLinearizationRemainder_tendstoZero`, then use local inverse-derivative bounds near
-- `hF.xStar` to convert the residual ratio to the Chapter 1 `Q`-superlinear ratio.
theorem quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero
    {D : Set Point}
    (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (B : ℕ → Point →L[ℝ] Point)
    (x : ℕ → Point)
    (hB_invertible : ∀ k : ℕ, (B k).IsInvertible)
    (h_update : ∀ k : ℕ, x (k + 1) = x k - (B k).inverse (F (x k)))
    (h_iterates_mem : ∀ k : ℕ, x k ∈ D)
    (hx : Tendsto x atTop (nhds hF.xStar)) :
    HasQSuperlinearConvergenceTo x hF.xStar ↔
      Tendsto (quasiNewtonSecantErrorRatio F hF.xStar B x) atTop (nhds 0) := by
  by_cases hHit : ∃ k0 : ℕ, x k0 = hF.xStar
  · rcases hHit with ⟨k0, hk0⟩
    have hTailConst : ∀ m : ℕ, x (k0 + m) = hF.xStar :=
      tailEq_xStar_of_hit_xStar F hF B x h_update hk0
    have hRatioEventuallyZero :
        ∀ᶠ k in atTop, qErrorRatio x hF.xStar 1 k = 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨k0, ?_⟩
      intro k hk
      rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
      -- Once the run is constant at `xStar`, the Chapter 1 ratio is identically zero.
      have hm : x (k0 + m) = hF.xStar := hTailConst m
      have hmSucc : x (k0 + m + 1) = hF.xStar := by
        simpa [Nat.add_assoc] using hTailConst (m + 1)
      simp [qErrorRatio_apply, hm, hmSucc]
    have hSecantEventuallyZero :
        ∀ᶠ k in atTop, quasiNewtonSecantErrorRatio F hF.xStar B x k = 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨k0, ?_⟩
      intro k hk
      rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
      -- The same constant-tail argument also kills the secant-error ratio.
      have hm : x (k0 + m) = hF.xStar := hTailConst m
      have hmSucc : x (k0 + m + 1) = hF.xStar := by
        simpa [Nat.add_assoc] using hTailConst (m + 1)
      simp [quasiNewtonSecantErrorRatio_apply, hm, hmSucc]
    have hRatioEventuallyEq :
        qErrorRatio x hF.xStar 1 =ᶠ[atTop] fun _ : ℕ ↦ 0 := by
      filter_upwards [hRatioEventuallyZero] with k hk
      exact hk
    have hSecantEventuallyEq :
        quasiNewtonSecantErrorRatio F hF.xStar B x =ᶠ[atTop] fun _ : ℕ ↦ 0 := by
      filter_upwards [hSecantEventuallyZero] with k hk
      exact hk
    have hRatioTendsto :
        Tendsto (qErrorRatio x hF.xStar 1) atTop (nhds 0) := by
      exact Tendsto.congr' hRatioEventuallyEq.symm tendsto_const_nhds
    have hSecantTendsto :
        Tendsto (quasiNewtonSecantErrorRatio F hF.xStar B x) atTop (nhds 0) := by
      exact Tendsto.congr' hSecantEventuallyEq.symm tendsto_const_nhds
    constructor
    · intro _
      exact hSecantTendsto
    · intro _
      exact ⟨hx, hRatioTendsto⟩
  · have h_ne : ∀ k : ℕ, x k ≠ hF.xStar := by
      intro k hk
      exact hHit ⟨k, hk⟩
    -- Route correction: after removing the obsolete Chapter 3 bridge, the proof stays entirely in
    -- the Chapter 1 `HasQSuperlinearConvergenceTo` API by comparing secant, residual, and
    -- `Q`-error ratios on the no-hit tail.
    calc
      HasQSuperlinearConvergenceTo x hF.xStar
          ↔ Tendsto (fun k ↦ ‖F (x (k + 1))‖ / ‖x (k + 1) - x k‖) atTop (nhds 0) := by
            exact residualRatio_tendstoZero_iff_hasQSuperlinear
              F hF B x hB_invertible h_update h_iterates_mem hx h_ne
      _ ↔ Tendsto (quasiNewtonSecantErrorRatio F hF.xStar B x) atTop (nhds 0) := by
            exact (secantRatio_tendstoZero_iff_residualRatio_tendstoZero
              F hF B x hB_invertible h_update h_iterates_mem hx).symm

end Chapter05Theorem543
