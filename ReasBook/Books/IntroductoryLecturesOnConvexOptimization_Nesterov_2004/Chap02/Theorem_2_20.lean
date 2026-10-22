/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_19

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex optimal-method objective-gap rates on a real Hilbert space.

Owner declarations sampled before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` owns the optimal-method trajectory together
  with the canonical scalar sequences `αₖ`, `γₖ`, and `λₖ`;
* `OptimalMethodRecurrence.weight_bounds` in `Lemma_2_10` owns the hyperbolic and quadratic
  bounds on the canonical weight `λₖ` for `γ₀ ∈ (μ, 3L + μ]`;
* `OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound` in `Lemma_2_10` owns the scalar
  hyperbolic-versus-quadratic factor comparison on the recurrence side;
* `estimating_sequence_suboptimality_le` in `Theorem_2_19` owns the estimating-sequence
  objective-gap estimate;
* the owner-style summary in `Definition_2_20` identifies whole-space strong convexity,
  `C¹` regularity, and gradient Lipschitzness as the primitive objective data in Chapter 2.

Best owner abstraction: the public object here is the owner method
`method : GeneralOptimalMethodScheme ... (3 * L + μ)`. The explicit hyperbolic and quadratic
right-hand sides are derived by combining the owner suboptimality theorem with the owner weight
bound, so this file states those rates directly rather than keeping parallel local bound
definitions.

Primitive data:
* the objective and its whole-space strong-convexity / smoothness hypotheses;
* a minimizer `xStar`;
* the owner method with `γ₀ = 3L + μ`.

Derived API:
* the explicit quadratic objective-gap estimate;
* the explicit hyperbolic objective-gap estimate;
* the comparison of the two displayed right-hand sides. -/

section OptimalMethodRates

variable {μ L gamma0 : ℝ} {f : E → ℝ}
variable {xStar : E}
variable {x0 : E}

/-- Helper for Theorem 2.20: every owner curvature `γ_k` stays positive. -/
private theorem optimal_method_gamma_pos
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0) :
    ∀ k : ℕ, 0 < method.gamma k := by
  intro k
  induction k with
  | zero =>
      simpa [method.gamma_zero] using method.gamma0_pos
  | succ k hk =>
      -- The owner recurrence preserves the positive `(1 - α_k) γ_k` term, while the `α_k μ`
      -- contribution is nonnegative.
      rw [method.gamma_succ k]
      have hfactor_pos : 0 < 1 - method.alpha k := sub_pos.mpr (method.alpha_mem_Ioo k).2
      have hterm_nonneg : 0 ≤ method.alpha k * μ := by
        exact mul_nonneg (method.alpha_pos k).le method.mu_nonneg
      exact add_pos_of_pos_of_nonneg (mul_pos hfactor_pos hk) hterm_nonneg

/-- Helper for Theorem 2.20: the source estimating-sequence weight `λ_k` agrees with the owner
weight of the optimal-method recurrence. -/
private theorem optimal_method_estimatingWeight_eq_weight
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    estimatingWeight method.alpha k = method.weight k := by
  -- Both weights satisfy the same recursion `λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ`.
  induction k with
  | zero =>
      simp [estimatingWeight]
  | succ k ih =>
      rw [estimatingWeight, method.weight_succ, ih]

/-- Helper for Theorem 2.20: the source curvature recursion for the estimating sequence is exactly
the owner curvature sequence `γ_k`. -/
private theorem optimal_method_estimating_curvature_eq_gamma
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    estimatingSequenceCurvature μ gamma0 method.alpha k = method.gamma k := by
  -- The source and owner curvatures share the same initial value and successor relation.
  induction k with
  | zero =>
      simpa using method.gamma_zero.symm
  | succ k ih =>
      rw [estimatingSequenceCurvature_succ, ih]
      simpa using (method.gamma_succ k).symm

/-- Helper for Theorem 2.20: the source estimating-sequence center recursion agrees with the owner
center sequence `v_k`. -/
private theorem optimal_method_estimating_center_eq_v
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    estimatingSequenceCenter f method.alpha method.y μ gamma0 x0 k = method.v k := by
  -- After matching the source curvatures with `γ_k`, the center update is exactly the owner
  -- `v_{k+1}` recurrence.
  induction k with
  | zero =>
      simpa [method.x_zero] using method.v_zero.symm
  | succ k ih =>
      rw [estimatingSequenceCenter_succ, ih]
      simpa [optimal_method_estimating_curvature_eq_gamma method k,
        optimal_method_estimating_curvature_eq_gamma method (k + 1), method.x_zero] using
        (method.v_succ k).symm

/-- Helper for Theorem 2.20: the owner interpolation formula rewrites the center gap `v_k - y_k`
into the iterate gap `y_k - x_k` with the exact source coefficient. -/
private theorem optimal_method_center_gap_scaled_eq_iterate_gap
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    ((method.alpha k * method.gamma k) / method.gamma (k + 1)) •
        (method.v k - method.y k) =
      method.y k - method k := by
  let A : ℝ := method.alpha k * method.gamma k
  let B : ℝ := method.gamma (k + 1)
  let D : ℝ := method.gamma k + method.alpha k * μ
  have hB_ne : B ≠ 0 := (optimal_method_gamma_pos method (k + 1)).ne'
  have hD_ne : D ≠ 0 := by
    have hD_pos : 0 < D := by
      dsimp [D]
      have hterm_nonneg : 0 ≤ method.alpha k * μ := by
        exact mul_nonneg (method.alpha_pos k).le method.mu_nonneg
      exact add_pos_of_pos_of_nonneg (optimal_method_gamma_pos method k) hterm_nonneg
    exact hD_pos.ne'
  have hcoef : D = A + B := by
    dsimp [A, B, D]
    rw [method.gamma_succ k]
    ring
  have hy_scaled :
      D • method.y k = A • method.v k + B • method k := by
    -- Clear the denominator in the interpolation formula once.
    calc
      D • method.y k
          = D • ((1 / D) • (A • method.v k + B • method k)) := by
              simpa [A, B, D] using congrArg (fun z ↦ D • z) (method.y_eq k)
      _ = A • method.v k + B • method k := by
            rw [smul_smul, one_div, mul_inv_cancel₀ hD_ne, one_smul]
  have hmain :
      B • (method.y k - method k) = A • (method.v k - method.y k) := by
    -- Compare the two affine decompositions of the same interpolation identity and cancel the
    -- common terms.
    calc
      B • (method.y k - method k) = B • method.y k - B • method k := by rw [smul_sub]
      _ = (D • method.y k - A • method.y k) - B • method k := by
            rw [hcoef]
            module
      _ = ((A • method.v k + B • method k) - A • method.y k) - B • method k := by
            rw [hy_scaled]
      _ = A • (method.v k - method.y k) := by
            module
  calc
    ((method.alpha k * method.gamma k) / method.gamma (k + 1)) •
        (method.v k - method.y k)
        = (1 / B) • (A • (method.v k - method.y k)) := by
            rw [smul_smul]
            congr 1
            dsimp [A, B]
            field_simp [hB_ne]
    _ = (1 / B) • (B • (method.y k - method k)) := by
          rw [hmain]
    _ = method.y k - method k := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hB_ne, one_smul]

/-- Helper for Theorem 2.20: every owner estimating function `φ_k` attains the minimum value
`φ_k^*` of its centered quadratic normal form. -/
private theorem optimal_method_estimating_value_isLeast
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    IsLeast
      (Set.range
        (strongConvexEstimatingFunction μ f
          (quadraticallyRegularizedObjective (fun _ ↦ f x0) gamma0 x0)
          method.y method.alpha k))
      (estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k) := by
  have hγ :
      ∀ j, estimatingSequenceCurvature μ gamma0 method.alpha (j + 1) ≠ 0 := by
    intro j
    rw [optimal_method_estimating_curvature_eq_gamma method (j + 1)]
    exact (optimal_method_gamma_pos method (j + 1)).ne'
  -- Re-express `φ_k` as its canonical quadratic and read off the minimum at the center.
  rw [estimatingSequence_eq_canonicalQuadratic
    f method.alpha method.y μ (f x0) gamma0 x0 hγ k]
  rw [optimal_method_estimating_curvature_eq_gamma method k,
    optimal_method_estimating_center_eq_v method k]
  simpa using
    canonical_quadratic_isLeast_value
      (E := E)
      (γ := method.gamma k)
      (c := estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k)
      (v := method.v k)
      (optimal_method_gamma_pos method k)

/-- Helper for Theorem 2.20: the estimating-value recursion takes the exact owner descent form
once the center gap is rewritten through the iterate gap. -/
private theorem optimal_method_estimating_value_succ_eq_descent_form
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (k : ℕ) :
    estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 (k + 1) =
      (1 - method.alpha k) *
          estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
        method.alpha k * f (method.y k) -
        (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
        (1 - method.alpha k) * inner ℝ (∇ f (method.y k)) (method.y k - method k) +
        (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
            (2 * method.alpha k * method.gamma k)) *
          ‖method k - method.y k‖ ^ (2 : ℕ) := by
  have halpha_ne : method.alpha k ≠ 0 := (method.alpha_pos k).ne'
  have hgamma_curr_ne : method.gamma k ≠ 0 := (optimal_method_gamma_pos method k).ne'
  have hgamma_next_ne : method.gamma (k + 1) ≠ 0 := (optimal_method_gamma_pos method (k + 1)).ne'
  have hgradient :
      method.alpha k ^ (2 : ℕ) / (2 * method.gamma (k + 1)) = 1 / (2 * L) := by
    rw [method.gamma_succ_eq_L_mul_sq]
    field_simp [method.L_pos.ne', halpha_ne]
  have hcenter := optimal_method_center_gap_scaled_eq_iterate_gap method k
  have hvy :
      method.v k - method.y k =
        (method.gamma (k + 1) / (method.alpha k * method.gamma k)) •
          (method.y k - method k) := by
    -- Invert the scaled center-gap identity so the quadratic term is written on `‖x_k - y_k‖²`.
    have hs_ne :
        method.alpha k * method.gamma k / method.gamma (k + 1) ≠ 0 := by
      exact div_ne_zero (mul_ne_zero halpha_ne hgamma_curr_ne) hgamma_next_ne
    calc
      method.v k - method.y k
          =
            (1 / (method.alpha k * method.gamma k / method.gamma (k + 1))) •
              (((method.alpha k * method.gamma k) / method.gamma (k + 1)) •
                (method.v k - method.y k)) := by
                  rw [smul_smul, one_div, inv_mul_cancel₀ hs_ne, one_smul]
      _ =
          (1 / (method.alpha k * method.gamma k / method.gamma (k + 1))) •
            (method.y k - method k) := by
              rw [hcenter]
      _ =
          (method.gamma (k + 1) / (method.alpha k * method.gamma k)) •
            (method.y k - method k) := by
              congr 1
              field_simp [halpha_ne, hgamma_curr_ne, hgamma_next_ne]
  have hlinear :
      method.alpha k * (1 - method.alpha k) * method.gamma k / method.gamma (k + 1) *
          inner ℝ (∇ f (method.y k)) (method.v k - method.y k) =
        (1 - method.alpha k) * inner ℝ (∇ f (method.y k)) (method.y k - method k) := by
    calc
      method.alpha k * (1 - method.alpha k) * method.gamma k / method.gamma (k + 1) *
          inner ℝ (∇ f (method.y k)) (method.v k - method.y k)
          =
            (1 - method.alpha k) *
              (((method.alpha k * method.gamma k) / method.gamma (k + 1)) *
                inner ℝ (∇ f (method.y k)) (method.v k - method.y k)) := by
                  ring
      _ =
          (1 - method.alpha k) *
            inner ℝ (∇ f (method.y k)) (method.y k - method k) := by
              rw [← real_inner_smul_right, hcenter]
  have hnorm :
      ‖method.y k - method.v k‖ ^ (2 : ℕ) =
        (method.gamma (k + 1) / (method.alpha k * method.gamma k)) ^ (2 : ℕ) *
          ‖method k - method.y k‖ ^ (2 : ℕ) := by
    calc
      ‖method.y k - method.v k‖ ^ (2 : ℕ)
          = ‖method.v k - method.y k‖ ^ (2 : ℕ) := by rw [norm_sub_rev]
      _ =
          ‖(method.gamma (k + 1) / (method.alpha k * method.gamma k)) •
              (method.y k - method k)‖ ^ (2 : ℕ) := by
              rw [hvy]
      _ =
          (method.gamma (k + 1) / (method.alpha k * method.gamma k)) ^ (2 : ℕ) *
            ‖method.y k - method k‖ ^ (2 : ℕ) := by
              rw [norm_smul]
              calc
                (|method.gamma (k + 1) / (method.alpha k * method.gamma k)| *
                    ‖method.y k - method k‖) ^ (2 : ℕ)
                    =
                  |method.gamma (k + 1) / (method.alpha k * method.gamma k)| ^ (2 : ℕ) *
                    ‖method.y k - method k‖ ^ (2 : ℕ) := by
                      ring
                _ =
                    (method.gamma (k + 1) / (method.alpha k * method.gamma k)) ^ (2 : ℕ) *
                      ‖method.y k - method k‖ ^ (2 : ℕ) := by
                        rw [sq_abs]
      _ =
          (method.gamma (k + 1) / (method.alpha k * method.gamma k)) ^ (2 : ℕ) *
            ‖method k - method.y k‖ ^ (2 : ℕ) := by
              rw [norm_sub_rev]
  have hquadratic :
      method.alpha k * (1 - method.alpha k) * method.gamma k / method.gamma (k + 1) *
          ((μ / 2) * ‖method.y k - method.v k‖ ^ (2 : ℕ)) =
        (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
            (2 * method.alpha k * method.gamma k)) *
          ‖method k - method.y k‖ ^ (2 : ℕ) := by
    rw [hnorm]
    field_simp [halpha_ne, hgamma_curr_ne, hgamma_next_ne]
  -- Rewrite the generic successor formula with the owner recurrences, then simplify the linear
  -- and quadratic corrections through the center-gap bridge.
  calc
    estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 (k + 1)
        =
          (1 - method.alpha k) *
              estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
            method.alpha k * f (method.y k) -
            (method.alpha k ^ (2 : ℕ) / (2 * method.gamma (k + 1))) *
              ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
            (method.alpha k * (1 - method.alpha k) * method.gamma k /
                method.gamma (k + 1)) *
              ((μ / 2) * ‖method.y k - method.v k‖ ^ (2 : ℕ) +
                inner ℝ (∇ f (method.y k)) (method.v k - method.y k)) := by
          simpa [optimal_method_estimating_curvature_eq_gamma method k,
            optimal_method_estimating_curvature_eq_gamma method (k + 1),
            optimal_method_estimating_center_eq_v method k] using
            estimatingSequenceValue_succ
              f method.alpha method.y μ (f x0) gamma0 x0 k
    _ =
        (1 - method.alpha k) *
            estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
          method.alpha k * f (method.y k) -
          (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
          (1 - method.alpha k) * inner ℝ (∇ f (method.y k)) (method.y k - method k) +
          (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
              (2 * method.alpha k * method.gamma k)) *
            ‖method k - method.y k‖ ^ (2 : ℕ) := by
              rw [hgradient, mul_add, hquadratic, hlinear]
              ring

/-- Helper for Theorem 2.20: the owner estimating-sequence values dominate the actual objective
values along the optimal-method trajectory. -/
private theorem optimal_method_estimating_value_ge_objective
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹) :
    ∀ k : ℕ,
      f (method k) ≤
        estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k := by
  let hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  intro k
  induction k with
  | zero =>
      -- At time `0`, the owner estimating value is exactly `f x₀`.
      simp [estimatingSequenceValue, method.x_zero]
  | succ k ih =>
      have hfactor_nonneg : 0 ≤ 1 - method.alpha k := by
        linarith [(method.alpha_mem_Ioo k).2]
      have hinside_nonneg :
          0 ≤
            estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k -
                f (method.y k) +
              inner ℝ (∇ f (method.y k)) (method.y k - method k) +
              (μ * method.gamma (k + 1) / (2 * method.alpha k * method.gamma k)) *
                ‖method k - method.y k‖ ^ (2 : ℕ) := by
        have hlower := hf'.lower_tangent_quadratic (method.y k) (method k)
        have hbase :
            0 ≤
              estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k -
                  f (method.y k) +
                inner ℝ (∇ f (method.y k)) (method.y k - method k) -
                (μ / 2) * ‖method k - method.y k‖ ^ (2 : ℕ) := by
          have hinner :
              -inner ℝ (∇ f (method.y k)) (method.y k - method k) =
                inner ℝ (∇ f (method.y k)) (method k - method.y k) := by
            have hvec : method.y k - method k = -(method k - method.y k) := by
              abel
            rw [hvec, inner_neg_right, neg_neg]
          have hlower' :
              f (method.y k) -
                  inner ℝ (∇ f (method.y k)) (method.y k - method k) +
                  (μ / 2) * ‖method k - method.y k‖ ^ (2 : ℕ) ≤
                f (method k) := by
            calc
              f (method.y k) -
                    inner ℝ (∇ f (method.y k)) (method.y k - method k) +
                    (μ / 2) * ‖method k - method.y k‖ ^ (2 : ℕ)
                  =
                    f (method.y k) +
                      inner ℝ (∇ f (method.y k)) (method k - method.y k) +
                      (μ / 2) * ‖method k - method.y k‖ ^ (2 : ℕ) := by
                        rw [sub_eq_add_neg, hinner]
              _ ≤ f (method k) := hlower
          nlinarith [ih, hlower']
        have hnorm_nonneg : 0 ≤ ‖method k - method.y k‖ ^ (2 : ℕ) := by
          positivity
        have hcoef_nonneg :
            0 ≤ μ * method.gamma (k + 1) / (2 * method.alpha k * method.gamma k) + μ / 2 := by
          have hleft :
              0 ≤ μ * method.gamma (k + 1) / (2 * method.alpha k * method.gamma k) := by
            have hnum_nonneg : 0 ≤ μ * method.gamma (k + 1) := by
              exact mul_nonneg method.mu_nonneg (optimal_method_gamma_pos method (k + 1)).le
            have hdenom_pos : 0 < 2 * method.alpha k * method.gamma k := by
              have hαγ_pos : 0 < method.alpha k * method.gamma k := by
                exact mul_pos (method.alpha_pos k) (optimal_method_gamma_pos method k)
              nlinarith
            exact div_nonneg hnum_nonneg hdenom_pos.le
          have hright : 0 ≤ μ / 2 := by
            exact div_nonneg method.mu_nonneg (by norm_num)
          linarith
        have hextra_nonneg :
            0 ≤
              (μ * method.gamma (k + 1) / (2 * method.alpha k * method.gamma k) + μ / 2) *
                ‖method k - method.y k‖ ^ (2 : ℕ) := by
          exact mul_nonneg hcoef_nonneg hnorm_nonneg
        nlinarith [hbase, hextra_nonneg]
      have hstep_model :
          f (method.y k) - (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) ≤
            (1 - method.alpha k) *
                estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
              method.alpha k * f (method.y k) -
              (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
              (1 - method.alpha k) *
                inner ℝ (∇ f (method.y k)) (method.y k - method k) +
              (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
                  (2 * method.alpha k * method.gamma k)) *
                ‖method k - method.y k‖ ^ (2 : ℕ) := by
        have hscaled :
            0 ≤
              (1 - method.alpha k) *
                (estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k -
                    f (method.y k) +
                  inner ℝ (∇ f (method.y k)) (method.y k - method k) +
                  (μ * method.gamma (k + 1) / (2 * method.alpha k * method.gamma k)) *
                    ‖method k - method.y k‖ ^ (2 : ℕ)) := by
          exact mul_nonneg hfactor_nonneg hinside_nonneg
        calc
          f (method.y k) - (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ)
              ≤
                f (method.y k) - (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
                  (1 - method.alpha k) *
                    (estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k -
                        f (method.y k) +
                      inner ℝ (∇ f (method.y k)) (method.y k - method k) +
                      (μ * method.gamma (k + 1) /
                          (2 * method.alpha k * method.gamma k)) *
                        ‖method k - method.y k‖ ^ (2 : ℕ)) := by
                    nlinarith
          _ =
              (1 - method.alpha k) *
                  estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
                method.alpha k * f (method.y k) -
                (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
                (1 - method.alpha k) *
                  inner ℝ (∇ f (method.y k)) (method.y k - method k) +
                (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
                    (2 * method.alpha k * method.gamma k)) *
                  ‖method k - method.y k‖ ^ (2 : ℕ) := by
                    ring
      -- Route correction: first rewrite `φ_{k+1}^*` into the owner descent form, then insert the
      -- lower-tangent remainder as an explicit nonnegative term.
      calc
        f (method (k + 1))
            ≤ f (method.y k) - (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) :=
              method.x_succ_le k
        _ ≤
            (1 - method.alpha k) *
                estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 k +
              method.alpha k * f (method.y k) -
              (1 / (2 * L)) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
              (1 - method.alpha k) *
                inner ℝ (∇ f (method.y k)) (method.y k - method k) +
              (((1 - method.alpha k) * μ * method.gamma (k + 1)) /
                  (2 * method.alpha k * method.gamma k)) *
                ‖method k - method.y k‖ ^ (2 : ℕ) := hstep_model
        _ = estimatingSequenceValue f method.alpha method.y μ (f x0) gamma0 x0 (k + 1) := by
              rw [optimal_method_estimating_value_succ_eq_descent_form method k]

/-- Helper for Theorem 2.20: the abstract estimating-sequence theorem bounds the owner objective
gap by the canonical weight times the initial energy. -/
private theorem optimal_method_suboptimality_le_weight_initial_energy
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      method.weight k *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  let hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hgrad :
      ∀ j : ℕ, HasGradientAt f (∇ f (method.y j)) (method.y j) := by
    intro j
    exact hf'.contDiff.differentiable_one (method.y j) |>.hasGradientAt
  have halpha_mem_Icc :
      ∀ j : ℕ, method.alpha j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    exact Set.mem_Icc_of_Ioo (method.alpha_mem_Ioo j)
  have hphiUpper :
      ∀ j : ℕ,
        strongConvexEstimatingFunction μ f
            (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
            method.y method.alpha j ≤
          lineMap f
            (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
            (estimatingWeight method.alpha j) := by
    intro j
    simpa using
      strongConvexEstimatingFunction_upper_bound
        (φ₀ := quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
        (y := method.y) (α := method.alpha)
        hf'.strongConvexOn hgrad halpha_mem_Icc j
  have hsubopt :=
    estimating_sequence_suboptimality_le
      f
      method
      (fun j ↦
        strongConvexEstimatingFunction μ f
          (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
          method.y method.alpha j)
      (fun j ↦ estimatingSequenceValue f method.alpha method.y μ (f (method 0)) gamma0 (method 0) j)
      method.alpha
      xStar
      hxStar
      gamma0
      (fun j ↦ by
        simpa [method.x_zero] using optimal_method_estimating_value_ge_objective method hf j)
      (fun j ↦ by
        simpa [method.x_zero] using optimal_method_estimating_value_isLeast method j)
      hphiUpper
      rfl
      k
  -- Rewrite the source estimating weight back to the owner weight and normalize the initial point
  -- through `method.x_zero`.
  simpa [method.x_zero, optimal_method_estimatingWeight_eq_weight method k] using hsubopt

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
objective gap is bounded above by the corresponding hyperbolic estimate with the canonical initial
energy `f(x₀) - f(x*) + (γ₀ / 2) ‖x₀ - x*‖²`. -/
theorem optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * μ *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((gamma0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
            (2 : ℕ)) := by
  let hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  let energy : ℝ :=
    f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)
  have hμ : 0 < μ := hf'.mu_pos
  have hgamma0_pos : 0 < gamma0 := lt_trans hμ hgamma0.1
  have henergy_nonneg : 0 ≤ energy := by
    have hgap_nonneg : 0 ≤ f x0 - f xStar := by
      exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
    have hquad_nonneg : 0 ≤ (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      exact mul_nonneg (div_nonneg hgamma0_pos.le (by norm_num)) (by positivity)
    exact add_nonneg hgap_nonneg hquad_nonneg
  have hsubopt :
      f (method k) - f xStar ≤ method.weight k * energy :=
    optimal_method_suboptimality_le_weight_initial_energy method hf hxStar k
  have hweight :
      method.weight k ≤
        (4 * μ) /
          ((gamma0 - μ) *
              (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (OptimalMethodRecurrence.weight_bounds
        (method := (method : OptimalMethodRecurrence f L μ x0 gamma0)) hμ hgamma0 k).1
  calc
    f (method k) - f xStar ≤ method.weight k * energy := hsubopt
    _ ≤
        ((4 * μ) /
            ((gamma0 - μ) *
              (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
                (2 : ℕ))) * energy := by
          exact mul_le_mul_of_nonneg_right hweight henergy_nonneg
    _ =
        (4 * μ * energy) /
          ((gamma0 - μ) *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
            simp [energy, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
hyperbolic estimate yields the quadratic `O((k + 1)⁻²)` objective-gap upper bound with the same
canonical initial energy. -/
theorem optimal_method_quadratic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  let hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  let energy : ℝ :=
    f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)
  have hμ : 0 < μ := hf'.mu_pos
  have hgamma0_pos : 0 < gamma0 := lt_trans hμ hgamma0.1
  have henergy_nonneg : 0 ≤ energy := by
    have hgap_nonneg : 0 ≤ f x0 - f xStar := by
      exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
    have hquad_nonneg : 0 ≤ (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      exact mul_nonneg (div_nonneg hgamma0_pos.le (by norm_num)) (by positivity)
    exact add_nonneg hgap_nonneg hquad_nonneg
  have hsubopt :
      f (method k) - f xStar ≤ method.weight k * energy :=
    optimal_method_suboptimality_le_weight_initial_energy method hf hxStar k
  have hweight_hyper :
      method.weight k ≤
        (4 * μ) /
          ((gamma0 - μ) *
              (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (OptimalMethodRecurrence.weight_bounds
        (method := (method : OptimalMethodRecurrence f L μ x0 gamma0)) hμ hgamma0 k).1
  have hweight :
      method.weight k ≤ 4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    have hquad_bound :
        (4 * μ) /
            ((gamma0 - μ) *
              (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
                (2 : ℕ)) ≤
          4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (OptimalMethodRecurrence.weight_bounds
          (method := (method : OptimalMethodRecurrence f L μ x0 gamma0)) hμ hgamma0 k).2
    exact hweight_hyper.trans hquad_bound
  calc
    f (method k) - f xStar ≤ method.weight k * energy := hsubopt
    _ ≤ (4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) * energy := by
          exact mul_le_mul_of_nonneg_right hweight henergy_nonneg

/-- Helper for Theorem 2.20: the hyperbolic factor is bounded above by the quadratic factor after
rewriting the denominator through `sinh`.

This is the scalar comparison underlying
`OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound`, but without the recurrence-side
restriction `q_f ∈ (0, 1)`. -/
-- Proof sketch: write `exp t - exp (-t) = 2 sinh t` with
-- `t = ((k + 1) / 2) * sqrt q_f`, use `t ≤ sinh t` for `t ≥ 0`, square both sides, and then
-- rewrite `q_f = μ / L`.
lemma optimal_method_hyperbolic_factor_le_quadratic_factor
    (hμ : 0 < μ) (hL : 0 < L) (k : ℕ) :
    μ /
        (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
          Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ) ≤
      L / (k + 1 : ℝ) ^ (2 : ℕ) := by
  let qμL : ℝ := μ / L
  let t : ℝ := ((k + 1 : ℝ) / 2) * Real.sqrt qμL
  let d : ℝ := Real.exp t - Real.exp (-t)
  have hq_nonneg : 0 ≤ qμL := div_nonneg hμ.le hL.le
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have htsinh : t ≤ Real.sinh t := (Real.self_le_sinh_iff).2 ht_nonneg
  have hsinh_sq :
      t ^ (2 : ℕ) ≤ Real.sinh t ^ (2 : ℕ) := by
    have hsinh_nonneg : 0 ≤ Real.sinh t := (Real.sinh_nonneg_iff).2 ht_nonneg
    nlinarith
  have hqf_sq :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hq_nonneg]
  have hd_sq :
      d ^ (2 : ℕ) = 4 * Real.sinh t ^ (2 : ℕ) := by
    dsimp [d]
    rw [Real.sinh_eq]
    ring
  have hfactor :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    calc
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := hqf_sq
      _ ≤ 4 * Real.sinh t ^ (2 : ℕ) := by
            gcongr
      _ = d ^ (2 : ℕ) := hd_sq.symm
  have hmul :
      μ * (k + 1 : ℝ) ^ (2 : ℕ) ≤ L * d ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hfactor hL.le
    calc
      μ * (k + 1 : ℝ) ^ (2 : ℕ) = L * (qμL * (k + 1 : ℝ) ^ (2 : ℕ)) := by
        dsimp [qμL]
        field_simp [hL.ne']
      _ ≤ L * d ^ (2 : ℕ) := hscaled
  have hd_pos : 0 < d := by
    dsimp [d]
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    refine sub_pos.mpr ?_
    exact Real.exp_lt_exp.mpr (by linarith)
  have hk_sq_pos : 0 < (k + 1 : ℝ) ^ (2 : ℕ) := by
    positivity
  refine (div_le_div_iff₀ (by positivity) hk_sq_pos).2 ?_
  simpa [d, t, qμL, mul_assoc, mul_left_comm, mul_comm] using hmul

variable {x0 : E}

/-- Helper for Theorem 2.20: the initial Lyapunov energy at `γ₀ = 3L + μ` is bounded by the
explicit radius term from the source statement. -/
private theorem optimal_method_initial_energy_le_explicit_radius_sq
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    f x0 - f xStar + ((3 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
      ((4 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  let hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hgrad_zero : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  have hgap :
      f x0 - f xStar ≤ (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hupper :
        f x0 ≤ f xStar + (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      simpa [hgrad_zero] using hf'.upper_tangent_quadratic xStar x0
    linarith
  -- The smooth upper tangent estimate at the minimizer absorbs the initial function-value gap.
  linarith

/-- Theorem 2.20 (1): for a smooth strongly convex minimization problem with `γ₀ = 3L + μ`, the
iterate sequence of the optimal method satisfies the `O((k + 1)⁻²)` function-value bound. -/
-- Proof sketch: apply `estimating_sequence_suboptimality_le` to the owner estimating sequence
-- attached to `method`. Then use `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ` to bound the canonical weight `λₖ`, and bound the initial energy by the smooth
-- upper quadratic estimate at the minimizer `xStar`.
theorem optimal_method_quadratic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  have hgamma0 : (3 * L + μ : ℝ) ∈ Set.Ioc μ (3 * L + μ) := by
    constructor
    · linarith [method.L_pos]
    · exact le_rfl
  have hbase :=
    optimal_method_quadratic_suboptimality_le_of_mem_Ioc method hf hxStar hgamma0 k
  have henergy :=
    optimal_method_initial_energy_le_explicit_radius_sq
      (μ := μ) (L := L) (f := f) (x0 := x0) (xStar := xStar) hf hxStar
  have hcoeff_nonneg :
      0 ≤ 4 * L / (((3 * L + μ) - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    have hdenom_pos : 0 < (((3 * L + μ) - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
      have hleft : 0 < ((3 * L + μ) - μ) := by
        nlinarith [method.L_pos]
      have hright : 0 < (k + 1 : ℝ) ^ (2 : ℕ) := by
        positivity
      exact mul_pos hleft hright
    exact div_nonneg (by nlinarith [method.L_pos]) hdenom_pos.le
  calc
    f (method k) - f xStar
        ≤ (4 * L / (((3 * L + μ) - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
            (f x0 - f xStar + ((3 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
              simpa using hbase
    _ ≤ (4 * L / (((3 * L + μ) - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
          (((4 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left henergy hcoeff_nonneg
    _ = (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
            field_simp [method.L_pos.ne']
            ring

/-- Theorem 2.20 (2): if `μ > 0`, then the iterate sequence of the optimal method satisfies the
sharper hyperbolic function-value estimate. -/
-- Proof sketch: combine `estimating_sequence_suboptimality_le` with the positive-`μ` upper bound
-- on the owner weight `λₖ` from `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ`, and rewrite the resulting factor using `q[μ, L] = μ / L`.
theorem optimal_method_hyperbolic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) := by
  have hgamma0 : (3 * L + μ : ℝ) ∈ Set.Ioc μ (3 * L + μ) := by
    constructor
    · linarith [method.L_pos]
    · exact le_rfl
  have hbase :=
    optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc method hf hxStar hgamma0 k
  have henergy :=
    optimal_method_initial_energy_le_explicit_radius_sq
      (μ := μ) (L := L) (f := f) (x0 := x0) (xStar := xStar) hf hxStar
  have hcoeff_nonneg :
      0 ≤
        (4 * μ) /
          (((3 * L + μ) - μ) *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
    have hq_pos : 0 < q[μ, L] := div_pos (mem_S11_iff.mp hf).mu_pos method.L_pos
    have ht_pos : 0 < (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) := by
      have hsqrt_pos : 0 < Real.sqrt q[μ, L] := Real.sqrt_pos.2 hq_pos
      positivity
    have hdiff_pos :
        0 < Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
          Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L])) := by
      refine sub_pos.mpr ?_
      exact Real.exp_lt_exp.mpr (by linarith)
    have hdenom_pos :
        0 <
          (((3 * L + μ) - μ) *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
      have hleft : 0 < ((3 * L + μ) - μ) := by
        nlinarith [method.L_pos]
      have hright :
          0 <
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ) := by
        exact pow_pos hdiff_pos 2
      exact mul_pos hleft hright
    exact div_nonneg (by nlinarith [(mem_S11_iff.mp hf).mu_pos]) hdenom_pos.le
  calc
    f (method k) - f xStar
        ≤
          ((4 * μ) /
              (((3 * L + μ) - μ) *
                (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                  Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
                  (2 : ℕ))) *
            (f x0 - f xStar + ((3 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
    _ ≤
        ((4 * μ) /
            (((3 * L + μ) - μ) *
              (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
                Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
                (2 : ℕ))) *
          (((4 * L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left henergy hcoeff_nonneg
    _ =
        (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          (3 *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
              (2 : ℕ)) := by
            field_simp [method.L_pos.ne']
            ring

end OptimalMethodRates

section ExplicitBoundComparison

variable {F : Type u} [NormedAddCommGroup F]
variable {μ L : ℝ}

/-- Theorem 2.20 (3): for `μ > 0`, the hyperbolic upper bound from the optimal-method estimate is
itself bounded above by the quadratic `O((k + 1)⁻²)` bound. -/
-- Proof sketch: compare the hyperbolic denominator with its quadratic lower bound from the scalar
-- recurrence analysis for the owner weights, equivalently the second inequality in
-- `OptimalMethodRecurrence.weight_bounds` specialized to `γ₀ = 3L + μ`.
theorem optimal_method_hyperbolic_bound_le_quadratic_bound
    (hμ : 0 < μ) (hL : 0 < L)
    (x0 xStar : F)
    (k : ℕ) :
    (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let c : ℝ := (2 * (4 + q[μ, L]) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3
  have hbase :=
    optimal_method_hyperbolic_factor_le_quadratic_factor hμ hL k
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hc_nonneg
  simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

end ExplicitBoundComparison

end
