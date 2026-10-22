/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v}

/- Theorem 6.3 lies in the Chapter 6 smoothing / primal-dual gap domain.

Sampled owner-style declarations:
- `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical owners for a finite
  normalized weighted average and its finite-sum expansion;
- `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Lemma_6_12`, the chapter owner for
  recording a raw primal-dual gap bound canonically as interval membership in `Set.Icc`;
- `scaled_smoothing_parameter_product_eq` in `Proposition_6_28`, the chapter's algebraic owner for
  simplifying the optimized smoothing-parameter substitution.

Best owner abstraction:
- source-facing: Theorem 6.3's explicit weight family, weighted dual iterate `\hat u_N`, and
  optimized smoothing parameter `μ(N)`;
- core/canonical: `Finset.centerMass` for `\hat u_N` and raw interval membership
  `f x_N - φ(\hat u_N) ∈ Set.Icc 0 bound` for the primal-dual gap;
- bridge/view: the explicit coefficient formula
  `2 (i + 1) / ((N + 1) (N + 2))` for the weight family.

Primitive data:
- the explicit finite weight family on `Fin (N + 1)`;
- the chosen smoothing parameter `μ(N)` at a positive iteration count `N`;
- the smoothed objective value `fμ x_N` together with its pointwise lower-approximation at `x_N`
  and residual-gap bounds.

Derived API:
- the normalized weighted-average realization of `\hat u_N` through `Finset.centerMass`;
- the source finite-sum expansion of that weighted average;
- the canonical interval-valued gap bounds.

Source/core/bridge triage:
- source-facing: the explicit model weights, the weighted dual iterate `\hat u_N`, and the
  optimized Theorem 6.3 gap estimate;
- core/canonical: `Finset.centerMass` and `Set.Icc`;
- bridge/view: the explicit coefficient formula and finite-sum expansion.

The previous version kept parallel local public wrappers for the averaged dual iterate and the raw
gap. This refinement deletes those wrappers, reuses the chapter's weighted-average owner directly,
and restores Theorem 6.3 as a source-facing smoothing statement rather than an algebraic
post-processing lemma on an already packaged raw gap bound. -/

/-- The weight family
`a_i^(N) = 2 (i + 1) / ((N + 1) (N + 2))`
used in the weighted dual iterate `\hat u_N` of Theorem 6.3. -/
def explicitModelDualAverageWeights (N : ℕ) : Fin (N + 1) → ℝ :=
  fun i ↦ (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2))

-- Proof sketch: unfold `explicitModelDualAverageWeights`.
/-- Evaluating `explicitModelDualAverageWeights N` at `i` recovers the textbook coefficient
`2 (i + 1) / ((N + 1) (N + 2))`. -/
theorem explicitModelDualAverageWeights_apply (N : ℕ) (i : Fin (N + 1)) :
    explicitModelDualAverageWeights N i =
      (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) :=
  rfl

-- Proof sketch: sum the arithmetic progression `1 + 2 + ··· + (N + 1)` and divide by
-- `((N + 1) (N + 2)) / 2`.
/-- The explicit-model weights form a normalized weight family. -/
theorem explicitModelDualAverageWeights_sum_eq_one (N : ℕ) :
    ∑ i, explicitModelDualAverageWeights N i = 1 := by
  let den : ℝ := ((N : ℝ) + 1) * ((N : ℝ) + 2)
  have hden : den ≠ 0 := by
    dsimp [den]
    positivity
  -- Rewrite the `Fin`-indexed weights as the source arithmetic progression over `range`.
  change ∑ i : Fin (N + 1), (2 * (((i : ℕ) : ℝ) + 1)) / den = 1
  have hsum_nat :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ i + 1) =
        ((N + 1) * (N + 2)) / 2 := by
    have hshift :
        Finset.sum (Finset.range (N + 2)) (fun i ↦ i) =
          Finset.sum (Finset.range (N + 1)) (fun i ↦ i + 1) := by
      simpa using (Finset.sum_range_succ' (fun i : ℕ ↦ i) (N + 1))
    calc
      Finset.sum (Finset.range (N + 1)) (fun i ↦ i + 1)
          = Finset.sum (Finset.range (N + 2)) (fun i ↦ i) := by
              rw [hshift]
      _ = ((N + 2) * ((N + 2) - 1)) / 2 := by
            simpa using (Finset.sum_range_id (N + 2))
      _ = ((N + 1) * (N + 2)) / 2 := by
            simp [Nat.mul_comm]
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ (((i : ℕ) : ℝ) + 1)) =
        (((N : ℝ) + 1) * ((N : ℝ) + 2)) / 2 := by
    -- Cast the natural arithmetic-series identity to `ℝ` only after the finite sum is settled.
    have hsum_cast :
        ((Finset.sum (Finset.range (N + 1)) (fun i ↦ i + 1) : ℕ) : ℝ) =
          ((((N + 1) * (N + 2)) / 2 : ℕ) : ℝ) := by
      exact congrArg (fun t : ℕ ↦ (t : ℝ)) hsum_nat
    calc
      Finset.sum (Finset.range (N + 1)) (fun i ↦ (((i : ℕ) : ℝ) + 1))
          = ((((N + 1) * (N + 2)) / 2 : ℕ) : ℝ) := by
              simpa using hsum_cast
      _ = (((N : ℝ) + 1) * ((N : ℝ) + 2)) / 2 := by
            have htwo_dvd : 2 ∣ (N + 1) * (N + 2) := by
              simpa [Nat.add_assoc] using (Nat.even_mul_succ_self (N + 1)).two_dvd
            have htwo_ne : ((2 : ℕ) : ℝ) ≠ 0 := by norm_num
            rw [Nat.cast_div htwo_dvd htwo_ne]
            norm_num
  -- Pull out the common denominator and simplify the arithmetic-series value.
  calc
    (∑ i : Fin (N + 1), (2 * (((i : ℕ) : ℝ) + 1)) / den)
        = Finset.sum (Finset.range (N + 1))
            (fun i : ℕ ↦ (2 * ((i : ℝ) + 1)) / den) := by
              simpa using (Fin.sum_univ_eq_sum_range
                (fun i : ℕ ↦ (2 * ((i : ℝ) + 1)) / den) (N + 1))
    _ = Finset.sum (Finset.range (N + 1))
            (fun i ↦ (2 / den) * ((((i : ℕ) : ℝ) + 1))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
    _ = (2 / den) *
          Finset.sum (Finset.range (N + 1)) (fun i ↦ ((((i : ℕ) : ℝ) + 1))) := by
            rw [Finset.mul_sum]
    _ = (2 / den) *
          ((((N : ℝ) + 1) * ((N : ℝ) + 2)) / 2) := by
            rw [hsum]
    _ = 1 := by
          dsimp [den] at hden ⊢
          field_simp [hden]

-- Proof sketch: apply `Finset.centerMass_eq_of_sum_1` and use
-- `explicitModelDualAverageWeights_sum_eq_one`.
/-- The center of mass with `explicitModelDualAverageWeights N` is the source finite sum
`\hat u_N = Σ_{i=0}^N 2 (i + 1) / ((N + 1) (N + 2)) u_i`. -/
theorem centerMass_explicitModelDualAverageWeights_eq_sum
    [AddCommGroup E₂] [Module ℝ E₂]
    (N : ℕ) (u : Fin (N + 1) → E₂) :
    Finset.univ.centerMass (explicitModelDualAverageWeights N) u =
      ∑ i, explicitModelDualAverageWeights N i • u i := by
  simpa using
    (Finset.univ.centerMass_eq_of_sum_1 u (explicitModelDualAverageWeights_sum_eq_one N))

section ExplicitModelSmoothing

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The smoothing parameter
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)`
chosen in Theorem 6.3. -/
def explicitModelSmoothingParameter
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) : ℝ :=
  (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂)

-- Proof sketch: unfold `explicitModelSmoothingParameter`.
/-- Evaluating `explicitModelSmoothingParameter` recovers the displayed formula for `μ(N)`. -/
theorem explicitModelSmoothingParameter_def
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) :
    explicitModelSmoothingParameter A D₁ D₂ N =
      (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂) :=
  rfl

/-- Helper for Theorem 6.3: multiplying the optimized smoothing parameter by `D₂` produces one
half of the displayed leading-order error term. -/
lemma explicit_model_smoothing_parameter_mul_D₂_eq
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+)
    (hD₁ : 0 ≤ D₁) :
    explicitModelSmoothingParameter A D₁ D₂ N * D₂ =
      (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) := by
  -- Expand `μ(N)` and isolate the scalar identity in `D₁` and `D₂`.
  rw [explicitModelSmoothingParameter_def]
  calc
    ((2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂)) * D₂
        = (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
            (Real.sqrt (D₁ / D₂) * D₂) := by
              ring
    _ = (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ((Real.sqrt D₁ / Real.sqrt D₂) * D₂) := by
            rw [Real.sqrt_div hD₁ D₂]
    _ = (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          (Real.sqrt D₁ * (D₂ / Real.sqrt D₂)) := by
            ring
    _ = (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          (Real.sqrt D₁ * Real.sqrt D₂) := by
            rw [Real.div_sqrt]
    _ = (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) := by
            rw [← Real.sqrt_mul hD₁ D₂]

/-- Helper for Theorem 6.3: the optimized smoothing parameter squares to the balancing ratio that
equates the direct and reciprocal smoothing contributions. -/
lemma explicit_model_smoothing_parameter_sq_eq
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂) :
    explicitModelSmoothingParameter A D₁ D₂ N ^ 2 =
      (4 * ‖A‖ ^ (2 : ℕ) * D₁) / (D₂ * ((N : ℝ) * ((N : ℝ) + 1))) := by
  let n : ℝ := (N : ℝ) * ((N : ℝ) + 1)
  have hn : 0 ≤ n := by
    dsimp [n]
    positivity
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  have hratio : 0 ≤ D₁ / D₂ := by
    exact div_nonneg hD₁ hD₂.le
  -- Square the explicit formula and collapse both square roots using nonnegativity.
  rw [explicitModelSmoothingParameter_def]
  calc
    ((2 * ‖A‖ / Real.sqrt n) * Real.sqrt (D₁ / D₂)) ^ 2
        = (2 * ‖A‖ / Real.sqrt n) ^ 2 * (Real.sqrt (D₁ / D₂)) ^ 2 := by
              ring
    _ = (2 * ‖A‖ / Real.sqrt n) ^ 2 * (D₁ / D₂) := by
          rw [Real.sq_sqrt hratio]
    _ = (((2 * ‖A‖) ^ 2) / (Real.sqrt n) ^ 2) * (D₁ / D₂) := by
          ring
    _ = (((2 * ‖A‖) ^ 2) / n) * (D₁ / D₂) := by
          rw [Real.sq_sqrt hn]
    _ = (4 * ‖A‖ ^ (2 : ℕ) * D₁) / (D₂ * n) := by
          have hn_ne : n ≠ 0 := by positivity
          have hD₂_ne : D₂ ≠ 0 := by linarith
          field_simp [hn_ne, hD₂_ne]
          ring
    _ = (4 * ‖A‖ ^ (2 : ℕ) * D₁) / (D₂ * ((N : ℝ) * ((N : ℝ) + 1))) := by
          rfl

/-- Helper for Theorem 6.3: the reciprocal smoothing contribution matches the direct smoothing
contribution for the optimized choice of `μ(N)`. -/
lemma explicit_model_reciprocal_gap_term_eq_parameter_mul
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂) :
    (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
        (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) =
      explicitModelSmoothingParameter A D₁ D₂ N * D₂ := by
  let μ := explicitModelSmoothingParameter A D₁ D₂ N
  let n : ℝ := (N : ℝ) * ((N : ℝ) + 1)
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  have hD₂n_ne : D₂ * n ≠ 0 := by
    positivity
  have hμsq :
      μ ^ 2 = (4 * ‖A‖ ^ (2 : ℕ) * D₁) / (D₂ * n) := by
    simpa [μ, n] using explicit_model_smoothing_parameter_sq_eq A D₁ D₂ N hD₁ hD₂
  have hnum :
      4 * ‖A‖ ^ (2 : ℕ) * D₁ = μ ^ 2 * (D₂ * n) := by
    exact (div_eq_iff hD₂n_ne).mp hμsq.symm
  -- Substitute the balanced numerator and cancel the common `μ * n` factor.
  rw [hnum]
  by_cases hμ : μ = 0
  · simp [hμ, μ, n]
  · have hn_ne : n ≠ 0 := by positivity
    -- Cross-multiply by the nonzero denominator instead of asking `field_simp` to guess
    -- the intended cancellation pattern.
    apply (div_eq_iff (mul_ne_zero hμ hn_ne)).2
    ring

/-- Helper for Theorem 6.3: after substituting the optimized smoothing parameter, the two
smoothing contributions collapse to the displayed leading-order term. -/
lemma explicit_model_smoothing_upper_endpoint_eq
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ M : ℝ) (N : ℕ+)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂) :
    explicitModelSmoothingParameter A D₁ D₂ N * D₂ +
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1)) =
      ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  have hfirst := explicit_model_smoothing_parameter_mul_D₂_eq A D₁ D₂ N hD₁
  have hsecond := explicit_model_reciprocal_gap_term_eq_parameter_mul A D₁ D₂ N hD₁ hD₂
  -- Replace both smoothing contributions by the same canonical half-term.
  rw [hsecond, hfirst]
  ring

-- Proof sketch: write
-- `f x_N - φ(\hat u_N) = (f x_N - fμ x_N) + (fμ x_N - φ(\hat u_N))`.
-- The smoothing lower-approximation bounds the first term by `μ(N) D₂`, while the source
-- residual hypothesis bounds the second term. The lower bound comes from
-- `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`.
/-- Companion source-facing bridge for Theorem 6.3: if the smoothed value `fμ x_N` lies between
`φ(\hat u_N)` and `f x_N`, if the lower smoothing estimate at `x_N` has error at most `μ(N) D₂`,
and if the residual smoothed gap is bounded by the model term
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`, then the raw primal-dual gap at
`(x_N, \hat u_N)` lies in the interval
`[0, μ(N) D₂ + 4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))]`. -/
theorem explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      (explicitModelSmoothingParameter A D₁ D₂ N * D₂ +
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  -- Repackage the explicit-model hypotheses into the chapter-level raw gap theorem.
  rcases Set.mem_Icc.mp
      (primal_dual_gap_bound_of_smoothed_lower_approximation
      (f := f) (fμ₂ := fμ) (φ := φ)
      (μ₂ := explicitModelSmoothingParameter A D₁ D₂ N) (D₂ := D₂)
      (r :=
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1)))
      (xBar := xN)
      (uBar := Finset.univ.centerMass (explicitModelDualAverageWeights N) u)
      hxN_approx hφ_le hsmoothed_gap hfμ_le) with ⟨hlow, hup⟩
  refine Set.mem_Icc.mpr ⟨hlow, ?_⟩
  -- Only reassociation separates the imported endpoint from the displayed one.
  simpa [add_assoc] using hup

-- Proof sketch: first apply `explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound`.
-- Then substitute the explicit choice of `μ(N)` and simplify the first two upper-bound terms to
-- `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))`, using the chapter's algebraic owner
-- `scaled_smoothing_parameter_product_eq`.
/-- Theorem 6.3: let
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)` and
`\hat u_N = Finset.univ.centerMass (explicitModelDualAverageWeights N) u`.
If `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`, if `fμ` is a lower smoothing of `f` with error at most
`μ(N) D₂` at `x_N`, and if the smoothed residual gap at `(x_N, \hat u_N)` is bounded by
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`,
then
`0 ≤ f(x_N) - φ(\hat u_N) ≤ 4 ‖A‖ √(D₁ D₂) / √(N (N + 1)) + 4 M D₁ / (N (N + 1))`. -/
theorem optimized_primal_dual_gap_bound_for_explicit_model_smoothing
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  have hgap :=
    explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound
      A f fμ φ N xN u D₁ D₂ M hxN_approx hφ_le hfμ_le hsmoothed_gap
  -- Rewrite the raw upper endpoint using the optimized choice of `μ(N)`.
  simpa [explicit_model_smoothing_upper_endpoint_eq A D₁ D₂ M N hD₁ hD₂] using hgap

/-- Helper for Theorem 6.3: the optimized upper endpoint is at most `ε` once the iteration count
dominates the source complexity expression. -/
lemma explicit_model_gap_upper_bound_le_epsilon_of_iteration_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    (N : ℕ+) (D₁ D₂ M ε : ℝ) (hε : 0 < ε)
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε + 2 * Real.sqrt (M * D₁ / ε) ≤ (N : ℝ)) :
    ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
      (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) ≤ ε := by
  let a : ℝ := 4 * ‖A‖ * Real.sqrt (D₁ * D₂)
  let s : ℝ := Real.sqrt (M * D₁ / ε)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hn_pos : 0 < (N : ℝ) := by
    exact_mod_cast N.pos
  have hn_ne : (N : ℝ) ≠ 0 := by
    linarith
  have hsqrt_ge : (N : ℝ) ≤ Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    refine (Real.le_sqrt' hn_pos).2 ?_
    nlinarith
  have hfirst_term :
      (4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) ≤
        a / (N : ℝ) := by
    have hdiv :
        a / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) ≤ a / (N : ℝ) := by
      exact div_le_div_of_nonneg_left ha_nonneg hn_pos hsqrt_ge
    simpa [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hs_sq :
      s ^ 2 = max (M * D₁ / ε) 0 := by
    dsimp [s]
    simpa using (Real.sq_sqrt' : Real.sqrt (M * D₁ / ε) ^ 2 = max (M * D₁ / ε) 0)
  have hratio_le : M * D₁ / ε ≤ s ^ 2 := by
    rw [hs_sq]
    exact le_max_left _ _
  have hMD₁_le : M * D₁ ≤ ε * s ^ 2 := by
    have hmul : M * D₁ ≤ s ^ 2 * ε := by
      exact (div_le_iff₀ hε).1 hratio_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsecond_term :
      (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1)) ≤ (4 * ε * s ^ 2) / ((N : ℝ) ^ 2) := by
    have hstep1 :
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1)) ≤
          (4 * ε * s ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) := by
      have hnum_le : 4 * M * D₁ ≤ 4 * ε * s ^ 2 := by
        nlinarith
      exact div_le_div_of_nonneg_right hnum_le (by positivity)
    have hstep2 :
        (4 * ε * s ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) ≤
          (4 * ε * s ^ 2) / ((N : ℝ) ^ 2) := by
      have hnum_nonneg : 0 ≤ 4 * ε * s ^ 2 := by
        positivity
      have hn_sq_pos : 0 < (N : ℝ) ^ 2 := by
        positivity
      have hn_sq_le : (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) + 1) := by
        nlinarith
      exact div_le_div_of_nonneg_left hnum_nonneg hn_sq_pos hn_sq_le
    exact le_trans hstep1 hstep2
  have hdiv_nonneg : 0 ≤ a / ε := by
    exact div_nonneg ha_nonneg hε.le
  have htwo_s_le : 2 * s ≤ (N : ℝ) := by
    linarith
  let y : ℝ := (2 * s) / (N : ℝ)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (by positivity) hn_pos.le
  have hy_le_one : y ≤ 1 := by
    dsimp [y]
    rw [div_le_iff₀ hn_pos]
    linarith
  have hy_rewrite : ((N : ℝ) - 2 * s) / (N : ℝ) = 1 - y := by
    dsimp [y]
    field_simp [hn_ne]
  have hfirst_budget : a / (N : ℝ) ≤ ε * (1 - y) := by
    have hbudget : a / ε ≤ (N : ℝ) - 2 * s := by
      linarith
    have hbudget_div : (a / ε) / (N : ℝ) ≤ ((N : ℝ) - 2 * s) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hbudget hn_pos.le
    have ha_rewrite : a / (N : ℝ) = ε * ((a / ε) / (N : ℝ)) := by
      field_simp [hε.ne', hn_ne]
    calc
      a / (N : ℝ) = ε * ((a / ε) / (N : ℝ)) := ha_rewrite
      _ ≤ ε * (((N : ℝ) - 2 * s) / (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hbudget_div hε.le
      _ = ε * (1 - y) := by rw [hy_rewrite]
  have hsecond_budget : (4 * ε * s ^ 2) / ((N : ℝ) ^ 2) = ε * y ^ 2 := by
    dsimp [y]
    field_simp [hn_ne]
    ring
  have hcombined :
      a / (N : ℝ) + (4 * ε * s ^ 2) / ((N : ℝ) ^ 2) ≤ ε := by
    calc
      a / (N : ℝ) + (4 * ε * s ^ 2) / ((N : ℝ) ^ 2)
          ≤ ε * (1 - y) + ε * y ^ 2 := by
              rw [hsecond_budget]
              exact add_le_add hfirst_budget le_rfl
      _ = ε * ((1 - y) + y ^ 2) := by ring
      _ ≤ ε * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            nlinarith [hy_nonneg, hy_le_one]
      _ = ε := by ring
  -- Bound the displayed endpoint by the simpler quadratic expression controlled by `hiter`.
  calc
    ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1)))
        ≤ a / (N : ℝ) + (4 * ε * s ^ 2) / ((N : ℝ) ^ 2) := by
              exact add_le_add hfirst_term hsecond_term
    _ ≤ ε := hcombined

-- Proof sketch: combine the optimized interval bound with the hypothesis
-- `4 ‖A‖ √(D₁ D₂) / ε + 2 √(M D₁ / ε) ≤ N`, then check that the right-hand side of the bound is
-- at most `ε`.
/-- If the iteration count dominates the Theorem 6.3 complexity expression, then the weighted
dual iterate `\hat u_N` and the primal iterate `x_N` form an `ε`-accurate primal-dual pair. -/
theorem primal_dual_gap_le_epsilon_of_iteration_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M ε : ℝ) (hε : 0 < ε)
    (hgap :
      f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
        ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))))
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε + 2 * Real.sqrt (M * D₁ / ε) ≤ (N : ℝ)) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ ε := by
  -- Extract the interval upper bound and compare it with the iteration-count estimate.
  exact le_trans hgap.2 <|
    explicit_model_gap_upper_bound_le_epsilon_of_iteration_bound A N D₁ D₂ M ε hε hiter

end ExplicitModelSmoothing

end
