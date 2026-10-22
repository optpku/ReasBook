/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_23
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_48

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ} [NeZero m]
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ}
variable {fOpt qOpt L ε : ℝ}
variable (xSel : (Fin m → NNReal) → {x // x ∈ X}) (lam0 : Fin m → NNReal)
variable {xBar : E}

local notation "γ" => fun n : ℕ ↦ 1 / Real.sqrt ((n : ℝ) + 1)
local notation "q" => lagrangian_dual_objective X f (dual_constraint_vector g)
local notation "α" => (f xBar - fOpt) / strict_feasibility_margin g xBar
local notation "C" =>
  dual_projected_subgradient_partial_average_rate_constant f fOpt qOpt g xBar L lam0
local notation "xSeq" => dual_projected_subgradient_primal_iterate X g xSel γ lam0
local notation "constraintSeq" =>
  fun n ↦ dual_projected_subgradient_constraint_vector g (xSeq n : E)
local notation "partialAvg" =>
  dual_projected_subgradient_partial_average_iterate (X := X) (g := g) xSel γ lam0
local notation "gVec" => fun x i ↦ g i x

/- Corollary 8.49 is `source-facing`: it converts the `O(1 / √k)` estimates from Theorem 8.48
into an iteration-complexity threshold of order `O(1 / ε^2)`. The canonical owners are already
present in the Chapter 8 API: the repaired partial averaging iterate
`dual_projected_subgradient_partial_average_iterate`,
the approximate-solution predicate `is_epsilon_optimal_and_feasible_solution` from
Definition 8.23, and the `O(1 / √k)` estimates from Theorem 8.48. The main labeled entry is
therefore the source-facing `ε`-optimal-and-feasible conclusion, with unpacked inequality
surfaces recovered as companion lemmas. -/

-- Proof sketch: unfold the displayed positive-part Euclidean norm and
-- `dual_projected_subgradient_constraint_vector`; each positive-part coordinate satisfies
-- `max (g_i x) 0 ≤ |g_i x|`, so the Euclidean norm of the positive part is bounded by the
-- Euclidean norm of the full constraint vector.
/-- The Euclidean norm of the coordinatewise positive part `[(g(x))]_+` is bounded by the
Euclidean norm of the full constraint vector `g(x)`. -/
theorem positive_constraint_violation_le_dual_projected_subgradient_constraint_vector_norm
    (g : Fin m → E → ℝ) (x : E) :
    positive_constraint_violation (fun y i ↦ g i y) x ≤
      ‖dual_projected_subgradient_constraint_vector g x‖ := by
  let posVec : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 ((fun i : Fin m ↦ g i x)⁺)
  let constraintVec : EuclideanSpace ℝ (Fin m) := dual_projected_subgradient_constraint_vector g x
  -- Compare the positive-part and full constraint vectors coordinatewise.
  have hcoord :
      ∀ i : Fin m,
        ‖posVec i‖ ^ (2 : ℕ) ≤ ‖constraintVec i‖ ^ (2 : ℕ) := by
    intro i
    have hcoordNorm : ‖posVec i‖ ≤ ‖constraintVec i‖ := by
      by_cases hi : 0 ≤ g i x
      · simp [posVec, constraintVec, hi]
      · have hi' : g i x ≤ 0 := le_of_not_ge hi
        simp [posVec, constraintVec, hi']
    nlinarith [hcoordNorm, norm_nonneg (posVec i), norm_nonneg (constraintVec i)]
  have hPosSq :
      ‖posVec‖ ^ (2 : ℕ) = ∑ i : Fin m, ‖posVec i‖ ^ (2 : ℕ) := by
    simpa [posVec] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m ↦ ℝ) posVec)
  have hConstraintSq :
      ‖constraintVec‖ ^ (2 : ℕ) = ∑ i : Fin m, ‖constraintVec i‖ ^ (2 : ℕ) := by
    simpa [constraintVec] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m ↦ ℝ) constraintVec)
  have hSq : ‖posVec‖ ^ (2 : ℕ) ≤ ‖constraintVec‖ ^ (2 : ℕ) := by
    -- Summing the coordinatewise square bounds gives the Euclidean square-norm comparison.
    rw [hPosSq, hConstraintSq]
    exact Finset.sum_le_sum fun i _ ↦ hcoord i
  -- Compare the two nonnegative norms through their squares.
  rw [positive_constraint_violation_def]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq

-- Proof sketch: rearrange the iteration lower bound into
-- `C^2 ≤ (k + 2) * (min (α^2) 1 * ε^2)`. Taking square roots gives
-- `C / √(k + 2) ≤ √(min (α^2) 1) * ε`, and `hα` identifies the square-root factor with
-- `min α 1`.
/-- The iteration threshold from Corollary 8.49 forces the `O(1 / √k)` rate from
Theorem 8.48 to be at most `min α 1 * ε`. -/
theorem dual_projected_subgradient_partial_average_rate_le_min_alpha_mul_epsilon
    (hε : 0 < ε) (hα : 0 < α) {k : ℕ}
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    C / Real.sqrt ((k : ℝ) + 2) ≤ min α 1 * ε := by
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
    positivity
  have hmin_pos : 0 < min α 1 := by
    exact lt_min hα zero_lt_one
  have hrhs_nonneg : 0 ≤ min α 1 * ε := by
    positivity
  have hk_shifted :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) ≤ (k : ℝ) + 2 := by
    linarith
  by_cases hC_nonneg : 0 ≤ C
  · by_cases hα_le_one : α ≤ 1
    · have hmin : min α 1 = α := min_eq_left hα_le_one
      have hmin_sq : min (α ^ (2 : ℕ)) 1 = α ^ (2 : ℕ) := by
        refine min_eq_left ?_
        nlinarith
      have hden_pos : 0 < α ^ (2 : ℕ) * ε ^ (2 : ℕ) := by
        positivity
      have hC_sq :
          C ^ (2 : ℕ) ≤ ((k : ℝ) + 2) * (α ^ (2 : ℕ) * ε ^ (2 : ℕ)) := by
        have hbound :
            C ^ (2 : ℕ) / (α ^ (2 : ℕ) * ε ^ (2 : ℕ)) ≤ (k : ℝ) + 2 := by
          have hbound' := hk_shifted
          rwa [hmin_sq] at hbound'
        exact (div_le_iff₀ hden_pos).mp hbound
      have hsquare :
          C ^ (2 : ℕ) ≤ (Real.sqrt ((k : ℝ) + 2) * (α * ε)) ^ (2 : ℕ) := by
        have hk_nonneg : 0 ≤ (k : ℝ) + 2 := by
          positivity
        nlinarith [hC_sq, Real.sq_sqrt hk_nonneg]
      have hmul :
          C ≤ Real.sqrt ((k : ℝ) + 2) * (α * ε) := by
        exact (sq_le_sq₀ hC_nonneg (mul_nonneg (le_of_lt hsqrt_pos) (by positivity))).mp hsquare
      have hdiv : C / Real.sqrt ((k : ℝ) + 2) ≤ α * ε := by
        exact (div_le_iff₀ hsqrt_pos).2 <| by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      rw [hmin]
      exact hdiv
    · have hmin : min α 1 = 1 := min_eq_right (le_of_not_ge hα_le_one)
      have hmin_sq : min (α ^ (2 : ℕ)) 1 = 1 := by
        refine min_eq_right ?_
        nlinarith [le_of_not_ge hα_le_one]
      have hden_pos : 0 < ε ^ (2 : ℕ) := by
        positivity
      have hC_sq :
          C ^ (2 : ℕ) ≤ ((k : ℝ) + 2) * ε ^ (2 : ℕ) := by
        have hbound :
            C ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 2 := by
          have hbound' := hk_shifted
          rwa [hmin_sq, one_mul] at hbound'
        exact (div_le_iff₀ hden_pos).mp hbound
      have hsquare :
          C ^ (2 : ℕ) ≤ (Real.sqrt ((k : ℝ) + 2) * ε) ^ (2 : ℕ) := by
        have hk_nonneg : 0 ≤ (k : ℝ) + 2 := by
          positivity
        nlinarith [hC_sq, Real.sq_sqrt hk_nonneg]
      have hmul : C ≤ Real.sqrt ((k : ℝ) + 2) * ε := by
        exact (sq_le_sq₀ hC_nonneg (mul_nonneg (le_of_lt hsqrt_pos) (le_of_lt hε))).mp hsquare
      have hdiv : C / Real.sqrt ((k : ℝ) + 2) ≤ ε := by
        exact (div_le_iff₀ hsqrt_pos).2 <| by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      rw [hmin]
      simpa using hdiv
  · have hC_nonpos : C ≤ 0 := le_of_not_ge hC_nonneg
    have hleft_nonpos : C / Real.sqrt ((k : ℝ) + 2) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hC_nonpos (le_of_lt hsqrt_pos)
    linarith

-- Route correction: the corollary now follows directly from the repaired Theorem 8.48 API on
-- `partialAvg k`. The only remaining bridge is the arithmetic step turning the displayed
-- `O(1 / ε^2)` threshold into the denominator `α * √(k + 2)` used in the feasibility bound.

/-- Helper for Corollary 8.49: the complexity threshold also forces the feasibility-rate
denominator `α * √(k + 2)` from Theorem 8.48 to be small enough to yield a final `≤ ε` bound. -/
lemma constraintRateDivAlpha_le_epsilonOfComplexity
    (hε : 0 < ε) (hα : 0 < α) {k : ℕ}
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    C / (α * Real.sqrt ((k : ℝ) + 2)) ≤ ε := by
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
    positivity
  have hrate :
      C / Real.sqrt ((k : ℝ) + 2) ≤ min α 1 * ε :=
    dual_projected_subgradient_partial_average_rate_le_min_alpha_mul_epsilon
      (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L) lam0 (xBar := xBar)
      hε hα hk_complexity
  by_cases hα_le_one : α ≤ 1
  · have hrate' : C / Real.sqrt ((k : ℝ) + 2) ≤ α * ε := by
      have hrate' := hrate
      rwa [min_eq_left hα_le_one] at hrate'
    have hmul : C ≤ ε * (α * Real.sqrt ((k : ℝ) + 2)) := by
      -- Multiply the rate estimate by `√(k + 2)` to recover the target denominator.
      have hscaled : C ≤ α * ε * Real.sqrt ((k : ℝ) + 2) :=
        (div_le_iff₀ hsqrt_pos).mp hrate'
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact (div_le_iff₀ (mul_pos hα hsqrt_pos)).mpr hmul
  · have hα_ge_one : 1 ≤ α := le_of_not_ge hα_le_one
    have hrate' : C / Real.sqrt ((k : ℝ) + 2) ≤ ε := by
      have hrate' := hrate
      rw [min_eq_right hα_ge_one, one_mul] at hrate'
      exact hrate'
    have hbase : C ≤ ε * Real.sqrt ((k : ℝ) + 2) :=
      (div_le_iff₀ hsqrt_pos).mp hrate'
    have hmono :
        ε * Real.sqrt ((k : ℝ) + 2) ≤ ε * (α * Real.sqrt ((k : ℝ) + 2)) := by
      -- When `α ≥ 1`, enlarging the denominator only improves the feasibility estimate.
      have hnonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 2) := by
        positivity
      calc
        ε * Real.sqrt ((k : ℝ) + 2) = (ε * Real.sqrt ((k : ℝ) + 2)) * 1 := by ring
        _ ≤ (ε * Real.sqrt ((k : ℝ) + 2)) * α := by
            exact mul_le_mul_of_nonneg_left hα_ge_one hnonneg
        _ = ε * (α * Real.sqrt ((k : ℝ) + 2)) := by ring
    exact (div_le_iff₀ (mul_pos hα hsqrt_pos)).mpr (le_trans hbase hmono)

-- Proof sketch: use the two bounds from Theorem 8.48 for the partial averaging iterate. The
-- complexity hypothesis first yields
-- `C / √(k + 2) ≤ min α 1 * ε`, so Theorem 8.48 gives both the objective and positive-part
-- feasibility estimates at level `ε`. Then `partialAverageMem` supplies the `x ∈ X` component
-- needed to package the three conditions through `is_epsilon_optimal_and_feasible_solution`.
/-- Corollary 8.49: under the hypotheses of Theorem 8.48, if `k ≥ 2` satisfies the displayed
`O(1 / ε^2)` iteration bound, then the partial averaging iterate `x^(k)` is an `ε`-optimal and
feasible solution in the sense of Definition 8.23. -/
theorem dual_projected_subgradient_partial_average_is_epsilon_optimal_and_feasible_solution
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    is_epsilon_optimal_and_feasible_solution f X gVec fOpt ε (partialAvg k) := by
  have hmem : partialAvg k ∈ X :=
    partialAverageMem
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
      (xSel := xSel) (lam0 := lam0) h_problem h_admissible
  have hrate :
      C / Real.sqrt ((k : ℝ) + 2) ≤ min α 1 * ε :=
    dual_projected_subgradient_partial_average_rate_le_min_alpha_mul_epsilon
      (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L) lam0 (xBar := xBar)
      hε hα hk_complexity
  have hrate_le_epsilon : C / Real.sqrt ((k : ℝ) + 2) ≤ ε := by
    -- The objective-side rate only needs the weaker comparison `min α 1 ≤ 1`.
    refine le_trans hrate ?_
    simpa using
      (mul_le_mul_of_nonneg_right (min_le_right α 1) (le_of_lt hε))
  have hobj :
      f (partialAvg k) - fOpt ≤ ε := by
    -- Specialize the Theorem 8.48 objective estimate and plug in the complexity threshold.
    refine le_trans
      (dual_projected_subgradient_partial_average_objective_gap_le
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (qOpt := qOpt) (L := L) (xSel := xSel) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hk)
      hrate_le_epsilon
  have hviol :
      positive_constraint_violation gVec (partialAvg k) ≤ ε := by
    -- The feasibility-side estimate uses the dedicated `α * √(k + 2)` adapter above.
    refine le_trans
      (dual_projected_subgradient_partial_average_constraint_norm_le
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (qOpt := qOpt) (L := L) (xSel := xSel) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hα hk)
      (constraintRateDivAlpha_le_epsilonOfComplexity
        (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L) lam0 (xBar := xBar)
        hε hα hk_complexity)
  -- Assemble the feasible-membership, objective-gap, and positive-part residual bounds.
  rw [is_epsilon_optimal_and_feasible_solution_iff]
  exact ⟨hmem, hobj, hviol⟩

-- Proof sketch: unpack
-- `dual_projected_subgradient_partial_average_is_epsilon_optimal_and_feasible_solution`
-- using `is_epsilon_optimal_and_feasible_solution_iff`, then bound the maximum of the objective
-- gap and positive-part constraint residual by `ε`.
/-- Unpacking Corollary 8.49 recovers the combined max-bound form: both the objective gap and the
positive-part constraint violation are at most `ε`, hence their maximum is bounded by `ε`. -/
theorem dual_projected_subgradient_partial_average_complexity_max_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    max (f (partialAvg k) - fOpt) (positive_constraint_violation gVec (partialAvg k)) ≤ ε := by
  have hmain :
      is_epsilon_optimal_and_feasible_solution f X gVec fOpt ε (partialAvg k) :=
    dual_projected_subgradient_partial_average_is_epsilon_optimal_and_feasible_solution
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
      (qOpt := qOpt) (L := L) (xSel := xSel) (lam0 := lam0)
      h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hε hα hk hk_complexity
  -- Unpack the main corollary and package the two scalar estimates as a single max bound.
  rw [is_epsilon_optimal_and_feasible_solution_iff] at hmain
  exact max_le_iff.mpr ⟨hmain.2.1, hmain.2.2⟩

-- Proof sketch: apply `le_trans` with `le_max_left _ _` to
-- `dual_projected_subgradient_partial_average_complexity_max_le_epsilon`.
/-- The complexity threshold from Corollary 8.49 implies the objective-gap estimate
`f(x^(k)) - fOpt ≤ ε`. -/
theorem dual_projected_subgradient_partial_average_objective_gap_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    f (partialAvg k) - fOpt ≤ ε := by
  -- Project the objective component from the combined max estimate.
  exact le_trans (le_max_left _ _)
    (dual_projected_subgradient_partial_average_complexity_max_le_epsilon
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
      (qOpt := qOpt) (L := L) (xSel := xSel) (lam0 := lam0)
      h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hε hα hk hk_complexity)

-- Proof sketch: project the feasibility component from
-- `dual_projected_subgradient_partial_average_is_epsilon_optimal_and_feasible_solution` using
-- `is_epsilon_optimal_and_feasible_solution_iff`.
/-- The complexity threshold from Corollary 8.49 also implies that the positive-part constraint
violation of `x^(k)` is at most `ε`. -/
theorem dual_projected_subgradient_partial_average_positive_constraint_violation_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    positive_constraint_violation gVec (partialAvg k) ≤ ε := by
  have hmain :
      is_epsilon_optimal_and_feasible_solution f X gVec fOpt ε (partialAvg k) :=
    dual_projected_subgradient_partial_average_is_epsilon_optimal_and_feasible_solution
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
      (qOpt := qOpt) (L := L) (xSel := xSel) (lam0 := lam0)
      h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hε hα hk hk_complexity
  -- Unpack the feasibility component from the Definition 8.23 predicate.
  rw [is_epsilon_optimal_and_feasible_solution_iff] at hmain
  exact hmain.2.2

end
