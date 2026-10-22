/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Theorem 7.2 lies in the chapter's relative-accuracy / lower-level subgradient-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the scalar radius-parameter owner used in
  Chapter 7;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, whose lower-level scheme
  input has type `ℕ → ℝ → X`;
- `schemeSNRestartingStep` in `Algorithm_7_4.lean`, which uses the same scalar-parameter scheme
  surface;
- `direct_structure_iterate_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_4.lean`, the
  sibling relative-error conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.2's conversion from a stagewise subgradient-approximation gap bound to
  a one-shot relative-value guarantee;
- core/canonical: a lower-level scheme `G : ℕ → ℝ → X` evaluated at a scalar radius parameter
  `rhoHat`;
- bridge/view: the specific floor-chosen index `⌊1 / (α⁴ δ²)⌋`.

Primitive data:
- `f`, `G`, `rhoHat`, `α`, `δ`, and `fStar`;
- the stagewise estimate for `G k rhoHat`.

Derived API:
- the chosen stage index `⌊1 / (α⁴ δ²)⌋`;
- the final relative-value inequality.

This file keeps the source-facing theorem directly, but it aligns the scheme input with the
chapter's canonical scalar-parameter owner surface and exposes the active scalar side conditions
instead of a stronger interval wrapper plus a hidden sign assumption on `fStar`.
-/

variable {X : Type u}

/-- Helper for Theorem 7.2: the floor-chosen stage is strictly below its successor bound. -/
lemma chosen_subgradient_floor_lt_succ (α δ : ℝ) :
    (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) : ℝ) <
      (Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ))) : ℝ) + 1 := by
  -- The floor comparison is the bridge from the chosen integer stage to the real bound on `N + 1`.
  simpa using Nat.lt_floor_add_one (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))

/-- Helper for Theorem 7.2: the floor-chosen stage makes the stagewise coefficient at most `δ`. -/
lemma chosen_subgradient_coefficient_le_delta
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    1 / (α ^ (2 : ℕ) *
        Real.sqrt ((Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ))) : ℝ) + 1)) ≤ δ := by
  let N : ℕ := Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))
  have hFloor : (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) : ℝ) < (N : ℝ) + 1 := by
    -- The floor inequality identifies the lower bound on `N + 1` used in the source proof.
    simpa [N] using chosen_subgradient_floor_lt_succ α δ
  have hDenom_pos : 0 < α ^ (4 : ℕ) * δ ^ (2 : ℕ) := by
    positivity
  have hN1_nonneg : 0 ≤ (N : ℝ) + 1 := by
    positivity
  have hCoeffDenom_pos : 0 < α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1) := by
    positivity
  have hMul : 1 < ((N : ℝ) + 1) * (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) := by
    -- Multiplying by the positive denominator turns the floor estimate into a product bound.
    exact (div_lt_iff₀ hDenom_pos).1 hFloor
  have hSquareIdentity :
      (δ * (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1))) ^ (2 : ℕ) =
        ((N : ℝ) + 1) * (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) := by
    -- Rewriting the product bound as a square prepares the monotone square-root step.
    calc
      (δ * (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1))) ^ (2 : ℕ)
          = δ ^ (2 : ℕ) * ((α ^ (2 : ℕ)) ^ (2 : ℕ) * (Real.sqrt ((N : ℝ) + 1)) ^ (2 : ℕ)) := by
              ring
      _ = δ ^ (2 : ℕ) * (α ^ (4 : ℕ) * ((N : ℝ) + 1)) := by
            rw [← pow_mul, Real.sq_sqrt hN1_nonneg]
      _ = ((N : ℝ) + 1) * (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) := by
            ring
  have hSquare : 1 < (δ * (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1))) ^ (2 : ℕ) := by
    -- The floor estimate now says the squared coefficient is already above `1`.
    rw [hSquareIdentity]
    exact hMul
  have hMainFactor_nonneg : 0 ≤ δ * (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1)) := by
    positivity
  have hMainFactor_gt_one : 1 < δ * (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1)) := by
    -- Nonnegativity lets us pass back from a square lower bound to the unsquared factor.
    exact (one_lt_sq_iff₀ hMainFactor_nonneg).1 hSquare
  have hInv : (α ^ (2 : ℕ) * Real.sqrt ((N : ℝ) + 1))⁻¹ ≤ δ := by
    -- Converting the lower bound on `δ * (...)` gives the desired reciprocal estimate.
    rw [inv_le_iff_one_le_mul₀ hCoeffDenom_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hMainFactor_gt_one.le
  simpa [one_div, N] using hInv

/-- Helper for Theorem 7.2: once the chosen coefficient is bounded by `δ`,
the iterate gap is at most `δ f*`. -/
lemma chosen_subgradient_gap_le_delta_mul_optimal_value
    (f : X → ℝ) (G : ℕ → ℝ → X) (rhoHat α δ fStar : ℝ) (N : ℕ)
    (hfStar_nonneg : 0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (G k rhoHat) - fStar ≤
          (1 / (α ^ (2 : ℕ) * Real.sqrt (k + 1 : ℝ))) * fStar)
    (hCoeff : 1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ)) ≤ δ) :
    f (G N rhoHat) - fStar ≤ δ * fStar := by
  have hScaled : (1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ))) * fStar ≤ δ * fStar := by
    -- Scaling the scalar coefficient bound by the nonnegative optimal value keeps the inequality.
    exact mul_le_mul_of_nonneg_right hCoeff hfStar_nonneg
  -- Specializing the stagewise estimate at the chosen index closes the gap bound.
  exact (hEstimate N).trans hScaled

-- Proof sketch: apply the assumed estimate at
-- `N = Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))`, then use
-- `Nat.floor_lt_add_one` to deduce `1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) ≤ N + 1` and hence
-- `1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ)) ≤ δ` from `0 < α` and `0 < δ`, then multiply by
-- `fStar` using `0 ≤ fStar`.
/-- Theorem 7.2 [Chapter7_1.json:15]: if `α` and `δ` are positive,
`fStar` is nonnegative, and every iterate `G k rhoHat` satisfies the
subgradient approximation estimate
`f (G k rhoHat) - fStar ≤ (1 / (α^2 * √(k + 1))) * fStar`, then the
iterate with index `⌊1 / (α^4 δ^2)⌋` satisfies
`f (G_N rhoHat) ≤ (1 + δ) fStar`. -/
theorem subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value
    (f : X → ℝ) (G : ℕ → ℝ → X) (rhoHat α δ fStar : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hfStar_nonneg : 0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (G k rhoHat) - fStar ≤
          (1 / (α ^ (2 : ℕ) * Real.sqrt (k + 1 : ℝ))) * fStar) :
    f (G (Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))) rhoHat) ≤ (1 + δ) * fStar := by
  let N : ℕ := Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))
  have hCoeff :
      1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ)) ≤ δ := by
    -- The floor choice of `N` gives exactly the coefficient bound needed at stage `N`.
    simpa [N] using chosen_subgradient_coefficient_le_delta α δ hα hδ
  have hGap : f (G N rhoHat) - fStar ≤ δ * fStar := by
    -- The source estimate at stage `N` converts directly into the desired gap bound.
    exact chosen_subgradient_gap_le_delta_mul_optimal_value
      f G rhoHat α δ fStar N hfStar_nonneg hEstimate hCoeff
  have hValue : f (G N rhoHat) ≤ δ * fStar + fStar := by
    -- Rearranging the gap bound isolates the iterate value on the left-hand side.
    exact (sub_le_iff_le_add.1 hGap)
  -- The final algebraic rewrite matches the source statement's `(1 + δ) f*` form.
  calc
    f (G N rhoHat) ≤ δ * fStar + fStar := hValue
    _ = (1 + δ) * fStar := by ring

end
