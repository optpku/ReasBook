/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 4.2.15 lies in the chapter's false-acceleration objective-gap transfer domain.

Sampled neighboring declarations:
* `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` in `Theorem_4_2_3`, the chapter's
  owner inverse-cubic objective-gap estimate for accelerated cubic Newton iterates;
* `false_acceleration_gap_ge_gap_to_next_iterate_of_isMinOn` in `Text_4_2_16`, the next scalar
  bridge statement in the same false-acceleration discussion;
* `false_acceleration_gap_le_inverse_eighth_rate` in `Text_4_2_17`, the downstream scalar
  consequence that reuses the chapter-standard nonnegative constants `L3` and `R`.

Best owner abstraction:
* source-facing: the displayed two-thirds-index objective-gap estimate
  `f (x hatK) - f xStar ≤ 3^3 L3 R^3 / N^3`;
* core/canonical: the scalar inverse-cubic gap profile `gap k ≤ (L3 * R^3) / k^3`;
* bridge/view: the companion specialization from the scalar profile to the objective-gap sequence
  `gap k = f (x k) - f xStar`.

Primitive data:
* the displayed indices `N` and `hatK`;
* the chapter-standard nonnegative constants `L3` and `R`.
* the objective `f`, iterate sequence `x`, and comparison point `xStar`.

Derived API:
* the scalar companion theorem obtained by abstracting the objective gaps to a sequence `gap`;
* positivity of the scalar prefactor, inherited from `L3 R : NNReal`.

The previous version made the scalar bridge theorem the main public entry and left the textbook
identification `gap k = f (x k) - f xStar` only in commentary. This refinement restores the
source-facing objective-gap statement as the main theorem and keeps the scalar inverse-cubic
algebra as a reusable companion.
-/

-- Proof sketch: apply the inverse-cubic estimate at the integer index `hatK`. Then use
-- `(hatK : ℝ) = (2 / 3) * N` to rewrite the denominator as `((2 / 3) * N)^3`, simplify this to
-- `(8 / 27) * N^3`, and compare the resulting factor `(27 / 8)` with `27 = 3^3`. The scalar
-- factor is nonnegative because the rate constants live in `NNReal`.
theorem inverse_cubic_gap_at_two_thirds_index_le_three_cubed_bound
    (gap : ℕ → ℝ) (N hatK : ℕ) (L3 R : NNReal)
    (hN : 0 < N)
    (hhatK : (hatK : ℝ) = (2 / 3 : ℝ) * (N : ℝ))
    (hgap :
      ∀ ⦃k : ℕ⦄, 1 ≤ k →
        gap k ≤
          ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (k : ℝ) ^ (3 : ℕ)) :
    gap hatK ≤
      ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hhatK_pos : 0 < (hatK : ℝ) := by
    rw [hhatK]
    positivity
  have hhatK_nat : 1 ≤ hatK := by
    exact Nat.succ_le_of_lt (by exact_mod_cast hhatK_pos)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real
  calc
    gap hatK ≤ ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (hatK : ℝ) ^ (3 : ℕ) :=
      hgap hhatK_nat
    _ = (27 / 8 : ℝ) * (((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (N : ℝ) ^ (3 : ℕ)) := by
      rw [hhatK]
      field_simp [hN_ne]
      ring
    _ ≤ (3 : ℝ) ^ (3 : ℕ) * (((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (N : ℝ) ^ (3 : ℕ)) := by
      gcongr
      norm_num
    _ = ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
      ring

/-- Text 4.2.15: if the objective gaps along an iterate sequence satisfy the inverse-cubic estimate
`gap k ≤ (L3 * R^3) / k^3` for every integer `k ≥ 1`, then at any index `hatK` with
`(hatK : ℝ) = (2 / 3) * N` one has
`f (x hatK) - f xStar ≤ 3^3 * L3 * R^3 / N^3`. -/
theorem false_acceleration_gap_at_two_thirds_index_le_three_cubed_bound
    {E : Type u} (f : E → ℝ) (x : ℕ → E) (xStar : E) (N hatK : ℕ) (L3 R : NNReal)
    (hN : 0 < N)
    (hhatK : (hatK : ℝ) = (2 / 3 : ℝ) * (N : ℝ))
    (hgap :
      ∀ ⦃k : ℕ⦄, 1 ≤ k →
        f (x k) - f xStar ≤
          ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (k : ℝ) ^ (3 : ℕ)) :
    f (x hatK) - f xStar ≤
      ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
  simpa using
    inverse_cubic_gap_at_two_thirds_index_le_three_cubed_bound
      (fun k ↦ f (x k) - f xStar) N hatK L3 R hN hhatK hgap
