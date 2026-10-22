/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: strong convergence implies weak convergence by continuity of the canonical map to
-- `WeakSpace ℝ 𝓗`, and it implies norm convergence by continuity of the norm. Conversely, test the
-- weak convergence against the fixed coordinate `y ↦ ⟪y, x⟫`, expand `‖xₙ - x‖²`, and use the
-- convergence of the norms to show the squared distances tend to `0`.
/-- Corollary 2.52: a sequence in a Hilbert space converges strongly to `x` if and only if it
converges weakly to `x` in the canonical weak topology `WeakSpace ℝ 𝓗` and its norms converge to
`‖x‖`. -/
theorem tendsto_iff_tendsto_weakly_and_tendsto_norm (xₙ : ℕ → 𝓗) (x : 𝓗) :
    Tendsto xₙ atTop (𝓝 x) ↔
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ∧
        Tendsto (fun n ↦ ‖xₙ n‖) atTop (𝓝 ‖x‖) := by
  constructor
  · intro hx
    constructor
    -- Send the strong limit through the canonical continuous map to the weak space.
    · simpa [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ 𝓗).continuous.tendsto x).comp hx
    -- Apply continuity of the norm to get convergence of the norm sequence.
    · simpa using (continuous_norm.tendsto x).comp hx
  · intro h
    rcases h with ⟨hWeak, hNorm⟩
    -- Recover strong convergence by showing that the squared norms of `xₙ - x` tend to `0`.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- Weak convergence gives convergence of the fixed-coordinate functional `y ↦ ⟪x, y⟫`.
    have hInner : Tendsto (fun n ↦ inner ℝ x (xₙ n)) atTop (𝓝 (‖x‖ ^ 2)) := by
      have hEval :
          Tendsto
            (fun n ↦
              ((topDualPairing ℝ 𝓗).flip (toWeakSpace ℝ 𝓗 (xₙ n))
                (InnerProductSpace.toDual ℝ 𝓗 x)))
            atTop
            (𝓝
              ((topDualPairing ℝ 𝓗).flip (toWeakSpace ℝ 𝓗 x)
                (InnerProductSpace.toDual ℝ 𝓗 x))) := by
        exact
          ((WeakBilin.eval_continuous ((topDualPairing ℝ 𝓗).flip)
              (InnerProductSpace.toDual ℝ 𝓗 x)).tendsto (toWeakSpace ℝ 𝓗 x)).comp hWeak
      change Tendsto (fun n ↦ inner ℝ x (xₙ n)) atTop (𝓝 (inner ℝ x x)) at hEval
      simpa [real_inner_self_eq_norm_sq] using hEval
    have hNormSq : Tendsto (fun n ↦ ‖xₙ n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
      simpa using hNorm.pow 2
    have hSqDiffEq :
        (fun n ↦ ‖xₙ n - x‖ ^ 2) =
          (fun n ↦ ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2) := by
      funext n
      calc
        ‖xₙ n - x‖ ^ 2 = inner ℝ (xₙ n - x) (xₙ n - x) := by
          rw [real_inner_self_eq_norm_sq]
        _ = inner ℝ (xₙ n) (xₙ n) - inner ℝ (xₙ n) x - inner ℝ x (xₙ n) + inner ℝ x x := by
          rw [inner_sub_right, inner_sub_left, inner_sub_left]
          ring
        _ = ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2 := by
          rw [real_inner_comm (xₙ n) x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
          ring
    have hSqDiff : Tendsto (fun n ↦ ‖xₙ n - x‖ ^ 2) atTop (𝓝 0) := by
      rw [hSqDiffEq]
      -- The polarization identity shows that all terms converge to cancel at `0`.
      have hTwoInner :
          Tendsto (fun n ↦ 2 * inner ℝ x (xₙ n)) atTop (𝓝 (2 * (‖x‖ ^ 2))) := by
        exact hInner.const_mul 2
      have hConst : Tendsto (fun _ : ℕ ↦ ‖x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
        tendsto_const_nhds
      have hSum :
          Tendsto (fun n ↦ ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2)
            atTop (𝓝 (‖x‖ ^ 2 - 2 * (‖x‖ ^ 2) + ‖x‖ ^ 2)) := by
        exact (hNormSq.sub hTwoInner).add hConst
      have hLimitZero : (‖x‖ ^ 2 - 2 * (‖x‖ ^ 2) + ‖x‖ ^ 2 : ℝ) = 0 := by
        ring
      simpa [hLimitZero] using hSum
    have hNormSub : Tendsto (fun n ↦ ‖xₙ n - x‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hSqEventually : ∀ᶠ n in atTop, dist (‖xₙ n - x‖ ^ 2) 0 < ε ^ 2 := by
        exact (Metric.tendsto_nhds.1 hSqDiff) (ε ^ 2) (sq_pos_of_pos hε)
      filter_upwards [hSqEventually] with n hn
      have hsquare_lt : ‖xₙ n - x‖ ^ 2 < ε ^ 2 := by
        simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg ‖xₙ n - x‖)] using hn
      -- Since norms are nonnegative, controlling the square controls the norm itself.
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (xₙ n - x))] using
        (sq_lt_sq₀ (norm_nonneg (xₙ n - x)) hε.le).1 hsquare_lt
    exact hNormSub
