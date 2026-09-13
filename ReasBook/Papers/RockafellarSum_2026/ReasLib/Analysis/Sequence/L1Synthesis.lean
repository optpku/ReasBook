/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Sequence.L1
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Summable sequence synthesis

This module develops norm and convergence estimates for synthesis from a
summable sequence of vectors.
-/

public section

noncomputable section

universe u

namespace L1Seq

/-- A uniform upper bound for the norms of a vector family is nonnegative. -/
private theorem synthesis_bound_nonneg
    {H : Type u} [NormedAddCommGroup H] (u : ℕ → H) {K : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ K) :
    0 ≤ K := by
  -- Compare the bound with the nonnegative norm at the zeroth coordinate.
  exact (norm_nonneg (u 0)).trans (hu 0)

/-- The scalar-multiplication maps associated to a uniformly bounded vector family
have the same uniform operator-norm bound. -/
private theorem synthesis_coordinate_norm_le
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) :
    ∀ n, ‖ContinuousLinearMap.toSpanSingleton ℝ (u n)‖ ≤ K := by
  -- The rank-one scalar-multiplication map has operator norm exactly `‖u n‖`.
  intro n
  simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hu n

/-- The continuous linear synthesis operator for a uniformly bounded vector family. -/
noncomputable def synthesis
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) :
    L1Seq →L[ℝ] H :=
  (lp.tsumCLM ℝ ℕ H).comp
    (lp.mapCLM 1 (fun n ↦ ContinuousLinearMap.toSpanSingleton ℝ (u n))
      (synthesis_bound_nonneg u hu) (synthesis_coordinate_norm_le u hu))

/-- The terms synthesized from an `L1Seq` element and a uniformly bounded vector family
are absolutely summable. -/
theorem summable_norm_smul
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) (a : L1Seq) :
    Summable (fun n ↦ ‖a n • u n‖) := by
  -- The mapped sequence belongs to `ℓ¹`, so its coordinate norms are summable.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hMapped :=
    (lp.mapCLM 1 (fun n ↦ ContinuousLinearMap.toSpanSingleton ℝ (u n))
      (synthesis_bound_nonneg u hu) (synthesis_coordinate_norm_le u hu) a).2.summable hOne
  -- Normalize exponent one and evaluate each scalar-multiplication map.
  simpa only [ENNReal.toReal_one, Real.rpow_one, lp.mapCLM_apply_coe,
    ContinuousLinearMap.toSpanSingleton_apply] using hMapped

/-- Applying `synthesis` gives the sum of the coordinatewise scalar multiples. -/
theorem synthesis_apply
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) (a : L1Seq) :
    synthesis u hu a = ∑' n, a n • u n := by
  -- Evaluate the outer composition, summation map, and coordinate maps in turn.
  simp only [synthesis, ContinuousLinearMap.comp_apply, lp.tsumCLM_apply, lp.mapCLM_apply_coe,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The operator norm of `synthesis` is at most the uniform bound on the vector family. -/
theorem norm_synthesis_le
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) :
    ‖synthesis u hu‖ ≤ K := by
  -- Bound the composition by the product of the two canonical operator bounds.
  calc
    ‖synthesis u hu‖ ≤
        ‖lp.tsumCLM ℝ ℕ H‖ *
          ‖lp.mapCLM 1 (fun n ↦ ContinuousLinearMap.toSpanSingleton ℝ (u n))
            (synthesis_bound_nonneg u hu) (synthesis_coordinate_norm_le u hu)‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * K := by
      exact mul_le_mul lp.norm_tsumCLM_le
        (lp.norm_mapCLM_le 1 (fun n ↦ ContinuousLinearMap.toSpanSingleton ℝ (u n))
          (synthesis_bound_nonneg u hu) (synthesis_coordinate_norm_le u hu))
        (norm_nonneg _) zero_le_one
    _ = K := one_mul K

end L1Seq
