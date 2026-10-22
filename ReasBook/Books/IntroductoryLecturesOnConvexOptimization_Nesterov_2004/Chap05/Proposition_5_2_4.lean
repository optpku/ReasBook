/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics Filter
open scoped StronglyConvexHalfGapIndex
open scoped StronglyConvexScaledGap

/- Proposition 5.2.4 lies in the Chapter 5 strongly-convex complexity-threshold domain.

Sampled owner declarations in this domain:
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the source-facing owner for the textbook
  threshold index `k_p`;
* `stronglyConvexHalfGapIndex_le_of_mem` in `Definition_5_2_10`, the canonical least-element
  consequence saying that any admissible positive index bounds `k_p` from above;
* `stronglyConvexScaledGap` and its scoped notation `Δ` in `Proposition_5_2_3`, the chapter owner
  for the scaled gap `M_f * √Δ₀`;
* `Asymptotics.IsBigO.of_bound` in mathlib, the canonical asymptotic bridge from a pointwise
  estimate to `=O[atTop]`.

Source/core/bridge triage:
* source-facing: Proposition 5.2.4 itself, asserting the asymptotic growth rate of `k_p`;
* core/canonical: `stronglyConvexHalfGapIndex`, `stronglyConvexScaledGap`, and `=O[atTop]`;
* bridge/view: the passage from the explicit admissibility inequality defining `k_p` to the
  asymptotic comparison with `Δ^(1 / p)`.

Primitive data:
* the strong-convexity scaling constant `Mf`;
* the exponent `p`;
* the source-facing threshold index owner `stronglyConvexHalfGapIndex`.

Derived API:
* the asymptotic estimate
  `stronglyConvexHalfGapIndex c Mf p =O[atTop] fun Δ₀ ↦ (Δ Mf Δ₀) ^ (1 / p)`.

The target asymptotic comparison is only faithful in the nondegenerate regime `0 < Mf`: when
`Mf = 0`, the defining admissibility inequality is already true at `k = 1`, so
`stronglyConvexHalfGapIndex c 0 p Δ₀ = 1` while `Δ 0 Δ₀ = 0`.

This file stays source-facing. The only local duplicate wheel was a second `Δ` notation; the
refinement deletes that copy and reuses the chapter-owned scoped notation directly. -/

-- Proof sketch: solve the defining half-gap inequality from
-- `stronglyConvexHalfGapIndex` for the threshold index `k_p`, obtain a pointwise bound by a
-- constant multiple of `(M_f * √(f(x₀) - f*))^(1 / p)`, and then pass to the canonical asymptotic
-- bridge `=O[atTop]` using the chapter owner notation `Δ`. The public statement excludes the
-- degenerate case `M_f = 0`, since then the threshold index is constantly `1` but the comparison
-- function vanishes identically.
/-- Proposition 5.2.4: the index `k_p` from Definition 5.2.10 grows at most on the order of
`Δ_f(x₀)^(1 / p)`, expressed here as `(Δ M_f (f(x₀) - f*))^(1 / p)`. The asymptotic target is
nontrivial only in the source-relevant regime `M_f > 0`, which is therefore part of the theorem
surface.
-/
theorem stronglyConvexHalfGapIndex_isBigO_scaledGap_rpow
    (c p : ℝ) (Mf : NNReal) (hMf : 0 < Mf) (hp : 0 < p) :
    (fun initialGap ↦ (k[c, Mf; p](initialGap) : ℝ)) =O[atTop]
      (fun initialGap ↦ Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)) := by
  let A : ℝ := Real.rpow (2 : ℝ) (7 / 2 : ℝ) * max c 0
  let B : ℝ := Real.rpow A (1 / p) + 1
  refine Asymptotics.IsBigO.of_bound (B + 1) ?_
  refine Filter.eventually_atTop.2 ?_
  refine ⟨max 1 ((1 / (Mf : ℝ)) ^ (2 : ℕ)), fun initialGap hGap ↦ ?_⟩
  have hMfR : 0 < (Mf : ℝ) := hMf
  have hgap_nonneg : 0 ≤ initialGap := le_trans (by positivity) hGap
  have hgap : 0 < initialGap := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hGap)
  let gapScale : ℝ := Δ (Mf : ℝ) initialGap
  let target : ℝ := Real.rpow gapScale (1 / p)
  let n : ℕ := Nat.ceil (B * target)
  have hgapScale_nonneg : 0 ≤ gapScale := by
    dsimp [gapScale]
    exact mul_nonneg hMfR.le (Real.sqrt_nonneg _)
  have hsqrt : 1 / (Mf : ℝ) ≤ Real.sqrt initialGap := by
    refine (Real.le_sqrt (by positivity) hgap_nonneg).2 ?_
    exact le_trans (le_max_right _ _) hGap
  have hgapScale_ge_one : 1 ≤ gapScale := by
    calc
      1 = (Mf : ℝ) * (1 / (Mf : ℝ)) := by field_simp [hMfR.ne']
      _ ≤ (Mf : ℝ) * Real.sqrt initialGap := by
        gcongr
      _ = gapScale := by rfl
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    exact Real.rpow_nonneg hgapScale_nonneg _
  have htarget_ge_one : 1 ≤ target := by
    dsimp [target]
    exact Real.one_le_rpow hgapScale_ge_one (by positivity)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAroot_nonneg : 0 ≤ Real.rpow A (1 / p) := by
    exact Real.rpow_nonneg hA_nonneg _
  have hAroot_pow : Real.rpow A (1 / p) ^ p = A := by
    simpa [one_div] using Real.rpow_inv_rpow hA_nonneg (show p ≠ 0 by linarith)
  have hAroot_le_B : Real.rpow A (1 / p) ≤ B := by
    dsimp [B]
    linarith
  have hA_le_Bpow : A ≤ B ^ p := by
    rw [← hAroot_pow]
    exact Real.rpow_le_rpow hAroot_nonneg hAroot_le_B hp.le
  have htarget_pow : target ^ p = gapScale := by
    dsimp [target]
    simpa [one_div] using Real.rpow_inv_rpow hgapScale_nonneg (show p ≠ 0 by linarith)
  have hBn_nonneg : 0 ≤ B * target := mul_nonneg hB_nonneg htarget_nonneg
  have hn_pos_real : (1 : ℝ) ≤ n := by
    have hB_ge_one : 1 ≤ B := by
      linarith
    have hBtarget_ge_one : 1 ≤ B * target := by
      nlinarith [hB_ge_one, htarget_ge_one, hB_nonneg, htarget_nonneg]
    exact le_trans hBtarget_ge_one (Nat.le_ceil _)
  have hn_pos : 1 ≤ n := by
    exact_mod_cast hn_pos_real
  have hBtarget_pow_le : (B * target) ^ p ≤ (n : ℝ) ^ p := by
    exact Real.rpow_le_rpow hBn_nonneg (Nat.le_ceil _) hp.le
  have hA_gapScale_le_npow : A * gapScale ≤ (n : ℝ) ^ p := by
    calc
      A * gapScale ≤ B ^ p * gapScale := by
        gcongr
      _ = (B * target) ^ p := by
        rw [Real.mul_rpow hB_nonneg htarget_nonneg, htarget_pow]
      _ ≤ (n : ℝ) ^ p := hBtarget_pow_le
  have htwo :
      Real.rpow (2 : ℝ) (7 / 2 : ℝ) = 2 * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by
    calc
      Real.rpow (2 : ℝ) (7 / 2 : ℝ) = Real.rpow (2 : ℝ) ((5 / 2 : ℝ) + 1) := by norm_num
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * Real.rpow (2 : ℝ) (1 : ℝ) := by
        simpa using
          (Real.rpow_add (show 0 < (2 : ℝ) by positivity) (5 / 2 : ℝ) (1 : ℝ))
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * 2 := by simp
      _ = 2 * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by ring
  have hgap32 : Real.rpow initialGap (3 / 2 : ℝ) = initialGap * Real.sqrt initialGap := by
    calc
      Real.rpow initialGap (3 / 2 : ℝ) = Real.rpow initialGap ((1 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow initialGap (1 : ℝ) * Real.rpow initialGap (1 / 2 : ℝ) := by
        simpa using
          (Real.rpow_add hgap (1 : ℝ) (1 / 2 : ℝ))
      _ = initialGap * Real.sqrt initialGap := by simp [Real.sqrt_eq_rpow]
  have hnum_rewrite :
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
        initialGap / 2 * (A * gapScale) := by
    change
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
        initialGap / 2 *
          (Real.rpow (2 : ℝ) (7 / 2 : ℝ) * max c 0 * ((Mf : ℝ) * Real.sqrt initialGap))
    rw [hgap32, htwo]
    ring
  have hnpow_pos : 0 < (n : ℝ) ^ p := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn_pos) _
  have hineq_max :
      (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) *
          Real.rpow initialGap (3 / 2 : ℝ)) /
        (n : ℝ) ^ p ≤
      initialGap / 2 := by
    refine (div_le_iff₀ hnpow_pos).2 ?_
    calc
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) =
          initialGap / 2 * (A * gapScale) := hnum_rewrite
      _ ≤ initialGap / 2 * (n : ℝ) ^ p := by
        exact mul_le_mul_of_nonneg_left hA_gapScale_le_npow (by positivity)
  have hnum_c_le :
      Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) ≤
        Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) := by
    have hfactor_nonneg :
        0 ≤ Real.rpow (2 : ℝ) (5 / 2 : ℝ) * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (2 : ℝ)) _) hMfR.le)
        (Real.rpow_nonneg hgap_nonneg _)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (le_max_left c 0) hfactor_nonneg
  have hnum_mono :
      (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
          (n : ℝ) ^ p ≤
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * max c 0 * (Mf : ℝ) *
            Real.rpow initialGap (3 / 2 : ℝ)) /
          (n : ℝ) ^ p := by
    exact div_le_div_of_nonneg_right hnum_c_le hnpow_pos.le
  have hn_mem : n ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap := by
    rw [mem_stronglyConvexHalfGapAdmissibleIndices_iff]
    exact ⟨hn_pos, hnum_mono.trans hineq_max⟩
  have hk_le_n : k[c, Mf; p](initialGap) ≤ n :=
    stronglyConvexHalfGapIndex_le_of_mem c Mf p initialGap hn_mem
  have hk_bound :
      (k[c, Mf; p](initialGap) : ℝ) ≤ (B + 1) * target := by
    calc
      (k[c, Mf; p](initialGap) : ℝ) ≤ n := by exact_mod_cast hk_le_n
      _ ≤ B * target + 1 := (Nat.ceil_lt_add_one hBn_nonneg).le
      _ ≤ B * target + target := by
        gcongr
      _ = (B + 1) * target := by ring
  calc
    ‖(k[c, Mf; p](initialGap) : ℝ)‖ = (k[c, Mf; p](initialGap) : ℝ) := by
      simp
    _ ≤ (B + 1) * target := hk_bound
    _ = (B + 1) * |Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)| := by
      have htarget_expr_nonneg : 0 ≤ Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p) := by
        simpa [gapScale, target] using htarget_nonneg
      have htarget_eq_abs : target = |Real.rpow (Δ (Mf : ℝ) initialGap) (1 / p)| := by
        dsimp [target]
        simpa [gapScale] using (abs_of_nonneg htarget_expr_nonneg).symm
      rw [htarget_eq_abs]
