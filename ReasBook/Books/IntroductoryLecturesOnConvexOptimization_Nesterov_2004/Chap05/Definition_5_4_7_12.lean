/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "LPoint" => E × E × ℝ × ℝ

/- Definition 5.4.7.12 lies in the Chapter 5 log-sum-exp epigraph / lifted exponential-cone
domain.

Sampled owner declarations:
* `exponentialCone` from `Definition_5_4_7_10`, the Chapter 5 source-facing scalar cone owner;
* `mem_exponentialCone_iff` from `Definition_5_4_7_10`, the scalar membership bridge for that
  owner;
* `logSumExpEpigraphCone` from `Definition_5_4_7_11`, the unlifted conic log-sum-exp epigraph
  owner on the same finite index family, obtained after forgetting the slack coordinates
  `y`.
* `mem_logSumExpEpigraphCone_iff` from `Definition_5_4_7_11`, the canonical owner-level
  membership bridge on that same finite-family ambient space.

Source/core/bridge triage:
* source-facing: `liftedConeLogSumExp`, the lifted cone `hat Q`;
* core/canonical: the earlier scalar owner `exponentialCone`;
* bridge/view: the coordinate map `i ↦ ((x i - t, y i), τ)` together with the normalization
  equation `∑ i, y i = τ`.

Primitive data:
* coordinatewise membership in the scalar exponential cone;
* the normalization equation `∑ i, y i = τ`.

Derived API:
* the membership bridge `mem_liftedConeLogSumExp_iff`, which keeps the lifted cone expressed
  through the scalar cone owner rather than re-expanding to raw inequalities;
* the owner-to-owner bridge `mem_logSumExpEpigraphCone_of_mem_liftedConeLogSumExp`, sending a
  lifted feasible point to the corresponding point of the canonical conic epigraph owner
  `logSumExpEpigraphCone`.

This refinement removes the recall-only surface and restores Definition 5.4.7.12 as the owner
file for the lifted log-sum-exp cone. The public definition now grows from the earlier
source-facing owner `exponentialCone`, exactly as the analogous lifted `ℓ_p` file grows from
`powerCone`, instead of bypassing the chapter owner with a raw coordinate inequality set. The
ambient family is now parameterized by an arbitrary finite index type `ι`, matching the upstream
owner `logSumExpEpigraphCone`; the textbook coordinate model `Fin n` is recovered by
specialization, and the nonempty-family hypothesis is only used where the projection theorem needs
one coordinate to read off the positivity of `τ`.
-/

/-- Definition 5.4.7.12: the lifted cone `hat Q` for the log-sum-exp epigraph consists of the
quadruples `(x, y, t, τ)` such that each coordinate triple `((x^(i) - t, y^(i)), τ)` lies in the
scalar exponential cone and the slack variables satisfy the normalization equation
`∑ i, y^(i) = τ`. -/
def liftedConeLogSumExp : Set LPoint
  | (x, y, t, τ) =>
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ

/-- A quadruple `(x, y, t, τ)` belongs to `liftedConeLogSumExp` exactly when each coordinate
triple `((x^(i) - t, y^(i)), τ)` belongs to `exponentialCone` and `∑ i, y^(i) = τ`. -/
theorem mem_liftedConeLogSumExp_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExp ↔
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ :=
  Iff.rfl

/-- A lifted feasible point `(x, y, t, τ)` projects to a feasible point `(x, t, τ)` of the
canonical log-sum-exp epigraph cone. This is the owner-level bridge from the lifted source-facing
cone `hat Q` to the earlier conic epigraph owner `logSumExpEpigraphCone`. -/
theorem mem_logSumExpEpigraphCone_of_mem_liftedConeLogSumExp
    [Nonempty ι] {x y : E} {t τ : ℝ}
    (h : (x, y, t, τ) ∈ liftedConeLogSumExp) :
    (x, t, τ) ∈ logSumExpEpigraphCone := by
  classical
  rw [mem_liftedConeLogSumExp_iff] at h
  rcases h with ⟨hcone, hsum⟩
  let i0 : ι := Classical.choice inferInstance
  have hτ : 0 < τ := (mem_exponentialCone_iff (x i0 - t) (y i0) τ).1 (hcone i0) |>.2
  let s : ℝ := ∑ i : ι, Real.exp (x i / τ)
  have hy_div (i : ι) : Real.exp ((x i - t) / τ) ≤ y i / τ := by
    have hi : τ * Real.exp ((x i - t) / τ) ≤ y i :=
      (mem_exponentialCone_iff (x i - t) (y i) τ).1 (hcone i) |>.1
    exact (le_div_iff₀ hτ).2 <| by simpa [mul_comm] using hi
  have hsum_div :
      ∑ i : ι, Real.exp ((x i - t) / τ) ≤ ∑ i : ι, y i / τ :=
    Finset.sum_le_sum fun i _ ↦ hy_div i
  have hy_norm : ∑ i : ι, y i / τ = 1 := by
    rw [← Finset.sum_div, hsum, div_self hτ.ne']
  have hshift :
      ∑ i : ι, Real.exp ((x i - t) / τ) = Real.exp (-t / τ) * s := by
    calc
      ∑ i : ι, Real.exp ((x i - t) / τ)
          = ∑ i : ι, Real.exp (x i / τ) * Real.exp (-t / τ) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [sub_eq_add_neg, add_div, neg_div, Real.exp_add]
      _ = (∑ i : ι, Real.exp (x i / τ)) * Real.exp (-t / τ) := by
            rw [Finset.sum_mul]
      _ = Real.exp (-t / τ) * s := by
            dsimp [s]
            rw [mul_comm]
  have hs_le : Real.exp (-t / τ) * s ≤ 1 := by
    simpa [hshift, hy_norm] using hsum_div
  have hs_pos : 0 < s := by
    have hs_ge : Real.exp (x i0 / τ) ≤ s := by
      dsimp [s]
      change Real.exp (x i0 / τ) ≤ ∑ i : ι, Real.exp (x i / τ)
      exact
        Finset.single_le_sum
          (fun i _ ↦ (Real.exp_pos (x i / τ)).le)
          (show i0 ∈ (Finset.univ : Finset ι) from by simp)
    exact lt_of_lt_of_le (Real.exp_pos (x i0 / τ)) hs_ge
  have hs_le_exp : s ≤ Real.exp (t / τ) := by
    have hs_le_div : s ≤ 1 / Real.exp (-t / τ) := by
      exact (le_div_iff₀ (Real.exp_pos (-t / τ))).2 <| by simpa [mul_comm] using hs_le
    simpa [one_div, neg_div, Real.exp_neg] using hs_le_div
  have hlog : Real.log s ≤ t / τ :=
    (Real.log_le_iff_le_exp hs_pos).2 hs_le_exp
  have hmem : τ * Real.log s ≤ t := by
    simpa [mul_comm] using (le_div_iff₀ hτ).1 hlog
  rw [mem_logSumExpEpigraphCone_iff x t τ]
  refine ⟨hτ, ?_⟩
  simpa [logSumExp, s, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmem

end
