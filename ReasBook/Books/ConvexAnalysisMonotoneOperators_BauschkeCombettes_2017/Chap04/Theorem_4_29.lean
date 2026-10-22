/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Theorem_4_27

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
universe u

open Function Set
open scoped InnerProductSpace

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Theorem 4.29: convexity keeps each affine regularization
`x ↦ α • x₀ + (1 - α) • T x` inside the set `D`. -/
private theorem regularized_map_mapsTo {D : Set H} (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) {x0 : H} (hx0 : x0 ∈ D) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D := by
  intro x hx
  -- Rewrite the affine combination as a line-map point of the segment `[T x, x₀]`.
  have hline : (AffineMap.lineMap (T x) x0) α ∈ D :=
    hD_convex.lineMap_mem (hTD hx) hx0 hα
  simpa [AffineMap.lineMap_apply, sub_eq_add_neg, smul_sub, add_smul, one_smul, add_comm,
    add_left_comm, add_assoc] using hline

/-- Helper for Theorem 4.29: a forward-invariant regularized affine combination defines a self-map
of the subtype `D`. -/
private noncomputable def regularized_selfMap {D : Set H} {T : H → H} {x0 : H} {α : ℝ}
    (hMap : MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D) : D → D :=
  fun x ↦ ⟨α • x0 + (1 - α) • T x, hMap x.2⟩

/-- Helper for Theorem 4.29: on the subtype `D`, the regularized map is a strict contraction with
constant `1 - α`. -/
private theorem regularized_map_contractingWith {D : Set H} (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) (hT : LipschitzOnWith 1 T D) {x0 : H} (hx0 : x0 ∈ D) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    ContractingWith (Real.toNNReal (1 - α))
      (regularized_selfMap
        (regularized_map_mapsTo hD_convex hTD hx0 ⟨le_of_lt hα_pos, hα_le⟩)) := by
  let hMap :
      MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D :=
    regularized_map_mapsTo hD_convex hTD hx0 ⟨le_of_lt hα_pos, hα_le⟩
  let K : NNReal := Real.toNNReal (1 - α)
  change ContractingWith K (regularized_selfMap hMap)
  refine ⟨?_, ?_⟩
  · -- The contraction constant is strictly less than `1` because `α` is positive.
    exact (Real.toNNReal_lt_one).2 (sub_lt_self (1 : ℝ) hα_pos)
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hxy : ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul x x.2 y y.2
    -- The common `α • x₀` term cancels, leaving only the scaled nonexpansive difference.
    calc
      dist (regularized_selfMap hMap x) (regularized_selfMap hMap y) =
          ‖(1 - α) • (T x - T y)‖ := by
            simp [regularized_selfMap, Subtype.dist_eq, dist_eq_norm, sub_eq_add_neg, add_comm,
              add_left_comm, add_assoc]
      _ = (1 - α) * ‖T x - T y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hα_le)]
      _ ≤ (1 - α) * ‖(x : H) - y‖ := by
        exact mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hα_le)
      _ = (1 - α) * dist x y := by
        rw [Subtype.dist_eq, dist_eq_norm]
      _ = K * dist x y := by
        rw [show (K : ℝ) = 1 - α by
          simp [K, Real.toNNReal_of_nonneg (sub_nonneg.mpr hα_le)]]

/-- Helper for Theorem 4.29: a fixed point of the regularized map has residual
`x - T x = α • (x₀ - T x)`. -/
private theorem regularized_fixed_point_residual_eq {T : H → H} {x x0 : H} {α : ℝ}
    (hx : x = α • x0 + (1 - α) • T x) :
    x - T x = α • (x0 - T x) := by
  -- Expand the fixed-point identity and collect the `T x` terms.
  have hx' : x - T x = (α • x0 + (1 - α) • T x) - T x := by
    simpa using congrArg (fun z ↦ z - T x) hx
  calc
    x - T x = (α • x0 + (1 - α) • T x) - T x := hx'
    _ = α • (x0 - T x) := by
      module

/-- Helper for Theorem 4.29: if regularized fixed points satisfy a uniform bound
`‖x₀ - T xₙ‖ ≤ R` and `αₙ → 0`, then the residuals `xₙ - T xₙ` converge strongly to `0`. -/
private theorem residual_tendsto_zero_of_regularized_fixed_points {D : Set H} {T : H → H}
    {x0 : H} {α : ℕ → ℝ} {xSeq : ℕ → D} {R : ℝ}
    (hbound : ∀ n, ‖x0 - T (xSeq n)‖ ≤ R)
    (hfixed : ∀ n, (xSeq n : H) = α n • x0 + (1 - α n) • T (xSeq n))
    (hα_nonneg : ∀ n, 0 ≤ α n) (hα_tendsto : Tendsto α atTop (nhds 0)) :
    Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (nhds 0) := by
  have hnorm_le : ∀ n, ‖(xSeq n : H) - T (xSeq n)‖ ≤ α n * R := by
    intro n
    rw [regularized_fixed_point_residual_eq (hfixed n), norm_smul,
      Real.norm_of_nonneg (hα_nonneg n)]
    exact mul_le_mul_of_nonneg_left (hbound n) (hα_nonneg n)
  have hαR : Tendsto (fun n ↦ α n * R) atTop (nhds (0 * R)) := by
    exact hα_tendsto.mul tendsto_const_nhds
  -- Squeeze the residual norms between `0` and the scalar sequence `αₙ R`.
  exact squeeze_zero_norm hnorm_le (by simpa using hαR)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use boundedness and closed convexity of `D` in the Hilbert space to obtain weak
-- sequential compactness, regularize `T` by the contractions `x ↦ α • x₀ + (1 - α) • T x`, apply
-- the Banach fixed-point theorem to each regularization, extract a weakly convergent subsequence,
-- and conclude with the demiclosedness principle for `id - T`.
/-- Theorem 4.29: Browder--Göhde--Kirk guarantees that a nonexpansive self-map of a nonempty
bounded closed convex subset of a real Hilbert space has a fixed point in that subset. -/
theorem browder_gohde_kirk_fixed_point
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_bounded : Bornology.IsBounded D)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) (hT : LipschitzOnWith 1 T D) :
    (D ∩ fixedPoints T).Nonempty := by
  classical
  obtain ⟨x0, hx0⟩ := hD_nonempty
  let α : ℕ → ℝ := fun n ↦ (1 : ℝ) / ((n : ℝ) + 1)
  letI : Nonempty D := ⟨⟨x0, hx0⟩⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  have hα_pos : ∀ n, 0 < α n := by
    intro n
    dsimp [α]
    positivity
  have hα_nonneg : ∀ n, 0 ≤ α n := by
    intro n
    exact (hα_pos n).le
  have hα_le : ∀ n, α n ≤ 1 := by
    intro n
    dsimp [α]
    have hden0 : 0 < (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_pos n
    have hden : 1 ≤ (n : ℝ) + 1 := by linarith
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
  have hα_tendsto : Tendsto α atTop (nhds 0) := by
    -- The explicit choice `αₙ = 1 / (n + 1)` tends to zero.
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [α, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  let hMap : ∀ n, MapsTo (fun x ↦ α n • x0 + (1 - α n) • T x) D D := by
    intro n
    exact regularized_map_mapsTo hD_convex hTD hx0 ⟨hα_nonneg n, hα_le n⟩
  let F : ℕ → D → D := fun n ↦ regularized_selfMap (hMap n)
  have hcontract : ∀ n, ContractingWith (Real.toNNReal (1 - α n)) (F n) := by
    intro n
    -- Each regularization is a strict contraction on the complete subtype `D`.
    simpa [F, hMap] using
      regularized_map_contractingWith hD_convex hTD hT hx0 (hα_pos n) (hα_le n)
  let xSeq : ℕ → D := fun n ↦ ContractingWith.fixedPoint (F n) (hcontract n)
  have hxSeq_fixed :
      ∀ n, (xSeq n : H) = α n • x0 + (1 - α n) • T (xSeq n) := by
    intro n
    -- The Banach fixed point of the `n`-th regularization satisfies the displayed affine equation.
    simpa [xSeq, F, regularized_selfMap] using
      congrArg Subtype.val ((hcontract n).fixedPoint_isFixedPt.eq.symm)
  obtain ⟨R, -, hR_sub⟩ := hD_bounded.subset_closedBall_lt 0 x0
  have hTxSeq_bound : ∀ n, ‖x0 - T (xSeq n)‖ ≤ R := by
    intro n
    have hmem : T (xSeq n) ∈ D := hTD (xSeq n).2
    -- Boundedness gives a uniform radius around `x₀` for all images `T xₙ`.
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hR_sub hmem
  have hresidual :
      Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (nhds 0) :=
    residual_tendsto_zero_of_regularized_fixed_points hTxSeq_bound hxSeq_fixed hα_nonneg
      hα_tendsto
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' D) :=
    (isClosed_iff_weak_image_isClosed_of_convex hD_convex).1 hD_closed
  have hweakCompact : IsCompact ((toWeakSpace ℝ H) '' D) := by
    exact
      (weaklyCompact_iff_weaklyClosed_and_bounded :
        IsCompact ((toWeakSpace ℝ H) '' D) ↔
          IsClosed ((toWeakSpace ℝ H) '' D) ∧ Bornology.IsBounded D).2
        ⟨hweakClosed, hD_bounded⟩
  have hweakSeqCompact : IsSeqCompact ((toWeakSpace ℝ H) '' D) :=
    (weaklyCompact_iff_weaklySeqCompact D).1 hweakCompact
  have hxSeq_mem : ∀ n, toWeakSpace ℝ H (xSeq n : H) ∈ ((toWeakSpace ℝ H) '' D) := by
    intro n
    exact ⟨xSeq n, (xSeq n).2, rfl⟩
  obtain ⟨xWeak, hxWeak_mem, φ, hφ, hφconv⟩ := hweakSeqCompact hxSeq_mem
  rcases hxWeak_mem with ⟨x, hxD, rfl⟩
  let ySeq : ℕ → H := fun n ↦ xSeq (φ n)
  have hySeq_mem : ∀ n, ySeq n ∈ D := by
    intro n
    exact (xSeq (φ n)).2
  have hySeq_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (ySeq n)) atTop (nhds (x : WeakSpace ℝ H)) := by
    -- Sequential compactness provides a weakly convergent ambient subsequence.
    simpa [ySeq, Function.comp] using hφconv
  have hySeq_residual :
      Tendsto (fun n ↦ ySeq n - T (ySeq n)) atTop (nhds 0) := by
    -- Strong convergence of the residuals is preserved under subsequences.
    simpa [ySeq] using hresidual.comp hφ.tendsto_atTop
  have hweakSeqClosed : IsSeqClosed ((toWeakSpace ℝ H) '' D) :=
    hweakClosed.isSeqClosed
  have hlimit_residual : x - T x = 0 := by
    -- Apply Browder demiclosedness to the weakly convergent approximate fixed-point subsequence.
    exact
      browder_demiclosedness_principle hweakSeqClosed hT hySeq_mem hySeq_weak hySeq_residual
  have hfix : x ∈ fixedPoints T := by
    -- A zero residual is exactly the fixed-point condition.
    exact Function.mem_fixedPoints_iff.mpr (sub_eq_zero.mp hlimit_residual).symm
  exact ⟨x, ⟨hxD, hfix⟩⟩

end
