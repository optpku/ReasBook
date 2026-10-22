/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private lemma tendsto_of_tendsto_weakly_and_tendsto_norm
    (xₙ : ℕ → H) (x : H)
    (hWeak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hNorm : Tendsto (fun n ↦ ‖xₙ n‖) atTop (𝓝 ‖x‖)) :
    Tendsto xₙ atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hInner : Tendsto (fun n ↦ inner ℝ x (xₙ n)) atTop (𝓝 (‖x‖ ^ 2)) := by
    have hEval :
        Tendsto
          (fun n ↦
            ((topDualPairing ℝ H).flip (toWeakSpace ℝ H (xₙ n))
              (InnerProductSpace.toDual ℝ H x)))
          atTop
          (𝓝
            ((topDualPairing ℝ H).flip (toWeakSpace ℝ H x)
              (InnerProductSpace.toDual ℝ H x))) := by
      exact
        ((WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
          (InnerProductSpace.toDual ℝ H x)).tendsto (toWeakSpace ℝ H x)).comp hWeak
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
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (xₙ n - x))] using
      (sq_lt_sq₀ (norm_nonneg (xₙ n - x)) hε.le).1 hsquare_lt
  exact hNormSub

omit [CompleteSpace H] in
private lemma toStrongContinuous_of_finiteDimensional [FiniteDimensional ℝ H] :
    Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) := by
  let b := Module.Basis.ofVectorSpace ℝ H
  have hcoords : Continuous fun y : WeakSpace ℝ H ↦ b.equivFun ((toWeakSpace ℝ H).symm y) := by
    rw [continuous_pi_iff]
    intro i
    let l : StrongDual ℝ H := ⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩
    simpa [Module.Basis.equivFun_apply, l] using
      (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip) l)
  have hsymm : Continuous b.equivFun.symm := b.equivFunL.symm.continuous
  have hcomp :
      (fun y : WeakSpace ℝ H ↦ b.equivFun.symm (b.equivFun ((toWeakSpace ℝ H).symm y))) =
        ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) := by
    funext y
    exact b.equivFun.symm_apply_apply _
  rw [← hcomp]
  exact hsymm.comp hcoords

-- Proof sketch: strong convergence implies weak convergence by continuity of the canonical map to
-- `WeakSpace ℝ H`, and it also implies convergence of norms, hence the required `limsup` bound.
-- Conversely, combine weak lower semicontinuity of the norm with the `limsup` hypothesis to force
-- convergence of norms, then expand `‖xₙ - x‖²` via the inner product and use weak convergence
-- against the fixed vector `x`.
/-- Lemma 2.51 (1): a sequence in a real Hilbert space converges strongly to `x` if and only if it
converges weakly to `x` in the canonical weak topology `WeakSpace ℝ H` and its norms satisfy
`limsup ‖xₙ‖ ≤ ‖x‖`. -/
theorem tendsto_iff_tendsto_weakly_and_limsup_norm_le (xₙ : ℕ → H) (x : H) :
    Tendsto xₙ atTop (𝓝 x) ↔
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) ∧
        Filter.limsup (fun n ↦ ‖xₙ n‖) atTop ≤ ‖x‖ := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ H).continuous.tendsto x).comp hx
    · simpa using hx.norm.limsup_eq.le
  · rintro ⟨hWeak, hLimsup⟩
    have hLiminf : ‖x‖ ≤ Filter.liminf (fun n ↦ ‖xₙ n‖) atTop :=
      norm_le_liminf_of_tendsto_weakly xₙ x hWeak
    have hxₙ_bdd : Bornology.IsBounded (Set.range xₙ) := bounded_range_of_tendsto_weakly hWeak
    obtain ⟨R, hR⟩ := hxₙ_bdd.subset_closedBall (0 : H)
    have hBoundedAbove : atTop.IsBoundedUnder (· ≤ ·) fun n ↦ ‖xₙ n‖ := by
      refine isBoundedUnder_of ?_
      refine ⟨R, ?_⟩
      intro n
      simpa [Metric.mem_closedBall, dist_eq_norm] using hR (Set.mem_range_self n)
    have hBoundedBelow : atTop.IsBoundedUnder (· ≥ ·) fun n ↦ ‖xₙ n‖ := by
      refine isBoundedUnder_of ?_
      exact ⟨0, fun n ↦ norm_nonneg (xₙ n)⟩
    have hNorm : Tendsto (fun n ↦ ‖xₙ n‖) atTop (𝓝 ‖x‖) :=
      tendsto_of_le_liminf_of_limsup_le hLiminf hLimsup hBoundedAbove hBoundedBelow
    exact tendsto_of_tendsto_weakly_and_tendsto_norm xₙ x hWeak hNorm

-- Proof sketch: in finite dimension, choose a basis. Weak convergence gives convergence of every
-- coordinate, and the inverse coordinate map is continuous, so the sequence converges strongly.
-- The converse is immediate from continuity of the canonical map to `WeakSpace ℝ H`.
/-- Lemma 2.51 (2): in a finite-dimensional real Hilbert space, weak convergence of sequences in
the canonical weak topology `WeakSpace ℝ H` is equivalent to strong convergence. -/
theorem tendsto_weakly_iff_tendsto_of_finiteDimensional
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (xₙ : ℕ → E) (x : E) :
    Tendsto xₙ atTop (𝓝 x) ↔
      Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x)) := by
  constructor
  · intro hx
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ E).continuous.tendsto x).comp hx
  · intro hWeak
    have hcont : Continuous ((toWeakSpace ℝ E).symm : WeakSpace ℝ E → E) :=
      toStrongContinuous_of_finiteDimensional
    simpa using (hcont.tendsto (toWeakSpace ℝ E x)).comp hWeak

-- Proof sketch: weak convergence makes `(xₙ)` bounded. Split
-- `inner ℝ (xₙ n) (uₙ n)` as `inner ℝ (xₙ n) (uₙ n - u) + inner ℝ (xₙ n) u`; the first term
-- tends to `0` by Cauchy-Schwarz and strong convergence of `uₙ`, while the second tends to
-- `inner ℝ x u` by weak convergence against the fixed vector `u`.
/-- Lemma 2.51 (3): if `xₙ` converges weakly to `x` in the canonical weak topology `WeakSpace ℝ H`
and `uₙ` converges strongly to `u`, then the inner products `⟪xₙ, uₙ⟫` converge to `⟪x, u⟫`. -/
theorem tendsto_inner_of_tendsto_weakly_of_tendsto (xₙ uₙ : ℕ → H) (x u : H)
    (hxₙ : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huₙ : Tendsto uₙ atTop (𝓝 u)) :
    Tendsto (fun n ↦ inner ℝ (xₙ n) (uₙ n)) atTop (𝓝 (inner ℝ x u)) := by
  have hxₙ_bdd : Bornology.IsBounded (Set.range xₙ) := bounded_range_of_tendsto_weakly hxₙ
  obtain ⟨R, hR⟩ := hxₙ_bdd.subset_closedBall (0 : H)
  have hR_norm : ∀ n, ‖xₙ n‖ ≤ R := by
    intro n
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR (Set.mem_range_self n)
  have huₙ_sub : Tendsto (fun n ↦ uₙ n - u) atTop (𝓝 (0 : H)) := by
    have hsub : Tendsto (fun n ↦ uₙ n - u) atTop (𝓝 (u - u)) :=
      huₙ.sub tendsto_const_nhds
    simpa using hsub
  have hsmall_bound :
      ∀ n, ‖inner ℝ (xₙ n) (uₙ n - u)‖ ≤ R * ‖uₙ n - u‖ := by
    intro n
    calc
      ‖inner ℝ (xₙ n) (uₙ n - u)‖ ≤ ‖xₙ n‖ * ‖uₙ n - u‖ := abs_real_inner_le_norm _ _
      _ ≤ R * ‖uₙ n - u‖ := by
        exact mul_le_mul_of_nonneg_right (hR_norm n) (norm_nonneg _)
  have hsmall_bound_tendsto : Tendsto (fun n ↦ R * ‖uₙ n - u‖) atTop (𝓝 0) := by
    simpa using huₙ_sub.norm.const_mul R
  have hsmall :
      Tendsto (fun n ↦ inner ℝ (xₙ n) (uₙ n - u)) atTop (𝓝 0) := by
    exact squeeze_zero_norm hsmall_bound hsmall_bound_tendsto
  have hfixed : Tendsto (fun n ↦ inner ℝ (xₙ n) u) atTop (𝓝 (inner ℝ x u)) := by
    simpa using ((weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H x)).comp hxₙ
  have hsum :
      Tendsto
        (fun n ↦ inner ℝ (xₙ n) (uₙ n - u) + inner ℝ (xₙ n) u)
        atTop (𝓝 (0 + inner ℝ x u)) :=
    hsmall.add hfixed
  convert hsum using 1
  · funext n
    rw [← inner_add_right, sub_add_cancel]
  · simp
