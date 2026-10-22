/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_45

open Filter
open scoped InnerProductSpace
open scoped Pointwise
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Helper for Proposition 3.42: a sequence taking values in a Minkowski sum admits termwise
decompositions into sequences in the two summands. -/
-- Proof sketch: unpack `z n ∈ C + D` for each index and choose compatible witnesses.
private lemma exists_component_sequences_of_mem_add {C D : Set E} {z : ℕ → E}
    (hz : ∀ n, z n ∈ C + D) :
    ∃ x y : ℕ → E, (∀ n, x n ∈ C) ∧ (∀ n, y n ∈ D) ∧ (∀ n, z n = x n + y n) := by
  have hdecomp : ∀ n, ∃ x ∈ C, ∃ y ∈ D, z n = x + y := by
    intro n
    simpa [Set.mem_add, eq_comm] using hz n
  choose x hx y hy hxy using hdecomp
  exact ⟨x, y, hx, hy, hxy⟩

/- Proposition 3.42 (1): the Minkowski sum of two nonempty subsets is nonempty, canonically
formalized by `Set.Nonempty.add`. -/
recall Set.Nonempty.add

section Hilbert

variable [InnerProductSpace ℝ E]

/- Proposition 3.42 (2): the Minkowski sum of two convex subsets of a real Hilbert space is
convex, canonically formalized by `Convex.add`. -/
recall Convex.add

section Complete

variable [CompleteSpace E]

/- Helper for Proposition 3.42: a weak limit of a sequence in a nonempty closed convex set of a
real Hilbert space still belongs to that set. -/
-- Proof sketch: project the weak limit onto the closed convex set, use the variational inequality
-- for the projection on every sequence term, and pass to the limit in the corresponding
-- inner-product coordinates.
private lemma weak_limit_mem_of_nonempty_isClosed_convex {C : Set E} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {xₙ : ℕ → E} {x : E}
    (hxₙ : ∀ n, xₙ n ∈ C)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop
      (nhds (toWeakSpace ℝ E x))) :
    x ∈ C := by
  obtain ⟨p, hp_mem, hp_best⟩ :=
    exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x
  have hvariational : ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
    -- The projection theorem turns the minimizing point `p` into a variational inequality.
    have hinner_nonpos : ∀ y ∈ C, ⟪x - p, y - p⟫_ℝ ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp_mem).mp hp_best
    intro y hy
    simpa [real_inner_comm] using hinner_nonpos y hy
  have hnonpos : ∀ n, ⟪xₙ n - p, x - p⟫_ℝ ≤ 0 := by
    -- Apply the variational inequality to each point of the sequence.
    intro n
    exact hvariational (xₙ n) (hxₙ n)
  have hinner_raw :
      Tendsto (fun n ↦ ⟪xₙ n, x - p⟫_ℝ) atTop (nhds (⟪x, x - p⟫_ℝ)) := by
    -- Weak convergence is tested against the fixed vector `x - p`.
    have hEval :=
      ((WeakBilin.eval_continuous ((topDualPairing ℝ E).flip)
        (InnerProductSpace.toDual ℝ E (x - p))).tendsto (toWeakSpace ℝ E x)).comp hweak
    have hEval' :
        Tendsto (fun n ↦ ⟪x - p, xₙ n⟫_ℝ) atTop (nhds (⟪x - p, x⟫_ℝ)) := by
      simpa only [toWeakSpace, LinearEquiv.refl_apply, LinearMap.flip_apply,
        topDualPairing_apply, InnerProductSpace.toDual_apply_apply] using hEval
    simpa [real_inner_comm] using hEval'
  have hinner :
      Tendsto (fun n ↦ ⟪xₙ n - p, x - p⟫_ℝ) atTop (nhds (‖x - p‖ ^ 2)) := by
    -- Subtract the constant projection term to reveal the squared norm of `x - p`.
    have hsub :
        Tendsto (fun n ↦ ⟪xₙ n, x - p⟫_ℝ - ⟪p, x - p⟫_ℝ) atTop
          (nhds (⟪x, x - p⟫_ℝ - ⟪p, x - p⟫_ℝ)) := by
      exact hinner_raw.sub tendsto_const_nhds
    convert hsub using 1
    · ext n
      rw [inner_sub_left]
    · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hnorm_sq_nonpos : ‖x - p‖ ^ 2 ≤ 0 := by
    -- The closed half-line `(-∞, 0]` captures the sign inequality in the limit.
    exact le_of_tendsto hinner (Filter.Eventually.of_forall hnonpos)
  have hnorm_sq_zero : ‖x - p‖ ^ 2 = 0 := by
    exact le_antisymm hnorm_sq_nonpos (sq_nonneg ‖x - p‖)
  have hxp : x = p := by
    -- A vanishing squared norm forces the weak limit to coincide with its projection.
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact eq_zero_of_pow_eq_zero hnorm_sq_zero
  exact hxp ▸ hp_mem

/-- Proposition 3.42 (3): If `C` and `D` are closed convex subsets of a Hilbert space and `D` is
bounded, then their Minkowski sum is closed. -/
-- Proof sketch: Take a convergent sequence in `C + D`, decompose it as `xₙ + yₙ` with `xₙ ∈ C`
-- and `yₙ ∈ D`, extract a weakly convergent subsequence from the bounded sequence `(yₙ)`, use
-- weak closedness of closed convex sets to keep the weak limits in `D` and `C`, and conclude that
-- the strong limit belongs to `C + D`.
theorem isClosed_minkowski_sum_of_isBounded {C D : Set E} (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_bounded : Bornology.IsBounded D) : IsClosed (C + D) := by
  rw [← isSeqClosed_iff_isClosed]
  intro z w hz hw
  rcases exists_component_sequences_of_mem_add hz with ⟨x, y, hxC, hyD, hz_eq⟩
  have hy_bounded_range : Bornology.IsBounded (Set.range y) := by
    -- The right-hand component sequence stays in the bounded set `D`.
    refine hD_bounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact hyD n
  obtain ⟨y_lim, φ, hφ, hy_lim⟩ :=
    bounded_sequence_has_weakly_convergent_subsequence y hy_bounded_range
  have hD_nonempty : D.Nonempty := ⟨y (φ 0), hyD (φ 0)⟩
  have hy_lim_mem : y_lim ∈ D := by
    -- Weak closedness of the closed convex set `D` keeps the weak subsequential limit in `D`.
    exact
      weak_limit_mem_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
        (fun n ↦ hyD (φ n)) hy_lim
  have hz_subseq : Tendsto (fun n ↦ z (φ n)) atTop (nhds w) := hw.comp hφ.tendsto_atTop
  have hw_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ E (z (φ n))) atTop (nhds (toWeakSpace ℝ E w)) := by
    -- Strong convergence implies weak convergence after passing to the extracted subsequence.
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ E).continuous.tendsto w).comp hz_subseq
  have hx_sub : ∀ n, x n = z n - y n := by
    intro n
    -- Rearranging the decomposition `z n = x n + y n` isolates the left-hand component.
    calc
      x n = x n + y n - y n := by abel
      _ = z n - y n := by rw [hz_eq n]
  have hx_lim_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ E (x (φ n))) atTop
        (nhds (toWeakSpace ℝ E (w - y_lim))) := by
    -- Subtract the weakly convergent `y`-subsequence from the weak limit of the `z`-subsequence.
    have hsub :
        Tendsto
          (fun n ↦ toWeakSpace ℝ E (z (φ n)) - toWeakSpace ℝ E (y (φ n)))
          atTop (nhds (toWeakSpace ℝ E w - toWeakSpace ℝ E y_lim)) := by
      exact hw_weak.sub hy_lim
    have hx_eq :
        (fun n ↦ toWeakSpace ℝ E (x (φ n))) =
          (fun n ↦ toWeakSpace ℝ E (z (φ n)) - toWeakSpace ℝ E (y (φ n))) := by
      funext n
      rw [hx_sub (φ n)]
      simp
    rw [hx_eq]
    simpa using hsub
  have hC_nonempty : C.Nonempty := ⟨x (φ 0), hxC (φ 0)⟩
  have hw_sub_mem : w - y_lim ∈ C := by
    -- Weak closedness of `C` captures the weak limit of the left-hand subsequence.
    exact
      weak_limit_mem_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
        (fun n ↦ hxC (φ n)) hx_lim_weak
  -- Reassemble the limit as a sum of the two weak limits.
  exact
    by
      simpa [Set.mem_add] using
        ⟨w - y_lim, hw_sub_mem, y_lim, hy_lim_mem, by simp [sub_eq_add_neg, add_assoc]⟩

end Complete
end Hilbert
