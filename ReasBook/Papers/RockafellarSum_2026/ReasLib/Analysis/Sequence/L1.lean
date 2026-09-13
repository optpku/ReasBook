/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The real `L1Seq` model

This module provides the real `ℓ¹` sequence model, finite truncations, and
their norm and density API.
-/

@[expose] public section

/-- The real `ℓ¹` space of sequences indexed by `ℕ`. -/
abbrev L1Seq : Type := lp (fun _ : ℕ ↦ ℝ) 1

namespace L1Seq

/-- The norm of a real summable sequence is the sum of its coordinatewise absolute values. -/
theorem norm_eq_tsum_abs (x : L1Seq) :
    ‖x‖ = ∑' n, |x n| := by
  -- Specialize the general `lp` norm formula and normalize the exponent-one terms.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  simpa only [ENNReal.toReal_one, div_one, Real.rpow_one, Real.norm_eq_abs] using
    lp.norm_eq_tsum_rpow hOne x

/-- The prefix truncation of a summable sequence to the coordinates in `Finset.range n`. -/
noncomputable def truncate (x : L1Seq) (n : ℕ) : L1Seq :=
  ∑ i ∈ Finset.range n, lp.single 1 i (x i)

/-- Prefix truncation agrees with the original sequence below its cutoff and vanishes elsewhere. -/
theorem truncate_apply (x : L1Seq) (n i : ℕ) :
    truncate x n i = if i < n then x i else 0 := by
  -- Evaluate the finite sum of coordinate singletons at the chosen coordinate.
  classical
  simp only [truncate, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Finset.sum_pi_single, Finset.mem_range]

/-- Every prefix truncation has finite coordinate support. -/
theorem truncate_hasFiniteSupport (x : L1Seq) (n : ℕ) :
    (fun i ↦ truncate x n i).HasFiniteSupport := by
  -- The coordinate support is contained in the finite prefix `Finset.range n`.
  rw [Function.HasFiniteSupport]
  refine (Finset.range n).finite_toSet.subset ?_
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hin
  rw [truncate_apply, if_neg hin] at hi
  exact hi rfl

/-- Prefix truncations converge to the original summable sequence. -/
theorem tendsto_truncate (x : L1Seq) :
    Filter.Tendsto (truncate x) Filter.atTop (nhds x) := by
  -- Take the natural partial sums of mathlib's canonical single-coordinate expansion.
  have hOneTop : (1 : ENNReal) ≠ ⊤ := by
    norm_num
  have hTruncate : truncate x =
      fun n ↦ ∑ i ∈ Finset.range n, lp.single 1 i (x i) := by
    funext n
    rfl
  rw [hTruncate]
  exact (lp.hasSum_single hOneTop x).tendsto_sum_nat

/-- The norm of the prefix-truncation error tends to zero. -/
theorem tendsto_norm_truncate_sub (x : L1Seq) :
    Filter.Tendsto (fun n ↦ ‖truncate x n - x‖) Filter.atTop (nhds 0) := by
  -- Subtract the constant limit and pass the resulting convergence through the norm.
  have hSub : Filter.Tendsto (fun n ↦ truncate x n - x) Filter.atTop (nhds (x - x)) :=
    (tendsto_truncate x).sub tendsto_const_nhds
  simpa only [sub_self, norm_zero] using hSub.norm

/-- Real summable sequences with finite coordinate support form a dense subset. -/
theorem finitelySupported_dense :
    Dense {x : L1Seq | (fun n ↦ x n).HasFiniteSupport} := by
  -- Every point is the limit of its finite-support prefix truncations.
  intro x
  refine mem_closure_of_tendsto (tendsto_truncate x) ?_
  exact Filter.Eventually.of_forall (truncate_hasFiniteSupport x)

/-- Every real summable sequence has arbitrarily small absolute-value tails outside a
finite set containing any prescribed index. -/
theorem exists_finset_tail_lt (a : L1Seq) (n₀ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ℕ, n₀ ∈ J ∧ (∑' n : {n // n ∉ J}, |a n|) < ε := by
  -- Complementary absolute-value sums vanish as finite sets exhaust the indices.
  have hTail : Filter.Tendsto
      (fun J : Finset ℕ ↦ ∑' n : {n // n ∉ J}, |a n|)
      Filter.atTop (nhds 0) :=
    tendsto_tsum_compl_atTop_zero (fun n : ℕ ↦ |a n|)
  -- Positivity of `ε` turns convergence to zero into an eventual strict bound.
  have hTailLt :
      ∀ᶠ J : Finset ℕ in Filter.atTop, (∑' n : {n // n ∉ J}, |a n|) < ε :=
    (tendsto_order.1 hTail).2 ε hε
  -- Eventually the same finite set both contains `n₀` and has the required tail bound.
  exact ((Filter.eventually_finset_mem_atTop n₀).and hTailLt).exists

end L1Seq
