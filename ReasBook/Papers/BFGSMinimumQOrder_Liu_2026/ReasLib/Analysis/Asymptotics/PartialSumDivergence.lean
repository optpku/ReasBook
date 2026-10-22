/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Asymptotics/PartialSumDivergence.lean
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

open Filter

/-! Finite telescoping estimates for sequences with nonnegative divergent increments. -/

/-- A one-step decrease inequality bounds the later value by the initial value minus the
partial sum of the nonnegative increments. -/
theorem le_sub_sum_range_of_succ_add_le {u v : ℕ → ℝ}
    (hstep : ∀ n, u (n + 1) + v n ≤ u n) (n : ℕ) :
    u n + ∑ i ∈ Finset.range n, v i ≤ u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n, ih]

/-- A real sequence that decreases by nonnegative increments whose series is not summable
tends to `atBot`. -/
theorem tendsto_atBot_of_succ_add_le_of_not_summable {u v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, u (n + 1) + v n ≤ u n)
    (hdiv : ¬ Summable v) :
    Tendsto u atTop atBot := by
  refine Filter.tendsto_atBot.2 ?_
  intro b
  have hsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, v i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hv).mp hdiv
  have hsum_event : ∀ᶠ n : ℕ in atTop,
      u 0 - b ≤ ∑ i ∈ Finset.range n, v i :=
    hsum.eventually (eventually_ge_atTop (u 0 - b))
  filter_upwards [hsum_event] with n hn
  have hbound := le_sub_sum_range_of_succ_add_le hstep n
  linarith
