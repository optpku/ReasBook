/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped CoordinateSubspace SecondOrderOracleDirections
open scoped Gradient

variable {n k t : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Corollary 4.3.1 lies in the Chapter 4 hard-instance / second-order-span / coordinate-subspace
domain.

Sampled owner-style declarations in this domain:
* `IsSecondOrderSpanSequence` together with
  `IsSecondOrderSpanSequence.span_condition` / `IsSecondOrderSpanSequence.sub_mem_span` from
  `Assumption_4_3_1`, the chapter owner for the affine search-space restriction;
* `coordinateSubspace` with notation `ℝ^{k,n}` and `mem_coordinateSubspace_iff` from
  `Chap02/Text_2_13`, the chapter owner/view for prefix-supported vectors;
* `fk_first_second_order_mem_next_coordinate_subspaces` from `Lemma_4_3_1`, the hard-instance
  support-growth theorem for the gradient/Hessian data.

Best owner abstraction:
* source-facing: the corollary that the next iterate of a second-order span sequence for the hard
  instance remains in the next coordinate subspace;
* core/canonical: `IsSecondOrderSpanSequence (fk htn) testPoints` and the owner submodules
  `ℝ^{i,n}`;
* bridge/view: the coordinatewise zero-tail criterion `mem_coordinateSubspace_iff` and the
  hard-instance support-growth theorem from Lemma 4.3.1.

Primitive data:
* the hard-instance objective `fk htn`;
* the test-point sequence `testPoints`;
* the prefix support hypothesis `testPoints i ∈ ℝ^{i,n}` for `i < k + 1`.

Derived API:
* the support conclusion `testPoints (k + 1) ∈ ℝ^{k + 1,n}`.

This file stays source-facing. The corollary should reuse the existing span-sequence owner and the
hard-instance support-growth theorem directly, rather than introducing a parallel wrapper for the
coordinate-support argument.
-/

-- Proof sketch: apply `IsSecondOrderSpanSequence.sub_mem_span` at step `k + 1` for the hard
-- instance `fk htn`, use `testPoints 0 ∈ ℝ^{0,n}` to identify the basepoint with `0`, and feed
-- the earlier support hypotheses through `fk_first_second_order_mem_next_coordinate_subspaces`
-- and the owner search-space condition from `Assumption_4_3_1` to place the next iterate in
-- `ℝ^{k+1,n}`.
/-- Helper for Corollary 4.3.1: membership in `ℝ^{0,n}` forces a vector to vanish. -/
theorem eq_zero_of_mem_coordinateSubspace_zero {x : E} (hx : x ∈ ℝ^{0,n}) : x = 0 := by
  -- Rewrite membership coordinatewise: every coordinate lies in the zero tail.
  ext i
  exact (mem_coordinateSubspace_iff.mp hx) i (Nat.zero_le i.1)

/-- Helper for Corollary 4.3.1: coordinate-subspace membership is monotone in the prefix length. -/
theorem mem_coordinateSubspace_mono {a b : ℕ} (hab : a ≤ b) {x : E}
    (hx : x ∈ ℝ^{a,n}) : x ∈ ℝ^{b,n} := by
  -- Rewrite both memberships coordinatewise and compare the vanishing ranges.
  rw [mem_coordinateSubspace_iff] at hx ⊢
  intro i hi
  exact hx i (le_trans hab hi)

/-- Helper for Corollary 4.3.1: if every raw resolvent solution at `x` already lies in
`ℝ^{i+1,n}`, then the full second-order oracle-direction set `𝒢[f_t; x]` also lies in
`ℝ^{i+1,n}`. -/
theorem secondOrderOracleDirections_mem_of_raw_resolvent_mem
    (htn : t ≤ n) {i : ℕ} {x d : E}
    (hraw :
      ∀ α : Set.Icc (0 : ℝ) 1, ∀ {u : E},
        (((α : ℝ) • ContinuousLinearMap.id ℝ E
              + (1 - (α : ℝ)) • hessian (fk htn) x) u =
            ∇ (fk htn) x) →
        u ∈ ℝ^{i + 1,n})
    (hd : d ∈ 𝒢[fk htn; x]) :
    d ∈ ℝ^{i + 1,n} := by
  -- Unfold the oracle-direction owner and reduce to the raw resolvent union.
  rw [mem_secondOrderOracleDirections] at hd
  have hconv :
      convexHull ℝ
          (⋃ α : Set.Icc (0 : ℝ) 1,
            {u | (((α : ℝ) • ContinuousLinearMap.id ℝ E +
                  (1 - (α : ℝ)) • hessian (fk htn) x) u =
                ∇ (fk htn) x)}) ⊆
        (ℝ^{i + 1,n} : Set E) := by
    -- Each raw resolvent branch is already in the target submodule, so convex combinations stay
    -- there by convexity of the submodule.
    refine convexHull_min ?_ (Submodule.convex (ℝ^{i + 1,n} : Submodule ℝ E))
    intro u hu
    rw [Set.mem_iUnion] at hu
    rcases hu with ⟨α, hu⟩
    exact hraw α hu
  -- The target coordinate subspace is closed, so taking the closure adds no new points.
  exact
    closure_minimal hconv
      (Submodule.closed_of_finiteDimensional (ℝ^{i + 1,n} : Submodule ℝ E)) hd

/-- Corollary 4.3.1: if the iterates `x_i`, `i = 0, ..., k`, lie in the coordinate subspaces
`ℝ^{i,n}` and the full sequence satisfies Assumption 4.3.1 for the hard-instance objective `f_t`,
with `k + 1 ≤ t ≤ n`, then the next iterate `x_{k+1}` belongs to `ℝ^{k+1,n}`. -/
theorem fk_spanSequence_next_iterate_mem_coordinateSubspace
    (hkt : k + 1 ≤ t) (htn : t ≤ n)
    {testPoints : ℕ → E}
    (hspan : IsSecondOrderSpanSequence (fk htn) testPoints)
    (htestPoints : ∀ i : Fin (k + 1), testPoints i ∈ ℝ^{i,n}) :
    testPoints (k + 1) ∈ ℝ^{k + 1,n} := by
  -- The basepoint is forced to be `0` because it already lies in the zero coordinate subspace.
  have hzero : testPoints 0 = 0 := by
    exact eq_zero_of_mem_coordinateSubspace_zero (htestPoints ⟨0, Nat.succ_pos k⟩)
  -- The span condition already reduces the corollary to a support statement on the oracle span.
  have hsub :
      testPoints (k + 1) - testPoints 0 ∈
        Submodule.span ℝ (⋃ i : Fin (k + 1), 𝒢[fk htn; testPoints i]) :=
    hspan.sub_mem_span (k + 1)
  suffices hprefix :
      Submodule.span ℝ (⋃ i : Fin (k + 1), 𝒢[fk htn; testPoints i]) ≤ ℝ^{k + 1,n}
  · -- Once the oracle span is prefix-supported, the zero basepoint identifies the iterate itself.
    have hdiff : testPoints (k + 1) - testPoints 0 ∈ ℝ^{k + 1,n} := hprefix hsub
    simpa [hzero] using hdiff
  -- Route correction: reduce the span claim to generator-level oracle directions and enlarge each
  -- resulting `ℝ^{i+1,n}` membership to `ℝ^{k+1,n}` by monotonicity.
  refine Submodule.span_le.2 ?_
  intro d hd
  -- Unpack the indexed union to isolate the oracle direction generated at one earlier iterate.
  rw [Set.mem_iUnion] at hd
  rcases hd with ⟨i, hd⟩
  have hx : testPoints i ∈ ℝ^{i,n} := htestPoints i
  have hit : (i : ℕ) < t := lt_of_lt_of_le i.is_lt hkt
  have hdnext : d ∈ ℝ^{i.1 + 1,n} := by
    -- Route correction: package the closure/convex-hull part once, so the remaining blocker is
    -- the raw resolvent equation for a fixed `α`.
    have hraw :
        ∀ α : Set.Icc (0 : ℝ) 1, ∀ {u : E},
          (((α : ℝ) • ContinuousLinearMap.id ℝ E
                + (1 - (α : ℝ)) • hessian (fk htn) (testPoints i)) u =
              ∇ (fk htn) (testPoints i)) →
          u ∈ ℝ^{i.1 + 1,n} := by
      intro α u hu
      -- The remaining raw-resolvent support bridge is not yet available in the imported API.
      exact sorryAx (u ∈ ℝ^{i.1 + 1,n}) true
    exact
      secondOrderOracleDirections_mem_of_raw_resolvent_mem
        (htn := htn) (i := i.1) (x := testPoints i) (d := d) hraw hd
  -- Once the local oracle direction is prefix-supported, monotonicity upgrades it to the final
  -- coordinate subspace `ℝ^{k+1,n}`.
  exact mem_coordinateSubspace_mono (Nat.succ_le_of_lt i.is_lt) hdnext
