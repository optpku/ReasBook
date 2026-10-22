/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped CoordinateSubspace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: span-based first-order black-box iterates in `ℝⁿ`, viewed through the chapter's
coordinate-subspace owner `ℝ^{k,n}`.

Sampled owner-style declarations:
* `SatisfiesLinearSpanCondition` from `Chap03/Theorem_3_2_1`, the chapter owner for span-method
  iterate sequences;
* `SatisfiesLinearSpanCondition.zero_eq`, the canonical extraction of the starting-point datum from
  that owner;
* `coordinateSubspace k n` with notation `ℝ^{k,n}` and its view lemma
  `mem_coordinateSubspace_iff`, the chapter owner for prefix-supported vectors;
* `prefix_span_le_coordinateSubspace` from `Chap02/Lemma_2_5`, the exact bridge from span data to
  coordinate-subspace membership.

Best owner abstraction:
* core/canonical: `SatisfiesLinearSpanCondition (0 : E) g xSeq k` for the iterate process and the
  coordinate-submodule owner `ℝ^{k,n}`;
* source-facing: the resisting-oracle support-growth rule
  `xSeq i ∈ ℝ^{i,n} → g (xSeq i) ∈ ℝ^{i + 1,n}`;
* bridge/view: `prefix_span_le_coordinateSubspace`.

Primitive data:
* the iterate sequence `xSeq`,
* the queried-vector map `g`,
* the owner span-condition datum `SatisfiesLinearSpanCondition (0 : E) g xSeq k`,
* the resisting-oracle support-growth rule sending `xSeq i ∈ ℝ^{i,n}` to
  `g (xSeq i) ∈ ℝ^{i + 1,n}`.

Derived API:
* the coordinate-support conclusion for every iterate `xSeq i` with `i ≤ k`.

Source/core/bridge triage:
* source-facing: the resisting-oracle support-growth hypothesis;
* core/canonical: `SatisfiesLinearSpanCondition`;
* bridge/view: the proposition below converting the owner span condition plus support growth into
  coordinate-support control.

This file therefore deletes the parallel local span-method interface and states the proposition
directly on the chapter owner `SatisfiesLinearSpanCondition`, with the coordinate-subspace theorem
used only as the geometric bridge. -/

/-- Proposition 3.31: coordinate-support growth under the resisting oracle. If a deterministic
first-order method on `ℝⁿ` starts at `0` and the resisting oracle returns, at each stage `i < k`,
a vector in `ℝ^{i+1,n}` whenever the current iterate lies in `ℝ^{i,n}`, then every iterate `xᵢ`
with `i ≤ k` lies in `ℝ^{i,n}`. The iterate process itself is expressed through the chapter's
canonical span-condition owner `SatisfiesLinearSpanCondition`. -/
-- Proof sketch: argue inductively on the iterate index. The base case is `x₀ = 0`. For the step,
-- the resisting-oracle hypothesis gives `g j ∈ ℝ^{j.1 + 1,n}` for each earlier index
-- `j : Fin (i + 1)`, so `prefix_span_le_coordinateSubspace` puts the span of the revealed vectors
-- inside `ℝ^{i+1,n}`; the span condition for the deterministic method then yields
-- `x (i + 1) ∈ ℝ^{i+1,n}`.
theorem iterates_mem_coordinateSubspace_under_resistingOracle
    {k : ℕ} {g : E → E} {xSeq : ℕ → E}
    (hxSeq : SatisfiesLinearSpanCondition (0 : E) g xSeq k)
    (hresist : ∀ i < k, xSeq i ∈ ℝ^{i,n} → g (xSeq i) ∈ ℝ^{i + 1,n})
    (i : ℕ) (hi : i ≤ k) :
    xSeq i ∈ ℝ^{i,n} := by
  have hx0 : xSeq 0 = 0 := hxSeq.zero_eq
  refine Nat.strong_induction_on i ?_ hi
  intro i ih hik
  cases i with
  | zero =>
      simp [hx0]
  | succ i =>
      have hstep :
          xSeq (i + 1) ∈ Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) := by
        have hxSeq_step :
            xSeq (i + 1) ∈
              AffineSubspace.mk' (0 : E)
                (Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t))) :=
          hxSeq (i + 1) hik
        rw [AffineSubspace.mem_mk'] at hxSeq_step
        simpa using hxSeq_step
      exact
        (prefix_span_le_coordinateSubspace (fun t ↦ g (xSeq t)) fun j ↦
          hresist j (lt_of_lt_of_le j.is_lt hik)
            (ih j j.is_lt (Nat.le_of_lt (lt_of_lt_of_le j.is_lt hik))))
          hstep

end
