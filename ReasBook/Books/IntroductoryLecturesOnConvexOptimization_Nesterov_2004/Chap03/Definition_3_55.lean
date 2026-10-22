/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-
Definition 3.55 lies in the Chapter 3 best-so-far value/radius domain.

Sampled owner-style declarations:
- `iInf`, the core mathlib finite-prefix infimum expression on `Fin (k + 1)`;
- `Finite.ciInf_le`, the canonical pointwise upper bound for a finite indexed infimum;
- `Finite.exists_min`, the canonical finite attainment theorem for real-valued prefixes;
- `bestFunctionValueUpTo_le`, the immediate companion inequality for the source-facing owner;
- `levelMethodHistoryFromApproximateValues_optimalValue_eq` in `Proposition_3_50`, the later
  level-method bridge identifying
  `(levelMethodHistoryFromApproximateValues hatf f xSeq).optimalValue k` with the same finite
  sampled infimum.

Best owner abstraction:
- source-facing: `bestFunctionValueUpTo`;
- core/canonical: the raw finite infimum `⨅ j : Fin (k + 1), values j`;
- bridge/view: the radius-language specialization `bestRadiusUpTo` and
  `(levelMethodHistoryFromApproximateValues hatf f xSeq).optimalValue k` from
  `Proposition_3_50`.

Primitive data:
- a real sequence `values : ℕ → ℝ`;
- an index cutoff `k : ℕ`.

Derived API:
- the best-so-far sampled value `bestFunctionValueUpTo values k`;
- the radius-language specialization `bestRadiusUpTo radii k`;
- the evaluation inequality `bestFunctionValueUpTo values k ≤ values j` for `j : Fin (k + 1)`.

Source/core/bridge triage:
- source-facing: `bestFunctionValueUpTo`;
- core/canonical: the finite indexed infimum underlying `bestFunctionValueUpTo`;
- bridge/view: `bestRadiusUpTo` and later packaged views such as
  `LevelMethodHistory.optimalValue`.

This file therefore keeps `bestFunctionValueUpTo` as the owner of the sampled-prefix minimum and
uses the radius-language surface only as a thin specialization of that owner. Later chapter results
should reuse the owner theorem `bestFunctionValueUpTo_le` rather than maintaining a second parallel
radius inequality API.
-/

/-- Definition 3.55: the best sampled objective value up to step `k`, namely the infimum of the
sampled values indexed by `0, ..., k`. -/
abbrev bestFunctionValueUpTo (values : ℕ → ℝ) (k : ℕ) : ℝ :=
  ⨅ j : Fin (k + 1), values j

/-- The best sampled radius up to step `k`, namely the infimum of the sampled radii indexed by
`0, ..., k`. -/
abbrev bestRadiusUpTo (radii : ℕ → ℝ) (k : ℕ) : ℝ :=
  bestFunctionValueUpTo radii k

/-- The best sampled objective value up to step `k` is bounded above by each sampled value among
the first `k + 1` terms. -/
-- Proof sketch: unfold `bestFunctionValueUpTo` and apply the finite indexed-infimum bound
-- `Finite.ciInf_le` at the chosen index `j : Fin (k + 1)`.
theorem bestFunctionValueUpTo_le
    {values : ℕ → ℝ} {k : ℕ} (j : Fin (k + 1)) :
    bestFunctionValueUpTo values k ≤ values j := by
  simpa [bestFunctionValueUpTo] using
    (Finite.ciInf_le (fun i : Fin (k + 1) ↦ values i) j)

/-- Adding one more sample point cannot increase the best sampled objective value. -/
theorem bestFunctionValueUpTo_antitone_step
    {values : ℕ → ℝ} (k : ℕ) :
    bestFunctionValueUpTo values (k + 1) ≤ bestFunctionValueUpTo values k := by
  refine le_ciInf ?_
  intro j
  simpa [bestFunctionValueUpTo] using
    (Finite.ciInf_le
      (fun i : Fin ((k + 1) + 1) ↦ values i)
      ⟨j, Nat.lt_succ_of_lt j.2⟩)

/-- The best sampled objective value up to step `k` is attained by one of the first `k + 1`
samples. -/
theorem bestFunctionValueUpTo_exists_eq
    (values : ℕ → ℝ) (k : ℕ) :
    ∃ j : Fin (k + 1), values j = bestFunctionValueUpTo values k := by
  obtain ⟨j, hjmin⟩ : ∃ j : Fin (k + 1), ∀ i : Fin (k + 1), values j ≤ values i := by
    simpa using (Finite.exists_min fun i : Fin (k + 1) ↦ values i)
  have hjbest : values j ≤ bestFunctionValueUpTo values k := by
    simpa [bestFunctionValueUpTo] using (le_ciInf hjmin)
  exact ⟨j, le_antisymm hjbest (bestFunctionValueUpTo_le j)⟩
