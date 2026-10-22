/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin

universe u v

/- Definition 7.88 lies in the finite sampled-minimizer / weighted-average domain.

Mandatory domain-style sampling before refinement:
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner of
  minimizers on a constrained set;
- `Finset.centerMass` in mathlib, the canonical owner of a finite weighted average;
- `Finset.centerMass_eq_of_sum_1` and the defining formula of `Finset.centerMass`, which identify
  the canonical owner with the usual normalized weighted sum.

Best owner abstraction:
- source-facing: a chosen best-point sequence `x_k^*` for sampled iterates and the weighted
  average sequence `\tilde x_k`;
- core/canonical: `argmin[Set.range (fun i : Fin (k + 1) ↦ xSeq i)] f` and
  `(Finset.range k).centerMass a xSeq`;
- bridge/view: the pointwise membership projection for the best-point sequence and the expansion
  of the weighted average to the textbook normalized sum using `A_k`.

Primitive data:
- an objective `f : X → ℝ`;
- an iterate sequence `xSeq : ℕ → X` or `xSeq : ℕ → E`;
- a chosen best-point sequence `xBest : ℕ → X`;
- a weight sequence `a : ℕ → ℝ`.

Derived API:
- the sampled-prefix minimizing condition for `xBest k`;
- the partial weight sum `A_k = ∑_{i=0}^{k-1} a_i`;
- the weighted-average sequence `\tilde x_k`.

Source/core/bridge triage:
- source-facing: `IsSampledIteratesBestPointSequence`, `prefixWeightSum`, and
  `weightedAverageSequence`;
- core/canonical: `argmin[...]` and `Finset.centerMass`;
- bridge/view: `IsSampledIteratesBestPointSequence.apply`,
  `prefixWeightSum_def`, and `weightedAverageSequence_eq_inv_smul_sum`.

This item is not a pure recall: the textbook introduces source-facing names `x_k^*`, `A_k`, and
`\tilde x_k`. The best-point object is noncanonical, so the Lean owner is a predicate on a chosen
sequence rather than a `Classical.choose` definition, while the weighted average is exposed as a
canonical sequence bridged to mathlib's `Finset.centerMass`.
-/

section SampledBestPoint

variable {X : Type u}

/-- Definition 7.88 (1): a sequence `xBest` realizes the textbook best points `x_k^*` when each
term `xBest k` minimizes `f` over the sampled prefix `{x₀, ..., x_k}`. -/
def IsSampledIteratesBestPointSequence
    (f : X → ℝ) (xSeq xBest : ℕ → X) : Prop :=
  ∀ k : ℕ, xBest k ∈ argmin[Set.range (fun i : Fin (k + 1) ↦ xSeq i)] f

namespace IsSampledIteratesBestPointSequence

variable {f : X → ℝ} {xSeq xBest : ℕ → X}

/-- Evaluating a sampled-best-point sequence at time `k` gives a minimizer of `f` on the sampled
prefix `{x₀, ..., x_k}`. -/
-- Proof sketch: unfold `IsSampledIteratesBestPointSequence` and evaluate the defining predicate
-- at the index `k`.
theorem apply
    (h : IsSampledIteratesBestPointSequence f xSeq xBest) (k : ℕ) :
    xBest k ∈ argmin[Set.range (fun i : Fin (k + 1) ↦ xSeq i)] f := by
  -- Evaluate the defining sampled-prefix minimizing predicate at the requested index.
  exact h k

end IsSampledIteratesBestPointSequence

end SampledBestPoint

section WeightedAverage

variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- The partial weight sum `A_k = \sum_{i=0}^{k-1} a_i` from the textbook weighted-average
formula. -/
def prefixWeightSum (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range k) fun i ↦ a i

-- Proof sketch: unfold `prefixWeightSum`.
/-- Expanding `prefixWeightSum a k` recovers the textbook quantity
`A_k = \sum_{i=0}^{k-1} a_i`. -/
theorem prefixWeightSum_def (a : ℕ → ℝ) (k : ℕ) :
    prefixWeightSum a k = Finset.sum (Finset.range k) (fun i ↦ a i) := by
  -- Unfold the textbook abbreviation `A_k` to its defining finite sum.
  rfl

/-- Definition 7.88 (2): the weighted-average sequence `\tilde x_k` is the canonical center of
mass of the first `k` iterates with weights `a_0, ..., a_{k-1}`. -/
def weightedAverageSequence (a : ℕ → ℝ) (xSeq : ℕ → E) : ℕ → E :=
  fun k ↦ (Finset.range k).centerMass a xSeq

-- Proof sketch: unfold `weightedAverageSequence`, then expand `Finset.centerMass` and rewrite the
-- denominator with `prefixWeightSum`.
/-- The weighted-average sequence satisfies the textbook formula
`\tilde x_k = A_k⁻¹ \sum_{i=0}^{k-1} a_i x_i`, with `A_k = \sum_{i=0}^{k-1} a_i`. -/
theorem weightedAverageSequence_eq_inv_smul_sum
    (a : ℕ → ℝ) (xSeq : ℕ → E) (k : ℕ) :
    weightedAverageSequence a xSeq k =
      (prefixWeightSum a k)⁻¹ •
        Finset.sum (Finset.range k) (fun i ↦ a i • xSeq i) := by
  -- Expand the weighted average to mathlib's center-of-mass formula on `Finset.range k`.
  simp [weightedAverageSequence, prefixWeightSum, Finset.centerMass]

end WeightedAverage

end
