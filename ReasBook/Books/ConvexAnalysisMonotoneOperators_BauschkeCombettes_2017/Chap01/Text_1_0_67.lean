/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter

variable {X : Type u} [MetricSpace X]

/- Text 1.0.67: a sequence in a metric space is Cauchy when it is formalized by the canonical
predicate `CauchySeq`; the usual metric-space distance criterion and the textbook sequential
formulation of completeness are recorded below as companion statements. -/
recall CauchySeq {α : Type u} {β : Type v} [UniformSpace α] [Preorder β] (u : β → α) : Prop

/- In a metric space, a sequence is Cauchy exactly when its pairwise distances are eventually
arbitrarily small. -/
recall Metric.cauchySeq_iff {α : Type u} {β : Type v} [PseudoMetricSpace α] [Nonempty β]
    [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε

/- Completeness of a metric space is formalized by the canonical typeclass `CompleteSpace X`. -/
recall CompleteSpace (α : Type u) [UniformSpace α] : Prop

/-- Text 1.0.67: a metric space is complete exactly when every Cauchy sequence converges to a
point of the space. -/
-- Proof sketch: use `cauchySeq_tendsto_of_complete` for the forward implication and
-- `Metric.complete_of_cauchySeq_tendsto` for the converse implication.
theorem completeSpace_iff_cauchySeq_tendsto :
    CompleteSpace X ↔ ∀ u : ℕ → X, CauchySeq u → ∃ x : X, Tendsto u atTop (nhds x) := by
  constructor
  · intro hX u hu
    letI : CompleteSpace X := hX
    exact cauchySeq_tendsto_of_complete hu
  · intro h
    exact Metric.complete_of_cauchySeq_tendsto h
