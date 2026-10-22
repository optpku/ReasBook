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

/- Text 1.0.66: in a metric space, convergence of a sequence to a point is expressed by the
canonical filter-theoretic notion `Tendsto u atTop (nhds x)`. -/
recall Tendsto

/-
Text 1.0.66: in a metric space, convergence to `x` is canonically characterized by
`tendsto_iff_dist_tendsto_zero`; the sequence-at-`atTop` formulation is the textbook
specialization recorded below.
-/
recall tendsto_iff_dist_tendsto_zero {α : Type u} {β : Type v} [PseudoMetricSpace α]
    {f : β → α} {l : Filter β} {a : α} :
    Tendsto f l (nhds a) ↔ Tendsto (fun b ↦ dist (f b) a) l (nhds 0)

/-- In a metric space, a sequence converges to `x` exactly when its distances to `x` tend to `0`.
-/
-- Proof sketch: specialize `tendsto_iff_dist_tendsto_zero` to the filter `atTop` on `ℕ`.
theorem sequence_tendsto_iff_dist_tendsto_zero {u : ℕ → X} {x : X} :
    Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0) := by
  simpa using
    (tendsto_iff_dist_tendsto_zero :
      Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0))
