/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.63: for a subset `C` of a metric space `X`, the diameter is the canonical extended
diameter `Metric.ediam C`, and the distance function to `C`, with value `∞` when `C = ∅`, is the
canonical extended infimum-edistance map `fun x ↦ Metric.infEDist x C`. -/
recall Metric.ediam {α : Type u} [PseudoEMetricSpace α] (s : Set α) : ENNReal

/- The distance-to-set function is the canonical extended infimum edistance. -/
recall Metric.infEDist {α : Type u} [PseudoEMetricSpace α] (x : α) (s : Set α) : ENNReal

/- For the empty set, the extended distance-to-set function is constantly `∞`. -/
recall Metric.infEDist_empty
