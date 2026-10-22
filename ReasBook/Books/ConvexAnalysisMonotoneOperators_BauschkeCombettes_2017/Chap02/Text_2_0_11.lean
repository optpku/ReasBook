/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗]

/- In a normed additive commutative group, the canonical metric is given by the norm of the
difference. -/
recall dist_eq_norm

/-- Text 2.0.11: the strong (norm) topology on a normed space is the topology induced by the
canonical metric `d x y = ‖x - y‖`. -/
theorem strong_topology_eq_metric_topology :
    (inferInstance : TopologicalSpace 𝓗) =
      (inferInstance : MetricSpace 𝓗).toUniformSpace.toTopologicalSpace := rfl
