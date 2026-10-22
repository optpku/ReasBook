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
open scoped Topology

variable {A : Type v} [Preorder A] [IsDirected A fun a b ↦ a ≤ b] [Nonempty A]
variable {𝓗 : Type u} [SeminormedAddCommGroup 𝓗]

/- Text 2.0.12: strong convergence of a net in a normed space is exactly the canonical
metric/net criterion recalled below; mathlib states it in the slightly more general setting of a
seminormed additive commutative group. -/
recall NormedAddCommGroup.tendsto_atTop
