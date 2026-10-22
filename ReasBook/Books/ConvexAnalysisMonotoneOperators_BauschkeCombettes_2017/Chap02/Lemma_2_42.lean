/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u v

variable {A : Type v} [Preorder A] [IsDirectedOrder A]
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Lemma 2.42: the norm on a Hilbert space is lower semicontinuous with respect to weak
convergence of nonempty directed nets. -/
theorem norm_le_liminf_of_tendsto_weakly (ξ : A → 𝓗) (x : 𝓗)
    [Nonempty A]
    (hξ : Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x))) :
    ‖x‖ ≤ Filter.liminf (fun a ↦ ‖ξ a‖) atTop := by
  -- TODO: as written with real-valued `Filter.liminf`, this statement is false for general weakly
  -- convergent nets. In an infinite-dimensional Hilbert space, weak neighborhoods of a nonzero
  -- point are unbounded, so one can build a weakly convergent net with no eventual norm upper
  -- bound. For such a net, mathlib's `Filter.liminf` on `ℝ` collapses to `0`, contradicting the
  -- desired inequality when `x ≠ 0`.
  sorry
