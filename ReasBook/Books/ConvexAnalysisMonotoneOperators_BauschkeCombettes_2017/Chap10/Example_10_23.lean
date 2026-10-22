/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {𝕜 : Type u} {E : Type v} {β : Type w}

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E] [LinearOrder β]

/-- Example 10.23: truncating a quasiconvex function on the whole space from above by a constant
preserves quasiconvexity. The textbook statement for an extended-real-valued function on a real
vector space is the specialization `𝕜 = ℝ` and `β = EReal`. -/
-- Proof sketch: view `x ↦ min (f x) η` as the composition of `f` with the monotone map
-- `t ↦ min t η`, then apply `QuasiconvexOn.monotone_comp` on `univ`.
theorem quasiconvexOn_univ_min_const
    {f : E → β} (hf : QuasiconvexOn 𝕜 Set.univ f) (η : β) :
    QuasiconvexOn 𝕜 Set.univ (fun x ↦ min (f x) η) := by
  simpa only [Function.comp_apply] using
    hf.monotone_comp (monotone_id.min monotone_const)
