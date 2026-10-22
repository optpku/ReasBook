/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {𝕜 : Type u} {E : Type v} {β : Type w}

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
variable [PosSMulMono 𝕜 E] [PartialOrder β]

/-- Example 10.22: a monotone or antitone function on a linearly ordered module is quasiconvex on
the whole space. The textbook extended-real-valued statement on a real vector space is the
specialization `𝕜 = ℝ` and `β = EReal`. -/
-- Proof sketch: split into the increasing and decreasing cases; then apply
-- `Monotone.quasiconvexOn` or `Antitone.quasiconvexOn` on `Set.univ`.
theorem quasiconvexOn_univ_of_monotone_or_antitone
    {f : E → β} (hf : Monotone f ∨ Antitone f) :
    QuasiconvexOn 𝕜 Set.univ f :=
  hf.elim Monotone.quasiconvexOn Antitone.quasiconvexOn
