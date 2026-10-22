/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

variable {𝕜 : Type u} {E : Type v} {β : Type w}

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E] [CompleteLattice β]

/-- On a convex set, the pointwise supremum of a family of quasiconvex functions is
quasiconvex. -/
theorem Convex.quasiconvexOn_iSup {s : Set E} {I : Type x} {f : I → E → β}
    (hs : Convex 𝕜 s) (hf : ∀ i, QuasiconvexOn 𝕜 s (f i)) :
    QuasiconvexOn 𝕜 s (fun x ↦ ⨆ i, f i x) := by
  classical
  intro r
  rcases isEmpty_or_nonempty I with hI | hI
  · by_cases hr : (⊥ : β) ≤ r
    · let _ : IsEmpty I := hI
      simpa [iSup_of_empty, hr] using hs
    · let _ : IsEmpty I := hI
      simpa [iSup_of_empty, hr] using (convex_empty : Convex 𝕜 (∅ : Set E))
  · let _ : Nonempty I := hI
    have hconv : Convex 𝕜 (⋂ i, {x : E | x ∈ s ∧ f i x ≤ r}) := by
      refine convex_iInter fun i ↦ ?_
      simpa [QuasiconvexOn] using hf i r
    have hset :
        {x : E | x ∈ s ∧ (⨆ i, f i x) ≤ r} = ⋂ i, {x : E | x ∈ s ∧ f i x ≤ r} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hx i
        exact ⟨hx.1, (iSup_le_iff.1 hx.2) i⟩
      · intro hx
        refine ⟨(hx (Classical.choice hI)).1, iSup_le_iff.2 fun i ↦ (hx i).2⟩
    rw [hset]
    exact hconv

/-- Proposition 10.24: the pointwise supremum of a family of quasiconvex functions is
quasiconvex on the whole space. The textbook extended-real-valued real-vector-space statement is
the specialization `𝕜 = ℝ` and `β = EReal`. -/
-- Proof sketch: for each real threshold `ξ`, the lower level set of `x ↦ ⨆ i, f i x` is the
-- intersection of the lower level sets of the `f i`. Each of those sets is convex by
-- quasiconvexity, so their intersection is convex as well.
theorem quasiconvexOn_univ_iSup
    {I : Type x} {f : I → E → β} (hf : ∀ i, QuasiconvexOn 𝕜 Set.univ (f i)) :
    QuasiconvexOn 𝕜 Set.univ (fun x ↦ ⨆ i, f i x) := by
  simpa using convex_univ.quasiconvexOn_iSup hf
