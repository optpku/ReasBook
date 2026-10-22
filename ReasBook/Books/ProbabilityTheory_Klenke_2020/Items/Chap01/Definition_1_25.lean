/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Set.Notation

universe u

variable {Ω : Type u}

/-- Definition 1.25: The trace `𝒜 |_ A` of a class of subsets `𝒜` of `Ω` on a set `A` is the
class of subsets of the subtype `A` obtained by restricting each member of `𝒜` to `A`, equivalently
by pulling it back along the canonical inclusion `Subtype.val : A → Ω`; here `A ↓∩ s` is Lean's
canonical subtype-level version of the intersection `A ∩ s` from (1.6). -/
def traceOn (𝒜 : Set (Set Ω)) (A : Set Ω) : Set (Set A) :=
  Set.preimage (Subtype.val : A → Ω) '' 𝒜

/-- A subset of `A` belongs to the trace of `𝒜` on `A` exactly when it is the restriction of some
member of `𝒜` to `A`. -/
theorem mem_traceOn_iff {𝒜 : Set (Set Ω)} {A : Set Ω} {s : Set A} :
    s ∈ traceOn 𝒜 A ↔ ∃ t ∈ 𝒜, s = Subtype.val ⁻¹' t := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
