import Mathlib

-- This source-facing owner is built directly from mathlib's canonical `IsExtreme` predicate for
-- faces and the order-theoretic predicate `Minimal` for inclusion-minimal members of a family.

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [SMul 𝕜 E]

/-- Definition 3.10-extra-1. A minimal face of `P` over `𝕜` is a nonempty face `F` of `P` that
contains no proper nonempty face of `P`. -/
abbrev IsMinimalFaceOf (P F : Set E) : Prop :=
  Minimal (fun G : Set E ↦ G.Nonempty ∧ IsExtreme 𝕜 P G) F

/-- A minimal face is nonempty. -/
theorem IsMinimalFaceOf.nonempty {P F : Set E} (h : IsMinimalFaceOf 𝕜 P F) : F.Nonempty :=
  h.1.1

/-- A minimal face is a face. -/
theorem IsMinimalFaceOf.isExtreme {P F : Set E} (h : IsMinimalFaceOf 𝕜 P F) : IsExtreme 𝕜 P F :=
  h.1.2

/-- Any nonempty face of `P` contained in a minimal face `F` coincides with `F`. -/
theorem IsMinimalFaceOf.minimal {P F : Set E} (h : IsMinimalFaceOf 𝕜 P F) {G : Set E}
    (hG_nonempty : G.Nonempty) (hG : IsExtreme 𝕜 P G) (hGF : G ⊆ F) :
    F ⊆ G :=
  h.2 ⟨hG_nonempty, hG⟩ hGF

/-- A minimal face is canonically recognized as a face. -/
instance isMinimalFaceOf_fact_isExtreme {P F : Set E} (h : IsMinimalFaceOf 𝕜 P F) :
    Fact (IsExtreme 𝕜 P F) :=
  ⟨h.isExtreme⟩

/-- Unfolding lemma for `IsMinimalFaceOf`. -/
theorem isMinimalFaceOf_iff {P F : Set E} :
    IsMinimalFaceOf 𝕜 P F ↔
      F.Nonempty ∧
        IsExtreme 𝕜 P F ∧ ∀ ⦃G : Set E⦄, G.Nonempty → IsExtreme 𝕜 P G → G ⊆ F → F ⊆ G := by
  simpa [IsMinimalFaceOf, and_assoc] using
    (minimal_subset_iff' :
      Minimal (fun G : Set E ↦ G.Nonempty ∧ IsExtreme 𝕜 P G) F ↔
        (F.Nonempty ∧ IsExtreme 𝕜 P F) ∧
          ∀ ⦃G : Set E⦄, (G.Nonempty ∧ IsExtreme 𝕜 P G) → G ⊆ F → F ⊆ G)

/-- A minimal face of `P` is in particular a subset of `P`. -/
theorem IsMinimalFaceOf.subset {P F : Set E} (h : IsMinimalFaceOf 𝕜 P F) : F ⊆ P :=
  h.isExtreme.subset

end
