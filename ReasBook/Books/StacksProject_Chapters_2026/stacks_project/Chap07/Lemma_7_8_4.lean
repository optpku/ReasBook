module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.Sieves

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w t s

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {U : C}
variable {I : Type t} {J : Type s}
variable (Ui : I → C) (π : ∀ i, Ui i ⟶ U)
variable (Vj : J → C) (ψ : ∀ j, Vj j ⟶ U)
variable (F : Cᵒᵖ ⥤ Type w)

/-- Helper for Lemma 7.8.4: componentwise slice isomorphisms force inclusion of the generated
sieves. -/
private theorem sieve_ofArrows_le_of_componentwise_iso
    (α : I → J)
    (hα : ∀ i, Over.mk (π i) ≅ Over.mk (ψ (α i))) :
    Sieve.ofArrows Ui π ≤ Sieve.ofArrows Vj ψ := by
  -- Each generator `π i` factors through the corresponding generator `ψ (α i)` in the slice.
  rw [Sieve.ofArrows]
  refine (Sieve.generate_le_iff (R := Presieve.ofArrows Ui π) (S := Sieve.ofArrows Vj ψ)).2 ?_
  rw [Presieve.ofArrows_le_iff]
  intro i
  refine ⟨Vj (α i), (hα i).hom.left, ψ (α i), Presieve.ofArrows.mk (α i), ?_⟩
  simpa using (Over.w ((hα i).hom))

/-- Helper for Lemma 7.8.4: comparison data in both directions identify the generated sieves. -/
private theorem sieve_ofArrows_eq_of_tautological_data
    (α : I → J) (β : J → I)
    (hα : ∀ i, Over.mk (π i) ≅ Over.mk (ψ (α i)))
    (hβ : ∀ j, Over.mk (ψ j) ≅ Over.mk (π (β j))) :
    Sieve.ofArrows Ui π = Sieve.ofArrows Vj ψ := by
  -- The two inclusions come from factoring each generator through an isomorphic one.
  exact le_antisymm
    (sieve_ofArrows_le_of_componentwise_iso Ui π Vj ψ α hα)
    (sieve_ofArrows_le_of_componentwise_iso Vj ψ Ui π β hβ)

/-- Lemma 7.8.4: tautologically equivalent indexed families of morphisms with the same fixed
target impose equivalent sheaf conditions on any presheaf. -/
theorem isSheafFor_ofArrows_iff_of_tautological_equivalence
    (α : I → J) (β : J → I)
    (hα : ∀ i, Over.mk (π i) ≅ Over.mk (ψ (α i)))
    (hβ : ∀ j, Over.mk (ψ j) ≅ Over.mk (π (β j))) :
    (Presieve.ofArrows Ui π).IsSheafFor F ↔ (Presieve.ofArrows Vj ψ).IsSheafFor F := by
  -- Step 1: replace each indexed-family sheaf condition by the equivalent generated-sieve form.
  calc
    (Presieve.ofArrows Ui π).IsSheafFor F ↔ (Sieve.ofArrows Ui π).arrows.IsSheafFor F := by
      simpa [Sieve.ofArrows] using
        (Presieve.isSheafFor_iff_generate (P := F) (Presieve.ofArrows Ui π))
    _ ↔ (Sieve.ofArrows Vj ψ).arrows.IsSheafFor F := by
      -- Step 2: tautological comparison identifies the generated sieves on `U`.
      rw [sieve_ofArrows_eq_of_tautological_data Ui π Vj ψ α β hα hβ]
    _ ↔ (Presieve.ofArrows Vj ψ).IsSheafFor F := by
      simpa [Sieve.ofArrows] using
        (Presieve.isSheafFor_iff_generate (P := F) (Presieve.ofArrows Vj ψ)).symm

end CategoryTheory
