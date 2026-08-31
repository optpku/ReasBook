module

public import Mathlib.Topology.Irreducible
public import Mathlib.Data.Set.Card
import Mathlib.SetTheory.ZFC.PSet

@[expose] public section

open Set

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for Lemma 5.8.5:
- primary domain: irreducible components under continuous surjective maps
- inspected owner declarations:
  `irreducibleComponents`,
  `irreducibleComponent`,
  `sUnion_irreducibleComponents`,
  `isIrreducible_iff_sUnion_isClosed`
- best owner abstraction: `irreducibleComponents X` is the core/canonical owner; the Stacks lemma
  is a `bridge/view` cardinality consequence of the fact that, when `X` has finitely many
  irreducible components, every irreducible component of `Y` is the closure of the image of some
  irreducible component of `X`
- primitive-vs-derived split: the primitive data are the continuous surjection `f` and the
  canonical owner sets `irreducibleComponents X` and `irreducibleComponents Y`; the finite-cardinal
  inequality is derived from the inclusion of `irreducibleComponents Y` into the finite closure-image
  family `{closure (f '' Z) | Z ∈ irreducibleComponents X}`, not from a separate local wrapper or
  chosen embedding of components
-/

/-- For a continuous surjection with finitely many irreducible components upstairs, every
irreducible component downstairs is the closure of the image of some irreducible component
upstairs. -/
theorem exists_irreducibleComponent_closure_image_eq_of_surjective_continuous
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f)
    (hXfin : (irreducibleComponents X).Finite) (W : irreducibleComponents Y) :
    ∃ Z : irreducibleComponents X, closure (f '' (Z : Set X)) = (W : Set Y) := by
  classical
  let S : Set (Set Y) := Set.range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  letI : Finite (irreducibleComponents X) := hXfin.to_subtype
  have hS : S.Finite := by
    simpa [S] using
      Set.finite_range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  have hcover : (W : Set Y) ⊆ ⋃₀ S := by
    intro y hy
    obtain ⟨x, rfl⟩ := hf_surj y
    refine mem_sUnion.2 ⟨closure (f '' irreducibleComponent x), ?_, ?_⟩
    · exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, rfl⟩
    · simpa using
        (subset_closure ⟨x, mem_irreducibleComponent, rfl⟩ :
          f x ∈ closure (f '' irreducibleComponent x))
  obtain ⟨Z, hZS, hWZ⟩ := isIrreducible_iff_sUnion_isClosed.mp W.2.1 hS.toFinset
    (fun Z hZ ↦ by
      rcases hS.mem_toFinset.mp hZ with ⟨Z', -, rfl⟩
      simp)
    (hS.coe_toFinset.symm ▸ hcover)
  rcases hS.mem_toFinset.mp hZS with ⟨Z, -, rfl⟩
  exact ⟨Z, Set.Subset.antisymm (W.2.2 ((Z.2.1.image f hf_cont.continuousOn).closure) hWZ) hWZ⟩

/-- Lemma 5.8.5: a surjective continuous map sends a space with exactly `n` irreducible
components to a space with at most `n` irreducible components. -/
theorem irreducibleComponents_encard_le_of_surjective_continuous
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f) {n : ℕ}
    (hX : (irreducibleComponents X).encard = n) :
    (irreducibleComponents Y).encard ≤ n := by
  classical
  let S : Set (Set Y) := Set.range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  have hXfin : (irreducibleComponents X).Finite := Set.finite_of_encard_eq_coe hX
  have hYS : irreducibleComponents Y ⊆ S := by
    intro W hW
    obtain ⟨Z, hZ⟩ :=
      exists_irreducibleComponent_closure_image_eq_of_surjective_continuous hf_surj hf_cont hXfin
        ⟨W, hW⟩
    have hZS : closure (f '' (Z : Set X)) ∈ S := by
      exact ⟨Z, by simp⟩
    simpa [hZ] using hZS
  have hS : S.encard ≤ (irreducibleComponents X).encard := by
    simpa [S] using
      (Set.encard_image_le (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
        (univ : Set (irreducibleComponents X)))
  calc
    (irreducibleComponents Y).encard ≤ S.encard := Set.encard_le_encard hYS
    _ ≤ (irreducibleComponents X).encard := hS
    _ = n := hX

end
