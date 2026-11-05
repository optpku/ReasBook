module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import stacks_project.Chap04.Lemma_4_33_3
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.33.12:
- primary domain: fibred functors and strongly cartesian lifts under composition;
- sampled owner declarations:
  `Functor.IsFibered`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.isStronglyCartesian_map_comp`, proved in Lemma 4.33.3;
- best owner abstraction: `Functor.IsFibered`;
- primitive data: fibred structures on `F` and `G` together with the cartesian lifts supplied by
  `IsPreFibered.exists_isCartesian`;
- derived API: the induced fibred structure on the composite functor `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the composite of fibred functors is fibred;
- `core/canonical`: the owner predicate `Functor.IsFibered`;
- `bridge/view`: the instance below deriving the composite owner from the two input owners. -/

-- Proof sketch: choose cartesian lifts first for `G` and then for `F`; in a fibred category these
-- lifts are strongly cartesian, and Lemma 4.33.3 upgrades the resulting lift to a strongly
-- cartesian morphism for the composite functor.
/-- Lemma 4.33.12: if `F : A ⥤ B` is fibred and `G : B ⥤ C` is fibred, then the composite functor
`F ⋙ G : A ⥤ C` is fibred. -/
instance isFibered_comp
    (F : A ⥤ B) (G : B ⥤ C) [F.IsFibered] [G.IsFibered] :
    (F ⋙ G).IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun a R f ↦ by
    obtain ⟨b, ψ, hψ⟩ := IsPreFibered.exists_isCartesian G rfl f
    obtain ⟨a', φ, hφ⟩ := IsPreFibered.exists_isCartesian F rfl ψ
    letI : G.IsCartesian f ψ := hψ
    letI : F.IsCartesian ψ φ := hφ
    have hb : F.obj a' = b := IsHomLift.domain_eq F ψ φ
    subst b
    have hφ_base : ψ = F.map φ := by
      simpa using (IsHomLift.eq_of_isHomLift F ψ φ)
    subst ψ
    have hR : G.obj (F.obj a') = R := IsHomLift.domain_eq G f (F.map φ)
    subst R
    have hf : f = (F ⋙ G).map φ := by
      simpa [Functor.comp_map] using (IsHomLift.eq_of_isHomLift G f (F.map φ))
    subst f
    letI : F.IsCartesian (F.map φ) φ := hφ
    letI : G.IsCartesian (G.map (F.map φ)) (F.map φ) := by
      simpa [Functor.comp_map] using hψ
    exact ⟨a', φ, isStronglyCartesian_map_comp F G φ⟩

end CategoryTheory.Functor
