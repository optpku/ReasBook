module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import stacks_project.Chap06.Definition_6_3_2
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open TopCat.Presheaf
open scoped TopCat

universe u

noncomputable section

/- Domain-style sampling for Example 6.11.3:
- primary domain: constant set-valued presheaves and sheaves on a topological space, together with
  their stalks;
- sampled owner API:
  `Functor.const`,
  `TopCat.Presheaf.Γgerm`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`,
  `CategoryTheory.constantSheaf`;
- best owner abstraction: the canonical stalk comparison
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, specialized to the constant presheaf;
- primitive data: the space `X`, the value type `A`, and the point `x : X`;
- derived API: the identification `A ≅ (A_p)_x` via `Γgerm` for the constant presheaf, and the
  composite map `A ⟶ \underline{A}_x`.

Source/core/bridge triage:
- `source-facing`: the map `(A_p)_x ⟶ \underline{A}_x` induced by sheafification, and the
  companion composite `A ⟶ \underline{A}_x`;
- `core/canonical`: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- `bridge/view`: `TopCat.Presheaf.Γgerm` for the constant presheaf.
-/

section

variable (X : TopCat.{u}) (A : Type u)

/-- Helper for Example 6.11.3: the canonical stalk map of the constant presheaf is an isomorphism. -/
theorem constantPresheafΓgerm_isIso (x : X) :
    IsIso (Γgerm (A ₚ X) x) := by
  -- Collapse the stalk colimit along the top neighborhood of `x`.
  let F : (OpenNhds x)ᵒᵖ ⥤ Type u := (OpenNhds.inclusion x).op ⋙ (A ₚ X)
  let j : (OpenNhds x)ᵒᵖ := op (⊤ : OpenNhds x)
  have hj : IsInitial j := by
    refine IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y m ↦ ?_)
    · exact (homOfLE le_top).op
    · exact Subsingleton.elim _ _
  -- Once the stalk is identified with this colimit, the initial object computes it.
  change IsIso (colimit.ι F j)
  letI : ∀ (i j : (OpenNhds x)ᵒᵖ) (f : i ⟶ j), IsIso (F.map f) := by
    intro i j f
    dsimp [F]
    infer_instance
  letI : HasColimit F := hasColimit_of_domain_hasInitial
  exact isIso_ι_of_isInitial hj F

/-- Helper for Example 6.11.3: the global germ map of the constant presheaf is bijective on every stalk. -/
theorem constantPresheafΓgerm_bijective (x : X) :
    Function.Bijective (Γgerm (A ₚ X) x) := by
  -- Extract the underlying equivalence from the stalk isomorphism.
  haveI := constantPresheafΓgerm_isIso X A x
  exact (asIso (Γgerm (A ₚ X) x)).toEquiv.bijective

end

section

variable (X : TopCat.{u})
variable (A : Type u)

local notation "J" => Opens.grothendieckTopology X
local notation "hTop" =>
  IsTerminal.ofUniqueHom (fun U : Opens X ↦ Opens.leTop U) (fun U m ↦ Subsingleton.elim _ _)

/- Example 6.11.3: the canonical map `(A_p)_x ⟶ \underline{A}_x` is the specialization of the
owner theorem `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` to the constant presheaf.
-/
recall TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso

/- Source-facing specialization of the owner theorem to the constant presheaf `A_p`. -/
#check
  fun x : X ↦ stalkFunctor_map_unit_toSheafify_isIso x (Type u) (A ₚ X)

/-- Helper for Example 6.11.3: rewrite the canonical map to the constant-sheaf stalk through the stalk map of sheafification. -/
private theorem constantSheafΓgerm_eq (x : X) :
    (constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x =
      Γgerm (A ₚ X) x ≫
        (stalkFunctor (Type u) x).map (toSheafify J (A ₚ X)) := by
  -- The bridge is `stalkFunctor_map_germ` evaluated on the top open set.
  simpa using
    (stalkFunctor_map_germ (⊤ : Opens X) x True.intro
      (toSheafify J (A ₚ X))).symm

/-- Helper for Example 6.11.3: the composite `A = (A_p)_x ⟶ \underline{A}_x` is an isomorphism. -/
theorem constantSheafΓgerm_isIso (x : X) :
    IsIso
      ((constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x) := by
  -- Rewrite the target map as the constant-presheaf germ map followed by sheafification on stalks.
  rw [constantSheafΓgerm_eq X A x]
  -- Both factors are canonical isomorphisms, so their composite is as well.
  exact IsIso.comp_isIso' (constantPresheafΓgerm_isIso X A x)
    (stalkFunctor_map_unit_toSheafify_isIso x (Type u) (A ₚ X))

/-- Example 6.11.3: the composite map `A ⟶ \underline{A}_x` is bijective. -/
theorem constantSheafΓgerm_bijective (x : X) :
    Function.Bijective
      ((constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x) := by
  -- Convert the composite isomorphism into an equivalence of underlying functions.
  haveI := constantSheafΓgerm_isIso X A x
  let e := asIso
    ((constantSheafAdj J (Type u) hTop).unit.app A ≫
      Γgerm ((constantSheaf J (Type u)).obj A).obj x)
  exact e.toEquiv.bijective

end
