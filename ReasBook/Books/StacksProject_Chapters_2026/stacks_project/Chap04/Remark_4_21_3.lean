module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Antisymmetrization
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

variable {I : Type u} [Preorder I]

/- Domain-style sampling for Remark 4.21.3:
- primary domain: preorder categories, antisymmetrization, and the induced equivalences of direct
  and inverse system categories.
- inspected owner declarations:
  `toAntisymmetrization_le_toAntisymmetrization_iff`,
  `ofAntisymmetrization`,
  `Functor.IsEquivalence`,
  `Functor.asEquivalence`,
  `CategoryTheory.Equivalence.congrLeft`.
- owner abstraction: the quotient functor
  `toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)` endowed with
  `Functor.IsEquivalence`, then the induced functor-category equivalences from
  `Functor.asEquivalence.congrLeft`, and finally `Functor.Final` / `Functor.Initial` for colimit/limit
  comparison.
- primitive data: the quotient map `toAntisymmetrization`, the order comparison theorem
  `toAntisymmetrization_le_toAntisymmetrization_iff`, and the chosen section
  `ofAntisymmetrization`.
- derived API: the category equivalences for systems and inverse systems, plus the resulting
  colimit/limit comparison theorems.

Source/core/bridge triage:
- `source-facing`: the quotient map `π`, its order characterization, the chosen section, and the
  induced equivalences between direct and inverse system categories.
- `core/canonical`: `Functor.IsEquivalence`, `Equivalence.congrLeft`,
  `Functor.Final.hasColimit_comp_iff`, `Functor.Final.colimitIso`,
  `Functor.Initial.hasLimit_comp_iff`, and `Functor.Initial.limitIso`.
- `bridge/view`: `toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)`.
-/

section

variable (i j : I)

/- The quotient order on the antisymmetrization is exactly the canonical owner
theorem `toAntisymmetrization_le_toAntisymmetrization_iff`. -/
#check (by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  exact (toAntisymmetrization_le_toAntisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) i ≤ toAntisymmetrization (· ≤ ·) j ↔ i ≤ j))

end

/- The chosen representative map from the antisymmetrization back to the preorder
is exactly the canonical section `ofAntisymmetrization`. -/
#check (by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  exact (ofAntisymmetrization (· ≤ ·) : Antisymmetrization I (· ≤ ·) → I))

/- The quotient map followed by the chosen representative is canonically the
identity on the antisymmetrization. -/
recall toAntisymmetrization_ofAntisymmetrization

private theorem toAntisymmetrization_obj_hom (i : I) :
    i ≤ (OrderEmbedding.ofAntisymmetrization I) (toAntisymmetrization (· ≤ ·) i) := by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  change i ≤ ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i)
  rw [← toAntisymmetrization_le_toAntisymmetrization_iff,
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·)]

private theorem toAntisymmetrization_obj_inv (i : I) :
    (OrderEmbedding.ofAntisymmetrization I) (toAntisymmetrization (· ≤ ·) i) ≤ i := by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  change ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i) ≤ i
  rw [← toAntisymmetrization_le_toAntisymmetrization_iff,
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·)]

private noncomputable def toAntisymmetrizationFunctorUnitIso :
    𝟭 I ≅
      (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)) ⋙
        (OrderEmbedding.ofAntisymmetrization I).toOrderHom.toFunctor := by
  refine NatIso.ofComponents (fun i ↦ ?_) fun {_ _} _ ↦ Subsingleton.elim _ _
  refine ⟨(toAntisymmetrization_obj_hom i).hom, (toAntisymmetrization_obj_inv i).hom, ?_, ?_⟩ <;>
    exact Subsingleton.elim _ _

/-- Remark 4.21.3: the canonical quotient functor from a preorder to its antisymmetrization is an
equivalence of categories. -/
noncomputable instance antisymmetrizationFunctor_isEquivalence :
    Functor.IsEquivalence (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)) :=
  Functor.IsEquivalence.mk'
    (OrderEmbedding.ofAntisymmetrization I).toOrderHom.toFunctor
    toAntisymmetrizationFunctorUnitIso
    (NatIso.ofComponents
      (fun q ↦ eqToIso (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) q))
      fun {_ _} _ ↦ Subsingleton.elim _ _)

/-- Directedness descends from a preorder to its antisymmetrization. -/
instance [IsDirectedOrder I] :
    IsDirectedOrder (Antisymmetrization I (· ≤ ·)) := by
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂' a b ?_
  intro i j
  rcases (toAntisymmetrization_mono.directed_le i j) with ⟨k, hik, hjk⟩
  exact ⟨toAntisymmetrization (· ≤ ·) k, hik, hjk⟩

section

variable {C : Type v} [Category.{w} C]

/- Direct systems: precomposition along the quotient equivalence yields the
canonical equivalence between systems indexed by `I` and systems indexed by its
antisymmetrization. -/
#check ((toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)).asEquivalence.congrLeft :
  (I ⥤ C) ≌ (Antisymmetrization I (· ≤ ·) ⥤ C))

/- Direct systems: the colimit-existence comparison is exactly the specialized
owner theorem `Functor.Final.hasColimit_comp_iff`; the needed `Functor.Final` instance is derived
canonically from the equivalence instance above. -/
variable (F : Antisymmetrization I (· ≤ ·) ⥤ C)

#check (Functor.Final.hasColimit_comp_iff toAntisymmetrization_mono.functor :
  HasColimit (toAntisymmetrization_mono.functor ⋙ F) ↔ HasColimit F)

/- Direct systems: the resulting colimit comparison isomorphism is exactly the
specialized owner theorem `Functor.Final.colimitIso`. -/
variable [HasColimit F]

#check (Functor.Final.colimitIso toAntisymmetrization_mono.functor F :
  colimit (toAntisymmetrization_mono.functor ⋙ F) ≅ colimit F)

end

section

variable {C : Type v} [Category.{w} C]

/- Inverse systems: precomposition along the quotient equivalence for the order dual
gives the canonical equivalence between inverse systems indexed by `I` and by its
antisymmetrization; `OrderIso.dualAntisymmetrization` is the canonical bridge from the
antisymmetrization of the order dual to the order dual of the antisymmetrization. -/
#check (((toAntisymmetrization_mono.functor :
    Iᵒᵈ ⥤ Antisymmetrization Iᵒᵈ (· ≤ ·)).asEquivalence.congrLeft).trans
  (OrderIso.dualAntisymmetrization I).equivalence.congrLeft.symm :
    (Iᵒᵈ ⥤ C) ≌ ((Antisymmetrization I (· ≤ ·))ᵒᵈ ⥤ C))

/- Inverse systems: the limit-existence comparison is exactly the specialized owner
theorem `Functor.Initial.hasLimit_comp_iff`; the needed `Functor.Initial` instance is derived
canonically from the finality of `toAntisymmetrization_mono.functor`. -/
variable (F : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C)

#check (Functor.Initial.hasLimit_comp_iff toAntisymmetrization_mono.functor.op :
  HasLimit (toAntisymmetrization_mono.functor.op ⋙ F) ↔ HasLimit F)

/- Inverse systems: the resulting limit comparison isomorphism is exactly the
specialized owner theorem `Functor.Initial.limitIso`. -/
variable [HasLimit F]

#check (Functor.Initial.limitIso toAntisymmetrization_mono.functor.op F :
  limit (toAntisymmetrization_mono.functor.op ⋙ F) ≅ limit F)

end
