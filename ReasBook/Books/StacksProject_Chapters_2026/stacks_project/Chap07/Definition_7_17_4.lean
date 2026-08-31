module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory
namespace Sheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type w)]

/- Domain-style sampling for Definition 7.17.4:
- primary domain: quasi-compactness in the topos of set-valued sheaves, expressed through locally
  surjective coproduct maps;
- sampled owner abstractions:
  `GrothendieckTopology.QuasiCompactObject`,
  `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Sheaf.isColimitSheafifyCocone`,
  `ObjectProperty.IsClosedUnderFiniteCoproducts`;
- source-facing layer here: `Sheaf.IsQuasiCompactObject`;
- core/canonical recall for part (2): quasi-compactness of the terminal sheaf
  `Sheaf.IsQuasiCompactObject (⊤_ (Sheaf J (Type w)))`;
- core/canonical owners reused here: coproducts in `Sheaf J (Type w)` and the terminal sheaf.

Primitive data are only a locally surjective morphism from a coproduct into `ℱ`. The induced map
from a finite subcoproduct is derived directly from the canonical coproduct owner
`Limits.Sigma.desc`. A finite subset of the original index type is primitive here, while an
auxiliary finite type or a specific `Fin n` presentation is only derived bookkeeping and should
not be part of the public owner field. -/

/- Definition 7.17.4 (1): an object `ℱ` of the topos `Sh(C)` is quasi-compact if every
locally surjective morphism from a coproduct `∐ᵢ ℱᵢ ⟶ ℱ` admits a finite subcoproduct whose
induced morphism to `ℱ` is still locally surjective. -/
@[mk_iff isQuasiCompactObject_iff]
class IsQuasiCompactObject (ℱ : Sheaf J (Type w)) : Prop where
  finite_subcoproduct {ι : Type w} (ℱᵢ : ι → Sheaf J (Type w)) [HasCoproduct ℱᵢ]
      (π : (∐ ℱᵢ) ⟶ ℱ) (hπ : IsLocallySurjective π) :
      ∃ (T : Set ι) (hT : T.Finite),
        let _ : Fintype T := hT.fintype
        let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type w)) :=
          Sheaf.instHasColimitsOfShape
        let πT : (∐ fun i : T ↦ ℱᵢ i.1) ⟶ ℱ :=
          Limits.Sigma.desc
            (fun i : T ↦
              Limits.Sigma.ι (fun j : ι ↦ ℱᵢ j) i.1 ≫ π)
        IsLocallySurjective πT

end Sheaf

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/- Definition 7.17.4 (2): the topos `Sh(C)` is quasi-compact if and only if its terminal sheaf is
a quasi-compact object. The canonical owner is the direct terminal-sheaf expression below, so no
parallel alias is introduced. -/
#check (Sheaf.IsQuasiCompactObject (⊤_ (Sheaf J (Type (max u v)))) : Prop)
end GrothendieckTopology

end CategoryTheory
