module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_14_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C₃ : Type u₁} [Category.{v₁} C₃]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {C₁ : Type u₃} [Category.{v₃} C₁]
variable (v : C₃ ⥤ C₂) (u : C₂ ⥤ C₁)
variable (J₃ : GrothendieckTopology C₃)
variable (J₂ : GrothendieckTopology C₂)
variable (J₁ : GrothendieckTopology C₁)

/- Domain-style sampling for Lemma 7.14.4:
- primary domain: Grothendieck topologies and morphisms of sites;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.isContinuous_comp`,
  `RepresentablyFlat.comp`,
  `IsMorphismOfSites`;
- source/core/bridge triage:
  `source-facing`: composition of morphisms of sites;
  `core/canonical`: the owner class `IsMorphismOfSites`, whose primitive data are continuity and
    representable flatness;
  `bridge/view`: the theorem `isMorphismOfSites_comp`, which exposes the canonical composition
    rule with the explicit middle topology.

Primitive data live in the owner abstraction `IsMorphismOfSites`: continuity and representable
flatness are not separate public fields of this lemma. The composite site morphism is therefore
derived via the canonical composition owners `Functor.isContinuous_comp` and
`RepresentablyFlat.comp`. Since the middle topology `J₂` is a genuine source input and is not
recoverable from the target `IsMorphismOfSites J₃ J₁ (v ⋙ u)`, this composition law belongs as an
explicit bridge theorem rather than as a global typeclass instance.
-/

/- Lemma 7.14.4: if `u : \mathcal C_2 \to \mathcal C_1` and `v : \mathcal C_3 \to \mathcal C_2`
are continuous functors which induce morphisms of sites, then the composite `u \circ v`, written
in Lean as `v ⋙ u`, is continuous. This is the composition statement underlying the induced
composite morphism of sites `\mathcal C_1 \to \mathcal C_3`. -/
recall Functor.isContinuous_comp
    [v.IsContinuous J₃ J₂] [u.IsContinuous J₂ J₁] :
  (v ⋙ u).IsContinuous J₃ J₁

/- Companion recall: representably flat functors are closed under composition, so the exactness
part of the site-morphism owner also composes along `v ⋙ u`. -/
recall RepresentablyFlat.comp [RepresentablyFlat v] [RepresentablyFlat u] :
  RepresentablyFlat (v ⋙ u)

/-- Lemma 7.14.4: if `u : \mathcal C_2 \to \mathcal C_1` and `v : \mathcal C_3 \to \mathcal C_2`
are morphisms of sites, then the composite `u \circ v`, written in Lean as `v ⋙ u`, again defines
a morphism of sites. The intermediate topology `J₂` is a genuine source input and is therefore an
explicit binder rather than a typeclass-inferred parameter. -/
theorem isMorphismOfSites_comp
    [IsMorphismOfSites J₃ J₂ v] [IsMorphismOfSites J₂ J₁ u] :
    IsMorphismOfSites J₃ J₁ (v ⋙ u) := by
  let _ : (v ⋙ u).IsContinuous J₃ J₁ := Functor.isContinuous_comp v u J₃ J₂ J₁
  infer_instance

end
