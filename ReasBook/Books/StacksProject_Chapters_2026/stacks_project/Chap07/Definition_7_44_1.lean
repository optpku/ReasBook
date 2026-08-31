module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable [Functor.IsContinuous u J K]

/- Domain-style sampling for Definition 7.44.1:
- primary domain: direct-image functors on sheaf categories induced by continuous functors of
  sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafAdjunctionContinuous`,
  `IsMorphismOfSites`;
- source-facing layer: the Stacks definition of the direct-image functor `f_*` attached to a
  morphism of sites presented by a continuous functor `u : C ⥤ D`;
- core/canonical owner: `u.sheafPushforwardContinuous A J K`;
- bridge/view: the underlying-presheaf comparison
  `u.sheafPushforwardContinuousCompSheafToPresheafIso A J K`, expressing that the owner functor
  is induced by precomposition with `u.op`.

Primitive data are only the topologies `J`, `K`, the functor `u`, and its continuity. The sheaf
pushforward and its comparison with precomposition on presheaves are derived API of that owner, so
this file should recall the canonical owner directly rather than introduce a local alias or wrapper.
-/

/- Definition 7.44.1: if `f : (D, K) ⟶ (C, J)` is the morphism of sites presented by a continuous
functor `u : C ⥤ D`, then the pushforward on sheaves of `A`-valued algebraic structures is the
canonical functor `u.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`. -/
recall Functor.sheafPushforwardContinuous

/- Companion check: on presheaves of `A`-valued algebraic structures, pushforward is just
precomposition with `u.op`, i.e. `u^p ℱ (U) = ℱ (u.obj U)`. -/
#check (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op

/- Companion recall: the sheaf pushforward functor above is induced by the same precomposition rule
on the underlying presheaves, which is the precise formal content of the objectwise formula
`f_*ℱ(U) = ℱ(uU)`. -/
recall Functor.sheafPushforwardContinuousCompSheafToPresheafIso

end
