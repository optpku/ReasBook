module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_6_1
public import stacks_project.Chap06.Lemma_6_6_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf RingCat.{u})

/- Domain-style sampling for Lemma 6.24.4:
- primary domain: pullback/pushforward of presheaves of modules along a continuous map, together
  with same-site change of rings along the counit `f_p f_* 𝒪 ⟶ 𝒪`;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pushforwardComp`,
  `TopCat.Presheaf.Lemma_6_6_2`'s identity-on-opens transport `ringPresheafHomOverId`;
- best owner abstraction: the source-facing tensor-pullback functor
  `𝒪 ⊗_{c_𝒪} f_p (-)`, presented canonically as the composite of the two owner pullback functors
  induced by the unit and counit of `TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`;
- primitive data: the continuous map `f`, the ring presheaf `𝒪`, and the canonical unit/counit
  maps derived from the presheaf pullback-pushforward adjunction;
- derived API: the composite tensor functor and its Hom-set equivalence.

Source/core/bridge triage:
- `source-facing`: the tensor-by-counit functor
  `𝒪 ⊗_{c_𝒪} f_p (-) : PMod(f_*𝒪) ⥤ PMod(𝒪)` and the induced bijection
  `Mor_{PMod(𝒪)}(𝒪 ⊗_{c_𝒪} f_p 𝒢, ℱ) ≃ Mor_{PMod(f_*𝒪)}(𝒢, f_*ℱ)`;
- `core/canonical`: `PresheafOfModules.pullbackPushforwardAdjunction` for the unit and counit
  ring maps, together with `PresheafOfModules.pushforwardComp`;
- `bridge/view`: the identity-on-opens transport `ringPresheafHomOverId` for the counit and the
  right triangle identity identifying the composite right adjoint with pushforward along
  `𝟙 (f_*𝒪)`.

Primitive-vs-derived decision:
- the source tensor construction should stay public;
- the owner pullback/pushforward functors and their adjunctions remain derived from the canonical
  mathlib/project API, so there is no need for a parallel wrapper around the owner adjunction;
- the triangle identity is used only on the right-adjoint side, matching the textbook semantics
  and the sheaf analogue `Lemma_6_24_8`.
-/

/- Lemma 6.24.4, owner ingredients: the relevant adjunctions are the canonical
`PresheafOfModules.pullbackPushforwardAdjunction` instances for the unit and counit ring maps, and
the comparison of the composite right adjoint with the identity-ring pushforward comes from
`PresheafOfModules.pushforwardComp` together with the right triangle identity for
`TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction
recall PresheafOfModules.pushforwardComp

/-- The extension-of-scalars functor corresponding to `𝒪 ⊗_{c_𝒪} f_p (-)`. -/
noncomputable def continuous_map_presheaf_module_tensor_functor :
    PMod((pushforward RingCat f).obj 𝒪) ⥤ PMod(𝒪) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  PresheafOfModules.pullback η ⋙ PresheafOfModules.pullback ε

-- Proof sketch: `PresheafOfModules.pushforwardComp` identifies the composite right adjoint
-- `pushforward ε_𝒪 ⋙ pushforward η_{f_* 𝒪}` with pushforward along
-- `η_{f_* 𝒪} ≫ f_*(ε_𝒪)`, and the latter is `𝟙_{f_* 𝒪}` by the right triangle identity for
-- `pullbackPushforwardAdjunction RingCat f`.
/-- The composite right adjoint for the counit and unit ring maps is canonically the ordinary
pushforward along the identity of `f_* 𝒪`. -/
public noncomputable def continuous_map_presheaf_module_pushforwardCompIso :
    let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
    let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
    PresheafOfModules.pushforward ε ⋙ PresheafOfModules.pushforward η ≅
      PresheafOfModules.pushforward (𝟙 ((pushforward RingCat f).obj 𝒪)) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  let hηε : η ≫ (Opens.map f).op.whiskerLeft ε = 𝟙 ((pushforward RingCat f).obj 𝒪) := by
    convert (pullbackPushforwardAdjunction RingCat f).right_triangle_components 𝒪 using 1
  PresheafOfModules.pushforwardComp η ε ≪≫
    eqToIso (congrArg PresheafOfModules.pushforward hηε)

/-- Lemma 6.24.4: the tensor-pullback object `𝒪 ⊗_{c_𝒪} f_p 𝒢` represents morphisms into `ℱ`
exactly as morphisms from `𝒢` into the direct image `f_* ℱ`. -/
noncomputable def continuous_map_presheaf_module_tensor_hom_equiv
    (𝒢 : PMod((pushforward RingCat f).obj 𝒪)) (ℱ : PMod(𝒪)) :
    ((continuous_map_presheaf_module_tensor_functor f 𝒪).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (PresheafOfModules.pushforward (𝟙 ((pushforward RingCat f).obj 𝒪))).obj ℱ) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  ((PresheafOfModules.pullbackPushforwardAdjunction ε).homEquiv
      ((PresheafOfModules.pullback η).obj 𝒢) ℱ).trans
    (((PresheafOfModules.pullbackPushforwardAdjunction η).homEquiv 𝒢
        ((PresheafOfModules.pushforward ε).obj ℱ)).trans
      ((Iso.refl 𝒢).homCongr
        ((continuous_map_presheaf_module_pushforwardCompIso f 𝒪).app ℱ)))

-- Proof sketch: `continuous_map_presheaf_module_tensor_hom_equiv` is an equivalence of hom-sets,
-- so its underlying function is bijective.
/-- The morphism correspondence of `continuous_map_presheaf_module_tensor_hom_equiv` is bijective.
-/
theorem continuous_map_presheaf_module_tensor_hom_equiv_bijective
    (𝒢 : PMod((pushforward RingCat f).obj 𝒪)) (ℱ : PMod(𝒪)) :
    Function.Bijective (continuous_map_presheaf_module_tensor_hom_equiv f 𝒪 𝒢 ℱ) :=
  (continuous_map_presheaf_module_tensor_hom_equiv f 𝒪 𝒢 ℱ).bijective

end
