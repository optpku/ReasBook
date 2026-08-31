module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} X)
variable (𝒢 : SheafOfModules ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))
variable (ℱ : SheafOfModules 𝒪)

/- Domain-style sampling for Lemma 6.24.8:
- primary domain: pullback-pushforward adjunction for sheaves of modules along a continuous map,
  specialized to the direct-image ring sheaf `f_* 𝒪`;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Lemma_6_24_7`'s direct use of the same adjunction owner;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`;
- primitive data: the continuous map `f`, the sheaf of rings `𝒪`, and module sheaves
  `𝒢 : Mod(f_* 𝒪)` and `ℱ : Mod(𝒪)`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its canonical bijectivity
  theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the tensor-pullback/direct-image correspondence
  `Hom_𝒪(𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢, ℱ) ≃ Hom_{f_* 𝒪}(𝒢, f_* ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`;
- `bridge/view`: the source tensor-pullback notation is exactly the pullback functor
  `SheafOfModules.pullback (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`, so this item should
  reuse the canonical adjunction owner directly instead of rebuilding it from same-site
  change-of-rings and unit/counit helpers.
-/

private abbrev pushforwardRingSheaf : TopCat.Sheaf RingCat.{u} Y :=
  (Sheaf.pushforward RingCat.{u} f).obj 𝒪

/- Lemma 6.24.8, owner form: for the identity morphism `f_* 𝒪 ⟶ f_* 𝒪`, the canonical
pullback functor
`SheafOfModules.pullback (𝟙 (f_* 𝒪)) : Mod(f_* 𝒪) ⥤ Mod(𝒪)`
is left adjoint to the direct-image functor
`SheafOfModules.pushforward (𝟙 (f_* 𝒪)) : Mod(𝒪) ⥤ Mod(f_* 𝒪)`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.24.8: the tensor-pullback object
`𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢`,
which is the canonical pullback object
`(SheafOfModules.pullback (𝟙 (f_* 𝒪))).obj 𝒢`,
represents morphisms into `ℱ` exactly as morphisms from `𝒢` into the direct image `f_* ℱ`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback (𝟙 (pushforwardRingSheaf f 𝒪))).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward (𝟙 (pushforwardRingSheaf f 𝒪))).obj ℱ))

/- Lemma 6.24.8 companion: the source bijection statement is exactly the canonical bijectivity
theorem for this specialized adjunction equivalence. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ))

end
