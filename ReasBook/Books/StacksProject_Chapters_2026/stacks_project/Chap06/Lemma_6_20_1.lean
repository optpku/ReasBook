module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) RingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective RingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.20.1:
- primary domain: sheafification of presheaves of modules on a topological space;
- sampled owner API:
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.sheafificationAdjunction_homEquiv_apply`,
  `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`;
- source/core/bridge triage:
  `source-facing`: the Stacks-style factorization through `ℱ ⟶ ℱ^#`;
  `core/canonical`: the module-sheafification adjunction and its underlying-additive compatibility;
  `bridge/view`: the existence-and-uniqueness reformulation derived from the owner Hom-equivalence.

Primitive data are the ring-presheaf map `toSheafify J 𝒪` and the canonical owner adjunction.
The additive compatibility statement is already an exact upstream owner theorem, and the
Hom-equivalence is derived API from that adjunction. The refined file therefore recalls the owner
theorem directly and keeps only the source-facing unique-factorization reformulation as a thin
bridge.
-/

/- Lemma 6.20.1: the compatibility of the sheafified `𝒪^#`-module with the sheafification of
the underlying additive presheaf is exactly the canonical compatibility theorem for the
module-sheafification adjunction. -/
recall PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app

section

variable (𝒪 : X.Presheaf RingCat.{u}) (ℱ : PresheafOfModules.{u} 𝒪)

-- Proof sketch: apply the adjunction
-- `PresheafOfModules.sheafification ⊣ SheafOfModules.forget ⋙ restrictScalars` along
-- `𝒪 ⟶ 𝒪^#`; the resulting hom-set bijection is equivalent to existence and uniqueness of the
-- factorization through the canonical map `ℱ ⟶ ℱ^#`.
/-- For a sheaf of `𝒪^#`-modules `𝒢`, every morphism of presheaves of `𝒪`-modules from `ℱ` to
the restriction of `𝒢` factors uniquely through the canonical map `ℱ ⟶ ℱ^#` by a morphism of
`𝒪^#`-modules. -/
theorem modulePresheafSheafification_factorsUniquely
    (𝒢 : SheafOfModules ((presheafToSheaf J RingCat.{u}).obj 𝒪))
    (η : ℱ ⟶
      (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
        restrictScalars (toSheafify J 𝒪)).obj 𝒢) :
    ∃! γ : (sheafification (toSheafify J 𝒪)).obj ℱ ⟶ 𝒢,
      (sheafificationAdjunction (toSheafify J 𝒪)).unit.app ℱ ≫
          (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
            restrictScalars (toSheafify J 𝒪)).map γ =
        η := by
  let e := (sheafificationAdjunction (toSheafify J 𝒪)).homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · -- The candidate lift is the inverse image of `η` under the adjunction equivalence.
    change e (e.symm η) = η
    exact Equiv.apply_symm_apply e η
  · intro γ hγ
    -- Translate the displayed factorization equation back through the adjunction unit formula.
    apply e.injective
    have hγη : e γ = η := by
      simpa [Adjunction.homEquiv_unit] using hγ
    rw [hγη]
    exact (Equiv.apply_symm_apply e η).symm

end

end
