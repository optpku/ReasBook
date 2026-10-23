module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Definition 6.11.2:
- primary domain: separated set-valued presheaves and sheafification on a topological space;
- sampled owner API:
  `Presieve.IsSeparated`,
  `Presheaf.IsLocallyInjective`,
  `TopCat.Presheaf.IsSheaf.section_ext`,
  `CategoryTheory.toSheafify`;
- best owner abstraction: the canonical site-theoretic predicate
  `Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ`;
- primitive data: the presheaf `ℱ`;
- derived API: injectivity of the canonical map on sections into the sheafification and the
  specialization to sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks Project criterion via injectivity of the canonical map to the family
  of stalk germs;
- `core/canonical`: `Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ`;
- `bridge/view`: the objectwise injectivity of `ℱ.toSheafify`. -/

/- Definition 6.11.2: the canonical owner notion for a separated set-valued presheaf on `X` is
`Presieve.IsSeparated (Opens.grothendieckTopology X)`. -/
recall Presieve.IsSeparated

/-- Definition 6.11.2: a set-valued presheaf on `X` is separated, in the canonical site-theoretic
sense for `Opens.grothendieckTopology X`, if and only if for every open subset `U` the canonical
map from sections on `U` to the family of germs in the stalks over points of `U`, namely the
underlying function of `(ℱ.toSheafify.app (op U))`, is injective. -/
theorem isSeparated_iff_injective_toStalkFamily (ℱ : X.Presheaf (Type u)) :
    Presieve.IsSeparated J ℱ ↔
      ∀ U : Opens X, Function.Injective (fun s ↦ (ℱ.toSheafify.app (op U) s).1) := by
  constructor
  · intro hℱ U s t hst
    -- Equality of the stalk-family images gives, at each point of `U`, a neighborhood on which the
    -- two sections agree.
    choose V hxV i₁ i₂ hV using fun x : U ↦
      ℱ.germ_eq x.1 x.2 x.2 s t (congrFun hst x)
    -- The pointwise neighborhoods form a covering presieve, so separatedness on the Grothendieck
    -- topology upgrades the local equalities to equality of the original sections.
    have hsep : Presieve.IsSeparatedFor ℱ (.ofArrows V i₁) := by
      rw [Presieve.isSeparatedFor_iff_generate]
      exact hℱ _ (by
        intro x hx
        exact ⟨V ⟨x, hx⟩, i₁ ⟨x, hx⟩, Sieve.ofArrows_mk _ _ _, hxV ⟨x, hx⟩⟩)
    exact hsep.ext fun _ _ hf ↦ by
      rcases hf with ⟨x⟩
      simpa [Subsingleton.elim (i₂ x) (i₁ x)] using hV x
  · intro hℱ U S hS x t₁ t₂ ht₁ ht₂
    -- Sheafification is a sheaf, hence separated on every covering sieve.
    have hsep : Presieve.IsSeparatedFor ℱ.sheafify.presheaf S.arrows :=
      ((isSheaf_iff_isSheaf_of_type J ℱ.sheafify.presheaf).1 ℱ.sheafify.2).isSeparated S hS
    -- Local equality along `S` therefore forces equality after applying the unit to sheafification,
    -- and the assumed injectivity on `U` pulls the conclusion back to `ℱ`.
    have hEq :
        ℱ.toSheafify.app (op U) t₁ = ℱ.toSheafify.app (op U) t₂ :=
      hsep (x.map ℱ.toSheafify) _ _ (ht₁.map ℱ.toSheafify) (ht₂.map ℱ.toSheafify)
    exact hℱ U (congrArg Subtype.val hEq)

end TopCat.Presheaf
