module

public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory TopCat
open TopCat.Sheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable {ℱ : X.Sheaf (Type v)} {𝒢 : Y.Sheaf (Type v)} {ℋ : Z.Sheaf (Type v)}
variable (φ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ)
variable (ψ : ℋ ⟶ (pushforward (Type v) g).obj 𝒢)

/- Domain-style sampling for Definition 6.21.9:
- primary domain: sheaf pushforward along continuous maps and morphisms into pushforwards;
- inspected owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_map`,
  `TopCat.Presheaf.pushforward`,
  `TopCat.Presheaf.Pushforward.comp`;
- owner abstraction: an `f`-map is already the canonical morphism type
  `𝒢 ⟶ (TopCat.Sheaf.pushforward (Type v) f).obj ℱ`, and composition is ordinary categorical
  composition together with `Functor.map`; the identification with a `(g ∘ f)`-map comes from the
  canonical presheaf-level comparison `TopCat.Presheaf.Pushforward.comp`, since sheaf pushforward is
  definitionally the underlying sheaf-category lift of presheaf pushforward;
- primitive data: continuous maps `f : X ⟶ Y`, `g : Y ⟶ Z`, and morphisms
  `φ : 𝒢 ⟶ f_* ℱ`, `ψ : ℋ ⟶ g_* 𝒢`;
- derived API: the induced `(g ∘ f)`-map, obtained by the canonical sheaf-pushforward owner.

Source/core/bridge triage:
- `source-facing`: Definition 6.21.9 names the composite of an `f`-map and a `g`-map;
- `core/canonical`: `TopCat.Sheaf.pushforward` together with ordinary composition in the sheaf
  category;
- `bridge/view`: the textbook phrase “the induced `(g ∘ f)`-map”, which is just the canonical term
  checked below and should not survive as a parallel wrapper definition. -/

/- Definition 6.21.9: after Definition 6.21.7 identifies an `f`-map with a morphism
`𝒢 ⟶ f_* ℱ`, and Lemma 6.21.2 identifies `(g ∘ f)_*` with the iterated pushforward `g_* ∘ f_*`,
the composite `(g ∘ f)`-map is the ordinary categorical composite below. -/
#check (ψ ≫ (pushforward (Type v) g).map φ :
  ℋ ⟶ (pushforward (Type v) (f ≫ g)).obj ℱ)
