module

public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat
open CategoryTheory.Limits

universe u v

/- Domain-style sampling for Lemma 6.9.2:
- primary domain: comparison of the sheaf condition for a `C`-valued presheaf on a topological
  space with the sheaf condition on its underlying set-valued presheaf.
- inspected owner declarations:
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`,
  `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.
- owner abstraction: `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.
- primitive data: a functor `G : C ⥤ Type (max u v)` together with
  `[G.ReflectsIsomorphisms]`, `[HasLimits C]`, `[PreservesLimits G]`, and a presheaf `ℱ`.
- derived API: the topological-space specialization comparing `ℱ` and the underlying set-valued
  presheaf `ℱ ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison between the sheaf condition on a `C`-valued presheaf and
  on its underlying `Type`-valued presheaf.
- `core/canonical`: `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.
- `bridge/view`: the `TopCat.Presheaf` specialization
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`.

The faithfulness hypothesis appearing in the prose is redundant for the canonical comparison
theorem, so it should not remain in the public API. -/

/- Lemma 6.9.2: for a `C`-valued presheaf on a topological space `X`, composing with a
limit-preserving functor `G : C ⥤ Type (max u v)` that reflects isomorphisms preserves and
detects the sheaf condition. This is the source-facing `Type`-valued specialization of the
canonical comparison theorem; the faithfulness hypothesis appearing in the prose is redundant and
is therefore omitted from the public API. The main entry stays `#check`-shaped because the
source-facing specialization uses the size-minimal bridge
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`; switching to
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp` or the more general owner
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` would strengthen the limit assumptions. -/
#check
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' :
    ∀ {C : Type u} [Category.{v} C] (G : C ⥤ Type (max u v)) [G.ReflectsIsomorphisms]
      [HasLimitsOfSize.{v, v} C] [PreservesLimitsOfSize.{v, v} G] {X : TopCat.{v}}
      (F : X.Presheaf C),
      F.IsSheaf ↔ Presheaf.IsSheaf (F ⋙ G))
