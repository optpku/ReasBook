module

public import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-
Domain-style sampling for 7.12.3.1:
- primary domain: subcanonical Grothendieck topologies and the sheaf-valued Yoneda embedding;
- sampled owner API:
  `GrothendieckTopology.yoneda`,
  `GrothendieckTopology.yonedaEquiv`,
  `GrothendieckTopology.yonedaEquiv_apply`,
  `GrothendieckTopology.uliftYonedaEquiv`;
- source/core/bridge triage:
  `source-facing`: the representable sheaf `J.yoneda.obj U` from Definition 7.12.3;
  `core/canonical`: the Hom-to-sections equivalence `J.yonedaEquiv`;
  `bridge/view`: the universe-raised variant `J.uliftYonedaEquiv`.

Primitive data are the subcanonical topology `J`, the object `U`, and the representable sheaf
`J.yoneda.obj U`. The equivalence between morphisms `J.yoneda.obj U ⟶ F` and sections
`F.obj.obj (op U)` is derived API from the owner declaration `J.yonedaEquiv`, with
`yonedaEquiv_apply` giving the pointwise evaluation formula. This file should therefore recall
that owner directly rather than introduce a parallel local wrapper theorem.
-/
/- 7.12.3.1: on a subcanonical site, morphisms from the representable sheaf attached to `U`
to a sheaf of sets `F` are canonically identified with sections of `F` over `U`. For the
source-facing owner `J.yoneda.obj U`, this is exactly `J.yonedaEquiv`; the
universe-raised statement `GrothendieckTopology.uliftYonedaEquiv` is only a later bridge/view
variant. -/
recall yonedaEquiv

end CategoryTheory.GrothendieckTopology
