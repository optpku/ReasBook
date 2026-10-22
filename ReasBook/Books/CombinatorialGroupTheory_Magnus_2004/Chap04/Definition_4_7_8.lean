/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: benign subgroups in the Higman embedding theorem via HNN extensions.

Layer triage:
- `source-facing`: a subgroup `H ≤ G` together with the source condition that the HNN extension
  `G_H`, obtained by adjoining a stable letter centralizing `H`, embeds in a finitely presented
  group.
- `core/canonical`: `HNNExtension G H H (MulEquiv.refl H)` for the ambient HNN extension,
  `Group.IsFinitelyPresented K` for the ambient finite presentability condition, and injective
  homomorphisms from that HNN extension.
- `bridge/view`: the textbook notation `G_H` is the canonical special case of the HNN-extension
  owner where the associated subgroups are both `H` and the gluing isomorphism is `MulEquiv.refl`.

Domain sampling:
1. `HNNExtension G A B φ` is the chapter and mathlib owner abstraction for adjoining a stable
   letter that conjugates `A` onto `B`.
2. `HNNExtension.equiv_eq_conj` and `HNNExtension.equiv_symm_eq_conj` show that in the special
   case `φ = MulEquiv.refl H`, the stable letter centralizes the image of `H`.
3. `Group.IsFinitelyPresented` is mathlib's owner predicate for the finitely presented target.
4. The surrounding chapter states embeddings source-faithfully by quantifying over a homomorphism
   together with `Function.Injective`, rather than by introducing a second wrapper owner.

Primitive vs. derived:
- primitive public data: only the subgroup `H`;
- derived owner object: the source group `G_H`, used directly as the canonical HNN extension
  `HNNExtension G H H (MulEquiv.refl H)`;
- derived public property: existence of a finitely presented overgroup together with an injective
  homomorphism from `HNNExtension G H H (MulEquiv.refl H)`.

The textbook restricts to finitely generated ambient groups `G`, but that hypothesis does not
enter the canonical owner construction or the definition itself, so it is omitted from the public
API.
-/

namespace Subgroup

/-- Definition 4-7-8: a subgroup `H` of `G` is benign in `G` if the HNN extension `G_H`
adjoining one stable letter that centralizes `H` embeds in a finitely presented group. -/
def IsBenign (H : Subgroup G) : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
    (f : HNNExtension G H H (MulEquiv.refl H) →* K),
    Function.Injective f

/-- A benign subgroup admits an embedding of its associated HNN extension `G_H` into a finitely
presented group. -/
theorem IsBenign.exists_finitelyPresented_embedding {H : Subgroup G} (hH : H.IsBenign) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (f : HNNExtension G H H (MulEquiv.refl H) →* K),
      Function.Injective f := by
  simpa [IsBenign] using hH

end Subgroup

end
