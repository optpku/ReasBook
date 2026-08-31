module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.OpenQuotient

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u v

/-
Domain-style sampling for Lemma 5.6.4:
- primary domain: quotient maps and locally closed subsets in general topology
- owner declarations inspected: `IsOpenMap.isQuotientMap`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`, `IsOpenQuotientMap`,
  `Topology.IsQuotientMap`, `coborder_preimage`
- best owner abstraction: `IsOpenQuotientMap f`
- primitive data: continuity and openness for the closure formula, and surjectivity in the
  source wording
- derived API: the quotient-map consequence, the closure formula, and the locally-closed
  preimage criterion

Layer triage:
- source-facing: `IsOpenMap.isQuotientMap`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`
- core/canonical: `IsOpenQuotientMap`
- bridge/view: the source wording “submersive” identified in Definition `5.6.3` with the
  quotient-map owner
-/

/- `IsOpenQuotientMap f` is mathlib's owner notion for a surjective continuous open map; the
owner-level theorem below uses this abstraction to package the locally closed preimage criterion.
-/
recall IsOpenQuotientMap

/- Lemma 5.6.4: the source statement "a surjective continuous open map is a quotient map" is
exactly mathlib's theorem `IsOpenMap.isQuotientMap`. -/
recall IsOpenMap.isQuotientMap

/- Lemma 5.6.4 also includes the closure identity
`f ⁻¹' closure T = closure (f ⁻¹' T)`, which is exactly mathlib's theorem
`IsOpenMap.preimage_closure_eq_closure_preimage`; the source surjectivity hypothesis is redundant
for this clause. -/
recall IsOpenMap.preimage_closure_eq_closure_preimage

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

namespace IsOpenQuotientMap

-- Proof sketch: rewrite local closedness as openness of the coborder, use the coborder preimage
-- identity for continuous open maps, and then apply the quotient-map openness criterion.
/-- Under an open quotient map, a subset is locally closed exactly when its preimage is locally
closed. -/
theorem isLocallyClosed_iff_preimage (hf : IsOpenQuotientMap f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  rw [isLocallyClosed_iff_isOpen_coborder, isLocallyClosed_iff_isOpen_coborder,
    coborder_preimage hf.isOpenMap hf.continuous]
  have hq : IsQuotientMap f := hf.isQuotientMap
  exact hq.isOpen_preimage.symm

end IsOpenQuotientMap

/-- Lemma 5.6.4, source-facing form: for a surjective continuous open map, a subset of the
codomain is locally closed if and only if its preimage is locally closed. -/
theorem isLocallyClosed_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isLocallyClosed_iff_preimage

end
