module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.LocallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Function Set Topology

universe u v

/- Domain-style sampling for Lemma 5.6.5:
- primary domain: quotient maps and locally closed subsets in general topology
- owner declarations inspected: `IsClosedMap.isQuotientMap`,
  `IsClosedMap.closure_image_eq_of_continuous`, `IsQuotientMap.isOpen_preimage`
- best owner abstraction: `IsQuotientMap f` for topology reflection, obtained canonically from
  `IsClosedMap.isQuotientMap`
- primitive data: `IsClosedMap f`, `Continuous f`, and `Surjective f`
- derived API: the closure formula, the locally-closed reflection statement, and the quotient-map
  corollary

Layer triage:
- source-facing: the closure formula for a surjective closed continuous map
- core/canonical: `IsClosedMap.isQuotientMap` and its `IsQuotientMap` consequences
- bridge/view: the source wording “submersive” identified in Definition `5.6.3` with the
  quotient-map owner
-/

/- Lemma 5.6.5: in particular, a surjective closed continuous map is a quotient map.
Definition 5.6.3 identifies this quotient-map owner with the Stacks notion of a submersive map. -/
recall IsClosedMap.isQuotientMap

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace IsClosedMap

/-- For a surjective closed continuous map, the closure of a subset of the codomain is the image
of the closure of its preimage. -/
-- Proof sketch: apply `IsClosedMap.closure_image_eq_of_continuous` to `f ⁻¹' T`, then use
-- surjectivity to identify `f '' (f ⁻¹' T)` with `T`.
theorem closure_eq_image_closure_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f)
    (T : Set Y) :
    closure T = f '' closure (f ⁻¹' T) := by
  simpa [hsurj.image_preimage] using
    hclosed.closure_image_eq_of_continuous hcont (f ⁻¹' T)

/-- A surjective closed continuous map reflects closed subsets along preimage. -/
theorem isClosed_iff_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) {T : Set Y} :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := by
  exact (hclosed.isQuotientMap hcont hsurj).isClosed_preimage.symm

/-- A surjective closed continuous map reflects open subsets along preimage. -/
theorem isOpen_iff_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) {T : Set Y} :
    IsOpen T ↔ IsOpen (f ⁻¹' T) := by
  exact (hclosed.isQuotientMap hcont hsurj).isOpen_preimage.symm

/-- A surjective closed continuous map reflects locally closed subsets along preimage. -/
-- Proof sketch: if `T` is locally closed then continuity gives local closedness of the preimage;
-- conversely, use the closure identity to identify `closure T` with the image of
-- `closure (f ⁻¹' T)`, restrict `f` to these closures, and apply the open-set criterion above.
theorem isLocallyClosed_iff_preimage (hclosed : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) {T : Set Y} :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hT.preimage hcont
  · intro hpre
    have hmaps : MapsTo f (closure (f ⁻¹' T)) (closure T) :=
      (mapsTo_preimage f T).closure hcont
    let g : closure (f ⁻¹' T) → closure T := hmaps.restrict f (closure (f ⁻¹' T)) (closure T)
    have hgcont : Continuous g :=
      Continuous.restrict hmaps hcont
    have hgclosed : IsClosedMap g :=
      (hclosed.restrict isClosed_closure).codRestrict fun x ↦ hmaps x.2
    have hgsurj : Surjective g := by
      intro y
      have hy' : y.1 ∈ f '' closure (f ⁻¹' T) := by
        simpa [hclosed.closure_eq_image_closure_preimage hcont hsurj T] using y.2
      rcases hy' with ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hopen_preimage : IsOpen (((↑) : closure (f ⁻¹' T) → X) ⁻¹' (f ⁻¹' T)) :=
      hpre.isOpen_preimage_val_closure
    have hquot : IsQuotientMap g := hgclosed.isQuotientMap hgcont hgsurj
    have hopen : IsOpen (((↑) : closure T → Y) ⁻¹' T) := by
      exact hquot.isOpen_preimage.mp <| by
        simpa [g] using hopen_preimage
    exact ((isLocallyClosed_tfae T).out 4 0).mp hopen

end IsClosedMap

/-- A surjective closed continuous map is a quotient map, hence submersive in the source
terminology of Definition 5.6.3. -/
theorem isQuotientMap_of_surjective_closed_continuous
    (hclosed : IsClosedMap f) (hcont : Continuous f) (hsurj : Surjective f) :
    IsQuotientMap f :=
  hclosed.isQuotientMap hcont hsurj

end
