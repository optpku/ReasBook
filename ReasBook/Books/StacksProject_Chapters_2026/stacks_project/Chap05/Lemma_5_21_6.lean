module

public import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Maps.OpenQuotient

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u v

/-
Domain-style sampling for nowhere dense subsets under open and open quotient maps:
- primary domain: general topology of nowhere dense subsets and quotient/open maps
- sampled owner-level declarations:
  `isClosed_isNowhereDense_iff_compl`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`,
  `IsOpenMap.preimage_interior_eq_interior_preimage`,
  `IsOpenQuotientMap.dense_preimage_iff`
- best owner abstractions: `IsOpenMap` for backward preservation of nowhere denseness, and
  `IsOpenQuotientMap` for the quotient-level equivalence
- primitive data: a map with the owner hypothesis and a subset `T`
- derived API: the bundled `IsClosed ∧ IsNowhereDense` forms, since closedness comes from
  `Continuous.preimage` and nowhere denseness is transported either by the owner-level
  closure/interior formulas or, for quotient maps, by dense complements

Layer triage:
- `core/canonical`: the owner-namespace theorems below on `IsOpenMap` and `IsOpenQuotientMap`
- `bridge/view`: the final surjective-open-continuous restatement, which packages the owner
  hypothesis in the source wording from earlier chapter items
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace IsOpenMap

variable {T : Set Y}

/-- Canonical owner-level form: for a continuous open map, the preimage of a nowhere dense subset
is nowhere dense. -/
theorem isNowhereDense_preimage
    (hf : IsOpenMap f) (hcont : Continuous f) (hT : IsNowhereDense T) :
    IsNowhereDense (f ⁻¹' T) := by
  rw [IsNowhereDense]
  calc
    interior (closure (f ⁻¹' T))
        = interior (f ⁻¹' closure T) := by
            rw [hf.preimage_closure_eq_closure_preimage hcont]
    _ = f ⁻¹' interior (closure T) := by
          rw [hf.preimage_interior_eq_interior_preimage hcont]
    _ = ∅ := by simpa [IsNowhereDense] using congrArg (preimage f) hT

/-- Owner-level closedness transport for preimages of continuous maps. -/
theorem isClosed_preimage (hcont : Continuous f) (hT : IsClosed T) :
    IsClosed (f ⁻¹' T) :=
  hT.preimage hcont

end IsOpenMap

namespace IsOpenQuotientMap

variable {T : Set Y}

/-- Canonical owner-level form: for an open quotient map, a subset of the target is nowhere dense
if and only if its preimage is nowhere dense. -/
theorem isNowhereDense_iff_preimage
    (hf : IsOpenQuotientMap f) :
    IsNowhereDense T ↔ IsNowhereDense (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hf.isOpenMap.isNowhereDense_preimage hf.continuous hT
  · intro hT
    have hpreimage_closure :
        f ⁻¹' closure T = closure (f ⁻¹' T) :=
      hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous T
    have hDensePreimage : Dense (f ⁻¹' (closure T)ᶜ) := by
      simpa [preimage_compl, hpreimage_closure]
        using
          (isClosed_isNowhereDense_iff_compl.mp
            ⟨isClosed_closure, hT.closure⟩).2
    have hDense : Dense (closure T)ᶜ :=
      (hf.dense_preimage_iff).1 hDensePreimage
    exact
      ((isClosed_isNowhereDense_iff_compl.mpr ⟨isClosed_closure.isOpen_compl, hDense⟩).2).mono
        subset_closure

/-- Owner-level closedness equivalence for open quotient maps. -/
theorem isClosed_iff_preimage (hf : IsOpenQuotientMap f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := by
  let hq : IsQuotientMap f := hf.isQuotientMap
  rw [hq.isClosed_preimage.symm]

end IsOpenQuotientMap

/-- Lemma 5.21.6 (1): for a surjective continuous open map, a subset is closed if and only if its
preimage is closed. -/
theorem isClosed_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsClosed T ↔ IsClosed (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isClosed_iff_preimage

/-- Lemma 5.21.6 (2): for a surjective continuous open map, a subset is nowhere dense if and only
if its preimage is nowhere dense. -/
theorem isNowhereDense_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsNowhereDense T ↔ IsNowhereDense (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isNowhereDense_iff_preimage

end
