module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.OpenQuotient

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace Topology

open Function Set
open IsInducing

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for submersive maps:
- primary domain: quotient maps and range factorizations in general topology
- owner abstraction: `Topology.IsQuotientMap`
- same-domain declarations inspected:
  `Topology.IsQuotientMap`,
  `Topology.isQuotientMap_iff`,
  `Topology.IsQuotientMap.comp`,
  `Topology.IsInducing.isQuotientMap_of_surjective`,
  `Set.rangeFactorization`,
  `Set.rangeFactorization_surjective`

Layer triage:
- `source-facing`: the Stacks notion `IsStrictMap`
- `core/canonical`: `Topology.IsQuotientMap`
- `bridge/view`: the quotient-map condition on `Set.rangeFactorization` and the source-facing
  characterization theorem `isSubmersiveMap_iff`

Primitive data belongs to the source-facing predicate `IsStrictMap`: the strictness clause is the
quotient-map condition on the range factorization. The canonical owner `IsQuotientMap` remains the
core topology predicate, and `isSubmersiveMap_iff` is the thin source-facing bridge expressing the
Stacks term “submersive” through surjectivity plus strictness.
-/

/- Definition 5.6.3 uses the canonical quotient-map owner `Topology.IsQuotientMap` for the
range-factorization clause of strict maps. -/
recall IsQuotientMap

/-- Definition 5.6.3: a map is strict if the induced map onto its image is a quotient map. -/
def IsStrictMap (f : X → Y) : Prop :=
  IsQuotientMap (rangeFactorization f)

/-- Definition 5.6.3, source-facing form: a map is submersive if and only if it is
surjective and strict, equivalently a quotient map. -/
theorem isSubmersiveMap_iff {f : X → Y} :
    IsQuotientMap f ↔ Surjective f ∧ IsStrictMap f := by
  constructor
  · intro hf
    refine ⟨hf.surjective, ?_⟩
    rw [IsStrictMap, isQuotientMap_iff]
    refine ⟨?_, rangeFactorization_surjective⟩
    refine IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨?_, ?_⟩
    · intro hs
      have hopen : IsOpen (Subtype.val '' s : Set Y) := by
        apply hf.isOpen_preimage.mp
        have hpre : f ⁻¹' (Subtype.val '' s : Set Y) = rangeFactorization f ⁻¹' s := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨y, hy, hxy⟩
            have hxy' : rangeFactorization f x = y := Subtype.ext hxy.symm
            simpa [hxy'] using hy
          · intro hx
            exact ⟨rangeFactorization f x, hx, rfl⟩
        rw [hpre]
        exact hs
      exact subtypeVal.isOpen_iff.mpr ⟨Subtype.val '' s, hopen, by
        ext y
        simp⟩
    · intro hs
      exact hs.preimage <| hf.continuous.rangeFactorization
  · rintro ⟨hsurj, hstrict⟩
    have hval : IsQuotientMap ((↑) : range f → Y) := by
      refine subtypeVal.isQuotientMap_of_surjective fun y ↦ ?_
      rcases hsurj y with ⟨x, rfl⟩
      exact ⟨rangeFactorization f x, rfl⟩
    simpa [IsStrictMap, Function.comp_def] using hval.comp hstrict

end Topology
