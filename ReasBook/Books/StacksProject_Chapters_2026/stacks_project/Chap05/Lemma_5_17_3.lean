module

public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Maps.Proper.UniversallyClosed
import Mathlib.Topology.Metrizable.Uniformity

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Homeomorph

/- Domain-style sampling for compactness via closed product projections:
- sampled owner declarations in this domain:
  `CompactSpace`,
  `isClosedMap_fst_of_compactSpace`,
  `IsProperMap.universally_closed`,
  `isProperMap_const_iff`
- owner abstraction: `CompactSpace`, with `IsProperMap` as the canonical bridge from compactness to
  closedness of product projections

Layer triage:
- `source-facing`: `compactSpace_iff_forall_isClosedMap_fst`
- `core/canonical`: compactness and properness
- `bridge/view`: closedness of `Prod.fst`

Primitive data is just compactness of `X`. Closedness of the projections and properness of the
constant map are derived API, so this file should keep the source-facing criterion and reuse the
canonical owner theorems instead of introducing any parallel wrapper notion.
-/

/-- Lemma 5.17.3: a topological space `X` is quasi-compact if and only if for every
topological space `Z`, the projection `Z × X → Z` is a closed map. -/
theorem compactSpace_iff_forall_isClosedMap_fst
    (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔ ∀ (Z : Type (max u v)) [TopologicalSpace Z],
      IsClosedMap (Prod.fst : Z × X → Z) := by
  constructor
  · intro hX Z _
    letI := hX
    simpa using
      (isClosedMap_fst_of_compactSpace : IsClosedMap (Prod.fst : Z × X → Z))
  · intro h
    have hsame : ∀ (Z : Type u) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z) := by
      intro Z _
      let e : Z × X ≃ₜ ULift.{v, u} Z × X :=
        ulift.symm.prodCongr (Homeomorph.refl X)
      have hpre :
          IsClosedMap ((Prod.fst : ULift.{v, u} Z × X → ULift.{v, u} Z) ∘ e) :=
        (h (ULift.{v, u} Z)).comp e.isClosedMap
      simpa [e, Function.comp] using ulift.isClosedMap.comp hpre
    have hproper : IsProperMap (fun _ : X ↦ (PUnit.unit : PUnit.{u + 1})) := by
      refine (isProperMap_iff_universally_closed).2 ?_
      refine ⟨continuous_const, fun Z _ ↦ by
        have hsnd : IsClosedMap (Prod.snd : X × Z → Z) := by
          simpa [Function.comp] using
            (hsame Z).comp (prodComm X Z).isClosedMap
        simpa [Function.comp] using
          (punitProd Z).symm.isClosedMap.comp hsnd⟩
    simpa using (isProperMap_const_iff (PUnit.unit : PUnit.{u + 1})).mp hproper
