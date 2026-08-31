module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Lemma 5.19.7:
- primary domain: specialization/generalization lifting for maps of topological spaces
- inspected owner declarations:
  `SpecializingMap`,
  `GeneralizingMap`,
  `IsClosedMap.specializingMap`,
  `TopologicalSpace.IsOpenCover.generalizingMap_iff_comp`
- best owner abstraction: the map-lifting owner predicates `SpecializingMap f` and
  `GeneralizingMap f`
- primitive data: a map `f : X → Y` with the geometric hypotheses needed to force one of those
  owner predicates
- derived API: clause `(1)` is already the canonical owner theorem
  `IsClosedMap.specializingMap`, while clause `(2)` is a source-facing sufficient criterion for
  `GeneralizingMap f`

Layer triage:
- `source-facing`: the Stacks criterion that an open continuous map from a Noetherian quasi-sober
  source to a `T₀` target is generalizing
- `core/canonical`: `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

Primitive data here is only the map together with open-map and continuity hypotheses; the conclusion
is the canonical owner predicate `GeneralizingMap f`. The file should therefore recall clause `(1)`
directly from mathlib and state clause `(2)` as a theorem returning that owner predicate, without a
parallel local wrapper notion.
-/

-- Proof sketch: closed subsets are stable under specialization, and the image of a closed subset
-- under a closed map is closed again; applied to closures of singletons, this is exactly the
-- specializing-map lifting condition.
/- Lemma 5.19.7 (1) is recalled canonically by `IsClosedMap.specializingMap`: a closed map is
specializing, and the canonical mathlib theorem is stronger than the Stacks phrasing because it
does not require continuity separately. -/
recall IsClosedMap.specializingMap

-- Proof sketch: for a point `x` over the specialization target, every open neighbourhood of `x`
-- meets the fibre over the specialization source because `f` is open; in a Noetherian space one
-- passes to an irreducible component of that fibre, chooses its generic point using quasi-sobriety,
-- and the `T₀` condition forces that generic point to map to the prescribed source point.
namespace IsOpenMap

/-- An open continuous map from a Noetherian quasi-sober space to a Kolmogorov space is
generalizing. -/
theorem generalizingMap_of_noetherianSpace_quasiSober_t0 [NoetherianSpace X] [QuasiSober X]
    [T0Space Y] {f : X → Y} (hopen : IsOpenMap f) (hf : Continuous f) : GeneralizingMap f := by
  intro x y hy
  have hx_closure : x ∈ closure (f ⁻¹' ({y} : Set Y)) := by
    rw [← hopen.preimage_closure_eq_closure_preimage hf ({y} : Set Y)]
    simpa [mem_preimage, specializes_iff_mem_closure] using hy
  let C : Set X := closure (f ⁻¹' ({y} : Set Y))
  have hC_closed : IsClosed C := by
    simp [C]
  have hC_closedEmb := hC_closed.isClosedEmbedding_subtypeVal
  let xC : C := ⟨x, by simpa [C] using hx_closure⟩
  haveI : QuasiSober C := hC_closedEmb.quasiSober
  let A : Set C := {z | f z = y}
  have hA_image : Subtype.val '' A = f ⁻¹' ({y} : Set Y) := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      simpa [A] using hz'
    · intro hz
      refine ⟨⟨z, by simpa [C] using subset_closure hz⟩, ?_, rfl⟩
      simpa [A] using hz
  have hA_closure : closure A = univ := by
    rw [hC_closedEmb.isEmbedding.closure_eq_preimage_closure_image, hA_image]
    ext z
    simp [C]
  have hA_dense : Dense A := dense_iff_closure_eq.mpr hA_closure
  let Z : Set C := irreducibleComponent xC
  have hZ_mem : Z ∈ irreducibleComponents C := irreducibleComponent_mem_irreducibleComponents xC
  obtain ⟨o, ho, hone, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ_mem
  obtain ⟨zC, hzo, hzA⟩ := hA_dense.inter_open_nonempty o ho hone
  have hzZ : zC ∈ Z := hoZ hzo
  have hZ_irr : IsIrreducible Z := isIrreducible_irreducibleComponent
  have hZ_closed : IsClosed Z := isClosed_irreducibleComponent
  let ξC : C := hZ_irr.genericPoint
  have hξC : IsGenericPoint ξC Z := hZ_irr.isGenericPoint_genericPoint hZ_closed
  have hξx : (ξC : X) ⤳ x :=
    (subtype_specializes_iff ξC xC).mp (hξC.specializes mem_irreducibleComponent)
  have hξz : (ξC : X) ⤳ (zC : X) :=
    (subtype_specializes_iff ξC zC).mp (hξC.specializes hzZ)
  have hzfy : f zC = y := hzA
  have hfξy : f ξC ⤳ y := by
    simpa [hzfy] using hξz.map hf
  have hyfξ : y ⤳ f ξC := by
    rw [specializes_iff_mem_closure]
    change (ξC : X) ∈ f ⁻¹' closure ({y} : Set Y)
    rw [hopen.preimage_closure_eq_closure_preimage hf ({y} : Set Y)]
    simp [C]
  refine ⟨ξC, hξx, ?_⟩
  exact (hyfξ.antisymm hfξy).eq.symm

end IsOpenMap
