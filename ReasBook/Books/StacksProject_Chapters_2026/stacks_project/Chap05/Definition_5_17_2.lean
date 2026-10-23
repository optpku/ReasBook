module

public import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.UniversallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for proper-map notions:
- sampled owner declarations:
  `IsProperMap`,
  `IsProperMap.universally_closed`,
  `isProperMap_iff_universally_closed`,
  `IsSeparatedMap`;
- `source-facing`: `IsQuasiProperMap`, `IsUniversallyClosedMap`, `IsStacksProperMap`;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: the conversion API between `IsUniversallyClosedMap` and `IsProperMap`.

The Stacks notion of universal closedness is the pullback-projection formulation, but the owner API
for closedness under base change lives on `IsProperMap` through closed product maps. The file
should therefore keep the source-facing pullback predicate while deriving its bridge to
`IsProperMap` from mathlib, rather than re-proving a parallel owner theorem. -/

/- Definition 5.17.2 (1): the Stacks phrase "closed map" is the canonical predicate
`IsClosedMap`. -/
recall IsClosedMap

/- Definition 5.17.2 (2): the Stacks phrase "Bourbaki-proper" is the canonical mathlib notion
`IsProperMap`. -/
recall IsProperMap

/- Companion recall: the separatedness condition in Stacks properness is the canonical predicate
`IsSeparatedMap`. -/
recall IsSeparatedMap

/- Companion recall: Bourbaki properness is characterized in mathlib by closedness of the product
maps `Prod.map f id`. -/
recall isProperMap_iff_universally_closed

section

open Function Pullback Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/-- Definition 5.17.2 (1): a map is quasi-proper if inverse images of quasi-compact subsets are
quasi-compact. In mathlib, quasi-compactness of subsets is expressed by `IsCompact`. -/
def IsQuasiProperMap (f : X → Y) : Prop :=
  Continuous f ∧ ∀ V : Set Y, IsCompact V → IsCompact (f ⁻¹' V)

theorem IsQuasiProperMap.continuous (hf : IsQuasiProperMap f) : Continuous f := hf.1

theorem IsQuasiProperMap.isCompactPreimage (hf : IsQuasiProperMap f)
    {V : Set Y} (hV : IsCompact V) : IsCompact (f ⁻¹' V) :=
  hf.2 V hV

theorem isQuasiProperMap_id : IsQuasiProperMap (id : X → X) :=
  ⟨continuous_id, fun _ hV ↦ by simpa using hV⟩

/-- Definition 5.17.2 (2): a map is universally closed if every pullback projection `X ×_Y Z → Z`
along a continuous map `Z → Y` is a closed map. -/
def IsUniversallyClosedMap (f : X → Y) : Prop :=
  Continuous f ∧ ∀ (Z : Type (max u v)) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (@Function.Pullback.snd X Y Z f g)

private noncomputable def pullbackFstHomeomorph {Z : Type u} [TopologicalSpace Z]
    (hf : Continuous f) : X × Z ≃ₜ f.Pullback (Prod.fst : Y × Z → Y) where
  toEquiv :=
    { toFun := fun xz ↦ ⟨(xz.1, (f xz.1, xz.2)), rfl⟩
      invFun := fun p ↦ (p.1.1, p.1.2.2)
      left_inv := by
        intro xz
        rfl
      right_inv := by
        rintro ⟨⟨x, y, z⟩, hxy⟩
        simp [hxy] }
  continuous_toFun := by
    let h : Continuous (fun xz : X × Z ↦ (xz.1, (f xz.1, xz.2)) : X × Z → X × (Y × Z)) :=
      continuous_fst.prodMk ((hf.comp continuous_fst).prodMk continuous_snd)
    exact h.subtype_mk (fun xz ↦ rfl)
  continuous_invFun := by
    let h₁ : Continuous (fun p : f.Pullback (Prod.fst : Y × Z → Y) ↦ p.1.1) :=
      continuous_fst.comp continuous_subtype_val
    let h₂ : Continuous (fun p : f.Pullback (Prod.fst : Y × Z → Y) ↦ p.1.2.2) :=
      continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
    exact h₁.prodMk h₂

private theorem isClosedMap_prodMap_of_isUniversallyClosedMap
    (hf : IsUniversallyClosedMap f) (Z : Type u) [TopologicalSpace Z] :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) := by
  let e : X × Z ≃ₜ f.Pullback (Prod.fst : Y × Z → Y) := pullbackFstHomeomorph hf.1
  have hsnd : IsClosedMap (@snd X Y (Y × Z) f Prod.fst) :=
    hf.2 (Y × Z) Prod.fst continuous_fst
  simpa [e, pullbackFstHomeomorph, Function.comp_def] using hsnd.comp e.isClosedMap

theorem IsProperMap.isUniversallyClosedMap (hf : IsProperMap f) :
    IsUniversallyClosedMap f :=
  ⟨hf.continuous, fun Z _ g hg ↦ by
    intro s hs
    rcases isClosed_induced_iff.mp hs with ⟨t, ht, rfl⟩
    let k : Z → Y × Z := fun z ↦ (g z, z)
    have hk : Continuous k := hg.prodMk continuous_id
    have hclosed : IsClosed ((Prod.map f (id : Z → Z)) '' t) :=
      (hf.universally_closed Z) t ht
    have hsnd : snd '' (Subtype.val ⁻¹' t : Set (f.Pullback g)) =
        k ⁻¹' ((Prod.map f (id : Z → Z)) '' t) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(p.fst, p.snd), hp, Prod.ext p.2 rfl⟩
      · rintro ⟨xz, hxt, hxz⟩
        have hx₁ : f xz.1 = g z := congrArg Prod.fst hxz
        have hx₂ : xz.2 = z := congrArg Prod.snd hxz
        let p : f.Pullback g := ⟨xz, by simpa [hx₂] using hx₁⟩
        refine ⟨p, hxt, ?_⟩
        simpa [p] using hx₂
    rw [hsnd]
    exact hclosed.preimage hk⟩

theorem IsUniversallyClosedMap.continuous (hf : IsUniversallyClosedMap f) :
  Continuous f :=
  hf.1

theorem IsUniversallyClosedMap.isClosedMap_snd (hf : IsUniversallyClosedMap f)
    {Z : Type (max u v)} [TopologicalSpace Z] (g : Z → Y) (hg : Continuous g) :
    IsClosedMap (@snd X Y Z f g) :=
  hf.2 Z g hg

theorem IsUniversallyClosedMap.isClosedMap_prodMap (hf : IsUniversallyClosedMap f)
    (Z : Type u) [TopologicalSpace Z] :
    IsClosedMap (Prod.map f (id : Z → Z) : X × Z → Y × Z) :=
  isClosedMap_prodMap_of_isUniversallyClosedMap hf Z

theorem IsUniversallyClosedMap.isProperMap (hf : IsUniversallyClosedMap f) :
    IsProperMap f := by
  rw [isProperMap_iff_universally_closed]
  exact ⟨hf.continuous, fun Z ↦ hf.isClosedMap_prodMap Z⟩

theorem isProperMap_iff_isUniversallyClosedMap :
    IsProperMap f ↔ IsUniversallyClosedMap f :=
  ⟨IsProperMap.isUniversallyClosedMap, IsUniversallyClosedMap.isProperMap⟩

theorem isUniversallyClosedMap_id : IsUniversallyClosedMap (id : X → X) :=
  isProperMap_id.isUniversallyClosedMap

/-- Definition 5.17.2 (3): a map is proper in the Stacks sense if it is separated and universally
closed. -/
def IsStacksProperMap (f : X → Y) : Prop :=
  IsSeparatedMap f ∧ IsUniversallyClosedMap f

theorem IsStacksProperMap.separated (hf : IsStacksProperMap f) : IsSeparatedMap f :=
  hf.1

theorem IsStacksProperMap.proper (hf : IsStacksProperMap f) : IsProperMap f :=
  hf.2.isProperMap

theorem IsStacksProperMap.universallyClosed (hf : IsStacksProperMap f) :
    IsUniversallyClosedMap f :=
  hf.2

theorem isStacksProperMap_id : IsStacksProperMap (id : X → X) :=
  ⟨Function.Injective.isSeparatedMap fun _ _ h ↦ h, isUniversallyClosedMap_id⟩

end
