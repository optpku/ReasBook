module

public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity on topological spaces:
- earlier chapter owner: `Order.coheight` on `IrreducibleCloseds X`, recalled in
  `Definition_5_11_1`
- mathlib interval bridge: `Order.coheight_bot_eq_krullDim`
- ambient owner for absolute dimension: `topologicalKrullDim`

Layer triage:
- `source-facing`: the relative codimension `codimBetween` and the catenary predicate
  `CatenarySpace`
- `core/canonical`: `coheight` and `krullDim` on the posets `IrreducibleCloseds X` and
  `Set.Icc T T'`
- `bridge/view`: the interval specialization of `Order.coheight_bot_eq_krullDim`

Primitive data belongs to `CatenarySpace`; any derived API should stay atomic. The relative
codimension remains source-facing, but it should be a thin specialization of the chapter owner
`Order.coheight`, not a parallel replacement for it.
-/

/-- The relative codimension of comparable irreducible closed subsets, realized as the thin
interval specialization of `Order.coheight`. -/
noncomputable abbrev codimBetween (T T' : IrreducibleCloseds X) (hTT' : T ≤ T') : ℕ∞ :=
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  coheight (⊥ : Set.Icc T T')

/-- The source-facing relative codimension agrees with the Krull dimension of the interval
`[T, T']`. -/
theorem codimBetween_eq_krullDim {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' = krullDim (Set.Icc T T') := by
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  change coheight (⊥ : Set.Icc T T') = krullDim (Set.Icc T T')
  exact coheight_bot_eq_krullDim

/-- Definition 5.11.4: a topological space is catenary if every comparable pair of irreducible
closed subsets has finite relative codimension; maximal chains in the corresponding interval have
that common length. -/
class CatenarySpace (X : Type u) [TopologicalSpace X] : Prop where
  finite_codimBetween {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' < ⊤
  maximalIrreducibleClosedChainsHaveLength {T T' : IrreducibleCloseds X}
      (hTT' : T ≤ T') (s : Set (Set.Icc T T')) (hs : IsMaxChain (· ≤ ·) s) :
      s.encard = ENat.toNat (codimBetween T T' hTT') + 1

/-- A catenary-space hypothesis can be supplied through `Fact` when a proposition-valued instance
is the natural interface. -/
instance instFactCatenarySpace [CatenarySpace X] : Fact (CatenarySpace X) := ⟨inferInstance⟩

namespace CatenarySpace

/-- Helper for Definition 5.11.4: the lower interval below a point of `[T, T'']` is order-isomorphic
to the interval `[T, a]`. -/
def iic_orderIso_interval {T T'' : IrreducibleCloseds X} [Fact (T ≤ T'')]
    (a : Set.Icc T T'') : Set.Iic a ≃o Set.Icc T a.1 where
  toFun x := by
    refine ⟨(x : IrreducibleCloseds X), ?_, ?_⟩
    · exact x.1.2.1
    · exact x.2
  invFun y := by
    refine ⟨⟨(y : IrreducibleCloseds X), ?_, ?_⟩, ?_⟩
    · exact y.2.1
    · exact y.2.2.trans a.2.2
    · exact y.2.2
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Definition 5.11.4: the upper interval above a point of `[T, T'']` is order-isomorphic
to the interval `[a, T'']`. -/
def ici_orderIso_interval {T T'' : IrreducibleCloseds X} [Fact (T ≤ T'')]
    (a : Set.Icc T T'') : Set.Ici a ≃o Set.Icc a.1 T'' where
  toFun x := by
    refine ⟨(x : IrreducibleCloseds X), ?_, ?_⟩
    · exact x.2
    · exact x.1.2.2
  invFun y := by
    refine ⟨⟨(y : IrreducibleCloseds X), ?_, ?_⟩, ?_⟩
    · exact a.2.1.trans y.2.1
    · exact y.2.2
    · exact y.2.1
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Definition 5.11.4: the part of a maximal chain lying below a chosen element is again
a maximal chain in the lower interval. -/
lemma maxChain_iic_of_mem {α : Type*} [Preorder α] {s : Set α} {a : α}
    (hs : IsMaxChain (· ≤ ·) s) (ha : a ∈ s) :
    IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' s : Set (Set.Iic a)) := by
  constructor
  · -- Restricting a chain to a subtype preserves comparability.
    simpa using hs.isChain.preimage (r := (· ≤ ·)) (s := (· ≤ ·))
      (f := Subtype.val) Subtype.val_injective (fun _ _ h ↦ h)
  · intro t ht hsubset
    -- Extend a larger lower chain by the unchanged upper slice of `s`.
    have h_union_chain : IsChain (· ≤ ·) (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := by
      rw [isChain_union]
      refine ⟨?_, ?_, ?_⟩
      · simpa using ht.image_of_map_rel (r := (· ≤ ·)) (s := (· ≤ ·))
          (f := Subtype.val) (fun _ _ h ↦ h)
      · simpa using hs.isChain.mono (by
          intro x hx
          exact hx.1)
      · intro x hx y hy hxy
        left
        rcases hx with ⟨x', hx', rfl⟩
        exact x'.2.trans hy.2
    have hs_subset : s ⊆ (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := by
      intro x hx
      by_cases hxa : x ≤ a
      · left
        refine ⟨⟨x, hxa⟩, ?_, rfl⟩
        exact hsubset hx
      · right
        refine ⟨hx, ?_⟩
        cases hs.isChain.total hx ha with
        | inl h => exact (hxa h).elim
        | inr h => exact h
    have hs_eq : s = (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := hs.2 h_union_chain hs_subset
    -- Maximality of `s` forces the lower slice to be unchanged.
    apply Set.Subset.antisymm hsubset
    intro x hx
    have : ((x : α) ∈ (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x})) := Or.inl ⟨x, hx, rfl⟩
    exact hs_eq.symm ▸ this

/-- Helper for Definition 5.11.4: the part of a maximal chain lying above a chosen element is again
a maximal chain in the upper interval. -/
lemma maxChain_ici_of_mem {α : Type*} [Preorder α] {s : Set α} {a : α}
    (hs : IsMaxChain (· ≤ ·) s) (ha : a ∈ s) :
    IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' s : Set (Set.Ici a)) := by
  constructor
  · -- Restricting a chain to a subtype preserves comparability.
    simpa using hs.isChain.preimage (r := (· ≤ ·)) (s := (· ≤ ·))
      (f := Subtype.val) Subtype.val_injective (fun _ _ h ↦ h)
  · intro t ht hsubset
    -- Extend a larger upper chain by the unchanged lower slice of `s`.
    have h_union_chain : IsChain (· ≤ ·) ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := by
      rw [isChain_union]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hs.isChain.mono (by
          intro x hx
          exact hx.1)
      · simpa using ht.image_of_map_rel (r := (· ≤ ·)) (s := (· ≤ ·))
          (f := Subtype.val) (fun _ _ h ↦ h)
      · intro x hx y hy hxy
        left
        rcases hy with ⟨y', hy', rfl⟩
        exact hx.2.trans y'.2
    have hs_subset : s ⊆ ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := by
      intro x hx
      by_cases hax : a ≤ x
      · right
        refine ⟨⟨x, hax⟩, ?_, rfl⟩
        exact hsubset hx
      · left
        refine ⟨hx, ?_⟩
        cases hs.isChain.total hx ha with
        | inl h => exact h
        | inr h => exact (hax h).elim
    have hs_eq : s = ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := hs.2 h_union_chain hs_subset
    -- Maximality of `s` forces the upper slice to be unchanged.
    apply Set.Subset.antisymm hsubset
    intro x hx
    have : ((x : α) ∈ ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t)) := Or.inr ⟨x, hx, rfl⟩
    exact hs_eq.symm ▸ this

/-- Helper for Definition 5.11.4: splitting a chain at a chosen point counts the point once. -/
lemma encard_split_at_mem {α : Type*} [PartialOrder α] {s : Set α} {a : α}
    (hs : IsChain (· ≤ ·) s) (ha : a ∈ s) :
    ({x | x ∈ s ∧ x ≤ a}.encard) + ({x | x ∈ s ∧ a ≤ x}.encard) = s.encard + 1 := by
  -- The lower and upper slices cover the chain because every point is comparable with `a`.
  have h_union : {x | x ∈ s ∧ x ≤ a} ∪ {x | x ∈ s ∧ a ≤ x} = s := by
    ext x
    constructor
    · intro hx
      exact hx.elim (fun hx' ↦ hx'.1) (fun hx' ↦ hx'.1)
    · intro hx
      cases hs.total hx ha with
      | inl h => exact Or.inl ⟨hx, h⟩
      | inr h => exact Or.inr ⟨hx, h⟩
  -- Their intersection is the singleton `{a}` by antisymmetry.
  have h_inter : {x | x ∈ s ∧ x ≤ a} ∩ {x | x ∈ s ∧ a ≤ x} = ({a} : Set α) := by
    ext x
    constructor
    · intro hx
      have hxa : x ≤ a := hx.1.2
      have hax : a ≤ x := hx.2.2
      exact Set.mem_singleton_iff.mpr (le_antisymm hxa hax)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨⟨ha, le_rfl⟩, ha, le_rfl⟩
  -- Now the standard inclusion-exclusion formula gives the count.
  calc
    {x | x ∈ s ∧ x ≤ a}.encard + {x | x ∈ s ∧ a ≤ x}.encard
        = ({x | x ∈ s ∧ x ≤ a} ∪ {x | x ∈ s ∧ a ≤ x}).encard
            + ({x | x ∈ s ∧ x ≤ a} ∩ {x | x ∈ s ∧ a ≤ x}).encard := by
            simpa [add_comm] using
              (Set.encard_union_add_encard_inter {x | x ∈ s ∧ x ≤ a} {x | x ∈ s ∧ a ≤ x}).symm
    _ = s.encard + ({a} : Set α).encard := by rw [h_union, h_inter]
    _ = s.encard + 1 := by simp

-- Proof sketch: compare maximal chains in `[T, T'']` with the concatenation of their restrictions
-- to `[T, T']` and `[T', T'']`. In a catenary space those maximal chains have lengths prescribed by
-- `codimBetween`, so the common length in the large interval is the sum of the common lengths in
-- the adjacent intervals.
/-- In a catenary space, relative codimension is additive along chains of irreducible closed
subsets. -/
theorem codimBetween_additive [CatenarySpace X] {T T' T'' : IrreducibleCloseds X}
    (hTT' : T ≤ T') (hT'T'' : T' ≤ T'') :
    codimBetween T T'' (hTT'.trans hT'T'') =
      codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := by
  let hTT'' : T ≤ T'' := hTT'.trans hT'T''
  let _ : Fact (T ≤ T'') := ⟨hTT''⟩
  let a : Set.Icc T T'' := ⟨T', hTT', hT'T''⟩
  obtain ⟨s, ha⟩ := Flag.exists_mem a
  let lower : Set (Set.Iic a) := Subtype.val ⁻¹' (s : Set (Set.Icc T T''))
  let upper : Set (Set.Ici a) := Subtype.val ⁻¹' (s : Set (Set.Icc T T''))
  -- The chosen maximal chain splits into maximal lower and upper subchains.
  have hlower : IsMaxChain (· ≤ ·) lower := by
    simpa [lower] using maxChain_iic_of_mem s.maxChain ha
  have hupper : IsMaxChain (· ≤ ·) upper := by
    simpa [upper] using maxChain_ici_of_mem s.maxChain ha
  have hlower_image :
      Subtype.val '' lower = {x | x ∈ (s : Set (Set.Icc T T'')) ∧ x ≤ a} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨hx', x'.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hupper_image :
      Subtype.val '' upper = {x | x ∈ (s : Set (Set.Icc T T'')) ∧ a ≤ x} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨hx', x'.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  -- Transport the lower slice to `[T, T']` and read off its length from catenarity.
  have hlower_len :
      lower.encard = ENat.toNat (codimBetween T T' hTT') + 1 := by
    have htransport :
        IsMaxChain (· ≤ ·) (iic_orderIso_interval a '' lower) :=
      (IsMaxChain.image (iic_orderIso_interval a) hlower)
    have hlen :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (X := X) (T := T) (T' := T') hTT' (iic_orderIso_interval a '' lower) htransport
    rw [← (iic_orderIso_interval a).injective.encard_image lower]
    simpa [a] using hlen
  -- Transport the upper slice to `[T', T'']` and read off its length from catenarity.
  have hupper_len :
      upper.encard = ENat.toNat (codimBetween T' T'' hT'T'') + 1 := by
    have htransport :
        IsMaxChain (· ≤ ·) (ici_orderIso_interval a '' upper) :=
      (IsMaxChain.image (ici_orderIso_interval a) hupper)
    have hlen :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (X := X) (T := T') (T' := T'') hT'T'' (ici_orderIso_interval a '' upper) htransport
    rw [← (ici_orderIso_interval a).injective.encard_image upper]
    simpa [a] using hlen
  -- The full chain also has the catenary length for `[T, T'']`.
  have hs_len :
      (s : Set (Set.Icc T T'')).encard = ENat.toNat (codimBetween T T'' hTT'') + 1 :=
    CatenarySpace.maximalIrreducibleClosedChainsHaveLength
      (X := X) (T := T) (T' := T'') hTT'' (s : Set (Set.Icc T T'')) s.maxChain
  -- Counting the split chain yields an equality of natural chain lengths.
  have hsplit :
      (ENat.toNat (codimBetween T T' hTT') + 1 : ℕ∞) +
          (ENat.toNat (codimBetween T' T'' hT'T'') + 1) =
        (ENat.toNat (codimBetween T T'' hTT'') + 1) + 1 := by
    have hcard :=
      encard_split_at_mem (α := Set.Icc T T'') s.chain_le ha
    rw [← hlower_image, ← hupper_image] at hcard
    rw [(Subtype.val_injective.encard_image lower), (Subtype.val_injective.encard_image upper)] at hcard
    rw [hlower_len, hupper_len, hs_len] at hcard
    exact hcard
  have hnat :
      ENat.toNat (codimBetween T T'' hTT'') =
        ENat.toNat (codimBetween T T' hTT') + ENat.toNat (codimBetween T' T'' hT'T'') := by
    have hnat' :
        ENat.toNat (codimBetween T T' hTT') + 1 +
            (ENat.toNat (codimBetween T' T'' hT'T'') + 1) =
          (ENat.toNat (codimBetween T T'' hTT'') + 1) + 1 := by
      exact_mod_cast hsplit
    omega
  -- Finiteness upgrades the equality of natural lengths back to an equality in `ℕ∞`.
  have hfinite_big : codimBetween T T'' hTT'' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hTT''
  have hfinite_left : codimBetween T T' hTT' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hTT'
  have hfinite_right : codimBetween T' T'' hT'T'' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hT'T''
  calc
    codimBetween T T'' hTT'' = ENat.toNat (codimBetween T T'' hTT'') := by
      symm
      exact ENat.coe_toNat hfinite_big
    _ = ENat.toNat (codimBetween T T' hTT') + ENat.toNat (codimBetween T' T'' hT'T'') := by
      exact_mod_cast hnat
    _ = codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := by
      rw [ENat.coe_toNat hfinite_left, ENat.coe_toNat hfinite_right]

end CatenarySpace
