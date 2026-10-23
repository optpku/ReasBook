module

public import stacks_project.Chap05.Definition_5_17_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for characterizations of proper maps:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_universally_closed`,
  and the chapter bridge `isProperMap_iff_isUniversallyClosedMap`;
- source-facing: `IsQuasiProperMap`;
- core/canonical: `IsProperMap`;
- bridge/view: `IsUniversallyClosedMap`. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- The source-facing condition that a map is both quasi-proper and closed. -/
def IsQuasiProperClosedMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

/-- The source-facing condition that a map is closed and has compact fibers. -/
def IsClosedMapWithCompactFibers (f : X → Y) : Prop :=
  IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y})

/-- Helper for Theorem 5.17.5: a proper map is quasi-proper because proper maps send compact
subsets of the target to compact inverse images. -/
theorem IsProperMap.isQuasiProperMap (hproper : IsProperMap f) : IsQuasiProperMap f := by
  -- Proper maps are continuous and preserve compactness under inverse image.
  refine ⟨hproper.continuous, ?_⟩
  intro V hV
  exact hproper.isCompact_preimage hV

/-- Bourbaki properness is equivalent to being both quasi-proper and closed. -/
-- Proof sketch: use `isProperMap_iff_isClosedMap_and_compact_fibers`; compact fibers come from
-- quasi-properness on singletons, and quasi-properness follows from properness by compact
-- preimages.
theorem isQuasiProperClosedMap_iff_isProperMap (hf : Continuous f) :
    IsQuasiProperClosedMap f ↔ IsProperMap f := by
  constructor
  · intro hsource
    rcases hsource with ⟨hquasi, hclosed⟩
    -- Route correction: identify the source-facing condition with the owner theorem
    -- `isProperMap_iff_isClosedMap_and_compact_fibers` instead of replaying the base-change proof.
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hf, hclosed, ?_⟩
    -- Quasi-properness supplies compactness of each singleton fiber.
    intro y
    simpa using hquasi.isCompactPreimage isCompact_singleton
  · intro hproper
    -- The reverse implication is the structural bridge from properness to quasi-properness,
    -- together with the standard closedness of proper maps.
    exact ⟨hproper.isQuasiProperMap, hproper.isClosedMap⟩

/-- Helper for Theorem 5.17.5: the source condition "closed with compact fibers" is exactly the
owner-level properness criterion. -/
theorem isClosedMapWithCompactFibers_iff_isProperMap (hf : Continuous f) :
    IsClosedMapWithCompactFibers f ↔ IsProperMap f := by
  constructor
  · intro hsource
    rcases hsource with ⟨hclosed, hcompact⟩
    -- This is exactly the backward direction of the standard proper-map characterization.
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    exact ⟨hf, hclosed, hcompact⟩
  · intro hproper
    -- Properness gives both closedness and compact singleton fibers.
    exact ⟨hproper.isClosedMap, fun y ↦ hproper.isCompact_preimage isCompact_singleton⟩

/-- Theorem 5.17.5: for a continuous map of topological spaces, the Stacks conditions
"quasi-proper and closed", "Bourbaki-proper", "universally closed", and "closed with
quasi-compact fibers" are equivalent. Here Bourbaki-proper is expressed by mathlib's
`IsProperMap`, Stacks universal closedness by the chapter's bridge predicate
`IsUniversallyClosedMap`, and quasi-compactness by `IsCompact`. -/
-- Proof sketch: combine the equivalence between quasi-proper closed maps and `IsProperMap`,
-- the chapter bridge `isProperMap_iff_isUniversallyClosedMap`, and the standard compact-fiber
-- characterization of proper maps.
theorem proper_map_characterization_tfae (hf : Continuous f) :
    List.TFAE
      [ IsQuasiProperClosedMap f,
        IsProperMap f,
        IsUniversallyClosedMap f,
        IsClosedMapWithCompactFibers f ] := by
  -- Package the four source clauses by using `IsProperMap f` as the central owner notion.
  tfae_have 1 ↔ 2 := isQuasiProperClosedMap_iff_isProperMap hf
  tfae_have 2 ↔ 3 := isProperMap_iff_isUniversallyClosedMap
  tfae_have 2 ↔ 4 := (isClosedMapWithCompactFibers_iff_isProperMap hf).symm
  tfae_finish

end
