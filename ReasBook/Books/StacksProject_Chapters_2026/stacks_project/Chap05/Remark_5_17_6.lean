module

public import stacks_project.Chap05.Theorem_5_17_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for proper-map characterizations:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_isUniversallyClosedMap`,
  `proper_map_characterization_tfae`;
- `source-facing`: the three-clause equivalence from Remark 5.17.6;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: `IsUniversallyClosedMap`.

Primitive data belongs to the owner layer: continuity, closedness, and compact fibers. The target
remark only extracts the clauses `(1)`, `(2)`, and `(4)` from the chapter's four-way
characterization, so the file should keep only that source-facing projection and reuse the chapter
owner theorem directly rather than rebuilding any of its component equivalences locally. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- A map is quasi-proper, moreover closed. -/
def IsClosedQuasiProperMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

-- Proof sketch: specialize Theorem `5.17.5` to clauses `(1)`, `(2)`, `(4)`, then rewrite the
-- first plus third clauses using the two semantic helper predicates above.
/-- Remark 5.17.6: for a continuous map, the quasi-proper closed condition, Bourbaki properness,
together with the closed compact-fiber condition from Theorem 5.17.5, are equivalent. -/
theorem proper_map_characterization_124_tfae (hf : Continuous f) :
    List.TFAE
      [ IsClosedQuasiProperMap f,
        IsProperMap f,
        IsClosedMapWithCompactFibers f ] := by
  -- Use `IsProperMap f` as the owner clause and import the two pairwise bridges from
  -- Theorem 5.17.5 instead of rebuilding the characterization locally.
  tfae_have 1 ↔ 2 := by
    -- The local clause `(1)` is definitionally the same as the source-facing clause `(1)`
    -- from Theorem 5.17.5.
    simpa [IsClosedQuasiProperMap, IsQuasiProperClosedMap] using
      (isQuasiProperClosedMap_iff_isProperMap (f := f) hf)
  tfae_have 2 ↔ 3 := by
    -- The local clause `(3)` is exactly the compact-fiber clause already related to
    -- properness in Theorem 5.17.5.
    simpa using (isClosedMapWithCompactFibers_iff_isProperMap (f := f) hf).symm
  tfae_finish

end
