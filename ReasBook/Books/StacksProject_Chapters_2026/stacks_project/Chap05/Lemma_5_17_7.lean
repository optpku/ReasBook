module

public import stacks_project.Chap05.Definition_5_17_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for proper maps:
- sampled owner declarations:
  `IsProperMap`,
  `Continuous.isProperMap`,
  `IsProperMap.isUniversallyClosedMap`;
- `source-facing`: the conclusion `IsUniversallyClosedMap`;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: `IsProperMap.isUniversallyClosedMap`.

Primitive data is only the continuous map `f` together with compactness of the source and
Hausdorffness of the target, which feed the canonical owner theorem `Continuous.isProperMap`.
Universal closedness here is derived bridge API, so this file should reuse that owner theorem
directly rather than importing the broader chapter characterization theorem.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

-- Proof sketch: `Continuous.isProperMap` gives the canonical owner theorem, and
-- `IsProperMap.isUniversallyClosedMap` is the chapter bridge to universal closedness.
/-- Lemma 5.17.7: a continuous map from a quasi-compact space to a Hausdorff space is universally
closed. In this chapter this is expressed by the bridge predicate `IsUniversallyClosedMap`. -/
theorem Continuous.isUniversallyClosed [CompactSpace X] [T2Space Y] (hf : Continuous f) :
    IsUniversallyClosedMap f := by
  -- First package the compact-source and Hausdorff-target hypotheses as properness.
  have hproper : IsProperMap f := hf.isProperMap
  -- Then pass from properness to universal closedness via the chapter bridge theorem.
  exact hproper.isUniversallyClosedMap

end
