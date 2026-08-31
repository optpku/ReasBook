module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I] [IsFiltered I]

/- Domain-style sampling for Lemma 4.19.2:
- primary domain: filtered categories and preservation of finite limits by colimits of
  `Type`-valued diagrams
- inspected owner declarations:
  - `CategoryTheory.IsFiltered`
  - `CategoryTheory.Limits.PreservesFiniteLimits`
  - `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSize`
  - `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`
- owner abstraction: `PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`
- primitive data: the filteredness hypothesis on `I`
- derived API: the canonical owner property is available by instance search; mathlib constructs it
  via `filtered_colim_preservesFiniteLimits_of_types`
- target layer here: `core/canonical`, so the file should expose the owner property directly rather
  than introduce a parallel local theorem or use the bridge instance name as the main entry
-/
/- Source/core/bridge triage for Lemma 4.19.2:
- `source-facing`: the filteredness hypothesis on the index category `I`
- `core/canonical`: `PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`
- `bridge/view`: the named mathlib instance
  `filtered_colim_preservesFiniteLimits_of_types`
-/
/- Lemma 4.19.2: if `I` is filtered, then colimits over `I` commute with finite limits in the
category of sets. In mathlib this is expressed directly by the owner property
`PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v)`. The named instance
`CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types` is the canonical proof term
behind the instance search below. -/
#check
  (show PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v) from inferInstance)

end CategoryTheory.Limits
