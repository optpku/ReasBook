module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.RE

/-!
# Computability closure used before DPRM

Generic facts about recursively enumerable predicates that this development needs *below* the
DPRM theorem. Nothing here mentions `Dioph`, and nothing here may depend on `REPred.dioph`.

## Why this is its own module

The import direction is the point:

```
Computability  →  DPRM  →  DerivedDioph  →  endpoints and examples
```

`REPred.of_manyOneReducible` is convenient enough to be reached for anywhere, and one of the
places it must *not* be reached for is inside the DPRM proof, where "recursive enumerability
transfers along a computable map" is close enough to the theorem being proved to invite a circle.
Keeping it here, below `DPRM`, makes the permitted direction visible in the import graph rather
than in a comment. The post-DPRM consequences live in `DerivedDioph`, above it.

Its two consumers are the integer formulation (`rePred_intSolvable`) and that derived layer.

## Main results

* `Hilbert10.REPred.of_manyOneReducible`
-/

@[expose] public section

namespace Hilbert10

/-- **Recursive enumerability transfers backwards along a many-one reduction.** -/
theorem REPred.of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} (h : p ≤₀ q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hfp⟩ := h
  refine (Partrec.comp hq hf).of_eq fun a => ?_
  rw [propext (hfp a)]

end Hilbert10
