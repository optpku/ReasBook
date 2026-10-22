/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Lemma 1.28: composing a lower semicontinuous extended-real-valued function with a continuous
map preserves lower semicontinuity. -/
theorem lowerSemicontinuous_comp {f : Y → EReal} {g : X → Y}
    (hf : LowerSemicontinuous f) (hg : Continuous g) :
    LowerSemicontinuous (f ∘ g) :=
  hf.comp hg

end ERealFunction
