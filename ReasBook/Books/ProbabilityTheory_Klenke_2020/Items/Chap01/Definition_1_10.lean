/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.10: A λ-system, or Dynkin system, on `Ω` is the canonical mathlib bundled object
`MeasurableSpace.DynkinSystem Ω`; its underlying family of sets contains `univ`, is closed under
differences `B \ A` when `A ⊆ B`, and is closed under countable pairwise disjoint unions. -/
recall MeasurableSpace.DynkinSystem
