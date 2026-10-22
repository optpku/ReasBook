/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 2.11: The textbook notion that a family of classes of events
`(ℰᵢ)ᵢ`, viewed as a family `ι → Set (Set Ω)` of collections of measurable sets, is independent is
the canonical mathlib predicate `ProbabilityTheory.iIndepSets`. -/
recall ProbabilityTheory.iIndepSets

/-- The finite-choice product formula characterizing independence of classes of events is the
canonical theorem `ProbabilityTheory.iIndepSets_iff`. -/
recall ProbabilityTheory.iIndepSets_iff
