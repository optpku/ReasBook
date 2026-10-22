/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 2.3: The textbook notion that a family of events `(A_i)_{i ∈ I}` is independent is
the canonical mathlib predicate `ProbabilityTheory.iIndepSet` for a family of measurable sets with
respect to a measure. -/
recall ProbabilityTheory.iIndepSet

/-- The finite-intersection product formula characterizing independence of a family of measurable
events is the canonical theorem `ProbabilityTheory.iIndepSet_iff_meas_biInter`. -/
recall ProbabilityTheory.iIndepSet_iff_meas_biInter
