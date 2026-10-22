/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 6.16: The textbook notion of a uniformly integrable family in `ℒ¹(μ)` is
formalized directly by the owner predicate `MeasureTheory.UniformIntegrable` at exponent `1`,
applied to the underlying functions. This item introduces no chapter-local alias or wrapper; the
later theorem files use the canonical predicate and its derived API directly. -/
recall MeasureTheory.UniformIntegrable
