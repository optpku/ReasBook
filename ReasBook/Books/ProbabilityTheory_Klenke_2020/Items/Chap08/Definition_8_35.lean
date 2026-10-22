/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Definition 8.35: The textbook notion of a Borel space is formalized by the canonical
measurable-space class `StandardBorelSpace`. This is the mathlib owner abstraction for spaces
measurably isomorphic to Borel subsets of `ℝ`; the companion recall below records the explicit
real-subset realization. -/
recall StandardBorelSpace

/- Any standard Borel space is measurably equivalent to a Borel subset of `ℝ`. -/
recall exists_subset_real_measurableEquiv

/- A Polish space is the canonical topological class `PolishSpace`. -/
recall PolishSpace

/- A closed subset of a Polish space is again Polish. -/
recall IsClosed.polishSpace
