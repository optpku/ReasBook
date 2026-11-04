/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: finite-dimensional convex geometry / Helly's theorem
-- * source-facing chapter owner: `helly_theorem_empty_subfamily`
-- * core/canonical mathlib owner: `Convex.helly_theorem`
-- * primitive data: a finite family `F : Fin h → Set E` with the Helly cardinality bound,
--   convexity of each member, and empty total intersection
-- * derived API: a subfamily of cardinality `finrank 𝕜 E + 1` with empty intersection

/-
Exercise 3.31. The exercise asks to recover the chapter's Helly theorem. That public
source-facing outcome is already the chapter owner `helly_theorem_empty_subfamily`; the mathlib
theorem `Convex.helly_theorem` is only supporting infrastructure for its proof. Accordingly this
exercise should recall the existing chapter statement rather than introduce a second
`EuclideanSpace ℝ (Fin d)`-specialized wrapper theorem.
-/
recall helly_theorem_empty_subfamily
