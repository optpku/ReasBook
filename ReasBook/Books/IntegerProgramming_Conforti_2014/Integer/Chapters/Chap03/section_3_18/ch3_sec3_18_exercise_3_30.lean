/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_43

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: Radon partitions for finite-dimensional convexity
-- * source-facing chapter owner: `radon_theorem`
-- * source-facing primitive data: an ambient set `S : Set E` with the Radon-cardinality bound
-- * core/canonical supporting theorem: `Convex.radon_partition`
-- * bridge inside the chapter proof: choose a finite subtype of `S`, apply the core partition
--   theorem there, then extend the resulting partition back to the ambient set

/-
Exercise 3.30. This exercise asks for a proof of Theorem 3.43 using affine dependence. The
source-facing statement is Chapter 3's `radon_theorem`. The proof route goes through the
affine-dependent family theorem `Convex.radon_partition`, but that mathlib theorem is only
supporting provenance for the chapter statement rather than the public outcome of this exercise.
-/
recall radon_theorem
