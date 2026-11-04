/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_corollary_3_47

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: projections of matrix-defined polyhedra via multiplier certificates
-- * primitive owner data: the canonical projection `Prod.fst '' S` of a subset `S ⊆ X × Z`
-- * core/canonical owner theorem:
--   `polyhedron_x_projection_image_eq_forall_nonneg_multipliers`
-- * bridge/view API: `mem_image_fst_iff`, which rewrites the projection image into the textbook
--   existential set-builder form

/- Exercise 3.36: this is already the chapter owner corollary
`polyhedron_x_projection_image_eq_forall_nonneg_multipliers`; the source-text set-builder form is
the companion projection view obtained by `mem_image_fst_iff`. -/
recall polyhedron_x_projection_image_eq_forall_nonneg_multipliers
recall mem_image_fst_iff
