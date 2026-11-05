/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Tactic.Recall
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch`, so this file reuses the Chapter 6 gauge API already established in
-- `ch6_sec6_2_1_definition_6_2_1_extra_1`.

/- Exercise 6.7 is a `bridge/view` recall: the source-facing exercise statement is exactly the
Chapter 6 gauge theorem
`gauge_le_one_iff_mem_of_isClosed_of_convex_of_zero_mem_interior`.

Keeping a second theorem with the same interface would only duplicate the public API, so this file
recalls the existing owner directly. -/
recall gauge_le_one_iff_mem_of_isClosed_of_convex_of_zero_mem_interior
