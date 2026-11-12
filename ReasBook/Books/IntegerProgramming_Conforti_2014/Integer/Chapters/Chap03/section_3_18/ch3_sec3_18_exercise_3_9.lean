/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; verified Mathlib's
-- canonical convexity API in `Mathlib.Analysis.Convex.Basic`, where `convex_iInter` is the exact
-- owner theorem for indexed intersections and `convex_sInter` is its set-indexed companion.

/- Exercise 3.9. The intersection of any family of convex sets is a convex set. This is exactly
mathlib's canonical theorem `convex_iInter`. -/

#check convex_iInter
