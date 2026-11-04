/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Exercise 3.34. Projecting a convex hull to the `x`-coordinates is a direct specialization of
mathlib's canonical linear-image theorem `LinearMap.image_convexHull`; the relevant projection map
is `LinearMap.fst`.
-/

#check LinearMap.fst
#check LinearMap.image_convexHull
