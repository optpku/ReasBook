import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Exercise 3.34. Projecting a convex hull to the `x`-coordinates is a direct specialization of
mathlib's canonical linear-image theorem `LinearMap.image_convexHull`; the relevant projection map
is `LinearMap.fst`.
-/

#check LinearMap.fst
#check LinearMap.image_convexHull
