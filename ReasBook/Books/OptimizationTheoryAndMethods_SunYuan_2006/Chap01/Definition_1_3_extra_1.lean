/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2

section Chapter01Definition13Extra1

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this file:
-- * `convexHull` is the canonical mathlib owner for convex hulls of subsets of a real vector space.
-- * `convexHull_eq_iInter` is the canonical lattice-style description as the intersection of all
--   convex supersets.
-- * `convexHull_eq` is the canonical finite-convex-combination description.
-- * `subset_convexHull` and `convexHull_min` express the minimality statement.

/-
Chapter01 Definition 1.3-extra-1

Core/canonical owner: for `S : Set Point`, the convex hull of `S` is
`convexHull ℝ S`. This item is a direct canonical recall, not a new source-facing wrapper.
The source assumes `S` is nonempty, but that hypothesis is redundant for the owner itself, which
is defined for arbitrary sets and specializes directly to the textbook setting.

Primitive data: only the set `S`.

Derived API already available in mathlib:
- `convexHull_eq_iInter`: `convexHull ℝ S` is the intersection of all convex sets containing `S`.
- `convexHull_eq`: `convexHull ℝ S` is the set of finite convex combinations of points of `S`.

The statement that `convexHull ℝ S` is the smallest convex set containing `S` is expressed by
`subset_convexHull` and `convexHull_min`.
-/
#check (convexHull ℝ : Set Point → Set Point)

#check fun (S : Set Point) ↦
  show convexHull ℝ S = ⋂ (T : Set Point) (_ : S ⊆ T) (_ : Convex ℝ T), T from
    convexHull_eq_iInter ℝ S

#check fun (S : Set Point) ↦
  show convexHull ℝ S =
      { x : Point | ∃ (ι : Type) (t : Finset ι) (w : ι → ℝ) (z : ι → Point),
          (∀ i ∈ t, 0 ≤ w i) ∧
            ∑ i ∈ t, w i = 1 ∧ (∀ i ∈ t, z i ∈ S) ∧ t.centerMass w z = x } from
    convexHull_eq S

#check fun (S : Set Point) ↦
  show S ⊆ convexHull ℝ S from subset_convexHull ℝ S

#check fun {S T : Set Point} (hST : S ⊆ T) (hT : Convex ℝ T) ↦
  show convexHull ℝ S ⊆ T from convexHull_min hST hT

end Chapter01Definition13Extra1
