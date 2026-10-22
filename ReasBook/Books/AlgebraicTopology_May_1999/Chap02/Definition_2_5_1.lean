/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory FundamentalGroupoid
open scoped FundamentalGroupoid

variable (X : Type u) [TopologicalSpace X]
variable {X} {x y : TopCat.of X}

/- Definition 2.5.1: the fundamental groupoid `Π(X)` is the canonical groupoid
`πₓ (TopCat.of X)`, whose objects are the points of `X` and whose morphisms are endpoint-fixed
homotopy classes of paths. -/
#check (πₓ (TopCat.of X))

/- The objects of the fundamental groupoid are the points of the underlying space. -/
recall toTop {Y : TopCat} (x : πₓ Y) : Y

/- A homotopy class of paths from `x` to `y` defines a morphism in the fundamental groupoid. -/
recall fromPath (p : Path.Homotopic.Quotient x y) :
    fromTop x ⟶ fromTop y

/- Every morphism in the fundamental groupoid can be viewed as an endpoint-fixed homotopy class
of paths. -/
recall toPath {Y : TopCat} {x₀ x₁ : πₓ Y} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient (toTop x₀) (toTop x₁)
