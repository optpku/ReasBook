/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 4.10: a map `T : D → H` on a real Hilbert space is `β`-cocoercive, or
`β`-inverse strongly monotone, when `β > 0` and
`⟪x - y, T x - T y⟫ ≥ β ‖T x - T y‖²` for all `x, y ∈ D`. -/
def CocoerciveOn (β : ℝ) (D : Set H) (T : D → H) : Prop :=
  0 < β ∧
    ∀ x y : D, β * ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y)

/-- A `β`-cocoercive map has positive cocoercivity parameter. -/
theorem CocoerciveOn.pos {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T) :
    0 < β :=
  hT.1

/-- A `β`-cocoercive map satisfies the textbook lower bound
`β ‖T x - T y‖² ≤ ⟪x - y, T x - T y⟫` at every pair of points in its domain. -/
theorem CocoerciveOn.ineq {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T)
    (x y : D) :
    β * ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y) :=
  hT.2 x y
