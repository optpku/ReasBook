/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetRel

universe u v w z

namespace SetRel

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A subset of `H × H` is monotone when any two of its points satisfy the standard
inner-product monotonicity inequality. -/
def IsMonotone (M : SetRel H H) : Prop :=
  ∀ ⦃x u y v : H⦄, x ~[M] u → y ~[M] v → 0 ≤ ⟪x - y, u - v⟫_ℝ

-- Proof sketch: unfold `SetRel.IsMonotone`; the displayed statement is exactly the defining
-- pairwise inequality on the relation.
/-- Unfolding `SetRel.IsMonotone` gives the pairwise monotonicity inequality on the relation. -/
theorem isMonotone_iff (M : SetRel H H) :
    M.IsMonotone ↔ ∀ ⦃x u y v : H⦄, x ~[M] u → y ~[M] v → 0 ≤ ⟪x - y, u - v⟫_ℝ :=
  Iff.rfl

end SetRel

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section Prod

variable {X : Type u} {Y : Type v}
variable {Z : Type w} {W : Type z}

/-- The product of two set-valued operators acts componentwise on pairs of inputs. -/
def prod (A : SetValuedOperator X Y) (B : SetValuedOperator Z W) :
    SetValuedOperator (X × Z) (Y × W) :=
  fun p ↦ A p.1 ×ˢ B p.2

/- The source-facing product operator is used repeatedly later in Chapter 20, so we expose the
ordinary product notation on the theorem surface. -/
scoped[SetValuedOperator] infixr:35 " × " => SetValuedOperator.prod

/-- Membership in the product operator is equivalent to componentwise membership. -/
@[simp] theorem mem_prod_iff
    (A : SetValuedOperator X Y) (B : SetValuedOperator Z W)
    (p : X × Z) (u : Y × W) :
    u ∈ (A × B) p ↔ u.1 ∈ A p.1 ∧ u.2 ∈ B p.2 := Iff.rfl

end Prod

/-- Definition 20.1: a set-valued operator on a real Hilbert space is monotone when any two
points of its graph satisfy the inequality `0 ≤ ⟪x - y, u - v⟫_ℝ`. -/
abbrev IsMonotone (A : SetValuedOperator H H) : Prop :=
  A.graph.IsMonotone

-- Proof sketch: unfold `SetValuedOperator.IsMonotone`, rewrite relation membership in `A.graph`
-- via `SetValuedOperator.mem_graph`, and obtain exactly the textbook pointwise inequality.
/-- A set-valued operator is monotone exactly when all `u ∈ A x` and `v ∈ A y` satisfy the
textbook monotonicity inequality. -/
theorem isMonotone_iff (A : SetValuedOperator H H) :
    A.IsMonotone ↔
      ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ :=
by
  change A.graph.IsMonotone ↔
    ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ
  rw [SetRel.isMonotone_iff]
  simp

/-- The singleton-valued operator attached to a map on a subset is monotone exactly when the map
itself satisfies the pointwise monotonicity inequality on that subset. -/
theorem ofFunction_isMonotone_iff {D : Set H} {T : D → H} :
    (ofFunction D T).IsMonotone ↔ ∀ x y : D, 0 ≤ ⟪(x : H) - y, T x - T y⟫_ℝ := by
  rw [isMonotone_iff]
  constructor
  · intro h x y
    have hx : T x ∈ ofFunction D T x := by
      simp [ofFunction_apply_of_mem D T x.2]
    have hy : T y ∈ ofFunction D T y := by
      simp [ofFunction_apply_of_mem D T y.2]
    simpa using h hx hy
  · intro h x u y v hu hv
    rcases hu with ⟨hx, rfl⟩
    rcases hv with ⟨hy, rfl⟩
    simpa using h ⟨x, hx⟩ ⟨y, hy⟩

end SetValuedOperator
