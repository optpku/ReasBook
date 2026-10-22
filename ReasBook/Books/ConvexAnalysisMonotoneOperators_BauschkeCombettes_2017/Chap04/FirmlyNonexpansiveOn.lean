/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SubtypeFirmness

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A map `T : D → H` is firmly nonexpansive on `D` when its displacement satisfies the standard
Hilbert-space firm nonexpansiveness inequality for every pair of points in `D`. -/
def FirmlyNonexpansiveOn (D : Set H) (T : D → H) : Prop :=
  ∀ x y : D, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ ((x : H) - y) (T x - T y)

/-- The predicate `FirmlyNonexpansiveOn D T` unfolds to the displayed inner-product inequality. -/
theorem firmlyNonexpansiveOn_iff (D : Set H) (T : D → H) :
    FirmlyNonexpansiveOn D T ↔
      ∀ x y : D, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ ((x : H) - y) (T x - T y) := by
  rfl

/-- On the whole space, firm nonexpansiveness is exactly the standard Hilbert-space inequality
`‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
theorem firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    simpa [real_inner_comm] using h ⟨x, by simp⟩ ⟨y, by simp⟩
  · intro h x y
    simpa [real_inner_comm] using h (x : H) (y : H)

/-- A self-map is firmly nonexpansive when it is firmly nonexpansive on the whole space. -/
def FirmlyNonexpansive (T : H → H) : Prop :=
  FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x)

/-- Unfolding `FirmlyNonexpansive` recovers the whole-space restriction formulation. -/
@[simp] theorem firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ {T : H → H} :
    FirmlyNonexpansive T ↔
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) := by
  rfl

/-- On the whole space, firm nonexpansiveness is exactly the standard Hilbert-space inequality
`‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
theorem firmlyNonexpansive_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansive T ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
  exact firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner

end

end SubtypeFirmness
