import Mathlib.Data.Real.Basic

-- This support owner isolates the Chapter 5 binary-point API used across later chapters without
-- importing the heavier sequential-convexification machinery.

section ZeroOnePointsSupport

variable {n p : ℕ}

/-- The unit-box constraint on the first `p` coordinates of `x ∈ ℝ^n`. -/
def prefix_unit_box
    (hpn : p ≤ n) : Set (Fin n → ℝ) :=
  {x | ∀ j : Fin p, 0 ≤ x (Fin.castLE hpn j) ∧ x (Fin.castLE hpn j) ≤ 1}

/-- Membership in `prefix_unit_box hpn` means that each of the first `p` coordinates lies in the
interval `[0, 1]`. -/
theorem mem_prefix_unit_box_iff
    (hpn : p ≤ n)
    (x : Fin n → ℝ) :
    x ∈ prefix_unit_box hpn ↔
      ∀ j : Fin p, 0 ≤ x (Fin.castLE hpn j) ∧ x (Fin.castLE hpn j) ≤ 1 :=
  Iff.rfl

/-- The points of `P` whose first `t` coordinates are binary. -/
def prefix_binary_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t ≤ p) : Set (Fin n → ℝ) :=
  {x |
    x ∈ P ∧
      ∀ j : Fin t,
        x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 0 ∨
          x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 1}

/-- Membership in `prefix_binary_points hpn P ht` means belonging to `P` and having binary first
`t` coordinates. -/
theorem mem_prefix_binary_points_iff
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t ≤ p)
    (x : Fin n → ℝ) :
    x ∈ prefix_binary_points hpn P ht ↔
      x ∈ P ∧
        ∀ j : Fin t,
          x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 0 ∨
            x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 1 :=
  Iff.rfl

/-- The set `S = {x ∈ P : x_j ∈ {0,1} for j = 1, …, p}` attached to the first `p` coordinates. -/
def zero_one_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  prefix_binary_points hpn P (Nat.le_refl p)

/-- The full-prefix binary-point owner agrees with the specialized source-facing owner
`zero_one_points`. -/
theorem prefix_binary_points_full_eq_zero_one_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    prefix_binary_points hpn P (Nat.le_refl p) = zero_one_points hpn P :=
  rfl

/-- If there are no distinguished binary coordinates, then `zero_one_points hpn P` is just `P`. -/
theorem zero_one_points_eq_self_of_eq_zero
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hp0 : p = 0) :
    zero_one_points hpn P = P := by
  subst p
  ext x
  simp [zero_one_points, prefix_binary_points]

/-- Membership in `zero_one_points hpn P` means belonging to `P` and having binary first
`p` coordinates. -/
theorem mem_zero_one_points_iff
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ zero_one_points hpn P ↔
      x ∈ P ∧
        ∀ j : Fin p, x (Fin.castLE hpn j) = 0 ∨ x (Fin.castLE hpn j) = 1 :=
  Iff.rfl

end ZeroOnePointsSupport
