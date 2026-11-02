module

public import Mathlib.Data.Real.Basic

public section

/-- The ambient mixed real space `ℝ^n × ℝ^p` for mixed-integer points. -/
abbrev MixedRealPoint (n p : ℕ) := (Fin n → ℝ) × (Fin p → ℝ)

/-- The embedded integer lattice `ℤ^n ⊆ ℝ^n`. -/
def integerVectors (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z)

namespace IntegerVectorNotation

scoped notation "ℤ^" n:max => integerVectors n

end IntegerVectorNotation

open scoped IntegerVectorNotation

/-- Membership in `ℤ^n` means that the vector is the real coercion of an integer vector. -/
theorem mem_integerVectors_iff
    {n : ℕ} {x : Fin n → ℝ} :
    x ∈ ℤ^n ↔ ∃ z : Fin n → ℤ, x = Int.cast ∘ z := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- A real vector lies in `ℤ^n` exactly when each coordinate is an integer. -/
theorem mem_integerVectors_iff_forall
    {n : ℕ} {x : Fin n → ℝ} :
    x ∈ ℤ^n ↔ ∀ j, x j ∈ Set.range (Int.cast : ℤ → ℝ) := by
  constructor
  · rintro ⟨z, rfl⟩ j
    exact ⟨z j, rfl⟩
  · intro hx
    refine ⟨fun j ↦ Classical.choose (hx j), ?_⟩
    funext j
    exact Classical.choose_spec (hx j)

/-- The embedded mixed-integer lattice `ℤ^n × ℝ^p` inside `MixedRealPoint n p`, with an integral
`x`-block and an arbitrary real `y`-block. -/
def mixed_integer_lattice (n p : ℕ) : Set (MixedRealPoint n p) :=
  {xy | ∃ z : Fin n → ℤ, xy.1 = Int.cast ∘ z}

namespace MixedIntegerNotation

scoped notation:max "ℤ^" n:max "×ℝ^" p:max => mixed_integer_lattice n p

end MixedIntegerNotation

open scoped MixedIntegerNotation

/-- Membership in `ℤ^n × ℝ^p` means that the integer block is the real coercion of an integer
vector. -/
theorem mem_mixed_integer_lattice_exists_iff
    {n p : ℕ} {xy : MixedRealPoint n p} :
    xy ∈ (ℤ^n×ℝ^p) ↔ ∃ z : Fin n → ℤ, xy.1 = Int.cast ∘ z := by
  rfl

/-- Membership in `ℤ^n × ℝ^p` is equivalent to integrality of the first block. -/
theorem mem_mixed_integer_lattice_iff
    {n p : ℕ} {xy : MixedRealPoint n p} :
    xy ∈ (ℤ^n×ℝ^p) ↔ xy.1 ∈ ℤ^n := by
  rw [mem_mixed_integer_lattice_exists_iff, mem_integerVectors_iff]

end
