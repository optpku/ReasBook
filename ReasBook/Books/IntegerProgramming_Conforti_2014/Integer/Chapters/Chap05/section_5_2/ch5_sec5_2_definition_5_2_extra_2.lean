/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: mixed-integer Chvatal closures for matrix polyhedra;
-- * sampled Chapter 5 owners: `mixed_integer_feasible_set`, `Split`,
--   `mixed_integer_rounding_closure`, and the later set-level `chvatalClosure`;
-- * source-facing owner kept here: the matrix presentation `chvatalClosure A b I`;
-- * primitive data kept here: `IsMixedIntegerCoefficient`;
-- * derived API kept here: `IsChvatalMultiplier`, `mem_chvatalClosure_iff`, and
--   `mem_chvatalClosure_expanded_iff`.

section Definition52Extra2

variable {m n : ℕ}

/-- A coefficient vector for the mixed-integer index set `I` is integral on the coordinates in
`I` and vanishes on the continuous-variable coordinates. -/
def IsMixedIntegerCoefficient
    (I : Finset (Fin n))
    (α : Fin n → ℝ) : Prop :=
  (∀ j : Fin n, j ∈ I → ∃ z : ℤ, α j = (z : ℝ)) ∧
    ∀ j : Fin n, j ∉ I → α j = 0

/-- `IsMixedIntegerCoefficient I α` unfolds to integrality on `I` and vanishing outside `I`. -/
theorem isMixedIntegerCoefficient_iff
    (I : Finset (Fin n))
    (α : Fin n → ℝ) :
    IsMixedIntegerCoefficient I α ↔
      (∀ j : Fin n, j ∈ I → ∃ z : ℤ, α j = (z : ℝ)) ∧
        ∀ j : Fin n, j ∉ I → α j = 0 :=
  Iff.rfl

namespace IsMixedIntegerCoefficient

/-- A mixed-integer coefficient vector is integral on the coordinates indexed by `I`. -/
theorem exists_int
    {I : Finset (Fin n)}
    {α : Fin n → ℝ}
    (hα : IsMixedIntegerCoefficient I α)
    {j : Fin n}
    (hj : j ∈ I) :
    ∃ z : ℤ, α j = (z : ℝ) :=
  hα.1 j hj

/-- A mixed-integer coefficient vector vanishes on the coordinates outside `I`. -/
theorem eq_zero_of_not_mem
    {I : Finset (Fin n)}
    {α : Fin n → ℝ}
    (hα : IsMixedIntegerCoefficient I α)
    {j : Fin n}
    (hj : j ∉ I) :
    α j = 0 :=
  hα.2 j hj

end IsMixedIntegerCoefficient

/-- A Chvátal multiplier for the mixed-integer system `A x ≤ b` is a nonnegative row multiplier
whose left product with `A` is integral on the integer-variable coordinates and vanishes on the
continuous-variable coordinates. -/
def IsChvatalMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ u i) ∧
    IsMixedIntegerCoefficient I (u ᵥ* A)

/-- `IsChvatalMultiplier A I u` unfolds to nonnegativity, integrality on the integer variables,
and vanishing on the continuous variables. -/
theorem isChvatalMultiplier_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ) :
    IsChvatalMultiplier A I u ↔
      (∀ i : Fin m, 0 ≤ u i) ∧
        (∀ j : Fin n, j ∈ I → ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ)) ∧
          ∀ j : Fin n, j ∉ I → (u ᵥ* A) j = 0 :=
  Iff.rfl

namespace IsChvatalMultiplier

/-- A Chvátal multiplier has nonnegative row coefficients. -/
theorem nonneg
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsChvatalMultiplier A I u)
    (i : Fin m) :
    0 ≤ u i :=
  hu.1 i

/-- The row-product coefficient vector of a Chvátal multiplier is mixed-integer on `I`. -/
theorem isMixedIntegerCoefficient
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsChvatalMultiplier A I u) :
    IsMixedIntegerCoefficient I (u ᵥ* A) :=
  hu.2

/-- The row-product coefficient vector of a Chvátal multiplier is integral on the
integer-variable coordinates. -/
theorem exists_int
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsChvatalMultiplier A I u)
    {j : Fin n}
    (hj : j ∈ I) :
    ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ) :=
  hu.isMixedIntegerCoefficient.exists_int hj

/-- The row-product coefficient vector of a Chvátal multiplier vanishes on the continuous
coordinates. -/
theorem eq_zero_of_not_mem
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsChvatalMultiplier A I u)
    {j : Fin n}
    (hj : j ∉ I) :
    (u ᵥ* A) j = 0 :=
  hu.isMixedIntegerCoefficient.eq_zero_of_not_mem hj

end IsChvatalMultiplier

/-- Definition 5.2-extra-2 (1). The Chvatal closure `P^Ch` of
`P = {x : R^n | A x <= b}` for the integer-variable index set `I` is the set of points of `P`
satisfying every Chvatal inequality, equivalently every inequality
`(u ᵥ* A) x <= floor (u b)` with `u >= 0`, integral coefficients on `I`, and zero coefficients on
the continuous-variable indices. -/
def chvatalClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    x ∈ polyhedron_le_set A b ∧
      ∀ u : Fin m → ℝ,
        IsChvatalMultiplier A I u →
          (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ)}

/-- Membership in `chvatalClosure A b I` means belonging to the original polyhedron and satisfying
every Chvátal inequality indexed by a Chvátal multiplier. -/
theorem mem_chvatalClosure_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ chvatalClosure A b I ↔
      x ∈ polyhedron_le_set A b ∧
        ∀ u : Fin m → ℝ,
          IsChvatalMultiplier A I u →
            (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) :=
  Iff.rfl

/-- Expanded companion form of `mem_chvatalClosure_iff` matching the textbook multiplier
conditions directly. -/
theorem mem_chvatalClosure_expanded_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ chvatalClosure A b I ↔
      x ∈ polyhedron_le_set A b ∧
        ∀ u : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ u i) →
          (∀ j : Fin n, j ∈ I → ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ)) →
          (∀ j : Fin n, j ∉ I → (u ᵥ* A) j = 0) →
          (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := by
  simp [mem_chvatalClosure_iff, isChvatalMultiplier_iff]

/-- Definition 5.2-extra-2 (2). The Chvatal closure `P^Ch` is contained in the original polyhedron
`P = {x : R^n | A x <= b}`. -/
theorem chvatalClosure_subset_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    chvatalClosure A b I ⊆ polyhedron_le_set A b := fun _ hx ↦ hx.1

end Definition52Extra2
