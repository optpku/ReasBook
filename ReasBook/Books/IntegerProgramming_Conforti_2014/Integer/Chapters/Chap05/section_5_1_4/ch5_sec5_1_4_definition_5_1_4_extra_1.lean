/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Archimedean

open scoped BigOperators

noncomputable section Definition514Extra1

variable {n : ℕ}

/-- The coefficient of the Gomory mixed integer inequality `(5.13)` attached to the aggregated
equation `α x = β`, assuming the right-hand side is fractional (`0 < Int.fract β`), with `I` the
set of integer-variable indices and `j ∉ I` treated as a continuous variable. -/
def gomory_mixed_integer_inequality_coefficient
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (j : Fin n) : ℝ :=
  let f :=
    if hfract : Int.fract β = 0 then
      False.elim ((ne_of_gt hβ) hfract)
    else
      Int.fract β
  if j ∈ I then
    if Int.fract (α j) ≤ f then
      Int.fract (α j) / f
    else
      (1 - Int.fract (α j)) / (1 - f)
  else if 0 ≤ α j then
    α j / f
  else
    (-α j) / (1 - f)

/-- The defining case split for `gomory_mixed_integer_inequality_coefficient`. -/
@[simp]
theorem gomory_mixed_integer_inequality_coefficient_eq
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (j : Fin n) :
    gomory_mixed_integer_inequality_coefficient I α β hβ j =
      if j ∈ I then
        if Int.fract (α j) ≤ Int.fract β then
          Int.fract (α j) / Int.fract β
        else
          (1 - Int.fract (α j)) / (1 - Int.fract β)
      else if 0 ≤ α j then
        α j / Int.fract β
      else
        (-α j) / (1 - Int.fract β) :=
  by simp [gomory_mixed_integer_inequality_coefficient, ne_of_gt hβ]

/-- A right-hand side admitted by the Gomory mixed integer inequality owner is nonintegral. -/
theorem gomory_mixed_integer_rhs_not_integral
    (β : ℝ)
    (hβ : 0 < Int.fract β) :
    β ∉ Set.range (Int.cast : ℤ → ℝ) := by
  exact (Int.fract_ne_zero_iff).1 (ne_of_gt hβ)

/-- Definition 5.1.4-extra-1. For the aggregated equation `α x = β` arising from a row
multiplier `u`, the Gomory mixed integer inequality `(5.13)` for the integer-variable index set
`I` and fractional right-hand side `β` is the halfspace with right-hand side `1` whose
coefficients are given by the mixed formula using `f = β - ⌊β⌋`, the fractional parts of `α_j`
on `I`, and the signs of `α_j` on the continuous-variable indices. -/
def gomory_mixed_integer_inequality
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    1 ≤ ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j}

/-- Membership in `gomory_mixed_integer_inequality I α β` is exactly the normalized Gomory mixed
integer inequality attached to `α x = β`. -/
@[simp]
theorem mem_gomory_mixed_integer_inequality_iff
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (x : Fin n → ℝ) :
    x ∈ gomory_mixed_integer_inequality I α β hβ ↔
      1 ≤ ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j :=
  Iff.rfl

/-- The split right-hand side `π₀` from `(5.14)` attached to the Gomory mixed integer inequality
derived from `α x = β`. -/
def gomory_mixed_integer_split_rhs
    (β : ℝ) : ℤ :=
  Int.floor β

/-- `gomory_mixed_integer_split_rhs β` is the floor of the aggregated right-hand side `β`. -/
@[simp]
theorem gomory_mixed_integer_split_rhs_eq_floor
    (β : ℝ) :
    gomory_mixed_integer_split_rhs β = Int.floor β :=
  rfl

/-- The split right-hand side from `(5.14)` decomposes `β` into its integral and fractional
parts. -/
theorem gomory_mixed_integer_split_rhs_add_fract
    (β : ℝ) :
    (gomory_mixed_integer_split_rhs β : ℝ) + Int.fract β = β := by
  rw [gomory_mixed_integer_split_rhs]
  exact Int.floor_add_fract β

/-- The split coefficient vector `π` from `(5.14)` attached to the Gomory mixed integer
inequality derived from `α x = β`. -/
def gomory_mixed_integer_split_vector
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) : Fin n → ℤ :=
  fun j ↦
    if j ∈ I then
      if Int.fract (α j) ≤ Int.fract β then
        Int.floor (α j)
      else
        Int.ceil (α j)
    else
      0

/-- The split vector from `(5.14)` vanishes on every continuous-variable index. -/
@[simp]
theorem gomory_mixed_integer_split_vector_eq_zero_of_not_mem
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    {j : Fin n}
    (hj : j ∉ I) :
    gomory_mixed_integer_split_vector I α β j = 0 := by
  simp [gomory_mixed_integer_split_vector, hj]

/-- On an integer-variable index with `Int.fract (α j) ≤ Int.fract β`, the split vector from
`(5.14)` uses `⌊α j⌋`. -/
@[simp] theorem gomory_mixed_integer_split_vector_eq_floor_of_mem
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    {j : Fin n}
    (hj : j ∈ I)
    (hfract : Int.fract (α j) ≤ Int.fract β) :
    gomory_mixed_integer_split_vector I α β j = Int.floor (α j) := by
  simp [gomory_mixed_integer_split_vector, hj, hfract]

/-- On an integer-variable index with `Int.fract β < Int.fract (α j)`, the split vector from
`(5.14)` uses `⌈α j⌉`. -/
@[simp] theorem gomory_mixed_integer_split_vector_eq_ceil_of_mem
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    {j : Fin n}
    (hj : j ∈ I)
    (hfract : ¬ Int.fract (α j) ≤ Int.fract β) :
    gomory_mixed_integer_split_vector I α β j = Int.ceil (α j) := by
  simp [gomory_mixed_integer_split_vector, hj, hfract]

/-- The split data `(π, π₀)` from `(5.14)` defines a Chapter 5 split whenever the coefficient
vector `π` is nonzero. -/
def gomory_mixed_integer_split
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hπ : gomory_mixed_integer_split_vector I α β ≠ 0) : Split I where
  π := gomory_mixed_integer_split_vector I α β
  π0 := gomory_mixed_integer_split_rhs β
  nonzero := hπ
  zero_on_continuous := by
    intro j hj
    exact gomory_mixed_integer_split_vector_eq_zero_of_not_mem I α β (Finset.mem_compl.mp hj)

/-- The coefficient vector of `gomory_mixed_integer_split` is the split vector `π` from `(5.14)`.
-/
@[simp] theorem gomory_mixed_integer_split_apply
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hπ : gomory_mixed_integer_split_vector I α β ≠ 0)
    (j : Fin n) :
    gomory_mixed_integer_split I α β hπ j = gomory_mixed_integer_split_vector I α β j :=
  rfl

/-- The split right-hand side of `gomory_mixed_integer_split` is the `π₀` from `(5.14)`. -/
@[simp] theorem gomory_mixed_integer_split_pi0
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hπ : gomory_mixed_integer_split_vector I α β ≠ 0) :
    (gomory_mixed_integer_split I α β hπ).π0 = gomory_mixed_integer_split_rhs β :=
  rfl

/-- The split vector from `(5.14)` is an integer split coefficient vector in the sense of
`split_dot`. -/
theorem gomory_mixed_integer_split_vector_split_dot_eq_sum
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (x : Fin n → ℝ) :
    split_dot (gomory_mixed_integer_split_vector I α β) x =
      ∑ j : Fin n, (gomory_mixed_integer_split_vector I α β j : ℝ) * x j := by
  simpa using split_dot_eq_sum (gomory_mixed_integer_split_vector I α β) x

end Definition514Extra1
