/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix

section Corollary57BasisFamily

variable {m n : ℕ}

/-- The restricted matrix obtained from `A` by keeping only the rows indexed by `B`. -/
abbrev basis_row_matrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin m)) :
    Matrix {i // i ∈ B} (Fin n) ℝ :=
  A.submatrix Subtype.val id

/-- The restricted right-hand side obtained from `b` by keeping only the entries indexed by
`B`. -/
abbrev basis_row_rhs
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) :
    {i // i ∈ B} → ℝ :=
  b ∘ Subtype.val

/-- The row-restricted polyhedron `P_B`, obtained by keeping only the inequalities indexed by
`B`. -/
def P_B
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | basis_row_matrix A B *ᵥ x ≤ basis_row_rhs b B}

/-- Membership in `P_B` is the restricted-row matrix system cut out by `A` and `b`. -/
theorem mem_P_B_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (x : Fin n → ℝ) :
    x ∈ P_B A b B ↔ basis_row_matrix A B *ᵥ x ≤ basis_row_rhs b B :=
  Iff.rfl

/-- Membership in `P_B` is exactly the family of inequalities indexed by `B`. -/
theorem mem_P_B_rows_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (x : Fin n → ℝ) :
    x ∈ P_B A b B ↔ ∀ i : Fin m, i ∈ B → (A *ᵥ x) i ≤ b i :=
by
  constructor
  · intro hx i hi
    rw [mem_P_B_iff] at hx
    simpa [basis_row_matrix, basis_row_rhs] using hx ⟨i, hi⟩
  · intro hx
    rw [mem_P_B_iff]
    intro i
    simpa [basis_row_matrix, basis_row_rhs] using hx i.1 i.2

/-- A row multiplier supported on `B` whose left multiplication with `A` reproduces the split
vector `π`. -/
def IsSupportedSplitRowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m))
    (u : Fin m → ℝ) : Prop :=
  (u ᵥ* A = fun j : Fin n ↦ (π j : ℝ)) ∧
    ∀ i : Fin m, i ∉ B → u i = 0

/-- A supported split row multiplier reproduces `π` and vanishes off `B`. -/
theorem isSupportedSplitRowMultiplier_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m))
    (u : Fin m → ℝ) :
    IsSupportedSplitRowMultiplier A π B u ↔
      (u ᵥ* A = fun j : Fin n ↦ (π j : ℝ)) ∧
        ∀ i : Fin m, i ∉ B → u i = 0 :=
  Iff.rfl

/-- The family of row sets `B` for which the split vector `π` admits a unique supported row
multiplier. The source-facing notation is `𝓑[A, π]`. -/
def splitBasisFamily
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ) : Set (Finset (Fin m)) :=
  {B : Finset (Fin m) | ∃! u : Fin m → ℝ, IsSupportedSplitRowMultiplier A π B u}

namespace SplitBasisNotation

scoped notation:max "𝓑[" A ", " π "]" => splitBasisFamily A π

end SplitBasisNotation

open scoped SplitBasisNotation

/-- Membership in `𝓑` means that `π` admits a unique supported row multiplier for the row set
`B`. -/
theorem mem_𝓑_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m)) :
    B ∈ 𝓑[A, π] ↔ ∃! u : Fin m → ℝ, IsSupportedSplitRowMultiplier A π B u :=
  Iff.rfl

/-- The split-closure family `𝓑[A]` of row sets whose rows are linearly independent. These are
the row subsets that can occur as independent supports in the Chapter 5 split-cut reduction. -/
def splitClosureBasisFamily
    (A : Matrix (Fin m) (Fin n) ℝ) : Set (Finset (Fin m)) :=
  {B : Finset (Fin m) |
    LinearIndependent ℝ (fun i : {i // i ∈ B} ↦ A i.1)}

namespace SplitBasisNotation

scoped notation:max "𝓑[" A "]" => splitClosureBasisFamily A

end SplitBasisNotation

/-- Membership in the split-closure family `𝓑[A]` means that the rows indexed by `B` are
linearly independent. -/
theorem mem_𝓑_split_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin m)) :
    B ∈ 𝓑[A] ↔
      LinearIndependent ℝ (fun i : {i // i ∈ B} ↦ A i.1) :=
  Iff.rfl

end Corollary57BasisFamily
