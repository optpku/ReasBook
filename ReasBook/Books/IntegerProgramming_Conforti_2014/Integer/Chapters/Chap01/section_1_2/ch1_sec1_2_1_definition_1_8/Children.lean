module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Archimedean

public section

namespace MilpBranchAndBound

variable {n m : ℕ}

/-- The left branch child from `(1.u26)` keeps the parent node `P` and adds the inequality
`x_j ≤ ⌊f⌋`. -/
def leftChild
    (P : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  P ∩ {xy | xy.1 j ≤ Int.floor f}

/-- Membership in `leftChild P j f` means membership in `P` together with the left split inequality
`x_j ≤ ⌊f⌋`. -/
@[simp] theorem mem_leftChild_iff
    {P : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ leftChild P j f ↔ xy ∈ P ∧ xy.1 j ≤ Int.floor f :=
  Iff.rfl

/-- The right branch child from `(1.u26)` keeps the parent node `P` and adds the inequality
`⌈f⌉ ≤ x_j`. -/
def rightChild
    (P : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  P ∩ {xy | Int.ceil f ≤ xy.1 j}

/-- Membership in `rightChild P j f` means membership in `P` together with the right split
inequality `⌈f⌉ ≤ x_j`. -/
@[simp] theorem mem_rightChild_iff
    {P : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ rightChild P j f ↔ xy ∈ P ∧ Int.ceil f ≤ xy.1 j :=
  Iff.rfl

/-- The objective values attained by `mixed_linear_objective c h` on the left child
`leftChild P j f`. -/
@[expose] def leftChildObjectiveValues
    (P : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  mixed_linear_objective c h '' leftChild P j f

/-- Membership in `leftChildObjectiveValues P c h j f` is equivalent to the existence of a point
of the left child whose objective value is the chosen real number. -/
theorem mem_leftChildObjectiveValues_iff
    {P : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ leftChildObjectiveValues P c h j f ↔
      ∃ xy, xy ∈ P ∧ xy.1 j ≤ Int.floor f ∧ mixed_linear_objective c h xy = z := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    exact ⟨xy, (mem_leftChild_iff.mp hxy).1, (mem_leftChild_iff.mp hxy).2, rfl⟩
  · rintro ⟨xy, hP, hj, rfl⟩
    exact ⟨xy, (mem_leftChild_iff.mpr ⟨hP, hj⟩), rfl⟩

/-- The objective values attained by `mixed_linear_objective c h` on the right child
`rightChild P j f`. -/
@[expose] def rightChildObjectiveValues
    (P : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  mixed_linear_objective c h '' rightChild P j f

/-- Membership in `rightChildObjectiveValues P c h j f` is equivalent to the existence of a point
of the right child whose objective value is the chosen real number. -/
theorem mem_rightChildObjectiveValues_iff
    {P : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ rightChildObjectiveValues P c h j f ↔
      ∃ xy, xy ∈ P ∧ Int.ceil f ≤ xy.1 j ∧ mixed_linear_objective c h xy = z := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    exact ⟨xy, (mem_rightChild_iff.mp hxy).1, (mem_rightChild_iff.mp hxy).2, rfl⟩
  · rintro ⟨xy, hP, hj, rfl⟩
    exact ⟨xy, (mem_rightChild_iff.mpr ⟨hP, hj⟩), rfl⟩

end MilpBranchAndBound

end
