import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_7.Coefficients

section SequentialLiftingOrder

universe u

variable {ι : Type u} [DecidableEq ι]

/-- A sequential lifting order is a duplication-free list containing exactly the variables
outside the base support `C`. -/
def IsSequentialLiftingOrder
    [Fintype ι]
    (C : Finset ι)
    (σ : List ι) : Prop :=
  σ.Nodup ∧ σ.toFinset = Finset.univ \ C

/-- `IsSequentialLiftingOrder C σ` means that `σ` is duplication-free and its underlying finite
set is exactly the complement of `C`. -/
theorem isSequentialLiftingOrder_iff
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι} :
    IsSequentialLiftingOrder C σ ↔
      σ.Nodup ∧ σ.toFinset = Finset.univ \ C :=
  Iff.rfl

/-- Auxiliary recursion for `IsFeasibleSequentialLiftingOrder`: along the lifting order `σ`,
each stage requires the corresponding `x_j = 1` slice with the still-unlifted variables fixed to
`0` to be nonempty. -/
private def feasibleSequentialLiftingOrderAux
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (σ : List ι) : Prop :=
  match σ with
  | [] => True
  | j :: τ =>
      (sequential_lifting_slice S C L j).Nonempty ∧
        feasibleSequentialLiftingOrderAux S C (insert j L) τ

/-- A sequential lifting order is feasible for `S` if every stagewise slice used to define the
next coefficient is nonempty. This rules out convention-dependent values coming from `sSup ∅` and
matches the source interpretation of the sequential lifting procedure. -/
def IsFeasibleSequentialLiftingOrder
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (σ : List ι) : Prop :=
  feasibleSequentialLiftingOrderAux S C ∅ σ

namespace IsSequentialLiftingOrder

/-- A sequential lifting order has no repeated indices. -/
theorem nodup
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ) :
    σ.Nodup :=
  hσ.1

/-- The finite support of a sequential lifting order is exactly the complement of `C`. -/
theorem toFinset_eq
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ) :
    σ.toFinset = Finset.univ \ C :=
  hσ.2

/-- In a sequential lifting order for `C`, an index appears exactly when it lies outside `C`. -/
theorem mem_iff
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι} :
    j ∈ σ ↔ j ∉ C := by
  rw [← List.mem_toFinset, hσ.toFinset_eq]
  simp

/-- Moving a variable `j ∉ C` to the front of an admissible sequential lifting order preserves
admissibility. -/
theorem cons_erase
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι}
    (hj : j ∉ C) :
    IsSequentialLiftingOrder C (j :: σ.erase j) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_cons]
    constructor
    · simp [hσ.nodup.mem_erase_iff]
    · simpa using hσ.nodup.erase j
  · ext k
    by_cases hk : k = j
    · simp [hk, hj]
    · simp [hk, hσ.nodup.mem_erase_iff, hσ.mem_iff]

/-- Moving a variable `j ∉ C` to the end of an admissible sequential lifting order preserves
admissibility. -/
theorem erase_append_single
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι}
    (hj : j ∉ C) :
    IsSequentialLiftingOrder C (σ.erase j ++ [j]) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨by simpa using hσ.nodup.erase j, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = j := by simpa using hb
    subst hb'
    simpa using (hσ.nodup.mem_erase_iff.1 ha).1
  · ext k
    by_cases hk : k = j
    · simp [hk, hj]
    · simp [hk, hσ.nodup.mem_erase_iff, hσ.mem_iff]

end IsSequentialLiftingOrder

end SequentialLiftingOrder
