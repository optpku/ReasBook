/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7.Lifting

open scoped BigOperators Matrix
open SequenceIndependentLifting

noncomputable section

section SequentialLiftingCoefficients

universe u

variable {ι : Type u} [DecidableEq ι]

/-- The slice used to compute the next sequential lifting coefficient of `x_j` after the
variables in `L` have already been lifted: the point lies in `S`, it satisfies `x_j = 1`, and
every still-unlifted variable outside `C ∪ L ∪ {j}` is fixed to `0`. -/
def sequential_lifting_slice
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (j : ι) : Set (ι → ℝ) :=
  {x | x ∈ S ∧ x j = 1 ∧ ∀ k, k ∉ insert j (C ∪ L) → x k = 0}

/-- Membership in `sequential_lifting_slice S C L j` means belonging to `S`, setting `x_j = 1`,
and forcing every as-yet-unlifted coordinate outside `C ∪ L ∪ {j}` to vanish. -/
theorem mem_sequential_lifting_slice_iff
    {S : Set (ι → ℝ)}
    {C L : Finset ι}
    {j : ι}
    {x : ι → ℝ} :
    x ∈ sequential_lifting_slice S C L j ↔
      x ∈ S ∧ x j = 1 ∧ ∀ k, k ∉ insert j (C ∪ L) → x k = 0 :=
  Iff.rfl

/-- The next coefficient assigned to `x_j` by the sequential lifting procedure after the
variables in `L` have already been lifted with current coefficient vector `c`. -/
def next_sequential_lifting_coefficient
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (c : ι → ℝ)
    (β : ℝ)
    (j : ι) : ℝ :=
  β - sSup ((fun x ↦ c ⬝ᵥ x) '' sequential_lifting_slice S C L j)

/-- Expanding `next_sequential_lifting_coefficient S C L c β j` recovers the usual sequential
lifting formula `β - sup {c x | x ∈ S, x_j = 1, x_k = 0 for the still-unlifted variables}`. -/
theorem next_sequential_lifting_coefficient_eq
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (c : ι → ℝ)
    (β : ℝ)
    (j : ι) :
    next_sequential_lifting_coefficient S C L c β j =
      β - sSup ((fun x ↦ c ⬝ᵥ x) '' sequential_lifting_slice S C L j) :=
  rfl

/-- The recursive coefficient vector produced by sequentially lifting the variables listed in
`σ`, starting from the base inequality supported on `C`. -/
private def sequential_lifting_coefficientsAux
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) : ι → ℝ :=
  match σ with
  | [] => c
  | j :: τ =>
      let αj := next_sequential_lifting_coefficient S C L c β j
      sequential_lifting_coefficientsAux S C β (insert j L) (Function.update c j αj) τ

/-- The coefficient vector obtained by sequentially lifting the complement variables in the order
`σ`, starting from the base coefficients on `C`. -/
def sequential_lifting_coefficients
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (σ : List ι) : ι → ℝ :=
  sequential_lifting_coefficientsAux S C β ∅ (base_coefficients C α) σ

/-- With no variables left to lift, the sequential lifting coefficient vector is the original
base coefficient vector. -/
theorem sequential_lifting_coefficients_nil
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ) :
    sequential_lifting_coefficients S C α β [] = base_coefficients C α :=
  rfl

end SequentialLiftingCoefficients
