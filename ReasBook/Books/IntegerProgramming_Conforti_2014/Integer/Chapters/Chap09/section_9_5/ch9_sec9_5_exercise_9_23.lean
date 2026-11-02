import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

section Exercise923

/-- A `v × b` binary matrix has row sum `r`, column sum `k`, and row scalar product `λ` between
distinct rows when every entry is `0` or `1`, each row contains exactly `r` ones, each column
contains exactly `k` ones, and any two distinct rows intersect in exactly `λ` columns. -/
def exercise_9_23_has_parameters
    {v b : ℕ} (A : Matrix (Fin v) (Fin b) ℕ) (r k lam : ℕ) : Prop :=
  is_zero_one_family (fun ij : Fin v × Fin b ↦ A ij.1 ij.2) ∧
    (∀ i, ∑ j, A i j = r) ∧
      (∀ j, ∑ i, A i j = k) ∧
        ∀ i i' : Fin v, i ≠ i' → dotProduct (A i) (A i') = lam

/-- Expanding `exercise_9_23_has_parameters A r k lam` recovers the entrywise binary condition,
the constant row and column sums, and the constant pairwise row scalar product. -/
theorem exercise_9_23_has_parameters_iff
    {v b : ℕ} {A : Matrix (Fin v) (Fin b) ℕ} {r k lam : ℕ} :
    exercise_9_23_has_parameters A r k lam ↔
      is_zero_one_family (fun ij : Fin v × Fin b ↦ A ij.1 ij.2) ∧
        (∀ i, ∑ j, A i j = r) ∧
          (∀ j, ∑ i, A i j = k) ∧
            ∀ i i' : Fin v, i ≠ i' → dotProduct (A i) (A i') = lam :=
  Iff.rfl

namespace exercise_9_23_has_parameters

/-- Every entry of a matrix with Exercise 9.23 parameters is binary. -/
theorem entries
    {v b : ℕ} {A : Matrix (Fin v) (Fin b) ℕ} {r k lam : ℕ}
    (hA : exercise_9_23_has_parameters A r k lam) :
    is_zero_one_family (fun ij : Fin v × Fin b ↦ A ij.1 ij.2) :=
  hA.1

/-- Every row of a matrix with Exercise 9.23 parameters has sum `r`. -/
theorem row_sum
    {v b : ℕ} {A : Matrix (Fin v) (Fin b) ℕ} {r k lam : ℕ}
    (hA : exercise_9_23_has_parameters A r k lam) (i : Fin v) :
    ∑ j, A i j = r :=
  hA.2.1 i

/-- Every column of a matrix with Exercise 9.23 parameters has sum `k`. -/
theorem col_sum
    {v b : ℕ} {A : Matrix (Fin v) (Fin b) ℕ} {r k lam : ℕ}
    (hA : exercise_9_23_has_parameters A r k lam) (j : Fin b) :
    ∑ i, A i j = k :=
  hA.2.2.1 j

/-- Distinct rows of a matrix with Exercise 9.23 parameters have scalar product `λ`. -/
theorem row_scalar_product
    {v b : ℕ} {A : Matrix (Fin v) (Fin b) ℕ} {r k lam : ℕ}
    (hA : exercise_9_23_has_parameters A r k lam) {i i' : Fin v} (hii' : i ≠ i') :
    dotProduct (A i) (A i') = lam :=
  hA.2.2.2 i i' hii'

end exercise_9_23_has_parameters

/-- The strict row pairs `(i, i')` with `i < i'`, used to index the auxiliary variables attached
to distinct rows. -/
abbrev exercise_9_23_row_pair (v : ℕ) := { p : Fin v × Fin v // p.1 < p.2 }

namespace exercise_9_23_row_pair

/-- The first row in a strict row pair. -/
abbrev fst {v : ℕ} (p : exercise_9_23_row_pair v) : Fin v :=
  p.1.1

/-- The second row in a strict row pair. -/
abbrev snd {v : ℕ} (p : exercise_9_23_row_pair v) : Fin v :=
  p.1.2

/-- The two rows in a strict row pair are distinct. -/
theorem fst_ne_snd {v : ℕ} (p : exercise_9_23_row_pair v) :
    p.fst ≠ p.snd :=
  Fin.ne_of_lt p.2

end exercise_9_23_row_pair

/-- A pure `0,1` linear programming formulation of Exercise 9.23 uses binary variables `x i j`
for the matrix entries and binary auxiliary variables `y p j`, indexed by strict row pairs
`p : exercise_9_23_row_pair v`, that linearize the products `x p.fst j * x p.snd j`. -/
def exercise_9_23_pure_zero_one_linear_program_feasible
    (v b r k lam : ℕ) : Prop :=
  ∃ x : Matrix (Fin v) (Fin b) ℝ,
    ∃ y : exercise_9_23_row_pair v → Fin b → ℝ,
      is_zero_one_family (fun ij : Fin v × Fin b ↦ x ij.1 ij.2) ∧
        is_zero_one_family (fun pj : exercise_9_23_row_pair v × Fin b ↦ y pj.1 pj.2) ∧
          (∀ i, ∑ j, x i j = r) ∧
            (∀ j, ∑ i, x i j = k) ∧
              (∀ p, ∑ j, y p j = lam) ∧
                (∀ p j, y p j ≤ x p.fst j) ∧
                  (∀ p j, y p j ≤ x p.snd j) ∧
                    ∀ p j, x p.fst j + x p.snd j - 1 ≤ y p j

/-- Expanding the pure `0,1` formulation recovers its binary matrix variables, binary auxiliary
variables, row and column equations, and the standard linearization inequalities. -/
theorem exercise_9_23_pure_zero_one_linear_program_feasible_iff
    {v b r k lam : ℕ} :
    exercise_9_23_pure_zero_one_linear_program_feasible v b r k lam ↔
      ∃ x : Matrix (Fin v) (Fin b) ℝ,
        ∃ y : exercise_9_23_row_pair v → Fin b → ℝ,
          is_zero_one_family (fun ij : Fin v × Fin b ↦ x ij.1 ij.2) ∧
            is_zero_one_family (fun pj : exercise_9_23_row_pair v × Fin b ↦ y pj.1 pj.2) ∧
              (∀ i, ∑ j, x i j = r) ∧
                (∀ j, ∑ i, x i j = k) ∧
                  (∀ p, ∑ j, y p j = lam) ∧
                    (∀ p j, y p j ≤ x p.fst j) ∧
                      (∀ p j, y p j ≤ x p.snd j) ∧
                        ∀ p j, x p.fst j + x p.snd j - 1 ≤ y p j :=
  Iff.rfl

/-- Helper for Exercise 9.23: the product of two binary real scalars satisfies the standard
`0,1` linearization inequalities and remains binary. -/
lemma zeroOneProductLinearization
    {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a * b = 0 ∨ a * b = 1) ∧ a * b ≤ a ∧ a * b ≤ b ∧ a + b - 1 ≤ a * b := by
  -- The scalar statement is finite, so we verify the four binary cases directly.
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- Helper for Exercise 9.23: the binary auxiliary variable in the standard product
linearization is forced to equal the product. -/
lemma linearizedBinaryValue_eq_mul
    {a b y : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hy : y = 0 ∨ y = 1)
    (hya : y ≤ a) (hyb : y ≤ b) (haby : a + b - 1 ≤ y) :
    y = a * b := by
  -- The inequalities leave only the unique feasible binary value in each of the four cases.
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hy with rfl | rfl <;>
    nlinarith

/-- Helper for Exercise 9.23: reconstructing a natural entry from a binary real entry preserves
that entry after casting back to `ℝ`. -/
lemma cast_binaryEntry_eq_of_zeroOne
    {x : ℝ} (hx : x = 0 ∨ x = 1) :
    (((if x = 0 then 0 else 1 : ℕ) : ℝ) = x) := by
  -- The reconstructed entry is exactly the unique binary value already carried by `x`.
  rcases hx with rfl | rfl <;> norm_num

/-- Helper for Exercise 9.23: summing the auxiliary variables over a strict row pair recovers
the dot product of the two corresponding rows. -/
lemma rowPairDotProduct_eq_lam
    {v b lam : ℕ}
    {x : Matrix (Fin v) (Fin b) ℝ}
    {y : exercise_9_23_row_pair v → Fin b → ℝ}
    (hx : is_zero_one_family (fun ij : Fin v × Fin b ↦ x ij.1 ij.2))
    (hy : is_zero_one_family (fun pj : exercise_9_23_row_pair v × Fin b ↦ y pj.1 pj.2))
    (hpair : ∀ p, ∑ j, y p j = lam)
    (hy_le_fst : ∀ p j, y p j ≤ x p.fst j)
    (hy_le_snd : ∀ p j, y p j ≤ x p.snd j)
    (hlower : ∀ p j, x p.fst j + x p.snd j - 1 ≤ y p j) :
    ∀ p : exercise_9_23_row_pair v, dotProduct (x p.fst) (x p.snd) = lam := by
  intro p
  -- Each auxiliary coordinate coincides with the corresponding row-entry product.
  calc
    dotProduct (x p.fst) (x p.snd) = ∑ j, x p.fst j * x p.snd j := by
      simp [dotProduct]
    _ = ∑ j, y p j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      symm
      exact linearizedBinaryValue_eq_mul
        (is_zero_one_family.apply hx (p.fst, j))
        (is_zero_one_family.apply hx (p.snd, j))
        (is_zero_one_family.apply hy (p, j))
        (hy_le_fst p j)
        (hy_le_snd p j)
        (hlower p j)
    _ = lam := hpair p

/-- Exercise 9.23 (1). The question whether there exists a `v × b` binary matrix with exactly
`r` ones in each row, exactly `k` ones in each column, and scalar product `λ` between distinct
rows is equivalent to feasibility of the pure `0,1` linear program obtained by introducing binary
auxiliary variables for the pairwise row products. -/
theorem exercise_9_23_zero_one_linear_program_formulation
    (v b r k lam : ℕ) :
    (∃ A : Matrix (Fin v) (Fin b) ℕ, exercise_9_23_has_parameters A r k lam) ↔
      exercise_9_23_pure_zero_one_linear_program_feasible v b r k lam := by
  constructor
  · rintro ⟨A, hA⟩
    let x : Matrix (Fin v) (Fin b) ℝ := fun i j ↦ A i j
    let y : exercise_9_23_row_pair v → Fin b → ℝ := fun p j ↦ x p.fst j * x p.snd j
    have hxBinary : is_zero_one_family (fun ij : Fin v × Fin b ↦ x ij.1 ij.2) := by
      intro ij
      -- Casting the natural `0/1` entries preserves the binary condition in `ℝ`.
      rcases is_zero_one_family.apply (exercise_9_23_has_parameters.entries hA) ij with h0 | h1
      · left
        simp [x, h0]
      · right
        simp [x, h1]
    have hyBinary : is_zero_one_family
        (fun pj : exercise_9_23_row_pair v × Fin b ↦ y pj.1 pj.2) := by
      intro pj
      -- The auxiliary variables are products of binary coordinates, hence still binary.
      exact (zeroOneProductLinearization
        (is_zero_one_family.apply hxBinary (pj.1.fst, pj.2))
        (is_zero_one_family.apply hxBinary (pj.1.snd, pj.2))).1
    refine ⟨x, y, hxBinary, hyBinary, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      -- Row sums transport along the natural-to-real cast.
      simpa [x, Nat.cast_sum] using
        congrArg (fun n : ℕ ↦ (n : ℝ)) (exercise_9_23_has_parameters.row_sum hA i)
    · intro j
      -- Column sums transport along the natural-to-real cast in the same way.
      simpa [x, Nat.cast_sum] using
        congrArg (fun n : ℕ ↦ (n : ℝ)) (exercise_9_23_has_parameters.col_sum hA j)
    · intro p
      -- The pairwise row-product sum is the casted row dot product.
      calc
        ∑ j, y p j = dotProduct (x p.fst) (x p.snd) := by
          simp [y, dotProduct]
        _ = ((dotProduct (A p.fst) (A p.snd) : ℕ) : ℝ) := by
          symm
          simpa [x] using
            RingHom.map_dotProduct (Nat.castRingHom ℝ) (A p.fst) (A p.snd)
        _ = lam := by
          simpa using congrArg (fun n : ℕ ↦ (n : ℝ))
            (exercise_9_23_has_parameters.row_scalar_product hA p.fst_ne_snd)
    · intro p j
      -- The standard linearization inequalities come from the scalar `0/1` product lemma.
      exact (zeroOneProductLinearization
        (is_zero_one_family.apply hxBinary (p.fst, j))
        (is_zero_one_family.apply hxBinary (p.snd, j))).2.1
    · intro p j
      exact (zeroOneProductLinearization
        (is_zero_one_family.apply hxBinary (p.fst, j))
        (is_zero_one_family.apply hxBinary (p.snd, j))).2.2.1
    · intro p j
      exact (zeroOneProductLinearization
        (is_zero_one_family.apply hxBinary (p.fst, j))
        (is_zero_one_family.apply hxBinary (p.snd, j))).2.2.2
  · rintro ⟨x, y, hxBinary, hyBinary, hrow, hcol, hpair, hy_le_fst, hy_le_snd, hlower⟩
    let A : Matrix (Fin v) (Fin b) ℕ := fun i j ↦ if x i j = 0 then 0 else 1
    have hAentry : ∀ i j, (((A i j : ℕ) : ℝ) = x i j) := by
      intro i j
      -- Route correction: instead of unfolding transport through the reconstructed matrix
      -- everywhere, we prove the entrywise cast-back identity once and rewrite through it.
      simpa [A] using cast_binaryEntry_eq_of_zeroOne (is_zero_one_family.apply hxBinary (i, j))
    have hDotCast : ∀ i i', (((dotProduct (A i) (A i') : ℕ) : ℝ) = dotProduct (x i) (x i')) := by
      intro i i'
      -- Expanding the dot product once lets us rewrite every factor by the cast-back lemma.
      calc
        (((dotProduct (A i) (A i') : ℕ) : ℝ)) =
            ∑ j, (((A i j : ℕ) : ℝ) * ((A i' j : ℕ) : ℝ)) := by
              simp [dotProduct, Nat.cast_sum]
        _ = ∑ j, x i j * x i' j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hAentry i j, hAentry i' j]
        _ = dotProduct (x i) (x i') := by
          simp [dotProduct]
    refine ⟨A, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ij
      -- The reconstructed natural matrix is manifestly binary.
      by_cases hzero : x ij.1 ij.2 = 0
      · left
        simp [A, hzero]
      · right
        simp [A, hzero]
    · intro i
      -- Row sums descend from the real feasibility witness by cast injectivity.
      have hrowCast : (((∑ j, A i j : ℕ) : ℝ)) = r := by
        calc
        (((∑ j, A i j : ℕ) : ℝ)) = ∑ j, (((A i j : ℕ) : ℝ)) := by
          simp [Nat.cast_sum]
        _ = ∑ j, x i j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hAentry i j
        _ = r := hrow i
      exact_mod_cast hrowCast
    · intro j
      -- Column sums descend in the same way.
      have hcolCast : (((∑ i, A i j : ℕ) : ℝ)) = k := by
        calc
        (((∑ i, A i j : ℕ) : ℝ)) = ∑ i, (((A i j : ℕ) : ℝ)) := by
          simp [Nat.cast_sum]
        _ = ∑ i, x i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hAentry i j
        _ = k := hcol j
      exact_mod_cast hcolCast
    · intro i i' hii'
      -- The LP constrains strict row pairs, so we orient an arbitrary distinct pair by order.
      have hrowPairDot := rowPairDotProduct_eq_lam
        hxBinary hyBinary hpair hy_le_fst hy_le_snd hlower
      obtain hlt | hgt := lt_or_gt_of_ne hii'
      · let p : exercise_9_23_row_pair v := ⟨(i, i'), hlt⟩
        have hdotCast : (((dotProduct (A i) (A i') : ℕ) : ℝ)) = lam := by
          calc
          (((dotProduct (A i) (A i') : ℕ) : ℝ)) = dotProduct (x i) (x i') := hDotCast i i'
          _ = lam := by
            simpa [p] using hrowPairDot p
        exact_mod_cast hdotCast
      · let p : exercise_9_23_row_pair v := ⟨(i', i), hgt⟩
        have hdotCast : (((dotProduct (A i) (A i') : ℕ) : ℝ)) = lam := by
          calc
          (((dotProduct (A i) (A i') : ℕ) : ℝ)) = dotProduct (x i) (x i') := hDotCast i i'
          _ = dotProduct (x i') (x i) := by
            simp [dotProduct_comm]
          _ = lam := by
            simpa [p] using hrowPairDot p
        exact_mod_cast hdotCast

/-- The cyclic `7 × 7` incidence matrix whose `i`th row has ones in columns
`i`, `i + 1`, and `i + 3` modulo `7`. -/
def exercise_9_23_solution_matrix_7_7 : Matrix (Fin 7) (Fin 7) ℕ :=
  fun i j ↦
    if j.1 = i.1 ∨ j.1 = (i.1 + 1) % 7 ∨ j.1 = (i.1 + 3) % 7 then 1 else 0

/-- Exercise 9.23 (2). The explicit cyclic `7 × 7` binary matrix
`exercise_9_23_solution_matrix_7_7` solves the instance `(v, b, r, k, λ) = (7, 7, 3, 3, 1)`. -/
theorem exercise_9_23_solution_7_7_3_3_1 :
    exercise_9_23_has_parameters exercise_9_23_solution_matrix_7_7 3 3 1 := by
  -- After unfolding the concrete cyclic matrix, the remaining finite check is computational.
  simp [exercise_9_23_has_parameters, exercise_9_23_solution_matrix_7_7, is_zero_one_family]
  native_decide

end Exercise923
