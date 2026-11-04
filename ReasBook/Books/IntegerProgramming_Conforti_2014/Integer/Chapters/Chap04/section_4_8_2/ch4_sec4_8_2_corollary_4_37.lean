/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_theorem_4_36

open scoped BigOperators Matrix

/- The local prerequisite cache predates the namespaced encoding API.  These transparent aliases
restore its former spelling while reducing definitionally to the current public declarations. -/

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the legacy scalar rational-encoding name agrees with the current encoding API. -/
abbrev rational_encoding_size (q : ℚ) : ℕ := EncodingSize.rational q

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the legacy integer-vector encoding name agrees with the current encoding API. -/
abbrev integer_vector_encoding_size (n : ℕ) (x : Fin n → ℤ) : ℕ :=
  EncodingSize.integerVector x

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the legacy rational-vector encoding name agrees with the current encoding API. -/
abbrev rational_vector_encoding_size (n : ℕ) (x : Fin n → ℚ) : ℕ :=
  EncodingSize.rationalVector x

-- Domain-style sampling for this refine pass:
-- * primary domain: encoding-size bounds for feasible integer points of rational systems
-- * sampled owner results: Chapter 4.8.2 Theorem 4.36 and Lemma 4.35, plus Chapter 4.1
--   `rational_matrix_polyhedron`
-- * owner abstraction: the uniform polynomial-bound theorem of Theorem 4.36
-- * primitive data: a rational system `A x ≤ b`, an entrywise encoding bound `L`, and an
--   integral feasible point
-- * derived API: a uniformly polynomially bounded integral feasible witness

section Corollary437

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the signed-variable matrix adjoining the negative of every column. -/
private def integerVariableSplitMatrix (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin (n + n)) ℚ :=
  fun i ↦ Fin.append (A i) (fun j ↦ -A i j)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the difference between the two blocks of a signed-variable vector. -/
private def integerVariableDifference (u : Fin (n + n) → ℤ) : Fin n → ℤ :=
  fun j ↦ u (Fin.castAdd n j) - u (Fin.natAdd n j)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the nonnegative positive and negative parts representing an integer vector. -/
private def integerVariableParts (x : Fin n → ℤ) : Fin (n + n) → ℤ :=
  Fin.append (fun j ↦ max 0 (x j)) (fun j ↦ max 0 (-x j))

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
subtracting the positive and negative parts recovers the original integer vector. -/
private lemma integerVariableDifference_parts (x : Fin n → ℤ) :
    integerVariableDifference (integerVariableParts x) = x := by
  -- Compute both blocks coordinatewise and use the standard positive/negative-parts identity.
  funext j
  rw [integerVariableDifference, integerVariableParts, Fin.append_left, Fin.append_right]
  simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self (x j)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
both blocks of the positive/negative-parts representation are nonnegative. -/
private lemma integerVariableParts_nonnegative (x : Fin n → ℤ) :
    0 ≤ integerVariableParts x := by
  -- Split the joined index and use nonnegativity of `max 0` in each block.
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    rw [integerVariableParts, Fin.append_left]
    exact le_max_left _ _
  · intro j
    rw [integerVariableParts, Fin.append_right]
    exact le_max_left _ _

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
negating the second block does not increase the entrywise rational encoding bound. -/
private lemma integerVariableSplitMatrix_encoding_le
    {A : Matrix (Fin m) (Fin n) ℚ} {L : ℕ}
    (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L) :
    ∀ i j, EncodingSize.rational (integerVariableSplitMatrix A i j) ≤ L := by
  -- Inspect the original and negated blocks separately.
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [integerVariableSplitMatrix, Fin.append_left]
    exact hA i k
  · intro k
    rw [integerVariableSplitMatrix, Fin.append_right]
    simpa [EncodingSize.rational_eq] using hA i k

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the signed-variable matrix acts through the difference of its two variable blocks. -/
private lemma integerVariableSplitMatrix_mulVec
    (A : Matrix (Fin m) (Fin n) ℚ) (u : Fin (n + n) → ℤ) :
    (integerVariableSplitMatrix A).map (Rat.castHom ℝ) *ᵥ (fun k ↦ (u k : ℝ)) =
      A.map (Rat.castHom ℝ) *ᵥ (fun j ↦ (integerVariableDifference u j : ℝ)) := by
  -- Split the matrix product into its two blocks and distribute the subtraction.
  ext i
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_add]
  simp only [Matrix.map_apply, integerVariableSplitMatrix, Fin.append_left,
    integerVariableDifference, Int.cast_sub]
  simp_rw [Fin.append_right]
  simp only [map_neg, neg_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the positive/negative-parts representation of a feasible integer vector is feasible for the
nonnegative signed-variable system. -/
private lemma integerVariableParts_mem_nonnegativeSplit
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {x : Fin n → ℤ}
    (hx : Int.cast ∘ x ∈ rational_matrix_polyhedron A b) :
    ((fun k ↦ (integerVariableParts x k : ℝ)), (0 : Fin 0 → ℝ)) ∈
      nonnegative_rational_mixed_integer_points (integerVariableSplitMatrix A)
        (0 : Matrix (Fin m) (Fin 0) ℚ) b := by
  -- Establish the inequalities and both nonnegativity conditions of the split system.
  rw [nonnegative_rational_mixed_integer_points, mem_mixed_integer_points_iff]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mem_rational_mixed_polyhedron_iff, integerVariableSplitMatrix_mulVec]
    rw [mem_rational_matrix_polyhedron] at hx
    simpa [integerVariableDifference_parts] using hx
  · intro k
    exact Int.cast_nonneg (integerVariableParts_nonnegative x k)
  · intro k
    exact Fin.elim0 k
  · rw [mem_mixed_integer_lattice_exists_iff]
    exact ⟨integerVariableParts x, rfl⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
the difference of the integer blocks of a feasible split point is feasible for the original
system. -/
private lemma integerVariableDifference_mem_of_split_mem
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {u : Fin (n + n) → ℤ} {y : Fin 0 → ℚ}
    (hu : ((fun k ↦ (u k : ℝ)), fun k ↦ (y k : ℝ)) ∈
      nonnegative_rational_mixed_integer_points (integerVariableSplitMatrix A)
        (0 : Matrix (Fin m) (Fin 0) ℚ) b) :
    Int.cast ∘ integerVariableDifference u ∈ rational_matrix_polyhedron A b := by
  -- Forget nonnegativity and integrality, then rewrite the split matrix action.
  have hpolyhedron := (mem_mixed_integer_points_iff.mp hu).1.1
  rw [mem_rational_mixed_polyhedron_iff, integerVariableSplitMatrix_mulVec] at hpolyhedron
  rw [mem_rational_matrix_polyhedron]
  simpa using hpolyhedron

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
encoding an integer difference costs no more than encoding its two operands separately. -/
private lemma integerEncoding_sub_le_add (a b : ℤ) :
    EncodingSize.integer (a - b) ≤ EncodingSize.integer a + EncodingSize.integer b := by
  -- Bound the absolute difference, then compare both summands with a common power of two.
  have habs : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le a b
  have ha : a.natAbs < 2 ^ Nat.size a.natAbs := Nat.lt_size_self _
  have hb : b.natAbs < 2 ^ Nat.size b.natAbs := Nat.lt_size_self _
  have hpowA :
      2 ^ Nat.size a.natAbs ≤ 2 ^ (Nat.size a.natAbs + Nat.size b.natAbs) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowB :
      2 ^ Nat.size b.natAbs ≤ 2 ^ (Nat.size a.natAbs + Nat.size b.natAbs) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have habsLt :
      (a - b).natAbs < 2 ^ (Nat.size a.natAbs + Nat.size b.natAbs + 1) := by
    calc
      (a - b).natAbs ≤ a.natAbs + b.natAbs := habs
      _ < 2 ^ Nat.size a.natAbs + 2 ^ Nat.size b.natAbs := Nat.add_lt_add ha hb
      _ ≤ 2 ^ (Nat.size a.natAbs + Nat.size b.natAbs) +
          2 ^ (Nat.size a.natAbs + Nat.size b.natAbs) := Nat.add_le_add hpowA hpowB
      _ = 2 ^ (Nat.size a.natAbs + Nat.size b.natAbs + 1) := by
        simp [pow_succ, Nat.mul_two]
  have hsize :
      Nat.size (a - b).natAbs ≤ Nat.size a.natAbs + Nat.size b.natAbs + 1 :=
    Nat.size_le.mpr habsLt
  simp only [EncodingSize.integer_eq]
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
taking the difference of two equal-length blocks does not increase their total integer encoding. -/
private lemma integerVector_difference_le (u : Fin (n + n) → ℤ) :
    EncodingSize.integerVector (integerVariableDifference u) ≤
      EncodingSize.integerVector u := by
  -- Sum the scalar difference bound and identify the two block sums with the joined vector.
  rw [EncodingSize.integerVector_eq_sum, EncodingSize.integerVector_eq_sum,
    Fin.sum_univ_add]
  simpa [integerVariableDifference, Finset.sum_add_distrib] using
    (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
      integerEncoding_sub_le_add (u (Fin.castAdd n j)) (u (Fin.natAdd n j)))

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean:
evaluation of a polynomial with natural coefficients is monotone. -/
private lemma polynomialNatEval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  -- Constants are fixed, while sums and positive-degree monomials preserve order.
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c a b hab
    simp
  · intro q r hq hr a b hab
    simpa only [Polynomial.eval_add] using Nat.add_le_add (hq hab) (hr hab)
  · intro k c _ a b hab
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab (k + 1))

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_corollary_4_37.lean — Corollary 4.37. Given `A ∈ ℚ^(m × n)` and `b ∈ ℚ^m`, let `L` be the maximum encoding size of
the coefficients of `(A, b)`. If the system `A x ≤ b` has an integral solution, then it has an
integral solution `xbar` whose encoding size is polynomially bounded by `n` and `L`. -/
theorem rational_linear_inequality_system_has_small_integral_solution :
    ∃ π : Polynomial ℕ,
      ∀ {m n : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ L)
        (hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
        (hfeas : ∃ x : Fin n → ℤ, Int.cast ∘ x ∈ rational_matrix_polyhedron A b),
        ∃ xbar : Fin n → ℤ,
          Int.cast ∘ xbar ∈ rational_matrix_polyhedron A b ∧
            EncodingSize.integerVector xbar ≤ π.eval (n + L) := by
  let π₀ : Polynomial ℕ :=
    Classical.choose mixed_integer_linear_feasibility_has_polynomially_bounded_certificate
  refine ⟨π₀.comp (Polynomial.X + Polynomial.X), ?_⟩
  intro m n A b L hA hb hfeas
  obtain ⟨x, hx⟩ := hfeas
  -- Represent the original feasible point by nonnegative positive and negative parts.
  have hsplitFeasible :
      Set.Nonempty
        (nonnegative_rational_mixed_integer_points (integerVariableSplitMatrix A)
          (0 : Matrix (Fin m) (Fin 0) ℚ) b) :=
    ⟨((fun k ↦ (integerVariableParts x k : ℝ)), (0 : Fin 0 → ℝ)),
      integerVariableParts_mem_nonnegativeSplit hx⟩
  have hzeroEncoding :
      ∀ i : Fin m, ∀ j : Fin 0,
        EncodingSize.rational ((0 : Matrix (Fin m) (Fin 0) ℚ) i j) ≤ L := by
    intro _ j
    exact Fin.elim0 j
  let hcertificate :=
    (Classical.choose_spec mixed_integer_linear_feasibility_has_polynomially_bounded_certificate)
      (integerVariableSplitMatrix A) (0 : Matrix (Fin m) (Fin 0) ℚ) b L
        (integerVariableSplitMatrix_encoding_le hA) hzeroEncoding hb hsplitFeasible
  let u : Fin (n + n) → ℤ := Classical.choose hcertificate
  let huExists := Classical.choose_spec hcertificate
  let y : Fin 0 → ℚ := Classical.choose huExists
  have huy := Classical.choose_spec huExists
  refine ⟨integerVariableDifference u, integerVariableDifference_mem_of_split_mem huy.1, ?_⟩
  -- Transfer the certificate bound to the block difference and absorb doubling into the polynomial.
  have huSize : EncodingSize.integerVector u ≤ π₀.eval (n + n + L) := by
    have hcombined :
        EncodingSize.integerVector u + EncodingSize.rationalVector y ≤
          π₀.eval (n + n + L) := by
      simpa [π₀, u, y] using huy.2
    omega
  calc
    EncodingSize.integerVector (integerVariableDifference u) ≤
        EncodingSize.integerVector u := integerVector_difference_le u
    _ ≤ π₀.eval (n + n + L) := huSize
    _ ≤ π₀.eval ((n + L) + (n + L)) :=
      polynomialNatEval_monotone π₀ (by omega)
    _ = (π₀.comp (Polynomial.X + Polynomial.X)).eval (n + L) := by
      simp [Polynomial.eval_comp]

end Corollary437

#print axioms rational_linear_inequality_system_has_small_integral_solution
