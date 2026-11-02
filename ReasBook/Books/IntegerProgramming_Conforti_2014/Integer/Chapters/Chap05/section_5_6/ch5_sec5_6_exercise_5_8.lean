import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_remark_5_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_1

open scoped IntegerVectorNotation

-- Domain-style sampling for this refine pass:
-- * primary domain: one-row pure-integer halfspaces and their rounded split/Chvatal hulls;
-- * core/canonical owner:
--   `convexHull_mixed_integer_halfspace_eq_rounded_halfspace_of_relatively_prime_coefficients`;
-- * supporting owners: `split_dot` and the Chapter 4 lattice owner `ℤ^n`;
-- * source-facing layer kept here: Exercise 5.8 as the pure-integer specialization.

section Exercise58

variable {n : ℕ}

/-- The pure-integer set
`S = {x ∈ ℤ^n | ∑_{j=1}^n a_j x_j ≤ b}`
from Exercise 5.8, viewed inside `ℝ^n`. -/
def exercise_5_8_integer_halfspace
    (a : Fin n → ℤ)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ ℤ^n ∧ split_dot a x ≤ b}

/-- Membership in `exercise_5_8_integer_halfspace a b` is exactly integrality together with the
defining one-row inequality. -/
theorem mem_exercise_5_8_integer_halfspace_iff
    (a : Fin n → ℤ)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ exercise_5_8_integer_halfspace a b ↔ x ∈ ℤ^n ∧ split_dot a x ≤ b :=
  Iff.rfl

/-- The coefficient gcd `k` from Exercise 5.8, computed as the gcd of the coordinate absolute
values of the integer row `a`. -/
def exercise_5_8_coefficientGcd (a : Fin n → ℤ) : ℕ :=
  Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j))

/-- The normalized coefficient vector `a / k` from Exercise 5.8, where
`k = exercise_5_8_coefficientGcd a`. -/
def exercise_5_8_normalizedCoefficients (a : Fin n → ℤ) : Fin n → ℤ :=
  fun j ↦ a j / exercise_5_8_coefficientGcd a

/-- The rounded real halfspace
`{x ∈ ℝ^n | ∑ (a_j / k) x_j ≤ ⌊b / k⌋}`
from Exercise 5.8, where `k = exercise_5_8_coefficientGcd a`. -/
def exercise_5_8_normalized_halfspace
    (a : Fin n → ℤ)
    (b : ℝ) : Set (Fin n → ℝ) :=
  {x |
    split_dot (exercise_5_8_normalizedCoefficients a) x ≤
      (Int.floor (b / exercise_5_8_coefficientGcd a) : ℝ)}

/-- Membership in `exercise_5_8_normalized_halfspace a b` is exactly the normalized one-row
inequality from Exercise 5.8. -/
theorem mem_exercise_5_8_normalized_halfspace_iff
    (a : Fin n → ℤ)
    (b : ℝ)
    (x : Fin n → ℝ) :
    x ∈ exercise_5_8_normalized_halfspace a b ↔
      split_dot (exercise_5_8_normalizedCoefficients a) x ≤
        (Int.floor (b / exercise_5_8_coefficientGcd a) : ℝ) :=
  Iff.rfl

/-- Exercise 5.8. Let `a ∈ ℤ^n \ {0}` and `b ∈ ℝ`, and let
`S = {x ∈ ℤ^n | ∑_{j=1}^n a_j x_j ≤ b}`.
If `k = exercise_5_8_coefficientGcd a` is the greatest common divisor of `a₁, …, aₙ`, then
`conv(S) = {x ∈ ℝ^n | ∑_{j=1}^n (a_j / k) x_j ≤ ⌊b / k⌋}`. This is the pure-integer
specialization of the Chapter 5 rounded mixed-integer halfspace owner. -/
theorem convexHull_exercise_5_8_integer_halfspace_eq_normalized_halfspace
    (a : Fin n → ℤ)
    (b : ℝ)
    (ha_nonzero : a ≠ 0) :
    convexHull ℝ (exercise_5_8_integer_halfspace a b) =
      exercise_5_8_normalized_halfspace a b := by
  let g := exercise_5_8_coefficientGcd a
  have hg_pos : 0 < g := by
    simpa [g, exercise_5_8_coefficientGcd] using coordinate_gcd_pos a ha_nonzero
  have hprimitive :
      Finset.univ.gcd
          (fun j : Fin n ↦ Int.natAbs (exercise_5_8_normalizedCoefficients a j)) = 1 := by
    simpa [exercise_5_8_normalizedCoefficients, exercise_5_8_coefficientGcd] using
      normalized_split_vector_gcd_eq_one a ha_nonzero
  have hnormalized_nonzero : exercise_5_8_normalizedCoefficients a ≠ 0 := by
    intro hzero
    have hzero_gcd :
        Finset.univ.gcd
            (fun j : Fin n ↦ Int.natAbs (exercise_5_8_normalizedCoefficients a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [hzero]
    rw [hzero_gcd] at hprimitive
    exact Nat.zero_ne_one hprimitive
  let s : Split Finset.univ :=
    { π := exercise_5_8_normalizedCoefficients a
      π0 := 0
      nonzero := hnormalized_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hs_primitive : s.IsPrimitive := by
    simpa [Split.IsPrimitive, s] using hprimitive
  have hscale (x : Fin n → ℝ) :
      split_dot a x = (g : ℝ) * split_dot s x := by
    simpa [g, s, exercise_5_8_coefficientGcd, exercise_5_8_normalizedCoefficients] using
      normalized_split_dot_eq_gcd_mul a ha_nonzero x
  have hleft :
      exercise_5_8_integer_halfspace a b =
        {x : Fin n → ℝ |
          (∀ j ∈ (Finset.univ : Finset (Fin n)), ∃ z : ℤ, x j = (z : ℝ)) ∧
            split_dot s x ≤ b / g} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_int, hx_le⟩
      refine ⟨?_, ?_⟩
      · rw [mem_integerVectors_iff_forall] at hx_int
        intro j hj
        rcases hx_int j with ⟨z, hz⟩
        exact ⟨z, hz.symm⟩
      · have hg_real_pos : (0 : ℝ) < g := by
          exact_mod_cast hg_pos
        rw [hscale x] at hx_le
        exact (le_div_iff₀ hg_real_pos).2 (by simpa [mul_comm] using hx_le)
    · intro hx
      rcases hx with ⟨hx_int, hx_le⟩
      refine ⟨?_, ?_⟩
      · rw [mem_integerVectors_iff_forall]
        intro j
        rcases hx_int j (by simp) with ⟨z, hz⟩
        exact ⟨z, hz.symm⟩
      · have hg_real_pos : (0 : ℝ) < g := by
          exact_mod_cast hg_pos
        rw [hscale x]
        have hmul : split_dot s x * g ≤ b := (le_div_iff₀ hg_real_pos).1 hx_le
        simpa [mul_comm] using hmul
  calc
    convexHull ℝ (exercise_5_8_integer_halfspace a b)
        = convexHull ℝ {x : Fin n → ℝ |
            (∀ j ∈ (Finset.univ : Finset (Fin n)), ∃ z : ℤ, x j = (z : ℝ)) ∧
              split_dot s x ≤ b / g} := by
            rw [hleft]
    _ = {x : Fin n → ℝ | split_dot s x ≤ (Int.floor (b / g) : ℝ)} := by
      simpa using
        convexHull_mixed_integer_halfspace_eq_rounded_halfspace_of_relatively_prime_coefficients
          Finset.univ s (b / g) hs_primitive
    _ = exercise_5_8_normalized_halfspace a b := by
      ext x
      simp [exercise_5_8_normalized_halfspace, g, s]

end Exercise58
