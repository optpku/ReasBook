/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_3_theorem_9_10

open scoped Matrix

-- Domain style sampling:
-- * primary domain: integral points of rational polyhedra cut out by integer hyperplanes
-- * source-facing layer: the coprime-row elimination lemma matching Lemma 9.11
-- * core/canonical owners reused here: `rational_matrix_polyhedron`,
--   `integer_hyperplane`, and `is_primitive_integer_vector`
-- * primitive data: `A`, `b`, `α`, `β`, and the coprime-row hypothesis
-- * derived API: the reduced system witness `(D, b')` and the induced integral-point equivalence

section Lemma911

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean`: multiplying a square matrix by
a vector with prescribed head coordinate splits into the first-column contribution and the action
of the tail columns on the remaining coordinates. -/
lemma mulVec_cons_eq_smul_col_add_submatrix
    {R : Type*} [CommSemiring R] {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (t : R)
    (y : Fin k → R) :
    M *ᵥ Fin.cons t y =
      t • M.col 0 + (M.submatrix id Fin.succ) *ᵥ y := by
  -- Expand the head-tail decomposition of the input vector and collect the surviving summands.
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.submatrix_apply, Fin.sum_univ_succ,
    Pi.smul_apply, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean`: an integer vector lies on the
real hyperplane `integer_hyperplane α β` exactly when it solves the corresponding integer dot
equation. -/
lemma cast_mem_integer_hyperplane_iff
    {k : ℕ}
    (α : Fin (k + 1) → ℤ)
    (β : ℤ)
    (x : Fin (k + 1) → ℤ) :
    Int.cast ∘ x ∈ integer_hyperplane α (β : ℚ) ↔ α ⬝ᵥ x = β := by
  rw [mem_linear_hyperplane_iff]
  constructor
  · intro hx
    -- Reflect the real hyperplane equation back to `ℤ` through the integer cast.
    apply Int.cast_injective (α := ℝ)
    calc
      ((α ⬝ᵥ x : ℤ) : ℝ) = (Int.cast ∘ α) ⬝ᵥ (Int.cast ∘ x) := by
        exact RingHom.map_dotProduct (Int.castRingHom ℝ) α x
      _ = (β : ℝ) := hx
  · intro hx
    -- Cast the integer dot equation to recover the defining real hyperplane equality.
    calc
      (Int.cast ∘ α) ⬝ᵥ (Int.cast ∘ x) = ((α ⬝ᵥ x : ℤ) : ℝ) := by
        exact (RingHom.map_dotProduct (Int.castRingHom ℝ) α x).symm
      _ = (β : ℝ) := by exact_mod_cast hx

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean`: a primitive integer row has
coefficient gcd equal to `1` in the Chapter 1 normalization API. -/
lemma primitiveRowCoefficientGcd_eq_one
    {k : ℕ}
    {α : Fin (k + 1) → ℤ}
    (hprimitive : is_primitive_integer_vector α) :
    coefficientGcd α = 1 := by
  rcases hprimitive with ⟨_, hgcdOne⟩
  have hnatAbsDvd :
      Int.natAbs (coefficientGcd α) ∣
        Finset.univ.gcd (fun i : Fin (k + 1) ↦ Int.natAbs (α i)) := by
    -- The integer coefficient gcd divides every coordinate, hence its absolute value divides the
    -- gcd of the coordinate absolute values.
    refine Finset.dvd_gcd ?_
    intro i hi
    exact Int.natAbs_dvd_natAbs.mpr (coefficientGcd_dvd α i)
  have hnatAbsEqOne : Int.natAbs (coefficientGcd α) = 1 := by
    exact Nat.dvd_one.mp (by simpa [hgcdOne] using hnatAbsDvd)
  have hcoeffNonneg : 0 ≤ coefficientGcd α := by
    exact Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := α))
  -- The coefficient gcd is normalized to be nonnegative, so its absolute value determines it.
  calc
    coefficientGcd α = (Int.natAbs (coefficientGcd α) : ℤ) := by
      symm
      exact Int.natAbs_of_nonneg hcoeffNonneg
    _ = 1 := by exact_mod_cast hnatAbsEqOne

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean`: a primitive integer
hyperplane `α ⬝ᵥ x = β` is the affine image of `ℤ^k` under the inverse first column and inverse
tail columns of a unimodular completion of `α`. -/
lemma primitiveHyperplaneSolutionSet_eq_range_tailColumns
    {k : ℕ}
    (α : Fin (k + 1) → ℤ)
    (β : ℤ)
    (hprimitive : is_primitive_integer_vector α) :
    ∃ D : Matrix (Fin (k + 1)) (Fin k) ℤ, ∃ x₀ : Fin (k + 1) → ℤ,
      {x : Fin (k + 1) → ℤ | α ⬝ᵥ x = β} =
        Set.range (fun y : Fin k → ℤ ↦ x₀ + D *ᵥ y) := by
  have hcoeff : coefficientGcd α = 1 := primitiveRowCoefficientGcd_eq_one hprimitive
  obtain ⟨T, hTdet, hform⟩ := exists_unimodular_normalForm α
  have hdiv : coefficientGcd α ∣ β := by
    simp [hcoeff]
  let D : Matrix (Fin (k + 1)) (Fin k) ℤ := T.submatrix id Fin.succ
  let x₀ : Fin (k + 1) → ℤ := β • T.col 0
  refine ⟨D, x₀, ?_⟩
  -- Reuse the Chapter 1 solution-set parametrization and rewrite the normal-form vectors as an
  -- affine first-column plus tail-columns expression.
  simpa [hcoeff, D, x₀, mulVec_cons_eq_smul_col_add_submatrix] using
    (solutionSet_eq_range_insertNth α hprimitive.1 T hTdet hform β hdiv)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean`: translating a rational
polyhedron along the affine parametrization `x₀ + D *ᵥ y` converts membership to the reduced
system with matrix `A * D`. -/
lemma tailColumnsPolyhedronMembership_iff
    {k m : ℕ}
    (A : Matrix (Fin m) (Fin (k + 1)) ℚ)
    (b : Fin m → ℚ)
    (D : Matrix (Fin (k + 1)) (Fin k) ℤ)
    (x₀ : Fin (k + 1) → ℤ)
    (y : Fin k → ℤ) :
    Int.cast ∘ (x₀ + D *ᵥ y) ∈ rational_matrix_polyhedron A b ↔
      Int.cast ∘ y ∈
        rational_matrix_polyhedron
          (A * D.map (Int.castRingHom ℚ))
          (fun i ↦ b i - (A *ᵥ fun j ↦ (x₀ j : ℚ)) i) := by
  let x₀Q : Fin (k + 1) → ℚ := fun j ↦ (x₀ j : ℚ)
  let x₀R : Fin (k + 1) → ℝ := fun j ↦ (x₀ j : ℝ)
  let yR : Fin k → ℝ := fun j ↦ (y j : ℝ)
  have hparam :
      Int.cast ∘ (x₀ + D *ᵥ y) =
        x₀R + D.map (Int.castRingHom ℝ) *ᵥ yR := by
    -- Cast the affine integer parametrization coordinatewise to `ℝ`.
    funext j
    simp only [Function.comp_apply, x₀R, yR, Pi.add_apply, Int.cast_add, Int.coe_castRingHom]
    simpa using RingHom.map_mulVec (Int.castRingHom ℝ) D y j
  have hAcast :
      (A.map (Rat.castHom ℝ)) *ᵥ x₀R =
        (fun i ↦ ((A *ᵥ x₀Q) i : ℝ)) := by
    -- Casting the fixed integer offset commutes with applying the rational matrix.
    funext i
    exact (RingHom.map_mulVec (Rat.castHom ℝ) A x₀Q i).symm
  have hmapMul :
      A.map (Rat.castHom ℝ) * D.map (Int.castRingHom ℝ) =
        (A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) := by
    -- The two-stage cast `ℤ → ℚ → ℝ` is the same as the direct cast `ℤ → ℝ`.
    ext i j
    simp [Matrix.mul_apply]
  have hAparam :
      (A.map (Rat.castHom ℝ)) *ᵥ (Int.cast ∘ (x₀ + D *ᵥ y)) =
        (fun i ↦ ((A *ᵥ x₀Q) i : ℝ)) +
          ((A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ yR := by
    -- Separate the fixed translation part from the variable tail contribution.
    calc
      (A.map (Rat.castHom ℝ)) *ᵥ (Int.cast ∘ (x₀ + D *ᵥ y)) =
          (A.map (Rat.castHom ℝ)) *ᵥ (x₀R + D.map (Int.castRingHom ℝ) *ᵥ yR) := by
            rw [hparam]
      _ =
          (A.map (Rat.castHom ℝ)) *ᵥ x₀R +
            (A.map (Rat.castHom ℝ)) *ᵥ (D.map (Int.castRingHom ℝ) *ᵥ yR) := by
              rw [Matrix.mulVec_add]
      _ =
          (A.map (Rat.castHom ℝ)) *ᵥ x₀R +
            (A.map (Rat.castHom ℝ) * D.map (Int.castRingHom ℝ)) *ᵥ yR := by
              rw [Matrix.mulVec_mulVec]
      _ =
          (fun i ↦ ((A *ᵥ x₀Q) i : ℝ)) +
            (A.map (Rat.castHom ℝ) * D.map (Int.castRingHom ℝ)) *ᵥ yR := by
              rw [hAcast]
      _ =
          (fun i ↦ ((A *ᵥ x₀Q) i : ℝ)) +
            ((A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ yR := by
              rw [hmapMul]
  rw [mem_rational_matrix_polyhedron, mem_rational_matrix_polyhedron, hAparam]
  constructor
  · intro hx i
    have hxi := hx i
    -- Move the fixed translation term to the right-hand side.
    have hReduced :
        (((A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ yR) i ≤
          (b i : ℝ) - ((A *ᵥ x₀Q) i : ℝ) := by
      exact (le_sub_iff_add_le).2 (by
        simpa [add_comm, add_left_comm, add_assoc] using hxi)
    simpa [Rat.cast_sub, x₀Q, yR] using hReduced
  · intro hy i
    have hyi := hy i
    -- Reinsert the fixed translation term to recover the original inequality.
    have hyiReal :
        (((A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ yR) i ≤
          (b i : ℝ) - ((A *ᵥ x₀Q) i : ℝ) := by
      simpa [Rat.cast_sub, x₀Q, yR] using hyi
    have hyi' :
        (((A * D.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ yR) i +
            ((A *ᵥ x₀Q) i : ℝ) ≤
          (b i : ℝ) := by
      exact (le_sub_iff_add_le).1 hyiReal
    simpa [x₀Q, yR, add_comm, add_left_comm, add_assoc] using hyi'

/-- The source hypothesis that the entries of `α` are relatively prime upgrades the row to the
canonical Chapter 9 owner `is_primitive_integer_vector α`. -/
theorem is_primitive_integer_vector_of_span_eq_top
    (α : Fin n → ℤ)
    (hcoprime : (Ideal.span (Set.range α) : Ideal ℤ) = ⊤) :
    is_primitive_integer_vector α := by
  have hone : (1 : ℤ) ∈ Ideal.span (Set.range α) := by
    -- Unit-ideal generation says that `1` is an integer combination of the coordinates.
    rw [hcoprime]
    exact Submodule.mem_top
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  refine ⟨?_, ?_⟩
  · intro hzero
    -- A vanishing row cannot support a Bézout identity equal to `1`.
    simp [hzero] at hu
  · have hgcdDvdSum :
        ((Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (α i)) : ℕ) : ℤ) ∣
          ∑ i : Fin n, u i * α i := by
      -- The coordinate gcd divides each summand in the Bézout relation.
      refine Finset.dvd_sum ?_
      intro i hi
      refine dvd_mul_of_dvd_right ?_ (u i)
      apply Int.dvd_natAbs.1
      exact Int.natCast_dvd_natCast.mpr (Finset.gcd_dvd hi)
    have hgcdDvdOne :
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (α i)) ∣ 1 := by
      have hgcdDvdOneInt :
          ((Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (α i)) : ℕ) : ℤ) ∣ 1 := by
        simpa [hu] using hgcdDvdSum
      exact Int.natCast_dvd_natCast.mp hgcdDvdOneInt
    -- A natural number dividing `1` must itself be `1`.
    exact Nat.dvd_one.mp hgcdDvdOne

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_lemma_9_11.lean
Lemma 9.11. Let
`A ∈ ℚ^(m × n)`, `b ∈ ℚ^m`, `α ∈ ℤ^n`, and `β ∈ ℤ`, and assume that the
entries of `α` are relatively prime. Then there exist an integer matrix
`D ∈ ℤ^(n × (n - 1))` and a rational vector `b' ∈ ℚ^m` such that the system
`A x ≤ b, α x = β` has an integral solution if and only if the reduced system
`A D y ≤ b'` has an integral solution. This canonical owner theorem packages the row
hypothesis as `is_primitive_integer_vector α`. -/
theorem exists_hyperplane_elimination_system_of_primitive_integer_row
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (α : Fin n → ℤ)
    (β : ℤ)
    (hprimitive : is_primitive_integer_vector α) :
    ∃ D : Matrix (Fin n) (Fin (n - 1)) ℤ, ∃ b' : Fin m → ℚ,
      contains_integral_point
          (rational_matrix_polyhedron A b ∩ integer_hyperplane α (β : ℚ)) ↔
        contains_integral_point
          (rational_matrix_polyhedron (A * D.map (Int.castRingHom ℚ)) b') := by
  cases n with
  | zero =>
      exfalso
      -- Route correction: the zero-dimensional case is impossible because a primitive row is
      -- nonzero, while every `Fin 0 → ℤ` vector vanishes.
      apply hprimitive.1
      funext i
      exact Fin.elim0 i
  | succ k =>
      rcases primitiveHyperplaneSolutionSet_eq_range_tailColumns α β hprimitive with
        ⟨D, x₀, hsolution⟩
      let b' : Fin m → ℚ := fun i ↦ b i - (A *ᵥ fun j ↦ (x₀ j : ℚ)) i
      refine ⟨D, b', ?_⟩
      rw [contains_integral_point_iff, contains_integral_point_iff]
      constructor
      · rintro ⟨x, hx⟩
        rcases hx with ⟨hxPoly, hxHyperplane⟩
        have hxEq : α ⬝ᵥ x = β := (cast_mem_integer_hyperplane_iff α β x).1 hxHyperplane
        have hxSolution : x ∈ Set.range (fun y : Fin k → ℤ ↦ x₀ + D *ᵥ y) := by
          -- Convert the hyperplane equation into the affine parametrization witness.
          rw [← hsolution]
          exact hxEq
        rcases hxSolution with ⟨y, hy⟩
        refine ⟨y, ?_⟩
        have hxParam :
            Int.cast ∘ (x₀ + D *ᵥ y) ∈ rational_matrix_polyhedron A b := by
          simpa [hy] using hxPoly
        -- Transport the original polyhedron membership through the affine parametrization.
        exact (tailColumnsPolyhedronMembership_iff A b D x₀ y).1 hxParam
      · rintro ⟨y, hyPoly⟩
        refine ⟨x₀ + D *ᵥ y, ?_⟩
        constructor
        · -- Recover membership in the original polyhedron by undoing the translated system.
          exact (tailColumnsPolyhedronMembership_iff A b D x₀ y).2 hyPoly
        · have hxEq : α ⬝ᵥ (x₀ + D *ᵥ y) = β := by
            -- The affine parametrization lands exactly in the integer hyperplane.
            have hxEqSet :
                x₀ + D *ᵥ y ∈ {x : Fin (k + 1) → ℤ | α ⬝ᵥ x = β} := by
              rw [hsolution]
              exact ⟨y, rfl⟩
            exact hxEqSet
          exact (cast_mem_integer_hyperplane_iff α β (x₀ + D *ᵥ y)).2 hxEq

/-- Source-facing bridge for Lemma 9.11, restating the primitive-row owner theorem with the
coprime-row hypothesis `Ideal.span (Set.range α) = ⊤`. -/
theorem exists_hyperplane_elimination_system_of_coprime_integer_row
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (α : Fin n → ℤ)
    (β : ℤ)
    (hcoprime : (Ideal.span (Set.range α) : Ideal ℤ) = ⊤) :
    ∃ D : Matrix (Fin n) (Fin (n - 1)) ℤ, ∃ b' : Fin m → ℚ,
      contains_integral_point
          (rational_matrix_polyhedron A b ∩ integer_hyperplane α (β : ℚ)) ↔
        contains_integral_point
          (rational_matrix_polyhedron (A * D.map (Int.castRingHom ℚ)) b') := by
  simpa using
    exists_hyperplane_elimination_system_of_primitive_integer_row
      A b α β (is_primitive_integer_vector_of_span_eq_top α hcoprime)

end Lemma911
