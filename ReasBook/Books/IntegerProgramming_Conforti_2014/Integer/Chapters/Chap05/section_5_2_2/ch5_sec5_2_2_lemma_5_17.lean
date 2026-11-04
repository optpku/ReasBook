/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_1.ch5_sec5_2_1_theorem_5_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import Mathlib.Analysis.Convex.Exposed

open scoped BigOperators Matrix

section Lemma517

variable {n : ℕ}

/-- Helper for Lemma 5.17: one pure-integer Chvátal closure step stays inside the ambient set. -/
lemma pureIntegerChvatalClosure_subset
    (P : Set (Fin n → ℝ)) :
    pure_integer_chvatal_closure P ⊆ P := by
  intro x hx
  -- The closure predicate records ambient membership as its first field.
  exact (mem_pure_integer_chvatal_closure_iff.mp hx).1

/-- Helper for Lemma 5.17: every iterate of the pure-integer Chvátal closure stays inside the
initial set. -/
lemma iteratePureIntegerChvatalClosure_subset
    (P : Set (Fin n → ℝ)) :
    ∀ s : ℕ, (pure_integer_chvatal_closure^[s]) P ⊆ P
  | 0 => by
      intro x hx
      simpa using hx
  | s + 1 => by
      intro x hx
      -- First drop one closure step, then apply the induction hypothesis.
      rw [Function.iterate_succ_apply] at hx
      exact pureIntegerChvatalClosure_subset P
        (iteratePureIntegerChvatalClosure_subset (pure_integer_chvatal_closure P) s hx)

/-- Helper for Lemma 5.17: every iterate of the pure-integer Chvátal closure of `∅` is `∅`. -/
lemma iteratePureIntegerChvatalClosure_empty
    (s : ℕ) :
    (pure_integer_chvatal_closure^[s]) (∅ : Set (Fin n → ℝ)) = ∅ := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      have hClosureEmpty : pure_integer_chvatal_closure (∅ : Set (Fin n → ℝ)) = ∅ := by
        ext x
        -- Membership in the closure of `∅` is impossible because ambient membership already fails.
        rw [mem_pure_integer_chvatal_closure_iff]
        simp
      rw [Function.iterate_succ_apply, hClosureEmpty]
      exact ih

/-- Helper for Lemma 5.17: restricting an exposed equality face along a subset is the equality
face of the restricted ambient set. -/
lemma inter_faceSet_eq_faceSet_of_subset
    {P Q : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hQP : Q ⊆ P) :
    Q ∩ face_set P c δ = face_set Q c δ := by
  ext x
  rw [Set.mem_inter_iff, mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hxQ, hxFace⟩
    exact ⟨hxQ, hxFace.2⟩
  · rintro ⟨hxQ, hxEq⟩
    exact ⟨hxQ, ⟨hQP hxQ, hxEq⟩⟩

/-- Helper for Lemma 5.17: a valid inequality on `P` remains valid on every subset `Q ⊆ P`. -/
lemma isValidInequality_of_subset
    {P Q : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hQP : Q ⊆ P)
    (hvalid : is_valid_inequality P c δ) :
    is_valid_inequality Q c δ := by
  intro x hxQ
  exact hvalid (hQP hxQ)

/-- Helper for Lemma 5.17: the intersection of a subset `Q ⊆ P` with an exposed equality face of
`P` is an exposed equality face of `Q`. -/
lemma isExposed_inter_faceSet_of_subset
    {P Q : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hQP : Q ⊆ P)
    (hvalid : is_valid_inequality P c δ) :
    IsExposed ℝ Q (Q ∩ face_set P c δ) := by
  have hvalidQ : is_valid_inequality Q c δ :=
    isValidInequality_of_subset hQP hvalid
  -- Rewrite the restricted face into the canonical `face_set` owner on `Q`.
  rw [inter_faceSet_eq_faceSet_of_subset hQP]
  exact isExposed_face_set_of_valid_inequality hvalidQ

/-- Helper for Lemma 5.17: taking fractional parts of a real multiplier subtracts the integral
floor combination of the integral rows. -/
lemma fractVecMul_eq_sub_floorVecMul
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (u : Fin m → ℝ) :
    (fun i ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ)) =
      fun j ↦
        (u ᵥ* (A.map (Int.castRingHom ℝ))) j -
          (((fun i ↦ Int.floor (u i)) ᵥ* A) j : ℝ) := by
  funext j
  -- Expand the row product coordinatewise and split each coefficient into fractional and floor
  -- parts.
  calc
    ((fun i ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j
        = ∑ i : Fin m, Int.fract (u i) * (A i j : ℝ) := by
            simp [Matrix.vecMul, dotProduct]
    _ = ∑ i : Fin m, (u i - Int.floor (u i)) * (A i j : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Int.self_sub_floor]
    _ = ∑ i : Fin m, (u i * (A i j : ℝ) - (Int.floor (u i) : ℝ) * (A i j : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (∑ i : Fin m, u i * (A i j : ℝ)) - ∑ i : Fin m, (Int.floor (u i) : ℝ) * (A i j : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = (u ᵥ* (A.map (Int.castRingHom ℝ))) j - (((fun i ↦ Int.floor (u i)) ᵥ* A) j : ℝ) := by
          simp [Matrix.vecMul, dotProduct]

/-- Helper for Lemma 5.17: taking fractional parts of a real multiplier subtracts the integral
floor combination on the right-hand side. -/
lemma fractDot_eq_sub_floorDot
    {m : ℕ}
    (b : Fin m → ℤ)
    (u : Fin m → ℝ) :
    (fun i ↦ Int.fract (u i)) ⬝ᵥ (fun i ↦ (b i : ℝ)) =
      u ⬝ᵥ (fun i ↦ (b i : ℝ)) - (((fun i ↦ Int.floor (u i)) ⬝ᵥ b : ℤ) : ℝ) := by
  -- The scalar case is the same floor/fract decomposition used for row products.
  calc
    (fun i ↦ Int.fract (u i)) ⬝ᵥ (fun i ↦ (b i : ℝ))
        = ∑ i : Fin m, Int.fract (u i) * (b i : ℝ) := by
            simp [dotProduct]
    _ = ∑ i : Fin m, (u i - Int.floor (u i)) * (b i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Int.self_sub_floor]
    _ = ∑ i : Fin m, (u i * (b i : ℝ) - (Int.floor (u i) : ℝ) * (b i : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (∑ i : Fin m, u i * (b i : ℝ)) - ∑ i : Fin m, (Int.floor (u i) : ℝ) * (b i : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = u ⬝ᵥ (fun i ↦ (b i : ℝ)) - (((fun i ↦ Int.floor (u i)) ⬝ᵥ b : ℤ) : ℝ) := by
          simp [dotProduct]

/-- Helper for Lemma 5.17: the common denominator of a rational vector is nonzero. -/
lemma rationalVectorCommonDenominator_ne_zero
    {k : ℕ}
    (v : Fin k → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Every coordinate denominator is positive, so the finite lcm is also positive.
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin k)), (v i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  simpa [rational_vector_common_denominator] using
    (Finset.lcm_ne_zero_iff.2 hden)

/-- Helper for Lemma 5.17: clearing denominators in a rational vector agrees with scaling by the
common denominator after casting to `ℝ`. -/
lemma commonDenominatorScaledVector_eq_smul_real
    {k : ℕ}
    (v : Fin k → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  funext i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
      (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  have hi :
      ((common_denominator_scaled_vector v i : ℤ) : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul v) i
  exact_mod_cast hi

/-- Helper for Lemma 5.17: every rational matrix presentation can be rewritten as one integral
system by clearing denominators rowwise in the augmented rows `(A i, b i)`. -/
lemma exists_eq_integralPolyhedron_of_rationalMatrixPolyhedron
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ Aint : Matrix (Fin m) (Fin n) ℤ, ∃ bint : Fin m → ℤ,
      rational_matrix_polyhedron A b =
        polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
  let augmentedRow : Fin m → Fin (n + 1) → ℚ :=
    fun i ↦ Fin.append (A i) (fun _ ↦ b i)
  let rowDen : Fin m → ℕ := fun i ↦ rational_vector_common_denominator (augmentedRow i)
  let Aint : Matrix (Fin m) (Fin n) ℤ :=
    fun i j ↦ common_denominator_scaled_vector (augmentedRow i) (Fin.castAdd 1 j)
  let bint : Fin m → ℤ :=
    fun i ↦ common_denominator_scaled_vector (augmentedRow i) (Fin.natAdd n 0)
  refine ⟨Aint, bint, ?_⟩
  ext x
  rw [mem_rational_matrix_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx i
    have hden_ne_zero : rowDen i ≠ 0 :=
      rationalVectorCommonDenominator_ne_zero (v := augmentedRow i)
    have hden_pos : 0 < (rowDen i : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hden_ne_zero
    have hrowScaled :
        (fun j ↦ (Aint i j : ℝ)) = (rowDen i : ℝ) • fun j ↦ (A i j : ℝ) := by
      funext j
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.castAdd 1 j)
      simpa [Aint, augmentedRow] using hscaled
    have hrhsScaled :
        (bint i : ℝ) = (rowDen i : ℝ) * (b i : ℝ) := by
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.natAdd n 0)
      simpa [bint, augmentedRow] using hscaled
    have hmulScaled :
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i =
          (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
      calc
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
            = (fun j ↦ (Aint i j : ℝ)) ⬝ᵥ x := by
                simp [Matrix.mulVec]
        _ = ((rowDen i : ℝ) • fun j ↦ (A i j : ℝ)) ⬝ᵥ x := by
              rw [hrowScaled]
        _ = (rowDen i : ℝ) * ((fun j ↦ (A i j : ℝ)) ⬝ᵥ x) := by
              simp [dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc]
        _ = (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
              simp [Matrix.mulVec]
    change ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ (bint i : ℝ)
    rw [hmulScaled, hrhsScaled]
    exact mul_le_mul_of_nonneg_left (hx i) hden_pos.le
  · intro hx i
    have hden_ne_zero : rowDen i ≠ 0 :=
      rationalVectorCommonDenominator_ne_zero (v := augmentedRow i)
    have hden_pos : 0 < (rowDen i : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hden_ne_zero
    have hrowScaled :
        (fun j ↦ (Aint i j : ℝ)) = (rowDen i : ℝ) • fun j ↦ (A i j : ℝ) := by
      funext j
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.castAdd 1 j)
      simpa [Aint, augmentedRow] using hscaled
    have hrhsScaled :
        (bint i : ℝ) = (rowDen i : ℝ) * (b i : ℝ) := by
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.natAdd n 0)
      simpa [bint, augmentedRow] using hscaled
    have hmulScaled :
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i =
          (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
      calc
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
            = (fun j ↦ (Aint i j : ℝ)) ⬝ᵥ x := by
                simp [Matrix.mulVec]
        _ = ((rowDen i : ℝ) • fun j ↦ (A i j : ℝ)) ⬝ᵥ x := by
              rw [hrowScaled]
        _ = (rowDen i : ℝ) * ((fun j ↦ (A i j : ℝ)) ⬝ᵥ x) := by
              simp [dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc]
        _ = (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
              simp [Matrix.mulVec]
    have hscaledLe : (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) ≤
        (rowDen i : ℝ) * (b i : ℝ) := by
      have hx' : ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ (bint i : ℝ) := by
        exact hx i
      rw [hmulScaled, hrhsScaled] at hx'
      exact hx'
    nlinarith

/-- Helper for Lemma 5.17: one pure-integer Chvátal step commutes with active-constraint faces of
an integral system. -/
lemma pureIntegerChvatalClosure_eq_inter_of_activeConstraintFace
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (I : Set (Fin m)) :
    pure_integer_chvatal_closure
        (active_constraint_face (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) I) =
      pure_integer_chvatal_closure
          (polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ))) ∩
        active_constraint_face (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) I := by
  classical
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  let bReal : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let Aaux : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix AReal I
  let baux : Fin (m + m) → ℝ := activeConstraintFaceRhs bReal I
  have hFaceEq :
      active_constraint_face AReal bReal I = polyhedron_le_set Aaux baux := by
    simpa [AReal, bReal, Aaux, baux] using active_constraint_face_eq_polyhedronAux AReal bReal I
  have hAmbientClosure :
      pure_integer_chvatal_closure (polyhedron_le_set AReal bReal) =
        chvatalClosure AReal bReal Finset.univ :=
    pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set AReal bReal
  have hFaceClosure :
      pure_integer_chvatal_closure (active_constraint_face AReal bReal I) =
        chvatalClosure Aaux baux Finset.univ := by
    rw [hFaceEq]
    exact pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set Aaux baux
  ext x
  rw [hFaceClosure, hAmbientClosure, Set.mem_inter_iff, mem_chvatalClosure_iff, mem_chvatalClosure_iff]
  constructor
  · intro hx
    have hxFace : x ∈ active_constraint_face AReal bReal I := by
      simpa [hFaceEq] using hx.1
    refine ⟨?_, hxFace⟩
    refine ⟨mem_polyhedron_of_mem_active_constraint_face hxFace, ?_⟩
    intro v hv
    let uLift : Fin (m + m) → ℝ := Fin.append v (fun _ : Fin m ↦ 0)
    have huLiftCast : ∀ i : Fin m, uLift (Fin.castAdd m i) = v i := by
      intro i
      simpa [uLift] using (Fin.append_left v (fun _ : Fin m ↦ 0) i)
    have huLiftNat : ∀ i : Fin m, uLift (Fin.natAdd m i) = 0 := by
      intro i
      simpa [uLift] using (Fin.append_right v (fun _ : Fin m ↦ 0) i)
    have huLiftRow : uLift ᵥ* Aaux = v ᵥ* AReal := by
      funext j
      calc
        (uLift ᵥ* Aaux) j
            = ∑ i : Fin m, uLift (Fin.castAdd m i) * AReal i j +
                ∑ i : Fin m, uLift (Fin.natAdd m i) * Aaux (Fin.natAdd m i) j := by
                  simp [Aaux, Matrix.vecMul, dotProduct, Fin.sum_univ_add,
                    activeConstraintFaceMatrix_castAdd]
        _ = ∑ i : Fin m, v i * AReal i j + ∑ i : Fin m, 0 := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro i hi
                rw [huLiftCast i]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                rw [huLiftNat i]
                simp
        _ = (v ᵥ* AReal) j := by
              simp [Matrix.vecMul, dotProduct]
    have huLiftRhs : uLift ⬝ᵥ baux = v ⬝ᵥ bReal := by
      calc
        uLift ⬝ᵥ baux
            = ∑ i : Fin m, uLift (Fin.castAdd m i) * bReal i +
                ∑ i : Fin m, uLift (Fin.natAdd m i) * baux (Fin.natAdd m i) := by
                  simp [baux, dotProduct, Fin.sum_univ_add, activeConstraintFaceRhs_castAdd]
        _ = ∑ i : Fin m, v i * bReal i + ∑ i : Fin m, 0 := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro i hi
                rw [huLiftCast i]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                rw [huLiftNat i]
                simp
        _ = v ⬝ᵥ bReal := by
              simp [dotProduct]
    have huLift : IsChvatalMultiplier Aaux Finset.univ uLift := by
      rw [isChvatalMultiplier_univ_iff] at hv ⊢
      constructor
      · intro p
        refine Fin.addCases ?_ ?_ p
        · intro i
          simpa [huLiftCast i] using hv.1 i
        · intro i
          rw [huLiftNat i]
      · intro j
        rcases hv.2 j with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        simpa [huLiftRow] using hz
    -- Every ambient Chvátal cut is already one of the auxiliary face-system cuts.
    simpa [huLiftRow, huLiftRhs] using hx.2 uLift huLift
  · rintro ⟨hxAmbient, hxFace⟩
    refine ⟨?_, ?_⟩
    · rw [← hFaceEq]
      exact hxFace
    intro u hu
    rw [isChvatalMultiplier_univ_iff] at hu
    let yPrime : Fin m → ℝ := fun i ↦ if i ∈ I then 0 else u (Fin.castAdd m i)
    let yDouble : Fin m → ℝ := fun i ↦
      if i ∈ I then u (Fin.castAdd m i) - u (Fin.natAdd m i) else 0
    let uFrac : Fin m → ℝ := fun i ↦ Int.fract (yDouble i)
    let uCorr : Fin m → ℝ := yPrime + uFrac
    let w : Fin m → ℤ := fun i ↦ Int.floor (yDouble i)
    have hxFaceEq :
        ∀ i : Fin m, i ∈ I → (AReal *ᵥ x) i = bReal i :=
      (mem_active_constraint_face_iff.mp hxFace).1
    have hyDouble_zero : ∀ i : Fin m, i ∉ I → yDouble i = 0 := by
      intro i hi
      simp [yDouble, hi]
    have hw_zero : ∀ i : Fin m, i ∉ I → w i = 0 := by
      intro i hi
      simp [w, hyDouble_zero i hi]
    have huSplitRow :
        u ᵥ* Aaux = yPrime ᵥ* AReal + yDouble ᵥ* AReal := by
      funext j
      -- Split the auxiliary multiplier into the inactive ambient part and the signed active part.
      calc
        (u ᵥ* Aaux) j
            = ∑ i : Fin m, u (Fin.castAdd m i) * AReal i j +
                ∑ i : Fin m, u (Fin.natAdd m i) * Aaux (Fin.natAdd m i) j := by
                  simp [Aaux, activeConstraintFaceMatrix, Matrix.vecMul, dotProduct,
                    Fin.sum_univ_add]
        _ = ∑ i : Fin m,
              (u (Fin.castAdd m i) * AReal i j + u (Fin.natAdd m i) * Aaux (Fin.natAdd m i) j) := by
              rw [← Finset.sum_add_distrib]
        _ = ∑ i : Fin m, (yPrime i * AReal i j + yDouble i * AReal i j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hiI : i ∈ I
              · rw [show Aaux (Fin.natAdd m i) = -AReal i by
                      simpa [Aaux] using activeConstraintFaceMatrix_natAdd_of_mem AReal I i hiI]
                simp [yPrime, yDouble, hiI]
                ring_nf
              · rw [show Aaux (Fin.natAdd m i) = 0 by
                      simpa [Aaux] using activeConstraintFaceMatrix_natAdd_of_not_mem AReal I i hiI]
                simp [yPrime, yDouble, hiI]
        _ = (yPrime ᵥ* AReal) j + (yDouble ᵥ* AReal) j := by
              simp [Matrix.vecMul, dotProduct, Finset.sum_add_distrib]
    have huSplitRhs :
        u ⬝ᵥ baux = yPrime ⬝ᵥ bReal + yDouble ⬝ᵥ bReal := by
      -- The same block split applies to the right-hand side.
      calc
        u ⬝ᵥ baux
            = ∑ i : Fin m, u (Fin.castAdd m i) * bReal i +
                ∑ i : Fin m, u (Fin.natAdd m i) * baux (Fin.natAdd m i) := by
                  simp [baux, activeConstraintFaceRhs, dotProduct, Fin.sum_univ_add]
        _ = ∑ i : Fin m,
              (u (Fin.castAdd m i) * bReal i + u (Fin.natAdd m i) * baux (Fin.natAdd m i)) := by
              rw [← Finset.sum_add_distrib]
        _ = ∑ i : Fin m, (yPrime i * bReal i + yDouble i * bReal i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hiI : i ∈ I
              · rw [show baux (Fin.natAdd m i) = -bReal i by
                      simpa [baux] using activeConstraintFaceRhs_natAdd_of_mem bReal I i hiI]
                simp [yPrime, yDouble, hiI]
                ring_nf
              · rw [show baux (Fin.natAdd m i) = 0 by
                      simpa [baux] using activeConstraintFaceRhs_natAdd_of_not_mem bReal I i hiI]
                simp [yPrime, yDouble, hiI]
        _ = yPrime ⬝ᵥ bReal + yDouble ⬝ᵥ bReal := by
              simp [dotProduct, Finset.sum_add_distrib]
    have huCorr_nonneg : ∀ i : Fin m, 0 ≤ uCorr i := by
      intro i
      by_cases hi : i ∈ I
      · simp [uCorr, yPrime, uFrac, hi, Int.fract_nonneg]
      · have huCast : 0 ≤ u (Fin.castAdd m i) := hu.1 (Fin.castAdd m i)
        simp [uCorr, yPrime, yDouble, uFrac, hi, huCast]
    have huCorrRow :
        uCorr ᵥ* AReal = u ᵥ* Aaux - fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ) := by
      -- Route correction: keep the corrected multiplier at the ambient matrix owner and separate
      -- the integer floor shift as one explicit row correction.
      calc
        uCorr ᵥ* AReal = yPrime ᵥ* AReal + uFrac ᵥ* AReal := by
          rw [show uCorr = yPrime + uFrac by rfl, Matrix.add_vecMul]
        _ = yPrime ᵥ* AReal +
              (yDouble ᵥ* AReal - fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ)) := by
              simpa [uFrac, w] using fractVecMul_eq_sub_floorVecMul A yDouble
        _ = (yPrime ᵥ* AReal + yDouble ᵥ* AReal) - fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ) := by
              funext j
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = u ᵥ* Aaux - fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ) := by
              rw [huSplitRow]
    have huCorrRhs :
        uCorr ⬝ᵥ bReal = u ⬝ᵥ baux - ((w ⬝ᵥ b : ℤ) : ℝ) := by
      calc
        uCorr ⬝ᵥ bReal = yPrime ⬝ᵥ bReal + uFrac ⬝ᵥ bReal := by
          rw [show uCorr = yPrime + uFrac by rfl, add_dotProduct]
        _ = yPrime ⬝ᵥ bReal + (yDouble ⬝ᵥ bReal - ((w ⬝ᵥ b : ℤ) : ℝ)) := by
              simpa [uFrac, w] using fractDot_eq_sub_floorDot b yDouble
        _ = (yPrime ⬝ᵥ bReal + yDouble ⬝ᵥ bReal) - ((w ⬝ᵥ b : ℤ) : ℝ) := by
              ring
        _ = u ⬝ᵥ baux - ((w ⬝ᵥ b : ℤ) : ℝ) := by
              rw [huSplitRhs]
    have huCorrInt : ∀ j : Fin n, ∃ z : ℤ, (uCorr ᵥ* AReal) j = (z : ℝ) := by
      intro j
      rcases hu.2 j with ⟨z, hz⟩
      refine ⟨z - (w ᵥ* A) j, ?_⟩
      have hcoord := congrFun huCorrRow j
      calc
        (uCorr ᵥ* AReal) j
            = (u ᵥ* Aaux) j - (((w ᵥ* A) j : ℤ) : ℝ) := by
                simpa using hcoord
        _ = (z : ℝ) - (((w ᵥ* A) j : ℤ) : ℝ) := by rw [hz]
        _ = ((z - (w ᵥ* A) j : ℤ) : ℝ) := by simp
    have huCorr : IsChvatalMultiplier AReal Finset.univ uCorr := by
      rw [isChvatalMultiplier_univ_iff]
      exact ⟨huCorr_nonneg, huCorrInt⟩
    have hShiftEval :
        (fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ)) ⬝ᵥ x = ((w ⬝ᵥ b : ℤ) : ℝ) := by
      -- The floor-shift row is supported on the active indices, so it evaluates to the same
      -- integer combination of the active right-hand sides on every point of the face.
      calc
        (fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ)) ⬝ᵥ x
            = ((fun i ↦ (w i : ℝ)) ᵥ* AReal) ⬝ᵥ x := by
                congr 1
                funext j
                simp [AReal, Matrix.vecMul, dotProduct]
        _ = (fun i ↦ (w i : ℝ)) ⬝ᵥ (AReal *ᵥ x) := by
              rw [Matrix.dotProduct_mulVec]
        _ = (fun i ↦ (w i : ℝ)) ⬝ᵥ bReal := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hiI : i ∈ I
              · rw [hxFaceEq i hiI]
              · have hwi : w i = 0 := hw_zero i hiI
                simp [hwi]
        _ = ((w ⬝ᵥ b : ℤ) : ℝ) := by
              simp [bReal, dotProduct]
    have huCorrEval :
        (uCorr ᵥ* AReal) ⬝ᵥ x = (u ᵥ* Aaux) ⬝ᵥ x - ((w ⬝ᵥ b : ℤ) : ℝ) := by
      calc
        (uCorr ᵥ* AReal) ⬝ᵥ x
            = (u ᵥ* Aaux - fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ)) ⬝ᵥ x := by
                rw [huCorrRow]
        _ = (u ᵥ* Aaux) ⬝ᵥ x - (fun j ↦ (((w ᵥ* A) j : ℤ) : ℝ)) ⬝ᵥ x := by
              rw [sub_dotProduct]
        _ = (u ᵥ* Aaux) ⬝ᵥ x - ((w ⬝ᵥ b : ℤ) : ℝ) := by
              rw [hShiftEval]
    have hFloorCorr :
        (((⌊uCorr ⬝ᵥ bReal⌋ : ℤ) : ℝ)) =
          ((⌊u ⬝ᵥ baux⌋ : ℤ) : ℝ) - ((w ⬝ᵥ b : ℤ) : ℝ) := by
      rw [huCorrRhs]
      calc
        (((⌊u ⬝ᵥ baux - ((w ⬝ᵥ b : ℤ) : ℝ)⌋ : ℤ) : ℝ))
            = (((Int.floor (u ⬝ᵥ baux) - (w ⬝ᵥ b)) : ℤ) : ℝ) := by
                exact_mod_cast (Int.floor_sub_intCast (u ⬝ᵥ baux) (w ⬝ᵥ b))
        _ = ((⌊u ⬝ᵥ baux⌋ : ℤ) : ℝ) - ((w ⬝ᵥ b : ℤ) : ℝ) := by
              simp
    have hCorrectedCut :
        (u ᵥ* Aaux) ⬝ᵥ x - ((w ⬝ᵥ b : ℤ) : ℝ) ≤
          ((⌊u ⬝ᵥ baux⌋ : ℤ) : ℝ) - ((w ⬝ᵥ b : ℤ) : ℝ) := by
      calc
        (u ᵥ* Aaux) ⬝ᵥ x - ((w ⬝ᵥ b : ℤ) : ℝ)
            = (uCorr ᵥ* AReal) ⬝ᵥ x := by
                rw [huCorrEval]
        _ ≤ ((⌊uCorr ⬝ᵥ bReal⌋ : ℤ) : ℝ) := hxAmbient.2 uCorr huCorr
        _ = ((⌊u ⬝ᵥ baux⌋ : ℤ) : ℝ) - ((w ⬝ᵥ b : ℤ) : ℝ) := hFloorCorr
    -- The corrected ambient cut implies the original auxiliary cut after canceling the same
    -- integer floor shift on both sides.
    linarith

/-- Helper for Lemma 5.17: one pure-integer Chvátal step commutes with restricting a rational
polyhedron to an exposed face. -/
lemma pureIntegerChvatalClosure_eq_inter_of_exposedFace_once
    (P F : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P)
    (hF_face : IsExposed ℝ P F) :
    pure_integer_chvatal_closure F =
      pure_integer_chvatal_closure P ∩ F := by
  by_cases hF_empty : F = ∅
  · -- The empty-face case is immediate because the closure predicate keeps ambient membership.
    rw [hF_empty]
    ext x
    rw [mem_pure_integer_chvatal_closure_iff]
    simp
  · have hF_nonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_empty
    rcases hP_rational with ⟨m, A, b, hP_eq⟩
    obtain ⟨Aint, bint, hIntegralEq⟩ :=
      exists_eq_integralPolyhedron_of_rationalMatrixPolyhedron A b
    have hPIntegral :
        P =
          polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
      rw [hP_eq]
      simpa [rational_matrix_polyhedron] using hIntegralEq
    have hFIntegral :
        IsExposed ℝ
          (polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)))
          F := by
      simpa [hPIntegral] using hF_face
    obtain ⟨I, hI⟩ :=
      exists_eq_active_constraint_face_of_isExposed
        (Aint.map (Int.castRingHom ℝ))
        (fun i ↦ (bint i : ℝ))
        F
        hFIntegral
        hF_nonempty
    -- Route correction: normalize the rational presentation first, then apply the active-face
    -- one-step lemma on the resulting integral system.
    simpa [hPIntegral, hI] using
      pureIntegerChvatalClosure_eq_inter_of_activeConstraintFace Aint bint I

/-- Helper for Lemma 5.17: every iterate of the pure-integer Chvátal closure of a rational
polyhedron is again rational. -/
lemma iteratePureIntegerChvatalClosure_isRational
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∀ s : ℕ, is_rational_polyhedron ((pure_integer_chvatal_closure^[s]) P) := by
  intro s
  induction s with
  | zero =>
      simpa using hP_rational
  | succ s ih =>
      rcases ih with ⟨m, A, b, hIterEq⟩
      obtain ⟨Aint, bint, hIntegralEq⟩ :=
        exists_eq_integralPolyhedron_of_rationalMatrixPolyhedron A b
      have hIterIntegral :
          (pure_integer_chvatal_closure^[s]) P =
            polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
        rw [hIterEq]
        simpa [rational_matrix_polyhedron] using hIntegralEq
      -- Normalize the current iterate to an integral system before invoking Theorem 5.14.
      rw [Function.iterate_succ_apply']
      rw [hIterIntegral]
      exact chvatalClosure_is_rational_polyhedron Aint bint

/-- Lemma 5.17. Let `P` be a rational polyhedron and `F` a face of `P`. On the canonical
Chapter 3 face owner this means `IsExposed ℝ P F`. The source states `F` is nonempty, but this is
redundant here: when `F = ∅`, both sides are `∅`. Then `F^(s) = P^(s) ∩ F` for every iterate
index `s`, where the textbook notation `Q^(s)` is represented by
`(pure_integer_chvatal_closure^[s]) Q`. -/
theorem iterate_chvatalClosure_eq_inter_of_exposed_face
    (P F : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P)
    (hF_face : IsExposed ℝ P F)
    (s : ℕ) :
    (pure_integer_chvatal_closure^[s]) F =
      (pure_integer_chvatal_closure^[s]) P ∩ F := by
  induction s generalizing P F with
  | zero =>
      ext x
      constructor
      · intro hx
        exact ⟨hF_face.subset hx, hx⟩
      · intro hx
        exact hx.2
  | succ s ih =>
      by_cases hF_empty : F = ∅
      · -- The empty-face case is trivial because every iterate of `∅` is still `∅`.
        have hClosureEmpty : pure_integer_chvatal_closure (∅ : Set (Fin n → ℝ)) = ∅ := by
          ext x
          rw [mem_pure_integer_chvatal_closure_iff]
          simp
        rw [hF_empty, Function.iterate_succ_apply, hClosureEmpty,
          iteratePureIntegerChvatalClosure_empty]
        simp
      · have hF_nonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_empty
        obtain ⟨c, δ, hvalid, hF_eq⟩ := hF_face.exists_eq_face_set_of_nonempty hF_nonempty
        let Q : Set (Fin n → ℝ) := pure_integer_chvatal_closure P
        have hQ_rational : is_rational_polyhedron Q := by
          simpa [Q, Function.iterate_succ_apply] using
            iteratePureIntegerChvatalClosure_isRational P hP_rational 1
        have hQ_subset : Q ⊆ P := pureIntegerChvatalClosure_subset P
        have hQ_face : IsExposed ℝ Q (Q ∩ F) := by
          -- Keep the exposing inequality fixed and restrict only the ambient set.
          rw [hF_eq]
          exact isExposed_inter_faceSet_of_subset hQ_subset hvalid
        have hOneStep :
            pure_integer_chvatal_closure F =
              pure_integer_chvatal_closure P ∩ F :=
          pureIntegerChvatalClosure_eq_inter_of_exposedFace_once
            P F hP_rational hF_face
        calc
          (pure_integer_chvatal_closure^[s + 1]) F
              = (pure_integer_chvatal_closure^[s]) (pure_integer_chvatal_closure F) := by
                  rw [Function.iterate_succ_apply]
          _ = (pure_integer_chvatal_closure^[s]) (Q ∩ F) := by
                simpa [Q] using congrArg (pure_integer_chvatal_closure^[s]) hOneStep
          _ = (pure_integer_chvatal_closure^[s]) Q ∩ (Q ∩ F) := by
                exact ih Q (Q ∩ F) hQ_rational hQ_face
          _ = (pure_integer_chvatal_closure^[s]) Q ∩ F := by
                ext x
                constructor
                · rintro ⟨hxCut, hxFace⟩
                  exact ⟨hxCut, hxFace.2⟩
                · intro hx
                  exact ⟨hx.1, iteratePureIntegerChvatalClosure_subset Q s hx.1, hx.2⟩
          _ = (pure_integer_chvatal_closure^[s + 1]) P ∩ F := by
                simp [Q, Function.iterate_succ_apply]

end Lemma517
