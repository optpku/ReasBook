import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30.Decomposition
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_definition_4_9_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_32
import Mathlib.Analysis.Convex.KreinMilman

open scoped BigOperators Matrix MixedIntegerNotation Pointwise

-- Semantic recall note: Exercise 4.33 reuses the chapter's canonical mixed-integer linear
-- representability owner on the flattened mixed-space image, instead of keeping a second local
-- owner for the same construction.

/-- Helper for Exercise 4.33: the auxiliary integer-variable matrix keeps the original
`C z` block on the genuine auxiliary integers and adds `±Id` rows tying a copied visible
integer block to the first visible coordinates. -/
private def copiedIntegerBlockWitnessIntMatrix
    {r n q : ℕ}
    (C : Matrix (Fin r) (Fin q) ℚ) :
    Matrix (Fin (r + (n + n))) (Fin (n + q)) ℚ :=
  fun i ↦
    Fin.addCases
      (fun i' ↦ Fin.addCases (fun _ ↦ 0) (C i'))
      (Fin.addCases
        (fun i' ↦ Fin.addCases (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0))
        (fun i' ↦ Fin.addCases (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0)))
      i

/-- Helper for Exercise 4.33: the auxiliary real-variable matrix carries the visible
`(x_int, x_real, y)` coefficients on the original rows and adds the opposite-sign
`∓Id` rows on the visible integer coordinates. -/
private def copiedIntegerBlockWitnessRealMatrix
    {r n p m q : ℕ}
    (Aint : Matrix (Fin r) (Fin n) ℚ)
    (Areal : Matrix (Fin r) (Fin p) ℚ)
    (B : Matrix (Fin r) (Fin m) ℚ) :
    Matrix (Fin (r + (n + n))) (Fin ((n + p) + m)) ℚ :=
  fun i ↦
    Fin.addCases
      (fun i' ↦ Fin.append (Fin.append (Aint i') (Areal i')) (B i'))
      (Fin.addCases
        (fun i' ↦
          Fin.append
            (Fin.append (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0))
            (fun _ ↦ 0))
        (fun i' ↦
          Fin.append
            (Fin.append (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0))
            (fun _ ↦ 0)))
      i

/-- Helper for Exercise 4.33: the copied-block witness keeps the original right-hand side and
uses zero on the equality rows tying the copied visible integer block to the visible coordinates.
-/
private def copiedIntegerBlockWitnessRhs
    {r n : ℕ}
    (d : Fin r → ℚ) :
    Fin (r + (n + n)) → ℚ :=
  Fin.addCases d (Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0))

/-- Helper for Exercise 4.33: the lower copied equality row of the witness right-hand side is
zero. -/
private lemma copiedIntegerBlockWitnessRhsLowerRow
    {r n : ℕ}
    (d : Fin r → ℚ)
    (i : Fin n) :
    (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
        (Fin.natAdd r (Fin.natAdd n i)) = 0 := by
  have hnat : i.addNat n = Fin.natAdd n i := by
    apply Fin.ext
    simpa [Nat.add_comm] using rfl
  simp [copiedIntegerBlockWitnessRhs]
  rw [hnat, Fin.addCases_right]

/-- Helper for Exercise 4.33: on an original row, the copied integer block contributes exactly the
auxiliary `C z` term and nothing on the visible integer copy. -/
private lemma copiedIntegerBlockOriginalIntPartSpec
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    (wz : Fin (n + q) → ℤ)
    (i : Fin r) :
    (((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
        (fun j ↦ (wz j : ℝ))) (Fin.castAdd (n + n) i) =
      ∑ j : Fin q, (C i j : ℝ) * (wz (Fin.natAdd n j) : ℝ) := by
  -- The original row sees only the genuine auxiliary integer block.
  simp [copiedIntegerBlockWitnessIntMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- Helper for Exercise 4.33: on an original row, the copied real block reproduces the displayed
`Aint x_int + Areal x_real + B y` term. -/
private lemma copiedIntegerBlockOriginalRealPartSpec
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    (x : MixedRealPoint n p)
    (y : Fin m → ℝ)
    (i : Fin r) :
    (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
          Aint Areal B).map (Rat.castHom ℝ)).mulVec
        (Fin.append (Fin.appendEquiv n p x) y)) (Fin.castAdd (n + n) i) =
      (∑ j : Fin n, (Aint i j : ℝ) * x.1 j) +
        (∑ j : Fin p, (Areal i j : ℝ) * x.2 j) +
        (∑ j : Fin m, (B i j : ℝ) * y j) := by
  -- The original row splits once into the visible mixed block and the auxiliary real block.
  simp [copiedIntegerBlockWitnessRealMatrix, Matrix.mulVec, dotProduct, Fin.append,
    Fin.appendEquiv, Fin.sum_univ_add, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 4.33: the upper copied equality row of the auxiliary integer matrix picks
out the copied visible integer coordinate. -/
private lemma copiedIntegerBlockWitnessIntUpperRow
    {n r q : ℕ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    (wz : Fin (n + q) → ℤ)
    (i : Fin n) :
    (((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
        (fun j ↦ (wz j : ℝ))) (Fin.natAdd r (Fin.castAdd n i)) =
      (wz (Fin.castAdd q i) : ℝ) := by
  classical
  -- Evaluate the `+Id` copied row by isolating the unique visible copied coordinate.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Finset.sum_eq_single i]
  · simp [copiedIntegerBlockWitnessIntMatrix, Fin.addCases_right]
  · intro j _ hj
    simp [copiedIntegerBlockWitnessIntMatrix, Fin.addCases_right, hj]
  · simp [copiedIntegerBlockWitnessIntMatrix, Fin.addCases_right]

/-- Helper for Exercise 4.33: the upper copied equality row of the auxiliary real matrix records
the negated visible integer coordinate of the mixed point. -/
private lemma copiedIntegerBlockWitnessRealUpperRow
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    (x : MixedRealPoint n p)
    (y : Fin m → ℝ)
    (i : Fin n) :
    (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
          Aint Areal B).map (Rat.castHom ℝ)).mulVec
        (Fin.append (Fin.appendEquiv n p x) y)) (Fin.natAdd r (Fin.castAdd n i)) =
      -x.1 i := by
  classical
  -- Split the visible and auxiliary real blocks so only the `-Id` coefficient on `x.1 i`
  -- survives.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_eq_single i]
  · simp [copiedIntegerBlockWitnessRealMatrix, Fin.addCases_right, Fin.append, Fin.appendEquiv]
  · intro j _ hj
    simp [copiedIntegerBlockWitnessRealMatrix, Fin.addCases_right, Fin.append,
      Fin.appendEquiv, hj]
  · simp [copiedIntegerBlockWitnessRealMatrix, Fin.addCases_right, Fin.append, Fin.appendEquiv]

/-- Helper for Exercise 4.33: the lower copied equality row of the auxiliary integer matrix
contributes the negated copied visible integer coordinate. -/
private lemma copiedIntegerBlockWitnessIntLowerRow
    {n r q : ℕ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    (wz : Fin (n + q) → ℤ)
    (i : Fin n) :
    (((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
        (fun j ↦ (wz j : ℝ))) (Fin.natAdd r (Fin.natAdd n i)) =
      -(wz (Fin.castAdd q i) : ℝ) := by
  classical
  have hcoeffLeft :
      ∀ j : Fin n,
        (((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ))
            (Fin.natAdd r (Fin.natAdd n i)) (Fin.castAdd q j)) =
          if j = i then (-1 : ℝ) else 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp [copiedIntegerBlockWitnessIntMatrix]
    rw [hnat, Fin.addCases_right]
    by_cases h : j = i <;> simp [h]
  have hcoeffRight :
      ∀ j : Fin q,
        (((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ))
            (Fin.natAdd r (Fin.natAdd n i)) (Fin.natAdd n j)) = 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp [copiedIntegerBlockWitnessIntMatrix]
    rw [hnat, Fin.addCases_right]
    simp
  -- Normalize the `-Id` row before summing, so the remaining calculation is a one-coordinate sum.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  simp_rw [hcoeffLeft, hcoeffRight]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Helper for Exercise 4.33: the lower copied equality row of the auxiliary real matrix records
the visible integer coordinate of the mixed point. -/
private lemma copiedIntegerBlockWitnessRealLowerRow
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    (x : MixedRealPoint n p)
    (y : Fin m → ℝ)
    (i : Fin n) :
    (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
          Aint Areal B).map (Rat.castHom ℝ)).mulVec
        (Fin.append (Fin.appendEquiv n p x) y)) (Fin.natAdd r (Fin.natAdd n i)) =
      x.1 i := by
  classical
  have hcoeffLeft :
      ∀ j : Fin n,
        (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
              Aint Areal B).map (Rat.castHom ℝ))
            (Fin.natAdd r (Fin.natAdd n i)) (Fin.castAdd m (Fin.castAdd p j))) =
          if j = i then (1 : ℝ) else 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp only [Rat.coe_castHom, Matrix.map_apply]
    simp [copiedIntegerBlockWitnessRealMatrix]
    rw [hnat, Fin.addCases_right]
    by_cases h : j = i <;> simp [h]
  have hcoeffMiddle :
      ∀ j : Fin p,
        (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
              Aint Areal B).map (Rat.castHom ℝ))
            (Fin.natAdd r (Fin.natAdd n i)) (Fin.castAdd m (Fin.natAdd n j))) = 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp only [Rat.coe_castHom, Matrix.map_apply]
    simp [copiedIntegerBlockWitnessRealMatrix]
    rw [hnat, Fin.addCases_right]
    simp
  have hcoeffRight :
      ∀ j : Fin m,
        (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
              Aint Areal B).map (Rat.castHom ℝ))
            (Fin.natAdd r (Fin.natAdd n i)) (Fin.natAdd (n + p) j)) = 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp only [Rat.coe_castHom, Matrix.map_apply]
    simp [copiedIntegerBlockWitnessRealMatrix]
    rw [hnat, Fin.addCases_right]
    simp
  -- Normalize the three appended blocks separately before evaluating the unique surviving term.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp_rw [hcoeffLeft, hcoeffMiddle, hcoeffRight]
  rw [Finset.sum_eq_single i]
  · simp [Fin.append, Fin.appendEquiv]
  · intro j _ hj
    simp [hj]
  · simp

/-- Helper for Exercise 4.33: the first copied equality row evaluates to
`(wz (Fin.castAdd q i) : ℝ) - x.1 i`. -/
private lemma copiedIntegerBlockUpperEqualityRowSpec
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    (x : MixedRealPoint n p)
    (y : Fin m → ℝ)
    (wz : Fin (n + q) → ℤ)
    (i : Fin n) :
    ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
          (fun j ↦ (wz j : ℝ))) +
        (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
            Aint Areal B).map (Rat.castHom ℝ)).mulVec
          (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.castAdd n i)) =
      (wz (Fin.castAdd q i) : ℝ) - x.1 i :=
by
  -- Combine the blockwise copied-row evaluations so the equality row becomes `zCopy_i - x_i`.
  rw [Pi.add_apply, copiedIntegerBlockWitnessIntUpperRow (C := C) (wz := wz) i,
    copiedIntegerBlockWitnessRealUpperRow (Aint := Aint) (Areal := Areal) (B := B)
      (q := q) (x := x) (y := y) i]
  simp [sub_eq_add_neg]

/-- Helper for Exercise 4.33: the second copied equality row evaluates to
`x.1 i - (wz (Fin.castAdd q i) : ℝ)`. -/
private lemma copiedIntegerBlockLowerEqualityRowSpec
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    (x : MixedRealPoint n p)
    (y : Fin m → ℝ)
    (wz : Fin (n + q) → ℤ)
    (i : Fin n) :
    ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
          (fun j ↦ (wz j : ℝ))) +
        (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
            Aint Areal B).map (Rat.castHom ℝ)).mulVec
          (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.natAdd n i)) =
      x.1 i - (wz (Fin.castAdd q i) : ℝ) :=
by
  -- Combine the blockwise copied-row evaluations so the equality row becomes `x_i - zCopy_i`.
  rw [Pi.add_apply, copiedIntegerBlockWitnessIntLowerRow (C := C) (wz := wz) i,
    copiedIntegerBlockWitnessRealLowerRow (Aint := Aint) (Areal := Areal) (B := B)
      (q := q) (x := x) (y := y) i]
  ring

/-- Helper for Exercise 4.33: the copied visible integer block converts the source-facing mixed
system into one canonical `mixed_integer_x_projection` witness on the flattened owner. -/
private lemma copiedIntegerBlockProjection_iff
    {n p r m q : ℕ}
    {Aint : Matrix (Fin r) (Fin n) ℚ}
    {Areal : Matrix (Fin r) (Fin p) ℚ}
    {B : Matrix (Fin r) (Fin m) ℚ}
    {C : Matrix (Fin r) (Fin q) ℚ}
    {d : Fin r → ℚ}
    {x : MixedRealPoint n p} :
    Fin.appendEquiv n p x ∈
        mixed_integer_x_projection
          (n := n + p)
          (p := m)
          (q := n + q)
          (rational_mixed_polyhedron
            (copiedIntegerBlockWitnessIntMatrix (n := n) C)
            (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
              Aint Areal B)
            (copiedIntegerBlockWitnessRhs (n := n) d)) ↔
      x ∈ (ℤ^n×ℝ^p) ∧
        ∃ y : Fin m → ℝ,
          ∃ z : Fin q → ℤ,
            ∀ i : Fin r,
              (∑ j : Fin n, (Aint i j : ℝ) * x.1 j) +
                  (∑ j : Fin p, (Areal i j : ℝ) * x.2 j) +
                  (∑ j : Fin m, (B i j : ℝ) * y j) +
                  (∑ j : Fin q, (C i j : ℝ) * (z j : ℝ)) ≤
                (d i : ℝ) :=
by
  rw [mem_mixed_integer_x_projection_iff]
  constructor
  · rintro ⟨y, wz, hwz⟩
    rw [mem_rational_mixed_polyhedron_iff] at hwz
    let xInt : Fin n → ℤ := fun i ↦ wz (Fin.castAdd q i)
    have hxIntEq : x.1 = fun i ↦ (xInt i : ℝ) := by
      funext i
      have hiUpper :
          ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
                (fun j ↦ (wz j : ℝ))) +
              (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                  Aint Areal B).map (Rat.castHom ℝ)).mulVec
                (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.castAdd n i)) ≤
            (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
              (Fin.natAdd r (Fin.castAdd n i)) := by
        simpa using hwz (Fin.natAdd r (Fin.castAdd n i))
      have hiLower :
          ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
                (fun j ↦ (wz j : ℝ))) +
              (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                  Aint Areal B).map (Rat.castHom ℝ)).mulVec
                (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.natAdd n i)) ≤
            (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
              (Fin.natAdd r (Fin.natAdd n i)) := by
        simpa using hwz (Fin.natAdd r (Fin.natAdd n i))
      rw [Pi.add_apply] at hiUpper hiLower
      rw [copiedIntegerBlockWitnessIntUpperRow (C := C) (wz := wz) i,
        copiedIntegerBlockWitnessRealUpperRow (Aint := Aint) (Areal := Areal) (B := B)
          (q := q) (x := x) (y := y) i] at hiUpper
      rw [copiedIntegerBlockWitnessIntLowerRow (C := C) (wz := wz) i,
        copiedIntegerBlockWitnessRealLowerRow (Aint := Aint) (Areal := Areal) (B := B)
          (q := q) (x := x) (y := y) i] at hiLower
      have hiUpper' : (wz (Fin.castAdd q i) : ℝ) - x.1 i ≤ 0 := by
        simpa [copiedIntegerBlockWitnessRhs, sub_eq_add_neg] using hiUpper
      have hiLower' : x.1 i - (wz (Fin.castAdd q i) : ℝ) ≤ 0 := by
        rw [copiedIntegerBlockWitnessRhsLowerRow (r := r) (d := d) i] at hiLower
        simpa [sub_eq_add_neg] using hiLower
      dsimp [xInt]
      linarith
    have hxMixed : x ∈ (ℤ^n×ℝ^p) := by
      rw [mem_mixed_integer_lattice_iff]
      exact (mem_integerVectors_iff (x := x.1)).2 ⟨xInt, hxIntEq⟩
    refine ⟨hxMixed, y, fun j ↦ wz (Fin.natAdd n j), ?_⟩
    intro i
    have hi :
        ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
              (fun j ↦ (wz j : ℝ))) +
            (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                Aint Areal B).map (Rat.castHom ℝ)).mulVec
              (Fin.append (Fin.appendEquiv n p x) y))) (Fin.castAdd (n + n) i) ≤
          (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
            (Fin.castAdd (n + n) i) := by
      simpa using hwz (Fin.castAdd (n + n) i)
    rw [Pi.add_apply] at hi
    rw [copiedIntegerBlockOriginalIntPartSpec (Aint := Aint) (Areal := Areal) (B := B)
      (C := C) (wz := wz) i,
      copiedIntegerBlockOriginalRealPartSpec (Aint := Aint) (Areal := Areal) (B := B)
        (q := q) (x := x) (y := y) i] at hi
    simpa [copiedIntegerBlockWitnessRhs, add_assoc, add_left_comm, add_comm] using hi
  · rintro ⟨hxMixed, y, z, hineq⟩
    rw [mem_mixed_integer_lattice_iff] at hxMixed
    rcases (mem_integerVectors_iff (x := x.1)).1 hxMixed with ⟨xInt, hxIntEq⟩
    let wz : Fin (n + q) → ℤ := Fin.append xInt z
    refine ⟨y, wz, ?_⟩
    rw [mem_rational_mixed_polyhedron_iff]
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i'
      change
        ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
              (fun j ↦ (wz j : ℝ))) +
            (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                Aint Areal B).map (Rat.castHom ℝ)).mulVec
              (Fin.append (Fin.appendEquiv n p x) y))) (Fin.castAdd (n + n) i') ≤
          (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
            (Fin.castAdd (n + n) i')
      rw [Pi.add_apply]
      have hi := hineq i'
      -- The original rows only read the genuine auxiliary `z` block and the displayed real part.
      rw [copiedIntegerBlockOriginalIntPartSpec (Aint := Aint) (Areal := Areal) (B := B)
        (C := C) (wz := wz) i',
        copiedIntegerBlockOriginalRealPartSpec (Aint := Aint) (Areal := Areal) (B := B)
          (q := q) (x := x) (y := y) i']
      simpa [wz, copiedIntegerBlockWitnessRhs, Fin.append, add_assoc, add_left_comm, add_comm]
        using hi
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        change
          ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
                (fun j ↦ (wz j : ℝ))) +
              (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                  Aint Areal B).map (Rat.castHom ℝ)).mulVec
                (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.castAdd n j')) ≤
            (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
              (Fin.natAdd r (Fin.castAdd n j'))
        rw [Pi.add_apply]
        have hj' : x.1 j' = (wz (Fin.castAdd q j') : ℝ) := by
          have hxCoord := congrFun hxIntEq j'
          simpa [wz, Fin.append] using hxCoord
        have hrow : (wz (Fin.castAdd q j') : ℝ) - x.1 j' ≤ 0 := by
          simpa [hj']
        -- Repackage the copied equality `wz_copy = x_int` as the upper inequality row.
        rw [copiedIntegerBlockWitnessIntUpperRow (C := C) (wz := wz) j',
          copiedIntegerBlockWitnessRealUpperRow (Aint := Aint) (Areal := Areal) (B := B)
            (q := q) (x := x) (y := y) j']
        simpa [copiedIntegerBlockWitnessRhs, sub_eq_add_neg] using hrow
      · intro j'
        change
          ((((copiedIntegerBlockWitnessIntMatrix (n := n) C).map (Rat.castHom ℝ)).mulVec
                (fun j ↦ (wz j : ℝ))) +
              (((copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                  Aint Areal B).map (Rat.castHom ℝ)).mulVec
                (Fin.append (Fin.appendEquiv n p x) y))) (Fin.natAdd r (Fin.natAdd n j')) ≤
            (fun i ↦ (copiedIntegerBlockWitnessRhs (n := n) d i : ℝ))
              (Fin.natAdd r (Fin.natAdd n j'))
        rw [Pi.add_apply]
        have hj' : x.1 j' = (wz (Fin.castAdd q j') : ℝ) := by
          have hxCoord := congrFun hxIntEq j'
          simpa [wz, Fin.append] using hxCoord
        have hrow : x.1 j' - (wz (Fin.castAdd q j') : ℝ) ≤ 0 := by
          simpa [hj']
        -- Repackage the same copied equality as the lower inequality row.
        rw [copiedIntegerBlockWitnessIntLowerRow (C := C) (wz := wz) j',
          copiedIntegerBlockWitnessRealLowerRow (Aint := Aint) (Areal := Areal) (B := B)
            (q := q) (x := x) (y := y) j']
        rw [copiedIntegerBlockWitnessRhsLowerRow (r := r) (d := d) j']
        simpa [sub_eq_add_neg] using hrow

/-- A subset of `ℤ^n × ℝ^p` is mixed integer linear representable exactly when its flattened image
in `ℝ^(n+p)` is mixed integer linear representable in the Chapter 4 owner sense, equivalently by a
rational mixed-integer linear extended formulation whose displayed mixed-space side explicitly
retains membership in `ℤ^n × ℝ^p`. -/
theorem is_mixed_integer_linear_representable_on_mixed_integer_point_iff
    {n p : ℕ} {S : Set (MixedRealPoint n p)}
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p)) :
    is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S) ↔
      ∃ r m q : ℕ,
        ∃ Aint : Matrix (Fin r) (Fin n) ℚ,
          ∃ Areal : Matrix (Fin r) (Fin p) ℚ,
            ∃ B : Matrix (Fin r) (Fin m) ℚ,
              ∃ C : Matrix (Fin r) (Fin q) ℚ,
                ∃ d : Fin r → ℚ,
                  S =
                    {x : MixedRealPoint n p |
                      x ∈ (ℤ^n×ℝ^p) ∧
                        ∃ y : Fin m → ℝ,
                          ∃ z : Fin q → ℤ,
                            ∀ i : Fin r,
                              (∑ j : Fin n, (Aint i j : ℝ) * x.1 j) +
                                  (∑ j : Fin p, (Areal i j : ℝ) * x.2 j) +
                                  (∑ j : Fin m, (B i j : ℝ) * y j) +
                                  (∑ j : Fin q, (C i j : ℝ) * (z j : ℝ)) ≤
                                (d i : ℝ)} := by
  constructor
  · intro hrepr
    rcases (is_mixed_integer_linear_representable_iff).1 hrepr with
      ⟨m, q, P, hP_rational, hSP⟩
    rcases (is_rational_mixed_polyhedron_iff).1 hP_rational with
      ⟨r, C, G, d, hP_eq⟩
    let Aint : Matrix (Fin r) (Fin n) ℚ :=
      fun i j ↦ G i (Fin.castAdd m (Fin.castAdd p j))
    let Areal : Matrix (Fin r) (Fin p) ℚ :=
      fun i j ↦ G i (Fin.castAdd m (Fin.natAdd n j))
    let B : Matrix (Fin r) (Fin m) ℚ := fun i j ↦ G i (Fin.natAdd (n + p) j)
    have hmem_projection :
        ∀ {x : MixedRealPoint n p},
          Fin.appendEquiv n p x ∈ mixed_integer_x_projection P ↔
            ∃ y : Fin m → ℝ,
              ∃ z : Fin q → ℤ,
                ∀ i : Fin r,
                  (∑ j : Fin n, (Aint i j : ℝ) * x.1 j) +
                      (∑ j : Fin p, (Areal i j : ℝ) * x.2 j) +
                      (∑ j : Fin m, (B i j : ℝ) * y j) +
                      (∑ j : Fin q, (C i j : ℝ) * (z j : ℝ)) ≤
                    (d i : ℝ) := by
      intro x
      rw [mem_mixed_integer_x_projection_iff]
      constructor
      · rintro ⟨y, z, hxyz⟩
        -- Expand the rational witness into the displayed mixed-space inequalities.
        rw [hP_eq, mem_rational_mixed_polyhedron_iff] at hxyz
        refine ⟨y, z, ?_⟩
        intro i
        have hi := hxyz i
        simpa [Aint, Areal, B, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
          Fin.append, Fin.appendEquiv, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hi
      · rintro ⟨y, z, hxyz⟩
        -- Repackage the displayed inequalities as membership in the witness polyhedron.
        refine ⟨y, z, ?_⟩
        rw [hP_eq, mem_rational_mixed_polyhedron_iff]
        intro i
        have hi := hxyz i
        simpa [Aint, Areal, B, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
          Fin.append, Fin.appendEquiv, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hi
    refine ⟨r, m, q, Aint, Areal, B, C, d, ?_⟩
    ext x
    constructor
    · intro hx
      -- Use the owner equality on the flattened image, then forget back to the mixed point.
      have hx_flat : Fin.appendEquiv n p x ∈ mixed_integer_x_projection P := by
        rw [← hSP]
        exact ⟨x, hx, rfl⟩
      rcases hmem_projection.mp hx_flat with ⟨y, z, hineq⟩
      exact ⟨hS_mixed hx, y, z, hineq⟩
    · rintro ⟨hx_mixed, y, z, hineq⟩
      -- The displayed formulation lands in the flattened owner set, so injectivity recovers `x`.
      have hx_flat : Fin.appendEquiv n p x ∈ mixed_integer_x_projection P :=
        hmem_projection.mpr ⟨y, z, hineq⟩
      rw [← hSP] at hx_flat
      rcases hx_flat with ⟨x', hx'S, hx'Eq⟩
      have hx_eq : x' = x := by
        exact (Fin.appendEquiv n p).injective (by simpa using hx'Eq)
      exact hx_eq ▸ hx'S
  · rintro ⟨r, m, q, Aint, Areal, B, C, d, hS_eq⟩
    rw [is_mixed_integer_linear_representable_iff]
    refine ⟨m, n + q, rational_mixed_polyhedron
      (copiedIntegerBlockWitnessIntMatrix (n := n) C)
      (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q) Aint Areal B)
      (copiedIntegerBlockWitnessRhs (n := n) d), ?_, ?_⟩
    · -- The copied visible integer block is a rational mixed polyhedron by construction.
      refine (is_rational_mixed_polyhedron_iff).2 ?_
      refine ⟨r + (n + n),
        copiedIntegerBlockWitnessIntMatrix (n := n) C,
        copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q) Aint Areal B,
        copiedIntegerBlockWitnessRhs (n := n) d, rfl⟩
    · ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [copiedIntegerBlockProjection_iff]
        rw [hS_eq] at hx
        exact hx
      · intro hu
        have hu' :
            (Fin.appendEquiv n p).symm u ∈ (ℤ^n×ℝ^p) ∧
              ∃ y : Fin m → ℝ,
                ∃ z : Fin q → ℤ,
                  ∀ i : Fin r,
                    (∑ j : Fin n, (Aint i j : ℝ) * ((Fin.appendEquiv n p).symm u).1 j) +
                        (∑ j : Fin p, (Areal i j : ℝ) * ((Fin.appendEquiv n p).symm u).2 j) +
                        (∑ j : Fin m, (B i j : ℝ) * y j) +
                        (∑ j : Fin q, (C i j : ℝ) * (z j : ℝ)) ≤
                      (d i : ℝ) := by
          have hu'' :
              Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) ∈
                mixed_integer_x_projection
                  (n := n + p)
                  (p := m)
                  (q := n + q)
                  (rational_mixed_polyhedron
                    (copiedIntegerBlockWitnessIntMatrix (n := n) C)
                    (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                      Aint Areal B)
                    (copiedIntegerBlockWitnessRhs (n := n) d)) := by
            rw [appendEquiv_symm_apply (n := n) (p := p) u]
            exact hu
          exact (copiedIntegerBlockProjection_iff
            (x := (Fin.appendEquiv n p).symm u)).1 hu''
        rw [hS_eq]
        exact ⟨(Fin.appendEquiv n p).symm u, hu', by
          simpa using (Fin.appendEquiv n p).apply_symm_apply u⟩

/-- Helper for Exercise 4.33: every natural multiple of a listed integral generator belongs to
the ambient integral cone. -/
private lemma natSmulGenerator_mem_integralIntcone
    {k t : ℕ}
    (r : Fin t → Fin k → ℤ)
    (j : Fin t)
    (m : ℕ) :
    (m : ℝ) • (fun i : Fin k ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  -- Use the one-hot coefficient vector supported at `j` to realize the chosen generator multiple.
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun s ↦ if s = j then m else 0, ?_⟩
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro s _ hsj
    simp [hsj]
  · simp

/-- Helper for Exercise 4.33: if every listed integral-cone generator is zero, then the whole
integral cone collapses to `{0}`. -/
private lemma integralIntconeEqSingletonZeroOfGeneratorsEqZero
    {k t : ℕ}
    {r : Fin t → Fin k → ℤ}
    (hr : ∀ j, (fun i : Fin k ↦ (r j i : ℝ)) = 0) :
    integral_intcone r = ({0} : Set (Fin k → ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff]
    rcases (mem_integral_intcone_iff).1 hx with ⟨a, rfl⟩
    -- Once every generator vanishes, every integral-cone combination is forced to be zero.
    simp [hr]
  · rintro rfl
    -- The zero vector is realized by the zero coefficient family.
    exact (mem_integral_intcone_iff).2 ⟨0, by simp⟩

/-- Helper for Exercise 4.33: if a bounded Minkowski sum `U + integral_intcone r` is nonempty on
the `U` side, then every listed integral-cone generator must vanish. -/
private lemma integralIntconeGeneratorsEqZeroOfBoundedNonemptySum
    {k t : ℕ}
    {U : Set (Fin k → ℝ)}
    {r : Fin t → Fin k → ℤ}
    (hbounded : Bornology.IsBounded (U + integral_intcone r))
    (hU_nonempty : Set.Nonempty U) :
    ∀ j, (fun i : Fin k ↦ (r j i : ℝ)) = 0 := by
  intro j
  obtain ⟨u0, hu0⟩ := hU_nonempty
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : Fin k → ℝ)
  let g : Fin k → ℝ := fun i ↦ (r j i : ℝ)
  by_contra hg_nonzero
  have hg_norm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_nonzero
  obtain ⟨m, hm⟩ := exists_nat_gt ((R + ‖u0‖ + 1) / ‖g‖)
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_mul :
      R + ‖u0‖ + 1 < (m : ℝ) * ‖g‖ := by
    have hm' : ((R + ‖u0‖ + 1) / ‖g‖) < (m : ℝ) := by
      exact hm
    exact (div_lt_iff₀ hg_norm_pos).mp hm'
  have hmem :
      u0 + (m : ℝ) • g ∈ U + integral_intcone r := by
    refine Set.mem_add.2 ⟨u0, hu0, (m : ℝ) • g, ?_, rfl⟩
    simpa [g] using natSmulGenerator_mem_integralIntcone r j m
  have hclosedBall :
      u0 + (m : ℝ) • g ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR hmem
  have hnorm_le : ‖u0 + (m : ℝ) • g‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hclosedBall
  have htriangle :
      (m : ℝ) * ‖g‖ ≤ ‖u0 + (m : ℝ) • g‖ + ‖u0‖ := by
    calc
      (m : ℝ) * ‖g‖ = ‖(m : ℝ) • g‖ := by
        rw [norm_smul, Real.norm_of_nonneg hm_nonneg]
      _ = ‖(u0 + (m : ℝ) • g) - u0‖ := by
        congr 1
        ext i
        simp
      _ ≤ ‖u0 + (m : ℝ) • g‖ + ‖u0‖ := norm_sub_le _ _
  linarith

/-- Helper for Exercise 4.33: boundedness collapses the integral cone in a decomposition
`U + integral_intcone r`, provided `U` is nonempty. -/
private lemma integralIntconeEqSingletonZeroOfBoundedNonemptySum
    {k t : ℕ}
    {U : Set (Fin k → ℝ)}
    {r : Fin t → Fin k → ℤ}
    (hbounded : Bornology.IsBounded (U + integral_intcone r))
    (hU_nonempty : Set.Nonempty U) :
    integral_intcone r = ({0} : Set (Fin k → ℝ)) := by
  -- First show every generator is zero, then rewrite the whole cone through that normal form.
  exact integralIntconeEqSingletonZeroOfGeneratorsEqZero
    (integralIntconeGeneratorsEqZeroOfBoundedNonemptySum hbounded hU_nonempty)

/-- Helper for Exercise 4.33: a bounded nonempty set has trivial recession cone. -/
private lemma recessionConeEqSingletonZeroOfNonemptyBounded
    {k : ℕ}
    {P : Set (Fin k → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_bounded : Bornology.IsBounded P) :
    recessionCone P = ({0} : Set (Fin k → ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := hP_nonempty
  have htranslate :
      ({x₀} + recessionCone P) ⊆ P := by
    -- Translate each recession direction by one feasible base point to stay in `P`.
    rintro y ⟨x', hx', r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    rw [mem_recessionCone_iff] at hr
    simpa using hr hx₀ 1 zero_le_one
  have hrec_bounded : Bornology.IsBounded (recessionCone P) := by
    -- The translated recession cone sits inside the bounded ambient set `P`.
    obtain ⟨R, _, hP_ball⟩ := hP_bounded.subset_ball_lt 0 (0 : Fin k → ℝ)
    exact Bornology.IsBounded.subset
      (show Bornology.IsBounded (Metric.ball (0 : Fin k → ℝ) (R + ‖x₀‖)) from
        Metric.isBounded_ball)
      (by
        intro r hr
        have hxrP : x₀ + r ∈ P := by
          exact htranslate ⟨x₀, Set.mem_singleton x₀, r, hr, by simp⟩
        have hxr_ball : ‖x₀ + r‖ < R := by
          simpa [Metric.mem_ball, dist_eq_norm] using hP_ball hxrP
        have hr_eq : r = (x₀ + r) + (-x₀) := by
          ext i
          simp
        have hr_norm_le : ‖r‖ ≤ ‖x₀ + r‖ + ‖x₀‖ := by
          rw [hr_eq]
          simpa using norm_add_le (x₀ + r) (-x₀)
        have hr_norm_lt : ‖r‖ < R + ‖x₀‖ := by
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hr_norm_lt)
  ext r
  constructor
  · intro hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · obtain ⟨R, hR⟩ := hrec_bounded.subset_closedBall (0 : Fin k → ℝ)
      have hzero_mem : (0 : Fin k → ℝ) ∈ recessionCone P := zero_mem_recessionCone
      have hR_nonneg : 0 ≤ R := by
        have hzero_ball : (0 : Fin k → ℝ) ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR hzero_mem
        simpa [Metric.mem_closedBall] using hzero_ball
      have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
      have hr_norm_ne : ‖r‖ ≠ 0 := ne_of_gt hr_norm_pos
      have ht_nonneg : 0 ≤ R / ‖r‖ + 1 := by positivity
      have htr_mem : ((R / ‖r‖ + 1) • r) ∈ recessionCone P :=
        smul_mem_recessionCone hr ht_nonneg
      have hmem_ball :
          ((R / ‖r‖ + 1) • r) ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR htr_mem
      have htr_bound : ‖(R / ‖r‖ + 1) • r‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hmem_ball
      have htr_norm : ‖(R / ‖r‖ + 1) • r‖ = R + ‖r‖ := by
        calc
          ‖(R / ‖r‖ + 1) • r‖ = |R / ‖r‖ + 1| * ‖r‖ := norm_smul _ _
          _ = (R / ‖r‖ + 1) * ‖r‖ := by rw [abs_of_nonneg ht_nonneg]
          _ = (R / ‖r‖) * ‖r‖ + ‖r‖ := by rw [add_mul, one_mul]
          _ = R + ‖r‖ := by rw [div_mul_cancel₀ _ hr_norm_ne]
      have hlarge : R + ‖r‖ ≤ R := by
        simpa [htr_norm] using htr_bound
      linarith
  · intro hr
    have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
    subst hr0
    exact zero_mem_recessionCone

/-- Helper for Exercise 4.33: applying `Fin.appendEquiv` to the pullback of a flat set along its
inverse recovers the original flat set. -/
private lemma appendEquiv_image_symm_eq
    {n p : ℕ}
    (Q : Set (Fin (n + p) → ℝ)) :
    Fin.appendEquiv n p '' ((Fin.appendEquiv n p).symm '' Q) = Q := by
  -- Compare both sides by unpacking the image witnesses through the flattening equivalence.
  ext u
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, hvu⟩
    have hu : u = w := by
      exact hvu.symm.trans (appendEquiv_symm_apply (n := n) (p := p) w)
    exact hu ▸ hw
  · intro hu
    refine ⟨(Fin.appendEquiv n p).symm u, ⟨u, hu, rfl⟩, ?_⟩
    simpa using appendEquiv_symm_apply (n := n) (p := p) u

/-- Helper for Exercise 4.33: if a flat piece sits inside the flattened image of a mixed-integer
set, then its pullback already equals its mixed-integer points. -/
private lemma mixedIntegerPointsSymmImageEqOfSubsetAppendEquivImage
    {n p : ℕ}
    {S : Set (MixedRealPoint n p)}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ_subset : Q ⊆ (Fin.appendEquiv n p '' S))
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p)) :
    mixed_integer_points ((Fin.appendEquiv n p).symm '' Q) =
      (Fin.appendEquiv n p).symm '' Q := by
  -- One inclusion is tautological; the reverse pulls a flat witness back to `S` and uses that
  -- every point of `S` is already mixed-integer.
  ext x
  constructor
  · intro hx
    exact (mem_mixed_integer_points_iff).1 hx |>.1
  · rintro ⟨u, huQ, rfl⟩
    refine (mem_mixed_integer_points_iff).2 ?_
    constructor
    · exact ⟨u, huQ, rfl⟩
    · rcases hQ_subset huQ with ⟨s, hsS, hus⟩
      have hsFlat :
          Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) = Fin.appendEquiv n p s := by
        calc
          Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) = u := by
            simpa using appendEquiv_symm_apply (n := n) (p := p) u
          _ = Fin.appendEquiv n p s := hus.symm
      exact (Fin.appendEquiv n p).injective hsFlat ▸ hS_mixed hsS

/-- Helper for Exercise 4.33: adding the zero singleton on the right leaves a set unchanged. -/
private lemma add_singleton_zero_eq
    {α : Type*}
    [AddMonoid α]
    {U : Set α} :
    U + ({0} : Set α) = U := by
  -- Unpack the set addition witness and use that the only point of `{0}` is the zero element.
  ext x
  constructor
  · intro hx
    rcases Set.mem_add.mp hx with ⟨u, hu, z, hz, hsum⟩
    have hz_zero : z = 0 := Set.mem_singleton_iff.mp hz
    have hx_eq : u = x := by
      simpa [hz_zero] using hsum
    simpa [hx_eq] using hu
  · intro hx
    exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩

/-- Helper for Exercise 4.33: a nested finite family of flat rational polytopes can be reindexed
by one finite flat family. -/
private lemma sigmaReindexFlatRationalPolytopeFamilies
    {d k : ℕ}
    (m : Fin k → ℕ)
    (Q : ∀ i : Fin k, Fin (m i) → Set (Fin d → ℝ))
    (hQ : ∀ i : Fin k, ∀ j : Fin (m i), (Q i j).IsRationalPolytope) :
    ∃ K : ℕ,
      ∃ Q' : Fin K → Set (Fin d → ℝ),
        (∀ s : Fin K, (Q' s).IsRationalPolytope) ∧
          (⋃ i : Fin k, ⋃ j : Fin (m i), Q i j) = ⋃ s : Fin K, Q' s := by
  classical
  let ι := Σ i : Fin k, Fin (m i)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Q' : Fin (Fintype.card ι) → Set (Fin d → ℝ) :=
    fun s ↦
      match e s with
      | ⟨i, j⟩ => Q i j
  refine ⟨Fintype.card ι, Q', ?_, ?_⟩
  · intro s
    rcases hs : e s with ⟨i, j⟩
    simpa [Q', hs] using hQ i j
  · -- Transport union membership through the sigma-index equivalence once.
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      rcases Set.mem_iUnion.mp hxi with ⟨j, hxij⟩
      refine Set.mem_iUnion.2 ⟨e.symm ⟨i, j⟩, ?_⟩
      simpa [Q', e] using hxij
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨s, hxs⟩
      rcases hs : e s with ⟨i, j⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      simpa [Q', hs] using hxs

/-- Helper for Exercise 4.33: every rational polytope in `ℝ^n` admits a rational matrix
presentation. -/
private lemma rationalPolytopeEqRationalMatrixPolyhedron
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    (hP : P.IsRationalPolytope) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
        ∃ b : Fin m → ℚ,
          P = rational_matrix_polyhedron A b := by
  rcases hP with ⟨k, v, rfl⟩
  let rays0 : Fin 0 → Fin n → ℚ := Fin.elim0
  let L : ℕ := ∑ j : Fin k, EncodingSize.rationalVector (v j)
  have hVertices :
      ∀ j : Fin k, EncodingSize.rationalVector (v j) ≤ L := by
    intro j
    exact Finset.single_le_sum
      (fun j' _ ↦ Nat.zero_le (EncodingSize.rationalVector (v j')))
      (Finset.mem_univ j)
  rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
      v
      rays0
      L
      hVertices
      (by intro j; exact Fin.elim0 j) with
    ⟨π, m, A, b, hrepr, -, -⟩
  refine ⟨m, A, b, ?_⟩
  have hConeEmpty :
      cone (Set.range fun i : Fin 0 ↦ fun j : Fin n ↦ (rays0 i j : ℝ)) =
        ({0} : Set (Fin n → ℝ)) := by
    simpa using (cone_empty : cone (∅ : Set (Fin n → ℝ)) = ({0} : Set (Fin n → ℝ)))
  calc
    convexHull ℝ (Set.range fun i : Fin k ↦ fun j : Fin n ↦ (v i j : ℝ))
        = convexHull ℝ (Set.range fun i : Fin k ↦ fun j : Fin n ↦ (v i j : ℝ)) +
            cone (Set.range fun i : Fin 0 ↦ fun j : Fin n ↦ (rays0 i j : ℝ)) := by
              rw [hConeEmpty, add_singleton_zero_eq]
    _ = rational_matrix_polyhedron A b := hrepr

/-- Helper for Exercise 4.33: every rational polytope is bounded because it is the convex hull of
a finite set of rational vertices. -/
private lemma isBoundedOfIsRationalPolytope
    {d : ℕ}
    {Q : Set (Fin d → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    Bornology.IsBounded Q := by
  rcases hQ with ⟨k, v, rfl⟩
  -- The ambient convex hull of a finite range is bounded.
  simpa using (isBounded_convexHull).2 (Set.finite_range _).isBounded

/-- Helper for Exercise 4.33: pulling a flat rational polytope back through `Fin.appendEquiv`
preserves rational mixed-polyhedrality. -/
private lemma pullbackRationalPolytopeIsRationalMixedPolyhedron
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    is_rational_mixed_polyhedron ((Fin.appendEquiv n p).symm '' Q) := by
  -- Route correction: use the canonical owner definition
  -- `is_rational_mixed_polyhedron P := is_rational_polyhedron ((Fin.appendEquiv n p) '' P)`
  -- and then rewrite the flattened pullback back to `Q`.
  change is_rational_polyhedron (Fin.appendEquiv n p '' ((Fin.appendEquiv n p).symm '' Q))
  rw [appendEquiv_image_symm_eq (n := n) (p := p) Q]
  rcases rationalPolytopeEqRationalMatrixPolyhedron hQ with ⟨m, A, b, hQeq⟩
  exact ⟨m, A, b, hQeq⟩

/-- Helper for Exercise 4.33: pulling a flat rational polyhedron back through `Fin.appendEquiv`
preserves rational mixed-polyhedrality. -/
private lemma pullbackRationalPolyhedronIsRationalMixedPolyhedron
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : is_rational_polyhedron Q) :
    is_rational_mixed_polyhedron ((Fin.appendEquiv n p).symm '' Q) := by
  -- Reinterpret the pullback through the defining flattened owner.
  change is_rational_polyhedron (Fin.appendEquiv n p '' ((Fin.appendEquiv n p).symm '' Q))
  rw [appendEquiv_image_symm_eq (n := n) (p := p) Q]
  exact hQ

/-- Helper for Exercise 4.33: the bounded flattened target can be normalized to one copied-block
witness whose visible `x`-projection is exactly the target set. -/
private lemma existsExplicitFlatMixedIntegerProjectionWitness
    {n p : ℕ}
    (S : Set (MixedRealPoint n p))
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p))
    (hrepr : is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S)) :
    ∃ r m q : ℕ,
      ∃ Aint : Matrix (Fin r) (Fin n) ℚ,
        ∃ Areal : Matrix (Fin r) (Fin p) ℚ,
          ∃ B : Matrix (Fin r) (Fin m) ℚ,
            ∃ C : Matrix (Fin r) (Fin q) ℚ,
              ∃ d : Fin r → ℚ,
                let W : Set (MixedRealPoint (n + q) ((n + p) + m)) :=
                  rational_mixed_polyhedron
                    (copiedIntegerBlockWitnessIntMatrix (n := n) C)
                    (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                      Aint Areal B)
                    (copiedIntegerBlockWitnessRhs (n := n) d)
                is_rational_mixed_polyhedron W ∧
                  ((Fin.appendEquiv n p) '' S =
                    mixed_integer_x_projection (n := n + p) (p := m) (q := n + q) W) := by
  rcases (is_mixed_integer_linear_representable_on_mixed_integer_point_iff
      (S := S) hS_mixed).1 hrepr with
    ⟨r, m, q, Aint, Areal, B, C, d, hS_eq⟩
  refine ⟨r, m, q, Aint, Areal, B, C, d, ?_⟩
  dsimp
  refine ⟨(is_rational_mixed_polyhedron_iff).2 ?_, ?_⟩
  · refine ⟨r + (n + n),
      copiedIntegerBlockWitnessIntMatrix (n := n) C,
      copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q) Aint Areal B,
      copiedIntegerBlockWitnessRhs (n := n) d, rfl⟩
  · -- Reuse the copied-block witness equivalence already proved above.
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hS_eq] at hx
      exact (copiedIntegerBlockProjection_iff
        (Aint := Aint) (Areal := Areal) (B := B) (C := C) (d := d) (x := x)).2 hx
    · intro hu
      have hu' :
          Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) ∈
            mixed_integer_x_projection
              (n := n + p)
              (p := m)
              (q := n + q)
              (rational_mixed_polyhedron
                (copiedIntegerBlockWitnessIntMatrix (n := n) C)
                (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q)
                  Aint Areal B)
                (copiedIntegerBlockWitnessRhs (n := n) d)) := by
        rw [appendEquiv_symm_apply (n := n) (p := p) u]
        exact hu
      have hx :
          (Fin.appendEquiv n p).symm u ∈ (ℤ^n×ℝ^p) ∧
            ∃ y : Fin m → ℝ,
              ∃ z : Fin q → ℤ,
                ∀ i : Fin r,
                  (∑ j : Fin n, (Aint i j : ℝ) * ((Fin.appendEquiv n p).symm u).1 j) +
                      (∑ j : Fin p, (Areal i j : ℝ) * ((Fin.appendEquiv n p).symm u).2 j) +
                      (∑ j : Fin m, (B i j : ℝ) * y j) +
                      (∑ j : Fin q, (C i j : ℝ) * (z j : ℝ)) ≤
                    (d i : ℝ) := by
        exact (copiedIntegerBlockProjection_iff
          (Aint := Aint) (Areal := Areal) (B := B) (C := C) (d := d)
          (x := (Fin.appendEquiv n p).symm u)).1 hu'
      rw [hS_eq]
      exact ⟨(Fin.appendEquiv n p).symm u, hx, by
        simpa using (Fin.appendEquiv n p).apply_symm_apply u⟩

/-- Helper for Exercise 4.33: the unit box is the convex hull of its `0/1` vertices, hence a
rational polytope. -/
private lemma unitBox_isRationalPolytope
    (n : ℕ) :
    (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).IsRationalPolytope := by
  let e : Fin (Fintype.card (Fin n → Bool)) ≃ (Fin n → Bool) :=
    (Fintype.equivFin (Fin n → Bool)).symm
  let v :
      Fin (Fintype.card (Fin n → Bool)) → Fin n → ℚ := fun i j ↦
        if e i j then 1 else 0
  have hRange :
      Set.range (fun i : Fin (Fintype.card (Fin n → Bool)) ↦ fun j : Fin n ↦ ((v i j : ℚ) : ℝ)) =
        zero_one_cube n := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [mem_zero_one_cube_iff]
      intro j
      by_cases hij : e i j
      · right
        simp [v, hij]
      · left
        simp [v, hij]
    · intro hx
      rw [mem_zero_one_cube_iff] at hx
      let b : Fin n → Bool := fun j ↦ x j = 1
      refine ⟨e.symm b, ?_⟩
      ext j
      have hj := hx j
      by_cases hb : b j
      · have hxj : x j = 1 := by
          simpa [b] using hb
        simp [v, e, b, hb, hxj]
      · have hxj : x j = 0 := by
          rcases hj with h0 | h1
          · exact h0
          · exfalso
            exact hb (by simpa [b, h1])
        simp [v, e, b, hb, hxj]
  have hCompact :
      IsCompact (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)) := by
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hConvex :
      Convex ℝ (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)) := by
    exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1
  have hExtremeFinite :
      ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ).Finite := by
    rw [extremePoints_unit_box_eq_zero_one_cube, ← hRange]
    exact Set.finite_range _
  refine ⟨Fintype.card (Fin n → Bool), v, ?_⟩
  calc
    Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
        = closure (convexHull ℝ ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ)) := by
            simpa using (closure_convexHull_extremePoints hCompact hConvex).symm
    _ = convexHull ℝ ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ) := by
          rw [(hExtremeFinite.isClosed_convexHull ℝ).closure_eq]
    _ = convexHull ℝ (zero_one_cube n) := by
          rw [extremePoints_unit_box_eq_zero_one_cube]
    _ = convexHull ℝ
          (Set.range (fun i : Fin (Fintype.card (Fin n → Bool)) ↦ fun j : Fin n ↦ ((v i j : ℚ) : ℝ))) := by
            rw [← hRange]

/-- Helper for Exercise 4.33: applying a rational linear map to a rational polytope preserves a
rational vertex presentation. -/
private lemma isRationalPolytope_image_rationalMatrixMulVec
    {m n : ℕ}
    {P : Set (Fin m → ℝ)}
    (hP : P.IsRationalPolytope)
    (A : Matrix (Fin n) (Fin m) ℚ) :
    ((fun x : Fin m → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ x) '' P).IsRationalPolytope := by
  rcases hP with ⟨k, v, hv⟩
  let w : Fin k → Fin n → ℚ := fun i ↦ A *ᵥ v i
  have hlin : IsLinearMap ℝ (fun x : Fin m → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ x) := by
    refine ⟨?_, ?_⟩
    · intro x y
      ext i
      simp [Matrix.mulVec_add]
    · intro a x
      ext i
      simp [Matrix.mulVec_smul]
  refine ⟨k, w, ?_⟩
  rw [hv, hlin.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [w, Matrix.mulVec, dotProduct]
  · rintro ⟨i, rfl⟩
    refine ⟨fun j : Fin m ↦ (v i j : ℝ), ⟨i, rfl⟩, ?_⟩
    ext j
    simp [w, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 4.33: Minkowski sums of rational polytopes stay rational. -/
private lemma isRationalPolytope_add
    {n : ℕ}
    {P Q : Set (Fin n → ℝ)}
    (hP : P.IsRationalPolytope)
    (hQ : Q.IsRationalPolytope) :
    (P + Q).IsRationalPolytope := by
  rcases hP with ⟨k, v, hv⟩
  rcases hQ with ⟨l, w, hw⟩
  let e : Fin (Fintype.card (Fin k × Fin l)) ≃ Fin k × Fin l :=
    (Fintype.equivFin (Fin k × Fin l)).symm
  refine ⟨Fintype.card (Fin k × Fin l), fun a i ↦ v (e a).1 i + w (e a).2 i, ?_⟩
  rw [hv, hw, ← convexHull_add]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, z, ⟨j, rfl⟩, rfl⟩
    refine ⟨e.symm (i, j), ?_⟩
    ext s
    simp [e]
  · rintro ⟨a, rfl⟩
    exact
      Set.mem_add.2
        ⟨fun i : Fin n ↦ (v (e a).1 i : ℝ), ⟨(e a).1, rfl⟩,
          fun i : Fin n ↦ (w (e a).2 i : ℝ), ⟨(e a).2, rfl⟩, by
            ext s
            simp [e]⟩

/-- Helper for Exercise 4.33: after flattening `ℤ^q × ℝ^(n+p)` into `ℝ^(q+n+p)`, the visible
`x`-projection drops both the leading integer block and the trailing auxiliary real block. -/
private def flattenedVisibleXProjection
    {n p q : ℕ} (u : Fin (q + (n + p)) → ℝ) : Fin n → ℝ :=
  fun l ↦ u (Fin.natAdd q (Fin.castAdd p l))

/-- Helper for Exercise 4.33: the flattened visible-`x` projection is a linear map. -/
private lemma isLinearMap_flattenedVisibleXProjection
    {n p q : ℕ} :
    IsLinearMap ℝ
      (flattenedVisibleXProjection : (Fin (q + (n + p)) → ℝ) → Fin n → ℝ) := by
  refine ⟨?_, ?_⟩
  · intro u v
    -- The visible coordinates are read coordinatewise from the flattened ambient vector.
    ext l
    simp [flattenedVisibleXProjection]
  · intro a u
    -- Scalar multiplication commutes with taking the visible coordinate block.
    ext l
    simp [flattenedVisibleXProjection]

/-- Helper for Exercise 4.33: projecting a rational polytope in the flattened mixed ambient space
to the visible `x` block preserves rational polyhedrality. -/
private lemma isRationalPolytope_image_flattenedVisibleXProjection
    {n p q : ℕ}
    {Q : Set (Fin (q + (n + p)) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    (flattenedVisibleXProjection '' Q).IsRationalPolytope := by
  rcases hQ with ⟨k, v, hv⟩
  refine ⟨k, fun i l ↦ v i (Fin.natAdd q (Fin.castAdd p l)), ?_⟩
  rw [hv]
  -- Push the visible-coordinate projection through the convex hull of the rational vertex family.
  have hlin : IsLinearMap ℝ
      (flattenedVisibleXProjection : (Fin (q + (n + p)) → ℝ) → Fin n → ℝ) :=
    isLinearMap_flattenedVisibleXProjection
  rw [hlin.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(fun j : Fin (q + (n + p)) ↦ (v i j : ℝ)), ⟨i, rfl⟩, rfl⟩

/-- Helper for Exercise 4.33: the canonical `mixed_integer_x_projection` is exactly the image of
the flattened mixed-integer points under `flattenedVisibleXProjection`. -/
private lemma flattenedVisibleXProjection_image_mixedIntegerPoints_eq
    {n p q : ℕ}
    (P : Set (MixedRealPoint q (n + p))) :
    flattenedVisibleXProjection '' (Fin.appendEquiv q (n + p) '' mixed_integer_points P) =
      mixed_integer_x_projection P := by
  ext x
  constructor
  · rintro ⟨u, ⟨wz, hwz, rfl⟩, rfl⟩
    -- Read the flattened witness back in mixed coordinates and keep only the visible `x` block.
    exact ⟨wz, hwz, by
      ext l
      simp [flattenedVisibleXProjection, Fin.appendEquiv]⟩
  · rintro ⟨wz, hwz, rfl⟩
    -- Flatten the mixed-space witness and observe that the visible coordinates are unchanged.
    refine ⟨Fin.appendEquiv q (n + p) wz, ⟨wz, hwz, rfl⟩, ?_⟩
    ext l
    simp [flattenedVisibleXProjection, Fin.appendEquiv]

/-- Helper for Exercise 4.33: projecting a flattened finite union plus one integral cone to the
visible `x` block preserves the finite union and drops the invisible coordinates of every ray. -/
private lemma flattenedVisibleXProjection_image_iUnion_add_integral_intcone_eq
    {n p q k t : ℕ}
    (Q : Fin k → Set (Fin (q + (n + p)) → ℝ))
    (r : Fin t → Fin (q + (n + p)) → ℤ) :
    flattenedVisibleXProjection '' ((⋃ i : Fin k, Q i) + integral_intcone r) =
      (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
        integral_intcone
          (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases Set.mem_add.1 hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    rcases Set.mem_iUnion.1 hu₁ with ⟨i, hui⟩
    rcases (mem_integral_intcone_iff).1 hu₂ with ⟨a, rfl⟩
    refine Set.mem_add.2 ⟨flattenedVisibleXProjection u₁, ?_, ?_, ?_, ?_⟩
    · -- The visible `x` block of the chosen piece stays in the projected finite union.
      exact Set.mem_iUnion.2 ⟨i, ⟨u₁, hui, rfl⟩⟩
    · exact ∑ j : Fin t, (a j : ℝ) •
        (fun l : Fin n ↦ (r j (Fin.natAdd q (Fin.castAdd p l)) : ℝ))
    · -- Projecting the cone combination simply projects each integral ray.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- The visible coordinates distribute across the sum of the piece and cone parts.
      ext l
      simp [flattenedVisibleXProjection, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rcases Set.mem_iUnion.1 hx₁ with ⟨i, hxi⟩
    rcases hxi with ⟨u₁, hu₁, rfl⟩
    rcases (mem_integral_intcone_iff).1 hx₂ with ⟨a, rfl⟩
    let u₂ : Fin (q + (n + p)) → ℝ :=
      ∑ j : Fin t, (a j : ℝ) • (fun idx : Fin (q + (n + p)) ↦ (r j idx : ℝ))
    refine ⟨u₁ + u₂, Set.mem_add.2 ⟨u₁, Set.mem_iUnion.2 ⟨i, hu₁⟩, u₂, ?_, rfl⟩, ?_⟩
    · -- Reinflate the projected cone witness by restoring the dropped coordinates of each ray.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- After reinflating the rays, taking the visible `x` block returns the prescribed sum.
      ext l
      simp [flattenedVisibleXProjection, u₂, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 4.33: once the mixed-integer points are decomposed on the flattened
ambient space, one final visible-`x` projection yields the desired union of rational pieces plus
the projected integral cone. -/
private lemma xProjection_transport_ofFlattenedDecomposition
    {n p q k t : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {Q : Fin k → Set (Fin (q + (n + p)) → ℝ)}
    {r : Fin t → Fin (q + (n + p)) → ℤ}
    (hdecomp :
      Fin.appendEquiv q (n + p) '' mixed_integer_points P =
        (⋃ i : Fin k, Q i) + integral_intcone r) :
    mixed_integer_x_projection P =
      (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
        integral_intcone
          (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
  -- Compare the canonical `mixed_integer_x_projection` to the same flattened witness surface,
  -- then project the finite union and cone in one step.
  calc
    mixed_integer_x_projection P =
        flattenedVisibleXProjection '' (Fin.appendEquiv q (n + p) '' mixed_integer_points P) := by
          symm
          exact flattenedVisibleXProjection_image_mixedIntegerPoints_eq P
    _ = flattenedVisibleXProjection '' ((⋃ i : Fin k, Q i) + integral_intcone r) := by
          rw [hdecomp]
    _ = (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
          integral_intcone
            (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
          exact flattenedVisibleXProjection_image_iUnion_add_integral_intcone_eq Q r

/-- Helper for Exercise 4.33: flattening by `Fin.appendEquiv` is linear on mixed real points. -/
private lemma appendEquivIsLinearMap
    {n p : ℕ} :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for Exercise 4.33: a singleton-weighted finite sum collapses to its active coordinate.
-/
private lemma sumCastIteMul_eq_active
    {k : ℕ}
    (f : Fin k → ℝ)
    (i : Fin k)
    (c : ℚ) :
    ∑ j : Fin k, (((if j = i then c else 0 : ℚ) : ℝ) * f j) = (c : ℝ) * f i := by
  -- Only the selected coordinate survives the singleton coefficient family.
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Helper for Exercise 4.33: flattening by `Fin.appendEquiv` rewrites mixed-integer membership as
ambient flattened membership together with integrality of the first block. -/
private lemma memFlatMixedIntegerPoints_iff
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    {u : Fin (n + p) → ℝ} :
    u ∈ (Fin.appendEquiv n p '' mixed_integer_points P) ↔
      u ∈ (Fin.appendEquiv n p '' P) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    -- Unpack flattened mixed-integer membership into ambient membership and integrality
    -- of the first block.
    rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hP, hxy_lattice⟩
    constructor
    · exact ⟨xy, hP, rfl⟩
    · rw [mem_mixed_integer_lattice_iff] at hxy_lattice
      simpa using hxy_lattice
  · rintro ⟨huP, huInt⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    -- The flattened integrality condition is exactly the mixed-lattice condition on `xy`.
    refine ⟨xy, ?_, rfl⟩
    refine (mem_mixed_integer_points_iff).2 ⟨hxyP, ?_⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa using huInt

/-- Helper for Exercise 4.33: the flattened points whose first `n` coordinates are integral. -/
private def firstBlockIntegerSet
    {n p : ℕ} : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n}

/-- Helper for Exercise 4.33: the sum of two integer vectors is again an integer vector. -/
private lemma integerVectors_add_mem
    {n : ℕ}
    {u v : Fin n → ℝ}
    (hu : u ∈ integerVectors n)
    (hv : v ∈ integerVectors n) :
    u + v ∈ integerVectors n := by
  rcases (mem_integerVectors_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integerVectors_iff).1 hv with ⟨b, rfl⟩
  -- Add the underlying integer witnesses coordinatewise before casting back to `ℝ`.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ a i + b i, ?_⟩
  funext i
  simp

/-- Helper for Exercise 4.33: subtracting one integer vector from another keeps the result in the
integer lattice. -/
private lemma integerVectors_sub_mem
    {n : ℕ}
    {u v : Fin n → ℝ}
    (hu : u ∈ integerVectors n)
    (hv : v ∈ integerVectors n) :
    u - v ∈ integerVectors n := by
  rcases (mem_integerVectors_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integerVectors_iff).1 hv with ⟨b, rfl⟩
  -- Subtract the integer witnesses coordinatewise before casting to the ambient real space.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ a i - b i, ?_⟩
  funext i
  simp

/-- Helper for Exercise 4.33: every element of `integral_intcone r` has integral first block after
flattening. -/
private lemma firstBlock_mem_integerVectors_of_mem_integralIntcone
    {n p q : ℕ}
    {r : Fin q → Fin (n + p) → ℤ}
    {u : Fin (n + p) → ℝ}
    (hu : u ∈ integral_intcone r) :
    (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  -- The first block is a finite integer linear combination of the integral ray coordinates.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ ∑ j : Fin q, (a j : ℤ) * r j (Fin.castAdd p i), ?_⟩
  funext i
  simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 4.33: once the flattened ambient set is in the normal form
`Q + integral_intcone r`, the flattened mixed-integer points are exactly the integer slice of `Q`
translated by the same integral cone. -/
private lemma flatMixedIntegerPoints_eq_baseSlice_add_integralIntcone
    {n p q : ℕ}
    {P : Set (MixedRealPoint n p)}
    {Q : Set (Fin (n + p) → ℝ)}
    {r : Fin q → Fin (n + p) → ℤ}
    (hdecomp : Fin.appendEquiv n p '' P = Q + integral_intcone r) :
    Fin.appendEquiv n p '' mixed_integer_points P =
      (Q ∩ firstBlockIntegerSet) + integral_intcone r := by
  ext u
  constructor
  · intro hu
    rcases (memFlatMixedIntegerPoints_iff).1 hu with ⟨huP, huInt⟩
    rw [hdecomp] at huP
    rcases Set.mem_add.1 huP with ⟨q, hqQ, c, hc, rfl⟩
    refine Set.mem_add.2 ⟨q, ?_, c, hc, rfl⟩
    refine ⟨hqQ, ?_⟩
    have hqcInt :
        (fun i : Fin n ↦ (q + c) (Fin.castAdd p i)) ∈ integerVectors n := by
      simpa [firstBlockIntegerSet] using huInt
    have hcInt :
        (fun i : Fin n ↦ c (Fin.castAdd p i)) ∈ integerVectors n :=
      firstBlock_mem_integerVectors_of_mem_integralIntcone hc
    -- Subtract the integral cone contribution to recover an integral first block for `q`.
    have hqEq :
        (fun i : Fin n ↦ q (Fin.castAdd p i)) =
          (fun i : Fin n ↦ (q + c) (Fin.castAdd p i)) -
            fun i : Fin n ↦ c (Fin.castAdd p i) := by
      funext i
      simp [Pi.sub_apply]
    have hqInt :
        (fun i : Fin n ↦ q (Fin.castAdd p i)) ∈ integerVectors n := by
      rw [hqEq]
      exact integerVectors_sub_mem hqcInt hcInt
    simpa [firstBlockIntegerSet] using hqInt
  · intro hu
    rcases Set.mem_add.1 hu with ⟨q, hq, c, hc, rfl⟩
    rcases hq with ⟨hqQ, hqInt⟩
    refine (memFlatMixedIntegerPoints_iff).2 ?_
    refine ⟨?_, ?_⟩
    · rw [hdecomp]
      exact Set.mem_add.2 ⟨q, hqQ, c, hc, rfl⟩
    · have hcInt :
          (fun i : Fin n ↦ c (Fin.castAdd p i)) ∈ integerVectors n :=
        firstBlock_mem_integerVectors_of_mem_integralIntcone hc
      have hqInt' :
          (fun i : Fin n ↦ q (Fin.castAdd p i)) ∈ integerVectors n := by
        simpa [firstBlockIntegerSet] using hqInt
      -- Add the integral cone contribution back to the integer slice of `Q`.
      simpa [Pi.add_apply] using integerVectors_add_mem hqInt' hcInt

/-- Helper for Exercise 4.33: a rational polytope has a uniform integer bound on its first block.
-/
private lemma boundedFirstBlockCoordinates_of_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    ∃ B : ℤ,
      ∀ ⦃u : Fin (n + p) → ℝ⦄, u ∈ Q → ∀ i : Fin n,
        (-(B : ℝ)) ≤ u (Fin.castAdd p i) ∧ u (Fin.castAdd p i) ≤ (B : ℝ) := by
  rcases hQ with ⟨k, v, hVeq⟩
  have hQ_bounded : Bornology.IsBounded Q := by
    -- Rational polytopes are bounded because they are finite convex hulls.
    simpa [hVeq] using (isBounded_convexHull).2 (Set.finite_range _).isBounded
  obtain ⟨R, hR⟩ := hQ_bounded.subset_closedBall (0 : Fin (n + p) → ℝ)
  let Bnat : ℕ := Nat.ceil R
  refine ⟨Bnat, ?_⟩
  intro u hu i
  have huBall : u ∈ Metric.closedBall (0 : Fin (n + p) → ℝ) R := hR hu
  have huNorm : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using huBall
  have hcoord_le_norm : |u (Fin.castAdd p i)| ≤ ‖u‖ := by
    -- A coordinate norm is bounded by the sup norm on a finite product.
    have hcoord_le_sup_nnreal :
        ‖u (Fin.castAdd p i)‖₊ ≤
          (Finset.univ : Finset (Fin (n + p))).sup (fun b : Fin (n + p) => ‖u b‖₊) := by
      simpa using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin (n + p))))
          (f := fun b : Fin (n + p) => ‖u b‖₊)
          (b := Fin.castAdd p i)
          (Finset.mem_univ (Fin.castAdd p i)))
    have hcoord_le_sup :
        ‖u (Fin.castAdd p i)‖ ≤ ↑(Finset.univ.sup fun b => ‖u b‖₊) := by
      exact_mod_cast hcoord_le_sup_nnreal
    have hcoord_le_norm' : ‖u (Fin.castAdd p i)‖ ≤ ‖u‖ := by
      simpa [Pi.norm_def'] using hcoord_le_sup
    simpa [Real.norm_eq_abs] using hcoord_le_norm'
  have hcoord_le_R : |u (Fin.castAdd p i)| ≤ R := le_trans hcoord_le_norm huNorm
  have hR_le_ceil : R ≤ Bnat := by
    simpa using (Nat.le_ceil R)
  have hcoord_le_Bnat : |u (Fin.castAdd p i)| ≤ (Bnat : ℝ) := by
    exact le_trans hcoord_le_R hR_le_ceil
  have hcoord_abs : |u (Fin.castAdd p i)| ≤ (Bnat : ℝ) := hcoord_le_Bnat
  constructor
  · exact (abs_le.mp hcoord_abs).1
  · exact (abs_le.mp hcoord_abs).2

/-- Helper for Exercise 4.33: fixing the first `n` coordinates to one integer vector defines the
corresponding coordinate fiber. -/
private def firstBlockFiber
    {n p : ℕ}
    (z : Fin n → ℤ) : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) = Int.cast ∘ z}

/-- Helper for Exercise 4.33: a nonempty bounded rational matrix polyhedron is a rational
polytope. -/
private lemma rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {b : Fin m → ℚ}
    (hP_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (hP_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b)) :
    (rational_matrix_polyhedron A b).IsRationalPolytope := by
  classical
  let P : Set (Fin n → ℝ) := rational_matrix_polyhedron A b
  have hP_polyhedron : is_polyhedron P := by
    -- Re-express the rational system as an ordinary real polyhedron.
    refine (is_polyhedron_iff).2 ?_
    exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩
  rcases (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 hP_polyhedron with
    ⟨Q, hQ_polytope, q, rays, hP_repr⟩
  rcases hQ_polytope with ⟨V, hV_finite, hQ_eq⟩
  have hQ_polytope' : Q.IsPolytope ℝ := ⟨V, hV_finite, hQ_eq⟩
  obtain ⟨p, vertex, -, hV_range⟩ := hV_finite.fin_param
  have hP_rec_zero : recessionCone P = ({0} : Set (Fin n → ℝ)) :=
    recessionConeEqSingletonZeroOfNonemptyBounded hP_nonempty hP_bounded
  have hP_rec_rays :
      recessionCone P = finitely_generated_cone rays := by
    -- Route correction: compute the recession cone from the `polytope + cone` normal form first,
    -- then collapse the cone using boundedness instead of importing an extra owner.
    have hP_repr' :
        P = convexHull ℝ (Set.range vertex) + finitely_generated_cone rays := by
      calc
        P = Q + finitely_generated_cone rays := hP_repr
        _ = convexHull ℝ V + finitely_generated_cone rays := by rw [hQ_eq]
        _ = convexHull ℝ (Set.range vertex) + finitely_generated_cone rays := by rw [hV_range]
    exact
      polyhedron_recessionCone_eq_finitely_generated_cone
        (A := A.map (Rat.castHom ℝ))
        (b := fun i ↦ (b i : ℝ))
        vertex
        rays
        hP_nonempty
        (by simpa [P] using hP_repr')
  have hcone_zero : finitely_generated_cone rays = ({0} : Set (Fin n → ℝ)) := by
    calc
      finitely_generated_cone rays = recessionCone P := hP_rec_rays.symm
      _ = ({0} : Set (Fin n → ℝ)) := hP_rec_zero
  have hP_eq_Q : P = Q := by
    -- Once the recession cone vanishes, the polyhedron is exactly its bounded polytope part.
    calc
      P = Q + finitely_generated_cone rays := hP_repr
      _ = Q + ({0} : Set (Fin n → ℝ)) := by rw [hcone_zero]
      _ = Q := add_singleton_zero_eq
  have hP_polytope : P.IsPolytope ℝ := by
    simpa [hP_eq_Q] using hQ_polytope'
  rcases hP_polytope with ⟨Vpoly, hVpoly_finite, hP_hull⟩
  have hP_compact : IsCompact P := by
    -- A polytope is compact because it is the convex hull of finitely many points.
    rw [hP_hull]
    exact hVpoly_finite.isCompact_convexHull ℝ
  have hP_convex : Convex ℝ P := by
    rw [hP_hull]
    exact convex_convexHull ℝ Vpoly
  have hPext_subset :
      P.extremePoints ℝ ⊆ Vpoly := by
    intro x hx
    rw [hP_hull] at hx
    exact extremePoints_convexHull_subset hx
  have hPext_finite : (P.extremePoints ℝ).Finite :=
    hVpoly_finite.subset hPext_subset
  have hP_eq_convexHull_extreme :
      P = convexHull ℝ (P.extremePoints ℝ) := by
    have hclosure := closure_convexHull_extremePoints hP_compact hP_convex
    calc
      P = closure (convexHull ℝ (P.extremePoints ℝ)) := by
            simpa using hclosure.symm
      _ = convexHull ℝ (P.extremePoints ℝ) := by
            exact (hPext_finite.isClosed_convexHull ℝ).closure_eq
  obtain ⟨t, xext, -, hxext_range⟩ := hPext_finite.fin_param
  let L : ℕ :=
    (∑ i : Fin m, ∑ j : Fin n, EncodingSize.rational (A i j)) +
      ∑ i : Fin m, EncodingSize.rational (b i)
  have hA_bound : ∀ i j, EncodingSize.rational (A i j) ≤ L := by
    intro i j
    have hij :
        EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := by
      exact Finset.single_le_sum
        (fun j' _ ↦ Nat.zero_le (EncodingSize.rational (A i j')))
        (Finset.mem_univ j)
    have hii :
        ∑ j' : Fin n, EncodingSize.rational (A i j') ≤
          ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (∑ j' : Fin n, EncodingSize.rational (A i' j')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := hij
      _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := hii
      _ ≤ L := Nat.le.intro rfl
  have hb_bound : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L := by
    intro i
    have hi :
        EncodingSize.rational (b i) ≤
          ∑ i' : Fin m, EncodingSize.rational (b i') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (EncodingSize.rational (b i')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (b i) ≤ ∑ i' : Fin m, EncodingSize.rational (b i') := hi
      _ ≤ L := Nat.le_add_left _ _
  obtain ⟨π, hπ⟩ := rational_vertices_have_polynomially_bounded_encoding_size
  choose vertexQ hvertexQ_eq hvertexQ_bound using
    fun i : Fin t ↦ by
      have hxext_mem : xext i ∈ P.extremePoints ℝ := by
        rw [← hxext_range]
        exact Set.mem_range_self i
      exact hπ A b L hA_bound hb_bound (xext i) hxext_mem
  refine ⟨t, vertexQ, ?_⟩
  have hvertexQ_range :
      Set.range (fun i : Fin t ↦ fun j : Fin n ↦ (vertexQ i j : ℝ)) = P.extremePoints ℝ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [← hxext_range]
      exact ⟨i, hvertexQ_eq i⟩
    · intro hx
      rw [← hxext_range] at hx
      rcases hx with ⟨i, rfl⟩
      exact ⟨i, (hvertexQ_eq i).symm⟩
  -- Replace the compact convex polyhedron by the convex hull of its rational extreme points.
  calc
    P = convexHull ℝ (P.extremePoints ℝ) := hP_eq_convexHull_extreme
    _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun j : Fin n ↦ (vertexQ i j : ℝ)) := by
          rw [← hvertexQ_range]

/-- Helper for Exercise 4.33: a selector row supported on the first block recovers the chosen
coordinate. -/
private lemma sumFirstBlockSelectorRow_eq_active
    {n p : ℕ}
    (u : Fin (n + p) → ℝ)
    (i : Fin n)
    (c : ℚ) :
    ∑ j : Fin (n + p),
        (((Fin.append
            (fun l : Fin n ↦ if l = i then c else 0)
            (fun _ : Fin p ↦ 0) j : ℚ) : ℝ) * u j) =
      (c : ℝ) * u (Fin.castAdd p i) := by
  -- Split the flattened coordinates into the first block and the tail block before collapsing
  -- the singleton selector.
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]
  simpa using sumCastIteMul_eq_active (f := fun l : Fin n ↦ u (Fin.castAdd p l)) i c

/-- Helper for Exercise 4.33: augmenting a rational matrix presentation by paired `±Id` rows on
the first block uses the negated selected integer on the lower right-hand side. -/
private lemma firstBlockFiberAugmentedRhs_lower_apply
    {n m : ℕ}
    (b : Fin m → ℚ)
    (z : Fin n → ℤ)
    (i : Fin n) :
    ((Fin.addCases b
        (Fin.addCases (fun i' : Fin n ↦ (z i' : ℚ)) (fun i' : Fin n ↦ -(z i' : ℚ)))
        (Fin.natAdd m (Fin.natAdd n i)) : ℚ) : ℝ) =
      -(z i : ℝ) := by
  -- The lower augmented row sits in the negative copy of the first-block equality system.
  change
    (((Fin.addCases b
        (Fin.addCases (fun i' ↦ (z i' : ℚ)) (fun i' ↦ -(z i' : ℚ)))
        (Fin.natAdd m (Fin.natAdd n i)) : ℚ) : ℝ)) =
      -(z i : ℝ)
  rw [Fin.addCases_right]
  show
    (((Fin.addCases (fun i' ↦ (z i' : ℚ)) (fun i' ↦ -(z i' : ℚ))
        (Fin.natAdd n i) : ℚ) : ℝ)) =
      -(z i : ℝ)
  rw [Fin.addCases_right]
  simp

/-- Helper for Exercise 4.33: augmenting a rational matrix presentation by paired `±Id` rows on
the first block cuts out the fixed-first-block fiber. -/
private lemma firstBlockFiber_eq_rationalMatrixPolyhedron
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope)
    (z : Fin n → ℤ) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin (n + p)) ℚ,
        ∃ b : Fin m → ℚ,
          Q ∩ firstBlockFiber z = rational_matrix_polyhedron A b := by
  rcases rationalPolytopeEqRationalMatrixPolyhedron hQ with ⟨m, A, b, hQeq⟩
  let A' : Matrix (Fin (m + (n + n))) (Fin (n + p)) ℚ :=
    fun i ↦
      Fin.addCases
        A
        (Fin.addCases
          (fun i' ↦ Fin.append (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0))
          (fun i' ↦ Fin.append (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0)))
        i
  let b' : Fin (m + (n + n)) → ℚ :=
    fun i ↦
      Fin.addCases
        b
        (Fin.addCases
          (fun i' ↦ z i')
          (fun i' ↦ -(z i')))
        i
  refine ⟨m + (n + n), A', b', ?_⟩
  ext u
  constructor
  · intro hu
    rcases hu with ⟨huQ, huFiber⟩
    rw [hQeq, mem_rational_matrix_polyhedron] at huQ
    rw [mem_rational_matrix_polyhedron]
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro s
      have hrow :
          (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.castAdd (n + n) s)) =
            (((A.map (Rat.castHom ℝ)) *ᵥ u) s) := by
        simp [A', Matrix.mulVec, dotProduct]
      rw [hrow]
      simpa [hQeq, b'] using huQ s
    · intro row'
      refine Fin.addCases ?_ ?_ row'
      · intro i
        have hi : u (Fin.castAdd p i) = (z i : ℝ) := by
          simpa [firstBlockFiber, Function.comp] using congrFun huFiber i
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.castAdd n i))) =
              u (Fin.castAdd p i) := by
          simpa [A', Matrix.mulVec, dotProduct, Fin.sum_univ_add] using
            sumFirstBlockSelectorRow_eq_active u i 1
        rw [hrow]
        simpa [b', hi]
      · intro i
        have hi : u (Fin.castAdd p i) = (z i : ℝ) := by
          simpa [firstBlockFiber, Function.comp] using congrFun huFiber i
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.natAdd n i))) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          have hcoeffLeft :
              ∀ j : Fin n,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.castAdd p j)) : ℝ) =
                  if j = i then (-1 : ℝ) else 0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            by_cases h : j = i <;> simp [h]
          have hcoeffRight :
              ∀ j : Fin p,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.natAdd n j)) : ℝ) =
                  0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            simp
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
          simp_rw [hcoeffLeft, hcoeffRight]
          simpa using sumCastIteMul_eq_active (f := fun l : Fin n ↦ u (Fin.castAdd p l)) i (-1)
        rw [hrow]
        have hb :
            (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) = -(z i : ℝ) := by
          simpa [b'] using firstBlockFiberAugmentedRhs_lower_apply (b := b) z i
        change (-1 : ℝ) * u (Fin.castAdd p i) ≤ (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ)
        rw [hb, hi]
        simp
  · intro hu
    rw [mem_rational_matrix_polyhedron] at hu
    refine ⟨?_, ?_⟩
    · rw [hQeq, mem_rational_matrix_polyhedron]
      intro s
      have hrow :
          (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.castAdd (n + n) s)) =
            (((A.map (Rat.castHom ℝ)) *ᵥ u) s) := by
        simp [A', Matrix.mulVec, dotProduct]
      rw [← hrow]
      simpa [b'] using hu (Fin.castAdd (n + n) s)
    · ext i
      have hupper := hu (Fin.natAdd m (Fin.castAdd n i))
      have hlower := hu (Fin.natAdd m (Fin.natAdd n i))
      have hupper' : u (Fin.castAdd p i) ≤ (z i : ℝ) := by
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.castAdd n i))) =
              u (Fin.castAdd p i) := by
          simpa [A', Matrix.mulVec, dotProduct, Fin.sum_univ_add] using
            sumFirstBlockSelectorRow_eq_active u i 1
        rw [hrow] at hupper
        simpa [b'] using hupper
      have hlower' : (-1 : ℝ) * u (Fin.castAdd p i) ≤ -(z i : ℝ) := by
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.natAdd n i))) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          have hcoeffLeft :
              ∀ j : Fin n,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.castAdd p j)) : ℝ) =
                  if j = i then (-1 : ℝ) else 0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            by_cases h : j = i <;> simp [h]
          have hcoeffRight :
              ∀ j : Fin p,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.natAdd n j)) : ℝ) =
                  0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            simp
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
          simp_rw [hcoeffLeft, hcoeffRight]
          simpa using sumCastIteMul_eq_active (f := fun l : Fin n ↦ u (Fin.castAdd p l)) i (-1)
        rw [hrow] at hlower
        have hb :
            (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) = -(z i : ℝ) := by
          simpa [b'] using firstBlockFiberAugmentedRhs_lower_apply (b := b) z i
        change (-1 : ℝ) * u (Fin.castAdd p i) ≤ (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) at hlower
        rw [hb] at hlower
        simpa using hlower
      have hlower'' : (z i : ℝ) ≤ u (Fin.castAdd p i) := by
        linarith
      exact le_antisymm hupper' hlower''

/-- Helper for Exercise 4.33: every fixed-first-block fiber of a rational polytope is again a
rational polytope. -/
private lemma firstBlockFiber_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope)
    (z : Fin n → ℤ) :
    (Q ∩ firstBlockFiber z).IsRationalPolytope := by
  classical
  by_cases hFiber_nonempty : (Q ∩ firstBlockFiber z).Nonempty
  · rcases firstBlockFiber_eq_rationalMatrixPolyhedron hQ z with ⟨m, A, b, hFiber_eq⟩
    have hQ_bounded : Bornology.IsBounded Q := isBoundedOfIsRationalPolytope hQ
    have hFiber_bounded : Bornology.IsBounded (Q ∩ firstBlockFiber z) := by
      exact hQ_bounded.subset (by
        intro u hu
        exact hu.1)
    -- Route correction: for a fixed first-block fiber, boundedness already kills the recession
    -- cone, so we can prove rational polyhedrality directly.
    have hFiber_nonempty_matrix : (rational_matrix_polyhedron A b).Nonempty := by
      rw [← hFiber_eq]
      exact hFiber_nonempty
    have hFiber_bounded_matrix : Bornology.IsBounded (rational_matrix_polyhedron A b) := by
      rw [← hFiber_eq]
      exact hFiber_bounded
    simpa [hFiber_eq] using
      rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
        hFiber_nonempty_matrix
        hFiber_bounded_matrix
  · have hFiber_empty : Q ∩ firstBlockFiber z = ∅ := Set.not_nonempty_iff_eq_empty.mp hFiber_nonempty
    -- The empty fiber is the convex hull of the empty rational vertex family.
    refine ⟨0, Fin.elim0, ?_⟩
    simpa [hFiber_empty]

/-- Helper for Exercise 4.33: the integer slice of one rational polytope is a finite union of
fixed-first-block rational-polytopal fibers. -/
private lemma existsRationalPolytopeFirstBlockIntegerSlices
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    ∃ K : ℕ,
      ∃ Qs : Fin K → Set (Fin (n + p) → ℝ),
        (∀ j : Fin K, (Qs j).IsRationalPolytope) ∧
          (Q ∩ firstBlockIntegerSet = ⋃ j : Fin K, Qs j) := by
  classical
  obtain ⟨B, hB⟩ := boundedFirstBlockCoordinates_of_isRationalPolytope hQ
  let box : Set (Fin n → ℤ) := {ρ | ∀ i : Fin n, ρ i ∈ Set.Icc (-B) B}
  have hboxFinite : box.Finite := by
    -- Enumerate all bounded integer first blocks coordinatewise.
    simpa [box, Set.pi] using
      (Set.Finite.pi' (t := fun i : Fin n ↦ Set.Icc (-B) B)
        fun i ↦ Set.finite_Icc (-B) B)
  obtain ⟨K, z, hz_inj, hz_range⟩ := hboxFinite.fin_param
  let Qs : Fin K → Set (Fin (n + p) → ℝ) := fun j ↦ Q ∩ firstBlockFiber (z j)
  refine ⟨K, Qs, ?_, ?_⟩
  · intro j
    -- Each enumerated first-block slice is a rational polytope.
    exact firstBlockFiber_isRationalPolytope hQ (z j)
  · -- Enumerate bounded integer first blocks of one piece and only then aggregate them.
    ext u
    constructor
    · intro hu
      rcases hu with ⟨huQ, huInt⟩
      have huInt' : (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
        simpa [firstBlockIntegerSet] using huInt
      rcases (mem_integerVectors_iff).1 huInt' with ⟨ρ, hρ⟩
      have hρ_box : ∀ i : Fin n, ρ i ∈ Set.Icc (-B) B := by
        intro i
        have hcoord := hB huQ i
        have hcoordEq : u (Fin.castAdd p i) = (ρ i : ℝ) := by
          simpa [Function.comp] using congrFun hρ i
        constructor
        · have hlow : (-(B : ℝ)) ≤ (ρ i : ℝ) := by
            simpa [hcoordEq] using hcoord.1
          exact_mod_cast hlow
        · have hupp : (ρ i : ℝ) ≤ (B : ℝ) := by
            simpa [hcoordEq] using hcoord.2
          exact_mod_cast hupp
      have hρ_mem : ρ ∈ box := hρ_box
      rw [← hz_range] at hρ_mem
      rcases hρ_mem with ⟨j, hj⟩
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine ⟨huQ, ?_⟩
      simpa [Qs, firstBlockFiber, Function.comp, hj] using hρ
    · intro hu
      rcases Set.mem_iUnion.1 hu with ⟨j, huj⟩
      rcases huj with ⟨huQ, huFiber⟩
      refine ⟨huQ, ?_⟩
      have huInt :
          (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
        refine (mem_integerVectors_iff).2 ⟨z j, ?_⟩
        simpa [Qs, firstBlockFiber, Function.comp] using huFiber
      simpa [firstBlockIntegerSet] using huInt

/-- Helper for Exercise 4.33: a nonempty rational mixed polyhedron admits one flattened rational
matrix presentation together with the corresponding homogeneous recession system. -/
private lemma exists_flattened_recession_system_of_nonempty
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hP_nonempty : Set.Nonempty P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin (n + p)) ℚ, ∃ b : Fin m → ℚ,
      ((Fin.appendEquiv n p) '' P) =
        polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
      recessionCone ((Fin.appendEquiv n p) '' P) =
        {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
  let Pflat : Set (Fin (n + p) → ℝ) := (Fin.appendEquiv n p) '' P
  have hPflat : is_rational_polyhedron Pflat := by
    simpa [Pflat] using hP
  rcases hPflat with ⟨m, A, b, hPflat_eq⟩
  have hPflat_nonempty : Set.Nonempty Pflat := by
    rcases hP_nonempty with ⟨xy, hxy⟩
    exact ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩⟩
  have hrec_hom :
      recessionCone Pflat =
        {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
    -- Pin down the recession cone first, before any truncation or vertex work.
    calc
      recessionCone Pflat
          = recessionCone
              (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
                rw [hPflat_eq]
      _ = {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
            exact
              polyhedron_recessionCone_eq_homogeneous_solution_set
                (A.map (Rat.castHom ℝ))
                (fun i ↦ (b i : ℝ))
                (by simpa [hPflat_eq] using hPflat_nonempty)
  exact ⟨m, A, b, hPflat_eq, by simpa [Pflat] using hrec_hom⟩

/-- Helper for Exercise 4.33: the common denominator of a rational vector is always nonzero. -/
private lemma rationalVectorCommonDenominator_ne_zero
    {k : ℕ} (v : Fin k → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  simpa [rational_vector_common_denominator] using
    (Finset.lcm_ne_zero_iff.2 (by
      intro i hi
      exact Nat.ne_of_gt (Rat.den_pos (v i))))

/-- Helper for Exercise 4.33: clearing a rational vector's common denominator gives the same
vector after scalar extension to `ℝ`, up to the obvious positive scalar. -/
private lemma commonDenominatorScaledVector_eq_smulReal
    {k : ℕ}
    (v : Fin k → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  ext i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
      (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  have hi :
      ((common_denominator_scaled_vector v i : ℤ) : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul v) i
  exact_mod_cast hi

/-- Helper for Exercise 4.33: clearing denominators on every rational ray does not change the
generated cone. -/
private lemma commonDenominatorScaledRays_eq_finitely_generated_cone
    {k q : ℕ}
    (r : Fin q → Fin k → ℚ) :
    finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j * (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · intro j
      exact mul_nonneg (hμ_nonneg j) (hD_nonneg j)
    · calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) :=
              hrepr
        _ = ∑ j : Fin q,
              (μ j * (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ (r j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smulReal (v := r j), smul_smul]
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    have hD_ne_zero :
        ∀ j : Fin q, (rational_vector_common_denominator (r j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast rationalVectorCommonDenominator_ne_zero (r j)
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j / (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · intro j
      exact div_nonneg (hμ_nonneg j) (hD_nonneg j)
    · calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j / (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smulReal (v := r j), smul_smul,
                div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hD_ne_zero j), mul_one]

/-- Helper for Exercise 4.33: a nonempty flattened rational mixed polyhedron admits finitely many
integral generators for its recession cone. -/
private lemma existsFlattenedIntegralRecessionGenerators
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hP_nonempty : Set.Nonempty P) :
    ∃ q : ℕ,
      ∃ rays : Fin q → Fin (n + p) → ℤ,
        recessionCone ((Fin.appendEquiv n p) '' P) =
          finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (rays j i : ℝ)) := by
  rcases exists_flattened_recession_system_of_nonempty (P := P) hP hP_nonempty with
    ⟨m, A, b, -, hrec_hom⟩
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin (n + p) → ℚ := fun j i ↦ R i j
  let raysInt : Fin q → Fin (n + p) → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, raysInt, ?_⟩
  -- Normalize the homogeneous rational system to a rational matrix cone, then clear
  -- denominators on each rational generator once and for all.
  calc
    recessionCone ((Fin.appendEquiv n p) '' P)
        = matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
            simpa [matrix_polyhedral_cone] using hrec_hom
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin (n + p) → ℝ)) := hR
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysInt j i : ℝ)) := by
          simpa [raysInt, raysQ] using
            (commonDenominatorScaledRays_eq_finitely_generated_cone
              (r := raysQ)).symm

/-- Helper for Exercise 4.33: the coefficient unit box is a rational polytope. -/
private lemma coefficientUnitBox_isRationalPolytope
    (q : ℕ) :
    (Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)).IsRationalPolytope :=
  unitBox_isRationalPolytope q

/-- Helper for Exercise 4.33: the fractional coefficient box for an integral ray family is the
image of the unit box under the corresponding rational linear map. -/
private def fractionalRayBox
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    Set (Fin k → ℝ) :=
  (fun μ : Fin q → ℝ ↦ ∑ j : Fin q, μ j • (fun i : Fin k ↦ (rays j i : ℝ))) ''
    Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)

/-- Helper for Exercise 4.33: the fractional coefficient box of an integral ray family is a
rational polytope. -/
private lemma fractionalRayBox_isRationalPolytope
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    (fractionalRayBox rays).IsRationalPolytope := by
  let A : Matrix (Fin k) (Fin q) ℚ := fun i j ↦ (rays j i : ℚ)
  have himage :
      fractionalRayBox rays =
        (fun μ : Fin q → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ μ) ''
          Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ, hμ, ?_⟩
      ext i
      simp [A, Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ, hμ, ?_⟩
      ext i
      simp [A, Matrix.mulVec, dotProduct, mul_comm]
  rw [himage]
  exact isRationalPolytope_image_rationalMatrixMulVec
    (coefficientUnitBox_isRationalPolytope q) A

/-- Helper for Exercise 4.33: the real cone generated by integral rays splits into a bounded
fractional part plus the integral cone. -/
private lemma finitelyGeneratedCone_eq_fractionalRayBox_add_integralIntcone
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ)) =
      fractionalRayBox rays + integral_intcone rays := by
  ext x
  constructor
  · intro hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    let a : Fin q → ℕ := fun j ↦ Int.toNat (Int.floor (μ j))
    let frac : Fin q → ℝ := fun j ↦ μ j - a j
    have ha_nonneg_int : ∀ j : Fin q, 0 ≤ Int.floor (μ j) := by
      intro j
      exact Int.floor_nonneg.mpr (hμ_nonneg j)
    have ha_cast : ∀ j : Fin q, ((a j : ℕ) : ℝ) = Int.floor (μ j) := by
      intro j
      have hcastInt : (((a j : ℕ) : ℤ)) = Int.floor (μ j) := by
        simp [a, Int.toNat_of_nonneg (ha_nonneg_int j)]
      exact_mod_cast hcastInt
    have hfrac_mem :
        frac ∈ Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1) := by
      rw [Set.mem_univ_pi]
      intro j
      constructor
      · have hfloor_le : (Int.floor (μ j) : ℝ) ≤ μ j := by
          exact_mod_cast Int.floor_le (μ j)
        have hcast := ha_cast j
        dsimp [frac]
        linarith
      · have hlt : μ j < Int.floor (μ j) + 1 := by
          exact Int.lt_floor_add_one (μ j)
        have hcast := ha_cast j
        dsimp [frac]
        linarith
    refine Set.mem_add.2 ?_
    refine ⟨∑ j : Fin q, frac j • (fun i : Fin k ↦ (rays j i : ℝ)), ?_,
      ∑ j : Fin q, (a j : ℝ) • (fun i : Fin k ↦ (rays j i : ℝ)), ?_, ?_⟩
    · -- The fractional coefficients stay in the bounded unit box.
      exact ⟨frac, hfrac_mem, rfl⟩
    · -- The floored coefficients give the integral cone contribution.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- Split each nonnegative coefficient into its floor and fractional part.
      have hsplit : ∀ j : Fin q, μ j = frac j + (a j : ℝ) := by
        intro j
        dsimp [frac]
        linarith [ha_cast j]
      ext i
      rw [hrepr]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
      calc
        ∑ c : Fin q, frac c * (rays c i : ℝ) + ∑ c : Fin q, (a c : ℝ) * (rays c i : ℝ)
            = ∑ c : Fin q, (frac c + (a c : ℝ)) * (rays c i : ℝ) := by
                simp [add_mul, Finset.sum_add_distrib]
        _ = ∑ c : Fin q, μ c * (rays c i : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [← hsplit j]
  · rintro ⟨u, hu, c, hc, rfl⟩
    rcases hu with ⟨μ, hμ, rfl⟩
    rcases (mem_integral_intcone_iff).1 hc with ⟨a, rfl⟩
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j + a j, ?_, ?_⟩
    · intro j
      have hμj : μ j ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.mem_univ_pi] using hμ j
      exact add_nonneg hμj.1 (by exact_mod_cast Nat.zero_le (a j))
    · ext i
      simp [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib]

/-- Helper for Exercise 4.33: once the recession rays are integral, the ambient flattened witness
can be normalized to one rational polytope plus one integral cone. -/
private lemma flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty
    {n p : ℕ}
    {W : Set (MixedRealPoint n p)}
    (hW : is_rational_mixed_polyhedron W)
    (hW_nonempty : Set.Nonempty W) :
    ∃ t : ℕ,
      ∃ Q0 : Set (Fin (n + p) → ℝ),
        ∃ r : Fin t → Fin (n + p) → ℤ,
          Q0.IsRationalPolytope ∧
            Fin.appendEquiv n p '' W = Q0 + integral_intcone r := by
  let Pflat : Set (Fin (n + p) → ℝ) := Fin.appendEquiv n p '' W
  have hPflat_rational : is_rational_polyhedron Pflat := by
    simpa [Pflat] using (show is_rational_polyhedron (Fin.appendEquiv n p '' W) from hW)
  have hPflat_nonempty : Set.Nonempty Pflat := by
    rcases hW_nonempty with ⟨w, hw⟩
    exact ⟨Fin.appendEquiv n p w, ⟨w, hw, rfl⟩⟩
  rcases existsFlattenedIntegralRecessionGenerators hW hW_nonempty with ⟨t, r, hrec⟩
  rcases existsFlattenedRationalVertexPresentationCompatibleWithIntegralRays
      hPflat_rational hPflat_nonempty r hrec with
    ⟨s, vQ, hQbase_repr⟩
  let Qbase : Set (Fin (n + p) → ℝ) :=
    convexHull ℝ (Set.range (fun i : Fin s ↦ fun u : Fin (n + p) ↦ (vQ i u : ℝ)))
  have hQbase : Qbase.IsRationalPolytope := by
    exact ⟨s, vQ, rfl⟩
  refine ⟨t, Qbase + fractionalRayBox r, r, isRationalPolytope_add hQbase
    (fractionalRayBox_isRationalPolytope r), ?_⟩
  -- Absorb the bounded fractional coefficients into one extra rational polytope.
  calc
    Fin.appendEquiv n p '' W
        = Qbase + finitely_generated_cone (fun j : Fin t ↦ fun i : Fin (n + p) ↦ (r j i : ℝ)) :=
          by simpa [Qbase] using hQbase_repr
    _ = Qbase + (fractionalRayBox r + integral_intcone r) := by
          rw [finitelyGeneratedCone_eq_fractionalRayBox_add_integralIntcone]
    _ = (Qbase + fractionalRayBox r) + integral_intcone r := by
          ext x
          constructor
          · rintro ⟨u, hu, v, hv, rfl⟩
            rcases hv with ⟨w, hw, c, hc, rfl⟩
            exact Set.mem_add.2 ⟨u + w, Set.mem_add.2 ⟨u, hu, w, hw, rfl⟩, c, hc, by
              ext i
              simp [add_assoc]⟩
          · rintro ⟨u, hu, c, hc, rfl⟩
            rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
            exact Set.mem_add.2 ⟨u₁, hu₁, u₂ + c, Set.mem_add.2 ⟨u₂, hu₂, c, hc, rfl⟩, by
              ext i
              simp [add_assoc]⟩

/-- Helper for Exercise 4.33: a bounded flattened mixed-integer representable mixed set should
decompose into finitely many flat rational polytope pieces. -/
private lemma boundedFlatRepresentableUnionOfRationalPolytopes
    {n p : ℕ}
    (S : Set (MixedRealPoint n p))
    (hS_nonempty : Set.Nonempty S)
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p))
    (hS_bounded : Bornology.IsBounded S)
    (hrepr : is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S)) :
    ∃ K : ℕ,
      ∃ Q : Fin K → Set (Fin (n + p) → ℝ),
        (∀ i : Fin K, (Q i).IsRationalPolytope) ∧
          ((Fin.appendEquiv n p) '' S = ⋃ i : Fin K, Q i) := by
  rcases existsExplicitFlatMixedIntegerProjectionWitness S hS_mixed hrepr with
    ⟨r, m, q, Aint, Areal, B, C, d, hW, hWproj⟩
  let W : Set (MixedRealPoint (n + q) ((n + p) + m)) :=
    rational_mixed_polyhedron
      (copiedIntegerBlockWitnessIntMatrix (n := n) C)
      (copiedIntegerBlockWitnessRealMatrix (n := n) (p := p) (m := m) (q := q) Aint Areal B)
      (copiedIntegerBlockWitnessRhs (n := n) d)
  have hW_nonempty : Set.Nonempty W := by
    -- One point of the flattened target gives one witness point of `W`.
    rcases hS_nonempty with ⟨x, hx⟩
    have hx_flat : Fin.appendEquiv n p x ∈ mixed_integer_x_projection W := by
      rw [← hWproj]
      exact ⟨x, hx, rfl⟩
    rcases (mem_mixed_integer_x_projection_iff).1 hx_flat with ⟨y, z, hzW⟩
    exact ⟨((fun j ↦ (z j : ℝ)), Fin.append (Fin.appendEquiv n p x) y), hzW⟩
  rcases flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty hW hW_nonempty with
    ⟨t, Qflat, rays, hQflat, hWambient⟩
  have hWslice :
      Fin.appendEquiv (n + q) ((n + p) + m) '' mixed_integer_points W =
        (Qflat ∩ firstBlockIntegerSet) + integral_intcone rays := by
    -- Rewrite the flattened mixed-integer witness through the ambient `polytope + integral cone`
    -- normal form before replacing the bounded first-block slice by finitely many fibers.
    simpa using flatMixedIntegerPoints_eq_baseSlice_add_integralIntcone hWambient
  rcases existsRationalPolytopeFirstBlockIntegerSlices hQflat with
    ⟨K, Qslice, hQslice, hslice⟩
  have hWdecomp :
      Fin.appendEquiv (n + q) ((n + p) + m) '' mixed_integer_points W =
        (⋃ j : Fin K, Qslice j) + integral_intcone rays := by
    calc
      Fin.appendEquiv (n + q) ((n + p) + m) '' mixed_integer_points W
          = (Qflat ∩ firstBlockIntegerSet) + integral_intcone rays := hWslice
      _ = (⋃ j : Fin K, Qslice j) + integral_intcone rays := by rw [hslice]
  have hflat_eq :
      (Fin.appendEquiv n p) '' S =
        (⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) +
          integral_intcone
            (fun j : Fin t ↦ fun l : Fin (n + p) ↦ rays j (Fin.natAdd (n + q) (Fin.castAdd m l))) := by
    calc
      (Fin.appendEquiv n p) '' S = mixed_integer_x_projection W := hWproj
      _ = (⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) +
            integral_intcone
              (fun j : Fin t ↦ fun l : Fin (n + p) ↦
                rays j (Fin.natAdd (n + q) (Fin.castAdd m l))) := by
            exact xProjection_transport_ofFlattenedDecomposition hWdecomp
  have hflat_bounded :
      Bornology.IsBounded
        ((⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) +
          integral_intcone
            (fun j : Fin t ↦ fun l : Fin (n + p) ↦ rays j (Fin.natAdd (n + q) (Fin.castAdd m l)))) := by
    -- Transport boundedness of the target to the projected decomposition.
    let eL :
        MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
      (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
    let e :
        MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
      eL.toContinuousLinearEquiv
    have himage : Bornology.IsBounded (e.toContinuousLinearMap '' S) := hS_bounded.image e.toContinuousLinearMap
    have htarget : Bornology.IsBounded ((Fin.appendEquiv n p) '' S) := by
      simpa [e, eL] using himage
    simpa [hflat_eq] using htarget
  have hUnion_nonempty :
      Set.Nonempty (⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) := by
    -- Peel one point of the bounded Minkowski sum back to the visible rational-polytope side.
    rcases (hS_nonempty.image (Fin.appendEquiv n p)) with ⟨u, hu⟩
    rw [hflat_eq] at hu
    rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩
    exact ⟨u₁, hu₁⟩
  have hcone_zero :
      integral_intcone
        (fun j : Fin t ↦ fun l : Fin (n + p) ↦ rays j (Fin.natAdd (n + q) (Fin.castAdd m l))) =
        ({0} : Set (Fin (n + p) → ℝ)) :=
    integralIntconeEqSingletonZeroOfBoundedNonemptySum hflat_bounded hUnion_nonempty
  refine ⟨K, fun j ↦ flattenedVisibleXProjection '' Qslice j, ?_, ?_⟩
  · intro j
    -- Each flattened visible image of a rational slice is still a rational polytope.
    exact isRationalPolytope_image_flattenedVisibleXProjection (hQslice j)
  · calc
      (Fin.appendEquiv n p) '' S
          = (⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) +
              integral_intcone
                (fun j : Fin t ↦ fun l : Fin (n + p) ↦
                  rays j (Fin.natAdd (n + q) (Fin.castAdd m l))) := hflat_eq
      _ = (⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j) + ({0} : Set (Fin (n + p) → ℝ)) := by
            rw [hcone_zero]
      _ = ⋃ j : Fin K, flattenedVisibleXProjection '' Qslice j := add_singleton_zero_eq

/-- Helper for Exercise 4.33: the rational one-hot row used in the reverse witness picks out the
selected integer coordinate after casting to `ℝ`. -/
private lemma sum_oneHotRatCast_mul
    {q : ℕ}
    (z : Fin q → ℤ)
    (j : Fin q) :
    ∑ k : Fin q, (((if k = j then (1 : ℚ) else 0) : ℚ) : ℝ) * (z k : ℝ) = (z j : ℝ) := by
  -- Isolate the unique nonzero coefficient in the one-hot row.
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Helper for Exercise 4.33: the rational negative one-hot row used in the reverse witness
records the negated selected integer coordinate after casting to `ℝ`. -/
private lemma sum_negOneHotRatCast_mul
    {q : ℕ}
    (z : Fin q → ℤ)
    (j : Fin q) :
    ∑ k : Fin q, (((if k = j then (-1 : ℚ) else 0) : ℚ) : ℝ) * (z k : ℝ) = -(z j : ℝ) := by
  -- Isolate the unique nonzero coefficient in the negative one-hot row.
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Helper for Exercise 4.33: for an integer vector, the `0/1` condition is equivalent to the
coordinatewise bounds `0 ≤ z ≤ 1`. -/
private lemma isZeroOneVector_iff_realBounds
    {q : ℕ}
    {z : Fin q → ℤ} :
    is_zero_one_vector (fun j ↦ (z j : ℝ)) ↔
      ∀ j : Fin q, (0 : ℝ) ≤ z j ∧ (z j : ℝ) ≤ 1 := by
  constructor
  · intro hz j
    rcases hz j with hzj | hzj
    · constructor
      · simpa [hzj]
      · simpa [hzj]
    · constructor
      · linarith
      · simpa [hzj]
  · intro hz j
    have hz_nonneg : 0 ≤ z j := by
      exact_mod_cast (hz j).1
    have hz_le_one : z j ≤ 1 := by
      exact_mod_cast (hz j).2
    have hz_cases : z j = 0 ∨ z j = 1 := by
      omega
    rcases hz_cases with hzj | hzj
    · left
      simpa [hzj]
    · right
      simpa [hzj]

/-- Helper for Exercise 4.33: the empty flattened set is mixed integer linear representable via
one inconsistent rational inequality. -/
private lemma emptyIsMixedIntegerLinearRepresentable
    {k : ℕ} :
    is_mixed_integer_linear_representable (∅ : Set (Fin k → ℝ)) := by
  rw [is_mixed_integer_linear_representable_iff]
  let P : Set (MixedRealPoint 0 (k + 0)) :=
    rational_mixed_polyhedron
      (fun _ _ ↦ (0 : ℚ))
      (fun _ _ ↦ (0 : ℚ))
      (fun _ : Fin 1 ↦ (-1 : ℚ))
  refine ⟨0, 0, P, ?_, ?_⟩
  · -- The witness set is rational because it is already given by a rational mixed system.
    exact (is_rational_mixed_polyhedron_iff).2
      ⟨1,
        (fun _ _ ↦ (0 : ℚ)),
        (fun _ _ ↦ (0 : ℚ)),
        (fun _ : Fin 1 ↦ (-1 : ℚ)),
        rfl⟩
  · -- The unique inequality row reduces every witness to the contradiction `0 ≤ -1`.
    ext x
    rw [mem_mixed_integer_x_projection_iff]
    constructor
    · intro hx
      exact False.elim hx
    · rintro ⟨y, z, hzP⟩
      have hzero_le : (0 : ℝ) ≤ -1 := by
        have h0 := hzP 0
        simpa [P, mem_rational_mixed_polyhedron_iff, Matrix.mulVec, dotProduct] using h0
      linarith

/-- Helper for Exercise 4.33: pulling a bounded nonempty flat piece back through
`Fin.appendEquiv` preserves the trivial recession cone. -/
private lemma pullbackRecessionConeEqSingletonZeroOfNonemptyBounded
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ_nonempty : Set.Nonempty Q)
    (hQ_bounded : Bornology.IsBounded Q) :
    recessionCone ((Fin.appendEquiv n p).symm '' Q) = ({0} : Set (MixedRealPoint n p)) := by
  -- Transport recession directions to the flat side, collapse the bounded flat cone there,
  -- and then pull the resulting zero direction back through the equivalence.
  have hQ_cone :
      recessionCone Q = ({0} : Set (Fin (n + p) → ℝ)) :=
    recessionConeEqSingletonZeroOfNonemptyBounded hQ_nonempty hQ_bounded
  ext d
  constructor
  · intro hd
    rw [Set.mem_singleton_iff]
    have hflat :
        Fin.appendEquiv n p d ∈ recessionCone Q := by
      have himage :
          Fin.appendEquiv n p '' ((Fin.appendEquiv n p).symm '' Q) = Q :=
        appendEquiv_image_symm_eq (n := n) (p := p) Q
      have hflat' :
          Fin.appendEquiv n p d ∈
            recessionCone (Fin.appendEquiv n p '' ((Fin.appendEquiv n p).symm '' Q)) :=
        (mem_recessionCone_appendEquiv_iff
          (Q := (Fin.appendEquiv n p).symm '' Q) (d := d)).2 hd
      rw [himage] at hflat'
      exact hflat'
    have hzero : Fin.appendEquiv n p d = 0 := by
      simpa [hQ_cone] using hflat
    have hzero0 : Fin.appendEquiv n p (0 : MixedRealPoint n p) = 0 := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [Fin.appendEquiv]
      · intro j
        simp [Fin.appendEquiv]
    have hzero' : Fin.appendEquiv n p d = Fin.appendEquiv n p (0 : MixedRealPoint n p) := by
      rw [hzero0]
      exact hzero
    exact (Fin.appendEquiv n p).injective hzero'
  · rintro rfl
    exact zero_mem_recessionCone

/-- Helper for Exercise 4.33: the forward nonempty branch should package a bounded flat mixed-
integer representation through Theorem 4.47 and Exercise 4.32. -/
private lemma mixedBinaryRepresentableOfBoundedFlatMixedIntegerRepresentable
    {n p : ℕ}
    (S : Set (MixedRealPoint n p))
    (hS_nonempty : Set.Nonempty S)
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p))
    (hS_bounded : Bornology.IsBounded S)
    (hrepr : is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S)) :
    is_mixed_binary_linear_representable S := by
  classical
  -- Route correction: the copied-block normalization is already finished above.
  -- The remaining work is bounded packaging: decompose the bounded flattened image into finitely
  -- many rational polytope pieces, pull each piece back through `Fin.appendEquiv`, and then feed
  -- the resulting bounded mixed-polyhedron family into Exercise 4.32.
  rcases boundedFlatRepresentableUnionOfRationalPolytopes
      S hS_nonempty hS_mixed hS_bounded hrepr with
    ⟨K, Q, hQ, hflat_eq⟩
  let Q0 : Fin K → Set (MixedRealPoint n p) := fun i ↦ (Fin.appendEquiv n p).symm '' Q i
  have hQsubset : ∀ i : Fin K, Q i ⊆ (Fin.appendEquiv n p '' S) := by
    intro i u hu
    rw [hflat_eq]
    exact Set.mem_iUnion.2 ⟨i, hu⟩
  have hQ0_points :
      ∀ i : Fin K, mixed_integer_points (Q0 i) = Q0 i := by
    intro i
    -- Every pullback piece already lies inside `S ⊆ ℤ^n × ℝ^p`, so no extra mixed-integer
    -- filtering remains.
    exact mixedIntegerPointsSymmImageEqOfSubsetAppendEquivImage (hQsubset i) hS_mixed
  have hUnionQ0 : S = ⋃ i : Fin K, mixed_integer_points (Q0 i) := by
    -- Pull the finite flat cover back through `Fin.appendEquiv` and rewrite each piece through
    -- the mixed-lattice normalization above.
    ext x
    constructor
    · intro hx
      have hx_flat : Fin.appendEquiv n p x ∈ ⋃ i : Fin K, Q i := by
        rw [← hflat_eq]
        exact ⟨x, hx, rfl⟩
      rcases Set.mem_iUnion.mp hx_flat with ⟨i, hxi⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [hQ0_points i]
      exact ⟨Fin.appendEquiv n p x, hxi, by simp⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      rw [hQ0_points i] at hxi
      rcases hxi with ⟨u, huQ, rfl⟩
      have huS_flat : u ∈ Fin.appendEquiv n p '' S := by
        rw [hflat_eq]
        exact Set.mem_iUnion.2 ⟨i, huQ⟩
      rcases huS_flat with ⟨x, hxS, hxEq⟩
      have hx_symm : x = (Fin.appendEquiv n p).symm u := by
        apply (Fin.appendEquiv n p).injective
        calc
          Fin.appendEquiv n p x = u := hxEq
          _ = Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) := by
            symm
            simpa using appendEquiv_symm_apply (n := n) (p := p) u
      simpa [hx_symm] using hxS
  have hUnion_nonempty :
      Set.Nonempty (⋃ i : Fin K, mixed_integer_points (Q0 i)) := by
    simpa [hUnionQ0] using hS_nonempty
  obtain ⟨i0, hi0_nonempty⟩ :=
    exists_nonempty_component_of_nonempty_iUnion_mixed_integer_points hUnion_nonempty
  let P : Fin K → Set (MixedRealPoint n p) := fun i ↦
    if h : Set.Nonempty (mixed_integer_points (Q0 i)) then Q0 i else Q0 i0
  have hQ0_flat_nonempty :
      ∀ i : Fin K, Set.Nonempty (mixed_integer_points (Q0 i)) →
        Set.Nonempty (Q i) := by
    intro i hi
    have hi' : Set.Nonempty (Q0 i) := by
      simpa [hQ0_points i] using hi
    rcases hi' with ⟨x, hx⟩
    rcases hx with ⟨u, hu, rfl⟩
    exact ⟨u, hu⟩
  have hQ0_nonempty_flat : Set.Nonempty (Q i0) :=
    hQ0_flat_nonempty i0 hi0_nonempty
  refine
    (mixed_binary_linear_representable_iff_finite_union_of_mixed_integer_linear_sets
      S hS_mixed hS_nonempty).2 ?_
  refine ⟨K, P, ?_, ?_, ?_, ?_⟩
  · intro i
    -- Each retained component is the pullback of one flat rational polytope.
    by_cases hi : Set.Nonempty (mixed_integer_points (Q0 i))
    · have hPi : P i = Q0 i := by simp [P, hi]
      rw [hPi]
      exact pullbackRationalPolytopeIsRationalMixedPolyhedron (hQ i)
    · have hPi : P i = Q0 i0 := by simp [P, hi]
      rw [hPi]
      exact pullbackRationalPolytopeIsRationalMixedPolyhedron (hQ i0)
  · intro i
    -- Empty components are replaced by the fixed nonempty one `i0`.
    dsimp [P]
    by_cases hi : Set.Nonempty (mixed_integer_points (Q0 i))
    · simpa [hi] using hi
    · simpa [hi] using hi0_nonempty
  · -- Replacing empty components does not change the represented union.
    ext x
    constructor
    · intro hx
      rw [hUnionQ0] at hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      have hi_nonempty : Set.Nonempty (mixed_integer_points (Q0 i)) := ⟨x, hxi⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      simpa [P, hi_nonempty] using hxi
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      by_cases hi : Set.Nonempty (mixed_integer_points (Q0 i))
      · rw [hUnionQ0]
        exact Set.mem_iUnion.2 ⟨i, by simpa [P, hi] using hxi⟩
      · rw [hUnionQ0]
        exact Set.mem_iUnion.2 ⟨i0, by simpa [P, hi] using hxi⟩
  · intro i j
    have hPi_zero :
        recessionCone (P i) = ({0} : Set (MixedRealPoint n p)) := by
      by_cases hi : Set.Nonempty (mixed_integer_points (Q0 i))
      · have hQi_nonempty : Set.Nonempty (Q i) := hQ0_flat_nonempty i hi
        have hPi : P i = Q0 i := by simp [P, hi]
        rw [hPi]
        exact
          pullbackRecessionConeEqSingletonZeroOfNonemptyBounded
            (n := n) (p := p) (Q := Q i) hQi_nonempty
            (isBoundedOfIsRationalPolytope (hQ i))
      · have hPi : P i = Q0 i0 := by simp [P, hi]
        rw [hPi]
        exact
          pullbackRecessionConeEqSingletonZeroOfNonemptyBounded
            (n := n) (p := p) (Q := Q i0) hQ0_nonempty_flat
            (isBoundedOfIsRationalPolytope (hQ i0))
    have hPj_zero :
        recessionCone (P j) = ({0} : Set (MixedRealPoint n p)) := by
      by_cases hj : Set.Nonempty (mixed_integer_points (Q0 j))
      · have hQj_nonempty : Set.Nonempty (Q j) := hQ0_flat_nonempty j hj
        have hPj : P j = Q0 j := by simp [P, hj]
        rw [hPj]
        exact
          pullbackRecessionConeEqSingletonZeroOfNonemptyBounded
            (n := n) (p := p) (Q := Q j) hQj_nonempty
            (isBoundedOfIsRationalPolytope (hQ j))
      · have hPj : P j = Q0 i0 := by simp [P, hj]
        rw [hPj]
        exact
          pullbackRecessionConeEqSingletonZeroOfNonemptyBounded
            (n := n) (p := p) (Q := Q i0) hQ0_nonempty_flat
            (isBoundedOfIsRationalPolytope (hQ i0))
    exact hPi_zero.trans hPj_zero.symm

/-- Helper for Exercise 4.33: the reverse nonempty branch should package a bounded mixed-binary
representation through Exercise 4.32, Corollary 4.31, and Theorem 4.47. -/
private lemma mixedIntegerRepresentableOfBoundedMixedBinaryRepresentable
    {n p : ℕ}
    (S : Set (MixedRealPoint n p))
    (hS_nonempty : Set.Nonempty S)
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p))
    (hS_bounded : Bornology.IsBounded S)
    (hrepr : is_mixed_binary_linear_representable S) :
    is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S) := by
  rcases hrepr with ⟨r, m, q, Aint, Areal, B, C, d, hS_eq⟩
  let Aint' : Matrix (Fin (r + (q + q))) (Fin n) ℚ :=
    fun i ↦
      Fin.addCases
        (fun i' ↦ Aint i')
        (Fin.addCases (fun _ _ ↦ 0) (fun _ _ ↦ 0))
        i
  let Areal' : Matrix (Fin (r + (q + q))) (Fin p) ℚ :=
    fun i ↦
      Fin.addCases
        (fun i' ↦ Areal i')
        (Fin.addCases (fun _ _ ↦ 0) (fun _ _ ↦ 0))
        i
  let B' : Matrix (Fin (r + (q + q))) (Fin m) ℚ :=
    fun i ↦
      Fin.addCases
        (fun i' ↦ B i')
        (Fin.addCases (fun _ _ ↦ 0) (fun _ _ ↦ 0))
        i
  let C' : Matrix (Fin (r + (q + q))) (Fin q) ℚ :=
    fun i ↦
      Fin.addCases
        (fun i' ↦ C i')
        (Fin.addCases
          (fun i' j ↦ if j = i' then 1 else 0)
          (fun i' j ↦ if j = i' then -1 else 0))
        i
  let d' : Fin (r + (q + q)) → ℚ :=
    Fin.addCases d (Fin.addCases (fun _ ↦ 1) (fun _ ↦ 0))
  -- Route correction: the reverse direction does not need the blocked Chapter 4.31 / 4.47 API.
  -- Replace each binary auxiliary variable by an integer auxiliary variable together with the
  -- explicit bounds `0 ≤ z ≤ 1`.
  refine (is_mixed_integer_linear_representable_on_mixed_integer_point_iff
    (S := S) hS_mixed).2 ?_
  refine ⟨r + (q + q), m, q, Aint', Areal', B', C', d', ?_⟩
  ext x
  constructor
  · intro hx
    rw [hS_eq] at hx
    rw [mem_mixed_binary_linear_projection_iff] at hx
    rcases hx with ⟨hxMixed, y, z, hz_binary, hineq⟩
    refine ⟨hxMixed, y, z, ?_⟩
    intro i
    -- Split the extended system into original rows, upper bounds, and lower bounds.
    refine Fin.addCases ?_ ?_ i
    · intro i'
      simpa [Aint', Areal', B', C', d'] using hineq i'
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        have hz_bounds := (isZeroOneVector_iff_realBounds (z := z)).1 hz_binary j'
        have hz_upper : (z j' : ℝ) ≤ 1 := hz_bounds.2
        have hrow :
            (∑ k : Fin n,
                (Aint' (Fin.natAdd r (Fin.castAdd q j')) k : ℝ) * x.1 k) +
              (∑ k : Fin p,
                  (Areal' (Fin.natAdd r (Fin.castAdd q j')) k : ℝ) * x.2 k) +
                (∑ k : Fin m,
                    (B' (Fin.natAdd r (Fin.castAdd q j')) k : ℝ) * y k) +
                  ∑ k : Fin q,
                    (C' (Fin.natAdd r (Fin.castAdd q j')) k : ℝ) * (z k : ℝ) =
              (z j' : ℝ) := by
          -- All nonselector rows are zero, and the one-hot row leaves only `z_j`.
          simp [Aint', Areal', B', C', sum_oneHotRatCast_mul]
        -- The upper extra row is the single inequality `z_j ≤ 1`.
        rw [hrow]
        simpa [d'] using hz_upper
      · intro j'
        have hz_bounds := (isZeroOneVector_iff_realBounds (z := z)).1 hz_binary j'
        have hz_lower : -(z j' : ℝ) ≤ 0 := by
          linarith [hz_bounds.1]
        have hcoeff :
            ∀ k : Fin q,
              (C' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) =
                if k = j' then (-1 : ℝ) else 0 := by
          intro k
          have hnat : j'.addNat q = Fin.natAdd q j' := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [C']
          rw [hnat, Fin.addCases_right]
          by_cases hk : k = j' <;> simp [hk]
        have hrow :
            (∑ k : Fin n,
                (Aint' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * x.1 k) +
              (∑ k : Fin p,
                  (Areal' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * x.2 k) +
                (∑ k : Fin m,
                    (B' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * y k) +
                  ∑ k : Fin q,
                    (C' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * (z k : ℝ) =
              -(z j' : ℝ) := by
          -- The lower extra row is the negative selector `-z_j`.
          have hAint :
              (∑ k : Fin n, (Aint' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * x.1 k) = 0 := by
            have hnat : j'.addNat q = Fin.natAdd q j' := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [Aint']
            rw [hnat, Fin.addCases_right]
            simp
          have hAreal :
              (∑ k : Fin p, (Areal' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * x.2 k) = 0 := by
            have hnat : j'.addNat q = Fin.natAdd q j' := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [Areal']
            rw [hnat, Fin.addCases_right]
            simp
          have hB :
            (∑ k : Fin m, (B' (Fin.natAdd r (Fin.natAdd q j')) k : ℝ) * y k) = 0 := by
            have hnat : j'.addNat q = Fin.natAdd q j' := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [B']
            rw [hnat, Fin.addCases_right]
            simp
          rw [hAint, hAreal, hB]
          simp_rw [hcoeff]
          rw [Finset.sum_eq_single j']
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        have hdrow : (d' (Fin.natAdd r (Fin.natAdd q j')) : ℝ) = 0 := by
          have hnat : j'.addNat q = Fin.natAdd q j' := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [d']
          rw [hnat, Fin.addCases_right]
        -- The lower extra row is the single inequality `-z_j ≤ 0`.
        rw [hrow]
        rw [hdrow]
        exact hz_lower
  · rintro ⟨hxMixed, y, z, hineq⟩
    rw [hS_eq, mem_mixed_binary_linear_projection_iff]
    refine ⟨hxMixed, y, z, ?_, ?_⟩
    · -- Read the extra rows as the coordinatewise bounds `0 ≤ z ≤ 1`.
      refine (isZeroOneVector_iff_realBounds (z := z)).2 ?_
      intro j
      have hupper := hineq (Fin.natAdd r (Fin.castAdd q j))
      have hlower := hineq (Fin.natAdd r (Fin.natAdd q j))
      have hupperRow :
          (∑ k : Fin n,
              (Aint' (Fin.natAdd r (Fin.castAdd q j)) k : ℝ) * x.1 k) +
            (∑ k : Fin p,
                (Areal' (Fin.natAdd r (Fin.castAdd q j)) k : ℝ) * x.2 k) +
              (∑ k : Fin m,
                  (B' (Fin.natAdd r (Fin.castAdd q j)) k : ℝ) * y k) +
                ∑ k : Fin q,
                  (C' (Fin.natAdd r (Fin.castAdd q j)) k : ℝ) * (z k : ℝ) =
            (z j : ℝ) := by
        -- Reduce the upper extra row to the positive selector term.
        simp [Aint', Areal', B', C', sum_oneHotRatCast_mul]
      have hlowerCoeff :
          ∀ k : Fin q,
            (C' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) =
              if k = j then (-1 : ℝ) else 0 := by
        intro k
        have hnat : j.addNat q = Fin.natAdd q j := by
          apply Fin.ext
          simpa [Nat.add_comm] using rfl
        simp [C']
        rw [hnat, Fin.addCases_right]
        by_cases hk : k = j <;> simp [hk]
      have hlowerRow :
          (∑ k : Fin n,
              (Aint' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * x.1 k) +
            (∑ k : Fin p,
                (Areal' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * x.2 k) +
              (∑ k : Fin m,
                  (B' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * y k) +
                ∑ k : Fin q,
                  (C' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * (z k : ℝ) =
            -(z j : ℝ) := by
        -- Reduce the lower extra row to the negative selector term.
        have hAint :
            (∑ k : Fin n, (Aint' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * x.1 k) = 0 := by
          have hnat : j.addNat q = Fin.natAdd q j := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [Aint']
          rw [hnat, Fin.addCases_right]
          simp
        have hAreal :
            (∑ k : Fin p, (Areal' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * x.2 k) = 0 := by
          have hnat : j.addNat q = Fin.natAdd q j := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [Areal']
          rw [hnat, Fin.addCases_right]
          simp
        have hB :
            (∑ k : Fin m, (B' (Fin.natAdd r (Fin.natAdd q j)) k : ℝ) * y k) = 0 := by
          have hnat : j.addNat q = Fin.natAdd q j := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [B']
          rw [hnat, Fin.addCases_right]
          simp
        rw [hAint, hAreal, hB]
        simp_rw [hlowerCoeff]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          simp [hk]
        · simp
      have hz_upper : (z j : ℝ) ≤ 1 := by
        rw [hupperRow] at hupper
        simpa [d'] using hupper
      have hz_lower : -(z j : ℝ) ≤ 0 := by
        have hdrow : (d' (Fin.natAdd r (Fin.natAdd q j)) : ℝ) = 0 := by
          have hnat : j.addNat q = Fin.natAdd q j := by
            apply Fin.ext
            simpa [Nat.add_comm] using rfl
          simp [d']
          rw [hnat, Fin.addCases_right]
        rw [hlowerRow] at hlower
        rw [hdrow] at hlower
        exact hlower
      constructor
      · linarith
      · exact hz_upper
    · intro i
      -- The original rows of the extended system are exactly the source mixed-binary rows.
      simpa [Aint', Areal', B', C', d'] using hineq (Fin.castAdd (q + q) i)

/-- Exercise 4.33. If a bounded set `S ⊆ ℤ^n × ℝ^p` is mixed integer linear representable, then
it is mixed binary linear representable, and conversely. The mixed-integer side is stated via the
canonical Chapter 4 owner on the flattened mixed-space image. -/
theorem bounded_mixed_integer_linear_representable_iff_mixed_binary_linear_representable
    {n p : ℕ}
    (S : Set (MixedRealPoint n p))
    (hS_mixed : S ⊆ (ℤ^n×ℝ^p))
    (hS_bounded : Bornology.IsBounded S) :
    is_mixed_integer_linear_representable ((Fin.appendEquiv n p) '' S) ↔
      is_mixed_binary_linear_representable S := by
  by_cases hS_empty : S = ∅
  · subst hS_empty
    -- The empty set is representable on both sides by the standard inconsistent witness.
    constructor
    · intro _
      simpa using (empty_is_mixed_binary_linear_representable (n := n) (p := p))
    · intro _
      simpa using (emptyIsMixedIntegerLinearRepresentable (k := n + p))
  · have hS_nonempty : Set.Nonempty S := Set.nonempty_iff_ne_empty.mpr hS_empty
    constructor
    · intro hrepr
      -- The nonempty forward branch is isolated in a theorem-local packaging lemma.
      exact mixedBinaryRepresentableOfBoundedFlatMixedIntegerRepresentable
        S hS_nonempty hS_mixed hS_bounded hrepr
    · intro hrepr
      -- The nonempty reverse branch is isolated in a theorem-local packaging lemma.
      exact mixedIntegerRepresentableOfBoundedMixedBinaryRepresentable
        S hS_nonempty hS_mixed hS_bounded hrepr
