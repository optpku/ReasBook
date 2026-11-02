import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_theorem_1_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_theorem_8_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_8.SplitFormulation

open scoped Matrix

section Exercise88

variable {m₁ m₂ n p : ℕ}

namespace SplitMixedInteger

/-- Helper for Exercise 8.8: the flattened objective on `(x, y)` keeps the original cost on the
first block and ignores the second block. -/
def splitFlatObjective
    {n : ℕ}
    (c : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.append c 0

/-- Helper for Exercise 8.8: the first split-row family encodes `x - y ≤ 0` on flattened pairs. -/
def splitUpperRowMatrix
    {n : ℕ} : Matrix (Fin n) (Fin (n + n)) ℝ :=
  mixedConstraintMatrix (1 : Matrix (Fin n) (Fin n) ℝ) (-1)

/-- Helper for Exercise 8.8: the second split-row family encodes `y - x ≤ 0` on flattened pairs. -/
def splitLowerRowMatrix
    {n : ℕ} : Matrix (Fin n) (Fin (n + n)) ℝ :=
  mixedConstraintMatrix (-1) (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Helper for Exercise 8.8: the full split-row matrix stacks the inequalities `x - y ≤ 0` and
`y - x ≤ 0`. -/
def splitRowMatrix
    {n : ℕ} : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl j => splitUpperRowMatrix j
    | Sum.inr j => splitLowerRowMatrix j

/-- Helper for Exercise 8.8: the split-row right-hand side is the zero vector. -/
def splitRowRhs
    {n : ℕ} : Fin (n + n) → ℝ :=
  0

/-- Helper for Exercise 8.8: the product-hull polyhedron keeps the first hull inequalities on the
`x`-block and the second hull inequalities on the `y`-block. -/
def splitHullProductIntegerMatrix
    {r₁ r₂ n : ℕ}
    (C₁ : Matrix (Fin r₁) (Fin n) ℝ) :
    Matrix (Fin (r₁ + r₂)) (Fin n) ℝ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl j => C₁ j
    | Sum.inr _ => 0

/-- Helper for Exercise 8.8: the second block of the product-hull polyhedron carries the
constraints of the second convexified factor. -/
def splitHullProductContinuousMatrix
    {r₁ r₂ n : ℕ}
    (C₂ : Matrix (Fin r₂) (Fin n) ℝ) :
    Matrix (Fin (r₁ + r₂)) (Fin n) ℝ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl _ => 0
    | Sum.inr j => C₂ j

/-- Helper for Exercise 8.8: the product-hull right-hand side is the rowwise sum of the two hull
right-hand sides. -/
def splitHullProductRhs
    {r₁ r₂ : ℕ}
    (d₁ : Fin r₁ → ℝ)
    (d₂ : Fin r₂ → ℝ) :
    Fin (r₁ + r₂) → ℝ :=
  fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl j => d₁ j
    | Sum.inr j => d₂ j

/-- Helper for Exercise 8.8: evaluating the flattened objective on `Fin.append x y` recovers the
original objective `c ⬝ᵥ x`. -/
lemma splitFlatObjective_dot_append
    {n : ℕ}
    (c x y : Fin n → ℝ) :
    splitFlatObjective c ⬝ᵥ Fin.append x y = c ⬝ᵥ x := by
  -- Expand the appended dot product once so the zero second block disappears coordinatewise.
  simp [splitFlatObjective, dotProduct, Fin.append, Fin.sum_univ_add,
    Fin.natAdd_eq_addNat]

/-- Helper for Exercise 8.8: the upper split rows applied to `Fin.append x y` compute `x - y`. -/
lemma splitUpperRowMatrix_mulVec_append
    {n : ℕ}
    (x y : Fin n → ℝ) :
    splitUpperRowMatrix *ᵥ Fin.append x y = x - y := by
  -- Read the upper split block through `mixedConstraintMatrix_mulVec_append`.
  calc
    splitUpperRowMatrix *ᵥ Fin.append x y
        = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x + (-1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y := by
            simpa [splitUpperRowMatrix] using
              (mixedConstraintMatrix_mulVec_append
                (1 : Matrix (Fin n) (Fin n) ℝ)
                (-1 : Matrix (Fin n) (Fin n) ℝ)
                x y)
    _ = x - y := by
          rw [Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, sub_eq_add_neg]

/-- Helper for Exercise 8.8: the lower split rows applied to `Fin.append x y` compute `y - x`. -/
lemma splitLowerRowMatrix_mulVec_append
    {n : ℕ}
    (x y : Fin n → ℝ) :
    splitLowerRowMatrix *ᵥ Fin.append x y = y - x := by
  -- Read the lower split block through `mixedConstraintMatrix_mulVec_append`.
  calc
    splitLowerRowMatrix *ᵥ Fin.append x y
        = (-1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x + (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y := by
            simpa [splitLowerRowMatrix] using
              (mixedConstraintMatrix_mulVec_append
                (-1 : Matrix (Fin n) (Fin n) ℝ)
                (1 : Matrix (Fin n) (Fin n) ℝ)
                x y)
    _ = y - x := by
          rw [Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, add_comm, sub_eq_add_neg]

/-- Helper for Exercise 8.8: the full split-row system applied to `Fin.append x y` stacks
`x - y` above `y - x`. -/
lemma splitRowMatrix_mulVec_append
    {n : ℕ}
    (x y : Fin n → ℝ) :
    splitRowMatrix *ᵥ Fin.append x y = Fin.append (x - y) (y - x) := by
  -- Evaluate each split row through `finSumFinEquiv`, then use the upper/lower block formulas.
  ext i
  cases h : finSumFinEquiv.symm i with
  | inl j =>
      have hrow : (splitRowMatrix *ᵥ Fin.append x y) i = (x - y) j := by
        simpa [Matrix.mulVec, splitRowMatrix, h] using
          congrFun (splitUpperRowMatrix_mulVec_append x y) j
      have hi : Fin.castAdd n j = i := by
        simpa [h] using finSumFinEquiv.apply_symm_apply i
      calc
        (splitRowMatrix *ᵥ Fin.append x y) i = (x - y) j := hrow
        _ = Fin.append (x - y) (y - x) i := by
              simpa [hi] using (Fin.append_left (x - y) (y - x) j).symm
  | inr j =>
      have hrow : (splitRowMatrix *ᵥ Fin.append x y) i = (y - x) j := by
        simpa [Matrix.mulVec, splitRowMatrix, h] using
          congrFun (splitLowerRowMatrix_mulVec_append x y) j
      have hi : Fin.natAdd n j = i := by
        simpa [h] using finSumFinEquiv.apply_symm_apply i
      calc
        (splitRowMatrix *ᵥ Fin.append x y) i = (y - x) j := hrow
        _ = Fin.append (x - y) (y - x) i := by
              simpa [hi.symm] using (Fin.append_right (x - y) (y - x) j).symm

/-- Helper for Exercise 8.8: the split-row inequalities are feasible at `Fin.append x y` exactly
when the two blocks agree. -/
lemma splitRowMatrix_mulVec_append_nonpos_iff
    {n : ℕ}
    {x y : Fin n → ℝ} :
    splitRowMatrix *ᵥ Fin.append x y ≤ splitRowRhs ↔ x = y := by
  -- The stacked inequalities are exactly `x - y ≤ 0` and `y - x ≤ 0`.
  rw [splitRowMatrix_mulVec_append, splitRowRhs]
  constructor
  · intro h
    ext i
    have hxy : (x - y) i ≤ 0 := by
      simpa [Fin.append] using h (Fin.castAdd n i)
    have hyx : (y - x) i ≤ 0 := by
      simpa [Fin.append, Fin.natAdd_eq_addNat] using h (Fin.natAdd n i)
    linarith
  · intro h
    subst h
    intro i
    cases hi : finSumFinEquiv.symm i with
    | inl j =>
        have hij : Fin.castAdd n j = i := by
          simpa [hi] using finSumFinEquiv.apply_symm_apply i
        simpa [Fin.append, Fin.natAdd_eq_addNat, ← hij]
    | inr j =>
        have hij : Fin.natAdd n j = i := by
          simpa [hi] using finSumFinEquiv.apply_symm_apply i
        simpa [Fin.append, ← hij]

/-- Helper for Exercise 8.8: the penalized split objective at `Fin.append x y` depends only on
the difference between the upper and lower multiplier blocks. -/
lemma splitPenalizedObjective_dot_append
    {n : ℕ}
    (c : Fin n → ℝ)
    (u : Fin (n + n) → ℝ)
    (x y : Fin n → ℝ) :
    splitFlatObjective c ⬝ᵥ Fin.append x y +
        u ⬝ᵥ (splitRowRhs - splitRowMatrix *ᵥ Fin.append x y) =
      c ⬝ᵥ x +
        (fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)) ⬝ᵥ (y - x) := by
  -- Rewrite the split slack as the stacked pair `(y - x, x - y)`.
  have hslack :
      splitRowRhs - splitRowMatrix *ᵥ Fin.append x y =
        Fin.append (y - x) (x - y) := by
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [splitRowRhs, splitRowMatrix_mulVec_append, sub_eq_add_neg]
    · intro j
      simp [splitRowRhs, splitRowMatrix_mulVec_append, sub_eq_add_neg, Fin.append,
        Fin.natAdd_eq_addNat]
  -- Split the multiplier dot product into its upper and lower blocks.
  calc
    splitFlatObjective c ⬝ᵥ Fin.append x y +
        u ⬝ᵥ (splitRowRhs - splitRowMatrix *ᵥ Fin.append x y)
        = c ⬝ᵥ x + u ⬝ᵥ Fin.append (y - x) (x - y) := by
            rw [splitFlatObjective_dot_append, hslack]
    _ = c ⬝ᵥ x +
          ((fun i ↦ u (Fin.castAdd n i)) ⬝ᵥ (y - x) +
            (fun i ↦ u (Fin.natAdd n i)) ⬝ᵥ (x - y)) := by
          simp [dotProduct, Fin.append, Fin.sum_univ_add, Fin.natAdd_eq_addNat]
    _ = c ⬝ᵥ x +
          ((fun i ↦ u (Fin.castAdd n i)) ⬝ᵥ (y - x) -
            (fun i ↦ u (Fin.natAdd n i)) ⬝ᵥ (y - x)) := by
          have hneg : x - y = -(y - x) := by
            ext i
            simp [sub_eq_add_neg]
          rw [hneg, dotProduct_neg, sub_eq_add_neg]
    _ = c ⬝ᵥ x +
          (fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)) ⬝ᵥ (y - x) := by
          rw [← sub_dotProduct]
          rfl

/-- Helper for Exercise 8.8: the equality `p + (n - p) = n` reindexes a flattened split vector
without changing its coordinates. -/
private def splitFlatCastEquiv
    {n p : ℕ}
    (hp : p ≤ n) :
    (Fin (p + (n - p)) → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.piCongrLeft ℝ (fun _ : Fin n ↦ ℝ) (finCongr (Nat.add_sub_of_le hp))

/-- Helper for Exercise 8.8: the first rational column block consists of the first `p` columns
of the original matrix. -/
private def splitIntegerColumns
    {m n p : ℕ}
    (hp : p ≤ n)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin p) ℚ :=
  fun i j ↦ A i (Fin.castLE hp j)

/-- Helper for Exercise 8.8: the second rational column block consists of the remaining `n - p`
columns of the original matrix. -/
private def splitContinuousColumns
    {m n p : ℕ}
    (hp : p ≤ n)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin (n - p)) ℚ :=
  fun i j ↦ A i (Fin.cast (Nat.add_sub_of_le hp) (Fin.natAdd p j))

/-- Helper for Exercise 8.8: casting a flattened split vector recovers the integer block on the
first `p` coordinates. -/
private lemma splitFlatCastEquiv_append_left
    {n p : ℕ}
    (hp : p ≤ n)
    (x : Fin p → ℝ)
    (y : Fin (n - p) → ℝ)
    (j : Fin p) :
    splitFlatCastEquiv hp (Fin.append x y) (Fin.castLE hp j) = x j := by
  -- Both embeddings carry `j` to the coordinate with underlying value `j`.
  simp [splitFlatCastEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

/-- Helper for Exercise 8.8: casting a flattened split vector recovers the continuous block on
the remaining coordinates. -/
private lemma splitFlatCastEquiv_append_right
    {n p : ℕ}
    (hp : p ≤ n)
    (x : Fin p → ℝ)
    (y : Fin (n - p) → ℝ)
    (j : Fin (n - p)) :
    splitFlatCastEquiv hp (Fin.append x y)
        (Fin.cast (Nat.add_sub_of_le hp) (Fin.natAdd p j)) = y j := by
  -- The cast preserves the underlying `p + j` coordinate of the second block.
  simp [splitFlatCastEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

/-- Helper for Exercise 8.8: splitting the rational columns and then flattening a mixed vector
reproduces multiplication by the original rational matrix. -/
private lemma splitColumns_mulVec_append
    {m n p : ℕ}
    (hp : p ≤ n)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (x : Fin p → ℝ)
    (y : Fin (n - p) → ℝ) :
    (A.map (Rat.castHom ℝ)) *ᵥ splitFlatCastEquiv hp (Fin.append x y) =
      ((splitIntegerColumns hp A).map (Rat.castHom ℝ)) *ᵥ x +
        ((splitContinuousColumns hp A).map (Rat.castHom ℝ)) *ᵥ y := by
  -- Reindex the original matrix first, then use the canonical block multiplication formula.
  let e : Fin (p + (n - p)) ≃ Fin n := finCongr (Nat.add_sub_of_le hp)
  have hreindex :
      (A.map (Rat.castHom ℝ)).submatrix id e =
        mixedConstraintMatrix
          ((splitIntegerColumns hp A).map (Rat.castHom ℝ))
          ((splitContinuousColumns hp A).map (Rat.castHom ℝ)) := by
    ext i j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Matrix.submatrix_apply, Function.id_def, Matrix.map_apply,
        Rat.coe_castHom, e, mixedConstraintMatrix, splitIntegerColumns, Fin.addCases_left]
      apply congrArg (A i)
      apply Fin.ext
      rfl
    · intro k
      simp only [Matrix.submatrix_apply, Function.id_def, Matrix.map_apply,
        Rat.coe_castHom, e, mixedConstraintMatrix, splitContinuousColumns, Fin.addCases_right]
      apply congrArg (A i)
      apply Fin.ext
      rfl
  calc
    (A.map (Rat.castHom ℝ)) *ᵥ splitFlatCastEquiv hp (Fin.append x y) =
        (A.map (Rat.castHom ℝ)).submatrix id e *ᵥ Fin.append x y := by
      symm
      simpa [e, splitFlatCastEquiv, LinearEquiv.piCongrLeft,
        LinearEquiv.piCongrLeft'] using
          Matrix.submatrix_mulVec_equiv
            (A.map (Rat.castHom ℝ)) (Fin.append x y) id e
    _ = mixedConstraintMatrix
          ((splitIntegerColumns hp A).map (Rat.castHom ℝ))
          ((splitContinuousColumns hp A).map (Rat.castHom ℝ)) *ᵥ Fin.append x y := by
      rw [hreindex]
    _ = ((splitIntegerColumns hp A).map (Rat.castHom ℝ)) *ᵥ x +
          ((splitContinuousColumns hp A).map (Rat.castHom ℝ)) *ᵥ y := by
      exact mixedConstraintMatrix_mulVec_append _ _ _ _

/-- Helper for Exercise 8.8: flattening a rational mixed polyhedron gives the corresponding
ordinary polyhedron with concatenated columns. -/
private lemma appendEquiv_image_rationalMixedPolyhedron_eq_polyhedron
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    Fin.appendEquiv n p '' rational_mixed_polyhedron A G b =
      polyhedron_le_set
        (mixedConstraintMatrix (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)))
        (fun i ↦ (b i : ℝ)) := by
  -- Membership on either side is the same block matrix inequality.
  ext z
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rw [mem_rational_mixed_polyhedron_iff] at hxy
    rw [mem_polyhedron_le_set_iff]
    simpa [Fin.appendEquiv, mixedConstraintMatrix_mulVec_append] using hxy
  · intro hz
    refine ⟨(Fin.appendEquiv n p).symm z, ?_, ?_⟩
    · rw [mem_rational_mixed_polyhedron_iff]
      rw [mem_polyhedron_le_set_iff] at hz
      have hzeq :
          Fin.append (fun i ↦ z (Fin.castAdd p i)) (fun i ↦ z (Fin.natAdd n i)) = z := by
        exact Fin.append_castAdd_natAdd
      rw [← hzeq] at hz
      simpa [Fin.appendEquiv, mixedConstraintMatrix_mulVec_append] using hz
    · exact (Fin.appendEquiv n p).apply_symm_apply z

/-- Helper for Exercise 8.8: reindexing a flat polyhedron along `p + (n - p) = n` only
reindexes its columns. -/
private lemma splitFlatCast_image_polyhedron_eq_polyhedron
    {m n p : ℕ}
    (hp : p ≤ n)
    (C : Matrix (Fin m) (Fin (p + (n - p))) ℝ)
    (d : Fin m → ℝ) :
    splitFlatCastEquiv hp '' polyhedron_le_set C d =
      polyhedron_le_set
        (C.submatrix id (finCongr (Nat.add_sub_of_le hp)).symm) d := by
  -- Use the standard submatrix/matrix-vector identity to move the coordinate equivalence.
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_polyhedron_le_set_iff] at hu ⊢
    intro i
    have hmul := congrFun
      (Matrix.submatrix_mulVec_equiv C (splitFlatCastEquiv hp u) id
        (finCongr (Nat.add_sub_of_le hp)).symm) i
    rw [hmul]
    simpa [splitFlatCastEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft'] using hu i
  · intro hz
    refine ⟨(splitFlatCastEquiv hp).symm z, ?_, (splitFlatCastEquiv hp).apply_symm_apply z⟩
    rw [mem_polyhedron_le_set_iff] at hz ⊢
    intro i
    have hmul := congrFun
      (Matrix.submatrix_mulVec_equiv C z id
        (finCongr (Nat.add_sub_of_le hp)).symm) i
    have hi := hz i
    rw [hmul] at hi
    simpa [splitFlatCastEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft'] using hi

/-- Helper for Exercise 8.8: the Section 8.1 base set is the two-stage flattened image of the
standard nonnegative rational mixed-integer set obtained by splitting its columns. -/
private lemma mixedIntegerEqualityBase_eq_splitFlatCastImage
    {m n p : ℕ}
    (hp : p ≤ n)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    mixed_integer_equality_lagrangian_base_set hp
        (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) =
      splitFlatCastEquiv hp ''
        (Fin.appendEquiv p (n - p) ''
          nonnegative_rational_mixed_integer_points
            (splitIntegerColumns hp A) (splitContinuousColumns hp A) b) := by
  -- Compare membership after exposing the integer and continuous blocks separately.
  ext z
  constructor
  · intro hz
    rw [mem_mixed_integer_equality_lagrangian_base_set_iff] at hz
    let u := (splitFlatCastEquiv hp).symm z
    let xy := (Fin.appendEquiv p (n - p)).symm u
    have happend : Fin.append xy.1 xy.2 = u := by
      exact (Fin.appendEquiv p (n - p)).apply_symm_apply u
    have hflat : splitFlatCastEquiv hp (Fin.append xy.1 xy.2) = z := by
      calc
        splitFlatCastEquiv hp (Fin.append xy.1 xy.2) = splitFlatCastEquiv hp u := by
          rw [happend]
        _ = z := (splitFlatCastEquiv hp).apply_symm_apply z
    have hxy :
        xy ∈ nonnegative_rational_mixed_integer_points
          (splitIntegerColumns hp A) (splitContinuousColumns hp A) b := by
      rw [mem_nonnegative_rational_mixed_integer_points_iff]
      constructor
      · rw [← splitColumns_mulVec_append hp A, hflat]
        exact hz.1
      · constructor
        · intro j
          rw [← splitFlatCastEquiv_append_left hp xy.1 xy.2 j, hflat]
          exact hz.2.2 (Fin.castLE hp j)
        · constructor
          · intro j
            rw [← splitFlatCastEquiv_append_right hp xy.1 xy.2 j, hflat]
            exact hz.2.2 (Fin.cast (Nat.add_sub_of_le hp) (Fin.natAdd p j))
          · rw [mem_integerVectors_iff_forall]
            intro j
            rcases hz.2.1 j with ⟨a, ha⟩
            have ha' : (a : ℝ) = xy.1 j := by
              rw [← splitFlatCastEquiv_append_left hp xy.1 xy.2 j, hflat]
              exact ha.symm
            exact ⟨a, ha'⟩
    refine ⟨Fin.append xy.1 xy.2, ⟨xy, hxy, rfl⟩, hflat⟩
  · rintro ⟨u, ⟨xy, hxy, rfl⟩, rfl⟩
    rw [mem_nonnegative_rational_mixed_integer_points_iff] at hxy
    rw [mem_mixed_integer_equality_lagrangian_base_set_iff]
    constructor
    · have happend : (Fin.appendEquiv p (n - p)) xy = Fin.append xy.1 xy.2 := rfl
      rw [happend, splitColumns_mulVec_append]
      exact hxy.1
    · constructor
      · rw [mem_integerVectors_iff_forall] at hxy
        intro j
        rcases hxy.2.2.2 j with ⟨a, ha⟩
        have ha' :
            splitFlatCastEquiv hp (Fin.append xy.1 xy.2) (Fin.castLE hp j) = (a : ℝ) := by
          rw [splitFlatCastEquiv_append_left]
          exact ha.symm
        exact ⟨a, ha'⟩
      · intro i
        let k := (finCongr (Nat.add_sub_of_le hp)).symm i
        have hi : finCongr (Nat.add_sub_of_le hp) k = i := by
          exact (finCongr (Nat.add_sub_of_le hp)).apply_symm_apply i
        rw [← hi]
        refine Fin.addCases ?_ ?_ k
        · intro j
          simpa [splitFlatCastEquiv, LinearEquiv.piCongrLeft,
            LinearEquiv.piCongrLeft', Fin.appendEquiv] using hxy.2.1 j
        · intro j
          simpa [splitFlatCastEquiv, LinearEquiv.piCongrLeft,
            LinearEquiv.piCongrLeft', Fin.appendEquiv, Fin.natAdd_eq_addNat] using
              hxy.2.2.1 j

/-- Helper for Exercise 8.8: each block hull `conv(Q)` can be rewritten as a polyhedron in the
original `Fin n → ℝ` owner. -/
lemma convexHull_mixedIntegerEqualityBase_eq_polyhedron
    {m n p : ℕ}
    (hp : p ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hQ : HasSection81RationalPresentation A b) :
    ∃ r : ℕ, ∃ C : Matrix (Fin r) (Fin n) ℝ, ∃ d : Fin r → ℝ,
      convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A b) = polyhedron_le_set C d := by
  -- Route correction: flatten first with `Fin.appendEquiv`, then perform the dimension cast as
  -- a separate linear reindexing; this avoids mixing both transports in the hull theorem.
  rcases (hasSection81RationalPresentation_iff.mp hQ) with ⟨Aq, bq, rfl, rfl⟩
  obtain ⟨r, Cq, Gq, dq, hHull⟩ :=
    nonnegative_rational_mixed_integer_hull_has_rational_presentation
      (splitIntegerColumns hp Aq) (splitContinuousColumns hp Aq) bq
  let Cflat : Matrix (Fin r) (Fin (p + (n - p))) ℝ :=
    mixedConstraintMatrix (Cq.map (Rat.castHom ℝ)) (Gq.map (Rat.castHom ℝ))
  let C : Matrix (Fin r) (Fin n) ℝ :=
    Cflat.submatrix id (finCongr (Nat.add_sub_of_le hp)).symm
  refine ⟨r, C, fun i ↦ (dq i : ℝ), ?_⟩
  -- Commute each linear image with `convexHull`, insert the rational hull presentation, and
  -- consume the two owner-normalization lemmas in their natural order.
  rw [mixedIntegerEqualityBase_eq_splitFlatCastImage]
  calc
    convexHull ℝ
          (splitFlatCastEquiv hp ''
            (Fin.appendEquiv p (n - p) ''
              nonnegative_rational_mixed_integer_points
                (splitIntegerColumns hp Aq) (splitContinuousColumns hp Aq) bq)) =
        splitFlatCastEquiv hp ''
          convexHull ℝ
            (Fin.appendEquiv p (n - p) ''
              nonnegative_rational_mixed_integer_points
                (splitIntegerColumns hp Aq) (splitContinuousColumns hp Aq) bq) := by
      symm
      exact (splitFlatCastEquiv hp).toLinearMap.image_convexHull _
    _ = splitFlatCastEquiv hp ''
          (Fin.appendEquiv p (n - p) ''
            convexHull ℝ
              (nonnegative_rational_mixed_integer_points
                (splitIntegerColumns hp Aq) (splitContinuousColumns hp Aq) bq)) := by
      apply congrArg (fun S ↦ splitFlatCastEquiv hp '' S)
      symm
      exact Theorem15Support.appendEquiv_image_convexHull _
    _ = splitFlatCastEquiv hp ''
          (Fin.appendEquiv p (n - p) '' rational_mixed_polyhedron Cq Gq dq) := by
      rw [hHull]
    _ = splitFlatCastEquiv hp '' polyhedron_le_set Cflat (fun i ↦ (dq i : ℝ)) := by
      rw [appendEquiv_image_rationalMixedPolyhedron_eq_polyhedron]
    _ = polyhedron_le_set C (fun i ↦ (dq i : ℝ)) := by
      simpa [Cflat, C] using
        splitFlatCast_image_polyhedron_eq_polyhedron hp Cflat (fun i ↦ (dq i : ℝ))

/-- Helper for Exercise 8.8: the convexified split relaxation over `Q₁ ×ˢ Q₂` equals the same
affine relaxation over `conv(Q₁) ×ˢ conv(Q₂)`. -/
lemma splitRelaxationValue_eq_convexifiedProductValue
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) :
    split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      sSup
        ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
          Set.prod
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂))) := by
  -- Treat the split objective as affine in the `x`-block and in the `y`-block separately.
  rw [split_mixed_integer_lagrangian_relaxation_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨xy, hxy, rfl⟩
    exact le_sSup ⟨xy,
      ⟨subset_convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) hxy.1,
        subset_convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) hxy.2⟩,
      rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨xy, hxy, rfl⟩
    rcases xy with ⟨x, y⟩
    let linearObjectiveX : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ (c - lam)
    have hconvX :
        ConvexOn ℝ Set.univ (fun x' : Fin n → ℝ ↦ linearObjectiveX x' + lam ⬝ᵥ y) := by
      simpa [linearObjectiveX] using
        (LinearMap.convexOn linearObjectiveX (s := Set.univ) convex_univ).add_const
          (lam ⬝ᵥ y)
    obtain ⟨x₀, hx₀, hx_ge⟩ :=
      ConvexOn.exists_ge_of_mem_convexHull hconvX
        (show mixed_integer_equality_lagrangian_base_set hp A₁ b₁ ⊆ Set.univ by
          intro z hz
          trivial)
        hxy.1
    have hx_eval (x' : Fin n → ℝ) :
        linearObjectiveX x' + lam ⬝ᵥ y =
          c ⬝ᵥ x' + lam ⬝ᵥ (y - x') := by
      calc
        linearObjectiveX x' + lam ⬝ᵥ y = (c - lam) ⬝ᵥ x' + lam ⬝ᵥ y := by
          rfl
        _ = (c ⬝ᵥ x' - lam ⬝ᵥ x') + lam ⬝ᵥ y := by
          rw [sub_dotProduct]
        _ = c ⬝ᵥ x' + (lam ⬝ᵥ y - lam ⬝ᵥ x') := by
          ring
        _ = c ⬝ᵥ x' + lam ⬝ᵥ (y - x') := by
          rw [dotProduct_sub]
    have hxy_le_x₀y :
        c ⬝ᵥ x + lam ⬝ᵥ (y - x) ≤ c ⬝ᵥ x₀ + lam ⬝ᵥ (y - x₀) := by
      simpa [hx_eval x, hx_eval x₀] using hx_ge
    let linearObjectiveY : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ lam
    have hconvY :
        ConvexOn ℝ Set.univ
          (fun y' : Fin n → ℝ ↦ linearObjectiveY y' + (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀)) := by
      simpa [linearObjectiveY] using
        (LinearMap.convexOn linearObjectiveY (s := Set.univ) convex_univ).add_const
          (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀)
    obtain ⟨y₀, hy₀, hy_ge⟩ :=
      ConvexOn.exists_ge_of_mem_convexHull hconvY
        (show mixed_integer_equality_lagrangian_base_set hp A₂ b₂ ⊆ Set.univ by
          intro z hz
          trivial)
        hxy.2
    have hy_eval (y' : Fin n → ℝ) :
        linearObjectiveY y' + (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀) =
          c ⬝ᵥ x₀ + lam ⬝ᵥ (y' - x₀) := by
      calc
        linearObjectiveY y' + (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀) =
            lam ⬝ᵥ y' + (c ⬝ᵥ x₀ - lam ⬝ᵥ x₀) := by
              rfl
        _ = c ⬝ᵥ x₀ + (lam ⬝ᵥ y' - lam ⬝ᵥ x₀) := by
          ring
        _ = c ⬝ᵥ x₀ + lam ⬝ᵥ (y' - x₀) := by
          rw [dotProduct_sub]
    have hx₀y_le_x₀y₀ :
        c ⬝ᵥ x₀ + lam ⬝ᵥ (y - x₀) ≤ c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) := by
      simpa [hy_eval y, hy_eval y₀] using hy_ge
    have hfinal :
        c ⬝ᵥ x + lam ⬝ᵥ (y - x) ≤ c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) :=
      hxy_le_x₀y.trans hx₀y_le_x₀y₀
    exact
      (show ((c ⬝ᵥ x + lam ⬝ᵥ (y - x) : ℝ) : EReal) ≤
          ((c ⬝ᵥ x₀ + lam ⬝ᵥ (y₀ - x₀) : ℝ) : EReal) by
        exact_mod_cast hfinal).trans <|
        le_sSup ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, rfl⟩

/-- Helper for Exercise 8.8: the product of the two convex hulls admits a flattened polyhedral
presentation once each factor hull is polyhedral. -/
lemma convexifiedProduct_eq_polyhedron
    {r₁ r₂ n : ℕ}
    {Q₁ Q₂ : Set (Fin n → ℝ)}
    (C₁ : Matrix (Fin r₁) (Fin n) ℝ)
    (d₁ : Fin r₁ → ℝ)
    (C₂ : Matrix (Fin r₂) (Fin n) ℝ)
    (d₂ : Fin r₂ → ℝ)
    (hQ₁ : convexHull ℝ Q₁ = polyhedron_le_set C₁ d₁)
    (hQ₂ : convexHull ℝ Q₂ = polyhedron_le_set C₂ d₂) :
    (Fin.appendEquiv n n) ''
        Set.prod (convexHull ℝ Q₁) (convexHull ℝ Q₂) =
      polyhedron_le_set
        (mixedConstraintMatrix
          (splitHullProductIntegerMatrix C₁)
          (splitHullProductContinuousMatrix C₂))
        (splitHullProductRhs d₁ d₂) := by
  -- The flattened product inequalities are exactly the two factor systems on the two blocks.
  ext z
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rcases xy with ⟨x, y⟩
    rw [mem_polyhedron_le_set_iff]
    have hxPoly : x ∈ polyhedron_le_set C₁ d₁ := by
      simpa [hQ₁] using hxy.1
    have hyPoly : y ∈ polyhedron_le_set C₂ d₂ := by
      simpa [hQ₂] using hxy.2
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hj := (mem_polyhedron_le_set_iff.mp hxPoly) j
      simpa [splitHullProductIntegerMatrix, splitHullProductContinuousMatrix,
        splitHullProductRhs, mixedConstraintMatrix_mulVec_append, Fin.appendEquiv,
        Fin.append, Fin.natAdd_eq_addNat]
        using hj
    · intro j
      have hj := (mem_polyhedron_le_set_iff.mp hyPoly) j
      simpa [splitHullProductIntegerMatrix, splitHullProductContinuousMatrix,
        splitHullProductRhs, mixedConstraintMatrix_mulVec_append, Fin.appendEquiv,
        Fin.append, Fin.natAdd_eq_addNat]
        using hj
  · intro hz
    let x : Fin n → ℝ := fun i ↦ z (Fin.castAdd n i)
    let y : Fin n → ℝ := fun i ↦ z (Fin.natAdd n i)
    have hxy : Fin.append x y = z := by
      exact Fin.append_castAdd_natAdd
    have hxPoly : x ∈ polyhedron_le_set C₁ d₁ := by
      rw [mem_polyhedron_le_set_iff]
      intro i
      have hi := (mem_polyhedron_le_set_iff.mp hz) (Fin.castAdd r₂ i)
      rw [← hxy] at hi
      simpa [x, y, splitHullProductIntegerMatrix, splitHullProductContinuousMatrix,
        splitHullProductRhs, mixedConstraintMatrix_mulVec_append, Fin.appendEquiv,
        Fin.append, Fin.natAdd_eq_addNat]
        using hi
    have hyPoly : y ∈ polyhedron_le_set C₂ d₂ := by
      rw [mem_polyhedron_le_set_iff]
      intro i
      have hi := (mem_polyhedron_le_set_iff.mp hz) (Fin.natAdd r₁ i)
      rw [← hxy] at hi
      simpa [x, y, splitHullProductIntegerMatrix, splitHullProductContinuousMatrix,
        splitHullProductRhs, mixedConstraintMatrix_mulVec_append, Fin.appendEquiv,
        Fin.append, Fin.natAdd_eq_addNat]
        using hi
    refine ⟨(x, y), ?_, ?_⟩
    · simpa [hQ₁, hQ₂] using And.intro hxPoly hyPoly
    · ext i
      exact congrFun hxy i

/-- Helper for Exercise 8.8: the polyhedral split relaxation with nonnegative row multipliers
depends only on the difference between the upper and lower multiplier blocks. -/
lemma polyhedralSplitRelaxation_eq_convexifiedProductValue
    {r : ℕ}
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin r) (Fin (n + n)) ℝ)
    (e : Fin r → ℝ)
    (hpoly :
      (Fin.appendEquiv n n) ''
        Set.prod
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) =
        polyhedron_le_set B e)
    (u : Fin (n + n) → ℝ) :
    lagrangian_relaxation_value splitRowMatrix splitRowRhs (splitFlatObjective c)
        (polyhedron_le_set B e) u =
      sSup
        ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 +
                (fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)) ⬝ᵥ (xy.2 - xy.1) : ℝ) :
              EReal)) ''
          Set.prod
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂))) := by
  -- Rewrite the polyhedral relaxation over the flattened product image and evaluate it on
  -- appended pairs.
  rw [lagrangian_relaxation_value_eq_sSup, ← hpoly]
  have himage :
      (fun z : Fin (n + n) → ℝ ↦
          ((splitFlatObjective c ⬝ᵥ z + u ⬝ᵥ (splitRowRhs - splitRowMatrix *ᵥ z) : ℝ) :
            EReal)) ''
        ((Fin.appendEquiv n n) ''
          Set.prod
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂))) =
        (fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 +
                (fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)) ⬝ᵥ (xy.2 - xy.1) : ℝ) :
              EReal)) ''
          Set.prod
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) := by
    ext v
    constructor
    · rintro ⟨z, ⟨xy, hxy, rfl⟩, rfl⟩
      rcases xy with ⟨x, y⟩
      refine ⟨(x, y), hxy, ?_⟩
      simpa [Fin.appendEquiv] using
        congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
          (splitPenalizedObjective_dot_append c u x y).symm
    · rintro ⟨xy, hxy, rfl⟩
      rcases xy with ⟨x, y⟩
      refine ⟨Fin.appendEquiv n n (x, y), ⟨(x, y), hxy, rfl⟩, ?_⟩
      simpa [Fin.appendEquiv] using
        congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
          (splitPenalizedObjective_dot_append c u x y)
  exact congrArg sSup himage

/-- Helper for Exercise 8.8: any unrestricted equality multiplier splits as the difference of two
nonnegative split-row multipliers. -/
lemma exists_nonnegative_splitMultipliers_sub_eq
    {n : ℕ}
    (lam : Fin n → ℝ) :
    ∃ u : Fin (n + n) → ℝ,
      0 ≤ u ∧
        (fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)) = lam := by
  -- Split each unrestricted multiplier into its positive and negative parts.
  refine ⟨Fin.append (fun i ↦ max (lam i) 0) (fun i ↦ max (-lam i) 0), ?_, ?_⟩
  · intro i
    cases hi : finSumFinEquiv.symm i with
    | inl j =>
        have hij : Fin.castAdd n j = i := by
          simpa [hi] using finSumFinEquiv.apply_symm_apply i
        simpa [← hij] using le_max_right (lam j) 0
    | inr j =>
        have hij : Fin.natAdd n j = i := by
          simpa [hi] using finSumFinEquiv.apply_symm_apply i
        simpa [Fin.natAdd_eq_addNat, ← hij] using le_max_right (-lam j) 0
  · ext i
    rw [Fin.append_left, Fin.append_right]
    by_cases hi : 0 ≤ lam i
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · have hlt : lam i < 0 := lt_of_not_ge hi
      have hnonpos : lam i ≤ 0 := le_of_lt hlt
      simp [max_eq_right hnonpos, max_eq_left (neg_nonneg.mpr hnonpos)]

/-- Helper for Exercise 8.8: once the convexified product is polyhedral, the unrestricted split
dual equals the generic polyhedral dual on the split-row system. -/
lemma splitConvexifiedDual_eq_polyhedralSplitDual
    {r : ℕ}
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin r) (Fin (n + n)) ℝ)
    (e : Fin r → ℝ)
    (hpoly :
      (Fin.appendEquiv n n) ''
        Set.prod
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) =
        polyhedron_le_set B e) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c =
      polyhedralLagrangianDualValue splitRowMatrix splitRowRhs (splitFlatObjective c) B e := by
  -- Compare the two infima pointwise after normalizing both fixed-multiplier relaxations.
  rw [split_mixed_integer_lagrangian_dual_value_eq_sInf,
    polyhedralLagrangianDualValue_eq_sInf]
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨u, hu, rfl⟩
    let lam : Fin n → ℝ := fun i ↦ u (Fin.castAdd n i) - u (Fin.natAdd n i)
    have hsplit :
        sInf
            (Set.range fun lam : Fin n → ℝ ↦
              split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam) ≤
          split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
      exact sInf_le ⟨lam, rfl⟩
    have hrel :
        split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
          lagrangian_relaxation_value splitRowMatrix splitRowRhs (splitFlatObjective c)
            (polyhedron_le_set B e) u := by
      rw [splitRelaxationValue_eq_convexifiedProductValue hp A₁ b₁ A₂ b₂ c lam]
      symm
      exact
        polyhedralSplitRelaxation_eq_convexifiedProductValue
          hp A₁ b₁ A₂ b₂ c B e hpoly u
    exact hsplit.trans (by simpa [lam] using hrel.le)
  · refine le_sInf ?_
    rintro _ ⟨lam, rfl⟩
    rcases exists_nonnegative_splitMultipliers_sub_eq lam with ⟨u, hu, hu_eq⟩
    have hpoly_le :
        sInf
            ((fun u : Fin (n + n) → ℝ ↦
                lagrangian_relaxation_value splitRowMatrix splitRowRhs (splitFlatObjective c)
                  (polyhedron_le_set B e) u) ''
              Set.Ici (0 : Fin (n + n) → ℝ)) ≤
          lagrangian_relaxation_value splitRowMatrix splitRowRhs (splitFlatObjective c)
            (polyhedron_le_set B e) u := by
      exact sInf_le ⟨u, hu, rfl⟩
    have hrel :
        lagrangian_relaxation_value splitRowMatrix splitRowRhs (splitFlatObjective c)
            (polyhedron_le_set B e) u =
          split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
      rw [polyhedralSplitRelaxation_eq_convexifiedProductValue hp A₁ b₁ A₂ b₂ c B e hpoly u,
        hu_eq, splitRelaxationValue_eq_convexifiedProductValue hp A₁ b₁ A₂ b₂ c lam]
    exact hpoly_le.trans hrel.le

/-- Helper for Exercise 8.8: the split-row primal feasible set consists exactly of diagonal
flattenings `Fin.append x x` with `x ∈ conv(Q₁) ∩ conv(Q₂)`. -/
lemma mem_splitPolyhedralPrimal_iff_diagonal
    {r : ℕ}
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (B : Matrix (Fin r) (Fin (n + n)) ℝ)
    (e : Fin r → ℝ)
    (hpoly :
      (Fin.appendEquiv n n) ''
        Set.prod
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) =
        polyhedron_le_set B e)
    {z : Fin (n + n) → ℝ} :
    z ∈ lagrangian_integer_feasible_set splitRowMatrix splitRowRhs (polyhedron_le_set B e) ↔
      ∃ x, x ∈ split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂ ∧ z = Fin.append x x := by
  constructor
  · intro hz
    rw [mem_lagrangian_integer_feasible_set_iff] at hz
    have hzImage :
        z ∈
          (Fin.appendEquiv n n) ''
            Set.prod
              (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
              (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) := by
      simpa [hpoly] using hz.1
    rcases hzImage with ⟨xy, hxy, rfl⟩
    rcases xy with ⟨x, y⟩
    have hdiag : x = y := by
      exact (splitRowMatrix_mulVec_append_nonpos_iff).1 <| by
        simpa [splitRowRhs, Fin.appendEquiv] using hz.2
    refine ⟨x, ?_, ?_⟩
    · -- The image witness lies in both convexified blocks, so the diagonal point lies in the
      -- intersection after rewriting `y` to `x`.
      rw [mem_split_mixed_integer_convex_hull_intersection_iff]
      exact ⟨hxy.1, hdiag ▸ hxy.2⟩
    · -- Flattening the diagonal pair `(x, x)` is exactly `Fin.append x x`.
      ext i
      simp [Fin.appendEquiv, hdiag]
  · rintro ⟨x, hx, rfl⟩
    rw [mem_lagrangian_integer_feasible_set_iff]
    refine ⟨?_, (splitRowMatrix_mulVec_append_nonpos_iff).2 rfl⟩
    have hxProd :
        (x, x) ∈
          Set.prod
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
            (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) := by
      exact (mem_split_mixed_integer_convex_hull_intersection_iff hp A₁ b₁ A₂ b₂).1 hx
    have hxImage :
        Fin.append x x ∈
          (Fin.appendEquiv n n) ''
            Set.prod
              (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
              (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) := by
      refine ⟨(x, x), hxProd, ?_⟩
      ext i
      simp [Fin.appendEquiv]
    simpa [hpoly] using hxImage

/-- Helper for Exercise 8.8: the polyhedral primal for the split rows is exactly the value over
`conv(Q₁) ∩ conv(Q₂)`. -/
lemma splitPolyhedralPrimal_eq_intersectionValue
    {r : ℕ}
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin r) (Fin (n + n)) ℝ)
    (e : Fin r → ℝ)
    (hpoly :
      (Fin.appendEquiv n n) ''
        Set.prod
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) =
        polyhedron_le_set B e) :
    integer_program_value splitRowMatrix splitRowRhs (splitFlatObjective c) (polyhedron_le_set B e) =
      split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c := by
  -- Rewrite both values as suprema, then identify the split-row feasible set with the diagonal
  -- copy of `conv(Q₁) ∩ conv(Q₂)`.
  rw [integer_program_value_eq_sSup, split_mixed_integer_convex_hull_intersection_value_eq_sSup]
  have himage :
      (fun z : Fin (n + n) → ℝ ↦ ((splitFlatObjective c ⬝ᵥ z : ℝ) : EReal)) ''
          lagrangian_integer_feasible_set splitRowMatrix splitRowRhs (polyhedron_le_set B e) =
        (fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂ := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases
          (mem_splitPolyhedralPrimal_iff_diagonal hp A₁ b₁ A₂ b₂ B e hpoly).1 hz with
        ⟨x, hx, hz_eq⟩
      subst hz_eq
      refine ⟨x, hx, ?_⟩
      simpa using
        congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
          (splitFlatObjective_dot_append c x x).symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Fin.append x x,
        (mem_splitPolyhedralPrimal_iff_diagonal hp A₁ b₁ A₂ b₂ B e hpoly).2 ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · simpa using
          congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
            (splitFlatObjective_dot_append c x x)
  exact congrArg sSup himage

/-- ch8_sec8_5_exercise_8_8. Exercise 8.8. In the setting of Sect. 8.1, let
`Qᵢ := {x ∈ ℤ_+^p × ℝ_+^(n-p) : Aᵢ x ≤ bⁱ}` for `i = 1, 2`, and assume each split block has the
Section 8.1 rational defining data recorded by
`HasSection81RationalPresentation Aᵢ bⁱ`. If `conv(Q₁) ∩ conv(Q₂)` is nonempty, then the optimal
value `z̄` of the Lagrangian dual obtained by dualizing `x - y = 0` in the split formulation
equals the canonical Chapter 8 value of maximizing `c x` over `conv(Q₁) ∩ conv(Q₂)`. -/
theorem dual_eq_convex_hull_intersection_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (hQ₁ : HasSection81RationalPresentation A₁ b₁)
    (hQ₂ : HasSection81RationalPresentation A₂ b₂)
    (hfeas :
      Set.Nonempty (split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂)) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c =
      split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c := by
  -- Route correction: use the polyhedral-duality owner from Proposition 8.8 rather than the
  -- older separation wrapper around zero-displacement certificates.
  obtain ⟨r₁, C₁, d₁, hHull₁⟩ :=
    convexHull_mixedIntegerEqualityBase_eq_polyhedron hp A₁ b₁ hQ₁
  obtain ⟨r₂, C₂, d₂, hHull₂⟩ :=
    convexHull_mixedIntegerEqualityBase_eq_polyhedron hp A₂ b₂ hQ₂
  let B :
      Matrix (Fin (r₁ + r₂)) (Fin (n + n)) ℝ :=
    mixedConstraintMatrix
      (splitHullProductIntegerMatrix C₁)
      (splitHullProductContinuousMatrix C₂)
  let e : Fin (r₁ + r₂) → ℝ := splitHullProductRhs d₁ d₂
  have hpoly :
      (Fin.appendEquiv n n) ''
        Set.prod
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁))
          (convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)) =
        polyhedron_le_set B e := by
    -- Replace each convexified block with its polyhedral presentation, then flatten the product.
    simpa [B, e] using
      convexifiedProduct_eq_polyhedron C₁ d₁ C₂ d₂ hHull₁ hHull₂
  have hnonempty :
      Set.Nonempty
        (lagrangian_integer_feasible_set splitRowMatrix splitRowRhs (polyhedron_le_set B e)) := by
    rcases hfeas with ⟨x, hx⟩
    -- A feasible intersection point produces the diagonal split-row witness `Fin.append x x`.
    refine ⟨Fin.append x x,
      (mem_splitPolyhedralPrimal_iff_diagonal hp A₁ b₁ A₂ b₂ B e hpoly).2 ?_⟩
    exact ⟨x, hx, rfl⟩
  calc
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c
        = polyhedralLagrangianDualValue splitRowMatrix splitRowRhs (splitFlatObjective c) B e := by
            exact splitConvexifiedDual_eq_polyhedralSplitDual hp A₁ b₁ A₂ b₂ c B e hpoly
    _ = integer_program_value splitRowMatrix splitRowRhs (splitFlatObjective c) (polyhedron_le_set B e) := by
          exact polyhedralLagrangianDualValue_eq_integerProgramValue
            splitRowMatrix splitRowRhs (splitFlatObjective c) B e (Or.inl hnonempty)
    _ = split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c := by
          exact splitPolyhedralPrimal_eq_intersectionValue hp A₁ b₁ A₂ b₂ c B e hpoly

end SplitMixedInteger

end Exercise88
