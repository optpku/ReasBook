/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Pointwise

section Theorem45

variable {m n : ℕ}

/-- The polyhedron in `ℝ^n` cut out by the interval system
`c ≤ A x ≤ d` and `l ≤ x ≤ u`, where the matrix and bounds are integral and are coerced to `ℝ`
in the defining inequalities. -/
def integer_interval_matrix_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) :
    Set (Fin n → ℝ) :=
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  {x | (fun i ↦ (c i : ℝ)) ≤ AReal *ᵥ x ∧
      AReal *ᵥ x ≤ (fun i ↦ (d i : ℝ)) ∧
      (fun j ↦ (l j : ℝ)) ≤ x ∧
      x ≤ (fun j ↦ (u j : ℝ))}

/-- Membership in `integer_interval_matrix_polyhedron A c d l u` is exactly the coordinatewise
system `c ≤ A x ≤ d` together with the box constraints `l ≤ x ≤ u`. -/
theorem mem_integer_interval_matrix_polyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) (x : Fin n → ℝ) :
    x ∈ integer_interval_matrix_polyhedron A c d l u ↔
      (fun i ↦ (c i : ℝ)) ≤ (A.map (Int.castRingHom ℝ)) *ᵥ x ∧
      (A.map (Int.castRingHom ℝ)) *ᵥ x ≤ (fun i ↦ (d i : ℝ)) ∧
      (fun j ↦ (l j : ℝ)) ≤ x ∧
      x ≤ (fun j ↦ (u j : ℝ)) := by
  -- Unfold the defining set and simplify the local real-cast matrix abbreviation.
  simp [integer_interval_matrix_polyhedron]

/-- Helper for Theorem 4.5: the three blocks of the interval reduction matrix are indexed by the
upper bounds, lower bounds, and box constraints. -/
private abbrev interval_reduction_row (m n : ℕ) := (Fin m ⊕ Fin m) ⊕ Fin n

/-- Helper for Theorem 4.5: the row index for the interval reduction matrix is reindexed to a
single `Fin` type so that Theorem 4.4 applies directly. -/
private def interval_reduction_row_equiv (m n : ℕ) :
    interval_reduction_row m n ≃ Fin ((m + m) + n) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- Helper for Theorem 4.5: the unreindexed matrix encoding the inequalities
`A (x - l) ≤ d - A l`, `-A (x - l) ≤ A l - c`, and `x - l ≤ u - l`. -/
private def interval_reduction_matrix_raw
    (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (interval_reduction_row m n) (Fin n) ℤ :=
  Matrix.fromRows (Matrix.fromRows A (-A)) (1 : Matrix (Fin n) (Fin n) ℤ)

/-- Helper for Theorem 4.5: the reindexed matrix used to reduce the interval system to the
nonnegative polyhedron from Theorem 4.4. -/
def interval_reduction_matrix
    (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin ((m + m) + n)) (Fin n) ℤ :=
  Matrix.reindex (interval_reduction_row_equiv m n) (Equiv.refl _) (interval_reduction_matrix_raw A)

/-- Helper for Theorem 4.5: the unreindexed right-hand side corresponding to the translated system
for `y = x - l`. -/
private def interval_reduction_rhs_raw
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) :
    interval_reduction_row m n → ℤ
  | Sum.inl (Sum.inl i) => d i - (A *ᵥ l) i
  | Sum.inl (Sum.inr i) => (A *ᵥ l) i - c i
  | Sum.inr j => u j - l j

/-- Helper for Theorem 4.5: the reindexed right-hand side for the reduction matrix. -/
def interval_reduction_rhs
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) :
    Fin ((m + m) + n) → ℤ :=
  interval_reduction_rhs_raw A c d l u ∘ (interval_reduction_row_equiv m n).symm

/-- Helper for Theorem 4.5: on a raw row of the interval reduction matrix, multiplication by a
vector returns the corresponding `A`, `-A`, or identity block entry. -/
private theorem interval_reduction_matrix_raw_mulVec_apply
    (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin n → ℝ) (r : interval_reduction_row m n) :
    (((interval_reduction_matrix_raw A).map (Int.castRingHom ℝ)) *ᵥ y) r =
      (Sum.elim
        (Sum.elim ((A.map (Int.castRingHom ℝ)) *ᵥ y)
          ((-(A.map (Int.castRingHom ℝ))) *ᵥ y))
        y) r := by
  -- Expand the outer and inner `fromRows` multiplications once, then read off the chosen row.
  have hnegMap :
      (-A).map (Int.castRingHom ℝ) = -(A.map (Int.castRingHom ℝ)) := by
    ext i j
    simp
  cases r with
  | inl r =>
      cases r with
      | inl i =>
          simp [interval_reduction_matrix_raw, Matrix.fromRows_map, Matrix.fromRows_mulVec,
            Matrix.neg_mulVec]
      | inr i =>
          simp [interval_reduction_matrix_raw, Matrix.fromRows_map, Matrix.fromRows_mulVec]
          change (((-A).map (Int.castRingHom ℝ)) *ᵥ y) i =
              ((-(A.map (Int.castRingHom ℝ))) *ᵥ y) i
          rw [hnegMap]
  | inr j =>
      simp [interval_reduction_matrix_raw, Matrix.fromRows_map, Matrix.fromRows_mulVec,
        Matrix.neg_mulVec]

/-- Helper for Theorem 4.5: after reindexing the interval reduction matrix, multiplication by a
vector simply reads off the three expected blocks. -/
private theorem interval_reduction_matrix_mulVec
    (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin n → ℝ) :
    ((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y =
      (Sum.elim
        (Sum.elim ((A.map (Int.castRingHom ℝ)) *ᵥ y)
          ((-(A.map (Int.castRingHom ℝ))) *ᵥ y))
        y) ∘ (interval_reduction_row_equiv m n).symm := by
  let e := interval_reduction_row_equiv m n
  ext i
  have hreindex :
      (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y) i =
        (((interval_reduction_matrix_raw A).map (Int.castRingHom ℝ)) *ᵥ y) (e.symm i) := by
    -- Reindexing the rows only composes the output vector with the inverse equivalence.
    simpa [interval_reduction_matrix, e, Matrix.reindex_apply] using
      congrFun
        (Matrix.submatrix_mulVec_equiv
          ((interval_reduction_matrix_raw A).map (Int.castRingHom ℝ))
          y e.symm (Equiv.refl (Fin n)))
        i
  rw [hreindex, interval_reduction_matrix_raw_mulVec_apply]
  rfl

/-- Helper for Theorem 4.5: the interval polyhedron is exactly the translated nonnegative
polyhedron obtained from the reduction matrix. -/
theorem mem_interval_reduction_polyhedron_shift_iff
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) (x : Fin n → ℝ) :
    x ∈ integer_interval_matrix_polyhedron A c d l u ↔
      (fun j ↦ x j - (l j : ℝ)) ∈
        nonnegative_matrix_polyhedron (interval_reduction_matrix A)
          (interval_reduction_rhs A c d l u) := by
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  let y : Fin n → ℝ := fun j ↦ x j - (l j : ℝ)
  have hAl :
      AReal *ᵥ (fun j ↦ (l j : ℝ)) = fun i ↦ ((A *ᵥ l) i : ℝ) := by
    -- Cast the integral matrix-vector product once so the remaining inequalities are purely real.
    ext i
    simpa [AReal] using (RingHom.map_mulVec (Int.castRingHom ℝ) A l i).symm
  have hAy :
      AReal *ᵥ y = AReal *ᵥ x - fun i ↦ ((A *ᵥ l) i : ℝ) := by
    -- The translated variable is `y = x - l`, so its image under `A` is `Ax - Al`.
    have hmul :
        AReal *ᵥ y = AReal *ᵥ x - AReal *ᵥ (fun j ↦ (l j : ℝ)) := by
      simpa [y] using Matrix.mulVec_sub AReal x (fun j ↦ (l j : ℝ))
    simpa [hAl] using hmul
  constructor
  · intro hx
    rcases (mem_integer_interval_matrix_polyhedron_iff A c d l u x).1 hx with
      ⟨hc, hd, hl, hu⟩
    refine ⟨?_, ?_⟩
    · intro s
      rcases hrow : (interval_reduction_row_equiv m n).symm s with ((i | i) | j)
      · have hiAy :
            (AReal *ᵥ y) i = (AReal *ᵥ x) i - ((A *ᵥ l) i : ℝ) := by
          simpa [AReal, y] using congrFun hAy i
        have hblock :
            (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
                ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i))) =
              (AReal *ᵥ y) i := by
          rw [interval_reduction_matrix_mulVec]
          simp [AReal]
        have hi :
            (AReal *ᵥ y) i ≤ (d i : ℝ) - ((A *ᵥ l) i : ℝ) := by
          nlinarith [hd i, hiAy]
        have hs : s = (interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i)) := by
          simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
        rw [hs, hblock]
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, AReal] using hi
      · have hiAy :
            (AReal *ᵥ y) i = (AReal *ᵥ x) i - ((A *ᵥ l) i : ℝ) := by
          simpa [AReal, y] using congrFun hAy i
        have hblock :
            (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
                ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i))) =
              -((AReal *ᵥ y) i) := by
          rw [interval_reduction_matrix_mulVec]
          simp [AReal, Matrix.neg_mulVec]
        have hi :
            -((AReal *ᵥ y) i) ≤ ((A *ᵥ l) i : ℝ) - (c i : ℝ) := by
          nlinarith [hc i, hiAy]
        have hs : s = (interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i)) := by
          simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
        rw [hs, hblock]
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, AReal, sub_eq_add_neg] using hi
      · have hj : y j ≤ (u j : ℝ) - (l j : ℝ) := by
          dsimp [y]
          nlinarith [hu j]
        have hblock :
            (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
                ((interval_reduction_row_equiv m n) (Sum.inr j)) =
              y j := by
          rw [interval_reduction_matrix_mulVec]
          simp
        have hs : s = (interval_reduction_row_equiv m n) (Sum.inr j) := by
          simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
        rw [hs, hblock]
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, y] using hj
    · intro j
      exact sub_nonneg.mpr (hl j)
  · rintro ⟨hy, hy_nonneg⟩
    refine (mem_integer_interval_matrix_polyhedron_iff A c d l u x).2 ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hi₀ :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i))) ≤
            ((interval_reduction_rhs A c d l u)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i))) : ℝ) :=
        hy ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i)))
      have hblock :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i))) =
            -((AReal *ᵥ y) i) := by
        rw [interval_reduction_matrix_mulVec]
        simp [AReal, Matrix.neg_mulVec]
      have hi :
          -((AReal *ᵥ y) i) ≤ ((A *ᵥ l) i : ℝ) - (c i : ℝ) := by
        rw [hblock] at hi₀
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, AReal, y, sub_eq_add_neg] using
          hi₀
      have hiAy :
          (AReal *ᵥ y) i = (AReal *ᵥ x) i - ((A *ᵥ l) i : ℝ) := by
        simpa [AReal, y] using congrFun hAy i
      nlinarith [hi, hiAy]
    · intro i
      have hi₀ :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i))) ≤
            ((interval_reduction_rhs A c d l u)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i))) : ℝ) :=
        hy ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i)))
      have hblock :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i))) =
            (AReal *ᵥ y) i := by
        rw [interval_reduction_matrix_mulVec]
        simp [AReal]
      have hi :
          (AReal *ᵥ y) i ≤ (d i : ℝ) - ((A *ᵥ l) i : ℝ) := by
        rw [hblock] at hi₀
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, AReal, y] using hi₀
      have hiAy :
          (AReal *ᵥ y) i = (AReal *ᵥ x) i - ((A *ᵥ l) i : ℝ) := by
        simpa [AReal, y] using congrFun hAy i
      nlinarith [hi, hiAy]
    · intro j
      have hj : 0 ≤ y j := hy_nonneg j
      dsimp [y] at hj
      linarith
    · intro j
      have hj₀ :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inr j)) ≤
            ((interval_reduction_rhs A c d l u)
              ((interval_reduction_row_equiv m n) (Sum.inr j)) : ℝ) :=
        hy ((interval_reduction_row_equiv m n) (Sum.inr j))
      have hblock :
          (((interval_reduction_matrix A).map (Int.castRingHom ℝ)) *ᵥ y)
              ((interval_reduction_row_equiv m n) (Sum.inr j)) =
            y j := by
        rw [interval_reduction_matrix_mulVec]
        simp
      have hj :
          y j ≤ (u j : ℝ) - (l j : ℝ) := by
        rw [hblock] at hj₀
        simpa [interval_reduction_rhs, interval_reduction_rhs_raw, y] using hj₀
      dsimp [y] at hj
      linarith

/-- Helper for Theorem 4.5: the interval polyhedron is the translate of the reduced nonnegative
polyhedron by the lower-bound vector `l`. -/
private theorem integer_interval_matrix_polyhedron_eq_translate_reduced
    (A : Matrix (Fin m) (Fin n) ℤ) (c d : Fin m → ℤ) (l u : Fin n → ℤ) :
    integer_interval_matrix_polyhedron A c d l u =
      (fun j ↦ (l j : ℝ)) +ᵥ
        nonnegative_matrix_polyhedron (interval_reduction_matrix A)
          (interval_reduction_rhs A c d l u) := by
  -- Route correction: package the translation equivalence once so the closing theorem no longer
  -- repeats the `Set.mem_vadd_set` transport argument inline.
  ext x
  constructor
  · intro hx
    -- Rewrite membership as `x = l + (x - l)` and use the shift lemma for the reduced system.
    rw [Set.mem_vadd_set]
    refine ⟨fun j ↦ x j - (l j : ℝ), ?_, ?_⟩
    · exact (mem_interval_reduction_polyhedron_shift_iff A c d l u x).1 hx
    · funext j
      simp
  · intro hx
    -- Read a translated point as `l + y`, then cancel the translation inside the shift lemma.
    rw [Set.mem_vadd_set] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' :
        (fun j ↦ (fun j ↦ (l j : ℝ) + y j) j - (l j : ℝ)) ∈
          nonnegative_matrix_polyhedron (interval_reduction_matrix A)
            (interval_reduction_rhs A c d l u) := by
      simpa [Pi.add_apply] using hy
    simpa [Pi.vadd_def, vadd_eq_add, Pi.add_apply, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm] using
      (mem_interval_reduction_polyhedron_shift_iff
        A c d l u (fun j ↦ (l j : ℝ) + y j)).2 hy'

/-- Helper for Theorem 4.5: with zero lower bounds, the interval system is exactly the reduced
nonnegative system associated to the chosen right-hand side `b`. -/
private theorem interval_reduction_zero_lower_eq_nonnegative
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin ((m + m) + n) → ℤ) :
    integer_interval_matrix_polyhedron A
      (fun i ↦ -b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i))))
      (fun i ↦ b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i))))
      (fun _ ↦ 0)
      (fun j ↦ b ((interval_reduction_row_equiv m n) (Sum.inr j))) =
      nonnegative_matrix_polyhedron (interval_reduction_matrix A) b := by
  let c : Fin m → ℤ := fun i ↦ -b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i)))
  let d : Fin m → ℤ := fun i ↦ b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i)))
  let u : Fin n → ℤ := fun j ↦ b ((interval_reduction_row_equiv m n) (Sum.inr j))
  have hAzero : A *ᵥ (fun _ ↦ 0) = 0 := by
    -- The zero lower bound removes the translation term from the reduced right-hand side.
    ext i
    simp [Matrix.mulVec]
  have hRhs : interval_reduction_rhs A c d (fun _ ↦ 0) u = b := by
    -- Each reindexed row of the reduced right-hand side is read directly from the chosen `b`.
    ext s
    rcases hrow : (interval_reduction_row_equiv m n).symm s with ((i | i) | j)
    · have hs : s = (interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i)) := by
        simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
      rw [hs]
      simp [interval_reduction_rhs, interval_reduction_rhs_raw, c, d, hAzero]
    · have hs : s = (interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i)) := by
        simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
      rw [hs]
      simp [interval_reduction_rhs, interval_reduction_rhs_raw, c, d, hAzero]
    · have hs : s = (interval_reduction_row_equiv m n) (Sum.inr j) := by
        simpa [hrow] using ((interval_reduction_row_equiv m n).apply_symm_apply s).symm
      rw [hs]
      simp [interval_reduction_rhs, interval_reduction_rhs_raw, u]
  -- Route correction: isolate the zero-lower bookkeeping so the main theorem can invoke
  -- Theorem 4.4 directly after a single rewrite.
  ext x
  simpa [c, d, u, hRhs] using
    (mem_interval_reduction_polyhedron_shift_iff A c d (fun _ ↦ 0) u x)

/-- Helper for Theorem 4.5: translating a point by an integral vector preserves integrality. -/
theorem mem_integerVectors_translate_iff
    (a : Fin n → ℤ) (x : Fin n → ℝ) :
    (fun j ↦ x j + (a j : ℝ)) ∈ integerVectors n ↔ x ∈ integerVectors n := by
  -- Coordinatewise, adding an integral vector just shifts each integer witness.
  rw [mem_integerVectors_iff_forall, mem_integerVectors_iff_forall]
  constructor
  · intro hx j
    rcases hx j with ⟨z, hz⟩
    refine ⟨z - a j, ?_⟩
    calc
      ((z - a j : ℤ) : ℝ) = (z : ℝ) - (a j : ℝ) := by simp
      _ = (x j + (a j : ℝ)) - (a j : ℝ) := by rw [hz]
      _ = x j := by ring
  · intro hx j
    rcases hx j with ⟨z, hz⟩
    refine ⟨z + a j, ?_⟩
    calc
      ((z + a j : ℤ) : ℝ) = (z : ℝ) + (a j : ℝ) := by simp
      _ = x j + (a j : ℝ) := by rw [hz]

/-- Helper for Theorem 4.5: translating a set by an integral vector translates its integral
points exactly. -/
theorem integral_points_translate_eq
    (a : Fin n → ℤ) (P : Set (Fin n → ℝ)) :
    ((fun j ↦ (a j : ℝ)) +ᵥ P) ∩ integerVectors n =
      (fun j ↦ (a j : ℝ)) +ᵥ (P ∩ integerVectors n) := by
  -- Unfold set translation and transport the integer-point condition through the translation.
  ext x
  constructor
  · rintro ⟨hx, hxInt⟩
    rw [Set.mem_vadd_set] at hx
    rcases hx with ⟨y, hyP, rfl⟩
    rw [Set.mem_vadd_set]
    refine ⟨y, ?_, rfl⟩
    refine ⟨hyP, ?_⟩
    have hyInt :
        (fun j ↦ y j + (a j : ℝ)) ∈ integerVectors n := by
      simpa [Pi.vadd_def, vadd_eq_add, add_comm] using hxInt
    exact (mem_integerVectors_translate_iff a y).1 hyInt
  · intro hx
    rw [Set.mem_vadd_set] at hx
    rcases hx with ⟨y, ⟨hyP, hyInt⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Set.mem_vadd_set]
      exact ⟨y, hyP, rfl⟩
    · have hxInt :
          (fun j ↦ y j + (a j : ℝ)) ∈ integerVectors n :=
        (mem_integerVectors_translate_iff a y).2 hyInt
      simpa [Pi.vadd_def, vadd_eq_add, add_comm] using hxInt

/-- Helper for Theorem 4.5: translating by `a` and then by `-a` returns the original set. -/
private theorem integer_translation_neg_cancel
    (a : Fin n → ℤ) (P : Set (Fin n → ℝ)) :
    (fun j ↦ ((-a j : ℤ) : ℝ)) +ᵥ ((fun j ↦ (a j : ℝ)) +ᵥ P) = P := by
  -- Unfold both translations and cancel the two integral shifts coordinatewise.
  ext x
  constructor
  · intro hx
    rw [Set.mem_vadd_set] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Set.mem_vadd_set] at hy
    rcases hy with ⟨z, hz, rfl⟩
    convert hz using 1
    funext j
    simp
  · intro hx
    rw [Set.mem_vadd_set]
    refine ⟨fun j ↦ (a j : ℝ) + x j, ?_, ?_⟩
    · rw [Set.mem_vadd_set]
      exact ⟨x, hx, rfl⟩
    · funext j
      simp [vadd_eq_add]

/-- Helper for Theorem 4.5: translating an integral polyhedron by an integral vector preserves
integrality. -/
theorem is_integral_translate
    (a : Fin n → ℤ) {P : Set (Fin n → ℝ)} (hP : is_integral P) :
    is_integral ((fun j ↦ (a j : ℝ)) +ᵥ P) := by
  rw [is_integral_iff] at hP ⊢
  -- Push the source integral decomposition through translation and use convex-hull equivariance.
  calc
    (fun j ↦ (a j : ℝ)) +ᵥ P
        = (fun j ↦ (a j : ℝ)) +ᵥ convexHull ℝ (P ∩ integerVectors n) := by
          exact congrArg (fun s ↦ (fun j ↦ (a j : ℝ)) +ᵥ s) hP
    _ = convexHull ℝ ((fun j ↦ (a j : ℝ)) +ᵥ (P ∩ integerVectors n)) := by
      symm
      exact convexHull_vadd (fun j ↦ (a j : ℝ)) (P ∩ integerVectors n)
    _ = convexHull ℝ (((fun j ↦ (a j : ℝ)) +ᵥ P) ∩ integerVectors n) := by
      rw [(integral_points_translate_eq a P).symm]

/-- Helper for Theorem 4.5: integral polyhedra are invariant under translation by an integral
vector. -/
theorem is_integral_translate_iff
    (a : Fin n → ℤ) (P : Set (Fin n → ℝ)) :
    is_integral ((fun j ↦ (a j : ℝ)) +ᵥ P) ↔ is_integral P := by
  constructor
  · intro h
    -- Translate back by `-a` to recover the original set.
    have hBack :
        is_integral ((fun j ↦ ((-a j : ℤ) : ℝ)) +ᵥ ((fun j ↦ (a j : ℝ)) +ᵥ P)) :=
      is_integral_translate (-a) h
    rw [integer_translation_neg_cancel a P] at hBack
    exact hBack
  · intro h
    exact is_integral_translate a h

/-- Helper for Theorem 4.5: duplicating every row of a totally unimodular matrix preserves total
unimodularity. -/
private theorem fromRows_self_isTotallyUnimodular_iff
    (A : Matrix (Fin m) (Fin n) ℤ) :
    (Matrix.fromRows A A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor
  · intro hAA
    exact hAA.submatrix Sum.inl id
  · intro hA
    -- `fromRows A A` is just a row-submatrix of `A` with repeated rows allowed.
    have hdup : Matrix.fromRows A A = A.submatrix (Sum.elim id id) id := by
      ext i j
      cases i <;> simp
    simpa [hdup] using hA.submatrix (Sum.elim id id) (id)

/-- Helper for Theorem 4.5: the sign attached to a duplicated row block records whether that row
comes from `A` or from `-A`. -/
private def duplicated_row_sign : Fin m ⊕ Fin m → SignType :=
  Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

/-- Helper for Theorem 4.5: every square submatrix of `fromRows A (-A)` is obtained from the
corresponding square submatrix of `fromRows A A` by multiplying rows by signs. -/
private theorem fromRows_self_neg_submatrix_eq_diagonal
    (A : Matrix (Fin m) (Fin n) ℤ) {k : ℕ}
    (f : Fin k → Fin m ⊕ Fin m) (g : Fin k → Fin n) :
    (Matrix.fromRows A (-A)).submatrix f g =
      Matrix.diagonal (fun i ↦ (duplicated_row_sign (f i) : ℤ)) *
        (Matrix.fromRows A A).submatrix f g := by
  -- Each selected row is either unchanged or multiplied by `-1`.
  ext i j
  cases hfi : f i with
  | inl r =>
      simp [duplicated_row_sign, hfi]
  | inr r =>
      simp [duplicated_row_sign, hfi]

/-- Helper for Theorem 4.5: adjoining the negated copy `-A` below `A` preserves total
unimodularity. -/
private theorem fromRows_self_neg_isTotallyUnimodular_iff
    (A : Matrix (Fin m) (Fin n) ℤ) :
    (Matrix.fromRows A (-A)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor
  · intro hA
    exact hA.submatrix Sum.inl id
  · intro hA
    have hDup : (Matrix.fromRows A A).IsTotallyUnimodular :=
      (fromRows_self_isTotallyUnimodular_iff A).2 hA
    rw [Matrix.isTotallyUnimodular_iff] at hDup ⊢
    intro k f g
    -- Compare the chosen minor to the duplicated-row minor by a diagonal sign matrix.
    have hsign :
        (Matrix.diagonal (fun i ↦ (duplicated_row_sign (f i) : ℤ))).det ∈
          Set.range SignType.cast := by
      refine ⟨∏ i, duplicated_row_sign (f i), ?_⟩
      have hcast :
          ((↑(∏ i, duplicated_row_sign (f i)) : ℤ)) =
            ∏ i, ↑(duplicated_row_sign (f i)) := by
        classical
        let u : Finset (Fin k) := Finset.univ
        change ((↑(Finset.prod u (fun i ↦ duplicated_row_sign (f i))) : ℤ)) =
          Finset.prod u fun i ↦ ↑(duplicated_row_sign (f i))
        clear_value u
        induction u using Finset.induction_on with
        | empty =>
            simp
        | insert a s ha ih =>
            simp [ha, ih, SignType.coe_mul]
      simpa [Matrix.det_diagonal] using hcast
    rcases hsign with ⟨s₁, hs₁⟩
    rcases hDup k f g with ⟨s₂, hs₂⟩
    rw [fromRows_self_neg_submatrix_eq_diagonal, Matrix.det_mul]
    refine ⟨s₁ * s₂, ?_⟩
    simp [hs₁, hs₂, SignType.coe_mul]

/-- Helper for Theorem 4.5: the interval reduction matrix is totally unimodular exactly when the
original matrix is. -/
theorem interval_reduction_matrix_isTotallyUnimodular_iff
    (A : Matrix (Fin m) (Fin n) ℤ) :
    (interval_reduction_matrix A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  calc
    (interval_reduction_matrix A).IsTotallyUnimodular
        ↔ (interval_reduction_matrix_raw A).IsTotallyUnimodular := by
          simpa [interval_reduction_matrix] using
            Matrix.reindex_isTotallyUnimodular
              (interval_reduction_matrix_raw A) (interval_reduction_row_equiv m n)
              (Equiv.refl (Fin n))
    _ ↔ (Matrix.fromRows A (-A)).IsTotallyUnimodular := by
      simpa [interval_reduction_matrix_raw] using
        Matrix.fromRows_one_isTotallyUnimodular_iff (Matrix.fromRows A (-A))
    _ ↔ A.IsTotallyUnimodular := fromRows_self_neg_isTotallyUnimodular_iff A

/-- Theorem 4.5. Let `A` be an `m × n` integral matrix. The polyhedron
`Q := {x | c ≤ A x ≤ d, l ≤ x ≤ u}` is integral for all integral vectors `c`, `d`, `l`, and `u`
if and only if `A` is totally unimodular. -/
theorem integer_interval_matrix_polyhedron_integral_iff_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ) :
    (∀ c d : Fin m → ℤ, ∀ l u : Fin n → ℤ,
      is_integral (integer_interval_matrix_polyhedron A c d l u)) ↔
      A.IsTotallyUnimodular := by
  constructor
  · intro hInterval
    have hReduced :
        ∀ b : Fin ((m + m) + n) → ℤ,
          is_integral (nonnegative_matrix_polyhedron (interval_reduction_matrix A) b) := by
      intro b
      let c : Fin m → ℤ :=
        fun i ↦ -b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inr i)))
      let d : Fin m → ℤ :=
        fun i ↦ b ((interval_reduction_row_equiv m n) (Sum.inl (Sum.inl i)))
      let u : Fin n → ℤ :=
        fun j ↦ b ((interval_reduction_row_equiv m n) (Sum.inr j))
      -- Route correction: use the dedicated zero-lower equality instead of replaying the row
      -- bookkeeping inside the main implication.
      simpa [c, d, u, interval_reduction_zero_lower_eq_nonnegative (A := A) (b := b)] using
        hInterval c d (fun _ ↦ 0) u
    have hTU :
        (interval_reduction_matrix A).IsTotallyUnimodular :=
      (nonnegative_matrix_polyhedron_integral_iff_totally_unimodular
        (interval_reduction_matrix A)).1 hReduced
    exact (interval_reduction_matrix_isTotallyUnimodular_iff A).1 hTU
  · intro hA c d l u
    have hReducedTU :
        (interval_reduction_matrix A).IsTotallyUnimodular :=
      (interval_reduction_matrix_isTotallyUnimodular_iff A).2 hA
    have hReducedIntegral :
        is_integral
          (nonnegative_matrix_polyhedron (interval_reduction_matrix A)
            (interval_reduction_rhs A c d l u)) :=
      ((nonnegative_matrix_polyhedron_integral_iff_totally_unimodular
        (interval_reduction_matrix A)).2 hReducedTU) (interval_reduction_rhs A c d l u)
    -- Rewrite the interval system as a translate of the reduced system, then use translation
    -- invariance of integral polyhedra.
    rw [integer_interval_matrix_polyhedron_eq_translate_reduced A c d l u]
    exact (is_integral_translate_iff l _).2 hReducedIntegral

end Theorem45
