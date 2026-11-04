/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3

open scoped Matrix

/-- The projection onto the original real `x`-block of the mixed-integer points of
`P ⊆ ℤ^q × ℝ^(n+p)`, where the real block is decomposed as `(x,y)`. -/
def mixed_integer_x_projection
    {n p q : ℕ} (P : Set (MixedRealPoint q (n + p))) : Set (Fin n → ℝ) :=
  (fun wz : MixedRealPoint q (n + p) ↦ fun i ↦ wz.2 (Fin.castAdd p i)) '' mixed_integer_points P

/-- Membership in `mixed_integer_x_projection P` means that `x` extends to some auxiliary real
variables `y` and auxiliary integer variables `z` whose combined mixed-space point belongs to `P`.
-/
theorem mem_mixed_integer_x_projection_iff
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {x : Fin n → ℝ} :
    x ∈ mixed_integer_x_projection P ↔
      ∃ y : Fin p → ℝ, ∃ z : Fin q → ℤ,
        ((fun j ↦ (z j : ℝ)), Fin.append x y) ∈ P := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases (mem_mixed_integer_points_iff).1 hw with ⟨hP, hw⟩
    have hwz : w.1 ∈ integerVectors q := by
      simpa using (mem_mixed_integer_lattice_iff (n := q) (p := n + p) (xy := w)).1 hw
    rcases (mem_integerVectors_iff (n := q) (x := w.1)).1 hwz with ⟨z, hz⟩
    refine ⟨fun j ↦ w.2 (Fin.natAdd n j), z, ?_⟩
    have hw₂ : Fin.append (fun i ↦ w.2 (Fin.castAdd p i)) (fun j ↦ w.2 (Fin.natAdd n j)) = w.2 := by
      funext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp
      · intro i
        simp
    have hpair :
        ((fun j ↦ (z j : ℝ)),
            Fin.append (fun i ↦ w.2 (Fin.castAdd p i)) (fun j ↦ w.2 (Fin.natAdd n j))) = w := by
      apply Prod.ext
      · funext j
        exact congrFun hz.symm j
      · exact hw₂
    simpa [hpair] using hP
  · rintro ⟨y, z, hP⟩
    refine ⟨((fun j ↦ (z j : ℝ)), Fin.append x y), ?_, ?_⟩
    · refine (mem_mixed_integer_points_iff).2 ⟨hP, ?_⟩
      rw [mem_mixed_integer_lattice_iff]
      exact (mem_integerVectors_iff (n := q) (x := fun j ↦ (z j : ℝ))).2 ⟨z, rfl⟩
    · funext i
      simp

private def realBlockMatrix
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin p) ℚ) :
    Matrix (Fin m) (Fin (n + p)) ℚ :=
  fun i ↦ Fin.addCases (A i) (B i)

private theorem realBlockMatrix_mulVec_append
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin p) ℚ)
    (x : Fin n → ℝ)
    (y : Fin p → ℝ) :
    (realBlockMatrix A B).map (Rat.castHom ℝ) *ᵥ Fin.append x y =
      (A.map (Rat.castHom ℝ)) *ᵥ x + (B.map (Rat.castHom ℝ)) *ᵥ y := by
  ext i
  simp [realBlockMatrix, Matrix.mulVec, dotProduct, Fin.append, Fin.sum_univ_add]

/-- The projection onto the `x`-coordinates of the mixed-integer linear system
`A x + B y + C z ≤ d`, expressed as the canonical projection of the mixed-integer points of its
lifted rational mixed polyhedron. -/
def mixed_integer_linear_projection
    {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin p) ℚ)
    (C : Matrix (Fin m) (Fin q) ℚ)
    (d : Fin m → ℚ) : Set (Fin n → ℝ) :=
  mixed_integer_x_projection (rational_mixed_polyhedron C (realBlockMatrix A B) d)

/-- Membership in `mixed_integer_linear_projection A B C d` is equivalent to the existence of
auxiliary real variables `y` and auxiliary integer variables `z` satisfying
`A x + B y + C z ≤ d`. -/
theorem mem_mixed_integer_linear_projection_iff
    {m n p q : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {B : Matrix (Fin m) (Fin p) ℚ}
    {C : Matrix (Fin m) (Fin q) ℚ}
    {d : Fin m → ℚ}
    {x : Fin n → ℝ} :
    x ∈ mixed_integer_linear_projection A B C d ↔
      ∃ y : Fin p → ℝ, ∃ z : Fin q → ℤ,
        ((A.map (Rat.castHom ℝ)) *ᵥ x +
            (B.map (Rat.castHom ℝ)) *ᵥ y +
            (C.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (z j : ℝ))) ≤
          fun i ↦ (d i : ℝ) := by
  rw [mixed_integer_linear_projection, mem_mixed_integer_x_projection_iff]
  constructor
  · rintro ⟨y, z, hxyz⟩
    rw [mem_rational_mixed_polyhedron_iff] at hxyz
    refine ⟨y, z, ?_⟩
    rw [realBlockMatrix_mulVec_append A B x y] at hxyz
    simpa [add_assoc, add_left_comm, add_comm] using hxyz
  · rintro ⟨y, z, hxyz⟩
    refine ⟨y, z, ?_⟩
    rw [mem_rational_mixed_polyhedron_iff]
    rw [realBlockMatrix_mulVec_append A B x y]
    simpa [add_assoc, add_left_comm, add_comm] using hxyz

/-- Definition 4.9.3-extra-1. A set `S ⊆ ℝ^n` is mixed integer linear representable when it is
the `x`-projection of the mixed-integer points of some rational mixed polyhedron
`P ⊆ ℤ^q × ℝ^(n+p)`. -/
def is_mixed_integer_linear_representable
    {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ p q : ℕ,
    ∃ P : Set (MixedRealPoint q (n + p)),
      is_rational_mixed_polyhedron P ∧ S = mixed_integer_x_projection P

/-- A set is mixed integer linear representable exactly when it is the `x`-projection of the
mixed-integer points of a rational mixed polyhedron in a larger mixed space. -/
theorem is_mixed_integer_linear_representable_iff
    {n : ℕ} {S : Set (Fin n → ℝ)} :
    is_mixed_integer_linear_representable S ↔
      ∃ p q : ℕ,
        ∃ P : Set (MixedRealPoint q (n + p)),
          is_rational_mixed_polyhedron P ∧ S = mixed_integer_x_projection P := Iff.rfl
