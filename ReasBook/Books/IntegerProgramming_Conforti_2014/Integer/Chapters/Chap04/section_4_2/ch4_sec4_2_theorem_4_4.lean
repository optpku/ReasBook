/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

section Theorem44

variable {m n : ℕ}

/-- Helper for Theorem 4.4: the stacked constraint matrix encoding `A x ≤ b` together with the
nonnegativity constraints `x ≥ 0`. -/
private def nonnegative_constraint_matrix
    (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n)) (Fin n) ℤ :=
  (Matrix.fromRows A (-(1 : Matrix (Fin n) (Fin n) ℤ))).reindex finSumFinEquiv (Equiv.refl _)

/-- Helper for Theorem 4.4: the stacked right-hand side encoding the inequalities `A x ≤ b` and
`-x ≤ 0`. -/
private def nonnegative_constraint_rhs
    (b : Fin m → ℤ) :
    Fin (m + n) → ℤ :=
  Sum.elim b (fun _ ↦ 0) ∘ finSumFinEquiv.symm

/-- The polyhedron `{x | A x ≤ b, x ≥ 0}` attached to an integral matrix `A` and an integral
right-hand side `b`, viewed inside `ℝ^n`. -/
def nonnegative_matrix_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Set (Fin n → ℝ) :=
  {x | (A.map (Int.castRingHom ℝ)) *ᵥ x ≤ (fun i ↦ (b i : ℝ)) ∧ 0 ≤ x}

/-- Membership in `nonnegative_matrix_polyhedron` is equivalent to satisfying the defining linear
inequalities and nonnegativity constraints. -/
theorem mem_nonnegative_matrix_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ} {x : Fin n → ℝ} :
    x ∈ nonnegative_matrix_polyhedron A b ↔
      (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) ∧ ∀ j, 0 ≤ x j := by
  constructor
  · rintro ⟨hAx, hx0⟩
    refine ⟨?_, by simpa using hx0⟩
    intro i
    simpa [Matrix.mulVec, dotProduct] using hAx i
  · rintro ⟨hAx, hx0⟩
    refine ⟨?_, by simpa using hx0⟩
    intro i
    simpa [Matrix.mulVec, dotProduct] using hAx i

/-- Helper for Theorem 4.4: the nonnegative system is the standard stacked polyhedron
`[A ; -I] x ≤ (b, 0)`. -/
lemma nonnegative_matrix_polyhedron_eq_polyhedron_le_set
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    nonnegative_matrix_polyhedron A b =
      polyhedron_le_set
        ((nonnegative_constraint_matrix A).map (Int.castRingHom ℝ))
        (fun i ↦ (nonnegative_constraint_rhs b i : ℝ)) := by
  ext x
  constructor
  · rintro ⟨hAx, hx0⟩
    rw [mem_polyhedron_le_set_iff]
    intro i
    -- Split the stacked row into an original inequality row or a nonnegativity row.
    cases h : finSumFinEquiv.symm i with
    | inl r =>
        simpa [nonnegative_constraint_matrix, nonnegative_constraint_rhs, h, Matrix.mulVec,
          dotProduct] using hAx r
    | inr s =>
        have hs : 0 ≤ ∑ j, (((1 : Matrix (Fin n) (Fin n) ℤ) s j : ℝ) * x j) := by
          simpa [Matrix.one_apply, dotProduct] using hx0 s
        simpa [nonnegative_constraint_matrix, nonnegative_constraint_rhs, h, Matrix.mulVec,
          dotProduct] using hs
  · rw [mem_polyhedron_le_set_iff]
    intro hx
    refine ⟨?_, ?_⟩
    · intro r
      let i : Fin (m + n) := finSumFinEquiv (Sum.inl r)
      have hi := hx i
      simpa [nonnegative_constraint_matrix, nonnegative_constraint_rhs, i, Matrix.mulVec,
        dotProduct] using hi
    · intro s
      let i : Fin (m + n) := finSumFinEquiv (Sum.inr s)
      have hi := hx i
      have hi' : 0 ≤ ∑ j, (((1 : Matrix (Fin n) (Fin n) ℤ) s j : ℝ) * x j) := by
        simpa [nonnegative_constraint_matrix, nonnegative_constraint_rhs, i, Matrix.mulVec,
          dotProduct] using hi
      simpa [Matrix.one_apply, dotProduct] using hi'

/-- Helper for Theorem 4.4: the nonnegative system is a polyhedron because it is already a finite
stacked linear-inequality system. -/
lemma nonnegative_matrix_polyhedron_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    is_polyhedron (nonnegative_matrix_polyhedron A b) := by
  -- Reuse the stacked-system presentation as the canonical polyhedral description.
  refine ⟨m + n, (nonnegative_constraint_matrix A).map (Int.castRingHom ℝ),
    (fun i ↦ (nonnegative_constraint_rhs b i : ℝ)), ?_⟩
  exact nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b

/-- Helper for Theorem 4.4: the nonnegative system is a rational polyhedron because both the
constraint matrix and the right-hand side are integral. -/
lemma nonnegative_matrix_polyhedron_is_rational
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    is_rational_polyhedron (nonnegative_matrix_polyhedron A b) := by
  refine ⟨m + n,
    (nonnegative_constraint_matrix A).map (Int.castRingHom ℚ),
    (fun i ↦ (nonnegative_constraint_rhs b i : ℚ)), ?_⟩
  -- Reuse the stacked-system description and simplify the casted data.
  change nonnegative_matrix_polyhedron A b =
    polyhedron_le_set
      (((nonnegative_constraint_matrix A).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ))
      (fun i ↦ ((fun j ↦ (nonnegative_constraint_rhs b j : ℚ)) i : ℝ))
  simpa using nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b

/-- Helper for Theorem 4.4: every equality face `face_set (nonnegative_matrix_polyhedron A b) c δ`
is again a polyhedron after adjoining the two rows `c` and `-c`. -/
lemma face_set_nonnegative_matrix_polyhedron_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (c : Fin n → ℝ)
    (δ : ℝ) :
    is_polyhedron (face_set (nonnegative_matrix_polyhedron A b) c δ) := by
  let M : Matrix (Fin (m + n)) (Fin n) ℝ :=
    (nonnegative_constraint_matrix A).map (Int.castRingHom ℝ)
  let rhs : Fin (m + n) → ℝ := fun i ↦ (nonnegative_constraint_rhs b i : ℝ)
  let B : Matrix (Fin ((m + n) + 2)) (Fin n) ℝ :=
    fun i j ↦ Fin.cases (c j) (fun i' ↦ Fin.cases (-c j) (fun i'' ↦ M i'' j) i') i
  let d : Fin ((m + n) + 2) → ℝ :=
    fun i ↦ Fin.cases δ (fun i' ↦ Fin.cases (-δ) rhs i') i
  refine ⟨(m + n) + 2, B, d, ?_⟩
  ext x
  rw [mem_face_set_iff, nonnegative_matrix_polyhedron_eq_polyhedron_le_set]
  constructor
  · rintro ⟨hxP, hxEq⟩
    have hxEq_sum : ∑ j : Fin n, c j * x j = δ := by
      simpa [dotProduct] using hxEq
    -- Add the two objective rows `c` and `-c` to the stacked system.
    change B *ᵥ x ≤ d
    intro i
    cases i using Fin.cases with
    | zero =>
        simpa [B, d, Matrix.mulVec, dotProduct] using hxEq_sum.le
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            have hneg_sum : ∑ j : Fin n, (-c j) * x j ≤ -δ := by
              have hneg_eq : ∑ j : Fin n, (-c j) * x j = -δ := by
                calc
                  ∑ j : Fin n, (-c j) * x j = ∑ j : Fin n, -(c j * x j) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                  _ = -(∑ j : Fin n, c j * x j) := by
                      rw [Finset.sum_neg_distrib]
                  _ = -δ := by
                      rw [hxEq_sum]
              exact hneg_eq.le
            convert hneg_sum using 1
        | succ i =>
            simpa [B, d, M, rhs, Matrix.mulVec, dotProduct] using hxP i
  · intro hxB
    refine ⟨?_, ?_⟩
    · -- The tail rows recover the original stacked system.
      intro i
      simpa [B, d, M, rhs, Matrix.mulVec, dotProduct] using hxB i.succ.succ
    · -- The first two rows force the objective to hold with equality.
      have hupper_sum : ∑ j : Fin n, c j * x j ≤ δ := by
        simpa [B, d, Matrix.mulVec, dotProduct] using hxB 0
      have hlower_sum : δ ≤ ∑ j : Fin n, c j * x j := by
        have hneg_sum : ∑ j : Fin n, (-c j) * x j ≤ -δ := by
          convert hxB (Fin.succ 0) using 1
        have hneg_sum' : -(∑ j : Fin n, c j * x j) ≤ -δ := by
          calc
            -(∑ j : Fin n, c j * x j) = ∑ j : Fin n, (-c j) * x j := by
              calc
                -(∑ j : Fin n, c j * x j) = ∑ j : Fin n, -(c j * x j) := by
                    rw [Finset.sum_neg_distrib]
                _ = ∑ j : Fin n, (-c j) * x j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ ≤ -δ := hneg_sum
        linarith
      have hxEq_sum : ∑ j : Fin n, c j * x j = δ := by
        linarith
      simpa [dotProduct] using hxEq_sum

/-- Helper for Theorem 4.4: once the nonnegative polyhedron is nonempty, the nonnegativity
constraints force every lineality direction to vanish. -/
lemma eq_zero_of_mem_linealitySpace_nonnegative_matrix_polyhedron
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}
    {r x : Fin n → ℝ}
    (hr : r ∈ linealitySpace (nonnegative_matrix_polyhedron A b))
    (hx : x ∈ nonnegative_matrix_polyhedron A b) :
    r = 0 := by
  -- Evaluate the lineality condition at a scalar that forces one coordinate to `-1`.
  rw [mem_linealitySpace_iff] at hr
  ext j
  by_cases hrj : r j = 0
  · simp [hrj]
  · let a : ℝ := (-x j - 1) / r j
    have hxa : x + a • r ∈ nonnegative_matrix_polyhedron A b := hr hx a
    have hnonneg : 0 ≤ (x + a • r) j := (mem_nonnegative_matrix_polyhedron_iff.mp hxa).2 j
    have hcoord : (x + a • r) j = -1 := by
      dsimp [a]
      field_simp [hrj]
      ring
    rw [hcoord] at hnonneg
    linarith

/-- Helper for Theorem 4.4: an extreme point of an integral set must itself be an integer vector,
because extreme points of a convex hull already lie in the generating set. -/
lemma mem_integerVectors_of_mem_extremePoints_of_is_integral
    {P : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hP : is_integral P)
    (hx : x ∈ P.extremePoints ℝ) :
    x ∈ integerVectors n := by
  rw [is_integral_iff] at hP
  have hx' : x ∈ (convexHull ℝ (P ∩ integerVectors n)).extremePoints ℝ := by
    rw [hP] at hx
    exact hx
  exact (extremePoints_convexHull_subset hx').2

/-- Helper for Theorem 4.4: total unimodularity of `A` implies total unimodularity of the stacked
matrix `[A ; -I]`. -/
lemma nonnegative_constraint_matrix_isTotallyUnimodular
    {A : Matrix (Fin m) (Fin n) ℤ}
    (hA : A.IsTotallyUnimodular) :
    (nonnegative_constraint_matrix A).IsTotallyUnimodular := by
  have hRows :
      (Matrix.fromRows A (-(1 : Matrix (Fin n) (Fin n) ℤ))).IsTotallyUnimodular := by
    refine hA.fromRows_unitlike ?_
    intro _ i
    refine ⟨i, SignType.neg, ?_⟩
    ext j
    by_cases h : j = i
    · subst h
      simp
    · have h' : ¬ i = j := by
        simpa [eq_comm] using h
      simp [h, h']
  simpa [nonnegative_constraint_matrix] using
    (Matrix.reindex_isTotallyUnimodular
      (Matrix.fromRows A (-(1 : Matrix (Fin n) (Fin n) ℤ)))
      finSumFinEquiv (Equiv.refl (Fin n))).2 hRows

/-- Helper for Theorem 4.4: `cramer` commutes with the integer-to-real coercion. -/
lemma cramer_int_cast
    {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℤ)
    (v : Fin k → ℤ) :
    (fun i ↦ ((M.cramer v) i : ℝ)) =
      (M.map (Int.castRingHom ℝ)).cramer (fun i ↦ (v i : ℝ)) := by
  ext i
  -- Expand both sides through Cramer's determinant formula.
  rw [Matrix.cramer_apply, Matrix.cramer_apply]
  calc
    (((M.updateCol i v).det : ℤ) : ℝ) =
        (((M.updateCol i v).map (Int.castRingHom ℝ)).det : ℝ) := by
          simpa using (RingHom.map_det (Int.castRingHom ℝ) (M.updateCol i v))
    _ = (((M.map (Int.castRingHom ℝ)).updateCol i ((Int.castRingHom ℝ) ∘ v)).det : ℝ) := by
          rw [Matrix.map_updateCol]
    _ = (((M.map (Int.castRingHom ℝ)).updateCol i (fun j ↦ (v j : ℝ))).det : ℝ) := by
          rfl

/-- Helper for Theorem 4.4: if the rows of a square matrix span the ambient space, then the
homogeneous system `M x = 0` has only the zero solution. -/
private lemma eq_zero_of_mulVec_eq_zero_of_row_span_eq_top
    {k : ℕ}
    {M : Matrix (Fin k) (Fin k) ℝ}
    {x : Fin k → ℝ}
    (hspan : Submodule.span ℝ (Set.range fun i : Fin k ↦ M i) = ⊤)
    (hx : M *ᵥ x = 0) :
    x = 0 := by
  ext j
  have hdot_zero :
      ∀ w ∈ Submodule.span ℝ (Set.range fun i : Fin k ↦ M i), w ⬝ᵥ x = 0 := by
    intro w hw
    -- Every generator row vanishes on `x`, and the property is stable under linear combinations.
    induction hw using Submodule.span_induction with
    | mem w hw =>
        rcases hw with ⟨i, rfl⟩
        simpa [Matrix.mulVec, dotProduct] using congrFun hx i
    | zero =>
        simp [dotProduct]
    | add u v hu hv ihu ihv =>
        calc
          (u + v) ⬝ᵥ x = u ⬝ᵥ x + v ⬝ᵥ x := by
              simp [dotProduct, add_mul, Finset.sum_add_distrib]
          _ = 0 := by simp [ihu, ihv]
    | smul a u hu ihu =>
        calc
          (a • u) ⬝ᵥ x = a * (u ⬝ᵥ x) := by
              simp [dotProduct, mul_assoc, Finset.mul_sum]
          _ = 0 := by simp [ihu]
  have hej_mem :
      (Pi.single j (1 : ℝ) : Fin k → ℝ) ∈ Submodule.span ℝ (Set.range fun i : Fin k ↦ M i) := by
    rw [hspan]
    simp
  have hej_zero := hdot_zero (Pi.single j (1 : ℝ)) hej_mem
  simpa [dotProduct, Pi.single_apply] using hej_zero

/-- Helper for Theorem 4.4: a square system whose rows span the ambient space has at most one
solution. -/
private lemma eq_of_mulVec_eq_of_row_span_eq_top
    {k : ℕ}
    {M : Matrix (Fin k) (Fin k) ℝ}
    {x y : Fin k → ℝ}
    (hspan : Submodule.span ℝ (Set.range fun i : Fin k ↦ M i) = ⊤)
    (hx : M *ᵥ x = M *ᵥ y) :
    x = y := by
  -- Compare the two solutions through the homogeneous equation satisfied by their difference.
  have hsub : M *ᵥ (x - y) = 0 := by
    ext i
    simp [Matrix.mulVec_sub, congrFun hx i]
  have hzero : x - y = 0 :=
    eq_zero_of_mulVec_eq_zero_of_row_span_eq_top hspan hsub
  exact sub_eq_zero.mp hzero

/-- Helper for Theorem 4.4: every nonempty exposed face of a polyhedron has the same lineality
space as the ambient polyhedron. -/
private lemma linealitySpace_eq_of_nonempty_exposedFace_polyhedron
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {F : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty) :
    linealitySpace F = linealitySpace (polyhedron_le_set A b) := by
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF hF_nonempty
  obtain ⟨x₀, hx₀F⟩ := hF_nonempty
  have hx₀_active : x₀ ∈ active_constraint_face A b I := by
    simpa [hI] using hx₀F
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
    exact ⟨x₀, mem_polyhedron_of_mem_active_constraint_face hx₀_active⟩
  have hkernelP := polyhedron_linealitySpace_eq_kernel_set A b hP_nonempty
  rw [hI, hkernelP]
  ext r
  constructor
  · intro hr
    rw [mem_linealitySpace_iff] at hr
    ext i
    by_cases hi : i ∈ I
    · have hx₀_eq : (A *ᵥ x₀) i = b i := (mem_active_constraint_face_iff.mp hx₀_active).1 i hi
      have htranslate_eq :
          (A *ᵥ (x₀ + (1 : ℝ) • r)) i = b i := by
        exact (mem_active_constraint_face_iff.mp (hr hx₀_active 1)).1 i hi
      calc
        (A *ᵥ r) i = (A *ᵥ (x₀ + (1 : ℝ) • r)) i - (A *ᵥ x₀) i := by
            simp [Matrix.mulVec_add]
        _ = b i - b i := by rw [htranslate_eq, hx₀_eq]
        _ = 0 := by simp
    · have htranslate :
          ∀ a : ℝ, (A *ᵥ (x₀ + a • r)) i ≤ b i := by
        intro a
        exact (mem_active_constraint_face_iff.mp (hr hx₀_active a)).2 i hi
      by_contra hri
      let a : ℝ := (b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i
      have htranslate' : (A *ᵥ x₀) i + a * (A *ᵥ r) i ≤ b i := by
        simpa [Matrix.mulVec_add, Matrix.mulVec_smul, a] using htranslate a
      have ha_mul : a * (A *ᵥ r) i = b i - (A *ᵥ x₀) i + 1 := by
        dsimp [a]
        exact div_mul_cancel₀ _ hri
      linarith
  · intro hr
    rw [mem_linealitySpace_iff]
    have hr_zero : A *ᵥ r = 0 := by
      simpa [hkernelP] using hr
    intro x hxF a
    refine (mem_active_constraint_face_iff).2 ?_
    rcases mem_active_constraint_face_iff.mp hxF with ⟨hxEq, hxLe⟩
    constructor
    · intro i hi
      have hri : (A *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxEq i hi
    · intro i hi
      have hri : (A *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxLe i hi

/-- Helper for Theorem 4.4: an extreme point of `polyhedron_le_set A b` admits `n` active rows
whose coefficient vectors are linearly independent. -/
private lemma exists_active_linearlyIndependent_rows_of_extremePoint
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_vertex : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    ∃ I : Fin n ↪ Fin m,
      (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  classical
  let activeRows : Set (Fin n → ℝ) :=
    Set.range fun i : {i // (A *ᵥ xbar) i = b i} ↦ A i.1
  have hspan : Submodule.span ℝ activeRows = ⊤ := by
    by_contra hspan_ne
    let K : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ activeRows
    have hKlt : K < ⊤ := lt_of_le_of_ne le_top hspan_ne
    obtain ⟨φ, hφ_ne, hKker⟩ := Submodule.exists_le_ker_of_lt_top K hKlt
    let r : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
    have hr_ne : r ≠ 0 := by
      intro hr
      apply hφ_ne
      simpa [r, hr] using ((dotProductEquiv ℝ (Fin n)).apply_symm_apply φ).symm
    have hactive_eval : ∀ i : Fin m, (A *ᵥ xbar) i = b i → (A *ᵥ r) i = 0 := by
      intro i hi
      have hAi_mem : A i ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨i, hi⟩, rfl⟩
      have hφAi : φ (A i) = 0 := by
        simpa using hKker hAi_mem
      have hφr : (dotProductEquiv ℝ (Fin n)) r = φ := by
        simp [r]
      have hdot : dotProduct r (A i) = 0 := by
        simpa [hφAi] using congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f (A i)) hφr
      have hrowdot : dotProduct (A i) r = 0 := by
        simpa [dotProduct_comm] using hdot
      simpa [Matrix.mulVec, dotProduct] using hrowdot
    let δ : Fin m → ℝ := fun i ↦
      if hi : (A *ᵥ xbar) i = b i then 1
      else if hzero : (A *ᵥ r) i = 0 then 1
      else (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|
    have hδ_pos : ∀ i : Fin m, 0 < δ i := by
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · simp [δ, hi]
      · by_cases hzero : (A *ᵥ r) i = 0
        · simp [δ, hi, hzero]
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hnum : 0 < b i - (A *ᵥ xbar) i := sub_pos.mpr hlt
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          simp [δ, hi, hzero, div_pos hnum hden]
    let δs : Finset ℝ := insert 1 (Finset.univ.image δ)
    let ε : ℝ := δs.min' (by simp [δs]) / 2
    have hmin_pos : 0 < δs.min' (by simp [δs]) := by
      have hmin_mem : δs.min' (by simp [δs]) ∈ δs := Finset.min'_mem _ _
      rcases Finset.mem_insert.mp hmin_mem with h1 | himage
      · simp [h1]
      · rcases Finset.mem_image.mp himage with ⟨i, _, hi⟩
        rw [← hi]
        exact hδ_pos i
    have hε_pos : 0 < ε := half_pos hmin_pos
    have hε_le : ∀ i : Fin m, ε ≤ δ i := by
      intro i
      have hmin_le : δs.min' (by simp [δs]) ≤ δ i := by
        apply Finset.min'_le
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      have hhalf_le : δs.min' (by simp [δs]) / 2 ≤ δs.min' (by simp [δs]) := by
        linarith
      exact hhalf_le.trans hmin_le
    have hperturb_eval (σ : ℝ) (i : Fin m) :
        (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp
    have hperturb_mem : ∀ {σ : ℝ}, |σ| ≤ ε → xbar + σ • r ∈ polyhedron_le_set A b := by
      intro σ hσ
      rw [mem_polyhedron_le_set_iff]
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · calc
          (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
          _ = b i := by simp [hi, hactive_eval i hi]
          _ ≤ b i := le_rfl
      · by_cases hzero : (A *ᵥ r) i = 0
        · calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ = (A *ᵥ xbar) i := by simp [hzero]
            _ ≤ b i := hxbar i
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hσ_bound : |σ| ≤ (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by
            calc
              |σ| ≤ ε := hσ
              _ ≤ δ i := hε_le i
              _ = (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by simp [δ, hi, hzero]
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          have hmul_le :
              |σ| * |(A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            have hmul := mul_le_mul_of_nonneg_right hσ_bound hden.le
            have hcancel :
                ((b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|) * |(A *ᵥ r) i| =
                  b i - (A *ᵥ xbar) i := by
              field_simp [hden.ne']
            simpa [hcancel] using hmul
          have habs_le : |σ * (A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            simpa [abs_mul] using hmul_le
          have hterm_le : σ * (A *ᵥ r) i ≤ b i - (A *ᵥ xbar) i := by
            exact (le_abs_self _).trans habs_le
          calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ ≤ b i := by linarith
    let xMinus : Fin n → ℝ := xbar - ε • r
    let xPlus : Fin n → ℝ := xbar + ε • r
    have hxMinus : xMinus ∈ polyhedron_le_set A b := by
      have hneg : |(-ε : ℝ)| ≤ ε := by simp [abs_of_nonneg hε_pos.le]
      simpa [xMinus, sub_eq_add_neg] using (hperturb_mem (σ := -ε) hneg)
    have hxPlus : xPlus ∈ polyhedron_le_set A b := by
      have hpos : |(ε : ℝ)| ≤ ε := by simp [abs_of_nonneg hε_pos.le]
      simpa [xPlus] using (hperturb_mem (σ := ε) hpos)
    have hxMinus_ne : xMinus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := sub_eq_self.mp hEq
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxPlus_ne : xPlus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := by
        have := congrArg (fun u : Fin n → ℝ ↦ u - xbar) hEq
        simpa [xPlus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxbar_segment : xbar ∈ segment ℝ xMinus xPlus := by
      simpa [xMinus, xPlus] using (mem_segment_sub_add (𝕜 := ℝ) xbar (ε • r))
    have hxbar_open : xbar ∈ openSegment ℝ xMinus xPlus := by
      exact mem_openSegment_of_ne_left_right hxMinus_ne hxPlus_ne hxbar_segment
    have hxext := (mem_extremePoints_iff_left).mp hxbar_vertex
    exact hxMinus_ne (hxext.2 xMinus hxMinus xPlus hxPlus hxbar_open)
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ activeRows) = n := by
    rw [hspan, finrank_top]
    exact Module.finrank_fin_fun ℝ (n := n)
  obtain ⟨g, hg_mem, _hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ activeRows
  let e : Fin (Module.finrank ℝ ↥(Submodule.span ℝ activeRows)) ≃ Fin n :=
    (Fin.castOrderIso hdim).toEquiv
  let rows : Fin n → Fin n → ℝ := fun i ↦ g (e.symm i)
  have hrows_mem : ∀ i : Fin n, rows i ∈ activeRows := by
    intro i
    exact hg_mem (e.symm i)
  have hrows_linear : LinearIndependent ℝ rows := by
    exact (linearIndependent_equiv e.symm).2 hg_linear
  have hrows_mem' :
      ∀ i : Fin n, ∃ j : {j // (A *ᵥ xbar) j = b j}, A j.1 = rows i := by
    intro i
    simpa [activeRows] using hrows_mem i
  let chosen : Fin n → {j // (A *ᵥ xbar) j = b j} :=
    fun i ↦ Classical.choose (hrows_mem' i)
  have hchosen_row : ∀ i : Fin n, A (chosen i).1 = rows i := by
    intro i
    exact Classical.choose_spec (hrows_mem' i)
  have hchosen_injective : Function.Injective fun i : Fin n ↦ (chosen i).1 := by
    intro i j hij
    apply hrows_linear.injective
    calc
      rows i = A (chosen i).1 := (hchosen_row i).symm
      _ = A (chosen j).1 := by simp [hij]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    exact (chosen i).2
  · have hrows : (fun i : Fin n ↦ A (I i)) = rows := by
      funext i
      exact hchosen_row i
    simpa [hrows] using hrows_linear

/-- Helper for Theorem 4.4: every extreme point of `{x | A x ≤ b, x ≥ 0}` is integral when `A` is
totally unimodular. -/
lemma extreme_point_mem_integerVectors_of_isTotallyUnimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    {x : Fin n → ℝ}
    (hA : A.IsTotallyUnimodular)
    (hx : x ∈ (nonnegative_matrix_polyhedron A b).extremePoints ℝ) :
    x ∈ integerVectors n := by
  let MZ : Matrix (Fin (m + n)) (Fin n) ℤ := nonnegative_constraint_matrix A
  let M : Matrix (Fin (m + n)) (Fin n) ℝ := MZ.map (Int.castRingHom ℝ)
  let rhsZ : Fin (m + n) → ℤ := nonnegative_constraint_rhs b
  let rhs : Fin (m + n) → ℝ := fun i ↦ (rhsZ i : ℝ)
  have hx_mem : x ∈ nonnegative_matrix_polyhedron A b := extremePoints_subset hx
  have hx_polyhedron : x ∈ polyhedron_le_set M rhs := by
    simpa [M, rhs, MZ, rhsZ, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hx_mem
  have hx_polyhedron_extreme : x ∈ (polyhedron_le_set M rhs).extremePoints ℝ := by
    -- Route correction: the Chapter 3.34 owner import works here, so reduce once to the stacked
    -- matrix presentation and reuse the existing vertex criterion directly.
    simpa [M, rhs, MZ, rhsZ, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hx
  obtain ⟨I, hactive, hlinear⟩ :=
    exists_active_linearlyIndependent_rows_of_extremePoint M rhs
      hx_polyhedron hx_polyhedron_extreme
  let BZ : Matrix (Fin n) (Fin n) ℤ := MZ.submatrix I id
  let rhsI : Fin n → ℤ := fun i ↦ rhsZ (I i)
  have hsystem : (BZ.map (Int.castRingHom ℝ)) *ᵥ x = fun i ↦ (rhsI i : ℝ) := by
    -- Restrict the stacked active equalities to the selected independent rows.
    ext i
    simpa [BZ, rhsI, M, rhs, MZ, rhsZ, Matrix.mulVec, dotProduct] using hactive i
  have hlinear_B :
      LinearIndependent ℝ (fun i : Fin n ↦ (BZ.map (Int.castRingHom ℝ)) i) := by
    simpa [BZ, M, MZ] using hlinear
  have hspan_B :
      Submodule.span ℝ
          (Set.range fun i : Fin n ↦ (BZ.map (Int.castRingHom ℝ)) i) = ⊤ := by
    -- `n` independent rows in `ℝ^n` already form a basis of the ambient row space.
    simpa using
      hlinear_B.span_eq_top_of_card_eq_finrank'
        (by simp)
  have hTU_B : BZ.IsTotallyUnimodular := by
    exact (nonnegative_constraint_matrix_isTotallyUnimodular hA).submatrix I id
  have hdet_sign : BZ.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
    rw [Matrix.isTotallyUnimodular_iff] at hTU_B
    simpa using hTU_B n id id
  have hdet_ne_zero_real : (BZ.map (Int.castRingHom ℝ)).det ≠ 0 := by
    intro hdet_zero
    obtain ⟨r, hr_ne, hr_zero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff).mpr hdet_zero
    exact hr_ne (eq_zero_of_mulVec_eq_zero_of_row_span_eq_top hspan_B hr_zero)
  have hdet_ne_zero_int : BZ.det ≠ 0 := by
    intro hdet_zero
    apply hdet_ne_zero_real
    rw [show (BZ.map (Int.castRingHom ℝ)).det = (BZ.det : ℝ) by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) BZ).symm]
    exact_mod_cast hdet_zero
  rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hdet_sign
  rcases hdet_sign with hdet_zero | hdet_neg_one | hdet_one
  · exact (hdet_ne_zero_int hdet_zero).elim
  · refine (mem_integerVectors_iff (n := n) (x := x)).2 ?_
    refine ⟨-BZ.cramer rhsI, ?_⟩
    -- When the determinant is `-1`, negating the Cramer vector recovers the unique solution.
    have hdet_neg_one_real :
        (BZ.map (Int.castRingHom ℝ)).det = (-1 : ℝ) := by
      rw [show (BZ.map (Int.castRingHom ℝ)).det = (BZ.det : ℝ) by
        simpa using (RingHom.map_det (Int.castRingHom ℝ) BZ).symm]
      norm_num [hdet_neg_one]
    have hmul_cramer :
        (BZ.map (Int.castRingHom ℝ)) *ᵥ
            (BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) =
          (-1 : ℝ) • (fun i ↦ (rhsI i : ℝ)) := by
      rw [Matrix.mulVec_cramer, hdet_neg_one_real]
    have hneg_solution :
        (BZ.map (Int.castRingHom ℝ)) *ᵥ
            (-(BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ))) =
          fun i ↦ (rhsI i : ℝ) := by
      calc
        (BZ.map (Int.castRingHom ℝ)) *ᵥ
            (-(BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ))) =
            -((BZ.map (Int.castRingHom ℝ)) *ᵥ
              (BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ))) := by
                simpa using Matrix.mulVec_neg
                  ((BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)))
                  (BZ.map (Int.castRingHom ℝ))
        _ = -((-1 : ℝ) • (fun i ↦ (rhsI i : ℝ))) := by rw [hmul_cramer]
        _ = fun i ↦ (rhsI i : ℝ) := by
              ext i
              simp
    have hcramer_eq :
        -(BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) = x := by
      exact eq_of_mulVec_eq_of_row_span_eq_top hspan_B (hneg_solution.trans hsystem.symm)
    calc
      x = -(BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) := hcramer_eq.symm
      _ = fun i ↦ ((-BZ.cramer rhsI) i : ℝ) := by
            funext i
            simp only [Pi.neg_apply]
            simpa using congrFun (cramer_int_cast BZ rhsI).symm i
  · refine (mem_integerVectors_iff (n := n) (x := x)).2 ?_
    refine ⟨BZ.cramer rhsI, ?_⟩
    -- When the selected determinant is `1`, Cramer's rule gives the unique active solution.
    have hdet_one_eq : BZ.det = 1 := by
      simpa using hdet_one
    have hdet_one_real :
        (BZ.map (Int.castRingHom ℝ)).det = (1 : ℝ) := by
      rw [show (BZ.map (Int.castRingHom ℝ)).det = (BZ.det : ℝ) by
        simpa using (RingHom.map_det (Int.castRingHom ℝ) BZ).symm]
      norm_num [hdet_one_eq]
    have hcramer_system :
        (BZ.map (Int.castRingHom ℝ)) *ᵥ
            (BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) =
          fun i ↦ (rhsI i : ℝ) := by
      rw [Matrix.mulVec_cramer, hdet_one_real, one_smul]
    have hcramer_eq :
        (BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) = x := by
      exact eq_of_mulVec_eq_of_row_span_eq_top hspan_B (hcramer_system.trans hsystem.symm)
    calc
      x = (BZ.map (Int.castRingHom ℝ)).cramer (fun i ↦ (rhsI i : ℝ)) := hcramer_eq.symm
      _ = fun i ↦ ((BZ.cramer rhsI) i : ℝ) := by
            symm
            exact cramer_int_cast BZ rhsI

/-- Helper for Theorem 4.4: if `A` is totally unimodular, then every nonnegative polyhedron
`{x | A x ≤ b, x ≥ 0}` is integral. -/
lemma nonnegative_matrix_polyhedron_is_integral_of_isTotallyUnimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (hA : A.IsTotallyUnimodular) :
    is_integral (nonnegative_matrix_polyhedron A b) := by
  -- Route correction: avoid the broken minimal-face import chain and use Theorem 4.1(2) on the
  -- exposed maximizer face instead.
  refine
    (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
      (nonnegative_matrix_polyhedron A b)
      (nonnegative_matrix_polyhedron_is_rational A b)).2 ?_
  intro c z hGreatest
  rcases hGreatest.1 with ⟨x₀, hx₀P, hx₀_obj⟩
  let P : Set (Fin n → ℝ) := nonnegative_matrix_polyhedron A b
  let F : Set (Fin n → ℝ) := face_set P c z
  have hP_polyhedron : is_polyhedron P := nonnegative_matrix_polyhedron_is_polyhedron A b
  have hF_polyhedron : is_polyhedron F := by
    simpa [P, F] using face_set_nonnegative_matrix_polyhedron_is_polyhedron A b c z
  have hvalid : is_valid_inequality P c z := by
    intro y hyP
    exact hGreatest.2 ⟨y, hyP, rfl⟩
  have hx₀F : x₀ ∈ F := by
    rw [mem_face_set_iff]
    exact ⟨hx₀P, hx₀_obj⟩
  have hF_nonempty : F.Nonempty := ⟨x₀, hx₀F⟩
  have hF_exposed : IsExposed ℝ P F := by
    simpa [P, F] using isExposed_face_set_of_valid_inequality hvalid
  have hP_lineality : linealitySpace P = ({0} : Set (Fin n → ℝ)) := by
    ext r
    constructor
    · intro hr
      simp [eq_zero_of_mem_linealitySpace_nonnegative_matrix_polyhedron hr hx₀P]
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      exact zero_mem_linealitySpace
  have hF_lineality : linealitySpace F = ({0} : Set (Fin n → ℝ)) := by
    let M : Matrix (Fin (m + n)) (Fin n) ℝ :=
      (nonnegative_constraint_matrix A).map (Int.castRingHom ℝ)
    let rhs : Fin (m + n) → ℝ := fun i ↦ (nonnegative_constraint_rhs b i : ℝ)
    have hF_exposed' : IsExposed ℝ (polyhedron_le_set M rhs) F := by
      simpa [P, M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hF_exposed
    have hlineality :
        linealitySpace F = linealitySpace (polyhedron_le_set M rhs) :=
      linealitySpace_eq_of_nonempty_exposedFace_polyhedron hF_exposed' hF_nonempty
    have hlineality_polyhedron :
        linealitySpace (polyhedron_le_set M rhs) = ({0} : Set (Fin n → ℝ)) := by
      simpa [P, M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hP_lineality
    exact hlineality.trans hlineality_polyhedron
  have hF_extreme_nonempty :
      (F.extremePoints ℝ).Nonempty := by
    exact
      (polyhedron_extremePoints_nonempty_iff_linealitySpace_eq_zero
        hF_polyhedron hF_nonempty).2 hF_lineality
  rcases hF_extreme_nonempty with ⟨x, hx_extreme_F⟩
  have hx_extreme_P : x ∈ P.extremePoints ℝ := by
    exact hF_exposed.isExtreme.extremePoints_subset_extremePoints hx_extreme_F
  have hx_int : x ∈ integerVectors n :=
    extreme_point_mem_integerVectors_of_isTotallyUnimodular A b hA hx_extreme_P
  have hxF : x ∈ F := extremePoints_subset hx_extreme_F
  rw [mem_face_set_iff] at hxF
  exact ⟨x, ⟨hxF.1, hx_int⟩, hxF.2⟩

/-- Helper for Theorem 4.4: a bad square integral minor has a column in its rational inverse that
is not the cast of an integer vector. -/
lemma exists_fractional_coordinate_of_inverse_of_bad_submatrix
    {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℤ)
    (hdet_ne_zero : C.det ≠ 0)
    (hdet_not_sign : C.det ∉ Set.range (SignType.cast : SignType → ℤ)) :
    ∃ j : Fin k,
      (fun i ↦ ((C.map (Int.castRingHom ℚ))⁻¹ i j)) ∉
        Set.range (fun z : Fin k → ℤ ↦ fun i ↦ (z i : ℚ)) := by
  by_contra hfrac
  push Not at hfrac
  choose z hz using hfrac
  let Z : Matrix (Fin k) (Fin k) ℤ := fun i j ↦ z j i
  have hInv :
      (C.map (Int.castRingHom ℚ))⁻¹ = Z.map (Int.castRingHom ℚ) := by
    -- Columnwise integrality of the inverse rebuilds it as the cast of an integral matrix.
    ext i j
    simpa [Z] using (congrFun (hz j) i).symm
  have hdetQ_unit : IsUnit ((C.map (Int.castRingHom ℚ)).det) := by
    -- Over `ℚ`, a nonzero determinant is automatically a unit.
    rw [show (C.map (Int.castRingHom ℚ)).det = (C.det : ℚ) by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) C).symm]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet_ne_zero)
  have hZdet_cast : (Z.map (Int.castRingHom ℚ)).det = (Z.det : ℚ) := by
    -- Determinants commute with the integer-to-rational cast.
    simpa using (RingHom.map_det (Int.castRingHom ℚ) Z).symm
  have hCdet_cast : (C.map (Int.castRingHom ℚ)).det = (C.det : ℚ) := by
    -- Determinants commute with the integer-to-rational cast.
    simpa using (RingHom.map_det (Int.castRingHom ℚ) C).symm
  have hprodQ :
      ((Z.det : ℚ) * (C.det : ℚ)) = 1 := by
    -- Taking determinants of the rebuilt inverse gives an integral determinant inverse.
    calc
      ((Z.det : ℚ) * (C.det : ℚ)) =
          ((Z.map (Int.castRingHom ℚ)).det * (C.map (Int.castRingHom ℚ)).det) := by
            rw [hZdet_cast, hCdet_cast]
      _ = ((C.map (Int.castRingHom ℚ))⁻¹.det * (C.map (Int.castRingHom ℚ)).det) := by
            rw [hInv]
      _ = 1 := Matrix.det_nonsing_inv_mul_det (C.map (Int.castRingHom ℚ)) hdetQ_unit
  have hprodZ : Z.det * C.det = 1 := by
    -- Integer-cast injectivity transports the determinant identity back to `ℤ`.
    apply Rat.intCast_injective
    simpa using hprodQ
  have hC_det_sign : C.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
    -- An integer with an integral reciprocal must be `1` or `-1`.
    rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprodZ) with
      ⟨_, hCdet⟩ | ⟨_, hCdet⟩
    · exact ⟨1, by simpa using hCdet.symm⟩
    · exact ⟨-1, by simpa using hCdet.symm⟩
  exact hdet_not_sign hC_det_sign

/-- Helper for Theorem 4.4: on vectors supported on the selected columns `range g`, the selected
rows `f` of `A *ᵥ y` are exactly the bad minor `A.submatrix f g` applied to the restricted
coordinates. -/
private lemma selectedRows_mulVec_eq_submatrix_mulVec
    {k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (f : Fin k → Fin m)
    (g : Fin k → Fin n)
    (hg : Function.Injective g)
    {y : Fin n → ℝ}
    (hy : ∀ t : Fin n, t ∉ Set.range g → y t = 0) :
    (fun i : Fin k ↦ ((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) =
      ((A.submatrix f g).map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ y (g s)) := by
  ext i
  let gEmb : Fin k ↪ Fin n := ⟨g, hg⟩
  have hfilter :
      Finset.univ.filter (fun t : Fin n ↦ t ∈ Set.range g) = Finset.univ.map gEmb := by
    ext t
    simp [gEmb, Set.mem_range]
  -- Remove the zero columns outside `range g`, then reindex the remaining sum by `g`.
  calc
    ((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i) = ∑ t : Fin n, (A (f i) t : ℝ) * y t := by
      simp [Matrix.mulVec, dotProduct]
    _ = Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t ∈ Set.range g))
          (fun t : Fin n ↦ (A (f i) t : ℝ) * y t) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro t _ ht
      have htg : t ∉ Set.range g := by
        simpa using ht
      simp [hy t htg]
    _ = Finset.sum (Finset.univ.map gEmb) (fun t : Fin n ↦ (A (f i) t : ℝ) * y t) := by
      rw [hfilter]
    _ = ∑ s : Fin k, (A (f i) (g s) : ℝ) * y (g s) := by
      simp [gEmb]
    _ = (((A.submatrix f g).map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ y (g s))) i := by
      simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 4.4: the `j`th column of the rational inverse solves the `j`th unit
system. -/
private lemma inverseColumn_mulVec_eq_single
    {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℤ)
    (hdet_ne_zero : C.det ≠ 0)
    (j : Fin k) :
    (C.map (Int.castRingHom ℚ)) *ᵥ (fun i ↦ ((C.map (Int.castRingHom ℚ))⁻¹ i j)) =
      Pi.single j 1 := by
  let Cq : Matrix (Fin k) (Fin k) ℚ := C.map (Int.castRingHom ℚ)
  have hdet_unit : IsUnit Cq.det := by
    rw [show Cq.det = (C.det : ℚ) by
      simpa [Cq] using (RingHom.map_det (Int.castRingHom ℚ) C).symm]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet_ne_zero)
  have hmul : Cq * Cq⁻¹ = 1 := Matrix.mul_nonsing_inv Cq hdet_unit
  ext i
  -- Read the matrix identity rowwise as a column equation for the chosen inverse column.
  simpa [Cq, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply] using
    congrFun (congrFun hmul i) j

/-- Helper for Theorem 4.4: a square real system obtained by casting an integral matrix with
nonzero determinant has at most one solution. -/
private lemma eq_of_mulVec_eq_of_det_ne_zero
    {k : ℕ}
    {C : Matrix (Fin k) (Fin k) ℤ}
    {u v : Fin k → ℝ}
    (hdet_ne_zero : C.det ≠ 0)
    (huv : (C.map (Int.castRingHom ℝ)) *ᵥ u = (C.map (Int.castRingHom ℝ)) *ᵥ v) :
    u = v := by
  by_contra huv_ne
  have hsub_ne : u - v ≠ 0 := sub_ne_zero.mpr huv_ne
  have hsub_zero : (C.map (Int.castRingHom ℝ)) *ᵥ (u - v) = 0 := by
    ext i
    simpa [Matrix.mulVec_sub] using sub_eq_zero.mpr (congrFun huv i)
  have hdet_real :
      (C.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [show (C.map (Int.castRingHom ℝ)).det = (C.det : ℝ) by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) C).symm]
    exact_mod_cast hdet_ne_zero
  exact hdet_real ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨u - v, hsub_ne, hsub_zero⟩)

/-- Helper for Theorem 4.4: a non-totally-unimodular matrix yields an integral right-hand side
whose nonnegative polyhedron has a fractional extreme point. -/
lemma exists_fractional_extreme_point_of_not_isTotallyUnimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ¬ A.IsTotallyUnimodular) :
    ∃ b : Fin m → ℤ, ∃ x : Fin n → ℝ,
      x ∈ (nonnegative_matrix_polyhedron A b).extremePoints ℝ ∧
        x ∉ integerVectors n := by
  -- Route correction: rather than rebuilding a converse active-basis theorem, embed the
  -- fractional inverse column directly, then use the open-segment criterion for extreme points.
  rw [Matrix.isTotallyUnimodular_iff] at hA
  push Not at hA
  obtain ⟨k, f, g, hbad⟩ := hA
  let C : Matrix (Fin k) (Fin k) ℤ := A.submatrix f g
  have hC_bad : C.det ∉ Set.range (SignType.cast : SignType → ℤ) := by
    simpa [C] using hbad
  have hC_det_ne_zero : C.det ≠ 0 := by
    intro hzero
    apply hC_bad
    exact ⟨0, by simp [hzero]⟩
  obtain ⟨j, hj⟩ :=
    exists_fractional_coordinate_of_inverse_of_bad_submatrix C hC_det_ne_zero hC_bad
  have hg_injective : Function.Injective g := by
    by_contra hg
    rw [Function.not_injective_iff] at hg
    rcases hg with ⟨i, i', hgi, hii'⟩
    apply hC_det_ne_zero
    apply Matrix.det_zero_of_column_eq hii'
    simp [C, hgi]
  let γQ : Fin k → ℚ := fun i ↦ ((C.map (Int.castRingHom ℚ))⁻¹ i j)
  let γ : Fin k → ℝ := fun i ↦ (γQ i : ℝ)
  let u : Fin k → ℝ := fun i ↦ (⌈γ i⌉ : ℝ) - γ i
  let xbar : Fin n → ℝ := Function.extend g u 0
  let b : Fin m → ℤ := fun r ↦ ⌈(((A.map (Int.castRingHom ℝ)) *ᵥ xbar) r)⌉
  have hxbar_apply_selected : ∀ i : Fin k, xbar (g i) = u i := by
    intro i
    -- On the selected columns, `Function.extend` recovers the defining fractional correction.
    simpa [xbar] using Function.Injective.extend_apply hg_injective u 0 i
  have hxbar_apply_outside : ∀ t : Fin n, t ∉ Set.range g → xbar t = 0 := by
    intro t ht
    -- Outside the selected columns, the witness is forced to vanish.
    simpa [xbar] using Function.extend_apply' (f := g) u 0 t (by
      simpa [Set.mem_range] using ht)
  have hγQ : (C.map (Int.castRingHom ℚ)) *ᵥ γQ = (Pi.single j (1 : ℚ) : Fin k → ℚ) :=
    inverseColumn_mulVec_eq_single C hC_det_ne_zero j
  have hγ : (C.map (Int.castRingHom ℝ)) *ᵥ γ = (Pi.single j (1 : ℝ) : Fin k → ℝ) := by
    -- Cast the rational inverse-column identity to `ℝ`.
    ext i
    have hγi :
        (((C.map (Int.castRingHom ℚ)) *ᵥ γQ) i : ℚ) =
          ((Pi.single j (1 : ℚ) : Fin k → ℚ) i) :=
      congrFun hγQ i
    have hγi_real := congrArg (fun q : ℚ ↦ (q : ℝ)) hγi
    by_cases hij : i = j
    · subst hij
      simpa [γ, γQ, Matrix.mulVec, dotProduct, Pi.single_apply] using hγi_real
    · simpa [γ, γQ, Matrix.mulVec, dotProduct, Pi.single_apply, hij] using hγi_real
  let zceil : Fin k → ℤ := fun i ↦ Int.ceil (γ i)
  have hselected_rows :
      ∀ i : Fin k,
        ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) =
          (((C *ᵥ zceil) i - (Pi.single j (1 : ℤ) : Fin k → ℤ) i : ℤ) : ℝ) := by
    intro i
    have hu :
        u = (fun s : Fin k ↦ (zceil s : ℝ)) - γ := by
      ext s
      simp [u, zceil]
    have hrestrict :=
      congrFun (selectedRows_mulVec_eq_submatrix_mulVec A f g hg_injective hxbar_apply_outside) i
    have hγi : ((C.map (Int.castRingHom ℝ)) *ᵥ γ) i = (Pi.single j (1 : ℝ) : Fin k → ℝ) i := by
      simpa using congrFun hγ i
    -- The chosen rows evaluate to an integral vector `C *ᵥ ⌈γ⌉ - e_j`.
    calc
      ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) =
          (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ xbar (g s))) i) := hrestrict
      _ = (((C.map (Int.castRingHom ℝ)) *ᵥ u) i) := by
            simp [hxbar_apply_selected]
      _ = (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ (zceil s : ℝ))) i) -
            (((C.map (Int.castRingHom ℝ)) *ᵥ γ) i) := by
            rw [hu, Matrix.mulVec_sub]
            rfl
      _ = (((C *ᵥ zceil) i : ℝ) - ((Pi.single j (1 : ℝ) : Fin k → ℝ) i)) := by
            rw [hγi]
            simp [zceil, Matrix.mulVec, dotProduct]
      _ = (((C *ᵥ zceil) i - (Pi.single j (1 : ℤ) : Fin k → ℤ) i : ℤ) : ℝ) := by
            by_cases hij : i = j
            · subst hij
              simp
            · simp [hij]
  have hselected_active :
      ∀ i : Fin k, ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) = (b (f i) : ℝ) := by
    intro i
    -- Those chosen rows are integral, so taking ceilings recovers them exactly.
    calc
      ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) =
          (((C *ᵥ zceil) i - (Pi.single j (1 : ℤ) : Fin k → ℤ) i : ℤ) : ℝ) :=
        hselected_rows i
      _ = (b (f i) : ℝ) := by
            have hb_int :
                b (f i) = (C *ᵥ zceil) i - (Pi.single j (1 : ℤ) : Fin k → ℤ) i := by
              dsimp [b]
              simpa using congrArg Int.ceil (hselected_rows i)
            exact_mod_cast hb_int.symm
  have hxbar_mem : xbar ∈ nonnegative_matrix_polyhedron A b := by
    refine ⟨?_, ?_⟩
    · intro r
      -- Feasibility of `A x̄ ≤ b` is immediate from the defining ceiling.
      dsimp [b]
      exact Int.le_ceil (((A.map (Int.castRingHom ℝ)) *ᵥ xbar) r)
    · intro t
      by_cases ht : t ∈ Set.range g
      · rcases ht with ⟨i, rfl⟩
        -- On selected coordinates, `x̄ = ⌈γ⌉ - γ` is nonnegative.
        rw [hxbar_apply_selected]
        exact sub_nonneg.mpr (Int.le_ceil (γ i))
      · -- Off the selected support, the witness is exactly zero.
        rw [hxbar_apply_outside t ht]
        exact le_rfl
  let M : Matrix (Fin (m + n)) (Fin n) ℝ :=
    (nonnegative_constraint_matrix A).map (Int.castRingHom ℝ)
  let rhs : Fin (m + n) → ℝ := fun i ↦ (nonnegative_constraint_rhs b i : ℝ)
  have hxbar_polyhedron : xbar ∈ polyhedron_le_set M rhs := by
    simpa [M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hxbar_mem
  have hxbar_extreme_polyhedron : xbar ∈ (polyhedron_le_set M rhs).extremePoints ℝ := by
    refine (mem_extremePoints_iff_left).2 ?_
    refine ⟨hxbar_polyhedron, ?_⟩
    intro y hyP z hzP hseg
    rcases (mem_openSegment_iff_div.mp hseg) with ⟨a, c, ha, hc, hcomb⟩
    have hden_pos : 0 < a + c := by linarith
    have ha_div_pos : 0 < a / (a + c) := by exact div_pos ha hden_pos
    have hc_div_pos : 0 < c / (a + c) := by exact div_pos hc hden_pos
    have hy_mem : y ∈ nonnegative_matrix_polyhedron A b := by
      simpa [M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hyP
    have hz_mem : z ∈ nonnegative_matrix_polyhedron A b := by
      simpa [M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using hzP
    have hy_rows : (A.map (Int.castRingHom ℝ)) *ᵥ y ≤ fun r ↦ (b r : ℝ) := hy_mem.1
    have hz_rows : (A.map (Int.castRingHom ℝ)) *ᵥ z ≤ fun r ↦ (b r : ℝ) := hz_mem.1
    have hy_nonneg : 0 ≤ y := hy_mem.2
    have hz_nonneg : 0 ≤ z := hz_mem.2
    have hsupport :
        ∀ t : Fin n, t ∉ Set.range g → y t = 0 ∧ z t = 0 := by
      intro t ht
      have hcoord : (a / (a + c)) * y t + (c / (a + c)) * z t = 0 := by
        have hcoord' := congrFun hcomb t
        rw [hxbar_apply_outside t ht] at hcoord'
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcoord'
      have hy_zero : y t = 0 := by
        have hy_nonpos : y t ≤ 0 := by
          by_contra hy_pos
          have hy_term_pos : 0 < (a / (a + c)) * y t :=
            mul_pos ha_div_pos (lt_of_not_ge hy_pos)
          have hz_term_nonneg : 0 ≤ (c / (a + c)) * z t :=
            mul_nonneg hc_div_pos.le (hz_nonneg t)
          linarith
        exact le_antisymm hy_nonpos (hy_nonneg t)
      have hz_zero : z t = 0 := by
        have hz_nonpos : z t ≤ 0 := by
          by_contra hz_pos
          have hz_term_pos : 0 < (c / (a + c)) * z t :=
            mul_pos hc_div_pos (lt_of_not_ge hz_pos)
          have hy_term_nonneg : 0 ≤ (a / (a + c)) * y t :=
            mul_nonneg ha_div_pos.le (hy_nonneg t)
          linarith
        exact le_antisymm hz_nonpos (hz_nonneg t)
      exact ⟨hy_zero, hz_zero⟩
    have hy_active :
        ∀ i : Fin k, ((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i) = (b (f i) : ℝ) := by
      intro i
      have hrow' := congrArg (fun x : Fin n → ℝ ↦ ((A.map (Int.castRingHom ℝ)) *ᵥ x) (f i)) hcomb
      -- Tightness of the convex combination forces both endpoints to activate the chosen rows.
      have hrow :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) =
            (b (f i) : ℝ) := by
        have hrow_eq :
            (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
                (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) =
              ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) := by
          simpa [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hrow'
        exact hrow_eq.trans (hselected_active i)
      refine le_antisymm (hy_rows (f i)) ?_
      by_contra hlt
      have hlt' : ((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i) < (b (f i) : ℝ) :=
        lt_of_not_ge hlt
      have hy_scaled_lt :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) <
            (a / (a + c)) * (b (f i) : ℝ) :=
        mul_lt_mul_of_pos_left hlt' ha_div_pos
      have hz_scaled_le :
          (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) ≤
            (c / (a + c)) * (b (f i) : ℝ) :=
        mul_le_mul_of_nonneg_left (hz_rows (f i)) hc_div_pos.le
      have hweights : a / (a + c) + c / (a + c) = (1 : ℝ) := by
        field_simp [hden_pos.ne']
      have hstrict :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) <
            (b (f i) : ℝ) := by
        calc
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) <
              (a / (a + c)) * (b (f i) : ℝ) + (c / (a + c)) * (b (f i) : ℝ) :=
            add_lt_add_of_lt_of_le hy_scaled_lt hz_scaled_le
          _ = ((a / (a + c)) + c / (a + c)) * (b (f i) : ℝ) := by ring
          _ = (b (f i) : ℝ) := by rw [hweights, one_mul]
      have hfalse : (b (f i) : ℝ) < (b (f i) : ℝ) := by
        exact hrow.symm ▸ hstrict
      exact (lt_irrefl _ hfalse)
    have hz_active :
        ∀ i : Fin k, ((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i) = (b (f i) : ℝ) := by
      intro i
      have hrow' := congrArg (fun x : Fin n → ℝ ↦ ((A.map (Int.castRingHom ℝ)) *ᵥ x) (f i)) hcomb
      -- The same tightness argument applies symmetrically to the second endpoint.
      have hrow :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) =
            (b (f i) : ℝ) := by
        have hrow_eq :
            (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
                (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) =
              ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) := by
          simpa [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hrow'
        exact hrow_eq.trans (hselected_active i)
      refine le_antisymm (hz_rows (f i)) ?_
      by_contra hlt
      have hlt' : ((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i) < (b (f i) : ℝ) :=
        lt_of_not_ge hlt
      have hy_scaled_le :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) ≤
            (a / (a + c)) * (b (f i) : ℝ) :=
        mul_le_mul_of_nonneg_left (hy_rows (f i)) ha_div_pos.le
      have hz_scaled_lt :
          (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) <
            (c / (a + c)) * (b (f i) : ℝ) :=
        mul_lt_mul_of_pos_left hlt' hc_div_pos
      have hweights : a / (a + c) + c / (a + c) = (1 : ℝ) := by
        field_simp [hden_pos.ne']
      have hstrict :
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) <
            (b (f i) : ℝ) := by
        calc
          (a / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i)) +
              (c / (a + c)) * (((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i)) <
              (a / (a + c)) * (b (f i) : ℝ) + (c / (a + c)) * (b (f i) : ℝ) :=
            add_lt_add_of_le_of_lt hy_scaled_le hz_scaled_lt
          _ = ((a / (a + c)) + c / (a + c)) * (b (f i) : ℝ) := by ring
          _ = (b (f i) : ℝ) := by rw [hweights, one_mul]
      have hfalse : (b (f i) : ℝ) < (b (f i) : ℝ) := by
        exact hrow.symm ▸ hstrict
      exact (lt_irrefl _ hfalse)
    have hy_system :
        ((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ y (g s))) =
          ((C.map (Int.castRingHom ℝ)) *ᵥ u) := by
      ext i
      have hyrestrict :=
        congrFun
          (selectedRows_mulVec_eq_submatrix_mulVec A f g hg_injective
            (fun t ht ↦ (hsupport t ht).1)) i
      have hxrestrict :=
        congrFun (selectedRows_mulVec_eq_submatrix_mulVec A f g hg_injective hxbar_apply_outside) i
      -- Both `y` and `x̄` solve the same selected square subsystem.
      calc
        (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ y (g s))) i) =
            ((A.map (Int.castRingHom ℝ)) *ᵥ y) (f i) := hyrestrict.symm
        _ = (b (f i) : ℝ) := hy_active i
        _ = ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) := (hselected_active i).symm
        _ = (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ xbar (g s))) i) := hxrestrict
        _ = (((C.map (Int.castRingHom ℝ)) *ᵥ u) i) := by
              simp [hxbar_apply_selected]
    have hz_system :
        ((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ z (g s))) =
          ((C.map (Int.castRingHom ℝ)) *ᵥ u) := by
      ext i
      have hzrestrict :=
        congrFun
          (selectedRows_mulVec_eq_submatrix_mulVec A f g hg_injective
            (fun t ht ↦ (hsupport t ht).2)) i
      have hxrestrict :=
        congrFun (selectedRows_mulVec_eq_submatrix_mulVec A f g hg_injective hxbar_apply_outside) i
      -- The same selected subsystem forces `z` onto the same restricted solution.
      calc
        (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ z (g s))) i) =
            ((A.map (Int.castRingHom ℝ)) *ᵥ z) (f i) := hzrestrict.symm
        _ = (b (f i) : ℝ) := hz_active i
        _ = ((A.map (Int.castRingHom ℝ)) *ᵥ xbar) (f i) := (hselected_active i).symm
        _ = (((C.map (Int.castRingHom ℝ)) *ᵥ (fun s : Fin k ↦ xbar (g s))) i) := hxrestrict
        _ = (((C.map (Int.castRingHom ℝ)) *ᵥ u) i) := by
              simp [hxbar_apply_selected]
    have hy_restricted_eq : (fun s : Fin k ↦ y (g s)) = u :=
      eq_of_mulVec_eq_of_det_ne_zero hC_det_ne_zero hy_system
    have hz_restricted_eq : (fun s : Fin k ↦ z (g s)) = u :=
      eq_of_mulVec_eq_of_det_ne_zero hC_det_ne_zero hz_system
    have hy_eq_xbar : y = xbar := by
      ext t
      by_cases ht : t ∈ Set.range g
      · rcases ht with ⟨i, rfl⟩
        simpa [hxbar_apply_selected] using congrFun hy_restricted_eq i
      · rw [(hsupport t ht).1, hxbar_apply_outside t ht]
    have hz_eq_xbar : z = xbar := by
      ext t
      by_cases ht : t ∈ Set.range g
      · rcases ht with ⟨i, rfl⟩
        simpa [hxbar_apply_selected] using congrFun hz_restricted_eq i
      · rw [(hsupport t ht).2, hxbar_apply_outside t ht]
    exact hy_eq_xbar
  have hxbar_extreme : xbar ∈ (nonnegative_matrix_polyhedron A b).extremePoints ℝ := by
    simpa [M, rhs, nonnegative_matrix_polyhedron_eq_polyhedron_le_set A b] using
      hxbar_extreme_polyhedron
  have hxbar_not_integer : xbar ∉ integerVectors n := by
    intro hxint
    rcases (mem_integerVectors_iff (n := n) (x := xbar)).1 hxint with ⟨z, hz⟩
    apply hj
    refine ⟨fun i ↦ Int.ceil (γ i) - z (g i), ?_⟩
    ext i
    have hcoord : xbar (g i) = (z (g i) : ℝ) := congrFun hz (g i)
    -- An integral witness `x̄` would force every inverse-column coordinate to be integral too.
    exact Rat.cast_injective (α := ℝ) <| by
      calc
        ((((fun i ↦ Int.ceil (γ i) - z (g i)) i : ℤ) : ℚ) : ℝ) =
            ((Int.ceil (γ i) - z (g i) : ℤ) : ℝ) := by
              simp
        _ = (⌈γ i⌉ : ℝ) - (z (g i) : ℝ) := by
              simp
        _ = (⌈γ i⌉ : ℝ) - xbar (g i) := by
              rw [← hcoord]
        _ = γ i := by
              rw [hxbar_apply_selected]
              ring
        _ = ((γQ i : ℚ) : ℝ) := rfl
  exact ⟨b, xbar, hxbar_extreme, hxbar_not_integer⟩

/-- Theorem 4.4 (Hoffman and Kruskal). Let `A` be an `m × n` integral matrix. Then the polyhedron
`{x | A x ≤ b, x ≥ 0}` is integral for every integral right-hand side `b` if and only if `A` is
totally unimodular. -/
theorem nonnegative_matrix_polyhedron_integral_iff_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ) :
    (∀ b : Fin m → ℤ, is_integral (nonnegative_matrix_polyhedron A b)) ↔
      A.IsTotallyUnimodular := by
  constructor
  · intro hIntegral
    by_contra hA
    rcases exists_fractional_extreme_point_of_not_isTotallyUnimodular A hA with
      ⟨b, x, hx_extreme, hx_frac⟩
    have hx_int :
        x ∈ integerVectors n :=
      mem_integerVectors_of_mem_extremePoints_of_is_integral (hIntegral b) hx_extreme
    exact hx_frac hx_int
  · intro hA b
    exact nonnegative_matrix_polyhedron_is_integral_of_isTotallyUnimodular A b hA

end Theorem44
