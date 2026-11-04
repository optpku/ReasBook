/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.LinearAlgebra.Matrix.Integer
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Pointwise

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this exercise
-- reuses the chapter owners `rational_matrix_polyhedron`, `is_integral`, and the imported
-- `nonnegative_matrix_polyhedron` / `integer_interval_matrix_polyhedron` APIs together with
-- mathlib's canonical pointwise set-scalar action and `Matrix.IsTotallyUnimodular`.

section Exercise411

variable {m n : ℕ}

/-- Helper for Exercise 4.11: the stacked rational constraint matrix encoding `A x ≤ b` together
with the nonnegativity constraints `x ≥ 0`. -/
private def nonnegative_rational_constraint_matrix
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin (m + n)) (Fin n) ℚ :=
  (Matrix.fromRows A (-(1 : Matrix (Fin n) (Fin n) ℚ))).reindex finSumFinEquiv (Equiv.refl _)

/-- Helper for Exercise 4.11: the stacked rational right-hand side encoding `A x ≤ b` and
`-x ≤ 0`. -/
private def nonnegative_rational_constraint_rhs
    (b : Fin m → ℚ) :
    Fin (m + n) → ℚ :=
  Sum.elim b (fun _ ↦ 0) ∘ finSumFinEquiv.symm

/-- The nonnegative rational polyhedron `{x ∈ ℝ^n_+ | A x ≤ b}` attached to rational data `A`
and `b`. -/
def nonnegative_rational_matrix_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : Set (Fin n → ℝ) :=
  {x | x ∈ rational_matrix_polyhedron A b ∧ 0 ≤ x}

/-- Membership in `nonnegative_rational_matrix_polyhedron A b` is equivalent to satisfying the
defining rational linear inequalities together with the nonnegativity constraints. -/
theorem mem_nonnegative_rational_matrix_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {x : Fin n → ℝ} :
    x ∈ nonnegative_rational_matrix_polyhedron A b ↔
      (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) ∧ ∀ j, 0 ≤ x j := by
  constructor
  · rintro ⟨hAx, hx0⟩
    refine ⟨?_, by simpa using hx0⟩
    intro i
    rw [mem_rational_matrix_polyhedron] at hAx
    simpa [Matrix.mulVec, dotProduct] using hAx i
  · rintro ⟨hAx, hx0⟩
    refine ⟨?_, by simpa using hx0⟩
    rw [mem_rational_matrix_polyhedron]
    intro i
    simpa [Matrix.mulVec, dotProduct] using hAx i

/-- Helper for Exercise 4.11: the rational nonnegative system is the standard stacked polyhedron
`[A ; -I] x ≤ (b, 0)`. -/
lemma nonnegative_rational_polyhedron_eq_augmented_system
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    nonnegative_rational_matrix_polyhedron A b =
      rational_matrix_polyhedron
        (nonnegative_rational_constraint_matrix A)
        (nonnegative_rational_constraint_rhs b) := by
  ext x
  constructor
  · rintro ⟨hAx, hx0⟩
    -- Split the stacked row into an original inequality row or a nonnegativity row.
    rw [mem_rational_matrix_polyhedron] at hAx ⊢
    intro i
    cases h : finSumFinEquiv.symm i with
    | inl r =>
        simpa [nonnegative_rational_constraint_matrix, nonnegative_rational_constraint_rhs, h,
          Matrix.mulVec, dotProduct] using hAx r
    | inr s =>
        have hs : ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ)) s j : ℝ) * x j = x s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro j _ hjs
            apply mul_eq_zero.mpr
            left
            have hsj : ¬ s = j := by
              exact fun hs => hjs hs.symm
            simp [hsj]
          · simp
        simpa [nonnegative_rational_constraint_matrix, nonnegative_rational_constraint_rhs, h,
          Matrix.mulVec, dotProduct, hs] using hx0 s
  · intro hx
    rw [mem_rational_matrix_polyhedron] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_rational_matrix_polyhedron]
      intro r
      let i : Fin (m + n) := finSumFinEquiv (Sum.inl r)
      have hi := hx i
      simpa [nonnegative_rational_constraint_matrix, nonnegative_rational_constraint_rhs, i,
        Matrix.mulVec, dotProduct] using hi
    · intro s
      let i : Fin (m + n) := finSumFinEquiv (Sum.inr s)
      have hi := hx i
      have hs : ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ)) s j : ℝ) * x j = x s := by
        rw [Finset.sum_eq_single s]
        · simp
        · intro j _ hjs
          apply mul_eq_zero.mpr
          left
          have hsj : ¬ s = j := by
            exact fun hs => hjs hs.symm
          simp [hsj]
        · simp
      simpa [nonnegative_rational_constraint_matrix, nonnegative_rational_constraint_rhs, i,
        Matrix.mulVec, dotProduct, hs] using hi

/-- Helper for Exercise 4.11: the rational nonnegative system is a rational polyhedron. -/
lemma nonnegative_rational_matrix_polyhedron_is_rational
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    is_rational_polyhedron (nonnegative_rational_matrix_polyhedron A b) := by
  refine
    ⟨m + n, nonnegative_rational_constraint_matrix A, nonnegative_rational_constraint_rhs b, ?_⟩
  -- The augmented-system presentation is already in the required rational-polyhedron form.
  simpa [rational_matrix_polyhedron] using
    nonnegative_rational_polyhedron_eq_augmented_system A b

/-- Helper for Exercise 4.11: a finite system of real linear inequalities defines a convex set. -/
lemma polyhedron_le_set_convex
    {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (d : Fin p → ℝ) :
    Convex ℝ (polyhedron_le_set M d) := by
  intro x hx y hy a c ha hc hac i
  have hx_i : (M *ᵥ x) i ≤ d i := hx i
  have hy_i : (M *ᵥ y) i ≤ d i := hy i
  calc
    (M *ᵥ (a • x + c • y)) i = a * (M *ᵥ x) i + c * (M *ᵥ y) i := by
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ a * d i + c * d i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
    _ = d i := by
      rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 4.11: the rational nonnegative polyhedron is convex because it is an
augmented linear-inequality system. -/
lemma nonnegative_rational_matrix_polyhedron_convex
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    Convex ℝ (nonnegative_rational_matrix_polyhedron A b) := by
  -- Rewrite to the augmented polyhedron and reuse the standard matrix-inequality convexity lemma.
  simpa [nonnegative_rational_polyhedron_eq_augmented_system, rational_matrix_polyhedron] using
    polyhedron_le_set_convex
      ((nonnegative_rational_constraint_matrix A).map (Rat.castHom ℝ))
      (fun i ↦ (nonnegative_rational_constraint_rhs b i : ℝ))

/-- Helper for Exercise 4.11: every rational vector becomes integral after multiplying by a
positive common denominator. -/
lemma exists_pos_nat_and_integer_multiple_of_rational_vector
    (v : Fin n → ℚ) :
    ∃ k : ℕ+, ∃ z : Fin n → ℤ,
      (fun j ↦ (z j : ℝ)) = fun j ↦ ((k : ℕ) : ℝ) * (v j : ℝ) := by
  let M : Matrix (Fin n) Unit ℚ := fun j _ ↦ v j
  let kNat : ℕ := M.den
  have hkNat_ne : kNat ≠ 0 := M.den_ne_zero
  refine ⟨⟨kNat, Nat.pos_of_ne_zero hkNat_ne⟩, fun j ↦ M.num j (), ?_⟩
  ext j
  change (M.num j () : ℝ) = (kNat : ℝ) * (v j : ℝ)
  have hdiv : (M.num j () : ℚ) / kNat = v j := by
    simpa [M, kNat] using M.num_div_den j ()
  have hkReal_ne : ((kNat : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hkNat_ne
  have hdivReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hdiv
  have hdivReal' : (M.num j () : ℝ) / (kNat : ℝ) = (v j : ℝ) := by
    simpa using hdivReal
  have hmul : (M.num j () : ℝ) = (v j : ℝ) * (kNat : ℝ) :=
    (div_eq_iff hkReal_ne).mp hdivReal'
  simpa [mul_comm] using hmul

/-- Helper for Exercise 4.11: the common-denominator lemma with an explicit positive natural
multiplier, so later IDP arguments can package it as a `ℕ+` only at the final application site. -/
lemma exists_pos_nat_and_integer_multiple_of_rational_vector_nat
    (v : Fin n → ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∃ z : Fin n → ℤ,
      (fun j ↦ (z j : ℝ)) = fun j ↦ (k : ℝ) * (v j : ℝ) := by
  -- Unpack the existing `ℕ+` witness and keep only its positivity proof.
  rcases exists_pos_nat_and_integer_multiple_of_rational_vector v with ⟨k, z, hz⟩
  exact ⟨k, k.2, z, hz⟩

/-- Helper for Exercise 4.11: if a set `F` lies in the nonnegative rational polyhedron and
contains a lineality direction `r`, then `r = 0`. The proof uses a large negative multiple of `r`
to contradict nonnegativity in any nonzero coordinate. -/
lemma eq_zero_of_mem_linealitySpace_of_subset_nonnegative_rational_matrix_polyhedron
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {F : Set (Fin n → ℝ)} (hF_subset : F ⊆ nonnegative_rational_matrix_polyhedron A b)
    {r x : Fin n → ℝ}
    (hr : r ∈ linealitySpace F)
    (hx : x ∈ F) :
    r = 0 := by
  rw [mem_linealitySpace_iff] at hr
  ext j
  by_contra hne
  let a : ℝ := (-x j - 1) / r j
  have hxaF : x + a • r ∈ F := hr hx a
  have hxa_nonneg :
      0 ≤ x j + a * r j := by
    have hxaP : x + a • r ∈ nonnegative_rational_matrix_polyhedron A b := hF_subset hxaF
    have hcoord := (mem_nonnegative_rational_matrix_polyhedron_iff.mp hxaP).2 j
    simpa [a, Pi.add_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hcoord
  have hrj : r j ≠ 0 := by
    simpa using hne
  have hcalc : x j + a * r j = -1 := by
    dsimp [a]
    field_simp [hrj]
    ring
  linarith [hxa_nonneg]

/-- Helper for Exercise 4.11: once the nonnegative rational polyhedron is nonempty, its
lineality space is trivial. -/
lemma eq_zero_of_mem_linealitySpace_nonnegative_rational_matrix_polyhedron
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {r x : Fin n → ℝ}
    (hr : r ∈ linealitySpace (nonnegative_rational_matrix_polyhedron A b))
    (hx : x ∈ nonnegative_rational_matrix_polyhedron A b) :
    r = 0 := by
  -- Specialize the subset version to the ambient polyhedron itself.
  exact
    eq_zero_of_mem_linealitySpace_of_subset_nonnegative_rational_matrix_polyhedron
      (A := A) (b := b) (F := nonnegative_rational_matrix_polyhedron A b) (fun _ hx' ↦ hx') hr hx

/-- Helper for Exercise 4.11: every minimal face of the nonnegative rational polyhedron is
pointed, because any lineality direction would violate the nonnegativity constraints at a point of
that face. -/
lemma minimal_face_is_pointed_of_nonnegative_rational_polyhedron
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {F : Set (Fin n → ℝ)}
    (hF : IsMinimalFaceOf ℝ (nonnegative_rational_matrix_polyhedron A b) F) :
    is_pointed F := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  rcases hF.nonempty with ⟨x, hxF⟩
  -- Apply the subset version to the minimal face itself.
  exact
    eq_zero_of_mem_linealitySpace_of_subset_nonnegative_rational_matrix_polyhedron
      (A := A) (b := b) (F := F) hF.subset hr hxF

/-- The integer decomposition property: every integral point of a positive integral dilate of `P`
decomposes as a sum of the same number of integral points of `P`. -/
def HasIntegerDecompositionProperty
    {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  let integerPoints : Set (ι → ℝ) :=
    Set.range (fun z : ι → ℤ ↦ fun i ↦ (z i : ℝ))
  ∀ k : ℕ+, ∀ x ∈ (((k : ℕ) : ℝ) • P ∩ integerPoints),
      ∃ y : Fin k → ι → ℝ,
        (∀ t : Fin k, y t ∈ P ∩ integerPoints) ∧
        x = fun j ↦ ∑ t : Fin k, y t j

/-- Helper for Exercise 4.11: a sum over `Fin k` splits into the `0`th term and the remaining
indices. This is the first algebraic normalization needed in the `k > 1` IDP endgame. -/
lemma fin_sum_eq_head_add_tail
    {k : ℕ+} (f : Fin k → ℝ) :
    (∑ t : Fin k, f t) =
      f 0 + Finset.sum (Finset.univ.erase (0 : Fin k)) f := by
  -- Peel off the distinguished index `0` from the finite sum.
  simpa [add_comm] using
    (Finset.sum_erase_add
      (s := Finset.univ)
      (a := (0 : Fin k))
      (f := f)
      (Finset.mem_univ (0 : Fin k))).symm

/-- Helper for Exercise 4.11: averaging the tail terms of a `Fin k`-family of points in the
nonnegative rational polyhedron stays inside that polyhedron. -/
lemma tailAverage_mem_nonnegative_rational_matrix_polyhedron
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {k : ℕ+}
    (hk_gt_one : 1 < (k : ℕ))
    {y : Fin k → Fin n → ℝ}
    (hyP : ∀ t : Fin k, y t ∈ nonnegative_rational_matrix_polyhedron A b) :
    (fun j ↦
      (Finset.sum (Finset.univ.erase (0 : Fin k)) (fun t ↦ y t j)) /
        ((((k : ℕ) - 1 : ℕ) : ℝ)) ) ∈
      nonnegative_rational_matrix_polyhedron A b := by
  let tail : Finset (Fin k) := Finset.univ.erase (0 : Fin k)
  let denom : ℝ := ((((k : ℕ) - 1 : ℕ) : ℝ))
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact_mod_cast Nat.sub_pos_of_lt hk_gt_one
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hweights :
      Finset.sum tail (fun _ ↦ (1 / denom : ℝ)) = 1 := by
    have hcard : tail.card = (k : ℕ) - 1 := by
      simp [tail]
    have hdenom_eq : (((k : ℕ) - 1 : ℕ) : ℝ) = denom := by
      rfl
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hdenom_eq]
    field_simp [hdenom_ne]
  have hcomb :
      Finset.sum tail (fun t ↦ (1 / denom : ℝ) • y t) ∈
        nonnegative_rational_matrix_polyhedron A b := by
    -- Apply convexity to the equal-weight tail barycenter.
    refine (nonnegative_rational_matrix_polyhedron_convex A b).sum_mem ?_ hweights ?_
    · intro t ht
      positivity
    · intro t ht
      exact hyP t
  have hsum_smul :
      Finset.sum tail (fun t ↦ (1 / denom : ℝ) • y t) =
        (1 / denom : ℝ) • Finset.sum tail y := by
    simpa using (Finset.smul_sum (s := tail) (r := (1 / denom : ℝ)) (f := y)).symm
  have hrepr :
      (1 / denom : ℝ) • Finset.sum tail y =
        fun j ↦ Finset.sum tail (fun t ↦ y t j) / denom := by
    -- Rewrite the vector-valued barycenter coordinatewise as the displayed tail average.
    ext j
    simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
  have hcomb' :
      (fun j ↦ Finset.sum tail (fun t ↦ y t j) / denom) ∈
        nonnegative_rational_matrix_polyhedron A b := by
    rwa [hsum_smul, hrepr] at hcomb
  simpa [tail, denom] using hcomb'

/-- Helper for Exercise 4.11: after clearing denominators, the original rational point is the
convex combination of the first IDP summand and the average of the remaining summands. -/
lemma rationalPoint_eq_headAdd_tailAverage
    {k : ℕ+} {x : Fin n → ℝ} {y : Fin k → Fin n → ℝ}
    (hk_gt_one : 1 < (k : ℕ))
    (hsum : (((k : ℕ) : ℝ) • x) = fun j ↦ ∑ t : Fin k, y t j) :
    x =
      (1 / (((k : ℕ) : ℝ))) • y 0 +
        (((((k : ℕ) - 1 : ℕ) : ℝ) / (((k : ℕ) : ℝ))) •
          (fun j ↦
            (Finset.sum (Finset.univ.erase (0 : Fin k)) (fun t ↦ y t j)) /
              (((((k : ℕ) - 1 : ℕ) : ℝ))))) := by
  let tail : Finset (Fin k) := Finset.univ.erase (0 : Fin k)
  let tailDen : ℝ := ((((k : ℕ) - 1 : ℕ) : ℝ))
  have hk_pos : 0 < (k : ℕ) := lt_trans Nat.zero_lt_one hk_gt_one
  have hkReal_ne : (((k : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk_pos
  have htailDen_pos : 0 < tailDen := by
    dsimp [tailDen]
    exact_mod_cast Nat.sub_pos_of_lt hk_gt_one
  have htailDen_ne : tailDen ≠ 0 := ne_of_gt htailDen_pos
  ext j
  have hsum_split :
      (∑ t : Fin k, y t j) = y 0 j + Finset.sum tail (fun t ↦ y t j) := by
    simpa [tail] using fin_sum_eq_head_add_tail (f := fun t : Fin k ↦ y t j)
  have hcoord :
      (((k : ℕ) : ℝ) * x j) = y 0 j + Finset.sum tail (fun t ↦ y t j) := by
    -- Split the cleared-denominator identity into the head summand and the remaining tail terms.
    have hcoord' := congrArg (fun f : Fin n → ℝ ↦ f j) hsum
    calc
      (((k : ℕ) : ℝ) * x j) = ∑ t : Fin k, y t j := by
        simpa [Pi.smul_apply] using hcoord'
      _ = y 0 j + Finset.sum tail (fun t ↦ y t j) := hsum_split
  have hx_as_div :
      x j = (y 0 j + Finset.sum tail (fun t ↦ y t j)) / (((k : ℕ) : ℝ)) := by
    -- Divide the cleared-denominator identity by `k`.
    refine (eq_div_iff hkReal_ne).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcoord
  have hcoord_repr :
      x j =
        (1 / (((k : ℕ) : ℝ))) * y 0 j +
          (((((k : ℕ) - 1 : ℕ) : ℝ) / (((k : ℕ) : ℝ))) *
            (Finset.sum tail (fun t ↦ y t j) / tailDen)) := by
    calc
      x j = (y 0 j + Finset.sum tail (fun t ↦ y t j)) / (((k : ℕ) : ℝ)) := hx_as_div
      _ =
          (1 / (((k : ℕ) : ℝ))) * y 0 j +
            (((((k : ℕ) - 1 : ℕ) : ℝ) / (((k : ℕ) : ℝ))) *
              (Finset.sum tail (fun t ↦ y t j) / tailDen)) := by
            field_simp [hkReal_ne, htailDen_ne]
            ring
  simpa [tail, tailDen, Pi.smul_apply] using hcoord_repr

/-- Helper for Exercise 4.11: once an extreme face of the nonnegative rational polyhedron contains
a rational point, the integer decomposition property produces an integral point on that same face.
The proof follows the source route: clear denominators, decompose the integral multiple, and use
the face property on the first summand versus the average of the remaining summands. -/
lemma exists_integer_point_of_rational_point_in_extreme_face_of_idp
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {F : Set (Fin n → ℝ)} {x : Fin n → ℝ} {v : Fin n → ℚ}
    (hF : IsExtreme ℝ (nonnegative_rational_matrix_polyhedron A b) F)
    (hxF : x ∈ F)
    (hv : x = fun j ↦ (v j : ℝ))
    (hIDP : HasIntegerDecompositionProperty (nonnegative_rational_matrix_polyhedron A b)) :
    ∃ y ∈ F, y ∈ integerVectors n := by
  rcases exists_pos_nat_and_integer_multiple_of_rational_vector_nat v with ⟨k, hk_pos, z, hz⟩
  let kp : ℕ+ := ⟨k, hk_pos⟩
  let zR : Fin n → ℝ := fun j ↦ (z j : ℝ)
  have hxP : x ∈ nonnegative_rational_matrix_polyhedron A b := hF.subset hxF
  have hkR_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk_pos
  have hz_smul : zR = (k : ℝ) • x := by
    -- Clearing denominators turns `x` into the integral point `zR = k • x`.
    simpa [zR, hv, Pi.smul_apply] using hz
  have hz_mem_scaled :
      zR ∈ (((k : ℕ) : ℝ) • nonnegative_rational_matrix_polyhedron A b) ∩
        Set.range (fun w : Fin n → ℤ ↦ fun j ↦ (w j : ℝ)) := by
    refine ⟨⟨x, hxP, hz_smul.symm⟩, ⟨z, rfl⟩⟩
  rcases hIDP kp zR (by simpa [kp] using hz_mem_scaled) with ⟨y, hy, hsum⟩
  have hyP :
      ∀ t : Fin kp, y t ∈ nonnegative_rational_matrix_polyhedron A b := fun t ↦ (hy t).1
  have hyInt : ∀ t : Fin kp, y t ∈ integerVectors n := by
    intro t
    -- The local `integerPoints` in `HasIntegerDecompositionProperty` is exactly `integerVectors n`.
    simpa [integerVectors, Function.comp] using (hy t).2
  by_cases hk_one : k = 1
  · -- When the cleared denominator is `1`, the unique IDP summand is exactly `x`.
    refine ⟨y 0, ?_, hyInt 0⟩
    have hzR_eq_y0 : zR = y 0 := by
      -- Evaluate the decomposition identity coordinatewise; on `Fin 1` the sum has one term.
      have hsub : Subsingleton (Fin kp) := by
        apply Fintype.card_le_one_iff_subsingleton.mp
        simpa [kp, hk_one]
      have huniv : (Finset.univ : Finset (Fin kp)) = {0} := by
        ext t
        simp [hsub.elim t 0]
      ext j
      have hcoord := congrArg (fun f : Fin n → ℝ ↦ f j) hsum
      have hsum_single : (∑ t : Fin kp, y t j) = y 0 j := by
        rw [show (Finset.univ : Finset (Fin kp)) = {0} from huniv]
        simp
      exact hcoord.trans hsum_single
    have hzR_eq_x : zR = x := by
      simpa [hk_one] using hz_smul
    have hy0_eq_x : y 0 = x := hzR_eq_y0.symm.trans hzR_eq_x
    simpa [hy0_eq_x] using hxF
  · have hk_gt_one : 1 < k := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hk_pos) (by
        intro hk_eq
        exact hk_one hk_eq.symm)
    let tailAvg : Fin n → ℝ :=
      fun j ↦
        (Finset.sum (Finset.univ.erase (0 : Fin kp)) fun t ↦ y t j) / (((k - 1 : ℕ) : ℝ))
    have htailP : tailAvg ∈ nonnegative_rational_matrix_polyhedron A b := by
      -- Average the tail summands inside the ambient convex polyhedron.
      simpa [kp, tailAvg] using
        tailAverage_mem_nonnegative_rational_matrix_polyhedron
          (A := A) (b := b) (k := kp) hk_gt_one hyP
    have hcomb : x = (1 / (k : ℝ)) • y 0 + ((((k - 1 : ℕ) : ℝ) / (k : ℝ))) • tailAvg := by
      -- Rewrite the cleared-denominator identity as a strict convex combination of one summand
      -- and the average of the remaining summands.
      simpa [kp, tailAvg] using
        rationalPoint_eq_headAdd_tailAverage
          (k := kp)
          hk_gt_one
          (x := x)
          (y := y)
          (hz_smul.symm.trans hsum)
    by_cases hy0_tail : y 0 = tailAvg
    · refine ⟨y 0, ?_, hyInt 0⟩
      have hx_eq_y0 : x = y 0 := by
        ext j
        have hcoord :
            x j =
              (1 / (k : ℝ)) * y 0 j +
                ((((k - 1 : ℕ) : ℝ) / (k : ℝ))) * y 0 j := by
          simpa [Pi.smul_apply, hy0_tail, mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun f : Fin n → ℝ ↦ f j) hcomb
        have hcoeff :
            (1 / (k : ℝ)) + ((((k - 1 : ℕ) : ℝ) / (k : ℝ))) = 1 := by
          have hk_one_add : (1 : ℝ) + (((k - 1 : ℕ) : ℝ)) = (k : ℝ) := by
            have hk_one_add_nat : 1 + (k - 1) = k := by
              omega
            exact_mod_cast hk_one_add_nat
          field_simp [hkR_ne]
          exact hk_one_add
        calc
          x j = ((1 / (k : ℝ)) + ((((k - 1 : ℕ) : ℝ) / (k : ℝ)))) * y 0 j := by
            nlinarith [hcoord]
          _ = y 0 j := by rw [hcoeff, one_mul]
      simpa [hx_eq_y0] using hxF
    · have hseg : x ∈ openSegment ℝ (y 0) tailAvg := by
        -- The coefficients are strictly between the endpoints because `k > 1`.
        have hk_sub_pos : 0 < k - 1 := Nat.sub_pos_of_lt hk_gt_one
        have hk_one_add_nat : 1 + (k - 1) = k := by
          omega
        have hk_one_add : (1 : ℝ) + (((k - 1 : ℕ) : ℝ)) = (k : ℝ) := by
          exact_mod_cast hk_one_add_nat
        refine (mem_openSegment_iff_div).2 ?_
        refine ⟨(1 : ℝ), (((k - 1 : ℕ) : ℝ)), zero_lt_one, by exact_mod_cast hk_sub_pos, ?_⟩
        simpa [hk_one_add] using hcomb.symm
      refine ⟨y 0, ?_, hyInt 0⟩
      exact hF.left_mem_of_mem_openSegment (hyP 0) htailP hxF hseg

/-- Helper for Exercise 4.11: an equality face of `polyhedron_le_set M d` is again a polyhedron,
obtained by adjoining the exposing inequality and its negation to the defining system. -/
lemma face_set_is_polyhedron
    {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (d : Fin p → ℝ)
    (c : Fin q → ℝ)
    (δ : ℝ) :
    is_polyhedron (face_set (polyhedron_le_set M d) c δ) := by
  let B : Matrix (Fin (p + 2)) (Fin q) ℝ :=
    fun i j ↦ Fin.cases (c j) (fun i' ↦ Fin.cases (-c j) (fun i'' ↦ M i'' j) i') i
  let rhs : Fin (p + 2) → ℝ :=
    fun i ↦ Fin.cases δ (fun i' ↦ Fin.cases (-δ) d i') i
  refine ⟨p + 2, B, rhs, ?_⟩
  ext x
  rw [mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    have hxEq_sum : ∑ j : Fin q, c j * x j = δ := by
      simpa [dotProduct] using hxEq
    change B *ᵥ x ≤ rhs
    intro i
    cases i using Fin.cases with
    | zero =>
        -- The first augmented row records the exposing inequality at equality.
        simpa [B, rhs, Matrix.mulVec, dotProduct] using hxEq_sum.le
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            -- The second augmented row enforces the opposite inequality.
            have hneg_sum : ∑ j : Fin q, (-c j) * x j ≤ -δ := by
              have hneg_eq : ∑ j : Fin q, (-c j) * x j = -δ := by
                calc
                  ∑ j : Fin q, (-c j) * x j = ∑ j : Fin q, -(c j * x j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
                  _ = -(∑ j : Fin q, c j * x j) := by
                    rw [Finset.sum_neg_distrib]
                  _ = -δ := by rw [hxEq_sum]
              exact hneg_eq.le
            convert hneg_sum using 1
        | succ i =>
            simpa [B, rhs, Matrix.mulVec, dotProduct] using hxP i
  · intro hxB
    refine ⟨?_, ?_⟩
    · -- The tail rows are exactly the original `M *ᵥ x ≤ d` system.
      intro i
      simpa [B, rhs, Matrix.mulVec, dotProduct] using hxB i.succ.succ
    · -- The two added rows force the exposing equation.
      have hupper_sum : ∑ j : Fin q, c j * x j ≤ δ := by
        simpa [B, rhs, Matrix.mulVec, dotProduct] using hxB 0
      have hlower_sum : δ ≤ ∑ j : Fin q, c j * x j := by
        have hneg_sum : ∑ j : Fin q, (-c j) * x j ≤ -δ := by
          convert hxB (Fin.succ 0) using 1
        have hneg_sum' : -(∑ j : Fin q, c j * x j) ≤ -δ := by
          calc
            -(∑ j : Fin q, c j * x j) = ∑ j : Fin q, (-c j) * x j := by
              calc
                -(∑ j : Fin q, c j * x j) = ∑ j : Fin q, -(c j * x j) := by
                  rw [Finset.sum_neg_distrib]
                _ = ∑ j : Fin q, (-c j) * x j := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ ≤ -δ := hneg_sum
        linarith
      have hxEq_sum : ∑ j : Fin q, c j * x j = δ := by
        linarith
      simpa [dotProduct] using hxEq_sum

/-- Helper for Exercise 4.11: every nonempty exposed face of `polyhedron_le_set M d` has the same
lineality space as the ambient polyhedron. -/
lemma linealitySpace_eq_of_nonempty_exposedFace_polyhedron
    {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {d : Fin p → ℝ}
    {F : Set (Fin q → ℝ)}
    (hF : IsExposed ℝ (polyhedron_le_set M d) F)
    (hF_nonempty : F.Nonempty) :
    linealitySpace F = linealitySpace (polyhedron_le_set M d) := by
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed M d F hF hF_nonempty
  obtain ⟨x0, hx0F⟩ := hF_nonempty
  have hx0_active : x0 ∈ active_constraint_face M d I := by
    simpa [hI] using hx0F
  have hP_nonempty : (polyhedron_le_set M d).Nonempty := by
    exact ⟨x0, mem_polyhedron_of_mem_active_constraint_face hx0_active⟩
  have hkernelP := polyhedron_linealitySpace_eq_kernel_set M d hP_nonempty
  rw [hI, hkernelP]
  ext r
  constructor
  · intro hr
    rw [mem_linealitySpace_iff] at hr
    ext i
    by_cases hi : i ∈ I
    · have hx0_eq : (M *ᵥ x0) i = d i := (mem_active_constraint_face_iff.mp hx0_active).1 i hi
      have htranslate_eq : (M *ᵥ (x0 + (1 : ℝ) • r)) i = d i := by
        exact (mem_active_constraint_face_iff.mp (hr hx0_active 1)).1 i hi
      calc
        (M *ᵥ r) i = (M *ᵥ (x0 + (1 : ℝ) • r)) i - (M *ᵥ x0) i := by
          simp [Matrix.mulVec_add]
        _ = d i - d i := by rw [htranslate_eq, hx0_eq]
        _ = 0 := by simp
    · have htranslate : ∀ a : ℝ, (M *ᵥ (x0 + a • r)) i ≤ d i := by
        intro a
        exact (mem_active_constraint_face_iff.mp (hr hx0_active a)).2 i hi
      by_contra hri
      let a : ℝ := (d i - (M *ᵥ x0) i + 1) / (M *ᵥ r) i
      have htranslate' : (M *ᵥ x0) i + a * (M *ᵥ r) i ≤ d i := by
        simpa [Matrix.mulVec_add, Matrix.mulVec_smul, a] using htranslate a
      have ha_mul : a * (M *ᵥ r) i = d i - (M *ᵥ x0) i + 1 := by
        dsimp [a]
        exact div_mul_cancel₀ _ hri
      linarith
  · intro hr
    rw [mem_linealitySpace_iff]
    have hr_zero : M *ᵥ r = 0 := by
      simpa [hkernelP] using hr
    intro x hxF a
    refine (mem_active_constraint_face_iff).2 ?_
    rcases mem_active_constraint_face_iff.mp hxF with ⟨hxEq, hxLe⟩
    constructor
    · intro i hi
      have hri : (M *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxEq i hi
    · intro i hi
      have hri : (M *ᵥ r) i = 0 := by
        simpa using congrFun hr_zero i
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hxLe i hi

/-- Helper for Exercise 4.11: every nonempty exposed face of the nonnegative rational polyhedron
contains an integral point when the ambient polyhedron has the integer decomposition property. -/
lemma exists_integer_point_of_nonempty_exposed_face_of_idp
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {F : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (nonnegative_rational_matrix_polyhedron A b) F)
    (hF_nonempty : F.Nonempty)
    (hIDP : HasIntegerDecompositionProperty (nonnegative_rational_matrix_polyhedron A b)) :
    ∃ x ∈ F, x ∈ integerVectors n := by
  let M : Matrix (Fin (m + n)) (Fin n) ℝ :=
    (nonnegative_rational_constraint_matrix A).map (Rat.castHom ℝ)
  let rhs : Fin (m + n) → ℝ := fun i ↦ (nonnegative_rational_constraint_rhs b i : ℝ)
  let Aaug : Matrix (Fin (m + n)) (Fin n) ℚ := nonnegative_rational_constraint_matrix A
  let baug : Fin (m + n) → ℚ := nonnegative_rational_constraint_rhs b
  have hF_exposed' : IsExposed ℝ (polyhedron_le_set M rhs) F := by
    simpa [M, rhs, nonnegative_rational_polyhedron_eq_augmented_system, rational_matrix_polyhedron]
      using hF
  obtain ⟨c, δ, -, hF_eqface⟩ := hF_exposed'.exists_eq_face_set_of_nonempty hF_nonempty
  have hF_polyhedron : is_polyhedron F := by
    rw [hF_eqface]
    exact face_set_is_polyhedron M rhs c δ
  have hF_lineality : linealitySpace F = ({0} : Set (Fin n → ℝ)) := by
    have hlineality :
        linealitySpace F = linealitySpace (polyhedron_le_set M rhs) :=
      linealitySpace_eq_of_nonempty_exposedFace_polyhedron hF_exposed' hF_nonempty
    have hambient_zero : linealitySpace (polyhedron_le_set M rhs) = ({0} : Set (Fin n → ℝ)) := by
      ext r
      constructor
      · intro hr
        obtain ⟨x0, hx0F⟩ := hF_nonempty
        have hx0P : x0 ∈ nonnegative_rational_matrix_polyhedron A b := hF.subset hx0F
        have hrP : r ∈ linealitySpace (nonnegative_rational_matrix_polyhedron A b) := by
          simpa [M, rhs, nonnegative_rational_polyhedron_eq_augmented_system,
            rational_matrix_polyhedron, mem_rational_matrix_polyhedron] using hr
        simp [eq_zero_of_mem_linealitySpace_nonnegative_rational_matrix_polyhedron
          (A := A) (b := b) hrP hx0P]
      · intro hr
        rcases Set.mem_singleton_iff.mp hr with rfl
        exact zero_mem_linealitySpace
    exact hlineality.trans hambient_zero
  have hF_extreme_nonempty : (F.extremePoints ℝ).Nonempty := by
    exact
      (polyhedron_extremePoints_nonempty_iff_linealitySpace_eq_zero
        hF_polyhedron hF_nonempty).2 hF_lineality
  rcases hF_extreme_nonempty with ⟨x, hx_extreme_F⟩
  have hx_extreme_P :
      x ∈ (nonnegative_rational_matrix_polyhedron A b).extremePoints ℝ := by
    exact hF.isExtreme.extremePoints_subset_extremePoints hx_extreme_F
  obtain ⟨π, hπ⟩ := rational_vertices_have_polynomially_bounded_encoding_size
  let L : ℕ :=
    (∑ i : Fin (m + n), ∑ j : Fin n, EncodingSize.rational (Aaug i j)) +
      ∑ i : Fin (m + n), EncodingSize.rational (baug i)
  have hAenc : ∀ i j, EncodingSize.rational (Aaug i j) ≤ L := by
    intro i j
    have hij :
        EncodingSize.rational (Aaug i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (Aaug i j') := by
      simpa using
        (Finset.single_le_sum
          (fun j' _ ↦ Nat.zero_le (EncodingSize.rational (Aaug i j')))
          (by simp : j ∈ (Finset.univ : Finset (Fin n))))
    have hii :
        (∑ j' : Fin n, EncodingSize.rational (Aaug i j')) ≤
          ∑ i' : Fin (m + n), ∑ j' : Fin n, EncodingSize.rational (Aaug i' j') := by
      simpa using
        (Finset.single_le_sum
          (fun i' _ ↦ Nat.zero_le (∑ j' : Fin n, EncodingSize.rational (Aaug i' j')))
          (by simp : i ∈ (Finset.univ : Finset (Fin (m + n)))))
    calc
      EncodingSize.rational (Aaug i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (Aaug i j') := hij
      _ ≤ ∑ i' : Fin (m + n), ∑ j' : Fin n, EncodingSize.rational (Aaug i' j') := hii
      _ ≤ L := by
          exact Nat.le_add_right _ _
  have hbenc : ∀ i, EncodingSize.rational (baug i) ≤ L := by
    intro i
    have hi :
        EncodingSize.rational (baug i) ≤
          ∑ i' : Fin (m + n), EncodingSize.rational (baug i') := by
      simpa using
        (Finset.single_le_sum
          (fun i' _ ↦ Nat.zero_le (EncodingSize.rational (baug i')))
          (by simp : i ∈ (Finset.univ : Finset (Fin (m + n)))))
    calc
      EncodingSize.rational (baug i) ≤
          ∑ i' : Fin (m + n), EncodingSize.rational (baug i') := hi
      _ ≤ L := by
          simpa [L, add_comm, add_left_comm, add_assoc] using
            (Nat.le_add_left
              (∑ i' : Fin (m + n), ∑ j : Fin n, EncodingSize.rational (Aaug i' j))
              (∑ i' : Fin (m + n), EncodingSize.rational (baug i')))
  rcases
      hπ Aaug baug L hAenc hbenc x
        (by
          simpa [Aaug, baug, nonnegative_rational_polyhedron_eq_augmented_system] using
            hx_extreme_P) with
    ⟨v, hv, _⟩
  have hxF : x ∈ F := extremePoints_subset hx_extreme_F
  exact
    exists_integer_point_of_rational_point_in_extreme_face_of_idp
      hF.isExtreme hxF (by simpa using hv) hIDP

/-- Exercise 4.11 (1). If `P = {x ∈ ℝ^n_+ | A x ≤ b}` has the integer decomposition property,
then `P` is an integral polyhedron. -/
theorem nonnegative_rational_polyhedron_is_integral_of_integer_decomposition_property
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hIDP : HasIntegerDecompositionProperty (nonnegative_rational_matrix_polyhedron A b)) :
    is_integral (nonnegative_rational_matrix_polyhedron A b) := by
  refine
    (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
      (P := nonnegative_rational_matrix_polyhedron A b)
      (hP := nonnegative_rational_matrix_polyhedron_is_rational A b)).2 ?_
  intro c z hGreatest
  rcases hGreatest.1 with ⟨x0, hx0P, hx0Obj⟩
  let F : Set (Fin n → ℝ) := face_set (nonnegative_rational_matrix_polyhedron A b) c z
  have hvalid : is_valid_inequality (nonnegative_rational_matrix_polyhedron A b) c z := by
    intro y hyP
    exact hGreatest.2 ⟨y, hyP, rfl⟩
  have hF_exposed : IsExposed ℝ (nonnegative_rational_matrix_polyhedron A b) F := by
    simpa [F] using isExposed_face_set_of_valid_inequality hvalid
  have hF_nonempty : F.Nonempty := by
    refine ⟨x0, ?_⟩
    simpa [F] using (mem_face_set_iff).2 ⟨hx0P, hx0Obj⟩
  rcases
      exists_integer_point_of_nonempty_exposed_face_of_idp
        (A := A) (b := b) hF_exposed hF_nonempty hIDP with
    ⟨x, hxF, hxInt⟩
  have hxF' := mem_face_set_iff.mp hxF
  exact ⟨x, ⟨hxF'.1, hxInt⟩, hxF'.2⟩

/-- Helper for Exercise 4.11: the sum of row `i` over the columns of `A` carrying color `c`. -/
def column_color_sum
    {k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c : Fin k)
    (i : Fin m) : ℤ :=
  (Finset.univ.filter fun j : Fin n ↦ κ j = c).sum fun j ↦ A i j

/-- Helper for Exercise 4.11: duplicating columns according to multiplicities preserves total
unimodularity after reindexing the duplicated family by `Fin`. -/
lemma duplicated_column_presentation_is_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (u : Fin n → ℕ)
    (hA : A.IsTotallyUnimodular) :
    ((A.submatrix id (fun a : Σ j, Fin (u j) ↦ a.1)).reindex
      (Equiv.refl _)
      (Fintype.equivFin (Σ j, Fin (u j)))).IsTotallyUnimodular := by
  -- The duplicated-column matrix is just a column submatrix, followed by a finite reindexing.
  have hDup :
      (A.submatrix id (fun a : Σ j, Fin (u j) ↦ a.1)).IsTotallyUnimodular :=
    hA.submatrix id (fun a : Σ j, Fin (u j) ↦ a.1)
  simpa using
    (Matrix.reindex_isTotallyUnimodular
      (A.submatrix id (fun a : Σ j, Fin (u j) ↦ a.1))
      (Equiv.refl _)
      (Fintype.equivFin (Σ j, Fin (u j)))).2 hDup

/-- Helper for Exercise 4.11: if the color-class row sums differ pairwise by at most `1`, then a
single class cannot exceed the average upper bound coming from the total row sum. -/
lemma balanced_color_sums_le_rhs_of_total_bound
    {k : ℕ} (hk : 0 < k) {s : Fin k → ℤ} {B : ℤ}
    (hbalanced : ∀ c d : Fin k, c ≠ d → Int.natAbs (s c - s d) ≤ 1)
    (htotal : ∑ t : Fin k, s t ≤ k * B) :
    ∀ t : Fin k, s t ≤ B := by
  intro t
  by_contra ht
  -- If one color exceeds `B`, pairwise balance forces every other color to be at least `B`.
  have ht_succ : B + 1 ≤ s t := by
    linarith
  have hall : ∀ d : Fin k, B ≤ s d := by
    intro d
    by_cases hdt : d = t
    · simpa [hdt] using le_trans (by linarith : B ≤ B + 1) ht_succ
    · have habs : |s t - s d| ≤ 1 := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hbalanced t d (fun htd' ↦ hdt htd'.symm)
      rcases Int.abs_le_one_iff.mp habs with hdiff | hdiff | hdiff
      · linarith
      · linarith
      · linarith
  -- Splitting off the offending color yields a strict total-sum contradiction.
  have hrest :
      Finset.sum (Finset.univ.erase t) (fun _ : Fin k ↦ (B : ℤ)) ≤
        Finset.sum (Finset.univ.erase t) s := by
    exact Finset.sum_le_sum fun d hd ↦ hall d
  have hsplit : (∑ d : Fin k, s d) = s t + Finset.sum (Finset.univ.erase t) s := by
    simpa using
      (Finset.sum_erase_add (s := Finset.univ) (a := t) (f := s) (Finset.mem_univ t)).symm
  have hlarge : k * B + 1 ≤ ∑ d : Fin k, s d := by
    rw [hsplit]
    have hrest' : (((Finset.univ.erase t).card : ℕ) : ℤ) * B ≤ Finset.sum (Finset.univ.erase t) s := by
      simpa [nsmul_eq_mul] using hrest
    have hcardNat : (Finset.univ.erase t).card = k - 1 := by
      simp
    have hk1 : 1 ≤ k := hk
    have hcastsub : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - (1 : ℤ) := by
      exact Nat.cast_sub hk1
    have hrest'' : ((k : ℤ) - 1) * B ≤ Finset.sum (Finset.univ.erase t) s := by
      rw [← hcastsub]
      simpa [hcardNat] using hrest'
    linarith
  have hcontr : k * B + 1 ≤ k * B := le_trans hlarge htotal
  linarith

/-- Helper for Exercise 4.11: partitioning the duplicated copies of one original column by color
recovers the original multiplicity. This is the coordinate-count identity needed in part (2). -/
lemma duplicated_column_fiber_card
    (u : Fin n → ℕ)
    (j : Fin n) :
    (Finset.univ.filter fun a : Σ j, Fin (u j) ↦ a.1 = j).card = u j := by
  classical
  let emb : Fin (u j) ↪ Σ j, Fin (u j) :=
    ⟨fun b ↦ ⟨j, b⟩, fun a b h ↦ by cases h; rfl⟩
  have hfiber :
      Finset.univ.filter (fun a : Σ j, Fin (u j) ↦ a.1 = j) =
        Finset.univ.map emb := by
    ext a
    rcases a with ⟨j', b⟩
    constructor
    · intro ha
      have hj' : j' = j := by simpa using ha
      subst hj'
      refine Finset.mem_map.2 ?_
      exact ⟨b, by simp, by simp [emb]⟩
    · intro ha
      rcases Finset.mem_map.1 ha with ⟨x, -, hx⟩
      simpa [emb] using (congrArg Sigma.fst hx).symm
  -- The fixed-`j` fiber is exactly the image of `Fin (u j)` under the obvious embedding.
  rw [hfiber, Finset.card_map, Finset.card_univ]
  simp

/-- Helper for Exercise 4.11: partitioning a fixed owner fiber by color recovers the total fiber
cardinality. This isolates the counting step used in the duplicated-column decomposition route. -/
lemma fiber_card_eq_sum_color_fiber_cards
    {α β γ : Type*}
    [Fintype α] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (owner : α → β)
    (color : α → γ)
    (b : β) :
    ∑ c : γ, ((Finset.univ.filter fun a : α ↦ owner a = b ∧ color a = c).card : ℕ) =
      (Finset.univ.filter fun a : α ↦ owner a = b).card := by
  let s : Finset α := Finset.univ.filter fun a : α ↦ owner a = b
  -- Sum the color-fiber cardinalities inside the fixed owner fiber.
  simpa [s, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
    (Finset.sum_card_fiberwise_eq_card_filter s (Finset.univ : Finset γ) color)

/-- Helper for Exercise 4.11: partitioning the duplicated copies of one original column by color
recovers the original multiplicity. This is the coordinate-count identity needed in part (2). -/
lemma duplicated_color_count_sum_eq_multiplicity
    {k : ℕ}
    (u : Fin n → ℕ)
    (κ : (Σ j, Fin (u j)) → Fin k)
    (j : Fin n) :
    ∑ t : Fin k,
      ((Finset.univ.filter fun a : Σ j, Fin (u j) ↦ κ a = t ∧ a.1 = j).card : ℕ) = u j := by
  -- First partition the duplicated copies of column `j` by their colors.
  calc
    ∑ t : Fin k,
        ((Finset.univ.filter fun a : Σ j, Fin (u j) ↦ κ a = t ∧ a.1 = j).card : ℕ)
      = (Finset.univ.filter fun a : Σ j, Fin (u j) ↦ a.1 = j).card := by
          simpa [and_assoc, and_left_comm, and_comm] using
            fiber_card_eq_sum_color_fiber_cards
              (owner := fun a : Σ j, Fin (u j) ↦ a.1)
              (color := κ)
              j
    -- Then identify that fixed-column fiber with the `u j` duplicated copies.
    _ = u j := duplicated_column_fiber_card u j

/-- Helper for Exercise 4.11: after reindexing the duplicated columns by `Fin`, the row sum over
one color class regroups into the original row coefficients weighted by the number of duplicated
copies of each original column carrying that color. -/
lemma duplicated_color_row_sum_eq_sum_mul_duplicate_color_cards
    {k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (u : Fin n → ℕ)
    (κFin : Fin (Fintype.card (Σ j', Fin (u j'))) → Fin k)
    (i : Fin m)
    (t : Fin k) :
    column_color_sum
        ((A.submatrix id (fun a : Σ j', Fin (u j') ↦ a.1)).reindex
          (Equiv.refl _)
          (Fintype.equivFin (Σ j', Fin (u j'))))
        κFin
        t
        i =
      ∑ j,
        A i j *
          ((Finset.univ.filter fun h : Fin (u j) ↦
              κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h⟩) = t).card : ℤ) := by
  classical
  let e : (Σ j', Fin (u j')) ≃ Fin (Fintype.card (Σ j', Fin (u j'))) :=
    Fintype.equivFin (Σ j', Fin (u j'))
  have huniv_sigma :
      (Finset.univ : Finset (Σ j', Fin (u j'))) =
        Finset.univ.sigma (fun j : Fin n ↦ (Finset.univ : Finset (Fin (u j)))) := by
    -- Every dependent pair is uniquely a column index together with one of its duplicated copies.
    ext a
    simp
  -- Reindex the filtered `Fin`-sum back to the duplicated Sigma columns.
  calc
    column_color_sum
        ((A.submatrix id (fun a : Σ j', Fin (u j') ↦ a.1)).reindex
          (Equiv.refl _)
          e)
        κFin
        t
        i =
      ∑ j : Fin (Fintype.card (Σ j', Fin (u j'))),
        if κFin j = t then
          ((A.submatrix id (fun a : Σ j', Fin (u j') ↦ a.1)).reindex
            (Equiv.refl _)
            e) i j
        else 0 := by
          unfold column_color_sum
          rw [Finset.sum_filter]
    _ =
      ∑ a : Σ j', Fin (u j'),
        if κFin (e a) = t then A i a.1 else 0 := by
          refine (Fintype.sum_equiv e.symm _ _ ?_)
          intro j
          by_cases hj : κFin j = t
          · simp [hj, Matrix.reindex_apply]
          · simp [hj, Matrix.reindex_apply]
    _ =
      (Finset.univ.filter (fun a : Σ j', Fin (u j') ↦ κFin (e a) = t)).sum
        (fun a ↦ A i a.1) := by
          rw [← Finset.sum_filter]
    _ =
      (Finset.univ.sigma fun j : Fin n ↦
        (Finset.univ.filter fun h : Fin (u j) ↦ κFin (e ⟨j, h⟩) = t)).sum
        (fun a ↦ A i a.1) := by
          -- Split the Sigma-indexed filter fiberwise by the original column owner.
          rw [huniv_sigma]
          congr
          ext a
          rcases a with ⟨j, h⟩
          simp [Finset.filter_sigma']
    _ = ∑ j,
          (Finset.univ.filter fun h : Fin (u j) ↦ κFin (e ⟨j, h⟩) = t).sum
            (fun _ ↦ A i j) := by
          rw [Finset.sum_sigma']
    _ = ∑ j,
          A i j *
            ((Finset.univ.filter fun h : Fin (u j) ↦ κFin (e ⟨j, h⟩) = t).card : ℤ) := by
          -- Each inner sum is constant, so it collapses to a cardinality factor.
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ =
      ∑ j,
        A i j *
          ((Finset.univ.filter fun h : Fin (u j) ↦
              κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h⟩) = t).card : ℤ) := by
          simp [e]

/-- Helper for Exercise 4.11: counting duplicated copies of a fixed original column by color can
be written either on the `Fin (u j)` fiber or on the full Sigma index with an owner filter. -/
lemma duplicated_color_card_eq_sigma_owner_filter_card
    {k : ℕ}
    (u : Fin n → ℕ)
    (κFin : Fin (Fintype.card (Σ j', Fin (u j'))) → Fin k)
    (j : Fin n)
    (t : Fin k) :
    ((Finset.univ.filter fun h : Fin (u j) ↦
        κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h⟩) = t).card : ℤ) =
      ((Finset.univ.filter fun a : Σ j', Fin (u j') ↦
          κFin (Fintype.equivFin (Σ j', Fin (u j')) a) = t ∧ a.1 = j).card : ℤ) := by
  classical
  let emb : Fin (u j) ↪ Σ j', Fin (u j') :=
    ⟨fun h ↦ ⟨j, h⟩, fun a b hab ↦ by cases hab; rfl⟩
  have hfilter :
      Finset.univ.filter (fun a : Σ j', Fin (u j') ↦
          κFin (Fintype.equivFin (Σ j', Fin (u j')) a) = t ∧ a.1 = j) =
        (Finset.univ.filter fun h : Fin (u j) ↦
          κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h⟩) = t).map emb := by
    -- Both finite sets enumerate exactly the duplicated copies of column `j` colored by `t`.
    ext a
    rcases a with ⟨j', h⟩
    constructor
    · intro ha
      have hmem := Finset.mem_filter.1 ha
      have hj' : j' = j := by simpa using hmem.2.2
      subst hj'
      refine Finset.mem_map.2 ?_
      exact ⟨h, by simpa using hmem.2.1, by simp [emb]⟩
    · intro ha
      rcases Finset.mem_map.1 ha with ⟨h', hh', hEq⟩
      have hcolor : κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h'⟩) = t :=
        (Finset.mem_filter.1 hh').2
      cases hEq
      exact Finset.mem_filter.2 ⟨by simp, by simp [hcolor]⟩
  -- Replace the Sigma-owner filter by the corresponding fiberwise filtered image.
  rw [hfilter, Finset.card_map]

/-- Helper for Exercise 4.11: the duplicated-column row sum for one color is exactly the original
row dotted with the Sigma-indexed color-count vector used in the final IDP assembly. -/
lemma duplicated_color_row_sum_eq_matrix_mulVec_counts
    {k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (u : Fin n → ℕ)
    (κFin : Fin (Fintype.card (Σ j', Fin (u j'))) → Fin k)
    (i : Fin m)
    (t : Fin k) :
    column_color_sum
        ((A.submatrix id (fun a : Σ j', Fin (u j') ↦ a.1)).reindex
          (Equiv.refl _)
          (Fintype.equivFin (Σ j', Fin (u j'))))
        κFin
        t
        i =
      ∑ j,
        A i j *
          ((Finset.univ.filter fun a : Σ j', Fin (u j') ↦
              κFin (Fintype.equivFin (Σ j', Fin (u j')) a) = t ∧ a.1 = j).card : ℤ) := by
  -- Route correction: package the existing fiberwise regrouping lemma into the Sigma-owner count
  -- vector that the duplicated-column decomposition uses later.
  calc
    column_color_sum
        ((A.submatrix id (fun a : Σ j', Fin (u j') ↦ a.1)).reindex
          (Equiv.refl _)
          (Fintype.equivFin (Σ j', Fin (u j'))))
        κFin
        t
        i =
      ∑ j,
        A i j *
          ((Finset.univ.filter fun h : Fin (u j) ↦
              κFin (Fintype.equivFin (Σ j', Fin (u j')) ⟨j, h⟩) = t).card : ℤ) := by
          simpa using
            duplicated_color_row_sum_eq_sum_mul_duplicate_color_cards A u κFin i t
    _ = ∑ j,
          A i j *
            ((Finset.univ.filter fun a : Σ j', Fin (u j') ↦
                κFin (Fintype.equivFin (Σ j', Fin (u j')) a) = t ∧ a.1 = j).card : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [duplicated_color_card_eq_sigma_owner_filter_card u κFin j t]

/-- Helper for Exercise 4.11: summing the color-sliced row sums over all colors recovers the full
row sum. -/
lemma sumColumnColorSumEqRowSum
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) (i : Fin m) :
    (∑ c : Fin k, column_color_sum A κ c i) = ∑ j : Fin n, A i j := by
  -- Rewrite the filtered color sums as indicator sums and let each column contribute once.
  unfold column_color_sum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp

/-- Helper for Exercise 4.11: an equitable coloring of the duplicated-column presentation packages
the integral point in `kP` into `k` integral feasible summands of `P`. -/
lemma duplicatedColorClassesAsIdpSummands
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    {k : ℕ+}
    {x : Fin n → ℝ}
    (hx : x ∈ (((k : ℕ) : ℝ) • nonnegative_matrix_polyhedron A b) ∩ integerVectors n)
    (hA : A.IsTotallyUnimodular) :
    ∃ y : Fin k → Fin n → ℝ,
      (∀ t : Fin k, y t ∈ nonnegative_matrix_polyhedron A b ∩ integerVectors n) ∧
      x = fun j ↦ ∑ t : Fin k, y t j := by
  classical
  cases' k with k hk
  have exists_integer_point_of_nonempty_integral_set :
      ∀ {Q : Set (Fin n → ℝ)},
        is_integral Q → Q.Nonempty → ∃ y ∈ Q, y ∈ integerVectors n := by
    intro Q hQ hQ_nonempty
    rw [is_integral_iff] at hQ
    have hHull_nonempty :
        (convexHull ℝ (Q ∩ Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z))).Nonempty := by
      rw [← hQ]
      exact hQ_nonempty
    rcases convexHull_nonempty_iff.mp hHull_nonempty with ⟨y, hyQ, hyInt⟩
    exact ⟨y, hyQ, by simpa [integerVectors] using hyInt⟩
  have hdecomp :
      ∀ t : ℕ, ∀ x ∈ ((((t + 1 : ℕ) : ℝ)) • nonnegative_matrix_polyhedron A b ∩ integerVectors n),
        ∃ y : Fin (t + 1) → Fin n → ℝ,
          (∀ s : Fin (t + 1), y s ∈ nonnegative_matrix_polyhedron A b ∩ integerVectors n) ∧
          x = fun j ↦ ∑ s : Fin (t + 1), y s j := by
    intro t
    induction t with
    | zero =>
        intro x hx
        have hxP : x ∈ nonnegative_matrix_polyhedron A b := by
          simpa [one_smul] using hx.1
        refine ⟨fun _ ↦ x, ?_, ?_⟩
        · intro s
          simpa using ⟨hxP, hx.2⟩
        · ext j
          simp
    | succ t ih =>
        intro x hx
        let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
        rcases hx with ⟨⟨xP, hxP, hxEq⟩, hxInt⟩
        rcases mem_integerVectors_iff.mp hxInt with ⟨xz, hxz⟩
        let c : Fin m → ℤ := fun i ↦ (A *ᵥ xz) i - (((t + 1 : ℕ) : ℤ) * b i)
        let Q : Set (Fin n → ℝ) := integer_interval_matrix_polyhedron A c b (fun _ ↦ 0) xz
        have hAxz :
            AReal *ᵥ x = fun i ↦ ((A *ᵥ xz) i : ℝ) := by
          ext i
          rw [hxz]
          simpa [AReal] using (RingHom.map_mulVec (Int.castRingHom ℝ) A xz i).symm
        have hxP_memQ : xP ∈ Q := by
          change xP ∈ integer_interval_matrix_polyhedron A c b (fun _ ↦ 0) xz
          rw [mem_integer_interval_matrix_polyhedron_iff]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i
            have hxPi : (AReal *ᵥ xP) i ≤ (b i : ℝ) :=
              (mem_nonnegative_matrix_polyhedron_iff.mp hxP).1 i
            have hxAx_i : (AReal *ᵥ x) i = ((t + 1 + 1 : ℝ) * (AReal *ᵥ xP) i) := by
              rw [← hxEq]
              simpa [AReal, Matrix.mulVec_smul, Pi.smul_apply]
            have hAxz_i : (AReal *ᵥ x) i = ((A *ᵥ xz) i : ℝ) := by
              simpa using congrArg (fun f : Fin m → ℝ ↦ f i) hAxz
            have hc_i :
                (c i : ℝ) = ((A *ᵥ xz) i : ℝ) - ((t + 1 : ℝ) * (b i : ℝ)) := by
              simp [c, Int.cast_sub, Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]
            change (c i : ℝ) ≤ (AReal *ᵥ xP) i
            rw [hc_i]
            nlinarith
          · intro i
            exact (mem_nonnegative_matrix_polyhedron_iff.mp hxP).1 i
          · intro j
            simpa using (mem_nonnegative_matrix_polyhedron_iff.mp hxP).2 j
          · intro j
            have hxP_nonneg : 0 ≤ xP j := (mem_nonnegative_matrix_polyhedron_iff.mp hxP).2 j
            have hxEqj : x j = ((t + 1 + 1 : ℝ) * xP j) := by
              simpa [Pi.smul_apply, mul_comm] using congrArg (fun f : Fin n → ℝ ↦ f j) hxEq.symm
            have hxzj : x j = (xz j : ℝ) := by
              simpa using congrArg (fun f : Fin n → ℝ ↦ f j) hxz
            nlinarith
        have hQ_integral : is_integral Q := by
          exact
            ((integer_interval_matrix_polyhedron_integral_iff_totally_unimodular A).2 hA)
              c b (fun _ ↦ 0) xz
        rcases
            exists_integer_point_of_nonempty_integral_set
              hQ_integral ⟨xP, hxP_memQ⟩ with
          ⟨y, hyQ, hyInt⟩
        rcases
            (mem_integer_interval_matrix_polyhedron_iff A c b (fun _ ↦ 0) xz y).mp hyQ with
          ⟨hyLower, hyUpper, hyBoxLower, hyBoxUpper⟩
        have hyP : y ∈ nonnegative_matrix_polyhedron A b := by
          rw [mem_nonnegative_matrix_polyhedron_iff]
          refine ⟨?_, ?_⟩
          · intro i
            simpa using hyUpper i
          · intro j
            simpa using hyBoxLower j
        rcases mem_integerVectors_iff.mp hyInt with ⟨yz, hyz⟩
        let zTail : Fin n → ℝ := (1 / ((t + 1 : ℕ) : ℝ)) • (x - y)
        have hzTail_mem : zTail ∈ nonnegative_matrix_polyhedron A b := by
          change AReal *ᵥ zTail ≤ (fun i ↦ (b i : ℝ)) ∧ 0 ≤ zTail
          refine ⟨?_, ?_⟩
          · intro i
            have hyLower_i :
                (((A *ᵥ xz) i : ℝ) - ((t + 1 : ℝ) * (b i : ℝ))) ≤ (AReal *ᵥ y) i := by
              simpa [c, AReal, Int.cast_sub, Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]
                using hyLower i
            have hAx_i : (AReal *ᵥ x) i = ((A *ᵥ xz) i : ℝ) := by
              simpa using congrArg (fun f : Fin m → ℝ ↦ f i) hAxz
            have hsub_i : (AReal *ᵥ (x - y)) i = (AReal *ᵥ x) i - (AReal *ᵥ y) i := by
              simpa using congrArg (fun f : Fin m → ℝ ↦ f i) (Matrix.mulVec_sub AReal x y)
            have hdiff_i : (AReal *ᵥ (x - y)) i ≤ ((t + 1 : ℝ) * (b i : ℝ)) := by
              nlinarith
            have hden_pos : 0 < ((t + 1 : ℕ) : ℝ) := by
              positivity
            have hdiv_i : ((AReal *ᵥ (x - y)) i) / ((t + 1 : ℝ)) ≤ (b i : ℝ) := by
              have hdiv :
                  ((AReal *ᵥ (x - y)) i) / ((t + 1 : ℝ)) ≤
                    (((t + 1 : ℕ) : ℝ) * (b i : ℝ)) / (((t + 1 : ℕ) : ℝ)) := by
                simpa using div_le_div_of_nonneg_right hdiff_i hden_pos.le
              calc
                ((AReal *ᵥ (x - y)) i) / ((t + 1 : ℝ)) ≤
                    (((t + 1 : ℝ) * (b i : ℝ)) / ((t + 1 : ℝ))) := by
                      simpa [Nat.cast_add] using hdiv
                _ = (b i : ℝ) := by
                    field_simp [hden_pos.ne']
            have hzTail_i :
                (AReal *ᵥ zTail) i = ((AReal *ᵥ (x - y)) i) / ((t + 1 : ℝ)) := by
              simpa [zTail, AReal, Matrix.mulVec_smul, Pi.smul_apply, div_eq_mul_inv,
                mul_comm, mul_left_comm, mul_assoc]
                using congrArg (fun f : Fin m → ℝ ↦ f i) (Matrix.mulVec_smul AReal (1 / ((t + 1 : ℕ) : ℝ)) (x - y))
            rw [hzTail_i]
            exact hdiv_i
          · intro j
            have hxzj : x j = (xz j : ℝ) := by
              simpa using congrArg (fun f : Fin n → ℝ ↦ f j) hxz
            have hdiff_nonneg : 0 ≤ (x - y) j := by
              have hyj : y j ≤ (xz j : ℝ) := by
                simpa using hyBoxUpper j
              rw [Pi.sub_apply, hxzj]
              exact sub_nonneg.mpr hyj
            simp [zTail, Pi.smul_apply]
            exact mul_nonneg (by positivity) hdiff_nonneg
        have htail_scaled : x - y ∈ ((((t + 1 : ℕ) : ℝ)) • nonnegative_matrix_polyhedron A b) := by
          refine Set.mem_smul_set.2 ?_
          refine ⟨zTail, hzTail_mem, ?_⟩
          ext j
          have hden_ne : ((t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          simp [zTail, Pi.smul_apply, Pi.sub_apply]
          field_simp [hden_ne]
        have htail_int : x - y ∈ integerVectors n := by
          refine (mem_integerVectors_iff).2 ?_
          refine ⟨fun j ↦ xz j - yz j, ?_⟩
          ext j
          have hxj : x j = (xz j : ℝ) := by
            simpa using congrArg (fun f : Fin n → ℝ ↦ f j) hxz
          have hyj : y j = (yz j : ℝ) := by
            simpa using congrArg (fun f : Fin n → ℝ ↦ f j) hyz
          simp [hxj, hyj, sub_eq_add_neg]
        rcases ih (x - y) ⟨htail_scaled, htail_int⟩ with ⟨z, hz, hsum⟩
        refine ⟨Fin.cases y z, ?_, ?_⟩
        · intro s
          cases s using Fin.cases with
          | zero =>
              simpa using ⟨hyP, hyInt⟩
          | succ s =>
              simpa using hz s
        · ext j
          calc
            x j = y j + (x - y) j := by
              rw [Pi.sub_apply]
              ring
            _ = y j + ∑ s : Fin (t + 1), z s j := by rw [hsum]
            _ = ∑ s : Fin (t + 2), Fin.cases y z s j := by
                simpa [Fin.sum_univ_succ]
  let t : ℕ := k - 1
  have hk_eq : t + 1 = (k : ℕ) := by
    dsimp [t]
    exact Nat.succ_pred_eq_of_pos hk
  have hx' : x ∈ ((((t + 1 : ℕ) : ℝ)) • nonnegative_matrix_polyhedron A b ∩ integerVectors n) := by
    simpa [hk_eq] using hx
  exact
    Eq.ndrec
      (motive := fun k' ↦
        ∃ y : Fin k' → Fin n → ℝ,
          (∀ s : Fin k', y s ∈ nonnegative_matrix_polyhedron A b ∩ integerVectors n) ∧
          x = fun j ↦ ∑ s : Fin k', y s j)
      (hdecomp t x hx')
      hk_eq

/-- Exercise 4.11 (2). If `A` is totally unimodular and `b` is integral, then
`P = {x ∈ ℝ^n_+ | A x ≤ b}` has the integer decomposition property. -/
theorem
    nonnegative_matrix_polyhedron_has_integer_decomposition_property_of_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (hA : A.IsTotallyUnimodular) :
    HasIntegerDecompositionProperty (nonnegative_matrix_polyhedron A b) := by
  intro k x hx
  -- Package the duplicated-column equitable coloring directly into the required IDP summands.
  exact duplicatedColorClassesAsIdpSummands A b hx hA

end Exercise411
