/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1

open scoped Matrix
open scoped IntegerVectorNotation

section Exercise518

variable {m n : ℕ}

/-- `is_largest_abs_square_subdeterminant A Δ` means that `Δ` is the maximum absolute value of the
determinants of the square submatrices of `A`. -/
def is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ) : Prop :=
  (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      |(A.submatrix rows cols).det| ≤ Δ) ∧
    ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      Δ = |(A.submatrix rows cols).det|

/-- Unfolding `is_largest_abs_square_subdeterminant A Δ` gives the stated upper-bound and
attainment conditions on the square subdeterminants of `A`. -/
theorem is_largest_abs_square_subdeterminant_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ) :
    is_largest_abs_square_subdeterminant A Δ ↔
      (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
        |(A.submatrix rows cols).det| ≤ Δ) ∧
        ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
          Δ = |(A.submatrix rows cols).det| :=
  Iff.rfl

/-- Every square subdeterminant of `A` has absolute value at most `Δ` when
`is_largest_abs_square_subdeterminant A Δ` holds. -/
theorem abs_square_subdet_le_of_is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {k : ℕ}
    (rows : Fin k ↪ Fin m)
    (cols : Fin k ↪ Fin n) :
    |(A.submatrix rows cols).det| ≤ Δ :=
  hΔ.1 rows cols

/-- If `Δ` is the largest absolute square subdeterminant of `A`, then some square subdeterminant
of `A` attains the value `Δ`. -/
theorem exists_square_subdeterminant_eq_of_is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      Δ = |(A.submatrix rows cols).det| :=
  hΔ.2

/-- A finite family `rays` represents the extreme rays of `C` when each listed vector generates an
extreme ray of `C`, different indices represent different rays, and every extreme ray of `C` is
same-ray equivalent to one of the listed vectors. -/
def IsExtremeRayRepresentativeFamily
    (C : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin n → ℝ) : Prop :=
  (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
  Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
    ∀ r : Fin n → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t)

/-- Unfolding `IsExtremeRayRepresentativeFamily C rays` gives the source-facing extreme-ray,
pairwise-distinct-ray, and spanning conditions. -/
theorem isExtremeRayRepresentativeFamily_iff
    (C : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin n → ℝ) :
    IsExtremeRayRepresentativeFamily C rays ↔
      (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
        Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
          ∀ r : Fin n → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t) :=
  Iff.rfl

theorem IsExtremeRayRepresentativeFamily.isExtremeRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    (t : Fin q) :
    IsExtremeRayOfCone C (rays t) :=
  hrays.1 t

theorem IsExtremeRayRepresentativeFamily.not_sameRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    {s t : Fin q}
    (hst : s ≠ t) :
    ¬ SameRay ℝ (rays s) (rays t) :=
  hrays.2.1 hst

theorem IsExtremeRayRepresentativeFamily.exists_sameRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    ∃ t : Fin q, SameRay ℝ r (rays t) :=
  hrays.2.2 r hr

/-- Helper for Exercise 5.18: every generator lies in the pointed-cone hull of its singleton. -/
lemma self_mem_singletonRayHull
    (r : Fin n → ℝ) :
    r ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  -- The singleton source set already contains the generator.
  exact PointedCone.subset_hull (by simp : r ∈ ({r} : Set (Fin n → ℝ)))

/-- Helper for Exercise 5.18: an extreme-ray generator belongs to the ambient cone it spans in. -/
lemma extremeRay_mem_of_isExtremeRayOfCone
    {C : Set (Fin n → ℝ)}
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  -- Unpack the extreme-ray predicate and evaluate the extreme-subset axiom at the generator.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  exact hr_edge.isExtreme.1 (self_mem_singletonRayHull r)

/-- Helper for Exercise 5.18: if `Δ` is the largest absolute square subdeterminant of `A`, then
`Δ` is nonnegative. -/
lemma largestAbsSquareSubdeterminant_nonneg
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    0 ≤ Δ := by
  -- Use the attained subdeterminant description and the nonnegativity of absolute values.
  rcases exists_square_subdeterminant_eq_of_is_largest_abs_square_subdeterminant A Δ hΔ with
    ⟨k, rows, cols, hdet⟩
  rw [hdet]
  exact abs_nonneg _

/-- Helper for Exercise 5.18: the largest absolute square subdeterminant bound is at least `1`
because the empty square submatrix has determinant `1`. -/
lemma largestAbsSquareSubdeterminant_one_le
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    1 ≤ Δ := by
  let rows : Fin 0 ↪ Fin m := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  let cols : Fin 0 ↪ Fin n := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  -- Evaluate the universal determinant bound on the `0 × 0` submatrix.
  simpa [rows, cols] using
    abs_square_subdet_le_of_is_largest_abs_square_subdeterminant A Δ hΔ rows cols

/-- Helper for Exercise 5.18: the real coercion of an integer vector belongs to `ℤ^n`. -/
lemma intCastVector_mem_integerVectors
    (z : Fin n → ℤ) :
    (fun i ↦ (z i : ℝ)) ∈ ℤ^n := by
  -- The coercion map itself is the witnessing integer vector.
  exact ⟨z, rfl⟩

/-- Helper for Exercise 5.18: a nonzero integer vector remains nonzero after coercion to `ℝ`. -/
lemma intCastVector_ne_zero
    {z : Fin n → ℤ}
    (hz : z ≠ 0) :
    (fun i ↦ (z i : ℝ)) ≠ 0 := by
  -- Coordinatewise coercion reflects zero because `Int.cast` into `ℝ` is injective.
  intro hcast
  apply hz
  ext i
  have hi : (z i : ℝ) = (0 : ℝ) := by
    simpa using congrFun hcast i
  exact_mod_cast hi

/-- Helper for Exercise 5.18: a nonzero integer vector has a nonzero coordinate. -/
lemma exists_nonzero_coordinate
    (z : Fin n → ℤ)
    (hz : z ≠ 0) :
    ∃ i : Fin n, z i ≠ 0 := by
  by_contra hcoord
  apply hz
  ext i
  by_contra hi
  exact hcoord ⟨i, hi⟩

/-- Helper for Exercise 5.18: the gcd of the coordinate absolute values of a nonzero integer
vector is positive. -/
lemma coordinate_gcd_pos
    (z : Fin n → ℤ)
    (hz : z ≠ 0) :
    0 < Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) := by
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate z hz
  have hg_dvd :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (z j)) ∣ Int.natAbs (z i) := by
    exact Finset.gcd_dvd (by simp)
  have hnatabs_ne : Int.natAbs (z i) ≠ 0 := by
    simpa using hi
  have hg_ne :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (z j)) ≠ 0 := by
    intro hg_zero
    rw [hg_zero] at hg_dvd
    exact hnatabs_ne (by simpa using hg_dvd)
  exact Nat.pos_of_ne_zero hg_ne

/-- Helper for Exercise 5.18: coercing a natural-valued family into `ℤ` commutes with
`Finset.gcd`. -/
lemma finset_gcd_int_cast_eq_nat_gcd
    (s : Finset (Fin n))
    (f : Fin n → ℕ) :
    s.gcd (fun i ↦ (f i : ℤ)) = ((Finset.gcd s f : ℕ) : ℤ) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.gcd_insert, Finset.gcd_insert, hs]
    exact congrArg (fun z : ℕ ↦ (z : ℤ)) (Int.gcd_natCast_natCast (f a) (Finset.gcd s f))

/-- Helper for Exercise 5.18: the integer gcd of coordinate absolute values is the coercion of
their natural gcd. -/
lemma coordinate_gcd_int_cast_eq_nat_gcd_natAbs
    (z : Fin n → ℤ) :
    Finset.univ.gcd (fun i : Fin n ↦ ((z i).natAbs : ℤ)) =
      ((Finset.gcd Finset.univ (fun i : Fin n ↦ Int.natAbs (z i)) : ℕ) : ℤ) := by
  simpa using
    finset_gcd_int_cast_eq_nat_gcd (n := n) Finset.univ (fun i : Fin n ↦ Int.natAbs (z i))

/-- Helper for Exercise 5.18: dividing a nonzero integer vector by the gcd of its coordinates
produces a primitive vector. -/
lemma normalized_split_vector_gcd_eq_one
    (z : Fin n → ℤ)
    (hz : z ≠ 0) :
    Finset.univ.gcd
        (fun i : Fin n ↦
          Int.natAbs (z i / Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (z j)))) = 1 := by
  set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) with hgN
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate z hz
  have hg_dvd : ∀ j : Fin n, (gN : ℤ) ∣ z j := by
    intro j
    rw [Int.natCast_dvd]
    simpa [hgN] using (Finset.gcd_dvd (b := j) (f := fun k : Fin n ↦ Int.natAbs (z k)) (by simp))
  have hgcd_one :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (z j) / gN) = 1 := by
    exact Finset.gcd_div_eq_one (i := i) (by simp) (by simpa using hi)
  refine (Finset.gcd_congr rfl ?_).trans hgcd_one
  intro j hj
  rw [Int.natAbs_ediv_of_dvd (hg_dvd j)]
  simp

/-- Helper for Exercise 5.18: a nonzero point of the nonnegative kernel cone has a positive
coordinate. -/
lemma exists_positive_coordinate_of_mem_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {x : Fin n → ℝ}
    (hx : x ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hx_ne : x ≠ 0) :
    ∃ j : Fin n, 0 < x j := by
  -- Only the coordinatewise nonnegativity part is needed to upgrade a nonzero coordinate to
  -- a positive one.
  have hx_nonneg : 0 ≤ x := (mem_standard_equality_form_iff.mp hx).2
  by_contra hpos
  apply hx_ne
  ext j
  by_cases hj : x j = 0
  · exact hj
  · have hzero_ne : (0 : ℝ) ≠ x j := by
      intro h0
      exact hj h0.symm
    have hxj_pos : 0 < x j := lt_of_le_of_ne (hx_nonneg j) hzero_ne
    exact False.elim (hpos ⟨j, hxj_pos⟩)

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone has a positive
coordinate. -/
lemma exists_positive_coordinate_of_extremeRay_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ j : Fin n, 0 < r j := by
  -- First place the extreme generator in the cone, then apply the previous nonzero-vector lemma.
  have hr_mem :
      r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 :=
    extremeRay_mem_of_isExtremeRayOfCone hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  exact exists_positive_coordinate_of_mem_nonnegative_kernel_cone A hr_mem hr_ne

/-- Helper for Exercise 5.18: for a nonnegative integer vector, the integer coordinate gcd is `1`
whenever the gcd of the coordinate absolute values is `1`. -/
lemma intGcd_eq_one_of_nonnegative_primitive
    {z : Fin n → ℤ}
    (hz_nonneg : ∀ i : Fin n, 0 ≤ z i)
    (hz_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1) :
    Finset.univ.gcd (fun i : Fin n ↦ z i) = 1 := by
  -- Rewrite the integer gcd through the nonnegative-coordinate normal form `z i = |z i|`.
  calc
    Finset.univ.gcd (fun i : Fin n ↦ z i)
      = Finset.univ.gcd (fun i : Fin n ↦ ((z i).natAbs : ℤ)) := by
          refine Finset.gcd_congr rfl ?_
          intro i hi
          rw [← Int.eq_natAbs_of_nonneg (hz_nonneg i)]
    _ = ((Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) : ℕ) : ℤ) := by
          exact coordinate_gcd_int_cast_eq_nat_gcd_natAbs z
    _ = 1 := by
          norm_num [hz_primitive]

/-- Helper for Exercise 5.18: primitive nonnegative integer generators on the same ray are equal.
This is the uniqueness step used to turn the finite primitive box into a representative family. -/
lemma eq_of_sameRay_of_nonnegative_primitiveGenerators
    {z w : Fin n → ℤ}
    (hz_ne : z ≠ 0)
    (hw_ne : w ≠ 0)
    (hz_nonneg : ∀ i : Fin n, 0 ≤ z i)
    (hw_nonneg : ∀ i : Fin n, 0 ≤ w i)
    (hz_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1)
    (hw_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (w i)) = 1)
    (hsame : SameRay ℝ (fun i ↦ (z i : ℝ)) (fun i ↦ (w i : ℝ))) :
    z = w := by
  -- Convert the primitive natAbs hypotheses to integer gcd statements usable by Bézout.
  have hz_gcd_int : Finset.univ.gcd (fun i : Fin n ↦ z i) = 1 :=
    intGcd_eq_one_of_nonnegative_primitive hz_nonneg hz_primitive
  have hw_gcd_int : Finset.univ.gcd (fun i : Fin n ↦ w i) = 1 :=
    intGcd_eq_one_of_nonnegative_primitive hw_nonneg hw_primitive
  have hz_cast_ne : (fun i ↦ (z i : ℝ)) ≠ 0 := intCastVector_ne_zero hz_ne
  have hw_cast_ne : (fun i ↦ (w i : ℝ)) ≠ 0 := intCastVector_ne_zero hw_ne
  obtain ⟨α, hα_pos, hα⟩ := hsame.exists_pos_left hz_cast_ne hw_cast_ne
  have hα_coord : ∀ i : Fin n, α * (z i : ℝ) = (w i : ℝ) := by
    -- Evaluate the same-ray scaling identity coordinatewise.
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hα i
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun i : Fin n ↦ z i)
  have hc_real : (1 : ℝ) =
      Finset.sum Finset.univ (fun i : Fin n ↦ (z i : ℝ) * (c i : ℝ)) := by
    -- Cast the Bézout identity from `ℤ` to `ℝ`.
    have hc_int : (1 : ℤ) = Finset.sum Finset.univ (fun i : Fin n ↦ z i * c i) := by
      simpa [hz_gcd_int] using hc
    exact_mod_cast hc_int
  let k : ℤ := Finset.sum Finset.univ (fun i : Fin n ↦ w i * c i)
  have hk_cast : (k : ℝ) = α := by
    -- Re-express `α` through the Bézout relation, showing that the same-ray scalar is integral.
    calc
      (k : ℝ) = Finset.sum Finset.univ (fun i : Fin n ↦ (w i : ℝ) * (c i : ℝ)) := by
        simp [k]
      _ = Finset.sum Finset.univ (fun i : Fin n ↦ (α * (z i : ℝ)) * (c i : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hα_coord i]
      _ = α * Finset.sum Finset.univ (fun i : Fin n ↦ (z i : ℝ) * (c i : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = α * 1 := by
        rw [hc_real]
      _ = α := by
        ring
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by
    simpa [hk_cast] using hα_pos
  have hk_pos : 0 < k := by
    exact_mod_cast hk_pos_real
  have hk_mul_coord : ∀ i : Fin n, k * z i = w i := by
    -- Replace the real same-ray scalar with its integral value on each coordinate.
    intro i
    have hi_real : (k : ℝ) * (z i : ℝ) = (w i : ℝ) := by
      simpa [hk_cast] using hα_coord i
    exact_mod_cast hi_real
  have hk_dvd_w : k ∣ Finset.univ.gcd (fun i : Fin n ↦ w i) := by
    -- Every coordinate of `w` is a multiple of `k`, so the gcd is also a multiple of `k`.
    refine Finset.dvd_gcd ?_
    intro i hi
    exact ⟨z i, (hk_mul_coord i).symm⟩
  have hk_dvd_one : k ∣ (1 : ℤ) := by
    simpa [hw_gcd_int] using hk_dvd_w
  have hk_eq_one : k = 1 := by
    exact Int.eq_one_of_dvd_one hk_pos.le hk_dvd_one
  -- Substituting the forced scalar `k = 1` identifies the two primitive generators.
  ext i
  calc
    z i = 1 * z i := by ring
    _ = k * z i := by rw [hk_eq_one]
    _ = w i := hk_mul_coord i

/-- Helper for Exercise 5.18: stack the equalities `A x = 0` and the nonnegativity constraints
`x ≥ 0` into one polyhedral inequality matrix. -/
def nonnegativeKernelConstraintMatrix
    (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin ((m + m) + n)) (Fin n) ℤ :=
  let equalities : Matrix (Fin (m + m)) (Fin n) ℤ :=
    (Matrix.fromRows A (-A)).reindex finSumFinEquiv (Equiv.refl _)
  (Matrix.fromRows equalities (-(1 : Matrix (Fin n) (Fin n) ℤ))).reindex
    finSumFinEquiv (Equiv.refl _)

/-- Helper for Exercise 5.18: membership in the stacked inequality owner is exactly membership in
the nonnegative kernel cone `standard_equality_form (A.map _) 0`. -/
lemma mem_nonnegativeKernelConstraintPolyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) ↔
      x ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 := by
  rw [mem_polyhedron_le_set_iff, mem_standard_equality_form_iff]
  constructor
  · intro hx
    constructor
    · ext i
      -- The paired `A` and `-A` rows force every equality row to vanish.
      have hi_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.castAdd n (Fin.castAdd m i)) ≤ 0 := hx (Fin.castAdd n (Fin.castAdd m i))
      have hi_neg_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.castAdd n (Fin.natAdd m i)) ≤ 0 := hx (Fin.castAdd n (Fin.natAdd m i))
      have hAi_le : ((A.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ 0 := by
        simpa [nonnegativeKernelConstraintMatrix, Matrix.mulVec, dotProduct] using hi_le
      have hAi_ge : 0 ≤ ((A.map (Int.castRingHom ℝ)) *ᵥ x) i := by
        have hneg_row :
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                (Fin.castAdd n (Fin.natAdd m i)) =
              -((A.map (Int.castRingHom ℝ)) *ᵥ x) i := by
          have hrow_matrix :
              ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
                  (Fin.castAdd n (Fin.natAdd m i)) =
                ((-A).map (Int.castRingHom ℝ)) i := by
            have houter :
                finSumFinEquiv.symm (Fin.castAdd n (Fin.natAdd m i)) =
                  Sum.inl (i.addNat m) := by
              apply finSumFinEquiv.injective
              simp
            have hinner :
                finSumFinEquiv.symm (i.addNat m) = Sum.inr i := by
              apply finSumFinEquiv.injective
              simp
            ext j
            simpa [nonnegativeKernelConstraintMatrix, houter, hinner]
          have hrow_eq :
              (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                  (Fin.castAdd n (Fin.natAdd m i)) =
                (((-A).map (Int.castRingHom ℝ)) *ᵥ x) i := by
            simpa [Matrix.mulVec, dotProduct] using
              congrArg (fun row : Fin n → ℝ ↦ dotProduct row x) hrow_matrix
          have hneg_map :
              ((-A).map (Int.castRingHom ℝ)) = -(A.map (Int.castRingHom ℝ)) := by
            ext j k
            simp
          calc
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                (Fin.castAdd n (Fin.natAdd m i))
                = (((-A).map (Int.castRingHom ℝ)) *ᵥ x) i := hrow_eq
            _ = ((-(A.map (Int.castRingHom ℝ))) *ᵥ x) i := by rw [hneg_map]
            _ = -((A.map (Int.castRingHom ℝ)) *ᵥ x) i := by
                  simpa using congrFun (Matrix.neg_mulVec x (A.map (Int.castRingHom ℝ))) i
        have hneg : -((A.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ 0 := by
          rw [← hneg_row]
          exact hi_neg_le
        linarith
      exact le_antisymm hAi_le hAi_ge
    · intro j
      -- The `-I` block is equivalent to coordinatewise nonnegativity.
      have hj_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.natAdd (m + m) j) ≤ 0 := hx (Fin.natAdd (m + m) j)
      have hnegx : -x j ≤ 0 := by
        have hneg_coord :
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                (Fin.natAdd (m + m) j) = -x j := by
          have hcoord_matrix :
              ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
                  (Fin.natAdd (m + m) j) =
                -((1 : Matrix (Fin n) (Fin n) ℝ)) j := by
            have houter :
                finSumFinEquiv.symm (Fin.natAdd (m + m) j) = Sum.inr j := by
              apply finSumFinEquiv.injective
              simp
            ext k
            by_cases hjk : j = k
            · subst hjk
              simp [nonnegativeKernelConstraintMatrix, houter]
            · simp [nonnegativeKernelConstraintMatrix, houter, Matrix.one_apply, hjk]
          have hcoord_eq :
              (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                  (Fin.natAdd (m + m) j) =
                -(((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) j) := by
            simpa [Matrix.mulVec, dotProduct] using
              congrArg (fun row : Fin n → ℝ ↦ dotProduct row x) hcoord_matrix
          calc
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
                (Fin.natAdd (m + m) j)
                = -((((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)) *ᵥ x) j) := by
                    simpa using hcoord_eq
            _ = -x j := by
                  simpa using congrArg Neg.neg (congrFun (Matrix.one_mulVec x) j)
        rw [hneg_coord] at hj_le
        exact hj_le
      have hxj_nonneg : 0 ≤ x j := by
        linarith
      exact hxj_nonneg
  · rintro ⟨hx_eq, hx_nonneg⟩ i
    -- Split the stacked system into an `A` row, a `-A` row, or a `-I` row.
    cases houter : finSumFinEquiv.symm i with
    | inl r =>
        cases hinner : finSumFinEquiv.symm r with
        | inl iA =>
            have hAi : ((A.map (Int.castRingHom ℝ)) *ᵥ x) iA = 0 := by
              simpa using congrFun hx_eq iA
            simpa [nonnegativeKernelConstraintMatrix, houter, hinner, Matrix.mulVec, dotProduct]
              using hAi.le
        | inr iNegA =>
            have hAi : ((A.map (Int.castRingHom ℝ)) *ᵥ x) iNegA = 0 := by
              simpa using congrFun hx_eq iNegA
            have hnegAi : -((A.map (Int.castRingHom ℝ)) *ᵥ x) iNegA ≤ 0 := by
              linarith
            simpa [nonnegativeKernelConstraintMatrix, houter, hinner, Matrix.mulVec, dotProduct]
              using hnegAi
    | inr j =>
        have hnegx : -x j ≤ 0 := by
          have hxj_nonneg : 0 ≤ x j := hx_nonneg j
          linarith
        have hneg_coord :
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x) i = -x j := by
          have hcoord_matrix :
              ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) i =
                -((1 : Matrix (Fin n) (Fin n) ℝ)) j := by
            ext k
            by_cases hjk : j = k
            · subst hjk
              simp [nonnegativeKernelConstraintMatrix, houter]
            · simp [nonnegativeKernelConstraintMatrix, houter, Matrix.one_apply, hjk]
          have hcoord_eq :
              (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x) i =
                -(((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) j) := by
            simpa [Matrix.mulVec, dotProduct] using
              congrArg (fun row : Fin n → ℝ ↦ dotProduct row x) hcoord_matrix
          calc
            (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x) i
                = -((((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)) *ᵥ x) j) := by
                    simpa using hcoord_eq
            _ = -x j := by
                  simpa using congrArg Neg.neg (congrFun (Matrix.one_mulVec x) j)
        rw [hneg_coord]
        exact hnegx

/-- Helper for Exercise 5.18: the nonnegative kernel cone is exactly the stacked polyhedron
defined by `nonnegativeKernelConstraintMatrix A`. -/
lemma standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) :
    standard_equality_form (A.map (Int.castRingHom ℝ)) 0 =
      polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
  ext x
  simpa using (mem_nonnegativeKernelConstraintPolyhedron_iff A (x := x)).symm

/-- Helper for Exercise 5.18: the nonnegative kernel cone is pointed because a lineality
direction would have to be both coordinatewise nonnegative and coordinatewise nonpositive. -/
lemma nonnegativeKernelConstraintPolyhedron_pointed
    (A : Matrix (Fin m) (Fin n) ℤ) :
    is_pointed
      (polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  have hzero_mem :
      (0 : Fin n → ℝ) ∈
        polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    exact (mem_nonnegativeKernelConstraintPolyhedron_iff A (x := 0)).2 (by
      simp [mem_standard_equality_form_iff])
  have hd_mem :
      d ∈ polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (1 : ℝ)
  have hnegd_mem :
      -d ∈ polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (-1 : ℝ)
  have hd_nonneg :
      0 ≤ d := (mem_standard_equality_form_iff.mp
        ((standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A).symm ▸ hd_mem)).2
  have hnegd_nonneg :
      0 ≤ -d := (mem_standard_equality_form_iff.mp
        ((standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A).symm ▸ hnegd_mem)).2
  ext j
  have hj_nonpos : d j ≤ 0 := by
    simpa using hnegd_nonneg j
  exact le_antisymm hj_nonpos (hd_nonneg j)

/-- Helper for Exercise 5.18: the stacked polyhedral owner has itself as recession cone because
its right-hand side is zero. -/
lemma recessionCone_polyhedron_eq_matrix_polyhedral_cone
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    recessionCone (polyhedron_le_set A b) = matrix_polyhedral_cone A := by
  -- Rewrite both sides to the same homogeneous rowwise inequality system.
  ext x
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
  rw [mem_matrix_polyhedral_cone]
  rfl

/-- Helper for Exercise 5.18: the common zero set of `n - 1` active independent rows is the line
spanned by the extreme-ray generator. -/
lemma mem_span_singleton_of_selected_rows_zero
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r s : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hs_zero : ∀ i : Fin (n - 1), (A *ᵥ s) (I i) = 0) :
    s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) := by
  have hn_pos : 0 < n := by
    -- A nonzero vector cannot live in the zero-dimensional ambient space.
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hr_ne_zero
    ext i
    exact Fin.elim0 i
  let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
  have hB_rows : LinearIndependent ℝ B.row := by
    -- The selected rows of `A` are exactly the rows of the rectangular selected matrix.
    simpa [B, Matrix.row] using hI_linearIndependent
  have hB_rank : B.rank = n - 1 := by
    -- Full row rank records the independence of the chosen active rows.
    simpa [B] using LinearIndependent.rank_matrix hB_rows
  have hker_finrank : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    calc
      Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n - B.rank := by
        simpa using finrank_matrix_kernel_eq_ambient_sub_rank B
      _ = n - (n - 1) := by rw [hB_rank]
      _ = 1 := by omega
  have hr_ker : r ∈ LinearMap.ker B.mulVecLin := by
    -- The extreme-ray generator satisfies the selected active equations.
    change B *ᵥ r = 0
    ext i
    simpa [B, Matrix.mulVec] using hI_active i
  have hs_ker : s ∈ LinearMap.ker B.mulVecLin := by
    -- The comparison vector satisfies the same selected-row equations.
    change B *ᵥ s = 0
    ext i
    simpa [B, Matrix.mulVec] using hs_zero i
  have hr_sub_ne_zero : (⟨r, hr_ker⟩ : LinearMap.ker B.mulVecLin) ≠ 0 := by
    -- Passing to the kernel subtype does not create a new zero vector.
    intro hzero
    apply hr_ne_zero
    exact congrArg Subtype.val hzero
  obtain ⟨μ, hμ⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (V := LinearMap.ker B.mulVecLin) hker_finrank
      (x := ⟨r, hr_ker⟩) hr_sub_ne_zero ⟨s, hs_ker⟩
  -- Convert the one-dimensional kernel relation back to the ambient space.
  exact Submodule.mem_span_singleton.mpr ⟨μ, by simpa using congrArg Subtype.val hμ⟩

lemma recessionCone_eq_nonnegativeKernelConstraintPolyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) :
    recessionCone
        (polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) =
      polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
  have hnonempty :
      (polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))).Nonempty := by
    refine ⟨0, ?_⟩
    exact (mem_nonnegativeKernelConstraintPolyhedron_iff A (x := 0)).2 (by
      simp [mem_standard_equality_form_iff])
  rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)))
      (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
      hnonempty]
  ext x
  rw [mem_matrix_polyhedral_cone, mem_polyhedron_le_set_iff]
  rfl

/-- Helper for Exercise 5.18: augment a homogeneous system `A *ᵥ x ≤ 0` with two slice rows that
fix one coordinate `x j = r j`. -/
def coneCoordinateSliceMatrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    Matrix (Fin (m + 2)) (Fin n) ℝ :=
  fun i ↦
    Fin.cases
      (Pi.single j (1 : ℝ))
      (fun i' ↦ Fin.cases (Pi.single j (-1 : ℝ)) (fun i'' ↦ A i'') i')
      i

/-- Helper for Exercise 5.18: right-hand side for the coordinate slice through `r`. -/
def coneCoordinateSliceRhs
    {m n : ℕ}
    (r : Fin n → ℝ)
    (j : Fin n) :
    Fin (m + 2) → ℝ :=
  fun i ↦
    Fin.cases (r j)
      (fun i' ↦ Fin.cases (-r j) (fun _ ↦ (0 : ℝ)) i')
      i

/-- Helper for Exercise 5.18: every non-auxiliary slice row is an original row of `A`. -/
lemma coneCoordinateSliceMatrix_tail_row
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n)
    (i : Fin m) :
    coneCoordinateSliceMatrix A j i.succ.succ = A i := by
  ext k
  simp [coneCoordinateSliceMatrix]

/-- Helper for Exercise 5.18: every non-auxiliary slice right-hand-side entry is `0`. -/
lemma coneCoordinateSliceRhs_tail_row
    {m n : ℕ}
    (r : Fin n → ℝ)
    (j : Fin n)
    (i : Fin m) :
    coneCoordinateSliceRhs r j i.succ.succ = 0 := by
  simp [coneCoordinateSliceRhs]

/-- Helper for Exercise 5.18: a slice-row index distinct from the two auxiliary rows must come
from the original tail block. -/
lemma exists_tail_index_of_ne_auxiliary_slice_row
    {m : ℕ}
    {p : Fin (m + 2)}
    (hp0 : p ≠ 0)
    (hp1 : p ≠ 1) :
    ∃ i : Fin m, p = i.succ.succ := by
  rcases p with ⟨k, hk⟩
  cases k with
  | zero =>
      exact False.elim (hp0 rfl)
  | succ k =>
      cases k with
      | zero =>
          exact False.elim (hp1 rfl)
      | succ k =>
          refine ⟨⟨k, by omega⟩, rfl⟩

/-- Helper for Exercise 5.18: the two auxiliary slice rows are negatives of each other, so they
cannot both appear in a linearly independent family. -/
lemma not_linearIndependent_auxiliary_slice_rows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    ¬ LinearIndependent ℝ
      (![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1] :
        Fin 2 → Fin n → ℝ) := by
  intro hlin
  have hrow0 : coneCoordinateSliceMatrix A j 0 = Pi.single j (1 : ℝ) := rfl
  have hrow1 : coneCoordinateSliceMatrix A j 1 = Pi.single j (-1 : ℝ) := rfl
  have hsum :
      ∑ i : Fin 2,
          ((![1, 1] : Fin 2 → ℝ) i) •
            (![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1] :
              Fin 2 → Fin n → ℝ) i = 0 := by
    ext k
    rw [Fin.sum_univ_two]
    by_cases hk : k = j
    · subst hk
      simp [hrow0, hrow1, Pi.single_apply]
    · simp [hrow0, hrow1, Pi.single_apply, hk]
  have hcoeff_zero :=
    (Fintype.linearIndependent_iff.mp hlin) (![1, 1] : Fin 2 → ℝ) hsum
  have h0 : ((![1, 1] : Fin 2 → ℝ) 0) = 0 := hcoeff_zero 0
  norm_num at h0

/-- Helper for Exercise 5.18: membership in the coordinate slice is exactly membership in the
matrix cone together with the fixed-coordinate equation `x j = r j`. -/
lemma mem_coneCoordinateSlice_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ)
    (j : Fin n)
    {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j) ↔
      x ∈ matrix_polyhedral_cone A ∧ x j = r j := by
  have hrow0 : coneCoordinateSliceMatrix A j 0 = Pi.single j (1 : ℝ) := rfl
  have hrow1 : coneCoordinateSliceMatrix A j 1 = Pi.single j (-1 : ℝ) := rfl
  have hrhs0 : coneCoordinateSliceRhs r j (0 : Fin (m + 2)) = r j := by
    simp [coneCoordinateSliceRhs]
  have hrhs1 : coneCoordinateSliceRhs r j (1 : Fin (m + 2)) = -r j := by
    cases m <;> rfl
  rw [mem_polyhedron_le_set_iff, mem_matrix_polyhedral_cone]
  constructor
  · intro hx
    constructor
    · intro i
      simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
        using hx i.succ.succ
    · have hleft : x j ≤ r j := by
        have hleft_raw :
            (coneCoordinateSliceMatrix A j *ᵥ x) 0 ≤ coneCoordinateSliceRhs r j 0 := hx 0
        change (coneCoordinateSliceMatrix A j 0) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 0 at hleft_raw
        rw [hrow0, hrhs0, dotProduct] at hleft_raw
        simpa [Pi.single_apply] using hleft_raw
      have hright : -x j ≤ -r j := by
        have hright_raw :
            (coneCoordinateSliceMatrix A j *ᵥ x) 1 ≤ coneCoordinateSliceRhs r j 1 := hx 1
        change (coneCoordinateSliceMatrix A j 1) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 1 at hright_raw
        rw [hrow1, hrhs1, dotProduct] at hright_raw
        simpa [Pi.single_apply] using hright_raw
      linarith
  · rintro ⟨hx_cone, hxj⟩
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      change (coneCoordinateSliceMatrix A j 0) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 0
      rw [hrow0, hrhs0, dotProduct]
      simpa [Pi.single_apply, hxj]
    · by_cases hi1 : i = 1
      · subst hi1
        change (coneCoordinateSliceMatrix A j 1) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 1
        rw [hrow1, hrhs1, dotProduct]
        simpa [Pi.single_apply, hxj]
      · rcases exists_tail_index_of_ne_auxiliary_slice_row hi0 hi1 with ⟨i', rfl⟩
        simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
          using hx_cone i'

/-- Helper for Exercise 5.18: an extreme ray generator belongs to its coordinate slice. -/
lemma extremeRay_mem_coneCoordinateSlice
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (j : Fin n) :
    r ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j) := by
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem_recession : r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singletonRayHull r)
  rw [mem_coneCoordinateSlice_iff]
  constructor
  · rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty] at hr_mem_recession
    exact hr_mem_recession
  · rfl

/-- Helper for Exercise 5.18: inside a coordinate slice, any point on the singleton ray through
`r` must equal `r` once the chosen coordinate is nonzero. -/
lemma eq_of_mem_coneCoordinateSlice_and_mem_singletonRayHull
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r x : Fin n → ℝ}
    (j : Fin n)
    (hrj : r j ≠ 0)
    (hx_slice :
      x ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j))
    (hx_ray : x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    x = r := by
  rcases mem_singletonRayHull_iff.mp hx_ray with ⟨μ, hμ, rfl⟩
  have hcoord : μ * r j = r j := by
    simpa using (mem_coneCoordinateSlice_iff A r j).mp hx_slice |>.2
  have hmu_eq : μ = 1 := by
    have hmul_zero : (μ - 1) * r j = 0 := by
      linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul_zero).resolve_right hrj))
  simp [hmu_eq]

/-- Helper for Exercise 5.18: an extreme point of `polyhedron_le_set A b` is cut out by `n`
active linearly independent rows. -/
lemma exists_active_linearlyIndependent_rows_of_extremePoint
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_extreme : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
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
        simpa [hφAi] using congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) ↦ f (A i)) hφr
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
      · simpa [h1]
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
        · have hσ_bound : |σ| ≤ (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by
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
      have hneg : |(-ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xMinus, sub_eq_add_neg] using (hperturb_mem (σ := -ε) hneg)
    have hxPlus : xPlus ∈ polyhedron_le_set A b := by
      have hpos : |(ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
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
    have hxext := (mem_extremePoints_iff_left).mp hxbar_extreme
    exact hxMinus_ne (hxext.2 xMinus hxMinus xPlus hxPlus hxbar_open)
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ activeRows) = n := by
    rw [hspan]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
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
      _ = A (chosen j).1 := by simpa [hij]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    exact (chosen i).2
  · have hrows :
        (fun i : Fin n ↦ A (I i)) = rows := by
        funext i
        exact hchosen_row i
    simpa [hrows] using hrows_linear

/-- Helper for Exercise 5.18: the coordinate slice turns an extreme recession ray into an extreme
point because every slice segment through `r` stays on the singleton ray. -/
lemma coneCoordinateSliceExtremePoint
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (j : Fin n)
    (hrj : r j ≠ 0) :
    r ∈ (polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j)).extremePoints
      ℝ := by
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  refine (mem_extremePoints_iff_left).2 ?_
  constructor
  · exact extremeRay_mem_coneCoordinateSlice A b hP_nonempty hr j
  · intro x hx y hy hr_open
    have hx_recession : x ∈ recessionCone (polyhedron_le_set A b) := by
      rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty]
      exact (mem_coneCoordinateSlice_iff A r j).mp hx |>.1
    have hy_recession : y ∈ recessionCone (polyhedron_le_set A b) := by
      rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty]
      exact (mem_coneCoordinateSlice_iff A r j).mp hy |>.1
    have hx_ray :
        x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
      hr_edge.isExtreme.left_mem_of_mem_openSegment
        hx_recession hy_recession (self_mem_singletonRayHull r) hr_open
    exact eq_of_mem_coneCoordinateSlice_and_mem_singletonRayHull A j hrj hx hx_ray

/-- Helper for Exercise 5.18: `n` linearly independent rows of `ℝ^n` annihilate only the zero
vector. -/
lemma eq_zero_of_linearIndependent_rows_annihilate
    {n : ℕ}
    {rows : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hrows : LinearIndependent ℝ rows)
    (hann : ∀ i : Fin n, rows i ⬝ᵥ x = 0) :
    x = 0 := by
  by_cases hn : n = 0
  · subst hn
    ext i
    exact Fin.elim0 i
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hspan : Submodule.span ℝ (Set.range rows) = ⊤ := by
      exact
        hrows.span_eq_top_of_card_eq_finrank
          (by simpa using (Module.finrank_fin_fun ℝ (n := n)).symm)
    have hdot_zero :
        ∀ v ∈ Submodule.span ℝ (Set.range rows), v ⬝ᵥ x = 0 := by
      intro v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hann i
      · simp
      · intro u w _ _ hu_zero hw_zero
        rw [add_dotProduct, hu_zero, hw_zero]
        simp
      · intro a v _ hv_zero
        rw [smul_dotProduct, hv_zero]
        simp
    ext i
    have hi_mem : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (Set.range rows) := by
      rw [hspan]
      exact Submodule.mem_top
    have hi_dot : (Pi.single i (1 : ℝ)) ⬝ᵥ x = 0 := hdot_zero (Pi.single i (1 : ℝ)) hi_mem
    have hi_single : (Pi.single i (1 : ℝ)) ⬝ᵥ x = x i := by
      rw [dotProduct, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    exact hi_single.symm.trans hi_dot

/-- Helper for Exercise 5.18: deleting the unique auxiliary slice row leaves `n - 1` original
rows that annihilate `r` and remain linearly independent. -/
lemma coordinateSliceActiveRowsDropToOriginalRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r : Fin n → ℝ}
    (j : Fin n)
    (hrj : r j ≠ 0)
    (J : Fin n ↪ Fin (m + 2))
    (hJ_active :
      ∀ i : Fin n,
        (coneCoordinateSliceMatrix A j *ᵥ r) (J i) = coneCoordinateSliceRhs r j (J i))
    (hJ_linearIndependent :
      LinearIndependent ℝ (fun i : Fin n ↦ coneCoordinateSliceMatrix A j (J i))) :
    ∃ I : Fin (n - 1) ↪ Fin m,
      (∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0) ∧
        LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  have haux_exists : ∃ kAux : Fin n, J kAux = 0 ∨ J kAux = 1 := by
    by_contra haux
    have hJ_nonaux : ∀ k : Fin n, J k ≠ 0 ∧ J k ≠ 1 := by
      intro k
      constructor
      · intro h0
        exact haux ⟨k, Or.inl h0⟩
      · intro h1
        exact haux ⟨k, Or.inr h1⟩
    let tail : Fin n → Fin m := fun k ↦
      Classical.choose
        (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_eq : ∀ k : Fin n, J k = (tail k).succ.succ := by
      intro k
      exact
        Classical.choose_spec
          (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_active : ∀ k : Fin n, (A *ᵥ r) (tail k) = 0 := by
      intro k
      have hk := hJ_active k
      rw [htail_eq k] at hk
      simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
        using hk
    have htail_linearIndependent : LinearIndependent ℝ (fun k : Fin n ↦ A (tail k)) := by
      simpa [htail_eq, coneCoordinateSliceMatrix_tail_row] using hJ_linearIndependent
    have hr_zero : r = 0 := by
      apply eq_zero_of_linearIndependent_rows_annihilate htail_linearIndependent
      intro k
      simpa [Matrix.mulVec, dotProduct] using htail_active k
    exact hrj (by simpa [hr_zero])
  obtain ⟨kAux, hkAux⟩ := haux_exists
  have hno_two_aux :
      ∀ {a b : Fin n}, a ≠ b → J a = 0 → J b = 1 → False := by
    intro a b hab hJa hJb
    let e : Fin 2 → Fin n := ![a, b]
    have he_inj : Function.Injective e := by
      intro u v huv
      fin_cases u <;> fin_cases v
      · rfl
      · have : a = b := by simpa [e] using huv
        exact False.elim (hab this)
      · have : a = b := by simpa [e] using huv.symm
        exact False.elim (hab this)
      · rfl
    have hpair_linearIndependent :
        LinearIndependent ℝ
          (fun t : Fin 2 ↦ coneCoordinateSliceMatrix A j (J (e t))) :=
      hJ_linearIndependent.comp e he_inj
    let pairRows : Fin 2 → Fin n → ℝ :=
      ![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1]
    have hpair_eq :
        (fun t : Fin 2 ↦ coneCoordinateSliceMatrix A j (J (e t))) = pairRows := by
      funext t
      fin_cases t <;> simp [pairRows, e, hJa, hJb]
    have hpair_linearIndependent' :
        LinearIndependent ℝ (fun t : Fin 2 ↦ pairRows t) := by
      simpa [hpair_eq] using hpair_linearIndependent
    exact not_linearIndependent_auxiliary_slice_rows A j hpair_linearIndependent'
  have hother_nonaux :
      ∀ {k : Fin n}, k ≠ kAux → J k ≠ 0 ∧ J k ≠ 1 := by
    intro k hk
    constructor
    · intro hk0
      cases hkAux with
      | inl hkAux0 =>
          exact hk (J.injective (hk0.trans hkAux0.symm))
      | inr hkAux1 =>
          exact False.elim (hno_two_aux hk hk0 hkAux1)
    · intro hk1
      cases hkAux with
      | inl hkAux0 =>
          have hkAux_ne_k : kAux ≠ k := fun h => hk h.symm
          exact False.elim (hno_two_aux hkAux_ne_k hkAux0 hk1)
      | inr hkAux1 =>
          exact hk (J.injective (hk1.trans hkAux1.symm))
  have hn_cast : (n - 1) + 1 = n := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt kAux.is_lt))
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm kAux
  let skip : Fin (n - 1) → Fin n := fun i ↦ Fin.cast hn_cast (pivot.succAboveEmb i)
  have hskip_ne_aux : ∀ i : Fin (n - 1), skip i ≠ kAux := by
    intro i
    intro hskip
    have :
        pivot.succAboveEmb i = pivot := by
      apply Fin.cast_injective hn_cast
      simpa [skip, pivot] using hskip
    exact Fin.succAbove_ne pivot i this
  let tail : Fin (n - 1) → Fin m := fun i ↦
    Classical.choose
      (exists_tail_index_of_ne_auxiliary_slice_row
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  have htail_eq :
      ∀ i : Fin (n - 1), J (skip i) = (tail i).succ.succ := by
    intro i
    exact
      Classical.choose_spec
        (exists_tail_index_of_ne_auxiliary_slice_row
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  let I : Fin (n - 1) ↪ Fin m :=
    ⟨tail, by
      intro i i' hij
      apply pivot.succAboveEmb.inj'
      apply Fin.cast_injective hn_cast
      apply J.injective
      calc
        J (skip i) = (tail i).succ.succ := htail_eq i
        _ = (tail i').succ.succ := by simpa [hij]
        _ = J (skip i') := (htail_eq i').symm⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    have hi := hJ_active (skip i)
    rw [htail_eq i] at hi
    simpa [I, Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
      using hi
  · have hskip_linearIndependent :
        LinearIndependent ℝ
          (fun i : Fin (n - 1) ↦ coneCoordinateSliceMatrix A j (J (skip i))) := by
      exact hJ_linearIndependent.comp skip (by
        intro i i' hij
        apply pivot.succAboveEmb.inj'
        apply Fin.cast_injective hn_cast
        exact hij)
    simpa [I, htail_eq, coneCoordinateSliceMatrix_tail_row] using hskip_linearIndependent

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone determines
`n - 1` active linearly independent rows of the stacked inequality owner. -/
lemma exists_active_linearlyIndependent_rows_of_extremeRay_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ I : Fin (n - 1) ↪ Fin ((m + m) + n),
      (∀ i : Fin (n - 1),
        (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0) ∧
        LinearIndependent ℝ
          (fun i : Fin (n - 1) ↦
            ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)) := by
  let M : Matrix (Fin ((m + m) + n)) (Fin n) ℝ :=
    (nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)
  have hpoly :
      standard_equality_form (A.map (Int.castRingHom ℝ)) 0 =
        polyhedron_le_set M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    -- The nonnegative kernel cone is exactly the zero-right-hand-side stacked polyhedron.
    simpa [M] using standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A
  have hnonempty :
      (polyhedron_le_set M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))).Nonempty := by
    refine ⟨0, ?_⟩
    exact (mem_nonnegativeKernelConstraintPolyhedron_iff A (x := 0)).2 (by
      simp [mem_standard_equality_form_iff])
  have hr_poly : IsExtremeRayOfPolyhedron
      (polyhedron_le_set M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) r := by
    rw [isExtremeRayOfPolyhedron_iff]
    have hr_owner :
        IsExtremeRayOfCone
          (polyhedron_le_set M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) r := by
      rw [← hpoly]
      exact hr
    rw [recessionCone_eq_nonnegativeKernelConstraintPolyhedron A]
    exact hr_owner
  obtain ⟨j, hrj_pos⟩ := exists_positive_coordinate_of_extremeRay_nonnegative_kernel_cone A hr
  have hr_extreme_slice :
      r ∈
        (polyhedron_le_set (coneCoordinateSliceMatrix M j) (coneCoordinateSliceRhs r j)).extremePoints
          ℝ :=
    coneCoordinateSliceExtremePoint M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
      hnonempty hr_poly j (ne_of_gt hrj_pos)
  obtain ⟨J, hJ_active, hJ_linearIndependent⟩ :=
    exists_active_linearlyIndependent_rows_of_extremePoint
      (coneCoordinateSliceMatrix M j) (coneCoordinateSliceRhs r j)
      (extremeRay_mem_coneCoordinateSlice M (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
        hnonempty hr_poly j)
      hr_extreme_slice
  exact
    coordinateSliceActiveRowsDropToOriginalRows
      M j (ne_of_gt hrj_pos) J hJ_active hJ_linearIndependent

/-- Helper for Exercise 5.18: any vector on the line spanned by `r` can be oriented onto the ray
generated by `r` after possibly flipping its sign. -/
lemma sameRay_or_sameRay_neg_of_mem_span_singleton
    {r s : Fin n → ℝ}
    (hs_span : s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ))) :
    SameRay ℝ r s ∨ SameRay ℝ r (-s) := by
  rcases Submodule.mem_span_singleton.mp hs_span with ⟨μ, rfl⟩
  -- The line witness is already a scalar multiple of `r`; only the sign of the scalar matters.
  by_cases hμ : 0 ≤ μ
  · -- A nonnegative scalar leaves the vector on the same ray.
    exact Or.inl (SameRay.sameRay_nonneg_smul_right r hμ)
  · have hnegμ : 0 ≤ -μ := by linarith
    -- A negative scalar becomes nonnegative after flipping the resulting vector.
    exact Or.inr (by simpa [neg_smul] using (SameRay.sameRay_nonneg_smul_right r hnegμ))

/-- Helper for Exercise 5.18: once an integer vector is on the same real ray as a point of the
nonnegative kernel cone, every integer coordinate is nonnegative. -/
lemma intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr_mem : r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hr_ne : r ≠ 0)
    {z : Fin n → ℤ}
    (hsame : SameRay ℝ r (fun i ↦ (z i : ℝ))) :
    ∀ i : Fin n, 0 ≤ z i := by
  have hr_nonneg : 0 ≤ r := (mem_standard_equality_form_iff.mp hr_mem).2
  obtain ⟨μ, hμ_nonneg, hz_eq⟩ := hsame.exists_nonneg_left hr_ne
  intro i
  have hz_cast_nonneg : 0 ≤ (z i : ℝ) := by
    -- The same-ray scaling writes the casted integer vector as a nonnegative multiple of `r`.
    calc
      0 ≤ μ * r i := mul_nonneg hμ_nonneg (hr_nonneg i)
      _ = ((fun j ↦ (z j : ℝ)) i) := by
            simpa [Pi.smul_apply, smul_eq_mul] using congrFun hz_eq i
  exact_mod_cast hz_cast_nonneg

/-- Helper for Exercise 5.18: an integer kernel witness for the selected stacked rows lies on the
line spanned by the extreme-ray generator. -/
lemma intKernelWitness_mem_span_singleton_of_selected_rows
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr_ne : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_active : ∀ i : Fin (n - 1),
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)))
    {z : Fin n → ℤ}
    (hz_zero : ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0) :
    (fun i ↦ (z i : ℝ)) ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) := by
  -- Cast the selected-row integer kernel relation to `ℝ`, then invoke the existing line lemma.
  refine mem_span_singleton_of_selected_rows_zero
    (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)))
    hr_ne I hI_active hI_linearIndependent ?_
  intro i
  have hi_int : (((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z) i = 0 := by
    simpa using congrFun hz_zero i
  have hi_real :
      ((((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ
          (fun j ↦ (z j : ℝ))) (I i)) = 0 := by
    calc
      ((((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ
            (fun j ↦ (z j : ℝ))) (I i))
          = (((((nonnegativeKernelConstraintMatrix A).submatrix I id).map (Int.castRingHom ℝ)) *ᵥ
                (fun j ↦ (z j : ℝ))) i) := by
              simp [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      _ = ((((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z) i : ℝ) := by
            simp [Matrix.mulVec, dotProduct]
      _ = 0 := by
            exact_mod_cast hi_int
  exact hi_real

/-- Helper for Exercise 5.18: orient a bounded integral line witness onto the nonnegative ray of
the extreme-ray generator. -/
lemma existsBoundedSameRayGenerator_of_intKernelWitness
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr_mem : r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hr_ne : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_active : ∀ i : Fin (n - 1),
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)))
    {z : Fin n → ℤ}
    (hz_ne : z ≠ 0)
    (hz_zero : ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0)
    (hz_abs : ∀ i : Fin n, |z i| ≤ Δ) :
    ∃ z' : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z' i : ℝ)) ∧
        z' ≠ 0 ∧
        ∀ i : Fin n, 0 ≤ z' i ∧ z' i ≤ Δ := by
  have hs_span :
      (fun i ↦ (z i : ℝ)) ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) :=
    intKernelWitness_mem_span_singleton_of_selected_rows
      A hr_ne I hI_active hI_linearIndependent hz_zero
  rcases sameRay_or_sameRay_neg_of_mem_span_singleton hs_span with hsame | hsame
  · -- When the line witness already points along the ray, use nonnegativity plus `|z i| ≤ Δ`.
    have hz_nonneg :
        ∀ i : Fin n, 0 ≤ z i :=
      intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone A hr_mem hr_ne hsame
    refine ⟨z, hsame, hz_ne, ?_⟩
    intro i
    have hz_abs_i : |z i| ≤ Δ := hz_abs i
    rw [abs_of_nonneg (hz_nonneg i)] at hz_abs_i
    exact ⟨hz_nonneg i, hz_abs_i⟩
  · -- Otherwise flip the sign: the absolute-value bound is unchanged and the ray orientation fixes.
    let z' : Fin n → ℤ := fun i ↦ -z i
    have hsame' : SameRay ℝ r (fun i ↦ (z' i : ℝ)) := by
      simpa [z', Pi.neg_apply] using hsame
    have hz'_ne : z' ≠ 0 := by
      intro hz'_zero
      apply hz_ne
      ext i
      have hi : z' i = 0 := by simpa using congrFun hz'_zero i
      exact neg_eq_zero.mp (by simpa [z'] using hi)
    have hz'_nonneg :
        ∀ i : Fin n, 0 ≤ z' i :=
      intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone A hr_mem hr_ne hsame'
    refine ⟨z', hsame', hz'_ne, ?_⟩
    intro i
    have hz'_abs_i : |z' i| ≤ Δ := by
      simpa [z'] using hz_abs i
    rw [abs_of_nonneg (hz'_nonneg i)] at hz'_abs_i
    exact ⟨hz'_nonneg i, hz'_abs_i⟩

/-- Helper for Exercise 5.18: a full-row-rank real matrix contains a square invertible submatrix
on some choice of columns. -/
lemma fullRowRankColumnBasis
    {r : ℕ} {c : Type*} [Fintype c]
    (N : Matrix (Fin r) c ℝ)
    (hrows : LinearIndependent ℝ N.row) :
    ∃ J : Fin r ↪ c, IsUnit (N.submatrix id J) := by
  classical
  let colSpace : Submodule ℝ (Fin r → ℝ) := Submodule.span ℝ (Set.range N.col)
  have hrank : N.rank = r := by
    -- Full row rank turns the row-independence hypothesis into a rank computation.
    simpa using LinearIndependent.rank_matrix hrows
  have hcol_finrank : Module.finrank ℝ colSpace = r := by
    -- The column space has the same dimension as the matrix rank.
    calc
      Module.finrank ℝ colSpace = N.rank := by
        simpa [colSpace] using (Matrix.rank_eq_finrank_span_cols (A := N)).symm
      _ = r := hrank
  obtain ⟨cols, hcols_mem, hcols_span, hcols_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range N.col)
  let e : Fin (Module.finrank ℝ colSpace) ≃ Fin r :=
    Fintype.equivOfCardEq (by simp [hcol_finrank])
  let picked : Fin r → c := fun i ↦ Classical.choose (hcols_mem (e.symm i))
  have hpicked_eq : ∀ i : Fin r, N.col (picked i) = cols (e.symm i) := by
    intro i
    exact Classical.choose_spec (hcols_mem (e.symm i))
  have hpicked_linear : LinearIndependent ℝ (fun i : Fin r ↦ N.col (picked i)) := by
    -- Reindex the selected spanning columns to `Fin r`, then rewrite them back to actual columns.
    have hcols_reindexed : LinearIndependent ℝ (fun i : Fin r ↦ cols (e.symm i)) := by
      exact (linearIndependent_equiv e.symm).2 hcols_linear
    have hEq :
        (fun i : Fin r ↦ N.col (picked i)) = fun i : Fin r ↦ cols (e.symm i) := by
      funext i
      exact hpicked_eq i
    exact hEq ▸ hcols_reindexed
  have hpicked_injective : Function.Injective picked := by
    intro i j hij
    apply hpicked_linear.injective
    simpa [hij]
  let J : Fin r ↪ c := ⟨picked, hpicked_injective⟩
  have hsub_cols : LinearIndependent ℝ (N.submatrix id J).col := by
    -- The chosen square submatrix has exactly the selected independent columns.
    simpa [J, Matrix.col, Matrix.submatrix_apply] using hpicked_linear
  exact ⟨J, (Matrix.linearIndependent_cols_iff_isUnit).1 hsub_cols⟩

/-- Helper for Exercise 5.18: in an `(r × (r + 1))` full-row-rank matrix, one can delete a single
column and keep an invertible square block. -/
lemma fullRowRankDeletedColumnBasis
    {r : ℕ}
    (N : Matrix (Fin r) (Fin (r + 1)) ℝ)
    (hrows : LinearIndependent ℝ N.row) :
    ∃ pivot : Fin (r + 1), IsUnit (N.submatrix id (Fin.succAbove pivot)) := by
  classical
  obtain ⟨J, hJunit⟩ := fullRowRankColumnBasis N hrows
  have hJ_cols : LinearIndependent ℝ (fun i : Fin r ↦ N.col (J i)) := by
    -- The invertible selected square block records the chosen independent column family.
    have hsub_cols : LinearIndependent ℝ (N.submatrix id J).col :=
      (Matrix.linearIndependent_cols_iff_isUnit).mpr hJunit
    simpa [Matrix.col, Matrix.submatrix_apply] using hsub_cols
  have hJ_not_surj : ¬ Function.Surjective J := by
    intro hsurj
    have hcard : r + 1 ≤ r := by
      simpa using Fintype.card_le_of_surjective J hsurj
    omega
  obtain ⟨pivot, hpivot⟩ : ∃ pivot : Fin (r + 1), pivot ∉ Set.range J := by
    by_contra hnone
    apply hJ_not_surj
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  let J' : Fin r → {x : Fin (r + 1) // x ≠ pivot} := fun i ↦ ⟨J i, by
    intro hJi
    exact hpivot ⟨i, hJi⟩⟩
  have hJ'_bijective : Function.Bijective J' := by
    refine (Fintype.bijective_iff_injective_and_card J').mpr ?_
    constructor
    · intro i j hij
      apply J.injective
      exact congrArg Subtype.val hij
    · simp
  let eJ : Fin r ≃ {x : Fin (r + 1) // x ≠ pivot} := Equiv.ofBijective J' hJ'_bijective
  let τ : Fin r ≃ Fin r := (finSuccAboveEquiv pivot).trans eJ.symm
  have hcanonical_cols :
      LinearIndependent ℝ (fun i : Fin r ↦ N.col (pivot.succAbove i)) := by
    -- The canonical deleted-column family is the chosen basis up to a permutation of the indices.
    have hperm :
        (fun i : Fin r ↦ N.col (pivot.succAbove i)) =
          fun i : Fin r ↦ N.col (J (τ i)) := by
      funext i
      have hsub : J' (τ i) = finSuccAboveEquiv pivot i := by
        change J' (eJ.symm (finSuccAboveEquiv pivot i)) = finSuccAboveEquiv pivot i
        exact eJ.apply_symm_apply (finSuccAboveEquiv pivot i)
      have hval : J (τ i) = pivot.succAbove i := by
        change Subtype.val (J' (τ i)) = Subtype.val (finSuccAboveEquiv pivot i)
        exact congrArg Subtype.val hsub
      simpa [hval]
    have hperm_linear : LinearIndependent ℝ (fun i : Fin r ↦ N.col (J (τ i))) := by
      exact hJ_cols.comp τ τ.injective
    exact hperm.symm ▸ hperm_linear
  have hcanonical_sub_cols : LinearIndependent ℝ (N.submatrix id (Fin.succAbove pivot)).col := by
    -- Repackage the canonical deleted columns as the column family of the square submatrix.
    simpa [Matrix.col, Matrix.submatrix_apply] using hcanonical_cols
  exact ⟨pivot, (Matrix.linearIndependent_cols_iff_isUnit).1 hcanonical_sub_cols⟩

/-- Helper for Exercise 5.18: inserting the pivot coordinate splits a row dot product into the
pivot term and the remaining `succAbove` coordinates. -/
lemma rowDot_insertNth
    {r : ℕ}
    (pivot : Fin (r + 1))
    (row : Fin (r + 1) → ℤ)
    (xPivot : ℤ)
    (xRest : Fin r → ℤ) :
    dotProduct row (Fin.insertNth pivot xPivot xRest) =
      row pivot * xPivot + ∑ i : Fin r, row (pivot.succAbove i) * xRest i := by
  -- Split the full sum into the pivot contribution and the remaining `succAbove` coordinates.
  let z : Fin (r + 1) → ℤ := Fin.insertNth pivot xPivot xRest
  simpa [dotProduct, z, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
    (Fin.sum_univ_succAbove (fun i : Fin (r + 1) ↦ row i * z i) pivot)

/-- Helper for Exercise 5.18: once a deleted square block is nonsingular, the deleted-column
Cramer construction gives a nonzero kernel vector for the original rectangular matrix. -/
lemma deletedColumnCramerKernelWitness
    {r : ℕ}
    (M : Matrix (Fin r) (Fin (r + 1)) ℤ)
    (pivot : Fin (r + 1))
    (hdet_ne_zero : (M.submatrix id (Fin.succAbove pivot)).det ≠ 0) :
    let B : Matrix (Fin r) (Fin r) ℤ := M.submatrix id (Fin.succAbove pivot)
    let rhs : Fin r → ℤ := fun i ↦ M i pivot
    let z : Fin (r + 1) → ℤ := Fin.insertNth pivot B.det (fun i ↦ -(B.cramer rhs i))
    z ≠ 0 ∧ M *ᵥ z = 0 := by
  let B : Matrix (Fin r) (Fin r) ℤ := M.submatrix id (Fin.succAbove pivot)
  let rhs : Fin r → ℤ := fun i ↦ M i pivot
  let z : Fin (r + 1) → ℤ := Fin.insertNth pivot B.det (fun i ↦ -(B.cramer rhs i))
  refine ⟨?_, ?_⟩
  · -- The inserted pivot coordinate is the nonzero determinant of the deleted square block.
    intro hz
    apply hdet_ne_zero
    have hzPivot : z pivot = 0 := by
      simpa [z] using congrFun hz pivot
    simpa [z, Fin.insertNth_apply_same] using hzPivot
  · -- The rectangular Cramer vector is designed so the deleted block contribution cancels the pivot.
    ext i
    have hmul_neg :
        B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s)) =
          -(B *ᵥ B.cramer rhs) := by
      simpa using Matrix.mulVec_neg (B.cramer rhs) B
    have hrow_neg :
        ∑ s : Fin r, B i s * (-(B.cramer rhs s)) = -(B.det * rhs i) := by
      have hAt : (B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s))) i = (-(B.det • rhs)) i := by
        calc
          (B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s))) i
              = (-(B *ᵥ B.cramer rhs)) i := by
                  simpa using congrFun hmul_neg i
          _ = (-(B.det • rhs)) i := by
                simpa using congrArg Neg.neg (congrFun (Matrix.mulVec_cramer B rhs) i)
      simpa [Matrix.mulVec, dotProduct, rhs] using hAt
    -- Split the full row sum at the deleted pivot coordinate and rewrite the remaining block part
    -- through Cramer's rule on `B`.
    calc
      (M *ᵥ z) i = M i pivot * B.det + ∑ s : Fin r, M i (pivot.succAbove s) * (-(B.cramer rhs s)) := by
        simp [Matrix.mulVec, z, rowDot_insertNth, B]
      _ = rhs i * B.det + ∑ s : Fin r, B i s * (-(B.cramer rhs s)) := by
        simp [B, rhs]
      _ = rhs i * B.det + (-(B.det * rhs i)) := by rw [hrow_neg]
      _ = 0 := by ring

/-- Helper for Exercise 5.18: selecting rows from `Matrix.fromRows A (-A)` only changes row signs,
unless two selected rows project to the same row of `A`, in which case the determinant vanishes. -/
lemma abs_square_subdet_le_of_selectedSignedEqualityRows
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {k : ℕ}
    (rows : Fin k ↪ Sum (Fin m) (Fin m))
    (cols : Fin k ↪ Fin n) :
    |(((Matrix.fromRows A (-A)).submatrix rows cols).det)| ≤ Δ := by
  classical
  let baseRow : Fin k → Fin m := fun i ↦ Sum.elim id id (rows i)
  let rowSign : Fin k → ℤ := fun i ↦
    match rows i with
    | Sum.inl _ => 1
    | Sum.inr _ => -1
  let baseMatrix : Matrix (Fin k) (Fin k) ℤ := fun i j ↦ A (baseRow i) (cols j)
  have hdecomp :
      ((Matrix.fromRows A (-A)).submatrix rows cols) =
        Matrix.diagonal rowSign * baseMatrix := by
    -- Split the selected signed rows into their underlying row of `A` and the sign carried by the
    -- choice of the top or bottom equality block.
    ext i j
    rcases hrow : rows i with r | r
    · simpa [Matrix.mul_apply, Matrix.diagonal_apply, baseMatrix, baseRow, rowSign, hrow]
    · simpa [Matrix.mul_apply, Matrix.diagonal_apply, baseMatrix, baseRow, rowSign, hrow]
  by_cases hbase_inj : Function.Injective baseRow
  · let rowsA : Fin k ↪ Fin m := ⟨baseRow, hbase_inj⟩
    have hbaseMatrix : baseMatrix = A.submatrix rowsA cols := by
      ext i j
      rfl
    have hdiag_abs : |(Matrix.diagonal rowSign).det| = 1 := by
      -- Every selected row contributes only a factor `1` or `-1` to the determinant.
      have habs : ∀ i : Fin k, |rowSign i| = 1 := by
        intro i
        rcases hrow : rows i with r | r <;> simp [rowSign, hrow]
      calc
        |(Matrix.diagonal rowSign).det| = ∏ i, |rowSign i| := by
          rw [Matrix.det_diagonal, Finset.abs_prod]
        _ = 1 := by simp [habs]
    calc
      |(((Matrix.fromRows A (-A)).submatrix rows cols).det)|
          = |(Matrix.diagonal rowSign).det| * |baseMatrix.det| := by
              rw [hdecomp, Matrix.det_mul, abs_mul]
      _ = |baseMatrix.det| := by rw [hdiag_abs, one_mul]
      _ = |((A.submatrix rowsA cols).det)| := by rw [hbaseMatrix]
      _ ≤ Δ := abs_square_subdet_le_of_is_largest_abs_square_subdeterminant A Δ hΔ rowsA cols
  · have hrepeat : ∃ i j : Fin k, i ≠ j ∧ baseRow i = baseRow j := by
      -- If the projected row map is not injective, two selected rows are equal up to sign.
      by_contra hrepeat
      apply hbase_inj
      intro i j hij
      by_contra hij_ne
      exact hrepeat ⟨i, j, hij_ne, hij⟩
    rcases hrepeat with ⟨i, j, hij, hbase_eq⟩
    have hrow_eq : baseMatrix i = baseMatrix j := by
      funext t
      simp [baseMatrix, hbase_eq]
    have hbase_det_zero : baseMatrix.det = 0 :=
      Matrix.det_zero_of_row_eq hij hrow_eq
    have hdet_zero :
        (((Matrix.fromRows A (-A)).submatrix rows cols).det) = 0 := by
      -- Repeated projected rows force the signed minor itself to have determinant zero.
      rw [hdecomp, Matrix.det_mul, hbase_det_zero]
      simp
    simpa [hdet_zero] using largestAbsSquareSubdeterminant_nonneg A Δ hΔ

/-- Helper for Exercise 5.18: every square subdeterminant of a selected square submatrix of the
stacked constraint matrix is bounded by `Δ`. -/
lemma abs_square_subdet_le_of_selectedConstraintMatrix
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {k : ℕ}
    (rows : Fin k ↪ Fin ((m + m) + n))
    (cols : Fin k ↪ Fin n) :
    |(((nonnegativeKernelConstraintMatrix A).submatrix rows cols).det)| ≤ Δ := by
  classical
  let equalities : Matrix (Fin (m + m)) (Fin n) ℤ :=
    (Matrix.fromRows A (-A)).reindex finSumFinEquiv (Equiv.refl _)
  let stacked : Matrix (Sum (Fin (m + m)) (Fin n)) (Fin n) ℤ :=
    Matrix.fromRows equalities (-(1 : Matrix (Fin n) (Fin n) ℤ))
  let rowsSum : Fin k ↪ Sum (Fin (m + m)) (Fin n) :=
    ⟨fun i ↦ finSumFinEquiv.symm (rows i), by
      intro i j hij
      apply rows.injective
      exact by simpa using congrArg finSumFinEquiv hij⟩
  have hsub :
      ((nonnegativeKernelConstraintMatrix A).submatrix rows cols) =
        stacked.submatrix rowsSum cols := by
    -- Rewrite the selected minor back to the unreindexed stacked owner.
    ext i j
    simp [nonnegativeKernelConstraintMatrix, equalities, stacked, rowsSum, Matrix.submatrix_apply]
  have hstack :
      ∀ {s : ℕ} (selectedRows : Fin s ↪ Sum (Fin (m + m)) (Fin n))
        (selectedCols : Fin s ↪ Fin n),
        |((stacked.submatrix selectedRows selectedCols).det)| ≤ Δ := by
    intro s
    induction s with
    | zero =>
        intro selectedRows selectedCols
        -- The empty selected minor has determinant `1`, so the universal `1 ≤ Δ` bound applies.
        simpa using largestAbsSquareSubdeterminant_one_le A Δ hΔ
    | succ s ih =>
        intro selectedRows selectedCols
        -- Route correction: peel off selected `-I` rows first, and only then compare the
        -- surviving equality-block minor with a square subdeterminant of `A`.
        by_cases hbottom : ∃ i : Fin (s + 1), ∃ j : Fin n, selectedRows i = Sum.inr j
        · rcases hbottom with ⟨i, j, hrowi⟩
          let M : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ :=
            stacked.submatrix selectedRows selectedCols
          by_cases hcol : ∃ x : Fin (s + 1), selectedCols x = j
          · rcases hcol with ⟨x, hx⟩
            let rowsTail : Fin s ↪ Sum (Fin (m + m)) (Fin n) :=
              ⟨fun t ↦ selectedRows (i.succAbove t), by
                intro a b hab
                exact Fin.succAbove_right_injective (selectedRows.injective hab)⟩
            let colsTail : Fin s ↪ Fin n :=
              ⟨fun t ↦ selectedCols (x.succAbove t), by
                intro a b hab
                exact Fin.succAbove_right_injective (selectedCols.injective hab)⟩
            have hminor :
                M.submatrix i.succAbove x.succAbove =
                  stacked.submatrix rowsTail colsTail := by
              ext a b
              simp [M, rowsTail, colsTail]
            have hmain_entry : M i x = -1 := by
              -- The chosen `-I` row meets the chosen column in exactly one entry equal to `-1`.
              simp [M, stacked, hrowi, hx]
            have hother_entry : ∀ y : Fin (s + 1), y ≠ x → M i y = 0 := by
              intro y hy
              have hy_ne : j ≠ selectedCols y := by
                intro hy_eq
                apply hy
                exact selectedCols.injective (hy_eq.symm.trans hx.symm)
              simp [M, stacked, hrowi, hy_ne, Matrix.one_apply]
            have hdet_expand := Matrix.det_succ_row M i
            rw [Fintype.sum_eq_single x] at hdet_expand
            · calc
                |M.det| = |(M.submatrix i.succAbove x.succAbove).det| := by
                  rw [hdet_expand, hmain_entry]
                  simp
                _ = |((stacked.submatrix rowsTail colsTail).det)| := by rw [hminor]
                _ ≤ Δ := ih rowsTail colsTail
            · intro y hy
              rw [hother_entry y hy]
              simp
          · have hzero_row : ∀ y : Fin (s + 1), M i y = 0 := by
              intro y
              have hy_ne : j ≠ selectedCols y := by
                intro hy_eq
                exact hcol ⟨y, hy_eq.symm⟩
              -- If the selected `-I` row misses every chosen column, it becomes a zero row.
              simp [M, stacked, hrowi, hy_ne, Matrix.one_apply]
            have hdet_zero : M.det = 0 :=
              Matrix.det_eq_zero_of_row_eq_zero i hzero_row
            simpa [M, hdet_zero] using largestAbsSquareSubdeterminant_nonneg A Δ hΔ
        · have htop : ∀ i : Fin (s + 1), ∃ r : Fin (m + m), selectedRows i = Sum.inl r := by
            intro i
            cases hrow : selectedRows i with
            | inl r =>
                exact ⟨r, rfl⟩
            | inr j =>
                exact False.elim (hbottom ⟨i, j, hrow⟩)
          choose rowsEq hrowsEq using htop
          have hrowsEq_inj : Function.Injective rowsEq := by
            intro a b hab
            apply selectedRows.injective
            rw [hrowsEq a, hrowsEq b, hab]
          let rowsEqEmb : Fin (s + 1) ↪ Fin (m + m) := ⟨rowsEq, hrowsEq_inj⟩
          let rowsEqSum : Fin (s + 1) ↪ Sum (Fin m) (Fin m) :=
            ⟨fun t ↦ finSumFinEquiv.symm (rowsEqEmb t), by
              intro a b hab
              apply rowsEqEmb.injective
              exact by simpa using congrArg finSumFinEquiv hab⟩
          have htop_sub :
              stacked.submatrix selectedRows selectedCols =
                equalities.submatrix rowsEqEmb selectedCols := by
            -- With no selected `-I` rows left, the stacked minor is already an equality-block minor.
            ext a b
            simpa [stacked, rowsEqEmb] using
              congrArg (fun row ↦ stacked row (selectedCols b)) (hrowsEq a)
          have hequalities :
              equalities.submatrix rowsEqEmb selectedCols =
                (Matrix.fromRows A (-A)).submatrix rowsEqSum selectedCols := by
            -- Undo the reindexing of the equality block before comparing with `A`.
            ext a b
            simp [equalities, rowsEqEmb, rowsEqSum, Matrix.submatrix_apply]
          calc
            |((stacked.submatrix selectedRows selectedCols).det)|
                = |(((Matrix.fromRows A (-A)).submatrix rowsEqSum selectedCols).det)| := by
                    rw [htop_sub, hequalities]
            _ ≤ Δ :=
              abs_square_subdet_le_of_selectedSignedEqualityRows A Δ hΔ rowsEqSum selectedCols
  calc
    |(((nonnegativeKernelConstraintMatrix A).submatrix rows cols).det)|
        = |((stacked.submatrix rowsSum cols).det)| := by rw [hsub]
    _ ≤ Δ := hstack rowsSum cols

/-- Helper for Exercise 5.18: selected active rows of the stacked constraint matrix yield a
nonzero bounded integer kernel witness. -/
lemma existsBoundedIntegralKernelWitness_of_selectedActiveRows
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    (hn : 0 < n)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i))) :
    ∃ z : Fin n → ℤ,
      z ≠ 0 ∧
        ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0 ∧
        ∀ i : Fin n, |z i| ≤ Δ := by
  classical
  cases n with
  | zero =>
      omega
  | succ n =>
      let MZ : Matrix (Fin n) (Fin (n + 1)) ℤ :=
        (nonnegativeKernelConstraintMatrix A).submatrix I id
      let MR : Matrix (Fin n) (Fin (n + 1)) ℝ := MZ.map (Int.castRingHom ℝ)
      have hrows : LinearIndependent ℝ MR.row := by
        -- The selected active rows are exactly the rows of the rectangular selected matrix.
        simpa [MR, MZ] using hI_linearIndependent
      obtain ⟨pivot, hBunit⟩ := fullRowRankDeletedColumnBasis MR hrows
      let BZ : Matrix (Fin n) (Fin n) ℤ := MZ.submatrix id (Fin.succAbove pivot)
      let rhs : Fin n → ℤ := fun i ↦ MZ i pivot
      let z : Fin (n + 1) → ℤ := Fin.insertNth pivot BZ.det (fun i ↦ -(BZ.cramer rhs i))
      have hBdet_real_ne : (MR.submatrix id (Fin.succAbove pivot)).det ≠ 0 := by
        exact ((Matrix.isUnit_iff_isUnit_det (A := MR.submatrix id (Fin.succAbove pivot))).mp
          hBunit).ne_zero
      have hBdet_int_ne : BZ.det ≠ 0 := by
        -- Transport nonvanishing of the selected determinant back from `ℝ` to `ℤ`.
        intro hdet_zero
        apply hBdet_real_ne
        rw [show (MR.submatrix id (Fin.succAbove pivot)).det = (BZ.det : ℝ) by
          simpa [MR, MZ, BZ] using
            (RingHom.map_det (Int.castRingHom ℝ) (MZ.submatrix id (Fin.succAbove pivot))).symm]
        exact_mod_cast hdet_zero
      have hz_spec : z ≠ 0 ∧ MZ *ᵥ z = 0 := by
        -- The deleted-column Cramer vector closes the rectangular kernel equation.
        simpa [MZ, BZ, rhs, z] using deletedColumnCramerKernelWitness MZ pivot hBdet_int_ne
      refine ⟨z, hz_spec.1, hz_spec.2, ?_⟩
      intro j
      by_cases hj : j = pivot
      · subst j
        -- The pivot coordinate is the determinant of the deleted square block.
        simpa [z, BZ, Fin.insertNth_apply_same] using
          abs_square_subdet_le_of_selectedConstraintMatrix A Δ hΔ
            (rows := I) (cols := Fin.succAboveEmb pivot)
      · rcases Fin.exists_succAbove_eq hj with ⟨s, rfl⟩
        let colsFun : Fin n → Fin (n + 1) := fun t ↦ if h : t = s then pivot else pivot.succAbove t
        let cols : Fin n ↪ Fin (n + 1) :=
          ⟨colsFun, by
            intro t₁ t₂ hcols
            by_cases ht₁ : t₁ = s
            · by_cases ht₂ : t₂ = s
              · simpa [ht₁, ht₂]
              · have : pivot = pivot.succAbove t₂ := by simpa [colsFun, ht₁, ht₂] using hcols
                exact False.elim (Fin.succAbove_ne pivot t₂ this.symm)
            · by_cases ht₂ : t₂ = s
              · have : pivot = pivot.succAbove t₁ := by simpa [colsFun, ht₁, ht₂] using hcols.symm
                exact False.elim (Fin.succAbove_ne pivot t₁ this.symm)
              · apply pivot.succAboveEmb.injective
                simpa [colsFun, ht₁, ht₂] using hcols⟩
        have hupdate :
            BZ.updateCol s rhs = MZ.submatrix id cols := by
          -- Replacing one deleted column by the pivot column is exactly another square submatrix.
          ext i t
          by_cases ht : t = s
          · subst ht
            simp [BZ, rhs, cols, colsFun]
          · simp [BZ, rhs, cols, colsFun, ht]
        have hcramer_abs : |BZ.cramer rhs s| ≤ Δ := by
          -- Each Cramer coordinate is the determinant of one square submatrix of the selected rows.
          calc
            |BZ.cramer rhs s| = |(BZ.updateCol s rhs).det| := by rw [Matrix.cramer_apply]
            _ = |((MZ.submatrix id cols).det)| := by rw [hupdate]
            _ ≤ Δ := by
                  simpa [MZ] using
                    abs_square_subdet_le_of_selectedConstraintMatrix A Δ hΔ
                      (rows := I) (cols := cols)
        simpa [z, Fin.insertNth_apply_succAbove, abs_neg] using hcramer_abs

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone has a primitive
integral generator whose coordinates lie in `[0, Δ]`. -/
lemma existsIntegralBoundedSameRayGenerator_of_extremeRay
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ z : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z i : ℝ)) ∧
        z ≠ 0 ∧
        ∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ := by
  have hr_mem :
      r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 :=
    extremeRay_mem_of_isExtremeRayOfCone hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  have hn : 0 < n := by
    by_contra hn_pos
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    subst hn_zero
    apply hr_ne
    ext i
    exact Fin.elim0 i
  obtain ⟨I, hI_active, hI_linearIndependent⟩ :=
    exists_active_linearlyIndependent_rows_of_extremeRay_nonnegative_kernel_cone A hr
  obtain ⟨z, hz_ne, hz_zero, hz_abs⟩ :=
    existsBoundedIntegralKernelWitness_of_selectedActiveRows
      A Δ hΔ hn I hI_linearIndependent
  -- Route correction: once the bounded integer kernel witness is available, only orientation onto
  -- the extreme ray and the conversion from `|z i| ≤ Δ` to `[0, Δ]` remain.
  exact
    existsBoundedSameRayGenerator_of_intKernelWitness
      A Δ hΔ hr_mem hr_ne I hI_active hI_linearIndependent hz_ne hz_zero hz_abs

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone has a primitive
integral generator whose coordinates lie in `[0, Δ]`. -/
lemma existsPrimitiveBoundedIntegralSameRayGenerator_of_extremeRay
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ z : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z i : ℝ)) ∧
        z ≠ 0 ∧
        (∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ) ∧
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1 := by
  obtain ⟨z, hsame, hz_ne, hz_bounds⟩ :=
    existsIntegralBoundedSameRayGenerator_of_extremeRay A Δ hΔ hr
  set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) with hgN
  let zPrimitive : Fin n → ℤ := fun i ↦ z i / gN
  have hg_pos : 0 < gN := by
    -- The coordinate gcd of a nonzero integer vector is positive.
    simpa [hgN] using coordinate_gcd_pos z hz_ne
  have hz_dvd : ∀ i : Fin n, (gN : ℤ) ∣ z i := by
    -- Each coordinate is divisible by the coordinate gcd.
    intro i
    rw [Int.natCast_dvd]
    simpa [hgN] using
      (Finset.gcd_dvd (b := i) (f := fun j : Fin n ↦ Int.natAbs (z j)) (by simp))
  have hz_sameRay_primitive :
      SameRay ℝ (fun i ↦ (z i : ℝ)) (fun i ↦ (zPrimitive i : ℝ)) := by
    -- Dividing by the positive coordinate gcd keeps the vector on the same real ray.
    have hcast_eq :
        (fun i ↦ (z i : ℝ)) = (gN : ℝ) • (fun i ↦ (zPrimitive i : ℝ)) := by
      ext i
      calc
        (z i : ℝ) = (((gN : ℤ) * zPrimitive i : ℤ) : ℝ) := by
          simpa [zPrimitive] using congrArg (fun t : ℤ ↦ (t : ℝ)) (Int.mul_ediv_cancel' (hz_dvd i)).symm
        _ = (gN : ℝ) * (zPrimitive i : ℝ) := by
          norm_num
        _ = ((gN : ℝ) • (fun j ↦ (zPrimitive j : ℝ))) i := by
          simp [Pi.smul_apply, smul_eq_mul]
    rw [hcast_eq]
    exact SameRay.sameRay_pos_smul_left (fun i ↦ (zPrimitive i : ℝ)) (by exact_mod_cast hg_pos)
  have hsamePrimitive : SameRay ℝ r (fun i ↦ (zPrimitive i : ℝ)) := by
    -- Compose the geometric same-ray witness with the positive gcd rescaling.
    exact SameRay.trans hsame hz_sameRay_primitive
      (fun hz_zero ↦ False.elim ((intCastVector_ne_zero hz_ne) hz_zero))
  have hzPrimitive_ne : zPrimitive ≠ 0 := by
    -- A positive rescaling of a nonzero vector cannot become zero after dividing by the gcd.
    intro hzPrimitive_zero
    apply hz_ne
    ext i
    calc
      z i = (gN : ℤ) * zPrimitive i := by
        simpa [zPrimitive] using (Int.mul_ediv_cancel' (hz_dvd i)).symm
      _ = 0 := by simp [hzPrimitive_zero]
  have hzPrimitive_bounds : ∀ i : Fin n, 0 ≤ zPrimitive i ∧ zPrimitive i ≤ Δ := by
    intro i
    have hzi_nonneg : 0 ≤ z i := (hz_bounds i).1
    have hzi_le : z i ≤ Δ := (hz_bounds i).2
    have hzPrimitive_nonneg : 0 ≤ zPrimitive i := by
      -- Integer division by a positive gcd preserves nonnegativity.
      exact Int.ediv_nonneg hzi_nonneg (by exact_mod_cast (Nat.zero_le gN))
    have hg_one_le : (1 : ℤ) ≤ gN := by
      exact_mod_cast (Nat.succ_le_of_lt hg_pos)
    have hzPrimitive_le_z : zPrimitive i ≤ z i := by
      -- Since `gN ≥ 1`, the normalized coordinate is bounded by the original coordinate.
      calc
        zPrimitive i ≤ (gN : ℤ) * zPrimitive i := by
          simpa using mul_le_mul_of_nonneg_right hg_one_le hzPrimitive_nonneg
        _ = z i := by
          simpa [zPrimitive] using (Int.mul_ediv_cancel' (hz_dvd i))
    exact ⟨hzPrimitive_nonneg, hzPrimitive_le_z.trans hzi_le⟩
  have hzPrimitive_gcd :
      Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (zPrimitive i)) = 1 := by
    -- Remark 5.1 provides primitiveness after dividing by the coordinate gcd.
    simpa [zPrimitive, hgN] using normalized_split_vector_gcd_eq_one z hz_ne
  exact ⟨zPrimitive, hsamePrimitive, hzPrimitive_ne, hzPrimitive_bounds, hzPrimitive_gcd⟩

/-- Exercise 5.18. Let `C = {x ∈ ℝ^n | A x = 0, x ≥ 0}` where `A` is an integral matrix. Let `Δ`
be the largest among the absolute values of the determinants of the square submatrices of `A`.
Then the extreme rays of `C` have a finite representative family of integral vectors whose
coordinates all lie in `[-Δ, Δ]`. -/
theorem exists_integral_bounded_extreme_ray_representative_family_of_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    ∃ q : ℕ,
      ∃ rays : Fin q → Fin n → ℝ,
        IsExtremeRayRepresentativeFamily
            (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) rays ∧
          (∀ t : Fin q, rays t ∈ ℤ^n) ∧
          ∀ t : Fin q, ∀ j : Fin n, (-(Δ : ℝ)) ≤ rays t j ∧ rays t j ≤ (Δ : ℝ) := by
  classical
  let C : Set (Fin n → ℝ) := standard_equality_form (A.map (Int.castRingHom ℝ)) 0
  let box : Set (Fin n → ℤ) := {z | ∀ i : Fin n, z i ∈ Set.Icc 0 Δ}
  let primitiveExtremeBox : Set (Fin n → ℤ) :=
    {z |
      z ≠ 0 ∧
        (∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ) ∧
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1 ∧
        IsExtremeRayOfCone C (fun i ↦ (z i : ℝ))}
  have hΔ_nonneg : 0 ≤ Δ := largestAbsSquareSubdeterminant_nonneg A Δ hΔ
  have hboxFinite : box.Finite := by
    -- The bounded integer coordinate box is finite.
    simpa [box, Set.pi] using
      (Set.Finite.pi' (t := fun i : Fin n ↦ Set.Icc (0 : ℤ) Δ)
        fun i ↦ Set.finite_Icc (0 : ℤ) Δ)
  have hprimitiveExtremeBoxFinite : primitiveExtremeBox.Finite := by
    -- Filtering the box by primitive and extreme-ray conditions preserves finiteness.
    refine hboxFinite.subset ?_
    intro z hz
    exact hz.2.1
  obtain ⟨q, zs, hzs_inj, hzs_range⟩ := hprimitiveExtremeBoxFinite.fin_param
  let rays : Fin q → Fin n → ℝ := fun t i ↦ (zs t i : ℝ)
  refine ⟨q, rays, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t
      -- Each enumerated vector was filtered to be an extreme-ray generator.
      have ht_mem : zs t ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨t, rfl⟩
      exact ht_mem.2.2.2
    · intro s t hst
      intro hsame
      -- Same-ray primitive nonnegative generators must coincide, contradicting injectivity.
      have hs_mem : zs s ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨s, rfl⟩
      have ht_mem : zs t ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨t, rfl⟩
      have hEq :
          zs s = zs t :=
        eq_of_sameRay_of_nonnegative_primitiveGenerators
          hs_mem.1
          ht_mem.1
          (fun i ↦ (hs_mem.2.1 i).1)
          (fun i ↦ (ht_mem.2.1 i).1)
          hs_mem.2.2.1
          ht_mem.2.2.1
          hsame
      exact hst (hzs_inj hEq)
    · intro r hr
      -- Coverage comes from the bounded primitive same-ray generator lemma.
      obtain ⟨z, hsame, hz_ne, hz_bounds, hz_primitive⟩ :=
        existsPrimitiveBoundedIntegralSameRayGenerator_of_extremeRay A Δ hΔ hr
      have hz_extreme : IsExtremeRayOfCone C (fun i ↦ (z i : ℝ)) := by
        -- Replacing an extreme generator by a nonzero vector on the same ray preserves the ray.
        exact isExtremeRayOfCone_of_sameRay hr hsame (intCastVector_ne_zero hz_ne)
      have hz_mem : z ∈ primitiveExtremeBox :=
        ⟨hz_ne, hz_bounds, hz_primitive, hz_extreme⟩
      rw [← hzs_range] at hz_mem
      rcases hz_mem with ⟨t, rfl⟩
      exact ⟨t, hsame⟩
  · intro t
    -- The enumerated rays are integer vectors by construction.
    exact intCastVector_mem_integerVectors (zs t)
  · intro t j
    -- Nonnegativity and `Δ ≥ 0` convert the `[0, Δ]` bounds into `[-Δ, Δ]`.
    have ht_mem : zs t ∈ primitiveExtremeBox := by
      rw [← hzs_range]
      exact ⟨t, rfl⟩
    constructor
    · have hzj_nonneg_real : (0 : ℝ) ≤ rays t j := by
        simpa [rays] using (show (0 : ℝ) ≤ (zs t j : ℝ) by exact_mod_cast (ht_mem.2.1 j).1)
      have hΔ_nonneg_real : (0 : ℝ) ≤ (Δ : ℝ) := by
        exact_mod_cast hΔ_nonneg
      linarith
    · simpa [rays] using (show (zs t j : ℝ) ≤ (Δ : ℝ) by exact_mod_cast (ht_mem.2.1 j).2)

end Exercise518
