/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped BigOperators

section Proposition1012

variable {n : ℕ}

/-- The degree-`t + 1` truncated Sherali-Adams moment vector attached to `x`. Coordinates indexed
by larger subsets are set to `0`. -/
def sherali_adams_moment_vector (t : ℕ) (x : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  fun I ↦ if I.card ≤ t + 1 then I.prod x else 0

/-- On subsets of size at most `t + 1`, `sherali_adams_moment_vector t x` agrees with the monomial
`∏ i ∈ I, x i`. -/
theorem sherali_adams_moment_vector_apply_of_card_le
    {t : ℕ} {x : Fin n → ℝ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vector t x I = I.prod x := by
  simp [sherali_adams_moment_vector, hI]

/-- On subsets of size greater than `t + 1`, `sherali_adams_moment_vector t x` vanishes. -/
theorem sherali_adams_moment_vector_apply_of_card_gt
    {t : ℕ} {x : Fin n → ℝ} {I : Finset (Fin n)} (hI : t + 1 < I.card) :
    sherali_adams_moment_vector t x I = 0 := by
  simp [sherali_adams_moment_vector, Nat.not_le.mpr hI]

/-- The truncated moment vectors of the binary points of `P`. -/
def sherali_adams_moment_vectors (P : Set (Fin n → ℝ)) (t : ℕ) :
    Set (Finset (Fin n) → ℝ) :=
  Set.range fun x : {x : Fin n → ℝ // x ∈ zero_one_points (Nat.le_refl n) P} ↦
    sherali_adams_moment_vector t x.1

/-- Membership in `sherali_adams_moment_vectors P t` means that the function is the truncated
moment vector of some binary point of `P`. -/
theorem mem_sherali_adams_moment_vectors_iff
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ} :
    y ∈ sherali_adams_moment_vectors P t ↔
      ∃ x : Fin n → ℝ,
        x ∈ zero_one_points (Nat.le_refl n) P ∧ sherali_adams_moment_vector t x = y := by
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The truncated Sherali-Adams lift `R_t` of `P`, modeled here as the convex hull of the
degree-`t + 1` moment vectors of the binary points of `P`. -/
def sherali_adams_relaxation (P : Set (Fin n → ℝ)) (t : ℕ) :
    Set (Finset (Fin n) → ℝ) :=
  convexHull ℝ (sherali_adams_moment_vectors P t)

namespace SheraliAdamsNotation

scoped notation:max "R_{" t "}(" P ")" => sherali_adams_relaxation P t

end SheraliAdamsNotation

open scoped SheraliAdamsNotation

/-- The Sherali-Adams relaxation is definitionally the convex hull of the truncated moment vectors
of the binary points of `P`. -/
theorem sherali_adams_relaxation_def
    (P : Set (Fin n → ℝ)) (t : ℕ) :
    R_{t}(P) = convexHull ℝ (sherali_adams_moment_vectors P t) :=
  rfl

/-- Membership in `R_{t}(P)` unfolds to membership in the convex hull of the truncated moment
vectors of the binary points of `P`. -/
theorem mem_sherali_adams_relaxation_iff
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ} :
    y ∈ R_{t}(P) ↔
      y ∈ convexHull ℝ (sherali_adams_moment_vectors P t) :=
  Iff.rfl

/-- Every truncated moment vector of a binary point of `P` lies in `R_t(P)`. -/
theorem sherali_adams_moment_vectors_subset_relaxation
    (P : Set (Fin n → ℝ)) (t : ℕ) :
    sherali_adams_moment_vectors P t ⊆ R_{t}(P) :=
  subset_convexHull ℝ (sherali_adams_moment_vectors P t)

/-- The truncated moment vector of a binary point of `P` belongs to `R_t(P)`. -/
theorem sherali_adams_moment_vector_mem_relaxation
    {P : Set (Fin n → ℝ)} {t : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ zero_one_points (Nat.le_refl n) P) :
    sherali_adams_moment_vector t x ∈ R_{t}(P) :=
  sherali_adams_moment_vectors_subset_relaxation P t ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Proposition 10.12: on a binary feasible point, each truncated moment coordinate is
the indicator of the event that all variables in the index set are equal to `1`. -/
lemma sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints
    {P : Set (Fin n → ℝ)} {t : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ zero_one_points (Nat.le_refl n) P) {I : Finset (Fin n)}
    (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vector t x I = if ∀ i ∈ I, x i = 1 then 1 else 0 := by
  classical
  -- First reduce the truncated coordinate to the product of the binary coordinates on `I`.
  rw [sherali_adams_moment_vector_apply_of_card_le hI]
  rw [mem_zero_one_points_iff (Nat.le_refl n) P x] at hx
  rcases hx with ⟨_, hx01raw⟩
  have hx01 : ∀ i : Fin n, x i = 0 ∨ x i = 1 := by
    simpa using hx01raw
  -- A product of binary scalars is `1` exactly when every factor is `1`, and otherwise it is `0`.
  have hprodIndicator :
      ∀ K : Finset (Fin n), K.prod x = if ∀ i ∈ K, x i = 1 then 1 else 0 := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        have hxa01 : x a = 0 ∨ x a = 1 := hx01 a
        by_cases hxa1 : x a = 1
        · simp [Finset.prod_insert, ha, hxa1, hs]
        · have hxa0 : x a = 0 := by
            rcases hxa01 with hxa0 | hxa1'
            · exact hxa0
            · exact False.elim (hxa1 hxa1')
          simp [Finset.prod_insert, ha, hxa0, hs]
  exact hprodIndicator I

/-- Helper for Proposition 10.12: every Sherali-Adams generator satisfies the nonnegativity
constraint on the coordinate indexed by `I`. -/
lemma sheraliAdamsMomentVectors_subset_nonnegativeCoordinate
    {P : Set (Fin n → ℝ)} {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y : Finset (Fin n) → ℝ | 0 ≤ y I} := by
  intro y hy
  rcases (mem_sherali_adams_moment_vectors_iff.mp hy) with ⟨x, hx, rfl⟩
  -- The generator coordinate is an indicator, hence either `0` or `1`.
  dsimp
  rw [sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints hx hI]
  by_cases hAll : ∀ i ∈ I, x i = 1
  · rw [if_pos hAll]
    norm_num
  · rw [if_neg hAll]

/-- Helper for Proposition 10.12: every Sherali-Adams generator satisfies the monotonicity
constraint `y I ≤ y J` whenever `J ⊆ I`. -/
lemma sheraliAdamsMomentVectors_subset_coordinateOrder
    {P : Set (Fin n → ℝ)} {t : ℕ} {I J : Finset (Fin n)}
    (hJI : J ⊆ I) (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y : Finset (Fin n) → ℝ | y I ≤ y J} := by
  intro y hy
  rcases (mem_sherali_adams_moment_vectors_iff.mp hy) with ⟨x, hx, rfl⟩
  have hJ : J.card ≤ t + 1 := le_trans (Finset.card_le_card hJI) hI
  -- Inclusion `J ⊆ I` means the all-ones condition on `I` forces the one on `J`.
  dsimp
  rw [sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints hx hI]
  rw [sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints hx hJ]
  by_cases hAllI : ∀ i ∈ I, x i = 1
  · have hAllJ : ∀ j ∈ J, x j = 1 := by
      intro j hj
      exact hAllI j (hJI hj)
    rw [if_pos hAllI, if_pos hAllJ]
  · by_cases hAllJ : ∀ j ∈ J, x j = 1
    · rw [if_neg hAllI, if_pos hAllJ]
      norm_num
    · rw [if_neg hAllI, if_neg hAllJ]

/-- Helper for Proposition 10.12: every Sherali-Adams generator satisfies the upper bound
constraint on the coordinate indexed by `I`. -/
lemma sheraliAdamsMomentVectors_subset_coordinateUpperBound
    {P : Set (Fin n → ℝ)} {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y : Finset (Fin n) → ℝ | y I ≤ 1} := by
  intro y hy
  rcases (mem_sherali_adams_moment_vectors_iff.mp hy) with ⟨x, hx, rfl⟩
  -- The same indicator rewrite bounds the coordinate above by `1`.
  dsimp
  rw [sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints hx hI]
  by_cases hAll : ∀ i ∈ I, x i = 1
  · rw [if_pos hAll]
  · rw [if_neg hAll]
    norm_num

/-- Helper for Proposition 10.12: if the all-ones face on `I` is empty, then every Sherali-Adams
generator has zero `I`-coordinate. -/
lemma sheraliAdamsMomentVectors_subset_coordinateZeroHyperplane_of_emptyAllOneFace
    {P : Set (Fin n → ℝ)} {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1)
    (hface : {x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I, x i = 1} = (∅ : Set (Fin n → ℝ))) :
    sherali_adams_moment_vectors P t ⊆ {y : Finset (Fin n) → ℝ | y I = 0} := by
  intro y hy
  rcases (mem_sherali_adams_moment_vectors_iff.mp hy) with ⟨x, hx, rfl⟩
  have hxP : x ∈ P := (mem_zero_one_points_iff (Nat.le_refl n) P x).1 hx |>.1
  -- The all-ones branch would produce a point of the forbidden face.
  dsimp
  rw [sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints hx hI]
  by_cases hAll : ∀ i ∈ I, x i = 1
  · have hFalse : False := by
      have hxFace : x ∈ ({x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I, x i = 1} : Set (Fin n → ℝ)) :=
        ⟨hxP, hAll⟩
      simp [hface] at hxFace
    exact False.elim hFalse
  · simp [hAll]

/-- Proposition 10.12 (1). Let `y ∈ R_t`. Then `0 ≤ y_I` for every
`I ⊆ {1, ..., n}` with `|I| ≤ t + 1`. -/
theorem sherali_adams_coordinate_nonneg
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ}
    (hy : y ∈ R_{t}(P)) {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    0 ≤ y I := by
  -- The defining coordinate inequality holds on generators, so it holds on their convex hull.
  rw [mem_sherali_adams_relaxation_iff] at hy
  have hconv : Convex ℝ ({z : Finset (Fin n) → ℝ | 0 ≤ z I} : Set (Finset (Fin n) → ℝ)) := by
    -- Nonnegative coordinates are preserved by convex combinations.
    intro a ha b hb u v hu hv huv
    have haI : 0 ≤ a I := ha
    have hbI : 0 ≤ b I := hb
    simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    nlinarith
  exact convexHull_min
    (sheraliAdamsMomentVectors_subset_nonnegativeCoordinate (P := P) (t := t) (I := I) hI)
    hconv hy

/-- Proposition 10.12 (2). Let `y ∈ R_t`. Then `y_I ≤ y_J` whenever `J ⊆ I` and
`|I| ≤ t + 1`. -/
theorem sherali_adams_coordinate_monotone
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ}
    (hy : y ∈ R_{t}(P)) {I J : Finset (Fin n)} (hJI : J ⊆ I)
    (hI : I.card ≤ t + 1) :
    y I ≤ y J := by
  -- Convexity transfers the generator-wise coordinate order to every point of `R_t(P)`.
  rw [mem_sherali_adams_relaxation_iff] at hy
  have hconv : Convex ℝ ({z : Finset (Fin n) → ℝ | z I ≤ z J} : Set (Finset (Fin n) → ℝ)) := by
    -- Coordinatewise inequalities are stable under affine averaging.
    intro a ha b hb u v hu hv huv
    have haIJ : a I ≤ a J := ha
    have hbIJ : b I ≤ b J := hb
    simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    nlinarith
  exact convexHull_min
    (sheraliAdamsMomentVectors_subset_coordinateOrder (P := P) (t := t) (I := I) (J := J) hJI hI)
    hconv hy

/-- Proposition 10.12 (3). Let `y ∈ R_t`. Then `y_I ≤ 1` for every
`I ⊆ {1, ..., n}` with `|I| ≤ t + 1`. -/
theorem sherali_adams_coordinate_le_one
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ}
    (hy : y ∈ R_{t}(P)) {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    y I ≤ 1 := by
  -- The coordinate upper bound is likewise preserved by taking the convex hull.
  rw [mem_sherali_adams_relaxation_iff] at hy
  have hconv : Convex ℝ ({z : Finset (Fin n) → ℝ | z I ≤ 1} : Set (Finset (Fin n) → ℝ)) := by
    -- Bounding each endpoint by `1` bounds every convex combination by `1`.
    intro a ha b hb u v hu hv huv
    have haI : a I ≤ 1 := ha
    have hbI : b I ≤ 1 := hb
    simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    nlinarith [huv]
  exact convexHull_min
    (sheraliAdamsMomentVectors_subset_coordinateUpperBound (P := P) (t := t) (I := I) hI)
    hconv hy

/-- Proposition 10.12 (4). Let `y ∈ R_t` and let `I ⊆ {1, ..., n}` with `|I| ≤ t + 1`.
If the face `{x ∈ P : x_i = 1 for all i ∈ I}` is empty, then `y_I = 0`. -/
theorem sherali_adams_coordinate_eq_zero_of_empty_all_one_face
    {P : Set (Fin n → ℝ)} {t : ℕ} {y : Finset (Fin n) → ℝ}
    (hy : y ∈ R_{t}(P)) {I : Finset (Fin n)} (hI : I.card ≤ t + 1)
    (hface : {x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I, x i = 1} = (∅ : Set (Fin n → ℝ))) :
    y I = 0 := by
  -- Once every generator lies on the zero hyperplane, so does the whole relaxation.
  rw [mem_sherali_adams_relaxation_iff] at hy
  have hconv : Convex ℝ ({z : Finset (Fin n) → ℝ | z I = 0} : Set (Finset (Fin n) → ℝ)) := by
    -- Equality to zero is preserved by convex combinations.
    intro a ha b hb u v hu hv huv
    have haI : a I = 0 := ha
    have hbI : b I = 0 := hb
    simp only [Set.mem_setOf_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul, haI, hbI, mul_zero,
      add_zero]
  exact convexHull_min
    (sheraliAdamsMomentVectors_subset_coordinateZeroHyperplane_of_emptyAllOneFace
      (P := P) (t := t) (I := I) hI hface)
    hconv hy

end Proposition1012
