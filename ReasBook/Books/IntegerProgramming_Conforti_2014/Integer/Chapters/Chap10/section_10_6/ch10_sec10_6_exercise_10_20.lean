/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Tactic.Recall
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_4.ch10_sec10_4_1_proposition_10_12

/- Source/core/bridge triage for Exercise 10.20:
* `source-facing`: the textbook item only recalls the Sherali-Adams truncated moment vector, its
  generator family, the relaxation `R_t`, their direct coordinate/membership companion API, and
  the Proposition 10.12 coordinate inequalities.
* `core/canonical`: Chapter 10.4 already owns these declarations as
  `sherali_adams_moment_vector`, `sherali_adams_moment_vectors`,
  `sherali_adams_relaxation`, their companion unfold/apply/membership lemmas, and the four
  coordinate theorems.
* `bridge/view`: this file is therefore recall-only and keeps no parallel local wrapper API. -/
-- Route correction: this exercise does not introduce a new local theorem body; it re-exposes the
-- canonical Proposition 10.12 API from Section 10.4, so proof search here would be spurious.
recall sherali_adams_moment_vector {n : ℕ} (t : ℕ) (x : Fin n → ℝ) :
    Finset (Fin n) → ℝ
recall sherali_adams_moment_vector_apply_of_card_le {n t : ℕ} {x : Fin n → ℝ}
    {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vector t x I = I.prod x
recall sherali_adams_moment_vector_apply_of_card_gt {n t : ℕ} {x : Fin n → ℝ}
    {I : Finset (Fin n)} (hI : t + 1 < I.card) :
    sherali_adams_moment_vector t x I = 0
recall sherali_adams_moment_vectors {n : ℕ} (P : Set (Fin n → ℝ)) (t : ℕ) :
    Set (Finset (Fin n) → ℝ)
recall mem_sherali_adams_moment_vectors_iff {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {y : Finset (Fin n) → ℝ} :
    y ∈ sherali_adams_moment_vectors P t ↔
      ∃ x ∈ zero_one_points (Nat.le_refl n) P, sherali_adams_moment_vector t x = y
recall sherali_adams_relaxation {n : ℕ} (P : Set (Fin n → ℝ)) (t : ℕ) :
    Set (Finset (Fin n) → ℝ)
recall sherali_adams_relaxation_def {n : ℕ} (P : Set (Fin n → ℝ)) (t : ℕ) :
    sherali_adams_relaxation P t = convexHull ℝ (sherali_adams_moment_vectors P t)
recall mem_sherali_adams_relaxation_iff {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {y : Finset (Fin n) → ℝ} :
    y ∈ sherali_adams_relaxation P t ↔ y ∈ convexHull ℝ (sherali_adams_moment_vectors P t)
recall sherali_adams_moment_vectors_subset_relaxation {n : ℕ} (P : Set (Fin n → ℝ)) (t : ℕ) :
    sherali_adams_moment_vectors P t ⊆ sherali_adams_relaxation P t
recall sherali_adams_moment_vector_mem_relaxation {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ zero_one_points (Nat.le_refl n) P) :
    sherali_adams_moment_vector t x ∈ sherali_adams_relaxation P t
recall sheraliAdamsMomentVector_apply_eq_indicator_of_memZeroOnePoints {n : ℕ}
    {P : Set (Fin n → ℝ)} {t : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ zero_one_points (Nat.le_refl n) P) {I : Finset (Fin n)}
    (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vector t x I = if ∀ i ∈ I, x i = 1 then 1 else 0
recall sheraliAdamsMomentVectors_subset_nonnegativeCoordinate {n : ℕ} {P : Set (Fin n → ℝ)}
    {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y | 0 ≤ y I}
recall sheraliAdamsMomentVectors_subset_coordinateOrder {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {I J : Finset (Fin n)} (hJI : J ⊆ I) (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y | y I ≤ y J}
recall sheraliAdamsMomentVectors_subset_coordinateUpperBound {n : ℕ} {P : Set (Fin n → ℝ)}
    {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    sherali_adams_moment_vectors P t ⊆ {y | y I ≤ 1}
recall sheraliAdamsMomentVectors_subset_coordinateZeroHyperplane_of_emptyAllOneFace {n : ℕ}
    {P : Set (Fin n → ℝ)} {t : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ t + 1)
    (hface : {x | x ∈ P ∧ ∀ i ∈ I, x i = 1} = ∅) :
    sherali_adams_moment_vectors P t ⊆ {y | y I = 0}
recall sherali_adams_coordinate_nonneg {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {y : Finset (Fin n) → ℝ} (hy : y ∈ sherali_adams_relaxation P t)
    {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    0 ≤ y I
recall sherali_adams_coordinate_monotone {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {y : Finset (Fin n) → ℝ} (hy : y ∈ sherali_adams_relaxation P t)
    {I J : Finset (Fin n)} (hJI : J ⊆ I) (hI : I.card ≤ t + 1) :
    y I ≤ y J
recall sherali_adams_coordinate_le_one {n : ℕ} {P : Set (Fin n → ℝ)} {t : ℕ}
    {y : Finset (Fin n) → ℝ} (hy : y ∈ sherali_adams_relaxation P t)
    {I : Finset (Fin n)} (hI : I.card ≤ t + 1) :
    y I ≤ 1
recall sherali_adams_coordinate_eq_zero_of_empty_all_one_face {n : ℕ} {P : Set (Fin n → ℝ)}
    {t : ℕ} {y : Finset (Fin n) → ℝ} (hy : y ∈ sherali_adams_relaxation P t)
    {I : Finset (Fin n)} (hI : I.card ≤ t + 1) (hface : {x | x ∈ P ∧ ∀ i ∈ I, x i = 1} = ∅) :
    y I = 0
