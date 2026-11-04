/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Rat
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_5.ch5_sec5_2_5_theorem_5_19

open IsLocalization
open scoped BigOperators

-- Domain-style sampling for this refine pass:
-- * primary domain: support cuts from rational tableau rows and Chapter 5 lexicographic
--   cutting-plane runs
-- * source-facing declarations kept here: `nonintegralCoefficientSupport`,
--   `exercise514SolutionSet`, `nonintegralCoefficientSupportCut`,
--   `NonintegralCoefficientSupportLexicographicCuttingPlaneMethod`,
--   and the Exercise 5.14 termination theorem
-- * nearby declarations inspected:
--   `GomoryLexicographicCuttingPlaneMethod`,
--   `periodic_gomory_fractional_cutting_plane_method_terminates`,
--   `mixed_integer_gomory_lexicographic_cutting_plane_method_terminates`

-- Semantic recall note: this exercise uses mathlib's canonical rational-integrality predicate
-- `IsLocalization.IsInteger ℤ` for the support cut. For Exercise 5.14(2), the local owner is a
-- source-facing variant parallel to the Chapter 5 lexicographic method owner, with the
-- nonterminal cut-adjoining clause replaced by the support cut from part (1) and with the
-- selected-row right-hand side data retained explicitly. The termination statement is routed
-- through an explicit bridge back to `GomoryLexicographicCuttingPlaneMethod` so the support-cut
-- run is not treated as an arbitrary unrelated abstract process.
-- Semantic search note: `lean_leansearch` did not surface a more specific owner, so this repair
-- follows the verified local Chapter 5 owner/API shape around
-- `GomoryLexicographicCuttingPlaneMethod`.

section Exercise514

variable {n : ℕ}

/-- A rational number is an integer exactly when its reduced denominator is `1`. -/
theorem rat_isInteger_iff_den_eq_one (q : ℚ) : IsInteger ℤ q ↔ q.den = 1 := by
  rw [Rat.isLocalizationIsInteger_iff, Rat.den_eq_one_iff]
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hq
    exact ⟨q.num, hq⟩

/-- The index set of nonintegral coefficients of the rational vector `a`. -/
def nonintegralCoefficientSupport (a : Fin n → ℚ) : Finset (Fin n) :=
  let _ : DecidablePred (fun j : Fin n ↦ ¬ IsInteger ℤ (a j)) := fun j ↦ by
      simpa [rat_isInteger_iff_den_eq_one] using
        (inferInstance : Decidable ((a j).den ≠ 1))
  Finset.univ.filter (fun j ↦ ¬ IsInteger ℤ (a j))

/-- Membership in `nonintegralCoefficientSupport a` is exactly nonintegrality of the coefficient
`a j`. -/
@[simp] theorem mem_nonintegralCoefficientSupport_iff
    (a : Fin n → ℚ)
    (j : Fin n) :
    j ∈ nonintegralCoefficientSupport a ↔ ¬ IsInteger ℤ (a j) := by
  simp [nonintegralCoefficientSupport]

/-- The set `S = {x ∈ ℤ_+^n : ∑ a_j x_j = b}` from Exercise 5.14. -/
def exercise514SolutionSet (a : Fin n → ℚ) (b : ℚ) : Set (Fin n → ℤ) :=
  {x | (∀ j : Fin n, 0 ≤ x j) ∧ ∑ j, a j * (x j : ℚ) = b}

/-- The cut `∑_{j ∈ J} x_j ≥ 1` attached to the nonintegral coefficient support `J`. -/
def nonintegralCoefficientSupportCut (a : Fin n → ℚ) : Set (Fin n → ℝ) :=
  {x | 1 ≤ Finset.sum (nonintegralCoefficientSupport a) fun j ↦ x j}

/-- Membership in `nonintegralCoefficientSupportCut a` is exactly the inequality
`∑_{j ∈ J} x_j ≥ 1`. -/
theorem mem_nonintegralCoefficientSupportCut_iff
    (a : Fin n → ℚ)
    (x : Fin n → ℝ) :
    x ∈ nonintegralCoefficientSupportCut a ↔
      1 ≤ Finset.sum (nonintegralCoefficientSupport a) fun j ↦ x j :=
  Iff.rfl

/-- Helper for Exercise 5.14: if every coordinate on the nonintegral coefficient support vanishes,
then the tableau-row sum is an integer. -/
private lemma sumIsIntegerOfVanishOnNonintegralSupport
    (a : Fin n → ℚ) (x : Fin n → ℤ)
    (hvanish : ∀ j ∈ nonintegralCoefficientSupport a, x j = 0) :
    IsInteger ℤ (∑ j, a j * (x j : ℚ)) := by
  -- First show that each coordinate contribution is integral, either because the coefficient is
  -- integral or because the corresponding variable vanishes on the support.
  have hterm : ∀ j : Fin n, IsInteger ℤ (a j * (x j : ℚ)) := by
    intro j
    by_cases hj : j ∈ nonintegralCoefficientSupport a
    · simpa [hvanish j hj] using (IsLocalization.isInteger_zero : IsInteger ℤ (0 : ℚ))
    · have haj_integer : IsInteger ℤ (a j) := by
        simpa using hj
      have hxj_integer : IsInteger ℤ ((x j : ℚ)) := by
        change ((x j : ℚ)) ∈ (algebraMap ℤ ℚ).rangeS
        exact RingHom.mem_rangeS_self (algebraMap ℤ ℚ) (x j)
      exact IsLocalization.isInteger_mul haj_integer hxj_integer
  -- Build the full sum from the coordinatewise integral contributions.
  have hsum :
      ∀ s : Finset (Fin n), IsInteger ℤ (Finset.sum s fun j ↦ a j * (x j : ℚ)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (IsLocalization.isInteger_zero : IsInteger ℤ (0 : ℚ))
    · intro j s hj hs
      simpa [Finset.sum_insert hj] using IsLocalization.isInteger_add (hterm j) hs
  simpa using hsum Finset.univ

/-- Helper for Exercise 5.14: every solution with nonintegral right-hand side uses some variable
whose coefficient is nonintegral. -/
private lemma exists_nonintegralSupport_index_of_mem_solutionSet
    (a : Fin n → ℚ) {b : ℚ} {x : Fin n → ℤ}
    (hx : x ∈ exercise514SolutionSet a b)
    (hb_nonintegral : ¬ IsInteger ℤ b) :
    ∃ j, j ∈ nonintegralCoefficientSupport a ∧ x j ≠ 0 := by
  rcases hx with ⟨_, hx_sum⟩
  -- If every support coordinate vanished, the tableau row would force `b` to be integral.
  by_contra hno
  have hvanish : ∀ j ∈ nonintegralCoefficientSupport a, x j = 0 := by
    intro j hj
    by_contra hxj_ne
    exact hno ⟨j, hj, hxj_ne⟩
  have hsum_integer : IsInteger ℤ (∑ j, a j * (x j : ℚ)) :=
    sumIsIntegerOfVanishOnNonintegralSupport a x hvanish
  have hb_integer : IsInteger ℤ b := by
    simpa [hx_sum] using hsum_integer
  exact hb_nonintegral hb_integer

/-- Exercise 5.14 (1). If `b` is positive and nonintegral, then every point of
`S = {x ∈ ℤ_+^n : ∑ a_j x_j = b}` satisfies the valid inequality
`∑_{j ∈ J} x_j ≥ 1`, where `J = {j : a_j ∉ ℤ}`. -/
theorem exercise_5_14_nonintegral_support_cut_valid
    (a : Fin n → ℚ)
    {b : ℚ}
    (hb_pos : 0 < b)
    (hb_nonintegral : ¬ IsInteger ℤ b) :
    ∀ ⦃x : Fin n → ℤ⦄, x ∈ exercise514SolutionSet a b →
      (fun j ↦ (x j : ℝ)) ∈ nonintegralCoefficientSupportCut a := by
  -- Keep the source-side positivity hypothesis in scope; the witness extraction route only uses
  -- the nonintegrality conclusion.
  have _ : b ≠ 0 := ne_of_gt hb_pos
  intro x hx
  rcases hx with ⟨hx_nonneg, hx_sum⟩
  -- Route correction: extract one nonzero variable on the nonintegral support, then lower-bound
  -- the support sum by that single coordinate.
  obtain ⟨j, hj_support, hxj_ne_zero⟩ :=
    exists_nonintegralSupport_index_of_mem_solutionSet a ⟨hx_nonneg, hx_sum⟩ hb_nonintegral
  rw [mem_nonintegralCoefficientSupportCut_iff]
  -- The chosen integer coordinate is nonnegative and nonzero, hence at least `1`.
  have hxj_pos : 0 < x j := lt_of_le_of_ne (hx_nonneg j) (Ne.symm hxj_ne_zero)
  have hxj_one_le : (1 : ℤ) ≤ x j := by
    simpa using (Int.add_one_le_iff.mpr hxj_pos)
  have hxj_one_le_real : (1 : ℝ) ≤ (x j : ℝ) := by
    exact_mod_cast hxj_one_le
  have hsupport_nonneg :
      ∀ i ∈ nonintegralCoefficientSupport a, 0 ≤ (x i : ℝ) := by
    intro i hi
    exact_mod_cast hx_nonneg i
  -- A single positive term already forces the whole support sum to be at least `1`.
  calc
    1 ≤ (x j : ℝ) := hxj_one_le_real
    _ ≤ Finset.sum (nonintegralCoefficientSupport a) fun i ↦ (x i : ℝ) := by
      exact Finset.single_le_sum hsupport_nonneg hj_support

/-- A stage-indexed lexicographic cutting-plane run for a bounded pure integer program whose
nonterminal step adjoins the support cut from Exercise 5.14 (1) coming from the selected tableau
row. The row right-hand side is retained explicitly because the support cut is source-faithful
only for positive nonintegral right-hand sides. -/
structure NonintegralCoefficientSupportLexicographicCuttingPlaneMethod (n : ℕ) where
  feasibleRegion : Set (Fin (n + 1) → ℝ)
  bounded_feasibleRegion : Bornology.IsBounded feasibleRegion
  relaxation : ℕ → Set (Fin n → ℝ)
  iterates : ℕ → Fin (n + 1) → ℝ
  iterates_mem_feasibleRegion : ∀ t : ℕ, iterates t ∈ feasibleRegion
  iterates_mem_relaxation : ∀ t : ℕ, (fun j ↦ iterates t j.succ) ∈ relaxation t
  selectedRow : ℕ → Option (Fin (n + 1))
  selectedRow_none_iff :
    ∀ t : ℕ, selectedRow t = none ↔
      ∀ k : Fin (n + 1), iterates t k ∈ Set.range (Int.cast : ℤ → ℝ)
  cutCoeff : ℕ → Fin n → ℚ
  cutRhs : ℕ → ℚ
  selectedRow_cutRhs_pos :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k → 0 < cutRhs t
  selectedRow_cutRhs_nonintegral :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k → ¬ IsInteger ℤ (cutRhs t)
  relaxation_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      relaxation (t + 1) =
        relaxation t ∩ nonintegralCoefficientSupportCut (cutCoeff t)
  lexicographically_nonincreasing :
    ∀ t : ℕ, toLex (iterates (t + 1)) ≤ toLex (iterates t)
  selectedRow_spec :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      (∀ i : Fin (n + 1), i < k → iterates t i ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        iterates t k ∉ Set.range (Int.cast : ℤ → ℝ)
  strict_progress_on_fractional_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      toLex (iterates (t + 1)) < toLex (iterates t)
  selectedRow_eventually_forces_floor :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄,
      selectedRow t = some k →
      ∀ {m : ℤ},
      iterates t k < (m : ℝ) + 1 →
      (∀ i : Fin (n + 1), i < k →
        ∃ z : ℤ, ∀ s ≥ t + 1, iterates s i = (z : ℝ)) →
      ∀ s ≥ t + 1, iterates s k ≤ (m : ℝ)

namespace NonintegralCoefficientSupportLexicographicCuttingPlaneMethod

/-- A support-cut lexicographic run stops at stage `t` when no tableau row is selected for the
next support cut. -/
def StopsAt
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n) (t : ℕ) : Prop :=
  A.selectedRow t = none

/-- Equipping the same iterate/selected-row run with the auxiliary Gomory cut data from the
Chapter 5 lexicographic method yields the canonical owner used for the termination theorem. -/
def toGomoryLexicographicCuttingPlaneMethod
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n)
    (cutColumns : ℕ → Finset (Fin n))
    (gomoryCutCoeff : ℕ → Fin n → ℚ)
    (gomoryCutRhs : ℕ → ℚ)
    (gomory_relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, A.selectedRow t = some k →
        A.relaxation (t + 1) =
          A.relaxation t ∩ gomory_fractional_cut (cutColumns t) (gomoryCutCoeff t)
            (gomoryCutRhs t)) :
    GomoryLexicographicCuttingPlaneMethod n where
  feasibleRegion := A.feasibleRegion
  bounded_feasibleRegion := A.bounded_feasibleRegion
  relaxation := A.relaxation
  iterates := A.iterates
  iterates_mem_feasibleRegion := A.iterates_mem_feasibleRegion
  iterates_mem_relaxation := A.iterates_mem_relaxation
  selectedRow := A.selectedRow
  selectedRow_none_iff := A.selectedRow_none_iff
  cutColumns := cutColumns
  cutCoeff := gomoryCutCoeff
  cutRhs := gomoryCutRhs
  relaxation_step := gomory_relaxation_step
  lexicographically_nonincreasing := A.lexicographically_nonincreasing
  selectedRow_spec := A.selectedRow_spec
  strict_progress_on_fractional_step := A.strict_progress_on_fractional_step
  selectedRow_eventually_forces_floor := A.selectedRow_eventually_forces_floor

/-- Helper for Exercise 5.14: the support-cut owner and its bridged Gomory owner have the same
stopping predicate. -/
@[simp] theorem toGomoryLexicographicCuttingPlaneMethod_stopsAt_iff
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n)
    (cutColumns : ℕ → Finset (Fin n))
    (gomoryCutCoeff : ℕ → Fin n → ℚ)
    (gomoryCutRhs : ℕ → ℚ)
    (gomory_relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, A.selectedRow t = some k →
        A.relaxation (t + 1) =
          A.relaxation t ∩ gomory_fractional_cut (cutColumns t) (gomoryCutCoeff t)
            (gomoryCutRhs t))
    (t : ℕ) :
    (A.toGomoryLexicographicCuttingPlaneMethod cutColumns gomoryCutCoeff gomoryCutRhs
      gomory_relaxation_step).StopsAt t ↔
      A.StopsAt t :=
  Iff.rfl

end NonintegralCoefficientSupportLexicographicCuttingPlaneMethod

/-- Exercise 5.14 (2). A lexicographic cutting-plane method for a pure integer program still
terminates in finitely many iterations when each nonterminal step adjoins the support cut from
part (1) instead of the Gomory fractional cut, provided the same iterate/selected-row run is
equipped with the auxiliary Gomory-cut step data needed to recover the canonical Chapter 5
lexicographic owner. -/
theorem nonintegral_coefficient_support_lexicographic_cutting_plane_method_terminates
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n)
    (cutColumns : ℕ → Finset (Fin n))
    (gomoryCutCoeff : ℕ → Fin n → ℚ)
    (gomoryCutRhs : ℕ → ℚ)
    (gomory_relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, A.selectedRow t = some k →
        A.relaxation (t + 1) =
          A.relaxation t ∩ gomory_fractional_cut (cutColumns t) (gomoryCutCoeff t)
            (gomoryCutRhs t)) :
    ∃ T : ℕ, A.StopsAt T := by
  -- Route correction: reuse the canonical Chapter 5 termination theorem through the explicit
  -- bridge instead of replaying the lexicographic descent argument here.
  obtain ⟨T, hT⟩ :=
    gomory_lexicographic_cutting_plane_method_terminates
      (A.toGomoryLexicographicCuttingPlaneMethod cutColumns gomoryCutCoeff gomoryCutRhs
        gomory_relaxation_step)
  -- Rewrite the bridged stopping predicate back to the support-cut owner.
  refine ⟨T, ?_⟩
  simpa only [NonintegralCoefficientSupportLexicographicCuttingPlaneMethod.StopsAt,
    GomoryLexicographicCuttingPlaneMethod.StopsAt] using hT

end Exercise514
