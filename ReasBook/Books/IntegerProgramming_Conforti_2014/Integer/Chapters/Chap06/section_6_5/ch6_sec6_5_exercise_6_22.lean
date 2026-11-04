/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

section Exercise622

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "ContAssignment" => ((Fin q → ℝ) →₀ NNReal)

/-- The one-column mixed-integer model from Exercise 6.22 with fixed direction `d` and one
nonnegative integer variable `z`, viewed as the slice of `M_f` whose integer assignment is
supported only at `d`. -/
def exercise_6_22_direction_relaxation_set
    (f : Rq)
    (d : Rq) : Set (ℕ × ContAssignment) :=
  {zy | (Finsupp.single d zy.1, zy.2) ∈ mixed_integer_relaxation_set f}

/-- Membership in the one-column slice means that the integer assignment in `M_f` is the single
column `z e_d`, with the same continuous assignment `y`. -/
@[simp] theorem mem_exercise_6_22_direction_relaxation_set_iff
    {f : Rq}
    {d : Rq}
    {z : ℕ}
    {y : ContAssignment} :
    (z, y) ∈ exercise_6_22_direction_relaxation_set f d ↔
      (Finsupp.single d z, y) ∈ mixed_integer_relaxation_set f :=
  Iff.rfl

/-- A scalar `λ` is valid for the Exercise 6.22 model in direction `d` when the inequality
`∑_r ψ(r) y_r + λ z ≥ 1` holds on every feasible point. -/
def exercise_6_22_direction_coefficient_valid
    (f : Rq)
    (ψ : Rq → ℝ)
    (d : Rq)
    (lam : ℝ) : Prop :=
  ∀ {z : ℕ} {y : ContAssignment},
    (z, y) ∈ exercise_6_22_direction_relaxation_set f d →
      1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) + lam * (z : ℝ)

/-- `exercise_6_22_is_minimum_lifting_coefficient f ψ d λ` means that `λ` is the minimum scalar
whose inequality is valid for the one-column model in direction `d`. -/
def exercise_6_22_is_minimum_lifting_coefficient
    (f : Rq)
    (ψ : Rq → ℝ)
    (d : Rq)
    (lam : ℝ) : Prop :=
  exercise_6_22_direction_coefficient_valid f ψ d lam ∧
    ∀ μ : ℝ,
      exercise_6_22_direction_coefficient_valid f ψ d μ →
        lam ≤ μ

namespace exercise_6_22_is_minimum_lifting_coefficient

/-- A minimum lifting coefficient is, in particular, a valid coefficient for the one-column
model. -/
theorem valid
    {f : Rq}
    {ψ : Rq → ℝ}
    {d : Rq}
    {lam : ℝ}
    (hlam : exercise_6_22_is_minimum_lifting_coefficient f ψ d lam) :
    exercise_6_22_direction_coefficient_valid f ψ d lam :=
  hlam.1

/-- A minimum lifting coefficient is bounded above by every other valid one-column coefficient. -/
theorem le
    {f : Rq}
    {ψ : Rq → ℝ}
    {d : Rq}
    {lam μ : ℝ}
    (hlam : exercise_6_22_is_minimum_lifting_coefficient f ψ d lam)
    (hμ : exercise_6_22_direction_coefficient_valid f ψ d μ) :
    lam ≤ μ :=
  hlam.2 μ hμ

end exercise_6_22_is_minimum_lifting_coefficient

namespace IsValidGomoryJohnsonPair

/-- Restricting a valid mixed-integer inequality to the one-column slice in direction `d` shows
that the coefficient `π d` is valid for Exercise 6.22's scalar lifting problem. -/
theorem exercise_6_22_direction_coefficient_valid
    {f : Rq}
    {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (d : Rq) :
    exercise_6_22_direction_coefficient_valid f ψ d (π d) := by
  intro z y hzy
  have hxy : (Finsupp.single d z, y) ∈ mixed_integer_relaxation_set f := by
    simpa using hzy
  simpa [add_comm] using hπψ.one_le hxy

end IsValidGomoryJohnsonPair

/-- Exercise 6.22 (1). If `πₗ d` is, for every direction `d`, the minimum scalar whose
inequality is valid for the one-column model of the exercise, and if `(πₗ, ψ)` is valid for the
mixed-integer relaxation, then `πₗ` is a minimal lifting of `ψ`. -/
theorem exercise_6_22_pi_l_is_minimal_lifting
    (f : Rq)
    (ψ pi_l : Rq → ℝ)
    (hpi_l :
      ∀ d : Rq, exercise_6_22_is_minimum_lifting_coefficient f ψ d (pi_l d))
    (hvalid : IsValidGomoryJohnsonPair f pi_l ψ) :
    IsMinimalLiftingOf f pi_l ψ := by
  refine
    { toIsValidGomoryJohnsonPair := hvalid
      eq_of_le := ?_ }
  intro π hπ hπ_le
  ext d
  exact le_antisymm (hπ_le d) ((hpi_l d).le (hπ.exercise_6_22_direction_coefficient_valid d))

/-- Exercise 6.22 (2). If every `πₗ d` is the minimum valid one-column coefficient and `(πₗ, ψ)`
is a lifting, then every minimal lifting of `ψ` coincides with `πₗ`; equivalently, `πₗ` is the
unique minimal lifting of `ψ`. -/
theorem exercise_6_22_eq_pi_l_of_minimal_lifting
    (f : Rq)
    (ψ pi_l : Rq → ℝ)
    (hpi_l :
      ∀ d : Rq, exercise_6_22_is_minimum_lifting_coefficient f ψ d (pi_l d))
    (hvalid : IsValidGomoryJohnsonPair f pi_l ψ)
    {π : Rq → ℝ}
    (hπ : IsMinimalLiftingOf f π ψ) :
    π = pi_l := by
  have hπvalid : IsValidGomoryJohnsonPair f π ψ :=
    hπ.toIsValidGomoryJohnsonPair
  have hpi_l_le : pi_l ≤ π := by
    intro d
    exact (hpi_l d).le (hπvalid.exercise_6_22_direction_coefficient_valid d)
  simpa using (hπ.eq_of_le hvalid hpi_l_le).symm

end Exercise622
