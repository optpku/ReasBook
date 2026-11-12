/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_theorem_3_35
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.PointedCore
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_lemma_5_4.MixedCut

open scoped Matrix

section Lemma59

variable {m nI nC : ℕ}

/-- `IsIntegralMixedConstraintPresentation A_I A_C b` means that every displayed coefficient of
the mixed-system matrix presentation and every right-hand-side entry is integral. This is the
source-faithful row-normalization premise used in Lemma 5.9 to rule out arbitrary nonintegral row
rescalings of the same mixed cut. -/
def IsIntegralMixedConstraintPresentation
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, ∀ j : Fin nI, ∃ z : ℤ, A_I i j = (z : ℝ)) ∧
    (∀ i : Fin m, ∀ j : Fin nC, ∃ z : ℤ, A_C i j = (z : ℝ)) ∧
    ∀ i : Fin m, ∃ z : ℤ, b i = (z : ℝ)

namespace IsIntegralMixedConstraintPresentation

/-- `IsIntegralMixedConstraintPresentation A_I A_C b` unpacks to integrality of the integer block,
the continuous block, and the right-hand side of the displayed matrix presentation. -/
theorem iff
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ) :
    IsIntegralMixedConstraintPresentation A_I A_C b ↔
      (∀ i : Fin m, ∀ j : Fin nI, ∃ z : ℤ, A_I i j = (z : ℝ)) ∧
        (∀ i : Fin m, ∀ j : Fin nC, ∃ z : ℤ, A_C i j = (z : ℝ)) ∧
        ∀ i : Fin m, ∃ z : ℤ, b i = (z : ℝ) :=
  Iff.rfl

/-- In an integral mixed constraint presentation, each coefficient of the integer block is an
integer. -/
theorem exists_int_A_I
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (i : Fin m)
    (j : Fin nI) :
    ∃ z : ℤ, A_I i j = (z : ℝ) :=
  hInt.1 i j

/-- In an integral mixed constraint presentation, each coefficient of the continuous block is an
integer. -/
theorem exists_int_A_C
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (i : Fin m)
    (j : Fin nC) :
    ∃ z : ℤ, A_C i j = (z : ℝ) :=
  hInt.2.1 i j

/-- In an integral mixed constraint presentation, each right-hand-side entry is an integer. -/
theorem exists_int_b
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (i : Fin m) :
    ∃ z : ℤ, b i = (z : ℝ) :=
  hInt.2.2 i

end IsIntegralMixedConstraintPresentation

/-- `IsLargestAbsSubdeterminantBound A_C Δ` means that `Δ` is the largest among `1`
and the absolute values of all square subdeterminants of `A_C`. -/
def IsLargestAbsSubdeterminantBound
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (Δ : ℝ) : Prop :=
  1 ≤ Δ ∧
    (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
      |(A_C.submatrix rows cols).det| ≤ Δ) ∧
    (Δ = 1 ∨
      ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
        Δ = |(A_C.submatrix rows cols).det|)

namespace IsLargestAbsSubdeterminantBound

/-- `IsLargestAbsSubdeterminantBound A_C Δ` unpacks to the lower bound `1 ≤ Δ`, the
subdeterminant upper bound, and attainment either at `1` or at a square subdeterminant. -/
theorem iff
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (Δ : ℝ) :
    IsLargestAbsSubdeterminantBound A_C Δ ↔
      1 ≤ Δ ∧
        (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
          |(A_C.submatrix rows cols).det| ≤ Δ) ∧
        (Δ = 1 ∨
          ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
            Δ = |(A_C.submatrix rows cols).det|) :=
  Iff.rfl

/-- The parameter in `IsLargestAbsSubdeterminantBound A_C Δ` is at least `1`. -/
theorem one_le
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {Δ : ℝ}
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ) :
    1 ≤ Δ :=
  hΔ.1

/-- Every square subdeterminant of `A_C` has absolute value at most `Δ` when
`IsLargestAbsSubdeterminantBound A_C Δ` holds. -/
theorem abs_subdet_le
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {Δ : ℝ}
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ)
    {k : ℕ}
    (rows : Fin k ↪ Fin m)
    (cols : Fin k ↪ Fin nC) :
    |(A_C.submatrix rows cols).det| ≤ Δ :=
  hΔ.2.1 rows cols

/-- A largest absolute subdeterminant bound is attained either by `1` itself or by the absolute
value of a square subdeterminant of `A_C`. -/
theorem eq_one_or_exists_abs_subdet_eq
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {Δ : ℝ}
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ) :
    Δ = 1 ∨
      ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
        Δ = |(A_C.submatrix rows cols).det| :=
  hΔ.2.2

/-- If `Δ ≠ 1`, then `IsLargestAbsSubdeterminantBound A_C Δ` is attained by the absolute
value of a square subdeterminant of `A_C`. -/
theorem exists_abs_subdet_eq_of_ne_one
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {Δ : ℝ}
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ)
    (hΔ_ne : Δ ≠ 1) :
    ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
      Δ = |(A_C.submatrix rows cols).det| := by
  rcases hΔ.eq_one_or_exists_abs_subdet_eq with hΔ_eq | hΔ_subdet
  · exact False.elim (hΔ_ne hΔ_eq)
  · exact hΔ_subdet

end IsLargestAbsSubdeterminantBound

/-- The slack-form value of the split inequality `(5.6)` generated by `u` on a slack vector `r`.
-/
private noncomputable abbrev split_cut_slack_value
    (u : Fin m → ℝ)
    (b : Fin m → ℝ)
    (r : Fin m → ℝ) : ℝ :=
  row_multiplier_pos u ⬝ᵥ r / Int.fract (u ⬝ᵥ b) +
    row_multiplier_neg u ⬝ᵥ r / (1 - Int.fract (u ⬝ᵥ b))

/-- `mixed_gomory_fractional_cut_value A_I A_C b u xy` is the mixed-point realization of the
slack-form expression `split_cut_slack_value`. -/
private theorem mixed_gomory_fractional_cut_value_eq_split_cut_slack_value
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (xy : MixedRealPoint nI nC) :
    mixed_gomory_fractional_cut_value A_I A_C b u xy =
      split_cut_slack_value u b (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) := by
  rw [split_cut_slack_value, mixed_gomory_fractional_cut_value_eq]

/-- The slack vector of a feasible mixed point belongs to the nonnegative orthant. -/
private theorem slack_mem_nonnegativeOrthant_of_mem_real_mixed_polyhedron
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    {xy : MixedRealPoint nI nC}
    (hxy : xy ∈ real_mixed_polyhedron A_I A_C b) :
    b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2) ∈ Set.Ici (0 : Fin m → ℝ) := by
  rw [Set.mem_Ici]
  intro i
  exact sub_nonneg.mpr ((mem_real_mixed_polyhedron_iff.mp hxy) i)

/-- `SplitCutStrictlyDominates A_I A_C b v u` means that the split inequality `(5.6)`
generated by `v` dominates the one generated by `u` on every nonnegative slack vector, and is
strict on at least one such slack vector. This is the source-faithful domination relation used in
Lemma 5.9. -/
def SplitCutStrictlyDominates
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (v u : Fin m → ℝ) : Prop :=
  IsMixedGomoryFractionalCutMultiplier A_I A_C b v ∧
    (∀ r ∈ Set.Ici (0 : Fin m → ℝ),
      split_cut_slack_value v b r ≤ split_cut_slack_value u b r) ∧
    ∃ r ∈ Set.Ici (0 : Fin m → ℝ),
      split_cut_slack_value v b r < split_cut_slack_value u b r

namespace SplitCutStrictlyDominates

/-- `SplitCutStrictlyDominates A_I A_C b v u` is exactly the conjunction of validity of the
dominating cut, pointwise dominance on the nonnegative orthant of slack vectors, and strictness at
one such slack vector. -/
theorem iff
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (v u : Fin m → ℝ) :
    SplitCutStrictlyDominates A_I A_C b v u ↔
      IsMixedGomoryFractionalCutMultiplier A_I A_C b v ∧
        (∀ r ∈ Set.Ici (0 : Fin m → ℝ),
          split_cut_slack_value v b r ≤ split_cut_slack_value u b r) ∧
        ∃ r ∈ Set.Ici (0 : Fin m → ℝ),
          split_cut_slack_value v b r < split_cut_slack_value u b r :=
  Iff.rfl

/-- A strictly dominating split cut is itself a mixed Gomory fractional cut multiplier. -/
theorem isMixedGomoryFractionalCutMultiplier
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {v u : Fin m → ℝ}
    (hdom : SplitCutStrictlyDominates A_I A_C b v u) :
    IsMixedGomoryFractionalCutMultiplier A_I A_C b v :=
  hdom.1

/-- Strict domination gives the pointwise slack inequality on the nonnegative orthant. -/
theorem split_cut_slack_value_le
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {v u : Fin m → ℝ}
    (hdom : SplitCutStrictlyDominates A_I A_C b v u)
    (r : Fin m → ℝ)
    (hr : r ∈ Set.Ici (0 : Fin m → ℝ)) :
    split_cut_slack_value v b r ≤ split_cut_slack_value u b r :=
  hdom.2.1 r hr

/-- Strict domination is witnessed by a nonnegative slack vector where the dominating cut value is
strictly smaller. -/
theorem exists_lt_split_cut_slack_value
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {v u : Fin m → ℝ}
    (hdom : SplitCutStrictlyDominates A_I A_C b v u) :
    ∃ r ∈ Set.Ici (0 : Fin m → ℝ),
      split_cut_slack_value v b r < split_cut_slack_value u b r :=
  hdom.2.2

/-- Slack-form strict domination implies the ambient pointwise cut inequality on every feasible
mixed point through evaluation at its nonnegative slack vector. -/
theorem mixed_gomory_fractional_cut_value_le
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {v u : Fin m → ℝ}
    (hdom : SplitCutStrictlyDominates A_I A_C b v u)
    {xy : MixedRealPoint nI nC}
    (hxy : xy ∈ real_mixed_polyhedron A_I A_C b) :
    mixed_gomory_fractional_cut_value A_I A_C b v xy ≤
      mixed_gomory_fractional_cut_value A_I A_C b u xy := by
  have hslack :
      b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2) ∈ Set.Ici (0 : Fin m → ℝ) :=
    slack_mem_nonnegativeOrthant_of_mem_real_mixed_polyhedron A_I A_C b hxy
  rw [mixed_gomory_fractional_cut_value_eq_split_cut_slack_value,
    mixed_gomory_fractional_cut_value_eq_split_cut_slack_value]
  exact hdom.split_cut_slack_value_le _ hslack

end SplitCutStrictlyDominates

/-- `SplitCutIsUndominated A_I A_C b hInt u` is the source-facing statement that the split
inequality `(5.6)` generated by `u` is undominated under the slack-form comparison used in
Lemma 5.9, for the displayed integral matrix presentation. -/
def SplitCutIsUndominated
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (u : Fin m → ℝ) : Prop :=
  let _ : IsIntegralMixedConstraintPresentation A_I A_C b := hInt
  ∀ v : Fin m → ℝ, ¬ SplitCutStrictlyDominates A_I A_C b v u

namespace SplitCutIsUndominated

/-- `SplitCutIsUndominated A_I A_C b hInt u` means that no split cut strictly dominates the one
generated by `u` in the displayed integral matrix presentation. -/
theorem iff
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (u : Fin m → ℝ) :
    SplitCutIsUndominated A_I A_C b hInt u ↔
      ∀ v : Fin m → ℝ, ¬ SplitCutStrictlyDominates A_I A_C b v u :=
  Iff.rfl

/-- An undominated split cut admits no strictly dominating cut. -/
theorem not_strictly_dominates
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {hInt : IsIntegralMixedConstraintPresentation A_I A_C b}
    {u v : Fin m → ℝ}
    (hundom : SplitCutIsUndominated A_I A_C b hInt u) :
    ¬ SplitCutStrictlyDominates A_I A_C b v u :=
  hundom v

/-- An undominated split cut is equivalently characterized by the absence of a strictly
dominating witness. -/
theorem not_exists_strictly_dominates
    {A_I : Matrix (Fin m) (Fin nI) ℝ}
    {A_C : Matrix (Fin m) (Fin nC) ℝ}
    {b : Fin m → ℝ}
    {hInt : IsIntegralMixedConstraintPresentation A_I A_C b}
    {u : Fin m → ℝ}
    (hundom : SplitCutIsUndominated A_I A_C b hInt u) :
    ¬ ∃ v : Fin m → ℝ, SplitCutStrictlyDominates A_I A_C b v u := by
  rintro ⟨v, hdom⟩
  exact hundom.not_strictly_dominates hdom

end SplitCutIsUndominated

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: the sign-compatible face of
the kernel of `A_C` at `u`. -/
private def signCompatibleKernelCone
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (u : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {w | w ᵥ* A_C = 0 ∧
    ∀ i : Fin m, (0 ≤ u i → 0 ≤ w i) ∧ (u i ≤ 0 → w i ≤ 0)}

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: an integral kernel shift
preserves the mixed multiplier conditions and its right-hand-side fractional part. -/
private theorem mixedMultiplier_sub_integralKernel
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u)
    (z : Fin m → ℤ)
    (hzKernel : (fun i ↦ (z i : ℝ)) ᵥ* A_C = 0) :
    IsMixedGomoryFractionalCutMultiplier A_I A_C b (u - fun i ↦ (z i : ℝ)) ∧
      Int.fract ((u - fun i ↦ (z i : ℝ)) ⬝ᵥ b) = Int.fract (u ⬝ᵥ b) := by
  classical
  choose A_I_int hA_I_int using hInt.1
  choose b_int hb_int using hInt.2.2
  have hzA_I :
      ∀ j : Fin nI, ∃ q : ℤ, ((fun i ↦ (z i : ℝ)) ᵥ* A_I) j = (q : ℝ) := by
    intro j
    refine ⟨∑ i, z i * A_I_int i j, ?_⟩
    -- Entrywise integrality turns the finite row combination into an integer cast.
    simp [Matrix.vecMul, dotProduct, hA_I_int]
  have hzb : ∃ q : ℤ, (fun i ↦ (z i : ℝ)) ⬝ᵥ b = (q : ℝ) := by
    refine ⟨∑ i, z i * b_int i, ?_⟩
    -- The same finite-sum calculation applies to the integral right-hand side.
    simp [dotProduct, hb_int]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      rcases hu.1 j with ⟨p, hp⟩
      rcases hzA_I j with ⟨q, hq⟩
      refine ⟨p - q, ?_⟩
      -- Subtract the two integer-valued row products.
      rw [Matrix.sub_vecMul]
      simp only [Pi.sub_apply]
      rw [hp, hq]
      norm_num
    · -- Both summands annihilate the continuous block.
      rw [Matrix.sub_vecMul, hu.2.1, hzKernel, sub_zero]
    · rintro ⟨p, hp⟩
      rcases hzb with ⟨q, hq⟩
      apply hu.2.2
      refine ⟨p + q, ?_⟩
      calc
        u ⬝ᵥ b = (u - fun i ↦ (z i : ℝ)) ⬝ᵥ b +
            (fun i ↦ (z i : ℝ)) ⬝ᵥ b := by
              rw [sub_dotProduct]
              ring
        _ = (p : ℝ) + (q : ℝ) := by rw [hp, hq]
        _ = ((p + q : ℤ) : ℝ) := by norm_num
  · rcases hzb with ⟨q, hq⟩
    -- Fractional parts agree because the two scalar products differ by an integer.
    refine (Int.fract_eq_fract).2 ⟨-q, ?_⟩
    rw [sub_dotProduct, hq]
    norm_num

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: a conformal summand and
remainder can only decrease the positive and negative parts of a multiplier. -/
private theorem rowMultiplierParts_sub_le_of_signCompatible
    (u z : Fin m → ℝ)
    (hzSign : ∀ i : Fin m, (0 ≤ u i → 0 ≤ z i) ∧ (u i ≤ 0 → z i ≤ 0))
    (hremSign : ∀ i : Fin m,
      (0 ≤ u i → 0 ≤ (u - z) i) ∧ (u i ≤ 0 → (u - z) i ≤ 0)) :
    row_multiplier_pos (u - z) ≤ row_multiplier_pos u ∧
      row_multiplier_neg (u - z) ≤ row_multiplier_neg u := by
  constructor
  · intro i
    by_cases hui : 0 ≤ u i
    · have hzi : 0 ≤ z i := (hzSign i).1 hui
      have hremi : 0 ≤ (u - z) i := (hremSign i).1 hui
      rw [row_multiplier_pos, row_multiplier_pos, max_eq_left hremi, max_eq_left hui]
      simp only [Pi.sub_apply]
      exact sub_le_self _ hzi
    · have hui_nonpos : u i ≤ 0 := le_of_not_ge hui
      have hremi : (u - z) i ≤ 0 := (hremSign i).2 hui_nonpos
      rw [row_multiplier_pos, row_multiplier_pos, max_eq_right hremi, max_eq_right hui_nonpos]
  · intro i
    by_cases hui : 0 ≤ u i
    · have hremi : 0 ≤ (u - z) i := (hremSign i).1 hui
      have hneg_u : -u i ≤ 0 := neg_nonpos.mpr hui
      have hneg_rem : -(u - z) i ≤ 0 := neg_nonpos.mpr hremi
      rw [row_multiplier_neg, row_multiplier_neg, max_eq_right hneg_rem, max_eq_right hneg_u]
    · have hui_nonpos : u i ≤ 0 := le_of_not_ge hui
      have hzi : z i ≤ 0 := (hzSign i).2 hui_nonpos
      have hremi : (u - z) i ≤ 0 := (hremSign i).2 hui_nonpos
      have hneg_u : 0 ≤ -u i := neg_nonneg.mpr hui_nonpos
      have hneg_rem : 0 ≤ -(u - z) i := neg_nonneg.mpr hremi
      rw [row_multiplier_neg, row_multiplier_neg, max_eq_left hneg_rem, max_eq_left hneg_u]
      simp only [Pi.sub_apply]
      linarith

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: a nonzero conformal integral
kernel step gives a strictly dominating translated split cut. -/
private theorem splitCutStrictlyDominates_sub_integralKernel
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u)
    (z : Fin m → ℤ)
    (hz_ne : z ≠ 0)
    (hz_mem : (fun i ↦ (z i : ℝ)) ∈ signCompatibleKernelCone A_C u)
    (hrem_mem : (u - fun i ↦ (z i : ℝ)) ∈ signCompatibleKernelCone A_C u) :
    SplitCutStrictlyDominates A_I A_C b (u - fun i ↦ (z i : ℝ)) u := by
  let zR : Fin m → ℝ := fun i ↦ (z i : ℝ)
  have htransport := mixedMultiplier_sub_integralKernel A_I A_C b u hInt hu z hz_mem.1
  have hparts := rowMultiplierParts_sub_le_of_signCompatible u zR hz_mem.2 hrem_mem.2
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) := by
    have hnot_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
      simpa [Set.mem_range, eq_comm] using hu.2.2
    exact lt_of_le_of_ne (Int.fract_nonneg _)
      (Ne.symm ((Int.fract_ne_zero_iff).2 hnot_mem))
  have hone_sub_pos : 0 < 1 - Int.fract (u ⬝ᵥ b) := by
    linarith [Int.fract_lt_one (u ⬝ᵥ b)]
  refine (SplitCutStrictlyDominates.iff A_I A_C b _ _).2 ⟨htransport.1, ?_, ?_⟩
  · intro r hr
    have hr_nonneg : 0 ≤ r := by
      simpa [Set.mem_Ici] using hr
    have hpos_dot : row_multiplier_pos (u - zR) ⬝ᵥ r ≤ row_multiplier_pos u ⬝ᵥ r :=
      dotProduct_le_dotProduct_of_nonneg_right hparts.1 hr_nonneg
    have hneg_dot : row_multiplier_neg (u - zR) ⬝ᵥ r ≤ row_multiplier_neg u ⬝ᵥ r :=
      dotProduct_le_dotProduct_of_nonneg_right hparts.2 hr_nonneg
    -- Equal fractional parts leave only monotonicity of the two nonnegative-part numerators.
    dsimp [split_cut_slack_value]
    rw [htransport.2]
    exact add_le_add (div_le_div_of_nonneg_right hpos_dot hf_pos.le)
      (div_le_div_of_nonneg_right hneg_dot hone_sub_pos.le)
  · have hzR_ne : zR ≠ 0 := by
      intro hzR_zero
      apply hz_ne
      ext i
      have hi_cast : (z i : ℝ) = 0 := by
        simpa [zR] using congrFun hzR_zero i
      exact_mod_cast hi_cast
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hzR_ne
    have hzi : zR i ≠ 0 := by
      simpa using hi
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · -- A coordinate unit vector is a nonnegative slack vector.
      rw [Set.mem_Ici]
      intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Pi.single_eq_of_ne hji]
    · have hfract : Int.fract ((u - zR) ⬝ᵥ b) = Int.fract (u ⬝ᵥ b) := by
        simpa [zR] using htransport.2
      by_cases hui : 0 ≤ u i
      · have hzi_nonneg : 0 ≤ zR i := (hz_mem.2 i).1 hui
        have hzi_pos : 0 < zR i := lt_of_le_of_ne hzi_nonneg (Ne.symm hzi)
        have hrem_nonneg : 0 ≤ (u - zR) i := (hrem_mem.2 i).1 hui
        have hpos_strict : row_multiplier_pos (u - zR) i < row_multiplier_pos u i := by
          rw [row_multiplier_pos, row_multiplier_pos, max_eq_left hrem_nonneg, max_eq_left hui]
          simp only [Pi.sub_apply]
          linarith
        have hneg_eq : row_multiplier_neg (u - zR) i = row_multiplier_neg u i := by
          have hneg_u : -u i ≤ 0 := neg_nonpos.mpr hui
          have hneg_rem : -(u - zR) i ≤ 0 := neg_nonpos.mpr hrem_nonneg
          rw [row_multiplier_neg, row_multiplier_neg, max_eq_right hneg_rem, max_eq_right hneg_u]
        have hpos_div := div_lt_div_of_pos_right hpos_strict hf_pos
        have hneg_div :=
          congrArg (fun x : ℝ ↦ x / (1 - Int.fract (u ⬝ᵥ b))) hneg_eq
        dsimp [split_cut_slack_value]
        rw [hfract]
        simp only [dotProduct_single, mul_one]
        exact add_lt_add_of_lt_of_le hpos_div (le_of_eq hneg_div)
      · have hui_nonpos : u i ≤ 0 := le_of_not_ge hui
        have hzi_nonpos : zR i ≤ 0 := (hz_mem.2 i).2 hui_nonpos
        have hzi_neg : zR i < 0 := lt_of_le_of_ne hzi_nonpos hzi
        have hrem_nonpos : (u - zR) i ≤ 0 := (hrem_mem.2 i).2 hui_nonpos
        have hpos_eq : row_multiplier_pos (u - zR) i = row_multiplier_pos u i := by
          rw [row_multiplier_pos, row_multiplier_pos, max_eq_right hrem_nonpos,
            max_eq_right hui_nonpos]
        have hneg_strict : row_multiplier_neg (u - zR) i < row_multiplier_neg u i := by
          have hneg_u : 0 ≤ -u i := neg_nonneg.mpr hui_nonpos
          have hneg_rem : 0 ≤ -(u - zR) i := neg_nonneg.mpr hrem_nonpos
          rw [row_multiplier_neg, row_multiplier_neg, max_eq_left hneg_rem, max_eq_left hneg_u]
          simp only [Pi.sub_apply]
          linarith
        have hpos_div :=
          congrArg (fun x : ℝ ↦ x / Int.fract (u ⬝ᵥ b)) hpos_eq
        have hneg_div := div_lt_div_of_pos_right hneg_strict hone_sub_pos
        dsimp [split_cut_slack_value]
        rw [hfract]
        simp only [dotProduct_single, mul_one]
        exact add_lt_add_of_le_of_lt (le_of_eq hpos_div) hneg_div

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: stack an integral homogeneous
system and nonnegativity constraints into one inequality matrix. -/
private def integralNonnegativeKernelConstraintMatrix
    (B : Matrix (Fin nC) (Fin m) ℤ) :
    Matrix (Fin ((nC + nC) + m)) (Fin m) ℤ :=
  let equalities : Matrix (Fin (nC + nC)) (Fin m) ℤ :=
    (Matrix.fromRows B (-B)).reindex finSumFinEquiv (Equiv.refl _)
  (Matrix.fromRows equalities (-(1 : Matrix (Fin m) (Fin m) ℤ))).reindex
    finSumFinEquiv (Equiv.refl _)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: membership in the stacked
inequality system is equivalent to a nonnegative vector in the kernel. -/
private theorem mem_integralNonnegativeKernelConstraintMatrix_iff
    (B : Matrix (Fin nC) (Fin m) ℤ)
    (x : Fin m → ℝ) :
    x ∈ matrix_polyhedral_cone
          ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) ↔
      (B.map (Int.castRingHom ℝ)) *ᵥ x = 0 ∧ 0 ≤ x := by
  rw [mem_matrix_polyhedral_cone]
  constructor
  · intro hx
    constructor
    · ext i
      have hi_le := hx (Fin.castAdd m (Fin.castAdd nC i))
      have hi_neg_le := hx (Fin.castAdd m (Fin.natAdd nC i))
      have hBi_le : ((B.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ 0 := by
        simpa [integralNonnegativeKernelConstraintMatrix, Matrix.mulVec, dotProduct] using hi_le
      have hBi_ge : 0 ≤ ((B.map (Int.castRingHom ℝ)) *ᵥ x) i := by
        have hneg_row :
            (((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) *ᵥ x)
                (Fin.castAdd m (Fin.natAdd nC i)) =
              -((B.map (Int.castRingHom ℝ)) *ᵥ x) i := by
          have houter :
              finSumFinEquiv.symm (Fin.castAdd m (Fin.natAdd nC i)) =
                Sum.inl (i.addNat nC) := by
            apply finSumFinEquiv.injective
            simp
          have hinner : finSumFinEquiv.symm (i.addNat nC) = Sum.inr i := by
            apply finSumFinEquiv.injective
            simp
          simp [integralNonnegativeKernelConstraintMatrix, hinner,
            Matrix.mulVec, dotProduct]
        have hnegBi_le : -((B.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ (0 : ℝ) := by
          rw [← hneg_row]
          simpa using hi_neg_le
        exact neg_nonpos.mp hnegBi_le
      exact le_antisymm hBi_le hBi_ge
    · intro j
      have hj_le := hx (Fin.natAdd (nC + nC) j)
      have houter : finSumFinEquiv.symm (Fin.natAdd (nC + nC) j) = Sum.inr j := by
        apply finSumFinEquiv.injective
        simp
      have hneg_coord :
          (((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.natAdd (nC + nC) j) = -x j := by
        simp [integralNonnegativeKernelConstraintMatrix, houter, Matrix.mulVec, dotProduct,
          Matrix.one_apply]
      have hnegx_le : -x j ≤ (0 : ℝ) := by
        rw [← hneg_coord]
        simpa using hj_le
      exact neg_nonpos.mp hnegx_le
  · rintro ⟨hx_zero, hx_nonneg⟩ i
    cases houter : finSumFinEquiv.symm i with
    | inl r =>
        cases hinner : finSumFinEquiv.symm r with
        | inl iB =>
            have hBi : ((B.map (Int.castRingHom ℝ)) *ᵥ x) iB = 0 := by
              simpa using congrFun hx_zero iB
            simpa [integralNonnegativeKernelConstraintMatrix, houter, hinner,
              Matrix.mulVec, dotProduct] using hBi.le
        | inr iNegB =>
            have hBi : ((B.map (Int.castRingHom ℝ)) *ᵥ x) iNegB = 0 := by
              simpa using congrFun hx_zero iNegB
            have hnegBi : -((B.map (Int.castRingHom ℝ)) *ᵥ x) iNegB ≤ 0 := by
              linarith
            simpa [integralNonnegativeKernelConstraintMatrix, houter, hinner,
              Matrix.mulVec, dotProduct] using hnegBi
    | inr j =>
        have hnegx : -x j ≤ 0 := neg_nonpos.mpr (hx_nonneg j)
        simpa [integralNonnegativeKernelConstraintMatrix, houter, Matrix.mulVec, dotProduct,
          Matrix.one_apply] using hnegx

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: the cone of nonnegative
solutions to an integral homogeneous system is pointed. -/
private theorem integralNonnegativeKernelCone_pointed
    (B : Matrix (Fin nC) (Fin m) ℤ) :
    is_pointed
      (matrix_polyhedral_cone
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ))) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  have hzero_mem :
      (0 : Fin m → ℝ) ∈ matrix_polyhedral_cone
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) := by
    have hzero_data :
        (B.map (Int.castRingHom ℝ)) *ᵥ (0 : Fin m → ℝ) = 0 ∧
          0 ≤ (0 : Fin m → ℝ) := by
      simp
    exact (mem_integralNonnegativeKernelConstraintMatrix_iff B 0).2 hzero_data
  have hd_mem :
      d ∈ matrix_polyhedral_cone
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (1 : ℝ)
  have hnegd_mem :
      -d ∈ matrix_polyhedral_cone
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (-1 : ℝ)
  have hd_nonneg : 0 ≤ d := (mem_integralNonnegativeKernelConstraintMatrix_iff B d).1 hd_mem |>.2
  have hnegd_nonneg : 0 ≤ -d :=
    (mem_integralNonnegativeKernelConstraintMatrix_iff B (-d)).1 hnegd_mem |>.2
  ext j
  have hd_nonpos : d j ≤ 0 := by simpa using hnegd_nonneg j
  exact le_antisymm hd_nonpos (hd_nonneg j)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: an extreme-ray generator
belongs to its ambient cone. -/
private theorem extremeRayGenerator_mem
    {C : Set (Fin m → ℝ)}
    {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  have hr_source : r ∈ ({r} : Set (Fin m → ℝ)) := Set.mem_singleton r
  exact hr_edge.isExtreme.1 (PointedCone.subset_hull hr_source)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: the common zero set of
`m - 1` independent active rows is the line through a nonzero kernel vector. -/
private theorem mem_span_singleton_of_active_rows
    (M : Matrix (Fin nC) (Fin m) ℝ)
    {r s : Fin m → ℝ}
    (hr_ne : r ≠ 0)
    (I : Fin (m - 1) ↪ Fin nC)
    (hI_active : ∀ i : Fin (m - 1), (M *ᵥ r) (I i) = 0)
    (hI_independent : LinearIndependent ℝ (fun i : Fin (m - 1) ↦ M (I i)))
    (hs_zero : ∀ i : Fin (m - 1), (M *ᵥ s) (I i) = 0) :
    s ∈ Submodule.span ℝ ({r} : Set (Fin m → ℝ)) := by
  have hm_pos : 0 < m := by
    by_contra hm
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    apply hr_ne
    ext i
    exact Fin.elim0 i
  let N : Matrix (Fin (m - 1)) (Fin m) ℝ := fun i j ↦ M (I i) j
  have hN_rows : LinearIndependent ℝ N.row := by
    simpa [N, Matrix.row] using hI_independent
  have hN_rank : N.rank = m - 1 := by
    simpa [N] using LinearIndependent.rank_matrix hN_rows
  have hker_finrank : Module.finrank ℝ (LinearMap.ker N.mulVecLin) = 1 := by
    calc
      Module.finrank ℝ (LinearMap.ker N.mulVecLin) = m - N.rank := by
        simpa using finrank_matrix_kernel_eq_ambient_sub_rank N
      _ = m - (m - 1) := by rw [hN_rank]
      _ = 1 := by omega
  have hr_ker : r ∈ LinearMap.ker N.mulVecLin := by
    change N *ᵥ r = 0
    ext i
    simpa [N, Matrix.mulVec] using hI_active i
  have hs_ker : s ∈ LinearMap.ker N.mulVecLin := by
    change N *ᵥ s = 0
    ext i
    simpa [N, Matrix.mulVec] using hs_zero i
  have hr_sub_ne : (⟨r, hr_ker⟩ : LinearMap.ker N.mulVecLin) ≠ 0 := by
    intro hzero
    apply hr_ne
    exact congrArg Subtype.val hzero
  obtain ⟨a, ha⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (V := LinearMap.ker N.mulVecLin) hker_finrank
      (x := ⟨r, hr_ker⟩) hr_sub_ne ⟨s, hs_ker⟩
  have hs_eq : a • r = s := by
    simpa using congrArg Subtype.val ha
  exact Submodule.mem_span_singleton.mpr ⟨a, hs_eq⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: a vector on a real line can
be oriented onto one of its two rays. -/
private theorem sameRay_or_sameRay_neg_of_mem_span_singleton
    {r s : Fin m → ℝ}
    (hs : s ∈ Submodule.span ℝ ({r} : Set (Fin m → ℝ))) :
    SameRay ℝ r s ∨ SameRay ℝ r (-s) := by
  rcases Submodule.mem_span_singleton.mp hs with ⟨a, rfl⟩
  by_cases ha : 0 ≤ a
  · exact Or.inl (SameRay.sameRay_nonneg_smul_right r ha)
  · have hneg_a : 0 ≤ -a := by linarith
    have hsame : SameRay ℝ r (-(a • r)) := by
      simpa [neg_smul] using SameRay.sameRay_nonneg_smul_right r hneg_a
    exact Or.inr hsame

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: coercion to `ℝ` reflects
nonzeroness of an integer vector. -/
private theorem intCastVector_ne_zero
    {z : Fin m → ℤ}
    (hz : z ≠ 0) :
    (fun i ↦ (z i : ℝ)) ≠ 0 := by
  intro hcast
  apply hz
  ext i
  have hi : (z i : ℝ) = 0 := by simpa using congrFun hcast i
  exact_mod_cast hi

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: a same-ray integer vector
with a nonnegative kernel vector has nonnegative coordinates. -/
private theorem intCastVector_nonneg_of_sameRay
    {r : Fin m → ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_ne : r ≠ 0)
    {z : Fin m → ℤ}
    (hsame : SameRay ℝ r (fun i ↦ (z i : ℝ))) :
    ∀ i : Fin m, 0 ≤ z i := by
  obtain ⟨a, ha_nonneg, hz_eq⟩ := hsame.exists_nonneg_left hr_ne
  intro i
  have hi : 0 ≤ (z i : ℝ) := by
    calc
      0 ≤ a * r i := mul_nonneg ha_nonneg (hr_nonneg i)
      _ = (z i : ℝ) := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun hz_eq i
  exact_mod_cast hi

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: a full-row-rank matrix has
an invertible square submatrix on a choice of columns. -/
private theorem fullRowRankColumnBasisForKernel
    {r : ℕ} {c : Type*} [Finite c]
    (N : Matrix (Fin r) c ℝ)
    (hrows : LinearIndependent ℝ N.row) :
    ∃ J : Fin r ↪ c, IsUnit (N.submatrix id J) := by
  classical
  -- Local instance justification (finite indexing): matrix rank needs an explicit enumeration.
  letI : Fintype c := Fintype.ofFinite c
  let colSpace : Submodule ℝ (Fin r → ℝ) := Submodule.span ℝ (Set.range N.col)
  have hrank : N.rank = r := by simpa using LinearIndependent.rank_matrix hrows
  have hcol_finrank : Module.finrank ℝ colSpace = r := by
    calc
      Module.finrank ℝ colSpace = N.rank := by
        simpa [colSpace] using (Matrix.rank_eq_finrank_span_cols (A := N)).symm
      _ = r := hrank
  obtain ⟨cols, hcols_mem, _, hcols_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range N.col)
  have hcard_eq : Fintype.card (Fin (Module.finrank ℝ colSpace)) = Fintype.card (Fin r) := by
    simp [hcol_finrank]
  let e : Fin (Module.finrank ℝ colSpace) ≃ Fin r :=
    Fintype.equivOfCardEq hcard_eq
  let picked : Fin r → c := fun i ↦ Classical.choose (hcols_mem (e.symm i))
  have hpicked_eq : ∀ i : Fin r, N.col (picked i) = cols (e.symm i) := by
    intro i
    exact Classical.choose_spec (hcols_mem (e.symm i))
  have hpicked_linear : LinearIndependent ℝ (fun i : Fin r ↦ N.col (picked i)) := by
    have hreindexed : LinearIndependent ℝ (fun i : Fin r ↦ cols (e.symm i)) :=
      (linearIndependent_equiv e.symm).2 hcols_linear
    have heq : (fun i : Fin r ↦ N.col (picked i)) = fun i : Fin r ↦ cols (e.symm i) := by
      funext i
      exact hpicked_eq i
    exact heq ▸ hreindexed
  have hpicked_injective : Function.Injective picked := by
    intro i j hij
    apply hpicked_linear.injective
    simp [hij]
  let J : Fin r ↪ c := ⟨picked, hpicked_injective⟩
  have hsub_cols : LinearIndependent ℝ (N.submatrix id J).col := by
    simpa [J, Matrix.col, Matrix.submatrix_apply] using hpicked_linear
  exact ⟨J, (Matrix.linearIndependent_cols_iff_isUnit).1 hsub_cols⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: deleting one column from a
full-row-rank `r × (r + 1)` matrix leaves an invertible square block. -/
private theorem fullRowRankDeletedColumnBasisForKernel
    {r : ℕ}
    (N : Matrix (Fin r) (Fin (r + 1)) ℝ)
    (hrows : LinearIndependent ℝ N.row) :
    ∃ pivot : Fin (r + 1), IsUnit (N.submatrix id (Fin.succAbove pivot)) := by
  classical
  obtain ⟨J, hJunit⟩ := fullRowRankColumnBasisForKernel N hrows
  have hJ_cols : LinearIndependent ℝ (fun i : Fin r ↦ N.col (J i)) := by
    have hsub_cols : LinearIndependent ℝ (N.submatrix id J).col :=
      (Matrix.linearIndependent_cols_iff_isUnit).mpr hJunit
    simpa [Matrix.col, Matrix.submatrix_apply] using hsub_cols
  have hJ_not_surj : ¬ Function.Surjective J := by
    intro hsurj
    have hcard : r + 1 ≤ r := by simpa using Fintype.card_le_of_surjective J hsurj
    omega
  obtain ⟨pivot, hpivot⟩ : ∃ pivot : Fin (r + 1), pivot ∉ Set.range J := by
    by_contra hnone
    apply hJ_not_surj
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  have hJ_mem : ∀ i : Fin r, J i ≠ pivot := by
    intro i hJi
    exact hpivot ⟨i, hJi⟩
  let Jsub : Fin r → {x : Fin (r + 1) // x ≠ pivot} := fun i ↦ ⟨J i, hJ_mem i⟩
  have hJsub_bijective : Function.Bijective Jsub := by
    refine (Fintype.bijective_iff_injective_and_card Jsub).mpr ?_
    constructor
    · intro i j hij
      apply J.injective
      exact congrArg Subtype.val hij
    · simp
  let eJ : Fin r ≃ {x : Fin (r + 1) // x ≠ pivot} := Equiv.ofBijective Jsub hJsub_bijective
  let τ : Fin r ≃ Fin r := (finSuccAboveEquiv pivot).trans eJ.symm
  have hcanonical_cols :
      LinearIndependent ℝ (fun i : Fin r ↦ N.col (pivot.succAbove i)) := by
    have hperm :
        (fun i : Fin r ↦ N.col (pivot.succAbove i)) =
          fun i : Fin r ↦ N.col (J (τ i)) := by
      funext i
      have hsub : Jsub (τ i) = finSuccAboveEquiv pivot i := by
        exact eJ.apply_symm_apply (finSuccAboveEquiv pivot i)
      have hval : J (τ i) = pivot.succAbove i := congrArg Subtype.val hsub
      simp [hval]
    exact hperm.symm ▸ hJ_cols.comp τ τ.injective
  have hsub_cols : LinearIndependent ℝ (N.submatrix id (Fin.succAbove pivot)).col := by
    simpa [Matrix.col, Matrix.submatrix_apply] using hcanonical_cols
  exact ⟨pivot, (Matrix.linearIndependent_cols_iff_isUnit).1 hsub_cols⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: inserting the pivot coordinate
splits a row dot product into its pivot and deleted-column parts. -/
private theorem rowDot_insertNthForKernel
    {r : ℕ}
    (pivot : Fin (r + 1))
    (row : Fin (r + 1) → ℤ)
    (xPivot : ℤ)
    (xRest : Fin r → ℤ) :
    dotProduct row (Fin.insertNth pivot xPivot xRest) =
      row pivot * xPivot + ∑ i : Fin r, row (pivot.succAbove i) * xRest i := by
  let z : Fin (r + 1) → ℤ := Fin.insertNth pivot xPivot xRest
  simpa [dotProduct, z, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
    Fin.sum_univ_succAbove (fun i : Fin (r + 1) ↦ row i * z i) pivot

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: the deleted-column Cramer vector
is a nonzero integral kernel vector. -/
private theorem deletedColumnCramerKernelWitness
    {r : ℕ}
    (M : Matrix (Fin r) (Fin (r + 1)) ℤ)
    (pivot : Fin (r + 1))
    (hdet_ne : (M.submatrix id (Fin.succAbove pivot)).det ≠ 0) :
    let B : Matrix (Fin r) (Fin r) ℤ := M.submatrix id (Fin.succAbove pivot)
    let rhs : Fin r → ℤ := fun i ↦ M i pivot
    let z : Fin (r + 1) → ℤ := Fin.insertNth pivot B.det (fun i ↦ -(B.cramer rhs i))
    z ≠ 0 ∧ M *ᵥ z = 0 := by
  let B : Matrix (Fin r) (Fin r) ℤ := M.submatrix id (Fin.succAbove pivot)
  let rhs : Fin r → ℤ := fun i ↦ M i pivot
  let z : Fin (r + 1) → ℤ := Fin.insertNth pivot B.det (fun i ↦ -(B.cramer rhs i))
  constructor
  · intro hz
    apply hdet_ne
    have hzPivot : z pivot = 0 := by simpa [z] using congrFun hz pivot
    simpa [z, Fin.insertNth_apply_same] using hzPivot
  · ext i
    have hmul_neg :
        B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s)) = -(B *ᵥ B.cramer rhs) := by
      simpa using Matrix.mulVec_neg (B.cramer rhs) B
    have hrow_neg :
        ∑ s : Fin r, B i s * (-(B.cramer rhs s)) = -(B.det * rhs i) := by
      have hi : (B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s))) i = (-(B.det • rhs)) i := by
        calc
          (B *ᵥ (fun s : Fin r ↦ -(B.cramer rhs s))) i = (-(B *ᵥ B.cramer rhs)) i := by
            simpa using congrFun hmul_neg i
          _ = (-(B.det • rhs)) i := by
            simpa only [Pi.neg_apply] using
              congrArg Neg.neg (congrFun (Matrix.mulVec_cramer B rhs) i)
      simpa [Matrix.mulVec, dotProduct, rhs] using hi
    calc
      (M *ᵥ z) i = M i pivot * B.det +
          ∑ s : Fin r, M i (pivot.succAbove s) * (-(B.cramer rhs s)) := by
            simp [Matrix.mulVec, z, rowDot_insertNthForKernel, B]
      _ = rhs i * B.det + ∑ s : Fin r, B i s * (-(B.cramer rhs s)) := by
            simp [B, rhs]
      _ = rhs i * B.det + (-(B.det * rhs i)) := by rw [hrow_neg]
      _ = 0 := by ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: an integral real matrix and
its attained real subdeterminant bound provide an integer-valued bound on the integral lift. -/
private theorem existsIntegralSubdeterminantBound
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (hA_C_int : ∀ i : Fin m, ∀ j : Fin nC, ∃ z : ℤ, A_C i j = (z : ℝ))
    (hDelta : IsLargestAbsSubdeterminantBound A_C Δ) :
    ∃ A_Z : Matrix (Fin m) (Fin nC) ℤ, ∃ D : ℤ,
      (∀ i j, A_C i j = (A_Z i j : ℝ)) ∧
        (D : ℝ) = Δ ∧
        1 ≤ D ∧
        ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
          |(A_Z.submatrix rows cols).det| ≤ D := by
  classical
  let A_Z : Matrix (Fin m) (Fin nC) ℤ :=
    fun i j ↦ Classical.choose (hA_C_int i j)
  have hA_Z : ∀ i j, A_C i j = (A_Z i j : ℝ) := by
    intro i j
    exact Classical.choose_spec (hA_C_int i j)
  have hdet_cast :
      ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
      ((A_Z.submatrix rows cols).det : ℝ) = (A_C.submatrix rows cols).det := by
    intro k rows cols
    have hmatrix :
        (A_Z.submatrix rows cols).map (Int.castRingHom ℝ) =
          A_C.submatrix rows cols := by
      ext i j
      simp [Matrix.submatrix_apply, hA_Z]
    calc
      ((A_Z.submatrix rows cols).det : ℝ) =
          ((A_Z.submatrix rows cols).map (Int.castRingHom ℝ)).det := by
            simpa using
              RingHom.map_det (Int.castRingHom ℝ) (A_Z.submatrix rows cols)
      _ = (A_C.submatrix rows cols).det := congrArg Matrix.det hmatrix
  rcases hDelta.eq_one_or_exists_abs_subdet_eq with hDelta_one | hDelta_attained
  · refine ⟨A_Z, 1, hA_Z, ?_, le_rfl, ?_⟩
    · norm_num [hDelta_one]
    · intro k rows cols
      have hbound := hDelta.abs_subdet_le rows cols
      rw [hDelta_one] at hbound
      rw [← hdet_cast rows cols] at hbound
      exact_mod_cast hbound
  · rcases hDelta_attained with ⟨k, rows, cols, hDelta_eq⟩
    let D : ℤ := |(A_Z.submatrix rows cols).det|
    have hD_cast : (D : ℝ) = Δ := by
      calc
        (D : ℝ) = |((A_Z.submatrix rows cols).det : ℝ)| := by simp [D]
        _ = |(A_C.submatrix rows cols).det| := by rw [hdet_cast rows cols]
        _ = Δ := hDelta_eq.symm
    have hD_one : 1 ≤ D := by
      have hreal : (1 : ℝ) ≤ (D : ℝ) := by
        rw [hD_cast]
        exact hDelta.one_le
      exact_mod_cast hreal
    refine ⟨A_Z, D, hA_Z, hD_cast, hD_one, ?_⟩
    intro s selectedRows selectedCols
    have hbound := hDelta.abs_subdet_le selectedRows selectedCols
    rw [← hD_cast, ← hdet_cast selectedRows selectedCols] at hbound
    exact_mod_cast hbound

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: transpose an integral matrix
and multiply each resulting column by a prescribed sign. -/
private def signedTransposeMatrix
    (A : Matrix (Fin m) (Fin nC) ℤ)
    (sign : Fin m → ℤ) : Matrix (Fin nC) (Fin m) ℤ :=
  fun j i ↦ sign i * A i j

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: signing columns and transposing
preserves absolute values of square subdeterminants. -/
private theorem abs_subdet_signedTransposeMatrix_le
    (A : Matrix (Fin m) (Fin nC) ℤ)
    (sign : Fin m → ℤ)
    (hsign : ∀ i, |sign i| = 1)
    (D : ℤ)
    (hbound : ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin nC),
      |(A.submatrix rows cols).det| ≤ D)
    {k : ℕ}
    (rows : Fin k ↪ Fin nC)
    (cols : Fin k ↪ Fin m) :
    |((signedTransposeMatrix A sign).submatrix rows cols).det| ≤ D := by
  let base : Matrix (Fin k) (Fin k) ℤ := (A.submatrix cols rows).transpose
  let selectedSign : Fin k → ℤ := fun j ↦ sign (cols j)
  have hmatrix :
      (signedTransposeMatrix A sign).submatrix rows cols =
        base * Matrix.diagonal selectedSign := by
    ext i j
    simp [signedTransposeMatrix, base, selectedSign, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_comm]
  have hdiag_abs : |(Matrix.diagonal selectedSign).det| = 1 := by
    calc
      |(Matrix.diagonal selectedSign).det| = ∏ j, |selectedSign j| := by
        rw [Matrix.det_diagonal, Finset.abs_prod]
      _ = 1 := by simp [selectedSign, hsign]
  have hbase_det : base.det = (A.submatrix cols rows).det := by
    exact Matrix.det_transpose (A.submatrix cols rows)
  calc
    |((signedTransposeMatrix A sign).submatrix rows cols).det| =
        |base.det| * |(Matrix.diagonal selectedSign).det| := by
          rw [hmatrix, Matrix.det_mul, abs_mul]
    _ = |base.det| := by rw [hdiag_abs, mul_one]
    _ = |(A.submatrix cols rows).det| := by rw [hbase_det]
    _ ≤ D := hbound cols rows

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: every square minor of the
stacked equality-and-nonnegativity matrix inherits the original determinant bound. -/
private theorem abs_subdet_integralNonnegativeKernelConstraintMatrix_le
    (B : Matrix (Fin nC) (Fin m) ℤ)
    (D : ℤ)
    (hD_one : 1 ≤ D)
    (hB_bound : ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin nC) (cols : Fin k ↪ Fin m),
      |(B.submatrix rows cols).det| ≤ D)
    {k : ℕ}
    (rows : Fin k ↪ Fin ((nC + nC) + m))
    (cols : Fin k ↪ Fin m) :
    |((integralNonnegativeKernelConstraintMatrix B).submatrix rows cols).det| ≤ D := by
  classical
  let equalities : Matrix (Fin (nC + nC)) (Fin m) ℤ :=
    (Matrix.fromRows B (-B)).reindex finSumFinEquiv (Equiv.refl _)
  let stacked : Matrix (Sum (Fin (nC + nC)) (Fin m)) (Fin m) ℤ :=
    Matrix.fromRows equalities (-(1 : Matrix (Fin m) (Fin m) ℤ))
  have hrowsSum_inj :
      Function.Injective (fun i : Fin k ↦ finSumFinEquiv.symm (rows i)) := by
    intro i j hij
    apply rows.injective
    simpa using congrArg finSumFinEquiv hij
  let rowsSum : Fin k ↪ Sum (Fin (nC + nC)) (Fin m) :=
    ⟨fun i ↦ finSumFinEquiv.symm (rows i), hrowsSum_inj⟩
  have hsub :
      (integralNonnegativeKernelConstraintMatrix B).submatrix rows cols =
        stacked.submatrix rowsSum cols := by
    ext i j
    simp [integralNonnegativeKernelConstraintMatrix, equalities, stacked, rowsSum,
      Matrix.submatrix_apply]
  have hD_nonneg : 0 ≤ D := by omega
  have hstack :
      ∀ {s : ℕ} (selectedRows : Fin s ↪ Sum (Fin (nC + nC)) (Fin m))
        (selectedCols : Fin s ↪ Fin m),
        |(stacked.submatrix selectedRows selectedCols).det| ≤ D := by
    intro s
    induction s with
    | zero =>
        intro selectedRows selectedCols
        simpa using hD_one
    | succ s ih =>
        intro selectedRows selectedCols
        by_cases hbottom : ∃ i : Fin (s + 1), ∃ j : Fin m, selectedRows i = Sum.inr j
        · rcases hbottom with ⟨i, j, hrowi⟩
          let M : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ :=
            stacked.submatrix selectedRows selectedCols
          by_cases hcol : ∃ x : Fin (s + 1), selectedCols x = j
          · rcases hcol with ⟨x, hx⟩
            have hrowsTail_inj :
                Function.Injective (fun t : Fin s ↦ selectedRows (i.succAbove t)) := by
              intro a b hab
              exact Fin.succAbove_right_injective (selectedRows.injective hab)
            let rowsTail : Fin s ↪ Sum (Fin (nC + nC)) (Fin m) :=
              ⟨fun t ↦ selectedRows (i.succAbove t), hrowsTail_inj⟩
            have hcolsTail_inj :
                Function.Injective (fun t : Fin s ↦ selectedCols (x.succAbove t)) := by
              intro a b hab
              exact Fin.succAbove_right_injective (selectedCols.injective hab)
            let colsTail : Fin s ↪ Fin m :=
              ⟨fun t ↦ selectedCols (x.succAbove t), hcolsTail_inj⟩
            have hminor :
                M.submatrix i.succAbove x.succAbove =
                  stacked.submatrix rowsTail colsTail := by
              ext a b
              simp [M, rowsTail, colsTail]
            have hmain_entry : M i x = -1 := by
              simp [M, stacked, hrowi, hx]
            have hother_entry : ∀ y : Fin (s + 1), y ≠ x → M i y = 0 := by
              intro y hy
              have hy_ne : j ≠ selectedCols y := by
                intro hy_eq
                apply hy
                exact selectedCols.injective (hy_eq.symm.trans hx.symm)
              simp [M, stacked, hrowi, hy_ne]
            have hdet_expand := Matrix.det_succ_row M i
            rw [Fintype.sum_eq_single x] at hdet_expand
            · calc
                |M.det| = |(M.submatrix i.succAbove x.succAbove).det| := by
                  rw [hdet_expand, hmain_entry]
                  simp
                _ = |(stacked.submatrix rowsTail colsTail).det| := by rw [hminor]
                _ ≤ D := ih rowsTail colsTail
            · intro y hy
              rw [hother_entry y hy]
              simp
          · have hzero_row : ∀ y : Fin (s + 1), M i y = 0 := by
              intro y
              have hy_ne : j ≠ selectedCols y := by
                intro hy_eq
                exact hcol ⟨y, hy_eq.symm⟩
              simp [M, stacked, hrowi, hy_ne]
            have hdet_zero : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i hzero_row
            simpa [M, hdet_zero] using hD_nonneg
        · have htop :
              ∀ i : Fin (s + 1), ∃ r : Fin (nC + nC), selectedRows i = Sum.inl r := by
            intro i
            cases hrow : selectedRows i with
            | inl r => exact ⟨r, rfl⟩
            | inr j => exact False.elim (hbottom ⟨i, j, hrow⟩)
          choose rowsEq hrowsEq using htop
          have hrowsEq_inj : Function.Injective rowsEq := by
            intro a b hab
            apply selectedRows.injective
            rw [hrowsEq a, hrowsEq b, hab]
          let rowsEqEmb : Fin (s + 1) ↪ Fin (nC + nC) := ⟨rowsEq, hrowsEq_inj⟩
          have hrowsEqSum_inj :
              Function.Injective (fun t : Fin (s + 1) ↦ finSumFinEquiv.symm (rowsEqEmb t)) := by
            intro a b hab
            apply rowsEqEmb.injective
            simpa using congrArg finSumFinEquiv hab
          let rowsEqSum : Fin (s + 1) ↪ Sum (Fin nC) (Fin nC) :=
            ⟨fun t ↦ finSumFinEquiv.symm (rowsEqEmb t), hrowsEqSum_inj⟩
          have htop_sub :
              stacked.submatrix selectedRows selectedCols =
                equalities.submatrix rowsEqEmb selectedCols := by
            ext a b
            simpa [stacked, rowsEqEmb] using
              congrArg (fun row ↦ stacked row (selectedCols b)) (hrowsEq a)
          have hequalities :
              equalities.submatrix rowsEqEmb selectedCols =
                (Matrix.fromRows B (-B)).submatrix rowsEqSum selectedCols := by
            ext a b
            simp [equalities, rowsEqEmb, rowsEqSum, Matrix.submatrix_apply]
          have hsigned_bound :
              |((Matrix.fromRows B (-B)).submatrix rowsEqSum selectedCols).det| ≤ D := by
            let baseRow : Fin (s + 1) → Fin nC := fun t ↦ Sum.elim id id (rowsEqSum t)
            let rowSign : Fin (s + 1) → ℤ := fun t ↦
              match rowsEqSum t with
              | Sum.inl _ => 1
              | Sum.inr _ => -1
            let baseMatrix : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ :=
              fun a b ↦ B (baseRow a) (selectedCols b)
            have hsigned_decomp :
                (Matrix.fromRows B (-B)).submatrix rowsEqSum selectedCols =
                  Matrix.diagonal rowSign * baseMatrix := by
              ext a b
              rcases hrow : rowsEqSum a with r | r
              · simp [Matrix.mul_apply, Matrix.diagonal_apply, baseMatrix, baseRow,
                  rowSign, hrow]
              · simp [Matrix.mul_apply, Matrix.diagonal_apply, baseMatrix, baseRow,
                  rowSign, hrow]
            by_cases hbase_inj : Function.Injective baseRow
            · let rowsB : Fin (s + 1) ↪ Fin nC := ⟨baseRow, hbase_inj⟩
              have hbase_eq : baseMatrix = B.submatrix rowsB selectedCols := by
                ext a b
                rfl
              have hdiag_abs : |(Matrix.diagonal rowSign).det| = 1 := by
                calc
                  |(Matrix.diagonal rowSign).det| = ∏ a, |rowSign a| := by
                    rw [Matrix.det_diagonal, Finset.abs_prod]
                  _ = 1 := by
                    apply Finset.prod_eq_one
                    intro a ha
                    rcases hrow : rowsEqSum a with r | r
                    · simp [rowSign, hrow]
                    · simp [rowSign, hrow]
              calc
                |((Matrix.fromRows B (-B)).submatrix rowsEqSum selectedCols).det| =
                    |(Matrix.diagonal rowSign).det| * |baseMatrix.det| := by
                      rw [hsigned_decomp, Matrix.det_mul, abs_mul]
                _ = |baseMatrix.det| := by rw [hdiag_abs, one_mul]
                _ = |(B.submatrix rowsB selectedCols).det| := by rw [hbase_eq]
                _ ≤ D := hB_bound rowsB selectedCols
            · have hrepeat :
                  ∃ a b : Fin (s + 1), a ≠ b ∧ baseRow a = baseRow b := by
                by_contra hrepeat
                apply hbase_inj
                intro a b hab
                by_contra hab_ne
                exact hrepeat ⟨a, b, hab_ne, hab⟩
              rcases hrepeat with ⟨a, b, hab, hbase_eq⟩
              have hrow_eq : baseMatrix a = baseMatrix b := by
                funext t
                simp [baseMatrix, hbase_eq]
              have hdet_zero : baseMatrix.det = 0 := Matrix.det_zero_of_row_eq hab hrow_eq
              rw [hsigned_decomp, Matrix.det_mul, hdet_zero]
              simpa using hD_nonneg
          calc
            |(stacked.submatrix selectedRows selectedCols).det| =
                |((Matrix.fromRows B (-B)).submatrix rowsEqSum selectedCols).det| := by
                  rw [htop_sub, hequalities]
            _ ≤ D := hsigned_bound
  calc
    |((integralNonnegativeKernelConstraintMatrix B).submatrix rows cols).det| =
        |(stacked.submatrix rowsSum cols).det| := by rw [hsub]
    _ ≤ D := hstack rowsSum cols

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: independent active rows of the
stacked cone yield a nonzero bounded integral kernel vector. -/
private theorem existsBoundedIntegralKernelWitness
    (B : Matrix (Fin nC) (Fin m) ℤ)
    (D : ℤ)
    (hD_one : 1 ≤ D)
    (hB_bound : ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin nC) (cols : Fin k ↪ Fin m),
      |(B.submatrix rows cols).det| ≤ D)
    (hm : 0 < m)
    (I : Fin (m - 1) ↪ Fin ((nC + nC) + m))
    (hI_independent : LinearIndependent ℝ
      (fun i : Fin (m - 1) ↦
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)) (I i))) :
    ∃ z : Fin m → ℤ, z ≠ 0 ∧
      ((integralNonnegativeKernelConstraintMatrix B).submatrix I id) *ᵥ z = 0 ∧
      ∀ i : Fin m, |z i| ≤ D := by
  classical
  cases m with
  | zero => omega
  | succ m =>
      let MZ : Matrix (Fin m) (Fin (m + 1)) ℤ :=
        (integralNonnegativeKernelConstraintMatrix B).submatrix I id
      let MR : Matrix (Fin m) (Fin (m + 1)) ℝ := MZ.map (Int.castRingHom ℝ)
      have hrows : LinearIndependent ℝ MR.row := by
        simpa [MR, MZ] using hI_independent
      obtain ⟨pivot, hBunit⟩ := fullRowRankDeletedColumnBasisForKernel MR hrows
      let square : Matrix (Fin m) (Fin m) ℤ := MZ.submatrix id (Fin.succAbove pivot)
      let rhs : Fin m → ℤ := fun i ↦ MZ i pivot
      let z : Fin (m + 1) → ℤ :=
        Fin.insertNth pivot square.det (fun i ↦ -(square.cramer rhs i))
      have hdet_real_ne : (MR.submatrix id (Fin.succAbove pivot)).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det (A := MR.submatrix id (Fin.succAbove pivot))).mp
          hBunit).ne_zero
      have hdet_int_ne : square.det ≠ 0 := by
        intro hzero
        apply hdet_real_ne
        have hdet_cast :
            (MR.submatrix id (Fin.succAbove pivot)).det = (square.det : ℝ) := by
          simpa [MR, MZ, square] using
            (RingHom.map_det (Int.castRingHom ℝ)
              (MZ.submatrix id (Fin.succAbove pivot))).symm
        rw [hdet_cast, hzero]
        norm_num
      have hz_spec : z ≠ 0 ∧ MZ *ᵥ z = 0 := by
        simpa [MZ, square, rhs, z] using
          deletedColumnCramerKernelWitness MZ pivot hdet_int_ne
      refine ⟨z, hz_spec.1, hz_spec.2, ?_⟩
      intro j
      by_cases hj : j = pivot
      · subst j
        simpa [z, square, Fin.insertNth_apply_same] using
          abs_subdet_integralNonnegativeKernelConstraintMatrix_le
            B D hD_one hB_bound I (Fin.succAboveEmb pivot)
      · rcases Fin.exists_succAbove_eq hj with ⟨s, rfl⟩
        let colsFun : Fin m → Fin (m + 1) :=
          fun t ↦ if t = s then pivot else pivot.succAbove t
        have hcols_inj : Function.Injective colsFun := by
          intro t₁ t₂ hcols
          by_cases ht₁ : t₁ = s
          · by_cases ht₂ : t₂ = s
            · exact ht₁.trans ht₂.symm
            · simp [colsFun, ht₁, ht₂] at hcols
          · by_cases ht₂ : t₂ = s
            · have hp : pivot = pivot.succAbove t₁ := by
                simpa [colsFun, ht₁, ht₂] using hcols.symm
              exact False.elim (Fin.succAbove_ne pivot t₁ hp.symm)
            · apply pivot.succAboveEmb.injective
              simpa [colsFun, ht₁, ht₂] using hcols
        let cols : Fin m ↪ Fin (m + 1) := ⟨colsFun, hcols_inj⟩
        have hupdate : square.updateCol s rhs = MZ.submatrix id cols := by
          ext i t
          by_cases ht : t = s
          · subst t
            simp [square, rhs, cols, colsFun]
          · simp [square, rhs, cols, colsFun, ht]
        have hcramer_abs : |square.cramer rhs s| ≤ D := by
          calc
            |square.cramer rhs s| = |(square.updateCol s rhs).det| := by
              rw [Matrix.cramer_apply]
            _ = |(MZ.submatrix id cols).det| := by rw [hupdate]
            _ ≤ D := by
              simpa [MZ] using
                abs_subdet_integralNonnegativeKernelConstraintMatrix_le
                  B D hD_one hB_bound I cols
        simpa [z, Fin.insertNth_apply_succAbove, abs_neg] using hcramer_abs

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: every extreme ray of an
integral nonnegative kernel cone has a nonzero integral generator bounded by `D`. -/
private theorem existsBoundedIntegralSameRayGeneratorOfExtremeRay
    (B : Matrix (Fin nC) (Fin m) ℤ)
    (D : ℤ)
    (hD_one : 1 ≤ D)
    (hB_bound : ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin nC) (cols : Fin k ↪ Fin m),
      |(B.submatrix rows cols).det| ≤ D)
    {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone
      (matrix_polyhedral_cone
        ((integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ))) r) :
    ∃ z : Fin m → ℤ,
      SameRay ℝ r (fun i ↦ (z i : ℝ)) ∧ z ≠ 0 ∧
        ∀ i : Fin m, 0 ≤ z i ∧ z i ≤ D := by
  let M : Matrix (Fin ((nC + nC) + m)) (Fin m) ℝ :=
    (integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)
  have hr_mem : r ∈ matrix_polyhedral_cone M := extremeRayGenerator_mem hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  have hm : 0 < m := by
    by_contra hm_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_pos
    subst m
    apply hr_ne
    ext i
    exact Fin.elim0 i
  obtain ⟨I, hI_active, hI_independent⟩ :=
    (matrix_polyhedral_cone_extreme_ray_iff_exists_active_linearlyIndependent_rows
      M (integralNonnegativeKernelCone_pointed B) hr_mem hr_ne).mp hr
  obtain ⟨z, hz_ne, hz_zero, hz_abs⟩ :=
    existsBoundedIntegralKernelWitness B D hD_one hB_bound hm I hI_independent
  have hz_selected_zero :
      ∀ i : Fin (m - 1), (M *ᵥ (fun j ↦ (z j : ℝ))) (I i) = 0 := by
    intro i
    have hi_int :
        (((integralNonnegativeKernelConstraintMatrix B).submatrix I id) *ᵥ z) i = 0 := by
      simpa using congrFun hz_zero i
    have hi_cast :
        (M *ᵥ (fun j ↦ (z j : ℝ))) (I i) =
          ((((integralNonnegativeKernelConstraintMatrix B).submatrix I id) *ᵥ z) i : ℝ) := by
      simp [M, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [hi_cast, hi_int]
    norm_num
  have hz_span :
      (fun j ↦ (z j : ℝ)) ∈ Submodule.span ℝ ({r} : Set (Fin m → ℝ)) :=
    mem_span_singleton_of_active_rows M hr_ne I hI_active hI_independent hz_selected_zero
  have hr_nonneg : 0 ≤ r :=
    (mem_integralNonnegativeKernelConstraintMatrix_iff B r).1 hr_mem |>.2
  rcases sameRay_or_sameRay_neg_of_mem_span_singleton hz_span with hsame | hsame
  · have hz_nonneg : ∀ i, 0 ≤ z i :=
      intCastVector_nonneg_of_sameRay hr_nonneg hr_ne hsame
    refine ⟨z, hsame, hz_ne, ?_⟩
    intro i
    have habs := hz_abs i
    rw [abs_of_nonneg (hz_nonneg i)] at habs
    exact ⟨hz_nonneg i, habs⟩
  · let zNeg : Fin m → ℤ := fun i ↦ -z i
    have hsameNeg : SameRay ℝ r (fun i ↦ (zNeg i : ℝ)) := by
      simpa [zNeg, Pi.neg_apply] using hsame
    have hzNeg_ne : zNeg ≠ 0 := by
      intro hzNeg_zero
      apply hz_ne
      ext i
      have hi : zNeg i = 0 := by simpa using congrFun hzNeg_zero i
      have hneg : -z i = 0 := by simpa [zNeg] using hi
      exact neg_eq_zero.mp hneg
    have hzNeg_nonneg : ∀ i, 0 ≤ zNeg i :=
      intCastVector_nonneg_of_sameRay hr_nonneg hr_ne hsameNeg
    refine ⟨zNeg, hsameNeg, hzNeg_ne, ?_⟩
    intro i
    have habs : |zNeg i| ≤ D := by simpa [zNeg] using hz_abs i
    rw [abs_of_nonneg (hzNeg_nonneg i)] at habs
    exact ⟨hzNeg_nonneg i, habs⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean: an oversized coordinate in
an integral kernel vector contains a nonzero bounded conformal integral kernel step. -/
private theorem existsIntegralKernelSplitOfCoordinateExceeds
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (u : Fin m → ℝ)
    (hA_C_int : ∀ i : Fin m, ∀ j : Fin nC, ∃ z : ℤ, A_C i j = (z : ℝ))
    (hDelta : IsLargestAbsSubdeterminantBound A_C Δ)
    (huKernel : u ᵥ* A_C = 0)
    (i : Fin m)
    (hi : (m : ℝ) * Δ < |u i|) :
    ∃ z : Fin m → ℤ, z ≠ 0 ∧
      (fun j ↦ (z j : ℝ)) ∈ signCompatibleKernelCone A_C u ∧
      (u - fun j ↦ (z j : ℝ)) ∈ signCompatibleKernelCone A_C u := by
  classical
  obtain ⟨A_Z, D, hA_Z, hD_cast, hD_one, hA_Z_bound⟩ :=
    existsIntegralSubdeterminantBound A_C hA_C_int hDelta
  let sign : Fin m → ℤ := fun j ↦ if 0 ≤ u j then 1 else -1
  let B : Matrix (Fin nC) (Fin m) ℤ := signedTransposeMatrix A_Z sign
  let x : Fin m → ℝ := fun j ↦ |u j|
  let M : Matrix (Fin ((nC + nC) + m)) (Fin m) ℝ :=
    (integralNonnegativeKernelConstraintMatrix B).map (Int.castRingHom ℝ)
  let C : Set (Fin m → ℝ) := matrix_polyhedral_cone M
  -- Signing coordinates transports `u` to its absolute-value vector in a pointed
  -- nonnegative kernel cone whose defining matrix is integral.
  have hsign_abs : ∀ j, |sign j| = 1 := by
    intro j
    by_cases hj : 0 ≤ u j
    · simp [sign, hj]
    · simp [sign, hj]
  have hB_bound :
      ∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin nC) (cols : Fin k ↪ Fin m),
        |(B.submatrix rows cols).det| ≤ D := by
    intro k rows cols
    exact abs_subdet_signedTransposeMatrix_le
      A_Z sign hsign_abs D hA_Z_bound rows cols
  have hx_kernel : (B.map (Int.castRingHom ℝ)) *ᵥ x = 0 := by
    ext j
    have huj : (u ᵥ* A_C) j = 0 := by
      simpa using congrFun huKernel j
    calc
      ((B.map (Int.castRingHom ℝ)) *ᵥ x) j = ∑ k, u k * A_C k j := by
        rw [Matrix.mulVec]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases huk : 0 ≤ u k
        · simp [B, signedTransposeMatrix, sign, x, huk, abs_of_nonneg huk, hA_Z]
          ring
        · have huk_nonpos : u k ≤ 0 := le_of_not_ge huk
          simp [B, signedTransposeMatrix, sign, x, huk, abs_of_nonpos huk_nonpos, hA_Z]
          ring
      _ = (u ᵥ* A_C) j := by simp [Matrix.vecMul, dotProduct]
      _ = 0 := huj
  have hx_mem : x ∈ C := by
    apply (mem_integralNonnegativeKernelConstraintMatrix_iff B x).2
    exact ⟨hx_kernel, fun j ↦ abs_nonneg (u j)⟩
  have hC_polyhedral : is_polyhedral_cone C := by
    exact (is_polyhedral_cone_iff).2 ⟨(nC + nC) + m, M, rfl⟩
  have hC_pointed : is_pointed C := by
    exact integralNonnegativeKernelCone_pointed B
  obtain ⟨k, gen, hC_gen, hgen_extreme⟩ :=
    existsExtremeRayGeneratingFamilyOfPointedPolyhedralCone C hC_polyhedral hC_pointed
  have hx_generated : x ∈ finitely_generated_cone gen := by
    rw [← hC_gen]
    exact hx_mem
  obtain ⟨generatedCoeff, hgeneratedCoeff_nonneg, hx_generated_sum⟩ :=
    mem_finitely_generated_cone_iff.mp hx_generated
  have hx_hull : x ∈ PointedCone.hull ℝ (Set.range gen) := by
    exact mem_hull_iff.mpr
      ⟨k, gen, fun j ↦ Set.mem_range_self j, generatedCoeff,
        hgeneratedCoeff_nonneg, hx_generated_sum⟩
  obtain ⟨q, rays, hrays_range, hrays_independent, hq_span,
      coeff, hcoeff_nonneg, hx_sum⟩ :=
    exists_linearIndependent_conicCombination_of_mem_hull hx_hull
  -- Conic Carathéodory leaves at most `m` independent extreme rays in the representation.
  have hrays_extreme : ∀ j : Fin q, IsExtremeRayOfCone C (rays j) := by
    intro j
    rcases hrays_range j with ⟨t, ht⟩
    rw [← ht]
    exact hgen_extreme t
  have hq_le_m : q ≤ m := by
    calc
      q ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range gen)) := hq_span
      _ ≤ Module.finrank ℝ (Fin m → ℝ) := Submodule.finrank_le _
      _ = m := by simp [Module.finrank_fintype_fun_eq_card]
  choose rayGenerator hsame hgenerator_ne hgenerator_bounds using
    fun j : Fin q ↦
      existsBoundedIntegralSameRayGeneratorOfExtremeRay
        B D hD_one hB_bound (hrays_extreme j)
  have hgeneratorCast_ne :
      ∀ j : Fin q, (fun s ↦ (rayGenerator j s : ℝ)) ≠ 0 := by
    intro j
    exact intCastVector_ne_zero (hgenerator_ne j)
  have hrays_ne : ∀ j : Fin q, rays j ≠ 0 := by
    intro j
    exact extremeRay_ne_zero (hrays_extreme j)
  choose scale hscale_pos hrays_scale using
    fun j : Fin q ↦ (hsame j).exists_pos_right (hrays_ne j) (hgeneratorCast_ne j)
  let adjustedCoeff : Fin q → ℝ := fun j ↦ coeff j * scale j
  -- Replace each real extreme ray by its bounded integral same-ray generator and absorb
  -- the positive rescaling into the coefficient.
  have hadjustedCoeff_nonneg : ∀ j, 0 ≤ adjustedCoeff j := by
    intro j
    exact mul_nonneg (hcoeff_nonneg j) (hscale_pos j).le
  have hx_adjusted_sum :
      x = ∑ j, adjustedCoeff j • (fun s ↦ (rayGenerator j s : ℝ)) := by
    rw [hx_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrays_scale j]
    simp [adjustedCoeff, smul_smul]
  have hlargeCoeff : ∃ j : Fin q, 1 < adjustedCoeff j := by
    by_contra hnone
    push Not at hnone
    have hterm_bound : ∀ j : Fin q,
        adjustedCoeff j * (rayGenerator j i : ℝ) ≤ Δ := by
      intro j
      have hgen_nonneg : (0 : ℝ) ≤ (rayGenerator j i : ℝ) := by
        exact_mod_cast (hgenerator_bounds j i).1
      have hgen_le : (rayGenerator j i : ℝ) ≤ Δ := by
        rw [← hD_cast]
        exact_mod_cast (hgenerator_bounds j i).2
      nlinarith [hadjustedCoeff_nonneg j, hnone j]
    have hsum_bound :
        ∑ j : Fin q, adjustedCoeff j * (rayGenerator j i : ℝ) ≤ (q : ℝ) * Δ := by
      calc
        ∑ j : Fin q, adjustedCoeff j * (rayGenerator j i : ℝ) ≤
            ∑ _j : Fin q, Δ := Finset.sum_le_sum fun j _ ↦ hterm_bound j
        _ = (q : ℝ) * Δ := by simp
    have hx_i : x i =
        ∑ j : Fin q, adjustedCoeff j * (rayGenerator j i : ℝ) := by
      have hi_eq := congrFun hx_adjusted_sum i
      simpa [Pi.smul_apply, smul_eq_mul] using hi_eq
    have hq_real : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hq_le_m
    have hzero_le_one : (0 : ℝ) ≤ 1 := zero_le_one
    have hDelta_nonneg : 0 ≤ Δ := le_trans hzero_le_one hDelta.one_le
    have hqm : (q : ℝ) * Δ ≤ (m : ℝ) * Δ :=
      mul_le_mul_of_nonneg_right hq_real hDelta_nonneg
    have hx_bound : x i ≤ (m : ℝ) * Δ := by
      rw [hx_i]
      exact hsum_bound.trans hqm
    have hu_bound : |u i| ≤ (m : ℝ) * Δ := by
      simpa [x] using hx_bound
    exact (not_lt_of_ge hu_bound) hi
  obtain ⟨selected, hselected⟩ := hlargeCoeff
  -- A coefficient larger than one permits subtraction of one integral generator while
  -- keeping the remaining signed-coordinate vector in the cone.
  let zNonneg : Fin m → ℤ := rayGenerator selected
  let zNonnegR : Fin m → ℝ := fun j ↦ (zNonneg j : ℝ)
  have hzNonneg_mem : zNonnegR ∈ C := by
    obtain ⟨a, ha_pos, ha⟩ :=
      (hsame selected).exists_pos_left (hrays_ne selected) (hgeneratorCast_ne selected)
    have hscaled_mem : a • rays selected ∈ C :=
      matrix_polyhedral_cone_nonneg_smul_mem M
        (extremeRayGenerator_mem (hrays_extreme selected)) ha_pos.le
    rw [ha] at hscaled_mem
    simpa [zNonnegR, zNonneg] using hscaled_mem
  have hzNonneg_data :
      (B.map (Int.castRingHom ℝ)) *ᵥ zNonnegR = 0 ∧ 0 ≤ zNonnegR :=
    (mem_integralNonnegativeKernelConstraintMatrix_iff B zNonnegR).1 hzNonneg_mem
  have hzNonneg_le_x : zNonnegR ≤ x := by
    intro s
    have hterm_nonneg : ∀ j : Fin q,
        0 ≤ adjustedCoeff j * (rayGenerator j s : ℝ) := by
      intro j
      have hgen_nonneg : (0 : ℝ) ≤ (rayGenerator j s : ℝ) := by
        exact_mod_cast (hgenerator_bounds j s).1
      exact mul_nonneg (hadjustedCoeff_nonneg j) hgen_nonneg
    have hselected_term_le_sum :
        adjustedCoeff selected * (rayGenerator selected s : ℝ) ≤
          ∑ j : Fin q, adjustedCoeff j * (rayGenerator j s : ℝ) := by
      exact Finset.single_le_sum
        (fun j _ ↦ hterm_nonneg j) (Finset.mem_univ selected)
    have hz_le_selected_term :
        (rayGenerator selected s : ℝ) ≤
          adjustedCoeff selected * (rayGenerator selected s : ℝ) := by
      have hgen_nonneg : (0 : ℝ) ≤ (rayGenerator selected s : ℝ) := by
        exact_mod_cast (hgenerator_bounds selected s).1
      nlinarith
    have hx_s : x s =
        ∑ j : Fin q, adjustedCoeff j * (rayGenerator j s : ℝ) := by
      have hs_eq := congrFun hx_adjusted_sum s
      simpa [Pi.smul_apply, smul_eq_mul] using hs_eq
    rw [hx_s]
    simpa [zNonnegR, zNonneg] using hz_le_selected_term.trans hselected_term_le_sum
  have hremNonneg_mem : x - zNonnegR ∈ C := by
    apply (mem_integralNonnegativeKernelConstraintMatrix_iff B (x - zNonnegR)).2
    constructor
    · rw [Matrix.mulVec_sub, hx_kernel, hzNonneg_data.1, sub_zero]
    · exact sub_nonneg.mpr hzNonneg_le_x
  have hremNonneg_data : 0 ≤ x - zNonnegR :=
    (mem_integralNonnegativeKernelConstraintMatrix_iff B (x - zNonnegR)).1 hremNonneg_mem |>.2
  let z : Fin m → ℤ := fun j ↦ sign j * zNonneg j
  have hsign_ne : ∀ j, sign j ≠ 0 := by
    intro j
    by_cases hj : 0 ≤ u j
    · simp [sign, hj]
    · simp [sign, hj]
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    apply hgenerator_ne selected
    ext j
    have hj : z j = 0 := by simpa using congrFun hz_zero j
    have hproduct : sign j * zNonneg j = 0 := by simpa [z] using hj
    exact (mul_eq_zero.mp hproduct).resolve_left (hsign_ne j)
  have hz_kernel : (fun j ↦ (z j : ℝ)) ᵥ* A_C = 0 := by
    ext j
    have hj := congrFun hzNonneg_data.1 j
    calc
      ((fun s ↦ (z s : ℝ)) ᵥ* A_C) j =
          ((B.map (Int.castRingHom ℝ)) *ᵥ zNonnegR) j := by
            rw [Matrix.vecMul, Matrix.mulVec]
            apply Finset.sum_congr rfl
            intro s hs
            simp [z, zNonnegR, B, signedTransposeMatrix, hA_Z]
            ring
      _ = 0 := hj
  -- Undoing the coordinate signs gives the required conformal kernel step and remainder.
  refine ⟨z, hz_ne, ⟨hz_kernel, ?_⟩, ?_⟩
  · intro j
    constructor
    · intro huj
      have hzj_nonneg : (0 : ℝ) ≤ (zNonneg j : ℝ) := by
        simpa [zNonnegR] using hzNonneg_data.2 j
      have hzj_eq : (z j : ℝ) = (zNonneg j : ℝ) := by
        simp [z, sign, huj]
      change 0 ≤ (z j : ℝ)
      rw [hzj_eq]
      exact hzj_nonneg
    · intro huj
      by_cases huj_nonneg : 0 ≤ u j
      · have huj_zero : u j = 0 := le_antisymm huj huj_nonneg
        have hzj_nonneg : (0 : ℝ) ≤ (zNonneg j : ℝ) := by
          simpa [zNonnegR] using hzNonneg_data.2 j
        have hremj : 0 ≤ x j - zNonnegR j := by
          simpa [Pi.sub_apply] using hremNonneg_data j
        have hremj_zero : 0 ≤ -(zNonneg j : ℝ) := by
          simpa [x, zNonnegR, huj_zero] using hremj
        have hzj_nonpos : (zNonneg j : ℝ) ≤ 0 := neg_nonneg.mp hremj_zero
        have hzj_zero : (zNonneg j : ℝ) = 0 := by
          exact le_antisymm hzj_nonpos hzj_nonneg
        simp [z, sign, huj_nonneg, hzj_zero]
      · have hzj_nonneg : (0 : ℝ) ≤ (zNonneg j : ℝ) := by
          simpa [zNonnegR] using hzNonneg_data.2 j
        have hzj_eq : (z j : ℝ) = -(zNonneg j : ℝ) := by
          simp [z, sign, huj_nonneg]
        change (z j : ℝ) ≤ 0
        rw [hzj_eq]
        exact neg_nonpos.mpr hzj_nonneg
  · constructor
    · rw [Matrix.sub_vecMul, huKernel, hz_kernel, sub_zero]
    · intro j
      constructor
      · intro huj
        have hremj : 0 ≤ x j - zNonnegR j := by
          simpa [Pi.sub_apply] using hremNonneg_data j
        have hzj_eq : (z j : ℝ) = (zNonneg j : ℝ) := by
          simp [z, sign, huj]
        simpa [x, zNonnegR, hzj_eq, abs_of_nonneg huj, Pi.sub_apply] using hremj
      · intro huj
        by_cases huj_nonneg : 0 ≤ u j
        · have huj_zero : u j = 0 := le_antisymm huj huj_nonneg
          have hzj_nonneg : (0 : ℝ) ≤ (zNonneg j : ℝ) := by
            simpa [zNonnegR] using hzNonneg_data.2 j
          have hremj : 0 ≤ x j - zNonnegR j := by
            simpa [Pi.sub_apply] using hremNonneg_data j
          have hremj_zero : 0 ≤ -(zNonneg j : ℝ) := by
            simpa [x, zNonnegR, huj_zero] using hremj
          have hzj_nonpos : (zNonneg j : ℝ) ≤ 0 := neg_nonneg.mp hremj_zero
          have hzj_zero : (zNonneg j : ℝ) = 0 := by
            exact le_antisymm hzj_nonpos hzj_nonneg
          simp [z, sign, huj_zero, hzj_zero]
        · have huj_nonpos : u j ≤ 0 := le_of_not_ge huj_nonneg
          have hremj : 0 ≤ x j - zNonnegR j := by
            simpa [Pi.sub_apply] using hremNonneg_data j
          have hzj_eq : (z j : ℝ) = -(zNonneg j : ℝ) := by
            simp [z, sign, huj_nonneg]
          simp [x, zNonnegR, hzj_eq, abs_of_nonpos huj_nonpos, Pi.sub_apply] at hremj ⊢
          linarith

/-- The proof-oriented companion to Lemma 5.9 packages the source-faithful no-domination
hypothesis as a raw quantified premise. -/
private theorem abs_row_multiplier_le_of_no_strict_slack_domination
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (Δ : ℝ)
    (u : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ)
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u)
    (hundom : ∀ v : Fin m → ℝ,
      ¬ SplitCutStrictlyDominates A_I A_C b v u) :
    ∀ i : Fin m, |u i| ≤ (m : ℝ) * Δ := by
  intro i
  by_contra hi
  have hi_strict : (m : ℝ) * Δ < |u i| := lt_of_not_ge hi
  obtain ⟨z, hz_ne, hz_mem, hrem_mem⟩ :=
    existsIntegralKernelSplitOfCoordinateExceeds A_C u hInt.2.1 hΔ hu.2.1 i hi_strict
  -- The conformal integral split produces exactly the forbidden dominating multiplier.
  exact hundom (u - fun j ↦ (z j : ℝ))
    (splitCutStrictlyDominates_sub_integralKernel
      A_I A_C b u hInt hu z hz_ne hz_mem hrem_mem)

/-- Companion bundled form of Lemma 5.9 using
`IsMixedGomoryFractionalCutMultiplier A_I A_C b u`. -/
theorem abs_row_multiplier_le_of_undominated_split_cut_of_multiplier
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (Δ : ℝ)
    (u : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ)
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u)
    (hundom : SplitCutIsUndominated A_I A_C b hInt u) :
    ∀ i : Fin m, |u i| ≤ (m : ℝ) * Δ := by
  exact abs_row_multiplier_le_of_no_strict_slack_domination
    A_I A_C b Δ u hInt hΔ hu hundom

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_lemma_5_9.lean

Lemma 5.9. Let `Δ` be the largest among `1` and the absolute values of all
subdeterminants of `A_C`. Let `u ∈ ℝ^m` satisfy `u A_I ∈ ℤ^I`, `u A_C = 0`,
`u ⬝ᵥ b ∉ ℤ`, and assume the displayed matrix presentation is integral. If the
inequality `(5.6)` is undominated, then `|u i| ≤ m * Δ` for every `i`. -/
theorem abs_row_multiplier_le_of_undominated_split_cut
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (Δ : ℝ)
    (u : Fin m → ℝ)
    (hInt : IsIntegralMixedConstraintPresentation A_I A_C b)
    (hΔ : IsLargestAbsSubdeterminantBound A_C Δ)
    (hA_I : ∀ j : Fin nI, ∃ z : ℤ, (u ᵥ* A_I) j = (z : ℝ))
    (hA_C : u ᵥ* A_C = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (hundom : SplitCutIsUndominated A_I A_C b hInt u) :
    ∀ i : Fin m, |u i| ≤ (m : ℝ) * Δ :=
  abs_row_multiplier_le_of_undominated_split_cut_of_multiplier
    A_I A_C b Δ u hInt hΔ ⟨hA_I, hA_C, hub_nonint⟩ hundom

end Lemma59
