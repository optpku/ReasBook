/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_63.ZeroOneLinearProgram

open scoped Matrix MixedIntegerNotation

namespace PenalizedQuadraticRelaxation

variable {m n : ℕ}

/-- Definition 2.64: the feasible set of the penalized quadratic relaxation consists of the real
vectors satisfying `A x ≤ b` and the box constraints `0 ≤ x ≤ 1`. -/
def feasibleSet
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    Set (Fin n → ℝ) :=
  {x |
    ((A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ)) ∧
      ∀ j : Fin n, 0 ≤ x j ∧ x j ≤ 1}

/-- Membership in `feasibleSet A b` is exactly the displayed linear system `A x ≤ b` together
with the coordinatewise box constraints `0 ≤ x j ≤ 1`. -/
theorem mem_feasibleSet_iff
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    x ∈ feasibleSet A b ↔
      ((A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ)) ∧
        ∀ j : Fin n, 0 ≤ x j ∧ x j ≤ 1 := by
  -- Unfold the set membership to expose its defining linear and box constraints.
  rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_64/PenalizedQuadraticRelaxation.lean:
the canonical mixed-integer encoding's stacked inequalities are precisely the original linear
system together with the coordinatewise upper bounds. -/
private lemma toMixedIntegerLinearProgram_linearSystem_iff
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    (ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).integerMatrix *ᵥ x +
          (ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).continuousMatrix *ᵥ
            (fun i : Fin 0 ↦ Fin.elim0 i) ≤
        (ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).rhs ↔
      ((A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ)) ∧
        ∀ j : Fin n, x j ≤ 1 := by
  -- Split the stacked rows into the original `A x ≤ b` block and the identity upper-bound block.
  constructor
  · intro hineq
    refine ⟨?_, ?_⟩
    · intro i
      simpa [ZeroOneLinearProgram.toMixedIntegerLinearProgram,
        MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec, dotProduct] using
        hineq (Fin.castAdd n i)
    · intro j
      simpa [ZeroOneLinearProgram.toMixedIntegerLinearProgram,
        MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec, dotProduct] using
        hineq (Fin.natAdd m j)
  · rintro ⟨hlinear, hupper⟩
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro i
      simpa [ZeroOneLinearProgram.toMixedIntegerLinearProgram,
        MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec, dotProduct] using hlinear i
    · intro j
      simpa [ZeroOneLinearProgram.toMixedIntegerLinearProgram,
        MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec, dotProduct] using hupper j

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_64/PenalizedQuadraticRelaxation.lean

The box-constrained feasible set is exactly the LP relaxation of the canonical Chapter 1 mixed
integer linear program attached to the underlying `0`--`1` linear program. -/
theorem mem_feasibleSet_iff_mem_toMixedIntegerLinearProgram_lpRelaxation
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    x ∈ feasibleSet A b ↔
      (x, fun i : Fin 0 ↦ Fin.elim0 i) ∈
        (ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).lpRelaxation := by
  -- Rewrite both feasible regions through their stable interfaces, then reassociate the bounds.
  rw [mem_feasibleSet_iff]
  rw [(ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).mem_lpRelaxation_iff]
  rw [toMixedIntegerLinearProgram_linearSystem_iff]
  constructor
  · rintro ⟨hlinear, hbox⟩
    refine ⟨⟨hlinear, fun j ↦ (hbox j).2⟩, fun j ↦ (hbox j).1, ?_⟩
    intro i
    exact Fin.elim0 i
  · rintro ⟨⟨hlinear, hupper⟩, hlower, _⟩
    exact ⟨hlinear, fun j ↦ ⟨hlower j, hupper j⟩⟩

/-- Every feasible binary vector of the underlying `0`--`1` linear program is feasible for the
penalized quadratic relaxation. -/
theorem zeroOneFeasibleSet_subset_feasibleSet
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    ZeroOneLinearProgram.feasibleSet c A b ⊆ feasibleSet A b := by
  -- Read the mixed-`0,1` system directly, retaining its original rows and binary coordinates.
  intro x hx
  rw [ZeroOneLinearProgram.feasibleSet, Set.mem_setOf_eq] at hx
  rw [(ZeroOneLinearProgram.toMixedIntegerLinearProgram c A b).mem_mixedZeroOneFeasibleSet_iff]
    at hx
  rcases hx with ⟨hineq, hbinary, _⟩
  rw [mem_feasibleSet_iff]
  refine ⟨(toMixedIntegerLinearProgram_linearSystem_iff.mp hineq).1, ?_⟩
  -- Each binary equation supplies both endpoints of the required box interval.
  intro j
  rcases hbinary j with hj | hj
  · have hj' : x j = 0 := hj
    simp [hj']
  · have hj' : x j = 1 := hj
    simp [hj']

/-- The quadratic penalty term `x ⬝ᵥ (fun j ↦ 1 - x j)` measuring the deviation of `x` from a
binary vector. -/
def penalty
    (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (fun j ↦ 1 - x j)

/-- Unfolding equation for the quadratic penalty. -/
theorem penalty_def
    {x : Fin n → ℝ} :
    penalty x = x ⬝ᵥ (fun j ↦ 1 - x j) := by
  -- Expose the defining dot product of the penalty wrapper.
  rfl

/-- The quadratic penalty vanishes on binary vectors. -/
theorem penalty_eq_zero_of_binary
    {x : Fin n → ℝ}
    (hx : ∀ j : Fin n, x j = 0 ∨ x j = 1) :
    penalty x = 0 := by
  -- Expand the dot product and show that every binary-coordinate summand vanishes.
  rw [penalty_def, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  rcases hx j with hj | hj
  · simp [hj]
  · simp [hj]

/-- The penalized quadratic objective is the linear objective `c x` minus `M` times the binary
penalty. -/
def objectiveValue
    (c : Fin n → ℤ)
    (M : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ZeroOneLinearProgram.objectiveValue c x - M * penalty x

/-- Unfolding equation for the penalized quadratic objective in the displayed source form. -/
theorem objectiveValue_def
    {c : Fin n → ℤ}
    {M : ℝ}
    {x : Fin n → ℝ} :
    objectiveValue c M x =
      (fun j ↦ (c j : ℝ)) ⬝ᵥ x - M * (x ⬝ᵥ (fun j ↦ 1 - x j)) := by
  -- Unfold both objective wrappers and the penalty wrapper.
  rfl

/-- On binary vectors, the penalized quadratic objective agrees with the underlying `0`--`1`
linear-program objective. -/
theorem objectiveValue_eq_zeroOneLinearProgram_objectiveValue_of_binary
    {c : Fin n → ℤ}
    {M : ℝ}
    {x : Fin n → ℝ}
    (hx : ∀ j : Fin n, x j = 0 ∨ x j = 1) :
    objectiveValue c M x = ZeroOneLinearProgram.objectiveValue c x := by
  -- The binary penalty vanishes, so the penalized objective reduces to its linear part.
  rw [objectiveValue, penalty_eq_zero_of_binary hx]
  simp

/-- The set of values attained by the penalized quadratic objective on the box-constrained
relaxation feasible set. -/
def objectiveValues
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (M : ℝ) :
    Set ℝ :=
  objectiveValue c M '' feasibleSet A b

/-- Membership in `objectiveValues c A b M` means that some feasible relaxation point attains the
given penalized objective value. -/
theorem mem_objectiveValues_iff
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {M : ℝ}
    {r : ℝ} :
    r ∈ objectiveValues c A b M ↔
      ∃ x : Fin n → ℝ, x ∈ feasibleSet A b ∧ objectiveValue c M x = r := by
  -- Unfold image membership to expose the attaining feasible point.
  rfl

#print axioms mem_feasibleSet_iff_mem_toMixedIntegerLinearProgram_lpRelaxation

end PenalizedQuadraticRelaxation
