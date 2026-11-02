import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.FeasibleRegion
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.LinearRelaxation

open scoped Matrix MixedIntegerNotation

section Definition15

variable {m n p : ℕ}

private def definition15ConstraintA
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + (n + p))) (Fin n) ℝ :=
  fun row col ↦
    Fin.addCases
      (fun i ↦ A i col)
      (Fin.addCases (fun j ↦ if col = j then -1 else 0) (fun _ ↦ 0))
      row

private def definition15ConstraintG
    (G : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin (m + (n + p))) (Fin p) ℝ :=
  fun row col ↦
    Fin.addCases
      (fun i ↦ G i col)
      (Fin.addCases (fun _ ↦ 0) (fun j ↦ if col = j then -1 else 0))
      row

private def definition15ConstraintRhs
    (b : Fin m → ℝ) :
    Fin (m + (n + p)) → ℝ :=
  Fin.addCases b (fun _ ↦ 0)

private theorem definition15Constraint_le_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (xy : MixedRealPoint n p) :
    definition15ConstraintA A *ᵥ xy.1 + definition15ConstraintG G *ᵥ xy.2 ≤
        definition15ConstraintRhs b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  constructor
  · intro hxy
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hrow := hxy (Fin.castAdd (n + p) i)
      simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
        Matrix.mulVec, dotProduct] using hrow
    · intro j
      have hrow := hxy (Fin.natAdd m (Fin.castAdd p j))
      exact neg_nonpos.mp (by
        simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
          Matrix.mulVec, dotProduct] using hrow)
    · intro j
      have hrow := hxy (Fin.natAdd m (Fin.natAdd n j))
      exact neg_nonpos.mp (by
        simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
          Matrix.mulVec, dotProduct] using hrow)
  · rintro ⟨hineq, hx_nonneg, hy_nonneg⟩
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro i
      simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
        Matrix.mulVec, dotProduct] using hineq i
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
          Matrix.mulVec, dotProduct] using neg_nonpos.mpr (hx_nonneg j)
      · intro j
        simpa [definition15ConstraintA, definition15ConstraintG, definition15ConstraintRhs,
          Matrix.mulVec, dotProduct] using neg_nonpos.mpr (hy_nonneg j)

private theorem lp_relaxation_feasible_set_eq_real_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    lp_relaxation_feasible_set A G b =
      real_mixed_polyhedron
        (definition15ConstraintA A)
        (definition15ConstraintG G)
        (definition15ConstraintRhs b) := by
  ext xy
  rw [mem_lp_relaxation_feasible_set_iff, mem_real_mixed_polyhedron_iff,
    definition15Constraint_le_iff]

/-- Definition 1.5 (Natural linear relaxation of a mixed integer linear set). For real coefficient
data `A`, `G`, and `b`, the canonical LP feasible region `lp_relaxation_feasible_set A G b` is a
linear relaxation in the sense of Definition 1.4 of the mixed-integer feasible set
`milp_feasible_set A G b`. -/
theorem lp_relaxation_feasible_set_isLinearRelaxation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    IsLinearRelaxation (milp_feasible_set A G b) (lp_relaxation_feasible_set A G b) := by
  exact
    IsLinearRelaxation.ofPresentation
      (milp_feasible_set A G b)
      (lp_relaxation_feasible_set A G b)
      (m + (n + p))
      (definition15ConstraintA A)
      (definition15ConstraintG G)
      (definition15ConstraintRhs b)
      (lp_relaxation_feasible_set_eq_real_mixed_polyhedron A G b)
      (milp_feasible_set_subset_lp_relaxation_feasible_set A G b)

/- The source-facing set owners and membership lemmas remain the reusable API behind Definition
1.5, while `lp_relaxation_feasible_set_isLinearRelaxation` packages their canonical bridge into the
existing `IsLinearRelaxation` owner from Definition 1.4. -/
#check milp_feasible_set
#check lp_relaxation_feasible_set
#check mem_milp_feasible_set_iff
#check mem_lp_relaxation_feasible_set_iff
#check milp_feasible_set_subset_lp_relaxation_feasible_set
#check lp_relaxation_feasible_set_isLinearRelaxation

end Definition15
