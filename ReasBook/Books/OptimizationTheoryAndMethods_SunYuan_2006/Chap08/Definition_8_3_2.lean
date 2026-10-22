/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_4

noncomputable section

section Chapter08Definition832

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: second-order constrained optimization via the Chapter 8 null-constraint set
--   `G(xStar, lamStar)`
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem.linearizedFeasibleDirectionSet` from `Definition_8_2_2`
--   `ConstrainedOptimizationProblem.IsKKTPoint`,
--   `ConstrainedOptimizationProblem.positiveActiveIneqIndexSet`, and
--   `ConstrainedOptimizationProblem.sequentialNullConstraintDirections`
--   from `Definition_8_3_1`
--   `tangentConeAt ℝ X xStar` as the canonical owner behind the source's sequential feasible
--   directions from `Definition_8_2_3`
-- * owner abstraction chosen here: the source-facing set
--   `linearizedNullConstraintDirections`, expressed directly as a bridge/view on the canonical
--   upstream owner `problem.linearizedFeasibleDirectionSet xStar`
-- * primitive data reused from the owner chain: a linearized feasible direction and the positive
--   active inequality index set
-- * derived API here: the explicit `G(xStar, lamStar)` membership formulas and subset lemmas

/-- `problem.linearizedNullConstraintDirections xStar lamStar` is the Chapter 8 set
`G(xStar, lamStar)` of nonzero linearized null constraint directions. If the KKT multiplier at
`xStar` is unique, the source also writes this set as `G(xStar)`. -/
def linearizedNullConstraintDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) : Set Point :=
  {d |
    d ∈ problem.linearizedFeasibleDirectionSet xStar ∧
      d ≠ 0 ∧
        ∀ i ∈ problem.positiveActiveIneqIndexSet xStar lamStar,
          problem.linearizedConstraintPairing xStar d i = 0}

/-- Chapter08 Definition 8.3.2 (2): formula `(8.3.15)` rewrites `G(xStar, lamStar)` against the
Chapter 8 owner `problem.linearizedFeasibleDirectionSet xStar`. -/
theorem mem_linearizedNullConstraintDirections_iff
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) (d : Point) :
    d ∈ problem.linearizedNullConstraintDirections xStar lamStar ↔
      d ∈ problem.linearizedFeasibleDirectionSet xStar ∧
        d ≠ 0 ∧
          ∀ i ∈ problem.positiveActiveIneqIndexSet xStar lamStar,
            problem.linearizedConstraintPairing xStar d i = 0 :=
  Iff.rfl

/-- The explicit set-builder formula `(8.3.14)` for `G(xStar, lamStar)`. -/
theorem mem_linearizedNullConstraintDirections_iff_explicit
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) (d : Point) :
    d ∈ problem.linearizedNullConstraintDirections xStar lamStar ↔
      xStar ∈ problem ∧
        problem.HasActiveConstraintGradientsAt xStar ∧
          d ≠ 0 ∧
            (∀ i ∈ problem.eqIndices ∪ problem.positiveActiveIneqIndexSet xStar lamStar,
              problem.linearizedConstraintPairing xStar d i = 0) ∧
            ∀ i ∈
                problem.activeIneqIndexSet xStar \
                  problem.positiveActiveIneqIndexSet xStar lamStar,
              0 ≤ problem.linearizedConstraintPairing xStar d i := by
  constructor
  · intro hd
    rcases (problem.mem_linearizedNullConstraintDirections_iff xStar lamStar d).1 hd with
      ⟨hd_linearized, h_nonzero, h_pairing⟩
    have hd' := (problem.mem_linearizedFeasibleDirectionSet_iff xStar d).1 hd_linearized
    refine
      ⟨hd'.feasiblePoint, hd'.hasActiveConstraintGradientsAt, h_nonzero, ?_, ?_⟩
    · intro i hi
      rcases hi with hi_eq | hi_pos
      · exact hd'.eq_pairing_eq_zero i hi_eq
      · exact h_pairing i hi_pos
    · intro i hi
      exact hd'.activeIneq_pairing_nonneg i hi.1
  · rintro ⟨hxStar, h_grad, h_nonzero, h_eq, h_nonneg⟩
    have h_linearized : problem.IsLinearizedFeasibleDirectionAt xStar d :=
      { feasiblePoint := hxStar
        hasActiveConstraintGradientsAt := h_grad
        eq_pairing_eq_zero := fun i hi ↦ h_eq i (Or.inl hi)
        activeIneq_pairing_nonneg := by
          intro i hi
          by_cases hi_pos : i ∈ problem.positiveActiveIneqIndexSet xStar lamStar
          · have hzero := h_eq i (Or.inr hi_pos)
            simpa [problem.linearizedConstraintPairing_eq xStar d i] using hzero.ge
          · exact h_nonneg i ⟨hi, hi_pos⟩ }
    exact
      (problem.mem_linearizedNullConstraintDirections_iff xStar lamStar d).2
        ⟨(problem.mem_linearizedFeasibleDirectionSet_iff xStar d).2 h_linearized,
          h_nonzero, fun i hi ↦ h_eq i (Or.inr hi)⟩

/-- Chapter08 Definition 8.3.2 (3): if the KKT multiplier at `xStar` is unique, then the set
`G(xStar, lamStar)` is independent of the corresponding multiplier and may be denoted by
`G(xStar)`. -/
theorem linearizedNullConstraintDirections_eq_of_uniqueKKTMultiplier
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point)
    (h_unique :
      ∀ lam₁ lam₂ : Fin m → ℝ,
        problem.IsKKTPoint xStar lam₁ → problem.IsKKTPoint xStar lam₂ → lam₁ = lam₂)
    (lam₁ lam₂ : Fin m → ℝ)
    (h_kkt₁ : problem.IsKKTPoint xStar lam₁)
    (h_kkt₂ : problem.IsKKTPoint xStar lam₂) :
    problem.linearizedNullConstraintDirections xStar lam₁ =
      problem.linearizedNullConstraintDirections xStar lam₂ := by
  simp [h_unique lam₁ lam₂ h_kkt₁ h_kkt₂]

/- Chapter08 Definition 8.3.2 (4): formula `(8.3.16)` is the source-facing inclusion
`S(xStar, lamStar) ⊆ SFD(xStar, problem.feasibleSet)`, realized in this repository by the
canonical positive tangent cone `posTangentConeAt problem.feasibleSet xStar`. -/
theorem sequentialNullConstraintDirections_subset_posTangentConeAt
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    problem.sequentialNullConstraintDirections xStar lamStar ⊆
      posTangentConeAt problem.feasibleSet xStar := by
  intro d hd
  have hd_seq := (problem.mem_sequentialNullConstraintDirections_iff xStar d lamStar).1 hd
  rcases hd_seq.exists_sequences with ⟨dSeq, delta, hseq⟩
  rcases hseq with ⟨hdelta_pos, hfeasible, _, hdSeq, hdelta⟩
  exact
    (mem_posTangentConeAt_iff_exists_seq_pos).2
      ⟨dSeq, delta, hdelta_pos, hfeasible, hdSeq, hdelta⟩

/- The tangent-cone consequence of `(8.3.16)` is already the upstream owner theorem
`ConstrainedOptimizationProblem.sequentialNullConstraintDirections_subset_tangentConeAt` from
`Definition_8_3_1`. -/
#check ConstrainedOptimizationProblem.sequentialNullConstraintDirections_subset_tangentConeAt

/-- Chapter08 Definition 8.3.2 (5): formula `(8.3.17)` says that every linearized null
constraint direction belongs to `problem.linearizedFeasibleDirectionSet xStar`. -/
theorem linearizedNullConstraintDirections_subset_linearizedFeasible
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    problem.linearizedNullConstraintDirections xStar lamStar ⊆
      problem.linearizedFeasibleDirectionSet xStar := by
  intro d hd
  exact (problem.mem_linearizedNullConstraintDirections_iff xStar lamStar d).1 hd |>.1

/-- Chapter08 Definition 8.3.2 (6): formula `(8.3.18)` says that every sequential null
constraint direction is a linearized null constraint direction whenever every active constraint
gradient at `xStar` exists. -/
theorem sequentialNullDirections_subset_linearizedNullDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ)
    (h_constraints : problem.HasActiveConstraintGradientsAt xStar) :
    problem.sequentialNullConstraintDirections xStar lamStar ⊆
      problem.linearizedNullConstraintDirections xStar lamStar := by
  intro d hd
  have hd_seq := (problem.mem_sequentialNullConstraintDirections_iff xStar d lamStar).1 hd
  rcases hd_seq.exists_sequences with ⟨dSeq, delta, hseq⟩
  rcases hseq with ⟨hdelta_pos, hfeasible, hzero, hdSeq, hdelta⟩
  have hxStar : xStar ∈ problem := hd_seq.isKKTPoint.feasible
  have hd_feasible :
      d ∈ posTangentConeAt problem.feasibleSet xStar := by
    exact
      (mem_posTangentConeAt_iff_exists_seq_pos).2
        ⟨dSeq, delta, hdelta_pos, hfeasible, hdSeq, hdelta⟩
  have hd_linearized :
      d ∈ problem.linearizedFeasibleDirectionSet xStar :=
    sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
      problem xStar hxStar h_constraints hd_feasible
  refine
    (problem.mem_linearizedNullConstraintDirections_iff xStar lamStar d).2
      ⟨hd_linearized, hd_seq.nonzero, ?_⟩
  intro i hi_pos
  have hi_active :
      i ∈ problem.activeIneqIndexSet xStar :=
    (problem.mem_positiveActiveIneqIndexSet_iff xStar lamStar i).1 hi_pos |>.1
  have hi_constraint :
      i ∈ problem.activeConstraintIndexSet xStar :=
    (problem.mem_activeConstraintIndexSet_iff xStar i).2 <|
      Or.inr ((problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active)
  have hx_zero : problem.constraint i xStar = 0 :=
    (problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active |>.2
  have hd_zero :
      d ∈ posTangentConeAt {x : Point | problem.constraint i x = 0} xStar := by
    exact
      (mem_posTangentConeAt_iff_exists_seq_pos).2
        ⟨dSeq, delta, hdelta_pos, by
            intro k
            simpa using hzero k i (Or.inr hi_pos), hdSeq, hdelta⟩
  have hd_zero' :
      d ∈ tangentConeAt ℝ {x : Point | problem.constraint i x = 0} xStar :=
    tangentConeAt_mono_field hd_zero
  have hzero_eq :
      Set.EqOn (problem.constraint i) (fun _ : Point ↦ (0 : ℝ))
        {x : Point | problem.constraint i x = 0} := by
    intro x hx
    simpa using hx
  have hzero_within :
      HasFDerivWithinAt (problem.constraint i) (0 : Point →L[ℝ] ℝ)
        {x : Point | problem.constraint i x = 0} xStar :=
    (hasFDerivWithinAt_const (0 : ℝ) xStar {x : Point | problem.constraint i x = 0}).congr
      hzero_eq hx_zero
  have hi_diff : DifferentiableAt ℝ (problem.constraint i) xStar :=
    h_constraints i hi_constraint
  have hderiv_zero : fderiv ℝ (problem.constraint i) xStar d = 0 := by
    have hzero_eval :
        (0 : Point →L[ℝ] ℝ) d =
          (fderiv ℝ (problem.constraint i) xStar : Point →L[ℝ] ℝ) d :=
      hzero_within.unique_on (hi_diff.hasFDerivAt.hasFDerivWithinAt) hd_zero'
    simpa using hzero_eval.symm
  rw [problem.linearizedConstraintPairing_eq xStar d i]
  exact hderiv_zero

end ConstrainedOptimizationProblem

end Chapter08Definition832
