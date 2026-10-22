/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

open Filter
open scoped BigOperators

section Chapter08Definition831

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: constrained optimization with KKT multipliers and tangent-cone feasible
--   directions
-- * inspected Chapter 8 owner declarations:
--   `ConstrainedOptimizationProblem.activeIneqIndexSet` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Theorem_8_2_7`
--   `posTangentConeAt` and
--   `mem_posTangentConeAt_iff_exists_seq_pos` from `Definition_8_2_3`
-- * source-facing owner kept here: `problem.IsSequentialNullConstraintDirectionAt`
-- * primitive data reused from upstream owners:
--   KKT feasibility/duality/stationarity/complementary-slackness from `problem.IsKKTPoint`
--   and active inequality indices from `problem.activeIneqIndexSet`
-- * derived API kept here: positive active indices, the sequence witness predicate, the
--   source-facing sequential null constraint direction owner, and the derived nonnegativity of
--   the remaining active inequalities from feasibility
-- * core/canonical feasible-direction owner reused directly:
--   `posTangentConeAt problem.feasibleSet xStar`, with the tangent-cone bridge supplied by
--   mathlib

/-- The inequality indices active at `xStar` whose multipliers are strictly positive. -/
def positiveActiveIneqIndexSet
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) : Set (Fin m) :=
  {i | i ∈ problem.activeIneqIndexSet xStar ∧ 0 < lamStar i}

/-- Membership in `problem.positiveActiveIneqIndexSet xStar lamStar` means being active at
`xStar` with strictly positive multiplier. -/
theorem mem_positiveActiveIneqIndexSet_iff
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) (i : Fin m) :
    i ∈ problem.positiveActiveIneqIndexSet xStar lamStar ↔
      i ∈ problem.activeIneqIndexSet xStar ∧ 0 < lamStar i :=
  Iff.rfl

/-- Witness conditions for the sequences used in a sequential null constraint direction. -/
def IsSequentialNullConstraintDirectionSeq
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) (d : Point)
    (dSeq : ℕ → Point) (delta : ℕ → ℝ) : Prop :=
  (∀ k, 0 < delta k) ∧
    (∀ k, xStar + delta k • dSeq k ∈ problem.feasibleSet) ∧
    (∀ k i, i ∈ E ∪ problem.positiveActiveIneqIndexSet xStar lamStar →
      problem.constraint i (xStar + delta k • dSeq k) = 0) ∧
    Tendsto dSeq atTop (nhds d) ∧
    Tendsto delta atTop (nhds (0 : ℝ))

/-- Feasibility of the witness sequence already forces the remaining active inequality
constraints to stay nonnegative. -/
theorem IsSequentialNullConstraintDirectionSeq.nonneg_of_mem_activeIneqIndexSet_diff
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ} {d : Point}
    {dSeq : ℕ → Point} {delta : ℕ → ℝ}
    (h :
      problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta) :
    ∀ k i,
      i ∈ problem.activeIneqIndexSet xStar \
        problem.positiveActiveIneqIndexSet xStar lamStar →
        0 ≤ problem.constraint i (xStar + delta k • dSeq k) := by
  rcases h with ⟨_, hfeasible, _, _, _⟩
  intro k i hi
  have hi_ineq : i ∈ problem.ineqIndices :=
    ((problem.mem_activeIneqIndexSet_iff xStar i).1 hi.1).1
  exact
    ((problem.mem_feasibleSet_iff (xStar + delta k • dSeq k)).1 (hfeasible k)).2 i
      hi_ineq

/-- For a KKT pair `(xStar, lamStar)`, a vector `d` is a
sequential null constraint direction when `d ≠ 0` and `d` is the limit of a feasible sequence
`xStar + delta k • dSeq k` whose equality constraints and strictly positive-multiplier active
inequality constraints remain null; the remaining active inequality constraints stay nonnegative
automatically by feasibility. -/
class IsSequentialNullConstraintDirectionAt
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ)
    (d : Point) : Prop where
  isKKTPoint : problem.IsKKTPoint xStar lamStar
  nonzero : d ≠ 0
  exists_sequences :
    ∃ dSeq : ℕ → Point, ∃ delta : ℕ → ℝ,
      problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta

/-- `problem.IsSequentialNullConstraintDirectionAt xStar lamStar d` is proof-irrelevant. -/
instance instSubsingletonIsSequentialNullConstraintDirectionAt
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ)
    (d : Point) :
    Subsingleton (problem.IsSequentialNullConstraintDirectionAt xStar lamStar d) :=
  inferInstance

/-- A sequential null constraint direction lies in the tangent cone of the feasible set at the
base point. -/
theorem IsSequentialNullConstraintDirectionAt.mem_tangentConeAt_feasibleSet
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ} {d : Point}
    (h : problem.IsSequentialNullConstraintDirectionAt xStar lamStar d) :
    d ∈ tangentConeAt ℝ problem.feasibleSet xStar := by
  rcases h.exists_sequences with ⟨dSeq, delta, hseq⟩
  rcases hseq with ⟨hdelta_pos, hfeasible, _, hdSeq, hdelta⟩
  have hd_tangent :
      d ∈ posTangentConeAt problem.feasibleSet xStar := by
    exact
      (mem_posTangentConeAt_iff_exists_seq_pos).2
        ⟨dSeq, delta, hdelta_pos, hfeasible, hdSeq, hdelta⟩
  exact tangentConeAt_mono_field hd_tangent

/-- `problem.sequentialNullConstraintDirections xStar lamStar` is the set `S(xStar, lamStar)` of
all sequential null constraint directions associated to the KKT pair `(xStar, lamStar)`. -/
def sequentialNullConstraintDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    Set Point :=
  {d | problem.IsSequentialNullConstraintDirectionAt xStar lamStar d}

/-- Membership in `problem.sequentialNullConstraintDirections xStar lamStar` is exactly the
sequential-null-constraint-direction predicate. -/
theorem mem_sequentialNullConstraintDirections_iff
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Fin m → ℝ) :
    d ∈ problem.sequentialNullConstraintDirections xStar lamStar ↔
      problem.IsSequentialNullConstraintDirectionAt xStar lamStar d :=
  Iff.rfl

/-- Helper for Chapter08 Definition 8.3.1: an inequality multiplier vanishes whenever the index
is not in `positiveActiveIneqIndexSet xStar lamStar`. -/
theorem IsKKTPoint.multiplier_eq_zero_of_not_mem_positiveActiveIneqIndexSet
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ}
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    {i : Fin m} (hi_ineq : i ∈ problem.ineqIndices)
    (hi_not_pos : i ∉ problem.positiveActiveIneqIndexSet xStar lamStar) :
    lamStar i = 0 := by
  -- Split according to whether the inequality is active at the KKT point.
  by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
  · -- An active inequality outside the positive-active set has a nonpositive multiplier, and KKT
    -- dual feasibility upgrades this to a zero multiplier.
    have hnot_lt : ¬ 0 < lamStar i := by
      intro hlam_pos
      exact
        hi_not_pos
          ((problem.mem_positiveActiveIneqIndexSet_iff xStar lamStar i).2
            ⟨hi_active, hlam_pos⟩)
    exact le_antisymm (not_lt.mp hnot_lt) (h_kkt.dualFeasible i hi_ineq)
  · -- An inactive inequality has strictly positive constraint value, so complementary slackness
    -- forces the multiplier to vanish.
    have hconstraint_nonneg : 0 ≤ problem.constraint i xStar :=
      h_kkt.ineq_constraints i hi_ineq
    have hconstraint_ne : problem.constraint i xStar ≠ 0 := by
      intro hzero
      exact hi_active ((problem.mem_activeIneqIndexSet_iff xStar i).2 ⟨hi_ineq, hzero⟩)
    have hconstraint_pos : 0 < problem.constraint i xStar :=
      lt_of_le_of_ne hconstraint_nonneg (by simpa using hconstraint_ne.symm)
    exact
      (mul_eq_zero.mp (h_kkt.complementarySlackness i hi_ineq)).resolve_right
        hconstraint_pos.ne'

/-- Helper for Chapter08 Definition 8.3.1: the multiplier-weighted constraint sum vanishes along
any witness sequence for a sequential null constraint direction. -/
theorem IsSequentialNullConstraintDirectionSeq.weightedConstraintSum_eq_zero
    {problem : ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ} {d : Point}
    {dSeq : ℕ → Point} {delta : ℕ → ℝ}
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_seq : problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta) :
    ∀ k,
      ∑ i : Fin m, lamStar i * problem.constraint i (xStar + delta k • dSeq k) = 0 := by
  rcases h_seq with ⟨_, _, hzero, _, _⟩
  intro k
  -- Split the finite sum along the equality/inequality partition of constraint indices.
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi_union : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
    simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
      using (show i ∈ E ∪ I from by
        rw [problem.eqIndices_union_ineqIndices]
        simp)
  rcases hi_union with hi_eq | hi_ineq
  · -- Equality constraints vanish along the witness sequence by definition.
    have hi_source : i ∈ E := by
      simpa [ConstrainedOptimizationProblem.eqIndices] using hi_eq
    rw [hzero k i (Or.inl hi_source), mul_zero]
  · by_cases hi_pos : i ∈ problem.positiveActiveIneqIndexSet xStar lamStar
    · -- Positive-active inequalities also vanish along the witness sequence.
      rw [hzero k i (Or.inr hi_pos), mul_zero]
    · -- All remaining inequality indices have zero multiplier by the KKT conditions.
      rw [h_kkt.multiplier_eq_zero_of_not_mem_positiveActiveIneqIndexSet hi_ineq hi_pos, zero_mul]

/-- Chapter08 Definition 8.3.1: equivalently, `d ∈ S(xStar, lamStar)` exactly when
`d ∈ SFD(xStar, problem.feasibleSet)` admits witnessing sequences
`xStar + delta k • dSeq k` along which the multiplier-weighted constraint sum
`∑ i : Fin m, lamStar i * problem.constraint i (xStar + delta k • dSeq k)` vanishes. -/
theorem mem_sequentialNullConstraintDirections_iff_exists_seq
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Fin m → ℝ) :
    d ∈ problem.sequentialNullConstraintDirections xStar lamStar ↔
      problem.IsKKTPoint xStar lamStar ∧
        d ≠ 0 ∧
        ∃ dSeq : ℕ → Point, ∃ delta : ℕ → ℝ,
          problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta ∧
            (∀ k,
              ∑ i : Fin m, lamStar i * problem.constraint i (xStar + delta k • dSeq k) = 0) :=
    by
  constructor
  · intro hd
    rcases (problem.mem_sequentialNullConstraintDirections_iff xStar d lamStar).1 hd with
      ⟨h_kkt, hd_nonzero, dSeq, delta, hseq⟩
    -- Keep the same witness sequences and add the source weighted-sum identity.
    refine ⟨h_kkt, hd_nonzero, dSeq, delta, hseq, ?_⟩
    exact hseq.weightedConstraintSum_eq_zero h_kkt
  · rintro ⟨h_kkt, hd_nonzero, dSeq, delta, hseq, _hsum⟩
    -- Repackage the existing witness data into the class-based owner of `S(xStar, lamStar)`.
    exact
      (problem.mem_sequentialNullConstraintDirections_iff xStar d lamStar).2
        { isKKTPoint := h_kkt
          nonzero := hd_nonzero
          exists_sequences := ⟨dSeq, delta, hseq⟩ }

/-- Every sequential null constraint direction lies in the tangent cone of
`problem.feasibleSet` at `xStar`. -/
theorem sequentialNullConstraintDirections_subset_tangentConeAt
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    problem.sequentialNullConstraintDirections xStar lamStar ⊆
      tangentConeAt ℝ problem.feasibleSet xStar := by
  intro d hd
  exact
    IsSequentialNullConstraintDirectionAt.mem_tangentConeAt_feasibleSet
      ((problem.mem_sequentialNullConstraintDirections_iff xStar d lamStar).1 hd)

end ConstrainedOptimizationProblem

end Chapter08Definition831
