/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_3
import Mathlib.Tactic.Linarith

open scoped BigOperators Matrix MixedIntegerNotation

/-- A single-machine scheduling problem with release times, positive processing times,
nonnegative weights, and a chosen big-M constant. -/
structure SingleMachineReleaseTimeProblem (n : ℕ) where
  releaseTime : Fin n → ℝ
  processingTime : Fin n → ℝ
  weight : Fin n → ℝ
  bigM : ℝ
  processing_pos : ∀ i : Fin n, 0 < processingTime i
  weight_nonneg : ∀ i : Fin n, 0 ≤ weight i

namespace SingleMachineReleaseTimeProblem

variable {n : ℕ}

/-- The directed off-diagonal job pairs indexing the ordering variables `δ_ij`. -/
abbrev jobArc (n : ℕ) := { ij : Fin n × Fin n // ij.1 ≠ ij.2 }

/-- Build the directed off-diagonal job pair `(i, j)` from an explicit proof `i ≠ j`. -/
def jobArcOfNe
    (i j : Fin n)
    (hij : i ≠ j) :
    jobArc n :=
  ⟨(i, j), hij⟩

/-- Reverse a directed off-diagonal job pair. -/
def reverseJobArc
    (a : jobArc n) :
    jobArc n :=
  ⟨(a.1.2, a.1.1), a.2.symm⟩

/-- The tail job of a directed off-diagonal job pair. -/
def jobArcTail
    (a : jobArc n) :
    Fin n :=
  a.1.1

/-- The head job of a directed off-diagonal job pair. -/
def jobArcHead
    (a : jobArc n) :
    Fin n :=
  a.1.2

/-- Reversing a directed off-diagonal job pair twice returns the original pair. -/
theorem reverseJobArc_reverseJobArc
    (a : jobArc n) :
    reverseJobArc (reverseJobArc a) = a := by
  -- Both reversals restore the underlying ordered pair; subtype extensionality ignores proofs.
  apply Subtype.ext
  rfl

/-- Construct a single-machine release-time scheduling problem from its source data. -/
def ofData
    (releaseTime : Fin n → ℝ)
    (processingTime : Fin n → ℝ)
    (weight : Fin n → ℝ)
    (bigM : ℝ)
    (processing_pos : ∀ i : Fin n, 0 < processingTime i)
    (weight_nonneg : ∀ i : Fin n, 0 ≤ weight i) :
    SingleMachineReleaseTimeProblem n :=
  { releaseTime := releaseTime
    processingTime := processingTime
    weight := weight
    bigM := bigM
    processing_pos := processing_pos
    weight_nonneg := weight_nonneg }

/-- The feasibility constraints for the release-time single-machine scheduling formulation:
release times, completion equations, both big-M disjunctive non-overlap inequalities, pairwise
ordering, nonnegativity, and binary ordering variables. -/
def feasible
  (P : SingleMachineReleaseTimeProblem n)
  (s C : Fin n → ℝ)
  (δ : jobArc n → ℝ) : Prop :=
  (∀ i : Fin n, s i ≥ P.releaseTime i) ∧
    (∀ i : Fin n, C i = s i + P.processingTime i) ∧
    (∀ a : jobArc n, s (jobArcHead a) ≥ C (jobArcTail a) - P.bigM * (1 - δ a)) ∧
    (∀ a : jobArc n, s (jobArcTail a) ≥ C (jobArcHead a) - P.bigM * δ a) ∧
    (∀ i j : Fin n, ∀ hij : i < j,
      δ (jobArcOfNe i j (ne_of_lt hij)) +
          δ (jobArcOfNe j i (ne_of_gt hij)) = 1) ∧
    (∀ i : Fin n, 0 ≤ s i) ∧
    (∀ i : Fin n, 0 ≤ C i) ∧
    ∀ a : jobArc n, δ a = 0 ∨ δ a = 1

/-- Membership in `P.feasible s C δ` is exactly the displayed conjunction of release-time,
completion, disjunctive non-overlap, pairwise choice, nonnegativity, and binary constraints. -/
theorem feasible_iff
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ} :
    P.feasible s C δ ↔
      (∀ i : Fin n, s i ≥ P.releaseTime i) ∧
        (∀ i : Fin n, C i = s i + P.processingTime i) ∧
        (∀ a : jobArc n,
          s (jobArcHead a) ≥ C (jobArcTail a) - P.bigM * (1 - δ a)) ∧
        (∀ a : jobArc n,
          s (jobArcTail a) ≥ C (jobArcHead a) - P.bigM * δ a) ∧
        (∀ i j : Fin n, ∀ hij : i < j,
          δ (jobArcOfNe i j (ne_of_lt hij)) +
              δ (jobArcOfNe j i (ne_of_gt hij)) = 1) ∧
        (∀ i : Fin n, 0 ≤ s i) ∧
        (∀ i : Fin n, 0 ≤ C i) ∧
        ∀ a : jobArc n, δ a = 0 ∨ δ a = 1 := by
  -- The theorem exposes the conjunction used to define source feasibility.
  rfl

/-- The release-time lower bound extracted from `P.feasible s C δ`. -/
theorem feasible_releaseTime
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (i : Fin n) :
    s i ≥ P.releaseTime i := by
  -- Project the release-time family from the feasibility conjunction.
  exact (feasible_iff.mp h_feasible).1 i

/-- The completion-time equation extracted from `P.feasible s C δ`. -/
theorem feasible_completionTime
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (i : Fin n) :
    C i = s i + P.processingTime i := by
  -- Project the completion equation from the feasibility conjunction.
  exact (feasible_iff.mp h_feasible).2.1 i

/-- The first big-M non-overlap inequality extracted from `P.feasible s C δ`. -/
theorem feasible_nonoverlapForward
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (a : jobArc n) :
    s (jobArcHead a) ≥ C (jobArcTail a) - P.bigM * (1 - δ a) := by
  -- Project the forward non-overlap inequality from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.1 a

/-- The second big-M non-overlap inequality extracted from `P.feasible s C δ`. -/
theorem feasible_nonoverlapBackward
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (a : jobArc n) :
    s (jobArcTail a) ≥ C (jobArcHead a) - P.bigM * δ a := by
  -- Project the backward non-overlap inequality from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.2.1 a

/-- The pairwise choice constraint `δ_ij + δ_ji = 1` extracted from `P.feasible s C δ`. -/
theorem feasible_pairwiseChoice
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (i j : Fin n)
    (hij : i < j) :
    δ (jobArcOfNe i j (ne_of_lt hij)) +
        δ (jobArcOfNe j i (ne_of_gt hij)) = 1 := by
  -- Project the pairwise-choice equation from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.2.2.1 i j hij

/-- The nonnegativity of the start times extracted from `P.feasible s C δ`. -/
theorem feasible_start_nonneg
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (i : Fin n) :
    0 ≤ s i := by
  -- Project start-time nonnegativity from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.2.2.2.1 i

/-- The nonnegativity of the completion times extracted from `P.feasible s C δ`. -/
theorem feasible_completion_nonneg
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (i : Fin n) :
    0 ≤ C i := by
  -- Project completion-time nonnegativity from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.2.2.2.2.1 i

/-- The binary ordering-variable condition extracted from `P.feasible s C δ`. -/
theorem feasible_binary
    {P : SingleMachineReleaseTimeProblem n}
    {s C : Fin n → ℝ}
    {δ : jobArc n → ℝ}
    (h_feasible : P.feasible s C δ)
    (a : jobArc n) :
    δ a = 0 ∨ δ a = 1 := by
  -- Project the binary coordinate condition from source feasibility.
  exact (feasible_iff.mp h_feasible).2.2.2.2.2.2.2 a

/-- The total weighted completion-time objective of a release-time single-machine schedule. -/
def objectiveValue
    (P : SingleMachineReleaseTimeProblem n)
    (C : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, P.weight i * C i

/-- Unfolding equation for `P.objectiveValue C`. -/
theorem objectiveValue_def
    (P : SingleMachineReleaseTimeProblem n)
    (C : Fin n → ℝ) :
    P.objectiveValue C = ∑ i : Fin n, P.weight i * C i := by
  -- The displayed weighted sum is the definition of the source objective.
  rfl

/-- The set of objective values attained by feasible schedules of `P`. -/
def objectiveValues
    (P : SingleMachineReleaseTimeProblem n) : Set ℝ :=
  { r | ∃ s : Fin n → ℝ, ∃ C : Fin n → ℝ, ∃ δ : jobArc n → ℝ,
      P.feasible s C δ ∧ P.objectiveValue C = r }

/-- Membership in `P.objectiveValues` means that some feasible schedule variables attain the
objective value `r`. -/
theorem mem_objectiveValues_iff
    {P : SingleMachineReleaseTimeProblem n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ s : Fin n → ℝ, ∃ C : Fin n → ℝ, ∃ δ : jobArc n → ℝ,
        P.feasible s C δ ∧ P.objectiveValue C = r := by
  -- Membership unfolds to the schedule witness tuple recorded by `objectiveValues`.
  rfl

/-- The ordered job pairs `(i, j)` with `i < j`, used by the pairwise choice rows of the MILP
bridge. -/
abbrev strictJobPair (n : ℕ) := { ij : Fin n × Fin n // ij.1 < ij.2 }

/-- The row families of the Chapter 1 MILP bridge: release bounds, two completion-equality row
blocks, two big-M row blocks, and two pairwise-choice row blocks. -/
abbrev constraintRow (n : ℕ) :=
  Fin n ⊕ Fin n ⊕ Fin n ⊕ jobArc n ⊕ jobArc n ⊕ strictJobPair n ⊕ strictJobPair n

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
encode source schedule coordinates as a mixed point. -/
private noncomputable def toMixedPoint
    (s C : Fin n → ℝ)
    (δ : jobArc n → ℝ) :
    MixedRealPoint (Fintype.card (jobArc n)) (n + n) :=
  (fun k ↦ δ ((Fintype.equivFin (jobArc n)).symm k), Fin.addCases s C)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
recover start times from a mixed point. -/
private def startTimeOfMixedPoint
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    Fin n → ℝ :=
  fun i ↦ xy.2 (Fin.castAdd n i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
recover completion times from a mixed point. -/
private def completionTimeOfMixedPoint
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    Fin n → ℝ :=
  fun i ↦ xy.2 (Fin.natAdd n i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
recover ordering coordinates from a mixed point. -/
private noncomputable def orderingOfMixedPoint
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    jobArc n → ℝ :=
  fun a ↦ xy.1 ((Fintype.equivFin (jobArc n)) a)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
encoding the coordinates decoded from a mixed point recovers that point. -/
private theorem toMixedPoint_ofMixedPoint
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    toMixedPoint (startTimeOfMixedPoint xy) (completionTimeOfMixedPoint xy)
      (orderingOfMixedPoint xy) = xy := by
  -- Cancel the finite arc enumeration and the two-block continuous-coordinate split.
  apply Prod.ext
  · funext k
    simp [toMixedPoint, orderingOfMixedPoint]
  · unfold toMixedPoint startTimeOfMixedPoint completionTimeOfMixedPoint
    exact Fin.addCases_castAdd_natAdd xy.2

/-- The canonical Chapter 1 mixed integer linear program whose binary block is indexed by
`jobArc n` and whose continuous block consists of the start and completion coordinates. -/
noncomputable def toMixedIntegerLinearProgram
    (P : SingleMachineReleaseTimeProblem n) :
    MixedIntegerLinearProgram
      (Fintype.card (constraintRow n))
      (Fintype.card (jobArc n))
      (n + n) :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun r k ↦
      let row := (Fintype.equivFin (constraintRow n)).symm r
      let a := (Fintype.equivFin (jobArc n)).symm k
      match row with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl _) => 0
      | Sum.inr (Sum.inr (Sum.inl _)) => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl a'))) => if a' = a then P.bigM else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a')))) =>
          if a' = a then -P.bigM else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ij))))) =>
          if a = jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2) then
            1
          else if a = jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2) then
            1
          else
            0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ij))))) =>
          if a = jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2) then
            -1
          else if a = jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2) then
            -1
          else
            0)
    (fun r c ↦
      let row := (Fintype.equivFin (constraintRow n)).symm r
      match row with
      | Sum.inl i =>
          Fin.addCases (fun j : Fin n ↦ if j = i then -1 else 0) (fun _ : Fin n ↦ 0) c
      | Sum.inr (Sum.inl i) =>
          Fin.addCases
            (fun j : Fin n ↦ if j = i then -1 else 0)
            (fun j : Fin n ↦ if j = i then 1 else 0)
            c
      | Sum.inr (Sum.inr (Sum.inl i)) =>
          Fin.addCases
            (fun j : Fin n ↦ if j = i then 1 else 0)
            (fun j : Fin n ↦ if j = i then -1 else 0)
            c
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) =>
          Fin.addCases
            (fun j : Fin n ↦ if j = jobArcHead a then -1 else 0)
            (fun j : Fin n ↦ if j = jobArcTail a then 1 else 0)
            c
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) =>
          Fin.addCases
            (fun j : Fin n ↦ if j = jobArcTail a then -1 else 0)
            (fun j : Fin n ↦ if j = jobArcHead a then 1 else 0)
            c
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => 0)
    (fun r ↦
      let row := (Fintype.equivFin (constraintRow n)).symm r
      match row with
      | Sum.inl i => -P.releaseTime i
      | Sum.inr (Sum.inl i) => P.processingTime i
      | Sum.inr (Sum.inr (Sum.inl i)) => -P.processingTime i
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => P.bigM
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 1
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => -1)
    (fun _ ↦ 0)
    (Fin.addCases (fun _ : Fin n ↦ 0) (fun i : Fin n ↦ P.weight i))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the conceptual integer-block value of each constraint row. -/
private def integerRowValue
    (P : SingleMachineReleaseTimeProblem n)
    (δ : jobArc n → ℝ) :
    constraintRow n → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) => P.bigM * δ a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) => -P.bigM * δ a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ij))))) =>
      δ (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) +
        δ (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ij))))) =>
      -δ (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) -
        δ (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the conceptual continuous-block value of each constraint row. -/
private def continuousRowValue
    (s C : Fin n → ℝ) :
    constraintRow n → ℝ
  | Sum.inl i => -s i
  | Sum.inr (Sum.inl i) => -s i + C i
  | Sum.inr (Sum.inr (Sum.inl i)) => s i - C i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) => -s (jobArcHead a) + C (jobArcTail a)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) =>
      -s (jobArcTail a) + C (jobArcHead a)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => 0

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the conceptual right-hand side of each constraint row. -/
private def constraintRowRhs
    (P : SingleMachineReleaseTimeProblem n) :
    constraintRow n → ℝ
  | Sum.inl i => -P.releaseTime i
  | Sum.inr (Sum.inl i) => P.processingTime i
  | Sum.inr (Sum.inr (Sum.inl i)) => -P.processingTime i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => P.bigM
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => -1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
an arc-sum summand is preserved by the enumeration round trip. -/
private theorem jobArcSumTerm_eq
    (f : jobArc n → ℝ)
    (x : Fin (Fintype.card (jobArc n)) → ℝ)
    (k : Fin (Fintype.card (jobArc n))) :
    f ((Fintype.equivFin (jobArc n)).symm k) * x k =
      f ((Fintype.equivFin (jobArc n)).symm k) *
        x ((Fintype.equivFin (jobArc n)) ((Fintype.equivFin (jobArc n)).symm k)) := by
  -- Cancel the enumeration and its inverse in the vector coordinate.
  rw [Equiv.apply_symm_apply]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
reindex a sum from flattened arc coordinates to directed job arcs. -/
private theorem sum_jobArcEquiv
    (f : jobArc n → ℝ)
    (x : Fin (Fintype.card (jobArc n)) → ℝ) :
    (∑ k : Fin (Fintype.card (jobArc n)),
        f ((Fintype.equivFin (jobArc n)).symm k) * x k) =
      ∑ a : jobArc n, f a * x ((Fintype.equivFin (jobArc n)) a) := by
  -- Transport the finite sum through the canonical enumeration of the arc type.
  exact
    Fintype.sum_equiv (Fintype.equivFin (jobArc n)).symm
      (fun k ↦ f ((Fintype.equivFin (jobArc n)).symm k) * x k)
      (fun a ↦ f a * x ((Fintype.equivFin (jobArc n)) a))
      (jobArcSumTerm_eq f x)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
a split-coordinate summand is preserved by the canonical equivalence round trip. -/
private theorem finAddSumTerm_eq
    {a b : ℕ}
    (f : Fin a → ℝ)
    (g : Fin b → ℝ)
    (x : Fin (a + b) → ℝ)
    (k : Fin (a + b)) :
    Fin.addCases f g k * x k =
      Fin.addCases f g (finSumFinEquiv (finSumFinEquiv.symm k)) *
        x (finSumFinEquiv (finSumFinEquiv.symm k)) := by
  -- Cancel the sum-index equivalence and its inverse in both factors.
  rw [Equiv.apply_symm_apply]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the dot product of an appended coefficient vector splits into its two blocks. -/
private theorem sum_addCases_mul
    {a b : ℕ}
    (f : Fin a → ℝ)
    (g : Fin b → ℝ)
    (x : Fin (a + b) → ℝ) :
    (∑ k : Fin (a + b), Fin.addCases f g k * x k) =
      (∑ i : Fin a, f i * x (Fin.castAdd b i)) +
        ∑ j : Fin b, g j * x (Fin.natAdd a j) := by
  -- Reindex the dot product before reducing `Fin.addCases` on the two injections.
  calc
    (∑ k : Fin (a + b), Fin.addCases f g k * x k) =
        ∑ s : Fin a ⊕ Fin b,
          Fin.addCases f g (finSumFinEquiv s) * x (finSumFinEquiv s) := by
      exact
        Fintype.sum_equiv finSumFinEquiv.symm
          (fun k : Fin (a + b) ↦ Fin.addCases f g k * x k)
          (fun s : Fin a ⊕ Fin b ↦
            Fin.addCases f g (finSumFinEquiv s) * x (finSumFinEquiv s))
          (finAddSumTerm_eq f g x)
    _ = (∑ i : Fin a, f i * x (Fin.castAdd b i)) +
          ∑ j : Fin b, g j * x (Fin.natAdd a j) := by
      simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the two orientations of a strict job pair are distinct arcs. -/
private theorem forwardArc_ne_backwardArc
    (i j : Fin n)
    (hij : i < j) :
    jobArcOfNe i j (ne_of_lt hij) ≠ jobArcOfNe j i (ne_of_gt hij) := by
  -- Equality of the arcs would identify their tails, contradicting strict order.
  intro h
  have hij_eq : i = j := congrArg jobArcTail h
  exact (ne_of_lt hij) hij_eq

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
a two-coordinate selector sum on `Fin m` evaluates at its two distinct indices. -/
private theorem sum_twoCoordinateSelectors
    {m : ℕ}
    (a b : Fin m)
    (hab : a ≠ b)
    (q : ℝ)
    (x : Fin m → ℝ) :
    (∑ v : Fin m, (if v = a then q else if v = b then q else 0) * x v) =
      q * x a + q * x b := by
  -- Separate the disjoint selectors and evaluate each singleton sum.
  calc
    (∑ v : Fin m, (if v = a then q else if v = b then q else 0) * x v) =
        ∑ v : Fin m,
          ((if v = a then q * x v else 0) + (if v = b then q * x v else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hva : v = a
      · subst v
        simp [hab]
      · by_cases hvb : v = b
        · subst v
          simp [hva]
        · simp [hva, hvb]
    _ = q * x a + q * x b := by
      rw [Finset.sum_add_distrib]
      simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
release rows have zero integer-block value. -/
private theorem integerMatrix_mulVec_release
    (P : SingleMachineReleaseTimeProblem n)
    (x : Fin (Fintype.card (jobArc n)) → ℝ)
    (i : Fin n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ x)
        ((Fintype.equivFin (constraintRow n)) (Sum.inl i)) = 0 := by
  -- Expand the release row; all of its integer coefficients vanish.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
    Matrix.mulVec, dotProduct]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
completion rows have zero integer-block value. -/
private theorem integerMatrix_mulVec_completionUpper
    (P : SingleMachineReleaseTimeProblem n)
    (x : Fin (Fintype.card (jobArc n)) → ℝ)
    (i : Fin n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ x)
        ((Fintype.equivFin (constraintRow n)) (Sum.inr (Sum.inl i))) = 0 := by
  -- Expand the upper completion row; all of its integer coefficients vanish.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
    Matrix.mulVec, dotProduct]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
reverse completion rows have zero integer-block value. -/
private theorem integerMatrix_mulVec_completionLower
    (P : SingleMachineReleaseTimeProblem n)
    (x : Fin (Fintype.card (jobArc n)) → ℝ)
    (i : Fin n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ x)
        ((Fintype.equivFin (constraintRow n)) (Sum.inr (Sum.inr (Sum.inl i)))) = 0 := by
  -- Expand the lower completion row; all of its integer coefficients vanish.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
    Matrix.mulVec, dotProduct]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
a forward non-overlap row selects its arc coordinate with coefficient `P.bigM`. -/
private theorem integerMatrix_mulVec_nonoverlapForward
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (a : jobArc n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1)
        ((Fintype.equivFin (constraintRow n))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))) =
      P.bigM * orderingOfMixedPoint xy a := by
  -- Reindex the arc dot product and evaluate its singleton selector.
  rw [Matrix.mulVec, dotProduct]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp only [Equiv.symm_apply_apply]
  simpa [orderingOfMixedPoint] using
    sum_jobArcEquiv (n := n) (fun b ↦ if a = b then P.bigM else 0) xy.1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
a backward non-overlap row selects its arc coordinate with coefficient `-P.bigM`. -/
private theorem integerMatrix_mulVec_nonoverlapBackward
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (a : jobArc n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1)
        ((Fintype.equivFin (constraintRow n))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))))) =
      -P.bigM * orderingOfMixedPoint xy a := by
  -- Reindex the arc dot product and evaluate its singleton selector.
  rw [Matrix.mulVec, dotProduct]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp only [Equiv.symm_apply_apply]
  simpa [orderingOfMixedPoint] using
    sum_jobArcEquiv (n := n) (fun b ↦ if a = b then -P.bigM else 0) xy.1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
an upper pairwise row sums the two oriented arc coordinates. -/
private theorem integerMatrix_mulVec_pairwiseUpper
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (ij : strictJobPair n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1)
        ((Fintype.equivFin (constraintRow n))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ij))))))) =
      orderingOfMixedPoint xy (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) +
        orderingOfMixedPoint xy (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2)) := by
  -- Reindex the arc dot product and evaluate the two disjoint selectors.
  rw [Matrix.mulVec, dotProduct]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp only [Equiv.symm_apply_apply]
  simpa [Equiv.symm_apply_eq, orderingOfMixedPoint] using
    sum_twoCoordinateSelectors
      ((Fintype.equivFin (jobArc n)) (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)))
      ((Fintype.equivFin (jobArc n)) (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2)))
      (fun h ↦ forwardArc_ne_backwardArc ij.1.1 ij.1.2 ij.2
        ((Fintype.equivFin (jobArc n)).injective h)) 1 xy.1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
a lower pairwise row is the negative sum of the two oriented arc coordinates. -/
private theorem integerMatrix_mulVec_pairwiseLower
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (ij : strictJobPair n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1)
        ((Fintype.equivFin (constraintRow n))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ij))))))) =
      -orderingOfMixedPoint xy (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) -
        orderingOfMixedPoint xy (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2)) := by
  -- Reindex the arc dot product and evaluate the two negative selectors.
  rw [Matrix.mulVec, dotProduct]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp only [Equiv.symm_apply_apply]
  simpa [Equiv.symm_apply_eq, orderingOfMixedPoint] using
    sum_twoCoordinateSelectors
      ((Fintype.equivFin (jobArc n)) (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)))
      ((Fintype.equivFin (jobArc n)) (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2)))
      (fun h ↦ forwardArc_ne_backwardArc ij.1.1 ij.1.2 ij.2
        ((Fintype.equivFin (jobArc n)).injective h)) (-1) xy.1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
evaluating the flattened integer matrix yields the conceptual row value. -/
private theorem integerMatrix_mulVec_apply
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (row : constraintRow n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1)
        ((Fintype.equivFin (constraintRow n)) row) =
      integerRowValue P (orderingOfMixedPoint xy) row := by
  -- Dispatch to the computation lemma for the semantic row family.
  rcases row with i | row
  · simpa [integerRowValue] using integerMatrix_mulVec_release P xy.1 i
  · rcases row with i | row
    · simpa [integerRowValue] using integerMatrix_mulVec_completionUpper P xy.1 i
    · rcases row with i | row
      · simpa [integerRowValue] using integerMatrix_mulVec_completionLower P xy.1 i
      · rcases row with a | row
        · simpa [integerRowValue] using integerMatrix_mulVec_nonoverlapForward P xy a
        · rcases row with a | row
          · simpa [integerRowValue] using integerMatrix_mulVec_nonoverlapBackward P xy a
          · rcases row with ij | ij
            · simpa [integerRowValue] using integerMatrix_mulVec_pairwiseUpper P xy ij
            · simpa [integerRowValue] using integerMatrix_mulVec_pairwiseLower P xy ij

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
evaluating the flattened continuous matrix yields the conceptual row value. -/
private theorem continuousMatrix_mulVec_apply
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (row : constraintRow n) :
    (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ xy.2)
        ((Fintype.equivFin (constraintRow n)) row) =
      continuousRowValue (startTimeOfMixedPoint xy) (completionTimeOfMixedPoint xy) row := by
  -- Split the continuous sum into start and completion blocks, then evaluate row selectors.
  rw [Matrix.mulVec, dotProduct]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp only [Equiv.symm_apply_apply]
  rcases row with i | row
  · rw [sum_addCases_mul]
    simp [continuousRowValue, startTimeOfMixedPoint]
  · rcases row with i | row
    · rw [sum_addCases_mul]
      simp [continuousRowValue, startTimeOfMixedPoint, completionTimeOfMixedPoint]
    · rcases row with i | row
      · rw [sum_addCases_mul]
        simp [continuousRowValue, startTimeOfMixedPoint, completionTimeOfMixedPoint,
          sub_eq_add_neg]
      · rcases row with a | row
        · rw [sum_addCases_mul]
          simp [continuousRowValue, startTimeOfMixedPoint, completionTimeOfMixedPoint]
        · rcases row with a | row
          · rw [sum_addCases_mul]
            simp [continuousRowValue, startTimeOfMixedPoint, completionTimeOfMixedPoint]
          · rcases row with ij | ij
            · simp [continuousRowValue]
            · simp [continuousRowValue]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
evaluating the flattened right-hand side yields the conceptual row bound. -/
private theorem rhs_apply
    (P : SingleMachineReleaseTimeProblem n)
    (row : constraintRow n) :
    P.toMixedIntegerLinearProgram.rhs ((Fintype.equivFin (constraintRow n)) row) =
      constraintRowRhs P row := by
  -- Cancel the row enumeration and reduce the matching right-hand-side branch.
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  simp [constraintRowRhs]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the source-facing proposition represented by each semantic row. -/
private def rowCondition
    (P : SingleMachineReleaseTimeProblem n)
    (s C : Fin n → ℝ)
    (δ : jobArc n → ℝ) :
    constraintRow n → Prop
  | Sum.inl i => P.releaseTime i ≤ s i
  | Sum.inr (Sum.inl i) => C i ≤ s i + P.processingTime i
  | Sum.inr (Sum.inr (Sum.inl i)) => s i + P.processingTime i ≤ C i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) =>
      C (jobArcTail a) - P.bigM * (1 - δ a) ≤ s (jobArcHead a)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) =>
      C (jobArcHead a) - P.bigM * δ a ≤ s (jobArcTail a)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ij))))) =>
      δ (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) +
        δ (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2)) ≤ 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ij))))) =>
      1 ≤ δ (jobArcOfNe ij.1.1 ij.1.2 (ne_of_lt ij.2)) +
        δ (jobArcOfNe ij.1.2 ij.1.1 (ne_of_gt ij.2))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
each enumerated MILP inequality is equivalent to its semantic row condition. -/
private theorem rowInequality_iff
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n))
    (row : constraintRow n) :
    (P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1 +
        P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ xy.2)
          ((Fintype.equivFin (constraintRow n)) row) ≤
        P.toMixedIntegerLinearProgram.rhs ((Fintype.equivFin (constraintRow n)) row) ↔
      rowCondition P (startTimeOfMixedPoint xy) (completionTimeOfMixedPoint xy)
        (orderingOfMixedPoint xy) row := by
  -- Replace all three flattened components by their semantic row values.
  rw [Pi.add_apply, integerMatrix_mulVec_apply, continuousMatrix_mulVec_apply, rhs_apply]
  rcases row with i | row
  · simp [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
  · rcases row with i | row
    · simp [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
    · rcases row with i | row
      · simp [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition,
          sub_eq_add_neg, add_comm]
      · rcases row with a | row
        · simp only [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
          constructor
          · intro h
            linarith
          · intro h
            linarith
        · rcases row with a | row
          · simp only [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
            constructor
            · intro h
              linarith
            · intro h
              linarith
          · rcases row with ij | ij
            · simp [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
            · simp only [integerRowValue, continuousRowValue, constraintRowRhs, rowCondition]
              constructor
              · intro h
                linarith
              · intro h
                linarith

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the complete flattened inequality system is the five source structural constraint families. -/
private theorem mixedPoint_linearConstraints_iff
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1 +
          P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ xy.2 ≤
        P.toMixedIntegerLinearProgram.rhs ↔
      (∀ i : Fin n, P.releaseTime i ≤ startTimeOfMixedPoint xy i) ∧
        (∀ i : Fin n,
          completionTimeOfMixedPoint xy i =
            startTimeOfMixedPoint xy i + P.processingTime i) ∧
        (∀ a : jobArc n,
          completionTimeOfMixedPoint xy (jobArcTail a) -
              P.bigM * (1 - orderingOfMixedPoint xy a) ≤
            startTimeOfMixedPoint xy (jobArcHead a)) ∧
        (∀ a : jobArc n,
          completionTimeOfMixedPoint xy (jobArcHead a) -
              P.bigM * orderingOfMixedPoint xy a ≤
            startTimeOfMixedPoint xy (jobArcTail a)) ∧
        ∀ i j : Fin n, ∀ hij : i < j,
          orderingOfMixedPoint xy (jobArcOfNe i j (ne_of_lt hij)) +
              orderingOfMixedPoint xy (jobArcOfNe j i (ne_of_gt hij)) = 1 := by
  -- Read paired inequalities as equalities, and conversely dispatch every semantic row.
  constructor
  · intro hrows
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (rowInequality_iff P xy (Sum.inl i)).mp (hrows _)
    · intro i
      have hu := (rowInequality_iff P xy (Sum.inr (Sum.inl i))).mp (hrows _)
      have hl := (rowInequality_iff P xy (Sum.inr (Sum.inr (Sum.inl i)))).mp (hrows _)
      exact le_antisymm hu hl
    · intro a
      exact
        (rowInequality_iff P xy (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))).mp
          (hrows _)
    · intro a
      exact
        (rowInequality_iff P xy
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))))).mp (hrows _)
    · intro i j hij
      let ij : strictJobPair n := ⟨(i, j), hij⟩
      have hu :=
        (rowInequality_iff P xy
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ij))))))).mp
            (hrows _)
      have hl :=
        (rowInequality_iff P xy
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ij))))))).mp
            (hrows _)
      exact le_antisymm hu hl
  · rintro ⟨hrelease, hcompletion, hforward, hbackward, hpair⟩ r
    rw [← (Fintype.equivFin (constraintRow n)).apply_symm_apply r]
    refine (rowInequality_iff P xy _).mpr ?_
    generalize (Fintype.equivFin (constraintRow n)).symm r = row
    rcases row with i | row
    · exact hrelease i
    · rcases row with i | row
      · exact le_of_eq (hcompletion i)
      · rcases row with i | row
        · exact le_of_eq (hcompletion i).symm
        · rcases row with a | row
          · exact hforward a
          · rcases row with a | row
            · exact hbackward a
            · rcases row with ij | ij
              · exact le_of_eq (hpair ij.1.1 ij.1.2 ij.2)
              · exact le_of_eq (hpair ij.1.1 ij.1.2 ij.2).symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
rebuilding an arc from its tail and head preserves it. -/
private theorem jobArcOfNe_tail_head
    (a : jobArc n) :
    jobArcOfNe (jobArcTail a) (jobArcHead a) a.2 = a := by
  -- Subtype extensionality reduces the claim to the unchanged ordered pair.
  apply Subtype.ext
  rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
rebuilding the opposite orientation gives the reversed arc. -/
private theorem jobArcOfNe_head_tail
    (a : jobArc n) :
    jobArcOfNe (jobArcHead a) (jobArcTail a) a.2.symm = reverseJobArc a := by
  -- Subtype extensionality reduces the claim to the reversed ordered pair.
  apply Subtype.ext
  rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
an integral real in the unit interval is binary. -/
private theorem eq_zero_or_one_of_nonneg_of_le_one_of_intCast
    {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hx_le_one : x ≤ 1)
    (hx_int : ∃ z : ℤ, x = (z : ℝ)) :
    x = 0 ∨ x = 1 := by
  -- Transfer the two real bounds to the integral witness and enumerate the interval.
  rcases hx_int with ⟨z, rfl⟩
  have hz_nonneg : 0 ≤ z := by
    exact_mod_cast hx_nonneg
  have hz_le_one : z ≤ 1 := by
    exact_mod_cast hx_le_one
  by_cases hz_zero : z = 0
  · left
    simp [hz_zero]
  · have hz_pos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz_zero)
    have hone_le : 1 ≤ z := (Int.add_one_le_iff).mpr hz_pos
    have hz_one : z = 1 := le_antisymm hz_le_one hone_le
    right
    simp [hz_one]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
nonnegative integral orderings satisfying pairwise choice are binary. -/
private theorem ordering_binary_of_pairwiseChoice
    (δ : jobArc n → ℝ)
    (h_nonneg : ∀ a, 0 ≤ δ a)
    (h_int : ∀ a, ∃ z : ℤ, δ a = (z : ℝ))
    (h_pair : ∀ i j : Fin n, ∀ hij : i < j,
      δ (jobArcOfNe i j (ne_of_lt hij)) +
          δ (jobArcOfNe j i (ne_of_gt hij)) = 1) :
    ∀ a, δ a = 0 ∨ δ a = 1 := by
  -- Orient each off-diagonal arc, bound it using the opposite nonnegative arc, and use integrality.
  intro a
  rcases lt_or_gt_of_ne a.2 with hlt | hgt
  · have hchoice := h_pair (jobArcTail a) (jobArcHead a) hlt
    rw [jobArcOfNe_tail_head a, jobArcOfNe_head_tail a] at hchoice
    have ha_le_one : δ a ≤ 1 := by
      linarith [h_nonneg (reverseJobArc a)]
    exact eq_zero_or_one_of_nonneg_of_le_one_of_intCast (h_nonneg a) ha_le_one (h_int a)
  · have hchoice := h_pair (jobArcHead a) (jobArcTail a) hgt
    rw [jobArcOfNe_head_tail a, jobArcOfNe_tail_head a] at hchoice
    have ha_le_one : δ a ≤ 1 := by
      linarith [h_nonneg (reverseJobArc a)]
    exact eq_zero_or_one_of_nonneg_of_le_one_of_intCast (h_nonneg a) ha_le_one (h_int a)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
source feasibility of decoded coordinates is equivalent to MILP feasibility. -/
private theorem mixedPoint_mem_feasibleSet_iff
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    xy ∈ P.toMixedIntegerLinearProgram.feasibleSet ↔
      P.feasible (startTimeOfMixedPoint xy) (completionTimeOfMixedPoint xy)
        (orderingOfMixedPoint xy) := by
  -- Forward, decode the linear, sign, and integrality conditions and derive binary orderings.
  constructor
  · intro hxy
    rcases (P.toMixedIntegerLinearProgram.mem_feasibleSet_iff xy).mp hxy with
      ⟨hrows, hx_nonneg, hy_nonneg, hx_int⟩
    rcases (mixedPoint_linearConstraints_iff P xy).mp hrows with
      ⟨hrelease, hcompletion, hforward, hbackward, hpair⟩
    have hordering_nonneg : ∀ a, 0 ≤ orderingOfMixedPoint xy a := by
      intro a
      exact hx_nonneg ((Fintype.equivFin (jobArc n)) a)
    have hordering_int : ∀ a, ∃ z : ℤ, orderingOfMixedPoint xy a = (z : ℝ) := by
      intro a
      exact hx_int ((Fintype.equivFin (jobArc n)) a)
    have hbinary :=
      ordering_binary_of_pairwiseChoice (orderingOfMixedPoint xy)
        hordering_nonneg hordering_int hpair
    refine feasible_iff.mpr ⟨hrelease, hcompletion, hforward, hbackward, hpair, ?_, ?_, hbinary⟩
    · intro i
      exact hy_nonneg (Fin.castAdd n i)
    · intro i
      exact hy_nonneg (Fin.natAdd n i)
  · intro hsource
    -- Reassemble mixed `0,1` feasibility, whose canonical inclusion supplies MILP feasibility.
    apply P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet_subset_feasibleSet
    rw [P.toMixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff]
    refine ⟨(mixedPoint_linearConstraints_iff P xy).mpr ?_, ?_, ?_⟩
    · exact ⟨feasible_releaseTime hsource, feasible_completionTime hsource,
        feasible_nonoverlapForward hsource, feasible_nonoverlapBackward hsource,
        feasible_pairwiseChoice hsource⟩
    · intro k
      have hk := feasible_binary hsource ((Fintype.equivFin (jobArc n)).symm k)
      simpa [orderingOfMixedPoint] using hk
    · have hs : ∀ i : Fin n, 0 ≤ xy.2 (Fin.castAdd n i) := by
        intro i
        exact feasible_start_nonneg hsource i
      have hC : ∀ i : Fin n, 0 ≤ xy.2 (Fin.natAdd n i) := by
        intro i
        exact feasible_completion_nonneg hsource i
      exact Fin.addCases hs hC

/-- The canonical Chapter 1 MILP bridge for `P` is mixed `0,1`. -/
theorem toMixedIntegerLinearProgram_isMixedZeroOne
    (P : SingleMachineReleaseTimeProblem n) :
    P.toMixedIntegerLinearProgram.IsMixedZeroOne := by
  -- It suffices to show that every MILP-feasible point has binary integer coordinates.
  rw [MixedIntegerLinearProgram.isMixedZeroOne_iff_feasibleSet_subset_mixedZeroOneFeasibleSet]
  intro xy hxy
  rcases (P.toMixedIntegerLinearProgram.mem_feasibleSet_iff xy).mp hxy with
    ⟨hrows, -, hy_nonneg, -⟩
  have hsource := (mixedPoint_mem_feasibleSet_iff P xy).mp hxy
  rw [P.toMixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff]
  refine ⟨hrows, ?_, hy_nonneg⟩
  intro k
  have hk := feasible_binary hsource ((Fintype.equivFin (jobArc n)).symm k)
  simpa [orderingOfMixedPoint] using hk

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
decoding start times after encoding returns the original start vector. -/
@[simp] private theorem startTimeOfMixedPoint_toMixedPoint
    (s C : Fin n → ℝ)
    (δ : jobArc n → ℝ) :
    startTimeOfMixedPoint (toMixedPoint s C δ) = s := by
  -- Evaluate the left injection of the continuous coordinate split.
  funext i
  simp [startTimeOfMixedPoint, toMixedPoint]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
decoding completion times after encoding returns the original completion vector. -/
@[simp] private theorem completionTimeOfMixedPoint_toMixedPoint
    (s C : Fin n → ℝ)
    (δ : jobArc n → ℝ) :
    completionTimeOfMixedPoint (toMixedPoint s C δ) = C := by
  -- Evaluate the right injection of the continuous coordinate split.
  funext i
  unfold completionTimeOfMixedPoint toMixedPoint
  simpa only using (Fin.addCases_right i : Fin.addCases s C (Fin.natAdd n i) = C i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
decoding ordering variables after encoding returns the original arc vector. -/
@[simp] private theorem orderingOfMixedPoint_toMixedPoint
    (s C : Fin n → ℝ)
    (δ : jobArc n → ℝ) :
    orderingOfMixedPoint (toMixedPoint s C δ) = δ := by
  -- Cancel the finite equivalence used to enumerate directed arcs.
  funext a
  simp [orderingOfMixedPoint, toMixedPoint]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean:
the MILP objective is the source weighted completion-time objective on decoded coordinates. -/
private theorem objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
    (P : SingleMachineReleaseTimeProblem n)
    (xy : MixedRealPoint (Fintype.card (jobArc n)) (n + n)) :
    P.objectiveValue (completionTimeOfMixedPoint xy) =
      P.toMixedIntegerLinearProgram.objectiveValue xy := by
  -- The integer and start-time objective coefficients vanish; the completion block remains.
  rw [P.objectiveValue_def, P.toMixedIntegerLinearProgram.objectiveValue_def]
  unfold toMixedIntegerLinearProgram MixedIntegerLinearProgram.ofCoefficients
  rw [dotProduct, dotProduct, sum_addCases_mul]
  simp [completionTimeOfMixedPoint]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_57/SingleMachineReleaseTime.lean

The source-facing attained-value set of `P` agrees with the objective-value set of the
canonical Chapter 1 MILP bridge. -/
theorem objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues
    (P : SingleMachineReleaseTimeProblem n) :
    P.objectiveValues = P.toMixedIntegerLinearProgram.objectiveValues := by
  -- Transport objective witnesses in both directions through the coordinate equivalence.
  ext r
  rw [mem_objectiveValues_iff, P.toMixedIntegerLinearProgram.mem_objectiveValues_iff]
  constructor
  · rintro ⟨s, C, δ, hsource, hvalue⟩
    refine ⟨toMixedPoint s C δ, ?_, ?_⟩
    · apply (mixedPoint_mem_feasibleSet_iff P (toMixedPoint s C δ)).mpr
      simpa using hsource
    · calc
        P.toMixedIntegerLinearProgram.objectiveValue (toMixedPoint s C δ) =
            P.objectiveValue C := by
          symm
          simpa using
            objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue P
              (toMixedPoint s C δ)
        _ = r := hvalue
  · rintro ⟨xy, hxy, hvalue⟩
    refine ⟨startTimeOfMixedPoint xy, completionTimeOfMixedPoint xy,
      orderingOfMixedPoint xy, ?_, ?_⟩
    · exact (mixedPoint_mem_feasibleSet_iff P xy).mp hxy
    · calc
        P.objectiveValue (completionTimeOfMixedPoint xy) =
            P.toMixedIntegerLinearProgram.objectiveValue xy :=
          objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue P xy
        _ = r := hvalue

end SingleMachineReleaseTimeProblem
