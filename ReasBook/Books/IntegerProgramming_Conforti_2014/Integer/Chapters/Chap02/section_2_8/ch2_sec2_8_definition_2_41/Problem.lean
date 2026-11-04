/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_3

open scoped BigOperators Matrix MixedIntegerNotation

/-- An operating-room scheduling problem with surgery-time matrix and room-time bound. -/
structure OperatingRoomSchedulingProblem (m n : ℕ) where
  surgeryTime : Matrix (Fin m) (Fin n) ℝ
  timeBound : ℝ

namespace OperatingRoomSchedulingProblem

/-- Construct an operating-room scheduling problem from its surgery-time matrix and room-time
bound. -/
def ofData
    {m n : ℕ}
    (surgeryTime : Matrix (Fin m) (Fin n) ℝ)
    (timeBound : ℝ) :
    OperatingRoomSchedulingProblem m n :=
  { surgeryTime := surgeryTime
    timeBound := timeBound }

/-- The canonical equivalence between matrix coordinates and flattened schedule indices. -/
private abbrev scheduleIndexEquiv (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) :=
  finProdFinEquiv

/-- The flattened index corresponding to the schedule entry in row `i` and column `j`. -/
private def scheduleIndex
    {m n : ℕ}
    (i : Fin m)
    (j : Fin n) :
    Fin (m * n) :=
  scheduleIndexEquiv m n (i, j)

@[simp] private theorem scheduleIndexEquiv_symm_scheduleIndex
    {m n : ℕ}
    (i : Fin m)
    (j : Fin n) :
    (scheduleIndexEquiv m n).symm (scheduleIndex i j) = (i, j) := by
  simp [scheduleIndex]

/-- Flatten a schedule matrix to the integer-variable block of the canonical Chapter 1 MILP. -/
private def scheduleVector
    {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) ℝ) :
    Fin (m * n) → ℝ :=
  fun k ↦
    let ij := (scheduleIndexEquiv m n).symm k
    x ij.1 ij.2

/-- Rebuild a schedule matrix from the flattened integer-variable block of the canonical Chapter 1
MILP. -/
private def scheduleMatrix
    {m n : ℕ}
    (x : Fin (m * n) → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j ↦ x (scheduleIndex i j)

/-- The canonical equivalence between schedule matrices and flattened MILP integer-variable
vectors. -/
private def scheduleEquiv
    {m n : ℕ} :
    Matrix (Fin m) (Fin n) ℝ ≃ (Fin (m * n) → ℝ) where
  toFun := scheduleVector
  invFun := scheduleMatrix
  left_inv x := by
    ext i j
    simp [scheduleVector, scheduleMatrix, scheduleIndex]
  right_inv x := by
    funext k
    exact congrArg x ((scheduleIndexEquiv m n).apply_symm_apply k)

@[simp] private theorem scheduleVector_apply
    {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m)
    (j : Fin n) :
    scheduleVector x (scheduleIndex i j) = x i j := by
  simp [scheduleVector, scheduleIndex]

@[simp] private theorem scheduleMatrix_apply
    {m n : ℕ}
    (x : Fin (m * n) → ℝ)
    (i : Fin m)
    (j : Fin n) :
    scheduleMatrix x i j = x (scheduleIndex i j) := by
  rfl

@[simp] private theorem scheduleMatrix_scheduleVector
    {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) ℝ) :
    scheduleMatrix (scheduleVector x) = x :=
  scheduleEquiv.left_inv x

@[simp] private theorem scheduleVector_scheduleMatrix
    {m n : ℕ}
    (x : Fin (m * n) → ℝ) :
    scheduleVector (scheduleMatrix x) = x :=
  scheduleEquiv.right_inv x

/-- View a schedule matrix as a mixed point with no continuous block. -/
private def toMixedPoint
    {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) ℝ) :
    MixedRealPoint (m * n) 0 :=
  (scheduleVector x, fun i ↦ Fin.elim0 i)

/-- Recover the schedule matrix from the integer block of a mixed point with no continuous
variables. -/
private def scheduleOfMixedPoint
    {m n : ℕ}
    (xy : MixedRealPoint (m * n) 0) :
    Matrix (Fin m) (Fin n) ℝ :=
  scheduleMatrix xy.1

private theorem eq_toMixedPoint_scheduleOfMixedPoint
    {m n : ℕ}
    (xy : MixedRealPoint (m * n) 0) :
    xy = toMixedPoint (scheduleOfMixedPoint xy) := by
  cases xy with
  | mk x y =>
      apply Prod.ext
      · simp [toMixedPoint, scheduleOfMixedPoint]
      · funext i
        exact Fin.elim0 i

/-- The operating-room scheduling data as the canonical Chapter 1 mixed integer linear program
with `m * n` integer variables and no continuous variables. -/
def toMixedIntegerLinearProgram
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n) :
    MixedIntegerLinearProgram (m + n) (m * n) 0 :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun r k ↦
      let ij := (scheduleIndexEquiv m n).symm k
      Fin.addCases
        (fun i : Fin m ↦ if ij.1 = i then 1 else 0)
        (fun j : Fin n ↦ if ij.2 = j then P.surgeryTime ij.1 ij.2 else 0)
        r)
    0
    (Fin.addCases (fun _ : Fin m ↦ 1) (fun _ : Fin n ↦ P.timeBound))
    (fun k ↦
      let ij := (scheduleIndexEquiv m n).symm k
      P.surgeryTime ij.1 ij.2)
    0

private theorem sum_scheduleIndexEquiv
    {m n : ℕ}
    (f : Fin m × Fin n → ℝ) :
    (∑ k : Fin (m * n), f ((scheduleIndexEquiv m n).symm k)) =
      ∑ i : Fin m, ∑ j : Fin n, f (i, j) := by
  -- Reindex the flattened sum by the canonical equivalence with matrix coordinates.
  calc
    (∑ k : Fin (m * n), f ((scheduleIndexEquiv m n).symm k)) =
        ∑ ij : Fin m × Fin n, f ij := by
          exact
            Fintype.sum_equiv (scheduleIndexEquiv m n).symm
              (fun k ↦ f ((scheduleIndexEquiv m n).symm k))
              (fun ij ↦ f ij)
              (fun _ ↦ rfl)
    _ = ∑ i : Fin m, ∑ j : Fin n, f (i, j) := by
          simpa using
            (Fintype.sum_prod_type (f := fun ij : Fin m × Fin n ↦ f ij))

private theorem integerMatrix_mul_scheduleVector_apply_row
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) :
    ((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ scheduleVector x)
        (Fin.castAdd n i)) =
      ∑ j : Fin n, x i j := by
  -- Reindex the flattened row dot product and collapse the row-selector coefficients.
  rw [Matrix.mulVec, dotProduct]
  calc
    ∑ k : Fin (m * n),
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.castAdd n i) k * scheduleVector x k =
        ∑ i' : Fin m, ∑ j' : Fin n, (if i' = i then 1 else 0) * x i' j' := by
          simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
            scheduleVector] using
            (sum_scheduleIndexEquiv
              (f := fun ij : Fin m × Fin n ↦ (if ij.1 = i then 1 else 0) * x ij.1 ij.2))
    _ = ∑ j : Fin n, x i j := by
      simp

private theorem integerMatrix_mul_scheduleVector_apply_room
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    ((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ scheduleVector x)
        (Fin.natAdd m j)) =
      ∑ i : Fin m, P.surgeryTime i j * x i j := by
  -- Reindex the flattened room constraint and keep only the matching room column.
  rw [Matrix.mulVec, dotProduct]
  calc
    ∑ k : Fin (m * n),
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.natAdd m j) k * scheduleVector x k =
        ∑ i' : Fin m, ∑ j' : Fin n,
          (if j' = j then P.surgeryTime i' j' else 0) * x i' j' := by
          simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
            scheduleVector] using
            (sum_scheduleIndexEquiv
              (f := fun ij : Fin m × Fin n ↦
                (if ij.2 = j then P.surgeryTime ij.1 ij.2 else 0) * x ij.1 ij.2))
    _ = ∑ i : Fin m, P.surgeryTime i j * x i j := by
      simp

private theorem integerObjective_dot_scheduleVector
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ) :
    P.toMixedIntegerLinearProgram.integerObjective ⬝ᵥ scheduleVector x =
      ∑ i : Fin m, ∑ j : Fin n, P.surgeryTime i j * x i j := by
  -- Reindex the flattened objective sum into the displayed double sum.
  rw [dotProduct]
  simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients, scheduleVector]
    using
      (sum_scheduleIndexEquiv
        (f := fun ij : Fin m × Fin n ↦ P.surgeryTime ij.1 ij.2 * x ij.1 ij.2))

/-- Helper for Definition 2.41: an integer whose real cast lies in `[0, 1]` is `0` or `1`. -/
private lemma intCast_eq_zero_or_one_of_nonneg_le_one
    {z : ℤ}
    (hz_nonneg : 0 ≤ (z : ℝ))
    (hz_le_one : (z : ℝ) ≤ 1) :
    z = 0 ∨ z = 1 := by
  -- Transfer the real bounds back to `ℤ`, then enumerate the only possible integers.
  have hz_nonneg' : 0 ≤ z := by
    exact_mod_cast hz_nonneg
  have hz_le_one' : z ≤ 1 := by
    exact_mod_cast hz_le_one
  omega

/-- Helper for Definition 2.41: the zero-dimensional continuous constraint block contributes
nothing. -/
private theorem continuousMatrix_mulVec_eq_zero
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (y : Fin 0 → ℝ) :
    P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ y = 0 := by
  -- Every coordinate is a sum over the empty continuous index type.
  ext r
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec,
    dotProduct]

/-- Helper for Definition 2.41: the zero-dimensional continuous objective block contributes
nothing. -/
private theorem continuousObjective_dot_eq_zero
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (y : Fin 0 → ℝ) :
    P.toMixedIntegerLinearProgram.continuousObjective ⬝ᵥ y = 0 := by
  -- The dot product over the empty continuous index type is zero.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients, dotProduct]

/-- Helper for Definition 2.41: every coordinate of the zero-dimensional continuous block is `0`. -/
private theorem continuousMatrix_mulVec_apply_eq_zero
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (y : Fin 0 → ℝ)
    (r : Fin (m + n)) :
    (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ y) r = 0 := by
  -- Apply the zero-function identity at the desired row.
  simpa [continuousMatrix_mulVec_eq_zero P y] using
    congrArg (fun v : Fin (m + n) → ℝ ↦ v r) (continuousMatrix_mulVec_eq_zero P y)

/-- Helper for Definition 2.41: the row-block right-hand side is `1`. -/
private theorem rhs_apply_row
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (i : Fin m) :
    P.toMixedIntegerLinearProgram.rhs (Fin.castAdd n i) = 1 := by
  -- The first `m` rows enforce the assignment inequalities.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]

/-- Helper for Definition 2.41: the room-block right-hand side is `P.timeBound`. -/
private theorem rhs_apply_room
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (j : Fin n) :
    P.toMixedIntegerLinearProgram.rhs (Fin.natAdd m j) = P.timeBound := by
  -- The last `n` rows enforce the room-time inequalities.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]

/-- The feasible schedule matrices of `P`, defined as the preimage of the canonical Chapter 1
mixed `0,1` feasible set under the schedule-matrix flattening map. -/
def feasibleSet
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x | toMixedPoint x ∈ P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet}

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed assignment,
room-time, and binary constraints. -/
theorem mem_feasibleSet_iff
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ} :
    x ∈ P.feasibleSet ↔
      (∀ i : Fin m, ∑ j : Fin n, x i j ≤ 1) ∧
        (∀ j : Fin n, ∑ i : Fin m, P.surgeryTime i j * x i j ≤ P.timeBound) ∧
          ∀ i : Fin m, ∀ j : Fin n, x i j = 0 ∨ x i j = 1 := by
  -- Unfold mixed `0,1` feasibility and project the flattened constraints onto rows, rooms,
  -- and schedule entries.
  change toMixedPoint x ∈ P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet ↔
      (∀ i : Fin m, ∑ j : Fin n, x i j ≤ 1) ∧
        (∀ j : Fin n, ∑ i : Fin m, P.surgeryTime i j * x i j ≤ P.timeBound) ∧
          ∀ i : Fin m, ∀ j : Fin n, x i j = 0 ∨ x i j = 1
  rw [P.toMixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff (toMixedPoint x)]
  constructor
  · rintro ⟨hineq, hbinary, hcontinuous⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hcontinuous_row :
          (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ fun i ↦ i.elim0)
              (Fin.castAdd n i) = 0 := by
        simpa [toMixedPoint] using
          continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint x).2 (Fin.castAdd n i)
      have hrow_i : ∑ j : Fin n, x i j + 0 ≤ 1 := by
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_row, toMixedPoint,
          integerMatrix_mul_scheduleVector_apply_row] using hineq (Fin.castAdd n i)
      simpa using hrow_i
    · intro j
      have hcontinuous_room :
          (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ fun i ↦ i.elim0)
              (Fin.natAdd m j) = 0 := by
        simpa [toMixedPoint] using
          continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint x).2 (Fin.natAdd m j)
      have hroom_j : ∑ i : Fin m, P.surgeryTime i j * x i j + 0 ≤ P.timeBound := by
        simpa [Pi.add_apply, hcontinuous_room, rhs_apply_room, toMixedPoint,
          integerMatrix_mul_scheduleVector_apply_room] using hineq (Fin.natAdd m j)
      simpa using hroom_j
    · intro i j
      simpa [toMixedPoint, scheduleVector_apply] using hbinary (scheduleIndex i j)
  · rintro ⟨hrow, hroom, hbinary⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r
      refine Fin.addCases ?_ ?_ r
      · intro i
        have hcontinuous_row :
            (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ fun i ↦ i.elim0)
                (Fin.castAdd n i) = 0 := by
          simpa [toMixedPoint] using
            continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint x).2 (Fin.castAdd n i)
        have hrow_i : ∑ j : Fin n, x i j + 0 ≤ 1 := by
          simpa using hrow i
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_row, toMixedPoint,
          integerMatrix_mul_scheduleVector_apply_row] using hrow_i
      · intro j
        have hcontinuous_room :
            (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ fun i ↦ i.elim0)
                (Fin.natAdd m j) = 0 := by
          simpa [toMixedPoint] using
            continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint x).2 (Fin.natAdd m j)
        have hroom_j : ∑ i : Fin m, P.surgeryTime i j * x i j + 0 ≤ P.timeBound := by
          simpa using hroom j
        simpa [Pi.add_apply, hcontinuous_room, rhs_apply_room, toMixedPoint,
          integerMatrix_mul_scheduleVector_apply_room] using hroom_j
    · intro k
      rcases hpair : (scheduleIndexEquiv m n).symm k with ⟨i, j⟩
      simpa [toMixedPoint, scheduleVector, hpair] using hbinary i j
    · intro k
      exact Fin.elim0 k

/-- A feasible operating-room schedule assigns each surgery to at most one room. -/
theorem feasible_rowSum_le_one
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (i : Fin m) :
    ∑ j : Fin n, x i j ≤ 1 := by
  exact (mem_feasibleSet_iff.mp hx).1 i

/-- A feasible operating-room schedule satisfies the room-time inequality in every room column. -/
theorem feasible_roomTime_le
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (j : Fin n) :
    ∑ i : Fin m, P.surgeryTime i j * x i j ≤ P.timeBound := by
  exact (mem_feasibleSet_iff.mp hx).2.1 j

/-- Every entry of a feasible operating-room schedule matrix is binary. -/
theorem feasible_binary
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {x : Matrix (Fin m) (Fin n) ℝ}
    (hx : x ∈ P.feasibleSet)
    (i : Fin m)
    (j : Fin n) :
    x i j = 0 ∨ x i j = 1 := by
  exact (mem_feasibleSet_iff.mp hx).2.2 i j

/-- Helper for Definition 2.41: every MILP-feasible mixed point is already mixed `0,1`. -/
private theorem mixedPoint_mem_mixedZeroOneFeasibleSet_of_mem_feasibleSet
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    {xy : MixedRealPoint (m * n) 0}
    (hxy : xy ∈ P.toMixedIntegerLinearProgram.feasibleSet) :
    xy ∈ P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet := by
  -- Extract the MILP inequalities, nonnegativity, and integrality from feasible membership.
  rw [P.toMixedIntegerLinearProgram.mem_feasibleSet_iff] at hxy
  rcases hxy with ⟨hineq, hx_nonneg, hy_nonneg, hint⟩
  rw [P.toMixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff]
  refine ⟨hineq, ?_, hy_nonneg⟩
  intro k
  rcases hpair : (scheduleIndexEquiv m n).symm k with ⟨i, j⟩
  have hk : scheduleIndex i j = k := by
    simpa [scheduleIndex, hpair] using (scheduleIndexEquiv m n).apply_symm_apply k
  have hcontinuous_row :
      (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ xy.2) (Fin.castAdd n i) = 0 :=
    continuousMatrix_mulVec_apply_eq_zero P xy.2 (Fin.castAdd n i)
  have hrow_raw :
      ((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1) (Fin.castAdd n i)) ≤ 1 := by
    -- The zero-dimensional continuous block vanishes in every row inequality.
    simpa [hcontinuous_row, rhs_apply_row] using hineq (Fin.castAdd n i)
  have hrow_le_one : ∑ j' : Fin n, scheduleMatrix xy.1 i j' ≤ 1 := by
    -- The row block of the MILP inequality is exactly the schedule row-sum constraint.
    calc
      ∑ j' : Fin n, scheduleMatrix xy.1 i j' =
          ((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ scheduleVector (scheduleMatrix xy.1))
            (Fin.castAdd n i)) := by
            symm
            exact integerMatrix_mul_scheduleVector_apply_row P (scheduleMatrix xy.1) i
      _ = ((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ xy.1) (Fin.castAdd n i)) := by
            simp [scheduleVector_scheduleMatrix]
      _ ≤ 1 := hrow_raw
  have hentry_le_row : scheduleMatrix xy.1 i j ≤ ∑ j' : Fin n, scheduleMatrix xy.1 i j' := by
    -- A single nonnegative row entry is bounded by the full nonnegative row sum.
    refine Finset.single_le_sum ?_ ?_
    · intro j' hj'
      simpa [scheduleMatrix_apply] using hx_nonneg (scheduleIndex i j')
    · simp
  have hentry_nonneg : 0 ≤ xy.1 (scheduleIndex i j) := by
    simpa using hx_nonneg (scheduleIndex i j)
  have hentry_le_one : xy.1 (scheduleIndex i j) ≤ 1 := by
    calc
      xy.1 (scheduleIndex i j) = scheduleMatrix xy.1 i j := by
        simp [scheduleMatrix_apply, scheduleIndex]
      _ ≤ ∑ j' : Fin n, scheduleMatrix xy.1 i j' := hentry_le_row
      _ ≤ 1 := hrow_le_one
  rcases hint (scheduleIndex i j) with ⟨z, hz⟩
  rcases intCast_eq_zero_or_one_of_nonneg_le_one (by simpa [hz] using hentry_nonneg)
      (by simpa [hz] using hentry_le_one) with hz0 | hz1
  · left
    simpa [hk, hz0] using hz
  · right
    simpa [hk, hz1] using hz

/-- Every Chapter 1 MILP-feasible point of `P.toMixedIntegerLinearProgram` determines a feasible
source-facing schedule matrix. -/
private theorem scheduleOfMixedPoint_mem_feasibleSet_of_mem_toMixedIntegerLinearProgram_feasibleSet
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    {xy : MixedRealPoint (m * n) 0}
    (hxy : xy ∈ P.toMixedIntegerLinearProgram.feasibleSet) :
    scheduleOfMixedPoint xy ∈ P.feasibleSet := by
  -- Upgrade the MILP-feasible point to mixed `0,1` feasibility, then transport it back to the
  -- schedule matrix representation.
  change
    toMixedPoint (scheduleOfMixedPoint xy) ∈
      P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet
  have hxy' : xy ∈ P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet :=
    mixedPoint_mem_mixedZeroOneFeasibleSet_of_mem_feasibleSet P hxy
  rw [← eq_toMixedPoint_scheduleOfMixedPoint xy]
  exact hxy'

/-- The canonical Chapter 1 MILP attached to an operating-room scheduling problem is mixed `0,1`. -/
theorem toMixedIntegerLinearProgram_isMixedZeroOne
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n) :
    P.toMixedIntegerLinearProgram.IsMixedZeroOne := by
  -- Route correction: prove mixed-`0,1` status by feasible-set inclusion into the canonical
  -- mixed-`0,1` feasible set, then invoke the Chapter 1 characterization.
  rw [MixedIntegerLinearProgram.isMixedZeroOne_iff_feasibleSet_subset_mixedZeroOneFeasibleSet]
  intro xy hxy
  exact mixedPoint_mem_mixedZeroOneFeasibleSet_of_mem_feasibleSet P hxy

/-- The operating-room scheduling objective value of `x`, defined via the canonical Chapter 1 MILP
objective on the flattened schedule vector. -/
def objectiveValue
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  P.toMixedIntegerLinearProgram.objectiveValue (toMixedPoint x)

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_def
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n)
    (x : Matrix (Fin m) (Fin n) ℝ) :
    P.objectiveValue x =
      ∑ i : Fin m, ∑ j : Fin n, P.surgeryTime i j * x i j := by
  -- Expand the Chapter 1 MILP objective and collapse the zero continuous block.
  have hcontinuous_zero :
      P.toMixedIntegerLinearProgram.continuousObjective ⬝ᵥ (toMixedPoint x).2 = 0 :=
    continuousObjective_dot_eq_zero P (toMixedPoint x).2
  rw [objectiveValue, P.toMixedIntegerLinearProgram.objectiveValue_def]
  change P.toMixedIntegerLinearProgram.integerObjective ⬝ᵥ scheduleVector x +
      P.toMixedIntegerLinearProgram.continuousObjective ⬝ᵥ (toMixedPoint x).2 =
    ∑ i : Fin m, ∑ j : Fin n, P.surgeryTime i j * x i j
  rw [integerObjective_dot_scheduleVector, hcontinuous_zero]
  simp

/-- The objective values attained by feasible schedules of the operating-room scheduling problem
`P`. -/
def objectiveValues
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- The source-facing attained-value set of `P` agrees with the objective-value set of its
canonical Chapter 1 MILP. -/
theorem objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues
    {m n : ℕ}
    (P : OperatingRoomSchedulingProblem m n) :
    P.objectiveValues = P.toMixedIntegerLinearProgram.objectiveValues := by
  -- Transport attained-value witnesses back and forth across the schedule/mixed-point
  -- equivalence.
  ext r
  change (∃ x : Matrix (Fin m) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r) ↔
    ∃ xy ∈ P.toMixedIntegerLinearProgram.feasibleSet,
      P.toMixedIntegerLinearProgram.objectiveValue xy = r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨toMixedPoint x, ?_, rfl⟩
    exact
      P.toMixedIntegerLinearProgram.mixedZeroOneFeasibleSet_subset_feasibleSet
        (by simpa [feasibleSet] using hx)
  · rintro ⟨xy, hxy, rfl⟩
    refine ⟨scheduleOfMixedPoint xy, ?_, ?_⟩
    · exact
        scheduleOfMixedPoint_mem_feasibleSet_of_mem_toMixedIntegerLinearProgram_feasibleSet
          P hxy
    · simpa [objectiveValue] using
        congrArg P.toMixedIntegerLinearProgram.objectiveValue
          (eq_toMixedPoint_scheduleOfMixedPoint xy).symm

/-- Foundation-level witness form for membership in `P.objectiveValues`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m n : ℕ}
    {P : OperatingRoomSchedulingProblem m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Matrix (Fin m) (Fin n) ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  rfl

end OperatingRoomSchedulingProblem
