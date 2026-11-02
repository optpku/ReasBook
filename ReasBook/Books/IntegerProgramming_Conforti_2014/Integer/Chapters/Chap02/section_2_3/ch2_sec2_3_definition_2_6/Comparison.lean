module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_definition_2_6.RollIndexed
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.Problem
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators Matrix MixedIntegerNotation

public section

namespace CuttingStock
namespace RollIndexed

private abbrev cutIndexEquiv (m p : ℕ) : Fin m × Fin p ≃ Fin (m * p) :=
  finProdFinEquiv

/-- Helper for Definition 2.6: the flattened index of the cut-count variable `z i j`. -/
private def cutIndex
    {m p : ℕ}
    (i : Fin m)
    (j : Fin p) :
    Fin (m * p) :=
  cutIndexEquiv m p (i, j)

@[simp] private theorem cutIndexEquiv_symm_cutIndex
    {m p : ℕ}
    (i : Fin m)
    (j : Fin p) :
    (cutIndexEquiv m p).symm (cutIndex i j) = (i, j) := by
  simp [cutIndex]

/-- The Chapter 1 mixed point corresponding to the roll-use vector `y` and cut-count matrix `z`,
with empty continuous block. -/
def toMixedPoint
    {m p : ℕ}
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ) :
    MixedRealPoint (p + m * p) 0 :=
  (fun k ↦
    Fin.addCases
      (fun j : Fin p ↦ (y j : ℝ))
      (fun l : Fin (m * p) ↦
        let ij := (cutIndexEquiv m p).symm l
        (z ij.1 ij.2 : ℝ))
      k,
    fun i ↦ Fin.elim0 i)

/-- The roll-indexed cutting stock formulation as a canonical Chapter 1 mixed integer linear
program with one integer block for the roll-use variables `y`, one integer block for the cut-count
variables `z`, and no continuous variables. -/
def toMixedIntegerLinearProgram
    {m p : ℕ}
    (P : RollIndexed m p) :
    MixedIntegerLinearProgram ((p + m) + p) (p + m * p) 0 :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun r k ↦
      Fin.addCases
        (fun r₁ : Fin (p + m) ↦
          Fin.addCases
            (fun j : Fin p ↦
              Fin.addCases
                (fun j' : Fin p ↦ if j' = j then -(P.stockWidth : ℝ) else 0)
                (fun l : Fin (m * p) ↦
                  let ij := (cutIndexEquiv m p).symm l
                  if ij.2 = j then (P.itemWidth ij.1 : ℝ) else 0)
                k)
            (fun i : Fin m ↦
              Fin.addCases
                (fun _ : Fin p ↦ 0)
                (fun l : Fin (m * p) ↦
                  let ij := (cutIndexEquiv m p).symm l
                  if ij.1 = i then (-1 : ℝ) else 0)
                k)
            r₁)
        (fun j : Fin p ↦
          Fin.addCases
            (fun j' : Fin p ↦ if j' = j then (1 : ℝ) else 0)
            (fun _ : Fin (m * p) ↦ 0)
            k)
        r)
    0
    (Fin.addCases
      (fun r₁ : Fin (p + m) ↦
        Fin.addCases
          (fun _ : Fin p ↦ 0)
          (fun i : Fin m ↦ -((P.demand i : ℕ) : ℝ))
          r₁)
      (fun _ : Fin p ↦ 1))
    (Fin.addCases
      (fun _ : Fin p ↦ (1 : ℝ))
      (fun _ : Fin (m * p) ↦ 0))
    0

/-- Helper for Definition 2.6: reindex a sum over flattened cut indices into the matrix
coordinates `(i, j)`. -/
private theorem sum_cutIndexEquiv
    {m p : ℕ}
    (f : Fin m × Fin p → ℝ) :
    (∑ l : Fin (m * p), f ((cutIndexEquiv m p).symm l)) =
      ∑ i : Fin m, ∑ j : Fin p, f (i, j) := by
  -- Reindex the flattened sum by the canonical product equivalence.
  calc
    (∑ l : Fin (m * p), f ((cutIndexEquiv m p).symm l)) =
        ∑ ij : Fin m × Fin p, f ij := by
          exact
            Fintype.sum_equiv (cutIndexEquiv m p).symm
              (fun l ↦ f ((cutIndexEquiv m p).symm l))
              (fun ij ↦ f ij)
              (fun _ ↦ rfl)
    _ = ∑ i : Fin m, ∑ j : Fin p, f (i, j) := by
          simpa using
            (Fintype.sum_prod_type (f := fun ij : Fin m × Fin p ↦ f ij))

/-- Helper for Definition 2.6: split a sum over `Fin (a + b)` into its left and right blocks. -/
private theorem sum_univ_split
    {a b : ℕ}
    (f : Fin (a + b) → ℝ) :
    (∑ k : Fin (a + b), f k) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ j : Fin b, f (Fin.natAdd a j) := by
  -- Reindex the sum by the canonical equivalence `Fin (a + b) ≃ Fin a ⊕ Fin b`.
  calc
    (∑ k : Fin (a + b), f k) =
        ∑ s : Fin a ⊕ Fin b, f (finSumFinEquiv s) := by
          exact
            Fintype.sum_equiv finSumFinEquiv.symm
              (fun k : Fin (a + b) ↦ f k)
              (fun s : Fin a ⊕ Fin b ↦ f (finSumFinEquiv s))
              (fun _ ↦ by simp)
    _ = (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ j : Fin b, f (Fin.natAdd a j) := by
          simp

/-- Helper for Definition 2.6: the zero-dimensional continuous constraint block contributes
nothing to every row. -/
private theorem continuousMatrix_mulVec_eq_zero
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin 0 → ℝ) :
    (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ y) = 0 := by
  -- Every row sum over the empty continuous block vanishes.
  ext r
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients, Matrix.mulVec,
    dotProduct]

/-- Helper for Definition 2.6: apply the zero continuous-block identity at one row. -/
private theorem continuousMatrix_mulVec_apply_eq_zero
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin 0 → ℝ)
    (r : Fin ((p + m) + p)) :
    ((P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ y) r) = 0 := by
  -- Evaluate the zero function produced by the empty continuous block.
  simpa [continuousMatrix_mulVec_eq_zero P y] using
    congrArg (fun v : Fin ((p + m) + p) → ℝ ↦ v r) (continuousMatrix_mulVec_eq_zero P y)

/-- Helper for Definition 2.6: the zero-dimensional continuous objective block contributes
nothing. -/
private theorem continuousObjective_dot_eq_zero
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin 0 → ℝ) :
    P.toMixedIntegerLinearProgram.continuousObjective ⬝ᵥ y = 0 := by
  -- The objective has no continuous variables.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients, dotProduct]

/-- Helper for Definition 2.6: the width-row right-hand side is `0`. -/
private theorem rhs_apply_width
    {m p : ℕ}
    (P : RollIndexed m p)
    (j : Fin p) :
    P.toMixedIntegerLinearProgram.rhs (Fin.castAdd p (Fin.castAdd m j)) = 0 := by
  -- The first `p` rows encode the width inequalities.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]

/-- Helper for Definition 2.6: the demand-row right-hand side is `-(P.demand i)`. -/
private theorem rhs_apply_demand
    {m p : ℕ}
    (P : RollIndexed m p)
    (i : Fin m) :
    P.toMixedIntegerLinearProgram.rhs (Fin.castAdd p (Fin.natAdd p i)) = -((P.demand i : ℕ) : ℝ) := by
  -- The middle `m` rows encode the demand-cover inequalities.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]

/-- Helper for Definition 2.6: the roll-upper-bound row right-hand side is `1`. -/
private theorem rhs_apply_upper
    {m p : ℕ}
    (P : RollIndexed m p)
    (j : Fin p) :
    P.toMixedIntegerLinearProgram.rhs (Fin.natAdd (p + m) j) = 1 := by
  -- The last `p` rows impose `y_j ≤ 1`.
  simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]

/-- Helper for Definition 2.6: the width row of the MILP bridge evaluates to the displayed
left-hand side `-W * y j + ∑ i, w_i * z i j`. -/
private theorem integerMatrix_mulVec_apply_width
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ)
    (j : Fin p) :
    (((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ (toMixedPoint y z).1))
        (Fin.castAdd p (Fin.castAdd m j))) =
      -(P.stockWidth : ℝ) * y j +
        ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j := by
  -- Split the flattened integer block into the `y`-coordinates and the flattened `z`-coordinates.
  rw [Matrix.mulVec, dotProduct, sum_univ_split]
  calc
    (∑ j' : Fin p,
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.castAdd p (Fin.castAdd m j))
            (Fin.castAdd (m * p) j') *
          (toMixedPoint y z).1 (Fin.castAdd (m * p) j')) +
      ∑ l : Fin (m * p),
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.castAdd p (Fin.castAdd m j))
            (Fin.natAdd p l) *
          (toMixedPoint y z).1 (Fin.natAdd p l) =
      ∑ j' : Fin p, (if j' = j then -(P.stockWidth : ℝ) else 0) * y j' +
        ∑ l : Fin (m * p),
          (if ((cutIndexEquiv m p).symm l).2 = j
            then (P.itemWidth ((cutIndexEquiv m p).symm l).1 : ℝ)
            else 0) *
            (z ((cutIndexEquiv m p).symm l).1 ((cutIndexEquiv m p).symm l).2 : ℝ) := by
          simp [toMixedPoint, toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]
    _ =
      -(P.stockWidth : ℝ) * y j +
        ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j := by
          congr 1
          · simp
          · calc
              ∑ l : Fin (m * p),
                  (if ((cutIndexEquiv m p).symm l).2 = j
                    then (P.itemWidth ((cutIndexEquiv m p).symm l).1 : ℝ)
                    else 0) *
                    (z ((cutIndexEquiv m p).symm l).1 ((cutIndexEquiv m p).symm l).2 : ℝ) =
                  ∑ i : Fin m, ∑ j' : Fin p,
                    (if j' = j then (P.itemWidth i : ℝ) else 0) * z i j' := by
                      simpa using
                        (sum_cutIndexEquiv
                          (f := fun ij : Fin m × Fin p ↦
                            (if ij.2 = j then (P.itemWidth ij.1 : ℝ) else 0) *
                              (z ij.1 ij.2 : ℝ)))
              _ = ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j := by
                    simp

/-- Helper for Definition 2.6: the demand row of the MILP bridge evaluates to the displayed
left-hand side `-∑ j, z i j`. -/
private theorem integerMatrix_mulVec_apply_demand
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ)
    (i : Fin m) :
    (((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ (toMixedPoint y z).1))
        (Fin.castAdd p (Fin.natAdd p i))) =
      -∑ j : Fin p, (z i j : ℝ) := by
  -- Only the flattened `z`-coordinates of row `i` survive, each with coefficient `-1`.
  rw [Matrix.mulVec, dotProduct, sum_univ_split]
  calc
    (∑ j' : Fin p,
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.castAdd p (Fin.natAdd p i))
            (Fin.castAdd (m * p) j') *
          (toMixedPoint y z).1 (Fin.castAdd (m * p) j')) +
      ∑ l : Fin (m * p),
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.castAdd p (Fin.natAdd p i))
            (Fin.natAdd p l) *
          (toMixedPoint y z).1 (Fin.natAdd p l) =
      ∑ l : Fin (m * p),
        (if ((cutIndexEquiv m p).symm l).1 = i then (-1 : ℝ) else 0) *
          (z ((cutIndexEquiv m p).symm l).1 ((cutIndexEquiv m p).symm l).2 : ℝ) := by
          simp [toMixedPoint, toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]
    _ = ∑ i' : Fin m, ∑ j : Fin p, (if i' = i then (-1 : ℝ) else 0) * z i' j := by
          simpa using
            (sum_cutIndexEquiv
              (f := fun ij : Fin m × Fin p ↦
                (if ij.1 = i then (-1 : ℝ) else 0) * (z ij.1 ij.2 : ℝ)))
    _ = -∑ j : Fin p, (z i j : ℝ) := by
          simp [Finset.mul_sum]

/-- Helper for Definition 2.6: the roll-upper-bound row of the MILP bridge evaluates to `y j`. -/
private theorem integerMatrix_mulVec_apply_upper
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ)
    (j : Fin p) :
    (((P.toMixedIntegerLinearProgram.integerMatrix *ᵥ (toMixedPoint y z).1))
        (Fin.natAdd (p + m) j)) =
      (y j : ℝ) := by
  -- The last `p` rows read off the roll-use coordinate and ignore every cut-count variable.
  rw [Matrix.mulVec, dotProduct, sum_univ_split]
  calc
    (∑ j' : Fin p,
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.natAdd (p + m) j)
            (Fin.castAdd (m * p) j') *
          (toMixedPoint y z).1 (Fin.castAdd (m * p) j')) +
      ∑ l : Fin (m * p),
        P.toMixedIntegerLinearProgram.integerMatrix (Fin.natAdd (p + m) j)
            (Fin.natAdd p l) *
          (toMixedPoint y z).1 (Fin.natAdd p l) =
      ∑ j' : Fin p, (if j' = j then (1 : ℝ) else 0) * y j' := by
          simp [toMixedPoint, toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]
    _ = y j := by
          simp

/-- Helper for Definition 2.6: the integer objective of the MILP bridge is exactly `∑ j, y j` on
the source point `(y, z)`. -/
private theorem integerObjective_dot_toMixedPoint
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ) :
    P.toMixedIntegerLinearProgram.integerObjective ⬝ᵥ (toMixedPoint y z).1 =
      ((∑ j : Fin p, y j : ℕ) : ℝ) := by
  -- The objective keeps the `y`-block and kills the flattened `z`-block.
  rw [dotProduct, sum_univ_split]
  calc
    (∑ j : Fin p,
        P.toMixedIntegerLinearProgram.integerObjective (Fin.castAdd (m * p) j) *
          (toMixedPoint y z).1 (Fin.castAdd (m * p) j)) +
      ∑ l : Fin (m * p),
        P.toMixedIntegerLinearProgram.integerObjective (Fin.natAdd p l) *
          (toMixedPoint y z).1 (Fin.natAdd p l) =
      ∑ j : Fin p, (1 : ℝ) * y j := by
          simp [toMixedPoint, toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients]
    _ = ∑ j : Fin p, y j := by
          simp

/-- A source-feasible roll-indexed solution is exactly a feasible point of the canonical Chapter 1
MILP bridge after inserting the empty continuous block and coercing the integer variables to `ℝ`. -/
theorem mem_toMixedIntegerLinearProgram_feasibleSet_iff
    {m p : ℕ}
    {P : RollIndexed m p}
    {y : Fin p → ℕ}
    {z : Matrix (Fin m) (Fin p) ℕ} :
    toMixedPoint y z ∈ P.toMixedIntegerLinearProgram.feasibleSet ↔
      (y, z) ∈ P.feasibleSet := by
  rw [P.toMixedIntegerLinearProgram.mem_feasibleSet_iff]
  constructor
  · rintro ⟨hineq, hx_nonneg, _, _⟩
    refine (mem_feasibleSet_iff : (y, z) ∈ P.feasibleSet ↔ _).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · intro j
      -- Read the width row of the MILP system as the source width inequality.
      have hcontinuous_row :
          (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
              (Fin.castAdd p (Fin.castAdd m j)) = 0 := by
        simpa [toMixedPoint] using
          continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
            (Fin.castAdd p (Fin.castAdd m j))
      have hrow_j :
          -(P.stockWidth : ℝ) * y j +
              ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j ≤ 0 := by
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_width, integerMatrix_mulVec_apply_width]
          using hineq (Fin.castAdd p (Fin.castAdd m j))
      have hsub :
          (∑ i : Fin m, (P.itemWidth i : ℝ) * z i j) - P.stockWidth * y j ≤ 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrow_j
      exact_mod_cast (sub_nonpos.mp hsub)
    · intro i
      -- Read the demand row and reverse the negation to recover the source covering inequality.
      have hcontinuous_row :
          (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
              (Fin.castAdd p (Fin.natAdd p i)) = 0 := by
        simpa [toMixedPoint] using
          continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
            (Fin.castAdd p (Fin.natAdd p i))
      have hrow_i :
          -∑ j : Fin p, (z i j : ℝ) ≤ -((P.demand i : ℕ) : ℝ) := by
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_demand, integerMatrix_mulVec_apply_demand]
          using hineq (Fin.castAdd p (Fin.natAdd p i))
      exact_mod_cast (neg_le_neg_iff.mp hrow_i)
    · intro j
      -- The upper-bound rows force the nonnegative integer variable `y j` to be at most `1`.
      have hcontinuous_row :
          (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
              (Fin.natAdd (p + m) j) = 0 := by
        simpa [toMixedPoint] using
          continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
            (Fin.natAdd (p + m) j)
      have hy_le_one_real : (y j : ℝ) ≤ 1 := by
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_upper, integerMatrix_mulVec_apply_upper]
          using hineq (Fin.natAdd (p + m) j)
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp (by exact_mod_cast hy_le_one_real)
  · intro hyz
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      -- Split the MILP rows into width rows, demand rows, and upper-bound rows.
      refine Fin.addCases ?_ ?_ r
      · intro r₁
        refine Fin.addCases ?_ ?_ r₁
        · intro j
          have hcontinuous_row :
              (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
                  (Fin.castAdd p (Fin.castAdd m j)) = 0 := by
            simpa [toMixedPoint] using
              continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
                (Fin.castAdd p (Fin.castAdd m j))
          have hwidth_cast :
              ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j ≤ P.stockWidth * y j := by
            exact_mod_cast feasible_width_bound hyz j
          have hrow_j :
              -(P.stockWidth : ℝ) * y j +
                  ∑ i : Fin m, (P.itemWidth i : ℝ) * z i j ≤ 0 := by
            have hsub :
                (∑ i : Fin m, (P.itemWidth i : ℝ) * z i j) - P.stockWidth * y j ≤ 0 :=
              sub_nonpos.mpr hwidth_cast
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
          simpa [Pi.add_apply, hcontinuous_row, rhs_apply_width, integerMatrix_mulVec_apply_width]
            using hrow_j
        · intro i
          have hcontinuous_row :
              (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
                  (Fin.castAdd p (Fin.natAdd p i)) = 0 := by
            simpa [toMixedPoint] using
              continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
                (Fin.castAdd p (Fin.natAdd p i))
          have hdemand_cast :
              (P.demand i : ℝ) ≤ ∑ j : Fin p, (z i j : ℝ) := by
            exact_mod_cast feasible_demand_cover hyz i
          have hrow_i :
              -∑ j : Fin p, (z i j : ℝ) ≤ -((P.demand i : ℕ) : ℝ) :=
            neg_le_neg hdemand_cast
          simpa [Pi.add_apply, hcontinuous_row, rhs_apply_demand, integerMatrix_mulVec_apply_demand]
            using hrow_i
      · intro j
        have hcontinuous_row :
            (P.toMixedIntegerLinearProgram.continuousMatrix *ᵥ (toMixedPoint y z).2)
                (Fin.natAdd (p + m) j) = 0 := by
          simpa [toMixedPoint] using
            continuousMatrix_mulVec_apply_eq_zero P (toMixedPoint y z).2
              (Fin.natAdd (p + m) j)
        have hy_le_one_real : (y j : ℝ) ≤ 1 := by
          rcases feasible_roll_binary hyz j with hy_zero | hy_one
          · simpa [hy_zero]
          · simpa [hy_one]
        simpa [Pi.add_apply, hcontinuous_row, rhs_apply_upper, integerMatrix_mulVec_apply_upper]
          using hy_le_one_real
    · intro k
      -- Every integer-block coordinate is a nonnegative cast from the source `ℕ` data.
      refine Fin.addCases ?_ ?_ k
      · intro j
        simpa [toMixedPoint] using
          (show (0 : ℝ) ≤ (y j : ℝ) by exact_mod_cast Nat.zero_le (y j))
      · intro l
        let ij := (cutIndexEquiv m p).symm l
        simpa [toMixedPoint, ij] using
          (show (0 : ℝ) ≤ (z ij.1 ij.2 : ℝ) by exact_mod_cast Nat.zero_le (z ij.1 ij.2))
    · intro k
      -- The continuous block is empty.
      exact Fin.elim0 k
    · intro k
      -- Every integer-block coordinate is an integer cast coming from `y` or `z`.
      refine Fin.addCases ?_ ?_ k
      · intro j
        refine ⟨Int.ofNat (y j), ?_⟩
        simp [toMixedPoint]
      · intro l
        let ij := (cutIndexEquiv m p).symm l
        refine ⟨Int.ofNat (z ij.1 ij.2), ?_⟩
        simp [toMixedPoint, ij]

/-- Helper for Definition 2.6: every feasible mixed point of the canonical MILP bridge comes from
a source feasible pair `(y, z)`. -/
private theorem exists_sourcePoint_of_mem_toMixedIntegerLinearProgram_feasibleSet
    {m p : ℕ}
    (P : RollIndexed m p)
    {xy : MixedRealPoint (p + m * p) 0}
    (hxy : xy ∈ P.toMixedIntegerLinearProgram.feasibleSet) :
    ∃ y : Fin p → ℕ, ∃ z : Matrix (Fin m) (Fin p) ℕ,
      xy = toMixedPoint y z ∧ (y, z) ∈ P.feasibleSet := by
  classical
  -- Recover the nonnegative integer coordinates of the mixed point as natural-valued source data.
  have hxy_feas := hxy
  rw [P.toMixedIntegerLinearProgram.mem_feasibleSet_iff] at hxy_feas
  rcases hxy_feas with ⟨_, hx_nonneg, _, hx_integral⟩
  let y : Fin p → ℕ := fun j ↦
    let hy_int : ∃ t : ℤ, xy.1 (Fin.castAdd (m * p) j) = (t : ℝ) :=
      hx_integral (Fin.castAdd (m * p) j)
    Int.toNat (Classical.choose hy_int : ℤ)
  let cutCount : Fin (m * p) → ℕ := fun l ↦
    let hz_int : ∃ t : ℤ, xy.1 (Fin.natAdd p l) = (t : ℝ) :=
      hx_integral (Fin.natAdd p l)
    Int.toNat (Classical.choose hz_int : ℤ)
  let z : Matrix (Fin m) (Fin p) ℕ := Matrix.of fun i j ↦ cutCount (cutIndex i j)
  have hxy_eq : xy = toMixedPoint y z := by
    -- Show that the recovered natural data reproduces the original mixed point coordinatewise.
    apply Prod.ext
    · funext k
      refine Fin.addCases ?_ ?_ k
      · intro j
        let hy_int : ∃ t : ℤ, xy.1 (Fin.castAdd (m * p) j) = (t : ℝ) :=
          hx_integral (Fin.castAdd (m * p) j)
        have hy_eq :
            xy.1 (Fin.castAdd (m * p) j) =
              ((Classical.choose hy_int : ℤ) : ℝ) :=
          Classical.choose_spec hy_int
        have hy_nonneg :
            0 ≤ (Classical.choose hy_int : ℤ) := by
          have hxj_nonneg : 0 ≤ xy.1 (Fin.castAdd (m * p) j) := hx_nonneg (Fin.castAdd (m * p) j)
          rw [hy_eq] at hxj_nonneg
          exact_mod_cast hxj_nonneg
        calc
          xy.1 (Fin.castAdd (m * p) j) =
              ((Classical.choose hy_int : ℤ) : ℝ) := hy_eq
          _ = (Int.toNat (Classical.choose hy_int : ℤ) : ℝ) := by
                symm
                exact_mod_cast Int.toNat_of_nonneg hy_nonneg
          _ = (toMixedPoint y z).1 (Fin.castAdd (m * p) j) := by
                simp [toMixedPoint, y, hy_int]
      · intro l
        let ij := (cutIndexEquiv m p).symm l
        have hcut : cutIndex ij.1 ij.2 = l := by
          simpa [ij, cutIndex] using (cutIndexEquiv m p).apply_symm_apply l
        let hz_int : ∃ t : ℤ, xy.1 (Fin.natAdd p l) = (t : ℝ) := hx_integral (Fin.natAdd p l)
        have hz_eq :
            xy.1 (Fin.natAdd p l) =
              ((Classical.choose hz_int : ℤ) : ℝ) :=
          Classical.choose_spec hz_int
        have hz_nonneg :
            0 ≤ (Classical.choose hz_int : ℤ) := by
          have hxl_nonneg : 0 ≤ xy.1 (Fin.natAdd p l) := hx_nonneg (Fin.natAdd p l)
          rw [hz_eq] at hxl_nonneg
          exact_mod_cast hxl_nonneg
        calc
          xy.1 (Fin.natAdd p l) =
              ((Classical.choose hz_int : ℤ) : ℝ) := hz_eq
          _ = (Int.toNat (Classical.choose hz_int : ℤ) : ℝ) := by
                symm
                exact_mod_cast Int.toNat_of_nonneg hz_nonneg
          _ = (cutCount l : ℝ) := by
                rfl
          _ = (z ij.1 ij.2 : ℝ) := by
                have hz_matrix : cutCount l = z ij.1 ij.2 := by
                  rw [← hcut]
                  simp [z]
                exact congrArg (fun n : ℕ ↦ (n : ℝ)) hz_matrix
          _ = (toMixedPoint y z).1 (Fin.natAdd p l) := by
                simp [toMixedPoint, ij]
    · funext i
      exact Fin.elim0 i
  refine ⟨y, z, hxy_eq, ?_⟩
  -- Reuse the previously proved bridge on the reconstructed source point.
  exact (mem_toMixedIntegerLinearProgram_feasibleSet_iff).mp (by simpa [hxy_eq] using hxy)

/-- The source objective agrees with the objective of the canonical Chapter 1 MILP bridge on the
mixed point determined by `(y, z)`. -/
theorem objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
    {m p : ℕ}
    (P : RollIndexed m p)
    (y : Fin p → ℕ)
    (z : Matrix (Fin m) (Fin p) ℕ) :
    (P.objectiveValue (y, z) : ℝ) =
      P.toMixedIntegerLinearProgram.objectiveValue (toMixedPoint y z) := by
  -- Expand both objectives and collapse the empty continuous block.
  have hcontinuous_zero :
      P.toMixedIntegerLinearProgram.continuousObjective ⬝ᵥ (toMixedPoint y z).2 = 0 :=
    continuousObjective_dot_eq_zero P (toMixedPoint y z).2
  rw [P.objectiveValue_def, P.toMixedIntegerLinearProgram.objectiveValue_def,
    integerObjective_dot_toMixedPoint, hcontinuous_zero]
  simp

/-- Membership in the source attained-value set is equivalent to membership of the cast value in
the attained-value set of the canonical Chapter 1 MILP bridge. -/
theorem mem_toMixedIntegerLinearProgram_objectiveValues_iff
    {m p : ℕ}
    (P : RollIndexed m p)
    {r : ℕ} :
    (r : ℝ) ∈ P.toMixedIntegerLinearProgram.objectiveValues ↔
      r ∈ P.objectiveValues := by
  constructor
  · intro hr
    -- Transport a MILP witness back to a source feasible pair.
    rcases (P.toMixedIntegerLinearProgram.mem_objectiveValues_iff (r : ℝ)).mp hr with
      ⟨xy, hxy, hobj⟩
    rcases exists_sourcePoint_of_mem_toMixedIntegerLinearProgram_feasibleSet P hxy with
      ⟨y, z, hxy_eq, hyz⟩
    refine (mem_objectiveValues_iff_exists_feasible).2 ?_
    refine ⟨y, z, hyz, ?_⟩
    have hobj_point :
        P.toMixedIntegerLinearProgram.objectiveValue (toMixedPoint y z) = (r : ℝ) := by
      simpa [hxy_eq] using hobj
    have hreal :
        ((P.objectiveValue (y, z) : ℕ) : ℝ) = (r : ℝ) := by
      exact (objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue P y z).trans hobj_point
    exact_mod_cast hreal
  · intro hr
    -- Send a source feasible witness into the canonical MILP bridge.
    rcases (mem_objectiveValues_iff_exists_feasible).mp hr with ⟨y, z, hyz, hobj⟩
    refine (P.toMixedIntegerLinearProgram.mem_objectiveValues_iff (r : ℝ)).2 ?_
    refine ⟨toMixedPoint y z, (mem_toMixedIntegerLinearProgram_feasibleSet_iff).2 hyz, ?_⟩
    simpa [hobj] using
      (objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue P y z).symm

/-- The objective values of the canonical Chapter 1 MILP bridge are exactly the real casts of the
source attained-value set. -/
theorem objectiveValues_natCast_eq_toMixedIntegerLinearProgram_objectiveValues
    {m p : ℕ}
    (P : RollIndexed m p) :
    ((fun r : ℕ ↦ (r : ℝ)) '' P.objectiveValues) =
      P.toMixedIntegerLinearProgram.objectiveValues := by
  -- Compare the two attained-value sets by transporting witnesses in both directions.
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_toMixedIntegerLinearProgram_objectiveValues_iff P).2 hr
  · intro hx
    rcases (P.toMixedIntegerLinearProgram.mem_objectiveValues_iff x).mp hx with ⟨xy, hxy, hobj⟩
    rcases exists_sourcePoint_of_mem_toMixedIntegerLinearProgram_feasibleSet P hxy with
      ⟨y, z, hxy_eq, hyz⟩
    refine ⟨P.objectiveValue (y, z), ?_, ?_⟩
    · exact (mem_objectiveValues_iff_exists_feasible).2 ⟨y, z, hyz, rfl⟩
    · calc
        ((P.objectiveValue (y, z) : ℕ) : ℝ) =
            P.toMixedIntegerLinearProgram.objectiveValue (toMixedPoint y z) :=
              objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue P y z
        _ = P.toMixedIntegerLinearProgram.objectiveValue xy := by
              simpa [hxy_eq]
        _ = x := hobj

end RollIndexed
end CuttingStock

end
