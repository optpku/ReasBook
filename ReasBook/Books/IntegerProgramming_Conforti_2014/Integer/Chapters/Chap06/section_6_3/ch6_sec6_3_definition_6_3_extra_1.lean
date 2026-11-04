/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.NNReal.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

section Definition63Extra1

-- Semantic recall note: no deferred semantic search tool such as `lean_leansearch` was available
-- in this environment, so the infinite relaxation is encoded directly using finitely supported
-- functions on `Fin q → ℝ`.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "NatAssignment" => Rq →₀ ℕ
local notation "IntAssignment" => Rq →₀ ℤ
local notation "ContAssignment" => Rq →₀ NNReal
local notation "RealAssignment" => Rq →₀ ℝ
local notation "Zq" => Fin q → ℤ

open scoped IntegerVectorNotation

/-- The canonical bridge from finitely supported natural assignments to integer assignments on
`ℝ^q`. -/
noncomputable abbrev nat_assignment_to_int_assignment (x : NatAssignment) : IntAssignment :=
  Finsupp.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp) x

@[simp] theorem nat_assignment_to_int_assignment_apply
    (x : NatAssignment) (r : Rq) :
    nat_assignment_to_int_assignment x r = (x r : ℤ) := by
  simp [nat_assignment_to_int_assignment]

/-- The canonical bridge from nonnegative integer assignments to natural assignments on `ℝ^q`. -/
noncomputable abbrev int_assignment_to_nat_assignment (x : IntAssignment) : NatAssignment :=
  Finsupp.mapRange Int.toNat (by simp) x

@[simp] theorem int_assignment_to_nat_assignment_apply
    (x : IntAssignment) (r : Rq) :
    int_assignment_to_nat_assignment x r = Int.toNat (x r) := by
  simp [int_assignment_to_nat_assignment]

@[simp] theorem nat_assignment_to_int_assignment_int_assignment_to_nat_assignment
    {x : IntAssignment} (hx : ∀ r, 0 ≤ x r) :
    nat_assignment_to_int_assignment (int_assignment_to_nat_assignment x) = x := by
  ext r
  simp [int_assignment_to_nat_assignment, nat_assignment_to_int_assignment, hx r]

/-- Helper for Definition 6.3-extra-1: the Gomory--Johnson mixed-integer infinite relaxation `M_f`
consists of the finitely supported nonnegative integer and continuous coefficient families whose
weighted sum with `f` lies in the embedded lattice `ℤ^q ⊆ ℝ^q`. -/
def mixed_integer_relaxation_set (f : Rq) : Set (NatAssignment × ContAssignment) :=
  { xy |
    f + xy.1.sum (fun r n ↦ (n : ℝ) • r) + xy.2.sum (fun r a ↦ (a : ℝ) • r) ∈ ℤ^q }

/-- Membership in `mixed_integer_relaxation_set f` is exactly the balance equation of the
mixed-integer infinite relaxation `M_f`. -/
theorem mem_mixed_integer_relaxation_set_iff
    (f : Rq) (x : NatAssignment) (y : ContAssignment) :
    (x, y) ∈ mixed_integer_relaxation_set f ↔
      ∃ z : Zq,
        f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r) =
          fun i ↦ (z i : ℝ) := by
  -- Unfold the owner once and reuse the chapter-level lattice characterization.
  simpa [mixed_integer_relaxation_set] using
    (mem_integerVectors_iff
      (x := f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r)))

/-- The mixed-integer infinite relaxation `M_f` is nonempty. -/
theorem mixed_integer_relaxation_set_nonempty (f : Rq) :
    (mixed_integer_relaxation_set f).Nonempty := by
  refine ⟨(Finsupp.single (-f) 1, 0), ?_⟩
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨0, ?_⟩
  -- The singleton coefficient at `-f` cancels the shift `f`.
  funext i
  simp

/-- The ambient signed balance relation associated to `M_f`; it forgets nonnegativity and widens
the coefficient types to `ℤ` and `ℝ`. -/
def gomory_johnson_relaxation (f : Rq) : Set (IntAssignment × RealAssignment) :=
  { xy |
    f + xy.1.sum (fun r z ↦ (z : ℝ) • r) + xy.2.sum (fun r a ↦ a • r) ∈ ℤ^q }

/-- Membership in `gomory_johnson_relaxation` is exactly the lattice-valued balance equation in the
ambient signed bridge. -/
theorem mem_gomory_johnson_relaxation_iff
    {f : Rq} {x : IntAssignment} {y : RealAssignment} :
    (x, y) ∈ gomory_johnson_relaxation f ↔
      f + x.sum (fun r z ↦ (z : ℝ) • r) + y.sum (fun r a ↦ a • r) ∈ ℤ^q :=
  Iff.rfl

/-- Every feasible point of the mixed-integer relaxation yields a feasible point of the ambient
signed bridge. -/
theorem mem_gomory_johnson_relaxation_of_mem_mixed_integer_relaxation_set
    {f : Rq} {x : NatAssignment} {y : ContAssignment}
    (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
    (nat_assignment_to_int_assignment x, nnreal_assignment_to_real_assignment y) ∈
      gomory_johnson_relaxation f := by
  have hxsum :
      (nat_assignment_to_int_assignment x).sum (fun r z ↦ (z : ℝ) • r) =
        x.sum (fun r n ↦ (n : ℝ) • r) := by
    -- Normalize the natural assignment by summing after the canonical cast to integers.
    simpa [nat_assignment_to_int_assignment] using
      (Finsupp.sum_mapRange_index
        (f := fun n : ℕ ↦ (n : ℤ))
        (g := x)
        (h := fun r (z : ℤ) ↦ (z : ℝ) • r)
        (h0 := fun r ↦ by simp))
  have hysum :
      (nnreal_assignment_to_real_assignment y).sum (fun r a ↦ a • r) =
        y.sum (fun r a ↦ (a : ℝ) • r) := by
    -- The continuous assignment uses the same weighted sum after widening `NNReal` to `ℝ`.
    simpa [nnreal_assignment_to_real_assignment] using
      (Finsupp.sum_mapRange_index
        (g := y)
        (h := fun r a ↦ a • r)
        (h0 := fun r ↦ by simp))
  -- After both coefficient families are widened, the balance equation is unchanged.
  simpa [gomory_johnson_relaxation, mixed_integer_relaxation_set, hxsum, hysum] using hxy

/-- The ambient signed bridge is nonempty because `M_f` is nonempty. -/
theorem gomory_johnson_relaxation_nonempty (f : Rq) :
    (gomory_johnson_relaxation f).Nonempty := by
  rcases mixed_integer_relaxation_set_nonempty f with ⟨⟨x, y⟩, hxy⟩
  exact ⟨(nat_assignment_to_int_assignment x, nnreal_assignment_to_real_assignment y),
    mem_gomory_johnson_relaxation_of_mem_mixed_integer_relaxation_set hxy⟩

namespace pure_integer_feasible_point

/-- A feasible point of the pure-integer relaxation yields a mixed-integer feasible point by using
zero continuous part and converting its nonnegative integer coefficients to naturals. -/
theorem toMixedIntegerRelaxation
    {f : Rq} {x : IntAssignment} (hx : pure_integer_feasible_point f x) :
    (int_assignment_to_nat_assignment x, 0) ∈ mixed_integer_relaxation_set f := by
  have hsum :
      (int_assignment_to_nat_assignment x).sum (fun r n ↦ (n : ℝ) • r) =
        x.sum (fun r z ↦ (z : ℝ) • r) := by
    have hsumMap :
        (nat_assignment_to_int_assignment (int_assignment_to_nat_assignment x)).sum
            (fun r z ↦ (z : ℝ) • r) =
          (int_assignment_to_nat_assignment x).sum (fun r n ↦ (n : ℝ) • r) := by
      simpa [nat_assignment_to_int_assignment] using
        (Finsupp.sum_mapRange_index
          (f := fun n : ℕ ↦ (n : ℤ))
          (hf := by simp)
          (g := int_assignment_to_nat_assignment x)
          (h := fun r (z : ℤ) ↦ (z : ℝ) • r)
          (h0 := fun r ↦ by simp))
    -- Convert the naturalized coefficients back to the original integer assignment.
    calc
      (int_assignment_to_nat_assignment x).sum (fun r n ↦ (n : ℝ) • r) =
          (nat_assignment_to_int_assignment (int_assignment_to_nat_assignment x)).sum
            (fun r z ↦ (z : ℝ) • r) := by
            exact hsumMap.symm
      _ = x.sum (fun r z ↦ (z : ℝ) • r) := by
            rw [nat_assignment_to_int_assignment_int_assignment_to_nat_assignment hx.nonneg]
  -- The mixed balance is the pure-integer balance with a zero continuous part.
  simpa [mixed_integer_relaxation_set, pure_integer_balance, hsum] using
    hx.balance_mem_integerVectors

end pure_integer_feasible_point

namespace IsContinuousInfiniteRelaxationFeasible

/-- A feasible point of the continuous relaxation yields a mixed-integer feasible point by using
zero integer part. -/
theorem toMixedIntegerRelaxation
    {f : Rq} {y : ContAssignment} (hy : IsContinuousInfiniteRelaxationFeasible f y) :
    ((0 : NatAssignment), y) ∈ mixed_integer_relaxation_set f := by
  -- This is exactly the continuous balance equation with zero integer part.
  simpa [mixed_integer_relaxation_set, continuous_infinite_balance] using
    hy.balance_mem_integerVectors

end IsContinuousInfiniteRelaxationFeasible

/-- Helper for Definition 6.3-extra-1: a pair of coefficient functions `(π, ψ)` is
valid for `M_f` when `π` is pointwise nonnegative and the corresponding cut
inequality is satisfied by every feasible pair in the infinite relaxation. -/
class IsValidGomoryJohnsonPair (f : Rq) (π ψ : Rq → ℝ) : Prop where
  nonneg : ∀ r, 0 ≤ π r
  one_le {x : NatAssignment} {y : ContAssignment}
      (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
      1 ≤ x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ))

namespace IsValidGomoryJohnsonPair

/-- A valid Gomory--Johnson pair satisfies the mixed-integer inequality in the direct balance
form used later for liftings. -/
theorem one_le_mixed_integer
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    {x : NatAssignment} {y : ContAssignment}
    (hxy :
      f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r) ∈ ℤ^q) :
    1 ≤ x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ)) :=
  hπψ.one_le hxy

/-- A valid Gomory--Johnson pair restricts to a valid function on the pure-integer relaxation. -/
theorem toPureIntegerValidFunction
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ) :
    pure_integer_valid_function f π := by
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Pointwise nonnegativity is inherited directly from the mixed valid pair.
    intro r
    exact hπψ.nonneg r
  · intro x hx
    have hx' : pure_integer_feasible_point f x := hx
    have hsum :
        (int_assignment_to_nat_assignment x).sum (fun r n ↦ π r * (n : ℝ)) =
          x.sum (fun r z ↦ π r * (z : ℝ)) := by
      have hsumMap :
          (nat_assignment_to_int_assignment (int_assignment_to_nat_assignment x)).sum
              (fun r z ↦ π r * (z : ℝ)) =
            (int_assignment_to_nat_assignment x).sum (fun r n ↦ π r * (n : ℝ)) := by
        simpa [nat_assignment_to_int_assignment] using
          (Finsupp.sum_mapRange_index
            (f := fun n : ℕ ↦ (n : ℤ))
            (hf := by simp)
            (g := int_assignment_to_nat_assignment x)
            (h := fun r (z : ℤ) ↦ π r * (z : ℝ))
            (h0 := fun r ↦ by simp))
      -- Rewrite the mixed cut sum back to the original integer coefficients.
      calc
        (int_assignment_to_nat_assignment x).sum (fun r n ↦ π r * (n : ℝ)) =
            (nat_assignment_to_int_assignment (int_assignment_to_nat_assignment x)).sum
              (fun r z ↦ π r * (z : ℝ)) := by
              exact hsumMap.symm
        _ = x.sum (fun r z ↦ π r * (z : ℝ)) := by
              rw [nat_assignment_to_int_assignment_int_assignment_to_nat_assignment hx'.nonneg]
    -- Apply mixed validity to the transported feasible point and simplify the zero continuous part.
    simpa [hsum, mul_comm] using
      hπψ.one_le (pure_integer_feasible_point.toMixedIntegerRelaxation hx')

/-- A valid Gomory--Johnson pair restricts to a valid function on the continuous relaxation. -/
theorem toContinuousValidFunction
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ) :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ := by
  refine { one_le := ?_ }
  intro y hy
  -- Apply mixed validity to the continuous feasible point with zero integer part.
  simpa using hπψ.one_le (IsContinuousInfiniteRelaxationFeasible.toMixedIntegerRelaxation hy)

end IsValidGomoryJohnsonPair
/-- Definition 6.3-extra-1 (3). A valid pair `(π, ψ)` is minimal when every valid pair lying
pointwise below it coincides with `(π, ψ)`. -/
class IsMinimalValidGomoryJohnsonPair (f : Rq) (π ψ : Rq → ℝ) :
    Prop extends IsValidGomoryJohnsonPair f π ψ where
  eq_of_le {π' ψ' : Rq → ℝ}
      (hπ'ψ' : IsValidGomoryJohnsonPair f π' ψ')
      (hπle : ∀ r, π' r ≤ π r)
      (hψle : ∀ r, ψ' r ≤ ψ r) :
      π' = π ∧ ψ' = ψ

instance instIsValidGomoryJohnsonPair
    {f : Rq} {π ψ : Rq → ℝ} [hπψ : IsMinimalValidGomoryJohnsonPair f π ψ] :
    IsValidGomoryJohnsonPair f π ψ :=
  hπψ.toIsValidGomoryJohnsonPair

end Definition63Extra1
