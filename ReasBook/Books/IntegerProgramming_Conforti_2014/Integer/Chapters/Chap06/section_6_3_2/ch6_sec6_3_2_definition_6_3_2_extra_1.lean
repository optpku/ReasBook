/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.NNReal.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

section Definition632Extra1

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch` in this environment, so this file follows the local Chapter 6 convention of
-- representing `ℝ^q` by `Fin q → ℝ` and finitely supported coefficient families by `Finsupp`.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "RealAssignment" => Rq →₀ ℝ
local notation "ContAssignment" => Rq →₀ NNReal

open scoped IntegerVectorNotation

/-- The canonical bridge from finitely supported `NNReal` assignments to real assignments on
`ℝ^q`. This keeps the source-facing continuous relaxation on nonnegative coefficients while
allowing comparison with raw-real balance expressions. -/
noncomputable abbrev nnreal_assignment_to_real_assignment (y : ContAssignment) : RealAssignment :=
  Finsupp.mapRange (fun a : NNReal ↦ (a : ℝ)) (by simp) y

@[simp] theorem nnreal_assignment_to_real_assignment_apply
    (y : ContAssignment) (r : Rq) :
    nnreal_assignment_to_real_assignment y r = y r := by
  simp [nnreal_assignment_to_real_assignment]

/-- The shifted weighted vector sum associated to a finitely supported nonnegative family. -/
def continuous_infinite_balance (f : Rq) (y : ContAssignment) : Rq :=
  f + y.sum (fun r a ↦ (a : ℝ) • r)

/-- `continuous_infinite_balance f y` is the coordinatewise sum
`f_i + ∑_r y_r r_i`. -/
@[simp] theorem continuous_infinite_balance_apply
    (f : Rq) (y : ContAssignment) (i : Fin q) :
    continuous_infinite_balance f y i = f i + y.sum (fun r a ↦ a * r i) := by
  rw [continuous_infinite_balance, Pi.add_apply, Finsupp.sum_apply']
  simp [Pi.smul_apply, smul_eq_mul]

/-- A finitely supported nonnegative coefficient family is feasible for the continuous infinite
relaxation when its weighted sum with `f` lands in the embedded lattice `ℤ^q ⊆ ℝ^q`. -/
class IsContinuousInfiniteRelaxationFeasible (f : Rq) (y : ContAssignment) : Prop where
  /-- The weighted balance equation for a feasible assignment lands in the embedded lattice. -/
  lattice_balance : continuous_infinite_balance f y ∈ ℤ^q

namespace IsContinuousInfiniteRelaxationFeasible

/-- A feasible point has lattice-valued shifted balance in the canonical vector form. -/
theorem balance_mem_integerVectors {f : Rq} {y : ContAssignment}
    (hy : IsContinuousInfiniteRelaxationFeasible f y) :
    continuous_infinite_balance f y ∈ ℤ^q :=
  hy.lattice_balance

end IsContinuousInfiniteRelaxationFeasible

/-- Definition 6.3.2-extra-1 (1). The feasible set `R_f` of the continuous infinite relaxation
consists of the finitely supported nonnegative coefficient families `y` on `ℝ^q`, encoded as
`NNReal` assignments, such that `f + ∑ r, r * y_r` belongs to the embedded lattice
`ℤ^q ⊆ ℝ^q`. -/
def continuous_infinite_relaxation_feasible_set (f : Rq) : Set ContAssignment :=
  IsContinuousInfiniteRelaxationFeasible f

/-- Membership in `continuous_infinite_relaxation_feasible_set f` is exactly the lattice-balance
condition, since nonnegativity is carried by the `NNReal` assignment type. -/
theorem mem_continuous_infinite_relaxation_feasible_set_iff
    {f : Rq} {y : ContAssignment} :
    y ∈ continuous_infinite_relaxation_feasible_set f ↔
      continuous_infinite_balance f y ∈ ℤ^q := by
  constructor
  · intro hy
    exact hy.lattice_balance
  · intro hlattice
    exact ⟨hlattice⟩

/-- Definition 6.3.2-extra-1 (2). A function `ψ : ℝ^q → ℝ` is valid for `R_f` when the inequality
`∑ r, ψ(r) y_r ≥ 1` holds for every feasible point `y ∈ R_f`. -/
class IsValidFunctionForContinuousInfiniteRelaxation
    (f : Rq) (ψ : Rq → ℝ) : Prop where
  /-- Every feasible point of `R_f` satisfies the cut inequality defined by `ψ`. -/
  one_le {y : ContAssignment} (hy : IsContinuousInfiniteRelaxationFeasible f y) :
    1 ≤ y.sum (fun r a ↦ ψ r * a)

/-- A valid function satisfies the defining inequality on every feasible point of `R_f`. -/
theorem continuous_infinite_valid_function_one_le {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    {y : ContAssignment} (hy : y ∈ continuous_infinite_relaxation_feasible_set f) :
    1 ≤ y.sum (fun r a ↦ ψ r * a) :=
  hψ.one_le hy

/-- Definition 6.3.2-extra-1 (3). A valid function `ψ` for `R_f` is minimal when every valid
function for `R_f` that is pointwise below `ψ` is equal to `ψ`. -/
class IsMinimalValidFunctionForContinuousInfiniteRelaxation
    (f : outParam Rq) (ψ : Rq → ℝ) : Prop
    extends IsValidFunctionForContinuousInfiniteRelaxation f ψ where
  /-- Any valid function for `R_f` lying pointwise below `ψ` coincides with `ψ`. -/
  eq_of_le {ψ' : Rq → ℝ}
      (hψ' : IsValidFunctionForContinuousInfiniteRelaxation f ψ')
      (hle : ∀ r : Rq, ψ' r ≤ ψ r) :
      ψ' = ψ

/-- A minimal valid function for `R_f` is, in particular, a valid function for `R_f`. -/
instance instIsMinimalValidFunctionForContinuousInfiniteRelaxationToIsValidFunction
    {f : Rq} {ψ : Rq → ℝ}
    [hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ] :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ :=
  hψ.toIsValidFunctionForContinuousInfiniteRelaxation

/-- A minimal valid function is determined among valid functions by pointwise domination. -/
theorem continuous_infinite_minimal_valid_function_eq_of_le {f : Rq}
    {ψ ψ' : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ)
    (hψ' : IsValidFunctionForContinuousInfiniteRelaxation f ψ')
    (hle : ∀ r : Rq, ψ' r ≤ ψ r) :
    ψ' = ψ :=
  hψ.eq_of_le hψ' hle

end Definition632Extra1
