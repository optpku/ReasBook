/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

open scoped BigOperators

namespace VariationalRegularization

section TotalVariation

/-- Definition 1.3-extra-1 (2). The discrete one-dimensional total-variation
penalty is the sum of absolute adjacent differences of a finite real signal. -/
def discreteTotalVariation {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin (n - 1),
    let left : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩
    let hn : 1 ≤ n :=
      Nat.succ_le_of_lt (Nat.zero_lt_of_lt (lt_of_lt_of_le i.2 (Nat.sub_le n 1)))
    let right : Fin n := ⟨i.1 + 1,
      lt_of_lt_of_le (Nat.succ_lt_succ i.2) (le_of_eq (Nat.sub_add_cancel hn))⟩
    |f right - f left|

/-- The defining adjacent-difference formula for `discreteTotalVariation`. -/
theorem discreteTotalVariation_def {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) :
    discreteTotalVariation f =
      ∑ i : Fin (n - 1),
        let left : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩
        let hn : 1 ≤ n :=
          Nat.succ_le_of_lt (Nat.zero_lt_of_lt (lt_of_lt_of_le i.2 (Nat.sub_le n 1)))
        let right : Fin n := ⟨i.1 + 1,
          lt_of_lt_of_le (Nat.succ_lt_succ i.2) (le_of_eq (Nat.sub_add_cancel hn))⟩
        |f right - f left| := by
  -- This rewrite theorem repeats the defining adjacent-difference sum verbatim.
  rfl

end TotalVariation

end VariationalRegularization
