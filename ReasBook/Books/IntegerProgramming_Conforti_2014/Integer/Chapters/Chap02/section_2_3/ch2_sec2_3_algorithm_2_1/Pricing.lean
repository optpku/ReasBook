/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

open scoped BigOperators

public section

namespace CuttingStockColumnGeneration

variable {m : ℕ}

/-- The pricing objective at a dual vector `u` is `∑ i, u_i s_i`. -/
def pricing_objective
    (u : Fin m → ℝ) (s : Fin m → ℕ) : ℝ :=
  ∑ i, u i * (s i : ℝ)

/-- The pricing objective values attained on the full pattern family `S`. -/
def pricing_objective_values
    (S : Finset (Fin m → ℕ)) (u : Fin m → ℝ) : Set ℝ :=
  pricing_objective u '' (S : Set (Fin m → ℕ))

/-- Membership in `pricing_objective_values S u` means that the pricing objective is attained by
some pattern in `S`. -/
@[simp] theorem mem_pricing_objective_values_iff
    {S : Finset (Fin m → ℕ)} {u : Fin m → ℝ} {r : ℝ} :
    r ∈ pricing_objective_values S u ↔
      ∃ s : Fin m → ℕ, s ∈ S ∧ pricing_objective u s = r :=
  Iff.rfl

end CuttingStockColumnGeneration
