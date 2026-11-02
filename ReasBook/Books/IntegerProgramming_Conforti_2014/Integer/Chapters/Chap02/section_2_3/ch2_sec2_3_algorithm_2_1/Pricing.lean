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
