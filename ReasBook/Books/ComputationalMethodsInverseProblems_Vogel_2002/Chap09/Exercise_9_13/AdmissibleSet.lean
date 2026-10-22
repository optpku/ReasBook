/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

namespace PoissonInverse

/-- The admissible set for the Chapter 9 Poisson inverse objective consists of
nonnegative feasible vectors whose forward data under `K` are strictly
positive. -/
def admissibleSet
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {f : EuclideanSpace ℝ (Fin n) |
    f ∈ NonnegativeOrthant.feasibleSet n ∧
      ∀ i : Fin m, 0 < Matrix.mulVec K f i}

/-- Membership in `PoissonInverse.admissibleSet` is exactly the conjunction of
nonnegative feasibility and strictly positive forward data. -/
@[simp] theorem mem_admissibleSet_iff
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    f ∈ admissibleSet K ↔
      f ∈ NonnegativeOrthant.feasibleSet n ∧
        ∀ i : Fin m, 0 < Matrix.mulVec K f i := by
  -- Unpack the set membership into the defining conjunction.
  rfl

/-- A feasible point with strictly positive forward data belongs to
`PoissonInverse.admissibleSet`. -/
theorem mem_admissibleSet_of_feasible_of_forwardPos
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hf_feasible : f ∈ NonnegativeOrthant.feasibleSet n)
    (hf_pos : ∀ i : Fin m, 0 < Matrix.mulVec K f i) :
    f ∈ admissibleSet K := by
  -- Build admissibility from its two defining components.
  rw [mem_admissibleSet_iff]
  exact ⟨hf_feasible, hf_pos⟩

/-- Any point in `PoissonInverse.admissibleSet` is feasible for the Chapter 9
nonnegative-orthant constraint. -/
theorem feasible_of_mem_admissibleSet
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ admissibleSet K) :
    f ∈ NonnegativeOrthant.feasibleSet n := by
  -- Project the feasibility component from admissibility.
  exact (mem_admissibleSet_iff K f).mp hf |>.1

/-- Any point in `PoissonInverse.admissibleSet` has strictly positive forward
data under `K`. -/
theorem forwardPos_of_mem_admissibleSet
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ admissibleSet K) :
    ∀ i : Fin m, 0 < Matrix.mulVec K f i := by
  -- Project the forward-positivity component from admissibility.
  exact (mem_admissibleSet_iff K f).mp hf |>.2

end PoissonInverse
