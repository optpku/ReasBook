module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.EReal.Basic

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- The consensus KKT conditions expressed by feasibility and the two
supporting-hyperplane inequalities with their signed multiplier terms. -/
def IsKKT {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E → EReal) (x y dual : E) : Prop :=
  x = y ∧
    (∀ z, f x + ((inner ℝ (-dual) (z - x) : ℝ) : EReal) ≤ f z) ∧
    ∀ z, g y + ((inner ℝ dual (z - y) : ℝ) : EReal) ≤ g z

/-- The consensus KKT predicate exposes feasibility and both signed support inequalities. -/
theorem kkt_iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → EReal} {x y dual : E} :
    IsKKT f g x y dual ↔
      x = y ∧
        (∀ z, f x + ((inner ℝ (-dual) (z - x) : ℝ) : EReal) ≤ f z) ∧
        ∀ z, g y + ((inner ℝ dual (z - y) : ℝ) : EReal) ≤ g z := by
  -- Unfolding `IsKKT` exposes exactly the stated feasibility and support conditions.
  rfl

/-- A point minimizes the consensus primal objective `z ↦ f z + g z`. -/
def IsPrimalMinimizer {E : Type u} (f g : E → EReal) (z : E) : Prop :=
  ∀ w, f z + g z ≤ f w + g w

/-- Primal minimality is the universal objective-value inequality. -/
theorem primalMinimizer_iff {E : Type u} {f g : E → EReal} {z : E} :
    IsPrimalMinimizer f g z ↔ ∀ w, f z + g z ≤ f w + g w := by
  -- Unfolding `IsPrimalMinimizer` yields the same universal inequality.
  rfl

end ConsensusADMM
