module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Set.Image

public section

open scoped BigOperators

namespace CuttingStock

/-- A roll-indexed cutting stock instance with stock width, item widths, item demands, and the
standard positivity and width-bound assumptions. -/
structure RollIndexed (m p : ℕ) where
  stockWidth : ℕ
  itemWidth : Fin m → ℕ
  demand : Fin m → ℕ
  stockWidth_pos : 0 < stockWidth
  itemWidth_pos : ∀ i, 0 < itemWidth i
  itemWidth_le_stockWidth : ∀ i, itemWidth i ≤ stockWidth

namespace RollIndexed

/-- Construct a roll-indexed cutting stock instance from its stock width, item widths, item
demands, and the standard positivity and width-bound assumptions. -/
def ofData
    {m p : ℕ}
    (stockWidth : ℕ)
    (itemWidth : Fin m → ℕ)
    (demand : Fin m → ℕ)
    (h_stockWidth_pos : 0 < stockWidth)
    (h_itemWidth_pos : ∀ i, 0 < itemWidth i)
    (h_itemWidth_le_stockWidth : ∀ i, itemWidth i ≤ stockWidth) :
    RollIndexed m p :=
  { stockWidth := stockWidth
    itemWidth := itemWidth
    demand := demand
    stockWidth_pos := h_stockWidth_pos
    itemWidth_pos := h_itemWidth_pos
    itemWidth_le_stockWidth := h_itemWidth_le_stockWidth }

/-- The feasible roll-use vectors and cut-count matrices `(y, z)` of `P`: every roll width
constraint, every demand-cover constraint, and the binary roll-use conditions must hold, while the
nonnegativity of `y` and `z` is intrinsic from `ℕ`. -/
def feasibleSet
    {m p : ℕ}
    (P : RollIndexed m p) :
    Set ((Fin p → ℕ) × Matrix (Fin m) (Fin p) ℕ) :=
  { yz |
      (∀ j : Fin p, ∑ i : Fin m, P.itemWidth i * yz.2 i j ≤ P.stockWidth * yz.1 j) ∧
      (∀ i : Fin m, P.demand i ≤ ∑ j : Fin p, yz.2 i j) ∧
      ∀ j : Fin p, yz.1 j = 0 ∨ yz.1 j = 1 }

/-- Membership in `P.feasibleSet` is exactly the conjunction of the displayed roll-width,
demand-cover, and binary roll-use constraints. -/
theorem mem_feasibleSet_iff
    {m p : ℕ}
    {P : RollIndexed m p}
    {yz : (Fin p → ℕ) × Matrix (Fin m) (Fin p) ℕ} :
    yz ∈ P.feasibleSet ↔
      (∀ j : Fin p, ∑ i : Fin m, P.itemWidth i * yz.2 i j ≤ P.stockWidth * yz.1 j) ∧
      (∀ i : Fin m, P.demand i ≤ ∑ j : Fin p, yz.2 i j) ∧
      ∀ j : Fin p, yz.1 j = 0 ∨ yz.1 j = 1 := by
  -- Unfold the owner definition to expose the displayed conjunction of constraints.
  rfl

/-- A feasible roll-indexed solution satisfies the width inequality
`∑ i, P.itemWidth i * z i j ≤ P.stockWidth * y j` for every roll `j`. -/
theorem feasible_width_bound
    {m p : ℕ}
    {P : RollIndexed m p}
    {y : Fin p → ℕ}
    {z : Matrix (Fin m) (Fin p) ℕ}
    (hyz : (y, z) ∈ P.feasibleSet)
    (j : Fin p) :
    ∑ i : Fin m, P.itemWidth i * z i j ≤ P.stockWidth * y j := by
  -- Project the width inequalities from the feasible-set characterization.
  exact (mem_feasibleSet_iff.mp hyz).1 j

/-- A feasible roll-indexed solution covers every item demand:
`P.demand i ≤ ∑ j, z i j`. -/
theorem feasible_demand_cover
    {m p : ℕ}
    {P : RollIndexed m p}
    {y : Fin p → ℕ}
    {z : Matrix (Fin m) (Fin p) ℕ}
    (hyz : (y, z) ∈ P.feasibleSet)
    (i : Fin m) :
    P.demand i ≤ ∑ j : Fin p, z i j := by
  -- Project the demand-cover inequalities from feasible membership.
  exact (mem_feasibleSet_iff.mp hyz).2.1 i

/-- Every roll-use variable of a feasible roll-indexed solution is binary. -/
theorem feasible_roll_binary
    {m p : ℕ}
    {P : RollIndexed m p}
    {y : Fin p → ℕ}
    {z : Matrix (Fin m) (Fin p) ℕ}
    (hyz : (y, z) ∈ P.feasibleSet)
    (j : Fin p) :
    y j = 0 ∨ y j = 1 := by
  -- Project the binary roll-use condition from feasible membership.
  exact (mem_feasibleSet_iff.mp hyz).2.2 j

/-- The roll-indexed cutting stock objective value of `(y, z)` is the displayed sum
`∑ j, y j` of used rolls. -/
def objectiveValue
    {m p : ℕ}
    (P : RollIndexed m p) :
    ((Fin p → ℕ) × Matrix (Fin m) (Fin p) ℕ) → ℕ :=
  fun yz ↦
    let _ := P
    ∑ j : Fin p, yz.1 j

/-- Unfolding equation for `P.objectiveValue`. -/
theorem objectiveValue_def
    {m p : ℕ}
    (P : RollIndexed m p)
    (yz : (Fin p → ℕ) × Matrix (Fin m) (Fin p) ℕ) :
    P.objectiveValue yz = ∑ j : Fin p, yz.1 j := by
  -- Unfold the source objective to the displayed sum of roll-use variables.
  rfl

/-- The objective values attained by feasible roll-indexed solutions of `P`. -/
def objectiveValues
    {m p : ℕ}
    (P : RollIndexed m p) :
    Set ℕ :=
  P.objectiveValue '' P.feasibleSet

/-- Foundation-level witness form for membership in `P.objectiveValues`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m p : ℕ}
    {P : RollIndexed m p}
    {r : ℕ} :
    r ∈ P.objectiveValues ↔
      ∃ y : Fin p → ℕ, ∃ z : Matrix (Fin m) (Fin p) ℕ,
        (y, z) ∈ P.feasibleSet ∧ P.objectiveValue (y, z) = r := by
  -- Unpack image membership into an explicit feasible witness and its attained value.
  constructor
  · rintro ⟨⟨y, z⟩, hyz, hobj⟩
    exact ⟨y, z, hyz, hobj⟩
  · rintro ⟨y, z, hyz, hobj⟩
    exact ⟨(y, z), hyz, hobj⟩

end RollIndexed
end CuttingStock

end
