module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs

open scoped BigOperators

public section

namespace LotSizing

variable {n : ℕ}

/-- The lot-sizing feasibility constraints consist of the initial inventory equation, the period
balance equations, production activation bounds, nonnegative end-of-period inventories, and binary
setup variables. -/
def feasible
    (d M : Fin n → ℝ) (s0 : ℝ)
    (q : Fin n → ℝ) (stock : Fin (n + 1) → ℝ) (y : Fin n → ℝ) : Prop :=
  stock 0 = s0 ∧
    (∀ t : Fin n, stock t.succ = stock (Fin.castSucc t) + q t - d t) ∧
    (∀ t : Fin n, 0 ≤ q t ∧ q t ≤ M t * y t) ∧
    (∀ t : Fin n, 0 ≤ stock t.succ) ∧
    ∀ t : Fin n, y t = 0 ∨ y t = 1

/-- Membership in `feasible d M s0 q stock y` is exactly the conjunction of the lot-sizing
initial inventory, balance, production bound, nonnegative inventory, and binary setup
constraints. -/
theorem feasible_iff
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ} :
    feasible d M s0 q stock y ↔
      stock 0 = s0 ∧
        (∀ t : Fin n, stock t.succ = stock (Fin.castSucc t) + q t - d t) ∧
        (∀ t : Fin n, 0 ≤ q t ∧ q t ≤ M t * y t) ∧
        (∀ t : Fin n, 0 ≤ stock t.succ) ∧
        ∀ t : Fin n, y t = 0 ∨ y t = 1 := by
  -- The feasibility predicate is defined by exactly this conjunction of constraints.
  rfl

/-- The initial inventory equation extracted from `feasible d M s0 q stock y`. -/
theorem feasible_initial
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ}
    (h_feasible : feasible d M s0 q stock y) :
    stock 0 = s0 := by
  -- Unpack feasibility and read off the initial inventory condition.
  rcases h_feasible with ⟨h_initial, _, _, _, _⟩
  exact h_initial

/-- The one-period balance equation extracted from `feasible d M s0 q stock y`. -/
theorem feasible_balance
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ}
    (h_feasible : feasible d M s0 q stock y) (t : Fin n) :
    stock t.succ = stock (Fin.castSucc t) + q t - d t := by
  -- Unpack feasibility and evaluate the balance family at the chosen period.
  rcases h_feasible with ⟨_, h_balance, _, _, _⟩
  exact h_balance t

/-- The production lower and upper bounds extracted from `feasible d M s0 q stock y`. -/
theorem feasible_production_bounds
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ}
    (h_feasible : feasible d M s0 q stock y) (t : Fin n) :
    0 ≤ q t ∧ q t ≤ M t * y t := by
  -- Unpack feasibility and evaluate the production-bound family at the chosen period.
  rcases h_feasible with ⟨_, _, h_bounds, _, _⟩
  exact h_bounds t

/-- The nonnegative end-of-period inventory condition extracted from
`feasible d M s0 q stock y`. -/
theorem feasible_inventory_nonneg
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ}
    (h_feasible : feasible d M s0 q stock y) (t : Fin n) :
    0 ≤ stock t.succ := by
  -- Unpack feasibility and evaluate the inventory nonnegativity family at the chosen period.
  rcases h_feasible with ⟨_, _, _, h_nonneg, _⟩
  exact h_nonneg t

/-- The binary setup condition extracted from `feasible d M s0 q stock y`. -/
theorem feasible_setup_binary
    {d M : Fin n → ℝ} {s0 : ℝ}
    {q : Fin n → ℝ} {stock : Fin (n + 1) → ℝ} {y : Fin n → ℝ}
    (h_feasible : feasible d M s0 q stock y) (t : Fin n) :
    y t = 0 ∨ y t = 1 := by
  -- Unpack feasibility and evaluate the binary-setup family at the chosen period.
  rcases h_feasible with ⟨_, _, _, _, h_binary⟩
  exact h_binary t

/-- The lot-sizing objective is the sum of setup, production, and holding costs over all
periods. -/
def objective
    (f p i : Fin n → ℝ)
    (q : Fin n → ℝ) (stock : Fin (n + 1) → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ t : Fin n, (f t * y t + p t * q t + i t * stock t.succ)

/-- Unfolding equation for `objective`. -/
theorem objective_def
    (f p i : Fin n → ℝ)
    (q : Fin n → ℝ) (stock : Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    objective f p i q stock y =
      ∑ t : Fin n, (f t * y t + p t * q t + i t * stock t.succ) := by
  -- The objective is defined to be this period-by-period cost sum.
  rfl

/-- The set of objective values attained by feasible lot-sizing schedules. -/
def objectiveValues
    (d f p i M : Fin n → ℝ) (s0 : ℝ) : Set ℝ :=
  { r | ∃ q : Fin n → ℝ, ∃ stock : Fin (n + 1) → ℝ, ∃ y : Fin n → ℝ,
      feasible d M s0 q stock y ∧ objective f p i q stock y = r }

/-- Membership in `objectiveValues d f p i M s0` means that some feasible production, inventory,
and setup schedule attains the value `r`. -/
theorem mem_objectiveValues_iff
    {d f p i M : Fin n → ℝ} {s0 r : ℝ} :
    r ∈ objectiveValues d f p i M s0 ↔
      ∃ q : Fin n → ℝ, ∃ stock : Fin (n + 1) → ℝ, ∃ y : Fin n → ℝ,
        feasible d M s0 q stock y ∧ objective f p i q stock y = r := by
  -- Membership in the attained-value set unfolds directly.
  -- The resulting predicate is existence of a feasible schedule with value `r`.
  rfl

end LotSizing
