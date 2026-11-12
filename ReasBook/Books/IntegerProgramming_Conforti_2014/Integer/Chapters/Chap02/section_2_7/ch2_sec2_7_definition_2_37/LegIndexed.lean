/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_34.Problem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one

open scoped BigOperators

universe w

namespace AsymmetricTravelingSalesmanProblem.LegIndexed

variable {n : ℕ} {A : Type w} [Fintype A]

/-- The natural number `n - 1` is a valid leg index whenever `n > 0`. -/
theorem lastLeg_isLt (hn : 0 < n) :
    n - 1 < n := by
  -- Reduce to the successor case, where the predecessor is visibly below the number itself.
  cases n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hn)
  | succ m =>
      simp

/-- The last leg index of a tour with `n` legs, encoded in `Fin n`. -/
def lastLeg (hn : 0 < n) : Fin n :=
  ⟨n - 1, lastLeg_isLt hn⟩

/-- The underlying natural number of `lastLeg hn` is `n - 1`. -/
@[simp] theorem lastLeg_val (hn : 0 < n) :
    (lastLeg hn : ℕ) = n - 1 := by
  -- Coercing the `Fin` constructor to `ℕ` returns its stored value definitionally.
  rfl

/-- A link index `k : Fin (n - 1)` is also a valid leg index in `Fin n`. -/
theorem linkLeg_isLt (k : Fin (n - 1)) :
    k.1 < n := by
  -- The link index is below `n - 1`, and `n - 1 ≤ n`.
  exact lt_of_lt_of_le k.is_lt (Nat.sub_le _ _)

/-- The successor of a link index `k : Fin (n - 1)` is a valid leg index in `Fin n`. -/
theorem succLinkLeg_isLt (hn : 0 < n) (k : Fin (n - 1)) :
    k.1 + 1 < n := by
  -- Reduce to the successor case so the target is exactly `Nat.succ_lt_succ k.is_lt`.
  cases n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hn)
  | succ m =>
      exact Nat.succ_lt_succ k.is_lt

/-- The distinguished textbook vertex `1`, encoded in zero-based `Fin n`. -/
def firstVertex (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- The underlying natural number of `firstVertex hn` is `0`. -/
@[simp] theorem firstVertex_val (hn : 0 < n) :
    (firstVertex hn : ℕ) = 0 := rfl

/-- A link index `k : Fin (n - 1)` viewed as the corresponding current leg in `Fin n`. -/
def linkLeg (k : Fin (n - 1)) : Fin n :=
  ⟨k.1, linkLeg_isLt k⟩

/-- The underlying natural number of `linkLeg k` is the underlying natural number of `k`. -/
@[simp] theorem linkLeg_val (k : Fin (n - 1)) :
    (linkLeg k : ℕ) = k.1 := rfl

/-- The successor leg associated to a link index `k : Fin (n - 1)`, viewed in `Fin n`. -/
def succLinkLeg (hn : 0 < n) (k : Fin (n - 1)) : Fin n :=
  ⟨k.1 + 1, succLinkLeg_isLt hn k⟩

/-- The underlying natural number of `succLinkLeg hn k` is `k.1 + 1`. -/
@[simp] theorem succLinkLeg_val (hn : 0 < n) (k : Fin (n - 1)) :
    (succLinkLeg hn k : ℕ) = k.1 + 1 := rfl

/-- The leg-indexed feasibility constraints for the asymmetric traveling salesman problem `P`.
They consist of one outgoing use and one incoming use at each vertex across all legs, one chosen
arc per leg, adjacent-leg flow linking, wrap-around at the distinguished textbook vertex `1`
(encoded as `firstVertex hn`), and binary arc-leg variables. -/
def feasible
    (P : AsymmetricTravelingSalesmanProblem (Fin n) A)
    (hn : 0 < n) (x : A → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ∑ k : Fin n, outgoing_flow P.tail (fun a ↦ x a k) i = 1) ∧
    (∀ i : Fin n, ∑ k : Fin n, incoming_flow P.head (fun a ↦ x a k) i = 1) ∧
      (∀ k : Fin n, ∑ a : A, x a k = 1) ∧
        (∀ i : Fin n, ∀ k : Fin (n - 1),
          incoming_flow P.head (fun a ↦ x a (linkLeg k)) i =
            outgoing_flow P.tail (fun a ↦ x a (succLinkLeg hn k)) i) ∧
          incoming_flow P.head (fun a ↦ x a (lastLeg hn)) (firstVertex hn) = 1 ∧
            outgoing_flow P.tail (fun a ↦ x a (firstVertex hn)) (firstVertex hn) = 1 ∧
              is_zero_one_family (fun p : A × Fin n ↦ x p.1 p.2)

/-- Membership in `feasible P hn x` is exactly the conjunction of the leg-indexed ATSP
constraints. -/
theorem feasible_iff
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ} :
    feasible P hn x ↔
      (∀ i : Fin n, ∑ k : Fin n, outgoing_flow P.tail (fun a ↦ x a k) i = 1) ∧
        (∀ i : Fin n, ∑ k : Fin n, incoming_flow P.head (fun a ↦ x a k) i = 1) ∧
          (∀ k : Fin n, ∑ a : A, x a k = 1) ∧
            (∀ i : Fin n, ∀ k : Fin (n - 1),
              incoming_flow P.head (fun a ↦ x a (linkLeg k)) i =
                outgoing_flow P.tail (fun a ↦ x a (succLinkLeg hn k)) i) ∧
              incoming_flow P.head (fun a ↦ x a (lastLeg hn)) (firstVertex hn) = 1 ∧
                outgoing_flow P.tail (fun a ↦ x a (firstVertex hn)) (firstVertex hn) = 1 ∧
                  is_zero_one_family (fun p : A × Fin n ↦ x p.1 p.2) := by
  -- `feasible` is defined to be exactly this conjunction of textbook constraints.
  rfl

/-- The outgoing-use equations extracted from `feasible P hn x`. -/
theorem feasible_outgoing_once
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) (i : Fin n) :
    ∑ k : Fin n, outgoing_flow P.tail (fun a ↦ x a k) i = 1 := by
  -- Project the first conjunct from the expanded feasibility condition.
  exact (feasible_iff.mp h_feasible).1 i

/-- The incoming-use equations extracted from `feasible P hn x`. -/
theorem feasible_incoming_once
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) (i : Fin n) :
    ∑ k : Fin n, incoming_flow P.head (fun a ↦ x a k) i = 1 := by
  -- Project the incoming-use equations from the feasibility conjunction.
  exact (feasible_iff.mp h_feasible).2.1 i

/-- The one-arc-per-leg equations extracted from `feasible P hn x`. -/
theorem feasible_leg_once
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) (k : Fin n) :
    ∑ a : A, x a k = 1 := by
  -- Project the one-arc-per-leg equations from the feasibility conjunction.
  exact (feasible_iff.mp h_feasible).2.2.1 k

/-- The adjacent-leg flow-linking equations extracted from `feasible P hn x`. -/
theorem feasible_link
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) (i : Fin n) (k : Fin (n - 1)) :
    incoming_flow P.head (fun a ↦ x a (linkLeg k)) i =
      outgoing_flow P.tail (fun a ↦ x a (succLinkLeg hn k)) i := by
  -- Project the adjacent-leg linking equations from the feasibility conjunction.
  exact (feasible_iff.mp h_feasible).2.2.2.1 i k

/-- The wrap-around incoming equation at the distinguished textbook vertex `1`, encoded as
`firstVertex hn`, extracted from `feasible P hn x`. -/
theorem feasible_wrap_in
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) :
    incoming_flow P.head (fun a ↦ x a (lastLeg hn)) (firstVertex hn) = 1 := by
  -- Project the wrap-around incoming equation at the distinguished first vertex.
  exact (feasible_iff.mp h_feasible).2.2.2.2.1

/-- The wrap-around outgoing equation at the distinguished textbook vertex `1`, encoded as
`firstVertex hn`, extracted from `feasible P hn x`. -/
theorem feasible_wrap_out
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) :
    outgoing_flow P.tail (fun a ↦ x a (firstVertex hn)) (firstVertex hn) = 1 := by
  -- Project the wrap-around outgoing equation at the distinguished first vertex.
  exact (feasible_iff.mp h_feasible).2.2.2.2.2.1

/-- The binary arc-leg coordinate conditions extracted from `feasible P hn x`. -/
theorem feasible_binary
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {x : A → Fin n → ℝ}
    (h_feasible : feasible P hn x) (a : A) (k : Fin n) :
    x a k = 0 ∨ x a k = 1 := by
  -- Evaluate the final `0/1`-valued family condition at the coordinate `(a, k)`.
  exact is_zero_one_family.apply (feasible_iff.mp h_feasible).2.2.2.2.2.2 (a, k)

/-- The leg-indexed objective attached to `P`, evaluated on the arc-leg variables `x`. -/
def objective
    (P : AsymmetricTravelingSalesmanProblem (Fin n) A)
    (x : A → Fin n → ℝ) : ℝ :=
  ∑ a : A, ∑ k : Fin n, P.cost a * x a k

/-- Unfolding equation for `objective P x`. -/
theorem objective_def
    (P : AsymmetricTravelingSalesmanProblem (Fin n) A)
    (x : A → Fin n → ℝ) :
    objective P x = ∑ a : A, ∑ k : Fin n, P.cost a * x a k := by
  -- This is the defining equation of the objective.
  rfl

/-- The attained objective values of the leg-indexed formulation of `P`. -/
def objectiveValues
    (P : AsymmetricTravelingSalesmanProblem (Fin n) A)
    (hn : 0 < n) : Set ℝ :=
  {r | ∃ x : A → Fin n → ℝ, feasible P hn x ∧ objective P x = r}

/-- Membership in `objectiveValues P hn` means that some leg-indexed feasible solution `x`
attains the objective value `r`. -/
theorem mem_objectiveValues_iff
    {P : AsymmetricTravelingSalesmanProblem (Fin n) A}
    {hn : 0 < n} {r : ℝ} :
    r ∈ objectiveValues P hn ↔
      ∃ x : A → Fin n → ℝ, feasible P hn x ∧ objective P x = r := by
  -- Membership in the attained-value set unfolds to the witness form directly.
  rfl

end AsymmetricTravelingSalesmanProblem.LegIndexed
