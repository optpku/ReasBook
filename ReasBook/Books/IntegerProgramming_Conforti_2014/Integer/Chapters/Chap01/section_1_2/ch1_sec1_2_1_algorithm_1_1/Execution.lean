/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective
public import Mathlib.Order.WithBot

public section

namespace MilpBranchAndBound

/-- A state of a generic MILP branch-and-bound run records the current active-node list, current
lower bound, and optional incumbent feasible point. -/
structure State (n m : ℕ) where
  activeNodes : List (Set (MixedRealPoint n m))
  lowerBound : WithBot ℝ
  incumbent : Option (MixedRealPoint n m)

/-- The initial branch-and-bound state starts from the root relaxation `P₀`, the initial lower
bound `L₀`, and the optional initial incumbent. -/
@[expose] def initial
    {n m : ℕ}
    (P₀ : Set (MixedRealPoint n m))
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m)) : State n m where
  activeNodes := [P₀]
  lowerBound := L₀
  incumbent := incumbent₀

/-- The root active-node list in `initial P₀ L₀ incumbent₀` is exactly `[P₀]`. -/
@[simp] theorem initial_activeNodes
    {n m : ℕ}
    (P₀ : Set (MixedRealPoint n m))
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m)) :
    (initial P₀ L₀ incumbent₀).activeNodes = [P₀] :=
  rfl

/-- The initial lower bound in `initial P₀ L₀ incumbent₀` is `L₀`. -/
@[simp] theorem initial_lowerBound
    {n m : ℕ}
    (P₀ : Set (MixedRealPoint n m))
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m)) :
    (initial P₀ L₀ incumbent₀).lowerBound = L₀ :=
  rfl

/-- The initial incumbent in `initial P₀ L₀ incumbent₀` is `incumbent₀`. -/
@[simp] theorem initial_incumbent
    {n m : ℕ}
    (P₀ : Set (MixedRealPoint n m))
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m)) :
    (initial P₀ L₀ incumbent₀).incumbent = incumbent₀ :=
  rfl

/-- `incumbentSpec S c h L incumbent` means that `incumbent`, when present, is a feasible point of
`S` whose objective value equals the stored lower bound `L`, and that `none` is allowed only at
the value `⊥`. -/
def incumbentSpec
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (L : WithBot ℝ)
    (incumbent : Option (MixedRealPoint n m)) : Prop :=
  (incumbent = none → L = ⊥) ∧
    ∀ xy, incumbent = some xy →
      xy ∈ S ∧ (mixed_linear_objective c h xy : WithBot ℝ) = L

/-- `incumbentSpec S c h L none` says exactly that the stored lower bound is `⊥`. -/
@[simp] theorem incumbentSpec_none_iff
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L : WithBot ℝ} :
    incumbentSpec S c h L none ↔ L = ⊥ := by
  simp [incumbentSpec]

/-- `incumbentSpec S c h L (some xy)` says exactly that `xy` is feasible for `S` and realizes the
stored lower bound `L`. -/
@[simp] theorem incumbentSpec_some_iff
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L : WithBot ℝ}
    {xy : MixedRealPoint n m} :
    incumbentSpec S c h L (some xy) ↔
      xy ∈ S ∧ (mixed_linear_objective c h xy : WithBot ℝ) = L := by
  simp [incumbentSpec]

end MilpBranchAndBound
