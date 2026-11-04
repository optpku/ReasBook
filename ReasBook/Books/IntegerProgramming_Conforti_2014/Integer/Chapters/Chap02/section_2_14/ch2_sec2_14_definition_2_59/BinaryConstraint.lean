/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

open scoped BigOperators

public section

namespace BinaryConstraint

universe u

variable {α : Type u}

/-- The inequality stating that at most one element of `S` is selected by the binary vector `x`. -/
def atMostOne (S : Finset α) (x : α → ℝ) : Prop :=
  S.sum x ≤ 1

/-- Unfolding characterization of `atMostOne`. -/
theorem atMostOne_iff
    {S : Finset α} {x : α → ℝ} :
    atMostOne S x ↔ S.sum x ≤ 1 :=
  Iff.rfl

/-- The equality stating that exactly `k` elements of `S` are selected by the binary vector `x`. -/
def exactly (S : Finset α) (k : ℕ) (x : α → ℝ) : Prop :=
  S.sum x = (k : ℝ)

/-- Unfolding characterization of `exactly`. -/
theorem exactly_iff
    {S : Finset α} {k : ℕ} {x : α → ℝ} :
    exactly S k x ↔ S.sum x = (k : ℝ) :=
  Iff.rfl

/-- The inequality encoding the implication `a → b` for binary variables. -/
def implies (a b : α) (x : α → ℝ) : Prop :=
  x a ≤ x b

/-- Unfolding characterization of `implies`. -/
theorem implies_iff
    {a b : α} {x : α → ℝ} :
    implies a b x ↔ x a ≤ x b :=
  Iff.rfl

/-- The inequality encoding the implication `a → ¬b` for binary variables. -/
def impliesNot (a b : α) (x : α → ℝ) : Prop :=
  x a + x b ≤ 1

/-- Unfolding characterization of `impliesNot`. -/
theorem impliesNot_iff
    {a b : α} {x : α → ℝ} :
    impliesNot a b x ↔ x a + x b ≤ 1 :=
  Iff.rfl

/-- The inequality encoding the implication `¬a → b` for binary variables. -/
def notImplies (a b : α) (x : α → ℝ) : Prop :=
  1 - x a ≤ x b

/-- Unfolding characterization of `notImplies`. -/
theorem notImplies_iff
    {a b : α} {x : α → ℝ} :
    notImplies a b x ↔ 1 - x a ≤ x b :=
  Iff.rfl

/-- The paired inequalities encoding the equivalence `a ↔ b` for binary variables. -/
def equivalent (a b : α) (x : α → ℝ) : Prop :=
  x a ≤ x b ∧ x b ≤ x a

/-- Unfolding characterization of `equivalent`. -/
theorem equivalent_iff
    {a b : α} {x : α → ℝ} :
    equivalent a b x ↔ x a ≤ x b ∧ x b ≤ x a :=
  Iff.rfl

/-- The implication `a → b` extracted from `equivalent a b x`. -/
theorem equivalent_forward
    {a b : α} {x : α → ℝ}
    (h_equivalent : equivalent a b x) :
    x a ≤ x b :=
  h_equivalent.1

/-- The implication `b → a` extracted from `equivalent a b x`. -/
theorem equivalent_backward
    {a b : α} {x : α → ℝ}
    (h_equivalent : equivalent a b x) :
    x b ≤ x a :=
  h_equivalent.2

/-- The paired inequalities encoding the implication `a → (b ∧ c)` for binary variables. -/
def impliesBoth (a b c : α) (x : α → ℝ) : Prop :=
  x a ≤ x b ∧ x a ≤ x c

/-- Unfolding characterization of `impliesBoth`. -/
theorem impliesBoth_iff
    {a b c : α} {x : α → ℝ} :
    impliesBoth a b c x ↔ x a ≤ x b ∧ x a ≤ x c :=
  Iff.rfl

/-- The implication `a → b` extracted from `impliesBoth a b c x`. -/
theorem impliesBoth_left
    {a b c : α} {x : α → ℝ}
    (h_impliesBoth : impliesBoth a b c x) :
    x a ≤ x b :=
  h_impliesBoth.1

/-- The implication `a → c` extracted from `impliesBoth a b c x`. -/
theorem impliesBoth_right
    {a b c : α} {x : α → ℝ}
    (h_impliesBoth : impliesBoth a b c x) :
    x a ≤ x c :=
  h_impliesBoth.2

/-- The inequality encoding the implication `a → (b ∨ c)` for binary variables. -/
def impliesOneOf (a b c : α) (x : α → ℝ) : Prop :=
  x a ≤ x b + x c

/-- Unfolding characterization of `impliesOneOf`. -/
theorem impliesOneOf_iff
    {a b c : α} {x : α → ℝ} :
    impliesOneOf a b c x ↔ x a ≤ x b + x c :=
  Iff.rfl

/-- The paired inequalities encoding the implication `(b ∨ c) → a` for binary variables. -/
def eitherImplies (b c a : α) (x : α → ℝ) : Prop :=
  x b ≤ x a ∧ x c ≤ x a

/-- Unfolding characterization of `eitherImplies`. -/
theorem eitherImplies_iff
    {a b c : α} {x : α → ℝ} :
    eitherImplies b c a x ↔ x b ≤ x a ∧ x c ≤ x a :=
  Iff.rfl

/-- The implication `b → a` extracted from `eitherImplies b c a x`. -/
theorem eitherImplies_left
    {a b c : α} {x : α → ℝ}
    (h_eitherImplies : eitherImplies b c a x) :
    x b ≤ x a :=
  h_eitherImplies.1

/-- The implication `c → a` extracted from `eitherImplies b c a x`. -/
theorem eitherImplies_right
    {a b c : α} {x : α → ℝ}
    (h_eitherImplies : eitherImplies b c a x) :
    x c ≤ x a :=
  h_eitherImplies.2

/-- The threshold implication encoding that if at least `k` elements of `S` are selected, then
`a` must also be selected. -/
def atLeastImplies (k : ℕ) (S : Finset α) (a : α) (x : α → ℝ) : Prop :=
  S.sum x - ((k : ℝ) - 1) ≤ ((S.card : ℝ) - ((k : ℝ) - 1)) * x a

/-- Unfolding characterization of `atLeastImplies`. -/
theorem atLeastImplies_iff
    {k : ℕ} {S : Finset α} {a : α} {x : α → ℝ} :
    atLeastImplies k S a x ↔
      S.sum x - ((k : ℝ) - 1) ≤ ((S.card : ℝ) - ((k : ℝ) - 1)) * x a :=
  Iff.rfl

end BinaryConstraint
