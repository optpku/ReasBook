/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Probability.Kernel.Composition.Comp

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Definition 18.1 (1): for states `x` and `y`, `positiveTransitionStepSet κ x y` is the set of
times `n ∈ ℕ₀` for which the `n`-step transition probability from `x` to `y` is strictly
positive. -/
def positiveTransitionStepSet (κ : Kernel E E) (x y : E) : Set ℕ :=
  {n : ℕ | 0 < (κ ^ n) x {y}}

/-- Definition 18.1 (2): the period of the state `x` is the greatest common divisor of the
positive-probability return times from `x` to itself. -/
def statePeriod (κ : Kernel E E) (x : E) : ℕ :=
  sSup {d : ℕ | ∀ n ∈ positiveTransitionStepSet κ x x, d ∣ n}

/-- Definition 18.1 (3): a discrete Markov chain has period `d` when every state has period `d`.
-/
def HasPeriod (κ : Kernel E E) (d : ℕ) : Prop :=
  ∀ x : E, statePeriod κ x = d

/-- Definition 18.1 (4): a discrete Markov chain is aperiodic when every state has period `1`. -/
def IsAperiodic (κ : Kernel E E) : Prop :=
  HasPeriod κ 1

-- Proof sketch: this is immediate from the definition of `positiveTransitionStepSet`.
/-- Membership in `positiveTransitionStepSet κ x y` means exactly that the `n`-step transition
probability from `x` to `y` is strictly positive. -/
theorem mem_positiveTransitionStepSet_iff (κ : Kernel E E) (x y : E) (n : ℕ) :
    n ∈ positiveTransitionStepSet κ x y ↔ 0 < (κ ^ n) x {y} := by
  -- Unfolding the set definition turns membership into the claimed inequality.
  rfl

-- Proof sketch: `statePeriod κ x` is defined as the supremum of the common divisors of all
-- positive-probability return times to `x`, so it divides each such return time.
/-- The period of a state divides every time at which the chain can return to that state with
positive probability. -/
theorem statePeriod_dvd_of_mem_positiveTransitionStepSet
    (κ : Kernel E E) (x : E) {n : ℕ} (hn : n ∈ positiveTransitionStepSet κ x x) :
    statePeriod κ x ∣ n := by
  cases n with
  | zero =>
      -- At time `0` the divisibility claim is immediate.
      simpa using dvd_zero (statePeriod κ x)
  | succ n =>
      let S : Set ℕ := {d : ℕ | ∀ m ∈ positiveTransitionStepSet κ x x, d ∣ m}
      -- The common-divisor set is nonempty because `1` divides every return time.
      have hS_nonempty : S.Nonempty := by
        refine ⟨1, ?_⟩
        intro m hm
        exact one_dvd m
      -- The positive return time `n + 1` bounds every common divisor from above.
      have hS_bddAbove : BddAbove S := by
        refine ⟨Nat.succ n, ?_⟩
        intro d hd
        exact Nat.le_of_dvd (Nat.succ_pos _) (hd (Nat.succ n) hn)
      -- Since `statePeriod κ x` is the supremum of `S`, boundedness puts it back inside `S`.
      have hstate_mem : statePeriod κ x ∈ S := by
        rw [statePeriod]
        exact Nat.sSup_mem hS_nonempty hS_bddAbove
      -- Membership in `S` is exactly the desired divisibility statement at the time `n + 1`.
      exact hstate_mem (Nat.succ n) hn

-- Proof sketch: specialize the defining equalities in `HasPeriod κ d` at the states `x` and `y`.
/-- If a chain has period `d`, then all states have the same period. -/
theorem statePeriod_eq_of_hasPeriod
    {κ : Kernel E E} {d : ℕ} (hκ : HasPeriod κ d) (x y : E) :
    statePeriod κ x = statePeriod κ y := by
  -- Rewrite both state periods using the global period hypothesis.
  calc
    statePeriod κ x = d := hκ x
    _ = statePeriod κ y := (hκ y).symm

section

variable {F : Type u} [MeasurableSpace F]

-- Proof sketch: unfold `IsAperiodic` and `HasPeriod`; both say exactly that every state period is
-- equal to `1`.
/-- A chain is aperiodic exactly when it has period `1`. -/
theorem isAperiodic_iff_hasPeriod_one (κ : Kernel F F) :
    IsAperiodic κ ↔ HasPeriod κ 1 :=
  Iff.rfl

end

end ProbabilityTheory
