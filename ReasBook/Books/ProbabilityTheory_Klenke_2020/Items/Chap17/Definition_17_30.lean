/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/- Layering for Definition 17.30:
- `F[P, X]` from Definition 17.28 is the chapter owner abstraction for positive-time ever-hit
  probabilities, so recurrence/transience of a state should be stated directly using
  `(F[P, X]) x x`.
- `expectedFirstReturnTime` is the remaining primitive data specific to this item.
- the recurrent/null/transient predicates and their chain-level versions are derived API. -/

/-- The expected first return time `𝔼_x[τ_x^1]`, taken in the extended nonnegative reals. -/
def expectedFirstReturnTime (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : ℝ≥0∞ :=
  ∫⁻ ω, ((τ_[X, x]^1) ω : ℝ≥0∞) ∂(P x : Measure Ω)

/-- Definition 17.30: a state `x` is recurrent if its return probability `F(x,x)` is `1`. -/
def IsRecurrentState (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  (F[P, X]) x x = 1

/-- A state `x` is positive recurrent if the expected first return time `𝔼_x[τ_x^1]` is finite. -/
def IsPositiveRecurrentState
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  expectedFirstReturnTime P X x < ⊤

/-- A state `x` is null recurrent if it is recurrent but not positive recurrent. -/
def IsNullRecurrentState
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  IsRecurrentState P X x ∧ ¬ IsPositiveRecurrentState P X x

/-- A state `x` is transient if its return probability `F(x,x)` is strictly smaller than `1`. -/
def IsTransientState (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  (F[P, X]) x x < 1

/-- A state `x` is absorbing for the one-step transition matrix `p` if it stays at `x` with
probability `1` in one step. -/
def IsAbsorbingState (p : E → E → ℝ≥0∞) (x : E) : Prop :=
  p x x = 1

/-- A Markov chain is recurrent if every state is recurrent. -/
def IsRecurrentMarkovChain (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsRecurrentState P X x

/-- A Markov chain is positive recurrent if every state is positive recurrent. -/
def IsPositiveRecurrentMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsPositiveRecurrentState P X x

/-- A Markov chain is null recurrent if every state is null recurrent. -/
def IsNullRecurrentMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsNullRecurrentState P X x

section TransientMarkovChain

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

/-- Definition 17.30: for a realization of the discrete chain with one-step transition matrix `p`,
the chain is transient if every recurrent state is absorbing for that actual transition matrix. -/
def IsTransientMarkovChain
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsRecurrentState P X x → IsAbsorbingState p x

-- Proof sketch: if every state is transient, then no state is recurrent, so Definition 17.30
-- holds vacuously.
/-- If every state of the chain is transient, then the chain is transient in the sense of
Definition 17.30. -/
theorem isTransientMarkovChain_of_forall_isTransientState
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (htransient : ∀ x : E, IsTransientState P X x) :
    IsTransientMarkovChain p P X := by
  intro x hx
  have hx_not_transient : ¬ IsTransientState P X x := by
    rw [IsTransientState, hx]
    simp
  exact False.elim (hx_not_transient (htransient x))

end TransientMarkovChain

end ProbabilityTheory
