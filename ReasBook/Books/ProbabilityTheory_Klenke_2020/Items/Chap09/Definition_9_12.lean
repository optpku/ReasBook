/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory TopologicalSpace

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

local notation "DiscreteFiltration" => Filtration ℕ mΩ

/-- Definition 9.12: a discrete process is predictable (previsible) with respect to a filtration
if its initial value is constant and each value at time `n + 1` is measurable with respect to the
previous σ-algebra `ℱ n`. -/
def IsPredictableProcess (ℱ : DiscreteFiltration) (X : ℕ → Ω → E) : Prop :=
  (∃ c : E, X 0 = fun _ ↦ c) ∧ ∀ n : ℕ, Measurable[ℱ n] (X (n + 1))

theorem IsPredictableProcess.measurable_zero
    {ℱ : DiscreteFiltration} {X : ℕ → Ω → E} (hX : IsPredictableProcess ℱ X) :
    Measurable[ℱ 0] (X 0) := by
  rcases hX.1 with ⟨c, h0⟩
  rw [h0]
  exact measurable_const

theorem IsPredictableProcess.measurable_add_one
    {ℱ : DiscreteFiltration} {X : ℕ → Ω → E} (hX : IsPredictableProcess ℱ X) (n : ℕ) :
    Measurable[ℱ n] (X (n + 1)) :=
  hX.2 n

-- Proof sketch: use the constant initial value to obtain `𝓕 0`-measurability at time `0`, then
-- apply `MeasureTheory.isPredictable_of_measurable_add_one` to the shifted measurability
-- conditions.
/-- A predictable process in the textbook sense is predictable in mathlib's discrete filtration
sense. -/
theorem isPredictableProcess_isPredictable
    [TopologicalSpace E] [MetrizableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ℱ : DiscreteFiltration} {X : ℕ → Ω → E} (hX : IsPredictableProcess ℱ X) :
    IsPredictable ℱ X :=
  isPredictable_of_measurable_add_one hX.measurable_zero (fun n ↦ hX.measurable_add_one n)

end ProbabilityTheory
