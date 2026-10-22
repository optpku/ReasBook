/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.ConditionalProbability

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: if `P B = 0`, then `P (B ∩ A) = 0` by `measure_inter_null_of_null_left`, while
-- `c * P B = c * 0 = 0`. So the defining equation from Definition 8.2 is automatically satisfied
-- for every `c`.
/-- Remark 8.3: if the conditioning event `B` has probability `0`, then every
chosen value `c` satisfies the defining equation `c * P B = P (B ∩ A)`. Thus Definition 8.2 does
not determine a unique conditional-probability value on null conditioning events. -/
theorem null_conditioning_value_irrelevant
    (P : Measure Ω) {A B : Set Ω}
    (hB : P B = 0) (c : ℝ≥0∞) :
    c * P B = P (B ∩ A) := by
  simpa [hB, Set.inter_comm] using (measure_inter_null_of_null_left A hB).symm

-- Proof sketch: `ProbabilityTheory.cond_eq_zero_of_meas_eq_zero` identifies the conditioned
-- measure `P[|B]` with `0` when `P B = 0`. Evaluating that measure at `A` gives `P[A | B] = 0`.
/-- Auxiliary canonical consequence of Remark 8.3: when `P B = 0`, the conditioned measure `P[|B]`
is `0`, so the canonical conditional probability `P[A | B]` evaluates to `0`. -/
theorem cond_apply_eq_zero_of_null
    (P : Measure Ω) {A B : Set Ω} (hB : P B = 0) :
    P[A | B] = 0 := by
  simpa using congrArg (fun ν : Measure Ω ↦ ν A) (cond_eq_zero_of_meas_eq_zero hB)
