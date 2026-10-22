/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {A B S T : Set Ω}

-- Proof sketch: use `indepSet_iff_measure_inter_eq_mul` to rewrite independence as
-- `P (A ∩ B) = P A * P B`, and use `cond_apply` with the positivity hypotheses `0 < P A` and
-- `0 < P B` to cancel the conditioning factors and obtain the two conditional-probability
-- identities. The converse implications are obtained by reversing the same calculation.
private theorem indepSet_iff_cond_eq_of_pos
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hPT : 0 < P T) :
    IndepSet S T P ↔ P[S | T] = P S := by
  constructor
  · intro hIndep
    have hPT0 : P T ≠ 0 := ne_of_gt hPT
    calc
      P[S | T] = (P T)⁻¹ * P (T ∩ S) := cond_apply hT P S
      _ = (P T)⁻¹ * P (S ∩ T) := by rw [Set.inter_comm]
      _ = (P T)⁻¹ * (P S * P T) := by
        rw [(indepSet_iff_measure_inter_eq_mul hS hT P).1 hIndep]
      _ = P S := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          congrArg (fun x ↦ P S * x) (ENNReal.inv_mul_cancel hPT0 (measure_ne_top P T))
  · intro hCond
    rw [indepSet_iff_measure_inter_eq_mul hS hT P]
    have h := congrArg (fun x ↦ x * P T) hCond
    simpa [cond_mul_eq_inter hT S P, Set.inter_comm, mul_assoc, mul_comm, mul_left_comm] using h

private theorem indepSet_comm (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B P ↔ IndepSet B A P := by
  rw [indepSet_iff_measure_inter_eq_mul hA hB P, indepSet_iff_measure_inter_eq_mul hB hA P,
    Set.inter_comm, mul_comm]

/-- Theorem 8.5: for measurable events `A` and `B` of positive probability in a probability space,
the following are equivalent: `A` and `B` are independent, `P[A | B] = P[A]`, and
`P[B | A] = P[B]`. -/
theorem indepSet_tfae_cond_eq_self
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hPA : 0 < P A) (hPB : 0 < P B) :
    List.TFAE
      [ IndepSet A B P
      , P[A | B] = P A
      , P[B | A] = P B
      ] := by
  tfae_have 1 ↔ 2 := indepSet_iff_cond_eq_of_pos P hA hB hPB
  tfae_have 1 ↔ 3 := by
    rw [indepSet_comm P hA hB]
    exact indepSet_iff_cond_eq_of_pos P hB hA hPA
  tfae_finish

end
