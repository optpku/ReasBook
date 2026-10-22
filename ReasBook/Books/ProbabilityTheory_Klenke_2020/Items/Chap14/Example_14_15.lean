/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {n : ℕ} {Ω : Fin n → Type v}

variable [∀ i, MeasurableSpace (Ω i)]

variable (P : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]

/- Example 14.15: the coordinate maps on the finite product probability space
`∏ i : Fin n, Ω i` are independent under the product measure `Measure.pi P`. -/
#check (iIndepFun_pi (fun _ ↦ aemeasurable_id) :
  iIndepFun Function.eval (Measure.pi P))

/- Each coordinate projection on the finite product space has its corresponding marginal law via
the canonical measure-preserving evaluation map on `Measure.pi P`. -/
#check (fun i : Fin n ↦
  ((measurePreserving_eval P i).hasLaw :
    HasLaw (Function.eval i) (P i) (Measure.pi P)))
