/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : ι → Type v}
variable [∀ i, MeasurableSpace (Ω i)]

variable (P : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]

/- Example 14.37: in the textbook this is stated for probability measures on the Borel
`σ`-algebras of Polish spaces; the canonical owner statement used here is the measurable-space
form saying that `Measure.infinitePi P` is the projective limit of the finite product measures
`Measure.pi (fun j : J ↦ P j)`. -/
recall Measure.isProjectiveLimit_infinitePi

/- The coordinate maps are independent under the infinite product probability measure by the
specialization of `iIndepFun_infinitePi` to the identity maps on the factor spaces. -/
#check (iIndepFun_infinitePi (fun _ ↦ measurable_id) :
  iIndepFun Function.eval (Measure.infinitePi P))

/- Each coordinate projection on the infinite product space has the corresponding marginal law via
the canonical measure-preserving evaluation map on `Measure.infinitePi P`. -/
#check (fun i ↦ MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi P i) :
  ∀ i : ι, HasLaw (Function.eval i) (P i) (Measure.infinitePi P))
