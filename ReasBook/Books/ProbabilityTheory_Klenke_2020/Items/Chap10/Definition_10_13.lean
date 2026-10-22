/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MeasureTheory

section

variable {Ω : Type u} {ι : Type v} {m : MeasurableSpace Ω} [LinearOrder ι]

/- Definition 10.13: The canonical stopped process of a process `X` at a random time `τ` is
`MeasureTheory.stoppedProcess X τ`; when `X` is adapted and `τ` is a stopping time, this is the
textbook stopped process `X^τ` with time-`t` value `X_{τ ∧ t}`. -/
recall MeasureTheory.stoppedProcess

/-- The stopped filtration `𝓕^τ` is the filtration whose time-`t` `σ`-algebra is `𝓕_{τ ∧ t}`. -/
def stoppedFiltration
    (ℱ : Filtration ι m) {τ : Ω → WithTop ι} (hτ : IsStoppingTime ℱ τ) : Filtration ι m :=
  Filtration.const ι hτ.measurableSpace hτ.measurableSpace_le ⊓ ℱ

/-- At each deterministic time `t`, the stopped filtration agrees with the stopping-time
`σ`-algebra of `τ ∧ t`. -/
@[simp]
theorem stoppedFiltration_apply
    (ℱ : Filtration ι m) {τ : Ω → WithTop ι} (hτ : IsStoppingTime ℱ τ) (t : ι) :
    stoppedFiltration ℱ hτ t = (hτ.min_const t).measurableSpace :=
  by
    simpa [stoppedFiltration] using (hτ.measurableSpace_min_const).symm

end
