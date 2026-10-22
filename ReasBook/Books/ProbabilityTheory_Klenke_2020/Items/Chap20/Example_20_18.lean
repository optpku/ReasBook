/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Dynamics.Ergodic.Extreme

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MeasureTheory
open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: decompose `Q` into its absolutely continuous and singular parts relative to `P`.
-- Mathlib shows that the absolutely continuous part is again `τ`-invariant; ergodicity then forces
-- it to be either `0` or all of `Q`. The latter would imply `Q ≪ P`, hence `Q = P` by the owner
-- theorem `Ergodic.eq_of_absolutelyContinuous`, contradicting `hPQ`.
private theorem mutuallySingular_of_ne_of_ergodic
    {Ω : Type u} [MeasurableSpace Ω] {τ : Ω → Ω} (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Ergodic τ P) (hQ : Ergodic τ Q) (hPQ : P ≠ Q) :
    P ⟂ₘ Q := by
  let Qac : Measure Ω := P.withDensity (Q.rnDeriv P)
  have hQac_pres : MeasurePreserving τ Qac Qac := by
    simpa [Qac] using hQ.toMeasurePreserving.withDensity_rnDeriv hP.toMeasurePreserving
  obtain ⟨c, hQac_eq⟩ :=
    hQ.eq_smul_of_absolutelyContinuous hQac_pres
      (Measure.withDensity_rnDeriv_le Q P).absolutelyContinuous
  rcases eq_or_ne c 0 with rfl | hc
  · have hQsing : Q.singularPart P = Q := by
      simpa [Qac, hQac_eq] using (Measure.rnDeriv_add_singularPart Q P)
    exact ((Measure.singularPart_eq_self).mp hQsing).symm
  · have hQ_acP : Q ≪ P := by
      have hQ_Qac : Q ≪ c • Q := Measure.absolutelyContinuous_smul hc
      rw [← hQac_eq] at hQ_Qac
      exact hQ_Qac.trans <| withDensity_absolutelyContinuous P _
    exact False.elim <| hPQ <| (hP.eq_of_absolutelyContinuous hQ.toMeasurePreserving hQ_acP).symm

-- Proof sketch: argue by cases on whether `P = Q`. In the unequal case, apply
-- `mutuallySingular_of_ne_of_ergodic`.
/-- Example 20.18: if the same transformation `τ` is ergodic for two probability measures `P`
and `Q` on `(Ω, 𝓐)`, then the measures either coincide or are mutually singular. -/
theorem ergodic_probability_measures_eq_or_mutuallySingular
    {Ω : Type u} [MeasurableSpace Ω] {τ : Ω → Ω} (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Ergodic τ P) (hQ : Ergodic τ Q) :
    P = Q ∨ P ⟂ₘ Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · exact Or.inl rfl
  · exact Or.inr <| mutuallySingular_of_ne_of_ergodic P Q hP hQ hPQ
