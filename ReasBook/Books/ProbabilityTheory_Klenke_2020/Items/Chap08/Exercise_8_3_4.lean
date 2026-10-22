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
variable {n : ℕ}

-- Proof sketch: push the conditioned measure `P[|X ⁻¹' B]` forward along `X`; by
-- `Measure.restrict_map_of_aemeasurable` and `hX.map_eq` this is exactly the conditioned
-- pushforward measure `(volume[|A])[|B]`. Since `A` has finite Lebesgue measure,
-- `ProbabilityTheory.cond_cond_eq_cond_inter'` rewrites this to
-- `volume[|A ∩ B]`, which simplifies to `volume[|B]` because `B ⊆ A`.
/-- Exercise 8.3.4: Let `A, B ⊆ ℝ^n` with `B ⊆ A`. If `A` and `B` are Borel measurable,
`A` has finite Lebesgue measure and `X` has law `volume[|A]` under `P`, then under the
conditioned measure `P[|X ⁻¹' B]` the random variable `X` has law `volume[|B]`. -/
theorem hasLaw_conditioned_on_mem_eq_volume_cond_subset
    {P : Measure Ω} {X : Ω → EuclideanSpace ℝ (Fin n)}
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B) (hBA : B ⊆ A)
    (hA_finite : volume A ≠ ⊤)
    (hX : HasLaw X (volume[|A]) P) :
    HasLaw X (volume[|B]) P[|X ⁻¹' B] := by
  refine ⟨hX.aemeasurable.mono_ac cond_absolutelyContinuous, ?_⟩
  calc
    P[|X ⁻¹' B].map X = (P.map X)[|B] := by
      rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
        Measure.restrict_map_of_aemeasurable hX.aemeasurable hB_meas,
        Measure.map_apply_of_aemeasurable hX.aemeasurable hB_meas]
    _ = (volume[|A])[|B] := by rw [hX.map_eq]
    _ = volume[|B] := by
      rw [cond_cond_eq_cond_inter' hA_meas hB_meas hA_finite]
      simp [Set.inter_eq_right.2 hBA]
