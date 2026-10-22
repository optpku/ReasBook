/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem measurable_real_sign_map : Measurable (Real.sign : ℝ → ℝ) := by
  refine Measurable.piecewise measurableSet_Iio measurable_const ?_
  exact Measurable.piecewise measurableSet_Ioi measurable_const measurable_const

private theorem measurable_ereal_abs_map : Measurable (fun x : EReal ↦ EReal.abs x) := by
  refine EReal.measurable_of_measurable_real ?_
  simpa [EReal.abs_def] using ENNReal.measurable_ofReal.comp continuous_abs.measurable

private theorem measurable_ereal_sign_map :
    Measurable (fun x : EReal ↦ (SignType.sign x : EReal)) := by
  have hsign :
      (fun x : EReal ↦ (SignType.sign x : EReal)) =
        (Set.Ioi (0 : EReal)).piecewise (fun _ ↦ (1 : EReal))
          ((Set.Iio (0 : EReal)).piecewise (fun _ ↦ (-1 : EReal)) fun _ ↦ (0 : EReal)) := by
    funext x
    rw [sign_apply]
    by_cases hx₁ : 0 < x
    · simp [hx₁, Set.piecewise]
    · by_cases hx₂ : x < 0
      · simp [hx₁, hx₂, Set.piecewise]
      · simp [hx₁, hx₂, Set.piecewise]
  rw [hsign]
  exact Measurable.piecewise (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : EReal)))
    (measurable_const : Measurable fun _ : EReal ↦ (1 : EReal)) <|
      Measurable.piecewise (measurableSet_Iio : MeasurableSet (Set.Iio (0 : EReal)))
        (measurable_const : Measurable fun _ : EReal ↦ (-1 : EReal))
        (measurable_const : Measurable fun _ : EReal ↦ (0 : EReal))

/-- Corollary 1.89 (1): if `X : Ω → ℝ` is measurable, then its positive part `X⁺` is measurable. -/
-- Proof sketch: compose the measurable map `X` with the measurable positive-part map on `ℝ`.
theorem measurable_real_posPart (X : Ω → ℝ) (hX : Measurable X) :
    Measurable fun ω ↦ (X ω)⁺ := by
  simpa using hX.posPart

/-- Corollary 1.89 (2): if `X : Ω → ℝ` is measurable, then its negative part `X⁻` is measurable. -/
-- Proof sketch: compose `X` with the measurable negative-part map on `ℝ`.
theorem measurable_real_negPart (X : Ω → ℝ) (hX : Measurable X) :
    Measurable fun ω ↦ (X ω)⁻ := by
  simpa using hX.negPart

/-- Corollary 1.89 (3): if `X : Ω → ℝ` is measurable,
then its absolute value `|X|` is measurable. -/
-- Proof sketch: apply measurability of absolute value and compose with `X`.
theorem measurable_real_abs (X : Ω → ℝ) (hX : Measurable X) :
    Measurable fun ω ↦ |X ω| := by
  fun_prop

/-- Corollary 1.89 (4): if `X : Ω → ℝ` is measurable, then its sign `sign(X)` is measurable. -/
-- Proof sketch: show `Real.sign` is measurable by its piecewise definition, then compose with `X`.
theorem measurable_real_sign (X : Ω → ℝ) (hX : Measurable X) :
    Measurable fun ω ↦ Real.sign (X ω) := by
  exact measurable_real_sign_map.comp hX

/-- Corollary 1.89 (5): if `X : Ω → EReal` is measurable, then its positive part `X⁺`,
formalized as `max X 0`, is measurable. -/
-- Proof sketch: `x ↦ max x 0` is measurable on `EReal`, so its composition with `X` is measurable.
theorem measurable_ereal_posPart (X : Ω → EReal) (hX : Measurable X) :
    Measurable fun ω ↦ max (X ω) 0 := by
  fun_prop

/-- Corollary 1.89 (6): if `X : Ω → EReal` is measurable, then its negative part `X⁻`,
formalized as `max (-X) 0`, is measurable. -/
-- Proof sketch: measurability follows from measurability of negation,
-- `max`, and the constant map `0`.
theorem measurable_ereal_negPart (X : Ω → EReal) (hX : Measurable X) :
    Measurable fun ω ↦ max (-X ω) 0 := by
  fun_prop

/-- Corollary 1.89 (7): if `X : Ω → EReal` is measurable, then its absolute value,
viewed as an `ℝ≥0∞`-valued map, is measurable. -/
-- Proof sketch: prove measurability of `EReal.abs` and compose it with `X`.
theorem measurable_ereal_abs (X : Ω → EReal) (hX : Measurable X) :
    Measurable fun ω ↦ EReal.abs (X ω) := by
  exact measurable_ereal_abs_map.comp hX

/-- Corollary 1.89 (8): if `X : Ω → EReal` is measurable, then its sign, viewed as an `EReal`-valued
map with values in `{-1, 0, 1}`, is measurable. -/
-- Proof sketch: use the piecewise description of `SignType.sign` on `EReal`
-- and then coerce to `EReal`.
theorem measurable_ereal_sign (X : Ω → EReal) (hX : Measurable X) :
    Measurable fun ω ↦ (SignType.sign (X ω) : EReal) := by
  exact measurable_ereal_sign_map.comp hX
