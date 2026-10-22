/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_31

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

def closedUnitDisc : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def unitSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

/-- The uniform law on the closed unit disc in `ℝ²`. -/
def unitDiscUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|closedUnitDisc]

/-- The uniform law on the square `[-1,1]^2` in `ℝ²`. -/
def unitSquareUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|unitSquare]

/-- Helper for Exercise 8.3.3: the closed unit disc is a measurable subset of `ℝ²`. -/
private theorem measurableSet_closedUnitDisc : MeasurableSet closedUnitDisc := by
  -- Proof comment: the defining inequality is the preimage of the closed ray `(-∞, 1]` under a
  -- continuous polynomial map.
  refine measurableSet_le (by fun_prop) measurable_const

/-- Helper for Exercise 8.3.3: the square `[-1,1]^2` is a measurable subset of `ℝ²`. -/
private theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  -- Proof comment: the square is a product of measurable closed intervals.
  simpa [unitSquare] using measurableSet_Icc.prod measurableSet_Icc

/-- Helper for Exercise 8.3.3: the unit-disc law is Lebesgue measure with constant density on the
disc. -/
private theorem unitDiscUniformMeasure_eq_withDensity_indicator :
    unitDiscUniformMeasure =
      (volume : Measure (ℝ × ℝ)).withDensity
        (Set.indicator closedUnitDisc fun _ ↦ (volume closedUnitDisc)⁻¹) := by
  -- Proof comment: unfold conditioned volume, rewrite the scalar multiple as a `withDensity`, and
  -- then move the support restriction into an indicator density on ambient Lebesgue measure.
  calc
    unitDiscUniformMeasure
        = (volume.restrict closedUnitDisc).withDensity
            ((volume closedUnitDisc)⁻¹ • (1 : (ℝ × ℝ) → ENNReal)) := by
            rw [unitDiscUniformMeasure, ProbabilityTheory.cond, withDensity_smul _ measurable_one,
              withDensity_one]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (Set.indicator closedUnitDisc (((volume closedUnitDisc)⁻¹) • (1 : (ℝ × ℝ) → ENNReal))) := by
          rw [← withDensity_indicator measurableSet_closedUnitDisc]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (Set.indicator closedUnitDisc fun _ ↦ (volume closedUnitDisc)⁻¹) := by
          congr with z
          by_cases hz : z ∈ closedUnitDisc
          · simp [Set.indicator_of_mem, hz]
          · simp [Set.indicator_of_notMem, hz]

/-- Helper for Exercise 8.3.3: the square law is Lebesgue measure with constant density on
`[-1,1]^2`. -/
private theorem unitSquareUniformMeasure_eq_withDensity_indicator :
    unitSquareUniformMeasure =
      (volume : Measure (ℝ × ℝ)).withDensity
        (Set.indicator unitSquare fun _ ↦ (volume unitSquare)⁻¹) := by
  -- Proof comment: the square case is the same normalized-restriction rewrite as for the disc.
  calc
    unitSquareUniformMeasure
        = (volume.restrict unitSquare).withDensity
            ((volume unitSquare)⁻¹ • (1 : (ℝ × ℝ) → ENNReal)) := by
            rw [unitSquareUniformMeasure, ProbabilityTheory.cond, withDensity_smul _ measurable_one,
              withDensity_one]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (Set.indicator unitSquare (((volume unitSquare)⁻¹) • (1 : (ℝ × ℝ) → ENNReal))) := by
          rw [← withDensity_indicator measurableSet_unitSquare]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (Set.indicator unitSquare fun _ ↦ (volume unitSquare)⁻¹) := by
          congr with z
          by_cases hz : z ∈ unitSquare
          · simp [Set.indicator_of_mem, hz]
          · simp [Set.indicator_of_notMem, hz]

private theorem closedUnitDisc_subset_unitSquare : closedUnitDisc ⊆ unitSquare := by
  intro z hz
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1 at hz
  rw [unitSquare]
  constructor
  · constructor
    · nlinarith [sq_nonneg z.2, hz]
    · nlinarith [sq_nonneg z.2, hz]
  · constructor
    · nlinarith [sq_nonneg z.1, hz]
    · nlinarith [sq_nonneg z.1, hz]

private theorem halfUnitSquare_subset_closedUnitDisc :
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) : Set (ℝ × ℝ)) ⊆
      closedUnitDisc := by
  intro z hz
  rcases hz with ⟨hx, hy⟩
  have hx_sq : z.1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hy_sq : z.2 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hy.1, hy.2]
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1
  nlinarith

private theorem volume_unitSquare_pos : 0 < volume unitSquare := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_unitSquare_ne_top : volume unitSquare ≠ ⊤ := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_pos : 0 < volume closedUnitDisc := by
  refine lt_of_lt_of_le ?_ (measure_mono halfUnitSquare_subset_closedUnitDisc)
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_ne_top : volume closedUnitDisc ≠ ⊤ := by
  refine ne_of_lt <| lt_of_le_of_lt (measure_mono closedUnitDisc_subset_unitSquare) ?_
  exact lt_top_iff_ne_top.mpr volume_unitSquare_ne_top

-- Proof sketch: apply the standard fact that conditioned Lebesgue measure on a set of positive
-- finite volume is a probability measure; here the unit disc has finite positive area.
/-- The uniform law on the closed unit disc is a probability measure. -/
instance : IsProbabilityMeasure unitDiscUniformMeasure := by
  rw [unitDiscUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_closedUnitDisc_pos.ne' volume_closedUnitDisc_ne_top

-- Proof sketch: apply the same conditioned-volume probability-measure fact to the square
-- `[-1,1]^2`, whose Lebesgue measure is finite and nonzero.
/-- The uniform law on `[-1,1]^2` is a probability measure. -/
instance : IsProbabilityMeasure unitSquareUniformMeasure := by
  rw [unitSquareUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_unitSquare_pos.ne' volume_unitSquare_ne_top

private theorem measurableSet_polarCoord_target : MeasurableSet polarCoord.target :=
  polarCoord.open_target.measurableSet

/-- The radius `R = sqrt (x^2 + y^2)` associated to a point `(x, y) ∈ ℝ²`. -/
abbrev planarRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

/-- The textbook angle variable `Θ = arctan (y / x)`. In Lean, division by `0` is defined, so
this gives a total measurable function on `ℝ²`. -/
abbrev principalAngle (z : ℝ × ℝ) : ℝ :=
  Real.arctan (z.2 / z.1)

/-- Helper for Exercise 8.3.3: the canonical full polar angle on `ℝ²`, expressed through
`Complex.arg`. -/
abbrev polarAngle (z : ℝ × ℝ) : ℝ :=
  Complex.arg (Complex.equivRealProd.symm z)

/-- Helper for Exercise 8.3.3: fold a full polar angle back to the textbook principal branch
`[-π / 2, π / 2]` via `tan` and `arctan`. -/
abbrev foldPolarAngle (θ : ℝ) : ℝ :=
  Real.arctan (Real.tan θ)

/-- Helper for Exercise 8.3.3: the canonical polar angle always lies in the principal
`(-π, π]` branch. -/
private theorem polarAngle_mem_Ioc (z : ℝ × ℝ) :
    polarAngle z ∈ Set.Ioc (-Real.pi) Real.pi := by
  -- Proof comment: `polarAngle` is just `Complex.arg` in real-product coordinates, so the
  -- standard range theorem for `Complex.arg` applies directly.
  simpa [polarAngle] using Complex.arg_mem_Ioc (Complex.equivRealProd.symm z)

/-- Helper for Exercise 8.3.3: the textbook principal angle is the folded full polar angle. -/
private theorem principalAngle_eq_foldPolarAngle (z : ℝ × ℝ) :
    principalAngle z = foldPolarAngle (polarAngle z) := by
  -- Route correction: work with the canonical full angle first and postpone the fold to
  -- `principalAngle` to a single rewrite through `Complex.tan_arg`.
  simp [principalAngle, foldPolarAngle, polarAngle, Complex.tan_arg,
    Complex.equivRealProd_symm_apply]

/-- The support of the principal angle on the circle of radius `r` inside the square `[-1,1]^2`.
-/
def squarePrincipalAngleSupport (r : ℝ) : Set ℝ :=
  Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ∩
    {θ | 0 ≤ r ∧ r * |Real.cos θ| ≤ 1 ∧ r * |Real.sin θ| ≤ 1}

/-- Helper for Exercise 8.3.3: the full polar-angle support on the circle of radius `r` inside
the square `[-1,1]^2`. -/
private def squareFullAngleSupport (r : ℝ) : Set ℝ :=
  Set.Ioo (-Real.pi) Real.pi ∩
    {θ | 0 ≤ r ∧ r * |Real.cos θ| ≤ 1 ∧ r * |Real.sin θ| ≤ 1}

/-- Helper for Exercise 8.3.3: the square principal-angle support is a measurable subset of `ℝ`.
-/
private theorem measurableSet_squarePrincipalAngleSupport (r : ℝ) :
    MeasurableSet (squarePrincipalAngleSupport r) := by
  -- Proof comment: each defining inequality is measurable because `sin`, `cos`, absolute value,
  -- and scalar multiplication are measurable maps on `ℝ`.
  have h_nonneg : MeasurableSet {θ : ℝ | 0 ≤ r} := by
    by_cases hr : 0 ≤ r <;> simp [hr]
  have h_cos : MeasurableSet {θ : ℝ | r * |Real.cos θ| ≤ 1} := by
    exact measurableSet_le (by fun_prop) measurable_const
  have h_sin : MeasurableSet {θ : ℝ | r * |Real.sin θ| ≤ 1} := by
    exact measurableSet_le (by fun_prop) measurable_const
  simpa [squarePrincipalAngleSupport, Set.setOf_and] using
    measurableSet_Icc.inter (h_nonneg.inter (h_cos.inter h_sin))

/-- Helper for Exercise 8.3.3: the square full-angle support is a measurable subset of `ℝ`. -/
private theorem measurableSet_squareFullAngleSupport (r : ℝ) :
    MeasurableSet (squareFullAngleSupport r) := by
  -- Proof comment: the full-angle support uses the same measurable inequalities as the principal
  -- branch, but with the open interval `(-π, π)` as angular range.
  have h_nonneg : MeasurableSet {θ : ℝ | 0 ≤ r} := by
    by_cases hr : 0 ≤ r <;> simp [hr]
  have h_cos : MeasurableSet {θ : ℝ | r * |Real.cos θ| ≤ 1} := by
    exact measurableSet_le (by fun_prop) measurable_const
  have h_sin : MeasurableSet {θ : ℝ | r * |Real.sin θ| ≤ 1} := by
    exact measurableSet_le (by fun_prop) measurable_const
  simpa [squareFullAngleSupport, Set.setOf_and] using
    measurableSet_Ioo.inter (h_nonneg.inter (h_cos.inter h_sin))

/-- Helper for Exercise 8.3.3: the polar chart inverse preserves the radius as the first
coordinate on the target. -/
private theorem planarRadius_polarCoord_symm (p : ℝ × ℝ) :
    planarRadius (polarCoord.symm p) = |p.1| := by
  -- Proof comment: expanding `(r cos θ, r sin θ)` leaves exactly `sqrt (r^2)` after the
  -- Pythagorean identity.
  change Real.sqrt ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) = |p.1|
  have hsq :
      (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    calc
      (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2
          = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = p.1 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [hsq, Real.sqrt_sq_eq_abs]

/-- Helper for Exercise 8.3.3: on the polar target, the radius returned by `polarCoord.symm`
is exactly the first coordinate. -/
private theorem planarRadius_polarCoord_symm_of_mem_target {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    planarRadius (polarCoord.symm p) = p.1 := by
  -- Proof comment: the target condition `0 < r` lets us remove the absolute value from the
  -- generic radius formula.
  rw [planarRadius_polarCoord_symm, abs_of_pos hp.1]

/-- Helper for Exercise 8.3.3: on the polar target, the full polar angle returned by
`polarCoord.symm` is exactly the second coordinate. -/
private theorem polarAngle_polarCoord_symm {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    polarAngle (polarCoord.symm p) = p.2 := by
  -- Proof comment: this is the right-inverse property of the polar chart, read on the angular
  -- component.
  simpa [polarAngle] using congrArg Prod.snd (polarCoord.right_inv hp)

/-- Helper for Exercise 8.3.3: on the polar target, the textbook principal angle of
`polarCoord.symm p` is obtained by folding the second coordinate. -/
private theorem principalAngle_polarCoord_symm {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    principalAngle (polarCoord.symm p) = foldPolarAngle p.2 := by
  -- Proof comment: first rewrite to the full polar angle, then use the right-inverse formula for
  -- the polar chart.
  rw [principalAngle_eq_foldPolarAngle, polarAngle_polarCoord_symm hp]

/-- Helper for Exercise 8.3.3: on the polar target, lying in the closed unit disc is equivalent to
the radial bound `r ≤ 1`. -/
private theorem mem_closedUnitDisc_polarCoord_symm_iff {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ closedUnitDisc ↔ p.1 ≤ 1 := by
  -- Proof comment: on polar coordinates, the disc inequality becomes `r^2 ≤ 1`, and the target
  -- condition `r > 0` turns this into the linear bound `r ≤ 1`.
  change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 ≤ 1 ↔ p.1 ≤ 1
  have hsq :
      (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    calc
      (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2
          = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = p.1 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [hsq]
  constructor
  · intro hp_sq
    nlinarith [hp.1]
  · intro hp_le
    have hp_nonneg : 0 ≤ p.1 := le_of_lt hp.1
    nlinarith [hp_nonneg, hp_le]

/-- Helper for Exercise 8.3.3: on the polar target, lying in the square `[-1,1]^2` is equivalent
to the explicit full-angle support condition. -/
private theorem mem_unitSquare_polarCoord_symm_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ unitSquare ↔ p.2 ∈ squareFullAngleSupport p.1 := by
  -- Proof comment: the target already enforces `r > 0` and `θ ∈ (-π, π)`, so square membership is
  -- exactly the pair of coordinate bounds `|r cos θ| ≤ 1` and `|r sin θ| ≤ 1`.
  constructor
  · intro hz
    rcases hz with ⟨hx, hy⟩
    refine ⟨hp.2, ?_⟩
    have hcos_abs : |p.1 * Real.cos p.2| ≤ 1 := by
      rw [abs_le]
      exact hx
    have hsin_abs : |p.1 * Real.sin p.2| ≤ 1 := by
      rw [abs_le]
      exact hy
    rw [abs_mul, abs_of_pos hp.1] at hcos_abs hsin_abs
    exact ⟨le_of_lt hp.1, hcos_abs, hsin_abs⟩
  · intro hz
    rcases hz with ⟨hθ, hr, hcos, hsin⟩
    have hcos_abs : |p.1 * Real.cos p.2| ≤ 1 := by
      simpa [abs_mul, abs_of_nonneg hr] using hcos
    have hsin_abs : |p.1 * Real.sin p.2| ≤ 1 := by
      simpa [abs_mul, abs_of_nonneg hr] using hsin
    refine ⟨?_, ?_⟩
    · rw [abs_le] at hcos_abs
      exact hcos_abs
    · rw [abs_le] at hsin_abs
      exact hsin_abs

/-- Helper for Exercise 8.3.3: for a fixed abscissa inside the unit disc, membership in the
vertical chord is equivalent to the disc inequality. -/
private theorem mem_discVerticalSegment_iff {x y : ℝ} (hx : x ^ 2 ≤ 1) :
    y ∈ Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)) ↔ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnonneg : 0 ≤ 1 - x ^ 2 := by
    linarith
  constructor
  · intro hy
    rcases hy with ⟨hy_lower, hy_upper⟩
    have h_abs : |y| ≤ Real.sqrt (1 - x ^ 2) := by
      rw [abs_le]
      constructor <;> linarith
    have hy_sq : y ^ 2 ≤ 1 - x ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (1 - x ^ 2) - |y|), Real.sq_sqrt hnonneg]
    linarith
  · intro hxy
    have hy_sq : y ^ 2 ≤ 1 - x ^ 2 := by
      linarith
    have h_abs : |y| ≤ Real.sqrt (1 - x ^ 2) := by
      exact Real.abs_le_sqrt hy_sq
    rw [abs_le] at h_abs
    exact ⟨by linarith, by linarith⟩

/-- Helper for Exercise 8.3.3: the unit-disc law is described by a constant ambient density on
`ℝ²`, supported on the closed unit disc. -/
private abbrev discDensity (z : ℝ × ℝ) : ENNReal :=
  Set.indicator closedUnitDisc (fun _ ↦ (volume closedUnitDisc)⁻¹) z

/-- Helper for Exercise 8.3.3: the square law is described by a constant ambient density on `ℝ²`,
supported on `[-1,1]^2`. -/
private abbrev squareDensity (z : ℝ × ℝ) : ENNReal :=
  Set.indicator unitSquare (fun _ ↦ (volume unitSquare)⁻¹) z

/-- Helper for Exercise 8.3.3: the first marginal of the unit-disc density is proportional to the
length of the vertical chord over `x`. -/
private abbrev discChordDensity (x : ℝ) : ENNReal :=
  (volume closedUnitDisc)⁻¹ * ENNReal.ofReal (2 * Real.sqrt (1 - x ^ 2))

/-- Helper for Exercise 8.3.3: dividing the joint disc density by the chord density gives the
candidate conditional density of the second coordinate over Lebesgue measure. -/
private abbrev discConditionalDensity (x y : ℝ) : ENNReal :=
  discDensity (x, y) / discChordDensity x

/-- Helper for Exercise 8.3.3: the ambient disc density is measurable on `ℝ²`. -/
private theorem measurable_discDensity : Measurable discDensity := by
  -- Proof comment: the density is a constant function cut down by the measurable disc indicator.
  exact measurable_const.indicator measurableSet_closedUnitDisc

/-- Helper for Exercise 8.3.3: the ambient square density is measurable on `ℝ²`. -/
private theorem measurable_squareDensity : Measurable squareDensity := by
  -- Proof comment: the square density is the same indicator construction over the measurable
  -- square support.
  exact measurable_const.indicator measurableSet_unitSquare

/-- Helper for Exercise 8.3.3: the chord density is measurable in the abscissa. -/
private theorem measurable_discChordDensity : Measurable discChordDensity := by
  -- Proof comment: the chord length is built from measurable polynomial and square-root maps.
  fun_prop

/-- Helper for Exercise 8.3.3: the conditional density candidate is measurable on `ℝ²`. -/
private theorem measurable_discConditionalDensity :
    Measurable (Function.uncurry discConditionalDensity) := by
  -- Proof comment: after uncurrying, the candidate density is just the measurable ambient density
  -- divided by the measurable chord-density pulled back along the first projection.
  change Measurable (fun z : ℝ × ℝ ↦ discDensity z / discChordDensity z.1)
  refine Measurable.div measurable_discDensity ?_
  exact measurable_discChordDensity.comp measurable_fst

/-- Helper for Exercise 8.3.3: the chord density is finite everywhere. -/
private theorem discChordDensity_ne_top (x : ℝ) : discChordDensity x ≠ ⊤ := by
  -- Proof comment: the normalizing constant is the inverse of a positive finite area, and the
  -- explicit chord length is an `ofReal`, so both factors are finite.
  rw [discChordDensity, ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 volume_closedUnitDisc_pos.ne')
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Helper for Exercise 8.3.3: the chord density vanishes exactly on the boundary and exterior
abscissae `|x| ≥ 1`. -/
private theorem discChordDensity_ne_zero_iff {x : ℝ} :
    discChordDensity x ≠ 0 ↔ x ^ 2 < 1 := by
  constructor
  · intro hx
    -- Proof comment: if `x² ≥ 1`, the square root term vanishes and so does the whole chord
    -- density, contradicting the hypothesis.
    by_contra hx_lt
    have hsqrt_zero : Real.sqrt (1 - x ^ 2) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      linarith
    apply hx
    rw [discChordDensity, hsqrt_zero]
    simp
  · intro hx
    -- Proof comment: inside the open interval `(-1, 1)`, the chord length is strictly positive,
    -- and multiplying by the nonzero normalizing constant keeps it nonzero.
    rw [discChordDensity]
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.inv_ne_zero.2 volume_closedUnitDisc_ne_top
    · refine ENNReal.ofReal_ne_zero_iff.2 ?_
      have hsqrt_pos : 0 < Real.sqrt (1 - x ^ 2) := by
        refine Real.sqrt_pos.2 ?_
        linarith
      nlinarith

/-- Helper for Exercise 8.3.3: for `x² ≤ 1`, the vertical fiber of the disc density is the
constant density `(volume closedUnitDisc)⁻¹` on the chord
`[-sqrt (1 - x^2), sqrt (1 - x^2)]`. -/
private theorem discDensity_fiber_eq_indicator_verticalSegment (x y : ℝ) (hx : x ^ 2 ≤ 1) :
    discDensity (x, y) =
      (volume closedUnitDisc)⁻¹ *
        Set.indicator (Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)))
          (fun _ ↦ (1 : ENNReal)) y := by
  -- Proof comment: once `x² ≤ 1` is fixed, disc membership is exactly membership in the vertical
  -- chord over `x`, so the fiber density becomes a constant times an interval indicator.
  by_cases hxy : (x, y) ∈ closedUnitDisc
  · have hy : y ∈ Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)) :=
      (mem_discVerticalSegment_iff hx).2 (by simpa [closedUnitDisc] using hxy)
    simp [discDensity, hxy, hy, mul_one]
  · have hy : y ∉ Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)) := by
      intro hy
      apply hxy
      exact (mem_discVerticalSegment_iff hx).1 hy
    simp [discDensity, hxy, hy]

/-- Helper for Exercise 8.3.3: integrating the ambient disc density over a vertical fiber gives
the explicit chord-length density in `x`. -/
private theorem discChordDensity_eval (x : ℝ) :
    ∫⁻ y, discDensity (x, y) ∂(volume : Measure ℝ) = discChordDensity x := by
  by_cases hx : x ^ 2 ≤ 1
  · let s : Set ℝ := Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))
    have hs : MeasurableSet s := measurableSet_Icc
    -- Proof comment: on interior abscissae, rewrite the fiber as a constant indicator on the
    -- vertical chord and evaluate the chord length by `Real.volume_Icc`.
    calc
      ∫⁻ y, discDensity (x, y) ∂(volume : Measure ℝ)
          = ∫⁻ y, (volume closedUnitDisc)⁻¹ * Set.indicator s (fun _ ↦ (1 : ENNReal)) y
              ∂(volume : Measure ℝ) := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              simpa [s] using discDensity_fiber_eq_indicator_verticalSegment x y hx
      _ = (volume closedUnitDisc)⁻¹ *
            ∫⁻ y, Set.indicator s (fun _ ↦ (1 : ENNReal)) y ∂(volume : Measure ℝ) := by
            rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 volume_closedUnitDisc_pos.ne')]
      _ = (volume closedUnitDisc)⁻¹ * volume s := by
            rw [lintegral_indicator_const hs, one_mul]
      _ = discChordDensity x := by
            rw [discChordDensity, Real.volume_Icc]
            congr 1
            rw [sub_eq_add_neg]
            ring
  · have hdisc : ∀ y : ℝ, discDensity (x, y) = 0 := by
      intro y
      have hxy : ¬ (x, y) ∈ closedUnitDisc := by
        intro hxy
        have hxy_le : x ^ 2 + y ^ 2 ≤ 1 := by
          simpa [closedUnitDisc] using hxy
        have hx_le : x ^ 2 ≤ 1 := by
          linarith [sq_nonneg y]
        exact hx hx_le
      simp [discDensity, hxy]
    -- Proof comment: outside the disc projection, every vertical fiber is empty, so both the
    -- fiber integral and the explicit chord density collapse to zero.
    calc
      ∫⁻ y, discDensity (x, y) ∂(volume : Measure ℝ)
          = ∫⁻ y, (0 : ENNReal) ∂(volume : Measure ℝ) := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              exact hdisc y
      _ = 0 := by simp
      _ = discChordDensity x := by
            have hsqrt_zero : Real.sqrt (1 - x ^ 2) = 0 := by
              apply Real.sqrt_eq_zero_of_nonpos
              linarith
            simp [discChordDensity, hsqrt_zero]

/-- Helper for Exercise 8.3.3: pushing a product-space density forward along `Prod.fst` integrates
out the second coordinate. -/
private theorem mapFstWithDensityEqWithDensityFiberIntegral {f : ℝ × ℝ → ENNReal}
    (hf : Measurable f) :
    Measure.map Prod.fst ((volume : Measure (ℝ × ℝ)).withDensity f) =
      (volume : Measure ℝ).withDensity (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure ℝ)) := by
  refine Measure.ext fun s hs ↦ ?_
  let g : ℝ × ℝ → ENNReal := Set.indicator (Prod.fst ⁻¹' s) f
  have hg : Measurable g := hf.indicator (hs.preimage measurable_fst)
  have hinner :
      (fun x ↦ ∫⁻ y, g (x, y) ∂(volume : Measure ℝ)) =
        Set.indicator s (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure ℝ)) := by
    -- Proof comment: after fixing `x`, the indicator either keeps the whole vertical fiber
    -- (`x ∈ s`) or kills it completely (`x ∉ s`).
    funext x
    by_cases hx : x ∈ s
    · simp [g, hx]
    · simp [g, hx]
  -- Proof comment: evaluate both measures on a measurable set, rewrite the preimage
  -- `Prod.fst ⁻¹' s`, and apply Tonelli to integrate first in the vertical variable.
  calc
    Measure.map Prod.fst ((volume : Measure (ℝ × ℝ)).withDensity f) s
        = ((volume : Measure (ℝ × ℝ)).withDensity f) (Prod.fst ⁻¹' s) := by
            rw [Measure.map_apply measurable_fst hs]
    _ = ∫⁻ z in Prod.fst ⁻¹' s, f z ∂(volume : Measure (ℝ × ℝ)) := by
          rw [withDensity_apply _ (hs.preimage measurable_fst)]
    _ = ∫⁻ z, g z ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
          rw [Measure.volume_eq_prod, lintegral_indicator (hs.preimage measurable_fst)]
    _ = ∫⁻ x, ∫⁻ y, g (x, y) ∂(volume : Measure ℝ) ∂(volume : Measure ℝ) := by
          rw [lintegral_prod _ hg.aemeasurable]
    _ = ∫⁻ x, Set.indicator s (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure ℝ)) x
          ∂(volume : Measure ℝ) := by
          simpa [hinner]
    _ = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂(volume : Measure ℝ) ∂(volume : Measure ℝ) := by
          rw [lintegral_indicator hs]
    _ = (volume : Measure ℝ).withDensity (fun x ↦ ∫⁻ y, f (x, y) ∂(volume : Measure ℝ)) s := by
          rw [withDensity_apply _ hs]

/-- Helper for Exercise 8.3.3: the first marginal of the unit-disc law is Lebesgue measure with
the explicit chord-length density. -/
private theorem unitDiscFst_eq_withDensity_discChordDensity :
    unitDiscUniformMeasure.map Prod.fst = (volume : Measure ℝ).withDensity discChordDensity := by
  -- Proof comment: first rewrite the unit-disc law as an ambient density on `ℝ²`, then push that
  -- density forward along `Prod.fst` using the generic fiber-integral lemma.
  calc
    unitDiscUniformMeasure.map Prod.fst
        = Measure.map Prod.fst ((volume : Measure (ℝ × ℝ)).withDensity discDensity) := by
            rw [unitDiscUniformMeasure_eq_withDensity_indicator]
    _ = (volume : Measure ℝ).withDensity (fun x ↦ ∫⁻ y, discDensity (x, y) ∂(volume : Measure ℝ)) := by
          exact mapFstWithDensityEqWithDensityFiberIntegral measurable_discDensity
    _ = (volume : Measure ℝ).withDensity discChordDensity := by
          congr 1
          funext x
          exact discChordDensity_eval x

/-- Helper for Exercise 8.3.3: if the ambient disc density is positive at `(x, y)` but the chord
density vanishes, then `(x, y)` must be one of the two boundary points with `|x| = 1`. -/
private theorem eq_boundary_of_disc_mem_and_chordDensity_zero {x y : ℝ}
    (hxy : (x, y) ∈ closedUnitDisc) (hzero : discChordDensity x = 0) :
    (x, y) = (-1, 0) ∨ (x, y) = (1, 0) := by
  -- Proof comment: a zero chord density means the vertical slice has collapsed, so `x² = 1`; the
  -- disc constraint then forces `y = 0`, leaving only the two horizontal boundary points.
  have hx_ge : 1 ≤ x ^ 2 := by
    by_contra hx_lt
    exact (discChordDensity_ne_zero_iff.2 <| by linarith) hzero
  have hxy_le : x ^ 2 + y ^ 2 ≤ 1 := by
    simpa [closedUnitDisc] using hxy
  have hy_sq_zero : y ^ 2 = 0 := by
    have hy_sq_le : y ^ 2 ≤ 0 := by linarith
    exact le_antisymm hy_sq_le (sq_nonneg y)
  have hy_zero : y = 0 := by
    nlinarith
  have hx_sq : x ^ 2 = 1 := by
    nlinarith
  have hx_eq : x = -1 ∨ x = 1 := by
    have hx_sq' : x ^ 2 = (-1 : ℝ) ^ 2 := by simpa using hx_sq
    simpa using sq_eq_sq_iff_eq_or_eq_neg.mp hx_sq'
  rcases hx_eq with rfl | rfl
  · left
    simp [hy_zero]
  · right
    simp [hy_zero]

/-- Helper for Exercise 8.3.3: away from the two boundary points `(-1,0)` and `(1,0)`, the
conditional-density factorization `joint = marginal * fiber` is pointwise valid. -/
private theorem discDensity_factor_ae :
    discDensity =ᵐ[((volume : Measure ℝ).prod (volume : Measure ℝ))]
      fun z : ℝ × ℝ ↦ discChordDensity z.1 * discConditionalDensity z.1 z.2 := by
  -- Proof comment: the factorization can only fail when the denominator `discChordDensity z.1`
  -- vanishes while the joint density stays positive; the previous boundary lemma shows this
  -- happens only at the two endpoints `(-1, 0)` and `(1, 0)`.
  let bad : Set (ℝ × ℝ) := {(-1, 0), (1, 0)}
  rw [aeEq_iff]
  have hsubset :
      {z | discDensity z ≠ discChordDensity z.1 * discConditionalDensity z.1 z.2} ⊆ bad := by
    intro z hz
    by_cases hzDisc : z ∈ closedUnitDisc
    · by_cases hzChord : discChordDensity z.1 = 0
      · rcases eq_boundary_of_disc_mem_and_chordDensity_zero hzDisc hzChord with hzBoundary | hzBoundary
        · left
          simpa using hzBoundary
        · right
          simpa using hzBoundary
      · exfalso
        apply hz
        symm
        simpa [discConditionalDensity] using
          (ENNReal.mul_div_cancel hzChord (discChordDensity_ne_top z.1))
    · exfalso
      apply hz
      simp [discConditionalDensity, discDensity, hzDisc]
  have hnull : ((volume : Measure ℝ).prod (volume : Measure ℝ)) bad = 0 := by
    have hbad :
        bad = ({(-1, 0)} : Set (ℝ × ℝ)) ∪ {(1, 0)} := by
          ext z
          simp [bad, or_comm]
    rw [hbad, measure_union]
    · simp
    · exact Set.disjoint_singleton_right.2 <| by
        intro h
        have : (1 : ℝ) = -1 := by
          simpa using congrArg Prod.fst h
        norm_num at this
    · exact measurableSet_singleton (1, 0)
  exact measure_mono_null hsubset hnull

/-- Helper for Exercise 8.3.3: on abscissae where the chord density is positive, the
`withDensity` kernel coincides with the normalized Lebesgue measure on the vertical chord. -/
private theorem discVerticalKernel_eq_uniformSegment {x : ℝ} (hx : discChordDensity x ≠ 0) :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity x =
      volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := by
  let s : Set ℝ := Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))
  have hs : MeasurableSet s := measurableSet_Icc
  have hx_lt : x ^ 2 < 1 := (discChordDensity_ne_zero_iff).1 hx
  have hx_le : x ^ 2 ≤ 1 := le_of_lt hx_lt
  have hsVolume :
      volume s = ENNReal.ofReal (2 * Real.sqrt (1 - x ^ 2)) := by
    -- Proof comment: the chord interval has the expected Euclidean length `2 * sqrt (1 - x²)`.
    dsimp [s]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hrowDensity :
      discConditionalDensity x = fun y ↦ Set.indicator s (fun _ ↦ (volume s)⁻¹) y := by
    -- Proof comment: inside the nondegenerate chord, the ambient disc density is constant, so
    -- dividing by the chord-length marginal leaves the normalized interval indicator.
    funext y
    calc
      discConditionalDensity x y
          = ((volume closedUnitDisc)⁻¹ *
              Set.indicator s (fun _ ↦ (1 : ENNReal)) y) / discChordDensity x := by
              rw [discConditionalDensity,
                discDensity_fiber_eq_indicator_verticalSegment x y hx_le]
      _ = ((volume closedUnitDisc)⁻¹ *
            Set.indicator s (fun _ ↦ (1 : ENNReal)) y) /
            ((volume closedUnitDisc)⁻¹ * volume s) := by
            rw [discChordDensity, hsVolume]
      _ = Set.indicator s (fun _ ↦ (1 : ENNReal)) y / volume s := by
            rw [ENNReal.mul_div_mul_left _ _
              (ENNReal.inv_ne_zero.2 volume_closedUnitDisc_ne_top)
              (ENNReal.inv_ne_top.2 volume_closedUnitDisc_pos.ne')]
      _ = Set.indicator s (fun _ ↦ (volume s)⁻¹) y := by
            by_cases hy : y ∈ s
            · simp [hy]
            · simp [hy]
  -- Proof comment: once the row density is normalized on the interval `s`, the kernel row is
  -- exactly the conditioned Lebesgue measure on `s`.
  calc
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity x
        = (volume : Measure ℝ).withDensity (discConditionalDensity x) := by
            rw [Kernel.withDensity_apply _ measurable_discConditionalDensity, Kernel.const_apply]
    _ = (volume : Measure ℝ).withDensity (Set.indicator s fun _ ↦ (volume s)⁻¹) := by
          rw [hrowDensity]
    _ = (volume.restrict s).withDensity (fun _ ↦ (volume s)⁻¹) := by
          rw [withDensity_indicator hs]
    _ = (volume.restrict s).withDensity ((volume s)⁻¹ • (1 : ℝ → ENNReal)) := by
          congr 1
          funext y
          simp
    _ = (volume s)⁻¹ • volume.restrict s := by
          rw [withDensity_smul _ measurable_one, withDensity_one]
    _ = volume[|s] := by
          rw [ProbabilityTheory.cond]
    _ = volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := by
          simp [s]

/-- Helper for Exercise 8.3.3: when the chord density vanishes, the conditional row density is
zero almost everywhere for Lebesgue measure. -/
private theorem discConditionalDensity_ae_zero_of_chordDensity_zero {x : ℝ}
    (hx : discChordDensity x = 0) :
    discConditionalDensity x =ᵐ[(volume : Measure ℝ)] 0 := by
  -- Proof comment: if the row density were nonzero, then the ambient disc density would also be
  -- nonzero, forcing the point onto one of the two boundary atoms `(-1, 0)` or `(1, 0)`.
  rw [Filter.EventuallyEq, ae_iff]
  change (volume : Measure ℝ) {y | discConditionalDensity x y ≠ 0} = 0
  have hsubset : {y | discConditionalDensity x y ≠ 0} ⊆ ({0} : Set ℝ) := by
    intro y hy
    have hdisc_ne_zero : discDensity (x, y) ≠ 0 := by
      intro hdisc_zero
      have hrow_zero : discConditionalDensity x y = 0 := by
        simp [discConditionalDensity, hdisc_zero, hx]
      exact hy hrow_zero
    have hxy : (x, y) ∈ closedUnitDisc := by
      by_contra hxy
      apply hdisc_ne_zero
      simp [discDensity, hxy]
    rcases eq_boundary_of_disc_mem_and_chordDensity_zero hxy hx with hboundary | hboundary
    · simpa using congrArg Prod.snd hboundary
    · simpa using congrArg Prod.snd hboundary
  have hnull : (volume : Measure ℝ) ({0} : Set ℝ) = 0 := by
    simpa using (measure_singleton (0 : ℝ) : (volume : Measure ℝ) ({0} : Set ℝ) = 0)
  exact measure_mono_null hsubset hnull

/-- Helper for Exercise 8.3.3: when the chord density vanishes, the corresponding vertical kernel
row is the zero measure. -/
private theorem discVerticalKernel_eq_zero_of_chordDensity_zero {x : ℝ}
    (hx : discChordDensity x = 0) :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity x = 0 := by
  -- Proof comment: rewrite the row as a measure `withDensity`, then collapse it with the
  -- almost-everywhere zero density from the previous lemma.
  calc
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity x
        = (volume : Measure ℝ).withDensity (discConditionalDensity x) := by
            rw [Kernel.withDensity_apply _ measurable_discConditionalDensity, Kernel.const_apply]
    _ = (volume : Measure ℝ).withDensity 0 := by
          exact MeasureTheory.withDensity_congr_ae
            (discConditionalDensity_ae_zero_of_chordDensity_zero hx)
    _ = 0 := by rw [MeasureTheory.withDensity_zero]

/-- Helper for Exercise 8.3.3: the explicit vertical kernel built from
`discConditionalDensity` is finite. -/
private theorem discVerticalKernel_isFinite :
    IsFiniteKernel
      (Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity) := by
  -- Proof comment: each row is either the zero measure or a conditioned interval measure, so the
  -- total mass is uniformly bounded by `1`.
  refine ⟨1, by simp, ?_⟩
  intro x
  by_cases hx : discChordDensity x = 0
  · -- Proof comment: zero chord density collapses the entire row to the zero measure.
    rw [discVerticalKernel_eq_zero_of_chordDensity_zero hx]
    simp
  · -- Proof comment: otherwise the row is a probability measure on the vertical chord.
    rw [discVerticalKernel_eq_uniformSegment hx]
    have hprob :
        volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] Set.univ ≤ 1 := prob_le_one
    simpa using hprob

/-- Helper for Exercise 8.3.3: after factorizing the disc density into its first marginal and
fiber densities, the ambient `withDensity` becomes a product-with-density measure. -/
private theorem discJointWithDensity_eq_prodWithDensity :
    (volume : Measure (ℝ × ℝ)).withDensity
        (fun z : ℝ × ℝ ↦ discChordDensity z.1 * discConditionalDensity z.1 z.2) =
      ((((volume : Measure ℝ).withDensity discChordDensity).prod (volume : Measure ℝ))).withDensity
        (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) := by
  -- Proof comment: first split the product density into two successive `withDensity` steps, then
  -- rewrite the first step as a density on the left marginal of the product measure.
  calc
    (volume : Measure (ℝ × ℝ)).withDensity
        (fun z : ℝ × ℝ ↦ discChordDensity z.1 * discConditionalDensity z.1 z.2)
      = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          (fun z : ℝ × ℝ ↦ discChordDensity z.1 * discConditionalDensity z.1 z.2)) := by
            rw [Measure.volume_eq_prod]
    _ = ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
            fun z : ℝ × ℝ ↦ discChordDensity z.1)).withDensity
          (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) := by
            simpa using
              (MeasureTheory.withDensity_mul
                ((volume : Measure ℝ).prod (volume : Measure ℝ))
                (by simpa using measurable_discChordDensity.comp measurable_fst)
                measurable_discConditionalDensity)
    _ = ((((volume : Measure ℝ).withDensity discChordDensity).prod (volume : Measure ℝ))).withDensity
          (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) := by
            rw [← MeasureTheory.prod_withDensity_left measurable_discChordDensity]

/-- Helper for Exercise 8.3.3: the product-with-density form of the disc law is the compProd of
the first marginal with the explicit vertical kernel. -/
private theorem prodWithDensity_eq_compProd_discVerticalKernel :
    ((((volume : Measure ℝ).withDensity discChordDensity).prod (volume : Measure ℝ))).withDensity
        (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) =
      ((volume : Measure ℝ).withDensity discChordDensity) ⊗ₘ
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
  haveI :
      IsFiniteKernel
        (Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity) :=
    discVerticalKernel_isFinite
  -- Proof comment: rewrite the product as the compProd with the constant kernel, then push the
  -- row density into that kernel via `Measure.compProd_withDensity`.
  calc
    ((((volume : Measure ℝ).withDensity discChordDensity).prod (volume : Measure ℝ))).withDensity
        (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2)
      = ((((volume : Measure ℝ).withDensity discChordDensity) ⊗ₘ
            Kernel.const ℝ (volume : Measure ℝ))).withDensity
          (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) := by
            rw [← Measure.compProd_const]
    _ = ((volume : Measure ℝ).withDensity discChordDensity) ⊗ₘ
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
            rw [← Measure.compProd_withDensity measurable_discConditionalDensity]

/-- Helper for Exercise 8.3.3: the unit-disc law factors as the first marginal composed with the
explicit vertical conditional kernel built from `discConditionalDensity`. -/
private theorem unitDisc_eq_compProd_discVerticalKernel :
    unitDiscUniformMeasure =
      unitDiscUniformMeasure.map Prod.fst ⊗ₘ
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
  -- Route correction: instead of crossing all normalization boundaries in one `rw` chain, move
  -- through the ambient-density, product-with-density, and compProd forms in separate lemmas.
  calc
    unitDiscUniformMeasure
      = (volume : Measure (ℝ × ℝ)).withDensity discDensity := by
          rw [unitDiscUniformMeasure_eq_withDensity_indicator]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (fun z : ℝ × ℝ ↦ discChordDensity z.1 * discConditionalDensity z.1 z.2) := by
          simpa [Measure.volume_eq_prod] using
            (MeasureTheory.withDensity_congr_ae discDensity_factor_ae)
    _ = ((((volume : Measure ℝ).withDensity discChordDensity).prod (volume : Measure ℝ))).withDensity
          (fun z : ℝ × ℝ ↦ discConditionalDensity z.1 z.2) := by
          exact discJointWithDensity_eq_prodWithDensity
    _ = ((volume : Measure ℝ).withDensity discChordDensity) ⊗ₘ
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
          exact prodWithDensity_eq_compProd_discVerticalKernel
    _ = unitDiscUniformMeasure.map Prod.fst ⊗ₘ
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
          rw [← unitDiscFst_eq_withDensity_discChordDensity]

/-- Helper for Exercise 8.3.3: under the first marginal of the unit-disc law, the explicit
vertical kernel agrees almost everywhere with the normalized chord measure. -/
private theorem ae_discVerticalKernel_eq_uniformSegment :
    ∀ᵐ x ∂(unitDiscUniformMeasure.map Prod.fst),
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity x =
        volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := by
  -- Proof comment: the first marginal is `volume.withDensity discChordDensity`, so almost every
  -- abscissa has positive chord density and the explicit row formula applies there.
  rw [unitDiscFst_eq_withDensity_discChordDensity, ae_withDensity_iff measurable_discChordDensity]
  filter_upwards with x hx
  exact discVerticalKernel_eq_uniformSegment hx

/-- Helper for Exercise 8.3.3: the identity pair map under the unit-disc law has the ambient disc
joint density used by `Example_8_31`. -/
private theorem unitDiscPair_hasLaw_discJointDensity :
    HasLaw (fun z : ℝ × ℝ ↦ (z.1, z.2))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ discDensity (z.1, z.2))
      unitDiscUniformMeasure := by
  -- Proof comment: the pair map is the identity on `ℝ × ℝ`, so the law statement is exactly the
  -- ambient-density description of `unitDiscUniformMeasure`.
  refine ⟨by fun_prop, ?_⟩
  simpa [Measure.volume_eq_prod, discDensity] using
    unitDiscUniformMeasure_eq_withDensity_indicator

/-- Helper for Exercise 8.3.3: the generic first marginal density from `Example_8_31` matches the
explicit disc chord density. -/
private theorem discFirstMarginalDensity_eq_discChordDensity :
    first_marginal_density (fun x y ↦ discDensity (x, y)) = discChordDensity := by
  -- Proof comment: the earlier generic marginal-density integral is exactly the vertical-fiber
  -- computation already recorded in `discChordDensity_eval`.
  funext x
  simpa [first_marginal_density] using discChordDensity_eval x

/-- Helper for Exercise 8.3.3: the density-ratio kernel from `Example_8_31` is the local vertical
disc kernel written with `discConditionalDensity`. -/
private theorem discDensityRatioKernel_eq_discVerticalKernel :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun x y ↦ discDensity (x, y) /
        first_marginal_density (fun x y ↦ discDensity (x, y)) x) =
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity := by
  -- Proof comment: rewrite the imported marginal-density spelling to the local chord density; the
  -- remaining density is definitionally `discConditionalDensity`.
  rw [discFirstMarginalDensity_eq_discChordDensity]

/-- Helper for Exercise 8.3.3: the uniform law on `[-1,1]^2` factors as the product of the two
uniform interval laws on `[-1,1]`. -/
private theorem unitSquareUniformMeasure_eq_prodUniformInterval :
    unitSquareUniformMeasure =
      (volume[|Set.Icc (-1 : ℝ) 1]).prod (volume[|Set.Icc (-1 : ℝ) 1]) := by
  let I : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hI : MeasurableSet I := measurableSet_Icc
  have hvolI : volume I = 2 := by
    norm_num [I, Real.volume_Icc]
  have hcoeff :
      (((2 : ENNReal) * 2)⁻¹) = (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
    calc
      (((2 : ENNReal) * 2)⁻¹) = (((2 : ENNReal) ^ 2)⁻¹) := by simp [pow_two]
      _ = ((2 : ENNReal)⁻¹) ^ 2 := ENNReal.inv_pow
      _ = (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by simp [pow_two]
  -- Compare the two measures on measurable rectangles, where both sides are explicit.
  refine Measure.ext_prod ?_
  intro s t hs ht
  rw [unitSquareUniformMeasure, ProbabilityTheory.cond_apply' (hs.prod ht), unitSquare,
    Set.prod_inter_prod, Measure.volume_eq_prod, Measure.prod_prod]
  rw [show ((volume[|I]).prod (volume[|I])) (s ×ˢ t) = (volume[|I]) s * (volume[|I]) t by
        exact Measure.prod_prod s t]
  rw [ProbabilityTheory.cond_apply' hs, ProbabilityTheory.cond_apply' ht]
  -- Both expressions reduce to the same normalized rectangle volume inside `[-1,1]^2`.
  rw [Measure.prod_prod, hvolI, hcoeff]
  simpa [I, mul_assoc, mul_left_comm, mul_comm]

-- Proof sketch: view the unit-disc law as a constant density on the disc and apply the density
-- formula for regular conditional distributions. The marginal in `x` is proportional to the length
-- of the vertical chord, so the fiber law is the normalized Lebesgue measure on that chord.
/-- For Exercise 8.3.3 (1): for the uniform law on the unit disc, the conditional
distribution of `Y` given `X = x` is the uniform law on
`[-sqrt (1 - x^2), sqrt (1 - x^2)]` for `P.map X`-almost every `x`. -/
theorem condDistrib_snd_given_fst_unitDisc_ae_eq_uniform_segment :
    ∀ᵐ x ∂(unitDiscUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitDiscUniformMeasure x =
        volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := by
  let κ : Kernel ℝ ℝ :=
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) discConditionalDensity
  letI : IsFiniteKernel κ := by
    simpa [κ] using discVerticalKernel_isFinite
  have hpair :
      unitDiscUniformMeasure.map (fun z : ℝ × ℝ ↦ (z.1, z.2)) =
        unitDiscUniformMeasure.map Prod.fst ⊗ₘ κ := by
    -- Proof comment: package the already-proved compProd factorization with the identity pair map.
    calc
      unitDiscUniformMeasure.map (fun z : ℝ × ℝ ↦ (z.1, z.2))
          = unitDiscUniformMeasure := by simp
      _ = unitDiscUniformMeasure.map Prod.fst ⊗ₘ κ := by
            simpa [κ] using unitDisc_eq_compProd_discVerticalKernel
  have hcond :
      condDistrib Prod.snd Prod.fst unitDiscUniformMeasure =ᵐ[unitDiscUniformMeasure.map Prod.fst]
        κ :=
    condDistrib_ae_eq_of_measure_eq_compProd Prod.fst (by fun_prop) hpair
  -- Proof comment: combine uniqueness of the conditional kernel with the explicit row formula for
  -- the vertical kernel.
  filter_upwards [hcond, ae_discVerticalKernel_eq_uniformSegment] with x hx hrow
  exact hx.trans hrow

-- Proof sketch: identify the uniform law on `[-1,1]^2` with the product of the two uniform laws
-- on `[-1,1]` and use the a.e.-uniqueness of `condDistrib` for a product decomposition.
/-- For Exercise 8.3.3 (2): for the uniform law on `[-1,1]^2`, the conditional
distribution of `Y` given `X = x` is the uniform law on `[-1,1]` for `P.map X`-almost every
`x`. -/
theorem condDistrib_snd_given_fst_unitSquare_ae_eq_uniform_interval :
    ∀ᵐ x ∂(unitSquareUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitSquareUniformMeasure x =
        volume[|Set.Icc (-1 : ℝ) 1] := by
  let ν : Measure ℝ := volume[|Set.Icc (-1 : ℝ) 1]
  have hprobν : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact cond_isProbabilityMeasure_of_finite
      (by norm_num [Real.volume_Icc])
      (by norm_num [Real.volume_Icc])
  letI : IsProbabilityMeasure ν := hprobν
  have hsq : unitSquareUniformMeasure = ν.prod ν := by
    simpa [ν] using unitSquareUniformMeasure_eq_prodUniformInterval
  have hpair :
      unitSquareUniformMeasure.map (fun z : ℝ × ℝ ↦ (z.1, z.2)) =
        unitSquareUniformMeasure.map Prod.fst ⊗ₘ Kernel.const ℝ ν := by
    -- Rewrite the square law as a product law, then package the second coordinate as a constant
    -- kernel over the first marginal.
    calc
      unitSquareUniformMeasure.map (fun z : ℝ × ℝ ↦ (z.1, z.2))
          = unitSquareUniformMeasure := by simp
      _ = ν.prod ν := hsq
      _ = (ν.prod ν).map Prod.fst ⊗ₘ Kernel.const ℝ ν := by
            rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.compProd_const]
      _ = unitSquareUniformMeasure.map Prod.fst ⊗ₘ Kernel.const ℝ ν := by rw [hsq]
  have hcond :
      condDistrib Prod.snd Prod.fst unitSquareUniformMeasure =ᵐ[unitSquareUniformMeasure.map Prod.fst]
        Kernel.const ℝ ν :=
    condDistrib_ae_eq_of_measure_eq_compProd Prod.fst (by fun_prop) hpair
  -- Evaluate the constant kernel pointwise to obtain the claimed conditional law.
  filter_upwards [hcond] with x hx
  simpa [ν] using hx

/-- Helper for Exercise 8.3.3: the polar support describing the unit-disc law after the
change-of-variables `(x, y) = (r cos θ, r sin θ)`. -/
private def discPolarSupport : Set (ℝ × ℝ) :=
  {p | p ∈ polarCoord.target ∧ p.1 ≤ 1}

/-- Helper for Exercise 8.3.3: the unit-disc law in polar coordinates has density proportional to
the Jacobian factor `r` on the polar support. -/
private abbrev discPolarDensity (p : ℝ × ℝ) : ENNReal :=
  Set.indicator discPolarSupport
    (fun p ↦ (volume closedUnitDisc)⁻¹ * ENNReal.ofReal p.1) p

/-- Helper for Exercise 8.3.3: the explicit polar-domain measure pushing forward to the uniform law
on the unit disc. -/
private abbrev discPolarMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).withDensity discPolarDensity

/-- Helper for Exercise 8.3.3: the polar support describing the square law after the
change-of-variables `(x, y) = (r cos θ, r sin θ)`. -/
private def squarePolarSupport : Set (ℝ × ℝ) :=
  {p | p ∈ polarCoord.target ∧ p.2 ∈ squareFullAngleSupport p.1}

/-- Helper for Exercise 8.3.3: the square law in polar coordinates has density proportional to the
Jacobian factor `r` on the square polar support. -/
private abbrev squarePolarDensity (p : ℝ × ℝ) : ENNReal :=
  Set.indicator squarePolarSupport
    (fun p ↦ (volume unitSquare)⁻¹ * ENNReal.ofReal p.1) p

/-- Helper for Exercise 8.3.3: the explicit polar-domain measure pushing forward to the uniform law
on `[-1,1]^2`. -/
private abbrev squarePolarMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).withDensity squarePolarDensity

/-- Helper for Exercise 8.3.3: the disc polar support is the pullback of the disc along
`polarCoord.symm`, restricted to the polar target. -/
private theorem discPolarSupport_eq :
    discPolarSupport = polarCoord.target ∩ polarCoord.symm ⁻¹' closedUnitDisc := by
  -- Proof comment: on the polar target, disc membership is exactly the radial bound `r ≤ 1`.
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hp_target, hp_le⟩
    refine ⟨hp_target, ?_⟩
    exact (mem_closedUnitDisc_polarCoord_symm_iff hp_target).2 hp_le
  · intro hp
    rcases hp with ⟨hp_target, hp_disc⟩
    refine ⟨hp_target, ?_⟩
    exact (mem_closedUnitDisc_polarCoord_symm_iff hp_target).1 hp_disc

/-- Helper for Exercise 8.3.3: the square polar support is the pullback of the square along
`polarCoord.symm`, restricted to the polar target. -/
private theorem squarePolarSupport_eq :
    squarePolarSupport = polarCoord.target ∩ polarCoord.symm ⁻¹' unitSquare := by
  -- Proof comment: on the polar target, square membership is exactly the full-angle support
  -- condition encoded by `squareFullAngleSupport`.
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hp_target, hp_square⟩
    refine ⟨hp_target, ?_⟩
    exact (mem_unitSquare_polarCoord_symm_iff hp_target).2 hp_square
  · intro hp
    rcases hp with ⟨hp_target, hp_square⟩
    refine ⟨hp_target, ?_⟩
    exact (mem_unitSquare_polarCoord_symm_iff hp_target).1 hp_square

/-- Helper for Exercise 8.3.3: the disc polar support is measurable. -/
private theorem measurableSet_discPolarSupport : MeasurableSet discPolarSupport := by
  -- Proof comment: the support is the intersection of the measurable polar target with the
  -- pullback of the measurable disc.
  rw [discPolarSupport_eq]
  exact measurableSet_polarCoord_target.inter
    (measurableSet_closedUnitDisc.preimage (by fun_prop))

/-- Helper for Exercise 8.3.3: the disc polar density is measurable. -/
private theorem measurable_discPolarDensity : Measurable discPolarDensity := by
  -- Proof comment: this is a measurable radial factor cut down by the measurable disc support.
  refine (by fun_prop : Measurable fun p : ℝ × ℝ ↦
    (volume closedUnitDisc)⁻¹ * ENNReal.ofReal p.1).indicator measurableSet_discPolarSupport

/-- Helper for Exercise 8.3.3: on the polar target, the disc polar density is the Jacobian factor
times the Cartesian disc density evaluated at `polarCoord.symm p`. -/
private theorem discPolarDensity_comp_symm_of_mem_target {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    discPolarDensity p = ENNReal.ofReal p.1 * discDensity (polarCoord.symm p) := by
  -- Proof comment: on the target, the support test for `discPolarDensity` is exactly the same as
  -- the disc-membership test after applying `polarCoord.symm`.
  by_cases hdisc : polarCoord.symm p ∈ closedUnitDisc
  · have hsupp : p ∈ discPolarSupport := by
      rw [discPolarSupport_eq]
      exact ⟨hp, hdisc⟩
    rw [discPolarDensity, Set.indicator_of_mem hsupp, discDensity, Set.indicator_of_mem hdisc]
    rw [mul_comm]
  · have hsupp : p ∉ discPolarSupport := by
      intro hsupp
      rw [discPolarSupport_eq] at hsupp
      exact hdisc hsupp.2
    rw [discPolarDensity, Set.indicator_of_notMem hsupp]
    rw [discDensity, Set.indicator_of_notMem hdisc]
    simp

/-- Helper for Exercise 8.3.3: the square polar support is measurable. -/
private theorem measurableSet_squarePolarSupport : MeasurableSet squarePolarSupport := by
  -- Proof comment: the square support is the measurable pullback of the square inside the polar
  -- target.
  rw [squarePolarSupport_eq]
  exact measurableSet_polarCoord_target.inter
    (measurableSet_unitSquare.preimage (by fun_prop))

/-- Helper for Exercise 8.3.3: the square polar density is measurable. -/
private theorem measurable_squarePolarDensity : Measurable squarePolarDensity := by
  -- Proof comment: this is the same measurable radial Jacobian factor restricted to the
  -- measurable square support.
  refine (by fun_prop : Measurable fun p : ℝ × ℝ ↦
    (volume unitSquare)⁻¹ * ENNReal.ofReal p.1).indicator measurableSet_squarePolarSupport

/-- Helper for Exercise 8.3.3: on the polar target, the square polar density is the Jacobian
factor times the Cartesian square density evaluated at `polarCoord.symm p`. -/
private theorem squarePolarDensity_comp_symm_of_mem_target {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    squarePolarDensity p = ENNReal.ofReal p.1 * squareDensity (polarCoord.symm p) := by
  -- Proof comment: on the target, the square-support test is the same as checking whether
  -- `polarCoord.symm p` lies in `unitSquare`; the radial factor is unchanged.
  by_cases hsquare : polarCoord.symm p ∈ unitSquare
  · have hsupp : p ∈ squarePolarSupport := by
      rw [squarePolarSupport_eq]
      exact ⟨hp, hsquare⟩
    rw [squarePolarDensity, Set.indicator_of_mem hsupp, squareDensity, Set.indicator_of_mem hsquare]
    rw [mul_comm]
  · have hsupp : p ∉ squarePolarSupport := by
      intro hsupp
      rw [squarePolarSupport_eq] at hsupp
      exact hsquare hsupp.2
    rw [squarePolarDensity, Set.indicator_of_notMem hsupp]
    rw [squareDensity, Set.indicator_of_notMem hsquare]
    simp

/-- Helper for Exercise 8.3.3: the unit-disc law is the pushforward of the explicit polar-domain
measure by `polarCoord.symm`. -/
private theorem unitDiscUniformMeasure_eq_map_discPolarMeasure :
    Measure.map polarCoord.symm discPolarMeasure = unitDiscUniformMeasure := by
  have hdiscMeas : Measurable discDensity := measurable_discDensity
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hcomp : Measurable fun p : ℝ × ℝ ↦ f (polarCoord.symm p) := hf.comp (by fun_prop)
  -- Proof comment: compare both measures on nonnegative test functions and move the Jacobian
  -- factor into the test function before applying the polar change-of-variables theorem.
  rw [lintegral_map' hf.aemeasurable (by fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul₀ measurable_discPolarDensity.aemeasurable
    hcomp.aemeasurable]
  rw [unitDiscUniformMeasure_eq_withDensity_indicator]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hdiscMeas.aemeasurable hf.aemeasurable]
  calc
    ∫⁻ p, discPolarDensity p * f (polarCoord.symm p) ∂(volume : Measure (ℝ × ℝ))
        = ∫⁻ p,
            Set.indicator polarCoord.target
              (fun p : ℝ × ℝ ↦ discPolarDensity p * f (polarCoord.symm p)) p
            ∂(volume : Measure (ℝ × ℝ)) := by
              refine lintegral_congr_ae ?_
              filter_upwards with p
              by_cases hp : p ∈ polarCoord.target
              · rw [Set.indicator_of_mem hp]
              · rw [Set.indicator_of_notMem hp]
                have hsupp : p ∉ discPolarSupport := by
                  intro hsupp
                  exact hp hsupp.1
                rw [discPolarDensity, Set.indicator_of_notMem hsupp]
                simp
    _ = ∫⁻ p in polarCoord.target, discPolarDensity p * f (polarCoord.symm p)
          ∂(volume : Measure (ℝ × ℝ)) := by
            rw [lintegral_indicator measurableSet_polarCoord_target]
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 * (discDensity (polarCoord.symm p) * f (polarCoord.symm p))
          ∂(volume : Measure (ℝ × ℝ)) := by
            refine setLIntegral_congr_fun measurableSet_polarCoord_target fun p hp ↦ ?_
            rw [discPolarDensity_comp_symm_of_mem_target hp, mul_assoc]
    _ = ∫⁻ z, discDensity z * f z ∂(volume : Measure (ℝ × ℝ)) := by
          simpa [smul_eq_mul, mul_assoc] using
            lintegral_comp_polarCoord_symm (fun z : ℝ × ℝ ↦ discDensity z * f z)

/-- Helper for Exercise 8.3.3: the square law is the pushforward of the explicit polar-domain
measure by `polarCoord.symm`. -/
private theorem unitSquareUniformMeasure_eq_map_squarePolarMeasure :
    Measure.map polarCoord.symm squarePolarMeasure = unitSquareUniformMeasure := by
  have hsquareMeas : Measurable squareDensity := measurable_squareDensity
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hcomp : Measurable fun p : ℝ × ℝ ↦ f (polarCoord.symm p) := hf.comp (by fun_prop)
  -- Proof comment: the square case is the same transport argument, now with the square-support
  -- pullback through `polarCoord.symm`.
  rw [lintegral_map' hf.aemeasurable (by fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul₀ measurable_squarePolarDensity.aemeasurable
    hcomp.aemeasurable]
  rw [unitSquareUniformMeasure_eq_withDensity_indicator]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hsquareMeas.aemeasurable hf.aemeasurable]
  calc
    ∫⁻ p, squarePolarDensity p * f (polarCoord.symm p) ∂(volume : Measure (ℝ × ℝ))
        = ∫⁻ p,
            Set.indicator polarCoord.target
              (fun p : ℝ × ℝ ↦ squarePolarDensity p * f (polarCoord.symm p)) p
            ∂(volume : Measure (ℝ × ℝ)) := by
              refine lintegral_congr_ae ?_
              filter_upwards with p
              by_cases hp : p ∈ polarCoord.target
              · rw [Set.indicator_of_mem hp]
              · rw [Set.indicator_of_notMem hp]
                have hsupp : p ∉ squarePolarSupport := by
                  intro hsupp
                  exact hp hsupp.1
                rw [squarePolarDensity, Set.indicator_of_notMem hsupp]
                simp
    _ = ∫⁻ p in polarCoord.target, squarePolarDensity p * f (polarCoord.symm p)
          ∂(volume : Measure (ℝ × ℝ)) := by
            rw [lintegral_indicator measurableSet_polarCoord_target]
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 * (squareDensity (polarCoord.symm p) * f (polarCoord.symm p))
          ∂(volume : Measure (ℝ × ℝ)) := by
            refine setLIntegral_congr_fun measurableSet_polarCoord_target fun p hp ↦ ?_
            rw [squarePolarDensity_comp_symm_of_mem_target hp, mul_assoc]
    _ = ∫⁻ z, squareDensity z * f z ∂(volume : Measure (ℝ × ℝ)) := by
          simpa [smul_eq_mul, mul_assoc] using
            lintegral_comp_polarCoord_symm (fun z : ℝ × ℝ ↦ squareDensity z * f z)

/-- Helper for Exercise 8.3.3: the first marginal density attached to a measurable joint density is
measurable. -/
private theorem measurable_firstMarginalDensity_of_measurable {f : ℝ → ℝ → ENNReal}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2) :
    Measurable (first_marginal_density f) := by
  -- Proof comment: this is the standard measurability of the fiberwise Tonelli integral.
  have hlintegral : Measurable fun x ↦ ∫⁻ y, f x y ∂(volume : Measure ℝ) :=
    Measurable.lintegral_prod_right hf
  simpa [first_marginal_density] using hlintegral

/-- Helper for Exercise 8.3.3: the polar-domain disc law has total mass `1`. -/
private theorem discPolarMeasure_univ :
    discPolarMeasure Set.univ = 1 := by
  -- Proof comment: push forward by `polarCoord.symm` to the already-normalized disc law and
  -- evaluate both sides on `Set.univ`.
  have h :=
    congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ Set.univ) unitDiscUniformMeasure_eq_map_discPolarMeasure
  simpa [Measure.map_apply_of_aemeasurable continuous_polarCoord_symm.aemeasurable
    MeasurableSet.univ] using h

/-- Helper for Exercise 8.3.3: the polar-domain disc law is a probability measure. -/
private instance discPolarMeasure_isProbabilityMeasure :
    IsProbabilityMeasure discPolarMeasure where
  measure_univ := discPolarMeasure_univ

/-- Helper for Exercise 8.3.3: the polar-domain square law has total mass `1`. -/
private theorem squarePolarMeasure_univ :
    squarePolarMeasure Set.univ = 1 := by
  -- Proof comment: the square polar law pushes forward to the already-normalized square law, so
  -- its total mass agrees with `unitSquareUniformMeasure`.
  have h := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ Set.univ)
    unitSquareUniformMeasure_eq_map_squarePolarMeasure
  simpa [Measure.map_apply_of_aemeasurable continuous_polarCoord_symm.aemeasurable
    MeasurableSet.univ] using h

/-- Helper for Exercise 8.3.3: the polar-domain square law is a probability measure. -/
private instance squarePolarMeasure_isProbabilityMeasure :
    IsProbabilityMeasure squarePolarMeasure where
  measure_univ := squarePolarMeasure_univ

/-- Helper for Exercise 8.3.3: under `discPolarMeasure`, the identity pair has the explicit polar
joint density. -/
private theorem discPolarPair_hasLaw_discPolarDensity :
    HasLaw (fun p : ℝ × ℝ ↦ (p.1, p.2))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ discPolarDensity (z.1, z.2))
      discPolarMeasure := by
  -- Proof comment: the pair map is the identity on `ℝ × ℝ`, so the law statement is exactly the
  -- ambient-density definition of `discPolarMeasure`.
  refine ⟨by fun_prop, ?_⟩
  simpa [discPolarMeasure, Measure.volume_eq_prod]

/-- Helper for Exercise 8.3.3: under `squarePolarMeasure`, the identity pair has the explicit
polar joint density. -/
private theorem squarePolarPair_hasLaw_squarePolarDensity :
    HasLaw (fun p : ℝ × ℝ ↦ (p.1, p.2))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ squarePolarDensity (z.1, z.2))
      squarePolarMeasure := by
  -- Proof comment: the square polar measure is also defined by an ambient density on `ℝ × ℝ`,
  -- so the identity pair realizes exactly that joint law.
  refine ⟨by fun_prop, ?_⟩
  simpa [squarePolarMeasure, Measure.volume_eq_prod]

/-- Helper for Exercise 8.3.3: on admissible radii, the disc polar row is the constant Jacobian
density on `(-π, π)`. -/
private theorem discPolarDensity_fiber_eq_indicator_of_mem (r θ : ℝ) (hr : 0 < r ∧ r ≤ 1) :
    discPolarDensity (r, θ) =
      ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
        Set.indicator (Set.Ioo (-Real.pi) Real.pi) (fun _ ↦ (1 : ENNReal)) θ := by
  -- Proof comment: for `0 < r ≤ 1`, the only remaining support condition is that the angle lies
  -- in the polar target interval `(-π, π)`.
  by_cases hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi
  · have hsupp : (r, θ) ∈ discPolarSupport := ⟨⟨hr.1, hθ⟩, hr.2⟩
    simp [discPolarDensity, hsupp, hθ]
  · have hsupp : (r, θ) ∉ discPolarSupport := by
      intro hsupp
      exact hθ hsupp.1.2
    simp [discPolarDensity, hsupp, hθ]

/-- Helper for Exercise 8.3.3: off the admissible radial interval, the disc polar density row
vanishes identically. -/
private theorem discPolarDensity_fiber_eq_zero_of_not_mem (r θ : ℝ) (hr : ¬ (0 < r ∧ r ≤ 1)) :
    discPolarDensity (r, θ) = 0 := by
  -- Proof comment: outside `0 < r ≤ 1`, the support condition in `discPolarSupport` fails before
  -- any angular constraint is considered.
  have hsupp : (r, θ) ∉ discPolarSupport := by
    intro hsupp
    exact hr ⟨hsupp.1.1, hsupp.2⟩
  simp [discPolarDensity, hsupp]

/-- Helper for Exercise 8.3.3: integrating the disc polar density over the angle variable gives
the explicit first marginal in the radius variable. -/
private theorem discPolarFirstMarginalDensity_eval (r : ℝ) :
    first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r =
      if hr : 0 < r ∧ r ≤ 1 then
        ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
          volume (Set.Ioo (-Real.pi) Real.pi)
      else 0 := by
  by_cases hr : 0 < r ∧ r ≤ 1
  · -- Proof comment: on admissible radii the row is a constant density on the full angular
    -- interval, so the marginal is just that constant times the interval length.
    calc
      first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r
          = ∫⁻ θ, discPolarDensity (r, θ) ∂(volume : Measure ℝ) := by
              rfl
      _ = ∫⁻ θ,
            ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
              Set.indicator (Set.Ioo (-Real.pi) Real.pi) (fun _ ↦ (1 : ENNReal)) θ
            ∂(volume : Measure ℝ) := by
              refine lintegral_congr_ae ?_
              filter_upwards with θ
              simpa using discPolarDensity_fiber_eq_indicator_of_mem r θ hr
      _ = ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
            ∫⁻ θ, Set.indicator (Set.Ioo (-Real.pi) Real.pi) (fun _ ↦ (1 : ENNReal)) θ
              ∂(volume : Measure ℝ) := by
              rw [lintegral_const_mul' _ _ <|
                ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 volume_closedUnitDisc_pos.ne')
                  ENNReal.ofReal_ne_top]
      _ = ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
            volume (Set.Ioo (-Real.pi) Real.pi) := by
              rw [lintegral_indicator_const measurableSet_Ioo, one_mul]
      _ = if hr : 0 < r ∧ r ≤ 1 then
            ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
              volume (Set.Ioo (-Real.pi) Real.pi)
          else 0 := by
              simp [hr]
  · -- Proof comment: outside `0 < r ≤ 1`, every angular fiber is empty, so the whole marginal
    -- integral is zero.
    calc
      first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r
          = ∫⁻ θ, discPolarDensity (r, θ) ∂(volume : Measure ℝ) := by
              rfl
      _ = ∫⁻ θ, (0 : ENNReal) ∂(volume : Measure ℝ) := by
            refine lintegral_congr_ae ?_
            filter_upwards with θ
            exact discPolarDensity_fiber_eq_zero_of_not_mem r θ hr
      _ = 0 := by simp
      _ = if hr : 0 < r ∧ r ≤ 1 then
            ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
              volume (Set.Ioo (-Real.pi) Real.pi)
          else 0 := by
              simp [hr]

/-- Helper for Exercise 8.3.3: on every square radius, the angular row is the Jacobian factor
times the indicator of the full-angle support. -/
private theorem squarePolarDensity_fiber_eq_indicator (r θ : ℝ) :
    squarePolarDensity (r, θ) =
      ((volume unitSquare)⁻¹ * ENNReal.ofReal r) *
        Set.indicator (squareFullAngleSupport r) (fun _ ↦ (1 : ENNReal)) θ := by
  by_cases hr : 0 < r
  · by_cases hθ : θ ∈ squareFullAngleSupport r
    · have hsupp : (r, θ) ∈ squarePolarSupport := by
        refine ⟨⟨hr, hθ.1⟩, hθ⟩
      -- Proof comment: once `r > 0`, the square support is exactly the angular support family.
      simp [squarePolarDensity, hsupp, hθ]
    · have hsupp : (r, θ) ∉ squarePolarSupport := by
        intro hsupp
        exact hθ hsupp.2
      simp [squarePolarDensity, hsupp, hθ]
  · have hsupp : (r, θ) ∉ squarePolarSupport := by
      intro hsupp
      exact hr hsupp.1.1
    have hzero : ENNReal.ofReal r = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hr)
    -- Proof comment: nonpositive radii never belong to `polarCoord.target`, so the row vanishes
    -- and the Jacobian factor `ofReal r` vanishes as well.
    simp [squarePolarDensity, hsupp, hzero]

/-- Helper for Exercise 8.3.3: integrating the square polar density over the angle variable gives
the explicit first marginal in the radius variable. -/
private theorem squarePolarFirstMarginalDensity_eval (r : ℝ) :
    first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r =
      ((volume unitSquare)⁻¹ * ENNReal.ofReal r) * volume (squareFullAngleSupport r) := by
  -- Proof comment: every angular row is a constant Jacobian factor on the measurable support
  -- family `squareFullAngleSupport r`, so the marginal is that constant times its volume.
  rw [first_marginal_density]
  calc
    ∫⁻ θ, squarePolarDensity (r, θ) ∂(volume : Measure ℝ)
        = ∫⁻ θ,
            ((volume unitSquare)⁻¹ * ENNReal.ofReal r) *
              Set.indicator (squareFullAngleSupport r) (fun _ ↦ (1 : ENNReal)) θ
            ∂(volume : Measure ℝ) := by
              refine lintegral_congr_ae ?_
              filter_upwards with θ
              simpa using squarePolarDensity_fiber_eq_indicator r θ
    _ = ((volume unitSquare)⁻¹ * ENNReal.ofReal r) *
          ∫⁻ θ, Set.indicator (squareFullAngleSupport r) (fun _ ↦ (1 : ENNReal)) θ
            ∂(volume : Measure ℝ) := by
            rw [lintegral_const_mul' _ _ <|
              ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 volume_unitSquare_pos.ne')
                ENNReal.ofReal_ne_top]
    _ = ((volume unitSquare)⁻¹ * ENNReal.ofReal r) * volume (squareFullAngleSupport r) := by
          rw [lintegral_indicator_const (measurableSet_squareFullAngleSupport r), one_mul]

/-- Helper for Exercise 8.3.3: once the disc polar first marginal is positive, the density-ratio
row from Example 8.31 is exactly the conditioned Lebesgue law on `(-π, π)`. -/
private theorem discPolarDensityRatioKernel_eq_uniformCircle {r : ℝ}
    (hr :
      0 < first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun r θ ↦ discPolarDensity (r, θ) /
        first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) r =
      volume[|Set.Ioo (-Real.pi) Real.pi] := by
  let s : Set ℝ := Set.Ioo (-Real.pi) Real.pi
  have hratio_meas :
      Measurable (Function.uncurry fun r θ ↦
        discPolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) := by
    -- Proof comment: the ratio kernel uses the measurable joint density and its measurable first
    -- marginal.
    simpa [Function.uncurry] using
      measurable_discPolarDensity.div
        ((measurable_firstMarginalDensity_of_measurable measurable_discPolarDensity).comp
          measurable_fst)
  have hr_mem : 0 < r ∧ r ≤ 1 := by
    by_cases hmem : 0 < r ∧ r ≤ 1
    · exact hmem
    · have hzero :
          first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r = 0 := by
            simpa [hmem] using discPolarFirstMarginalDensity_eval r
      rw [hzero] at hr
      simp at hr
  have hscale_ne_zero :
      ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.inv_ne_zero.2 volume_closedUnitDisc_ne_top
    · exact ENNReal.ofReal_ne_zero_iff.2 hr_mem.1
  have hscale_ne_top :
      ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 volume_closedUnitDisc_pos.ne') ENNReal.ofReal_ne_top
  have hmass :
      first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r =
        ((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) * volume s := by
    simpa [s, hr_mem] using discPolarFirstMarginalDensity_eval r
  have hrowDensity :
      (fun θ ↦
        discPolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) =
        Set.indicator s (fun _ ↦ (volume s)⁻¹) := by
    -- Proof comment: on an admissible radius, dividing the constant Jacobian row by its total
    -- mass leaves the normalized interval indicator.
    funext θ
    calc
      discPolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r
        = (((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) *
            Set.indicator s (fun _ ↦ (1 : ENNReal)) θ) /
            (((volume closedUnitDisc)⁻¹ * ENNReal.ofReal r) * volume s) := by
              rw [discPolarDensity_fiber_eq_indicator_of_mem r θ hr_mem, hmass]
      _ = Set.indicator s (fun _ ↦ (1 : ENNReal)) θ / volume s := by
            rw [ENNReal.mul_div_mul_left _ _ hscale_ne_zero hscale_ne_top]
      _ = Set.indicator s (fun _ ↦ (volume s)⁻¹) θ := by
            by_cases hθ : θ ∈ s <;> simp [hθ]
  -- Proof comment: once the row density is identified with the normalized interval indicator, the
  -- `withDensity` kernel is exactly the conditioned Lebesgue measure on `(-π, π)`.
  calc
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun r θ ↦ discPolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) r
      = (volume : Measure ℝ).withDensity
          (fun θ ↦
            discPolarDensity (r, θ) /
              first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) := by
              rw [Kernel.withDensity_apply _ hratio_meas, Kernel.const_apply]
    _ = (volume : Measure ℝ).withDensity (Set.indicator s fun _ ↦ (volume s)⁻¹) := by
          rw [hrowDensity]
    _ = (volume.restrict s).withDensity (fun _ ↦ (volume s)⁻¹) := by
          rw [withDensity_indicator measurableSet_Ioo]
    _ = (volume.restrict s).withDensity ((volume s)⁻¹ • (1 : ℝ → ENNReal)) := by
          congr 1
          funext θ
          simp
    _ = (volume s)⁻¹ • volume.restrict s := by
          rw [withDensity_smul _ measurable_one, withDensity_one]
    _ = volume[|s] := by
          rw [ProbabilityTheory.cond]
    _ = volume[|Set.Ioo (-Real.pi) Real.pi] := by
          simp [s]

/-- Helper for Exercise 8.3.3: once the square polar first marginal is positive, the
density-ratio row from Example 8.31 is exactly the conditioned Lebesgue law on the full-angle
support. -/
private theorem squarePolarDensityRatioKernel_eq_uniformSupport {r : ℝ}
    (hr :
      0 < first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun r θ ↦ squarePolarDensity (r, θ) /
        first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) r =
      volume[|squareFullAngleSupport r] := by
  have hratio_meas :
      Measurable (Function.uncurry fun r θ ↦
        squarePolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) := by
    -- Proof comment: the square row ratio is measurable for the same reason as in the disc case.
    simpa [Function.uncurry] using
      measurable_squarePolarDensity.div
        ((measurable_firstMarginalDensity_of_measurable measurable_squarePolarDensity).comp
          measurable_fst)
  have hmass :
      first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r =
        ((volume unitSquare)⁻¹ * ENNReal.ofReal r) * volume (squareFullAngleSupport r) :=
    squarePolarFirstMarginalDensity_eval r
  have hscale_ne_zero :
      ((volume unitSquare)⁻¹ * ENNReal.ofReal r) ≠ 0 := by
    intro hzero
    have : first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r = 0 := by
      rw [hmass, hzero]
      simp
    exact (ne_of_gt hr) this
  have hscale_ne_top :
      ((volume unitSquare)⁻¹ * ENNReal.ofReal r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 volume_unitSquare_pos.ne') ENNReal.ofReal_ne_top
  have hrowDensity :
      (fun θ ↦
        squarePolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) =
        Set.indicator (squareFullAngleSupport r)
          (fun _ ↦ (volume (squareFullAngleSupport r))⁻¹) := by
    -- Proof comment: after dividing the square row by its total mass, only the normalized support
    -- indicator remains.
    funext θ
    calc
      squarePolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r
        = (((volume unitSquare)⁻¹ * ENNReal.ofReal r) *
            Set.indicator (squareFullAngleSupport r) (fun _ ↦ (1 : ENNReal)) θ) /
            (((volume unitSquare)⁻¹ * ENNReal.ofReal r) *
              volume (squareFullAngleSupport r)) := by
              rw [squarePolarDensity_fiber_eq_indicator r θ, hmass]
      _ = Set.indicator (squareFullAngleSupport r) (fun _ ↦ (1 : ENNReal)) θ /
            volume (squareFullAngleSupport r) := by
            rw [ENNReal.mul_div_mul_left _ _ hscale_ne_zero hscale_ne_top]
      _ = Set.indicator (squareFullAngleSupport r)
            (fun _ ↦ (volume (squareFullAngleSupport r))⁻¹) θ := by
            by_cases hθ : θ ∈ squareFullAngleSupport r <;> simp [hθ]
  -- Proof comment: the normalized support indicator is exactly the conditioned Lebesgue row on
  -- `squareFullAngleSupport r`.
  calc
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun r θ ↦ squarePolarDensity (r, θ) /
          first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) r
      = (volume : Measure ℝ).withDensity
          (fun θ ↦
            squarePolarDensity (r, θ) /
              first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) := by
              rw [Kernel.withDensity_apply _ hratio_meas, Kernel.const_apply]
    _ = (volume : Measure ℝ).withDensity
          (Set.indicator (squareFullAngleSupport r)
            (fun _ ↦ (volume (squareFullAngleSupport r))⁻¹)) := by
          rw [hrowDensity]
    _ = (volume.restrict (squareFullAngleSupport r)).withDensity
          (fun _ ↦ (volume (squareFullAngleSupport r))⁻¹) := by
          rw [withDensity_indicator (measurableSet_squareFullAngleSupport r)]
    _ = (volume.restrict (squareFullAngleSupport r)).withDensity
          ((volume (squareFullAngleSupport r))⁻¹ • (1 : ℝ → ENNReal)) := by
          congr 1
          funext θ
          simp
    _ = (volume (squareFullAngleSupport r))⁻¹ •
          volume.restrict (squareFullAngleSupport r) := by
            rw [withDensity_smul _ measurable_one, withDensity_one]
    _ = volume[|squareFullAngleSupport r] := by
          rw [ProbabilityTheory.cond]

/-- Helper for Exercise 8.3.3: in polar coordinates for the unit disc, the conditional
distribution of the full polar angle given the radius is uniform on `(-π, π)`. -/
private theorem condDistrib_snd_given_fst_discPolar_ae_eq_uniformCircle :
    ∀ᵐ r ∂(discPolarMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst discPolarMeasure r =
        volume[|Set.Ioo (-Real.pi) Real.pi] := by
  have hmeas :
      Measurable (Function.uncurry fun r θ ↦ discPolarDensity (r, θ)) := by
    -- Proof comment: this is exactly the measurability of the polar joint density, restated in
    -- the curried form required by Example 8.31.
    simpa [Function.uncurry] using measurable_discPolarDensity
  have hcond :
      condDistrib Prod.snd Prod.fst discPolarMeasure =ᵐ[discPolarMeasure.map Prod.fst]
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun r θ ↦
            discPolarDensity (r, θ) /
              first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r) := by
    -- Proof comment: apply the generic conditional-density theorem to the identity pair on the
    -- polar domain.
    simpa using
      (condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
        (P := discPolarMeasure) (X := Prod.fst) (Y := Prod.snd)
        (f := fun r θ ↦ discPolarDensity (r, θ)) hmeas
        discPolarPair_hasLaw_discPolarDensity)
  have hpos :
      ∀ᵐ r ∂(discPolarMeasure.map Prod.fst),
        0 < first_marginal_density (fun r θ ↦ discPolarDensity (r, θ)) r := by
    -- Proof comment: the density-ratio row formula is valid on almost every radius because the
    -- first marginal density is positive there.
    simpa using
      (first_marginal_density_pos_ae_of_hasLaw_prod_withDensity
        (P := discPolarMeasure) (X := Prod.fst) (Y := Prod.snd)
        (f := fun r θ ↦ discPolarDensity (r, θ)) hmeas
        discPolarPair_hasLaw_discPolarDensity)
  -- Proof comment: on radii with positive first marginal density, the local row computation turns
  -- the generic density-ratio kernel into the uniform circle law.
  filter_upwards [hcond, hpos] with r hrcond hrpos
  exact hrcond.trans (discPolarDensityRatioKernel_eq_uniformCircle hrpos)

/-- Helper for Exercise 8.3.3: in polar coordinates for the square, the conditional distribution
of the full polar angle given the radius is uniform on `squareFullAngleSupport r`. -/
private theorem condDistrib_snd_given_fst_squarePolar_ae_eq_uniformSupport :
    ∀ᵐ r ∂(squarePolarMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst squarePolarMeasure r =
        volume[|squareFullAngleSupport r] := by
  have hmeas :
      Measurable (Function.uncurry fun r θ ↦ squarePolarDensity (r, θ)) := by
    -- Proof comment: restate measurability of the square polar joint density in the curried
    -- format expected by the imported conditional-density theorem.
    simpa [Function.uncurry] using measurable_squarePolarDensity
  have hcond :
      condDistrib Prod.snd Prod.fst squarePolarMeasure =ᵐ[squarePolarMeasure.map Prod.fst]
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun r θ ↦
            squarePolarDensity (r, θ) /
              first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r) := by
    -- Proof comment: the polar square law is also an identity-pair joint density, so Example 8.31
    -- yields the conditional kernel directly.
    simpa using
      (condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
        (P := squarePolarMeasure) (X := Prod.fst) (Y := Prod.snd)
        (f := fun r θ ↦ squarePolarDensity (r, θ)) hmeas
        squarePolarPair_hasLaw_squarePolarDensity)
  have hpos :
      ∀ᵐ r ∂(squarePolarMeasure.map Prod.fst),
        0 < first_marginal_density (fun r θ ↦ squarePolarDensity (r, θ)) r := by
    -- Proof comment: the square row simplification also needs positivity of the radial marginal.
    simpa using
      (first_marginal_density_pos_ae_of_hasLaw_prod_withDensity
        (P := squarePolarMeasure) (X := Prod.fst) (Y := Prod.snd)
        (f := fun r θ ↦ squarePolarDensity (r, θ)) hmeas
        squarePolarPair_hasLaw_squarePolarDensity)
  -- Proof comment: combine the generic density-ratio description with the explicit square row
  -- normalization already proved locally.
  filter_upwards [hcond, hpos] with r hrcond hrpos
  exact hrcond.trans (squarePolarDensityRatioKernel_eq_uniformSupport hrpos)

/-- Helper for Exercise 8.3.3: `discPolarMeasure` is supported on the polar target. -/
private theorem ae_mem_polarTarget_discPolarMeasure :
    ∀ᵐ p ∂discPolarMeasure, p ∈ polarCoord.target := by
  -- Proof comment: the disc polar density vanishes outside `discPolarSupport`, and that support
  -- is contained in `polarCoord.target`.
  rw [discPolarMeasure, ae_withDensity_iff measurable_discPolarDensity]
  filter_upwards with p hp
  by_contra hp_target
  apply hp
  have hsupp : p ∉ discPolarSupport := by
    intro hsupp
    exact hp_target hsupp.1
  simp [discPolarDensity, hsupp]

/-- Helper for Exercise 8.3.3: `squarePolarMeasure` is supported on the polar target. -/
private theorem ae_mem_polarTarget_squarePolarMeasure :
    ∀ᵐ p ∂squarePolarMeasure, p ∈ polarCoord.target := by
  -- Proof comment: the square polar density also vanishes outside its support, which sits inside
  -- `polarCoord.target`.
  rw [squarePolarMeasure, ae_withDensity_iff measurable_squarePolarDensity]
  filter_upwards with p hp
  by_contra hp_target
  apply hp
  have hsupp : p ∉ squarePolarSupport := by
    intro hsupp
    exact hp_target hsupp.1
  simp [squarePolarDensity, hsupp]

/-- Helper for Exercise 8.3.3: the folded-angle map is measurable. -/
private theorem measurable_foldPolarAngle : Measurable foldPolarAngle := by
  -- Proof comment: `foldPolarAngle` is the composition `arctan ∘ tan`, and both factors are
  -- measurable on `ℝ`.
  have htan : Measurable fun θ : ℝ ↦ Real.tan θ := by
    -- Proof comment: rewrite `tan` as the quotient `sin / cos`, whose numerator and denominator
    -- are both measurable.
    simpa [Real.tan_eq_sin_div_cos] using
      (Measurable.div Real.measurable_sin Real.measurable_cos :
        Measurable fun θ : ℝ ↦ Real.sin θ / Real.cos θ)
  simpa [foldPolarAngle] using Real.measurable_arctan.comp htan

/-- Helper for Exercise 8.3.3: on the middle branch, folding the angle does nothing. -/
private theorem foldPolarAngle_eq_self_of_mem_middle {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    foldPolarAngle θ = θ := by
  -- Proof comment: on `(-π/2, π/2)`, `arctan` is a genuine inverse to `tan`.
  exact Real.arctan_tan hθ.1 hθ.2

/-- Helper for Exercise 8.3.3: on the right outer branch, folding subtracts `π`. -/
private theorem foldPolarAngle_eq_sub_pi_of_mem_right {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi) :
    foldPolarAngle θ = θ - Real.pi := by
  -- Proof comment: translate the angle back into the principal branch, where `arctan_tan`
  -- applies directly.
  have hleft : -(Real.pi / 2) < θ - Real.pi := by
    linarith [hθ.1]
  have hright : θ - Real.pi < Real.pi / 2 := by
    linarith [hθ.2]
  calc
    foldPolarAngle θ = Real.arctan (Real.tan (θ - Real.pi)) := by
      simp [foldPolarAngle, Real.tan_sub_pi]
    _ = θ - Real.pi := Real.arctan_tan hleft hright

/-- Helper for Exercise 8.3.3: on the left outer branch, folding adds `π`. -/
private theorem foldPolarAngle_eq_add_pi_of_mem_left {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-Real.pi) (-(Real.pi / 2))) :
    foldPolarAngle θ = θ + Real.pi := by
  -- Proof comment: adding `π` moves the angle into the principal branch, where `arctan_tan`
  -- becomes available.
  have hleft : -(Real.pi / 2) < θ + Real.pi := by
    linarith [hθ.1, Real.pi_pos]
  have hright : θ + Real.pi < Real.pi / 2 := by
    linarith [hθ.2]
  calc
    foldPolarAngle θ = Real.arctan (Real.tan (θ + Real.pi)) := by
      simp [foldPolarAngle, Real.tan_add_pi]
    _ = θ + Real.pi := Real.arctan_tan hleft hright

/-- Helper for Exercise 8.3.3: on the middle branch, the full and principal supports coincide. -/
private theorem mem_squareFullAngleSupport_middle_iff
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    θ ∈ squareFullAngleSupport r ↔
      θ ∈ squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  -- Proof comment: inside the principal strip the two support conditions differ only by replacing
  -- `(-π, π)` with `[-π/2, π/2]`.
  constructor
  · intro hfull
    rcases hfull with ⟨_, hr, hcos, hsin⟩
    refine ⟨?_, hθ⟩
    exact ⟨⟨le_of_lt hθ.1, le_of_lt hθ.2⟩, hr, hcos, hsin⟩
  · rintro ⟨hprincipal, _⟩
    rcases hprincipal with ⟨_, hr, hcos, hsin⟩
    exact ⟨by constructor <;> linarith [hθ.1, hθ.2], hr, hcos, hsin⟩

/-- Helper for Exercise 8.3.3: the right branch translates to the negative principal half. -/
private theorem mem_squareFullAngleSupport_right_iff
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi) :
    θ ∈ squareFullAngleSupport r ↔
      θ - Real.pi ∈ squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0 := by
  -- Proof comment: subtracting `π` moves the right branch into the negative principal half, and
  -- the support inequalities are unchanged because they involve absolute values.
  constructor
  · intro hfull
    rcases hfull with ⟨_, hr, hcos, hsin⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨le_of_lt ?_, le_of_lt ?_⟩, hr, ?_, ?_⟩
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
      · simpa [Real.cos_sub_pi, abs_neg] using hcos
      · simpa [Real.sin_sub_pi, abs_neg] using hsin
    · constructor
      · linarith [hθ.1]
      · linarith [hθ.2]
  · rintro ⟨hprincipal, hbranch⟩
    rcases hprincipal with ⟨_, hr, hcos, hsin⟩
    refine ⟨?_, hr, ?_, ?_⟩
    · constructor
      · linarith [hbranch.1, Real.pi_pos]
      · linarith [hbranch.2]
    · simpa [Real.cos_sub_pi, abs_neg] using hcos
    · simpa [Real.sin_sub_pi, abs_neg] using hsin

/-- Helper for Exercise 8.3.3: the left branch translates to the positive principal half. -/
private theorem mem_squareFullAngleSupport_left_iff
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi) (-(Real.pi / 2))) :
    θ ∈ squareFullAngleSupport r ↔
      θ + Real.pi ∈ squarePrincipalAngleSupport r ∩ Set.Ioo 0 (Real.pi / 2) := by
  -- Proof comment: adding `π` moves the left branch into the positive principal half, and the
  -- support inequalities stay unchanged because only absolute values occur.
  constructor
  · intro hfull
    rcases hfull with ⟨_, hr, hcos, hsin⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨le_of_lt ?_, le_of_lt ?_⟩, hr, ?_, ?_⟩
      · linarith [hθ.1, Real.pi_pos]
      · linarith [hθ.2]
      · simpa [Real.cos_add_pi, abs_neg] using hcos
      · simpa [Real.sin_add_pi, abs_neg] using hsin
    · constructor
      · linarith [hθ.1]
      · linarith [hθ.2]
  · rintro ⟨hprincipal, hbranch⟩
    rcases hprincipal with ⟨_, hr, hcos, hsin⟩
    refine ⟨?_, hr, ?_, ?_⟩
    · constructor
      · linarith [hbranch.1]
      · linarith [hbranch.2, Real.pi_pos]
    · simpa [Real.cos_add_pi, abs_neg] using hcos
    · simpa [Real.sin_add_pi, abs_neg] using hsin

/-- Helper for Exercise 8.3.3: translating restricted Lebesgue measure by a constant transports
preimage restrictions to the target restriction. -/
private theorem mapVolumeRestrictPreimageAddRight {s : Set ℝ} (hs : MeasurableSet s) (c : ℝ) :
    Measure.map (fun θ : ℝ ↦ θ + c)
      ((volume : Measure ℝ).restrict ((fun θ : ℝ ↦ θ + c) ⁻¹' s)) =
        (volume : Measure ℝ).restrict s := by
  -- Proof comment: first commute restriction with pushforward, then use translation invariance of
  -- Lebesgue measure.
  rw [← Measure.restrict_map (by fun_prop) hs]
  exact congrArg (fun μ : Measure ℝ ↦ μ.restrict s) (map_add_right_eq_self (volume : Measure ℝ) c)

/-- Helper for Exercise 8.3.3: on the middle branch, folding the angle is the identity on the
restricted Lebesgue row. -/
private theorem map_foldPolarAngle_restrict_squareMiddleBranch (r : ℝ) :
    let sMid := squareFullAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    let tMid := squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sMid) =
      (volume : Measure ℝ).restrict tMid := by
  let sMid := squareFullAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let tMid := squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hsMid : MeasurableSet sMid := by
    simp [sMid, measurableSet_squareFullAngleSupport]
  have hEqOn : Set.EqOn foldPolarAngle id sMid := by
    intro θ hθ
    exact foldPolarAngle_eq_self_of_mem_middle hθ.2
  have hset : sMid = tMid := by
    ext θ
    constructor
    · intro hθ
      exact (mem_squareFullAngleSupport_middle_iff r θ hθ.2).1 hθ.1
    · intro hθ
      exact ⟨(mem_squareFullAngleSupport_middle_iff r θ hθ.2).2 hθ, hθ.2⟩
  -- Proof comment: once the middle branch is isolated, the fold is literally `id`, and the only
  -- remaining work is to rewrite the support from the full-angle to the principal-angle form.
  calc
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sMid)
        = Measure.map id ((volume : Measure ℝ).restrict sMid) := by
            exact Measure.map_congr (hEqOn.aeEq_restrict hsMid)
    _ = (volume : Measure ℝ).restrict sMid := by simp
    _ = (volume : Measure ℝ).restrict tMid := by rw [hset]

/-- Helper for Exercise 8.3.3: on the right branch, folding the angle is translation by `-π` on
the restricted Lebesgue row. -/
private theorem map_foldPolarAngle_restrict_squareRightBranch (r : ℝ) :
    let sRight := squareFullAngleSupport r ∩ Set.Ioo (Real.pi / 2) Real.pi
    let tNeg := squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sRight) =
      (volume : Measure ℝ).restrict tNeg := by
  let sRight := squareFullAngleSupport r ∩ Set.Ioo (Real.pi / 2) Real.pi
  let tNeg := squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0
  have hsRight : MeasurableSet sRight := by
    simp [sRight, measurableSet_squareFullAngleSupport]
  have htNeg : MeasurableSet tNeg := by
    simp [tNeg, measurableSet_squarePrincipalAngleSupport]
  have hEqOn : Set.EqOn foldPolarAngle (fun θ : ℝ ↦ θ + (-Real.pi)) sRight := by
    intro θ hθ
    simpa [sub_eq_add_neg] using foldPolarAngle_eq_sub_pi_of_mem_right hθ.2
  have hpre :
      sRight = (fun θ : ℝ ↦ θ + (-Real.pi)) ⁻¹' tNeg := by
    ext θ
    constructor
    · intro hθ
      have himage :
          θ - Real.pi ∈ squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0 :=
        (mem_squareFullAngleSupport_right_iff r θ hθ.2).1 hθ.1
      simpa [tNeg, sub_eq_add_neg] using himage
    · intro hθ
      have hθ' :
          θ - Real.pi ∈ squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0 := by
        simpa [tNeg, sub_eq_add_neg] using hθ
      have hbranch : θ ∈ Set.Ioo (Real.pi / 2) Real.pi := by
        constructor
        · linarith [hθ'.2.1]
        · linarith [hθ'.2.2, Real.pi_pos]
      exact ⟨(mem_squareFullAngleSupport_right_iff r θ hbranch).2
        hθ', hbranch⟩
  -- Proof comment: rewrite the fold map to translation by `-π` on the right branch, then invoke
  -- the generic translation-transport lemma for restricted Lebesgue measure.
  calc
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sRight)
        = Measure.map (fun θ : ℝ ↦ θ + (-Real.pi)) ((volume : Measure ℝ).restrict sRight) := by
            exact Measure.map_congr (hEqOn.aeEq_restrict hsRight)
    _ = Measure.map (fun θ : ℝ ↦ θ + (-Real.pi))
          ((volume : Measure ℝ).restrict ((fun θ : ℝ ↦ θ + (-Real.pi)) ⁻¹' tNeg)) := by
            rw [hpre]
    _ = (volume : Measure ℝ).restrict tNeg := by
          exact mapVolumeRestrictPreimageAddRight htNeg (-Real.pi)

/-- Helper for Exercise 8.3.3: on the left branch, folding the angle is translation by `+π` on
the restricted Lebesgue row. -/
private theorem map_foldPolarAngle_restrict_squareLeftBranch (r : ℝ) :
    let sLeft := squareFullAngleSupport r ∩ Set.Ioo (-Real.pi) (-(Real.pi / 2))
    let tPos := squarePrincipalAngleSupport r ∩ Set.Ioo 0 (Real.pi / 2)
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sLeft) =
      (volume : Measure ℝ).restrict tPos := by
  let sLeft := squareFullAngleSupport r ∩ Set.Ioo (-Real.pi) (-(Real.pi / 2))
  let tPos := squarePrincipalAngleSupport r ∩ Set.Ioo 0 (Real.pi / 2)
  have hsLeft : MeasurableSet sLeft := by
    simp [sLeft, measurableSet_squareFullAngleSupport]
  have htPos : MeasurableSet tPos := by
    simp [tPos, measurableSet_squarePrincipalAngleSupport]
  have hEqOn : Set.EqOn foldPolarAngle (fun θ : ℝ ↦ θ + Real.pi) sLeft := by
    intro θ hθ
    exact foldPolarAngle_eq_add_pi_of_mem_left hθ.2
  have hpre :
      sLeft = (fun θ : ℝ ↦ θ + Real.pi) ⁻¹' tPos := by
    ext θ
    constructor
    · intro hθ
      exact (mem_squareFullAngleSupport_left_iff r θ hθ.2).1 hθ.1
    · intro hθ
      have hbranch : θ ∈ Set.Ioo (-Real.pi) (-(Real.pi / 2)) := by
        constructor
        · linarith [hθ.2.1, Real.pi_pos]
        · linarith [hθ.2.2]
      exact ⟨(mem_squareFullAngleSupport_left_iff r θ hbranch).2 hθ, hbranch⟩
  -- Proof comment: the left branch is the symmetric translation-by-`π` case of the right branch.
  calc
    Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sLeft)
        = Measure.map (fun θ : ℝ ↦ θ + Real.pi) ((volume : Measure ℝ).restrict sLeft) := by
            exact Measure.map_congr (hEqOn.aeEq_restrict hsLeft)
    _ = Measure.map (fun θ : ℝ ↦ θ + Real.pi)
          ((volume : Measure ℝ).restrict ((fun θ : ℝ ↦ θ + Real.pi) ⁻¹' tPos)) := by
            rw [hpre]
    _ = (volume : Measure ℝ).restrict tPos := by
          exact mapVolumeRestrictPreimageAddRight htPos Real.pi

/-- Helper for Exercise 8.3.3: deleting the endpoint angles `± π / 2` splits the full support
into the three open fold branches. -/
private theorem squareFullAngleSupport_diffBoundary_eq_branchUnion (r : ℝ) :
    squareFullAngleSupport r \ ({-(Real.pi / 2), Real.pi / 2} : Set ℝ) =
      (squareFullAngleSupport r ∩ Set.Ioo (-Real.pi) (-(Real.pi / 2))) ∪
        (squareFullAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) ∪
          (squareFullAngleSupport r ∩ Set.Ioo (Real.pi / 2) Real.pi) := by
  ext θ
  constructor
  · intro hθ
    rcases hθ with ⟨hfull, hnotBoundary⟩
    rcases hfull with ⟨hAngle, hSupport⟩
    -- Proof comment: once the boundary points are removed, trichotomy against `± π / 2`
    -- places the angle in exactly one of the three open branches.
    by_cases hLeft : θ < -(Real.pi / 2)
    · exact Or.inl <| Or.inl ⟨⟨hAngle, hSupport⟩, ⟨hAngle.1, hLeft⟩⟩
    · by_cases hMid : θ < Real.pi / 2
      · have hLower : -(Real.pi / 2) < θ := by
          refine lt_of_le_of_ne (le_of_not_gt hLeft) ?_
          intro hEq
          exact hnotBoundary (by simp [hEq])
        exact Or.inl <| Or.inr ⟨⟨hAngle, hSupport⟩, ⟨hLower, hMid⟩⟩
      · have hUpper : Real.pi / 2 < θ := by
          refine lt_of_le_of_ne (le_of_not_gt hMid) ?_
          intro hEq
          exact hnotBoundary (by simp [hEq])
        exact Or.inr ⟨⟨hAngle, hSupport⟩, ⟨hUpper, hAngle.2⟩⟩
  · intro hθ
    rcases hθ with hLeft | hRight
    · rcases hLeft with hLeft | hMid
      · rcases hLeft with ⟨hfull, hLeft⟩
        refine ⟨hfull, ?_⟩
        -- Proof comment: strict left-branch inequalities keep the angle away from both deleted
        -- boundary points.
        have hneLeft : θ ≠ -(Real.pi / 2) := ne_of_lt hLeft.2
        have hneRight : θ ≠ Real.pi / 2 := by
          have hlt : θ < Real.pi / 2 := by
            linarith [hLeft.2, Real.pi_pos]
          exact ne_of_lt hlt
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hneLeft, hneRight]
      · rcases hMid with ⟨hfull, hMid⟩
        refine ⟨hfull, ?_⟩
        -- Proof comment: strict middle-branch inequalities exclude both endpoint angles directly.
        have hneLeft : θ ≠ -(Real.pi / 2) := ne_of_gt hMid.1
        have hneRight : θ ≠ Real.pi / 2 := ne_of_lt hMid.2
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hneLeft, hneRight]
    · rcases hRight with ⟨hfull, hRight⟩
      refine ⟨hfull, ?_⟩
      -- Proof comment: strict right-branch inequalities again remove both deleted boundary
      -- points.
      have hneLeft : θ ≠ -(Real.pi / 2) := by
        intro hEq
        linarith [hRight.1, Real.pi_pos]
      have hneRight : θ ≠ Real.pi / 2 := ne_of_gt hRight.1
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, hneLeft, hneRight]

/-- Helper for Exercise 8.3.3: deleting the endpoint angles `± π / 2` from the principal support
leaves the open middle strip. -/
private theorem squarePrincipalAngleSupport_diffBoundary_eq_middleOpen (r : ℝ) :
    squarePrincipalAngleSupport r \ ({-(Real.pi / 2), Real.pi / 2} : Set ℝ) =
      squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  ext θ
  constructor
  · intro hθ
    rcases hθ with ⟨hprincipal, hnotBoundary⟩
    rcases hprincipal with ⟨hAngle, hSupport⟩
    -- Proof comment: removing the two endpoints from the closed principal interval leaves the
    -- open interval.
    have hLower : -(Real.pi / 2) < θ := by
      refine lt_of_le_of_ne hAngle.1 ?_
      intro hEq
      exact hnotBoundary (by simp [hEq])
    have hUpper : θ < Real.pi / 2 := by
      refine lt_of_le_of_ne hAngle.2 ?_
      intro hEq
      exact hnotBoundary (by simp [hEq])
    exact ⟨⟨hAngle, hSupport⟩, ⟨hLower, hUpper⟩⟩
  · intro hθ
    rcases hθ with ⟨hprincipal, hAngle⟩
    refine ⟨hprincipal, ?_⟩
    -- Proof comment: strict interior points cannot lie in the deleted endpoint set.
    have hneLeft : θ ≠ -(Real.pi / 2) := ne_of_gt hAngle.1
    have hneRight : θ ≠ Real.pi / 2 := ne_of_lt hAngle.2
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hneLeft, hneRight]

/-- Helper for Exercise 8.3.3: deleting the overlap point `0` from the open principal strip splits
it into the negative and positive half-strips. -/
private theorem squarePrincipalMiddle_diffZero_eq_halfUnion (r : ℝ) :
    (squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) \ ({0} : Set ℝ) =
      (squarePrincipalAngleSupport r ∩ Set.Ioo (-(Real.pi / 2)) 0) ∪
        (squarePrincipalAngleSupport r ∩ Set.Ioo 0 (Real.pi / 2) : Set ℝ) := by
  ext θ
  constructor
  · intro hθ
    rcases hθ with ⟨hMid, hneZero⟩
    rcases hMid with ⟨hprincipal, hAngle⟩
    -- Proof comment: after removing the overlap point `0`, the open middle strip splits by the
    -- sign of `θ`.
    by_cases hNeg : θ < 0
    · exact Or.inl ⟨hprincipal, ⟨hAngle.1, hNeg⟩⟩
    · have hPos : 0 < θ := by
        refine lt_of_le_of_ne (le_of_not_gt hNeg) ?_
        intro hEq
        exact hneZero (by simpa [hEq])
      exact Or.inr ⟨hprincipal, ⟨hPos, hAngle.2⟩⟩
  · intro hθ
    rcases hθ with hNeg | hPos
    · rcases hNeg with ⟨hprincipal, hAngle⟩
      refine ⟨⟨hprincipal, ⟨hAngle.1, ?_⟩⟩, ?_⟩
      · -- Proof comment: the negative half-strip sits inside the full open middle strip.
        linarith [hAngle.2, Real.pi_pos]
      · exact by simp [Set.mem_singleton_iff, ne_of_lt hAngle.2]
    · rcases hPos with ⟨hprincipal, hAngle⟩
      refine ⟨⟨hprincipal, ⟨?_, hAngle.2⟩⟩, ?_⟩
      · -- Proof comment: the positive half-strip is the complementary half of the same middle
        -- strip.
        linarith [hAngle.1, Real.pi_pos]
      · exact by simp [Set.mem_singleton_iff, ne_of_gt hAngle.1]

/-- Helper for Exercise 8.3.3: folding the full angular support back to the principal branch sends
the conditioned Lebesgue law on `squareFullAngleSupport r` to the conditioned Lebesgue law on
`squarePrincipalAngleSupport r`. -/
private theorem map_foldPolarAngle_uniformSquareSupport (r : ℝ) :
    Measure.map foldPolarAngle (volume[|squareFullAngleSupport r]) =
      volume[|squarePrincipalAngleSupport r] := by
  -- Route correction: the remaining blocker is no longer the fold geometry. The missing layer is
  -- the exact source/target set decomposition and the mass normalization that turns the assembled
  -- branch pushforwards into the conditioned-measure identity.
  let s := squareFullAngleSupport r
  let p := squarePrincipalAngleSupport r
  let boundary : Set ℝ := ({-(Real.pi / 2), Real.pi / 2} : Set ℝ)
  let sLeft := s ∩ Set.Ioo (-Real.pi) (-(Real.pi / 2))
  let sMid := s ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let sRight := s ∩ Set.Ioo (Real.pi / 2) Real.pi
  let bSrc := s ∩ boundary
  let bTgt := p ∩ boundary
  let tMid := p ∩ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let tNeg := p ∩ Set.Ioo (-(Real.pi / 2)) 0
  let tPos := p ∩ Set.Ioo 0 (Real.pi / 2)
  have hboundaryMeas : MeasurableSet boundary := by
    simp [boundary]
  have hsRightMeas : MeasurableSet sRight := by
    simp [sRight, s, measurableSet_squareFullAngleSupport]
  have hsMidRightMeas : MeasurableSet (sMid ∪ sRight) := by
    simp [sMid, sRight, s, measurableSet_squareFullAngleSupport]
  have htPosMeas : MeasurableSet tPos := by
    simp [tPos, p, measurableSet_squarePrincipalAngleSupport]
  have hbSrcZero : (volume : Measure ℝ) bSrc = 0 := by
    refine measure_mono_null (fun θ hθ ↦ hθ.2) ?_
    change (volume : Measure ℝ)
        (({-(Real.pi / 2)} : Set ℝ) ∪ ({Real.pi / 2} : Set ℝ)) = 0
    have hdisj :
        Disjoint ({-(Real.pi / 2)} : Set ℝ) ({Real.pi / 2} : Set ℝ) := by
      refine Set.disjoint_left.2 ?_
      intro θ hleft hright
      simp at hleft hright
      nlinarith [Real.pi_pos]
    rw [measure_union hdisj (measurableSet_singleton (Real.pi / 2))]
    simp [measure_singleton]
  have hbTgtZero : (volume : Measure ℝ) bTgt = 0 := by
    refine measure_mono_null (fun θ hθ ↦ hθ.2) ?_
    change (volume : Measure ℝ)
        (({-(Real.pi / 2)} : Set ℝ) ∪ ({Real.pi / 2} : Set ℝ)) = 0
    have hdisj :
        Disjoint ({-(Real.pi / 2)} : Set ℝ) ({Real.pi / 2} : Set ℝ) := by
      refine Set.disjoint_left.2 ?_
      intro θ hleft hright
      simp at hleft hright
      nlinarith [Real.pi_pos]
    rw [measure_union hdisj (measurableSet_singleton (Real.pi / 2))]
    simp [measure_singleton]
  have hmidZero : (volume : Measure ℝ) (tMid ∩ ({0} : Set ℝ)) = 0 := by
    refine measure_mono_null (fun θ hθ ↦ hθ.2) ?_
    simpa using (measure_singleton (0 : ℝ) : (volume : Measure ℝ) ({0} : Set ℝ) = 0)
  have hsMidRightDisj : Disjoint sMid sRight := by
    refine Set.disjoint_left.2 ?_
    intro θ hMid hRight
    linarith [hMid.2.2, hRight.2.1]
  have hsLeftRestDisj : Disjoint sLeft (sMid ∪ sRight) := by
    refine Set.disjoint_left.2 ?_
    intro θ hLeft hRest
    rcases hRest with hMid | hRight
    · linarith [hLeft.2.2, hMid.2.1]
    · linarith [hLeft.2.2, hRight.2.1, Real.pi_pos]
  have htNegPosDisj : Disjoint tNeg tPos := by
    refine Set.disjoint_left.2 ?_
    intro θ hNeg hPos
    linarith [hNeg.2.2, hPos.2.1]
  have htargetRestrict :
      (volume : Measure ℝ).restrict p = (volume : Measure ℝ).restrict tMid := by
    -- Proof comment: deleting the endpoint boundary from the principal support does not change the
    -- restricted Lebesgue measure because the boundary has zero volume.
    calc
      (volume : Measure ℝ).restrict p
          = (volume : Measure ℝ).restrict (p ∩ boundary) +
              (volume : Measure ℝ).restrict (p \ boundary) := by
                symm
                exact Measure.restrict_inter_add_diff p hboundaryMeas
      _ = (0 : Measure ℝ) + (volume : Measure ℝ).restrict tMid := by
            rw [show p ∩ boundary = bTgt by rfl,
              show p \ boundary = tMid by
                simpa [p, bTgt, tMid] using squarePrincipalAngleSupport_diffBoundary_eq_middleOpen r,
              Measure.restrict_zero_set hbTgtZero]
      _ = (volume : Measure ℝ).restrict tMid := by simp
  have hmidSplit :
      (volume : Measure ℝ).restrict tMid =
        (volume : Measure ℝ).restrict tNeg + (volume : Measure ℝ).restrict tPos := by
    -- Proof comment: removing the null overlap point `0` splits the open principal strip into its
    -- negative and positive halves.
    calc
      (volume : Measure ℝ).restrict tMid
          = (volume : Measure ℝ).restrict (tMid ∩ ({0} : Set ℝ)) +
              (volume : Measure ℝ).restrict (tMid \ ({0} : Set ℝ)) := by
                symm
                exact Measure.restrict_inter_add_diff tMid (measurableSet_singleton (0 : ℝ))
      _ = (0 : Measure ℝ) + (volume : Measure ℝ).restrict (tMid \ ({0} : Set ℝ)) := by
            rw [Measure.restrict_zero_set hmidZero]
      _ = (volume : Measure ℝ).restrict (tNeg ∪ tPos) := by
            rw [zero_add]
            rw [show tMid \ ({0} : Set ℝ) = tNeg ∪ tPos by
              simpa [tMid, tNeg, tPos] using squarePrincipalMiddle_diffZero_eq_halfUnion r]
      _ = (volume : Measure ℝ).restrict tNeg + (volume : Measure ℝ).restrict tPos := by
            rw [Measure.restrict_union htNegPosDisj htPosMeas]
  have hsourceRestrict :
      (volume : Measure ℝ).restrict s =
        (volume : Measure ℝ).restrict sLeft + (volume : Measure ℝ).restrict sMid +
          (volume : Measure ℝ).restrict sRight := by
    -- Proof comment: after deleting the null source boundary, the full support is exactly the
    -- disjoint union of the three fold branches.
    calc
      (volume : Measure ℝ).restrict s
          = (volume : Measure ℝ).restrict (s ∩ boundary) +
              (volume : Measure ℝ).restrict (s \ boundary) := by
                symm
                exact Measure.restrict_inter_add_diff s hboundaryMeas
      _ = (0 : Measure ℝ) + (volume : Measure ℝ).restrict (sLeft ∪ sMid ∪ sRight) := by
            rw [show s ∩ boundary = bSrc by rfl,
              show s \ boundary = sLeft ∪ sMid ∪ sRight by
                simpa [s, boundary, sLeft, sMid, sRight] using
                  squareFullAngleSupport_diffBoundary_eq_branchUnion r,
              Measure.restrict_zero_set hbSrcZero]
      _ = (volume : Measure ℝ).restrict (sLeft ∪ sMid ∪ sRight) := by simp
      _ = (volume : Measure ℝ).restrict sLeft + (volume : Measure ℝ).restrict (sMid ∪ sRight) := by
            rw [show sLeft ∪ sMid ∪ sRight = sLeft ∪ (sMid ∪ sRight) by
              ext θ
              simp [or_assoc],
              Measure.restrict_union hsLeftRestDisj hsMidRightMeas]
      _ = (volume : Measure ℝ).restrict sLeft +
            ((volume : Measure ℝ).restrict sMid + (volume : Measure ℝ).restrict sRight) := by
              rw [Measure.restrict_union hsMidRightDisj hsRightMeas]
      _ = (volume : Measure ℝ).restrict sLeft + (volume : Measure ℝ).restrict sMid +
            (volume : Measure ℝ).restrict sRight := by
              rw [add_assoc]
  have hleftMap :
      Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sLeft) =
        (volume : Measure ℝ).restrict tPos := by
    simpa [sLeft, tPos, s, p] using map_foldPolarAngle_restrict_squareLeftBranch r
  have hmidMap :
      Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sMid) =
        (volume : Measure ℝ).restrict tMid := by
    simpa [sMid, tMid, s, p] using map_foldPolarAngle_restrict_squareMiddleBranch r
  have hrightMap :
      Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sRight) =
        (volume : Measure ℝ).restrict tNeg := by
    simpa [sRight, tNeg, s, p] using map_foldPolarAngle_restrict_squareRightBranch r
  have hunnorm :
      Measure.map foldPolarAngle ((volume : Measure ℝ).restrict s) =
        ((volume : Measure ℝ).restrict tMid) + (volume : Measure ℝ).restrict tMid := by
    -- Proof comment: the three branch pushforwards cover the middle strip twice, once from the
    -- middle branch and once from the folded outer branches.
    calc
      Measure.map foldPolarAngle ((volume : Measure ℝ).restrict s)
          = Measure.map foldPolarAngle
              (((volume : Measure ℝ).restrict sLeft + (volume : Measure ℝ).restrict sMid) +
                (volume : Measure ℝ).restrict sRight) := by
                  rw [hsourceRestrict, add_assoc]
      _ = Measure.map foldPolarAngle
            ((volume : Measure ℝ).restrict sLeft + (volume : Measure ℝ).restrict sMid) +
            Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sRight) := by
              rw [Measure.map_add _ _ measurable_foldPolarAngle]
      _ = (Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sLeft) +
            Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sMid)) +
            Measure.map foldPolarAngle ((volume : Measure ℝ).restrict sRight) := by
              rw [Measure.map_add _ _ measurable_foldPolarAngle]
      _ = ((volume : Measure ℝ).restrict tPos + (volume : Measure ℝ).restrict tMid) +
            (volume : Measure ℝ).restrict tNeg := by
              rw [hleftMap, hmidMap, hrightMap]
      _ = (volume : Measure ℝ).restrict tMid +
            ((volume : Measure ℝ).restrict tNeg + (volume : Measure ℝ).restrict tPos) := by
              simpa [add_assoc, add_left_comm, add_comm]
      _ = (volume : Measure ℝ).restrict tMid + ((volume : Measure ℝ).restrict tMid) := by
            rw [← hmidSplit]
      _ = (volume : Measure ℝ).restrict tMid + (volume : Measure ℝ).restrict tMid := by
            rfl
  have hmassSource : volume s = 2 * volume tMid := by
    -- Proof comment: evaluating the unnormalized equality on `univ` identifies the total mass of
    -- the source support as twice the open principal-strip mass.
    simpa [s, tMid, two_mul, Measure.map_apply measurable_foldPolarAngle MeasurableSet.univ,
      Measure.restrict_apply MeasurableSet.univ] using
      congrArg (fun ν : Measure ℝ ↦ ν Set.univ) hunnorm
  have hmassTarget : volume p = volume tMid := by
    -- Proof comment: the target endpoints have zero volume, so the principal support and its open
    -- interior have the same total mass.
    simpa [p, tMid] using congrArg (fun ν : Measure ℝ ↦ ν Set.univ) htargetRestrict
  ext u hu
  have hunnormApply :
      volume (s ∩ foldPolarAngle ⁻¹' u) = 2 * volume (tMid ∩ u) := by
    -- Proof comment: apply the unnormalized measure equality to the measurable target set `u`.
    simpa [s, tMid, hu, two_mul, Measure.map_apply measurable_foldPolarAngle hu,
      Measure.restrict_apply (measurable_foldPolarAngle hu), Measure.restrict_apply hu,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      congrArg (fun ν : Measure ℝ ↦ ν u) hunnorm
  have htargetApply :
      volume (p ∩ u) = volume (tMid ∩ u) := by
    -- Proof comment: the endpoint-null replacement on the target also holds after intersecting
    -- with an arbitrary measurable test set.
    simpa [p, tMid, hu, Measure.restrict_apply hu, Set.inter_comm, Set.inter_left_comm,
      Set.inter_assoc] using
      congrArg (fun ν : Measure ℝ ↦ ν u) htargetRestrict
  -- Proof comment: rewrite both conditioned measures using `cond_apply'`, insert the
  -- unnormalized source equality, and cancel the common factor `2`.
  calc
    Measure.map foldPolarAngle (volume[|s]) u
        = (volume s)⁻¹ * volume (s ∩ foldPolarAngle ⁻¹' u) := by
            rw [Measure.map_apply measurable_foldPolarAngle hu,
              ProbabilityTheory.cond_apply' (measurable_foldPolarAngle hu)]
    _ = (volume s)⁻¹ * (2 * volume (tMid ∩ u)) := by rw [hunnormApply]
    _ = (2 * volume (tMid ∩ u)) / (2 * volume tMid) := by
          rw [hmassSource, ← ENNReal.div_eq_inv_mul]
    _ = volume (tMid ∩ u) / volume tMid := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (ENNReal.mul_div_mul_left (volume (tMid ∩ u)) (volume tMid) (by norm_num)
              (by norm_num))
    _ = (volume tMid)⁻¹ * volume (tMid ∩ u) := by rw [ENNReal.div_eq_inv_mul]
    _ = (volume p)⁻¹ * volume (p ∩ u) := by rw [hmassTarget, htargetApply]
    _ = volume[|p] u := by rw [ProbabilityTheory.cond_apply' hu]

-- Proof sketch: pass to polar coordinates on the disc. The angular component is independent of
-- the radius and is uniform on the full circle; pushing that law forward by the principal-angle
-- map gives the uniform law on `[-π / 2, π / 2]`.
/-- For Exercise 8.3.3 (3): for the uniform law on the unit disc, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on
`[-π / 2, π / 2]` for `P.map R`-almost every `r`. -/
-- Route correction: instead of rebuilding a pair-map factorization on `ℝ²`, transport the disc
-- law to the polar domain via `polarCoord.symm`, compute the conditional law there with
-- `condDistrib_map`, and only at the end push the full-angle row through `foldPolarAngle`.
theorem condDistrib_principalAngle_given_radius_unitDisc_ae_eq_uniform_interval :
    ∀ᵐ r ∂(unitDiscUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitDiscUniformMeasure r =
        volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := by
  have hmeasPlanarRadius : Measurable planarRadius := by
    fun_prop
  have hmeasPrincipalAngle : Measurable principalAngle := by
    fun_prop
  have hRadiusAe :
      planarRadius ∘ polarCoord.symm =ᵐ[discPolarMeasure] Prod.fst := by
    -- Proof comment: on the polar target, the radius collapses to the first coordinate.
    filter_upwards [ae_mem_polarTarget_discPolarMeasure] with p hp
    simpa [Function.comp_def] using planarRadius_polarCoord_symm_of_mem_target hp
  have hAngleAe :
      principalAngle ∘ polarCoord.symm =ᵐ[discPolarMeasure] foldPolarAngle ∘ Prod.snd := by
    -- Proof comment: on the polar target, the textbook angle is the folded second coordinate.
    filter_upwards [ae_mem_polarTarget_discPolarMeasure] with p hp
    simpa [Function.comp_def] using principalAngle_polarCoord_symm hp
  have hmapRadiusFromPolar :
      unitDiscUniformMeasure.map planarRadius = discPolarMeasure.map Prod.fst := by
    -- Proof comment: push the disc law back to polar coordinates and then replace the radius by
    -- the first polar coordinate almost everywhere.
    calc
      unitDiscUniformMeasure.map planarRadius
          = discPolarMeasure.map (planarRadius ∘ polarCoord.symm) := by
              rw [← unitDiscUniformMeasure_eq_map_discPolarMeasure,
                Measure.map_map hmeasPlanarRadius continuous_polarCoord_symm.measurable]
      _ = discPolarMeasure.map Prod.fst := Measure.map_congr hRadiusAe
  have hcondMap :
      condDistrib principalAngle planarRadius unitDiscUniformMeasure =ᵐ[unitDiscUniformMeasure.map planarRadius]
        condDistrib (principalAngle ∘ polarCoord.symm) (planarRadius ∘ polarCoord.symm)
          discPolarMeasure := by
    have h :
        condDistrib principalAngle planarRadius (discPolarMeasure.map polarCoord.symm) =ᵐ[
          discPolarMeasure.map (planarRadius ∘ polarCoord.symm)]
          condDistrib (principalAngle ∘ polarCoord.symm) (planarRadius ∘ polarCoord.symm)
            discPolarMeasure :=
      condDistrib_map hmeasPlanarRadius.aemeasurable hmeasPrincipalAngle.aemeasurable
        continuous_polarCoord_symm.aemeasurable
    have hfilter :
        discPolarMeasure.map (planarRadius ∘ polarCoord.symm) =
          unitDiscUniformMeasure.map planarRadius := by
      calc
        discPolarMeasure.map (planarRadius ∘ polarCoord.symm)
            = (discPolarMeasure.map polarCoord.symm).map planarRadius := by
                symm
                rw [Measure.map_map hmeasPlanarRadius continuous_polarCoord_symm.measurable]
        _ = unitDiscUniformMeasure.map planarRadius := by
              rw [unitDiscUniformMeasure_eq_map_discPolarMeasure]
    simpa [hfilter, unitDiscUniformMeasure_eq_map_discPolarMeasure] using h
  have hpolar :
      condDistrib principalAngle planarRadius unitDiscUniformMeasure =ᵐ[unitDiscUniformMeasure.map planarRadius]
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst discPolarMeasure := by
    -- Proof comment: after the source move to polar coordinates, rewrite both observables to the
    -- canonical radius/full-angle pair on the polar source.
    simpa [condDistrib_congr hAngleAe hRadiusAe] using hcondMap
  have hcomp :
      ∀ᵐ r ∂(discPolarMeasure.map Prod.fst),
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst discPolarMeasure r =
          (condDistrib Prod.snd Prod.fst discPolarMeasure).map foldPolarAngle r := by
    -- Proof comment: pushing the angular observable through `foldPolarAngle` is exactly the
    -- `condDistrib_comp` transport.
    simpa [Function.comp_def] using
      (condDistrib_comp Prod.fst measurable_snd.aemeasurable measurable_foldPolarAngle)
  have hfoldCircle :
      Measure.map foldPolarAngle (volume[|Set.Ioo (-Real.pi) Real.pi]) =
        volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := by
    -- Proof comment: the square fold theorem at radius `1` specializes to the full unit-circle
    -- angle law because the square support conditions become vacuous.
    have hfull :
        squareFullAngleSupport (1 : ℝ) = Set.Ioo (-Real.pi) Real.pi := by
      ext θ
      simp [squareFullAngleSupport, Real.abs_cos_le_one, Real.abs_sin_le_one]
    have hprincipal :
        squarePrincipalAngleSupport (1 : ℝ) = Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      ext θ
      simp [squarePrincipalAngleSupport, Real.abs_cos_le_one, Real.abs_sin_le_one]
    simpa [hfull, hprincipal] using map_foldPolarAngle_uniformSquareSupport (1 : ℝ)
  have hrows :
      ∀ᵐ r ∂(discPolarMeasure.map Prod.fst),
        (condDistrib Prod.snd Prod.fst discPolarMeasure).map foldPolarAngle r =
          volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := by
    -- Proof comment: the full-angle conditional rows are uniform on the whole circle, so after
    -- folding they become the uniform principal-angle law on `[-π/2, π/2]`.
    filter_upwards [condDistrib_snd_given_fst_discPolar_ae_eq_uniformCircle] with r hr
    rw [Kernel.map_apply _ measurable_foldPolarAngle]
    calc
      Measure.map foldPolarAngle (condDistrib Prod.snd Prod.fst discPolarMeasure r)
          = Measure.map foldPolarAngle (volume[|Set.Ioo (-Real.pi) Real.pi]) := by rw [hr]
      _ = volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := hfoldCircle
  have hpolarRows :
      ∀ᵐ r ∂(unitDiscUniformMeasure.map planarRadius),
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst discPolarMeasure r =
          volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := by
    -- Proof comment: now merge the rowwise pushforward with the radius-measure identification.
    have hcombined :
        ∀ᵐ r ∂(discPolarMeasure.map Prod.fst),
          condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst discPolarMeasure r =
            volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] :=
      Filter.EventuallyEq.trans hcomp hrows
    simpa [hmapRadiusFromPolar] using hcombined
  exact hpolar.trans hpolarRows

-- Proof sketch: condition on the radius and describe the fiber as the arc of the circle of radius
-- `r` lying in `[-1,1]^2`. The conditional law is uniform in arc length on that fiber, and the
-- principal-angle map pushes it forward to the conditioned Lebesgue measure on the angle support.
/-- Exercise 8.3.3 (4): for the uniform law on `[-1,1]^2`, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on the
principal-angle support cut out by the circle of radius `r` inside the square, for `P.map R`-almost
every `r`. -/
-- Route correction: first move the square law to the polar domain, where the support is the
-- measurable family `squareFullAngleSupport`; after computing the full-angle conditional law
-- there, push each row forward by `foldPolarAngle`.
theorem condDistrib_principalAngle_given_radius_unitSquare_ae_eq_uniform_support :
    ∀ᵐ r ∂(unitSquareUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitSquareUniformMeasure r =
        volume[|squarePrincipalAngleSupport r] := by
  have hmeasPlanarRadius : Measurable planarRadius := by
    fun_prop
  have hmeasPrincipalAngle : Measurable principalAngle := by
    fun_prop
  have hRadiusAe :
      planarRadius ∘ polarCoord.symm =ᵐ[squarePolarMeasure] Prod.fst := by
    -- Proof comment: on the polar target, the radius again collapses to the first coordinate.
    filter_upwards [ae_mem_polarTarget_squarePolarMeasure] with p hp
    simpa [Function.comp_def] using planarRadius_polarCoord_symm_of_mem_target hp
  have hAngleAe :
      principalAngle ∘ polarCoord.symm =ᵐ[squarePolarMeasure] foldPolarAngle ∘ Prod.snd := by
    -- Proof comment: on the polar target, the principal angle is the folded second coordinate.
    filter_upwards [ae_mem_polarTarget_squarePolarMeasure] with p hp
    simpa [Function.comp_def] using principalAngle_polarCoord_symm hp
  have hmapRadiusFromPolar :
      unitSquareUniformMeasure.map planarRadius = squarePolarMeasure.map Prod.fst := by
    -- Proof comment: transport the radius observable through the polar parametrization of the
    -- square law.
    calc
      unitSquareUniformMeasure.map planarRadius
          = squarePolarMeasure.map (planarRadius ∘ polarCoord.symm) := by
              rw [← unitSquareUniformMeasure_eq_map_squarePolarMeasure,
                Measure.map_map hmeasPlanarRadius continuous_polarCoord_symm.measurable]
      _ = squarePolarMeasure.map Prod.fst := Measure.map_congr hRadiusAe
  have hcondMap :
      condDistrib principalAngle planarRadius unitSquareUniformMeasure =ᵐ[unitSquareUniformMeasure.map planarRadius]
        condDistrib (principalAngle ∘ polarCoord.symm) (planarRadius ∘ polarCoord.symm)
          squarePolarMeasure := by
    have h :
        condDistrib principalAngle planarRadius (squarePolarMeasure.map polarCoord.symm) =ᵐ[
          squarePolarMeasure.map (planarRadius ∘ polarCoord.symm)]
          condDistrib (principalAngle ∘ polarCoord.symm) (planarRadius ∘ polarCoord.symm)
            squarePolarMeasure :=
      condDistrib_map hmeasPlanarRadius.aemeasurable hmeasPrincipalAngle.aemeasurable
        continuous_polarCoord_symm.aemeasurable
    have hfilter :
        squarePolarMeasure.map (planarRadius ∘ polarCoord.symm) =
          unitSquareUniformMeasure.map planarRadius := by
      calc
        squarePolarMeasure.map (planarRadius ∘ polarCoord.symm)
            = (squarePolarMeasure.map polarCoord.symm).map planarRadius := by
                symm
                rw [Measure.map_map hmeasPlanarRadius continuous_polarCoord_symm.measurable]
        _ = unitSquareUniformMeasure.map planarRadius := by
              rw [unitSquareUniformMeasure_eq_map_squarePolarMeasure]
    simpa [hfilter, unitSquareUniformMeasure_eq_map_squarePolarMeasure] using h
  have hpolar :
      condDistrib principalAngle planarRadius unitSquareUniformMeasure =ᵐ[unitSquareUniformMeasure.map planarRadius]
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst squarePolarMeasure := by
    -- Proof comment: after transporting to the polar source, rewrite to the canonical radius and
    -- full-angle observables there.
    simpa [condDistrib_congr hAngleAe hRadiusAe] using hcondMap
  have hcomp :
      ∀ᵐ r ∂(squarePolarMeasure.map Prod.fst),
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst squarePolarMeasure r =
          (condDistrib Prod.snd Prod.fst squarePolarMeasure).map foldPolarAngle r := by
    -- Proof comment: compose the full-angle conditional rows with the measurable fold map.
    simpa [Function.comp_def] using
      (condDistrib_comp Prod.fst measurable_snd.aemeasurable measurable_foldPolarAngle)
  have hrows :
      ∀ᵐ r ∂(squarePolarMeasure.map Prod.fst),
        (condDistrib Prod.snd Prod.fst squarePolarMeasure).map foldPolarAngle r =
          volume[|squarePrincipalAngleSupport r] := by
    -- Proof comment: fold each full-angle row through the measure-level pushforward theorem proved
    -- above.
    filter_upwards [condDistrib_snd_given_fst_squarePolar_ae_eq_uniformSupport] with r hr
    rw [Kernel.map_apply _ measurable_foldPolarAngle]
    calc
      Measure.map foldPolarAngle (condDistrib Prod.snd Prod.fst squarePolarMeasure r)
          = Measure.map foldPolarAngle (volume[|squareFullAngleSupport r]) := by rw [hr]
      _ = volume[|squarePrincipalAngleSupport r] := map_foldPolarAngle_uniformSquareSupport r
  have hpolarRows :
      ∀ᵐ r ∂(unitSquareUniformMeasure.map planarRadius),
        condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst squarePolarMeasure r =
          volume[|squarePrincipalAngleSupport r] := by
    -- Proof comment: transfer the rowwise result back along the identified radius marginal.
    have hcombined :
        ∀ᵐ r ∂(squarePolarMeasure.map Prod.fst),
          condDistrib (foldPolarAngle ∘ Prod.snd) Prod.fst squarePolarMeasure r =
            volume[|squarePrincipalAngleSupport r] :=
      Filter.EventuallyEq.trans hcomp hrows
    simpa [hmapRadiusFromPolar] using hcombined
  exact hpolar.trans hpolarRows
