/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

-- Declarations for this item will be appended below by the statement pipeline.

open Function MeasureTheory Set

open scoped BigOperators Topology

noncomputable section

/-- Helper for Exercise 14.2.3: the real-valued mass of `(a, x]` under the Stieltjes measure of
`F` is `F x - F a`. -/
lemma stieltjesMeasureRealIocEqSub (F : StieltjesFunction ℝ) {a x : ℝ} (hax : a ≤ x) :
    F.measure.real (Ioc a x) = F x - F a := by
  -- Convert the interval mass formula from `ENNReal` to its real-valued version.
  rw [MeasureTheory.measureReal_def, StieltjesFunction.measure_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hax))

/-- Helper for Exercise 14.2.3: the real-valued mass of `[x, b]` under the Stieltjes measure of
`F` is `F b - leftLim F x`. -/
lemma stieltjesMeasureRealIccEqSubLeftLim (F : StieltjesFunction ℝ) {x b : ℝ} (hxb : x ≤ b) :
    F.measure.real (Icc x b) = F b - leftLim F x := by
  -- Convert the closed-interval Stieltjes mass formula to `ℝ`.
  rw [MeasureTheory.measureReal_def, StieltjesFunction.measure_Icc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono.leftLim_le hxb))

/-- Helper for Exercise 14.2.3: the real-valued mass of a singleton under the Stieltjes measure
of `F` is the jump height `F x - leftLim F x`. -/
lemma stieltjesMeasureRealSingletonEqJump (F : StieltjesFunction ℝ) (x : ℝ) :
    F.measure.real {x} = F x - leftLim F x := by
  -- Convert the singleton-mass formula to `ℝ`.
  rw [MeasureTheory.measureReal_def, StieltjesFunction.measure_singleton]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono.leftLim_le le_rfl))

/-- Helper for Exercise 14.2.3: the lower-triangle indicator is integrable on the rectangle
`Ioc a b ×ˢ Ioc a b` for the product Stieltjes measure `Fν.measure.prod Fμ.measure`. -/
lemma lowerTriangleRectangleIntegrable
    (Fμ Fν : StieltjesFunction ℝ) (a b : ℝ) :
    IntegrableOn (({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)))
      (Ioc a b ×ˢ Ioc a b) (Fν.measure.prod Fμ.measure) := by
  -- The product rectangle has finite mass, so the constant function stays integrable there.
  have hrectFinite : (Fν.measure.prod Fμ.measure) (Ioc a b ×ˢ Ioc a b) ≠ ⊤ := by
    have hνFinite : Fν.measure (Ioc a b) ≠ ⊤ := by
      simp [StieltjesFunction.measure_Ioc]
    have hμFinite : Fμ.measure (Ioc a b) ≠ ⊤ := by
      simp [StieltjesFunction.measure_Ioc]
    simpa [Measure.prod_prod] using ENNReal.mul_ne_top hνFinite hμFinite
  have htriangleMeas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := by
    -- The lower triangle is closed because it is defined by the closed relation `p.2 ≤ p.1`.
    exact (isClosed_le continuous_snd continuous_fst).measurableSet
  exact
    (integrableOn_const
      (μ := Fν.measure.prod Fμ.measure) (s := Ioc a b ×ˢ Ioc a b) hrectFinite).indicator
      htriangleMeas

/-- Helper for Exercise 14.2.3: fixing `x ∈ Ioc a b`, the lower-triangle section inside
`Ioc a b` is exactly the interval `(a, x]`. -/
lemma lowerTriangleSectionIoc
    (Fμ : StieltjesFunction ℝ) {a b x : ℝ} (hx : x ∈ Ioc a b) :
    ∫ y in Ioc a b, ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y) ∂Fμ.measure =
      ∫ y in Ioc a x, (fun _ : ℝ ↦ (1 : ℝ)) y ∂Fμ.measure := by
  have hsection :
      EqOn
        (fun y : ℝ ↦ ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y))
        ((Ioc a x).indicator fun _ : ℝ ↦ (1 : ℝ))
        (Ioc a b) := by
    intro y hy
    by_cases hxy : y ≤ x
    · -- Inside the lower triangle, the indicator agrees with the indicator of `(a, x]`.
      have hyx : y ∈ Ioc a x := ⟨hy.1, hxy⟩
      simp [hxy, hyx]
    · -- Outside the section `(a, x]`, both indicators vanish.
      have hyx : y ∉ Ioc a x := by
        intro hyx
        exact hxy hyx.2
      simp [hxy, hyx]
  have hsectionSet : Ioc a b ∩ Ioc a x = Ioc a x := by
    ext y
    constructor
    · intro hy
      exact hy.2
    · intro hy
      exact ⟨⟨hy.1, le_trans hy.2 hx.2⟩, hy⟩
  calc
    ∫ y in Ioc a b, ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y)
        ∂Fμ.measure
        = ∫ y in Ioc a b, ((Ioc a x).indicator fun _ : ℝ ↦ (1 : ℝ)) y ∂Fμ.measure := by
            -- Replace the section by the interval indicator on the ambient rectangle.
            exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hsection
    _ = ∫ y in Ioc a b ∩ Ioc a x, (1 : ℝ) ∂Fμ.measure := by
          -- Restricting by an indicator shrinks the domain to the intersection.
          rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    _ = ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure := by
          -- Since `x ∈ Ioc a b`, intersecting with `Ioc a b` does not change `(a, x]`.
          simp [hsectionSet]

/-- Helper for Exercise 14.2.3: fixing `y ∈ Ioc a b`, the lower-triangle section inside
`Ioc a b` is exactly the interval `[y, b]`. -/
lemma lowerTriangleSectionIcc
    (Fν : StieltjesFunction ℝ) {a b y : ℝ} (hy : y ∈ Ioc a b) :
    ∫ x in Ioc a b, ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y) ∂Fν.measure =
      ∫ x in Icc y b, (fun _ : ℝ ↦ (1 : ℝ)) x ∂Fν.measure := by
  have hsection :
      EqOn
        (fun x : ℝ ↦ ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y))
        ((Ici y).indicator fun _ : ℝ ↦ (1 : ℝ))
        (Ioc a b) := by
    intro x hx
    by_cases hyx : y ≤ x
    · -- On the lower triangle, the section is the ray `Ici y`.
      have hxray : x ∈ Ici y := hyx
      simp [hyx, hxray]
    · -- Outside that ray, both indicators are zero.
      have hxray : x ∉ Ici y := hyx
      simp [hyx, hxray]
  have hsectionSet : Ioc a b ∩ Ici y = Icc y b := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, hx.1.2⟩
    · intro hx
      exact ⟨⟨lt_of_lt_of_le hy.1 hx.1, hx.2⟩, hx.1⟩
  calc
    ∫ x in Ioc a b, ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y)
        ∂Fν.measure
        = ∫ x in Ioc a b, ((Ici y).indicator fun _ : ℝ ↦ (1 : ℝ)) x ∂Fν.measure := by
            -- Replace the fixed-`y` section by the interval indicator of `Ici y`.
            exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hsection
    _ = ∫ x in Ioc a b ∩ Ici y, (1 : ℝ) ∂Fν.measure := by
          -- Intersecting with the indicator domain isolates the relevant section.
          rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
    _ = ∫ x in Icc y b, (1 : ℝ) ∂Fν.measure := by
          -- Because `y ∈ Ioc a b`, this intersection is precisely `[y, b]`.
          simp [hsectionSet]

/-- Helper for Exercise 14.2.3: the lower-triangle section integrals over `(a, b]²` agree after
swapping the order of integration. -/
lemma triangleSectionIntegralSwap
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (_hab : a < b) :
    ∫ x in Ioc a b, (∫ y in Ioc a x, (fun _ : ℝ ↦ (1 : ℝ)) y ∂Fμ.measure) ∂Fν.measure =
      ∫ y in Ioc a b, (∫ x in Icc y b, (fun _ : ℝ ↦ (1 : ℝ)) x ∂Fν.measure) ∂Fμ.measure := by
  let triFun : ℝ → ℝ → ℝ :=
    fun x y ↦ ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun _ ↦ (1 : ℝ)) (x, y)
  have htriInt :
      Integrable (uncurry triFun)
        ((Fν.measure.restrict (Ioc a b)).prod (Fμ.measure.restrict (Ioc a b))) := by
    -- The rectangle indicator remains integrable after rewriting set integrals as restricted
    -- product integrals.
    simpa [triFun, IntegrableOn, ← Measure.prod_restrict] using
      lowerTriangleRectangleIntegrable Fμ Fν a b
  -- Route correction: swap the two restricted integrals directly via `integral_integral_swap`,
  -- then rewrite the fixed sections back to the intervals `(a, x]` and `[y, b]`.
  calc
    ∫ x in Ioc a b, (∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure) ∂Fν.measure
        = ∫ x in Ioc a b,
            (∫ y in Ioc a b, triFun x y ∂Fμ.measure)
            ∂Fν.measure := by
              -- Normalize each inner section to the lower-triangle indicator on the rectangle.
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
              intro x hx
              symm
              simpa [triFun] using lowerTriangleSectionIoc Fμ hx
    _ = ∫ y in Ioc a b,
          (∫ x in Ioc a b, triFun x y ∂Fν.measure)
          ∂Fμ.measure := by
            -- Swap the restricted iterated integrals on the rectangle in one step.
            simpa [triFun] using
              (MeasureTheory.integral_integral_swap
                (μ := Fν.measure.restrict (Ioc a b))
                (ν := Fμ.measure.restrict (Ioc a b))
                (f := triFun) htriInt)
    _ = ∫ y in Ioc a b, (∫ x in Icc y b, (1 : ℝ) ∂Fν.measure) ∂Fμ.measure := by
          -- Each swapped section is exactly the interval `[y, b]`.
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
          intro y hy
          simpa [triFun] using lowerTriangleSectionIcc Fν hy

-- Proof sketch: apply Stieltjes integration by parts on `(a, b]` for the two Stieltjes measures
-- associated to `Fμ` and `Fν`, and use the boundary terms together with the left-limit version of
-- the Stieltjes integral.
/-- Exercise 14.2.3: for two distribution functions `F_μ` and `F_ν` of locally finite measures on
`ℝ`, partial integration on `(a, b]` identifies the integral of `F_μ` against `dν` with the
boundary term `F_μ(b) F_ν(b) - F_μ(a) F_ν(a)` minus the integral of the left limit `F_ν(x-)`
against `dμ`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_leftLimIntegral
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure := by
  have hIocμFinite : Fμ.measure (Ioc a b) ≠ ⊤ := by
    -- The Stieltjes mass of `(a, b]` is explicitly finite.
    simp [StieltjesFunction.measure_Ioc]
  have hIocνFinite : Fν.measure (Ioc a b) ≠ ⊤ := by
    -- The same finiteness holds for `Fν`.
    simp [StieltjesFunction.measure_Ioc]
  have hconstμInt : IntegrableOn (fun _ : ℝ ↦ Fμ a) (Ioc a b) Fν.measure :=
    integrableOn_const hIocνFinite
  have hconstνInt : IntegrableOn (fun _ : ℝ ↦ Fν b) (Ioc a b) Fμ.measure :=
    integrableOn_const hIocμFinite
  have hFμUpperInt : IntegrableOn (fun _ : ℝ ↦ Fμ b) (Ioc a b) Fν.measure :=
    integrableOn_const hIocνFinite
  have hFμInt : IntegrableOn Fμ (Ioc a b) Fν.measure := by
    -- On `(a, b]`, monotonicity traps `Fμ` between the two endpoint constants.
    rw [IntegrableOn]
    refine integrable_of_le_of_le (Fμ.mono.measurable.aestronglyMeasurable.restrict) ?_ ?_
      hconstμInt hFμUpperInt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fμ.mono hx.1.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fμ.mono hx.2
  have hLeftLowerInt : IntegrableOn (fun _ : ℝ ↦ Fν a) (Ioc a b) Fμ.measure :=
    integrableOn_const hIocμFinite
  have hLeftLimInt : IntegrableOn (leftLim Fν) (Ioc a b) Fμ.measure := by
    -- The left limit is likewise bounded by the endpoint values on `(a, b]`.
    rw [IntegrableOn]
    refine integrable_of_le_of_le (((Fν.mono.leftLim).measurable).aestronglyMeasurable.restrict)
      ?_ ?_ hLeftLowerInt hconstνInt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono.le_leftLim hx.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono.leftLim_le hx.2
  have htriangleInt :
      IntegrableOn (fun x ↦ ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure) (Ioc a b) Fν.measure := by
    -- The inner section integral is just `Fμ x - Fμ a` on `(a, b]`.
    refine (hFμInt.sub hconstμInt).congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hx' : ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure = Fμ x - Fμ a := by
      rw [MeasureTheory.setIntegral_one_eq_measureReal, stieltjesMeasureRealIocEqSub Fμ hx.1.le]
    simp [hx']
  have hsplit (x : ℝ) (hx : x ∈ Ioc a b) :
      Fμ x = Fμ a + ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure := by
    -- Rewrite `Fμ x` as the left endpoint plus the Stieltjes mass of `(a, x]`.
    have hx' : ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure = Fμ x - Fμ a := by
      rw [MeasureTheory.setIntegral_one_eq_measureReal, stieltjesMeasureRealIocEqSub Fμ hx.1.le]
    linarith
  have hswapSection (y : ℝ) (hy : y ∈ Ioc a b) :
      ∫ x in Icc y b, (1 : ℝ) ∂Fν.measure = Fν b - leftLim Fν y := by
    -- After swapping the triangle, the section becomes `[y, b]`.
    rw [MeasureTheory.setIntegral_one_eq_measureReal,
      stieltjesMeasureRealIccEqSubLeftLim Fν hy.2]
  calc
    ∫ x in Ioc a b, Fμ x ∂Fν.measure
        = ∫ x in Ioc a b, (Fμ a + ∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure) ∂Fν.measure := by
            -- Expand `Fμ x` into an endpoint term plus a section integral.
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
            intro x hx
            exact hsplit x hx
    _ = ∫ x in Ioc a b, (fun _ : ℝ ↦ Fμ a) x ∂Fν.measure
          + ∫ x in Ioc a b, (∫ y in Ioc a x, (1 : ℝ) ∂Fμ.measure) ∂Fν.measure := by
            -- Separate the constant boundary contribution from the triangle term.
            simpa using integral_add hconstμInt htriangleInt
    _ = Fν.measure.real (Ioc a b) * Fμ a
          + ∫ y in Ioc a b, (∫ x in Icc y b, (1 : ℝ) ∂Fν.measure) ∂Fμ.measure := by
            -- The remaining double integral is the triangle integral with swapped order.
            rw [MeasureTheory.setIntegral_const, smul_eq_mul,
              triangleSectionIntegralSwap Fμ Fν hab]
    _ = Fμ a * (Fν b - Fν a)
          + ∫ y in Ioc a b, (∫ x in Icc y b, (1 : ℝ) ∂Fν.measure) ∂Fμ.measure := by
            -- Rewrite the outer interval mass in terms of the endpoint values of `Fν`.
            rw [stieltjesMeasureRealIocEqSub Fν hab.le]
            ring
    _ = Fμ a * (Fν b - Fν a)
          + ∫ y in Ioc a b, (Fν b - leftLim Fν y) ∂Fμ.measure := by
            -- Replace each swapped section by the corresponding `[y, b]` mass.
            refine congrArg (fun t => Fμ a * (Fν b - Fν a) + t) ?_
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
            intro y hy
            exact hswapSection y hy
    _ = Fμ a * (Fν b - Fν a)
          + (∫ y in Ioc a b, (fun _ : ℝ ↦ Fν b) y ∂Fμ.measure
            - ∫ y in Ioc a b, leftLim Fν y ∂Fμ.measure) := by
              -- Split off the constant `Fν b` from the left-limit integral.
              congr 1
              simpa using integral_sub hconstνInt hLeftLimInt
    _ = Fμ a * (Fν b - Fν a)
          + (Fμ.measure.real (Ioc a b) * Fν b - ∫ y in Ioc a b, leftLim Fν y ∂Fμ.measure) := by
              -- Evaluate the constant integral over `(a, b]`.
              rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    _ = Fμ a * (Fν b - Fν a)
          + (Fν b * (Fμ b - Fμ a) - ∫ y in Ioc a b, leftLim Fν y ∂Fμ.measure) := by
              -- Rewrite the interval mass of `Fμ` by endpoint values.
              rw [stieltjesMeasureRealIocEqSub Fμ hab.le]
              ring
    _ = Fμ b * Fν b - Fμ a * Fν a - ∫ y in Ioc a b, leftLim Fν y ∂Fμ.measure := by
          -- The algebraic rearrangement now matches the desired boundary formula.
          ring

-- Proof sketch: start from the partial-integration identity with the left-limit integral, then
-- decompose `∫ Fν(x-) dμ` into `∫ Fν dμ` minus the sum of the products of the jumps, using the
-- singleton-mass formula for Stieltjes measures.
/-- A companion reformulation of partial integration replaces the left-limit integral by the
ordinary integral of `F_ν` against `dμ` plus the sum of the products of the jump heights on
`(a, b]`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_integral_add_jumpSum
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, Fν x ∂Fμ.measure +
          ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * (Fν x - leftLim Fν x) := by
  let jump : ℝ → ℝ := fun x ↦ Fν x - leftLim Fν x
  have hIocμFinite : Fμ.measure (Ioc a b) ≠ ⊤ := by
    -- The restricted Stieltjes measure on `(a, b]` is finite.
    simp [StieltjesFunction.measure_Ioc]
  have hIocνFinite : Fν.measure (Ioc a b) ≠ ⊤ := by
    -- We use the same finiteness for the symmetric integral.
    simp [StieltjesFunction.measure_Ioc]
  have hFνLowerInt : IntegrableOn (fun _ : ℝ ↦ Fν a) (Ioc a b) Fμ.measure :=
    integrableOn_const hIocμFinite
  have hFνUpperInt : IntegrableOn (fun _ : ℝ ↦ Fν b) (Ioc a b) Fμ.measure :=
    integrableOn_const hIocμFinite
  have hFνInt : IntegrableOn Fν (Ioc a b) Fμ.measure := by
    -- On `(a, b]`, monotonicity bounds `Fν` between its endpoint values.
    rw [IntegrableOn]
    refine integrable_of_le_of_le (Fν.mono.measurable.aestronglyMeasurable.restrict) ?_ ?_
      hFνLowerInt hFνUpperInt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono hx.1.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono hx.2
  have hLeftLimInt : IntegrableOn (leftLim Fν) (Ioc a b) Fμ.measure := by
    -- The left limit enjoys the same endpoint bounds on `(a, b]`.
    rw [IntegrableOn]
    refine integrable_of_le_of_le (((Fν.mono.leftLim).measurable).aestronglyMeasurable.restrict)
      ?_ ?_ hFνLowerInt hFνUpperInt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono.le_leftLim hx.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Fν.mono.leftLim_le hx.2
  have hjumpInt : IntegrableOn jump (Ioc a b) Fμ.measure := by
    -- The jump function is the difference between `Fν` and its left limit.
    simpa [jump, sub_eq_add_neg] using hFνInt.sub hLeftLimInt
  let μsub : Measure (Ioc a b) := Measure.comap Subtype.val Fμ.measure
  let s : Set (Ioc a b) := {x | leftLim Fν x ≠ Fν x}
  have hs_count : s.Countable := by
    -- Jumps occur only at countably many points, even after restricting to `(a, b]`.
    simpa [s] using
      (Fν.countable_leftLim_ne.preimage
        (Subtype.val_injective : Injective (Subtype.val : Ioc a b → ℝ)))
  have hs_meas : MeasurableSet s := hs_count.measurableSet
  have hjumpSubInt : Integrable (fun x : Ioc a b ↦ jump x) μsub := by
    -- Move the jump integral from `(a, b]` to the corresponding subtype measure.
    let hsubtype : MeasurableEmbedding (Subtype.val : Ioc a b → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ioc
    have hmapInt : Integrable jump (Measure.map (Subtype.val : Ioc a b → ℝ) μsub) := by
      simpa [μsub, IntegrableOn, map_comap_subtype_coe measurableSet_Ioc] using hjumpInt
    exact hsubtype.integrable_map_iff.mp hmapInt
  have hsubtypeRestrict :
      ∫ x : Ioc a b, jump x ∂μsub = ∫ x in s, jump x ∂μsub := by
    calc
      ∫ x : Ioc a b, jump x ∂μsub = ∫ x in (univ : Set (Ioc a b)), jump x ∂μsub := by
            simp
      _ = ∫ x in (univ : Set (Ioc a b)), s.indicator (fun x : Ioc a b ↦ jump x) x ∂μsub := by
            -- Outside the jump set, the jump function vanishes identically.
            refine MeasureTheory.setIntegral_congr_fun MeasurableSet.univ ?_
            intro x hx
            by_cases hsx : x ∈ s
            · simp [s, jump, hsx]
            · have hsx' : leftLim Fν x = Fν x := by
                by_contra hneq
                exact hsx hneq
              simp [s, jump, hsx, hsx']
      _ = ∫ x in s, jump x ∂μsub := by
            -- Restrict the integral to the countable jump support.
            rw [MeasureTheory.setIntegral_indicator hs_meas]
            simp
  have hsingleton (x : s) :
      μsub.real ({(x : Ioc a b)} : Set (Ioc a b)) = Fμ x - leftLim Fμ x := by
    -- A singleton in the subtype carries exactly the jump mass of `Fμ` at that point.
    unfold μsub
    rw [MeasureTheory.measureReal_def,
      Measure.comap_apply Subtype.val Subtype.coe_injective
        (fun t ht ↦ MeasurableSet.subtype_image measurableSet_Ioc ht) _
        (MeasurableSet.singleton (x : Ioc a b))]
    simp only [Set.image_singleton]
    rw [StieltjesFunction.measure_singleton]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Fμ.mono.leftLim_le le_rfl))
  have hcountableEval :
      ∫ x in s, jump x ∂μsub = ∑' x : s, (Fμ x - leftLim Fμ x) * jump x := by
    -- Evaluate the integral over the countable jump set as a `tsum` of singleton masses.
    rw [MeasureTheory.setIntegral_countable _ hs_count hjumpSubInt.integrableOn]
    congr with x
    rw [hsingleton x, smul_eq_mul]
  have hs_support :
      Function.support (fun x : Ioc a b ↦ (Fμ x - leftLim Fμ x) * jump x) ⊆ s := by
    -- The summand vanishes away from jump points of `Fν`.
    intro x hx
    by_contra hxs
    apply hx
    have hxs' : leftLim Fν x = Fν x := by
      by_contra hneq
      exact hxs hneq
    simp [jump, hxs']
  have hjumpSum :
      ∫ x in Ioc a b, jump x ∂Fμ.measure =
        ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * jump x := by
    calc
      ∫ x in Ioc a b, jump x ∂Fμ.measure = ∫ x : Ioc a b, jump x ∂μsub := by
            -- Express the integral over `(a, b]` as an integral on the subtype.
            symm
            exact integral_subtype_comap measurableSet_Ioc jump
      _ = ∫ x in s, jump x ∂μsub := hsubtypeRestrict
      _ = ∑' x : s, (Fμ x - leftLim Fμ x) * jump x := hcountableEval
      _ = ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * jump x :=
            tsum_subtype_eq_of_support_subset hs_support
  have hsplitLeft :
      ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure =
        ∫ x in Ioc a b, Fν x ∂Fμ.measure - ∫ x in Ioc a b, jump x ∂Fμ.measure := by
    calc
      ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure =
          ∫ x in Ioc a b, (Fν x - jump x) ∂Fμ.measure := by
            -- Rewrite the left limit as `Fν - jump`.
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
            intro x hx
            simp [jump]
      _ = ∫ x in Ioc a b, Fν x ∂Fμ.measure - ∫ x in Ioc a b, jump x ∂Fμ.measure := by
            -- The difference splits because both pieces are integrable on `(a, b]`.
            simpa [jump, sub_eq_add_neg] using integral_sub hFνInt hjumpInt
  calc
    ∫ x in Ioc a b, Fμ x ∂Fν.measure
        = Fμ b * Fν b - Fμ a * Fν a - ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure := by
            -- Start from the first partial-integration identity.
            simpa using partialIntegration_stieltjes_eq_boundary_sub_leftLimIntegral Fμ Fν hab
    _ = Fμ b * Fν b - Fμ a * Fν a -
          (∫ x in Ioc a b, Fν x ∂Fμ.measure - ∫ x in Ioc a b, jump x ∂Fμ.measure) := by
            -- Replace the left-limit integral by `∫ Fν - ∫ jump`.
            rw [hsplitLeft]
    _ = Fμ b * Fν b - Fμ a * Fν a - ∫ x in Ioc a b, Fν x ∂Fμ.measure
          + ∫ x in Ioc a b, jump x ∂Fμ.measure := by
            -- Rearrange the subtraction.
            ring
    _ = Fμ b * Fν b - Fμ a * Fν a - ∫ x in Ioc a b, Fν x ∂Fμ.measure
          + ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * jump x := by
            -- Insert the countable jump expansion.
            rw [hjumpSum]
    _ = Fμ b * Fν b - Fμ a * Fν a - ∫ x in Ioc a b, Fν x ∂Fμ.measure
          + ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * (Fν x - leftLim Fν x) := by
            -- Finally unfold the jump notation.
            simp [jump]

end
