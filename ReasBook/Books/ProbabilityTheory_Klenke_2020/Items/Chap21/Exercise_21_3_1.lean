/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19Core
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_20

open MeasureTheory ProbabilityTheory Filter
open Lean Meta Elab Term
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

/-- Helper for Exercise 21.3.1: expose the compiled unit-slice reflection lemma from
`Theorem_21_19Core` without importing the broken `Theorem_21_19.UnitSlice` source file. -/
syntax "theorem21_19CoreUnitSliceReflectedTail" : term

-- Local declaration justification (syntax): the needed reflection lemma only exists as a compiled
-- private declaration in `Theorem_21_19Core`, so a small term elaborator is the least invasive
-- way to reuse it from this target file.
elab_rules : term
  | `(theorem21_19CoreUnitSliceReflectedTail) =>
      mkConstWithFreshMVarLevels
        "_private.Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19Core.0.\
ProbabilityTheory.unitHitUpperBeforeOne_terminalBelow_measure_eq_reflectedTail_core_local".toName

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 21.3.1: the exit time from the interval `(0, a)` for Brownian motion started at `x`
is the first time the centered Brownian path hits one of the translated barriers `-x` or `a - x`.
-/
def brownianIntervalExitTime (W : NNReal → Ω → ℝ) (x a : ℝ) : Ω → ENNReal :=
  fun ω ↦ hittingAfter W ({-x, a - x} : Set ℝ) 0 ω

/-- Exercise 21.3.1: the alternating sign attached to the strip index `n`. -/
def paritySign (n : ℤ) : ℝ :=
  if Even n then 1 else -1

/-- Exercise 21.3.1: the Gaussian mass of the strip `[(n : ℝ) * a, ((n : ℝ) + 1) * a]` under the
terminal law `N(x, T)`. -/
def shiftedStripMass (x a : ℝ) (T : NNReal) (n : ℤ) : ℝ :=
  (gaussianReal x T).real (Set.Icc ((n : ℝ) * a) (((n : ℝ) + 1) * a))

/-- Exercise 21.3.1: the `k`th odd Fourier-sine mode in the interval-survival expansion. -/
def oddSineSurvivalTerm (x a : ℝ) (T : NNReal) (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℝ)⁻¹) *
    Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)) *
    Real.sin ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)

/-- Exercise 21.3.1: pair the centered alternating strip series into the natural `ℕ`-indexed
shells `n` and `-(n + 1)`. -/
def alternatingStripPairShell (x a : ℝ) (T : NNReal) (n : ℕ) : ℝ :=
  paritySign (n : ℤ) * shiftedStripMass x a T (n : ℤ) +
    paritySign (-(n + 1 : ℤ)) * shiftedStripMass x a T (-(n + 1 : ℤ))

/-- Exercise 21.3.1: the continuous Poisson input whose integer samples recover the centered
alternating strip masses. -/
def modulatedStripCellAverage (x a : ℝ) (T : NNReal) (s : ℝ) : ℂ :=
  Complex.exp (Real.pi * s * Complex.I) *
    ∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)

/-- Helper for Exercise 21.3.1: the modulation factor `exp (π n I)` is exactly the textbook
alternating sign at the integer index `n`. -/
theorem paritySign_eq_complexExp_pi_mul_intLocal
    (n : ℤ) :
    Complex.exp (Real.pi * (n : ℝ) * Complex.I) = (paritySign n : ℂ) := by
  have hmul :
      Real.pi * (n : ℝ) * Complex.I = (n : ℂ) * (Real.pi * Complex.I) := by
    norm_num
    ring_nf
  -- Proof comment: rewrite the modulation as an integer power of `exp (π I) = -1`, then use the
  -- parity split built into `paritySign`.
  rw [hmul, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  by_cases hEven : Even n
  · simpa [paritySign, hEven] using (Even.neg_one_zpow (α := ℂ) hEven)
  · rw [paritySign, if_neg hEven]
    have hOdd : Odd n := Int.not_even_iff_odd.mp hEven
    simpa using (Odd.neg_one_zpow (α := ℂ) hOdd)

/-- Helper for Exercise 21.3.1: specializing the Gaussian characteristic function to the odd
Fourier frequency `((2k + 1) * π) / a` packages the exponential phase needed for Poisson
summation. -/
theorem gaussianCharFun_oddModeLocal
    {x a : ℝ} {T : NNReal} (k : ℕ) :
    charFun (gaussianReal x T) ((((2 * k + 1 : ℝ) * Real.pi) / a)) =
      Complex.exp
        (((((2 * k + 1 : ℝ) * Real.pi) / a) * x) * Complex.I -
          (((T : ℝ) * ((((2 * k + 1 : ℝ) * Real.pi) / a) ^ (2 : ℕ))) / 2 : ℝ)) := by
  -- Proof comment: this is the standard Gaussian characteristic-function formula evaluated at the
  -- odd mode `((2k + 1) * π) / a`; only scalar reassociation is needed afterwards.
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (ProbabilityTheory.charFun_gaussianReal
      (μ := x) (v := T) ((((2 * k + 1 : ℝ) * Real.pi) / a)))

/-- Helper for Exercise 21.3.1: the same Gaussian characteristic-function normalization holds for
all integer odd modes, which is the index type used by the Fourier coefficients. -/
theorem gaussianCharFun_oddIntModeLocal
    {x a : ℝ} {T : NNReal} (n : ℤ) :
    charFun (gaussianReal x T) (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)) =
      Complex.exp
        (((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) * x) * Complex.I) -
          (((T : ℝ) * ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)) ^ (2 : ℕ))) / 2 : ℝ)) := by
  -- Proof comment: this is the same owner Gaussian characteristic-function formula, now written
  -- at the integer odd frequencies that appear in the Fourier transform branch.
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (ProbabilityTheory.charFun_gaussianReal
      (μ := x) (v := T) (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)))

/-- Helper for Exercise 21.3.1: the Fourier transform convention uses the negative odd frequency,
so we record the conjugation bridge from the positive odd frequency to `-((2 * n + 1) * π / a)`.
-/
theorem gaussianCharFun_neg_oddIntModeLocal
    {x a : ℝ} {T : NNReal} (n : ℤ) :
    charFun (gaussianReal x T) (-(((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a))) =
      star
        (charFun (gaussianReal x T) (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a))) := by
  -- Proof comment: the negative Fourier frequency is the complex conjugate of the positive one,
  -- which is the exact sign bridge needed before pairing opposite odd modes.
  simpa using
    (MeasureTheory.charFun_neg
      (μ := gaussianReal x T) (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)))

/-- Helper for Exercise 21.3.1: the paired Fourier indices `n` and `-(n + 1)` correspond to odd
frequencies of opposite sign. -/
theorem oddModeFrequency_neg_add_oneLocal
    {a : ℝ} (n : ℕ) :
    (((((2 * (-(n + 1 : ℤ)) + 1 : ℤ) : ℝ) * Real.pi) / a)) =
      -(((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)) := by
  -- Proof comment: the arithmetic identity `2 * (-(n + 1)) + 1 = -(2 * n + 1)` is the exact
  -- frequency pairing used when the Fourier series is regrouped into the shells `n` and `-(n+1)`.
  push_cast
  ring

/-- Helper for Exercise 21.3.1: for a positive-time Gaussian law, removing the left endpoint of a
strip does not change its real-valued mass. -/
theorem gaussianStripReal_Icc_eq_Ioc
    {m : ℝ} {T : NNReal} (hT : 0 < T) (l u : ℝ) :
    (gaussianReal m T).real (Set.Icc l u) = (gaussianReal m T).real (Set.Ioc l u) := by
  -- Proof comment: positive-time Gaussian laws are atomless, so the boundary point `l` carries no
  -- mass and `Icc l u` has the same measure as `Ioc l u`.
  exact
    (MeasureTheory.measureReal_congr
      (MeasureTheory.Ioc_ae_eq_Icc'
        ((ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton l))).symm

/-- Helper for Exercise 21.3.1: shifting the centered Brownian terminal value by the deterministic
start point `x` gives the Gaussian law `N(x, T)`. -/
theorem shiftedBrownianTerminalReal_eq_gaussianReal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} {T : NNReal} (hT : 0 < T) {s : Set ℝ} (hs : MeasurableSet s) :
    μ.real {ω | x + W T ω ∈ s} = (gaussianReal x T).real s := by
  have hLaw : HasLaw (fun ω ↦ x + W T ω) (gaussianReal x T) μ := by
    -- Proof comment: adding the deterministic offset `x` to the centered Gaussian marginal
    -- transports `N(0, T)` to `N(x, T)`.
    simpa [add_comm] using ProbabilityTheory.gaussianReal_add_const (hW.gaussian_marginal hT) x
  -- Proof comment: once the terminal law is identified, the strip event is just the preimage of
  -- `s` under the terminal random variable.
  calc
    μ.real {ω | x + W T ω ∈ s} = μ.real ((fun ω ↦ x + W T ω) ⁻¹' s) := by
      rfl
    _ = (μ.map (fun ω ↦ x + W T ω)).real s := by
          symm
          rw [MeasureTheory.map_measureReal_apply
            (μ := μ) (f := fun ω ↦ x + W T ω)
            ((measurable_const.add (hW.stronglyMeasurable T).measurable)) hs]
    _ = (gaussianReal x T).real s := by
          rw [hLaw.map_eq]

/-- Helper for Exercise 21.3.1: the `n`th textbook strip mass is the Brownian terminal
probability of landing in that strip at time `T`. -/
theorem shiftedStripMass_eq_terminalReal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      μ.real {ω | x + W T ω ∈ Set.Icc ((n : ℝ) * a) (((n : ℝ) + 1) * a)} := by
  -- Proof comment: specialize the shifted terminal Gaussian law to the `n`th strip.
  symm
  exact
    shiftedBrownianTerminalReal_eq_gaussianReal
      (hW := hW) (x := x) (T := T) hT measurableSet_Icc

/-- Helper for Exercise 21.3.1: the Gaussian strip mass can be normalized to the half-open strip
form used in the reflection-prefix decomposition. -/
theorem shiftedStripMass_eq_Ioc
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      (gaussianReal x T).real (Set.Ioc ((n : ℝ) * a) (((n : ℝ) + 1) * a)) := by
  -- Proof comment: the previous atomlessness rewrite applies directly to the concrete strip
  -- endpoints `n * a` and `(n + 1) * a`.
  exact
    gaussianStripReal_Icc_eq_Ioc
      (m := x) (T := T) hT ((n : ℝ) * a) (((n : ℝ) + 1) * a)

/-- Helper for Exercise 21.3.1: every strip mass is nonnegative because it is a real-valued
Gaussian measure of a measurable interval. -/
theorem shiftedStripMass_nonneg
    {x a : ℝ} {T : NNReal} (n : ℤ) :
    0 ≤ shiftedStripMass x a T n := by
  -- Proof comment: `shiftedStripMass` is defined as the real measure of the strip `Icc`.
  simpa [shiftedStripMass] using
    (MeasureTheory.measureReal_nonneg
      (μ := gaussianReal x T)
      (s := Set.Icc ((n : ℝ) * a) (((n : ℝ) + 1) * a)))

/-- Helper for Exercise 21.3.1: positive-time Gaussian strip masses can be rewritten as density
integrals over the closed strip. -/
theorem shiftedStripMass_eq_integral_Icc
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      ∫ y in Set.Icc ((n : ℝ) * a) (((n : ℝ) + 1) * a), gaussianPDFReal x T y := by
  -- Proof comment: expand the Gaussian law by its density on the concrete strip and then remove
  -- the outer `ENNReal.toReal`.
  rw [shiftedStripMass, MeasureTheory.Measure.real_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral
      (μ := x) (v := T) (ne_of_gt hT)
      (Set.Icc ((n : ℝ) * a) (((n : ℝ) + 1) * a))]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦ gaussianPDFReal_nonneg x T y)]

/-- Helper for Exercise 21.3.1: positive-time Gaussian strip masses can also be written as density
integrals over the half-open strip used in the reflection decomposition. -/
theorem shiftedStripMass_eq_integral_Ioc
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      ∫ y in Set.Ioc ((n : ℝ) * a) (((n : ℝ) + 1) * a), gaussianPDFReal x T y := by
  -- Proof comment: the Gaussian density is integrated against Lebesgue measure, so removing one
  -- endpoint of the strip does not change the value of the integral.
  rw [shiftedStripMass_eq_integral_Icc (x := x) (a := a) (T := T) hT n]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Helper for Exercise 21.3.1: when `a ≥ 0`, the strip mass is the interval integral of the
Gaussian density across that strip. -/
theorem shiftedStripMass_eq_intervalIntegral
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T y := by
  have hlu : (n : ℝ) * a ≤ ((n : ℝ) + 1) * a := by
    calc
      (n : ℝ) * a ≤ (n : ℝ) * a + a := by linarith
      _ = ((n : ℝ) + 1) * a := by ring
  -- Proof comment: for ordered strip endpoints, the interval integral is exactly the `Ioc`
  -- integral over the same strip.
  rw [intervalIntegral.integral_of_le hlu]
  exact shiftedStripMass_eq_integral_Ioc (x := x) (a := a) (T := T) hT n

/-- Helper for Exercise 21.3.1: integer samples of the modulated strip-cell average recover the
centered alternating Gaussian strip terms. -/
theorem modulatedStripCellAverage_int_eq_parityShiftedStripMassLocal
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℤ) :
    modulatedStripCellAverage x a T n =
      (paritySign n * shiftedStripMass x a T n : ℂ) := by
  -- Proof comment: at integer arguments, the exponential modulation is exactly `paritySign n`,
  -- and the cell integral is the interval-integral form of `shiftedStripMass`.
  rw [modulatedStripCellAverage, paritySign_eq_complexExp_pi_mul_intLocal]
  have hLower : a * (n : ℝ) = (n : ℝ) * a := by ring
  have hUpper : a * ((n : ℝ) + 1) = ((n : ℝ) + 1) * a := by ring
  rw [hLower, hUpper]
  rw [shiftedStripMass_eq_intervalIntegral (x := x) (a := a) ha (T := T) hT n]
  rw [intervalIntegral.integral_ofReal]

/-- Helper for Exercise 21.3.1: the strip-cell average is the modulation factor times the
difference of the Gaussian primitive at the two cell endpoints. -/
theorem modulatedStripCellAverage_eq_primitiveDifferenceLocal
    {x a : ℝ} {T : NNReal} (s : ℝ) :
    modulatedStripCellAverage x a T s =
      Complex.exp (Real.pi * s * Complex.I) *
        ((∫ y in (0 : ℝ)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)) -
          ∫ y in (0 : ℝ)..(a * s), ((gaussianPDFReal x T y : ℝ) : ℂ)) := by
  let g : ℝ → ℂ := fun y ↦ ((gaussianPDFReal x T y : ℝ) : ℂ)
  have hg : Continuous g := by
    -- Proof comment: the complex Gaussian density is continuous because it is a scalar multiple of
    -- the real exponential of a quadratic polynomial.
    dsimp [g]
    rw [gaussianPDFReal_def]
    continuity
  have hInt1 : IntervalIntegrable g volume 0 (a * (s + 1)) := hg.intervalIntegrable _ _
  have hInt0 : IntervalIntegrable g volume 0 (a * s) := hg.intervalIntegrable _ _
  -- Proof comment: subtract the Gaussian primitive values at the two cell endpoints to recover
  -- the interval integral over the strip `[a * s, a * (s + 1)]`.
  dsimp [modulatedStripCellAverage]
  rw [← intervalIntegral.integral_interval_sub_left hInt1 hInt0]

/-- Helper for Exercise 21.3.1: the strip-cell average is equally the modulation factor times the
same Gaussian density integrated over the fixed cell `[0,a]` after translating by `a * s`. -/
theorem modulatedStripCellAverage_eq_translatedCellIntegralLocal
    {x a : ℝ} {T : NNReal} (s : ℝ) :
    modulatedStripCellAverage x a T s =
      Complex.exp (Real.pi * s * Complex.I) *
        ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun y ↦ ((gaussianPDFReal x T y : ℝ) : ℂ)
  have hTranslate :
      ∫ t in (0 : ℝ)..a, g (t + a * s) = ∫ y in a * s..a * (s + 1), g y := by
    -- Proof comment: translate the fixed cell `[0,a]` by `a * s` to recover the moving strip
    -- `[a * s, a * (s + 1)]`.
    simpa [g, zero_add, add_comm, add_left_comm, add_assoc, mul_add] using
      (intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := a) (d := a * s))
  -- Proof comment: rewrite the cell integral through the translated coordinates while keeping the
  -- oscillatory modulation factor untouched.
  dsimp [modulatedStripCellAverage]
  simpa [g, add_comm, add_left_comm, add_assoc] using
    congrArg (fun z : ℂ ↦ Complex.exp (Real.pi * s * Complex.I) * z) hTranslate.symm

/-- Helper for Exercise 21.3.1: at the shifted Fourier frequency `n + 1`, the Fourier kernel and
the modulation factor collapse to the single odd mode `2 * n + 1`. -/
theorem shiftedFourierKernel_mul_cellAverage_eq_oddModeLocal
    {x a : ℝ} {T : NNReal} (n : ℤ) (s : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
        modulatedStripCellAverage x a T s =
      Complex.exp ((↑(-((((2 * n + 1 : ℤ) : ℝ) * Real.pi) * s)) : ℂ) * Complex.I) *
        ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) := by
  have hPhase :
      Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
          Complex.exp (Real.pi * s * Complex.I) =
        Complex.exp ((↑(-((((2 * n + 1 : ℤ) : ℝ) * Real.pi) * s)) : ℂ) * Complex.I) := by
    -- Proof comment: combine the Fourier phase `-2π (n + 1) s` with the modulation `π s` into
    -- the single odd phase `-(2n + 1) π s`.
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  -- Proof comment: first normalize the moving strip integral to the translated fixed cell, then
  -- collapse the two exponential factors into the odd mode.
  calc
    Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
        modulatedStripCellAverage x a T s
        =
          Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
            (Complex.exp (Real.pi * s * Complex.I) *
              ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
              rw [modulatedStripCellAverage_eq_translatedCellIntegralLocal
                (x := x) (a := a) (T := T) s]
    _ =
        (Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
          Complex.exp (Real.pi * s * Complex.I)) *
          ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) := by
            rw [← mul_assoc]
    _ =
        Complex.exp ((↑(-((((2 * n + 1 : ℤ) : ℝ) * Real.pi) * s)) : ℂ) * Complex.I) *
          ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) := by
            rw [hPhase]

/-- Helper for Exercise 21.3.1: the Poisson input `modulatedStripCellAverage x a T` is continuous
in the spatial parameter `s`. -/
theorem modulatedStripCellAverage_continuousLocal
    {x a : ℝ} {T : NNReal} :
    Continuous (modulatedStripCellAverage x a T) := by
  let g : ℝ → ℂ := fun y ↦ ((gaussianPDFReal x T y : ℝ) : ℂ)
  let primitive : ℝ → ℂ := fun s ↦ ∫ y in (0 : ℝ)..(a * s), g y
  have hg : Continuous g := by
    -- Proof comment: the complex Gaussian density is continuous because its real part is the
    -- usual Gaussian density and the imaginary part vanishes identically.
    dsimp [g]
    rw [gaussianPDFReal_def]
    continuity
  have hContIntegrand : Continuous (fun p : ℝ × ℝ ↦ g p.2) := hg.comp continuous_snd
  have hPrimitive : Continuous primitive := by
    -- Proof comment: integrate the continuous Gaussian density from the fixed anchor `0` to the
    -- moving upper endpoint `a * s`.
    simpa [primitive] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (_s : ℝ) y ↦ g y) (a₀ := (0 : ℝ))
        hContIntegrand (hs := continuous_id.const_mul a))
  have hShiftedPrimitive : Continuous (fun s : ℝ ↦ primitive (s + 1)) :=
    hPrimitive.comp (continuous_id.add continuous_const)
  have hModulation : Continuous (fun s : ℝ ↦ Complex.exp (Real.pi * s * Complex.I)) := by
    continuity
  have hDifference : Continuous (fun s : ℝ ↦ primitive (s + 1) - primitive s) :=
    hShiftedPrimitive.sub hPrimitive
  have hEq :
      modulatedStripCellAverage x a T =
        fun s : ℝ ↦
          Complex.exp (Real.pi * s * Complex.I) * (primitive (s + 1) - primitive s) := by
    funext s
    exact modulatedStripCellAverage_eq_primitiveDifferenceLocal (x := x) (a := a) (T := T) s
  -- Proof comment: combine the primitive-difference normalization with continuity of the
  -- oscillatory modulation factor.
  rw [hEq]
  exact hModulation.mul hDifference

/-- Helper for Exercise 21.3.1: the half-open strip mass is also the Brownian terminal
probability of the corresponding half-open strip. -/
theorem shiftedStripMass_eq_terminalIocReal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      μ.real {ω | x + W T ω ∈ Set.Ioc ((n : ℝ) * a) (((n : ℝ) + 1) * a)} := by
  -- Proof comment: combine the Gaussian strip normalization to `Ioc` with the shifted terminal
  -- law of Brownian motion at time `T`.
  rw [shiftedStripMass_eq_Ioc (x := x) (a := a) (T := T) hT n]
  symm
  exact
    shiftedBrownianTerminalReal_eq_gaussianReal
      (hW := hW) (x := x) (T := T) hT measurableSet_Ioc

/-- Helper for Exercise 21.3.1: the reflected negative strip `-(n + 1)` has the explicit
terminal-event `Ioc` spelling used in the upper-loss parity comparison. -/
theorem reflectedShiftedStripMass_eq_terminalIocReal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (n : ℕ) :
    shiftedStripMass x a T (-(n + 1 : ℤ)) =
      μ.real {ω | x + W T ω ∈ Set.Ioc (((-1 : ℝ) - (n : ℝ)) * a) (-((n : ℝ) * a))} := by
  -- Proof comment: specialize the general terminal-strip transport to the reflected index
  -- `-(n + 1)` and simplify the two strip endpoints to the raw arithmetic form used later.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using
    shiftedStripMass_eq_terminalIocReal
      (hW := hW) (x := x) (a := a) (T := T) hT (n := (-(n + 1 : ℤ)))

/-- Helper for Exercise 21.3.1: for a real probability law, the mass of a half-open interval is
the increment of its cdf across that interval. -/
theorem probabilityMeasureReal_Ioc_eq_cdf_sub
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {l u : ℝ} (hlu : l ≤ u) :
    ν.real (Set.Ioc l u) = cdf ν u - cdf ν l := by
  have hunion : Set.Iic u = Set.Iic l ∪ Set.Ioc l u := by
    ext x
    constructor
    · intro hx
      by_cases hxl : x ≤ l
      · exact Or.inl hxl
      · exact Or.inr ⟨lt_of_not_ge hxl, hx⟩
    · intro hx
      rcases hx with hx | hx
      · exact le_trans hx hlu
      · exact hx.2
  have hdisj : Disjoint (Set.Iic l) (Set.Ioc l u) := by
    rw [Set.disjoint_left]
    intro x hxIic hxIoc
    exact (not_lt_of_ge hxIic) hxIoc.1
  have hmass :
      ν.real (Set.Iic u) = ν.real (Set.Iic l) + ν.real (Set.Ioc l u) := by
    -- Proof comment: split the upper half-line at the left endpoint `l` into the earlier half-line
    -- and the disjoint half-open increment `Ioc l u`.
    simpa [hunion] using
      (MeasureTheory.measureReal_union
        (μ := ν) (s₁ := Set.Iic l) (s₂ := Set.Ioc l u) hdisj measurableSet_Ioc)
  -- Proof comment: rewrite the two half-line masses as cdf values and isolate the interval mass.
  rw [← ProbabilityTheory.cdf_eq_real (μ := ν) u, ← ProbabilityTheory.cdf_eq_real (μ := ν) l] at hmass
  linarith

/-- Helper for Exercise 21.3.1: when `a ≥ 0`, each half-open strip mass is the corresponding cdf
increment of the Gaussian terminal law. -/
theorem shiftedStripMass_eq_cdf_sub
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℤ) :
    shiftedStripMass x a T n =
      cdf (gaussianReal x T) (((n : ℝ) + 1) * a) -
        cdf (gaussianReal x T) ((n : ℝ) * a) := by
  have hlu : (n : ℝ) * a ≤ ((n : ℝ) + 1) * a := by
    calc
      (n : ℝ) * a ≤ (n : ℝ) * a + a := by linarith
      _ = ((n : ℝ) + 1) * a := by ring
  -- Proof comment: after normalizing the strip to `Ioc`, the mass is exactly the cdf jump across
  -- its endpoints.
  rw [shiftedStripMass_eq_Ioc (x := x) (a := a) (T := T) hT n]
  exact probabilityMeasureReal_Ioc_eq_cdf_sub (ν := gaussianReal x T) hlu

/-- Helper for Exercise 21.3.1: the reflected strip `-(2 * N + 2)` is the difference between the
two consecutive left tails of `gaussianReal x T` at `-(2 * N + 1) * a` and `-(2 * N + 2) * a`.
-/
theorem shiftedStripMass_negEven_eq_leftTailDiffLocal
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    shiftedStripMass x a T (-(2 * N + 2 : ℤ)) =
      (gaussianReal x T).real (Set.Iic (-(((2 * N + 1 : ℕ) : ℝ) * a))) -
        (gaussianReal x T).real (Set.Iic (-(((2 * N + 2 : ℕ) : ℝ) * a))) := by
  have hStripCdf :
      shiftedStripMass x a T (-(2 * N + 2 : ℤ)) =
        cdf (gaussianReal x T) (-(((2 * N + 1 : ℕ) : ℝ) * a)) -
          cdf (gaussianReal x T) (-(((2 * N + 2 : ℕ) : ℝ) * a)) := by
    calc
      shiftedStripMass x a T (-(2 * N + 2 : ℤ))
          = cdf (gaussianReal x T) ((((-(2 * N + 2 : ℤ) : ℝ)) + 1) * a) -
              cdf (gaussianReal x T) (((-(2 * N + 2 : ℤ) : ℝ)) * a) := by
              simpa using
                shiftedStripMass_eq_cdf_sub
                  (x := x) (a := a) ha (T := T) hT (n := (-(2 * N + 2 : ℤ)))
      _ =
          cdf (gaussianReal x T) (-(((2 * N + 1 : ℕ) : ℝ) * a)) -
            cdf (gaussianReal x T) (-(((2 * N + 2 : ℕ) : ℝ) * a)) := by
            congr 1 <;> ring
  -- Proof comment: rewrite the reflected strip mass as a cdf increment, then identify each cdf
  -- value with the corresponding left-tail mass.
  rw [hStripCdf, ← ProbabilityTheory.cdf_eq_real
    (μ := gaussianReal x T) (-(((2 * N + 1 : ℕ) : ℝ) * a)),
    ← ProbabilityTheory.cdf_eq_real
      (μ := gaussianReal x T) (-(((2 * N + 2 : ℕ) : ℝ) * a))]

/-- Helper for Exercise 21.3.1: even strip indices carry the positive alternating sign. -/
theorem paritySign_two_mul (k : ℤ) :
    paritySign (2 * k) = 1 := by
  -- Proof comment: every even index satisfies the `Even` branch in the definition of
  -- `paritySign`.
  simp [paritySign]

/-- Helper for Exercise 21.3.1: odd strip indices carry the negative alternating sign. -/
theorem paritySign_two_mul_add_one (k : ℤ) :
    paritySign (2 * k + 1) = -1 := by
  -- Proof comment: every odd index falls into the `else` branch of `paritySign`.
  simp [paritySign]

/-- Helper for Exercise 21.3.1: an even paired shell is the positive strip mass at `2n` minus the
reflected partner at `-(2n + 1)`. -/
theorem alternatingStripPairShell_even
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    alternatingStripPairShell x a T (2 * n) =
      shiftedStripMass x a T (2 * n : ℤ) -
        shiftedStripMass x a T (-(2 * n + 1 : ℤ)) := by
  have hEven :
      paritySign ((2 * n : ℕ) : ℤ) = 1 := by
    -- Proof comment: the nonnegative shell index `2n` is even, so it keeps the positive sign.
    simpa using paritySign_two_mul (k := (n : ℤ))
  have hOdd :
      paritySign (-(2 * n + 1 : ℤ)) = -1 := by
    have hRewrite : (-(2 * n + 1 : ℤ)) = 2 * (-(n : ℤ) - 1) + 1 := by
      ring_nf
    -- Proof comment: the reflected partner `-(2n + 1)` is odd, so it contributes with sign `-1`.
    rw [hRewrite, paritySign_two_mul_add_one]
  have hNegIndex : (-(((2 * n : ℕ) : ℤ) + 1)) = -(2 * n + 1 : ℤ) := by
    norm_num
  -- Proof comment: after evaluating the two parity signs, the paired shell is exactly a
  -- difference of the outward strip masses.
  rw [alternatingStripPairShell, hEven, hNegIndex, hOdd]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 21.3.1: an odd paired shell is the negative strip mass at `2n + 1` plus
the reflected even partner at `-(2n + 2)`. -/
theorem alternatingStripPairShell_odd
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    alternatingStripPairShell x a T (2 * n + 1) =
      -shiftedStripMass x a T (2 * n + 1 : ℤ) +
        shiftedStripMass x a T (-(2 * n + 2 : ℤ)) := by
  have hOdd :
      paritySign ((2 * n + 1 : ℕ) : ℤ) = -1 := by
    -- Proof comment: the shell index `2n + 1` is odd, so it contributes with sign `-1`.
    simpa using paritySign_two_mul_add_one (k := (n : ℤ))
  have hEven :
      paritySign (-(2 * n + 2 : ℤ)) = 1 := by
    have hRewrite : (-(2 * n + 2 : ℤ)) = 2 * (-(n + 1 : ℤ)) := by
      ring_nf
    -- Proof comment: the reflected partner `-(2n + 2)` is even, so it keeps the positive sign.
    rw [hRewrite, paritySign_two_mul]
  have hNegIndex : (-((((2 * n + 1 : ℕ) : ℤ)) + 1)) = -(2 * n + 2 : ℤ) := by
    omega
  -- Proof comment: evaluating the two parity signs rewrites the odd shell as the expected
  -- negative-plus-positive strip combination.
  rw [alternatingStripPairShell, hOdd, hNegIndex, hEven]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 21.3.1: every paired shell is the lower-barrier shell difference
`shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1))` weighted by the alternating sign
`paritySign n`. -/
theorem alternatingStripPairShell_eq_paritySign_mul_shellDifferenceLocal
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    alternatingStripPairShell x a T n =
      paritySign (n : ℤ) *
        (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- Proof comment: on even shells, the alternating sign is `+1`, so the paired shell is
    -- exactly the unsigned lower-barrier shell difference.
    rw [hk]
    have hkTwo : k + k = 2 * k := by omega
    rw [hkTwo]
    have hNegIndex : (-(↑(2 * k) + 1 : ℤ)) = -(2 * k + 1 : ℤ) := by
      omega
    rw [hNegIndex]
    calc
      alternatingStripPairShell x a T (2 * k)
          = shiftedStripMass x a T (2 * k : ℤ) -
              shiftedStripMass x a T (-(2 * k + 1 : ℤ)) := by
                exact alternatingStripPairShell_even (x := x) (a := a) (T := T) k
      _ = paritySign ((2 * k : ℕ) : ℤ) *
            (shiftedStripMass x a T (2 * k : ℤ) -
              shiftedStripMass x a T (-(2 * k + 1 : ℤ))) := by
            have hsign : paritySign ((2 * k : ℕ) : ℤ) = 1 := by
              simpa using paritySign_two_mul (k := (k : ℤ))
            rw [hsign, one_mul]
  · -- Proof comment: on odd shells, the alternating sign is `-1`, so the paired shell is the
    -- negative of the same shell difference.
    rw [hk]
    have hNegIndex : (-(↑(2 * k + 1) + 1 : ℤ)) = -(2 * k + 2 : ℤ) := by
      omega
    rw [hNegIndex]
    calc
      alternatingStripPairShell x a T (2 * k + 1)
          = -shiftedStripMass x a T (2 * k + 1 : ℤ) +
              shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
                exact alternatingStripPairShell_odd (x := x) (a := a) (T := T) k
      _ = paritySign ((2 * k + 1 : ℕ) : ℤ) *
            (shiftedStripMass x a T (2 * k + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * k + 2 : ℤ))) := by
            have hsign : paritySign ((2 * k + 1 : ℕ) : ℤ) = -1 := by
              simpa using paritySign_two_mul_add_one (k := (k : ℤ))
            rw [hsign]
            ring

/-- Helper for Exercise 21.3.1: each paired shell is the unsigned lower-barrier shell difference
minus twice that shell difference on odd indices. This isolates the finite upper-loss correction
from the one-sided lower-barrier prefix. -/
theorem alternatingStripPairShell_eq_shellDifference_sub_oddCorrectionLocal
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    alternatingStripPairShell x a T n =
      (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))) -
        (if Even n then 0 else
          2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))) := by
  -- Proof comment: after factoring out the shell difference, only the odd indices contribute the
  -- extra factor `2` that separates the two-barrier prefix from the one-sided lower-barrier one.
  rw [alternatingStripPairShell_eq_paritySign_mul_shellDifferenceLocal]
  by_cases hEven : Even n
  · have hSign : paritySign (n : ℤ) = 1 := by
      have hEvenInt : Even (n : ℤ) := by
        simpa using hEven
      simp [paritySign, hEvenInt]
    rw [hSign, if_pos hEven]
    ring
  · have hSign : paritySign (n : ℤ) = -1 := by
      have hEvenInt : ¬ Even (n : ℤ) := by
        simpa using hEven
      simp [paritySign, hEvenInt]
    rw [hSign, if_neg hEven]
    ring

/-- Helper for Exercise 21.3.1: each shell-correction term is the lower-barrier shell difference
minus the paired alternating shell. This is the finite algebra needed to isolate the upper-loss
prefix from the lower-barrier and interval-survival prefixes. -/
theorem upperLossCorrection_eq_shellDifference_sub_pairShellLocal
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    (if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))) =
      (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))) -
        alternatingStripPairShell x a T n := by
  -- Proof comment: rearrange the already proved shell decomposition
  -- `alternatingStripPairShell = shellDifference - correction`.
  have hShell :=
    alternatingStripPairShell_eq_shellDifference_sub_oddCorrectionLocal
      (x := x) (a := a) (T := T) n
  linarith

/-- Helper for Exercise 21.3.1: every finite correction prefix is the difference between the
lower-barrier shell prefix and the paired alternating shell prefix. -/
theorem upperLossCorrection_prefix_eq_shellDifferencePrefix_sub_pairShellPrefixLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let shellDifference : ℕ → ℝ := fun n ↦
      shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
    ∑ n ∈ Finset.range N, correction n =
      ∑ n ∈ Finset.range N, shellDifference n -
        ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := by
  -- Proof comment: sum the termwise correction identity over the finite prefix and split the
  -- resulting difference of sums.
  dsimp
  calc
    ∑ n ∈ Finset.range N,
        (if Even n then 0 else
          2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))))
        =
          ∑ n ∈ Finset.range N,
            ((shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))) -
              alternatingStripPairShell x a T n) := by
                refine Finset.sum_congr rfl ?_
                intro n _hn
                exact upperLossCorrection_eq_shellDifference_sub_pairShellLocal
                  (x := x) (a := a) (T := T) n
    _ =
        ∑ n ∈ Finset.range N, (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))) -
          ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := by
            rw [Finset.sum_sub_distrib]

/-- Helper for Exercise 21.3.1: the odd correction prefix through `2 * N` keeps exactly the odd
shell-difference terms `1, 3, ..., 2 * N - 1`. -/
theorem upperLossCorrection_oddPrefix_eq_doubleOddShellSumLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let g : ℕ → ℝ := fun n ↦
      shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
    let correction : ℕ → ℝ := fun n ↦ if Even n then 0 else 2 * g n
    ∑ n ∈ Finset.range (2 * N + 1), correction n =
      ∑ k ∈ Finset.range N, 2 * g (2 * k + 1) := by
  let g : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let correction : ℕ → ℝ := fun n ↦ if Even n then 0 else 2 * g n
  induction N with
  | zero =>
      -- Proof comment: the odd prefix ending at `0` contains no odd shell, so both sides vanish.
      simp [g, correction]
  | succ N ih =>
      -- Proof comment: extending the odd prefix from `2 * N` to `2 * (N + 1)` appends exactly the
      -- new odd shell `2 * N + 1`; the next even shell contributes `0`.
      have ih' :
          ∑ n ∈ Finset.range (2 * N + 1), correction n =
            ∑ k ∈ Finset.range N, 2 * g (2 * k + 1) := by
        simpa [g, correction] using ih
      have hOdd :
          correction (2 * N + 1) = 2 * g (2 * N + 1) := by
        have hOdd' : ¬ Even (2 * N + 1) := by
          intro hEven
          rcases hEven with ⟨k, hk⟩
          omega
        simp [correction, hOdd']
      have hEven :
          correction (2 * N + 2) = 0 := by
        have hEven' : Even (2 * N + 2) := ⟨N + 1, by ring⟩
        simp [correction, hEven']
      calc
        ∑ n ∈ Finset.range (2 * (N + 1) + 1), correction n
            = ∑ n ∈ Finset.range (2 * N + 2), correction n + correction (2 * N + 2) := by
                rw [show 2 * (N + 1) + 1 = 2 * N + 2 + 1 by omega, Finset.sum_range_succ]
        _ = (∑ n ∈ Finset.range (2 * N + 1), correction n + correction (2 * N + 1)) +
              correction (2 * N + 2) := by
                rw [show 2 * N + 2 = 2 * N + 1 + 1 by omega, Finset.sum_range_succ]
        _ = (∑ k ∈ Finset.range N, 2 * g (2 * k + 1) + 2 * g (2 * N + 1)) + 0 := by
              rw [ih', hOdd, hEven]
        _ = ∑ k ∈ Finset.range (N + 1), 2 * g (2 * k + 1) := by
              rw [Finset.sum_range_succ]
              ring

/-- Helper for Exercise 21.3.1: the even correction prefix through `2 * N + 1` keeps exactly the
odd shell-difference terms `1, 3, ..., 2 * N + 1`. -/
theorem upperLossCorrection_evenPrefix_eq_doubleOddShellSumLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let g : ℕ → ℝ := fun n ↦
      shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
    let correction : ℕ → ℝ := fun n ↦ if Even n then 0 else 2 * g n
    ∑ n ∈ Finset.range (2 * N + 2), correction n =
      ∑ k ∈ Finset.range (N + 1), 2 * g (2 * k + 1) := by
  let g : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let correction : ℕ → ℝ := fun n ↦ if Even n then 0 else 2 * g n
  -- Proof comment: the even prefix is the odd prefix plus its last odd shell `2 * N + 1`.
  have hOddPrefix :
      ∑ n ∈ Finset.range (2 * N + 1), correction n =
        ∑ k ∈ Finset.range N, 2 * g (2 * k + 1) := by
    simpa [g, correction] using
      upperLossCorrection_oddPrefix_eq_doubleOddShellSumLocal (x := x) (a := a) (T := T) N
  have hOddTerm :
      correction (2 * N + 1) = 2 * g (2 * N + 1) := by
    have hOdd : ¬ Even (2 * N + 1) := by simp
    simp [correction, hOdd]
  calc
    ∑ n ∈ Finset.range (2 * N + 2), correction n
        = ∑ n ∈ Finset.range (2 * N + 1), correction n + correction (2 * N + 1) := by
            rw [show 2 * N + 2 = 2 * N + 1 + 1 by omega, Finset.sum_range_succ]
    _ = (∑ k ∈ Finset.range N, 2 * g (2 * k + 1)) + 2 * g (2 * N + 1) := by
          rw [hOddPrefix, hOddTerm]
    _ = ∑ k ∈ Finset.range (N + 1), 2 * g (2 * k + 1) := by
          rw [Finset.sum_range_succ]

/-- Helper for Exercise 21.3.1: each lower-barrier shell difference is the increment of the
symmetric Gaussian cdf profile `u ↦ cdf u + cdf (-u)` across one strip width. -/
theorem shellDifference_eq_cdfSymmetricIncrementLocal
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℕ) :
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)) =
      (cdf (gaussianReal x T) (((n + 1 : ℕ) : ℝ) * a) +
          cdf (gaussianReal x T) (-(((n + 1 : ℕ) : ℝ) * a))) -
        (cdf (gaussianReal x T) ((n : ℝ) * a) +
          cdf (gaussianReal x T) (-((n : ℝ) * a))) := by
  have hPos :
      shiftedStripMass x a T n =
        cdf (gaussianReal x T) (((n + 1 : ℕ) : ℝ) * a) -
          cdf (gaussianReal x T) ((n : ℝ) * a) := by
    -- Proof comment: the positive strip is already the cdf jump across its two endpoints.
    simpa using shiftedStripMass_eq_cdf_sub
      (x := x) (a := a) ha (T := T) hT (n := (n : ℤ))
  have hNeg :
      shiftedStripMass x a T (-(n + 1 : ℤ)) =
        cdf (gaussianReal x T) (-((n : ℝ) * a)) -
          cdf (gaussianReal x T) (-(((n + 1 : ℕ) : ℝ) * a)) := by
    -- Proof comment: the reflected strip `-(n + 1)` has endpoints `-((n + 1) a)` and `-(n a)`.
    have h :=
      shiftedStripMass_eq_cdf_sub
        (x := x) (a := a) ha (T := T) hT (n := (-(n + 1 : ℤ)))
    have hLowerCast : (((-(n + 1 : ℤ) : ℤ) : ℝ)) = (-1 : ℝ) - (n : ℝ) := by
      norm_num
      ring_nf
    have hUpper : ((((-(n + 1 : ℤ) : ℤ) : ℝ) + 1) * a) = -((n : ℝ) * a) := by
      simp
    have hNat : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
      norm_num
    have hLowerArg : (((-1 : ℝ) - (n : ℝ)) * a) = -(((n + 1 : ℕ) : ℝ) * a) := by
      calc
        (((-1 : ℝ) - (n : ℝ)) * a) = (-1 : ℝ) * a - (n : ℝ) * a := by ring
        _ = -a - (n : ℝ) * a := by ring
        _ = -(a * ((n : ℝ) + 1)) := by ring
        _ = -(a * (((n + 1 : ℕ) : ℝ))) := by rw [hNat]
        _ = -(((n + 1 : ℕ) : ℝ) * a) := by ring
    calc
      shiftedStripMass x a T (-(n + 1 : ℤ)) =
          cdf (gaussianReal x T) (-((n : ℝ) * a)) -
            cdf (gaussianReal x T) (((-1 : ℝ) - (n : ℝ)) * a) := by
              simpa [hLowerCast, hUpper] using h
      _ =
          cdf (gaussianReal x T) (-((n : ℝ) * a)) -
            cdf (gaussianReal x T) (-(((n + 1 : ℕ) : ℝ) * a)) := by
              rw [hLowerArg]
  -- Proof comment: subtract the reflected cdf jump from the positive one and regroup the four
  -- endpoints into one symmetric cdf increment.
  rw [hPos, hNeg]
  ring


/-- Helper for Exercise 21.3.1: each consecutive even/odd shell pair expands to the difference of
the adjacent positive strip block and its reflected negative companion block. -/
theorem alternatingStripPairShell_twoStep_blockLocal
    {x a : ℝ} {T : NNReal} (n : ℕ) :
    alternatingStripPairShell x a T (2 * n) + alternatingStripPairShell x a T (2 * n + 1) =
      (shiftedStripMass x a T (2 * n : ℤ) - shiftedStripMass x a T (2 * n + 1 : ℤ)) +
        (shiftedStripMass x a T (-(2 * n + 2 : ℤ)) -
          shiftedStripMass x a T (-(2 * n + 1 : ℤ))) := by
  -- Proof comment: expand the even and odd shells separately and regroup the four strip masses
  -- into the positive block minus the reflected negative block.
  rw [alternatingStripPairShell_even, alternatingStripPairShell_odd]
  ring

/-- Helper for Exercise 21.3.1: a Gaussian half-open strip whose endpoints both drift to `+∞`
has vanishing mass. -/
theorem gaussianIocMass_tendsto_zero_of_endpoints_atTopLocal
    {m : ℝ} {T : NNReal} {l u : ℕ → ℝ}
    (hlu : ∀ n, l n ≤ u n)
    (hl : Filter.Tendsto l Filter.atTop Filter.atTop)
    (hu : Filter.Tendsto u Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ (gaussianReal m T).real (Set.Ioc (l n) (u n)))
      Filter.atTop (𝓝 0) := by
  have hlcdf :
      Filter.Tendsto (fun n ↦ cdf (gaussianReal m T) (l n)) Filter.atTop (𝓝 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop (μ := gaussianReal m T)).comp hl
  have hucdf :
      Filter.Tendsto (fun n ↦ cdf (gaussianReal m T) (u n)) Filter.atTop (𝓝 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop (μ := gaussianReal m T)).comp hu
  have hrewrite :
      (fun n ↦ (gaussianReal m T).real (Set.Ioc (l n) (u n))) =
        (fun n ↦ cdf (gaussianReal m T) (u n) - cdf (gaussianReal m T) (l n)) := by
    funext n
    exact probabilityMeasureReal_Ioc_eq_cdf_sub (ν := gaussianReal m T) (hlu n)
  -- Proof comment: rewrite each strip mass as a cdf increment and use that both cdf values tend
  -- to `1` when the endpoints go to `+∞`.
  rw [hrewrite]
  simpa using hucdf.sub hlcdf

/-- Helper for Exercise 21.3.1: a Gaussian half-open strip whose endpoints both drift to `-∞`
has vanishing mass. -/
theorem gaussianIocMass_tendsto_zero_of_endpoints_atBotLocal
    {m : ℝ} {T : NNReal} {l u : ℕ → ℝ}
    (hlu : ∀ n, l n ≤ u n)
    (hl : Filter.Tendsto l Filter.atTop Filter.atBot)
    (hu : Filter.Tendsto u Filter.atTop Filter.atBot) :
    Filter.Tendsto (fun n ↦ (gaussianReal m T).real (Set.Ioc (l n) (u n)))
      Filter.atTop (𝓝 0) := by
  have hlcdf :
      Filter.Tendsto (fun n ↦ cdf (gaussianReal m T) (l n)) Filter.atTop (𝓝 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot (μ := gaussianReal m T)).comp hl
  have hucdf :
      Filter.Tendsto (fun n ↦ cdf (gaussianReal m T) (u n)) Filter.atTop (𝓝 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot (μ := gaussianReal m T)).comp hu
  have hrewrite :
      (fun n ↦ (gaussianReal m T).real (Set.Ioc (l n) (u n))) =
        (fun n ↦ cdf (gaussianReal m T) (u n) - cdf (gaussianReal m T) (l n)) := by
    funext n
    exact probabilityMeasureReal_Ioc_eq_cdf_sub (ν := gaussianReal m T) (hlu n)
  -- Proof comment: the same cdf-increment rewrite now lands in a `0 - 0` limit because both
  -- endpoints go to `-∞`.
  rw [hrewrite]
  simpa using hucdf.sub hlcdf

/-- Helper for Exercise 21.3.1: the two outer Gaussian strips in the paired-shell truncation both
escape to infinity, so their combined mass tends to `0`. -/
theorem outerStripMass_tendsto_zeroLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ ↦ shiftedStripMass x a T (N : ℤ) + shiftedStripMass x a T (-(N + 1 : ℤ)))
      Filter.atTop (𝓝 0) := by
  have hScaled :
      Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) * a) Filter.atTop Filter.atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hPos :
      Filter.Tendsto (fun N : ℕ ↦ shiftedStripMass x a T (N : ℤ))
        Filter.atTop (𝓝 0) := by
    have hRewrite :
        (fun N : ℕ ↦ shiftedStripMass x a T (N : ℤ)) =
          (fun N : ℕ ↦
            (gaussianReal x T).real (Set.Ioc ((N : ℝ) * a) (((N : ℝ) + 1) * a))) := by
      funext N
      exact shiftedStripMass_eq_Ioc (x := x) (a := a) (T := T) hT (n := (N : ℤ))
    rw [hRewrite]
    have hUpper :
        Filter.Tendsto (fun N : ℕ ↦ (((N : ℝ) + 1) * a)) Filter.atTop Filter.atTop := by
      convert tendsto_atTop_add_const_right _ a hScaled using 1
      funext N
      ring
    -- Proof comment: the positive-side outer strip is a fixed-width Gaussian `Ioc` interval whose
    -- endpoints both drift to `+∞`.
    refine gaussianIocMass_tendsto_zero_of_endpoints_atTopLocal ?_ hScaled hUpper
    intro N
    nlinarith [ha.le]
  have hScaledSucc :
      Filter.Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) * a) Filter.atTop Filter.atTop := by
    exact hScaled.comp (tendsto_add_atTop_nat 1)
  have hNeg :
      Filter.Tendsto (fun N : ℕ ↦ shiftedStripMass x a T (-(N + 1 : ℤ)))
        Filter.atTop (𝓝 0) := by
    have hRewrite :
        (fun N : ℕ ↦ shiftedStripMass x a T (-(N + 1 : ℤ))) =
          (fun N : ℕ ↦
            (gaussianReal x T).real
              (Set.Ioc (((-1 : ℝ) - (N : ℝ)) * a) (-((N : ℝ) * a)))) := by
      funext N
      simpa using shiftedStripMass_eq_Ioc (x := x) (a := a) (T := T) hT (n := (-(N + 1 : ℤ)))
    rw [hRewrite]
    have hLower :
        Filter.Tendsto (fun N : ℕ ↦ (((-1 : ℝ) - (N : ℝ)) * a)) Filter.atTop Filter.atBot := by
      have hLowerEq :
          (fun N : ℕ ↦ (((-1 : ℝ) - (N : ℝ)) * a)) =
            fun N : ℕ ↦ -(((N + 1 : ℕ) : ℝ) * a) := by
        funext N
        calc
          (((-1 : ℝ) - (N : ℝ)) * a) = -((((N : ℝ) + 1) * a)) := by ring
          _ = -(((N + 1 : ℕ) : ℝ) * a) := by
            congr 1
            norm_num
      rw [hLowerEq]
      exact tendsto_neg_atTop_atBot.comp hScaledSucc
    have hUpperEq :
        (fun N : ℕ ↦ -((N : ℝ) * a)) = (Neg.neg ∘ fun N : ℕ ↦ (N : ℝ) * a) := by
      funext N
      rfl
    have hUpper :
        Filter.Tendsto (fun N : ℕ ↦ -((N : ℝ) * a)) Filter.atTop Filter.atBot := by
      rw [hUpperEq]
      exact tendsto_neg_atTop_atBot.comp hScaled
    -- Proof comment: the reflected negative-side outer strip is the symmetric `Ioc` interval with
    -- both endpoints drifting to `-∞`.
    refine gaussianIocMass_tendsto_zero_of_endpoints_atBotLocal ?_ hLower hUpper
    intro N
    nlinarith [ha.le]
  -- Proof comment: each outer strip mass vanishes separately, so their sum also vanishes.
  simpa using hPos.add hNeg

/-- Helper for Exercise 21.3.1: if the Brownian sample paths are everywhere continuous, then the
two-barrier exit time is a stopping time for the natural filtration. -/
theorem brownianIntervalExitTime_isStoppingTimeLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (hWcont : ∀ ω, Continuous (fun t : NNReal ↦ W t ω))
    {x a : ℝ} :
    IsStoppingTime
      (Filtration.natural W (fun t ↦ (hW.stronglyMeasurable t)))
      (brownianIntervalExitTime W x a) := by
  -- Route correction: the owner stopping-time theorem from Exercise 21.2.4 requires pointwise
  -- continuity of the sample paths, so this helper is stated on that stronger surface instead of
  -- reopening the almost-sure continuity transport used in the gap lemma below.
  simpa [brownianIntervalExitTime] using
    (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
      (X := W)
      (hXsm := fun t ↦ hW.stronglyMeasurable t)
      (hXcont := hWcont)
      (a := -x)
      (b := a - x))

/-- Helper for Exercise 21.3.1: surviving inside `(0, a)` up to time `T` implies surviving above
the lower barrier `0` up to time `T`. -/
theorem intervalSurvival_event_subset_lowerSurvivalLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} :
    {ω | T < brownianIntervalExitTime W x a ω} ⊆
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
  intro ω hω
  have hHit :
      brownianIntervalExitTime W x a ω ≤ hittingAfter W ({-x} : Set ℝ) 0 ω := by
    -- Proof comment: enlarging the target from `{-x}` to `{-x, a - x}` can only decrease the
    -- first hitting time.
    exact
      hittingAfter_apply_anti (u := W) (n := 0) (ω := ω) <|
        by
          intro z hz
          exact Or.inl (by simpa using hz)
  -- Proof comment: if the earlier two-barrier exit time is already after `T`, then the later
  -- lower-barrier hitting time is also after `T`.
  exact lt_of_lt_of_le hω hHit

/-- Helper for Exercise 21.3.1: the `upperLoss` event is exactly lower-barrier survival together
with hitting the upper barrier by time `T`. -/
theorem upperLoss_eq_lowerSurvival_inter_upperHitLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} :
    ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}) =
      ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
        {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T}) := by
  ext ω
  constructor
  · intro hω
    refine ⟨hω.1, ?_⟩
    have hExitLe : brownianIntervalExitTime W x a ω ≤ T := le_of_not_gt hω.2
    rcases
        (hittingAfter_le_iff
          (u := W) (s := ({-x, a - x} : Set ℝ)) (n := (0 : NNReal)) (ω := ω) (i := T)).1
          hExitLe with
      ⟨j, hj, hjMem⟩
    have hjLtLower : (j : ENNReal) < hittingAfter W ({-x} : Set ℝ) 0 ω := by
      exact lt_of_le_of_lt (by exact_mod_cast hj.2) hω.1
    have hjNotLower : W j ω ∉ ({-x} : Set ℝ) := by
      exact
        notMem_of_lt_hittingAfter
          (u := W) (s := ({-x} : Set ℝ)) (n := (0 : NNReal)) (ω := ω) (k := j) hjLtLower
          (by simp)
    have hjUpper : W j ω ∈ ({a - x} : Set ℝ) := by
      have hjCases : W j ω = -x ∨ W j ω = a - x := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hjMem
      rcases hjCases with hjLower | hjUpper
      · exact False.elim <| hjNotLower (by simpa [Set.mem_singleton_iff, hjLower])
      · simpa [Set.mem_singleton_iff] using hjUpper
    -- Proof comment: once the two-barrier exit occurs by time `T`, lower survival forces the
    -- realized barrier to be `a - x`, so the upper-barrier hitting time is at most `T`.
    exact
      (hittingAfter_le_of_mem
        (u := W) (s := ({a - x} : Set ℝ)) (n := (0 : NNReal)) (ω := ω) hj.1 hjUpper).trans hj.2
  · rintro ⟨hLower, hUpper⟩
    refine ⟨hLower, ?_⟩
    have hExitLeUpper :
        brownianIntervalExitTime W x a ω ≤ hittingAfter W ({a - x} : Set ℝ) 0 ω := by
      exact
        hittingAfter_apply_anti (u := W) (n := 0) (ω := ω) <|
          by
            intro z hz
            exact Or.inr (by simpa using hz)
    -- Proof comment: an upper-barrier hit by time `T` is already a two-barrier exit by time `T`,
    -- while `hLower` supplies the surviving-lower-barrier half of `upperLoss`.
    exact not_lt_of_ge (hExitLeUpper.trans hUpper)

/-- Helper for Exercise 21.3.1: the gap between lower-barrier survival and interval survival is
exactly the real mass of the `upperLoss` event `lower \\ interval`. -/
theorem intervalSurvivalGap_eq_upperLossRealLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} :
    μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} -
        μ.real {ω | T < brownianIntervalExitTime W x a ω} =
      μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}) := by
  let Wc : NNReal → Ω → ℝ := brownianContinuousVersion (μ := μ) (B := W) hW
  have hIntervalMeasWc :
      MeasurableSet {ω | T < brownianIntervalExitTime Wc x a ω} := by
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc
        (fun t ↦ (brownianContinuousVersion_measurable (μ := μ) (B := W) hW t).stronglyMeasurable)
    have hStopWc :
        IsStoppingTime ℱWc (brownianIntervalExitTime Wc x a) := by
      -- Proof comment: the patched continuous version has everywhere-continuous paths, so the
      -- owner two-sided hitting-time stopping theorem applies on that modified process.
      simpa [ℱWc, brownianIntervalExitTime] using
        (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
          (X := Wc)
          (hXsm := fun t ↦
            (brownianContinuousVersion_measurable (μ := μ) (B := W) hW t).stronglyMeasurable)
          (hXcont := brownianContinuousVersion_continuous (μ := μ) (B := W) hW)
          (a := -x) (b := a - x))
    have hEq :
        {ω | T < brownianIntervalExitTime Wc x a ω} =
          ({ω | brownianIntervalExitTime Wc x a ω ≤ T})ᶜ := by
      ext ω
      simp [not_le]
    rw [hEq]
    exact (ℱWc.le T _ (hStopWc.measurableSet_le T)).compl
  have hIntervalAe :
      {ω | T < brownianIntervalExitTime W x a ω} =ᵐ[μ]
        {ω | T < brownianIntervalExitTime Wc x a ω} := by
    -- Proof comment: outside the null exceptional set of the continuous version, both paths
    -- agree at every time, so their two-sided exit clocks coincide.
    filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := W) hW] with ω hω
    have hClock :
        brownianIntervalExitTime W x a ω = brownianIntervalExitTime Wc x a ω := by
      simpa [brownianIntervalExitTime] using
        (twoSidedBoundaryHittingTime_eq_of_forall_eq
          (X := W) (Y := Wc) (a := -x) (b := a - x) (ω := ω)
          (fun t ↦ (hω t).symm))
    change (T < brownianIntervalExitTime W x a ω) = (T < brownianIntervalExitTime Wc x a ω)
    rw [hClock]
  have hIntervalNullMeas :
      NullMeasurableSet {ω | T < brownianIntervalExitTime W x a ω} μ := by
    -- Proof comment: transfer measurability back from the everywhere-continuous modification
    -- along the almost-everywhere equality of the exit events.
    exact hIntervalMeasWc.nullMeasurableSet.congr hIntervalAe.symm
  have hSubset :
      {ω | T < brownianIntervalExitTime W x a ω} ⊆
        {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} :=
    intervalSurvival_event_subset_lowerSurvivalLocal (W := W) (x := x) (a := a) (T := T)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hFinite :
      μ {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ≠ ∞ := by
    exact measure_ne_top μ _
  have hInter :
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
          {ω | T < brownianIntervalExitTime W x a ω} =
        {ω | T < brownianIntervalExitTime W x a ω} := by
    -- Proof comment: interval survival is already contained in lower-barrier survival, so the
    -- intersection keeps only the smaller event.
    ext ω
    constructor
    · intro hω
      exact hω.2
    · intro hω
      exact ⟨hSubset hω, hω⟩
  have hDecomp :
      μ.real ({ω | T < brownianIntervalExitTime W x a ω}) +
          μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
            {ω | T < brownianIntervalExitTime W x a ω}) =
        μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
    -- Proof comment: because interval survival is a subset of lower-barrier survival, the
    -- standard `inter + diff` decomposition collapses the intersection back to the interval
    -- event itself.
    have hDecomp0 :=
      (MeasureTheory.measureReal_inter_add_diff₀
        (μ := μ)
        (s := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω})
        (t := {ω | T < brownianIntervalExitTime W x a ω})
        hIntervalNullMeas hFinite)
    rw [hInter] at hDecomp0
    exact hDecomp0
  -- Proof comment: rearrange the scalar decomposition to isolate the upper-loss difference.
  linarith

/-- Helper for Exercise 21.3.1: the nonnegative strip masses on the nonnegative side telescope to
the upper Gaussian tail, so they form a summable `ℕ`-series. -/
theorem shiftedStripMass_nat_hasSumLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℕ ↦ shiftedStripMass x a T n)
      (1 - cdf (gaussianReal x T) 0) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ shiftedStripMass x a T n := by
    intro n
    simpa using shiftedStripMass_nonneg (x := x) (a := a) (T := T) (n := (n : ℤ))
  have hterm :
      ∀ n : ℕ,
        shiftedStripMass x a T n =
          cdf (gaussianReal x T) (((n : ℝ) + 1) * a) -
            cdf (gaussianReal x T) ((n : ℝ) * a) := by
    intro n
    simpa using
      shiftedStripMass_eq_cdf_sub
        (x := x) (a := a) ha.le (T := T) hT (n := (n : ℤ))
  have hpartial (n : ℕ) :
      Finset.sum (Finset.range n) (fun i ↦ shiftedStripMass x a T i) =
        cdf (gaussianReal x T) ((n : ℝ) * a) - cdf (gaussianReal x T) 0 := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, hterm n]
        have hsucc : ((n : ℝ) + 1) * a = ((n + 1 : ℕ) : ℝ) * a := by
          norm_num
        rw [hsucc]
        ring
  have hScaled :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * a) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hCdf :
      Tendsto (fun n : ℕ ↦ cdf (gaussianReal x T) ((n : ℝ) * a)) atTop (𝓝 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop (μ := gaussianReal x T)).comp hScaled
  have hLimit :
      Tendsto
        (fun n : ℕ ↦ cdf (gaussianReal x T) ((n : ℝ) * a) - cdf (gaussianReal x T) 0)
        atTop
        (𝓝 (1 - cdf (gaussianReal x T) 0)) := by
    simpa using hCdf.sub tendsto_const_nhds
  -- Proof comment: identify the partial sums explicitly as a telescoping cdf difference and send
  -- the right endpoint to `+∞`.
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2 ?_
  convert hLimit using 1
  ext n
  rw [hpartial n]

/-- Helper for Exercise 21.3.1: the negative-index strip masses telescope to the lower Gaussian
tail, so the reflected `ℕ`-series over `-(n + 1)` is summable as well. -/
theorem shiftedStripMass_neg_add_one_hasSumLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℕ ↦ shiftedStripMass x a T (-(n + 1 : ℤ)))
      (cdf (gaussianReal x T) 0) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ shiftedStripMass x a T (-(n + 1 : ℤ)) := by
    intro n
    exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (n := (-(n + 1 : ℤ)))
  have hterm :
      ∀ n : ℕ,
        shiftedStripMass x a T (-(n + 1 : ℤ)) =
          cdf (gaussianReal x T) (-((n : ℝ) * a)) -
            cdf (gaussianReal x T) (((-1 : ℝ) - (n : ℝ)) * a) := by
    intro n
    have h :=
      shiftedStripMass_eq_cdf_sub
        (x := x) (a := a) ha.le (T := T) hT (n := (-(n + 1 : ℤ)))
    have hu : ((((-(n + 1 : ℤ) : ℤ) : ℝ) + 1) * a) = -((n : ℝ) * a) := by
      simp
    simpa [hu] using h
  have hpartial (n : ℕ) :
      Finset.sum (Finset.range n) (fun i ↦ shiftedStripMass x a T (-(i + 1 : ℤ))) =
        cdf (gaussianReal x T) 0 - cdf (gaussianReal x T) (-((n : ℝ) * a)) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, hterm n]
        have hsucc : (((-1 : ℝ) - (n : ℝ)) * a) = -(((n + 1 : ℕ) : ℝ) * a) := by
          norm_num
          ring
        rw [hsucc]
        ring
  have hScaled :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * a) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hNegScaled :
      Tendsto (fun n : ℕ ↦ -((n : ℝ) * a)) atTop atBot := by
    refine (tendsto_neg_atTop_atBot.comp hScaled).congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ rfl
  have hCdf :
      Tendsto (fun n : ℕ ↦ cdf (gaussianReal x T) (-((n : ℝ) * a))) atTop (𝓝 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot (μ := gaussianReal x T)).comp hNegScaled
  have hLimit :
      Tendsto
        (fun n : ℕ ↦ cdf (gaussianReal x T) 0 - cdf (gaussianReal x T) (-((n : ℝ) * a)))
        atTop
        (𝓝 (cdf (gaussianReal x T) 0)) := by
    simpa using tendsto_const_nhds.sub hCdf
  -- Proof comment: the negative strips telescope against the lower tail, and that tail vanishes
  -- when the left endpoint drifts to `-∞`.
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2 ?_
  convert hLimit using 1
  ext n
  rw [hpartial n]

/-- Helper for Exercise 21.3.1: combining the positive and negative strip decompositions gives
absolute summability of the full Gaussian strip series over `ℤ`. -/
theorem summable_shiftedStripMassLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Summable (fun n : ℤ ↦ shiftedStripMass x a T n) := by
  -- Proof comment: split the `ℤ`-series into its nonnegative and negative halves and use the two
  -- telescoping Gaussian tail computations above.
  exact Summable.of_nat_of_neg_add_one
    (shiftedStripMass_nat_hasSumLocal (x := x) (a := a) ha hT).summable
    (shiftedStripMass_neg_add_one_hasSumLocal (x := x) (a := a) ha hT).summable

/-- Helper for Exercise 21.3.1: the alternating Gaussian strip series is absolutely summable,
because the sign factor has absolute value `1` on every strip. -/
theorem summable_parityShiftedStripMassLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Summable (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n) := by
  -- Proof comment: compare the norm of each signed strip mass to the unsigned strip mass, which
  -- is already known to be summable.
  refine Summable.of_norm_bounded (summable_shiftedStripMassLocal (x := x) (a := a) ha hT) ?_
  intro n
  have hmass : 0 ≤ shiftedStripMass x a T n :=
    shiftedStripMass_nonneg (x := x) (a := a) (T := T) n
  by_cases hEven : Even n
  · rw [paritySign, if_pos hEven]
    rw [one_mul, Real.norm_eq_abs]
    simpa [abs_of_nonneg hmass] using (le_rfl : shiftedStripMass x a T n ≤ shiftedStripMass x a T n)
  · rw [paritySign, if_neg hEven]
    rw [neg_mul, Real.norm_eq_abs]
    simpa [abs_of_nonneg hmass] using (le_rfl : shiftedStripMass x a T n ≤ shiftedStripMass x a T n)

/-- Helper for Exercise 21.3.1: the paired shell series is summable because it is the
`nat_add_neg_add_one` repackaging of the full alternating strip series over `ℤ`. -/
theorem summable_alternatingStripPairShellLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Summable (alternatingStripPairShell x a T) := by
  -- Proof comment: summability is already known for the full centered `ℤ`-series, so pairing the
  -- nonnegative and negative indices into one `ℕ`-indexed shell keeps the same convergence.
  have hPair :
      Summable (fun n : ℕ ↦
        paritySign (n : ℤ) * shiftedStripMass x a T (n : ℤ) +
          paritySign (-(n + 1 : ℤ)) * shiftedStripMass x a T (-(n + 1 : ℤ))) := by
    simpa using
      (summable_parityShiftedStripMassLocal (x := x) (a := a) ha hT).nat_add_neg_add_one
  convert hPair using 1

/-- Helper for Exercise 21.3.1: if the paired `ℕ`-shell series has sum `l`, then the original
centered `ℤ`-series has the same sum. -/
theorem hasSum_of_alternatingStripPairShellLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) {l : ℝ}
    (hshell : HasSum (alternatingStripPairShell x a T) l) :
    HasSum (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n) l := by
  have hsum :
      Summable (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n) :=
    summable_parityShiftedStripMassLocal (x := x) (a := a) ha hT
  have htsum :
      (∑' n : ℤ, paritySign n * shiftedStripMass x a T n) = l := by
    -- Proof comment: `tsum_nat_add_neg_add_one` is exactly the canonical transport from the full
    -- centered `ℤ`-series to the paired `ℕ`-shell series.
    rw [← tsum_nat_add_neg_add_one hsum]
    simpa [alternatingStripPairShell] using hshell.tsum_eq
  -- Proof comment: once the two `tsum` values agree, the full `ℤ`-series inherits the desired
  -- `HasSum` statement from its already established summability.
  exact hsum.hasSum_iff.mpr htsum

/-- Helper for Exercise 21.3.1: if the paired shell prefixes are `l` plus a remainder tending to
`0`, then the paired shell series has sum `l`. -/
theorem hasSum_alternatingStripPairShell_of_prefixRemainderLocal
    {g : ℕ → ℝ} (hg : Summable g) {l : ℝ} {remainder : ℕ → ℝ}
    (hprefix : ∀ N : ℕ, (∑ n ∈ Finset.range N, g n) = l + remainder N)
    (hrem : Tendsto remainder atTop (𝓝 0)) :
    HasSum g l := by
  have hprefixTendsto :
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, g n) atTop (𝓝 l) := by
    -- Proof comment: the explicit prefix formula reduces convergence of the partial sums to the
    -- vanishing of the remainder term.
    have hSumTendsto : Tendsto (fun N : ℕ ↦ l + remainder N) atTop (𝓝 l) := by
      simpa using (tendsto_const_nhds.add hrem)
    exact hSumTendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hprefix N).symm)
  have htsum : (∑' n : ℕ, g n) = l := by
    -- Proof comment: a summable series has a unique limit for its ordered partial sums, so the
    -- limit extracted from the prefix formula must be the `tsum`.
    exact tendsto_nhds_unique hg.hasSum.tendsto_sum_nat hprefixTendsto
  exact hg.hasSum_iff.mpr htsum

/-- Helper for Exercise 21.3.1: convergence of the shifted sequence `u (n + 1)` already forces
convergence of the original sequence `u n`. -/
theorem tendsto_atTop_of_add_oneLocal
    {u : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n : ℕ ↦ u (n + 1)) atTop (𝓝 l)) :
    Tendsto u atTop (𝓝 l) := by
  -- Proof comment: dropping finitely many initial terms does not change the limit of a sequence
  -- at `atTop`, so we unwrap `n ≥ N + 1` as `n = (N + m) + 1`.
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N + 1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hNm : N ≤ N + m := Nat.le_add_right N m
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hN (N + m) hNm

/-- Helper for Exercise 21.3.1: if the even values of a sequence lie below `l`, the odd values
lie above `l`, and the odd-even gap tends to `0`, then the full sequence converges to `l`. -/
theorem tendsto_of_paritySqueezeLocal
    {u : ℕ → ℝ} {l : ℝ}
    (hBounds : ∀ N : ℕ, u (2 * N) ≤ l ∧ l ≤ u (2 * N + 1))
    (hGap : Tendsto (fun N : ℕ ↦ u (2 * N + 1) - u (2 * N)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 l) := by
  -- Proof comment: the parity bounds pin both subsequences against `l`, while the vanishing
  -- odd-even gap forces the distance from each side to be controlled by the same shrinking error.
  rw [Metric.tendsto_atTop] at hGap ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hGap ε hε
  refine ⟨2 * N, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨k, rfl⟩
    have hk : N ≤ k := by omega
    have hkBounds := hBounds k
    have hGapNonneg : 0 ≤ u (2 * k + 1) - u (2 * k) := by
      linarith
    have hGapLt : u (2 * k + 1) - u (2 * k) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg hGapNonneg] using hN k hk
    have hLowerNonneg : 0 ≤ l - u (2 * k) := by
      linarith
    have hLowerLe : l - u (2 * k) ≤ u (2 * k + 1) - u (2 * k) := by
      linarith
    have hLowerLt : l - u (2 * k) < ε := lt_of_le_of_lt hLowerLe hGapLt
    have hLowerNonneg' : 0 ≤ l - u (k + k) := by
      simpa [two_mul] using hLowerNonneg
    have hAbs : |l - u (k + k)| < ε := by
      rw [abs_of_nonneg hLowerNonneg']
      simpa [two_mul] using hLowerLt
    have hDist : dist (u (2 * k)) l < ε := by
      simpa [Real.dist_eq, two_mul, abs_sub_comm] using hAbs
    simpa [two_mul] using hDist
  · rcases hOdd with ⟨k, rfl⟩
    have hk : N ≤ k := by omega
    have hkBounds := hBounds k
    have hGapNonneg : 0 ≤ u (2 * k + 1) - u (2 * k) := by
      linarith
    have hGapLt : u (2 * k + 1) - u (2 * k) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg hGapNonneg] using hN k hk
    have hUpperNonneg : 0 ≤ u (2 * k + 1) - l := by
      linarith
    have hUpperLe : u (2 * k + 1) - l ≤ u (2 * k + 1) - u (2 * k) := by
      linarith
    have hUpperLt : u (2 * k + 1) - l < ε := lt_of_le_of_lt hUpperLe hGapLt
    have hUpperNonneg' : 0 ≤ u (k + k + 1) - l := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hUpperNonneg
    have hAbs : |u (k + k + 1) - l| < ε := by
      rw [abs_of_nonneg hUpperNonneg']
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hUpperLt
    have hDist : dist (u (2 * k + 1)) l < ε := by
      simpa [Real.dist_eq, two_mul] using hAbs
    simpa [two_mul] using hDist

/-- Helper for Exercise 21.3.1: the one-sided lower-barrier survival probability already equals
the signed strip series with positive sign on the nonnegative strips and negative sign on the
reflected negative strips. -/
theorem lowerBarrierSignedStripSeries_hasSumLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum
      (fun n : ℤ ↦ if 0 ≤ n then shiftedStripMass x a T n else -shiftedStripMass x a T n)
      (μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}) := by
  have ha : 0 < a := by
    linarith
  let f : ℤ → ℝ := fun n ↦ if 0 ≤ n then shiftedStripMass x a T n else -shiftedStripMass x a T n
  have hnat :
      HasSum (fun n : ℕ ↦ f n) (1 - cdf (gaussianReal x T) 0) := by
    -- Proof comment: on the nonnegative side, the strips partition the terminal half-line
    -- `[0, ∞)`, so the strip series is exactly the positive Gaussian tail.
    simpa [f] using shiftedStripMass_nat_hasSumLocal (x := x) (a := a) ha hT
  have hneg :
      HasSum (fun n : ℕ ↦ f (-(n + 1 : ℤ))) (-cdf (gaussianReal x T) 0) := by
    -- Proof comment: on the negative side, the same telescoping computation gives the lower
    -- Gaussian tail, now with the global minus sign built into `f`.
    have hEval :
        (fun n : ℕ ↦ f (-(n + 1 : ℤ))) =
          (fun n : ℕ ↦ -shiftedStripMass x a T (-(n + 1 : ℤ))) := by
      ext n
      have hlt : ¬ 0 ≤ (-(n + 1 : ℤ)) := by
        omega
      rw [show f (-(n + 1 : ℤ)) = -shiftedStripMass x a T (-(n + 1 : ℤ)) by
        dsimp [f]
        rw [if_neg hlt]]
    rw [hEval]
    simpa using (shiftedStripMass_neg_add_one_hasSumLocal (x := x) (a := a) ha hT).neg
  have hstrip :
      HasSum f ((1 - cdf (gaussianReal x T) 0) + (-cdf (gaussianReal x T) 0)) :=
    hnat.of_nat_of_neg_add_one hneg
  have hTail :
      μ.real {ω | W T ω ≤ -x} = cdf (gaussianReal x T) 0 := by
    have hSet :
        {ω | W T ω ≤ -x} = {ω | x + W T ω ∈ Set.Iic 0} := by
      ext ω
      constructor
      · intro hω
        simpa [Set.mem_Iic, add_comm, add_left_comm, add_assoc] using add_le_add_left hω x
      · intro hω
        simpa [Set.mem_Iic, add_comm, add_left_comm, add_assoc] using
          add_le_add_left hω (-x)
    -- Proof comment: the lower tail of `W T` is exactly the centered strip boundary event after
    -- shifting the Gaussian terminal law by the deterministic start point `x`.
    calc
      μ.real {ω | W T ω ≤ -x} = μ.real {ω | x + W T ω ∈ Set.Iic 0} := by
        rw [hSet]
      _ = (gaussianReal x T).real (Set.Iic 0) := by
            exact
              shiftedBrownianTerminalReal_eq_gaussianReal
                (hW := hW) (x := x) (T := T) hT measurableSet_Iic
      _ = cdf (gaussianReal x T) 0 := by
            rw [← ProbabilityTheory.cdf_eq_real (μ := gaussianReal x T) 0]
  have hLower :
      μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} =
        1 - 2 * cdf (gaussianReal x T) 0 := by
    letI : IsBrownianMotionStartedAt μ W 0 := inferInstance
    -- Proof comment: the one-sided reflection principle rewrites lower-barrier survival as the
    -- same boundary cdf difference produced by the strip telescoping.
    calc
      μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
          = 1 - 2 * μ.real {ω | W T ω ≤ -x} := by
              exact startedAtZero_survivalAboveLowerBarrier_eq_boundaryCdf inferInstance hx hT
      _ = 1 - 2 * cdf (gaussianReal x T) 0 := by
            rw [hTail]
  -- Proof comment: combine the positive and negative strip sums, then identify their common value
  -- with the lower-barrier survival probability.
  rw [hLower]
  convert hstrip using 1
  ring

/-- Helper for Exercise 21.3.1: pairing the already proved one-sided strip series over `ℤ` gives
the natural `ℕ`-indexed shell differences `m_n - m_{-(n+1)}`. -/
theorem lowerBarrierStripPairShell_hasSumLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum
      (fun n : ℕ ↦ shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
      (μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}) := by
  -- Proof comment: the one-sided owner theorem already lives on the full centered `ℤ`-series; the
  -- standard `nat_add_neg_add_one` transport repackages it into the shell differences.
  convert
      (lowerBarrierSignedStripSeries_hasSumLocal
        (hW := hW) (x := x) (a := a) hx hxa hT).nat_add_neg_add_one using 1

/-- Helper for Exercise 21.3.1: the centered prefix over `[-N, N]` is the paired-shell prefix up
to `N`, minus the single reflected outer strip at `-(N + 1)`. -/
theorem centeredAlternatingPrefix_eq_shellPrefix_sub_outerLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun n ↦ paritySign n * shiftedStripMass x a T n)) =
      (Finset.sum (Finset.range (N + 1)) (fun n ↦ alternatingStripPairShell x a T n)) -
        paritySign (-(N + 1 : ℤ)) * shiftedStripMass x a T (-(N + 1 : ℤ)) := by
  induction N with
  | zero =>
      -- Proof comment: at `N = 0`, the shell prefix contains the central strip together with the
      -- first reflected outer strip, so subtracting that outer strip leaves exactly the centered
      -- singleton prefix.
      simp [alternatingStripPairShell]
  | succ N ih =>
      have hSplit :
          Finset.Icc (-((N + 1 : ℕ) : ℤ)) (((N + 1 : ℕ) : ℤ)) =
            insert (-((N + 1 : ℕ) : ℤ))
              (insert (((N + 1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
        ext z
        simp [Finset.mem_Icc]
        omega
      have hNegNotMem :
          (-((N + 1 : ℕ) : ℤ)) ∉
            insert (((N + 1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
        simp [Finset.mem_Icc]
        omega
      have hPosNotMem :
          (((N + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp [Finset.mem_Icc]
      -- Proof comment: the step from `N` to `N + 1` adds the new symmetric endpoints; after the
      -- induction hypothesis, the previous outer strip cancels against the newly appended shell.
      have hRange :
          (Finset.sum (Finset.range (N + 2)) (fun n ↦ alternatingStripPairShell x a T n)) =
            (Finset.sum (Finset.range (N + 1)) (fun n ↦ alternatingStripPairShell x a T n)) +
              alternatingStripPairShell x a T (N + 1) := by
        rw [Finset.sum_range_succ]
      have hNegCast : (-(↑N + 1 : ℤ)) = -((N + 1 : ℕ) : ℤ) := by
        omega
      rw [show Finset.Icc (-((N + 1 : ℕ) : ℤ)) (((N + 1 : ℕ) : ℤ)) =
          insert (-((N + 1 : ℕ) : ℤ))
            (insert (((N + 1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) (N : ℤ))) from hSplit,
        Finset.sum_insert, Finset.sum_insert]
      · rw [ih, hRange, alternatingStripPairShell, hNegCast, sub_eq_add_neg]
        abel_nf
      · exact hPosNotMem
      · exact hNegNotMem

/-- Helper for Exercise 21.3.1: the single reflected outer strip in the centered prefix
decomposition escapes to `-∞`, so its Gaussian mass tends to `0`. -/
theorem reflectedOuterStripMass_tendsto_zeroLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ ↦ shiftedStripMass x a T (-(N + 1 : ℤ)))
      Filter.atTop (𝓝 0) := by
  have hScaled :
      Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) * a) Filter.atTop Filter.atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hScaledSucc :
      Filter.Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) * a) Filter.atTop Filter.atTop := by
    exact hScaled.comp (tendsto_add_atTop_nat 1)
  have hRewrite :
      (fun N : ℕ ↦ shiftedStripMass x a T (-(N + 1 : ℤ))) =
        (fun N : ℕ ↦
          (gaussianReal x T).real
            (Set.Ioc (((-1 : ℝ) - (N : ℝ)) * a) (-((N : ℝ) * a)))) := by
    funext N
    simpa using shiftedStripMass_eq_Ioc (x := x) (a := a) (T := T) hT (n := (-(N + 1 : ℤ)))
  rw [hRewrite]
  have hLower :
      Filter.Tendsto (fun N : ℕ ↦ (((-1 : ℝ) - (N : ℝ)) * a)) Filter.atTop Filter.atBot := by
    have hLowerEq :
        (fun N : ℕ ↦ (((-1 : ℝ) - (N : ℝ)) * a)) =
          fun N : ℕ ↦ -(((N + 1 : ℕ) : ℝ) * a) := by
      funext N
      calc
        (((-1 : ℝ) - (N : ℝ)) * a) = -((((N : ℝ) + 1) * a)) := by ring
        _ = -(((N + 1 : ℕ) : ℝ) * a) := by
          congr 1
          norm_num
    rw [hLowerEq]
    exact tendsto_neg_atTop_atBot.comp hScaledSucc
  have hUpper :
      Filter.Tendsto (fun N : ℕ ↦ -((N : ℝ) * a)) Filter.atTop Filter.atBot := by
    exact tendsto_neg_atTop_atBot.comp hScaled
  -- Proof comment: the reflected strip has fixed width `a`, and both endpoints drift to `-∞`, so
  -- the generic Gaussian `Ioc` tail lemma applies directly.
  refine gaussianIocMass_tendsto_zero_of_endpoints_atBotLocal ?_ hLower hUpper
  intro N
  nlinarith [ha.le]

/-- Helper for Exercise 21.3.1: the odd shell-correction term is controlled by the two outer strip
masses at the same shell level, so it vanishes when the shell index escapes to infinity. -/
theorem upperLossCorrection_oddTerm_tendsto_zeroLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Tendsto
      (fun N : ℕ ↦
        2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) -
          shiftedStripMass x a T (-(2 * N + 2 : ℤ))))
      atTop (𝓝 0) := by
  have hIndex : Tendsto (fun N : ℕ ↦ 2 * N + 1) atTop atTop := by
    refine tendsto_atTop_mono ?_ tendsto_id
    intro N
    calc
      N ≤ N + N := by simpa [two_mul] using Nat.le_add_left N N
      _ ≤ N + N + 1 := Nat.le_succ (N + N)
      _ = 2 * N + 1 := by ring
  have hOuter :
      Tendsto
        (fun N : ℕ ↦
          shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ)))
        atTop (𝓝 0) := by
    convert (outerStripMass_tendsto_zeroLocal (x := x) (a := a) ha hT).comp hIndex using 1 with N
  rw [Metric.tendsto_atTop] at hOuter ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := hOuter (ε / 2) hε2
  refine ⟨N, ?_⟩
  intro n hn
  let mPos : ℝ := shiftedStripMass x a T (2 * n + 1 : ℤ)
  let mNeg : ℝ := shiftedStripMass x a T (-(2 * n + 2 : ℤ))
  have hmPos : 0 ≤ mPos := by
    dsimp [mPos]
    exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (2 * n + 1 : ℤ)
  have hmNeg : 0 ≤ mNeg := by
    dsimp [mNeg]
    exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (-(2 * n + 2 : ℤ))
  have hOuterAbs : |mPos + mNeg| < ε / 2 := by
    have hOuterDist := hN n hn
    simpa [Real.dist_eq, mPos, mNeg] using hOuterDist
  have hOuterLt : mPos + mNeg < ε / 2 := by
    simpa [abs_of_nonneg (add_nonneg hmPos hmNeg)] using hOuterAbs
  have hAbsLe : |2 * (mPos - mNeg)| ≤ 2 * (mPos + mNeg) := by
    have hCore : |mPos - mNeg| ≤ mPos + mNeg := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith
    calc
      |2 * (mPos - mNeg)| = 2 * |mPos - mNeg| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (mPos + mNeg) := by
        gcongr
  have hDistLt : dist (2 * (mPos - mNeg)) 0 < ε := by
    have hTwoOuterLt : 2 * (mPos + mNeg) < ε := by
      nlinarith
    have hAbsLt : |2 * (mPos - mNeg)| < ε := lt_of_le_of_lt hAbsLe hTwoOuterLt
    simpa [Real.dist_eq] using hAbsLt
  simpa [mPos, mNeg] using hDistLt

/-- Helper for Exercise 21.3.1: consecutive even and odd correction prefixes differ by exactly
the last odd shell term. This is the parity-gap identity consumed by the squeeze argument. -/
theorem upperLossCorrection_evenOddGap_eq_lastTermLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    (∑ n ∈ Finset.range (2 * N + 2), correction n) -
        (∑ n ∈ Finset.range (2 * N + 1), correction n) =
      2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  dsimp
  have hOdd : ¬ Even (2 * N + 1) := by
    intro hEven
    rcases hEven with ⟨m, hm⟩
    omega
  -- Proof comment: extending the shorter prefix by one index adds the unique odd shell term at
  -- `2 * N + 1`, so subtracting the two prefixes isolates exactly that contribution.
  rw [Finset.sum_range_succ]
  rw [if_neg hOdd]
  simpa [two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]

/-- Helper for Exercise 21.3.1: once the odd and even correction prefixes squeeze a scalar `l`,
the full correction-prefix sequence converges to `l` by the existing parity-gap estimates. -/
theorem upperLossCorrection_tendsto_of_prefixBoundsLocal
    {x a l : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T)
    (hBounds : ∀ N : ℕ,
      let correction : ℕ → ℝ := fun n ↦
        if Even n then 0 else
          2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
      (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤ l ∧
        l ≤ (∑ n ∈ Finset.range (2 * N + 2), correction n)) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, correction n) atTop (𝓝 l) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  have hBounds' :
      ∀ N : ℕ,
        (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤ l ∧
          l ≤ (∑ n ∈ Finset.range (2 * N + 2), correction n) := by
    intro N
    simpa [correction] using hBounds N
  have hParityBounds :
      ∀ N : ℕ,
        (∑ n ∈ Finset.range ((2 * N) + 1), correction n) ≤ l ∧
          l ≤ (∑ n ∈ Finset.range ((2 * N + 1) + 1), correction n) := by
    intro N
    convert hBounds' N using 1 <;> omega
  have hGap :
      Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range ((2 * N + 1) + 1), correction n) -
            (∑ n ∈ Finset.range ((2 * N) + 1), correction n))
        atTop (𝓝 0) := by
    -- Proof comment: the shifted odd-even gap is exactly the final odd shell term, which is
    -- already known to vanish at infinity.
    convert upperLossCorrection_oddTerm_tendsto_zeroLocal (x := x) (a := a) ha hT using 1
    ext N
    convert
      (upperLossCorrection_evenOddGap_eq_lastTermLocal
        (x := x) (a := a) (T := T) N) using 1 <;>
      omega
  have hShifted :
      Tendsto
        (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), correction n)
        atTop (𝓝 l) := by
    -- Proof comment: apply the parity squeeze to the one-step-shifted prefix sequence so that its
    -- even and odd terms match the odd and even correction prefixes.
    exact tendsto_of_paritySqueezeLocal hParityBounds hGap
  -- Proof comment: dropping the first term of a sequence does not affect its limit at `atTop`.
  exact
    tendsto_atTop_of_add_oneLocal
      (u := fun N : ℕ ↦ ∑ n ∈ Finset.range N, correction n) hShifted

/-- Helper for Exercise 21.3.1: on continuous Brownian paths, hitting the upper level `b` by time
`T` is equivalent to the closed running-maximum event on `[0, T]`. -/
theorem hitUpperBeforeTime_event_ae_eq_runningMaxClosedLocal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T} =ᵐ[μ]
      ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) := by
  -- Proof comment: on every continuous sample path, `hittingAfter ≤ T` gives a witness in
  -- `[0, T]`, and continuity upgrades the closed running-maximum witness back to an exact hit.
  filter_upwards [hB.continuous_paths] with ω hω
  apply propext
  constructor
  · intro hHit
    classical
    let hitSet : Set NNReal := {t : NNReal | B t ω = b}
    have hHit_ne_top : hittingAfter B ({b} : Set ℝ) 0 ω ≠ ⊤ := by
      have hT_ne_top : ((T : NNReal) : ENNReal) ≠ ⊤ := by simp
      exact ne_top_of_le_ne_top hT_ne_top hHit
    have hHitSet_nonempty : hitSet.Nonempty := by
      by_contra hEmpty
      have hTop : hittingAfter B ({b} : Set ℝ) 0 ω = ⊤ := by
        rw [hittingAfter_eq_top_iff]
        intro t ht0 ht_mem
        exact hEmpty ⟨t, by simpa [hitSet] using ht_mem⟩
      exact hHit_ne_top hTop
    have hHitSet_closed : IsClosed hitSet := by
      simpa [hitSet, processPath] using (isClosed_singleton.preimage hω)
    have hHitSet_bddBelow : BddBelow hitSet := by
      refine ⟨0, ?_⟩
      intro t ht_mem
      positivity
    have hInf_mem : sInf hitSet ∈ hitSet :=
      hHitSet_closed.csInf_mem hHitSet_nonempty hHitSet_bddBelow
    have hInf_le : sInf hitSet ≤ T := by
      have hExistsEq : ∃ j : NNReal, B j ω = b := hHitSet_nonempty
      have hHitProp :
          (if ∃ j : NNReal, B j ω = b then ((sInf hitSet : NNReal) : ENNReal) else ⊤) ≤
            (T : ENNReal) := by
        simpa [hittingAfter_def, hitSet] using hHit
      have hHit' : ((sInf hitSet : NNReal) : ENNReal) ≤ (T : ENNReal) := by
        simpa [hExistsEq] using hHitProp
      exact ENNReal.coe_le_coe.mp hHit'
    exact ⟨sInf hitSet, ⟨by positivity, hInf_le⟩, by simpa [hitSet] using hInf_mem.ge⟩
  · rintro ⟨t, ht, ht_ge⟩
    by_cases ht_eq : B t ω = b
    · -- Proof comment: an exact hit at the witness time immediately closes the hitting-time side.
      exact (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
          (ω := ω) ht.1 (by simp [ht_eq])).trans (by exact_mod_cast ht.2)
    · have hb_mem : b ∈ Set.Icc (B 0 ω) (B t ω) := by
        refine ⟨?_, ht_ge⟩
        simpa [hB.zero] using hb.le
      obtain ⟨s, hsIcc, hs_eq⟩ :=
        (intermediate_value_Icc
          (a := (0 : NNReal))
          (b := t)
          ht.1
          hω.continuousOn) hb_mem
      -- Proof comment: if the witness only reaches `b` weakly, the intermediate value theorem
      -- recovers an exact hit earlier on the same path segment.
      exact
        (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
          (ω := ω) hsIcc.1 (by simpa [processPath] using hs_eq)).trans <|
          by
            exact_mod_cast hsIcc.2.trans ht.2

/-- Helper for Exercise 21.3.1: adjoining the terminal cutoff preserves the almost-sure bridge
between the upper-hit event and the closed running-maximum event. -/
theorem hitUpperBeforeTime_terminalBelow_event_ae_eq_runningMaxClosedLocal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T ∧ B T ω ≤ y} =ᵐ[μ]
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) ∩
        {ω | B T ω ≤ y}) : Set Ω) := by
  -- Proof comment: intersect the hit-by-time/running-maximum bridge with the shared terminal
  -- cutoff event `B T ≤ y`.
  filter_upwards [hitUpperBeforeTime_event_ae_eq_runningMaxClosedLocal (μ := μ) (B := B) hB hb
      (T := T)] with ω hω
  apply propext
  constructor
  · intro hω'
    exact ⟨hω.mp hω'.1, hω'.2⟩
  · rintro ⟨hRun, hTerm⟩
    exact ⟨hω.mpr hRun, hTerm⟩

/-- Helper for Exercise 21.3.1: Brownian scaling transports the closed upper-hit slice on
`[0, T]` to the corresponding unit-time slice for the scaled Brownian motion. -/
theorem scaledClosedRunningMaximum_terminalBelow_event_eqLocal
    {B : NNReal → Ω → ℝ} {b y : ℝ} {T : NNReal} (hT : 0 < T) :
    ((({ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ B s ω} : Set Ω) ∩
      {ω | B T ω ≤ y}) : Set Ω) =
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) 1,
            b / Real.sqrt (T : ℝ) ≤
              brownianScaling B (Real.sqrt (T : ℝ)) t ω} : Set Ω) ∩
        {ω | brownianScaling B (Real.sqrt (T : ℝ)) 1 ω ≤ y / Real.sqrt (T : ℝ)}) : Set Ω) := by
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hSqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨s, hsIcc, hsLevel⟩, hTerm⟩
    refine ⟨?_, ?_⟩
    · refine ⟨s / T, ?_, ?_⟩
      · -- Proof comment: dividing the original witness time by the positive horizon `T` moves it
        -- into the unit interval.
        refine ⟨by positivity, ?_⟩
        exact (div_le_iff₀ hT).2 (by simpa using hsIcc.2)
      · -- Proof comment: after rewriting the scaled path at time `s / T`, the barrier inequality
        -- is just the original inequality divided by the positive factor `√T`.
        rw [brownianScaling_apply, brownianScalingTime_sqrt]
        rw [mul_div_cancel₀ _ (ne_of_gt hT)]
        simpa [div_eq_mul_inv, mul_comm] using
          (div_le_div_of_nonneg_right hsLevel hSqrt.le)
    · -- Proof comment: the terminal cutoff transports by the same positive division after
      -- evaluating the scaled process at unit time.
      rw [brownianScaling_apply, brownianScalingTime_sqrt]
      simpa [div_eq_mul_inv, mul_comm] using
        (div_le_div_of_nonneg_right hTerm hSqrt.le)
  · rintro ⟨⟨t, htIcc, htLevel⟩, hTerm⟩
    refine ⟨?_, ?_⟩
    · refine ⟨T * t, ?_, ?_⟩
      · -- Proof comment: multiplying the normalized witness time by `T` recovers a witness in
        -- the original interval `[0, T]`.
        refine ⟨by positivity, ?_⟩
        have hmul : T * t ≤ T * 1 := by
          simpa using mul_le_mul_of_nonneg_left htIcc.2 T.2
        simpa using hmul
      · -- Proof comment: once the scaled inequality is rewritten with a common positive
        -- denominator `√T`, cancel that denominator to recover the original barrier inequality.
        have htLevel' : b / Real.sqrt (T : ℝ) ≤ B (T * t) ω / Real.sqrt (T : ℝ) := by
          simpa [brownianScaling_apply, brownianScalingTime_sqrt, div_eq_mul_inv, mul_comm]
            using htLevel
        exact (div_le_div_iff_of_pos_right hSqrt).mp htLevel'
    · -- Proof comment: the terminal cutoff is recovered by the same denominator cancellation at
      -- unit time.
      have hTerm' : B T ω / Real.sqrt (T : ℝ) ≤ y / Real.sqrt (T : ℝ) := by
        simpa [brownianScaling_apply, brownianScalingTime_sqrt, div_eq_mul_inv, mul_comm]
          using hTerm
      exact (div_le_div_iff_of_pos_right hSqrt).mp hTerm'

/-- Helper for Exercise 21.3.1: the closed terminal Brownian tail at time `1` matches the
corresponding closed tail of the standard Gaussian marginal. -/
theorem brownianTerminalClosedTail_eq_standardGaussianClosedTailLocal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} :
    μ {ω | b ≤ B 1 ω} = (gaussianReal 0 1) (Set.Ici b) := by
  let hLaw : HasLaw (B 1) (gaussianReal 0 1) μ := hB.gaussian_marginal (by positivity)
  have hMapEq := congrArg (fun ν : Measure ℝ => ν (Set.Ici b)) hLaw.map_eq
  -- Proof comment: evaluate the Brownian time-`1` Gaussian marginal on the closed upper tail.
  simpa [Measure.map_apply ((hB.stronglyMeasurable 1).measurable) measurableSet_Ici] using hMapEq

/-- Helper for Exercise 21.3.1: the truncated weighted standard Gaussian integral is exactly the
reflected closed tail beyond `2 * b - y`. -/
theorem gaussianWeightedLowerSection_eq_reflectedClosedTailLocal
    {b y : ℝ} (_hyb : y < b) :
    ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x))) ∂(gaussianReal 0 1) =
      (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
  have hpdfReal :
      ∀ x : ℝ,
        Real.exp (-2 * b * (b - x)) * gaussianPDFReal 0 1 x = gaussianPDFReal (2 * b) 1 x := by
    intro x
    -- Proof comment: complete the square to absorb the exponential weight into the density of
    -- `N(2 * b, 1)`.
    rw [gaussianPDFReal_def, gaussianPDFReal_def]
    have hmul :
        Real.exp (-2 * b * (b - x)) *
            ((√(2 * Real.pi * (1 : ℝ≥0)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0)))) =
          (√(2 * Real.pi * (1 : ℝ≥0)))⁻¹ *
            (Real.exp (-2 * b * (b - x)) *
              Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0)))) := by
      ring
    rw [hmul, ← Real.exp_add]
    congr 2
    · norm_num
      ring
  have hpdf :
      ∀ x : ℝ,
        ENNReal.ofReal (Real.exp (-2 * b * (b - x))) * gaussianPDF 0 1 x =
          gaussianPDF (2 * b) 1 x := by
    intro x
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact congrArg ENNReal.ofReal (hpdfReal x)
  have hLeft :
      ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x))) ∂(gaussianReal 0 1) =
        (gaussianReal (2 * b) 1) (Set.Iic y) := by
    -- Proof comment: after the density rewrite, the weighted truncated integral becomes the left
    -- tail of the shifted Gaussian `N(2 * b, 1)`.
    rw [gaussianReal_of_var_ne_zero (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero]
    rw [MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀]
    · have hfun :
          (fun x : ℝ =>
            (gaussianPDF 0 1 * fun z => ENNReal.ofReal (Real.exp (-2 * b * (b - z)))) x) =
            fun x : ℝ => gaussianPDF (2 * b) 1 x := by
        funext x
        simpa [Pi.mul_apply, mul_comm] using hpdf x
      rw [hfun]
      exact (gaussianReal_apply (μ := 2 * b) (v := (1 : ℝ≥0)) one_ne_zero (Set.Iic y)).symm
    · fun_prop
    · fun_prop
    · exact measurableSet_Iic
  have hMap :
      (gaussianReal 0 1).map (fun x : ℝ ↦ 2 * b - x) = gaussianReal (2 * b) 1 := by
    -- Proof comment: reflecting the standard Gaussian across the midpoint `b` shifts the mean to
    -- `2 * b`.
    simpa using gaussianReal_map_const_sub (μ := 0) (v := (1 : ℝ≥0)) (y := 2 * b)
  have hReflect :
      (gaussianReal (2 * b) 1) (Set.Iic y) = (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
    -- Proof comment: pull the left tail of `N(2 * b, 1)` back through the affine reflection
    -- `x ↦ 2 * b - x`.
    rw [← hMap]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x
    simp
  -- Proof comment: the weighted integral is identified with a shifted Gaussian tail and then
  -- reflected back to the standard Gaussian tail.
  rw [hLeft, hReflect]

/-- Helper for Exercise 21.3.1: the one-sided lower-barrier survival probability can be rewritten
as the shifted Gaussian boundary cdf at `0`. -/
theorem lowerBarrierSurvival_eq_terminalBoundaryCdfLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (_hxa : x < a) {T : NNReal} (hT : 0 < T) :
    μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} =
      1 - 2 * cdf (gaussianReal x T) 0 := by
  letI : IsBrownianMotionStartedAt μ W 0 := inferInstance
  have hTail :
      μ.real {ω | W T ω ≤ -x} = cdf (gaussianReal x T) 0 := by
    have hSet :
        {ω | W T ω ≤ -x} = {ω | x + W T ω ∈ Set.Iic 0} := by
      ext ω
      constructor
      · intro hω
        simpa [Set.mem_Iic, add_comm, add_left_comm, add_assoc] using add_le_add_left hω x
      · intro hω
        simpa [Set.mem_Iic, add_comm, add_left_comm, add_assoc] using
          add_le_add_left hω (-x)
    -- Proof comment: shifting the terminal value by `x` turns the lower-barrier tail into the
    -- Gaussian lower tail at the centered boundary `0`.
    calc
      μ.real {ω | W T ω ≤ -x} = μ.real {ω | x + W T ω ∈ Set.Iic 0} := by
        rw [hSet]
      _ = (gaussianReal x T).real (Set.Iic 0) := by
            exact
              shiftedBrownianTerminalReal_eq_gaussianReal
                (hW := hW) (x := x) (T := T) hT measurableSet_Iic
      _ = cdf (gaussianReal x T) 0 := by
            rw [← ProbabilityTheory.cdf_eq_real (μ := gaussianReal x T) 0]
  -- Proof comment: apply the one-sided lower-barrier survival theorem and then rewrite the
  -- terminal boundary event by the shifted Gaussian marginal.
  calc
    μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
        = 1 - 2 * μ.real {ω | W T ω ≤ -x} := by
            exact startedAtZero_survivalAboveLowerBarrier_eq_boundaryCdf inferInstance hx hT
    _ = 1 - 2 * cdf (gaussianReal x T) 0 := by
          rw [hTail]

/-- Helper for Exercise 21.3.1: the one-sided upper-barrier survival probability can be rewritten
as the corresponding Gaussian boundary cdf at the translated terminal point `a`. -/
theorem upperBarrierSurvival_eq_terminalBoundaryCdfLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    μ.real {ω | T < hittingAfter W ({a - x} : Set ℝ) 0 ω} =
      2 * cdf (gaussianReal x T) a - 1 := by
  letI : IsBrownianMotionStartedAt μ W 0 := inferInstance
  have hUpperPos : 0 < a - x := by
    linarith
  have hTail :
      μ.real {ω | W T ω ≤ a - x} = cdf (gaussianReal x T) a := by
    have hSet :
        {ω | W T ω ≤ a - x} = {ω | x + W T ω ∈ Set.Iic a} := by
      ext ω
      constructor
      · intro hω
        simpa [Set.mem_Iic, add_comm, add_left_comm, add_assoc] using add_le_add_left hω x
      · intro hω
        have hShift : x + W T ω ≤ a := by
          simpa [Set.mem_Iic] using hω
        have hTarget : W T ω ≤ a - x := by
          linarith [hShift]
        exact hTarget
    -- Proof comment: shifting the terminal value by `x` turns the upper-barrier tail into the
    -- Gaussian lower tail at the physical endpoint `a`.
    calc
      μ.real {ω | W T ω ≤ a - x} = μ.real {ω | x + W T ω ∈ Set.Iic a} := by
        rw [hSet]
      _ = (gaussianReal x T).real (Set.Iic a) := by
            exact
              shiftedBrownianTerminalReal_eq_gaussianReal
                (hW := hW) (x := x) (T := T) hT measurableSet_Iic
      _ = cdf (gaussianReal x T) a := by
            rw [← ProbabilityTheory.cdf_eq_real (μ := gaussianReal x T) a]
  -- Proof comment: apply the already available one-sided upper-barrier survival theorem and then
  -- rewrite its terminal tail by the shifted Gaussian marginal.
  calc
    μ.real {ω | T < hittingAfter W ({a - x} : Set ℝ) 0 ω}
        = 2 * μ.real {ω | W T ω ≤ a - x} - 1 := by
            exact startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf inferInstance hUpperPos hT
    _ = 2 * cdf (gaussianReal x T) a - 1 := by
          rw [hTail]

/-- Helper for Exercise 21.3.1: each shell difference is the decrement of the boundary-tail
profile `n ↦ 1 - cdf (gaussianReal x T) (n * a) - cdf (gaussianReal x T) (-n * a)` between two
consecutive strip radii. -/
theorem shellDifference_eq_boundaryTailDiffLocal
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℕ) :
    let boundaryTail : ℕ → ℝ := fun m ↦
      1 - cdf (gaussianReal x T) ((m : ℝ) * a) -
        cdf (gaussianReal x T) (-((m : ℝ) * a))
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)) =
      boundaryTail n - boundaryTail (n + 1) := by
  let boundaryTail : ℕ → ℝ := fun m ↦
    1 - cdf (gaussianReal x T) ((m : ℝ) * a) -
      cdf (gaussianReal x T) (-((m : ℝ) * a))
  -- Proof comment: first rewrite the shell difference as the increment of the symmetric boundary
  -- cdf profile, then repackage that increment as the decrement of the complementary boundary tail.
  rw [shellDifference_eq_cdfSymmetricIncrementLocal (x := x) (a := a) ha hT n]
  dsimp [boundaryTail]
  ring

/-- Helper for Exercise 21.3.1: each lower-barrier shell difference is nonnegative because the
Gaussian boundary-tail profile decreases as the strip radius grows. -/
theorem shellDifference_nonnegLocal
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) (n : ℕ) :
    0 ≤ shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)) := by
  have hlu : (n : ℝ) * a ≤ ((n : ℝ) + 1) * a := by
    calc
      (n : ℝ) * a ≤ (n : ℝ) * a + a := by linarith
      _ = ((n : ℝ) + 1) * a := by ring
  have hPos :
      shiftedStripMass x a T n =
        ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T y := by
    -- Proof comment: the positive shell already has the standard interval-integral form.
    simpa using
      shiftedStripMass_eq_intervalIntegral
        (x := x) (a := a) ha (T := T) hT (n := (n : ℤ))
  have hNeg :
      shiftedStripMass x a T (-(n + 1 : ℤ)) =
        ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T (-y) := by
    -- Proof comment: rewrite the reflected shell by the interval-integral formula and transport
    -- it back to the positive interval using the change of variables `y ↦ -y`.
    have hNegIntegral :
        shiftedStripMass x a T (-(n + 1 : ℤ)) =
          ∫ y in (-(((n : ℝ) + 1) * a))..(-((n : ℝ) * a)), gaussianPDFReal x T y := by
      calc
        shiftedStripMass x a T (-(n + 1 : ℤ))
            = ∫ y in (((-(n + 1 : ℤ) : ℤ) : ℝ) * a)..((((-(n + 1 : ℤ) : ℤ) : ℝ) + 1) * a),
                gaussianPDFReal x T y := by
                  simpa using
                    shiftedStripMass_eq_intervalIntegral
                      (x := x) (a := a) ha (T := T) hT (n := (-(n + 1 : ℤ)))
        _ = ∫ y in (-(((n : ℝ) + 1) * a))..(-((n : ℝ) * a)), gaussianPDFReal x T y := by
              congr 1 <;> push_cast <;> ring
    calc
      shiftedStripMass x a T (-(n + 1 : ℤ))
          = ∫ y in (-(((n : ℝ) + 1) * a))..(-((n : ℝ) * a)), gaussianPDFReal x T y := by
            exact hNegIntegral
      _ = ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T (-y) := by
            symm
            simpa using
              (intervalIntegral.integral_comp_neg
                (a := ((n : ℝ) * a))
                (b := (((n : ℝ) + 1) * a))
                (fun y ↦ gaussianPDFReal x T y))
  have hMono :
      ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T (-y)
        ≤ ∫ y in ((n : ℝ) * a)..(((n : ℝ) + 1) * a), gaussianPDFReal x T y := by
    have hPosInt :
        IntervalIntegrable (fun y ↦ gaussianPDFReal x T y) volume ((n : ℝ) * a) (((n : ℝ) + 1) * a) := by
      simpa using (integrable_gaussianPDFReal x T).intervalIntegrable
    have hNegInt :
        IntervalIntegrable (fun y ↦ gaussianPDFReal x T (-y)) volume ((n : ℝ) * a) (((n : ℝ) + 1) * a) := by
      simpa using (integrable_gaussianPDFReal x T).comp_neg.intervalIntegrable
    -- Proof comment: on the positive half-line, the Gaussian density with mean `x ≥ 0` is larger
    -- at `y` than at its reflection `-y`, because `|y - x| ≤ |-y - x|`.
    exact
      intervalIntegral.integral_mono_on
        (μ := volume) hlu hNegInt hPosInt (by
          intro y hy
          have hy' : 0 ≤ y := le_trans (by positivity) hy.1
          have hsq : (y - x) ^ 2 ≤ (-y - x) ^ 2 := by
            nlinarith
          have hnum : -((-y - x) ^ 2) ≤ -(y - x) ^ 2 := by
            nlinarith [hsq]
          have hExpArg :
              -((-y - x) ^ 2) / (2 * (T : ℝ)) ≤ -(y - x) ^ 2 / (2 * (T : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
          have hExp :
              Real.exp (-((-y - x) ^ 2) / (2 * (T : ℝ))) ≤
                Real.exp (-(y - x) ^ 2 / (2 * (T : ℝ))) := by
            exact Real.exp_le_exp.mpr hExpArg
          rw [gaussianPDFReal, gaussianPDFReal]
          exact mul_le_mul_of_nonneg_left hExp (by positivity))
  -- Proof comment: substituting the two interval-integral descriptions reduces the shell
  -- comparison to the pointwise density comparison on the positive interval.
  rw [hPos, hNeg]
  exact sub_nonneg.mpr hMono

/-- Helper for Exercise 21.3.1: the boundary-tail profile used in the correction-prefix rewrite
vanishes at infinity because its positive cdf term tends to `1` and its reflected cdf term tends
to `0`. -/
theorem boundaryTail_tendsto_zeroLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} :
    Tendsto
      (fun n : ℕ ↦
        1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
          cdf (gaussianReal x T) (-((n : ℝ) * a)))
      atTop (𝓝 0) := by
  have hPos :
      Tendsto (fun n : ℕ ↦ cdf (gaussianReal x T) ((n : ℝ) * a)) atTop (𝓝 1) := by
    have hScaled :
        Tendsto (fun n : ℕ ↦ (n : ℝ) * a) atTop atTop := by
      simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
    exact (ProbabilityTheory.tendsto_cdf_atTop (μ := gaussianReal x T)).comp hScaled
  have hNeg :
      Tendsto (fun n : ℕ ↦ cdf (gaussianReal x T) (-((n : ℝ) * a))) atTop (𝓝 0) := by
    have hScaled :
        Tendsto (fun n : ℕ ↦ (n : ℝ) * a) atTop atTop := by
      simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop ha
    exact (ProbabilityTheory.tendsto_cdf_atBot (μ := gaussianReal x T)).comp
      (tendsto_neg_atTop_atBot.comp hScaled)
  -- Proof comment: combine the two one-sided cdf limits and simplify the resulting scalar limit.
  have hTail :
      Tendsto
        (fun n : ℕ ↦
          1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
            cdf (gaussianReal x T) (-((n : ℝ) * a)))
        atTop (𝓝 (1 - 1 - 0)) := by
    have hTail' :
        Tendsto
          (fun n : ℕ ↦
            1 - (cdf (gaussianReal x T) ((n : ℝ) * a) +
              cdf (gaussianReal x T) (-((n : ℝ) * a))))
          atTop (𝓝 (1 - (1 + 0))) := by
      exact tendsto_const_nhds.sub (hPos.add hNeg)
    convert hTail' using 1
    · ext n
      ring
    · ring
  simpa using hTail

/-- Helper for Exercise 21.3.1: every finite lower-barrier shell-difference prefix is the
one-sided lower-barrier survival mass minus the remaining boundary tail at the outer radius `N`.
-/
theorem shellDifferencePrefix_eq_lowerBarrierSurvival_sub_boundaryTailLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let shellDifference : ℕ → ℝ := fun n ↦
      shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    ∑ n ∈ Finset.range N, shellDifference n =
      μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} - boundaryTail N := by
  have ha : 0 ≤ a := by
    linarith
  let shellDifference : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  have hTelescoping :
      ∀ M : ℕ,
        ∑ n ∈ Finset.range M, shellDifference n = boundaryTail 0 - boundaryTail M := by
    intro M
    induction M with
    | zero =>
        -- Proof comment: the empty shell prefix leaves exactly the full boundary tail at radius
        -- `0`, so the telescoping difference is trivial.
        simp [shellDifference, boundaryTail]
    | succ M ih =>
        -- Proof comment: adjoining one more shell adds exactly the next boundary-tail decrement,
        -- so the partial sums telescope to `boundaryTail 0 - boundaryTail (M + 1)`.
        rw [Finset.sum_range_succ, ih]
        have hStep :
            shellDifference M = boundaryTail M - boundaryTail (M + 1) := by
          simpa [shellDifference, boundaryTail] using
            shellDifference_eq_boundaryTailDiffLocal
              (x := x) (a := a) ha (T := T) hT M
        rw [hStep]
        ring
  have hLower :
      μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} = boundaryTail 0 := by
    -- Proof comment: the zero-radius boundary tail is exactly the one-sided lower-barrier
    -- survival mass `1 - 2 * cdf (gaussianReal x T) 0`.
    rw [lowerBarrierSurvival_eq_terminalBoundaryCdfLocal
      (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT]
    simp [boundaryTail]
    ring
  -- Proof comment: combine the telescoping shell identity with the explicit zero-radius value of
  -- `boundaryTail`.
  rw [hLower]
  simpa [shellDifference, boundaryTail] using hTelescoping N

/-- Helper for Exercise 21.3.1: every finite correction prefix is the lower-barrier survival mass
minus the current boundary tail and minus the paired-shell interval prefix. -/
theorem upperLossCorrection_prefix_eq_lowerBarrierSurvival_sub_boundaryTail_sub_pairShellPrefixLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    ∑ n ∈ Finset.range N, correction n =
      (μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} - boundaryTail N) -
        ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let shellDifference : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  have hPrefix :
      ∑ n ∈ Finset.range N, correction n =
        ∑ n ∈ Finset.range N, shellDifference n -
          ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := by
    -- Proof comment: this is the already proved finite shell-algebra decomposition of the
    -- correction prefix.
    simpa [correction, shellDifference] using
      upperLossCorrection_prefix_eq_shellDifferencePrefix_sub_pairShellPrefixLocal
        (x := x) (a := a) (T := T) N
  have hShell :
      ∑ n ∈ Finset.range N, shellDifference n =
        μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} - boundaryTail N := by
    -- Proof comment: rewrite the lower-barrier shell prefix by the telescoping boundary-tail
    -- remainder proved just above.
    simpa [shellDifference, boundaryTail] using
      shellDifferencePrefix_eq_lowerBarrierSurvival_sub_boundaryTailLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT N
  -- Proof comment: substitute the exact lower-barrier shell prefix value into the finite
  -- correction-prefix decomposition.
  calc
    ∑ n ∈ Finset.range N, correction n
        = ∑ n ∈ Finset.range N, shellDifference n -
            ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := hPrefix
    _ = (μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} - boundaryTail N) -
          ∑ n ∈ Finset.range N, alternatingStripPairShell x a T n := by
            rw [hShell]

/-- Helper for Exercise 21.3.1: the finite odd/even correction prefixes are exactly the
corresponding alternating partial sums of the Gaussian boundary-tail decrements. -/
theorem upperLossCorrection_parityBoundsLocal
    {x a : ℝ} (ha : 0 ≤ a) {T : NNReal} (hT : 0 < T) :
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (2 * N + 1), correction n) =
        ∑ k ∈ Finset.range N, 2 * (boundaryTail (2 * k + 1) - boundaryTail (2 * k + 2)) ∧
      (∑ n ∈ Finset.range (2 * N + 2), correction n) =
        ∑ k ∈ Finset.range (N + 1), 2 * (boundaryTail (2 * k + 1) - boundaryTail (2 * k + 2)) := by
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let g : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else 2 * g n
  dsimp
  intro N
  constructor
  · -- Proof comment: the odd correction prefix already isolates the odd shell differences, and
    -- each such shell difference is exactly one boundary-tail decrement.
    have hOddPrefix :
        ∑ n ∈ Finset.range (2 * N + 1), correction n =
          ∑ k ∈ Finset.range N,
            2 * (shiftedStripMass x a T (2 * k + 1) -
              shiftedStripMass x a T (-(2 * k + 2 : ℤ))) := by
      convert upperLossCorrection_oddPrefix_eq_doubleOddShellSumLocal
          (x := x) (a := a) (T := T) N using 1
    rw [hOddPrefix]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hShell :
        2 * (shiftedStripMass x a T (2 * k + 1) -
            shiftedStripMass x a T (-(2 * k + 2 : ℤ))) =
          2 * (boundaryTail (2 * k + 1) - boundaryTail (2 * k + 2)) := by
      have hCore :=
        congrArg (fun z : ℝ => 2 * z) <|
          shellDifference_eq_cdfSymmetricIncrementLocal
            (x := x) (a := a) ha hT (2 * k + 1)
      dsimp [boundaryTail] at hCore ⊢
      ring_nf at hCore ⊢
      exact hCore
    exact hShell
  · -- Proof comment: the even correction prefix is the same alternating boundary-tail sum with
    -- one more odd shell term included.
    have hEvenPrefix :
        ∑ n ∈ Finset.range (2 * N + 2), correction n =
          ∑ k ∈ Finset.range (N + 1),
            2 * (shiftedStripMass x a T (2 * k + 1) -
              shiftedStripMass x a T (-(2 * k + 2 : ℤ))) := by
      convert upperLossCorrection_evenPrefix_eq_doubleOddShellSumLocal
          (x := x) (a := a) (T := T) N using 1
    rw [hEvenPrefix]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hShell :
        2 * (shiftedStripMass x a T (2 * k + 1) -
            shiftedStripMass x a T (-(2 * k + 2 : ℤ))) =
          2 * (boundaryTail (2 * k + 1) - boundaryTail (2 * k + 2)) := by
      have hCore :=
        congrArg (fun z : ℝ => 2 * z) <|
          shellDifference_eq_cdfSymmetricIncrementLocal
            (x := x) (a := a) ha hT (2 * k + 1)
      dsimp [boundaryTail] at hCore ⊢
      ring_nf at hCore ⊢
      exact hCore
    exact hShell

/-- Helper for Exercise 21.3.1: pointwise equality of two sample paths at one sample point forces
their singleton hitting times to agree at that sample. -/
theorem hittingAfter_eq_of_pointwise_eqLocal
    {u v : NNReal → Ω → ℝ} {S : Set ℝ} {n : NNReal} {ω : Ω}
    (hω : ∀ k : NNReal, u k ω = v k ω) :
    hittingAfter u S n ω = hittingAfter v S n ω := by
  by_cases hu : ∃ j : NNReal, n ≤ j ∧ u j ω ∈ S
  · have hv : ∃ j : NNReal, n ≤ j ∧ v j ω ∈ S := by
      rcases hu with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    have hset :
        {j : NNReal | n ≤ j ∧ u j ω ∈ S} =
          {j : NNReal | n ≤ j ∧ v j ω ∈ S} := by
      ext i
      constructor
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
    -- Proof comment: once the samplewise hit-index sets agree, the defining `sInf` formula for
    -- `hittingAfter` is identical on both sides.
    simp [hittingAfter_def, hu, hv, hset]
  · have hv : ¬ ∃ j : NNReal, n ≤ j ∧ v j ω ∈ S := by
      intro hv
      apply hu
      rcases hv with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    -- Proof comment: if neither path hits `S` after `n`, both hitting times are `⊤`.
    simp [hittingAfter_def, hu, hv]

/-- Helper for Exercise 21.3.1: the upper-hit event with a terminal cutoff is null measurable,
obtained by transferring measurability from the everywhere-continuous Brownian version. -/
theorem upperHitTerminalBelow_nullMeasurableLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {b y : ℝ} {T : NNReal} :
    NullMeasurableSet
      {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y} μ := by
  have upperHitBeforeTime_nullMeasurable_of_pos :
      ∀ {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {c : ℝ},
        0 < c → NullMeasurableSet {ω | hittingAfter B ({c} : Set ℝ) 0 ω ≤ T} μ := by
    intro B hB c hc
    let R : Set Ω := {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, c ≤ B s ω}
    let RApprox : Set Ω :=
      ⋂ n : ℕ,
        ⋃ q : {q : ℚ≥0 // (q : NNReal) ≤ T},
          {ω | c - c / (n + 2 : ℝ) < B (q : NNReal) ω}
    have hHitRunAe :
        {ω | hittingAfter B ({c} : Set ℝ) 0 ω ≤ T} =ᵐ[μ] R := by
      -- Proof comment: positive upper hits are already identified almost surely with the closed
      -- running-maximum event on `[0, T]`.
      simpa [R] using
        hitUpperBeforeTime_event_ae_eq_runningMaxClosedLocal
          (μ := μ) (B := B) hB (b := c) hc (T := T)
    have hRunApproxAe : R =ᵐ[μ] RApprox := by
      -- Proof comment: on continuous paths, the closed running-maximum event is the countable
      -- rational approximation through the strict lower levels `c - c / (n + 2)`.
      filter_upwards [hB.continuous_paths] with ω hω
      apply propext
      have hcont : Continuous (fun s : NNReal ↦ B s ω) := by
        simpa [HasAlmostSurelyContinuousPaths, processPath] using hω
      constructor
      · intro hMem
        have hLevels :
            ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧
              c - c / (n + 2 : ℝ) < B (q : NNReal) ω := by
          exact
            (continuous_exists_upperCrossing_iff_forall_nnrat_strictLowerLevels
              (f := fun s : NNReal ↦ B s ω) hcont (by simp [hB.zero]) (hb := hc) (T := T)).mp
              (by simpa [R] using hMem)
        refine Set.mem_iInter.mpr ?_
        intro n
        rcases hLevels n with ⟨q, hqT, hq⟩
        exact Set.mem_iUnion.mpr ⟨⟨q, hqT⟩, by simpa using hq⟩
      · intro hMem
        have hLevels :
            ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧
              c - c / (n + 2 : ℝ) < B (q : NNReal) ω := by
          intro n
          rcases Set.mem_iUnion.mp (Set.mem_iInter.mp hMem n) with ⟨q, hq⟩
          exact ⟨q, q.2, by simpa using hq⟩
        exact
          (continuous_exists_upperCrossing_iff_forall_nnrat_strictLowerLevels
            (f := fun s : NNReal ↦ B s ω) hcont (by simp [hB.zero]) (hb := hc) (T := T)).mpr
            hLevels
    have hRApproxMeas : MeasurableSet RApprox := by
      -- Proof comment: each rational row is a measurable terminal evaluation event, so the full
      -- approximation is a countable intersection of countable unions of measurable sets.
      refine MeasurableSet.iInter ?_
      intro n
      refine MeasurableSet.iUnion ?_
      intro q
      change MeasurableSet ((B (q : NNReal)) ⁻¹' Set.Ioi (c - c / (n + 2 : ℝ)))
      exact (hB.stronglyMeasurable (q : NNReal)).measurable measurableSet_Ioi
    have hEventAe :
        {ω | hittingAfter B ({c} : Set ℝ) 0 ω ≤ T} =ᵐ[μ] RApprox :=
      hHitRunAe.trans hRunApproxAe
    -- Proof comment: a measurable rational approximation is enough because the hit event agrees
    -- with it almost surely.
    exact hRApproxMeas.nullMeasurableSet.congr hEventAe.symm
  have hHitNull :
      NullMeasurableSet {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T} μ := by
    by_cases hb : 0 < b
    · -- Proof comment: positive barriers use the direct running-maximum approximation.
      exact upperHitBeforeTime_nullMeasurable_of_pos (B := W) hW hb
    · by_cases hzero : b = 0
      · have hHitEq :
            {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T} = Set.univ := by
          ext ω
          constructor
          · intro _hω
            simp
          · intro _hω
            have hHitZero :
                hittingAfter W ({b} : Set ℝ) 0 ω ≤ (0 : NNReal) := by
              exact
                hittingAfter_le_of_mem
                  (u := W) (s := ({b} : Set ℝ)) (n := (0 : NNReal)) (ω := ω)
                  le_rfl (by simp [hzero, hW.zero])
            exact hHitZero.trans (by simp)
        -- Proof comment: at level `0`, the Brownian path starts inside the singleton barrier, so
        -- the hit-by-time event is the whole space.
        rw [hHitEq]
        exact MeasurableSet.univ.nullMeasurableSet
      · have hb_le : b ≤ 0 := le_of_not_gt hb
        have hb_lt : b < 0 := lt_of_le_of_ne hb_le hzero
        have hbneg : 0 < -b := by
          simpa using neg_pos.mpr hb_lt
        let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
        have hBneg : IsBrownianMotion μ Bneg := neg_isBrownianMotion hW
        have hHitEq :
            {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T} =
              {ω | hittingAfter Bneg ({-b} : Set ℝ) 0 ω ≤ T} := by
          ext ω
          classical
          have hHit :
              hittingAfter Bneg ({-b} : Set ℝ) 0 ω =
                hittingAfter W ({b} : Set ℝ) 0 ω := by
            rw [hittingAfter_def, hittingAfter_def]
            simp only [Bneg, Set.mem_singleton_iff, zero_le, true_and]
            have hExists :
                (∃ j : NNReal, -W j ω = -b) ↔
                  ∃ j : NNReal, W j ω = b := by
              constructor
              · rintro ⟨j, hj⟩
                exact ⟨j, by linarith⟩
              · rintro ⟨j, hj⟩
                exact ⟨j, by linarith⟩
            have hSet :
                {i : NNReal | -W i ω = -b} =
                  {i : NNReal | W i ω = b} := by
              ext i
              constructor
              · intro hi
                have hEq : -W i ω = -b := by simpa using hi
                change W i ω = b
                linarith
              · intro hi
                have hEq : W i ω = b := by simpa using hi
                change -W i ω = -b
                linarith
            by_cases h : ∃ j : NNReal, -W j ω = -b
            · have h' : ∃ j : NNReal, W j ω = b := hExists.mp h
              rw [if_pos h, if_pos h']
              have hsInf :
                  (sInf {i : NNReal | -W i ω = -b} : NNReal) =
                    sInf {i : NNReal | W i ω = b} := by
                simpa using congrArg (fun s : Set NNReal ↦ (sInf s : NNReal)) hSet
              exact_mod_cast hsInf
            · have h' : ¬ ∃ j : NNReal, W j ω = b := by
                exact mt hExists.mpr h
              rw [if_neg h, if_neg h']
          simpa [hHit]
        have hNegNull :
            NullMeasurableSet {ω | hittingAfter Bneg ({-b} : Set ℝ) 0 ω ≤ T} μ :=
          upperHitBeforeTime_nullMeasurable_of_pos (B := Bneg) hBneg hbneg
        have hHitAe :
            {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T} =ᵐ[μ]
              {ω | hittingAfter Bneg ({-b} : Set ℝ) 0 ω ≤ T} := by
          rw [hHitEq]
        -- Proof comment: negative barriers are upper barriers for the negated Brownian path.
        exact hNegNull.congr hHitAe.symm
  have hTermNull :
      NullMeasurableSet {ω | W T ω ≤ y} μ := by
    exact ((hW.stronglyMeasurable T).measurable measurableSet_Iic).nullMeasurableSet
  -- Proof comment: the full event is the intersection of the null-measurable hit event with the
  -- measurable terminal cutoff.
  change NullMeasurableSet ({ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T} ∩ {ω | W T ω ≤ y}) μ
  exact hHitNull.inter hTermNull

-- Helper for Exercise 21.3.1: the future part of the time-inverted path, recentered at time `1`,
-- is the Brownian motion that drives the unit-slice reflection bridge.
-- Route correction: the stable Brownian owner is the exported unit-time reflected
-- slice theorem from `Theorem_21_19.UnitSlice`; the long theorem-local time-inversion
-- bridge below only needs that closed-tail identity.
/-- Helper for Exercise 21.3.1: the unit-time upper-hit slice with terminal cutoff `y < b`
matches the reflected standard-Gaussian closed tail beyond `2 * b - y`. -/
theorem unitHitUpperBeforeOne_terminalBelow_eq_reflectedClosedTailRealLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {b y : ℝ} (hb : 0 < b) (hyb : y < b) :
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ 1 ∧ W 1 ω ≤ y} =
      (gaussianReal 0 1).real (Set.Ici (2 * b - y)) := by
  have hEventEq :
      μ {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ 1 ∧ W 1 ω ≤ y} =
        μ {ω | 2 * b - y ≤ W 1 ω} := by
    exact theorem21_19CoreUnitSliceReflectedTail (hB := hW) (b := b) (y := y) hb hyb
  have hTailEq :
      μ {ω | 2 * b - y ≤ W 1 ω} = (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
    simpa using brownianTerminalClosedTail_eq_standardGaussianClosedTailLocal
      (hB := hW) (b := 2 * b - y)
  simpa [Measure.real_def] using congrArg ENNReal.toReal (hEventEq.trans hTailEq)

/-- Helper for Exercise 21.3.1: the upper-hit event with a terminal cutoff `y < b` has the same
real mass as the reflected Gaussian closed tail beyond `2 * b - y`. -/
theorem hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {b y : ℝ} (hb : 0 < b) {T : NNReal} (hT : 0 < T) (hyb : y < b) :
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y} =
      (gaussianReal 0 T).real (Set.Ici (2 * b - y)) := by
  let c : ℝ := Real.sqrt (T : ℝ)
  let Bscaled : NNReal → Ω → ℝ := brownianScaling W c
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.mpr hTreal
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hBscaled : IsBrownianMotion μ Bscaled := by
    dsimp [Bscaled, c]
    exact hW.scaling hc_ne
  have hbScaled : 0 < b / c := by
    exact div_pos hb hc
  have hyScaled : y / c < b / c := by
    exact (div_lt_div_iff_of_pos_right hc).2 hyb
  let E : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let R : Set Ω := (({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ W t ω} : Set Ω) ∩
    {ω | W T ω ≤ y})
  let Escaled : Set Ω :=
    {ω | hittingAfter Bscaled ({b / c} : Set ℝ) 0 ω ≤ 1 ∧ Bscaled 1 ω ≤ y / c}
  let Rscaled : Set Ω :=
    (({ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, b / c ≤ Bscaled t ω} : Set Ω) ∩
      {ω | Bscaled 1 ω ≤ y / c})
  have hEventReal :
      μ.real E = μ.real Escaled := by
    calc
      μ.real E = μ.real R := by
        exact
          MeasureTheory.measureReal_congr
            (hitUpperBeforeTime_terminalBelow_event_ae_eq_runningMaxClosedLocal
              (μ := μ) (B := W) hW hb (T := T))
      _ = μ.real Rscaled := by
        dsimp [R, Rscaled, Bscaled, c]
        exact
          congrArg (fun s : Set Ω ↦ μ.real s)
            (scaledClosedRunningMaximum_terminalBelow_event_eqLocal
              (B := W) (b := b) (y := y) hT)
      _ = μ.real Escaled := by
        exact
          MeasureTheory.measureReal_congr
            (hitUpperBeforeTime_terminalBelow_event_ae_eq_runningMaxClosedLocal
              (μ := μ) (B := Bscaled) hBscaled hbScaled (T := (1 : NNReal))).symm
  have hScaledTail :
      μ.real Escaled =
        (gaussianReal 0 1).real (Set.Ici (2 * (b / c) - y / c)) := by
    simpa [Escaled, Bscaled, c] using
      unitHitUpperBeforeOne_terminalBelow_eq_reflectedClosedTailRealLocal
        (μ := μ) (W := Bscaled) (hW := hBscaled) (b := b / c) (y := y / c) hbScaled hyScaled
  have hTailReal :
      μ.real {ω | 2 * (b / c) - y / c ≤ Bscaled 1 ω} =
        (gaussianReal 0 1).real (Set.Ici (2 * (b / c) - y / c)) := by
    -- Proof comment: the scaled Brownian motion at time `1` has the standard Gaussian law.
    simpa [Measure.real_def] using
      congrArg ENNReal.toReal
        (brownianTerminalClosedTail_eq_standardGaussianClosedTailLocal
          (μ := μ) (B := Bscaled) (hB := hBscaled) (b := 2 * (b / c) - y / c))
  have hScaledTerminalEq :
      {ω | 2 * (b / c) - y / c ≤ Bscaled 1 ω} = {ω | 2 * b - y ≤ W T ω} := by
    ext ω
    have hThreshold : 2 * (b / c) - y / c = (2 * b - y) / c := by
      field_simp [hc_ne]
    have hValue : Bscaled 1 ω = W T ω / c := by
      dsimp [Bscaled, c]
      rw [brownianScalingTime_sqrt]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    constructor
    · intro hω
      have hω' : (2 * b - y) / c ≤ W T ω / c := by
        simpa [hThreshold, hValue] using hω
      exact (div_le_div_iff_of_pos_right hc).mp hω'
    · intro hω
      have hω' : (2 * b - y) / c ≤ W T ω / c := by
        exact (div_le_div_iff_of_pos_right hc).mpr hω
      simpa [hThreshold, hValue] using hω'
  have hTerminalReal :
      μ.real {ω | 2 * b - y ≤ W T ω} = (gaussianReal 0 T).real (Set.Ici (2 * b - y)) := by
    -- Proof comment: the original Brownian terminal value at time `T` has law `N(0, T)`.
    simpa using
      shiftedBrownianTerminalReal_eq_gaussianReal
        (hW := hW) (x := 0) (T := T) hT
        (s := Set.Ici (2 * b - y)) measurableSet_Ici
  calc
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y} = μ.real E := by
      rfl
    _ = μ.real Escaled := hEventReal
    _ = (gaussianReal 0 1).real (Set.Ici (2 * (b / c) - y / c)) := hScaledTail
    _ = μ.real {ω | 2 * (b / c) - y / c ≤ Bscaled 1 ω} := by
          rw [hTailReal]
    _ = μ.real {ω | 2 * b - y ≤ W T ω} := by rw [hScaledTerminalEq]
    _ = (gaussianReal 0 T).real (Set.Ici (2 * b - y)) := hTerminalReal

/-- Helper for Exercise 21.3.1: the upper-hit slice with terminal window `Set.Ioc l u` is exactly
the reflected Gaussian strip `Set.Ioc (2 * b - u) (2 * b - l)`. -/
theorem upperBarrierHitBeforeTime_terminalIoc_eq_reflectedStripLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {b l u : ℝ} (hb : 0 < b) {T : NNReal} (hT : 0 < T) (hlu : l < u) (hub : u < b) :
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l u} =
      (gaussianReal 0 T).real (Set.Ioc (2 * b - u) (2 * b - l)) := by
  let Au : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ u}
  let Al : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ l}
  let gu : Set ℝ := Set.Ici (2 * b - u)
  let gl : Set ℝ := Set.Ici (2 * b - l)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hlb : l < b := lt_trans hlu hub
  have hAuNull : NullMeasurableSet Au μ := by
    -- Proof comment: the upper-hit event with the upper cutoff `u` is already packaged as a
    -- null-measurable terminal-slice event.
    simpa [Au] using
      upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := u) (T := T)
  have hAlNull : NullMeasurableSet Al μ := by
    -- Proof comment: the same null-measurability package applies to the lower cutoff `l`.
    simpa [Al] using
      upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := l) (T := T)
  have hAlSubsetAu : Al ⊆ Au := by
    intro ω hω
    exact ⟨hω.1, le_trans hω.2 hlu.le⟩
  have hAuInter : Au ∩ Al = Al := by
    -- Proof comment: the lower cutoff event is a subset of the upper cutoff event.
    ext ω
    constructor
    · intro hω
      exact hω.2
    · intro hω
      exact ⟨hAlSubsetAu hω, hω⟩
  have hAuDiff :
      Au \ Al = {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l u} := by
    -- Proof comment: subtracting the lower closed cutoff from the upper closed cutoff leaves
    -- exactly the half-open terminal window `Set.Ioc l u`.
    ext ω
    constructor
    · intro hω
      have hlt : l < W T ω := by
        by_contra hNotLt
        exact hω.2 ⟨hω.1.1, le_of_not_gt hNotLt⟩
      exact ⟨hω.1.1, ⟨hlt, hω.1.2⟩⟩
    · intro hω
      refine ⟨⟨hω.1, hω.2.2⟩, ?_⟩
      intro hAlω
      exact (not_lt_of_ge hAlω.2) hω.2.1
  have hAuFinite : μ Au ≠ ∞ := by
    exact measure_ne_top μ _
  have hAuDecomp :
      μ.real Al + μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l u} =
        μ.real Au := by
    -- Proof comment: `measureReal_inter_add_diff₀` turns the nested terminal cutoffs into an
    -- exact real-valued difference formula for the `Set.Ioc` slice.
    have hDecomp :=
      MeasureTheory.measureReal_inter_add_diff₀
        (μ := μ) (s := Au) (t := Al) hAlNull hAuFinite
    rw [hAuInter, hAuDiff] at hDecomp
    exact hDecomp
  have hClosedU :
      μ.real Au = (gaussianReal 0 T).real gu := by
    -- Proof comment: the upper cutoff `u` is exactly the restored reflected closed-tail owner.
    simpa [Au, gu] using
      hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := u) hb hT hub
  have hClosedL :
      μ.real Al = (gaussianReal 0 T).real gl := by
    -- Proof comment: the same closed-tail identity at cutoff `l` supplies the lower endpoint.
    simpa [Al, gl] using
      hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := l) hb hT hlb
  have hGlSubsetGu : gl ⊆ gu := by
    intro z hz
    have hThreshold : 2 * b - u ≤ 2 * b - l := by linarith
    exact le_trans hThreshold hz
  have hGaussInter : gu ∩ gl = gl := by
    -- Proof comment: on the Gaussian side, the larger threshold event `GL` is contained in `GU`.
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨hGlSubsetGu hz, hz⟩
  have hGaussDiff : gu \ gl = Set.Ico (2 * b - u) (2 * b - l) := by
    -- Proof comment: subtracting the two closed tails leaves the half-open reflected strip.
    ext z
    simp [gu, gl, Set.mem_Ici, Set.mem_Ico]
  have hGaussFinite : (gaussianReal 0 T) gu ≠ ∞ := by
    letI : IsProbabilityMeasure (gaussianReal 0 T) := inferInstance
    exact measure_ne_top (gaussianReal 0 T) _
  have hGaussDecomp :
      (gaussianReal 0 T).real gl + (gaussianReal 0 T).real (Set.Ico (2 * b - u) (2 * b - l)) =
        (gaussianReal 0 T).real gu := by
    -- Proof comment: the same finite-difference identity holds for the nested Gaussian tails.
    have hDecomp :=
      MeasureTheory.measureReal_inter_add_diff₀
        (μ := gaussianReal 0 T) (s := gu) (t := gl)
        measurableSet_Ici.nullMeasurableSet hGaussFinite
    rw [hGaussInter, hGaussDiff] at hDecomp
    exact hDecomp
  have hIcoEqIoc :
      (gaussianReal 0 T).real (Set.Ico (2 * b - u) (2 * b - l)) =
        (gaussianReal 0 T).real (Set.Ioc (2 * b - u) (2 * b - l)) := by
    -- Proof comment: positive-time Gaussian laws are atomless, so swapping which endpoint is
    -- included does not change the strip mass.
    have hLeftZero :
        (gaussianReal 0 T) {(2 * b - u)} = 0 := by
      exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton (2 * b - u)
    have hRightZero :
        (gaussianReal 0 T) {(2 * b - l)} = 0 := by
      exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton (2 * b - l)
    exact
      MeasureTheory.measureReal_congr
        (MeasureTheory.Ico_ae_eq_Ioc' (μ := gaussianReal 0 T) hLeftZero hRightZero)
  -- Proof comment: subtract the two reflected closed-tail formulas and normalize the remaining
  -- Gaussian half-open strip from `Ico` to the target `Ioc` spelling.
  calc
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l u}
        = μ.real Au - μ.real Al := by
            linarith [hAuDecomp]
    _ = (gaussianReal 0 T).real gu - (gaussianReal 0 T).real gl := by
          rw [hClosedU, hClosedL]
    _ = (gaussianReal 0 T).real (Set.Ico (2 * b - u) (2 * b - l)) := by
          linarith [hGaussDecomp]
    _ = (gaussianReal 0 T).real (Set.Ioc (2 * b - u) (2 * b - l)) := hIcoEqIoc

/-- Helper for Exercise 21.3.1: the boundary-touching upper-hit slice `Set.Ioc l b` is exactly
the reflected Gaussian strip `Set.Ioc b (2 * b - l)`. This is the missing `u = b` endpoint case
for the upper-barrier reflection API. -/
theorem upperBarrierHitBeforeTime_terminalIoc_top_eq_reflectedStripLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {b l : ℝ} (hb : 0 < b) {T : NNReal} (hT : 0 < T) (hlb : l < b) :
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l b} =
      (gaussianReal 0 T).real (Set.Ioc b (2 * b - l)) := by
  let hit : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T}
  let cutoffTop : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ b}
  let cutoffLow : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ l}
  let above : Set Ω := {ω | b < W T ω}
  let gaussTop : Set ℝ := Set.Ici b
  let gaussLow : Set ℝ := Set.Ici (2 * b - l)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hCutoffLowNull : NullMeasurableSet cutoffLow μ := by
    -- Proof comment: the lower terminal cutoff is already covered by the reflected closed-tail
    -- null-measurability package.
    simpa [cutoffLow] using
      upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := l) (T := T)
  have hAboveNull : NullMeasurableSet above μ := by
    -- Proof comment: the strict terminal tail is measurable by Brownian terminal measurability.
    exact ((hW.stronglyMeasurable T).measurable measurableSet_Ioi).nullMeasurableSet
  have hCutoffDiff :
      cutoffTop \ cutoffLow = {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l b} := by
    -- Proof comment: subtracting the lower cutoff from the top cutoff leaves exactly the
    -- half-open terminal window `Set.Ioc l b`.
    ext ω
    constructor
    · intro hω
      have hlt : l < W T ω := by
        by_contra hNotLt
        exact hω.2 ⟨hω.1.1, le_of_not_gt hNotLt⟩
      exact ⟨hω.1.1, ⟨hlt, hω.1.2⟩⟩
    · intro hω
      refine ⟨⟨hω.1, hω.2.2⟩, ?_⟩
      intro hLow
      exact (not_lt_of_ge hLow.2) hω.2.1
  have hHitInterAbove :
      hit ∩ above =ᵐ[μ] above := by
    have hHitAe :
        hit =ᵐ[μ] ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ W t ω} : Set Ω) := by
      simpa [hit] using
        hitUpperBeforeTime_event_ae_eq_runningMaxClosedLocal
          (μ := μ) (B := W) hW hb (T := T)
    filter_upwards [hHitAe] with ω hω
    apply propext
    constructor
    · intro hω'
      exact hω'.2
    · intro hω'
      have hRun : ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ W t ω := by
        refine ⟨T, ?_, hω'.le⟩
        exact ⟨by positivity, le_rfl⟩
      exact ⟨hω.mpr hRun, hω'⟩
  have hHitDiff : hit \ above = cutoffTop := by
    -- Proof comment: removing the strict terminal-above tail from the hit event leaves exactly
    -- the top cutoff `W T ≤ b`.
    ext ω
    simp [hit, cutoffTop, above, not_lt]
  have hHitTopDecomp :
      μ.real above + μ.real cutoffTop = μ.real hit := by
    have hDecomp :=
      MeasureTheory.measureReal_inter_add_diff₀
        (μ := μ) (s := hit) (t := above) hAboveNull (measure_ne_top μ _)
    have hInter :
        μ.real (hit ∩ above) = μ.real above := by
      exact MeasureTheory.measureReal_congr hHitInterAbove
    rw [hHitDiff] at hDecomp
    linarith
  have hHitCompl : hitᶜ = {ω | T < hittingAfter W ({b} : Set ℝ) 0 ω} := by
    -- Proof comment: the complement of the hit-by-time event is exactly the strict survival event.
    ext ω
    simp [hit, not_le]
  have hHitNull : NullMeasurableSet hit μ := by
    have hHitEq : hit = cutoffTop ∪ above := by
      -- Proof comment: every hit path either ends above the barrier or ends in the terminal
      -- cutoff `≤ b`.
      ext ω
      simp [hit, cutoffTop, above, or_and_right, le_or_lt]
    rw [hHitEq]
    exact
      (upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := b) (T := T)).union hAboveNull
  have hGaussTailIoi :
      (gaussianReal 0 T).real (Set.Ioi b) = 1 - cdf (gaussianReal 0 T) b := by
    letI : IsProbabilityMeasure (gaussianReal 0 T) := inferInstance
    rw [← ProbabilityTheory.cdf_eq_real (μ := gaussianReal 0 T) b]
    simpa using
      (MeasureTheory.measureReal_compl
        (μ := gaussianReal 0 T) (s := Set.Iic b) measurableSet_Iic)
  have hGaussTail :
      (gaussianReal 0 T).real gaussTop = 1 - cdf (gaussianReal 0 T) b := by
    have hSingle : (gaussianReal 0 T) {b} = 0 := by
      exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton b
    calc
      (gaussianReal 0 T).real gaussTop = (gaussianReal 0 T).real (Set.Ioi b) := by
          exact
            MeasureTheory.measureReal_congr
              (MeasureTheory.Ioi_ae_eq_Ici' (μ := gaussianReal 0 T) hSingle).symm
      _ = 1 - cdf (gaussianReal 0 T) b := hGaussTailIoi
  have hAboveReal :
      μ.real above = (gaussianReal 0 T).real gaussTop := by
    calc
      μ.real above = (gaussianReal 0 T).real (Set.Ioi b) := by
          simpa [above] using
            shiftedBrownianTerminalReal_eq_gaussianReal
              (hW := hW) (x := 0) (T := T) hT measurableSet_Ioi
      _ = (gaussianReal 0 T).real gaussTop := by
          have hSingle : (gaussianReal 0 T) {b} = 0 := by
            exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton b
          exact
            MeasureTheory.measureReal_congr
              (MeasureTheory.Ioi_ae_eq_Ici' (μ := gaussianReal 0 T) hSingle)
  have hHitReal :
      μ.real hit = 2 * (gaussianReal 0 T).real gaussTop := by
    letI : IsBrownianMotionStartedAt μ W 0 := inferInstance
    calc
      μ.real hit = 1 - μ.real hitᶜ := by
          simpa using (MeasureTheory.measureReal_compl₀ (μ := μ) (s := hit) hHitNull)
      _ = 1 - μ.real {ω | T < hittingAfter W ({b} : Set ℝ) 0 ω} := by
            rw [hHitCompl]
      _ = 1 - (2 * cdf (gaussianReal 0 T) b - 1) := by
            rw [startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf inferInstance hb hT]
      _ = 2 * (1 - cdf (gaussianReal 0 T) b) := by ring
      _ = 2 * (gaussianReal 0 T).real gaussTop := by rw [hGaussTail]
  have hCutoffTop :
      μ.real cutoffTop = (gaussianReal 0 T).real gaussTop := by
    -- Proof comment: split the hit event into the terminal-above tail and the cutoff slice.
    linarith [hHitTopDecomp, hAboveReal, hHitReal]
  have hCutoffLow :
      μ.real cutoffLow = (gaussianReal 0 T).real gaussLow := by
    -- Proof comment: below the barrier, the reflected closed-tail formula applies directly.
    simpa [cutoffLow, gaussLow] using
      hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal
        (μ := μ) (W := W) (hW := hW) (b := b) (y := l) hb hT hlb
  have hGaussSubset : gaussLow ⊆ gaussTop := by
    intro z hz
    have hThreshold : b ≤ 2 * b - l := by linarith
    exact le_trans hThreshold hz
  have hGaussInter : gaussTop ∩ gaussLow = gaussLow := by
    -- Proof comment: the larger reflected threshold `2 * b - l` lies inside the tail above `b`.
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨hGaussSubset hz, hz⟩
  have hGaussDiff : gaussTop \ gaussLow = Set.Ico b (2 * b - l) := by
    -- Proof comment: subtracting the two closed tails leaves the half-open reflected strip.
    ext z
    simp [gaussTop, gaussLow, Set.mem_Ici, Set.mem_Ico]
  have hGaussDecomp :
      (gaussianReal 0 T).real gaussLow +
          (gaussianReal 0 T).real (Set.Ico b (2 * b - l)) =
        (gaussianReal 0 T).real gaussTop := by
    have hDecomp :=
      MeasureTheory.measureReal_inter_add_diff₀
        (μ := gaussianReal 0 T) (s := gaussTop) (t := gaussLow)
        measurableSet_Ici.nullMeasurableSet (measure_ne_top (gaussianReal 0 T) _)
    rw [hGaussInter, hGaussDiff] at hDecomp
    exact hDecomp
  have hIcoEqIoc :
      (gaussianReal 0 T).real (Set.Ico b (2 * b - l)) =
        (gaussianReal 0 T).real (Set.Ioc b (2 * b - l)) := by
    have hLeftZero :
        (gaussianReal 0 T) {b} = 0 := by
      exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton b
    have hRightZero :
        (gaussianReal 0 T) {2 * b - l} = 0 := by
      exact
        (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton (2 * b - l)
    exact
      MeasureTheory.measureReal_congr
        (MeasureTheory.Ico_ae_eq_Ioc' (μ := gaussianReal 0 T) hLeftZero hRightZero)
  -- Proof comment: subtract the reflected lower cutoff from the top cutoff and normalize the
  -- resulting Gaussian half-open strip.
  calc
    μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l b}
        = μ.real cutoffTop - μ.real cutoffLow := by
            linarith [show μ.real cutoffLow +
              μ.real {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l b} =
              μ.real cutoffTop from by
                have hDecomp :=
                  MeasureTheory.measureReal_inter_add_diff₀
                    (μ := μ) (s := cutoffTop) (t := cutoffLow) hCutoffLowNull (measure_ne_top μ _)
                rw [hCutoffDiff] at hDecomp
                exact hDecomp]
    _ = (gaussianReal 0 T).real gaussTop - (gaussianReal 0 T).real gaussLow := by
          rw [hCutoffTop, hCutoffLow]
    _ = (gaussianReal 0 T).real (Set.Ico b (2 * b - l)) := by
          linarith [hGaussDecomp]
    _ = (gaussianReal 0 T).real (Set.Ioc b (2 * b - l)) := hIcoEqIoc

/-- Helper for Exercise 21.3.1: the barrier-touching base upper-hit strip is the first shifted
Gaussian strip mass, supplying the `n = 1` shell that the arithmetic-strip theorem cannot cover
because its upper endpoint coincides with the barrier. -/
theorem upperBarrierHitBeforeTime_terminalBaseStrip_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    μ.real
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc (-x) (a - x)} =
      shiftedStripMass x a T (1 : ℤ) := by
  calc
    μ.real
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc (-x) (a - x)}
        = (gaussianReal 0 T).real (Set.Ioc (a - x) (2 * (a - x) - (-x))) := by
            -- Proof comment: this is exactly the boundary-touching reflected strip handled by the
            -- new `u = b` adapter.
            exact
              upperBarrierHitBeforeTime_terminalIoc_top_eq_reflectedStripLocal
                (μ := μ) (W := W) (hW := hW) (b := a - x) (l := -x)
                (hb := by linarith) (hT := hT) (hlb := by linarith)
    _ = (gaussianReal 0 T).real (Set.Ioc (a - x) ((2 : ℝ) * a - x)) := by
          congr 1
          ring
    _ = μ.real {ω | x + W T ω ∈ Set.Ioc a (2 * a)} := by
          symm
          congr 1
          ext ω
          constructor <;> intro hω <;> constructor <;> linarith [hω.1, hω.2]
    _ = shiftedStripMass x a T (1 : ℤ) := by
          symm
          simpa using
            shiftedStripMass_eq_terminalIocReal
              (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) hT (n := (1 : ℤ))

/-- Helper for Exercise 21.3.1: reflecting the upper-hit terminal strip
`Set.Ioc (((1 : ℝ) - n) * a - x) (((2 : ℝ) - n) * a - x)` below the barrier `a - x`
produces exactly the shifted Gaussian strip mass `shiftedStripMass x a T n`. -/
theorem upperBarrierHitBeforeTime_terminalArithmeticStrip_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    {n : ℕ} (hn : 2 ≤ n) :
    μ.real
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc ((((1 : ℝ) - n) * a) - x) ((((2 : ℝ) - n) * a) - x)} =
      shiftedStripMass x a T (n : ℤ) := by
  have ha : 0 < a := by
    linarith
  have hlu : (((1 : ℝ) - n) * a) - x < (((2 : ℝ) - n) * a) - x := by
    nlinarith
  have hub : (((2 : ℝ) - n) * a) - x < a - x := by
    have hna : (((2 : ℝ) - n) * a) ≤ 0 := by
      nlinarith [ha.le, hn]
    linarith
  calc
    μ.real
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc ((((1 : ℝ) - n) * a) - x) ((((2 : ℝ) - n) * a) - x)}
        =
          (gaussianReal 0 T).real
            (Set.Ioc
              (2 * (a - x) - ((((2 : ℝ) - n) * a) - x))
              (2 * (a - x) - ((((1 : ℝ) - n) * a) - x))) := by
            -- Proof comment: specialize the reflected-strip owner theorem at the arithmetic
            -- window whose reflection lands on the `n`th shifted strip.
            exact
              upperBarrierHitBeforeTime_terminalIoc_eq_reflectedStripLocal
                (μ := μ) (W := W) (hW := hW) (b := a - x)
                (l := (((1 : ℝ) - n) * a) - x)
                (u := (((2 : ℝ) - n) * a) - x)
                (hb := by linarith) (hT := hT) hlu hub
    _ =
        (gaussianReal 0 T).real
          (Set.Ioc (((n : ℝ) * a) - x) ((((n : ℝ) + 1) * a) - x)) := by
            -- Proof comment: simplify the reflected endpoints to the standard shifted-strip
            -- coordinates `n * a - x` and `(n + 1) * a - x`.
            congr 1 <;> ring
    _ =
        μ.real
          {ω | W T ω ∈ Set.Ioc (((n : ℝ) * a) - x) ((((n : ℝ) + 1) * a) - x)} := by
            -- Proof comment: the centered Brownian terminal law at time `T` is `gaussianReal 0 T`.
            symm
            exact
              shiftedBrownianTerminalReal_eq_gaussianReal
                (hW := hW) (x := 0) (T := T) hT measurableSet_Ioc
    _ =
        μ.real
          {ω | x + W T ω ∈ Set.Ioc ((n : ℝ) * a) (((n : ℝ) + 1) * a)} := by
            -- Proof comment: translating the terminal value by `x` rewrites the reflected strip
            -- back to the textbook strip for `shiftedStripMass`.
            congr 1
            ext ω
            constructor
            · intro hω
              constructor <;> linarith [hω.1, hω.2]
            · intro hω
              constructor <;> linarith [hω.1, hω.2]
    _ = shiftedStripMass x a T (n : ℤ) := by
          -- Proof comment: this is exactly the half-open terminal-event spelling of the shifted
          -- strip mass.
          symm
          exact
            shiftedStripMass_eq_terminalIocReal
              (hW := hW) (x := x) (a := a) (T := T) hT (n := (n : ℤ))

/-- Helper for Exercise 21.3.1: every reflected upper-hit strip with index `n ≥ 1` has the
uniform arithmetic spelling `Set.Ioc (((1 : ℝ) - n) * a - x) (((2 : ℝ) - n) * a - x)`, covering
the boundary-touching base case `n = 1` and the later arithmetic strips `n ≥ 2` in one API. -/
theorem upperBarrierHitBeforeTime_terminalStrip_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    {n : ℕ} (hn : 1 ≤ n) :
    μ.real
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc ((((1 : ℝ) - n) * a) - x) ((((2 : ℝ) - n) * a) - x)} =
      shiftedStripMass x a T (n : ℤ) := by
  cases' n with n
  · cases Nat.not_succ_le_zero 0 hn
  · cases' n with n
    · -- Proof comment: the index `n = 1` is the boundary-touching base strip.
      simpa using
        upperBarrierHitBeforeTime_terminalBaseStrip_eq_shiftedStripMassLocal
          (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
    · -- Proof comment: every later index `n + 2` lies strictly below the barrier, so the
      -- arithmetic reflected-strip theorem applies directly.
      have hn_two : 2 ≤ n.succ.succ := by omega
      simpa using
        upperBarrierHitBeforeTime_terminalArithmeticStrip_eq_shiftedStripMassLocal
          (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
          (n := n.succ.succ) hn_two

/-- Helper for Exercise 21.3.1: subtracting two nested upper-hit terminal cutoffs leaves the
half-open terminal strip `Set.Ioc l u`. -/
theorem upperHitCutoffDiff_eq_terminalIocLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} {l u : ℝ} (hlu : l < u) :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    cutoff u \ cutoff l =
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ∈ Set.Ioc l u} := by
  dsimp
  -- Proof comment: the lower cutoff event is nested in the upper one, so their difference keeps
  -- exactly the paths whose terminal value lands in the half-open strip `Set.Ioc l u`.
  ext ω
  constructor
  · intro hω
    have hlt : l < W T ω := by
      by_contra hNotLt
      exact hω.2 ⟨hω.1.1, le_of_not_gt hNotLt⟩
    exact ⟨hω.1.1, ⟨hlt, hω.1.2⟩⟩
  · intro hω
    refine ⟨⟨hω.1, hω.2.2⟩, ?_⟩
    intro hLow
    exact (not_lt_of_ge hLow.2) hω.2.1

/-- Helper for Exercise 21.3.1: the difference of two consecutive upper-hit cutoffs is exactly
the shifted Gaussian strip indexed by `n ≥ 1`. This packages the cutoff-to-strip bridge needed
for the odd correction-prefix decomposition into one reusable rewrite lemma. -/
theorem upperHitCutoffDiff_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    {n : ℕ} (hn : 1 ≤ n) :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    μ.real (cutoff ((((2 : ℝ) - n) * a) - x) \ cutoff ((((1 : ℝ) - n) * a) - x)) =
      shiftedStripMass x a T (n : ℤ) := by
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  have hlu : (((1 : ℝ) - n) * a) - x < (((2 : ℝ) - n) * a) - x := by
    have ha : 0 < a := by linarith
    nlinarith
  have hSet :
      cutoff ((((2 : ℝ) - n) * a) - x) \ cutoff ((((1 : ℝ) - n) * a) - x) =
        {ω |
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
            W T ω ∈ Set.Ioc ((((1 : ℝ) - n) * a) - x) ((((2 : ℝ) - n) * a) - x)} := by
    simpa [cutoff] using
      (upperHitCutoffDiff_eq_terminalIocLocal
        (W := W) (x := x) (a := a) (T := T)
        (l := (((1 : ℝ) - n) * a) - x) (u := (((2 : ℝ) - n) * a) - x) hlu)
  -- Proof comment: rewrite the cutoff difference to its `Set.Ioc` window and then use the
  -- unified reflected-strip mass formula above.
  calc
    μ.real (cutoff ((((2 : ℝ) - n) * a) - x) \ cutoff ((((1 : ℝ) - n) * a) - x))
        =
          μ.real
            {ω |
              hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
                W T ω ∈ Set.Ioc ((((1 : ℝ) - n) * a) - x) ((((2 : ℝ) - n) * a) - x)} := by
            rw [hSet]
    _ = shiftedStripMass x a T (n : ℤ) := by
          exact
            upperBarrierHitBeforeTime_terminalStrip_eq_shiftedStripMassLocal
              (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT hn

-- Route correction: the real Brownian frontier is the paired shell `HasSum` for interval
-- survival. Once that owner theorem is available, the current correction series follows by the
-- already proved finite prefix identity and the boundary-tail limit.
/-- Helper for Exercise 21.3.1: the correction sequence already has a clean owner `HasSum` onto
its odd shell-difference subseries, so the remaining Brownian work is only to identify that scalar
with the `upperLoss` event. -/
theorem upperLossCorrectionSeries_hasSum_oddShellDifferenceLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    HasSum correction (∑' k : ℕ, oddShell k) := by
  let shellDifference : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * shellDifference n
  let oddShell : ℕ → ℝ := fun k ↦ 2 * shellDifference (2 * k + 1)
  have hShellSummable : Summable shellDifference := by
    -- Proof comment: the one-sided lower-barrier owner theorem already gives summability of the
    -- full shell-difference series.
    simpa [shellDifference] using
      (lowerBarrierStripPairShell_hasSumLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT).summable
  have hOddShellSummableCore :
      Summable (fun k : ℕ ↦ shellDifference (2 * k + 1)) := by
    -- Proof comment: the odd shells are just the injective subsequence `n ↦ 2 * n + 1` of the
    -- summable shell-difference series.
    exact hShellSummable.comp_injective (fun m n hmn ↦ by omega)
  have hOddShellSummable : Summable oddShell := by
    -- Proof comment: `oddShell` is exactly twice that odd subsequence.
    convert hOddShellSummableCore.mul_left 2 using 1
    ext k
    simp [oddShell, shellDifference]
  have hCorrectionNonneg : ∀ n : ℕ, 0 ≤ correction n := by
    intro n
    by_cases hEven : Even n
    · -- Proof comment: even correction terms vanish by definition.
      simp [correction, hEven]
    · -- Proof comment: odd correction terms are twice a nonnegative shell difference.
      have hShellNonneg : 0 ≤ shellDifference n := by
        dsimp [shellDifference]
        exact
          shellDifference_nonnegLocal
            (x := x) (a := a) hx.le (by linarith) (T := T) hT n
      simp [correction, hEven, hShellNonneg]
  have hOddHasSum : HasSum oddShell (∑' k : ℕ, oddShell k) := hOddShellSummable.hasSum
  have hOddTendsto :
      Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, oddShell i) atTop
        (𝓝 (∑' k : ℕ, oddShell k)) := hOddHasSum.tendsto_sum_nat
  rw [hasSum_iff_tendsto_nat_of_nonneg hCorrectionNonneg]
  rw [Metric.tendsto_atTop] at hOddTendsto ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hOddTendsto ε hε
  refine ⟨2 * N + 2, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hkpos : 0 < k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    have hNm : N ≤ m + 1 := by omega
    have hPrefix :
        ∑ i ∈ Finset.range (2 * (m + 1)), correction i =
          ∑ j ∈ Finset.range (m + 1), oddShell j := by
      -- Proof comment: even correction prefixes coincide with the odd-shell prefix of the same
      -- shell length.
      simpa [correction, oddShell, shellDifference] using
        oddShellPrefix_succ_eq_upperLossCorrectionEvenPrefixLocal
          (x := x) (a := a) (T := T) m
    simpa [hPrefix] using hN (m + 1) hNm
  · have hNk : N ≤ k := by omega
    have hPrefix :
        ∑ i ∈ Finset.range (2 * k + 1), correction i =
          ∑ j ∈ Finset.range k, oddShell j := by
      -- Proof comment: odd correction prefixes are exactly the matching odd-shell prefixes.
      simpa [correction, oddShell, shellDifference] using
        oddShellPrefix_eq_upperLossCorrectionOddPrefixLocal
          (x := x) (a := a) (T := T) k
    simpa [hPrefix] using hN k hNk

/-- Helper for Exercise 21.3.1: the odd reflected-shell prefix is exactly the odd correction
prefix through `2 * N`. This isolates the finite reindexing needed in the remaining `upperLoss`
limit theorem. -/
theorem oddShellPrefix_eq_upperLossCorrectionOddPrefixLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    ∑ k ∈ Finset.range N, oddShell k =
      ∑ n ∈ Finset.range (2 * N + 1), correction n := by
  -- Proof comment: the existing odd-prefix normalization theorem already has exactly this content;
  -- only the reflected index `-(2 * k + 2)` needs to be rewritten to the same normal form.
  convert
    (upperLossCorrection_oddPrefix_eq_doubleOddShellSumLocal
      (x := x) (a := a) (T := T) N).symm using 1

/-- Helper for Exercise 21.3.1: adding the next odd shell turns the odd-shell prefix into the
even correction prefix through `2 * N + 1`. This is the companion reindexing for parity-based
prefix arguments around `upperLoss`. -/
theorem oddShellPrefix_succ_eq_upperLossCorrectionEvenPrefixLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    ∑ k ∈ Finset.range (N + 1), oddShell k =
      ∑ n ∈ Finset.range (2 * N + 2), correction n := by
  -- Proof comment: the companion even-prefix normalization theorem matches this statement after a
  -- direct symmetry flip, after the same reflected-index normalization as above.
  convert
    (upperLossCorrection_evenPrefix_eq_doubleOddShellSumLocal
      (x := x) (a := a) (T := T) N).symm using 1

/-- Helper for Exercise 21.3.1: once the paired-shell Brownian owner theorem is known, the
correction series lands on `upperLoss` by subtracting the paired shell sum from the lower-barrier
shell sum. -/
theorem upperLossCorrectionSeries_hasSum_of_pairShellIntervalLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    (hPair :
      HasSum (alternatingStripPairShell x a T)
        (μ.real {ω | T < brownianIntervalExitTime W x a ω})) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    HasSum correction (μ.real upperLoss) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let shellDifference : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hLower : HasSum shellDifference lower := by
    -- Proof comment: the one-sided lower-barrier shell series is already proved earlier in the
    -- file, so only the interval-survival shell owner needs to be supplied externally here.
    simpa [shellDifference, lower] using
      lowerBarrierStripPairShell_hasSumLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
  have hCorrection :
      HasSum correction (lower - interval) := by
    have hDiff :
        HasSum (fun n : ℕ ↦ shellDifference n - alternatingStripPairShell x a T n)
          (lower - interval) := by
      -- Proof comment: subtract the paired-shell interval series from the lower-barrier shell
      -- series termwise; the scalar target becomes the corresponding difference of masses.
      exact hLower.sub (by simpa [interval] using hPair)
    have hSeq :
        (fun n : ℕ ↦ shellDifference n - alternatingStripPairShell x a T n) = correction := by
      -- Proof comment: each correction coefficient is exactly one shell difference minus the
      -- paired-shell coefficient at the same index.
      funext n
      have hTerm :=
        upperLossCorrection_eq_shellDifference_sub_pairShellLocal
          (x := x) (a := a) (T := T) n
      dsimp [shellDifference, correction] at hTerm ⊢
      linarith
    rw [← hSeq] at hDiff
    exact hDiff
  have hGap : lower - interval = μ.real upperLoss := by
    -- Proof comment: the event-theoretic gap between lower-barrier survival and interval survival
    -- is exactly the `upperLoss` event introduced for this exercise.
    simpa [lower, interval, upperLoss] using
      intervalSurvivalGap_eq_upperLossRealLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T)
  -- Proof comment: rewrite the scalar target of the correction-series `HasSum` with the explicit
  -- lower-minus-interval gap identity.
  simpa [correction, upperLoss, hGap] using hCorrection

/-- Helper for Exercise 21.3.1: the direct Brownian owner still missing after the shell-difference
transport is the odd-shell prefix formula for `upperLoss`, with an explicit remainder tending to
`0`. -/
theorem oddShell_le_twoOuterStripsLocal
    {x a : ℝ} {T : NNReal} (N : ℕ) :
    2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
      2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
        shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  have hNegNonneg :
      0 ≤ shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
    exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (n := (-(2 * N + 2 : ℤ)))
  -- Proof comment: replacing the reflected-strip subtraction by addition only enlarges the
  -- coefficient, because every Gaussian strip mass is nonnegative.
  linarith

/-- Helper for Exercise 21.3.1: the interval paired-shell remainder is exactly the boundary tail
minus the transported odd correction-prefix error for `upperLoss`. -/
theorem upperLossCorrectionOddPrefix_error_eq_boundaryTail_sub_intervalRemainderLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) =
        boundaryTail (2 * N + 1) -
          (interval - ∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hGap : lower - interval = μ.real upperLoss := by
    -- Proof comment: `upperLoss` is exactly the event-level gap between lower-barrier survival and
    -- interval survival.
    simpa [lower, interval, upperLoss] using
      intervalSurvivalGap_eq_upperLossRealLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T)
  intro N
  have hPrefix :
      ∑ n ∈ Finset.range (2 * N + 1), correction n =
        (lower - boundaryTail (2 * N + 1)) -
          ∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n := by
    -- Proof comment: normalize the odd correction prefix through the finite
    -- lower-survival minus boundary-tail minus paired-prefix identity.
    simpa [correction, boundaryTail, lower] using
      upperLossCorrection_prefix_eq_lowerBarrierSurvival_sub_boundaryTail_sub_pairShellPrefixLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT (2 * N + 1)
  -- Proof comment: substituting the finite correction-prefix formula rewrites the interval
  -- paired-shell remainder to the transported `upperLoss` correction error.
  linarith [hGap, hPrefix]

/-- Helper for Exercise 21.3.1: the odd correction-prefix window for `upperLoss` is exactly the
transport of the paired-shell boundary window for interval survival through the boundary-tail
error identity. -/
theorem upperLossCorrectionOddPrefix_window_iff_intervalWindowLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    (0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
        μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ)))) ↔
      (boundaryTail (2 * N + 1) -
            2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
              shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
          interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ∧
        interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ≤
          boundaryTail (2 * N + 1)) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hError :=
    upperLossCorrectionOddPrefix_error_eq_boundaryTail_sub_intervalRemainderLocal
      (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
      (T := T) (hT := hT) N
  constructor
  · intro h
    constructor
    · -- Proof comment: the lower interval window bound is just the transported upper-loss
      -- upper-error bound through the exact boundary-tail identity.
      linarith [hError, h.2]
    · -- Proof comment: the upper interval window bound is the same transport of the
      -- nonnegativity half of the upper-loss error.
      linarith [hError, h.1]
  · intro h
    constructor
    · -- Proof comment: moving the interval window back through the same identity recovers
      -- nonnegativity of the upper-loss odd-prefix error.
      linarith [hError, h.2]
    · -- Proof comment: the interval lower window bound transports back to the desired two-strip
      -- upper bound for the upper-loss error.
      linarith [hError, h.1]

/-- Helper for Exercise 21.3.1: the next uncovered upper-hit cutoff shell in the odd-prefix
remainder is already in the exact `shiftedStripMass` normal form needed by the owner window
estimate. -/
theorem nextUpperHitShell_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
      cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) =
      shiftedStripMass x a T (2 * N + 1 : ℤ) := by
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  have hIndex : 1 ≤ 2 * N + 1 := by
    omega
  -- Proof comment: this is just the generic cutoff-to-strip bridge specialized to the odd shell
  -- index `2 * N + 1`.
  simpa [cutoff] using
    upperHitCutoffDiff_eq_shiftedStripMassLocal
      (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
      (n := 2 * N + 1) hIndex

/-- Helper for Exercise 21.3.1: the reflected negative companion of the next odd shell is already
written in the terminal `Set.Ioc` form used by the remaining upper-loss remainder geometry. -/
theorem nextReflectedNegativeShell_eq_shiftedStripMassLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} (hT : 0 < T) (N : ℕ) :
    μ.real
        {ω |
          x + W T ω ∈
            Set.Ioc (((-1 : ℝ) - (2 * N + 1 : ℝ)) * a) (-(((2 * N + 1 : ℕ) : ℝ) * a))} =
      shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
  -- Proof comment: specialize the reflected negative-strip transport to the odd shell index
  -- `2 * N + 1`; this removes the last endpoint-arithmetic rewrite from the core theorem.
  simpa using
    (reflectedShiftedStripMass_eq_terminalIocReal
      (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) hT
      (n := 2 * N + 1)).symm

/-- Helper for Exercise 21.3.1: each odd reflected shell is exactly the difference between the
matching upper-hit cutoff slice and its reflected negative companion. This packages the one-shell
normal form needed before any finite remainder algebra. -/
theorem oddShell_eq_upperHitSlice_sub_reflectedNegativeLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let reflectedNegative : Set Ω :=
      {ω |
        x + W T ω ∈
          Set.Ioc (((-1 : ℝ) - (2 * N + 1 : ℝ)) * a) (-(((2 * N + 1 : ℕ) : ℝ) * a))}
    μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
        cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) -
        μ.real reflectedNegative =
      shiftedStripMass x a T (2 * N + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let reflectedNegative : Set Ω :=
    {ω |
      x + W T ω ∈
        Set.Ioc (((-1 : ℝ) - (2 * N + 1 : ℝ)) * a) (-(((2 * N + 1 : ℕ) : ℝ) * a))}
  have hPos :
      μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
          cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) =
        shiftedStripMass x a T (2 * N + 1 : ℤ) := by
    -- Proof comment: the positive odd branch is already the cutoff-to-strip bridge for the
    -- next uncovered upper-hit shell.
    simpa [cutoff] using
      nextUpperHitShell_eq_shiftedStripMassLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
        (T := T) (hT := hT) N
  have hNeg :
      μ.real reflectedNegative =
        shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
    -- Proof comment: the reflected negative branch is already normalized to the matching
    -- terminal `Set.Ioc` strip by the companion reflection lemma.
    simpa [reflectedNegative] using
      nextReflectedNegativeShell_eq_shiftedStripMassLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) (hT := hT) N
  -- Proof comment: once both branches are in `shiftedStripMass` normal form, the shell
  -- coefficient is just their scalar difference.
  linarith

/-- Helper for Exercise 21.3.1: the one-shell upper-hit slice always dominates its reflected
negative companion, so the odd shell coefficient is nonnegative already at the event-level normal
form used by the remaining owner theorem. -/
theorem upperHitSlice_sub_reflectedNegative_nonnegLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let reflectedNegative : Set Ω :=
      {ω |
        x + W T ω ∈
          Set.Ioc (((-1 : ℝ) - (2 * N + 1 : ℝ)) * a) (-(((2 * N + 1 : ℕ) : ℝ) * a))}
    0 ≤
      μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
          cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) -
        μ.real reflectedNegative := by
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let reflectedNegative : Set Ω :=
    {ω |
      x + W T ω ∈
        Set.Ioc (((-1 : ℝ) - (2 * N + 1 : ℝ)) * a) (-(((2 * N + 1 : ℕ) : ℝ) * a))}
  have hShell :
      μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
          cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) -
        μ.real reflectedNegative =
      shiftedStripMass x a T (2 * N + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
    -- Proof comment: first rewrite the event-level difference to the canonical odd shell.
    simpa [cutoff, reflectedNegative] using
      oddShell_eq_upperHitSlice_sub_reflectedNegativeLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
        (T := T) (hT := hT) N
  have hNonneg :
      0 ≤ shiftedStripMass x a T (2 * N + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
    -- Proof comment: odd shells are instances of the general lower-barrier shell monotonicity.
    exact
      shellDifference_nonnegLocal
        (x := x) (a := a) hx.le (by linarith) (T := T) hT (2 * N + 1)
  -- Proof comment: the event-level slice difference inherits the same nonnegativity after the
  -- normal-form rewrite.
  linarith

/-- Helper for Exercise 21.3.1: every finite odd-shell prefix is already the difference between
the corresponding upper-hit cutoff-slice prefix and the reflected negative prefix. This isolates
the remaining owner theorem to one final assembly step after the prefix telescope. -/
theorem oddShellPrefix_eq_upperHitSlicePrefix_sub_reflectedNegativePrefixLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let oddSliceMass : ℕ → ℝ := fun k ↦
      μ.real (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
        cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))
    let reflectedNegativeMass : ℕ → ℝ := fun k ↦
      μ.real
        {ω |
          x + W T ω ∈
            Set.Ioc (((-1 : ℝ) - (2 * k + 1 : ℝ)) * a) (-(((2 * k + 1 : ℕ) : ℝ) * a))}
    ∑ k ∈ Finset.range N, oddShell k =
      2 * ((∑ k ∈ Finset.range N, oddSliceMass k) -
        ∑ k ∈ Finset.range N, reflectedNegativeMass k) := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let oddSliceMass : ℕ → ℝ := fun k ↦
    μ.real (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
      cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))
  let reflectedNegativeMass : ℕ → ℝ := fun k ↦
    μ.real
      {ω |
        x + W T ω ∈
          Set.Ioc (((-1 : ℝ) - (2 * k + 1 : ℝ)) * a) (-(((2 * k + 1 : ℕ) : ℝ) * a))}
  have hTerm :
      ∀ k : ℕ,
        oddShell k = 2 * (oddSliceMass k - reflectedNegativeMass k) := by
    intro k
    -- Proof comment: each summand is exactly the one-shell reflected-slice identity proved
    -- just above.
    dsimp [oddShell, oddSliceMass, reflectedNegativeMass]
    have hCore :=
      oddShell_eq_upperHitSlice_sub_reflectedNegativeLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
        (T := T) (hT := hT) k
    linarith
  -- Proof comment: sum the one-shell bridge over the finite odd prefix and factor out the
  -- common scalar `2`.
  calc
    ∑ k ∈ Finset.range N, oddShell k
        = ∑ k ∈ Finset.range N, 2 * (oddSliceMass k - reflectedNegativeMass k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hTerm k
    _ = 2 * ((∑ k ∈ Finset.range N, oddSliceMass k) -
          ∑ k ∈ Finset.range N, reflectedNegativeMass k) := by
            rw [Finset.mul_sum]
            ring

/-- Helper for Exercise 21.3.1: after removing the first `N` odd upper-hit cutoff shells from the
top cutoff `W T ≤ a - x`, the remaining mass is exactly the sum of the first `N` even shells
together with the deeper cutoff tail. This isolates the cutoff bookkeeping from the later
lower-survival geometry. -/
theorem upperHitCutoffOddPrefix_telescopesLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} :
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let oddSlice : ℕ → ℝ := fun k ↦
      μ.real (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
        cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))
    let evenSlice : ℕ → ℝ := fun k ↦
      μ.real (cutoff ((-((2 * k : ℕ) : ℝ) * a) - x) \
        cutoff ((-((2 * k + 1 : ℕ) : ℝ) * a) - x))
    ∀ N : ℕ,
      μ.real (cutoff (a - x)) - (∑ k ∈ Finset.range N, oddSlice k) =
        (∑ k ∈ Finset.range N, evenSlice k) +
          μ.real (cutoff ((((1 : ℝ) - (2 * N : ℕ)) * a) - x)) := by
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let oddSlice : ℕ → ℝ := fun k ↦
    μ.real (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
      cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))
  let evenSlice : ℕ → ℝ := fun k ↦
    μ.real (cutoff ((-((2 * k : ℕ) : ℝ) * a) - x) \
      cutoff ((-((2 * k + 1 : ℕ) : ℝ) * a) - x))
  have ha : 0 < a := by
    linarith
  have hCutoffNull : ∀ y : ℝ, NullMeasurableSet (cutoff y) μ := by
    intro y
    -- Proof comment: every concrete upper-hit terminal cutoff is already packaged as a
    -- null-measurable set.
    simpa [cutoff] using
      (upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := a - x) (y := y) (T := T))
  have hCutoffDecomp :
      ∀ u l : ℝ, l ≤ u →
        μ.real (cutoff u) = μ.real (cutoff u \ cutoff l) + μ.real (cutoff l) := by
    intro u l hlu
    have hSubset : cutoff l ⊆ cutoff u := by
      intro ω hω
      exact ⟨hω.1, le_trans hω.2 hlu⟩
    have hInter : cutoff u ∩ cutoff l = cutoff l := by
      -- Proof comment: the smaller cutoff is contained in the larger one, so the intersection
      -- collapses to the lower threshold event.
      ext ω
      constructor
      · intro hω
        exact hω.2
      · intro hω
        exact ⟨hSubset hω, hω⟩
    have hDecomp :=
      MeasureTheory.measureReal_inter_add_diff₀
        (μ := μ) (s := cutoff u) (t := cutoff l) (hCutoffNull l) (measure_ne_top μ _)
    rw [hInter] at hDecomp
    linarith
  intro N
  induction N with
  | zero =>
      -- Proof comment: before removing any odd shell, the remainder is the full top cutoff.
      simp [cutoff, oddSlice, evenSlice]
  | succ N ih =>
      have hOddStep :
          μ.real (cutoff ((((1 : ℝ) - (2 * N : ℕ)) * a) - x)) =
            oddSlice N + μ.real (cutoff ((-((2 * N : ℕ) : ℝ) * a) - x)) := by
        -- Proof comment: the next odd shell is exactly the difference between the current tail
        -- cutoff and the next lower cutoff.
        have hLevel :
            (-((2 * N : ℕ) : ℝ) * a) - x ≤
              (((1 : ℝ) - (2 * N : ℕ)) * a) - x := by
          nlinarith [ha]
        simpa [oddSlice, cutoff] using
          (hCutoffDecomp
            ((((1 : ℝ) - (2 * N : ℕ)) * a) - x)
            ((-((2 * N : ℕ) : ℝ) * a) - x)
            hLevel)
      have hEvenStep :
          μ.real (cutoff ((-((2 * N : ℕ) : ℝ) * a) - x)) =
            evenSlice N + μ.real (cutoff ((-((2 * N + 1 : ℕ) : ℝ) * a) - x)) := by
        -- Proof comment: the next even shell is the following consecutive cutoff difference.
        have hLevel :
            (-((2 * N + 1 : ℕ) : ℝ) * a) - x ≤
              (-((2 * N : ℕ) : ℝ) * a) - x := by
          nlinarith [ha]
        simpa [evenSlice, cutoff] using
          (hCutoffDecomp
            ((-((2 * N : ℕ) : ℝ) * a) - x)
            ((-((2 * N + 1 : ℕ) : ℝ) * a) - x)
            hLevel)
      -- Proof comment: subtracting the next odd shell exposes the next even shell and one
      -- deeper cutoff tail, which is the recursive telescoping pattern needed later.
      calc
        μ.real (cutoff (a - x)) - ∑ k ∈ Finset.range (N + 1), oddSlice k
            = (μ.real (cutoff (a - x)) - ∑ k ∈ Finset.range N, oddSlice k) - oddSlice N := by
                rw [Finset.sum_range_succ]
                ring
        _ = ((∑ k ∈ Finset.range N, evenSlice k) +
              μ.real (cutoff ((((1 : ℝ) - (2 * N : ℕ)) * a) - x))) - oddSlice N := by
              rw [ih]
        _ = ((∑ k ∈ Finset.range N, evenSlice k) +
              μ.real (cutoff ((-((2 * N : ℕ) : ℝ) * a) - x))) := by
              linarith [hOddStep]
        _ = ((∑ k ∈ Finset.range N, evenSlice k) + evenSlice N) +
              μ.real (cutoff ((-((2 * N + 1 : ℕ) : ℝ) * a) - x)) := by
                linarith [hEvenStep]
        _ = (∑ k ∈ Finset.range (N + 1), evenSlice k) +
              μ.real (cutoff ((((1 : ℝ) - (2 * (N + 1) : ℕ)) * a) - x)) := by
                rw [Finset.sum_range_succ]
                congr 1
                ring

/-- Helper for Exercise 21.3.1: surviving above the lower barrier `-x` up to time `T` is
incompatible with ending at or below `-x` at time `T`. -/
theorem lowerSurvival_terminalBelowLowerBarrier_real_eq_zeroLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : 0 < x) {T : NNReal} :
    μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x}) = 0 := by
  let Wc : NNReal → Ω → ℝ := brownianContinuousVersion (μ := μ) (B := W) hW
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let lowerC : Set Ω := {ω | T < hittingAfter Wc ({-x} : Set ℝ) 0 ω}
  let terminal : Set Ω := {ω | W T ω ≤ -x}
  let terminalC : Set Ω := {ω | Wc T ω ≤ -x}
  have hAe :
      (lower ∩ terminal : Set Ω) =ᵐ[μ] (lowerC ∩ terminalC : Set Ω) := by
    filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := W) hW] with ω hω
    have hClock :
        hittingAfter W ({-x} : Set ℝ) 0 ω =
          hittingAfter Wc ({-x} : Set ℝ) 0 ω := by
      exact
        hittingAfter_eq_of_pointwise_eqLocal
          (u := W) (v := Wc) (S := ({-x} : Set ℝ)) (n := (0 : NNReal)) (ω := ω)
          (fun t ↦ (hω t).symm)
    -- Proof comment: off the exceptional set, the continuous modification agrees pointwise with
    -- `W`, so both the lower-barrier clock and the terminal inequality are identical.
    apply propext
    constructor <;> rintro ⟨hLower, hTerm⟩
    · refine ⟨?_, ?_⟩
      · change T < hittingAfter Wc ({-x} : Set ℝ) 0 ω
        change T < hittingAfter W ({-x} : Set ℝ) 0 ω at hLower
        rw [hClock] at hLower
        exact hLower
      · change Wc T ω ≤ -x
        change W T ω ≤ -x at hTerm
        simpa [terminal, hω T] using hTerm
    · refine ⟨?_, ?_⟩
      · change T < hittingAfter W ({-x} : Set ℝ) 0 ω
        change T < hittingAfter Wc ({-x} : Set ℝ) 0 ω at hLower
        rw [hClock] at hLower
        exact hLower
      · change W T ω ≤ -x
        change Wc T ω ≤ -x at hTerm
        simpa [terminalC, hω T] using hTerm
  have hEmpty : (lowerC ∩ terminalC : Set Ω) = ∅ := by
    ext ω
    constructor
    · rintro ⟨hLower, hTerm⟩
      change T < hittingAfter Wc ({-x} : Set ℝ) 0 ω at hLower
      change Wc T ω ≤ -x at hTerm
      have hCont : Continuous (fun t : NNReal ↦ Wc t ω) := by
        simpa [Wc] using brownianContinuousVersion_continuous (μ := μ) (B := W) hW ω
      have hNegCont : Continuous (fun t : NNReal ↦ -Wc t ω) := by
        simpa using hCont.neg
      have hxMem :
          x ∈ Set.Icc ((fun t : NNReal ↦ -Wc t ω) 0) ((fun t : NNReal ↦ -Wc t ω) T) := by
        refine ⟨?_, ?_⟩
        · simpa [Wc, brownianContinuousVersion_zero (μ := μ) (B := W) hW ω] using hx.le
        · have hxUpper : x ≤ -Wc T ω := by
            linarith
          simpa using hxUpper
      obtain ⟨s, hsIcc, hsEq⟩ :=
        (intermediate_value_Icc
          (a := (0 : NNReal))
          (b := T)
          (by positivity)
          hNegCont.continuousOn) hxMem
      have hsMem : Wc s ω ∈ ({-x} : Set ℝ) := by
        simp [Set.mem_singleton_iff]
        linarith [hsEq]
      have hHitLe :
          hittingAfter Wc ({-x} : Set ℝ) 0 ω ≤ T := by
        exact
          (hittingAfter_le_of_mem
            (u := Wc) (s := ({-x} : Set ℝ)) (n := (0 : NNReal)) (ω := ω)
            hsIcc.1 hsMem).trans <|
            by exact_mod_cast hsIcc.2
      exact (not_lt_of_ge hHitLe) hLower
    · simp
  -- Proof comment: transfer the impossible terminal/lower-survival configuration to the
  -- continuous Brownian modification, where continuity forces an exact lower-barrier hit by time
  -- `T`.
  calc
    μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x})
        = μ.real (lowerC ∩ terminalC : Set Ω) := by
            simpa [lower, lowerC, terminal, terminalC] using
              (MeasureTheory.measureReal_congr hAe)
    _ = 0 := by
          rw [hEmpty]
          simp

/-- Helper for Exercise 21.3.1: every even upper-hit cutoff slice is null on `upperLoss`, because
its terminal window lies at or below the forbidden lower barrier `-x`. -/
theorem upperLossEvenSlice_real_eq_zeroLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (k : ℕ) :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let evenSlice : Set Ω :=
      {ω |
        hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
          W T ω ∈
            Set.Ioc ((-((2 * k + 1 : ℕ) : ℝ) * a) - x) ((-((2 * k : ℕ) : ℝ) * a) - x)}
    μ.real (upperLoss ∩ evenSlice) = 0 := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let evenSlice : Set Ω :=
    {ω |
      hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
        W T ω ∈
          Set.Ioc ((-((2 * k + 1 : ℕ) : ℝ) * a) - x) ((-((2 * k : ℕ) : ℝ) * a) - x)}
  have ha : 0 < a := by
    linarith
  have hSub :
      upperLoss ∩ evenSlice ⊆
        ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x}) := by
    intro ω hω
    rcases hω with ⟨hUpperLoss, hEven⟩
    refine ⟨hUpperLoss.1, ?_⟩
    have hUpper :
        (-((2 * k : ℕ) : ℝ) * a) - x ≤ -x := by
      nlinarith [ha]
    exact le_trans hEven.2.2 hUpper
  have hZero :
      μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x}) = 0 := by
    simpa using
      lowerSurvival_terminalBelowLowerBarrier_real_eq_zeroLocal
        (μ := μ) (W := W) hW (x := x) hx (T := T)
  -- Proof comment: every even slice sits inside the impossible configuration “survive above `-x`
  -- but end at or below `-x`”, so its `upperLoss` contribution vanishes.
  exact
    MeasureTheory.measureReal_mono_null
      (s₁ := upperLoss ∩ evenSlice)
      (s₂ := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x})
      hSub hZero (measure_ne_top μ _)

/-- Helper for Exercise 21.3.1: every odd upper-hit slice below the first one already forces the
terminal value to lie at or below `-x`, so it is incompatible with lower-barrier survival.
This rules out the previously attempted `lower ∩ oddSlice` bridge for indices `k ≥ 1`. -/
theorem lowerSurvivalOddSlice_real_eq_zero_of_one_leLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (k : ℕ) (hk : 1 ≤ k) :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    μ.real
        (lower ∩
          (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
            cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))) = 0 := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  have ha : 0 < a := by
    linarith
  have hSub :
      lower ∩
          (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
            cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x)) ⊆
        ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x}) := by
    intro ω hω
    rcases hω with ⟨hLower, hOdd⟩
    refine ⟨hLower, ?_⟩
    have hUpper :
        (((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x ≤ -x := by
      nlinarith [ha, hk]
    exact le_trans hOdd.1.2 hUpper
  have hZero :
      μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x}) = 0 := by
    simpa using
      lowerSurvival_terminalBelowLowerBarrier_real_eq_zeroLocal
        (μ := μ) (W := W) hW (x := x) hx (T := T)
  -- Proof comment: once the odd slice is below `-x`, it is contained in the impossible
  -- configuration "survive above `-x` but end at or below `-x`".
  exact
    MeasureTheory.measureReal_mono_null
      (s₁ := lower ∩
        (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
          cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x)))
      (s₂ := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ {ω | W T ω ≤ -x})
      hSub hZero (measure_ne_top μ _)

/-- Helper for Exercise 21.3.1: every odd upper-hit slice below the first one also has zero real
mass on `upperLoss`, because on any such slice `upperLoss` agrees with lower-barrier survival and
the lower-survival mass was already shown to vanish. -/
theorem upperLossOddSlice_real_eq_zero_of_one_leLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (k : ℕ) (hk : 1 ≤ k) :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let oddSlice : Set Ω :=
      cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
        cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x)
    μ.real (upperLoss ∩ oddSlice) = 0 := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let oddSlice : Set Ω :=
    cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
      cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x)
  have hUpperLoss :
      upperLoss =
        lower ∩ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
    -- Proof comment: on the event-level, `upperLoss` is exactly lower-barrier survival together
    -- with an upper-barrier hit by time `T`.
    simpa [upperLoss, lower] using
      (upperLoss_eq_lowerSurvival_inter_upperHitLocal
        (W := W) (x := x) (a := a) (T := T))
  have hSet :
      upperLoss ∩ oddSlice = lower ∩ oddSlice := by
    ext ω
    constructor
    · intro hω
      -- Proof comment: an `upperLoss` point already carries lower-barrier survival, so
      -- intersecting with the odd cutoff slice forgets only the redundant interval-failure data.
      exact ⟨hω.1.1, hω.2⟩
    · intro hω
      have hHit :
          ω ∈ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := hω.2.1
      have hUpperLossMem :
          ω ∈ lower ∩ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
        exact ⟨hω.1, hHit⟩
      -- Proof comment: conversely, on any odd cutoff slice the upper-hit condition is built in,
      -- so lower-barrier survival reconstructs `upperLoss`.
      exact ⟨by simpa [hUpperLoss] using hUpperLossMem, hω.2⟩
  have hZero :
      μ.real (lower ∩ oddSlice) = 0 := by
    -- Proof comment: the corresponding lower-survival slice is already known to be null when
    -- `k ≥ 1`.
    simpa [lower, cutoff, oddSlice] using
      lowerSurvivalOddSlice_real_eq_zero_of_one_leLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
        (T := T) k hk
  -- Proof comment: rewrite the `upperLoss` slice to the lower-survival slice and apply the
  -- established vanishing result.
  rw [hSet]
  exact hZero

/-- Helper for Exercise 21.3.1: the odd correction-prefix error for `upperLoss` is exactly the
boundary tail minus the interval paired-shell remainder at the same odd prefix. -/
theorem upperLossCorrectionOddPrefix_intervalWindowTransportLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) =
      boundaryTail (2 * N + 1) -
        (interval - ∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hGap : lower - interval = μ.real upperLoss := by
    -- Proof comment: the lower-minus-interval scalar gap is exactly the explicit `upperLoss`
    -- event introduced for the Brownian correction terms.
    simpa [lower, interval, upperLoss] using
      intervalSurvivalGap_eq_upperLossRealLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T)
  have hPrefix :
      ∑ n ∈ Finset.range (2 * N + 1), correction n =
        (lower - boundaryTail (2 * N + 1)) -
          ∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n := by
    -- Proof comment: normalize the odd correction prefix by the earlier exact finite
    -- lower-survival minus boundary-tail minus paired-shell identity.
    simpa [correction, boundaryTail, lower] using
      upperLossCorrection_prefix_eq_lowerBarrierSurvival_sub_boundaryTail_sub_pairShellPrefixLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT (2 * N + 1)
  -- Proof comment: substituting the exact odd-prefix formula transports the upper-loss error to
  -- the interval remainder against the same boundary tail.
  linarith [hGap, hPrefix]

/-- Helper for Exercise 21.3.1: once we restrict to an upper-hit terminal cutoff, the explicit
`upperLoss` event is just lower-barrier survival intersected with that same cutoff. This removes
the redundant upper-hit factor before the remaining cutoff telescoping step. -/
theorem upperLoss_inter_cutoff_eq_lowerSurvival_inter_cutoffLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} (y : ℝ) :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoff : ℝ → Set Ω := fun z ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ z}
    upperLoss ∩ cutoff y = lower ∩ cutoff y := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoff : ℝ → Set Ω := fun z ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ z}
  have hUpperLoss :
      upperLoss =
        lower ∩ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
    -- Proof comment: this is the earlier structural rewrite of `upperLoss` as lower survival
    -- together with an upper-barrier hit by time `T`.
    simpa [lower, upperLoss] using
      (upperLoss_eq_lowerSurvival_inter_upperHitLocal
        (W := W) (x := x) (a := a) (T := T))
  ext ω
  constructor
  · rintro ⟨hUpperLossMem, hCutoff⟩
    have hLowerMem :
        ω ∈ lower ∩ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
      simpa [hUpperLoss] using hUpperLossMem
    -- Proof comment: the cutoff already records the upper-hit half, so only lower survival
    -- remains after intersecting with `upperLoss`.
    exact ⟨hLowerMem.1, hCutoff⟩
  · rintro ⟨hLowerMem, hCutoff⟩
    have hUpperLossMem :
        ω ∈ lower ∩ {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
      exact ⟨hLowerMem, hCutoff.1⟩
    -- Proof comment: conversely, the cutoff itself supplies the upper-hit condition needed to
    -- rebuild `upperLoss`.
    exact ⟨by simpa [hUpperLoss] using hUpperLossMem, hCutoff⟩

/-- Helper for Exercise 21.3.1: taking real measures preserves the cutoff-side rewrite from
`upperLoss` to lower-barrier survival. This packages the exact scalar replacement used when the
odd cutoff telescope is intersected with `upperLoss`. -/
theorem upperLoss_inter_cutoff_real_eq_lowerSurvival_inter_cutoffLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} (y : ℝ) :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoff : ℝ → Set Ω := fun z ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ z}
    μ.real (upperLoss ∩ cutoff y) = μ.real (lower ∩ cutoff y) := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoff : ℝ → Set Ω := fun z ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ z}
  have hSet :
      upperLoss ∩ cutoff y = lower ∩ cutoff y := by
    -- Proof comment: this is the set-level cutoff rewrite proved just above, now reused at the
    -- scalar measure level without any extra transport.
    simpa [lower, upperLoss, cutoff] using
      upperLoss_inter_cutoff_eq_lowerSurvival_inter_cutoffLocal
        (W := W) (x := x) (a := a) (T := T) y
  rw [hSet]

/-- Helper for Exercise 21.3.1: every `upperLoss` path either stays in the top upper-hit cutoff
`W T ≤ a - x` or finishes above the upper barrier at time `T`. This is the first pathwise split
needed for the remaining odd-prefix owner theorem. -/
theorem upperLoss_eq_inter_cutoffTop_union_inter_terminalAboveLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoffTop : Set Ω :=
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ a - x}
    let above : Set Ω := {ω | a - x < W T ω}
    upperLoss = (upperLoss ∩ cutoffTop) ∪ (upperLoss ∩ above) := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoffTop : Set Ω :=
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ a - x}
  let above : Set Ω := {ω | a - x < W T ω}
  have hUpperLoss :
      upperLoss =
        ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
          {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T}) := by
    -- Proof comment: the earlier structural rewrite exposes the upper-hit event underlying
    -- `upperLoss`, so we can split by the terminal inequality at time `T`.
    simpa [upperLoss] using
      (upperLoss_eq_lowerSurvival_inter_upperHitLocal
        (W := W) (x := x) (a := a) (T := T))
  ext ω
  constructor
  · intro hω
    by_cases hTerminal : W T ω ≤ a - x
    · left
      exact ⟨hω, ⟨by
        have hUpperLossMem :
            ω ∈ {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
              {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
          simpa [hUpperLoss] using hω
        exact hUpperLossMem.2, hTerminal⟩⟩
    · right
      -- Proof comment: if the terminal value is not in the top cutoff, it must lie strictly above
      -- the upper barrier, and this is the complementary branch of the split.
      exact ⟨hω, by exact lt_of_not_ge hTerminal⟩
  · rintro (⟨hω, -⟩ | ⟨hω, -⟩)
    · exact hω
    · exact hω

/-- Helper for Exercise 21.3.1: the real mass of `upperLoss` splits into its terminal-below-top
cutoff branch and its terminal-above branch. This removes the union bookkeeping before the final
finite remainder identity is assembled. -/
theorem upperLoss_real_eq_inter_cutoffTop_add_inter_terminalAboveLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} {T : NNReal} :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoffTop : Set Ω :=
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ a - x}
    let above : Set Ω := {ω | a - x < W T ω}
    μ.real upperLoss =
      μ.real (upperLoss ∩ cutoffTop) + μ.real (upperLoss ∩ above) := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoffTop : Set Ω :=
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ a - x}
  let above : Set Ω := {ω | a - x < W T ω}
  have hAboveNull : NullMeasurableSet above μ := by
    -- Proof comment: the terminal-above branch is a measurable terminal event.
    exact ((hW.stronglyMeasurable T).measurable measurableSet_Ioi).nullMeasurableSet
  have hDiff :
      upperLoss \ above = upperLoss ∩ cutoffTop := by
    have hUpperLoss :
        upperLoss =
          ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
            {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T}) := by
      -- Proof comment: rewrite `upperLoss` to expose the upper-hit component needed to recover
      -- the cutoff-top branch from the complement of `above`.
      simpa [upperLoss] using
        (upperLoss_eq_lowerSurvival_inter_upperHitLocal
          (W := W) (x := x) (a := a) (T := T))
    ext ω
    constructor
    · rintro ⟨hUpperLossMem, hNotAbove⟩
      have hUpperHit :
          hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T := by
        have hMem :
            ω ∈ {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩
              {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T} := by
          simpa [hUpperLoss] using hUpperLossMem
        exact hMem.2
      have hTerminal : W T ω ≤ a - x := by
        have hNotAbove' : ¬ a - x < W T ω := by
          simpa [above] using hNotAbove
        exact not_lt.mp hNotAbove'
      -- Proof comment: outside the strict terminal-above branch, an `upperLoss` path sits
      -- exactly in the cutoff-top branch.
      exact ⟨hUpperLossMem, ⟨hUpperHit, hTerminal⟩⟩
    · rintro ⟨hUpperLossMem, hCutoffTop⟩
      refine ⟨hUpperLossMem, ?_⟩
      -- Proof comment: the cutoff-top inequality `W T ≤ a - x` excludes the strict above branch.
      simpa [above] using (not_lt_of_ge hCutoffTop.2)
  have hDecomp :=
    MeasureTheory.measureReal_inter_add_diff₀
      (μ := μ) (s := upperLoss) (t := above) hAboveNull (measure_ne_top μ _)
  -- Proof comment: split `upperLoss` by the measurable branch `above`, then rewrite the
  -- complementary difference back to `upperLoss ∩ cutoffTop`.
  rw [hDiff] at hDecomp
  linarith

/-- Helper for Exercise 21.3.1: the `upperLoss` branch below the lower barrier has zero real mass,
because lower-barrier survival is incompatible with terminal values `W T ≤ -x`. -/
theorem upperLossCutoffBelowLowerBarrier_real_eq_zeroLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) {T : NNReal} :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    μ.real (upperLoss ∩ cutoff (-x)) = 0 := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  have hRewrite :
      μ.real (upperLoss ∩ cutoff (-x)) = μ.real (lower ∩ cutoff (-x)) := by
    -- Proof comment: on any upper-hit cutoff, `upperLoss` is just lower-barrier survival.
    simpa [lower, upperLoss, cutoff] using
      upperLoss_inter_cutoff_real_eq_lowerSurvival_inter_cutoffLocal
        (μ := μ) (W := W) (x := x) (a := a) (T := T) (-x)
  have hSub :
      lower ∩ cutoff (-x) ⊆ lower ∩ {ω | W T ω ≤ -x} := by
    intro ω hω
    exact ⟨hω.1, hω.2.2⟩
  have hZero :
      μ.real (lower ∩ {ω | W T ω ≤ -x}) = 0 := by
    -- Proof comment: lower-barrier survival cannot coexist with a terminal value at or below
    -- the same lower barrier.
    simpa [lower] using
      lowerSurvival_terminalBelowLowerBarrier_real_eq_zeroLocal
        (μ := μ) (W := W) hW (x := x) hx (T := T)
  -- Proof comment: the cutoff branch `W T ≤ -x` sits inside the impossible lower-survival
  -- terminal event, so its real mass vanishes as well.
  rw [hRewrite]
  exact
    MeasureTheory.measureReal_mono_null
      (s₁ := lower ∩ cutoff (-x))
      (s₂ := lower ∩ {ω | W T ω ≤ -x})
      hSub hZero (measure_ne_top μ _)

/-- Helper for Exercise 21.3.1: after removing the null piece below `-x`, the cutoff-top
contribution of `upperLoss` lives entirely on the surviving base slice `Set.Ioc (-x) (a - x)`. -/
theorem upperLoss_inter_cutoffTop_real_eq_baseSliceLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let cutoffTop : Set Ω := cutoff (a - x)
    let baseSlice : Set Ω := cutoffTop \ cutoff (-x)
    μ.real (upperLoss ∩ cutoffTop) = μ.real (upperLoss ∩ baseSlice) := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let cutoff : ℝ → Set Ω := fun y ↦
    {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
  let cutoffTop : Set Ω := cutoff (a - x)
  let baseSlice : Set Ω := cutoffTop \ cutoff (-x)
  have hLevel : -x ≤ a - x := by
    linarith
  have hCutoffNull : NullMeasurableSet (cutoff (-x)) μ := by
    -- Proof comment: every upper-hit cutoff `W T ≤ y` is already a null-measurable terminal
    -- event.
    simpa [cutoff] using
      upperHitTerminalBelow_nullMeasurableLocal
        (μ := μ) (W := W) (hW := hW) (b := a - x) (y := -x) (T := T)
  have hInter :
      (upperLoss ∩ cutoffTop) ∩ cutoff (-x) = upperLoss ∩ cutoff (-x) := by
    ext ω
    constructor
    · rintro ⟨⟨hUpperLoss, -⟩, hCutoffBelow⟩
      exact ⟨hUpperLoss, hCutoffBelow⟩
    · rintro ⟨hUpperLoss, hCutoffBelow⟩
      have hCutoffTopMem : ω ∈ cutoffTop := by
        exact ⟨hCutoffBelow.1, le_trans hCutoffBelow.2 hLevel⟩
      exact ⟨⟨hUpperLoss, hCutoffTopMem⟩, hCutoffBelow⟩
  have hDiff :
      (upperLoss ∩ cutoffTop) \ cutoff (-x) = upperLoss ∩ baseSlice := by
    ext ω
    constructor
    · rintro ⟨⟨hUpperLoss, hCutoffTopMem⟩, hNotCutoffBelow⟩
      exact ⟨hUpperLoss, ⟨hCutoffTopMem, hNotCutoffBelow⟩⟩
    · rintro ⟨hUpperLoss, hBaseSlice⟩
      exact ⟨⟨hUpperLoss, hBaseSlice.1⟩, hBaseSlice.2⟩
  have hZero :
      μ.real (upperLoss ∩ cutoff (-x)) = 0 := by
    -- Proof comment: the discarded lower cutoff was proved to be null just above.
    simpa [upperLoss, cutoff] using
      upperLossCutoffBelowLowerBarrier_real_eq_zeroLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (T := T)
  have hDecomp :=
    MeasureTheory.measureReal_inter_add_diff₀
      (μ := μ) (s := upperLoss ∩ cutoffTop) (t := cutoff (-x))
      hCutoffNull (measure_ne_top μ _)
  -- Proof comment: split the cutoff-top branch at `-x`; the lower cutoff contributes zero, so
  -- only the surviving base slice remains.
  rw [hInter, hDiff] at hDecomp
  linarith

/-- Helper for Exercise 21.3.1: on the strict terminal-above branch `W T > a - x`, the
upper-barrier hit is forced almost surely, so `upperLoss` agrees in real measure with lower
survival on that branch. -/
theorem upperLoss_inter_terminalAbove_real_eq_lowerSurvival_inter_terminalAboveLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hxa : x < a) {T : NNReal} :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let above : Set Ω := {ω | a - x < W T ω}
    μ.real (upperLoss ∩ above) = μ.real (lower ∩ above) := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let above : Set Ω := {ω | a - x < W T ω}
  let upperHit : Set Ω := {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T}
  have hb : 0 < a - x := sub_pos.mpr hxa
  have hUpperLoss :
      upperLoss = lower ∩ upperHit := by
    -- Proof comment: rewrite `upperLoss` as lower-barrier survival together with the upper hit.
    simpa [lower, upperLoss, upperHit] using
      (upperLoss_eq_lowerSurvival_inter_upperHitLocal
        (W := W) (x := x) (a := a) (T := T))
  have hUpperHitAe :
      upperHit =ᵐ[μ] ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a - x ≤ W t ω} : Set Ω) := by
    -- Proof comment: the upper hit by time `T` is almost surely the closed running-maximum event.
    simpa [upperHit] using
      hitUpperBeforeTime_event_ae_eq_runningMaxClosedLocal
        (μ := μ) (B := W) hW (b := a - x) hb (T := T)
  have hAboveAe : upperHit ∩ above =ᵐ[μ] above := by
    filter_upwards [hUpperHitAe] with ω hω
    apply propext
    constructor
    · intro hMem
      exact hMem.2
    · intro hMem
      have hRun :
          ω ∈ ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a - x ≤ W t ω} : Set Ω) := by
        exact ⟨T, ⟨by positivity, le_rfl⟩, le_of_lt hMem⟩
      exact ⟨hω.mpr hRun, hMem⟩
  have hInterAe : lower ∩ (upperHit ∩ above) =ᵐ[μ] lower ∩ above := by
    filter_upwards [hAboveAe] with ω hω
    simp [hω]
  calc
    μ.real (upperLoss ∩ above) = μ.real ((lower ∩ upperHit) ∩ above) := by
      rw [hUpperLoss]
    _ = μ.real (lower ∩ (upperHit ∩ above)) := by
          congr 1
          ext ω
          simp [and_left_comm, and_assoc]
    _ = μ.real (lower ∩ above) := by
          exact MeasureTheory.measureReal_congr hInterAe

/-- Helper for Exercise 21.3.1: on the strict terminal-above branch, negating the Brownian path
turns lower-barrier survival for `W` into upper-barrier survival below the reflected cutoff
`x - a`. -/
theorem lowerSurvival_inter_terminalAbove_eq_negUpperSurvival_terminalBelowLocal
    {W : NNReal → Ω → ℝ} {x a : ℝ} {T : NNReal} :
    let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
    let above : Set Ω := {ω | a - x < W T ω}
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    let below : Set Ω := {ω | Bneg T ω < x - a}
    lower ∩ above = ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩ below) := by
  let lower : Set Ω := {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let above : Set Ω := {ω | a - x < W T ω}
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  let below : Set Ω := {ω | Bneg T ω < x - a}
  have hLowerEq :
      lower = {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} := by
    -- Proof comment: the imported negation bridge already identifies the two singleton
    -- lower-survival events pathwise.
    simpa [lower, Bneg] using
      (negSingletonHittingEvent_eq_singletonHit (W := W) (c := x) (δ := T)).symm
  have hBelowEq : above = below := by
    -- Proof comment: negating the terminal value rewrites the strict above-cutoff inequality to
    -- the reflected strict below-cutoff inequality.
    ext ω
    dsimp [above, below, Bneg]
    linarith
  calc
    lower ∩ above = {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩ above := by
      rw [hLowerEq]
    _ = {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩ below := by
      rw [hBelowEq]

/-- Helper for Exercise 21.3.1: the strict terminal-above branch of `upperLoss` has the same real
mass as the base closed cutoff on the negated path, because the single boundary level `x - a`
has zero terminal Gaussian mass. -/
theorem upperLoss_inter_terminalAbove_real_eq_negatedClosedCutoffBaseLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    let above : Set Ω := {ω | a - x < W T ω}
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    μ.real (upperLoss ∩ above) =
      μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩
        {ω | Bneg T ω ≤ x - a}) := by
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let above : Set Ω := {ω | a - x < W T ω}
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  let survive : Set Ω := {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω}
  let belowOpen : Set Ω := {ω | Bneg T ω < x - a}
  let belowClosed : Set Ω := {ω | Bneg T ω ≤ x - a}
  have hRewrite :
      μ.real (upperLoss ∩ above) =
        μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ above) := by
    -- Proof comment: on the terminal-above branch, `upperLoss` is already just lower-barrier
    -- survival before the negation transport is applied.
    simpa [upperLoss, above] using
      upperLoss_inter_terminalAbove_real_eq_lowerSurvival_inter_terminalAboveLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hxa := hxa) (T := T)
  have hNegPath :
      ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ above) = survive ∩ belowOpen := by
    -- Proof comment: negating the path moves the strict terminal-above branch to the strict
    -- reflected cutoff on the negated Brownian motion.
    simpa [above, Bneg, survive, belowOpen] using
      lowerSurvival_inter_terminalAbove_eq_negUpperSurvival_terminalBelowLocal
        (W := W) (x := x) (a := a) (T := T)
  have hBneg : IsBrownianMotion μ Bneg := neg_isBrownianMotion hW
  have hBelowAeMap :
      Set.Iio (x - a) =ᵐ[μ.map (fun ω ↦ Bneg T ω)] Set.Iic (x - a) := by
    have hMapSingleton :
        (μ.map (fun ω ↦ Bneg T ω)) ({x - a} : Set ℝ) = 0 := by
      rw [show μ.map (fun ω ↦ Bneg T ω) = gaussianReal 0 T by
        simpa [Bneg] using (hBneg.gaussian_marginal hT).map_eq]
      exact (ProbabilityTheory.noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton (x - a)
    -- Proof comment: the terminal law of the negated Brownian path has no atom at `x - a`, so
    -- the strict and closed reflected cutoffs agree almost everywhere under that law.
    exact MeasureTheory.Iio_ae_eq_Iic' hMapSingleton
  have hBelowAe :
      belowOpen =ᵐ[μ] belowClosed := by
    have hPred :
        ∀ᵐ y ∂μ.map (fun ω ↦ Bneg T ω), y < x - a ↔ y ≤ x - a := by
      simpa using hBelowAeMap
    have hPredPre :
        ∀ᵐ ω ∂μ, Bneg T ω < x - a ↔ Bneg T ω ≤ x - a := by
      exact
        (MeasureTheory.ae_map_iff
          ((hBneg.stronglyMeasurable T).measurable.aemeasurable) (by measurability)).1 hPred
    -- Proof comment: pull the almost-everywhere strict-to-closed equality back through the
    -- measurable terminal map `ω ↦ Bneg T ω`.
    simpa [belowOpen, belowClosed]
      using hPredPre
  have hInterAe :
      survive ∩ belowOpen =ᵐ[μ] survive ∩ belowClosed := by
    filter_upwards [hBelowAe] with ω hω
    simp [hω]
  calc
    μ.real (upperLoss ∩ above) =
      μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ above) := hRewrite
    _ = μ.real (survive ∩ belowOpen) := by
          rw [hNegPath]
    _ = μ.real (survive ∩ belowClosed) := by
          exact MeasureTheory.measureReal_congr hInterAe

/-- Helper for Exercise 21.3.1: on each odd window below `x - a` for the negated path `Bneg`,
survival below the upper barrier `x` is exactly the positive odd strip mass minus the reflected
negative companion strip. This isolates the one-window reflection step needed on the
terminal-above branch. -/
theorem negatedLowerSurvival_terminalWindow_eq_shellDifferenceLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (k : ℕ) :
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    let window : Set Ω :=
      {ω |
        Bneg T ω ∈
          Set.Ioc
            (x - (((2 * k + 2 : ℕ) : ℝ) * a))
            (x - (((2 * k + 1 : ℕ) : ℝ) * a))}
    μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩ window) =
      shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  let window : Set Ω :=
    {ω |
      Bneg T ω ∈
        Set.Ioc
          (x - (((2 * k + 2 : ℕ) : ℝ) * a))
          (x - (((2 * k + 1 : ℕ) : ℝ) * a))}
  let hit : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T}
  have hBneg : IsBrownianMotion μ Bneg := neg_isBrownianMotion hW
  have ha : 0 < a := by
    linarith
  have hWindowReal :
      μ.real window = shiftedStripMass x a T (2 * k + 1 : ℤ) := by
    have hSet :
        window =
          {ω |
            x + W T ω ∈
              Set.Ioc
                ((((2 * k + 1 : ℕ) : ℝ) * a))
                ((((2 * k + 2 : ℕ) : ℝ) * a))} := by
      ext ω
      constructor
      · intro hω
        constructor <;> linarith [hω.1, hω.2]
      · intro hω
        constructor <;> linarith [hω.1, hω.2]
    -- Proof comment: negating the terminal value on the odd window below `x - a` is the same as
    -- landing in the positive odd strip for `x + W T`.
    rw [hSet]
    symm
    exact
      shiftedStripMass_eq_terminalIocReal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) hT (2 * k + 1 : ℤ)
  have hHitReal :
      μ.real (hit ∩ window) = shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
    have hStrip :
        μ.real (hit ∩ window) = shiftedStripMass (a - x) a T (2 * k + 2 : ℤ) := by
      -- Proof comment: for `Bneg`, the odd window below `x - a` is exactly the standard
      -- reflected upper-hit strip below the upper barrier `x`.
      simpa [Bneg, window, hit] using
        upperBarrierHitBeforeTime_terminalStrip_eq_shiftedStripMassLocal
          (μ := μ) (W := Bneg) (hW := hBneg) (x := a - x) (a := a)
          (hx := by linarith) (hxa := by linarith)
          (T := T) (hT := hT) (n := 2 * k + 2) (hn := by omega)
    have hReflect :
        shiftedStripMass (a - x) a T (2 * k + 2 : ℤ) =
          shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
      calc
        shiftedStripMass (a - x) a T (2 * k + 2 : ℤ)
            =
              μ.real
                {ω |
                  (a - x) + Bneg T ω ∈
                    Set.Ioc
                      ((((2 * k + 2 : ℕ) : ℝ) * a))
                      ((((2 * k + 3 : ℕ) : ℝ) * a))} := by
                symm
                exact
                  shiftedStripMass_eq_terminalIocReal
                    (μ := μ) (W := Bneg) (hW := hBneg) (x := a - x) (a := a) (T := T) hT
                    (2 * k + 2 : ℤ)
        _ =
            μ.real
              {ω |
                x + W T ω ∈
                  Set.Ioc
                    (((-1 : ℝ) - ((2 * k + 1 : ℕ) : ℝ)) * a)
                    (-((((2 * k + 1 : ℕ) : ℝ) * a)))} := by
              congr 1
              ext ω
              constructor
              · intro hω
                constructor <;> linarith [hω.1, hω.2]
              · intro hω
                constructor <;> linarith [hω.1, hω.2]
        _ = shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
              symm
              simpa using
                reflectedShiftedStripMass_eq_terminalIocReal
                  (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) hT (2 * k + 1)
    exact hStrip.trans hReflect
  have hHitNull : NullMeasurableSet hit μ := by
    let cutoffTop : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T ∧ Bneg T ω ≤ x}
    let above : Set Ω := {ω | x < Bneg T ω}
    have hCutoffTopNull : NullMeasurableSet cutoffTop μ := by
      -- Proof comment: the top terminal cutoff for the hit event is the standard null-measurable
      -- upper-hit terminal slice.
      simpa [cutoffTop, Bneg] using
        upperHitTerminalBelow_nullMeasurableLocal
          (μ := μ) (W := Bneg) (hW := hBneg) (b := x) (y := x) (T := T)
    have hAboveNull : NullMeasurableSet above μ := by
      -- Proof comment: the complementary strict-above terminal branch is measurable by terminal
      -- measurability of the Brownian path.
      exact ((hBneg.stronglyMeasurable T).measurable measurableSet_Ioi).nullMeasurableSet
    have hHitEq : hit = cutoffTop ∪ above := by
      -- Proof comment: every hit-by-time path either ends at or below `x` or strictly above `x`.
      ext ω
      simp [hit, cutoffTop, above, and_left_comm, and_assoc, le_or_lt]
    rw [hHitEq]
    exact hCutoffTopNull.union hAboveNull
  have hDiff :
      window \ hit = ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩ window) := by
    ext ω
    simp [hit, window, not_le, and_left_comm, and_assoc]
  have hDecomp :=
    MeasureTheory.measureReal_inter_add_diff₀
      (μ := μ) (s := window) (t := hit) hHitNull (measure_ne_top μ _)
  have hInter :
      μ.real (window ∩ hit) = μ.real (hit ∩ window) := by
    congr 1
    ext ω
    simp [and_left_comm, and_assoc]
  -- Proof comment: decompose the terminal window into the hit part and the surviving-below-`x`
  -- part, then substitute the two normal forms proved above.
  rw [hDiff, hInter] at hDecomp
  linarith [hWindowReal, hHitReal, hDecomp]

/-- Helper for Exercise 21.3.1: on the negated Brownian path, the surviving closed cutoff
`Bneg T ≤ x - m * a` is the terminal Gaussian upper tail at level `m * a` minus the reflected
closed tail beyond `x + m * a`. -/
theorem negatedLowerSurvival_terminalBelowCutoffRealLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    {m : ℕ} (hm : 1 ≤ m) :
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩
        {ω | Bneg T ω ≤ x - ((m : ℝ) * a)}) =
      (gaussianReal x T).real (Set.Ici ((m : ℝ) * a)) -
        (gaussianReal 0 T).real (Set.Ici (x + ((m : ℝ) * a))) := by
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  let survive : Set Ω := {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω}
  let cutoff : Set Ω := {ω | Bneg T ω ≤ x - ((m : ℝ) * a)}
  let hit : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T}
  have hBneg : IsBrownianMotion μ Bneg := neg_isBrownianMotion hW
  have ha : 0 < a := by
    linarith
  have hHitReal :
      μ.real (hit ∩ cutoff) =
        (gaussianReal 0 T).real (Set.Ici (x + ((m : ℝ) * a))) := by
    have hCutoffLt : x - ((m : ℝ) * a) < x := by
      nlinarith [ha, hm]
    -- Proof comment: once the cutoff lies strictly below the upper barrier `x`, the restored
    -- closed-tail reflection theorem applies directly to the negated path.
    simpa [hit, cutoff, Bneg] using
      hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal
        (μ := μ) (W := Bneg) (hW := hBneg) (b := x) (y := x - ((m : ℝ) * a)) hx hT
        hCutoffLt
  have hCutoffReal :
      μ.real cutoff = (gaussianReal x T).real (Set.Ici ((m : ℝ) * a)) := by
    have hSet :
        cutoff = {ω | x + W T ω ∈ Set.Ici ((m : ℝ) * a)} := by
      ext ω
      constructor <;> intro hω <;> dsimp [cutoff, Bneg] at * <;> linarith
    -- Proof comment: terminal values for the negated cutoff become the shifted Brownian upper
    -- tail `{m * a ≤ x + W T}` under the original path.
    rw [hSet]
    exact
      shiftedBrownianTerminalReal_eq_gaussianReal
        (hW := hW) (x := x) (T := T) hT measurableSet_Ici
  have hHitNull : NullMeasurableSet hit μ := by
    let cutoffTop : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T ∧ Bneg T ω ≤ x}
    let above : Set Ω := {ω | x < Bneg T ω}
    have hCutoffTopNull : NullMeasurableSet cutoffTop μ := by
      -- Proof comment: the standard null-measurable upper-hit cutoff package applies unchanged
      -- to the negated Brownian path at level `x`.
      simpa [cutoffTop, Bneg] using
        upperHitTerminalBelow_nullMeasurableLocal
          (μ := μ) (W := Bneg) (hW := hBneg) (b := x) (y := x) (T := T)
    have hAboveNull : NullMeasurableSet above μ := by
      -- Proof comment: the complementary strict-above terminal branch is measurable by terminal
      -- measurability of `Bneg`.
      exact ((hBneg.stronglyMeasurable T).measurable measurableSet_Ioi).nullMeasurableSet
    have hHitEq : hit = cutoffTop ∪ above := by
      -- Proof comment: every hit-by-time path ends either at or below `x` or strictly above it
      -- at time `T`.
      ext ω
      simp [hit, cutoffTop, above, le_or_lt]
    rw [hHitEq]
    exact hCutoffTopNull.union hAboveNull
  have hDiff : cutoff \ hit = survive ∩ cutoff := by
    ext ω
    simp [cutoff, hit, survive, and_left_comm, and_assoc, not_le]
  have hDecomp :=
    MeasureTheory.measureReal_inter_add_diff₀
      (μ := μ) (s := cutoff) (t := hit) hHitNull (measure_ne_top μ _)
  have hInter : μ.real (cutoff ∩ hit) = μ.real (hit ∩ cutoff) := by
    congr 1
    ext ω
    simp [and_left_comm, and_assoc]
  -- Proof comment: split the terminal cutoff into the hit branch and the surviving branch, then
  -- substitute the Gaussian cutoff mass and the reflected closed-tail mass.
  rw [hDiff, hInter] at hDecomp
  linarith [hCutoffReal, hHitReal, hDecomp]

/-- Helper for Exercise 21.3.1: the same negated closed-cutoff mass can be rewritten entirely in
the single `gaussianReal x T` spelling as a right tail minus a left tail. -/
theorem negatedLowerSurvival_terminalBelowCutoff_eq_twoSidedTailLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T)
    {m : ℕ} (hm : 1 ≤ m) :
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩
        {ω | Bneg T ω ≤ x - ((m : ℝ) * a)}) =
      (gaussianReal x T).real (Set.Ici ((m : ℝ) * a)) -
        (gaussianReal x T).real (Set.Iic (-((m : ℝ) * a))) := by
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  have hMap :
      (gaussianReal (0 : ℝ) T).map (fun z : ℝ ↦ x - z) = gaussianReal x T := by
    -- Proof comment: reflecting a centered Gaussian through `x / 2` produces the shifted law
    -- `gaussianReal x T`.
    simpa using gaussianReal_map_const_sub (μ := (0 : ℝ)) (v := T) (y := x)
  have hTailReflect :
      (gaussianReal 0 T).real (Set.Ici (x + ((m : ℝ) * a))) =
        (gaussianReal x T).real (Set.Iic (-((m : ℝ) * a))) := by
    rw [← hMap]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext z
    constructor <;> intro hz <;> linarith
  -- Proof comment: first use the existing reflected closed-tail formula, then transport the
  -- `gaussianReal 0 T` upper tail through the affine reflection map so both tails live on the
  -- same `gaussianReal x T` measure.
  linarith [negatedLowerSurvival_terminalBelowCutoffRealLocal
    (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa)
    (T := T) (hT := hT) (m := m) hm, hTailReflect]

/-- Helper for Exercise 21.3.1: consecutive closed cutoffs on the negated survival branch differ
by exactly the odd shell coefficient already normalized by
`negatedLowerSurvival_terminalWindow_eq_shellDifferenceLocal`. -/
theorem negatedLowerSurvival_cutoffStep_eq_shellDifferenceLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) (k : ℕ) :
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    let cutoffMass : ℕ → ℝ := fun m ↦
      μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩
        {ω | Bneg T ω ≤ x - ((m : ℝ) * a)})
    cutoffMass (2 * k + 1) - cutoffMass (2 * k + 2) =
      shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  let survive : Set Ω := {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω}
  let cutoffMass : ℕ → ℝ := fun m ↦
    μ.real (survive ∩ {ω | Bneg T ω ≤ x - ((m : ℝ) * a)})
  let Sodd : Set Ω := survive ∩ {ω | Bneg T ω ≤ x - (((2 * k + 1 : ℕ) : ℝ) * a)}
  let Seven : Set Ω := survive ∩ {ω | Bneg T ω ≤ x - (((2 * k + 2 : ℕ) : ℝ) * a)}
  let window : Set Ω :=
    {ω |
      Bneg T ω ∈
        Set.Ioc
          (x - (((2 * k + 2 : ℕ) : ℝ) * a))
          (x - (((2 * k + 1 : ℕ) : ℝ) * a))}
  let hit : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T}
  have hBneg : IsBrownianMotion μ Bneg := neg_isBrownianMotion hW
  have hHitNull : NullMeasurableSet hit μ := by
    let cutoffTop : Set Ω := {ω | hittingAfter Bneg ({x} : Set ℝ) 0 ω ≤ T ∧ Bneg T ω ≤ x}
    let above : Set Ω := {ω | x < Bneg T ω}
    have hCutoffTopNull : NullMeasurableSet cutoffTop μ := by
      -- Proof comment: the hit event below the barrier `x` is null measurable on the negated
      -- path by the same upper-hit cutoff package used elsewhere in the file.
      simpa [cutoffTop, Bneg] using
        upperHitTerminalBelow_nullMeasurableLocal
          (μ := μ) (W := Bneg) (hW := hBneg) (b := x) (y := x) (T := T)
    have hAboveNull : NullMeasurableSet above μ := by
      -- Proof comment: the complementary terminal-above branch is measurable from the terminal
      -- Brownian marginal.
      exact ((hBneg.stronglyMeasurable T).measurable measurableSet_Ioi).nullMeasurableSet
    have hHitEq : hit = cutoffTop ∪ above := by
      ext ω
      simp [hit, cutoffTop, above, le_or_lt]
    rw [hHitEq]
    exact hCutoffTopNull.union hAboveNull
  have hSevenEq :
      Seven = {ω | Bneg T ω ≤ x - (((2 * k + 2 : ℕ) : ℝ) * a)} \ hit := by
    ext ω
    simp [Seven, survive, hit, and_left_comm, and_assoc, not_le]
  have hSevenNull : NullMeasurableSet Seven μ := by
    have hCutoffNull :
        NullMeasurableSet {ω | Bneg T ω ≤ x - (((2 * k + 2 : ℕ) : ℝ) * a)} μ := by
      exact
        ((hBneg.stronglyMeasurable T).measurable measurableSet_Iic).nullMeasurableSet
    rw [hSevenEq]
    exact hCutoffNull.diff hHitNull
  have hSevenSubset : Seven ⊆ Sodd := by
    intro ω hω
    refine ⟨hω.1, ?_⟩
    exact le_trans hω.2 (by nlinarith)
  have hInter : Sodd ∩ Seven = Seven := by
    ext ω
    constructor
    · intro hω
      exact hω.2
    · intro hω
      exact ⟨hSevenSubset hω, hω⟩
  have hDiff :
      Sodd \ Seven = survive ∩ window := by
    ext ω
    simp [Sodd, Seven, survive, window, and_left_comm, and_assoc, not_le]
  have hWindowReal :
      μ.real (survive ∩ window) =
        shiftedStripMass x a T (2 * k + 1 : ℤ) -
          shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
    -- Proof comment: the difference between two consecutive closed cutoffs is exactly the odd
    -- terminal window already normalized to the shell difference.
    simpa [survive, window, Bneg] using
      negatedLowerSurvival_terminalWindow_eq_shellDifferenceLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT k
  have hDecomp :=
    MeasureTheory.measureReal_inter_add_diff₀
      (μ := μ) (s := Sodd) (t := Seven) hSevenNull (measure_ne_top μ _)
  -- Proof comment: decompose the odd closed cutoff into the deeper even cutoff plus the single
  -- odd terminal window, then substitute the one-window shell identity.
  rw [hInter, hDiff] at hDecomp
  have hOdd :
      cutoffMass (2 * k + 1) = μ.real Sodd := by
    rfl
  have hEven :
      cutoffMass (2 * k + 2) = μ.real Seven := by
    rfl
  linarith [hWindowReal, hOdd, hEven, hDecomp]

/-- Helper for Exercise 21.3.1: once the odd correction prefix is normalized by `2`, advancing
from shell `M` to shell `M + 1` subtracts exactly the next odd reflected shell difference. -/
theorem upperLossHalfError_stepLocal
    {x a : ℝ} {T : NNReal} (upperLossMass : ℝ) (M : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let halfErr : ℕ → ℝ := fun N ↦
      (upperLossMass - (∑ n ∈ Finset.range (2 * N + 1), correction n)) / 2
    halfErr (M + 1) =
      halfErr M -
        (shiftedStripMass x a T (2 * M + 1 : ℤ) -
          shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let halfErr : ℕ → ℝ := fun N ↦
    (upperLossMass - (∑ n ∈ Finset.range (2 * N + 1), correction n)) / 2
  have hOdd :
      correction (2 * M + 1) =
        2 * (shiftedStripMass x a T (2 * M + 1 : ℤ) -
          shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
    have hNegIndex :
        (-((((2 * M + 1 : ℕ) : ℤ)) + 1)) = -(2 * M + 2 : ℤ) := by
      omega
    -- Proof comment: the odd correction index `2 * M + 1` is exactly the next odd reflected
    -- shell in the normalized error sequence.
    simp [correction, hNegIndex]
  have hEven : correction (2 * M + 2) = 0 := by
    -- Proof comment: the companion even correction term vanishes by definition.
    simp [correction]
  have hPrefixStep :
      (∑ n ∈ Finset.range (2 * (M + 1) + 1), correction n) =
        (∑ n ∈ Finset.range (2 * M + 1), correction n) +
          2 * (shiftedStripMass x a T (2 * M + 1 : ℤ) -
            shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
    -- Proof comment: extending the odd correction prefix by one shell adds only the next odd
    -- reflected shell, because the intervening even term is zero.
    calc
      ∑ n ∈ Finset.range (2 * (M + 1) + 1), correction n
          = (∑ n ∈ Finset.range (2 * M + 2), correction n) +
              correction (2 * M + 2) := by
                rw [show 2 * (M + 1) + 1 = 2 * M + 2 + 1 by ring, Finset.sum_range_succ]
      _ = (∑ n ∈ Finset.range (2 * M + 1), correction n) +
            correction (2 * M + 1) + correction (2 * M + 2) := by
              rw [show 2 * M + 2 = 2 * M + 1 + 1 by ring, Finset.sum_range_succ]
              ring
      _ = (∑ n ∈ Finset.range (2 * M + 1), correction n) +
            2 * (shiftedStripMass x a T (2 * M + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
              rw [hOdd, hEven]
              ring
  -- Proof comment: dividing the one-shell prefix update by `2` produces the half-error
  -- recurrence used by the remaining candidate-remainder assembly.
  dsimp [halfErr]
  linarith [hPrefixStep]

/-- Helper for Exercise 21.3.1: any odd-prefix correction decomposition of the form
`correctionPrefix = 2 * (oddSlicePrefix - reflectedNegativePrefix)` identifies the normalized
half-error with the corresponding explicit candidate remainder. -/
theorem halfErr_eq_candidate_of_prefixDecompositionLocal
    {upperLossMass : ℝ} {correction oddSliceMass reflectedNegativeMass : ℕ → ℝ}
    (hPrefix :
      ∀ M : ℕ,
        ∑ n ∈ Finset.range (2 * M + 1), correction n =
          2 * ((∑ k ∈ Finset.range M, oddSliceMass k) -
            ∑ k ∈ Finset.range M, reflectedNegativeMass k))
    (M : ℕ) :
    let halfErr : ℕ → ℝ := fun N ↦
      (upperLossMass - (∑ n ∈ Finset.range (2 * N + 1), correction n)) / 2
    let cand : ℕ → ℝ := fun N ↦
      upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
        ∑ k ∈ Finset.range N, reflectedNegativeMass k
    halfErr M = cand M := by
  let halfErr : ℕ → ℝ := fun N ↦
    (upperLossMass - (∑ n ∈ Finset.range (2 * N + 1), correction n)) / 2
  let cand : ℕ → ℝ := fun N ↦
    upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
      ∑ k ∈ Finset.range N, reflectedNegativeMass k
  have hPrefixM := hPrefix M
  -- Proof comment: substitute the odd-prefix decomposition once and simplify the resulting scalar
  -- normalization of the half-error.
  dsimp [halfErr, cand]
  linarith

/-- Helper for Exercise 21.3.1: once the one-shell difference is identified, the explicit
candidate remainder advances by subtracting exactly that shell. -/
theorem candidate_step_of_shellDifferenceLocal
    {upperLossMass : ℝ} {oddSliceMass reflectedNegativeMass shell : ℕ → ℝ}
    (hShell : ∀ M : ℕ, oddSliceMass M - reflectedNegativeMass M = shell M)
    (M : ℕ) :
    let cand : ℕ → ℝ := fun N ↦
      upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
        ∑ k ∈ Finset.range N, reflectedNegativeMass k
    cand (M + 1) = cand M - shell M := by
  let cand : ℕ → ℝ := fun N ↦
    upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
      ∑ k ∈ Finset.range N, reflectedNegativeMass k
  have hShellM := hShell M
  -- Proof comment: adjoining one more shell only changes the candidate by the new odd positive
  -- slice and the new reflected negative slice, whose difference is the declared shell term.
  dsimp [cand]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  linarith

/-- Helper for Exercise 21.3.1: if the one-shell candidate decrement has been rewritten as the
difference of two consecutive closed cutoffs, then the whole candidate is the initial half-mass
minus the corresponding closed-cutoff prefix. -/
theorem candidate_eq_closedCutoffPrefix_of_shellDecompositionLocal
    {upperLossMass : ℝ} {oddSliceMass reflectedNegativeMass : ℕ → ℝ}
    {closedCutoffMass : ℕ → ℝ}
    (hClosedShell :
      ∀ M : ℕ,
        oddSliceMass M - reflectedNegativeMass M =
          closedCutoffMass (2 * M + 1) - closedCutoffMass (2 * M + 2))
    (M : ℕ) :
    let cand : ℕ → ℝ := fun N ↦
      upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
        ∑ k ∈ Finset.range N, reflectedNegativeMass k
    cand M =
      upperLossMass / 2 -
        ∑ k ∈ Finset.range M,
          (closedCutoffMass (2 * k + 1) - closedCutoffMass (2 * k + 2)) := by
  let cand : ℕ → ℝ := fun N ↦
    upperLossMass / 2 - (∑ k ∈ Finset.range N, oddSliceMass k) +
      ∑ k ∈ Finset.range N, reflectedNegativeMass k
  have hSum :
      ∑ k ∈ Finset.range M, (oddSliceMass k - reflectedNegativeMass k) =
        ∑ k ∈ Finset.range M,
          (closedCutoffMass (2 * k + 1) - closedCutoffMass (2 * k + 2)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact hClosedShell k
  -- Proof comment: first rewrite the candidate as the initial half-mass minus the summed shell
  -- differences, then substitute the closed-cutoff normalization termwise.
  dsimp [cand]
  calc
    upperLossMass / 2 - (∑ k ∈ Finset.range M, oddSliceMass k) +
        ∑ k ∈ Finset.range M, reflectedNegativeMass k =
      upperLossMass / 2 -
        ((∑ k ∈ Finset.range M, oddSliceMass k) -
          ∑ k ∈ Finset.range M, reflectedNegativeMass k) := by
            ring
    _ =
      upperLossMass / 2 -
        ∑ k ∈ Finset.range M, (oddSliceMass k - reflectedNegativeMass k) := by
          rw [← Finset.sum_sub_distrib]
    _ =
      upperLossMass / 2 -
        ∑ k ∈ Finset.range M,
          (closedCutoffMass (2 * k + 1) - closedCutoffMass (2 * k + 2)) := by
            rw [hSum]

/-- Helper for Exercise 21.3.1: once a candidate remainder is split into a nonnegative cutoff
tail and a nonnegative reflected closed-cutoff tail, the desired two-strip window follows by
componentwise comparison. -/
theorem candidate_nonneg_and_le_twoStrips_of_componentBoundsLocal
    {cand cutoffTail closedTail posStrip negStrip : ℝ}
    (hDecomp : cand = cutoffTail + closedTail)
    (hCutoff : 0 ≤ cutoffTail ∧ cutoffTail ≤ posStrip)
    (hClosed : 0 ≤ closedTail ∧ closedTail ≤ negStrip) :
    0 ≤ cand ∧ cand ≤ posStrip + negStrip := by
  -- Proof comment: after the candidate is written as the sum of the two surviving tails, both
  -- the lower bound and the two-strip upper bound are immediate scalar assemblies.
  constructor
  · linarith [hDecomp, hCutoff.1, hClosed.1]
  · linarith [hDecomp, hCutoff.2, hClosed.2]

/-- Helper for Exercise 21.3.1: the source-facing Brownian owner theorem is the odd
correction-prefix window on `upperLoss`, whose remainder should be the surviving reflected tail
between the next positive strip and its reflected negative companion. -/
theorem intervalPairShellOddPrefix_boundaryWindowOwnerLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) (N : ℕ) :
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    (boundaryTail (2 * N + 1) -
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
        interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ∧
      interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ≤
        boundaryTail (2 * N + 1)) := by
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hUpper :
      0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
        μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
    let cutoff : ℝ → Set Ω := fun y ↦
      {ω | hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧ W T ω ≤ y}
    let cutoffTop : Set Ω := cutoff (a - x)
    let baseSlice : Set Ω := cutoffTop \ cutoff (-x)
    let above : Set Ω := {ω | a - x < W T ω}
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let oddSliceMass : ℕ → ℝ := fun k ↦
      μ.real (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
        cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))
    let reflectedNegativeMass : ℕ → ℝ := fun k ↦
      μ.real
        {ω |
          x + W T ω ∈
            Set.Ioc (((-1 : ℝ) - (2 * k + 1 : ℝ)) * a) (-(((2 * k + 1 : ℕ) : ℝ) * a))}
    let evenSlice : ℕ → Set Ω := fun k ↦
      {ω |
        hittingAfter W ({a - x} : Set ℝ) 0 ω ≤ T ∧
          W T ω ∈
            Set.Ioc ((-((2 * k + 1 : ℕ) : ℝ) * a) - x) ((-((2 * k : ℕ) : ℝ) * a) - x)}
    have ha : 0 < a := by
      linarith
    have hCorrectionPrefix :
        ∑ n ∈ Finset.range (2 * N + 1), correction n =
          2 * ((∑ k ∈ Finset.range N, oddSliceMass k) -
            ∑ k ∈ Finset.range N, reflectedNegativeMass k) := by
      have hOddPrefix :
          ∑ k ∈ Finset.range N, oddShell k =
            ∑ n ∈ Finset.range (2 * N + 1), correction n := by
        -- Proof comment: first rewrite the odd correction prefix through the odd reflected shells.
        simpa [oddShell, correction] using
          oddShellPrefix_eq_upperLossCorrectionOddPrefixLocal
            (x := x) (a := a) (T := T) N
      have hSlicePrefix :
          ∑ k ∈ Finset.range N, oddShell k =
            2 * ((∑ k ∈ Finset.range N, oddSliceMass k) -
              ∑ k ∈ Finset.range N, reflectedNegativeMass k) := by
        -- Proof comment: then rewrite the same odd-shell prefix as cutoff slices minus reflected
        -- negative slices.
        simpa [oddShell, cutoff, oddSliceMass, reflectedNegativeMass] using
          oddShellPrefix_eq_upperHitSlicePrefix_sub_reflectedNegativePrefixLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) N
      linarith
    have hCorrectionPrefixAll :
        ∀ M : ℕ,
          ∑ n ∈ Finset.range (2 * M + 1), correction n =
            2 * ((∑ k ∈ Finset.range M, oddSliceMass k) -
              ∑ k ∈ Finset.range M, reflectedNegativeMass k) := by
      intro M
      have hOddPrefix :
          ∑ k ∈ Finset.range M, oddShell k =
            ∑ n ∈ Finset.range (2 * M + 1), correction n := by
        -- Proof comment: first rewrite each odd correction prefix through the odd reflected-shell
        -- normalization, now with a variable shell index `M`.
        simpa [oddShell, correction] using
          oddShellPrefix_eq_upperLossCorrectionOddPrefixLocal
            (x := x) (a := a) (T := T) M
      have hSlicePrefix :
          ∑ k ∈ Finset.range M, oddShell k =
            2 * ((∑ k ∈ Finset.range M, oddSliceMass k) -
              ∑ k ∈ Finset.range M, reflectedNegativeMass k) := by
        -- Proof comment: the same odd-shell prefix is the difference between the positive
        -- upper-hit slices and their reflected negative companions.
        simpa [oddShell, cutoff, oddSliceMass, reflectedNegativeMass] using
          oddShellPrefix_eq_upperHitSlicePrefix_sub_reflectedNegativePrefixLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) M
      linarith
    have hUpperLossSplit :
        upperLoss = (upperLoss ∩ cutoffTop) ∪ (upperLoss ∩ above) := by
      -- Proof comment: split `upperLoss` into the top cutoff branch and the terminal-above
      -- branch before assembling the finite remainder.
      simpa [upperLoss, cutoffTop, above, cutoff] using
        upperLoss_eq_inter_cutoffTop_union_inter_terminalAboveLocal
          (W := W) (x := x) (a := a) (T := T)
    have hCutoffTelescopes :
        μ.real (cutoff (a - x)) - (∑ k ∈ Finset.range N, oddSliceMass k) =
          (∑ k ∈ Finset.range N,
              μ.real (cutoff ((-((2 * k : ℕ) : ℝ) * a) - x) \
                cutoff ((-((2 * k + 1 : ℕ) : ℝ) * a) - x))) +
            μ.real (cutoff ((((1 : ℝ) - (2 * N : ℕ)) * a) - x)) := by
      -- Proof comment: the upper-hit cutoff bookkeeping is already packaged as a telescope over
      -- odd and even shells plus one deeper cutoff tail.
      simpa [cutoff, oddSliceMass] using
        (upperHitCutoffOddPrefix_telescopesLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
          (T := T)) N
    have hEvenZero :
        ∀ k : ℕ, μ.real (upperLoss ∩ evenSlice k) = 0 := by
      intro k
      -- Proof comment: every even cutoff slice lies terminally at or below `-x`, so it vanishes
      -- on `upperLoss`.
      simpa [upperLoss, evenSlice] using
        upperLossEvenSlice_real_eq_zeroLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
          (T := T) k
    have hOddZero :
        ∀ k : ℕ, 1 ≤ k → μ.real (upperLoss ∩
          (cutoff ((((2 : ℝ) - (2 * k + 1 : ℕ)) * a) - x) \
            cutoff ((((1 : ℝ) - (2 * k + 1 : ℕ)) * a) - x))) = 0 := by
      intro k hk
      -- Proof comment: after the cutoff-side rewrite `upperLoss = lower` on odd slices, every
      -- odd slice below the base strip vanishes for the same reason as on lower-barrier survival.
      simpa [upperLoss, cutoff] using
        upperLossOddSlice_real_eq_zero_of_one_leLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
          (T := T) k hk
    have hNextUpper :
        μ.real (cutoff ((((2 : ℝ) - (2 * N + 1 : ℕ)) * a) - x) \
            cutoff ((((1 : ℝ) - (2 * N + 1 : ℕ)) * a) - x)) =
          shiftedStripMass x a T (2 * N + 1 : ℤ) := by
      -- Proof comment: the next uncovered positive cutoff shell is already in the target strip
      -- normal form.
      simpa [cutoff] using
        nextUpperHitShell_eq_shiftedStripMassLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
          (T := T) (hT := _hT) N
    have hNextReflected :
        reflectedNegativeMass N = shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
      -- Proof comment: the reflected negative remainder shell is already normalized to the
      -- companion shifted strip.
      simpa [reflectedNegativeMass] using
        nextReflectedNegativeShell_eq_shiftedStripMassLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (T := T) (hT := _hT) N
    have hUpperLossMeasureSplit :
        μ.real upperLoss =
          μ.real (upperLoss ∩ cutoffTop) + μ.real (upperLoss ∩ above) := by
      -- Proof comment: split `upperLoss` at the measurable terminal-above branch so the cutoff
      -- part and the reflected-above part can be assembled independently.
      simpa [upperLoss, cutoffTop, above, cutoff] using
        upperLoss_real_eq_inter_cutoffTop_add_inter_terminalAboveLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (T := T)
    have hUpperLossCutoffRewrite :
        μ.real (upperLoss ∩ cutoffTop) =
          μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ cutoffTop) := by
      -- Proof comment: on every upper-hit cutoff, `upperLoss` is just lower-barrier survival, so
      -- the cutoff branch can be rewritten before telescoping.
      simpa [upperLoss, cutoffTop, cutoff] using
        upperLoss_inter_cutoff_real_eq_lowerSurvival_inter_cutoffLocal
          (μ := μ) (W := W) (x := x) (a := a) (T := T) (a - x)
    have hUpperLossCutoffBelowZero :
        μ.real (upperLoss ∩ cutoff (-x)) = 0 := by
      -- Proof comment: the part of `upperLoss` whose terminal value is already at or below `-x`
      -- is impossible by lower-barrier survival.
      simpa [upperLoss, cutoff] using
        upperLossCutoffBelowLowerBarrier_real_eq_zeroLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (T := T)
    have hUpperLossCutoffBaseSlice :
        μ.real (upperLoss ∩ cutoffTop) = μ.real (upperLoss ∩ baseSlice) := by
      -- Proof comment: splitting `cutoffTop` at the geometric threshold `-x` removes the null
      -- lower piece, so only the base strip `Set.Ioc (-x) (a - x)` survives on `upperLoss`.
      simpa [upperLoss, cutoffTop, cutoff, baseSlice] using
        upperLoss_inter_cutoffTop_real_eq_baseSliceLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
          (T := T)
    have hUpperLossAboveRewrite :
        μ.real (upperLoss ∩ above) =
          μ.real ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ above) := by
      -- Proof comment: above the upper barrier at time `T`, the upper hit is already forced, so
      -- the branch is measured purely by lower-barrier survival.
      simpa [upperLoss, above] using
        upperLoss_inter_terminalAbove_real_eq_lowerSurvival_inter_terminalAboveLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hxa := _hxa) (T := T)
    have hAboveNegPath :
        ({ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} ∩ above) =
          ({ω | T < hittingAfter (fun t ω ↦ -W t ω) ({x} : Set ℝ) 0 ω} ∩
            {ω | -(W T ω) < x - a}) := by
      -- Proof comment: negating the path converts the hard terminal-above branch into a one-sided
      -- upper-barrier survival problem at level `x`.
      simpa [above] using
        lowerSurvival_inter_terminalAbove_eq_negUpperSurvival_terminalBelowLocal
          (W := W) (x := x) (a := a) (T := T)
    let halfErr : ℕ → ℝ := fun M ↦
      (μ.real upperLoss - (∑ n ∈ Finset.range (2 * M + 1), correction n)) / 2
    let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
    let posCutoffRemainder : ℕ → ℝ := fun M ↦
      μ.real (cutoff (a - x)) - ∑ k ∈ Finset.range M, oddSliceMass k
    let negClosedCutoffMass : ℕ → ℝ := fun m ↦
      μ.real ({ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω} ∩
        {ω | Bneg T ω ≤ x - ((m : ℝ) * a)})
    have hUpperLossAboveClosed :
        μ.real (upperLoss ∩ above) = negClosedCutoffMass 1 := by
      -- Proof comment: the strict terminal-above branch is now transported once and for all to
      -- the base closed cutoff on the negated path.
      simpa [negClosedCutoffMass, Bneg] using
        upperLoss_inter_terminalAbove_real_eq_negatedClosedCutoffBaseLocal
          (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hxa := _hxa)
          (T := T) (hT := _hT)
    have hHalfErrStep :
        ∀ M : ℕ,
          halfErr (M + 1) =
            halfErr M -
              (shiftedStripMass x a T (2 * M + 1 : ℤ) -
                shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
      intro M
      -- Proof comment: the normalized odd-prefix recurrence is now isolated as a file-local
      -- helper, so the owner theorem can focus only on matching it with the right remainder.
      simpa [correction, halfErr] using
        upperLossHalfError_stepLocal
          (x := x) (a := a) (T := T) (upperLossMass := μ.real upperLoss) M
    have hPosCutoffRemainder_eq :
        ∀ M : ℕ,
          posCutoffRemainder M =
            (∑ k ∈ Finset.range M, evenSlice k) +
              μ.real (cutoff ((((1 : ℝ) - (2 * M : ℕ)) * a) - x)) := by
      intro M
      -- Proof comment: the cutoff telescope isolates the positive geometric remainder as the
      -- even-shell prefix plus one deeper cutoff tail.
      simpa [posCutoffRemainder] using hCutoffTelescopes M
    have hPosCutoffRemainder_nonneg :
        ∀ M : ℕ, 0 ≤ posCutoffRemainder M := by
      intro M
      have hEvenNonneg :
          0 ≤ ∑ k ∈ Finset.range M, evenSlice k := by
        refine Finset.sum_nonneg ?_
        intro k hk
        -- Proof comment: every real-valued measure term in the cutoff telescope is nonnegative.
        exact
          MeasureTheory.measureReal_nonneg
            (μ := μ)
            (s := cutoff ((-((2 * k : ℕ) : ℝ) * a) - x) \
              cutoff ((-((2 * k + 1 : ℕ) : ℝ) * a) - x))
      have hTailNonneg :
          0 ≤ μ.real (cutoff ((((1 : ℝ) - (2 * M : ℕ)) * a) - x)) := by
        exact
          MeasureTheory.measureReal_nonneg
            (μ := μ)
            (s := cutoff ((((1 : ℝ) - (2 * M : ℕ)) * a) - x))
      -- Proof comment: the telescope representation is a sum of nonnegative cutoff masses.
      linarith [hPosCutoffRemainder_eq M, hEvenNonneg, hTailNonneg]
    have hClosedShell :
        ∀ M : ℕ,
          oddSliceMass M - reflectedNegativeMass M =
            negClosedCutoffMass (2 * M + 1) - negClosedCutoffMass (2 * M + 2) := by
      intro M
      have hOddShell :
          oddSliceMass M - reflectedNegativeMass M =
            shiftedStripMass x a T (2 * M + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * M + 2 : ℤ)) := by
        -- Proof comment: the odd cutoff slice minus its reflected negative companion is already
        -- the canonical shell difference.
        simpa [cutoff, oddSliceMass, reflectedNegativeMass] using
          oddShell_eq_upperHitSlice_sub_reflectedNegativeLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) M
      have hClosedStep :
          negClosedCutoffMass (2 * M + 1) - negClosedCutoffMass (2 * M + 2) =
            shiftedStripMass x a T (2 * M + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * M + 2 : ℤ)) := by
        -- Proof comment: the same shell difference is also the one-step decrement between the
        -- consecutive closed cutoffs on the negated survival branch.
        simpa [negClosedCutoffMass, Bneg] using
          negatedLowerSurvival_cutoffStep_eq_shellDifferenceLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) M
      linarith
    -- Route correction: the interval-side theorem is now fully transported to the upper-loss
    -- normal form, but the previously planned bridge
    -- `μ.real (lower ∩ oddSlice) = oddSliceMass - reflectedNegativeMass` is false for `k ≥ 1`:
    -- `lowerSurvivalOddSlice_real_eq_zero_of_one_leLocal` and the upgraded
    -- `upperLossOddSlice_real_eq_zero_of_one_leLocal` show those odd slices already end at or
    -- below `-x`. The cutoff side is now reduced to the base strip by
    -- `hUpperLossCutoffBaseSlice`, and the terminal-above branch is now normalized by
    -- `hUpperLossAboveRewrite` and `hAboveNegPath` to a one-sided survival problem for the
    -- negated path. The negated branch now has both the closed-cutoff normalization
    -- `negatedLowerSurvival_terminalBelowCutoffRealLocal` and the consecutive-step identity
    -- `negatedLowerSurvival_cutoffStep_eq_shellDifferenceLocal`, and `hHalfErrStep` now isolates
    -- the exact one-shell recurrence of the normalized odd-prefix error. The only remaining
    -- blocker is the finite tail assembly that identifies a candidate remainder satisfying the
    -- same recurrence and base value by coupling those cutoff steps with the cutoff telescope on
    -- `W`.
    let cand : ℕ → ℝ := fun M ↦
      μ.real upperLoss / 2 - (∑ k ∈ Finset.range M, oddSliceMass k) +
        ∑ k ∈ Finset.range M, reflectedNegativeMass k
    have hCandZero : halfErr 0 = cand 0 := by
      -- Proof comment: at `M = 0` both the normalized odd-prefix error and the explicit
      -- candidate reduce to half of the full `upperLoss` mass.
      simp [halfErr, cand]
    have hHalfErrEqCand : ∀ M : ℕ, halfErr M = cand M := by
      intro M
      -- Proof comment: the generic prefix-to-candidate bridge applies once the odd correction
      -- prefix is normalized by the proved upper-hit slice minus reflected-negative identity.
      simpa [halfErr, cand] using
        halfErr_eq_candidate_of_prefixDecompositionLocal
          (upperLossMass := μ.real upperLoss) (correction := correction)
          (oddSliceMass := oddSliceMass) (reflectedNegativeMass := reflectedNegativeMass)
          hCorrectionPrefixAll M
    have hCandStep :
        ∀ M : ℕ,
          cand (M + 1) =
            cand M -
              (shiftedStripMass x a T (2 * M + 1 : ℤ) -
                shiftedStripMass x a T (-(2 * M + 2 : ℤ))) := by
      intro M
      have hShell :
          oddSliceMass M - reflectedNegativeMass M =
            shiftedStripMass x a T (2 * M + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * M + 2 : ℤ)) := by
        -- Proof comment: the one-step candidate decrement is exactly the normalized odd shell.
        simpa [cutoff, oddSliceMass, reflectedNegativeMass] using
          oddShell_eq_upperHitSlice_sub_reflectedNegativeLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) M
      -- Proof comment: after isolating the shell identity, the candidate recurrence is the
      -- generic one-step update for a finite prefix remainder.
      simpa [cand] using
        candidate_step_of_shellDifferenceLocal
          (upperLossMass := μ.real upperLoss) (oddSliceMass := oddSliceMass)
          (reflectedNegativeMass := reflectedNegativeMass)
          (shell := fun k ↦
            shiftedStripMass x a T (2 * k + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
          hShell M
    have hCandClosedPrefix :
        ∀ M : ℕ,
          cand M =
            μ.real upperLoss / 2 -
              ∑ k ∈ Finset.range M,
                (negClosedCutoffMass (2 * k + 1) - negClosedCutoffMass (2 * k + 2)) := by
      intro M
      -- Proof comment: package the closed-cutoff normal form once so the remaining blocker is
      -- purely the geometric coupling between the cutoff-side remainder and the negated tail.
      simpa [cand] using
        candidate_eq_closedCutoffPrefix_of_shellDecompositionLocal
          (upperLossMass := μ.real upperLoss) (oddSliceMass := oddSliceMass)
          (reflectedNegativeMass := reflectedNegativeMass)
          (closedCutoffMass := negClosedCutoffMass) hClosedShell M
    have hCandBounds :
        ∀ M : ℕ,
          0 ≤ cand M ∧
            cand M ≤
              shiftedStripMass x a T (2 * M + 1 : ℤ) +
                shiftedStripMass x a T (-(2 * M + 2 : ℤ)) := by
      intro M
      let closedResidual : ℝ := cand (M + 1) - reflectedNegativeMass M
      have hShellNonneg :
          ∀ k : ℕ, 0 ≤ oddSliceMass k - reflectedNegativeMass k := by
        intro k
        -- Proof comment: each odd upper-hit slice dominates its reflected negative companion, so
        -- the corresponding shell difference is already nonnegative before any candidate-tail
        -- assembly.
        simpa [cutoff, oddSliceMass, reflectedNegativeMass] using
          upperHitSlice_sub_reflectedNegative_nonnegLocal
            (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
            (T := T) (hT := _hT) k
      have hClosedStepNonneg :
          ∀ k : ℕ,
            0 ≤ negClosedCutoffMass (2 * k + 1) - negClosedCutoffMass (2 * k + 2) := by
        intro k
        -- Proof comment: transport the shell nonnegativity through the closed-cutoff
        -- normalization, so the negated closed cutoffs decrease across each odd/even step.
        linarith [hClosedShell k, hShellNonneg k]
      have hCandAnti :
          ∀ k : ℕ, cand (k + 1) ≤ cand k := by
        intro k
        have hShellNonneg' :
            0 ≤ shiftedStripMass x a T (2 * k + 1 : ℤ) -
              shiftedStripMass x a T (-(2 * k + 2 : ℤ)) := by
          -- Proof comment: the canonical odd shell is a nonnegative lower-barrier shell
          -- difference in shifted-strip normal form.
          exact
            shellDifference_nonnegLocal
              (x := x) (a := a) _hx.le (by linarith) (T := T) _hT (2 * k + 1)
        -- Proof comment: once the shell decrement is known to be nonnegative, the explicit
        -- candidate can only decrease when one more odd shell is removed.
        linarith [hCandStep k, hShellNonneg']
      have hCutoffComponent :
          0 ≤
              μ.real
                (cutoff ((((2 : ℝ) - (2 * M + 1 : ℕ)) * a) - x) \
                  cutoff ((((1 : ℝ) - (2 * M + 1 : ℕ)) * a) - x)) ∧
            μ.real
                (cutoff ((((2 : ℝ) - (2 * M + 1 : ℕ)) * a) - x) \
                  cutoff ((((1 : ℝ) - (2 * M + 1 : ℕ)) * a) - x)) ≤
              shiftedStripMass x a T (2 * M + 1 : ℤ) := by
        constructor
        · -- Proof comment: the extracted positive shell is a real-valued measure term, so it is
          -- nonnegative before any transport to the strip normal form.
          exact
            MeasureTheory.measureReal_nonneg
              (μ := μ)
              (s := cutoff ((((2 : ℝ) - (2 * M + 1 : ℕ)) * a) - x) \
                cutoff ((((1 : ℝ) - (2 * M + 1 : ℕ)) * a) - x))
        · -- Proof comment: this positive shell already is the next shifted strip mass, so the
          -- componentwise upper bound is equality.
          simpa [hNextUpper]
      have hCandShellDecomp :
          cand M =
            μ.real
                (cutoff ((((2 : ℝ) - (2 * M + 1 : ℕ)) * a) - x) \
                  cutoff ((((1 : ℝ) - (2 * M + 1 : ℕ)) * a) - x)) +
              closedResidual := by
        -- Proof comment: peel off exactly one odd cutoff shell from `cand M`, leaving only the
        -- residual `cand (M + 1) - reflectedNegativeMass M`.
        dsimp [closedResidual]
        linarith [hCandStep M, hNextUpper, hNextReflected]
      have hClosedResidualRewrite :
          closedResidual =
            cand M -
              μ.real
                (cutoff ((((2 : ℝ) - (2 * M + 1 : ℕ)) * a) - x) \
                  cutoff ((((1 : ℝ) - (2 * M + 1 : ℕ)) * a) - x)) := by
        -- Proof comment: restate the residual in the exact shell-extracted normal form needed for
        -- the final reflected-tail estimate.
        linarith [hCandShellDecomp]
      have hClosedResidualClosedPrefix :
          closedResidual =
            μ.real upperLoss / 2 -
              ∑ k ∈ Finset.range (M + 1),
                (negClosedCutoffMass (2 * k + 1) - negClosedCutoffMass (2 * k + 2)) -
              reflectedNegativeMass M := by
        -- Proof comment: rewrite the residual completely into the closed-cutoff prefix spelling so
        -- the only open step is the reflected closed-residual estimate.
        dsimp [closedResidual]
        rw [hCandClosedPrefix (M + 1)]
      have hClosedResidualAsClosedCutoffRemainder :
          closedResidual =
            μ.real upperLoss / 2 -
              ∑ k ∈ Finset.range M,
                (negClosedCutoffMass (2 * k + 1) - negClosedCutoffMass (2 * k + 2)) -
              oddSliceMass M := by
        -- Proof comment: expand the last closed-cutoff increment and use the already proved shell
        -- identity to replace that final increment plus the reflected strip by the odd cutoff
        -- shell itself.
        rw [hClosedResidualClosedPrefix, Finset.sum_range_succ]
        linarith [hClosedShell M]
      have hClosedResidualWindowBounds :
          0 ≤ closedResidual ∧ closedResidual ≤ reflectedNegativeMass M := by
        -- Route correction: stop rewriting `closedResidual` into Gaussian two-sided tails here.
        -- The surviving blocker is the event-level comparison showing that, after the positive
        -- cutoff shell is peeled off by `hCandShellDecomp`, the remaining coupled cutoff/negated
        -- remainder is still a nonnegative subset of the reflected negative window whose mass is
        -- `reflectedNegativeMass M`.
        let surviveNeg : Set Ω := {ω | T < hittingAfter Bneg ({x} : Set ℝ) 0 ω}
        let oddWindow : Set Ω :=
          {ω |
            Bneg T ω ∈
              Set.Ioc
                (x - (((2 * M + 2 : ℕ) : ℝ) * a))
                (x - (((2 * M + 1 : ℕ) : ℝ) * a))}
        let deeperCutoff : Set Ω :=
          {ω | Bneg T ω ≤ x - (((2 * M + 2 : ℕ) : ℝ) * a)}
        let reflectedWindow : Set Ω :=
          {ω |
            x + W T ω ∈
              Set.Ioc (((-1 : ℝ) - (2 * M + 1 : ℝ)) * a) (-(((2 * M + 1 : ℕ) : ℝ) * a))}
        have hOddClosedCutoffSplit :
            surviveNeg ∩ {ω | Bneg T ω ≤ x - (((2 * M + 1 : ℕ) : ℝ) * a)} =
              (surviveNeg ∩ oddWindow) ∪ (surviveNeg ∩ deeperCutoff) := by
          -- Proof comment: split the odd closed cutoff on the negated path into the current
          -- odd terminal window and the strictly deeper closed cutoff.
          ext ω
          constructor
          · intro hω
            by_cases hDeeper : Bneg T ω ≤ x - (((2 * M + 2 : ℕ) : ℝ) * a)
            · exact Or.inr ⟨hω.1, hDeeper⟩
            · have hLower :
                x - (((2 * M + 2 : ℕ) : ℝ) * a) < Bneg T ω := lt_of_not_ge hDeeper
              exact Or.inl ⟨hω.1, ⟨hLower, hω.2⟩⟩
          · intro hω
            rcases hω with hω | hω
            · exact ⟨hω.1, hω.2.2⟩
            · refine ⟨hω.1, ?_⟩
              exact le_trans hω.2 (by nlinarith [ha])
        have hOddWindowMass :
            μ.real (surviveNeg ∩ oddWindow) =
              oddSliceMass M - reflectedNegativeMass M := by
          -- Proof comment: the current odd negated terminal window is already the normalized
          -- shell difference between the positive odd slice and its reflected negative companion.
          simpa [surviveNeg, oddWindow, Bneg] using
            negatedLowerSurvival_terminalWindow_eq_shellDifferenceLocal
              (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
              (T := T) (hT := _hT) M
        have hOddClosedCutoffMass :
            negClosedCutoffMass (2 * M + 1) =
              μ.real (surviveNeg ∩ oddWindow) + negClosedCutoffMass (2 * M + 2) := by
          -- Proof comment: combining the consecutive closed-cutoff step with the one-window
          -- shell identity isolates the odd closed cutoff as window mass plus deeper cutoff.
          linarith [hClosedShell M, hOddWindowMass]
        have hClosedResidualAsReflectedDifference :
            ∃ hitCoreWindow : Set Ω,
              NullMeasurableSet hitCoreWindow μ ∧
              hitCoreWindow ⊆ reflectedWindow ∧
              closedResidual = μ.real reflectedWindow - μ.real hitCoreWindow := by
          -- TODO: finish the scalar reflected-window cancellation by introducing the theorem-local
          -- reflected hit slice whose real mass is exactly the part subtracted from
          -- `reflectedWindow`. The remaining blocker is the exact normalization from
          -- `hClosedResidualAsClosedCutoffRemainder` to this reflected difference, together with
          -- the null-measurability package for that reflected hit slice.
          sorry
        have hClosedResidualAsResidualWindow :
            ∃ residualWindow : Set Ω,
              closedResidual = μ.real residualWindow ∧ residualWindow ⊆ reflectedWindow := by
          rcases hClosedResidualAsReflectedDifference with
            ⟨hitCoreWindow, hHitCoreNull, hHitCoreSub, hClosedResidualDiff⟩
          let residualWindow : Set Ω := reflectedWindow \ hitCoreWindow
          have hInter :
              reflectedWindow ∩ hitCoreWindow = hitCoreWindow := by
            -- Proof comment: once the reflected hit slice is known to lie inside
            -- `reflectedWindow`, the intersection in `measureReal_inter_add_diff₀` collapses.
            ext ω
            constructor
            · intro hω
              exact hω.2
            · intro hω
              exact ⟨hHitCoreSub hω, hω⟩
          have hMeasureDiff :
              μ.real residualWindow = μ.real reflectedWindow - μ.real hitCoreWindow := by
            have hDecomp :=
              MeasureTheory.measureReal_inter_add_diff₀
                (μ := μ) (s := reflectedWindow) (t := hitCoreWindow)
                hHitCoreNull (measure_ne_top μ _)
            rw [hInter] at hDecomp
            -- Proof comment: the remaining branch of `reflectedWindow` is exactly the set
            -- difference `reflectedWindow \\ hitCoreWindow`, so its real mass is the difference
            -- of the two reflected masses.
            dsimp [residualWindow] at hDecomp
            linarith
          refine ⟨residualWindow, ?_, Set.diff_subset⟩
          linarith
        rcases hClosedResidualAsResidualWindow with ⟨residualWindow, hResidualEq, hResidualSub⟩
        constructor
        · -- Proof comment: once the residual is realized as a real measure term, its lower bound
          -- is immediate from nonnegativity of `μ.real`.
          simpa [hResidualEq] using
            (MeasureTheory.measureReal_nonneg (μ := μ) (s := residualWindow))
        · have hResidualMono :
              μ.real residualWindow ≤ μ.real reflectedWindow := by
            -- Proof comment: the reflected residual sits inside the full reflected odd window, so
            -- monotonicity of `μ.real` gives the desired upper bound.
            exact
              MeasureTheory.measureReal_mono
                (μ := μ) (s₁ := residualWindow) (s₂ := reflectedWindow) hResidualSub
          simpa [hResidualEq, reflectedWindow, reflectedNegativeMass] using hResidualMono
      have hClosedResidualBounds :
          0 ≤ closedResidual ∧
            closedResidual ≤ shiftedStripMass x a T (-(2 * M + 2 : ℤ)) := by
        constructor
        · exact hClosedResidualWindowBounds.1
        · simpa [hNextReflected] using hClosedResidualWindowBounds.2
      -- Proof comment: once the positive cutoff shell and the reflected residual are both bounded
      -- componentwise, the full two-strip window is a direct scalar assembly.
      exact
        candidate_nonneg_and_le_twoStrips_of_componentBoundsLocal
          hCandShellDecomp hCutoffComponent hClosedResidualBounds
    have hCandBoundsN := hCandBounds N
    -- Proof comment: after identifying `halfErr` with the explicit candidate, multiply the
    -- candidate bounds back by `2` to recover the desired odd-prefix window for `upperLoss`.
    constructor
    · have hHalfErrNonneg : 0 ≤ halfErr N := by
        simpa [hHalfErrEqCand N] using hCandBoundsN.1
      linarith
    · have hHalfErrLe :
          halfErr N ≤
            shiftedStripMass x a T (2 * N + 1 : ℤ) +
              shiftedStripMass x a T (-(2 * N + 2 : ℤ)) := by
        simpa [hHalfErrEqCand N] using hCandBoundsN.2
      linarith
  -- Proof comment: once the upper-loss odd-prefix window is established, transport it back to the
  -- interval paired-shell boundary window through the exact algebraic equivalence.
  exact
    (upperLossCorrectionOddPrefix_window_iff_intervalWindowLocal
      (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa) (T := T) (hT := _hT) N).mp
      hUpper

/-- Helper for Exercise 21.3.1: the source-facing Brownian owner theorem is the odd
correction-prefix window on `upperLoss`, whose remainder should be the surviving reflected tail
between the next positive strip and its reflected negative companion. -/
theorem upperLossCorrectionOddPrefix_outerStripWindowLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
      μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
        2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
          shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  have hInterval :
      boundaryTail (2 * N + 1) -
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
        interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ∧
      interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ≤
        boundaryTail (2 * N + 1) := by
    -- Proof comment: the exact paired-shell interval boundary window is now isolated as its own
    -- owner theorem, so the source-facing `upperLoss` statement is only a transport step.
    simpa [boundaryTail, interval] using
      intervalPairShellOddPrefix_boundaryWindowOwnerLocal
        (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
        (T := T) (_hT := _hT) N
  -- Proof comment: transport the isolated interval-side window back through the exact boundary
  -- tail identity to recover the source-facing correction-prefix bound on `upperLoss`.
  simpa [correction, upperLoss, boundaryTail, interval] using
    (upperLossCorrectionOddPrefix_window_iff_intervalWindowLocal
      (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa) (hT := _hT) N).mpr hInterval

/-- Helper for Exercise 21.3.1: the remaining blocker is the interval paired-shell boundary window
at odd prefixes, which transports back to the desired upper-loss correction bound. -/
theorem intervalPairShellOddPrefix_boundaryWindowCoreLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) (N : ℕ) :
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    (boundaryTail (2 * N + 1) -
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
        interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ∧
      interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ≤
        boundaryTail (2 * N + 1)) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: after isolating the exact interval-side boundary window earlier, this core
  -- theorem is only the public local spelling of that owner statement.
  simpa [correction, boundaryTail, interval] using
    intervalPairShellOddPrefix_boundaryWindowOwnerLocal
      (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
      (T := T) (_hT := _hT) N

/-- Helper for Exercise 21.3.1: after removing the first `N` odd correction shells, the remaining
upper-loss error is nonnegative and is controlled by the two outer reflected strips at the same
shell level. This is the corrected owner statement consumed by the downstream interval-error
transport. -/
theorem upperLossCorrectionOddPrefix_remainderWindowLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) (N : ℕ) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
      μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
        2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
          shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: after correcting the dependency direction, this theorem is only the public
  -- spelling of the single upper-loss owner theorem.
  simpa [correction, upperLoss] using
    upperLossCorrectionOddPrefix_outerStripWindowLocal
      (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
      (T := T) (_hT := _hT) N

/-- Helper for Exercise 21.3.1: the remaining Brownian owner theorem is the direct window bound on
the odd correction-prefix error for `upperLoss`; the interval paired-shell window is just its
algebraic transport through the boundary-tail identity. -/
theorem upperLossCorrectionOddPrefix_errorWindowCoreLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
        μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: after correcting the helper surface, this theorem is only the public-name
  -- transport of the same odd-prefix outer-strip bound.
  simpa [correction, upperLoss] using
    upperLossCorrectionOddPrefix_remainderWindowLocal
      (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
      (T := T) (_hT := _hT) N

/-- Helper for Exercise 21.3.1: the interval paired-shell odd prefix differs from interval
survival by a boundary-tail window, and the remaining uncovered reflected tail is bounded by the
two outer strips at the same shell level. -/
theorem intervalPairShellOddPrefix_boundaryWindowLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let boundaryTail : ℕ → ℝ := fun n ↦
      1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
        cdf (gaussianReal x T) (-((n : ℝ) * a))
    let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      boundaryTail (2 * N + 1) -
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) ≤
        interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ∧
      interval - (∑ n ∈ Finset.range (2 * N + 1), alternatingStripPairShell x a T n) ≤
        boundaryTail (2 * N + 1) := by
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: this later public theorem is now only a spelling wrapper around the earlier
  -- owner theorem, so no extra prefix algebra is needed here.
  simpa [boundaryTail, interval] using
    intervalPairShellOddPrefix_boundaryWindowOwnerLocal
      (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
      (T := T) (_hT := _hT)

/-- Helper for Exercise 21.3.1: once the interval paired-shell odd prefix is trapped inside its
boundary-tail window, the odd correction prefix has the same two-outer-strip error bound around
`upperLoss`. -/
theorem upperLossCorrectionOddPrefix_errorBoundLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
        μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let boundaryTail : ℕ → ℝ := fun n ↦
    1 - cdf (gaussianReal x T) ((n : ℝ) * a) -
      cdf (gaussianReal x T) (-((n : ℝ) * a))
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  -- Proof comment: the source-facing blocker has been isolated as the owner theorem
  -- `upperLossCorrectionOddPrefix_errorWindowCoreLocal`, so this wrapper is now only a spelling
  -- transport to the established public local names.
  simpa [correction, upperLoss] using
    upperLossCorrectionOddPrefix_errorWindowCoreLocal
      (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa)
      (T := T) (_hT := hT)

/-- Helper for Exercise 21.3.1: the direct Brownian owner still missing after the shell-difference
transport is the odd-shell prefix formula for `upperLoss`, with an explicit remainder tending to
`0`. -/
theorem upperLossOddShellPrefix_errorBoundLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      0 ≤ μ.real upperLoss - (∑ k ∈ Finset.range N, oddShell k) ∧
        μ.real upperLoss - (∑ k ∈ Finset.range N, oddShell k) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  dsimp [oddShell, upperLoss, correction]
  intro N
  have hCorrection :
      0 ≤ μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ∧
        μ.real upperLoss - (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))) := by
    -- Proof comment: the new interval-side remainder window transports directly to the odd
    -- correction prefixes.
    simpa [correction, upperLoss] using
      upperLossCorrectionOddPrefix_errorBoundLocal
        (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa)
        (T := T) (hT := _hT) N
  have hPrefix :
      (∑ k ∈ Finset.range N, oddShell k) =
        ∑ n ∈ Finset.range (2 * N + 1), correction n := by
    -- Proof comment: rewrite the odd-shell prefix into the corresponding odd correction prefix.
    simpa [oddShell, correction] using
      oddShellPrefix_eq_upperLossCorrectionOddPrefixLocal (x := x) (a := a) (T := T) N
  constructor
  · simpa [hPrefix] using hCorrection.1
  · simpa [hPrefix] using hCorrection.2

/-- Helper for Exercise 21.3.1: once the finite odd-shell prefix error is dominated by the
explicit outer strips, that error tends to `0`. -/
theorem upperLossOddShellPrefix_errorTendstoZeroLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    Tendsto
      (fun N : ℕ ↦ μ.real upperLoss - (∑ k ∈ Finset.range N, oddShell k))
      atTop (𝓝 0) := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have ha : 0 < a := by
    linarith
  have hIndex : Tendsto (fun N : ℕ ↦ 2 * N + 1) atTop atTop := by
    refine tendsto_atTop_mono ?_ tendsto_id
    intro N
    calc
      N ≤ N + N := by simpa [two_mul] using Nat.le_add_left N N
      _ ≤ N + N + 1 := Nat.le_succ (N + N)
      _ = 2 * N + 1 := by ring
  have hOuter :
      Tendsto
        (fun N : ℕ ↦
          2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * N + 2 : ℤ))))
        atTop (𝓝 0) := by
    have hOuterCore :
        Tendsto
          (fun N : ℕ ↦
            shiftedStripMass x a T (2 * N + 1 : ℤ) +
              shiftedStripMass x a T (-(2 * N + 2 : ℤ)))
          atTop (𝓝 0) := by
      convert (outerStripMass_tendsto_zeroLocal (x := x) (a := a) ha hT).comp hIndex using 1 with N
    have hScaled :
        Tendsto
          (fun N : ℕ ↦
            2 * (shiftedStripMass x a T (2 * N + 1 : ℤ) +
              shiftedStripMass x a T (-(2 * N + 2 : ℤ))))
          atTop
          (𝓝 (2 * (0 : ℝ))) := by
      exact tendsto_const_nhds.mul hOuterCore
    simpa using hScaled
  rw [Metric.tendsto_atTop] at hOuter ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hOuter ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hNonneg, hBound⟩ :=
    upperLossOddShellPrefix_errorBoundLocal
      (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa) (_hT := hT) n
  have hUpperDist :
      dist
          (2 * (shiftedStripMass x a T (2 * n + 1 : ℤ) +
            shiftedStripMass x a T (-(2 * n + 2 : ℤ))))
          0 < ε := by
    exact hN n hn
  have hUpperNonneg :
      0 ≤ 2 * (shiftedStripMass x a T (2 * n + 1 : ℤ) +
        shiftedStripMass x a T (-(2 * n + 2 : ℤ))) := by
    have hPosNonneg : 0 ≤ shiftedStripMass x a T (2 * n + 1 : ℤ) := by
      exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (2 * n + 1 : ℤ)
    have hNegNonneg : 0 ≤ shiftedStripMass x a T (-(2 * n + 2 : ℤ)) := by
      exact shiftedStripMass_nonneg (x := x) (a := a) (T := T) (-(2 * n + 2 : ℤ))
    positivity
  have hUpperLt :
      2 * (shiftedStripMass x a T (2 * n + 1 : ℤ) +
        shiftedStripMass x a T (-(2 * n + 2 : ℤ))) < ε := by
    have hUpperAbs :
        |2 * (shiftedStripMass x a T (2 * n + 1 : ℤ) +
          shiftedStripMass x a T (-(2 * n + 2 : ℤ)))| < ε := by
      simpa [Real.dist_eq] using hUpperDist
    rwa [abs_of_nonneg hUpperNonneg] at hUpperAbs
  have hErrorLt :
      μ.real upperLoss - ∑ k ∈ Finset.range n, oddShell k < ε := by
    exact lt_of_le_of_lt hBound hUpperLt
  have hErrorDist :
      dist (μ.real upperLoss - ∑ k ∈ Finset.range n, oddShell k) 0 < ε := by
    have hErrorAbs :
        |μ.real upperLoss - ∑ k ∈ Finset.range n, oddShell k| < ε := by
      rwa [abs_of_nonneg hNonneg]
    simpa [Real.dist_eq] using hErrorAbs
  simpa [oddShell, upperLoss] using hErrorDist

/-- Helper for Exercise 21.3.1: the direct Brownian owner still missing after the shell-difference
transport is the odd-shell prefix formula for `upperLoss`, with an explicit remainder tending to
`0`. -/
theorem upperLossOddShellPrefix_hasVanishingRemainderLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∃ remainder : ℕ → ℝ,
      (∀ N : ℕ,
        μ.real upperLoss =
          (∑ k ∈ Finset.range N, oddShell k) + remainder N) ∧
      Tendsto remainder atTop (𝓝 0) := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  let remainder : ℕ → ℝ := fun N ↦
    μ.real upperLoss - (∑ k ∈ Finset.range N, oddShell k)
  have hRemainder :
      Tendsto remainder atTop (𝓝 0) := by
    -- Proof comment: after isolating the finite odd-shell error as `remainder`, its limit is the
    -- dedicated outer-strip tail theorem proved just above.
    simpa [remainder, oddShell, upperLoss] using
      upperLossOddShellPrefix_errorTendstoZeroLocal
        (μ := μ) (W := W) (x := x) (a := a) (T := T) _hW _hx _hxa _hT
  refine ⟨remainder, ?_, hRemainder⟩
  intro N
  -- Proof comment: the remainder is defined as the scalar gap between `μ.real upperLoss` and the
  -- odd-shell prefix, so the advertised prefix identity is just a rearrangement.
  calc
    μ.real upperLoss
        = (∑ k ∈ Finset.range N, oddShell k) +
            (μ.real upperLoss - ∑ k ∈ Finset.range N, oddShell k) := by
              ring
    _ = (∑ k ∈ Finset.range N, oddShell k) + remainder N := by
          rfl

/-- Helper for Exercise 21.3.1: once the direct odd-shell prefix formula for `upperLoss` is in
place, the odd reflected-shell series has the desired Brownian sum. -/
theorem upperLossOddShell_hasSumLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    HasSum oddShell (μ.real upperLoss) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  obtain ⟨remainder, hPrefix, hRem⟩ :=
    upperLossOddShellPrefix_hasVanishingRemainderLocal
      (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa) (_hT := hT)
  have hCorrectionSummable : Summable correction := by
    -- Proof comment: the correction-series owner theorem already gives summability of the full
    -- odd/even correction sequence.
    exact
      (upperLossCorrectionSeries_hasSum_oddShellDifferenceLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T) hx hxa hT).summable
  have hOddShellSummable : Summable oddShell := by
    -- Proof comment: `oddShell k` is exactly the odd-index subsequence `correction (2 * k + 1)`.
    have hOddSub : Summable (fun k : ℕ ↦ correction (2 * k + 1)) := by
      exact hCorrectionSummable.comp_injective (fun m n hmn ↦ by omega)
    convert hOddSub using 1
    ext k
    have hNotEven : ¬ Even (2 * k + 1) := by
      simp
    dsimp [correction, oddShell]
    rw [if_neg hNotEven]
    congr 1
    congr 1
    ring
  have hPrefix' :
      ∀ N : ℕ,
        (∑ k ∈ Finset.range N, oddShell k) =
          μ.real upperLoss + (-remainder N) := by
    intro N
    -- Proof comment: rewrite the prefix identity to the `l + error` normal form expected by the
    -- generic prefix-to-`HasSum` helper.
    linarith [hPrefix N]
  have hNegRem : Tendsto (fun N : ℕ ↦ -remainder N) atTop (𝓝 0) := by
    -- Proof comment: negating the remainder does not change its limit.
    simpa using hRem.neg
  -- Proof comment: summability of the odd shells and the vanishing prefix remainder close the
  -- direct Brownian `HasSum` statement.
  exact
    hasSum_alternatingStripPairShell_of_prefixRemainderLocal
      hOddShellSummable hPrefix' hNegRem

-- Helper for Exercise 21.3.1: the odd reflected shell-difference series is exactly the Brownian
-- upper-loss mass `lower \\ interval`.
-- Route correction: the stable Brownian owner is the scalar identity for `upperLoss` itself, not
-- another paired-prefix remainder package. Once this scalar is available, both open Brownian
-- `HasSum` theorems become short transports.
/-- Helper for Exercise 21.3.1: the structurally correct Brownian owner statement is that the full
correction series has sum `μ.real upperLoss`. The old even-prefix lower bound was false because
all correction terms are nonnegative, so the prefix theorems below now derive from this `HasSum`
statement instead of trying to squeeze `upperLoss` from above and below by partial sums. -/
theorem upperLossCorrectionSeries_hasSum_upperLossCoreLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    HasSum correction (μ.real upperLoss) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hOddShell : HasSum oddShell (μ.real upperLoss) := by
    -- Proof comment: the direct odd-shell owner theorem packages the remaining Brownian scalar.
    simpa [oddShell, upperLoss] using
      upperLossOddShell_hasSumLocal
        (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (hx := _hx) (hxa := _hxa) (hT := _hT)
  have hCorrection : HasSum correction (∑' k : ℕ, oddShell k) := by
    -- Proof comment: the correction sequence already sums to the odd-shell `tsum`; only the
    -- Brownian scalar on the right had to be repaired.
    simpa [correction, oddShell] using
      upperLossCorrectionSeries_hasSum_oddShellDifferenceLocal
        (μ := μ) (W := W) (hW := _hW) (x := x) (a := a) (T := T) _hx _hxa _hT
  have hOddScalar : (∑' k : ℕ, oddShell k) = μ.real upperLoss := hOddShell.tsum_eq
  -- Proof comment: rewrite the scalar target of the correction-series `HasSum` through the
  -- repaired direct odd-shell owner theorem.
  simpa [correction, upperLoss, hOddScalar] using hCorrection

/-- Helper for Exercise 21.3.1: every odd correction prefix is bounded above by the Brownian
upper-loss mass. -/
theorem upperLossCorrection_oddPrefix_le_upperLossLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (2 * N + 1), correction n) ≤ μ.real upperLoss := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hCore : HasSum correction (μ.real upperLoss) := by
    -- Proof comment: the correction prefixes are now compared to `upperLoss` through the repaired
    -- owner `HasSum` theorem for the full correction series.
    simpa [correction, upperLoss] using
      upperLossCorrectionSeries_hasSum_upperLossCoreLocal
        (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
        (_hT := _hT)
  have hNonneg : ∀ n : ℕ, 0 ≤ correction n := by
    intro n
    by_cases hEven : Even n
    · -- Proof comment: even correction terms vanish by definition.
      simp [correction, hEven]
    · -- Proof comment: odd correction terms are twice a nonnegative shell difference.
      have hShellNonneg :
          0 ≤ shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)) := by
        exact
          shellDifference_nonnegLocal
            (x := x) (a := a) _hx.le (by linarith) (T := T) _hT n
      simp [correction, hEven, hShellNonneg]
  intro N
  -- Proof comment: every nonnegative finite correction prefix is bounded above by the full sum.
  exact hCore.sum_le_tsum _ (fun n _ ↦ hNonneg n)

/-- Helper for Exercise 21.3.1: every even correction prefix is also bounded above by the Brownian
upper-loss mass, because the correction series is nonnegative termwise. -/
theorem upperLossCorrection_evenPrefix_le_upperLossLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (2 * N + 2), correction n) ≤ μ.real upperLoss := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hCore : HasSum correction (μ.real upperLoss) := by
    -- Proof comment: the same repaired owner theorem controls the even correction prefixes.
    simpa [correction, upperLoss] using
      upperLossCorrectionSeries_hasSum_upperLossCoreLocal
        (μ := μ) (W := W) (_hW := _hW) (x := x) (a := a) (_hx := _hx) (_hxa := _hxa)
        (_hT := _hT)
  have hNonneg : ∀ n : ℕ, 0 ≤ correction n := by
    intro n
    by_cases hEven : Even n
    · -- Proof comment: even correction terms vanish by definition.
      simp [correction, hEven]
    · -- Proof comment: odd correction terms are twice a nonnegative shell difference.
      have hShellNonneg :
          0 ≤ shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)) := by
        exact
          shellDifference_nonnegLocal
            (x := x) (a := a) _hx.le (by linarith) (T := T) _hT n
      simp [correction, hEven, hShellNonneg]
  intro N
  -- Proof comment: as above, nonnegative finite correction prefixes lie below the full sum.
  exact hCore.sum_le_tsum _ (fun n _ ↦ hNonneg n)

/-- Helper for Exercise 21.3.1: the source-facing Brownian owner lives on the correction prefixes
before any odd-shell reindexing is performed. -/
theorem upperLossCorrectionPrefix_tendsto_upperLossLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∃ remainder : ℕ → ℝ,
      (∀ N : ℕ,
        μ.real upperLoss =
          (∑ n ∈ Finset.range N, correction n) + remainder N) ∧
      Tendsto remainder atTop (𝓝 0) := by
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hCore : HasSum correction (μ.real upperLoss) := by
    -- Proof comment: the repaired source-facing owner theorem already packages convergence of the
    -- full correction-prefix sequence to the Brownian `upperLoss` mass.
    simpa [correction, upperLoss] using
      upperLossCorrectionSeries_hasSum_upperLossCoreLocal
        (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa) (_hT := hT)
  have hPrefixTendsto :
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, correction n) atTop (𝓝 (μ.real upperLoss)) := by
    -- Proof comment: ordered partial sums of a `HasSum` series converge to its sum.
    exact hCore.tendsto_sum_nat
  let remainder : ℕ → ℝ := fun N ↦ μ.real upperLoss - ∑ n ∈ Finset.range N, correction n
  have hRemainder : Tendsto remainder atTop (𝓝 0) := by
    -- Proof comment: define the remainder as the difference between the target scalar and the
    -- correction prefix; its vanishing is exactly the convergence statement proved above.
    have hDiff :
        Tendsto remainder atTop (𝓝 (μ.real upperLoss - μ.real upperLoss)) := by
      simpa [remainder] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ μ.real upperLoss) atTop
          (𝓝 (μ.real upperLoss))).sub hPrefixTendsto)
    simpa using hDiff
  refine ⟨remainder, ?_, hRemainder⟩
  intro N
  -- Proof comment: the prefix identity is just the defining rearrangement of the remainder term.
  dsimp [remainder]
  linarith

/-- Helper for Exercise 21.3.1: the Brownian upper-loss mass is the limit of the odd reflected
shell prefixes, with a remainder that vanishes at infinity. -/
-- TODO: prove this by the finite `Set.Ioc` reflected-slice decomposition from
-- `upperBarrierHitBeforeTime_terminalIoc_eq_reflectedStripLocal`, then rewrite the remainder to
-- the explicit outer-strip normal form controlled by `outerStripMass_tendsto_zeroLocal`.
theorem upperLoss_oddShellPrefix_tendstoLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    ∃ remainder : ℕ → ℝ,
      (∀ N : ℕ,
        μ.real upperLoss =
          (∑ k ∈ Finset.range N, oddShell k) + remainder N) ∧
      Tendsto remainder atTop (𝓝 0) := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: after moving the real blocker earlier in the file, the historical wrapper
  -- theorem is just the direct odd-shell prefix owner statement.
  simpa [oddShell, upperLoss] using
    upperLossOddShellPrefix_hasVanishingRemainderLocal
      (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa) (_hT := hT)

/-- Helper for Exercise 21.3.1: once the odd-shell prefix limit is isolated, the scalar identity
for `upperLoss` is a direct uniqueness-of-limits argument. -/
theorem upperLoss_eq_tsum_oddShellDifferenceLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let oddShell : ℕ → ℝ := fun k ↦
      2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
        shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    μ.real upperLoss = ∑' k : ℕ, oddShell k := by
  let oddShell : ℕ → ℝ := fun k ↦
    2 * (shiftedStripMass x a T (2 * k + 1 : ℤ) -
      shiftedStripMass x a T (-(2 * k + 2 : ℤ)))
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  -- Proof comment: the direct odd-shell Brownian owner theorem already packages the needed
  -- `HasSum`, so the scalar identity is just its `tsum`.
  simpa [oddShell, upperLoss] using
    (upperLossOddShell_hasSumLocal
      (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (hx := hx) (hxa := hxa) (hT := hT)).tsum_eq.symm

/-- Helper for Exercise 21.3.1: the upper-loss correction series should sum directly to the
Brownian upper-loss event, without the false odd/even parity squeeze from earlier attempts. -/
-- Route correction: the old helper surface `odd prefix ≤ l ≤ even prefix` is not mathematically
-- compatible with the already proved nonnegative shell decomposition of the correction terms. The
-- stable Brownian frontier is the exact `HasSum` statement below, fed by the finite prefix
-- identity `upperLossCorrection_prefix_eq_lowerBarrierSurvival_sub_boundaryTail_sub_pairShellPrefixLocal`
-- together with the reflected-slice bridges
-- `hitUpperBeforeTime_terminalBelow_eq_reflectedClosedTailRealLocal` and
-- `upperBarrierHitBeforeTime_terminalIoc_eq_reflectedStripLocal`.
theorem upperLossCorrectionSeries_hasSum_upperLossLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    let correction : ℕ → ℝ := fun n ↦
      if Even n then 0 else
        2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
    let upperLoss : Set Ω :=
      {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
        {ω | T < brownianIntervalExitTime W x a ω}
    HasSum correction (μ.real upperLoss) := by
  -- Proof comment: after the direct odd-shell owner is moved before the core theorem, the public
  -- wrapper is just that repaired owner theorem.
  simpa [correction, upperLoss] using
    upperLossCorrectionSeries_hasSum_upperLossCoreLocal
      (μ := μ) (W := W) (_hW := hW) (x := x) (a := a) (_hx := hx) (_hxa := hxa) (_hT := hT)

/-- Helper for Exercise 21.3.1: the paired shell series is the single Brownian owner statement
needed to recover both the correction series and the centered alternating strip series. -/
theorem alternatingStripPairShell_hasSum_intervalSurvivalCoreLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (alternatingStripPairShell x a T)
      (μ.real {ω | T < brownianIntervalExitTime W x a ω}) := by
  let shellDifference : ℕ → ℝ := fun n ↦
    shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ))
  let correction : ℕ → ℝ := fun n ↦
    if Even n then 0 else
      2 * (shiftedStripMass x a T n - shiftedStripMass x a T (-(n + 1 : ℤ)))
  let lower : ℝ := μ.real {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω}
  let upperLoss : Set Ω :=
    {ω | T < hittingAfter W ({-x} : Set ℝ) 0 ω} \
      {ω | T < brownianIntervalExitTime W x a ω}
  have hLowerHasSum : HasSum shellDifference lower := by
    -- Proof comment: the one-sided lower-barrier shell series is already available as the owner
    -- Brownian `HasSum`.
    simpa [shellDifference, lower] using
      lowerBarrierStripPairShell_hasSumLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
  have hCorrectionHasSum : HasSum correction (μ.real upperLoss) := by
    -- Proof comment: after the source-facing upper-loss scalar is fixed, the correction series is
    -- just its direct corollary.
    simpa [correction, upperLoss] using
      upperLossCorrectionSeries_hasSum_upperLossLocal
        (μ := μ) (W := W) (hW := hW) (x := x) (a := a) hx hxa hT
  have hPairHasSum :
      HasSum (fun n : ℕ ↦ shellDifference n - correction n)
        (lower - μ.real upperLoss) := by
    -- Proof comment: subtract the upper-loss correction series from the lower-barrier shell
    -- series termwise; the paired-shell coefficients are exactly that difference.
    exact hLowerHasSum.sub hCorrectionHasSum
  have hPairRewrite :
      HasSum (alternatingStripPairShell x a T) (lower - μ.real upperLoss) := by
    -- Proof comment: the finite shell algebra was already packaged as
    -- `correction = shellDifference - pairedShell`, so we only rewrite the coefficient sequence.
    have hSeq :
        (fun n : ℕ ↦ shellDifference n - correction n) = alternatingStripPairShell x a T := by
      funext n
      have hTerm :=
        upperLossCorrection_eq_shellDifference_sub_pairShellLocal
          (x := x) (a := a) (T := T) n
      dsimp [shellDifference, correction] at hTerm ⊢
      linarith
    rw [← hSeq]
    exact hPairHasSum
  have hGap :
      lower - μ.real upperLoss =
        μ.real {ω | T < brownianIntervalExitTime W x a ω} := by
    have hGap' :
        lower - μ.real {ω | T < brownianIntervalExitTime W x a ω} =
          μ.real upperLoss := by
      -- Proof comment: this is the already packaged event-level gap `lower \\ interval`.
      simpa [lower, upperLoss] using
        intervalSurvivalGap_eq_upperLossRealLocal
          (μ := μ) (W := W) (hW := hW) (x := x) (a := a) (T := T)
    linarith
  -- Proof comment: once the scalar gap is rewritten, the paired-shell series lands exactly on
  -- the interval-survival mass.
  simpa [hGap] using hPairRewrite

/-- Helper for Exercise 21.3.1: the Brownian shell-prefix correction problem is exactly to show
that the paired shell prefixes differ from the interval-survival mass by a remainder tending to
`0`. This isolates the remaining finite upper-loss normalization from the final `HasSum`
assembly. -/
theorem upperLossCorrection_prefix_hasVanishingRemainderLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (_hW : IsBrownianMotion μ W)
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    ∃ remainder : ℕ → ℝ,
      (∀ N : ℕ,
        (∑ n ∈ Finset.range N, alternatingStripPairShell x a T n) =
          μ.real {ω | T < brownianIntervalExitTime W x a ω} + remainder N) ∧
      Tendsto remainder atTop (𝓝 0) := by
  -- Route correction: after isolating the paired-shell owner theorem, this companion statement is
  -- just the finite-prefix form of its `HasSum`.
  have hW := _hW
  have hx := _hx
  have hxa := _hxa
  have hT := _hT
  let interval : ℝ := μ.real {ω | T < brownianIntervalExitTime W x a ω}
  let remainder : ℕ → ℝ := fun N ↦
    (∑ n ∈ Finset.range N, alternatingStripPairShell x a T n) - interval
  have hPairHasSum :
      HasSum (alternatingStripPairShell x a T) interval := by
    -- Proof comment: use the smaller owner theorem for the paired-shell Brownian series.
    simpa [interval] using
      alternatingStripPairShell_hasSum_intervalSurvivalCoreLocal
        (μ := μ) (W := W) (x := x) (a := a) (T := T) hW hx hxa hT
  have hRemainder :
      Tendsto remainder atTop (𝓝 0) := by
    -- Proof comment: by definition the remainder is exactly the paired-shell partial sum error.
    simpa [remainder] using
      (hPairHasSum.tendsto_sum_nat.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ interval) atTop (𝓝 interval)))
  refine ⟨remainder, ?_, hRemainder⟩
  intro N
  -- Proof comment: the explicit finite-prefix equality is just the definition of the remainder.
  dsimp [remainder]
  ring

/-- Helper for Exercise 21.3.1: the Brownian reflection argument is now reduced to the paired
`ℕ`-shell series. -/
theorem centeredAlternatingStripSeries_hasSum_intervalSurvivalLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n)
      (μ.real {ω | T < brownianIntervalExitTime W x a ω}) := by
  -- Route correction: the remaining Brownian owner statement now lives on the centered `ℤ`-series,
  -- so the shell theorem below only transports this `HasSum` through `nat_add_neg_add_one`.
  have ha : 0 < a := by
    linarith
  obtain ⟨remainder, hprefix, hrem⟩ :=
    upperLossCorrection_prefix_hasVanishingRemainderLocal
      (μ := μ) (W := W) (x := x) (a := a) (T := T) hW hx hxa hT
  have hsummable : Summable (alternatingStripPairShell x a T) := by
    -- Proof comment: absolute summability of the centered alternating strip series already gives
    -- summability of the paired shell repackaging.
    exact summable_alternatingStripPairShellLocal (x := x) (a := a) ha hT
  have hshell :
      HasSum (alternatingStripPairShell x a T)
        (μ.real {ω | T < brownianIntervalExitTime W x a ω}) := by
    -- Proof comment: once the finite shell prefixes are normalized to the target interval-survival
    -- mass plus a vanishing remainder, the abstract prefix-to-`HasSum` lemma closes the shell
    -- series immediately.
    exact
      hasSum_alternatingStripPairShell_of_prefixRemainderLocal
        hsummable hprefix hrem
  -- Proof comment: the centered `ℤ`-series is just the canonical shell-to-centered transport of
  -- the paired `ℕ`-shell series.
  exact hasSum_of_alternatingStripPairShellLocal (x := x) (a := a) (T := T) ha hT hshell

/-- Helper for Exercise 21.3.1: the Brownian reflection argument is now reduced to the paired
`ℕ`-shell series. -/
theorem alternatingStripPairShell_hasSum_intervalSurvivalLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (alternatingStripPairShell x a T)
      (μ.real {ω | T < brownianIntervalExitTime W x a ω}) := by
  -- Proof comment: once the centered Brownian `ℤ`-series is known, the paired shell statement is
  -- just the canonical `nat_add_neg_add_one` repackaging of that owner theorem.
  convert
      (centeredAlternatingStripSeries_hasSum_intervalSurvivalLocal
        (hW := hW) (x := x) (a := a) hx hxa hT).nat_add_neg_add_one using 1

/-- Helper for Exercise 21.3.1: once the reflected strip-prefix argument is packaged as a `HasSum`
statement, the alternating Brownian strip formula `(21.18)` is immediate. -/
theorem alternatingStripSeries_hasSum_intervalSurvivalLocal
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n)
      (μ.real {ω | T < brownianIntervalExitTime W x a ω}) := by
  have ha : 0 < a := by
    linarith
  -- Proof comment: after pairing indices `n` and `-(n + 1)`, the public `ℤ`-series statement is
  -- just the abstract shell-to-centered transport of the smaller Brownian shell theorem.
  exact
    hasSum_of_alternatingStripPairShellLocal (x := x) (a := a) (T := T) ha hT
      (alternatingStripPairShell_hasSum_intervalSurvivalLocal
        (hW := hW) hx hxa hT)

/-- Exercise 21.3.1: the interval-survival probability is the alternating sum of the Gaussian
terminal strip masses. This is formula `(21.18)` in the text. -/
theorem brownianIntervalSurvival_eq_alternatingStripSeries
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    μ.real {ω | T < brownianIntervalExitTime W x a ω} =
      ∑' n : ℤ, paritySign n * shiftedStripMass x a T n := by
  -- Proof comment: once the centered alternating strip series is available as a `HasSum`, the
  -- textbook identity is just the corresponding `tsum` equality.
  simpa [eq_comm] using
    (alternatingStripSeries_hasSum_intervalSurvivalLocal
      (hW := hW) hx hxa hT).tsum_eq

/-- Helper for Exercise 21.3.1: outside every compact interval, the cocompact filter forces
`|s|` to dominate any prescribed nonnegative radius. -/
theorem eventually_abs_ge_cocompactLocal
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ s : ℝ in cocompact ℝ, R ≤ |s| := by
  have hCompact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  filter_upwards [hCompact.compl_mem_cocompact] with s hs
  by_cases hs_nonneg : 0 ≤ s
  · have hRs : R < s := by
      by_contra hle
      exact hs ⟨by linarith, le_of_not_gt hle⟩
    exact le_of_lt <| by simpa [abs_of_nonneg hs_nonneg] using hRs
  · have hs_neg : s < 0 := lt_of_not_ge hs_nonneg
    have hsR : s < -R := by
      by_contra hge
      exact hs ⟨by linarith, by linarith⟩
    have : R < -s := by linarith
    exact le_of_lt <| by simpa [abs_of_neg hs_neg] using this

/-- Helper for Exercise 21.3.1: the oscillatory modulation factor has norm `1`, so the norm of
`modulatedStripCellAverage` is exactly the norm of the underlying Gaussian cell integral. -/
theorem norm_modulatedStripCellAverage_eq_integralLocal
    {x a : ℝ} {T : NNReal} (s : ℝ) :
    ‖modulatedStripCellAverage x a T s‖ =
      ‖∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)‖ := by
  -- Proof comment: the phase factor `exp (π s I)` lies on the unit circle, so it disappears
  -- after taking norms.
  rw [modulatedStripCellAverage, norm_mul]
  simp [Complex.norm_exp]

/-- Helper for Exercise 21.3.1: if the strip `Set.uIcc (a * s) (a * (s + 1))` lies far enough from the
starting point `x`, then every point in that strip stays at distance at least `(a / 2) * |s|`
from `x`. -/
theorem stripDistanceLowerBoundLocal
    {x a s y : ℝ} (ha : 0 < a)
    (hLarge : 2 * (a + |x|) ≤ a * |s|)
    (hy : y ∈ Set.uIcc (a * s) (a * (s + 1))) :
    (a / 2) * |s| ≤ |y - x| := by
  have hsOrder : a * s ≤ a * (s + 1) := by
    nlinarith
  have hyIcc : y ∈ Set.Icc (a * s) (a * (s + 1)) := by
    simpa [Set.uIcc_of_le hsOrder] using hy
  have hyShiftNonneg : 0 ≤ y - a * s := by
    linarith [hyIcc.1]
  have hyShiftLe : y - a * s ≤ a := by
    have : y ≤ a * (s + 1) := hyIcc.2
    linarith
  have hyShiftAbs : |y - a * s| ≤ a := by
    rw [abs_of_nonneg hyShiftNonneg]
    exact hyShiftLe
  have hStripAbs :
      a * |s| - a ≤ |y| := by
    have hReverse : |a * s| - |y| ≤ |y - a * s| := by
      simpa [abs_sub_comm] using (abs_sub_abs_le_abs_sub (a * s) y)
    have hScaleAbs : |a * s| = a * |s| := by
      rw [abs_mul, abs_of_nonneg ha.le]
    linarith
  have hDistAbs : |y| - |x| ≤ |y - x| := by
    exact abs_sub_abs_le_abs_sub y x
  -- Proof comment: the strip itself stays at distance at least `a * |s| - a` from the origin,
  -- and the large-cocompact hypothesis upgrades that to a lower bound away from the center `x`.
  have hFar : a * |s| - (a + |x|) ≤ |y - x| := by
    linarith
  linarith

/-- Helper for Exercise 21.3.1: the Gaussian cell average has polynomial decay of order `2` on
the cocompact filter, which is the exact Poisson-summation hypothesis used later. -/
theorem modulatedStripCellAverage_isBigO_cocompactLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Asymptotics.IsBigO (cocompact ℝ) (modulatedStripCellAverage x a T)
      (fun s : ℝ => |s| ^ (-2 : ℝ)) := by
  -- Route correction: keep the decay theorem as the isolated analytic blocker. The proved helper
  -- lemmas above fix the two normal forms needed next: eventual control of `|s|` on
  -- `cocompact ℝ` and removal of the harmless unit-modulus phase factor.
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  let coeff : ℝ := (Real.sqrt (2 * Real.pi * (T : ℝ≥0)))⁻¹
  let decay : ℝ := a ^ 2 / (8 * (T : ℝ))
  have hDecayPos : 0 < decay := by
    dsimp [decay]
    positivity
  have hLarge :
      ∀ᶠ s : ℝ in cocompact ℝ, 2 * (a + |x|) ≤ a * |s| := by
    have hRadius :
        0 ≤ (2 * (a + |x|)) / a := by
      positivity
    filter_upwards
        [eventually_abs_ge_cocompactLocal (R := (2 * (a + |x|)) / a) hRadius] with s hs
    have hs' : 2 * (a + |x|) ≤ |s| * a := (div_le_iff₀ ha).mp hs
    simpa [mul_comm] using hs'
  have hExpBigO :
      Asymptotics.IsBigO (cocompact ℝ)
        (fun s : ℝ => Real.exp (-(decay * |s| ^ 2)))
        (fun s : ℝ => |s| ^ (-2 : ℝ)) := by
    have hExpProd :
        Tendsto (fun s : ℝ => |s| ^ (2 : ℝ) * Real.exp (-(decay * |s| ^ 2)))
          (cocompact ℝ) (𝓝 0) := by
      simpa [decay, mul_assoc, mul_left_comm, mul_comm] using
        (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hDecayPos (2 : ℝ))
    have hProdBound :
        ∀ᶠ s : ℝ in cocompact ℝ,
          |s| ^ (2 : ℝ) * Real.exp (-(decay * |s| ^ 2)) ≤ 1 := by
      filter_upwards [hExpProd (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)] with s hs
      have hsDist :
          dist (|s| ^ (2 : ℝ) * Real.exp (-(decay * |s| ^ 2))) 0 ≤ 1 := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hs
      have hsNonneg : 0 ≤ |s| ^ (2 : ℝ) * Real.exp (-(decay * |s| ^ 2)) := by
        positivity
      simpa [abs_of_nonneg hsNonneg] using hsDist
    have hAbsPos :
        ∀ᶠ s : ℝ in cocompact ℝ, 1 ≤ |s| := by
      simpa using eventually_abs_ge_cocompactLocal (R := 1) zero_le_one
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hProdBound, hAbsPos] with s hsProd hsAbs
    have hsSqPos : 0 < |s| ^ (2 : ℝ) := by
      have hsPos : 0 < |s| := lt_of_lt_of_le zero_lt_one hsAbs
      positivity
    have hExpLeInv :
        Real.exp (-(decay * |s| ^ 2)) ≤ 1 / |s| ^ (2 : ℝ) := by
      have hMul :
          Real.exp (-(decay * |s| ^ 2)) * |s| ^ (2 : ℝ) ≤ 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsProd
      exact (le_div_iff₀ hsSqPos).2 hMul
    have hTarget :
        Real.exp (-(decay * |s| ^ 2)) ≤ |s| ^ (-2 : ℝ) := by
      simpa [Real.rpow_neg (abs_nonneg s), Real.rpow_natCast] using hExpLeInv
    have hExpNonneg : 0 ≤ Real.exp (-(decay * |s| ^ 2)) := by
      positivity
    have hPowNonneg : 0 ≤ |s| ^ (-2 : ℝ) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hExpNonneg, Real.norm_eq_abs, abs_of_nonneg hPowNonneg,
      one_mul]
    exact hTarget
  have hIntegralBound :
      ∀ᶠ s : ℝ in cocompact ℝ,
        ‖∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)‖ ≤
          ‖(a * coeff) * Real.exp (-(decay * |s| ^ 2))‖ := by
    filter_upwards [hLarge] with s hs
    have hPointwise :
        ∀ y ∈ Set.uIoc (a * s) (a * (s + 1)),
          ‖((gaussianPDFReal x T y : ℝ) : ℂ)‖ ≤ coeff * Real.exp (-(decay * |s| ^ 2)) := by
      intro y hy
      have hsOrder : a * s ≤ a * (s + 1) := by
        nlinarith
      have hyIoc : y ∈ Set.Ioc (a * s) (a * (s + 1)) := by
        simpa [Set.uIoc_of_le hsOrder] using hy
      have hy' : y ∈ Set.uIcc (a * s) (a * (s + 1)) := by
        simpa [Set.uIcc_of_le hsOrder] using
          (show y ∈ Set.Icc (a * s) (a * (s + 1)) from ⟨hyIoc.1.le, hyIoc.2⟩)
      have hDist :
          (a / 2) * |s| ≤ |y - x| :=
        stripDistanceLowerBoundLocal (x := x) (a := a) (s := s) (y := y) ha hs hy'
      have hSquareAbs :
          a ^ 2 * |s| ^ 2 / 4 ≤ |y - x| ^ 2 := by
        have hSq : ((a / 2) * |s|) ^ 2 ≤ |y - x| ^ 2 := by
          apply sq_le_sq.2
          rwa [abs_of_nonneg (by positivity), abs_of_nonneg (abs_nonneg _)]
        nlinarith [hSq]
      have hSquare :
          a ^ 2 * |s| ^ 2 / 4 ≤ (y - x) ^ 2 := by
        simpa [sq_abs] using hSquareAbs
      have hExponent :
          decay * |s| ^ 2 ≤ (y - x) ^ 2 / (2 * (T : ℝ)) := by
        have hDenomPos : 0 < 2 * (T : ℝ) := by
          positivity
        apply (le_div_iff₀ hDenomPos).2
        calc
          decay * |s| ^ 2 * (2 * (T : ℝ)) = a ^ 2 * |s| ^ 2 / 4 := by
            dsimp [decay]
            field_simp [hTreal.ne']
            ring
          _ ≤ (y - x) ^ 2 := hSquare
      have hExpLe :
          Real.exp (-(y - x) ^ 2 / (2 * (T : ℝ))) ≤
            Real.exp (-(decay * |s| ^ 2)) := by
        have hNeg : -(y - x) ^ 2 / (2 * (T : ℝ)) ≤ -(decay * |s| ^ 2) := by
          have hNeg' : -((y - x) ^ 2 / (2 * (T : ℝ))) ≤ -(decay * |s| ^ 2) :=
            neg_le_neg hExponent
          simpa [neg_div] using hNeg'
        exact Real.exp_le_exp.mpr hNeg
      have hCoeffNonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      have hPdfLe :
          gaussianPDFReal x T y ≤ coeff * Real.exp (-(decay * |s| ^ 2)) := by
        rw [gaussianPDFReal_def]
        exact mul_le_mul_of_nonneg_left hExpLe hCoeffNonneg
      have hPdfNonneg : 0 ≤ gaussianPDFReal x T y := gaussianPDFReal_nonneg x T y
      -- Proof comment: once every point in the strip is a fixed quadratic distance from `x`,
      -- the explicit Gaussian density formula gives a uniform exponential bound on that strip.
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPdfNonneg]
      exact hPdfLe
    have hNormLe :
        ‖∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)‖ ≤
          (coeff * Real.exp (-(decay * |s| ^ 2))) * |a * (s + 1) - a * s| := by
      exact intervalIntegral.norm_integral_le_of_norm_le_const hPointwise
    have hLen : |a * (s + 1) - a * s| = a := by
      have hDiff : a * (s + 1) - a * s = a := by ring
      rw [hDiff, abs_of_pos ha]
    -- Proof comment: the strip has fixed width `a`, so the pointwise exponential bound integrates
    -- to the same exponential factor up to the constant prefactor `a * coeff`.
    calc
      ‖∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)‖
          ≤ (coeff * Real.exp (-(decay * |s| ^ 2))) * |a * (s + 1) - a * s| := hNormLe
      _ = ‖(a * coeff) * Real.exp (-(decay * |s| ^ 2))‖ := by
            rw [hLen, Real.norm_eq_abs]
            have hNonneg :
                0 ≤ (a * coeff) * Real.exp (-(decay * |s| ^ 2)) := by
              positivity
            rw [abs_of_nonneg hNonneg]
            ring
  have hIntegralBigO :
      Asymptotics.IsBigO (cocompact ℝ)
        (fun s : ℝ =>
          (a * coeff) * Real.exp (-(decay * |s| ^ 2)))
        (fun s : ℝ => |s| ^ (-2 : ℝ)) := by
    exact hExpBigO.const_mul_left (a * coeff)
  have hNormBigO :
      Asymptotics.IsBigO (cocompact ℝ)
        (fun s : ℝ =>
          ∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ))
        (fun s : ℝ => |s| ^ (-2 : ℝ)) := by
    exact hIntegralBound.trans_isBigO hIntegralBigO
  -- Proof comment: combine the phase-removal lemma with the cocompact Gaussian tail estimate to
  -- obtain the exact polynomial-decay hypothesis required by Poisson summation.
  refine (Asymptotics.isBigO_norm_left).mp ?_
  have hNormEq :
      (fun s : ℝ => ‖modulatedStripCellAverage x a T s‖) =ᶠ[cocompact ℝ]
        (fun s : ℝ =>
          ‖∫ y in (a * s)..(a * (s + 1)), ((gaussianPDFReal x T y : ℝ) : ℂ)‖) :=
    Filter.Eventually.of_forall fun s =>
      norm_modulatedStripCellAverage_eq_integralLocal (x := x) (a := a) (T := T) s
  exact hNormEq.trans_isBigO hNormBigO.norm_left

/-- Helper for Exercise 21.3.1: translating a bi-infinite integer series by a fixed offset does
not change its sum. This is the reindexing step needed when the Fourier coefficients are first
identified in the shifted odd-mode normal form `n + 1 ↦ 2 * n + 1`. -/
theorem hasSum_int_add_right_iffLocal
    {f : ℤ → ℂ} {l : ℂ} (k : ℤ) :
    HasSum (fun n : ℤ ↦ f (n + k)) l ↔ HasSum f l := by
  -- Proof comment: `Equiv.addRight k` is a permutation of `ℤ`, so transporting the series across
  -- that equivalence preserves the `HasSum` statement exactly.
  simpa [Equiv.coe_addRight, Function.comp] using
    ((Equiv.addRight k).hasSum_iff (f := f) (a := l))

/-- Helper for Exercise 21.3.1: the same integer translation preserves summability of a
bi-infinite series. This isolates the shifted-index bookkeeping from the analytic coefficient
estimate. -/
theorem summable_int_add_right_iffLocal
    {f : ℤ → ℂ} (k : ℤ) :
    Summable (fun n : ℤ ↦ f (n + k)) ↔ Summable f := by
  -- Proof comment: summability is likewise invariant under the integer translation equivalence
  -- `n ↦ n + k`.
  simpa [Equiv.coe_addRight, Function.comp] using
    ((Equiv.addRight k).summable_iff (f := f))

/-- Helper for Exercise 21.3.1: the odd sine eigenfunction series is absolutely summable for
positive time. This isolates the analytic summability input from the still-open Fourier
coefficient computation. -/
theorem summable_oddSineSurvivalTermLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Summable (oddSineSurvivalTerm x a T) := by
  let decay : ℝ := (Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)
  have hDecay : 0 < decay := by
    dsimp [decay]
    positivity
  have hMajorant :
      Summable (fun k : ℕ ↦ Real.exp (-decay * (k + 1))) := by
    -- Proof comment: the majorant is a shifted geometric series with ratio `exp (-decay)`.
    have hRatioNonneg : 0 ≤ Real.exp (-decay) := by positivity
    have hRatioLtOne : Real.exp (-decay) < 1 := by
      simpa [Real.exp_lt_one_iff] using (neg_lt_zero.mpr hDecay)
    have hGeom :
        Summable (fun k : ℕ ↦ Real.exp (-decay) * (Real.exp (-decay)) ^ k) := by
      simpa [pow_succ', mul_assoc] using
        (summable_geometric_of_lt_one hRatioNonneg hRatioLtOne).mul_left (Real.exp (-decay))
    refine hGeom.congr ?_
    intro k
    calc
      Real.exp (-decay) * Real.exp (-decay) ^ k
          = Real.exp ((k : ℝ) * (-decay)) * Real.exp (-decay) := by
              rw [Real.exp_nat_mul, mul_comm]
      _ = Real.exp ((k : ℝ) * (-decay) + (-decay)) := by
            rw [Real.exp_add]
      _ = Real.exp (-decay * (k + 1)) := by ring
  refine Summable.of_norm_bounded hMajorant ?_
  intro k
  have hInvNonneg : 0 ≤ ((2 * k + 1 : ℝ)⁻¹) := by
    positivity
  have hInvLe : ((2 * k + 1 : ℝ)⁻¹) ≤ 1 := by
    have hk : 1 ≤ (2 * k + 1 : ℝ) := by
      nlinarith
    exact inv_le_one_of_one_le₀ hk
  have hSquareLower : (k + 1 : ℝ) ≤ (2 * k + 1 : ℝ) ^ 2 := by
    norm_num
    nlinarith
  have hExpLe :
      Real.exp (-decay * ((2 * k + 1 : ℝ) ^ 2)) ≤
        Real.exp (-decay * (k + 1)) := by
    apply Real.exp_monotone
    nlinarith [hSquareLower, hDecay]
  have hSinLe : |Real.sin ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)| ≤ 1 := by
    simpa using Real.abs_sin_le_one ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)
  -- Proof comment: bound the reciprocal prefactor and the sine term by `1`, then compare the
  -- Gaussian decay against the simpler exponential majorant `exp (-decay * (k + 1))`.
  calc
    ‖oddSineSurvivalTerm x a T k‖
        = |((2 * k + 1 : ℝ)⁻¹) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)) *
            Real.sin ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)| := by
              simp [oddSineSurvivalTerm]
    _ = |((2 * k + 1 : ℝ)⁻¹)| *
          |Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))| *
          |Real.sin ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)| := by
            rw [abs_mul, abs_mul]
    _ ≤ 1 * |Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))| *
          |Real.sin ((((2 * k + 1 : ℝ) * Real.pi) * x) / a)| := by
          gcongr
          · simpa [abs_of_nonneg hInvNonneg] using hInvLe
    _ ≤ 1 * Real.exp (-decay * (k + 1)) * 1 := by
          gcongr
          · have hExpNonneg :
                0 ≤ Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)) := by
              positivity
            rw [abs_of_nonneg hExpNonneg]
            simpa [decay, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hExpLe
    _ = Real.exp (-decay * (k + 1)) := by ring

/-- Helper for Exercise 21.3.1: the Gaussian damping majorant behind the odd Fourier coefficients
is summable for positive time. -/
theorem summable_oddGaussianMajorantLocal
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    Summable (fun k : ℕ ↦
      ((2 * k + 1 : ℝ)⁻¹) *
        Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))) := by
  let decay : ℝ := (Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)
  have hDecay : 0 < decay := by
    dsimp [decay]
    positivity
  have hMajorant :
      Summable (fun k : ℕ ↦ Real.exp (-decay * (k + 1))) := by
    -- Proof comment: the auxiliary comparison series is the same shifted geometric series used
    -- for the odd-sine summability argument, but without the extra sine factor.
    have hRatioNonneg : 0 ≤ Real.exp (-decay) := by positivity
    have hRatioLtOne : Real.exp (-decay) < 1 := by
      simpa [Real.exp_lt_one_iff] using (neg_lt_zero.mpr hDecay)
    have hGeom :
        Summable (fun k : ℕ ↦ Real.exp (-decay) * (Real.exp (-decay)) ^ k) := by
      simpa [pow_succ', mul_assoc] using
        (summable_geometric_of_lt_one hRatioNonneg hRatioLtOne).mul_left (Real.exp (-decay))
    refine hGeom.congr ?_
    intro k
    calc
      Real.exp (-decay) * Real.exp (-decay) ^ k
          = Real.exp ((k : ℝ) * (-decay)) * Real.exp (-decay) := by
              rw [Real.exp_nat_mul, mul_comm]
      _ = Real.exp ((k : ℝ) * (-decay) + (-decay)) := by
            rw [Real.exp_add]
      _ = Real.exp (-decay * (k + 1)) := by ring
  refine Summable.of_norm_bounded hMajorant ?_
  intro k
  have hInvNonneg : 0 ≤ ((2 * k + 1 : ℝ)⁻¹) := by
    positivity
  have hInvLe : ((2 * k + 1 : ℝ)⁻¹) ≤ 1 := by
    have hk : 1 ≤ (2 * k + 1 : ℝ) := by
      nlinarith
    exact inv_le_one_of_one_le₀ hk
  have hSquareLower : (k + 1 : ℝ) ≤ (2 * k + 1 : ℝ) ^ 2 := by
    norm_num
    nlinarith
  have hExpLe :
      Real.exp (-decay * ((2 * k + 1 : ℝ) ^ 2)) ≤
        Real.exp (-decay * (k + 1)) := by
    apply Real.exp_monotone
    nlinarith [hSquareLower, hDecay]
  -- Proof comment: bound the reciprocal prefactor by `1`, then compare the quadratic Gaussian
  -- decay against the simpler exponential majorant `exp (-decay * (k + 1))`.
  calc
    ‖((2 * k + 1 : ℝ)⁻¹) *
        Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))‖
        =
          |((2 * k + 1 : ℝ)⁻¹) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))| := by
              simp
    _ = |((2 * k + 1 : ℝ)⁻¹)| *
          |Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))| := by
            rw [abs_mul]
    _ ≤ 1 * |Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))| := by
          gcongr
          simpa [abs_of_nonneg hInvNonneg] using hInvLe
    _ ≤ 1 * Real.exp (-decay * (k + 1)) := by
          gcongr
          have hExpNonneg :
              0 ≤ Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)) := by
            positivity
          rw [abs_of_nonneg hExpNonneg]
          simpa [decay, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hExpLe
    _ = Real.exp (-decay * (k + 1)) := by ring

/-- Helper for Exercise 21.3.1: integrating the odd Fourier kernel over one strip cell produces
the explicit denominator `((2 * n + 1) * π * I)⁻¹` needed in the shifted coefficient formula. -/
theorem oddModeCellIntegralLocal
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    ∫ t in (0 : ℝ)..a,
        Complex.exp
          (((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) * t) : ℂ) * Complex.I) =
      -(((2 * a : ℝ) : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hOddInt_ne : (2 * n + 1 : ℤ) ≠ 0 := by omega
  have hOddReal_ne : (((2 * n + 1 : ℤ) : ℝ) * Real.pi) ≠ 0 := by
    refine mul_ne_zero ?_ Real.pi_ne_zero
    exact_mod_cast hOddInt_ne
  have hCoeff_ne :
      ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast div_ne_zero hOddReal_ne ha_ne
  -- Proof comment: this is the antiderivative evaluation for `exp (c * t)` at the odd frequency
  -- `c = (((2 * n + 1) * π) / a) * I`, followed by `exp ((2 * n + 1) * π * I) = -1`.
  calc
    ∫ t in (0 : ℝ)..a,
        Complex.exp
          (((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) * t) : ℂ) * Complex.I)
        =
          (Complex.exp
              (((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) * a) : ℂ) * Complex.I) - 1) /
            ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) : ℂ) * Complex.I) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (integral_exp_mul_complex
                  (a := (0 : ℝ))
                  (b := a)
                  (c := ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) : ℂ) * Complex.I))
                  hCoeff_ne)
    _ = (-1 - 1) / ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) : ℂ) * Complex.I) := by
          congr 1
          have hMul :
              ((((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a) * a) : ℂ) * Complex.I =
                (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) : ℂ) * Complex.I) := by
            field_simp [ha_ne]
          have hIntMul :
              (((((2 * n + 1 : ℤ) : ℝ) * Real.pi) : ℂ) * Complex.I) =
                (((2 * n + 1 : ℤ) : ℂ) * (Real.pi * Complex.I)) := by
            change ((((2 * n + 1 : ℤ) : ℂ) * (Real.pi : ℂ)) * Complex.I) =
              (((2 * n + 1 : ℤ) : ℂ) * (Real.pi * Complex.I))
            ring
          rw [hMul, hIntMul, Complex.exp_int_mul]
          have hNotEven : ¬ Even (2 * n + 1) := by
            intro hEven
            rcases hEven with ⟨k, hk⟩
            omega
          have hOdd : Odd (2 * n + 1) := Int.not_even_iff_odd.mp hNotEven
          rw [Complex.exp_pi_mul_I]
          simpa using (Odd.neg_one_zpow (α := ℂ) hOdd)
    _ = -(((2 * a : ℝ) : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)) := by
          field_simp [ha_ne, Complex.I_ne_zero, hOddReal_ne]
          have hCastTwo : (((2 * a : ℝ) : ℂ)) = (2 : ℂ) * a := by
            norm_num
          have hFinal :
              ((-1 - 1 : ℂ) * (a : ℂ) / (((2 * n + 1 : ℤ) : ℂ))) =
                -((((2 * a : ℝ) : ℂ) / (((2 * n + 1 : ℤ) : ℂ)))) := by
            rw [hCastTwo]
            ring
          simpa using hFinal

/-- Helper for Exercise 21.3.1: the universal complex odd-mode pair already collapses to the
real sine factor after the common Gaussian damping term is separated. -/
theorem complexOddModePair_eq_realSineLocal
    (theta lam d : ℝ) (hd : d ≠ 0) :
    ((2 : ℂ) / (d * Complex.I)) * Complex.exp (((theta : ℂ) * Complex.I) - lam) -
        ((2 : ℂ) / (d * Complex.I)) * Complex.exp (-((theta : ℂ) * Complex.I) - lam) =
      (((4 / d) * Real.exp (-lam) * Real.sin theta : ℝ) : ℂ) := by
  -- Proof comment: split off the common real Gaussian damping factor `exp (-lam)`, expand the
  -- two oscillatory phases with `Complex.exp_mul_I`, and simplify the resulting sine difference.
  rw [show (((theta : ℂ) * Complex.I) - lam) = ((theta : ℂ) * Complex.I) + (-lam : ℂ) by ring]
  rw [show (-((theta : ℂ) * Complex.I) - lam) = (-(theta : ℂ) * Complex.I) + (-lam : ℂ) by ring]
  rw [Complex.exp_add, Complex.exp_add]
  have hLam : Complex.exp (-↑lam) = ((Real.exp (-lam) : ℝ) : ℂ) := by
    simp
  rw [hLam]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp
  field_simp [hd]
  ring

/-- Helper for Exercise 21.3.1: the square of the odd Fourier frequency simplifies to the
textbook Gaussian damping exponent. -/
theorem oddModeQuadraticExponent_eqLocal
    {a : ℝ} (ha : 0 < a) {T : NNReal} (n : ℕ) :
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    (((T : ℝ) * (omega ^ (2 : ℕ))) / 2) =
      (((2 * n + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2) := by
  have hCast : ((((2 * n + 1 : ℤ) : ℝ))) = (2 * n + 1 : ℝ) := by
    norm_num
  -- Proof comment: rewrite the odd integer frequency with its natural-number spelling, then clear
  -- the nonzero denominator `a` once and let polynomial normalization finish.
  dsimp
  rw [hCast]
  field_simp [ha.ne']

/-- Helper for Exercise 21.3.1: multiplying the odd Fourier frequency by `x` gives the textbook
odd sine phase `((2n + 1) * π * x) / a`. -/
theorem oddModePhase_eqLocal
    {x a : ℝ} (ha : 0 < a) (n : ℕ) :
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    omega * x = ((((2 * n + 1 : ℝ) * Real.pi) * x) / a) := by
  have hCast : ((((2 * n + 1 : ℤ) : ℝ))) = (2 * n + 1 : ℝ) := by
    norm_num
  -- Proof comment: after replacing the odd integer cast by the corresponding natural-number
  -- scalar, the phase identity is just the same denominator-clearing normalization.
  dsimp
  rw [hCast]
  field_simp [ha.ne']

/-- Helper for Exercise 21.3.1: once the positive and negative odd Gaussian frequencies are frozen
explicitly, their pair already equals the textbook odd-sine term. -/
theorem oddGaussianModePair_eq_oddSineTermLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) (n : ℕ) :
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    let kappa : ℂ := (2 : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
    kappa * charFun (gaussianReal x T) omega -
        kappa * charFun (gaussianReal x T) (-omega) =
      (((4 / Real.pi) * oddSineSurvivalTerm x a T n) : ℂ) := by
  let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
  let kappa : ℂ := (2 : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
  have hOddInt_ne : (2 * n + 1 : ℤ) ≠ 0 := by omega
  have hOddReal_ne : (((2 * n + 1 : ℤ) : ℝ) * Real.pi) ≠ 0 := by
    refine mul_ne_zero ?_ Real.pi_ne_zero
    exact_mod_cast hOddInt_ne
  have hCharPos :
      charFun (gaussianReal x T) omega =
        Complex.exp
          ((((omega * x) : ℂ) * Complex.I) -
            (((T : ℝ) * (omega ^ (2 : ℕ))) / 2 : ℝ)) := by
    -- Proof comment: freeze the positive odd Fourier mode using the dedicated Gaussian
    -- characteristic-function normalization.
    simpa [omega] using
      gaussianCharFun_oddIntModeLocal
        (x := x) (a := a) (T := T) (n := (n : ℤ))
  have hCharNeg :
      charFun (gaussianReal x T) (-omega) =
        Complex.exp
          (-(((omega * x) : ℂ) * Complex.I) -
            (((T : ℝ) * (omega ^ (2 : ℕ))) / 2 : ℝ)) := by
    -- Proof comment: the negative odd mode is the complex conjugate of the positive one, which
    -- flips only the oscillatory phase.
    rw [gaussianCharFun_neg_oddIntModeLocal
      (x := x) (a := a) (T := T) (n := (n : ℤ))]
    rw [hCharPos]
    simp
  have hPhasePair :
      kappa * charFun (gaussianReal x T) omega -
          kappa * charFun (gaussianReal x T) (-omega) =
        (((4 / ((((2 * n + 1 : ℤ) : ℝ) * Real.pi))) *
            Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) *
            Real.sin (omega * x) : ℝ) : ℂ) := by
    -- Proof comment: after both Gaussian modes are frozen explicitly, the universal complex
    -- odd-mode pair lemma collapses them to the real sine factor.
    rw [hCharPos, hCharNeg]
    simpa [omega, kappa] using
      complexOddModePair_eq_realSineLocal
        (theta := omega * x)
        (lam := (((T : ℝ) * (omega ^ (2 : ℕ))) / 2))
        (d := (((2 * n + 1 : ℤ) : ℝ) * Real.pi))
        hOddReal_ne
  have hOddCast : (((2 * n + 1 : ℤ) : ℝ)) = (2 * n + 1 : ℝ) := by
    norm_num
  have hExp :
      (((T : ℝ) * (omega ^ (2 : ℕ))) / 2) =
        (((2 * n + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2) := by
    -- Proof comment: normalize the Gaussian damping exponent to the textbook odd-mode shape.
    simpa [omega] using oddModeQuadraticExponent_eqLocal (a := a) (T := T) ha n
  have hPhase :
      omega * x = ((((2 * n + 1 : ℝ) * Real.pi) * x) / a) := by
    -- Proof comment: rewrite the odd Fourier phase to the exact sine argument of the textbook
    -- series term.
    simpa [omega] using oddModePhase_eqLocal (x := x) (a := a) ha n
  have hOddNat_ne : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  calc
    kappa * charFun (gaussianReal x T) omega -
        kappa * charFun (gaussianReal x T) (-omega)
        =
          (((4 / ((((2 * n + 1 : ℤ) : ℝ) * Real.pi))) *
              Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) *
              Real.sin (omega * x) : ℝ) : ℂ) := hPhasePair
    _ = (((4 / Real.pi) * oddSineSurvivalTerm x a T n) : ℂ) := by
          -- Proof comment: substitute the normalized damping and phase expressions and clear the
          -- remaining reciprocal factor `((2 * n + 1) * π)⁻¹`.
          congr 1
          rw [hOddCast, hExp, hPhase, oddSineSurvivalTerm]
          field_simp [Real.pi_ne_zero, hOddNat_ne]
          ring

-- Route correction: the stable Fourier owner is the single shifted coefficient at index `n`.
-- The paired `HasSum` theorem and the full `ℤ`-summability statement below are now downstream
-- transports of this one explicit odd-mode identity.
/-- Helper for Exercise 21.3.1: after translating by one strip cell and rescaling by `a`, the
oscillatory Gaussian-density integral is exactly the scaled characteristic function at the
frequency `-omega`. -/
theorem gaussianOscillatoryIntegral_eq_invScale_charFunLocal
    {x a omega t : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    ∫ s : ℝ,
        Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
          ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) =
      (1 / a : ℂ) * charFun (gaussianReal x T) (-omega) := by
  let g : ℝ → ℂ := fun y ↦
    Complex.exp ((↑(-(omega * y)) : ℂ) * Complex.I) * ((gaussianPDFReal x T y : ℝ) : ℂ)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hShift :
      (∫ s : ℝ, g (a * s + t)) = ∫ s : ℝ, g (a * s) := by
    have hRewrite :
        (fun s : ℝ ↦ g (a * s + t)) = fun s : ℝ ↦ g (a * (s + t / a)) := by
      funext s
      congr 1
      field_simp [ha_ne]
    -- Proof comment: rewrite the affine shift as a translate in the integration variable, then
    -- remove that translation by Haar invariance of Lebesgue measure on `ℝ`.
    rw [hRewrite]
    simpa using integral_add_right_eq_self (fun s : ℝ ↦ g (a * s)) (t / a)
  have hScaleCore :
      (∫ s : ℝ, g (a * s)) = |a⁻¹| • ∫ y : ℝ, g y := by
    -- Proof comment: the remaining affine map is pure scaling, so the whole-line integral picks
    -- up the Jacobian factor `|a⁻¹|`.
    exact Measure.integral_comp_mul_left g a
  have hScaleSmul :
      ((|a⁻¹| : ℝ) • ∫ y : ℝ, g y : ℂ) = (1 / a : ℂ) * ∫ y : ℝ, g y := by
    -- Proof comment: because `a > 0`, the real Jacobian `|a⁻¹|` is exactly the complex scalar
    -- `1 / a` appearing in the target statement.
    rw [abs_of_pos (inv_pos.mpr ha), Algebra.smul_def]
    simp
  have hChar :
      (∫ y : ℝ, g y) = charFun (gaussianReal x T) (-omega) := by
    calc
      (∫ y : ℝ, g y)
          = ∫ y : ℝ,
              (gaussianPDFReal x T y : ℝ) •
                Complex.exp ((↑((-omega) * y) : ℂ) * Complex.I) := by
                  congr with y
                  simp [g, mul_comm]
      _ = ∫ y,
            Complex.exp ((↑((-omega) * y) : ℂ) * Complex.I) ∂(gaussianReal x T) := by
            -- Proof comment: replace the Gaussian law by its density against Lebesgue measure.
            symm
            simpa using
              (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
                (μ := x) (v := T)
                (f := fun y : ℝ ↦ Complex.exp ((↑((-omega) * y) : ℂ) * Complex.I))
                (hv := ne_of_gt hT))
      _ = charFun (gaussianReal x T) (-omega) := by
            -- Proof comment: the remaining whole-line oscillatory Gaussian integral is exactly
            -- the characteristic function evaluated at frequency `-omega`.
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (MeasureTheory.charFun_apply_real (μ := gaussianReal x T) (-omega)).symm
  -- Proof comment: rewrite the affine oscillatory integral to one scaled whole-line Gaussian
  -- Fourier integral, then identify that remaining integral with the characteristic function.
  calc
    ∫ s : ℝ,
        Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
          ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)
        = ∫ s : ℝ, g (a * s + t) := by
            rfl
    _ = ∫ s : ℝ, g (a * s) := hShift
    _ = |a⁻¹| • ∫ y : ℝ, g y := hScaleCore
    _ = (1 / a : ℂ) * ∫ y : ℝ, g y := hScaleSmul
    _ = (1 / a : ℂ) * charFun (gaussianReal x T) (-omega) := by rw [hChar]

/-- Helper for Exercise 21.3.1: the two-variable oscillatory kernel used in the Fourier-coefficient
Fubini step is integrable on `Set.uIoc 0 a × ℝ`. Both exponential factors have unit norm, so the
kernel reduces to an affine translate/dilate of the Gaussian density. -/
theorem shiftedFourierKernelProdIntegrableLocal
    {x a omega : ℝ} (ha : 0 < a) {T : NNReal} (_hT : 0 < T) :
    Integrable
      (Function.uncurry fun t s : ℝ ↦
        Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
            ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)))
      (((volume.restrict (Set.uIoc (0 : ℝ) a)).prod volume)) := by
  let kernel : ℝ × ℝ → ℂ :=
    Function.uncurry fun t s : ℝ ↦
      Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
        (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
          ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ))
  change Integrable kernel (((volume.restrict (Set.uIoc (0 : ℝ) a)).prod volume))
  have hKernelMeas :
      AEStronglyMeasurable kernel
        (((volume.restrict (Set.uIoc (0 : ℝ) a)).prod volume)) := by
    have hKernelMeasurable : Measurable kernel := by
      -- Proof comment: every factor in the frozen oscillatory kernel is Borel measurable in
      -- `(t, s)`, so the full uncurry is measurable on the product space.
      dsimp [kernel, Function.uncurry]
      fun_prop
    exact hKernelMeasurable.aestronglyMeasurable
  rw [integrable_prod_iff hKernelMeas]
  constructor
  · refine Filter.Eventually.of_forall fun t ↦ ?_
    have hGaussianSlice :
        Integrable (fun s : ℝ ↦ ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
      have hBase : Integrable (fun y : ℝ ↦ ((gaussianPDFReal x T y : ℝ) : ℂ)) := by
        -- Proof comment: the complex Gaussian density is integrable because the real density is.
        simpa using (ProbabilityTheory.integrable_gaussianPDFReal x T).ofReal
      have hShifted :
          Integrable (fun y : ℝ ↦ ((gaussianPDFReal x T (y + t) : ℝ) : ℂ)) := by
        -- Proof comment: translating an integrable whole-line Gaussian density preserves
        -- integrability by Haar invariance of Lebesgue measure.
        simpa using
          (measurePreserving_add_right volume t).integrable_comp_of_integrable hBase
      have hScaled :
          Integrable (fun s : ℝ ↦ ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
        -- Proof comment: scaling by the positive factor `a` preserves whole-line integrability.
        simpa [add_comm, add_left_comm, add_assoc] using
          hShifted.comp_mul_left' (R := a) ha.ne'
      exact hScaled
    have hSectionMeas :
        AEStronglyMeasurable
          (fun s : ℝ ↦
            Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)))
          volume := by
      have hSectionMeasurable :
          Measurable
            (fun s : ℝ ↦
              Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
                (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                  ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ))) := by
        -- Proof comment: the fixed-`t` section remains a measurable product of the same two
        -- oscillatory factors and the affine Gaussian density.
        fun_prop
      exact hSectionMeasurable.aestronglyMeasurable
    -- Proof comment: both exponential factors have norm `1`, so each fixed-`t` section is
    -- integrable with exactly the same norm as the affine Gaussian slice.
    refine Integrable.congr' hGaussianSlice hSectionMeas ?_
    filter_upwards with s
    simp [norm_mul, Complex.norm_exp]
  · have hInnerEq :
        (fun t : ℝ ↦
          ∫ s : ℝ,
            ‖Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
                (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                  ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ))‖) =
          fun _ : ℝ ↦ (1 / a : ℝ) := by
      funext t
      have hGaussianComplex :
          (∫ s : ℝ, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) = (1 / a : ℂ) := by
        -- Proof comment: the already-proved affine oscillatory Gaussian integral collapses to the
        -- scaled total mass when the frequency parameter is `0`.
        simpa using
          gaussianOscillatoryIntegral_eq_invScale_charFunLocal
            (x := x) (a := a) (omega := 0) (t := t) ha _hT
      have hGaussianReal :
          ∫ s : ℝ, gaussianPDFReal x T (a * s + t) = 1 / a := by
        apply Complex.ofReal_injective
        simpa [integral_complex_ofReal] using hGaussianComplex
      -- Proof comment: the norm of the frozen kernel is exactly the affine Gaussian density, so
      -- the inner integral is the constant `1 / a`.
      calc
        ∫ s : ℝ,
            ‖Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
                (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                  ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ))‖
            = ∫ s : ℝ, gaussianPDFReal x T (a * s + t) := by
                congr 1
                ext s
                simp [norm_mul, Complex.norm_exp]
        _ = 1 / a := hGaussianReal
    rw [hInnerEq]
    have hFinite :
        volume (Set.uIoc (0 : ℝ) a) ≠ ∞ := by
      simpa [Set.uIoc_of_le ha.le] using measure_Ioc_lt_top (0 : ℝ) a
    -- Proof comment: once the outer integrand is the constant `1 / a`, integrability reduces to
    -- the finite measure of the strip base interval `(0, a]`.
    simpa [IntegrableOn] using
      (integrableOn_const (μ := volume) (s := Set.uIoc (0 : ℝ) a) (C := (1 / a : ℝ)) hFinite)

/-- Helper for Exercise 21.3.1: after the Fubini/change-of-variables step, the shifted Fourier
coefficient is the odd cell integral times the Gaussian characteristic function at the negative odd
frequency. -/
-- TODO: swap the fixed cell integral with the Fourier integral and normalize the affine change of
-- variables `y = a * s + t`; the change-of-variables/characteristic-function part is already
-- isolated in `gaussianOscillatoryIntegral_eq_invScale_charFunLocal`.
theorem shiftedFourierCoefficient_eq_cellIntegral_mul_charFunLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (_hT : 0 < T) (n : ℤ) :
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ)) =
      ((1 / a : ℂ) *
        (∫ t in (0 : ℝ)..a, Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I))) *
        charFun (gaussianReal x T) (-omega) := by
  dsimp
  let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
  have hKernelInt :
      Integrable
        (Function.uncurry fun t s : ℝ ↦
          Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
            (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
              ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)))
        (((volume.restrict (Set.uIoc (0 : ℝ) a)).prod volume)) := by
    -- Proof comment: keep exactly the frozen product-kernel spelling already used by the
    -- integrability owner theorem, so the later Fubini step is a direct rewrite.
    simpa [omega] using
      shiftedFourierKernelProdIntegrableLocal
        (x := x) (a := a) (omega := omega) ha _hT
  have hPointwise :
      (fun s : ℝ ↦
        Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
          modulatedStripCellAverage x a T s) =
        (fun s : ℝ ↦
          ∫ t in (0 : ℝ)..a,
            Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ))) := by
    funext s
    calc
      Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
          modulatedStripCellAverage x a T s
          =
        Complex.exp ((↑(-((((2 * n + 1 : ℤ) : ℝ) * Real.pi) * s)) : ℂ) * Complex.I) *
          ∫ t in (0 : ℝ)..a, ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ) := by
            -- Proof comment: the modulation factor and the Fourier kernel combine to the unique
            -- odd frequency `((2 * n + 1) * π) / a`.
            simpa [omega] using
              shiftedFourierKernel_mul_cellAverage_eq_oddModeLocal
                (x := x) (a := a) (T := T) n s
      _ = ∫ t in (0 : ℝ)..a,
            Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
            -- Proof comment: insert the fixed-cell oscillatory factor inside the interval
            -- integral so that Fubini can use the exact product kernel from `hKernelInt`.
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with t
            have hExp :
                Complex.exp ((↑(-((((2 * n + 1 : ℤ) : ℝ) * Real.pi) * s)) : ℂ) * Complex.I) =
                  Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
                    Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) := by
              rw [← Complex.exp_add]
              congr 1
              field_simp [omega, (ne_of_gt ha)]
              ring
            rw [hExp]
            ring
  calc
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
        =
          ∫ s : ℝ,
            Complex.exp ((↑(-2 * Real.pi * s * (((n + 1 : ℤ) : ℝ))) : ℂ) * Complex.I) *
              modulatedStripCellAverage x a T s := by
                -- Proof comment: unfold the real Fourier transform at the shifted integer mode.
                rw [Real.fourier_real_eq_integral_exp_smul]
                simp [smul_eq_mul]
    _ =
        ∫ s : ℝ,
          ∫ t in (0 : ℝ)..a,
            Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
          rw [hPointwise]
    _ =
        ∫ t in (0 : ℝ)..a,
          ∫ s : ℝ,
            Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(-(omega * (a * s + t))) : ℂ) * Complex.I) *
                ((gaussianPDFReal x T (a * s + t) : ℝ) : ℂ)) := by
          -- Proof comment: swap the whole-line Fourier integral with the fixed strip-cell
          -- interval integral using the already frozen product-kernel integrability.
          rw [(intervalIntegral_integral_swap hKernelInt).symm]
    _ =
        ∫ t in (0 : ℝ)..a,
          Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
            ((1 / a : ℂ) * charFun (gaussianReal x T) (-omega)) := by
          -- Proof comment: the inner whole-line affine Gaussian integral is exactly the scaled
          -- characteristic function at the negative odd frequency.
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with t
          rw [gaussianOscillatoryIntegral_eq_invScale_charFunLocal
            (x := x) (a := a) (omega := omega) (t := t) ha _hT]
    _ =
        (∫ t in (0 : ℝ)..a, Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)) *
          ((1 / a : ℂ) * charFun (gaussianReal x T) (-omega)) := by
            rw [intervalIntegral.integral_mul_const]
    _ =
        ((1 / a : ℂ) *
          (∫ t in (0 : ℝ)..a, Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I))) *
          charFun (gaussianReal x T) (-omega) := by
            ring

/-- Helper for Exercise 21.3.1: the shifted Fourier coefficient at index `n` is the odd-mode
Gaussian characteristic function multiplied by the explicit strip-cell factor. -/
-- Route correction: this coefficient formula needs `hT : 0 < T`; at `T = 0` the strip-density
-- side vanishes while the Gaussian characteristic function side does not.
-- TODO: start from `shiftedFourierKernel_mul_cellAverage_eq_oddModeLocal`, swap the fixed
-- `[0,a]` cell integral with the Fourier integral by one Fubini step, reduce the cell factor with
-- `oddModeCellIntegralLocal`, and identify the remaining Gaussian integral with
-- `charFun (gaussianReal x T)` at the negative odd frequency.
theorem shiftedFourierCoefficient_eq_negOddModeLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) (n : ℤ) :
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    let kappa : ℂ := (2 : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ)) =
      -(kappa * charFun (gaussianReal x T) (-omega)) := by
  -- TODO: combine `shiftedFourierCoefficient_eq_cellIntegral_mul_charFunLocal` with
  -- `oddModeCellIntegralLocal`, then normalize the remaining scalar factor without relying on
  -- brittle `ring` normal forms for the local `omega` abbreviation.
  dsimp
  let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
  let kappa : ℂ := (2 : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
  have hCell :
      (1 / a : ℂ) *
          (∫ t in (0 : ℝ)..a, Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)) =
        -kappa := by
    -- Proof comment: the explicit cell integral isolates the odd denominator
    -- `((2 * n + 1) * π * I)⁻¹`, leaving only a one-line scalar normalization.
    rw [oddModeCellIntegralLocal (a := a) ha n]
    dsimp [kappa, omega]
    field_simp [Complex.I_ne_zero, (ne_of_gt ha), Real.pi_ne_zero]
    ring
  calc
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
        =
          ((1 / a : ℂ) *
            (∫ t in (0 : ℝ)..a, Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I))) *
            charFun (gaussianReal x T) (-omega) := by
              -- Proof comment: start from the Fubini/characteristic-function coefficient owner.
              simpa [omega] using
                shiftedFourierCoefficient_eq_cellIntegral_mul_charFunLocal
                  (x := x) (a := a) (T := T) ha hT n
    _ = (-kappa) * charFun (gaussianReal x T) (-omega) := by rw [hCell]
    _ = -(kappa * charFun (gaussianReal x T) (-omega)) := by ring

/-- Helper for Exercise 21.3.1: pairing the shifted Fourier coefficients at `n` and `-(n + 1)`
already gives the odd-sine `ℕ`-series. -/
theorem shiftedFourierCoefficientPairs_hasSum_oddSineLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    let coeff : ℤ → ℂ := fun n ↦
      𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
    HasSum (fun n : ℕ ↦ coeff n + coeff (-(n + 1 : ℤ)))
      (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
  let coeff : ℤ → ℂ := fun n ↦
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
  have hPointwise :
      ∀ n : ℕ,
        coeff n + coeff (-(n + 1 : ℤ)) =
          (((4 / Real.pi) * oddSineSurvivalTerm x a T n) : ℂ) := by
    intro n
    let omega : ℝ := ((((2 * n + 1 : ℤ) : ℝ) * Real.pi) / a)
    let kappa : ℂ := (2 : ℂ) / ((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
    have hPos :
        coeff n = -(kappa * charFun (gaussianReal x T) (-omega)) := by
      -- Proof comment: the positive branch is exactly the normalized single-coefficient formula
      -- at the odd mode indexed by `n`.
      simpa [coeff, omega, kappa] using
        shiftedFourierCoefficient_eq_negOddModeLocal
          (x := x) (a := a) (T := T) ha hT (n := (n : ℤ))
    have hOddInt :
        (2 * (-(n + 1 : ℤ)) + 1 : ℤ) = -((2 * n + 1 : ℤ)) := by
      omega
    have hDen :
        ((((2 * (-(n + 1 : ℤ)) + 1 : ℤ) : ℂ) * Real.pi) * Complex.I) =
          -(((((2 * n + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)) := by
      rw [show (((2 * (-(n + 1 : ℤ)) + 1 : ℤ) : ℂ)) = -(((2 * n + 1 : ℤ) : ℂ)) by
        exact_mod_cast hOddInt]
      ring
    have hNeg :
        coeff (-(n + 1 : ℤ)) = kappa * charFun (gaussianReal x T) omega := by
      -- Proof comment: rewriting the reflected index `-(n + 1)` identifies the second branch
      -- with the positive odd Gaussian mode from the same shell pair.
      simpa [coeff, omega, kappa, hDen,
        oddModeFrequency_neg_add_oneLocal (a := a) n] using
        shiftedFourierCoefficient_eq_negOddModeLocal
          (x := x) (a := a) (T := T) ha hT (n := (-(n + 1 : ℤ)))
    calc
      coeff n + coeff (-(n + 1 : ℤ))
          = -(kappa * charFun (gaussianReal x T) (-omega)) +
              kappa * charFun (gaussianReal x T) omega := by rw [hPos, hNeg]
      _ = kappa * charFun (gaussianReal x T) omega -
            kappa * charFun (gaussianReal x T) (-omega) := by ring
      _ = (((4 / Real.pi) * oddSineSurvivalTerm x a T n) : ℂ) := by
            simpa [omega, kappa] using
              oddGaussianModePair_eq_oddSineTermLocal
                (x := x) (a := a) (T := T) ha hT n
  have hOddSineReal :
      HasSum (fun n : ℕ ↦ (4 / Real.pi) * oddSineSurvivalTerm x a T n)
        ((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) := by
    -- Proof comment: the textbook odd-sine series is already known to be summable, so scaling it
    -- by `4 / π` preserves its `HasSum`.
    simpa using
      (summable_oddSineSurvivalTermLocal (x := x) (a := a) (T := T) ha hT).hasSum.mul_left
        (4 / Real.pi)
  have hOddSineComplex :
      HasSum (fun n : ℕ ↦ (((4 / Real.pi) * oddSineSurvivalTerm x a T n) : ℂ))
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: the paired coefficient identity lands in `ℂ`, so move the real odd-sine
    -- `HasSum` across the standard complex coercion.
    exact Complex.hasSum_ofReal.mpr hOddSineReal
  -- Proof comment: replace the target coefficient pair termwise by the pointwise odd-sine
  -- identity proved above.
  convert hOddSineComplex using 1
  ext n
  exact hPointwise n

/-- Helper for Exercise 21.3.1: the explicit odd-mode prefactor has norm
`(2 / π) * (2k + 1)⁻¹`, which is the deterministic part of the Fourier majorant. -/
theorem oddModeKappaNorm_eq_majorantFactorLocal
    (k : ℕ) :
    let kappa : ℂ := (2 : ℂ) / ((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
    ‖kappa‖ = (2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹) := by
  dsimp
  let kappa : ℂ := (2 : ℂ) / ((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
  have hOddPos : 0 < (2 * k + 1 : ℝ) := by positivity
  have hCast :
      ((((2 * k + 1 : ℤ) : ℂ) * Real.pi) : ℂ) =
        ((((2 * k + 1 : ℝ) * Real.pi : ℝ)) : ℂ) := by
    norm_num
  have hDenNorm :
      ‖((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)‖ =
        (2 * k + 1 : ℝ) * Real.pi := by
    have hNonneg : 0 ≤ (2 * k + 1 : ℝ) * Real.pi := by
      positivity
    calc
      ‖((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)‖
          = ‖((((2 * k + 1 : ℝ) * Real.pi : ℝ)) : ℂ)‖ * ‖Complex.I‖ := by
              rw [norm_mul, hCast]
      _ = |(2 * k + 1 : ℝ) * Real.pi| * 1 := by
            rw [Complex.norm_real, Complex.norm_I]
      _ = (2 * k + 1 : ℝ) * Real.pi := by
            simp [abs_of_nonneg hNonneg]
  calc
    ‖kappa‖ = ‖(2 : ℂ)‖ / ‖((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)‖ := by
      simp [kappa, norm_div]
    _ = 2 / ((2 * k + 1 : ℝ) * Real.pi) := by
      rw [hDenNorm]
      norm_num
    _ = (2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹) := by
      field_simp [Real.pi_ne_zero, hOddPos.ne']

/-- Helper for Exercise 21.3.1: the nonnegative shifted Fourier branch has exactly the odd
Gaussian majorant norm. -/
theorem shiftedFourierCoefficient_natNorm_eq_majorantLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) (k : ℕ) :
    let coeff : ℤ → ℂ := fun n ↦
      𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
    ‖coeff k‖ =
      (2 / Real.pi) *
        (((2 * k + 1 : ℝ)⁻¹) *
          Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))) := by
  dsimp
  let coeff : ℤ → ℂ := fun n ↦
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
  let omega : ℝ := ((((2 * k + 1 : ℤ) : ℝ) * Real.pi) / a)
  let kappa : ℂ := (2 : ℂ) / ((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
  have hCharNeg :
      charFun (gaussianReal x T) (-omega) =
        Complex.exp
          (-(((omega * x) : ℂ) * Complex.I) -
            (((T : ℝ) * (omega ^ (2 : ℕ))) / 2 : ℝ)) := by
    -- Proof comment: the negative odd mode is the complex conjugate of the positive one, so only
    -- the oscillatory phase changes sign.
    rw [gaussianCharFun_neg_oddIntModeLocal
      (x := x) (a := a) (T := T) (n := (k : ℤ))]
    rw [gaussianCharFun_oddIntModeLocal
      (x := x) (a := a) (T := T) (n := (k : ℤ))]
    simp [omega]
  have hCoeff :
      coeff k = -(kappa * charFun (gaussianReal x T) (-omega)) := by
    -- Proof comment: normalize the `k`th shifted Fourier coefficient to the odd Gaussian mode.
    simpa [coeff, omega, kappa] using
      shiftedFourierCoefficient_eq_negOddModeLocal
        (x := x) (a := a) (T := T) ha hT (n := (k : ℤ))
  have hCharNorm :
      ‖charFun (gaussianReal x T) (-omega)‖ =
        Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) := by
    -- Proof comment: the negative odd mode has the same norm as the explicit Gaussian
    -- characteristic function, and only the real damping term survives.
    rw [hCharNeg]
    simp [Complex.norm_exp]
  have hKappaNorm :
      ‖kappa‖ = (2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹) := by
    -- Proof comment: reuse the scalar odd-mode norm package instead of redoing denominator
    -- algebra inside the branch proof.
    simpa [kappa] using oddModeKappaNorm_eq_majorantFactorLocal k
  have hExp :
      (((T : ℝ) * (omega ^ (2 : ℕ))) / 2) =
        (((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2) := by
    -- Proof comment: rewrite the odd-mode damping exponent into the textbook majorant form.
    simpa [omega] using oddModeQuadraticExponent_eqLocal (a := a) (T := T) ha k
  calc
    ‖coeff k‖ = ‖-(kappa * charFun (gaussianReal x T) (-omega))‖ := by rw [hCoeff]
    _ = ‖kappa‖ * ‖charFun (gaussianReal x T) (-omega)‖ := by
          simp [norm_mul]
    _ = ((2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹)) *
          Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) := by
            rw [hKappaNorm, hCharNorm]
    _ = (2 / Real.pi) *
          (((2 * k + 1 : ℝ)⁻¹) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))) := by
          rw [hExp]
          ring

/-- Helper for Exercise 21.3.1: the reflected negative shifted Fourier branch is controlled by
the same odd Gaussian majorant as the nonnegative branch. -/
theorem shiftedFourierCoefficient_negAddOneNorm_eq_majorantLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) (k : ℕ) :
    let coeff : ℤ → ℂ := fun n ↦
      𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
    ‖coeff (-(k + 1 : ℤ))‖ =
      (2 / Real.pi) *
        (((2 * k + 1 : ℝ)⁻¹) *
          Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))) := by
  dsimp
  let coeff : ℤ → ℂ := fun n ↦
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
  let omega : ℝ := ((((2 * k + 1 : ℤ) : ℝ) * Real.pi) / a)
  let kappa : ℂ := (2 : ℂ) / ((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)
  have hOddInt :
      (2 * (-(k + 1 : ℤ)) + 1 : ℤ) = -((2 * k + 1 : ℤ)) := by
    omega
  have hIndexOmega :
      ((((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℝ) * Real.pi) / a) = -omega := by
    simpa [omega] using oddModeFrequency_neg_add_oneLocal (a := a) k
  have hDen :
      ((((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℂ) * Real.pi) * Complex.I) =
        -(((((2 * k + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)) := by
    rw [show (((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℂ)) = -(((2 * k + 1 : ℤ) : ℂ)) by
      exact_mod_cast hOddInt]
    ring
  have hKappaNeg :
      (2 : ℂ) / ((((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℂ) * Real.pi) * Complex.I) = -kappa := by
    rw [hDen, kappa]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
    ring
  have hCoeff :
      coeff (-(k + 1 : ℤ)) = kappa * charFun (gaussianReal x T) omega := by
    -- Proof comment: the reflected index `-(k + 1)` flips the odd frequency sign and the
    -- denominator sign, leaving the same positive-frequency Gaussian mode.
    have hRaw := shiftedFourierCoefficient_eq_negOddModeLocal
      (x := x) (a := a) (T := T) ha hT (n := (-(k + 1 : ℤ)))
    calc
      coeff (-(k + 1 : ℤ))
          =
            -(((2 : ℂ) / ((((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℂ) * Real.pi) * Complex.I)) *
              charFun (gaussianReal x T)
                (-(((((2 * (-(k + 1 : ℤ)) + 1 : ℤ) : ℝ) * Real.pi) / a)))) := by
                  simpa [coeff] using hRaw
      _ = -((-kappa) * charFun (gaussianReal x T) omega) := by
            rw [hKappaNeg, hIndexOmega]
      _ = kappa * charFun (gaussianReal x T) omega := by
            ring
  have hCharPos :
      charFun (gaussianReal x T) omega =
        Complex.exp
          ((((omega * x) : ℂ) * Complex.I) -
            (((T : ℝ) * (omega ^ (2 : ℕ))) / 2 : ℝ)) := by
    -- Proof comment: freeze the positive odd Gaussian mode explicitly before taking norms.
    rw [gaussianCharFun_oddIntModeLocal
      (x := x) (a := a) (T := T) (n := (k : ℤ))]
    simp [omega]
  have hCharNorm :
      ‖charFun (gaussianReal x T) omega‖ =
        Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) := by
    -- Proof comment: the positive odd Gaussian mode has norm exactly equal to its real damping
    -- factor.
    rw [hCharPos]
    simp [Complex.norm_exp]
  have hKappaNorm :
      ‖kappa‖ = (2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹) := by
    -- Proof comment: the reflected branch keeps the same odd scalar prefactor norm.
    simpa [kappa] using oddModeKappaNorm_eq_majorantFactorLocal k
  have hExp :
      (((T : ℝ) * (omega ^ (2 : ℕ))) / 2) =
        (((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2) := by
    -- Proof comment: the Gaussian damping exponent is unchanged under the reflected branch.
    simpa [omega] using oddModeQuadraticExponent_eqLocal (a := a) (T := T) ha k
  calc
    ‖coeff (-(k + 1 : ℤ))‖ = ‖kappa * charFun (gaussianReal x T) omega‖ := by rw [hCoeff]
    _ = ‖kappa‖ * ‖charFun (gaussianReal x T) omega‖ := by
          simp [norm_mul]
    _ = ((2 / Real.pi) * ((2 * k + 1 : ℝ)⁻¹)) *
          Real.exp (-(((T : ℝ) * (omega ^ (2 : ℕ))) / 2)) := by
            rw [hKappaNorm, hCharNorm]
    _ = (2 / Real.pi) *
          (((2 * k + 1 : ℝ)⁻¹) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2))) := by
          rw [hExp]
          ring

/-- Helper for Exercise 21.3.1: the shifted Fourier coefficient series is summable on `ℤ`. -/
theorem summable_shiftedFourierCoefficientsLocal
    {x a : ℝ} (_ha : 0 < a) {T : NNReal} (_hT : 0 < T) :
    let coeff : ℤ → ℂ := fun n ↦
      𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
    Summable coeff := by
  let coeff : ℤ → ℂ := fun n ↦
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
  have hMajorant :
      Summable (fun k : ℕ ↦
        (2 / Real.pi) *
          (((2 * k + 1 : ℝ)⁻¹) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * (T : ℝ)) / (2 * a ^ 2)))) := by
    -- Proof comment: scale the already-proved odd Gaussian majorant by the deterministic factor
    -- `2 / π` coming from the odd cell integral.
    simpa [mul_assoc] using
      (summable_oddGaussianMajorantLocal (a := a) _ha _hT).mul_left (2 / Real.pi)
  have hNat :
      Summable (fun k : ℕ ↦ coeff k) := by
    -- Proof comment: the nonnegative branch is exactly the normalized odd Gaussian majorant on
    -- `ℕ`.
    refine Summable.of_norm_bounded hMajorant ?_
    intro k
    simpa [coeff] using
      le_of_eq (shiftedFourierCoefficient_natNorm_eq_majorantLocal
        (x := x) (a := a) (T := T) _ha _hT k)
  have hNeg :
      Summable (fun k : ℕ ↦ coeff (-(k + 1 : ℤ))) := by
    -- Proof comment: the reflected negative branch obeys the same majorant after the
    -- `n ↦ -(k + 1)` index transport.
    refine Summable.of_norm_bounded hMajorant ?_
    intro k
    simpa [coeff] using
      le_of_eq (shiftedFourierCoefficient_negAddOneNorm_eq_majorantLocal
        (x := x) (a := a) (T := T) _ha _hT k)
  -- Proof comment: recombine the two `ℕ`-indexed branches with the standard `ℤ`-series
  -- decomposition.
  exact Summable.of_nat_of_neg_add_one hNat hNeg

/-- Helper for Exercise 21.3.1: after shifting the Fourier index by `+1`, the remaining Poisson
input is a pure regrouping of the paired coefficient series. -/
theorem shiftedFourierCoefficients_hasSum_oddSineLocal
    {x a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℤ ↦ 𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ)))
      (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
  let coeff : ℤ → ℂ := fun n ↦
    𝓕 (modulatedStripCellAverage x a T) (((n + 1 : ℤ) : ℝ))
  have hPair :
      HasSum (fun n : ℕ ↦ coeff n + coeff (-(n + 1 : ℤ)))
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: isolate the analytic work in the paired `ℕ`-indexed coefficient series.
    simpa [coeff] using
      shiftedFourierCoefficientPairs_hasSum_oddSineLocal (x := x) (a := a) (T := T) ha hT
  have hCoeffSummable : Summable coeff := by
    -- Proof comment: summability of the full shifted `ℤ`-series is packaged separately from the
    -- pairwise odd-mode computation so the final theorem is a pure `tsum` transport.
    simpa [coeff] using
      summable_shiftedFourierCoefficientsLocal (x := x) (a := a) (T := T) ha hT
  have hTsum :
      (∑' n : ℤ, coeff n) =
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: the canonical `tsum_nat_add_neg_add_one` regrouping rewrites the full
    -- shifted `ℤ`-series into the paired `ℕ`-series handled above.
    rw [← tsum_nat_add_neg_add_one hCoeffSummable]
    simpa [coeff] using hPair.tsum_eq
  -- Proof comment: once summability and the `tsum` identity are both fixed, the desired `HasSum`
  -- statement is immediate.
  exact hCoeffSummable.hasSum_iff.mpr hTsum

/-- Helper for Exercise 21.3.1: the Fourier coefficients of the Poisson input sum to the odd-sine
series from the textbook statement. -/
theorem fourier_modulatedStripCellAverage_hasSum_oddSineLocal
    {x a : ℝ} (_ha : 0 < a) {T : NNReal} (_hT : 0 < T) :
    HasSum (fun n : ℤ ↦ 𝓕 (modulatedStripCellAverage x a T) n)
      (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
  -- Proof comment: once the shifted coefficient series is identified, the original coefficient
  -- series follows immediately by the already packaged integer-translation equivalence.
  exact
    (hasSum_int_add_right_iffLocal
      (f := fun n : ℤ ↦ 𝓕 (modulatedStripCellAverage x a T) n)
      (l := (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ))
      1).mp <|
      shiftedFourierCoefficients_hasSum_oddSineLocal (x := x) (a := a) _ha _hT

/-- Helper for Exercise 21.3.1: the remaining Poisson step is to identify the complex-valued
integer sample series of `modulatedStripCellAverage` with the odd-sine expansion. This isolates
the continuity/decay setup and the paired Fourier-coefficient computation from the real-valued
strip-series transport. -/
theorem modulatedStripCellAverage_integerHasSum_oddSineLocal
    {x a : ℝ} (_hx : 0 < x) (_hxa : x < a) {T : NNReal} (_hT : 0 < T) :
    HasSum (fun n : ℤ ↦ modulatedStripCellAverage x a T n)
      (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
  -- Route correction: keep the Poisson identity in `ℂ` until the last line. The missing work is
  -- the concrete Poisson-at-zero proof for `modulatedStripCellAverage`, with the Fourier modes
  -- paired as `k` and `-(k + 1)` before any real-part conversion.
  have hx := _hx
  have hxa := _hxa
  have hT := _hT
  have ha : 0 < a := by
    linarith
  let f : ℝ → ℂ := modulatedStripCellAverage x a T
  have hc : Continuous f := by
    simpa [f] using modulatedStripCellAverage_continuousLocal (x := x) (a := a) (T := T)
  have hSampleEval :
      ∀ n : ℤ, f n = (paritySign n * shiftedStripMass x a T n : ℂ) := by
    intro n
    simpa [f] using
      modulatedStripCellAverage_int_eq_parityShiftedStripMassLocal
        (x := x) (a := a) ha.le (T := T) hT n
  have hSampleSummable :
      Summable (fun n : ℤ ↦ f n) := by
    have hSignedSummable :
        Summable (fun n : ℤ ↦ (paritySign n * shiftedStripMass x a T n : ℂ)) := by
      -- Proof comment: the integer sample series is the complex coercion of the already proved
      -- absolutely summable real strip series.
      refine Summable.of_norm ?_
      convert (summable_parityShiftedStripMassLocal (x := x) (a := a) ha hT).norm using 1
      ext n
      simp
    refine hSignedSummable.congr ?_
    intro n
    exact (hSampleEval n).symm
  have hDecay :
      Asymptotics.IsBigO (cocompact ℝ) f (fun s : ℝ => |s| ^ (-2 : ℝ)) := by
    -- Proof comment: the polynomial-decay input for Poisson summation is now isolated as its own
    -- theorem-level Gaussian tail estimate.
    simpa [f] using modulatedStripCellAverage_isBigO_cocompactLocal
      (x := x) (a := a) ha hT
  have hCoeff :
      HasSum (fun n : ℤ ↦ 𝓕 f n)
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: the Fourier-side identification is likewise isolated as a dedicated theorem
    -- on `𝓕 (modulatedStripCellAverage x a T)`.
    simpa [f] using fourier_modulatedStripCellAverage_hasSum_oddSineLocal
      (x := x) (a := a) ha hT
  have hPoisson :
      (∑' n : ℤ, f (0 + n)) =
        ∑' n : ℤ, 𝓕 f n * fourier n ((0 : ℝ) : UnitAddCircle) := by
    -- Proof comment: the weaker Poisson theorem only needs continuity, polynomial decay of `f`,
    -- and summability of the integer Fourier coefficients.
    simpa using
      Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
        hc one_lt_two hDecay hCoeff.summable 0
  have hTsum :
      (∑' n : ℤ, f n) =
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    calc
      (∑' n : ℤ, f n) = (∑' n : ℤ, f (0 + n)) := by simp
      _ = ∑' n : ℤ, 𝓕 f n * fourier n ((0 : ℝ) : UnitAddCircle) := hPoisson
      _ = ∑' n : ℤ, 𝓕 f n := by
            congr with n
            simp [fourier_eval_zero]
      _ = (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := hCoeff.tsum_eq
  exact hSampleSummable.hasSum_iff.mpr hTsum

/-- Helper for Exercise 21.3.1: the Poisson/Fourier step is likewise reduced to the paired
`ℕ`-shell series. -/
theorem centeredAlternatingStripSeries_hasSum_oddSineLocal
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n)
      ((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) := by
  -- Route correction: the Poisson owner statement also belongs on the centered `ℤ`-series, with
  -- the shell theorem below serving only as the transport wrapper.
  have ha : 0 < a := by
    linarith
  have hSample :
      ∀ n : ℤ,
        modulatedStripCellAverage x a T n =
          (paritySign n * shiftedStripMass x a T n : ℂ) := by
    intro n
    exact modulatedStripCellAverage_int_eq_parityShiftedStripMassLocal
      (x := x) (a := a) ha.le hT n
  have hPoisson :
      HasSum (fun n : ℤ ↦ modulatedStripCellAverage x a T n)
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: use the dedicated complex-valued Poisson helper, then transport its terms
    -- back to the real strip series with `hSample`.
    exact modulatedStripCellAverage_integerHasSum_oddSineLocal
      (x := x) (a := a) hx hxa hT
  have hComplex :
      HasSum (fun n : ℤ ↦ ((paritySign n * shiftedStripMass x a T n : ℝ) : ℂ))
        (((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) : ℂ) := by
    -- Proof comment: rewrite the complex Poisson series termwise using the integer-sample formula
    -- for `modulatedStripCellAverage`.
    convert hPoisson using 1
    ext n
    simpa [Complex.ofReal_mul] using (hSample n).symm
  -- Proof comment: every term in the complex identity is already real, so mapping by real part
  -- recovers the desired real-valued `HasSum`.
  simpa using hComplex.mapL Complex.reCLM

/-- Helper for Exercise 21.3.1: the Poisson/Fourier step is likewise reduced to the paired
`ℕ`-shell series. -/
theorem alternatingStripPairShell_hasSum_oddSineLocal
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (alternatingStripPairShell x a T)
      ((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) := by
  -- Proof comment: the paired shell identity is obtained by repackaging the centered analytic
  -- `ℤ`-series through the same `nat_add_neg_add_one` transport.
  convert
      (centeredAlternatingStripSeries_hasSum_oddSineLocal
        (x := x) (a := a) hx hxa hT).nat_add_neg_add_one using 1

/-- Helper for Exercise 21.3.1: once the Poisson/Fourier analysis is packaged as a `HasSum`
statement, formula `(21.20)` follows by taking the `tsum` of that series. -/
theorem alternatingGaussianStripSeries_hasSum_oddSineLocal
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    HasSum (fun n : ℤ ↦ paritySign n * shiftedStripMass x a T n)
      ((4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k) := by
  have ha : 0 < a := by
    linarith
  -- Proof comment: the same abstract shell-to-centered transport turns the paired Poisson `HasSum`
  -- into the public `ℤ`-series statement.
  exact
    hasSum_of_alternatingStripPairShellLocal (x := x) (a := a) (T := T) ha hT
      (alternatingStripPairShell_hasSum_oddSineLocal (x := x) (a := a) hx hxa hT)

/-- Helper for Exercise 21.3.1: Poisson summation turns the alternating Gaussian strip series into
the odd Fourier-sine eigenfunction expansion. -/
theorem alternatingGaussianStripSeries_eq_oddSineExpansion
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    (∑' n : ℤ, paritySign n * shiftedStripMass x a T n) =
      (4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k := by
  -- Proof comment: after packaging the analytic argument as a `HasSum`, the displayed equality is
  -- exactly the `tsum` of that series.
  exact
    (alternatingGaussianStripSeries_hasSum_oddSineLocal
      (x := x) (a := a) hx hxa hT).tsum_eq

/-- Exercise 21.3.1: the two-barrier survival probability of Brownian motion started at `x` equals
the odd sine eigenfunction series in formula `(21.20)`. -/
theorem brownianIntervalSurvival_eq_oddSineSeries
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x a : ℝ} (hx : 0 < x) (hxa : x < a) {T : NNReal} (hT : 0 < T) :
    μ.real {ω | T < brownianIntervalExitTime W x a ω} =
      (4 / Real.pi) * ∑' k : ℕ, oddSineSurvivalTerm x a T k := by
  -- Proof comment: once the Brownian reflection series and the analytic Poisson computation are
  -- available, the final formula is their direct concatenation.
  rw [brownianIntervalSurvival_eq_alternatingStripSeries (hW := hW) hx hxa hT]
  exact alternatingGaussianStripSeries_eq_oddSineExpansion hx hxa hT

end ProbabilityTheory
