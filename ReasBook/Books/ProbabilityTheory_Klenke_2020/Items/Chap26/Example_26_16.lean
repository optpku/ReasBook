/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_73
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_74
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Lemma_25_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_35.Regularity
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_14

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology InnerProductSpace

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "VectorProcess" => NNReal → Ω → Fin n → ℝ
local notation "ScalarProcess" => NNReal → Ω → ℝ
local notation "ScalarState" => Fin 1 → ℝ

/-- Helper for Example 26.16: the squared Euclidean norm on `ℝⁿ`, written as a finite sum of
coordinate squares. -/
def euclideanSquaredNorm (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i) ^ 2

/-- Evaluating `euclideanSquaredNorm` unfolds to the coordinate-square sum. -/
theorem euclideanSquaredNorm_def (x : Fin n → ℝ) :
    euclideanSquaredNorm x = ∑ i : Fin n, (x i) ^ 2 := by
  -- Proof comment: this is just the defining finite sum.
  rfl

/-- The Brownian motion started at `y` obtained by adding the deterministic initial point `y` to a
standard vector Brownian driver `B`. -/
def shiftedBrownianProcess (y : Fin n → ℝ) (B : VectorProcess) : VectorProcess :=
  fun t ω i ↦ y i + B t ω i

/-- Evaluating `shiftedBrownianProcess y B` adds the starting point coordinatewise. -/
theorem shiftedBrownianProcess_apply (y : Fin n → ℝ) (B : VectorProcess)
    (t : NNReal) (ω : Ω) (i : Fin n) :
    shiftedBrownianProcess y B t ω i = y i + B t ω i := by
  -- Proof comment: unfold the shifted process at the chosen coordinate.
  rfl

/-- The squared radial process `X_t = ‖B_t‖²` associated with an `ℝⁿ`-valued process `B`. -/
def squaredNormProcess (B : VectorProcess) : ScalarProcess :=
  fun t ω ↦ euclideanSquaredNorm (B t ω)

/-- Evaluating `squaredNormProcess B` gives the squared Euclidean norm of `B_t`. -/
theorem squaredNormProcess_apply (B : VectorProcess) (t : NNReal) (ω : Ω) :
    squaredNormProcess B t ω = euclideanSquaredNorm (B t ω) := by
  -- Proof comment: unfold the radial process at `(t, ω)`.
  rfl

/-- Helper for Example 26.16: the fixed time-space test function
`F(z, s) = ∑ i, (y i + z i)^2` used to compare the shifted squared norm with the Chapter 25 Itô
formula. -/
private def shiftedSquaredNormFunction
    (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) × ℝ → ℝ :=
  fun xt ↦ ∑ i : Fin n, (y i + xt.1 i) ^ 2

/-- Helper for Example 26.16: moving along one coordinate line changes only that coordinate. -/
private theorem coordinateLine_apply
    (z : EuclideanSpace ℝ (Fin n)) (i j : Fin n) (t : ℝ) :
    (z + EuclideanSpace.single i (t - z i)) j = if j = i then t else z j := by
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- Helper for Example 26.16: on the `i`-th coordinate line, the shifted squared norm splits into
the `i`-th quadratic term plus a constant tail. -/
private theorem shiftedSquaredNormFunction_onCoordinateLine
    (y : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s t : ℝ) :
    shiftedSquaredNormFunction y (z + EuclideanSpace.single i (t - z i), s) =
      (y i + t) ^ 2 + ∑ j in Finset.univ.erase i, (y j + z j) ^ 2 := by
  classical
  rw [shiftedSquaredNormFunction, Finset.sum_erase_add _ (Finset.mem_univ i)]
  simp [coordinateLine_apply]

/-- Helper for Example 26.16: the shifted squared norm does not depend on the time coordinate, so
its time partial derivative vanishes. -/
private theorem shiftedSquaredNormFunction_timePartialDeriv
    (y : Fin n → ℝ) (xt : EuclideanSpace ℝ (Fin n) × ℝ) :
    (∂ₜ shiftedSquaredNormFunction y) xt = 0 := by
  rw [timePartialDeriv_def]
  simp [shiftedSquaredNormFunction]

/-- Helper for Example 26.16: the `i`-th spatial partial derivative of the shifted squared norm is
`2 * (y i + z i)`. -/
private theorem shiftedSquaredNormFunction_spacePartialDeriv
    (y : Fin n → ℝ) (i : Fin n) (xt : EuclideanSpace ℝ (Fin n) × ℝ) :
    (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2)) xt.1 =
      2 * (y i + xt.1 i) := by
  let C : ℝ := ∑ j in Finset.univ.erase i, (y j + xt.1 j) ^ 2
  have hEq :
      (fun t : ℝ ↦ shiftedSquaredNormFunction y (xt.1 + EuclideanSpace.single i (t - xt.1 i), xt.2)) =
        fun t : ℝ ↦ (y i + t) ^ 2 + C := by
    funext t
    rw [shiftedSquaredNormFunction_onCoordinateLine]
    simp [C]
  have hDeriv :
      HasDerivAt (fun t : ℝ ↦ (y i + t) ^ 2 + C) (2 * (y i + xt.1 i)) (xt.1 i) := by
    -- Proof comment: the coordinate-line slice is one quadratic term plus a constant tail.
    simpa [pow_two, two_mul, C, add_assoc, add_left_comm, add_comm] using
      ((((hasDerivAt_id (xt.1 i)).const_add (y i)).pow 2).add_const C)
  rw [partialDeriv_def, hEq]
  exact hDeriv.deriv

/-- Helper for Example 26.16: the second spatial partials of the shifted squared norm are `2` on
the diagonal and `0` off the diagonal. -/
private theorem shiftedSquaredNormFunction_spaceSecondPartialDeriv
    (y : Fin n → ℝ) (i j : Fin n) (xt : EuclideanSpace ℝ (Fin n) × ℝ) :
    (∂²[i, j] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2)) xt.1 =
      if i = j then 2 else 0 := by
  rw [secondPartialDeriv_def]
  by_cases hij : i = j
  · subst hij
    have hEq :
        (fun t : ℝ ↦
          (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2))
            (xt.1 + EuclideanSpace.single i (t - xt.1 i))) =
          fun t : ℝ ↦ 2 * (y i + t) := by
      funext t
      rw [shiftedSquaredNormFunction_spacePartialDeriv]
      simp [coordinateLine_apply]
    have hDeriv :
        HasDerivAt (fun t : ℝ ↦ 2 * (y i + t)) 2 (xt.1 i) := by
      -- Proof comment: along the diagonal, the first partial is an affine function of the moving
      -- coordinate.
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using
        (((hasDerivAt_id (xt.1 i)).const_add (y i)).const_mul 2)
    rw [hEq]
    simpa using hDeriv.deriv
  · have hEq :
        (fun t : ℝ ↦
          (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2))
            (xt.1 + EuclideanSpace.single j (t - xt.1 j))) =
          fun _ : ℝ ↦ 2 * (y i + xt.1 i) := by
      funext t
      rw [shiftedSquaredNormFunction_spacePartialDeriv]
      simp [coordinateLine_apply, hij]
    rw [hEq]
    simp [hij]

/-- Helper for Example 26.16: the shifted squared norm belongs to the `C^{2,1}` class required by
Corollary 25.35. -/
private theorem shiftedSquaredNorm_isTimeSpaceC21
    (y : Fin n → ℝ) :
    IsTimeSpaceC21 (shiftedSquaredNormFunction y) := by
  refine
    { hasDerivAt_time := ?_
      continuous_timePartialDeriv := ?_
      hasDerivAt_space := ?_
      continuous_spacePartialDeriv := ?_
      hasDerivAt_spaceSecond := ?_
      continuous_spaceSecondPartialDeriv := ?_ }
  · intro xt
    -- Proof comment: the time slice is constant because the test function depends only on the
    -- spatial variable.
    simpa [shiftedSquaredNormFunction_timePartialDeriv, shiftedSquaredNormFunction] using
      (hasDerivAt_const xt.2 (c := ∑ i : Fin n, (y i + xt.1 i) ^ 2))
  · have hEq :
        (∂ₜ shiftedSquaredNormFunction y) = fun _ : EuclideanSpace ℝ (Fin n) × ℝ ↦ (0 : ℝ) := by
      funext xt
      exact shiftedSquaredNormFunction_timePartialDeriv y xt
    rw [hEq]
    exact continuous_const
  · intro i xt
    let C : ℝ := ∑ j in Finset.univ.erase i, (y j + xt.1 j) ^ 2
    have hEq :
        (fun t : ℝ ↦ shiftedSquaredNormFunction y (xt.1 + EuclideanSpace.single i (t - xt.1 i), xt.2)) =
          fun t : ℝ ↦ (y i + t) ^ 2 + C := by
      funext t
      rw [shiftedSquaredNormFunction_onCoordinateLine]
      simp [C]
    have hDeriv :
        HasDerivAt
          (fun t : ℝ ↦ (y i + t) ^ 2 + C)
          ((∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2)) xt.1)
          (xt.1 i) := by
      simpa [shiftedSquaredNormFunction_spacePartialDeriv] using
        ((((hasDerivAt_id (xt.1 i)).const_add (y i)).pow 2).add_const C)
    rw [hEq]
    simpa [pow_two, two_mul, C, add_assoc, add_left_comm, add_comm] using hDeriv
  · intro i
    have hEq :
        (fun xt : EuclideanSpace ℝ (Fin n) × ℝ ↦
          (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2)) xt.1) =
          fun xt : EuclideanSpace ℝ (Fin n) × ℝ ↦ 2 * (y i + xt.1 i) := by
      funext xt
      exact shiftedSquaredNormFunction_spacePartialDeriv y i xt
    rw [hEq]
    exact (continuous_fst.apply i).const_add (y i) |>.const_mul 2
  · intro i j xt
    by_cases hij : i = j
    · subst hij
      have hEq :
          (fun t : ℝ ↦
            (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2))
              (xt.1 + EuclideanSpace.single i (t - xt.1 i))) =
            fun t : ℝ ↦ 2 * (y i + t) := by
        funext t
        rw [shiftedSquaredNormFunction_spacePartialDeriv]
        simp [coordinateLine_apply]
      rw [hEq]
      simpa [shiftedSquaredNormFunction_spaceSecondPartialDeriv] using
        (((hasDerivAt_id (xt.1 i)).const_add (y i)).const_mul 2)
    · have hEq :
          (fun t : ℝ ↦
            (∂[i] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2))
              (xt.1 + EuclideanSpace.single j (t - xt.1 j))) =
            fun _ : ℝ ↦ 2 * (y i + xt.1 i) := by
        funext t
        rw [shiftedSquaredNormFunction_spacePartialDeriv]
        simp [coordinateLine_apply, hij]
      rw [hEq]
      simpa [shiftedSquaredNormFunction_spaceSecondPartialDeriv, hij] using
        (hasDerivAt_const (xt.1 j) (c := 2 * (y i + xt.1 i)))
  · intro i j
    have hEq :
        (fun xt : EuclideanSpace ℝ (Fin n) × ℝ ↦
          (∂²[i, j] fun z : EuclideanSpace ℝ (Fin n) ↦ shiftedSquaredNormFunction y (z, xt.2))
            xt.1) =
          fun _ : EuclideanSpace ℝ (Fin n) × ℝ ↦ if i = j then (2 : ℝ) else 0 := by
      funext xt
      exact shiftedSquaredNormFunction_spaceSecondPartialDeriv y i j xt
    rw [hEq]
    exact continuous_const

/-- The source integrand `(y_i + B_t^i) / sqrt (‖y + B_t‖²)` from Example 26.16. -/
def squaredBesselDriverIntegrand
    (y : Fin n → ℝ) (B : VectorProcess) (i : Fin n) : ScalarProcess :=
  fun t ω ↦
    shiftedBrownianProcess y B t ω i /
      Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω)

/-- Evaluating the source integrand unfolds the normalized coordinate formula. -/
theorem squaredBesselDriverIntegrand_apply
    (y : Fin n → ℝ) (B : VectorProcess) (i : Fin n) (t : NNReal) (ω : Ω) :
    squaredBesselDriverIntegrand y B i t ω =
      shiftedBrownianProcess y B t ω i /
        Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) := by
  -- Proof comment: unfold the normalized coordinate integrand.
  rfl

/-- The one-dimensional squared-Bessel diffusion coefficient in the chapter's `Fin 1 → ℝ` state
format. -/
def squaredBesselDiffusionCoeff : NNReal → ScalarState → Fin 1 → Fin 1 → ℝ :=
  fun _ x _ _ ↦ 2 * Real.sqrt (x 0)

/-- Evaluating `squaredBesselDiffusionCoeff` gives `2 * sqrt (x 0)`. -/
theorem squaredBesselDiffusionCoeff_apply
    (t : NNReal) (x : ScalarState) (i j : Fin 1) :
    squaredBesselDiffusionCoeff t x i j = 2 * Real.sqrt (x 0) := by
  -- Proof comment: unfold the coefficient.
  rfl

/-- The constant drift coefficient `δ` of the one-dimensional squared-Bessel equation. -/
def squaredBesselDriftCoeff (δ : ℕ) : NNReal → ScalarState → Fin 1 → ℝ :=
  fun _ _ _ ↦ (δ : ℝ)

/-- Evaluating `squaredBesselDriftCoeff δ` gives the constant value `δ`. -/
theorem squaredBesselDriftCoeff_apply
    (δ : ℕ) (t : NNReal) (x : ScalarState) (i : Fin 1) :
    squaredBesselDriftCoeff δ t x i = (δ : ℝ) := by
  -- Proof comment: unfold the drift coefficient.
  rfl

/-- Helper for Example 26.16: the distinguished coordinate used to totalize the unit direction on
the zero set of the shifted Brownian path. -/
private def squaredBesselDistinguishedCoordinate (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- Helper for Example 26.16: the exact unit radial direction of `y + B_t`, obtained by using the
normalized vector away from the origin and a fixed basis vector on the zero set. -/
def squaredBesselUnitDirection
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n) (i : Fin n) : ScalarProcess :=
  fun t ω ↦
    if _ : squaredNormProcess (shiftedBrownianProcess y B) t ω = 0 then
      if i = squaredBesselDistinguishedCoordinate hn then 1 else 0
    else
      squaredBesselDriverIntegrand y B i t ω

/-- Evaluating the exact unit direction unfolds the zero-case totalization and the nonzero radial
normalization. -/
theorem squaredBesselUnitDirection_apply
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n) (i : Fin n) (t : NNReal) (ω : Ω) :
    squaredBesselUnitDirection y B hn i t ω =
      if squaredNormProcess (shiftedBrownianProcess y B) t ω = 0 then
        if i = squaredBesselDistinguishedCoordinate hn then 1 else 0
      else
        squaredBesselDriverIntegrand y B i t ω := by
  -- Proof comment: unfold the exact unit-direction helper at `(t, ω)`.
  rfl

/-- Helper for Example 26.16: the source-facing scalar driver `W` is packaged as the sum of the
coordinate Itô integrals against the exact unit radial direction. This keeps the proof surface on
the bracket-exact integrand, while the textbook quotient integrand can be recovered later away
from the zero set. -/
def HasSourceSquaredBesselDriverFormula
    (ℱ : TimeFiltration) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n)
    (W : ScalarProcess) : Prop :=
  ∃ coordinate_localMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i),
    ∃ coordinate_bracket :
        ∀ i : Fin n,
          HasAbsolutelyContinuousSquareVariation (fun t ω ↦ B t ω i)
            (coordinate_localMartingale i),
      ∃ coordinate_integral : Fin n → ScalarProcess,
        (∀ i : Fin n,
          IsContinuousLocalMartingaleItoIntegralSpec
            (μ := μ)
            (ℱ := ℱ)
            (hM := coordinate_localMartingale i)
            (coordinate_bracket i)
            (squaredBesselUnitDirection y B hn i)
            (coordinate_integral i)) ∧
        AreModifications μ W (fun t ω ↦ ∑ i : Fin n, coordinate_integral i t ω)

/-- A scalar local martingale `W` realizes the squared radial process of the shifted Brownian
motion as a weak solution of the one-dimensional squared-Bessel equation with dimension `n`. -/
def IsWeakSquaredBesselRealization
    (ℱ : TimeFiltration) (μ : Measure Ω) (y : Fin n → ℝ) (B : VectorProcess)
    [IsProbabilityMeasure μ] (hn : 0 < n) (W : ScalarProcess) : Prop :=
  ∃ hW : IsContinuousLocalMartingale ℱ μ W,
    ∃ hQuad : IsContinuousSquareVariationProcess ℱ μ W (fun t _ ↦ (t : ℝ)),
      ∃ hbr : HasAbsolutelyContinuousSquareVariation W hW,
        HasSourceSquaredBesselDriverFormula ℱ μ y B hn W ∧
          ∃ N : ScalarProcess,
            IsContinuousLocalMartingaleItoIntegralSpec
              (μ := μ)
              (ℱ := ℱ)
              (hM := hW)
              hbr
              (fun t ω ↦
                squaredBesselDiffusionCoeff
                  t
                  (fun _ ↦ squaredNormProcess (shiftedBrownianProcess y B) t ω)
                  0
                  0)
              N ∧
            AreModifications μ
              (fun t ω ↦
                squaredNormProcess (shiftedBrownianProcess y B) t ω -
                  ((∑ j : Fin n, (y j) ^ 2) + n * t))
              N

/-- Helper for Example 26.16: each Brownian coordinate has the continuous local martingale and
identity-bracket package needed by the canonical coordinate Itô integrals. -/
theorem brownianCoordinateIdentityBracketData
    {ℱ : TimeFiltration} {B : VectorProcess}
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (i : Fin n) :
    ∃ hMi : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i),
      HasAbsolutelyContinuousSquareVariation (fun t ω ↦ B t ω i) hMi ∧
        IsContinuousSquareVariationProcess ℱ μ
          (fun t ω ↦ B t ω i)
          (fun t _ ↦ (t : ℝ)) := by
  -- Proof comment: realize the `i`-th coordinate as the constant-one Brownian Itô integral, then
  -- rewrite its compensator to the identity path `t ↦ t`.
  have hCoordIto :
      IsBrownianLocalItoIntegral ℱ μ
        (fun t ω ↦ B t ω i)
        (fun _ _ ↦ (1 : ℝ))
        (fun t ω ↦ B t ω i) := by
    simpa [CoordinateProcess.toEuclidean] using
      (brownianCoordinate_constOne_isBrownianLocalItoIntegral
        (ℱ := ℱ)
        (μ := μ)
        (W := B.toEuclidean)
        hB.1
        i)
  have hCoordData :
      IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i) ∧
        IsContinuousSquareVariationProcess ℱ μ
          (fun t ω ↦ B t ω i)
          (MeasureTheory.secondMomentCompensator (fun _ _ ↦ (1 : ℝ))) :=
    brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
      (ℱ := ℱ)
      (μ := μ)
      hCoordIto
  have hCoordBracket :
      HasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ B t ω i)
        hCoordData.1 := by
    refine ⟨fun _ _ ↦ (1 : NNReal), ?_, ?_, ?_⟩
    · -- Proof comment: the bracket density is the deterministic constant `1`.
      simpa using
        (stronglyMeasurable_const.progMeasurable :
          ProgMeasurable ℱ (fun _ _ : Ω ↦ (1 : ℝ)))
    · -- Proof comment: the Brownian coordinate square variation is the standard second-moment
      -- compensator of the constant-one Itô integral.
      simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
    · -- Proof comment: integrating the density `1` over `[0, t]` yields `t`.
      intro t ω
      simp [MeasureTheory.secondMomentCompensator]
  have hCoordSquareVariation :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ B t ω i)
        (fun t _ ↦ (t : ℝ)) := by
    -- Proof comment: this is the same compensator identity on the public square-variation
    -- surface.
    simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
  exact ⟨hCoordData.1, hCoordBracket, hCoordSquareVariation⟩

/-- Helper for Example 26.16: the exact owner sum of the canonical coordinate Itô integrals
already satisfies the source-driver clause of the weak squared-Bessel realization. -/
theorem exists_sourceSquaredBesselDriverFormula
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B) :
    ∃ W : ScalarProcess, HasSourceSquaredBesselDriverFormula ℱ μ y B hn W := by
  classical
  have hCoordData :
      ∀ i : Fin n,
        ∃ hMi : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i),
          HasAbsolutelyContinuousSquareVariation (fun t ω ↦ B t ω i) hMi ∧
            IsContinuousSquareVariationProcess ℱ μ
              (fun t ω ↦ B t ω i)
              (fun t _ ↦ (t : ℝ)) := by
    intro i
    exact brownianCoordinateIdentityBracketData (ℱ := ℱ) (μ := μ) (B := B) hB i
  choose coordinateLocalMartingale hCoordRest using hCoordData
  choose coordinateBracket hCoordSquareVariation using hCoordRest
  let coordinateIntegral : Fin n → ScalarProcess :=
    fun i ↦
      continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (squaredBesselUnitDirection y B hn i)
  let W : ScalarProcess := fun t ω ↦ ∑ i : Fin n, coordinateIntegral i t ω
  refine ⟨W, ?_⟩
  refine ⟨coordinateLocalMartingale, coordinateBracket, coordinateIntegral, ?_, ?_⟩
  · -- Proof comment: each coordinate witness is the canonical Itô realization against the exact
    -- unit-direction coefficient.
    intro i
    exact
      canonicalItoIntegralSpec
        (μ := μ)
        (ℱ := ℱ)
        (M := fun t ω ↦ B t ω i)
        (H := squaredBesselUnitDirection y B hn i)
        (coordinateLocalMartingale i)
        (coordinateBracket i)
  · -- Proof comment: the selected source driver is definitionally the exact finite sum of those
    -- coordinate integral realizations.
    intro t
    filter_upwards with ω
    rfl

/-- Helper for Example 26.16: if the shifted Brownian path has squared norm `0` at `(t, ω)`,
then each coordinate vanishes at that point. -/
theorem shiftedBrownian_eq_zero_of_squaredNorm_eq_zero
    (y : Fin n → ℝ) (B : VectorProcess) {t : NNReal} {ω : Ω} {i : Fin n}
    (hX : squaredNormProcess (shiftedBrownianProcess y B) t ω = 0) :
    shiftedBrownianProcess y B t ω i = 0 := by
  let z : Fin n → ℝ := shiftedBrownianProcess y B t ω
  have hs : ∑ j : Fin n, (z j) ^ 2 = 0 := by
    simpa [z, squaredNormProcess_apply, euclideanSquaredNorm_def] using hX
  have hle :
      (z i) ^ 2 ≤ ∑ j : Fin n, (z j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (by simp)
  have hle_zero : (z i) ^ 2 ≤ 0 := by
    simpa [hs] using hle
  have hsq : (z i) ^ 2 = 0 := le_antisymm hle_zero (sq_nonneg (z i))
  have hz : z i = 0 := by
    nlinarith
  -- Proof comment: the vanishing sum of nonnegative coordinate squares forces each coordinate to
  -- vanish individually.
  simpa [z] using hz

/-- Helper for Example 26.16: the exact unit-direction field has Euclidean norm `1` at every
space-time point. -/
theorem squaredBesselUnitDirection_sum_sq
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n) (t : NNReal) (ω : Ω) :
    ∑ i : Fin n, (squaredBesselUnitDirection y B hn i t ω) ^ 2 = 1 := by
  by_cases hX : squaredNormProcess (shiftedBrownianProcess y B) t ω = 0
  · -- Proof comment: on the zero set the unit direction is the distinguished basis vector.
    simp [squaredBesselUnitDirection_apply, hX]
  · have hXnonneg :
        0 ≤ squaredNormProcess (shiftedBrownianProcess y B) t ω := by
      simpa [squaredNormProcess_apply, euclideanSquaredNorm_def] using
        (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (shiftedBrownianProcess y B t ω j)))
    have hsqrt_ne :
        Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) ≠ 0 := by
      intro hsqrt
      apply hX
      nlinarith [Real.sq_sqrt hXnonneg, hsqrt]
    -- Proof comment: away from the zero set, the exact unit direction is the normalized radial
    -- vector, so its squared norm is the squared norm of the numerator divided by itself.
    calc
      ∑ i : Fin n, (squaredBesselUnitDirection y B hn i t ω) ^ 2
          = ∑ i : Fin n,
              ((shiftedBrownianProcess y B t ω i) /
                Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω)) ^ 2 := by
              simp [squaredBesselUnitDirection_apply, hX, squaredBesselDriverIntegrand_apply]
      _ = ∑ i : Fin n,
            (shiftedBrownianProcess y B t ω i) ^ 2 *
              (Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω))⁻¹ ^ 2 := by
            simp_rw [div_eq_mul_inv, mul_pow]
      _ = (∑ i : Fin n, (shiftedBrownianProcess y B t ω i) ^ 2) *
            (Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω))⁻¹ ^ 2 := by
            rw [Finset.sum_mul]
      _ = squaredNormProcess (shiftedBrownianProcess y B) t ω *
            (Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω))⁻¹ ^ 2 := by
            simp [squaredNormProcess_apply, euclideanSquaredNorm_def]
      _ = 1 := by
            rw [← Real.sq_sqrt hXnonneg]
            field_simp [hsqrt_ne]

/-- Helper for Example 26.16: each squared coordinate of the exact unit-direction field is bounded
by `1`. -/
theorem squaredBesselUnitDirection_sq_le_one
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n)
    (i : Fin n) (t : NNReal) (ω : Ω) :
    (squaredBesselUnitDirection y B hn i t ω) ^ 2 ≤ 1 := by
  have hle :
      (squaredBesselUnitDirection y B hn i t ω) ^ 2 ≤
        ∑ j : Fin n, (squaredBesselUnitDirection y B hn j t ω) ^ 2 := by
    exact
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (squaredBesselUnitDirection y B hn j t ω))
        (by simp)
  -- Proof comment: each nonnegative square is bounded by the total squared norm, and that total
  -- squared norm is exactly `1`.
  simpa [squaredBesselUnitDirection_sum_sq y B hn t ω] using hle

/-- Helper for Example 26.16: multiplying the exact unit direction by the radial length recovers
the corresponding shifted-Brownian coordinate. -/
theorem sqrt_mul_squaredBesselUnitDirection
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n)
    (i : Fin n) (t : NNReal) (ω : Ω) :
    Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) *
        squaredBesselUnitDirection y B hn i t ω =
      shiftedBrownianProcess y B t ω i := by
  by_cases hX : squaredNormProcess (shiftedBrownianProcess y B) t ω = 0
  · have hz :
        shiftedBrownianProcess y B t ω i = 0 :=
      shiftedBrownian_eq_zero_of_squaredNorm_eq_zero y B (i := i) hX
    -- Proof comment: on the zero set both sides vanish, with the right-hand side given by the
    -- coordinate-zero lemma above.
    simp [squaredBesselUnitDirection_apply, hX, hz]
  · have hXnonneg :
        0 ≤ squaredNormProcess (shiftedBrownianProcess y B) t ω := by
      simpa [squaredNormProcess_apply, euclideanSquaredNorm_def] using
        (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (shiftedBrownianProcess y B t ω j)))
    have hsqrt_ne :
        Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) ≠ 0 := by
      intro hsqrt
      apply hX
      nlinarith [Real.sq_sqrt hXnonneg, hsqrt]
    -- Proof comment: away from the zero set this is just cancellation of the normalizing factor.
    rw [squaredBesselUnitDirection_apply, if_neg hX, squaredBesselDriverIntegrand_apply]
    field_simp [hsqrt_ne]

/-- Helper for Example 26.16: each shifted-Brownian coordinate is progressively measurable on the
ambient filtration. -/
theorem shiftedBrownianCoordinate_progMeasurable
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hB : IsBrownianMotionWithFiltration ℱ μ B) (i : Fin n) :
    ProgMeasurable ℱ (fun t ω ↦ shiftedBrownianProcess y B t ω i) := by
  rcases brownianCoordinateIdentityBracketData (ℱ := ℱ) (μ := μ) (B := B) hB i with
    ⟨hMi, -, -⟩
  have hCoordProg : ProgMeasurable ℱ (fun t ω ↦ B t ω i) :=
    hMi.adapted.stronglyAdapted.progMeasurable_of_continuous hMi.continuous
  -- Proof comment: adding the deterministic initial coordinate preserves progressive
  -- measurability.
  simpa [shiftedBrownianProcess_apply] using
    (stronglyMeasurable_const.progMeasurable :
      ProgMeasurable ℱ (fun _ _ : Ω ↦ y i)).add hCoordProg

/-- Helper for Example 26.16: the shifted radial square `‖y + B_t‖²` is jointly measurable on
`ℝ≥0 × Ω`. -/
theorem squaredNormShiftedBrownian_measurable_uncurry
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hB : IsBrownianMotionWithFiltration ℱ μ B) :
    Measurable (Function.uncurry (squaredNormProcess (shiftedBrownianProcess y B))) := by
  -- Proof comment: the squared radial process is the finite sum of the jointly measurable shifted
  -- coordinate squares.
  simpa [Function.uncurry, squaredNormProcess_apply, euclideanSquaredNorm_def] using
    (Finset.measurable_sum fun i _ ↦
      ((shiftedBrownianCoordinate_progMeasurable (μ := μ) y hB i).measurable_uncurry).pow_const 2)

/-- Helper for Example 26.16: the exact unit-direction coefficient is jointly measurable on
`ℝ≥0 × Ω`. -/
theorem squaredBesselUnitDirection_measurable_uncurry
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n) (hB : IsBrownianMotionWithFiltration ℱ μ B) (i : Fin n) :
    Measurable (Function.uncurry (squaredBesselUnitDirection y B hn i)) := by
  let X : ScalarProcess := squaredNormProcess (shiftedBrownianProcess y B)
  have hCoordProd :
      Measurable (Function.uncurry (fun t ω ↦ shiftedBrownianProcess y B t ω i)) :=
    (shiftedBrownianCoordinate_progMeasurable (μ := μ) y hB i).measurable_uncurry
  have hXProd : Measurable (Function.uncurry X) :=
    squaredNormShiftedBrownian_measurable_uncurry (μ := μ) y hB
  have hDiv :
      Measurable (Function.uncurry (squaredBesselDriverIntegrand y B i)) := by
    -- Proof comment: away from the zero set, the coefficient is the measurable quotient of one
    -- shifted coordinate by the measurable radial square root.
    simpa [Function.uncurry, squaredBesselDriverIntegrand_apply, X] using
      hCoordProd.div hXProd.sqrt
  let zeroSet : Set (NNReal × Ω) := {p | X p.1 p.2 = 0}
  have hZeroSet : MeasurableSet zeroSet := by
    -- Proof comment: the zero branch is cut out by the measurable radial-square process.
    exact hXProd measurableSet_singleton
  have hZeroBranch :
      Measurable
        (fun _ : NNReal × Ω ↦
          if i = squaredBesselDistinguishedCoordinate hn then (1 : ℝ) else 0) :=
    measurable_const
  -- Proof comment: package the zero-set totalization as a measurable piecewise combination of the
  -- constant basis-vector branch and the radial quotient branch.
  simpa [Function.uncurry, squaredBesselUnitDirection_apply, zeroSet, X] using
    Measurable.piecewise hZeroSet hZeroBranch hDiv

/-- Helper for Example 26.16: the exact unit-direction coefficient is progressively measurable on
the ambient filtration. -/
theorem squaredBesselUnitDirection_progMeasurable
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n) (hB : IsBrownianMotionWithFiltration ℱ μ B) (i : Fin n) :
    ProgMeasurable ℱ (squaredBesselUnitDirection y B hn i) := by
  -- Proof comment: joint measurability of the exact coefficient restricts to every deterministic
  -- strip, which is the real-valued progressive measurability criterion used in Chapter 25.
  refine Adapted.progMeasurable_of_measurableOnStrips (ℱ := ℱ) ?_
  intro T
  exact
    Adapted.measurableOnStrip_of_productMeasurable
      (ℱ := ℱ)
      (H := squaredBesselUnitDirection y B hn i)
      (squaredBesselUnitDirection_measurable_uncurry (μ := μ) y hn hB i)
      T

/-- Helper for Example 26.16: a jointly measurable scalar field whose square is pointwise bounded
by `1` has finite deterministic-horizon square energy on every interval `[0, T]`. -/
theorem squareIntegrableUpTo_of_uncurryMeasurable_sq_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H : NNReal → Ω → ℝ}
    (hH_prod : Measurable (Function.uncurry H))
    (hH_sq_le : ∀ t : NNReal, ∀ ω : Ω, (H t ω) ^ 2 ≤ 1)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hMeas :
      AEStronglyMeasurable
        (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
    have hSliceMeas : Measurable (fun s : ℝ ↦ H s.toNNReal ω) := by
      -- Proof comment: fixing `ω` turns the jointly measurable uncurry into a measurable time
      -- slice on `ℝ`.
      simpa [Function.uncurry] using
        hH_prod.comp (measurable_real_toNNReal.prod_mk measurable_const)
    exact (hSliceMeas.pow_const 2).aestronglyMeasurable
  have hConst :
      Integrable (fun _ : ℝ ↦ (1 : ℝ))
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
    simpa using
      (integrableOn_const (μ := volume) (s := Set.Icc (0 : ℝ) (T : ℝ))
        measure_Icc_lt_top.ne)
  -- Proof comment: dominate the squared slice by the integrable constant `1` on the
  -- deterministic strip.
  exact hConst.mono' hMeas <| Filter.Eventually.of_forall fun s ↦ by
    have hsq_nonneg : 0 ≤ (H s.toNNReal ω) ^ 2 := sq_nonneg _
    have hsq_le : (H s.toNNReal ω) ^ 2 ≤ 1 := hH_sq_le s.toNNReal ω
    simpa [abs_of_nonneg hsq_nonneg] using hsq_le

/-- Helper for Example 26.16: each exact unit-direction coefficient has finite deterministic-horizon
square energy on every interval `[0, T]`. -/
theorem squaredBesselUnitDirection_squareIntegrableUpTo
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n) (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (i : Fin n) (T : NNReal) :
    ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦ (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: combine joint measurability of the exact coefficient with the pointwise bound
  -- `(U_i)^2 ≤ 1`.
  exact
    squareIntegrableUpTo_of_uncurryMeasurable_sq_le_one
      (μ := μ)
      (H := squaredBesselUnitDirection y B hn i)
      (squaredBesselUnitDirection_measurable_uncurry (μ := μ) y hn hB i)
      (squaredBesselUnitDirection_sq_le_one y B hn i)
      T

/-- Helper for Example 26.16: if two continuous local martingales share the same square-variation
witness and that same witness is also their quadratic covariation, then their difference has zero
square variation. -/
private lemma sub_zeroSquareVariation_of_sharedWitness
    {ℱ : TimeFiltration} {M N A : ScalarProcess}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω - N t ω)
      (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · -- Proof comment: the zero compensator starts from `0` by definition.
    funext ω
    simp
  · -- Proof comment: the zero compensator is adapted at every deterministic time.
    intro t
    simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
  · -- Proof comment: the zero compensator has continuous sample paths.
    intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · -- Proof comment: the zero compensator is monotone because it is constant.
    intro ω s t hst
    simp
  · refine
      { local_martingale := ?_
        continuous := ?_ }
    · -- Proof comment: expand `(M - N)^2` into the shared-witness combination
      -- `(M^2 - A) + (N^2 - A) - 2 * (MN - A)`.
      convert
        (hAleft.local_martingale_sq_sub.add
          (hAright.local_martingale_sq_sub.sub
            ((hQuad.local_martingale_mul_sub.const_mul (2 : ℝ)).local_martingale))) using 1
      funext t ω
      ring
    · -- Proof comment: the same algebraic decomposition preserves pathwise continuity.
      intro ω
      exact
        (hAleft.local_martingale_sq_sub.continuous ω).add
          ((hAright.local_martingale_sq_sub.continuous ω).sub
            ((hQuad.local_martingale_mul_sub.const_mul (2 : ℝ)).continuous ω))

/-- Helper for Example 26.16: a continuous local martingale with identically zero square
variation and zero initial value is almost surely zero at every fixed deterministic time. -/
private lemma ae_eq_zero_at_time_of_zeroSquareVariation
    {ℱ : TimeFiltration} {X : ScalarProcess}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hXsq : IsContinuousSquareVariationProcess ℱ μ X (fun _ _ ↦ (0 : ℝ)))
    (hX0 : X 0 =ᵐ[μ] fun _ : Ω ↦ 0)
    (T : NNReal) :
    X T =ᵐ[μ] fun _ : Ω ↦ 0 := by
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hX with
    ⟨B, hB, huniq⟩
  have hCanonEqB :
      AreIndistinguishable μ (⟨X⟩[hX]) B := by
    exact huniq _ (continuousSquareVariationProcess_spec hX)
  have hBEqZero :
      AreIndistinguishable μ B (fun _ _ ↦ (0 : ℝ)) := by
    exact huniq _ hXsq
  have hCanonEqZero :
      AreIndistinguishable μ (⟨X⟩[hX]) (fun _ _ ↦ (0 : ℝ)) := by
    exact areIndistinguishable_trans hCanonEqB hBEqZero
  have hZeroAllTimes :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
    rcases hCanonEqZero with ⟨bad, hbad_meas, hbad_null, hbad_sub⟩
    have hbad_ae : ∀ᵐ ω ∂μ, ω ∉ bad :=
      compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hbad_ae] with ω hωbad t
    by_contra hneq
    exact hωbad (hbad_sub t hneq)
  have hConstAtTime :
      X T =ᵐ[μ] X 0 :=
    ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hZeroAllTimes T
  -- Proof comment: once the process is almost surely constant in time, the zero initial value
  -- forces the fixed-time value to vanish.
  exact hConstAtTime.trans hX0

/-- Helper for Example 26.16: two continuous local martingales with the same square-variation and
quadratic-covariation witnesses agree almost surely at every fixed deterministic time once they
agree at time `0`. -/
private lemma ae_eq_at_time_of_sharedWitness
    {ℱ : TimeFiltration} {M N A : ScalarProcess}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0)
    (T : NNReal) :
    M T =ᵐ[μ] N T := by
  have hSubSq :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ M t ω - N t ω)
        (fun _ _ ↦ (0 : ℝ)) :=
    sub_zeroSquareVariation_of_sharedWitness hMmart hNmart hAleft hAright hQuad
  have hSubZero :
      (fun ω ↦ M 0 ω - N 0 ω) =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- Proof comment: the shared initial-value hypothesis turns the difference process into a
    -- zero-start continuous local martingale.
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hSubAtTime :
      (fun ω ↦ M T ω - N T ω) =ᵐ[μ] fun _ : Ω ↦ 0 :=
    ae_eq_zero_at_time_of_zeroSquareVariation
      (ℱ := ℱ)
      (μ := μ)
      (X := fun t ω ↦ M t ω - N t ω)
      (hMmart.sub hNmart)
      hSubSq
      hSubZero
      T
  -- Proof comment: vanishing of the difference at time `T` is exactly the desired endpoint
  -- equality.
  filter_upwards [hSubAtTime] with ω hω
  exact sub_eq_zero.mp hω

/-- Helper for Example 26.16: deterministic-time modifications of continuous paths agree
simultaneously at all times almost surely. -/
private theorem ae_all_eq_of_modifications_of_continuous
    {X Y : ScalarProcess}
    (hXY : AreModifications μ X Y)
    (hXcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hYcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω := by
  have hRat : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = Y (q : NNReal) ω := by
    rw [ae_all_iff]
    intro q
    simpa using hXY (q : NNReal)
  filter_upwards [hRat] with ω hωRat t
  have hEqOn :
      Set.EqOn (fun s : NNReal ↦ X s ω) (fun s : NNReal ↦ Y s ω)
        (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    exact hωRat q
  -- Proof comment: equality on the dense set of nonnegative rationals upgrades to equality on all
  -- of `NNReal` because both sample paths are continuous.
  exact congrFun (Continuous.ext_on nnratDense (hXcont ω) (hYcont ω) hEqOn) t

/-- Helper for Example 26.16: an all-times almost-sure equality transports a square-variation
witness between continuous local martingales. -/
private theorem squareVariation_of_ae_allTimes_eq
    {ℱ : TimeFiltration} {M N A : ScalarProcess}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hAllEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω)
    (hNA : IsContinuousSquareVariationProcess ℱ μ N A) :
    IsContinuousSquareVariationProcess ℱ μ M A := by
  refine
    { zero := hNA.zero
      adapted := hNA.adapted
      continuous := hNA.continuous
      monotone := hNA.monotone
      local_martingale_sq_sub := ?_ }
  have hTargetAdapted :
      Adapted ℱ (fun t ω ↦ M t ω ^ 2 - A t ω) := by
    intro t
    -- Proof comment: the transported square-minus-bracket process is adapted because `M` is
    -- adapted and the compensator `A` stays unchanged.
    exact ((hM.adapted t).pow_const 2).sub (hNA.adapted t)
  have hTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω ^ 2 - A t ω := by
    intro ω
    -- Proof comment: continuity is preserved under the pointwise square and subtraction by the
    -- existing compensator path.
    exact ((hM.continuous ω).pow 2).sub (hNA.continuous ω)
  have hSqSubEq :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω ^ 2 - A t ω = N t ω ^ 2 - A t ω := by
    filter_upwards [hAllEq] with ω hω t
    -- Proof comment: the all-times equality identifies the square term pointwise.
    simp [hω t]
  -- Proof comment: once the compensated square processes agree at all times almost surely, the
  -- local-martingale witness transports directly.
  exact
    isLocalMartingale_congr_ae_allTimes
      hNA.local_martingale_sq_sub.local_martingale
      hTargetAdapted
      hTargetCont
      hSqSubEq

/-- Helper for Example 26.16: the shared-witness comparison can be upgraded from each fixed
deterministic time to one all-times almost-sure identity. -/
private lemma ae_eq_allTimes_of_sharedWitness
    {M N A : ScalarProcess}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω := by
  have hMods : AreModifications μ M N := by
    intro t
    -- Proof comment: the fixed-time shared-witness comparison already supplies the modification
    -- relation at each deterministic time.
    exact
      ae_eq_at_time_of_sharedWitness
        (ℱ := ℱ)
        (μ := μ)
        hMmart
        hNmart
        hAleft
        hAright
        hQuad
        hZero
        t
  -- Proof comment: continuity of both processes upgrades the timewise modification relation to a
  -- single null set controlling all times.
  exact
    ae_all_eq_of_modifications_of_continuous
      (μ := μ)
      hMods
      hMmart.continuous
      hNmart.continuous

/-- Helper for Example 26.16: if two square-variation owners have zero mixed quadratic
covariation, then the sum process has bracket equal to the sum of the two individual brackets. -/
private lemma addSquareVariation_of_zeroQuadraticCovariation
    {ℱ : TimeFiltration} {M N A B : ScalarProcess}
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hB : IsContinuousSquareVariationProcess ℱ μ N B)
    (hZero : IsContinuousQuadraticCovariationProcess ℱ μ M N (fun _ _ ↦ (0 : ℝ))) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω + N t ω)
      (fun t ω ↦ A t ω + B t ω) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · -- Proof comment: both bracket owners start from `0`, so their sum does as well.
    funext ω
    simp [hA.zero, hB.zero]
  · -- Proof comment: adaptedness is preserved by pointwise addition of the two owners.
    intro t
    exact (hA.adapted t).add (hB.adapted t)
  · -- Proof comment: the bracket sum is continuous because both component brackets are.
    intro ω
    exact (hA.continuous ω).add (hB.continuous ω)
  · -- Proof comment: monotonicity is preserved because both compensators are increasing.
    intro ω s t hst
    exact add_le_add (hA.monotone ω hst) (hB.monotone ω hst)
  · refine
      { local_martingale := ?_
        continuous := ?_ }
    · -- Proof comment: expand `(M + N)^2 - (A + B)` into the sum of the two square-minus-bracket
      -- terms and twice the zero mixed-covariation martingale `MN - 0`.
      convert
        (hA.local_martingale_sq_sub.add
          (hB.local_martingale_sq_sub.add
            ((hZero.local_martingale_mul_sub.const_mul (2 : ℝ)).local_martingale))) using 1
      funext t ω
      ring
    · -- Proof comment: the same algebraic decomposition is continuous pathwise.
      intro ω
      exact
        (hA.local_martingale_sq_sub.continuous ω).add
          ((hB.local_martingale_sq_sub.continuous ω).add
            ((hZero.local_martingale_mul_sub.const_mul (2 : ℝ)).continuous ω))

/-- Helper for Example 26.16: any chosen Brownian-coordinate local martingale witness carries the
canonical density-one bracket. -/
private theorem brownianCoordinateUnitBracket
    {ℱ : TimeFiltration} {B : VectorProcess}
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) :
    HasAbsolutelyContinuousSquareVariation
      (fun t ω ↦ B t ω i)
      (coordinateLocalMartingale i) := by
  rcases brownianCoordinateIdentityBracketData (ℱ := ℱ) (μ := μ) (B := B) hB i with
    ⟨_, _, hSquareVariation⟩
  refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hSquareVariation, ?_, ?_⟩
  · -- Proof comment: the Brownian coordinate bracket density is the deterministic constant `1`.
    simpa using
      (stronglyMeasurable_const.progMeasurable :
        ProgMeasurable ℱ (fun _ _ : Ω ↦ (1 : ℝ)))
  · -- Proof comment: integrating the density `1` yields the identity clock `t`.
    intro t ω
    simp

/-- Helper for Example 26.16: with the canonical density-one Brownian-coordinate bracket, the
bracket-density integral is exactly the plain time integral of the squared coefficient. -/
private theorem brownianCoordinateUnitBracketDensityIntegral
    {ℱ : TimeFiltration} {B : VectorProcess}
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (H : ScalarProcess) (i : Fin n) :
    Theorem25_22.bracketDensityIntegralUpTo
        (brownianCoordinateUnitBracket (μ := μ) (ℱ := ℱ) (B := B)
          hB coordinateLocalMartingale i)
        H
      =
        fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H s.toNNReal ω) ^ 2 := by
  -- Proof comment: the chosen coordinate bracket has density `1`, so the density factor
  -- disappears definitionally.
  funext t ω
  simp [Theorem25_22.bracketDensityIntegralUpTo, brownianCoordinateUnitBracket]

/-- Helper for Example 26.16: each canonical coordinate Itô integral already carries its
finite-horizon local-martingale and square-variation clauses. -/
private theorem coordinateIntegral_singleClausesUpTo
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) (T : NNReal) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i)) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i))
        (fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
  -- Proof comment: the coordinate integral is already the canonical Chapter 25 Itô integral, so
  -- the single-integral finite-horizon clauses come directly from `canonicalItoIntegral...UpTo`;
  -- the explicit density-one coordinate bracket turns the compensator into the plain integral of
  -- `(U_i)^2`.
  simpa [brownianCoordinateUnitBracketDensityIntegral] using
    Theorem25_22.canonicalItoIntegral_singleClausesUpTo
      (μ := μ)
      (ℱ := ℱ)
      (M := fun t ω ↦ B t ω i)
      (hM := coordinateLocalMartingale i)
      (hbr := brownianCoordinateUnitBracket
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        hB
        coordinateLocalMartingale
        i)
      (H := squaredBesselUnitDirection y B hn i)
      T
      (squaredBesselUnitDirection_progMeasurable (μ := μ) y hn hB i)
      (squaredBesselUnitDirection_squareIntegrableUpTo (μ := μ) y hn hB i T)

/-- Helper for Example 26.16: distinct canonical coordinate Itô integrals have zero finite-horizon
quadratic covariation because the Brownian coordinates are independent. -/
private theorem coordinateIntegrals_zeroQuadraticCovariationUpTo
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    {i j : Fin n} (hij : i ≠ j) (T : NNReal) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
      (continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (squaredBesselUnitDirection y B hn i))
      (continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale j)
        (squaredBesselUnitDirection y B hn j))
      0 := by
  have hIndep :
      IndepFun
        (fun ω ↦ fun t : NNReal ↦ B t ω i)
        (fun ω ↦ fun t : NNReal ↦ B t ω j)
        μ := by
    -- Proof comment: the Brownian-vector owner stores independence of the full coordinate
    -- processes, not only their fixed-time marginals.
    simpa [CoordinateProcess.toEuclidean] using
      hB.1.iIndepFun.indepFun (i := i) (j := j) hij
  -- Proof comment: with the coordinate-process independence in hand, the Chapter 25 pair theorem
  -- gives the zero-covariation clause on every deterministic horizon.
  exact
    Theorem25_22.quadraticCovariation_zero_of_indepFun
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := fun t ω ↦ B t ω i)
      (M₂ := fun t ω ↦ B t ω j)
      (hM₁ := coordinateLocalMartingale i)
      (hM₂ := coordinateLocalMartingale j)
      (hbr₁ := brownianCoordinateUnitBracket
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        hB
        coordinateLocalMartingale
        i)
      (hbr₂ := brownianCoordinateUnitBracket
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        hB
        coordinateLocalMartingale
        j)
      (H₁ := squaredBesselUnitDirection y B hn i)
      (H₂ := squaredBesselUnitDirection y B hn j)
      T
      (squaredBesselUnitDirection_progMeasurable (μ := μ) y hn hB i)
      (squaredBesselUnitDirection_progMeasurable (μ := μ) y hn hB j)
      (squaredBesselUnitDirection_squareIntegrableUpTo (μ := μ) y hn hB i T)
      (squaredBesselUnitDirection_squareIntegrableUpTo (μ := μ) y hn hB j T)
      (Theorem25_22.canonicalSelf
        (μ := μ)
        (ℱ := ℱ)
        (M := fun t ω ↦ B t ω i)
        (hM := coordinateLocalMartingale i)
        (hbr := brownianCoordinateUnitBracket
          (μ := μ)
          (ℱ := ℱ)
          (B := B)
          hB
          coordinateLocalMartingale
          i)
        (H := squaredBesselUnitDirection y B hn i))
      (Theorem25_22.canonicalSelf
        (μ := μ)
        (ℱ := ℱ)
        (M := fun t ω ↦ B t ω j)
        (hM := coordinateLocalMartingale j)
        (hbr := brownianCoordinateUnitBracket
          (μ := μ)
          (ℱ := ℱ)
          (B := B)
          hB
          coordinateLocalMartingale
          j)
        (H := squaredBesselUnitDirection y B hn j))
      hIndep

/-- Helper for Example 26.16: finite-horizon equality is stable under addition. -/
private theorem eqUpTo_add
    {T : NNReal}
    {X X' Y Y' : ScalarProcess}
    (hX : EqUpTo μ T X X') (hY : EqUpTo μ T Y Y') :
    EqUpTo μ T
      (fun t ω ↦ X t ω + Y t ω)
      (fun t ω ↦ X' t ω + Y' t ω) := by
  rcases hX with ⟨NX, hNX_meas, hNX_null, hNX_sub⟩
  rcases hY with ⟨NY, hNY_meas, hNY_null, hNY_sub⟩
  refine ⟨NX ∪ NY, hNX_meas.union hNY_meas, ?_, ?_⟩
  · have hUnionLe : μ (NX ∪ NY) ≤ μ NX + μ NY := measure_union_le NX NY
    refine le_antisymm ?_ bot_le
    simpa [hNX_null, hNY_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXω : X t ω ≠ X' t ω
    · exact Set.mem_union_left NY (hNX_sub ht hXω)
    · have hEqX : X t ω = X' t ω := not_ne_iff.mp hXω
      have hYω : Y t ω ≠ Y' t ω := by
        intro hEqY
        apply hω
        simpa [hEqX, hEqY]
      exact Set.mem_union_right NX (hNY_sub ht hYω)

/-- Helper for Example 26.16: finite sums preserve equality up to a deterministic horizon. -/
private theorem eqUpTo_finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {T : NNReal}
    {X Y : ι → ScalarProcess}
    (hXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i)) :
    EqUpTo μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ X i t ω))
      (fun t ω ↦ Finset.sum s (fun i ↦ Y i t ω)) := by
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sums are definitionally the same zero process.
      simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert a s ha ih =>
      have hsXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i) := by
        intro i hi
        exact hXY i (by simp [hi])
      -- Proof comment: rewrite both finite sums into head-plus-tail form and combine the two
      -- horizonwise equalities by additivity.
      simpa [Finset.sum_insert, ha] using eqUpTo_add (hXY a (by simp)) (ih hsXY)

/-- Helper for Example 26.16: finite sums preserve the deterministic-horizon local-martingale-up-to
package. -/
private theorem finsetSum_isContinuousLocalMartingaleUpTo
    {ℱ : TimeFiltration}
    (s : Finset (Fin n)) {T : NNReal} {N : Fin n → ScalarProcess}
    (hN : ∀ i ∈ s, IsContinuousLocalMartingaleUpTo ℱ μ T (N i)) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ N i t ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ _ ↦ (0 : ℝ), ?_, ?_⟩
      · refine
          { local_martingale := ?_
            continuous := ?_ }
        · simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale
        · intro ω
          simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      · simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert i s hi hs =>
      rcases hN i (by simp) with ⟨Ni, hNi, hEqi⟩
      have hsN : ∀ j ∈ s, IsContinuousLocalMartingaleUpTo ℱ μ T (N j) := by
        intro j hj
        exact hN j (by simp [hj])
      rcases hs hsN with ⟨Ns, hNs, hEqs⟩
      let Nsum : ScalarProcess := fun t ω ↦ Ni t ω + Ns t ω
      refine ⟨Nsum, ?_, ?_⟩
      · refine
          { local_martingale := hNi.local_martingale.add hNs.local_martingale
            continuous := ?_ }
        intro ω
        -- Proof comment: the global witness sum is continuous because both component witnesses
        -- already have continuous sample paths.
        simpa [Nsum] using (hNi.continuous ω).add (hNs.continuous ω)
      · have hEqSum :
            EqUpTo μ T
              (fun t ω ↦ N i t ω + Finset.sum s (fun j ↦ N j t ω))
              Nsum :=
          eqUpTo_add hEqi hEqs
        -- Proof comment: after rewriting the visible finite sum into head-plus-tail form, the
        -- combined equality witness applies directly.
        simpa [Nsum, Finset.sum_insert, hi] using hEqSum

/-- Helper for Example 26.16: deterministic stopped martingale owners for all horizons recover a
genuine continuous local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingale
    {ℱ : TimeFiltration} {Y : ScalarProcess}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic horizons `n` increase pointwise to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      have hDet :
          Martingale
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime
          (ℱ := ℱ)
          (μ := μ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)
      -- Proof comment: stopping again at the same deterministic horizon does not change the
      -- process, so the uniform-integrability clause descends directly.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hDet.2
    exact ⟨hMart, hUI⟩

/-- Helper for Example 26.16: equality up to a deterministic horizon survives stopping both
processes at that same horizon, because the stopped time is always a point `≤ T`. -/
private theorem eqUpTo_stoppedProcess_const
    {α : Type*} {T U : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ U
      (stoppedProcess X (fun _ ↦ (T : ENNReal)))
      (stoppedProcess Y (fun _ ↦ (T : ENNReal))) := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  have hmin : min t T ≤ T := min_le_right _ _
  -- Proof comment: after deterministic stopping at `T`, every visible sample is evaluated at
  -- time `min t T`, so the original `EqUpTo` witness still applies.
  exact hN_sub hmin (by simpa [stoppedProcessConstTime_eq_min] using hω)

/-- Helper for Example 26.16: a square-variation witness up to `T` can be stopped at `T` and then
reused as a square-variation witness up to any comparison horizon. -/
private theorem stoppedSquareVariationProcessUpTo_const
    {ℱ : TimeFiltration} {T U : NNReal} {N A : ScalarProcess}
    (hNA : IsContinuousSquareVariationProcessUpTo ℱ μ T N A) :
    IsContinuousSquareVariationProcessUpTo ℱ μ U
      (stoppedProcess N (fun _ ↦ (T : ENNReal)))
      (stoppedProcess A (fun _ ↦ (T : ENNReal))) := by
  rcases hNA with ⟨N', A', hNA', hEqN, hEqA⟩
  have hStopped :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess N' (fun _ ↦ (T : ENNReal)))
        (stoppedProcess A' (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: once the owner pair is genuine, Theorem 21.75 preserves the square
    -- variation package under deterministic stopping.
    exact
      stoppedSquareVariationProcess
        (ℱ := ℱ)
        (μ := μ)
        hNA'
        (isStoppingTime_const ℱ T)
  -- Proof comment: transport the stopped genuine witness back to the visible stopped processes
  -- using the stopped `EqUpTo` comparisons on both coordinates.
  exact
    isContinuousSquareVariationProcessUpTo_of_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      (eqUpTo_stoppedProcess_const (μ := μ) (T := T) (U := U) hEqN)
      (eqUpTo_stoppedProcess_const (μ := μ) (T := T) (U := U) hEqA)
      (isContinuousSquareVariationProcessUpTo_of_isContinuousSquareVariationProcess
        (μ := μ)
        (ℱ := ℱ)
        (T := U)
        hStopped)

/-- Helper for Example 26.16: the canonical deterministic-cutoff coordinate already carries the
genuine continuous local martingale and explicit stopped clock. -/
private theorem cutoffCoordinateHasExplicitSquareVariation
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) (T : NNReal) :
    let NiT :=
      continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (processBeforeStoppingTime (squaredBesselUnitDirection y B hn i) (fun _ ↦ (T : ENNReal)))
    IsContinuousLocalMartingale ℱ μ NiT ∧
      IsContinuousSquareVariationProcess ℱ μ NiT
        (fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
            (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
  let U : ScalarProcess := squaredBesselUnitDirection y B hn i
  let hbr :=
    brownianCoordinateUnitBracket
      (μ := μ)
      (ℱ := ℱ)
      (B := B)
      hB
      coordinateLocalMartingale
      i
  let NiT : ScalarProcess :=
    continuousLocalMartingaleItoIntegralProcess
      (coordinateLocalMartingale i)
      (processBeforeStoppingTime U (fun _ ↦ (T : ENNReal)))
  have hCut :=
    Theorem25_22.canonicalConstCutoffGlobalClauses
      (μ := μ)
      (ℱ := ℱ)
      (M := fun t ω ↦ B t ω i)
      (H := U)
      (hM := coordinateLocalMartingale i)
      (hbr := hbr)
      T
      (squaredBesselUnitDirection_progMeasurable (μ := μ) y hn hB i)
      (by
        -- Proof comment: the Brownian coordinate bracket has density `1`, so the bracket-energy
        -- hypothesis is exactly the deterministic-horizon square integrability of `U_i`.
        simpa [U, hbr, Theorem25_22.squareVariationDensity] using
          squaredBesselUnitDirection_squareIntegrableUpTo (μ := μ) y hn hB i T)
  have hClockEq :
      Theorem25_22.bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime U (fun _ ↦ (T : ENNReal))) =
        (fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
            (U s.toNNReal ω) ^ 2) := by
    funext t ω
    rw [brownianCoordinateUnitBracketDensityIntegral
      (μ := μ)
      (ℱ := ℱ)
      (B := B)
      hB
      coordinateLocalMartingale]
    by_cases ht : t ≤ T
    · -- Proof comment: on `[0, t]` the deterministic cutoff already agrees pointwise with the
      -- original coefficient, so the explicit clock reduces immediately to the unclipped one.
      have hIntegralEq :
          (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            (processBeforeStoppingTime U (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2) =
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (U s.toNNReal ω) ^ 2 := by
        refine integral_congr_ae ?_
        rw [ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall ?_
        intro s hs
        have hs_mem :
            s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs.1, hs.2.trans (show (t : ℝ) ≤ (T : ℝ) by
          exact_mod_cast ht)⟩
        simpa [U] using congrArg (fun x : ℝ ↦ x ^ 2)
          ((Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := U) T ω) hs_mem)
      simpa [min_eq_left ht] using hIntegralEq
    · have hTt : T ≤ t := le_of_not_ge ht
      have hTt_real : (T : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast hTt
      let f : ℝ → ℝ := fun s ↦
        (processBeforeStoppingTime U (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2
      have hCutoffZero :
          ∀ ⦃s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) (t : ℝ) →
            ¬ s ∈ Set.Icc (0 : ℝ) (T : ℝ) → f s = 0 := by
        intro s hs hs_not_mem
        have hsT : ¬ s ≤ (T : ℝ) := by
          intro hs_le_T
          exact hs_not_mem ⟨hs.1, hs_le_T⟩
        have hs_not_cutoff : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
          intro hs_cutoff
          exact hsT ((Real.toNNReal_le_iff_le_coe).1 (by exact_mod_cast hs_cutoff))
        -- Proof comment: strictly after `T`, the deterministic cutoff kills the coefficient.
        simp [f, ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_cutoff]
      have hIndicatorEq :
          (∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s) =
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := by
        refine integral_congr_ae ?_
        rw [ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall ?_
        intro s hs
        by_cases hs_mem : s ∈ Set.Icc (0 : ℝ) (T : ℝ)
        · simp [Set.indicator_of_mem, hs_mem]
        · simp [Set.indicator_of_notMem, hs_mem, hCutoffZero hs hs_mem]
      have hSubset :
          Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
        intro s hs
        exact ⟨hs.1, hs.2.trans hTt_real⟩
      have hReplace :
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) =
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (U s.toNNReal ω) ^ 2 := by
        refine integral_congr_ae ?_
        rw [ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall ?_
        intro s hs
        simpa [f, U] using congrArg (fun x : ℝ ↦ x ^ 2)
          ((Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := U) T ω) hs)
      calc
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (processBeforeStoppingTime U (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 =
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := hIndicatorEq
        _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
          rw [Measure.restrict_restrict, integral_indicator measurableSet_Icc]
          simp [Set.inter_eq_right.mpr hSubset, measurableSet_Icc]
        _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (U s.toNNReal ω) ^ 2 := hReplace
        _ = ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ), (U s.toNNReal ω) ^ 2 := by
          simp [min_eq_right hTt]
  refine ⟨hCut.1, ?_⟩
  -- Proof comment: after the density-one simplification, the cutoff bracket is exactly the
  -- explicit integral up to `min t T`.
  simpa [NiT, U, hClockEq] using hCut.2

/-- Helper for Example 26.16: before the cutoff horizon, the stopped visible coordinate agrees
with the canonical deterministic-cutoff coordinate. -/
private theorem stoppedCanonicalCoordinate_eqUpTo_cutoffCoordinate
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) (T : NNReal) :
    EqUpTo μ T
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i))
        (fun _ ↦ (T : ENNReal)))
      (continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (processBeforeStoppingTime (squaredBesselUnitDirection y B hn i) (fun _ ↦ (T : ENNReal)))) := by
  have hStopEq :
      EqUpTo μ T
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess
            (coordinateLocalMartingale i)
            (squaredBesselUnitDirection y B hn i))
          (fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i)) := by
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    intro t ht ω hω
    -- Proof comment: on `[0, T]`, deterministic stopping leaves the original coordinate integral
    -- untouched.
    simp [stoppedProcessConstTime_eq_min, min_eq_left ht]
  have hCutoffEq :
      EqUpTo μ T
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i))
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (processBeforeStoppingTime (squaredBesselUnitDirection y B hn i)
            (fun _ ↦ (T : ENNReal)))) :=
    Theorem25_22.continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
      (μ := μ)
      (ℱ := ℱ)
      (M := fun t ω ↦ B t ω i)
      (H := squaredBesselUnitDirection y B hn i)
      (hM := coordinateLocalMartingale i)
      T
  -- Proof comment: compose the literal stopping identity with the Chapter 25 cutoff comparison.
  exact eqUpTo_trans hStopEq hCutoffEq

/-- Helper for Example 26.16: the stopped visible coordinate inherits the explicit deterministic
cutoff clock from the canonical cutoff owner, but currently only on the `...UpTo` surface. -/
private theorem stoppedCanonicalCoordinateHasExplicitSquareVariationUpTo
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) (T U : NNReal) :
    IsContinuousSquareVariationProcessUpTo ℱ μ U
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i))
        (fun _ ↦ (T : ENNReal)))
      (fun t ω ↦
        ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
          (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
  let NiT : ScalarProcess :=
    continuousLocalMartingaleItoIntegralProcess
      (coordinateLocalMartingale i)
      (processBeforeStoppingTime (squaredBesselUnitDirection y B hn i) (fun _ ↦ (T : ENNReal)))
  let AiT : ScalarProcess := fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
      (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2
  have hCutoff :
      IsContinuousLocalMartingale ℱ μ NiT ∧
        IsContinuousSquareVariationProcess ℱ μ NiT AiT := by
    simpa [NiT, AiT] using
      cutoffCoordinateHasExplicitSquareVariation
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        T
  have hStoppedCutoff :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess NiT (fun _ ↦ (T : ENNReal)))
        AiT := by
    have hStopped :
        IsContinuousSquareVariationProcess ℱ μ
          (stoppedProcess NiT (fun _ ↦ (T : ENNReal)))
          (stoppedProcess AiT (fun _ ↦ (T : ENNReal))) := by
      -- Proof comment: first stop the genuine cutoff owner and its explicit clock at the same
      -- deterministic horizon.
      exact
        stoppedSquareVariationProcess
          (ℱ := ℱ)
          (μ := μ)
          hCutoff.2
          (isStoppingTime_const ℱ T)
    -- Proof comment: the explicit clock is already frozen after `T`, so the extra stop on the
    -- witness disappears.
    simpa [AiT, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hStopped
  have hEqStopped :
      EqUpTo μ U
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess
            (coordinateLocalMartingale i)
            (squaredBesselUnitDirection y B hn i))
          (fun _ ↦ (T : ENNReal)))
        (stoppedProcess NiT (fun _ ↦ (T : ENNReal))) := by
    have hEqBase :
        EqUpTo μ U
          (stoppedProcess
            (stoppedProcess
              (continuousLocalMartingaleItoIntegralProcess
                (coordinateLocalMartingale i)
                (squaredBesselUnitDirection y B hn i))
              (fun _ ↦ (T : ENNReal)))
            (fun _ ↦ (T : ENNReal)))
          (stoppedProcess NiT (fun _ ↦ (T : ENNReal))) :=
      eqUpTo_stoppedProcess_const
        (μ := μ)
        (T := T)
        (U := U)
        (stoppedCanonicalCoordinate_eqUpTo_cutoffCoordinate
          (μ := μ)
          (ℱ := ℱ)
          (B := B)
          y
          hn
          coordinateLocalMartingale
          i
          T)
    -- Proof comment: stopping the already stopped visible coordinate a second time at the same
    -- horizon does not change it.
    simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hEqBase
  -- Proof comment: the cutoff-canonical square-variation witness now transports to the visible
  -- stopped coordinate, but only on the deterministic-horizon `...UpTo` interface.
  exact
    isContinuousSquareVariationProcessUpTo_of_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      hEqStopped
      (eqUpTo_rfl (μ := μ) U AiT)
      (isContinuousSquareVariationProcessUpTo_of_isContinuousSquareVariationProcess
        (μ := μ)
        (ℱ := ℱ)
        (T := U)
        hStoppedCutoff)

/-- Helper for Example 26.16: cutting off an already deterministically cutoff coefficient at a
later deterministic horizon does not change it. -/
private theorem processBeforeStoppingTime_constCutoff_eq_self_of_le
    {H : ScalarProcess} {T U : NNReal} (hTU : T ≤ U) :
    processBeforeStoppingTime
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (fun _ ↦ (U : ENNReal)) =
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
  funext t ω
  have hTU' : (T : ENNReal) ≤ (U : ENNReal) := by
    exact_mod_cast hTU
  by_cases hU : (t : ENNReal) ≤ (U : ENNReal)
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · -- Proof comment: before the original cutoff time, both deterministic cutoffs return the
      -- original coefficient value.
      simp [processBeforeStoppingTime_apply, hU, hT]
    · -- Proof comment: between `T` and `U`, both deterministic cutoffs already vanish.
      simp [processBeforeStoppingTime_apply, hU, hT]
  · have hT : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
      intro ht
      exact hU (le_trans ht hTU')
    -- Proof comment: after the later cutoff horizon, both sides are in the zero branch.
    rw [processBeforeStoppingTime_apply, if_neg hU, processBeforeStoppingTime_apply, if_neg hT]

/-- Helper for Example 26.16: the visible stopped coordinate should inherit the genuine explicit
stopped clock from the deterministic-cutoff owner. -/
private theorem stoppedCoordinateHasExplicitSquareVariation
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n)
    (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (coordinateLocalMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (fun t ω ↦ B t ω i))
    (i : Fin n) (T : NNReal) :
    IsContinuousSquareVariationProcess ℱ μ
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i))
        (fun _ ↦ (T : ENNReal)))
      (fun t ω ↦
        ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
          (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
  let visibleCoordinate : ScalarProcess :=
    stoppedProcess
      (continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (squaredBesselUnitDirection y B hn i))
      (fun _ ↦ (T : ENNReal))
  let NiT : ScalarProcess :=
    continuousLocalMartingaleItoIntegralProcess
      (coordinateLocalMartingale i)
      (processBeforeStoppingTime (squaredBesselUnitDirection y B hn i) (fun _ ↦ (T : ENNReal)))
  let AiT : ScalarProcess := fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
      (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2
  have hVisibleUpTo :
      ∀ U : NNReal,
        IsContinuousLocalMartingaleUpTo ℱ μ U
          (continuousLocalMartingaleItoIntegralProcess
            (coordinateLocalMartingale i)
            (squaredBesselUnitDirection y B hn i)) := by
    intro U
    exact
      (coordinateIntegral_singleClausesUpTo
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        U).1
  have hVisibleMart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess
          (coordinateLocalMartingale i)
          (squaredBesselUnitDirection y B hn i)) := by
    -- Proof comment: the unstopped visible coordinate already has deterministic-horizon
    -- local-martingale owners, so the constant-stop globalization theorem upgrades it to a
    -- genuine continuous local martingale.
    refine
      isContinuousLocalMartingale_of_constStoppedMartingale
        (ℱ := ℱ)
        (μ := μ)
        (Y :=
          continuousLocalMartingaleItoIntegralProcess
            (coordinateLocalMartingale i)
            (squaredBesselUnitDirection y B hn i))
        (hY_adapted := (hVisibleUpTo 0).adapted)
        (hY_cont := (hVisibleUpTo 0).continuous)
        ?_
    intro U
    simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (τ := fun _ ↦ (U : ENNReal))
        (M :=
          continuousLocalMartingaleItoIntegralProcess
            (coordinateLocalMartingale i)
            (squaredBesselUnitDirection y B hn i))
        (hVisibleUpTo U)
        U
  have hVisibleStoppedMart :
      IsContinuousLocalMartingale ℱ μ visibleCoordinate := by
    -- Proof comment: the visible stopped coordinate has continuous sample paths and each of its
    -- deterministic stops is a true martingale because stopping twice just clips at `min U T`.
    refine
      isContinuousLocalMartingale_of_constStoppedMartingale
        (ℱ := ℱ)
        (μ := μ)
        (Y := visibleCoordinate)
        (hY_adapted := by
          intro U
          exact
            (hVisibleMart.adapted.stronglyAdapted.stoppedProcess
              hVisibleMart.continuous
              (isStoppingTime_const ℱ T)).adapted U)
        (hY_cont := by
          simpa [visibleCoordinate] using
            (continuous_stoppedProcess_of_continuous hVisibleMart.continuous))
        ?_
    intro U
    simpa [visibleCoordinate, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm]
      using
        IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
          (ℱ := ℱ)
          (μ := μ)
          (τ := fun _ ↦ (min U T : ENNReal))
          (M :=
            continuousLocalMartingaleItoIntegralProcess
              (coordinateLocalMartingale i)
              (squaredBesselUnitDirection y B hn i))
          (hVisibleUpTo (min U T))
          (min U T)
  have hCutoff :
      IsContinuousLocalMartingale ℱ μ NiT ∧
        IsContinuousSquareVariationProcess ℱ μ NiT AiT := by
    simpa [NiT, AiT] using
      cutoffCoordinateHasExplicitSquareVariation
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        T
  have hStoppedCutoff :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess NiT (fun _ ↦ (T : ENNReal)))
        AiT := by
    have hStopped :
        IsContinuousSquareVariationProcess ℱ μ
          (stoppedProcess NiT (fun _ ↦ (T : ENNReal)))
          (stoppedProcess AiT (fun _ ↦ (T : ENNReal))) := by
      -- Proof comment: first stop the genuine cutoff owner and its explicit clock at the same
      -- deterministic horizon.
      exact
        stoppedSquareVariationProcess
          (ℱ := ℱ)
          (μ := μ)
          hCutoff.2
          (isStoppingTime_const ℱ T)
    -- Proof comment: the explicit cutoff clock is already frozen after `T`, so the extra stop on
    -- the witness disappears.
    simpa [AiT, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      hStopped
  have hEqStopped :
      ∀ U : NNReal,
        EqUpTo μ U
          visibleCoordinate
          (stoppedProcess NiT (fun _ ↦ (T : ENNReal))) := by
    intro U
    have hEqBase :
        EqUpTo μ U
          (stoppedProcess
            (stoppedProcess
              (continuousLocalMartingaleItoIntegralProcess
                (coordinateLocalMartingale i)
                (squaredBesselUnitDirection y B hn i))
              (fun _ ↦ (T : ENNReal)))
            (fun _ ↦ (T : ENNReal)))
          (stoppedProcess NiT (fun _ ↦ (T : ENNReal))) :=
      eqUpTo_stoppedProcess_const
        (μ := μ)
        (T := T)
        (U := U)
        (stoppedCanonicalCoordinate_eqUpTo_cutoffCoordinate
          (μ := μ)
          (ℱ := ℱ)
          (B := B)
          y
          hn
          coordinateLocalMartingale
          i
          T)
    -- Proof comment: stopping the already stopped visible coordinate a second time at `T` does
    -- not change it.
    simpa [visibleCoordinate, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm]
      using hEqBase
  have hMods :
      AreModifications μ
        visibleCoordinate
        (stoppedProcess NiT (fun _ ↦ (T : ENNReal))) := by
    intro U
    rcases eqUpTo_forall_eq (μ := μ) (T := U) (hEqStopped U) with
      ⟨bad, hbad_meas, hbad_null, hbad_eq⟩
    refine ae_iff.2 ⟨bad, hbad_meas, hbad_null, ?_⟩
    intro ω hω
    by_contra hbadω
    exact hω (hbad_eq le_rfl hbadω)
  have hAllEq :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        visibleCoordinate t ω =
          stoppedProcess NiT (fun _ ↦ (T : ENNReal)) t ω := by
    -- Proof comment: fixed-time equality for every deterministic time upgrades to one common null
    -- set because both stopped processes have continuous sample paths.
    exact
      ae_all_eq_of_modifications_of_continuous
        (μ := μ)
        hMods
        hVisibleStoppedMart.continuous
        (continuous_stoppedProcess_of_continuous hCutoff.1.continuous)
  -- Proof comment: transport the genuine cutoff-owner bracket through the all-times almost-sure
  -- identity with the visible stopped coordinate.
  exact
    squareVariation_of_ae_allTimes_eq
      (μ := μ)
      (ℱ := ℱ)
      hVisibleStoppedMart
      hAllEq
      hStoppedCutoff

/-- Helper for Example 26.16: a zero quadratic-covariation witness up to `T` upgrades to a
genuine zero witness after deterministically stopping both coordinates at `T`. -/
private theorem stoppedZeroQuadraticCovariation_of_upTo
    {ℱ : TimeFiltration} {T : NNReal} {M N : ScalarProcess}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hUpTo : IsContinuousQuadraticCovariationProcessUpTo ℱ μ T M N 0) :
    IsContinuousQuadraticCovariationProcess ℱ μ
      (stoppedProcess M (fun _ ↦ (T : ENNReal)))
      (stoppedProcess N (fun _ ↦ (T : ENNReal)))
      0 := by
  let σ : Ω → ENNReal := fun _ ↦ (T : ENNReal)
  have hσ : IsStoppingTime ℱ σ := by
    simpa [σ] using isStoppingTime_const ℱ T
  rcases hUpTo with ⟨Mw, Nw, Aw, hMwNwAw, hEqMw, hEqNw, hEqAw⟩
  have hStoppedDriver :
      IsLocalMartingale ℱ μ
        (stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ) := by
    -- Proof comment: deterministically stopping the genuine compensated-product witness preserves
    -- its local-martingale property.
    exact
      _root_.ProbabilityTheory.isLocalMartingale_stoppedProcess
        hMwNwAw.local_martingale_mul_sub.local_martingale
        hMwNwAw.local_martingale_mul_sub.continuous
        hσ
  have hStoppedMAdapted : Adapted ℱ (stoppedProcess M σ) :=
    (hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hσ).adapted
  have hStoppedNAdapted : Adapted ℱ (stoppedProcess N σ) :=
    (hN.adapted.stronglyAdapted.stoppedProcess hN.continuous hσ).adapted
  have hStoppedTargetAdapted :
      Adapted ℱ
        (fun t ω ↦
          stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    exact
      (hStoppedMAdapted.mul hStoppedNAdapted).sub
        (adapted_const' ℱ (fun _ : NNReal ↦ (0 : ℝ)))
  have hStoppedTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦
        stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
    intro ω
    -- Proof comment: deterministic stopping preserves continuity of both coordinates, so their
    -- stopped product remains continuous.
    exact
      ((continuous_stoppedProcess_of_continuous hM.continuous ω).mul
        (continuous_stoppedProcess_of_continuous hN.continuous ω)).sub
        (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqMw with
    ⟨SMw, hSMwMeas, hSMwNull, hSMwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqNw with
    ⟨SNw, hSNwMeas, hSNwNull, hSNwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqAw with
    ⟨SAw, hSAwMeas, hSAwNull, hSAwEq⟩
  have hStoppedEq :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          (stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    let S : Set Ω := (SMw ∪ SNw) ∪ SAw
    have hSnull : μ S = 0 := by
      have hLeftNull : μ (SMw ∪ SNw) = 0 := by
        have hUnionLe : μ (SMw ∪ SNw) ≤ μ SMw + μ SNw := measure_union_le SMw SNw
        refine le_antisymm ?_ bot_le
        simpa [hSMwNull, hSNwNull] using hUnionLe
      have hUnionLe : μ ((SMw ∪ SNw) ∪ SAw) ≤ μ (SMw ∪ SNw) + μ SAw :=
        measure_union_le (SMw ∪ SNw) SAw
      refine le_antisymm ?_ bot_le
      simpa [S, hLeftNull, hSAwNull] using hUnionLe
    refine ae_iff.2 ?_
    refine measure_mono_null ?_ hSnull
    intro ω hω
    have hωMw : ω ∉ SMw := by
      exact fun hSMwω ↦ hω (Set.mem_union_left SAw (Set.mem_union_left SNw hSMwω))
    have hωNw : ω ∉ SNw := by
      exact fun hSNwω ↦ hω (Set.mem_union_left SAw (Set.mem_union_right SMw hSNwω))
    have hωAw : ω ∉ SAw := by
      exact fun hSAwω ↦ hω (Set.mem_union_right (SMw ∪ SNw) hSAwω)
    intro t
    have hMwStopped :
        stoppedProcess Mw σ t ω = stoppedProcess M σ t ω := by
      have hEq : Mw (min t T) ω = M (min t T) ω :=
        hSMwEq (min_le_right _ _) hωMw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hNwStopped :
        stoppedProcess Nw σ t ω = stoppedProcess N σ t ω := by
      have hEq : Nw (min t T) ω = N (min t T) ω :=
        hSNwEq (min_le_right _ _) hωNw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hAwStopped :
        stoppedProcess Aw σ t ω = 0 := by
      have hEq : Aw (min t T) ω = 0 := hSAwEq (min_le_right _ _) hωAw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    calc
      stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          stoppedProcess Mw σ t ω * stoppedProcess Nw σ t ω - stoppedProcess Aw σ t ω := by
        simp [σ, stoppedProcess]
      _ = stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
        rw [hMwStopped, hNwStopped, hAwStopped]
  refine
    { zero := by
        funext ω
        simp [σ, stoppedProcess]
      adapted := by
        intro t
        exact (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
      continuous := by
        intro ω
        exact (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := by
        -- Proof comment: after stopping, the compensated-product driver agrees almost surely at
        -- all times with the target stopped product because the compensator coordinate is
        -- `EqUpTo` to `0`.
        exact
          isLocalMartingale_congr_ae_allTimes
            hStoppedDriver
            hStoppedTargetAdapted
            hStoppedTargetCont
            hStoppedEq }

/-- Helper for Example 26.16: quadratic covariation is additive in the right argument. -/
private theorem quadraticCovariation_add_right
    {ℱ : TimeFiltration} {M N P A B : ScalarProcess}
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hB : IsContinuousQuadraticCovariationProcess ℱ μ M P B) :
    IsContinuousQuadraticCovariationProcess ℱ μ
      M
      (fun t ω ↦ N t ω + P t ω)
      (fun t ω ↦ A t ω + B t ω) := by
  refine
    { zero := by
        simp [hA.zero, hB.zero]
      adapted := by
        intro t
        exact (hA.adapted t).add (hB.adapted t)
      continuous := by
        intro ω
        exact (hA.continuous ω).add (hB.continuous ω)
      locally_finite_variation := ?_
      local_martingale_mul_sub := ?_ }
  · filter_upwards [hA.locally_finite_variation, hB.locally_finite_variation] with ω hωA hωB
    let GA : C(NNReal, ℝ) := ⟨fun t ↦ A t ω, hA.continuous ω⟩
    let GB : C(NNReal, ℝ) := ⟨fun t ↦ B t ω, hB.continuous ω⟩
    have hGA : GA ∈ continuousVariationSubmodule := by
      exact (mem_continuousVariationSubmodule_iff GA).2 hωA
    have hGB : GB ∈ continuousVariationSubmodule := by
      exact (mem_continuousVariationSubmodule_iff GB).2 hωB
    have hAdd : GA + GB ∈ continuousVariationSubmodule := by
      exact Submodule.add_mem continuousVariationSubmodule hGA hGB
    -- Proof comment: almost every pathwise sum of two finite-variation compensators still has
    -- locally finite variation.
    simpa [GA, GB] using (mem_continuousVariationSubmodule_iff (GA + GB)).1 hAdd
  · -- Proof comment: expand the compensated product against `N + P` into the sum of the two
    -- existing compensated-product local martingales.
    convert hA.local_martingale_mul_sub.add hB.local_martingale_mul_sub using 1
    funext t ω
    ring

/-- Helper for Example 26.16: quadratic covariation with a finite sum is the sum of the
individual quadratic covariations. -/
private theorem quadraticCovariation_finsetSum_right
    {ℱ : TimeFiltration} (s : Finset (Fin n))
    {M : ScalarProcess} {N A : Fin n → ScalarProcess}
    (hNA :
      ∀ i ∈ s, IsContinuousQuadraticCovariationProcess ℱ μ M (N i) (A i)) :
    IsContinuousQuadraticCovariationProcess ℱ μ
      M
      (fun t ω ↦ ∑ i in s, N i t ω)
      (fun t ω ↦ ∑ i in s, A i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine
        { zero := by simp
          adapted := by
            intro t
            simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
          continuous := by
            intro ω
            simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
          locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
          local_martingale_mul_sub := by
            simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale }
  | @insert i s hi hs =>
      have hsNA :
          ∀ j ∈ s, IsContinuousQuadraticCovariationProcess ℱ μ M (N j) (A j) := by
        intro j hj
        exact hNA j (by simp [hj])
      -- Proof comment: rewrite the finite sum into head-plus-tail form and use additivity of
      -- quadratic covariation in the second slot.
      simpa [Finset.sum_insert, hi] using
        quadraticCovariation_add_right
          (hNA i (by simp))
          (hs hsNA)

/-- Helper for Example 26.16: finite sums of square-variation processes with pairwise zero mixed
quadratic covariation have square variation equal to the sum of the component brackets. -/
private theorem finsetSumSquareVariation_of_pairwiseZeroQuadraticCovariation
    {ℱ : TimeFiltration} (s : Finset (Fin n))
    {N A : Fin n → ScalarProcess}
    (hNA :
      ∀ i ∈ s, IsContinuousSquareVariationProcess ℱ μ (N i) (A i))
    (hZero :
      ∀ ⦃i j : Fin n⦄, i ∈ s → j ∈ s → i ≠ j →
        IsContinuousQuadraticCovariationProcess ℱ μ
          (N i)
          (N j)
          (fun _ _ ↦ (0 : ℝ))) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ ∑ i in s, N i t ω)
      (fun t ω ↦ ∑ i in s, A i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine
        { zero := by
            funext ω
            simp
          adapted := by
            intro t
            simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
          continuous := by
            intro ω
            simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
          monotone := by
            intro ω s t hst
            simp
          local_martingale_sq_sub := by
            refine
              { local_martingale := ?_
                continuous := ?_ }
            · simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale
            · intro ω
              simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ)) }
  | @insert i s hi hs =>
      have hsNA :
          ∀ j ∈ s, IsContinuousSquareVariationProcess ℱ μ (N j) (A j) := by
        intro j hj
        exact hNA j (by simp [hj])
      have hsZero :
          ∀ ⦃j k : Fin n⦄, j ∈ s → k ∈ s → j ≠ k →
            IsContinuousQuadraticCovariationProcess ℱ μ
              (N j)
              (N k)
              (fun _ _ ↦ (0 : ℝ)) := by
        intro j k hj hk hjk
        exact hZero (by simp [hj]) (by simp [hk]) hjk
      have hRest :
          IsContinuousSquareVariationProcess ℱ μ
            (fun t ω ↦ ∑ j in s, N j t ω)
            (fun t ω ↦ ∑ j in s, A j t ω) :=
        hs hsNA hsZero
      have hZeroSum :
          IsContinuousQuadraticCovariationProcess ℱ μ
            (N i)
            (fun t ω ↦ ∑ j in s, N j t ω)
            (fun _ _ ↦ (0 : ℝ)) := by
        -- Proof comment: the mixed bracket against the tail sum is the sum of the pairwise zero
        -- mixed brackets against each tail coordinate.
        simpa using
          quadraticCovariation_finsetSum_right
            (μ := μ)
            (ℱ := ℱ)
            (s := s)
            (M := N i)
            (N := N)
            (A := fun _ ↦ fun _ _ ↦ (0 : ℝ))
            (fun j hj ↦
              hZero
                (by simp)
                (by simp [hj])
                (by
                  intro hij
                  exact hi (hij ▸ hj)))
      -- Proof comment: combine the head square-variation witness with the tail witness using the
      -- vanishing mixed covariation of the head against the whole tail sum.
      simpa [Finset.sum_insert, hi] using
        addSquareVariation_of_zeroQuadraticCovariation
          (μ := μ)
          (ℱ := ℱ)
          (M := N i)
          (N := fun t ω ↦ ∑ j in s, N j t ω)
          (A := A i)
          (B := fun t ω ↦ ∑ j in s, A j t ω)
          (hNA i (by simp))
          hRest
          hZeroSum

/-- Helper for Example 26.16: deterministic stopping commutes with the finite coordinate sum
defining the exact driver witness. -/
private theorem stoppedFinsetSum_eq_finsetSum_stopped
    {X : Fin n → ScalarProcess} (T : NNReal) :
    stoppedProcess (fun t ω ↦ ∑ i : Fin n, X i t ω) (fun _ ↦ (T : ENNReal)) =
      fun t ω ↦ ∑ i : Fin n, stoppedProcess (X i) (fun _ ↦ (T : ENNReal)) t ω := by
  funext t ω
  -- Proof comment: both sides evaluate every coordinate at the same clipped time `min t T`.
  simp [stoppedProcessConstTime_eq_min]

/-- Helper for Example 26.16: the summed explicit stopped coordinate clocks collapse to
`min t T` because the exact unit direction has squared norm `1`. -/
private theorem sumStoppedCoordinateClocks_eq_min
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n)
    (t T : NNReal) (ω : Ω) :
    ∑ i : Fin n,
        ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
          (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2 =
      (min t T : ℝ) := by
  have hle : (0 : ℝ) ≤ (min t T : ℝ) := by
    exact_mod_cast (min_nonneg t.2 T.2)
  calc
    ∑ i : Fin n,
        ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
          (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2 =
      ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
        ∑ i : Fin n, (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2 := by
          rw [Finset.integral_sum]
    _ = ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ), (1 : ℝ) := by
          congr with s
          simpa using squaredBesselUnitDirection_sum_sq y B hn s.toNNReal ω
    _ = (min t T : ℝ) := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hle]
          simp

/-- Helper for Example 26.16: once each stopped coordinate integral has its explicit stopped
clock as a genuine square-variation witness, the stopped exact driver sum has clock `min t T`. -/
private theorem stoppedWsumHasMinClock_of_coordinateSquareVariation
    {ℱ : TimeFiltration} {coordinateIntegral : Fin n → ScalarProcess}
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n) (T : NNReal)
    (hStoppedCoordinate :
      ∀ i : Fin n,
        IsContinuousSquareVariationProcess ℱ μ
          (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
          (fun t ω ↦
            ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
              (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2))
    (hStoppedCoordinatePairZero :
      ∀ ⦃i j : Fin n⦄, i ≠ j →
        IsContinuousQuadraticCovariationProcess ℱ μ
          (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
          (stoppedProcess (coordinateIntegral j) (fun _ ↦ (T : ENNReal)))
          (fun _ _ ↦ (0 : ℝ))) :
    IsContinuousSquareVariationProcess ℱ μ
      (stoppedProcess (fun t ω ↦ ∑ i : Fin n, coordinateIntegral i t ω) (fun _ ↦ (T : ENNReal)))
      (fun t _ ↦ (min t T : ℝ)) := by
  have hSum :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦
          ∑ i : Fin n, stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)) t ω)
        (fun t ω ↦
          ∑ i : Fin n,
            ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
              (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
    exact
      finsetSumSquareVariation_of_pairwiseZeroQuadraticCovariation
        (μ := μ)
        (ℱ := ℱ)
        (s := Finset.univ)
        (N := fun i ↦ stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
        (A := fun i t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
            (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2)
        (fun i _ ↦ hStoppedCoordinate i)
        (fun i j _ _ hij ↦ hStoppedCoordinatePairZero hij)
  -- Proof comment: rewrite the stopped exact driver as the visible finite sum of the stopped
  -- coordinates, then collapse the summed clock by `∑ i U_i^2 = 1`.
  simpa [stoppedFinsetSum_eq_finsetSum_stopped, sumStoppedCoordinateClocks_eq_min] using hSum

/-- Helper for Example 26.16: the centered radial square is exactly the finite sum of the
coordinatewise centered squares. -/
private theorem centeredSquaredNorm_eq_coordinateCenteredSquareSum
    (y : Fin n → ℝ) (B : VectorProcess)
    (t : NNReal) (ω : Ω) :
    squaredNormProcess (shiftedBrownianProcess y B) t ω -
        ((∑ j : Fin n, (y j) ^ 2) + n * t) =
      ∑ i : Fin n,
        ((shiftedBrownianProcess y B t ω i) ^ 2 - ((y i) ^ 2 + t)) := by
  -- Proof comment: unfold the radial square into the finite sum of coordinate squares and then
  -- regroup the deterministic drift contribution coordinatewise.
  calc
    squaredNormProcess (shiftedBrownianProcess y B) t ω -
        ((∑ j : Fin n, (y j) ^ 2) + n * t) =
      (∑ i : Fin n, (shiftedBrownianProcess y B t ω i) ^ 2) -
        ((∑ j : Fin n, (y j) ^ 2) + ∑ _ : Fin n, (t : ℝ)) := by
          simp [squaredNormProcess_apply, euclideanSquaredNorm_def]
    _ =
      ∑ i : Fin n,
        ((shiftedBrownianProcess y B t ω i) ^ 2 - ((y i) ^ 2 + t)) := by
          rw [sub_eq_add_neg, Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

/-- Helper for Example 26.16: multiplying the public squared-Bessel coefficient
`2 * sqrt (‖y + B_t‖²)` by the exact unit direction recovers twice the shifted coordinate. -/
private theorem doubledSqrtCoeff_mul_unitDirection_eq_twice_shiftedCoordinate
    (y : Fin n → ℝ) (B : VectorProcess) (hn : 0 < n)
    (i : Fin n) (t : NNReal) (ω : Ω) :
    squaredBesselDiffusionCoeff
        t
        (fun _ ↦ squaredNormProcess (shiftedBrownianProcess y B) t ω)
        0
        0 *
      squaredBesselUnitDirection y B hn i t ω =
        2 * shiftedBrownianProcess y B t ω i := by
  -- Proof comment: rewrite the public coefficient to `2 * sqrt X` and then use the exact
  -- coefficient bridge `sqrt X * U_i = y_i + B_t^i`.
  rw [squaredBesselDiffusionCoeff_apply]
  calc
    2 * Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) *
        squaredBesselUnitDirection y B hn i t ω =
      2 *
        (Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) *
          squaredBesselUnitDirection y B hn i t ω) := by
            ring
    _ = 2 * shiftedBrownianProcess y B t ω i := by
          rw [sqrt_mul_squaredBesselUnitDirection y B hn i t ω]

/-- Helper for Example 26.16: once each coordinate half-compensated square agrees almost surely at
all times with its canonical coordinate Itô integral, the centered radial square agrees almost
surely at all times with twice the sum of those coordinate integrals. -/
private theorem centeredSquaredNorm_ae_eq_twoMulCoordinateItoSum_of_coordinateHalfIdentities
    {Ii : Fin n → ScalarProcess}
    (y : Fin n → ℝ) (B : VectorProcess)
    (hCoord :
      ∀ i : Fin n, ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ((shiftedBrownianProcess y B t ω i) ^ 2 - ((y i) ^ 2 + t)) / 2 = Ii i t ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      squaredNormProcess (shiftedBrownianProcess y B) t ω -
          ((∑ j : Fin n, (y j) ^ 2) + n * t) =
        2 * ∑ i : Fin n, Ii i t ω := by
  classical
  have hCoordAll :
      ∀ᵐ ω ∂μ, ∀ i : Fin n, ∀ t : NNReal,
        ((shiftedBrownianProcess y B t ω i) ^ 2 - ((y i) ^ 2 + t)) / 2 = Ii i t ω := by
    rw [ae_all_iff]
    intro i
    exact hCoord i
  filter_upwards [hCoordAll] with ω hω t
  -- Proof comment: rewrite the centered radial square as the sum of the coordinatewise centered
  -- squares, then replace each coordinate term by twice its canonical Itô realization.
  calc
    squaredNormProcess (shiftedBrownianProcess y B) t ω -
        ((∑ j : Fin n, (y j) ^ 2) + n * t) =
      ∑ i : Fin n,
        ((shiftedBrownianProcess y B t ω i) ^ 2 - ((y i) ^ 2 + t)) := by
          rw [centeredSquaredNorm_eq_coordinateCenteredSquareSum]
    _ = ∑ i : Fin n, (2 * Ii i t ω) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hcoord_i := hω i t
          linarith
    _ = 2 * ∑ i : Fin n, Ii i t ω := by
          rw [Finset.mul_sum]

/-- Helper for Example 26.16: if two processes agree almost surely at all times with the same
comparison process, then they are modifications of one another. -/
private theorem areModifications_of_commonAeAllTimes
    {X Y J : ScalarProcess}
    (hX : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = J t ω)
    (hY : ∀ᵐ ω ∂μ, ∀ t : NNReal, Y t ω = J t ω) :
    AreModifications μ X Y := by
  intro t
  filter_upwards [hX, hY] with ω hωX hωY
  -- Proof comment: the shared all-times almost-sure identity supplies the fixed-time equality
  -- required by `AreModifications`.
  exact (hωX t).trans (hωY t).symm

/-- Helper for Example 26.16: deterministic-horizon `EqUpTo` comparisons for every horizon
upgrade to a modification relation. -/
private theorem areModifications_of_forallEqUpTo
    {X Y : ScalarProcess}
    (hXY : ∀ T : NNReal, EqUpTo μ T X Y) :
    AreModifications μ X Y := by
  intro t
  rcases eqUpTo_forall_eq (μ := μ) (T := t) (hXY t) with
    ⟨N, hN_meas, hN_null, hN_eq⟩
  refine ae_iff.2 ⟨N, hN_meas, hN_null, ?_⟩
  intro ω hω
  -- Proof comment: at the fixed deterministic time `t`, the horizon-`t` comparison already
  -- yields equality because `t ≤ t`.
  exact hN_eq le_rfl hω

-- Proof sketch: apply Itô's formula to the squared norm of the shifted Brownian motion
-- `t ↦ y + B_t`, identify the radial martingale term, compute its bracket as `t`, and then
-- package the resulting one-dimensional integral equation in the chapter's weak-solution
-- interface.
/-- Example 26.16: if `n > 0`, `B` is a standard `n`-dimensional Brownian driver whose coordinate
increments are independent of the past of `ℱ`, and `X_t = ‖y + B_t‖²`, then there exists a scalar
continuous local martingale `W` with bracket `⟨W⟩_t = t` realizing `X` as a one-dimensional weak
solution of the squared-radial equation with initial value `‖y‖²`, diffusion coefficient
`2 * sqrt (x)`, and drift `n`. -/
theorem shiftedBrownian_squaredNorm_hasWeakSquaredBesselRealization
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hn : 0 < n) (hB : IsBrownianMotionWithFiltration ℱ μ B)
    (hBindep :
      ∀ i : Fin n, ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ B t ω i - B s ω i) (borel ℝ))
          (ℱ s)
          μ) :
    ∃ W : ScalarProcess,
      IsWeakSquaredBesselRealization ℱ μ y B hn W := by
  rcases exists_sourceSquaredBesselDriverFormula
      (μ := μ) (ℱ := ℱ) (B := B) y hn hB with
    ⟨_, hSource⟩
  rcases hSource with
    ⟨coordinateLocalMartingale, coordinateBracket, coordinateIntegral, hCoordIto, _⟩
  let Wsum : ScalarProcess := fun t ω ↦ ∑ i : Fin n, coordinateIntegral i t ω
  have hUnitSq :
      ∀ t : NNReal, ∀ ω : Ω,
        ∑ i : Fin n, (squaredBesselUnitDirection y B hn i t ω) ^ 2 = 1 := by
    intro t ω
    exact squaredBesselUnitDirection_sum_sq y B hn t ω
  have hUnitBound :
      ∀ i : Fin n, ∀ t : NNReal, ∀ ω : Ω,
        (squaredBesselUnitDirection y B hn i t ω) ^ 2 ≤ 1 := by
    intro i t ω
    exact squaredBesselUnitDirection_sq_le_one y B hn i t ω
  have hCoeffBridge :
      ∀ i : Fin n, ∀ t : NNReal, ∀ ω : Ω,
        Real.sqrt (squaredNormProcess (shiftedBrownianProcess y B) t ω) *
            squaredBesselUnitDirection y B hn i t ω =
          shiftedBrownianProcess y B t ω i := by
    intro i t ω
    exact sqrt_mul_squaredBesselUnitDirection y B hn i t ω
  have hUnitProg :
      ∀ i : Fin n, ProgMeasurable ℱ (squaredBesselUnitDirection y B hn i) := by
    intro i
    exact squaredBesselUnitDirection_progMeasurable (μ := μ) y hn hB i
  have hUnitSqIntegrable :
      ∀ i : Fin n, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦ (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2)
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro i T
    exact squaredBesselUnitDirection_squareIntegrableUpTo (μ := μ) y hn hB i T
  -- Route correction: the live setup surface is now the exact canonical coefficient
  -- `squaredBesselUnitDirection`; its progressive measurability and deterministic-horizon square
  -- energy are proved directly above, so the remaining blocker is the finite-sum/globalization
  -- step for `Wsum`, not coefficient regularity.
  -- Proof comment: the exact owner sum `Wsum` already satisfies the source driver formula. The
  -- only remaining work is the structural tail: first upgrade `Wsum` to an
  -- identity-bracket scalar martingale using pairwise covariation assembly, then compare the
  -- centered squared norm with the scalar canonical Itô integral through `hCoeffBridge`.
  have hCoordinateSingleUpTo :
      ∀ i : Fin n, ∀ T : NNReal,
        IsContinuousLocalMartingaleUpTo ℱ μ T (coordinateIntegral i) ∧
          IsContinuousSquareVariationProcessUpTo ℱ μ T
            (coordinateIntegral i)
            (fun t ω ↦
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
    intro i T
    -- Proof comment: `coordinateIntegral i` is definitionally the canonical coordinate Itô
    -- integral, and the explicit density-one Brownian coordinate bracket makes the clock a plain
    -- time integral of `(U_i)^2`.
    simpa [coordinateIntegral] using
      coordinateIntegral_singleClausesUpTo
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        T
  have hCoordinatePairZeroUpTo :
      ∀ ⦃i j : Fin n⦄, i ≠ j → ∀ T : NNReal,
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (coordinateIntegral i)
          (coordinateIntegral j)
          0 := by
    intro i j hij T
    -- Proof comment: the canonical coordinate integrals inherit zero covariation from the
    -- independence of the corresponding Brownian coordinates.
    simpa [coordinateIntegral] using
      coordinateIntegrals_zeroQuadraticCovariationUpTo
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        hij
        T
  have hWsumUpTo :
      ∀ T : NNReal,
        IsContinuousLocalMartingaleUpTo ℱ μ T Wsum := by
    intro T
    -- Proof comment: once each coordinate owner is a local martingale up to `T`, the exact
    -- driver sum `Wsum` inherits the same deterministic-horizon package by finite summation.
    simpa [Wsum] using
      finsetSum_isContinuousLocalMartingaleUpTo
        (μ := μ)
        (ℱ := ℱ)
        (s := Finset.univ)
        (N := coordinateIntegral)
        (T := T)
        (fun i _ ↦ (hCoordinateSingleUpTo i T).1)
  have hStoppedCoordinateClockUpTo :
      ∀ i : Fin n, ∀ T U : NNReal,
        IsContinuousSquareVariationProcessUpTo ℱ μ U
          (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
          (fun t ω ↦
            ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
              (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
    intro i T U
    -- Proof comment: route the stopped coordinate through the owner-aligned deterministic-cutoff
    -- canonical surface; this is the proof-side route correction from the old direct
    -- `hStoppedCoordinateClockUpTo` globalization attempt.
    simpa [coordinateIntegral] using
      stoppedCanonicalCoordinateHasExplicitSquareVariationUpTo
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        T
        U
  have hCoordinateMartingale :
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (coordinateIntegral i) := by
    intro i
    -- Proof comment: each exact coordinate integral already has deterministic-horizon local
    -- martingale owners, so the constant-stop globalization theorem upgrades it to a genuine
    -- continuous local martingale.
    refine
      isContinuousLocalMartingale_of_constStoppedMartingale
        (ℱ := ℱ)
        (μ := μ)
        (Y := coordinateIntegral i)
        (hY_adapted := (hCoordinateSingleUpTo i 0).1.adapted)
        (hY_cont := (hCoordinateSingleUpTo i 0).1.continuous) ?_
    intro T
    simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (τ := fun _ ↦ (T : ENNReal))
        (M := coordinateIntegral i)
        ((hCoordinateSingleUpTo i T).1)
        T
  have hStoppedCoordinatePairZero :
      ∀ ⦃i j : Fin n⦄, i ≠ j → ∀ T : NNReal,
        IsContinuousQuadraticCovariationProcess ℱ μ
          (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
          (stoppedProcess (coordinateIntegral j) (fun _ ↦ (T : ENNReal)))
          (fun _ _ ↦ (0 : ℝ)) := by
    intro i j hij T
    -- Proof comment: once the exact coordinate owners are genuine continuous local martingales,
    -- the existing `...UpTo` zero-covariation witness upgrades to a genuine zero witness after
    -- stopping both coordinates at the same deterministic horizon.
    exact
      stoppedZeroQuadraticCovariation_of_upTo
        (μ := μ)
        (ℱ := ℱ)
        (M := coordinateIntegral i)
        (N := coordinateIntegral j)
        (hCoordinateMartingale i)
        (hCoordinateMartingale j)
        (hCoordinatePairZeroUpTo hij T)
  have hStoppedWsumHasMinClock :
      ∀ T : NNReal,
        (∀ i : Fin n,
          IsContinuousSquareVariationProcess ℱ μ
            (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
            (fun t ω ↦
              ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
                (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2)) →
          IsContinuousSquareVariationProcess ℱ μ
            (stoppedProcess Wsum (fun _ ↦ (T : ENNReal)))
            (fun t _ ↦ (min t T : ℝ)) := by
    intro T hStoppedCoordinateExact
    -- Proof comment: once the stopped coordinate clocks are genuine, the stopped exact driver
    -- bracket is the finite-sum assembly already isolated in
    -- `stoppedWsumHasMinClock_of_coordinateSquareVariation`.
    simpa [Wsum] using
      stoppedWsumHasMinClock_of_coordinateSquareVariation
        (μ := μ)
        (ℱ := ℱ)
        (coordinateIntegral := coordinateIntegral)
        y
        B
        hn
        T
        hStoppedCoordinateExact
        (fun hij ↦ hStoppedCoordinatePairZero hij T)
  have hSourceWsum : HasSourceSquaredBesselDriverFormula ℱ μ y B hn Wsum := by
    refine ⟨coordinateLocalMartingale, coordinateBracket, coordinateIntegral, hCoordIto, ?_⟩
    intro t
    filter_upwards with ω
    simp [Wsum]
  have hWsum : IsContinuousLocalMartingale ℱ μ Wsum := by
    refine
      isContinuousLocalMartingale_of_constStoppedMartingale
        (ℱ := ℱ)
        (μ := μ)
        (hY_adapted := (hWsumUpTo 0).adapted)
        (hY_cont := (hWsumUpTo 0).continuous) ?_
    intro T
    -- Proof comment: the deterministic-horizon owner `hWsumUpTo T` already yields the true
    -- martingale statement for the stop at the same horizon.
    simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (τ := fun _ ↦ (T : ENNReal))
        (M := Wsum)
        (hWsumUpTo T)
        T
  have hStoppedCoordinateExact :
      ∀ i : Fin n, ∀ T : NNReal,
        IsContinuousSquareVariationProcess ℱ μ
          (stoppedProcess (coordinateIntegral i) (fun _ ↦ (T : ENNReal)))
          (fun t ω ↦
            ∫ s in Set.Icc (0 : ℝ) (min t T : ℝ),
              (squaredBesselUnitDirection y B hn i s.toNNReal ω) ^ 2) := by
    intro i T
    -- Proof comment: this is the remaining cutoff-to-visible transport lemma isolated above.
    simpa [coordinateIntegral] using
      stoppedCoordinateHasExplicitSquareVariation
        (μ := μ)
        (ℱ := ℱ)
        (B := B)
        y
        hn
        hB
        coordinateLocalMartingale
        i
        T
  have hStoppedWsumClock :
      ∀ T : NNReal,
        IsContinuousSquareVariationProcess ℱ μ
          (stoppedProcess Wsum (fun _ ↦ (T : ENNReal)))
          (fun t _ ↦ (min t T : ℝ)) := by
    intro T
    -- Proof comment: once each stopped coordinate has the genuine explicit clock, the exact
    -- driver sum inherits the stopped clock `min t T`.
    exact hStoppedWsumHasMinClock T (fun i ↦ hStoppedCoordinateExact i T)
  let Y : ScalarProcess := fun t ω ↦ Wsum t ω ^ 2 - (t : ℝ)
  have hYAdapted : Adapted ℱ Y := by
    intro t
    -- Proof comment: the compensated square process is adapted because `Wsum` is adapted and the
    -- deterministic time path is measurable.
    exact ((hWsum.adapted t).pow_const 2).sub
      (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (t : ℝ))
  have hYCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω := by
    intro ω
    -- Proof comment: continuity is preserved under squaring and subtraction of the deterministic
    -- clock `t ↦ t`.
    exact ((hWsum.continuous ω).pow 2).sub
      (show Continuous fun t : NNReal ↦ (t : ℝ) from continuous_subtype_val)
  have hYUpTo :
      ∀ T : NNReal, IsContinuousLocalMartingaleUpTo ℱ μ T Y := by
    intro T
    let Z : ScalarProcess := fun t ω ↦
      stoppedProcess Wsum (fun _ ↦ (T : ENNReal)) t ω ^ 2 - (min t T : ℝ)
    have hZ : IsContinuousLocalMartingale ℱ μ Z := by
      -- Proof comment: the stopped bracket witness already packages the compensated stopped
      -- square as a continuous local martingale.
      simpa [Z] using (hStoppedWsumClock T).local_martingale_sq_sub
    have hYZ :
        EqUpTo μ T Y Z := by
      refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
      intro t ht ω hω
      -- Proof comment: on `[0, T]`, the deterministic stop does not change `Wsum`, so the
      -- compensated square agrees with the stopped compensated square.
      simp [Y, Z, stoppedProcessConstTime_eq_min, min_eq_left ht]
    exact
      isContinuousLocalMartingaleUpTo_of_eqUpTo
        (μ := μ)
        (ℱ := ℱ)
        hYZ
        (isContinuousLocalMartingaleUpTo_of_isContinuousLocalMartingale
          (μ := μ)
          (ℱ := ℱ)
          (T := T)
          hZ)
  have hYMart : IsContinuousLocalMartingale ℱ μ Y := by
    -- Proof comment: every deterministic stop of `Y` is a genuine martingale, so the constant-
    -- stop globalization theorem upgrades `Y` itself to a continuous local martingale.
    refine
      isContinuousLocalMartingale_of_constStoppedMartingale
        (ℱ := ℱ)
        (μ := μ)
        (Y := Y)
        hYAdapted
        hYCont
        ?_
    intro T
    simpa [Y, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (τ := fun _ ↦ (T : ENNReal))
        (M := Y)
        (hYUpTo T)
        T
  have hWsumSq :
      IsContinuousSquareVariationProcess ℱ μ Wsum (fun t _ ↦ (t : ℝ)) := by
    refine
      { zero := by
          funext ω
          simp
        adapted := by
          intro t
          simpa using
            (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (t : ℝ))
        continuous := by
          intro ω
          simpa using
            (show Continuous fun t : NNReal ↦ (t : ℝ) from continuous_subtype_val)
        monotone := by
          intro ω s t hst
          exact_mod_cast hst
        local_martingale_sq_sub := by
          -- Proof comment: the compensated square process `Y` is exactly the globalized local
          -- martingale constructed just above.
          simpa [Y] using hYMart }
  have hbrWsum :
      HasAbsolutelyContinuousSquareVariation Wsum hWsum := by
    refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hWsumSq, ?_, ?_⟩
    · -- Proof comment: the global bracket density of `Wsum` is the deterministic constant `1`.
      simpa using
        (stronglyMeasurable_const.progMeasurable :
          ProgMeasurable ℱ (fun _ _ : Ω ↦ (1 : ℝ)))
    · -- Proof comment: integrating the density `1` over `[0, t]` gives the identity clock.
      intro t ω
      simp
  refine ⟨Wsum, ?_⟩
  refine ⟨hWsum, ?_⟩
  refine ⟨hWsumSq, ?_⟩
  refine ⟨hbrWsum, ?_⟩
  refine ⟨hSourceWsum, ?_⟩
  let H : ScalarProcess := fun t ω ↦
    squaredBesselDiffusionCoeff
      t
      (fun _ ↦ squaredNormProcess (shiftedBrownianProcess y B) t ω)
      0
      0
  let N : ScalarProcess := continuousLocalMartingaleItoIntegralProcess hWsum H
  refine ⟨N, ?_, ?_⟩
  · -- Proof comment: the public weak-solution interface records the canonical scalar Itô
    -- realization driven by `Wsum`.
    exact
      canonicalItoIntegralSpec
        (μ := μ)
        (ℱ := ℱ)
        (M := Wsum)
        (H := H)
        hWsum
        hbrWsum
  · -- TODO: the remaining state-side bridge is to compare the centered radial square with `N`
    -- by comparing both visible processes with the common coordinate-sum process `J`.
    let Ii : Fin n → ScalarProcess := fun i ↦
      continuousLocalMartingaleItoIntegralProcess
        (coordinateLocalMartingale i)
        (fun s ξ ↦ shiftedBrownianProcess y B s ξ i)
    let J : ScalarProcess := fun t ω ↦ 2 * ∑ i : Fin n, Ii i t ω
    have hStateMods :
        AreModifications μ
          (fun t ω ↦
            squaredNormProcess (shiftedBrownianProcess y B) t ω -
              ((∑ j : Fin n, (y j) ^ 2) + n * t))
          J := by
      -- TODO: route-correct the state comparison through one global Brownian Itô identity for
      -- `F(z, s) = ‖y + z‖²`, then transport the corollary's coordinate stochastic terms to the
      -- local canonical surface `Ii` and conclude by `areModifications_of_commonAeAllTimes`.
      sorry
    have hDriverMods :
        AreModifications μ N J := by
      -- TODO: prove the driver comparison horizonwise as `∀ T, EqUpTo μ T N J` on the
      -- deterministic-cutoff canonical surface, then globalize with
      -- `areModifications_of_forallEqUpTo`. The only coefficient rewrite should be
      -- `doubledSqrtCoeff_mul_unitDirection_eq_twice_shiftedCoordinate`.
      sorry
    -- Proof comment: once both visible processes are modifications of the same comparison
    -- process `J`, the target modification relation follows by transitivity at each fixed time.
    intro t
    exact (hStateMods t).trans (hDriverMods t).symm

end ProbabilityTheory
