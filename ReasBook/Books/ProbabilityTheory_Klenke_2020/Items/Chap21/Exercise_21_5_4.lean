/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Example_14_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- The index set `[0,1]^d` for the `d`-parameter Brownian sheet. -/
abbrev BrownianSheetIndex (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

/-- The covariance kernel `∏ᵢ min (sᵢ, tᵢ)` of the Brownian sheet on `[0,1]^d`. -/
def brownianSheetCovariance {d : ℕ} (s t : BrownianSheetIndex d) : ℝ :=
  ∏ i : Fin d, min (s i : ℝ) (t i : ℝ)

-- Proof sketch: unfold `brownianSheetCovariance`.
/-- Expanding `brownianSheetCovariance` gives the product of the coordinatewise minima. -/
theorem brownianSheetCovariance_def {d : ℕ} (s t : BrownianSheetIndex d) :
    brownianSheetCovariance s t = ∏ i : Fin d, min (s i : ℝ) (t i : ℝ) := by
  -- Proof comment: this lemma is just the definitional expansion of the covariance kernel.
  rfl

/-- The canonical coordinate process on the Brownian-sheet path space `(BrownianSheetIndex d → ℝ)`.
-/
def brownianSheetCoordinateProcess (d : ℕ) :
    BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ :=
  fun t ω ↦ ω t

-- Proof sketch: unfold `brownianSheetCoordinateProcess`.
/-- Evaluating the Brownian-sheet coordinate process at `t` returns the coordinate `ω t`. -/
theorem brownianSheetCoordinateProcess_apply {d : ℕ}
    (t : BrownianSheetIndex d) (ω : BrownianSheetIndex d → ℝ) :
    brownianSheetCoordinateProcess d t ω = ω t := by
  -- Proof comment: the coordinate process is defined by evaluation on the path `ω`.
  rfl

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 21.5.4: each fixed Brownian-sheet coordinate map is measurable on path
space. -/
theorem measurable_brownianSheetCoordinateProcess {d : ℕ} (t : BrownianSheetIndex d) :
    Measurable (brownianSheetCoordinateProcess d t) := by
  -- Proof comment: on the product measurable space, evaluation at a fixed coordinate is
  -- measurable.
  simpa [brownianSheetCoordinateProcess] using measurable_pi_apply t

/-- Helper for Exercise 21.5.4: on the diagonal, the covariance kernel collapses to the product of
the coordinates. -/
theorem brownianSheetCovariance_self {d : ℕ} (t : BrownianSheetIndex d) :
    brownianSheetCovariance t t = ∏ i : Fin d, (t i : ℝ) := by
  -- Proof comment: each coordinatewise minimum becomes the coordinate itself on the diagonal.
  simp [brownianSheetCovariance]

/-- Helper for Exercise 21.5.4: a centered Gaussian random variable has the standard even-moment
formula with the variance raised to the matching power. -/
theorem centeredGaussianEvenMoment_eq_factorialRatio_mul_variance_pow
    {μ : Measure Ω} {Y : Ω → ℝ} (hY : HasGaussianLaw Y μ)
    (hY_mean : ∫ ω, Y ω ∂μ = 0) (k : ℕ) :
    ∫ ω, Y ω ^ (2 * k) ∂μ =
      ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
        Var[Y; μ] ^ k := by
  letI : IsProbabilityMeasure μ := hY.isProbabilityMeasure
  let v : NNReal := Var[Y; μ].toNNReal
  have hLaw :
      HasLaw Y (gaussianReal (∫ ω, Y ω ∂μ) v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    calc
      μ.map Y = gaussianReal ((μ.map Y)[id]) Var[id; μ.map Y].toNNReal := by
        exact ProbabilityTheory.IsGaussian.eq_gaussianReal (μ := μ.map Y) hY.isGaussian_map
      _ = gaussianReal (∫ ω, Y ω ∂μ) v := by
        -- Proof comment: rewrite the Gaussian owner parameters in terms of the original random
        -- variable.
        congr 1
        · simpa using
            (integral_map hY.aemeasurable measurable_id'.aestronglyMeasurable :
              ∫ x : ℝ, id x ∂Measure.map Y μ = ∫ ω, id (Y ω) ∂μ)
        · simpa [v] using
            congrArg Real.toNNReal
              (variance_map measurable_id'.aemeasurable hY.aemeasurable :
                Var[id; μ.map Y] = Var[id ∘ Y; μ])
  have hLaw0 :
      HasLaw Y (gaussianReal 0 v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    -- Proof comment: the centered hypothesis identifies the Gaussian mean parameter with `0`.
    simpa [v, hY_mean] using hLaw.map_eq
  let c : ℝ := Real.sqrt (v : ℝ)
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdMoment :
      ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 =
        (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := by
    -- Proof comment: this is the standard Gaussian even-moment formula from the earlier Chapter
    -- 15 exercise.
    simpa using gaussianReal_even_moments_eq_factorial_ratio
      (P' := gaussianReal 0 1) (Y := id) hStdId k
  have hScaleLaw :
      HasLaw (fun x : ℝ ↦ c * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    -- Proof comment: `N(0, v)` is the image of the standard Gaussian under multiplication by
    -- `sqrt v`.
    simpa [c, sq_abs, Real.sq_sqrt] using
      (gaussianReal_const_mul
        (P := gaussianReal 0 1) (X := id) (μ := (0 : ℝ)) (v := (1 : NNReal)) hStdId c)
  have hMomentBase :
      ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v =
        ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
          ((v : ℝ) ^ k) := by
    calc
      ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v
          = ∫ x : ℝ, (c * x) ^ (2 * k) ∂gaussianReal 0 1 := by
              symm
              simpa [Function.comp] using
                (hScaleLaw.integral_comp
                  (f := fun x : ℝ ↦ x ^ (2 * k))
                  ((continuous_pow _).aestronglyMeasurable))
      _ = ∫ x : ℝ, c ^ (2 * k) * x ^ (2 * k) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [mul_pow]
      _ = c ^ (2 * k) * ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
            rw [integral_const_mul]
      _ = c ^ (2 * k) *
            ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) := by
            rw [hStdMoment]
      _ = ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
            ((v : ℝ) ^ k) := by
            have hv_nonneg : 0 ≤ (v : ℝ) := by
              exact_mod_cast v.2
            have hsq : c ^ (2 : ℕ) = (v : ℝ) := by
              simp [c, Real.sq_sqrt, hv_nonneg]
            have hpow : c ^ (2 * k) = (v : ℝ) ^ k := by
              rw [pow_mul, hsq]
            rw [hpow, mul_comm]
  calc
    ∫ ω, Y ω ^ (2 * k) ∂μ = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v := by
      -- Proof comment: move the even moment to the centered Gaussian owner law.
      exact
        hLaw0.integral_comp
          (f := fun x : ℝ ↦ x ^ (2 * k))
          ((continuous_pow _).aestronglyMeasurable)
    _ =
        ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
          ((v : ℝ) ^ k) := hMomentBase
    _ =
        ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
          Var[Y; μ] ^ k := by
          have hv : (v : ℝ) = Var[Y; μ] := by
            simp [v, variance_nonneg Y μ]
          rw [hv]

/-- Brownian-sheet structure for Exercise 21.5.4: a Brownian sheet on `[0,1]^d` is a Gaussian
process with covariance kernel `∏ᵢ min (sᵢ, tᵢ)` that admits an almost surely continuous
modification. -/
class IsBrownianSheet (d : ℕ) (μ : Measure Ω) (W : BrownianSheetIndex d → Ω → ℝ) : Prop
    extends IsGaussianProcess W μ where
  /-- The covariance kernel of a Brownian sheet is `∏ᵢ min (sᵢ, tᵢ)`. -/
  covariance_eq :
    ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t
  /-- A Brownian sheet admits a modification with almost surely continuous sample paths. -/
  exists_continuous_modification :
    ∃ W' : BrownianSheetIndex d → Ω → ℝ,
      AreModifications μ W W' ∧ HasAlmostSurelyContinuousPaths μ W'

/-- A Gaussian process with Brownian-sheet covariance and almost surely continuous paths is a
Brownian sheet. -/
instance {d : ℕ} {μ : Measure Ω} {W : BrownianSheetIndex d → Ω → ℝ}
    (hgauss : IsGaussianProcess W μ)
    (hcov : ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t)
    (hcont : HasAlmostSurelyContinuousPaths μ W) :
    IsBrownianSheet d μ W := by
  -- Proof comment: if `W` already has the Gaussian law, covariance kernel, and continuous paths,
  -- it is itself the required continuous modification.
  refine
    { toIsGaussianProcess := hgauss
      covariance_eq := hcov
      exists_continuous_modification := ?_ }
  exact ⟨W, fun _ ↦ Filter.EventuallyEq.rfl, hcont⟩

/-- Helper for Exercise 21.5.4: under the canonical Gaussian increment path law, the time-zero
coordinate is almost surely equal to `0`. -/
private lemma gaussianIncrementCoordinate_zero_ae :
    Function.eval 0 =ᵐ[gaussianIncrementPathMeasure] fun _ : NNReal → ℝ ↦ 0 := by
  -- Proof comment: the start law is `δ₀`, so the time-zero coordinate hits `{0}` with
  -- probability one.
  refine (ae_iff_prob_eq_one ((measurable_pi_apply 0).eq measurable_const)).2 ?_
  have hMap :
      gaussianIncrementPathMeasure.map (Function.eval 0) = Measure.dirac 0 :=
    gaussianIncrementPathMeasure_start_hasLaw.map_eq
  have hOne :
      gaussianIncrementPathMeasure ((Function.eval 0) ⁻¹' ({0} : Set ℝ)) = 1 := by
    calc
      gaussianIncrementPathMeasure ((Function.eval 0) ⁻¹' ({0} : Set ℝ))
          = gaussianIncrementPathMeasure.map (Function.eval 0) ({0} : Set ℝ) := by
              symm
              exact Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton 0)
      _ = 1 := by
            rw [hMap]
            simp
  simpa [Function.eval] using hOne

/-- Helper for Exercise 21.5.4: every deterministic coordinate of the canonical Gaussian
increment path law has the centered Gaussian law with variance equal to its time parameter. -/
private lemma gaussianIncrementCoordinate_eval_hasLaw (t : NNReal) :
    HasLaw (Function.eval t) (gaussianReal 0 t) gaussianIncrementPathMeasure := by
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the owner start law is exactly `δ₀ = N(0,0)`.
    subst ht
    simpa [gaussianReal_zero_var] using gaussianIncrementPathMeasure_start_hasLaw
  · have hInc :
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω 0) (gaussianReal 0 (t - 0))
          gaussianIncrementPathMeasure := by
      simpa using
        gaussianIncrementPathMeasure_increment_hasLaw
          (s := 0) (t := t) (show (0 : NNReal) ≤ t by simp)
    have hEval :
        HasLaw (Function.eval t) (gaussianReal 0 (t - 0)) gaussianIncrementPathMeasure :=
      hInc.congr <| by
        -- Proof comment: the time-zero coordinate vanishes almost surely, so the `0`-increment
        -- is just the time-`t` coordinate almost surely.
        filter_upwards [gaussianIncrementCoordinate_zero_ae] with ω hω
        simp [Function.eval, hω]
    simpa using hEval

/-- Helper for Exercise 21.5.4: every deterministic coordinate of the canonical Gaussian
increment path law is centered. -/
private lemma gaussianIncrementCoordinate_mean_zero (t : NNReal) :
    ∫ ω, Function.eval t ω ∂gaussianIncrementPathMeasure = 0 := by
  -- Proof comment: each fixed-time marginal is the centered Gaussian law `N(0,t)`.
  simpa using (gaussianIncrementCoordinate_eval_hasLaw t).integral_eq

/-- Helper for Exercise 21.5.4: the canonical Gaussian increment path law has Brownian covariance
kernel `cov(B_s, B_t) = s ∧ t`. -/
private lemma gaussianIncrementCoordinate_covariance_eq (s t : NNReal) :
    cov[Function.eval s, Function.eval t; gaussianIncrementPathMeasure] =
      ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure gaussianIncrementPathMeasure := inferInstance
  -- Proof comment: order the times, split the later coordinate into the earlier coordinate plus
  -- the future increment, and use independent increments to kill the mixed covariance term.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (Function.eval s) 2 gaussianIncrementPathMeasure :=
    (gaussianIncrementCoordinate_eval_hasLaw s).hasGaussianLaw.memLp_two
  have hIncLaw :
      HasLaw (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω)
        (gaussianReal 0 (t - s)) gaussianIncrementPathMeasure := by
    simpa [Function.eval] using
      gaussianIncrementPathMeasure_increment_hasLaw (s := s) (t := t) hst
  have hInc_mem :
      MemLp (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω) 2
        gaussianIncrementPathMeasure :=
    hIncLaw.hasGaussianLaw.memLp_two
  have hIndep :
      (Function.eval s) ⟂ᵢ[gaussianIncrementPathMeasure]
        (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω) :=
    gaussianIncrementPathMeasure_hasStationaryIndependentIncrements.1.indepFun_eval_sub
      (show (0 : NNReal) ≤ s by simp) hst gaussianIncrementCoordinate_zero_ae
  have hSplit :
      Function.eval t =
        fun ω : NNReal → ℝ ↦ Function.eval s ω + (Function.eval t ω - Function.eval s ω) := by
    funext ω
    ring
  have hVarS : Var[Function.eval s; gaussianIncrementPathMeasure] = (s : ℝ) := by
    simpa using (gaussianIncrementCoordinate_eval_hasLaw s).variance_eq
  rw [hSplit]
  change
    cov[Function.eval s,
      Function.eval s + (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω);
      gaussianIncrementPathMeasure] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem,
    hIndep.covariance_eq_zero hs_mem hInc_mem, covariance_self hs_mem.aemeasurable, hVarS]
  simp [inf_eq_left.mpr hst]

/-- Helper for Exercise 21.5.4: the anchored rectangle below `t` inside `[0,1]^d`. -/
private def brownianSheetRectangle {d : ℕ} (t : BrownianSheetIndex d) : Set (Fin d → ℝ) :=
  Set.Icc 0 fun i ↦ (t i : ℝ)

/-- Helper for Exercise 21.5.4: anchored rectangles are measurable. -/
private theorem measurableSet_brownianSheetRectangle {d : ℕ} (t : BrownianSheetIndex d) :
    MeasurableSet (brownianSheetRectangle t) := by
  -- Proof comment: the rectangle is the closed box `∏ i [0, tᵢ]`, hence measurable.
  simpa [brownianSheetRectangle] using
    (measurableSet_Icc :
      MeasurableSet (Set.Icc (0 : Fin d → ℝ) fun i ↦ (t i : ℝ)))

/-- Helper for Exercise 21.5.4: anchored rectangles have finite Lebesgue volume. -/
private theorem volume_brownianSheetRectangle_ne_top {d : ℕ} (t : BrownianSheetIndex d) :
    volume (brownianSheetRectangle t) ≠ ⊤ := by
  -- Proof comment: a finite product of finite interval lengths gives a finite box volume.
  rw [brownianSheetRectangle, Real.volume_Icc_pi]
  exact ne_of_lt <| by
    simpa using
      (ENNReal.prod_lt_top (s := Finset.univ)
        (f := fun i : Fin d ↦ ENNReal.ofReal (t i : ℝ))
        (fun i _ ↦ ENNReal.ofReal_lt_top))

/-- Helper for Exercise 21.5.4: the `L²` indicator of the anchored rectangle below `t`. -/
private noncomputable def brownianSheetRectangleVector {d : ℕ} (t : BrownianSheetIndex d) :
    Lp ℝ 2 (volume : Measure (Fin d → ℝ)) :=
  MeasureTheory.indicatorConstLp 2
    (measurableSet_brownianSheetRectangle t)
    (volume_brownianSheetRectangle_ne_top t)
    (1 : ℝ)

/-- Helper for Exercise 21.5.4: intersecting two anchored rectangles takes coordinatewise minima.
-/
private theorem inter_brownianSheetRectangle_eq_Icc_min {d : ℕ}
    (s t : BrownianSheetIndex d) :
    brownianSheetRectangle s ∩ brownianSheetRectangle t =
      Set.Icc (0 : Fin d → ℝ) (fun i ↦ min (s i : ℝ) (t i : ℝ)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hs, ht⟩
    -- Proof comment: both box constraints hold simultaneously exactly when each coordinate is
    -- bounded by the smaller upper endpoint.
    exact ⟨hs.1, fun i ↦ le_min (hs.2 i) (ht.2 i)⟩
  · intro hx
    -- Proof comment: the minimum bound is stronger than either original rectangle bound.
    refine ⟨?_, ?_⟩
    · exact ⟨hx.1, fun i ↦ (hx.2 i).trans (min_le_left _ _)⟩
    · exact ⟨hx.1, fun i ↦ (hx.2 i).trans (min_le_right _ _)⟩

/-- Helper for Exercise 21.5.4: the rectangle indicators realize the Brownian-sheet covariance as
an `L²` inner product. -/
private theorem brownianSheetRectangleVector_inner_eq_covariance {d : ℕ}
    (s t : BrownianSheetIndex d) :
    inner ℝ
        (brownianSheetRectangleVector (d := d) s)
        (brownianSheetRectangleVector (d := d) t) =
      brownianSheetCovariance s t := by
  have hle :
      (0 : Fin d → ℝ) ≤ fun i ↦ min (s i : ℝ) (t i : ℝ) := by
    intro i
    exact le_min (s i).2.1 (t i).2.1
  -- Proof comment: the indicator inner product is the box-intersection volume, and the
  -- intersection box has side lengths `min (sᵢ, tᵢ)`.
  simpa [brownianSheetRectangleVector, inter_brownianSheetRectangle_eq_Icc_min, Measure.real,
    Real.volume_Icc_pi_toReal hle, brownianSheetCovariance] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (measurableSet_brownianSheetRectangle s)
      (measurableSet_brownianSheetRectangle t)
      (volume_brownianSheetRectangle_ne_top s)
      (volume_brownianSheetRectangle_ne_top t))

/-- Helper for Exercise 21.5.4: every finite Brownian-sheet covariance matrix is positive
semidefinite. -/
private theorem brownianSheetCovarianceMatrix_posSemidef {d : ℕ}
    (J : Finset (BrownianSheetIndex d)) :
    Matrix.PosSemidef (fun i j : J => brownianSheetCovariance (d := d) i.1 j.1) := by
  -- Proof comment: after identifying the entries with `L²` inner products, the covariance matrix
  -- is the Gram matrix of the anchored rectangle indicators.
  convert (Matrix.posSemidef_gram ℝ (fun i : J ↦ brownianSheetRectangleVector (d := d) i.1)) using 1
  ext i j
  simpa [Matrix.gram] using
    (brownianSheetRectangleVector_inner_eq_covariance (d := d) i.1 j.1).symm

/-- Helper for Exercise 21.5.4: the raw Euclidean finite marginal on `J` before forgetting the
`WithLp` wrapper. -/
private noncomputable def brownianSheetFiniteMarginalRaw (d : ℕ)
    (J : Finset (BrownianSheetIndex d)) : Measure (EuclideanSpace ℝ J) :=
  multivariateGaussian 0 (fun i j : J => brownianSheetCovariance (d := d) i.1 j.1)

/-- Helper for Exercise 21.5.4: the finite-dimensional Brownian-sheet marginal on `J` is the
centered multivariate Gaussian with the Brownian-sheet covariance matrix on `J`. -/
private noncomputable def brownianSheetFiniteMarginal (d : ℕ)
    (J : Finset (BrownianSheetIndex d)) : Measure (J → ℝ) :=
  (brownianSheetFiniteMarginalRaw d J).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ))

/-- Helper for Exercise 21.5.4: each raw finite Brownian-sheet marginal is a probability measure.
-/
private instance instIsProbabilityMeasureBrownianSheetFiniteMarginalRaw {d : ℕ}
    (J : Finset (BrownianSheetIndex d)) :
    IsProbabilityMeasure (brownianSheetFiniteMarginalRaw d J) := by
  dsimp [brownianSheetFiniteMarginalRaw]
  infer_instance

/-- Helper for Exercise 21.5.4: each function-space finite Brownian-sheet marginal is a
probability measure. -/
private instance instIsProbabilityMeasureBrownianSheetFiniteMarginal {d : ℕ}
    (J : Finset (BrownianSheetIndex d)) :
    IsProbabilityMeasure (brownianSheetFiniteMarginal d J) := by
  rw [brownianSheetFiniteMarginal]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Helper for Exercise 21.5.4: the raw Euclidean Brownian-sheet marginals are projective under
coordinate restriction. -/
private theorem brownianSheetFiniteMarginalRaw_projective {d : ℕ}
    (I J : Finset (BrownianSheetIndex d)) (hJI : J ⊆ I) :
    (brownianSheetFiniteMarginalRaw d I).map (EuclideanSpace.restrict₂ hJI) =
      brownianSheetFiniteMarginalRaw d J := by
  let S : Matrix I I ℝ := fun i j ↦ brownianSheetCovariance (d := d) i.1 j.1
  -- Proof comment: the raw owner is exactly a multivariate Gaussian, so restriction is handled by
  -- the canonical multivariate-Gaussian projection theorem.
  simpa [brownianSheetFiniteMarginalRaw, S] using
    (measurePreserving_restrict₂_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ I))
      (S := S)
      (brownianSheetCovarianceMatrix_posSemidef (d := d) I)
      hJI).map_eq

/-- Helper for Exercise 21.5.4: the canonical Euclidean/function-space equivalence commutes with
restriction of coordinates. -/
private theorem withLpRestrict₂_comm {d : ℕ}
    {I J : Finset (BrownianSheetIndex d)} (hJI : J ⊆ I) :
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ)) ∘ EuclideanSpace.restrict₂ hJI =
      ((Finset.restrict₂ (π := fun _ : BrownianSheetIndex d ↦ ℝ) hJI : (I → ℝ) → (J → ℝ)) ∘
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ))) := by
  -- Proof comment: both sides just read the same `J`-coordinates from the ambient Euclidean
  -- vector after unpacking it as a finite function.
  funext x
  ext j
  rfl

/-- Helper for Exercise 21.5.4: each finite Brownian-sheet marginal is a Gaussian measure. -/
private theorem brownianSheetFiniteMarginal_isGaussian {d : ℕ}
    (J : Finset (BrownianSheetIndex d)) :
    IsGaussian (brownianSheetFiniteMarginal d J) := by
  -- Proof comment: the function-space marginal is the image of a multivariate Gaussian under the
  -- canonical linear equivalence between Euclidean vectors and coordinate tuples.
  haveI :
      IsGaussian (brownianSheetFiniteMarginalRaw d J) := by
    simpa [brownianSheetFiniteMarginalRaw] using
      (ProbabilityTheory.isGaussian_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ J))
        (S := fun i j : J => brownianSheetCovariance (d := d) i.1 j.1))
  let hRaw :
      HasGaussianLaw
        (id : EuclideanSpace ℝ J → EuclideanSpace ℝ J)
        (brownianSheetFiniteMarginalRaw d J) :=
    IsGaussian.hasGaussianLaw_id
  simpa [brownianSheetFiniteMarginal] using
    (hRaw.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ))).isGaussian_map

/-- Helper for Exercise 21.5.4: the finite-dimensional Brownian-sheet Gaussian marginals are
projective under restriction of coordinates. -/
private theorem brownianSheetFiniteMarginals_projective (d : ℕ) :
    IsProjectiveMeasureFamily
      (α := fun _ : BrownianSheetIndex d ↦ ℝ)
      (brownianSheetFiniteMarginal d) := by
  intro I J hJI
  -- Proof comment: first restrict the raw Euclidean Gaussian owner, then transport that identity
  -- once through the canonical Euclidean/function-space equivalence.
  calc
    brownianSheetFiniteMarginal d J
        = ((brownianSheetFiniteMarginalRaw d I).map (EuclideanSpace.restrict₂ hJI)).map
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ)) := by
              rw [brownianSheetFiniteMarginal]
              rw [brownianSheetFiniteMarginalRaw_projective (d := d) I J hJI]
    _ = (brownianSheetFiniteMarginalRaw d I).map
          ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ)) ∘ EuclideanSpace.restrict₂ hJI) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (brownianSheetFiniteMarginalRaw d I).map
          (((Finset.restrict₂ (π := fun _ : BrownianSheetIndex d ↦ ℝ) hJI : (I → ℝ) → (J → ℝ)) ∘
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)))) := by
          refine Measure.map_congr <| Filter.Eventually.of_forall fun x ↦ ?_
          exact congrFun (withLpRestrict₂_comm (d := d) (I := I) (J := J) hJI) x
    _ = ((brownianSheetFiniteMarginalRaw d I).map
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ))).map
          (Finset.restrict₂ (π := fun _ : BrownianSheetIndex d ↦ ℝ) hJI : (I → ℝ) → (J → ℝ)) := by
          symm
          exact Measure.map_map (Finset.measurable_restrict₂ hJI) (by fun_prop)
    _ = (brownianSheetFiniteMarginal d I).map
          (Finset.restrict₂ (π := fun _ : BrownianSheetIndex d ↦ ℝ) hJI : (I → ℝ) → (J → ℝ)) := by
          rw [brownianSheetFiniteMarginal]

/-- Helper for Exercise 21.5.4: a projective-limit path law has the prescribed finite coordinate
laws. -/
private theorem brownianSheetCoordinateRestriction_hasLaw {d : ℕ}
    {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hμ : IsProjectiveLimit μ (brownianSheetFiniteMarginal d))
    (J : Finset (BrownianSheetIndex d)) :
    HasLaw J.restrict (brownianSheetFiniteMarginal d J) μ := by
  -- Proof comment: the projective-limit identity is exactly the statement that the `J`-coordinate
  -- restriction has law `brownianSheetFiniteMarginal d J`.
  exact ⟨(Finset.measurable_restrict J).aemeasurable, hμ J⟩

/-- Helper for Exercise 21.5.4: after re-bundling a finite restriction with `toLp`, the
projective-limit law is exactly the raw multivariate Gaussian marginal. -/
private theorem brownianSheetCoordinateRestriction_toLp_hasLaw {d : ℕ}
    {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hμ : IsProjectiveLimit μ (brownianSheetFiniteMarginal d))
    (J : Finset (BrownianSheetIndex d)) :
    HasLaw
      (fun ω ↦ MeasurableEquiv.toLp 2 (J → ℝ) (J.restrict ω))
      (brownianSheetFiniteMarginalRaw d J)
      μ := by
  refine
    ⟨((MeasurableEquiv.toLp 2 (J → ℝ)).measurable.comp
        (Finset.measurable_restrict J)).aemeasurable, ?_⟩
  -- Proof comment: the projective-limit law on coordinate tuples is pushed back to the raw
  -- Euclidean owner by composing with the inverse `toLp` map.
  calc
    μ.map (fun ω ↦ MeasurableEquiv.toLp 2 (J → ℝ) (J.restrict ω))
        = μ.map (((MeasurableEquiv.toLp 2 (J → ℝ)) : (J → ℝ) → EuclideanSpace ℝ J) ∘
            J.restrict) := by
            rfl
    _ = (μ.map J.restrict).map (MeasurableEquiv.toLp 2 (J → ℝ)) := by
          rw [Measure.map_map
            (MeasurableEquiv.toLp 2 (J → ℝ)).measurable
            (Finset.measurable_restrict J)]
    _ = (brownianSheetFiniteMarginal d J).map (MeasurableEquiv.toLp 2 (J → ℝ)) := by
          rw [hμ J]
    _ = (brownianSheetFiniteMarginalRaw d J).map
          ((MeasurableEquiv.toLp 2 (J → ℝ)) ∘
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J ↦ ℝ))) := by
          rw [brownianSheetFiniteMarginal, Measure.map_map
            (MeasurableEquiv.toLp 2 (J → ℝ)).measurable (by fun_prop)]
    _ = (brownianSheetFiniteMarginalRaw d J).map id := by
          refine Measure.map_congr <| Filter.Eventually.of_forall fun x ↦ ?_
          ext j
          simp
    _ = brownianSheetFiniteMarginalRaw d J := by
          rw [Measure.map_id]

/-- Helper for Exercise 21.5.4: the Brownian-sheet finite marginals admit a canonical projective
limit path law. -/
private theorem existsBrownianSheetFiniteMarginalProjectiveLimit (d : ℕ) :
    ∃ μ : Measure (BrownianSheetIndex d → ℝ),
      IsProjectiveLimit μ (brownianSheetFiniteMarginal d) := by
  -- Proof comment: Theorem 14.36 applies directly to the already-proved projective family of
  -- finite Brownian-sheet marginals.
  exact exists_projectiveLimit_of_isProjectiveMeasureFamily
    (I := BrownianSheetIndex d)
    (Ω := fun _ : BrownianSheetIndex d ↦ ℝ)
    (P := brownianSheetFiniteMarginal d)
    (brownianSheetFiniteMarginals_projective d)

/-- Helper for Exercise 21.5.4: evaluating a finite `toLp` restriction at a coordinate recovers
the original Brownian-sheet coordinate process. -/
private theorem brownianSheetRestrictionToLp_apply {d : ℕ}
    {J : Finset (BrownianSheetIndex d)} (t : J) (ω : BrownianSheetIndex d → ℝ) :
    MeasurableEquiv.toLp 2 (J → ℝ) (J.restrict ω) t =
      brownianSheetCoordinateProcess d t.1 ω := by
  -- Proof comment: `toLp` only rebundles the finite function `J.restrict ω`, so evaluating it
  -- at `t` is still the original coordinate `ω t.1`.
  rfl

/-- Helper for Exercise 21.5.4: the projective-limit path law makes the canonical coordinate
process Gaussian. -/
private theorem brownianSheetCoordinateProcess_isGaussian_ofProjectiveLimit {d : ℕ}
    {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hμ : IsProjectiveLimit μ (brownianSheetFiniteMarginal d)) :
    IsGaussianProcess (brownianSheetCoordinateProcess d) μ := by
  refine { hasGaussianLaw := ?_ }
  intro J
  let _ : IsGaussian (brownianSheetFiniteMarginal d J) :=
    brownianSheetFiniteMarginal_isGaussian (d := d) J
  -- Proof comment: every finite restriction has the prescribed Brownian-sheet Gaussian marginal,
  -- hence every finite-dimensional law of the coordinate process is Gaussian.
  simpa [brownianSheetCoordinateProcess] using
    (brownianSheetCoordinateRestriction_hasLaw (d := d) hμ J).hasGaussianLaw

/-- Helper for Exercise 21.5.4: the projective-limit path law keeps every Brownian-sheet
coordinate centered. -/
private theorem brownianSheetCoordinate_meanZero_ofProjectiveLimit {d : ℕ}
    {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hμ : IsProjectiveLimit μ (brownianSheetFiniteMarginal d))
    (t : BrownianSheetIndex d) :
    ∫ ω, brownianSheetCoordinateProcess d t ω ∂μ = 0 := by
  classical
  let J : Finset (BrownianSheetIndex d) := {t}
  let it : J := ⟨t, by simp [J]⟩
  have hLaw :=
    brownianSheetCoordinateRestriction_toLp_hasLaw (d := d) hμ J
  have hCoordLaw :
      HasLaw
        (brownianSheetCoordinateProcess d t)
        (gaussianReal 0 (brownianSheetCovariance (d := d) t t).toNNReal)
        μ := by
    let hEvalLaw :
        HasLaw
          (fun x : EuclideanSpace ℝ J ↦ x it)
          (gaussianReal 0 ((fun i j : J ↦ brownianSheetCovariance (d := d) i.1 j.1) it it).toNNReal)
          (brownianSheetFiniteMarginalRaw d J) :=
      (measurePreserving_eval_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ J))
        (S := fun i j : J ↦ brownianSheetCovariance (d := d) i.1 j.1)
        (brownianSheetCovarianceMatrix_posSemidef (d := d) J)).hasLaw
    -- Proof comment: the singleton raw marginal is a one-dimensional centered Gaussian, and the
    -- restriction-evaluation adapter identifies it with the target coordinate process.
    simpa [J, it, brownianSheetRestrictionToLp_apply, brownianSheetCoordinateProcess] using
      hEvalLaw.comp hLaw
  -- Proof comment: the mean of the centered one-dimensional Gaussian marginal is `0`.
  rw [hCoordLaw.integral_eq, integral_id_gaussianReal]

/-- Helper for Exercise 21.5.4: the projective-limit path law has the Brownian-sheet covariance
kernel. -/
private theorem brownianSheetCoordinate_covariance_ofProjectiveLimit {d : ℕ}
    {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hμ : IsProjectiveLimit μ (brownianSheetFiniteMarginal d))
    (s t : BrownianSheetIndex d) :
    cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t; μ] =
      brownianSheetCovariance s t := by
  classical
  let J : Finset (BrownianSheetIndex d) := {s, t}
  let is : J := ⟨s, by simp [J]⟩
  let it : J := ⟨t, by simp [J]⟩
  have hLaw :=
    brownianSheetCoordinateRestriction_toLp_hasLaw (d := d) hμ J
  have hs_meas :
      AEMeasurable (fun x : EuclideanSpace ℝ J ↦ x is) (brownianSheetFiniteMarginalRaw d J) := by
    fun_prop
  have ht_meas :
      AEMeasurable (fun x : EuclideanSpace ℝ J ↦ x it) (brownianSheetFiniteMarginalRaw d J) := by
    fun_prop
  have hTransport :
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t; μ] =
        cov[fun x : EuclideanSpace ℝ J ↦ x is, fun x ↦ x it;
          brownianSheetFiniteMarginalRaw d J] := by
    -- Proof comment: transport the covariance through the finite two-point restriction law and
    -- pay the `toLp`/coordinate identification once.
    simpa [J, is, it, brownianSheetRestrictionToLp_apply, brownianSheetCoordinateProcess] using
      (hLaw.covariance_fun_comp hs_meas ht_meas)
  rw [hTransport]
  -- Proof comment: the raw two-point marginal is the centered multivariate Gaussian with the
  -- Brownian-sheet covariance matrix, so its covariance entry is the desired kernel value.
  simpa [brownianSheetFiniteMarginalRaw, J, is, it] using
    (covariance_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ J))
      (S := fun i j : J ↦ brownianSheetCovariance (d := d) i.1 j.1)
      (brownianSheetCovarianceMatrix_posSemidef (d := d) J)
      is it)

-- Proof sketch: realize the coordinate process on path space under a Gaussian probability law
-- whose finite-dimensional marginals have covariance matrix
-- `(brownianSheetCovariance s t)_{s,t}`, obtained from a suitable orthonormal basis on
-- `[0,1]^d`.
/-- Exercise 21.5.4: the canonical Brownian-sheet coordinate process admits a centered Gaussian
path law with covariance kernel `∏ᵢ min (sᵢ, tᵢ)`. -/
theorem exists_centeredBrownianSheetGaussianPathLaw (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsGaussianProcess
        (brownianSheetCoordinateProcess d)
        (μ : Measure (BrownianSheetIndex d → ℝ)) ∧
      (∀ t : BrownianSheetIndex d,
        ∫ ω, brownianSheetCoordinateProcess d t ω ∂
          (μ : Measure (BrownianSheetIndex d → ℝ)) = 0) ∧
      ∀ s t : BrownianSheetIndex d,
        cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
          (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t := by
  rcases existsBrownianSheetFiniteMarginalProjectiveLimit d with ⟨μ, hμ⟩
  let μprob : ProbabilityMeasure (BrownianSheetIndex d → ℝ) := ⟨μ, hμ.isProbabilityMeasure⟩
  -- Route correction: the continuity side is already stable; the remaining work is to build the
  -- projective-limit path law and extract Gaussianity, centeredness, and covariance from its
  -- finite-dimensional marginals.
  refine ⟨μprob, ?_, ?_, ?_⟩
  · -- Proof comment: Gaussian finite-dimensional marginals make the coordinate process Gaussian.
    exact brownianSheetCoordinateProcess_isGaussian_ofProjectiveLimit (d := d) hμ
  · intro t
    -- Proof comment: the singleton finite marginal is the centered one-dimensional Gaussian at
    -- `t`.
    exact brownianSheetCoordinate_meanZero_ofProjectiveLimit (d := d) hμ t
  · intro s t
    -- Proof comment: the two-point finite marginal reads off the covariance kernel entry.
    exact brownianSheetCoordinate_covariance_ofProjectiveLimit (d := d) hμ s t

/-- Part (1): there exists a Gaussian process on `[0,1]^d` whose covariance kernel is
`∏ᵢ min (sᵢ, tᵢ)`. -/
theorem exists_brownianSheetGaussianProcess (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsGaussianProcess
        (brownianSheetCoordinateProcess d)
        (μ : Measure (BrownianSheetIndex d → ℝ)) ∧
      ∀ s t : BrownianSheetIndex d,
        cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
          (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t := by
  -- Proof comment: project the richer centered path-law helper to the covariance-only statement
  -- required by part (1).
  rcases exists_centeredBrownianSheetGaussianPathLaw d with ⟨μ, hgauss, -, hcov⟩
  exact ⟨μ, hgauss, hcov⟩

/-- Helper for Exercise 21.5.4: clipping a real coordinate into `[0,1]` is the scalar part of the
Brownian-sheet cube projection. -/
private noncomputable def clipUnitReal (x : ℝ) : ℝ :=
  max 0 (min 1 x)

/-- Helper for Exercise 21.5.4: the scalar clipping map always lands in `[0,1]`. -/
private theorem clipUnitReal_mem_Icc (x : ℝ) :
    clipUnitReal x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · unfold clipUnitReal
    exact (max_le_iff.2 ⟨by norm_num, min_le_left _ _⟩)

/-- Helper for Exercise 21.5.4: view a sheet index point as its ambient Euclidean coordinate
vector. -/
private def sheetIndexToEuclidean {d : ℕ} :
    BrownianSheetIndex d → EuclideanSpace ℝ (Fin d) :=
  fun t ↦
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm
      (fun i ↦ (t i : ℝ))

/-- Helper for Exercise 21.5.4: the subtype embedding `[0,1]^d ↪ ℝ^d` is continuous. -/
private theorem continuous_sheetIndexToEuclidean {d : ℕ} :
    Continuous (sheetIndexToEuclidean (d := d)) := by
  -- Proof comment: continuity is coordinatewise because each component is just the subtype
  -- coercion `Set.Icc (0 : ℝ) 1 → ℝ`.
  exact
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm.continuous.comp <|
      continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)

/-- Helper for Exercise 21.5.4: clip an ambient Euclidean point coordinatewise back into the
Brownian-sheet cube `[0,1]^d`. -/
private def clipUnitCube {d : ℕ} :
    EuclideanSpace ℝ (Fin d) → BrownianSheetIndex d :=
  fun x i ↦ ⟨clipUnitReal (x i), clipUnitReal_mem_Icc (x i)⟩

/-- Helper for Exercise 21.5.4: clipping fixes points already lying in the Brownian-sheet cube. -/
private theorem clipUnitCube_coe_eq {d : ℕ} (t : BrownianSheetIndex d) :
    clipUnitCube (sheetIndexToEuclidean t) = t := by
  ext i
  have h0 : (0 : ℝ) ≤ (t i : ℝ) := (t i).2.1
  have h1 : (t i : ℝ) ≤ 1 := (t i).2.2
  -- Proof comment: on genuine sheet coordinates, both `min 1` and `max 0` are inactive.
  simp [clipUnitCube, sheetIndexToEuclidean, clipUnitReal, h0, h1]

/-- Helper for Exercise 21.5.4: extend the sheet-indexed coordinate process to ambient Euclidean
space by clipping back to `[0,1]^d`. -/
private def brownianSheetClippedProcess (d : ℕ) :
    EuclideanSpace ℝ (Fin d) → (BrownianSheetIndex d → ℝ) → ℝ :=
  fun z ω ↦ brownianSheetCoordinateProcess d (clipUnitCube z) ω

/-- Helper for Exercise 21.5.4: scalar clipping to `[0,1]` is `1`-Lipschitz. -/
private theorem dist_clipUnitReal_le (x y : ℝ) :
    dist (clipUnitReal x) (clipUnitReal y) ≤ dist x y := by
  -- Proof comment: `x ↦ max 0 (min 1 x)` is the composition of two standard `1`-Lipschitz
  -- interval truncations.
  unfold clipUnitReal
  simpa [one_mul] using ((LipschitzWith.id.const_min 1).const_max 0).dist_le_mul x y

/-- Helper for Exercise 21.5.4: each clipped coordinate difference is bounded by the ambient
Euclidean distance. -/
private theorem abs_sub_clipUnitReal_le_dist
    {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |clipUnitReal (x i) - clipUnitReal (y i)| ≤ dist x y := by
  have hclip :
      dist (clipUnitReal (x i)) (clipUnitReal (y i)) ≤ dist (x i) (y i) :=
    dist_clipUnitReal_le (x i) (y i)
  have hcoord_sq : dist (x i) (y i) ^ 2 ≤ dist x y ^ 2 := by
    have hsingle :
        dist (x i) (y i) ^ 2 ≤ ∑ j : Fin d, dist (x j) (y j) ^ 2 := by
      simpa using
        (Finset.single_le_sum
          (fun j _ ↦ sq_nonneg (dist (x j) (y j)))
          (Finset.mem_univ i))
    simpa [EuclideanSpace.dist_sq_eq] using hsingle
  have hcoord : dist (x i) (y i) ≤ dist x y := by
    have hcoord_nonneg : 0 ≤ dist (x i) (y i) := dist_nonneg
    have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
    nlinarith
  calc
    |clipUnitReal (x i) - clipUnitReal (y i)| =
        dist (clipUnitReal (x i)) (clipUnitReal (y i)) := by
          rw [Real.dist_eq]
    _ ≤ dist (x i) (y i) := hclip
    _ ≤ dist x y := hcoord

/-- Helper for Exercise 21.5.4: the total clipped coordinate increment is controlled by the
ambient Euclidean distance. -/
private theorem sum_abs_sub_clipUnitReal_le_mul_dist
    {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    ∑ i : Fin d, |clipUnitReal (x i) - clipUnitReal (y i)| ≤ (d : ℝ) * dist x y := by
  -- Proof comment: there are `d` coordinates, and each clipped coordinate difference is bounded
  -- by the ambient Euclidean distance.
  calc
    ∑ i : Fin d, |clipUnitReal (x i) - clipUnitReal (y i)|
        ≤ ∑ i : Fin d, dist x y := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact abs_sub_clipUnitReal_le_dist x y i
    _ = (d : ℝ) * dist x y := by simp

/-- Helper for Exercise 21.5.4: even powers of real `edist` increments are `ENNReal.ofReal` of
the corresponding even polynomial increment. -/
private theorem realEdist_pow_even_eq_ofReal_sub_pow_even (a b : ℝ) (k : ℕ) :
    edist a b ^ (2 * k : ℕ) = ENNReal.ofReal ((b - a) ^ (2 * k)) := by
  -- Proof comment: rewrite the metric distance through `|a - b|`, then use that an even power is
  -- determined by the square of the increment.
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg (a - b))]
  congr 1
  calc
    |a - b| ^ (2 * k) = (|a - b| ^ 2) ^ k := by
      rw [pow_mul]
    _ = ((b - a) ^ 2) ^ k := by
      rw [abs_sub_comm, sq_abs]
    _ = (b - a) ^ (2 * k) := by
      rw [pow_mul]

/-- Helper for Exercise 21.5.4: finite products of numbers in `[0,1]` stay bounded by `1`. -/
private theorem prod_range_le_one_of_nonneg_of_le_one
    (f : ℕ → ℝ) :
    ∀ n : ℕ,
      (∀ i < n, 0 ≤ f i) →
      (∀ i < n, f i ≤ 1) →
        Finset.prod (Finset.range n) f ≤ 1
  | 0, _, _ => by simp
  | n + 1, hnonneg, hle => by
      -- Proof comment: split off the last factor; both the prefix product and the final factor
      -- are bounded by `1`, so their product is again bounded by `1`.
      rw [Finset.prod_range_succ]
      have hprefix :
          Finset.prod (Finset.range n) f ≤ 1 :=
        prod_range_le_one_of_nonneg_of_le_one f n
          (fun i hi ↦ hnonneg i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ hle i (lt_trans hi (Nat.lt_succ_self n)))
      have hprefix_nonneg :
          0 ≤ Finset.prod (Finset.range n) f := by
        exact Finset.prod_nonneg fun i hi ↦
          hnonneg i (lt_trans (Finset.mem_range.1 hi) (Nat.lt_succ_self n))
      have hlast : f n ≤ 1 := hle n (Nat.lt_succ_self n)
      have hlast_nonneg : 0 ≤ f n := hnonneg n (Nat.lt_succ_self n)
      nlinarith

/-- Helper for Exercise 21.5.4: if `0 ≤ bᵢ ≤ aᵢ ≤ 1`, then the product gap is controlled by the
sum of the coordinate gaps. -/
private theorem prod_range_sub_le_sum_range_sub_of_nonneg_of_le_one_of_le
    (a b : ℕ → ℝ) :
    ∀ n : ℕ,
      (∀ i < n, 0 ≤ a i) →
      (∀ i < n, 0 ≤ b i) →
      (∀ i < n, a i ≤ 1) →
      (∀ i < n, b i ≤ a i) →
        (Finset.prod (Finset.range n) a - Finset.prod (Finset.range n) b) ≤
          Finset.sum (Finset.range n) (fun i ↦ a i - b i)
  | 0, _, _, _, _ => by simp
  | n + 1, ha_nonneg, hb_nonneg, ha_le_one, hb_le_a => by
      -- Proof comment: isolate the last factor and telescope the product difference into a prefix
      -- gap plus the last-coordinate gap, both controlled by the induction hypothesis and the
      -- `[0,1]` bounds.
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
      let A := Finset.prod (Finset.range n) a
      let B := Finset.prod (Finset.range n) b
      have hA_le_one : A ≤ 1 := by
        dsimp [A]
        exact prod_range_le_one_of_nonneg_of_le_one a n
          (fun i hi ↦ ha_nonneg i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ ha_le_one i (lt_trans hi (Nat.lt_succ_self n)))
      have hB_le_one : B ≤ 1 := by
        dsimp [B]
        exact prod_range_le_one_of_nonneg_of_le_one b n
          (fun i hi ↦ hb_nonneg i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ (hb_le_a i (lt_trans hi (Nat.lt_succ_self n))).trans
            (ha_le_one i (lt_trans hi (Nat.lt_succ_self n))))
      have hB_le_A : B ≤ A := by
        dsimp [A, B]
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          exact hb_nonneg i (lt_trans (Finset.mem_range.1 hi) (Nat.lt_succ_self n))
        · intro i hi
          exact hb_le_a i (lt_trans (Finset.mem_range.1 hi) (Nat.lt_succ_self n))
      have hAB_nonneg : 0 ≤ A - B := sub_nonneg.mpr hB_le_A
      have hgap_nonneg : 0 ≤ a n - b n := sub_nonneg.mpr (hb_le_a n (Nat.lt_succ_self n))
      have hstep :
          A * a n - B * b n ≤ (A - B) + (a n - b n) := by
        calc
          A * a n - B * b n = a n * (A - B) + B * (a n - b n) := by ring
          _ ≤ 1 * (A - B) + 1 * (a n - b n) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (ha_le_one n (Nat.lt_succ_self n)) hAB_nonneg
            · exact mul_le_mul_of_nonneg_right hB_le_one hgap_nonneg
          _ = (A - B) + (a n - b n) := by ring
      have hprefix :
          A - B ≤ Finset.sum (Finset.range n) (fun i ↦ a i - b i) := by
        dsimp [A, B]
        exact prod_range_sub_le_sum_range_sub_of_nonneg_of_le_one_of_le a b n
          (fun i hi ↦ ha_nonneg i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ hb_nonneg i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ ha_le_one i (lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ hb_le_a i (lt_trans hi (Nat.lt_succ_self n)))
      linarith

/-- Helper for Exercise 21.5.4: the Brownian-sheet variance kernel is controlled by the sum of
the coordinate increments. -/
theorem brownianSheetIncrementVariance_le_sumAbsSub
    {d : ℕ} (s t : BrownianSheetIndex d) :
    brownianSheetCovariance s s + brownianSheetCovariance t t - 2 * brownianSheetCovariance s t ≤
      ∑ i : Fin d, |(s i : ℝ) - (t i : ℝ)| := by
  classical
  let a : ℕ → ℝ := fun i ↦ if h : i < d then (s ⟨i, h⟩ : ℝ) else 0
  let b : ℕ → ℝ := fun i ↦ if h : i < d then min (s ⟨i, h⟩ : ℝ) (t ⟨i, h⟩ : ℝ) else 0
  let c : ℕ → ℝ := fun i ↦ if h : i < d then (t ⟨i, h⟩ : ℝ) else 0
  have hprod_s :
      (∏ i : Fin d, (s i : ℝ)) = Finset.prod (Finset.range d) a := by
    simpa [a] using (Fin.prod_univ_eq_prod_range a d)
  have hprod_t :
      (∏ i : Fin d, (t i : ℝ)) = Finset.prod (Finset.range d) c := by
    simpa [c] using (Fin.prod_univ_eq_prod_range c d)
  have hprod_min :
      (∏ i : Fin d, min (s i : ℝ) (t i : ℝ)) = Finset.prod (Finset.range d) b := by
    simpa [b] using (Fin.prod_univ_eq_prod_range b d)
  have hsum_abs :
      (∑ i : Fin d, |(s i : ℝ) - (t i : ℝ)|) =
        Finset.sum (Finset.range d) (fun i ↦ |a i - c i|) := by
    simpa [a, c] using (Fin.sum_univ_eq_sum_range (fun i ↦ |a i - c i|) d)
  have hs_bound :
      Finset.prod (Finset.range d) a - Finset.prod (Finset.range d) b ≤
        Finset.sum (Finset.range d) (fun i ↦ a i - b i) := by
    -- Proof comment: the product difference is bounded by the sum of the coordinatewise losses
    -- because every factor lives in `[0,1]`.
    exact
      prod_range_sub_le_sum_range_sub_of_nonneg_of_le_one_of_le a b d
        (fun i hi ↦ by simp [a, hi, (s ⟨i, hi⟩).2.1])
        (fun i hi ↦ by simp [b, hi, (s ⟨i, hi⟩).2.1, (t ⟨i, hi⟩).2.1])
        (fun i hi ↦ by simp [a, hi, (s ⟨i, hi⟩).2.2])
        (fun i hi ↦ by simp [a, b, hi])
  have ht_bound :
      Finset.prod (Finset.range d) c - Finset.prod (Finset.range d) b ≤
        Finset.sum (Finset.range d) (fun i ↦ c i - b i) := by
    -- Proof comment: the same estimate applies to the second rectangle against the common overlap
    -- product.
    exact
      prod_range_sub_le_sum_range_sub_of_nonneg_of_le_one_of_le c b d
        (fun i hi ↦ by simp [c, hi, (t ⟨i, hi⟩).2.1])
        (fun i hi ↦ by simp [b, hi, (s ⟨i, hi⟩).2.1, (t ⟨i, hi⟩).2.1])
        (fun i hi ↦ by simp [c, hi, (t ⟨i, hi⟩).2.2])
        (fun i hi ↦ by simp [b, c, hi])
  have hsum_gap :
      Finset.sum (Finset.range d) (fun i ↦ a i - b i) +
          Finset.sum (Finset.range d) (fun i ↦ c i - b i) =
        Finset.sum (Finset.range d) (fun i ↦ |a i - c i|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hid : i < d := Finset.mem_range.1 hi
    dsimp [a, b, c]
    simp [hid]
    by_cases hst : (s ⟨i, hid⟩ : ℝ) ≤ (t ⟨i, hid⟩ : ℝ)
    · rw [min_eq_left hst, abs_of_nonpos (sub_nonpos.mpr hst)]
      linarith
    · have hts : (t ⟨i, hid⟩ : ℝ) ≤ (s ⟨i, hid⟩ : ℝ) := le_of_not_ge hst
      rw [min_eq_right hts, abs_of_nonneg (sub_nonneg.mpr hts)]
      linarith
  -- Proof comment: write the symmetric-difference volume as the sum of the two one-sided product
  -- gaps, then replace those product gaps by the coordinatewise losses.
  rw [brownianSheetCovariance_self, brownianSheetCovariance_self, brownianSheetCovariance,
    hprod_s, hprod_t, hprod_min, hsum_abs]
  linarith

/-- Helper for Exercise 21.5.4: the clipped increment variance rewrites to the deterministic
Brownian-sheet kernel expression. -/
private theorem brownianSheetClippedIncrement_covarianceForm
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
        (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Var[fun ω ↦ brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω;
      (μ : Measure (BrownianSheetIndex d → ℝ))] =
      brownianSheetCovariance (clipUnitCube x) (clipUnitCube x) +
        brownianSheetCovariance (clipUnitCube y) (clipUnitCube y) -
          2 * brownianSheetCovariance (clipUnitCube x) (clipUnitCube y) := by
  let inc : (BrownianSheetIndex d → ℝ) → ℝ := fun ω ↦
    brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω
  have hxGaussian :
      HasGaussianLaw (brownianSheetClippedProcess d x)
        (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: every clipped coordinate is still one evaluation of the Gaussian process.
    simpa [brownianSheetClippedProcess] using hgauss.hasGaussianLaw_eval (clipUnitCube x)
  have hyGaussian :
      HasGaussianLaw (brownianSheetClippedProcess d y)
        (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: the same evaluation argument applies at the clipped point `y`.
    simpa [brownianSheetClippedProcess] using hgauss.hasGaussianLaw_eval (clipUnitCube y)
  have hincGaussian : HasGaussianLaw inc (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: differences of two coordinates of a Gaussian process are Gaussian.
    simpa [inc, brownianSheetClippedProcess] using
      hgauss.hasGaussianLaw_fun_sub (s := clipUnitCube x) (t := clipUnitCube y)
  have hxMem :
      MemLp (brownianSheetClippedProcess d x) 2 (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    hxGaussian.memLp_two
  have hyMem :
      MemLp (brownianSheetClippedProcess d y) 2 (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    hyGaussian.memLp_two
  have hincMem :
      MemLp inc 2 (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    hincGaussian.memLp_two
  have hxx :
      cov[brownianSheetClippedProcess d x, brownianSheetClippedProcess d x;
        (μ : Measure (BrownianSheetIndex d → ℝ))] =
        brownianSheetCovariance (clipUnitCube x) (clipUnitCube x) := by
    simpa [brownianSheetClippedProcess] using hcov (clipUnitCube x) (clipUnitCube x)
  have hyy :
      cov[brownianSheetClippedProcess d y, brownianSheetClippedProcess d y;
        (μ : Measure (BrownianSheetIndex d → ℝ))] =
        brownianSheetCovariance (clipUnitCube y) (clipUnitCube y) := by
    simpa [brownianSheetClippedProcess] using hcov (clipUnitCube y) (clipUnitCube y)
  have hxy :
      cov[brownianSheetClippedProcess d x, brownianSheetClippedProcess d y;
        (μ : Measure (BrownianSheetIndex d → ℝ))] =
        brownianSheetCovariance (clipUnitCube x) (clipUnitCube y) := by
    simpa [brownianSheetClippedProcess] using hcov (clipUnitCube x) (clipUnitCube y)
  have hyx :
      cov[brownianSheetClippedProcess d y, brownianSheetClippedProcess d x;
        (μ : Measure (BrownianSheetIndex d → ℝ))] =
        brownianSheetCovariance (clipUnitCube y) (clipUnitCube x) := by
    simpa [brownianSheetClippedProcess] using hcov (clipUnitCube y) (clipUnitCube x)
  have hsymm :
      brownianSheetCovariance (clipUnitCube y) (clipUnitCube x) =
        brownianSheetCovariance (clipUnitCube x) (clipUnitCube y) := by
    -- Proof comment: the kernel is symmetric because `min` is symmetric in each coordinate.
    simp [brownianSheetCovariance, min_comm]
  -- Proof comment: expand the variance through covariance bilinearity and substitute the Brownian
  -- kernel values at the clipped endpoints.
  calc
    Var[fun ω ↦ brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω;
        (μ : Measure (BrownianSheetIndex d → ℝ))]
        = Var[inc; (μ : Measure (BrownianSheetIndex d → ℝ))] := by
            rfl
    _ =
        brownianSheetCovariance (clipUnitCube x) (clipUnitCube x) +
          brownianSheetCovariance (clipUnitCube y) (clipUnitCube y) -
            2 * brownianSheetCovariance (clipUnitCube x) (clipUnitCube y) := by
              rw [← covariance_self hincGaussian.aemeasurable,
                covariance_fun_sub_left hxMem hyMem hincMem,
                covariance_fun_sub_right hxMem hxMem hyMem,
                covariance_fun_sub_right hyMem hxMem hyMem,
                hxx, hxy, hyx, hyy, hsymm]
              ring

/-- Helper for Exercise 21.5.4: the clipped Brownian-sheet increment has variance bounded by the
ambient Euclidean distance up to the factor `d`. -/
private theorem brownianSheetClippedIncrement_variance_le_mulDist
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
        (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Var[fun ω ↦ brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω;
      (μ : Measure (BrownianSheetIndex d → ℝ))] ≤ (d : ℝ) * dist x y := by
  -- Proof comment: first rewrite the variance to the deterministic covariance kernel, then use
  -- the previously proved product-gap estimate and the clipped-coordinate distance bound.
  calc
    Var[fun ω ↦ brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω;
        (μ : Measure (BrownianSheetIndex d → ℝ))]
        =
          brownianSheetCovariance (clipUnitCube x) (clipUnitCube x) +
            brownianSheetCovariance (clipUnitCube y) (clipUnitCube y) -
              2 * brownianSheetCovariance (clipUnitCube x) (clipUnitCube y) := by
              exact brownianSheetClippedIncrement_covarianceForm μ hgauss hcov x y
    _ ≤ ∑ i : Fin d, |((clipUnitCube x) i : ℝ) - ((clipUnitCube y) i : ℝ)| := by
          exact brownianSheetIncrementVariance_le_sumAbsSub (clipUnitCube x) (clipUnitCube y)
    _ ≤ (d : ℝ) * dist x y := by
          simpa [clipUnitCube] using sum_abs_sub_clipUnitReal_le_mul_dist x y

/-- Helper for Exercise 21.5.4: the clipped Brownian-sheet increment satisfies the explicit even
moment estimate needed for the Euclidean Kolmogorov criterion. -/
private theorem brownianSheetClippedIncrement_evenMoment_bound
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (hmean_zero : ∀ t : BrownianSheetIndex d,
      ∫ ω, brownianSheetCoordinateProcess d t ω ∂
        (μ : Measure (BrownianSheetIndex d → ℝ)) = 0)
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
        (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, (brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω) ^ (2 * (d + 1))
        ∂(μ : Measure (BrownianSheetIndex d → ℝ)) ≤
      (((Nat.factorial (2 * (d + 1)) : ℝ) /
          (((2 : ℝ) ^ (d + 1)) * (Nat.factorial (d + 1) : ℝ))) *
        (d : ℝ) ^ (d + 1)) *
        dist x y ^ (d + 1) := by
  let n : ℕ := d + 1
  let inc : (BrownianSheetIndex d → ℝ) → ℝ := fun ω ↦
    brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω
  let coeff : ℝ :=
    (Nat.factorial (2 * n) : ℝ) / (((2 : ℝ) ^ n) * (Nat.factorial n : ℝ))
  have hxGaussian :
      HasGaussianLaw (brownianSheetClippedProcess d x)
        (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: each clipped value is one Gaussian coordinate evaluation.
    simpa [brownianSheetClippedProcess] using hgauss.hasGaussianLaw_eval (clipUnitCube x)
  have hyGaussian :
      HasGaussianLaw (brownianSheetClippedProcess d y)
        (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: the same coordinate-evaluation argument works at `y`.
    simpa [brownianSheetClippedProcess] using hgauss.hasGaussianLaw_eval (clipUnitCube y)
  have hincGaussian : HasGaussianLaw inc (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: Gaussianity is preserved under subtracting two coordinates.
    simpa [inc, brownianSheetClippedProcess] using
      hgauss.hasGaussianLaw_fun_sub (s := clipUnitCube x) (t := clipUnitCube y)
  have hxMem :
      MemLp (brownianSheetClippedProcess d x) 2 (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    hxGaussian.memLp_two
  have hyMem :
      MemLp (brownianSheetClippedProcess d y) 2 (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    hyGaussian.memLp_two
  have hMean : ∫ ω, inc ω ∂(μ : Measure (BrownianSheetIndex d → ℝ)) = 0 := by
    -- Proof comment: centeredness of the two coordinates makes the clipped increment centered.
    rw [show inc = fun ω ↦ brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω by
      rfl]
    rw [integral_sub (hxMem.integrable (by norm_num)) (hyMem.integrable (by norm_num))]
    simp [brownianSheetClippedProcess, hmean_zero]
  have hcoeff_nonneg : 0 ≤ coeff := by
    positivity
  have hpow :
      Var[inc; (μ : Measure (BrownianSheetIndex d → ℝ))] ^ n ≤
        ((d : ℝ) * dist x y) ^ n := by
    exact
      pow_le_pow_left₀
        (variance_nonneg inc (μ : Measure (BrownianSheetIndex d → ℝ)))
        (brownianSheetClippedIncrement_variance_le_mulDist μ hgauss hcov x y)
        n
  calc
    ∫ ω, (brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω) ^ (2 * (d + 1))
        ∂(μ : Measure (BrownianSheetIndex d → ℝ))
        = coeff * Var[inc; (μ : Measure (BrownianSheetIndex d → ℝ))] ^ n := by
            -- Proof comment: apply the centered Gaussian even-moment formula to the clipped
            -- increment.
            simpa [inc, coeff, n] using
              centeredGaussianEvenMoment_eq_factorialRatio_mul_variance_pow
                hincGaussian hMean n
    _ ≤ coeff * (((d : ℝ) * dist x y) ^ n) := by
          exact mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
    _ = coeff * ((d : ℝ) ^ n * dist x y ^ n) := by
          rw [mul_pow]
    _ = (coeff * (d : ℝ) ^ n) * dist x y ^ n := by
          ring
    _ = (((Nat.factorial (2 * (d + 1)) : ℝ) /
            (((2 : ℝ) ^ (d + 1)) * (Nat.factorial (d + 1) : ℝ))) *
          (d : ℝ) ^ (d + 1)) *
          dist x y ^ (d + 1) := by
            simp [coeff, n]

/-- Helper for Exercise 21.5.4: a real Gaussian random variable has integrable even powers of all
orders. -/
private theorem integrable_evenPow_of_hasGaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasGaussianLaw X μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ (2 * n)) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  cases n with
  | zero =>
      simp
  | succ n =>
      let p : ENNReal := (2 * Nat.succ n : ℕ)
      have hp_ne_top : p ≠ ⊤ := by
        simpa [p] using ENNReal.natCast_ne_top (2 * Nat.succ n)
      have hMem : MemLp X p μ := hX.memLp (p := p) hp_ne_top
      have hNorm : Integrable (fun ω ↦ ‖X ω‖ ^ (2 * Nat.succ n)) μ := by
        simpa using
          (MeasureTheory.MemLp.integrable_norm_pow
            (μ := μ) (f := X) (p := 2 * Nat.succ n)
            (hX.memLp (p := (2 * Nat.succ n : ℕ)) (by simpa [p] using hp_ne_top))
            (by simp))
      have hEq :
          (fun ω ↦ ‖X ω‖ ^ (2 * Nat.succ n)) =ᵐ[μ] fun ω ↦ X ω ^ (2 * Nat.succ n) := by
        -- Proof comment: an even power does not see the sign, so the norm power and the raw power
        -- coincide pointwise.
        filter_upwards with ω
        rw [Real.norm_eq_abs, pow_mul, pow_mul, sq_abs]
      exact hNorm.congr hEq

/-- Helper for Exercise 21.5.4: the clipped increment `lintegral` is exactly the `ENNReal.ofReal`
of the corresponding even moment. -/
private theorem brownianSheetClippedIncrement_lintegral_eq_ofReal_evenMoment
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ ω,
        edist (brownianSheetClippedProcess d x ω) (brownianSheetClippedProcess d y ω) ^
          (2 * ((d : NNReal) + (1 : NNReal)) : ℝ)
        ∂(μ : Measure (BrownianSheetIndex d → ℝ)) =
      ENNReal.ofReal
        (∫ ω,
          (brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω) ^
            (2 * (d + 1))
          ∂(μ : Measure (BrownianSheetIndex d → ℝ))) := by
  let inc : (BrownianSheetIndex d → ℝ) → ℝ := fun ω ↦
    brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω
  have hincGaussian :
      HasGaussianLaw inc (μ : Measure (BrownianSheetIndex d → ℝ)) := by
    -- Proof comment: a difference of two clipped Gaussian coordinates is still Gaussian.
    simpa [inc, brownianSheetClippedProcess] using
      hgauss.hasGaussianLaw_fun_sub (s := clipUnitCube x) (t := clipUnitCube y)
  have hIntegrable :
      Integrable (fun ω ↦ inc ω ^ (2 * (d + 1)))
        (μ : Measure (BrownianSheetIndex d → ℝ)) :=
    integrable_evenPow_of_hasGaussianLaw hincGaussian (d + 1)
  have hNonneg :
      0 ≤ᵐ[(μ : Measure (BrownianSheetIndex d → ℝ))] fun ω ↦ inc ω ^ (2 * (d + 1)) :=
    Filter.Eventually.of_forall fun ω ↦ by
      have hsq : 0 ≤ (inc ω ^ (d + 1)) ^ 2 := by
        positivity
      simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hsq
  have hAlpha :
      (2 * ((d : NNReal) + (1 : NNReal)) : ℝ) = (2 * (d + 1) : ℝ) := by
    norm_num
  calc
    ∫⁻ ω,
        edist (brownianSheetClippedProcess d x ω) (brownianSheetClippedProcess d y ω) ^
          (2 * ((d : NNReal) + (1 : NNReal)) : ℝ)
        ∂(μ : Measure (BrownianSheetIndex d → ℝ))
        =
          ∫⁻ ω,
            edist (brownianSheetClippedProcess d x ω) (brownianSheetClippedProcess d y ω) ^
              (2 * (d + 1) : ℕ)
            ∂(μ : Measure (BrownianSheetIndex d → ℝ)) := by
            refine lintegral_congr_ae ?_
            filter_upwards with ω
            let a := edist (brownianSheetClippedProcess d x ω) (brownianSheetClippedProcess d y ω)
            have hNat : a ^ (2 * (d + 1) : ℕ) = a ^ (2 * (d + 1) : ℝ) := by
              simpa using (ENNReal.rpow_natCast (x := a) (n := 2 * (d + 1))).symm
            rw [hNat]
            exact (congrArg (fun r : ℝ ↦ a ^ r) hAlpha).symm
    _ =
        ∫⁻ ω, ENNReal.ofReal (inc ω ^ (2 * (d + 1))) ∂(μ : Measure (BrownianSheetIndex d → ℝ)) := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          -- Proof comment: the even metric power is the absolute even polynomial increment.
          simpa [inc, edist_comm] using
            (realEdist_pow_even_eq_ofReal_sub_pow_even
              (a := brownianSheetClippedProcess d y ω)
              (b := brownianSheetClippedProcess d x ω)
              (k := d + 1))
    _ =
        ENNReal.ofReal
          (∫ ω, inc ω ^ (2 * (d + 1)) ∂(μ : Measure (BrownianSheetIndex d → ℝ))) := by
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntegrable hNonneg]
    _ =
        ENNReal.ofReal
          (∫ ω,
            (brownianSheetClippedProcess d x ω - brownianSheetClippedProcess d y ω) ^
              (2 * (d + 1))
            ∂(μ : Measure (BrownianSheetIndex d → ℝ))) := by
            rfl

/-- Helper for Exercise 21.5.4: a cube-subtype `edist` raised to a natural exponent is the
`ENNReal.ofReal` of the ambient Euclidean distance power. -/
private theorem euclideanClosedCube_edist_natCast_eq_ofReal_dist_pow
    {d : ℕ} (T : ℝ) (s t : euclideanClosedCube d T) (n : ℕ) :
    edist s t ^ (n : ℝ) =
      ENNReal.ofReal
        (dist (s : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^ n) := by
  -- Proof comment: the subtype metric is the ambient Euclidean metric, and `ENNReal` turns a
  -- natural `rpow` into an ordinary power.
  rw [ENNReal.rpow_natCast, edist_dist, ← ENNReal.ofReal_pow]
  · rw [Subtype.dist_eq]
  · exact dist_nonneg

/-- Helper for Exercise 21.5.4: the clipped Euclidean extension satisfies the cube-owner
Kolmogorov condition with the exponent pair needed for the Brownian-sheet continuity argument. -/
private theorem brownianSheetClippedProcess_isKolmogorovOnEuclideanClosedCube
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (hmean_zero : ∀ t : BrownianSheetIndex d,
      ∫ ω, brownianSheetCoordinateProcess d t ω ∂
        (μ : Measure (BrownianSheetIndex d → ℝ)) = 0)
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
        (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t)
    (T : NNReal) (_hT : (0 : NNReal) < T) :
    ∃ C : NNReal,
      IsKolmogorovProcessOnEuclideanClosedCube
        (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetClippedProcess d)
        T
        (2 * ((d : NNReal) + (1 : NNReal)))
        (1 : NNReal)
        C := by
  let coeff : ℝ :=
    ((Nat.factorial (2 * (d + 1)) : ℝ) /
      (((2 : ℝ) ^ (d + 1)) * (Nat.factorial (d + 1) : ℝ))) *
      (d : ℝ) ^ (d + 1)
  let C : NNReal := Real.toNNReal coeff
  refine ⟨C, ?_⟩
  refine IsKolmogorovProcess.mk_of_secondCountableTopology ?_ ?_ ?_ ?_
  · intro s
    -- Proof comment: each cube point still evaluates one fixed clipped Brownian-sheet coordinate.
    simpa [brownianSheetClippedProcess] using
      measurable_brownianSheetCoordinateProcess
        (clipUnitCube (s : EuclideanSpace ℝ (Fin d)))
  · intro s t
    have hMoment :=
      brownianSheetClippedIncrement_evenMoment_bound
        (d := d) μ hgauss hmean_zero hcov
        (s : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d))
    have hCoeff_nonneg : 0 ≤ coeff := by
      positivity
    -- Proof comment: rewrite the left side to the real even moment, apply the explicit bound, and
    -- then convert the ambient Euclidean distance back to the cube subtype metric once.
    calc
      ∫⁻ ω,
          edist (brownianSheetClippedProcess d s ω) (brownianSheetClippedProcess d t ω) ^
            (2 * ((d : NNReal) + (1 : NNReal)) : ℝ)
          ∂(μ : Measure (BrownianSheetIndex d → ℝ))
          =
            ENNReal.ofReal
              (∫ ω,
                (brownianSheetClippedProcess d (s : EuclideanSpace ℝ (Fin d)) ω -
                    brownianSheetClippedProcess d (t : EuclideanSpace ℝ (Fin d)) ω) ^
                  (2 * (d + 1))
                ∂(μ : Measure (BrownianSheetIndex d → ℝ))) := by
              simpa using
                brownianSheetClippedIncrement_lintegral_eq_ofReal_evenMoment
                  (d := d) μ hgauss
                  (s : EuclideanSpace ℝ (Fin d))
                  (t : EuclideanSpace ℝ (Fin d))
      _ ≤
          ENNReal.ofReal
            (coeff *
              dist (s : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^ (d + 1)) := by
            exact ENNReal.ofReal_le_ofReal hMoment
      _ = (C : ENNReal) *
            edist s t ^ ((d : ℝ) + 1) := by
            rw [ENNReal.ofReal_mul hCoeff_nonneg]
            have hC : (C : ENNReal) = ENNReal.ofReal coeff := by
              change ((coeff.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal coeff
              rw [show coeff.toNNReal = ⟨coeff, hCoeff_nonneg⟩ by
                apply NNReal.eq
                simp [Real.toNNReal_of_nonneg hCoeff_nonneg]]
              exact (ENNReal.ofReal_eq_coe_nnreal hCoeff_nonneg).symm
            rw [hC]
            have hdist :
                ENNReal.ofReal
                    (dist (s : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
                      (d + 1)) =
                  edist s t ^ ((d : ℝ) + 1) := by
              simpa using
                (euclideanClosedCube_edist_natCast_eq_ofReal_dist_pow
                  (d := d) (T := (T : ℝ)) (s := s) (t := t) (n := d + 1)).symm
            rw [hdist]
  · have hpos : (0 : ℝ) < (2 : ℝ) * ((d : ℝ) + 1) := by
      positivity
    simpa [Nat.cast_add, Nat.cast_mul, two_mul, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using hpos
  · have hpos : (0 : ℝ) < (d : ℝ) + 1 := by
      positivity
    simpa using hpos

/-- Helper for Exercise 21.5.4: restricting the clipped ambient process along the cube embedding
recovers the original sheet-index coordinate process. -/
private theorem brownianSheetClippedProcess_sheetIndexToEuclidean
    {d : ℕ} (t : BrownianSheetIndex d) :
    brownianSheetClippedProcess d (sheetIndexToEuclidean t) =
      brownianSheetCoordinateProcess d t := by
  -- Proof comment: clipping does nothing on points that already lie in `[0,1]^d`.
  funext ω
  simp [brownianSheetClippedProcess, brownianSheetCoordinateProcess, clipUnitCube_coe_eq]

/-- Helper for Exercise 21.5.4: restricting the Euclidean locally Hölder version back to
`BrownianSheetIndex d` yields a modification with almost surely continuous sample paths. -/
private theorem brownianSheetRestriction_of_locallyHolderVersion
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (γIoc : Set.Ioc (0 : NNReal) (1 : NNReal))
    (Y : EuclideanSpace ℝ (Fin d) → (BrownianSheetIndex d → ℝ) → ℝ)
    (hmod :
      AreModifications
        (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetClippedProcess d)
        Y)
    (hHolder : HasLocallyHolderPaths (γIoc : NNReal) Y) :
    let W' : BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ :=
      fun t ω ↦ Y (sheetIndexToEuclidean t) ω
    AreModifications
        (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetCoordinateProcess d)
        W' ∧
      HasAlmostSurelyContinuousPaths
        (μ : Measure (BrownianSheetIndex d → ℝ))
        W' := by
  let W' : BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ :=
    fun t ω ↦ Y (sheetIndexToEuclidean t) ω
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: on actual sheet-index points, clipping is the identity, so the Euclidean
    -- modification property restricts directly back to the original coordinate process.
    filter_upwards [hmod (sheetIndexToEuclidean t)] with ω hω
    simpa [W', brownianSheetClippedProcess_sheetIndexToEuclidean (d := d) t] using hω
  · -- Proof comment: every ambient path of `Y` is locally Hölder, hence continuous; composing
    -- with the continuous cube embedding gives continuity on `BrownianSheetIndex d`.
    filter_upwards with ω
    have hcontAmbient : Continuous (fun z : EuclideanSpace ℝ (Fin d) ↦ Y z ω) :=
      continuous_of_locallyHolderWith (γ := γIoc) (hHolder ω)
    simpa [HasAlmostSurelyContinuousPaths, processPath, W'] using
      hcontAmbient.comp continuous_sheetIndexToEuclidean

/-- Helper for Exercise 21.5.4: once the canonical coordinate process has the Brownian-sheet
Gaussian law and a continuous modification, the Brownian-sheet structure is immediate. -/
theorem isBrownianSheet_of_gaussianCovariance_and_continuousModification
    {d : ℕ} {μ : Measure (BrownianSheetIndex d → ℝ)}
    (hgauss : IsGaussianProcess (brownianSheetCoordinateProcess d) μ)
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t; μ] =
        brownianSheetCovariance s t)
    (hmod :
      ∃ W' : BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ,
        AreModifications μ (brownianSheetCoordinateProcess d) W' ∧
          HasAlmostSurelyContinuousPaths μ W') :
    IsBrownianSheet d μ (brownianSheetCoordinateProcess d) := by
  -- Proof comment: the class fields are exactly the Gaussian law, the covariance identity, and the
  -- existence of a continuous modification.
  refine
    { toIsGaussianProcess := hgauss
      covariance_eq := hcov
      exists_continuous_modification := hmod }

/-- Helper for Exercise 21.5.4: a centered Gaussian Brownian-sheet coordinate process with the
target covariance kernel admits a continuous modification. -/
theorem exists_brownianSheetCoordinateContinuousModification_of_meanZero
    {d : ℕ} (μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ))
    (hgauss : IsGaussianProcess
      (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)))
    (hmean_zero : ∀ t : BrownianSheetIndex d,
      ∫ ω, brownianSheetCoordinateProcess d t ω ∂
        (μ : Measure (BrownianSheetIndex d → ℝ)) = 0)
    (hcov : ∀ s t : BrownianSheetIndex d,
      cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
        (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t) :
    ∃ W' : BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ,
      AreModifications (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetCoordinateProcess d) W' ∧
        HasAlmostSurelyContinuousPaths (μ : Measure (BrownianSheetIndex d → ℝ)) W' := by
  -- Route correction: covariance alone is not enough for continuity transfer, since the mean can
  -- be changed by a discontinuous deterministic function without changing the covariance.
  let γ : NNReal := (4 * ((d : NNReal) + (1 : NNReal)))⁻¹
  have hα : 0 < 2 * ((d : NNReal) + (1 : NNReal)) := by
    positivity
  have hβ : 0 < (1 : NNReal) := by
    positivity
  have hγ₀ : 0 < γ := by
    positivity
  have hγ_lt :
      γ < (1 : NNReal) / (2 * ((d : NNReal) + (1 : NNReal))) := by
    have hγ_real :
        ((γ : NNReal) : ℝ) <
          (((1 : NNReal) / (2 * ((d : NNReal) + (1 : NNReal))) : NNReal) : ℝ) := by
      simp [γ]
      have hx : 0 < (((d : NNReal) + (1 : NNReal) : NNReal) : ℝ) := by
        positivity
      field_simp [hx.ne']
      nlinarith
    exact_mod_cast hγ_real
  have hγ_le_one :
      γ ≤ (1 : NNReal) := by
    have hγ_real : ((γ : NNReal) : ℝ) ≤ (1 : ℝ) := by
      simp [γ]
      have hx : 0 < (((d : NNReal) + (1 : NNReal) : NNReal) : ℝ) := by
        positivity
      field_simp [hx.ne']
      nlinarith
    exact_mod_cast hγ_real
  let γIoc : Set.Ioc (0 : NNReal) (1 : NNReal) := ⟨γ, ⟨hγ₀, hγ_le_one⟩⟩
  rcases
      exists_locallyHolderWith_version_of_euclidean_moment_bound
        (μ := (μ : Measure (BrownianSheetIndex d → ℝ)))
        (X := brownianSheetClippedProcess d)
        (hα := hα)
        (hβ := hβ)
        (hγ₀ := hγ₀)
        (hγ := hγ_lt)
        (hMoment :=
          brownianSheetClippedProcess_isKolmogorovOnEuclideanClosedCube
            (d := d) μ hgauss hmean_zero hcov) with
    ⟨Y, hmod, hHolder⟩
  -- Proof comment: the Euclidean Hölder version restricts along the cube embedding to the
  -- original sheet-indexed process and therefore yields an almost surely continuous modification.
  refine ⟨fun t ω ↦ Y (sheetIndexToEuclidean t) ω, ?_⟩
  simpa [γIoc] using
    (brownianSheetRestriction_of_locallyHolderVersion
      (d := d) μ γIoc Y hmod hHolder)

-- Proof sketch: apply the continuity criterion from Remark 21.7 to the Gaussian process from
-- part (1), using the Brownian-sheet covariance kernel to obtain the required moment bounds, and
-- then package the Gaussian, covariance, and path-regularity clauses into `IsBrownianSheet`.
/-- Part (2): the Brownian-sheet coordinate process on `[0,1]^d` carries a Brownian-sheet law on
path space. -/
theorem exists_brownianSheetContinuousModification (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsBrownianSheet d (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetCoordinateProcess d) := by
  -- Proof comment: use the richer centered path law directly, since the continuity bridge needs
  -- the mean-zero input in addition to Gaussianity and the covariance identity.
  rcases exists_centeredBrownianSheetGaussianPathLaw d with ⟨μ, hgauss, hmean_zero, hcov⟩
  refine ⟨μ, ?_⟩
  exact
    isBrownianSheet_of_gaussianCovariance_and_continuousModification
      hgauss hcov
      (exists_brownianSheetCoordinateContinuousModification_of_meanZero
        (d := d) μ hgauss hmean_zero hcov)

end ProbabilityTheory
