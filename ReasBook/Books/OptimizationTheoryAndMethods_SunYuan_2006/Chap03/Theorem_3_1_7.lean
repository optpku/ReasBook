/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.LiminfLimsup
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_1_2

open Filter

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * `IsSteepestDescentMethod` is the Chapter 3 owner for steepest-descent runs, and
--   `Theorem_3_1_6` already refines local convergence further to direct iterate/step-size data.
-- * `IsStationaryPoint` is the project owner for genuine stationary-point data.
-- * `IsExactLineSearchStepOnNonnegativeRay` is the Chapter 2 owner for exact line search on the
--   nonnegative steepest-descent ray.
-- * `IsSteepestDescentSequence` is the Chapter 3 owner for exact-line-search steepest-descent
--   iterates with their canonical updates.
-- * `hessianAt` / `hessianQuadraticAt` from `Definition_3_5_1` are the project Hessian owners
--   for Euclidean problems.
-- * The source-facing local `C²` and quadratic-form bounds are the primitive neighborhood data,
--   and the spectral statements below are bridge lemmas from those bounds to `hessianAt`.
--
-- Triage:
-- * source-facing: asymptotic contraction of a steepest-descent iterate sequence;
-- * core/canonical: `steepestDescentDirection`, `steepestDescentStep`,
--   `IsExactLineSearchStepOnNonnegativeRay`, and the Hessian owners above;
-- * bridge/view removed here: the Chapter 2 wrapper
--   `GeneralUnconstrainedOptimizationMethod` plus a separate direction-equality hypothesis.
--
-- Primitive data are therefore the iterate sequence `x`, the step sizes `α`, and the source-facing
-- Chapter 3 owner `IsSteepestDescentSequence f x α`.

variable {f : Point → ℝ} {xStar : Point} {x : ℕ → Point} {α : ℕ → ℝ}

/-- The objective-gap ratio attached to a steepest-descent sequence. -/
def steepestDescentContractionFactor
    (f : Point → ℝ) (xStar : Point) (x : ℕ → Point) (k : ℕ) : ℝ :=
  (f (x (k + 1)) - f xStar) / (f (x k) - f xStar)

/-- `steepestDescentContractionFactor` is the ratio of two consecutive objective gaps. -/
theorem steepestDescentContractionFactor_def
    (f : Point → ℝ) (xStar : Point) (x : ℕ → Point) (k : ℕ) :
    steepestDescentContractionFactor f xStar x k =
      (f (x (k + 1)) - f xStar) / (f (x k) - f xStar) := rfl

/-- Helper for Chapter03 Theorem 3.1.7: a local `C²` neighborhood can be shrunk to a concrete
metric ball centered at `xStar`. -/
lemma exists_contDiffOn_ball_of_nhds
    {f : Point → ℝ} {xStar : Point}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s) :
    ∃ ε > 0, ContDiffOn ℝ 2 f (Metric.ball xStar ε) := by
  rcases hC2 with ⟨s, hsNhd, hsC2⟩
  rcases Metric.mem_nhds_iff.mp hsNhd with ⟨ε, hε, hBallSubset⟩
  -- Shrink the abstract neighborhood from the source hypothesis to a metric ball.
  exact ⟨ε, hε, hsC2.mono hBallSubset⟩

/-- Helper for Chapter03 Theorem 3.1.7: once ball-wise quadratic Hessian bounds are known, they
package directly into the canonical Chapter 1 lower and upper Hessian-bound owners. -/
lemma hasHessianBoundsOn_ball_of_neighborhoodHessianBounds
    {f : Point → ℝ} {xStar : Point} {ε m M : ℝ}
    (hHessian :
      ∀ ⦃x : Point⦄, x ∈ Metric.ball xStar ε → ∀ y : Point,
        m * ‖y‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ (2 : ℕ)) :
    HasHessianLowerBoundOn (Metric.ball xStar ε) f m ∧
      HasHessianUpperBoundOn (Metric.ball xStar ε) f M := by
  constructor
  · intro x hx y
    -- The lower owner is just the first component of the pointwise pair.
    exact (hHessian hx y).1
  · intro x hx y
    -- The upper owner is the second component of the same pointwise pair.
    exact (hHessian hx y).2

/-- Helper for Chapter03 Theorem 3.1.7: under a local `C²` hypothesis, the bilinear Hessian
operator matches the second iterated Fréchet derivative after pairing with a test vector. -/
lemma inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
    {f : Point → ℝ} {x y z : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    inner ℝ z (hessianAt f x y) = (iteratedFDeriv ℝ 2 f x) ![y, z] := by
  let e : StrongDual ℝ Point ≃L[ℝ] Point :=
    (InnerProductSpace.toDual ℝ Point).symm.toContinuousLinearEquiv
  -- Differentiate `fderiv ℝ f` once, then transport through the Riesz isomorphism defining
  -- `gradient`.
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hgrad := by
    simpa [gradient, Function.comp, e] using ((e.hasFDerivAt).comp x hfd)
  have hgrad' :
      fderiv ℝ (gradient f) x = e.toContinuousLinearMap ∘SL fderiv ℝ (fderiv ℝ f) x :=
    (show HasFDerivAt (gradient f) _ x from hgrad).fderiv
  have hyEq :
      hessianAt f x y = e ((fderiv ℝ (fderiv ℝ f) x) y) := by
    simpa [hessianAt, e] using congrArg (fun T : Point →L[ℝ] Point => T y) hgrad'
  calc
    inner ℝ z (hessianAt f x y) = inner ℝ z (e ((fderiv ℝ (fderiv ℝ f) x) y)) := by
      rw [hyEq]
    _ = ((fderiv ℝ (fderiv ℝ f) x) y) z := by
      rw [real_inner_comm]
      change
        inner ℝ (((InnerProductSpace.toDual ℝ Point).symm) ((fderiv ℝ (fderiv ℝ f) x) y)) z =
          ((fderiv ℝ (fderiv ℝ f) x) y) z
      simp
    _ = (iteratedFDeriv ℝ 2 f x) ![y, z] := by
      symm
      exact iteratedFDeriv_two_apply f x ![y, z]

/-- Helper for Chapter03 Theorem 3.1.7: on a `C²` point, the quadratic Hessian owner agrees
with evaluating the second iterated Fréchet derivative twice on the same direction. -/
lemma hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
    {f : Point → ℝ} {x y : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    hessianQuadraticAt f x y = (iteratedFDeriv ℝ 2 f x) ![y, y] := by
  -- This is the diagonal specialization of the bilinear bridge above.
  exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt hC2

/-- Helper for Chapter03 Theorem 3.1.7: at a `C²` point, the Hessian operator is symmetric, so
its Rayleigh quotient and extremal eigenvalue API apply without unfolding `gradient` again. -/
lemma hessianAt_toLinearMap_isSymmetric_of_contDiffAt
    {f : Point → ℝ} {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    ((hessianAt f x).toLinearMap).IsSymmetric := by
  intro y z
  -- Transfer symmetry from the second iterated derivative through the Hessian bridge.
  have hswap :
      (iteratedFDeriv ℝ 2 f x) ![y, z] = (iteratedFDeriv ℝ 2 f x) ![z, y] :=
    (hC2.isSymmSndFDerivAt (n := (2 : WithTop ℕ∞)) (by simp)).iteratedFDeriv_cons
      (x := x) (v := y) (w := z)
  calc
    inner ℝ (hessianAt f x y) z = inner ℝ z (hessianAt f x y) := by
      rw [real_inner_comm]
    _ = (iteratedFDeriv ℝ 2 f x) ![y, z] :=
      inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
        (f := f) (x := x) (y := y) (z := z) hC2
    _ = (iteratedFDeriv ℝ 2 f x) ![z, y] := hswap
    _ = inner ℝ y (hessianAt f x z) := by
      exact
        (inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
          (f := f) (x := x) (y := z) (z := y) hC2).symm

/-- Helper for Chapter03 Theorem 3.1.7: the canonical Rayleigh quotient of the Hessian operator is
the Hessian quadratic form divided by the squared norm of the testing direction. -/
lemma rayleighQuotient_hessianAt_eq_diag_ratio
    {f : Point → ℝ} {x y : Point} :
    ContinuousLinearMap.rayleighQuotient (hessianAt f x) y =
      hessianQuadraticAt f x y / ‖y‖ ^ (2 : ℕ) := by
  -- Unfold the canonical quotient once and rewrite it back to the project Hessian owner.
  simp [ContinuousLinearMap.rayleighQuotient, hessianQuadraticAt,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]

/-- Helper for Chapter03 Theorem 3.1.7: once the least and greatest Hessian eigenvalues are known,
every nonzero Rayleigh quotient lies between them. -/
lemma rayleigh_quotient_hessianAt_mem_Icc_of_eigen_endpoints
    [Nontrivial Point]
    {f : Point → ℝ} {xStar : Point} {lambdaMin lambdaMax : ℝ}
    (hSymm : ((hessianAt f xStar).toLinearMap).IsSymmetric)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (u : Point)
    (hu : u ≠ 0) :
    lambdaMin ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u ∧
      ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u ≤ lambdaMax := by
  have hBddBelow :
      BddBelow
        (Set.range
          (fun x : {x : Point // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x)) := by
    refine ⟨-‖hessianAt f xStar‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The Rayleigh quotient is bounded below by `-‖T‖` because its absolute value is at most `‖T‖`.
    have hv := (hessianAt f xStar).rayleighQuotient_le_norm v
    have habs := abs_le.mp hv
    linarith
  have hBddAbove :
      BddAbove
        (Set.range
          (fun x : {x : Point // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x)) := by
    refine ⟨‖hessianAt f xStar‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The same norm control gives a uniform upper bound on the quotient family.
    exact le_trans (le_abs_self _) ((hessianAt f xStar).rayleighQuotient_le_norm v)
  have hrqMinEigen :
      Module.End.HasEigenvalue
        (hessianAt f xStar).toLinearMap
        (⨅ x : {x : Point // x ≠ 0},
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x) := by
    -- The symmetric-operator extremal Rayleigh theorem packages the infimum as an eigenvalue.
    simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply] using
      (LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
        (T := (hessianAt f xStar).toLinearMap) hSymm)
  have hrqMaxEigen :
      Module.End.HasEigenvalue
        (hessianAt f xStar).toLinearMap
        (⨆ x : {x : Point // x ≠ 0},
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x) := by
    -- The same theorem packages the supremum as the top eigenvalue witness.
    simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply] using
      (LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional
        (T := (hessianAt f xStar).toLinearMap) hSymm)
  constructor
  · -- Compare the current quotient with the infimal Rayleigh value, then use the least eigenvalue.
    calc
      lambdaMin ≤
          ⨅ x : {x : Point // x ≠ 0},
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x := hLambdaMin.2 hrqMinEigen
      _ ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u := ciInf_le hBddBelow ⟨u, hu⟩
  · -- Compare the current quotient with the supremal Rayleigh value, then use the top eigenvalue.
    calc
      ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u ≤
          ⨆ x : {x : Point // x ≠ 0},
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x := le_ciSup hBddAbove ⟨u, hu⟩
      _ ≤ lambdaMax := hLambdaMax.2 hrqMaxEigen

/-- Helper for Chapter03 Theorem 3.1.7: positive definiteness of the Hessian quadratic form at
`xStar` yields uniform lower and upper diagonal Hessian bounds on a sufficiently small ball when
the direction is normalized to the unit sphere. -/
lemma exists_uniform_unitSphere_hessian_band_of_contDiff_posDef
    {f : Point → ℝ} {xStar : Point}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y) :
    ∃ ε m M : ℝ,
      0 < ε ∧
        0 < m ∧
          m ≤ M ∧
            ContDiffOn ℝ 2 f (Metric.ball xStar ε) ∧
              ∀ ⦃z : Point⦄, z ∈ Metric.ball xStar ε → ∀ u ∈ Metric.sphere (0 : Point) 1,
                m ≤ (iteratedFDeriv ℝ 2 f z) ![u, u] ∧
                  (iteratedFDeriv ℝ 2 f z) ![u, u] ≤ M := by
  by_cases hPoint : Subsingleton Point
  · rcases exists_contDiffOn_ball_of_nhds hC2 with ⟨ε, hε, hBallC2⟩
    refine ⟨ε, 1, 1, hε, zero_lt_one, le_rfl, hBallC2, ?_⟩
    intro z hz u hu
    exfalso
    have hu_zero : u = 0 := hPoint.elim _ _
    have : ‖u‖ = (1 : ℝ) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hu
    simp [hu_zero] at this
  · letI : Nontrivial Point := not_subsingleton_iff_nontrivial.mp hPoint
    rcases exists_contDiffOn_ball_of_nhds hC2 with ⟨ε0, hε0, hBallC2⟩
    have hContDiffAt : ContDiffAt ℝ 2 f xStar :=
      hBallC2.contDiffAt (Metric.ball_mem_nhds xStar hε0)
    let A0 := iteratedFDeriv ℝ 2 f xStar
    let q : Point → ℝ := fun u ↦ A0 ![u, u]
    -- First get a positive minimum of the quadratic form on the unit sphere.
    have hq_cont : Continuous q := by
      fun_prop
    have hsphere_compact : IsCompact (Metric.sphere (0 : Point) 1) := isCompact_sphere _ _
    have hsphere_nonempty : (Metric.sphere (0 : Point) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨u0, hu0, hu0min⟩ :=
      hsphere_compact.exists_isMinOn hsphere_nonempty hq_cont.continuousOn
    have hu0_ne : u0 ≠ 0 := by
      intro hu0_zero
      have : ‖u0‖ = 0 := by simpa [hu0_zero]
      have hu0_norm : ‖u0‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hu0
      linarith
    let m0 : ℝ := q u0
    have hm0_pos : 0 < m0 := by
      -- Convert the source-facing positive-definite hypothesis to the iterated-derivative surface.
      rw [show m0 = (iteratedFDeriv ℝ 2 f xStar) ![u0, u0] by rfl]
      exact
        (hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt hContDiffAt).symm ▸
          hPosDef u0 hu0_ne
    have hm0_lower : ∀ u ∈ Metric.sphere (0 : Point) 1, m0 ≤ q u := by
      intro u hu
      exact hu0min hu
    -- Then use continuity in operator norm to keep the nearby Hessians close to the one at `xStar`.
    have hm_half_pos : 0 < m0 / 2 := by positivity
    have hcontA : ContinuousAt (iteratedFDeriv ℝ 2 f) xStar :=
      hContDiffAt.continuousAt_iteratedFDeriv (by norm_num)
    have hA_ball_lower :
        (iteratedFDeriv ℝ 2 f) ⁻¹' Metric.ball A0 (m0 / 2) ∈ nhds xStar :=
      hcontA.preimage_mem_nhds (Metric.ball_mem_nhds A0 hm_half_pos)
    have hA_ball_upper :
        (iteratedFDeriv ℝ 2 f) ⁻¹' Metric.ball A0 1 ∈ nhds xStar :=
      hcontA.preimage_mem_nhds (Metric.ball_mem_nhds A0 zero_lt_one)
    rcases Metric.mem_nhds_iff.mp hA_ball_lower with ⟨δ1, hδ1, hδ1ball⟩
    rcases Metric.mem_nhds_iff.mp hA_ball_upper with ⟨δ2, hδ2, hδ2ball⟩
    let ε : ℝ := min ε0 (min δ1 δ2)
    let m : ℝ := m0 / 2
    let M0 : ℝ := ‖A0‖ + 1
    let M : ℝ := max M0 m
    refine ⟨ε, m, M, ?_⟩
    refine ⟨by
        dsimp [ε]
        positivity, by
        dsimp [m]
        positivity, by
        dsimp [M, M0]
        exact le_max_right _ _, ?_, ?_⟩
    · -- Keep the original `C²` ball while shrinking the radius to match the operator-norm control.
      exact hBallC2.mono (Metric.ball_subset_ball (min_le_left _ _))
    · intro z hz u hu
      have hu_norm : ‖u‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hu
      have hzδ : z ∈ Metric.ball xStar (min δ1 δ2) :=
        Metric.ball_subset_ball (min_le_right _ _) hz
      have hzδ1 : z ∈ Metric.ball xStar δ1 :=
        Metric.ball_subset_ball (min_le_left _ _) hzδ
      have hzδ2 : z ∈ Metric.ball xStar δ2 :=
        Metric.ball_subset_ball (min_le_right _ _) hzδ
      have hzA_lower :
          ‖iteratedFDeriv ℝ 2 f z - A0‖ < m0 / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm, A0] using hδ1ball hzδ1
      have hzA_upper :
          ‖iteratedFDeriv ℝ 2 f z - A0‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, A0] using hδ2ball hzδ2
      have hOpLower :
          ‖(iteratedFDeriv ℝ 2 f z - A0) ![u, u]‖ ≤ ‖iteratedFDeriv ℝ 2 f z - A0‖ := by
        have hle := (iteratedFDeriv ℝ 2 f z - A0).le_opNorm ![u, u]
        simpa [hu_norm] using hle
      have habs :
          |(iteratedFDeriv ℝ 2 f z) ![u, u] - A0 ![u, u]| < m0 / 2 := by
        have hzA' :
            ‖(iteratedFDeriv ℝ 2 f z - A0) ![u, u]‖ < m0 / 2 :=
          lt_of_le_of_lt hOpLower hzA_lower
        simpa [A0, Real.norm_eq_abs] using hzA'
      have hA0_lower : m0 ≤ A0 ![u, u] := hm0_lower u hu
      have hLower :
          m ≤ (iteratedFDeriv ℝ 2 f z) ![u, u] := by
        dsimp [m]
        have hdiff_lower :
            -(m0 / 2) < (iteratedFDeriv ℝ 2 f z) ![u, u] - A0 ![u, u] :=
          (abs_lt.mp habs).1
        linarith
      have hOpUpper :
          |(iteratedFDeriv ℝ 2 f z) ![u, u]| ≤ ‖iteratedFDeriv ℝ 2 f z‖ := by
        have hle := (iteratedFDeriv ℝ 2 f z).le_opNorm ![u, u]
        simpa [Real.norm_eq_abs, hu_norm] using hle
      have hNormUpper :
          ‖iteratedFDeriv ℝ 2 f z‖ ≤ M0 := by
        have htri :
            ‖iteratedFDeriv ℝ 2 f z‖ ≤ ‖iteratedFDeriv ℝ 2 f z - A0‖ + ‖A0‖ := by
          calc
            ‖iteratedFDeriv ℝ 2 f z‖ = ‖(iteratedFDeriv ℝ 2 f z - A0) + A0‖ := by
              abel_nf
            _ ≤ ‖iteratedFDeriv ℝ 2 f z - A0‖ + ‖A0‖ := norm_add_le _ _
        dsimp [M0]
        linarith
      have hUpper :
          (iteratedFDeriv ℝ 2 f z) ![u, u] ≤ M := by
        dsimp [M]
        exact le_trans (le_trans (le_abs_self _) hOpUpper) (le_trans hNormUpper (le_max_left _ _))
      exact ⟨hLower, hUpper⟩

/-- If local `C²` Hessian bounds are available near `xStar`, then any nonzero objective gap
`f (x k) - f xStar` is positive. This is the source-facing positivity statement from which the
contraction-factor denominator positivity is derived on the intended ratio domain. -/
theorem steepestDescentContractionFactor_denominator_pos
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    {ε m M : ℝ}
    (hStationary : IsStationaryPoint f xStar)
    (hε : 0 < ε)
    (hm : 0 < m)
    (hmM : m ≤ M)
    (hC2 : ContDiffOn ℝ 2 f (Metric.ball xStar ε))
    (hHessian :
      ∀ ⦃x : Point⦄, x ∈ Metric.ball xStar ε → ∀ y : Point,
        m * ‖y‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ (2 : ℕ))
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (k : ℕ)
    (hGapNe : f (x k) ≠ f xStar) :
    0 < f (x k) - f xStar := by
  -- The lower Hessian bound at `xStar` upgrades stationarity to a strict local minimum.
  have hxStar_mem : xStar ∈ Metric.ball xStar ε := Metric.mem_ball_self hε
  have hContDiffAt : ContDiffAt ℝ 2 f xStar :=
    hC2.contDiffAt (Metric.ball_mem_nhds xStar hε)
  have hPosDefAt :
      ∀ y : Point, y ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f xStar) ![y, y] := by
    intro y hy
    exact lt_of_lt_of_le
      (mul_pos hm (pow_pos (norm_pos_iff.mpr hy) 2))
      (hHessian hxStar_mem y).1
  have hStrictMin : IsStrictLocalMin f xStar :=
    isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos
      f xStar hContDiffAt hStationary hPosDefAt
  have hEventuallyGe : ∀ᶠ n in atTop, f xStar ≤ f (x n) := by
    exact hx.eventually hStrictMin.isLocalMin
  have hAntitone : Antitone (fun n : ℕ ↦ f (x n)) :=
    steepestDescent_value_antitone f x α hSeq
  have hGapNonneg : 0 ≤ f (x k) - f xStar := by
    by_contra hneg
    have hkLt : f (x k) < f xStar := by
      linarith
    rcases Filter.mem_atTop_sets.mp hEventuallyGe with ⟨N, hN⟩
    have hGeAtMax : f xStar ≤ f (x (max N k)) := hN (max N k) (le_max_left N k)
    have hLtAtMax : f (x (max N k)) < f xStar := by
      exact lt_of_le_of_lt (hAntitone (le_max_right N k)) hkLt
    exact not_lt_of_ge hGeAtMax hLtAtMax
  rcases lt_or_eq_of_le hGapNonneg with hGapPos | hGapEq
  · exact hGapPos
  · exact False.elim (hGapNe (sub_eq_zero.mp hGapEq))

/-- Local `C²` regularity near a stationary point and positivity of the Hessian quadratic form at
`xStar` produce explicit neighborhood bounds `m` and `M` for the Theorem 3.1.6/3.1.7 surface. -/
theorem exists_neighborhoodHessianBounds_of_contDiff_posDef
    {f : Point → ℝ} {xStar : Point}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y) :
    ∃ ε m M : ℝ,
      0 < ε ∧
        0 < m ∧
          m ≤ M ∧
            ContDiffOn ℝ 2 f (Metric.ball xStar ε) ∧
              ∀ ⦃x : Point⦄, x ∈ Metric.ball xStar ε → ∀ y : Point,
                m * ‖y‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
                  (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ (2 : ℕ) := by
  -- Route correction: first control the Hessian diagonals on the unit sphere, then rescale an
  -- arbitrary direction back from its normalized representative.
  rcases exists_uniform_unitSphere_hessian_band_of_contDiff_posDef hC2 hPosDef with
    ⟨ε, m, M, hε, hm, hmM, hBallC2, hSphereBand⟩
  refine ⟨ε, m, M, hε, hm, hmM, hBallC2, ?_⟩
  intro x hx y
  by_cases hy : y = 0
  · -- The zero direction has vanishing quadratic term, so both inequalities are immediate.
    subst hy
    have hzero : (iteratedFDeriv ℝ 2 f x) ![(0 : Point), 0] = 0 := by
      simp
    constructor <;> simpa [hzero]
  · let u : Point := ‖y‖⁻¹ • y
    have hy_norm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hu_sphere : u ∈ Metric.sphere (0 : Point) 1 := by
      simp [u, hy_norm_ne, norm_smul]
    have hxu : m ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] ∧ (iteratedFDeriv ℝ 2 f x) ![u, u] ≤ M :=
      hSphereBand hx u hu_sphere
    have hy_expand : y = ‖y‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hy_norm_ne, one_smul]
    have hScale :
        (iteratedFDeriv ℝ 2 f x) ![y, y] =
          ‖y‖ ^ (2 : ℕ) * (iteratedFDeriv ℝ 2 f x) ![u, u] := by
      -- Evaluate the multilinear map on the normalized direction and then rescale.
      have hyy : (![y, y] : Fin 2 → Point) = fun _ : Fin 2 ↦ ‖y‖ • u := by
        ext i
        fin_cases i <;> simpa using hy_expand
      have huu : (![u, u] : Fin 2 → Point) = fun _ : Fin 2 ↦ u := by
        ext i
        fin_cases i <;> rfl
      have hmap :
          (iteratedFDeriv ℝ 2 f x) ![y, y] =
            ‖y‖ ^ (2 : ℕ) * (iteratedFDeriv ℝ 2 f x) ![u, u] := by
        simpa [hyy, huu] using
          (iteratedFDeriv ℝ 2 f x).map_smul_univ (fun _ : Fin 2 ↦ ‖y‖) (fun _ ↦ u)
      exact hmap
    constructor
    · -- Multiply the unit-sphere lower bound by `‖y‖²` and rewrite back to the original vector.
      have hnonneg : 0 ≤ ‖y‖ ^ (2 : ℕ) := by positivity
      calc
        m * ‖y‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) * m := by ring
        _ ≤ ‖y‖ ^ (2 : ℕ) * (iteratedFDeriv ℝ 2 f x) ![u, u] :=
          mul_le_mul_of_nonneg_left hxu.1 hnonneg
        _ = (iteratedFDeriv ℝ 2 f x) ![y, y] := by rw [hScale]
    · -- The same rescaling transports the unit-sphere upper bound.
      have hnonneg : 0 ≤ ‖y‖ ^ (2 : ℕ) := by positivity
      calc
        (iteratedFDeriv ℝ 2 f x) ![y, y] = ‖y‖ ^ (2 : ℕ) * (iteratedFDeriv ℝ 2 f x) ![u, u] := hScale
        _ ≤ ‖y‖ ^ (2 : ℕ) * M := mul_le_mul_of_nonneg_left hxu.2 hnonneg
        _ = M * ‖y‖ ^ (2 : ℕ) := by ring

/-- The Chapter 3 source setup implies positivity of any nonzero objective gap
`f (x k) - f xStar`, so this companion supplies the ratio-domain hypothesis needed by the
labeled contraction-factor statements. -/
theorem steepestDescentContractionFactor_denominator_pos_of_sourceHypotheses
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (k : ℕ)
    (hGapNe : f (x k) ≠ f xStar) :
    0 < f (x k) - f xStar := by
  -- Package the source hypotheses into the local Hessian bounds used by the quantitative proof.
  rcases exists_neighborhoodHessianBounds_of_contDiff_posDef hC2 hPosDef with
    ⟨ε, m, M, hε, hm, hmM, hBallC2, hBallHessian⟩
  exact steepestDescentContractionFactor_denominator_pos
    x α hStationary hε hm hmM hBallC2 hBallHessian hSeq hx k hGapNe

/-- Chapter03 Theorem 3.1.7 (1): assume `f` is `C²` near `xStar`, `xStar` is stationary, the
Hessian at `xStar` is positive definite, and `x` is a steepest-descent sequence with step sizes
`α` whose iterates converge to `xStar`. Then every ratio
`steepestDescentContractionFactor f xStar x k` whose objective-gap denominator is nonzero is
less than `1`. -/
theorem steepestDescentContractionFactor_lt_one_of_sourceHypotheses
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (k : ℕ)
    (hGapNe : f (x k) ≠ f xStar) :
    steepestDescentContractionFactor f xStar x k < 1 := by
  -- First make the source-domain denominator positive.
  have hDenPos : 0 < f (x k) - f xStar :=
    steepestDescentContractionFactor_denominator_pos_of_sourceHypotheses
      x α hC2 hStationary hPosDef hSeq hx k hGapNe
  -- A zero gradient would freeze the exact-line-search tail, contradicting the nonzero gap.
  have hGradNe : gradient f (x k) ≠ 0 := by
    intro hGradZero
    have hTailConst : ∀ n : ℕ, x (k + n) = x k := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          have hGradTail : gradient f (x (k + n)) = 0 := by
            simpa [ih] using hGradZero
          have hStepTail : x (k + n + 1) = x (k + n) := by
            simpa [steepestDescentStep, steepestDescentDirection, hGradTail] using
              (hSeq.update (k + n))
          simpa [Nat.add_assoc, ih] using hStepTail
    have hTailTendsto : Tendsto (fun n : ℕ ↦ x (k + n)) atTop (nhds xStar) :=
      (tendsto_add_atTop_iff_nat k).2 hx
    have hConstTendsto : Tendsto (fun _ : ℕ ↦ x k) atTop (nhds xStar) := by
      exact Tendsto.congr' (Filter.Eventually.of_forall hTailConst) hTailTendsto
    have hxk_eq : xStar = x k := tendsto_nhds_unique hConstTendsto tendsto_const_nhds
    have hValueEq : f (x k) = f xStar := by
      simpa using congrArg f hxk_eq.symm
    exact hGapNe hValueEq
  -- Exact line search beats a fixed short trial step in the steepest-descent direction.
  have hDescent :
      IsDescentDirectionAt f (x k) (steepestDescentDirection f (x k)) :=
    steepestDescentDirection_isDescentDirection f (x k) hGradNe
  obtain ⟨δ, hδ, hTrialDecrease⟩ := hDescent.exists_localDecrease_lineSearchObjective
  have hStepLeTrial :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) ≤
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (δ / 2) :=
    (hSeq.exactLineSearch k).optimal (by positivity)
  have hTrialStrict :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (δ / 2) <
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) 0 := by
    exact hTrialDecrease (δ / 2) (by positivity) (by linarith)
  have hValueStrict : f (x (k + 1)) < f (x k) := by
    have hStrictLine :
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) <
          lineSearchObjective f (x k) (steepestDescentDirection f (x k)) 0 :=
      lt_of_le_of_lt hStepLeTrial hTrialStrict
    simpa [lineSearchObjective_apply, lineSearchObjective_zero, hSeq.update k, steepestDescentStep]
      using hStrictLine
  -- Rewriting the ratio and using the positive denominator gives the desired strict contraction.
  rw [steepestDescentContractionFactor_def]
  have hGapStrict :
      f (x (k + 1)) - f xStar < f (x k) - f xStar := by
    exact sub_lt_sub_right hValueStrict (f xStar)
  simpa [one_mul] using (div_lt_iff₀ hDenPos).2 hGapStrict

/-- Helper for Chapter03 Theorem 3.1.7: rewrite the contraction factor as `1` minus the
normalized objective decrease. This is the exact algebraic form used in the source proof before
the Chapter 2 decrease estimate is inserted. -/
lemma steepestDescentContractionFactor_eq_one_sub_objectiveDecreaseRatio
    (f : Point → ℝ) (xStar : Point) (x : ℕ → Point) (k : ℕ)
    (hGapNe : f (x k) ≠ f xStar) :
    steepestDescentContractionFactor f xStar x k =
      1 - (f (x k) - f (x (k + 1))) / (f (x k) - f xStar) := by
  have hDen : f (x k) - f xStar ≠ 0 := sub_ne_zero.mpr hGapNe
  -- Clear the common denominator once to recover the source formula `β_k = 1 - Δf_k / gap_k`.
  rw [steepestDescentContractionFactor_def]
  field_simp [hDen]
  ring

/-- Helper for Chapter03 Theorem 3.1.7: once the Chapter 2 exact-line-search estimate supplies
`f (x k) - f (x (k + 1))`, the source inequality `(3.1.24)` is just denominator-positive
algebra. -/
lemma steepestDescentContractionFactor_le_one_sub_gradientGapRatio_of_decrease
    (f : Point → ℝ) (xStar : Point) (x : ℕ → Point) (k : ℕ) {M : ℝ}
    (hM : 0 < M)
    (hGapPos : 0 < f (x k) - f xStar)
    (hDecrease :
      (1 / (2 * M)) * ‖gradient f (x k)‖ ^ (2 : ℕ) ≤
        f (x k) - f (x (k + 1))) :
    steepestDescentContractionFactor f xStar x k ≤
      1 - ‖gradient f (x k)‖ ^ (2 : ℕ) /
        (2 * M * (f (x k) - f xStar)) := by
  have hGapNe : f (x k) ≠ f xStar := by
    intro hEq
    rw [hEq, sub_self] at hGapPos
    linarith
  have hDiv :
      ((1 / (2 * M)) * ‖gradient f (x k)‖ ^ (2 : ℕ)) / (f (x k) - f xStar) ≤
        (f (x k) - f (x (k + 1))) / (f (x k) - f xStar) :=
    div_le_div_of_nonneg_right hDecrease hGapPos.le
  -- Rewrite `β_k` as `1 - Δf_k / gap_k`, then compare the normalized decrease terms.
  rw [steepestDescentContractionFactor_eq_one_sub_objectiveDecreaseRatio f xStar x k hGapNe]
  have hSub :
      1 - (f (x k) - f (x (k + 1))) / (f (x k) - f xStar) ≤
        1 - ((1 / (2 * M)) * ‖gradient f (x k)‖ ^ (2 : ℕ)) / (f (x k) - f xStar) := by
    linarith
  refine hSub.trans_eq ?_
  field_simp [hM.ne', hGapPos.ne']
  ring

/-- Helper for Chapter03 Theorem 3.1.7: a positive lower eigenvalue bound on the symmetric
Hessian operator gives the quadratic-form lower bound `m * ‖y‖² ≤ yᵀ ∇²f(xStar) y`. -/
lemma hessianQuadraticAt_ge_mul_normSq_of_eigen_lower_bound
    [Nontrivial Point]
    {f : Point → ℝ} {xStar : Point} {m lambdaMin lambdaMax : ℝ}
    (hC2 : ContDiffAt ℝ 2 f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hmMin : m ≤ lambdaMin)
    (y : Point) :
    m * ‖y‖ ^ (2 : ℕ) ≤ hessianQuadraticAt f xStar y := by
  by_cases hy : y = 0
  · -- The zero direction contributes zero on both sides.
    subst hy
    simp
  · have hSymm :
        ((hessianAt f xStar).toLinearMap).IsSymmetric :=
      hessianAt_toLinearMap_isSymmetric_of_contDiffAt (f := f) (x := xStar) hC2
    have hRay :
        lambdaMin ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) y :=
      (rayleigh_quotient_hessianAt_mem_Icc_of_eigen_endpoints
        (f := f) (xStar := xStar) (lambdaMin := lambdaMin) (lambdaMax := lambdaMax)
        hSymm hLambdaMin hLambdaMax y hy).1
    have hy_sq_pos : 0 < ‖y‖ ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr hy) 2
    have hScaled :
        m ≤ hessianQuadraticAt f xStar y / ‖y‖ ^ (2 : ℕ) := by
      exact le_trans hmMin (by simpa [rayleighQuotient_hessianAt_eq_diag_ratio] using hRay)
    -- Multiply the Rayleigh lower bound back by `‖y‖²`.
    exact (le_div_iff₀ hy_sq_pos).mp hScaled

/-- Helper for Chapter03 Theorem 3.1.7: the spectral lower bound implies that
`hessianQuadraticAt f xStar` is positive definite, which is the source-side curvature hypothesis
needed to reopen the neighborhood argument around `xStar`. -/
lemma hessianQuadraticAt_pos_of_eigen_lower_bound
    [Nontrivial Point]
    {f : Point → ℝ} {xStar : Point} {m lambdaMin lambdaMax : ℝ}
    (hC2 : ContDiffAt ℝ 2 f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin) :
    ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y := by
  intro y hy
  have hy_sq_pos : 0 < ‖y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr hy) 2
  -- The lower spectral bound gives `m * ‖y‖²`, and `m > 0` turns that into strict positivity.
  exact lt_of_lt_of_le
    (mul_pos hm hy_sq_pos)
    (hessianQuadraticAt_ge_mul_normSq_of_eigen_lower_bound
      (f := f) (xStar := xStar) (m := m) (lambdaMin := lambdaMin) (lambdaMax := lambdaMax)
      hC2 hLambdaMin hLambdaMax hmMin y)

/-- Helper for Chapter03 Theorem 3.1.7: spectral control at `xStar` plus `C²` regularity shrinks
to a ball where the Hessian operator norm is bounded by `M + η`. -/
lemma exists_ball_hessianAt_norm_le_add_eta_of_spectral_bounds
    {m lambdaMin lambdaMax M η : ℝ}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin)
    (hMaxM : lambdaMax ≤ M)
    (hη : 0 < η) :
    ∃ ε > 0,
      ContDiffOn ℝ 2 f (Metric.ball xStar ε) ∧
        ∀ z ∈ Metric.ball xStar ε, ‖hessianAt f z‖ ≤ M + η := by
  rcases exists_contDiffOn_ball_of_nhds hC2 with ⟨ε0, hε0, hBallC2⟩
  have hContDiffAt : ContDiffAt ℝ 2 f xStar :=
    hBallC2.contDiffAt (Metric.ball_mem_nhds xStar hε0)
  have hSymm :
      ((hessianAt f xStar).toLinearMap).IsSymmetric :=
    hessianAt_toLinearMap_isSymmetric_of_contDiffAt (f := f) (x := xStar) hContDiffAt
  have hMinMax : lambdaMin ≤ lambdaMax := hLambdaMax.2 hLambdaMin.1
  have hmM : m ≤ M := le_trans hmMin (le_trans hMinMax hMaxM)
  have hM_nonneg : 0 ≤ M := le_trans hm.le hmM
  have hAbsRayleigh_le_M :
      ∀ u : Point,
        |ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u| ≤ M := by
    intro u
    by_cases hu : u = 0
    · simpa [hu] using hM_nonneg
    · have hBounds :=
        rayleigh_quotient_hessianAt_mem_Icc_of_eigen_endpoints
          (f := f) (xStar := xStar) (lambdaMin := lambdaMin) (lambdaMax := lambdaMax)
          hSymm hLambdaMin hLambdaMax u hu
      have hRayleigh_nonneg :
          0 ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u := by
        exact le_trans hm.le (le_trans hmMin hBounds.1)
      rw [abs_of_nonneg hRayleigh_nonneg]
      exact le_trans hBounds.2 hMaxM
  have hBddAboveAbsRayleigh :
      BddAbove
        (Set.range
          (fun u : Point ↦
            |ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u|)) := by
    refine ⟨M, ?_⟩
    intro r hr
    rcases hr with ⟨u, rfl⟩
    exact hAbsRayleigh_le_M u
  have hnorm_le_M : ‖hessianAt f xStar‖ ≤ M := by
    rw [(hessianAt f xStar).norm_eq_iSup_rayleighQuotient hSymm]
    exact ciSup_le hBddAboveAbsRayleigh hAbsRayleigh_le_M
  have hGradContDiffAt : ContDiffAt ℝ 1 (gradient f) xStar := by
    -- `gradient f` is `C¹` at `xStar` because `f` is `C²` there.
    change
      ContDiffAt ℝ 1
        (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f))
        xStar
    exact
      (LinearIsometryEquiv.contDiff ((InnerProductSpace.toDual ℝ Point).symm)).contDiffAt.comp
        xStar
        hContDiffAt.fderiv_right_succ
  have hHessianCont :
      ContinuousAt (fun z : Point ↦ hessianAt f z) xStar := by
    -- View `hessianAt` as `fderiv ℝ (gradient f)` and use the `C¹` regularity of `gradient f`.
    simpa [hessianAt] using hGradContDiffAt.continuousAt_fderiv (by norm_num)
  have hNear :
      (fun z : Point ↦ hessianAt f z) ⁻¹' Metric.ball (hessianAt f xStar) η ∈ nhds xStar :=
    hHessianCont.preimage_mem_nhds (Metric.ball_mem_nhds (hessianAt f xStar) hη)
  rcases Metric.mem_nhds_iff.mp hNear with ⟨δ, hδ, hδball⟩
  let ε : ℝ := min ε0 δ
  refine ⟨ε, by
      dsimp [ε]
      positivity, hBallC2.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_⟩
  intro z hz
  have hzδ : z ∈ Metric.ball xStar δ :=
    Metric.ball_subset_ball (min_le_right _ _) hz
  have hzNear :
      ‖hessianAt f z - hessianAt f xStar‖ < η := by
    simpa [Metric.mem_ball, dist_eq_norm] using hδball hzδ
  -- Split `hessianAt f z` into the perturbation from `xStar` plus the base Hessian norm.
  calc
    ‖hessianAt f z‖ = ‖(hessianAt f z - hessianAt f xStar) + hessianAt f xStar‖ := by
      congr 1
      abel_nf
    _ ≤ ‖hessianAt f z - hessianAt f xStar‖ + ‖hessianAt f xStar‖ := norm_add_le _ _
    _ ≤ M + η := by
      linarith

/-- Helper for Chapter03 Theorem 3.1.7: if `x k → xStar`, then both consecutive iterates are
eventually in the same small ball, so the whole segment between them stays in that ball. -/
lemma eventually_segment_subset_ball_of_tendsto_succ
    {xStar : Point} (x : ℕ → Point) {ε : ℝ}
    (hε : 0 < ε)
    (hx : Tendsto x atTop (nhds xStar)) :
    ∀ᶠ k in atTop, segment ℝ (x k) (x (k + 1)) ⊆ Metric.ball xStar ε := by
  have hxBall : ∀ᶠ k in atTop, x k ∈ Metric.ball xStar ε := by
    exact hx.eventually (Metric.ball_mem_nhds xStar hε)
  have hxSucc : Tendsto (fun k ↦ x (k + 1)) atTop (nhds xStar) :=
    (tendsto_add_atTop_iff_nat 1).2 hx
  have hxSuccBall : ∀ᶠ k in atTop, x (k + 1) ∈ Metric.ball xStar ε := by
    exact hxSucc.eventually (Metric.ball_mem_nhds xStar hε)
  filter_upwards [hxBall, hxSuccBall] with k hk hkSucc
  -- Convexity of the open ball keeps the segment between the two nearby iterates inside it.
  exact (convex_ball xStar ε).segment_subset hk hkSucc

/-- Helper for Chapter03 Theorem 3.1.7: for every `η > 0`, the source exact-line-search route
eventually upgrades the Chapter 2 decrease estimate to the textbook inequality `(3.1.24)` with
the denominator `2 * (M + η)`. -/
lemma eventually_contractionFactor_le_one_sub_gradientGapRatio_div_two_mul_add_eta
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    {m lambdaMin lambdaMax M η : ℝ}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin)
    (hMaxM : lambdaMax ≤ M)
    (hη : 0 < η)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (hGapNe : ∀ k : ℕ, f (x k) ≠ f xStar) :
    ∀ᶠ k in atTop,
      steepestDescentContractionFactor f xStar x k ≤
        1 - ‖gradient f (x k)‖ ^ (2 : ℕ) /
          (2 * (M + η) * (f (x k) - f xStar)) := by
  -- Route correction: first shrink to a ball with Hessian norm at most `M + η`, then apply the
  -- Chapter 2 exact-line-search decrease theorem on the whole traced segment.
  have hMinMax : lambdaMin ≤ lambdaMax := hLambdaMax.2 hLambdaMin.1
  have hmM : m ≤ M := le_trans hmMin (le_trans hMinMax hMaxM)
  have hMη : 0 < M + η := by
    linarith
  have hContDiffAt : ContDiffAt ℝ 2 f xStar := by
    rcases exists_contDiffOn_ball_of_nhds hC2 with ⟨ε, hε, hBallC2⟩
    exact hBallC2.contDiffAt (Metric.ball_mem_nhds xStar hε)
  have hPosDef :
      ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y :=
    hessianQuadraticAt_pos_of_eigen_lower_bound
      (f := f) (xStar := xStar) (m := m) (lambdaMin := lambdaMin) (lambdaMax := lambdaMax)
      hContDiffAt hLambdaMin hLambdaMax hm hmMin
  rcases exists_ball_hessianAt_norm_le_add_eta_of_spectral_bounds
      (f := f) (xStar := xStar) (m := m) (lambdaMin := lambdaMin) (lambdaMax := lambdaMax)
      (M := M) (η := η) hC2 hLambdaMin hLambdaMax hm hmMin hMaxM hη with
    ⟨ε, hε, hBallC2, hBallHessianNorm⟩
  have hSegment :
      ∀ᶠ k in atTop, segment ℝ (x k) (x (k + 1)) ⊆ Metric.ball xStar ε :=
    eventually_segment_subset_ball_of_tendsto_succ (xStar := xStar) x hε hx
  filter_upwards [hSegment] with k hkSegment
  have hGapPos : 0 < f (x k) - f xStar :=
    steepestDescentContractionFactor_denominator_pos_of_sourceHypotheses
      (f := f) (xStar := xStar) x α hC2 hStationary hPosDef hSeq hx k (hGapNe k)
  have hGradNe : gradient f (x k) ≠ 0 := by
    intro hGradZero
    have hTailConst : ∀ n : ℕ, x (k + n) = x k := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          have hGradTail : gradient f (x (k + n)) = 0 := by
            simpa [ih] using hGradZero
          have hStepTail : x (k + n + 1) = x (k + n) := by
            simpa [steepestDescentStep, steepestDescentDirection, hGradTail] using
              (hSeq.update (k + n))
          simpa [Nat.add_assoc, ih] using hStepTail
    have hTailTendsto : Tendsto (fun n : ℕ ↦ x (k + n)) atTop (nhds xStar) :=
      (tendsto_add_atTop_iff_nat k).2 hx
    have hConstTendsto : Tendsto (fun _ : ℕ ↦ x k) atTop (nhds xStar) := by
      exact Tendsto.congr' (Filter.Eventually.of_forall hTailConst) hTailTendsto
    have hxk_eq : xStar = x k :=
      tendsto_nhds_unique hConstTendsto tendsto_const_nhds
    have hValueEq : f (x k) = f xStar := by
      simpa using congrArg f hxk_eq.symm
    exact hGapNe k hValueEq
  have hDescent :
      IsDescentDirectionAt f (x k) (steepestDescentDirection f (x k)) :=
    steepestDescentDirection_isDescentDirection f (x k) hGradNe
  have hDecrease :
      (1 / (2 * (M + η))) * ‖gradient f (x k)‖ ^ (2 : ℕ) ≤
        f (x k) - f (x (k + 1)) := by
    have hCosOne :
        Real.cos
            (InnerProductGeometry.angle
              (steepestDescentDirection f (x k))
              (-(gradient f (x k)))) = 1 := by
      have hNegGradNe : -(gradient f (x k)) ≠ 0 := by
        simpa using neg_ne_zero.mpr hGradNe
      rw [show InnerProductGeometry.angle
            (steepestDescentDirection f (x k))
            (-(gradient f (x k))) = 0 by
              simpa [steepestDescentDirection] using
                InnerProductGeometry.angle_self hNegGradNe]
      simp
    -- Apply the Chapter 2 decrease estimate on the eventual ball containing the whole step
    -- segment, then collapse the cosine term because the search direction is exactly `-∇f`.
    simpa [hSeq.update k, steepestDescentStep, hessianAt, hCosOne] using
      (exactLineSearch_decrease_ge_half_inv_hessianBound_mul_gradientNormSq_mul_cosSq
        (D := Metric.ball xStar ε) f (x k) (steepestDescentDirection f (x k)) (α k) (M + η)
        hMη hDescent (hSeq.exactLineSearch k) Metric.isOpen_ball
        (by simpa [hSeq.update k, steepestDescentStep] using hkSegment) hBallC2
        (by
          intro z hz
          simpa [hessianAt] using hBallHessianNorm z hz))
  exact steepestDescentContractionFactor_le_one_sub_gradientGapRatio_of_decrease
    f xStar x k hMη hGapPos hDecrease

/-- Helper for Chapter03 Theorem 3.1.7: the normalized-displacement subsequence argument from
the source proof yields the asymptotic lower bound `(3.1.25)` on
`‖gradient f (x k)‖² / (f (x k) - f xStar)`. -/
lemma gradient_gap_ratio_liminf_ge_two_mul_lambda_min
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    {m lambdaMin lambdaMax : ℝ}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (hGapNe : ∀ k : ℕ, f (x k) ≠ f xStar) :
    2 * lambdaMin ≤
      Filter.liminf
        (fun k ↦ ‖gradient f (x k)‖ ^ (2 : ℕ) / (f (x k) - f xStar))
        atTop := by
  -- Route correction: stay with the source proof by passing to a bad-ratio subsequence on the
  -- unit sphere, then evaluate the subsequential limit via Taylor expansion and a Rayleigh bound.
  -- TODO: extract a normalized displacement subsequence, prove its ratio limit is the Hessian
  -- ratio at the limit direction, and compare that limit with `2 * lambdaMin`.
  sorry

/-- Chapter03 Theorem 3.1.7 (2): assume `f` is `C²` near `xStar`, `xStar` is stationary, the
steepest-descent iterates converge to `xStar`, and `lambdaMin`, `lambdaMax` are respectively the
smallest and largest eigenvalues of `hessianAt f xStar` with `0 < m ≤ lambdaMin` and
`lambdaMax ≤ M`. Then `Filter.limsup (steepestDescentContractionFactor f xStar x) atTop ≤
(M - m) / M` on runs whose objective gap never vanishes, so the ratio is only used on its
source domain. -/
theorem limsup_steepestDescentContractionFactor_le_of_sourceHypotheses
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    {m lambdaMin lambdaMax M : ℝ}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin)
    (hMaxM : lambdaMax ≤ M)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (hGapNe : ∀ k : ℕ, f (x k) ≠ f xStar) :
    Filter.limsup (steepestDescentContractionFactor f xStar x) atTop ≤ (M - m) / M := by
  by_cases hPoint : Subsingleton Point
  · -- In the degenerate ambient space every iterate equals `xStar`, contradicting `hGapNe`.
    exfalso
    have hx0_eq : x 0 = xStar := hPoint.elim _ _
    exact hGapNe 0 (by simpa [hx0_eq])
  · letI : Nontrivial Point := not_subsingleton_iff_nontrivial.mp hPoint
    let gapRatio : ℕ → ℝ :=
      fun k ↦ ‖gradient f (x k)‖ ^ (2 : ℕ) / (f (x k) - f xStar)
    have hLambdaMin_le_lambdaMax : lambdaMin ≤ lambdaMax := hLambdaMax.2 hLambdaMin.1
    have hmM : m ≤ M := le_trans hmMin (le_trans hLambdaMin_le_lambdaMax hMaxM)
    have hM : 0 < M := lt_of_lt_of_le hm hmM
    have hEventuallyBeta :
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∀ᶠ k in atTop,
            steepestDescentContractionFactor f xStar x k ≤
              1 - ‖gradient f (x k)‖ ^ (2 : ℕ) /
                (2 * (M + η) * (f (x k) - f xStar)) := by
      intro η hη
      exact eventually_contractionFactor_le_one_sub_gradientGapRatio_div_two_mul_add_eta
        (f := f) (xStar := xStar) x α hC2 hStationary hLambdaMin hLambdaMax
        hm hmMin hMaxM hη hSeq hx hGapNe
    have hRatioLiminf :
        2 * lambdaMin ≤ Filter.liminf gapRatio atTop :=
      gradient_gap_ratio_liminf_ge_two_mul_lambda_min
        (f := f) (xStar := xStar) x α hC2 hStationary hLambdaMin hLambdaMax
        hm hmMin hSeq hx hGapNe
    have hTwoM_liminf : 2 * m ≤ Filter.liminf gapRatio atTop := by
      linarith
    -- Route correction: fix an arbitrary upper target `y > (M - m) / M`, then choose a small
    -- `η` and a slightly weakened ratio threshold below `2m` so the eventual textbook estimate
    -- forces `β_k ≤ y` on the tail.
    refine (Filter.limsup_le_iff').2 ?_
    intro y hy
    let δ : ℝ := y - (M - m) / M
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    let η : ℝ := δ * M / 4
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have hMη : 0 < M + η := by
      dsimp [η]
      positivity
    let τ : ℝ := min m (δ * M / 4)
    have hτ_pos : 0 < τ := by
      dsimp [τ]
      positivity
    have hτ_le : τ ≤ δ * M / 4 := by
      exact min_le_right _ _
    have hEventuallyBeta' :
        ∀ᶠ k in atTop,
          steepestDescentContractionFactor f xStar x k ≤
            1 - gapRatio k / (2 * (M + η)) := by
      filter_upwards [hEventuallyBeta hη] with k hk
      -- Repackage the textbook estimate through the named ratio so the later comparison is flat.
      simpa [gapRatio, η, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hk
    have hEventuallyRatio :
        ∀ᶠ k in atTop, 2 * m - τ ≤ gapRatio k := by
      have hThreshold_lt : 2 * m - τ < 2 * m := by
        linarith
      exact ((Filter.le_liminf_iff').1 hTwoM_liminf) (2 * m - τ) hThreshold_lt
    have hBaseDeviation :
        1 - m / (M + η) ≤ (M - m) / M + δ / 4 := by
      -- The `η`-perturbed denominator deviates from `(M - m) / M` by at most `δ / 4`.
      rw [show η / M = δ / 4 by
        field_simp [η, hM.ne']
        ring]
      field_simp [η, hM.ne', hMη.ne']
      nlinarith
    have hRatioDeviation :
        τ / (2 * (M + η)) ≤ δ / 8 := by
      -- The ratio weakening `τ` contributes only another `δ / 8` to the final upper bound.
      field_simp [η, hM.ne', hMη.ne']
      nlinarith [hτ_le]
    have hUpper_lt :
        1 - (2 * m - τ) / (2 * (M + η)) < y := by
      have hy_eq : y = (M - m) / M + δ := by
        dsimp [δ]
        ring
      calc
        1 - (2 * m - τ) / (2 * (M + η))
            = (1 - m / (M + η)) + τ / (2 * (M + η)) := by ring
        _ ≤ ((M - m) / M + δ / 4) + δ / 8 :=
          add_le_add hBaseDeviation hRatioDeviation
        _ < (M - m) / M + δ := by
          linarith
        _ = y := hy_eq.symm
    filter_upwards [hEventuallyBeta', hEventuallyRatio] with k hkBeta hkRatio
    have hkScaled :
        (2 * m - τ) / (2 * (M + η)) ≤ gapRatio k / (2 * (M + η)) := by
      exact div_le_div_of_nonneg_right hkRatio (by positivity)
    -- Compare the eventual exact-line-search upper bound with the eventual lower ratio bound.
    have hkUpper :
        steepestDescentContractionFactor f xStar x k ≤
          1 - (2 * m - τ) / (2 * (M + η)) := by
      linarith
    exact le_of_lt (lt_of_le_of_lt hkUpper hUpper_lt)

/-- Chapter03 Theorem 3.1.7 (3): the final contraction bound is strictly less than `1` as soon
as `0 < m ≤ M`; the spectral data from part (2) are only a route to these arithmetic bounds,
not primitive inputs of this clause. -/
theorem steepestDescentContractionFactor_bound_lt_one_of_sourceHypotheses
    {m M : ℝ}
    (hm : 0 < m)
    (hmM : m ≤ M) :
    (M - m) / M < 1 := by
  -- The quantitative bound is `1 - m / M`, and the positive curvature ratio is nonzero.
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  rw [sub_div, div_self hM.ne']
  linarith [div_pos hm hM]

/-- Local `C²` quadratic-form bounds yield spectral witnesses for the canonical Hessian owner
`hessianAt f xStar`, with the comparison constants `m` and `M` retained on the public surface. -/
theorem exists_hessian_spectral_bounds_of_neighborhoodHessianBounds
    {f : Point → ℝ} {xStar : Point}
    {ε m M : ℝ}
    [Nontrivial Point]
    (hε : 0 < ε)
    (hm : 0 < m)
    (hC2 : ContDiffOn ℝ 2 f (Metric.ball xStar ε))
    (hHessian :
      ∀ ⦃x : Point⦄, x ∈ Metric.ball xStar ε → ∀ y : Point,
        m * ‖y‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ (2 : ℕ)) :
    ∃ lambdaMin lambdaMax : ℝ,
      IsLeast
          {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
          lambdaMin ∧
        IsGreatest
            {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
            lambdaMax ∧
          m ≤ lambdaMin ∧
            lambdaMax ≤ M := by
  letI : Nonempty {x : Point // x ≠ 0} := by
    rcases exists_ne (0 : Point) with ⟨u, hu⟩
    exact ⟨⟨u, hu⟩⟩
  have hxStar_mem : xStar ∈ Metric.ball xStar ε := Metric.mem_ball_self hε
  have hContDiffAt : ContDiffAt ℝ 2 f xStar :=
    hC2.contDiffAt (Metric.ball_mem_nhds xStar hε)
  have hSymm :
      ((hessianAt f xStar).toLinearMap).IsSymmetric :=
    hessianAt_toLinearMap_isSymmetric_of_contDiffAt (f := f) (x := xStar) hContDiffAt
  have hBddBelow :
      BddBelow
        (Set.range
          (fun x : {x : Point // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x)) := by
    refine ⟨-‖hessianAt f xStar‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The Rayleigh family is bounded below by the negative operator norm.
    have hv := (hessianAt f xStar).rayleighQuotient_le_norm v
    have habs := abs_le.mp hv
    linarith
  have hBddAbove :
      BddAbove
        (Set.range
          (fun x : {x : Point // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x)) := by
    refine ⟨‖hessianAt f xStar‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The same norm control supplies a global upper bound.
    exact le_trans (le_abs_self _) ((hessianAt f xStar).rayleighQuotient_le_norm v)
  refine
    ⟨
      ⨅ x : {x : Point // x ≠ 0},
        ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x,
      ⨆ x : {x : Point // x ≠ 0},
        ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x,
      ?_
    ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The infimal Rayleigh value is an eigenvalue and lies below every other eigenvalue.
    refine ⟨?_, ?_⟩
    · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply] using
        (LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
          (T := (hessianAt f xStar).toLinearMap) hSymm)
    · intro μ hμ
      rcases hμ.exists_hasEigenvector with ⟨u, hu⟩
      have hrq_eq :
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u = μ := by
        -- An eigenvector realizes its eigenvalue as a Rayleigh quotient.
        calc
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u =
              hessianQuadraticAt f xStar u / ‖u‖ ^ (2 : ℕ) :=
            rayleighQuotient_hessianAt_eq_diag_ratio
          _ = (μ * ‖u‖ ^ (2 : ℕ)) / ‖u‖ ^ (2 : ℕ) := by
            rw [hessianQuadraticAt_eq_mul_normSq_of_eigenvector hu.apply_eq_smul]
          _ = μ := by
            field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hu.2)]
      have hInf :
          (⨅ x : {x : Point // x ≠ 0},
            ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x) ≤
              ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u :=
        ciInf_le hBddBelow ⟨u, hu.2⟩
      rwa [hrq_eq] at hInf
  · -- The supremal Rayleigh value is likewise an eigenvalue and dominates every eigenvalue.
    refine ⟨?_, ?_⟩
    · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply] using
        (LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional
          (T := (hessianAt f xStar).toLinearMap) hSymm)
    · intro μ hμ
      rcases hμ.exists_hasEigenvector with ⟨u, hu⟩
      have hrq_eq :
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u = μ := by
        -- The same eigenvector-to-Rayleigh identity controls the maximal endpoint.
        calc
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u =
              hessianQuadraticAt f xStar u / ‖u‖ ^ (2 : ℕ) :=
            rayleighQuotient_hessianAt_eq_diag_ratio
          _ = (μ * ‖u‖ ^ (2 : ℕ)) / ‖u‖ ^ (2 : ℕ) := by
            rw [hessianQuadraticAt_eq_mul_normSq_of_eigenvector hu.apply_eq_smul]
          _ = μ := by
            field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hu.2)]
      have hSup :
          ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) u ≤
            (⨆ x : {x : Point // x ≠ 0},
              ContinuousLinearMap.rayleighQuotient (hessianAt f xStar) x) :=
        le_ciSup hBddAbove ⟨u, hu.2⟩
      rwa [hrq_eq] at hSup
  · -- Evaluate the neighborhood lower Hessian bound at `xStar` and divide by `‖u‖²`.
    refine le_ciInf ?_
    intro u
    have hu_pos : 0 < ‖(u : Point)‖ ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr u.2) 2
    have hLower :
        m * ‖(u : Point)‖ ^ (2 : ℕ) ≤ hessianQuadraticAt f xStar u := by
      rw [hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt (f := f) (x := xStar)
        (y := (u : Point)) hContDiffAt]
      exact (hHessian hxStar_mem u).1
    rw [rayleighQuotient_hessianAt_eq_diag_ratio]
    exact (le_div_iff₀ hu_pos).2 hLower
  · -- The upper Hessian bound at `xStar` gives the same quotient control from above.
    refine ciSup_le ?_
    intro u
    have hu_pos : 0 < ‖(u : Point)‖ ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr u.2) 2
    have hUpper :
        hessianQuadraticAt f xStar u ≤ M * ‖(u : Point)‖ ^ (2 : ℕ) := by
      rw [hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt (f := f) (x := xStar)
        (y := (u : Point)) hContDiffAt]
      exact (hHessian hxStar_mem u).2
    rw [rayleighQuotient_hessianAt_eq_diag_ratio]
    exact (div_le_iff₀ hu_pos).2 hUpper

/-- Quantitative bridge companion: the local `C²` quadratic-form bounds from Theorem 3.1.6,
combined with stationarity at `xStar` and convergence of the steepest-descent iterates, force
every stage whose objective gap is nonzero to have contraction factor strictly less than `1`.
This keeps the neighborhood regularity and curvature assumptions on the public surface instead of
treating the inequality as a consequence of exact line search alone. -/
theorem steepestDescentContractionFactor_lt_one_of_neighborhoodHessianBounds
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    {ε m M : ℝ}
    (hStationary : IsStationaryPoint f xStar)
    (hε : 0 < ε)
    (hm : 0 < m)
    (hmM : m ≤ M)
    (hC2 : ContDiffOn ℝ 2 f (Metric.ball xStar ε))
    (hHessian :
      ∀ ⦃x : Point⦄, x ∈ Metric.ball xStar ε → ∀ y : Point,
        m * ‖y‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ (2 : ℕ))
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (k : ℕ)
    (hGapNe : f (x k) ≠ f xStar) :
    steepestDescentContractionFactor f xStar x k < 1 := by
  -- First make the ratio denominator positive on the source domain.
  have hDenPos : 0 < f (x k) - f xStar :=
    steepestDescentContractionFactor_denominator_pos
      x α hStationary hε hm hmM hC2 hHessian hSeq hx k hGapNe
  -- A zero gradient would freeze the entire tail, forcing `x k = xStar` by convergence.
  have hGradNe : gradient f (x k) ≠ 0 := by
    intro hGradZero
    have hTailConst : ∀ n : ℕ, x (k + n) = x k := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          have hGradTail : gradient f (x (k + n)) = 0 := by
            simpa [ih] using hGradZero
          have hStepTail : x (k + n + 1) = x (k + n) := by
            simpa [steepestDescentStep, steepestDescentDirection, hGradTail] using
              (hSeq.update (k + n))
          simpa [Nat.add_assoc, ih] using hStepTail
    have hTailTendsto : Tendsto (fun n : ℕ ↦ x (k + n)) atTop (nhds xStar) :=
      (tendsto_add_atTop_iff_nat k).2 hx
    have hConstTendsto : Tendsto (fun _ : ℕ ↦ x k) atTop (nhds xStar) := by
      exact Tendsto.congr' (Filter.Eventually.of_forall hTailConst) hTailTendsto
    have hxk_eq : xStar = x k := tendsto_nhds_unique hConstTendsto tendsto_const_nhds
    have hValueEq : f (x k) = f xStar := by
      simpa using congrArg f hxk_eq.symm
    exact hGapNe hValueEq
  -- Exact line search beats a fixed short trial step in the descent direction, so the value drops.
  have hDescent :
      IsDescentDirectionAt f (x k) (steepestDescentDirection f (x k)) :=
    steepestDescentDirection_isDescentDirection f (x k) hGradNe
  obtain ⟨δ, hδ, hTrialDecrease⟩ := hDescent.exists_localDecrease_lineSearchObjective
  have hStepLeTrial :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) ≤
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (δ / 2) :=
    (hSeq.exactLineSearch k).optimal (by positivity)
  have hTrialStrict :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (δ / 2) <
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) 0 := by
    exact hTrialDecrease (δ / 2) (by positivity) (by linarith)
  have hValueStrict : f (x (k + 1)) < f (x k) := by
    have hStrictLine :
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) <
          lineSearchObjective f (x k) (steepestDescentDirection f (x k)) 0 :=
      lt_of_le_of_lt hStepLeTrial hTrialStrict
    simpa [lineSearchObjective_apply, lineSearchObjective_zero, hSeq.update k, steepestDescentStep]
      using hStrictLine
  -- Rewriting the ratio and using the positive denominator gives the desired strict contraction.
  rw [steepestDescentContractionFactor_def]
  have hGapStrict :
      f (x (k + 1)) - f xStar < f (x k) - f xStar := by
    exact sub_lt_sub_right hValueStrict (f xStar)
  simpa [one_mul] using (div_lt_iff₀ hDenPos).2 hGapStrict
