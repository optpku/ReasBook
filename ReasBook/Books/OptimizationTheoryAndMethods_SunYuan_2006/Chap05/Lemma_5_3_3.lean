/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.OrderClosed

noncomputable section

section Chapter05Lemma533

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
variable {D : Set Point} {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f)
variable (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
variable (hIterates : ∀ k : ℕ, A k ∈ quasiNewtonLevelSet f A.x0)
variable
  (hExactLineSearch :
    ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (A k) (broydenStep A k) 1)

include hA hIterates hExactLineSearch

/-- Helper for Chapter05 Lemma 5.3.3: the Chapter 5 lower Hessian bound yields a uniform lower
bound for the objective on the quasi-Newton level set. -/
lemma objectiveLowerBoundOnLevelSet :
    ∃ c : ℝ, ∀ x ∈ quasiNewtonLevelSet f A.x0, c ≤ f x := by
  rcases hA.lower_hessian with ⟨mD, hmD, hLowerD⟩
  have hStrongD : StrongConvexOn D mD f := by
    exact
      (strongConvexOn_iff_iteratedFDeriv_lower_bound
        hA.open_domain hA.convex_domain hA.contDiffOn mD).2 hLowerD
  have hDiff : DifferentiableOn ℝ f D :=
    hA.contDiffOn.differentiableOn (by norm_num : (2 : ℕ∞) ≠ 0)
  rcases
      (exists_strongConvexOn_iff_ge_gradient_inner_sub_add_sq
        (S := D) (f := f) hA.open_domain hA.convex_domain hDiff).1
        ⟨mD, hmD, hStrongD⟩
    with ⟨c, hc, hSupportOnD⟩
  refine ⟨f (A 0) - ‖A.g 0‖ ^ (2 : ℕ) / (2 * c), ?_⟩
  intro x hx
  -- Lower support at the base iterate reduces the problem to a one-variable quadratic bound.
  have hSupport :
      f (A 0) + inner ℝ (A.g 0) (x - A 0) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) ≤ f x := by
    have hxD : x ∈ D := hA.levelSet_subset hx
    have hSupportBase := hSupportOnD (A 0) hA.x0_mem x hxD
    simpa [A.gradient_eq 0, add_assoc, add_left_comm, add_comm] using hSupportBase
  have hInner :
      -(‖A.g 0‖ * ‖x - A 0‖) ≤ inner ℝ (A.g 0) (x - A 0) := by
    exact neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hQuad :
      -(‖A.g 0‖ ^ (2 : ℕ)) / (2 * c) ≤
        -(‖A.g 0‖ * ‖x - A 0‖) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) := by
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hScaled : 0 ≤ (c / 2) * (‖x - A 0‖ - ‖A.g 0‖ / c) ^ (2 : ℕ) := by
      positivity
    have hExpand :
        -(‖A.g 0‖ ^ (2 : ℕ)) / (2 * c) =
          -(‖A.g 0‖ * ‖x - A 0‖) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) -
            (c / 2) * (‖x - A 0‖ - ‖A.g 0‖ / c) ^ (2 : ℕ) := by
      field_simp [pow_two, hc_ne]
      ring
    linarith
  have hLinear :
      f (A 0) - ‖A.g 0‖ ^ (2 : ℕ) / (2 * c) ≤
        f (A 0) + inner ℝ (A.g 0) (x - A 0) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) := by
    have hInnerQuad :
        -(‖A.g 0‖ * ‖x - A 0‖) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) ≤
          inner ℝ (A.g 0) (x - A 0) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) := by
      linarith
    have hCore :
        -(‖A.g 0‖ ^ (2 : ℕ)) / (2 * c) ≤
          inner ℝ (A.g 0) (x - A 0) + (c / 2) * ‖x - A 0‖ ^ (2 : ℕ) :=
      le_trans hQuad hInnerQuad
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hCore (f (A 0))
  exact le_trans hLinear hSupport

/-- Helper for Chapter05 Lemma 5.3.3: every exact line-search step yields a quadratic objective
drop on the Chapter 5 level set. -/
lemma oneStepObjectiveDrop
    {m : ℝ} (hStrong : StrongConvexOn D m f)
    (k : ℕ) :
    (m / 2) * ‖broydenStep A k‖ ^ (2 : ℕ) ≤ f (A k) - f (A (k + 1)) := by
  let xk := A k
  let yk := A (k + 1)
  let sk := broydenStep A k
  let c : ℝ := (m / 2) * ‖sk‖ ^ (2 : ℕ)
  have hDecrease : f yk ≤ f xk := by
    simpa [xk, yk, sk, lineSearchObjective_apply, lineSearchObjective_zero, broydenStep] using
      (hExactLineSearch k).optimal (show 0 ≤ (0 : ℝ) by norm_num)
  by_cases hc : c ≤ 0
  · exact le_trans hc (sub_nonneg.mpr hDecrease)
  · have hc_pos : 0 < c := lt_of_not_ge hc
    by_contra hbound
    have hlt : f xk - f yk < c := lt_of_not_ge hbound
    let t : ℝ := ((f xk - f yk) / c + 1) / 2
    have hratio_nonneg : 0 ≤ (f xk - f yk) / c := by
      exact div_nonneg (sub_nonneg.mpr hDecrease) hc_pos.le
    have hratio_lt_one : (f xk - f yk) / c < 1 := by
      have hlt' : f xk - f yk < 1 * c := by
        simpa using hlt
      exact (div_lt_iff₀ hc_pos).2 hlt'
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      linarith
    have htlt1 : t < 1 := by
      dsimp [t]
      linarith
    have hMin : f yk ≤ f (AffineMap.lineMap xk yk t) := by
      have hOpt := (hExactLineSearch k).optimal ht0
      have hAtOne : lineSearchObjective f xk sk 1 = f yk := by
        dsimp [xk, yk, sk]
        simp [lineSearchObjective_apply, broydenStep]
      have hAtT : lineSearchObjective f xk sk t = f (AffineMap.lineMap xk yk t) := by
        dsimp [xk, yk, sk]
        rw [lineSearchObjective_apply, AffineMap.lineMap_apply_module']
        simp [broydenStep, add_comm]
      rw [hAtOne, hAtT] at hOpt
      exact hOpt
    have hStrongStep :
        f (AffineMap.lineMap xk yk t) ≤
          (1 - t) * f xk + t * f yk - (1 - t) * t * c := by
      have hWeights : (1 - t) + t = 1 := by ring
      have hstep :=
        hStrong.2
          (hA.levelSet_subset (hIterates k))
          (hA.levelSet_subset (hIterates (k + 1)))
          (sub_nonneg.mpr ht1) ht0 hWeights
      have hnorm : ‖xk - yk‖ ^ (2 : ℕ) = ‖sk‖ ^ (2 : ℕ) := by
        dsimp [xk, yk, sk]
        simp [broydenStep, norm_sub_rev]
      have hstep' :
          f ((1 - t) • xk + t • yk) ≤
            (1 - t) * f xk + t * f yk - (1 - t) * t * c := by
        calc
          f ((1 - t) • xk + t • yk) ≤
              (1 - t) * f xk + t * f yk -
                (1 - t) * t * ((m / 2) * ‖xk - yk‖ ^ (2 : ℕ)) := hstep
          _ = (1 - t) * f xk + t * f yk - (1 - t) * t * c := by
              rw [c, hnorm]
      simpa [AffineMap.lineMap_apply_module] using hstep'
    have hGap : c * t ≤ f xk - f yk := by
      nlinarith [hMin, hStrongStep, htlt1]
    have hGap' : f xk - f yk < c * t := by
      have hRewrite :
          c * t = (f xk - f yk + c) / 2 := by
        dsimp [t]
        field_simp [hc_pos.ne']
      rw [hRewrite]
      linarith
    exact (not_lt_of_ge hGap) hGap'

/-- Helper for Chapter05 Lemma 5.3.3: the partial sums of the step-square series are controlled
by the telescoping objective gap. -/
lemma sumRange_stepNormSq_le_objectiveGap
    {m : ℝ} (hStrong : StrongConvexOn D m f) :
    ∀ N : ℕ, (m / 2) *
        Finset.sum (Finset.range N) (fun i ↦ ‖broydenStep A i‖ ^ (2 : ℕ)) ≤
      f (A 0) - f (A N) := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      calc
        (m / 2) * Finset.sum (Finset.range (N + 1)) (fun i ↦ ‖broydenStep A i‖ ^ (2 : ℕ))
            = (m / 2) *
                (Finset.sum (Finset.range N) (fun i ↦ ‖broydenStep A i‖ ^ (2 : ℕ)) +
                  ‖broydenStep A N‖ ^ (2 : ℕ)) := by
                rw [Finset.sum_range_succ]
        _ = (m / 2) * Finset.sum (Finset.range N) (fun i ↦ ‖broydenStep A i‖ ^ (2 : ℕ)) +
              (m / 2) * ‖broydenStep A N‖ ^ (2 : ℕ) := by
                ring
        _ ≤ (f (A 0) - f (A N)) + (f (A N) - f (A (N + 1))) := by
              exact add_le_add ih (oneStepObjectiveDrop (A := A) (hExactLineSearch := hExactLineSearch)
                (hIterates := hIterates) hStrong N)
        _ = f (A 0) - f (A (N + 1)) := by
              ring

/-- Helper for Chapter05 Lemma 5.3.3: at a `C²` point, the diagonal second derivative agrees
with the gradient derivative pairing. -/
lemma iteratedFDerivDiag_eq_inner_fderivGradientAt
    {x u : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    (iteratedFDeriv ℝ 2 f x) ![u, u] = inner ℝ u ((fderiv ℝ (gradient f) x) u) := by
  -- Reuse the canonical Hessian interface so the gradient derivative stays in inner-product form.
  calc
    (iteratedFDeriv ℝ 2 f x) ![u, u] = inner ℝ u (hessianAt f x u) := by
      symm
      exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
        (f := f) (x := x) (y := u) (z := u) hC2
    _ = inner ℝ u ((fderiv ℝ (gradient f) x) u) := by
      rfl

/-- Helper for Chapter05 Lemma 5.3.3: at a `C²` point, the Hessian operator is symmetric. -/
lemma hessianAtToLinearMap_isSymmetric
    {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    ((hessianAt f x).toLinearMap).IsSymmetric := by
  intro y z
  -- Transfer symmetry of the second derivative through the canonical Hessian bridge.
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

/-- Helper for Chapter05 Lemma 5.3.3: on the Chapter 5 level set, the gradient derivative has
operator norm bounded by the upper Hessian constant once the lower bound supplies positivity. -/
lemma fderivGradient_norm_le_of_levelHessianBounds
    {m M : ℝ} (hm : 0 < m) (hM_nonneg : 0 ≤ M)
    (hLower : HasLowerLevelHessianLowerBound D f A.x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f A.x0 M)
    {z : Point}
    (hz : z ∈ quasiNewtonLevelSet f A.x0) :
    ‖fderiv ℝ (gradient f) z‖ ≤ M := by
  let T : Point →L[ℝ] Point := fderiv ℝ (gradient f) z
  have hzD : z ∈ D := hA.levelSet_subset hz
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hzD)
  have hzLower : z ∈ lowerLevelSetOn D f A.x0 := by
    simpa [hA.levelSet_eq_lowerLevelSetOn] using hz
  have hsymm : T.IsSymmetric := by
    change ((hessianAt f z).toLinearMap).IsSymmetric
    exact hessianAtToLinearMap_isSymmetric (A := A) (f := f) hC2z
  rw [T.norm_eq_iSup_rayleighQuotient hsymm]
  refine ciSup_le ?_
  intro u
  by_cases hu : u = 0
  · simp [T, ContinuousLinearMap.rayleighQuotient, hu, hM_nonneg]
  have hlower :
      0 ≤ inner ℝ u (T u) := by
    have hbound : m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f z) ![u, u] :=
      hLower z hzLower u
    rw [iteratedFDerivDiag_eq_inner_fderivGradientAt (A := A) (f := f) hC2z] at hbound
    have hmul_nonneg : 0 ≤ m * ‖u‖ ^ (2 : ℕ) := by
      positivity
    exact le_trans hmul_nonneg hbound
  have hupper :
      inner ℝ u (T u) ≤ M * ‖u‖ ^ (2 : ℕ) := by
    have hbound : (iteratedFDeriv ℝ 2 f z) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ) :=
      hUpper z hzLower u
    rw [iteratedFDerivDiag_eq_inner_fderivGradientAt (A := A) (f := f) hC2z] at hbound
    exact hbound
  have hu_norm_sq_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  have hrq_nonneg : 0 ≤ T.rayleighQuotient u := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    simpa [real_inner_comm] using div_nonneg hlower (pow_two_nonneg ‖u‖)
  have hrq_le : T.rayleighQuotient u ≤ M := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (div_le_iff₀ hu_norm_sq_pos).2 (by simpa [real_inner_comm] using hupper)
  simpa [abs_of_nonneg hrq_nonneg] using hrq_le

/-- Helper for Chapter05 Lemma 5.3.3: on the ambient domain `D`, the gradient map is
differentiable because `f` is `C²` there. -/
lemma gradientDifferentiableAtOnDomain
    {z : Point}
    (hz : z ∈ D) :
    DifferentiableAt ℝ (gradient f) z := by
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hz)
  have hGradC1 : ContDiffAt ℝ 1 (gradient f) z := by
    change ContDiffAt ℝ 1 (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) z
    exact
      (LinearIsometryEquiv.contDiff ((InnerProductSpace.toDual ℝ Point).symm)).contDiffAt.comp z
        hC2z.fderiv_right_succ
  exact hGradC1.differentiableAt_one

/-- Helper for Chapter05 Lemma 5.3.3: under the Chapter 5 Hessian bounds, each secant square is
bounded by `M ^ 2` times the corresponding step square. -/
lemma secantNormSq_le_mul_stepNormSq
    {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hLower : HasLowerLevelHessianLowerBound D f A.x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f A.x0 M)
    (k : ℕ) :
    ‖broydenSecant A.g k‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * ‖broydenStep A k‖ ^ (2 : ℕ) := by
  have hDiff : ∀ z ∈ quasiNewtonLevelSet f A.x0, DifferentiableAt ℝ (gradient f) z := by
    intro z hz
    exact gradientDifferentiableAtOnDomain (A := A) (hA := hA) (hA.levelSet_subset hz)
  have hBound : ∀ z ∈ quasiNewtonLevelSet f A.x0, ‖fderiv ℝ (gradient f) z‖ ≤ M := by
    intro z hz
    exact
      fderivGradient_norm_le_of_levelHessianBounds
        (A := A) (hA := hA) hm hM.le hLower hUpper hz
  have hGradDiff :
      ‖gradient f (A (k + 1)) - gradient f (A k)‖ ≤ M * ‖A (k + 1) - A k‖ := by
    exact
      hA.levelSet_convex.norm_image_sub_le_of_norm_fderiv_le
        (f := gradient f) hDiff hBound (hIterates k) (hIterates (k + 1))
  have hSec :
      ‖broydenSecant A.g k‖ ≤ M * ‖broydenStep A k‖ := by
    simpa [broydenSecant, broydenStep, A.gradient_eq] using hGradDiff
  nlinarith [hSec, hM.le, norm_nonneg (broydenSecant A.g k), norm_nonneg (broydenStep A k)]

/-- Chapter05 Lemma 5.3.3 (1): under Chapter05 Assumption 5.3.1, if `A` is an exact-line-search
quasi-Newton run whose iterates stay in `quasiNewtonLevelSet f A.x0` and whose realized
displacements `broydenStep A k = A (k + 1) - A k` are exact line-search steps of length `1`,
then the step-square series `∑ ‖s_k‖ ^ 2` is convergent, formalized canonically as
`Summable (fun k ↦ ‖broydenStep A k‖ ^ (2 : ℕ))`. -/
theorem stepNormSq_summable_of_exactLineSearch :
    Summable (fun k ↦ ‖broydenStep A k‖ ^ (2 : ℕ)) := by
  rcases hA.lower_hessian with ⟨m, hm, hLowerD⟩
  have hStrong : StrongConvexOn D m f := by
    exact
      (strongConvexOn_iff_iteratedFDeriv_lower_bound
        hA.open_domain hA.convex_domain hA.contDiffOn m).2 hLowerD
  rcases objectiveLowerBoundOnLevelSet (A := A) (hA := hA) with ⟨c, hc⟩
  have hscaled :
      Summable (fun k ↦ (m / 2) * ‖broydenStep A k‖ ^ (2 : ℕ)) := by
    refine summable_of_sum_range_le (fun _ ↦ by positivity) ?_
    intro N
    calc
      ∑ i ∈ Finset.range N, (m / 2) * ‖broydenStep A i‖ ^ (2 : ℕ)
          = (m / 2) * Finset.sum (Finset.range N) (fun i ↦ ‖broydenStep A i‖ ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
      _ ≤ f (A 0) - f (A N) :=
        sumRange_stepNormSq_le_objectiveGap (A := A) (hExactLineSearch := hExactLineSearch)
          (hIterates := hIterates) hStrong N
      _ ≤ f (A 0) - c := by
        gcongr
        exact hc (A N) (hIterates N)
  have hm_ne : m / 2 ≠ 0 := by
    positivity
  simpa using (summable_mul_left_iff hm_ne).mp hscaled

/-- Chapter05 Lemma 5.3.3 (2): under the same exact-line-search and Chapter05 Assumption 5.3.1
hypotheses, the secant-square series `∑ ‖y_k‖ ^ 2` is convergent, formalized canonically as
`Summable (fun k ↦ ‖broydenSecant A.g k‖ ^ (2 : ℕ))`. -/
theorem secantNormSq_summable_of_exactLineSearch :
    Summable (fun k ↦ ‖broydenSecant A.g k‖ ^ (2 : ℕ)) := by
  rcases hA.lower_hessianOn_levelSet with ⟨m, hm, hLower⟩
  rcases hA.upper_hessianOn_levelSet with ⟨M, hM, hUpper⟩
  have hStep :
      Summable (fun k ↦ ‖broydenStep A k‖ ^ (2 : ℕ)) :=
    stepNormSq_summable_of_exactLineSearch
      (A := A) (hA := hA) (hIterates := hIterates) (hExactLineSearch := hExactLineSearch)
  have hScaled :
      Summable (fun k ↦ M ^ (2 : ℕ) * ‖broydenStep A k‖ ^ (2 : ℕ)) := by
    exact Summable.mul_left _ hStep
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) ?_ hScaled
  intro k
  exact secantNormSq_le_mul_stepNormSq
    (A := A) (hA := hA) (hIterates := hIterates) hm hM hLower hUpper k

end Chapter05Lemma533
