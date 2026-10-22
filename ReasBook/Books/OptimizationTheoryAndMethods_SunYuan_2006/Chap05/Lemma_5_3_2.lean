/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

section Chapter05Lemma532

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * source-facing layer: Lemma 5.3.2 secant estimates under
--   `HasQuasiNewtonGlobalConvergenceAssumptions`;
-- * core/canonical project owners: `quasiNewtonLevelSet`, `lowerLevelSetOn`,
--   `HasLowerLevelHessianLowerBound`, and `HasLowerLevelHessianUpperBound`;
-- * bridge/view layer: the explicit constants `m` and `M` extracted from the Chapter 5
--   assumption package.
-- The gradient-difference estimates in this file use the Chapter 5 convexity and `C²` regularity
-- on the level set segment between `xk` and `xk + sk`, so the source-facing assumption package
-- remains part of the public theorem surface.

/-- Helper for Chapter05 Lemma 5.3.2: every point of the secant trace
`xk + t • sk`, `t ∈ [0, 1]`, stays in `quasiNewtonLevelSet f x0`. -/
lemma segmentPoint_mem_quasiNewtonLevelSet
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xk + t • sk ∈ quasiNewtonLevelSet f x0 := by
  -- Rewrite the trace point as the convex combination of the secant endpoints.
  have hconv :=
    hA.levelSet_convex hxk hxk_add_sk (sub_nonneg.mpr ht.2) ht.1 (by linarith)
  have hrewrite : (1 - t) • xk + t • (xk + sk) = xk + t • sk := by
    rw [smul_add]
    calc
      (1 - t) • xk + (t • xk + t • sk) = ((1 - t) • xk + t • xk) + t • sk := by
        abel_nf
      _ = (1 - t + t) • xk + t • sk := by
        rw [← add_smul]
      _ = xk + t • sk := by
        simp
  exact hrewrite ▸ hconv

/-- Helper for Chapter05 Lemma 5.3.2: the entire secant segment from `xk` to `xk + sk` lies in
the ambient domain `D`. -/
lemma secantSegment_subset_domain
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0) :
    segment ℝ xk (xk + sk) ⊆ D := by
  intro z hz
  rw [segment_eq_image' ℝ xk (xk + sk)] at hz
  rcases hz with ⟨t, ht, rfl⟩
  -- Push the level-set segment membership through `levelSet_subset`.
  exact hA.levelSet_subset <|
    by
      simpa [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using
          segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht

/-- Helper for Chapter05 Lemma 5.3.2: at a `C²` point, the diagonal second derivative agrees with
the gradient derivative pairing. -/
lemma iteratedFDerivDiag_eq_inner_fderivGradient
    {f : Point → ℝ} {x u : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    (iteratedFDeriv ℝ 2 f x) ![u, u] = inner ℝ u ((fderiv ℝ (gradient f) x) u) := by
  -- Use the canonical Hessian owner to avoid unfolding the gradient derivative in place.
  calc
    (iteratedFDeriv ℝ 2 f x) ![u, u] = inner ℝ u (hessianAt f x u) := by
      symm
      exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
        (f := f) (x := x) (y := u) (z := u) hC2
    _ = inner ℝ u ((fderiv ℝ (gradient f) x) u) := by
      rfl

/-- Helper for Chapter05 Lemma 5.3.2: on real Euclidean space, `dotProduct` is the inner product
with reversed arguments. -/
lemma dotProduct_eq_inner (u v : Point) :
    dotProduct u v = inner ℝ v u := by
  simpa using (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v u).symm

/-- Helper for Chapter05 Lemma 5.3.2: the Hessian operator is symmetric at every `C²` point. -/
lemma hessianAt_toLinearMap_isSymmetric_of_contDiffAt
    {f : Point → ℝ} {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    ((hessianAt f x).toLinearMap).IsSymmetric := by
  intro y z
  -- Transfer symmetry of the second iterated derivative through the local Hessian bridge.
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

/-- Helper for Chapter05 Lemma 5.3.2: the gradient map is differentiable at every point of the
ambient domain `D`, with derivative `fderiv ℝ (gradient f) z`. -/
lemma gradient_differentiableAt_onDomain
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    {z : Point}
    (hz : z ∈ D) :
    DifferentiableAt ℝ (gradient f) z := by
  -- Upgrade the on-domain `C²` hypothesis to a pointwise Fréchet derivative for `gradient f`.
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hz)
  have hGradC1 : ContDiffAt ℝ 1 (gradient f) z := by
    change ContDiffAt ℝ 1 (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) z
    exact
      (LinearIsometryEquiv.contDiff ((InnerProductSpace.toDual ℝ Point).symm)).contDiffAt.comp z
        hC2z.fderiv_right_succ
  exact hGradC1.differentiableAt_one

/-- Helper for Chapter05 Lemma 5.3.2: on the ambient domain `D`, the gradient field inherits the
needed `C¹` regularity from the `C²` objective. -/
lemma gradient_contDiffOnDomain
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ContDiffOn ℝ 1 (gradient f) D := by
  have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) D := by
    simpa using hA.contDiffOn.fderiv_of_isOpen hA.open_domain (by norm_num)
  -- Rewrite the gradient through the Riesz map so the derivative regularity is transparent.
  change ContDiffOn ℝ 1 (fun z ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f z)) D
  exact (InnerProductSpace.toDual ℝ Point).symm.contDiff.comp_contDiffOn hC1fderiv

/-- Helper for Chapter05 Lemma 5.3.2: the derivative field `z ↦ fderiv ℝ (gradient f) z` is
continuous on the ambient domain `D`. -/
lemma fderivGradient_continuousOnDomain
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ContinuousOn (fun z ↦ fderiv ℝ (gradient f) z) D := by
  -- Once `gradient f` is `C¹` on `D`, its Fréchet derivative is continuous there.
  exact
    (gradient_contDiffOnDomain f x0 hA).continuousOn_fderiv_of_isOpen
      hA.open_domain le_rfl

/-- Helper for Chapter05 Lemma 5.3.2: the secant vector equals the interval integral of the
gradient derivative along the secant segment. -/
lemma gradientSecant_eq_intervalIntegral_fderivGradientOnSegment
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk) :
    yk = ∫ t in (0 : ℝ)..1, (fderiv ℝ (gradient f) (xk + t • sk)) sk := by
  have hpath_mem :
      Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
    intro t ht
    exact hA.levelSet_subset <|
      segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
  have hpath_cont :
      ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk)
        MeasureTheory.volume 0 1 := by
    -- The traced derivative is continuous on the compact unit interval, hence integrable.
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hclm_cont :
        ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
      exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
    exact (continuousOn_clm_apply.mp hclm_cont) sk
  have hftc :
      ∫ t in (0 : ℝ)..1, (fderiv ℝ (gradient f) (xk + t • sk)) sk =
        gradient f (xk + sk) - gradient f xk := by
    -- Apply the vector-valued fundamental theorem of calculus to the traced gradient field.
    simpa [zero_smul, one_smul] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ ↦ gradient f (xk + s • sk))
        (f' := fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk)
        (by
          intro t ht
          have hz : xk + t • sk ∈ D := by
            exact hpath_mem (by simpa [Set.uIcc_of_le zero_le_one] using ht)
          have hgrad :
              HasFDerivAt (gradient f) (fderiv ℝ (gradient f) (xk + t • sk)) (xk + t • sk) :=
            (gradient_differentiableAt_onDomain f x0 hA hz).hasFDerivAt
          have htrace : HasDerivAt (fun s : ℝ ↦ xk + s • sk) sk t := by
            simpa [one_smul] using (((hasDerivAt_id t).smul_const sk).const_add xk)
          exact hgrad.comp_hasDerivAt t htrace)
        hint)
  calc
    yk = gradient f (xk + sk) - gradient f xk := hyk
    _ = ∫ t in (0 : ℝ)..1, (fderiv ℝ (gradient f) (xk + t • sk)) sk := by
      simpa using hftc.symm

/-- Helper for Chapter05 Lemma 5.3.2: pairing the secant vector with the step turns the secant
identity into the corresponding Hessian quadratic integral along the segment. -/
lemma gradientSecant_pairing_eq_intervalIntegral_hessianQuadraticOnSegment
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk) :
    dotProduct sk yk =
      ∫ t in (0 : ℝ)..1,
        inner ℝ sk ((fderiv ℝ (gradient f) (xk + t • sk)) sk) := by
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk)
        MeasureTheory.volume 0 1 := by
    -- Reuse continuity of the traced derivative to justify the interval integral rewrite.
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hclm_cont :
        ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
      exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
    exact (continuousOn_clm_apply.mp hclm_cont) sk
  calc
    dotProduct sk yk = inner ℝ yk sk := dotProduct_eq_inner sk yk
    _ = inner ℝ sk yk := by rw [real_inner_comm]
    _ = inner ℝ sk (∫ t in (0 : ℝ)..1, (fderiv ℝ (gradient f) (xk + t • sk)) sk) := by
      rw [gradientSecant_eq_intervalIntegral_fderivGradientOnSegment
        f x0 xk sk yk hA hxk hxk_add_sk hyk]
    _ = ∫ t in (0 : ℝ)..1, inner ℝ sk ((fderiv ℝ (gradient f) (xk + t • sk)) sk) := by
      symm
      exact ((innerSL ℝ sk).restrictScalars ℝ).intervalIntegral_comp_comm hint

/-- Helper for Chapter05 Lemma 5.3.2: at every `C²` point, the derivative of the gradient is a
symmetric operator. -/
lemma fderivGradient_isSymmetric_of_contDiffAt
    {f : Point → ℝ} {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (gradient f) x).IsSymmetric := by
  -- Route correction: use the local Hessian interface instead of unfolding `gradient` directly.
  change ((hessianAt f x).toLinearMap).IsSymmetric
  exact hessianAt_toLinearMap_isSymmetric_of_contDiffAt (f := f) hC2

/-- Helper for Chapter05 Lemma 5.3.2: the lower Hessian bound on the level set rewrites directly
to the quadratic form of `fderiv ℝ (gradient f)`. -/
lemma fderivGradient_quadratic_lower_of_levelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point) {m : ℝ}
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    {z u : Point}
    (hz : z ∈ quasiNewtonLevelSet f x0) :
    m * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ u ((fderiv ℝ (gradient f) z) u) := by
  have hzD : z ∈ D := hA.levelSet_subset hz
  have hzLower : z ∈ lowerLevelSetOn D f x0 := by
    simpa [hA.levelSet_eq_lowerLevelSetOn] using hz
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hzD)
  -- Normalize the lower Hessian bound to the gradient derivative once and stay in `inner` form.
  rw [← iteratedFDerivDiag_eq_inner_fderivGradient (f := f) (x := z) (u := u) hC2z]
  exact hLower z hzLower u

/-- Helper for Chapter05 Lemma 5.3.2: the upper Hessian bound on the level set rewrites directly
to the quadratic form of `fderiv ℝ (gradient f)`. -/
lemma fderivGradient_quadratic_upper_of_levelHessianUpperBound
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point) {M : ℝ}
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    {z u : Point}
    (hz : z ∈ quasiNewtonLevelSet f x0) :
    inner ℝ u ((fderiv ℝ (gradient f) z) u) ≤ M * ‖u‖ ^ (2 : ℕ) := by
  have hzD : z ∈ D := hA.levelSet_subset hz
  have hzLower : z ∈ lowerLevelSetOn D f x0 := by
    simpa [hA.levelSet_eq_lowerLevelSetOn] using hz
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hzD)
  -- Normalize the upper Hessian bound to the gradient derivative once and stay in `inner` form.
  rw [← iteratedFDerivDiag_eq_inner_fderivGradient (f := f) (x := z) (u := u) hC2z]
  exact hUpper z hzLower u

/-- Helper for Chapter05 Lemma 5.3.2: along the level set, the gradient derivative has operator
norm bounded by the upper Hessian constant once the lower bound supplies positivity. -/
lemma hessianOperatorNorm_le_of_levelHessianBounds
    {D : Set Point}
    (f : Point → ℝ) (x0 : Point) {m M : ℝ}
    (hm : 0 < m)
    (hM_nonneg : 0 ≤ M)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    {z : Point}
    (hz : z ∈ quasiNewtonLevelSet f x0) :
    ‖fderiv ℝ (gradient f) z‖ ≤ M := by
  let A : Point →L[ℝ] Point := fderiv ℝ (gradient f) z
  have hzD : z ∈ D := hA.levelSet_subset hz
  have hC2z : ContDiffAt ℝ 2 f z := hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hzD)
  have hsymm : A.IsSymmetric := by
    simpa [A] using fderivGradient_isSymmetric_of_contDiffAt (f := f) hC2z
  rw [A.norm_eq_iSup_rayleighQuotient hsymm]
  refine ciSup_le ?_
  intro u
  by_cases hu : u = 0
  · simp [A, ContinuousLinearMap.rayleighQuotient, hu, hM_nonneg]
  have hlower :
      0 ≤ inner ℝ u (A u) := by
    have hbound :=
      fderivGradient_quadratic_lower_of_levelHessianLowerBound
        f x0 hA hLower hz (u := u)
    have hmul_nonneg : 0 ≤ m * ‖u‖ ^ (2 : ℕ) := by positivity
    exact le_trans hmul_nonneg hbound
  have hupper :
      inner ℝ u (A u) ≤ M * ‖u‖ ^ (2 : ℕ) := by
    simpa [A] using
      fderivGradient_quadratic_upper_of_levelHessianUpperBound
        f x0 hA hUpper hz (u := u)
  have hu_norm_sq_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  have hrq_nonneg : 0 ≤ A.rayleighQuotient u := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    simpa [real_inner_comm] using div_nonneg hlower (pow_two_nonneg ‖u‖)
  have hrq_le : A.rayleighQuotient u ≤ M := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (div_le_iff₀ hu_norm_sq_pos).2 (by simpa [real_inner_comm] using hupper)
  simpa [abs_of_nonneg hrq_nonneg] using hrq_le

/-- Under the lower Hessian bound on the Chapter 5 level set `quasiNewtonLevelSet f x0`, every
secant vector
`yk = gradient f (xk + sk) - gradient f xk` has curvature bounded below by
`m * ‖sk‖ ^ 2`. -/
theorem secantCurvature_lowerBound_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk) :
    m * ‖sk‖ ^ (2 : ℕ) ≤ dotProduct sk yk := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ sk ((fderiv ℝ (gradient f) (xk + t • sk)) sk)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hvec_cont :
        ContinuousOn
          (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk)
          (Set.Icc (0 : ℝ) 1) := by
      have hclm_cont :
          ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
        exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
      exact (continuousOn_clm_apply.mp hclm_cont) sk
    -- Pair the continuous traced derivative with the fixed step vector.
    exact continuousOn_const.inner hvec_cont
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    exact hg_cont.intervalIntegrable_of_Icc zero_le_one
  have hmono :
      ∫ t in (0 : ℝ)..1, (m * ‖sk‖ ^ (2 : ℕ) : ℝ) ≤ ∫ t in (0 : ℝ)..1, g t := by
    refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ ↦ m * ‖sk‖ ^ (2 : ℕ)) (g := g) (μ := MeasureTheory.volume)
      zero_le_one (intervalIntegrable_const) hg_int ?_
    intro t ht
    exact fderivGradient_quadratic_lower_of_levelHessianLowerBound
      f x0 hA hLower
      (segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht)
  -- Identify the right-hand integral with the secant curvature and simplify the constant integral.
  calc
    m * ‖sk‖ ^ (2 : ℕ) = ∫ t in (0 : ℝ)..1, (m * ‖sk‖ ^ (2 : ℕ) : ℝ) := by
      simp
    _ ≤ ∫ t in (0 : ℝ)..1, g t := hmono
    _ = dotProduct sk yk := by
      symm
      exact gradientSecant_pairing_eq_intervalIntegral_hessianQuadraticOnSegment
        f x0 xk sk yk hA hxk hxk_add_sk hyk

/-- The secant curvature denominator is strictly positive under the lower Hessian bound on the
Chapter 5 level set `quasiNewtonLevelSet f x0` for every nonzero step `sk`. -/
theorem secantCurvature_pos_of_step_nonzero_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    0 < dotProduct sk yk := by
  -- The lower curvature estimate becomes strict once `sk ≠ 0` and `m > 0`.
  have hcurv :
      m * ‖sk‖ ^ (2 : ℕ) ≤ dotProduct sk yk :=
    secantCurvature_lowerBound_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hA hLower hxk hxk_add_sk hyk
  have hmul_pos : 0 < m * ‖sk‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
    positivity
  exact lt_of_lt_of_le hmul_pos hcurv

/-- A nonzero quasi-Newton step produces a nonzero secant vector when the lower Hessian bound
holds on the Chapter 5 level set `quasiNewtonLevelSet f x0` and
`yk = gradient f (xk + sk) - gradient f xk`. -/
theorem secant_nonzero_of_step_nonzero_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    yk ≠ 0 := by
  have hcurv_pos :
      0 < dotProduct sk yk :=
    secantCurvature_pos_of_step_nonzero_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  -- Positive curvature cannot occur if the secant vector itself vanishes.
  intro hyk_zero
  have hzero : dotProduct sk yk = 0 := by
    simp [hyk_zero]
  nlinarith [hcurv_pos, hzero]

/-- If the lower Hessian bound with modulus `m > 0` holds on the Chapter 5 level set
`quasiNewtonLevelSet f x0`, both `xk` and `xk + sk` lie in that set,
`yk = gradient f (xk + sk) - gradient f xk`, and `sk ≠ 0`, then the ratio
`‖sk‖ / ‖yk‖` is bounded above by `1 / m`. -/
theorem stepNorm_div_secantNorm_le_inv_m_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    ‖sk‖ / ‖yk‖ ≤ 1 / m := by
  have hyk_nonzero :
      yk ≠ 0 :=
    secant_nonzero_of_step_nonzero_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  have hcurv :
      m * ‖sk‖ ^ (2 : ℕ) ≤ dotProduct sk yk :=
    secantCurvature_lowerBound_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hA hLower hxk hxk_add_sk hyk
  have hcauchy :
      dotProduct sk yk ≤ ‖sk‖ * ‖yk‖ := by
    have hinner :
        |inner ℝ yk sk| ≤ ‖yk‖ * ‖sk‖ := by
      simpa [Real.norm_eq_abs, mul_comm] using norm_inner_le_norm (𝕜 := ℝ) yk sk
    exact le_trans (le_abs_self _) (by simpa [dotProduct_eq_inner, mul_comm] using hinner)
  have hnorm_bound : m * ‖sk‖ ≤ ‖yk‖ := by
    have hsk_norm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
    have hmul : m * ‖sk‖ ^ (2 : ℕ) ≤ ‖sk‖ * ‖yk‖ := le_trans hcurv hcauchy
    have hdiv : (m * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ ≤ (‖sk‖ * ‖yk‖) / ‖sk‖ := by
      exact div_le_div_of_nonneg_right hmul (norm_nonneg sk)
    calc
      m * ‖sk‖ = (m * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ := by
        field_simp [pow_two, hsk_norm_pos.ne']
      _ ≤ (‖sk‖ * ‖yk‖) / ‖sk‖ := hdiv
      _ = ‖yk‖ := by
        field_simp [hsk_norm_pos.ne']
  have hyk_norm_pos : 0 < ‖yk‖ := norm_pos_iff.mpr hyk_nonzero
  -- Clear the positive denominator to reduce the ratio estimate to `m * ‖sk‖ ≤ ‖yk‖`.
  field_simp [hyk_norm_pos.ne', hm.ne']
  nlinarith [hnorm_bound]

/-- If Chapter05 Assumption 5.3.1 holds and `m > 0` and `M` are lower and upper Hessian
constants on the level set `quasiNewtonLevelSet f x0`, then every nonzero secant pair
`yk = gradient f (xk + sk) - gradient f xk` with `xk, xk + sk ∈ quasiNewtonLevelSet f x0`
satisfies `‖yk‖ / ‖sk‖ ≤ M`. The lower bound keeps the Hessian positive on the segment and avoids
claiming this operator-norm estimate from the quadratic-form upper bound alone. -/
theorem secantNorm_div_stepNorm_le_M_of_lowerLevelHessianBounds
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m M : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    ‖yk‖ / ‖sk‖ ≤ M := by
  let v : ℝ → Point := fun t ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk
  have hM_nonneg : 0 ≤ M := by
    have hxkLower : xk ∈ lowerLevelSetOn D f x0 := by
      simpa [hA.levelSet_eq_lowerLevelSetOn] using hxk
    have hlower_xk :
        m * ‖sk‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f xk) ![sk, sk] :=
      hLower xk hxkLower sk
    have hupper_xk :
        (iteratedFDeriv ℝ 2 f xk) ![sk, sk] ≤ M * ‖sk‖ ^ (2 : ℕ) :=
      hUpper xk hxkLower sk
    have hchain : m * ‖sk‖ ^ (2 : ℕ) ≤ M * ‖sk‖ ^ (2 : ℕ) := le_trans hlower_xk hupper_xk
    have hsk_norm_sq_pos : 0 < ‖sk‖ ^ (2 : ℕ) := by
      have hsk_norm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
      positivity
    have hm_le_M : m ≤ M := by
      have hdiv :
          (m * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ ^ (2 : ℕ) ≤
            (M * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_right hchain (pow_two_nonneg ‖sk‖)
      simpa [hsk_norm_sq_pos.ne'] using hdiv
    exact le_trans hm.le hm_le_M
  have hv_cont : ContinuousOn v (Set.Icc (0 : ℝ) 1) := by
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hclm_cont :
        ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
      exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
    exact (continuousOn_clm_apply.mp hclm_cont) sk
  have hv_int : IntervalIntegrable v MeasureTheory.volume 0 1 := by
    exact hv_cont.intervalIntegrable_of_Icc zero_le_one
  have hvnorm_int : IntervalIntegrable (fun t : ℝ ↦ ‖v t‖) MeasureTheory.volume 0 1 := by
    exact hv_cont.norm.intervalIntegrable_of_Icc zero_le_one
  have hvnorm_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v t‖ ≤ M * ‖sk‖ := by
    intro t ht
    have hz :
        xk + t • sk ∈ quasiNewtonLevelSet f x0 :=
      segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hop :
        ‖fderiv ℝ (gradient f) (xk + t • sk)‖ ≤ M :=
      hessianOperatorNorm_le_of_levelHessianBounds
        f x0 hm hM_nonneg hA hLower hUpper hz
    calc
      ‖v t‖ ≤ ‖fderiv ℝ (gradient f) (xk + t • sk)‖ * ‖sk‖ := by
        simpa [v] using (fderiv ℝ (gradient f) (xk + t • sk)).le_opNorm sk
      _ ≤ M * ‖sk‖ := by
        exact mul_le_mul_of_nonneg_right hop (norm_nonneg sk)
  have hvnorm_mono :
      ∫ t in (0 : ℝ)..1, ‖v t‖ ≤ ∫ t in (0 : ℝ)..1, (M * ‖sk‖ : ℝ) := by
    refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ ↦ ‖v t‖) (g := fun _ : ℝ ↦ M * ‖sk‖) (μ := MeasureTheory.volume)
      zero_le_one hvnorm_int (intervalIntegrable_const) hvnorm_bound
  have hyk_bound : ‖yk‖ ≤ M * ‖sk‖ := by
    calc
      ‖yk‖ = ‖∫ t in (0 : ℝ)..1, v t‖ := by
        rw [gradientSecant_eq_intervalIntegral_fderivGradientOnSegment
          f x0 xk sk yk hA hxk hxk_add_sk hyk]
      _ ≤ ∫ t in (0 : ℝ)..1, ‖v t‖ := by
        exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in (0 : ℝ)..1, (M * ‖sk‖ : ℝ) := hvnorm_mono
      _ = M * ‖sk‖ := by
        simp
  have hsk_norm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
  exact (div_le_iff₀ hsk_norm_pos).2 (by simpa [mul_comm] using hyk_bound)

/-- Under Chapter05 Assumption 5.3.1 and an upper Hessian bound with constant `M` on the level
set `quasiNewtonLevelSet f x0`, the curvature ratio `dotProduct sk yk / ‖sk‖ ^ 2` is bounded
above by `M` for every nonzero step `sk`. -/
theorem secantCurvature_div_stepNormSq_le_M_of_lowerLevelHessianBounds
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {M : ℝ}
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    dotProduct sk yk / ‖sk‖ ^ (2 : ℕ) ≤ M := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ sk ((fderiv ℝ (gradient f) (xk + t • sk)) sk)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hvec_cont :
        ContinuousOn
          (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) sk)
          (Set.Icc (0 : ℝ) 1) := by
      have hclm_cont :
          ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
        exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
      exact (continuousOn_clm_apply.mp hclm_cont) sk
    -- Pair the continuous traced derivative with the fixed step vector.
    exact continuousOn_const.inner hvec_cont
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    exact hg_cont.intervalIntegrable_of_Icc zero_le_one
  have hmono :
      ∫ t in (0 : ℝ)..1, g t ≤ ∫ t in (0 : ℝ)..1, (M * ‖sk‖ ^ (2 : ℕ) : ℝ) := by
    refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (f := g) (g := fun _ : ℝ ↦ M * ‖sk‖ ^ (2 : ℕ)) (μ := MeasureTheory.volume)
      zero_le_one hg_int (intervalIntegrable_const) ?_
    intro t ht
    exact fderivGradient_quadratic_upper_of_levelHessianUpperBound
      f x0 hA hUpper
      (segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht)
  have hcurv_upper :
      dotProduct sk yk ≤ M * ‖sk‖ ^ (2 : ℕ) := by
    calc
      dotProduct sk yk = ∫ t in (0 : ℝ)..1, g t := by
        exact gradientSecant_pairing_eq_intervalIntegral_hessianQuadraticOnSegment
          f x0 xk sk yk hA hxk hxk_add_sk hyk
      _ ≤ ∫ t in (0 : ℝ)..1, (M * ‖sk‖ ^ (2 : ℕ) : ℝ) := hmono
      _ = M * ‖sk‖ ^ (2 : ℕ) := by
        simp
  have hsk_norm_sq_pos : 0 < ‖sk‖ ^ (2 : ℕ) := by
    have hsk_norm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
    positivity
  exact (div_le_iff₀ hsk_norm_sq_pos).2 hcurv_upper

/-- Under the lower Hessian bound with modulus `m > 0` on the Chapter 5 level set
`quasiNewtonLevelSet f x0`, the curvature ratio `dotProduct sk yk / ‖yk‖ ^ 2` is bounded above by
`1 / m`. -/
theorem secantCurvature_div_secantNormSq_le_inv_m_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    dotProduct sk yk / ‖yk‖ ^ (2 : ℕ) ≤ 1 / m := by
  have hyk_nonzero :
      yk ≠ 0 :=
    secant_nonzero_of_step_nonzero_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  have hcauchy :
      dotProduct sk yk ≤ ‖sk‖ * ‖yk‖ := by
    have hinner :
        |inner ℝ yk sk| ≤ ‖yk‖ * ‖sk‖ := by
      simpa [Real.norm_eq_abs, mul_comm] using norm_inner_le_norm (𝕜 := ℝ) yk sk
    exact le_trans (le_abs_self _) (by simpa [dotProduct_eq_inner, mul_comm] using hinner)
  have hyk_norm_pos : 0 < ‖yk‖ := norm_pos_iff.mpr hyk_nonzero
  have hratio_le :
      dotProduct sk yk / ‖yk‖ ^ (2 : ℕ) ≤ ‖sk‖ / ‖yk‖ := by
    have hyk_norm_sq_pos : 0 < ‖yk‖ ^ (2 : ℕ) := by positivity
    refine (div_le_iff₀ hyk_norm_sq_pos).2 ?_
    field_simp [pow_two, hyk_norm_pos.ne']
    nlinarith [hcauchy]
  exact hratio_le.trans <|
    stepNorm_div_secantNorm_le_inv_m_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk

/-- Helper for Chapter05 Lemma 5.3.2: if a finite-dimensional real positive operator has norm at
most `M`, then its image satisfies the quadratic estimate `‖T x‖² ≤ M * ⟪x, T x⟫`. -/
lemma sq_norm_apply_le_mul_inner_apply_of_isPositive_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T : E →L[ℝ] E} {M : ℝ}
    (hT : T.IsPositive)
    (hTnorm : ‖T‖ ≤ M)
    (x : E) :
    ‖T x‖ ^ (2 : ℕ) ≤ M * inner ℝ x (T x) := by
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hT with ⟨m, u, hu⟩
  let S : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
      (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (u i)))
  have hgram :
      ContinuousLinearMap.adjoint S ∘L S =
        ∑ i : Fin m, InnerProductSpace.rankOne ℝ (u i) (u i) := by
    ext z
    -- Identify the Gram operator of the coefficient map by comparing all right inner products.
    apply ext_inner_right ℝ
    intro y
    calc
      inner ℝ ((ContinuousLinearMap.adjoint S ∘L S) z) y = inner ℝ (S z) (S y) := by
        simpa [ContinuousLinearMap.comp_apply] using
          (ContinuousLinearMap.adjoint_inner_left (A := S) (x := y) (y := S z))
      _ = ∑ i : Fin m, inner ℝ (u i) z * inner ℝ (u i) y := by
        simp [S, PiLp.inner_apply, mul_comm]
      _ = inner ℝ ((∑ i : Fin m, InnerProductSpace.rankOne ℝ (u i) (u i)) z) y := by
        calc
          ∑ i : Fin m, inner ℝ (u i) z * inner ℝ (u i) y
              = ∑ i : Fin m, inner ℝ (inner ℝ (u i) z • u i) y := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  simpa using
                    (inner_smul_left (𝕜 := ℝ) (r := inner ℝ (u i) z) (x := u i) (y := y)).symm
          _ = inner ℝ (∑ i : Fin m, inner ℝ (u i) z • u i) y := by
            simpa using
              (sum_inner (s := Finset.univ) (f := fun i : Fin m ↦ inner ℝ (u i) z • u i) y).symm
          _ = inner ℝ ((∑ i : Fin m, InnerProductSpace.rankOne ℝ (u i) (u i)) z) y := by
            simp [InnerProductSpace.rankOne_apply]
  have hTS : T = ContinuousLinearMap.adjoint S ∘L S := by
    -- Replace the positive operator by its Gram-factorization from the rank-one decomposition.
    rw [hu]
    exact hgram.symm
  have hSsq_le_M : ‖S‖ * ‖S‖ ≤ M := by
    have hnormGram : ‖ContinuousLinearMap.adjoint S ∘L S‖ ≤ M := by
      simpa [hTS] using hTnorm
    -- The Gram operator norm is exactly the square of the coefficient-map norm.
    rw [ContinuousLinearMap.norm_adjoint_comp_self] at hnormGram
    exact hnormGram
  have hApply : ‖T x‖ ≤ ‖S‖ * ‖S x‖ := by
    -- Rewrite `T` through the Gram factorization and bound `S†` by its operator norm.
    calc
      ‖T x‖ = ‖ContinuousLinearMap.adjoint S (S x)‖ := by
          simp [hTS, ContinuousLinearMap.comp_apply]
      _ ≤ ‖ContinuousLinearMap.adjoint S‖ * ‖S x‖ := by
          simpa using (ContinuousLinearMap.adjoint S).le_opNorm (S x)
      _ = ‖S‖ * ‖S x‖ := by
        have hnormAdj : ‖ContinuousLinearMap.adjoint S‖ = ‖S‖ :=
          ContinuousLinearMap.adjoint.norm_map S
        simp [hnormAdj]
  have hInner : ‖S x‖ ^ (2 : ℕ) = inner ℝ x (T x) := by
    -- The Gram factorization turns the quadratic form into the squared coefficient norm.
    calc
      ‖S x‖ ^ (2 : ℕ) = inner ℝ x ((ContinuousLinearMap.adjoint S ∘L S) x) := by
        simpa using (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (A := S) x)
      _ = inner ℝ x (T x) := by simp [hTS, ContinuousLinearMap.comp_apply]
  calc
    ‖T x‖ ^ (2 : ℕ) ≤ (‖S‖ * ‖S x‖) ^ (2 : ℕ) := by gcongr
    _ = (‖S‖ * ‖S‖) * (‖S x‖ ^ (2 : ℕ)) := by ring
    _ ≤ M * (‖S x‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right hSsq_le_M (pow_two_nonneg ‖S x‖)
    _ = M * inner ℝ x (T x) := by rw [hInner]

/-- Helper for Chapter05 Lemma 5.3.2: the averaged derivative along the secant segment is
interval-integrable as an operator-valued map. -/
lemma secantAveragedFderiv_intervalIntegrable
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0) :
    IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk))
      MeasureTheory.volume 0 1 := by
  have hpath_mem :
      Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
    intro t ht
    exact hA.levelSet_subset <|
      segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
  have hpath_cont :
      ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hclm_cont :
      ContinuousOn (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk)) (Set.Icc (0 : ℝ) 1) := by
    exact (fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem
  -- Continuity of the operator field on the compact segment gives interval integrability.
  exact hclm_cont.intervalIntegrable_of_Icc zero_le_one

/-- Helper for Chapter05 Lemma 5.3.2: the averaged derivative along the secant segment is a
positive operator. -/
lemma secantAveragedFderiv_isPositive
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ (gradient f) (xk + t • sk)).IsPositive := by
  let A : ℝ → Point →L[ℝ] Point := fun t ↦ fderiv ℝ (gradient f) (xk + t • sk)
  have hA_int :
      IntervalIntegrable A MeasureTheory.volume 0 1 :=
    secantAveragedFderiv_intervalIntegrable f x0 xk sk hA hxk hxk_add_sk
  have hA_apply_int (u : Point) :
      IntervalIntegrable (fun t : ℝ ↦ (A t) u) MeasureTheory.volume 0 1 := by
    rw [show (fun t : ℝ ↦ (A t) u) = fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) u by
      rfl]
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hu_cont :
        ContinuousOn
          (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) u)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_clm_apply.mp
        ((fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem)) u
    exact hu_cont.intervalIntegrable_of_Icc zero_le_one
  refine (ContinuousLinearMap.isPositive_iff _).2 ⟨?_, ?_⟩
  · intro u v
    -- Symmetry survives the interval integral because each pointwise derivative is symmetric.
    calc
      inner ℝ ((∫ t in (0 : ℝ)..1, A t) u) v
          = inner ℝ (∫ t in (0 : ℝ)..1, (A t) u) v := by
              rw [ContinuousLinearMap.intervalIntegral_apply hA_int]
      _ = inner ℝ v (∫ t in (0 : ℝ)..1, (A t) u) := by
        rw [real_inner_comm]
      _ = ∫ t in (0 : ℝ)..1, inner ℝ v ((A t) u) := by
        symm
        simpa using
          ((innerSL ℝ v).restrictScalars ℝ).intervalIntegral_comp_comm
            (hA_apply_int u)
      _ = ∫ t in (0 : ℝ)..1, inner ℝ ((A t) u) v := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t
        intro _
        rw [real_inner_comm]
      _ = ∫ t in (0 : ℝ)..1, inner ℝ u ((A t) v) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t
        intro ht
        have hz :
            xk + t • sk ∈ D := by
          have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
            simpa [Set.uIoc_of_le zero_le_one] using ht
          exact hA.levelSet_subset <|
            segmentPoint_mem_quasiNewtonLevelSet
              f x0 xk sk hA hxk hxk_add_sk ⟨le_of_lt ht'.1, ht'.2⟩
        have hC2 :
            ContDiffAt ℝ 2 f (xk + t • sk) := by
          exact hA.contDiffOn.contDiffAt (hA.open_domain.mem_nhds hz)
        exact (fderivGradient_isSymmetric_of_contDiffAt (f := f) hC2) u v
      _ = inner ℝ u (∫ t in (0 : ℝ)..1, (A t) v) := by
        exact
          ((innerSL ℝ u).restrictScalars ℝ).intervalIntegral_comp_comm
            (hA_apply_int v)
      _ = inner ℝ u ((∫ t in (0 : ℝ)..1, A t) v) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hA_int]
  · intro u
    -- Integrate the pointwise lower quadratic bound with `m > 0` to keep positivity explicit.
    calc
      0 ≤ ∫ t in (0 : ℝ)..1, inner ℝ u ((A t) u) := by
        exact intervalIntegral.integral_nonneg zero_le_one fun t ht ↦ by
          have hz :
              xk + t • sk ∈ quasiNewtonLevelSet f x0 :=
            segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
          have hbound :
              m * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ u ((A t) u) := by
            simpa [A] using
              fderivGradient_quadratic_lower_of_levelHessianLowerBound
                f x0 hA hLower hz (u := u)
          have hmul_nonneg : 0 ≤ m * ‖u‖ ^ (2 : ℕ) := by positivity
          exact le_trans hmul_nonneg hbound
      _ = ∫ t in (0 : ℝ)..1, inner ℝ ((A t) u) u := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t
        simp [real_inner_comm]
      _ = ∫ t in (0 : ℝ)..1, inner ℝ u ((A t) u) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t
        intro _
        rw [real_inner_comm]
      _ = inner ℝ u (∫ t in (0 : ℝ)..1, (A t) u) := by
        simpa using
          ((innerSL ℝ u).restrictScalars ℝ).intervalIntegral_comp_comm
            (hA_apply_int u)
      _ = inner ℝ ((∫ t in (0 : ℝ)..1, A t) u) u := by
        rw [ContinuousLinearMap.intervalIntegral_apply hA_int, real_inner_comm]

/-- Helper for Chapter05 Lemma 5.3.2: the averaged derivative along the secant segment has
operator norm at most the upper Hessian constant `M`. -/
lemma secantAveragedFderiv_norm_le
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk : Point) {m M : ℝ}
    (hm : 0 < m)
    (hM_nonneg : 0 ≤ M)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0) :
    ‖∫ t in (0 : ℝ)..1, fderiv ℝ (gradient f) (xk + t • sk)‖ ≤ M := by
  let A : ℝ → Point →L[ℝ] Point := fun t ↦ fderiv ℝ (gradient f) (xk + t • sk)
  have hA_int :
      IntervalIntegrable A MeasureTheory.volume 0 1 :=
    secantAveragedFderiv_intervalIntegrable f x0 xk sk hA hxk hxk_add_sk
  have hA_apply_int (u : Point) :
      IntervalIntegrable (fun t : ℝ ↦ (A t) u) MeasureTheory.volume 0 1 := by
    rw [show (fun t : ℝ ↦ (A t) u) = fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) u by
      rfl]
    have hpath_mem :
        Set.MapsTo (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) D := by
      intro t ht
      exact hA.levelSet_subset <|
        segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hpath_cont :
        ContinuousOn (fun t : ℝ ↦ xk + t • sk) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hu_cont :
        ContinuousOn
          (fun t : ℝ ↦ (fderiv ℝ (gradient f) (xk + t • sk)) u)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_clm_apply.mp
        ((fderivGradient_continuousOnDomain f x0 hA).comp hpath_cont hpath_mem)) u
    exact hu_cont.intervalIntegrable_of_Icc zero_le_one
  refine ContinuousLinearMap.opNorm_le_bound _ hM_nonneg ?_
  intro u
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ ↦ M * ‖u‖) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hAu_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(A t) u‖ ≤ M * ‖u‖ := by
    intro t ht
    have hz :
        xk + t • sk ∈ quasiNewtonLevelSet f x0 :=
      segmentPoint_mem_quasiNewtonLevelSet f x0 xk sk hA hxk hxk_add_sk ht
    have hop :
        ‖A t‖ ≤ M := by
      simpa [A] using
        hessianOperatorNorm_le_of_levelHessianBounds
          f x0 hm hM_nonneg hA hLower hUpper hz
    calc
      ‖(A t) u‖ ≤ ‖A t‖ * ‖u‖ := by exact (A t).le_opNorm u
      _ ≤ M * ‖u‖ := by exact mul_le_mul_of_nonneg_right hop (norm_nonneg u)
  calc
    ‖(∫ t in (0 : ℝ)..1, A t) u‖ = ‖∫ t in (0 : ℝ)..1, (A t) u‖ := by
      rw [ContinuousLinearMap.intervalIntegral_apply hA_int]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖(A t) u‖ := by
      exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, (M * ‖u‖ : ℝ) := by
      exact
        intervalIntegral.integral_mono_on zero_le_one ((hA_apply_int u).norm) hconst_int
          hAu_bound
    _ = M * ‖u‖ := by simp

/-- Helper for Chapter05 Lemma 5.3.2: applying the averaged secant derivative to `sk` recovers
the secant vector `yk`. -/
lemma secantAveragedFderiv_apply_step
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ (gradient f) (xk + t • sk)) sk = yk := by
  have hA_int :
      IntervalIntegrable
        (fun t : ℝ ↦ fderiv ℝ (gradient f) (xk + t • sk))
        MeasureTheory.volume 0 1 :=
    secantAveragedFderiv_intervalIntegrable f x0 xk sk hA hxk hxk_add_sk
  -- Move the interval integral through application and reuse the FTC secant identity.
  rw [ContinuousLinearMap.intervalIntegral_apply hA_int]
  symm
  exact gradientSecant_eq_intervalIntegral_fderivGradientOnSegment
    f x0 xk sk yk hA hxk hxk_add_sk hyk

/-- Chapter05 Lemma 5.3.2: if Chapter05 Assumption 5.3.1 holds and lower and upper Hessian
bounds with constants `0 < m` and `M` hold on the level set `quasiNewtonLevelSet f x0`, then the
reciprocal curvature ratio `‖yk‖ ^ 2 / dotProduct sk yk` is bounded above by `M`. The lower bound
makes the denominator positivity part of the mathematical input instead of leaving it hidden
behind totalized division. -/
theorem secantNormSq_div_secantCurvature_le_M_of_lowerLevelHessianBounds
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m M : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    ‖yk‖ ^ (2 : ℕ) / dotProduct sk yk ≤ M := by
  let B : Point →L[ℝ] Point :=
    ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient f) (xk + t • sk)
  have hM_nonneg : 0 ≤ M := by
    have hxkLower : xk ∈ lowerLevelSetOn D f x0 := by
      simpa [hA.levelSet_eq_lowerLevelSetOn] using hxk
    have hlower_xk : m * ‖sk‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f xk) ![sk, sk] :=
      hLower xk hxkLower sk
    have hupper_xk : (iteratedFDeriv ℝ 2 f xk) ![sk, sk] ≤ M * ‖sk‖ ^ (2 : ℕ) :=
      hUpper xk hxkLower sk
    have hchain : m * ‖sk‖ ^ (2 : ℕ) ≤ M * ‖sk‖ ^ (2 : ℕ) := le_trans hlower_xk hupper_xk
    have hsk_norm_sq_pos : 0 < ‖sk‖ ^ (2 : ℕ) := by
      have hsk_norm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
      positivity
    have hm_le_M : m ≤ M := by
      have hdiv :
          (m * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ ^ (2 : ℕ) ≤
            (M * ‖sk‖ ^ (2 : ℕ)) / ‖sk‖ ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_right hchain (pow_two_nonneg ‖sk‖)
      simpa [hsk_norm_sq_pos.ne'] using hdiv
    exact le_trans hm.le hm_le_M
  have hB_pos : B.IsPositive := by
    -- The averaged derivative keeps the pointwise symmetry and lower Hessian positivity.
    simpa [B] using
      secantAveragedFderiv_isPositive
        f x0 xk sk hm hA hLower hxk hxk_add_sk
  have hB_norm : ‖B‖ ≤ M := by
    -- The averaged derivative inherits the pointwise operator-norm upper bound.
    simpa [B] using
      secantAveragedFderiv_norm_le
        f x0 xk sk hm hM_nonneg hA hLower hUpper hxk hxk_add_sk
  have hB_apply : B sk = yk := by
    -- The averaged derivative applied to the step is exactly the secant vector.
    simpa [B] using
      secantAveragedFderiv_apply_step
        f x0 xk sk yk hA hxk hxk_add_sk hyk
  have hnum_le :
      ‖yk‖ ^ (2 : ℕ) ≤ M * dotProduct sk yk := by
    -- Route correction: finish through the averaged positive operator instead of repeating FTC.
    calc
      ‖yk‖ ^ (2 : ℕ) = ‖B sk‖ ^ (2 : ℕ) := by rw [hB_apply]
      _ ≤ M * inner ℝ sk (B sk) := by
        exact sq_norm_apply_le_mul_inner_apply_of_isPositive_norm_le hB_pos hB_norm sk
      _ = M * dotProduct sk yk := by
        rw [hB_apply, dotProduct_eq_inner, real_inner_comm]
  have hcurv_pos :
      0 < dotProduct sk yk :=
    secantCurvature_pos_of_step_nonzero_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  -- Clear the positive curvature denominator once the numerator comparison is in place.
  exact (div_le_iff₀ hcurv_pos).2 hnum_le

/-- Consolidated ratio bounds for Chapter05 Lemma 5.3.2: if Chapter05 Assumption 5.3.1 holds and
lower and upper Hessian bounds with constants `0 < m` and `M` hold on `quasiNewtonLevelSet f x0`,
then every nonzero secant pair `yk = gradient f (xk + sk) - gradient f xk` with
`xk, xk + sk ∈ quasiNewtonLevelSet f x0` satisfies the five bounded ratios `‖sk‖ / ‖yk‖`,
`‖yk‖ / ‖sk‖`, `dotProduct sk yk / ‖sk‖ ^ 2`, `dotProduct sk yk / ‖yk‖ ^ 2`, and
`‖yk‖ ^ 2 / dotProduct sk yk`. -/
theorem secantRatioBounds_of_lowerLevelHessianBounds
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m M : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hUpper : HasLowerLevelHessianUpperBound D f x0 M)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    ‖sk‖ / ‖yk‖ ≤ 1 / m ∧
      ‖yk‖ / ‖sk‖ ≤ M ∧
      dotProduct sk yk / ‖sk‖ ^ (2 : ℕ) ≤ M ∧
      dotProduct sk yk / ‖yk‖ ^ (2 : ℕ) ≤ 1 / m ∧
      ‖yk‖ ^ (2 : ℕ) / dotProduct sk yk ≤ M := by
  constructor
  · exact
      stepNorm_div_secantNorm_le_inv_m_of_lowerLevelHessianLowerBound
        f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  constructor
  · exact
      secantNorm_div_stepNorm_le_M_of_lowerLevelHessianBounds
        f x0 xk sk yk hm hA hLower hUpper hxk hxk_add_sk hyk hsk
  constructor
  · exact
      secantCurvature_div_stepNormSq_le_M_of_lowerLevelHessianBounds
        f x0 xk sk yk hA hUpper hxk hxk_add_sk hyk hsk
  constructor
  · exact
      secantCurvature_div_secantNormSq_le_inv_m_of_lowerLevelHessianLowerBound
        f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  · exact
      secantNormSq_div_secantCurvature_le_M_of_lowerLevelHessianBounds
        f x0 xk sk yk hm hA hLower hUpper hxk hxk_add_sk hyk hsk

end Chapter05Lemma532
