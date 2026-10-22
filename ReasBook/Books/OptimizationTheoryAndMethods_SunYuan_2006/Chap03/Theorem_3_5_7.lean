/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_5_5

noncomputable section

open Filter
open scoped Topology

-- Domain sampling pass:
-- * primary domain: accumulation-point analysis for negative-curvature line-search
--   sequences for Chapter 3 negative-curvature methods;
-- * sampled source/core owners:
--   `IsNegativeCurvatureLineSearchSequence` from `Theorem_3_5_6`,
--   `hessianAt` / `HasPositiveSemidefiniteHessianAt` from `Definition_3_5_1`,
--   and the Euclidean Hessian-matrix bridge `hessianMatrixAt` from `Theorem_3_4_3`;
-- * owner abstraction chosen here:
--   the labeled source-facing theorem keeps the common Theorem 3.5.6-style
--   sequence hypotheses together with the additional constants and inequalities
--   `(3.5.40)`-`(3.5.42)`; its three conclusion clauses use the
--   canonical owners `IsStationaryPoint`, `HasPositiveSemidefiniteHessianAt`, and
--   `Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap 0`;
-- * primitive data on the source-facing side: the sequence data from Theorem 3.5.6; the
--   additional constants `c₁`, `c₂`, `c₃` and the source inequalities
--   `(3.5.40)`-`(3.5.42)` are kept explicit together with the sequence
--   `leastEigenvalueSeq` that records the most negative Hessian eigenvalue and the
--   normalized least-eigenvalue directions `d k`;
--   the positive-semidefinite and zero-eigenvalue clauses use the
--   finite-dimensional least-eigenvalue and matrix-positive-semidefinite
--   surfaces supplied by `hessianMatrixAt`, while the final zero-eigenvalue clause stays on
--   the intrinsic Hessian eigenvalue owner;
-- * bridge/view note: `hessianMatrixAt` is the existing project bridge from the intrinsic owner
--   `hessianAt` to the textbook Euclidean matrix surface, so no local spectral wrapper is kept.

section FiniteDimensionalNegativeCurvatureDirectionMethod

variable {n : ℕ}

variable (D : Set (NegativeCurvaturePoint n)) (f : NegativeCurvaturePoint n → ℝ)
  (x s d : ℕ → NegativeCurvaturePoint n)
  (backtrackingExponent : ℕ → ℕ) (x₀ : NegativeCurvaturePoint n) (ρ γ : ℝ)
variable (hD : IsOpen D) (hC2 : ContDiffOn ℝ 2 f D)
variable (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
variable (hx_mem : ∀ k, x k ∈ D)
variable (hs_bounded : Bornology.IsBounded (Set.range s))
variable (hd_bounded : Bornology.IsBounded (Set.range d))
variable (hLineSearch :
  IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
variable (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
variable (c₁ c₂ c₃ : ℝ) (leastEigenvalueSeq : ℕ → ℝ)
variable (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
variable (hStepNormLowerBound :
  ∀ k, c₃ * ‖gradient f (x k)‖ ≤ ‖s k‖)
variable (hLeastEigenvalue :
  ∀ k,
    IsLeast
      {μ : ℝ |
        Module.End.HasEigenvalue (Matrix.toEuclideanLin (hessianMatrixAt f (x k))) μ}
      (leastEigenvalueSeq k))
variable (hLeastEigenDirection :
  ∀ k, hessianAt f (x k) (d k) = leastEigenvalueSeq k • d k)
variable (hDirectionUnit : ∀ k, ‖d k‖ = 1)
variable (hCurvatureUpperBound :
  ∀ k, hessianQuadraticAt f (x k) (d k) ≤ c₂ * leastEigenvalueSeq k)
variable (hDescentLowerBound :
  ∀ k, c₁ * ‖s k‖ * ‖gradient f (x k)‖ ≤ -inner ℝ (s k) (gradient f (x k)))

include D f x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound

variable {xStar : NegativeCurvaturePoint n} {φ : ℕ → ℕ}
variable (hφ : StrictMono φ) (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))

include hφ hxStar

omit hD hC2 hs_bounded hd_bounded hφ
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound in
/-- Helper for Chapter03 Theorem 3.5.7: every accumulation point of the negative-curvature
line-search iterates remains in `negativeCurvatureLevelSet D f x₀`. -/
lemma accumulationPoint_mem_currentLevelSet :
    xStar ∈ negativeCurvatureLevelSet D f x₀ := by
  have hLevelEventually :
      ∀ᶠ n in atTop, (x ∘ φ) n ∈ negativeCurvatureLevelSet D f x₀ :=
    Filter.Eventually.of_forall fun n ↦
      negativeCurvature_iterates_mem_levelSet
        (D := D) (f := f) (x := x) (s := s) (d := d)
        (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
        hx_mem hLineSearch hDescentPair (φ n)
  -- Closedness of the compact level set keeps the subsequential limit inside the set.
  exact hLevelSetCompact.isClosed.mem_of_tendsto hxStar hLevelEventually

omit D s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenDirection hDirectionUnit hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: the matrix-side least-eigenvalue hypothesis is the same
as the intrinsic least-eigenvalue statement for `(hessianAt f (x k)).toLinearMap`. -/
lemma leastEigenvalueIsLeastHessianAt (k : ℕ) :
    IsLeast
      {μ : ℝ | Module.End.HasEigenvalue (hessianAt f (x k)).toLinearMap μ}
      (leastEigenvalueSeq k) := by
  -- Normalize the Euclidean matrix Hessian owner to the intrinsic Hessian operator once.
  have hEq :
      Matrix.toEuclideanLin (hessianMatrixAt f (x k)) =
        (hessianAt f (x k)).toLinearMap := by
    ext y
    unfold hessianMatrixAt
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp
  simpa [hEq] using hLeastEigenvalue k

omit D s backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: the least-eigenvalue sequence is the Hessian quadratic
form along the chosen unit least-eigenvalue directions. -/
lemma leastEigenvalue_eq_hessianQuadraticAlongDirection (k : ℕ) :
    leastEigenvalueSeq k = hessianQuadraticAt f (x k) (d k) := by
  -- Combine the eigenvector identity with the unit-length normalization of `d k`.
  calc
    leastEigenvalueSeq k = leastEigenvalueSeq k * ‖d k‖ ^ (2 : ℕ) := by
      simp [hDirectionUnit k]
    _ = hessianQuadraticAt f (x k) (d k) := by
      rw [hessianQuadraticAt_eq_mul_normSq_of_eigenvector (hLeastEigenDirection k)]

omit D f x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: a nonnegative multiple of `u k ^ 2` squeezed by a null
sequence forces `u k → 0`. -/
private theorem tendstoZeroOfMulSqLeOfTendstoZero
    {a : ℝ} (ha : 0 < a) {u v : ℕ → ℝ}
    (hbound : ∀ k, a * u k ^ 2 ≤ v k)
    (hv : Tendsto v atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  have hau_sq : Tendsto (fun k ↦ a * u k ^ 2) atTop (nhds 0) := by
    -- The lower squeeze is `0 ≤ a * u k ^ 2`, while the upper squeeze tends to `0`.
    refine squeeze_zero ?_ hbound hv
    intro k
    positivity
  have hu_sq : Tendsto (fun k ↦ u k ^ 2) atTop (nhds 0) := by
    -- Multiply by `1 / a` to isolate the square sequence.
    simpa [one_div, ha.ne', mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 1 / a) atTop (nhds (1 / a))).mul hau_sq)
  have hu_abs : Tendsto (fun k ↦ |u k|) atTop (nhds 0) := by
    -- Taking square roots converts convergence of squares to convergence of absolute values.
    simpa [Real.sqrt_sq_eq_abs] using Filter.Tendsto.sqrt hu_sq
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hu_abs

omit D x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: the difference of two Hessian quadratic forms is bounded
by the operator-norm difference of the Hessians times `‖y‖²`. -/
lemma abs_sub_hessianQuadraticAt_le
    (z₁ z₂ y : NegativeCurvaturePoint n) :
    |hessianQuadraticAt f z₁ y - hessianQuadraticAt f z₂ y| ≤
      ‖hessianAt f z₁ - hessianAt f z₂‖ * ‖y‖ ^ (2 : ℕ) := by
  -- Rewrite the difference as a single inner product against the Hessian difference.
  calc
    |hessianQuadraticAt f z₁ y - hessianQuadraticAt f z₂ y|
        = |inner ℝ y ((hessianAt f z₁) y) - inner ℝ y ((hessianAt f z₂) y)| := by
          simp [hessianQuadraticAt]
    _ = |inner ℝ y ((hessianAt f z₁) y - (hessianAt f z₂) y)| := by
      rw [inner_sub_right]
    _ = |inner ℝ y ((hessianAt f z₁ - hessianAt f z₂) y)| := by
      simp
    _ ≤ ‖y‖ * ‖(hessianAt f z₁ - hessianAt f z₂) y‖ := by
      exact abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖hessianAt f z₁ - hessianAt f z₂‖ * ‖y‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖hessianAt f z₁ - hessianAt f z₂‖ * ‖y‖ ^ (2 : ℕ) := by
      ring

omit D x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: at a `C²` point, the Hessian operator is symmetric. -/
lemma hessianAt_toLinearMap_isSymmetric_of_contDiffAt
    {z : NegativeCurvaturePoint n}
    (hC2z : ContDiffAt ℝ 2 f z) :
    ((hessianAt f z).toLinearMap).IsSymmetric := by
  intro y w
  -- Transfer symmetry of the second iterated derivative through the Hessian bridge.
  have hswap :
      (iteratedFDeriv ℝ 2 f z) ![y, w] = (iteratedFDeriv ℝ 2 f z) ![w, y] :=
    (hC2z.isSymmSndFDerivAt (n := (2 : WithTop ℕ∞)) (by simp)).iteratedFDeriv_cons
      (x := z) (v := y) (w := w)
  calc
    inner ℝ (hessianAt f z y) w = inner ℝ w (hessianAt f z y) := by
      rw [real_inner_comm]
    _ = (iteratedFDeriv ℝ 2 f z) ![y, w] :=
      inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
        (f := f) (x := z) (y := y) (z := w) hC2z
    _ = (iteratedFDeriv ℝ 2 f z) ![w, y] := hswap
    _ = inner ℝ y (hessianAt f z w) := by
      exact
        (inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
          (f := f) (x := z) (y := w) (z := y) hC2z).symm

omit D x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: the Rayleigh quotient of the Hessian operator is the
Hessian quadratic form divided by `‖y‖²`. -/
lemma rayleighQuotient_hessianAt_eq_diag_ratio
    {z y : NegativeCurvaturePoint n} :
    ContinuousLinearMap.rayleighQuotient (hessianAt f z) y =
      hessianQuadraticAt f z y / ‖y‖ ^ (2 : ℕ) := by
  -- Unfold the quotient once and rewrite it through the project Hessian owner.
  simp [ContinuousLinearMap.rayleighQuotient, hessianQuadraticAt,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]

omit D x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: a least Hessian eigenvalue bounds every fixed-direction
Hessian quadratic form from below by `λ * ‖y‖²`. -/
lemma leastEigenvalue_le_hessianQuadraticFixedDirection
    {z y : NegativeCurvaturePoint n} {lambda : ℝ}
    (hy : y ≠ 0)
    (hC2z : ContDiffAt ℝ 2 f z)
    (hLeast :
      IsLeast {μ : ℝ | Module.End.HasEigenvalue (hessianAt f z).toLinearMap μ} lambda) :
    lambda * ‖y‖ ^ (2 : ℕ) ≤ hessianQuadraticAt f z y := by
  -- Local instance justification (spectral): the Rayleigh infimum theorem needs `Nontrivial`,
  -- and the explicit nonzero direction `y` supplies it for this proof only.
  letI : Nontrivial (NegativeCurvaturePoint n) := ⟨⟨y, 0, hy⟩⟩
  have hSymm :
      ((hessianAt f z).toLinearMap).IsSymmetric :=
    hessianAt_toLinearMap_isSymmetric_of_contDiffAt
      (f := f) (z := z) hC2z
  have hBddBelow :
      BddBelow
        (Set.range
          (fun x : {x : NegativeCurvaturePoint n // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f z) x)) := by
    refine ⟨-‖hessianAt f z‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The Rayleigh quotient is uniformly bounded below by `-‖hessianAt f z‖`.
    have hv := (hessianAt f z).rayleighQuotient_le_norm v
    have habs := abs_le.mp hv
    linarith
  have hInfEigen :
      Module.End.HasEigenvalue
        (hessianAt f z).toLinearMap
        (⨅ x : {x : NegativeCurvaturePoint n // x ≠ 0},
          ContinuousLinearMap.rayleighQuotient (hessianAt f z) x) := by
    -- Symmetry identifies the Rayleigh infimum as an eigenvalue.
    simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply] using
      (LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
        (T := (hessianAt f z).toLinearMap) hSymm)
  have hRay :
      lambda ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f z) y := by
    calc
      lambda ≤
          ⨅ x : {x : NegativeCurvaturePoint n // x ≠ 0},
            ContinuousLinearMap.rayleighQuotient (hessianAt f z) x := hLeast.2 hInfEigen
      _ ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f z) y := ciInf_le hBddBelow ⟨y, hy⟩
  have hy_sq_pos : 0 < ‖y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr hy) 2
  have hScaled :
      lambda ≤ hessianQuadraticAt f z y / ‖y‖ ^ (2 : ℕ) := by
    simpa [rayleighQuotient_hessianAt_eq_diag_ratio] using hRay
  -- Multiply the Rayleigh lower bound back by `‖y‖²`.
  exact (le_div_iff₀ hy_sq_pos).mp hScaled

omit D x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar in
/-- Helper for Chapter03 Theorem 3.5.7: at a `C²` point, the Hessian operator has a least
eigenvalue in the finite-dimensional Euclidean setting. -/
lemma exists_isLeast_hessianAt_eigenvalue
    [Nontrivial (NegativeCurvaturePoint n)]
    {z : NegativeCurvaturePoint n}
    (hC2z : ContDiffAt ℝ 2 f z) :
    ∃ lambda : ℝ,
      IsLeast {μ : ℝ | Module.End.HasEigenvalue (hessianAt f z).toLinearMap μ} lambda := by
  let lambda : ℝ :=
    ⨅ x : {x : NegativeCurvaturePoint n // x ≠ 0},
      ContinuousLinearMap.rayleighQuotient (hessianAt f z) x
  have hSymm :
      ((hessianAt f z).toLinearMap).IsSymmetric :=
    hessianAt_toLinearMap_isSymmetric_of_contDiffAt
      (f := f) (z := z) hC2z
  have hBddBelow :
      BddBelow
        (Set.range
          (fun x : {x : NegativeCurvaturePoint n // x ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessianAt f z) x)) := by
    refine ⟨-‖hessianAt f z‖, ?_⟩
    intro r hr
    rcases hr with ⟨v, rfl⟩
    -- The operator norm bounds every Rayleigh quotient from below.
    have hv := (hessianAt f z).rayleighQuotient_le_norm v
    have habs := abs_le.mp hv
    linarith
  refine ⟨lambda, ?_⟩
  constructor
  · -- The Rayleigh infimum is itself an eigenvalue of the symmetric Hessian operator.
    simpa [lambda, ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
      using
        (LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
          (T := (hessianAt f z).toLinearMap) hSymm)
  · intro μ hμ
    rcases hμ.exists_hasEigenvector with ⟨u, hu⟩
    have hu_sq_ne : ‖u‖ ^ (2 : ℕ) ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hu.2)
    have hRayleighEq :
        ContinuousLinearMap.rayleighQuotient (hessianAt f z) u = μ := by
      -- Evaluate the Rayleigh quotient on the eigenvector itself.
      calc
        ContinuousLinearMap.rayleighQuotient (hessianAt f z) u =
            hessianQuadraticAt f z u / ‖u‖ ^ (2 : ℕ) := by
              rw [rayleighQuotient_hessianAt_eq_diag_ratio]
        _ = (μ * ‖u‖ ^ (2 : ℕ)) / ‖u‖ ^ (2 : ℕ) := by
              rw [hessianQuadraticAt_eq_mul_normSq_of_eigenvector hu.apply_eq_smul]
        _ = μ := by
              rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hu_sq_ne, mul_one]
    calc
      lambda ≤ ContinuousLinearMap.rayleighQuotient (hessianAt f z) u := by
        exact ciInf_le hBddBelow ⟨u, hu.2⟩
      _ = μ := hRayleighEq

omit c₂ leastEigenvalueSeq hc₂ hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound in
/-- Stationarity conclusion for Chapter03 Theorem 3.5.7: under the hypotheses above,
every accumulation point `x*`
of `{x_k}` is a stationary point of `f`. -/
theorem accumulationPoint_stationary :
    IsStationaryPoint f xStar := by
  have hxStar_level :
      xStar ∈ negativeCurvatureLevelSet D f x₀ :=
    by
      have hLevelEventually :
          ∀ᶠ n in atTop, (x ∘ φ) n ∈ negativeCurvatureLevelSet D f x₀ :=
        Filter.Eventually.of_forall fun n ↦
          negativeCurvature_iterates_mem_levelSet
            (D := D) (f := f) (x := x) (s := s) (d := d)
            (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
            hx_mem hLineSearch hDescentPair (φ n)
      exact hLevelSetCompact.isClosed.mem_of_tendsto hxStar hLevelEventually
  have hxStar_mem : xStar ∈ D := hxStar_level.1
  have hGradientPairing :
      Tendsto (fun k ↦ inner ℝ (s k) (gradient f (x k))) atTop (nhds 0) :=
    negativeCurvatureDirectionMethod_gradientPairing_tendsto_zero
      D f x s d backtrackingExponent x₀ ρ γ
      hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  have hGradientNorm :
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (nhds 0) := by
    -- The descent-angle and step-size lower bounds convert the pairing limit into `‖g_k‖ → 0`.
    refine
      tendstoZeroOfMulSqLeOfTendstoZero
        (a := c₁ * c₃)
        (u := fun k ↦ ‖gradient f (x k)‖)
        (v := fun k ↦ -inner ℝ (s k) (gradient f (x k)))
        (mul_pos hc₁ hc₃) ?_ ?_
    · intro k
      have hStepMul :
          c₃ * ‖gradient f (x k)‖ ^ (2 : ℕ) ≤ ‖s k‖ * ‖gradient f (x k)‖ := by
        have hmul :=
          mul_le_mul_of_nonneg_right
            (hStepNormLowerBound k)
            (norm_nonneg (gradient f (x k)))
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hScaled :
          c₁ * c₃ * ‖gradient f (x k)‖ ^ (2 : ℕ) ≤
            c₁ * ‖s k‖ * ‖gradient f (x k)‖ := by
        nlinarith [hStepMul, hc₁]
      exact le_trans hScaled (hDescentLowerBound k)
    · simpa using hGradientPairing.neg
  have hDifferentiable :
      DifferentiableAt ℝ f xStar := by
    -- The `C²` hypothesis on the open domain gives differentiability at the limit point.
    exact
      ((show ContDiffOn ℝ 1 f D from hC2.of_le (by norm_num)).contDiffAt
        (hD.mem_nhds hxStar_mem)).differentiableAt_one
  rw [isStationaryPoint_iff]
  refine ⟨?_, hDifferentiable⟩
  by_contra hGradient_ne
  obtain ⟨ε, hε_pos, N, hLower⟩ :=
    subsequenceGradientNorm_eventually_ge_of_limitGradient_ne_zero
      (f := f) (D := D) hD hC2 hxStar_mem hxStar hGradient_ne
  have hSubseqGradientNorm :
      Tendsto (fun n ↦ ‖gradient f (x (φ n))‖) atTop (nhds 0) :=
    hGradientNorm.comp hφ.tendsto_atTop
  have hEventuallySmall :
      ∀ᶠ n in atTop, ‖gradient f (x (φ n))‖ < ε := by
    exact hSubseqGradientNorm.eventually (Iio_mem_nhds hε_pos)
  rcases hEventuallySmall.exists_forall_of_atTop with ⟨Nsmall, hNsmall⟩
  let M : ℕ := max N Nsmall
  have hGe : ε ≤ ‖gradient f (x (φ M))‖ := hLower M (le_max_left _ _)
  have hLt : ‖gradient f (x (φ M))‖ < ε := hNsmall M (le_max_right _ _)
  exact not_lt_of_ge hGe hLt

omit c₁ c₂ c₃ hc₁ hc₂ hc₃ hStepNormLowerBound hCurvatureUpperBound
  hDescentLowerBound in
/-- Chapter03 Theorem 3.5.7: under the hypotheses above, the Hessian at an
accumulation point `x*` is positive semidefinite, formalized by
`HasPositiveSemidefiniteHessianAt f xStar`. -/
theorem accumulationPoint_hasPositiveSemidefiniteHessianAt :
    HasPositiveSemidefiniteHessianAt f xStar := by
  have hxStar_level :
      xStar ∈ negativeCurvatureLevelSet D f x₀ :=
    accumulationPoint_mem_currentLevelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hLevelSetCompact hx_mem hLineSearch hDescentPair hxStar
  have hxStar_mem : xStar ∈ D := hxStar_level.1
  have hC2xStar : ContDiffAt ℝ 2 f xStar :=
    hC2.contDiffAt (hD.mem_nhds hxStar_mem)
  have hHessianExists :
      DifferentiableAt ℝ (gradient f) xStar := by
    have hGradC1 : ContDiffAt ℝ 1 (gradient f) xStar := by
      change ContDiffAt ℝ 1
        (((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm) ∘ (fderiv ℝ f))
        xStar
      exact
        (LinearIsometryEquiv.contDiff
          ((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm)).contDiffAt.comp
          xStar hC2xStar.fderiv_right_succ
    exact hGradC1.differentiableAt_one
  have hLeastSubseq :
      Tendsto (fun k ↦ leastEigenvalueSeq (φ k)) atTop (nhds 0) := by
    -- Rewrite the curvature convergence along the unit least-eigenvalue directions.
    have hCurvatureSubseq :
        Tendsto (fun k ↦ hessianQuadraticAt f (x (φ k)) (d (φ k))) atTop (nhds 0) :=
      (negativeCurvatureDirectionMethod_curvature_tendsto_zero
        D f x s d backtrackingExponent x₀ ρ γ
        hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair).comp
        hφ.tendsto_atTop
    have hEq :
        (fun k ↦ leastEigenvalueSeq (φ k)) =ᶠ[atTop]
          fun k ↦ hessianQuadraticAt f (x (φ k)) (d (φ k)) := by
      exact Filter.Eventually.of_forall fun k ↦
        leastEigenvalue_eq_hessianQuadraticAlongDirection
          (f := f) (x := x) (d := d) (leastEigenvalueSeq := leastEigenvalueSeq)
          (hLeastEigenDirection := hLeastEigenDirection)
          (hDirectionUnit := hDirectionUnit) (k := φ k)
    exact Tendsto.congr' hEq.symm hCurvatureSubseq
  refine hasPositiveSemidefiniteHessianAt_of_not_isIndefinitePoint hHessianExists ?_
  -- Route correction: instead of building a second endpoint spectral theorem at `xStar`,
  -- contradict a fixed negative quadratic direction against `leastEigenvalueSeq (φ k) → 0`.
  intro hIndef
  rcases (isIndefinitePoint_iff f xStar).1 hIndef with ⟨y, hyNeg⟩
  have hy : y ≠ 0 := by
    intro hy0
    subst hy0
    simp [hessianQuadraticAt] at hyNeg
  have hy_sq_pos : 0 < ‖y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr hy) 2
  have hHessianCont :
      ContinuousAt (fun z : NegativeCurvaturePoint n ↦ hessianAt f z) xStar := by
    -- `hessianAt` is `fderiv ℝ (gradient f)` at a `C²` point.
    simpa [hessianAt] using
      continuousAt_gradientFDeriv_of_contDiffOn f hD hC2 hxStar_mem
  have hQuadraticSubseq :
      Tendsto (fun k ↦ hessianQuadraticAt f (x (φ k)) y) atTop
        (nhds (hessianQuadraticAt f xStar y)) := by
    have hApply :
        ContinuousAt (fun z : NegativeCurvaturePoint n ↦ hessianAt f z y) xStar :=
      hHessianCont.clm_apply continuousAt_const
    have hQuadCont :
        ContinuousAt (fun z : NegativeCurvaturePoint n ↦ hessianQuadraticAt f z y) xStar := by
      simpa [hessianQuadraticAt] using continuousAt_const.inner hApply
    exact hQuadCont.tendsto.comp hxStar
  have hHalfNeg :
      hessianQuadraticAt f xStar y < hessianQuadraticAt f xStar y / 2 := by
    nlinarith [hyNeg]
  have hEventuallyNeg :
      ∀ᶠ k in atTop, hessianQuadraticAt f (x (φ k)) y < hessianQuadraticAt f xStar y / 2 := by
    exact hQuadraticSubseq.eventually (Iio_mem_nhds hHalfNeg)
  let lambdaBarrier : ℝ := (hessianQuadraticAt f xStar y / 2) / ‖y‖ ^ (2 : ℕ)
  have hlambdaBarrier_neg : lambdaBarrier < 0 := by
    dsimp [lambdaBarrier]
    have hHalfNeg' : hessianQuadraticAt f xStar y / 2 < 0 := by
      nlinarith [hyNeg]
    exact div_neg_of_neg_of_pos hHalfNeg' hy_sq_pos
  have hEventuallyLe :
      ∀ᶠ k in atTop, leastEigenvalueSeq (φ k) ≤ lambdaBarrier := by
    filter_upwards [hEventuallyNeg] with k hk
    have hRayleighLower :
        leastEigenvalueSeq (φ k) * ‖y‖ ^ (2 : ℕ) ≤
          hessianQuadraticAt f (x (φ k)) y :=
      leastEigenvalue_le_hessianQuadraticFixedDirection
        (f := f) (z := x (φ k)) (y := y) (lambda := leastEigenvalueSeq (φ k))
        hy
        (hC2.contDiffAt (hD.mem_nhds (hx_mem (φ k))))
        (leastEigenvalueIsLeastHessianAt
          (f := f) (x := x) (leastEigenvalueSeq := leastEigenvalueSeq)
          (hLeastEigenvalue := hLeastEigenvalue) (k := φ k))
    exact (le_div_iff₀ hy_sq_pos).2 (le_trans hRayleighLower (le_of_lt hk))
  have hEventuallyGt :
      ∀ᶠ k in atTop, lambdaBarrier / 2 < leastEigenvalueSeq (φ k) := by
    have hHalfBarrier : lambdaBarrier / 2 < 0 := by
      nlinarith [hlambdaBarrier_neg]
    exact hLeastSubseq.eventually (Ioi_mem_nhds hHalfBarrier)
  rcases hEventuallyLe.exists_forall_of_atTop with ⟨Nle, hNle⟩
  rcases hEventuallyGt.exists_forall_of_atTop with ⟨Ngt, hNgt⟩
  let N : ℕ := max Nle Ngt
  have hLe : leastEigenvalueSeq (φ N) ≤ lambdaBarrier := hNle N (le_max_left _ _)
  have hGt : lambdaBarrier / 2 < leastEigenvalueSeq (φ N) := hNgt N (le_max_right _ _)
  have hBarrierOrder : lambdaBarrier < lambdaBarrier / 2 := by
    nlinarith [hlambdaBarrier_neg]
  have hLt : leastEigenvalueSeq (φ N) < lambdaBarrier / 2 := by
    exact lt_of_le_of_lt hLe hBarrierOrder
  exact not_lt_of_ge (le_of_lt hGt) hLt

omit c₁ c₂ c₃ hc₁ hc₂ hc₃ hStepNormLowerBound hLeastEigenvalue hCurvatureUpperBound
  hDescentLowerBound in
/-- Zero-eigenvalue conclusion for Chapter03 Theorem 3.5.7: under the hypotheses above,
the Hessian at an
accumulation point `x*` has `0` as an eigenvalue, formalized by
`Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap 0`. -/
theorem accumulationPoint_hessianAt_hasZeroEigenvalue :
    Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap 0 := by
  have hxStar_level :
      xStar ∈ negativeCurvatureLevelSet D f x₀ :=
    accumulationPoint_mem_currentLevelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hLevelSetCompact hx_mem hLineSearch hDescentPair hxStar
  have hxStar_mem : xStar ∈ D := hxStar_level.1
  have hHessianCont :
      ContinuousAt (fun z : NegativeCurvaturePoint n ↦ hessianAt f z) xStar := by
    -- The Hessian operator varies continuously on the `C²` domain.
    simpa [hessianAt] using
      continuousAt_gradientFDeriv_of_contDiffOn f hD hC2 hxStar_mem
  have hLeastSubseq :
      Tendsto (fun k ↦ leastEigenvalueSeq (φ k)) atTop (nhds 0) := by
    -- The least-eigenvalue sequence is the quadratic curvature sequence along `d k`.
    have hCurvatureSubseq :
        Tendsto (fun k ↦ hessianQuadraticAt f (x (φ k)) (d (φ k))) atTop (nhds 0) :=
      (negativeCurvatureDirectionMethod_curvature_tendsto_zero
        D f x s d backtrackingExponent x₀ ρ γ
        hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair).comp
        hφ.tendsto_atTop
    have hEq :
        (fun k ↦ leastEigenvalueSeq (φ k)) =ᶠ[atTop]
          fun k ↦ hessianQuadraticAt f (x (φ k)) (d (φ k)) := by
      exact Filter.Eventually.of_forall fun k ↦
        leastEigenvalue_eq_hessianQuadraticAlongDirection
          (f := f) (x := x) (d := d) (leastEigenvalueSeq := leastEigenvalueSeq)
          (hLeastEigenDirection := hLeastEigenDirection)
          (hDirectionUnit := hDirectionUnit) (k := φ k)
    exact Tendsto.congr' hEq.symm hCurvatureSubseq
  have hdSubseq_sphere :
      ∀ k, d (φ k) ∈ Metric.sphere (0 : NegativeCurvaturePoint n) 1 := by
    intro k
    rw [Metric.mem_sphere, dist_eq_norm]
    simp [hDirectionUnit (φ k)]
  -- Route correction: use compactness of the unit sphere and pass the eigenvector equation
  -- to the limit, rather than forcing a second least-eigenvalue endpoint theorem at `xStar`.
  rcases (isCompact_sphere (0 : NegativeCurvaturePoint n) 1).tendsto_subseq hdSubseq_sphere with
    ⟨dBar, hdBar_sphere, ψ, hψ, hψTendsto⟩
  have hxSubSub :
      Tendsto (fun k ↦ x (φ (ψ k))) atTop (nhds xStar) := by
    change Tendsto (((x ∘ φ) ∘ ψ)) atTop (nhds xStar)
    exact hxStar.comp hψ.tendsto_atTop
  have hLeastSubSub :
      Tendsto (fun k ↦ leastEigenvalueSeq (φ (ψ k))) atTop (nhds 0) := by
    change Tendsto (((fun k ↦ leastEigenvalueSeq (φ k)) ∘ ψ)) atTop (nhds 0)
    exact hLeastSubseq.comp hψ.tendsto_atTop
  have hdSubSub :
      Tendsto (fun k ↦ d (φ (ψ k))) atTop (nhds dBar) := by
    change Tendsto (((fun k ↦ d (φ k)) ∘ ψ)) atTop (nhds dBar)
    exact hψTendsto
  have hLeft :
      Tendsto
        (fun k ↦ hessianAt f (x (φ (ψ k))) (d (φ (ψ k))))
        atTop
        (nhds (hessianAt f xStar dBar)) := by
    have hHessianAlong :
        Tendsto (fun k ↦ hessianAt f (x (φ (ψ k)))) atTop (nhds (hessianAt f xStar)) :=
      hHessianCont.tendsto.comp hxSubSub
    -- Apply the continuous evaluation map to the convergent operator and direction subsequences.
    exact
      (Continuous.clm_apply continuous_fst continuous_snd).continuousAt.tendsto.comp
        (Filter.Tendsto.prodMk_nhds hHessianAlong hψTendsto)
  have hRight :
      Tendsto
        (fun k ↦ hessianAt f (x (φ (ψ k))) (d (φ (ψ k))))
        atTop
        (nhds 0) := by
    have hEigenEq :
        (fun k ↦ hessianAt f (x (φ (ψ k))) (d (φ (ψ k)))) =ᶠ[atTop]
          fun k ↦ leastEigenvalueSeq (φ (ψ k)) • d (φ (ψ k)) := by
      exact Filter.Eventually.of_forall fun k ↦ hLeastEigenDirection (φ (ψ k))
    have hSmul :
        Tendsto (fun k ↦ leastEigenvalueSeq (φ (ψ k)) • d (φ (ψ k))) atTop
          (nhds ((0 : ℝ) • dBar)) := by
      exact hLeastSubSub.smul hdSubSub
    exact Tendsto.congr' hEigenEq.symm (by simpa using (hSmul : Tendsto
      (fun k ↦ leastEigenvalueSeq (φ (ψ k)) • d (φ (ψ k))) atTop
      (nhds ((0 : ℝ) • dBar))))
  have hZeroVector :
      hessianAt f xStar dBar = 0 :=
    tendsto_nhds_unique hLeft hRight
  have hdBar_ne : dBar ≠ 0 := by
    have hdBar_norm : ‖dBar‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hdBar_sphere
    exact norm_ne_zero_iff.mp (by simp [hdBar_norm])
  -- Package the limiting nonzero direction as a `0`-eigenvector of the Hessian operator.
  exact Module.End.hasEigenvalue_of_hasEigenvector <|
    (Module.End.hasEigenvector_iff).2 <|
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hZeroVector), hdBar_ne⟩

omit D f x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  c₁ c₂ c₃ leastEigenvalueSeq hc₁ hc₂ hc₃ hStepNormLowerBound
  hLeastEigenvalue hLeastEigenDirection hDirectionUnit
  hCurvatureUpperBound hDescentLowerBound hφ hxStar

end FiniteDimensionalNegativeCurvatureDirectionMethod
