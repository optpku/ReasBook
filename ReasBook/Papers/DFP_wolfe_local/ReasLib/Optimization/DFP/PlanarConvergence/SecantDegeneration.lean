module

public import ReasLib.Optimization.DFP.SecantDegeneration
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.CStarAlgebra.Matrix

public section

noncomputable section

open Set Filter
open scoped Matrix Topology ContDiff

namespace DFP.PlanarConvergence.SecantDegeneration

/-- Helper for lem:planar-degeneration: affine-line differentiation identifies the
ordinary derivative with the source directional gradient pairing. -/
theorem hasDerivAt_line_objective {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {f : F → ℝ} (hf : Differentiable ℝ f)
    (x v : F) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa only [one_smul] using (hasDerivAt_id' t).smul_const v |>.const_add x
  have hcomp := (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
  convert! hcomp using 1
  simp only [inner_gradient_left]

/-- Helper for lem:planar-degeneration: C² strong convexity gives the source Hessian
lower bound by differentiating the convex quadratic-adjusted line restriction twice. -/
theorem hessianLowerBound_of_strongConvex {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {f : F → ℝ} {μ : ℝ}
    (hf : ContDiff ℝ 2 f) (hstrong : StrongConvexOn Set.univ μ f) (x v : F) :
    μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v := by
  have horder : (2 : WithTop ℕ∞) = (1 : ℕ∞) + 1 := by norm_num
  have hgradient : Differentiable ℝ (gradient f) := by
    rw [horder] at hf
    exact hf.gradient_succ.differentiable_one
  have hdiff : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hconvex := strongConvexOn_iff_convex.mp hstrong
  have hlineConvex : ConvexOn ℝ Set.univ
      (fun t : ℝ ↦ f (x + t • v) - μ / 2 * ‖x + t • v‖ ^ 2) := by
    have h := hconvex.comp_affineMap (AffineMap.lineMap x (x + v))
    simpa only [Set.preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
      add_sub_cancel_left, add_comm] using h
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ ↦ f (x + s • v) - μ / 2 * ‖x + s • v‖ ^ 2)
      (inner ℝ (gradient f (x + t • v)) v - μ * inner ℝ (x + t • v) v) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
      simpa only [one_smul] using (hasDerivAt_id' t).smul_const v |>.const_add x
    have hquad := hline.norm_sq.const_mul (μ / 2)
    have hquad' : HasDerivAt (fun s : ℝ ↦ μ / 2 * ‖x + s • v‖ ^ 2)
        (μ * inner ℝ (x + t • v) v) t := by
      convert! hquad using 1
      simp only [real_inner_comm v (x + t • v)]
      ring
    exact (hasDerivAt_line_objective hdiff x v t).sub hquad'
  have hmono : Monotone
      (fun t : ℝ ↦ inner ℝ (gradient f (x + t • v)) v - μ * inner ℝ (x + t • v) v) := by
    have h := hlineConvex.monotoneOn_deriv
      (fun t _ ↦ (hderiv t).differentiableAt)
    intro a b hab
    simpa only [(hderiv a).deriv, (hderiv b).deriv] using h (mem_univ a) (mem_univ b) hab
  have hlineZero : HasDerivAt (fun s : ℝ ↦ x + s • v) v 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v |>.const_add x
  have hgradLine := (hgradient (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hlineZero
  have hinner := hgradLine.inner ℝ (hasDerivAt_const (0 : ℝ) v)
  have hlinear := (hlineZero.inner ℝ (hasDerivAt_const (0 : ℝ) v)).const_mul μ
  have hsecond := hinner.sub hlinear
  have hnonneg := hsecond.nonneg_of_monotone hmono
  simpa only [zero_smul, add_zero, inner_zero_right, zero_add,
    real_inner_self_eq_norm_sq, sub_nonneg] using hnonneg


/-- Helper for eq:planar-scalar-definition and lem:planar-degeneration: the actual
source step of the canonical general secant-search interface. -/
def step (iteration : DFP.SecantIteration 2) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  iteration.point (k + 1) - iteration.point k

/-- Helper for lem:planar-degeneration: evaluation of the original source step. -/
theorem step_def (iteration : DFP.SecantIteration 2) (k : ℕ) :
    step iteration k = iteration.point (k + 1) - iteration.point k := by
  rfl

/-- Helper for eq:planar-scalar-definition and lem:planar-degeneration: the original
gradient secant, with the canonical interface's genuine objective gradients. -/
def secant (iteration : DFP.SecantIteration 2) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)

/-- Helper for lem:planar-degeneration: evaluation of the original gradient secant. -/
theorem secant_def (iteration : DFP.SecantIteration 2) (k : ℕ) :
    secant iteration k = gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k) := by
  rfl

/-- Helper for eq:planar-scalar-definition and lem:planar-degeneration: exactly the
source scalar `κ_k = s_kᵀ y_k / ell_k²`. -/
def curvature (iteration : DFP.SecantIteration 2) (k : ℕ) : ℝ :=
  inner ℝ (step iteration k) (secant iteration k) / ‖step iteration k‖ ^ 2

/-- Helper for lem:planar-degeneration: the exact source curvature formula. -/
theorem curvature_def (iteration : DFP.SecantIteration 2) (k : ℕ) :
    curvature iteration k = inner ℝ (step iteration k) (secant iteration k) /
      ‖step iteration k‖ ^ 2 := by
  rfl

/-- Helper for eq:planar-scalar-definition and lem:planar-degeneration: the ORIGINAL
source coefficient at k≥1 is `λ_k = κ_(k−1) det H_k`. Nat subtraction merely totalizes at zero. -/
def freeCoefficient (iteration : DFP.SecantIteration 2) (k : ℕ) : ℝ :=
  curvature iteration (k - 1) * (iteration.inverseHessian k).det

/-- Helper for lem:planar-degeneration: the public coefficient retains the source
index k and original matrix H_k. -/
theorem freeCoefficient_def (iteration : DFP.SecantIteration 2) (k : ℕ) :
    freeCoefficient iteration k = curvature iteration (k - 1) *
      (iteration.inverseHessian k).det := by
  rfl

/-- Helper for lem:planar-degeneration: the existing internal coefficient at step k
is EXACTLY the manuscript's λ_(k+1), with no altered invariant. -/
theorem freeCoefficient_succ (iteration : DFP.SecantIteration 2) (k : ℕ) :
    freeCoefficient iteration (k + 1) =
      (inner ℝ (secant iteration k) (step iteration k) / ‖step iteration k‖ ^ 2) *
        (iteration.inverseHessian (k + 1)).det := by
  rw [freeCoefficient_def, Nat.add_sub_cancel, curvature_def, real_inner_comm]

/-- Helper for lem:planar-degeneration: source strong convexity controls each
original normalized secant curvature from below. -/
theorem curvature_lower (iteration : DFP.SecantIteration 2) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k) (k : ℕ) : μ ≤ curvature iteration k := by
  have h := DFP.SecantIteration.normalizedOrbitCurvatureLowerBound iteration hf hμ
    hlower k (hStep k)
  simpa only [curvature_def, step_def, secant_def, normalizedSecantCurvature,
    real_inner_comm] using h

/-- Helper for lem:planar-degeneration: the source coefficient is strictly positive
at every original index k≥1, independently of nonconvergence. -/
theorem freeCoefficient_pos (iteration : DFP.SecantIteration 2) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k) (k : ℕ) :
    0 < freeCoefficient iteration k := by
  rw [freeCoefficient_def]
  exact mul_pos (hμ.trans_le (curvature_lower iteration hf hμ hlower hStep (k - 1)))
    (iteration.inverseHessianPosDef k).det_pos

/-- Helper for lem:planar-degeneration: the generic source free-coefficient proof
gives the paper's original k-indexed product bound and limit, using only secant laws. -/
theorem sourceFreeCoefficientDegeneration (iteration : DFP.SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ z, iteration.objective xstar ≤ iteration.objective z)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    (∃ C > 0, ∀ᶠ k in atTop, 0 < freeCoefficient iteration k ∧
      freeCoefficient iteration k ≤ C * ‖step iteration (k - 1)‖ * ‖step iteration k‖) ∧
      Tendsto (freeCoefficient iteration) atTop (𝓝 0) := by
  have hcore := DFP.SecantIteration.orbitFreeCoefficientDegeneration iteration hf hμ
    hlower hStep hw hmin hnot
  have hshift : Tendsto (fun k ↦ freeCoefficient iteration (k + 1)) atTop (𝓝 0) := by
    simpa only [freeCoefficient_succ, step_def, secant_def] using hcore.2
  refine ⟨?_, (tendsto_add_atTop_iff_nat 1).mp hshift⟩
  obtain ⟨C, hC, hbound⟩ := hcore.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk
  have hprevious : N ≤ k - 1 := by omega
  have hindex : k - 1 + 1 = k := by omega
  have hraw := hN (k - 1) hprevious
  simpa only [hindex, freeCoefficient_def, curvature_def, step_def, secant_def,
    real_inner_comm] using hraw

/-- Helper for lem:planar-degeneration: source determinant decay is derived from
λ_k=κ_(k−1) det H_k and the positive source lower curvature bound. -/
theorem determinant_tendsto_zero (iteration : DFP.SecantIteration 2) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hfree : Tendsto (freeCoefficient iteration) atTop (𝓝 0)) :
    Tendsto (fun k ↦ (iteration.inverseHessian k).det) atTop (𝓝 0) := by
  have hbound (k : ℕ) : (iteration.inverseHessian k).det ≤ freeCoefficient iteration k / μ := by
    apply (le_div_iff₀ hμ).mpr
    have hκ := curvature_lower iteration hf hμ hlower hStep (k - 1)
    have hdet := (iteration.inverseHessianPosDef k).det_pos.le
    simpa only [freeCoefficient_def, mul_comm] using mul_le_mul_of_nonneg_right hκ hdet
  have hupper : Tendsto (fun k ↦ freeCoefficient iteration k / μ) atTop (𝓝 0) := by
    simpa only [zero_div] using hfree.div_const μ
  exact squeeze_zero (fun k ↦ (iteration.inverseHessianPosDef k).det_pos.le) hbound hupper

/-- Helper for lem:planar-degeneration: the Rayleigh quotient of a unit vector is
bounded by the canonical largest ordered Hermitian eigenvalue. -/
theorem quadraticForm_le_maxEigenvalue {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.IsHermitian) (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) u ≤ hA.eigenvalues₀ 0 := by
  let T := Matrix.toEuclideanLin A
  have hs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have happly (v : EuclideanSpace ℝ (Fin 2)) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) A v = T v := by
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 2) ↦ L v) (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A)
  let q := fun v : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0} ↦
    inner ℝ (T v) v / ‖(v : EuclideanSpace ℝ (Fin 2))‖ ^ 2
  have hbounded : BddAbove (Set.range q) := by
    refine ⟨‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖, ?_⟩
    rintro z ⟨v, rfl⟩
    have hnorm := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient_le_norm v
    have hnorm' : |q v| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
      simpa only [q, ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
        happly] using hnorm
    exact (le_abs_self _).trans hnorm'
  have heigen : Module.End.HasEigenvalue T (⨆ v, q v) := by
    convert! hs.hasEigenvalue_iSup_of_finiteDimensional using 1
  obtain ⟨i, hi⟩ := hs.exists_eigenvalues_eq finrank_euclideanSpace heigen
  have hune : u ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hu
    exact zero_ne_one hu
  have hunit : inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) u ≤ ⨆ v, q v := by
    have hbound := le_ciSup hbounded (⟨u, hune⟩ : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0})
    simpa only [q, hu, one_pow, div_one, happly] using hbound
  have hmax : (⨆ v, q v) ≤ hA.eigenvalues₀ 0 := by
    rw [← hi, Matrix.IsHermitian.eigenvalues₀]
    exact hs.eigenvalues_antitone finrank_euclideanSpace (Fin.zero_le i)
  exact hunit.trans hmax

/-- Helper for lem:planar-degeneration: the canonical ordered eigenvalues of a
Hermitian planar matrix have product equal to its determinant. -/
theorem orderedEigenvalues_product {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ 1 * hA.eigenvalues₀ 0 = A.det := by
  have hprod : A.det = ∏ i : Fin (Fintype.card (Fin 2)), hA.eigenvalues₀ i := by
    rw [hA.det_eq_prod_eigenvalues]
    exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm.prod_comp
      hA.eigenvalues₀
  have hprod' : A.det = ∏ i : Fin 2, hA.eigenvalues₀ i := hprod
  rw [Fin.prod_univ_two] at hprod'
  convert! hprod'.symm using 1
  exact mul_comm _ _

/-- Helper for lem:planar-degeneration: every canonical ordered eigenvalue of a
positive-definite planar matrix is positive. -/
theorem orderedEigenvalue_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (i : Fin (Fintype.card (Fin 2))) : 0 < hA.isHermitian.eigenvalues₀ i := by
  let e : Fin (Fintype.card (Fin 2)) ≃ Fin 2 := Fintype.equivOfCardEq
    (Fintype.card_fin (Fintype.card (Fin 2)))
  have hp := hA.eigenvalues_pos (e i)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hp

/-- Helper for eq:planar-secant-representation and lem:planar-degeneration: the
first matrix entry in the source step frame is the source longitudinal Rayleigh form. -/
theorem frame_first_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) u =
      ((EuclideanPlane.frame u).transpose * A * EuclideanPlane.frame u) 0 0 := by
  have hoperator : Matrix.toEuclideanCLM (𝕜 := ℝ) A u =
      WithLp.toLp 2 (A *ᵥ WithLp.ofLp u) := by
    simpa only [WithLp.toLp_ofLp] using Matrix.toEuclideanCLM_toLp A (WithLp.ofLp u)
  rw [hoperator, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    planarFrameFirstColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for lem:planar-degeneration: the source secant representation gives
`λ_max(H_(k+1)) ≥ uᵀ H_(k+1) u ≥ 1/M` for the actual normalized previous step. -/
theorem source_maxEigenvalue_lower (iteration : DFP.SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ M > 0, ∀ k,
      let u := ‖step iteration k‖⁻¹ • step iteration k
      1 / M ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1)) u) u ∧
        inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1)) u) u ≤
          (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 0 := by
  obtain ⟨M, hM, hbounds⟩ := DFP.SecantIteration.secantBoundsAlongOrbit iteration
    hf hμ hlower hStep hw
  refine ⟨M, hM, ?_⟩
  intro k
  let u := ‖step iteration k‖⁻¹ • step iteration k
  let v := ‖step iteration k‖⁻¹ • secant iteration k
  let R := EuclideanPlane.frame u
  let K := R.transpose * iteration.inverseHessian (k + 1) * R
  have hs : 0 < ‖step iteration k‖ := by
    simpa only [step_def] using DFP.SecantIteration.orbitStepNormPos iteration k (hStep k)
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hs.ne']
  have hv : ‖v‖ ≤ M := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← div_eq_inv_mul]
    apply (div_le_iff₀ hs).mpr
    simpa only [secant_def, step_def] using (hbounds k).1
  have hκ : μ ≤ inner ℝ u v := by
    simpa only [u, v, step_def, secant_def] using
      DFP.SecantIteration.normalizedOrbitCurvatureLowerBound iteration hf hμ hlower k (hStep k)
  have hκpos := hμ.trans_le hκ
  have hκupper : inner ℝ u v ≤ M := by
    have hpair := real_inner_le_norm u v
    rw [hu, one_mul] at hpair
    exact hpair.trans hv
  have hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    dsimp only [R, u]
    exact normalizedStepFrameOrthogonal (step iteration k) (norm_pos_iff.mp hs)
  have hK : K.PosDef := orthogonalCoordinatesPosDef
    (iteration.inverseHessianPosDef (k + 1)) hR
  have hsec : iteration.inverseHessian (k + 1) *ᵥ WithLp.ofLp v = WithLp.ofLp u := by
    simpa only [u, v, step_def, secant_def] using
      DFP.SecantIteration.normalizedOrbitSecantEquation iteration k
  have hsecK : K *ᵥ ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] = ![1, 0] :=
    planarSecantFrameSpecification (iteration.inverseHessian (k + 1)) u v hu hsec
  have hentry := secantLongitudinal hK.isHermitian hκpos.ne' hsecK
  have hterm : 0 ≤ K 1 1 * inner ℝ (EuclideanPlane.perp u) v ^ 2 / (inner ℝ u v) ^ 2 :=
    div_nonneg (mul_nonneg (hK.diag_pos (i := 1)).le (sq_nonneg _)) (sq_nonneg _)
  have hdiag : 1 / inner ℝ u v ≤ K 0 0 := by
    rw [hentry]
    exact le_add_of_nonneg_right hterm
  have hfrac : 1 / M ≤ 1 / inner ℝ u v :=
    div_le_div_of_nonneg_left zero_le_one hκpos hκupper
  have hphysical : inner ℝ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1)) u) u = K 0 0 :=
    frame_first_quadratic (iteration.inverseHessian (k + 1)) u
  exact ⟨(hfrac.trans hdiag).trans_eq hphysical.symm,
    quadraticForm_le_maxEigenvalue (iteration.inverseHessianPosDef (k + 1)).isHermitian u hu⟩

/-- Helper for lem:planar-degeneration: determinant decay and the source positive
largest-eigenvalue lower bound force the ACTUAL canonical smallest eigenvalue to zero. -/
theorem source_smallestEigenvalue_tendsto_zero (iteration : DFP.SecantIteration 2)
    {μ c₁ c₂ : ℝ} (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hlower : ∀ z v, μ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hdet : Tendsto (fun k ↦ (iteration.inverseHessian k).det) atTop (𝓝 0)) :
    Tendsto (fun k ↦ (iteration.inverseHessianPosDef k).isHermitian.eigenvalues₀ 1)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hmax⟩ := source_maxEigenvalue_lower iteration hf hμ hlower hStep hw
  have hbound (k : ℕ) :
      (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1 ≤
        M * (iteration.inverseHessian (k + 1)).det := by
    have hlowerMax := (hmax k).1.trans (hmax k).2
    have hscaled : 1 ≤ M * (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 0 := by
      nlinarith [(div_le_iff₀ hM).mp hlowerMax]
    have hpositive := (orderedEigenvalue_pos (iteration.inverseHessianPosDef (k + 1)) 1).le
    have hproduct := orderedEigenvalues_product
      (iteration.inverseHessianPosDef (k + 1)).isHermitian
    calc
      (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1 =
          1 * (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1 := by ring
      _ ≤ (M * (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 0) *
          (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1 :=
        mul_le_mul_of_nonneg_right hscaled hpositive
      _ = M * ((iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1 *
          (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 0) := by ring
      _ = M * (iteration.inverseHessian (k + 1)).det := by rw [hproduct]
  have hdetShift : Tendsto (fun k ↦ (iteration.inverseHessian (k + 1)).det) atTop (𝓝 0) :=
    hdet.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun k ↦ M * (iteration.inverseHessian (k + 1)).det) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdetShift.const_mul M
  have hminimum : Tendsto
      (fun k ↦ (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1)
      atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (orderedEigenvalue_pos (iteration.inverseHessianPosDef (k + 1)) 1).le)
      hbound hupper
  exact (tendsto_add_atTop_iff_nat 1).mp hminimum

/-- Helper for lem:planar-degeneration: all source conclusions for the original
k-indexed free coefficient and the genuine Euclidean operator and eigenvalue norms. -/
structure DegenerationEstimates (iteration : DFP.SecantIteration 2) : Prop where
  /-- Helper for lem:planar-degeneration: the source coefficient is positive for k≥1. -/
  positive : ∀ k, 1 ≤ k → 0 < freeCoefficient iteration k
  /-- Helper for lem:planar-degeneration and eq:planar-degeneration: the exact
  original adjacent-step product bound. -/
  product_bound : ∃ C > 0, ∀ᶠ k in atTop,
    freeCoefficient iteration k ≤ C * ‖step iteration (k - 1)‖ * ‖step iteration k‖
  /-- Helper for lem:planar-degeneration and eq:planar-degeneration: the original
  source coefficient tends to zero. -/
  coefficient_limit : Tendsto (freeCoefficient iteration) atTop (𝓝 0)
  /-- Helper for lem:planar-degeneration: the FULL matrix sequence, including H₀, is bounded. -/
  operator_bound : ∃ B > 0, ∀ k,
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)‖ ≤ B
  /-- Helper for lem:planar-degeneration: the original matrix determinants tend to zero. -/
  determinant_limit : Tendsto (fun k ↦ (iteration.inverseHessian k).det) atTop (𝓝 0)
  /-- Helper for lem:planar-degeneration: the canonical smallest ordered
  eigenvalue tends to zero. -/
  smallest_eigenvalue_limit : Tendsto
    (fun k ↦ (iteration.inverseHessianPosDef k).isHermitian.eigenvalues₀ 1) atTop (𝓝 0)

/-- lem:planar-degeneration (v21 Lemma7, GENERAL secant-search sequence).
A C² globally μ-strongly convex objective has a unique minimizer. Under nonconvergence,
an arbitrary nonstationary positive-definite search sequence satisfying fixed weak Wolfe
and the PREVIOUS SECANT equation has the source positive coefficient, adjacent-step
product bound and limit zero, a bounded full operator sequence, and smallest eigenvalue
tending to zero. No DFP update or Hessian Lipschitz hypothesis is imposed. -/
theorem planarDegeneration (iteration : DFP.SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective)
    (hstrong : StrongConvexOn Set.univ μ iteration.objective)
    (hμ : 0 < μ) (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃! xstar : EuclideanSpace ℝ (Fin 2),
      (∀ z, iteration.objective xstar ≤ iteration.objective z) ∧
        (¬ Tendsto iteration.point atTop (𝓝 xstar) → DegenerationEstimates iteration) := by
  have hlower := hessianLowerBound_of_strongConvex hf hstrong
  obtain ⟨xstar, hmin, hunique⟩ := existsUniqueGlobalMinimizerOfHessian hf hμ hlower
  refine ⟨xstar, ⟨hmin, ?_⟩, ?_⟩
  · intro hnot
    obtain ⟨hproduct, hlimit⟩ := sourceFreeCoefficientDegeneration iteration hf hμ hlower
      hStep hw hmin hnot
    have hdet := determinant_tendsto_zero iteration hf hμ hlower hStep hlimit
    have hop := DFP.SecantIteration.orbitInverseHessianBoundedOfNonconvergence iteration
      hf hμ hlower hStep hw hmin hnot
    obtain ⟨C, hC, hbound⟩ := hproduct
    have hbound' : ∃ C > 0, ∀ᶠ k in atTop,
        freeCoefficient iteration k ≤ C * ‖step iteration (k - 1)‖ * ‖step iteration k‖ :=
      ⟨C, hC, hbound.mono (fun k hk ↦ hk.2)⟩
    exact ⟨fun k _ ↦ freeCoefficient_pos iteration hf hμ hlower hStep k,
      hbound', hlimit, hop, hdet,
      source_smallestEigenvalue_tendsto_zero iteration hf hμ hlower hStep hw hdet⟩
  · intro z hz
    exact hunique z hz.1

end DFP.PlanarConvergence.SecantDegeneration
