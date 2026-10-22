/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.V21.IdentityInitialization

public section

noncomputable section

open Filter DFP.Polar
open scoped MatrixOrder Topology InnerProduct

namespace DFPWolfe.V21.IdentityQuantitative

/-- Helper for cor:identity-initialization: every canonical decreasing-order
eigenvalue of a positive-definite real planar matrix is strictly positive. -/
theorem orderedEigenvalue_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (i : Fin (Fintype.card (Fin 2))) : 0 < hA.isHermitian.eigenvalues₀ i := by
  let e : Fin (Fintype.card (Fin 2)) ≃ Fin 2 := Fintype.equivOfCardEq
    (Fintype.card_fin (Fintype.card (Fin 2)))
  have hp := hA.eigenvalues_pos (e i)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hp

/-- Helper for cor:identity-initialization: the canonical smallest and largest
Hermitian eigenvalues are exact scalar Loewner bounds for the original matrix. -/
theorem orderedEigenvalue_bounds {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ 1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ A ∧
      A ≤ hA.eigenvalues₀ 0 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hlower : algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (hA.eigenvalues₀ 1) ≤ A := by
    apply algebraMap_le_of_le_spectrum _ hA.isSelfAdjoint
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Matrix.IsHermitian.eigenvalues]
    exact hA.eigenvalues₀_antitone (Fin.le_last _)
  have hupper : A ≤ algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (hA.eigenvalues₀ 0) := by
    apply le_algebraMap_of_spectrum_le _ hA.isSelfAdjoint
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Matrix.IsHermitian.eigenvalues]
    exact hA.eigenvalues₀_antitone (Fin.zero_le _)
  simpa only [Algebra.algebraMap_eq_smul_one] using And.intro hlower hupper

/-- Helper for cor:identity-initialization: Euclidean realization preserves
the Loewner order of real matrices. -/
theorem matrixOperator_mono {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A ≤ Matrix.toEuclideanCLM (𝕜 := ℝ) B := by
  rw [ContinuousLinearMap.le_def, ← map_sub]
  exact Matrix.isPositive_toEuclideanCLM_iff.mpr (Matrix.le_iff.mp h)

/-- Helper for cor:identity-initialization: both `P†P` and `PP†` of the literal
positive square root have the exact original canonical eigenvalue bounds. -/
theorem positiveRoot_spectral_bounds {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    let P := hA.sqrtEquiv.toContinuousLinearMap
    let lo := hA.isHermitian.eigenvalues₀ 1
    let hi := hA.isHermitian.eigenvalues₀ 0
    (lo • 1 ≤ P.pullback 1 ∧ P.pullback 1 ≤ hi • 1) ∧
      (lo • 1 ≤ P.pushforward 1 ∧ P.pushforward 1 ≤ hi • 1) := by
  dsimp only
  have hmatrix := orderedEigenvalue_bounds hA.isHermitian
  have hlower := matrixOperator_mono hmatrix.1
  have hupper := matrixOperator_mono hmatrix.2
  simp only [map_smul, map_one] at hlower hupper
  have hpull : hA.sqrtEquiv.toContinuousLinearMap.pullback 1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A := by
    rw [ContinuousLinearMap.pullback_one_eq_pushforward_one _ hA.sqrtEquiv_isSelfAdjoint,
      ← hA.sqrtEquiv_pushforward_one]
  rw [hpull, ← hA.sqrtEquiv_pushforward_one]
  exact ⟨⟨hlower, hupper⟩, ⟨hlower, hupper⟩⟩

/-- Helper for cor:identity-initialization: a precise adjoint lower singular
value bound passes the FULL source gradient limit to the transformed liminf. -/
theorem pulledGradient_liminf_ge {n : ℕ} {c₁ c₂ q : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (hq : 0 ≤ q)
    (hlower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
      P.toContinuousLinearMap.pushforward 1) :
    Real.sqrt q * c.gradientLimit ≤
      liminf (fun k ↦ ‖IdentityInitialization.pulledGradients c.iteration P k‖) atTop := by
  have hlimit := c.gradientNormTendsto.const_mul (Real.sqrt q)
  have hpointwise : ∀ᶠ k in atTop,
      Real.sqrt q * ‖DFP.gradients c.iteration.objective c.iteration.point k‖ ≤
        ‖IdentityInitialization.pulledGradients c.iteration P k‖ := by
    filter_upwards [] with k
    rw [IdentityInitialization.pulledGradients_apply]
    exact P.toContinuousLinearMap.norm_adjoint_lower_bound hq hlower _
  obtain ⟨B, hB⟩ := c.gradientNormTendsto.isBoundedUnder_le
  have hupper : ∀ᶠ k in atTop, ‖IdentityInitialization.pulledGradients c.iteration P k‖ ≤
      ‖P.toContinuousLinearMap.adjoint‖ * B := by
    filter_upwards [hB] with k hk
    rw [IdentityInitialization.pulledGradients_apply]
    exact (P.toContinuousLinearMap.adjoint.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
  have hmono := liminf_le_liminf hpointwise hlimit.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_eventually_le atTop hupper)
  rwa [hlimit.liminf_eq] at hmono

/-- Helper for cor:identity-initialization: the source initial minimum is the
canonical Hermitian eigenvalue at decreasing-order index one. -/
def initialMinEigenvalue {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) : ℝ :=
  (c.iteration.inverseHessianPosDef 0).isHermitian.eigenvalues₀ 1

/-- Helper for cor:identity-initialization: the source initial maximum is the
canonical Hermitian eigenvalue at decreasing-order index zero. -/
def initialMaxEigenvalue {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) : ℝ :=
  (c.iteration.inverseHessianPosDef 0).isHermitian.eigenvalues₀ 0

/-- Helper for cor:identity-initialization: the initial minimum uses the
original initial inverse matrix and canonical source eigenvalue. -/
theorem initialMinEigenvalue_def {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) :
    initialMinEigenvalue c =
      (c.iteration.inverseHessianPosDef 0).isHermitian.eigenvalues₀ 1 := by
  rfl

/-- Helper for cor:identity-initialization: the initial maximum uses the
original initial inverse matrix and canonical source eigenvalue. -/
theorem initialMaxEigenvalue_def {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) :
    initialMaxEigenvalue c =
      (c.iteration.inverseHessianPosDef 0).isHermitian.eigenvalues₀ 0 := by
  rfl

/-- Helper for cor:identity-initialization: both extremal eigenvalues of the
actual positive-definite initial inverse matrix are positive. -/
theorem initialEigenvalues_pos {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) :
    0 < initialMinEigenvalue c ∧ 0 < initialMaxEigenvalue c := by
  exact ⟨orderedEigenvalue_pos (c.iteration.inverseHessianPosDef 0) 1,
    orderedEigenvalue_pos (c.iteration.inverseHessianPosDef 0) 0⟩

/-- Helper for cor:identity-initialization: the Hessian of the SAME literal
pullback is exactly `P† ∘ Hess f(Pz) ∘ P`. -/
theorem pullback_hessian_eq {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    {target : DFP.InverseIteration (Fin 2)}
    {P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hdata : IdentityInitialization.PullbackData c.iteration target P)
    (z : EuclideanSpace ℝ (Fin 2)) :
    hessian target.objective z =
      P.toContinuousLinearMap.pullback (hessian c.iteration.objective (P z)) := by
  rw [hdata.objective, IdentityInitialization.pulledObjective_def]
  exact P.comp_right_hessian _ z
    ((c.objectiveContDiff.gradient_succ (n := 1)).differentiable_one (P z))

/-- Helper for cor:identity-initialization: the actual positive-root pullback
has the LITERAL displayed planar Hessian bounds, without changing its objective. -/
theorem pullback_hessian_bounds {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    {target : DFP.InverseIteration (Fin 2)}
    {P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hP : P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv)
    (hdata : IdentityInitialization.PullbackData c.iteration target P) :
    HasHessianBounds (initialMinEigenvalue c / 2) (3 * initialMaxEigenvalue c / 2)
      target.objective := by
  have hroot := positiveRoot_spectral_bounds (c.iteration.inverseHessianPosDef 0)
  rw [← hP] at hroot
  have hdiff : Differentiable ℝ (gradient c.iteration.objective) :=
    (c.objectiveContDiff.gradient_succ (n := 1)).differentiable_one
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hthree : (0 : ℝ) ≤ 3 / 2 := by norm_num
  rw [hdata.objective, IdentityInitialization.pulledObjective_def]
  have h : HasHessianBounds ((1 / 2 : ℝ) * initialMinEigenvalue c)
      ((3 / 2 : ℝ) * initialMaxEigenvalue c) (c.iteration.objective ∘ P) :=
    c.hessianBounds.comp_continuousLinearEquiv P hdiff hhalf hthree hroot.1.1 hroot.1.2
  simpa only [div_mul_eq_mul_div, one_mul] using h

/-- Helper for cor:identity-initialization: the exact source gradient limit one
gives `liminf ‖P†gₖ‖ ≥ sqrt(λmin(H₀))` on that SAME canonical pullback. -/
theorem pullback_gradient_liminf {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    (hlimit : c.gradientLimit = 1)
    {target : DFP.InverseIteration (Fin 2)}
    {P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hP : P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv)
    (hdata : IdentityInitialization.PullbackData c.iteration target P) :
    Real.sqrt (initialMinEigenvalue c) ≤
      liminf (fun k ↦ ‖DFP.gradients target.objective target.point k‖) atTop := by
  have hroot := positiveRoot_spectral_bounds (c.iteration.inverseHessianPosDef 0)
  rw [← hP] at hroot
  have h := pulledGradient_liminf_ge c P (initialEigenvalues_pos c).1.le hroot.2.1
  simpa only [hdata.gradients, hlimit, mul_one] using h

/-- Helper for cor:identity-initialization: the prescribed identity-block
extension embeds the SAME canonical planar gradients at every source index. -/
theorem extension_gradients {n : ℕ} {hn : 2 ≤ n}
    {source : DFP.InverseIteration (Fin 2)} {target : DFP.InverseIteration (Fin n)}
    (h : IdentityInitialization.DimensionExtensionData n hn source target) (k : ℕ) :
    DFP.gradients target.objective target.point k =
      OrthogonalExtension.planeEmbedding n hn (DFP.gradients source.objective source.point k) := by
  rw [DFP.gradients_apply, DFP.gradients_apply, h.objective, h.point,
    OrthogonalExtension.planeEmbedding_apply, OrthogonalExtension.gradient_isometric_comp,
    (OrthogonalExtension.coordinateEquiv n hn).apply_symm_apply,
    OrthogonalExtension.leftEmbedding_apply,
    EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (source.differentiableAt k),
    OrthogonalExtension.planeEmbedding_apply, OrthogonalExtension.leftEmbedding_apply]

/-- Helper for cor:identity-initialization: the source identity-block extension
preserves each normalized planar gradient norm exactly. -/
theorem extension_gradient_norm {n : ℕ} {hn : 2 ≤ n}
    {source : DFP.InverseIteration (Fin 2)} {target : DFP.InverseIteration (Fin n)}
    (h : IdentityInitialization.DimensionExtensionData n hn source target) (k : ℕ) :
    ‖DFP.gradients target.objective target.point k‖ =
      ‖DFP.gradients source.objective source.point k‖ := by
  rw [extension_gradients h, (OrthogonalExtension.planeEmbedding n hn).norm_map]

/-- Helper for cor:identity-initialization: the SAME orthogonal extension
has the displayed minimum and maximum of the planar and identity-block bounds. -/
theorem extension_hessian_bounds {n : ℕ} {hn : 2 ≤ n} {m M : ℝ}
    {source : DFP.InverseIteration (Fin 2)} {target : DFP.InverseIteration (Fin n)}
    (h : IdentityInitialization.DimensionExtensionData n hn source target)
    (hC2 : ContDiff ℝ 2 source.objective) (hm : 0 < m)
    (hbound : HasHessianBounds m M source.objective) :
    HasHessianBounds (min m 1) (max M 1) target.objective := by
  have hwide := PlanarCounterexample.hessianBounds_mono hC2 hbound
    (min_le_left m 1) (le_max_left M 1)
  have hsum := EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective
    (kappa := Fin (n - 2)) hC2 hwide (min_le_right m 1) (le_max_right M 1)
  have hsumC2 := EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective
    (kappa := Fin (n - 2)) hC2
  have hdiff := (hsumC2.gradient_succ (n := 1)).differentiable_one
  rw [h.objective]
  exact hsum.comp_linearIsometryEquiv (OrthogonalExtension.coordinateEquiv n hn) hdiff
    (lt_min hm zero_lt_one).le (zero_lt_one.trans_le (le_max_right M 1)).le

end DFPWolfe.V21.IdentityQuantitative

namespace DFPWolfe.V21

open IdentityQuantitative

/-- cor:identity-initialization, quantitative paragraph (main.tex:1185–1210).
The SAME original polar source and literal positive-root normalization have
global planar Hessian bounds `λmin(H₀)/2` and `3λmax(H₀)/2`, and transformed
gradient-norm liminf at least `sqrt(λmin(H₀))`. The canonical eigenvalues are
in decreasing order, with indices one and zero respectively, and are positive.

The accepted normalized matrix iteration, its objective `f(Pz)`, points `P⁻¹x`,
matrices `P⁻¹HP⁻ᵀ`, original positive alpha and Wolfe pair are retained through
`PullbackData`. The SAME subsequent identity-block extension has the displayed
minimum/maximum with one, exactly preserves normalized planar gradient norms,
and retains the full centered ellipse, half-Hölder Hessian and unique origin.
The existing certificate bounds `m,M` remain as provenance; the additional
sharp bounds below hold on those VERY SAME iterations. -/
theorem identityInitializationQuantitative (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ source ∧
        PlanarCounterexample.CounterexampleProperties (1 / 2) source ∧
        0 < initialMinEigenvalue source ∧ 0 < initialMaxEigenvalue source ∧
        ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
          (m M : ℝ)
          (planar : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
            2 m M c₁ c₂),
          P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
          IdentityInitialization.PullbackData source.iteration planar.iteration P ∧
          HasHessianBounds (initialMinEigenvalue source / 2)
            (3 * initialMaxEigenvalue source / 2) planar.iteration.objective ∧
          Real.sqrt (initialMinEigenvalue source) ≤
            liminf (fun k ↦ ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖)
              atTop ∧
          ∃ result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
              n (min m 1) (max M 1) c₁ c₂,
            IdentityInitialization.DimensionExtensionData n hn planar.iteration result.iteration ∧
            IdentityInitialization.EllipseObjectiveProperties result.iteration
              ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp P.symm.toLinearMap) ∧
            HasHessianBounds (min (initialMinEigenvalue source / 2) 1)
              (max (3 * initialMaxEigenvalue source / 2) 1) result.iteration.objective ∧
            Real.sqrt (initialMinEigenvalue source) ≤
              liminf (fun k ↦ ‖DFP.gradients result.iteration.objective result.iteration.point k‖)
                atTop ∧
            result.iteration.stepLength = source.iteration.stepLength ∧
            ∀ k, ‖DFP.gradients result.iteration.objective result.iteration.point k‖ =
              ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖ := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource, hproperties⟩ :=
    PlanarCounterexample.planarCounterexample c₁ c₂ (1 / 2)
      hc₁ hc₁lim hc₂lim hc₂ hhalf hhalfOne
  obtain ⟨P, m, M, planar, hP, hdata, hellipse⟩ :=
    IdentityInitialization.normalizePlanarWithProperties source
      hproperties.origin hproperties.unique_minimizer hproperties.half_holder hproperties.cluster
  have heigen := initialEigenvalues_pos source
  have hplanar := pullback_hessian_bounds source hP hdata
  have hgradient := pullback_gradient_liminf source hproperties.gradientLimit hP hdata
  obtain ⟨result, hextend, hfinal⟩ := IdentityInitialization.extendNormalizedPlanar
    n hn planar P.symm.toLinearMap hellipse
  have hextended := extension_hessian_bounds hextend planar.objectiveContDiff
    (half_pos heigen.1) hplanar
  have hnorm := extension_gradient_norm hextend
  have hliminf : Real.sqrt (initialMinEigenvalue source) ≤
      liminf (fun k ↦ ‖DFP.gradients result.iteration.objective result.iteration.point k‖)
        atTop := by
    simpa only [hnorm] using hgradient
  have halpha : result.iteration.stepLength = source.iteration.stepLength :=
    hextend.stepLength.trans hdata.stepLength
  exact ⟨νStar, hνStar, κ, hκ, j₀, hj₀, source, hsource, hproperties,
    heigen.1, heigen.2, P, m, M, planar, hP, hdata, hplanar, hgradient,
    result, hextend, hfinal, hextended, hliminf, halpha, hnorm⟩

end DFPWolfe.V21
