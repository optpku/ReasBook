module

public import ReasLib.Optimization.DFP.Polar.IdentityInitialization
public import ReasLib.Analysis.Convex.Hessian

public section

open Filter DFP.Polar
open scoped Topology InnerProduct

namespace DFPWolfe.V21

/-- Helper for cor:identity-initialization: the canonical matrix certificate's
positive global Hessian lower bound makes its C² objective strongly convex. -/
theorem identityCertificateStrongConvexOn {n : ℕ} {m M c₁ c₂ : ℝ}
    (d : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) :
    StrongConvexOn Set.univ m d.iteration.objective := by
  have hLower : ∀ x v, m * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient d.iteration.objective) x v) v := by
    intro x v
    simpa only [hessian_def] using ((d.hessianBounds.at x).quadraticForm v).1
  exact ContDiff.strongConvexOnOfHessianLowerBound _ _ d.objectiveContDiff
    d.hessianLowerPos hLower

/-- cor:identity-initialization. For every `n≥2`, `0<c₁<2/3` and `2/3≤c₂<1`,
the v21 polar construction gives a canonical matrix-valued inverse DFP iteration
initialized at `I`, with positive step lengths and strong Wolfe at every index.
The existing certificate records a C² objective, positive global example-dependent
Hessian bounds, and a strictly positive gradient-norm liminf. The objective is
strongly convex, has globally half-Hölder Hessian, and has its unique minimum at
the origin with value zero. Its full cluster set is an injective linear image
of the unit circle, centered at zero in a subspace of dimension exactly two.

The source proof, main.tex:1160–1212, uses the literal positive root `P=H₀^(1/2)`:
`f∘P`, `P⁻¹x`, `Pᵀg` and `P⁻¹HP⁻ᵀ` preserve the original alpha and Wolfe pair.
Positive adjoint distortion gives the positive liminf; inverse-root transport
gives the ellipse. The normalized plane is then extended by an identity block. -/
theorem identityInitialization (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ m ≤ M ∧
      ∃ d : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂,
        StrongConvexOn Set.univ m d.iteration.objective ∧
          ∃ i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
            IdentityInitialization.EllipseObjectiveProperties d.iteration i := by
  obtain ⟨m, M, hm, hM, hmM, d, i, hproperties⟩ :=
    IdentityInitialization.existsIdentityInitializedCounterexample
      n hn c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  exact ⟨m, M, hm, hM, hmM, d, identityCertificateStrongConvexOn d, i, hproperties⟩

/-- Helper for cor:identity-initialization: the direct source-facing form exposes
the C² objective, matrix identity initialization, every Wolfe step, positive liminf,
global Hessian and half-Hölder bounds, unique origin and complete centered ellipse. -/
theorem identityInitializationExplicit (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ m ≤ M ∧
      ∃ it : DFP.InverseIteration (Fin n),
        ContDiff ℝ 2 it.objective ∧ StrongConvexOn Set.univ m it.objective ∧
          HasHessianBounds m M it.objective ∧
          it.inverseHessian 0 = (1 : Matrix (Fin n) (Fin n) ℝ) ∧
          (∀ k, 0 < it.stepLength k) ∧
          (∀ k, LineSearch.IsStrongWolfe c₁ c₂ it.objective
            (it.point k) (it.point (k + 1) - it.point k)) ∧
          0 < liminf (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop ∧
          ∃ i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
            Function.Injective i ∧ Module.finrank ℝ (LinearMap.range i) = 2 ∧
              {x | MapClusterPt x atTop it.point} = i '' Metric.sphere 0 1 ∧
              (∃ C > 0, ∀ x y, ‖hessian it.objective x - hessian it.objective y‖ ≤
                C * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
              it.objective 0 = 0 ∧
              ∀ x, (∀ y, it.objective x ≤ it.objective y) ↔ x = 0 := by
  obtain ⟨m, M, hm, hM, hmM, d, hconvex, i, hproperties⟩ :=
    identityInitialization n hn c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  exact ⟨m, M, hm, hM, hmM, d.iteration, d.objectiveContDiff, hconvex,
    d.hessianBounds, d.initialInverseHessian_eq_one, d.stepLengthPos, d.strongWolfe,
    d.gradientNormLiminfPos, i, hproperties.injective, hproperties.range_finrank,
    hproperties.cluster, hproperties.half_holder, hproperties.origin,
    hproperties.unique_minimizer⟩

/-- Helper for cor:identity-initialization: exact provenance through the NEW
polar source witness, its literal positive planar square root, canonical matrix
pullback with the same alpha, and the subsequent identity-block extension.
The ellipse map is explicitly the source plane embedding composed with `P⁻¹`. -/
theorem identityInitializationWithSource (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ source ∧
        ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
          (m M : ℝ)
          (planar : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
            2 m M c₁ c₂),
          P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
            IdentityInitialization.PullbackData source.iteration planar.iteration P ∧
            ∃ result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
                n (min m 1) (max M 1) c₁ c₂,
              IdentityInitialization.DimensionExtensionData n hn planar.iteration result.iteration ∧
                IdentityInitialization.EllipseObjectiveProperties result.iteration
                  ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp
                    P.symm.toLinearMap) := by
  exact IdentityInitialization.polarIdentityInitialization
    n hn c₁ c₂ hc₁ hc₁lim hc₂lim hc₂

end DFPWolfe.V21
