module

public import ReasLib.Analysis.QuadraticTail

public section

open scoped ContDiff Manifold Matrix.Norms.L2Operator MatrixOrder

/- Lemma 4.2 (1): the gradient of a smooth quadratic-tail function is a global smooth
diffeomorphism. -/
#check (QuadraticTail.gradientDiffeomorph :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, e x = gradient H x)

/- Lemma 4.2 (2): the convex conjugate of a smooth quadratic-tail function is smooth. -/
#check (QuadraticTail.conjugateContDiff :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ContDiff ℝ ⊤ (ConvexAnalysis.conjugate H))

/- Lemma 4.2 (3): the gradient of the convex conjugate is the inverse of the original
gradient. -/
#check (QuadraticTail.gradient_conjugate :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    gradient (ConvexAnalysis.conjugate H) = Function.invFun (gradient H))

/- Lemma 4.2 (4): the Hessian of the convex conjugate is the inverse Hessian at the
inverse-gradient point. -/
#check (QuadraticTail.hessian_conjugate :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ∀ x : EuclideanSpace ℝ (Fin n),
      ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x =
        (ConvexAnalysis.hessian H (Function.invFun (gradient H) x))⁻¹)

/- Lemma 4.2 (5): the Hessian of the convex conjugate obeys the two-sided Loewner bound. -/
#check (QuadraticTail.hessian_mem_Icc :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ∀ x : EuclideanSpace ℝ (Fin n),
      ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x ∈
        Set.Icc ((1 / (1 + θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
          ((1 / (1 - θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))

/- Lemma 4.2 (6): the Hessian of the convex conjugate is uniformly close to the identity. -/
#check (QuadraticTail.hessianNorm_le :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x - 1‖ ≤ θ / (1 - θ))

/- Lemma 4.2 (7): subtracting the standard quadratic from the convex conjugate gives a
smooth function. -/
#check (QuadraticTail.conjugateSub_contDiff :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ContDiff ℝ ⊤
      (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))

/- Lemma 4.2 (8): subtracting the standard quadratic from the convex conjugate gives a
compactly supported function. -/
#check (QuadraticTail.conjugateSub_hasCompactSupport :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    HasCompactSupport
      (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))

/- Lemma 4.2 (9): the topological support of the conjugate's quadratic tail is contained in
that of the original function. -/
#check (QuadraticTail.tsupport_conjugateSub_subset :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    tsupport
        (ConvexAnalysis.conjugate H -
          (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
      tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))

/- Lemma 4.2 (10): the origin is a global minimizer of the convex conjugate. -/
#check (QuadraticTail.conjugate_isMinOn :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    IsMinOn (ConvexAnalysis.conjugate H) Set.univ 0)

/- Lemma 4.2 (11): every global minimizer of the convex conjugate is the origin. -/
#check (QuadraticTail.eq_zero_of_conjugate_isMinOn :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ∀ x : EuclideanSpace ℝ (Fin n),
      IsMinOn (ConvexAnalysis.conjugate H) Set.univ x → x = 0)

/- Lemma 4.2 (12): the Hessian of the convex conjugate at the origin is the identity. -/
#check (QuadraticTail.hessian_conjugate_zero :
  ∀ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ),
    ContDiff ℝ ⊤ H →
    ContDiff ℝ ⊤ (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    HasCompactSupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) →
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ) →
    θ < 1 → gradient H 0 = 0 → ConvexAnalysis.hessian H 0 = 1 →
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) 0 = 1)
