module

public import ReasLib.Analysis.Convex.EuclideanPlaneHessian
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_1_Euclidean_gradient_Hessian_and_matrix_operator_bridge_Hessian

public section

universe u

/- Infrastructure I.30 (Global Hessian lower bound implies strong convexity) (1):
a global positive lower bound on the Hessian quadratic form gives the first-order
strong-convexity inequality. -/
#check (ContDiff.firstOrderOfHessianLowerBound :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ), ContDiff ℝ 2 f → 0 < m →
      (∀ x v : E,
        m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) x v) v) →
        ∀ x y : E,
          f x + Inner.inner ℝ (gradient f x) (y - x) +
              m / (2 : ℝ) * ‖y - x‖ ^ 2 ≤ f y)

/- Infrastructure I.30 (Global Hessian lower bound implies strong convexity) (2):
a `C²` function with a globally positive Hessian lower bound is strongly convex on
`Set.univ`. -/
#check (ContDiff.strongConvexOnOfHessianLowerBound :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ), ContDiff ℝ 2 f → 0 < m →
      (∀ x v : E,
        m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) x v) v) →
        StrongConvexOn Set.univ m f)

/- Infrastructure I.30 (Global Hessian lower bound implies strong convexity) (3):
the same Hessian lower bound makes the function uniformly convex with quadratic modulus
`fun r ↦ m / 2 * r ^ 2`. -/
#check (ContDiff.strongConvexOnOfHessianLowerBound :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ), ContDiff ℝ 2 f → 0 < m →
      (∀ x v : E,
        m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) x v) v) →
        UniformConvexOn Set.univ (fun r ↦ m / (2 : ℝ) * r ^ 2) f)

/- The generic criterion specializes to the Euclidean-plane Hessian operator. -/
#check (EuclideanPlane.strongConvexOnOfHessianLowerBound :
  ∀ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (m : ℝ), ContDiff ℝ 2 f → 0 < m →
    (∀ x v : EuclideanSpace ℝ (Fin 2),
      m * ‖v‖ ^ 2 ≤ inner ℝ (EuclideanPlane.hessian f x v) v) →
      StrongConvexOn Set.univ m f)
