/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_39
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_42
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

public section

noncomputable section

namespace QuadraticOptimization

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The affine quadratic functional `f ↦ c + inner ℝ b f + (1 / 2) * inner ℝ (A f) f`
associated to the vector `b` and matrix `A`. -/
def quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n → ℝ :=
  fun f ↦ c + inner ℝ b f + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin f) f

/-- The defining formula for `quadraticFunctional`. -/
theorem quadraticFunctional_def (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (f : EuclideanSpace ℝ n) :
    quadraticFunctional c b A f =
      c + inner ℝ b f + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin f) f := sorry

/-- A map `J` is a quadratic functional when it admits a representation
`J = quadraticFunctional c b A` with symmetric matrix part `A`. -/
def IsQuadraticFunctional (J : EuclideanSpace ℝ n → ℝ) : Prop :=
  ∃ (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ), A.IsSymm ∧
    J = quadraticFunctional c b A

/-- A quadratic functional is exactly a function admitting a symmetric affine
quadratic representation. -/
theorem isQuadraticFunctional_iff (J : EuclideanSpace ℝ n → ℝ) :
    IsQuadraticFunctional J ↔
      ∃ (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ), A.IsSymm ∧
        J = quadraticFunctional c b A := sorry

/-- Helper for Definition 3.4: the pure quadratic matrix term has derivative
`InnerProductSpace.toDual ℝ (A.toEuclideanLin f)` when `A` is symmetric. -/
theorem hasFDerivAt_quadraticMatrixTerm
    (A : Matrix n n ℝ) (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    HasFDerivAt
      (fun x : EuclideanSpace ℝ n ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (A.toEuclideanLin f)) f := sorry

/-- Helper for Definition 3.4: the Fréchet derivative of a symmetric quadratic
functional is the Riesz functional represented by `b + A.toEuclideanLin f`. -/
theorem fderiv_quadraticFunctional
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    fderiv ℝ (quadraticFunctional c b A) f =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (b + A.toEuclideanLin f) := sorry

/-- If `A` is symmetric, then the gradient of `quadraticFunctional c b A` is
`f ↦ b + A.toEuclideanLin f`. -/
theorem gradient_quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    gradient (quadraticFunctional c b A) f = b + A.toEuclideanLin f := sorry

/-- If `A` is symmetric, then the Hessian of `quadraticFunctional c b A`
applied to any vector agrees with `A.toEuclideanLin`. -/
theorem hessian_quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f h : EuclideanSpace ℝ n) :
    hessian (quadraticFunctional c b A) f h = A.toEuclideanLin h := sorry

/-- The canonical minimizer of `quadraticFunctional c b A` is the solution of
`A f = -b`. -/
@[expose]
def quadraticFunctionalMinimizer (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n :=
  -(A⁻¹).toEuclideanLin b

/-- Helper for Definition 3.4: the explicit inverse candidate satisfies the
stationary equation for the quadratic gradient. -/
theorem quadraticFunctionalCriticalPoint
    (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    b + A.toEuclideanLin (-(A⁻¹).toEuclideanLin b) = 0 := sorry

/-- The canonical minimizer satisfies the stationary equation for the quadratic
gradient. -/
theorem quadraticFunctionalMinimizer_isCriticalPoint
    (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    b + A.toEuclideanLin (quadraticFunctionalMinimizer b A) = 0 := by
  simpa [quadraticFunctionalMinimizer] using quadraticFunctionalCriticalPoint b A hspd

/-- Helper for Definition 3.4: translating a symmetric quadratic functional by
any increment splits into the current gradient pairing plus a pure quadratic remainder. -/
theorem quadraticFunctional_increment_eq_base_add_linear_add_half_inner
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    {f0 h : EuclideanSpace ℝ n} (hA : A.IsSymm) :
    quadraticFunctional c b A (f0 + h) =
      quadraticFunctional c b A f0 + inner ℝ (b + A.toEuclideanLin f0) h +
        (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin h) h := sorry

/-- Helper for Definition 3.4: translating a symmetric quadratic functional by
any critical point leaves only the pure quadratic remainder. -/
theorem quadraticFunctional_translate_eq_base_add_half_inner
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    {f0 h : EuclideanSpace ℝ n} (hA : A.IsSymm)
    (hcrit : b + A.toEuclideanLin f0 = 0) :
    quadraticFunctional c b A (f0 + h) =
      quadraticFunctional c b A f0 + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin h) h := sorry

/-- If `A` is positive definite, then `quadraticFunctional c b A` is strictly
convex on `Set.univ`. -/
theorem strictConvexOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    StrictConvexOn ℝ Set.univ (quadraticFunctional c b A) := sorry

/-- If `A` is positive definite, then `quadraticFunctional c b A` attains its
minimum at `-(A⁻¹).toEuclideanLin b`. -/
theorem isMinOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    IsMinOn (quadraticFunctional c b A) Set.univ (-(A⁻¹).toEuclideanLin b) := sorry

/-- If `A` is positive definite, then `quadraticFunctional c b A` attains its
minimum at `quadraticFunctionalMinimizer b A`. -/
theorem isMinOn_quadraticFunctionalMinimizer_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    IsMinOn (quadraticFunctional c b A) Set.univ (quadraticFunctionalMinimizer b A) := by
  simpa [quadraticFunctionalMinimizer] using isMinOn_quadraticFunctional_of_posDef c b A hspd

/-- A positive-definite quadratic functional has `-(A⁻¹).toEuclideanLin b` as
its unique minimizer. -/
theorem eq_minimizer_of_isMinOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef)
    {fStar : EuclideanSpace ℝ n}
    (hmin : IsMinOn (quadraticFunctional c b A) Set.univ fStar) :
    fStar = -(A⁻¹).toEuclideanLin b := sorry

/-- A positive-definite quadratic functional has `quadraticFunctionalMinimizer b A`
as its unique minimizer. -/
theorem eq_quadraticFunctionalMinimizer_of_isMinOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef)
    {fStar : EuclideanSpace ℝ n}
    (hmin : IsMinOn (quadraticFunctional c b A) Set.univ fStar) :
    fStar = quadraticFunctionalMinimizer b A := by
  simpa [quadraticFunctionalMinimizer] using
    eq_minimizer_of_isMinOn_quadraticFunctional_of_posDef c b A hspd hmin

/-- Helper for Definition 3.4: profiling a quadratic functional along the negative gradient
direction produces a scalar quadratic polynomial in the step length. -/
theorem profile_quadraticFunctional_negGradient
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    let g := b + A.toEuclideanLin f
    LineSearch.profile (quadraticFunctional c b A) f (-g) =
      fun τ : ℝ ↦
        quadraticFunctional c b A f - τ * ‖g‖ ^ 2 +
          (1 / 2 : ℝ) * τ ^ 2 * inner ℝ (A.toEuclideanLin g) g := sorry

/-- For the steepest-descent direction `-(b + A.toEuclideanLin f)`, the exact
line-search step of a positive-definite quadratic functional is
`‖b + A.toEuclideanLin f‖ ^ 2 /
inner ℝ (A.toEuclideanLin (b + A.toEuclideanLin f)) (b + A.toEuclideanLin f)`.
-/
theorem exactLineSearchStep_quadraticFunctional
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    IsMinOn
      (LineSearch.profile (quadraticFunctional c b A) f (-(b + A.toEuclideanLin f)))
      (Set.Ioi (0 : ℝ))
      (‖b + A.toEuclideanLin f‖ ^ 2 /
        inner ℝ (A.toEuclideanLin (b + A.toEuclideanLin f)) (b + A.toEuclideanLin f)) := sorry

end QuadraticOptimization
