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
@[expose] def quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n → ℝ :=
  fun f ↦ c + inner ℝ b f + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin f) f

/-- The defining formula for `quadraticFunctional`. -/
theorem quadraticFunctional_def (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (f : EuclideanSpace ℝ n) :
    quadraticFunctional c b A f =
      c + inner ℝ b f + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin f) f := rfl

/-- A map `J` is a quadratic functional when it admits a representation
`J = quadraticFunctional c b A` with symmetric matrix part `A`. -/
@[expose] def IsQuadraticFunctional (J : EuclideanSpace ℝ n → ℝ) : Prop :=
  ∃ (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ), A.IsSymm ∧
    J = quadraticFunctional c b A

/-- A quadratic functional is exactly a function admitting a symmetric affine
quadratic representation. -/
theorem isQuadraticFunctional_iff (J : EuclideanSpace ℝ n → ℝ) :
    IsQuadraticFunctional J ↔
      ∃ (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ), A.IsSymm ∧
        J = quadraticFunctional c b A := Iff.rfl

/-- Helper for Definition 3.4: a symmetric matrix induces a self-adjoint Euclidean linear map,
so the associated quadratic form satisfies `⟪A x, y⟫ = ⟪x, A y⟫`. -/
theorem inner_toEuclideanLin_eq (A : Matrix n n ℝ) (hA : A.IsSymm)
    (x y : EuclideanSpace ℝ n) :
    inner ℝ (A.toEuclideanLin x) y = inner ℝ x (A.toEuclideanLin y) := by
  have hadj : A.toEuclideanLin.adjoint = A.toEuclideanLin := by
    rw [(Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm]
    have hA' : A.conjTranspose = A := by simpa [Matrix.IsSymm] using hA
    rw [hA']
  conv_lhs => rw [← hadj]
  exact LinearMap.adjoint_inner_left A.toEuclideanLin y x

/-- Helper for Definition 3.4: the pure quadratic matrix term has derivative
`InnerProductSpace.toDual ℝ (A.toEuclideanLin f)` when `A` is symmetric. -/
theorem hasFDerivAt_quadraticMatrixTerm
    (A : Matrix n n ℝ) (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    HasFDerivAt
      (fun x : EuclideanSpace ℝ n ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (A.toEuclideanLin f)) f := by
  have hsymm : ∀ x y : EuclideanSpace ℝ n,
      inner ℝ (A.toEuclideanLin x) y = inner ℝ x (A.toEuclideanLin y) :=
    inner_toEuclideanLin_eq A hA
  have hM : HasFDerivAt (fun x : EuclideanSpace ℝ n ↦ A.toEuclideanLin x)
      (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap f :=
    (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap.hasFDerivAt
  have hid : HasFDerivAt (fun x : EuclideanSpace ℝ n ↦ x)
      (1 : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) f := hasFDerivAt_id f
  have hprod := HasFDerivAt.inner (𝕜 := ℝ) hM hid
  refine (hprod.const_mul (1 / 2 : ℝ)).congr_fderiv ?_
  ext h
  -- Evaluate both sides on a test direction.
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, fderivInnerCLM_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  show (1 / 2 : ℝ) *
      (inner ℝ (A.toEuclideanLin f) h + inner ℝ (A.toEuclideanLin h) f) =
    inner ℝ (A.toEuclideanLin f) h
  rw [hsymm h f, real_inner_comm (A.toEuclideanLin f) h]
  ring

/-- Helper for Definition 3.4: the Fréchet derivative of a symmetric quadratic
functional is the Riesz functional represented by `b + A.toEuclideanLin f`. -/
theorem fderiv_quadraticFunctional
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    fderiv ℝ (quadraticFunctional c b A) f =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (b + A.toEuclideanLin f) := by
  have hconst : HasFDerivAt (fun _ : EuclideanSpace ℝ n => c) (0 : EuclideanSpace ℝ n →L[ℝ] ℝ) f :=
    hasFDerivAt_const c f
  have hlin : HasFDerivAt (fun x : EuclideanSpace ℝ n => inner ℝ b x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) b) f :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n) b).hasFDerivAt
  have hquad := hasFDerivAt_quadraticMatrixTerm A hA f
  have hsum : HasFDerivAt
      (fun x : EuclideanSpace ℝ n =>
        c + inner ℝ b x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
      (0 + (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) b +
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (A.toEuclideanLin f)) f :=
    (hconst.add hlin).add hquad
  have hfun : (fun x : EuclideanSpace ℝ n =>
        c + inner ℝ b x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x) =
      quadraticFunctional c b A := rfl
  rw [← hfun, hsum.fderiv]
  simp [map_add]

/-- If `A` is symmetric, then the gradient of `quadraticFunctional c b A` is
`f ↦ b + A.toEuclideanLin f`. -/
theorem gradient_quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    gradient (quadraticFunctional c b A) f = b + A.toEuclideanLin f := by
  rw [gradient, fderiv_quadraticFunctional c b A hA f]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).symm_apply_apply _

/-- If `A` is symmetric, then the Hessian of `quadraticFunctional c b A`
applied to any vector agrees with `A.toEuclideanLin`. -/
theorem hessian_quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    (hA : A.IsSymm) (f h : EuclideanSpace ℝ n) :
    hessian (quadraticFunctional c b A) f h = A.toEuclideanLin h := by
  refine ext_inner_right (𝕜 := ℝ) (fun k => ?_)
  rw [hessian_inner]
  -- The first derivative is `x ↦ toDual (b + A x)`, hence the second derivative is `h ↦ toDual (A h)`.
  have hJ : fderiv ℝ (quadraticFunctional c b A) =
      fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (b + A.toEuclideanLin x) := by
    funext x
    exact fderiv_quadraticFunctional c b A hA x
  rw [hJ]
  have hM : HasFDerivAt (fun x : EuclideanSpace ℝ n => A.toEuclideanLin x)
      (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap f :=
    (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap.hasFDerivAt
  have hinner : HasFDerivAt (fun x : EuclideanSpace ℝ n => b + A.toEuclideanLin x)
      (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap f := by
    fun_prop
  let T : EuclideanSpace ℝ n →L[ℝ] (EuclideanSpace ℝ n →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).toLinearIsometry.toContinuousLinearMap
  have hcomp : HasFDerivAt
      (fun x : EuclideanSpace ℝ n =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (b + A.toEuclideanLin x))
      (T.comp (A.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).toContinuousLinearMap) f :=
    T.hasFDerivAt.comp f hinner
  rw [hcomp.fderiv]
  rfl

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
    b + A.toEuclideanLin (-(A⁻¹).toEuclideanLin b) = 0 := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hspd))
  have hmap : A.toEuclideanLin ((A⁻¹).toEuclideanLin b) = b := by
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (A := A) hdet]
  rw [map_neg, hmap, add_neg_cancel]

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
        (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin h) h := by
  rw [quadraticFunctional_def, quadraticFunctional_def, map_add]
  simp only [inner_add_left, inner_add_right]
  rw [inner_toEuclideanLin_eq A hA h f0, real_inner_comm (A.toEuclideanLin f0) h]
  ring

/-- Helper for Definition 3.4: translating a symmetric quadratic functional by
any critical point leaves only the pure quadratic remainder. -/
theorem quadraticFunctional_translate_eq_base_add_half_inner
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ)
    {f0 h : EuclideanSpace ℝ n} (hA : A.IsSymm)
    (hcrit : b + A.toEuclideanLin f0 = 0) :
    quadraticFunctional c b A (f0 + h) =
      quadraticFunctional c b A f0 + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin h) h := by
  rw [quadraticFunctional_increment_eq_base_add_linear_add_half_inner c b A hA]
  rw [hcrit, inner_zero_left, add_zero]

/-- Helper for Definition 3.4: the quadratic form of a positive definite matrix is nonnegative. -/
theorem inner_toEuclideanLin_self_nonneg {A : Matrix n n ℝ} (hspd : A.PosDef)
    (h : EuclideanSpace ℝ n) :
    0 ≤ inner ℝ (A.toEuclideanLin h) h := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have hx : WithLp.ofLp h ≠ 0 := by simpa using hh
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hspd hx
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa using hpos.le

/-- Helper for Definition 3.4: the quadratic form of a positive definite matrix is strictly
positive on nonzero vectors. -/
theorem inner_toEuclideanLin_self_pos {A : Matrix n n ℝ} (hspd : A.PosDef)
    {h : EuclideanSpace ℝ n} (hh : h ≠ 0) :
    0 < inner ℝ (A.toEuclideanLin h) h := by
  have hx : WithLp.ofLp h ≠ 0 := by simpa using hh
  have hpos := Matrix.PosDef.re_dotProduct_pos hspd hx
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa using hpos

/-- Helper for Definition 3.4: the quadratic functional is differentiable everywhere. -/
theorem differentiableAt_quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ n)
    (A : Matrix n n ℝ) (hA : A.IsSymm) (f : EuclideanSpace ℝ n) :
    DifferentiableAt ℝ (quadraticFunctional c b A) f := by
  have hconst : HasFDerivAt (fun _ : EuclideanSpace ℝ n => c) (0 : EuclideanSpace ℝ n →L[ℝ] ℝ) f :=
    hasFDerivAt_const c f
  have hlin : HasFDerivAt (fun x : EuclideanSpace ℝ n => inner ℝ b x)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) b) f :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n) b).hasFDerivAt
  have hquad := hasFDerivAt_quadraticMatrixTerm A hA f
  have hsum : HasFDerivAt
      (fun x : EuclideanSpace ℝ n =>
        c + inner ℝ b x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
      (0 + (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) b +
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)) (A.toEuclideanLin f)) f :=
    (hconst.add hlin).add hquad
  have hfun : (fun x : EuclideanSpace ℝ n =>
        c + inner ℝ b x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x) =
      quadraticFunctional c b A := rfl
  rw [← hfun]
  exact hsum.differentiableAt

/-- If `A` is positive definite, then `quadraticFunctional c b A` is strictly
convex on `Set.univ`. -/
theorem strictConvexOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    StrictConvexOn ℝ Set.univ (quadraticFunctional c b A) := by
  have hA : A.IsSymm := by simpa using hspd.isHermitian
  rw [strictConvexOn_iff_inner_gradient_sub_pos (quadraticFunctional c b A) convex_univ
    (fun x _ => differentiableAt_quadraticFunctional c b A hA x)]
  intro f1 f2 _ _ hne
  rw [gradient_quadraticFunctional c b A hA f1, gradient_quadraticFunctional c b A hA f2]
  have hsub : b + A.toEuclideanLin f1 - (b + A.toEuclideanLin f2) =
      A.toEuclideanLin (f1 - f2) := by
    rw [map_sub]
    abel
  rw [hsub]
  exact inner_toEuclideanLin_self_pos hspd (sub_ne_zero.mpr hne)

/-- If `A` is positive definite, then `quadraticFunctional c b A` attains its
minimum at `-(A⁻¹).toEuclideanLin b`. -/
theorem isMinOn_quadraticFunctional_of_posDef
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hspd : A.PosDef) :
    IsMinOn (quadraticFunctional c b A) Set.univ (-(A⁻¹).toEuclideanLin b) := by
  have hA : A.IsSymm := by simpa using hspd.isHermitian
  have hcrit := quadraticFunctionalCriticalPoint b A hspd
  intro x _
  change quadraticFunctional c b A (-(A⁻¹).toEuclideanLin b) ≤ quadraticFunctional c b A x
  -- Every point is the canonical minimizer plus an increment.
  have hx : x = -(A⁻¹).toEuclideanLin b + (x - (-(A⁻¹).toEuclideanLin b)) := by abel
  rw [hx, quadraticFunctional_increment_eq_base_add_linear_add_half_inner c b A hA]
  rw [show b + A.toEuclideanLin (-(A⁻¹).toEuclideanLin b) = 0 from hcrit, inner_zero_left, add_zero]
  have hnn : 0 ≤ inner ℝ (A.toEuclideanLin (x - (-(A⁻¹).toEuclideanLin b)))
      (x - (-(A⁻¹).toEuclideanLin b)) :=
    inner_toEuclideanLin_self_nonneg hspd _
  nlinarith

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
    fStar = -(A⁻¹).toEuclideanLin b := by
  have hA : A.IsSymm := by simpa using hspd.isHermitian
  have hcrit := quadraticFunctionalCriticalPoint b A hspd
  have hle : quadraticFunctional c b A fStar ≤
      quadraticFunctional c b A (-(A⁻¹).toEuclideanLin b) := hmin (Set.mem_univ _)
  have hge : quadraticFunctional c b A (-(A⁻¹).toEuclideanLin b) ≤
      quadraticFunctional c b A fStar :=
    isMinOn_quadraticFunctional_of_posDef c b A hspd (Set.mem_univ _)
  have heq : quadraticFunctional c b A fStar =
      quadraticFunctional c b A (-(A⁻¹).toEuclideanLin b) := le_antisymm hle hge
  -- Translate the functional at the critical point and compare.
  have htr := quadraticFunctional_translate_eq_base_add_half_inner c b A
    (f0 := -(A⁻¹).toEuclideanLin b)
    (h := fStar - (-(A⁻¹).toEuclideanLin b)) hA hcrit
  have hms : -(A⁻¹).toEuclideanLin b + (fStar - (-(A⁻¹).toEuclideanLin b)) = fStar := by abel
  rw [hms] at htr
  have hzero : inner ℝ (A.toEuclideanLin (fStar - (-(A⁻¹).toEuclideanLin b)))
      (fStar - (-(A⁻¹).toEuclideanLin b)) = 0 := by
    nlinarith
  have hsub : fStar - (-(A⁻¹).toEuclideanLin b) = 0 := by
    by_contra hne
    have hpos := inner_toEuclideanLin_self_pos hspd hne
    linarith
  have := sub_eq_zero.mp hsub
  exact this

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
          (1 / 2 : ℝ) * τ ^ 2 * inner ℝ (A.toEuclideanLin g) g := by
  dsimp only
  funext τ
  rw [LineSearch.profile_apply]
  rw [quadraticFunctional_increment_eq_base_add_linear_add_half_inner c b A
    (f0 := f) (h := τ • (-(b + A.toEuclideanLin f))) hA]
  have h1 : inner ℝ (b + A.toEuclideanLin f) (τ • (-(b + A.toEuclideanLin f))) =
      -(τ * ‖b + A.toEuclideanLin f‖ ^ 2) := by
    rw [inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  have h2 : inner ℝ (A.toEuclideanLin (τ • (-(b + A.toEuclideanLin f))))
        (τ • (-(b + A.toEuclideanLin f))) =
      τ ^ 2 * inner ℝ (A.toEuclideanLin (b + A.toEuclideanLin f))
        (b + A.toEuclideanLin f) := by
    rw [map_smul, map_neg, inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right]
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [h1, h2]
  ring

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
      (Set.Ici (0 : ℝ))
      (‖b + A.toEuclideanLin f‖ ^ 2 /
        inner ℝ (A.toEuclideanLin (b + A.toEuclideanLin f)) (b + A.toEuclideanLin f)) := by
  have hA : A.IsSymm := by simpa using hspd.isHermitian
  intro τ hτ
  rw [profile_quadraticFunctional_negGradient c b A hA f]
  simp only [Set.mem_setOf_eq]
  set g : EuclideanSpace ℝ n := b + A.toEuclideanLin f with hgdef
  by_cases hg : g = 0
  · simp [hg]
  · set q : ℝ := inner ℝ (A.toEuclideanLin g) g with hqdef
    have hqpos : 0 < q := inner_toEuclideanLin_self_pos hspd hg
    have hkey : quadraticFunctional c b A f - (‖g‖ ^ 2 / q) * ‖g‖ ^ 2 +
          (1 / 2 : ℝ) * (‖g‖ ^ 2 / q) ^ 2 * q =
        quadraticFunctional c b A f - τ * ‖g‖ ^ 2 + (1 / 2 : ℝ) * τ ^ 2 * q -
          (1 / 2 : ℝ) * q * (τ - ‖g‖ ^ 2 / q) ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ (1 / 2 : ℝ) * q * (τ - ‖g‖ ^ 2 / q) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hqpos.le) (sq_nonneg _)
    linarith

end QuadraticOptimization
