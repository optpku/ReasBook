/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_34
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_45
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (ofLp toLp)
open scoped RealInnerProductSpace
open scoped Matrix

universe u

noncomputable section

section

variable {ι : Type u} [Fintype ι]

local notation "E" => ι → ℝ

/- Proposition 5.1 is `source-facing`: it studies the quadratic-affine function from
Chapter 4 under the Chapter 5 owner predicate `is_l_smooth_on`, after transporting a finite real
product `ι → ℝ`, and hence `ℝ^n` when `ι = Fin n`, to the canonical `WithLp p` model. Domain
sampling points to the owner abstractions `quadratic_affine_function`, `is_l_smooth_on`, and the
induced matrix norm `‖A‖[p,q]` from Chapter 1. -/

/-- The quadratic-affine function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c`, viewed on the canonical
`WithLp p` model of a finite real product, specializing to `ℝ^n` for `ι = Fin n`. -/
def quadratic_affine_function_on_lp (p : ENNReal) (A : Matrix ι ι ℝ) (b : E)
    (c : ℝ) : WithLp p E → ℝ :=
  quadratic_affine_function A b c ∘ ofLp

-- Proof sketch: `quadratic_affine_function_on_lp p A b c` is the Chapter 4 owner quadratic
-- precomposed with `WithLp.ofLp`, so evaluation at `x` unfolds directly to the coordinate formula
-- applied to `ofLp x`.
/-- Evaluating `quadratic_affine_function_on_lp p A b c` at `x` applies the Chapter 4
quadratic-affine function to the underlying coordinate vector `ofLp x`. -/
@[simp] theorem quadratic_affine_function_on_lp_apply (p : ENNReal)
    (A : Matrix ι ι ℝ) (b : E) (c : ℝ) (x : WithLp p E) :
    quadratic_affine_function_on_lp p A b c x = quadratic_affine_function A b c (ofLp x) :=
  rfl

section

variable [DecidableEq ι]

local notation "X" => EuclideanSpace ℝ ι

-- Proof sketch: identify the `p = 2` coordinate model with `EuclideanSpace ℝ ι`; the quadratic
-- term becomes the Euclidean pairing against `A.toEuclideanLin`, and the linear term becomes the
-- standard inner product with `b`.
/-- The Chapter 5 coordinate quadratic owner at `p = 2` is the intrinsic Euclidean quadratic
`x ↦ (1 / 2) ⟪A.toEuclideanLin x, x⟫ + ⟪b, x⟫`. -/
@[simp] theorem quadratic_affine_function_on_lp_two_apply_eq
    (A : Matrix ι ι ℝ) (b x : X) :
    quadratic_affine_function_on_lp (2 : ENNReal) A b.ofLp 0 x =
      (1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫ + ⟪b, x⟫ := by
  have hAx : ⟪A.toEuclideanLin x, x⟫ = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    change ⟪((A.toLpLin 2 2) : WithLp 2 (ι → ℝ) →ₗ[ℝ] X) x, x⟫ = _
    simpa [Matrix.toLpLin_apply] using EuclideanSpace.inner_toLp_toLp (A *ᵥ x.ofLp) x.ofLp
  have hbx : ⟪b, x⟫ = x.ofLp ⬝ᵥ b.ofLp := by
    simpa using (EuclideanSpace.inner_eq_star_dotProduct b x)
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply, hAx, hbx]
  simp [dotProduct_comm]

end

section

-- Proof sketch: the quadratic derivative is organized through the bounded bilinear owner
-- `dotProduct`; turning it into a continuous bilinear map lets the main proof use the standard
-- `hasFDerivAt_of_bilinear` calculus route instead of repeated coordinate expansions.
/-- Helper for Proposition 5.1: the coordinate dot product, packaged as a continuous bilinear map
on `ι → ℝ`. -/
private abbrev dotProductContinuousBilin : E →L[ℝ] E →L[ℝ] ℝ :=
  ((((↑(LinearMap.toContinuousLinearMap : ((E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ))) :
      ((E →ₗ[ℝ] ℝ) →ₗ[ℝ] E →L[ℝ] ℝ)) ∘ₗ dotProductBilin ℝ ℝ).toContinuousLinearMap)

-- Proof sketch: first differentiate the coordinate quadratic on `ι → ℝ`; bilinearity gives the
-- two raw derivative terms, and symmetry of `A` collapses them to the single functional against
-- `A *ᵥ x + b`.
/-- Helper for Proposition 5.1: the Fréchet derivative of the coordinate quadratic-affine map is
the dot-product functional with coefficient `A *ᵥ x + b`. -/
private theorem quadratic_affine_function_coordinate_hasFDerivAt
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) (x : E) :
    HasFDerivAt (quadratic_affine_function A b c)
      (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (A *ᵥ x + b))) x := by
  have hHerm : A.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  have hquadRaw :
      HasFDerivAt (fun y : E ↦ dotProduct y (A *ᵥ y))
        ((dotProductContinuousBilin.precompR E x A.mulVecLin.toContinuousLinearMap) +
          (dotProductContinuousBilin.precompL E (ContinuousLinearMap.id ℝ E) (A *ᵥ x))) x := by
    -- Differentiate the bilinear pairing `y ↦ dotProduct y (A *ᵥ y)` through its two inputs.
    simpa [dotProductContinuousBilin] using
      (ContinuousLinearMap.hasFDerivAt_of_bilinear
        (B := dotProductContinuousBilin)
        (ContinuousLinearMap.id ℝ E).hasFDerivAt A.mulVecLin.toContinuousLinearMap.hasFDerivAt :
        HasFDerivAt (fun y : E ↦ dotProductContinuousBilin y (A *ᵥ y)) _ x)
  have hquad :
      HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) * dotProduct y (A *ᵥ y))
        ((1 / 2 : ℝ) •
          ((dotProductContinuousBilin.precompR E x A.mulVecLin.toContinuousLinearMap) +
            (dotProductContinuousBilin.precompL E (ContinuousLinearMap.id ℝ E) (A *ᵥ x)))) x := by
    -- Scaling by `1 / 2` preserves the derivative and prepares the symmetry cancellation.
    simpa using hquadRaw.const_smul (1 / 2 : ℝ)
  have hlin :
      HasFDerivAt (fun y : E ↦ dotProduct b y)
        (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ b)) x := by
    -- The linear term already is its own derivative.
    simpa [dotProduct_comm] using
      (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ b)).hasFDerivAt
  have hsum := (hquad.add hlin).add_const c
  have hsum' :
      HasFDerivAt
        (fun z : E ↦
          ((fun y : E ↦ (1 / 2 : ℝ) * dotProduct y (A *ᵥ y)) + fun y ↦ dotProduct b y) z + c)
        (((1 / 2 : ℝ) •
          ((dotProductContinuousBilin.precompR E x A.mulVecLin.toContinuousLinearMap) +
            (dotProductContinuousBilin.precompL E (ContinuousLinearMap.id ℝ E) (A *ᵥ x)))) +
          LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ b)) x := by
    -- Rewrite the derivative into the standard `scaled quadratic part + linear part` shape.
    simpa [smul_add] using hsum
  have hderiv_eq :
      (((1 / 2 : ℝ) •
          ((dotProductContinuousBilin.precompR E x A.mulVecLin.toContinuousLinearMap) +
            (dotProductContinuousBilin.precompL E (ContinuousLinearMap.id ℝ E) (A *ᵥ x)))) +
        LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ b)) =
        LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (A *ᵥ x + b)) := by
    -- Symmetry turns the two bilinear contributions into the same functional against `A *ᵥ x`.
    ext v
    have hswap : dotProduct x (A *ᵥ v) = dotProduct (A *ᵥ x) v :=
      dotProduct_mulVec_swap_of_isHermitian A hHerm x v
    simp [dotProductContinuousBilin, hswap, dotProduct_comm, add_comm]
    ring
  rw [hderiv_eq] at hsum'
  -- The function side is exactly the coordinate quadratic-affine owner from Chapter 4.
  convert hsum' using 1

-- Proof sketch: compose the coordinate derivative formula with `WithLp.ofLp`; the composite
-- functional is precisely the Chapter 1 pairing owner `lpPairingDual`.
/-- Helper for Proposition 5.1: on `WithLp p (ι → ℝ)`, the derivative of the quadratic-affine map
is the pairing functional `lpPairingDual p (A *ᵥ ofLp x + b)`. -/
private theorem quadratic_affine_function_on_lp_hasFDerivAt
    (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) (x : WithLp p E) :
    HasFDerivAt (quadratic_affine_function_on_lp p A b c)
      (LinearMap.toContinuousLinearMap (lpPairingDual p (A *ᵥ ofLp x + b))) x := by
  have hcoord := quadratic_affine_function_coordinate_hasFDerivAt A hA b c (ofLp x)
  have hcomp := hcoord.comp x (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) (p := p) x)
  have hderiv_eq :
      (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (A *ᵥ ofLp x + b))).comp
          (PiLp.continuousLinearEquiv p ℝ (fun _ : ι ↦ ℝ)).toContinuousLinearMap =
        LinearMap.toContinuousLinearMap (lpPairingDual p (A *ᵥ ofLp x + b)) := by
    -- Composing with `ofLp` turns the coordinate dot product into the canonical pairing dual.
    ext v
    simp [PiLp.coe_continuousLinearEquiv, lpPairingDual_apply, dotProduct_comm, add_comm]
  rw [hderiv_eq] at hcomp
  simpa [quadratic_affine_function_on_lp] using hcomp

-- Proof sketch: subtract the two explicit derivative formulas, rewrite the difference as a single
-- `lpPairingDual`, and use Proposition 1.9 to identify its operator norm with the `ℓ_q` norm of
-- `A.toLpLin p q (x - y)`.
/-- Helper for Proposition 5.1: the norm of the derivative difference equals the `ℓ_q` norm of
`A.toLpLin p q (x - y)`. -/
private theorem quadratic_affine_function_on_lp_fderiv_sub_norm_eq
    (p q : ENNReal) [DecidableEq ι] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) (x y : WithLp p E) :
    ‖fderiv ℝ (quadratic_affine_function_on_lp p A b c) x -
        fderiv ℝ (quadratic_affine_function_on_lp p A b c) y‖ =
      ‖A.toLpLin p q (x - y)‖ := by
  rw [(quadratic_affine_function_on_lp_hasFDerivAt p A hA b c x).fderiv,
    (quadratic_affine_function_on_lp_hasFDerivAt p A hA b c y).fderiv]
  have hpairing_sub :
      lpPairingDual p (A *ᵥ ofLp x + b) - lpPairingDual p (A *ᵥ ofLp y + b) =
        lpPairingDual p (A *ᵥ (ofLp x - ofLp y)) := by
    -- The affine shift `b` cancels, leaving the pairing against `A *ᵥ (x - y)`.
    ext v
    suffices
        dotProduct (ofLp v) (A *ᵥ ofLp x + b) - dotProduct (ofLp v) (A *ᵥ ofLp y + b) =
          dotProduct (ofLp v) (A *ᵥ (ofLp x - ofLp y)) by
      simpa [lpPairingDual_apply] using this
    rw [Matrix.mulVec_sub, dotProduct_sub, dotProduct_add, dotProduct_add]
    ring
  have hclm_sub :
      LinearMap.toContinuousLinearMap (lpPairingDual p (A *ᵥ ofLp x + b)) -
          LinearMap.toContinuousLinearMap (lpPairingDual p (A *ᵥ ofLp y + b)) =
        LinearMap.toContinuousLinearMap (lpPairingDual p (A *ᵥ (ofLp x - ofLp y))) :=
    congrArg LinearMap.toContinuousLinearMap hpairing_sub
  have hdual :
      dualNorm (lpPairingDual p (A *ᵥ (ofLp x - ofLp y))) =
        ‖toLp q (A *ᵥ (ofLp x - ofLp y))‖ :=
    by
      have hdualConj :
          dualNorm (lpPairingDual p (A *ᵥ (ofLp x - ofLp y))) =
            ‖toLp (ENNReal.conjExponent p) (A *ᵥ (ofLp x - ofLp y))‖ :=
        dualNorm_lpPairingDual_eq_conjExponent_lp_norm (p := p) (A *ᵥ (ofLp x - ofLp y))
      have hconj : p.conjExponent = q := by
        letI : ENNReal.HolderConjugate p q := inferInstance
        exact ENNReal.HolderConjugate.conjExponent_eq
      rw [hconj] at hdualConj
      exact hdualConj
  rw [hclm_sub, ← dualNorm_eq_toContinuousLinearMap_norm, hdual]
  simp [Matrix.toLpLin_apply]

-- Proof sketch: `is_l_smooth_on` is the derivative Lipschitz estimate from Definition 5.1, and
-- the previous norm identity reduces that estimate to the operator norm bound for `A.toLpLin p q`.
set_option maxHeartbeats 800000 in
/-- Helper for Proposition 5.1: the induced matrix norm `Real.toNNReal ‖A‖[p,q]` is a global
smoothness parameter for the quadratic-affine function on `WithLp p (ι → ℝ)`. -/
theorem quadratic_affine_function_on_lp_is_l_smooth_on_opNorm
    (p q : ENNReal) [DecidableEq ι] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) :
    is_l_smooth_on (quadratic_affine_function_on_lp p A b c) Set.univ
      (Real.toNNReal ‖A‖[p,q]) := by
  rw [is_l_smooth_on_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Differentiability is immediate from the explicit `HasFDerivAt` formula.
    exact (quadratic_affine_function_on_lp_hasFDerivAt p A hA b c x).differentiableAt
  · intro x hx y hy
    -- The derivative-difference formula matches the source proof's `‖A (x - y)‖` estimate.
    rw [quadratic_affine_function_on_lp_fderiv_sub_norm_eq p q A hA b c x y]
    have hOp :
        ‖A.toLpLin p q‖ = (Real.toNNReal ‖A‖[p,q] : ℝ) := by
      rw [Real.toNNReal_of_nonneg (norm_nonneg ((A.toLpLin p q).toContinuousLinearMap))]
      rfl
    calc
      ‖A.toLpLin p q (x - y)‖ ≤ ‖A.toLpLin p q‖ * ‖x - y‖ := by
        simpa only [LinearMap.coe_toContinuousLinearMap] using
          (A.toLpLin p q).toContinuousLinearMap.le_opNorm (x - y)
      _ = (Real.toNNReal ‖A‖[p,q] : ℝ) * ‖x - y‖ := by
        rw [hOp]
-- Proof sketch: evaluate any smoothness inequality on a unit-ball maximizer of `A.toLpLin p q`;
-- the derivative-difference identity then forces every valid smoothness constant to dominate
-- `‖A‖[p,q]`.
/-- Helper for Proposition 5.1: every global smoothness parameter of the quadratic-affine function
dominates `Real.toNNReal ‖A‖[p,q]`. -/
private theorem quadratic_affine_function_on_lp_opNorm_le_of_is_l_smooth_on
    (p q : ENNReal) [DecidableEq ι] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) {L : NNReal}
    (hL : is_l_smooth_on (quadratic_affine_function_on_lp p A b c) Set.univ L) :
    Real.toNNReal ‖A‖[p,q] ≤ L := by
  letI : FiniteDimensional ℝ (WithLp p E) :=
    (PiLp.continuousLinearEquiv p ℝ (fun _ : ι ↦ ℝ)).toLinearEquiv.symm.finiteDimensional
  obtain ⟨xStar, hxStar_unit, hxStar_value⟩ := LinearMap.exists_norm_le_one_eq_norm (A.toLpLin p q)
  rw [is_l_smooth_on_iff] at hL
  have hbound := hL.2 xStar (by simp) 0 (by simp)
  have hbound' := hbound
  rw [quadratic_affine_function_on_lp_fderiv_sub_norm_eq p q A hA b c] at hbound'
  have hnorm_le : ‖A‖[p,q] ≤ (L : ℝ) := by
    calc
      ‖A‖[p,q] = ‖A.toLpLin p q xStar‖ := by
        simpa using hxStar_value
      _ ≤ (L : ℝ) * ‖xStar‖ := by
        simpa using hbound'
      _ ≤ (L : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hxStar_unit L.2
      _ = L := by
        simp
  change (Real.toNNReal ‖A‖[p,q] : ℝ) ≤ (L : ℝ)
  rw [Real.toNNReal_of_nonneg (norm_nonneg ((A.toLpLin p q).toContinuousLinearMap))]
  exact hnorm_le

-- Proof sketch: differentiate `quadratic_affine_function_on_lp p A b c` on the `WithLp` model;
-- the symmetry hypothesis identifies the derivative difference with the operator `A.toLpLin p q`,
-- which yields `is_l_smooth_on` with parameter `Real.toNNReal ‖A‖[p,q]`.
-- For optimality, use the unit-ball maximizer for the induced operator norm to show that any
-- smoothness constant must dominate this operator norm.
/-- Proposition 5.1: for the quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n`,
viewed with the `ℓ_p` norm on a finite real product `ι → ℝ`, and hence on `ℝ^n` when
`ι = Fin n`, the smallest global smoothness parameter is `Real.toNNReal ‖A‖[p,q]`, the textbook
induced matrix norm `‖A‖_{p,q}` for a Hölder-conjugate pair `p, q`. -/
theorem quadratic_affine_function_on_lp_opNorm_isLeast_smoothness_parameter
    (p q : ENNReal) [DecidableEq ι] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) :
    IsLeast
      {L : NNReal | is_l_smooth_on (quadratic_affine_function_on_lp p A b c) Set.univ L}
      (Real.toNNReal ‖A‖[p,q]) := by
  refine ⟨quadratic_affine_function_on_lp_is_l_smooth_on_opNorm p q A hA b c, ?_⟩
  intro L hL
  -- The upper-bound helper gives existence, and the norm-attainment helper gives optimality.
  exact quadratic_affine_function_on_lp_opNorm_le_of_is_l_smooth_on p q A hA b c hL

end

end
