/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_44
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (toLp ofLp)
open InnerProductSpace (toDualMap)
open scoped BigOperators

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin m)

/- Proposition 3.25 is `source-facing` in the Chapter 3 finite-max subdifferential calculus. Its
core owners are already upstream: Proposition 3.23 supplies the max/active-face data
`coordinatewiseMax`, `activeCoordinateFace`, and the Euclidean/dual bridges
`euclideanSubdifferentialAt`, `toLp`, and `toDualMap`. The only primitive data here are the
affine slopes `a` and offsets `b`, so the public API is organized around the source-facing
max-affine objective `piecewiseLinearMax` rather than a separate packaging layer. -/

-- Semantic recall note: `lean_leansearch` returned only generic simplex/convex-combination APIs,
-- not a reusable max-affine subdifferential theorem, so this item stays chapter-local.

-- Proof sketch: apply the finite max rule for subdifferentials to the affine family
-- `x ↦ a i ⬝ᵥ x + b i`. Each affine function has singleton Euclidean/vector-side
-- subdifferential given by the slope vector `a i`, transported into `E` through `toLp`.
-- The Euclidean subdifferential of the maximum is therefore the image of the chapter-owned active
-- face `activeCoordinateFace (fun i ↦ a i ⬝ᵥ x + b i)` under the barycentric slope map
-- `λ ↦ ∑ i, λ i • a i`, viewed in `E` through `toLp`.
/-- The max-affine objective `x ↦ max_i (a_i^T x + b_i)` on `ℝ^n`. -/
noncomputable def piecewiseLinearMax
    (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  coordinatewiseMax (fun i : Fin m ↦ a i ⬝ᵥ x + b i)

/-- Helper for Proposition 3.25: the max-affine objective is the coordinatewise maximum of the
affine value vector `A x + b`, written in Euclidean coordinates. -/
lemma piecewiseLinearMax_eq_coordinatewiseMax_affineValues
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : E) :
    piecewiseLinearMax (fun i ↦ A i) b (ofLp y) =
      coordinatewiseMax (ofLp (A.toEuclideanLin y + toLp 2 b)) := by
  -- Expand the affine value vector and compare both sides coordinatewise.
  rfl

/-- Helper for Proposition 3.25: the coordinatewise maximum is convex on `Fin m → ℝ`. -/
lemma coordinatewiseMax_convexOn [Nonempty (Fin m)] :
    ConvexOn ℝ Set.univ (coordinatewiseMax : (Fin m → ℝ) → ℝ) := by
  -- Bound each coordinate of a convex combination by the same convex combination of maxima.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  change (⨆ i : Fin m, ((α • x + β • y) i : ℝ)) ≤
    α * (⨆ i : Fin m, (x i : ℝ)) + β * (⨆ i : Fin m, (y i : ℝ))
  refine ciSup_le fun i : Fin m ↦ ?_
  calc
    (α • x + β • y) i = α * x i + β * y i := by
      simp [smul_eq_mul]
    _ ≤ α * (⨆ j : Fin m, x j) + β * (⨆ j : Fin m, y j) := by
      gcongr
      · exact Finite.le_ciSup_of_le i le_rfl
      · exact Finite.le_ciSup_of_le i le_rfl

/-- Helper for Proposition 3.25: the owner extended-real function
`z ↦ (coordinatewiseMax (ofLp z) : EReal)` is convex. -/
lemma coordinatewiseMax_isConvexFunction [Nonempty (Fin m)] :
    is_convex_function (fun z : Em ↦ (coordinatewiseMax (ofLp z) : EReal)) := by
  -- Reduce owner convexity to the real-valued coordinate model and precompose with `ofLp`.
  let coordMap : Em →ₗ[ℝ] Fin m → ℝ :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin m → ℝ)).toLinearMap
  have hconv : ConvexOn ℝ Set.univ (fun z : Em ↦ coordinatewiseMax (coordMap z)) := by
    simpa using coordinatewiseMax_convexOn.comp_linearMap coordMap
  simpa [coordMap, Function.toEReal] using
    (Function.toEReal_isConvexFunction (ω := fun z : Em ↦ coordinatewiseMax (coordMap z)) hconv)

/-- Helper for Proposition 3.25: applying `Aᵀ` to a simplex weight vector gives the Euclidean
vector of weighted slopes `∑ i, coeff i • A i`. -/
lemma transposeSlopeMatrix_apply_weights
    (A : Matrix (Fin m) (Fin n) ℝ) (coeff : Fin m → ℝ) :
    A.transpose.toEuclideanLin (toLp 2 coeff) = toLp 2 (∑ i : Fin m, coeff i • A i) := by
  -- Convert the transpose action to row-vector multiplication and then to the explicit sum.
  calc
    A.transpose.toEuclideanLin (toLp 2 coeff)
        = toLp 2 ((Matrix.toLin' A.transpose) coeff) := by
            exact Matrix.toLpLin_toLp 2 2 A.transpose coeff
    _ = toLp 2 (coeff ᵥ* A) := by
      simp [Matrix.mulVec_transpose]
    _ = toLp 2 (∑ i : Fin m, coeff i • A i) := by
      rw [Matrix.vecMul_eq_sum]

/-- Helper for Proposition 3.25: pulling back a coordinate-space Riesz functional along
`A.toEuclideanLin` is the Riesz functional of the transpose action `Aᵀ`. -/
private lemma dualMap_riesz_eq_riesz_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (z : Em) :
    (A.toEuclideanLin.dualMap (toDualMap ℝ Em z) : Module.Dual ℝ E) =
      toDualMap ℝ E (A.transpose.toEuclideanLin z) := by
  -- Compare the two dual functionals pointwise and rewrite the pairing through the adjoint.
  ext x
  have hAdj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  simpa [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, hAdj] using
    (A.toEuclideanLin.adjoint_inner_left x z).symm

/-- Helper for Proposition 3.25: the Euclidean/vector-side subdifferential of the max-affine
objective is the image of the active face of the standard simplex under the map sending a simplex
coefficient vector to the corresponding convex combination of the active slope vectors `a_i`,
viewed in `EuclideanSpace ℝ (Fin n)` through `toLp`. -/
theorem euclidean_subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace
    (hm : 0 < m) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : E) :
    euclideanSubdifferentialAt
        (fun y : E ↦ piecewiseLinearMax a b (ofLp y))
        x =
      toLp 2 ''
        ((fun coeff : Fin m → ℝ ↦ (∑ i : Fin m, coeff i • a i : Fin n → ℝ)) ''
          activeCoordinateFace (fun i : Fin m ↦ a i ⬝ᵥ ofLp x + b i)) := by
  let A : Matrix (Fin m) (Fin n) ℝ := fun i j ↦ a i j
  let φ : E →ᵃ[ℝ] Em := A.toEuclideanLin.toAffineMap + AffineMap.const ℝ E (toLp 2 b)
  let g : Em → ℝ := fun y ↦ coordinatewiseMax (ofLp y)
  let h : E → EReal := fun y ↦ ((piecewiseLinearMax a b (ofLp y) : ℝ) : EReal)
  let k : Em → EReal := fun y ↦ ((coordinatewiseMax (ofLp y) : ℝ) : EReal)
  let coordMap : Em →ₗ[ℝ] Fin m → ℝ :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin m → ℝ)).toLinearMap
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hg_convexOn : ConvexOn ℝ Set.univ g := by
    -- The coordinatewise maximum is convex on coordinates, hence also after transport to `Em`.
    simpa [g, coordMap] using coordinatewiseMax_convexOn.comp_linearMap coordMap
  have hprecompose :
      ∂ h(x) = A.toEuclideanLin.dualMap '' ∂ k(A.toEuclideanLin x + toLp 2 b) := by
    have hcomp : (fun y : E ↦ g (φ y)) = fun y : E ↦ piecewiseLinearMax a b (ofLp y) := by
      funext y
      simpa [g, φ, A] using (piecewiseLinearMax_eq_coordinatewiseMax_affineValues A b y).symm
    -- Apply the owner affine chain rule once to the coordinatewise-max model.
    simpa [h, k, hcomp, φ, g, Function.toEReal] using
      (subdifferential_precompose_affineMap_eq
        (f := g.toEReal) (φ := φ) (x := x)
        (hconvex := Function.toEReal_isConvexFunction hg_convexOn)
        (hφx := by
          simp [g, finite_domain, effective_domain, Function.toEReal]))
  have hresidual :
      ofLp (A.toEuclideanLin x + toLp 2 b) = fun i : Fin m ↦ a i ⬝ᵥ ofLp x + b i := by
    ext i
    rfl
  have htranspose :
      euclideanSubdifferentialAt (fun y : E ↦ piecewiseLinearMax a b (ofLp y)) x =
        A.transpose.toEuclideanLin ''
          euclideanSubdifferentialAt (fun y : Em ↦ coordinatewiseMax (ofLp y))
            (A.toEuclideanLin x + toLp 2 b) := by
    ext z
    constructor
    · intro hz
      -- Rewrite Euclidean membership to the owner subdifferential and pull the witness back.
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential, hprecompose] at hz
      rcases hz with ⟨g', hg', hz'⟩
      let w : Em := (InnerProductSpace.toDual ℝ Em).symm (LinearMap.toContinuousLinearMap g')
      have hw_dual : (toDualMap ℝ Em w : Module.Dual ℝ Em) = g' := by
        -- The chosen vector `w` is the Riesz representative of the owner dual witness.
        ext u
        simp [w, InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDual_symm_apply]
      have hw :
          w ∈ euclideanSubdifferentialAt (fun y : Em ↦ coordinatewiseMax (ofLp y))
            (A.toEuclideanLin x + toLp 2 b) := by
        -- Transport the owner witness back to the Euclidean-side subdifferential.
        rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
        simpa [hw_dual] using hg'
      refine ⟨w, hw, ?_⟩
      -- Identify the pulled-back Riesz functional with the transpose image of `w`.
      apply (toDualMap ℝ E).injective
      ext u
      exact congrArg (fun ψ : Module.Dual ℝ E ↦ ψ u) <| calc
        (toDualMap ℝ E (A.transpose.toEuclideanLin w) : Module.Dual ℝ E)
            = A.toEuclideanLin.dualMap (toDualMap ℝ Em w) := by
                symm
                simpa using dualMap_riesz_eq_riesz_transpose A w
        _ = A.toEuclideanLin.dualMap g' := by
          rw [hw_dual]
        _ = (toDualMap ℝ E z : Module.Dual ℝ E) := hz'
    · rintro ⟨w, hw, rfl⟩
      -- Push the Euclidean residual witness to the owner side, then apply the affine chain rule.
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential, hprecompose]
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential] at hw
      refine ⟨(toDualMap ℝ Em w : Module.Dual ℝ Em), hw, ?_⟩
      simpa using dualMap_riesz_eq_riesz_transpose A w
  -- Substitute Proposition 3.23 at the residual point and collapse the transpose image.
  rw [htranspose, euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace
    (x := A.toEuclideanLin x + toLp 2 b), hresidual]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext coeff
  simpa [A] using transposeSlopeMatrix_apply_weights A coeff

/-- Helper for Proposition 3.25: evaluating the coordinate-space dual image of a Euclidean vector
`z` on a coordinate vector `y` agrees with evaluating the Euclidean Riesz functional of `z` on
`toLp 2 y`. -/
lemma coordinateStrongDualOfEuclidean_apply
    (z : E) (y : Fin n → ℝ) :
    (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)) y =
      (toDualMap ℝ E z) (toLp 2 y) := by
  -- Both sides are the same dot-product pairing after rewriting the Euclidean inner product.
  simpa [dotProductEquiv, InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (ofLp z) y)

/-- Helper for Proposition 3.25: precomposing a real-valued function on `E` with `toLp 2`
transports its owner-side subdifferential to the Euclidean/vector-side subdifferential through the
coordinate dot-product equivalence. -/
lemma subdifferentialAt_precompose_toLp_eq_image_euclideanSubdifferentialAt
    (h : E → ℝ) (x : Fin n → ℝ) :
    subdifferentialAt (fun y : Fin n → ℝ ↦ h (toLp 2 y)) x =
      (fun z : E ↦ ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)) ''
        euclideanSubdifferentialAt h (toLp 2 x) := by
  ext g
  constructor
  · intro hg
    rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff] at hg
    let z : E :=
      toLp 2 ((((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap).symm g) :
        Fin n → ℝ)
    have hg_eq :
        ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z) = g := by
      -- The chosen `z` is defined by applying the inverse coordinate-dual equivalence to `g`.
      ext y
      simp [z]
    refine ⟨z, ?_, hg_eq⟩
    -- Pull the coordinate-space subgradient inequality back to the Euclidean model via `ofLp`.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff]
    intro u
    have hu : h (toLp 2 (ofLp u)) ≥ h (toLp 2 x) + g (ofLp u - x) := hg (ofLp u)
    have hpair :
        g (ofLp u - x) = (toDualMap ℝ E z) (u - toLp 2 x) := by
      rw [← hg_eq]
      calc
        (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)) (ofLp u - x)
            = (toDualMap ℝ E z) (toLp 2 (ofLp u - x)) :=
              coordinateStrongDualOfEuclidean_apply z (ofLp u - x)
        _ = (toDualMap ℝ E z) (u - toLp 2 x) := by
            rfl
    have hu' : h u ≥ h (toLp 2 x) + g (ofLp u - x) := by
      simpa using hu
    simpa [hpair] using hu'
  · rintro ⟨z, hz, rfl⟩
    -- Push the Euclidean subgradient inequality forward along `toLp 2`.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff] at hz
    rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff]
    intro y
    have hy : h (toLp 2 y) ≥ h (toLp 2 x) + (toDualMap ℝ E z) (toLp 2 y - toLp 2 x) :=
      hz (toLp 2 y)
    have hpair :
        (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)) (y - x) =
          (toDualMap ℝ E z) (toLp 2 y - toLp 2 x) := by
      calc
        (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)) (y - x)
            = (toDualMap ℝ E z) (toLp 2 (y - x)) :=
              coordinateStrongDualOfEuclidean_apply z (y - x)
        _ = (toDualMap ℝ E z) (toLp 2 y - toLp 2 x) := by
            rfl
    have hy' :
        h (toLp 2 y) ≥ h (toLp 2 x) +
          (((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z))
            (y - x) := by
      rw [hpair]
      exact hy
    simpa using hy'

/-- Helper for Proposition 3.25: transporting a coordinate slope vector through `toLp 2` and then
the coordinate dual identification agrees with applying the dual identification directly to that
coordinate vector. -/
lemma coordinateStrongDualOfEuclidean_toLp
    (coeff : Fin n → ℝ) :
    (fun z : E ↦ ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z))
        (toLp 2 coeff) =
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) coeff := by
  -- `ofLp` is the inverse of `toLp 2` on the coordinate model.
  simp

/-- Proposition 3.25: for the piecewise linear function
`x ↦ max_i (a_i^T x + b_i)` on `ℝ^n`, the subdifferential at `x` is the image of the active face
of the standard simplex under the map sending a simplex coefficient vector to the corresponding
convex combination of the active slope vectors `a_i`, viewed through the coordinate-space
dot-product identification. -/
theorem subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace
    (hm : 0 < m) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    subdifferentialAt (piecewiseLinearMax a b) x =
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) ''
        ((fun coeff : Fin m → ℝ ↦ (∑ i : Fin m, coeff i • a i : Fin n → ℝ)) ''
          activeCoordinateFace (fun i : Fin m ↦ a i ⬝ᵥ x + b i)) := by
  let τ : E → StrongDual ℝ (Fin n → ℝ) :=
    fun z ↦ ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap) (ofLp z)
  have htransport :
      subdifferentialAt (piecewiseLinearMax a b) x =
        τ ''
          euclideanSubdifferentialAt (fun y : E ↦ piecewiseLinearMax a b (ofLp y))
            (toLp 2 x) := by
    -- Route correction: transport the whole subgradient predicate across `toLp 2`.
    simpa [τ, WithLp.ofLp_toLp] using
      (subdifferentialAt_precompose_toLp_eq_image_euclideanSubdifferentialAt
        (h := fun y : E ↦ piecewiseLinearMax a b (ofLp y)) (x := x))
  have heuclidean :
      euclideanSubdifferentialAt (fun y : E ↦ piecewiseLinearMax a b (ofLp y)) (toLp 2 x) =
        toLp 2 ''
          ((fun coeff : Fin m → ℝ ↦ (∑ i : Fin m, coeff i • a i : Fin n → ℝ)) ''
            activeCoordinateFace (fun i : Fin m ↦ a i ⬝ᵥ x + b i)) := by
    -- Rewrite the Euclidean theorem at `toLp 2 x` back to the coordinate point `x`.
    simpa [WithLp.ofLp_toLp] using
      (euclidean_subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace hm a b
        (toLp 2 x))
  -- Route correction: combine the generic `toLp 2` transport with the Euclidean active-face
  -- formula, then normalize the outer image map.
  rw [htransport, heuclidean, Set.image_image]

end
