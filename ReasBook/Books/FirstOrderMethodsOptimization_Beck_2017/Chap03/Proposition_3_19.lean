/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual toDualMap)
open scoped BigOperators
open WithLp (ofLp toLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.19 is a `bridge/view` item in the chapter real-valued subdifferential API. The
core owner abstraction is `subdifferentialAt`, and the canonical vector-side bridge owner is
`euclideanSubdifferentialAt`. The affine pullback is already owned upstream by
`subdifferential_precompose_affineMap_eq`, while the source-facing `ℓ₁` subgradient set is
already packaged by `l1CoordinateSubgradientVectors` together with
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. This file exposes the book's
coordinate sign-cube description as the labeled statement and keeps the affine-chain-rule image
formula as a companion. -/

recall euclideanSubdifferentialAt
recall l1CoordinateSubgradientVectors
recall subdifferential_precompose_affineMap_eq
recall subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
recall sgn

/-- Helper for Proposition 3.19: the Euclidean `ℓ₁` norm on `Em` is convex on all of `Em`. -/
private theorem l1Norm_convexOn : ConvexOn ℝ Set.univ (fun y : Em ↦ ‖y‖₁) := by
  -- Transport the ambient norm convexity along the canonical `ℓ₂`-to-`ℓ₁` coordinate map.
  let l1Map : Em →ₗ[ℝ] WithLp (1 : ENNReal) (Fin m → ℝ) :=
    ((WithLp.linearEquiv (1 : ENNReal) ℝ (Fin m → ℝ)).symm.toLinearMap).comp
      ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin m → ℝ)).toLinearMap)
  have hconv : ConvexOn ℝ Set.univ (fun y : Em ↦ ‖l1Map y‖) := by
    -- The norm of any linear image is convex.
    simpa using convexOn_univ_norm.comp_linearMap l1Map
  -- Unfolding `l1Map` recovers the Euclidean `ℓ₁` norm.
  simpa [EuclideanSpace.l1Norm, l1Map] using hconv

/-- Helper for Proposition 3.19: pulling back the Riesz functional of `w` along the Euclidean
matrix map `A.toEuclideanLin` gives the Riesz functional of the transpose image
`A.transpose.toEuclideanLin w`. -/
private lemma dualMap_riesz_eq_riesz_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Em) :
    (A.toEuclideanLin.dualMap (toDualMap ℝ Em w) : Module.Dual ℝ En) =
      toDualMap ℝ En (A.transpose.toEuclideanLin w) := by
  -- Compare the two dual functionals pointwise and rewrite the pairing through the adjoint.
  ext x
  have hAdj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  simpa [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, hAdj] using
    (A.toEuclideanLin.adjoint_inner_left x w).symm

/-- Pulling back the Euclidean `ℓ₁` subdifferential along the affine map
`y ↦ A.toEuclideanLin y + b` gives the vector-form chain-rule description
`Aᵀ ∂‖·‖₁ (A.toEuclideanLin x + b)`. -/
theorem euclidean_subdifferentialAt_affine_l1_eq_transpose_image_subdifferentialAt_l1_norm
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun y : Em ↦ ‖y‖₁) (A.toEuclideanLin x + b) := by
  let φ : En →ᵃ[ℝ] Em := A.toEuclideanLin.toAffineMap + AffineMap.const ℝ En b
  let g : Em → ℝ := fun y ↦ ‖y‖₁
  have hprecompose :
      ∂ (fun y : En ↦ (((∑ i : Fin m, |(A.toEuclideanLin y + b) i|) : ℝ) : EReal))(x) =
        A.toEuclideanLin.dualMap ''
          ∂ (fun y : Em ↦ (((‖y‖₁ : ℝ)) : EReal))(A.toEuclideanLin x + b) := by
    -- Apply the owner affine chain rule once to the residual map `y ↦ A y + b`.
    simpa [φ, g, EuclideanSpace.l1Norm_eq_sum_abs, Function.toEReal] using
      (subdifferential_precompose_affineMap_eq
        g.toEReal φ x
        (Function.toEReal_isConvexFunction l1Norm_convexOn)
        (by
          simp [g, finite_domain, effective_domain, Function.toEReal]))
  ext z
  constructor
  · intro hz
    -- Convert the Euclidean witness to an owner-side dual witness and pull it back.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
      mem_strongDualSubdifferential, hprecompose] at hz
    rcases hz with ⟨g', hg', hz'⟩
    let w : Em := (toDual ℝ Em).symm (LinearMap.toContinuousLinearMap g')
    have hw_dual : (toDualMap ℝ Em w : Module.Dual ℝ Em) = g' := by
      -- The chosen vector `w` is the Riesz representative of the owner dual witness.
      ext u
      simp [w, InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDual_symm_apply]
    have hw :
        w ∈ euclideanSubdifferentialAt (fun y : Em ↦ ‖y‖₁) (A.toEuclideanLin x + b) := by
      -- Rewrite the owner witness back to the Euclidean residual subdifferential.
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
      simpa [hw_dual] using hg'
    refine ⟨w, hw, ?_⟩
    -- Identify the pulled-back Riesz functional with the transpose image of `w`.
    apply (toDualMap ℝ En).injective
    ext u
    exact congrArg (fun ψ : Module.Dual ℝ En ↦ ψ u) <| calc
      (toDualMap ℝ En (A.transpose.toEuclideanLin w) : Module.Dual ℝ En)
          = A.toEuclideanLin.dualMap (toDualMap ℝ Em w) := by
              symm
              simpa using dualMap_riesz_eq_riesz_transpose A w
      _ = A.toEuclideanLin.dualMap g' := by rw [hw_dual]
      _ = (toDualMap ℝ En z : Module.Dual ℝ En) := hz'
  · rintro ⟨w, hw, rfl⟩
    -- Push the Euclidean residual witness to the owner side and apply the affine chain rule.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
      mem_strongDualSubdifferential, hprecompose]
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential] at hw
    refine ⟨(toDualMap ℝ Em w : Module.Dual ℝ Em), hw, ?_⟩
    simpa using dualMap_riesz_eq_riesz_transpose A w

/-- Helper for Proposition 3.19: unpacking the transpose image of the residual sign-cube gives the
existential coordinate form used in the labeled statement. -/
private lemma transposeImage_toLp_l1CoordinateSubgradientVectors_eq
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Em) :
    A.transpose.toEuclideanLin '' (toLp 2 '' l1CoordinateSubgradientVectors (ofLp r)) =
      {z : En | ∃ w : Fin m → ℝ,
          z = A.transpose.toEuclideanLin (toLp 2 w) ∧
            w ∈ l1CoordinateSubgradientVectors (ofLp r)} := by
  ext z
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, hz⟩
    -- Expand the nested image witnesses into the existential statement used by the theorem.
    exact ⟨w, hz.symm, hw⟩
  · rintro ⟨w, rfl, hw⟩
    -- Repackage a coordinate witness as an element of the nested image.
    exact ⟨toLp 2 w, ⟨w, hw, rfl⟩, rfl⟩

-- Proof sketch: combine the affine chain rule with the coordinatewise `ℓ₁` sign-cube
-- description from Proposition 3.17, then rewrite the resulting image through
-- `A.transpose.toEuclideanLin`.
/-- Proposition 3.19 (1): for the affine `ℓ¹` objective
`x ↦ ∑ i, |(A.toEuclideanLin x + b) i|`, the Euclidean/vector-side subdifferential consists
exactly of the vectors `Aᵀ w` whose coefficients `w i` match the residual signs on the nonzero
coordinates of `A.toEuclideanLin x + b` and satisfy `|w i| ≤ 1` on the zero coordinates, i.e.
whose coordinate representative belongs to
`l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))`. -/
theorem euclidean_subdifferentialAt_affine_l1_eq_coordinate_sign_constraints
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x =
      {z : En | ∃ w : Fin m → ℝ,
          z = A.transpose.toEuclideanLin (toLp 2 w) ∧
            w ∈ l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))} := by
  -- Route correction: prove the affine pullback once, then rewrite the residual owner formula.
  calc
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x
        =
          A.transpose.toEuclideanLin ''
            euclideanSubdifferentialAt (fun y : Em ↦ ‖y‖₁) (A.toEuclideanLin x + b) := by
              -- The affine chain rule reduces the problem to the residual `ℓ₁` norm.
              simpa using
                euclidean_subdifferentialAt_affine_l1_eq_transpose_image_subdifferentialAt_l1_norm
                  A b x
    _ =
          A.transpose.toEuclideanLin ''
            (toLp 2 '' l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))) := by
              -- Proposition 3.17 supplies the coordinatewise residual `ℓ₁` subgradient formula.
              rw [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints]
    _ =
          {z : En | ∃ w : Fin m → ℝ,
              z = A.transpose.toEuclideanLin (toLp 2 w) ∧
                w ∈ l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))} := by
              -- Unpack the nested image into the displayed existential form.
              simpa using
                transposeImage_toLp_l1CoordinateSubgradientVectors_eq
                  A (A.toEuclideanLin x + b)

-- Proof sketch: apply the affine chain rule from Theorem 3.19 to the `ℓ₁` norm
-- `z ↦ ∑ i, |z i|`, then transport the resulting pullback through the Euclidean bridge
-- `euclideanSubdifferentialAt`. Proposition 3.17 already identifies the target-side
-- subdifferential with `l1CoordinateSubgradientVectors`, so the affine formula is exactly
-- the transpose image of that canonical source-facing set.
/-- Companion affine-chain-rule form: the Euclidean/vector-side subdifferential of the affine
`ℓ¹` objective is the transpose image of the canonical coordinatewise `ℓ₁`
subgradient set at the residual `A.toEuclideanLin x + b`. -/
theorem euclidean_subdifferentialAt_affine_l1_eq_transpose_image_l1CoordinateSubgradientVectors
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x =
      A.transpose.toEuclideanLin ''
        (toLp 2 '' l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))) := by
  calc
    euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x
        =
          A.transpose.toEuclideanLin ''
            euclideanSubdifferentialAt (fun y : Em ↦ ‖y‖₁) (A.toEuclideanLin x + b) := by
              simpa using
                euclidean_subdifferentialAt_affine_l1_eq_transpose_image_subdifferentialAt_l1_norm
                  A b x
    _ =
          A.transpose.toEuclideanLin ''
            (toLp 2 '' l1CoordinateSubgradientVectors (ofLp (A.toEuclideanLin x + b))) := by
              rw [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints]

/-- Companion membership form of Proposition 3.19 (1): a vector belongs to the Euclidean
subdifferential of the affine `ℓ¹` objective exactly when it is `Aᵀ w` for some coordinate
vector `w` satisfying the coordinatewise sign-or-interval constraints at the residual
`A.toEuclideanLin x + b`. -/
theorem mem_euclidean_subdifferentialAt_affine_l1_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x z : En) :
    z ∈ euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x ↔
      ∃ w : Fin m → ℝ,
        z = A.transpose.toEuclideanLin (toLp 2 w) ∧
          (∀ i, (A.toEuclideanLin x + b) i ≠ 0 →
            w i = Real.sign ((A.toEuclideanLin x + b) i)) ∧
          ∀ i, (A.toEuclideanLin x + b) i = 0 → |w i| ≤ 1 := by
  rw [euclidean_subdifferentialAt_affine_l1_eq_coordinate_sign_constraints]
  simp [mem_l1CoordinateSubgradientVectors_iff]

-- Proof sketch: Proposition 3.18 provides the canonical sign vector
-- `toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))` as an element of the
-- `ℓ₁` subdifferential
-- at the residual `A.toEuclideanLin x + b`. Pull that vector back through the affine chain rule
-- above; in Euclidean coordinates the pullback is represented by `A.transpose.toEuclideanLin`.
/-- Proposition 3.19 (2): taking the coordinatewise sign vector from Definition 1.27, which uses
`sgn 0 = 1`, yields a concrete element of the Euclidean/vector-side subdifferential of the affine
`ℓ¹` objective, namely `Aᵀ *ᵥ sgn (fun i ↦ (A.toEuclideanLin x + b) i)`. -/
theorem transpose_sgn_mem_subdifferentialAt_affine_l1
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    A.transpose.toEuclideanLin
        (toLp 2 (sgn (fun i ↦ (A.toEuclideanLin x + b) i))) ∈
      euclideanSubdifferentialAt
        (fun y : En ↦ ∑ i : Fin m, |(A.toEuclideanLin y + b) i|) x := by
  rw [euclidean_subdifferentialAt_affine_l1_eq_coordinate_sign_constraints]
  refine ⟨sgn (fun i ↦ (A.toEuclideanLin x + b) i), rfl, ?_⟩
  simpa using
    sign_vector_mem_l1CoordinateSubgradientVectors
      (fun i ↦ (A.toEuclideanLin x + b) i)

end
