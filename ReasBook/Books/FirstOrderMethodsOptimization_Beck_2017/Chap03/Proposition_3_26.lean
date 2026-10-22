/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_24
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDualMap)
open WithLp (toLp ofLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.26 is a `bridge/view` item in the chapter's coordinate `ℓ∞` subdifferential
API. The owner abstractions already live upstream: Theorem 3.19 gives the affine-map pullback
rule on `subdifferential`, and Proposition 3.24 gives the vector-side owner formula through
`euclideanSubdifferentialAt` for the residual `ℓ∞` norm on `Fin m → ℝ`. The only primitive data
here are the affine matrix map `A.toEuclideanLin` and the offset `b`; the transpose-image formula is
derived from those owners. -/
-- Semantic recall note: `lean_leansearch` did not return a more specific affine `ℓ∞`
-- subdifferential theorem, so this item stays chapter-local and reuses Theorem 3.19 together
-- with Proposition 3.24.

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_linf_eq_piecewise

/-- Helper for Proposition 3.26: pulling back the Riesz functional of `y` along the Euclidean
matrix map `A.toEuclideanLin` gives the Riesz functional of the transpose image
`A.transpose.toEuclideanLin y`. -/
private lemma dualMap_riesz_eq_riesz_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Em) :
    (A.toEuclideanLin.dualMap (toDualMap ℝ Em y) : Module.Dual ℝ En) =
      toDualMap ℝ En (A.transpose.toEuclideanLin y) := by
  -- Compare the two dual functionals pointwise and rewrite the pairing through the adjoint.
  ext x
  have hAdj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  simpa [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, hAdj] using
    (A.toEuclideanLin.adjoint_inner_left x y).symm

-- Proof sketch: apply the affine chain rule to the `ℓ∞` norm, then reuse the source-facing
-- residual formula from Proposition 3.24. The owner-level affine pullback step is the transpose
-- image description below; Proposition 3.26 is its source-facing zero/nonzero case split.
/-- Pulling back the `ℓ∞` subdifferential along the affine map `y ↦ A y + b` gives the
vector-form chain-rule description `Aᵀ ∂‖·‖∞(A x + b)`. -/
theorem euclidean_subdifferentialAt_affine_linf_eq_transpose_image_subdifferentialAt_linf
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖ofLp (A.toEuclideanLin y + b)‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) (A.toEuclideanLin x + b) :=
  by
    let φ : En →ᵃ[ℝ] Em := A.toEuclideanLin.toAffineMap + AffineMap.const ℝ En b
    let g : Em → ℝ := fun y ↦ ‖ofLp y‖
    let coordMap : Em →ₗ[ℝ] Fin m → ℝ :=
      (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin m → ℝ)).toLinearMap
    have hg_convexOn : ConvexOn ℝ Set.univ g := by
      -- The residual `ℓ∞` norm is the ambient norm on coordinates composed with the `ofLp` map.
      have hconv : ConvexOn ℝ Set.univ (fun y : Em ↦ ‖coordMap y‖) := by
        simpa using convexOn_univ_norm.comp_linearMap coordMap
      simpa [g, coordMap] using hconv
    have hprecompose :
        ∂ (fun y : En ↦ ((‖ofLp (A.toEuclideanLin y + b)‖ : ℝ) : EReal))(x) =
          A.toEuclideanLin.dualMap ''
            ∂ (fun y : Em ↦ ((‖ofLp y‖ : ℝ) : EReal))(A.toEuclideanLin x + b) := by
      -- Apply the owner affine chain rule exactly once at the residual affine map `φ`.
      simpa [φ, g, Function.toEReal] using
        (subdifferential_precompose_affineMap_eq
          (f := g.toEReal) (φ := φ) (x := x)
          (hconvex := Function.toEReal_isConvexFunction hg_convexOn)
          (hφx := by
            simp [g, finite_domain, effective_domain, Function.toEReal]))
    ext z
    constructor
    · intro hz
      -- Rewrite Euclidean membership to the owner subdifferential and pull the witness back.
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential, hprecompose] at hz
      rcases hz with ⟨g', hg', hz'⟩
      let w : Em := (InnerProductSpace.toDual ℝ Em).symm (LinearMap.toContinuousLinearMap g')
      have hw_dual : (toDualMap ℝ Em w : Module.Dual ℝ Em) = g' := by
        -- The chosen vector `w` is exactly the Riesz representative of the owner dual witness.
        ext u
        simp [w, InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDual_symm_apply]
      have hw :
          w ∈ euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) (A.toEuclideanLin x + b) := by
        -- Transport the owner witness back to the Euclidean-side subdifferential.
        rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
        simpa [hw_dual] using hg'
      refine ⟨w, hw, ?_⟩
      -- Identify the pulled-back Riesz functional with the transpose image of `w`.
      apply (toDualMap ℝ En).injective
      ext u
      exact congrArg (fun φ : Module.Dual ℝ En ↦ φ u) <| calc
        (toDualMap ℝ En (A.transpose.toEuclideanLin w) : Module.Dual ℝ En)
            = A.toEuclideanLin.dualMap (toDualMap ℝ Em w) := by
                symm
                simpa using dualMap_riesz_eq_riesz_transpose A w
        _ = A.toEuclideanLin.dualMap g' := by rw [hw_dual]
        _ = (toDualMap ℝ En z : Module.Dual ℝ En) := hz'
    · rintro ⟨w, hw, rfl⟩
      -- Push the Euclidean residual witness to the owner side, then apply the affine chain rule.
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential, hprecompose]
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
        mem_strongDualSubdifferential] at hw
      refine ⟨(toDualMap ℝ Em w : Module.Dual ℝ Em), hw, ?_⟩
      simpa using dualMap_riesz_eq_riesz_transpose A w

-- Proof sketch: first rewrite the affine `ℓ∞` subdifferential using the transpose-image formula
-- above together with the residual-side coordinate description from Proposition 3.24. When the
-- residual `A.toEuclideanLin x + b` vanishes,
-- the `ℓ∞` subdifferential is the canonical Euclidean `ℓ₁` unit ball `{z | ‖z‖₁ ≤ 1}`, whose
-- pullback along `A` is the transpose image `Aᵀ '' {z | ‖z‖₁ ≤ 1}`. Otherwise,
-- the active signed-coordinate image from Proposition 3.24 pulls back along `A` to the transpose
-- image of those active combinations.
/-- Proposition 3.26: for the affine `ℓ∞` objective `x ↦ ‖A x + b‖∞`, the Euclidean/vector-side
subdifferential is the transpose image of the `ℓ₁` unit ball `{z | ‖z‖₁ ≤ 1}` when
`A x + b = 0`, and otherwise it is the transpose image of the active signed-coordinate image from
Proposition 3.24, evaluated at the residual `A x + b`. This is the concrete specialization of
`euclidean_subdifferentialAt_affine_linf_eq_transpose_image_subdifferentialAt_linf` using the
residual-side `ℓ∞` formula from Proposition 3.24. -/
theorem euclidean_subdifferentialAt_affine_linf_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖ofLp (A.toEuclideanLin y + b)‖) x =
      if A.toEuclideanLin x + b = 0 then
        A.transpose.toEuclideanLin '' {z : Em | ‖z‖₁ ≤ 1}
      else
        A.transpose.toEuclideanLin ''
          ((fun coeff : Fin m → ℝ ↦
              toLp 2 fun i ↦ coeff i * Real.sign (ofLp (A.toEuclideanLin x + b) i)) ''
            activeCoordinateFace (fun i ↦ |ofLp (A.toEuclideanLin x + b) i|)) :=
  by
    -- Rewrite once by the affine chain rule result, then specialize the residual-side formula.
    rw [euclidean_subdifferentialAt_affine_linf_eq_transpose_image_subdifferentialAt_linf]
    by_cases h : A.toEuclideanLin x + b = 0
    · simp [h, euclidean_subdifferentialAt_linf_zero_eq_l1_unitBall]
    · simp [h,
        euclidean_subdifferentialAt_linf_eq_signed_activeCoordinateFace
          (A.toEuclideanLin x + b) h]

end
