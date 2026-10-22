/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal

-- Declarations for this item will be appended below by the statement pipeline.

section

open InnerProductSpace
open Metric

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.20 is a `bridge/view` item in the chapter real-valued subdifferential API. Its
core owner abstraction is the canonical `subdifferentialAt` from Theorem 3.4, and its Euclidean
bridge/view owner is `euclideanSubdifferentialAt`. The affine pullback step is governed upstream
by the source-facing owner theorem `subdifferential_precompose_affineMap_eq` from
Theorem 3.19, while the concrete norm-side case split already belongs to Proposition 3.15. The
primitive data here are just the affine map `y ↦ A y + b` and the owner Euclidean-norm
subdifferential; the transpose-image and piecewise singleton/ball formulas are derived API. -/

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_l2_norm_eq_piecewise

-- Proof sketch: apply the affine chain rule to `g(z) = ‖z‖`, so the dual subgradients pull back
-- along `A` by the owner theorem on `subdifferential`, then transport that canonical dual pullback
-- through the chapter bridges `strongDualSubdifferential` and `euclideanSubdifferentialAt`. In
-- Euclidean coordinates the pullback is represented by applying `Aᵀ`, and `toDualMap` converts
-- the dual-valued statement into the vector-valued image formula.
/-- Helper for Proposition 3.20: pulling back the Riesz functional of `y` along the Euclidean
matrix map `A.toEuclideanLin` gives the Riesz functional of the transpose image
`A.transpose.toEuclideanLin y`. -/
lemma dualMap_riesz_eq_riesz_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Em) :
    (A.toEuclideanLin.dualMap (toDualMap ℝ Em y) : Module.Dual ℝ En) =
      toDualMap ℝ En (A.transpose.toEuclideanLin y) := by
  -- Compare the two dual functionals pointwise and rewrite the pairing through the adjoint.
  ext x
  have hAdj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  simpa [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, hAdj] using
    (A.toEuclideanLin.adjoint_inner_left x y).symm

/-- Pulling back the Euclidean norm subdifferential along the affine map `y ↦ A y + b` gives the
vector-form chain-rule description `Aᵀ ∂‖·‖(A x + b)`. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun z : Em ↦ ‖z‖) (A.toEuclideanLin x + b) := by
  let φ : En →ᵃ[ℝ] Em := A.toEuclideanLin.toAffineMap + AffineMap.const ℝ En b
  let g : Em → ℝ := fun y ↦ ‖y‖
  have hg_convexOn : ConvexOn ℝ Set.univ g := by
    -- The residual Euclidean norm is the ambient norm, so convexity is immediate.
    simpa [g] using (convexOn_univ_norm : ConvexOn ℝ Set.univ fun y : Em ↦ ‖y‖)
  have hprecompose :
      ∂ (fun y : En ↦ ((‖A.toEuclideanLin y + b‖ : ℝ) : EReal))(x) =
        A.toEuclideanLin.dualMap ''
          ∂ (fun y : Em ↦ ((‖y‖ : ℝ) : EReal))(A.toEuclideanLin x + b) := by
    -- Apply the affine chain rule exactly once at the residual affine map `φ`.
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
        w ∈ euclideanSubdifferentialAt (fun y : Em ↦ ‖y‖) (A.toEuclideanLin x + b) := by
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

-- Proof sketch: first rewrite the affine subdifferential through the transpose-image formula
-- above. Then specialize Proposition 3.15 at the residual vector `A.toEuclideanLin x + b`; the
-- zero case gives the transpose image of the closed unit ball, and the nonzero case gives the
-- transpose of the singleton containing the normalized residual.
/-- Proposition 3.20: for `f(x) = ‖A x + b‖₂` on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing `Aᵀ ((A x + b) / ‖A x + b‖₂)` when
`A x + b ≠ 0`, and it is the image of the closed Euclidean unit ball under `Aᵀ` when
`A x + b = 0`. This is the concrete specialization of
`euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm` using the
norm formula from Proposition 3.15. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      if A.toEuclideanLin x + b = 0 then
        A.transpose.toEuclideanLin '' closedBall (0 : Em) 1
      else
        {A.transpose.toEuclideanLin
          (‖A.toEuclideanLin x + b‖⁻¹ • (A.toEuclideanLin x + b))} := by
  -- Rewrite once by the affine chain rule result, then specialize the residual-side formula.
  rw [euclidean_subdifferentialAt_affine_l2_norm_eq_transpose_image_subdifferentialAt_norm]
  by_cases h : A.toEuclideanLin x + b = 0
  · simp [h, euclidean_subdifferentialAt_l2_norm_zero_eq_closedBall]
  · simp [h,
      euclidean_subdifferentialAt_l2_norm_eq_singleton_of_ne_zero
        (x := A.toEuclideanLin x + b) h]

/-- When the affine residual `A x + b` vanishes, Proposition 3.20 specializes to the transpose
image of the closed Euclidean unit ball. -/
@[simp] theorem euclidean_subdifferentialAt_affine_l2_norm_eq_image_closedBall_of_eq_zero
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En)
    (h : A.toEuclideanLin x + b = 0) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      A.transpose.toEuclideanLin '' closedBall (0 : Em) 1 := by
  simpa [h] using
    (euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise A b x)

/-- Away from the zero residual, Proposition 3.20 specializes to the singleton containing the
transpose of the normalized affine residual. -/
theorem euclidean_subdifferentialAt_affine_l2_norm_eq_singleton_of_ne_zero
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Em) (x : En)
    (h : A.toEuclideanLin x + b ≠ 0) :
    euclideanSubdifferentialAt (fun y ↦ ‖A.toEuclideanLin y + b‖) x =
      {A.transpose.toEuclideanLin
        (‖A.toEuclideanLin x + b‖⁻¹ • (A.toEuclideanLin x + b))} := by
  simpa [h] using
    (euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise A b x)

end
