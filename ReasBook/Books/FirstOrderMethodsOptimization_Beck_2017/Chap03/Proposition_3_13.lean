/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_10
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient Matrix

noncomputable section

section

variable {m : ℕ}

variable (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosDef)

/- Proposition 3.13 is a `bridge/view` item in the chapter calculus API. The source-facing input is
the Euclidean Fréchet derivative represented by `D`, while the weighted Hilbert-space owners are
kept internal and exposed through the reusable source-facing bridges `Matrix.HasQGradientAt` and
`Matrix.qGradient`. -/

-- Proof sketch: under the `H`-weighted inner product, the derivative functional `v ↦ dotProduct D
-- v` is exactly the Riesz image of `(H⁻¹).mulVec D`. First transfer the Euclidean `HasFDerivAt`
-- hypothesis to the equivalent `H`-weighted norm, then apply the `HasFDerivAt`/`HasGradientAt`
-- bridge in that weighted inner-product structure, where completeness is inferred from finite
-- dimensionality.
-- Semantic recall: mathlib provides `HasFDerivAt.hasGradientAt`,
-- `HasGradientAt.hasFDerivAt`, and `HasGradientAt.gradient` as the canonical bridge between
-- Fréchet derivatives and gradients.

/-- Helper for Proposition 3.13: a separate type alias lets the weighted norm coexist with the
ambient Euclidean norm on `ℝ^m`. -/
private def WeightedSpace (_H : Matrix (Fin m) (Fin m) ℝ) (_hH : _H.PosDef) : Type :=
  Fin m → ℝ

/-- Helper for Proposition 3.13: the weighted alias inherits the norm induced by the positive
definite matrix. -/
private instance weightedSpaceNormedAddCommGroup
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) :
    NormedAddCommGroup (WeightedSpace Q hQ) :=
  Q.toNormedAddCommGroup hQ

/-- Helper for Proposition 3.13: the weighted alias carries the `Q`-inner product. -/
private instance weightedSpaceInnerProductSpace
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) :
    InnerProductSpace ℝ (WeightedSpace Q hQ) :=
  Q.toInnerProductSpace hQ.posSemidef

/-- Helper for Proposition 3.13: the weighted alias is still finite-dimensional over `ℝ`. -/
private instance weightedSpaceFiniteDimensional
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) :
    FiniteDimensional ℝ (WeightedSpace Q hQ) := by
  dsimp [WeightedSpace]
  infer_instance

/-- Helper for Proposition 3.13: the identity map from the `H`-weighted model of `ℝ^m` to the
ambient Euclidean model is a continuous linear equivalence. -/
private noncomputable abbrev weightedToEuclidean :
    WeightedSpace H hH ≃L[ℝ] (Fin m → ℝ) :=
  { toLinearEquiv := show WeightedSpace H hH ≃ₗ[ℝ] (Fin m → ℝ) from LinearEquiv.refl ℝ _
    continuous_toFun := (show WeightedSpace H hH →ₗ[ℝ] (Fin m → ℝ) from LinearMap.id)
      |>.continuous_of_finiteDimensional
    continuous_invFun := (show (Fin m → ℝ) →ₗ[ℝ] WeightedSpace H hH from LinearMap.id)
      |>.continuous_of_finiteDimensional }

namespace Matrix

/-- `HasGradientAt` computed in the `Q`-inner product induced by
`Matrix.toInnerProductSpace`. -/
abbrev HasQGradientAt (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (f : (Fin m → ℝ) → ℝ) (g x : Fin m → ℝ) : Prop :=
  let qComplete : CompleteSpace (WeightedSpace Q hQ) := inferInstance
  @HasGradientAt ℝ (WeightedSpace Q hQ) Real.instRCLike
    (inferInstance : NormedAddCommGroup (WeightedSpace Q hQ))
    (inferInstance : InnerProductSpace ℝ (WeightedSpace Q hQ))
    qComplete
    (fun y : WeightedSpace Q hQ ↦ f y) g x

/-- The gradient of `f` at `x` computed in the `Q`-inner product induced by
`Matrix.toInnerProductSpace`. -/
noncomputable abbrev qGradient (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (f : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  let qComplete : CompleteSpace (WeightedSpace Q hQ) := inferInstance
  @gradient ℝ (WeightedSpace Q hQ) Real.instRCLike
    (inferInstance : NormedAddCommGroup (WeightedSpace Q hQ))
    (inferInstance : InnerProductSpace ℝ (WeightedSpace Q hQ))
    qComplete
    (fun y : WeightedSpace Q hQ ↦ f y) x

end Matrix

/-- Helper for Proposition 3.13: in the `H`-weighted geometry, the Riesz functional of
`(H⁻¹).mulVec D` is the Euclidean dot-product functional represented by `D`. -/
private lemma weighted_toDual_inv_mulVec_eq_dotProductBilin
    (D : Fin m → ℝ) :
    let e : WeightedSpace H hH ≃L[ℝ] (Fin m → ℝ) := weightedToEuclidean H hH
    (InnerProductSpace.toDual ℝ (WeightedSpace H hH) ((H⁻¹).mulVec D) :
      StrongDual ℝ (WeightedSpace H hH)) =
        (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)).comp
          (e : WeightedSpace H hH →L[ℝ] (Fin m → ℝ)) := by
  let e : WeightedSpace H hH ≃L[ℝ] (Fin m → ℝ) := weightedToEuclidean H hH
  -- Route correction: compare the weighted Riesz map with the Euclidean derivative after
  -- transporting the weighted variable through the identity equivalence `e`.
  ext y
  change H.qInner hH ((H⁻¹).mulVec D) y = dotProduct D y
  simpa using Matrix.qInner_invMulVec_eq_dotProduct H hH D y

/-- Under the `H`-weighted inner product on `ℝ^m`, a Euclidean derivative represented by `D`
corresponds to the gradient vector `(H⁻¹).mulVec D`. -/
theorem hasGradientAt_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    H.HasQGradientAt hH f ((H⁻¹).mulVec D) x := by
  let e : WeightedSpace H hH ≃L[ℝ] (Fin m → ℝ) := weightedToEuclidean H hH
  -- Rewrite the weighted-gradient claim to the corresponding Fréchet-derivative statement.
  rw [Matrix.HasQGradientAt, hasGradientAt_iff_hasFDerivAt]
  -- Transfer the Euclidean derivative across the identity equivalence from the weighted model.
  have hD_at_weighted_point :
      HasFDerivAt
        f
        (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D))
        ((e : WeightedSpace H hH →L[ℝ] (Fin m → ℝ)) x) := by
    simpa [weightedToEuclidean] using hD
  have hD_weighted :
      HasFDerivAt
        (fun y : WeightedSpace H hH ↦ f y)
        ((LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)).comp
          (e : WeightedSpace H hH →L[ℝ] (Fin m → ℝ)))
        x := by
    -- Transport the Euclidean derivative across the domain equivalence `e`.
    simpa [Function.comp, weightedToEuclidean] using
      (e.comp_right_hasFDerivAt_iff
        (f := f)
        (x := x)
        (f' := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D))).2
        hD_at_weighted_point
  -- Replace the transported Euclidean functional by the weighted Riesz functional.
  simpa [weighted_toDual_inv_mulVec_eq_dotProductBilin (H := H) (hH := hH) D] using hD_weighted

-- Proof sketch: apply `HasGradientAt.gradient` to
-- `hasGradientAt_inv_mulVec_of_posDef_matrix_inner`.
/-- Proposition 3.13: if the Fréchet derivative of `f` at `x` is represented by `D` through the
standard Euclidean dot product on `ℝ^m`, then replacing the inner product by
`⟪u, v⟫ = dotProduct u (H.mulVec v)` for a positive definite matrix `H` changes the gradient to
`(H⁻¹).mulVec D`. -/
theorem gradient_eq_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    H.qGradient hH f x = (H⁻¹).mulVec D := by
  -- Unfold the totalized weighted gradient and identify it through the `HasGradientAt` witness.
  rw [Matrix.qGradient]
  exact
    (hasGradientAt_inv_mulVec_of_posDef_matrix_inner (H := H) (hH := hH) hD).gradient

end
