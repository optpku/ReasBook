/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

local notation "Z" => WithLp 2 (E₂ × E₃)

private theorem fderiv_prod_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z v : E₃}
    (hΦ : DifferentiableAt ℝ Φ (y, z)) :
    fderiv ℝ Φ (y, z) (u, v) =
      inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v := by
  have hleft :
      HasFDerivAt (fun y' : E₂ ↦ Φ (y', z))
        ((fderiv ℝ Φ (y, z)).comp (ContinuousLinearMap.inl ℝ E₂ E₃)) y := by
    simpa [Function.comp] using
      hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y z)
  have hright :
      HasFDerivAt (fun z' : E₃ ↦ Φ (y, z'))
        ((fderiv ℝ Φ (y, z)).comp (ContinuousLinearMap.inr ℝ E₂ E₃)) z := by
    simpa [Function.comp] using
      hΦ.hasFDerivAt.comp z (hasFDerivAt_prodMk_right y z)
  have hsplit : ((u, v) : E₂ × E₃) = (u, (0 : E₃)) + ((0 : E₂), v) := by
    ext <;> simp
  have hleft_apply :
      fderiv ℝ (fun y' : E₂ ↦ Φ (y', z)) y u =
        fderiv ℝ Φ (y, z) (u, (0 : E₃)) := by
    rw [hleft.fderiv]
    simp
  have hright_apply :
      fderiv ℝ (fun z' : E₃ ↦ Φ (y, z')) z v =
        fderiv ℝ Φ (y, z) ((0 : E₂), v) := by
    rw [hright.fderiv]
    simp
  calc
    fderiv ℝ Φ (y, z) (u, v)
        = fderiv ℝ Φ (y, z) (u, (0 : E₃)) + fderiv ℝ Φ (y, z) ((0 : E₂), v) := by
            rw [hsplit, map_add]
    _ = fderiv ℝ (fun y' : E₂ ↦ Φ (y', z)) y u +
          fderiv ℝ (fun z' : E₃ ↦ Φ (y, z')) z v := by
            rw [← hleft_apply, ← hright_apply]
    _ = inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v := by
            rw [← inner_gradient_left hleft.differentiableAt,
              ← inner_gradient_left hright.differentiableAt]

omit [CompleteSpace E₂] [CompleteSpace E₃] in
private theorem compositionPotential_hasFDerivAt
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x : E₁} {z : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    HasFDerivAt (compositionPotential Φ ξ)
      ((fderiv ℝ Φ (ξ x, z)).comp
        ((fderiv ℝ ξ x).prodMap (ContinuousLinearMap.id ℝ E₃))) (x, z) := by
  have hmap_has :
      HasFDerivAt (Prod.map ξ (id : E₃ → E₃))
        ((fderiv ℝ ξ x).prodMap (ContinuousLinearMap.id ℝ E₃)) (x, z) := by
    simpa using HasFDerivAt.prodMap (x, z) hξ.hasFDerivAt (hasFDerivAt_id z)
  simpa [compositionPotential, Function.comp] using hΦ.hasFDerivAt.comp (x, z) hmap_has

private theorem compositionPotential_fderiv_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z v : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v := by
  have hcomp :
      fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
        fderiv ℝ Φ (ξ x, z) (fderiv ℝ ξ x h, v) := by
    rw [(compositionPotential_hasFDerivAt hξ hΦ).fderiv]
    simp
  calc
    fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v)
        = fderiv ℝ Φ (ξ x, z) (fderiv ℝ ξ x h, v) := hcomp
    _ = inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v :=
      fderiv_prod_eq_sum_partialGradient_pairings hΦ

-- Proof sketch: differentiate the map `(x, z) ↦ (ξ x, z)` at `(x, z)`, obtaining the lifted
-- direction `(Dξ(x)[h], v)`, and then apply the chain rule together with the gradient pairing
-- formula for the directional derivative of `Φ` at `(ξ x, z)`.
/-- Theorem 5.4.6.4: under the auxiliary data from Definition 5.4.6.6, if `ξ` is
differentiable at `x` and `Φ` is differentiable at `(ξ x, z)`, then the first directional
derivative of `ψ(x, z) = Φ (ξ x, z)` in direction `(h, v)` splits into the `y`-gradient term
paired with `Dξ(x)[h]` and the `z`-gradient term paired with `v`. -/
theorem compositionPotential_lineDeriv_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z v : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    lineDeriv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v := by
  rw [(compositionPotential_hasFDerivAt hξ hΦ).differentiableAt.lineDeriv_eq_fderiv]
  exact compositionPotential_fderiv_eq_sum_partialGradient_pairings hξ hΦ

-- Proof sketch: identify the gradient of the ambient bridge
-- `w ↦ Φ w.ofLp` on the canonical `L²` product owner `Z = WithLp 2 (E₂ × E₃)` with the pair of
-- partial gradients, then expand the `L²` inner product against
-- `WithLp.toLp 2 (Dξ(x)[h], v)`.
/-- With the canonical `L²` product inner-product structure on `Z = WithLp 2 (E₂ × E₃)`, the
sum of the partial-gradient pairings is the ambient gradient pairing of `w ↦ Φ w.ofLp` against
the lifted direction `WithLp.toLp 2 (u, v)`. -/
theorem sum_partialGradient_pairings_eq_inner_gradient_pair
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z v : E₃}
    (hΦ : DifferentiableAt ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))) :
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v =
      inner ℝ
        (∇ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z)))
        (WithLp.toLp 2 (u, v)) := by
  have hΦraw : DifferentiableAt ℝ Φ (y, z) := by
    simpa using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).comp_right_differentiableAt_iff).1 hΦ
  have hchain :
      fderiv ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))
          (WithLp.toLp 2 (u, v)) =
        fderiv ℝ Φ (y, z) (u, v) := by
    have hchain_has :
        HasFDerivAt (fun w : Z ↦ Φ w.ofLp)
          ((fderiv ℝ Φ (y, z)).comp
            (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap)
          (WithLp.toLp 2 (y, z)) := by
      simpa [Function.comp] using
        hΦraw.hasFDerivAt.comp (WithLp.toLp 2 (y, z))
          (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).hasFDerivAt
    rw [hchain_has.fderiv]
    rfl
  calc
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v
      = fderiv ℝ Φ (y, z) (u, v) := by
          symm
          exact fderiv_prod_eq_sum_partialGradient_pairings hΦraw
    _ = fderiv ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))
          (WithLp.toLp 2 (u, v)) := hchain.symm
    _ = inner ℝ
          (∇ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z)))
          (WithLp.toLp 2 (u, v)) := by
          rw [← inner_gradient_left hΦ]
