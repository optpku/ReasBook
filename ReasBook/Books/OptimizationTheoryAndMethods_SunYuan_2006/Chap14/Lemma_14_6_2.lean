/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)

-- Layer triage:
-- * source-facing new owner here: `compositeNonsmoothChi`, `compositeNonsmoothPsiValueSet`,
--   `compositeNonsmoothPsi`
-- * reused core mathlib directional-derivative owner: `HasDerivWithinAt` on `Set.Ici 0`
-- * reused core/canonical Section 14.6 owners from `Lemma_14_6_1`:
--   `subdifferential`, `compositeNonsmoothJacobianTranspose`,
--   `compositeNonsmoothDirectionalValueSet`, `compositeNonsmoothDF`
-- * reused earlier Chapter 14 owner via `Lemma_14_6_1`: `subdifferential` from
--   `Algorithm_14_3_1`

/-- The source quantity `χ(x, d) = h (f x) - h (f x + A(x)ᵀ d)` from `(14.6.4)`, where
`A(x) = compositeNonsmoothJacobianTranspose f x = ∇ f(x)ᵀ`. -/
def compositeNonsmoothChi
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) : ℝ :=
  h (f x) -
    h (f x + WithLp.toLp 2
      ((compositeNonsmoothJacobianTranspose f x).transpose.mulVec d.ofLp))

/-- Unfolding `compositeNonsmoothChi h f x d` gives the source formula `(14.6.4)`. -/
@[simp] theorem compositeNonsmoothChi_apply
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) :
    compositeNonsmoothChi h f x d =
      h (f x) -
        h (f x + WithLp.toLp 2
          ((compositeNonsmoothJacobianTranspose f x).transpose.mulVec d.ofLp)) :=
  rfl

/-- The source value set `{χ(x, d) | ‖d‖ ≤ t}` used to define `ψ_t(x)`. -/
def compositeNonsmoothPsiValueSet
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point) (t : ℝ) : Set ℝ :=
  {r | ∃ d : Point, ‖d‖ ≤ t ∧ compositeNonsmoothChi h f x d = r}

/-- Membership in `compositeNonsmoothPsiValueSet h f x t` is exactly the source bounded-step
condition `‖d‖ ≤ t` together with the value `r = χ(x, d)`. -/
@[simp] theorem mem_compositeNonsmoothPsiValueSet_iff
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point) (t r : ℝ) :
    r ∈ compositeNonsmoothPsiValueSet h f x t ↔
      ∃ d : Point, ‖d‖ ≤ t ∧ compositeNonsmoothChi h f x d = r :=
  Iff.rfl

/-- `ψ_t(x)` is the supremum of the source value set `{χ(x, d) | ‖d‖ ≤ t}` from `(14.6.5)`. -/
def compositeNonsmoothPsi
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (t : ℝ) (x : Point) : ℝ :=
  sSup (compositeNonsmoothPsiValueSet h f x t)

/-- Unfolding `compositeNonsmoothPsi h f t x` gives the supremum of the source constrained-value
set from `(14.6.5)`. -/
@[simp] theorem compositeNonsmoothPsi_eq_sSup
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (t : ℝ) (x : Point) :
    compositeNonsmoothPsi h f t x =
      sSup (compositeNonsmoothPsiValueSet h f x t) :=
  rfl

/-- Helper for Chapter14 Lemma 14.6.2: `χ(x, d)` is the constant term `h (f x)` minus the
convex outer function evaluated at the affine Fréchet-derivative step `f x + (fderiv ℝ f x) d`.
-/
theorem compositeNonsmoothChi_eq_sub_fderiv
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) :
    compositeNonsmoothChi h f x d =
      h (f x) - h (f x + (fderiv ℝ f x) d) := by
  let A : Matrix (Fin m) (Fin n) ℝ :=
    LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (fderiv ℝ f x).toLinearMap
  have hA_toEuclidean :
      Matrix.toEuclideanLin A = (fderiv ℝ f x).toLinearMap := by
    -- Recover the Fréchet derivative from its Euclidean matrix representation.
    ext y i
    simp [A, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [compositeNonsmoothChi_apply]
  apply congrArg (fun z ↦ h (f x) - h z)
  calc
    f x +
        WithLp.toLp 2
          ((compositeNonsmoothJacobianTranspose f x).transpose.mulVec d.ofLp)
      = f x + Matrix.toEuclideanLin A d := by
          -- Replace the source matrix owner by the Euclidean linear map it represents.
          simp [A, compositeNonsmoothJacobianTranspose_eq, Matrix.toLpLin_apply]
    _ = f x + (fderiv ℝ f x) d := by
          -- Collapse the matrix action back to the canonical derivative.
          simp [hA_toEuclidean]

/-- Helper for Chapter14 Lemma 14.6.2: the directional-value set for `DF(x, d)` is nonempty and
bounded above once the outer function is convex. -/
theorem compositeNonsmoothDirectionalValueSet_nonempty_bddAbove
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    (compositeNonsmoothDirectionalValueSet h f x d).Nonempty ∧
      BddAbove (compositeNonsmoothDirectionalValueSet h f x d) := by
  let evalSet : Set ℝ :=
    (fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) '' subdifferential h (f x)
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have h_subdiff_nonempty : (subdifferential h (f x)).Nonempty := by
    -- Convexity lets us identify the nonempty Clarke differential with the convex subdifferential.
    rcases clarkeDifferential_nonempty_of_locallyLipschitzAt h (f x) h_outer_local with ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    simpa [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
      h (f x) h_convex h_outer_local] using hξ
  have h_eval_nonempty : evalSet.Nonempty := by
    -- Evaluating any subgradient witness on the derivative direction produces a support value.
    rcases h_subdiff_nonempty with ⟨ξ, hξ⟩
    exact ⟨ξ ((fderiv ℝ f x) d), ⟨ξ, hξ, rfl⟩⟩
  have h_eval_bdd : BddAbove evalSet := by
    -- Every subgradient evaluation is controlled by the convex one-sided directional derivative.
    refine ⟨oneSidedDirectionalDeriv h (f x) ((fderiv ℝ f x) d), ?_⟩
    rintro r ⟨ξ, hξ, rfl⟩
    exact
      (mem_subdifferential_iff_le_oneSidedDirectionalDeriv_of_convexOn
        h (f x) h_convex ξ).1 hξ ((fderiv ℝ f x) d)
  have h_eval :
      compositeNonsmoothDirectionalValueSet h f x d = evalSet :=
    compositeNonsmoothDirectionalValueSet_eq_image_subdifferentialEval_fderiv h f x d
  constructor
  · simpa [h_eval] using h_eval_nonempty
  · simpa [h_eval] using h_eval_bdd

/-- Helper for Chapter14 Lemma 14.6.2: `DF(x, d)` is the real Clarke directional derivative of
the convex outer function `h` at `f x` along `(fderiv ℝ f x) d`. -/
theorem compositeNonsmoothDF_eq_clarkeDirectionalDerivReal
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    compositeNonsmoothDF h f x d =
      clarkeDirectionalDerivReal h (f x) ((fderiv ℝ f x) d) := by
  let v : ValuePoint := (fderiv ℝ f x) d
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have hgreatest :
      IsGreatest
        (((fun ξ : StrongDual ℝ ValuePoint ↦ ξ v) '' subdifferential h (f x)))
        (clarkeDirectionalDerivReal h (f x) v) := by
    -- Rewrite the maximizing Clarke-differential image through the convex subdifferential.
    simpa [v, clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
      h (f x) h_convex h_outer_local] using
      (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
        h (f x) v h_outer_local)
  calc
    compositeNonsmoothDF h f x d =
        sSup (((fun ξ : StrongDual ℝ ValuePoint ↦ ξ v) '' subdifferential h (f x))) := by
          simp [v, compositeNonsmoothDF_eq_sSup_image_subdifferentialEval_fderiv]
    _ = clarkeDirectionalDerivReal h (f x) v := hgreatest.csSup_eq

/-- Helper for Chapter14 Lemma 14.6.2: `DF(x, a • d)` is positively homogeneous in the
direction argument. -/
theorem compositeNonsmoothDF_smul_nonneg
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point) (h_convex : ConvexOn ℝ Set.univ h)
    {a : ℝ} (ha : 0 ≤ a) :
    compositeNonsmoothDF h f x (a • d) = a * compositeNonsmoothDF h f x d := by
  let v : ValuePoint := (fderiv ℝ f x) d
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have h_hom :
      clarkeDirectionalDerivReal h (f x) (a • v) =
        a * clarkeDirectionalDerivReal h (f x) v := by
    have h_hom_ereal :
        (((clarkeDirectionalDerivReal h (f x) (a • v) : ℝ) : EReal)) =
          ((a * clarkeDirectionalDerivReal h (f x) v : ℝ) : EReal) := by
      -- Pass positive homogeneity from the canonical Clarke owner down to its real-valued
      -- specialization.
      simpa [v, coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt h (f x) (a • v)
        h_outer_local, coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt h (f x) v
        h_outer_local] using
        (clarkeDirectionalDerivative_posHomogeneous
          (f := h) (x := f x) h_outer_local v a ha)
    exact_mod_cast h_hom_ereal
  calc
    compositeNonsmoothDF h f x (a • d)
      = clarkeDirectionalDerivReal h (f x) (a • v) := by
          simpa [v, map_smul] using
            (compositeNonsmoothDF_eq_clarkeDirectionalDerivReal h f x (a • d) h_convex)
    _ = a * clarkeDirectionalDerivReal h (f x) v := h_hom
    _ = a * compositeNonsmoothDF h f x d := by
          rw [compositeNonsmoothDF_eq_clarkeDirectionalDerivReal h f x d h_convex]

/-- Helper for Chapter14 Lemma 14.6.2: for fixed `x`, the map `d ↦ χ(x, d)` is continuous. -/
theorem continuous_compositeNonsmoothChi
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    Continuous (fun d : Point ↦ compositeNonsmoothChi h f x d) := by
  have h_cont : Continuous h := by
    -- A convex function on the whole finite-dimensional space is continuous everywhere.
    rw [continuous_iff_continuousAt]
    intro y
    simpa [continuousWithinAt_univ] using (h_convex.continuousOn isOpen_univ y (by simp))
  have h_affine :
      Continuous (fun d : Point ↦ f x + (fderiv ℝ f x) d) := by
    -- The Fréchet derivative at the fixed base point is a continuous linear map in `d`.
    have h_linear : Continuous (fun d : Point ↦ (fderiv ℝ f x) d) :=
      ContinuousLinearMap.continuous (fderiv ℝ f x)
    exact continuous_const.add h_linear
  have h_model :
      Continuous (fun d : Point ↦ h (f x) - h (f x + (fderiv ℝ f x) d)) :=
    continuous_const.sub (h_cont.comp h_affine)
  -- Rewrite `χ` to its affine/derivative normal form and then use continuity of the model form.
  convert h_model using 1
  ext d
  rw [compositeNonsmoothChi_eq_sub_fderiv]

/-- Helper for Chapter14 Lemma 14.6.2: on the closed ball `‖d‖ ≤ t`, `χ(x, d)` attains a
maximum. -/
theorem exists_isMaxOn_compositeNonsmoothChi_closedBall
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point) {t : ℝ} (ht : 0 ≤ t)
    (h_convex : ConvexOn ℝ Set.univ h) :
    ∃ dStar ∈ Metric.closedBall (0 : Point) t,
      IsMaxOn (fun d : Point ↦ compositeNonsmoothChi h f x d)
        (Metric.closedBall 0 t) dStar := by
  have h_nonempty : (Metric.closedBall (0 : Point) t).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [Metric.mem_closedBall] using ht
  -- Compactness of the closed ball and continuity of `χ(x, ·)` give an exact maximizer.
  exact
    (isCompact_closedBall (x := (0 : Point)) (r := t)).exists_isMaxOn h_nonempty
      (continuous_compositeNonsmoothChi h f x h_convex).continuousOn

/-- Helper for Chapter14 Lemma 14.6.2: the affine Fréchet-derivative step respects convex
combinations in the direction variable. -/
theorem compositeNonsmoothAffineStep_convexCombination
    (f : Point → ValuePoint) (x d₁ d₂ : Point) {a b : ℝ}
    (hab : a + b = 1) :
    f x + (fderiv ℝ f x) (a • d₁ + b • d₂) =
      a • (f x + (fderiv ℝ f x) d₁) + b • (f x + (fderiv ℝ f x) d₂) := by
  -- Expand the derivative across the convex combination and collect the constant base point.
  calc
    f x + (fderiv ℝ f x) (a • d₁ + b • d₂)
      = (1 : ℝ) • f x + (a • ((fderiv ℝ f x) d₁) + b • ((fderiv ℝ f x) d₂)) := by
          simp [map_add, map_smul]
    _ = (a + b) • f x + (a • ((fderiv ℝ f x) d₁) + b • ((fderiv ℝ f x) d₂)) := by
          rw [← hab]
    _ = a • (f x + (fderiv ℝ f x) d₁) + b • (f x + (fderiv ℝ f x) d₂) := by
          simp [smul_add, add_smul, add_assoc, add_left_comm]

/-- Helper for Chapter14 Lemma 14.6.2: along a scalar ray, `χ(x, t • d)` is the constant term
`h (f x)` minus the convex outer function evaluated at `f x + t • ((fderiv ℝ f x) d)`. -/
theorem compositeNonsmoothChi_ray_eq_sub_fderiv_smul
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point) (t : ℝ) :
    compositeNonsmoothChi h f x (t • d) =
      h (f x) - h (f x + t • ((fderiv ℝ f x) d)) := by
  -- Route correction: freeze the ray normalization once instead of re-expanding it in each proof.
  rw [compositeNonsmoothChi_eq_sub_fderiv]
  simp [map_smul]

/-- Helper for Chapter14 Lemma 14.6.2: `ψ_t(x)` is the supremum of the image of the closed ball
`Metric.closedBall 0 t` under the map `d ↦ χ(x, d)`. -/
theorem compositeNonsmoothPsi_eq_sSup_image_closedBall
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point) {t : ℝ} (_ht : 0 ≤ t) :
    compositeNonsmoothPsi h f t x =
      sSup ((fun d : Point ↦ compositeNonsmoothChi h f x d) '' Metric.closedBall 0 t) := by
  have hset :
      compositeNonsmoothPsiValueSet h f x t =
        ((fun d : Point ↦ compositeNonsmoothChi h f x d) '' Metric.closedBall 0 t) := by
    ext r
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, by simpa [Metric.mem_closedBall] using hd, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, by simpa [Metric.mem_closedBall] using hd, rfl⟩
  -- Rewrite the source value-set definition to the closed-ball image interface.
  rw [compositeNonsmoothPsi_eq_sSup, hset]

/-- Helper for Chapter14 Lemma 14.6.2: a maximizer of `χ(x, ·)` on the closed ball
`Metric.closedBall 0 t` realizes the supremum `ψ_t(x)`. -/
theorem compositeNonsmoothPsi_eq_compositeNonsmoothChi_of_isMaxOn_closedBall
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point) {t : ℝ} (ht : 0 ≤ t)
    {dStar : Point}
    (hdStar : dStar ∈ Metric.closedBall (0 : Point) t)
    (hmax : IsMaxOn (fun d : Point ↦ compositeNonsmoothChi h f x d)
      (Metric.closedBall 0 t) dStar) :
    compositeNonsmoothPsi h f t x = compositeNonsmoothChi h f x dStar := by
  have hgreatest :
      IsGreatest
        (((fun d : Point ↦ compositeNonsmoothChi h f x d) '' Metric.closedBall 0 t))
        (compositeNonsmoothChi h f x dStar) := by
    refine ⟨⟨dStar, hdStar, rfl⟩, ?_⟩
    intro r hr
    rcases hr with ⟨d, hd, rfl⟩
    exact (isMaxOn_iff.mp hmax) d hd
  -- The compact maximizer identifies the `sSup` value with its attained image value.
  rw [compositeNonsmoothPsi_eq_sSup_image_closedBall h f x ht]
  exact hgreatest.csSup_eq

/-- Helper for Chapter14 Lemma 14.6.2: every feasible closed-ball direction contributes a
`χ`-value bounded above by `ψ_t(x)`. -/
theorem compositeNonsmoothChi_le_compositeNonsmoothPsi_of_mem_closedBall
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point) {t : ℝ}
    (hd : d ∈ Metric.closedBall (0 : Point) t)
    (ht : 0 ≤ t)
    (h_convex : ConvexOn ℝ Set.univ h) :
    compositeNonsmoothChi h f x d ≤ compositeNonsmoothPsi h f t x := by
  rcases exists_isMaxOn_compositeNonsmoothChi_closedBall h f x ht h_convex with
    ⟨dStar, hdStar, hmax⟩
  rw [compositeNonsmoothPsi_eq_compositeNonsmoothChi_of_isMaxOn_closedBall
    h f x ht hdStar hmax]
  -- Compare the chosen feasible direction against the exact maximizer on the same closed ball.
  exact (isMaxOn_iff.mp hmax) d hd

/-- Helper for Chapter14 Lemma 14.6.2: convexity of the outer function bounds each model value
`χ(x, d)` above by `- DF(x, d)`. -/
theorem compositeNonsmoothChi_le_neg_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    compositeNonsmoothChi h f x d ≤ -compositeNonsmoothDF h f x d := by
  let v : ValuePoint := (fderiv ℝ f x) d
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have h_secant :
      oneSidedDirectionalDeriv h (f x) v ≤
        (h (f x + (1 : ℝ) • v) - h (f x)) / (1 : ℝ) := by
    -- Evaluate the convex secant inequality at the unit time parameter.
    simpa [v] using
      oneSidedDirectionalDeriv_le_secant_along_ray_of_convexOn h (f x) v h_convex zero_lt_one
  have h_df_le :
      compositeNonsmoothDF h f x d ≤ h (f x + v) - h (f x) := by
    calc
      compositeNonsmoothDF h f x d = oneSidedDirectionalDeriv h (f x) v := by
        rw [compositeNonsmoothDF_eq_clarkeDirectionalDerivReal h f x d h_convex,
          clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
            h (f x) v h_convex h_outer_local]
      _ ≤ (h (f x + (1 : ℝ) • v) - h (f x)) / (1 : ℝ) := h_secant
      _ = h (f x + v) - h (f x) := by simp
  -- After the secant bound is in place, the remaining step is linear arithmetic on real numbers.
  have hineq :
      h (f x) - h (f x + v) ≤ -compositeNonsmoothDF h f x d := by
    linarith
  rw [compositeNonsmoothChi_eq_sub_fderiv]
  simpa [v] using hineq

/-- Helper for Chapter14 Lemma 14.6.2: the uncurried map `(x, d) ↦ χ(x, d)` is continuous when
the inner map `f` is `C¹`. -/
theorem continuous_compositeNonsmoothChi_uncurry
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    Continuous (fun p : Point × Point ↦ compositeNonsmoothChi h f p.1 p.2) := by
  have h_cont : Continuous h := by
    -- A convex function on the whole finite-dimensional space is continuous everywhere.
    rw [continuous_iff_continuousAt]
    intro y
    simpa [continuousWithinAt_univ] using (h_convex.continuousOn isOpen_univ y (by simp))
  have hf_cont : Continuous f := h_contDiff.continuous
  have h_base : Continuous (fun p : Point × Point ↦ h (f p.1)) :=
    h_cont.comp (hf_cont.comp continuous_fst)
  have h_step :
      Continuous (fun p : Point × Point ↦ (fderiv ℝ f p.1 : Point →L[ℝ] ValuePoint) p.2) :=
    h_contDiff.continuous_fderiv_apply one_ne_zero
  have h_shift : Continuous (fun p : Point × Point ↦ h (f p.1 + (fderiv ℝ f p.1) p.2)) :=
    h_cont.comp ((hf_cont.comp continuous_fst).add h_step)
  have h_model :
      Continuous
        (fun p : Point × Point ↦ h (f p.1) - h (f p.1 + (fderiv ℝ f p.1) p.2)) :=
    h_base.sub h_shift
  -- Rewrite `χ` to its derivative normal form and reuse the continuity of the model expression.
  convert h_model using 1
  ext p
  rw [compositeNonsmoothChi_eq_sub_fderiv]

/-- Companion to Chapter14 Lemma 14.6.2 (1): if `h` is convex, then the directional
value set defining `DF(x, d)` has least upper bound `compositeNonsmoothDF h f x d`,
so `DF(x, d)` exists for all `x` and `d`. -/
theorem compositeNonsmoothDF_isLUB
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    IsLUB (compositeNonsmoothDirectionalValueSet h f x d) (compositeNonsmoothDF h f x d) := by
  -- Control the source support set so the conditionally complete supremum API applies.
  rcases compositeNonsmoothDirectionalValueSet_nonempty_bddAbove h f x d h_convex with
    ⟨h_nonempty, h_bdd⟩
  -- `DF(x, d)` is exactly the supremum of that directional-value set.
  simpa [compositeNonsmoothDF_eq_sSup] using (isLUB_csSup h_nonempty h_bdd)

/-- Companion to Chapter14 Lemma 14.6.2 (2): if `h` is convex, then for every fixed
`x`, the function `d ↦ compositeNonsmoothChi h f x d` is concave. -/
theorem compositeNonsmoothChi_concaveOn
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    ConcaveOn ℝ Set.univ (fun d : Point ↦ compositeNonsmoothChi h f x d) := by
  refine ⟨convex_univ, ?_⟩
  intro d₁ _ d₂ _ a b ha hb hab
  -- Route correction: use one affine-step bridge for the derivative image, then reduce the rest
  -- of the concavity inequality to the outer convexity of `h`.
  have hconv :
      h (f x + (fderiv ℝ f x) (a • d₁ + b • d₂)) ≤
        a * h (f x + (fderiv ℝ f x) d₁) + b * h (f x + (fderiv ℝ f x) d₂) := by
    rw [compositeNonsmoothAffineStep_convexCombination f x d₁ d₂ hab]
    exact h_convex.2 (by simp) (by simp) ha hb hab
  have hineq :
      a * (h (f x) - h (f x + (fderiv ℝ f x) d₁)) +
          b * (h (f x) - h (f x + (fderiv ℝ f x) d₂)) ≤
        h (f x) - h (f x + (fderiv ℝ f x) (a • d₁ + b • d₂)) := by
    calc
      a * (h (f x) - h (f x + (fderiv ℝ f x) d₁)) +
          b * (h (f x) - h (f x + (fderiv ℝ f x) d₂))
        = ((a + b) * h (f x)) -
            (a * h (f x + (fderiv ℝ f x) d₁) +
              b * h (f x + (fderiv ℝ f x) d₂)) := by ring
      _ = h (f x) -
            (a * h (f x + (fderiv ℝ f x) d₁) +
              b * h (f x + (fderiv ℝ f x) d₂)) := by
            rw [hab]
            ring
      _ ≤ h (f x) - h (f x + (fderiv ℝ f x) (a • d₁ + b • d₂)) := by
            linarith
  change a * compositeNonsmoothChi h f x d₁ + b * compositeNonsmoothChi h f x d₂ ≤
    compositeNonsmoothChi h f x (a • d₁ + b • d₂)
  rw [compositeNonsmoothChi_eq_sub_fderiv, compositeNonsmoothChi_eq_sub_fderiv,
    compositeNonsmoothChi_eq_sub_fderiv, map_add, map_smul, map_smul]
  simpa [smul_eq_mul] using hineq

/-- Companion to Chapter14 Lemma 14.6.2 (3): if `h` is convex, then the directional derivative of
`dStar ↦ compositeNonsmoothChi h f x dStar` at `dStar = 0` in direction `d` is
`- compositeNonsmoothDF h f x d`, formalized as the right derivative of
`t ↦ compositeNonsmoothChi h f x (t • d)` at `t = 0`. -/
theorem compositeNonsmoothChi_hasRightDirectionalDerivAt_zero
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x d : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    HasDerivWithinAt
      (fun t : ℝ ↦ compositeNonsmoothChi h f x (t • d))
      (-compositeNonsmoothDF h f x d) (Set.Ici 0) 0 := by
  let v : ValuePoint := (fderiv ℝ f x) d
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have h_ray :
      HasDerivWithinAt
        (fun t : ℝ ↦ h (f x + t • v))
        (oneSidedDirectionalDeriv h (f x) v) (Set.Ici 0) 0 := by
    -- Differentiate the convex scalar ray of the outer function.
    simpa [HasOneSidedDirectionalDerivAt, v] using
      convex_hasOneSidedDirectionalDerivAt_along_ray h (f x) v h_convex
  have h_model :
      HasDerivWithinAt
        (fun t : ℝ ↦ h (f x) - h (f x + t • v))
        (-oneSidedDirectionalDeriv h (f x) v) (Set.Ici 0) 0 :=
    h_ray.const_sub (h (f x))
  -- Rewrite the ray through `χ` and then replace the one-sided derivative by `DF`.
  convert h_model using 1
  · ext t
    rw [compositeNonsmoothChi_ray_eq_sub_fderiv_smul]
  · rw [compositeNonsmoothDF_eq_clarkeDirectionalDerivReal h f x d h_convex,
      clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
        h (f x) v h_convex h_outer_local]

/-- Companion to Chapter14 Lemma 14.6.2 (4): if `h` is convex, then
`compositeNonsmoothPsi h f t x` is nonnegative for every `t ≥ 0`. -/
theorem zero_le_compositeNonsmoothPsi
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point) {t : ℝ} (ht : 0 ≤ t)
    (h_convex : ConvexOn ℝ Set.univ h) :
    0 ≤ compositeNonsmoothPsi h f t x := by
  rcases exists_isMaxOn_compositeNonsmoothChi_closedBall h f x ht h_convex with
    ⟨dStar, hdStar, hmax⟩
  have hgreatest :
      IsGreatest (compositeNonsmoothPsiValueSet h f x t) (compositeNonsmoothChi h f x dStar) := by
    refine ⟨?_, ?_⟩
    · -- The maximizing direction contributes its `χ`-value to the source value set.
      exact ⟨dStar, by simpa [Metric.mem_closedBall] using hdStar, rfl⟩
    · intro r hr
      rcases hr with ⟨d, hd, rfl⟩
      -- Any feasible direction lies in the closed ball where `dStar` is maximizing.
      exact (isMaxOn_iff.mp hmax) d (by simpa [Metric.mem_closedBall] using hd)
  have hzero_mem : (0 : Point) ∈ Metric.closedBall (0 : Point) t := by
    simpa [Metric.mem_closedBall] using ht
  have hzero :
      compositeNonsmoothChi h f x (0 : Point) = 0 := by
    -- The zero step leaves the outer function unchanged.
    simp
  have h_nonneg :
      0 ≤ compositeNonsmoothChi h f x dStar := by
    -- Compare the maximizer against the always-feasible zero step.
    have := (isMaxOn_iff.mp hmax) 0 hzero_mem
    simpa [hzero] using this
  have hpsi :
      compositeNonsmoothPsi h f t x = compositeNonsmoothChi h f x dStar := by
    simpa [compositeNonsmoothPsi_eq_sSup] using hgreatest.csSup_eq
  rw [hpsi]
  exact h_nonneg

/-- Companion to Chapter14 Lemma 14.6.2 (5): if `h` is convex, then
`compositeNonsmoothPsi h f 1 x = 0` exactly when `compositeNonsmoothDF h f x d`
is nonnegative in every direction `d`, i.e. when the source stationary condition
holds at `x`. -/
theorem compositeNonsmoothPsi_one_eq_zero_iff_stationaryCondition
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    compositeNonsmoothPsi h f 1 x = 0 ↔ ∀ d : Point, 0 ≤ compositeNonsmoothDF h f x d := by
  constructor
  · intro hpsi1 d
    let a : ℝ := max 1 ‖d‖
    let u : Point := a⁻¹ • d
    have ha_pos : 0 < a := by
      exact lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖d‖)
    have ha_nonneg : 0 ≤ a := ha_pos.le
    have hu_mem :
        u ∈ Metric.closedBall (0 : Point) 1 := by
      have hnormu : ‖u‖ ≤ 1 := by
        have : ‖a⁻¹ • d‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ha_nonneg), inv_eq_one_div]
          have hd_le_a : ‖d‖ ≤ a := by
            exact le_max_right 1 ‖d‖
          have hd_le_a' : ‖d‖ ≤ (1 : ℝ) * a := by
            simpa using hd_le_a
          have hdiv : ‖d‖ / a ≤ 1 := (div_le_iff₀ ha_pos).2 hd_le_a'
          simpa [div_eq_mul_inv, mul_comm] using hdiv
        simpa [u] using this
      simpa [Metric.mem_closedBall] using hnormu
    have h_unit_nonneg : 0 ≤ compositeNonsmoothDF h f x u := by
      by_contra hneg
      have hneg' : compositeNonsmoothDF h f x u < 0 := lt_of_not_ge hneg
      let v : ValuePoint := (fderiv ℝ f x) u
      let g : ℝ → ℝ := fun t ↦ h (f x + t • v) - h (f x)
      have h_outer_local : LocallyLipschitzAt h (f x) :=
        convexOn_univ_locallyLipschitzAt h (f x) h_convex
      have h_ray :
          HasDerivWithinAt
            (fun t : ℝ ↦ h (f x + t • v))
            (oneSidedDirectionalDeriv h (f x) v) (Set.Ici 0) 0 := by
        simpa [HasOneSidedDirectionalDerivAt, v] using
          convex_hasOneSidedDirectionalDerivAt_along_ray h (f x) v h_convex
      have hderiv_neg :
          HasDerivWithinAt g
            (compositeNonsmoothDF h f x u) (Set.Ici 0) 0 := by
        -- Use the positive ray model `h (f x + t • v) - h (f x)` instead of the definally noisy
        -- negated `χ` expression.
        have h_df_eq :
            compositeNonsmoothDF h f x u = oneSidedDirectionalDeriv h (f x) v := by
          rw [compositeNonsmoothDF_eq_clarkeDirectionalDerivReal h f x u h_convex,
            clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
              h (f x) v h_convex h_outer_local]
        have hmodel :
            HasDerivWithinAt g
              (oneSidedDirectionalDeriv h (f x) v) (Set.Ici 0) 0 := by
          simpa [g] using (h_ray.sub_const (h (f x)))
        simpa [h_df_eq] using hmodel
      have hslope :
          ∃ᶠ z in nhdsWithin (0 : ℝ) (Set.Ioi 0), slope g 0 z < 0 :=
        hderiv_neg.liminf_right_slope_le hneg'
      have hposSet : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
      have hltOne :
          Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
        refine Filter.mem_of_superset
          (inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)) ?_
        intro z hz
        exact hz.2
      rcases ((hslope.and_eventually hposSet).and_eventually hltOne).exists with
        ⟨z, hz, hzLtOne⟩
      rcases hz with ⟨hzSlope, hzPosSet⟩
      have hz_pos : 0 < z := hzPosSet
      have hz_lt_one : z < 1 := hzLtOne
      have hz_mem :
          z • u ∈ Metric.closedBall (0 : Point) 1 := by
        have hnormzu : ‖z • u‖ ≤ 1 := by
          calc
            ‖z • u‖ = z * ‖u‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hz_pos]
            _ ≤ z * 1 := by gcongr; simpa [Metric.mem_closedBall] using hu_mem
            _ ≤ 1 := by nlinarith
        simpa [Metric.mem_closedBall] using hnormzu
      have hchi_le_zero : compositeNonsmoothChi h f x (z • u) ≤ 0 := by
        -- The unit-ball hypothesis `ψ₁ = 0` bounds every feasible ray point from above.
        have hfeasible :
            compositeNonsmoothChi h f x (z • u) ≤ compositeNonsmoothPsi h f 1 x :=
          compositeNonsmoothChi_le_compositeNonsmoothPsi_of_mem_closedBall
            h f x (z • u) hz_mem zero_le_one h_convex
        linarith [hfeasible, hpsi1]
      have hg_nonneg : 0 ≤ g z := by
        have hchi_ray : h (f x) ≤ h (f x + z • v) := by
          have htmp := hchi_le_zero
          rw [compositeNonsmoothChi_ray_eq_sub_fderiv_smul] at htmp
          simpa [v, sub_nonpos] using htmp
        change 0 ≤ h (f x + z • v) - h (f x)
        linarith
      have hslope_nonneg : 0 ≤ slope g 0 z := by
        have hg0 : g 0 = 0 := by
          simp [g]
        rw [slope_def_field, hg0, sub_zero]
        exact div_nonneg hg_nonneg (sub_nonneg.mpr hz_pos.le)
      linarith
    have hd_recover : a • u = d := by
      -- Recover the original direction from the normalized unit-ball direction.
      calc
        a • u = a • (a⁻¹ • d) := by rfl
        _ = (a * a⁻¹) • d := by rw [smul_smul]
        _ = d := by
          rw [mul_inv_cancel₀ ha_pos.ne', one_smul]
    have hd_recover' : d = a • u := hd_recover.symm
    have hhom :
        compositeNonsmoothDF h f x (a • u) =
          a * compositeNonsmoothDF h f x u :=
      compositeNonsmoothDF_smul_nonneg h f x u h_convex ha_nonneg
    -- Positive homogeneity transfers the unit-ball nonnegativity back to the original direction.
    have : 0 ≤ compositeNonsmoothDF h f x (a • u) := by
      rw [hhom]
      exact mul_nonneg ha_nonneg h_unit_nonneg
    simpa [hd_recover'] using this
  · intro h_nonneg
    rcases exists_isMaxOn_compositeNonsmoothChi_closedBall h f x zero_le_one h_convex with
      ⟨dStar, hdStar, hmax⟩
    have h_upper :
        compositeNonsmoothPsi h f 1 x ≤ 0 := by
      rw [compositeNonsmoothPsi_eq_compositeNonsmoothChi_of_isMaxOn_closedBall
        h f x zero_le_one hdStar hmax]
      exact
        (compositeNonsmoothChi_le_neg_compositeNonsmoothDF h f x dStar h_convex).trans
          (by linarith [h_nonneg dStar])
    exact le_antisymm h_upper (zero_le_compositeNonsmoothPsi h f x zero_le_one h_convex)

/-- Companion to Chapter14 Lemma 14.6.2 (6): if `h` is convex, then for every fixed
`x`, the function `t ↦ compositeNonsmoothPsi h f t x` is concave on `Set.Ici 0`. -/
theorem compositeNonsmoothPsi_concaveOn
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (x : Point)
    (h_convex : ConvexOn ℝ Set.univ h) :
    ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ ↦ compositeNonsmoothPsi h f t x) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro t₁ ht₁ t₂ ht₂ a b ha hb hab
  have ht₁_nonneg : 0 ≤ t₁ := ht₁
  have ht₂_nonneg : 0 ≤ t₂ := ht₂
  rcases exists_isMaxOn_compositeNonsmoothChi_closedBall h f x ht₁_nonneg h_convex with
    ⟨d₁, hd₁, hmax₁⟩
  rcases exists_isMaxOn_compositeNonsmoothChi_closedBall h f x ht₂_nonneg h_convex with
    ⟨d₂, hd₂, hmax₂⟩
  have hcombo_nonneg : 0 ≤ a * t₁ + b * t₂ := by
    nlinarith [ht₁_nonneg, ht₂_nonneg]
  have hd₁_norm : ‖d₁‖ ≤ t₁ := by
    simpa [Metric.mem_closedBall] using hd₁
  have hd₂_norm : ‖d₂‖ ≤ t₂ := by
    simpa [Metric.mem_closedBall] using hd₂
  have hcombo_mem :
      a • d₁ + b • d₂ ∈ Metric.closedBall (0 : Point) (a * t₁ + b * t₂) := by
    have hnorm :
        ‖a • d₁ + b • d₂‖ ≤ a * t₁ + b * t₂ := by
      calc
        ‖a • d₁ + b • d₂‖ ≤ ‖a • d₁‖ + ‖b • d₂‖ := norm_add_le _ _
        _ = a * ‖d₁‖ + b * ‖d₂‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * t₁ + b * t₂ := by
              nlinarith
    simpa [Metric.mem_closedBall] using hnorm
  have hchi_combo :
      a * compositeNonsmoothChi h f x d₁ + b * compositeNonsmoothChi h f x d₂ ≤
        compositeNonsmoothChi h f x (a • d₁ + b • d₂) := by
    -- Concavity of `χ` controls the convex combination of the maximizing directions.
    simpa [smul_eq_mul] using
      (compositeNonsmoothChi_concaveOn h f x h_convex).2 (by simp) (by simp) ha hb hab
  have hpsi_combo :
      compositeNonsmoothChi h f x (a • d₁ + b • d₂) ≤
        compositeNonsmoothPsi h f (a * t₁ + b * t₂) x :=
    compositeNonsmoothChi_le_compositeNonsmoothPsi_of_mem_closedBall
      h f x (a • d₁ + b • d₂) hcombo_mem hcombo_nonneg h_convex
  -- Exact maximizers identify the endpoint `ψ` values with the corresponding `χ` values.
  have hineq :
      a * compositeNonsmoothPsi h f t₁ x + b * compositeNonsmoothPsi h f t₂ x ≤
        compositeNonsmoothPsi h f (a * t₁ + b * t₂) x := by
    calc
    a * compositeNonsmoothPsi h f t₁ x + b * compositeNonsmoothPsi h f t₂ x
      = a * compositeNonsmoothChi h f x d₁ + b * compositeNonsmoothChi h f x d₂ := by
          rw [compositeNonsmoothPsi_eq_compositeNonsmoothChi_of_isMaxOn_closedBall
              h f x ht₁_nonneg hd₁ hmax₁,
            compositeNonsmoothPsi_eq_compositeNonsmoothChi_of_isMaxOn_closedBall
              h f x ht₂_nonneg hd₂ hmax₂]
    _ ≤ compositeNonsmoothChi h f x (a • d₁ + b • d₂) := hchi_combo
    _ ≤ compositeNonsmoothPsi h f (a * t₁ + b * t₂) x := hpsi_combo
  simpa [smul_eq_mul] using hineq

/-- Companion to Chapter14 Lemma 14.6.2 (7): for every fixed `t ≥ 0`, if `h` is convex
and `f` is `ContDiff ℝ 1`, then the map `x ↦ compositeNonsmoothPsi h f t x` is
continuous. -/
theorem continuous_compositeNonsmoothPsi
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    {t : ℝ} (ht : 0 ≤ t)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    Continuous (fun x : Point ↦ compositeNonsmoothPsi h f t x) := by
  have h_sup :
      Continuous
        (fun x : Point ↦
          sSup ((fun d : Point ↦ compositeNonsmoothChi h f x d) '' Metric.closedBall 0 t)) := by
    -- View `χ` as a jointly continuous two-variable function and apply compact `sSup` continuity.
    simpa using
      (isCompact_closedBall (x := (0 : Point)) (r := t)).continuous_sSup
        (f := fun x (d : Point) ↦ compositeNonsmoothChi h f x d)
        (continuous_compositeNonsmoothChi_uncurry h f h_contDiff h_convex)
  -- Rewrite `ψ_t` to the closed-ball `sSup` interface on the fixed compact parameter set.
  convert h_sup using 1
  ext x
  rw [compositeNonsmoothPsi_eq_sSup_image_closedBall h f x ht]

/-- Chapter14 Lemma 14.6.2 bundle (remaining clauses `(2)`-`(7)`)

Bundle for the remaining clauses `(2)`-`(7)`: if `h` is convex, then the source properties of
`χ(x, d)` and `ψ_t(x)` hold, and the continuity clause holds when `f` is `ContDiff ℝ 1`. -/
theorem compositeNonsmoothChiPsiBasicProperties
    (h : ValuePoint → ℝ) (f : Point → ValuePoint)
    (h_convex : ConvexOn ℝ Set.univ h) :
    (∀ x : Point,
      ConcaveOn ℝ Set.univ (fun d : Point ↦ compositeNonsmoothChi h f x d)) ∧
    (∀ x d : Point,
      HasDerivWithinAt
        (fun t : ℝ ↦ compositeNonsmoothChi h f x (t • d))
        (-compositeNonsmoothDF h f x d) (Set.Ici 0) 0) ∧
    (∀ x : Point, ∀ {t : ℝ}, 0 ≤ t → 0 ≤ compositeNonsmoothPsi h f t x) ∧
    (∀ x : Point,
      compositeNonsmoothPsi h f 1 x = 0 ↔
        ∀ d : Point, 0 ≤ compositeNonsmoothDF h f x d) ∧
    (∀ x : Point,
      ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ ↦ compositeNonsmoothPsi h f t x)) ∧
    (∀ {t : ℝ}, 0 ≤ t → ∀ _ : ContDiff ℝ 1 f,
      Continuous (fun x : Point ↦ compositeNonsmoothPsi h f t x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact compositeNonsmoothChi_concaveOn h f x h_convex
  · intro x d
    exact compositeNonsmoothChi_hasRightDirectionalDerivAt_zero h f x d h_convex
  · intro x t ht
    exact zero_le_compositeNonsmoothPsi h f x ht h_convex
  · intro x
    exact compositeNonsmoothPsi_one_eq_zero_iff_stationaryCondition h f x h_convex
  · intro x
    exact compositeNonsmoothPsi_concaveOn h f x h_convex
  · intro t ht h_contDiff
    exact continuous_compositeNonsmoothPsi h f ht h_contDiff h_convex

#print axioms compositeNonsmoothJacobianTranspose
#print axioms compositeNonsmoothChi
#print axioms compositeNonsmoothPsiValueSet
#print axioms compositeNonsmoothPsi
#print axioms compositeNonsmoothDirectionalValueSet
#print axioms compositeNonsmoothDF

end
