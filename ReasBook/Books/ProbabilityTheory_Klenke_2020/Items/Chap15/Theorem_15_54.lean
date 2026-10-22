/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_53

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {d : ℕ}
variable {X : Ω → EuclideanSpace ℝ (Fin d)}
variable {μ : EuclideanSpace ℝ (Fin d)} {C : Matrix (Fin d) (Fin d) ℝ}

-- Proof sketch: this is the coordinate projection of the canonical mean identity
-- `HasMultivariateNormalLaw.integral_eq_mean`.
/-- Item (i) for theorem 15.54: if `X` has multivariate Gaussian law `N_{μ,C}`, then the
expectation of its `i`th coordinate is `μ i`. -/
theorem integral_coord_eq_mean_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (i : Fin d) :
    ∫ ω, X ω i ∂P = μ i := by
  -- Push the owner law of `X` through the coordinate evaluation map.
  have hcoord :
      HasLaw (fun ω ↦ X ω i) (gaussianReal (μ i) (C i i).toNNReal) P := by
    simpa [Function.comp] using
      (measurePreserving_eval_multivariateGaussian (μ := μ) (S := C) hX.posDef.posSemidef
        (i := i)).hasLaw.comp hX.hasLaw
  -- The mean of the resulting real Gaussian is the target coordinate.
  rw [hcoord.integral_eq, integral_id_gaussianReal]

-- Proof sketch: this is exactly `HasMultivariateNormalLaw.covariance_eval_eq`.
/-- Item (ii) for theorem 15.54: if `X` has multivariate Gaussian law `N_{μ,C}` and `C` is
positive definite, then the covariance of coordinates `i` and `j` is `C i j`. -/
theorem covariance_coord_eq_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (i j : Fin d) :
    cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] = C i j :=
  hX.covariance_eval_eq i j

-- Proof sketch: push the law of `X` forward along the continuous linear functional
-- `x ↦ ⟪λ, x⟫`; the image of `multivariateGaussian μ C` under that map is the one-dimensional
-- Gaussian law with mean `⟪λ, μ⟫` and variance `λᵀ C λ`.
/-- Helper for theorem 15.54: pushing `multivariateGaussian μ C` forward along the linear
functional `x ↦ ⟪v, x⟫` gives the corresponding one-dimensional Gaussian law. -/
lemma innerMap_multivariateGaussian_eq_gaussianReal
    (hC : C.PosSemidef) (v : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian μ C).map
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d)) v) =
      gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v))) := by
  -- Rewrite the pushforward through the abstract Gaussian map identity.
  rw [IsGaussian.map_eq_gaussianReal]
  congr
  · -- The pushed-forward mean is the inner product against `μ`.
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp [InnerProductSpace.toDualMap_apply_apply]
  · -- The pushed-forward variance is the quadratic form defined by `C`.
    calc
      Var[⇑((InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d))) v);
          multivariateGaussian μ C]
          = covarianceBilin (multivariateGaussian μ C) v v := by
              simpa [InnerProductSpace.toDualMap_apply_apply] using
                (covarianceBilin_self IsGaussian.memLp_two_id v).symm
      _ = dotProduct v (Matrix.mulVec C v) := covarianceBilin_multivariateGaussian hC v v

/-- Item (iii) for theorem 15.54: every linear functional of a multivariate Gaussian random
vector is a one-dimensional Gaussian with the corresponding mean and variance. -/
theorem hasLaw_inner_eq_gaussianReal_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (v : EuclideanSpace ℝ (Fin d)) :
    HasLaw (fun ω ↦ ⟪v, X ω⟫)
      (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d)) v
  -- First identify the linear image of the owner Gaussian law.
  have hL :
      HasLaw L
        (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v))))
        (multivariateGaussian μ C) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [L] using innerMap_multivariateGaussian_eq_gaussianReal (μ := μ) (C := C)
      hX.posDef.posSemidef v
  -- Then compose that owner law with the stored law of `X`.
  simpa [L, Function.comp, InnerProductSpace.toDualMap_apply_apply] using hL.comp hX.hasLaw

-- Proof sketch: identify the law of `X` with `multivariateGaussian μ C` via `hX`, then rewrite
-- the characteristic function using `charFun_multivariateGaussian`.
/-- Item (iv) for theorem 15.54: the characteristic function of a multivariate Gaussian random
vector with mean `μ` and covariance `C` is `t ↦ exp (i⟪t, μ⟫ - ⟪t, Ct⟫ / 2)`. -/
theorem charFun_eq_exp_of_hasMultivariateNormalLaw
    (hX : HasMultivariateNormalLaw X P μ C) (t : EuclideanSpace ℝ (Fin d)) :
    MeasureTheory.charFun (P.map X) t =
      Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) := by
  -- Replace the law of `X` by the canonical multivariate Gaussian owner law.
  rw [hX.hasLaw.map_eq, charFun_multivariateGaussian hX.posDef.posSemidef]

/-- Helper for theorem 15.54: Gaussian laws for all inner products force `X` to be
`P`-almost-everywhere measurable. -/
lemma aemeasurable_of_allInner_gaussianLaw
    (hlinear : ∀ v : EuclideanSpace ℝ (Fin d),
      HasLaw (fun ω ↦ ⟪v, X ω⟫)
        (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P) :
    AEMeasurable X P := by
  -- Recover each coordinate from the corresponding basis vector projection.
  have hcoord :
      AEMeasurable (fun ω i ↦ X ω i) P := by
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    have hi := (hlinear (EuclideanSpace.basisFun (Fin d) ℝ i)).aemeasurable
    rw [show (fun ω ↦ ⟪EuclideanSpace.basisFun (Fin d) ℝ i, X ω⟫) = fun ω ↦ X ω i by
      funext ω
      simpa using (EuclideanSpace.basisFun_inner (x := X ω) (i := i))] at hi
    exact hi
  simpa using
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable.comp_aemeasurable hcoord

/-- Helper for theorem 15.54: the prescribed Gaussian laws for all inner products imply the
multivariate Gaussian characteristic-function formula for `P.map X`. -/
lemma charFun_eq_exp_of_allInner_gaussianLaw
    (hX_meas : AEMeasurable X P) (hC : C.PosDef)
    (hlinear : ∀ v : EuclideanSpace ℝ (Fin d),
      HasLaw (fun ω ↦ ⟪v, X ω⟫)
        (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P)
    (t : EuclideanSpace ℝ (Fin d)) :
    MeasureTheory.charFun (P.map X) t =
      Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) := by
  -- Rewrite the vector characteristic function as the scalar one of the projected law.
  rw [MeasureTheory.charFun_eq_charFunDual_toDualMap, MeasureTheory.charFunDual_eq_charFun_map_one]
  have hmap :
      (P.map X).map (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d)) t) =
        P.map (fun ω ↦ ⟪t, X ω⟫) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX_meas]
    exact Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ rfl
  -- Apply the assumed scalar Gaussian law at `t`.
  rw [hmap, (hlinear t).map_eq, charFun_gaussianReal]
  have hnonneg : 0 ≤ dotProduct t (Matrix.mulVec C t) := hC.posSemidef.dotProduct_mulVec_nonneg t
  simp [Real.toNNReal_of_nonneg hnonneg]

/-- Helper for theorem 15.54: the multivariate Gaussian characteristic-function formula
determines the law of `X` to be `multivariateGaussian μ C`. -/
lemma hasMultivariateNormalLaw_of_charFun_eq_exp
    (hC : C.PosDef)
    (hchar : ∀ t : EuclideanSpace ℝ (Fin d),
      MeasureTheory.charFun (P.map X) t =
        Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2)) :
    HasMultivariateNormalLaw X P μ C := by
  -- The displayed characteristic function already forces `P.map X` to be a probability measure.
  have hprob : IsProbabilityMeasure (P.map X) := by
    rw [MeasureTheory.isProbabilityMeasure_iff_real]
    simpa using hchar 0
  letI : IsProbabilityMeasure (P.map X) := hprob
  -- Characteristic functions identify the pushforward law of `X`.
  have hmap : P.map X = multivariateGaussian μ C := by
    apply Measure.ext_of_charFun
    ext t
    rw [hchar t, charFun_multivariateGaussian hC.posSemidef]
  -- The identified pushforward is nonzero, so `X` is a genuine random variable.
  have hX_meas : AEMeasurable X P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hmap]
    exact IsProbabilityMeasure.ne_zero _
  exact ⟨hC, ⟨hX_meas, hmap⟩⟩

-- Proof sketch: for the forward implication, unpack `HasMultivariateNormalLaw` and apply the
-- previous linear-image Gaussian theorem. For the converse implication, combine `hC` with the
-- Gaussianity of all linear functionals to identify `P.map X` with `multivariateGaussian μ C`.
/-- The linear-form equivalence for theorem 15.54: `X` has multivariate normal law `N_{μ,C}`
exactly when `C` is positive
definite and every linear functional `⟪λ, X⟫` has the corresponding one-dimensional Gaussian law.
-/
theorem hasMultivariateNormalLaw_iff_all_linearForms_gaussian :
    HasMultivariateNormalLaw X P μ C ↔
      C.PosDef ∧
        ∀ v : EuclideanSpace ℝ (Fin d),
          HasLaw (fun ω ↦ ⟪v, X ω⟫)
            (gaussianReal ⟪v, μ⟫ (Real.toNNReal (dotProduct v (Matrix.mulVec C v)))) P := by
  constructor
  · intro hX
    -- The forward implication is the stored positivity plus the linear-image law.
    exact ⟨hX.posDef, hasLaw_inner_eq_gaussianReal_of_hasMultivariateNormalLaw hX⟩
  · rintro ⟨hC, hlinear⟩
    -- Recover measurability, then identify the characteristic function of `P.map X`.
    have hX_meas : AEMeasurable X P := aemeasurable_of_allInner_gaussianLaw hlinear
    have hchar :
        ∀ t : EuclideanSpace ℝ (Fin d),
          MeasureTheory.charFun (P.map X) t =
            Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) :=
      charFun_eq_exp_of_allInner_gaussianLaw hX_meas hC hlinear
    exact hasMultivariateNormalLaw_of_charFun_eq_exp hC hchar

-- Proof sketch: the forward implication is `charFun_eq_exp_of_hasMultivariateNormalLaw`. For the
-- converse implication, the displayed formula identifies the characteristic function of `P.map X`
-- with that of `multivariateGaussian μ C`; together with `hC`, this yields the owner law.
/-- Theorem 15.54: `X` has multivariate normal law `N_{μ,C}` exactly when `C` is positive
definite and the characteristic function of `P.map X` is
`t ↦ exp (i⟪t, μ⟫ - ⟪t, Ct⟫ / 2)`. -/
theorem hasMultivariateNormalLaw_iff_charFun_eq :
    HasMultivariateNormalLaw X P μ C ↔
      C.PosDef ∧
        ∀ t : EuclideanSpace ℝ (Fin d),
          MeasureTheory.charFun (P.map X) t =
            Complex.exp (⟪t, μ⟫ * Complex.I - dotProduct t (Matrix.mulVec C t) / 2) := by
  constructor
  · intro hX
    -- The forward implication is the stored positivity plus the owner characteristic function.
    exact ⟨hX.posDef, charFun_eq_exp_of_hasMultivariateNormalLaw hX⟩
  · rintro ⟨hC, hchar⟩
    -- The converse is exactly the characteristic-function reconstruction helper.
    exact hasMultivariateNormalLaw_of_charFun_eq_exp hC hchar
