/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_67
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Helper for Lemma 12.5: the gradient of the shifted pullback
`z ↦ ((f∗) (A.adjoint z + b)).toReal` is the pushforward by `A` of the ambient conjugate
gradient evaluated at `A.adjoint v + b`. -/
lemma shiftedGradientConjugatePullback_eq
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] V) (b : E)
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (v : V) :
    ∇ (fun z : V ↦ (((f∗) (A.adjoint z + b)).toReal)) v =
      A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) := by
  let fStarReal : E → ℝ := fun x ↦ (((f∗) x).toReal)
  let AadjMap : V →L[ℝ] E := A.adjoint.toContinuousLinearMap
  have hdiffFStar : DifferentiableAt ℝ fStarReal (A.adjoint v + b) := by
    -- Lemma 12.3 makes the primal conjugate globally smooth, hence differentiable, everywhere.
    simpa [fStarReal] using
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        σ f hf_proper hf_closed hf_strong).1
        (A.adjoint v + b)
        (by simp)
  have hdiffShifted : DifferentiableAt ℝ (fun x : E ↦ fStarReal (x + b)) (A.adjoint v) := by
    -- Recenter the differentiability statement at the shifted point `A.adjoint v + b`.
    rw [differentiableAt_comp_add_right b]
    simpa [fStarReal] using hdiffFStar
  have hderiv :
      fderiv ℝ (fun z : V ↦ fStarReal (A.adjoint z + b)) v =
        (fderiv ℝ fStarReal (A.adjoint v + b)).comp AadjMap := by
    -- Differentiate the composite `z ↦ fStarReal (A.adjoint z + b)` via the linear pullback
    -- `A.adjoint` and the shifted conjugate surface.
    change fderiv ℝ (fun z : V ↦ (fun x : E ↦ fStarReal (x + b)) (A.adjoint z)) v =
      (fderiv ℝ fStarReal (A.adjoint v + b)).comp AadjMap
    have hcomp :
        fderiv ℝ (fun z : V ↦ (fun x : E ↦ fStarReal (x + b)) (A.adjoint z)) v =
          (fderiv ℝ (fun x : E ↦ fStarReal (x + b)) (A.adjoint v)).comp AadjMap := by
      simpa [AadjMap] using (hdiffShifted.hasFDerivAt.comp v AadjMap.hasFDerivAt).fderiv
    rw [hcomp, fderiv_comp_add_right b]
  have hgradMap :
      (fderiv ℝ fStarReal (A.adjoint v + b)).comp AadjMap =
        (InnerProductSpace.toDual ℝ V)
          (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) := by
    -- Identify the Fréchet derivative with the Riesz image of the pushed-forward gradient.
    have hgradAt := hdiffFStar.hasGradientAt
    have hFDerivAt := hgradAt.hasFDerivAt
    have hgradFStar :
        fderiv ℝ fStarReal (A.adjoint v + b) =
          (InnerProductSpace.toDual ℝ E)
            (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) := by
      simpa [fStarReal] using hFDerivAt.fderiv
    ext y
    calc
      ((fderiv ℝ fStarReal (A.adjoint v + b)).comp AadjMap) y
          = fderiv ℝ fStarReal (A.adjoint v + b) (AadjMap y) := by
              rfl
      _ = fderiv ℝ fStarReal (A.adjoint v + b) (A.adjoint y) := by
            simp [AadjMap]
      _ = inner ℝ (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b)) (A.adjoint y) := by
            rw [hgradFStar, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) y := by
            rw [LinearMap.adjoint_inner_right]
      _ =
          (InnerProductSpace.toDual ℝ V)
            (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))) y := by
            rfl
  -- Convert the derivative identity back to the corresponding gradient formula.
  simpa [gradient, fStarReal] using
    congrArg ((InnerProductSpace.toDual ℝ V).symm) (hderiv.trans hgradMap)

/-- Helper for Lemma 12.5: the proximal mapping of `z ↦ (g∗) (-z)` is the negated image of the
proximal mapping of the scaled conjugate `((1 / L) • (g∗))`. -/
lemma proxNegatedConjugate_eq_negImageScaledConjugateProx
    (g : V → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) (L : PosReal) (w : V) :
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w =
      (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
  let gScaled : V → EReal := (((1 / L : PosReal) : EReal) • (g∗))
  let φ : V →ᴬ[ℝ] V := (-ContinuousLinearMap.id ℝ V).toContinuousAffineMap
  have hgConjProper : IsProperExtendedRealFunction (g∗) :=
    conjugate_function_primal_proper_of_proper_convex g hg_proper hg_convex
  have hgScaledProper : IsProperExtendedRealFunction gScaled :=
    scaled_function_proper_of_pos (g∗) (1 / L : PosReal) hgConjProper
  have hφ :
      φ.contLinear ∘L ContinuousLinearMap.adjoint φ.contLinear = (1 : ℝ) • (1 : V →L[ℝ] V) := by
    -- The negation map is an isometry, so composing it with its adjoint gives the identity.
    ext z
    simp [φ]
  calc
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w
        = prox[gScaled ∘ φ] w := by
            congr 1
    _ =
        (fun z : V ↦ w + ((1 : ℝ)⁻¹ • ContinuousLinearMap.adjoint φ.contLinear) (z - φ w)) ''
          prox[((1 : EReal) • gScaled)] (φ w) := by
            simpa using
              proximal_mapping_precompose_continuousAffineMap
                gScaled hgScaledProper φ 1 zero_lt_one hφ w
    _ = (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
      -- Simplify the affine correction for the special affine map `φ = -id`.
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ] using hz
        · simp [φ]
      · rintro ⟨z, hz, hy⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ] using hz
        · simpa [φ] using hy

/-- Helper for Lemma 12.5: the negated scaled-conjugate proximal point is equivalent to the
Chapter 12 primal `y`-step owner. -/
lemma negScaledConjugateProx_mem_iff_memDualPrimalYStep
    (g : V → EReal) (A : E →ₗ[ℝ] V) (x : E) (v yNext : V) (L : PosReal)
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) :
    yNext ∈ (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) ↔
      yNext ∈ dual_proximal_gradient_primal_y_step g A x v L := by
  rcases scaled_function_proper_closed_convex_of_pos g hg_proper hg_closed hg_convex L with
    ⟨hgScaledProper, hgScaledClosed, hgScaledConvex⟩
  rcases prox_eq_singleton_of_proper_closed_convex
      (((L : EReal) • g)) hgScaledProper hgScaledClosed hgScaledConvex
      (A x - (L : ℝ) • v) with
    ⟨p, hpSingleton⟩
  have hdualSingleton :=
    dual_moreau_prox_eq_singleton
      g hg_proper hg_closed hg_convex L (A x - (L : ℝ) • v) p hpSingleton
  have hbase :
      ((L : ℝ)⁻¹ • (A x - (L : ℝ) • v)) = ((1 / L : ℝ) • A x - v) := by
    -- Normalize the Moreau base point into the Chapter 12 forward point.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    rw [smul_sub, smul_smul]
    simp [one_div, hL]
  have hdualSingletonBase :
      prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) =
        {((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} := by
    simpa [hbase] using hdualSingleton
  have hnegResidual :
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p)) =
        v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
    -- Expand the negated Moreau residual into the Chapter 12 affine dual update.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    calc
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))
          = (L : ℝ)⁻¹ • p - (L : ℝ)⁻¹ • (A x - (L : ℝ) • v) := by
              rw [smul_sub, neg_sub]
      _ = v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
            rw [smul_sub, smul_smul]
            simp [one_div, hL, sub_eq_add_neg, add_left_comm, add_comm]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huSingleton :
        u = (L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p) := by
      have : u ∈ ({((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} : Set V) := by
        rw [hdualSingletonBase] at hu
        exact hu
      simpa using this
    -- Convert the transported Moreau singleton into the canonical Chapter 12 step witness.
    rw [mem_dual_proximal_gradient_primal_y_step_iff]
    refine ⟨p, ?_, ?_⟩
    · have hpMem : p ∈ ({p} : Set V) := by simp
      simp [hpSingleton]
    · simp [huSingleton, hnegResidual]
  · intro hy
    -- Unfold the Chapter 12 step owner and rewrite the unique prox witness back into the
    -- transported Moreau residual.
    rw [mem_dual_proximal_gradient_primal_y_step_iff] at hy
    rcases hy with ⟨p', hp', hyEq⟩
    have hp'Eq : p' = p := by
      have : p' ∈ ({p} : Set V) := by
        simpa [hpSingleton] using hp'
      simpa using this
    refine ⟨(L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p), ?_, ?_⟩
    · rw [hdualSingletonBase]
      simp
    · simp [hyEq, hp'Eq, hnegResidual]

/-- Lemma 12.5: the shifted dual proximal-gradient step for
`F(y) = f∗(A.adjoint y + b)` and `G(y) = g∗(-y)` is equivalent to the primal-representation
`y`-step at the canonical point `xTilde = ∇ (fun x ↦ (((f∗) x).toReal)) (A.adjoint v + b)`,
which is the source argmax point for `x ↦ ⟪x, A.adjoint v + b⟫ - f x`. -/
theorem dual_based_proximal_gradient_dual_step_iff_mem_dual_proximal_gradient_primal_y_step
    (σ : PosReal) (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (b : E)
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) (y v : V) (L : PosReal) :
    y ∈ dual_based_proximal_gradient_dual_step
      (fun z : V ↦ (g∗) (-z))
      (fun w ↦ ∇ (fun z : V ↦ (((f∗) (A.adjoint z + b)).toReal)) w)
      L
      v ↔
      y ∈ dual_proximal_gradient_primal_y_step
        g
        A
        (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))
        v
        L := by
  -- Rewrite the dual-step owner into the explicit proximal point at the forward-gradient base.
  rw [mem_dual_based_proximal_gradient_dual_step_iff]
  -- Normalize the shifted conjugate gradient into `A` applied to the canonical primal point.
  rw [shiftedGradientConjugatePullback_eq σ f A b hf_proper hf_closed hf_strong v]
  -- Transport the proximal mapping of `z ↦ (g∗) (-z)` through the involution `u ↦ -u`.
  rw [proxNegatedConjugate_eq_negImageScaledConjugateProx g hg_proper hg_convex L]
  -- Finish with the Moreau decomposition rewritten as the Chapter 12 primal `y`-step owner.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    negScaledConjugateProx_mem_iff_memDualPrimalYStep
      g
      A
      (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v + b))
      v
      y
      L
      hg_proper
      hg_closed
      hg_convex

end
