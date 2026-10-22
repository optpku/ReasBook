/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ConditionalGradientContraction

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Lemma 6.17 lies in the Chapter 6 dual-selection / Hölder-gradient domain.

Sampled owner-style declarations:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner for dual objectives of
  the form `u ↦ (A x) u - g(u) - μ d(u)`;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter owner for feasible
  maximizers of that dual maximand;
- `IsMaxRepresentationWithUniformlyConvexDualTerm` in `Definition_6_63`, the neighboring
  source-facing Chapter 6 owner that already records the same zero-smoothed geometry through
  `smoothedPrimalObjectiveArgmax`;
- `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the chapter owner for a
  chosen derivative field that is Hölder continuous on a feasible set.

Best owner abstraction:
- source-facing: Lemma 6.17's Hölder continuity statement for the gradient field attached to a
  maximizing selector `u`;
- core/canonical: the zero-smoothed argmax owner `smoothedPrimalObjectiveArgmax A Set.univ g 0 0`
  together with `ConditionalGradientContraction.HolderGradientOn` for the Hölder derivative
  field;
- bridge/view: the pointwise `fderiv` norm estimate below, recovered from the canonical owner
  using the assumed derivative identification `fderiv ℝ f x = A.flip (u x)`.

Primitive data:
- the dual pairing map `A`, the dual term `g`, the selector `u`, and the parameters `p`, `σg`;
- pointwise argmax membership of `u x` for the zero-smoothed chapter owner;
- differentiability of `g` through `gradg`;
- the `p`-uniform convexity inequality for `gradg`;
- the derivative identification `HasFDerivAt f (A.flip (u x)) x`.

Derived API:
- the canonical Hölder-gradient owner below;
- the source-facing pointwise derivative estimate.
-/

/-- Helper for Lemma 6.17: the zero-smoothed maximand
`u' ↦ smoothedPrimalObjectiveMaximand A g 0 0 x u' = A x u' - g u'`
has derivative `A x - gradg z` at every point `z`. -/
private lemma maximand_hasFDerivAt_sub_grad
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {g : E₂ → ℝ} {gradg : E₂ → StrongDual ℝ E₂}
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z) (x : E₁) (z : E₂) :
    HasFDerivAt (fun u' : E₂ ↦ smoothedPrimalObjectiveMaximand A g 0 0 x u')
      (A x - gradg z) z := by
  -- Differentiate the affine dual term and subtract the derivative of `g`.
  simpa [smoothedPrimalObjectiveMaximand] using (A x).hasFDerivAt.sub (hg z)

/-- Helper for Lemma 6.17: every unconstrained maximizer of
`u' ↦ smoothedPrimalObjectiveMaximand A g 0 0 x u'` satisfies the stationary equation
`gradg (u x) = A x`. -/
private lemma argmax_stationary_eq_grad
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {g : E₂ → ℝ} {u : E₁ → E₂}
    {gradg : E₂ → StrongDual ℝ E₂}
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z) (x : E₁) :
    gradg (u x) = A x := by
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Set.univ g 0 0 x (u x)).mp (hu x) with
    ⟨-, hu_max⟩
  -- Fermat's theorem turns the unconstrained maximizing property into vanishing derivative.
  have hlocal :
      IsLocalMax (fun u' : E₂ ↦ smoothedPrimalObjectiveMaximand A g 0 0 x u') (u x) :=
    hu_max.isLocalMax (by simp)
  have hzero :
      A x - gradg (u x) = 0 :=
    hlocal.hasFDerivAt_eq_zero (maximand_hasFDerivAt_sub_grad hg x (u x))
  exact (sub_eq_zero.mp hzero).symm

/-- Helper for Lemma 6.17: the selected maximizers vary Hölder continuously with exponent
`1 / (p - 1)` under the assumed uniform convexity inequality for `gradg`. -/
private lemma selector_norm_sub_le_holder_core
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {g : E₂ → ℝ} {u : E₁ → E₂}
    {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (x₁ x₂ : E₁) :
    ‖u x₁ - u x₂‖ ≤
      (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 / (p - 1))) *
        Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
  let du : ℝ := ‖u x₁ - u x₂‖
  let dx : ℝ := ‖x₁ - x₂‖
  let q : ℝ := 1 / (p - 1)
  have hp_sub_pos : 0 < p - 1 := by
    linarith
  have hq_nonneg : 0 ≤ q := by
    positivity
  have hdu_nonneg : 0 ≤ du := by
    dsimp [du]
    positivity
  have hdx_nonneg : 0 ≤ dx := by
    dsimp [dx]
    positivity
  have hstationary₁ : gradg (u x₁) = A x₁ :=
    argmax_stationary_eq_grad hu hg x₁
  have hstationary₂ : gradg (u x₂) = A x₂ :=
    argmax_stationary_eq_grad hu hg x₂
  have hdual_apply :
      (gradg (u x₁) - gradg (u x₂)) (u x₁ - u x₂) ≤ ‖A‖ * dx * du := by
    -- Rewrite the dual difference through the stationary identities and bound it by `‖A‖`.
    have h_apply_norm :
        ‖(A (x₁ - x₂)) (u x₁ - u x₂)‖ ≤ ‖A (x₁ - x₂)‖ * ‖u x₁ - u x₂‖ :=
      (A (x₁ - x₂)).le_opNorm (u x₁ - u x₂)
    have h_apply_abs :
        |(A (x₁ - x₂)) (u x₁ - u x₂)| ≤ ‖A (x₁ - x₂)‖ * ‖u x₁ - u x₂‖ := by
      simpa [Real.norm_eq_abs] using h_apply_norm
    have hA_bound : ‖A (x₁ - x₂)‖ ≤ ‖A‖ * dx := by
      simpa [dx] using A.le_opNorm (x₁ - x₂)
    have hA_sub :
        (A x₁ - A x₂) (u x₁ - u x₂) = (A (x₁ - x₂)) (u x₁ - u x₂) := by
      exact congrArg (fun L : StrongDual ℝ E₂ => L (u x₁ - u x₂)) (A.map_sub x₁ x₂).symm
    calc
      (gradg (u x₁) - gradg (u x₂)) (u x₁ - u x₂)
          = (A (x₁ - x₂)) (u x₁ - u x₂) := by
            rw [hstationary₁, hstationary₂]
            simpa [ContinuousLinearMap.sub_apply] using hA_sub
      _ ≤ ‖A (x₁ - x₂)‖ * ‖u x₁ - u x₂‖ := by
        exact le_trans (le_abs_self _) h_apply_abs
      _ ≤ (‖A‖ * ‖x₁ - x₂‖) * ‖u x₁ - u x₂‖ := by
        exact mul_le_mul_of_nonneg_right hA_bound (norm_nonneg _)
      _ = ‖A‖ * dx * du := by
        simp [du, dx, mul_assoc]
  have hcore :
      σg * Real.rpow du p ≤ ‖A‖ * dx * du := by
    exact (huniform (u x₁) (u x₂)).trans hdual_apply
  by_cases hdu : du = 0
  · -- When the selector difference vanishes, the Hölder bound is immediate.
    dsimp [du] at hdu ⊢
    rw [hdu]
    positivity
  · have hdu_pos : 0 < du := lt_of_le_of_ne hdu_nonneg (by simpa [eq_comm] using hdu)
    have hdu_pow :
        Real.rpow du p = Real.rpow du (p - 1) * du := by
      calc
        Real.rpow du p = Real.rpow du ((p - 1) + 1) := by
          congr 2
          ring
        _ = Real.rpow du (p - 1) * Real.rpow du 1 := by
          simpa using (Real.rpow_add hdu_pos (p - 1) 1)
        _ = Real.rpow du (p - 1) * du := by simp
    have hpm1_scaled :
        σg * Real.rpow du (p - 1) ≤ ‖A‖ * dx := by
      have hmul :
          (σg * Real.rpow du (p - 1)) * du ≤ (‖A‖ * dx) * du := by
        calc
          (σg * Real.rpow du (p - 1)) * du = σg * Real.rpow du p := by
            rw [hdu_pow]
            ring
          _ ≤ ‖A‖ * dx * du := hcore
          _ = (‖A‖ * dx) * du := by ring
      exact le_of_mul_le_mul_right hmul hdu_pos
    have hpm1 :
        Real.rpow du (p - 1) ≤ (‖A‖ * dx) / σg := by
      exact (le_div_iff₀ hσg).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hpm1_scaled)
    have hquot_nonneg : 0 ≤ (‖A‖ * dx) / σg := by
      positivity
    have hroot :
        du ≤ Real.rpow ((‖A‖ * dx) / σg) q := by
      simpa [q, one_div] using
        (Real.le_rpow_inv_iff_of_pos hdu_nonneg hquot_nonneg hp_sub_pos).2 hpm1
    have hsplit :
        Real.rpow ((‖A‖ * dx) / σg) q =
          (Real.rpow (1 / σg) q * Real.rpow ‖A‖ q) * Real.rpow dx q := by
      have hquot_eq : (‖A‖ * dx) / σg = (1 / σg) * (‖A‖ * dx) := by
        field_simp [hσg.ne']
      have hmul₁ :
          Real.rpow ((1 / σg) * (‖A‖ * dx)) q =
            Real.rpow (1 / σg) q * Real.rpow (‖A‖ * dx) q := by
        simpa using
          (Real.mul_rpow (show 0 ≤ 1 / σg by positivity) (show 0 ≤ ‖A‖ * dx by positivity))
      have hmul₂ :
          Real.rpow (‖A‖ * dx) q = Real.rpow ‖A‖ q * Real.rpow dx q := by
        simpa using
          (Real.mul_rpow (show 0 ≤ ‖A‖ by positivity) (show 0 ≤ dx by positivity))
      calc
        Real.rpow ((‖A‖ * dx) / σg) q
            = Real.rpow ((1 / σg) * (‖A‖ * dx)) q := by rw [hquot_eq]
        _ = Real.rpow (1 / σg) q * Real.rpow (‖A‖ * dx) q := hmul₁
        _ = Real.rpow (1 / σg) q * (Real.rpow ‖A‖ q * Real.rpow dx q) := by
              rw [hmul₂]
        _ = (Real.rpow (1 / σg) q * Real.rpow ‖A‖ q) * Real.rpow dx q := by ring
    calc
      ‖u x₁ - u x₂‖ = du := by rfl
      _ ≤ Real.rpow ((‖A‖ * dx) / σg) q := hroot
      _ = (Real.rpow (1 / σg) q * Real.rpow ‖A‖ q) * Real.rpow dx q := hsplit
      _ = (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 / (p - 1))) *
            Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
            simp [dx, q]

/-- Helper for Lemma 6.17: composing the selector Hölder bound with `A.flip` produces the
Hölder bound for the chosen derivative field `x ↦ A.flip (u x)`. -/
private lemma adjoint_selector_norm_sub_le_holder
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {g : E₂ → ℝ} {u : E₁ → E₂}
    {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (x₁ x₂ : E₁) :
    ‖A.flip (u x₁) - A.flip (u x₂)‖ ≤
      (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
        Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
  let q : ℝ := 1 / (p - 1)
  have hq_nonneg : 0 ≤ q := by
    have hp_sub_pos : 0 < p - 1 := by
      linarith
    dsimp [q]
    exact one_div_nonneg.mpr hp_sub_pos.le
  have hA_pow :
      Real.rpow ‖A‖ (1 + q) = ‖A‖ * Real.rpow ‖A‖ q := by
    have hpow :=
      Real.rpow_add_of_nonneg (norm_nonneg (A : E₁ →L[ℝ] StrongDual ℝ E₂)) hq_nonneg
        (show 0 ≤ (1 : ℝ) by positivity)
    calc
      Real.rpow ‖A‖ (1 + q) = Real.rpow ‖A‖ (q + 1) := by ring_nf
      _ = Real.rpow ‖A‖ q * Real.rpow ‖A‖ 1 := by simpa using hpow
      _ = ‖A‖ * Real.rpow ‖A‖ q := by simp [mul_comm]
  -- Apply the operator norm of `A.flip` to the selector estimate from the previous lemma.
  calc
    ‖A.flip (u x₁) - A.flip (u x₂)‖ = ‖A.flip (u x₁ - u x₂)‖ := by
      rw [map_sub]
    _ ≤ ‖A.flip‖ * ‖u x₁ - u x₂‖ := (A.flip).le_opNorm (u x₁ - u x₂)
    _ ≤ ‖A.flip‖ *
          ((Real.rpow (1 / σg) q * Real.rpow ‖A‖ q) *
            Real.rpow ‖x₁ - x₂‖ q) := by
          gcongr
          exact selector_norm_sub_le_holder_core hp hσg hu hg huniform x₁ x₂
    _ = (Real.rpow (1 / σg) q * Real.rpow ‖A‖ (1 + q)) *
          Real.rpow ‖x₁ - x₂‖ q := by
          rw [ContinuousLinearMap.opNorm_flip, hA_pow]
          ring
    _ = (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
          Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
          simp [q]

/-- Lemma 6.17 in the canonical Chapter 6 Hölder-gradient owner form: under the argmax-selection
and dual uniform-convexity hypotheses, the chosen derivative field `x ↦ A.flip (u x)`
defines `ConditionalGradientContraction.HolderGradientOn` on `Set.univ` with exponent
`v = 1 / (p - 1)` and constant `Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem holderGradientOn_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) :
    HolderGradientOn
      (Real.toNNReal (1 / (p - 1)))
      (Real.toNNReal
        (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))))
      Set.univ f (fun x ↦ A.flip (u x)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    -- On `Set.univ`, the within-derivative is exactly the ambient derivative.
    exact (hf x).hasFDerivWithinAt
  · -- Convert the real norm estimate on `A.flip ∘ u` into the `HolderOnWith` owner on `Set.univ`.
    rw [holderOnWith_univ]
    intro x y
    set C : ℝ :=
      Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))
    have hp_sub_nonneg : 0 ≤ 1 / (p - 1) := by
      have : 0 < p - 1 := by
        linarith
      exact one_div_nonneg.mpr this.le
    have hbound :=
      adjoint_selector_norm_sub_le_holder hp hσg hu hg huniform x y
    have hconst_nonneg :
        0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hbound' :
        ‖A.flip (u x) - A.flip (u y)‖ ≤ C * Real.rpow ‖x - y‖ (1 / (p - 1)) := by
      simpa [C] using hbound
    rw [edist_dist, edist_dist]
    have hq_coe : ((Real.toNNReal (1 / (p - 1)) : NNReal) : ℝ) = 1 / (p - 1) := by
      exact Real.coe_toNNReal _ hp_sub_nonneg
    rw [hq_coe]
    have hpow_enn :
        ENNReal.ofReal (dist x y) ^ (1 / (p - 1)) =
          ENNReal.ofReal (dist x y ^ (1 / (p - 1))) := by
      exact ENNReal.ofReal_rpow_of_nonneg (x := dist x y) (p := 1 / (p - 1))
        dist_nonneg hp_sub_nonneg
    rw [hpow_enn]
    change ENNReal.ofReal (dist (A.flip (u x)) (A.flip (u y))) ≤
      ENNReal.ofReal C * ENNReal.ofReal (dist x y ^ (1 / (p - 1)))
    rw [← ENNReal.ofReal_mul hconst_nonneg]
    simpa [C, dist_eq_norm] using ENNReal.ofReal_le_ofReal hbound'

-- Proof sketch: compare the first-order optimality conditions for the maximizers `u x₁` and
-- `u x₂`, use the assumed monotonicity inequality for `gradg` to bound `‖u x₁ - u x₂‖`, then
-- apply the operator-norm estimates for `A` and `A.flip` together with
-- `ContinuousLinearMap.opNorm_flip`, or equivalently reuse the canonical owner theorem above and
-- read off its pointwise Hölder bound.
/-- Lemma 6.17: if `u(x)` lies in the canonical argmax set of `u' ↦ A x u' - g(u')` for every
`x`, `g` has derivative selection `gradg` satisfying the uniform convexity inequality
`σ_g ‖u₁ - u₂‖^p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂)` with `p ≥ 2` and `σ_g > 0`, and `f` has
derivative `A.flip (u x)` at every `x` (the Lean form of `A^* u(x)`), then `∇f` is Hölder
continuous of order `v = 1 / (p - 1)` with constant
`Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem gradient_holder_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) (x₁ x₂ : E₁) :
    ‖fderiv ℝ f x₁ - fderiv ℝ f x₂‖ ≤
      (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
        Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
  -- Rewrite the derivatives using `hf` and apply the Hölder bound for `A.flip ∘ u`.
  calc
    ‖fderiv ℝ f x₁ - fderiv ℝ f x₂‖
        = ‖A.flip (u x₁) - A.flip (u x₂)‖ := by
            rw [(hf x₁).fderiv, (hf x₂).fderiv]
    _ ≤
        (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
          Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := by
            exact adjoint_selector_norm_sub_le_holder hp hσg hu hg huniform x₁ x₂

end
