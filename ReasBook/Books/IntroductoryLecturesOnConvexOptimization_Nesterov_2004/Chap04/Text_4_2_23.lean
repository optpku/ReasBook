/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DegreeConditioning FunctionClasses

/- Text 4.2.23 lies in Chapter 4's degree-conditioning example domain.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`, the chapter owner for the source functions `d₂` and `d₃`
* `powerDistance_two_uniformConvexityParameter` and
  `powerDistance_three_uniformConvexityParameter` in `Text_4_2_7`
* `powerDistance_three_lipschitzConstant` in `Text_4_2_7`
* `IsInFunctionClassF23` in `Definition_4_2_17`, the chapter owner for `𝓕₂₃`

Source/core/bridge triage:
* source-facing: the example `ξ_{α,β}`
* core/canonical: `powerDistance`, `σ[p](f)`, `L[p](f)`, and `f ∈ 𝓕₂₃`
* bridge/view: the exact identities for `σ₂`, `σ₃`, and `L₃` of `ξ_{α,β}`

Primitive data:
* the positive coefficients `α` and `β`, carried canonically by `NNRealˣ`
* the chapter owners `powerDistance (2 : ℝ) (0 : E)` and `powerDistance (3 : ℝ) (0 : E)`

Derived API:
* the source-facing function `xi_alpha_beta`
* the exact conditioning identities `σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`,
  and `L₃(ξ_{α,β}) = 2β`
* the resulting membership `ξ_{α,β} ∈ 𝓕₂₃`

The previous refinement replaced the conditioning example by a lattice-distance periodicity model,
which erased the mathematical content of Text 4.2.23. This file returns to the chapter's
conditioning owners: `ξ_{α,β}` is built directly from the canonical `powerDistance` owners from
Text 4.2.7, and the public surface states the exact `σ₂`/`σ₃`/`L₃` identities together with the
`𝓕₂₃` consequence. -/

section Basic

variable (E : Type u) [NormedAddCommGroup E]

/-- The source-facing example
`ξ_{α,β} = α d₂ + β d₃`, with `d₂` and `d₃` realized by the chapter owner `powerDistance` at the
origin. The positive coefficients are carried by the project-standard owner `NNRealˣ`. -/
def xi_alpha_beta (α β : NNRealˣ) : E → ℝ :=
  (α : ℝ) • powerDistance (2 : ℝ) (0 : E) + (β : ℝ) • powerDistance (3 : ℝ) (0 : E)

/-- Expanding `xi_alpha_beta α β` at `x` gives the textbook formula
`α d₂(x) + β d₃(x)`. -/
@[simp] theorem xi_alpha_beta_apply (α β : NNRealˣ) (x : E) :
    xi_alpha_beta E α β x =
      (α : ℝ) * powerDistance (2 : ℝ) (0 : E) x +
        (β : ℝ) * powerDistance (3 : ℝ) (0 : E) x :=
  rfl

end Basic

section Conditioning

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

/-- Helper for Text 4 2 23: scaling a whole-space uniform-convexity witness by a nonnegative
scalar rescales the power modulus by the same factor. -/
lemma uniformConvexOn_nonneg_smul
    {f : E → ℝ} {σ p c : ℝ} (hc : 0 ≤ c)
    (hf : UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f) :
    UniformConvexOn Set.univ (uniformConvexPowerModulus (c * σ) p) (c • f) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Scale the source witness inequality by the nonnegative coefficient.
  simpa [smul_eq_mul, uniformConvexPowerModulus, sub_eq_add_neg, mul_add, add_mul, mul_assoc,
    mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc

/-- Helper for Text 4 2 23: decreasing the coefficient in a positive power modulus preserves a
whole-space uniform-convexity witness. -/
lemma uniformConvexOn_mono_parameter
    {f : E → ℝ} {σ τ p : ℝ} (hp : 0 < p) (hστ : σ ≤ τ)
    (hf : UniformConvexOn Set.univ (uniformConvexPowerModulus τ p) f) :
    UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Compare the two remainder terms through the monotonicity in the coefficient.
  have hbase := hf.2 hx hy ha hb hab
  have hrpow_nonneg : 0 ≤ Real.rpow ‖x - y‖ p := Real.rpow_nonneg (norm_nonneg _) _
  have hcoef_nonneg : 0 ≤ (1 / p) * Real.rpow ‖x - y‖ p := by positivity
  have hmod_le :
      uniformConvexPowerModulus σ p ‖x - y‖ ≤ uniformConvexPowerModulus τ p ‖x - y‖ := by
    dsimp [uniformConvexPowerModulus]
    calc
      ((1 / p) * σ) * Real.rpow ‖x - y‖ p
          = ((1 / p) * Real.rpow ‖x - y‖ p) * σ := by ring
      _ ≤ ((1 / p) * Real.rpow ‖x - y‖ p) * τ := by
            gcongr
      _ = ((1 / p) * τ) * Real.rpow ‖x - y‖ p := by ring
  have hright :
      a * f x + b * f y - a * b * uniformConvexPowerModulus τ p ‖x - y‖ ≤
        a * f x + b * f y - a * b * uniformConvexPowerModulus σ p ‖x - y‖ := by
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
    nlinarith
  exact hbase.trans hright

/-- Helper for Text 4 2 23: any strict sub-parameter of `σ[p](f)` is itself a whole-space
uniform-convexity witness. -/
lemma uniformConvexOn_of_lt_uniformConvexityParameter
    {p : ℕ} {f : E → ℝ} [HasUniformConvexityParameterOfDegree p f]
    (hp : 0 < (p : ℝ)) {σ : ℝ} (_hσ_pos : 0 < σ) (hσ_lt : σ < σ[p](f)) :
    UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f := by
  let S : Set ℝ := {τ : ℝ |
    0 < τ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus τ (p : ℝ)) f}
  have hnonempty : Set.Nonempty S := HasUniformConvexityParameterOfDegree.nonempty
  change σ < sSup S at hσ_lt
  obtain ⟨τ, hτS, hστ⟩ := exists_lt_of_lt_csSup hnonempty hσ_lt
  exact uniformConvexOn_mono_parameter (p := (p : ℝ)) hp (le_of_lt hστ) hτS.2

/-- Helper for Text 4 2 23: `uniformConvexPowerModulus σ p r` is nonnegative whenever `σ`, `p`,
and `r` are nonnegative. -/
lemma uniformConvexPowerModulus_nonneg {σ p r : ℝ}
    (hσ : 0 ≤ σ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    0 ≤ uniformConvexPowerModulus σ p r := by
  dsimp [uniformConvexPowerModulus]
  have hrpow : 0 ≤ Real.rpow r p := Real.rpow_nonneg hr p
  exact mul_nonneg (mul_nonneg (by positivity) hσ) hrpow

/-- Helper for Text 4 2 23: a whole-space uniform-convexity witness is convex once its modulus is
nonnegative on nonnegative radii. -/
lemma uniformConvexOn_convexOn_of_nonneg
    {f : E → ℝ} {φ : ℝ → ℝ}
    (hf : UniformConvexOn Set.univ φ f)
    (hφ : ∀ r ≥ 0, 0 ≤ φ r) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbase := hf.2 hx hy ha hb hab
  have hφnorm : 0 ≤ φ ‖x - y‖ := hφ ‖x - y‖ (norm_nonneg _)
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hdrop :
      a * f x + b * f y - a * b * φ ‖x - y‖ ≤ a * f x + b * f y := by
    nlinarith
  exact hbase.trans hdrop

/-- Helper for Text 4 2 23: every nontrivial real inner-product space contains a unit vector,
which is the direction used to obtain coarse witness upper bounds. -/
lemma exists_unit_vector : ∃ u : E, ‖u‖ = 1 := by
  -- Normalize a nonzero vector to obtain a unit test direction.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨‖x‖⁻¹ • x, ?_⟩
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    ‖‖x‖⁻¹ • x‖ = |‖x‖⁻¹| * ‖x‖ := norm_smul _ _
    _ = ‖x‖⁻¹ * ‖x‖ := by rw [abs_of_pos (inv_pos.mpr hxnorm)]
    _ = 1 := inv_mul_cancel₀ hxnorm.ne'

/-- Helper for Text 4 2 23: `ξ_{α,β}` vanishes at the origin. -/
@[simp] lemma xi_alpha_beta_zero (α β : NNRealˣ) :
    xi_alpha_beta E α β (0 : E) = 0 := by
  -- Expand the definition and use that both centered power distances vanish at the center.
  rw [xi_alpha_beta_apply, powerDistance_apply, powerDistance_apply]
  simp

/-- Helper for Text 4 2 23: along a unit vector, the mixed example has the textbook value
`α / 2 + β / 3`. -/
lemma xi_alpha_beta_apply_unit (α β : NNRealˣ) {u : E} (hu : ‖u‖ = 1) :
    xi_alpha_beta E α β u = (α : ℝ) / 2 + (β : ℝ) / 3 := by
  -- Evaluate both norm-power owners on a unit vector.
  rw [xi_alpha_beta_apply, powerDistance_apply, powerDistance_apply]
  simp [hu]
  ring

/-- Helper for Text 4 2 23: at the midpoint direction `(1 / 2) • u` of a unit vector, the mixed
example has value `α / 8 + β / 24`. -/
lemma xi_alpha_beta_apply_half_unit (α β : NNRealˣ) {u : E} (hu : ‖u‖ = 1) :
    xi_alpha_beta E α β ((1 / 2 : ℝ) • u) = (α : ℝ) / 8 + (β : ℝ) / 24 :=
by
  -- Evaluate both power-distance owners at `‖(1 / 2) • u‖ = 1 / 2`.
  rw [xi_alpha_beta_apply, powerDistance_apply, powerDistance_apply]
  have hnorm : ‖((1 / 2 : ℝ) • u)‖ = 1 / 2 := by
    simpa [hu] using norm_smul (1 / 2 : ℝ) u
  have hnorm0 : ‖((1 / 2 : ℝ) • u) - (0 : E)‖ = 1 / 2 := by
    simpa using hnorm
  rw [hnorm0]
  ring_nf

/-- Helper for Text 4 2 23: along a nonnegative dilation of a unit vector, `ξ_{α,β}` reduces to
the expected quadratic-plus-cubic polynomial. -/
lemma xi_alpha_beta_apply_smul_unit (α β : NNRealˣ) {u : E} (hu : ‖u‖ = 1) {t : ℝ}
    (ht : 0 ≤ t) :
    xi_alpha_beta E α β (t • u) =
      (α : ℝ) * t ^ (2 : ℕ) / 2 + (β : ℝ) * t ^ (3 : ℕ) / 3 := by
  -- Rewrite the norm of `t • u` as `t` and then normalize the two power terms.
  rw [xi_alpha_beta_apply, powerDistance_apply, powerDistance_apply]
  have hnorm : ‖t • u‖ = t := by
    simpa [hu, abs_of_nonneg ht] using norm_smul t u
  simp [hnorm, Real.rpow_natCast]
  ring

/-- Helper for Text 4 2 23: the second Taylor coefficient is isometric to the second Fréchet
derivative. -/
lemma ftaylorSeriesCoeffTwo_normSub_eq_sndFDeriv_normSub {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x y : E) :
    ‖ftaylorSeries ℝ f x 2 - ftaylorSeries ℝ f y 2‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  -- Rewrite the Taylor coefficient through `iteratedFDeriv`, then curry twice.
  have hx : ftaylorSeries ℝ f x 2 = iteratedFDeriv ℝ 2 f x :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl x
  have hy : ftaylorSeries ℝ f y 2 = iteratedFDeriv ℝ 2 f y :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl y
  rw [hx, hy]
  let eEquiv : (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) :=
    continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ
  let e : (E [×2]→L[ℝ] ℝ) →ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) := eEquiv.toLinearIsometry
  have hx' : e (iteratedFDeriv ℝ 2 f x) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x := by
    -- The second iterated derivative is the curried first derivative of `fderiv`.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hy' : e (iteratedFDeriv ℝ 2 f y) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y := by
    -- The same identification holds at the second base point.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hdist :
      dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) =
        dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) := by
    simpa [hx', hy'] using (e.dist_map (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y)).symm
  have hiter :
      dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) =
        dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y) := by
    let e1 : (E [×1]→L[ℝ] E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    have hx1 : e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x) = fderiv ℝ (fderiv ℝ f) x := by
      ext z
      simp [e1]
    have hy1 : e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) = fderiv ℝ (fderiv ℝ f) y := by
      ext z
      simp [e1]
    simpa [hx1, hy1] using
      (e1.dist_map (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
        (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y)).symm
  calc
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ =
        dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) := by
          rw [dist_eq_norm]
    _ = dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y) := hdist.trans hiter
    _ = ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
          exact dist_eq_norm (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y)

/-- Helper for Text 4 2 23: a Hessian-Lipschitz witness on `C22[L]` yields the corresponding
whole-space Taylor-coefficient witness `𝒞^{2,2}_{L}(Set.univ)`. -/
lemma mem_taylorCoeffLipschitzClass_of_memC22 {L : NNReal} {f : E → ℝ}
    (hf : HasLipschitzContinuousHessian L f) :
    f ∈ 𝒞^{2,2}_{L}(Set.univ) := by
  refine ⟨by norm_num, ftaylorSeries ℝ f, ?_, ?_⟩
  · -- The twice continuously differentiable owner provides the whole-space Taylor witness.
    rw [hasFTaylorSeriesUpToOn_univ_iff]
    exact hf.contDiff.ftaylorSeries
  · -- Rewrite the second Taylor coefficient through `fderiv (fderiv f)`.
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    calc
      ‖ftaylorSeries ℝ f x 2 - ftaylorSeries ℝ f y 2‖ =
          ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
            exact ftaylorSeriesCoeffTwo_normSub_eq_sndFDeriv_normSub hf.contDiff x y
      _ ≤ (L : ℝ) * ‖x - y‖ := HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y

/-- Helper for Text 4 2 23: the canonical degree-three constant controls the second iterated
derivative exactly. -/
lemma iteratedFDerivTwo_norm_sub_le_canonical
    {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f] (x y : E) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ (L[3](f) : ℝ) * ‖x - y‖ := by
  let S : Set NNReal := {L : NNReal | f ∈ 𝒞^{2,2}_{L}(Set.univ)}
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hdist_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    let r : NNReal := ⟨‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ / ‖x - y‖, by positivity⟩
    have hr : r ≤ L[3](f) := by
      change r ≤ sInf S
      refine le_csInf ?_ ?_
      · rcases (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 f).exists_mem with
          ⟨L, hL⟩
        exact ⟨L, hL⟩
      · intro L hL
        have hL' : f ∈ 𝒞^{2,2}_{L}(Set.univ) := by
          simpa [S] using hL
        have hbound :
            ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ (L : ℝ) * ‖x - y‖ :=
          @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le E _ _ L 3 f hL' x y
        exact_mod_cast (show
            ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ / ‖x - y‖ ≤ (L : ℝ) by
          exact (div_le_iff₀ hdist_pos).2 hbound)
    exact
      (div_le_iff₀ hdist_pos).mp <| by
        simpa [r] using (show (r : ℝ) ≤ (L[3](f) : ℝ) from by exact_mod_cast hr)

/-- Helper for Text 4 2 23: the canonical degree-three owner yields the matching `C22` witness at
the canonical constant. -/
lemma memC22_canonical {f : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 f] :
    HasLipschitzContinuousHessian (L[3](f)) f := by
  have hcontDiffTwo : ContDiff ℝ 2 f := by
    simpa using (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 f).contDiff
  refine ⟨hcontDiffTwo, ?_⟩
  -- Re-express the canonical Taylor-class estimate on the Hessian surface.
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [← ftaylorSeriesCoeffTwo_normSub_eq_sndFDeriv_normSub hcontDiffTwo x y]
  simpa using iteratedFDerivTwo_norm_sub_le_canonical (f := f) x y

/-- Helper for Text 4 2 23: scaling a `C22[L]` witness by a nonnegative scalar scales the
Lipschitz constant by the same factor. -/
lemma memC22_nonneg_smul {L : NNReal} {f : E → ℝ} (c : NNReal)
    (hf : HasLipschitzContinuousHessian L f) :
    HasLipschitzContinuousHessian (c * L) ((c : ℝ) • f) := by
  refine ⟨hf.contDiff.const_smul (c : ℝ), ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Pull the scalar out of the second derivative and scale the source estimate.
  have hbase := HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y
  calc
    ‖fderiv ℝ (fderiv ℝ ((c : ℝ) • f)) x - fderiv ℝ (fderiv ℝ ((c : ℝ) • f)) y‖
        = ‖(c : ℝ) • (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)‖ := by
            simp [fderiv_const_smul_field, smul_sub]
    _ = (c : ℝ) * ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
          simp [norm_smul, Real.norm_of_nonneg c.2]
    _ ≤ (c : ℝ) * ((L : ℝ) * ‖x - y‖) := by
          gcongr
    _ = ((c * L : NNReal) : ℝ) * ‖x - y‖ := by
          rw [show ((c * L : NNReal) : ℝ) = (c : ℝ) * (L : ℝ) by rfl]
          ring

/-- Helper for Text 4 2 23: a zero-cost Hessian-Lipschitz witness stays zero-cost under arbitrary
real scaling. -/
lemma memC22_zero_smul {f : E → ℝ} {c : ℝ}
    (hf : HasLipschitzContinuousHessian (0 : NNReal) f) :
    HasLipschitzContinuousHessian (0 : NNReal) (c • f) :=
by
  refine ⟨hf.contDiff.const_smul c, ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Pull the scalar through the second derivative and collapse the source bound to zero.
  have hbase := HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y
  have hzero :
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ = 0 := by
    have hright :
        ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ 0 := by
      simpa using hbase
    exact le_antisymm hright (norm_nonneg _)
  calc
    ‖fderiv ℝ (fderiv ℝ (c • f)) x - fderiv ℝ (fderiv ℝ (c • f)) y‖
        = |c| * ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
            rw [fderiv_const_smul_field, fderiv_const_smul_field]
            rw [show (c • fderiv ℝ (fderiv ℝ f)) x = c • fderiv ℝ (fderiv ℝ f) x by rfl]
            rw [show (c • fderiv ℝ (fderiv ℝ f)) y = c • fderiv ℝ (fderiv ℝ f) y by rfl]
            have hsmul :
                c • fderiv ℝ (fderiv ℝ f) x - c • fderiv ℝ (fderiv ℝ f) y =
                  c • (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) := by
              rw [smul_sub]
            rw [hsmul, norm_smul, Real.norm_eq_abs]
    _ = 0 := by simp [hzero]
    _ ≤ ((0 : NNReal) : ℝ) * ‖x - y‖ := by simp

/-- Helper for Text 4 2 23: adding `C22` witnesses adds their degree-three constants. -/
lemma memC22_add {L₁ L₂ : NNReal} {f g : E → ℝ}
    (hf : HasLipschitzContinuousHessian L₁ f) (hg : HasLipschitzContinuousHessian L₂ g) :
    HasLipschitzContinuousHessian (L₁ + L₂) (f + g) :=
by
  refine ⟨hf.contDiff.add hg.contDiff, ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Differentiate the summed derivative field pointwise and combine the two source estimates.
  have hfdiff_x : DifferentiableAt ℝ (fun z ↦ fderiv ℝ f z) x := by
    exact (hf.contDiff.contDiffAt (x := x)).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero
  have hfdiff_y : DifferentiableAt ℝ (fun z ↦ fderiv ℝ f z) y := by
    exact (hf.contDiff.contDiffAt (x := y)).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero
  have hgdiff_x : DifferentiableAt ℝ (fun z ↦ fderiv ℝ g z) x := by
    exact (hg.contDiff.contDiffAt (x := x)).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero
  have hgdiff_y : DifferentiableAt ℝ (fun z ↦ fderiv ℝ g z) y := by
    exact (hg.contDiff.contDiffAt (x := y)).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero
  have hdiff_f : ∀ z : E, DifferentiableAt ℝ f z := fun z ↦
    (hf.contDiff.contDiffAt (x := z)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hdiff_g : ∀ z : E, DifferentiableAt ℝ g z := fun z ↦
    (hg.contDiff.contDiffAt (x := z)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hfun :
      (fun z : E ↦ fderiv ℝ (f + g) z) = fun z ↦ fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    rw [fderiv_add (hdiff_f z) (hdiff_g z)]
  have hxadd :
      fderiv ℝ (fun z ↦ fderiv ℝ f z + fderiv ℝ g z) x =
        fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    simpa using (fderiv_add hfdiff_x hgdiff_x)
  have hyadd :
      fderiv ℝ (fun z ↦ fderiv ℝ f z + fderiv ℝ g z) y =
        fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ g) y := by
    simpa using (fderiv_add hfdiff_y hgdiff_y)
  have hfbound := HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y
  have hgbound := HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hg x y
  calc
    ‖fderiv ℝ (fderiv ℝ (f + g)) x - fderiv ℝ (fderiv ℝ (f + g)) y‖
        = ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) +
            (fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y)‖ := by
            rw [show fderiv ℝ (fderiv ℝ (f + g)) x =
                fderiv ℝ (fun z ↦ fderiv ℝ f z + fderiv ℝ g z) x by simpa [hfun]]
            rw [show fderiv ℝ (fderiv ℝ (f + g)) y =
                fderiv ℝ (fun z ↦ fderiv ℝ f z + fderiv ℝ g z) y by simpa [hfun]]
            rw [hxadd, hyadd]
            abel_nf
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ +
          ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ := norm_add_le _ _
    _ ≤ (L₁ : ℝ) * ‖x - y‖ + (L₂ : ℝ) * ‖x - y‖ := add_le_add hfbound hgbound
    _ = ((L₁ + L₂ : NNReal) : ℝ) * ‖x - y‖ := by
          rw [show ((L₁ + L₂ : NNReal) : ℝ) = (L₁ : ℝ) + (L₂ : ℝ) by rfl]
          ring

/-- Helper for Text 4 2 23: the quadratic power-distance at the origin has derivative
`innerSL ℝ x`. -/
lemma powerDistance_two_fderiv_zero_eq (x : E) :
    fderiv ℝ (powerDistance (2 : ℝ) (0 : E)) x = innerSL ℝ x :=
by
  -- Port the quadratic derivative computation from `Text_4_2_7` with the center specialized to `0`.
  have hsub : HasFDerivAt (fun y : E ↦ y - (0 : E)) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const (0 : E)
  have hpowShift : ((2 : ℝ) - 2) = 0 := by norm_num
  have hsq :
      HasFDerivAt (fun y : E ↦ ‖y - (0 : E)‖ ^ (2 : ℝ))
        ((2 : ℝ) • innerSL ℝ (x - (0 : E))) x := by
    simpa [hpowShift] using
      (hasFDerivAt_norm_rpow (x - (0 : E)) (by norm_num : (1 : ℝ) < 2)).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (2 : ℝ)) * ‖y - (0 : E)‖ ^ (2 : ℝ))
        ((1 / (2 : ℝ)) • ((2 : ℝ) • innerSL ℝ (x - (0 : E)))) x := by
    simpa using hsq.const_mul (1 / (2 : ℝ))
  have hfun :
      powerDistance (2 : ℝ) (0 : E) =
        fun y : E ↦ ‖y - (0 : E)‖ ^ (2 : ℝ) * (1 / (2 : ℝ)) := by
    funext y
    rw [powerDistance_apply, mul_comm]
  simpa [hfun, sub_zero, one_div, Real.rpow_natCast, smul_smul, mul_comm, mul_left_comm,
    mul_assoc] using hscaled.fderiv

/-- Helper for Text 4 2 23: the second derivative of the quadratic power-distance at the origin is
constant. -/
lemma powerDistance_two_sndFDeriv_zero_eq (x : E) :
    fderiv ℝ (fderiv ℝ (powerDistance (2 : ℝ) (0 : E))) x =
      ((innerSL ℝ) : E →L[ℝ] E →L[ℝ] ℝ) :=
by
  -- Rewrite the derivative field to the linear map `x ↦ innerSL ℝ x`, then differentiate it.
  have hlin :
      HasFDerivAt
        (fun y : E ↦ ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y))
        ((innerSL ℝ) : E →L[ℝ] E →L[ℝ] ℝ) x :=
    ((innerSL ℝ) : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt
  have hderiv :
      HasFDerivAt (fun y : E ↦ fderiv ℝ (powerDistance (2 : ℝ) (0 : E)) y)
        ((innerSL ℝ) : E →L[ℝ] E →L[ℝ] ℝ) x := by
    simpa [powerDistance_two_fderiv_zero_eq] using hlin
  exact hderiv.fderiv

/-- Helper for Text 4 2 23: the centered quadratic power-distance contributes zero degree-three
Lipschitz cost. -/
lemma powerDistanceTwoZero_memC22_zero :
    HasLipschitzContinuousHessian (0 : NNReal) (powerDistance (2 : ℝ) (0 : E)) :=
by
  refine ⟨?_, ?_⟩
  · -- Identify the quadratic owner with `(1 / 2) • ‖x‖²`, which is `C²` on the whole space.
    have hsub : ContDiff ℝ 2 (fun y : E ↦ y - (0 : E)) := contDiff_id.sub contDiff_const
    have hfun :
        powerDistance (2 : ℝ) (0 : E) = fun y : E ↦ (1 / (2 : ℝ)) * ‖y‖ ^ (2 : ℕ) := by
      funext y
      simp [powerDistance_apply, sub_zero, Real.rpow_natCast]
    simpa [hfun] using ((contDiff_norm_sq ℝ).comp hsub).const_smul (1 / (2 : ℝ))
  · -- The second-derivative field is constant, so its Lipschitz constant is exactly zero.
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    -- Route correction: use the constant second-derivative formula directly instead of relying on
    -- implicit typeclass inference for a constant `LipschitzWith` owner.
    rw [powerDistance_two_sndFDeriv_zero_eq, powerDistance_two_sndFDeriv_zero_eq, sub_self]
    simp

/-- Helper for Text 4 2 23: every admissible degree-two witness for `ξ_{α,β}` is at most `α`. -/
lemma xi_alpha_beta_degreeTwo_uniformWitness_le_alpha
    (α β : NNRealˣ) {σ : ℝ} (hσ_pos : 0 < σ)
    (huniform :
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (2 : ℝ))
        (xi_alpha_beta E α β)) :
    σ ≤ (α : ℝ) :=
by
  rcases exists_unit_vector (E := E) with ⟨u, hu⟩
  have hα_pos : 0 < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hβ_pos : 0 < (β : ℝ) := by
    exact_mod_cast (show 0 < (β : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero β))
  by_contra hσα
  have hσα' : (α : ℝ) < σ := lt_of_not_ge hσα
  let t : ℝ := 3 * (σ - (α : ℝ)) / (4 * (β : ℝ))
  have ht_pos : 0 < t := by
    -- Choose a small positive radius so the cubic term cannot support a witness above `α`.
    dsimp [t]
    have hden_pos : 0 < 4 * (β : ℝ) := by nlinarith
    exact div_pos (by nlinarith) hden_pos
  have ht : 0 ≤ t := le_of_lt ht_pos
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have hmid :=
    huniform.2
      (by simp : -(t • u) ∈ (Set.univ : Set E))
      (by simp : t • u ∈ (Set.univ : Set E))
      hhalf_nonneg
      hhalf_nonneg
      hhalf_sum
  have hmidpoint : (1 / 2 : ℝ) • (-(t • u)) + (1 / 2 : ℝ) • (t • u) = (0 : E) := by
    -- The antipodal pair has midpoint at the origin.
    simp [smul_smul]
  have hnorm : ‖-(t • u) - t • u‖ = 2 * t := by
    -- The antipodal distance is exactly `2t` along the unit direction.
    have h2t_nonneg : 0 ≤ 2 * t := by nlinarith
    calc
      ‖-(t • u) - t • u‖ = ‖-((t • u) + (t • u))‖ := by abel_nf
      _ = ‖(t • u) + (t • u)‖ := norm_neg _
      _ = ‖(2 : ℝ) • (t • u)‖ := by rw [two_smul]
      _ = ‖(2 * t) • u‖ := by rw [smul_smul]
      _ = |2 * t| * ‖u‖ := norm_smul _ _
      _ = 2 * t := by simpa [hu, abs_of_nonneg h2t_nonneg]
  have hleft :
      xi_alpha_beta E α β (-(t • u)) =
        (α : ℝ) * t ^ (2 : ℕ) / 2 + (β : ℝ) * t ^ (3 : ℕ) / 3 := by
    -- The source function depends only on the norm, so the two antipodal values agree.
    simpa using
      (xi_alpha_beta_apply_smul_unit (E := E) α β (u := -u) (by simpa using hu) ht)
  have hright :
      xi_alpha_beta E α β (t • u) =
        (α : ℝ) * t ^ (2 : ℕ) / 2 + (β : ℝ) * t ^ (3 : ℕ) / 3 := by
    -- Evaluate the positive antipodal point through the polynomial formula.
    simpa using xi_alpha_beta_apply_smul_unit (E := E) α β (u := u) hu ht
  have hmod :
      uniformConvexPowerModulus σ (2 : ℝ) ‖-(t • u) - t • u‖ = 2 * σ * t ^ (2 : ℕ) := by
    -- On the antipodal pair, the degree-two modulus collapses to `2σ t²`.
    have hrpow : (2 * t).rpow (2 : ℝ) = 4 * t ^ (2 : ℕ) := by
      calc
        (2 * t).rpow (2 : ℝ) = (2 * t) ^ (2 : ℕ) := by
          simpa using (Real.rpow_natCast (2 * t) 2)
        _ = 4 * t ^ (2 : ℕ) := by ring
    rw [uniformConvexPowerModulus, hnorm, hrpow]
    ring
  have hineq := hmid
  rw [hmidpoint, xi_alpha_beta_zero, hleft, hright, hmod] at hineq
  ring_nf at hineq
  dsimp [t] at hineq
  field_simp [hβ_pos.ne'] at hineq
  have hineq' :
      0 ≤ 3 ^ 2 * (σ - (α : ℝ)) ^ 2 * (4 * ((α : ℝ) + -σ) + (σ - (α : ℝ)) * 2) := by
    simpa using hineq
  have hineq'' := hineq'
  ring_nf at hineq''
  have hsa_pos : 0 < σ - (α : ℝ) := sub_pos.mpr hσα'
  have hneg :
      -(σ * (α : ℝ) ^ 2 * 54) + σ ^ 2 * (α : ℝ) * 54 - σ ^ 3 * 18 + (α : ℝ) ^ 3 * 18 < 0 := by
    have hp : 0 < (σ - (α : ℝ)) ^ (3 : ℕ) := pow_pos hsa_pos 3
    nlinarith
  exact (not_le_of_gt hneg) hineq''

/-- Helper for Text 4 2 23: every admissible degree-three witness for `ξ_{α,β}` is at most
`β / 2`. -/
lemma xi_alpha_beta_degreeThree_uniformWitness_le_halfBeta
    (α β : NNRealˣ) {σ : ℝ} (hσ_pos : 0 < σ)
    (huniform :
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (3 : ℝ))
        (xi_alpha_beta E α β)) :
    σ ≤ (β : ℝ) / 2 :=
by
  rcases exists_unit_vector (E := E) with ⟨u, hu⟩
  have hα_pos : 0 < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  by_contra hσβ
  have hσβ' : (β : ℝ) / 2 < σ := lt_of_not_ge hσβ
  have hdenom_pos : 0 < 2 * σ - (β : ℝ) := by
    nlinarith
  let t : ℝ := 3 * (α : ℝ) / (2 * σ - (β : ℝ))
  have ht_pos : 0 < t := by
    -- Choose a large positive radius so the cubic term dominates the quadratic perturbation.
    dsimp [t]
    exact div_pos (by nlinarith) hdenom_pos
  have ht : 0 ≤ t := le_of_lt ht_pos
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have hmid :=
    huniform.2
      (by simp : -(t • u) ∈ (Set.univ : Set E))
      (by simp : t • u ∈ (Set.univ : Set E))
      hhalf_nonneg
      hhalf_nonneg
      hhalf_sum
  have hmidpoint : (1 / 2 : ℝ) • (-(t • u)) + (1 / 2 : ℝ) • (t • u) = (0 : E) := by
    -- The same antipodal pair still has midpoint at the origin.
    simp [smul_smul]
  have hnorm : ‖-(t • u) - t • u‖ = 2 * t := by
    -- The distance between the antipodes is again `2t`.
    have h2t_nonneg : 0 ≤ 2 * t := by nlinarith
    calc
      ‖-(t • u) - t • u‖ = ‖-((t • u) + (t • u))‖ := by abel_nf
      _ = ‖(t • u) + (t • u)‖ := norm_neg _
      _ = ‖(2 : ℝ) • (t • u)‖ := by rw [two_smul]
      _ = ‖(2 * t) • u‖ := by rw [smul_smul]
      _ = |2 * t| * ‖u‖ := norm_smul _ _
      _ = 2 * t := by simpa [hu, abs_of_nonneg h2t_nonneg]
  have hleft :
      xi_alpha_beta E α β (-(t • u)) =
        (α : ℝ) * t ^ (2 : ℕ) / 2 + (β : ℝ) * t ^ (3 : ℕ) / 3 := by
    -- The antipodal value matches the same quadratic-plus-cubic polynomial.
    simpa using
      (xi_alpha_beta_apply_smul_unit (E := E) α β (u := -u) (by simpa using hu) ht)
  have hright :
      xi_alpha_beta E α β (t • u) =
        (α : ℝ) * t ^ (2 : ℕ) / 2 + (β : ℝ) * t ^ (3 : ℕ) / 3 := by
    -- Evaluate the positive antipodal point through the same owner formula.
    simpa using xi_alpha_beta_apply_smul_unit (E := E) α β (u := u) hu ht
  have hmod :
      uniformConvexPowerModulus σ (3 : ℝ) ‖-(t • u) - t • u‖ =
        (8 / 3 : ℝ) * σ * t ^ (3 : ℕ) := by
    -- On the antipodal pair, the degree-three modulus becomes `(8/3)σ t³`.
    have hrpow : (2 * t).rpow (3 : ℝ) = 8 * t ^ (3 : ℕ) := by
      calc
        (2 * t).rpow (3 : ℝ) = (2 * t) ^ (3 : ℕ) := by
          simpa using (Real.rpow_natCast (2 * t) 3)
        _ = 8 * t ^ (3 : ℕ) := by ring
    rw [uniformConvexPowerModulus, hnorm, hrpow]
    ring
  have hineq := hmid
  rw [hmidpoint, xi_alpha_beta_zero, hleft, hright, hmod] at hineq
  ring_nf at hineq
  dsimp [t] at hineq
  field_simp [hdenom_pos.ne'] at hineq
  have hineq' :
      0 ≤ (α : ℝ) ^ 3 * 3 ^ 2 * (2 * σ - (β : ℝ) + 2 * (β : ℝ) + -(2 ^ 2 * σ)) := by
    simpa using hineq
  have hineq'' := hineq'
  ring_nf at hineq''
  have hαcube_pos : 0 < (α : ℝ) ^ (3 : ℕ) := by positivity
  have hneg : -(α : ℝ) ^ 3 * σ * 18 + (α : ℝ) ^ 3 * (β : ℝ) * 9 < 0 := by
    nlinarith [hαcube_pos, hσβ']
  have hineq''' : 0 ≤ -(α : ℝ) ^ 3 * σ * 18 + (α : ℝ) ^ 3 * (β : ℝ) * 9 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hineq''
  exact (not_le_of_gt hneg) hineq'''

instance xi_alpha_beta_degreeTwo_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 2 (xi_alpha_beta E α β) :=
by
  refine ⟨?_, ?_⟩
  · have hhalf_lt : (1 / 2 : ℝ) < σ[2](powerDistance (2 : ℝ) (0 : E)) := by
      -- Use a strict sub-witness of the exact quadratic parameter `σ₂ = 1`.
      rw [powerDistance_two_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hquad :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus ((α : ℝ) / 2) (2 : ℝ))
          ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
      -- Scale the quadratic `1/2`-witness by the positive coefficient `α`.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 2 : ℝ) (2 : ℝ))
            (powerDistance (2 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 2)
          (f := powerDistance (2 : ℝ) (0 : E)) (by norm_num) (by positivity) hhalf_lt
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        uniformConvexOn_nonneg_smul (c := (α : ℝ)) (σ := (1 / 2 : ℝ)) (p := (2 : ℝ))
          (by positivity) hbase
    have hquarter_lt : (1 / 4 : ℝ) < σ[3](powerDistance (3 : ℝ) (0 : E)) := by
      -- Any positive sub-witness of the cubic parameter suffices to recover convexity.
      rw [powerDistance_three_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hcubic_convex : ConvexOn ℝ Set.univ ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
      -- Route correction: obtain convexity from a small cubic uniform-convexity witness instead
      -- of searching for a separate norm-power convexity API.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 4 : ℝ) (3 : ℝ))
            (powerDistance (3 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 3)
          (f := powerDistance (3 : ℝ) (0 : E)) (by norm_num) (by positivity) hquarter_lt
      have hscaled :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus ((β : ℝ) / 4) (3 : ℝ))
            ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          uniformConvexOn_nonneg_smul (c := (β : ℝ)) (σ := (1 / 4 : ℝ)) (p := (3 : ℝ))
            (by positivity) hbase
      exact uniformConvexOn_convexOn_of_nonneg hscaled fun r hr ↦
        uniformConvexPowerModulus_nonneg (by positivity) (by positivity) hr
    have hα_pos : 0 < (α : ℝ) := by
      exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
    refine ⟨(α : ℝ) / 2, by nlinarith, ?_⟩
    -- Add the convex cubic perturbation as a zero-modulus witness.
    simpa [xi_alpha_beta] using hquad.add hcubic_convex.uniformConvexOn_zero
  · refine ⟨(α : ℝ), ?_⟩
    intro σ hσ
    exact xi_alpha_beta_degreeTwo_uniformWitness_le_alpha (E := E) α β hσ.1 hσ.2


instance xi_alpha_beta_degreeThree_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 3 (xi_alpha_beta E α β) :=
by
  refine ⟨?_, ?_⟩
  · have hquarter_lt : (1 / 4 : ℝ) < σ[3](powerDistance (3 : ℝ) (0 : E)) := by
      -- Use a strict sub-witness of the exact cubic parameter `σ₃ = 1 / 2`.
      rw [powerDistance_three_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hcubic :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus ((β : ℝ) / 4) (3 : ℝ))
          ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
      -- Scale the cubic `1/4`-witness by the positive coefficient `β`.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 4 : ℝ) (3 : ℝ))
            (powerDistance (3 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 3)
          (f := powerDistance (3 : ℝ) (0 : E)) (by norm_num) (by positivity) hquarter_lt
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        uniformConvexOn_nonneg_smul (c := (β : ℝ)) (σ := (1 / 4 : ℝ)) (p := (3 : ℝ))
          (by positivity) hbase
    have hhalf_lt : (1 / 2 : ℝ) < σ[2](powerDistance (2 : ℝ) (0 : E)) := by
      -- Any positive sub-witness of the quadratic parameter suffices to recover convexity.
      rw [powerDistance_two_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hquad_convex : ConvexOn ℝ Set.univ ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
      -- Obtain convexity of the scaled quadratic term from a small degree-two witness.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 2 : ℝ) (2 : ℝ))
            (powerDistance (2 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 2)
          (f := powerDistance (2 : ℝ) (0 : E)) (by norm_num) (by positivity) hhalf_lt
      have hscaled :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus ((α : ℝ) / 2) (2 : ℝ))
            ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          uniformConvexOn_nonneg_smul (c := (α : ℝ)) (σ := (1 / 2 : ℝ)) (p := (2 : ℝ))
            (by positivity) hbase
      exact uniformConvexOn_convexOn_of_nonneg hscaled fun r hr ↦
        uniformConvexPowerModulus_nonneg (by positivity) (by positivity) hr
    have hβ_pos : 0 < (β : ℝ) := by
      exact_mod_cast (show 0 < (β : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero β))
    refine ⟨(β : ℝ) / 4, by nlinarith, ?_⟩
    -- Add the convex quadratic perturbation as a zero-modulus witness.
    simpa [xi_alpha_beta, add_comm] using hquad_convex.uniformConvexOn_zero.add hcubic
  · refine ⟨(β : ℝ) / 2, ?_⟩
    intro σ hσ
    exact xi_alpha_beta_degreeThree_uniformWitness_le_halfBeta (E := E) α β hσ.1 hσ.2


instance xi_alpha_beta_degreeThree_lipschitz (α β : NNRealˣ) :
    HasIteratedFDerivLipschitzConstantOfDegree 3 (xi_alpha_beta E α β) :=
by
  -- Combine the zero-cost quadratic witness with the scaled cubic `C22[2]` witness.
  have hquad :
      HasLipschitzContinuousHessian (0 : NNReal)
        ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) :=
    memC22_zero_smul (c := (α : ℝ)) powerDistanceTwoZero_memC22_zero
  have hcubic :
      HasLipschitzContinuousHessian ((β : NNReal) * 2)
        ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) :=
    memC22_nonneg_smul (c := (β : NNReal)) powerDistance_three_zero_mem_C22
  have hsum :
      HasLipschitzContinuousHessian (2 * (β : NNReal)) (xi_alpha_beta E α β) := by
    simpa [xi_alpha_beta, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using memC22_add hquad hcubic
  exact HasIteratedFDerivLipschitzConstantOfDegree.of_constant
    (mem_taylorCoeffLipschitzClass_of_memC22 hsum)

instance xi_alpha_beta_memFunctionClassF23 (α β : NNRealˣ) :
    IsInFunctionClassF23 (xi_alpha_beta E α β) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A component of Text 4 2 23: the degree-two conditioning parameter of `ξ_{α,β}` is exactly
`α`. -/
theorem xi_alpha_beta_sigma_two (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) :=
by
  have hα_pos : 0 < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hlower : (α : ℝ) ≤ σ[2](xi_alpha_beta E α β) := by
    by_contra hlt
    have hlt' : σ[2](xi_alpha_beta E α β) < (α : ℝ) := lt_of_not_ge hlt
    let τ : ℝ := (σ[2](xi_alpha_beta E α β) + (α : ℝ)) / 2
    have hτ_pos : 0 < τ := by
      -- Pick a midpoint parameter still strictly below `α` but above the current canonical `σ₂`.
      have hσ_pos :
          0 < σ[2](xi_alpha_beta E α β) :=
        HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos
          (p := 2) (f := xi_alpha_beta E α β)
      dsimp [τ]
      nlinarith
    have hτ_lt_alpha : τ < (α : ℝ) := by
      dsimp [τ]
      nlinarith
    have hbase_lt : τ / (α : ℝ) < σ[2](powerDistance (2 : ℝ) (0 : E)) := by
      -- The quadratic owner admits every positive sub-witness of `1`.
      rw [powerDistance_two_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      have hτ_lt_alpha' : τ < 1 * (α : ℝ) := by simpa using hτ_lt_alpha
      exact (div_lt_iff₀ hα_pos).2 hτ_lt_alpha'
    have hquad :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus τ (2 : ℝ))
          ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
      -- Scale the imported quadratic sub-witness so its parameter becomes exactly `τ`.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (τ / (α : ℝ)) (2 : ℝ))
            (powerDistance (2 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 2)
          (f := powerDistance (2 : ℝ) (0 : E)) (by norm_num) (by positivity) hbase_lt
      simpa [τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        uniformConvexOn_nonneg_smul (c := (α : ℝ)) (σ := τ / (α : ℝ)) (p := (2 : ℝ))
          (by positivity) hbase
    have hquarter_lt : (1 / 4 : ℝ) < σ[3](powerDistance (3 : ℝ) (0 : E)) := by
      -- A small cubic witness is enough to recover convexity of the perturbation.
      rw [powerDistance_three_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hcubic_convex : ConvexOn ℝ Set.univ ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
      -- Route correction: obtain convexity from a small degree-three witness, then forget the modulus.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 4 : ℝ) (3 : ℝ))
            (powerDistance (3 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 3)
          (f := powerDistance (3 : ℝ) (0 : E)) (by norm_num) (by positivity) hquarter_lt
      have hscaled :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus ((β : ℝ) / 4) (3 : ℝ))
            ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          uniformConvexOn_nonneg_smul (c := (β : ℝ)) (σ := (1 / 4 : ℝ)) (p := (3 : ℝ))
            (by positivity) hbase
      exact uniformConvexOn_convexOn_of_nonneg hscaled fun r hr ↦
        uniformConvexPowerModulus_nonneg (by positivity) (by positivity) hr
    have hτ_witness :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus τ (2 : ℝ))
          (xi_alpha_beta E α β) := by
      -- Add the convex cubic perturbation to the near-sharp quadratic witness.
      simpa [xi_alpha_beta] using hquad.add hcubic_convex.uniformConvexOn_zero
    have hτ_le :
        τ ≤ σ[2](xi_alpha_beta E α β) :=
      HasUniformConvexityParameterOfDegree.le_uniformConvexityParameterOfDegree hτ_pos hτ_witness
    have hσ_lt_τ : σ[2](xi_alpha_beta E α β) < τ := by
      dsimp [τ]
      nlinarith
    exact (not_le_of_gt hσ_lt_τ) hτ_le
  have hupper : σ[2](xi_alpha_beta E α β) ≤ (α : ℝ) := by
    let S : Set ℝ := {σ : ℝ |
      0 < σ ∧
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus σ (2 : ℝ))
          (xi_alpha_beta E α β)}
    change sSup S ≤ (α : ℝ)
    have hnonempty : Set.Nonempty S :=
      HasUniformConvexityParameterOfDegree.nonempty (p := 2) (f := xi_alpha_beta E α β)
    refine csSup_le hnonempty ?_
    intro σ hσ
    exact xi_alpha_beta_degreeTwo_uniformWitness_le_alpha (E := E) α β hσ.1 hσ.2
  exact le_antisymm hupper hlower

/-- A component of Text 4 2 23: the degree-three conditioning parameter of `ξ_{α,β}` is exactly
`β / 2`. -/
theorem xi_alpha_beta_sigma_three (α β : NNRealˣ) :
    σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 :=
by
  have hβ_pos : 0 < (β : ℝ) := by
    exact_mod_cast (show 0 < (β : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero β))
  have hlower : (β : ℝ) / 2 ≤ σ[3](xi_alpha_beta E α β) := by
    by_contra hlt
    have hlt' : σ[3](xi_alpha_beta E α β) < (β : ℝ) / 2 := lt_of_not_ge hlt
    let τ : ℝ := (σ[3](xi_alpha_beta E α β) + (β : ℝ) / 2) / 2
    have hτ_pos : 0 < τ := by
      -- Pick a midpoint parameter still strictly below `β / 2` but above the canonical `σ₃`.
      have hσ_pos :
          0 < σ[3](xi_alpha_beta E α β) :=
        HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos
          (p := 3) (f := xi_alpha_beta E α β)
      dsimp [τ]
      nlinarith
    have hτ_lt_halfBeta : τ < (β : ℝ) / 2 := by
      dsimp [τ]
      nlinarith
    have hbase_lt : τ / (β : ℝ) < σ[3](powerDistance (3 : ℝ) (0 : E)) := by
      -- The cubic owner admits every positive sub-witness of `1 / 2`.
      rw [powerDistance_three_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      have hτ_lt_halfBeta' : τ < (1 / 2 : ℝ) * (β : ℝ) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hτ_lt_halfBeta
      exact (div_lt_iff₀ hβ_pos).2 hτ_lt_halfBeta'
    have hcubic :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus τ (3 : ℝ))
          ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
      -- Scale the imported cubic sub-witness so its parameter becomes exactly `τ`.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (τ / (β : ℝ)) (3 : ℝ))
            (powerDistance (3 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 3)
          (f := powerDistance (3 : ℝ) (0 : E)) (by norm_num) (by positivity) hbase_lt
      simpa [τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        uniformConvexOn_nonneg_smul (c := (β : ℝ)) (σ := τ / (β : ℝ)) (p := (3 : ℝ))
          (by positivity) hbase
    have hhalf_lt : (1 / 2 : ℝ) < σ[2](powerDistance (2 : ℝ) (0 : E)) := by
      -- A small quadratic witness is enough to recover convexity of the perturbation.
      rw [powerDistance_two_uniformConvexityParameter (E := E) (x0 := (0 : E))]
      norm_num
    have hquad_convex : ConvexOn ℝ Set.univ ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
      -- Obtain convexity of the quadratic term from a small degree-two witness.
      have hbase :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus (1 / 2 : ℝ) (2 : ℝ))
            (powerDistance (2 : ℝ) (0 : E)) :=
        uniformConvexOn_of_lt_uniformConvexityParameter (E := E) (p := 2)
          (f := powerDistance (2 : ℝ) (0 : E)) (by norm_num) (by positivity) hhalf_lt
      have hscaled :
          UniformConvexOn Set.univ
            (uniformConvexPowerModulus ((α : ℝ) / 2) (2 : ℝ))
            ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          uniformConvexOn_nonneg_smul (c := (α : ℝ)) (σ := (1 / 2 : ℝ)) (p := (2 : ℝ))
            (by positivity) hbase
      exact uniformConvexOn_convexOn_of_nonneg hscaled fun r hr ↦
        uniformConvexPowerModulus_nonneg (by positivity) (by positivity) hr
    have hτ_witness :
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus τ (3 : ℝ))
          (xi_alpha_beta E α β) := by
      -- Add the convex quadratic perturbation to the near-sharp cubic witness.
      simpa [xi_alpha_beta, add_comm] using hquad_convex.uniformConvexOn_zero.add hcubic
    have hτ_le :
        τ ≤ σ[3](xi_alpha_beta E α β) :=
      HasUniformConvexityParameterOfDegree.le_uniformConvexityParameterOfDegree hτ_pos hτ_witness
    have hσ_lt_τ : σ[3](xi_alpha_beta E α β) < τ := by
      dsimp [τ]
      nlinarith
    exact (not_le_of_gt hσ_lt_τ) hτ_le
  have hupper : σ[3](xi_alpha_beta E α β) ≤ (β : ℝ) / 2 := by
    let S : Set ℝ := {σ : ℝ |
      0 < σ ∧
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus σ (3 : ℝ))
          (xi_alpha_beta E α β)}
    change sSup S ≤ (β : ℝ) / 2
    have hnonempty : Set.Nonempty S :=
      HasUniformConvexityParameterOfDegree.nonempty (p := 3) (f := xi_alpha_beta E α β)
    refine csSup_le hnonempty ?_
    intro σ hσ
    exact xi_alpha_beta_degreeThree_uniformWitness_le_halfBeta (E := E) α β hσ.1 hσ.2
  exact le_antisymm hupper hlower

/-- A component of Text 4 2 23: the degree-three Lipschitz constant of `ξ_{α,β}` is exactly
`2β`. -/
theorem xi_alpha_beta_L_three (α β : NNRealˣ) :
    L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) :=
by
  have hquad :
      HasLipschitzContinuousHessian (0 : NNReal)
        ((α : ℝ) • powerDistance (2 : ℝ) (0 : E)) := by
    -- The quadratic term contributes no degree-three cost.
    exact memC22_zero_smul (c := (α : ℝ)) powerDistanceTwoZero_memC22_zero
  have hcubic :
      HasLipschitzContinuousHessian ((β : NNReal) * 2)
        ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
    -- The cubic owner scales its exact `C22[2]` witness by `β`.
    exact memC22_nonneg_smul (c := (β : NNReal)) powerDistance_three_zero_mem_C22
  have hsum :
      HasLipschitzContinuousHessian (2 * (β : NNReal)) (xi_alpha_beta E α β) := by
    -- Assemble the explicit mixed `C22[2β]` witness.
    simpa [xi_alpha_beta, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using memC22_add hquad hcubic
  have hupper : L[3](xi_alpha_beta E α β) ≤ 2 * (β : NNReal) := by
    let S : Set NNReal := {L : NNReal | xi_alpha_beta E α β ∈ 𝒞^{2,2}_{L}(Set.univ)}
    change sInf S ≤ 2 * (β : NNReal)
    -- The explicit `C22[2β]` witness is one candidate in the defining infimum set.
    refine csInf_le ?_ ?_
    · exact ⟨0, by intro L hL; exact zero_le L⟩
    · simpa [S] using mem_taylorCoeffLipschitzClass_of_memC22 hsum
  have hcubic_from_canonical :
      HasLipschitzContinuousHessian (L[3](xi_alpha_beta E α β))
        ((β : ℝ) • powerDistance (3 : ℝ) (0 : E)) := by
    -- Cancel the zero-cost quadratic summand from the canonical `C22[L₃]` witness of `ξ_{α,β}`.
    have hcanonical :
        HasLipschitzContinuousHessian (L[3](xi_alpha_beta E α β))
          (xi_alpha_beta E α β) :=
      memC22_canonical (f := xi_alpha_beta E α β)
    have hnegQuad :
        HasLipschitzContinuousHessian (0 : NNReal)
          ((-(α : ℝ)) • powerDistance (2 : ℝ) (0 : E)) := by
      exact memC22_zero_smul (c := (-(α : ℝ))) powerDistanceTwoZero_memC22_zero
    simpa [xi_alpha_beta, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_comm,
      mul_left_comm, mul_assoc] using memC22_add hcanonical hnegQuad
  have hscaled_cubic :
      HasLipschitzContinuousHessian
        (((↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β)))
        (powerDistance (3 : ℝ) (0 : E)) := by
    -- Scale back by `β⁻¹` so the comparison lands on the canonical cubic owner.
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using
      memC22_nonneg_smul (c := (↑(β⁻¹) : NNReal)) hcubic_from_canonical
  have hlower_scaled :
      (2 : NNReal) ≤ (↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β) := by
    let S : Set NNReal := {L : NNReal | powerDistance (3 : ℝ) (0 : E) ∈ 𝒞^{2,2}_{L}(Set.univ)}
    have hwitness :
        powerDistance (3 : ℝ) (0 : E) ∈
          𝒞^{2,2}_{(↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β)}(Set.univ) :=
      mem_taylorCoeffLipschitzClass_of_memC22 hscaled_cubic
    have hupper_cubic : L[3](powerDistance (3 : ℝ) (0 : E)) ≤
        (↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β) := by
      change sInf S ≤ (↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β)
      refine csInf_le ?_ ?_
      · exact ⟨0, by intro L hL; exact zero_le L⟩
      · simpa [S] using hwitness
    rw [powerDistance_three_lipschitzConstant (E := E) (x0 := (0 : E))] at hupper_cubic
    exact hupper_cubic
  have hlower : 2 * (β : NNReal) ≤ L[3](xi_alpha_beta E α β) := by
    -- Multiply the scaled comparison by `β` and simplify `β * β⁻¹ = 1`.
    have hmul :
        (β : NNReal) * 2 ≤
          (β : NNReal) * ((↑(β⁻¹) : NNReal) * L[3](xi_alpha_beta E α β)) := by
      exact mul_le_mul_left' hlower_scaled (β : NNReal)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact le_antisymm hupper hlower

/-- A component of Text 4 2 23: the exact conditioning identities imply `ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_mem_F23 (α β : NNRealˣ) :
    xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  let _ : Nontrivial E := inferInstance
  infer_instance

/-- Text 4 2 23: the source-facing function `ξ_{α,β}` has the exact conditioning data
`σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`, and `L₃(ξ_{α,β}) = 2β`; in particular,
`ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_conditioning (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) ∧
      σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 ∧
      L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) ∧
      xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  exact ⟨xi_alpha_beta_sigma_two α β, xi_alpha_beta_sigma_three α β, xi_alpha_beta_L_three α β,
    xi_alpha_beta_mem_F23 α β⟩

end Conditioning
