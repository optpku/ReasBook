/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_42
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

recall IsProperExtendedRealFunction
recall is_convex_function
recall is_l_smooth_on
recall moreau_envelope
recall prox_eq_singleton_of_proper_closed_convex
recall hasGradientAt_moreau_envelope_toReal_of_scaled_prox_eq_singleton
recall prox_eq_singleton_nonexpansive

local notation:65 f " □r " ω => infimal_convolution f (fun z ↦ (ω z : EReal))

/- Theorem 6.60 splits across the established chapter owners.

- The source-facing owner is the Moreau envelope `M[μ, f]` from Definition 6.7.
- The `core/canonical` smoothness owner is `is_l_smooth_on` from Definition 5.1, together with
  its gradient-Lipschitz characterization on real Hilbert spaces.
- The Chapter 6 derived API used to reach that owner abstraction is:
  `prox_eq_singleton_of_proper_closed_convex` from Theorem 6.3 for existence and uniqueness of
  proximal points on a proper space,
  `hasGradientAt_moreau_envelope_toReal_of_scaled_prox_eq_singleton` from Definition 6.10 for the
  pointwise Moreau-envelope gradient, and
  `prox_eq_singleton_nonexpansive` from Theorem 6.42 for the Lipschitz control of those proximal
  points.

Part (1) is therefore `source-facing`: it should stay on the Moreau-envelope owner surface rather
than reintroduce a finite-dimensional infimal-convolution proof-route wrapper specialized to
`ω(μ)`.
- Part (2) is `bridge/view` only: Definition 6.10 already owns the singleton-valued proximal
  gradient formula for `M[μ, f]`, so this file should reuse that theorem directly rather than keep
  a second public copy under a new local name. -/

-- Proof sketch: for each `x`, use `prox_eq_singleton_of_proper_closed_convex` on the scaled
-- function `((μ : EReal) • f)` to obtain the unique proximal point `u(x)`. Definition 6.10 then
-- identifies the gradient of `y ↦ (M[μ, f] y).toReal` at `x` with `(1 / μ) • (x - u(x))`, and
-- Theorem 6.42 shows that `x ↦ u(x)` is nonexpansive. Hence the gradient field is
-- `(1 / μ)`-Lipschitz on `Set.univ`, so `is_l_smooth_on_iff_lipschitzOnWith_gradient` yields the
-- global smoothness statement at the Chapter 5 owner level.
/-- Helper for Theorem 6.60: the quadratic kernel `x ↦ (1 / (2 * μ)) ‖x‖²` has gradient
`(1 / μ) • x`. -/
lemma moreau_quadratic_kernel_hasGradientAt (μ : PosReal) (x : E) :
    HasGradientAt (fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ)) ((1 / μ : ℝ) • x) x := by
  -- Differentiate the squared norm, then scale by the Moreau quadratic coefficient.
  have hsq : HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ))
        ((1 / (2 * μ : ℝ)) • (2 • innerSL ℝ x)) x :=
    hsq.const_mul (1 / (2 * μ : ℝ))
  -- Re-express the Fréchet derivative through the Riesz map to read off the gradient vector.
  have hfrechet :
      ((1 / (2 * μ : ℝ)) • (2 • innerSL ℝ x)) =
        (InnerProductSpace.toDual ℝ E) ((1 / μ : ℝ) • x) := by
    ext y
    have hμ : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
    simp
    field_simp [hμ]
  rw [hfrechet] at hscaled
  simpa using hscaled.hasGradientAt

/-- Helper for Theorem 6.60: the Moreau quadratic kernel is globally `(1 / μ)`-smooth. -/
lemma moreau_quadratic_kernel_is_inv_mu_smooth (μ : PosReal) :
    is_l_smooth_on (fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ))
      Set.univ (Real.toNNReal (1 / μ)) := by
  rw [is_l_smooth_on_iff_lipschitzOnWith_gradient]
  refine ⟨?_, ?_⟩
  · intro x _
    -- The pointwise gradient formula gives differentiability everywhere.
    exact (moreau_quadratic_kernel_hasGradientAt (E := E) μ x).differentiableAt
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro x _ y _
    -- The gradient field is the linear map `x ↦ (1 / μ) • x`, so its Lipschitz constant is
    -- exactly `1 / μ`.
    have hxgrad :
        ∇ (fun z : E ↦ (1 / (2 * μ : ℝ)) * ‖z‖ ^ (2 : ℕ)) x = (1 / μ : ℝ) • x :=
      (moreau_quadratic_kernel_hasGradientAt (E := E) μ x).gradient
    have hygrad :
        ∇ (fun z : E ↦ (1 / (2 * μ : ℝ)) * ‖z‖ ^ (2 : ℕ)) y = (1 / μ : ℝ) • y :=
      (moreau_quadratic_kernel_hasGradientAt (E := E) μ y).gradient
    rw [hxgrad, hygrad]
    have hμ_nonneg : 0 ≤ (1 / μ : ℝ) := by
      exact le_of_lt (one_div_pos.mpr μ.2)
    calc
      ‖(1 / μ : ℝ) • x - (1 / μ : ℝ) • y‖ = ‖(1 / μ : ℝ) • (x - y)‖ := by
        rw [smul_sub]
      _ = |(1 / μ : ℝ)| * ‖x - y‖ := norm_smul _ _
      _ = max (1 / μ : ℝ) 0 * ‖x - y‖ := by
        rw [abs_of_nonneg hμ_nonneg, max_eq_left hμ_nonneg]
      _ = (↑(Real.toNNReal (1 / μ)) : ℝ) * ‖x - y‖ := by
        rw [Real.coe_toNNReal']
      _ ≤ (↑(Real.toNNReal (1 / μ)) : ℝ) * ‖x - y‖ := le_rfl

/-- Theorem 6.60 (1): if `f` is a proper closed convex extended-real-valued function and `μ > 0`,
then the real-valued Moreau envelope `x ↦ (M[μ, f] x).toReal` is globally `(1 / μ)`-smooth. -/
theorem moreau_envelope_toReal_is_inv_mu_smooth
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (μ : PosReal) :
    is_l_smooth_on (fun x ↦ (M[μ, f] x).toReal) Set.univ (Real.toNNReal (1 / μ)) := by
  let _ := hf_proper
  let _ := hf_closed
  let _ := hf_convex
  let ωμ : E → ℝ := fun x ↦ (1 / (2 * μ : ℝ)) * ‖x‖ ^ (2 : ℕ)
  have hnorm_sq : ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ (2 : ℕ)) :=
    convexOn_univ_norm.pow (fun x _ ↦ norm_nonneg x) 2
  have hcoeff : 0 ≤ 1 / (2 * (μ : ℝ)) := by
    have hμ : 0 < (μ : ℝ) := μ.2
    positivity
  have hω_convex : ConvexOn ℝ Set.univ ωμ := by
    simpa [ωμ] using hnorm_sq.smul hcoeff
  have hω_real : ∀ x, ∃ r : ℝ, (f □r ωμ) x = (r : EReal) := by
    intro x
    change ∃ r : ℝ, (f □ ω(μ)) x = (r : EReal)
    exact moreau_envelope_eq_real_of_proper_convex f μ hf_proper hf_closed hf_convex x
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  -- Route correction: the textbook owner theorem is already exposed as
  -- `infimal_convolution_toReal_is_l_smooth`, so after rewriting `M[μ, f]` as `f □ ω(μ)` it
  -- closes the Chapter 5 smoothness goal directly.
  change is_l_smooth_on (fun x ↦ ((f □ ω(μ)) x).toReal) Set.univ (Real.toNNReal (1 / μ))
  change is_l_smooth_on (fun x ↦ ((f □r ωμ) x).toReal) Set.univ (Real.toNNReal (1 / μ))
  exact
    infimal_convolution_toReal_is_l_smooth
      f ωμ (Real.toNNReal (1 / μ)) hf_proper hf_closed hf_convex hω_convex
      (moreau_quadratic_kernel_is_inv_mu_smooth (E := E) μ) hω_real

/- Theorem 6.60 (2): Definition 6.10 already owns the singleton-valued proximal gradient formula
for the real-valued Moreau envelope, so the canonical owner theorem is reused directly here. -/
recall moreau_envelope_gradient_formula_of_scaled_prox_eq_singleton

end
