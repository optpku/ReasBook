/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_2

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

/- Lemma 12.7 is `source-facing`: it compares the Chapter 12 primal argmax point attached to a
dual iterate with a primal optimizer. Domain sampling points to the Chapter 12 owners
`dual_proximal_gradient_primal_x_argmax`,
`composite_model_objective f (g ∘ A)`, and
`dual_based_proximal_gradient_lagrange_dual_objective_primal`, while the core convex-analysis
ingredients are Chapter 4's `conjugate_function_eq_iff_isMaxOn_pairing_sub_function` and Chapter
5's `lower_quadratic_bound_of_isMinOn_of_strongly_convex`. The natural statement is therefore a
direct gap estimate for an argmax point and a primal minimizer, rather than a new wrapper for
`xBar`, `xStar`, or a local copy of the Chapter 12 dual objective. -/

local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

-- Proof sketch: apply the strong-convexity growth bound from Theorem 5.25 to the shifted function
-- `x ↦ f x - ⟪x, Aᵀ yBar⟫`, whose minimizers are exactly the points in
-- `dual_proximal_gradient_primal_x_argmax f A yBar`. Then compare the resulting Lagrangian value at
-- `(xStar, A xStar)` with the canonical primal-space dual objective value at `yBar`, use strong
-- duality from Theorem 12.2 to identify the primal optimum with the dual optimal value, and
-- rearrange to the displayed dual-gap bound.
/-- Helper for Lemma 12.7: an argmax point of `x ↦ ⟪x, Aᵀ yBar⟫ - f x` attains the conjugate
value `(f∗) (A.adjoint yBar)`. -/
lemma conjugate_primal_eq_pairing_sub_of_mem_primal_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    (f∗) (A.adjoint yBar) =
      (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal) - f xBar) := by
  -- Reinterpret the primal-space argmax condition as the Chapter 4 dual-attainment statement.
  have hmax :
      IsMaxOn
        (fun x : E ↦
          (((InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) x : EReal) - f x))
        Set.univ xBar := by
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff,
      InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hxBar
  -- Theorem 4.11 turns that argmax condition into the exact conjugate equality.
  have hconj :
      (f∗) (A.adjoint yBar) =
        ((((InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) xBar : ℝ) : EReal) - f xBar) := by
    rw [conjugate_function_primal_apply]
    exact
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
        f xBar (InnerProductSpace.toDualMap ℝ E (A.adjoint yBar))).2 hmax
  simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hconj

/-- Helper for Lemma 12.7: negating `a - r` with a finite real term `r` gives `r - a`. -/
lemma ereal_neg_sub_real (a : EReal) (r : ℝ) :
    -(a - (r : EReal)) = ((r : EReal) - a) := by
  -- The real term is finite, so `EReal.neg_sub` applies without mixed infinite cases.
  have hneg : -(a - (r : EReal)) = -a + (r : EReal) := by
    exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- Helper for Lemma 12.7: negating `r - a` with a finite real term `r` gives `a - r`. -/
lemma ereal_neg_real_sub (a : EReal) (r : ℝ) :
    -(((r : EReal)) - a) = a - (r : EReal) := by
  -- The finite left term keeps the negated subtraction in the stable `a - r` normal form.
  rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 12.7: the Chapter 12 primal argmax point is the minimizer of the shifted
objective `x ↦ f x - ⟪x, Aᵀ yBar⟫`. -/
lemma isMinOn_shifted_objective_of_mem_primal_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    IsMinOn
      (fun x : E ↦ f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal)))
      Set.univ xBar := by
  -- Rewrite the argmax objective as the negation of the shifted objective.
  have hmax :
      IsMaxOn
        (fun x : E ↦
          -((f x) - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))))
        Set.univ xBar := by
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff, ereal_neg_sub_real] using hxBar
  -- Negating the max inequality turns it into the desired min inequality.
  rw [isMinOn_univ_iff]
  intro x
  have hle :
      -((f x) - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) ≤
        -((f xBar) - (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal))) :=
    (isMaxOn_univ_iff.mp hmax) x
  simpa using (EReal.neg_le_neg_iff.mp hle)

/-- Helper for Lemma 12.7: every primal minimizer has finite `f`-value, because the qualification
point provides a finite comparison value for the primal objective. -/
lemma primal_minimizer_mem_effective_domain
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    xStar ∈ effective_domain f := by
  obtain ⟨xHat, hxHat, zHat, hzHat, hAz⟩ := h_problem.exists_mem_intrinsicInterior_map_eq
  have hxHat_eff : xHat ∈ effective_domain f := intrinsicInterior_subset hxHat
  have hzHat_eff : zHat ∈ effective_domain g := intrinsicInterior_subset hzHat
  have hle :
      composite_model_objective f (g ∘ A) xStar ≤
        composite_model_objective f (g ∘ A) xHat :=
    (isMinOn_univ_iff.mp hxStar) xHat
  -- The qualification point yields a finite primal value to compare against the minimizer.
  have hcomp_xHat_ne_top :
      composite_model_objective f (g ∘ A) xHat ≠ ⊤ := by
    simpa [Function.comp, hAz] using
      (ne_of_lt (EReal.add_lt_top (ne_of_lt hxHat_eff) (ne_of_lt hzHat_eff)))
  have hcomp_xStar_ne_top :
      composite_model_objective f (g ∘ A) xStar ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hcomp_xHat_ne_top))
  -- If `f xStar = ⊤`, then the whole composite objective is `⊤`, contradicting minimality.
  have hfxStar_ne_top : f xStar ≠ ⊤ := by
    intro hfxStar_top
    have hcomp_top :
        composite_model_objective f (g ∘ A) xStar = ⊤ := by
      rw [composite_model_objective_apply, hfxStar_top]
      simp [h_problem.g_proper.ne_bot (A xStar)]
    exact hcomp_xStar_ne_top hcomp_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfxStar_ne_top)

/-- Helper for Lemma 12.7: subtracting the finite linear term `⟪x, Aᵀ yBar⟫` does not change the
effective domain of `f`. -/
lemma shifted_objective_effective_domain_eq
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V) :
    effective_domain
        (fun x : E ↦ f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) =
      effective_domain f := by
  ext x
  constructor
  · intro hx
    -- A finite subtraction can only be infinite above when `f x` already is.
    change f x < ⊤
    refine lt_top_iff_ne_top.mpr ?_
    intro hfx_top
    have hshift_top :
        f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal)) = ⊤ := by
      rw [hfx_top]
      simp
    exact (ne_of_lt hx) hshift_top
  · intro hx
    -- Adding a finite affine term preserves finiteness from above.
    simpa [sub_eq_add_neg] using
      (EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top (-inner ℝ x (A.adjoint yBar))))

/-- Helper for Lemma 12.7: the shifted objective inherits the strong-convexity gap
`(σ / 2) ‖x - xBar‖² ≤ φ(x) - φ(xBar)` from `f`. -/
lemma shifted_objective_gap_ge_half_sigma_sqdist_of_mem_primal_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (x : E)
    (hx : x ∈ effective_domain f) :
    ((((σ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      (f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) -
        (f xBar - (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal))) := by
  let φ : E → EReal := fun z ↦ f z - (((inner ℝ z (A.adjoint yBar) : ℝ) : EReal))
  -- Route correction: transport strong convexity to the shifted objective first, then invoke the
  -- Chapter 5 quadratic-growth theorem on that stable auxiliary objective.
  have hdomShift : effective_domain φ = effective_domain f := by
    simpa [φ] using shifted_objective_effective_domain_eq
      (f := f) (g := g) (A := A) σ h_problem yBar
  have hne_bot_shift : ∀ z : E, φ z ≠ ⊥ := by
    intro z
    -- The shifted objective is `f z` plus a finite real term, so it still avoids `⊥`.
    simpa [φ, sub_eq_add_neg, EReal.add_ne_bot_iff] using
      (show f z ≠ ⊥ ∧ (((-inner ℝ z (A.adjoint yBar) : ℝ) : EReal) ≠ ⊥) from
        ⟨h_problem.ne_bot z, EReal.coe_ne_bot _⟩)
  have htoRealShift :
      ∀ {z : E}, z ∈ effective_domain φ →
        (φ z).toReal = (f z).toReal - inner ℝ z (A.adjoint yBar) := by
    intro z hz
    have hz_dom : z ∈ effective_domain f := by
      simpa [hdomShift] using hz
    have hz_top : f z ≠ ⊤ := ne_of_lt hz_dom
    have hz_bot : f z ≠ ⊥ := h_problem.ne_bot z
    rw [show φ z = f z + (((-inner ℝ z (A.adjoint yBar) : ℝ) : EReal)) by
      simp [φ, sub_eq_add_neg],
      EReal.toReal_add hz_top hz_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp [EReal.coe_toReal hz_top hz_bot, sub_eq_add_neg]
  have hstrongShift :
      StrongConvexOn (effective_domain φ) (σ : ℝ) (fun z ↦ (φ z).toReal) := by
    refine ⟨?_, ?_⟩
    · simpa [hdomShift] using h_problem.f_strongly_convex.1
    · intro z hz w hw a b ha hb hab
      have hz_dom : z ∈ effective_domain f := by
        simpa [hdomShift] using hz
      have hw_dom : w ∈ effective_domain f := by
        simpa [hdomShift] using hw
      have hzw_dom : a • z + b • w ∈ effective_domain f :=
        h_problem.f_strongly_convex.1 hz_dom hw_dom ha hb hab
      have hzw_shift : a • z + b • w ∈ effective_domain φ := by
        simpa [hdomShift] using hzw_dom
      have hbase := h_problem.f_strongly_convex.2 hz_dom hw_dom ha hb hab
      have hinner :
          inner ℝ (a • z + b • w) (A.adjoint yBar) =
            a * inner ℝ z (A.adjoint yBar) + b * inner ℝ w (A.adjoint yBar) := by
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp
      calc
        (φ (a • z + b • w)).toReal =
            (f (a • z + b • w)).toReal - inner ℝ (a • z + b • w) (A.adjoint yBar) := by
              exact htoRealShift hzw_shift
        _ ≤ a * (f z).toReal + b * (f w).toReal -
            a * b * (((σ : ℝ) / 2) * ‖z - w‖ ^ (2 : ℕ)) -
              inner ℝ (a • z + b • w) (A.adjoint yBar) := by
              exact sub_le_sub_right hbase _
        _ = a * (φ z).toReal + b * (φ w).toReal -
            a * b * (((σ : ℝ) / 2) * ‖z - w‖ ^ (2 : ℕ)) := by
              rw [htoRealShift hz, htoRealShift hw, hinner]
              ring
  have hminShift : IsMinOn φ Set.univ xBar := by
    -- The Chapter 12 argmax point is exactly the minimizer of the shifted objective.
    simpa [φ] using isMinOn_shifted_objective_of_mem_primal_argmax
      (f := f) (g := g) (A := A) σ h_problem yBar xBar hxBar
  have hxShift : x ∈ effective_domain φ := by
    simpa [hdomShift] using hx
  have hxBarShift : xBar ∈ effective_domain φ := by
    -- Compare against the finite value at `x` to see that the minimizer is finite as well.
    have hle : φ xBar ≤ φ x := (isMinOn_univ_iff.mp hminShift) x
    exact lt_top_iff_ne_top.mpr (lt_top_iff_ne_top.mp (lt_of_le_of_lt hle hxShift))
  let ψ : E → ℝ := fun z ↦ (φ z).toReal
  have hminReal : ∀ {z : E}, z ∈ effective_domain φ → ψ xBar ≤ ψ z := by
    intro z hz
    have hle : φ xBar ≤ φ z := (isMinOn_univ_iff.mp hminShift) z
    exact EReal.toReal_le_toReal hle (hne_bot_shift xBar) (ne_of_lt hz)
  let c : ℝ := ((σ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)
  have happrox :
      ∀ n : ℕ, ψ x - ψ xBar ≥ (n : ℝ) / (n + 1 : ℝ) * c := by
    intro n
    let a : ℝ := (n : ℝ) / (n + 1 : ℝ)
    let b : ℝ := 1 / (n + 1 : ℝ)
    have ha : 0 ≤ a := by
      positivity
    have hb : 0 ≤ b := by
      positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    have hm_dom : a • xBar + b • x ∈ effective_domain φ :=
      hstrongShift.1 hxBarShift hxShift ha hb hab
    have hmin_mid : ψ xBar ≤ ψ (a • xBar + b • x) :=
      hminReal hm_dom
    have hstrong_mid :
        ψ (a • xBar + b • x) ≤
          a * ψ xBar + b * ψ x - a * b * c :=
      by
        simpa [ψ, c, norm_sub_rev] using
          (hstrongShift.2 hxBarShift hxShift ha hb hab)
    have hcombine :
        ψ xBar ≤ a * ψ xBar + b * ψ x - a * b * c :=
      le_trans hmin_mid hstrong_mid
    have hb_pos : 0 < b := by
      positivity
    have hscaled :
        0 ≤ b * (ψ x - ψ xBar - a * c) := by
      have hcombine' : 0 ≤ a * ψ xBar + b * ψ x - a * b * c - ψ xBar := by
        linarith
      have hrewrite :
          a * ψ xBar + b * ψ x - a * b * c - ψ xBar =
            b * (ψ x - ψ xBar - a * c) := by
        have ha' : a = 1 - b := by
          linarith
        rw [ha']
        ring
      simpa [hrewrite] using hcombine'
    have hgoal_nonneg :
        0 ≤ ψ x - ψ xBar - a * c := by
      by_contra hneg
      have hneg' : ψ x - ψ xBar - a * c < 0 := lt_of_not_ge hneg
      have : b * (ψ x - ψ xBar - a * c) < 0 := by
        exact mul_neg_of_pos_of_neg hb_pos hneg'
      linarith
    simpa [a, c] using hgoal_nonneg
  have hquadReal :
      ψ x ≥ ψ xBar + c := by
    by_cases hxxBar : x = xBar
    · subst hxxBar
      simp [c]
    · have hc : 0 < c := by
        have hnorm_pos : 0 < ‖x - xBar‖ ^ (2 : ℕ) := by
          exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxxBar)) _
        have hσhalf_pos : 0 < ((σ : ℝ) / 2) := by
          exact div_pos σ.2 (by norm_num)
        exact mul_pos hσhalf_pos hnorm_pos
      by_contra hlt
      have hgap_pos : 0 < (c - (ψ x - ψ xBar)) / c := by
        have : 0 < c - (ψ x - ψ xBar) := by
          linarith
        exact div_pos this hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap_pos
      have hfrac :
          (ψ x - ψ xBar) / c < (n : ℝ) / (n + 1 : ℝ) := by
        have hleft :
            1 - (1 / (n + 1 : ℝ)) > 1 - ((c - (ψ x - ψ xBar)) / c) := by
          linarith
        have hleft' : (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
          field_simp
          ring
        have hright' : 1 - ((c - (ψ x - ψ xBar)) / c) = (ψ x - ψ xBar) / c := by
          have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
          field_simp [hc_ne]
          ring
        linarith
      have hlt' : ψ x - ψ xBar < (n : ℝ) / (n + 1 : ℝ) * c := by
        have hmul := mul_lt_mul_of_pos_right hfrac hc
        have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
        field_simp [hc_ne] at hmul
        have hn1pos : 0 < (n + 1 : ℝ) := by
          positivity
        have hmul' : (ψ x - ψ xBar) * (n + 1 : ℝ) < (n : ℝ) * c := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hdiv :
            ψ x - ψ xBar < ((n : ℝ) * c) / (n + 1 : ℝ) := by
          have hmul'' :
              (ψ x - ψ xBar) * (n + 1 : ℝ) <
                (((n : ℝ) * c) / (n + 1 : ℝ)) * (n + 1 : ℝ) := by
            simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
          have hdiv' :
              ((ψ x - ψ xBar) * (n + 1 : ℝ)) / (n + 1 : ℝ) <
                ((n : ℝ) * c) / (n + 1 : ℝ) := by
            exact (div_lt_iff₀ hn1pos).2 hmul''
          simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hge' := happrox n
      linarith
  have hx_toReal : ((ψ x : ℝ) : EReal) = φ x := by
    exact EReal.coe_toReal (ne_of_lt hxShift) (hne_bot_shift x)
  have hxBar_toReal : ((ψ xBar : ℝ) : EReal) = φ xBar := by
    exact EReal.coe_toReal (ne_of_lt hxBarShift) (hne_bot_shift xBar)
  have hquad :
      φ xBar + (((c : ℝ) : EReal)) ≤ φ x := by
    -- Push the real-valued quadratic gap back to `EReal` using finiteness on both endpoints.
    have hcoe :
        (((ψ xBar + c : ℝ) : EReal) ≤ ((ψ x : ℝ) : EReal)) := by
      exact EReal.coe_le_coe_iff.mpr hquadReal
    simpa [ψ, c, hx_toReal, hxBar_toReal, add_assoc] using hcoe
  -- Convert the additive lower bound into the subtraction form used in the target statement.
  exact
    (EReal.le_sub_iff_add_le
      (.inl (hne_bot_shift xBar))
      (.inr (ne_of_lt hxShift))).2 (by simpa [add_comm] using hquad)

/-- Helper for Lemma 12.7: the value attained by any primal minimizer is the dual problem value
`qOpt`, by primal attainment plus strong duality. -/
lemma primal_minimizer_value_eq_dual_problem_value
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    composite_model_objective f (g ∘ A) xStar =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  have hglb :
      IsGLB
        (Set.range (composite_model_objective f (g ∘ A)))
        (composite_model_objective f (g ∘ A) xStar) := by
    simpa using hxStar.isGLB (by simp : xStar ∈ (Set.univ : Set E))
  have hpOpt :
      dual_based_proximal_gradient_primal_optimal_value f g A =
        composite_model_objective f (g ∘ A) xStar := by
    rw [dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
    exact hglb.csInf_eq ⟨composite_model_objective f (g ∘ A) xStar, ⟨xStar, rfl⟩⟩
  -- Strong duality identifies the attained primal value with the Chapter 12 dual optimum.
  calc
    composite_model_objective f (g ∘ A) xStar =
        dual_based_proximal_gradient_primal_optimal_value f g A := hpOpt.symm
    _ = dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
        simpa using dual_based_proximal_gradient_problem_strong_duality
          (f := f) (g := g) (A := A) (σ := σ) h_problem

/-- Helper for Lemma 12.7: Fenchel's inequality at `(-yBar)` gives
`-(g∗) (-yBar) ≤ g z + ⟪yBar, z⟫`. -/
lemma fenchel_neg_conjugate_le_primal_plus_pairing
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (z : V) :
    -((g∗) (-yBar)) ≤ g z + (((inner ℝ yBar z : ℝ) : EReal)) := by
  have hconj_ne_bot : (g∗) (-yBar) ≠ ⊥ := by
    exact
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g) h_problem.g_proper h_problem.g_convex).ne_bot yBar
  -- Start from Fenchel's inequality at the dual point `-yBar`.
  have hfenchel :
      (((-inner ℝ yBar z : ℝ) : EReal)) ≤ g z + (g∗) (-yBar) := by
    simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
      inner_neg_left, add_comm] using
      (fenchel_inequality g z (InnerProductSpace.toDualMap ℝ V (-yBar)) h_problem.g_proper)
  -- Move the conjugate term left, then move the finite pairing term back to the right.
  have hsub :
      -((g∗) (-yBar)) - (((inner ℝ yBar z : ℝ) : EReal)) ≤ g z := by
    have htmp :
        (((-inner ℝ yBar z : ℝ) : EReal) - (g∗) (-yBar)) ≤ g z :=
      (EReal.sub_le_iff_le_add
        (.inl hconj_ne_bot)
        (.inr (h_problem.g_proper.ne_bot z))).2 hfenchel
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
  exact
    (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot _))
      (.inr (h_problem.g_proper.ne_bot z))).1 hsub

/-- Helper for Lemma 12.7: the normalized `EReal` shape
`a + (r + (-r - b))` collapses to `a - b`. -/
lemma ereal_add_real_cancel_sub (a b : EReal) (r : ℝ) :
    a + ((r : EReal) + (-((r : EReal)) - b)) = a - b := by
  -- This packages the exact cancellation shape produced by the dual-objective rewrite.
  have hzero : ((r : EReal) + -((r : EReal))) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  calc
    a + ((r : EReal) + (-((r : EReal)) - b)) =
        a + ((((r : EReal)) + -((r : EReal))) + -b) := by
          rw [sub_eq_add_neg, add_assoc]
    _ = a + (0 + -b) := by
          rw [hzero]
    _ = a - b := by
          rw [zero_add, sub_eq_add_neg]

/-- Helper for Lemma 12.7: the normalized `EReal` shape
`(a - r) + (b + r)` collapses to `a + b`. -/
lemma ereal_sub_real_add_real_cancel (a b : EReal) (r : ℝ) :
    (a - ((r : EReal))) + (b + ((r : EReal))) = a + b := by
  -- This records the pairing cancellation after rewriting through the adjoint identity.
  have hzero : (-((r : EReal)) + ((r : EReal))) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  have hinner :
      -((r : EReal)) + (b + ((r : EReal))) =
        b + (-((r : EReal)) + ((r : EReal))) := by
    calc
      -((r : EReal)) + (b + ((r : EReal))) =
          (-((r : EReal)) + b) + ((r : EReal)) := by
            rw [add_assoc]
      _ = (b + -((r : EReal))) + ((r : EReal)) := by
            rw [add_comm (-((r : EReal))) b]
      _ = b + (-((r : EReal)) + ((r : EReal))) := by
            rw [← add_assoc]
  calc
    (a - ((r : EReal))) + (b + ((r : EReal))) =
        a + (-((r : EReal)) + (b + ((r : EReal)))) := by
          rw [sub_eq_add_neg, add_assoc]
    _ = a + (b + (-((r : EReal)) + ((r : EReal)))) := by
          simpa using congrArg (fun t : EReal ↦ a + t) hinner
    _ = a + (b + 0) := by
          rw [hzero]
    _ = a + b := by
          rw [add_zero]

/-- Helper for Lemma 12.7: every Chapter 12 primal-space dual objective value avoids `⊤`. -/
lemma dual_objective_ne_top
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V) :
    q yBar ≠ ⊤ := by
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yBar
  have hG_ne_bot : (g∗) (-yBar) ≠ ⊥ := by
    exact
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g) h_problem.g_proper h_problem.g_convex).ne_bot yBar
  by_cases hG_top : (g∗) (-yBar) = ⊤
  · -- If `g*(-yBar) = ⊤`, then the dual objective is `⊥`, hence certainly not `⊤`.
    rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, hG_top]
    simp
  · have hF_val :
        (((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) = (f∗) (A.adjoint yBar) := by
        exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
    have hG_val :
        (((((g∗) (-yBar)).toReal : ℝ) : EReal)) = (g∗) (-yBar) := by
        exact EReal.coe_toReal hG_top hG_ne_bot
    -- When both conjugate terms are finite, the dual objective is a finite `EReal` value.
    have hfinite_ne_top :
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
          (((((g∗) (-yBar)).toReal : ℝ) : EReal)) ≠ ⊤ := by
      rw [sub_eq_add_neg]
      have hcoe :
          -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) +
            -(((((g∗) (-yBar)).toReal : ℝ) : EReal)) =
            (((-((f∗) (A.adjoint yBar)).toReal + -((g∗) (-yBar)).toReal : ℝ)) : EReal) := by
              rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
      rw [hcoe]
      exact EReal.coe_ne_top _
    intro htop
    have htop' :
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
          (((((g∗) (-yBar)).toReal : ℝ) : EReal)) = ⊤ := by
      -- Rewrite the source dual objective back to its real-coercion normal form before
      -- contradicting finiteness above.
      calc
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
            (((((g∗) (-yBar)).toReal : ℝ) : EReal)) =
          -((f∗) (A.adjoint yBar)) - (g∗) (-yBar) := by
            rw [hF_val, hG_val]
        _ = ⊤ := by
            simpa [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply] using htop
    exact hfinite_ne_top htop'

/-- Helper for Lemma 12.7: the source proof naturally produces the additive inequality
`(σ / 2) ‖xBar - xStar‖² + q(yBar) ≤ f(xStar) + g(A xStar)`. -/
lemma half_sigma_sqdist_add_dual_objective_le_primal_value_of_primal_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar xStar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
      composite_model_objective f (g ∘ A) xStar := by
  let innerBar : ℝ := inner ℝ xBar (A.adjoint yBar)
  let innerStar : ℝ := inner ℝ xStar (A.adjoint yBar)
  let dualCoeff : ℝ := ((f∗) (A.adjoint yBar)).toReal
  have hxStar_dom :
      xStar ∈ effective_domain f := by
    exact primal_minimizer_mem_effective_domain
      (f := f) (g := g) (A := A) σ h_problem xStar hxStar
  have hgap :=
    shifted_objective_gap_ge_half_sigma_sqdist_of_mem_primal_argmax
      (f := f) (g := g) (A := A) σ h_problem yBar xBar hxBar xStar hxStar_dom
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yBar
  have hdualCoeff :
      (((dualCoeff : ℝ) : EReal)) = (f∗) (A.adjoint yBar) := by
    -- The Chapter 12 `F`-term is finite everywhere, so we can safely pass to its real value.
    exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
  have hshift_bar :
      f xBar - (((innerBar : ℝ) : EReal)) = -((f∗) (A.adjoint yBar)) := by
    -- Route correction: identify the shifted value at `xBar` with `-f*(Aᵀ yBar)` first, then the
    -- endgame reduces to the explicit cancellation lemmas instead of broad `simp`.
    calc
      f xBar - (((innerBar : ℝ) : EReal)) =
          -((((innerBar : ℝ) : EReal) - f xBar)) := by
            simpa [innerBar] using (ereal_neg_real_sub (a := f xBar) (r := innerBar)).symm
      _ = -((f∗) (A.adjoint yBar)) := by
            rw [conjugate_primal_eq_pairing_sub_of_mem_primal_argmax
              (f := f) (g := g) (A := A) σ h_problem yBar xBar hxBar]
  have hadj :
      inner ℝ xStar (A.adjoint yBar) = inner ℝ yBar (A xStar) := by
    -- Rewrite the primal-space pairing through the adjoint before the final cancellation step.
    simpa [real_inner_comm] using (LinearMap.adjoint_inner_right A xStar yBar)
  calc
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
        ((f xStar - (((innerStar : ℝ) : EReal))) -
          (f xBar - (((innerBar : ℝ) : EReal)))) + q yBar := by
          simpa [add_assoc, add_left_comm, add_comm, innerBar, innerStar, norm_sub_rev] using
            add_le_add_left hgap (q yBar)
    _ = (f xStar - (((innerStar : ℝ) : EReal))) +
          (((dualCoeff : ℝ) : EReal) +
            (-(((dualCoeff : ℝ) : EReal)) - (g∗) (-yBar))) := by
          rw [hshift_bar, dual_based_proximal_gradient_lagrange_dual_objective_primal_apply,
            hdualCoeff]
          rw [sub_eq_add_neg, sub_eq_add_neg, neg_neg]
          ac_rfl
    _ = (f xStar - (((innerStar : ℝ) : EReal))) - (g∗) (-yBar) := by
          rw [ereal_add_real_cancel_sub]
    _ ≤ (f xStar - (((innerStar : ℝ) : EReal))) +
          (g (A xStar) + (((inner ℝ yBar (A xStar) : ℝ) : EReal))) := by
          -- Apply Fenchel to the `g`-term at `z = A xStar`.
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            add_le_add_left
              (fenchel_neg_conjugate_le_primal_plus_pairing
                (f := f) (g := g) (A := A) σ h_problem yBar (A xStar))
              (f xStar - (((innerStar : ℝ) : EReal)))
    _ = f xStar + g (A xStar) := by
          simpa [innerStar, hadj] using
            (ereal_sub_real_add_real_cancel
              (a := f xStar) (b := g (A xStar)) (r := inner ℝ yBar (A xStar)))
    _ = composite_model_objective f (g ∘ A) xStar := by
          rw [composite_model_objective_apply, Function.comp]

/-- Lemma 12.7: under Assumption 12.1, if `xBar` belongs to the primal argmax set
`argmax_x {⟪x, Aᵀ yBar⟫ - f x}`, then for every primal optimizer `xStar` the canonical Chapter 12
dual gap at `yBar` dominates `(σ / 2) ‖xBar - xStar‖²`. This is the owner-level form of the
textbook inequality `‖xBar - xStar‖² ≤ (2 / σ) (q_opt - q(yBar))`, stated directly with
`dual_based_proximal_gradient_lagrange_dual_objective_primal`. -/
theorem half_sigma_sqdist_le_dual_gap_of_primal_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar xStar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      qOpt - q yBar := by
  have hadd :
      ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤ qOpt := by
    -- Follow the source proof: first prove the additive inequality against the primal value,
    -- then identify that primal value with `qOpt`.
    calc
      ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
          composite_model_objective f (g ∘ A) xStar :=
        half_sigma_sqdist_add_dual_objective_le_primal_value_of_primal_argmax
          (f := f) (g := g) (A := A) σ h_problem yBar xBar xStar hxBar hxStar
      _ = qOpt := by
          simpa using primal_minimizer_value_eq_dual_problem_value
            (f := f) (g := g) (A := A) σ h_problem xStar hxStar
  -- Convert the additive source inequality into the displayed dual-gap subtraction form.
  have hq_ne_top : q yBar ≠ ⊤ :=
    dual_objective_ne_top (f := f) (g := g) (A := A) σ h_problem yBar
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    rw [← primal_minimizer_value_eq_dual_problem_value
      (f := f) (g := g) (A := A) σ h_problem xStar hxStar]
    simp [Function.comp,
      h_problem.ne_bot xStar, h_problem.g_proper.ne_bot (A xStar)]
  exact
    (EReal.le_sub_iff_add_le
      (a := ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal))
      (b := q yBar) (c := qOpt)
      (.inr hqOpt_ne_bot)
      (.inl hq_ne_top)).2 hadd

end
