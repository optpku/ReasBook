/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_43
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section NormPower

variable (K : Type v) [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: the norm is convex, continuous, and nonnegative; composing it with the increasing
-- convex map `t ↦ t^p` on `[0,+∞)` for `p > 1` yields a lower semicontinuous convex proper
-- function.
/-- The norm-power function belongs to `Γ₀(K)` for exponents `p > 1`. -/
theorem normPowerFunction_mem_gammaZero (p : ℝ) (hp : 1 < p) :
    (fun y : K ↦ ‖y‖ ^ p).toEReal ∈ Γ₀(K) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- The real-valued norm-power map is continuous, so its `EReal` coercion is lsc.
    have hcont : Continuous (fun y : K ↦ (((‖y‖ ^ p : ℝ) : EReal))) := by
      exact continuous_coe_real_ereal.comp
        (continuous_norm.rpow_const fun y ↦ Or.inr (le_trans zero_le_one hp.le))
    simpa using hcont.lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · -- A finite real-valued function has nonempty effective domain.
      exact ⟨0, by simp [Function.effectiveDomain_toEReal]⟩
    · -- Every point is in the effective domain of a finite real-valued function.
      simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy α hα0 hα1
      have hβ0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
      have hnorm : ‖α • x + (1 - α) • y‖ ≤ α * ‖x‖ + (1 - α) * ‖y‖ := by
        -- First apply convexity of the norm itself.
        simpa [smul_eq_mul] using
          (convexOn_univ_norm.2 (by simp) (by simp) hα0.le hβ0 (by ring))
      have hpow_monotone :
          ‖α • x + (1 - α) • y‖ ^ p ≤ (α * ‖x‖ + (1 - α) * ‖y‖) ^ p := by
        -- Then raise both sides with the monotone exponent map on `[0, +∞)`.
        exact Real.rpow_le_rpow (norm_nonneg _) hnorm (le_trans zero_le_one hp.le)
      have hpow_convex :
          (α * ‖x‖ + (1 - α) * ‖y‖) ^ p ≤ α * ‖x‖ ^ p + (1 - α) * ‖y‖ ^ p := by
        -- Finally use convexity of `t ↦ t ^ p` on the nonnegative reals.
        simpa [smul_eq_mul] using
          (convexOn_rpow hp.le).2 (by simp [norm_nonneg]) (by simp [norm_nonneg])
            hα0.le hβ0 (by ring)
      have hreal :
          ‖α • x + (1 - α) • y‖ ^ p ≤ α * ‖x‖ ^ p + (1 - α) * ‖y‖ ^ p :=
        le_trans hpow_monotone hpow_convex
      simpa [Function.toEReal_apply] using
        (show (((‖α • x + (1 - α) • y‖ ^ p : ℝ) : EReal)) ≤
            (α : EReal) * (((‖x‖ ^ p : ℝ) : EReal)) +
              ((1 - α : ℝ) : EReal) * (((‖y‖ ^ p : ℝ) : EReal)) from by
          exact_mod_cast hreal)

end NormPower

section Perspective

variable {H : Type u} (K : Type v)
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The explicit `]-∞,+∞]`-valued formula of Example 9.45. -/
noncomputable def normPowerPerspectiveEReal
    (p : ℝ) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    H → EReal :=
  fun x ↦
    if ρ < ⟪x, u⟫_ℝ then
      ((‖L x - r‖ ^ p / (⟪x, u⟫_ℝ - ρ) ^ (p - 1) : ℝ) : EReal)
    else if ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0 then
      0
    else
      ⊤

/-- The explicit formula of Example 9.45 never takes the value `-∞`. -/
theorem normPowerPerspectiveEReal_ne_bot
    (p : ℝ) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) (x : H) :
    ⊥ < normPowerPerspectiveEReal K p L r u ρ x := by
  -- Split according to the three textbook branches of the explicit formula.
  unfold normPowerPerspectiveEReal
  split_ifs with hρ hEq
  · exact EReal.bot_lt_coe _
  · simp
  · exact bot_lt_top

/-- The source-facing `]-∞,+∞]`-valued function of Example 9.45. -/
noncomputable def normPowerPerspective
    (p : ℝ) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨normPowerPerspectiveEReal K p L r u ρ x,
      normPowerPerspectiveEReal_ne_bot K p L r u ρ x⟩

/-- Coercing `normPowerPerspective` to `EReal` recovers its explicit formula. -/
@[simp] theorem normPowerPerspective_coe
    (p : ℝ) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) (x : H) :
    (normPowerPerspective K p L r u ρ x : EReal) =
      normPowerPerspectiveEReal K p L r u ρ x := rfl

-- Proof sketch: evaluate the specialized `closedPerspective`. In the positive-height branch, the
-- perspective of `y ↦ ‖y‖^p` simplifies to the quotient formula
-- `‖L x - r‖^p / (⟪x, u⟫_ℝ - ρ)^(p - 1)`. For `p > 1`, Example 9.32 identifies the
-- zero-height recession value with `0` exactly when `‖L x - r‖ = 0`, and with `+∞` otherwise.
/-- The source-facing formula of Example 9.45 agrees with the canonical closed-perspective
specialization of `y ↦ ‖y‖ ^ p`. -/
@[simp] theorem normPowerPerspective_coe_eq_closedPerspective_comp
    (p : ℝ) (hp : 1 < p) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) (x : H) :
    (normPowerPerspective K p L r u ρ x : EReal) =
      (closedPerspective
        ((fun y : K ↦ ‖y‖ ^ p).toEReal)
        (normPowerFunction_mem_gammaZero K p hp).2.nonempty
        (⟪x, u⟫_ℝ - ρ, L x - r) : EReal) := by
  -- Evaluate the origin model from Example 9.43 at the affine-substituted point.
  rw [normPowerPerspective_coe, normPowerPerspectiveEReal, closedPerspective_coe]
  by_cases hρ : ρ < ⟪x, u⟫_ℝ
  · -- In the positive branch, both formulas reduce to the same quotient.
    simpa [normPowerPerspectiveAtOrigin, sub_pos, hρ, sub_eq_zero, norm_eq_zero] using
      (normPowerPerspectiveAtOrigin_apply
        (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r)).symm
  · by_cases hEq : ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0
    · -- On the zero slice with vanishing residual, the origin model takes the value `0`.
      have hpair : (⟪x, u⟫_ℝ - ρ, L x - r) = (0, (0 : K)) := by
        simpa [sub_eq_zero, norm_eq_zero] using hEq
      have horigin0 :
          closedPerspectiveEReal ((fun y : K ↦ ‖y‖ ^ p).toEReal)
            (normPowerFunction_mem_gammaZero K p hp).2.nonempty
            (⟪x, u⟫_ℝ - ρ, L x - r) = 0 := by
        simpa [normPowerPerspectiveAtOrigin, sub_pos, hρ, hpair] using
          (normPowerPerspectiveAtOrigin_apply
            (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r))
      simpa [hρ, hEq] using horigin0.symm
    · -- Otherwise both formulas land in the `+∞` branch.
      have hpair : (⟪x, u⟫_ℝ - ρ, L x - r) ≠ (0, (0 : K)) := by
        intro hpair
        apply hEq
        simpa [sub_eq_zero, norm_eq_zero] using hpair
      have horigin_top :
          closedPerspectiveEReal ((fun y : K ↦ ‖y‖ ^ p).toEReal)
            (normPowerFunction_mem_gammaZero K p hp).2.nonempty
            (⟪x, u⟫_ℝ - ρ, L x - r) = ⊤ := by
        simpa [normPowerPerspectiveAtOrigin, sub_pos, hρ, hpair] using
          (normPowerPerspectiveAtOrigin_apply
            (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r))
      have hleft :
          (if ρ < ⟪x, u⟫_ℝ then
              ((‖L x - r‖ ^ p / (⟪x, u⟫_ℝ - ρ) ^ (p - 1) : ℝ) : EReal)
            else if ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0 then
              0
            else
              ⊤) = ⊤ := by
        rw [if_neg hρ]
        by_cases hcond : ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0
        · exact False.elim (hEq hcond)
        · rw [if_neg hcond]
      rw [hleft]
      exact horigin_top.symm

/-- Evaluating `normPowerPerspective` gives the explicit textbook formula of Example 9.45. -/
@[simp] theorem normPowerPerspective_apply
    (p : ℝ) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) (x : H) :
    (normPowerPerspective K p L r u ρ x : EReal) =
      if ρ < ⟪x, u⟫_ℝ then
        ((‖L x - r‖ ^ p / (⟪x, u⟫_ℝ - ρ) ^ (p - 1) : ℝ) : EReal)
      else if ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0 then
        0
      else
        ⊤ := rfl

/-- Helper for Example 9.45: the substitution
`x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)` splits into its linear part plus its value at the origin. -/
lemma norm_power_perspective_substitution_linear_decomp
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    ∀ x : H,
      (fun y : H ↦ (⟪y, u⟫_ℝ - ρ, L y - r)) x =
        ((((innerSL ℝ u).toLinearMap).prod L.toLinearMap) (x -ᵥ (0 : H))) +ᵥ
          (fun y : H ↦ (⟪y, u⟫_ℝ - ρ, L y - r)) 0 := by
  intro x
  -- Expanding the linear part at the origin recovers the explicit affine formula.
  simp [vsub_eq_sub, vadd_eq_add, LinearMap.prod_apply, sub_eq_add_neg, real_inner_comm]

/-- Helper for Example 9.45: the substitution
`x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)` is affine. -/
lemma norm_power_perspective_substitution_affine
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    ∃ A : H →ᵃ[ℝ] (ℝ × K), (A : H → (ℝ × K)) = fun x ↦ (⟪x, u⟫_ℝ - ρ, L x - r) := by
  -- Package the explicit substitution into the bundled affine map used in the pullback proof.
  let A : H →ᵃ[ℝ] (ℝ × K) :=
    AffineMap.mk'
      (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r))
      ((((innerSL ℝ u).toLinearMap).prod L.toLinearMap))
      (0 : H)
      (norm_power_perspective_substitution_linear_decomp
        (K := K) (L := L) (r := r) (u := u) (ρ := ρ))
  exact ⟨A, rfl⟩

-- Proof sketch: apply Corollary 9.44 with `φ = (fun y ↦ ‖y‖^p).toEReal`. The bridge theorem
-- `normPowerPerspective_coe_eq_closedPerspective_comp` identifies the source-facing formula with
-- the canonical closed perspective, while the extra hypothesis supplies a point where that closed
-- perspective is finite, which is the properness witness needed by the owner theorem.
/-- Example 9.45: for `p > 1`, if there exists `z` with either `ρ < ⟪z, u⟫_ℝ` or
`⟪z, u⟫_ℝ = ρ` and `L z = r`, then the function
`x ↦ ‖L x - r‖^p / (⟪x, u⟫_ℝ - ρ)^(p - 1)` on the half-space `ρ < ⟪x, u⟫_ℝ`, extended by `0`
when `⟪x, u⟫_ℝ = ρ` and `L x = r`, and by `+∞` otherwise, belongs to `Γ₀(H)`. -/
theorem normPowerPerspective_mem_gammaZero
    (p : ℝ) (hp : 1 < p) (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ)
    (hz : ∃ z : H, ρ < ⟪z, u⟫_ℝ ∨ ⟪z, u⟫_ℝ = ρ ∧ L z = r) :
    normPowerPerspective K p L r u ρ ∈ Γ₀(H) := by
  have hcomp :
      (normPowerPerspectiveAtOrigin (H := K) p) ∘
        (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r)) ∈ Γ₀(H) := by
    rcases norm_power_perspective_substitution_affine
      (K := K) (L := L) (r := r) (u := u) (ρ := ρ) with ⟨A, hA⟩
    have hA_apply : ∀ x : H, A x = (⟪x, u⟫_ℝ - ρ, L x - r) := by
      intro x
      simpa using congrFun hA x
    have horigin : normPowerPerspectiveAtOrigin (H := K) p ∈ Γ₀(ℝ × K) :=
      normPowerPerspectiveAtOrigin_mem_gammaZero (H := K) p hp
    rw [mem_gammaZero_iff] at horigin ⊢
    constructor
    · -- Lower semicontinuity is preserved by the continuous affine substitution.
      have hcont : Continuous (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r)) := by
        have hfst0 : Continuous (fun x : H ↦ ⟪u, x⟫_ℝ) :=
          continuous_const.inner continuous_id
        have hfst : Continuous (fun x : H ↦ ⟪x, u⟫_ℝ - ρ) := by
          simpa [real_inner_comm] using hfst0.sub continuous_const
        have hsnd : Continuous (fun x : H ↦ L x - r) := L.continuous.sub continuous_const
        exact hfst.prodMk hsnd
      simpa [Function.comp, hA_apply] using horigin.1.comp hcont
    · refine ⟨?_, subset_rfl, ?_⟩
      · rcases hz with ⟨z, hz | hz⟩
        · -- A strict-height witness lands in the positive branch of the origin model.
          refine ⟨z, ?_⟩
          have hz_mem : (normPowerPerspectiveAtOrigin (H := K) p (A z) : EReal) < ⊤ := by
            rw [hA_apply z, normPowerPerspectiveAtOrigin_apply (H := K) p hp]
            simp [sub_pos.mpr hz]
          have hz_mem' :
              (normPowerPerspectiveAtOrigin (H := K) p (⟪z, u⟫_ℝ - ρ, L z - r) : EReal) < ⊤ := by
            simpa [hA_apply z] using hz_mem
          simpa [effectiveDomain, Function.comp] using hz_mem'
        · -- A zero-height witness with `L z = r` lands at the finite value `0`.
          refine ⟨z, ?_⟩
          have hz_sub : ⟪z, u⟫_ℝ - ρ = 0 := sub_eq_zero.mpr hz.1
          have hz_lin : L z - r = 0 := sub_eq_zero.mpr hz.2
          have hz_eval : (normPowerPerspectiveAtOrigin (H := K) p (A z) : EReal) = 0 := by
            rw [hA_apply z, normPowerPerspectiveAtOrigin_apply (H := K) p hp]
            simp [hz_sub, hz_lin]
          have hz_mem : (normPowerPerspectiveAtOrigin (H := K) p (A z) : EReal) < ⊤ := by
            rw [hz_eval]
            simp
          have hz_mem' :
              (normPowerPerspectiveAtOrigin (H := K) p (⟪z, u⟫_ℝ - ρ, L z - r) : EReal) < ⊤ := by
            simpa [hA_apply z] using hz_mem
          simpa [effectiveDomain, Function.comp] using hz_mem'
      · intro x hx y hy α hα0 hα1
        have hx_origin : A x ∈ effectiveDomain (normPowerPerspectiveAtOrigin (H := K) p) := by
          simpa [effectiveDomain, Function.comp, hA_apply x] using hx
        have hy_origin : A y ∈ effectiveDomain (normPowerPerspectiveAtOrigin (H := K) p) := by
          simpa [effectiveDomain, Function.comp, hA_apply y] using hy
        have hmap :
            α • A x + (1 - α) • A y = A (α • x + (1 - α) • y) := by
          -- The affine map sends convex combinations in `H` to convex combinations in `ℝ × K`.
          simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
            (A.apply_lineMap y x α).symm
        have hineq := horigin.2.ineq hx_origin hy_origin hα0 hα1
        -- Rewrite the owner inequality back along the affine substitution.
        rw [hmap] at hineq
        simpa [Function.comp, hA_apply (α • x + (1 - α) • y), hA_apply x, hA_apply y] using hineq
  have hfun :
      normPowerPerspective K p L r u ρ =
        (normPowerPerspectiveAtOrigin (H := K) p) ∘
          (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r)) := by
    funext x
    apply Subtype.ext
    rw [normPowerPerspective_coe, normPowerPerspectiveEReal]
    -- Route correction: transport the textbook formula through Example 9.43 instead of the
    -- stronger ambient assumptions from Corollary 9.44.
    by_cases hρ : ρ < ⟪x, u⟫_ℝ
    · simpa [Function.comp, sub_pos, hρ, sub_eq_zero, norm_eq_zero] using
        (normPowerPerspectiveAtOrigin_apply
          (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r)).symm
    · by_cases hEq : ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0
      · have hpair : (⟪x, u⟫_ℝ - ρ, L x - r) = (0, (0 : K)) := by
          simpa [sub_eq_zero, norm_eq_zero] using hEq
        have horigin0 :
            (normPowerPerspectiveAtOrigin (H := K) p (⟪x, u⟫_ℝ - ρ, L x - r) : EReal) = 0 := by
          simpa [sub_pos, hρ, hpair] using
            (normPowerPerspectiveAtOrigin_apply
              (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r))
        simpa [Function.comp, hρ, hEq] using horigin0.symm
      · have hpair : (⟪x, u⟫_ℝ - ρ, L x - r) ≠ (0, (0 : K)) := by
          intro hpair
          apply hEq
          simpa [sub_eq_zero, norm_eq_zero] using hpair
        have horigin_top :
            (normPowerPerspectiveAtOrigin (H := K) p (⟪x, u⟫_ℝ - ρ, L x - r) : EReal) = ⊤ := by
          simpa [sub_pos, hρ, hpair] using
            (normPowerPerspectiveAtOrigin_apply
              (H := K) p hp (⟪x, u⟫_ℝ - ρ, L x - r))
        have hleft :
            (if ρ < ⟪x, u⟫_ℝ then
                ((‖L x - r‖ ^ p / (⟪x, u⟫_ℝ - ρ) ^ (p - 1) : ℝ) : EReal)
              else if ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0 then
                0
              else
                ⊤) = ⊤ := by
          rw [if_neg hρ]
          by_cases hcond : ⟪x, u⟫_ℝ = ρ ∧ ‖L x - r‖ = 0
          · exact False.elim (hEq hcond)
          · rw [if_neg hcond]
        rw [hleft]
        exact horigin_top.symm
  -- The source-facing function is exactly the pulled-back origin model.
  simpa [hfun] using hcomp

end Perspective

end ERealFunction
