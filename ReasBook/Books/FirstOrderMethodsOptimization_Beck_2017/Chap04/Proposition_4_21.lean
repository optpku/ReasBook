/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_7
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/-- The function `x ↦ √(α² + ‖x‖²)`, regarded as an `EReal`-valued function so it can be fed to
the chapter owner `conjugate_function`. -/
def sqrt_alpha_sq_add_norm_sq_function (α : ℝ) : E → EReal :=
  fun x ↦ ((Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)

-- Proof sketch: unfold `sqrt_alpha_sq_add_norm_sq_function`; the statement is exactly its defining
-- formula.
/-- Evaluating `sqrt_alpha_sq_add_norm_sq_function α` at `x` gives the `EReal` lift of
`√(α² + ‖x‖²)`. -/
theorem sqrt_alpha_sq_add_norm_sq_function_apply (α : ℝ) (x : E) :
    sqrt_alpha_sq_add_norm_sq_function α x =
      ((Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

/-- The values of `sqrt_alpha_sq_add_norm_sq_function α` are finite, so `toReal` recovers the
underlying square-root expression. -/
@[simp] theorem sqrt_alpha_sq_add_norm_sq_function_toReal (α : ℝ) (x : E) :
    (sqrt_alpha_sq_add_norm_sq_function α x).toReal =
      Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ)) := by
  simp [sqrt_alpha_sq_add_norm_sq_function]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.21 is `source-facing` in the chapter conjugacy API. The owner abstractions for
the conjugate and the dual norm already live upstream as `conjugate_function` and `dualNorm`, so
the only primitive data local to this file are the specific model function
`x ↦ √(α² + ‖x‖²)` and the source-facing conjugacy formula for that function. -/
recall conjugate_function
recall dualNorm

omit [FiniteDimensional ℝ E] in
-- Proof sketch: factor `α²` out of the radical and use `α > 0` to rewrite `√(α²)` as `α`.
/-- For `α > 0`, evaluating `sqrt_alpha_sq_add_norm_sq_function α` at `x` is the same as
evaluating the unit profile `sqrt_alpha_sq_add_norm_sq_function 1` at `(1 / α) • x` and then
scaling by `α`. -/
theorem sqrt_alpha_sq_add_norm_sq_function_eq_pos_real_mul_precomp_inv_smul
    (α : ℝ) (hα : 0 < α) (x : E) :
    sqrt_alpha_sq_add_norm_sq_function α x =
      (α : EReal) * sqrt_alpha_sq_add_norm_sq_function 1 ((1 / α) • x) := by
  have hα_nonneg : 0 ≤ α := hα.le
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hnorm_smul : ‖((1 / α) • x : E)‖ = ‖x‖ / α := by
    rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr hα_nonneg)]
    field_simp [hα_ne]
  have hmul :
      α ^ (2 : ℕ) * (1 + ‖((1 / α) • x : E)‖ ^ (2 : ℕ)) =
        α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ) := by
    rw [hnorm_smul]
    field_simp [hα_ne]
  rw [sqrt_alpha_sq_add_norm_sq_function_apply, sqrt_alpha_sq_add_norm_sq_function_apply,
    ← EReal.coe_mul]
  congr 1
  simpa using calc
    Real.sqrt (α ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ))
        = Real.sqrt (α ^ (2 : ℕ) * (1 + ‖((1 / α) • x : E)‖ ^ (2 : ℕ))) := by
            rw [← hmul]
    _ = Real.sqrt (α ^ (2 : ℕ)) * Real.sqrt (1 + ‖((1 / α) • x : E)‖ ^ (2 : ℕ)) := by
          rw [Real.sqrt_mul (by positivity)]
    _ = α * Real.sqrt (1 + ‖((1 / α) • x : E)‖ ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hα_nonneg]

/-- Helper for Proposition 4.21: the strict interior optimizer of
`r ↦ s * r - √(1 + r²)` attains the value `-√(1 - s²)` for `0 ≤ s < 1`. -/
lemma scalarSqrtObjective_eq_optimizer
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    let r := s / Real.sqrt (1 - s ^ (2 : ℕ))
    s * r - Real.sqrt (1 + r ^ (2 : ℕ)) = -Real.sqrt (1 - s ^ (2 : ℕ)) := by
  have hs_sq_lt : s ^ (2 : ℕ) < 1 := by
    nlinarith
  have hs_rad_nonneg : 0 ≤ 1 - s ^ (2 : ℕ) := by
    linarith
  have hs_rad_pos : 0 < 1 - s ^ (2 : ℕ) := by
    linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - s ^ (2 : ℕ)) := Real.sqrt_pos.2 hs_rad_pos
  have hsqrt_ne : Real.sqrt (1 - s ^ (2 : ℕ)) ≠ 0 := ne_of_gt hsqrt_pos
  -- Rewrite the optimizer radius into a rational expression in `√(1 - s²)`.
  dsimp
  have hrad :
      1 + (s / Real.sqrt (1 - s ^ (2 : ℕ))) ^ (2 : ℕ) =
        (1 - s ^ (2 : ℕ))⁻¹ := by
    field_simp [pow_two, hsqrt_ne]
    ring_nf
    rw [Real.sq_sqrt hs_rad_nonneg]
    ring
  have hsqrt_eval :
      Real.sqrt (1 + (s / Real.sqrt (1 - s ^ (2 : ℕ))) ^ (2 : ℕ)) =
        1 / Real.sqrt (1 - s ^ (2 : ℕ)) := by
    rw [hrad, Real.sqrt_inv]
    simp [one_div]
  rw [hsqrt_eval]
  have hsqrt_sq : Real.sqrt (1 - s ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - s ^ (2 : ℕ) := by
    rw [Real.sq_sqrt hs_rad_nonneg]
  -- Clearing denominators finishes the scalar computation.
  field_simp [pow_two, hsqrt_ne]
  ring_nf
  rw [hsqrt_sq]
  ring

/-- Helper for Proposition 4.21: along a unit witness `u` with `y u = ‖y‖_*`, the Fenchel
integrand of `x ↦ √(1 + ‖x‖²)` at the ray `t • u` reduces to the scalar objective
`t * ‖y‖_* - √(1 + t²)`. -/
lemma sqrtOneAddNormSqFunction_integrand_smul_unit
    (y : Module.Dual ℝ E) {u : E} (hu_norm : ‖u‖ = 1)
    (hu_dual : y u = dualNorm y) (t : ℝ) (ht : 0 ≤ t) :
    ((y (t • u) : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 (t • u)) =
      (((t * dualNorm y - Real.sqrt (1 + t ^ (2 : ℕ)) : ℝ)) : EReal) := by
  -- Evaluate both the dual pairing and the norm on the chosen ray.
  have hyt : y (t • u) = t * dualNorm y := by
    rw [map_smul, hu_dual, smul_eq_mul]
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, hu_norm, Real.norm_of_nonneg ht, mul_one]
  rw [hyt, sqrt_alpha_sq_add_norm_sq_function_apply, hnorm, ← EReal.coe_sub]
  norm_num

/-- Helper for Proposition 4.21: the boundary ray difference
`n - √(1 + n²)` is the negative reciprocal of `n + √(1 + n²)`. -/
lemma rayDifference_eq_negInv (n : ℕ) :
    (n : ℝ) - Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) =
      -(1 / ((n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)))) := by
  have hsqrt_pos : 0 < Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) := by
    apply Real.sqrt_pos.2
    positivity
  have hden_ne : (n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) ≠ 0 := by
    linarith
  have hsqrt_sq : Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) = 1 + (n : ℝ) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt]
    positivity
  -- Multiply by the positive conjugate denominator once, then simplify the square root.
  field_simp [hden_ne]
  ring_nf
  rw [hsqrt_sq]
  ring

/-- Helper for Proposition 4.21: on the closed dual unit ball, the conjugate of
`x ↦ √(1 + ‖x‖²)` is `-√(1 - ‖y‖_*²)`. -/
lemma sqrtOneAddNormSqFunction_conjugate_eq_of_dualNorm_le_one
    (y : Module.Dual ℝ E) (hy : dualNorm y ≤ 1) :
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function (E := E) 1) y =
      ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  rw [conjugate_function_apply]
  apply le_antisymm
  · -- Compare each Fenchel term to the scalar barrier inequality from Proposition 4.19.
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    have hpair : y x ≤ dualNorm y * ‖x‖ := by
      exact le_trans (le_abs_self _) (abs_apply_le_dual_norm_mul_norm y x)
    have hscalar :
        dualNorm y * ‖x‖ + Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) ≤
          Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)) := by
      simpa [add_comm, mul_comm] using
        scalarBarrierObjective_le ‖x‖ (dualNorm y) (norm_nonneg x) hdual_nonneg hy
    have hreal :
        y x - Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)) ≤
          -Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) := by
      linarith
    have hrealE :
        (((y x - Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) ≤
          (((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ)) : EReal) := by
      exact_mod_cast hreal
    simpa [sqrt_alpha_sq_add_norm_sq_function_apply, EReal.coe_sub] using hrealE
  · by_cases hy0 : dualNorm y = 0
    · -- At `‖y‖_* = 0`, the origin attains the exact value `-1`.
      refine le_sSup ?_
      refine ⟨0, ?_⟩
      change ((y 0 : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 0) =
        ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
      rw [sqrt_alpha_sq_add_norm_sq_function_apply, hy0, ← EReal.coe_sub]
      norm_num
    · by_cases hy1 : dualNorm y = 1
      · -- On the boundary, the ray values approach `0` from below.
        have hypos : 0 < dualNorm y := by
          linarith
        obtain ⟨u, hu_norm, hu_dual⟩ := exists_unitDualNormWitnessOfPos y hypos
        have hzero_lower :
            (0 : EReal) ≤
              sSup (Set.range fun x : E ↦
                (y x : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 x) := by
          by_contra hneg
          have hlt0 :
              sSup (Set.range fun x : E ↦
                (y x : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 x) < 0 :=
            lt_of_not_ge hneg
          rcases EReal.lt_iff_exists_real_btwn.1 hlt0 with ⟨r, hsup_lt_r, hr_lt0⟩
          have hr_lt0_real : r < 0 := by
            exact_mod_cast hr_lt0
          have hrpos : 0 < -r := by
            linarith
          obtain ⟨n, hn⟩ := exists_nat_gt ((-r)⁻¹)
          have hn_real : ((-r)⁻¹ : ℝ) < (n : ℝ) := by
            exact_mod_cast hn
          have hm_pos : 0 < (n : ℝ) := by
            exact lt_trans (by positivity) hn_real
          have hr_lt_neg_inv : r < -(1 / (n : ℝ)) := by
            have hrecip_lt : 1 / (n : ℝ) < -r := by
              simpa [one_div] using
                (one_div_lt_one_div_of_lt (show 0 < (-r)⁻¹ by positivity) hn_real)
            linarith
          have hsqrt_pos : 0 < Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) := by
            apply Real.sqrt_pos.2
            positivity
          have hden_gt :
              (n : ℝ) < (n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) := by
            linarith
          have hrecip_order :
              1 / ((n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ))) < 1 / (n : ℝ) := by
            exact one_div_lt_one_div_of_lt hm_pos hden_gt
          have hray_lower : r < (n : ℝ) - Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) := by
            have hneg_lt :
                -(1 / (n : ℝ)) <
                  -(1 / ((n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)))) := by
              simpa using (neg_lt_neg hrecip_order)
            calc
              r < -(1 / (n : ℝ)) := hr_lt_neg_inv
              _ < -(1 / ((n : ℝ) + Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)))) := hneg_lt
              _ = (n : ℝ) - Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) := (rayDifference_eq_negInv n).symm
          have hvalue :
              ((r : ℝ) : EReal) <
                ((y ((n : ℝ) • u) : EReal) -
                  sqrt_alpha_sq_add_norm_sq_function 1 ((n : ℝ) • u)) := by
            calc
              ((r : ℝ) : EReal) <
                  (((n : ℝ) - Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
                    exact_mod_cast hray_lower
              _ = ((y ((n : ℝ) • u) : EReal) -
                    sqrt_alpha_sq_add_norm_sq_function 1 ((n : ℝ) • u)) := by
                      simpa [hy1] using
                        (sqrtOneAddNormSqFunction_integrand_smul_unit
                          (E := E) y hu_norm hu_dual (n : ℝ)
                          (show 0 ≤ (n : ℝ) by positivity)).symm
          have hr_lt_sup :
              ((r : ℝ) : EReal) <
                sSup (Set.range fun x : E ↦
                  (y x : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 x) := by
            exact lt_of_lt_of_le hvalue (le_sSup ⟨(n : ℝ) • u, rfl⟩)
          exact (not_lt_of_ge (le_of_lt hr_lt_sup)) hsup_lt_r
        simpa [hy1] using hzero_lower
      · -- In the strict interior, the optimizer ray attains the scalar maximum exactly.
        have hy_lt : dualNorm y < 1 := lt_of_le_of_ne hy hy1
        have hyne0 : 0 ≠ dualNorm y := by
          intro h
          exact hy0 h.symm
        have hypos : 0 < dualNorm y := lt_of_le_of_ne hdual_nonneg hyne0
        obtain ⟨u, hu_norm, hu_dual⟩ := exists_unitDualNormWitnessOfPos y hypos
        let r : ℝ := dualNorm y / Real.sqrt (1 - dualNorm y ^ (2 : ℕ))
        have hr_nonneg : 0 ≤ r := by
          dsimp [r]
          positivity
        refine le_sSup ?_
        refine ⟨r • u, ?_⟩
        change ((y (r • u) : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 (r • u)) =
          ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
        calc
          ((y (r • u) : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 (r • u)) =
              (((r * dualNorm y - Real.sqrt (1 + r ^ (2 : ℕ)) : ℝ)) : EReal) :=
                sqrtOneAddNormSqFunction_integrand_smul_unit
                  (E := E) y hu_norm hu_dual r hr_nonneg
          _ = ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
                dsimp [r]
                exact_mod_cast (by
                  simpa [mul_comm] using
                    scalarSqrtObjective_eq_optimizer (dualNorm y) hdual_nonneg hy_lt)

/-- Helper for Proposition 4.21: outside the closed dual unit ball, the conjugate of
`x ↦ √(1 + ‖x‖²)` is `⊤`. -/
lemma sqrtOneAddNormSqFunction_conjugate_eq_top_of_one_lt_dualNorm
    (y : Module.Dual ℝ E) (hy : 1 < dualNorm y) :
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function (E := E) 1) y = ⊤ := by
  have hypos : 0 < dualNorm y := by
    linarith
  obtain ⟨u, hu_norm, hu_dual⟩ := exists_unitDualNormWitnessOfPos y hypos
  rw [conjugate_function_apply]
  refine (sSup_eq_top).2 ?_
  intro b hb
  rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
  let δ : ℝ := dualNorm y - 1
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((r + 1) / δ)
  have hn_real : (r + 1) / δ < (n : ℝ) := by
    exact_mod_cast hn
  have hr_lt :
      r < (n : ℝ) * (dualNorm y - 1) - 1 := by
    have hscaled : r + 1 < (n : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at hn_real
      simpa [mul_comm] using hn_real
    dsimp [δ] at hscaled
    linarith
  have hsqrt_le : Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) ≤ (n : ℝ) + 1 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · nlinarith
  refine ⟨_, Set.mem_range.mpr ⟨(n : ℝ) • u, rfl⟩, ?_⟩
  calc
    b < (r : EReal) := hbr
    _ < ((((n : ℝ) * (dualNorm y - 1) - 1 : ℝ)) : EReal) := by
          exact_mod_cast hr_lt
    _ = ((((n : ℝ) * dualNorm y - ((n : ℝ) + 1) : ℝ)) : EReal) := by
          congr 1
          ring
    _ ≤ (((n : ℝ) * dualNorm y - Real.sqrt (1 + (n : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
          exact_mod_cast
            (sub_le_sub_left hsqrt_le ((n : ℝ) * dualNorm y))
    _ = ((y ((n : ℝ) • u) : EReal) - sqrt_alpha_sq_add_norm_sq_function 1 ((n : ℝ) • u)) := by
          simpa using
            (sqrtOneAddNormSqFunction_integrand_smul_unit
              (E := E) y hu_norm hu_dual (n : ℝ) (show 0 ≤ (n : ℝ) by positivity)).symm

/-- Helper for Proposition 4.21: the unit profile `x ↦ √(1 + ‖x‖²)` has conjugate
`-√(1 - ‖y‖_*²)` on the dual unit ball and `∞` outside. -/
lemma sqrtOneAddNormSqFunction_conjugate_eq
    (y : Module.Dual ℝ E) :
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function (E := E) 1) y =
      if dualNorm y ≤ 1 then
        ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
      else ⊤ := by
  by_cases hy : dualNorm y ≤ 1
  · -- The closed-ball branch is the exact scalar optimizer formula.
    rw [if_pos hy]
    exact sqrtOneAddNormSqFunction_conjugate_eq_of_dualNorm_le_one (E := E) y hy
  · -- Outside the dual unit ball, the conjugate is unbounded along a dual-norm witness ray.
    rw [if_neg hy]
    exact sqrtOneAddNormSqFunction_conjugate_eq_top_of_one_lt_dualNorm (E := E) y (lt_of_not_ge hy)

-- Proof sketch: rewrite `g_α` as the positive scalar multiple
-- `x ↦ α * √(1 + ‖(1 / α) • x‖²)` and combine the scaling rule for Fenchel conjugates with the
-- unit-profile formula above. After simplifying the rescaled finite branch, the value on the dual
-- unit ball is `-α * √(1 - ‖y‖_*²)` and it is `∞` outside that ball.
/-- Proposition 4.21: for `α > 0`, the Fenchel conjugate of `g_α(x) = √(α² + ‖x‖²)` is
`-α √(1 - ‖y‖_*²)` on the dual unit ball and `∞` outside it, where `‖y‖_*` is `dualNorm y`. -/
theorem sqrt_alpha_sq_add_norm_sq_function_conjugate_eq
    (α : ℝ) (hα : 0 < α) (y : Module.Dual ℝ E) :
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function α) y =
      if dualNorm y ≤ 1 then
        ((-α * Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
      else ⊤ := by
  have hscale :
      sqrt_alpha_sq_add_norm_sq_function α =
        fun x : E ↦ (α : EReal) * sqrt_alpha_sq_add_norm_sq_function 1 ((1 / α) • x) := by
    -- Package the pointwise rescaling identity as a function equality before applying
    -- Proposition 4.7.
    funext x
    exact sqrt_alpha_sq_add_norm_sq_function_eq_pos_real_mul_precomp_inv_smul α hα x
  calc
    conjugate_function (sqrt_alpha_sq_add_norm_sq_function α) y =
        conjugate_function
          (fun x : E ↦ (α : EReal) * sqrt_alpha_sq_add_norm_sq_function 1 ((1 / α) • x)) y := by
            rw [hscale]
    _ = (α : EReal) *
          conjugate_function (sqrt_alpha_sq_add_norm_sq_function (E := E) 1) y := by
            simpa using
              congrFun
                (conjugate_function_pos_real_precomp_inv_smul
                  (sqrt_alpha_sq_add_norm_sq_function (E := E) 1) α hα) y
    _ = (α : EReal) *
          (if dualNorm y ≤ 1 then
            ((-Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
          else ⊤) := by
            rw [sqrtOneAddNormSqFunction_conjugate_eq (E := E)]
    _ = if dualNorm y ≤ 1 then
          ((-α * Real.sqrt (1 - dualNorm y ^ (2 : ℕ)) : ℝ) : EReal)
        else ⊤ := by
          by_cases hy : dualNorm y ≤ 1
          · -- On the finite branch, multiplication by the positive scalar `α` stays in `ℝ`.
            rw [if_pos hy, if_pos hy, ← EReal.coe_mul]
            congr 1
            ring
          · -- Outside the dual unit ball, positive `EReal` multiplication preserves `⊤`.
            rw [if_neg hy, if_neg hy, EReal.coe_mul_top_of_pos hα]

end
