/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 4.11 is `source-facing`: its primitive data is the scalar integrand
`negative_rpow_extension`. The chapter `core/canonical` owner for Fenchel conjugates is
`conjugate_function` from Definition 4.1, and its scalar `bridge/view` owner is the primal-space
notation `f∗`. The conjugacy formulas below therefore use that canonical scalar surface instead of
reintroducing an explicit `toDualMap ℝ ℝ` wrapper. -/
recall conjugate_function_primal

/-- The extended-real function equal to `-x^p / p` on the nonnegative ray and `∞` on the negative
half-line. -/
def negative_rpow_extension (p : ℝ) : ℝ → EReal :=
  fun x ↦ if 0 ≤ x then ((-(x ^ p) / p : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_rpow_extension`; on the nonnegative branch the `if` reduces to
-- the defining formula.
/-- On the nonnegative ray, `negative_rpow_extension p` is `-x^p / p`. -/
theorem negative_rpow_extension_of_nonneg
    (p x : ℝ) (hx : 0 ≤ x) :
    negative_rpow_extension p x = ((-(x ^ p) / p : ℝ) : EReal) := by
  simp [negative_rpow_extension, hx]

-- Proof sketch: unfold `negative_rpow_extension`; on the negative branch the function is `∞`.
/-- On the negative half-line, `negative_rpow_extension p` is `∞`. -/
theorem negative_rpow_extension_of_neg
    (p x : ℝ) (hx : x < 0) :
    negative_rpow_extension p x = ⊤ := by
  simp [negative_rpow_extension, not_le.mpr hx]

/-- Helper for Proposition 4.11: the conjugate-defining range for `negative_rpow_extension p`
splits into the `⊥` contribution from the negative half-line and the affine-power image of
`Set.Ici 0`. -/
lemma negativeRpowExtensionPairingRange_eq_insertBotImage
    (p y : ℝ) :
    Set.range
        (fun x : ℝ ↦ (((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) -
          negative_rpow_extension p x) =
      insert ⊥ ((fun x : ℝ ↦ ((x * y + x ^ p / p : ℝ) : EReal)) '' Set.Ici (0 : ℝ)) := by
  -- Compare the two sets pointwise, splitting the source variable by the sign of `x`.
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, rfl⟩
    by_cases hx : 0 ≤ x
    · right
      refine ⟨x, hx, ?_⟩
      -- On the nonnegative branch the extended-real term is the explicit affine-power objective.
      change (((x * y + x ^ p / p : ℝ) : EReal) =
        (((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) - negative_rpow_extension p x)
      rw [negative_rpow_extension_of_nonneg p x hx, ← EReal.coe_sub]
      congr 1
      have hinner' : inner ℝ y x = x * y := by
        rfl
      have hinner : inner ℝ y x = y * x := by
        simpa [mul_comm] using hinner'
      calc
        x * y + x ^ p / p = y * x + x ^ p * p⁻¹ := by ring
        _ = inner ℝ y x - -x ^ p / p := by
              rw [hinner]
              simp [div_eq_mul_inv]
    · left
      have hx' : x < 0 := lt_of_not_ge hx
      -- On the negative branch we subtract `⊤`, so the contribution is exactly `⊥`.
      simp [negative_rpow_extension, hx, InnerProductSpace.toDualMap_apply_apply]
  · intro hz
    rcases hz with rfl | hz
    · refine ⟨-1, ?_⟩
      have hneg : ¬ 0 ≤ (-1 : ℝ) := by
        norm_num
      -- Any negative witness maps to `⊥`; `x = -1` is a fixed convenient choice.
      simp [negative_rpow_extension, hneg, InnerProductSpace.toDualMap_apply_apply]
    · rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ?_⟩
      -- A point from the nonnegative ray already appears in the original range.
      change ((((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) - negative_rpow_extension p x =
        ((x * y + x ^ p / p : ℝ) : EReal))
      rw [negative_rpow_extension_of_nonneg p x hx, ← EReal.coe_sub]
      congr 1
      have hinner' : inner ℝ y x = x * y := by
        rfl
      have hinner : inner ℝ y x = y * x := by
        simpa [mul_comm] using hinner'
      calc
        inner ℝ y x - -x ^ p / p = y * x + x ^ p * p⁻¹ := by
              rw [hinner]
              simp [div_eq_mul_inv]
        _ = x * y + x ^ p / p := by ring

-- Proof sketch: unfold `negative_rpow_extension` inside the canonical Chapter 4 definition
-- `conjugate_function`. On `x < 0`, the value of `negative_rpow_extension p x` is `⊤`, so the term
-- `(x * y : EReal) - ⊤` is `⊥` and does not change the supremum. On `x ≥ 0`, the affine term is
-- `x * y + x ^ p / p`, so the supremum is taken over `Set.Ici 0`.
/-- Evaluating the scalar Fenchel conjugate `(negative_rpow_extension p)∗` at `y` reduces to the
supremum of `x * y + x ^ p / p` over the nonnegative ray. -/
theorem negative_rpow_extension_conjugate_eq_sSup_Ici
    (p y : ℝ) :
    (negative_rpow_extension p)∗ y =
      sSup ((fun x : ℝ ↦ ((x * y + x ^ p / p : ℝ) : EReal)) '' Set.Ici (0 : ℝ)) := by
  -- Unfold the canonical conjugate and take the supremum of the normalized range formula.
  simpa [conjugate_function_primal_apply, conjugate_function_apply, sSup_insert] using
    congrArg sSup (negativeRpowExtensionPairingRange_eq_insertBotImage p y)

/-- Helper for Proposition 4.11: when `y ≥ 0`, the objective `x * y + x ^ p / p` is cofinal in
`ℝ` along the nonnegative ray. -/
lemma negativeRpowObjectiveAboveAnyReal_of_nonneg
    (p y : ℝ) (hp0 : 0 < p) (hy0 : 0 ≤ y) :
    ∀ z : ℝ, ∃ x ∈ Set.Ici (0 : ℝ), z < x * y + x ^ p / p := by
  intro z
  by_cases hz : z < 0
  · refine ⟨0, by simp, ?_⟩
    -- At `x = 0`, the objective is `0`, which already beats any negative threshold.
    simpa [hp0.ne'] using hz
  · have hz0 : 0 ≤ z := le_of_not_gt hz
    let x : ℝ := (p * (z + 1)) ^ p⁻¹
    refine ⟨x, ?_, ?_⟩
    · -- The explicit witness lies on the nonnegative ray because its base is nonnegative.
      have hbase_nonneg : 0 ≤ p * (z + 1) := by
        positivity
      exact Real.rpow_nonneg hbase_nonneg _
    · have hbase_nonneg : 0 ≤ p * (z + 1) := by
        positivity
      have hxpow : x ^ p = p * (z + 1) := by
        -- The witness was chosen so that its `p`-power is exactly `p * (z + 1)`.
        dsimp [x]
        simpa [one_div] using Real.rpow_inv_rpow hbase_nonneg hp0.ne'
      have hx_nonneg : 0 ≤ x := Real.rpow_nonneg hbase_nonneg _
      have hxy_nonneg : 0 ≤ x * y := mul_nonneg hx_nonneg hy0
      have hxp_div : x ^ p / p = z + 1 := by
        rw [hxpow]
        field_simp [hp0.ne']
      have hz_lt_div : z < x ^ p / p := by
        rw [hxp_div]
        linarith
      have hdiv_le : x ^ p / p ≤ x * y + x ^ p / p := by
        linarith
      exact lt_of_lt_of_le hz_lt_div hdiv_le

/-- Helper for Proposition 4.11: the critical point
`x₀ = (-y) ^ (1 / (p - 1))` lies on `Set.Ici 0` and evaluates the objective to the claimed
closed form when `y < 0`. -/
lemma negativeRpowCriticalPoint_mem_and_eval
    (p y : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hy : y < 0) :
    let x0 := (-y) ^ (1 / (p - 1))
    x0 ∈ Set.Ici (0 : ℝ) ∧
      x0 * y + x0 ^ p / p = -((-y) ^ (p / (p - 1))) / (p / (p - 1)) := by
  let x0 := (-y) ^ (1 / (p - 1))
  have hpm1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne
  have hyneg : 0 < -y := by
    linarith
  have hx0_pos : 0 < x0 := by
    dsimp [x0]
    exact Real.rpow_pos_of_pos hyneg _
  have hx0_pow : x0 ^ (p - 1) = -y := by
    -- The critical point was chosen so its `(p - 1)`-power matches `-y`.
    dsimp [x0]
    simpa [one_div] using Real.rpow_inv_rpow hyneg.le hpm1
  have hx0_pow_p : x0 ^ p = (-y) ^ (p / (p - 1)) := by
    -- Re-express the critical point's `p`-power in the final exponent form.
    calc
      x0 ^ p = (((-y) ^ ((p - 1)⁻¹)) : ℝ) ^ p := by
        simp [x0, one_div]
      _ = (-y) ^ (((p - 1)⁻¹) * p) := by
        rw [← Real.rpow_mul hyneg.le]
      _ = (-y) ^ (p / (p - 1)) := by
        congr 1
        field_simp [hpm1]
  have hmul_x0 : x0 * x0 ^ (p - 1) = x0 ^ p := by
    -- The product `x0 * x0^(p-1)` collapses to `x0^p`.
    calc
      x0 * x0 ^ (p - 1) = x0 ^ (p - 1) * x0 := by ring
      _ = x0 ^ ((p - 1) + 1) := by rw [Real.rpow_add hx0_pos (p - 1) 1, Real.rpow_one]
      _ = x0 ^ p := by congr 1; ring
  refine ⟨hx0_pos.le, ?_⟩
  -- Evaluate the objective at the critical point by collapsing it to the closed form.
  calc
    x0 * y + x0 ^ p / p
        = x0 * (-(x0 ^ (p - 1))) + x0 ^ p / p := by
            rw [hx0_pow]
            ring
    _ = -(x0 ^ p) + x0 ^ p / p := by
          rw [show x0 * -(x0 ^ (p - 1)) = -(x0 * x0 ^ (p - 1)) by ring, hmul_x0]
    _ = x0 ^ p * (1 / p - 1) := by
          ring
    _ = (-y) ^ (p / (p - 1)) * (1 / p - 1) := by
          rw [hx0_pow_p]
    _ = -((-y) ^ (p / (p - 1))) / (p / (p - 1)) := by
          field_simp [hp0.ne', hpm1]
          ring

/-- Helper for Proposition 4.11: when `y < 0`, every point on the nonnegative ray lies below the
critical value `-((-y) ^ (p / (p - 1))) / (p / (p - 1))`. -/
lemma negativeRpowObjective_le_criticalValue_of_neg
    (p y x : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hy : y < 0) (hx : x ∈ Set.Ici (0 : ℝ)) :
    x * y + x ^ p / p ≤ -((-y) ^ (p / (p - 1))) / (p / (p - 1)) := by
  let x0 := (-y) ^ (1 / (p - 1))
  let a := x / x0
  have hpm1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne
  have hyneg : 0 < -y := by
    linarith
  have hx0_pos : 0 < x0 := by
    dsimp [x0]
    exact Real.rpow_pos_of_pos hyneg _
  have hx0_nonneg : 0 ≤ x0 := hx0_pos.le
  have hx0_pow : x0 ^ (p - 1) = -y := by
    -- The normalization point is defined by the critical-point equation.
    dsimp [x0]
    simpa [one_div] using Real.rpow_inv_rpow hyneg.le hpm1
  have hx0_pow_p : x0 ^ p = (-y) ^ (p / (p - 1)) := by
    calc
      x0 ^ p = (((-y) ^ ((p - 1)⁻¹)) : ℝ) ^ p := by
        simp [x0, one_div]
      _ = (-y) ^ (((p - 1)⁻¹) * p) := by
        rw [← Real.rpow_mul hyneg.le]
      _ = (-y) ^ (p / (p - 1)) := by
        congr 1
        field_simp [hpm1]
  have hx_eq : x = x0 * a := by
    dsimp [a]
    field_simp [hx0_pos.ne']
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hx hx0_nonneg
  have hpow_bound : a ^ p ≤ 1 + p * (a - 1) := by
    -- Bernoulli's inequality for `0 ≤ p ≤ 1` gives the tangent-line upper bound for `a ^ p`.
    have hs : -1 ≤ a - 1 := by
      linarith
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      rpow_one_add_le_one_add_mul_self (s := a - 1) hs hp0.le hp1.le
  have hx_rpow : x ^ p = x0 ^ p * a ^ p := by
    -- Rewrite `x` as `x0 * a` so the power factors cleanly.
    rw [hx_eq, Real.mul_rpow hx0_nonneg ha_nonneg]
  have hmul_x0 : x0 * x0 ^ (p - 1) = x0 ^ p := by
    -- The normalization point satisfies the same power-collapsing identity as in the witness lemma.
    calc
      x0 * x0 ^ (p - 1) = x0 ^ (p - 1) * x0 := by ring
      _ = x0 ^ ((p - 1) + 1) := by rw [Real.rpow_add hx0_pos (p - 1) 1, Real.rpow_one]
      _ = x0 ^ p := by congr 1; ring
  have hy_expr : y = -(x0 ^ (p - 1)) := by
    linarith [hx0_pow]
  have hcoeff :
      (1 + p * (a - 1)) / p - a = 1 / p - 1 := by
    field_simp [hp0.ne']
    ring
  have hmul_bound : x0 ^ p * (a ^ p / p - a) ≤ x0 ^ p * ((1 + p * (a - 1)) / p - a) := by
    have hdiv : a ^ p / p ≤ (1 + p * (a - 1)) / p := by
      exact div_le_div_of_nonneg_right hpow_bound hp0.le
    have hsub : a ^ p / p - a ≤ (1 + p * (a - 1)) / p - a := sub_le_sub_right hdiv a
    exact mul_le_mul_of_nonneg_left hsub (Real.rpow_nonneg hx0_nonneg _)
  calc
    x * y + x ^ p / p
        = x0 ^ p * (a ^ p / p - a) := by
            rw [hx_eq, hy_expr, Real.mul_rpow hx0_nonneg ha_nonneg]
            rw [show x0 * a * (-(x0 ^ (p - 1))) = -(x0 ^ p * a) by
              rw [show x0 * a * (-(x0 ^ (p - 1))) = -((x0 * a) * x0 ^ (p - 1)) by ring]
              rw [mul_assoc, mul_comm a, ← mul_assoc, hmul_x0]]
            ring
    _ ≤ x0 ^ p * ((1 + p * (a - 1)) / p - a) := hmul_bound
    _ = x0 ^ p * (1 / p - 1) := by rw [hcoeff]
    _ = (-y) ^ (p / (p - 1)) * (1 / p - 1) := by rw [hx0_pow_p]
    _ = -((-y) ^ (p / (p - 1))) / (p / (p - 1)) := by
          field_simp [hp0.ne', hpm1]
          ring

-- Proof sketch: start from `negative_rpow_extension_conjugate_eq_sSup_Ici`. For `0 < p < 1`, the
-- objective `x ↦ x * y + x ^ p / p` is concave on `[0, ∞)`. If `y < 0`, its derivative vanishes at
-- the unique maximizer `x = (-y) ^ (1 / (1 - p))`, and evaluating there gives
-- `-((-y) ^ (p / (p - 1))) / (p / (p - 1))`. If `y ≥ 0`, the objective tends to `∞` along
-- `x → ∞`, so the conjugate value is `⊤`.
/-- Proposition 4.11: for `0 < p < 1`, let `f(x) = -x^p / p` on `[0, ∞)` and `f(x) = ∞` on
`(-∞, 0)`. Then the scalar Fenchel conjugate `f∗` is
`-(-y)^q / q` for `y < 0` and `∞` otherwise, where `q = p / (p - 1) < 0`. -/
theorem negative_rpow_extension_conjugate_eq
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (y : ℝ) :
    (negative_rpow_extension p)∗ y =
      if y < 0 then ((-((-y) ^ (p / (p - 1))) / (p / (p - 1)) : ℝ) : EReal) else ⊤ := by
  rw [negative_rpow_extension_conjugate_eq_sSup_Ici]
  by_cases hy : y < 0
  · -- In the negative branch, the explicit critical point is the greatest point of the image set.
    have hcrit := negativeRpowCriticalPoint_mem_and_eval p y hp0 hp1 hy
    dsimp at hcrit
    rcases hcrit with ⟨hx0_mem, hx0_eval⟩
    let x0 : ℝ := (-y) ^ (1 / (p - 1))
    have hgreatest :
        IsGreatest
          ((fun x : ℝ ↦ ((x * y + x ^ p / p : ℝ) : EReal)) '' Set.Ici (0 : ℝ))
          (((-((-y) ^ (p / (p - 1))) / (p / (p - 1)) : ℝ) : EReal)) := by
      refine ⟨?_, ?_⟩
      · refine ⟨x0, hx0_mem, ?_⟩
        simpa [x0] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hx0_eval
      · intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        change (((x * y + x ^ p / p : ℝ) : EReal) ≤
          (((-((-y) ^ (p / (p - 1))) / (p / (p - 1)) : ℝ) : EReal)))
        exact_mod_cast negativeRpowObjective_le_criticalValue_of_neg p y x hp0 hp1 hy hx
    -- Replace the supremum by the value of its greatest element.
    simpa [hy] using hgreatest.csSup_eq
  · have hy0 : 0 ≤ y := by
      linarith
    have hsSup_top :
        sSup ((fun x : ℝ ↦ ((x * y + x ^ p / p : ℝ) : EReal)) '' Set.Ici (0 : ℝ)) = ⊤ := by
      rw [sSup_eq_top]
      intro b hb
      -- Reduce the extended-real threshold to a real one, then use the cofinality lemma.
      rcases EReal.lt_iff_exists_real_btwn.mp hb with ⟨z, hbz, hzt⟩
      rcases negativeRpowObjectiveAboveAnyReal_of_nonneg p y hp0 hy0 z with ⟨x, hx, hzx⟩
      refine ⟨((x * y + x ^ p / p : ℝ) : EReal), ⟨x, hx, rfl⟩, ?_⟩
      exact hbz.trans <| by exact_mod_cast hzx
    -- The objective is unbounded above for `y ≥ 0`, so the conjugate value is `⊤`.
    simpa [hy] using hsSup_top
