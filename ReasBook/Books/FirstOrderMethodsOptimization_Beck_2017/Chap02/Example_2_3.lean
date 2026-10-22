/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The Example 2.3 family takes the value `α` at `0`, agrees with the identity on `(0, 1]`, and
is `∞` elsewhere. -/
def truncated_identity_with_origin_value (α : ℝ) : ℝ → EReal :=
  fun x ↦ (δ_ (Set.Icc (0 : ℝ) 1)) x + if x = 0 then (α : EReal) else x

/-- Evaluating `truncated_identity_with_origin_value α` gives the textbook piecewise formula:
inside `[0, 1]` the value is `α` at `0` and `x` on `(0, 1]`, while outside `[0, 1]` the value is
`∞`. -/
theorem truncated_identity_with_origin_value_apply (α x : ℝ) :
    truncated_identity_with_origin_value α x =
      if x ∈ Set.Icc (0 : ℝ) 1 then if x = 0 then (α : EReal) else x else ⊤ := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp [truncated_identity_with_origin_value, hx]
  · have hbranch : (if x = 0 then (α : EReal) else x) ≠ ⊥ := by
      by_cases h0 : x = 0 <;> simp [h0]
    simp [truncated_identity_with_origin_value, hx, EReal.top_add_of_ne_bot hbranch]

/-- At the origin, `truncated_identity_with_origin_value α` takes the prescribed value `α`. -/
@[simp] theorem truncated_identity_with_origin_value_zero (α : ℝ) :
    truncated_identity_with_origin_value α 0 = α := by
  simp [truncated_identity_with_origin_value_apply]

/-- On the open interval `(0, 1]`, `truncated_identity_with_origin_value α` agrees with the
identity. -/
theorem truncated_identity_with_origin_value_of_mem_Ioc {α x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    truncated_identity_with_origin_value α x = x := by
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
  rw [truncated_identity_with_origin_value_apply]
  simp [hx', hx.1.ne']

/-- Outside `[0, 1]`, `truncated_identity_with_origin_value α` takes the value `∞`. -/
theorem truncated_identity_with_origin_value_of_not_mem_Icc {α x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    truncated_identity_with_origin_value α x = ⊤ := by
  rw [truncated_identity_with_origin_value_apply]
  simp [hx]

-- Proof sketch: unfold `truncated_identity_with_origin_value` and `effective_domain`, then split
-- into the cases `x = 0`, `0 < x ∧ x ≤ 1`, and the complement. The value at `0` is finite because
-- `α : ℝ`, so the finite-value locus is exactly the interval `[0, 1]`.
/-- The effective domain of `truncated_identity_with_origin_value α` is exactly the interval
`[0, 1]`. -/
theorem truncated_identity_with_origin_value_effective_domain_eq (α : ℝ) :
    effective_domain (truncated_identity_with_origin_value α) = Set.Icc (0 : ℝ) 1 := by
  ext x
  rw [mem_effective_domain, truncated_identity_with_origin_value_apply]
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · by_cases h0 : x = 0 <;> simp [hx, h0]
  · simp [hx]

/-- A real number lies in the effective domain of `truncated_identity_with_origin_value α`
exactly when it belongs to `[0, 1]`. -/
@[simp] theorem mem_effective_domain_truncated_identity_with_origin_value {α x : ℝ} :
    x ∈ effective_domain (truncated_identity_with_origin_value α) ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [truncated_identity_with_origin_value_effective_domain_eq]

/-- Helper for Example 2.3: for a negative threshold, the only possible point in the sublevel set
is the origin. -/
theorem preimage_Iic_truncated_identity_with_origin_value_of_lt_zero {α y : ℝ}
    (hy : y < 0) :
    (truncated_identity_with_origin_value α) ⁻¹' Set.Iic (y : EReal) =
      if α ≤ y then ({0} : Set ℝ) else ∅ := by
  ext x
  by_cases h0 : x = 0
  · -- At the origin the sublevel condition reduces to the scalar comparison `α ≤ y`.
    subst x
    by_cases hαy : α ≤ y
    · simp [truncated_identity_with_origin_value_zero, hαy]
    · simp [truncated_identity_with_origin_value_zero, hαy]
  · -- Away from the origin, all function values are either positive reals or `∞`.
    have hnotmem :
        x ∉ (truncated_identity_with_origin_value α) ⁻¹' Set.Iic (y : EReal) := by
      intro hx
      rw [Set.mem_preimage, Set.mem_Iic] at hx
      by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
      · have h0' : (0 : ℝ) ≠ x := by
          simpa [eq_comm] using h0
        have hx0 : 0 < x := lt_of_le_of_ne hxIcc.1 h0'
        have hxy : x ≤ y := by
          have hxyEReal : (x : EReal) ≤ (y : EReal) := by
            simpa [truncated_identity_with_origin_value_apply, hxIcc, h0] using hx
          exact_mod_cast hxyEReal
        linarith
      · have hfalse : False := by
          simp [truncated_identity_with_origin_value_apply, hxIcc] at hx
        exact False.elim hfalse
    by_cases hαy : α ≤ y
    · simp [h0, hαy, hnotmem]
    · simp [hαy, hnotmem]

/-- Helper for Example 2.3: a nonnegative threshold below both `α` and `1` cuts out the open-right
interval `(0, y]`. -/
theorem preimage_Iic_truncated_identity_with_origin_value_of_nonneg_lt {α y : ℝ}
    (_hy0 : 0 ≤ y) (hyα : y < α) (hy1 : y ≤ 1) :
    (truncated_identity_with_origin_value α) ⁻¹' Set.Iic (y : EReal) = Set.Ioc (0 : ℝ) y := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage, Set.mem_Iic] at hx
    by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
    · by_cases h0 : x = 0
      · have hαle : α ≤ y := by
          simpa [truncated_identity_with_origin_value_apply, hxIcc, h0] using hx
        have hfalse : False := (not_le_of_gt hyα) hαle
        exact False.elim hfalse
      · have h0' : (0 : ℝ) ≠ x := by
          simpa [eq_comm] using h0
        have hx0 : 0 < x := lt_of_le_of_ne hxIcc.1 h0'
        have hxy : x ≤ y := by
          have hxyEReal : (x : EReal) ≤ (y : EReal) := by
            simpa [truncated_identity_with_origin_value_apply, hxIcc, h0] using hx
          exact_mod_cast hxyEReal
        exact ⟨hx0, hxy⟩
    · have hfalse : False := by
        simp [truncated_identity_with_origin_value_apply, hxIcc] at hx
      exact False.elim hfalse
  · intro hx
    rw [Set.mem_preimage, Set.mem_Iic]
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 hy1⟩
    have hxyEReal : (x : EReal) ≤ (y : EReal) := by
      exact_mod_cast hx.2
    simpa [truncated_identity_with_origin_value_of_mem_Ioc hxIoc] using hxyEReal

/-- Helper for Example 2.3: once `α ≤ 0`, every nonnegative sublevel set is the closed interval
`[0, min y 1]`. -/
theorem preimage_Iic_truncated_identity_with_origin_value_of_nonneg {α y : ℝ}
    (hα : α ≤ 0) (hy0 : 0 ≤ y) :
    (truncated_identity_with_origin_value α) ⁻¹' Set.Iic (y : EReal) =
      Set.Icc (0 : ℝ) (min y 1) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage, Set.mem_Iic] at hx
    by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
    · by_cases h0 : x = 0
      · subst x
        have h01 : (0 : ℝ) ≤ 1 := by
          norm_num
        have hmin : 0 ≤ min y 1 := le_min hy0 h01
        simp [hmin]
      · have h0' : (0 : ℝ) ≠ x := by
          simpa [eq_comm] using h0
        have hx0 : 0 < x := lt_of_le_of_ne hxIcc.1 h0'
        have hxy : x ≤ y := by
          have hxyEReal : (x : EReal) ≤ (y : EReal) := by
            simpa [truncated_identity_with_origin_value_apply, hxIcc, h0] using hx
          exact_mod_cast hxyEReal
        exact ⟨le_of_lt hx0, le_min hxy hxIcc.2⟩
    · have hfalse : False := by
        simp [truncated_identity_with_origin_value_apply, hxIcc] at hx
      exact False.elim hfalse
  · intro hx
    rw [Set.mem_preimage, Set.mem_Iic]
    by_cases h0 : x = 0
    · subst x
      have hαy : α ≤ y := le_trans hα hy0
      rw [truncated_identity_with_origin_value_zero]
      exact_mod_cast hαy
    · have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
        have h0' : (0 : ℝ) ≠ x := by
          simpa [eq_comm] using h0
        have hx0 : 0 < x := lt_of_le_of_ne hx.1 h0'
        have hx1 : x ≤ 1 := le_trans hx.2 (min_le_right y 1)
        exact ⟨hx0, hx1⟩
      have hxyEReal : (x : EReal) ≤ (y : EReal) := by
        have hxy : x ≤ y := le_trans hx.2 (min_le_left y 1)
        exact_mod_cast hxy
      simpa [truncated_identity_with_origin_value_of_mem_Ioc hxIoc] using hxyEReal

/-- Helper for Example 2.3: on `[0, 1]`, the example coincides with the identity updated at the
origin. -/
theorem eqOn_truncated_identity_with_origin_value_update_Icc (α : ℝ) :
    Set.EqOn (truncated_identity_with_origin_value α)
      (Function.update (fun x : ℝ ↦ (x : EReal)) 0 α) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases h0 : x = 0
  · -- At the origin, both presentations return the prescribed value `α`.
    subst x
    simp [truncated_identity_with_origin_value_zero]
  · -- Away from the origin inside the interval, both presentations agree with the identity.
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
      have h0' : (0 : ℝ) ≠ x := by
        simpa [eq_comm] using h0
      have hx0 : 0 < x := lt_of_le_of_ne hx.1 h0'
      exact ⟨hx0, hx.2⟩
    simp [Function.update, h0, truncated_identity_with_origin_value_of_mem_Ioc hxIoc]

/-- Helper for Example 2.3: the right-hand limit of the identity on `(0, 1]` is uniquely `0`. -/
theorem tendsto_update_identity_right_interval_iff (α : ℝ) :
    Filter.Tendsto (fun x : ℝ ↦ (x : EReal)) (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1))
      (nhds (α : EReal)) ↔ α = 0 := by
  have hzeroReal :
      Filter.Tendsto (fun x : ℝ ↦ x) (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) (nhds (0 : ℝ)) :=
    continuousWithinAt_id.tendsto
  have hzero :
      Filter.Tendsto (fun x : ℝ ↦ (x : EReal)) (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1))
        (nhds (0 : EReal)) :=
    (continuous_coe_real_ereal.tendsto (0 : ℝ)).comp hzeroReal
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  have hneBot : Filter.NeBot (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) := left_nhdsWithin_Ioc_neBot h01
  constructor
  · intro hα
    have hEq : (0 : EReal) = (α : EReal) := tendsto_nhds_unique hzero hα
    exact_mod_cast hEq.symm
  · intro hα
    simpa [hα] using hzero

-- Proof sketch: the function is continuous on each branch away from `0`. At the origin, the only
-- possible failure of lower semicontinuity comes from approaching through positive points in the
-- domain, where the values converge to `0`, so the lower-semicontinuity condition is exactly
-- `α ≤ 0`.
/-- Example 2.3: the function `truncated_identity_with_origin_value α` is closed, equivalently
lower semicontinuous, if and only if `α ≤ 0`. -/
theorem truncated_identity_with_origin_value_lowerSemicontinuous_iff (α : ℝ) :
    LowerSemicontinuous (truncated_identity_with_origin_value α) ↔ α ≤ 0 := by
  constructor
  · intro h
    -- A positive origin value would create a nonclosed sublevel set `(0, y]`.
    by_contra hα
    have hαpos : 0 < α := lt_of_not_ge hα
    let y : ℝ := min (α / 2) (1 / 2)
    have hy0 : 0 ≤ y := by
      dsimp [y]
      refine le_min ?_ ?_
      · linarith
      · norm_num
    have hyα : y < α := by
      have hhalf_lt : α / 2 < α := by
        linarith
      dsimp [y]
      exact lt_of_le_of_lt (min_le_left (α / 2) ((1 : ℝ) / 2)) hhalf_lt
    have hy1 : y ≤ 1 := by
      dsimp [y]
      have hhalf : (1 : ℝ) / 2 ≤ 1 := by norm_num
      exact le_trans (min_le_right (α / 2) ((1 : ℝ) / 2)) hhalf
    have hclosed :
        IsClosed ((truncated_identity_with_origin_value α) ⁻¹' Set.Iic (y : EReal)) :=
      (lowerSemicontinuous_iff_isClosed_preimage (f := truncated_identity_with_origin_value α)).1 h
        (y : EReal)
    rw [preimage_Iic_truncated_identity_with_origin_value_of_nonneg_lt hy0 hyα hy1] at hclosed
    have hy_le_zero : y ≤ 0 := (isClosed_Ioc_iff.1 hclosed)
    have hy_pos : 0 < y := by
      dsimp [y]
      refine lt_min ?_ ?_
      · linarith
      · norm_num
    linarith
  · intro hα
    -- Check the closed-sublevel characterization threshold by threshold.
    refine
      (lowerSemicontinuous_iff_isClosed_preimage (f := truncated_identity_with_origin_value α)).2 ?_
    refine EReal.rec ?_ (fun y ↦ ?_) ?_
    · have hbot :
          (truncated_identity_with_origin_value α) ⁻¹' Set.Iic (⊥ : EReal) = (∅ : Set ℝ) := by
        ext x
        rw [Set.mem_preimage, Set.mem_Iic]
        by_cases hxIcc : x ∈ Set.Icc (0 : ℝ) 1
        · by_cases h0 : x = 0
          · simp [truncated_identity_with_origin_value_apply, h0]
          · simp [truncated_identity_with_origin_value_apply, hxIcc, h0]
        · simp [truncated_identity_with_origin_value_apply, hxIcc]
      rw [hbot]
      exact isClosed_empty
    · by_cases hy : y < 0
      · rw [preimage_Iic_truncated_identity_with_origin_value_of_lt_zero hy]
        by_cases hαy : α ≤ y
        · simp [hαy]
        · simp [hαy]
      · have hy0 : 0 ≤ y := le_of_not_gt hy
        rw [preimage_Iic_truncated_identity_with_origin_value_of_nonneg hα hy0]
        exact isClosed_Icc
    · simp

-- Proof sketch: use `truncated_identity_with_origin_value_effective_domain_eq` to identify the
-- effective domain with `[0, 1]`. Relative continuity is automatic away from `0`, and at `0` the
-- right-hand limit along the domain is `0`, so continuity on the effective domain holds exactly
-- when the value assigned at `0` is also `0`.
/-- The Example 2.3 family is continuous on its effective domain exactly when the origin value is
`0`. -/
theorem truncated_identity_with_origin_value_continuousOn_effective_domain_iff (α : ℝ) :
    ContinuousOn (truncated_identity_with_origin_value α)
      (effective_domain (truncated_identity_with_origin_value α)) ↔ α = 0 := by
  rw [truncated_identity_with_origin_value_effective_domain_eq]
  constructor
  · intro hcont
    -- Replace the domain-restricted function by the `update` form that isolates the origin.
    have hupdate :
        ContinuousOn (Function.update (fun x : ℝ ↦ (x : EReal)) 0 α) (Set.Icc (0 : ℝ) 1) :=
      ContinuousOn.congr hcont (eqOn_truncated_identity_with_origin_value_update_Icc α).symm
    rw [continuousOn_update_iff, Set.Icc_diff_left] at hupdate
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    exact (tendsto_update_identity_right_interval_iff α).1 (hupdate.2 hmem)
  · intro hα
    -- When `α = 0`, the update becomes the identity, which is continuous on the interval.
    have hcontUpdate :
        ContinuousOn (Function.update (fun x : ℝ ↦ (x : EReal)) 0 α) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_update_iff, Set.Icc_diff_left]
      constructor
      · exact continuous_coe_real_ereal.continuousOn
      · intro hmem
        exact (tendsto_update_identity_right_interval_iff α).2 hα
    exact ContinuousOn.congr hcontUpdate (eqOn_truncated_identity_with_origin_value_update_Icc α)

-- Proof sketch: combine
-- `truncated_identity_with_origin_value_lowerSemicontinuous_iff` and
-- `truncated_identity_with_origin_value_continuousOn_effective_domain_iff` at `α = -1 / 10`.
/-- The parameter choice `α = -1 / 10` gives a closed function that is not continuous on its
effective domain. -/
theorem truncated_identity_with_origin_value_neg_tenth_closed_not_continuousOn_effective_domain :
    LowerSemicontinuous (truncated_identity_with_origin_value (-(1 : ℝ) / 10)) ∧
      ¬ ContinuousOn (truncated_identity_with_origin_value (-(1 : ℝ) / 10))
        (effective_domain (truncated_identity_with_origin_value (-(1 : ℝ) / 10))) := by
  constructor
  · refine (truncated_identity_with_origin_value_lowerSemicontinuous_iff (-(1 : ℝ) / 10)).2 ?_
    norm_num
  · intro hcont
    have hα :
        (-(1 : ℝ) / 10 : ℝ) = 0 :=
      (truncated_identity_with_origin_value_continuousOn_effective_domain_iff
        (-(1 : ℝ) / 10)).1 hcont
    norm_num at hα

end
