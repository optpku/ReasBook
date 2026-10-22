/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Corollary_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Set Filter EuclideanGeometry

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

recall IsProperExtendedRealFunction
recall is_convex_function
recall proximal_objective
recall mem_proximal_mapping_iff

/- Theorem 6.3 is `source-facing` for the chapter's proximal-operator API. The domain is convex
analysis for extended-real-valued functions on a proper real inner product space. The owner
sampling in the minimal semantic closure is:

- `IsProperExtendedRealFunction` from Definition 2.5 for properness,
- `is_convex_function` from Definition 2.6 for convexity,
- `proximal_objective` and the set-valued owner `prox[f]` from Definition 6.1,
- the `[ProperSpace E]` ambient existence owner already used upstream in Theorem 6.4.

Accordingly, this file should not duplicate local definitions of effective domain, properness,
convexity, or the proximal objective. The public statement is the textbook singleton claim for the
proximal set itself, while the minimizer predicate `IsMinOn` remains the canonical derived view via
`mem_proximal_mapping_iff`. -/

-- Proof sketch: on a proper real inner product space, the quadratic penalty in
-- `proximal_objective f x` is closed, coercive, and `1`-strongly convex. Theorem 6.4 gives
-- existence of a proximal minimizer, and strict convexity of the quadratic term makes that
-- minimizer unique after adding the proper closed convex function `f`. Rewriting with
-- `mem_proximal_mapping_iff` identifies the proximal set with the singleton containing that
-- minimizer.
/-- Helper for Theorem 6.3: if `f` is lower semicontinuous, then adding the continuous quadratic
penalty preserves lower semicontinuity of the proximal objective. -/
private theorem lowerSemicontinuous_proximal_objective
    {f : E → EReal} (hf_closed : LowerSemicontinuous f) (x : E) :
    LowerSemicontinuous (proximal_objective f x) := by
  -- The quadratic penalty is continuous as a real-valued function, hence lower semicontinuous
  -- after coercion to `EReal`.
  have hpenalty_closed : LowerSemicontinuous
      (fun u : E ↦ ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal)) :=
    continuous_real_isClosed (by fun_prop)
  -- The proximal objective is the sum of `f` and that finite continuous penalty.
  simpa only [proximal_objective_apply] using
    hf_closed.add' hpenalty_closed <| fun u ↦
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))

/-- Helper for Theorem 6.3: for a proper convex function, the proximal objective at any base point
is coercive because the quadratic term dominates the affine lower support of `f` at a relative-
interior point of its effective domain. -/
theorem proximal_objective_coercive_of_proper_convex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x : E) :
    IsCoerciveExtendedRealFunction (proximal_objective f x) := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  rcases (intrinsicInterior_nonempty (effective_domain_convex_of_is_convex_function hf_convex)).2
      hf_proper.effective_domain_nonempty with ⟨u0, hu0ri⟩
  have hu0_eff : u0 ∈ effective_domain f := intrinsicInterior_subset hu0ri
  rcases subdifferential_nonempty_at_relativeInterior_point f u0 hf_convex hu0ri with ⟨g0, hg0⟩
  let g0c : StrongDual ℝ E := LinearMap.toContinuousLinearMap g0
  refine
    { ne_bot := ?_, effective_domain_nonempty := ?_, tendsto_top := ?_ }
  · intro u
    -- The quadratic penalty is finite, so the proximal objective inherits `f`'s exclusion of `⊥`.
    rw [proximal_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hf_proper.ne_bot u, EReal.coe_ne_bot _⟩
  · refine hf_proper.effective_domain_nonempty.mono ?_
    intro u hu
    -- Any finite point of `f` stays finite after adding the quadratic penalty.
    rw [mem_effective_domain] at hu ⊢
    simpa [proximal_objective_apply] using
      EReal.add_lt_top hu.ne (EReal.coe_ne_top _)
  · rw [EReal.tendsto_nhds_top_iff_real]
    intro b
    have hg0' := (mem_subdifferential.mp hg0).2
    let c : ℝ := (f u0).toReal - ‖g0c‖ * ‖u0‖ - (‖x‖ + ‖g0c‖) ^ (2 : ℕ)
    have hlower : ∀ u : E,
        (((1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) + c : ℝ) : EReal) ≤ proximal_objective f x u := by
      intro u
      -- The subgradient inequality gives an affine lower support for `f`.
      have hsubgrad : f u0 + (g0 u - g0 u0 : EReal) ≤ f u := by
        simpa [LinearMap.map_sub] using hg0' u
      have hlinear : -(‖g0c‖ * (‖u‖ + ‖u0‖)) ≤ g0 u - g0 u0 := by
        have hop : ‖g0c (u - u0)‖ ≤ ‖g0c‖ * ‖u - u0‖ := g0c.le_opNorm (u - u0)
        have htri : ‖u - u0‖ ≤ ‖u‖ + ‖u0‖ := by
          simpa [sub_eq_add_neg, add_comm] using norm_sub_le u u0
        have hleft : -(‖g0c‖ * ‖u - u0‖) ≤ g0c (u - u0) :=
          neg_le_of_abs_le hop
        have hmul : ‖g0c‖ * ‖u - u0‖ ≤ ‖g0c‖ * (‖u‖ + ‖u0‖) :=
          mul_le_mul_of_nonneg_left htri (norm_nonneg _)
        calc
          -(‖g0c‖ * (‖u‖ + ‖u0‖)) ≤ -(‖g0c‖ * ‖u - u0‖) := by nlinarith
          _ ≤ g0c (u - u0) := hleft
          _ = g0 u - g0 u0 := by simp [g0c, LinearMap.map_sub]
      -- The quadratic penalty controls the translation by `x`.
      have hquad : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≥
          (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - ‖x‖ * ‖u‖ := by
        have hnorm := norm_sub_sq_real u x
        nlinarith [real_inner_le_norm u x]
      -- Absorb the remaining linear term into a quarter of the quadratic growth.
      have habsorb : (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) - (‖x‖ + ‖g0c‖) ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (‖x‖ + ‖g0c‖) * ‖u‖ := by
        nlinarith [sq_nonneg (‖u‖ / 2 - (‖x‖ + ‖g0c‖))]
      have habsorb' :
          (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) + c ≤
            (f u0).toReal - ‖g0c‖ * ‖u0‖ +
              ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (‖x‖ + ‖g0c‖) * ‖u‖) := by
        dsimp [c]
        nlinarith [habsorb]
      have hrough :
          (f u0).toReal - ‖g0c‖ * ‖u0‖ +
              ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (‖x‖ + ‖g0c‖) * ‖u‖) ≤
            (f u0).toReal + (g0 u - g0 u0) + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
        nlinarith [hlinear, hquad]
      calc
        (((1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) + c : ℝ) : EReal)
            ≤ ((((f u0).toReal - ‖g0c‖ * ‖u0‖) +
                ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - (‖x‖ + ‖g0c‖) * ‖u‖) : ℝ) : EReal) := by
              exact_mod_cast habsorb'
        _ ≤ ((((f u0).toReal : ℝ) + (g0 u - g0 u0) +
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
              exact_mod_cast hrough
        _ = f u0 + ((g0 u - g0 u0 : ℝ) : EReal) +
            ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
              simp [EReal.coe_toReal (mem_effective_domain.mp hu0_eff).ne (hf_proper.ne_bot u0),
                add_assoc]
        _ ≤ f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hsubgrad
                  ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal)
        _ = proximal_objective f x u := by
              simp [proximal_objective_apply]
    have hquad_tendsto :
        Tendsto (fun u : E ↦ (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) + c) (comap norm atTop) atTop := by
      have hpow : Tendsto (fun r : ℝ ↦ (1 / 4 : ℝ) * r ^ (2 : ℕ)) atTop atTop := by
        exact Filter.tendsto_const_mul_pow_atTop (n := 2) (by norm_num) (by norm_num)
      have hpowc : Tendsto (fun r : ℝ ↦ (1 / 4 : ℝ) * r ^ (2 : ℕ) + c) atTop atTop := by
        simpa using tendsto_atTop_add_const_right atTop c hpow
      exact hpowc.comp
        (Filter.tendsto_comap : Tendsto norm (comap norm atTop) atTop)
    filter_upwards [hquad_tendsto.eventually_gt_atTop b] with u hu
    exact lt_of_lt_of_le
      (show (b : EReal) < (((1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) + c : ℝ) : EReal) by
        exact_mod_cast hu)
      (hlower u)
/-- Helper for Theorem 6.3: two proximal points at the same base point must coincide, because the
quadratic penalty strictly improves at the midpoint unless the points are equal. -/
theorem eq_of_mem_proximal_mapping_of_mem_proximal_mapping
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x y z : E)
    (hy : y ∈ prox[f] x) (hz : z ∈ prox[f] x) : y = z := by
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy hz
  rcases hf_proper.effective_domain_nonempty with ⟨u0, hu0_eff⟩
  have hy_eff : y ∈ effective_domain f := by
    -- Compare the minimizing value at `y` with one finite comparison point in the domain of `f`.
    have hy_obj : proximal_objective f x y ≤ proximal_objective f x u0 := hy u0
    have hu0_obj_top : proximal_objective f x u0 < ⊤ := by
      simpa [proximal_objective_apply] using
        EReal.add_lt_top (mem_effective_domain.mp hu0_eff).ne (EReal.coe_ne_top _)
    have hy_top' : proximal_objective f x y < ⊤ := lt_of_le_of_lt hy_obj hu0_obj_top
    have hy_top : f y ≠ ⊤ := by
      intro hfy
      have hobj_top : proximal_objective f x y = ⊤ := by
        rw [proximal_objective_apply, hfy, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [hobj_top] at hy_top'
      simp at hy_top'
    exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hy_top)
  have hz_eff : z ∈ effective_domain f := by
    -- The same finiteness argument applies to `z`.
    have hz_obj : proximal_objective f x z ≤ proximal_objective f x u0 := hz u0
    have hu0_obj_top : proximal_objective f x u0 < ⊤ := by
      simpa [proximal_objective_apply] using
        EReal.add_lt_top (mem_effective_domain.mp hu0_eff).ne (EReal.coe_ne_top _)
    have hz_top' : proximal_objective f x z < ⊤ := lt_of_le_of_lt hz_obj hu0_obj_top
    have hz_top : f z ≠ ⊤ := by
      intro hfz
      have hobj_top : proximal_objective f x z = ⊤ := by
        rw [proximal_objective_apply, hfz, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [hobj_top] at hz_top'
      simp at hz_top'
    exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hz_top)
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  have hm_eq : midpoint ℝ y z = (1 / 2 : ℝ) • y + (1 - (1 / 2 : ℝ)) • z := by
    calc
      midpoint ℝ y z = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z := by
        simpa [smul_add] using midpoint_eq_smul_add ℝ y z
      _ = (1 / 2 : ℝ) • y + (1 - (1 / 2 : ℝ)) • z := by
        congr 1
        ring
  have hm_eff : midpoint ℝ y z ∈ effective_domain f := by
    -- Convexity keeps the midpoint inside the effective domain.
    simpa [hm_eq] using
      combo_mem_effective_domain_of_is_convex_function hf_convex hy_eff hz_eff hhalf
  have hhalfE : (1 - ((1 / 2 : ℝ) : EReal)) = ((1 / 2 : ℝ) : EReal) := by
    exact_mod_cast (by norm_num : (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ))
  have hmid_conv :
      f (midpoint ℝ y z) ≤
        (((1 / 2 : ℝ) : EReal) * f y + (((1 / 2 : ℝ) : EReal) * f z)) := by
    -- The convexity inequality for `f` at the midpoint is the only nonlinear input.
    have hconv_mid :=
      (is_convex_function_iff_segment_ineq.mp hf_convex) y hy_eff z hz_eff hhalf
    calc
      f (midpoint ℝ y z) = f ((1 / 2 : ℝ) • y + (1 - (1 / 2 : ℝ)) • z) := by
        rw [hm_eq]
      _ ≤ (((1 / 2 : ℝ) : EReal) * f y + (1 - ((1 / 2 : ℝ) : EReal)) * f z) := hconv_mid
      _ = (((1 / 2 : ℝ) : EReal) * f y + (((1 / 2 : ℝ) : EReal) * f z)) := by
        rw [hhalfE]
  let py : ℝ := (f y).toReal + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)
  let pz : ℝ := (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)
  let pm : ℝ := (f (midpoint ℝ y z)).toReal + (1 / 2 : ℝ) * ‖midpoint ℝ y z - x‖ ^ (2 : ℕ)
  have hpy : proximal_objective f x y = (py : EReal) := by
    simp [py, proximal_objective_apply,
      EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)]
  have hpz : proximal_objective f x z = (pz : EReal) := by
    simp [pz, proximal_objective_apply,
      EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)]
  have hpm : proximal_objective f x (midpoint ℝ y z) = (pm : EReal) := by
    simp [pm, proximal_objective_apply,
      EReal.coe_toReal (mem_effective_domain.mp hm_eff).ne (hf_proper.ne_bot _)]
  have hy_le_pm : py ≤ pm := by
    -- Both `y` and `z` minimize the same proximal objective, so each is no larger than the
    -- midpoint value.
    have htmp := hy (midpoint ℝ y z)
    rw [hpy, hpm] at htmp
    exact EReal.coe_le_coe_iff.mp htmp
  have hz_le_pm : pz ≤ pm := by
    have htmp := hz (midpoint ℝ y z)
    rw [hpz, hpm] at htmp
    exact EReal.coe_le_coe_iff.mp htmp
  have hpy_le_pz : py ≤ pz := by
    have htmp := hy z
    rw [hpy, hpz] at htmp
    exact EReal.coe_le_coe_iff.mp htmp
  have hpz_le_py : pz ≤ py := by
    have htmp := hz y
    rw [hpz, hpy] at htmp
    exact EReal.coe_le_coe_iff.mp htmp
  have hpy_eq_pz : py = pz := le_antisymm hpy_le_pz hpz_le_py
  have hy_val : f y = (((f y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
  have hz_val : f z = (((f z).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
  have hmid_real : (f (midpoint ℝ y z)).toReal ≤ ((f y).toReal + (f z).toReal) / 2 := by
    -- Convert the convexity inequality to an ordinary real inequality on the finite values.
    have htmp : f (midpoint ℝ y z) ≤ ((((f y).toReal + (f z).toReal) / 2 : ℝ) : EReal) := by
      calc
        f (midpoint ℝ y z)
            ≤ (((1 / 2 : ℝ) : EReal) * f y + (((1 / 2 : ℝ) : EReal) * f z)) := hmid_conv
        _ = ((((f y).toReal + (f z).toReal) / 2 : ℝ) : EReal) := by
            have hreal :
                (1 / 2 : ℝ) * (f y).toReal + (1 / 2 : ℝ) * (f z).toReal =
                  (((f y).toReal + (f z).toReal) / 2 : ℝ) := by
              ring
            rw [hy_val, hz_val]
            exact_mod_cast hreal
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [EReal.coe_toReal (mem_effective_domain.mp hm_eff).ne (hf_proper.ne_bot _)] using htmp
  have hmid_quad : (1 / 2 : ℝ) * ‖midpoint ℝ y z - x‖ ^ (2 : ℕ) =
      (1 / 4 : ℝ) * (‖y - x‖ ^ (2 : ℕ) + ‖z - x‖ ^ (2 : ℕ)) -
        (1 / 8 : ℝ) * ‖y - z‖ ^ (2 : ℕ) := by
    -- The Euclidean midpoint identity isolates the strict loss term `‖y - z‖² / 8`.
    have hdist := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      x y z
    have hdist' : ‖y - x‖ ^ (2 : ℕ) + ‖z - x‖ ^ (2 : ℕ) =
        2 * (‖midpoint ℝ y z - x‖ ^ (2 : ℕ) + (‖y - z‖ / 2) ^ (2 : ℕ)) := by
      simpa [dist_eq_norm, norm_sub_rev, add_comm, add_left_comm, add_assoc] using hdist
    nlinarith [hdist']
  have hpm_upper : pm ≤ (py + pz) / 2 - (1 / 8 : ℝ) * ‖y - z‖ ^ (2 : ℕ) := by
    -- Combining convexity of `f` with the quadratic midpoint identity yields a strict upper bound
    -- unless `y = z`.
    dsimp [pm, py, pz]
    nlinarith [hmid_real, hmid_quad]
  have hnorm_sq : ‖y - z‖ ^ (2 : ℕ) = 0 := by
    nlinarith [hy_le_pm, hz_le_pm, hpm_upper, hpy_eq_pz]
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))

/-- Theorem 6.3: if `f` is a proper closed convex extended-real-valued function, then the proximal
set `prox[f] x` is a singleton for every `x`. This is the chapter's set-valued rendering of the
textbook point-valued proximal map `prox_f(x)`. The ambient assumption `[ProperSpace E]` is the
canonical abstraction replacing the explicit finite-dimensional Euclidean model from the textbook
proof route. -/
theorem prox_eq_singleton_of_proper_closed_convex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    ∃ y : E, prox[f] x = {y} := by
  -- Route correction: instead of importing the Chapter 5 singleton minimizer theorem, prove
  -- existence from coercivity of the proximal objective and uniqueness from the midpoint drop.
  have hcoercive := proximal_objective_coercive_of_proper_convex f hf_proper hf_convex x
  rcases attains_min_on_closed_set_of_coercive (proximal_objective f x)
      (lowerSemicontinuous_proximal_objective hf_closed x) hcoercive isClosed_univ
      (by simpa using hcoercive.effective_domain_nonempty) with ⟨y, -, hy_min⟩
  refine ⟨y, Set.eq_singleton_iff_unique_mem.2 ?_⟩
  constructor
  · -- The chosen minimizer is, by definition, a proximal point.
    simpa [mem_proximal_mapping_iff] using hy_min
  · intro z hz
    -- Any other proximal point coincides with `y` by the uniqueness helper above.
    exact eq_of_mem_proximal_mapping_of_mem_proximal_mapping f hf_proper hf_convex x z y hz
      (by simpa [mem_proximal_mapping_iff] using hy_min)

end
