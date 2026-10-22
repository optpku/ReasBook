/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Corollary 6.40 is `source-facing` for the proximal-operator chapter. Domain sampling in the
minimal closure checks the same owner stack already used upstream:

- `prox[f]`, `proximal_objective_apply`, and `mem_proximal_mapping_iff` from Definition 6.1 for
  the proximal owner and its minimizer view;
- `is_convex_function_iff_segment_ineq` and
  `combo_mem_effective_domain_of_is_convex_function` from Definition 2.7 for the convex segment
  argument on the effective domain;
- Theorem 6.39 only as a stronger inner-product bridge, not as the owner abstraction here.

The primitive data are therefore only `f`, properness, convexity, and the base point `x`. Since
the strong-dual bridge would force an unnecessary `InnerProductSpace` assumption, this file keeps
the weaker normed-space formulation directly on the owner set `prox[f]` and the minimizer
predicate `IsMinOn`. The textbook fixed-point statement `x = prox_f(x)` is therefore rendered
canonically as the singleton identity `prox[f] x = {x}` rather than by introducing a parallel
single-valued proximal operator. -/

-- Proof sketch: for `→`, if `x` globally minimizes `f`, then `x` minimizes the proximal
-- objective at `x`, and any other proximal point `u` would satisfy
-- `f u + (1 / 2) ‖u - x‖² ≤ f x ≤ f u`, forcing `u = x`. For `←`, the singleton hypothesis gives
-- that `x` minimizes the proximal objective at `x`. If `f y < f x`, convexity along the segment
-- from `x` to `y` and the proximal optimality inequality at `x` produce
-- `f x ≤ f y + (t / 2) ‖y - x‖²` for every sufficiently small `t > 0`, a contradiction.
/-- Corollary 6.40: for a proper convex extended-real-valued function, a point `x` is a global
minimizer of `f` if and only if `x` is a fixed point of the proximal mapping, expressed in the
chapter's set-valued API as `prox[f] x = {x}`. -/
theorem isMinOn_univ_iff_prox_eq_singleton_self
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x : E) :
    IsMinOn f Set.univ x ↔ prox[f] x = {x} := by
  constructor
  · intro hx
    rw [isMinOn_univ_iff] at hx
    rw [Set.eq_singleton_iff_unique_mem]
    constructor
    · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro y
      have hy : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by positivity
      calc
        proximal_objective f x x = f x := by simp [proximal_objective_apply]
        _ ≤ f y := hx y
        _ ≤ f y + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
          exact le_add_of_nonneg_right (by exact_mod_cast hy)
        _ = proximal_objective f x y := by
          rw [proximal_objective_apply]
    · intro u hu
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
      rcases hf_proper.effective_domain_nonempty with ⟨y, hy⟩
      have hfx_top : f x ≠ ⊤ := (lt_of_le_of_lt (hx y) hy).ne
      have hfu_top : f u ≠ ⊤ := by
        intro hfu_top
        have hux : (⊤ : EReal) + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤ f x := by
          simpa [proximal_objective_apply, hfu_top] using hu x
        have hux' : (⊤ : EReal) ≤ f x := by
          calc
            (⊤ : EReal) = (⊤ : EReal) + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
              symm
              exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
            _ ≤ f x := hux
        exact hfx_top (top_le_iff.mp hux)
      have hux : f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤ f x := by
        simpa [proximal_objective_apply] using hu x
      have hxu : f x ≤ f u := hx u
      have hux_real : (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤ (f x).toReal := by
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [EReal.coe_add, EReal.coe_toReal hfu_top (hf_proper.ne_bot u),
            EReal.coe_toReal hfx_top (hf_proper.ne_bot x)] using hux
      have hxu_real : (f x).toReal ≤ (f u).toReal := by
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [EReal.coe_toReal hfx_top (hf_proper.ne_bot x),
            EReal.coe_toReal hfu_top (hf_proper.ne_bot u)] using hxu
      have hnorm_sq : ‖u - x‖ ^ (2 : ℕ) = 0 := by
        nlinarith
      exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))
  · intro hprox
    rw [isMinOn_univ_iff]
    have hx_prox : x ∈ prox[f] x := by simp [hprox]
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hx_prox
    rcases hf_proper.effective_domain_nonempty with ⟨u, hu⟩
    have hfx_top : f x ≠ ⊤ := by
      have hxu : proximal_objective f x x ≤ proximal_objective f x u := hx_prox u
      have hu_top : f u ≠ ⊤ := (mem_effective_domain.mp hu).ne
      intro hfx_top
      have htop : (⊤ : EReal) ≤ proximal_objective f x u := by
        simpa [proximal_objective_apply, hfx_top] using hxu
      have hpu_top : proximal_objective f x u ≠ ⊤ := by
        intro hpu_top
        have : f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊤ :=
          EReal.add_ne_top hu_top (EReal.coe_ne_top _)
        exact this (by simpa [proximal_objective_apply] using hpu_top)
      exact hpu_top (top_le_iff.mp htop)
    have hx_eff : x ∈ effective_domain f := by
      exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfx_top)
    intro y
    by_cases hy_top : f y = ⊤
    · simp [hy_top]
    · by_contra hxy
      have hxy_real : (f y).toReal < (f x).toReal := by
        exact EReal.coe_lt_coe_iff.mp <| by
          simpa [EReal.coe_toReal hy_top (hf_proper.ne_bot y),
            EReal.coe_toReal hfx_top (hf_proper.ne_bot x)] using lt_of_not_ge hxy
      let δ : ℝ := (f x).toReal - (f y).toReal
      let κ : ℝ := ‖y - x‖ ^ (2 : ℕ)
      let t : ℝ := min 1 (δ / (κ + 1))
      have hδ : 0 < δ := by
        dsimp [δ]
        linarith
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min (by norm_num) ?_
        exact div_pos hδ (by positivity)
      have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨le_of_lt ht_pos, ?_⟩
        dsimp [t]
        exact min_le_left _ _
      have hy_eff : y ∈ effective_domain f := by
        exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hy_top)
      let z : E := t • y + (1 - t) • x
      have hz_eff : z ∈ effective_domain f := by
        dsimp [z]
        exact combo_mem_effective_domain_of_is_convex_function hf_convex hy_eff hx_eff ht_mem
      have hz_conv :
          f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f x := by
        dsimp [z]
        simpa using
          (is_convex_function_iff_segment_ineq.mp hf_convex) y hy_eff x hx_eff ht_mem
      have hxz :
          f x ≤ f z + ((((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
        simpa [proximal_objective_apply] using hx_prox z
      have hz_bound : f z ≤ (((t * (f y).toReal + (1 - t) * (f x).toReal : ℝ) : EReal)) := by
        simpa [EReal.coe_add, EReal.coe_mul,
          EReal.coe_toReal hy_top (hf_proper.ne_bot y),
          EReal.coe_toReal hfx_top (hf_proper.ne_bot x)] using hz_conv
      have hz_sub : z - x = t • (y - x) := by
        dsimp [z]
        calc
          t • y + (1 - t) • x - x = t • y + ((1 - t) • x - 1 • x) := by
            abel_nf
          _ = t • y + ((1 - t - 1) • x) := by
            simp [sub_smul]
          _ = t • y + (-t) • x := by ring_nf
          _ = t • y - t • x := by rw [sub_eq_add_neg, neg_smul]
          _ = t • (y - x) := by rw [smul_sub]
      have hx_bound :
          (f x).toReal ≤ (f z).toReal + (1 / 2 : ℝ) * t ^ (2 : ℕ) * κ := by
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [hz_sub, κ, proximal_objective_apply, EReal.coe_add,
            EReal.coe_toReal hfx_top (hf_proper.ne_bot x),
            EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z),
            norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), mul_pow, mul_assoc, mul_left_comm,
            mul_comm] using hxz
      have hz_conv_real : (f z).toReal ≤ t * (f y).toReal + (1 - t) * (f x).toReal := by
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)] using
            hz_bound
      have hmain : δ ≤ (1 / 2 : ℝ) * t * κ := by
        dsimp [δ] at *
        nlinarith [hx_bound, hz_conv_real, ht_mem.1, ht_mem.2]
      have ht_le : t ≤ δ / (κ + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have hκ : 0 ≤ κ := by
        dsimp [κ]
        positivity
      have hκ1 : 0 < κ + 1 := by positivity
      have hδκ : (1 / 2 : ℝ) * t * κ ≤ δ * κ / (2 * (κ + 1)) := by
        have hmul : t * κ ≤ (δ / (κ + 1)) * κ := mul_le_mul_of_nonneg_right ht_le hκ
        have hhalfmul :
            (1 / 2 : ℝ) * (t * κ) ≤ (1 / 2 : ℝ) * ((δ / (κ + 1)) * κ) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        calc
          (1 / 2 : ℝ) * t * κ = (1 / 2 : ℝ) * (t * κ) := by ring
          _ ≤ (1 / 2 : ℝ) * ((δ / (κ + 1)) * κ) := hhalfmul
          _ = δ * κ / (2 * (κ + 1)) := by
            field_simp [hκ1.ne']
      have hfrac_lt_one : κ / (κ + 1) < 1 := by
        rw [div_lt_iff₀ hκ1]
        nlinarith
      have hsmall : δ * κ / (2 * (κ + 1)) < δ / 2 := by
        have hδ2 : 0 < δ / 2 := by positivity
        have hrew : δ * κ / (2 * (κ + 1)) = (δ / 2) * (κ / (κ + 1)) := by
          field_simp [hκ1.ne']
        rw [hrew]
        simpa using mul_lt_mul_of_pos_left hfrac_lt_one hδ2
      have hhalf : δ ≤ δ / 2 := le_trans (le_trans hmain hδκ) hsmall.le
      nlinarith

end
