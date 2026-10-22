/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

recall effective_domain
recall strongDualSubdifferential
recall subdifferential
recall isMinOn_univ_iff_zero_mem_subdifferential
recall is_subgradient_at_iff_forall_mem_effective_domain
recall convexOn_toReal_of_is_convex_function
recall combo_mem_effective_domain_of_is_convex_function

/-- Helper for Theorem 6.39: subtracting a finite real constant from a finite extended-real value
agrees with subtraction in the real line after applying `toReal`. -/
private lemma ereal_sub_real_eq_coe_sub {a : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) (α : ℝ) :
    a - α = (((a.toReal - α : ℝ)) : EReal) := by
  calc
    a - α = (((a.toReal : ℝ)) : EReal) - ((α : ℝ) : EReal) := by
      rw [EReal.coe_toReal ha_top ha_bot]
    _ = (((a.toReal - α : ℝ)) : EReal) := by
      rw [← EReal.coe_sub]

/-- Helper for Theorem 6.39: translating the quadratic penalty from `u` to `y` produces the
standard linear support term plus the residual quadratic correction. -/
lemma quadratic_translate_identity (x u y : E) :
    (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) =
      (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (y - u) +
        (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ) := by
  -- Rewrite `y - x` as the translated displacement from `u`, then expand the squared norm.
  have hyx : y - x = (y - u) + (u - x) := by
    abel
  have hsq :
      ‖y - x‖ ^ (2 : ℕ) =
        ‖y - u‖ ^ (2 : ℕ) + ‖u - x‖ ^ (2 : ℕ) +
          2 * inner ℝ (y - u) (u - x) := by
    rw [hyx, norm_add_sq_real]
    ring
  nlinarith [hsq, real_inner_comm (u - x) (y - u)]

/-- Helper for Theorem 6.39: every proximal point of a proper function lies in the effective
domain, because a finite comparison point forces the proximal objective value to stay finite. -/
lemma mem_effective_domain_of_mem_prox
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x : E) {u : E}
    (hu : u ∈ prox[f] x) :
    u ∈ effective_domain f := by
  rcases hf_proper.effective_domain_nonempty with ⟨u0, hu0_eff⟩
  have hu_min : ∀ v, proximal_objective f x u ≤ proximal_objective f x v := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
    exact hu
  have hu_obj : proximal_objective f x u ≤ proximal_objective f x u0 := hu_min u0
  have hu0_obj_top : proximal_objective f x u0 < ⊤ := by
    -- A single finite point of `f` yields a finite proximal objective value.
    have hu0_val :
        f u0 = (((f u0).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hu0_eff).ne (hf_proper.ne_bot u0)).symm
    rw [proximal_objective_apply, hu0_val]
    exact EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
  have hu_obj_top : proximal_objective f x u < ⊤ := lt_of_le_of_lt hu_obj hu0_obj_top
  have hu_top : f u ≠ ⊤ := by
    intro hfu
    have hobj_top : proximal_objective f x u = ⊤ := by
      rw [proximal_objective_apply, hfu, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    rw [hobj_top] at hu_obj_top
    simp at hu_obj_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hu_top)

/-- Helper for Theorem 6.39: singleton proximality forces both finiteness of the proximal point
and the textbook support inequality on the effective domain. -/
lemma prox_singleton_implies_effective_domain_and_inner_support
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) (hprox : prox[f] x = {u}) :
    u ∈ effective_domain f ∧
      ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  -- Route correction: the forward implication comes from convex perturbations of the proximal
  -- objective along the segment from `u` to `y`, not from a finite-dimensional exact sum rule.
  have hu_mem : u ∈ prox[f] x := by
    simpa [hprox]
  have hu_eff : u ∈ effective_domain f := mem_effective_domain_of_mem_prox f hf_proper x hu_mem
  refine ⟨hu_eff, ?_⟩
  intro y hy_eff
  by_cases hyu : y = u
  · -- At the proximal point itself the support inequality is the trivial `0 ≤ 0`.
    subst y
    have hzero : ((0 : ℝ) : EReal) ≤ f u - f u := by
      have hsupport_add :
          ((0 : ℝ) : EReal) + f u ≤ f u := by
        simpa using le_rfl
      exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
        (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add
    simpa using hzero
  · set A : ℝ := inner ℝ (x - u) (y - u) - ((f y).toReal - (f u).toReal)
    set B : ℝ := (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ)
    have hA_le_tB : ∀ {t : ℝ}, 0 < t → t ≤ 1 → A ≤ t * B := by
      intro t ht_pos ht_one
      have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_one⟩
      let z : E := t • y + (1 - t) • u
      have hz_eff : z ∈ effective_domain f :=
        combo_mem_effective_domain_of_is_convex_function hf_convex hy_eff hu_eff ht_mem
      have hy_val :
          f y = (((f y).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
      have hu_min : proximal_objective f x u ≤ proximal_objective f x z := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu_mem
        exact hu_mem z
      have hu_val :
          f u = (((f u).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
      have hz_val :
          f z = (((f z).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
      have hu_obj_real :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
            (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        -- Convert the proximal minimality inequality to the real line.
        have hu_min' := hu_min
        rw [proximal_objective_apply, proximal_objective_apply, hu_val, hz_val] at hu_min'
        have hu_min'' :
            ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
              ((((f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [EReal.coe_add] using hu_min'
        exact EReal.coe_le_coe_iff.mp hu_min''
      have hz_convE :
          f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f u := by
        -- Convexity controls the value of `f` along the segment from `u` to `y`.
        simpa [z, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
          (is_convex_function_iff_segment_ineq.mp hf_convex) y hy_eff u hu_eff ht_mem
      have hz_conv :
          (f z).toReal ≤ t * (f y).toReal + (1 - t) * (f u).toReal := by
        have hz_convE' := hz_convE
        rw [hz_val, hy_val, hu_val] at hz_convE'
        have hz_convE'' :
            (((f z).toReal : ℝ) : EReal) ≤
              ((((t * (f y).toReal + (1 - t) * (f u).toReal : ℝ)) : EReal)) := by
          simpa [EReal.coe_add, EReal.coe_mul] using hz_convE'
        exact EReal.coe_le_coe_iff.mp hz_convE''
      have hz_sub : z - u = t • (y - u) := by
        have hz_def : z = u + t • (y - u) := by
          dsimp [z]
          rw [smul_sub]
          module
        calc
          z - u = (u + t • (y - u)) - u := by rw [hz_def]
          _ = t • (y - u) := by
            abel
      have hinner_smul :
          inner ℝ (u - x) (t • (y - u)) = -t * inner ℝ (x - u) (y - u) := by
        have hinner_base :
            inner ℝ (u - x) (y - u) = -inner ℝ (x - u) (y - u) := by
          have hneg : u - x = -(x - u) := by
            abel
          rw [hneg, inner_neg_left]
        rw [inner_smul_right]
        rw [hinner_base]
        ring
      have hnorm_smul :
          (1 / 2 : ℝ) * ‖t • (y - u)‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * B := by
        dsimp [B]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
        ring
      have hz_quad :
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
              t ^ (2 : ℕ) * B := by
        -- The quadratic identity isolates the first-order term plus a `t²` remainder.
        calc
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
              (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (z - u) +
                (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := quadratic_translate_identity x u z
          _ = (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
                t ^ (2 : ℕ) * B := by
            rw [hz_sub, hinner_smul, hnorm_smul]
            ring
      have hstep :
          (f u).toReal + inner ℝ (x - u) (y - u) - (f y).toReal ≤ t * B := by
        nlinarith [hu_obj_real, hz_conv, hz_quad]
      simpa [A, B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hA_nonpos : A ≤ 0 := by
      by_contra hA
      have hA_pos : 0 < A := lt_of_not_ge hA
      let t : ℝ := min 1 (A / (B + 1))
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min (by norm_num) ?_
        have hden_pos : 0 < B + 1 := by
          linarith
        exact div_pos hA_pos hden_pos
      have ht_one : t ≤ 1 := by
        dsimp [t]
        exact min_le_left _ _
      have hAt : A ≤ t * B := hA_le_tB ht_pos ht_one
      have ht_bound : t ≤ A / (B + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have hmul_bound : t * B ≤ A * B / (B + 1) := by
        have := mul_le_mul_of_nonneg_right ht_bound hB_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hfrac_lt_one : B / (B + 1) < 1 := by
        have hden_pos : 0 < B + 1 := by
          linarith
        field_simp [hden_pos.ne']
        nlinarith
      have hstrict : A * B / (B + 1) < A := by
        have hden_pos : 0 < B + 1 := by
          linarith
        field_simp [hden_pos.ne']
        nlinarith [hA_pos, hB_nonneg]
      exact (not_lt_of_ge (le_trans hAt hmul_bound)) hstrict
    have hreal :
        inner ℝ (x - u) (y - u) ≤ (f y).toReal - (f u).toReal := by
      dsimp [A] at hA_nonpos
      linarith
    have hsupport_add_real :
        inner ℝ (x - u) (y - u) + (f u).toReal ≤ (f y).toReal := by
      linarith
    have hsupport_addE :
        ((((inner ℝ (x - u) (y - u) + (f u).toReal : ℝ)) : EReal)) ≤
          (((f y).toReal : ℝ) : EReal) := EReal.coe_le_coe hsupport_add_real
    have hu_val :
        f u = (((f u).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
    have hy_val :
        f y = (((f y).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
    have hsupport_add :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) + f u ≤ f y := by
      rw [hu_val, hy_val]
      simpa [EReal.coe_add] using hsupport_addE
    exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
      (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add

/-- Helper for Theorem 6.39: the support inequality on the effective domain forces `u` to be the
unique proximal minimizer. -/
lemma prox_eq_singleton_of_effective_domain_and_inner_support
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x u : E)
    (hu : u ∈ effective_domain f)
    (hineq : ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u) :
    prox[f] x = {u} := by
  have hu_val :
      f u = (((f u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hu).ne (hf_proper.ne_bot u)).symm
  have hu_mem : u ∈ prox[f] x := by
    -- The support inequality upgrades directly to global minimality of the proximal objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    by_cases hy : y ∈ effective_domain f
    · have hy_val :
          f y = (((f y).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hy).ne (hf_proper.ne_bot y)).symm
      have hsupport : ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := hineq y hy
      have hsupport_add :
          (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) + f u ≤ f y :=
        (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
          (.inl (mem_effective_domain.mp hu).ne)).1 hsupport
      have hsupport_real :
          inner ℝ (x - u) (y - u) + (f u).toReal ≤ (f y).toReal := by
        have hsupport_add' := hsupport_add
        rw [hu_val, hy_val] at hsupport_add'
        have hsupport_add'' :
            ((((inner ℝ (x - u) (y - u) + (f u).toReal : ℝ)) : EReal)) ≤
              (((f y).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_add] using hsupport_add'
        exact EReal.coe_le_coe_iff.mp hsupport_add''
      have hquad' :
          (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) =
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - inner ℝ (x - u) (y - u) +
              (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ) := by
        have hinner_base :
            inner ℝ (u - x) (y - u) = -inner ℝ (x - u) (y - u) := by
          rw [inner_sub_left, inner_sub_left]
          ring
        calc
          (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) =
              (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (y - u) +
                (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ) := quadratic_translate_identity x u y
          _ = (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - inner ℝ (x - u) (y - u) +
                (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ) := by
                  rw [hinner_base]
                  ring
      have hrest_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ) := by
        positivity
      have hobj_real :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
            (f y).toReal + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
        have hsupport_real' :
            (f u).toReal ≤ (f y).toReal - inner ℝ (x - u) (y - u) := by
          linarith
        calc
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)
              ≤ (f y).toReal - inner ℝ (x - u) (y - u) +
                  (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
                    linarith
          _ ≤ (f y).toReal - inner ℝ (x - u) (y - u) +
                ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ)) := by
                  nlinarith
          _ = (f y).toReal + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
                  nlinarith [hquad']
      have hobjE : ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
          ((((f y).toReal + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal) :=
        EReal.coe_le_coe hobj_real
      change
        f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
          f y + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal)
      rw [hu_val, hy_val]
      simpa [EReal.coe_add] using hobjE
    · -- Outside the effective domain, the proximal objective is `⊤`, so minimality is automatic.
      have hfy_top : f y = ⊤ := by
        have hnot : ¬ f y < ⊤ := by
          simpa [effective_domain] using hy
        exact le_antisymm le_top (not_lt.mp hnot)
      rw [proximal_objective_apply, proximal_objective_apply, hfy_top,
        EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · exact hu_mem
  · intro z hz
    have hz_eff : z ∈ effective_domain f := mem_effective_domain_of_mem_prox f hf_proper x hz
    have hz_val :
        f z = (((f z).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
    have hz_min : proximal_objective f x z ≤ proximal_objective f x u := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hz
      exact hz u
    have hz_min_real :
        (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) ≤
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
      have hz_min' := hz_min
      rw [proximal_objective_apply, proximal_objective_apply, hz_val, hu_val] at hz_min'
      have hz_min'' :
          ((((f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
            ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        simpa [EReal.coe_add] using hz_min'
      exact EReal.coe_le_coe_iff.mp hz_min''
    have hsupport : ((inner ℝ (x - u) (z - u) : ℝ) : EReal) ≤ f z - f u := hineq z hz_eff
    have hsupport_add :
        (((inner ℝ (x - u) (z - u) : ℝ)) : EReal) + f u ≤ f z :=
      (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
        (.inl (mem_effective_domain.mp hu).ne)).1 hsupport
    have hsupport_real :
        inner ℝ (x - u) (z - u) + (f u).toReal ≤ (f z).toReal := by
      have hsupport_add' := hsupport_add
      rw [hu_val, hz_val] at hsupport_add'
      have hsupport_add'' :
          ((((inner ℝ (x - u) (z - u) + (f u).toReal : ℝ)) : EReal)) ≤
            (((f z).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_add] using hsupport_add'
      exact EReal.coe_le_coe_iff.mp hsupport_add''
    have hquad' :
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
          (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - inner ℝ (x - u) (z - u) +
            (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := by
      have hinner_base :
          inner ℝ (u - x) (z - u) = -inner ℝ (x - u) (z - u) := by
        have hneg : u - x = -(x - u) := by
          abel
        rw [hneg, inner_neg_left]
      calc
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (z - u) +
              (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := quadratic_translate_identity x u z
        _ = (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - inner ℝ (x - u) (z - u) +
              (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := by
                rw [hinner_base]
                ring
    have hrest_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_sq : ‖z - u‖ ^ (2 : ℕ) = 0 := by
      have hlower :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) ≤
            (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        nlinarith [hsupport_real, hquad']
      have hgap_le : (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) ≤ 0 := by
        nlinarith [hlower, hz_min_real]
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))

/- Theorem 6.39 is `source-facing` for the chapter's proximal-operator API. Domain sampling
shows that the canonical owners already exist upstream: Chapter 6's set-valued proximal mapping
`prox[f]`, Chapter 3's continuous-dual bridge `strongDualSubdifferential`, and the Riesz map
`toDualMap ℝ E : E → StrongDual ℝ E`. The primitive data on the theorem surface is therefore the
canonical strong-dual membership `toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u`, while
the algebraic-dual set `subdifferential f u` remains internal supporting API through
`mem_strongDualSubdifferential`. -/

-- Proof sketch: extract the `(ii) ↔ (iii)` part of Theorem 6.39 by specializing the Chapter 3
-- owner theorem `is_subgradient_at_iff_forall_mem_effective_domain` to
-- `g = (toDualMap ℝ E (x - u) : Module.Dual ℝ E)` after rewriting the strong-dual clause with
-- `mem_strongDualSubdifferential`, and then rewriting
-- `toDualMap ℝ E (x - u) (y - u)` as `⟪x - u, y - u⟫`. The only extra local datum needed for the
-- converse direction is exactly the owner-domain condition `u ∈ effective_domain f`, and the
-- pointwise inequality only needs to be checked on `effective_domain f`, exactly as in the
-- Chapter 3 owner theorem. This remains a `bridge/view` reformulation of the primitive Chapter 3
-- subgradient owner, without any proximal or finite-dimensional hypotheses.
/-- Companion bridge for Theorem 6.39: for a proper function,
`toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u` is equivalent to the owner-domain
condition `u ∈ effective_domain f` together with the pointwise inequality
`⟪x - u, y - u⟫ ≤ f(y) - f(u)` on `effective_domain f`. -/
theorem toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x u : E) :
    toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u ↔
      u ∈ effective_domain f ∧
        ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  -- This is exactly the Chapter 3 owner predicate rewritten through the Riesz identification.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · rintro ⟨hu, hsub⟩
    refine ⟨hu, ?_⟩
    intro y hy
    have hsupport_add :
        ((inner ℝ (x - u) (y - u) : ℝ) : EReal) + f u ≤ f y := by
      have htmp := hsub y hy
      change f y ≥ f u + (((inner ℝ (x - u) (y - u) : ℝ) : EReal)) at htmp
      simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using htmp
    exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
      (.inl (mem_effective_domain.mp hu).ne)).2 hsupport_add
  · rintro ⟨hu, hineq⟩
    refine ⟨hu, ?_⟩
    intro y hy
    have hsupport_add :
        ((inner ℝ (x - u) (y - u) : ℝ) : EReal) + f u ≤ f y :=
      (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
        (.inl (mem_effective_domain.mp hu).ne)).1 (hineq y hy)
    change f y ≥ f u + (((inner ℝ (x - u) (y - u) : ℝ) : EReal))
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using hsupport_add

-- Proof sketch: this is the local `bridge/view` form of the `(i) ↔ (ii)` part of Theorem 6.39.
-- The semantically active owner-level assumptions are exactly properness and convexity of `f`.
-- The public statement uses the Chapter 3 strong-dual bridge because `toDualMap ℝ E` already
-- lands in `StrongDual ℝ E`; the algebraic-dual reformulation is only an internal consequence via
-- `mem_strongDualSubdifferential`.
/-- Companion bridge for Theorem 6.39: for a proper convex extended-real-valued function,
`prox[f] x = {u}` is equivalent to the canonical strong-dual subgradient condition
`toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u`. -/
theorem prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) :
    prox[f] x = {u} ↔
      toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u := by
  constructor
  · intro hprox
    -- The forward direction is the support inequality bridge specialized to a singleton prox set.
    exact (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le f hf_proper x u).2
      (prox_singleton_implies_effective_domain_and_inner_support f hf_proper hf_convex x u hprox)
  · intro hsub
    -- The reverse direction rebuilds the proximal singleton directly from the support inequality.
    rcases (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le f hf_proper x u).1
        hsub with
      ⟨hu, hineq⟩
    exact prox_eq_singleton_of_effective_domain_and_inner_support f hf_proper x u hu hineq

-- Proof sketch: for `(i) → (ii)`, rewrite `u ∈ prox[f] x` as global minimality of the proximal
-- objective and apply the proved forward support helper; for `(ii) ↔ (iii)`, use the proper
-- strong-dual bridge above; for `(iii) → (i)`, rebuild the unique proximal point directly from the
-- support inequality.
/-- Theorem 6.39: second prox theorem. For a proper convex extended-real-valued function, the
following are equivalent for fixed `x` and `u`: (i) the proximal set `prox[f] x` is the singleton
`{u}`, (ii) the Riesz image of `x - u` belongs to the canonical strong-dual subdifferential of
`f` at `u`, and (iii) the
inequality `⟪x - u, y - u⟫ ≤ f(y) - f(u)` holds for every `y`. -/
theorem prox_eq_singleton_tfae_strongDualSubdifferential_inner_le
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) :
    List.TFAE
      [prox[f] x = {u},
        toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u,
        ∀ y, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u] := by
  -- The main equivalence is assembled from the two canonical companion bridges.
  tfae_have 1 ↔ 2 := prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
    f hf_proper hf_convex x u
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hsub y
      rcases (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le f hf_proper x u).1
          hsub with
        ⟨hu, hineq⟩
      by_cases hy : y ∈ effective_domain f
      · exact hineq y hy
      · have hfy_top : f y = ⊤ := by
          have hnot : ¬ f y < ⊤ := by
            simpa [effective_domain] using hy
          exact le_antisymm le_top (not_lt.mp hnot)
        rw [hfy_top, EReal.top_sub (mem_effective_domain.mp hu).ne]
        exact le_top
    · intro hineq_all
      rcases hf_proper.effective_domain_nonempty with ⟨y0, hy0⟩
      have hfu_top : f u ≠ ⊤ := by
        intro hfu
        have hbad : (((inner ℝ (x - u) (y0 - u) : ℝ) : EReal)) ≤ (⊥ : EReal) := by
          simpa [hfu, hf_proper.ne_bot y0] using hineq_all y0
        simpa using hbad
      have hu : u ∈ effective_domain f :=
        mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfu_top)
      exact (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le f hf_proper x u).2
        ⟨hu, fun y hy ↦ hineq_all y⟩
  tfae_finish

end
