/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_15
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (is_convex_function g)]
variable (x0 : E) (c : PosReal)
variable {x : ℕ → E}

local notation "XStar" => unconstrained_problem_solutions g

open scoped ProximalPoint

/- Theorem 10.28 is `source-facing` in the Chapter 10 proximal-point API.

Domain sampling in the surrounding project identifies:
- `is_proximal_point_trajectory` from Definition 10.12 as the owner of the generated iterate
  sequence `x^k` at the weakest ambient level;
- `proximal_point_method` from Definition 10.12 as the point-valued bridge/view available once the
  scaled proximal sets are known to be singletons;
- `unconstrained_problem_solutions` from Chapter 8 as the owner of the whole-space optimizer set
  `X^*`;
- `IsFejerMonotoneWithRespectTo` from Chapter 8 as the canonical owner abstraction for the
  descent mechanism behind convergence.

Triage for this file:
- `source-facing`: the objective-gap and convergence clauses of Theorem 10.28;
- `core/canonical`: the proximal-point trajectory owner `is_proximal_point_trajectory`;
- `bridge/view`: the singleton-valued recursion `proximal_point_method` and the Chapter 8
  optimizer-set / Fejér-monotonicity interfaces.

Primitive data are only the objective `g`, its proper/closed/convex regularity, the initial point
`x0`, the positive parameter `c`, and for clause (1) a trajectory witness
`is_proximal_point_trajectory g x0 c x`. Membership in `X^*`, the objective-gap estimate, and the
properness-dependent convergence conclusion are derived API over that owner stack, so this file
reuses the Chapter 8 Fejér owner directly instead of introducing a parallel local descent or
cluster-point wrapper. -/

/-- Helper for Theorem 10.28: a proximal membership already yields the effective-domain inclusion
and affine support inequality from the source proof, without first packaging the proximal set as a
singleton. -/
private lemma mem_prox_implies_effective_domain_and_inner_support
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) (hu : u ∈ prox[f] x) :
    u ∈ effective_domain f ∧
      ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  -- Route correction: use the original convex-perturbation proof directly from proximal
  -- membership, rather than trying to recover a singleton description first.
  have hu_eff : u ∈ effective_domain f := mem_effective_domain_of_mem_prox f hf_proper x hu
  refine ⟨hu_eff, ?_⟩
  intro y hy_eff
  by_cases hyu : y = u
  · -- At `y = u`, the support inequality is the trivial `0 ≤ 0`.
    subst y
    have hzero : ((0 : ℝ) : EReal) ≤ f u - f u := by
      have hsupport_add :
          ((0 : ℝ) : EReal) + f u ≤ f u := by
        simp
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
        -- Unfold the proximal membership into minimality of the penalized objective.
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        exact hu z
      have hu_val :
          f u = (((f u).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
      have hz_val :
          f z = (((f z).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
      have hu_obj_real :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
            (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        -- Convert proximal minimality from `EReal` to the real line at finite points.
        have hu_min' := hu_min
        rw [proximal_objective_apply, proximal_objective_apply, hu_val, hz_val] at hu_min'
        have hu_min'' :
            ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
              ((((f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [EReal.coe_add] using hu_min'
        exact EReal.coe_le_coe_iff.mp hu_min''
      have hz_convE :
          f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f u := by
        -- Convexity controls the objective along the segment from `u` to `y`.
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
        -- The quadratic identity isolates the linear support term plus a `t^2` remainder.
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

/-- Helper for Theorem 10.28: descaling the previous proximal support lemma gives the textbook
affine support inequality for the original objective `g`. -/
private lemma mem_scaled_prox_implies_effective_domain_and_inner_support
    (x u : E) (hu : u ∈ prox[((c : EReal) • g)] x) :
    u ∈ effective_domain g ∧
      ∀ y ∈ effective_domain g,
        ((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ) : EReal) ≤ g y - g u := by
  let gScaled : E → EReal := ((c : EReal) • g)
  have hgScaled_proper : IsProperExtendedRealFunction gScaled :=
    by
      refine ⟨?_, ?_⟩
      · intro z
        dsimp [gScaled]
        exact
          (EReal.mul_ne_bot _ _).2
            ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (‹IsProperExtendedRealFunction g›.ne_bot z),
              Or.inl (EReal.coe_ne_top _),
              Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ))⟩
      · rcases (‹IsProperExtendedRealFunction g›).effective_domain_nonempty with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        rw [mem_effective_domain]
        dsimp [gScaled]
        exact
          lt_top_iff_ne_top.mpr <|
            (EReal.mul_ne_top _ _).2
              ⟨Or.inl (EReal.coe_ne_bot _),
                Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ)),
                Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hz).ne⟩
  have hg_convex : is_convex_function g := Fact.out
  have hgScaled_convex : is_convex_function gScaled :=
    by
      rw [is_convex_function]
      intro p hp q hq a b ha hb hab
      have hp0 : gScaled p.1 ≤ (p.2 : EReal) := by
        simpa [Set.mem_setOf_eq, gScaled] using hp
      have hq0 : gScaled q.1 ≤ (q.2 : EReal) := by
        simpa [Set.mem_setOf_eq, gScaled] using hq
      have hc_pos : (0 : EReal) < (c : ℝ) := by
        exact_mod_cast (show 0 < (c : ℝ) from c.2)
      have hc_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hp' : (p.1, p.2 / (c : ℝ)) ∈ {r : E × ℝ | g r.1 ≤ (r.2 : EReal)} := by
        rw [Set.mem_setOf_eq, EReal.coe_div]
        dsimp [gScaled] at hp0
        exact (EReal.le_div_iff_mul_le hc_pos hc_top).2 (by simpa [mul_comm] using hp0)
      have hq' : (q.1, q.2 / (c : ℝ)) ∈ {r : E × ℝ | g r.1 ≤ (r.2 : EReal)} := by
        rw [Set.mem_setOf_eq, EReal.coe_div]
        dsimp [gScaled] at hq0
        exact (EReal.le_div_iff_mul_le hc_pos hc_top).2 (by simpa [mul_comm] using hq0)
      have hcombo := hg_convex hp' hq' ha hb hab
      have hdivr :
          a * (p.2 / (c : ℝ)) + b * (q.2 / (c : ℝ)) =
            (a * p.2 + b * q.2) / (c : ℝ) := by
        field_simp [(show 0 < (c : ℝ) from c.2).ne']
      have hcombo' :
          g (a • p.1 + b • q.1) ≤ ((((a * p.2 + b * q.2) / (c : ℝ) : ℝ)) : EReal) := by
        simpa [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hdivr] using hcombo
      rw [Set.mem_setOf_eq]
      dsimp [gScaled]
      rw [EReal.coe_div] at hcombo'
      have hscaled := (EReal.le_div_iff_mul_le hc_pos hc_top).1 hcombo'
      simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hscaled
  rcases mem_prox_implies_effective_domain_and_inner_support
      gScaled hgScaled_proper hgScaled_convex x u hu with
    ⟨hu_eff_scaled, hsupport_scaled⟩
  have hu_eff : u ∈ effective_domain g :=
    by
      rw [mem_effective_domain] at hu_eff_scaled ⊢
      refine lt_top_iff_ne_top.mpr ?_
      intro hgu_top
      have hscaled_top : gScaled u = ⊤ := by
        dsimp [gScaled]
        rw [hgu_top]
        exact EReal.coe_mul_top_of_pos c.2
      exact (lt_irrefl (⊤ : EReal)) (hscaled_top ▸ hu_eff_scaled)
  refine ⟨hu_eff, ?_⟩
  intro y hy
  have hy_scaled : y ∈ effective_domain gScaled :=
    by
      rw [mem_effective_domain] at hy ⊢
      dsimp [gScaled]
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.mul_ne_top _ _).2
            ⟨Or.inl (EReal.coe_ne_bot _),
              Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ)),
              Or.inl (EReal.coe_ne_top _), Or.inr hy.ne⟩
  have hu_val :
      g u = (((g u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal
      (mem_effective_domain.mp hu_eff).ne
      (‹IsProperExtendedRealFunction g›.ne_bot u)).symm
  have hy_val :
      g y = (((g y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (‹IsProperExtendedRealFunction g›.ne_bot y)).symm
  have hu_scaled_val :
      gScaled u = ((((c : ℝ) * (g u).toReal : ℝ)) : EReal) := by
    have htoReal : (gScaled u).toReal = (c : ℝ) * (g u).toReal := by
      change (((c : EReal) * g u).toReal) = (c : ℝ) * (g u).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled u = (((gScaled u).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hu_eff_scaled).ne (hgScaled_proper.ne_bot u)]
      _ = ((((c : ℝ) * (g u).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hy_scaled_val :
      gScaled y = ((((c : ℝ) * (g y).toReal : ℝ)) : EReal) := by
    have htoReal : (gScaled y).toReal = (c : ℝ) * (g y).toReal := by
      change (((c : EReal) * g y).toReal) = (c : ℝ) * (g y).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled y = (((gScaled y).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hy_scaled).ne (hgScaled_proper.ne_bot y)]
      _ = ((((c : ℝ) * (g y).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hsupport_real :
      inner ℝ (x - u) (y - u) ≤ (c : ℝ) * ((g y).toReal - (g u).toReal) := by
    have hsupportE := hsupport_scaled y hy_scaled
    rw [hu_scaled_val, hy_scaled_val] at hsupportE
    have hsupportE' :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) ≤
          ((((c : ℝ) * ((g y).toReal - (g u).toReal) : ℝ)) : EReal) := by
      simpa [EReal.coe_sub, mul_sub_left_distrib] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_div :
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) ≤ (g y).toReal - (g u).toReal := by
    have hscaled :
        (1 / c : ℝ) * inner ℝ (x - u) (y - u) ≤
          (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := by
      exact
        mul_le_mul_of_nonneg_left hsupport_real
          (by
            simpa [one_div] using
              inv_nonneg.mpr (show 0 ≤ (c : ℝ) by exact le_of_lt c.2))
    have hcancel :
        (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) =
          (g y).toReal - (g u).toReal := by
      field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast c.2.ne']
    calc
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u)
          = (1 / c : ℝ) * inner ℝ (x - u) (y - u) := by
            simpa using inner_smul_left (x - u) (y - u) (1 / c : ℝ)
      _ ≤ (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := hscaled
      _ = (g y).toReal - (g u).toReal := hcancel
  have hsupport_realE :
      (((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ)) : EReal) ≤
        (((((g y).toReal - (g u).toReal : ℝ)) : EReal)) :=
    EReal.coe_le_coe hsupport_div
  rw [hy_val, hu_val]
  simpa [EReal.coe_sub] using hsupport_realE

/-- Helper for Theorem 10.28: every positive-index iterate has finite objective value. -/
lemma proximal_point_trajectory_mem_effective_domain
    (htraj : is_proximal_point_trajectory g x0 c x) {k : ℕ} (hk : 1 ≤ k) :
    x k ∈ effective_domain g := by
  -- Positive-index iterates are successor points, so one step of the trajectory gives the
  -- required scaled-proximal membership.
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  exact
    (mem_scaled_prox_implies_effective_domain_and_inner_support
      g c (x j) (x (j + 1))
      (is_proximal_point_trajectory_step htraj j)).1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (is_convex_function g)] in
/-- Helper for Theorem 10.28: every optimizer has finite objective value. -/
lemma optimal_point_mem_effective_domain
    {xStar : E} (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  rcases (inferInstance : IsProperExtendedRealFunction g).effective_domain_nonempty with
    ⟨y, hy⟩
  have hxStar_le : g xStar ≤ g y :=
    (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar) y
  have hy_top : g y ≠ ⊤ := (mem_effective_domain.mp hy).ne
  have hxStar_top : g xStar ≠ ⊤ := by
    intro hxStar_top
    have htop_le : (⊤ : EReal) ≤ g y := by
      simpa [hxStar_top] using hxStar_le
    exact hy_top (top_le_iff.mp htop_le)
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hxStar_top)

/-- Helper for Theorem 10.28: the singleton proximal-point step yields the real affine support
inequality used in the source proof. -/
lemma proximal_point_step_support_ineq_real
    (htraj : is_proximal_point_trajectory g x0 c x)
    (k : ℕ) {y : E} (hy : y ∈ effective_domain g) :
    inner ℝ (x k - x (k + 1)) (y - x (k + 1)) ≤
      (c : ℝ) * ((g y).toReal - (g (x (k + 1))).toReal) := by
  -- Apply the scaled proximal support lemma to the actual trajectory membership, then clear the
  -- factor `1 / c` to recover the textbook real inequality.
  have hstep_mem :
      x (k + 1) ∈ prox[((c : EReal) • g)] (x k) :=
    is_proximal_point_trajectory_step htraj k
  rcases mem_scaled_prox_implies_effective_domain_and_inner_support
      g c (x k) (x (k + 1)) hstep_mem with
    ⟨hxNext_eff, hsupport⟩
  have hy_val :
      g y = (((g y).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hy).ne
        (‹IsProperExtendedRealFunction g›.ne_bot y)).symm
  have hxNext_val :
      g (x (k + 1)) = ((((g (x (k + 1))).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  have hsupportE := hsupport y hy
  rw [hy_val, hxNext_val] at hsupportE
  have hsupportE' :
      (((inner ℝ ((1 / c : ℝ) • (x k - x (k + 1))) (y - x (k + 1)) : ℝ)) : EReal) ≤
        (((((g y).toReal - (g (x (k + 1))).toReal : ℝ)) : EReal)) := by
    simpa [EReal.coe_sub] using hsupportE
  have hsupport_real :
      inner ℝ ((1 / c : ℝ) • (x k - x (k + 1))) (y - x (k + 1)) ≤
        (g y).toReal - (g (x (k + 1))).toReal :=
    EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_real' :
      (1 / c : ℝ) * inner ℝ (x k - x (k + 1)) (y - x (k + 1)) ≤
        (g y).toReal - (g (x (k + 1))).toReal := by
    calc
      (1 / c : ℝ) * inner ℝ (x k - x (k + 1)) (y - x (k + 1))
          = inner ℝ ((1 / c : ℝ) • (x k - x (k + 1))) (y - x (k + 1)) := by
            simpa using
              (inner_smul_left (x k - x (k + 1)) (y - x (k + 1)) (1 / c : ℝ)).symm
      _ ≤ (g y).toReal - (g (x (k + 1))).toReal := hsupport_real
  have hc_pos : 0 < (c : ℝ) := c.2
  have hmul :
      (c : ℝ) *
          ((1 / c : ℝ) * inner ℝ (x k - x (k + 1)) (y - x (k + 1))) ≤
        (c : ℝ) * ((g y).toReal - (g (x (k + 1))).toReal) := by
    exact mul_le_mul_of_nonneg_left hsupport_real' hc_pos.le
  calc
    inner ℝ (x k - x (k + 1)) (y - x (k + 1))
        = (c : ℝ) * ((1 / c : ℝ) * inner ℝ (x k - x (k + 1)) (y - x (k + 1))) := by
            field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast c.2.ne']
    _ ≤ (c : ℝ) * ((g y).toReal - (g (x (k + 1))).toReal) := hmul

/-- Helper for Theorem 10.28: the proximal-point step satisfies the textbook three-point
estimate against any finite comparison point. -/
lemma proximal_point_step_gap_le_sqdist_drop
    (htraj : is_proximal_point_trajectory g x0 c x)
    (k : ℕ) {y : E} (hy : y ∈ effective_domain g) :
    2 * (c : ℝ) * ((g (x (k + 1))).toReal - (g y).toReal) ≤
      ‖x k - y‖ ^ (2 : ℕ) - ‖x (k + 1) - y‖ ^ (2 : ℕ) - ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
  have hsupport :=
    proximal_point_step_support_ineq_real g x0 c htraj k hy
  have hsq :
      ‖x k - y‖ ^ (2 : ℕ) =
        ‖x k - x (k + 1)‖ ^ (2 : ℕ) -
          2 * inner ℝ (x k - x (k + 1)) (y - x (k + 1)) +
            ‖y - x (k + 1)‖ ^ (2 : ℕ) := by
    -- Expand the translated norm square so the support inequality becomes a quadratic estimate.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_sub_sq_real (x k - x (k + 1)) (y - x (k + 1)))
  have hy_norm :
      ‖y - x (k + 1)‖ ^ (2 : ℕ) = ‖x (k + 1) - y‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  have hstep_norm :
      ‖x k - x (k + 1)‖ ^ (2 : ℕ) = ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  nlinarith [hsupport, hsq, hy_norm, hstep_norm]

/-- Helper for Theorem 10.28: the proximal-point objective values along successor iterates form an
antitone real sequence. -/
lemma proximal_point_successor_objective_antitone
    (htraj : is_proximal_point_trajectory g x0 c x) :
    Antitone (fun k ↦ (g (x (k + 1))).toReal) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  have hk_eff :
      x (k + 1) ∈ effective_domain g :=
    proximal_point_trajectory_mem_effective_domain g x0 c htraj
      (Nat.succ_le_succ (Nat.zero_le k))
  have hstep :=
    proximal_point_step_gap_le_sqdist_drop g x0 c htraj (k + 1) hk_eff
  have hgap_nonpos :
      2 * (c : ℝ) * ((g (x (k + 2))).toReal - (g (x (k + 1))).toReal) ≤ 0 := by
    -- Specializing the three-point inequality at `y = x^(k+1)` leaves only the objective drop.
    have hrhs_nonpos :
        ‖x (k + 1) - x (k + 1)‖ ^ (2 : ℕ) - ‖x (k + 2) - x (k + 1)‖ ^ (2 : ℕ) -
            ‖x (k + 2) - x (k + 1)‖ ^ (2 : ℕ) ≤
          0 := by
      have hnorm_nonneg : 0 ≤ ‖x (k + 2) - x (k + 1)‖ ^ (2 : ℕ) := by positivity
      simp
    exact le_trans hstep hrhs_nonpos
  have hc_pos : 0 < 2 * (c : ℝ) := by
    nlinarith [show 0 < (c : ℝ) from c.2]
  nlinarith

/-- Helper for Theorem 10.28: summing the optimizer-specialized three-point inequality telescopes
the objective gaps against the initial squared distance. -/
lemma proximal_point_prefix_gap_sum_le
    (htraj : is_proximal_point_trajectory g x0 c x)
    (xStar : E) (hxStar : xStar ∈ XStar) (K : ℕ) :
    2 * (c : ℝ) *
        (Finset.sum (Finset.range (K + 1))
          fun i ↦ (g (x (i + 1))).toReal - (g xStar).toReal) +
      ‖x (K + 1) - xStar‖ ^ (2 : ℕ) ≤
        ‖x0 - xStar‖ ^ (2 : ℕ) := by
  have hxStar_eff : xStar ∈ effective_domain g :=
    optimal_point_mem_effective_domain g hxStar
  induction K with
  | zero =>
      have hstep :=
        proximal_point_step_gap_le_sqdist_drop g x0 c htraj 0 hxStar_eff
      have hstep' :
          2 * (c : ℝ) * ((g (x 1)).toReal - (g xStar).toReal) + ‖x 1 - xStar‖ ^ (2 : ℕ) ≤
            ‖x 0 - xStar‖ ^ (2 : ℕ) := by
        nlinarith [hstep, sq_nonneg ‖x 1 - x 0‖]
      have hxzero : x 0 = x0 := is_proximal_point_trajectory_zero htraj
      simpa [hxzero, Finset.sum_range_one] using hstep'
  | succ K ih =>
      have hstep :=
        proximal_point_step_gap_le_sqdist_drop g x0 c htraj (K + 1) hxStar_eff
      have hstep' :
          2 * (c : ℝ) * ((g (x (K + 2))).toReal - (g xStar).toReal) +
            ‖x (K + 2) - xStar‖ ^ (2 : ℕ) ≤
              ‖x (K + 1) - xStar‖ ^ (2 : ℕ) := by
        nlinarith [hstep, sq_nonneg ‖x (K + 2) - x (K + 1)‖]
      calc
        2 * (c : ℝ) *
            (Finset.sum (Finset.range (K + 2))
              fun i ↦ (g (x (i + 1))).toReal - (g xStar).toReal) +
            ‖x (K + 2) - xStar‖ ^ (2 : ℕ)
            =
          2 * (c : ℝ) *
              (Finset.sum (Finset.range (K + 1))
                fun i ↦ (g (x (i + 1))).toReal - (g xStar).toReal) +
              (2 * (c : ℝ) * ((g (x (K + 2))).toReal - (g xStar).toReal) +
                ‖x (K + 2) - xStar‖ ^ (2 : ℕ)) := by
                  rw [Finset.sum_range_succ]
                  ring
        _ ≤
          2 * (c : ℝ) *
              (Finset.sum (Finset.range (K + 1))
                fun i ↦ (g (x (i + 1))).toReal - (g xStar).toReal) +
              ‖x (K + 1) - xStar‖ ^ (2 : ℕ) := by
                gcongr
        _ ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := ih

-- Proof sketch: apply the proximal optimality condition at each step with an arbitrary optimizer
-- `xStar ∈ X^*` along a proximal-point trajectory. Rearranging the resulting one-step inequality
-- gives
-- `‖x^(k+1) - xStar‖ ≤ ‖x^k - xStar‖`, which is exactly the Chapter 8 Fejér owner predicate.
/-- Helper for Theorem 10.28: any proximal-point trajectory is Fejér monotone with respect to the
canonical optimizer set `X^*`. -/
theorem proximal_point_method_fejer_monotonicity
    (htraj : is_proximal_point_trajectory g x0 c x) :
    IsFejerMonotoneWithRespectTo x XStar := by
  intro xStar hxStar k
  have hxStar_eff : xStar ∈ effective_domain g :=
    optimal_point_mem_effective_domain g hxStar
  have hstep :=
    proximal_point_step_gap_le_sqdist_drop g x0 c htraj k hxStar_eff
  have hopt :
      g xStar ≤ g (x (k + 1)) :=
    (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar) (x (k + 1))
  have hxNext_eff :
      x (k + 1) ∈ effective_domain g :=
    proximal_point_trajectory_mem_effective_domain g x0 c htraj
      (Nat.succ_le_succ (Nat.zero_le k))
  have hgap_nonneg :
      0 ≤ (g (x (k + 1))).toReal - (g xStar).toReal := by
    have htoReal :=
      EReal.toReal_le_toReal hopt
        (‹IsProperExtendedRealFunction g›.ne_bot xStar)
        (mem_effective_domain.mp hxNext_eff).ne
    nlinarith
  have hsq :
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
    have hgap_scaled_nonneg :
        0 ≤ 2 * (c : ℝ) * ((g (x (k + 1))).toReal - (g xStar).toReal) := by
      have hc_pos : 0 < 2 * (c : ℝ) := by
        nlinarith [show 0 < (c : ℝ) from c.2]
      nlinarith
    have hdrop :
        0 ≤ ‖x k - xStar‖ ^ (2 : ℕ) - ‖x (k + 1) - xStar‖ ^ (2 : ℕ) := by
      have hstep_norm_nonneg : 0 ≤ ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by positivity
      linarith [hstep, hgap_scaled_nonneg, hstep_norm_nonneg]
    nlinarith
  have hdist_norm : ‖x (k + 1) - xStar‖ ≤ ‖x k - xStar‖ := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq
    exact hsq
  simpa [dist_eq_norm] using hdist_norm

-- Proof sketch: apply the proximal optimality condition at each step to obtain a Fejér-type
-- descent inequality with respect to an arbitrary optimizer `xStar`; telescope the resulting
-- estimate over the first `k` steps and use monotonicity of `g (x^k)` to obtain the `O(1 / k)`
-- bound.
/-- Theorem 10.28 (1): along any proximal-point trajectory starting from `x^0 = x0`, for any
optimal point `xStar ∈ X^*` and any index `k ≥ 1`, the `k`-th iterate satisfies the `O(1 / k)`
objective-gap estimate relative to the canonical optimal value `g xStar`. -/
theorem proximal_point_method_objective_gap_le
    (htraj : is_proximal_point_trajectory g x0 c x)
    (xStar : E) (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    g (x k) - g xStar ≤
      ((((‖x0 - xStar‖ ^ (2 : ℕ)) / (2 * (c : ℝ) * (k : ℝ))) : ℝ) : EReal) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  let gap : ℕ → ℝ := fun i ↦ (g (x (i + 1))).toReal - (g xStar).toReal
  have hprefix :=
    proximal_point_prefix_gap_sum_le g x0 c htraj xStar hxStar K
  have hanti :=
    proximal_point_successor_objective_antitone g x0 c htraj
  have hsum_lower :
      ((K + 1 : ℝ) * gap K) ≤
        Finset.sum (Finset.range (K + 1)) gap := by
    calc
      ((K + 1 : ℝ) * gap K) = Finset.sum (Finset.range (K + 1)) fun _ ↦ gap K := by
        simp
      _ ≤ Finset.sum (Finset.range (K + 1)) gap := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi_le : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hi_obj : (g (x (K + 1))).toReal ≤ (g (x (i + 1))).toReal := hanti hi_le
        nlinarith
  have hsum_upper :
      2 * (c : ℝ) * Finset.sum (Finset.range (K + 1)) gap ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Dropping the terminal squared-distance term keeps the telescope valid.
    nlinarith [hprefix, sq_nonneg ‖x (K + 1) - xStar‖]
  have hc_pos : 0 < 2 * (c : ℝ) * (K + 1 : ℝ) := by
    exact mul_pos (by nlinarith [show 0 < (c : ℝ) from c.2]) (by exact_mod_cast Nat.succ_pos K)
  have hreal :
      gap K ≤ ‖x0 - xStar‖ ^ (2 : ℕ) / (2 * (c : ℝ) * (K + 1 : ℝ)) := by
    have hmul :
        gap K * (2 * (c : ℝ) * (K + 1 : ℝ)) ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
      have hc_nonneg : 0 ≤ 2 * (c : ℝ) := by
        nlinarith [show 0 < (c : ℝ) from c.2]
      calc
        gap K * (2 * (c : ℝ) * (K + 1 : ℝ))
            =
          2 * (c : ℝ) * ((K + 1 : ℝ) * gap K) := by ring
        _ ≤ 2 * (c : ℝ) * Finset.sum (Finset.range (K + 1)) gap := by
          exact mul_le_mul_of_nonneg_left hsum_lower hc_nonneg
        _ ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := hsum_upper
    exact (le_div_iff₀ hc_pos).2 <| by
      simpa [gap, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hxNext_eff :
      x (K + 1) ∈ effective_domain g :=
    proximal_point_trajectory_mem_effective_domain g x0 c htraj
      (Nat.succ_le_succ (Nat.zero_le K))
  have hxNext_val :
      g (x (K + 1)) = ((((g (x (K + 1))).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  have hxStar_eff : xStar ∈ effective_domain g :=
    optimal_point_mem_effective_domain g hxStar
  have hxStar_val :
      g xStar = ((((g xStar).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  -- Rewrite both finite objective values to `ℝ` and cast the final real estimate back to `EReal`.
  have hreal' :
      (g (x (K + 1))).toReal - (g xStar).toReal ≤
        ‖x0 - xStar‖ ^ (2 : ℕ) / (2 * (c : ℝ) * (K + 1 : ℝ)) := by
    simpa [gap] using hreal
  have hxTarget_val :
      g (x (1 + K)) = ((((g (x (1 + K))).toReal : ℝ)) : EReal) := by
    simpa [Nat.add_comm] using hxNext_val
  rw [hxTarget_val, hxStar_val]
  simpa [Nat.add_comm, EReal.coe_sub] using (EReal.coe_le_coe hreal')

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable (x0 : E) (c : PosReal)

local notation "x" => proximal_point_method g x0 c
local notation "XStar" => unconstrained_problem_solutions g

/-- Helper for Theorem 10.28: every sequential cluster point of the proximal-point method belongs
to the canonical optimizer set `X^*`. -/
lemma cluster_point_mem_optimal_set_of_proximal_point_method
    {xStar0 xBar : E}
    (hxStar0 : xStar0 ∈ XStar)
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    xBar ∈ XStar := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  let htraj := proximal_point_method_is_proximal_point_trajectory g x0 c
  have hxStar0_eff : xStar0 ∈ effective_domain g :=
    optimal_point_mem_effective_domain g hxStar0
  have hxStar0_val :
      g xStar0 = ((((g xStar0).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxStar0_eff).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  let gap : ℕ → ℝ := fun n ↦ (g (x (ψ (n + 1)))).toReal - (g xStar0).toReal
  have hgap_nonneg : ∀ n, 0 ≤ gap n := by
    intro n
    have hψ_ge : n + 1 ≤ ψ (n + 1) := StrictMono.id_le hψmono (n + 1)
    have hkψ : 1 ≤ ψ (n + 1) := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) hψ_ge
    have hopt :
        g xStar0 ≤ g (x (ψ (n + 1))) :=
      (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar0) (x (ψ (n + 1)))
    have hxψ_eff :
        x (ψ (n + 1)) ∈ effective_domain g :=
      proximal_point_trajectory_mem_effective_domain g x0 c htraj hkψ
    have htoReal :=
      EReal.toReal_le_toReal hopt
        (‹IsProperExtendedRealFunction g›.ne_bot xStar0)
        (mem_effective_domain.mp hxψ_eff).ne
    nlinarith
  have hgap_le :
      ∀ n,
        gap n ≤
          (‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ))) / (ψ (n + 1) : ℝ) := by
    intro n
    have hψ_ge : n + 1 ≤ ψ (n + 1) := StrictMono.id_le hψmono (n + 1)
    have hkψ : 1 ≤ ψ (n + 1) := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) hψ_ge
    have hbound :=
      proximal_point_method_objective_gap_le g x0 c htraj xStar0 hxStar0 (ψ (n + 1)) hkψ
    have hxψ_eff :
        x (ψ (n + 1)) ∈ effective_domain g :=
      proximal_point_trajectory_mem_effective_domain g x0 c htraj hkψ
    have hxψ_val :
        g (x (ψ (n + 1))) = ((((g (x (ψ (n + 1)))).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hxψ_eff).ne
          (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
    rw [hxψ_val, hxStar0_val] at hbound
    have hbound_real :
        gap n ≤ ‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ) * (ψ (n + 1) : ℝ)) := by
      simpa [gap, EReal.coe_sub] using EReal.coe_le_coe_iff.mp hbound
    have hψ_ne_zero : (ψ (n + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.succ_pos' hψ_ge))
    have hdiv :
        ‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ) * (ψ (n + 1) : ℝ)) =
          (‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ))) / (ψ (n + 1) : ℝ) := by
      have htwo_c_ne_zero : (2 * (c : ℝ)) ≠ 0 := by
        nlinarith [show 0 < (c : ℝ) from c.2]
      field_simp [hψ_ne_zero, htwo_c_ne_zero]
    simpa [hdiv] using hbound_real
  have hψtail_atTop : Filter.Tendsto (fun n ↦ ψ (n + 1)) Filter.atTop Filter.atTop :=
    hψmono.tendsto_atTop.comp
      (by
        have hid : Filter.Tendsto (fun n : ℕ ↦ n) Filter.atTop Filter.atTop := by
          exact Filter.tendsto_id
        exact Filter.tendsto_atTop_mono Nat.le_succ hid)
  have hbound_tendsto :
      Filter.Tendsto
        (fun n ↦ (‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ))) / (ψ (n + 1) : ℝ))
        Filter.atTop
        (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (‖x0 - xStar0‖ ^ (2 : ℕ) / (2 * (c : ℝ)))).comp
      hψtail_atTop
  have hgap_tendsto : Filter.Tendsto gap Filter.atTop (nhds 0) := by
    -- The sublinear rate squeezes the objective gaps of the convergent subsequence to zero.
    exact squeeze_zero hgap_nonneg hgap_le hbound_tendsto
  have hsubseq_obj_real :
      Filter.Tendsto (fun n ↦ (g (x (ψ (n + 1)))).toReal) Filter.atTop
        (nhds ((g xStar0).toReal)) := by
    simpa [gap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hgap_tendsto.const_add ((g xStar0).toReal)
  have hsubseq_obj :
      Filter.Tendsto (fun n ↦ g (x (ψ (n + 1)))) Filter.atTop (nhds (g xStar0)) := by
    have hxvals :
        (fun n ↦ g (x (ψ (n + 1)))) =
          fun n ↦ ((((g (x (ψ (n + 1)))).toReal : ℝ)) : EReal) := by
      ext n
      have hψ_ge : n + 1 ≤ ψ (n + 1) := StrictMono.id_le hψmono (n + 1)
      have hkψ : 1 ≤ ψ (n + 1) := by
        exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) hψ_ge
      have hxψ_eff :
          x (ψ (n + 1)) ∈ effective_domain g :=
        proximal_point_trajectory_mem_effective_domain g x0 c htraj hkψ
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hxψ_eff).ne
          (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
    have hcoe :
        Filter.Tendsto
          (fun n ↦ ((((g (x (ψ (n + 1)))).toReal : ℝ)) : EReal))
          Filter.atTop
          (nhds ((((g xStar0).toReal : ℝ)) : EReal)) := by
      exact (continuous_coe_real_ereal.tendsto (((g xStar0).toReal : ℝ))).comp hsubseq_obj_real
    rw [hxStar0_val]
    simpa [hxvals]
  have hclosed : LowerSemicontinuous g := Fact.out
  have hxBar_le_opt :
      g xBar ≤ g xStar0 := by
    have htail_tendsto :
        Filter.Tendsto (fun n ↦ x (ψ (n + 1))) Filter.atTop (nhds xBar) :=
      hψtendsto.comp
        (by
          have hid : Filter.Tendsto (fun n : ℕ ↦ n) Filter.atTop Filter.atTop := by
            exact Filter.tendsto_id
          exact Filter.tendsto_atTop_mono Nat.le_succ hid)
    have hxBar_le_liminf :
        g xBar ≤ Filter.liminf (fun n ↦ g (x (ψ (n + 1)))) Filter.atTop := by
      calc
        g xBar ≤ Filter.liminf g (nhds xBar) := hclosed.le_liminf xBar
        _ ≤ Filter.liminf g (Filter.map (fun n ↦ x (ψ (n + 1))) Filter.atTop) := by
          exact Filter.liminf_le_liminf_of_le htail_tendsto
        _ = Filter.liminf (fun n ↦ g (x (ψ (n + 1)))) Filter.atTop := by
          rfl
    simpa [hsubseq_obj.liminf_eq] using hxBar_le_liminf
  -- Comparing the cluster-point value with the optimizer value recovers global optimality.
  refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
  intro y
  exact le_trans hxBar_le_opt ((mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar0) y)

-- Proof sketch: apply `proximal_point_method_fejer_monotonicity` to the canonical bridge
-- `proximal_point_method_is_proximal_point_trajectory`. In a proper metric space this yields the
-- boundedness/cluster-point input needed for the Chapter 8 Fejér-convergence layer. Then combine
-- clause (1), lower semicontinuity of `g`, and optimality of accumulation points to conclude that
-- the whole sequence converges to a point of the canonical optimizer set `X^*`.
/-- Theorem 10.28 (2): if the unconstrained optimizer set `X^*` is nonempty, then the
proximal-point iterates converge to some point of `X^*`. -/
theorem proximal_point_method_tendsto_optimal_point
    (hXStar_nonempty : Set.Nonempty XStar) :
    ∃ xStar ∈ XStar, Filter.Tendsto x Filter.atTop (nhds xStar) := by
  obtain ⟨xStar0, hxStar0⟩ := hXStar_nonempty
  let htraj := proximal_point_method_is_proximal_point_trajectory g x0 c
  have hFejer :
      IsFejerMonotoneWithRespectTo x XStar :=
    proximal_point_method_fejer_monotonicity g x0 c htraj
  let r : ℝ := dist (x 0) xStar0
  have hball : ∀ n : ℕ, x n ∈ Metric.closedBall xStar0 r := by
    intro n
    have hdist : dist (x n) xStar0 ≤ dist (x 0) xStar0 := by
      induction n with
      | zero =>
          exact le_rfl
      | succ n ih =>
          exact le_trans (hFejer xStar0 hxStar0 n) ih
    simpa [r, Metric.mem_closedBall] using hdist
  have hfreq :
      ∃ᶠ n in Filter.atTop, x n ∈ Metric.closedBall xStar0 r :=
    (Filter.Eventually.of_forall hball).frequently
  rcases (isCompact_closedBall xStar0 r).exists_mapClusterPt_of_frequently hfreq with
    ⟨xBar, -, hxBar⟩
  have hlimitPoints_subset :
      {y : E | MapClusterPt y Filter.atTop x} ⊆ XStar := by
    intro y hy
    exact cluster_point_mem_optimal_set_of_proximal_point_method
      g x0 c hxStar0 hy
  have hlimitPoint : ∃ y : E, MapClusterPt y Filter.atTop x := ⟨xBar, hxBar⟩
  obtain ⟨xStar, hxStar, hxTendsto⟩ :=
    tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo hFejer hlimitPoints_subset hlimitPoint
  exact ⟨xStar, hlimitPoints_subset hxStar, hxTendsto⟩

end
