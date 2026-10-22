/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.List.TFAE
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_27
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

recall effective_domain
recall subdifferentialAt
recall conjugate_function
recall conjugate_function_apply

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.13 is `source-facing` in the chapter's convex Lipschitz/conjugacy interface.
Domain sampling identifies the owner abstractions upstream as Definition 2.1's
`effective_domain`, Theorem 3.4's strong-dual bridge `subdifferentialAt`, and Definition 4.1's
`conjugate_function`. The primitive data here are only the convex function `f` and the radius `L`;
the subgradient clause is expressed directly through `subdifferentialAt`, while the conjugate-domain
clause is the continuous-dual restriction of the owner `conjugate_function`. This file therefore
keeps the textbook `TFAE` statement as the main entry, together with direct companion equivalences
for the two reusable atomic clauses, and no parallel local wrappers. -/

-- Proof sketch: identify clause (i) with clause (ii) using the global/full-domain specialization
-- of the Chapter 3 bounded-subdifferential characterization of Lipschitz continuity. For
-- `(iii) → (ii)`, use the conjugate-subgradient theorem: every `g ∈ subdifferentialAt f x` lies
-- in the effective domain of `f*`, hence in the dual closed ball. For `(i) → (iii)`, bound
-- `-f x` below by `-f 0 - L * ‖x‖` and then show that if `‖y‖ > L`, scaling along a unit vector
-- realizing `y` forces the supremum defining `f* y` to be `⊤`.
/-- Helper for Theorem 4.13: every real-valued strong-dual subgradient belongs to the effective
domain of the conjugate. -/
private lemma mem_effectiveDomain_conjugate_of_mem_subdifferentialAt
    {f : E → ℝ} {x : E} {g : StrongDual ℝ E} (hg : g ∈ subdifferentialAt f x) :
    g ∈ effective_domain
      (fun y : StrongDual ℝ E ↦ conjugate_function (fun z ↦ (f z : EReal)) y) := by
  -- Rewrite to the owner subdifferential and bound the defining supremum termwise by the support
  -- value at `x`.
  have hg_owner : (g : Module.Dual ℝ E) ∈ ∂ (fun z ↦ (f z : EReal))(x) := by
    simpa [subdifferentialAt] using hg
  have hconj_upper :
      conjugate_function (fun z ↦ (f z : EReal)) (g : Module.Dual ℝ E) ≤
        (g x : EReal) - (f x : EReal) := by
    rw [conjugate_function_apply]
    refine sSup_le ?_
    rintro _ ⟨z, rfl⟩
    have hsub_real :
        (g : Module.Dual ℝ E) (z - x) ≤ f z - f x := by
      simpa using
        subgradient_eval_le_toReal_sub
          (f := fun y ↦ (f y : EReal))
          x
          z
          (h_ne_bot := by intro y hy; simp)
          (by simp [effective_domain])
          (by simp [effective_domain])
          hg_owner
    have hsub_real' : (g : Module.Dual ℝ E) z - g x ≤ f z - f x := by
      simpa using hsub_real
    have hpair_real : (g : Module.Dual ℝ E) z - f z ≤ g x - f x := by
      linarith
    have hpair_ereal :
        (((g z - f z : ℝ) : EReal)) ≤ (((g x - f x : ℝ) : EReal)) := by
      exact_mod_cast hpair_real
    simpa [EReal.coe_sub] using hpair_ereal
  -- The support value at the finite point `x` is finite, so the conjugate lies in the effective
  -- domain.
  refine mem_effective_domain.mpr ?_
  have hfinite : ((g x : EReal) - (f x : EReal)) < ⊤ := by
    simpa [EReal.coe_sub] using (EReal.coe_lt_top (g x - f x))
  exact lt_of_le_of_lt hconj_upper hfinite

/-- Helper for Theorem 4.13: if `‖y‖ > L`, then some direction gives a positive gap
`y x - L * ‖x‖`. -/
private lemma exists_eval_sub_lipschitz_mul_norm_pos_of_lt_norm
    {L : NNReal} {y : StrongDual ℝ E} (hy : (L : ℝ) < ‖y‖) :
    ∃ x : E, 0 < y x - (L : ℝ) * ‖x‖ := by
  -- First find a vector where the functional grows faster than the slope `L`.
  rcases y.exists_mul_lt_of_lt_opNorm L.2 hy with ⟨x, hx⟩
  by_cases hsign : 0 ≤ y x
  · -- In the nonnegative case, the absolute value disappears immediately.
    refine ⟨x, ?_⟩
    calc
      0 < ‖y x‖ - (L : ℝ) * ‖x‖ := sub_pos.mpr hx
      _ = y x - (L : ℝ) * ‖x‖ := by rw [Real.norm_of_nonneg hsign]
  · -- Otherwise flip the direction to make the evaluation positive without changing the norm.
    refine ⟨-x, ?_⟩
    have hneg : y x < 0 := lt_of_not_ge hsign
    calc
      0 < ‖y x‖ - (L : ℝ) * ‖x‖ := sub_pos.mpr hx
      _ = (-y x) - (L : ℝ) * ‖x‖ := by rw [Real.norm_eq_abs, abs_of_neg hneg]
      _ = y (-x) - (L : ℝ) * ‖-x‖ := by simp

/-- Helper for Theorem 4.13: along a natural ray, the conjugate integrand dominates the linear
gap coming from the Lipschitz estimate. -/
private lemma lipschitzConjugateIntegrand_natSmul_lower
    {f : E → ℝ} {L : NNReal} (hLip : LipschitzWith L f)
    (y : StrongDual ℝ E) (x : E) (n : ℕ) :
    (((((n : ℝ) * (y x - (L : ℝ) * ‖x‖) - f 0) : ℝ) : EReal))
      ≤ (y ((n : ℝ) • x) : EReal) - (f ((n : ℝ) • x) : EReal) := by
  -- The global Lipschitz estimate bounds `f ((n : ℝ) • x)` from above by `f 0 + L * ‖(n : ℝ) • x‖`.
  have hdist : |f ((n : ℝ) • x) - f 0| ≤ (L : ℝ) * ‖(n : ℝ) • x‖ := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul ((n : ℝ) • x) 0
  have hf_upper : f ((n : ℝ) • x) ≤ f 0 + (L : ℝ) * ‖(n : ℝ) • x‖ := by
    have hle : f ((n : ℝ) • x) - f 0 ≤ (L : ℝ) * ‖(n : ℝ) • x‖ := by
      exact le_trans (le_abs_self _) hdist
    linarith
  have hn : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  -- Rewrite both sides into the same real normal form and compare them directly.
  have hreal :
      (n : ℝ) * (y x - (L : ℝ) * ‖x‖) - f 0 ≤ y ((n : ℝ) • x) - f ((n : ℝ) • x) := by
    have hy_smul : y ((n : ℝ) • x) = (n : ℝ) * y x := by
      simp
    have hnorm_smul : ‖(n : ℝ) • x‖ = (n : ℝ) * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hn]
    have hf_upper' : f ((n : ℝ) • x) ≤ f 0 + (L : ℝ) * ((n : ℝ) * ‖x‖) := by
      simpa [hnorm_smul] using hf_upper
    rw [hy_smul]
    linarith
  have hrealEReal :
      (((((n : ℝ) * (y x - (L : ℝ) * ‖x‖) - f 0) : ℝ) : EReal))
        ≤ ((((y ((n : ℝ) • x) - f ((n : ℝ) • x)) : ℝ) : EReal)) := by
    exact_mod_cast hreal
  simpa using hrealEReal

/-- Helper for Theorem 4.13: if `f` is globally `L`-Lipschitz and `‖y‖ > L`, then the conjugate
value at `y` is `⊤`. -/
private lemma conjugate_function_eq_top_of_lipschitzWith_lt_norm
    {f : E → ℝ} {L : NNReal} {y : StrongDual ℝ E}
    (hLip : LipschitzWith L f) (hy : (L : ℝ) < ‖y‖) :
    conjugate_function (fun x ↦ (f x : EReal)) y = ⊤ := by
  -- Route correction: prove unboundedness of the defining supremum directly along a ray instead
  -- of importing the later norm-conjugate theorem.
  rw [conjugate_function_apply]
  rcases exists_eval_sub_lipschitz_mul_norm_pos_of_lt_norm (L := L) hy with ⟨x, hx⟩
  let δ : ℝ := y x - (L : ℝ) * ‖x‖
  have hδ : 0 < δ := hx
  -- Every finite threshold is exceeded by some large enough natural multiple of `x`.
  refine (sSup_eq_top).2 ?_
  intro b hb
  rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((r + f 0) / δ)
  have hr_lt_scaled : r < (n : ℝ) * δ - f 0 := by
    have hn' : (r + f 0) / δ < (n : ℝ) := by
      exact_mod_cast hn
    have hscaled : r + f 0 < (n : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at hn'
      simpa [mul_comm] using hn'
    linarith
  refine ⟨_, Set.mem_range.mpr ⟨(n : ℝ) • x, rfl⟩, ?_⟩
  calc
    b < (r : EReal) := hbr
    _ < (((n : ℝ) * δ - f 0 : ℝ) : EReal) := by
      exact_mod_cast hr_lt_scaled
    _ ≤ (y ((n : ℝ) • x) : EReal) - (f ((n : ℝ) • x) : EReal) := by
      simpa [δ] using
        lipschitzConjugateIntegrand_natSmul_lower (f := f) (L := L) hLip y x n

/-- Helper for Theorem 4.13: the Chapter 3 Lipschitz/subgradient equivalence specialized to
`Set.univ`. -/
private theorem lipschitzWith_iff_subdifferentialAt_norm_le_core
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    LipschitzWith L f ↔ ∀ x : E, ∀ g ∈ subdifferentialAt f x, ‖g‖ ≤ L := by
  -- Specialize the Chapter 3 theorem to the everywhere-finite `EReal` lift on `Set.univ`.
  have hiff :=
    lipschitzOnWith_toReal_iff_subdifferential_norm_le_on_of_isOpen
      (f := fun x ↦ (f x : EReal))
      (X := Set.univ)
      (L := L)
      (h_ne_bot := by intro x hx; simp)
      (hf_convex := toERealIsConvexFunction hf)
      (hX_open := isOpen_univ)
      (hX_subset := by simp [effective_domain])
  simpa [subdifferentialAt] using hiff

/-- Helper for Theorem 4.13: global `L`-Lipschitz continuity is equivalent to the conjugate-domain
inclusion in the dual closed ball of radius `L`. -/
private theorem lipschitzWith_iff_conjugate_domain_subset_closedBall_core
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    LipschitzWith L f ↔
      effective_domain
          (fun y : StrongDual ℝ E ↦ conjugate_function (fun x ↦ (f x : EReal)) y) ⊆
        closedBall (0 : StrongDual ℝ E) L := by
  constructor
  · intro hLip y hy_dom
    -- Any domain point must lie in the closed ball, since outside points force `f* y = ⊤`.
    rw [mem_closedBall_zero_iff]
    by_contra hy_ball
    have hy_lt : (L : ℝ) < ‖y‖ := lt_of_not_ge hy_ball
    have htop :=
      conjugate_function_eq_top_of_lipschitzWith_lt_norm (f := f) (L := L) hLip hy_lt
    exact (ne_of_lt (mem_effective_domain.mp hy_dom)) (by simpa using htop)
  · intro hdom
    -- Domain inclusion gives the norm bound for every subgradient, then Chapter 3 closes the route.
    rw [lipschitzWith_iff_subdifferentialAt_norm_le_core f hf L]
    intro x g hg
    have hg_dom :
        g ∈ effective_domain
          (fun y : StrongDual ℝ E ↦ conjugate_function (fun z ↦ (f z : EReal)) y) :=
      mem_effectiveDomain_conjugate_of_mem_subdifferentialAt (f := f) hg
    have hg_ball : g ∈ closedBall (0 : StrongDual ℝ E) L := hdom hg_dom
    simpa [mem_closedBall_zero_iff] using hg_ball

/-- Theorem 4.13: for a convex real-valued function, the following are equivalent for the given
Lipschitz bound `L`: (i) `f` is globally `L`-Lipschitz, (ii) every subgradient of `f` has norm at
most `L`, and (iii) the effective domain of the conjugate `f*` is contained in the closed dual
ball of radius `L`. -/
theorem convex_lipschitz_tfae_subdifferential_norm_le_conjugate_domain_subset_closedBall
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    List.TFAE
      [LipschitzWith L f,
        ∀ x : E, ∀ g ∈ subdifferentialAt f x, ‖g‖ ≤ L,
        effective_domain (fun y : StrongDual ℝ E ↦ conjugate_function (fun x ↦ (f x : EReal)) y) ⊆
          closedBall (0 : StrongDual ℝ E) L] := by
  -- Assemble the `TFAE` from the two reusable companion equivalences.
  tfae_have 1 ↔ 2 := lipschitzWith_iff_subdifferentialAt_norm_le_core f hf L
  tfae_have 1 ↔ 3 := lipschitzWith_iff_conjugate_domain_subset_closedBall_core f hf L
  tfae_finish

/-- Companion bridge for Theorem 4.13: for a convex real-valued function, global
`LipschitzWith L` is equivalent to the pointwise bound `‖g‖ ≤ L` on every
`g ∈ subdifferentialAt f x`. -/
theorem lipschitzWith_iff_subdifferentialAt_norm_le_of_convexOn_univ
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    LipschitzWith L f ↔ ∀ x : E, ∀ g ∈ subdifferentialAt f x, ‖g‖ ≤ L := by
  -- Reuse the specialized Chapter 3 equivalence prepared for the main `TFAE`.
  simpa using lipschitzWith_iff_subdifferentialAt_norm_le_core f hf L

/-- Companion bridge for Theorem 4.13: for a convex real-valued function, global
`LipschitzWith L` is equivalent to the conjugate-domain inclusion
`effective_domain (fun y : StrongDual ℝ E ↦ conjugate_function (fun x ↦ (f x : EReal)) y) ⊆
closedBall 0 L`. -/
theorem lipschitzWith_iff_conjugate_domain_subset_closedBall_of_convexOn_univ
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    LipschitzWith L f ↔
      effective_domain
          (fun y : StrongDual ℝ E ↦ conjugate_function (fun x ↦ (f x : EReal)) y) ⊆
        closedBall (0 : StrongDual ℝ E) L := by
  -- Reuse the conjugate-domain companion equivalence already used in the main theorem.
  simpa using lipschitzWith_iff_conjugate_domain_subset_closedBall_core f hf L

end
