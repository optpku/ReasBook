/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.15 is `source-facing` in the Chapter 4 conjugacy API. Its primitive data are the
owner predicates `IsProperExtendedRealFunction` and `is_convex_function`, while the conjugate is
the Chapter 4 owner `conjugate_function` on the dual space from Definition 4.1. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall conjugate_function
recall conjugate_function_apply
recall conjugate_function_ne_bot_of_proper
recall mem_subdifferential
recall exists_subdifferentiable_point_in_effective_domain_of_proper_convex
recall subgradient_eval_le_toReal_sub

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 4.15: a subgradient at `x` bounds `conjugate_function f g` above by the
affine support value `(g x : EReal) - f x`. -/
lemma conjugate_function_le_pairing_sub_of_mem_subdifferential
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {x : E} {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    conjugate_function f g ≤ (g x : EReal) - f x := by
  have hx : x ∈ effective_domain f := by
    rw [mem_subdifferential] at hg
    exact hg.1
  have hne_bot : ∀ z ∈ effective_domain f, f z ≠ ⊥ := fun z _ ↦ hproper.ne_bot z
  -- Bound each term in the supremum either by the subgradient inequality or trivially off the
  -- effective domain.
  rw [conjugate_function_apply]
  refine sSup_le ?_
  rintro _ ⟨z, rfl⟩
  by_cases hz : z ∈ effective_domain f
  · have hsub_real :
        g (z - x) ≤ (f z).toReal - (f x).toReal :=
      subgradient_eval_le_toReal_sub f x z hne_bot hx hz hg
    have hpair_real : g z - (f z).toReal ≤ g x - (f x).toReal := by
      have hlin : g (z - x) = g z - g x := by
        simp
      linarith [hsub_real, hlin]
    have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt hx) (hproper.ne_bot x)).symm
    have hfz_eq : f z = (((f z).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt hz) (hproper.ne_bot z)).symm
    -- Normalize both function values to real coercions before converting the inequality back.
    change (g z : EReal) - f z ≤ (g x : EReal) - f x
    rw [hfx_eq, hfz_eq]
    simpa [EReal.coe_sub] using (EReal.coe_le_coe hpair_real)
  · have hzf_top : f z = ⊤ := by
      refine le_antisymm le_top (not_lt.mp ?_)
      simpa [mem_effective_domain] using hz
    simp [hzf_top]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 4.15: any subgradient witness gives a point of the effective domain of the
conjugate. -/
lemma mem_effective_domain_conjugate_function_of_mem_subdifferential
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {x : E} {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    g ∈ effective_domain (conjugate_function f) := by
  have hx : x ∈ effective_domain f := by
    rw [mem_subdifferential] at hg
    exact hg.1
  lift f x to ℝ using ⟨hx.ne, hproper.ne_bot x⟩ with fx hfx
  -- The affine support value at a finite point is itself finite.
  have hfinite : ((g x : EReal) - f x) < ⊤ := by
    rw [← hfx]
    simpa [EReal.coe_sub] using (EReal.coe_lt_top (g x - fx))
  -- Combine the upper bound from the subgradient inequality with finiteness of that support value.
  refine mem_effective_domain.mpr ?_
  exact
    lt_of_le_of_lt
      (conjugate_function_le_pairing_sub_of_mem_subdifferential f hproper hg) hfinite

-- Proof sketch: choose `x₀ ∈ effective_domain f` from properness. Then `(y x₀ : EReal) - f x₀`
-- is finite for every dual vector `y`, so `conjugate_function f y` is never `⊥` because it
-- dominates this affine value. For finiteness at some dual vector, choose a point of the effective
-- domain with a subgradient and use the subgradient inequality to bound the supremum defining the
-- conjugate above.
/-- Theorem 4.15: properness of conjugate functions. In the finite-dimensional real normed-space
setting of the chapter, the conjugate of a proper convex extended-real-valued function is proper.
-/
theorem isProperExtendedRealFunction_conjugate_function
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hconvex : is_convex_function f) :
    IsProperExtendedRealFunction (conjugate_function f) := by
  -- The `≠ ⊥` field comes from evaluating the conjugate at one finite primal point.
  refine ⟨conjugate_function_ne_bot_of_proper f hproper, ?_⟩
  -- For the finite-domain witness, choose any point with a nonempty subdifferential.
  rcases exists_subdifferentiable_point_in_effective_domain_of_proper_convex f hproper hconvex with
    ⟨x, _hx, hxsub⟩
  rcases hxsub with ⟨g, hg⟩
  exact ⟨g, mem_effective_domain_conjugate_function_of_mem_subdifferential f hproper hg⟩

/-- Instance form of Theorem 4.15 for automation-driven reuse of conjugate properness. -/
instance instIsProperExtendedRealFunctionConjugateFunction
    (f : E → EReal) [hproper : IsProperExtendedRealFunction f]
    (hconvex : is_convex_function f) :
    IsProperExtendedRealFunction (conjugate_function f) :=
  isProperExtendedRealFunction_conjugate_function f hproper hconvex

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Companion theorem for Theorem 4.15: the conjugate of a proper extended-real-valued function
never takes the value `-∞`. -/
theorem conjugate_function_ne_bot
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f) (y : Module.Dual ℝ E) :
    conjugate_function f y ≠ ⊥ := by
  rcases hproper.effective_domain_nonempty with ⟨z, hz⟩
  lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
  have hz' :
      ((y z : EReal) - f z) ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self z)
  have hterm_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
    rw [← hfz]
    simpa [EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
  exact bot_lt_iff_ne_bot.mp <| (bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hz'

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Companion theorem for Theorem 4.15: the effective domain of the conjugate of a proper convex
extended-real-valued function is nonempty. -/
theorem conjugate_function_effective_domain_nonempty
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hconvex : is_convex_function f) :
    (effective_domain (conjugate_function f)).Nonempty := by
  exact
    (isProperExtendedRealFunction_conjugate_function f hproper hconvex).effective_domain_nonempty

end
