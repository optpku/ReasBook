/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.10 is `source-facing` in the chapter Fenchel/subdifferential API. A semantic
`lean_leansearch` recall did not expose a single direct Fenchel--Young/subdifferential owner, and
local verification shows that the `core/canonical` owners are already upstream:
`IsProperExtendedRealFunction` from Definition 2.5, `is_convex_function` from Definition 2.6,
`subdifferential` from Definition 3.2, and `conjugate_function` from Definition 4.1, together
with the bridge theorems
`self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex` from Theorem 4.11 and
`isProperExtendedRealFunction_conjugate_function` from Theorem 4.15. The primitive data here are
only `f`, `x`, `y`, and the source-active hypotheses; the subdifferential and conjugate
expressions are derived views through those owners, so this file keeps only the equivalence
theorems and no parallel local wrappers. -/

recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall conjugate_function

/-- Helper for Theorem 4.10: a subgradient controls every term in the supremum defining
`conjugate_function f y` by the value attained at the supporting point `x`. -/
lemma conjugateObjective_le_pairingSub_of_memSubdifferential
    (f : E → EReal) (hf_ne_bot : ∀ z, f z ≠ ⊥) {x : E} {y : Module.Dual ℝ E}
    (hy : y ∈ ∂f(x)) (z : E) :
    ((y z : EReal) - f z) ≤ (y x : EReal) - f x := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hy
  rcases hy with ⟨hx, hy⟩
  by_cases hz : z ∈ effective_domain f
  · have hfx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
    have hfz_top : f z ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hz)
    lift f x to ℝ using ⟨hfx_top, hf_ne_bot x⟩ with fx hfx
    lift f z to ℝ using ⟨hfz_top, hf_ne_bot z⟩ with fz hfz
    -- Move the subgradient inequality to `ℝ`, where the rearrangement is linear.
    have hy_real : fx + y (z - x) ≤ fz := by
      have hy_ereal : (((fx + y (z - x) : ℝ) : EReal) ≤ (fz : EReal)) := by
        simpa [← hfx, ← hfz, ge_iff_le, EReal.coe_add] using hy z hz
      exact EReal.coe_le_coe_iff.mp hy_ereal
    have hpair_real : y z - fz ≤ y x - fx := by
      have hy_real' : fx + (y z - y x) ≤ fz := by
        simpa [map_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_real
      linarith
    have hpair_ereal :
        (((y z - fz : ℝ) : EReal) ≤ ((y x - fx : ℝ) : EReal)) :=
      EReal.coe_le_coe hpair_real
    simpa [hfx, hfz, EReal.coe_sub] using hpair_ereal
  · have hfz_top : f z = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hz))
    -- Outside the effective domain the objective is `⊥`, so the estimate is automatic.
    simp [hfz_top]

/-- Helper for Theorem 4.10: an upper bound on `conjugate_function f y` by the value at `x`
implies the full subgradient inequality at `x`. -/
lemma mem_subdifferential_of_conjugate_le_pairingSub
    (f : E → EReal) (hf_ne_bot : ∀ z, f z ≠ ⊥) {x : E} {y : Module.Dual ℝ E}
    (hx : x ∈ effective_domain f) (hle : conjugate_function f y ≤ (y x : EReal) - f x) :
    y ∈ ∂ f(x) := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hx, ?_⟩
  intro z hz
  have hz_term : ((y z : EReal) - f z) ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self z)
  have hpair : ((y z : EReal) - f z) ≤ (y x : EReal) - f x := hz_term.trans hle
  have hfx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  have hfz_top : f z ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hz)
  lift f x to ℝ using ⟨hfx_top, hf_ne_bot x⟩ with fx hfx
  lift f z to ℝ using ⟨hfz_top, hf_ne_bot z⟩ with fz hfz
  -- Convert the supremum bound to a real inequality and rearrange it back to the subgradient form.
  have hpair_real : y z - fz ≤ y x - fx := by
    have hpair_ereal : (((y z - fz : ℝ) : EReal) ≤ ((y x - fx : ℝ) : EReal)) := by
      simpa [hfx, hfz, EReal.coe_sub] using hpair
    exact EReal.coe_le_coe_iff.mp hpair_ereal
  have hsubgrad_real : fx + y (z - x) ≤ fz := by
    have hsubgrad_real' : fx + (y z - y x) ≤ fz := by
      linarith
    simpa [map_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsubgrad_real'
  have hsubgrad_ereal : (((fx + y (z - x) : ℝ) : EReal) ≤ (fz : EReal)) :=
    EReal.coe_le_coe hsubgrad_real
  simpa [ge_iff_le, hfx, hfz, EReal.coe_add] using hsubgrad_ereal

-- Proof sketch: the Chapter 4 owner/API layer for the Fenchel--Young equality criterion uses only
-- the no-`⊥` hypothesis on `f`; the textbook proper/convex form is packaged below as a separate
-- source-facing corollary.
/-- Theorem 4.10, Chapter 4 owner form: if `f` never takes the value `⊥`, then
Fenchel--Young equality at
`(x, y)` is equivalent to `y` belonging to `∂ f(x)`. -/
theorem pairing_eq_add_conjugate_iff_mem_subdifferential
    (f : E → EReal) (hf_ne_bot : ∀ z, f z ≠ ⊥) (x : E) (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔ y ∈ ∂ f(x) := by
  constructor
  · intro hEq
    have hx : x ∈ effective_domain f := by
      by_contra hx
      have hfx_top : f x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hx))
      by_cases hconj_bot : conjugate_function f y = ⊥
      · have hyx_bot : (y x : EReal) = ⊥ := by
          calc
            (y x : EReal) = f x + conjugate_function f y := hEq
            _ = ⊥ := by simp [hfx_top, hconj_bot]
        exact EReal.coe_ne_bot (y x) hyx_bot
      · have hyx_top : (y x : EReal) = ⊤ := by
          calc
            (y x : EReal) = f x + conjugate_function f y := hEq
            _ = ⊤ := by simp [hfx_top, hconj_bot]
        exact EReal.coe_ne_top (y x) hyx_top
    have hfx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
    -- Rewrite the displayed equality as the needed upper bound on the conjugate value.
    have hsum : conjugate_function f y + f x ≤ (y x : EReal) := by
      simpa [add_comm] using hEq.ge
    have hle : conjugate_function f y ≤ (y x : EReal) - f x := by
      exact (EReal.le_sub_iff_add_le (.inl (hf_ne_bot x)) (.inl hfx_top)).2 hsum
    exact mem_subdifferential_of_conjugate_le_pairingSub f hf_ne_bot hx hle
  · intro hy
    have hx : x ∈ effective_domain f := by
      rw [mem_subdifferential] at hy
      exact hy.1
    have hobj :
        conjugate_function f y ≤ (y x : EReal) - f x := by
      rw [conjugate_function_apply]
      refine sSup_le ?_
      rintro _ ⟨z, rfl⟩
      exact conjugateObjective_le_pairingSub_of_memSubdifferential f hf_ne_bot hy z
    have hterm : ((y x : EReal) - f x) ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self x)
    have hterm_ne_bot : ((y x : EReal) - f x) ≠ ⊥ := by
      have hfx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
      lift f x to ℝ using ⟨hfx_top, hf_ne_bot x⟩ with fx hfx
      simpa [← hfx, EReal.coe_sub] using EReal.coe_ne_bot (y x - fx)
    have hconj_ne_bot : conjugate_function f y ≠ ⊥ := by
      exact bot_lt_iff_ne_bot.mp
        ((bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hterm)
    -- Compare the lower bound from the defining supremum with the upper bound from subgradient
    -- membership, then cancel `f x`.
    have hlower : (y x : EReal) ≤ f x + conjugate_function f y := by
      have hlower' : (y x : EReal) ≤ conjugate_function f y + f x := by
        exact (EReal.sub_le_iff_le_add (.inl (hf_ne_bot x)) (.inr hconj_ne_bot)).1 hterm
      simpa [add_comm] using hlower'
    have hupper : f x + conjugate_function f y ≤ (y x : EReal) := by
      have hupper' : conjugate_function f y + f x ≤ (y x : EReal) :=
        EReal.add_le_of_le_sub hobj
      simpa [add_comm] using hupper'
    exact le_antisymm hlower hupper

/-- Source-facing corollary: properness already contains the active
no-`⊥` hypothesis for Fenchel--Young equality, so the convexity assumption from the textbook
statement is intentionally omitted from this canonical API surface. -/
theorem pairing_eq_add_conjugate_iff_mem_subdifferential_of_proper
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x : E)
    (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔ y ∈ ∂ f(x) := by
  -- Properness supplies the only hypothesis needed by the owner theorem.
  simpa using pairing_eq_add_conjugate_iff_mem_subdifferential f hf_proper.ne_bot x y

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Theorem 4.10: a proper function has a conjugate that never takes the value `⊥`. -/
lemma conjugateFunctionNeBot_ofProper
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (y : Module.Dual ℝ E) :
    conjugate_function f y ≠ ⊥ := by
  rcases hf_proper.effective_domain_nonempty with ⟨z, hz⟩
  have hz_term : ((y z : EReal) - f z) ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self z)
  have hfz_top : f z ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hz)
  lift f z to ℝ using ⟨hfz_top, hf_proper.ne_bot z⟩ with fz hfz
  have hz_term' : ((y z : EReal) - (fz : EReal)) ≤ conjugate_function f y := by
    simpa [← hfz] using hz_term
  have hz_term_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
    simpa [← hfz, EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
  -- One finite term in the defining supremum prevents the conjugate value from being `⊥`.
  exact bot_lt_iff_ne_bot.mp
    ((bot_lt_iff_ne_bot.mpr hz_term_ne_bot).trans_le (by simpa [← hfz] using hz_term'))

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 4.10: for finite `c` and non-`⊥` summands, the equality `c = a + b`
is equivalent to the subtraction form `a = c - b`. -/
lemma eq_add_iff_left_eq_sub_of_ne_bot
    {a b c : EReal} (ha_ne_bot : a ≠ ⊥) (hb_ne_bot : b ≠ ⊥) (hc_ne_top : c ≠ ⊤) :
    c = a + b ↔ a = c - b := by
  constructor
  · intro hEq
    refine le_antisymm ?_ ?_
    · exact
        (EReal.le_sub_iff_add_le (a := a) (b := b) (c := c)
          (.inl hb_ne_bot) (.inr hc_ne_top)).2 hEq.ge
    · exact
        (EReal.sub_le_iff_le_add (a := c) (b := b) (c := a)
          (.inl hb_ne_bot) (.inr ha_ne_bot)).2 hEq.le
  · intro hEq
    refine le_antisymm ?_ ?_
    · exact
        (EReal.sub_le_iff_le_add (a := c) (b := b) (c := a)
          (.inl hb_ne_bot) (.inr ha_ne_bot)).1 hEq.ge
    · exact
        (EReal.add_le_of_le_sub (a := a) (b := c) (c := b) hEq.le)

/-- Helper for Theorem 4.10: under properness, closedness, and convexity, both the primal value
`f x` and the double-conjugate value at `x` are characterized by the same dual argmax equation. -/
lemma primalSub_eq_biconjugateSub_iff_of_proper_closedConvex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (x : E) (y : Module.Dual ℝ E) :
    f x = (y x : EReal) - conjugate_function f y ↔
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
        (y x : EReal) - conjugate_function f y := by
  have hprimal :
      f x = (y x : EReal) - conjugate_function f y ↔
        IsMaxOn
          (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
          Set.univ y := by
    simpa using
      (self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex
        f hf_proper hf_closed hf_convex x y)
  have hdual :
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          (y x : EReal) - conjugate_function f y ↔
        IsMaxOn
          (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
          Set.univ y := by
    simpa using
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
        (conjugate_function f) y (Module.Dual.eval ℝ E x))
  exact hprimal.trans hdual.symm

/-- Helper for Theorem 4.10: properness and convexity ensure that the biconjugate value at `x`
is not `⊥`. -/
lemma biconjugateValue_ne_bot_of_proper_convex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f)
    (x : E) :
    conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) ≠ ⊥ := by
  have hproper_conj : IsProperExtendedRealFunction (conjugate_function f) :=
    isProperExtendedRealFunction_conjugate_function f hf_proper hf_convex
  exact conjugate_function_ne_bot (conjugate_function f) hproper_conj (Module.Dual.eval ℝ E x)

/-- Helper for Theorem 4.10: under properness, closedness, and convexity, the primal
Fenchel--Young equality is equivalent to the conjugate-side Fenchel--Young equality. -/
lemma primalPairingEq_iff_conjugatePairingEq_of_proper_closedConvex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E)
    (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔
      (y x : EReal) = conjugate_function f y +
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) := by
  have hyx_ne_top : (y x : EReal) ≠ ⊤ := EReal.coe_ne_top (y x)
  have hfy_ne_bot : conjugate_function f y ≠ ⊥ :=
    conjugateFunctionNeBot_ofProper f hf_proper y
  have hbiconj_ne_bot :
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) ≠ ⊥ :=
    biconjugateValue_ne_bot_of_proper_convex f hf_proper hf_convex x
  have hprimal_add :
      (y x : EReal) = f x + conjugate_function f y ↔
        f x = (y x : EReal) - conjugate_function f y :=
    eq_add_iff_left_eq_sub_of_ne_bot (hf_proper.ne_bot x) hfy_ne_bot hyx_ne_top
  have hdual_add :
      (y x : EReal) = conjugate_function f y +
          conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) ↔
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          (y x : EReal) - conjugate_function f y := by
    simpa [add_comm] using
      (eq_add_iff_left_eq_sub_of_ne_bot hbiconj_ne_bot hfy_ne_bot hyx_ne_top)
  exact hprimal_add.trans <| (primalSub_eq_biconjugateSub_iff_of_proper_closedConvex
    f hf_proper hf_closed hf_convex x y).trans hdual_add.symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 4.10: the owner theorem applied to `conjugate_function f` rewrites the
conjugate-side Fenchel--Young equality as membership in `∂ (conjugate_function f)(y)`. -/
lemma conjugatePairingEq_iff_eval_mem_subdifferential
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x : E)
    (y : Module.Dual ℝ E) :
    (y x : EReal) = conjugate_function f y +
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) ↔
      Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) := by
  let g : Module.Dual ℝ E → EReal := conjugate_function f
  have hg_ne_bot : ∀ z : Module.Dual ℝ E, g z ≠ ⊥ := fun z ↦
    conjugateFunctionNeBot_ofProper f hf_proper z
  simpa [g, add_comm] using
    (pairing_eq_add_conjugate_iff_mem_subdifferential
      g hg_ne_bot y (Module.Dual.eval ℝ E x))

-- Proof sketch: clause (iii) is formalized by transporting the same Fenchel--Young equality
-- through the shared dual argmax characterization from Theorem 4.11, then repackage the result
-- with the conjugate-side owner theorem.
/-- Under properness, convexity, and lower semicontinuity,
Fenchel--Young equality at `(x, y)` is
equivalent to the canonical double-dual image of `x` lying in `∂ (conjugate_function f)(y)`. -/
theorem pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E)
    (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔
      Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) := by
  -- Rewrite first to the conjugate-side Fenchel--Young equality, then apply the owner theorem on
  -- `conjugate_function f`.
  exact
    (primalPairingEq_iff_conjugatePairingEq_of_proper_closedConvex
      f hf_proper hf_closed hf_convex x y).trans
      (conjugatePairingEq_iff_eval_mem_subdifferential f hf_proper x y)

end
