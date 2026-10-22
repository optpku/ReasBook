/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Lemma_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 4.2 is `source-facing` in the chapter conjugacy API: it states the biconjugate
identity for a proper, closed, convex `EReal`-valued function. Chapter 2's
`IsProperExtendedRealFunction` and `is_convex_function` together with Mathlib's
`LowerSemicontinuous` and Definition 4.2's `biconjugate_function` (built on Definition 4.1's
`conjugate_function`) provide the ambient notions. The textbook proper/closed/convex statement
remains the unique labeled main entry in this item file: for general `EReal`-valued functions the
properness hypothesis is semantically active, because allowing `⊥` changes the biconjugate. -/
recall IsProperExtendedRealFunction
recall is_convex_function
recall biconjugate_function

-- Helper for Theorem 4.2: a separator on `E × ℝ` splits into its `E`-component plus its slope
-- in the vertical `ℝ`-direction.
private lemma prodSeparator_apply_eq_dual_add_smul
    (L : StrongDual ℝ (E × ℝ)) (z : E) (s : ℝ) :
    L (z, s) =
      ((L.comp (ContinuousLinearMap.inl ℝ E ℝ) : StrongDual ℝ E) : Module.Dual ℝ E) z +
        L (0, 1) * s := by
  -- Decompose `(z, s)` into its horizontal part and a vertical scalar multiple.
  have hdecomp : (z, s) = (z, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul]
  simp [smul_eq_mul, mul_comm]

-- Helper for Theorem 4.2: properness prevents `conjugate_function f` from taking the value `⊥`.
private lemma conjugateFunction_neBot_of_proper
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f) (y : Module.Dual ℝ E) :
    conjugate_function f y ≠ ⊥ := by
  rcases hproper.effective_domain_nonempty with ⟨z, hz⟩
  lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
  -- Evaluate the conjugate at one finite primal point.
  have hz' : ((y z : EReal) - f z) ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self z)
  have hterm_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
    rw [← hfz]
    simpa [EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
  exact bot_lt_iff_ne_bot.mp <| (bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hz'

-- Helper for Theorem 4.2: a subgradient at `x` bounds `conjugate_function f g` above by the
-- affine support value `(g x : EReal) - f x`.
private lemma conjugateFunction_le_pairingSub_of_memSubdifferential
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {x : E} {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    conjugate_function f g ≤ (g x : EReal) - f x := by
  have hx : x ∈ effective_domain f := by
    rw [mem_subdifferential] at hg
    exact hg.1
  have hne_bot : ∀ z ∈ effective_domain f, f z ≠ ⊥ := fun z _ ↦ hproper.ne_bot z
  -- Bound each conjugate witness either by the subgradient inequality or trivially off the domain.
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
      linarith
    have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt hx) (hproper.ne_bot x)).symm
    have hfz_eq : f z = (((f z).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt hz) (hproper.ne_bot z)).symm
    change (g z : EReal) - f z ≤ (g x : EReal) - f x
    rw [hfx_eq, hfz_eq]
    simpa [EReal.coe_sub] using (EReal.coe_le_coe hpair_real)
  · have hztop : f z = ⊤ := by
      simpa [mem_effective_domain] using hz
    simp [hztop]

/-- Helper for Theorem 4.2: a subgradient witness gives a point of the effective domain of the
conjugate. -/
private lemma mem_effectiveDomain_conjugateFunction_of_memSubdifferential
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {x : E} {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    g ∈ effective_domain (conjugate_function f) := by
  have hx : x ∈ effective_domain f := by
    rw [mem_subdifferential] at hg
    exact hg.1
  lift f x to ℝ using ⟨hx.ne, hproper.ne_bot x⟩ with fx hfx
  -- The supporting affine value at a finite primal point is itself finite.
  have hfinite : ((g x : EReal) - f x) < ⊤ := by
    rw [← hfx]
    simpa [EReal.coe_sub] using (EReal.coe_lt_top (g x - fx))
  refine mem_effective_domain.mpr ?_
  exact
    lt_of_le_of_lt
      (conjugateFunction_le_pairingSub_of_memSubdifferential f hproper hg) hfinite

section

variable [FiniteDimensional ℝ E]

/-- Helper for Theorem 4.2: a proper convex function admits a dual vector where its conjugate is
finite. -/
private lemma exists_dual_mem_effectiveDomain_conjugate_of_proper_convex
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f) (hconvex : is_convex_function f) :
    ∃ y : Module.Dual ℝ E, y ∈ effective_domain (conjugate_function f) := by
  -- Choose a point with nonempty subdifferential and convert that subgradient into a finite
  -- conjugate value.
  rcases exists_subdifferentiable_point_in_effective_domain_of_proper_convex f hproper hconvex with
    ⟨x, _hx, hxsub⟩
  rcases hxsub with ⟨g, hg⟩
  exact ⟨g, mem_effectiveDomain_conjugateFunction_of_memSubdifferential f hproper hg⟩

end

-- Helper for Theorem 4.2: a pointwise bound on the Fenchel integrand over `effective_domain f`
-- bounds `conjugate_function f y` by the same real constant.
private lemma conjugateFunction_le_of_integrand_le_on_effectiveDomain
    (f : E → EReal) (y : Module.Dual ℝ E) {K : ℝ}
    (hK : ∀ z ∈ effective_domain f, (y z : EReal) - f z ≤ (K : EReal)) :
    conjugate_function f y ≤ (K : EReal) := by
  -- Control the supremum defining `conjugate_function` term-by-term.
  rw [conjugate_function_apply]
  refine sSup_le ?_
  rintro _ ⟨z, rfl⟩
  by_cases hz : z ∈ effective_domain f
  · exact hK z hz
  · have hztop : f z = ⊤ := by
      simpa [mem_effective_domain] using hz
    simp [hztop]

/-- Helper for Theorem 4.2: a dual witness with finite conjugate upper bound produces a strict
lower bound for `biconjugate_function f x`. -/
private lemma ereal_lt_biconjugate_of_dualWitness
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {x : E} {t K : ℝ} {y : Module.Dual ℝ E}
    (hconj_le : conjugate_function f y ≤ (K : EReal))
    (hstrict : t + K < y x) :
    (t : EReal) < biconjugate_function f x := by
  have hconj_ne_bot : conjugate_function f y ≠ ⊥ :=
    conjugateFunction_neBot_of_proper f hproper y
  have hconj_lt_top : conjugate_function f y < ⊤ :=
    lt_of_le_of_lt hconj_le (EReal.coe_lt_top K)
  lift conjugate_function f y to ℝ using
      ⟨lt_top_iff_ne_top.mp hconj_lt_top, hconj_ne_bot⟩ with ky hky
  -- Replace the conjugate value by a real scalar so the final inequality is a real calculation.
  have hky_le : ky ≤ K := by
    simpa [← hky] using hconj_le
  have htky : t + ky < y x := by
    have htk_le : t + ky ≤ t + K := by
      linarith
    exact lt_of_le_of_lt htk_le hstrict
  have hterm : (t : EReal) < (y x : EReal) - conjugate_function f y := by
    rw [← hky]
    exact_mod_cast (show t < y x - ky by linarith)
  -- Insert this one dual vector into the biconjugate supremum.
  rw [biconjugate_function_apply]
  exact lt_of_lt_of_le hterm (le_sSup (Set.mem_range_self y))

/-- Helper for Theorem 4.2: a strict horizontal separator on `effective_domain f`, together with
one finite conjugate point, yields a dual witness above any prescribed real level `t`. -/
private lemma exists_dualWitness_of_horizontalSeparator
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    {a yHat : Module.Dual ℝ E} {x : E} {u t : ℝ}
    (ha : ∀ z ∈ effective_domain f, a z < u) (hax : u < a x)
    (hyHat_eff : yHat ∈ effective_domain (conjugate_function f)) :
    ∃ y : Module.Dual ℝ E, ∃ K : ℝ,
      conjugate_function f y ≤ (K : EReal) ∧ t + K < y x := by
  have hyHat_ne_bot : conjugate_function f yHat ≠ ⊥ :=
    conjugateFunction_neBot_of_proper f hproper yHat
  have hyHat_lt_top : conjugate_function f yHat < ⊤ :=
    mem_effective_domain.mp hyHat_eff
  lift conjugate_function f yHat to ℝ using
      ⟨lt_top_iff_ne_top.mp hyHat_lt_top, hyHat_ne_bot⟩ with kHat hkHat
  -- Choose a scaling factor large enough to absorb the target level `t`.
  have hgap : 0 < a x - u := by
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((t + kHat - yHat x) / (a x - u))
  let lam : ℝ := n
  let y : Module.Dual ℝ E := lam • a + yHat
  let K : ℝ := lam * u + kHat
  have hlam_nonneg : 0 ≤ lam := by
    exact Nat.cast_nonneg n
  have htarget_gap : t + K < y x := by
    -- The positive gap `a x - u` lets the scaled separator dominate the target level.
    have hn_real : (t + kHat - yHat x) / (a x - u) < lam := by
      exact_mod_cast hn
    have hmul_gap : t + kHat - yHat x < lam * (a x - u) := by
      exact (div_lt_iff₀ hgap).1 hn_real
    have hyx : y x = lam * a x + yHat x := by
      simp [y, lam]
    have hK : K = lam * u + kHat := rfl
    rw [hyx, hK]
    linarith
  have hconj_le : conjugate_function f y ≤ (K : EReal) := by
    -- Bound the scaled Fenchel integrand on `effective_domain f` and then take the supremum.
    refine conjugateFunction_le_of_integrand_le_on_effectiveDomain f y ?_
    intro z hz
    lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
    have hyHat_term_ereal : ((yHat z : EReal) - f z) ≤ (kHat : EReal) := by
      calc
        ((yHat z : EReal) - f z) ≤ conjugate_function f yHat := by
          rw [conjugate_function_apply]
          exact le_sSup (Set.mem_range_self z)
        _ = (kHat : EReal) := by rw [← hkHat]
    have hyHat_term : yHat z - fz ≤ kHat := by
      rw [← hfz] at hyHat_term_ereal
      exact_mod_cast hyHat_term_ereal
    have hscaled : lam * a z ≤ lam * u := by
      exact mul_le_mul_of_nonneg_left (le_of_lt (ha z hz)) hlam_nonneg
    have hy_apply : y z = lam * a z + yHat z := by
      simp [y, lam]
    have hreal : lam * a z + yHat z - fz ≤ K := by
      rw [show K = lam * u + kHat by rfl]
      linarith
    simpa [hy_apply, hfz, EReal.coe_sub] using (EReal.coe_le_coe hreal)
  exact ⟨y, K, hconj_le, htarget_gap⟩

section

variable [FiniteDimensional ℝ E]

/-- Helper for Theorem 4.2: every real level strictly below `f x` lies strictly below
`biconjugate_function f x`. -/
private lemma ereal_lt_biconjugate_of_lt_value
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f)
    {x : E} {t : ℝ} (ht : (t : EReal) < f x) :
    (t : EReal) < biconjugate_function f x := by
  -- Separate the point `(x, t)` from the closed convex real epigraph of `f`.
  have hxt_not_mem : (x, t) ∉ realEpigraph f := by
    intro hmem
    exact (not_le_of_gt ht) (mem_realEpigraph.mp hmem)
  obtain ⟨L, α, hL_epi, hL_xt⟩ :=
    geometric_hahn_banach_closed_point
      ((is_convex_function_iff_convex_real_epigraph f).1 hconvex)
      hclosed.isClosed_real_epigraph hxt_not_mem
  let a : Module.Dual ℝ E :=
    ((L.comp (ContinuousLinearMap.inl ℝ E ℝ) : StrongDual ℝ E) : Module.Dual ℝ E)
  let b : ℝ := L (0, 1)
  have hsep_epi : ∀ z s, (z, s) ∈ realEpigraph f → a z + b * s < α := by
    intro z s hs
    have hLs : L (z, s) < α := hL_epi (z, s) hs
    rw [prodSeparator_apply_eq_dual_add_smul L z s] at hLs
    simpa [a, b] using hLs
  have hsep_xt : α < a x + b * t := by
    have hxt : α < L (x, t) := hL_xt
    rw [prodSeparator_apply_eq_dual_add_smul L x t] at hxt
    simpa [a, b] using hxt
  have hb_nonpos : b ≤ 0 := by
    rcases hproper.effective_domain_nonempty with ⟨z0, hz0⟩
    lift f z0 to ℝ using ⟨hz0.ne, hproper.ne_bot z0⟩ with fz0 hfz0
    -- A positive vertical slope would fail on a sufficiently high point of the same vertical ray.
    by_contra hb_pos
    have hb_pos' : 0 < b := lt_of_not_ge hb_pos
    let s : ℝ := max fz0 (((α - a z0) / b) + 1)
    have hs_mem : (z0, s) ∈ realEpigraph f := by
      rw [mem_realEpigraph, ← hfz0]
      exact_mod_cast le_max_left fz0 (((α - a z0) / b) + 1)
    have hs_lt : a z0 + b * s < α := hsep_epi z0 s hs_mem
    have hs_ge : α < a z0 + b * s := by
      have hmul :
          b * (((α - a z0) / b) + 1) ≤ b * s :=
        mul_le_mul_of_nonneg_left (le_max_right fz0 (((α - a z0) / b) + 1)) hb_pos'.le
      have hbase : α - a z0 + b ≤ b * s := by
        calc
          α - a z0 + b = b * (((α - a z0) / b) + 1) := by
            field_simp [hb_pos'.ne']
          _ ≤ b * s := hmul
      linarith
    exact (not_lt_of_ge hs_ge.le) hs_lt
  rcases lt_or_eq_of_le hb_nonpos with hb_neg | hb_zero
  · -- A negative vertical slope directly yields a dual witness after normalization.
    let κ : ℝ := (-b)⁻¹
    let y : Module.Dual ℝ E := κ • a
    let K : ℝ := κ * α
    have hκ_pos : 0 < κ := by
      dsimp [κ]
      exact inv_pos.mpr (by linarith)
    have hconj_le : conjugate_function f y ≤ (K : EReal) := by
      refine conjugateFunction_le_of_integrand_le_on_effectiveDomain f y ?_
      intro z hz
      lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
      have hz_lt : a z + b * fz < α := by
        have hz_mem : (z, fz) ∈ realEpigraph f := by
          rw [mem_realEpigraph, ← hfz]
        exact hsep_epi z fz hz_mem
      have hy_apply : y z = κ * a z := by
        simp [y, κ]
      have hreal : κ * a z - fz < K := by
        have hscaled_lt : κ * (a z + b * fz) < κ * α :=
          mul_lt_mul_of_pos_left hz_lt hκ_pos
        have hbκ : κ * b = -1 := by
          dsimp [κ]
          field_simp [hb_neg.ne]
        have hscaled_lt' : κ * a z - fz < κ * α := by
          have htmp : κ * a z < κ * α + fz := by
            simpa [hbκ, mul_add, ← mul_assoc] using hscaled_lt
          linarith
        rw [show K = κ * α by rfl]
        exact hscaled_lt'
      have hreal_le : κ * a z - fz ≤ K := hreal.le
      simpa [hy_apply, hfz, EReal.coe_sub] using (EReal.coe_le_coe hreal_le)
    have hstrict : t + K < y x := by
      have hyx : y x = κ * a x := by
        simp [y, κ]
      rw [hyx, show K = κ * α by rfl]
      have hscaled_xt : κ * α < κ * (a x + b * t) :=
        mul_lt_mul_of_pos_left hsep_xt hκ_pos
      have hbκ : κ * b = -1 := by
        dsimp [κ]
        field_simp [hb_neg.ne]
      have hscaled_xt' : κ * α < κ * a x - t := by
        calc
          κ * α < κ * a x + κ * (b * t) := by
            simpa [mul_add] using hscaled_xt
          _ = κ * a x + (κ * b) * t := by ring
          _ = κ * a x - t := by rw [hbκ]; ring
      linarith
    exact ereal_lt_biconjugate_of_dualWitness f hproper hconj_le hstrict
  · -- Route correction: when the separator is horizontal, only the `f x = ⊤` branch survives.
    cases hfx : f x with
    | bot =>
        exfalso
        simp [hfx] at ht
    | coe r =>
        exfalso
        have hx_mem : (x, r) ∈ realEpigraph f := by
          rw [mem_realEpigraph, hfx]
        have hx_lt : a x < α := by
          simpa [hb_zero] using hsep_epi x r hx_mem
        have : α < a x := by
          simpa [hb_zero] using hsep_xt
        exact (not_lt_of_ge hx_lt.le) this
    | top =>
        rcases exists_dual_mem_effectiveDomain_conjugate_of_proper_convex f hproper hconvex with
          ⟨yHat, hyHat_eff⟩
        have ha_eff : ∀ z ∈ effective_domain f, a z < α := by
          intro z hz
          lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
          have hz_mem : (z, fz) ∈ realEpigraph f := by
            rw [mem_realEpigraph, ← hfz]
          simpa [hb_zero] using hsep_epi z fz hz_mem
        have hax : α < a x := by
          simpa [hb_zero] using hsep_xt
        rcases
            exists_dualWitness_of_horizontalSeparator f hproper ha_eff hax hyHat_eff with
          ⟨y, K, hconj_le, hstrict⟩
        exact ereal_lt_biconjugate_of_dualWitness f hproper hconj_le hstrict

-- Proof sketch: combine the earlier inequality `f** ≤ f` with strict separation of the epigraph
-- of a proper closed convex function from any point below it. The separating functional produces a
-- dual vector contradicting Fenchel's inequality unless `f x ≤ f** x`, so pointwise equality
-- follows.

/-- Theorem 4.2 (Theorem 4.8): a proper lower semicontinuous convex `EReal`-valued function
equals its biconjugate. -/
theorem biconjugate_function_eq_self_of_proper_closed_convex
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f) :
    biconjugate_function f = f := by
  funext x
  refine le_antisymm (biconjugate_function_apply_le f x) ?_
  cases hfx : f x with
  | bot =>
      exact False.elim (hproper.ne_bot x hfx)
  | top =>
      have hbiconj_top : biconjugate_function f x = ⊤ := by
        rw [EReal.eq_top_iff_forall_lt]
        intro t
        exact
          ereal_lt_biconjugate_of_lt_value f hproper hclosed hconvex
            (by simp [hfx])
      simp [hbiconj_top]
  | coe r =>
      have hlower : ((r : ℝ) : EReal) ≤ biconjugate_function f x := by
        cases hbiconj : biconjugate_function f x with
        | bot =>
            exfalso
            have hlt :
                (((r - 1 : ℝ) : EReal)) < biconjugate_function f x :=
              ereal_lt_biconjugate_of_lt_value f hproper hclosed hconvex
                <| by
                  simpa [hfx] using
                    (show (((r - 1 : ℝ) : EReal)) < ((r : ℝ) : EReal) by
                      exact_mod_cast (show r - 1 < r by linarith))
            simp [hbiconj] at hlt
        | top =>
            simp
        | coe s =>
            have hrs : r ≤ s := by
              by_contra hrs
              have hsr : s < r := lt_of_not_ge hrs
              rcases exists_between hsr with ⟨t, hst, htr⟩
              have hlt :
                  ((t : ℝ) : EReal) < biconjugate_function f x :=
                ereal_lt_biconjugate_of_lt_value f hproper hclosed hconvex
                  <| by
                    simpa [hfx] using
                      (show ((t : ℝ) : EReal) < ((r : ℝ) : EReal) by
                        exact_mod_cast htr)
              have : ¬ ((t : ℝ) : EReal) < ((s : ℝ) : EReal) := by
                exact not_lt_of_ge (by exact_mod_cast hst.le)
              exact this <| by simpa [hbiconj] using hlt
            exact_mod_cast hrs
      exact hlower

end

end
