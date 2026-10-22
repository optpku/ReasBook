/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part6

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-!
Helpers for Theorem 31.1.

This part file proves the statements available from the dependency-closed Section 31
development (in particular Lemma 31.0.1), including the concave-side attainment bridges used
by the main theorem.
-/

/-- Helper for Theorem 31.1: if `a ≠ ⊥` and `b ≠ ⊤` then `a - b ≠ ⊥` in `EReal`. This is the
simple case split used to show the dual objective is not `-∞` at a domain point. -/
lemma helperForTheorem_31_1_sub_ne_bot_of_ne_bot_of_ne_top {a b : EReal}
    (ha : a ≠ (⊥ : EReal)) (hb : b ≠ (⊤ : EReal)) :
    a - b ≠ (⊥ : EReal) := by
  -- Reduce to the three-constructor case split for `EReal`.
  cases ha' : a with
  | bot =>
      -- Contradiction with the hypothesis `a ≠ ⊥`.
      exact (ha ha').elim
  | top =>
      -- `⊤ - b` is `⊤` whenever `b ≠ ⊤`, hence never `⊥`.
      intro hSub
      have : (⊤ : EReal) = (⊥ : EReal) := by
        simpa [ha', EReal.top_sub hb] using hSub
      simpa using this
  | coe r =>
      cases hb' : b with
      | top =>
          exact (hb hb').elim
      | bot =>
          -- `r - ⊥ = ⊤`, so it cannot be `⊥`.
          intro hSub
          have : (⊤ : EReal) = (⊥ : EReal) := by
            simpa [ha', hb', EReal.sub_bot (EReal.coe_ne_bot r)] using hSub
          simpa using this
      | coe s =>
          -- Real subtraction stays real.
          intro hSub
          have : ((r - s : ℝ) : EReal) = (⊥ : EReal) := by
            simpa [ha', hb', EReal.coe_sub] using hSub
          simpa using (EReal.coe_ne_bot (r - s)) this

/-- Helper for Theorem 31.1: the universal Fenchel-inequality lower bound, in the sign
conventions of this section, gives `primal ≥ dual` without any qualification hypotheses. -/
lemma helperForTheorem_31_1_primal_ge_dual {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    fenchelPrimalInfimum f g ≥ fenchelDualSupremum (n := n) f g := by
  -- This is exactly Lemma 31.0.1 after unfolding the definitions of `primal` and `dual`.
  simpa [fenchelPrimalInfimum, fenchelDualSupremum, fenchelDualObjective,
    commonBookEffectiveDomainDifference, concaveEffectiveDomain, concaveFenchelConjugate,
    ProperConcaveFunctionOn] using
      (fenchel_duality_lower_bound_from_fenchel_inequality (n := n) (f := f) (g := g) hf hg)

/-- Helper for Theorem 31.1: under condition (a), the primal infimum cannot be `+∞` because a
relative-interior point lies in the common effective domain, hence the guarded primal objective
is finite at that point. -/
lemma helperForTheorem_31_1_primal_ne_top_of_conditionA {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hA : FenchelConditionA (n := n) f g) :
    fenchelPrimalInfimum f g ≠ (⊤ : EReal) := by
  -- Pick the relative-interior witness from condition (a).
  rcases hA with ⟨x0, hx0riF, hx0riG⟩
  have hx0F :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hx0riF
  have hx0G :
      x0 ∈ concaveEffectiveDomain g :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (concaveEffectiveDomain g) hx0riG
  have hx0Common :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g :=
    And.intro hx0F hx0G
  -- On the common effective domain, the guard is inactive.
  have hEval :
      commonBookEffectiveDomainDifference f g x0 = f x0 - g x0 := by
    simp [commonBookEffectiveDomainDifference, hx0Common]
  -- The sampled value is not `⊤` because `f x0 < ⊤` and `g x0 ≠ ⊥`.
  have hf_x0_ne_top : f x0 ≠ (⊤ : EReal) := by
    have hx0F' : x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x0 < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx0F
    exact (lt_top_iff_ne_top).1 hx0F'.2
  have hg_x0_ne_bot : g x0 ≠ (⊥ : EReal) := by
    -- If `g x0 = ⊥`, then `-g x0 = ⊤`, contradicting `x0 ∈ dom(-g)`.
    intro hg_bot
    have hx0G' :
        x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧ (-(g x0)) < (⊤ : EReal) := by
      -- `concaveEffectiveDomain g = effectiveDomain univ (fun x => -(g x))`.
      simpa [concaveEffectiveDomain, effectiveDomain_eq] using hx0G
    have : (-(g x0)) = (⊤ : EReal) := by
      simpa [hg_bot] using (show (-(g x0)) = (-(⊥ : EReal)) from rfl)
    exact (lt_top_iff_ne_top).1 hx0G'.2 (by simpa [this])
  have hSample_ne_top : commonBookEffectiveDomainDifference f g x0 ≠ (⊤ : EReal) := by
    -- Reduce to the `EReal` constructor cases for `f x0` and `g x0`.
    cases hfx0 : f x0 with
    | top =>
        exact (hf_x0_ne_top hfx0).elim
    | bot =>
        have : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
        exact (this hfx0).elim
    | coe r =>
        cases hgx0 : g x0 with
        | bot =>
            exact (hg_x0_ne_bot hgx0).elim
        | top =>
            -- Proper concavity of `g` rules out `g x0 = ⊤`.
            have hnegG_ne_bot : (-(g x0)) ≠ (⊥ : EReal) := hg.2.2 x0 (by simp)
            have hgx0_ne_top : g x0 ≠ (⊤ : EReal) := by
              intro htop
              have hnegEq : (-(g x0)) = (⊥ : EReal) := by
                simpa [htop]
              exact hnegG_ne_bot hnegEq
            exact (hgx0_ne_top hgx0).elim
        | coe s =>
            -- In the real/real case, subtraction stays real.
            have : (f x0 - g x0) ≠ (⊤ : EReal) := by
              -- `simp` rewrites to a real coercion.
              simpa [hfx0, hgx0, EReal.coe_sub] using (EReal.coe_ne_top (r - s))
            simpa [hEval, hfx0, hgx0] using this
  -- The infimum is at most the sampled value, so it cannot be `⊤`.
  intro hPrimalTop
  have hInfLe :
      fenchelPrimalInfimum f g ≤ commonBookEffectiveDomainDifference f g x0 := by
    -- `functionInfimumEReal` is an `iInf`, so `iInf_le` provides the evaluation bound.
    simpa [fenchelPrimalInfimum, functionInfimumEReal] using
      (iInf_le (commonBookEffectiveDomainDifference f g) x0)
  have hTopLeSample : (⊤ : EReal) ≤ commonBookEffectiveDomainDifference f g x0 := by
    simpa [hPrimalTop] using hInfLe
  exact hSample_ne_top ((top_le_iff).1 hTopLeSample)

/-- Helper for Theorem 31.1: under condition (b), the dual supremum cannot be `-∞` because a
relative-interior dual domain point gives a dual objective value that is not `-∞`. -/
lemma helperForTheorem_31_1_dual_ne_bot_of_conditionB {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hB : FenchelConditionB (n := n) f g) :
    fenchelDualSupremum (n := n) f g ≠ (⊥ : EReal) := by
  -- Extract a dual-domain witness from the qualification.
  rcases hB with ⟨_hfClosed, _hgClosed, hNonempty⟩
  rcases hNonempty with ⟨xStar, hxStar_riG, hxStar_riF⟩
  have hxStar_domG :
      xStar ∈ concaveConjugateEffectiveDomain g :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (concaveConjugateEffectiveDomain g) hxStar_riG
  have hxStar_domF :
      xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) hxStar_riF
  -- `xStar ∈ dom g⋆` implies `g⋆ xStar ≠ ⊥` because `-g⋆ xStar < ⊤`.
  have hGstar_ne_bot : concaveFenchelConjugate g xStar ≠ (⊥ : EReal) := by
    intro hbot
    have hxStar_domG' :
        xStar ∈ (Set.univ : Set (Fin n → ℝ)) ∧
          (-(concaveFenchelConjugate g xStar)) < (⊤ : EReal) := by
      simpa [concaveConjugateEffectiveDomain, effectiveDomain_eq] using hxStar_domG
    have hNegTop : (-(concaveFenchelConjugate g xStar)) = (⊤ : EReal) := by
      simpa [hbot] using (show (-(concaveFenchelConjugate g xStar)) = (-(⊥ : EReal)) from rfl)
    exact (lt_top_iff_ne_top).1 hxStar_domG'.2 (by simpa [hNegTop])
  -- `xStar ∈ dom f⋆` implies `f⋆ xStar ≠ ⊤`.
  have hFstar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    have hxStar_domF' :
        xStar ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fenchelConjugate n f xStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxStar_domF
    exact (lt_top_iff_ne_top).1 hxStar_domF'.2
  have hObj_ne_bot : fenchelDualObjective (n := n) f g xStar ≠ (⊥ : EReal) := by
    -- This is the `a - b ≠ ⊥` check in the helper above.
    exact
      helperForTheorem_31_1_sub_ne_bot_of_ne_bot_of_ne_top
        (a := concaveFenchelConjugate g xStar) (b := fenchelConjugate n f xStar)
        hGstar_ne_bot hFstar_ne_top
  -- If the supremum were `⊥`, then every term would be `≤ ⊥`, in particular the witness term.
  intro hSupBot
  have hLeSup :
      fenchelDualObjective (n := n) f g xStar ≤ fenchelDualSupremum (n := n) f g := by
    -- By definition, `dual = ⨆ xStar, dualObj xStar`.
    simpa [fenchelDualSupremum] using
      (le_iSup (fun z : Fin n → ℝ => fenchelDualObjective (n := n) f g z) xStar)
  have hLeBot : fenchelDualObjective (n := n) f g xStar ≤ (⊥ : EReal) := by
    simpa [hSupBot] using hLeSup
  have hEqBot : fenchelDualObjective (n := n) f g xStar = (⊥ : EReal) :=
    (le_bot_iff).1 hLeBot
  exact hObj_ne_bot hEqBot

/-- Helper for Theorem 31.1: the polyhedral-pair qualification `(a)` already supplies a common
effective-domain point of `f` and `g`, so the guarded primal infimum cannot be `+∞`. -/
lemma helperForTheorem_31_1_primal_ne_top_of_polyhedral_pair_conditionA {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hA_pair : FenchelConditionAForPolyhedralPair (n := n) f g) :
    fenchelPrimalInfimum f g ≠ (⊤ : EReal) := by
  -- Extract a common effective-domain witness directly from the polyhedral-pair hypothesis.
  rcases hA_pair with ⟨x0, hx0F, hx0G⟩
  have hx0Common :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g :=
    And.intro hx0F hx0G
  -- On the common domain, the guard is inactive and the sampled primal objective is `f x0 - g x0`.
  have hEval :
      commonBookEffectiveDomainDifference f g x0 = f x0 - g x0 := by
    simp [commonBookEffectiveDomainDifference, hx0Common]
  have hf_x0_ne_top : f x0 ≠ (⊤ : EReal) := by
    have hx0F' : x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x0 < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx0F
    exact (lt_top_iff_ne_top).1 hx0F'.2
  have hf_x0_ne_bot : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
  have hg_x0_ne_bot : g x0 ≠ (⊥ : EReal) := by
    intro hg_bot
    have hx0G' :
        x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧ (-(g x0)) < (⊤ : EReal) := by
      simpa [concaveEffectiveDomain, effectiveDomain_eq] using hx0G
    have : (-(g x0)) = (⊤ : EReal) := by
      simpa [hg_bot] using (show (-(g x0)) = (-(⊥ : EReal)) from rfl)
    exact (lt_top_iff_ne_top).1 hx0G'.2 (by simpa [this])
  have hg_x0_ne_top : g x0 ≠ (⊤ : EReal) := by
    intro hg_top
    have hNeg_ne_bot : (-(g x0)) ≠ (⊥ : EReal) := hg.2.2 x0 (by simp)
    have : (-(g x0)) = (⊥ : EReal) := by
      simpa [hg_top]
    exact hNeg_ne_bot this
  have hSample_ne_top : commonBookEffectiveDomainDifference f g x0 ≠ (⊤ : EReal) := by
    -- Reduce to constructor cases and use the real/real subtraction branch.
    cases hfx0 : f x0 with
    | top =>
        exact (hf_x0_ne_top hfx0).elim
    | bot =>
        exact (hf_x0_ne_bot hfx0).elim
    | coe r =>
        cases hgx0 : g x0 with
        | bot =>
            exact (hg_x0_ne_bot hgx0).elim
        | top =>
            exact (hg_x0_ne_top hgx0).elim
        | coe s =>
            have : (f x0 - g x0) ≠ (⊤ : EReal) := by
              simpa [hfx0, hgx0, EReal.coe_sub] using (EReal.coe_ne_top (r - s))
            simpa [hEval, hfx0, hgx0] using this
  -- The infimum is bounded above by the sampled value; therefore `primal = ⊤` is impossible.
  intro hPrimalTop
  have hInfLe :
      fenchelPrimalInfimum f g ≤ commonBookEffectiveDomainDifference f g x0 := by
    simpa [fenchelPrimalInfimum, functionInfimumEReal] using
      (iInf_le (commonBookEffectiveDomainDifference f g) x0)
  have hTopLeSample : (⊤ : EReal) ≤ commonBookEffectiveDomainDifference f g x0 := by
    simpa [hPrimalTop] using hInfLe
  exact hSample_ne_top ((top_le_iff).1 hTopLeSample)

/-- Helper for Theorem 31.1: the polyhedral-pair qualification `(b)` gives a dual-domain witness
where the dual objective is not `-∞`, forcing the dual supremum to be different from `-∞`. -/
lemma helperForTheorem_31_1_dual_ne_bot_of_polyhedral_pair_conditionB {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hB_pair : FenchelConditionBForPolyhedralPair (n := n) f g) :
    fenchelDualSupremum (n := n) f g ≠ (⊥ : EReal) := by
  -- Extract the dual witness directly from the polyhedral-pair condition.
  rcases hB_pair with ⟨xStar, hxStar_domG, hxStar_domF⟩
  have hGstar_ne_bot : concaveFenchelConjugate g xStar ≠ (⊥ : EReal) := by
    intro hbot
    have hxStar_domG' :
        xStar ∈ (Set.univ : Set (Fin n → ℝ)) ∧
          (-(concaveFenchelConjugate g xStar)) < (⊤ : EReal) := by
      simpa [concaveConjugateEffectiveDomain, effectiveDomain_eq] using hxStar_domG
    have hNegTop : (-(concaveFenchelConjugate g xStar)) = (⊤ : EReal) := by
      simpa [hbot] using
        (show (-(concaveFenchelConjugate g xStar)) = (-(⊥ : EReal)) from rfl)
    exact (lt_top_iff_ne_top).1 hxStar_domG'.2 (by simpa [hNegTop])
  have hFstar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    have hxStar_domF' :
        xStar ∈ (Set.univ : Set (Fin n → ℝ)) ∧
          fenchelConjugate n f xStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxStar_domF
    exact (lt_top_iff_ne_top).1 hxStar_domF'.2
  have hObj_ne_bot : fenchelDualObjective (n := n) f g xStar ≠ (⊥ : EReal) := by
    -- The sampled dual objective is a subtraction `a - b` with `a ≠ ⊥` and `b ≠ ⊤`.
    exact
      helperForTheorem_31_1_sub_ne_bot_of_ne_bot_of_ne_top
        (a := concaveFenchelConjugate g xStar) (b := fenchelConjugate n f xStar)
        hGstar_ne_bot hFstar_ne_top
  -- If the supremum were `⊥`, every sampled value would be `≤ ⊥`, including this witness value.
  intro hSupBot
  have hLeSup :
      fenchelDualObjective (n := n) f g xStar ≤ fenchelDualSupremum (n := n) f g := by
    simpa [fenchelDualSupremum] using
      (le_iSup (fun z : Fin n → ℝ => fenchelDualObjective (n := n) f g z) xStar)
  have hLeBot : fenchelDualObjective (n := n) f g xStar ≤ (⊥ : EReal) := by
    simpa [hSupBot] using hLeSup
  have hEqBot : fenchelDualObjective (n := n) f g xStar = (⊥ : EReal) :=
    (le_bot_iff).1 hLeBot
  exact hObj_ne_bot hEqBot

/-!
The remaining work for Theorem 31.1 is the concave-sign *reverse* bridge:
we need `primal ≤ dual` and attainment, phrased in terms of `concaveFenchelConjugate g`.

Route correction (vs earlier failed attempts): we do **not** use the known-false Lemma 31.0.5.
Instead, we reduce to the convex pair `(f, -g)` and invoke Chapter 20’s exact
`(f + (-g))⋆ = f⋆ □ (-g)⋆` theorem with attainment at `0`.
-/

/-- Helper for Theorem 31.1: under condition (a), strong duality holds and the dual supremum is
attained for the concave-sign objective `xStar ↦ g⋆ xStar - f⋆ xStar`. -/
lemma helperForTheorem_31_1_conditionA_concaveDuality_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hA : FenchelConditionA (n := n) f g) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  -- Introduce the convex function `h := -g`, so `f - g = f + h`.
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg

  -- We apply Theorem 20.1 to the ordered pair `(h, f)`, so the infimal convolution at `0`
  -- matches the book's dual objective `xStar ↦ -h⋆(-xStar) - f⋆ xStar`.
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then h else f
  have hpolyTwo :
      ∀ i : Fin 2, i.1 < 0 → IsPolyhedralConvexFunction n (fTwo i) := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i.1 hi)
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hh
    · simpa [fTwo] using hf

  -- Convert the fin-space qualification hypothesis into the EuclideanSpace-preimage form
  -- required by Theorem 20.1.
  rcases hA with ⟨x0, hx0riF, hx0riG⟩
  have hx0riH :
      x0 ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
    simpa [concaveEffectiveDomain, h] using hx0riG
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let y0 : EuclideanSpace ℝ (Fin n) := e.symm x0
  have hPreimage_eq_image (C : Set (Fin n → ℝ)) :
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C) = e.symm '' C := by
    ext y
    constructor
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp [e]
    · rintro ⟨x, hxC, rfl⟩
      simpa [e] using hxC
  have hdomRiTwo :
      Set.Nonempty
        ((⋂ i : {i : Fin 2 // i.1 < 0},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
          ∩
          (⋂ i : {i : Fin 2 // 0 ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
    refine ⟨y0, ?_⟩
    refine And.intro ?_ ?_
    · -- The `i.1 < 0` block is empty; membership is trivial by contradiction.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      exact False.elim (Nat.not_lt_zero i.1 hi)
    · -- For `k = 0`, both indices lie in the relative-interior block.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · -- Index `0`: relative interior of `dom h`.
        have hy0ri :
            y0 ∈ euclideanRelativeInterior n
              (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
          have := (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)
            (x := x0)).1 hx0riH
          simpa [y0, e] using this
        simpa [hPreimage_eq_image] using hy0ri
      · -- Index `1`: relative interior of `dom f`.
        have hy0ri :
            y0 ∈ euclideanRelativeInterior n
              (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
          have := (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
            (x := x0)).1 hx0riF
          simpa [y0, e] using this
        simpa [hPreimage_eq_image] using hy0ri

  -- Invoke Theorem 20.1 and specialize to `xStar = 0`.
  obtain ⟨hConjEq, hAttained⟩ :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
      (f := fTwo) (k := 0) (hk := by decide) (hmPos := by decide)
      hpolyTwo hproperTwo hdomRiTwo
  have hConjEq0 :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
    simpa using congrArg (fun F => F 0) hConjEq
  have hInfConvFamilyEq :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) := by
    have hConjTwo :
        (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
          (fun i : Fin 2 =>
            if i = 0 then fenchelConjugate n h else fenchelConjugate n f) := by
      funext i
      fin_cases i
      · simp [fTwo]
      · simp [fTwo]
    simpa [hConjTwo] using
      (infimalConvolution_eq_infimalConvolutionFamily_two
        (f := fenchelConjugate n h) (g := fenchelConjugate n f)).symm
  have hConjEq0' :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    simpa [hInfConvFamilyEq] using hConjEq0

  -- Step 1: rewrite the primal infimum as `- (fTwo-sum)⋆(0)`.
  have hCommonEq :
      commonBookEffectiveDomainDifference f g = fun x => f x + h x := by
    funext x
    by_cases hx :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g
    · -- On the common effective domain, the guard is inactive and `f - g = f + (-g)`.
      simp [commonBookEffectiveDomainDifference, hx, h, sub_eq_add_neg, add_assoc]
    · -- Outside the common domain, at least one term is `⊤`, so the sum is `⊤` as well.
      have hxOr :
          x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨
            x ∉ concaveEffectiveDomain g := by
        have : ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
            x ∈ concaveEffectiveDomain g) := by
          simpa [Set.mem_inter_iff] using hx
        exact not_and_or.mp this
      cases hxOr with
      | inl hxNotDomF =>
          have hfTop : f x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := f) hxNotDomF
          have hhNeBot : h x ≠ (⊥ : EReal) := hh.2.2 x (by simp)
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hfTop] using (EReal.top_add_of_ne_bot hhNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
      | inr hxNotDomG =>
          have hxNotDomH :
              x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
            simpa [concaveEffectiveDomain, h] using hxNotDomG
          have hhTop : h x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := h) hxNotDomH
          have hfNeBot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hhTop] using (EReal.add_top_of_ne_bot hfNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
  have hPrimal_as_negConj0 :
      fenchelPrimalInfimum f g =
        -fenchelConjugate n (fun x => f x + h x) 0 := by
    -- Replace the guarded primal objective by the pointwise sum `f + (-g)`.
    have :
        fenchelPrimalInfimum f g =
          functionInfimumEReal (fun x => f x + h x) := by
      simp [fenchelPrimalInfimum, hCommonEq]
    -- Convert `inf` into `- conj(0)` using `fenchelConjugate_zero_eq_neg_iInf`.
    have h0 :=
      fenchelConjugate_zero_eq_neg_iInf (n := n) (f := fun x => f x + h x)
    have h0' : -fenchelConjugate n (fun x => f x + h x) 0 =
        functionInfimumEReal (fun x => f x + h x) := by
      -- Negate the identity `conj(0) = -inf`.
      have := congrArg (fun a : EReal => -a) h0
      simpa [functionInfimumEReal] using this
    simpa [this] using h0'.symm

  -- Step 2: identify the dual value as the negative of the infimal convolution at `0`.
  have hInfConv0_eq_iInf :
      infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
        ⨅ xStar : Fin n → ℝ, fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
    -- Unfold the `sInf`-based definition and observe it is the `iInf` over the range
    -- `xStar ↦ h⋆(-xStar) + f⋆(xStar)`.
    unfold infimalConvolution
    -- Rewrite the defining set by eliminating `x1` from `x1 + x2 = 0`.
    have hset :
        {z : EReal |
            ∃ x1 x2 : Fin n → ℝ, x1 + x2 = (0 : Fin n → ℝ) ∧
              z = fenchelConjugate n h x1 + fenchelConjugate n f x2} =
          Set.range (fun xStar : Fin n → ℝ =>
            fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      ext z
      constructor
      · rintro ⟨x1, x2, hsum, rfl⟩
        have hx1 : x1 = -x2 := by
          -- Solve `x1 + x2 = 0`.
          exact eq_neg_of_add_eq_zero_left hsum
        refine ⟨x2, ?_⟩
        simp [hx1, add_comm, add_left_comm, add_assoc]
      · rintro ⟨xStar, rfl⟩
        refine ⟨-xStar, xStar, ?_, rfl⟩
        simp
    -- Rewrite the defining set to a `Set.range`, then unfold `⨅` (definitionally) and close by `rfl`.
    simp [hset]
    rfl

  have hDual_as_negInfConv0 :
      fenchelDualSupremum (n := n) f g =
        -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    -- Rewrite the dual objective in terms of `h = -g`.
    have hDualObj :
        (fun xStar : Fin n → ℝ => fenchelDualObjective (n := n) f g xStar) =
          (fun xStar : Fin n → ℝ =>
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar)) := by
      funext xStar
      -- `concaveFenchelConjugate g xStar = -h⋆(-xStar)`. Use `EReal.neg_add` to rewrite
      -- `(-A) - B` as `-(A + B)` under the `≠ ⊥` hypotheses supplied by properness of conjugates.
      have hHstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
        proper_fenchelConjugate_of_proper (n := n) (f := h) hh
      have hFstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hA_ne_bot : fenchelConjugate n h (-xStar) ≠ (⊥ : EReal) :=
        hHstarProper.2.2 (-xStar) (by simp)
      have hB_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        hFstarProper.2.2 xStar (by simp)
      have hneg :
          (-fenchelConjugate n h (-xStar)) - fenchelConjugate n f xStar =
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
        -- `-(A + B) = -A - B`, so `(-A) - B = -(A + B)`.
        simpa using
          (EReal.neg_add (x := fenchelConjugate n h (-xStar))
            (y := fenchelConjugate n f xStar)
            (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
      simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
    -- Convert `sup (-a)` into `- inf a`.
    have hSupNeg :
        (⨆ xStar : Fin n → ℝ,
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar)) =
          - (⨅ xStar : Fin n → ℝ,
              fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      simpa using (ereal_iSup_neg_eq_neg_iInf
        (g := fun xStar : Fin n → ℝ =>
          fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar))
    -- Replace the `iInf` by the infimal convolution at `0`.
    have hInfRewrite :
        (⨅ xStar : Fin n → ℝ, fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [hInfConv0_eq_iInf] using rfl
    -- Put everything together.
    simp [fenchelDualSupremum, hDualObj, hSupNeg, hInfRewrite]

  -- Step 3: combine the conjugate-of-sum bridge at `0` with the primal/dual rewrites.
  have hSumRewrite :
      (fun x => ∑ i : Fin 2, fTwo i x) = fun x => h x + f x := by
    funext x
    simp [fTwo, Fin.sum_univ_two]
  have hConjSum0 :
      fenchelConjugate n (fun x => f x + h x) 0 =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    -- Transport `hConjEq0'` through the `∑`-rewrite, then commute `h + f` to `f + h`.
    have hConjSum0_hf :
        fenchelConjugate n (fun x => h x + f x) 0 =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [hSumRewrite] using hConjEq0'
    have hSwap : (fun x => f x + h x) = fun x => h x + f x := by
      funext x
      simp [add_comm]
    simpa [hSwap] using hConjSum0_hf

  have hEq : fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g := by
    -- Both sides are `- (f + (-g))⋆(0)` by the bridge and `fenchelConjugate_zero_eq_neg_iInf`.
    calc
      fenchelPrimalInfimum f g
          = -fenchelConjugate n (fun x => f x + h x) 0 := hPrimal_as_negConj0
      _ = -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
            simpa [hConjSum0]
      _ = fenchelDualSupremum (n := n) f g := by
            simpa [hDual_as_negInfConv0]

  -- Step 4: dual attainment comes from the attained decomposition of the infimal convolution at `0`.
  have hAtt0 := hAttained (0 : Fin n → ℝ)
  rcases hAtt0 with ⟨xStarFam, hsum0, hval⟩
  -- Extract `xStar := xStarFam 1`, so `xStarFam 0 = -xStar` by the sum constraint.
  have hsum0' : xStarFam 0 + xStarFam 1 = (0 : Fin n → ℝ) := by
    simpa [Fin.sum_univ_two] using hsum0
  have hx0 : xStarFam 0 = -xStarFam 1 := by
    exact eq_neg_of_add_eq_zero_left hsum0'
  let xStar : Fin n → ℝ := xStarFam 1
  have hInfConv0_value :
      infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
    -- Rewrite the attained value through `Fin.sum_univ_two` and the sum constraint.
    have hval' :
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 =
          fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) := by
      -- Expand the `Fin 2` sum in the attainment witness.
      simpa [fTwo, Fin.sum_univ_two] using hval
    -- Transport from the family infimal convolution to the binary one.
    have hInf0 :
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
      simpa [hInfConvFamilyEq] using rfl
    -- Replace `xStarFam 0` with `-xStar`.
    have : fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
      -- `xStarFam 1 = xStar` by definition.
      simp [xStar, hx0]
    -- Combine the rewrites.
    exact hInf0.trans (hval'.trans this)

  have hDualAttained :
      fenchelDualSupremum (n := n) f g =
        fenchelDualObjective (n := n) f g xStar := by
    -- The supremum equals `-infConv(0)` and the objective at `xStar` is `- (attained infConv)`.
    have hObj :
        fenchelDualObjective (n := n) f g xStar =
          -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      -- Same `EReal.neg_add` rewrite as in `hDualObj`.
      have hHstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
        proper_fenchelConjugate_of_proper (n := n) (f := h) hh
      have hFstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hA_ne_bot : fenchelConjugate n h (-xStar) ≠ (⊥ : EReal) :=
        hHstarProper.2.2 (-xStar) (by simp)
      have hB_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        hFstarProper.2.2 xStar (by simp)
      have hneg :
          (-fenchelConjugate n h (-xStar)) - fenchelConjugate n f xStar =
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
        simpa using
          (EReal.neg_add (x := fenchelConjugate n h (-xStar))
            (y := fenchelConjugate n f xStar)
            (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
      simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
    calc
      fenchelDualSupremum (n := n) f g
          = -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := hDual_as_negInfConv0
      _ = -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
            simpa [hInfConv0_value]
      _ = fenchelDualObjective (n := n) f g xStar := by
            simpa [hObj]

  refine And.intro hEq ?_
  refine ⟨xStar, ?_⟩
  simpa [hEq] using hDualAttained

/-- Helper for Theorem 31.1: closed concave functions satisfy concave biconjugacy, i.e.
`(g⋆)⋆ = g`, provided the properness hypotheses needed to apply the convex biconjugacy theorem
to `-g`. -/
lemma helperForTheorem_31_1_concave_biconjugate_eq_of_closedConcave {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hg_closed : ClosedConcaveFunction g)
    (hg_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ∀ x : Fin n → ℝ, concaveFenchelConjugate (n := n) (concaveFenchelConjugate (n := n) g) x = g x := by
  classical
  -- Apply convex biconjugacy to `h := -g`.
  let h : (Fin n → ℝ) → EReal := fun z => -(g z)
  have hh_closed : ClosedConvexFunction h := by
    simpa [ClosedConcaveFunction, h] using hg_closed
  have hh_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg_proper
  have hh_biconj :
      fenchelConjugate n (fenchelConjugate n h) = h := by
    -- The closed-convex hypotheses supply convexity + lsc; properness supplies `h ≠ ⊥`.
    have hneBot : ∀ x : Fin n → ℝ, h x ≠ (⊥ : EReal) := by
      intro x
      exact hh_proper.2.2 x (by simp)
    exact
      fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := h)
        (hf_closed := hh_closed.2) (hf_convex := hh_closed.1) (hf_ne_bot := hneBot)
  -- Unfold the concave conjugate twice and rewrite by the convex biconjugate identity.
  intro x
  -- `-(concaveFenchelConjugate g)` is `h⋆` precomposed with negation.
  have hnegEq :
      (fun y : Fin n → ℝ => -(concaveFenchelConjugate (n := n) g y)) =
        fun y : Fin n → ℝ => fenchelConjugate n h (-y) := by
    funext y
    simp [concaveFenchelConjugate, h]
  -- Use Fenchel conjugacy under the negation isometry to remove the precomposition.
  have hprecomp :
      fenchelConjugate n (fun y : Fin n → ℝ => fenchelConjugate n h (-y)) =
        fun y : Fin n → ℝ => fenchelConjugate n (fenchelConjugate n h) (-y) := by
    -- `y ↦ -y` is an orthogonal map for the dot product.
    let negIso : (Fin n → ℝ) ≃ₗᵢ[ℝ] (Fin n → ℝ) := LinearIsometryEquiv.neg ℝ
    have hAStar :
        ∀ u v : Fin n → ℝ, (negIso u) ⬝ᵥ v = u ⬝ᵥ (negIso.symm v) := by
      intro u v
      -- `(-u)·v = u·(-v)`.
      simp [negIso, neg_dotProduct, dotProduct_neg]
    -- Apply the general orthogonal-precomposition lemma.
    simpa [negIso] using
      (fenchelConjugate_precomp_orthogonal (n := n) (f := fenchelConjugate n h) (g := negIso)
        (hAStar := hAStar))
  -- Finish by unfolding, rewriting, and applying `hh_biconj`.
  calc
    concaveFenchelConjugate (n := n) (concaveFenchelConjugate (n := n) g) x
        = -(fenchelConjugate n (fun y : Fin n → ℝ => -(concaveFenchelConjugate (n := n) g y)) (-x)) := by
            simp [concaveFenchelConjugate]
    _ = -(fenchelConjugate n (fun y : Fin n → ℝ => fenchelConjugate n h (-y)) (-x)) := by
            simp [hnegEq]
    _ = -(fenchelConjugate n (fenchelConjugate n h) x) := by
            -- Use the precomposition rewrite and `-(-x)=x`.
            simp [hprecomp]
    _ = -h x := by
            -- Apply the convex biconjugacy identity.
            simpa [hh_biconj]
    _ = g x := by
            simp [h]

/-- Helper for Theorem 31.1: proper concavity is preserved by the concave Fenchel conjugate in the
book sign convention. -/
lemma helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) (concaveFenchelConjugate g) := by
  -- Write the concave conjugate through the convex conjugate of `-g`.
  let hNeg : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hNegProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) hNeg := by
    simpa [ProperConcaveFunctionOn, hNeg] using hg
  have hConjProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hNeg) :=
    proper_fenchelConjugate_of_proper (n := n) (f := hNeg) hNegProper
  let negMap : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := -LinearMap.id
  have hRangeDom :
      ∃ z : Fin n → ℝ,
        z ∈ Set.range negMap ∧
          z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hNeg) := by
    have hDomNonempty :
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hNeg)) := by
      exact
        (nonempty_epigraph_iff_nonempty_effectiveDomain
          (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hNeg)).1 hConjProper.2.1
    rcases hDomNonempty with ⟨z, hzDom⟩
    refine ⟨z, ?_, hzDom⟩
    refine ⟨-z, ?_⟩
    ext i
    simp [negMap]
  have hPrecompProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun y => fenchelConjugate n hNeg (negMap y)) :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain
      (A := negMap) (h := fenchelConjugate n hNeg) hConjProper hRangeDom
  -- Identify this precomposition with the negated concave conjugate.
  have hPrecompEq :
      (fun y : Fin n → ℝ => fenchelConjugate n hNeg (negMap y)) =
        (fun y : Fin n → ℝ => -(concaveFenchelConjugate g y)) := by
    funext y
    simp [hNeg, negMap, concaveFenchelConjugate]
  simpa [ProperConcaveFunctionOn, hPrecompEq] using hPrecompProper

/-- Helper for Theorem 31.1: under properness hypotheses, the guarded primal objective equals the
pointwise difference `f - g` everywhere. -/
lemma helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
    {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    commonBookEffectiveDomainDifference f g = fun x => f x - g x := by
  funext x
  -- Split by whether the guard is active.
  by_cases hx :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g
  · simp [commonBookEffectiveDomainDifference, hx]
  · have hxOr :
        x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨
          x ∉ concaveEffectiveDomain g := by
      have : ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧ x ∈ concaveEffectiveDomain g) := by
        simpa [Set.mem_inter_iff] using hx
      exact not_and_or.mp this
    cases hxOr with
    | inl hxNotDomF =>
        -- Outside `dom f`, one has `f x = ⊤`; proper concavity gives `g x ≠ ⊤`, so `f x - g x = ⊤`.
        have hFxTop : f x = (⊤ : EReal) :=
          not_mem_effectiveDomain_univ_imp_eq_top (f := f) hxNotDomF
        have hGx_ne_top : g x ≠ (⊤ : EReal) := by
          intro hGxTop
          have hNegG_ne_bot : (-(g x)) ≠ (⊥ : EReal) := hg.2.2 x (by simp)
          have hNegG_bot : (-(g x)) = (⊥ : EReal) := by
            simpa [hGxTop]
          exact hNegG_ne_bot hNegG_bot
        have hSubTop : f x - g x = (⊤ : EReal) := by
          simpa [hFxTop] using (EReal.top_sub hGx_ne_top)
        simp [commonBookEffectiveDomainDifference, hx, hSubTop]
    | inr hxNotDomG =>
        -- Outside `dom g` (in the concave sense), `g x = ⊥`; then `f x - g x = ⊤`.
        have hxNotDomNeg :
            x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y => -(g y)) := by
          simpa [concaveEffectiveDomain] using hxNotDomG
        have hNegG_top : (-(g x)) = (⊤ : EReal) :=
          not_mem_effectiveDomain_univ_imp_eq_top (f := fun y => -(g y)) hxNotDomNeg
        have hGx_bot : g x = (⊥ : EReal) := by
          cases hGx : g x with
          | bot =>
              simpa [hGx]
          | top =>
              have hNegG_ne_bot : (-(g x)) ≠ (⊥ : EReal) := hg.2.2 x (by simp)
              have hNegG_bot : (-(g x)) = (⊥ : EReal) := by
                simpa [hGx]
              exact (hNegG_ne_bot hNegG_bot).elim
          | coe r =>
              have hNegG_ne_top : (-(g x)) ≠ (⊤ : EReal) := by
                simpa [hGx] using (EReal.coe_ne_top (-r))
              exact (hNegG_ne_top hNegG_top).elim
        have hFx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
        have hSubTop : f x - g x = (⊤ : EReal) := by
          simpa [hGx_bot] using (EReal.sub_bot hFx_ne_bot)
        simp [commonBookEffectiveDomainDifference, hx, hSubTop]

/-- Helper for Theorem 31.1: the original dual value equals minus the primal value of the
conjugate pair `(f⋆, g⋆)` in the book sign convention. -/
lemma helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    fenchelDualSupremum (n := n) f g =
      -fenchelPrimalInfimum (fenchelConjugate n f) (concaveFenchelConjugate g) := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
  have hfStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hgStar :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
        (n := n) (g := g) hg
  have hCommonStar :
      commonBookEffectiveDomainDifference fStar gStar = fun x => fStar x - gStar x :=
    helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
      (n := n) fStar gStar hfStar hgStar
  have hObjRewrite :
      (fun xStar : Fin n → ℝ => fenchelDualObjective (n := n) f g xStar) =
        (fun xStar : Fin n → ℝ => -(fStar xStar - gStar xStar)) := by
    funext xStar
    have hGStar_ne_top : gStar xStar ≠ (⊤ : EReal) := by
      intro hTop
      have hNeg_ne_bot : (-(gStar xStar)) ≠ (⊥ : EReal) := hgStar.2.2 xStar (by simp)
      have hNeg_bot : (-(gStar xStar)) = (⊥ : EReal) := by
        simpa [hTop]
      exact hNeg_ne_bot hNeg_bot
    have hNegSub :
        -(fStar xStar - gStar xStar) = gStar xStar - fStar xStar := by
      calc
        -(fStar xStar - gStar xStar) = -(fStar xStar) + gStar xStar := by
          exact
            EReal.neg_sub (x := fStar xStar) (y := gStar xStar)
              (h1 := Or.inl (hfStar.2.2 xStar (by simp))) (h2 := Or.inr hGStar_ne_top)
        _ = gStar xStar - fStar xStar := by
          simp [sub_eq_add_neg, add_comm]
    simpa [fenchelDualObjective, fStar, gStar] using hNegSub.symm
  -- Convert `sup (-a)` into `- inf a`, then rewrite the primal objective by the guard-elimination helper.
  calc
    fenchelDualSupremum (n := n) f g
        = (⨆ xStar : Fin n → ℝ, -(fStar xStar - gStar xStar)) := by
            simp [fenchelDualSupremum, hObjRewrite]
    _ = -(⨅ xStar : Fin n → ℝ, fStar xStar - gStar xStar) := by
          simpa using
            (ereal_iSup_neg_eq_neg_iInf
              (g := fun xStar : Fin n → ℝ => fStar xStar - gStar xStar))
    _ = -fenchelPrimalInfimum fStar gStar := by
          simp [fenchelPrimalInfimum, functionInfimumEReal, hCommonStar]

/-- Helper for Theorem 31.1: once strong duality and dual attainment are known for the conjugate
pair `(f⋆, g⋆)`, closedness allows translating them back to primal equality and primal attainment
for `(f, g)`. -/
lemma helperForTheorem_31_1_translate_conjugatePair_duality_to_original {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hfClosed : ClosedConvexFunction f)
    (hgClosed : ClosedConcaveFunction g)
    (hEqStar :
      fenchelPrimalInfimum (fenchelConjugate n f) (concaveFenchelConjugate g) =
        fenchelDualSupremum (n := n) (fenchelConjugate n f) (concaveFenchelConjugate g))
    (hAttStar :
      ∃ x : Fin n → ℝ,
        fenchelDualSupremum (n := n) (fenchelConjugate n f) (concaveFenchelConjugate g) =
          fenchelDualObjective (n := n) (fenchelConjugate n f) (concaveFenchelConjugate g) x) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ x : Fin n → ℝ,
        fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
  have hfStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hgStar :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
        (n := n) (g := g) hg
  -- Route correction: instead of invoking the invalid closed-case bridge from Lemma 31.0.5,
  -- translate through the conjugate pair using the stable sign identity and biconjugacy.
  have hDualOrig :
      fenchelDualSupremum (n := n) f g = -fenchelPrimalInfimum fStar gStar := by
    simpa [fStar, gStar] using
      helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair (n := n) f g hf hg
  have hDualStar :
      fenchelDualSupremum (n := n) fStar gStar =
        -fenchelPrimalInfimum (fenchelConjugate n fStar) (concaveFenchelConjugate gStar) := by
    exact
      helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair
        (n := n) fStar gStar hfStar hgStar
  have hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  have hfBiconj :
      fenchelConjugate n (fenchelConjugate n f) = f :=
    fenchelConjugate_biconjugate_eq_of_closedConvex
      (n := n) (f := f)
      (hf_closed := hfClosed.2) (hf_convex := hfClosed.1) (hf_ne_bot := hf_ne_bot)
  have hgBiconj :
      ∀ x : Fin n → ℝ,
        concaveFenchelConjugate (n := n) (concaveFenchelConjugate (n := n) g) x = g x := by
    exact
      helperForTheorem_31_1_concave_biconjugate_eq_of_closedConcave
        (n := n) (g := g) hgClosed hg
  have hgBiconj_fun :
      concaveFenchelConjugate (n := n) (concaveFenchelConjugate (n := n) g) = g := by
    funext x
    exact hgBiconj x
  have hPrimalBiconjEq :
      fenchelPrimalInfimum (fenchelConjugate n fStar) (concaveFenchelConjugate gStar) =
        fenchelPrimalInfimum f g := by
    simp [fStar, gStar, hfBiconj, hgBiconj_fun]
  have hNegDualStarEqPrimal :
      -fenchelDualSupremum (n := n) fStar gStar = fenchelPrimalInfimum f g := by
    have hNeg := congrArg (fun t : EReal => -t) hDualStar
    calc
      -fenchelDualSupremum (n := n) fStar gStar
          = fenchelPrimalInfimum (fenchelConjugate n fStar) (concaveFenchelConjugate gStar) := by
              simpa using hNeg
      _ = fenchelPrimalInfimum f g := hPrimalBiconjEq
  have hEq :
      fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g := by
    have hDualOrigEqNegDualStar :
        fenchelDualSupremum (n := n) f g =
          -fenchelDualSupremum (n := n) fStar gStar := by
      calc
        fenchelDualSupremum (n := n) f g
            = -fenchelPrimalInfimum fStar gStar := hDualOrig
        _ = -fenchelDualSupremum (n := n) fStar gStar := by
              simpa [hEqStar]
    calc
      fenchelPrimalInfimum f g = -fenchelDualSupremum (n := n) fStar gStar := by
        simpa [hNegDualStarEqPrimal] using hNegDualStarEqPrimal.symm
      _ = fenchelDualSupremum (n := n) f g := by
        simpa [hDualOrigEqNegDualStar] using hDualOrigEqNegDualStar.symm
  rcases hAttStar with ⟨x, hx⟩
  have hCommonEq :
      commonBookEffectiveDomainDifference f g = fun y => f y - g y :=
    helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
      (n := n) f g hf hg
  have hNegObjEq :
      -fenchelDualObjective (n := n) fStar gStar x =
        commonBookEffectiveDomainDifference f g x := by
    have hObjAs :
        fenchelDualObjective (n := n) fStar gStar x = g x - f x := by
      simp [fenchelDualObjective, fStar, gStar, hfBiconj, hgBiconj]
    have hGx_ne_top : g x ≠ (⊤ : EReal) := by
      intro hTop
      have hNeg_ne_bot : (-(g x)) ≠ (⊥ : EReal) := hg.2.2 x (by simp)
      have hNeg_bot : (-(g x)) = (⊥ : EReal) := by
        simpa [hTop]
      exact hNeg_ne_bot hNeg_bot
    have hNegSub :
        -(g x - f x) = f x - g x := by
      calc
        -(g x - f x) = -(g x) + f x := by
          exact
            EReal.neg_sub (x := g x) (y := f x)
              (h1 := Or.inr (hf.2.2 x (by simp))) (h2 := Or.inl hGx_ne_top)
        _ = f x - g x := by
          simp [sub_eq_add_neg, add_comm]
    calc
      -fenchelDualObjective (n := n) fStar gStar x = -(g x - f x) := by
        simpa [hObjAs]
      _ = f x - g x := hNegSub
      _ = commonBookEffectiveDomainDifference f g x := by
        simpa [hCommonEq] using (congrArg (fun h : (Fin n → ℝ) → EReal => h x) hCommonEq).symm
  have hPrimalAtt :
      fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x := by
    calc
      fenchelPrimalInfimum f g = -fenchelDualSupremum (n := n) fStar gStar := by
        simpa [hNegDualStarEqPrimal] using hNegDualStarEqPrimal.symm
      _ = -fenchelDualObjective (n := n) fStar gStar x := by
            simpa [hx]
      _ = commonBookEffectiveDomainDifference f g x := hNegObjEq
  exact ⟨hEq, ⟨x, hPrimalAtt⟩⟩
end Section31
end Chap06
