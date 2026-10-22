/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part2

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.5: after the route correction, the raw mixed `(⊥, ⊤)` branch closes
as soon as the raw closure itself is already known to satisfy Jensen's inequality. -/
lemma helperForLemma33_0_5_functionConvexClosure_closedConvex_mixedBotTop_bridge
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ} {a b : ℝ}
    (hClosureConv :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
        (fun z =>
          ⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hPosB : 0 < b)
    (hClosureXBot :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥)
    (hClosureYTop :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊤) :
    (⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) = ⊥ := by
  -- Route correction: the standalone closed-convex hypotheses are not enough for the mixed
  -- branch. Once Jensen for the raw closure is already available, the earlier raw-classification
  -- collapse lemma applies directly.
  exact
    helperForLemma33_0_5_functionConvexClosure_mixedBotTop_collapse_from_rawClassification
      (f := f) (x := x) (y := y) hClosureConv ha hb hab hPosA hPosB
      hClosureXBot hClosureYTop

/-- Helper for Lemma33.0.5: the remaining raw `cl_v` blocker is the target-specific mixed
`(⊥, ⊤)` Jensen branch for the raw closure, stated directly in terms of the original convexity
assumption on `f`. -/
lemma helperForLemma33_0_5_functionConvexClosure_preserves_convexity_mixedBotTop_case
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hPosB : 0 < b)
    (hClosureXBot :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥)
    (hClosureYTop :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊤) :
    (⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) = ⊥ := by
  let localInf : {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun ε z => ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  have hAllRadiiXBot : ∀ ε : {r : ℝ // 0 < r}, localInf ε x = (⊥ : EReal) := by
    intro ε
    have hLe : localInf ε x ≤ ⨆ ε' : {r : ℝ // 0 < r}, localInf ε' x :=
      le_iSup (fun ε' : {r : ℝ // 0 < r} => localInf ε' x) ε
    exact le_antisymm (by simpa [localInf, hClosureXBot] using hLe) bot_le
  have hAllRadiiTargetBot :
      ∀ ε : {r : ℝ // 0 < r}, localInf ε (a • x + b • y) = (⊥ : EReal) := by
    intro ε
    by_cases hYTop : localInf ε y = (⊤ : EReal)
    · simpa [localInf] using
        helperForLemma33_0_5_fixedRadiusLocalInfimum_mixedBotTop_collapse
          (ε := ε) (f := f) (x := x) (y := y) hConv ha hb hab hPosA hPosB
          (hAllRadiiXBot ε) hYTop
    · have hTargetLe :
          localInf ε (a • x + b • y) ≤
            (a : EReal) * localInf ε x + (b : EReal) * localInf ε y :=
        helperForLemma33_0_5_fixedRadiusLocalInfimum_preserves_convexity
          (ε := ε) (f := f) hConv
          (x := x) (y := y) (Set.mem_univ x) (Set.mem_univ y)
          (a := a) (b := b) ha hb hab (Set.mem_univ _)
      have hRhsBot :
          (a : EReal) * localInf ε x + (b : EReal) * localInf ε y = (⊥ : EReal) := by
        simp [hAllRadiiXBot ε, EReal.coe_mul_bot_of_pos hPosA]
      exact le_antisymm (by simpa [hRhsBot] using hTargetLe) bot_le
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    simpa [localInf, hAllRadiiTargetBot ε]
  · exact bot_le

/-- Helper for Lemma33.0.5: the one-variable convex closure obtained from local infima remains
convex. -/
lemma helperForLemma33_0_5_functionConvexClosure_preserves_convexity {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  let g : (Fin n → ℝ) → EReal :=
    fun z =>
      ⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  have hConvFun : ConvexFunction g :=
    helperForLemma33_0_5_functionConvexClosure_convexFunction (f := f) hConv
  have hLsc : LowerSemicontinuous g := by
    simpa [g] using helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
  intro x y hx hy a b ha hb hab hxy
  by_cases hNoBot : ∀ z, g z ≠ (⊥ : EReal)
  · -- Away from `⊥`, the Chapter 1 Jensen bridge converts epigraph convexity back into the
    -- desired `EReal` inequality directly.
    simpa [g] using
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := g) hConvFun hNoBot
        (x := x) (y := y) hx hy (a := a) (b := b) ha hb hab hxy
  · rcases not_forall.mp hNoBot with ⟨z₀, hz₀Bot⟩
    have hTopOrBot : ∀ z, g z = (⊤ : EReal) ∨ g z = (⊥ : EReal) := by
      -- Once the raw closure attains `⊥`, the closed improper convex classification leaves only
      -- the two infinite values.
      exact helperForLemma33_0_5_closedImproperConvex_values_top_or_bot
        (g := g) hConvFun hLsc ⟨z₀, by simpa using hz₀Bot⟩
    by_cases hZeroA : a = 0
    · have hBOne : b = 1 := by linarith
      -- When the first weight vanishes, the target is exactly `y`.
      subst hZeroA
      subst hBOne
      calc
        g ((0 : ℝ) • x + (1 : ℝ) • y) = g y := by simp
        _ ≤ (0 : EReal) * g x + (1 : EReal) * g y := by simp
    by_cases hZeroB : b = 0
    · have hAOne : a = 1 := by linarith
      -- The symmetric zero-weight case reduces to the first endpoint.
      subst hZeroB
      subst hAOne
      calc
        g ((1 : ℝ) • x + (0 : ℝ) • y) = g x := by simp
        _ ≤ (1 : EReal) * g x + (0 : EReal) * g y := by simp
    have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
    have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
    by_cases hXBot : g x = (⊥ : EReal)
    · by_cases hYTop : g y = (⊤ : EReal)
      · have hTargetBot : g (a • x + b • y) = (⊥ : EReal) :=
          helperForLemma33_0_5_functionConvexClosure_preserves_convexity_mixedBotTop_case
            (f := f) (x := x) (y := y) hConv ha hb hab hPosA hPosB hXBot hYTop
        -- Once the target is `⊥`, the right-hand side collapses because the left endpoint is
        -- already exactly `⊥`.
        simpa [g, hTargetBot, hXBot, EReal.coe_mul_bot_of_pos hPosA]
      · have hTargetBot : g (a • x + b • y) = (⊥ : EReal) :=
          helperForLemma33_0_5_convexFunction_leftBot_rightNotTop_forces_comboBot
            (g := g) hConvFun ha hb hab hPosA hXBot hYTop
        -- Outside the mixed `(⊥, ⊤)` branch, the positive left weight already forces the
        -- Jensen right-hand side to be `⊥`.
        simpa [g, hTargetBot, hXBot, EReal.coe_mul_bot_of_pos hPosA]
    · have hXTop : g x = (⊤ : EReal) := by
        rcases hTopOrBot x with hXT | hXB
        · exact hXT
        · exact False.elim (hXBot hXB)
      by_cases hYBot : g y = (⊥ : EReal)
      · have hTargetBot : g (b • y + a • x) = (⊥ : EReal) :=
          helperForLemma33_0_5_functionConvexClosure_preserves_convexity_mixedBotTop_case
            (f := f) (x := y) (y := x) hConv hb ha (by simpa [add_comm] using hab)
            hPosB hPosA hYBot hXTop
        -- Swap the endpoints to reuse the same raw mixed-corner blocker in the symmetric case.
        simpa [g, add_comm, add_left_comm, add_assoc, hXTop, hYBot,
          EReal.coe_mul_bot_of_pos hPosB] using hTargetBot
      · have hYTop : g y = (⊤ : EReal) := by
          rcases hTopOrBot y with hYT | hYB
          · exact hYT
          · exact False.elim (hYBot hYB)
        -- When both endpoint values are `⊤`, the Jensen right-hand side is trivially `⊤`.
        have hRhsTop : (a : EReal) * g x + (b : EReal) * g y = (⊤ : EReal) := by
          simp [hXTop, hYTop, EReal.coe_mul_top_of_pos hPosA, EReal.coe_mul_top_of_pos hPosB]
        rw [hRhsTop]
        exact le_top

/-- Helper for Lemma33.0.5: `convexClosureInSecond` preserves concavity in the first variable. -/
lemma helperForLemma33_0_5_convexClosureInSecond_preserves_firstVariable_concavity
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} (v : Fin n → ℝ)
    (hConc : ∀ w : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u w)) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
      (fun u => convexClosureInSecond K u v) := by
  intro x y hx hy a b ha hb hab hz
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    -- When the first weight vanishes, the closure value at the second endpoint is unchanged.
    simp [convexClosureInSecond, hZeroA, hBOne]
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    -- The symmetric zero-weight case reduces to the first endpoint.
    simp [convexClosureInSecond, hZeroB, hAOne]
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  let localInf :
      {r : ℝ // 0 < r} → (Fin m → ℝ) → EReal :=
    fun ε u => ⨅ w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}, K u w.1
  have hOuter :
      ((a : EReal) * (⨆ ε : {r : ℝ // 0 < r}, localInf ε x)) +
          ((b : EReal) * (⨆ ε : {r : ℝ // 0 < r}, localInf ε y)) ≤
        ⨆ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
          (a : EReal) * localInf p.1 x + (b : EReal) * localInf p.2 y := by
    -- First choose independent radii for the two endpoints by a product-indexed supremum.
    simpa [localInf] using helperForLemma33_0_5_weightedSum_le_productIndexed_iSup hPosA hPosB
      (f := fun ε : {r : ℝ // 0 < r} => localInf ε x)
      (g := fun ε : {r : ℝ // 0 < r} => localInf ε y)
  have hRadiusComparison :
      (⨆ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
        (a : EReal) * localInf p.1 x + (b : EReal) * localInf p.2 y) ≤
        ⨆ ε : {r : ℝ // 0 < r}, localInf ε (a • x + b • y) := by
    -- Replace the two endpoint radii by their common minimum and then apply the fixed-radius
    -- parameterwise concavity lemma at that smaller radius.
    refine iSup_le ?_
    intro p
    rcases p with ⟨ε₁, ε₂⟩
    let δ : {r : ℝ // 0 < r} := ⟨min ε₁.1 ε₂.1, lt_min ε₁.2 ε₂.2⟩
    have hxMono : localInf ε₁ x ≤ localInf δ x :=
      helperForLemma33_0_5_localInfimum_antitone_radius
        (f := fun w => K x w) (x := v) (δ := δ) (ε := ε₁) (min_le_left _ _)
    have hyMono : localInf ε₂ y ≤ localInf δ y :=
      helperForLemma33_0_5_localInfimum_antitone_radius
        (f := fun w => K y w) (x := v) (δ := δ) (ε := ε₂) (min_le_right _ _)
    have hScaled :
        (a : EReal) * localInf ε₁ x + (b : EReal) * localInf ε₂ y ≤
          (a : EReal) * localInf δ x + (b : EReal) * localInf δ y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxMono hNonnegA)
        (mul_le_mul_of_nonneg_left hyMono hNonnegB)
    have hFixed :
        (a : EReal) * localInf δ x + (b : EReal) * localInf δ y ≤
          localInf δ (a • x + b • y) :=
      helperForLemma33_0_5_fixedRadiusLocalInfimum_preserves_parameterConcavity
        (ε := δ) (v := v) hConc (x := x) (y := y) hx hy ha hb hab hz
    have hToSup :
        localInf δ (a • x + b • y) ≤ ⨆ ε : {r : ℝ // 0 < r}, localInf ε (a • x + b • y) :=
      le_iSup (fun ε : {r : ℝ // 0 < r} => localInf ε (a • x + b • y)) δ
    exact le_trans hScaled (le_trans hFixed hToSup)
  simpa [convexClosureInSecond] using le_trans hOuter hRadiusComparison

/-- Helper for Lemma33.0.5: if the outer `u`-closure equals `⊥`, then every strict upper bound on
`⊥` is beaten by some fixed-radius local supremum. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_eq_bot_implies_exists_radius_localSup_lt
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hBot : concaveClosureInFirst K u x = ⊥) :
    ∀ {z : EReal}, (⊥ : EReal) < z → ∃ ε : {r : ℝ // 0 < r},
      (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) < z := by
  intro z hz
  -- Unfold the outer closure and extract a radius from `iInf_lt_iff`.
  unfold concaveClosureInFirst at hBot
  have hlt :
      (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) < z := by
    simpa [hBot] using hz
  rcases iInf_lt_iff.mp hlt with ⟨ε, hε⟩
  exact ⟨ε, hε⟩

/-- Helper for Lemma33.0.5: if the outer `u`-closure equals `⊤`, then every fixed-radius local
supremum at that point already equals `⊤`. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_eq_top_implies_everyRadius_localSup_eq_top
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hTop : concaveClosureInFirst K u x = ⊤) :
    ∀ ε : {r : ℝ // 0 < r},
      (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) = ⊤ := by
  intro ε
  -- Unfold the outer closure and apply the generic `iInf = ⊤` pointwise lemma to the radius
  -- family.
  unfold concaveClosureInFirst at hTop
  exact helperForLemma33_0_5_iInf_eq_top_implies_pointwise_top hTop ε

/-- Helper for Lemma33.0.5: if some fixed radius already has local supremum `⊥` on the `x`
endpoint, then the outer `u`-closure at the convex combination is also `⊥`. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_radiusBot_forces_targetBot
    {m n : ℕ} (ε : {r : ℝ // 0 < r}) {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a)
    (hLocalSupXBot : (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) = ⊥) :
    concaveClosureInFirst K u (a • x + b • y) = ⊥ := by
  let localSup :
      {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun δ v => ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < δ.1}, K w.1 v
  have hFixed :
      localSup ε (a • x + b • y) ≤
        (a : EReal) * localSup ε x + (b : EReal) * localSup ε y :=
    helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_parameterConvexity
      (ε := ε) (u := u) hConv
      (x := x) (y := y) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  have hFixedBot : localSup ε (a • x + b • y) = ⊥ := by
    -- The exact `⊥` radius on the `x`-side collapses the Jensen upper bound at the same radius.
    have hLeBot : localSup ε (a • x + b • y) ≤ (⊥ : EReal) := by
      calc
        localSup ε (a • x + b • y) ≤
            (a : EReal) * localSup ε x + (b : EReal) * localSup ε y := hFixed
        _ = ⊥ := by simp [localSup, hLocalSupXBot, EReal.coe_mul_bot_of_pos hPosA]
    exact le_antisymm hLeBot bot_le
  have hClosureLe :
      concaveClosureInFirst K u (a • x + b • y) ≤ localSup ε (a • x + b • y) := by
    -- The outer infimum is bounded above by any chosen radius.
    simpa [concaveClosureInFirst, localSup] using
      (iInf_le
        (fun δ : {r : ℝ // 0 < r} =>
          ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < δ.1}, K w.1 (a • x + b • y))
        ε)
  have hTargetLeBot : concaveClosureInFirst K u (a • x + b • y) ≤ (⊥ : EReal) := by
    exact le_trans hClosureLe (by simpa [hFixedBot])
  exact le_antisymm hTargetLeBot bot_le

/-- Helper for Lemma33.0.5: for fixed `u`, the outer `inf-sup` closure is convex in the second
variable when each section `v ↦ K w v` is convex. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_convexFunction
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} (u : Fin m → ℝ)
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v)) :
    ConvexFunction (fun v => concaveClosureInFirst K u v) := by
  -- Route correction: prove the outer `inf-sup` operator directly at finite real heights, so the
  -- remaining blocker is isolated to the generic `ConvexFunction -> IsERealConvexOn` bridge.
  unfold ConvexFunction ConvexFunctionOn epigraph
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  rcases hp with ⟨hpUniv, hpHeight⟩
  rcases hq with ⟨hqUniv, hqHeight⟩
  constructor
  · show a • x + b • y ∈ (Set.univ : Set (Fin n → ℝ))
    simp
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  let localSup :
      {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun ε v => ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 v
  have hBound :
      concaveClosureInFirst K u (a • x + b • y) ≤ (((a * α + b * β : ℝ)) : EReal) := by
    -- Compare the outer infimum to any strict real upper bound, then choose endpoint radii and
    -- shrink them to a common radius.
    refine (EReal.le_of_forall_lt_iff_le
      (x := (((a * α + b * β : ℝ)) : EReal))
      (y := concaveClosureInFirst K u (a • x + b • y))).1 ?_
    intro z hz
    let η : ℝ := z - (a * α + b * β)
    have hzReal : a * α + b * β < z := by
      exact_mod_cast hz
    have hη : 0 < η := by
      exact sub_pos.mpr hzReal
    let ε₀ : {r : ℝ // 0 < r} := ⟨1, by norm_num⟩
    letI : Nonempty {r : ℝ // 0 < r} := ⟨ε₀⟩
    have hXlt :
        concaveClosureInFirst K u x < (((α + η : ℝ)) : EReal) := by
      calc
        concaveClosureInFirst K u x ≤ (α : EReal) := hpHeight
        _ < (((α + η : ℝ)) : EReal) := by
          have hαη : α < α + η := by linarith
          exact_mod_cast hαη
    have hYlt :
        concaveClosureInFirst K u y < (((β + η : ℝ)) : EReal) := by
      calc
        concaveClosureInFirst K u y ≤ (β : EReal) := hqHeight
        _ < (((β + η : ℝ)) : EReal) := by
          have hβη : β < β + η := by linarith
          exact_mod_cast hβη
    rcases iInf_lt_iff.mp (by simpa [concaveClosureInFirst] using hXlt) with ⟨εx, hεx⟩
    rcases iInf_lt_iff.mp (by simpa [concaveClosureInFirst] using hYlt) with ⟨εy, hεy⟩
    let δ : {r : ℝ // 0 < r} := ⟨min εx.1 εy.1, lt_min εx.2 εy.2⟩
    have hxMono : localSup δ x ≤ localSup εx x :=
      helperForLemma33_0_5_localSupremum_monotone_radius
        (f := fun w => K w x) (x := u) (δ := δ) (ε := εx) (min_le_left _ _)
    have hyMono : localSup δ y ≤ localSup εy y :=
      helperForLemma33_0_5_localSupremum_monotone_radius
        (f := fun w => K w y) (x := u) (δ := δ) (ε := εy) (min_le_right _ _)
    have hFixed :
        localSup δ (a • x + b • y) ≤
          (a : EReal) * localSup δ x + (b : EReal) * localSup δ y :=
      helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_parameterConvexity
        (ε := δ) (u := u) hConv
        (x := x) (y := y) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
    have hScaled :
        (a : EReal) * localSup δ x + (b : EReal) * localSup δ y ≤ (z : EReal) := by
      -- Move the shrunken-radius bounds through the nonnegative weights and simplify the real
      -- upper bound back to `z`.
      have hUpperEq : a * (α + η) + b * (β + η) = z := by
        calc
          a * (α + η) + b * (β + η) = (a * α + b * β) + (a + b) * η := by ring
          _ = (a * α + b * β) + η := by rw [hab, one_mul]
          _ = z := by
            dsimp [η]
            ring
      calc
        (a : EReal) * localSup δ x + (b : EReal) * localSup δ y ≤
            (a : EReal) * (((α + η : ℝ)) : EReal) +
              (b : EReal) * (((β + η : ℝ)) : EReal) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (le_trans hxMono hεx.le) hNonnegA)
            (mul_le_mul_of_nonneg_left (le_trans hyMono hεy.le) hNonnegB)
        _ = (z : EReal) := by
          exact_mod_cast hUpperEq
    have hClosureLe :
        concaveClosureInFirst K u (a • x + b • y) ≤ localSup δ (a • x + b • y) := by
      -- The outer infimum is bounded above by every chosen radius.
      simpa [concaveClosureInFirst, localSup] using
        (iInf_le
          (fun ε : {r : ℝ // 0 < r} =>
            ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 (a • x + b • y))
          δ)
    exact le_trans hClosureLe (le_trans hFixed hScaled)
  -- Rewrite the target height back into the second coordinate of the convex combination in the
  -- epigraph.
  simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hBound

/-- Helper for Lemma33.0.5: the target outer `inf-sup` value is controlled by a product-indexed
infimum over independent endpoint radii. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_target_le_productInfimum
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    concaveClosureInFirst K u (a • x + b • y) ≤
      ⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
        (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
          (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y) := by
  let localSup :
      {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun ε v => ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 v
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  -- Compare the target outer infimum to any pair of endpoint radii by shrinking to a common
  -- radius and then applying the fixed-radius convexity lemma there.
  refine le_iInf ?_
  intro p
  rcases p with ⟨ε₁, ε₂⟩
  let δ : {r : ℝ // 0 < r} := ⟨min ε₁.1 ε₂.1, lt_min ε₁.2 ε₂.2⟩
  have hClosureLe :
      concaveClosureInFirst K u (a • x + b • y) ≤ localSup δ (a • x + b • y) := by
    simpa [concaveClosureInFirst, localSup] using
      (iInf_le
        (fun ε : {r : ℝ // 0 < r} =>
          ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 (a • x + b • y))
        δ)
  have hxMono : localSup δ x ≤ localSup ε₁ x :=
    helperForLemma33_0_5_localSupremum_monotone_radius
      (f := fun w => K w x) (x := u) (δ := δ) (ε := ε₁) (min_le_left _ _)
  have hyMono : localSup δ y ≤ localSup ε₂ y :=
    helperForLemma33_0_5_localSupremum_monotone_radius
      (f := fun w => K w y) (x := u) (δ := δ) (ε := ε₂) (min_le_right _ _)
  have hFixed :
      localSup δ (a • x + b • y) ≤
        (a : EReal) * localSup δ x + (b : EReal) * localSup δ y :=
    helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_parameterConvexity
      (ε := δ) (u := u) hConv
      (x := x) (y := y) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  have hScaled :
      (a : EReal) * localSup δ x + (b : EReal) * localSup δ y ≤
        (a : EReal) * localSup ε₁ x + (b : EReal) * localSup ε₂ y := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hxMono hNonnegA)
      (mul_le_mul_of_nonneg_left hyMono hNonnegB)
  exact le_trans hClosureLe (le_trans hFixed hScaled)

/-- Helper for Lemma33.0.5: outside the two mixed `(⊥, ⊤)` corners, the product-indexed
infimum of weighted outer-radius local suprema is bounded by the weighted sum of the outer
closure values. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_productInfimum_nonexceptionalBound
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ}
    {x y : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h₁ : concaveClosureInFirst K u x ≠ (⊥ : EReal) ∨
      concaveClosureInFirst K u y ≠ (⊤ : EReal))
    (h₂ : concaveClosureInFirst K u x ≠ (⊤ : EReal) ∨
      concaveClosureInFirst K u y ≠ (⊥ : EReal)) :
    (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
      (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
        (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y)) ≤
      (a : EReal) * concaveClosureInFirst K u x + (b : EReal) * concaveClosureInFirst K u y := by
  let localSup :
      {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun ε v => ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 v
  let ε₀ : {r : ℝ // 0 < r} := ⟨1, by norm_num⟩
  letI : Nonempty {r : ℝ // 0 < r} := ⟨ε₀⟩
  have h₁Scaled :
      (⨅ ε : {r : ℝ // 0 < r}, (a : EReal) * localSup ε x) ≠ (⊥ : EReal) ∨
        (⨅ ε : {r : ℝ // 0 < r}, (b : EReal) * localSup ε y) ≠ (⊤ : EReal) := by
    rcases h₁ with hX | hY
    · left
      simpa [concaveClosureInFirst, localSup,
          helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
            (fun ε : {r : ℝ // 0 < r} => localSup ε x)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_bot ha hX)
    · right
      simpa [concaveClosureInFirst, localSup,
          helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
            (fun ε : {r : ℝ // 0 < r} => localSup ε y)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_top hb hY)
  have h₂Scaled :
      (⨅ ε : {r : ℝ // 0 < r}, (a : EReal) * localSup ε x) ≠ (⊤ : EReal) ∨
        (⨅ ε : {r : ℝ // 0 < r}, (b : EReal) * localSup ε y) ≠ (⊥ : EReal) := by
    rcases h₂ with hX | hY
    · left
      simpa [concaveClosureInFirst, localSup,
          helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
            (fun ε : {r : ℝ // 0 < r} => localSup ε x)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_top ha hX)
    · right
      simpa [concaveClosureInFirst, localSup,
          helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
            (fun ε : {r : ℝ // 0 < r} => localSup ε y)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_bot hb hY)
  -- Once the scaled outer infima avoid the exceptional corners, the generic product-infimum
  -- estimate applies exactly as in the fixed-radius argument.
  have hBase :
      (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
        (a : EReal) * localSup p.1 x + (b : EReal) * localSup p.2 y) ≤
        (⨅ ε : {r : ℝ // 0 < r}, (a : EReal) * localSup ε x) +
          (⨅ ε : {r : ℝ // 0 < r}, (b : EReal) * localSup ε y) :=
    helperForLemma33_0_5_productIndexed_iInf_weightedSum_le_of_nonexceptional
      (ι := {r : ℝ // 0 < r})
      (κ := {r : ℝ // 0 < r})
      (F := fun ε : {r : ℝ // 0 < r} => (a : EReal) * localSup ε x)
      (G := fun ε : {r : ℝ // 0 < r} => (b : EReal) * localSup ε y)
      h₁Scaled h₂Scaled
  calc
    (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
      (a : EReal) * localSup p.1 x + (b : EReal) * localSup p.2 y) ≤
        (⨅ ε : {r : ℝ // 0 < r}, (a : EReal) * localSup ε x) +
          (⨅ ε : {r : ℝ // 0 < r}, (b : EReal) * localSup ε y) := hBase
    _ = (a : EReal) * concaveClosureInFirst K u x +
          (b : EReal) * concaveClosureInFirst K u y := by
      rw [(helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
            (fun ε : {r : ℝ // 0 < r} => localSup ε x)).symm,
        (helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
            (fun ε : {r : ℝ // 0 < r} => localSup ε y)).symm]
      simp [concaveClosureInFirst, localSup]

/-- Helper for Lemma33.0.5: the true outer `(⊥, ⊤)` branch for `concaveClosureInFirst` is where
the current local-radius route stops. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_commonRadius_mixedBotTop_bridge
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v))
    (hCenterNoBot : K u x ≠ (⊥ : EReal))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hPosB : 0 < b)
    (hClosureXBot :
      (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) = ⊥)
    (hClosureYTop :
      (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 y) = ⊤) :
    concaveClosureInFirst K u (a • x + b • y) = ⊥ := by
  exfalso
  apply hCenterNoBot
  apply le_antisymm
  · have hCenterLeClosure : K u x ≤ concaveClosureInFirst K u x := by
      unfold concaveClosureInFirst
      refine le_iInf ?_
      intro ε
      let wu : {w : Fin m → ℝ // ‖w - u‖ < ε.1} :=
        ⟨u, by simpa using ε.2⟩
      exact le_iSup_of_le wu le_rfl
    unfold concaveClosureInFirst at hCenterLeClosure
    rw [hClosureXBot] at hCenterLeClosure
    exact hCenterLeClosure
  · exact bot_le

/-- Helper for Lemma33.0.5: the true outer `(⊥, ⊤)` branch for `concaveClosureInFirst` is where
the current local-radius route stops. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_exceptional_branch
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} {u : Fin m → ℝ}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v))
    (hCenterNoBot : K u x ≠ (⊥ : EReal))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hPosB : 0 < b)
    (hClosureXBot :
      (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) = ⊥)
    (hClosureYTop :
      (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 y) = ⊤) :
    concaveClosureInFirst K u (a • x + b • y) ≤
      (a : EReal) * (⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) +
        (b : EReal) * (⨅ ε : {r : ℝ // 0 < r},
          ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 y) := by
  -- Reduce the branch to the exact target-`⊥` bridge, then simplify the right-hand side to `⊥`.
  have hTargetBot :
      concaveClosureInFirst K u (a • x + b • y) = ⊥ :=
    helperForLemma33_0_5_concaveClosureInFirst_commonRadius_mixedBotTop_bridge
      (K := K) (u := u) (x := x) (y := y) hConv hCenterNoBot ha hb hab hPosA hPosB
      hClosureXBot hClosureYTop
  have hRhsBot :
      (a : EReal) * (⨅ ε : {r : ℝ // 0 < r},
          ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) +
          (b : EReal) * (⨅ ε : {r : ℝ // 0 < r},
            ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 y) = ⊥ := by
    simp [hClosureXBot, hClosureYTop, EReal.coe_mul_bot_of_pos hPosA]
  rw [hTargetBot, hRhsBot]

/-- Helper for Lemma33.0.5: `concaveClosureInFirst` preserves convexity in the second variable. -/
lemma helperForLemma33_0_5_concaveClosureInFirst_preserves_secondVariable_convexity_of_noBot
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} (u : Fin m → ℝ)
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v))
    (hNoBot : ∀ w v, K w v ≠ (⊥ : EReal)) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun v => concaveClosureInFirst K u v) := by
  let closure : (Fin n → ℝ) → EReal := fun v => concaveClosureInFirst K u v
  intro x y hx hy a b ha hb hab hz
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    -- When the first weight vanishes, the target point is exactly `y`.
    subst hZeroA
    subst hBOne
    calc
      closure ((0 : ℝ) • x + (1 : ℝ) • y) = closure y := by simp [closure]
      _ ≤ (0 : EReal) * closure x + (1 : EReal) * closure y := by simp
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    -- The symmetric zero-weight case reduces to the first endpoint.
    subst hZeroB
    subst hAOne
    calc
      closure ((1 : ℝ) • x + (0 : ℝ) • y) = closure x := by simp [closure]
      _ ≤ (1 : EReal) * closure x + (0 : EReal) * closure y := by simp
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  have hTargetLeProduct :
      closure (a • x + b • y) ≤
        ⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
          (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
            (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y) := by
    -- Compare the target outer infimum to independent endpoint radii before splitting into
    -- the mixed exceptional corners.
    simpa [closure] using
      helperForLemma33_0_5_concaveClosureInFirst_target_le_productInfimum
        (K := K) (u := u) (x := x) (y := y) hConv ha hb hab
  by_cases hClosureXBot : closure x = (⊥ : EReal)
  · by_cases hClosureYTop : closure y = (⊤ : EReal)
    · -- The only remaining outer mixed corner is isolated in the dedicated exceptional-branch
      -- wrapper above.
      simpa [closure] using
        helperForLemma33_0_5_concaveClosureInFirst_exceptional_branch
          (K := K) (u := u) (x := x) (y := y) hConv (hNoBot u x)
          ha hb hab hPosA hPosB
          hClosureXBot hClosureYTop
    · have hProductLe :
          (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
            (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
              (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y)) ≤
            (a : EReal) * closure x + (b : EReal) * closure y := by
          simpa [closure] using
            helperForLemma33_0_5_concaveClosureInFirst_productInfimum_nonexceptionalBound
              (K := K) (u := u) (x := x) (y := y) hPosA hPosB
              (Or.inr hClosureYTop) (Or.inl (by simpa [closure, hClosureXBot]))
      exact le_trans hTargetLeProduct hProductLe
  · by_cases hClosureXTop : closure x = (⊤ : EReal)
    · by_cases hClosureYBot : closure y = (⊥ : EReal)
      · -- Swap the two endpoints to reuse the same mixed-corner lemma in the symmetric branch.
        have hSymm :
            closure (b • y + a • x) ≤
              (b : EReal) * closure y + (a : EReal) * closure x := by
          simpa [closure] using
            helperForLemma33_0_5_concaveClosureInFirst_exceptional_branch
              (K := K) (u := u) (x := y) (y := x) hConv (hNoBot u y) hb ha
              (by simpa [add_comm] using hab) hPosB hPosA hClosureYBot hClosureXTop
        simpa [closure, add_comm, add_left_comm, add_assoc] using hSymm
      · have hProductLe :
          (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
            (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
              (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y)) ≤
            (a : EReal) * closure x + (b : EReal) * closure y := by
          simpa [closure] using
            helperForLemma33_0_5_concaveClosureInFirst_productInfimum_nonexceptionalBound
              (K := K) (u := u) (x := x) (y := y) hPosA hPosB
              (Or.inl (by simpa [closure, hClosureXTop])) (Or.inr hClosureYBot)
        exact le_trans hTargetLeProduct hProductLe
    · have hProductLe :
        (⨅ p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r},
          (a : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.1.1}, K w.1 x) +
            (b : EReal) * (⨆ w : {w : Fin m → ℝ // ‖w - u‖ < p.2.1}, K w.1 y)) ≤
          (a : EReal) * closure x + (b : EReal) * closure y := by
        simpa [closure] using
          helperForLemma33_0_5_concaveClosureInFirst_productInfimum_nonexceptionalBound
            (K := K) (u := u) (x := x) (y := y) hPosA hPosB
            (Or.inl hClosureXBot) (Or.inl hClosureXTop)
      exact le_trans hTargetLeProduct hProductLe

/-! The book defines convexity and concavity by convex epi- and hypographs.  This distinction is
essential for improper mixed `⊥/⊤` sections: Mathlib's totalized `EReal` addition makes the
unqualified two-point Jensen predicate strictly stronger than epigraph convexity. -/

/-- A concave-convex kernel in the literal Rockafellar epi/hypograph sense. -/
def IsEpigraphHypographConcaveConvex {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∀ v, Convex ℝ (extendedRealHypograph (fun u => K u v))) ∧
    ∀ u, ConvexFunction (fun v => K u v)

/-- The symmetric epi/hypograph notion for a kernel convex in its first argument and concave
in its second argument. -/
def IsEpigraphHypographConvexConcave {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsEpigraphHypographConcaveConvex (fun v u => K u v)

/-- The strong concave Jensen predicate implies convexity of the real-height hypograph. -/
lemma helperForLemma33_0_5_isERealConcaveOn_univ_to_hypographConvex {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) f) :
    Convex ℝ (extendedRealHypograph f) := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by exact_mod_cast hb
  have hHeight :
      (((a * α + b * β : ℝ)) : EReal) ≤
        (a : EReal) * f x + (b : EReal) * f y := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hp hNonnegA)
      (mul_le_mul_of_nonneg_left hq hNonnegB)
  have hJensen :
      (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y) :=
    hConc (Set.mem_univ x) (Set.mem_univ y) ha hb hab (Set.mem_univ _)
  simpa [extendedRealHypograph, smul_eq_mul, EReal.coe_add, EReal.coe_mul] using
    le_trans hHeight hJensen

/-- Corollary33.1.1 in the book's epi/hypograph semantics: both coordinatewise closures remain
concave-convex, including the improper mixed endpoint cases. -/
lemma isConcaveConvexOn_univ_closureData_closures
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K) :
    IsEpigraphHypographConcaveConvex (convexConcaveClosureData K).cl_v ∧
      IsEpigraphHypographConcaveConvex (convexConcaveClosureData K).cl_u := by
  rcases hK with ⟨hConc, hConv⟩
  constructor
  · constructor
    · intro v
      apply helperForLemma33_0_5_isERealConcaveOn_univ_to_hypographConvex
      simpa [convexConcaveClosureData] using
        helperForLemma33_0_5_convexClosureInSecond_preserves_firstVariable_concavity
          (K := K) (v := v) (fun w => hConc w (Set.mem_univ w))
    · intro u
      simpa [convexConcaveClosureData, convexClosureInSecond] using
        helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
          (helperForLemma33_0_5_functionConvexClosure_preserves_convexity
            (f := fun v => K u v) (hConv u (Set.mem_univ u)))
  · constructor
    · intro v
      apply helperForLemma33_0_5_isERealConcaveOn_univ_to_hypographConvex
      simpa [convexConcaveClosureData, concaveClosureInFirst] using
        helperForLemma33_0_5_functionConcaveClosure_preserves_concavity
          (f := fun u => K u v) (hConc v (Set.mem_univ v))
    · intro u
      simpa [convexConcaveClosureData] using
        helperForLemma33_0_5_concaveClosureInFirst_convexFunction
          (K := K) u (fun w => hConv w (Set.mem_univ w))

-- Proof sketch: apply the standard fact that taking the lower semicontinuous regularization
-- in the second variable preserves convexity in that variable and leaves concavity in the
-- first variable intact; argue dually for the upper semicontinuous regularization in the
-- first variable.
/-- Lemma33.0.5: If `K : ℝ^m × ℝ^n → EReal` is concave-convex, then the closure operators
from Definition33.0.4 produce bifunctions `(cl_v K)` and `(cl_u K)` that are also
concave-convex. -/
lemma isConcaveConvexOn_univ_closureData_closures_of_noBot
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hNoBot : ∀ u v, K u v ≠ (⊥ : EReal)) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (convexConcaveClosureData K).cl_v ∧
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (convexConcaveClosureData K).cl_u := by
  rcases hK with ⟨hConc, hConv⟩
  constructor
  · constructor
    · -- The first-variable concavity of `cl_v` is exactly the mixed closure helper.
      intro v hv
      have hSection :
          ∀ w : Fin n → ℝ,
            IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u w) := by
        intro w
        exact hConc w (Set.mem_univ w)
      simpa [convexConcaveClosureData]
        using helperForLemma33_0_5_convexClosureInSecond_preserves_firstVariable_concavity
          (K := K) (v := v) hSection
    · -- The second-variable convexity of `cl_v` comes from the one-variable closure lemma.
      intro u hu
      have hSection :
          IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K u v) :=
        hConv u (Set.mem_univ u)
      simpa [convexConcaveClosureData, convexClosureInSecond]
        using helperForLemma33_0_5_functionConvexClosure_preserves_convexity
          (f := fun v => K u v) hSection
  · constructor
    · -- The first-variable concavity of `cl_u` is the one-variable concave-closure statement.
      intro v hv
      have hSection :
          IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u v) :=
        hConc v (Set.mem_univ v)
      simpa [convexConcaveClosureData, concaveClosureInFirst]
        using helperForLemma33_0_5_functionConcaveClosure_preserves_concavity
          (f := fun u => K u v) hSection
    · -- The second-variable convexity of `cl_u` is exactly the mixed closure helper.
      intro u hu
      have hSection :
          ∀ w : Fin m → ℝ,
            IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v) := by
        intro w
        exact hConv w (Set.mem_univ w)
      simpa [convexConcaveClosureData]
        using helperForLemma33_0_5_concaveClosureInFirst_preserves_secondVariable_convexity_of_noBot
          (K := K) (u := u) hSection hNoBot

/-- A real-valued bifunction on `ℝ^m × ℝ^n` is bilinear when it is additive and
homogeneous in each variable separately. -/
def IsBilinearOnReal {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  (∀ u₁ u₂ xStar, K (u₁ + u₂) xStar = K u₁ xStar + K u₂ xStar) ∧
    (∀ a u xStar, K (a • u) xStar = a * K u xStar) ∧
    (∀ u xStar₁ xStar₂, K u (xStar₁ + xStar₂) = K u xStar₁ + K u xStar₂) ∧
    ∀ a u xStar, K u (a • xStar) = a * K u xStar

/-- Helper for Theorem33.0.6: the pairing induced by a linear map is bilinear in both variables. -/
lemma helperForTheorem33_0_6_pairing_bilinear_of_linearMap
    {m n : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    IsBilinearOnReal (fun u xStar => dotProduct (A u) xStar) := by
  constructor
  · intro u₁ u₂ xStar
    -- Rewrite addition through `A` and use additivity of the dot product in its first input.
    change dotProduct (A (u₁ + u₂)) xStar =
      dotProduct (A u₁) xStar + dotProduct (A u₂) xStar
    rw [A.map_add, add_dotProduct]
  · constructor
    · intro a u xStar
      -- Rewrite scalar multiplication through `A` and use homogeneity of the dot product.
      change dotProduct (A (a • u)) xStar = a * dotProduct (A u) xStar
      rw [A.map_smul, smul_dotProduct]
      rfl
    · constructor
      · intro u xStar₁ xStar₂
        -- Additivity in the second variable is the standard `dotProduct_add` identity.
        change dotProduct (A u) (xStar₁ + xStar₂) =
          dotProduct (A u) xStar₁ + dotProduct (A u) xStar₂
        rw [dotProduct_add]
      · intro a u xStar
        -- Homogeneity in the second variable is the standard `dotProduct_smul` identity.
        change dotProduct (A u) (a • xStar) = a * dotProduct (A u) xStar
        rw [dotProduct_smul]
        rfl

/-- Helper for Theorem33.0.6: bilinearity in the second variable forces `K u 0 = 0`. -/
lemma helperForTheorem33_0_6_secondVariable_zero
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) (u : Fin m → ℝ) :
    K u 0 = 0 := by
  -- Specialize homogeneity in the second variable to the scalar `0`.
  simpa using hK.2.2.2 0 u (0 : Fin n → ℝ)

/-- Helper for Theorem33.0.6: bilinearity expands `K u` across a finite sum in the second variable. -/
lemma helperForTheorem33_0_6_coordinateSum_in_second_variable
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) (u : Fin m → ℝ)
    (s : Finset (Fin n)) (c : Fin n → ℝ) :
    K u (∑ i ∈ s, c i • Pi.single (M := fun _ : Fin n => ℝ) i 1) =
      ∑ i ∈ s, c i * K u (Pi.single (M := fun _ : Fin n => ℝ) i 1) := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is zero, so the claim reduces to the previously isolated zero lemma.
      simp [helperForTheorem33_0_6_secondVariable_zero hK u]
  | @insert i s hi ih =>
      -- Split off the new basis vector and use additivity plus homogeneity in the second variable.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hK.2.2.1]
      rw [ih, hK.2.2.2]

/-- Helper for Theorem33.0.6: a bilinear kernel admits a coordinate expansion in the second variable. -/
lemma helperForTheorem33_0_6_coordinateExpansion_in_second_variable
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    K u xStar = ∑ i, xStar i * K u (Pi.single (M := fun _ : Fin n => ℝ) i 1) := by
  calc
    K u xStar = K u (∑ i, xStar i • Pi.single (M := fun _ : Fin n => ℝ) i 1) := by
      -- Expand `xStar` in the canonical basis of coordinate vectors.
      conv_lhs => rw [pi_eq_sum_univ' xStar]
    _ = ∑ i, xStar i * K u (Pi.single (M := fun _ : Fin n => ℝ) i 1) := by
      -- Push `K u` through the coordinate sum using bilinearity in the second variable.
      simpa using helperForTheorem33_0_6_coordinateSum_in_second_variable hK u Finset.univ xStar

/-- Helper for Theorem33.0.6: the coordinate reconstruction is additive in the source variable. -/
lemma helperForTheorem33_0_6_reconstructedLinearMap_map_add
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) (u₁ u₂ : Fin m → ℝ) :
    (fun i => K (u₁ + u₂) (Pi.single (M := fun _ : Fin n => ℝ) i 1)) =
      (fun i => K u₁ (Pi.single (M := fun _ : Fin n => ℝ) i 1) +
        K u₂ (Pi.single (M := fun _ : Fin n => ℝ) i 1)) := by
  -- Compare the two coordinate functions one coordinate at a time.
  funext i
  exact hK.1 u₁ u₂ (Pi.single (M := fun _ : Fin n => ℝ) i 1)

/-- Helper for Theorem33.0.6: the coordinate reconstruction is homogeneous in the source variable. -/
lemma helperForTheorem33_0_6_reconstructedLinearMap_map_smul
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) (a : ℝ) (u : Fin m → ℝ) :
    (fun i => K (a • u) (Pi.single (M := fun _ : Fin n => ℝ) i 1)) =
      a • (fun i : Fin n => K u (Pi.single (M := fun _ : Fin n => ℝ) i 1)) := by
  -- Again, reduce linearity to the coordinate formulas supplied by bilinearity in the first variable.
  funext i
  simpa using hK.2.1 a u (Pi.single (M := fun _ : Fin n => ℝ) i 1)

/-- Helper for Theorem33.0.6: a bilinear kernel reconstructs a linear map from its coordinate values. -/
def helperForTheorem33_0_6_reconstructedLinearMap
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hK : IsBilinearOnReal K) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := fun u i => K u (Pi.single (M := fun _ : Fin n => ℝ) i 1)
    map_add' := helperForTheorem33_0_6_reconstructedLinearMap_map_add hK
    map_smul' := helperForTheorem33_0_6_reconstructedLinearMap_map_smul hK }

/-- Helper for Theorem33.0.6: the reconstructed coordinate map represents the original bilinear kernel. -/
lemma helperForTheorem33_0_6_reconstructedLinearMap_represents_kernel
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsBilinearOnReal K) :
    ∀ u xStar, K u xStar =
      dotProduct (helperForTheorem33_0_6_reconstructedLinearMap K hK u) xStar := by
  intro u xStar
  calc
    K u xStar = ∑ i, xStar i * K u (Pi.single (M := fun _ : Fin n => ℝ) i 1) :=
      helperForTheorem33_0_6_coordinateExpansion_in_second_variable hK u xStar
    _ = ∑ i, K u (Pi.single (M := fun _ : Fin n => ℝ) i 1) * xStar i := by
      -- Commute each scalar factor so the sum matches the `dotProduct` definition.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [mul_comm]
    _ = dotProduct (helperForTheorem33_0_6_reconstructedLinearMap K hK u) xStar := by
      -- Unfold the reconstructed map and the coordinate dot product.
      simp [helperForTheorem33_0_6_reconstructedLinearMap, dotProduct]

/-- Helper for Theorem33.0.6: a representing linear map is determined by testing against basis vectors. -/
lemma helperForTheorem33_0_6_representation_unique
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {A B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hA : ∀ u xStar, K u xStar = dotProduct (A u) xStar)
    (hB : ∀ u xStar, K u xStar = dotProduct (B u) xStar) :
    A = B := by
  apply LinearMap.ext
  intro u
  funext i
  -- Evaluate both representation formulas on the `i`th basis vector.
  have hAi := hA u (Pi.single (M := fun _ : Fin n => ℝ) i 1)
  have hBi := hB u (Pi.single (M := fun _ : Fin n => ℝ) i 1)
  rw [dotProduct_single_one] at hAi hBi
  exact hAi.symm.trans hBi

-- Proof sketch: the forward implication is the routine bilinearity of the coordinate pairing.
-- For the converse, reconstruct `A u` from the coordinate values `K u (Pi.single i 1)`, expand any
-- `xStar` in the standard basis, and then prove uniqueness by testing the representation on basis vectors.
/-- Theorem33.0.6: Let `A : ℝ^m → ℝ^n` be linear and define `K(u, x^*) = ⟪A u, x^*⟫`.
Then `K` is bilinear on `ℝ^m × ℝ^n`. Conversely, if `K : ℝ^m × ℝ^n → ℝ` is bilinear,
then there exists a unique linear map `A : ℝ^m → ℝ^n` such that
`K(u, x^*) = (A u) ⬝ᵥ x^*` for all `u` and `x^*`, where `⬝ᵥ` is the standard Euclidean
pairing on coordinate vectors. -/
theorem bilinear_forms_and_linear_maps
    {m n : ℕ} :
    (∀ A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      IsBilinearOnReal (fun u xStar => dotProduct (A u) xStar)) ∧
    (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ,
      IsBilinearOnReal K →
        ∃! A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ),
          ∀ u xStar, K u xStar = dotProduct (A u) xStar) := by
  constructor
  · intro A
    -- The forward direction is exactly the isolated bilinearity lemma for pairings.
    exact helperForTheorem33_0_6_pairing_bilinear_of_linearMap A
  · intro K hK
    -- Use the coordinate reconstruction as the candidate representing linear map.
    refine ⟨helperForTheorem33_0_6_reconstructedLinearMap K hK,
      helperForTheorem33_0_6_reconstructedLinearMap_represents_kernel hK, ?_⟩
    intro B hB
    -- Uniqueness follows by testing both representations on the standard basis vectors.
    exact (helperForTheorem33_0_6_representation_unique
      (K := K)
      (A := helperForTheorem33_0_6_reconstructedLinearMap K hK)
      (B := B)
      (hA := helperForTheorem33_0_6_reconstructedLinearMap_represents_kernel hK)
      (hB := hB)).symm

/-- Helper for Corollary33.0.7: the first-variable Jensen combination for the bilinear pairing
is an exact equality after coercing the real-valued pairing into `EReal`. -/
lemma helperForCorollary33_0_7_firstVariable_jensen_eq
    {m n : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (x y : Fin m → ℝ) (xStar : Fin n → ℝ) (a b : ℝ) :
    ((dotProduct (A (a • x + b • y)) xStar : ℝ) : EReal) =
      (a : EReal) * ((dotProduct (A x) xStar : ℝ) : EReal) +
        (b : EReal) * ((dotProduct (A y) xStar : ℝ) : EReal) := by
  -- Reuse Theorem 33.0.6 to expand the pairing linearly in the source variable.
  have hBil := (bilinear_forms_and_linear_maps (m := m) (n := n)).1 A
  have hReal :
      dotProduct (A (a • x + b • y)) xStar =
        a * dotProduct (A x) xStar + b * dotProduct (A y) xStar := by
    calc
      dotProduct (A (a • x + b • y)) xStar
          = dotProduct (A (a • x)) xStar + dotProduct (A (b • y)) xStar := by
            simpa using hBil.1 (a • x) (b • y) xStar
      _ = a * dotProduct (A x) xStar + b * dotProduct (A y) xStar := by
            exact congrArg₂ (fun p q : ℝ => p + q) (hBil.2.1 a x xStar) (hBil.2.1 b y xStar)
  -- Coercing the real identity into `EReal` gives the exact Jensen formula.
  simpa [EReal.coe_add, EReal.coe_mul] using congrArg (fun t : ℝ => ((t : ℝ) : EReal)) hReal

/-- Helper for Corollary33.0.7: the second-variable Jensen combination for the bilinear pairing
is likewise an exact equality after coercion to `EReal`. -/
lemma helperForCorollary33_0_7_secondVariable_jensen_eq
    {m n : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (xStar₁ xStar₂ : Fin n → ℝ) (a b : ℝ) :
    ((dotProduct (A u) (a • xStar₁ + b • xStar₂) : ℝ) : EReal) =
      (a : EReal) * ((dotProduct (A u) xStar₁ : ℝ) : EReal) +
        (b : EReal) * ((dotProduct (A u) xStar₂ : ℝ) : EReal) := by
  -- Reuse Theorem 33.0.6 to expand the pairing linearly in the dual variable.
  have hBil := (bilinear_forms_and_linear_maps (m := m) (n := n)).1 A
  have hReal :
      dotProduct (A u) (a • xStar₁ + b • xStar₂) =
        a * dotProduct (A u) xStar₁ + b * dotProduct (A u) xStar₂ := by
    calc
      dotProduct (A u) (a • xStar₁ + b • xStar₂)
          = dotProduct (A u) (a • xStar₁) + dotProduct (A u) (b • xStar₂) := by
            simpa using hBil.2.2.1 u (a • xStar₁) (b • xStar₂)
      _ = a * dotProduct (A u) xStar₁ + b * dotProduct (A u) xStar₂ := by
            exact
              congrArg₂ (fun p q : ℝ => p + q)
                (hBil.2.2.2 a u xStar₁) (hBil.2.2.2 b u xStar₂)
  -- Coercing the real identity into `EReal` gives the exact Jensen formula.
  simpa [EReal.coe_add, EReal.coe_mul] using congrArg (fun t : ℝ => ((t : ℝ) : EReal)) hReal

/-- Helper for Corollary33.0.7: the exact Jensen identities in each variable package into both
the concave-convex and convex-concave orientations of the bilinear pairing kernel. -/
lemma helperForCorollary33_0_7_concaveConvex_and_convexConcave
    {m n : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => ((dotProduct (A u) xStar : ℝ) : EReal)) ∧
    IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => ((dotProduct (A u) xStar : ℝ) : EReal)) := by
  constructor
  · constructor
    · intro xStar hxStar
      intro x y hx hy a b ha hb hab hxy
      -- In the first variable, linearity makes the concavity Jensen inequality an equality.
      exact le_of_eq
        (helperForCorollary33_0_7_firstVariable_jensen_eq
          (A := A) (x := x) (y := y) (xStar := xStar) (a := a) (b := b)).symm
    · intro u hu
      intro xStar₁ xStar₂ hx hy a b ha hb hab hxy
      -- In the second variable, the same equality proves convexity.
      exact le_of_eq
        (helperForCorollary33_0_7_secondVariable_jensen_eq
          (A := A) (u := u) (xStar₁ := xStar₁) (xStar₂ := xStar₂) (a := a) (b := b))
  · constructor
    · intro xStar hxStar
      intro x y hx hy a b ha hb hab hxy
      -- Reusing the first-variable equality in the forward direction gives convexity.
      exact le_of_eq
        (helperForCorollary33_0_7_firstVariable_jensen_eq
          (A := A) (x := x) (y := y) (xStar := xStar) (a := a) (b := b))
    · intro u hu
      intro xStar₁ xStar₂ hx hy a b ha hb hab hxy
      -- Reversing the second-variable equality gives the concavity inequality.
      exact le_of_eq
        (helperForCorollary33_0_7_secondVariable_jensen_eq
          (A := A) (u := u) (xStar₁ := xStar₁) (xStar₂ := xStar₂) (a := a) (b := b)).symm

-- Proof sketch: for each fixed variable, the function is linear in the other variable,
-- hence simultaneously convex and concave on the whole space; combining the two coordinatewise
-- statements gives both saddle-function orientations, and either one implies the saddle property.
/-- Corollary33.0.7: Any bifunction of the form `K(u, x^*) = ⟪A u, x^*⟫` with `A : ℝ^m → ℝ^n`
is both concave-convex and convex-concave on `ℝ^m × ℝ^n`, hence is a saddle function. -/
theorem bilinear_pairing_is_saddle
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => ((dotProduct (A u) xStar : ℝ) : EReal)) ∧
      IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => ((dotProduct (A u) xStar : ℝ) : EReal)) ∧
      IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => ((dotProduct (A u) xStar : ℝ) : EReal)) := by
  -- Package the slice-wise Jensen equalities into the two saddle orientations first.
  rcases helperForCorollary33_0_7_concaveConvex_and_convexConcave (A := A) with
    ⟨hConcaveConvex, hConvexConcave⟩
  refine ⟨hConcaveConvex, hConvexConcave, ?_⟩
  -- Either orientation is enough for the saddle-function definition.
  exact Or.inl hConcaveConvex


end Section33
end Chap07
