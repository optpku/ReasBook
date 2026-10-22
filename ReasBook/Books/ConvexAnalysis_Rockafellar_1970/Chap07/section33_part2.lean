/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part1

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.5: outside the two mixed `(⊥, ⊤)` corners, the product-indexed
infimum of weighted endpoint values is bounded by the weighted sum of the endpoint local
infima. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_productInfimum_nonexceptionalBound {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    {x y : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h₁ :
      (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≠ (⊥ : EReal) ∨
        (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) ≠ (⊤ : EReal))
    (h₂ :
      (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≠ (⊤ : EReal) ∨
        (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) ≠ (⊥ : EReal)) :
    (⨅ p :
        {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
          {w : Fin n → ℝ // ‖w - y‖ < ε.1},
      (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1) ≤
      (a : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) +
        (b : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) := by
  let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
  let wy : {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨y, by simpa using ε.2⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨wx⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨wy⟩
  have h₁Scaled :
      (⨅ i : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, (a : EReal) * f i.1) ≠ (⊥ : EReal) ∨
        (⨅ j : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, (b : EReal) * f j.1) ≠ (⊤ : EReal) := by
    rcases h₁ with hX | hY
    · left
      simpa [helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
          (fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => f w.1)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_bot ha hX)
    · right
      simpa [helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
          (fun w : {w : Fin n → ℝ // ‖w - y‖ < ε.1} => f w.1)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_top hb hY)
  have h₂Scaled :
      (⨅ i : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, (a : EReal) * f i.1) ≠ (⊤ : EReal) ∨
        (⨅ j : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, (b : EReal) * f j.1) ≠ (⊥ : EReal) := by
    rcases h₂ with hX | hY
    · left
      simpa [helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
          (fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => f w.1)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_top ha hX)
    · right
      simpa [helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
          (fun w : {w : Fin n → ℝ // ‖w - y‖ < ε.1} => f w.1)]
        using (helperForLemma33_0_5_positiveReal_mul_ne_bot hb hY)
  -- Once the scaled endpoint infima avoid the exceptional corners, the generic product-infimum
  -- estimate applies directly.
  simpa [helperForLemma33_0_5_positiveReal_mul_iInf (a := a) ha
      (fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => f w.1),
    helperForLemma33_0_5_positiveReal_mul_iInf (a := b) hb
      (fun w : {w : Fin n → ℝ // ‖w - y‖ < ε.1} => f w.1)]
    using
      (helperForLemma33_0_5_productIndexed_iInf_weightedSum_le_of_nonexceptional
        (ι := {w : Fin n → ℝ // ‖w - x‖ < ε.1})
        (κ := {w : Fin n → ℝ // ‖w - y‖ < ε.1})
        (F := fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => (a : EReal) * f w.1)
        (G := fun w : {w : Fin n → ℝ // ‖w - y‖ < ε.1} => (b : EReal) * f w.1)
        h₁Scaled h₂Scaled)

/-- Helper for Lemma33.0.5: at a fixed radius, local infima preserve convexity. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_preserves_convexity {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  let localInf : (Fin n → ℝ) → EReal :=
    fun z => ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  intro x y hx hy a b ha hb hab hz
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    -- When the first weight vanishes, the target center is exactly `y`, so the inequality is
    -- the identity map on the second local infimum.
    subst hZeroA
    subst hBOne
    calc
      localInf ((0 : ℝ) • x + (1 : ℝ) • y) = localInf y := by simp [localInf]
      _ ≤ (0 : EReal) * localInf x + (1 : EReal) * localInf y := by simp
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    -- The symmetric zero-weight case reduces to the first endpoint.
    subst hZeroB
    subst hAOne
    calc
      localInf ((1 : ℝ) • x + (0 : ℝ) • y) = localInf x := by simp [localInf]
      _ ≤ (1 : EReal) * localInf x + (0 : EReal) * localInf y := by simp
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  have hTargetLeProduct :
      localInf (a • x + b • y) ≤
        ⨅ p :
            {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
              {w : Fin n → ℝ // ‖w - y‖ < ε.1},
          (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1 :=
    helperForLemma33_0_5_fixedRadiusLocalInfimum_target_le_productInfimum
      (ε := ε) (f := f) (x := x) (y := y) hConv ha hb hab
  by_cases hLocalInfXBot : localInf x = (⊥ : EReal)
  · by_cases hLocalInfYTop : localInf y = (⊤ : EReal)
    · -- This is the only genuinely mixed corner, and it is exactly the remaining fixed-radius
      -- blocker isolated in `helperForLemma33_0_5_fixedRadiusLocalInfimum_exceptional_branch`.
      simpa [localInf] using
        helperForLemma33_0_5_fixedRadiusLocalInfimum_exceptional_branch
          (ε := ε) (f := f) (x := x) (y := y) hConv ha hb hab hPosA hPosB
          hLocalInfXBot hLocalInfYTop
    · have hProductLe :
          (⨅ p :
              {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
                {w : Fin n → ℝ // ‖w - y‖ < ε.1},
            (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1) ≤
            (a : EReal) * localInf x + (b : EReal) * localInf y :=
        helperForLemma33_0_5_fixedRadiusLocalInfimum_productInfimum_nonexceptionalBound
          (ε := ε) (f := f) (x := x) (y := y) hPosA hPosB
          (Or.inr hLocalInfYTop) (Or.inl (by simpa [localInf, hLocalInfXBot]))
      exact le_trans hTargetLeProduct hProductLe
  · by_cases hLocalInfXTop : localInf x = (⊤ : EReal)
    · by_cases hLocalInfYBot : localInf y = (⊥ : EReal)
      · -- Swap the endpoints to reuse the same mixed-corner lemma in the symmetric `(⊤, ⊥)` case.
        have hSymm :
            localInf (b • y + a • x) ≤
              (b : EReal) * localInf y + (a : EReal) * localInf x := by
          simpa [localInf] using
            helperForLemma33_0_5_fixedRadiusLocalInfimum_exceptional_branch
              (ε := ε) (f := f) (x := y) (y := x) hConv hb ha (by simpa [add_comm] using hab)
              hPosB hPosA hLocalInfYBot hLocalInfXTop
        simpa [localInf, add_comm, add_left_comm, add_assoc] using hSymm
      · have hProductLe :
            (⨅ p :
                {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
                  {w : Fin n → ℝ // ‖w - y‖ < ε.1},
              (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1) ≤
              (a : EReal) * localInf x + (b : EReal) * localInf y :=
          helperForLemma33_0_5_fixedRadiusLocalInfimum_productInfimum_nonexceptionalBound
            (ε := ε) (f := f) (x := x) (y := y) hPosA hPosB
            (Or.inl hLocalInfXBot) (Or.inr hLocalInfYBot)
        exact le_trans hTargetLeProduct hProductLe
    · have hProductLe :
          (⨅ p :
              {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
                {w : Fin n → ℝ // ‖w - y‖ < ε.1},
            (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1) ≤
            (a : EReal) * localInf x + (b : EReal) * localInf y :=
        helperForLemma33_0_5_fixedRadiusLocalInfimum_productInfimum_nonexceptionalBound
          (ε := ε) (f := f) (x := x) (y := y) hPosA hPosB
          (Or.inl hLocalInfXBot) (Or.inl hLocalInfXTop)
      exact le_trans hTargetLeProduct hProductLe

/-- Helper for Lemma33.0.5: at a fixed radius, local infima have a convex epigraph. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_convexFunction {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    ConvexFunction (fun x => ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  -- Route correction: prove the fixed-radius operator at finite real epigraph heights, so the
  -- argument never has to transport the mixed `(⊥, ⊤)` corner through `EReal.le_add_of_forall_gt`.
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
  have hBound :
      (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) ≤
        (((a * α + b * β : ℝ)) : EReal) := by
    -- Compare the target local infimum to any strict real upper bound, then extract endpoint
    -- witnesses from `iInf_lt_iff`.
    refine (EReal.le_of_forall_lt_iff_le
      (x := (((a * α + b * β : ℝ)) : EReal))
      (y := ⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1)).1 ?_
    intro z hz
    let η : ℝ := z - (a * α + b * β)
    have hzReal : a * α + b * β < z := by
      exact_mod_cast hz
    have hη : 0 < η := by
      exact sub_pos.mpr hzReal
    let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
    let wy : {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨y, by simpa using ε.2⟩
    letI : Nonempty {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨wx⟩
    letI : Nonempty {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨wy⟩
    have hXlt :
        (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) <
          (((α + η : ℝ)) : EReal) := by
      calc
        (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≤ (α : EReal) := hpHeight
        _ < (((α + η : ℝ)) : EReal) := by
          have hαη : α < α + η := by linarith
          exact_mod_cast hαη
    have hYlt :
        (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) <
          (((β + η : ℝ)) : EReal) := by
      calc
        (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) ≤ (β : EReal) := hqHeight
        _ < (((β + η : ℝ)) : EReal) := by
          have hβη : β < β + η := by linarith
          exact_mod_cast hβη
    rcases iInf_lt_iff.mp hXlt with ⟨w₁, hw₁lt⟩
    rcases iInf_lt_iff.mp hYlt with ⟨w₂, hw₂lt⟩
    have hBall :
        ‖(a • w₁.1 + b • w₂.1) - (a • x + b • y)‖ < ε.1 :=
      helperForLemma33_0_5_convexCombination_mem_ball w₁.2 w₂.2 ha hb hab
    let wCombo : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} :=
      ⟨a • w₁.1 + b • w₂.1, hBall⟩
    have hJensen :
        f (a • w₁.1 + b • w₂.1) ≤ (a : EReal) * f w₁.1 + (b : EReal) * f w₂.1 :=
      hConv (x := w₁.1) (y := w₂.1) (Set.mem_univ _) (Set.mem_univ _)
        ha hb hab (Set.mem_univ _)
    have hScaled :
        (a : EReal) * f w₁.1 + (b : EReal) * f w₂.1 ≤ (z : EReal) := by
      -- Move the strict endpoint bounds through the nonnegative weights and simplify the real
      -- upper bound back to `z`.
      have hUpperEq : a * (α + η) + b * (β + η) = z := by
        calc
          a * (α + η) + b * (β + η) = (a * α + b * β) + (a + b) * η := by ring
          _ = (a * α + b * β) + η := by rw [hab, one_mul]
          _ = z := by
            dsimp [η]
            ring
      calc
        (a : EReal) * f w₁.1 + (b : EReal) * f w₂.1 ≤
            (a : EReal) * (((α + η : ℝ)) : EReal) +
              (b : EReal) * (((β + η : ℝ)) : EReal) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hw₁lt.le hNonnegA)
            (mul_le_mul_of_nonneg_left hw₂lt.le hNonnegB)
        _ = (z : EReal) := by
          exact_mod_cast hUpperEq
    have hPoint :
        (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) ≤
          f wCombo.1 :=
      iInf_le (fun w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} => f w.1) wCombo
    exact le_trans hPoint (le_trans hJensen hScaled)
  -- Rewrite the target height back into the second coordinate of the convex combination in the
  -- epigraph.
  simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hBound

/-- Helper for Lemma33.0.5: at a fixed radius in the second variable, local infima preserve
concavity in the first variable. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_preserves_parameterConcavity
    {m n : ℕ} (ε : {r : ℝ // 0 < r}) (v : Fin n → ℝ)
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConc : ∀ w : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u w)) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
      (fun u => ⨅ w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}, K u w.1) := by
  intro x y hx hy a b ha hb hab hz
  -- Keep the same ball witness on both endpoints and apply sectionwise concavity.
  refine le_iInf ?_
  intro w
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hxLe : (⨅ q : {q : Fin n → ℝ // ‖q - v‖ < ε.1}, K x q.1) ≤ K x w.1 := iInf_le _ w
  have hyLe : (⨅ q : {q : Fin n → ℝ // ‖q - v‖ < ε.1}, K y q.1) ≤ K y w.1 := iInf_le _ w
  have hScaled :
      (a : EReal) * (⨅ q : {q : Fin n → ℝ // ‖q - v‖ < ε.1}, K x q.1) +
          (b : EReal) * (⨅ q : {q : Fin n → ℝ // ‖q - v‖ < ε.1}, K y q.1) ≤
        (a : EReal) * K x w.1 + (b : EReal) * K y w.1 := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hxLe hNonnegA)
      (mul_le_mul_of_nonneg_left hyLe hNonnegB)
  have hXMem : x ∈ (Set.univ : Set (Fin m → ℝ)) := Set.mem_univ x
  have hYMem : y ∈ (Set.univ : Set (Fin m → ℝ)) := Set.mem_univ y
  have hCombMem : a • x + b • y ∈ (Set.univ : Set (Fin m → ℝ)) := Set.mem_univ (a • x + b • y)
  have hJensen :
      (a : EReal) * K x w.1 + (b : EReal) * K y w.1 ≤ K (a • x + b • y) w.1 :=
    hConc w.1 (x := x) (y := y) hXMem hYMem ha hb hab hCombMem
  exact le_trans hScaled hJensen

/-- Helper for Lemma33.0.5: at a fixed radius in the first variable, local suprema preserve
convexity in the second variable. -/
lemma helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_parameterConvexity
    {m n : ℕ} (ε : {r : ℝ // 0 < r}) (u : Fin m → ℝ)
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConv : ∀ w : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun v => K w v)) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun v => ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 v) := by
  intro x y hx hy a b ha hb hab hz
  -- Keep the same ball witness on both endpoints and apply sectionwise convexity.
  refine iSup_le ?_
  intro w
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hXMem : x ∈ (Set.univ : Set (Fin n → ℝ)) := Set.mem_univ x
  have hYMem : y ∈ (Set.univ : Set (Fin n → ℝ)) := Set.mem_univ y
  have hCombMem : a • x + b • y ∈ (Set.univ : Set (Fin n → ℝ)) := Set.mem_univ (a • x + b • y)
  have hJensen :
      K w.1 (a • x + b • y) ≤ (a : EReal) * K w.1 x + (b : EReal) * K w.1 y :=
    hConv w.1 (x := x) (y := y) hXMem hYMem ha hb hab hCombMem
  have hxLe : K w.1 x ≤ ⨆ q : {q : Fin m → ℝ // ‖q - u‖ < ε.1}, K q.1 x :=
    le_iSup (fun q : {q : Fin m → ℝ // ‖q - u‖ < ε.1} => K q.1 x) w
  have hyLe : K w.1 y ≤ ⨆ q : {q : Fin m → ℝ // ‖q - u‖ < ε.1}, K q.1 y :=
    le_iSup (fun q : {q : Fin m → ℝ // ‖q - u‖ < ε.1} => K q.1 y) w
  have hScaled :
      (a : EReal) * K w.1 x + (b : EReal) * K w.1 y ≤
        (a : EReal) * (⨆ q : {q : Fin m → ℝ // ‖q - u‖ < ε.1}, K q.1 x) +
          (b : EReal) * (⨆ q : {q : Fin m → ℝ // ‖q - u‖ < ε.1}, K q.1 y) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hxLe hNonnegA)
      (mul_le_mul_of_nonneg_left hyLe hNonnegB)
  exact le_trans hJensen hScaled

/-- Helper for Lemma33.0.5: the one-variable concave closure obtained from local suprema remains
concave. -/
lemma helperForLemma33_0_5_functionConcaveClosure_preserves_concavity {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsERealConcaveOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ⨅ ε : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  intro x y hx hy a b ha hb hab hz
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  -- Compare the global infima to each fixed-radius section and then invoke the fixed-radius
  -- concavity statement at that common radius.
  refine le_iInf ?_
  intro ε
  have hxLe :
      (⨅ ε' : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, f w.1) ≤
        ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1 :=
    iInf_le _ ε
  have hyLe :
      (⨅ ε' : {r : ℝ // 0 < r},
        ⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε'.1}, f w.1) ≤
        ⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1 :=
    iInf_le _ ε
  have hScaled :
      (a : EReal) *
          (⨅ ε' : {r : ℝ // 0 < r},
            ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, f w.1) +
          (b : EReal) *
            (⨅ ε' : {r : ℝ // 0 < r},
              ⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε'.1}, f w.1) ≤
        (a : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) +
          (b : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hxLe hNonnegA)
      (mul_le_mul_of_nonneg_left hyLe hNonnegB)
  have hFixed :
      (a : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) +
          (b : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) ≤
        ⨆ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1 :=
    helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_concavity
      (ε := ε) hConc (x := x) (y := y) hx hy ha hb hab hz
  exact le_trans hScaled hFixed

/-- Helper for Lemma33.0.5: the one-variable convex closure obtained from local infima remains
convex. -/
lemma helperForLemma33_0_5_functionConvexClosure_convexFunction {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    ConvexFunction (fun x => ⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  -- Route correction: prove the outer `sup-inf` operator by epigraph convexity radius by radius,
  -- then take the supremum over radii.
  unfold ConvexFunction ConvexFunctionOn epigraph
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  rcases hp with ⟨hpUniv, hpHeight⟩
  rcases hq with ⟨hqUniv, hqHeight⟩
  constructor
  · show a • x + b • y ∈ (Set.univ : Set (Fin n → ℝ))
    simp
  let localInf :
      {r : ℝ // 0 < r} → (Fin n → ℝ) → EReal :=
    fun ε z => ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  have hBound :
      (⨆ ε : {r : ℝ // 0 < r}, localInf ε (a • x + b • y)) ≤
        (((a * α + b * β : ℝ)) : EReal) := by
    -- Each fixed-radius local infimum is bounded by the same convex-combination height, so the
    -- outer supremum is as well.
    refine iSup_le ?_
    intro ε
    have hpε : (x, α) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (localInf ε) := by
      refine ⟨?_, ?_⟩
      · show x ∈ (Set.univ : Set (Fin n → ℝ))
        simp
      exact le_trans (le_iSup (fun ε' : {r : ℝ // 0 < r} => localInf ε' x) ε) hpHeight
    have hqε : (y, β) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (localInf ε) := by
      refine ⟨?_, ?_⟩
      · show y ∈ (Set.univ : Set (Fin n → ℝ))
        simp
      exact le_trans (le_iSup (fun ε' : {r : ℝ // 0 < r} => localInf ε' y) ε) hqHeight
    have hFixedConv :
        ConvexFunction (localInf ε) :=
      helperForLemma33_0_5_fixedRadiusLocalInfimum_convexFunction (ε := ε) hConv
    unfold ConvexFunction ConvexFunctionOn epigraph at hFixedConv
    have hmem :
        a • (x, α) + b • (y, β) ∈
          epigraph (Set.univ : Set (Fin n → ℝ)) (localInf ε) :=
      hFixedConv hpε hqε ha hb hab
    simpa [localInf, smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hmem.2
  -- Rewrite the target height into the second coordinate of the epigraph point.
  simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hBound

/-- Helper for Lemma33.0.5: the raw `sup-inf` closure operator is idempotent. -/
lemma helperForLemma33_0_5_functionConvexClosure_raw_idempotent {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (x : Fin n → ℝ) :
    (⨆ δ : {r : ℝ // 0 < r},
      ⨅ z : {z : Fin n → ℝ // ‖z - x‖ < δ.1},
        (⨆ ε : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - z.1‖ < ε.1}, f w.1)) =
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  let rawClosure :
      (Fin n → ℝ) → EReal :=
    fun z =>
      ⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  apply le_antisymm
  · -- The second closure cannot exceed the first one because every radius-ball around `x`
    -- already contains the center point `x` itself.
    refine iSup_le ?_
    intro δ
    have hxMem : ‖x - x‖ < δ.1 := by
      simpa using δ.2
    exact iInf_le
      (fun z : {z : Fin n → ℝ // ‖z - x‖ < δ.1} => rawClosure z.1)
      ⟨x, hxMem⟩
  · -- For a fixed outer radius `ε`, shrink to `ε / 2`. Every point in the smaller `x`-ball
    -- has its own `ε / 2`-ball contained in the original `ε`-ball, so the first closure
    -- value is already attained after one more closure step.
    refine iSup_le ?_
    intro ε
    let δ : {r : ℝ // 0 < r} := ⟨ε.1 / 2, half_pos ε.2⟩
    have hDouble : δ.1 + δ.1 = ε.1 := by
      dsimp [δ]
      ring
    have hBallInclusion :
        ∀ {z w : Fin n → ℝ}, ‖z - x‖ < δ.1 → ‖w - z‖ < δ.1 → ‖w - x‖ < ε.1 := by
      intro z w hz hw
      calc
        ‖w - x‖ ≤ ‖w - z‖ + ‖z - x‖ := by
          simpa [dist_eq_norm, norm_sub_rev] using dist_triangle_right w x z
        _ < δ.1 + δ.1 := add_lt_add hw hz
        _ = ε.1 := hDouble
    have hLowerOnSmallBall :
        (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≤
          ⨅ z : {z : Fin n → ℝ // ‖z - x‖ < δ.1}, rawClosure z.1 := by
      refine le_iInf ?_
      intro z
      have hLowerAtZ :
          (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≤
            ⨅ w : {w : Fin n → ℝ // ‖w - z.1‖ < δ.1}, f w.1 := by
        -- The smaller `z`-ball sits inside the original `x`-ball.
        refine le_iInf ?_
        intro w
        exact iInf_le
          (fun q : {q : Fin n → ℝ // ‖q - x‖ < ε.1} => f q.1)
          ⟨w.1, hBallInclusion z.2 w.2⟩
      have hChooseSameRadius :
          (⨅ w : {w : Fin n → ℝ // ‖w - z.1‖ < δ.1}, f w.1) ≤ rawClosure z.1 := by
        exact le_iSup
          (fun η : {r : ℝ // 0 < r} =>
            ⨅ w : {w : Fin n → ℝ // ‖w - z.1‖ < η.1}, f w.1)
          δ
      exact le_trans hLowerAtZ hChooseSameRadius
    exact le_trans hLowerOnSmallBall
      (le_iSup
        (fun ρ : {r : ℝ // 0 < r} =>
          ⨅ z : {z : Fin n → ℝ // ‖z - x‖ < ρ.1}, rawClosure z.1)
        δ)

/-- Helper for Lemma33.0.5: the raw `sup-inf` closure operator is lower semicontinuous. -/
lemma helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous {n : ℕ}
    {f : (Fin n → ℝ) → EReal} :
    LowerSemicontinuous (fun x => ⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  -- Open superlevel sets are witnessed by a single radius. Nearby centers keep a smaller ball
  -- inside that witness ball, so the same strict lower bound persists locally.
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro α
  refine Metric.isOpen_iff.2 ?_
  intro x hx
  let ε₀ : {r : ℝ // 0 < r} := ⟨1, by norm_num⟩
  letI : Nonempty {r : ℝ // 0 < r} := ⟨ε₀⟩
  have hx' :
      α < (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
    simpa [Set.preimage, Set.mem_Ioi] using hx
  rcases lt_iSup_iff.mp hx' with ⟨ε, hε⟩
  let δ : ℝ := ε.1 / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact half_pos ε.2
  have hDouble : δ + δ = ε.1 := by
    dsimp [δ]
    ring
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  let η : {r : ℝ // 0 < r} := ⟨δ, hδ⟩
  let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
  let wy : {w : Fin n → ℝ // ‖w - y‖ < η.1} := ⟨y, by simpa [η] using η.2⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨wx⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - y‖ < η.1} := ⟨wy⟩
  rcases lt_iInf_iff.mp hε with ⟨β, hβα, hβBound⟩
  have hPointwiseX :
      ∀ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, β ≤ f w.1 := by
    -- The chosen radius gives a uniform lower bound on every point in its ball.
    exact hβBound
  have hBallInclusion :
      ∀ {w : Fin n → ℝ}, ‖w - y‖ < η.1 → ‖w - x‖ < ε.1 := by
    intro w hw
    have hyx : ‖y - x‖ < η.1 := by
      simpa [Metric.mem_ball, dist_eq_norm, η] using hy
    calc
      ‖w - x‖ ≤ ‖w - y‖ + ‖y - x‖ := by
        simpa [dist_eq_norm, norm_sub_rev] using dist_triangle_right w x y
      _ < η.1 + η.1 := add_lt_add hw hyx
      _ = ε.1 := by
        simpa [η] using hDouble
  have hLocalY :
      α < ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < η.1}, f w.1 := by
    -- Every point in the smaller `y`-ball lies in the original `x`-ball, so the same strict
    -- lower bound transfers to the new local infimum.
    refine lt_iInf_iff.mpr ?_
    refine ⟨β, hβα, ?_⟩
    intro w
    exact hPointwiseX ⟨w.1, hBallInclusion w.2⟩
  have hAtY :
      α < (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) := by
    exact lt_of_lt_of_le hLocalY
      (le_iSup
        (fun ε : {r : ℝ // 0 < r} =>
          ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1)
        η)
  simpa [Set.preimage, Set.mem_Ioi] using hAtY

/-- Helper for Lemma33.0.5: the raw `sup-inf` closure never exceeds the original function,
because every ball contains its own center. -/
lemma helperForLemma33_0_5_functionConvexClosure_raw_le_self {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (x : Fin n → ℝ) :
    (⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≤ f x := by
  -- At every radius, the center point itself contributes to the local infimum.
  refine iSup_le ?_
  intro ε
  let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
  exact iInf_le (fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => f w.1) wx

/-- Helper for Lemma33.0.5: if the raw `sup-inf` closure takes the value `⊤` at some point and
all of its values are already classified into `{⊤, ⊥}`, then a whole neighborhood is forced to
stay at `⊤`. -/
lemma helperForLemma33_0_5_functionConvexClosure_top_has_topNeighborhood {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {y : Fin n → ℝ}
    (hTopOrBot :
      ∀ x,
        (⨆ ε : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = (⊤ : EReal) ∨
          (⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = (⊥ : EReal))
    (hyTop :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = (⊤ : EReal)) :
    ∃ δ : {r : ℝ // 0 < r},
      ∀ z : {z : Fin n → ℝ // ‖z - y‖ < δ.1},
        (⨆ ε : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - z.1‖ < ε.1}, f w.1) = (⊤ : EReal) := by
  let g : (Fin n → ℝ) → EReal :=
    fun x =>
      ⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1
  have hSupEq :
      (⨆ δ : {r : ℝ // 0 < r},
        ⨅ z : {z : Fin n → ℝ // ‖z - y‖ < δ.1}, g z.1) = g y := by
    -- Apply raw idempotence once more, now to the already-closed function `g`.
    simpa [g] using helperForLemma33_0_5_functionConvexClosure_raw_idempotent (f := f) y
  have hSupTop :
      (⊥ : EReal) <
        (⨆ δ : {r : ℝ // 0 < r},
          ⨅ z : {z : Fin n → ℝ // ‖z - y‖ < δ.1}, g z.1) := by
    rw [hSupEq]
    simpa [g, hyTop]
  rcases lt_iSup_iff.mp hSupTop with ⟨δ, hδ⟩
  refine ⟨δ, ?_⟩
  intro z
  have hzNotBot : g z.1 ≠ (⊥ : EReal) := by
    intro hzBot
    have hInfLe :
        (⨅ q : {q : Fin n → ℝ // ‖q - y‖ < δ.1}, g q.1) ≤ g z.1 :=
      iInf_le (fun q : {q : Fin n → ℝ // ‖q - y‖ < δ.1} => g q.1) z
    have hBotLtBot : (⊥ : EReal) < (⊥ : EReal) := by
      exact lt_of_lt_of_le hδ (by simpa [hzBot] using hInfLe)
    exact (lt_irrefl (⊥ : EReal)) hBotLtBot
  rcases hTopOrBot z.1 with hzTop | hzBot
  · simpa [g] using hzTop
  · exact False.elim (hzNotBot (by simpa [g] using hzBot))

/-- Helper for Lemma33.0.5: a lower semicontinuous convex function on `univ` that already
attains `⊥` is improper, so Chapter 2 forces all of its values to lie in `{⊤, ⊥}`. -/
lemma helperForLemma33_0_5_closedImproperConvex_values_top_or_bot {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hConv : ConvexFunction g) (hLsc : LowerSemicontinuous g)
    (hBot : ∃ x, g x = ⊥) :
    ∀ x, g x = (⊤ : EReal) ∨ g x = (⊥ : EReal) := by
  have hImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    refine ⟨?_, ?_⟩
    · -- The epigraph convexity is exactly the ambient `ConvexFunction` hypothesis.
      simpa [ConvexFunction] using hConv
    · intro hProper
      rcases hBot with ⟨x, hx⟩
      exact hProper.2.2 x (by simp) hx
  -- Apply the Chapter 2 improper-closed classification directly to `g`.
  exact lowerSemicontinuous_improperConvexFunction_no_finite_values
    (f := g) hImproper hLsc

/-- Helper for Lemma33.0.5: once a `{⊤, ⊥}`-valued raw closure equals `⊥` at `x`, every
positive-radius ball around `x` already contains an exact `⊥` witness. -/
lemma helperForLemma33_0_5_topBotValued_rawClosure_eq_bot_implies_everyBall_has_botWitness
    {n : ℕ} {g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    (hTopOrBot : ∀ z, g z = (⊤ : EReal) ∨ g z = (⊥ : EReal))
    (hRawIdem :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1) = g x)
    (hxBot : g x = (⊥ : EReal)) :
    ∀ ε : {r : ℝ // 0 < r},
      ∃ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1 = (⊥ : EReal) := by
  intro ε
  by_contra hNoBot
  have hAllTop :
      ∀ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1 = (⊤ : EReal) := by
    intro w
    rcases hTopOrBot w.1 with hwTop | hwBot
    · exact hwTop
    · exact False.elim (hNoBot ⟨w, hwBot⟩)
  have hInfTop :
      (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1) = (⊤ : EReal) := by
    apply le_antisymm le_top
    refine le_iInf ?_
    intro w
    simpa [hAllTop w]
  have hSupTop :
      (⊤ : EReal) ≤
        ⨆ ε' : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, g w.1 := by
    -- If one local infimum were already `⊤`, the outer supremum would be forced to be `⊤`.
    have hLe :
        (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1) ≤
          ⨆ ε' : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, g w.1 :=
      le_iSup
        (fun ε' : {r : ℝ // 0 < r} =>
          ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, g w.1)
        ε
    simpa [hInfTop] using hLe
  have hxTop : g x = (⊤ : EReal) := by
    -- Compare the `⊤` lower bound on the supremum with the idempotence identity at `x`.
    exact top_le_iff.mp (by simpa [hRawIdem] using hSupTop)
  exact (by simp : (⊤ : EReal) ≠ (⊥ : EReal)) (hxTop.symm.trans hxBot)

/-- Helper for Lemma33.0.5: a strict convex combination of an exact `⊥` witness at the `x`
endpoint and the `⊤` endpoint value at `y` cannot land inside a neighborhood where the target
function is identically `⊤`. -/
lemma helperForLemma33_0_5_topNeighborhood_contradicts_botWitnessUnderConvexity {n : ℕ}
    {g : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) g)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a)
    {δ : {r : ℝ // 0 < r}}
    (hTopNeighborhood :
      ∀ z : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < δ.1}, g z.1 = ⊤)
    {w : Fin n → ℝ} (hw : ‖w - x‖ < δ.1)
    (hwBot : g w = ⊥) (hyTop : g y = ⊤) :
    False := by
  -- Move the exact `⊥` witness from the `x`-ball to the target neighborhood using the same
  -- convex combination as in Jensen's inequality.
  have hBall :
      ‖(a • w + b • y) - (a • x + b • y)‖ < δ.1 := by
    simpa using
      helperForLemma33_0_5_convexCombination_mem_ball
        (x := x) (y := y) (w₁ := w) (w₂ := y) (r := δ.1)
        hw (by simpa using δ.2) ha hb hab
  let zCombo : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < δ.1} :=
    ⟨a • w + b • y, hBall⟩
  have hComboTop : g zCombo.1 = ⊤ := hTopNeighborhood zCombo
  have hJensen :
      g (a • w + b • y) ≤ (a : EReal) * g w + (b : EReal) * g y :=
    hConv (x := w) (y := y) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  have hComboBot : g zCombo.1 = ⊥ := by
    -- The exact `⊥` witness on the left endpoint collapses the weighted upper bound to `⊥`.
    have hLeBot : g zCombo.1 ≤ (⊥ : EReal) := by
      calc
        g zCombo.1 ≤ (a : EReal) * g w + (b : EReal) * g y := by
          simpa [zCombo] using hJensen
        _ = ⊥ := by
          simp [hwBot, hyTop, EReal.coe_mul_bot_of_pos hPosA]
    exact le_bot_iff.mp hLeBot
  have hTopEqBot : (⊤ : EReal) = ⊥ := hComboTop.symm.trans hComboBot
  simp at hTopEqBot

/-- Helper for Lemma33.0.5: once the raw `sup-inf` closure is already known to satisfy Jensen,
the mixed `(⊥, ⊤)` branch collapses by combining top neighborhoods at `⊤` points with exact
`⊥` witnesses in every ball around a `⊥` point. -/
lemma helperForLemma33_0_5_functionConvexClosure_mixedBotTop_collapse_from_rawClassification
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ} {a b : ℝ}
    (hClosureConv :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
        (fun z =>
          ⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (_hPosB : 0 < b)
    (hClosureXBot :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥)
    (hClosureYTop :
      (⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊤) :
    (⨆ ε : {r : ℝ // 0 < r},
      ⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) = ⊥ := by
  let g : (Fin n → ℝ) → EReal :=
    fun z =>
      ⨆ ε : {r : ℝ // 0 < r},
        ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1
  have hConvFun : ConvexFunction g :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hClosureConv
  have hTopOrBot : ∀ z, g z = (⊤ : EReal) ∨ g z = (⊥ : EReal) := by
    -- Closed improper convex functions are already classified into `{⊤, ⊥}`.
    refine helperForLemma33_0_5_closedImproperConvex_values_top_or_bot
      (g := g) hConvFun
      (by simpa [g] using helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f))
      ?_
    exact ⟨x, by simpa [g] using hClosureXBot⟩
  have hEveryBallHasBotWitness :
      ∀ ε : {r : ℝ // 0 < r},
        ∃ w : Fin n → ℝ, ‖w - x‖ < ε.1 ∧ g w = (⊥ : EReal) := by
    have hRawIdemG :
        (⨆ ε : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, g w.1) = g x := by
      simpa [g] using helperForLemma33_0_5_functionConvexClosure_raw_idempotent (f := f) x
    intro ε
    rcases
        helperForLemma33_0_5_topBotValued_rawClosure_eq_bot_implies_everyBall_has_botWitness
          (g := g) (x := x) hTopOrBot hRawIdemG
          (by simpa [g] using hClosureXBot) ε with
      ⟨w, hwBot⟩
    exact ⟨w.1, w.2, hwBot⟩
  have hTargetNotTop : g (a • x + b • y) ≠ (⊤ : EReal) := by
    intro hTargetTop
    rcases
        helperForLemma33_0_5_functionConvexClosure_top_has_topNeighborhood
          (f := f) (y := a • x + b • y)
          hTopOrBot (by simpa [g] using hTargetTop) with
      ⟨δ, hδTop⟩
    rcases hEveryBallHasBotWitness δ with ⟨w, hwBall, hwBot⟩
    exact
      helperForLemma33_0_5_topNeighborhood_contradicts_botWitnessUnderConvexity
        (hConv := hClosureConv) ha hb hab hPosA hδTop hwBall hwBot
        (by simpa [g] using hClosureYTop)
  -- The top/bottom classification at the target point leaves `⊥` as the only possibility.
  rcases hTopOrBot (a • x + b • y) with hTargetTop | hTargetBot
  · exact False.elim (hTargetNotTop hTargetTop)
  · simpa [g] using hTargetBot

/-- Helper for Lemma33.0.5: for a convex epigraph, an exact `⊥` left endpoint and any
right endpoint different from `⊤` already force every strict convex combination to be `⊥`. -/
lemma helperForLemma33_0_5_convexFunction_leftBot_rightNotTop_forces_comboBot {n : ℕ}
    {g : (Fin n → ℝ) → EReal} {x y : Fin n → ℝ} {a b : ℝ}
    (hConvFun : ConvexFunction g)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hxBot : g x = ⊥) (hyNeTop : g y ≠ ⊤) :
    g (a • x + b • y) = ⊥ := by
  -- Compare the target value with an arbitrary real upper bound and use the `⊥` endpoint to
  -- drive the left epigraph height arbitrarily low.
  unfold ConvexFunction ConvexFunctionOn epigraph at hConvFun
  by_contra hTargetNeBot
  rcases exists_real_not_le_of_ne_bot (x := g (a • x + b • y)) hTargetNeBot with ⟨γ, hγ⟩
  let β : ℝ := (g y).toReal
  have hgyLe : g y ≤ (β : EReal) := by
    exact EReal.le_coe_toReal hyNeTop
  let α : ℝ := (γ - b * β) / a
  have hAlphaHeight :
      (((a * α + b * β : ℝ)) : EReal) = (γ : EReal) := by
    have hEq : a * α + b * β = γ := by
      calc
        a * α + b * β = a * ((γ - b * β) / a) + b * β := by simp [α]
        _ = γ - b * β + b * β := by
          field_simp [hPosA.ne']
        _ = γ := by ring
    exact_mod_cast hEq
  have hxMem : (x, α) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) g := by
    refine ⟨?_, ?_⟩
    · show x ∈ (Set.univ : Set (Fin n → ℝ))
      exact Set.mem_univ x
    simpa [hxBot]
  have hyMem : (y, β) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) g := by
    refine ⟨?_, hgyLe⟩
    · show y ∈ (Set.univ : Set (Fin n → ℝ))
      exact Set.mem_univ y
  have hComboMem :
      a • (x, α) + b • (y, β) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) g :=
    hConvFun hxMem hyMem ha hb hab
  have hTargetLeGamma : g (a • x + b • y) ≤ (γ : EReal) := by
    simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul, hAlphaHeight] using hComboMem.2
  exact hγ hTargetLeGamma


end Section33
end Chap07
