/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part13

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-- Helper for Text 34.1.6: a nonnegative weighted sum of two `EReal` values strictly above `⊥`
is still strictly above `⊥`. -/
lemma helperForText_34_1_6_weightedSum_gt_bot
    {x y : EReal} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hab : a + b = 1)
    (hx : (⊥ : EReal) < x) (hy : (⊥ : EReal) < y) :
    (⊥ : EReal) < (a : EReal) * x + (b : EReal) * y := by
  -- Each nonnegative weighted term avoids `⊥`, so their sum avoids `⊥` as well.
  have hx_ne_bot : x ≠ (⊥ : EReal) := (bot_lt_iff_ne_bot.mp hx)
  have hy_ne_bot : y ≠ (⊥ : EReal) := (bot_lt_iff_ne_bot.mp hy)
  have ha_ereal_nonneg : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hb_ereal_nonneg : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hax_ne_bot : (a : EReal) * x ≠ (⊥ : EReal) := by
    rw [EReal.mul_ne_bot]
    refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inr hx_ne_bot, Or.inl (EReal.coe_ne_top a),
      Or.inl ha_ereal_nonneg⟩
  have hby_ne_bot : (b : EReal) * y ≠ (⊥ : EReal) := by
    rw [EReal.mul_ne_bot]
    refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inr hy_ne_bot, Or.inl (EReal.coe_ne_top b),
      Or.inl hb_ereal_nonneg⟩
  exact bot_lt_iff_ne_bot.mpr ((EReal.add_ne_bot_iff).2 ⟨hax_ne_bot, hby_ne_bot⟩)

/-- Helper for Text 34.1.6: a nonnegative weighted sum of two `EReal` values strictly below `⊤`
is still strictly below `⊤`. -/
lemma helperForText_34_1_6_weightedSum_lt_top
    {x y : EReal} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hab : a + b = 1)
    (hx : x < (⊤ : EReal)) (hy : y < (⊤ : EReal)) :
    (a : EReal) * x + (b : EReal) * y < (⊤ : EReal) := by
  -- Each nonnegative weighted term avoids `⊤`, and then `EReal.add_lt_top` finishes.
  have hx_ne_top : x ≠ (⊤ : EReal) := (lt_top_iff_ne_top.mp hx)
  have hy_ne_top : y ≠ (⊤ : EReal) := (lt_top_iff_ne_top.mp hy)
  have hax_ne_top : (a : EReal) * x ≠ (⊤ : EReal) := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), Or.inr hx_ne_top⟩
    exact_mod_cast ha
  have hby_ne_top : (b : EReal) * y ≠ (⊤ : EReal) := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), Or.inr hy_ne_top⟩
    exact_mod_cast hb
  exact EReal.add_lt_top hax_ne_top hby_ne_top

-- Route correction: rewrite each coordinate effective domain as an intersection of one-variable
-- slice domains, so the convexity proof only needs one generic slice argument in each variable.
/-- Helper for Text 34.1.6: the effective domain of a globally concave `EReal` slice is
convex. -/
lemma helperForText_34_1_6_concaveSlice_effectiveDomain_convex
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) f) :
    Convex ℝ (concaveFunctionEffectiveDomain f) := by
  intro x hx y hy a b ha hb hab
  -- Unfold the endpoint hypotheses into strict lower bounds for the slice values.
  have hx_gt : (⊥ : EReal) < f x := by
    simpa [concaveFunctionEffectiveDomain] using hx
  have hy_gt : (⊥ : EReal) < f y := by
    simpa [concaveFunctionEffectiveDomain] using hy
  have hx_univ : x ∈ (Set.univ : Set (Fin k → ℝ)) := by
    simp
  have hy_univ : y ∈ (Set.univ : Set (Fin k → ℝ)) := by
    simp
  have hxy_univ : a • x + b • y ∈ (Set.univ : Set (Fin k → ℝ)) := by
    simp
  -- Jensen moves the midpoint value above the weighted endpoint sum.
  have hJensen :
      (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y) :=
    hConc hx_univ hy_univ ha hb hab hxy_univ
  -- The weighted endpoint sum still avoids `⊥`, so the midpoint does as well.
  have hWeighted :
      (⊥ : EReal) < (a : EReal) * f x + (b : EReal) * f y :=
    helperForText_34_1_6_weightedSum_gt_bot ha hb hab hx_gt hy_gt
  simpa [concaveFunctionEffectiveDomain] using lt_of_lt_of_le hWeighted hJensen

/-- Helper for Text 34.1.6: the first effective domain is the intersection of the concave slice
domains `dom (u ↦ K u v)`. -/
lemma helperForText_34_1_6_effectiveDomain1_eq_iInter_concaveSlices
    (K : SaddleFunction m n) :
    effectiveDomain₁ K = ⋂ v : Fin n → ℝ, concaveFunctionEffectiveDomain (fun u => K u v) := by
  -- Unfold the universal quantifier in `dom₁ K` into indexed intersection membership.
  ext u
  simp [effectiveDomain₁, concaveFunctionEffectiveDomain]

/-- Helper for Text 34.1.6: the second effective domain is the intersection of the convex slice
domains `dom (v ↦ K u v)`. -/
lemma helperForText_34_1_6_effectiveDomain2_eq_iInter_convexSlices
    (K : SaddleFunction m n) :
    effectiveDomain₂ K = ⋂ u : Fin m → ℝ, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) := by
  -- Unfold the universal quantifier in `dom₂ K` into indexed intersection membership.
  ext v
  simp [effectiveDomain₂, effectiveDomain_eq]

/-- Helper for Text 34.1.6: fixing the second variable yields a convex first-variable slice
domain. -/
lemma helperForText_34_1_6_convex_concaveSlice_for_fixedSecond
    (K : SaddleFunction m n) (h : IsConcaveConvex K) (v : Fin n → ℝ) :
    Convex ℝ (concaveFunctionEffectiveDomain (fun u => K u v)) := by
  -- Specialize the saddle concavity hypothesis to the chosen second-variable slice.
  have hv_univ : v ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  exact
    helperForText_34_1_6_concaveSlice_effectiveDomain_convex
      (hConc := h.1 v hv_univ)

/-- Helper for Text 34.1.6: fixing the first variable yields a convex second-variable slice
domain. -/
lemma helperForText_34_1_6_convex_effectiveDomainSlice_for_fixedFirst
    (K : SaddleFunction m n) (h : IsConcaveConvex K) (u : Fin m → ℝ) :
    Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)) := by
  -- Convert the fixed-`u` convex slice into the Chapter 1 convex-function API.
  have hu_univ : u ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hSliceConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (K u) := h.2 u hu_univ
  have hSliceConvFun : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) := by
    -- Repackage the Jensen inequality as the convex-epigraph formulation used earlier.
    simpa [ConvexFunction] using
      (helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
        (f := K u) hSliceConv)
  exact effectiveDomain_convex hSliceConvFun

/-- Helper for Text 34.1.6: every point of `dom₁ K × dom₂ K` is a finite-valued point of `K`. -/
lemma helperForText_34_1_6_domainPoint_isFinite
    (K : SaddleFunction m n) {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ effectiveDomain₁ K) (hv : v ∈ effectiveDomain₂ K) :
    K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := by
  -- The first-domain condition excludes `⊥`, while the second-domain condition excludes `⊤`.
  constructor
  · exact lt_top_iff_ne_top.mp (hv u)
  · exact bot_lt_iff_ne_bot.mp (hu v)

/-- Helper for Text 34.1.6: membership in the saddle effective domain is exactly coordinatewise
membership in the two effective domains. -/
lemma helperForText_34_1_6_mem_saddleEffectiveDomain_iff
    (K : SaddleFunction m n) {p : (Fin m → ℝ) × (Fin n → ℝ)} :
    p ∈ saddleEffectiveDomain K ↔ p.1 ∈ effectiveDomain₁ K ∧ p.2 ∈ effectiveDomain₂ K := by
  -- Expand the product-domain definition into separate coordinate conditions.
  simp [saddleEffectiveDomain]

/-- Helper for Text 34.1.6: every point of `dom K` lies in the finiteness domain of `K`. -/
lemma helperForText_34_1_6_mem_finitenessDomain_of_mem_saddleEffectiveDomain
    (K : SaddleFunction m n) {p : (Fin m → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ saddleEffectiveDomain K) :
    p ∈ finitenessDomain K := by
  -- Unpack the product-domain hypothesis into coordinatewise effective-domain membership.
  have hp' : p.1 ∈ effectiveDomain₁ K ∧ p.2 ∈ effectiveDomain₂ K := by
    exact (helperForText_34_1_6_mem_saddleEffectiveDomain_iff (K := K)).mp hp
  -- Convert the coordinatewise domain facts into finiteness of the saddle value.
  simpa [finitenessDomain] using
    helperForText_34_1_6_domainPoint_isFinite (K := K) hp'.1 hp'.2

/-- Helper for Text 34.1.6: the saddle effective domain is convex once the two coordinate
effective domains are convex. -/
lemma helperForText_34_1_6_convex_saddleEffectiveDomain
    (K : SaddleFunction m n)
    (hDom1 : Convex ℝ (effectiveDomain₁ K))
    (hDom2 : Convex ℝ (effectiveDomain₂ K)) :
    Convex ℝ (saddleEffectiveDomain K) := by
  -- Expand `dom K` as a product of the two coordinatewise effective domains.
  simpa [saddleEffectiveDomain] using hDom1.prod hDom2

/-- Helper for Text 34.1.6: the concavity side of a saddle-function gives Jensen's inequality
on each fixed-second-variable slice. -/
lemma helperForText_34_1_6_concaveSlice_jensen
    (K : SaddleFunction m n) (h : IsConcaveConvex K) (v : Fin n → ℝ)
    {u₁ u₂ : Fin m → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * K u₁ v + (b : EReal) * K u₂ v ≤ K (a • u₁ + b • u₂) v := by
  -- Put the slice parameter and all first-variable points into the ambient set `univ`.
  have hv_univ : v ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hu₁_univ : u₁ ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hu₂_univ : u₂ ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hcomb_univ : a • u₁ + b • u₂ ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  -- Now specialize the concavity-in-`u` hypothesis to this slice and these three points.
  have hSliceConc : IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u v) :=
    h.1 v hv_univ
  exact hSliceConc hu₁_univ hu₂_univ ha hb hab hcomb_univ

/-- Helper for Text 34.1.6: the convexity side of a saddle-function gives Jensen's inequality
on each fixed-first-variable slice. -/
lemma helperForText_34_1_6_convexSlice_jensen
    (K : SaddleFunction m n) (h : IsConcaveConvex K) (u : Fin m → ℝ)
    {v₁ v₂ : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    K u (a • v₁ + b • v₂) ≤ (a : EReal) * K u v₁ + (b : EReal) * K u v₂ := by
  -- Put the slice parameter and all second-variable points into the ambient set `univ`.
  have hu_univ : u ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hv₁_univ : v₁ ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hv₂_univ : v₂ ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hcomb_univ : a • v₁ + b • v₂ ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  -- Now specialize the convexity-in-`v` hypothesis to this slice and these three points.
  have hSliceConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (K u) :=
    h.2 u hu_univ
  exact hSliceConv hv₁_univ hv₂_univ ha hb hab hcomb_univ

/-- Helper for Text 34.1.6: convex combinations of points in `dom₁ K` stay in `dom₁ K`. -/
lemma helperForText_34_1_6_mem_effectiveDomain1_of_convexCombination
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {u₁ u₂ : Fin m → ℝ} (hu₁ : u₁ ∈ effectiveDomain₁ K) (hu₂ : u₂ ∈ effectiveDomain₁ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • u₁ + b • u₂ ∈ effectiveDomain₁ K := by
  -- Unfold `dom₁ K` and freeze the second variable.
  rw [effectiveDomain₁] at hu₁ hu₂ ⊢
  intro v
  -- Apply the fixed-slice Jensen inequality on the concave first-variable section `u ↦ K u v`.
  have hJensen :
      (a : EReal) * K u₁ v + (b : EReal) * K u₂ v ≤ K (a • u₁ + b • u₂) v :=
    helperForText_34_1_6_concaveSlice_jensen (K := K) h v ha hb hab
  -- The weighted endpoint values stay above `⊥`, so the midpoint value does as well.
  have hWeighted :
      (⊥ : EReal) < (a : EReal) * K u₁ v + (b : EReal) * K u₂ v :=
    helperForText_34_1_6_weightedSum_gt_bot ha hb hab (hu₁ v) (hu₂ v)
  exact lt_of_lt_of_le hWeighted hJensen

/-- Helper for Text 34.1.6: convex combinations of points in `dom₂ K` stay in `dom₂ K`. -/
lemma helperForText_34_1_6_mem_effectiveDomain2_of_convexCombination
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {v₁ v₂ : Fin n → ℝ} (hv₁ : v₁ ∈ effectiveDomain₂ K) (hv₂ : v₂ ∈ effectiveDomain₂ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • v₁ + b • v₂ ∈ effectiveDomain₂ K := by
  -- Unfold `dom₂ K` and freeze the first variable.
  rw [effectiveDomain₂] at hv₁ hv₂ ⊢
  intro u
  -- Apply the fixed-slice Jensen inequality on the convex second-variable section `v ↦ K u v`.
  have hJensen :
      K u (a • v₁ + b • v₂) ≤ (a : EReal) * K u v₁ + (b : EReal) * K u v₂ :=
    helperForText_34_1_6_convexSlice_jensen (K := K) h u ha hb hab
  -- The weighted endpoint values stay below `⊤`, so the midpoint value does as well.
  have hWeighted :
      (a : EReal) * K u v₁ + (b : EReal) * K u v₂ < (⊤ : EReal) :=
    helperForText_34_1_6_weightedSum_lt_top ha hb hab (hv₁ u) (hv₂ u)
  exact lt_of_le_of_lt hJensen hWeighted

/-- Helper for Text 34.1.6: convex combinations of points in `dom K` stay in `dom K`. -/
lemma helperForText_34_1_6_mem_saddleEffectiveDomain_of_convexCombination
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {p₁ p₂ : (Fin m → ℝ) × (Fin n → ℝ)}
    (hp₁ : p₁ ∈ saddleEffectiveDomain K) (hp₂ : p₂ ∈ saddleEffectiveDomain K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p₁ + b • p₂ ∈ saddleEffectiveDomain K := by
  -- Unpack the two product-domain hypotheses into coordinatewise effective-domain membership.
  rcases (helperForText_34_1_6_mem_saddleEffectiveDomain_iff (K := K)).mp hp₁ with ⟨hu₁, hv₁⟩
  rcases (helperForText_34_1_6_mem_saddleEffectiveDomain_iff (K := K)).mp hp₂ with ⟨hu₂, hv₂⟩
  -- Repack the coordinatewise convex-combination closure facts into the product domain.
  refine (helperForText_34_1_6_mem_saddleEffectiveDomain_iff (K := K)).2 ?_
  constructor
  · simpa using
      helperForText_34_1_6_mem_effectiveDomain1_of_convexCombination
        (K := K) h hu₁ hu₂ ha hb hab
  · simpa using
      helperForText_34_1_6_mem_effectiveDomain2_of_convexCombination
        (K := K) h hv₁ hv₂ ha hb hab

/-- Helper for Text 34.1.6: the first effective domain is convex for a concave-convex saddle
function. -/
lemma helperForText_34_1_6_convex_effectiveDomain1
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    Convex ℝ (effectiveDomain₁ K) := by
  -- Route correction: rewrite `dom₁ K` as an intersection of concave slice domains and apply
  -- the generic concave-slice convexity lemma slice by slice.
  rw [helperForText_34_1_6_effectiveDomain1_eq_iInter_concaveSlices]
  refine convex_iInter ?_
  intro v
  -- Each fixed-`v` slice is convex by the concavity-in-`u` half of the saddle hypothesis.
  exact helperForText_34_1_6_convex_concaveSlice_for_fixedSecond (K := K) h v

/-- Helper for Text 34.1.6: the second effective domain is convex for a concave-convex saddle
function. -/
lemma helperForText_34_1_6_convex_effectiveDomain2
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    Convex ℝ (effectiveDomain₂ K) := by
  -- Rewrite `dom₂ K` as an intersection of ordinary convex effective domains.
  rw [helperForText_34_1_6_effectiveDomain2_eq_iInter_convexSlices]
  refine convex_iInter ?_
  intro u
  -- Each fixed-`u` slice is convex by the convexity-in-`v` half of the saddle hypothesis.
  exact helperForText_34_1_6_convex_effectiveDomainSlice_for_fixedFirst (K := K) h u

-- Proof sketch: use the concavity in the first variable and convexity in the second variable to
-- show each coordinate effective domain is convex, then combine those two closure results to
-- close the full saddle effective domain under convex combinations and finally unpack the
-- definitions of `saddleEffectiveDomain` and `finitenessDomain`.
/-- Text 34.1.6: if `K` is concave-convex on `ℝ^m × ℝ^n`, then `dom₁ K` is convex in `ℝ^m`
and `dom₂ K` is convex in `ℝ^n`; consequently `dom K` is convex in `ℝ^m × ℝ^n`, and `K` is
finite at every point of `dom K`. -/
theorem section34_text_34_1_6 (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    Convex ℝ (effectiveDomain₁ K) ∧
      Convex ℝ (effectiveDomain₂ K) ∧
      Convex ℝ (saddleEffectiveDomain K) ∧
      saddleEffectiveDomain K ⊆ finitenessDomain K := by
  -- Package the two coordinatewise convexity arguments into reusable helper lemmas.
  have hDom1 : Convex ℝ (effectiveDomain₁ K) :=
    helperForText_34_1_6_convex_effectiveDomain1 (K := K) h
  have hDom2 : Convex ℝ (effectiveDomain₂ K) :=
    helperForText_34_1_6_convex_effectiveDomain2 (K := K) h
  -- The full saddle domain is the product of the two coordinatewise convex domains.
  have hSaddle : Convex ℝ (saddleEffectiveDomain K) :=
    helperForText_34_1_6_convex_saddleEffectiveDomain (K := K) hDom1 hDom2
  -- Every point of the product domain is finite by the two defining inequalities.
  have hFinite : saddleEffectiveDomain K ⊆ finitenessDomain K := by
    intro p hp
    -- Reuse the dedicated finiteness helper for points of the saddle effective domain.
    exact helperForText_34_1_6_mem_finitenessDomain_of_mem_saddleEffectiveDomain (K := K) hp
  exact ⟨hDom1, hDom2, hSaddle, hFinite⟩

/-- Helper for Text 34.1.7: the `v`-section of the open-unit-square power upper simple
extension at `u = 1 / 2` fails concavity on all of `ℝ`, because two off-domain points have an
in-domain midpoint. -/
lemma helperForText_34_1_7_secondSection_not_concave_at_half :
    ¬ IsERealConcaveOn (Set.univ : Set (Fin 1 → ℝ))
      (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) := by
  intro hConc
  let x : Fin 1 → ℝ := fun _ => (-1 / 4 : ℝ)
  let y : Fin 1 → ℝ := fun _ => (7 / 4 : ℝ)
  let a : ℝ := 1 / 2
  let b : ℝ := 1 / 2
  have hx : x ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have hy : y ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have ha : 0 ≤ a := by
    norm_num [a]
  have hb : 0 ≤ b := by
    norm_num [b]
  have hab : a + b = 1 := by
    norm_num [a, b]
  have hxy : a • x + b • y ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  -- Apply the global concavity inequality to the chosen second-variable section.
  have hIneq := hConc (x := x) (y := y) hx hy ha hb hab hxy
  have hxNotOpen : ¬ InOpenUnitInterval x := by
    dsimp [x, InOpenUnitInterval]
    norm_num
  have hyNotOpen : ¬ InOpenUnitInterval y := by
    dsimp [y, InOpenUnitInterval]
    norm_num
  have huOpen : InOpenUnitInterval (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
    dsimp [InOpenUnitInterval]
    constructor <;> norm_num
  have hxyOpen : InOpenUnitInterval (a • x + b • y) := by
    dsimp [a, b, x, y, InOpenUnitInterval]
    constructor <;> norm_num
  have hLeft :
      ((a : EReal) * (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) x +
        (b : EReal) * (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) y) =
        ⊤ := by
    have haPos : 0 < a := by
      norm_num [a]
    have hbPos : 0 < b := by
      norm_num [b]
    have hxVal :
        (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) x = ⊤ := by
      -- Both endpoints lie outside `(0, 1)`, so the upper simple extension is already `⊤`.
      simp [openUnitSquarePowerSaddle, hxNotOpen]
    have hyVal :
        (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) y = ⊤ := by
      simp [openUnitSquarePowerSaddle, hyNotOpen]
    -- Positive weights preserve `⊤`, so the Jensen left-hand side stays `⊤`.
    rw [hxVal, hyVal]
    simp [EReal.coe_mul_top_of_pos haPos, EReal.coe_mul_top_of_pos hbPos]
  have hRight :
      (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (1 / 2 : ℝ)) v) (a • x + b • y) =
        oneDimensionalPowerKernel (fun _ : Fin 1 => (1 / 2 : ℝ)) (a • x + b • y) := by
    -- The midpoint falls back inside `(0, 1)`, so the section takes the finite power-kernel value.
    simpa using helperForText_34_1_1_openSquare_value_of_open_membership huOpen hxyOpen
  rw [hLeft, hRight] at hIneq
  simp [oneDimensionalPowerKernel] at hIneq

/-- Helper for Text 34.1.7: the open-unit-square power upper simple extension is not
convex-concave on all of `ℝ × ℝ`. -/
lemma helperForText_34_1_7_openUnitSquarePowerSaddle_not_convexConcave :
    ¬ IsConvexConcave openUnitSquarePowerSaddle := by
  intro hK
  -- Specialize the convex-concave hypothesis to the second-variable section at `u = 1 / 2`.
  exact helperForText_34_1_7_secondSection_not_concave_at_half
    ((show IsConvexConcaveOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
        openUnitSquarePowerSaddle from hK).2
      (fun _ : Fin 1 => (1 / 2 : ℝ)) (by simp))

/-- Helper for Text 34.1.7: the open-unit-square power upper simple extension is not a global
saddle-function, so it cannot satisfy the theorem's upper-extension conclusion. -/
lemma helperForText_34_1_7_openUnitSquarePowerSaddle_not_saddle :
    ¬ IsSaddleFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
      openUnitSquarePowerSaddle := by
  intro hSaddle
  rcases hSaddle with hConcave | hConvex
  · -- The concave-convex branch is ruled out by the earlier off-domain convexity counterexample.
    exact helperForText_34_1_1_openUnitSquarePowerSaddle_not_concaveConvex
      (show IsConcaveConvex openUnitSquarePowerSaddle from hConcave)
  · -- The convex-concave branch is ruled out by the new second-section concavity failure.
    exact helperForText_34_1_7_openUnitSquarePowerSaddle_not_convexConcave
      (show IsConvexConcave openUnitSquarePowerSaddle from hConvex)

/-- Helper for Text 34.1.7: the open unit interval subset of `Fin 1 → ℝ` is convex. -/
lemma helperForText_34_1_7_openUnitInterval_convex :
    Convex ℝ {u : Fin 1 → ℝ | InOpenUnitInterval u} := by
  -- Reduce convexity of the set to the earlier closure of `(0, 1)` under convex combinations.
  intro x hx y hy a b ha hb hab
  exact helperForText_34_1_1_openUnitInterval_combo_mem hx hy ha hb hab

/-- Helper for Text 34.1.7: the open unit interval subset of `Fin 1 → ℝ` is nonempty. -/
lemma helperForText_34_1_7_openUnitInterval_nonempty :
    ({u : Fin 1 → ℝ | InOpenUnitInterval u} : Set (Fin 1 → ℝ)).Nonempty := by
  -- The midpoint `1 / 2` lies in `(0, 1)`.
  refine ⟨fun _ : Fin 1 => (1 / 2 : ℝ), ?_⟩
  dsimp [InOpenUnitInterval]
  constructor <;> norm_num

/-- Helper for Text 34.1.7: on the open unit square, the real power kernel carries the
concave-convex saddle orientation used by the textbook example. -/
lemma helperForText_34_1_7_oneDimensionalPowerKernel_isConcaveConvexOn :
    IsConcaveConvexOn
      {u : Fin 1 → ℝ | InOpenUnitInterval u}
      {v : Fin 1 → ℝ | InOpenUnitInterval v}
      oneDimensionalPowerKernel := by
  constructor
  · -- Transfer first-variable concavity from the already formalized open-square saddle example.
    intro v hv
    have hSection := (section34_example_u_pow_v).1.1 v hv
    intro x y hx hy a b ha hb hab hxy
    simpa [helperForText_34_1_1_openSquare_value_of_open_membership hxy hv,
      helperForText_34_1_1_openSquare_value_of_open_membership hx hv,
      helperForText_34_1_1_openSquare_value_of_open_membership hy hv] using
      hSection hx hy ha hb hab hxy
  · -- Transfer second-variable convexity from the same example in the same way.
    intro u hu
    have hSection := (section34_example_u_pow_v).1.2 u hu
    intro x y hx hy a b ha hb hab hxy
    simpa [helperForText_34_1_1_openSquare_value_of_open_membership hu hxy,
      helperForText_34_1_1_openSquare_value_of_open_membership hu hx,
      helperForText_34_1_1_openSquare_value_of_open_membership hu hy] using
      hSection hx hy ha hb hab hxy

/-- Helper for Text 34.1.7: the upper simple extension of the open-unit-square power kernel is
definitionally the `openUnitSquarePowerSaddle` counterexample. -/
lemma helperForText_34_1_7_upperSimpleExtension_eq_openUnitSquarePowerSaddle :
    upperSimpleExtension
      {u : Fin 1 → ℝ | InOpenUnitInterval u}
      {v : Fin 1 → ℝ | InOpenUnitInterval v}
      oneDimensionalPowerKernel =
      openUnitSquarePowerSaddle := by
  -- Both sides unfold to the same nested `if v ∈ (0,1) then if u ∈ (0,1) then u^v else ⊥ else ⊤`.
  rfl

/-- Helper for Text 34.1.7: the exact universal theorem claim, isolated as a single proposition
so the open-unit-square counterexample can specialize it. -/
def helperForText_34_1_7_targetTheoremClaim : Prop :=
  ∀ {m n : ℕ} {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)},
    Convex ℝ C → Convex ℝ D → C.Nonempty → D.Nonempty →
    ∀ J : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsSaddleFunctionOn C D J →
      (∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) →
      IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
          (lowerSimpleExtension C D J) ∧
        effectiveDomain₁ (lowerSimpleExtension C D J) = C ∧
        effectiveDomain₂ (lowerSimpleExtension C D J) = D ∧
        saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D ∧
        IsProperSaddleFunction (lowerSimpleExtension C D J) ∧
        IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
          (upperSimpleExtension C D J) ∧
        effectiveDomain₁ (upperSimpleExtension C D J) = C ∧
        effectiveDomain₂ (upperSimpleExtension C D J) = D ∧
        saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D ∧
        IsProperSaddleFunction (upperSimpleExtension C D J)

/-- Helper for Text 34.1.7: the open-unit-square power example satisfies every hypothesis in the
isolated theorem claim. -/
lemma helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses :
    Convex ℝ {u : Fin 1 → ℝ | InOpenUnitInterval u} ∧
      Convex ℝ {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
      ({u : Fin 1 → ℝ | InOpenUnitInterval u} : Set (Fin 1 → ℝ)).Nonempty ∧
      ({v : Fin 1 → ℝ | InOpenUnitInterval v} : Set (Fin 1 → ℝ)).Nonempty ∧
      IsSaddleFunctionOn
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel ∧
      (∀ u ∈ ({u : Fin 1 → ℝ | InOpenUnitInterval u} : Set (Fin 1 → ℝ)),
        ∀ v ∈ ({v : Fin 1 → ℝ | InOpenUnitInterval v} : Set (Fin 1 → ℝ)),
          (⊥ : EReal) < oneDimensionalPowerKernel u v ∧
            oneDimensionalPowerKernel u v < (⊤ : EReal)) := by
  -- Package the earlier convexity, nonemptiness, saddle, and finiteness facts for the
  -- counterexample into a single specialization lemma.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact helperForText_34_1_7_openUnitInterval_convex
  · exact helperForText_34_1_7_openUnitInterval_convex
  · exact helperForText_34_1_7_openUnitInterval_nonempty
  · exact helperForText_34_1_7_openUnitInterval_nonempty
  · -- The textbook `u^v` example already gives the needed saddle orientation on `(0, 1)²`.
    left
    exact helperForText_34_1_7_oneDimensionalPowerKernel_isConcaveConvexOn
  · intro u hu v hv
    -- Every in-domain power-kernel value is a coerced real number, hence finite.
    simp [oneDimensionalPowerKernel]

/-- Helper for Text 34.1.7: the specialized upper simple extension for the open-unit-square
power kernel is already not a global saddle-function. -/
lemma helperForText_34_1_7_specializedUpperSimpleExtension_not_saddle :
    ¬ IsSaddleFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
      (upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel) := by
  intro hUpperSaddle
  have hUpperEq :
      upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel =
        openUnitSquarePowerSaddle := by
    -- The specialized upper simple extension is definitionally the explicit counterexample.
    exact helperForText_34_1_7_upperSimpleExtension_eq_openUnitSquarePowerSaddle
  -- Transport the claimed global saddle property across the definitional identification.
  exact helperForText_34_1_7_openUnitSquarePowerSaddle_not_saddle
    (by simpa [hUpperEq] using hUpperSaddle)

/-- Helper for Text 34.1.7: the full specialized conclusion is false, because its upper simple
extension branch is the already refuted open-unit-square counterexample. -/
lemma helperForText_34_1_7_specializedConclusion_false :
    ¬ (IsSaddleFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
          (lowerSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) ∧
        effectiveDomain₁
            (lowerSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {u : Fin 1 → ℝ | InOpenUnitInterval u} ∧
        effectiveDomain₂
            (lowerSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
        saddleEffectiveDomain
            (lowerSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {u : Fin 1 → ℝ | InOpenUnitInterval u} ×ˢ
            {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
        IsProperSaddleFunction
          (lowerSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) ∧
        IsSaddleFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
          (upperSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) ∧
        effectiveDomain₁
            (upperSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {u : Fin 1 → ℝ | InOpenUnitInterval u} ∧
        effectiveDomain₂
            (upperSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
        saddleEffectiveDomain
            (upperSimpleExtension
              {u : Fin 1 → ℝ | InOpenUnitInterval u}
              {v : Fin 1 → ℝ | InOpenUnitInterval v}
              oneDimensionalPowerKernel) =
          {u : Fin 1 → ℝ | InOpenUnitInterval u} ×ˢ
            {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
        IsProperSaddleFunction
          (upperSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel)) := by
  intro hConclusion
  rcases hConclusion with ⟨_, _, _, _, _, hUpperSaddle, _, _, _, _⟩
  -- The specialized conclusion already contains the upper-extension saddle claim that fails.
  exact helperForText_34_1_7_specializedUpperSimpleExtension_not_saddle hUpperSaddle

end SaddleAmbient

end Section34
end Chap07
