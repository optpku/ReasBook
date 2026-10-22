/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- Definition 9.12: `Γ₀(H)` is the set of lower semicontinuous convex `]-∞,+∞]`-valued
functions on `H`, with convexity imposed on the effective domain so that properness is built into
the definition. -/
def gammaZero (H : Type u) [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] :
    Set (H → Set.Ioi (⊥ : EReal)) :=
  {f | LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∧ ConvexOn f (effectiveDomain f)}

notation "Γ₀(" H ")" => gammaZero H

/-- Membership in `Γ₀(H)` means lower semicontinuity together with convexity on the effective
domain. -/
@[simp] theorem mem_gammaZero_iff {f : H → Set.Ioi (⊥ : EReal)} :
    f ∈ Γ₀(H) ↔
      LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∧ ConvexOn f (effectiveDomain f) :=
  Iff.rfl

/-- Precomposing a `Γ₀(K)` function with a continuous linear equivalence preserves membership in
`Γ₀`. -/
theorem mem_gammaZero_comp_continuousLinearEquiv
    {K : Type*} [TopologicalSpace K] [AddCommGroup K] [Module ℝ K]
    {f : K → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(K))
    (e : H ≃L[ℝ] K) :
    f ∘ e ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa [Function.comp] using hf.1.comp e.continuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨y, hy⟩
      refine ⟨e.symm y, ?_⟩
      rw [mem_effectiveDomain_iff] at hy ⊢
      simpa [Function.comp] using hy
    · intro x hx y hy a ha0 ha1
      have hx' : e x ∈ effectiveDomain f := by
        rw [mem_effectiveDomain_iff] at hx ⊢
        simpa [Function.comp] using hx
      have hy' : e y ∈ effectiveDomain f := by
        rw [mem_effectiveDomain_iff] at hy ⊢
        simpa [Function.comp] using hy
      simpa [Function.comp, map_add, map_smul] using
        hf.2.ineq (x := e x) hx' (y := e y) hy' (α := a) ha0 ha1

/-- A proper `EReal`-valued function, packaged pointwise as an `]-∞,+∞]`-valued function. -/
noncomputable abbrev properIoi (f : H → EReal) (hproper : IsProper f) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨f x, bot_lt_iff_ne_bot.mpr (hproper.1 x)⟩

/-- Coercing `properIoi f hproper` back to `EReal` recovers the original function. -/
@[simp] theorem properIoi_apply {X : Type*} {f : X → EReal} (hproper : IsProper f) (x : X) :
    (properIoi f hproper x : EReal) = f x :=
  rfl

/-- The canonical `EReal` coercion of `properIoi f hproper` is exactly `f`. -/
@[simp] theorem asEReal_properIoi {X : Type*} {f : X → EReal} (hproper : IsProper f) :
    (properIoi f hproper).asEReal = f :=
  rfl

/-- A real-valued member of `Γ(H)` yields a member of `Γ₀(H)` after the canonical coercion to
`]-∞,+∞]`. -/
theorem toEReal_mem_gammaZero_of_mem_gamma
    [SequentialSpace H] {f : H → ℝ} (hf : (fun x : H ↦ (f x : EReal)) ∈ gamma H) :
    f.toEReal ∈ Γ₀(H) := by
  rw [mem_gamma_iff] at hf
  rw [mem_gammaZero_iff]
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · simpa [Function.toEReal_apply] using hf_lsc
  · refine ⟨by simp [Function.effectiveDomain_toEReal], ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy a ha0 ha1
      simpa [Function.toEReal_apply] using hf_convex ha0.le ha1.le

/-- Outside the effective domain of an `]-∞,+∞]`-valued function, the coerced value is `⊤`. -/
private theorem asEReal_eq_top_of_not_mem_effectiveDomain
    {K : Type*} {f : K → Set.Ioi (⊥ : EReal)} {x : K} (hx : x ∉ effectiveDomain f) :
    f.asEReal x = ⊤ := by
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Coercing a `Γ₀(K)` function to `EReal` gives a member of `γ(K)`. -/
theorem asEReal_mem_gamma_of_mem_gammaZero
    [SequentialSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal ∈ gamma H := by
  rw [mem_gammaZero_iff] at hf
  rw [mem_gamma_iff]
  rcases hf with ⟨hf_lsc, hf_convex⟩
  refine ⟨?_, hf_lsc⟩
  intro x y a ha0 ha1
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    have hx1 : ((1 : ℝ) • x + (1 - (1 : ℝ)) • y) = x := by
      simp
    rw [hx1]
    have hzero : (1 - (1 : EReal)) * f.asEReal y = 0 := by
      have hcoef_zero : (1 - (1 : EReal)) = 0 := by
        exact EReal.sub_self (x := (1 : EReal)) (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      rw [hcoef_zero]
      simp
    simp [Function.asEReal_apply, hzero]
  have h0a : (0 : ℝ) ≠ a := by
    intro h
    exact ha_zero h.symm
  have ha_pos : 0 < a := lt_of_le_of_ne ha0 h0a
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 ha_one
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  change f.asEReal (a • x + (1 - a) • y) ≤
    (a : EReal) * f.asEReal x + (1 - (a : EReal)) * f.asEReal y
  by_cases hx : x ∈ effectiveDomain f
  · by_cases hy : y ∈ effectiveDomain f
    · exact hf_convex.ineq hx hy ha_pos ha_lt_one
    · have hy_top : f.asEReal y = ⊤ :=
        asEReal_eq_top_of_not_mem_effectiveDomain hy
      have hx_term_ne_bot : (a : EReal) * f.asEReal x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inr (ne_of_gt (f x).2), Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha0)⟩
      rw [hy_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
      rw [EReal.add_top_of_ne_bot hx_term_ne_bot]
      exact le_top
  · have hx_top : f.asEReal x = ⊤ :=
      asEReal_eq_top_of_not_mem_effectiveDomain hx
    have hcoef_nonneg : (0 : EReal) ≤ 1 - (a : EReal) := by
      exact_mod_cast sub_nonneg.mpr ha1
    have hy_term_ne_bot : (1 - (a : EReal)) * f.asEReal y ≠ ⊥ := by
      have hcoef_ne_bot : (1 - (a : EReal)) ≠ ⊥ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_bot (1 - a)
      have hcoef_ne_top : (1 - (a : EReal)) ≠ ⊤ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_top (1 - a)
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl hcoef_ne_bot, Or.inr (ne_of_gt (f y).2), Or.inl hcoef_ne_top,
        Or.inl hcoef_nonneg⟩
    rw [hx_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
    rw [EReal.top_add_of_ne_bot hy_term_ne_bot]
    exact le_top

/-- A proper member of `Γ(H)` becomes a member of `Γ₀(H)` through `properIoi`. -/
theorem properIoi_mem_gammaZero_of_mem_gamma
    [SequentialSpace H] {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    properIoi f hproper ∈ Γ₀(H) := by
  rw [mem_gamma_iff] at hf
  rw [mem_gammaZero_iff]
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · simpa using hf_lsc
  · refine ⟨?_, ?_, ?_⟩
    · simpa [effectiveDomain, dom] using hproper.2
    · intro x hx
      exact hx
    · intro x hx y hy a ha0 ha1
      simpa using hf_convex ha0.le ha1.le

/-- A function in `Γ₀(H)` is proper as an extended-real-valued function. -/
theorem isProper_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    IsProper (fun x : H ↦ (f x : EReal)) := by
  refine ⟨?_, ConvexOn.nonempty hf.2⟩
  intro x hx
  simpa [hx] using (f x).2

/-- A member of `Γ₀(H)` has a convex real-height epigraph when viewed through its canonical
underlying `EReal`-valued function. -/
theorem convex_epigraph_asEReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Convex ℝ (epigraph f.asEReal) := by
  refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
  intro x y hx hy α hα0 hα1
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.2.ineq hx' hy' hα0 hα1

/-- Hence every real lower level set of a member of `Γ₀(H)` is convex. -/
theorem convex_lowerLevelSet_asEReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (ξ : ℝ) :
    Convex ℝ (lowerLevelSet f.asEReal ξ) :=
  convex_lowerLevelSet_of_convex_epigraph f.asEReal
    (convex_epigraph_asEReal_of_mem_gammaZero hf) ξ

end ERealFunction
