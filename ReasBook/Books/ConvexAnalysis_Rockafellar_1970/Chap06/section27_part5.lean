/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part4

section Chap06
section Section27

/- The linewise-attainment conjecture preceding Theorem 27.3 in Rockafellar is intentionally
omitted: the book immediately disproves it using the squared distance to the parabolic set
`P = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` minus the first coordinate.  That finite convex function
attains its infimum on every affine line but is unbounded below along `(t, t²)`. -/

/-- A function attains its infimum on `C` when some point of `C` realizes the infimum of the
restriction of the function to `C`. -/
def AttainsInfimumOn {n : ℕ} (f : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ xBar : C, f xBar = ⨅ x : C, f x

/-- A function and a set have no common recession directions when every vector that is both a
recession direction of the function and a recession direction of the set is zero. -/
def HasNoCommonRecessionDirections {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (C : Set (Fin n → ℝ)) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f y → y ∈ Set.recessionCone C → y = 0

/-- Every common recession direction of `f` and `C` is a direction of constancy of `f`. -/
def CommonRecessionDirectionsAreDirectionsOfConstancy {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f y → y ∈ Set.recessionCone C →
    IsDirectionOfConstancy f y

/-- Helper for Theorem 6.27.4: if `h` is identically `⊤` on `C`, then the constrained infimum is
already attained at any point of `C`. -/
lemma helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hCne : Set.Nonempty C)
    (hallTop : ∀ x : Fin n → ℝ, x ∈ C → h x = (⊤ : EReal)) :
    AttainsInfimumOn h C := by
  rcases hCne with ⟨x0, hx0C⟩
  refine ⟨⟨x0, hx0C⟩, ?_⟩
  apply le_antisymm
  · -- Every constrained value is `⊤`, so the restricted infimum is also `⊤`.
    apply le_iInf
    intro x
    simp [hallTop x x.property]
  · -- The restricted infimum is always bounded above by the value at any feasible point.
    simpa [hallTop x0 hx0C] using
      (iInf_le (fun x : C => h x) ⟨x0, hx0C⟩)

/-- Helper for Theorem 6.27.4: whenever a real level lies strictly above the constrained infimum,
the corresponding restricted sublevel is nonempty. -/
lemma helperForTheorem_6_27_4_exists_point_of_restrictedInf_lt_level
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) (β : ℝ)
    (hβ : (⨅ x : C, h x) < (β : EReal)) :
    ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (β : EReal) := by
  by_contra hEmpty
  push_neg at hEmpty
  have hβle : (β : EReal) ≤ ⨅ x : C, h x := by
    refine le_iInf ?_
    intro x
    exact le_of_lt (hEmpty x x.property)
  exact (not_lt_of_ge hβle) hβ

/-- Helper for Theorem 6.27.4: a feasible point lying in every approximate restricted sublevel
already attains the constrained infimum. -/
lemma helperForTheorem_6_27_4_eq_restrictedInf_of_mem_all_approximateSublevels
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) (x : Fin n → ℝ)
    (hxC : x ∈ C) (hInfFinite : IsFiniteEReal (⨅ y : C, h y))
    (hxApprox :
      ∀ k : ℕ,
        h x ≤ ((((⨅ y : C, h y).toReal) + 1 / (k + 1 : ℝ) : ℝ) : EReal))
    (hxBot : h x ≠ (⊥ : EReal)) :
    h x = ⨅ y : C, h y := by
  have hInfLe : (⨅ y : C, h y) ≤ h x := by
    exact iInf_le (fun y : C => h y) ⟨x, hxC⟩
  have hInfCoe : ((((⨅ y : C, h y).toReal) : ℝ) : EReal) = (⨅ y : C, h y) := by
    simpa using EReal.coe_toReal (x := (⨅ y : C, h y)) hInfFinite.1 hInfFinite.2
  have hxTop : h x ≠ (⊤ : EReal) := by
    have h0 := hxApprox 0
    intro hxTop
    have : (⊤ : EReal) ≤
        ((((⨅ y : C, h y).toReal) + 1 / (0 + 1 : ℝ) : ℝ) : EReal) := by
      simpa [hxTop] using h0
    exact (not_top_le_coe (((⨅ y : C, h y).toReal) + 1 / (0 + 1 : ℝ))) this
  have hxCoe : ((((h x).toReal) : ℝ) : EReal) = h x := by
    simpa using EReal.coe_toReal (x := h x) hxTop hxBot
  apply le_antisymm
  · -- If `h x` were still above the constrained infimum, a sufficiently tight approximate
    -- sublevel would exclude `x`, contradicting the hypothesis that `x` belongs to them all.
    by_contra hxGt
    have hxGt' : (⨅ y : C, h y) < h x := lt_of_not_ge hxGt
    have hRealGap : (⨅ y : C, h y).toReal < (h x).toReal := by
      exact EReal.coe_lt_coe_iff.mp (by simpa [hInfCoe, hxCoe] using hxGt')
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hRealGap)
    have hk' : (⨅ y : C, h y).toReal + 1 / (k + 1 : ℝ) < (h x).toReal := by
      have hdiv :
          1 / (k + 1 : ℝ) < (h x).toReal - (⨅ y : C, h y).toReal := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hk
      linarith
    have hltE :
        ((((⨅ y : C, h y).toReal + 1 / (k + 1 : ℝ) : ℝ)) : EReal) < h x := by
      rw [← hxCoe]
      exact_mod_cast hk'
    exact (not_lt_of_ge (hxApprox k)) hltE
  · -- The constrained infimum is always below every feasible value.
    exact hInfLe


end Section27
end Chap06
