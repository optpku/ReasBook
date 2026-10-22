/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part11

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Corollary 20.2.1: the support function at `0` is `0` on every
nonempty set. -/
lemma helperForCorollary_20_2_1_supportFunctionEReal_zero_of_nonempty
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCne : C.Nonempty) :
    supportFunctionEReal C (0 : Fin n → ℝ) = (0 : EReal) := by
  unfold supportFunctionEReal
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC, rfl⟩
    simp
  · rcases hCne with ⟨x, hxC⟩
    exact le_sSup ⟨x, hxC, by simp⟩

/-- Helper for Corollary 20.2.1: if a nonempty set is contained in a level
hyperplane, then its support function in that normal direction is exactly the
corresponding level. -/
lemma helperForCorollary_20_2_1_supportFunctionEReal_eq_level_of_nonempty_subset_level_hyperplane
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCne : C.Nonempty)
    {b : Fin n → ℝ} {β : ℝ}
    (hCsubset : C ⊆ {x : Fin n → ℝ | x ⬝ᵥ b = β}) :
    supportFunctionEReal C b = (β : EReal) := by
  have hSupportLe : supportFunctionEReal C b ≤ (β : EReal) := by
    refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := β)).2 ?_
    intro x hxC
    exact le_of_eq (hCsubset hxC)
  rcases hCne with ⟨x0, hx0C⟩
  have hx0Eq : x0 ⬝ᵥ b = β := hCsubset hx0C
  have hBetaLe : (β : EReal) ≤ supportFunctionEReal C b := by
    have hx0Le : ((x0 ⬝ᵥ b : ℝ) : EReal) ≤ supportFunctionEReal C b := by
      unfold supportFunctionEReal
      exact le_sSup ⟨x0, hx0C, rfl⟩
    simpa [hx0Eq] using hx0Le
  exact le_antisymm hSupportLe hBetaLe

/-- Helper for Corollary 20.2.1: reformulate nonemptiness of
`C₁ ∩ intrinsicInterior ℝ C₂` as exclusion of proper separators that fail to
contain `C₂`. -/
lemma helperForCorollary_20_2_1_nonemptyInter_iff_no_noncontainment_separator
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) :
    Set.Nonempty (C₁ ∩ intrinsicInterior ℝ C₂) ↔
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  have hSepIffInterEmpty :
      (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) ↔
        C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) :=
    exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hC₂conv hC₁poly
  constructor
  · intro hInter hSep
    have hInterEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) := hSepIffInterEmpty.mp hSep
    exact (Set.not_nonempty_iff_eq_empty.mpr hInterEmpty) hInter
  · intro hNoSep
    by_contra hInterNot
    have hInterEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) :=
      Set.not_nonempty_iff_eq_empty.mp hInterNot
    have hSep : ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
      hSepIffInterEmpty.mpr hInterEmpty
    exact hNoSep hSep

/-- Helper for Corollary 20.2.1: a proper separator that does not contain `C₂`
produces a support-function counterexample. -/
lemma helperForCorollary_20_2_1_exists_support_counterexample_of_noncontainment_separator
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    ∃ xStar : Fin n → ℝ,
      supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
        supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar := by
  rcases hSep with ⟨H, hHsep, hC₂notSubset⟩
  rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hHsep with
    ⟨b, β, hb0, hHdef, hC₁_ge, hC₂_le, hnotBoth⟩
  let xStar : Fin n → ℝ := -b
  have hC₁xStarLeNegBeta : ∀ x : Fin n → ℝ, x ∈ C₁ → x ⬝ᵥ xStar ≤ -β := by
    intro x hxC₁
    have hxGe : β ≤ x ⬝ᵥ b := hC₁_ge x hxC₁
    have hxLe : -(x ⬝ᵥ b) ≤ -β := neg_le_neg hxGe
    simpa [xStar, dotProduct_neg] using hxLe
  have hSupportC₁xStarLeNegBeta : supportFunctionEReal C₁ xStar ≤ ((-β : ℝ) : EReal) := by
    exact
      (section13_supportFunctionEReal_le_coe_iff
        (n := n) (C := C₁) (y := xStar) (μ := -β)).2 hC₁xStarLeNegBeta
  have hSupportC₂bLeBeta : supportFunctionEReal C₂ b ≤ (β : EReal) := by
    exact
      (section13_supportFunctionEReal_le_coe_iff
        (n := n) (C := C₂) (y := b) (μ := β)).2 hC₂_le
  have hNegBetaLeNegSupportC₂b : ((-β : ℝ) : EReal) ≤ -supportFunctionEReal C₂ b := by
    exact (EReal.neg_le_neg_iff).2 hSupportC₂bLeBeta
  have hPremise :
      supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) := by
    have hStep1 : supportFunctionEReal C₁ xStar ≤ ((-β : ℝ) : EReal) := hSupportC₁xStarLeNegBeta
    have hStep2 : ((-β : ℝ) : EReal) ≤ -supportFunctionEReal C₂ (-xStar) := by
      simpa [xStar] using hNegBetaLeNegSupportC₂b
    exact le_trans hStep1 hStep2
  have hWitnessStrict :
      ∃ y : Fin n → ℝ, y ∈ C₂ ∧ (-β : ℝ) < y ⬝ᵥ xStar := by
    rcases Set.not_subset.1 hC₂notSubset with ⟨y, hyC₂, hyNotH⟩
    have hyNe : y ⬝ᵥ b ≠ β := by
      intro hyEq
      apply hyNotH
      simpa [hHdef, hyEq]
    have hyLe : y ⬝ᵥ b ≤ β := hC₂_le y hyC₂
    have hyLt : y ⬝ᵥ b < β := lt_of_le_of_ne hyLe hyNe
    have hyGt : (-β : ℝ) < y ⬝ᵥ xStar := by
      have hNegLt : (-β : ℝ) < -(y ⬝ᵥ b) := neg_lt_neg hyLt
      simpa [xStar, dotProduct_neg] using hNegLt
    exact ⟨y, hyC₂, hyGt⟩
  have hNegBetaLtSupportC₂xStar : ((-β : ℝ) : EReal) < supportFunctionEReal C₂ xStar := by
    rcases hWitnessStrict with ⟨y, hyC₂, hyGt⟩
    have hyLeSup : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ supportFunctionEReal C₂ xStar := by
      unfold supportFunctionEReal
      exact le_sSup ⟨y, hyC₂, rfl⟩
    have hyGtEReal : ((-β : ℝ) : EReal) < ((y ⬝ᵥ xStar : ℝ) : EReal) :=
      (EReal.coe_lt_coe_iff).2 hyGt
    exact lt_of_lt_of_le hyGtEReal hyLeSup
  have hStrict : supportFunctionEReal C₁ xStar < supportFunctionEReal C₂ xStar := by
    exact lt_of_le_of_lt hSupportC₁xStarLeNegBeta hNegBetaLtSupportC₂xStar
  have hNotEq : supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar := ne_of_lt hStrict
  exact ⟨xStar, hPremise, hNotEq⟩

/-- Helper for Corollary 20.2.1: a support-function counterexample yields a
proper separating hyperplane that does not contain `C₂`. -/
lemma helperForCorollary_20_2_1_exists_noncontainment_separator_of_support_counterexample
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hCounter :
      ∃ xStar : Fin n → ℝ,
        supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
          supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  rcases hCounter with ⟨xStar, hLe, hNe⟩
  have hSupportC₁xStarNeTop : supportFunctionEReal C₁ xStar ≠ ⊤ := by
    intro hTop
    have hTopLe : (⊤ : EReal) ≤ -supportFunctionEReal C₂ (-xStar) := by
      simpa [hTop] using hLe
    have hTopEq : -supportFunctionEReal C₂ (-xStar) = (⊤ : EReal) := (top_le_iff.mp hTopLe)
    have hBotEq : supportFunctionEReal C₂ (-xStar) = (⊥ : EReal) := by
      have hNegEq : -(-supportFunctionEReal C₂ (-xStar)) = -((⊤ : EReal)) :=
        congrArg Neg.neg hTopEq
      simpa using hNegEq
    exact
      (section13_supportFunctionEReal_ne_bot_of_nonempty
        (n := n) (C := C₂) hC₂ne (-xStar)) hBotEq
  let β : ℝ := (supportFunctionEReal C₁ xStar).toReal
  have hSupportC₁xStarEqBeta : supportFunctionEReal C₁ xStar = (β : EReal) := by
    symm
    exact
      section13_supportFunctionEReal_coe_toReal
        (n := n) (C := C₁) hC₁ne (y := xStar) hSupportC₁xStarNeTop
  have hSupportC₁xStarLeBeta : supportFunctionEReal C₁ xStar ≤ (β : EReal) := by
    simpa [β] using (EReal.le_coe_toReal (x := supportFunctionEReal C₁ xStar) hSupportC₁xStarNeTop)
  have hC₁leBeta : ∀ x : Fin n → ℝ, x ∈ C₁ → x ⬝ᵥ xStar ≤ β :=
    (section13_supportFunctionEReal_le_coe_iff
      (n := n) (C := C₁) (y := xStar) (μ := β)).1 hSupportC₁xStarLeBeta
  have hBetaLeNegSupportC₂NegXStar : (β : EReal) ≤ -supportFunctionEReal C₂ (-xStar) := by
    simpa [hSupportC₁xStarEqBeta] using hLe
  have hSupportC₂NegXStarLeNegBeta : supportFunctionEReal C₂ (-xStar) ≤ ((-β : ℝ) : EReal) := by
    have hNeg : supportFunctionEReal C₂ (-xStar) ≤ -(β : EReal) :=
      (EReal.le_neg).1 hBetaLeNegSupportC₂NegXStar
    simpa using hNeg
  have hC₂negBound : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ (-xStar) ≤ -β :=
    (section13_supportFunctionEReal_le_coe_iff
      (n := n) (C := C₂) (y := -xStar) (μ := -β)).1 hSupportC₂NegXStarLeNegBeta
  have hC₂geBeta : ∀ y : Fin n → ℝ, y ∈ C₂ → β ≤ y ⬝ᵥ xStar := by
    intro y hyC₂
    have hyNegLe : y ⬝ᵥ (-xStar) ≤ -β := hC₂negBound y hyC₂
    have hyNegLe' : -(y ⬝ᵥ xStar) ≤ -β := by
      simpa [dotProduct_neg] using hyNegLe
    exact (neg_le_neg_iff).1 hyNegLe'
  have hxStarNeZero : xStar ≠ 0 := by
    intro hxStarZero
    have hSupportC₁zero :
        supportFunctionEReal C₁ (0 : Fin n → ℝ) = (0 : EReal) :=
      helperForCorollary_20_2_1_supportFunctionEReal_zero_of_nonempty
        (n := n) (C := C₁) hC₁ne
    have hSupportC₂zero :
        supportFunctionEReal C₂ (0 : Fin n → ℝ) = (0 : EReal) :=
      helperForCorollary_20_2_1_supportFunctionEReal_zero_of_nonempty
        (n := n) (C := C₂) hC₂ne
    have hEq : supportFunctionEReal C₁ xStar = supportFunctionEReal C₂ xStar := by
      simpa [hxStarZero, hSupportC₁zero, hSupportC₂zero]
    exact hNe hEq
  let H : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ xStar = β}
  have hC₁subsetLeHalf : C₁ ⊆ {x : Fin n → ℝ | x ⬝ᵥ xStar ≤ β} := by
    intro x hxC₁
    exact hC₁leBeta x hxC₁
  have hC₂subsetGeHalf : C₂ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ xStar} := by
    intro y hyC₂
    exact hC₂geBeta y hyC₂
  have hSep : HyperplaneSeparates n H C₁ C₂ := by
    refine ⟨hC₁ne, hC₂ne, xStar, β, hxStarNeZero, ?_, ?_⟩
    · ext x
      simp [H]
    · exact Or.inl ⟨hC₁subsetLeHalf, hC₂subsetGeHalf⟩
  have hC₂notSubsetH : ¬ C₂ ⊆ H := by
    intro hC₂subsetH
    have hSupportC₂xStarEqBeta : supportFunctionEReal C₂ xStar = (β : EReal) :=
      helperForCorollary_20_2_1_supportFunctionEReal_eq_level_of_nonempty_subset_level_hyperplane
        (n := n) (C := C₂) hC₂ne (b := xStar) (β := β) hC₂subsetH
    have hEq : supportFunctionEReal C₁ xStar = supportFunctionEReal C₂ xStar := by
      calc
        supportFunctionEReal C₁ xStar = (β : EReal) := hSupportC₁xStarEqBeta
        _ = supportFunctionEReal C₂ xStar := hSupportC₂xStarEqBeta.symm
    exact hNe hEq
  have hProper : HyperplaneSeparatesProperly n H C₁ C₂ := by
    refine ⟨hSep, ?_⟩
    intro hBoth
    exact hC₂notSubsetH hBoth.2
  exact ⟨H, hProper, hC₂notSubsetH⟩

/-- Helper for Corollary 20.2.1: logical normalization between a universal
implication and absence of a counterexample witness. -/
lemma helperForCorollary_20_2_1_forallImp_iff_no_support_counterexample
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (∀ xStar : Fin n → ℝ,
      supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) →
        supportFunctionEReal C₁ xStar = supportFunctionEReal C₂ xStar) ↔
      ¬ ∃ xStar : Fin n → ℝ,
        supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
          supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar := by
  constructor
  · intro hAll hCounter
    rcases hCounter with ⟨xStar, hLe, hNe⟩
    exact hNe (hAll xStar hLe)
  · intro hNoCounter xStar hLe
    by_contra hEq
    exact hNoCounter ⟨xStar, hLe, hEq⟩

/-- Corollary 20.2.1: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` with
`C₁` polyhedral. Then `C₁ ∩ ri(C₂)` is nonempty if and only if every vector
`x*` satisfying `δ*(x* | C₁) ≤ -δ*(-x* | C₂)` also satisfies
`δ*(x* | C₁) = δ*(x* | C₂)`, with `δ*` formalized by `supportFunctionEReal`
and `ri` by `intrinsicInterior`. -/
theorem inter_intrinsicInterior_nonempty_iff_supportFunction_imp_eq_of_nonempty_convex_polyhedral_left
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) :
    Set.Nonempty (C₁ ∩ intrinsicInterior ℝ C₂) ↔
      ∀ xStar : Fin n → ℝ,
        supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) →
          supportFunctionEReal C₁ xStar = supportFunctionEReal C₂ xStar := by
  have hGeom :
      Set.Nonempty (C₁ ∩ intrinsicInterior ℝ C₂) ↔
        ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
    helperForCorollary_20_2_1_nonemptyInter_iff_no_noncontainment_separator
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hC₂conv hC₁poly
  have hSepCounter :
      (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) ↔
        (∃ xStar : Fin n → ℝ,
          supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
            supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar) := by
    constructor
    · intro hSep
      exact
        helperForCorollary_20_2_1_exists_support_counterexample_of_noncontainment_separator
          (n := n) (C₁ := C₁) (C₂ := C₂) hSep
    · intro hCounter
      exact
        helperForCorollary_20_2_1_exists_noncontainment_separator_of_support_counterexample
          (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hCounter
  have hNoSepNoCounter :
      (¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) ↔
        (¬ ∃ xStar : Fin n → ℝ,
          supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
            supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar) := by
    constructor
    · intro hNoSep hCounter
      exact hNoSep (hSepCounter.mpr hCounter)
    · intro hNoCounter hSep
      exact hNoCounter (hSepCounter.mp hSep)
  calc
    Set.Nonempty (C₁ ∩ intrinsicInterior ℝ C₂) ↔
        ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := hGeom
    _ ↔
        (¬ ∃ xStar : Fin n → ℝ,
          supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) ∧
            supportFunctionEReal C₁ xStar ≠ supportFunctionEReal C₂ xStar) := hNoSepNoCounter
    _ ↔
        ∀ xStar : Fin n → ℝ,
          supportFunctionEReal C₁ xStar ≤ -supportFunctionEReal C₂ (-xStar) →
            supportFunctionEReal C₁ xStar = supportFunctionEReal C₂ xStar := by
          simpa using
            (helperForCorollary_20_2_1_forallImp_iff_no_support_counterexample
              (n := n) (C₁ := C₁) (C₂ := C₂)).symm

end Section20
end Chap04
