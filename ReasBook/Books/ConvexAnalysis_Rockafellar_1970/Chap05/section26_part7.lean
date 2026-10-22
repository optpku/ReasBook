/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part6

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped ConvexAnalysis Pointwise

/-- Helper for Corollary 26.3.2: every point of `dom ∂(f₁* + f₂*)` lies in `dom ∂(f₁*)`. -/
lemma helperForCorollary_26_3_2_subdifferentialEffectiveDomain_sum_subset_left
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₁)
    (hf₂ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₂)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂)))) :
    subdifferentialEffectiveDomain
        (fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x) ⊆
      subdifferentialEffectiveDomain (fenchelConjugate n f₁) := by
  let gTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases (fenchelConjugate n f₁) (fun _ => fenchelConjugate n f₂) i
  have hf₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁
  have hf₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₂) hf₂
  have hgTwo_proper :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (gTwo i) := by
    intro i
    fin_cases i
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper)
  have hriWitness :=
    helperForCorollary_26_3_2_commonRelativeInterior_twoConjugates (f₁ := f₁) (f₂ := f₂) hri
  intro x hx
  have hxNonempty :
      (subdifferentialAt (fun y => ∑ i : Fin 2, gTwo i y) x).Nonempty := by
    simpa [gTwo, Fin.sum_univ_two] using
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        (fun y => fenchelConjugate n f₁ y + fenchelConjugate n f₂ y) x).1 hx
  rcases hxNonempty with ⟨xDual, hxDual⟩
  have hsum :
      subdifferentialAt (fun y => ∑ i : Fin 2, gTwo i y) x =
        ∑ i : Fin 2, (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain gTwo hgTwo_proper
      hriWitness x
  have hxInSum :
      xDual ∈
        ∑ i : Fin 2, (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    rw [← hsum]
    exact hxDual
  rcases
      (Set.mem_fintype_sum
        (f := fun i : Fin 2 => (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))))
        (a := xDual)).1 hxInSum with
    ⟨parts, hparts, _hsumParts⟩
  -- Any summand decomposition produced by the Minkowski-sum formula gives a left summand witness.
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fenchelConjugate n f₁) x).2 (by
        refine ⟨parts 0, ?_⟩
        simpa [gTwo] using hparts 0)

/-- Helper for Corollary 26.3.2: every point of `dom ∂(f₁* + f₂*)` lies in `dom ∂(f₂*)`. -/
lemma helperForCorollary_26_3_2_subdifferentialEffectiveDomain_sum_subset_right
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₁)
    (hf₂ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₂)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂)))) :
    subdifferentialEffectiveDomain
        (fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x) ⊆
      subdifferentialEffectiveDomain (fenchelConjugate n f₂) := by
  let gTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases (fenchelConjugate n f₁) (fun _ => fenchelConjugate n f₂) i
  have hf₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁
  have hf₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₂) hf₂
  have hgTwo_proper :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (gTwo i) := by
    intro i
    fin_cases i
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper)
  have hriWitness :=
    helperForCorollary_26_3_2_commonRelativeInterior_twoConjugates (f₁ := f₁) (f₂ := f₂) hri
  intro x hx
  have hxNonempty :
      (subdifferentialAt (fun y => ∑ i : Fin 2, gTwo i y) x).Nonempty := by
    simpa [gTwo, Fin.sum_univ_two] using
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        (fun y => fenchelConjugate n f₁ y + fenchelConjugate n f₂ y) x).1 hx
  rcases hxNonempty with ⟨xDual, hxDual⟩
  have hsum :
      subdifferentialAt (fun y => ∑ i : Fin 2, gTwo i y) x =
        ∑ i : Fin 2, (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain gTwo hgTwo_proper
      hriWitness x
  have hxInSum :
      xDual ∈
        ∑ i : Fin 2, (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    rw [← hsum]
    exact hxDual
  rcases
      (Set.mem_fintype_sum
        (f := fun i : Fin 2 => (subdifferentialAt (gTwo i) x : Set (Module.Dual ℝ (Fin n → ℝ))))
        (a := xDual)).1 hxInSum with
    ⟨parts, hparts, _hsumParts⟩
  -- The right component of the same decomposition supplies the required right subgradient.
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fenchelConjugate n f₂) x).2 (by
        refine ⟨parts 1, ?_⟩
        simpa [gTwo] using hparts 1)

/-- Helper for Corollary 26.3.2: subdifferentiability forces finiteness at the same point. -/
lemma helperForCorollary_26_3_2_finite_of_mem_subdifferentialEffectiveDomain
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ} (hx : x ∈ subdifferentialEffectiveDomain f) :
    f x ≠ (⊤ : EReal) := by
  rcases
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).1 hx with
    ⟨xDual, hxDual⟩
  let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
  have hxSub : IsEuclideanSubgradientAt f x xStar := by
    simpa [xStar, IsEuclideanSubgradientAt] using hxDual
  exact (helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x xStar hxSub).1

/-- Helper for Corollary 26.3.2: on every convex subset of `dom ∂(f₁* + f₂*)`, the real-valued
restriction of `f₁* + f₂*` is strictly convex. -/
lemma helperForCorollary_26_3_2_strictConvexOn_conjugateSum_subdifferentialEffectiveDomain
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₁)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₂)
    (hf₁_smooth : IsEssentiallySmooth f₁)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂))))
    {C : Set (Fin n → ℝ)}
    (hCSubset :
      C ⊆ subdifferentialEffectiveDomain
        (fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x))
    (hCConv : Convex ℝ C) :
    StrictConvexOn ℝ C
      (fun x => ((fenchelConjugate n f₁ x + fenchelConjugate n f₂ x)).toReal) := by
  let g₁ : (Fin n → ℝ) → EReal := fenchelConjugate n f₁
  let g₂ : (Fin n → ℝ) → EReal := fenchelConjugate n f₂
  have hf₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁
  have hf₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₂) hf₂
  have hg₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g₁ := by
    simpa [g₁] using (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
  have hg₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g₂ := by
    simpa [g₂] using (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper)
  have hg₁_closed : LowerSemicontinuous g₁ := (fenchelConjugate_closedConvex (n := n) (f := f₁)).1
  have hg₁_ereal : ProperConvexERealFunction (F := (Fin n → ℝ)) g₁ :=
    helperForLemma_26_2_properConvexERealFunction hg₁_proper
  have hbiconj₁ :
      fenchelConjugate n g₁ = f₁ := by
    -- Closed proper convexity of `f₁` identifies the conjugate of `g₁ = f₁*` with `f₁`.
    simpa [g₁] using
      (fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f₁)
        (hf_closed := hf₁_closed)
        (hf_convex := (helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁).1)
        (hf_ne_bot := fun x => hf₁.1.1 x))
  have hg₁_essStrict : IsEssentiallyStrictlyConvex g₁ := by
    -- Theorem 26.3 turns essential smoothness of `f₁ = (f₁*)*` into essential strict convexity of `f₁*`.
    refine
      (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
        (f := g₁) hg₁_ereal hg₁_closed).2 ?_
    simpa [hbiconj₁] using hf₁_smooth
  have hLeftSubset :
      C ⊆ subdifferentialEffectiveDomain g₁ :=
    helperForCorollary_26_3_2_subdifferentialEffectiveDomain_sum_subset_left
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hri |> Set.Subset.trans hCSubset
  have hRightSubset :
      C ⊆ subdifferentialEffectiveDomain g₂ :=
    helperForCorollary_26_3_2_subdifferentialEffectiveDomain_sum_subset_right
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hri |> Set.Subset.trans hCSubset
  have hStrictLeft :
      StrictConvexOn ℝ C (fun x => (g₁ x).toReal) :=
    hg₁_essStrict.2 hLeftSubset hCConv
  have hConvRight :
      ConvexOn ℝ C (fun x => (g₂ x).toReal) := by
    refine ⟨hCConv, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxTop : g₂ x ≠ (⊤ : EReal) :=
      helperForCorollary_26_3_2_finite_of_mem_subdifferentialEffectiveDomain hg₂_proper
        (hRightSubset hx)
    have hyTop : g₂ y ≠ (⊤ : EReal) :=
      helperForCorollary_26_3_2_finite_of_mem_subdifferentialEffectiveDomain hg₂_proper
        (hRightSubset hy)
    exact
      (helperForTheorem_26_3_convexCombination_toReal_le hg₂_proper ha hb hab hxTop hyTop).2
  have hEqOn :
      Set.EqOn
        (fun x => ((g₁ x + g₂ x)).toReal)
        ((fun x => (g₁ x).toReal) + fun x => (g₂ x).toReal) C := by
    intro x hx
    have hxLeft : x ∈ subdifferentialEffectiveDomain g₁ := hLeftSubset hx
    have hxRight : x ∈ subdifferentialEffectiveDomain g₂ := hRightSubset hx
    have hxLeftTop :
        g₁ x ≠ (⊤ : EReal) :=
      helperForCorollary_26_3_2_finite_of_mem_subdifferentialEffectiveDomain hg₁_proper hxLeft
    have hxRightTop :
        g₂ x ≠ (⊤ : EReal) :=
      helperForCorollary_26_3_2_finite_of_mem_subdifferentialEffectiveDomain hg₂_proper hxRight
    have hxLeftBot : g₁ x ≠ (⊥ : EReal) := hg₁_proper.2.2 x (by simp)
    have hxRightBot : g₂ x ≠ (⊥ : EReal) := hg₂_proper.2.2 x (by simp)
    simpa [Pi.add_apply, EReal.toReal_add hxLeftTop hxLeftBot hxRightTop hxRightBot]
  -- Strict convexity of `g₁` survives addition of the convex real-valued restriction of `g₂`.
  exact (hStrictLeft.add_convexOn hConvRight).congr hEqOn.symm

/-- Helper for Corollary 26.3.2: the pointwise sum `f₁* + f₂*` is essentially strictly convex. -/
lemma helperForCorollary_26_3_2_essentiallyStrictlyConvex_conjugateSum
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₁)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₂)
    (hf₁_smooth : IsEssentiallySmooth f₁)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂)))) :
    IsEssentiallyStrictlyConvex
      (fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x) := by
  let gTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases (fenchelConjugate n f₁) (fun _ => fenchelConjugate n f₂) i
  have hf₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁
  have hf₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₂) hf₂
  have hgTwo_proper :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (gTwo i) := by
    intro i
    fin_cases i
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
    · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper)
  have hsumProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x) := by
    -- The common relative-interior witness supplies the qualification for properness of the sum.
    have hriWitness :=
      helperForCorollary_26_3_2_commonRelativeInterior_twoConjugates (f₁ := f₁) (f₂ := f₂) hri
    simpa [gTwo, Fin.sum_univ_two] using
      (helperForTheorem_23_8_sum_proper_of_qualification gTwo hgTwo_proper Set.univ (Or.inl hriWitness))
  refine ⟨hsumProper, ?_⟩
  intro C hCSubset hCConv
  -- The previous helper isolates the strict-convexity-on-domain argument.
  exact
    helperForCorollary_26_3_2_strictConvexOn_conjugateSum_subdifferentialEffectiveDomain
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₁_closed hf₂ hf₁_smooth hri hCSubset hCConv

end Section26
end Chap05
