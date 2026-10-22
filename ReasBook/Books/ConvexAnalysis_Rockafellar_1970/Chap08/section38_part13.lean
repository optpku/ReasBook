/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Corollary 38.5.1: the Chapter 38 book-style closure is monotone. The only extra
case split is the exceptional branch where the smaller function already takes the value `⊥`,
forcing its closure to collapse to the constant `⊥` function. -/
lemma helperForCorollary_38_5_1_erealFunctionClosure_mono
    {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hfg : f ≤ g) :
    erealFunctionClosure f ≤ erealFunctionClosure g := by
  intro x
  unfold erealFunctionClosure
  by_cases hfNoBot : ∀ z : X, f z ≠ (⊥ : EReal)
  · have hgNoBot : ∀ z : X, g z ≠ (⊥ : EReal) := by
      intro z hzBot
      apply hfNoBot z
      exact le_bot_iff.mp <| by simpa [hzBot] using hfg z
    -- In the non-`⊥` branch, monotonicity is exactly the hull monotonicity proved above.
    simpa [hfNoBot, hgNoBot] using
      helperForCorollary_38_5_1_erealLowerSemicontinuousHull_mono
        (f := f) (g := g) hfg x
  · -- If `f` already hits `⊥`, its closure is constant `⊥`, so the comparison is immediate.
    split_ifs <;> simp

/-- Helper for Corollary 38.5.1: the Chapter 38 bifunction closure is monotone with respect to
pointwise order. This packages the product-space monotonicity of `erealFunctionClosure` back into
curried bifunction form. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_mono
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    {K₁ K₂ : U → X → EReal} (h₁₂ : K₁ ≤ K₂) :
    bifunctionClosure K₁ ≤ bifunctionClosure K₂ := by
  intro u x
  -- View both bifunctions as functions on the product and apply function-level monotonicity.
  simpa [bifunctionClosure] using
    helperForCorollary_38_5_1_erealFunctionClosure_mono
      (f := fun p : U × X => K₁ p.1 p.2)
      (g := fun p : U × X => K₂ p.1 p.2)
      (fun p => h₁₂ p.1 p.2) (u, x)

/-- Helper for Corollary 38.5.1: the raw lower-semicontinuous hull already fixes any
lower-semicontinuous function, so later closure comparisons can isolate the exceptional `⊥`
branch of `erealFunctionClosure` instead of re-proving hull maximality each time. -/
lemma helperForCorollary_38_5_1_erealLowerSemicontinuousHull_eq_of_lsc
    {X : Type*} [TopologicalSpace X] {f : X → EReal}
    (hf_lsc : LowerSemicontinuous f) :
    erealLowerSemicontinuousHull f = f := by
  funext x
  apply le_antisymm
  · -- Every admissible lower-semicontinuous minorant in the hull is pointwise below `f`.
    rw [erealLowerSemicontinuousHull]
    refine iSup_le ?_
    intro h
    exact h.2.2 x
  · -- The function itself is one admissible hull candidate.
    rw [erealLowerSemicontinuousHull]
    exact le_iSup_of_le ⟨f, hf_lsc, le_rfl⟩ le_rfl

/-- Helper for Corollary 38.5.1: once a function is already lower semicontinuous and never
attains `⊥`, the Chapter 38 book-style closure leaves it unchanged. -/
lemma helperForCorollary_38_5_1_erealFunctionClosure_eq_of_lsc_of_no_bot
    {X : Type*} [TopologicalSpace X] {f : X → EReal}
    (hf_lsc : LowerSemicontinuous f)
    (hf_noBot : ∀ x : X, f x ≠ (⊥ : EReal)) :
    erealFunctionClosure f = f := by
  -- Collapse the non-`⊥` branch to the raw lower-semicontinuous hull and then use the previous
  -- hull fixed-point lemma.
  unfold erealFunctionClosure
  simp [hf_noBot,
    helperForCorollary_38_5_1_erealLowerSemicontinuousHull_eq_of_lsc (f := f) hf_lsc]

/-- Helper for Corollary 38.5.1: a bifunction that is already lower semicontinuous on the product
and never takes the value `⊥` is fixed by the Chapter 38 closure operator. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_eq_of_productLowerSemicontinuous_of_no_bot
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U → X → EReal}
    (hK_lsc : IsProductLowerSemicontinuousBifunction K)
    (hK_noBot : ∀ u : U, ∀ x : X, K u x ≠ (⊥ : EReal)) :
    bifunctionClosure K = K := by
  funext u x
  -- Repackage the bifunction as a function on the product and apply the function-level
  -- fixed-point lemma there.
  have hClosure :
      erealFunctionClosure (fun p : U × X => K p.1 p.2) =
        (fun p : U × X => K p.1 p.2) :=
    helperForCorollary_38_5_1_erealFunctionClosure_eq_of_lsc_of_no_bot
      (f := fun p : U × X => K p.1 p.2) hK_lsc
      (fun p => hK_noBot p.1 p.2)
  simpa [bifunctionClosure] using congrFun hClosure (u, x)


/-- Helper for Corollary 38.5.1: the Chapter 38 closure is the maximal lower-semicontinuous
minorant once the raw bifunction never takes the value `⊥`. This is the exact reverse-comparison
principle needed at the end of Corollary 38.5.1 after all domain/ri transport has been reduced to
a global minorant statement. -/
lemma helperForCorollary_38_5_1_le_erealFunctionClosure_of_lowerSemicontinuous_of_le_of_no_bot
    {X : Type*} [TopologicalSpace X] {h f : X → EReal}
    (hh_lsc : LowerSemicontinuous h)
    (hhf : h ≤ f)
    (hf_noBot : ∀ x : X, f x ≠ (⊥ : EReal)) :
    h ≤ erealFunctionClosure f := by
  intro x
  unfold erealFunctionClosure
  simp [hf_noBot]
  exact le_iSup_of_le ⟨h, ⟨hh_lsc, hhf⟩⟩ le_rfl

/-- Helper for Corollary 38.5.1: curried back to bifunctions, any product-lower-semicontinuous
minorant of a nowhere-`⊥` bifunction lies below its Chapter 38 closure. This packages the
closure-uniqueness direction separately from the remaining operator transport. -/
lemma helperForCorollary_38_5_1_le_bifunctionClosure_of_productLowerSemicontinuous_of_le_of_no_bot
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {H K : U → X → EReal}
    (hH_lsc : IsProductLowerSemicontinuousBifunction H)
    (hHK : H ≤ K)
    (hK_noBot : ∀ u : U, ∀ x : X, K u x ≠ (⊥ : EReal)) :
    H ≤ bifunctionClosure K := by
  intro u x
  have hProdLe :
      (fun p : U × X => H p.1 p.2) ≤ fun p : U × X => K p.1 p.2 := by
    intro p
    exact hHK p.1 p.2
  have hProdNoBot :
      ∀ p : U × X, (fun q : U × X => K q.1 q.2) p ≠ (⊥ : EReal) := by
    intro p
    exact hK_noBot p.1 p.2
  simpa [bifunctionClosure] using
    helperForCorollary_38_5_1_le_erealFunctionClosure_of_lowerSemicontinuous_of_le_of_no_bot
      (h := fun p : U × X => H p.1 p.2)
      (f := fun p : U × X => K p.1 p.2)
      hH_lsc hProdLe hProdNoBot (u, x)

/-- Helper for Corollary 38.5.1: once the packaged adjoint of `GF` is known to be Chapter-38
product lower semicontinuous and nowhere `⊥`, the Chapter 38 closure operator fixes it as well.
This isolates the closure-uniqueness half of the final bridge from the remaining domain/ri
transport work. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_bifunctionClosure_eq_self_of_productLowerSemicontinuous_of_no_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hAcomp_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≠ (⊥ : EReal)) :
    bifunctionClosure
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  exact
    helperForCorollary_38_5_1_bifunctionClosure_eq_of_productLowerSemicontinuous_of_no_bot
      (hK_lsc := hAcomp_lsc) (hK_noBot := hAcomp_noBot)

/-- Helper for Corollary 38.5.1: once the remaining operator transport has been sharpened to a
Chapter 38 product-lower-semicontinuous minorant statement for the closed packaged adjoint, the
reverse comparison `(GF)^* ≤ cl (F^* G^*)` is immediate from the maximality of
`bifunctionClosure`. This isolates the last missing inputs to a pure transport problem. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_lsc_minorant
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hMinorant :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ ≤
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u))
    (hKpkg_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠ (⊥ : EReal)) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
        bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u := by
  exact
    helperForCorollary_38_5_1_le_bifunctionClosure_of_productLowerSemicontinuous_of_le_of_no_bot
      (H := adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩)
      (K := fun y u =>
        ⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u)
      hAcomp_lsc hMinorant hKpkg_noBot

/-- Helper for Corollary 38.5.1: under the original theorem-38.5 primal qualification hypothesis,
the raw reverse inequality `(GF)^* ≤ F^* G^*` is already available in packaged coordinates. So
once the remaining Chapter 38 inputs are upgraded to product lower semicontinuity of `(GF)^*` and
global non-`⊥` for `F^* G^*`, the reverse closure comparison follows immediately. This packages
the theorem-local part of the argument separately from the corollary-level transport still missing
in the file. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_no_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hTheoremHri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hKpkg_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠ (⊥ : EReal)) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
        bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u := by
  have hMinorant :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ ≤
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
    intro y u
    exact
      helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSup_of_theorem_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hTheoremHri) (y := y) (u := u)
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_lsc_minorant
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hAcomp_lsc := hAcomp_lsc)
      (hMinorant := hMinorant) (hKpkg_noBot := hKpkg_noBot)

/-- Helper for Corollary 38.5.1: under the original theorem-38.5 primal qualification
hypothesis, the Chapter 38 closure identity also follows as soon as the packaged adjoint `(GF)^*`
is known to be product lower semicontinuous and the packaged supremal composition `F^* G^*`
avoids `⊥` everywhere. This isolates the remaining transport gap to exactly those two Chapter 38
inputs. -/
lemma helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose_of_theorem_hri_of_lsc_of_no_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hTheoremHri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hKpkg_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠ (⊥ : EReal)) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  apply le_antisymm
  · intro y u
    have hRawEq :=
      helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hTheoremHri)
    calc
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u ≤
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u :=
        helperForCorollary_38_5_1_bifunctionClosure_le
          (K := fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u
      _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
        simpa using congrFun (congrFun hRawEq y) u
  · intro y u
    exact
      helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_no_bot
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hTheoremHri := hTheoremHri)
        (hAcomp_lsc := hAcomp_lsc) (hKpkg_noBot := hKpkg_noBot) (y := y) (u := u)


/-- Helper for Corollary 38.5.1: the theorem-local reverse Chapter 38 comparison can also be
packaged using a nowhere-`⊥` hypothesis on the closed packaged adjoint `(GF)^*` itself. Under the
raw theorem-38.5 identity, that immediately transfers to the packaged supremal composition
`F^* G^*`, so the remaining side conditions stay attached to the operator one actually wants to
identify with the closure. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_Acomp_no_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hTheoremHri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hAcomp_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≠ (⊥ : EReal)) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
        bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u := by
  have hRawEq :=
    helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hTheoremHri)
  have hKpkg_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠ (⊥ : EReal) := by
    intro y u hBot
    have hEq_point :
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
          adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
      simpa using congrFun (congrFun hRawEq y) u
    exact hAcomp_noBot y u (hEq_point.symm.trans hBot)
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_no_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hTheoremHri := hTheoremHri)
      (hAcomp_lsc := hAcomp_lsc) (hKpkg_noBot := hKpkg_noBot)

/-- Helper for Corollary 38.5.1: likewise, once theorem-38.5 gives the raw packaged identity,
a nowhere-`⊥` hypothesis on the packaged adjoint `(GF)^*` is enough to upgrade the whole theorem-local
Chapter 38 closure equality. This is the version whose side conditions now live entirely on the
adjoint side. -/
lemma helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose_of_theorem_hri_of_lsc_of_Acomp_no_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hTheoremHri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hAcomp_lsc :
      IsProductLowerSemicontinuousBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩))
    (hAcomp_noBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≠ (⊥ : EReal)) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  apply le_antisymm
  · intro y u
    have hRawEq :=
      helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hTheoremHri)
    calc
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u ≤
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u :=
        helperForCorollary_38_5_1_bifunctionClosure_le
          (K := fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u
      _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
        simpa using congrFun (congrFun hRawEq y) u
  · intro y u
    exact
      helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_Acomp_no_bot
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hTheoremHri := hTheoremHri)
        (hAcomp_lsc := hAcomp_lsc) (hAcomp_noBot := hAcomp_noBot) (y := y) (u := u)

/-- Helper for Corollary 38.5.1: weak duality already gives the raw packaged inequality
`F^* G^* ≤ (GF)^*` in Chapter 6 coordinates. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_le_packagedAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≤
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
  -- First rewrite the packaged supremal composition back into the current Chapter 38 coordinates.
  calc
    (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        (dotProductEquiv ℝ (Fin p) (-y))
        (dotProductEquiv ℝ (Fin m) (-u)) := by
          symm
          exact
            helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
              (F := F) (G := G)
              (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
              (y := y) (u := u)
    _ ≤ bifunctionAdjoint (bifunctionCompose G F)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) :=
        helperForTheorem_38_5_composeSupGeneric_le_adjoint_compose
          (F := F) (G := G)
          (yStar := dotProductEquiv ℝ (Fin p) (-y))
          (uStar := dotProductEquiv ℝ (Fin m) (-u))
    _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
          -- Finally return to the packaged Chapter 6 adjoint coordinates for the composed
          -- bifunction.
          symm
          exact
            congrFun
              (congrFun
                (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                  (F := bifunctionCompose G F) hComposeConvex)
                y)
              u

/-- Helper for Corollary 38.5.1: combining closure-below-self with weak duality yields the easy
half `cl (F^* G^*) ≤ (GF)^*` in packaged coordinates. -/
lemma helperForCorollary_38_5_1_packagedComposeSupClosure_le_packagedAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u ≤
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
  let Kpkg : (Fin p → ℝ) → (Fin m → ℝ) → EReal := fun y u =>
    ⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u
  let Acomp : (Fin p → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩
  have hRaw : Kpkg ≤ Acomp := by
    intro y u
    -- Weak duality is exactly the raw packaged comparison `F^* G^* ≤ (GF)^*`.
    simpa [Kpkg, Acomp] using
      helperForCorollary_38_5_1_packagedComposeSup_le_packagedAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) y u
  have hClosureMono : bifunctionClosure Kpkg ≤ bifunctionClosure Acomp :=
    -- Apply the new closure monotonicity theorem to the raw weak-duality inequality.
    helperForCorollary_38_5_1_bifunctionClosure_mono hRaw
  calc
    bifunctionClosure Kpkg y u ≤ bifunctionClosure Acomp y u := hClosureMono y u
    _ ≤ Acomp y u := helperForCorollary_38_5_1_bifunctionClosure_le Acomp y u

/-- Helper for Corollary 38.5.1: any value that lies above a non-`⊥` value must itself avoid
`⊥`. This is the exact order-theoretic step used to pass from `F^* G^*` to `(GF)^*` via weak
duality. -/
lemma helperForCorollary_38_5_1_ne_bot_of_le_of_ne_bot {a b : EReal}
    (hLe : a ≤ b) (ha_ne_bot : a ≠ (⊥ : EReal)) :
    b ≠ (⊥ : EReal) := by
  intro hb
  have hLeBot : a ≤ (⊥ : EReal) := by
    -- Substituting `b = ⊥` into the comparison would force the lower value down to `⊥`.
    simpa [hb] using hLe
  exact ha_ne_bot (bot_unique hLeBot)

/-- Helper for Corollary 38.5.1: weak duality transports any packaged non-`⊥` witness for
`F^* G^*` directly to a packaged non-`⊥` witness for `(GF)^*` at the same dual pair. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_packagedComposeSup_ne_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    {yStarVec : Fin p → ℝ} {uStarVec : Fin m → ℝ}
    (hKpkg_ne_bot :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) ≠
        (⊥ : EReal)) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
      (⊥ : EReal) := by
  have hLe :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) ≤
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec := by
    -- This is exactly the packaged weak-duality inequality already proved above.
    simpa using
      helperForCorollary_38_5_1_packagedComposeSup_le_packagedAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) yStarVec uStarVec
  -- Push the non-`⊥` witness through the order comparison.
  exact helperForCorollary_38_5_1_ne_bot_of_le_of_ne_bot hLe hKpkg_ne_bot

/-- Helper for Corollary 38.5.1: the same transported qualification witness already forces the
packaged adjoint of `GF` to be non-`⊥` at some point, because weak duality puts `F^* G^*` below
`(GF)^*`. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_transported_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hTransportedHri :
      (intrinsicInterior ℝ
            (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty) :
    ∃ yStarVec : Fin p → ℝ, ∃ uStarVec : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊥ : EReal) := by
  rcases
      helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_transported_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        hTransportedHri with
    ⟨yStarVec, uStarVec, hKpkg_ne_bot⟩
  refine ⟨yStarVec, uStarVec, ?_⟩
  -- The transported dual witness survives after passing from `F^* G^*` to `(GF)^*`.
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_packagedComposeSup_ne_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) hKpkg_ne_bot

/-- Helper for Corollary 38.5.1: the original Chapter 38 qualification hypothesis already
provides a packaged `(GF)^*` value that is not `⊥`, once transported through the signed
Euclidean/dual identification. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    ∃ yStarVec : Fin p → ℝ, ∃ uStarVec : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊥ : EReal) := by
  rcases
      helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri with
    ⟨yStarVec, uStarVec, hKpkg_ne_bot⟩
  refine ⟨yStarVec, uStarVec, ?_⟩
  -- The original Chapter 38 witness is the same packaged witness after the signed transport.
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_packagedComposeSup_ne_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) hKpkg_ne_bot

/-- Helper for Corollary 38.5.1: once a bifunction takes the value `⊥` somewhere, the Chapter 38
closure definition immediately collapses to the constant `⊥` branch on the whole product. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_eq_const_bot_of_exists_bot
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U → X → EReal}
    (hBot : ∃ u : U, ∃ x : X, K u x = (⊥ : EReal)) :
    bifunctionClosure K = fun _ _ => (⊥ : EReal) := by
  rcases hBot with ⟨u₀, x₀, hBot⟩
  have hNotNoBot : ¬ ∀ p : U × X, K p.1 p.2 ≠ (⊥ : EReal) := by
    -- The exhibited bottom value falsifies the universal guard in `erealFunctionClosure`.
    intro hNoBot
    exact (hNoBot (u₀, x₀)) hBot
  funext u x
  -- Unfold the closure and select the constant-`⊥` branch forced by the witness.
  unfold bifunctionClosure erealFunctionClosure
  rw [if_neg hNotNoBot]

/-- Helper for Corollary 38.5.1: any reverse inequality `(GF)^* ≤ cl (F^* G^*)`, together with
the qualification-produced non-`⊥` witness for `(GF)^*`, would already force the packaged dual
composition `F^* G^*` to avoid `⊥` everywhere. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_global_no_bot_of_reverseClosureComparison
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hReverse :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠
        (⊥ : EReal) := by
  intro y u hKpkgBot
  rcases
      helperForCorollary_38_5_1_packagedAdjointCompose_ne_bot_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) hri with
    ⟨y₀, u₀, hAcomp_ne_bot⟩
  have hClosureBot :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        fun _ _ => (⊥ : EReal) :=
    helperForCorollary_38_5_1_bifunctionClosure_eq_const_bot_of_exists_bot
      (K := fun y u =>
        ⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u)
      ⟨y, u, hKpkgBot⟩
  have hAcomp_le_bot :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y₀ u₀ ≤ (⊥ : EReal) := by
    -- The claimed reverse inequality would evaluate into the collapsed closure branch.
    simpa [hClosureBot] using hReverse y₀ u₀
  have hAcomp_bot :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y₀ u₀ =
        (⊥ : EReal) :=
    bot_unique hAcomp_le_bot
  exact hAcomp_ne_bot hAcomp_bot

/-- Helper for Corollary 38.5.1: if a dual output `y` lies outside the first effective domain of
`G^*`, then the whole packaged row of `F^* G^*` at that `y` is already identically `⊥`. This
extracts the first concrete way in which the Chapter 38 closure can collapse to its bad constant-
`⊥` branch. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_eq_bot_of_not_mem_leftDomBot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {y : Fin p → ℝ}
    (hy :
      y ∉ bifunctionDomBot (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))
    (u : Fin m → ℝ) :
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) = (⊥ : EReal) := by
  have hyBot :
      ∀ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x = (⊥ : EReal) := by
    intro x
    by_contra hne
    exact hy ⟨x, hne⟩
  -- Every summand already contains the left `⊥` factor forced by the missing `G^*` domain point.
  calc
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        ⨆ x : Fin n → ℝ, (⊥ : EReal) := by
          refine iSup_congr ?_
          intro x
          rw [hyBot x, EReal.bot_add]
    _ = (⊥ : EReal) := by simp

/-- Helper for Corollary 38.5.1: if a dual input `u` lies outside the effective domain of
`F^*_ *`, then the whole packaged column of `F^* G^*` at that `u` is identically `⊥`. This is the
second concrete obstruction to any reverse comparison into `bifunctionClosure`. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_eq_bot_of_not_mem_rightDom
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {u : Fin m → ℝ}
    (hu :
      u ∉ bifunctionDom
        (bifunctionInverse
          (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)))
    (y : Fin p → ℝ) :
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) = (⊥ : EReal) := by
  have huBot :
      ∀ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u = (⊥ : EReal) := by
    intro x
    by_contra hne
    apply hu
    rw [helperForCorollary_38_5_1_bifunctionDom_inverse_eq_exists_ne_bot]
    exact ⟨x, hne⟩
  -- Here every summand collapses because the right `F^*_ *` domain point is missing.
  calc
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        ⨆ x : Fin n → ℝ, (⊥ : EReal) := by
          refine iSup_congr ?_
          intro x
          rw [huBot x, EReal.add_bot]
    _ = (⊥ : EReal) := by simp

/-- Helper for Corollary 38.5.1: any completed reverse comparison would force every dual output to
belong to `dom G^*`, because missing one such point would make the corresponding entire row of
`F^* G^*` equal `⊥` and hence contradict the already isolated bad-branch obstruction. -/
lemma helperForCorollary_38_5_1_reverseClosureComparison_forces_leftDomain_full
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hReverse :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) :
    ∀ y : Fin p → ℝ,
      y ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) := by
  intro y
  have hGlobalNoBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠
          (⊥ : EReal) :=
    helperForCorollary_38_5_1_packagedComposeSup_global_no_bot_of_reverseClosureComparison
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri) hReverse
  by_contra hy
  have hBot :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x (0 : Fin m → ℝ)) =
        (⊥ : EReal) :=
    helperForCorollary_38_5_1_packagedComposeSup_eq_bot_of_not_mem_leftDomBot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      hy (u := 0)
  exact (hGlobalNoBot y 0) hBot

/-- Helper for Corollary 38.5.1: any completed reverse comparison would also force every dual
input to belong to `dom (F^*_ *)`, because otherwise the corresponding entire column of `F^* G^*`
would be `⊥` and the same Chapter 38 bad branch would reappear. -/
lemma helperForCorollary_38_5_1_reverseClosureComparison_forces_rightDomain_full
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hReverse :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) :
    ∀ u : Fin m → ℝ,
      u ∈ bifunctionDom
        (bifunctionInverse
          (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) := by
  intro u
  have hGlobalNoBot :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≠
          (⊥ : EReal) :=
    helperForCorollary_38_5_1_packagedComposeSup_global_no_bot_of_reverseClosureComparison
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri) hReverse
  by_contra hu
  have hBot :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ (0 : Fin p → ℝ) x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        (⊥ : EReal) :=
    helperForCorollary_38_5_1_packagedComposeSup_eq_bot_of_not_mem_rightDom
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      hu (y := 0)
  exact (hGlobalNoBot 0 u) hBot

/-- Helper for Corollary 38.5.1: any completed reverse comparison would force both packaged dual
effective domains to be full. This packages the two one-sided obstructions into the exact global
domain consequence that any valid Chapter 38 transport theorem would have to supply upstream. -/
lemma helperForCorollary_38_5_1_reverseClosureComparison_forces_full_domains
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hReverse :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) :
    (∀ y : Fin p → ℝ,
        y ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) ∧
      (∀ u : Fin m → ℝ,
        u ∈ bifunctionDom
          (bifunctionInverse
            (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩))) := by
  constructor
  · -- The left-domain obstruction was isolated just above.
    exact
      helperForCorollary_38_5_1_reverseClosureComparison_forces_leftDomain_full
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) hReverse
  · -- The right-domain obstruction is the symmetric columnwise statement.
    exact
      helperForCorollary_38_5_1_reverseClosureComparison_forces_rightDomain_full
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) hReverse

/-- Helper for Corollary 38.5.1: any completed reverse comparison would already force the
current Chapter 38 dual domains of the reversed packaged composition to be full, not just their
packaged Chapter 6 coordinate images. This rewrites the obstruction theorem back in current
notation, but with the roles swapped exactly as they arise from the packaged `(y,u)` variables:
full `dom G^*` on the left and full `dom F^*_ *` on the right. -/
lemma helperForCorollary_38_5_1_reverseClosureComparison_forces_full_currentSwappedDualDomains
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hReverse :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) :
    (∀ yStar : Module.Dual ℝ (Fin p → ℝ),
        yStar ∈ bifunctionDomBot (bifunctionAdjoint G.toFun)) ∧
      (∀ uStar : Module.Dual ℝ (Fin m → ℝ),
        uStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint F.toFun))) := by
  rcases
      helperForCorollary_38_5_1_reverseClosureComparison_forces_full_domains
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) hReverse with
    ⟨hLeftPkg, hRightPkg⟩
  constructor
  · exact
      helperForCorollary_38_5_1_full_currentDual_leftDomain_of_full_packagedDomain
        (F := G) (hF_properConvex := hG_properConvex) hLeftPkg
  · exact
      helperForCorollary_38_5_1_full_currentDual_rightDomain_of_full_packagedDomain
        (G := F) (hG_properConvex := hF_properConvex) hRightPkg

/-- Helper for Corollary 38.5.1: if the two current Chapter 38 dual effective domains are already
known to be full, then the corollary's dual relative-interior qualification is automatic. This
isolates the exact upstream full-domain theorem still missing from the final reverse-closure
comparison. -/
lemma helperForCorollary_38_5_1_hri_of_full_currentDualDomains
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hLeftFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDomBot (bifunctionAdjoint F.toFun))
    (hRightFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun))) :
    (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
      intrinsicInterior ℝ
        (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty := by
  have hLeftEqUniv : bifunctionDomBot (bifunctionAdjoint F.toFun) = Set.univ := by
    ext xStar
    constructor
    · intro _
      simp
    · intro _
      exact hLeftFull xStar
  have hRightEqUniv :
      bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)) = Set.univ := by
    ext xStar
    constructor
    · intro _
      simp
    · intro _
      exact hRightFull xStar
  refine ⟨0, ?_, ?_⟩
  · rw [hLeftEqUniv]
    exact
      interior_subset_intrinsicInterior
        (s := (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ)))) (by simp [interior_univ])
  · rw [hRightEqUniv]
    exact
      interior_subset_intrinsicInterior
        (s := (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ)))) (by simp [interior_univ])

lemma helperForCorollary_38_5_1_not_reverseClosureComparison_of_packagedComposeSup_exists_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (hKpkgBot :
      ∃ y : Fin p → ℝ, ∃ u : Fin m → ℝ,
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
          (⊥ : EReal)) :
    ¬ (∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
          bifunctionClosure
            (fun y u =>
              ⨆ x : Fin n → ℝ,
                adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u) := by
  intro hReverse
  rcases hKpkgBot with ⟨y, u, hBot⟩
  -- Any completed reverse comparison would force the packaged dual composition to avoid `⊥`
  -- everywhere, contradicting the exhibited bad point.
  exact
    (helperForCorollary_38_5_1_packagedComposeSup_global_no_bot_of_reverseClosureComparison
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri) hReverse y u) hBot



end Section38
end Chap08
