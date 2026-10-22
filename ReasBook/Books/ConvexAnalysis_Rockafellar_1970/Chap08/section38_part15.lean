/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part14

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/- Legacy transport through the generic lower closure. The source corollary uses the concave
upper closure; the corrected packaged proof follows after this commented block. -/
/-
/-- Helper for Corollary 38.5.1: evaluating the packaged adjoint of `GF` at the canonical signed
preimage of a dual pair recovers the current-coordinate adjoint `(GF)^*`. -/
lemma helperForCorollary_38_5_1_signedPreimage_packagedAdjointCompose_eq_currentAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩
        (-((dotProductEquiv ℝ (Fin p)).symm yStar))
        (-((dotProductEquiv ℝ (Fin m)).symm uStar)) =
      bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
  -- Evaluate the signed transport formula at the canonical preimage of the current dual pair.
  simpa using
    congrFun
      (congrFun
        (helperForCorollary_38_5_1_currentAdjointCompose_eq_packagedAdjointCompose_under_signedHomeomorph
          (F := F) (G := G) (hComposeConvex := hComposeConvex))
        (-((dotProductEquiv ℝ (Fin p)).symm yStar)))
      (-((dotProductEquiv ℝ (Fin m)).symm uStar))

/-- Helper for Corollary 38.5.1: evaluating the packaged supremal composition `F^* G^*` at the
canonical signed preimage of a dual pair recovers its current-coordinate form. -/
lemma helperForCorollary_38_5_1_signedPreimage_packagedComposeSup_eq_currentComposeSup
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩
          (-((dotProductEquiv ℝ (Fin p)).symm yStar)) x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x
          (-((dotProductEquiv ℝ (Fin m)).symm uStar))) =
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar := by
  -- Evaluate the packaged-to-current transport at the same signed preimage as above.
  simpa using
    (helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (y := -((dotProductEquiv ℝ (Fin p)).symm yStar))
      (u := -((dotProductEquiv ℝ (Fin m)).symm uStar))).symm

/-- Helper for Corollary 38.5.1: the packaged lower closure of `F^* G^*`, evaluated at the
canonical signed preimage of a dual pair, matches the current-coordinate lower closure. -/
lemma helperForCorollary_38_5_1_signedPreimage_packagedClosureComposeSup_eq_currentClosureComposeSup
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u)
        (-((dotProductEquiv ℝ (Fin p)).symm yStar))
        (-((dotProductEquiv ℝ (Fin m)).symm uStar)) =
      bifunctionClosure
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
        yStar uStar := by
  -- The closure transport uses the same signed Euclidean/dual identification pointwise.
  simpa using
    congrFun
      (congrFun
        (helperForCorollary_38_5_1_currentClosureComposeSup_eq_packagedClosure_under_signedHomeomorph
          (F := F) (G := G)
          (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex))
        (-((dotProductEquiv ℝ (Fin p)).symm yStar)))
      (-((dotProductEquiv ℝ (Fin m)).symm uStar))

/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
reverse raw comparison also holds directly in the current Chapter 38 coordinates after transporting
the packaged theorem-local identity through the signed Euclidean/dual homeomorphism. This keeps
the theorem-local raw reverse inequality separate from the remaining corollary-level closure
transport. -/
lemma helperForCorollary_38_5_1_currentAdjointCompose_le_currentComposeSup_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar ≤
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar := by
  let y : Fin p → ℝ := -((dotProductEquiv ℝ (Fin p)).symm yStar)
  let u : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm uStar)
  have hPackaged :=
    helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSup_of_theorem_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri) (y := y) (u := u)
  have hCurrentAdjoint :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
    -- Evaluate the packaged adjoint transport at the chosen signed preimage.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedAdjointCompose_eq_currentAdjointCompose
        (F := F) (G := G) (hComposeConvex := hComposeConvex)
        (yStar := yStar) (uStar := uStar)
  have hCurrentSup :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
          yStar uStar := by
    -- Read the packaged supremal composition back in the current Chapter 38 coordinates.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedComposeSup_eq_currentComposeSup
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (yStar := yStar) (uStar := uStar)
  simpa [hCurrentAdjoint, hCurrentSup] using hPackaged

/-- Helper for Corollary 38.5.1: under the original theorem-38.5 primal qualification
hypothesis, the current Chapter 38 closure identity also follows once the packaged adjoint `(GF)^*`
is known to be product lower semicontinuous in packaged coordinates and the packaged supremal
composition `F^* G^*` avoids `⊥` everywhere. This is just the signed homeomorphism transport of the
preceding packaged theorem-local closure wrapper, recorded directly in current notation. -/
lemma helperForCorollary_38_5_1_currentClosureEquality_of_packagedClosureEquality
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hPackagedClosure :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) :
    bifunctionClosure
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) =
      bifunctionAdjoint (bifunctionCompose G F) := by
  funext yStar
  funext uStar
  let y : Fin p → ℝ := -((dotProductEquiv ℝ (Fin p)).symm yStar)
  let u : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm uStar)
  have hAtSigned := congrFun (congrFun hPackagedClosure y) u
  have hAdjointAtSigned :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
    -- The signed preimage was chosen so the packaged adjoint lands back on the original dual pair.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedAdjointCompose_eq_currentAdjointCompose
        (F := F) (G := G) (hComposeConvex := hComposeConvex)
        (yStar := yStar) (uStar := uStar)
  have hClosureAtSigned :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u =
        bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
          yStar uStar := by
    -- The same signed preimage converts the packaged closure value back to the current one.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedClosureComposeSup_eq_currentClosureComposeSup
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (yStar := yStar) (uStar := uStar)
  -- Compare the packaged equality at the signed preimage and rewrite both sides back to the
  -- current Chapter 38 coordinates.
  exact hClosureAtSigned.symm.trans hAtSigned |>.trans hAdjointAtSigned

/-- Helper for Corollary 38.5.1: under the original theorem-38.5 primal qualification
hypothesis, the current Chapter 38 closure identity also follows once the packaged adjoint `(GF)^*`
is known to be product lower semicontinuous in packaged coordinates and the packaged supremal
composition `F^* G^*` avoids `⊥` everywhere. This is just the signed homeomorphism transport of the
preceding packaged theorem-local closure wrapper, recorded directly in current notation. -/
lemma helperForCorollary_38_5_1_currentComposeSupClosure_eq_currentAdjointCompose_of_theorem_hri_of_lsc_of_no_bot
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
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) =
      bifunctionAdjoint (bifunctionCompose G F) := by
  have hPackagedClosure :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ :=
    helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose_of_theorem_hri_of_lsc_of_no_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hTheoremHri := hTheoremHri)
      (hAcomp_lsc := hAcomp_lsc) (hKpkg_noBot := hKpkg_noBot)
  -- Once the packaged closure equality is available, only the signed coordinate transport remains.
  exact
    helperForCorollary_38_5_1_currentClosureEquality_of_packagedClosureEquality
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hPackagedClosure := hPackagedClosure)

/-- Helper for Corollary 38.5.1: the current Chapter 38 closure identity can likewise be recorded
with the theorem-local side condition stated directly on the closed packaged adjoint `(GF)^*`, rather
than on the raw packaged supremal composition `F^* G^*`. This is just the signed-homeomorphism
transport of the preceding packaged wrapper. -/
lemma helperForCorollary_38_5_1_currentComposeSupClosure_eq_currentAdjointCompose_of_theorem_hri_of_lsc_of_Acomp_no_bot
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
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) =
      bifunctionAdjoint (bifunctionCompose G F) := by
  have hPackagedClosure :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ :=
    helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose_of_theorem_hri_of_lsc_of_Acomp_no_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hTheoremHri := hTheoremHri)
      (hAcomp_lsc := hAcomp_lsc) (hAcomp_noBot := hAcomp_noBot)
  -- The signed homeomorphism turns the packaged equality into the current-coordinate equality.
  exact
    helperForCorollary_38_5_1_currentClosureEquality_of_packagedClosureEquality
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hPackagedClosure := hPackagedClosure)

/-- Helper for Corollary 38.5.1: weak duality already gives the raw current-coordinate estimate
`F^* G^* ≤ (GF)^*`. This is just the packaged Chapter 6 weak-duality inequality rewritten through
the signed Euclidean/dual identification used throughout the corollary. -/
lemma helperForCorollary_38_5_1_currentComposeSup_le_currentAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar ≤
      bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
  let y : Fin p → ℝ := -((dotProductEquiv ℝ (Fin p)).symm yStar)
  let u : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm uStar)
  have hPackaged :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ≤
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
    -- The packaged Chapter 6 inequality is the usual weak-duality estimate for infimal
    -- composition before any closure operator is introduced.
    exact
      helperForCorollary_38_5_1_packagedComposeSup_le_packagedAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (y := y) (u := u)
  have hCurrentSup :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
          yStar uStar := by
    -- Read the packaged supremal composition back in the current Chapter 38 coordinates.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedComposeSup_eq_currentComposeSup
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (yStar := yStar) (uStar := uStar)
  have hCurrentAdjoint :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose G F) yStar uStar := by
    -- The packaged adjoint uses the same signed homeomorphism, so the two coordinate systems agree
    -- at the chosen preimage.
    simpa [y, u] using
      helperForCorollary_38_5_1_signedPreimage_packagedAdjointCompose_eq_currentAdjointCompose
        (F := F) (G := G) (hComposeConvex := hComposeConvex)
        (yStar := yStar) (uStar := uStar)
  -- Rewrite both sides of the packaged estimate back to the Chapter 38 current coordinates.
  rw [← hCurrentSup, ← hCurrentAdjoint]
  exact hPackaged

/-- Helper for Corollary 38.5.1: since `bifunctionClosure` is a lower-semicontinuous minorant of
the raw composition `F^* G^*`, the easy half of the corollary's final identity is already local:
`cl(F^* G^*) ≤ (GF)^*` in the current Chapter 38 coordinates. -/
lemma helperForCorollary_38_5_1_currentComposeSupClosure_le_currentAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F)) :
    bifunctionClosure
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) ≤
      bifunctionAdjoint (bifunctionCompose G F) := by
  intro yStar uStar
  calc
    bifunctionClosure
        (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
        yStar uStar ≤
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar :=
      helperForCorollary_38_5_1_bifunctionClosure_le
        (K := bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
        yStar uStar
    _ ≤ bifunctionAdjoint (bifunctionCompose G F) yStar uStar :=
      helperForCorollary_38_5_1_currentComposeSup_le_currentAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (yStar := yStar) (uStar := uStar)

/-- Helper for Corollary 38.5.1: once the relative-interior hypothesis is transported through the
Euclidean-dual identification, the reversed-dual theorem should deliver the closedness,
primal-attainment, and closure identity for `GF` in one package. -/
lemma helperForCorollary_38_5_1_reversedDual_bridge
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) ∧
      (∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y) ∧
      bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) := by
  have hClosed :
      IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) :=
    helperForCorollary_38_5_1_reversedDual_closedness
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hri
  have hAttained :
      ∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y :=
    helperForCorollary_38_5_1_reversedDual_attainment_to_primal_minimizer
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hri
  have hComposeConvex :
      ConvexBifunction (bifunctionCompose G F) := by
    -- The corollary only needs the convexity half of Theorem 38.5 to package the composed
    -- bifunction into the Chapter 6 adjoint framework.
    exact
      (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
        (F := F) (G := G) hF_properConvex hG_properConvex).1
  have hPackagedClosure :
      bifunctionClosure
          (fun y u =>
            ⨆ x : Fin n → ℝ,
              adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ :=
    helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) (hri := hri)
  have hCurrentClosureEq :
      bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) =
        bifunctionAdjoint (bifunctionCompose G F) :=
    helperForCorollary_38_5_1_currentClosureEquality_of_packagedClosureEquality
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hPackagedClosure := hPackagedClosure)
  refine ⟨hClosed, hAttained, ?_⟩
  -- The reversed-dual bridge already delivers the full closure identity; the corollary statement
  -- uses the opposite orientation of the transported equality.
  exact hCurrentClosureEq.symm

/-- Corollary 38.5.1: Let `F` be a closed proper convex bifunction from `ℝ^m` to `ℝ^n`, and let
`G` be a closed proper convex bifunction from `ℝ^n` to `ℝ^p`. If `ri (dom F^*)` and
`ri (dom G^*_*)` have a point in common, then `GF` is closed and the infimum in the definition of
`((GF)u)(y)` is always attained. Moreover, then `(GF)^* = cl (F^* G^*)`.

In Lean:
- `GF` is `bifunctionCompose G F`;
- closedness is `IsProductLowerSemicontinuousBifunction`;
- the book's proper convexity assumptions are recorded by
  `ProperConvexBifunction F.toFun` and `ProperConvexBifunction G.toFun`;
- `F^*` is `bifunctionAdjoint F.toFun`, so `dom F^*` is modeled using
  `bifunctionDomBot (bifunctionAdjoint F.toFun)`;
- `G^*_ *` is modeled as `(bifunctionAdjoint G.toFun)_* = bifunctionInverse (bifunctionAdjoint G.toFun)`,
  and its `dom` (for the relative-interior condition) is modeled using `bifunctionDom`;
- `F^* G^*` is `bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)`;
- `cl` is modeled by `bifunctionClosure` on the product of dual spaces (with the weak topology). -/
theorem corollary38_5_1_compose_closed_and_infimum_attained_and_adjoint_eq_closure
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) ∧
      (∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y) ∧
      bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)) :=
  by
    let _ := hF_properConvex
    let _ := hG_properConvex
    let _ := hF_closed
    let _ := hG_closed
    let _ := hri
    -- Route correction: the corollary-level proof in this file is only the final transport step.
    -- The packaged reverse closure comparison is isolated upstream in `section38_part14.lean`,
    -- so the local theorem correctly closes by invoking the reversed-dual bridge already built
    -- from those packaged inputs.
    -- Book route: use the reversed dual pair, then collapse the resulting biadjoints with the
    -- closed-proper Chapter 6 rewrites proved just above.
    exact
      helperForCorollary_38_5_1_reversedDual_bridge
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) hri

-/

/-- Local bridge used by Corollary 38.5.1.  This is stated here as well as upstream so that the
corollary does not depend on a stale transitive build artifact during chapter migration. -/
lemma helperForCorollary_38_5_1_textbookAdjoint_eq_packagedAdjoint
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : ConvexBifunction F) :
    textbookBifunctionAdjoint F = adjointOfConvexBifunction ⟨F, hF⟩ := by
  funext x u
  rw [textbookBifunctionAdjoint, adjointOfConvexBifunction, sInf_range,
    iInf_pair_eq_nested]

/-- Corollary 38.5.1 in the book's finite Euclidean coordinates.  Here `cl` is the
upper-semicontinuous concave closure of the supremal product of the two adjoints. -/
theorem corollary38_5_1_compose_closed_and_infimum_attained_and_adjoint_eq_concaveClosure
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) ∧
      (∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y) ∧
      textbookBifunctionAdjoint (bifunctionCompose G F) =
        concaveBifunctionClosure
          (bifunctionComposeSup (textbookBifunctionAdjoint F.toFun)
            (textbookBifunctionAdjoint G.toFun)) := by
  have hClosed :=
    helperForCorollary_38_5_1_reversedDual_closedness
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hri
  have hAttained :=
    helperForCorollary_38_5_1_reversedDual_attainment_to_primal_minimizer
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hri
  have hComposeConvex : ConvexBifunction (bifunctionCompose G F) :=
    (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
      (F := F) (G := G) hF_properConvex hG_properConvex).1
  have hPackaged :=
    helperForCorollary_38_5_1_packagedComposeSupConcaveClosure_eq_packagedAdjointCompose
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hri
  refine ⟨hClosed, hAttained, ?_⟩
  calc
    textbookBifunctionAdjoint (bifunctionCompose G F) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ :=
      helperForCorollary_38_5_1_textbookAdjoint_eq_packagedAdjoint
        (bifunctionCompose G F) hComposeConvex
    _ = concaveBifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := hPackaged.symm
    _ = concaveBifunctionClosure
        (bifunctionComposeSup (textbookBifunctionAdjoint F.toFun)
          (textbookBifunctionAdjoint G.toFun)) := by
      rw [helperForCorollary_38_5_1_textbookAdjoint_eq_packagedAdjoint F.toFun
          hF_properConvex.1,
        helperForCorollary_38_5_1_textbookAdjoint_eq_packagedAdjoint G.toFun
          hG_properConvex.1]
      rfl

/-- Infimum-based composition of raw bifunctions on general types:
`(G ⊙ F) u y = inf_x (F u x + G x y)`.

This uses `EReal`'s built-in addition. For the book's extended convention at indeterminate sums
(`⊤ + ⊥` interpreted as `⊤`, i.e. `∞ - ∞ = +∞`), use `bifunctionComposeInfBook`. -/
noncomputable def bifunctionComposeInfGeneric
    {U X Y : Type*} (G : X → Y → EReal) (F : U → X → EReal) : U → Y → EReal :=
  fun u y => ⨅ x : X, F u x + G x y

/-- Book convention for adding extended reals in this section: the indeterminate sum `⊤ + ⊥`
(equivalently `∞ - ∞`) is interpreted as `⊤` rather than using `EReal`'s built-in convention. -/
noncomputable def erealAddBook (a b : EReal) : EReal :=
  if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then ⊤ else a + b

/-- Infimum-based composition of bifunctions using the book convention `erealAddBook` to interpret
indeterminate sums (`⊤ + ⊥` and `⊥ + ⊤`) as `⊤`. -/
noncomputable def bifunctionComposeInfBook
    {U X Y : Type*} (G : X → Y → EReal) (F : U → X → EReal) : U → Y → EReal :=
  fun u y => ⨅ x : X, erealAddBook (F u x) (G x y)

/-- The graph-epigraph formulation of joint convexity used by the extended part of
Proposition 38.5.1.  Unlike the older arithmetic `IsConvexBifunction` predicate, this
continues to express the textbook notion when an improper bifunction takes both infinite
values and the book convention `∞ - ∞ = +∞` is in force. -/
def IsBookConvexBifunction {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsERealConvex (bifunctionGraphFunction F)

/-- A jointly convex bifunction, bundled using its graph epigraph. -/
abbrev BookConvexBifunction (m n : Nat) : Type :=
  {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsBookConvexBifunction F}

lemma helperForProposition_38_5_1_erealAddBook_top_left (a : EReal) :
    erealAddBook ⊤ a = ⊤ := by
  induction a using EReal.rec <;> simp [erealAddBook]

lemma helperForProposition_38_5_1_erealAddBook_top_right (a : EReal) :
    erealAddBook a ⊤ = ⊤ := by
  induction a using EReal.rec <;> simp [erealAddBook]

lemma helperForProposition_38_5_1_erealAddBook_bot_left (a : EReal) :
    erealAddBook ⊥ a = if a = ⊤ then ⊤ else ⊥ := by
  induction a using EReal.rec <;> simp [erealAddBook]

lemma helperForProposition_38_5_1_erealAddBook_assoc (a b c : EReal) :
    erealAddBook (erealAddBook a b) c = erealAddBook a (erealAddBook b c) := by
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    induction c using EReal.rec <;> simp [erealAddBook, add_assoc]
  all_goals exact EReal.add_ne_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)

lemma helperForProposition_38_5_1_erealAddBook_comm (a b : EReal) :
    erealAddBook a b = erealAddBook b a := by
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    simp [erealAddBook, add_comm]

noncomputable def helperForProposition_38_5_1_addRealOrderIso (r : ℝ) : EReal ≃o EReal where
  toFun x := (r : EReal) + x
  invFun x := ((-r : ℝ) : EReal) + x
  left_inv x := by
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x =>
        change ((-r : ℝ) : EReal) + (((r : ℝ) : EReal) + (x : EReal)) = (x : EReal)
        rw [← add_assoc, ← EReal.coe_add]
        norm_num
  right_inv x := by
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x =>
        change (r : EReal) + (((-r : ℝ) : EReal) + (x : EReal)) = (x : EReal)
        rw [← add_assoc, ← EReal.coe_add]
        norm_num
  map_rel_iff' {x y} := by
    constructor
    · intro h
      have h' := add_le_add_right h ((-r : ℝ) : EReal)
      have hx : ((-r : ℝ) : EReal) + ((r : EReal) + x) = x := by
        induction x using EReal.rec with
        | bot => simp
        | top => simp
        | coe x => rw [← add_assoc, ← EReal.coe_add]; norm_num
      have hy : ((-r : ℝ) : EReal) + ((r : EReal) + y) = y := by
        induction y using EReal.rec with
        | bot => simp
        | top => simp
        | coe y => rw [← add_assoc, ← EReal.coe_add]; norm_num
      change ((-r : ℝ) : EReal) + ((r : EReal) + x) ≤
        ((-r : ℝ) : EReal) + ((r : EReal) + y) at h'
      simpa only [hx, hy] using h'
    · intro h
      change (r : EReal) + x ≤ (r : EReal) + y
      exact add_le_add_right h (r : EReal)

lemma helperForProposition_38_5_1_erealAddBook_coe (r : ℝ) (a : EReal) :
    erealAddBook (r : EReal) a = (r : EReal) + a := by
  induction a using EReal.rec <;> simp [erealAddBook]

lemma helperForProposition_38_5_1_erealAddBook_iInf
    {I : Type*} [Nonempty I] (a : EReal) (f : I → EReal) :
    erealAddBook a (⨅ i, f i) = ⨅ i, erealAddBook a (f i) := by
  induction a using EReal.rec with
  | top => simp [helperForProposition_38_5_1_erealAddBook_top_left]
  | bot =>
      by_cases htop : (⨅ i, f i) = (⊤ : EReal)
      · have hall : ∀ i, f i = (⊤ : EReal) := by
          intro i
          exact top_unique (by simpa [htop] using (iInf_le f i))
        simp [hall, helperForProposition_38_5_1_erealAddBook_bot_left]
      · have hex : ∃ i, f i ≠ (⊤ : EReal) := by
          by_contra h
          push_neg at h
          exact htop (by simp [h])
        rcases hex with ⟨i, hi⟩
        apply le_antisymm
        · rw [helperForProposition_38_5_1_erealAddBook_bot_left, if_neg htop]
          exact bot_le
        · exact le_trans (iInf_le (fun j => erealAddBook ⊥ (f j)) i)
            (by simp [helperForProposition_38_5_1_erealAddBook_bot_left, hi])
  | coe r =>
      simp_rw [helperForProposition_38_5_1_erealAddBook_coe]
      exact (helperForProposition_38_5_1_addRealOrderIso r).map_iInf f

lemma helperForProposition_38_5_1_iInf_erealAddBook
    {I : Type*} [Nonempty I] (f : I → EReal) (a : EReal) :
    erealAddBook (⨅ i, f i) a = ⨅ i, erealAddBook (f i) a := by
  simpa [helperForProposition_38_5_1_erealAddBook_comm] using
    helperForProposition_38_5_1_erealAddBook_iInf a f

lemma helperForProposition_38_5_1_bookCompose_assoc
    {U X Y Z : Type*} [Nonempty X] [Nonempty Y]
    (F : U → X → EReal) (G : X → Y → EReal) (H : Y → Z → EReal) :
    bifunctionComposeInfBook H (bifunctionComposeInfBook G F) =
      bifunctionComposeInfBook (bifunctionComposeInfBook H G) F := by
  funext u z
  simp only [bifunctionComposeInfBook]
  simp_rw [helperForProposition_38_5_1_iInf_erealAddBook,
    helperForProposition_38_5_1_erealAddBook_iInf,
    helperForProposition_38_5_1_erealAddBook_assoc]
  rw [iInf_comm]

lemma helperForProposition_38_5_1_erealAddBook_eq_add_of_ne_bot
    {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    erealAddBook a b = a + b := by
  simp [erealAddBook, ha, hb]

lemma helperForProposition_38_5_1_bookCompose_eq_generic_of_no_bot
    {U X Y : Type*} (F : U → X → EReal) (G : X → Y → EReal)
    (hF : ∀ u x, F u x ≠ ⊥) (hG : ∀ x y, G x y ≠ ⊥) :
    bifunctionComposeInfBook G F = bifunctionComposeInfGeneric G F := by
  funext u y
  simp only [bifunctionComposeInfBook, bifunctionComposeInfGeneric]
  congr 1
  funext x
  exact helperForProposition_38_5_1_erealAddBook_eq_add_of_ne_bot (hF u x) (hG x y)

lemma helperForProposition_38_5_1_genericCompose_assoc_of_no_bot
    {U X Y Z : Type*} [Nonempty X] [Nonempty Y]
    (F : U → X → EReal) (G : X → Y → EReal) (H : Y → Z → EReal)
    (hF : ∀ u x, F u x ≠ ⊥) (hG : ∀ x y, G x y ≠ ⊥)
    (hH : ∀ y z, H y z ≠ ⊥)
    (hGF : ∀ u y, bifunctionComposeInfGeneric G F u y ≠ ⊥)
    (hHG : ∀ x z, bifunctionComposeInfGeneric H G x z ≠ ⊥) :
    bifunctionComposeInfGeneric H (bifunctionComposeInfGeneric G F) =
      bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H G) F := by
  have hBookFG : bifunctionComposeInfBook G F = bifunctionComposeInfGeneric G F :=
    helperForProposition_38_5_1_bookCompose_eq_generic_of_no_bot F G hF hG
  have hBookHG : bifunctionComposeInfBook H G = bifunctionComposeInfGeneric H G :=
    helperForProposition_38_5_1_bookCompose_eq_generic_of_no_bot G H hG hH
  calc
    bifunctionComposeInfGeneric H (bifunctionComposeInfGeneric G F) =
        bifunctionComposeInfBook H (bifunctionComposeInfGeneric G F) :=
      (helperForProposition_38_5_1_bookCompose_eq_generic_of_no_bot
        (bifunctionComposeInfGeneric G F) H hGF hH).symm
    _ = bifunctionComposeInfBook H (bifunctionComposeInfBook G F) := by rw [hBookFG]
    _ = bifunctionComposeInfBook (bifunctionComposeInfBook H G) F :=
      helperForProposition_38_5_1_bookCompose_assoc F G H
    _ = bifunctionComposeInfBook (bifunctionComposeInfGeneric H G) F := by rw [hBookHG]
    _ = bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H G) F :=
      helperForProposition_38_5_1_bookCompose_eq_generic_of_no_bot
        F (bifunctionComposeInfGeneric H G) hF hHG

lemma helperForProposition_38_5_1_erealAddBook_le_coe_iff
    (a b : EReal) (r : ℝ) :
    erealAddBook a b ≤ (r : EReal) ↔
      ∃ s t : ℝ, a ≤ (s : EReal) ∧ b ≤ (t : EReal) ∧ s + t ≤ r := by
  induction a using EReal.rec with
  | bot =>
      induction b using EReal.rec with
      | bot =>
          constructor
          · intro _; exact ⟨r, 0, bot_le, bot_le, by simp⟩
          · intro _; simp [erealAddBook]
      | coe b =>
          constructor
          · intro _; exact ⟨r - b, b, bot_le, le_rfl, by linarith⟩
          · intro _; simp [erealAddBook]
      | top => simp [erealAddBook]
  | coe a =>
      induction b using EReal.rec with
      | bot =>
          constructor
          · intro _; exact ⟨a, r - a, le_rfl, bot_le, by linarith⟩
          · intro _; simp [erealAddBook]
      | coe b =>
          simp only [erealAddBook, EReal.coe_ne_top, EReal.coe_ne_bot, and_false,
            or_self, if_false, EReal.coe_add, EReal.coe_le_coe_iff]
          constructor
          · intro h
            have h' : a + b ≤ r := by exact_mod_cast h
            exact ⟨a, b, le_rfl, le_rfl, h'⟩
          · rintro ⟨s, t, has, hbt, hst⟩
            exact_mod_cast (le_trans (add_le_add has hbt) hst)
      | top => simp [erealAddBook]
  | top =>
      induction b using EReal.rec <;> simp [erealAddBook]

lemma helperForProposition_38_5_1_isERealConvex_erealAddBook
    {X : Type*} [AddCommMonoid X] [Module ℝ X] {f g : X → EReal}
    (hf : IsERealConvex f) (hg : IsERealConvex g) :
    IsERealConvex (fun x => erealAddBook (f x) (g x)) := by
  intro p hp q hq a b ha hb hab
  rcases (helperForProposition_38_5_1_erealAddBook_le_coe_iff
      (f p.1) (g p.1) p.2).1 hp with ⟨pf, pg, hpf, hpg, hpSum⟩
  rcases (helperForProposition_38_5_1_erealAddBook_le_coe_iff
      (f q.1) (g q.1) q.2).1 hq with ⟨qf, qg, hqf, hqg, hqSum⟩
  have hfCombo := hf (show (p.1, pf) ∈ ERealEpigraph f from hpf)
    (show (q.1, qf) ∈ ERealEpigraph f from hqf) ha hb hab
  have hgCombo := hg (show (p.1, pg) ∈ ERealEpigraph g from hpg)
    (show (q.1, qg) ∈ ERealEpigraph g from hqg) ha hb hab
  apply (helperForProposition_38_5_1_erealAddBook_le_coe_iff _ _ _).2
  refine ⟨a * pf + b * qf, a * pg + b * qg, ?_, ?_, ?_⟩
  · simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hfCombo
  · simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hgCombo
  · dsimp
    nlinarith [mul_le_mul_of_nonneg_left hpSum ha, mul_le_mul_of_nonneg_left hqSum hb]

/-- Joint graph-epigraph convexity is preserved by the book-totalized composition.  The proof
packs `(x,u,y)`, adds the two lifted graph functions with `erealAddBook`, and eliminates `x` by
the linear-fiber infimum theorem. -/
lemma helperForProposition_38_5_1_bookCompose_isBookConvex
    {m n p : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (G : (Fin n → ℝ) → (Fin p → ℝ) → EReal)
    (hF : IsBookConvexBifunction F) (hG : IsBookConvexBifunction G) :
    IsBookConvexBifunction (bifunctionComposeInfBook G F) := by
  let packedFMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
          (projXLinearMap (n := n) (m := m + p) w)
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases <;>
          simp [projLamLinearMap, projXLinearMap, Fin.append_left, Fin.append_right]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases <;>
          simp [projLamLinearMap, projXLinearMap, Fin.append_left, Fin.append_right] }
  let packedGMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (n + p) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := n) (m := m + p) w)
          (projLamLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases <;>
          simp [projLamLinearMap, projXLinearMap, Fin.append_left, Fin.append_right]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases <;>
          simp [projLamLinearMap, projXLinearMap, Fin.append_left, Fin.append_right] }
  let objective : (Fin (n + (m + p)) → ℝ) → EReal := fun w =>
    erealAddBook (bifunctionGraphFunction F (packedFMap w))
      (bifunctionGraphFunction G (packedGMap w))
  have hFpre :
      IsERealConvex (fun w => bifunctionGraphFunction F (packedFMap w)) := by
    have h := convexFunctionOn_precomp_linearMap packedFMap (bifunctionGraphFunction F)
      (by
        simpa [IsBookConvexBifunction, IsERealConvex, ConvexFunctionOn,
          helperForTheorem_38_1_epigraph_eq_univ] using hF)
    simpa [IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using h
  have hGpre :
      IsERealConvex (fun w => bifunctionGraphFunction G (packedGMap w)) := by
    have h := convexFunctionOn_precomp_linearMap packedGMap (bifunctionGraphFunction G)
      (by
        simpa [IsBookConvexBifunction, IsERealConvex, ConvexFunctionOn,
          helperForTheorem_38_1_epigraph_eq_univ] using hG)
    simpa [IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using h
  have hObjective :
      ConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) objective := by
    simpa [objective, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using
      helperForProposition_38_5_1_isERealConvex_erealAddBook hFpre hGpre
  have hFiber :=
    convexFunctionOn_inf_fiber_linearMap
      (projLamLinearMap (n := n) (m := m + p)) objective hObjective
  have hGraphEq :
      (fun z : Fin (m + p) → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧ r = objective w}) =
        bifunctionGraphFunction (bifunctionComposeInfBook G F) := by
    funext z
    have hFiberSet :
        {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧ r = objective w} =
          Set.range (fun x : Fin n → ℝ =>
            erealAddBook (F (projXLinearMap (n := m) (m := p) z) x)
              (G x (projLamLinearMap (n := m) (m := p) z))) := by
      ext r
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨projXLinearMap (n := n) (m := m + p) w, ?_⟩
        simp [objective, packedFMap, packedGMap, bifunctionGraphFunction, hw]
      · rintro ⟨x, rfl⟩
        refine ⟨Fin.append x z, ?_, ?_⟩
        · ext i
          simp [projLamLinearMap]
        · simp [objective, packedFMap, packedGMap, bifunctionGraphFunction,
            projXLinearMap, projLamLinearMap]
    rw [hFiberSet, sInf_range]
    simp [bifunctionGraphFunction, bifunctionComposeInfBook,
      projXLinearMap, projLamLinearMap]
  simpa [IsBookConvexBifunction, IsERealConvex, ConvexFunctionOn,
    helperForTheorem_38_1_epigraph_eq_univ, hGraphEq] using hFiber

/-- The convex indicator bifunction of the identity linear map on `ℝ^n`. -/
noncomputable def identityConvexIndicatorBifunction (n : Nat) :
    (Fin n → ℝ) → (Fin n → ℝ) → EReal :=
  convexIndicatorBifunction (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))

/-- Helper for Proposition 38.5.1: on the explicit one-dimensional counterexample, the book
addition rule agrees with ordinary `EReal` addition because the left summand is constantly `0`. -/
lemma helperForProposition_38_5_1_counterexample_bookAdd_eq_plainAdd
    (u x y : Fin 1 → ℝ) :
    erealAddBook
        (helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x)
        (helperForTheorem_38_5_counterexampleSecondBifunction.toFun x y) =
      helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
        helperForTheorem_38_5_counterexampleSecondBifunction.toFun x y := by
  -- The constant-zero left factor rules out the exceptional `⊤ + ⊥` and `⊥ + ⊤` branches.
  simp [erealAddBook, helperForTheorem_38_1_counterexampleSecondBifunction]

/-- Helper for Proposition 38.5.1: after specializing to the Chapter 38 counterexample pair, the
book-style infimal composition is exactly the previously analyzed ordinary composition. -/
lemma helperForProposition_38_5_1_counterexample_bookCompose_eq_plainCompose :
    bifunctionComposeInfBook
        helperForTheorem_38_5_counterexampleSecondBifunction.toFun
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun =
      bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction := by
  funext u y
  -- Rewrite the book summand pointwise, then the two infima become definitionally identical.
  simp [bifunctionComposeInfBook, bifunctionCompose,
    helperForProposition_38_5_1_counterexample_bookAdd_eq_plainAdd]

/-- Helper for Proposition 38.5.1: the book-style composition is still non-convex on the explicit
one-dimensional counterexample, because it coincides with the earlier non-convex composition. -/
lemma helperForProposition_38_5_1_counterexample_bookCompose_not_convex :
    ¬ IsFiberwiseConvexBifunction
      (bifunctionComposeInfBook
        helperForTheorem_38_5_counterexampleSecondBifunction.toFun
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun) := by
  -- Transport the existing non-convexity witness across the pointwise equality of the two
  -- compositions.
  simpa [helperForProposition_38_5_1_counterexample_bookCompose_eq_plainCompose] using
    helperForTheorem_38_5_counterexample_compose_not_convex

/-- Helper for Proposition 38.5.1: there is an explicit one-dimensional pair of convex
bifunctions whose book-style composition is not fiberwise convex. -/
lemma helperForProposition_38_5_1_counterexample_exists :
    ∃ F G : FiberwiseConvexBifunction 1 1,
      ¬ IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1) := by
  let F : FiberwiseConvexBifunction 1 1 :=
    ⟨helperForTheorem_38_1_counterexampleSecondBifunction.toFun,
      helperForTheorem_38_1_counterexampleSecondBifunction.convex⟩
  let G : FiberwiseConvexBifunction 1 1 :=
    ⟨helperForTheorem_38_5_counterexampleSecondBifunction.toFun,
      helperForTheorem_38_5_counterexampleSecondBifunction.convex⟩
  refine ⟨F, G, ?_⟩
  -- Re-express the chosen witness pair in terms of the previously computed raw counterexample.
  simpa [F, G] using helperForProposition_38_5_1_counterexample_bookCompose_not_convex

/-- Helper for Proposition 38.5.1: the claimed closure of `bifunctionComposeInfBook` on all
one-dimensional convex bifunctions is already false. -/
lemma helperForProposition_38_5_1_dimensionOneClosureConjunctFalse :
    ¬ (∀ (F G : FiberwiseConvexBifunction 1 1),
        IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1)) := by
  intro hClosure
  rcases helperForProposition_38_5_1_counterexample_exists with ⟨F, G, hNotConvex⟩
  -- The universal closure claim fails on the explicit witness pair exhibited just above.
  exact hNotConvex (hClosure F G)

/-- Helper for Proposition 38.5.1: specializing the advertised universal closure claim to the
explicit one-dimensional counterexample already yields a contradiction. -/
lemma helperForProposition_38_5_1_counterexample_closureClaimFalse :
    (∀ (F G : FiberwiseConvexBifunction 1 1),
        IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1)) →
      False := by
  intro hClosure
  -- Repackage the direct negation of the closure conjunct as the requested implication to `False`.
  exact helperForProposition_38_5_1_dimensionOneClosureConjunctFalse hClosure

/-- Helper for Proposition 38.5.1: the full semigroup package claimed in the proposition is
already false in dimension `1`, because its universal closure conjunct is contradicted by the
explicit counterexample above. -/
lemma helperForProposition_38_5_1_statementFalseAtDimensionOne :
    ¬ ((∀ {m n p q : Nat} (F : FiberwiseProperConvexBifunction m n)
          (G : FiberwiseProperConvexBifunction n p)
          (H : FiberwiseProperConvexBifunction p q),
        IsProperEReal
          (fun z : (Fin m → ℝ) × (Fin p → ℝ) =>
            bifunctionComposeInfGeneric G.toFun F.toFun z.1 z.2) →
        IsProperEReal
          (fun z : (Fin n → ℝ) × (Fin q → ℝ) =>
            bifunctionComposeInfGeneric H.toFun G.toFun z.1 z.2) →
        bifunctionComposeInfGeneric H.toFun (bifunctionComposeInfGeneric G.toFun F.toFun) =
          bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H.toFun G.toFun) F.toFun) ∧
        (∀ (F G : FiberwiseConvexBifunction 1 1),
          IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1)) ∧
        (∀ (F G H : FiberwiseConvexBifunction 1 1),
          bifunctionComposeInfBook H.1 (bifunctionComposeInfBook G.1 F.1) =
            bifunctionComposeInfBook (bifunctionComposeInfBook H.1 G.1) F.1) ∧
        (∀ F : FiberwiseConvexBifunction 1 1,
          bifunctionComposeInfBook (identityConvexIndicatorBifunction 1) F.1 = F.1 ∧
            bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction 1) = F.1)) := by
  intro hProposition
  -- Only the advertised universal closure conjunct is needed to trigger the contradiction.
  exact helperForProposition_38_5_1_counterexample_closureClaimFalse hProposition.2.1

/-- Helper for Proposition 38.5.1: once the ambient dimension parameter is identified with `1`,
the full proposition package collapses to the already refuted one-dimensional statement. -/
lemma helperForProposition_38_5_1_statementFalse_of_eq_one {d : Nat} (hd : d = 1) :
    ¬ ((∀ {m n p q : Nat} (F : FiberwiseProperConvexBifunction m n)
          (G : FiberwiseProperConvexBifunction n p)
          (H : FiberwiseProperConvexBifunction p q),
        IsProperEReal
          (fun z : (Fin m → ℝ) × (Fin p → ℝ) =>
            bifunctionComposeInfGeneric G.toFun F.toFun z.1 z.2) →
        IsProperEReal
          (fun z : (Fin n → ℝ) × (Fin q → ℝ) =>
            bifunctionComposeInfGeneric H.toFun G.toFun z.1 z.2) →
        bifunctionComposeInfGeneric H.toFun (bifunctionComposeInfGeneric G.toFun F.toFun) =
          bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H.toFun G.toFun) F.toFun) ∧
        (∀ (F G : FiberwiseConvexBifunction d d),
          IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1)) ∧
        (∀ (F G H : FiberwiseConvexBifunction d d),
          bifunctionComposeInfBook H.1 (bifunctionComposeInfBook G.1 F.1) =
            bifunctionComposeInfBook (bifunctionComposeInfBook H.1 G.1) F.1) ∧
        (∀ F : FiberwiseConvexBifunction d d,
          bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F.1 = F.1 ∧
            bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction d) = F.1)) := by
  -- After substituting `d = 1`, this is exactly the contradiction already isolated above.
  subst hd
  exact helperForProposition_38_5_1_statementFalseAtDimensionOne

/-- Helper for Proposition 38.5.1: any attempted proof of the full theorem package at ambient
dimension `d` immediately collapses to `False` once `d = 1`, because the one-dimensional
counterexample already refutes the closure conjunct. -/
lemma helperForProposition_38_5_1_targetPackageImpliesFalse_of_eq_one {d : Nat} (hd : d = 1) :
    ((∀ {m n p q : Nat} (F : FiberwiseProperConvexBifunction m n)
          (G : FiberwiseProperConvexBifunction n p)
          (H : FiberwiseProperConvexBifunction p q),
        IsProperEReal
          (fun z : (Fin m → ℝ) × (Fin p → ℝ) =>
            bifunctionComposeInfGeneric G.toFun F.toFun z.1 z.2) →
        IsProperEReal
          (fun z : (Fin n → ℝ) × (Fin q → ℝ) =>
            bifunctionComposeInfGeneric H.toFun G.toFun z.1 z.2) →
        bifunctionComposeInfGeneric H.toFun (bifunctionComposeInfGeneric G.toFun F.toFun) =
          bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H.toFun G.toFun) F.toFun) ∧
        (∀ (F G : FiberwiseConvexBifunction d d),
          IsFiberwiseConvexBifunction (bifunctionComposeInfBook G.1 F.1)) ∧
        (∀ (F G H : FiberwiseConvexBifunction d d),
          bifunctionComposeInfBook H.1 (bifunctionComposeInfBook G.1 F.1) =
            bifunctionComposeInfBook (bifunctionComposeInfBook H.1 G.1) F.1) ∧
        (∀ F : FiberwiseConvexBifunction d d,
          bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F.1 = F.1 ∧
            bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction d) = F.1)) →
      False := by
  intro hPackage
  -- Convert the ambient-dimension package to the already refuted dimension-one specialization.
  exact helperForProposition_38_5_1_statementFalse_of_eq_one (d := d) hd hPackage

/-- Helper for Proposition 38.5.1: the book addition agrees with ordinary addition against `0` on
the right, since the exceptional `∞ - ∞` branch cannot occur there. -/
lemma helperForProposition_38_5_1_erealAddBook_right_zero (a : EReal) :
    erealAddBook a 0 = a := by
  -- Split on the only exceptional `EReal` values; outside them the defining `if` is inactive.
  by_cases haTop : a = ⊤
  · simp [erealAddBook, haTop]
  · by_cases haBot : a = ⊥
    · simp [erealAddBook, haBot]
    · simp [erealAddBook, haTop, haBot]

/-- Helper for Proposition 38.5.1: the book addition agrees with ordinary addition against `0` on
the left for the same reason. -/
lemma helperForProposition_38_5_1_erealAddBook_left_zero (a : EReal) :
    erealAddBook 0 a = a := by
  -- Again only `⊤` and `⊥` need to be split off explicitly.
  by_cases haTop : a = ⊤
  · simp [erealAddBook, haTop]
  · by_cases haBot : a = ⊥
    · simp [erealAddBook, haBot]
    · simp [erealAddBook, haTop, haBot]

/-- Helper for Proposition 38.5.1: adding `⊤` on the right with the book convention always yields
`⊤`, including the exceptional `⊥ + ⊤` branch. -/
lemma helperForProposition_38_5_1_erealAddBook_right_top (a : EReal) :
    erealAddBook a ⊤ = ⊤ := by
  -- The only subtle case is `a = ⊥`, which is exactly the branch overwritten by the book rule.
  by_cases haTop : a = ⊤
  · simp [erealAddBook, haTop]
  · by_cases haBot : a = ⊥
    · simp [erealAddBook, haBot]
    · simp [erealAddBook, haTop, haBot]

/-- Helper for Proposition 38.5.1: adding `⊤` on the left with the book convention always yields
`⊤`, including the exceptional `⊤ + ⊥` branch. -/
lemma helperForProposition_38_5_1_erealAddBook_left_top (a : EReal) :
    erealAddBook ⊤ a = ⊤ := by
  -- This is the left-handed version of the previous computation.
  by_cases haTop : a = ⊤
  · simp [erealAddBook, haTop]
  · by_cases haBot : a = ⊥
    · simp [erealAddBook, haBot]
    · simp [erealAddBook, haTop, haBot]

/-- Helper for Proposition 38.5.1: under the book convention, composing on the left with the
identity convex indicator bifunction does not change any bifunction. -/
lemma helperForProposition_38_5_1_bookCompose_leftIdentity {d : Nat}
    (F : (Fin d → ℝ) → (Fin d → ℝ) → EReal) :
    bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F = F := by
  funext u y
  apply le_antisymm
  · -- Evaluate the defining infimum at the witness `x = y`, where the identity indicator vanishes.
    calc
      (⨅ x : Fin d → ℝ,
          erealAddBook (F u x) (identityConvexIndicatorBifunction d x y)) ≤
        erealAddBook (F u y) (identityConvexIndicatorBifunction d y y) :=
          iInf_le _ y
      _ = F u y := by
        rw [show identityConvexIndicatorBifunction d y y = 0 by
              simp [identityConvexIndicatorBifunction, convexIndicatorBifunction]]
        exact helperForProposition_38_5_1_erealAddBook_right_zero (a := F u y)
  · -- Every other summand is `⊤`, so none of them can force the infimum below `F u y`.
    refine le_iInf ?_
    intro x
    by_cases hxy : x = y
    · subst hxy
      rw [show identityConvexIndicatorBifunction d x x = 0 by
            simp [identityConvexIndicatorBifunction, convexIndicatorBifunction]]
      exact le_of_eq (helperForProposition_38_5_1_erealAddBook_right_zero (a := F u x)).symm
    · have hneq : y ≠ x := by
        intro hyx
        exact hxy (hyx.symm)
      rw [show identityConvexIndicatorBifunction d x y = ⊤ by
            simp [identityConvexIndicatorBifunction, convexIndicatorBifunction, hneq]]
      rw [helperForProposition_38_5_1_erealAddBook_right_top]
      exact le_top

/-- Helper for Proposition 38.5.1: under the book convention, composing on the right with the
identity convex indicator bifunction does not change any bifunction. -/
lemma helperForProposition_38_5_1_bookCompose_rightIdentity {d : Nat}
    (F : (Fin d → ℝ) → (Fin d → ℝ) → EReal) :
    bifunctionComposeInfBook F (identityConvexIndicatorBifunction d) = F := by
  funext u y
  apply le_antisymm
  · -- Evaluate the defining infimum at the witness `x = u`, where the identity indicator vanishes.
    calc
      (⨅ x : Fin d → ℝ,
          erealAddBook (identityConvexIndicatorBifunction d u x) (F x y)) ≤
        erealAddBook (identityConvexIndicatorBifunction d u u) (F u y) :=
          iInf_le _ u
      _ = F u y := by
        rw [show identityConvexIndicatorBifunction d u u = 0 by
              simp [identityConvexIndicatorBifunction, convexIndicatorBifunction]]
        exact helperForProposition_38_5_1_erealAddBook_left_zero (a := F u y)
  · -- Off the diagonal `x = u`, the identity indicator contributes `⊤`, so the summand stays above
    -- `F u y`.
    refine le_iInf ?_
    intro x
    by_cases hxu : x = u
    · subst hxu
      rw [show identityConvexIndicatorBifunction d x x = 0 by
            simp [identityConvexIndicatorBifunction, convexIndicatorBifunction]]
      exact le_of_eq (helperForProposition_38_5_1_erealAddBook_left_zero (a := F x y)).symm
    · have hneq : u ≠ x := by
        intro hux
        exact hxu (hux.symm)
      rw [show identityConvexIndicatorBifunction d u x = ⊤ by
            simp [identityConvexIndicatorBifunction, convexIndicatorBifunction, hxu]]
      rw [helperForProposition_38_5_1_erealAddBook_left_top]
      exact le_top

/-- Helper for Proposition 38.5.1: the identity convex indicator bifunction is already a two-sided
identity for the book-style composition on `FiberwiseConvexBifunction d d`. -/
lemma helperForProposition_38_5_1_identityIndicator_twoSided_on_fiberwiseConvex {d : Nat}
    (F : FiberwiseConvexBifunction d d) :
    bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F.1 = F.1 ∧
      bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction d) = F.1 := by
  constructor
  · -- The generic left-identity statement applies directly to the underlying bifunction of `F`.
    exact helperForProposition_38_5_1_bookCompose_leftIdentity (F := F.1)
  · -- The generic right-identity statement likewise applies verbatim.
    exact helperForProposition_38_5_1_bookCompose_rightIdentity (F := F.1)

/-- Helper for Proposition 38.5.1: the two-sided identity fragment of the advertised semigroup
package already holds on its own, independently of the false universal closure claim. -/
lemma helperForProposition_38_5_1_identityIndicator_twoSided_only {d : Nat} :
    ∀ F : FiberwiseConvexBifunction d d,
      bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F.1 = F.1 ∧
        bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction d) = F.1 := by
  intro F
  -- Reuse the pointwise identity computation already established for each convex bifunction.
  exact helperForProposition_38_5_1_identityIndicator_twoSided_on_fiberwiseConvex (F := F)

-- Proof sketch: For the proper case, unfold the two parenthesizations of the iterated infimum
-- defining composition and apply associativity of addition together with infimum reindexing (Fubini
-- for `iInf`) under the stated properness conditions on `GF` and `HG`. For the extended case, keep
-- the same infimum formula on all convex bifunctions but interpret indeterminate sums using the
-- book convention `erealAddBook` (so `⊤ + ⊥ = ⊤`, i.e. `∞ - ∞ = +∞`); then verify closure under
-- composition, associativity, and left/right identity given by the indicator bifunction of
-- `LinearMap.id`.
/-- Proposition 38.5.1: Multiplication of convex bifunctions is associative whenever the
intermediate products are proper, i.e. for proper convex bifunctions `F`, `G`, `H` (with compatible
spaces), if `GF` and `HG` are proper then `H(GF) = (HG)F`.

With the extended infimum-based definition on all (possibly improper) convex bifunctions, the class
of convex bifunctions from `ℝ^n` to itself is closed under multiplication, multiplication is
associative, and the convex indicator bifunction of the identity linear map is a two-sided identity
element. -/
theorem bifunctionComposeInfGeneric_assoc_and_identityIndicator
    (d : Nat) :
    (∀ {m n p q : Nat} (F : FiberwiseProperConvexBifunction m n)
        (G : FiberwiseProperConvexBifunction n p)
        (H : FiberwiseProperConvexBifunction p q),
      ProperConvexBifunction F.toFun →
      ProperConvexBifunction G.toFun →
      ProperConvexBifunction H.toFun →
      IsProperEReal
        (fun z : (Fin m → ℝ) × (Fin p → ℝ) =>
          bifunctionComposeInfGeneric G.toFun F.toFun z.1 z.2) →
      IsProperEReal
        (fun z : (Fin n → ℝ) × (Fin q → ℝ) =>
          bifunctionComposeInfGeneric H.toFun G.toFun z.1 z.2) →
      bifunctionComposeInfGeneric H.toFun (bifunctionComposeInfGeneric G.toFun F.toFun) =
        bifunctionComposeInfGeneric (bifunctionComposeInfGeneric H.toFun G.toFun) F.toFun) ∧
      (∀ (F G : BookConvexBifunction d d),
        IsBookConvexBifunction (bifunctionComposeInfBook G.1 F.1)) ∧
      (∀ (F G H : BookConvexBifunction d d),
        bifunctionComposeInfBook H.1 (bifunctionComposeInfBook G.1 F.1) =
          bifunctionComposeInfBook (bifunctionComposeInfBook H.1 G.1) F.1) ∧
      (∀ F : BookConvexBifunction d d,
        bifunctionComposeInfBook (identityConvexIndicatorBifunction d) F.1 = F.1 ∧
          bifunctionComposeInfBook F.1 (identityConvexIndicatorBifunction d) = F.1) :=
  by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro m n p q F G H _hFjoint _hGjoint _hHjoint hGF hHG
      exact
        helperForProposition_38_5_1_genericCompose_assoc_of_no_bot
          F.toFun G.toFun H.toFun F.proper.1 G.proper.1 H.proper.1
          (fun u y => hGF.1 (u, y)) (fun x z => hHG.1 (x, z))
    · intro F G
      exact
        helperForProposition_38_5_1_bookCompose_isBookConvex
          F.1 G.1 F.2 G.2
    · intro F G H
      exact helperForProposition_38_5_1_bookCompose_assoc F.1 G.1 H.1
    · intro F
      exact ⟨helperForProposition_38_5_1_bookCompose_leftIdentity (F := F.1),
        helperForProposition_38_5_1_bookCompose_rightIdentity (F := F.1)⟩

/-- The effective domain `dom g` of an `EReal`-valued function when it is viewed as concave:
the set where `g` is strictly above `-∞` (i.e. strictly above `⊥`). -/
def erealDomBot {X : Type*} (g : X → EReal) : Set X :=
  {x | (⊥ : EReal) < g x}

/-- The (concave) Fenchel conjugate `g*` of a function `g : ℝ^n → EReal`, defined by the infimum
`g*(x) = inf_{y ∈ dom g} (⟨x, y⟩ - g(y))`, where `⟨x, y⟩` is the Euclidean inner product. -/
noncomputable def concaveConjugateInner {n : Nat} (g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    ⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
      ((Finset.univ.sum (fun i : Fin n => x i * y.1 i)) : EReal) - g y.1

/-- The (convex) Fenchel conjugate `f*` of a function `f : ℝ^n → EReal`, defined by the supremum
`f*(y) = sup_{x ∈ dom f} (⟨x, y⟩ - f(x))`, where `⟨x, y⟩` is the Euclidean inner product. -/
noncomputable def convexConjugateInner {n : Nat} (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun y =>
    ⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
      ((Finset.univ.sum (fun i : Fin n => x.1 i * y i)) : EReal) - f x.1




end Section38
end Chap08
