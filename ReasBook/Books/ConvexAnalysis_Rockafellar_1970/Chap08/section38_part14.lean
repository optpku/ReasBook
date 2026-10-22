/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part13

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Corollary 38.5.1: after transporting the qualification hypothesis to the reversed
Dual pair, the theorem-local non-`⊤` witness there forces the original primal composition `GF` to
avoid `⊥` everywhere. This is the clean operator-transport consequence of the reversed packaged
adjoint identity, independent of the remaining closure comparison. -/
lemma helperForCorollary_38_5_1_compose_ne_bot_of_transported_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hTransportedHri :
      (intrinsicInterior ℝ
            (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty) :
    ∀ u : Fin m → ℝ, ∀ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊥ : EReal) := by
  rcases
      helperForCorollary_38_5_1_reversedDual_theorem38_5_application
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) hTransportedHri with
    ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq, hGdualInv_proper,
      hReversedEq, _hReversedAttainment⟩
  have hReversedConvex :
      ConvexBifunction (bifunctionCompose GdualInv FdualInv) := by
    exact
      (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
        (F := FdualInv) (G := GdualInv) hFdualInv_proper hGdualInv_proper).1
  have hFdualInv_domBot :
      bifunctionDomBot (bifunctionInverse FdualInv.toFun) =
        bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) := by
    ext xStar
    constructor
    · intro hx
      rcases hx with ⟨uStar, huStar⟩
      refine ⟨uStar, ?_⟩
      simpa [hFdualInv_eq, bifunctionInverse] using huStar
    · intro hx
      rcases hx with ⟨uStar, huStar⟩
      refine ⟨uStar, ?_⟩
      simpa [hFdualInv_eq, bifunctionInverse] using huStar
  have hTheorem38_5_hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse FdualInv.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom GdualInv.toFun)).Nonempty := by
    rw [hFdualInv_domBot, hGdualInv_eq]
    exact hTransportedHri
  rcases
      helperForTheorem_38_5_compose_exists_ne_top_of_hri
        (F := FdualInv) (G := GdualInv) hTheorem38_5_hri with
    ⟨u0, y0, hReversedWitness⟩
  have hAdjointNeTop :
      ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ y u ≠
          (⊤ : EReal) := by
    intro y u
    have hTermNeTop :
        bifunctionCompose GdualInv FdualInv u0 y0 - (((y0 ⬝ᵥ y : ℝ) : EReal)) +
            (((u0 ⬝ᵥ u : ℝ) : EReal)) ≠ (⊤ : EReal) := by
      have hLeftNeTop :
          bifunctionCompose GdualInv FdualInv u0 y0 + (-(((y0 ⬝ᵥ y : ℝ) : EReal))) ≠
            (⊤ : EReal) := by
        exact EReal.add_ne_top hReversedWitness (by simp)
      simpa [sub_eq_add_neg, add_assoc] using
        EReal.add_ne_top hLeftNeTop (by simp)
    intro hTop
    have hLe :
        adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ y u ≤
          bifunctionCompose GdualInv FdualInv u0 y0 - (((y0 ⬝ᵥ y : ℝ) : EReal)) +
            (((u0 ⬝ᵥ u : ℝ) : EReal)) := by
      rw [adjointOfConvexBifunction]
      exact sInf_le ⟨(u0, y0), rfl⟩
    have hTopLe :
        (⊤ : EReal) ≤ bifunctionCompose GdualInv FdualInv u0 y0 - (((y0 ⬝ᵥ y : ℝ) : EReal)) +
          (((u0 ⬝ᵥ u : ℝ) : EReal)) := by
      simpa [hTop] using hLe
    exact hTermNeTop (top_unique hTopLe)
  have hFBiadjEq : biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ = F.toFun := by
    exact
      (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed)).1
  have hGBiadjEq : biadjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ = G.toFun := by
    exact
      (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed)).2
  have hPackagedAdjointEq :
      adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ =
        bifunctionInverse (bifunctionCompose G F) := by
    funext y u
    calc
      adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose GdualInv FdualInv)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            exact
              congrFun
                (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                    (F := bifunctionCompose GdualInv FdualInv) hReversedConvex) y)
                u
      _ =
        bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
          (bifunctionAdjoint GdualInv.toFun)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            rw [hReversedEq]
      _ = - bifunctionCompose G F u y := by
            exact
              helperForCorollary_38_5_1_reversedDual_output_rewrite_at_primalPair
                (F := F) (G := G)
                (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
                (hFdualInv_eq := hFdualInv_eq) (hFdualInv_proper := hFdualInv_proper)
                (hGdualInv_eq := hGdualInv_eq) (hGdualInv_proper := hGdualInv_proper)
                (hFBiadjEq := hFBiadjEq) (hGBiadjEq := hGBiadjEq) u y
      _ = bifunctionInverse (bifunctionCompose G F) y u := by
            rfl
  intro u y
  have hInvNeTop : bifunctionInverse (bifunctionCompose G F) y u ≠ (⊤ : EReal) := by
    intro hTop
    have hPointEq :
        adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ y u =
          bifunctionInverse (bifunctionCompose G F) y u := by
      simpa using congrFun (congrFun hPackagedAdjointEq y) u
    exact hAdjointNeTop y u (hPointEq.trans hTop)
  simpa [bifunctionInverse, EReal.neg_eq_top_iff] using hInvNeTop

/-- Helper for Corollary 38.5.1: the original Chapter 38 qualification hypothesis therefore
already rules out `⊥` values of `GF` everywhere after the signed domain transport. -/
lemma helperForCorollary_38_5_1_compose_ne_bot_of_hri
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
    ∀ u : Fin m → ℝ, ∀ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊥ : EReal) := by
  have hTransportedHri :
      (intrinsicInterior ℝ
            (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty :=
    helperForCorollary_38_5_1_signedDotProductEquiv_hri_transport
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri
  exact
    helperForCorollary_38_5_1_compose_ne_bot_of_transported_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed) hTransportedHri

/-- Helper for Corollary 38.5.1: the Chapter 6 packaged adjoint of `GF` is automatically a
closed concave bifunction as soon as `GF` is known to be convex. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_closedConcave
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F)) :
    ClosedConcaveBifunction
      (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) := by
  -- The Chapter 6 adjoint theorem already upgrades every convex primal bifunction to a closed
  -- concave packaged adjoint.
  exact
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := bifunctionCompose G F)).1 hComposeConvex).1

/-- Helper for Corollary 38.5.1: a proper concave packaged bifunction has negated graph nowhere
equal to `⊥`, which is exactly the side condition needed by the Chapter 6 closed-only fixed-point
theorem for `concaveBifunctionClosure`. -/
lemma helperForCorollary_38_5_1_negGraph_ne_bot_of_properConcave
    {m n : Nat} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK_proper : ProperConcaveBifunction K) :
    ∀ z : Fin (m + n) → ℝ, (-bifunctionGraphFunction K z) ≠ (⊥ : EReal) := by
  intro z
  simpa [ProperConcaveERealFunction] using hK_proper.2.1.1 z

/-- Helper for Corollary 38.5.1: the effective domain of the negated graph function is exactly
the set of product points where the original bifunction is not `⊥`. This is the graph-level domain
rewrite needed to compare Chapter 6 concave closures with the Chapter 38 operator transport. -/
lemma helperForCorollary_38_5_1_negGraph_effectiveDomain_eq_ne_bot
    {m n : Nat} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K z) =
        {z : Fin (m + n) → ℝ | bifunctionGraphFunction K z ≠ (⊥ : EReal)} := by
  ext z
  rw [effectiveDomain_eq]
  constructor
  · intro hz
    have hne : -bifunctionGraphFunction K z ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hz.2
    simpa [EReal.neg_eq_top_iff] using hne
  · intro hz
    refine ⟨by simp, ?_⟩
    exact lt_top_iff_ne_top.mpr <| by simpa [EReal.neg_eq_top_iff] using hz

/-- Helper for Corollary 38.5.1: every bifunction lies below its Chapter 6 packaged concave
closure, pointwise on the graph-function coordinates. This gives the basic one-way comparison from
the Chapter 38 lower closure to the Chapter 6 packaged upper closure. -/
lemma helperForCorollary_38_5_1_self_le_concaveBifunctionClosure
    {m n : Nat} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    K ≤ concaveBifunctionClosure K := by
  intro u x
  simpa [concaveBifunctionClosure, bifunctionGraphFunction] using
    helperForCorollary_6_30_3_self_le_concaveClosure
      (g := bifunctionGraphFunction K) (Fin.append u x)

/-- Helper for Corollary 38.5.1: the Chapter 38 lower closure is always pointwise bounded above by
the Chapter 6 packaged concave closure of the same bifunction. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_le_concaveBifunctionClosure
    {m n : Nat} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    bifunctionClosure K ≤ concaveBifunctionClosure K := by
  intro u x
  exact
    le_trans
      (helperForCorollary_38_5_1_bifunctionClosure_le (K := K) u x)
      (helperForCorollary_38_5_1_self_le_concaveBifunctionClosure K u x)

/-- Helper for Corollary 38.5.1: if two concave bifunctions have the same relative
interior effective domain after negating their graph functions, and those negated graph functions
agree there, then their Chapter 6 concave closures coincide. This is the bifunction-shaped form of
Corollary 7.3.4 used by the original text when the final identity is obtained from equality on a
common relative interior and then closed up globally. -/
lemma helperForCorollary_38_5_1_concaveBifunctionClosure_eq_of_agree_on_ri_effectiveDomain
    {m n : Nat} {K₁ K₂ : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK₁_concave : ConcaveBifunction K₁)
    (hK₂_concave : ConcaveBifunction K₂)
    (hri :
      euclideanRelativeInterior (m + n)
        ((fun z : EuclideanSpace Real (Fin (m + n)) => (z : Fin (m + n) → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin (m + n) → Real))
            (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₁ z)) =
      euclideanRelativeInterior (m + n)
        ((fun z : EuclideanSpace Real (Fin (m + n)) => (z : Fin (m + n) → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin (m + n) → Real))
            (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₂ z)))
    (hagree :
      ∀ z ∈
        euclideanRelativeInterior (m + n)
          ((fun z : EuclideanSpace Real (Fin (m + n)) => (z : Fin (m + n) → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin (m + n) → Real))
              (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₁ z)),
        -bifunctionGraphFunction K₁ (z : Fin (m + n) → ℝ) =
          -bifunctionGraphFunction K₂ (z : Fin (m + n) → ℝ)) :
    concaveBifunctionClosure K₁ = concaveBifunctionClosure K₂ := by
  have hClosure :
      convexFunctionClosure (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₁ z) =
        convexFunctionClosure (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₂ z) := by
    exact
      convexFunctionClosure_eq_of_agree_on_ri_effectiveDomain
        (n := m + n)
        (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₁ z)
        (g := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction K₂ z)
        (by simpa [ConcaveBifunction] using hK₁_concave)
        (by simpa [ConcaveBifunction] using hK₂_concave)
        hri hagree
  funext u x
  simpa [concaveBifunctionClosure, concaveClosure_eq_neg_convexClosure_neg, convexClosure] using
    congrArg Neg.neg (congrFun hClosure (Fin.append u x))

/-- Helper for Corollary 38.5.1: the Chapter 6 one-variable concave closure is monotone. -/
lemma helperForCorollary_38_5_1_concaveClosure_mono
    {n : Nat} {g₁ g₂ : (Fin n → ℝ) → EReal}
    (h₁₂ : g₁ ≤ g₂) :
    concaveClosure g₁ ≤ concaveClosure g₂ := by
  intro x
  have hneg : (fun z : Fin n → ℝ => -g₂ z) ≤ fun z : Fin n → ℝ => -g₁ z := by
    intro z
    exact EReal.neg_le_neg_iff.mpr (h₁₂ z)
  have hcl := convexFunctionClosure_mono hneg x
  have hnegcl :
      -convexFunctionClosure (fun z : Fin n → ℝ => -g₁ z) x ≤
        -convexFunctionClosure (fun z : Fin n → ℝ => -g₂ z) x := by
    simpa using (EReal.neg_le_neg_iff.mpr hcl)
  simpa [concaveClosure_eq_neg_convexClosure_neg, convexClosure] using hnegcl

/-- Helper for Corollary 38.5.1: the Chapter 6 packaged concave closure is monotone. -/
lemma helperForCorollary_38_5_1_concaveBifunctionClosure_mono
    {m n : Nat} {K₁ K₂ : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (h₁₂ : K₁ ≤ K₂) :
    concaveBifunctionClosure K₁ ≤ concaveBifunctionClosure K₂ := by
  intro u x
  simpa [concaveBifunctionClosure, bifunctionGraphFunction] using
    helperForCorollary_38_5_1_concaveClosure_mono
      (g₁ := bifunctionGraphFunction K₁)
      (g₂ := bifunctionGraphFunction K₂)
      (fun z => h₁₂ (fun i : Fin m => z (Fin.castAdd n i))
        (fun j : Fin n => z (Fin.natAdd m j)))
      (Fin.append u x)

/-- Helper for Corollary 38.5.1: if the packaged adjoint of a convex bifunction avoids `⊤` at
some dual pair, then the primal bifunction itself must avoid `⊤` somewhere. Otherwise every term in
the defining infimum would already be `⊤`. -/
lemma helperForCorollary_38_5_1_exists_primal_ne_top_of_packagedAdjoint_ne_top
    {m n : Nat} {H : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hH_convex : ConvexBifunction H)
    {xStar : Fin n → ℝ} {uStar : Fin m → ℝ}
    (hAdjointNeTop :
      adjointOfConvexBifunction ⟨H, hH_convex⟩ xStar uStar ≠ (⊤ : EReal)) :
    ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, H u x ≠ (⊤ : EReal) := by
  by_contra hNoWitness
  push_neg at hNoWitness
  have hEveryTermTop :
      ∀ p : (Fin m → ℝ) × (Fin n → ℝ),
        H p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) =
          (⊤ : EReal) := by
    intro p
    have hHx : H p.1 p.2 = (⊤ : EReal) := hNoWitness p.1 p.2
    calc
      H p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))
          = (⊤ : EReal) - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) := by
              rw [hHx]
      _ = (⊤ : EReal) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) := by
            simp [sub_eq_add_neg]
      _ = (⊤ : EReal) := by simp
  have hAdjointEqTop :
      adjointOfConvexBifunction ⟨H, hH_convex⟩ xStar uStar = (⊤ : EReal) := by
    rw [adjointOfConvexBifunction, sInf_range]
    exact top_unique <| by
      refine le_iInf ?_
      intro p
      simpa [hEveryTermTop p]
  exact hAdjointNeTop hAdjointEqTop

/-- Helper for Corollary 38.5.1: any non-`⊤` packaged-adjoint value of `GF` already yields the
primal non-`⊤` witness needed later for the Chapter 6 negated-graph condition. -/
lemma helperForCorollary_38_5_1_compose_exists_ne_top_of_packagedAdjointCompose_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    {yStarVec : Fin p → ℝ} {uStarVec : Fin m → ℝ}
    (hAdjointNeTop :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊤ : EReal)) :
    ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal) := by
  simpa using
    helperForCorollary_38_5_1_exists_primal_ne_top_of_packagedAdjoint_ne_top
      (hH_convex := hComposeConvex) (xStar := yStarVec) (uStar := uStarVec) hAdjointNeTop

/-- Helper for Corollary 38.5.1: the preceding primal non-`⊤` witness is exactly what is needed
to verify the Chapter 6 no-`⊥` graph condition for the packaged adjoint. -/
lemma helperForCorollary_38_5_1_negGraph_ne_bot_of_packagedAdjoint_exists_primal_ne_top
    {m n : Nat} {H : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hH_convex : ConvexBifunction H)
    (hWitness : ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, H u x ≠ (⊤ : EReal)) :
    ∀ z : Fin (n + m) → ℝ,
      (-bifunctionGraphFunction (adjointOfConvexBifunction ⟨H, hH_convex⟩) z) ≠ (⊥ : EReal) := by
  intro z
  have hAdjNeTop :
      adjointOfConvexBifunction ⟨H, hH_convex⟩
        (fun j : Fin n => z (Fin.castAdd m j))
        (fun i : Fin m => z (Fin.natAdd n i)) ≠ (⊤ : EReal) :=
    helperForCorollary_38_5_1_packagedAdjoint_ne_top_of_exists_primal_ne_top
      (hH_convex := hH_convex) (hWitness := hWitness)
      (fun j : Fin n => z (Fin.castAdd m j))
      (fun i : Fin m => z (Fin.natAdd n i))
  simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using hAdjNeTop

/-- Helper for Corollary 38.5.1: one primal point where `GF` is not `⊤` already forces
all packaged values of `(GF)^*` to avoid `⊤`. This is just the specialized `H := GF` form of the
generic packaged-adjoint estimate and keeps later properness arguments in the current notation. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_ne_top_of_compose_exists_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hComposeWitness :
      ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal)) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≠ (⊤ : EReal) := by
  exact
    helperForCorollary_38_5_1_packagedAdjoint_ne_top_of_exists_primal_ne_top
      (hH_convex := hComposeConvex) (hWitness := hComposeWitness)

/-- Helper for Corollary 38.5.1: to obtain the Chapter 6 no-`⊥` graph condition for the packaged
adjoint of `GF`, it is enough to know that the primal composition `GF` is convex and has one
point where it is not `⊤`. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_compose_exists_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hComposeWitness :
      ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal)) :
    ∀ z : Fin (p + m) → ℝ,
      (-bifunctionGraphFunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) z) ≠
          (⊥ : EReal) := by
  exact
    helperForCorollary_38_5_1_negGraph_ne_bot_of_packagedAdjoint_exists_primal_ne_top
      (hH_convex := hComposeConvex) (hWitness := hComposeWitness)

/-- Helper for Corollary 38.5.1: if one packaged-adjoint value of `GF` avoids `⊤`, then the
Chapter 6 negated-graph condition follows after extracting the corresponding primal non-`⊤`
witness. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_packagedAdjoint_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    {yStarVec : Fin p → ℝ} {uStarVec : Fin m → ℝ}
    (hAdjointNeTop :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊤ : EReal)) :
    ∀ z : Fin (p + m) → ℝ,
      (-bifunctionGraphFunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) z) ≠
          (⊥ : EReal) := by
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_compose_exists_ne_top
      (F := F) (G := G) (hComposeConvex := hComposeConvex)
      (helperForCorollary_38_5_1_compose_exists_ne_top_of_packagedAdjointCompose_ne_top
        (F := F) (G := G) (hComposeConvex := hComposeConvex) hAdjointNeTop)

/-- Helper for Corollary 38.5.1: once `GF` has attained primal values everywhere and one packaged
adjoint value avoids `⊤`, the primal composition is proper convex in the Chapter 6 graph sense. -/
lemma helperForCorollary_38_5_1_compose_properConvex_of_attained_and_packagedAdjoint_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hAttained :
      ∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y)
    {yStarVec : Fin p → ℝ} {uStarVec : Fin m → ℝ}
    (hAdjointNeTop :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊤ : EReal)) :
    ProperConvexBifunction (bifunctionCompose G F) := by
  refine ⟨hComposeConvex, ?_⟩
  have hGraphConvexOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (bifunctionGraphFunction (bifunctionCompose G F)) := by
    simpa [ConvexBifunction, ConvexFunction] using hComposeConvex
  have hGraphProperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (bifunctionGraphFunction (bifunctionCompose G F)) := by
    refine ⟨hGraphConvexOn, ?_, ?_⟩
    · rcases
        helperForCorollary_38_5_1_compose_exists_ne_top_of_packagedAdjointCompose_ne_top
          (F := F) (G := G) (hComposeConvex := hComposeConvex) hAdjointNeTop with
        ⟨u, y, hNeTop⟩
      refine
        (nonempty_epigraph_iff_nonempty_effectiveDomain
          (S := Set.univ) (f := bifunctionGraphFunction (bifunctionCompose G F))).2 ?_
      refine ⟨Fin.append u y, ?_⟩
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.2 (by simpa [bifunctionGraphFunction] using hNeTop)⟩
    · intro z _hz
      let u : Fin m → ℝ := fun i => z (Fin.castAdd p i)
      let y : Fin p → ℝ := fun j => z (Fin.natAdd m j)
      rcases hAttained u y with ⟨x, hx⟩
      have hFNeBot : F.toFun u x ≠ (⊥ : EReal) := F.proper.1 u x
      have hGNeBot : G.toFun x y ≠ (⊥ : EReal) := G.proper.1 x y
      simpa [bifunctionGraphFunction, u, y, hx, hFNeBot, hGNeBot]
  exact
    helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn hGraphProperOn

/-- Helper for Corollary 38.5.1: under the same attained-primal hypothesis, one packaged-adjoint
non-`⊤` witness already upgrades the packaged adjoint of `GF` to proper concavity. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_proper_of_attained_and_packagedAdjoint_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hAttained :
      ∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y)
    {yStarVec : Fin p → ℝ} {uStarVec : Fin m → ℝ}
    (hAdjointNeTop :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ yStarVec uStarVec ≠
        (⊤ : EReal)) :
    ProperConcaveBifunction
      (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) := by
  have hComposeProper :
      ProperConvexBifunction (bifunctionCompose G F) :=
    helperForCorollary_38_5_1_compose_properConvex_of_attained_and_packagedAdjoint_ne_top
      (F := F) (G := G) (hComposeConvex := hComposeConvex) (hAttained := hAttained)
      hAdjointNeTop
  exact
    (((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := bifunctionCompose G F)).1 hComposeConvex).2.1).2 hComposeProper

/-- Helper for Corollary 38.5.1: if the primal composition `GF` is attained everywhere and has
one point where it is not `⊤`, then the packaged adjoint `(GF)^*` is already proper concave. This
repackages the generic properness upgrade entirely in the current compose notation. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_proper_of_attained_and_compose_exists_ne_top
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hAttained :
      ∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
        ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y)
    (hComposeWitness :
      ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal)) :
    ProperConcaveBifunction
      (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) := by
  have hAdjointNeTopAll :=
    helperForCorollary_38_5_1_packagedAdjointCompose_ne_top_of_compose_exists_ne_top
      (F := F) (G := G) (hComposeConvex := hComposeConvex) hComposeWitness
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_proper_of_attained_and_packagedAdjoint_ne_top
      (F := F) (G := G) (hComposeConvex := hComposeConvex) (hAttained := hAttained)
      (yStarVec := 0) (uStarVec := 0) (hAdjointNeTop := hAdjointNeTopAll 0 0)

/-- Helper for Corollary 38.5.1: for the packaged adjoint of `GF`, closedness alone is enough for
the Chapter 6 concave-closure fixed-point theorem once the negated graph never hits `⊥`. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_negGraph_ne_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hPackagedAdjointNegGraphNeBot :
      ∀ z : Fin (p + m) → ℝ,
        (-bifunctionGraphFunction
          (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) z) ≠
            (⊥ : EReal)) :
    concaveBifunctionClosure
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  have hClosedConcave :
      ClosedConcaveBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) :=
    helperForCorollary_38_5_1_packagedAdjointCompose_closedConcave
      (F := F) (G := G) (hComposeConvex := hComposeConvex)
  -- The closed Chapter 6 fixed-point theorem is the exact packaged result once the negated graph
  -- is known to avoid `⊥`.
  exact
    helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed_of_neg_graph_ne_bot
      (hClosed := hClosedConcave)
      (hNegGraphNeBot := hPackagedAdjointNegGraphNeBot)

/-- Helper for Corollary 38.5.1: once the packaged adjoint of `GF` is known to be proper on the
concave side, Theorem 6.30.11 fixes it under the Chapter 6 concave closure. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hPackagedAdjointProper :
      ProperConcaveBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩)) :
    concaveBifunctionClosure
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  have hClosedConcave :
      ClosedConcaveBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) :=
    helperForCorollary_38_5_1_packagedAdjointCompose_closedConcave
      (F := F) (G := G) (hComposeConvex := hComposeConvex)
  have hNegGraphNeBot :
      ∀ z : Fin (p + m) → ℝ,
        (-bifunctionGraphFunction
          (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) z) ≠
            (⊥ : EReal) := by
    exact
      helperForCorollary_38_5_1_negGraph_ne_bot_of_properConcave
        hPackagedAdjointProper
  -- Route correction: factor the old closed-proper argument through the smaller closed-plus-no-`⊥`
  -- statement, because that is the exact Chapter 6 input needed later.
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_negGraph_ne_bot
      (F := F) (G := G) (hComposeConvex := hComposeConvex)
      (hPackagedAdjointNegGraphNeBot := hNegGraphNeBot)


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis for the
original pair `(F, G)`, the packaged adjoint of `GF` already satisfies the Chapter 6 negated-graph
non-`⊥` condition. This isolates the exact fixed-point input needed later from the remaining
Chapter 38 closure transport. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ z : Fin (p + m) → ℝ,
      (-bifunctionGraphFunction
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) z) ≠
          (⊥ : EReal) := by
  rcases helperForTheorem_38_5_compose_exists_ne_top_of_hri
      (F := F) (G := G) hri with ⟨u0, y0, hWitness⟩
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_compose_exists_ne_top
      (F := F) (G := G) (hComposeConvex := hComposeConvex) ⟨u0, y0, hWitness⟩

/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
packaged adjoint of `GF` is fixed by the Chapter 6 concave closure without any extra local
hypotheses. This packages the whole Chapter 6 fixed-point half of the argument in theorem-local
coordinates. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    concaveBifunctionClosure
        (adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  have hNegGraphNeBot :=
    helperForCorollary_38_5_1_packagedAdjointCompose_negGraph_ne_bot_of_theorem_hri
      (F := F) (G := G) (hComposeConvex := hComposeConvex) hri
  exact
    helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_negGraph_ne_bot
      (F := F) (G := G) (hComposeConvex := hComposeConvex)
      (hPackagedAdjointNegGraphNeBot := hNegGraphNeBot)

/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
Chapter 6 inequality `concaveBifunctionClosure (F^* G^*) ≤ (GF)^*` follows without separately
carrying any packaged properness witness. -/
lemma helperForCorollary_38_5_1_packagedComposeSupConcaveClosure_le_packagedAdjointCompose_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    concaveBifunctionClosure
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
    simpa [Kpkg, Acomp] using
      helperForCorollary_38_5_1_packagedComposeSup_le_packagedAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (y := y) (u := u)
  have hFixedAcomp : concaveBifunctionClosure Acomp = Acomp := by
    simpa [Acomp] using
      helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_theorem_hri
        (F := F) (G := G) (hComposeConvex := hComposeConvex) hri
  have hClosureLe : concaveBifunctionClosure Kpkg ≤ concaveBifunctionClosure Acomp :=
    helperForCorollary_38_5_1_concaveBifunctionClosure_mono hRaw
  calc
    concaveBifunctionClosure Kpkg y u ≤ concaveBifunctionClosure Acomp y u := hClosureLe y u
    _ = Acomp y u := by simpa [hFixedAcomp]


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
entire Chapter 6 closure statement is already an equality in packaged coordinates, not merely the
inequality `concaveBifunctionClosure (F^* G^*) ≤ (GF)^*`. This isolates the remaining gap in the
corollary to the Chapter 38 closure transport alone. -/
lemma helperForCorollary_38_5_1_packagedComposeSupConcaveClosure_eq_packagedAdjointCompose_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    concaveBifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  let Kpkg : (Fin p → ℝ) → (Fin m → ℝ) → EReal := fun y u =>
    ⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u
  let Acomp : (Fin p → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩
  have hRawEq : Kpkg = Acomp := by
    simpa [Kpkg, Acomp] using
      helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri)
  have hFixedAcomp : concaveBifunctionClosure Acomp = Acomp := by
    simpa [Acomp] using
      helperForCorollary_38_5_1_packagedAdjointCompose_fixed_by_concaveClosure_of_theorem_hri
        (F := F) (G := G) (hComposeConvex := hComposeConvex) hri
  calc
    concaveBifunctionClosure Kpkg = concaveBifunctionClosure Acomp := by simpa [hRawEq]
    _ = Acomp := hFixedAcomp
    _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by rfl

/- The following legacy block used `bifunctionClosure`, the lower-semicontinuous convex minorant.
For the concave product `F⁺G⁺` this is the wrong closure polarity: Rockafellar's `cl` is the
upper-semicontinuous concave closure.  Keep the old exploration out of the environment while the
correct packaged theorem below records the source statement. -/
/-
/-- Helper for Corollary 38.5.1: in packaged finite coordinates, the closure of the packaged
supremal composition `F^* G^*` should be the packaged adjoint of `GF`. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
      bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) y u := by
  let Kpkg : (Fin p → ℝ) → (Fin m → ℝ) → EReal := fun y u =>
    ⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u
  let Acomp : (Fin p → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩
  -- Route correction: this reverse inequality is only expected under the closed/proper plus
  -- qualification hypotheses from Corollary 38.5.1, exactly as in the text. The Chapter 6 side is
  -- now reduced to completed pieces: the packaged adjoint is fixed by
  -- `concaveBifunctionClosure`, and monotonicity already gives
  -- `helperForCorollary_38_5_1_packagedComposeSupConcaveClosure_le_packagedAdjointCompose`.
  -- The witness side of the transport is likewise discharged: the original corollary
  -- qualification already gives `helperForCorollary_38_5_1_compose_ne_bot_of_hri`, so the
  -- reversed-dual operator transport no longer leaves an unresolved `⊥`/properness branch.
  -- The raw inverse transport has also now been isolated in the provable one-sided estimate
  -- `helperForCorollary_38_5_1_packagedAdjointInverseCompose_le_inverse_packagedComposeSup`:
  -- the remaining gap is no longer how to rewrite `inverse (F^* G^*)`, but how to transport the
  -- closure operator itself. What remains is the actual operator comparison: transporting the Chapter 38 closure
  -- `bifunctionClosure` on the packaged dual composition to the corresponding Chapter 6 packaged
  -- `concaveBifunctionClosure` statement under the signed finite-dimensional identifications.
  -- Concretely, the current file now isolates both closure fixed-point halves separately:
  -- 1. on the Chapter 6 side, `concaveBifunctionClosure Kpkg ≤ Acomp`;
  -- 2. on the Chapter 38 side, if one can prove that `Acomp` is product lower semicontinuous and
  --    nowhere `⊥`, then
  --    `helperForCorollary_38_5_1_packagedAdjointCompose_bifunctionClosure_eq_self_of_productLowerSemicontinuous_of_no_bot`
  --    fixes `bifunctionClosure Acomp = Acomp`.
  -- The theorem-local raw comparison itself is no longer missing: under the primal qualification
  -- hypothesis, `helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri`
  -- gives the finite packaged identity `Kpkg = Acomp`, and
  -- `helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSup_of_theorem_hri`
  -- isolates its reverse inequality pointwise before any closure operator appears. In fact, the
  -- theorem-local closure upgrade has now also been factored out: if upstream later supplies the
  -- Chapter 38 inputs `Acomp` product-lsc and `Kpkg` nowhere `⊥`, then
  -- `helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure_of_theorem_hri_of_lsc_of_no_bot`
  -- finishes the reverse closure comparison immediately.
  -- What is still missing is the actual uniqueness/transport theorem from the original text:
  -- a dependency-closed bridge turning the corollary's dual-domain qualification into equality on
  -- the common relative interior of the non-`⊥` graph domain, and then into the reverse Chapter 38
  -- comparison `Acomp ≤ bifunctionClosure Kpkg`.
  -- Equivalently, the remaining work is to prove the specialized transport package for `Kpkg` and
  -- `Acomp` consisting of:
  -- 1. a description of the common `ri` non-`⊥` graph domain after the signed coordinate transport;
  -- 2. transport from the corollary dual `ri` hypothesis to the theorem-local raw equality on that
  --    transported `ri`;
  -- 3. the resulting Chapter 38 closure-uniqueness theorem identifying `bifunctionClosure Kpkg`
  --    with the closed packaged adjoint `Acomp`.
  have hFullDomainsFromAnyReverseProof :
      (∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ, Acomp y u ≤ bifunctionClosure Kpkg y u) →
        (∀ y : Fin p → ℝ,
            y ∈ bifunctionDomBot
              (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) ∧
          (∀ u : Fin m → ℝ,
            u ∈ bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩))) := by
    intro hReverse
    -- Package the row and column obstructions into one full-domain consequence.
    simpa [Acomp, Kpkg] using
      helperForCorollary_38_5_1_reverseClosureComparison_forces_full_domains
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) hReverse
  have hFullCurrentSwappedDomainsFromAnyReverseProof :
      (∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ, Acomp y u ≤ bifunctionClosure Kpkg y u) →
        (∀ yStar : Module.Dual ℝ (Fin p → ℝ),
            yStar ∈ bifunctionDomBot (bifunctionAdjoint G.toFun)) ∧
          (∀ uStar : Module.Dual ℝ (Fin m → ℝ),
            uStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint F.toFun))) := by
    intro hReverse
    simpa [Acomp, Kpkg] using
      helperForCorollary_38_5_1_reverseClosureComparison_forces_full_currentSwappedDualDomains
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) hReverse
  -- TODO: this local file can only finish after an earlier dependency supplies one of the two
  -- now-normalized missing ingredients:
  -- 1. a direct reverse comparison
  --    `adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ ≤ bifunctionClosure Kpkg`;
  -- 2. a theorem upgrading the corollary hypotheses to full current dual domains
  --    `∀ xStar, xStar ∈ domBot F^*` and `∀ xStar, xStar ∈ dom G^*_*`, after which
  --    `helperForCorollary_38_5_1_hri_of_full_currentDualDomains` makes the dual `ri`
  --    assumption automatic.
  -- Without one of those upstream inputs, the obstruction lemmas above show that any local proof
  -- attempt here can only rename the same missing bridge. In particular, any successful reverse
  -- comparison would already force full current dual domains for the swapped pair `(G^*, F^*_*)`,
  -- not merely their packaged coordinate images. But this obstruction cannot by itself be turned
  -- into a new `ri` hypothesis of the original corollary form: `dom G^*` lives in
  -- `Module.Dual ℝ (Fin p → ℝ)` while `dom F^*_ *` lives in `Module.Dual ℝ (Fin m → ℝ)`, so those
  -- swapped domains do not lie in a common ambient space and therefore do not support the same
  -- intersection-based qualification statement.
  let _ := hFullDomainsFromAnyReverseProof
  let _ := hFullCurrentSwappedDomainsFromAnyReverseProof
  legacy_unresolved

/-- Helper for Corollary 38.5.1: in packaged finite coordinates, the closure of the packaged
supremal composition `F^* G^*` should be the packaged adjoint of `GF`. -/
lemma helperForCorollary_38_5_1_packagedComposeSupClosure_eq_packagedAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  let Kpkg : (Fin p → ℝ) → (Fin m → ℝ) → EReal := fun y u =>
    ⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u
  let Acomp : (Fin p → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩
  have hUpper : bifunctionClosure Kpkg ≤ Acomp := by
    intro y u
    -- This is the easy half: `cl (F^* G^*)` stays below `F^* G^*`, and weak duality gives
    -- `F^* G^* ≤ (GF)^*`.
    simpa [Kpkg, Acomp] using
      helperForCorollary_38_5_1_packagedComposeSupClosure_le_packagedAdjointCompose
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (y := y) (u := u)
  -- Split the equality into the finished easy half and the unresolved reverse inequality so the
  -- remaining blocker is isolated to a single pointwise Chapter 6 bridge.
  apply le_antisymm
  · exact hUpper
  · intro y u
    -- The reverse inequality is exactly the packaged pointwise blocker recorded above.
    simpa [Kpkg, Acomp] using
      helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSupClosure
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) (hri := hri)
        (y := y) (u := u)

/-- Helper for Corollary 38.5.1: the packaged Chapter 6 adjoint of `GF`, evaluated in Euclidean
coordinates, is exactly the current Chapter 38 adjoint after the signed `dotProductEquiv`
identification. -/
lemma helperForCorollary_38_5_1_currentAdjointCompose_eq_packagedAdjointCompose_under_signedHomeomorph
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F)) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ =
      fun y u =>
        bifunctionAdjoint (bifunctionCompose G F)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
  -- This is the standard packaged-to-current adjoint rewrite, specialized to the composed
  -- bifunction `GF`.
  exact
    helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
      (F := bifunctionCompose G F) hComposeConvex

/-- Helper for Corollary 38.5.1: the packaged-coordinate closure of `F^* G^*` is exactly the
current Chapter 38 closure after precomposing with the signed Euclidean/dual homeomorphism. -/
lemma helperForCorollary_38_5_1_currentClosureComposeSup_eq_packagedClosure_under_signedHomeomorph
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      fun y u =>
        bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
  -- Commute `bifunctionClosure` with the signed product homeomorphism on the two dual factors.
  calc
    bifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      bifunctionClosure
        (fun y u =>
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            ((helperForCorollary_38_5_1_signedDotProductHomeomorph p) y)
            ((helperForCorollary_38_5_1_signedDotProductHomeomorph m) u)) := by
            -- First rewrite the raw packaged composition pointwise into the current Chapter 38
            -- composition evaluated at the signed dual images.
            congr 1
            funext y u
            simpa [helperForCorollary_38_5_1_signedDotProductHomeomorph] using
              (helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
                (F := F) (G := G)
                (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
                (y := y) (u := u)).symm
    _ = fun y u =>
        bifunctionClosure
          (bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun))
          ((helperForCorollary_38_5_1_signedDotProductHomeomorph p) y)
          ((helperForCorollary_38_5_1_signedDotProductHomeomorph m) u) := by
            -- Then transport the closure itself through the same product homeomorphism.
            exact
              helperForCorollary_38_5_1_bifunctionClosure_precomp_homeomorph
                (eU := helperForCorollary_38_5_1_signedDotProductHomeomorph p)
                (eX := helperForCorollary_38_5_1_signedDotProductHomeomorph m)
                (F := bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun)
                  (bifunctionAdjoint G.toFun))



-/

/-- Corollary 38.5.1, packaged closure identity.  Under the dual relative-interior
qualification, apply Theorem 38.5 to the inverses of the two closed adjoints.  Their composition
is the inverse of the concave product `F⁺G⁺`; hence biconjugation identifies the adjoint of `GF`
with the upper-semicontinuous concave closure of that product. -/
lemma helperForCorollary_38_5_1_packagedComposeSupConcaveClosure_eq_packagedAdjointCompose
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    concaveBifunctionClosure
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  let AF : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩
  let AG : (Fin p → ℝ) → (Fin n → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩
  let K : (Fin p → ℝ) → (Fin m → ℝ) → EReal :=
    fun y u => ⨆ x : Fin n → ℝ, AG y x + AF x u
  have hTransportedHri :
      (intrinsicInterior ℝ (bifunctionDomBot AF) ∩
          intrinsicInterior ℝ (bifunctionDom (bifunctionInverse AG))).Nonempty := by
    simpa [AF, AG] using
      helperForCorollary_38_5_1_signedDotProductEquiv_hri_transport
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri
  rcases
      helperForCorollary_38_5_1_reversedDual_theorem38_5_application
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) hTransportedHri with
    ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper,
      hGdualInv_eq, hGdualInv_proper, hReversedEq, _hAttained⟩
  let R : (Fin m → ℝ) → (Fin p → ℝ) → EReal :=
    bifunctionCompose GdualInv FdualInv
  have hRconvex : ConvexBifunction R := by
    exact
      (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
        (F := FdualInv) (G := GdualInv) hFdualInv_proper hGdualInv_proper).1
  have hInverseK : bifunctionInverse K = R := by
    funext u y
    have hNegSup :
        -(⨆ x : Fin n → ℝ, AG y x + AF x u) =
          ⨅ x : Fin n → ℝ, -(AG y x + AF x u) := by
      have h := congrArg Neg.neg
        (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
          (fun x : Fin n → ℝ => -(AG y x + AF x u)))
      simpa using h.symm
    simp only [bifunctionInverse, K]
    rw [hNegSup]
    simp only [R, bifunctionCompose]
    refine iInf_congr ?_
    intro x
    have hNeg := helperForProposition_38_4_2_neg_add_of_neBot
      (FdualInv.proper.1 u x) (GdualInv.proper.1 x y)
    have hNegNeg := congrArg Neg.neg hNeg
    simpa [hFdualInv_eq, hGdualInv_eq, bifunctionInverse, AF, AG, add_comm] using hNegNeg.symm
  have hInverseKConvex : ConvexBifunction (bifunctionInverse K) := by
    simpa [hInverseK] using hRconvex
  let swapMap : (Fin (p + m) → ℝ) →ₗ[ℝ] (Fin (m + p) → ℝ) :=
    { toFun := fun z =>
        Fin.append (fun i : Fin m => z (Fin.natAdd p i))
          (fun j : Fin p => z (Fin.castAdd m j))
      map_add' := by
        intro z₁ z₂
        ext i
        cases i using Fin.addCases <;> simp [Pi.add_apply]
      map_smul' := by
        intro a z
        ext i
        cases i using Fin.addCases <;> simp [Pi.smul_apply] }
  have hKconcave : ConcaveBifunction K := by
    have hPre :=
      convexFunctionOn_precomp_linearMap swapMap
        (bifunctionGraphFunction (bifunctionInverse K))
        (by simpa [ConvexBifunction, ConvexFunction] using hInverseKConvex)
    simpa [ConcaveBifunction, ConvexFunction, swapMap, bifunctionGraphFunction,
      bifunctionInverse] using hPre
  have hFBiadjEq : biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ = F.toFun :=
    (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed)).1
  have hGBiadjEq : biadjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ = G.toFun :=
    (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hF_closed := hF_closed) (hG_closed := hG_closed)).2
  have hAdjointR :
      adjointOfConvexBifunction ⟨R, hRconvex⟩ =
        bifunctionInverse (bifunctionCompose G F) := by
    funext y u
    calc
      adjointOfConvexBifunction ⟨R, hRconvex⟩ y u =
          bifunctionAdjoint R (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin m) (-u)) := by
              exact congrFun (congrFun
                (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                  (F := R) hRconvex) y) u
      _ = bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
          (bifunctionAdjoint GdualInv.toFun) (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin m) (-u)) := by
              have hAt := congrFun (congrFun hReversedEq
                (dotProductEquiv ℝ (Fin p) (-y))) (dotProductEquiv ℝ (Fin m) (-u))
              simpa [R] using hAt
      _ = -bifunctionCompose G F u y :=
        helperForCorollary_38_5_1_reversedDual_output_rewrite_at_primalPair
          (F := F) (G := G)
          (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
          (hFdualInv_eq := hFdualInv_eq) (hFdualInv_proper := hFdualInv_proper)
          (hGdualInv_eq := hGdualInv_eq) (hGdualInv_proper := hGdualInv_proper)
          (hFBiadjEq := hFBiadjEq) (hGBiadjEq := hGBiadjEq) u y
      _ = bifunctionInverse (bifunctionCompose G F) y u := rfl
  have hInverseAdjointK :
      bifunctionInverse (adjointOfConcaveBifunction ⟨K, hKconcave⟩) =
        bifunctionInverse (bifunctionCompose G F) := by
    calc
      bifunctionInverse (adjointOfConcaveBifunction ⟨K, hKconcave⟩) =
          adjointOfConvexBifunction ⟨bifunctionInverse K, hInverseKConvex⟩ :=
        (helperForCorollary_38_5_1_adjointOfInverseConcave_eq_inverseAdjoint
          K hKconcave hInverseKConvex).symm
      _ = adjointOfConvexBifunction ⟨R, hRconvex⟩ := by
        have hSubtype :
            (⟨bifunctionInverse K, hInverseKConvex⟩ :
              {H // ConvexBifunction H}) =
              ⟨R, hRconvex⟩ := by
          apply Subtype.ext
          exact hInverseK
        exact congrArg adjointOfConvexBifunction hSubtype
      _ = bifunctionInverse (bifunctionCompose G F) := hAdjointR
  have hAdjointK :
      adjointOfConcaveBifunction ⟨K, hKconcave⟩ = bifunctionCompose G F := by
    funext u y
    have hAt := congrFun (congrFun hInverseAdjointK y) u
    have hNeg := congrArg Neg.neg hAt
    simpa [bifunctionInverse] using hNeg
  have hBiK :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality (F := K)).2
      hKconcave).2.2.1
  calc
    concaveBifunctionClosure
        (fun y u => ⨆ x : Fin n → ℝ, AG y x + AF x u) =
        concaveBifunctionClosure K := by rfl
    _ = biadjointOfConcaveBifunction ⟨K, hKconcave⟩ := hBiK.symm
    _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
      simp [biadjointOfConcaveBifunction, adjointOfConcaveBifunctionAsConvex, hAdjointK]
    _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := rfl

end Section38
end Chap08
