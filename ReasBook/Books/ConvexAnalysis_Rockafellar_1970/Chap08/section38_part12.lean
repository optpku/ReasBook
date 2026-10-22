/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part11

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Corollary 38.5.1: a continuous linear equivalence transports intrinsic interiors in
the ambient additive-torsor topology. -/
lemma helperForCorollary_38_5_1_continuousLinearEquiv_image_intrinsicInterior
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul ℝ F]
    (e : E ≃L[ℝ] F) (s : Set E) :
    intrinsicInterior ℝ (e '' s) = e '' intrinsicInterior ℝ s := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ s
  let B : AffineSubspace ℝ F := affineSpan ℝ (e '' s)
  have hAB : ∀ x : E, x ∈ A ↔ e x ∈ B := by
    intro x
    -- The affine span commutes with the linear equivalence, so membership transports directly.
    have hmap : A.map e.toAffineEquiv.toAffineMap = B := by
      simpa [A, B] using
        (AffineSubspace.map_span (k := ℝ) (f := e.toAffineEquiv.toAffineMap) s)
    simpa [hmap] using
      (AffineSubspace.mem_map_iff_mem_of_injective
        (f := e.toAffineEquiv.toAffineMap) (x := x) (s := A) (hf := e.injective)).symm
  let f : A ≃ₜ B :=
    e.toHomeomorph.subtype (p := fun x : E => x ∈ A) (q := fun y : F => y ∈ B) hAB
  have hcoe : (fun y : B => (y : F)) = fun y => e ((f.symm y : A) : E) := by
    ext y
    -- The subtype homeomorphism is induced by the ambient continuous linear equivalence.
    simp [f, Homeomorph.subtype]
  have hpre :
      ((↑) : B → F) ⁻¹' (e '' s) = f.symm ⁻¹' (((↑) : A → E) ⁻¹' s) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      have : (f.symm y : A) = ⟨x, by
          have hxA : x ∈ A := subset_affineSpan (k := ℝ) (s := s) hx
          simpa [A] using hxA⟩ := by
        ext
        simpa using (congrArg e.symm hxy).symm
      have hxpre : (f.symm y : E) ∈ s := by
        simpa [this] using hx
      simpa [hcoe] using hxpre
    · intro hy
      have : e ((f.symm y : A) : E) ∈ e '' s :=
        ⟨(f.symm y : E), by simpa using hy, rfl⟩
      simpa [hcoe] using this
  -- Rewrite both intrinsic interiors inside the affine spans and transport the ordinary interior
  -- through the subtype homeomorphism induced by `e`.
  calc
    intrinsicInterior ℝ (e '' s)
        = ((↑) : B → F) '' interior (((↑) : B → F) ⁻¹' (e '' s)) := by
            simp [intrinsicInterior, B]
    _ = (fun y : B => e ((f.symm y : A) : E)) '' interior (((↑) : B → F) ⁻¹' (e '' s)) := by
          simp [hcoe]
    _ = e '' (((↑) : A → E) '' (f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)))) := by
          simp [Set.image_image]
    _ = e '' (((↑) : A → E) '' interior (((↑) : A → E) ⁻¹' s)) := by
          have :
              f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)) =
                interior (((↑) : A → E) ⁻¹' s) := by
            have himage :
                f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)) =
                  interior (f.symm '' (((↑) : B → F) ⁻¹' (e '' s))) := by
              simpa using (f.symm.image_interior (((↑) : B → F) ⁻¹' (e '' s)))
            have himage2 :
                f.symm '' (((↑) : B → F) ⁻¹' (e '' s)) = (((↑) : A → E) ⁻¹' s) := by
              ext x
              constructor
              · rintro ⟨y, hy, rfl⟩
                simpa [hpre] using hy
              · intro hx
                refine ⟨f x, ?_, by simp⟩
                simpa [hpre] using hx
            simpa [himage2] using himage
          simp [this]
    _ = e '' intrinsicInterior ℝ s := by
          simp [intrinsicInterior, A]

/-- Helper for Corollary 38.5.1: the signed Euclidean/dual identification sends intrinsic-interior
points in the weak dual to intrinsic-interior points of the corresponding coordinate image. -/
lemma helperForCorollary_38_5_1_mem_intrinsicInterior_signedDotProductImage
    {n : Nat} {S : Set (Module.Dual ℝ (Fin n → ℝ))}
    {xStar : Module.Dual ℝ (Fin n → ℝ)}
    (hxStar : xStar ∈ intrinsicInterior ℝ S) :
    -((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
      intrinsicInterior ℝ
        (((fun z : Module.Dual ℝ (Fin n → ℝ) => -((dotProductEquiv ℝ (Fin n)).symm z)) '' S)) := by
  -- Recreate the weak-topology algebraic structure needed to turn the finite-dimensional linear
  -- equivalence into a continuous linear equivalence.
  haveI : T2Space (Module.Dual ℝ (Fin n → ℝ)) := by
    let f : Module.Dual ℝ (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) := fun φ x => φ x
    have hf : Topology.IsEmbedding f := by
      refine
        (WeakBilin.isEmbedding
          (B := (LinearMap.applyₗ (R := ℝ) (M := Fin n → ℝ) (M₂ := ℝ)).flip) ?_)
      intro φ ψ h
      ext y
      simpa [LinearMap.applyₗ] using LinearMap.congr_fun h (Pi.single y (1 : ℝ))
    exact hf.t2Space
  haveI : ContinuousAdd (Module.Dual ℝ (Fin n → ℝ)) := by
    let B : (Module.Dual ℝ (Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.applyₗ (R := ℝ) (M := Fin n → ℝ) (M₂ := ℝ)).flip
    change ContinuousAdd (WeakBilin B)
    infer_instance
  haveI : IsTopologicalAddGroup (Module.Dual ℝ (Fin n → ℝ)) := by
    let B : (Module.Dual ℝ (Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.applyₗ (R := ℝ) (M := Fin n → ℝ) (M₂ := ℝ)).flip
    change IsTopologicalAddGroup (WeakBilin B)
    infer_instance
  haveI : ContinuousSMul ℝ (Module.Dual ℝ (Fin n → ℝ)) := by
    let B : (Module.Dual ℝ (Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.applyₗ (R := ℝ) (M := Fin n → ℝ) (M₂ := ℝ)).flip
    change ContinuousSMul ℝ (WeakBilin B)
    infer_instance
  let signedDotProductEquiv : Module.Dual ℝ (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (((dotProductEquiv ℝ (Fin n)).symm).trans (LinearEquiv.neg ℝ)).toContinuousLinearEquiv
  have hxImage :
      signedDotProductEquiv xStar ∈ intrinsicInterior ℝ (signedDotProductEquiv '' S) := by
    rw [helperForCorollary_38_5_1_continuousLinearEquiv_image_intrinsicInterior
      (e := signedDotProductEquiv) (s := S)]
    exact ⟨xStar, hxStar, rfl⟩
  change signedDotProductEquiv xStar ∈ intrinsicInterior ℝ (signedDotProductEquiv '' S)
  exact hxImage

/-- Helper for Corollary 38.5.1: the given weak-topology intrinsic-interior hypothesis on the
Chapter 38 dual domains transports to the coordinate-space qualification needed for the reversed
dual theorem-38.5 inputs. -/
lemma helperForCorollary_38_5_1_signedDotProductEquiv_hri_transport
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    (intrinsicInterior ℝ
          (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
        intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty := by
  rcases hri with ⟨xStar, hxF, hxG⟩
  refine ⟨-((dotProductEquiv ℝ (Fin n)).symm xStar), ?_, ?_⟩
  · -- Transport the `dom F^*` witness through the signed Euclidean/dual identification and then
    -- rewrite the target set using the packaged-adjoint domain formula proved above.
    have hxTransport :
        -((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
          intrinsicInterior ℝ
            ((fun z : Module.Dual ℝ (Fin n → ℝ) =>
                -((dotProductEquiv ℝ (Fin n)).symm z)) '' bifunctionDomBot
                  (bifunctionAdjoint F.toFun)) :=
      helperForCorollary_38_5_1_mem_intrinsicInterior_signedDotProductImage hxF
    rw [helperForCorollary_38_5_1_vectorizedAdjoint_domBot_eq_signedImage
      (F := F) (hF_properConvex := hF_properConvex)]
    exact hxTransport
  · -- The same signed transport works for the `dom G^*_ *` witness after replacing `domBot` by
    -- `dom` and invoking the corresponding inverse-adjoint set identity.
    have hxTransport :
        -((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
          intrinsicInterior ℝ
            ((fun z : Module.Dual ℝ (Fin n → ℝ) =>
                -((dotProductEquiv ℝ (Fin n)).symm z)) '' bifunctionDom
                  (bifunctionInverse (bifunctionAdjoint G.toFun))) :=
      helperForCorollary_38_5_1_mem_intrinsicInterior_signedDotProductImage hxG
    rw [helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_eq_signedImage
      (G := G) (hG_properConvex := hG_properConvex)]
    exact hxTransport

/-- Helper for Corollary 38.5.1: the transported qualification hypothesis can be unpacked into a
concrete coordinate-space middle dual point together with one packaged `F^*` witness avoiding
`⊤` and one packaged `G^*` witness avoiding `⊥`. This is the exact data later Chapter 31 / finite-
branch arguments need. -/
lemma helperForCorollary_38_5_1_transported_hri_concrete_witnesses
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hTransportedHri :
      (intrinsicInterior ℝ
            (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty) :
    ∃ xStarVec : Fin n → ℝ, ∃ uStarVec : Fin m → ℝ, ∃ yStarVec : Fin p → ℝ,
      xStarVec ∈ intrinsicInterior ℝ
          (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∧
      xStarVec ∈ intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverse
              (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))) ∧
      adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ xStarVec uStarVec ≠ (⊥ : EReal) ∧
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec xStarVec ≠ (⊥ : EReal) := by
  rcases hTransportedHri with ⟨xStarVec, hxF, hxG⟩
  have hxF_mem :
      xStarVec ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) :=
    intrinsicInterior_subset (𝕜 := ℝ)
      (s := bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) hxF
  have hxG_mem :
      xStarVec ∈ bifunctionDom
        (bifunctionInverse
          (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) :=
    intrinsicInterior_subset (𝕜 := ℝ)
      (s := bifunctionDom
        (bifunctionInverse
          (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))) hxG
  rcases hxF_mem with ⟨uStarVec, huStarVec⟩
  rcases hxG_mem with ⟨yStarVec, hyStarVec⟩
  exact ⟨xStarVec, uStarVec, yStarVec, hxF, hxG, huStarVec, by
    simpa [bifunctionDom, bifunctionInverse] using hyStarVec⟩

/-- Helper for Corollary 38.5.1: one middle vector whose two packaged adjoint summands both avoid
`⊥` already forces the corresponding packaged supremal composition value to avoid `⊥` as well. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_middle_non_bot
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (xStarVec : Fin n → ℝ) (uStarVec : Fin m → ℝ) (yStarVec : Fin p → ℝ)
    (hF_ne_bot :
      adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ xStarVec uStarVec ≠ (⊥ : EReal))
    (hG_ne_bot :
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec xStarVec ≠ (⊥ : EReal)) :
    (⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) ≠ (⊥ : EReal) := by
  have hSummand_ne_bot :
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec xStarVec +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ xStarVec uStarVec ≠
        (⊥ : EReal) := by
    -- The chosen middle vector gives one displayed summand that stays strictly above `-∞`.
    exact add_ne_bot_of_notbot hG_ne_bot hF_ne_bot
  intro hBot
  have hLeSummand :
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec xStarVec +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ xStarVec uStarVec ≤
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) := by
    -- Every concrete summand is bounded above by the defining `iSup`.
    exact le_iSup (fun x : Fin n → ℝ =>
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) xStarVec
  have hLeBot :
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec xStarVec +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ xStarVec uStarVec ≤
        (⊥ : EReal) := by
    -- If the supremum collapsed to `⊥`, the chosen summand would collapse with it.
    simpa [hBot] using hLeSummand
  exact hSummand_ne_bot (bot_unique hLeBot)

/-- Helper for Corollary 38.5.1: the transported qualification hypothesis already provides one
finite summand in the packaged supremal composition `F^* G^*`, hence one point where that packaged
composition is not `⊥`. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_transported_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hTransportedHri :
      (intrinsicInterior ℝ
            (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty) :
    ∃ yStarVec : Fin p → ℝ, ∃ uStarVec : Fin m → ℝ,
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) ≠ (⊥ : EReal) := by
  rcases
      helperForCorollary_38_5_1_transported_hri_concrete_witnesses
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        hTransportedHri with
    ⟨xStarVec, uStarVec, yStarVec, _hxF, _hxG, hF_ne_bot, hG_ne_bot⟩
  -- Repackage the transported witness as one concrete middle summand of the displayed `iSup`.
  refine ⟨yStarVec, uStarVec, ?_⟩
  exact
    helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_middle_non_bot
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (xStarVec := xStarVec) (uStarVec := uStarVec) (yStarVec := yStarVec)
      hF_ne_bot hG_ne_bot

/-- Helper for Corollary 38.5.1: the original Chapter 38 qualification hypothesis already gives
one point where the packaged supremal composition `F^* G^*` avoids `⊥`, once the relative-interior
data is transported to the packaged Chapter 6 domains. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionAdjoint F.toFun)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)))).Nonempty) :
    ∃ yStarVec : Fin p → ℝ, ∃ uStarVec : Fin m → ℝ,
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ yStarVec x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x uStarVec) ≠
        (⊥ : EReal) := by
  -- Transport the original Chapter 38 relative-interior assumption to the packaged Chapter 6
  -- qualification sets where the explicit witness theorem is already available.
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
  -- Reuse the transported witness verbatim.
  exact
    helperForCorollary_38_5_1_packagedComposeSup_ne_bot_of_transported_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      hTransportedHri


/-- Helper for Corollary 38.5.1: the closed proper packaged adjoints of `F` and `G` become valid
Theorem 38.5 inputs after inversion, with the required Chapter 6 proper-convex graph packages.
-/
lemma helperForCorollary_38_5_1_packagedAdjointInverse_properConvex_inputs
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun) :
    (∃ FdualInv : FiberwiseProperConvexBifunction m n,
        FdualInv.toFun =
          bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) ∧
        ProperConvexBifunction FdualInv.toFun) ∧
      (∃ GdualInv : FiberwiseProperConvexBifunction n p,
        GdualInv.toFun =
          bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) ∧
        ProperConvexBifunction GdualInv.toFun) := by
  -- Package the closed proper Chapter 6 adjoints, then apply the generic inverse constructor to
  -- each of them separately.
  have hPackagedAdjointF :
      ClosedConcaveBifunction
          (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) ∧
        ProperConcaveBifunction
          (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) :=
    helperForCorollary_38_5_1_packagedAdjoint_closedProperConcave
      (F := F) (hF_properConvex := hF_properConvex) (hF_closed := hF_closed)
  have hPackagedAdjointG :
      ClosedConcaveBifunction
          (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) ∧
        ProperConcaveBifunction
          (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) :=
    helperForCorollary_38_5_1_packagedAdjoint_closedProperConcave
      (F := G) (hF_properConvex := hG_properConvex) (hF_closed := hG_closed)
  constructor
  · -- Apply the generic inverse-packaging lemma to the packaged adjoint of `F`.
    exact
      helperForCorollary_38_5_1_packagedAdjointInverse_fiberwiseProperConvex
        (K := adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)
        hPackagedAdjointF.1 hPackagedAdjointF.2
  · -- Repeat the same inverse-packaging step for `G`.
    exact
      helperForCorollary_38_5_1_packagedAdjointInverse_fiberwiseProperConvex
        (K := adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)
        hPackagedAdjointG.1 hPackagedAdjointG.2

/-- Helper for Corollary 38.5.1: after transporting the qualification hypothesis, Theorem 38.5
applies directly to the inverse packaged adjoints and produces the reversed-dual equality and
attainment package. -/
lemma helperForCorollary_38_5_1_reversedDual_theorem38_5_application
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
    ∃ FdualInv : FiberwiseProperConvexBifunction m n,
      ∃ GdualInv : FiberwiseProperConvexBifunction n p,
        FdualInv.toFun =
            bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) ∧
          ProperConvexBifunction FdualInv.toFun ∧
          GdualInv.toFun =
            bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) ∧
          ProperConvexBifunction GdualInv.toFun ∧
          bifunctionAdjoint (bifunctionCompose GdualInv FdualInv) =
            bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
              (bifunctionAdjoint GdualInv.toFun) ∧
          (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
            ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
              bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
                  (bifunctionAdjoint GdualInv.toFun) yStar uStar =
                bifunctionAdjoint GdualInv.toFun yStar xStar +
                  bifunctionAdjoint FdualInv.toFun xStar uStar) := by
  rcases
      helperForCorollary_38_5_1_packagedAdjointInverse_properConvex_inputs
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) with
    ⟨⟨FdualInv, hFdualInv_eq, hFdualInv_proper⟩, ⟨GdualInv, hGdualInv_eq, hGdualInv_proper⟩⟩
  have hTheorem38_5 :
      ConvexBifunction (bifunctionCompose GdualInv FdualInv) ∧
        ((intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse FdualInv.toFun)) ∩
              intrinsicInterior ℝ (bifunctionDom GdualInv.toFun)).Nonempty →
          bifunctionAdjoint (bifunctionCompose GdualInv FdualInv) =
              bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
                (bifunctionAdjoint GdualInv.toFun) ∧
            (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
              ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
                bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
                    (bifunctionAdjoint GdualInv.toFun) yStar uStar =
                  bifunctionAdjoint GdualInv.toFun yStar xStar +
                    bifunctionAdjoint FdualInv.toFun xStar uStar)) :=
    theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
      (F := FdualInv) (G := GdualInv) hFdualInv_proper hGdualInv_proper
  rcases hTheorem38_5 with ⟨_, hQualified⟩
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
  have hQualifiedOut :
      bifunctionAdjoint (bifunctionCompose GdualInv FdualInv) =
          bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
            (bifunctionAdjoint GdualInv.toFun) ∧
        (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
          ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
            bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
                (bifunctionAdjoint GdualInv.toFun) yStar uStar =
              bifunctionAdjoint GdualInv.toFun yStar xStar +
                bifunctionAdjoint FdualInv.toFun xStar uStar) := by
    -- The transported qualification is exactly the theorem-38.5 hypothesis once the inverse
    -- packaged adjoints are unfolded through the equalities just packaged.
    have hTheorem38_5_hri :
        (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse FdualInv.toFun)) ∩
            intrinsicInterior ℝ (bifunctionDom GdualInv.toFun)).Nonempty := by
      rw [hFdualInv_domBot, hGdualInv_eq]
      exact hTransportedHri
    exact hQualified hTheorem38_5_hri
  exact ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq, hGdualInv_proper,
    hQualifiedOut.1, hQualifiedOut.2⟩

/-- Helper for Corollary 38.5.1: after transporting the qualification hypothesis to the reversed
dual pair, the theorem-local primal non-`⊤` witness lemma applies directly to that pair as well.
This isolates the original-text witness extraction from the remaining closure transport. -/
lemma helperForCorollary_38_5_1_reversedDual_compose_exists_ne_top
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
    ∃ FdualInv : FiberwiseProperConvexBifunction m n,
      ∃ GdualInv : FiberwiseProperConvexBifunction n p,
        FdualInv.toFun =
            bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) ∧
          ProperConvexBifunction FdualInv.toFun ∧
          GdualInv.toFun =
            bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) ∧
          ProperConvexBifunction GdualInv.toFun ∧
          (∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ,
            bifunctionCompose GdualInv FdualInv u y ≠ (⊤ : EReal)) := by
  rcases
      helperForCorollary_38_5_1_reversedDual_theorem38_5_application
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) hTransportedHri with
    ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq, hGdualInv_proper,
      _hReversedEq, _hReversedAttainment⟩
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
  refine ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq, hGdualInv_proper, ?_⟩
  exact
    helperForTheorem_38_5_compose_exists_ne_top_of_hri
      (F := FdualInv) (G := GdualInv) hTheorem38_5_hri

/-- Helper for Corollary 38.5.1: taking the Chapter 6 convex adjoint after inverting a concave
bifunction is the same as inverting its Chapter 6 concave adjoint. -/
lemma helperForCorollary_38_5_1_adjointOfInverseConcave_eq_inverseAdjoint
    {m n : Nat} (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hK_concave : ConcaveBifunction K)
    (hInvProper : ConvexBifunction (bifunctionInverse K)) :
    adjointOfConvexBifunction ⟨bifunctionInverse K, hInvProper⟩ =
      bifunctionInverse (adjointOfConcaveBifunction ⟨K, hK_concave⟩) := by
  -- Expand both Chapter 6 adjoints and rewrite the inverse integrand as the negation of the
  -- corresponding concave-adjoint integrand.
  funext xStar uStar
  let φ : (Fin m → ℝ) × (Fin n → ℝ) → EReal := fun p =>
    K p.2 p.1 - (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))
  have hRange :
      Set.range φ =
        Set.range (fun q : (Fin n → ℝ) × (Fin m → ℝ) =>
          K q.1 q.2 - (((q.2 ⬝ᵥ uStar : ℝ) : EReal)) + (((q.1 ⬝ᵥ xStar : ℝ) : EReal))) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p.2, p.1), rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q.2, q.1), rfl⟩
  calc
    adjointOfConvexBifunction ⟨bifunctionInverse K, hInvProper⟩ xStar uStar =
      iInf (fun p : (Fin m → ℝ) × (Fin n → ℝ) => -φ p) := by
        -- The inverse swaps the variables and negates the value, so the convex-adjoint integrand
        -- is exactly the negative of the concave-adjoint integrand with the arguments reversed.
        rw [adjointOfConvexBifunction, sInf_range]
        refine iInf_congr ?_
        intro p
        have hAffineTop :
            (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) ≠
              (⊤ : EReal) := by
          simpa using (EReal.coe_ne_top (-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar)))
        have hAffineBot :
            (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) ≠
              (⊥ : EReal) := by
          rw [show (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) : EReal) =
                (((-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar) : ℝ) : EReal)) by simp]
          exact EReal.coe_ne_bot (-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar))
        have hAffineNeg :
            -(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) =
              (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (-(((p.2 ⬝ᵥ xStar : ℝ) : EReal))) := by
          simpa [add_comm] using
            (EReal.neg_add
              (x := -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
              (y := (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))
              (h1 := Or.inl (by simp)) (h2 := Or.inr (by simp)))
        have hNegAdd :
            -(K p.2 p.1 + (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) =
              (-(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) +
                (-K p.2 p.1) := by
          simpa [add_comm] using
            (EReal.neg_add
              (x := K p.2 p.1)
              (y := -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))
              (h1 := Or.inr hAffineTop) (h2 := Or.inr hAffineBot))
        calc
          bifunctionInverse K p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
              (((p.1 ⬝ᵥ uStar : ℝ) : EReal))
              = (-K p.2 p.1) +
                  (-(((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
                    simp [bifunctionInverse, sub_eq_add_neg, add_assoc]
          _ = (-(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) +
                (-K p.2 p.1) := by
                  simpa [add_assoc, add_left_comm, add_comm] using
                    (congrArg (fun t : EReal => t + (-K p.2 p.1)) hAffineNeg).symm
          _ = -(K p.2 p.1 + (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) := by
                simpa [add_comm] using hNegAdd.symm
          _ = -φ p := by simp [φ, sub_eq_add_neg, add_assoc]
    _ = -(iSup φ) := by
          simpa using
            congrArg Neg.neg
              (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg (φ := fun p => -φ p))
    _ = -(sSup (Set.range φ)) := by rw [sSup_range]
    _ = -(sSup
          (Set.range (fun q : (Fin n → ℝ) × (Fin m → ℝ) =>
            K q.1 q.2 - (((q.2 ⬝ᵥ uStar : ℝ) : EReal)) + (((q.1 ⬝ᵥ xStar : ℝ) : EReal))))) := by
          rw [hRange]
    _ = bifunctionInverse (adjointOfConcaveBifunction ⟨K, hK_concave⟩) xStar uStar := by
          simp [bifunctionInverse, adjointOfConcaveBifunction]

/-- Helper for Corollary 38.5.1: evaluating the current Chapter 38 adjoint of the inverse
packaged adjoint at the signed Euclidean/dual image of a primal pair gives the negative primal
value. -/
lemma helperForCorollary_38_5_1_inversePackagedAdjoint_packagedAdjoint_eq_inverseBiadjoint
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hInvProper :
      ProperConvexBifunction
        (bifunctionInverse (adjointOfConvexBifunction ⟨(F.toFun : (Fin m → ℝ) → (Fin n → ℝ) → EReal), hF_properConvex.1⟩))) :
    adjointOfConvexBifunction
        ⟨bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩),
          hInvProper.1⟩ =
      bifunctionInverse (biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) := by
  have hPackagedConcave :
      ConcaveBifunction (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) :=
    (adjointOfConvexBifunctionAsConcave ⟨F.toFun, hF_properConvex.1⟩).2
  -- Instantiate the generic inverse/adjoint bridge with the packaged adjoint of `F`, then unfold
  -- the Chapter 6 biconjugate definition.
  simpa [biadjointOfConvexBifunction, adjointOfConvexBifunctionAsConcave] using
    helperForCorollary_38_5_1_adjointOfInverseConcave_eq_inverseAdjoint
      (K := adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)
      (hK_concave := hPackagedConcave) (hInvProper := hInvProper.1)

/-- Helper for Corollary 38.5.1: evaluating the current Chapter 38 adjoint of the inverse
packaged adjoint at the signed Euclidean/dual image of a primal pair gives the negative primal
value. -/
lemma helperForCorollary_38_5_1_inversePackagedAdjoint_currentAdjoint_apply
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    {FdualInv : FiberwiseProperConvexBifunction m n}
    (hFdualInv_eq :
      FdualInv.toFun =
        bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩))
    (hFdualInv_proper : ProperConvexBifunction FdualInv.toFun)
    (hBiadjEq : biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ = F.toFun)
    (x : Fin n → ℝ) (u : Fin m → ℝ) :
    bifunctionAdjoint FdualInv.toFun
        (dotProductEquiv ℝ (Fin n) (-x))
        (dotProductEquiv ℝ (Fin m) (-u)) =
      -F.toFun u x := by
  -- First rewrite the packaged adjoint of the inverse packaged adjoint as the inverse of the
  -- Chapter 6 biadjoint.
  have hInvProper :
      ProperConvexBifunction
        (bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) := by
    simpa [hFdualInv_eq] using hFdualInv_proper
  have hPackaged :
      adjointOfConvexBifunction ⟨FdualInv.toFun, hFdualInv_proper.1⟩ =
        bifunctionInverse (biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) := by
    simpa [hFdualInv_eq] using
      helperForCorollary_38_5_1_inversePackagedAdjoint_packagedAdjoint_eq_inverseBiadjoint
        (F := F) (hF_properConvex := hF_properConvex) hInvProper
  have hVectorized :
      adjointOfConvexBifunction ⟨FdualInv.toFun, hFdualInv_proper.1⟩ =
        fun xStar uStar =>
          bifunctionAdjoint FdualInv.toFun (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-uStar)) :=
    helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
      (F := FdualInv) (hF_properConvex := hFdualInv_proper)
  -- Then collapse the Chapter 6 biadjoint back to `F`.
  simpa [hPackaged, hBiadjEq, dotProductEquiv_apply_apply] using
    (congrFun (congrFun hVectorized x) u).symm

/-- Helper for Corollary 38.5.1: after unpacking the reversed Theorem 38.5 witnesses, evaluating
its dual output at the signed Euclidean/dual image of a primal pair gives the negative of the
primal composition value. -/
lemma helperForCorollary_38_5_1_reversedDual_output_rewrite_at_primalPair
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    {FdualInv : FiberwiseProperConvexBifunction m n}
    {GdualInv : FiberwiseProperConvexBifunction n p}
    (hFdualInv_eq :
      FdualInv.toFun =
        bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩))
    (hFdualInv_proper : ProperConvexBifunction FdualInv.toFun)
    (hGdualInv_eq :
      GdualInv.toFun =
        bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))
    (hGdualInv_proper : ProperConvexBifunction GdualInv.toFun)
    (hFBiadjEq : biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ = F.toFun)
    (hGBiadjEq : biadjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ = G.toFun)
    (u : Fin m → ℝ) (y : Fin p → ℝ) :
    bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun) (bifunctionAdjoint GdualInv.toFun)
        (dotProductEquiv ℝ (Fin p) (-y))
        (dotProductEquiv ℝ (Fin m) (-u)) =
      - bifunctionCompose G F u y := by
  -- Rewrite the supremum over middle dual vectors into the equivalent supremum over Euclidean
  -- middle vectors using `dotProductEquiv`.
  calc
    bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun) (bifunctionAdjoint GdualInv.toFun)
        (dotProductEquiv ℝ (Fin p) (-y))
        (dotProductEquiv ℝ (Fin m) (-u)) =
      ⨆ x : Fin n → ℝ,
        bifunctionAdjoint FdualInv.toFun (dotProductEquiv ℝ (Fin n) (-x))
            (dotProductEquiv ℝ (Fin m) (-u)) +
          bifunctionAdjoint GdualInv.toFun (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin n) (-x)) := by
            rw [bifunctionComposeSupGeneric]
            refine le_antisymm ?_ ?_
            · refine iSup_le ?_
              intro xStar
              refine le_iSup_of_le (-((dotProductEquiv ℝ (Fin n)).symm xStar)) ?_
              simp [add_comm]
            · refine iSup_le ?_
              intro x
              refine le_iSup_of_le (dotProductEquiv ℝ (Fin n) (-x)) ?_
              simp [add_comm]
    _ = ⨆ x : Fin n → ℝ, (-G.toFun x y) + (-F.toFun u x) := by
          refine iSup_congr ?_
          intro x
          -- Evaluate each inverse packaged adjoint term at the signed dual pair separately.
          rw [helperForCorollary_38_5_1_inversePackagedAdjoint_currentAdjoint_apply
              (F := F) (hF_properConvex := hF_properConvex) (FdualInv := FdualInv)
              (hFdualInv_eq := hFdualInv_eq) (hFdualInv_proper := hFdualInv_proper)
              (hBiadjEq := hFBiadjEq) x u,
            helperForCorollary_38_5_1_inversePackagedAdjoint_currentAdjoint_apply
              (F := G) (hF_properConvex := hG_properConvex) (FdualInv := GdualInv)
              (hFdualInv_eq := hGdualInv_eq) (hFdualInv_proper := hGdualInv_proper)
              (hBiadjEq := hGBiadjEq) y x]
          rw [add_comm]
    _ = - bifunctionCompose G F u y := by
          -- Properness excludes `⊥`, so negation commutes with the pointwise infimal-composition
          -- summands and converts the infimum into the displayed supremum.
          calc
            (⨆ x : Fin n → ℝ, (-G.toFun x y) + (-F.toFun u x)) =
              ⨆ x : Fin n → ℝ, -(F.toFun u x + G.toFun x y) := by
                refine iSup_congr ?_
                intro x
                simpa [add_comm] using
                  (helperForProposition_38_4_2_neg_add_of_neBot (F.proper.1 u x) (G.proper.1 x y)).symm
            _ = -(⨅ x : Fin n → ℝ, F.toFun u x + G.toFun x y) := by
              symm
              exact helperForProposition_38_4_2_neg_iInf (h := fun x => F.toFun u x + G.toFun x y)
            _ = - bifunctionCompose G F u y := by rw [bifunctionCompose]

/-- Helper for Corollary 38.5.1: the attaining dual middle vector supplied by the reversed
Theorem 38.5 package rewrites to a primal minimizer for the textbook infimal composition. -/
lemma helperForCorollary_38_5_1_reversedDual_attainment_to_primal_minimizer
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
    ∀ (u : Fin m → ℝ) (y : Fin p → ℝ),
      ∃ x : Fin n → ℝ, bifunctionCompose G F u y = F.toFun u x + G.toFun x y := by
  intro u y
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
  rcases
      helperForCorollary_38_5_1_reversedDual_theorem38_5_application
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hF_closed := hF_closed) (hG_closed := hG_closed) hTransportedHri with
    ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq, hGdualInv_proper,
      _hReversedDualEq, hReversedAttainment⟩
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
  have hOutputAtPair :
      bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun) (bifunctionAdjoint GdualInv.toFun)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) =
        - bifunctionCompose G F u y := by
    -- Route correction: the old bridge tried to prove the stronger formula `(GF)^* = F^* G^*`.
    -- The reversed theorem only gives the textbook signed evaluation of the dual output, which is
    -- exactly the datum needed to recover an attained primal minimizer.
    exact
      helperForCorollary_38_5_1_reversedDual_output_rewrite_at_primalPair
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hFdualInv_eq := hFdualInv_eq) (hFdualInv_proper := hFdualInv_proper)
        (hGdualInv_eq := hGdualInv_eq) (hGdualInv_proper := hGdualInv_proper)
        (hFBiadjEq := hFBiadjEq) (hGBiadjEq := hGBiadjEq) u y
  rcases
      hReversedAttainment (dotProductEquiv ℝ (Fin p) (-y)) (dotProductEquiv ℝ (Fin m) (-u)) with
    ⟨xStar, hxStar⟩
  let x : Fin n → ℝ := -((dotProductEquiv ℝ (Fin n)).symm xStar)
  refine ⟨x, ?_⟩
  have hFterm :
      bifunctionAdjoint FdualInv.toFun xStar (dotProductEquiv ℝ (Fin m) (-u)) =
        -F.toFun u x := by
    -- Rewrite the first factor through the inverse packaged adjoint of `F`.
    simpa [x, hFdualInv_eq, dotProductEquiv_apply_apply] using
      helperForCorollary_38_5_1_inversePackagedAdjoint_currentAdjoint_apply
        (F := F) (hF_properConvex := hF_properConvex) (FdualInv := FdualInv)
        (hFdualInv_eq := hFdualInv_eq) (hFdualInv_proper := hFdualInv_proper)
        (hBiadjEq := hFBiadjEq) x u
  have hGterm :
      bifunctionAdjoint GdualInv.toFun (dotProductEquiv ℝ (Fin p) (-y)) xStar =
        -G.toFun x y := by
    -- The second factor is the symmetric rewrite for `G`.
    simpa [x, hGdualInv_eq, dotProductEquiv_apply_apply] using
      helperForCorollary_38_5_1_inversePackagedAdjoint_currentAdjoint_apply
        (F := G) (hF_properConvex := hG_properConvex) (FdualInv := GdualInv)
        (hFdualInv_eq := hGdualInv_eq) (hFdualInv_proper := hGdualInv_proper)
        (hBiadjEq := hGBiadjEq) y x
  have hNegComposeEq :
      - bifunctionCompose G F u y = (-G.toFun x y) + (-F.toFun u x) := by
    calc
      - bifunctionCompose G F u y =
        bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun) (bifunctionAdjoint GdualInv.toFun)
            (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin m) (-u)) := hOutputAtPair.symm
      _ =
        bifunctionAdjoint GdualInv.toFun (dotProductEquiv ℝ (Fin p) (-y)) xStar +
          bifunctionAdjoint FdualInv.toFun xStar (dotProductEquiv ℝ (Fin m) (-u)) := hxStar
      _ = (-G.toFun x y) + (-F.toFun u x) := by rw [hGterm, hFterm]
  have hNegSummand :
      -(F.toFun u x + G.toFun x y) = (-G.toFun x y) + (-F.toFun u x) := by
    -- Properness excludes `⊥`, so the sum negates by reversing the order of the two terms.
    exact helperForProposition_38_4_2_neg_add_of_neBot (F.proper.1 u x) (G.proper.1 x y)
  have hNegEq :
      - bifunctionCompose G F u y = -(F.toFun u x + G.toFun x y) := by
    rw [hNegSummand]
    exact hNegComposeEq
  -- Negating the equality of negatives recovers the attained primal infimum identity.
  simpa using congrArg Neg.neg hNegEq

/-- Helper for Corollary 38.5.1: a closed concave bifunction stays closed after inversion, now in
the Chapter 38 product lower-semicontinuity sense. -/
lemma helperForCorollary_38_5_1_inverse_closedConcave_is_productLowerSemicontinuous
    {m n : Nat} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hK_closed : ClosedConcaveBifunction K) :
    IsProductLowerSemicontinuousBifunction (bifunctionInverse K) := by
  -- Product lower semicontinuity of the inverse is exactly lower semicontinuity of the negated
  -- graph of `K` after swapping the two coordinate blocks.
  simpa [IsProductLowerSemicontinuousBifunction, bifunctionInverse, bifunctionGraphFunction,
    Function.comp] using
    hK_closed.2.comp_continuous
      (show Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => Fin.append p.2 p.1) by
        simpa using
          (Fin.continuous_append m n).comp (continuous_snd.prodMk continuous_fst))

/-- Helper for Corollary 38.5.1: the reversed-dual Theorem 38.5 application already implies the
closedness of `GF`, exactly as in the book's sentence "as the adjoint of something, `GF` is
closed". -/
lemma helperForCorollary_38_5_1_reversedDual_closedness
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
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) := by
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
        bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun) (bifunctionAdjoint GdualInv.toFun)
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
  have hClosedPackaged :
      ClosedConcaveBifunction
        (adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩) := by
    exact
      ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
        (F := bifunctionCompose GdualInv FdualInv)).1 hReversedConvex).1
  have hClosedInverseCompose :
      ClosedConcaveBifunction (bifunctionInverse (bifunctionCompose G F)) := by
    simpa [hPackagedAdjointEq] using hClosedPackaged
  have hInvInvCompose :
      bifunctionInverse (bifunctionInverse (bifunctionCompose G F)) = bifunctionCompose G F := by
    funext u y
    simp [bifunctionInverse]
  rw [← hInvInvCompose]
  exact
    helperForCorollary_38_5_1_inverse_closedConcave_is_productLowerSemicontinuous
      (K := bifunctionInverse (bifunctionCompose G F)) hClosedInverseCompose

/-- Helper for Corollary 38.5.1: the book-style closure is always a pointwise minorant of the
original bifunction, because it is built from lower-semicontinuous minorants. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_le
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] (K : U → X → EReal) :
    bifunctionClosure K ≤ K := by
  intro u x
  -- Rewrite the bifunction closure as the product-space closure of the associated function.
  dsimp [bifunctionClosure]
  unfold erealFunctionClosure
  split_ifs with hNoBot
  · -- In the non-`⊥` branch, every candidate in the hull is by definition bounded above by `K`.
    rw [erealLowerSemicontinuousHull]
    refine iSup_le ?_
    intro h
    exact h.2.2 (u, x)
  · -- In the `⊥` branch the closure is constantly `⊥`, hence automatically below `K`.
    simp

/-- Helper for Corollary 38.5.1: the raw lower-semicontinuous hull is monotone, since every
lower-semicontinuous minorant of `f` is automatically one of `g` whenever `f ≤ g`. -/
lemma helperForCorollary_38_5_1_erealLowerSemicontinuousHull_mono
    {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hfg : f ≤ g) :
    erealLowerSemicontinuousHull f ≤ erealLowerSemicontinuousHull g := by
  intro x
  rw [erealLowerSemicontinuousHull, erealLowerSemicontinuousHull]
  -- Push each hull candidate for `f` into the hull of `g` using the pointwise inequality `f ≤ g`.
  refine iSup_le ?_
  intro h
  exact
    le_iSup_of_le
      ⟨h.1, h.2.1, le_trans h.2.2 hfg⟩
      le_rfl



end Section38
end Chap08
