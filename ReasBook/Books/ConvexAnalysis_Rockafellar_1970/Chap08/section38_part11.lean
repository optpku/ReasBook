/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part10

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Corollary 38.5.1: the sign-corrected finite-dimensional Euclidean/dual
identification is a homeomorphism for the weak dual topology used in Chapter 38. -/
noncomputable def helperForCorollary_38_5_1_signedDotProductHomeomorph
    (n : Nat) :
    (Fin n → ℝ) ≃ₜ Module.Dual ℝ (Fin n → ℝ) := by
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
  exact signedDotProductEquiv.symm.toHomeomorph

/-- Helper for Corollary 38.5.1: the Chapter 6 packaged adjoint is exactly the Chapter 38 adjoint
after identifying finite-dimensional dual vectors with coordinate vectors via `dotProductEquiv`
and correcting the sign convention difference between the two adjoint definitions. -/
lemma helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
    {m n : Nat} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : ConvexBifunction F) :
    adjointOfConvexBifunction ⟨F, hF_convex⟩ =
      fun xStar uStar =>
        bifunctionAdjoint F (dotProductEquiv ℝ (Fin n) (-xStar))
          (dotProductEquiv ℝ (Fin m) (-uStar)) := by
  -- Rewrite the Chapter 6 `sInf` formula into the Chapter 38 `iInf` adjoint on `Module.Dual`.
  funext xStar uStar
  simp only [adjointOfConvexBifunction]
  rw [sInf_range]
  calc
    (⨅ p : (Fin m → ℝ) × (Fin n → ℝ),
        F p.1 p.2 - ↑(p.2 ⬝ᵥ xStar) + ↑(p.1 ⬝ᵥ uStar)) =
      ⨅ u : Fin m → ℝ, ⨅ x : Fin n → ℝ,
        (F u x - ↑(x ⬝ᵥ xStar) + ↑(u ⬝ᵥ uStar)) := by
          exact
            helperForTheorem_6_30_22_iInf_prod_eq_nested
              (H := fun u x => F u x - ↑(x ⬝ᵥ xStar) + ↑(u ⬝ᵥ uStar))
    _ =
      ⨅ u : Fin m → ℝ, ⨅ x : Fin n → ℝ,
        ↑(((dotProductEquiv ℝ (Fin n)) (-xStar)) x) +
          -↑(((dotProductEquiv ℝ (Fin m)) (-uStar)) u) +
          F u x := by
            refine iInf_congr ?_
            intro u
            refine iInf_congr ?_
            intro x
            simp [dotProductEquiv_apply_apply, dotProduct_comm, sub_eq_add_neg, add_left_comm,
              add_comm]
    _ =
      bifunctionAdjoint F (dotProductEquiv ℝ (Fin n) (-xStar))
        (dotProductEquiv ℝ (Fin m) (-uStar)) := by
          rw [bifunctionAdjoint]

/-- Helper for Corollary 38.5.1: the Chapter 6 packaged adjoint is exactly the Chapter 38 adjoint
after identifying finite-dimensional dual vectors with coordinate vectors via `dotProductEquiv`
and correcting the sign convention difference between the two adjoint definitions. -/
lemma helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun) :
    adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ =
      fun xStar uStar =>
        bifunctionAdjoint F.toFun (dotProductEquiv ℝ (Fin n) (-xStar))
          (dotProductEquiv ℝ (Fin m) (-uStar)) := by
  exact
    helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
      (F := F.toFun) hF_properConvex.1

/-- Helper for Corollary 38.5.1: the current Chapter 38 dual product `F^* G^*`, evaluated at the
sign-corrected Euclidean/dual image of a coordinate pair, is exactly the packaged Chapter 6
supremal composition of the packaged adjoints. -/
lemma helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        (dotProductEquiv ℝ (Fin p) (-y))
        (dotProductEquiv ℝ (Fin m) (-u)) =
      ⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨(G.toFun : (Fin n → ℝ) → (Fin p → ℝ) → EReal), hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
  calc
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        (dotProductEquiv ℝ (Fin p) (-y))
        (dotProductEquiv ℝ (Fin m) (-u)) =
      ⨆ x : Fin n → ℝ,
        bifunctionAdjoint F.toFun (dotProductEquiv ℝ (Fin n) (-x))
            (dotProductEquiv ℝ (Fin m) (-u)) +
          bifunctionAdjoint G.toFun (dotProductEquiv ℝ (Fin p) (-y))
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
    _ = ⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
            refine iSup_congr ?_
            intro x
            rw [← congrFun (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
                    (F := F) (hF_properConvex := hF_properConvex)) x) u,
              ← congrFun (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
                    (F := G) (hF_properConvex := hG_properConvex)) y) x]
            simp [add_comm]


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
finite packaged dual composition `F^* G^*` agrees pointwise with the packaged adjoint of `GF`.
This is the exact finite-coordinate reformulation of the theorem-local identity
`(GF)^* = F^* G^*` before any closure operator is introduced. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    (fun y u =>
      ⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ := by
  have hCurrentEq :
      bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) := by
    exact
      (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
        (F := F) (G := G) hF_properConvex hG_properConvex).2 hri |>.1
  funext y u
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
    _ = bifunctionAdjoint (bifunctionCompose G F)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            rw [← hCurrentEq]
    _ = adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
          exact
            (congrFun
              (congrFun
                (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                  (F := bifunctionCompose G F) hComposeConvex)
                y)
              u).symm


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
reverse raw packaged inequality `(GF)^* ≤ F^* G^*` is immediate because the theorem-local
packaged identity is already an equality. This isolates the theorem-local reverse comparison from
the later corollary-level domain transport. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_le_packagedComposeSup_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≤
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
  have hEq :=
    helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri)
  have hEq_point :
      (⨆ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) =
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u := by
    simpa using congrFun (congrFun hEq y) u
  rw [← hEq_point]


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
finite packaged dual composition not only equals the packaged adjoint of `GF`, but its middle
supremum is attained at some packaged coordinate vector. This is the packaged-coordinate form of
Theorem 38.5's attainment clause. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_pointwiseEqualityAndAttainment_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) ∧
      ∃ x : Fin n → ℝ,
        (⨆ x' : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x' +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x' u) =
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
  have hPoint :=
    helperForTheorem_38_5_pointwiseDualEqualityAndAttainment_of_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hri := hri)
      (dotProductEquiv ℝ (Fin p) (-y))
      (dotProductEquiv ℝ (Fin m) (-u))
  rcases hPoint with ⟨hEqCurrent, hxCurrent⟩
  rcases hxCurrent with ⟨xStar, hxCurrent⟩
  let x : Fin n → ℝ := -((dotProductEquiv ℝ (Fin n)).symm xStar)
  have hEqPackaged :
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        (⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
    calc
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose G F)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            exact
              congrFun
                (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                    (F := bifunctionCompose G F) hComposeConvex)
                  y)
                u
      _ = bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin m) (-u)) := hEqCurrent
      _ = (⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
            exact
              helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
                (F := F) (G := G)
                (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
                (y := y) (u := u)
  have hxStar_eq :
      xStar = dotProductEquiv ℝ (Fin n) (-x) := by
    simp [x]
  have hxPackaged :
      (⨆ x' : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x' +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x' u) =
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
    calc
      (⨆ x' : Fin n → ℝ,
        adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x' +
          adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x' u) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            symm
            exact
              helperForCorollary_38_5_1_vectorizedComposeSup_eq_packagedComposeSup
                (F := F) (G := G)
                (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
                (y := y) (u := u)
      _ = bifunctionAdjoint G.toFun (dotProductEquiv ℝ (Fin p) (-y))
            (dotProductEquiv ℝ (Fin n) (-x)) +
          bifunctionAdjoint F.toFun (dotProductEquiv ℝ (Fin n) (-x))
            (dotProductEquiv ℝ (Fin m) (-u)) := by
            rw [hxCurrent, hxStar_eq]
      _ = adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
            rw [← congrFun (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
                    (F := G) (hF_properConvex := hG_properConvex)) y) x,
                ← congrFun (congrFun
                  (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
                    (F := F) (hF_properConvex := hF_properConvex)) x) u]
  exact ⟨hEqPackaged, ⟨x, hxPackaged⟩⟩


/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, the
packaged supremal composition `F^* G^*` attains its displayed middle supremum at every packaged
coordinate pair. This is the global packaged form of the theorem-local attainment clause. -/
lemma helperForCorollary_38_5_1_packagedComposeSup_attainment_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      ∃ x : Fin n → ℝ,
        (⨆ x' : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x' +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x' u) =
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
  intro y u
  exact
    (helperForCorollary_38_5_1_packagedComposeSup_pointwiseEqualityAndAttainment_of_theorem_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hComposeConvex := hComposeConvex) (hri := hri) (y := y) (u := u)).2

/-- Helper for Corollary 38.5.1: the same theorem-local attainment clause can be read directly as
an attained packaged formula for the composed adjoint `(GF)^*` at every packaged dual pair. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_attainment_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      ∃ x : Fin n → ℝ,
        adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u =
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u := by
  intro y u
  rcases
      helperForCorollary_38_5_1_packagedComposeSup_pointwiseEqualityAndAttainment_of_theorem_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hComposeConvex := hComposeConvex) (hri := hri) (y := y) (u := u) with
    ⟨hEq, x, hx⟩
  exact ⟨x, hEq.trans hx⟩


/-- Helper for Corollary 38.5.1: one primal point where `H` is not `⊤` already bounds every
value of the packaged adjoint away from `⊤`, because the adjoint is defined as an infimum over all
primal points. -/
lemma helperForCorollary_38_5_1_packagedAdjoint_ne_top_of_exists_primal_ne_top
    {m n : Nat} {H : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hH_convex : ConvexBifunction H)
    (hWitness : ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, H u x ≠ (⊤ : EReal)) :
    ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
      adjointOfConvexBifunction ⟨H, hH_convex⟩ xStar uStar ≠ (⊤ : EReal) := by
  intro xStar uStar
  rcases hWitness with ⟨u, x, hHx⟩
  have hTermNeTop :
      H u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((u ⬝ᵥ uStar : ℝ) : EReal)) ≠ (⊤ : EReal) := by
    have hLeftNeTop :
        H u x + (-(((x ⬝ᵥ xStar : ℝ) : EReal))) ≠ (⊤ : EReal) := by
      exact EReal.add_ne_top hHx (by simp)
    simpa [sub_eq_add_neg, add_assoc] using
      EReal.add_ne_top hLeftNeTop (by simp)
  intro hTop
  have hLe :
      adjointOfConvexBifunction ⟨H, hH_convex⟩ xStar uStar ≤
        H u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) + (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
    rw [adjointOfConvexBifunction]
    exact sInf_le ⟨(u, x), rfl⟩
  have hTopLe :
      (⊤ : EReal) ≤
        H u x - ((((x ⬝ᵥ xStar : ℝ) : EReal))) + ((((u ⬝ᵥ uStar : ℝ) : EReal))) := by
    simpa [hTop] using hLe
  exact hTermNeTop (top_unique hTopLe)



/-- Helper for Corollary 38.5.1: under the theorem-38.5 primal qualification hypothesis, every
packaged value of the composed adjoint `(GF)^*` avoids `⊤`. This is the packaged-coordinate form
of the textbook fact that one primal non-`⊤` point forces the whole adjoint to be proper on the
`+∞` side. -/
lemma helperForCorollary_38_5_1_packagedAdjointCompose_ne_top_of_theorem_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hComposeConvex : ConvexBifunction (bifunctionCompose G F))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
          intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ y : Fin p → ℝ, ∀ u : Fin m → ℝ,
      adjointOfConvexBifunction ⟨bifunctionCompose G F, hComposeConvex⟩ y u ≠ (⊤ : EReal) := by
  have hWitness :
      ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal) :=
    helperForTheorem_38_5_compose_exists_ne_top_of_hri (F := F) (G := G) hri
  exact
    helperForCorollary_38_5_1_packagedAdjoint_ne_top_of_exists_primal_ne_top
      (hH_convex := hComposeConvex) (hWitness := hWitness)

/-- Helper for Corollary 38.5.1: the inverse of the packaged Chapter 6 supremal composition
`F^* G^*` is pointwise bounded below by the infimal composition of the inverse packaged adjoints.

This is the precise extended-value transport that survives without any extra no-`⊥` hypotheses:
termwise we only have `(-a) + (-b) ≤ -(a + b)`, so the reversed-dual primal composition gives a
one-sided lower bound for `bifunctionInverse (F^* G^*)`. -/
lemma helperForCorollary_38_5_1_packagedAdjointInverseCompose_le_inverse_packagedComposeSup
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    (fun u y =>
      ⨅ x : Fin n → ℝ,
        bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) u x +
          bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) x y) ≤
      bifunctionInverse
        (fun y u =>
          ⨆ x : Fin n → ℝ,
            adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
  intro u y
  change (⨅ x : Fin n → ℝ,
      bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) u x +
        bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) x y) ≤
    -(⨆ x : Fin n → ℝ,
      adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
        adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u)
  calc
    (⨅ x : Fin n → ℝ,
      bifunctionInverse (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) u x +
        bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩) x y)
        ≤ ⨅ x : Fin n → ℝ,
            -(adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
              adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
          refine iInf_mono ?_
          intro x
          simpa [bifunctionInverse, add_comm] using
            (helperForLemma33_0_5_neg_sum_upper_bound
              (x := adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x)
              (y := adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u))
    _ = -(⨆ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
            adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u) := by
          symm
          simpa using
            (helperForLemma33_0_5_neg_iSup_neg_eq_iInf
              (f := fun x : Fin n → ℝ =>
                -(adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩ y x +
                  adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ x u)))

/-- Helper for Corollary 38.5.1: the first-domain `domBot` of the Chapter 6 packaged adjoint is
the pullback of the Chapter 38 `dom F^*` set along the sign-corrected Euclidean/dual
identification. -/
lemma helperForCorollary_38_5_1_vectorizedAdjoint_domBot_preimage
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun) :
    bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) =
      {xStarVec : Fin n → ℝ |
        dotProductEquiv ℝ (Fin n) (-xStarVec) ∈
          bifunctionDomBot (bifunctionAdjoint F.toFun)} := by
  ext xStarVec
  constructor
  · intro hxStarVec
    rcases hxStarVec with ⟨uStarVec, huStarVec⟩
    -- Rewrite the packaged adjoint witness directly into a Chapter 38 dual witness.
    refine ⟨dotProductEquiv ℝ (Fin m) (-uStarVec), ?_⟩
    simpa [helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
      (F := F) (hF_properConvex := hF_properConvex)] using huStarVec
  · intro hxStar
    rcases hxStar with ⟨uStar, huStar⟩
    -- Pull the `Module.Dual` witness back to coordinates using the inverse `dotProductEquiv`.
    refine ⟨-((dotProductEquiv ℝ (Fin m)).symm uStar), ?_⟩
    simpa [helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
      (F := F) (hF_properConvex := hF_properConvex), dotProductEquiv_apply_apply] using huStar

/-- Helper for Corollary 38.5.1: the packaged `dom F^*` qualification set is exactly the image
of the Chapter 38 dual-domain under the signed Euclidean-coordinate identification
`xStar ↦ -((dotProductEquiv).symm xStar)`. -/
lemma helperForCorollary_38_5_1_vectorizedAdjoint_domBot_eq_signedImage
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun) :
    bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) =
      (fun xStar : Module.Dual ℝ (Fin n → ℝ) =>
        -((dotProductEquiv ℝ (Fin n)).symm xStar)) ''
        bifunctionDomBot (bifunctionAdjoint F.toFun) := by
  -- Repackage the previously proved preimage formula as an explicit image under the signed
  -- coordinate/dual identification; this is the exact set-level transport needed later for `ri`.
  rw [helperForCorollary_38_5_1_vectorizedAdjoint_domBot_preimage
    (F := F) (hF_properConvex := hF_properConvex)]
  ext xStarVec
  constructor
  · intro hxStarVec
    refine ⟨dotProductEquiv ℝ (Fin n) (-xStarVec), hxStarVec, ?_⟩
    ext i
    simp
  · rintro ⟨xStar, hxStar, rfl⟩
    simpa [dotProductEquiv_apply_apply] using hxStar

/-- Helper for Corollary 38.5.1: unfolding `dom` after taking the inverse of a bifunction exposes
the middle-variable points where the original bifunction is not `⊥`. -/
lemma helperForCorollary_38_5_1_bifunctionDom_inverse_eq_exists_ne_bot
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (H : U → X → EReal) :
    bifunctionDom (bifunctionInverse H) = {x : X | ∃ u : U, H u x ≠ ⊥} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu⟩
    -- Unfolding the inverse turns `≠ ⊤` into the corresponding `≠ ⊥` statement for `H`.
    refine ⟨u, ?_⟩
    simpa [bifunctionDom, bifunctionInverse] using hu
  · intro hx
    rcases hx with ⟨u, hu⟩
    -- The converse rewrite is the same sign change in the opposite direction.
    refine ⟨u, ?_⟩
    simpa [bifunctionDom, bifunctionInverse] using hu

/-- Helper for Corollary 38.5.1: unfolding `domBot` after taking the inverse exposes the
middle-variable points where the original bifunction is not `⊤`. -/
lemma helperForCorollary_38_5_1_bifunctionDomBot_inverse_eq_exists_ne_top
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (H : U → X → EReal) :
    bifunctionDomBot (bifunctionInverse H) = {x : X | ∃ u : U, H u x ≠ ⊤} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu⟩
    -- Negating the value swaps the excluded endpoint from `⊥` to `⊤`.
    refine ⟨u, ?_⟩
    simpa [bifunctionDomBot, bifunctionInverse] using hu
  · intro hx
    rcases hx with ⟨u, hu⟩
    -- The same endpoint swap rewrites membership in the opposite direction.
    refine ⟨u, ?_⟩
    simpa [bifunctionDomBot, bifunctionInverse] using hu

/-- Helper for Corollary 38.5.1: after taking the inverse, the first-domain of the packaged
adjoint of `G` is the pullback of the Chapter 38 `dom G^*_ *` set along the same sign-corrected
Euclidean/dual identification. -/
lemma helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_preimage
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    bifunctionDom (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) =
      {xStarVec : Fin n → ℝ |
        dotProductEquiv ℝ (Fin n) (-xStarVec) ∈
          bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun))} := by
  ext xStarVec
  constructor
  · intro hxStarVec
    rcases hxStarVec with ⟨yStarVec, hyStarVec⟩
    -- Translate the packaged coordinate witness into a `Module.Dual` witness for `dom G^*_ *`.
    refine ⟨dotProductEquiv ℝ (Fin p) (-yStarVec), ?_⟩
    simpa [bifunctionInverse, helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
      (F := G) (hF_properConvex := hG_properConvex)] using hyStarVec
  · intro hxStar
    rcases hxStar with ⟨yStar, hyStar⟩
    -- Pull the `Module.Dual` witness back to coordinates before reusing the same adjoint rewrite.
    refine ⟨-((dotProductEquiv ℝ (Fin p)).symm yStar), ?_⟩
    simpa [bifunctionInverse, helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint
      (F := G) (hF_properConvex := hG_properConvex), dotProductEquiv_apply_apply] using hyStar

/-- Helper for Corollary 38.5.1: the packaged `dom G^*_ *` qualification set is exactly the
image of the Chapter 38 dual-domain under the same signed Euclidean-coordinate identification. -/
lemma helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_eq_signedImage
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    bifunctionDom (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) =
      (fun xStar : Module.Dual ℝ (Fin n → ℝ) =>
        -((dotProductEquiv ℝ (Fin n)).symm xStar)) ''
        bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)) := by
  -- The inverse-adjoint qualification set uses the same signed identification, so the image
  -- reformulation is identical after replacing `domBot` by `dom`.
  rw [helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_preimage
    (G := G) (hG_properConvex := hG_properConvex)]
  ext xStarVec
  constructor
  · intro hxStarVec
    refine ⟨dotProductEquiv ℝ (Fin n) (-xStarVec), hxStarVec, ?_⟩
    ext i
    simp
  · rintro ⟨xStar, hxStar, rfl⟩
    simpa [dotProductEquiv_apply_apply] using hxStar

/-- Helper for Corollary 38.5.1: if the current Chapter 38 left dual domain is already full, then
its packaged Chapter 6 counterpart is full as well under the signed Euclidean-coordinate
identification. -/
lemma helperForCorollary_38_5_1_full_packaged_leftDomain_of_full_currentDualDomain
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hLeftFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDomBot (bifunctionAdjoint F.toFun)) :
    ∀ xStarVec : Fin n → ℝ,
      xStarVec ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) := by
  intro xStarVec
  rw [helperForCorollary_38_5_1_vectorizedAdjoint_domBot_preimage
    (F := F) (hF_properConvex := hF_properConvex)]
  exact hLeftFull (dotProductEquiv ℝ (Fin n) (-xStarVec))

/-- Helper for Corollary 38.5.1: if the current Chapter 38 right dual domain is already full, then
its packaged Chapter 6 inverse-adjoint counterpart is full as well under the same signed
Euclidean-coordinate identification. -/
lemma helperForCorollary_38_5_1_full_packaged_rightDomain_of_full_currentDualDomain
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hRightFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun))) :
    ∀ xStarVec : Fin n → ℝ,
      xStarVec ∈ bifunctionDom
        (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) := by
  intro xStarVec
  rw [helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_preimage
    (G := G) (hG_properConvex := hG_properConvex)]
  exact hRightFull (dotProductEquiv ℝ (Fin n) (-xStarVec))


/-- Helper for Corollary 38.5.1: fullness of the packaged Chapter 6 left dual domain transports
back to fullness of the current Chapter 38 dual `dom F^*`. This is the converse of the previous
packaging lemma and lets obstruction statements be read back in the current notation. -/
lemma helperForCorollary_38_5_1_full_currentDual_leftDomain_of_full_packagedDomain
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hLeftFull :
      ∀ xStarVec : Fin n → ℝ,
        xStarVec ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) :
    ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
      xStar ∈ bifunctionDomBot (bifunctionAdjoint F.toFun) := by
  intro xStar
  have hxVec :
      -((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
        bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) :=
    hLeftFull (-((dotProductEquiv ℝ (Fin n)).symm xStar))
  rw [helperForCorollary_38_5_1_vectorizedAdjoint_domBot_preimage
    (F := F) (hF_properConvex := hF_properConvex)] at hxVec
  simpa [dotProductEquiv_apply_apply] using hxVec

/-- Helper for Corollary 38.5.1: fullness of the packaged Chapter 6 right dual domain transports
back to fullness of the current Chapter 38 dual `dom G^*_ *`. -/
lemma helperForCorollary_38_5_1_full_currentDual_rightDomain_of_full_packagedDomain
    {n p : Nat} (G : FiberwiseProperConvexBifunction n p)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hRightFull :
      ∀ xStarVec : Fin n → ℝ,
        xStarVec ∈ bifunctionDom
          (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))) :
    ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
      xStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun)) := by
  intro xStar
  have hxVec :
      -((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
        bifunctionDom
          (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) :=
    hRightFull (-((dotProductEquiv ℝ (Fin n)).symm xStar))
  rw [helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_preimage
    (G := G) (hG_properConvex := hG_properConvex)] at hxVec
  simpa [dotProductEquiv_apply_apply] using hxVec

/-- Helper for Corollary 38.5.1: once the two packaged Chapter 6 dual domains are full, the
transported qualification hypothesis needed for the reversed-dual Theorem 38.5 application is
automatic. -/
lemma helperForCorollary_38_5_1_transported_hri_of_full_packagedDualDomains
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hLeftFull :
      ∀ xStarVec : Fin n → ℝ,
        xStarVec ∈ bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩))
    (hRightFull :
      ∀ xStarVec : Fin n → ℝ,
        xStarVec ∈ bifunctionDom
          (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩))) :
    (intrinsicInterior ℝ
          (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
        intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty := by
  have hLeftEqUniv :
      bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) = Set.univ := by
    ext xStarVec
    constructor
    · intro _
      simp
    · intro _
      exact hLeftFull xStarVec
  have hRightEqUniv :
      bifunctionDom (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)) =
        Set.univ := by
    ext xStarVec
    constructor
    · intro _
      simp
    · intro _
      exact hRightFull xStarVec
  refine ⟨0, ?_, ?_⟩
  · rw [hLeftEqUniv]
    exact
      interior_subset_intrinsicInterior
        (s := (Set.univ : Set (Fin n → ℝ))) (by simp [interior_univ])
  · rw [hRightEqUniv]
    exact
      interior_subset_intrinsicInterior
        (s := (Set.univ : Set (Fin n → ℝ))) (by simp [interior_univ])

/-- Helper for Corollary 38.5.1: an upstream theorem proving full current Chapter 38 dual domains
would automatically provide not only the current `ri` hypothesis, but also its transported packaged
Chapter 6 version for the reversed-dual theorem application. -/
lemma helperForCorollary_38_5_1_transported_hri_of_full_currentDualDomains
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hLeftFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDomBot (bifunctionAdjoint F.toFun))
    (hRightFull :
      ∀ xStar : Module.Dual ℝ (Fin n → ℝ),
        xStar ∈ bifunctionDom (bifunctionInverse (bifunctionAdjoint G.toFun))) :
    (intrinsicInterior ℝ
          (bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩)) ∩
        intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hG_properConvex.1⟩)))).Nonempty := by
  exact
    helperForCorollary_38_5_1_transported_hri_of_full_packagedDualDomains
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      (hLeftFull :=
        helperForCorollary_38_5_1_full_packaged_leftDomain_of_full_currentDualDomain
          (F := F) (hF_properConvex := hF_properConvex) hLeftFull)
      (hRightFull :=
        helperForCorollary_38_5_1_full_packaged_rightDomain_of_full_currentDualDomain
          (G := G) (hG_properConvex := hG_properConvex) hRightFull)

/-- Helper for Corollary 38.5.1: a convex epigraph in the full bifunction variables restricts to
an `EReal`-convex slice once the first variable is frozen. -/
lemma helperForCorollary_38_5_1_isERealConvex_slice_of_epigraphConvex
    {m n : Nat} (H : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hH : IsEpigraphConvexBifunction (m := m) (n := n) H) (u : Fin m → ℝ) :
    IsERealConvex (H u) := by
  -- Freeze the first bifunction variable by pulling the global epigraph back along the affine
  -- embedding `(x, t) ↦ ((u, x), t)`.
  rw [IsERealConvex]
  let φ : ((Fin n → ℝ) × ℝ) →ᵃ[ℝ] (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
    { toFun := fun p => ((u, p.1), p.2)
      linear :=
        { toFun := fun p => ((0, p.1), p.2)
          map_add' := by
            intro p q
            ext <;> simp
          map_smul' := by
            intro a p
            ext <;> simp }
      map_vadd' := by
        intro p q
        ext <;> simp [vadd_eq_add] }
  have hpre : ERealEpigraph (H u) = φ ⁻¹' bifunctionEpigraph (m := m) (n := n) H := by
    ext p
    simp [ERealEpigraph, φ, bifunctionEpigraph]
  -- Convexity is stable under affine preimages, so the slice inherits the ambient epigraph
  -- convexity.
  simpa [hpre] using (Convex.affine_preimage φ hH)

/-- Helper for Corollary 38.5.1: a proper concave bifunction has a proper convex inverse in the
Chapter 6 graph-function sense. -/
lemma helperForCorollary_38_5_1_properConcave_inverse_properConvex
    {m n : Nat} (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hK_proper : ProperConcaveBifunction (m := n) (n := m) K) :
    ProperConvexBifunction (m := m) (n := n) (bifunctionInverse K) := by
  let swapCoords : (Fin (m + n) → ℝ) → (Fin (n + m) → ℝ) :=
    fun z => Fin.append (fun j : Fin n => z (Fin.natAdd m j))
      (fun i : Fin m => z (Fin.castAdd n i))
  have hInverseGraphConvex :
      ConvexERealFunction (F := Fin (m + n) → ℝ)
        (bifunctionGraphFunction (bifunctionInverse K)) := by
    -- The inverse graph is the negated original graph after swapping the `u` and `x`
    -- coordinates, so convexity transports through that linear reindexing.
    intro x y a b ha hb hab
    have hConv := hK_proper.2.2
      (x := swapCoords x) (y := swapCoords y) ha hb hab
    simpa [swapCoords, bifunctionGraphFunction, bifunctionInverse, Pi.add_apply, Pi.smul_apply]
      using hConv
  have hInverseGraphProper :
      ProperConvexERealFunction (F := Fin (m + n) → ℝ)
        (bifunctionGraphFunction (bifunctionInverse K)) := by
    refine ⟨?_, hInverseGraphConvex⟩
    constructor
    · intro z
      -- Excluding `⊤` from the original concave graph excludes `⊥` from the negated inverse graph.
      have hNoTop :
          bifunctionGraphFunction K (swapCoords z) ≠ (⊤ : EReal) := by
        simpa [ProperConcaveERealFunction, swapCoords] using hK_proper.2.1.1 (swapCoords z)
      simpa [swapCoords, bifunctionGraphFunction, bifunctionInverse, EReal.neg_eq_bot_iff]
        using hNoTop
    · rcases hK_proper.2.1.2 with ⟨z, hz⟩
      -- Reindex the original finite witness through the coordinate swap defining the inverse graph.
      refine ⟨Fin.append (fun i : Fin m => z (Fin.natAdd n i))
        (fun j : Fin n => z (Fin.castAdd m j)), ?_⟩
      simpa [swapCoords, bifunctionGraphFunction, bifunctionInverse, EReal.neg_eq_top_iff] using hz
  have hInverseGraphConvexOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction (bifunctionInverse K)) :=
    (helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := bifunctionGraphFunction (bifunctionInverse K)) hInverseGraphProper).1
  refine ⟨?_, hInverseGraphProper⟩
  -- The graph convexity part of `ProperConvexBifunction` is exactly convexity on the full space.
  simpa [ConvexBifunction, ConvexFunction] using hInverseGraphConvexOn

/-- Helper for Corollary 38.5.1: once the inverse is proper convex on the graph, each of its
fiber slices is convex in the Chapter 38 sense. -/
lemma helperForCorollary_38_5_1_inverse_sliceConvex_of_properConvex
    {m n : Nat} (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hInverseProperConvex :
      ProperConvexBifunction (m := m) (n := n) (bifunctionInverse K)) :
    ∀ u : Fin m → ℝ, IsERealConvex (bifunctionInverse K u) := by
  intro u
  have hInverseGraphConvexOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction (bifunctionInverse K)) := by
    simpa [ConvexBifunction, ConvexFunction] using hInverseProperConvex.1
  -- Freeze the first variable by pulling the graph epigraph back along the affine map
  -- `(x, t) ↦ (append u x, t)`.
  rw [IsERealConvex]
  let φ : ((Fin n → ℝ) × ℝ) →ᵃ[ℝ] ((Fin (m + n) → ℝ) × ℝ) :=
    { toFun := fun p => (Fin.append u p.1, p.2)
      linear :=
        { toFun := fun p => (Fin.append (fun _ : Fin m => 0) p.1, p.2)
          map_add' := by
            intro p q
            apply Prod.ext
            · ext i
              cases Nat.lt_or_ge i.1 m with
              | inl hi =>
                  simp [Fin.append, Fin.addCases, hi, Pi.add_apply]
              | inr hi =>
                  let j : Fin n := ⟨i.1 - m, by omega⟩
                  have hj' : Fin.natAdd m j = i := by
                    ext
                    simp [j]
                    omega
                  have hj : i = Fin.natAdd m j := hj'.symm
                  rw [hj]
                  simp [Pi.add_apply]
            · simp
          map_smul' := by
            intro a p
            apply Prod.ext
            · ext i
              cases Nat.lt_or_ge i.1 m with
              | inl hi =>
                  simp [Fin.append, Fin.addCases, hi, Pi.smul_apply]
              | inr hi =>
                  let j : Fin n := ⟨i.1 - m, by omega⟩
                  have hj' : Fin.natAdd m j = i := by
                    ext
                    simp [j]
                    omega
                  have hj : i = Fin.natAdd m j := hj'.symm
                  rw [hj]
                  simp [Pi.smul_apply]
            · simp }
      map_vadd' := by
        intro p q
        apply Prod.ext
        · ext i
          cases Nat.lt_or_ge i.1 m with
          | inl hi =>
              simp [vadd_eq_add, Fin.append, Fin.addCases, hi, Pi.add_apply]
          | inr hi =>
              let j : Fin n := ⟨i.1 - m, by omega⟩
              have hj' : Fin.natAdd m j = i := by
                ext
                simp [j]
                omega
              have hj : i = Fin.natAdd m j := hj'.symm
              rw [hj]
              simp [vadd_eq_add, Pi.add_apply]
        · simp [vadd_eq_add] }
  have hpre :
      ERealEpigraph (bifunctionInverse K u) =
        φ ⁻¹' epigraph (Set.univ : Set (Fin (m + n) → ℝ))
          (bifunctionGraphFunction (bifunctionInverse K)) := by
    ext p
    constructor
    · intro hp
      constructor
      · show Fin.append u p.1 ∈ (Set.univ : Set (Fin (m + n) → ℝ))
        trivial
      · simpa [ERealEpigraph, epigraph, φ, bifunctionGraphFunction] using hp
    · intro hp
      simpa [ERealEpigraph, epigraph, φ, bifunctionGraphFunction] using hp.2
  -- Convexity is stable under affine preimages, so the frozen slice inherits convex epigraph.
  simpa [hpre] using (Convex.affine_preimage φ hInverseGraphConvexOn)

/-- Helper for Corollary 38.5.1: a closed proper concave bifunction becomes a fiberwise proper
convex theorem-38.5 input after inversion, and its graph is proper convex in the Chapter 6 sense.
-/
lemma helperForCorollary_38_5_1_packagedAdjointInverse_fiberwiseProperConvex
    {m n : Nat} (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (_hK_closed : ClosedConcaveBifunction (m := n) (n := m) K)
    (hK_proper : ProperConcaveBifunction (m := n) (n := m) K) :
    ∃ H : FiberwiseProperConvexBifunction m n,
      H.toFun = bifunctionInverse K ∧ ProperConvexBifunction H.toFun := by
  have hInverseProperConvex :
      ProperConvexBifunction (m := m) (n := n) (bifunctionInverse K) :=
    helperForCorollary_38_5_1_properConcave_inverse_properConvex
      (K := K) hK_proper
  have hInverseSliceConvex :
      ∀ u : Fin m → ℝ, IsERealConvex (bifunctionInverse K u) := by
    exact helperForCorollary_38_5_1_inverse_sliceConvex_of_properConvex
      (K := K) hInverseProperConvex
  refine ⟨{
      toFun := bifunctionInverse K
      proper := ?_
      convex := hInverseSliceConvex
    }, rfl, hInverseProperConvex⟩
  -- The Chapter 38 bundle only remembers no-`⊥` values plus one non-`⊤` witness.
  constructor
  · intro u x
    have hNoTop : bifunctionGraphFunction K (Fin.append x u) ≠ (⊤ : EReal) := by
      simpa [ProperConcaveERealFunction] using hK_proper.2.1.1 (Fin.append x u)
    simpa [bifunctionGraphFunction, bifunctionInverse, EReal.neg_eq_bot_iff] using hNoTop
  · rcases hK_proper.2.1.2 with ⟨z, hz⟩
    refine ⟨fun i : Fin m => z (Fin.natAdd n i), fun j : Fin n => z (Fin.castAdd m j), ?_⟩
    simpa [bifunctionGraphFunction, bifunctionInverse, EReal.neg_eq_top_iff] using hz



end Section38
end Chap08
