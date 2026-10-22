/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part12

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Chap08
section Section39

namespace ConvexProcess

/-- The textbook Chapter 39 dual image `A^{*-1} f^*`, represented under the current local
conventions as the indicator-image operator built from the inverse fibers of `adjointVec A`. -/
noncomputable def textbookDualImage {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  bifunctionImageRaw
    (indicatorBifunctionSetValued (setValuedInverse (adjointVec A).toSetValued))
    (fenchelConjugate m f)

/-- The Section 38 surrogate dual image obtained by specializing `F_*^* f^*` to the indicator
bifunction of a convex process. This is the object currently produced by the local Theorem 38.4
pipeline, even though it is not the textbook `A^{*-1} f^*`. -/
noncomputable def theoremLocalDualImage {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  bifunctionImageRaw
    (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
    (fenchelConjugate m f)

/-- The Chapter 39 dual image built from `adjointVec A` matches the Chapter 38 indicator-image
operator when applied to `f^*`. -/
lemma sInf_image_adjointVec_fenchelConjugate_eq_bifunctionImageRaw_indicator_of_proper
    {m n : ℕ} (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) (hf : IsProperEReal f) :
    (fun xStar => sInf ((fenchelConjugate m f) '' (adjointVec A).toSetValued xStar)) =
      textbookDualImage A f := by
  -- Reduce the textbook `sInf` expression to the Chapter 39 indicator-image formula.
  refine sInf_image_adjointVec_eq_bifunctionImageRaw_indicator_of_noBot A
    (g := fenchelConjugate m f) ?_
  exact fenchelConjugate_ne_bot_of_exists_ne_top m f hf.2

/-- Helper for Theorem 39.7: the textbook set-valued adjoint image `A^{*-1} f^*` is exactly the
Chapter 39 indicator-image formula built from `adjointVec A`. -/
lemma helperForTheorem_39_7_textbook_value_eq_indicator_dual_image
    {m n : ℕ} (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) (hf : IsProperEReal f) :
    (fun xStar => sInf ((fenchelConjugate m f) '' (adjointVec A).toSetValued xStar)) =
      textbookDualImage A f := by
  -- Reuse the generic Chapter 39 indicator-image rewrite specialized to `f^*`.
  exact sInf_image_adjointVec_fenchelConjugate_eq_bifunctionImageRaw_indicator_of_proper A f hf

/-- Helper for Theorem 39.7: applying `erealFunctionClosure` preserves the established rewrite
from the textbook `A^{*-1} f^*` formula to the Chapter 39 indicator-image operator. -/
lemma helperForTheorem_39_7_closure_textbook_value_eq_closure_indicator_dual_image
    {m n : ℕ} (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) (hf : IsProperEReal f) :
    erealFunctionClosure
      (fun xStar => sInf ((fenchelConjugate m f) '' (adjointVec A).toSetValued xStar)) =
        erealFunctionClosure (textbookDualImage A f) := by
  -- Rewrite the underlying function before applying closure.
  rw [helperForTheorem_39_7_textbook_value_eq_indicator_dual_image A f hf]

/-- Helper for Theorem 39.7: once the Chapter 38 dual-image operator is identified with the
Chapter 39 indicator-image operator, the same bridge remains valid after taking
`erealFunctionClosure`. -/
lemma helperForTheorem_39_7_closure_of_bookAdjoint_image_bridge
    {m n : ℕ} {A : ConvexProcess m n} {f : (Fin m → ℝ) → EReal}
    (hBridge :
      theoremLocalDualImage A f = textbookDualImage A f) :
    erealFunctionClosure (theoremLocalDualImage A f) =
      erealFunctionClosure (textbookDualImage A f) := by
  -- Apply closure to the already-established value-level bridge.
  simpa using congrArg erealFunctionClosure hBridge

/- The former identity-lower-process counterexample chain used the pre-Section-38
  concave-adjoint semantics.  Under the current joint Fenchel definition of
  `bifunctionInverseBookAdjoint`, its claimed `bot` value at the origin is false,
  so the unused legacy chain is intentionally omitted. -/

/-- Specialization of Theorem 38.4 to the indicator bifunction of a convex process. This is the
book's Chapter 39 primal-dual conjugacy theorem before identifying the Chapter 38 object `F_*^*`
with the textbook set-valued adjoint image `A^{*-1}`. -/
lemma convexProcess_indicator_image_conjugate {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f) :
    IsERealConvex (infPreimageEReal A f) ∧
      (Set.Nonempty (ri (erealDom f) ∩ ri A.dom) →
        fenchelConjugate n (infPreimageEReal A f) =
          theoremLocalDualImage A f ∧
        (∀ xStar : Fin n → ℝ,
          ∃ uStar : Fin m → ℝ,
            theoremLocalDualImage A f xStar =
              fenchelConjugate m f uStar +
                (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
                  uStar xStar)) := by
  have h38 :=
    theorem38_4_image_convex_and_conjugate
      (F := ConvexProcess.indicatorBifunction A) (f := f)
      (hF_proper := indicatorBifunction_isProperEReal A)
      (hF_convex := indicatorBifunction_isERealConvex A)
      (hf_proper := hf_proper) (hf_convex := hf_convex)
  refine ⟨?_, ?_⟩
  · simpa [infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper A f hf_proper] using h38.1
  · intro hri
    have hri38 :
        (intrinsicInterior ℝ (erealDom f) ∩
            intrinsicInterior ℝ (bifunctionDom (ConvexProcess.indicatorBifunction A))).Nonempty := by
      simpa [bifunctionDom_indicatorBifunction_eq_dom] using hri
    simpa [infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper A f hf_proper] using h38.2 hri38

/-- Theorem 39.7, theorem-local value-function form: specialize Theorem 38.4 to the indicator
bifunction of a convex process and keep the resulting Chapter 38 dual image
`bifunctionImageRaw (bifunctionInverseBookAdjoint (indicatorBifunction A)) (f^*)`.

The separate textbook rewrite to `x* ↦ inf_{u* ∈ A* x*} f*(u*)` requires its own bridge, so this
lemma records exactly the object supplied by the current Section 38 API. -/
lemma convexProcess_indicator_image_conjugate_theorem_local_value {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f) :
    IsERealConvex (infPreimageEReal A f) ∧
      (Set.Nonempty (ri (erealDom f) ∩ ri A.dom) →
        fenchelConjugate n (infPreimageEReal A f) = theoremLocalDualImage A f ∧
        (∀ xStar : Fin n → ℝ,
          ∃ uStar : Fin m → ℝ,
            theoremLocalDualImage A f xStar =
              fenchelConjugate m f uStar +
                (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
                  uStar xStar)) := by
  exact convexProcess_indicator_image_conjugate A f hf_proper hf_convex

/-- Specialization of Corollary 38.4.1 to the indicator bifunction of a closed convex process.
This is the Chapter 39 closed-image statement before replacing the Chapter 38 dual object
`F_*^* f^*` by the textbook `A^{*-1} f^*`. -/
lemma closed_convexProcess_indicator_image_conjugate_closure {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal)
    (hA_closed : A.IsClosed) (hf_closed : IsClosedEReal f)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom (fenchelConjugate m f)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverseBookAdjoint
                (ConvexProcess.indicatorBifunction A)))).Nonempty) :
    IsClosedEReal (infPreimageEReal A f) ∧
      (∀ x : Fin n → ℝ,
        ∃ u : Fin m → ℝ,
          infPreimageEReal A f x = f u + ConvexProcess.indicatorBifunction A u x) ∧
      fenchelConjugate n (infPreimageEReal A f) =
        erealFunctionClosure (theoremLocalDualImage A f) := by
  have hf_lsc :
      LowerSemicontinuous f :=
    lowerSemicontinuous_of_IsClosedEReal hf_closed
  have h38 :=
    corollary38_4_1_image_closed_and_infimum_attained_and_conjugate_eq_closure
      (F := ConvexProcess.indicatorBifunction A) (f := f)
      (hF_closed := indicatorBifunction_isProductLowerSemicontinuous_of_closed A hA_closed)
      (hF_proper := indicatorBifunction_isProperEReal A)
      (hF_convex := indicatorBifunction_isERealConvex A)
      (hf_closed := hf_lsc) (hf_proper := hf_proper) (hf_convex := hf_convex)
      hri
  have hLscImage : LowerSemicontinuous (infPreimageEReal A f) := by
    simpa [infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper A f hf_proper] using h38.1
  have hAttain :
      ∀ x : Fin n → ℝ,
        ∃ u : Fin m → ℝ,
          infPreimageEReal A f x = f u + ConvexProcess.indicatorBifunction A u x := by
    simpa [infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper A f hf_proper] using h38.2.1
  have hConj :
      fenchelConjugate n (infPreimageEReal A f) =
        erealFunctionClosure (theoremLocalDualImage A f) := by
    simpa [infPreimageEReal_eq_bifunctionImageRaw_indicator_of_proper A f hf_proper] using h38.2.2
  exact
    ⟨isClosedEReal_of_lowerSemicontinuous hLscImage, hAttain, hConj⟩

/-- Theorem 39.7, theorem-local closure form: in the closed case, keep the Chapter 38 closure
formula for the surrogate dual image `F_*^* f^*`.

This lemma records the theorem-local statement supplied directly by Corollary 38.4.1. -/
lemma closed_convexProcess_indicator_image_conjugate_theorem_local_closure {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal)
    (hA_closed : A.IsClosed) (hf_closed : IsClosedEReal f)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom (fenchelConjugate m f)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverseBookAdjoint
                (ConvexProcess.indicatorBifunction A)))).Nonempty) :
    IsClosedEReal (infPreimageEReal A f) ∧
      (∀ x : Fin n → ℝ,
        ∃ u : Fin m → ℝ,
          infPreimageEReal A f x = f u + ConvexProcess.indicatorBifunction A u x) ∧
      fenchelConjugate n (infPreimageEReal A f) =
        erealFunctionClosure (theoremLocalDualImage A f) := by
  exact
    closed_convexProcess_indicator_image_conjugate_closure
      A f hA_closed hf_closed hf_proper hf_convex hri


end ConvexProcess

end Section39
end Chap08
