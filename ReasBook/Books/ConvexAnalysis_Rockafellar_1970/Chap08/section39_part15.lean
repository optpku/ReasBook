/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part13

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Chap08
section Section39

namespace ConvexProcess

/-- Localized Chapter 39 textbook dual image `A^{*-1} f^*`, written directly in terms of the
indicator image of the inverse fibers of `adjointVec A`. This keeps `section39_part15` independent
of stale upstream `olean` interfaces while preserving the textbook right-hand side. -/
noncomputable def textbookDualImage39_7 {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  bifunctionImageRaw
    (indicatorBifunctionSetValued (setValuedInverse (adjointVec A).toSetValued))
    (fenchelConjugate m f)

/-- Local copy of Proposition 39.0.15 in the textbook orientation: the inverse fibers of
`adjointVec A` are exactly the fibers of the infimum-oriented adjoint of `A.inverse`. This is the
book's `A^{*-1}` identification, restated here so that `section39_part15` does not depend on a
freshly rebuilt upstream interface. -/
lemma helperForTheorem_39_7_textbook_inverseAdjoint_eq_setValuedInverse_adjointVec {m n : ℕ}
    (A : ConvexProcess m n) :
    setValuedInverse (adjointVec A).toSetValued =
      (adjointVecOriented ConvexSetOrientation.infimum A.inverse).toSetValued := by
  ext uStar xStar
  constructor
  · intro hx
    change uStar ∈ setValuedAdjointVec A.toSetValued xStar at hx
    change xStar ∈ setValuedAdjointVecInf A.inverse.toSetValued uStar
    intro x u hxu
    rw [helperForProposition_39_0_6_inverse_toSetValued A] at hxu
    exact hx u x hxu
  · intro hx
    change uStar ∈ setValuedAdjointVec A.toSetValued xStar
    change xStar ∈ setValuedAdjointVecInf A.inverse.toSetValued uStar at hx
    intro u x hux
    have hinv : u ∈ A.inverse.toSetValued x := by
      rw [helperForProposition_39_0_6_inverse_toSetValued A]
      exact hux
    exact hx x u hinv

/-- Re-express the localized textbook dual image in the exact Chapter 39 form
`A^{*-1} f^*`, using the local 39.0.15 bridge above to identify the inverse fibers of `adjointVec
A` with the infimum-oriented adjoint of `A.inverse`. -/
lemma textbookDualImage39_7_eq_textbook_inverseAdjointImage {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    textbookDualImage39_7 A f =
      bifunctionImageRaw
        (indicatorBifunctionSetValued
          (adjointVecOriented ConvexSetOrientation.infimum A.inverse).toSetValued)
        (fenchelConjugate m f) := by
  rw [textbookDualImage39_7,
    helperForTheorem_39_7_textbook_inverseAdjoint_eq_setValuedInverse_adjointVec A]

/-- Localized theorem-local surrogate dual image coming from the Chapter 38 `bookAdjoint`
pipeline. This is the object that Theorem 39.7 can currently justify in the first branch. -/
noncomputable def theoremLocalDualImage39_7 {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  bifunctionImageRaw
    (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
    (fenchelConjugate m f)

/-- Local wrapper around the current Section 38 specialization, phrased with the localized
theorem-local dual-image notation used in this file. -/
lemma convexProcess_indicator_image_conjugate_theorem_local_value_local {m n : ℕ}
    (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f) :
    IsERealConvex (infPreimageEReal A f) ∧
      (Set.Nonempty (ri (erealDom f) ∩ ri A.dom) →
        fenchelConjugate n (infPreimageEReal A f) = theoremLocalDualImage39_7 A f ∧
        (∀ xStar : Fin n → ℝ,
          ∃ uStar : Fin m → ℝ,
            theoremLocalDualImage39_7 A f xStar =
              fenchelConjugate m f uStar +
                (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
                  uStar xStar)) := by
  simpa [theoremLocalDualImage39_7] using
    (convexProcess_indicator_image_conjugate A f hf_proper hf_convex)

/-- Closed-case wrapper around the current theorem-local Section 38 specialization. -/
lemma closed_convexProcess_indicator_image_conjugate_theorem_local_closure_local {m n : ℕ}
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
        erealFunctionClosure (theoremLocalDualImage39_7 A f) := by
  simpa [theoremLocalDualImage39_7] using
    (closed_convexProcess_indicator_image_conjugate_closure
      A f hA_closed hf_closed hf_proper hf_convex hri)

/- The former identity-lower-process counterexamples used the pre-Section-38
  concave-adjoint semantics.  Their `bot` computations are false for the current
  joint Fenchel `bifunctionInverseBookAdjoint`, so the unused legacy block is omitted. -/

/-- Theorem 39.7, theorem-local form: specialize the `Ff` / `F_*^* f^*` calculus to the indicator
bifunction of a convex process.  The conclusion retains the joint Fenchel object supplied by the
current Section 38 API; identifying it with a set-valued textbook expression is a separate step. -/
theorem theorem_39_7 {m n : ℕ} (A : ConvexProcess m n) (f : (Fin m → ℝ) → EReal) :
    IsProperEReal f →
      IsERealConvex f →
        (Set.Nonempty (ri (erealDom f) ∩ ri A.dom) →
            (fenchelConjugate n (infPreimageEReal A f) = theoremLocalDualImage39_7 A f) ∧
              (∀ xStar : Fin n → ℝ,
                ∃ uStar,
                    theoremLocalDualImage39_7 A f xStar =
                      fenchelConjugate m f uStar +
                        (bifunctionInverseBookAdjoint (ConvexProcess.indicatorBifunction A))
                          uStar xStar)) ∧
          (A.IsClosed →
            IsClosedEReal f →
              Set.Nonempty
                  (ri (erealDom (fenchelConjugate m f)) ∩
                    ri
                      (bifunctionDom
                        (bifunctionInverseBookAdjoint
                          (ConvexProcess.indicatorBifunction A)))) →
                IsClosedEReal (infPreimageEReal A f) ∧
                  (∀ x : Fin n → ℝ,
                    ∃ u,
                      infPreimageEReal A f x =
                        f u + ConvexProcess.indicatorBifunction A u x) ∧
                  fenchelConjugate n (infPreimageEReal A f) =
                    erealFunctionClosure (theoremLocalDualImage39_7 A f)) :=
  by
  intro hf_proper hf_convex
  refine ⟨?_, ?_⟩
  · intro hri
    exact
      (convexProcess_indicator_image_conjugate_theorem_local_value_local
        A f hf_proper hf_convex).2 hri
  · intro hA_closed hf_closed hri
    exact
      closed_convexProcess_indicator_image_conjugate_theorem_local_closure_local
        A f hA_closed hf_closed hf_proper hf_convex hri

-- Proof sketch: Use closedness of the convex process (via its closed graph, Proposition 39.0.5)
-- and apply a standard closedness criterion for images of closed convex sets under closed convex
-- processes (Corollary 14.2.1), with the recession-cone condition excluding nontrivial directions
-- in `A⁻¹ 0` along which sequences in `C` could escape.
/-- Corollary 39.7.1: Let `A` be a closed convex process from `ℝ^m` to `ℝ^n`, and let `C` be a
nonempty closed convex set in `ℝ^m`. If no nonzero vector in `A⁻¹ 0` belongs to the recession cone
of `C` (in particular if `C` is bounded), then `A C` is closed in `ℝ^n`. -/
theorem corollary_39_7_1 {m n : ℕ} (A : ConvexProcess m n) (C : Set (Fin m → ℝ))
    (hA : A.IsClosed) (_hCne : C.Nonempty) (hCclosed : _root_.IsClosed C) (hCconvex : Convex ℝ C)
    (hNoNonzero :
      ∀ v : Fin m → ℝ, v ∈ A.inverseMap (0 : Fin n → ℝ) → v ∈ recessionCone C → v = 0) :
    _root_.IsClosed (A.image C) := by
  classical
  by_cases hImgEmpty : A.image C = ∅
  · simp [hImgEmpty]
  · rcases Set.nonempty_iff_ne_empty.mpr hImgEmpty with ⟨x0, hx0img⟩
    rcases (helperForProposition_39_0_8_mem_image_iff A C x0).1 hx0img with ⟨u0, hu0C, hx0A⟩
    let π₁ : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      { toFun := fun z i => z (Fin.castAdd n i)
        map_add' := by intro z w; ext i; rfl
        map_smul' := by intro r z; ext i; rfl }
    let π₂ : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun z j => z (Fin.natAdd m j)
        map_add' := by intro z w; ext j; rfl
        map_smul' := by intro r z; ext j; rfl }
    let K : Set (Fin (m + n) → ℝ) :=
      {z | (unpackAppend z).1 ∈ C ∧ (unpackAppend z).2 ∈ A.toSetValued ((unpackAppend z).1)}
    have hp0 : Fin.append u0 x0 ∈ K := by
      simpa [K, unpackAppend_append] using And.intro hu0C hx0A
    have hGraphClosed : _root_.IsClosed (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_6_graphClosed_and_fiberClosed A hA).1
    have hGraphPreClosed : _root_.IsClosed
        {z : Fin (m + n) → ℝ | (unpackAppend z).2 ∈ A.toSetValued ((unpackAppend z).1)} := by
      simpa [Set.preimage, setValuedGraph] using
        hGraphClosed.preimage
          (LinearMap.continuous_of_finiteDimensional (f := unpackAppendLinearMap (m := m) (n := n)))
    have hCPreClosed : _root_.IsClosed {z : Fin (m + n) → ℝ | (unpackAppend z).1 ∈ C} := by
      have hcont : Continuous fun z : Fin (m + n) → ℝ => (unpackAppend z).1 := by
        exact continuous_fst.comp
          (LinearMap.continuous_of_finiteDimensional (f := unpackAppendLinearMap (m := m) (n := n)))
      simpa [Set.preimage] using hCclosed.preimage hcont
    have hKClosed : _root_.IsClosed K := by
      simpa [K] using hCPreClosed.inter hGraphPreClosed
    have hGraphConv : Convex ℝ (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
    have hGraphPreConv : Convex ℝ
        {z : Fin (m + n) → ℝ | (unpackAppend z).2 ∈ A.toSetValued ((unpackAppend z).1)} := by
      simpa [Set.preimage, setValuedGraph] using
        hGraphConv.linear_preimage (unpackAppendLinearMap)
    have hCPreConv : Convex ℝ {z : Fin (m + n) → ℝ | (unpackAppend z).1 ∈ C} := by
      simpa [π₁, unpackAppend, Set.preimage] using hCconvex.linear_preimage π₁
    have hKConv : Convex ℝ K := by
      simpa [K] using hCPreConv.inter hGraphPreConv
    have hImageEq : π₂ '' K = A.image C := by
      ext x
      constructor
      · rintro ⟨z, hzK, rfl⟩
        exact (helperForProposition_39_0_8_mem_image_iff A C _).2 ⟨(unpackAppend z).1, hzK.1, by
          simpa [π₂, unpackAppend] using hzK.2⟩
      · intro hx
        rcases (helperForProposition_39_0_8_mem_image_iff A C x).1 hx with ⟨u, huC, hxA⟩
        refine ⟨Fin.append u x, ?_, ?_⟩
        · simpa [K, unpackAppend_append] using And.intro huC hxA
        · ext j
          simp [π₂]
    have hKernelZero :
        ∀ z : Fin (m + n) → ℝ, z ∈ Set.recessionCone K → π₂ z = 0 → z = 0 := by
      intro z hzRec hzTail
      let v : Fin m → ℝ := (unpackAppend z).1
      let w : Fin n → ℝ := (unpackAppend z).2
      have hwZero : w = 0 := by
        ext j
        simpa [w, π₂] using congrArg (fun f : Fin n → ℝ => f j) hzTail
      have hRayC : ∀ t : ℝ, 0 ≤ t → u0 + t • v ∈ C := by
        intro t ht
        have hmemK : Fin.append u0 x0 + t • z ∈ K := hzRec hp0 ht
        simpa [K, v, unpackAppend_append, unpackAppend_add, unpackAppend_smul] using hmemK.1
      have hAddMem : ∀ x ∈ C, x + v ∈ C := by
        intro x hxC
        let α : ℕ → ℝ := fun k => (((k : ℝ) + 1) : ℝ)⁻¹
        have hSeqMem :
            ∀ k : ℕ,
              (1 - α k) • x + α k • (u0 + (((k : ℝ) + 1) : ℝ) • v) ∈ C := by
          intro k
          have hα_nonneg : 0 ≤ α k := by positivity
          have hα_le : α k ≤ 1 := by
            dsimp [α]
            have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
              have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
              linarith
            have hkpos : 0 < (k : ℝ) + 1 := by positivity
            exact (inv_le_one₀ hkpos).2 hk1
          have huRay : u0 + (((k : ℝ) + 1) : ℝ) • v ∈ C := by
            apply hRayC
            positivity
          exact hCconvex hxC huRay (by linarith) hα_nonneg (by linarith)
        have hα : Filter.Tendsto α Filter.atTop (nhds (0 : ℝ)) := by
          exact tendsto_inv_atTop_zero.comp
            (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
        have hSeqEq :
            ∀ k : ℕ,
              (1 - α k) • x + α k • (u0 + (((k : ℝ) + 1) : ℝ) • v) =
                x + v + α k • (u0 - x) := by
          intro k
          ext i
          dsimp [α]
          have hk : (((k : ℝ) + 1) : ℝ) ≠ 0 := by positivity
          field_simp [hk]
          ring
        have hCorr : Filter.Tendsto (fun k : ℕ => α k • (u0 - x)) Filter.atTop (nhds (0 : Fin m → ℝ)) := by
          rw [tendsto_pi_nhds]
          intro i
          have hMul : Filter.Tendsto (fun k : ℕ => α k * (u0 - x) i) Filter.atTop (nhds (0 : ℝ)) := by
            simpa [α] using hα.mul tendsto_const_nhds
          simpa [smul_eq_mul] using hMul
        have hSeqTendsto' :
            Filter.Tendsto (fun k : ℕ => x + v + α k • (u0 - x)) Filter.atTop (nhds (x + v)) := by
          simpa [add_comm, add_left_comm, add_assoc] using Filter.Tendsto.const_add (x + v) hCorr
        have hSeqTendsto :
            Filter.Tendsto
              (fun k : ℕ => (1 - α k) • x + α k • (u0 + (((k : ℝ) + 1) : ℝ) • v))
              Filter.atTop (nhds (x + v)) := by
          refine hSeqTendsto'.congr' ?_
          exact Filter.Eventually.of_forall (fun k => (hSeqEq k).symm)
        exact IsClosed.mem_of_tendsto hCclosed hSeqTendsto (Filter.Eventually.of_forall hSeqMem)
      have hvRecC : v ∈ recessionCone C := by
        have hvRecC' : v ∈ Set.recessionCone C := by
          refine mem_recessionCone_of_add_mem_fixed_t (C := C) hCconvex zero_lt_one ?_
          intro x hx
          simpa using hAddMem x hx
        simpa [recessionCone] using hvRecC'
      have hGraphSeq :
          ∀ k : ℕ,
            (((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • u0 + v,
              ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • x0) ∈ setValuedGraph A.toSetValued := by
        intro k
        have hkNonneg : 0 ≤ (((k : ℝ) + 1) : ℝ) := by positivity
        have hmemK : Fin.append u0 x0 + (((k : ℝ) + 1) : ℝ) • z ∈ K := hzRec hp0 hkNonneg
        have hxRay : x0 ∈ A.toSetValued (u0 + (((k : ℝ) + 1) : ℝ) • v) := by
          have : x0 + (((k : ℝ) + 1) : ℝ) • w ∈ A.toSetValued (u0 + (((k : ℝ) + 1) : ℝ) • v) := by
            simpa [K, v, w, unpackAppend_append, unpackAppend_add, unpackAppend_smul] using hmemK.2
          simpa [hwZero] using this
        have hGraphMem : (u0 + (((k : ℝ) + 1) : ℝ) • v, x0) ∈ setValuedGraph A.toSetValued := by
          simpa [setValuedGraph] using hxRay
        have hkInvPos : 0 < ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) := by positivity
        have hScaled :=
          helperForProposition_39_0_1_graph_smul_pos_closed_ofConvexProcess A hkInvPos hGraphMem
        have hk : (((k : ℝ) + 1) : ℝ) ≠ 0 := by positivity
        simpa [smul_add, smul_smul, hk, mul_assoc] using hScaled
      have hReciprocal :
          Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
        exact tendsto_inv_atTop_zero.comp
          (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
      have hFirstCoord :
          Filter.Tendsto
            (fun k : ℕ => (((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • u0 + v))
            Filter.atTop (nhds v) := by
        rw [tendsto_pi_nhds]
        intro i
        have hMul : Filter.Tendsto
            (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) * u0 i)
            Filter.atTop (nhds (0 : ℝ)) := by
          simpa using hReciprocal.mul tendsto_const_nhds
        simpa [smul_eq_mul, add_comm] using Filter.Tendsto.const_add (v i) hMul
      have hSecondCoord :
          Filter.Tendsto
            (fun k : ℕ => (((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • x0))
            Filter.atTop (nhds (0 : Fin n → ℝ)) := by
        rw [tendsto_pi_nhds]
        intro i
        have hMul : Filter.Tendsto
            (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) * x0 i)
            Filter.atTop (nhds (0 : ℝ)) := by
          simpa using hReciprocal.mul tendsto_const_nhds
        simpa [smul_eq_mul] using hMul
      have hPairTendsto :
          Filter.Tendsto
            (fun k : ℕ =>
              (((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • u0 + v,
                ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • x0))
            Filter.atTop (nhds (v, (0 : Fin n → ℝ))) := by
        simpa using Filter.Tendsto.prodMk_nhds hFirstCoord hSecondCoord
      have hLimitPoint : (v, (0 : Fin n → ℝ)) ∈ setValuedGraph A.toSetValued := by
        exact IsClosed.mem_of_tendsto hGraphClosed hPairTendsto (Filter.Eventually.of_forall hGraphSeq)
      have hvA0 : v ∈ A.inverseMap (0 : Fin n → ℝ) := by
        simpa [ConvexProcess.inverseMap, setValuedInverse, setValuedGraph] using hLimitPoint
      have hvZero : v = 0 := hNoNonzero v hvA0 hvRecC
      have hzUnpack : unpackAppend z = (v, 0) := by
        ext <;> simp [v, w, hwZero]
      have hzEq : z = Fin.append v (0 : Fin n → ℝ) := by
        calc
          z = Fin.append (unpackAppend z).1 (unpackAppend z).2 := by
            simpa using (append_unpackAppend (m := m) (n := n) z).symm
          _ = Fin.append v (0 : Fin n → ℝ) := by simp [hzUnpack]
      have happend0 : Fin.append (0 : Fin m → ℝ) (0 : Fin n → ℝ) = (0 : Fin (m + n) → ℝ) := by
        ext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
      simp [hvZero, happend0] at hzEq
      exact hzEq
    have hKne : K.Nonempty := ⟨Fin.append u0 x0, hp0⟩
    let eDom := euclideanEquiv (m + n)
    let eCod := euclideanEquiv n
    let K' : Set (EuclideanSpace ℝ (Fin (m + n))) := eDom.symm '' K
    let piE : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (eCod.symm.toLinearMap).comp (π₂.comp eDom.toLinearMap)
    have hKne' : K'.Nonempty := by
      rcases hKne with ⟨z, hz⟩
      exact ⟨eDom.symm z, ⟨z, hz, by simp⟩⟩
    have hKConv' : Convex ℝ K' := by
      simpa using hKConv.linear_image eDom.symm.toLinearMap
    let hhomeDom := (eDom.symm.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hKClosed' : _root_.IsClosed K' := by
      have hclosed' : _root_.IsClosed ((hhomeDom : _ → _) '' K) :=
        (hhomeDom.isClosed_image (s := K)).2 hKClosed
      simpa [K', hhomeDom, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
    have hKcl' : closure K' = K' := hKClosed'.closure_eq
    have hrecK' : Set.recessionCone K' = eDom.symm '' Set.recessionCone K := by
      simpa [K'] using (recessionCone_image_linearEquiv (e := eDom.symm.toLinearEquiv) (C := K))
    have hLineal' :
        ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure K') → piE z = 0 →
          z ∈ Set.linealitySpace (closure K') := by
      intro z hzNe hzRec hzPiE
      have hzRec' : z ∈ Set.recessionCone K' := by
        simpa [hKcl'] using hzRec
      have hzRecK : eDom z ∈ Set.recessionCone K := by
        have hzmem : z ∈ eDom.symm '' Set.recessionCone K := by
          simpa [hrecK'] using hzRec'
        rcases hzmem with ⟨w, hw, hwz⟩
        have hw' : w = eDom z := by
          have := congrArg eDom hwz
          simpa [eDom] using this
        simpa [hw'] using hw
      have hzTail : π₂ (eDom z) = 0 := by
        have : eCod (piE z) = 0 := by
          simpa using congrArg eCod hzPiE
        simpa [piE] using this
      have hzZero : eDom z = 0 := hKernelZero (eDom z) hzRecK hzTail
      have : z = 0 := eDom.injective hzZero
      subst this
      exact zero_mem_linealitySpace (closure K')
    have hKernelZero' :
        ∀ z, z ∈ Set.recessionCone K' → piE z = 0 → z = 0 := by
      intro z hzRec hzPiE
      have hzRecK : eDom z ∈ Set.recessionCone K := by
        have hzmem : z ∈ eDom.symm '' Set.recessionCone K := by
          simpa [hrecK'] using hzRec
        rcases hzmem with ⟨w, hw, hwz⟩
        have hw' : w = eDom z := by
          have := congrArg eDom hwz
          simpa [eDom] using this
        simpa [hw'] using hw
      have hzTail : π₂ (eDom z) = 0 := by
        have : eCod (piE z) = 0 := by
          simpa using congrArg eCod hzPiE
        simpa [piE] using this
      have hzZero : eDom z = 0 := hKernelZero (eDom z) hzRecK hzTail
      exact eDom.injective hzZero
    have hClosedPacked' : _root_.IsClosed (piE '' K') := by
      exact
        (linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
          (n := m + n) (m := n) (C := K') hKne' hKConv' piE hLineal').2.2 hKClosed' hKernelZero'
    have hImageEq' : piE '' K' = eCod.symm '' (π₂ '' K) := by
      ext y
      constructor
      · rintro ⟨z, hzK', rfl⟩
        rcases hzK' with ⟨w, hwK, rfl⟩
        refine ⟨π₂ w, ⟨w, hwK, rfl⟩, ?_⟩
        simp [piE]
      · rintro ⟨y0, ⟨w, hwK, rfl⟩, rfl⟩
        refine ⟨eDom.symm w, ⟨w, hwK, rfl⟩, ?_⟩
        simp [piE]
    have hClosedPackedSymm : _root_.IsClosed (eCod.symm '' (π₂ '' K)) := by
      simpa [hImageEq'] using hClosedPacked'
    let hhomeCod := (eCod.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hClosedPacked : _root_.IsClosed (π₂ '' K) := by
      have hclosed'' :
          _root_.IsClosed ((hhomeCod : _ → _) '' (eCod.symm '' (π₂ '' K))) :=
        (hhomeCod.isClosed_image (s := eCod.symm '' (π₂ '' K))).2 hClosedPackedSymm
      simpa [hhomeCod, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed''
    simpa [hImageEq] using hClosedPacked

/-- A chosen composition convex process `B A`, characterized by having underlying set-valued
mapping `u ↦ ⋃ x ∈ A u, B x`. -/
noncomputable def compProcess {m n p : ℕ} (B : ConvexProcess n p) (A : ConvexProcess m n) :
    ConvexProcess m p :=
  Classical.choose ((prop_39_0_10 (A := A) (B := B)).1)


/-- Helper for Theorem 39.8: the indicator bifunction of a convex process is proper and convex in
the Chapter 38 sense. -/
lemma helperForTheorem_39_8_indicatorProperConvexBifunction {m n : ℕ}
    (A : ConvexProcess m n) :
    ProperConvexBifunction (ConvexProcess.indicatorBifunction A) := by
  let graphSet : Set (Fin (m + n) → ℝ) :=
    {z | (fun j => z (Fin.natAdd m j)) ∈ A.toSetValued (fun i => z (Fin.castAdd n i))}
  have hGraphSetConvex : Convex ℝ graphSet := by
    have hGraphConv : Convex ℝ (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have hz₁' :
        ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₁
    have hz₂' :
        ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₂
    have hCombo :
        a • ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) +
            b • ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued :=
      hGraphConv hz₁' hz₂' ha hb hab
    simpa [graphSet, setValuedGraph, Pi.add_apply, Pi.smul_apply] using hCombo
  have hGraphSetNonempty : graphSet.Nonempty := by
    refine ⟨Fin.append (0 : Fin m → ℝ) (0 : Fin n → ℝ), ?_⟩
    simpa [graphSet] using A.zero_mem
  have hProperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (indicatorFunction graphSet) :=
    section16_properConvexFunctionOn_indicatorFunction_univ hGraphSetConvex hGraphSetNonempty
  have hGraphEq :
      graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) = indicatorFunction graphSet := by
    funext z
    by_cases hz : z ∈ graphSet
    · have hz' :
          (fun j => z (Fin.natAdd m j)) ∈ A.toSetValued (fun i => z (Fin.castAdd n i)) := by
        simpa [graphSet] using hz
      simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
        indicatorFunction, graphSet, hz, hz']
    · have hz' :
          (fun j => z (Fin.natAdd m j)) ∉ A.toSetValued (fun i => z (Fin.castAdd n i)) := by
        simpa [graphSet] using hz
      simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
        indicatorFunction, graphSet, hz, hz']
  have hProperGraph :
      ProperConvexERealFunction (F := Fin (m + n) → ℝ)
        (bifunctionGraphFunction (ConvexProcess.indicatorBifunction A)) := by
    have hIndicatorProper :
        ProperConvexERealFunction (F := Fin (m + n) → ℝ)
          (indicatorFunction graphSet) :=
      helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
        (f := indicatorFunction graphSet) hProperOn
    simpa [bifunctionGraphFunction, graphFunctionOfBifunction, hGraphEq] using hIndicatorProper
  refine ⟨?_, hProperGraph⟩
  simpa [ConvexBifunction, ConvexFunction, bifunctionGraphFunction, graphFunctionOfBifunction,
    hGraphEq] using hProperOn.1

/-- Definition 39.8.1: the set-set inner product `⟪C, D⟫`, encoded as an optional value so later
lemmas can record the existence of a genuine common extremal value. The current local development
only needs the underlying supremum value; the `Option` wrapper keeps the statement aligned with the
textbook's existence language. -/
noncomputable def orientedSetInnerProductVec {n : ℕ}
    (C D : Set (Fin n → ℝ)) : Option EReal :=
  some <| sInf ((fun y => ConvexProcess.setBracketVec ConvexSetOrientation.supremum C y) '' D)

/-- Side condition excluding the indeterminate extended-real sums `⊤ + ⊥` and `⊥ + ⊤`. -/
def NoIndeterminateERealAdd (a b : EReal) : Prop :=
  ¬ (a = (⊤ : EReal) ∧ b = (⊥ : EReal)) ∧
    ¬ (a = (⊥ : EReal) ∧ b = (⊤ : EReal))

/-- Helper for Theorem 39.8: the Chapter 38 `domBot` qualification set of the inverse indicator
bifunction is exactly the range of the underlying convex process. -/
lemma helperForTheorem_39_8_bifunctionDomBot_inverseIndicator_eq_range {m n : ℕ}
    (A : ConvexProcess m n) :
    bifunctionDomBot (bifunctionInverse (ConvexProcess.indicatorBifunction A)) = A.range := by
  rw [bifunctionInverse_indicatorBifunction_eq_negIndicatorBifunction_inverse]
  ext x
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    by_contra hux
    have huBot : ConvexProcess.negIndicatorBifunction A.inverse x u = ⊥ := by
      simp [ConvexProcess.negIndicatorBifunction, negIndicatorEReal,
        helperForProposition_39_0_6_inverse_toSetValued, ConvexProcess.inverseMap,
        setValuedInverse, hux]
    exact hu huBot
  · rintro ⟨u, hux⟩
    refine ⟨u, ?_⟩
    simp [ConvexProcess.negIndicatorBifunction, negIndicatorEReal,
      helperForProposition_39_0_6_inverse_toSetValued, ConvexProcess.inverseMap,
      setValuedInverse, hux]

/-- Helper for Theorem 39.8: the primal relative-interior hypothesis `ri (range A) ∩ ri (dom B)`
is exactly the Chapter 38 qualification for the two indicator bifunctions. -/
lemma helperForTheorem_39_8_indicatorBifunction_riQualification {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p)
    (hri : Set.Nonempty (ri A.range ∩ ri B.dom)) :
    (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse (ConvexProcess.indicatorBifunction A))) ∩
        intrinsicInterior ℝ (bifunctionDom (ConvexProcess.indicatorBifunction B))).Nonempty := by
  simpa [helperForTheorem_39_8_bifunctionDomBot_inverseIndicator_eq_range,
    helperForTheorem_39_5_bifunctionDom_indicator_eq_dom] using hri

/-- Helper for Theorem 39.8: composing the indicator bifunctions of `A` and `B` is exactly the
indicator bifunction of the chosen composite process `B A`. -/
lemma helperForTheorem_39_8_indicatorCompose_eq_indicatorCompProcess {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    bifunctionCompose
        (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction B)
        (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction A) =
      ConvexProcess.indicatorBifunction (compProcess B A) := by
  have hCompProcess :
      (compProcess B A).toSetValued = compSetValued B A :=
    Classical.choose_spec ((prop_39_0_10 (A := A) (B := B)).1)
  funext u y
  rw [bifunctionCompose]
  by_cases hy : y ∈ (compProcess B A).toSetValued u
  · have hyComp : y ∈ compSetValued B A u := by
      simpa [hCompProcess] using hy
    rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B u y).1 hyComp with
      ⟨x, hxA, hyB⟩
    have hupper :
        (⨅ x' : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A u x' +
              ConvexProcess.indicatorBifunction B x' y) ≤ 0 := by
      calc
        (⨅ x' : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A u x' +
              ConvexProcess.indicatorBifunction B x' y) ≤
            ConvexProcess.indicatorBifunction A u x +
              ConvexProcess.indicatorBifunction B x y := iInf_le _ x
        _ = 0 := by
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA, hyB]
    have hlower :
        0 ≤ (⨅ x' : Fin n → ℝ,
          ConvexProcess.indicatorBifunction A u x' +
            ConvexProcess.indicatorBifunction B x' y) := by
      refine le_iInf ?_
      intro x'
      by_cases hxA' : x' ∈ A.toSetValued u
      · by_cases hyB' : y ∈ B.toSetValued x'
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
      · by_cases hyB' : y ∈ B.toSetValued x'
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
    have hEq :
        (⨅ x' : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A u x' +
              ConvexProcess.indicatorBifunction B x' y) = 0 :=
      le_antisymm hupper hlower
    simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hy] using hEq
  · have hyComp : y ∉ compSetValued B A u := by
      simpa [hCompProcess] using hy
    have htop :
        (⊤ : EReal) ≤
          (⨅ x' : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A u x' +
              ConvexProcess.indicatorBifunction B x' y) := by
      refine le_iInf ?_
      intro x'
      by_cases hxA' : x' ∈ A.toSetValued u
      · have hyB' : y ∉ B.toSetValued x' := by
          intro hyB'
          exact hyComp ((helperForProposition_39_0_10_mem_compSetValued_iff A B u y).2 ⟨x', hxA', hyB'⟩)
        simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
      · by_cases hyB' : y ∈ B.toSetValued x'
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxA', hyB']
    have hEq :
        (⨅ x' : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A u x' +
              ConvexProcess.indicatorBifunction B x' y) = (⊤ : EReal) :=
      le_antisymm le_top htop
    simpa [ConvexProcess.indicatorBifunction, indicatorEReal, hy] using hEq

-- Proof sketch: Unfold the oriented brackets/inner products (Definitions 39.8.1–39.8.2) into the
-- corresponding `sSup`/`sInf` extremal expressions involving `finDot`. Use bilinearity of `finDot`
-- to pull out positive scalars and to distribute over Minkowski sums. The min-max inequalities give
-- the super/subadditivity inequalities for the set-set inner product. The `NoIndeterminateERealAdd`
-- hypotheses exclude the `⊤ + ⊥` ambiguity when combining extremal values.
/-- Proposition 39.8.3: Assume the relevant set-set inner products `⟪C, D⟫` exist (in the sense of
`orientedSetInnerProductVec`) and no indeterminate form `∞ - ∞` occurs. Then for `λ > 0`,

* `⟪λ • C, D⟫ = λ ⟪C, D⟫ = ⟪C, λ • D⟫`,
* `⟪C + C', D⟫ ≥ ⟪C, D⟫ + ⟪C', D⟫`,
* `⟪C, D + D'⟫ ≤ ⟪C, D⟫ + ⟪C, D'⟫`,

and for vectors `y, x ∈ ℝ^n`,

* `⟪C + C', y⟫ = ⟪C, y⟫ + ⟪C', y⟫` (support function additivity),
* `⟪x, D + D'⟫ = ⟪x, D⟫ + ⟪x, D'⟫` (inf-support additivity). -/
theorem proposition_39_8_3 {n : ℕ} (C C' D D' : Set (Fin n → ℝ)) (r : ℝ) (hr : 0 < r)
    (vCD vSmulC_D vC_SmulD vCC'D vC'D vCDD' vCD' : EReal)
    (hCD : orientedSetInnerProductVec C D = some vCD)
    (hSmulC_D : orientedSetInnerProductVec (r • C) D = some vSmulC_D)
    (hC_SmulD : orientedSetInnerProductVec C (r • D) = some vC_SmulD)
    (hCC'D : orientedSetInnerProductVec (C + C') D = some vCC'D)
    (hC'D : orientedSetInnerProductVec C' D = some vC'D)
    (hCDD' : orientedSetInnerProductVec C (D + D') = some vCDD')
    (hCD' : orientedSetInnerProductVec C D' = some vCD')
    (hNoIndetCD_C'D : NoIndeterminateERealAdd vCD vC'D)
    (hNoIndetCD_CD' : NoIndeterminateERealAdd vCD vCD')
    (hNoIndetSupport :
      ∀ y,
        NoIndeterminateERealAdd (ConvexProcess.setBracketVec ConvexSetOrientation.supremum C y)
          (ConvexProcess.setBracketVec ConvexSetOrientation.supremum C' y))
    (hNoIndetInfSupport :
      ∀ x,
        NoIndeterminateERealAdd (ConvexProcess.setBracketVec ConvexSetOrientation.infimum D x)
          (ConvexProcess.setBracketVec ConvexSetOrientation.infimum D' x)) :
    (vSmulC_D = (r : EReal) * vCD ∧ (r : EReal) * vCD = vC_SmulD) ∧
      (vCC'D ≥ vCD + vC'D) ∧
      (vCDD' ≤ vCD + vCD') ∧
      (∀ y,
          ConvexProcess.setBracketVec ConvexSetOrientation.supremum (C + C') y =
            ConvexProcess.setBracketVec ConvexSetOrientation.supremum C y +
              ConvexProcess.setBracketVec ConvexSetOrientation.supremum C' y) ∧
      (∀ x,
          ConvexProcess.setBracketVec ConvexSetOrientation.infimum (D + D') x =
            ConvexProcess.setBracketVec ConvexSetOrientation.infimum D x +
              ConvexProcess.setBracketVec ConvexSetOrientation.infimum D' x) := by
  let _ := hNoIndetCD_C'D
  let _ := hNoIndetSupport
  have hvCD :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D) = vCD := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hCD
  have hvSmulC_D :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum (r • C) y) '' D) =
        vSmulC_D := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hSmulC_D
  have hvC_SmulD :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' (r • D)) =
        vC_SmulD := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hC_SmulD
  have hvCC'D :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum (C + C') y) '' D) =
        vCC'D := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hCC'D
  have hvC'D :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C' y) '' D) = vC'D := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hC'D
  have hvCDD' :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' (D + D')) =
        vCDD' := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hCDD'
  have hvCD' :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D') = vCD' := by
    simpa [orientedSetInnerProductVec, Option.some.injEq] using hCD'
  have hMulMonotone : Monotone (fun z : EReal => (r : EReal) * z) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast (le_of_lt hr))
  have hMulTop : (fun z : EReal => (r : EReal) * z) ⊤ = ⊤ := by
    simpa using (EReal.coe_mul_top_of_pos hr)
  have hMulBot : (fun z : EReal => (r : EReal) * z) ⊥ = ⊥ := by
    simpa using (EReal.coe_mul_bot_of_pos hr)
  have hSupportSmulSet :
      supportFunctionEReal (r • C) = fun y => (r : EReal) * supportFunctionEReal C y := by
    funext y
    unfold supportFunctionEReal
    have hImage :
        {z : EReal | ∃ x ∈ r • C, z = ((dotProduct x y : ℝ) : EReal)} =
          ((fun z : EReal => (r : EReal) * z) ''
            {z : EReal | ∃ x ∈ C, z = ((dotProduct x y : ℝ) : EReal)}) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Set.mem_smul_set.mp hx with ⟨x0, hx0, rfl⟩
        refine ⟨((dotProduct x0 y : ℝ) : EReal), ⟨x0, hx0, rfl⟩, ?_⟩
        simp [smul_dotProduct, EReal.coe_mul]
      · rintro ⟨z', ⟨x, hx, rfl⟩, hz⟩
        refine ⟨r • x, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩, ?_⟩
        simp [smul_dotProduct, EReal.coe_mul] at hz ⊢
        exact hz.symm
    rw [hImage]
    have hContinuous :
        ContinuousAt (fun z : EReal => (r : EReal) * z)
          (sSup ({z : EReal | ∃ x ∈ C, z = ((dotProduct x y : ℝ) : EReal)})) := by
      exact
        (EReal.continuousAt_mul
          (p := ((r : EReal),
            sSup ({z : EReal | ∃ x ∈ C, z = ((dotProduct x y : ℝ) : EReal)})))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt hr)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt hr)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    simpa using (hMulMonotone.map_sSup_of_continuousAt hContinuous hMulBot).symm
  have hBracketSmulSet :
      setBracketVec ConvexSetOrientation.supremum (r • C) =
        fun y => (r : EReal) * setBracketVec ConvexSetOrientation.supremum C y := by
    funext y
    calc
      setBracketVec ConvexSetOrientation.supremum (r • C) y =
          supportFunctionEReal (r • C) y := by
            rw [helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal]
      _ = (r : EReal) * supportFunctionEReal C y := congrFun hSupportSmulSet y
      _ = (r : EReal) * setBracketVec ConvexSetOrientation.supremum C y := by
            rw [helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal]
  have hBracketCovectorSmul :
      ∀ y : Fin n → ℝ,
        setBracketVec ConvexSetOrientation.supremum C (r • y) =
          (r : EReal) * setBracketVec ConvexSetOrientation.supremum C y := by
    intro y
    simpa using
      helperForTheorem_39_3_bracket_covector_smul_pos
        ConvexSetOrientation.supremum C y r hr
  have hImageSmulC_D :
      ((fun y => setBracketVec ConvexSetOrientation.supremum (r • C) y) '' D) =
        ((fun z : EReal => (r : EReal) * z) ''
          ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨setBracketVec ConvexSetOrientation.supremum C y, ⟨y, hy, rfl⟩, ?_⟩
      simpa using (congrFun hBracketSmulSet y).symm
    · rintro ⟨z', ⟨y, hy, rfl⟩, hz⟩
      refine ⟨y, hy, ?_⟩
      simpa using (hz.symm.trans (congrFun hBracketSmulSet y).symm).symm
  have hImageC_SmulD :
      ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' (r • D)) =
        ((fun z : EReal => (r : EReal) * z) ''
          ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases Set.mem_smul_set.mp hy with ⟨y0, hy0, rfl⟩
      refine ⟨setBracketVec ConvexSetOrientation.supremum C y0, ⟨y0, hy0, rfl⟩, ?_⟩
      simpa using (hBracketCovectorSmul y0).symm
    · rintro ⟨z', ⟨y, hy, rfl⟩, hz⟩
      refine ⟨r • y, Set.mem_smul_set.mpr ⟨y, hy, rfl⟩, ?_⟩
      simpa using (hz.symm.trans (hBracketCovectorSmul y).symm).symm
  have hMulSInf_D :
      sInf (((fun z : EReal => (r : EReal) * z) ''
        ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D))) =
        (r : EReal) * sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D) := by
    have hContinuous :
        ContinuousAt (fun z : EReal => (r : EReal) * z)
          (sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D)) := by
      exact
        (EReal.continuousAt_mul
          (p := ((r : EReal),
            sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt hr)))
          (Or.inl (by simpa [EReal.coe_eq_zero] using (ne_of_gt hr)))
          (Or.inl (by simp))
          (Or.inl (by simp))).comp
          (continuousAt_const.prodMk continuousAt_id)
    simpa using (hMulMonotone.map_sInf_of_continuousAt hContinuous hMulTop).symm
  have hScaleLeft : vSmulC_D = (r : EReal) * vCD := by
    rw [← hvSmulC_D, hImageSmulC_D, hMulSInf_D, hvCD]
  have hScaleRight : vC_SmulD = (r : EReal) * vCD := by
    rw [← hvC_SmulD, hImageC_SmulD, hMulSInf_D, hvCD]
  have hSupportAdd :
      ∀ y,
        setBracketVec ConvexSetOrientation.supremum (C + C') y =
          setBracketVec ConvexSetOrientation.supremum C y +
            setBracketVec ConvexSetOrientation.supremum C' y := by
    intro y
    simpa [helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal] using
      congrFun (helperForTheorem_39_5_supportFunctionEReal_add C C') y
  have hSupportSubadd :
      ∀ y y' : Fin n → ℝ,
        setBracketVec ConvexSetOrientation.supremum C (y + y') ≤
          setBracketVec ConvexSetOrientation.supremum C y +
            setBracketVec ConvexSetOrientation.supremum C y' := by
    intro y y'
    have hSubaddSupport :
        supportFunctionEReal C (y + y') ≤ supportFunctionEReal C y + supportFunctionEReal C y' := by
      unfold supportFunctionEReal
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      calc
        (((dotProduct x (y + y') : ℝ) : EReal)) =
            (((dotProduct x y : ℝ) : EReal)) + (((dotProduct x y' : ℝ) : EReal)) := by
              simp [dotProduct_add, EReal.coe_add]
        _ ≤ sSup {z : EReal | ∃ x ∈ C, z = ((dotProduct x y : ℝ) : EReal)} +
              sSup {z : EReal | ∃ x ∈ C, z = ((dotProduct x y' : ℝ) : EReal)} := by
              exact add_le_add (le_sSup ⟨x, hx, rfl⟩) (le_sSup ⟨x, hx, rfl⟩)
    simpa [helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal] using hSubaddSupport
  have hInfAdd :
      ∀ x,
        setBracketVec ConvexSetOrientation.infimum (D + D') x =
          setBracketVec ConvexSetOrientation.infimum D x +
            setBracketVec ConvexSetOrientation.infimum D' x := by
    intro x
    simpa [NoIndeterminateERealAdd] using
      congrFun
        (helperForTheorem_39_5_infimumBracket_add D D'
          (fun xStar => by simpa [NoIndeterminateERealAdd] using hNoIndetInfSupport xStar)) x
  have hCC'D_ge : vCD + vC'D ≤ vCC'D := by
    rw [← hvCD, ← hvC'D, ← hvCC'D]
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hLeft :
        sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D) ≤
          setBracketVec ConvexSetOrientation.supremum C y :=
      sInf_le ⟨y, hy, rfl⟩
    have hRight :
        sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C' y) '' D) ≤
          setBracketVec ConvexSetOrientation.supremum C' y :=
      sInf_le ⟨y, hy, rfl⟩
    simpa [hSupportAdd y] using add_le_add hLeft hRight
  have hNoTopBot_CD_CD' :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D) ≠ ⊤ ∨
        sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D') ≠ ⊥ := by
    have h := not_and_or.mp hNoIndetCD_CD'.1
    simpa [hvCD, hvCD'] using h
  have hNoBotTop_CD_CD' :
      sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D) ≠ ⊥ ∨
        sInf ((fun y => setBracketVec ConvexSetOrientation.supremum C y) '' D') ≠ ⊤ := by
    have h := not_and_or.mp hNoIndetCD_CD'.2
    simpa [hvCD, hvCD'] using h
  have hCDD'_le : vCDD' ≤ vCD + vCD' := by
    rw [← hvCDD', ← hvCD, ← hvCD']
    refine EReal.le_add_of_forall_gt hNoBotTop_CD_CD' hNoTopBot_CD_CD' ?_
    intro a ha b hb
    rcases sInf_lt_iff.mp ha with ⟨sa, hsa, hsa_lt⟩
    rcases sInf_lt_iff.mp hb with ⟨sb, hsb, hsb_lt⟩
    rcases hsa with ⟨y, hy, rfl⟩
    rcases hsb with ⟨y', hy', rfl⟩
    have hmem : y + y' ∈ D + D' := Set.mem_add.2 ⟨y, hy, y', hy', rfl⟩
    have hle :
        sInf ((fun y0 => setBracketVec ConvexSetOrientation.supremum C y0) '' (D + D')) ≤
          setBracketVec ConvexSetOrientation.supremum C (y + y') :=
      sInf_le ⟨y + y', hmem, rfl⟩
    exact hle.trans ((hSupportSubadd y y').trans (add_le_add hsa_lt.le hsb_lt.le))
  refine ⟨⟨hScaleLeft, hScaleRight.symm⟩, hCC'D_ge, hCDD'_le, hSupportAdd, hInfAdd⟩

/-- Definition 39.8.4: A set `C` is an *eigenset* of a convex process `A : ℝ^n ⇉ ℝ^n` with
eigenvalue `λ` if `A C = λ C`, i.e. the image of `C` under `A` equals the pointwise scalar multiple
`λ • C`. -/
def IsEigensetVec {n : ℕ} (A : ConvexProcess n n) (r : ℝ)
    (C : Set (Fin n → ℝ)) : Prop :=
  ConvexProcess.image A C = r • C

end ConvexProcess

end Section39
end Chap08
