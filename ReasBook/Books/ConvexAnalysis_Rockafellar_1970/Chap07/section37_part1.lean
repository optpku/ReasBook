/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part18
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part5

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Theorem 37.1: the `inf_u sup_x*` value of the affine tilt of a saddle kernel `K`. -/
noncomputable def theorem37ValueInfSup
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) : EReal :=
  iInf fun u : Fin m → ℝ =>
    iSup fun xStar : Fin n → ℝ =>
      (((finDot u uStar + finDot x xStar : ℝ) : EReal) - K u xStar)

/-- Theorem 37.1: the `sup_x* inf_u` value of the affine tilt of a saddle kernel `K`. -/
noncomputable def theorem37ValueSupInf
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) : EReal :=
  iSup fun xStar : Fin n → ℝ =>
    iInf fun u : Fin m → ℝ =>
      (((finDot u uStar + finDot x xStar : ℝ) : EReal) - K u xStar)

/-- Helper for Proposition 37.1.2: the affine-tilted kernel whose maximin and minimax values
recover the lower and upper conjugates. -/
noncomputable def helperForProposition_37_1_2_affineTiltKernel
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar u =>
    (((finDot u uStar + finDot x xStar : ℝ) : EReal) - K u xStar)

/-- Helper for Proposition 37.1.2: the lower conjugate is the maximin value of the affine-tilted
kernel. -/
lemma helperForProposition_37_1_2_affineTiltKernel_maximin_eq
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    maximinValue (C := Fin n → ℝ) (D := Fin m → ℝ)
      (helperForProposition_37_1_2_affineTiltKernel K uStar x) =
      theorem37ValueSupInf K uStar x := by
  -- Both sides are the same `sup_x* inf_u` expression after unfolding the two definitions.
  rfl

/-- Helper for Proposition 37.1.2: the upper conjugate is the minimax value of the affine-tilted
kernel. -/
lemma helperForProposition_37_1_2_affineTiltKernel_minimax_eq
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    minimaxValue (C := Fin n → ℝ) (D := Fin m → ℝ)
      (helperForProposition_37_1_2_affineTiltKernel K uStar x) =
      theorem37ValueInfSup K uStar x := by
  -- Both sides are the same `inf_u sup_x*` expression after unfolding the two definitions.
  rfl

/-- Proposition 37.1.2: the lower conjugate never exceeds the upper conjugate. In the present
formalization these are `theorem37ValueSupInf` and `theorem37ValueInfSup`, respectively. -/
theorem lowerConjugate_le_upperConjugate
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    theorem37ValueSupInf K uStar x ≤ theorem37ValueInfSup K uStar x := by
  -- Rewrite both conjugate values as the maximin/minimax values of the same affine-tilted kernel.
  rw [← helperForProposition_37_1_2_affineTiltKernel_maximin_eq (K := K) (uStar := uStar)
      (x := x)]
  rw [← helperForProposition_37_1_2_affineTiltKernel_minimax_eq (K := K) (uStar := uStar)
      (x := x)]
  -- Lemma 36.1 gives the universal order inequality `sup inf ≤ inf sup`.
  exact maximinValue_le_minimaxValue
    (C := Fin n → ℝ) (D := Fin m → ℝ)
    (helperForProposition_37_1_2_affineTiltKernel K uStar x)
    inferInstance inferInstance

/-- Helper for Corollary 37.1.1: a closed convex bifunction is graph-convex once its
sectionwise closure is identified with the original section values. -/
lemma helperForCorollary_37_1_1_closedConvex_isGraphConvex
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F) :
    IsGraphConvexBifunction F := by
  rcases hF with ⟨hRockF, hNoBotF, hSectionClosedF⟩
  -- Convert the sectionwise fixed-point identity into the Chapter 2 closure notation used by
  -- the graph-convex upgrade lemma.
  have hClosureExactF : ∀ u x, convexFunctionClosure (F u) x = F u x := by
    intro u x
    have hSectionPoint : functionConvexClosure (F u) x = F u x := by
      exact congrArg (fun g => g x) (hSectionClosedF u).symm
    have hBridge : functionConvexClosure (F u) = convexFunctionClosure (F u) :=
      helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
        (f := F u) (hNoBot := hNoBotF u)
    simpa [hBridge] using hSectionPoint
  -- Closed convex sections upgrade Rockafellar convexity to graph convexity.
  simpa [IsGraphConvexBifunction] using
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRockF hClosureExactF hNoBotF

/-- Helper for Corollary 37.1.1: the original pairing slice is already fixed by the one-variable
convex closure operator. -/
lemma helperForCorollary_37_1_1_originalKernelSlice_functionConvexClosure_eq_self
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar =
      convexBifunctionPairing F u xStar := by
  have hClosedF := hF
  rcases hF with ⟨_, hNoBotF, _⟩
  -- First obtain the closedness of the adjoint image `y ↦ ⟪F u, y⟫`.
  have hGraphConvexF : IsGraphConvexBifunction F :=
    helperForCorollary_37_1_1_closedConvex_isGraphConvex (F := F) (hF := hClosedF)
  have hSliceClosed :
      IsFunctionConvexClosed (fun y => convexBifunctionPairing F u y) := by
    simpa [convexBifunctionAdjoint] using
      helperForLemma33_0_22_adjointImage_isFunctionConvexClosed
        (F := F) (hF_convex := hGraphConvexF) (hF_noBot := hNoBotF) u
  -- Then evaluate the fixed-point identity at the requested point.
  simpa using (congrArg (fun g => g xStar) hSliceClosed).symm

/-- Helper for Corollary 37.1.1: Theorem 34.2 identifies each fixed `xStar` slice of the
concave adjoint with the original convex pairing section. -/
lemma helperForCorollary_37_1_1_infPairing_concaveAdjointSlice_eq_originalPairing
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    infPairing u (section34ConcaveBifunctionAdjoint F xStar) =
      convexBifunctionPairing F u xStar := by
  have hPairingEqF :
      convexBifunctionClosedKernel F = section34ConcaveBifunctionAdjointPairing F :=
    (hGlobal.qualification F hF).adjointPairing_eq
  -- Evaluate Theorem 34.2 at the requested point of the saddle kernel.
  have hPoint :
      convexBifunctionClosedKernel F u xStar =
        section34ConcaveBifunctionAdjointPairing F u xStar :=
    congrArg (fun H : SaddleFunction m n => H u xStar) hPairingEqF
  -- Unfold the two pairings so the result becomes a pointwise identity of indexed infima.
  calc
    infPairing u (section34ConcaveBifunctionAdjoint F xStar)
        = section34ConcaveBifunctionAdjointPairing F u xStar := by
            simp [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing,
              bifunctionPairingNotation, conjugatePairingNotation, infPairing, sInf_range,
              finDot, dotProduct, sub_eq_add_neg, mul_comm, add_comm]
    _ = convexBifunctionClosedKernel F u xStar := hPoint.symm
    _ = convexBifunctionPairing F u xStar := by
          rfl

/-- Helper for Corollary 37.1.1: the first adjoint-inverse iterate at a fixed `x` is the
negative of the convex conjugate of the original pairing slice. -/
lemma helperForCorollary_37_1_1_firstIterateSlice_concaveConjugate_eq_neg_sliceConjugate
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    concaveConjugate
        (fun u' =>
          convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) u' x) u =
      -convexConjugate (fun y => convexBifunctionPairing F u y) x := by
  -- Rewrite the outer concave conjugate as the indexed infimum over the intermediate parameter.
  calc
    concaveConjugate
        (fun u' =>
          convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) u' x) u
        = iInf (fun u' : Fin m → ℝ =>
            (((u' ⬝ᵥ u : ℝ) : EReal) +
              -(iSup fun y : Fin n → ℝ =>
                (((y ⬝ᵥ x : ℝ) : EReal) +
                  section34ConcaveBifunctionAdjoint F y u')))) := by
            rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
            refine iInf_congr ?_
            intro u'
            -- Expand the first inverse-adjoint iterate as one convex conjugate in `y`.
            rw [convexBifunctionPairing,
              helperForTheorem33_1_convexConjugate_eq_fenchelConjugate,
              fenchelConjugate_eq_iSup]
            refine congrArg
              (fun s : EReal => (((u' ⬝ᵥ u : ℝ) : EReal) + -s)) ?_
            refine iSup_congr ?_
            intro y
            simp [bifunctionInverse, sub_eq_add_neg]
    _ = iInf (fun u' : Fin m → ℝ =>
          (((u' ⬝ᵥ u : ℝ) : EReal) +
            iInf (fun y : Fin n → ℝ =>
              -((((y ⬝ᵥ x : ℝ) : EReal) +
                section34ConcaveBifunctionAdjoint F y u'))))) := by
          refine iInf_congr ?_
          intro u'
          congr 1
          -- Convert the negated supremum in `y` into an infimum of negated summands.
          have hneg :=
            congrArg Neg.neg
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun y : Fin n → ℝ =>
                  -((((y ⬝ᵥ x : ℝ) : EReal) +
                    section34ConcaveBifunctionAdjoint F y u'))))
          simpa using hneg
    _ = iInf (fun u' : Fin m → ℝ =>
          iInf (fun y : Fin n → ℝ =>
            (((u' ⬝ᵥ u : ℝ) : EReal) +
              -((((y ⬝ᵥ x : ℝ) : EReal) +
                section34ConcaveBifunctionAdjoint F y u'))))) := by
          refine iInf_congr ?_
          intro u'
          -- Push the finite affine term through the inner infimum.
          simpa using
            (helperForTheorem_6_30_15_real_add_iInf
              (c := (u' ⬝ᵥ u : ℝ))
              (f := fun y : Fin n → ℝ =>
                -((((y ⬝ᵥ x : ℝ) : EReal) +
                  section34ConcaveBifunctionAdjoint F y u'))))
    _ = iInf (fun y : Fin n → ℝ =>
          iInf (fun u' : Fin m → ℝ =>
            (((u' ⬝ᵥ u : ℝ) : EReal) +
              -((((y ⬝ᵥ x : ℝ) : EReal) +
                section34ConcaveBifunctionAdjoint F y u'))))) := by
          -- Commute the two indexed infima so the fixed `y` slice can be simplified pointwise.
          rw [iInf_comm]
    _ = iInf (fun y : Fin n → ℝ =>
          (((-(y ⬝ᵥ x : ℝ)) : EReal) +
            infPairing u (section34ConcaveBifunctionAdjoint F y))) := by
          refine iInf_congr ?_
          intro y
          -- For fixed `y`, isolate the affine `-⟨y,x⟩` term and recognize the remaining infimum
          -- as the `infPairing` of the adjoint slice.
          calc
            iInf (fun u' : Fin m → ℝ =>
              (((u' ⬝ᵥ u : ℝ) : EReal) +
                -((((y ⬝ᵥ x : ℝ) : EReal) +
                  section34ConcaveBifunctionAdjoint F y u'))))
                = iInf (fun u' : Fin m → ℝ =>
                    (((-(y ⬝ᵥ x : ℝ)) : EReal) +
                      ((((u' ⬝ᵥ u : ℝ) : EReal) +
                        -(section34ConcaveBifunctionAdjoint F y u'))))) := by
                    refine iInf_congr ?_
                    intro u'
                    simp [EReal.neg_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            _ = (((-(y ⬝ᵥ x : ℝ)) : EReal) +
                  iInf (fun u' : Fin m → ℝ =>
                    (((u' ⬝ᵥ u : ℝ) : EReal) +
                      -(section34ConcaveBifunctionAdjoint F y u')))) := by
                  symm
                  simpa using
                    (helperForTheorem_6_30_15_real_add_iInf
                      (c := (-(y ⬝ᵥ x : ℝ)))
                      (f := fun u' : Fin m → ℝ =>
                        (((u' ⬝ᵥ u : ℝ) : EReal) +
                          -(section34ConcaveBifunctionAdjoint F y u'))))
            _ = (((-(y ⬝ᵥ x : ℝ)) : EReal) +
                  concaveConjugate (section34ConcaveBifunctionAdjoint F y) u) := by
                  rw [← helperForTheorem_6_30_4_concaveConjugate_eq_iInf
                    (g := section34ConcaveBifunctionAdjoint F y) u]
            _ = (((-(y ⬝ᵥ x : ℝ)) : EReal) +
                  infPairing u (section34ConcaveBifunctionAdjoint F y)) := by
                  rw [← helperForProposition_36_4_6_infPairing_eq_concaveConjugate
                    (uStar := u) (g := section34ConcaveBifunctionAdjoint F y)]
    _ = iInf (fun y : Fin n → ℝ =>
          (((-(y ⬝ᵥ x : ℝ)) : EReal) + convexBifunctionPairing F u y)) := by
          refine iInf_congr ?_
          intro y
          -- Collapse the recovered adjoint slice back to the original convex pairing.
          rw [helperForCorollary_37_1_1_infPairing_concaveAdjointSlice_eq_originalPairing
            (F := F) (hF := hF) hGlobal (u := u) (xStar := y)]
    _ = -convexConjugate (fun y => convexBifunctionPairing F u y) x := by
          -- Repackage the fixed-`y` infimum as the negative of the usual convex-conjugate
          -- supremum of the original section.
          rw [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate, fenchelConjugate_eq_iSup]
          simpa [sub_eq_add_neg, EReal.neg_add, add_assoc, add_left_comm, add_comm] using
            (helperForLemma33_0_5_neg_iSup_neg_eq_iInf
              (f := fun y : Fin n → ℝ =>
                -((((y ⬝ᵥ x : ℝ) : EReal) - convexBifunctionPairing F u y)))).symm

/-- Helper for Corollary 37.1.1: unfolding the double adjoint-inverse slice produces the ordinary
slice biconjugate of the original pairing section. -/
lemma helperForCorollary_37_1_1_doubleAdjointInverseSlice_eq_negConcaveConjugateConjugate
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexBifunctionPairing
        (bifunctionInverse
          (section34ConcaveBifunctionAdjoint
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))) u xStar =
      convexConjugate (convexConjugate (fun y => convexBifunctionPairing F u y)) xStar := by
  -- Unfold the outer convex pairing so the goal becomes equality of two `iSup` formulas indexed
  -- by the intermediate point `x`.
  rw [convexBifunctionPairing, helperForTheorem33_1_convexConjugate_eq_fenchelConjugate,
    fenchelConjugate_eq_iSup]
  -- Each summand is the first adjoint-inverse iterate at `x`, which simplifies definitionally to
  -- the inner convex conjugate of the original slice `y ↦ ⟪F u, y⟫`.
  refine iSup_congr ?_
  intro x
  rw [bifunctionInverse, section34ConcaveBifunctionAdjoint,
    helperForCorollary_37_1_1_firstIterateSlice_concaveConjugate_eq_neg_sliceConjugate
      (F := F) (hF := hF) hGlobal (u := u) (x := x)]
  -- The isolated first-iterate identity removes the nested concave conjugate and leaves the
  -- plain biconjugate summand.
  simp [convexBifunctionPairing, fenchelConjugate_eq_iSup]

/-- Helper for Corollary 37.1.1: the biconjugate of the original pairing slice agrees with its
one-variable convex closure. -/
lemma helperForCorollary_37_1_1_originalKernelSlice_biconjugate_eq_functionConvexClosure
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexConjugate (convexConjugate (fun y => convexBifunctionPairing F u y)) xStar =
      functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
  rcases hF with ⟨_, _, _⟩
  by_cases hAllTop : ∀ y : Fin n → ℝ, F u y = ⊤
  · have hPairBot : convexBifunctionPairing F u = fun _ : Fin n → ℝ => (⊥ : EReal) := by
      -- If the whole primal section is `⊤`, its first conjugate is the constant `⊥` section.
      funext y
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      apply le_antisymm
      · refine iSup_le ?_
        intro z
        simp [hAllTop]
      · exact bot_le
    have hConstBotLsc : LowerSemicontinuous (fun _ : Fin n → ℝ => (⊥ : EReal)) :=
      closed_improper_const_bot.1.2
    have hLeft :
        convexConjugate (convexConjugate (fun y => convexBifunctionPairing F u y)) xStar =
          (⊥ : EReal) := by
      -- Conjugating the constant `⊥` section again leaves the value `⊥`.
      rw [hPairBot]
      simp [convexConjugate, fenchelConjugate_eq_iSup]
    have hConstBotClosure :
        functionConvexClosure (fun _ : Fin n → ℝ => (⊥ : EReal)) xStar = (⊥ : EReal) := by
      -- The raw convex closure fixes the constant `⊥` section because it is lower semicontinuous.
      simpa using congrArg (fun g => g xStar)
        (helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
          (f := fun _ : Fin n → ℝ => (⊥ : EReal)) hConstBotLsc).symm
    have hRight :
        functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar = (⊥ : EReal) := by
      -- Replace the original slice by the constant `⊥` section established above.
      simpa [hPairBot] using hConstBotClosure
    exact hLeft.trans hRight.symm
  · rcases not_forall.mp hAllTop with ⟨y₀, hy₀⟩
    -- A single point with finite primal value lets Fenchel-Moreau identify the slice
    -- biconjugate with its convex closure.
    exact
      helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
        (f := fun y => convexBifunctionPairing F u y)
        (hConv := helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
          (f := F u) (x₀ := y₀) hy₀)
        (hNoBot := helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := F u) (x₀ := y₀) hy₀)
        xStar

/-- Helper for Corollary 37.1.1: the upper recovery kernel obtained from `F_*` should coincide
with the convex closure of the original slice `y ↦ ⟪F u, y⟫`.

This is the remaining Lean blocker inside Theorem 37.1: after unfolding, the left-hand side is a
nested `convexConjugate`/`concaveConjugate` expression for the double adjoint-inverse transform,
while the right-hand side is the one-variable convex closure of the original slice. The intended
route is to identify that nested transform with the Fenchel biconjugate of the slice and then
invoke `helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex`. -/
lemma helperForCorollary_37_1_1_upperRecoveredKernel_eq_functionConvexClosure
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexBifunctionPairing
        (bifunctionInverse
          (section34ConcaveBifunctionAdjoint
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))) u xStar =
      functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
  -- First unfold the nested Section 34 transform to a one-variable mixed conjugate expression.
  calc
    convexBifunctionPairing
        (bifunctionInverse
          (section34ConcaveBifunctionAdjoint
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))) u xStar
        = convexConjugate (convexConjugate (fun y => convexBifunctionPairing F u y)) xStar := by
            simpa using
              helperForCorollary_37_1_1_doubleAdjointInverseSlice_eq_negConcaveConjugateConjugate
                (F := F) (hF := hF) hGlobal (u := u) (xStar := xStar)
    _ = functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
          -- Identify the slice biconjugate with its convex closure sectionwise.
          exact
            helperForCorollary_37_1_1_originalKernelSlice_biconjugate_eq_functionConvexClosure
              (F := F) (hF := hF) (u := u) (xStar := xStar)

/-- Theorem 37.1: let `F` be a closed convex bifunction, let `K ∈ Ω(F)`, and let
`KStar ∈ Ω(F_*)`. Then the two affine-tilt minimax values attached to `K` recover the inverse
pairing of `F` and the inverse-adjoint pairing of `F`, while the corresponding values attached to
`KStar` recover the original pairings of `F`. -/
theorem section37_theorem37_1
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (KStar : SaddleFunction m n)
    (hFStar : IsClosedConvexBifunction
      (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hKStar : KStar ∈ EquivalenceClassGeneratedByConvexBifunction
      ⟨bifunctionInverse (section34ConcaveBifunctionAdjoint F), hFStar⟩)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    (∀ uStar x,
      theorem37ValueInfSup K uStar x = infPairing uStar (bifunctionInverse F x)) ∧
      (∀ uStar x,
        theorem37ValueSupInf K uStar x =
          convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) uStar x) ∧
      (∀ u xStar,
        theorem37ValueInfSup KStar u xStar = convexBifunctionPairing F u xStar) ∧
      ∀ u xStar,
        theorem37ValueSupInf KStar u xStar = convexBifunctionPairing F u xStar := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hPairingEqF :
      convexBifunctionClosedKernel F = section34ConcaveBifunctionAdjointPairing F :=
    (hGlobal.qualification F hF).adjointPairing_eq
  -- First package the lower-conjugate recovery route for any representative of `Ω(G)`.
  have hInfSupOfGeneratedClass :
      ∀ {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
        (hG : IsClosedConvexBifunction G)
        {L : SaddleFunction m n}
        (hL : L ∈ EquivalenceClassGeneratedByConvexBifunction ⟨G, hG⟩),
        ∀ uStar x,
          theorem37ValueInfSup L uStar x = infPairing uStar (bifunctionInverse G x) := by
    intro G hG L hL uStar x
    have hSection34G := section34_theorem34_2 G hG
    have hLOmega : L ∈ omegaClassOfConvexBifunction G := by
      -- Theorem 34.2 identifies the generated class with the `Ω(G)` class.
      rw [hSection34G.1]
      exact hL
    rcases
        (section34_theorem34_2_qualified G hG (hGlobal.qualification G hG)).2.2.2.2
          L hLOmega with
      ⟨_, _, _, hRecoverConv, _, _⟩
    -- Rewrite the inner supremum as the convex conjugate section recovered by Theorem 34.2.
    calc
      theorem37ValueInfSup L uStar x
          = iInf (fun u : Fin m → ℝ =>
              ((finDot u uStar : ℝ) : EReal) +
                iSup (fun xStar : Fin n → ℝ =>
                  (((finDot x xStar : ℝ) : EReal) + (-L u xStar)))) := by
              unfold theorem37ValueInfSup
              congr 1
              funext u
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (helperForTheorem_6_30_15_real_add_iSup (c := finDot u uStar)
                  (f := fun xStar : Fin n → ℝ =>
                    (((finDot x xStar : ℝ) : EReal) + (-L u xStar)))).symm
      _ = iInf (fun u : Fin m → ℝ => ((finDot u uStar : ℝ) : EReal) + G u x) := by
            congr 1
            funext u
            rw [hRecoverConv u x]
            rw [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate]
            rw [fenchelConjugate_eq_iSup]
            simp [finDot, dotProduct, sub_eq_add_neg, mul_comm, add_comm]
      _ = infPairing uStar (bifunctionInverse G x) := by
            simp [infPairing, bifunctionInverse, finDot, dotProduct_comm, add_comm]
  -- Next package the upper-conjugate recovery route for any representative of `Ω(G)`.
  have hSupInfOfGeneratedClass :
      ∀ {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
        (hG : IsClosedConvexBifunction G)
        {L : SaddleFunction m n}
        (hL : L ∈ EquivalenceClassGeneratedByConvexBifunction ⟨G, hG⟩),
        ∀ uStar x,
          theorem37ValueSupInf L uStar x =
            convexBifunctionPairing
              (bifunctionInverse (section34ConcaveBifunctionAdjoint G)) uStar x := by
    intro G hG L hL uStar x
    have hSection34G := section34_theorem34_2 G hG
    have hLOmega : L ∈ omegaClassOfConvexBifunction G := by
      -- Theorem 34.2 again converts the generated-class hypothesis into `Ω(G)` membership.
      rw [hSection34G.1]
      exact hL
    rcases
        (section34_theorem34_2_qualified G hG (hGlobal.qualification G hG)).2.2.2.2
          L hLOmega with
      ⟨_, _, _, _, hRecoverConc, _⟩
    -- Rewrite the inner infimum as the concave conjugate section recovered by Theorem 34.2.
    calc
      theorem37ValueSupInf L uStar x
          = iSup (fun xStar : Fin n → ℝ =>
              ((finDot x xStar : ℝ) : EReal) +
                iInf (fun u : Fin m → ℝ =>
                  ((finDot u uStar : ℝ) : EReal) + (-L u xStar))) := by
              unfold theorem37ValueSupInf
              congr 1
              funext xStar
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (helperForTheorem_6_30_15_real_add_iInf (c := finDot x xStar)
                  (f := fun u : Fin m → ℝ =>
                    (((finDot u uStar : ℝ) : EReal) + (-L u xStar)))).symm
      _ = iSup (fun xStar : Fin n → ℝ =>
            ((finDot x xStar : ℝ) : EReal) +
              section34ConcaveBifunctionAdjoint G xStar uStar) := by
            congr 1
            funext xStar
            rw [hRecoverConc xStar uStar]
            rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
            simp [finDot, dotProduct, mul_comm, add_comm]
      _ = convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint G)) uStar x := by
            simp [convexBifunctionPairing, fenchelConjugate_eq_iSup, bifunctionInverse, finDot,
              dotProduct, sub_eq_add_neg, mul_comm, add_comm]
  have hInfPairingAdjointEqKernel :
      ∀ u xStar,
        infPairing u (section34ConcaveBifunctionAdjoint F xStar) =
          convexBifunctionPairing F u xStar := by
    intro u xStar
    -- Theorem 34.2 identifies the original kernel with the concave-adjoint pairing.
    have hPoint :
        convexBifunctionClosedKernel F u xStar =
          section34ConcaveBifunctionAdjointPairing F u xStar :=
      congrArg (fun H : SaddleFunction m n => H u xStar) hPairingEqF
    calc
      infPairing u (section34ConcaveBifunctionAdjoint F xStar)
          = section34ConcaveBifunctionAdjointPairing F u xStar := by
              simp [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing,
                bifunctionPairingNotation, conjugatePairingNotation, infPairing, sInf_range,
                finDot, dotProduct, sub_eq_add_neg, mul_comm, add_comm]
      _ = convexBifunctionClosedKernel F u xStar := hPoint.symm
      _ = convexBifunctionPairing F u xStar := by rfl
  constructor
  · intro uStar x
    -- Apply the generic `Ω(F)` lower-conjugate recovery.
    exact hInfSupOfGeneratedClass hF hK uStar x
  constructor
  · intro uStar x
    -- Apply the generic `Ω(F)` upper-conjugate recovery.
    exact hSupInfOfGeneratedClass hF hK uStar x
  constructor
  · intro u xStar
    -- Apply the same lower-conjugate recovery to `KStar ∈ Ω(F_*)`, then collapse the
    -- doubled inverse to the original kernel via Theorem 34.2.
    calc
      theorem37ValueInfSup KStar u xStar = infPairing u (bifunctionInverse FStar xStar) :=
        hInfSupOfGeneratedClass hFStar hKStar u xStar
      _ = infPairing u (section34ConcaveBifunctionAdjoint F xStar) := by
            change infPairing u (fun uStar => -FStar uStar xStar) =
              infPairing u (section34ConcaveBifunctionAdjoint F xStar)
            simp [FStar, bifunctionInverse]
      _ = convexBifunctionPairing F u xStar := hInfPairingAdjointEqKernel u xStar
  · intro u xStar
    have hUpperRecoveredKernelAsClosure :
        convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint FStar)) u xStar =
          functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
      -- Route correction: isolate the nested adjoint-inverse computation in a dedicated helper.
      simpa [FStar] using
        helperForCorollary_37_1_1_upperRecoveredKernel_eq_functionConvexClosure
          (F := F) hF hGlobal u xStar
    have hClosureCollapsed :
        functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar =
          convexBifunctionPairing F u xStar := by
      -- The original slice is already convex-closed, so its closure collapses immediately.
      exact
        helperForCorollary_37_1_1_originalKernelSlice_functionConvexClosure_eq_self
          (F := F) hF u xStar
    -- Combine the generic `Ω(F_*)` upper-conjugate recovery with the sectionwise closure
    -- identification and the closedness of the recovered original slice.
    calc
      theorem37ValueSupInf KStar u xStar =
          convexBifunctionPairing
            (bifunctionInverse (section34ConcaveBifunctionAdjoint FStar)) u xStar :=
        hSupInfOfGeneratedClass hFStar hKStar u xStar
      _ = functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar :=
        hUpperRecoveredKernelAsClosure
      _ = convexBifunctionPairing F u xStar := hClosureCollapsed

/-- Helper for Corollary 37.1.2: a closed proper saddle-function admits a proper closed convex
representative in the Section 34 generated class. -/
lemma helperForCorollary_37_1_2_closedProperRepresentative
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      ∃ hF : IsClosedConvexBifunction F,
        IsProperConvexBifunction F ∧
          K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩ := by
  -- Extract the concave-convex orientation already bundled into closedness.
  have hKcc : IsConcaveConvex K := hKclosed.1.1
  let Ω : Set (SaddleFunction m n) := {L | saddleEquivalent L K}
  have hΩclosedClass : IsClosedConcaveConvexEquivalenceClass Ω := by
    refine ⟨K, hKcc, hKclosed, ?_⟩
    rfl
  have hOmegaExistsUnique :
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsClosedConvexBifunction F ∧ Ω = omegaClassOfConvexBifunction F := by
    exact hGlobal.uniqueRealization Ω hΩclosedClass
  rcases hOmegaExistsUnique with ⟨F, hFOmega, -⟩
  rcases hFOmega with ⟨hF, hOmegaEq⟩
  have hSection34F := section34_theorem34_2 F hF
  have hKSelfEquiv : saddleEquivalent K K := by
    exact ⟨hKcc, hKcc, rfl, rfl⟩
  have hKInOmega : K ∈ omegaClassOfConvexBifunction F := by
    have hKInClass : K ∈ Ω := by
      simpa [Ω] using hKSelfEquiv
    simpa [hOmegaEq] using hKInClass
  have hKEquivKernel : saddleEquivalent K (convexBifunctionPairing F) := by
    rw [hSection34F.2.1] at hKInOmega
    simpa [convexBifunctionClosedKernel] using hKInOmega
  have hKGenerated :
      K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩ := by
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hKEquivKernel
  have hPairingProper :
      IsProperSaddleFunction (convexBifunctionPairing F) := by
    -- Closed equivalent saddle-functions have the same saddle effective domain.
    have hSameDomain :
        saddleEffectiveDomain (convexBifunctionPairing F) = saddleEffectiveDomain K :=
      (closed_equivalent_saddle_functions_have_same_domain_and_agree_on_relativeInterior
        (K := K) (L := convexBifunctionPairing F) hKclosed hKEquivKernel hGlobal).1
    simpa [IsProperSaddleFunction, hSameDomain] using hKproper
  have hPairingDomainNonempty :
      (saddleEffectiveDomain (convexBifunctionPairing F)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hPairingProper
  rcases hPairingDomainNonempty with ⟨⟨u₀, xStar₀⟩, hu₀xStar₀⟩
  have hu₀ : u₀ ∈ effectiveDomain₁ (convexBifunctionPairing F) :=
    (Set.mem_prod.mp hu₀xStar₀).1
  have hFiniteSection : ∃ x : Fin n → ℝ, F u₀ x < (⊤ : EReal) := by
    by_contra hNoFiniteSection
    have hAllTop : ∀ x : Fin n → ℝ, F u₀ x = (⊤ : EReal) := by
      intro x
      by_contra hxTop
      have hxFinite : F u₀ x < (⊤ : EReal) := by
        simpa [lt_top_iff_ne_top] using hxTop
      exact hNoFiniteSection ⟨x, hxFinite⟩
    have hPairingBot :
        convexBifunctionPairing F u₀ = fun _ : Fin n → ℝ => (⊥ : EReal) := by
      -- If the whole primal section is `⊤`, its conjugate pairing is constantly `⊥`.
      funext y
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      apply le_antisymm
      · refine iSup_le ?_
        intro z
        simp [hAllTop]
      · exact bot_le
    have hu₀zero : (⊥ : EReal) < convexBifunctionPairing F u₀ (0 : Fin n → ℝ) := by
      simpa using hu₀ (0 : Fin n → ℝ)
    rw [hPairingBot] at hu₀zero
    exact (lt_irrefl (⊥ : EReal)) hu₀zero
  have hFproper : IsProperConvexBifunction F := by
    -- `hF` already supplies the no-`⊥` convention; the nonempty saddle domain above gives one
    -- finite section value.
    rcases hF with ⟨hRockF, hNoBotF, hClosedSectionsF⟩
    refine ⟨hNoBotF, ?_⟩
    rcases hFiniteSection with ⟨x₀, hx₀⟩
    exact ⟨u₀, x₀, hx₀⟩
  exact ⟨F, hF, hFproper, hKGenerated⟩

/-- Helper for Corollary 37.1.2: once the dual bifunction `F_*` is known to be closed convex,
Theorem 37.1 rewrites the lower conjugate of `K` as the canonical dual pairing. -/
lemma helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hFStar :
      IsClosedConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∀ uStar x,
      theorem37ValueSupInf K uStar x =
        convexBifunctionPairing
          (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) uStar x := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hSection34FStar := section34_theorem34_2 FStar hFStar
  have hKStar :
      convexBifunctionClosedKernel FStar ∈
        EquivalenceClassGeneratedByConvexBifunction ⟨FStar, hFStar⟩ := by
    -- The canonical kernel of `F_*` is itself a member of the generated equivalence class.
    have hOmega :
        convexBifunctionClosedKernel FStar ∈ omegaClassOfConvexBifunction FStar :=
      hSection34FStar.2.2
    have hEqClass :
        omegaClassOfConvexBifunction FStar =
          {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} :=
      hSection34FStar.2.1
    have hEquivKernel :
        convexBifunctionClosedKernel FStar ∈
          {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} := by
      rw [← hEqClass]
      exact hOmega
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hEquivKernel
  have hSection37 :=
      section37_theorem37_1 F hF K hK (convexBifunctionClosedKernel FStar) hFStar hKStar hGlobal
  -- The second component of Theorem 37.1 is exactly the desired lower-conjugate formula.
  exact hSection37.2.1

/-- Helper for Corollary 37.1.2: the explicit dual inverse `F_*` is already proper on the convex
side once the original representative `F` is closed proper convex. -/
lemma helperForCorollary_37_1_2_dualAdjointInverse_isProperConvex
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hFproper : IsProperConvexBifunction F) :
    IsProperConvexBifunction (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) := by
  have hAdjointProper :
      IsProperConcaveBifunction (section34ConcaveBifunctionAdjoint F) :=
    (closed_convex_bifunction_proper_implies_adjoint_proper F hF hFproper).1
  have hAdjointHypographProper :
      IsHypographProperConcaveBifunction (section34ConcaveBifunctionAdjoint F) := by
    rcases hAdjointProper with ⟨hNoTop, hNonempty⟩
    rcases hNonempty with ⟨x, hx⟩
    rcases hx with ⟨uStar, huStar⟩
    exact ⟨⟨x, uStar, huStar⟩, hNoTop⟩
  have hInverseProper :
      IsEpigraphProperConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) :=
    (bifunctionInverse_convex_concave_closed_proper_involutive
      (section34ConcaveBifunctionAdjoint F)).2.2.2.2.2.1 hAdjointHypographProper
  rcases hInverseProper with ⟨⟨x, uStar, hFinite⟩, hNoBot⟩
  -- The Section 36 inverse-properness theorem already gives both no-`⊥` values and one
  -- finite witness for the dual inverse.
  exact ⟨hNoBot, ⟨x, uStar, hFinite⟩⟩

end Section37
end Chap07
