/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part6

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart7 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}


/-- Helper for Text 34.1.4: the proposed left closed-ball bridge is already false for the
one-dimensional coordinate kernel. -/


lemma helperForText_34_1_4_leftClosedBallEnvelope_bridge_false :
    ¬ ((⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
          ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
            ⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
              ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
                helperForText_34_1_4_coordKernel w.1 z.1)
        ≤
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨆ (yStar : {yStar : Fin 1 → ℝ // ‖yStar‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_coordKernel
              helperForText_34_1_4_coordKernel_isConcaveConvex
              0 ((0 : Fin 1 → ℝ) + yStar.1))) := by
  have hRightZero :
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨆ (yStar : {yStar : Fin 1 → ℝ // ‖yStar‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_coordKernel
              helperForText_34_1_4_coordKernel_isConcaveConvex
              0 ((0 : Fin 1 → ℝ) + yStar.1)) = 0 := by
    have hInfZero :
        (⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨆ (yStar : {yStar : Fin 1 → ℝ // ‖yStar‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_coordKernel
              helperForText_34_1_4_coordKernel_isConcaveConvex
              0 ((0 : Fin 1 → ℝ) + yStar.1)) = (0 : EReal) := by
      apply le_antisymm
      · refine iInf_le_of_le ⟨(1 / 2 : ℝ), by norm_num⟩ ?_
        refine iSup_le ?_
        intro yStar
        rw [helperForText_34_1_4_coordKernel_lowerClosure_at_origin]
        simp
      · refine le_iInf ?_
        intro ρ
        refine le_iSup_of_le ⟨(0 : Fin 1 → ℝ), by simpa using le_of_lt ρ.2.1⟩ ?_
        rw [helperForText_34_1_4_coordKernel_lowerClosure_at_origin]
        simp
    calc
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨆ (yStar : {yStar : Fin 1 → ℝ // ‖yStar‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_coordKernel
              helperForText_34_1_4_coordKernel_isConcaveConvex
              0 ((0 : Fin 1 → ℝ) + yStar.1))
          = -(0 : EReal) := by rw [hInfZero]
      _ = 0 := by simp
  have hLeftHalf :
      (((1 / 2 : ℝ)) : EReal) ≤
        (⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
          ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
            ⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
              ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
                helperForText_34_1_4_coordKernel w.1 z.1) := by
    refine le_iInf ?_
    intro ρz
    refine le_iInf ?_
    intro z
    refine le_iSup_of_le ⟨(3 / 4 : ℝ), by norm_num⟩ ?_
    refine le_iSup_of_le ⟨(fun _ => (1 / 2 : ℝ)), ?_⟩ ?_
    · simpa [Pi.norm_def, Real.norm_eq_abs] using
        (show |(1 / 2 : ℝ)| ≤ (3 / 4 : ℝ) by norm_num)
    · simp [helperForText_34_1_4_coordKernel]
  intro hBridge
  have : (((1 / 2 : ℝ)) : EReal) ≤ (0 : EReal) := by
    calc
      (((1 / 2 : ℝ)) : EReal) ≤
          (⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
            ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
              ⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
                ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
                  helperForText_34_1_4_coordKernel w.1 z.1) := hLeftHalf
      _ ≤
          -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
              ⨆ (yStar : {yStar : Fin 1 → ℝ // ‖yStar‖ ≤ ρ.1}),
                -lowerClosureConcaveConvex
                  helperForText_34_1_4_coordKernel
                  helperForText_34_1_4_coordKernel_isConcaveConvex
                  0 ((0 : Fin 1 → ℝ) + yStar.1)) := hBridge
      _ = 0 := hRightZero
  norm_num at this

/-- Helper for Text 34.1.4: the proposed right closed-ball bridge is already false for the
one-dimensional second-coordinate kernel. -/
lemma helperForText_34_1_4_rightClosedBallEnvelope_bridge_false :
    ¬ (-(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
            ⨅ (v : {v : Fin 1 → ℝ // ‖v‖ ≤ ρ.1}),
              -lowerClosureConcaveConvex
                helperForText_34_1_4_secondCoordKernel
                helperForText_34_1_4_secondCoordKernel_isConcaveConvex
                ((0 : Fin 1 → ℝ) + v.1) 0)
          ≤
        (⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
          ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
            ⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
              ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
                helperForText_34_1_4_secondCoordKernel w.1 z.1)) := by
  have hLeftZero :
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨅ (v : {v : Fin 1 → ℝ // ‖v‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_secondCoordKernel
              helperForText_34_1_4_secondCoordKernel_isConcaveConvex
              ((0 : Fin 1 → ℝ) + v.1) 0) = 0 := by
    have hSupZero :
        (⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨅ (v : {v : Fin 1 → ℝ // ‖v‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_secondCoordKernel
              helperForText_34_1_4_secondCoordKernel_isConcaveConvex
              ((0 : Fin 1 → ℝ) + v.1) 0) = 0 := by
      apply le_antisymm
      · refine iSup_le ?_
        intro ρ
        refine iInf_le_of_le ⟨(0 : Fin 1 → ℝ), by simpa using le_of_lt ρ.2.1⟩ ?_
        rw [helperForText_34_1_4_secondCoordKernel_lowerClosure_at_origin]
        simp
      · refine le_iSup_of_le ⟨(1 / 2 : ℝ), by norm_num⟩ ?_
        refine le_iInf ?_
        intro v
        rw [helperForText_34_1_4_secondCoordKernel_lowerClosure_at_origin]
        simp
    calc
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
          ⨅ (v : {v : Fin 1 → ℝ // ‖v‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex
              helperForText_34_1_4_secondCoordKernel
              helperForText_34_1_4_secondCoordKernel_isConcaveConvex
              ((0 : Fin 1 → ℝ) + v.1) 0)
          = -(0 : EReal) := by rw [hSupZero]
      _ = 0 := by simp
  have hRightNegHalf :
      (⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
        ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
          ⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
            ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
              helperForText_34_1_4_secondCoordKernel w.1 z.1)
        ≤ (((-1 / 2 : ℝ)) : EReal) := by
    refine iSup_le ?_
    intro ρw
    refine iSup_le ?_
    intro w
    refine iInf_le_of_le ⟨(3 / 4 : ℝ), by norm_num⟩ ?_
    refine iInf_le_of_le ⟨(fun _ => (-1 / 2 : ℝ)), ?_⟩ ?_
    · simpa [Pi.norm_def, Real.norm_eq_abs] using
        (show (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) by norm_num)
    · simp [helperForText_34_1_4_secondCoordKernel]
  intro hBridge
  have : (0 : EReal) ≤ (((-1 / 2 : ℝ)) : EReal) := by
    calc
      (0 : EReal) =
          -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < (1 : ℝ)}),
              ⨅ (v : {v : Fin 1 → ℝ // ‖v‖ ≤ ρ.1}),
                -lowerClosureConcaveConvex
                  helperForText_34_1_4_secondCoordKernel
                  helperForText_34_1_4_secondCoordKernel_isConcaveConvex
                  ((0 : Fin 1 → ℝ) + v.1) 0) := hLeftZero.symm
      _ ≤
          (⨆ (ρw : {ρ : ℝ // ρ < (1 : ℝ)}),
            ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ ≤ ρw.1}),
              ⨅ (ρz : {ρ : ℝ // ρ < (1 : ℝ)}),
                ⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ ≤ ρz.1}),
                  helperForText_34_1_4_secondCoordKernel w.1 z.1) := hBridge
      _ ≤ (((-1 / 2 : ℝ)) : EReal) := hRightNegHalf
  norm_num at this

/-- Helper for Text 34.1.4: the translated-tilted package already squeezes the base
lower-closure value between the two shifted closed-ball envelopes that come directly from the
Chapter 6 `liminf`/`limsup` identities.

This packages the exact dependency-closed information available before any transport back to the
raw fixed-ball envelopes of `K`. -/
lemma helperForText_34_1_4_lowerClosure_between_shiftedRestrictedClosedBallEnvelopes
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    (-(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
      ≤
      lowerClosureConcaveConvex K h u xStar) ∧
      (lowerClosureConcaveConvex K h u xStar
        ≤
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex K h (u + v.1) xStar)) := by
  constructor
  · -- The left inequality is the shifted-dual envelope bound proved just above.
    exact
      helperForText_34_1_4_negRestrictedDualClosedBallEnvelope_le_lowerClosure
        (K := K) (h := h) (F := F) (hLowerRep := hLowerRep)
        (hGenuineSelfRep := hGenuineSelfRep) (u := u) (xStar := xStar) (δ := δ)
        (hGClosed := hGClosed) (hEqualValues := hEqualValues)
  · -- The right inequality is the matching shifted-primal envelope bound.
    exact
      helperForText_34_1_4_lowerClosure_le_negRestrictedPrimalClosedBallEnvelope
        (K := K) (h := h) (F := F) (hLowerRep := hLowerRep)
        (hGenuineSelfRep := hGenuineSelfRep) (u := u) (xStar := xStar) (ε := ε)
        (hGClosed := hGClosed) (hEqualValues := hEqualValues)

/-- Helper for Text 34.1.4: every translated-and-tilted program attached to a closed-convex
witness for `underline(K)` is itself a closed convex bifunction.

This isolates the Chapter 6 packaging needed by the remaining transport argument: once a fixed
witness represents `underline(K)`, the translated objective `(v, y) ↦ F (u + v) y - ⟪y, xStar⟫`
inherits closed convexity from the original witness. -/
lemma helperForText_34_1_4_translatedTiltedBifunction_isClosedConvex_of_lowerRepresentation
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hFiniteSections : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x < (⊤ : EReal))
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    ClosedConvexBifunction (translatedTiltedBifunction F u xStar) := by
  have hGraphConvex : IsGraphConvexBifunction F :=
    -- First expose the witness as a graph-convex bifunction so the translated Chapter 6
    -- closedness theorem can be applied.
    helperForText_34_1_4_graphConvex_of_closedConvexBifunction hRock hNoBot hClosed
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    -- Closed convexity of the witness already packages graph-function closedness.
    helperForText_34_1_4_graphFunction_isFunctionConvexClosed_of_closedConvexBifunction hClosed
  have hLowerNoBot :
      HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) :=
    -- The represented mixed lower closure never attains `⊥`, so no witness section can be
    -- identically `⊤`.
    helperForText_34_1_4_lowerClosure_hasNoBot_of_closedConvexLowerRepresentation
      (K := K) (h := h) hRock hNoBot hClosed hLowerRep
        hFiniteSections
  have hNotTop :
      ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ (⊤ : EReal) :=
    helperForText_34_1_4_witness_sections_notTop_of_lowerRepresentation
      (K := K) (h := h) hLowerNoBot hLowerRep
  -- With graph convexity, graph closedness, and the nontriviality of each parameter section in
  -- place, the translated Chapter 6 program is closed convex.
  simpa [translatedTiltedBifunction] using
    helperForLemma33_0_22_translatedTiltedBifunction_isClosedConvex
      hGraphConvex hGraphClosed hNoBot hNotTop u xStar

/-- Helper for Text 34.1.4: for a fixed second-variable point, the closed-ball supremum envelope
around `u` is unchanged when the radius index is restricted to positive values below `ε`.

Nonpositive radii contribute only the center point `u` (or the empty ball), and every positive
closed ball still contains that same center. -/
lemma helperForText_34_1_4_iSup_closedBallValues_eq_iSup_positiveRadii
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (z : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) :
    (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z)
      =
    (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z) := by
  apply le_antisymm
  · -- A nonpositive radius contributes no more than the center value, which already appears in
    -- every positive-radius ball.
    refine iSup_le ?_
    intro ρw
    by_cases hPos : 0 < ρw.1
    · exact le_iSup_of_le ⟨ρw.1, hPos, ρw.2⟩ le_rfl
    · have hNonpos : ρw.1 ≤ 0 := le_of_not_gt hPos
      have hCenter :
          (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z)
            ≤
          K u z := by
        refine iSup_le ?_
        intro w
        have hw_eq_u : w.1 = u := by
          have hNormEq :
              ‖w.1 - u‖ = 0 := le_antisymm (le_trans w.2 hNonpos) (norm_nonneg _)
          exact sub_eq_zero.mp (norm_eq_zero.mp hNormEq)
        simpa [hw_eq_u]
      have hCenterLePositive :
          K u z
            ≤
          (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z) := by
        have hHalfPos : 0 < ε.1 / 2 := by
          linarith [ε.2]
        have hHalfLt : ε.1 / 2 < ε.1 := by
          linarith [ε.2]
        refine le_iSup_of_le ⟨ε.1 / 2, hHalfPos, hHalfLt⟩ ?_
        refine le_iSup_of_le ⟨u, ?_⟩ ?_
        · simpa using (show (0 : ℝ) ≤ ε.1 / 2 by linarith [ε.2])
        · rfl
      exact le_trans hCenter hCenterLePositive
  · -- The positive-radius family is a subfamily of the unrestricted one.
    refine iSup_le ?_
    intro ρw
    exact le_iSup_of_le ⟨ρw.1, ρw.2.2⟩ le_rfl

/-- Helper for Text 34.1.4: for a fixed first-variable point, the closed-ball infimum envelope
around `xStar` is unchanged when the radius index is restricted to positive values below `δ`.

As on the primal side, nonpositive radii contribute only the base point `xStar` or the empty
ball, both of which are already controlled by the positive-radius family. -/
lemma helperForText_34_1_4_iInf_closedBallValues_eq_iInf_positiveRadii
    (K : SaddleFunction m n)
    (w : Fin m → ℝ) (xStar : Fin n → ℝ)
    (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1)
      =
    (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1) := by
  apply le_antisymm
  · -- The unrestricted infimum is taken over a larger radius family.
    refine le_iInf ?_
    intro ρz
    exact iInf_le_of_le ⟨ρz.1, ρz.2.2⟩ le_rfl
  · -- For nonpositive radii, every admissible point is forced to be `xStar`, and every
    -- positive-radius ball still contains that base point.
    refine le_iInf ?_
    intro ρz
    by_cases hPos : 0 < ρz.1
    · exact iInf_le_of_le ⟨ρz.1, hPos, ρz.2⟩ le_rfl
    · have hNonpos : ρz.1 ≤ 0 := le_of_not_gt hPos
      refine le_iInf ?_
      intro z
      have hz_eq_xStar : z.1 = xStar := by
        have hNormEq :
            ‖z.1 - xStar‖ = 0 := le_antisymm (le_trans z.2 hNonpos) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp hNormEq)
      have hPositiveLeBase :
          (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1)
            ≤
          K w xStar := by
        have hHalfPos : 0 < δ.1 / 2 := by
          linarith [δ.2]
        have hHalfLt : δ.1 / 2 < δ.1 := by
          linarith [δ.2]
        calc
          (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1)
              ≤
            (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ δ.1 / 2}), K w z.1) :=
              iInf_le_of_le ⟨δ.1 / 2, hHalfPos, hHalfLt⟩ le_rfl
          _ ≤ K w xStar := by
                refine iInf_le_of_le ⟨xStar, ?_⟩ ?_
                · have hHalfNonneg : 0 ≤ δ.1 / 2 := by
                    linarith [δ.2]
                  simpa using hHalfNonneg
                · rfl
      simpa [hz_eq_xStar] using hPositiveLeBase

/-- Helper for Text 34.1.4: on the left closed-ball-radius minimax envelope, both the outer
second-variable radii and the inner first-variable radii may be restricted to positive values
without changing the resulting value. -/
lemma helperForText_34_1_4_leftClosedBallRadiusEnvelope_eq_positiveRadii
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
      =
    (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1) := by
  let Kpos : SaddleFunction 0 n :=
    fun _ z =>
      (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z)
  have hInner :
      ∀ z : Fin n → ℝ,
        (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z)
          =
        Kpos 0 z := by
    intro z
    -- First normalize the inner first-variable radius family at the fixed point `z`.
    simpa [Kpos] using
      helperForText_34_1_4_iSup_closedBallValues_eq_iSup_positiveRadii
        (K := K) (u := u) (z := z) (ε := ε)
  have hOuter :
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), Kpos 0 z.1)
        =
      (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), Kpos 0 z.1) := by
    -- Then apply the already-proved outer-radius normalization to the derived section kernel.
    simpa [Kpos] using
      helperForText_34_1_4_iInf_closedBallValues_eq_iInf_positiveRadii
        (K := Kpos) (w := (0 : Fin 0 → ℝ)) (xStar := xStar) (δ := δ)
  calc
    (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
        =
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), Kpos 0 z.1) := by
          -- Rewrite the inner envelope pointwise before touching the outer radius family.
          refine iInf_congr ?_
          intro ρz
          refine iInf_congr ?_
          intro z
          exact hInner z.1
    _ =
      (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), Kpos 0 z.1) := hOuter
    _ =
      (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
          ⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1) := by
          -- Finally expand the derived section kernel back to the positive-radius raw envelope.
          refine iInf_congr ?_
          intro ρz
          refine iInf_congr ?_
          intro z
          simp [Kpos]

/-- Helper for Text 34.1.4: on the right closed-ball-radius maximin envelope, both the outer
first-variable radii and the inner second-variable radii may be restricted to positive values
without changing the resulting value. -/
lemma helperForText_34_1_4_rightClosedBallRadiusEnvelope_eq_positiveRadii
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1)
      =
    (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
  let Kpos : SaddleFunction m 0 :=
    fun w _ =>
      (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1)
  have hInner :
      ∀ w : Fin m → ℝ,
        (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w z.1)
          =
        Kpos w 0 := by
    intro w
    -- First normalize the inner second-variable radius family at the fixed point `w`.
    simpa [Kpos] using
      helperForText_34_1_4_iInf_closedBallValues_eq_iInf_positiveRadii
        (K := K) (w := w) (xStar := xStar) (δ := δ)
  have hOuter :
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), Kpos w.1 0)
        =
      (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), Kpos w.1 0) := by
    -- Then normalize the outer radius family for the derived first-variable section kernel.
    simpa [Kpos] using
      helperForText_34_1_4_iSup_closedBallValues_eq_iSup_positiveRadii
        (K := Kpos) (u := u) (z := (0 : Fin 0 → ℝ)) (ε := ε)
  calc
    (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1)
        =
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), Kpos w.1 0) := by
          -- Rewrite the inner envelope pointwise before touching the outer radius family.
          refine iSup_congr ?_
          intro ρw
          refine iSup_congr ?_
          intro w
          exact hInner w.1
    _ =
      (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), Kpos w.1 0) := hOuter
    _ =
      (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
          ⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
          -- Finally expand the derived section kernel back to the positive-radius raw envelope.
          refine iSup_congr ?_
          intro ρw
          refine iSup_congr ?_
          intro w
          simp [Kpos]

/-- Helper for Text 34.1.4: after restricting both radius families to positive values, the left
closed-ball-radius envelope is exactly the open-ball minimax expression on the same neighborhood
pair. -/
lemma helperForText_34_1_4_positiveRadiusLeftEnvelope_eq_fixedNeighborhood_minimax
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
      =
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
  -- First undo the positive-radius normalization to recover the earlier closed-ball-radius
  -- envelope.
  calc
    (⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
        ⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1)
        =
      (⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}),
          ⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
            ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}), K w.1 z.1) := by
          symm
          exact
            helperForText_34_1_4_leftClosedBallRadiusEnvelope_eq_positiveRadii
              (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
    -- Then rewrite that closed-ball-radius envelope back to the open-ball minimax expression.
    _ =
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
          exact
            (helperForText_34_1_4_fixedNeighborhood_minimax_openBall_as_closedBallRadii
              (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)).symm

/-- Helper for Text 34.1.4: after restricting both radius families to positive values, the
right closed-ball-radius envelope is exactly the open-ball maximin expression on the same
neighborhood pair. -/
lemma helperForText_34_1_4_positiveRadiusRightEnvelope_eq_fixedNeighborhood_maximin
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1)
      =
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- First undo the positive-radius normalization to recover the earlier closed-ball-radius
  -- envelope.
  calc
    (⨆ (ρw : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
        ⨅ (ρz : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
          ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1)
        =
      (⨆ (ρw : {ρ : ℝ // ρ < ε.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ ≤ ρw.1}),
          ⨅ (ρz : {ρ : ℝ // ρ < δ.1}),
            ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ ≤ ρz.1}), K w.1 z.1) := by
          symm
          exact
            helperForText_34_1_4_rightClosedBallRadiusEnvelope_eq_positiveRadii
              (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
    -- Then rewrite that closed-ball-radius envelope back to the open-ball maximin expression.
    _ =
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
          exact
            (helperForText_34_1_4_fixedNeighborhood_maximin_openBall_as_closedBallRadii
              (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)).symm

end SaddleAmbient

end Section34
end Chap07
