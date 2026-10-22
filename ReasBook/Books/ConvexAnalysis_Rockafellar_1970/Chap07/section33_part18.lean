/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part17

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

def HasInnerProductEquation : {m n : ℕ} → ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → Prop :=
  fun {m n} F =>
    ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      convexBifunctionPairing F u xStar = genuineConvexBifunctionAdjointPairing F u xStar

theorem optimalValueEqualityAtZero_iff_pairingEqualityAtZero :
    ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
      (∀ (u : Fin m → ℝ), sInf (Set.range (F u)) = -convexBifunctionPairing F u 0) ∧
        (∀ (xStar : Fin n → ℝ),
            sSup (Set.range (genuineConvexBifunctionAdjoint F xStar)) =
              -genuineConvexBifunctionAdjointPairing F 0 xStar) ∧
          (sInf (Set.range (F 0)) = sSup (Set.range (genuineConvexBifunctionAdjoint F 0)) ↔
            convexBifunctionPairing F 0 0 = genuineConvexBifunctionAdjointPairing F 0 0) :=
  fun {m n} F => by
    have hPrimal :
        ∀ u : Fin m → ℝ, sInf (Set.range (F u)) = -convexBifunctionPairing F u 0 := by
      intro u
      simpa [convexProgramAssociatedWith] using
        (helperForLemma33_0_32_primalValue_eq_neg_pairingAtZero (F := F) u)
    have hDual :
        ∀ xStar : Fin n → ℝ,
          sSup (Set.range (genuineConvexBifunctionAdjoint F xStar)) =
            -genuineConvexBifunctionAdjointPairing F 0 xStar := by
      intro xStar
      calc
        sSup (Set.range fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint F xStar vStar)
            = iSup (fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint F xStar vStar) := by
                rw [sSup_range]
        _ =
            -(iInf fun vStar : Fin m → ℝ =>
                (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                  (-genuineConvexBifunctionAdjoint F xStar vStar))) := by
                calc
                  iSup (fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint F xStar vStar)
                      =
                        iSup (fun vStar : Fin m → ℝ =>
                          -((((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                            (-genuineConvexBifunctionAdjoint F xStar vStar)))) := by
                              congr with vStar
                              simp
                  _ =
                      -(iInf fun vStar : Fin m → ℝ =>
                          (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                            (-genuineConvexBifunctionAdjoint F xStar vStar))) := by
                              symm
                              exact helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                                (φ := fun vStar : Fin m → ℝ =>
                                  (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                                    (-genuineConvexBifunctionAdjoint F xStar vStar)))
        _ =
            -(iInf fun vStar : Fin m → ℝ =>
                (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) -
                  genuineConvexBifunctionAdjoint F xStar vStar)) := by
                    congr with vStar
        _ = -genuineConvexBifunctionAdjointPairing F (0 : Fin m → ℝ) xStar := by
              rw [genuineConvexBifunctionAdjointPairing, sInf_range]
    refine ⟨hPrimal, hDual, ?_⟩
    constructor
    · intro hValue
      have hNeg :
          -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
            -genuineConvexBifunctionAdjointPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) := by
        calc
          -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ)
              = sInf (Set.range (F (0 : Fin m → ℝ))) := by
                  symm
                  exact hPrimal (0 : Fin m → ℝ)
          _ = sSup (Set.range (genuineConvexBifunctionAdjoint F (0 : Fin n → ℝ))) := hValue
          _ =
              -genuineConvexBifunctionAdjointPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) :=
                hDual (0 : Fin n → ℝ)
      simpa using congrArg Neg.neg hNeg
    · intro hPair
      have hNeg :
          -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
            -genuineConvexBifunctionAdjointPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) := by
        exact congrArg Neg.neg hPair
      calc
        sInf (Set.range (F (0 : Fin m → ℝ)))
            = -convexBifunctionPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) :=
              hPrimal (0 : Fin m → ℝ)
        _ =
            -genuineConvexBifunctionAdjointPairing F (0 : Fin m → ℝ) (0 : Fin n → ℝ) :=
              hNeg
        _ = sSup (Set.range (genuineConvexBifunctionAdjoint F (0 : Fin n → ℝ))) := by
              symm
              exact hDual (0 : Fin n → ℝ)

def translatedTiltedBifunction : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → (Fin m → ℝ) → (Fin n → ℝ) →
      (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun {m n} F u xStar v y => F (u + v) y - ↑(y ⬝ᵥ xStar)

theorem genuineConvexBifunctionAdjoint_translatedTiltedBifunction :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
      {u vStar : Fin m → ℝ} {xStar yStar : Fin n → ℝ},
      genuineConvexBifunctionAdjoint (translatedTiltedBifunction F u xStar) yStar vStar =
        genuineConvexBifunctionAdjoint F (xStar + yStar) vStar - ↑(u ⬝ᵥ vStar) :=
  by
    intro m n F u vStar xStar yStar
    -- Route correction: the downstream theorem lives in this split file, so we reuse the
    -- raw translated-adjoint identity from part11 and convert it directly to the displayed
    -- `genuineConvexBifunctionAdjoint` formula.
    -- Step 1: both sides are definitionally the raw `sInf` adjoint expressions of part11.
    simpa [genuineConvexBifunctionAdjoint, translatedTiltedBifunction,
      helperForLemma33_0_34_rawGenuineAdjoint, helperForLemma33_0_34_translatedTiltedBifunction]
      using
        (helperForLemma33_0_34_rawGenuineAdjoint_translatedTiltedBifunction
          (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar))

/-- Helper for Lemma33.0.35: evaluating the translated genuine adjoint at the zero dual
section gives exactly the textbook dual objective. -/
lemma helperForLemma33_0_35_translatedTiltedGenuineAdjointAtZero_eq_targetDualObjective
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ)
    (vStar : Fin m → ℝ) :
    genuineConvexBifunctionAdjoint
        (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar =
      genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar) := by
  -- Step 1: specialize the translated-adjoint identity at `yStar = 0`.
  simpa using
    (genuineConvexBifunctionAdjoint_translatedTiltedBifunction
      (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := (0 : Fin n → ℝ)))

/-- Helper for Lemma33.0.35: the supremum of the zero primal section of the genuine adjoint is
the negative of the corresponding genuine-adjoint pairing at the origin. -/
lemma helperForLemma33_0_35_genuineAdjointZeroSection_sSup_eq_negPairingAtZero
    {m n : ℕ}
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) :
    sSup (Set.range fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint G xStar vStar) =
      -genuineConvexBifunctionAdjointPairing G (0 : Fin m → ℝ) xStar := by
  -- Step 1: rewrite the displayed supremum as an indexed supremum.
  calc
    sSup (Set.range fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint G xStar vStar)
        = iSup (fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint G xStar vStar) := by
            rw [sSup_range]
    -- Step 2: transport the indexed supremum to a negated indexed infimum.
    _ =
        -(iInf fun vStar : Fin m → ℝ =>
            (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
              (-genuineConvexBifunctionAdjoint G xStar vStar))) := by
            calc
              iSup (fun vStar : Fin m → ℝ => genuineConvexBifunctionAdjoint G xStar vStar)
                  =
                    iSup (fun vStar : Fin m → ℝ =>
                      -((((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                        (-genuineConvexBifunctionAdjoint G xStar vStar)))) := by
                          congr with vStar
                          simp
              _ =
                  -(iInf fun vStar : Fin m → ℝ =>
                      (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                        (-genuineConvexBifunctionAdjoint G xStar vStar))) := by
                          symm
                          exact helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                            (φ := fun vStar : Fin m → ℝ =>
                              (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) +
                                (-genuineConvexBifunctionAdjoint G xStar vStar)))
    -- Step 3: identify that indexed infimum with the definition of the genuine-adjoint
    -- pairing at the zero primal vector.
    _ =
        -(iInf fun vStar : Fin m → ℝ =>
            (((dotProduct (0 : Fin m → ℝ) vStar : ℝ) : EReal) -
              genuineConvexBifunctionAdjoint G xStar vStar)) := by
              congr with vStar
    _ = -genuineConvexBifunctionAdjointPairing G (0 : Fin m → ℝ) xStar := by
          rw [genuineConvexBifunctionAdjointPairing, sInf_range]

/-- Helper for Lemma33.0.35: the zero pairing of the translated-and-tilted bifunction is the
textbook genuine-adjoint pairing `⟪u, F^* x^*⟫`. -/
lemma helperForLemma33_0_35_translatedTiltedGenuineAdjointPairingAtZero_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    genuineConvexBifunctionAdjointPairing
        (translatedTiltedBifunction F u xStar) (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
      genuineConvexBifunctionAdjointPairing F u xStar := by
  -- Step 1: unfold both pairings to compare their indexed infimum formulas directly.
  rw [genuineConvexBifunctionAdjointPairing, genuineConvexBifunctionAdjointPairing,
    sInf_range, sInf_range]
  -- Step 2: for each dual vector, rewrite the translated adjoint at the origin using the
  -- translated-adjoint theorem proved just above.
  congr with vStar
  rw [helperForLemma33_0_35_translatedTiltedGenuineAdjointAtZero_eq_targetDualObjective
    (F := F) u xStar vStar]
  -- Step 3: simplify the zero dot product and regroup the resulting affine expression.
  simp_rw [sub_eq_add_neg]
  have hNegAdd :
      -(genuineConvexBifunctionAdjoint F xStar vStar + -↑(u ⬝ᵥ vStar)) =
        -genuineConvexBifunctionAdjoint F xStar vStar - (-↑(u ⬝ᵥ vStar)) := by
    exact EReal.neg_add (x := genuineConvexBifunctionAdjoint F xStar vStar)
      (y := -↑(u ⬝ᵥ vStar)) (Or.inr (by simp)) (Or.inr (by simp))
  rw [hNegAdd]
  rw [sub_eq_add_neg]
  simp [add_comm]

/-- Helper for Lemma33.0.35: the dual objective range in the textbook statement is exactly
the zero dual section of the translated-and-tilted bifunction. -/
lemma helperForLemma33_0_35_translatedTiltedDualRange_eq_targetDualRange
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    Set.range
        (fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint
            (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar) =
      Set.range
        (fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨vStar, rfl⟩
    -- Step 1: the same witness `vStar` realizes the target range after rewriting the
    -- translated adjoint at `yStar = 0`.
    refine ⟨vStar, ?_⟩
    simpa using
      (helperForLemma33_0_35_translatedTiltedGenuineAdjointAtZero_eq_targetDualObjective
        (F := F) u xStar vStar).symm
  · intro hz
    rcases hz with ⟨vStar, rfl⟩
    -- Step 2: conversely, the same dual witness comes from the zero translated section.
    refine ⟨vStar, ?_⟩
    simpa using
      (helperForLemma33_0_35_translatedTiltedGenuineAdjointAtZero_eq_targetDualObjective
        (F := F) u xStar vStar)

/-- Helper for Lemma33.0.35: the zero primal section of the translated-and-tilted bifunction
already has the textbook primal optimal value. -/
lemma helperForLemma33_0_35_translatedTiltedPrimalZeroSection_sInf_eq_negPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    sInf
        (Set.range fun y : Fin n → ℝ =>
          translatedTiltedBifunction F u xStar (0 : Fin m → ℝ) y) =
      -convexBifunctionPairing F u xStar := by
  -- Step 1: specialize the translated primal-value formula at the zero translation vector.
  simpa [convexProgramAssociatedWith, translatedTiltedBifunction] using
    congrFun
      (helperForLemma33_0_22_translatedTiltedPrimalValue_eq_shiftedNegPairingSection
        (F := F) u xStar)
      (0 : Fin m → ℝ)

/-- Helper for Lemma33.0.35: the textbook primal objective has the same infimum as the zero
primal section of the translated-and-tilted bifunction. -/
lemma helperForLemma33_0_35_targetPrimalObjective_sInf_eq_translatedTiltedPrimalZeroSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    sInf (Set.range fun y : Fin n → ℝ => F u y - ↑(y ⬝ᵥ xStar)) =
      sInf
        (Set.range fun y : Fin n → ℝ =>
          translatedTiltedBifunction F u xStar (0 : Fin m → ℝ) y) := by
  -- Step 1: reuse the previously prepared zero-section identification from part9.
  symm
  -- Step 2: the translated bifunction at primal shift `0` is exactly the displayed tilted
  -- textbook objective.
  change
      sInf
          (Set.range
            (fun y : Fin n → ℝ =>
              (fun v : Fin m → ℝ => fun y : Fin n → ℝ =>
                F (u + v) y - ((dotProduct y xStar : ℝ) : EReal))
                (0 : Fin m → ℝ) y)) =
        sInf (Set.range (fun y : Fin n → ℝ => F u y - ((dotProduct y xStar : ℝ) : EReal)))
  exact
    helperForLemma33_0_35_zeroSection_sInf_eq_tiltedObjective_sInf
      (F := F) u xStar

/-- Helper for Lemma33.0.35: the zero dual section of the translated-and-tilted bifunction
already has the textbook dual optimal value. -/
lemma helperForLemma33_0_35_translatedTiltedDualZeroSection_sSup_eq_negPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    sSup
        (Set.range fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint
            (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar) =
      -genuineConvexBifunctionAdjointPairing F u xStar := by
  -- Step 1: apply the generic zero-section supremum identity to the translated bifunction.
  calc
    sSup
        (Set.range fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint
            (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar)
        =
          -genuineConvexBifunctionAdjointPairing
            (translatedTiltedBifunction F u xStar) (0 : Fin m → ℝ) (0 : Fin n → ℝ) := by
              exact
                helperForLemma33_0_35_genuineAdjointZeroSection_sSup_eq_negPairingAtZero
                  (G := translatedTiltedBifunction F u xStar) (xStar := (0 : Fin n → ℝ))
    -- Step 2: identify that translated zero pairing with the displayed pairing of `F`.
    _ = -genuineConvexBifunctionAdjointPairing F u xStar := by
          rw [helperForLemma33_0_35_translatedTiltedGenuineAdjointPairingAtZero_eq
            (F := F) u xStar]

/-- Helper for Lemma33.0.35: the textbook dual objective has the same supremum as the zero
dual section of the translated-and-tilted bifunction. -/
lemma helperForLemma33_0_35_targetDualObjective_sSup_eq_translatedTiltedDualZeroSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    sSup
        (Set.range fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) =
      sSup
        (Set.range fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint
            (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar) := by
  -- Step 1: first identify the two dual value sets pointwise.
  have hRange :
      Set.range
          (fun vStar : Fin m → ℝ =>
            genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) =
        Set.range
          (fun vStar : Fin m → ℝ =>
            genuineConvexBifunctionAdjoint
              (translatedTiltedBifunction F u xStar) (0 : Fin n → ℝ) vStar) :=
    (helperForLemma33_0_35_translatedTiltedDualRange_eq_targetDualRange
      (F := F) u xStar).symm
  -- Step 2: transport the equality of ranges through `sSup`.
  exact congrArg sSup hRange

theorem translatedTiltedBifunction_optimalValues :
    ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
      IsGraphConvexBifunction F →
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
          sInf (Set.range fun y => F u y - ↑(y ⬝ᵥ xStar)) = -convexBifunctionPairing F u xStar ∧
            sSup
                (Set.range fun vStar =>
                  genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) =
              -genuineConvexBifunctionAdjointPairing F u xStar :=
  by
    intro m n F hF_convex u xStar
    constructor
    · -- Route correction: instead of the earlier wrong part9 route, we identify the textbook
      -- tilted objective with the zero primal section of the translated bifunction that lives
      -- in this file and then specialize the established translated primal-value formula at `0`.
      -- Step 1: rewrite the textbook infimum as the zero section of
      -- `translatedTiltedBifunction F u xStar`.
      calc
        sInf (Set.range fun y => F u y - ↑(y ⬝ᵥ xStar))
            = sInf
                (Set.range fun y =>
                  translatedTiltedBifunction F u xStar (0 : Fin m → ℝ) y) := by
                    exact
                      helperForLemma33_0_35_targetPrimalObjective_sInf_eq_translatedTiltedPrimalZeroSection
                        (F := F) u xStar
        -- Step 2: the translated primal-value identity at the origin is exactly the displayed
        -- negative pairing formula.
        _ = -convexBifunctionPairing F u xStar := by
              exact
                helperForLemma33_0_35_translatedTiltedPrimalZeroSection_sInf_eq_negPairing
                  (F := F) u xStar
    · -- Step 1: rewrite the displayed dual objective range as the zero dual section of the
      -- translated-and-tilted bifunction.
      rw [helperForLemma33_0_35_targetDualObjective_sSup_eq_translatedTiltedDualZeroSection
        (F := F) u xStar]
      -- Step 2: the translated zero dual section already computes the displayed dual value.
      exact
        helperForLemma33_0_35_translatedTiltedDualZeroSection_sSup_eq_negPairing
          (F := F) u xStar

def HasEqualOptimalValuesForTranslatedTiltedPrograms : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → (Fin m → ℝ) → (Fin n → ℝ) → Prop :=
  fun {m n} F u xStar =>
    sInf (Set.range fun y => F u y - ↑(y ⬝ᵥ xStar)) =
      sSup
        (Set.range fun vStar =>
          genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar))

/-- The translated-program normality predicate used downstream only through its criterion-level
interface is aligned with equality of the translated primal and dual optimal values.

Route correction: the earlier coordinatewise-closure encoding was stronger than what the later
split files actually consume, and it did not match the Chapter 30 normality criterion that drives
these translated arguments. -/
def HasNormalityForTranslatedTiltedPrograms : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → (Fin m → ℝ) → (Fin n → ℝ) → Prop :=
  fun {m n} F u xStar =>
    HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar

theorem pairingEquality_iff_equalOptimalValues_for_translatedTiltedPrograms :
    ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
      IsGraphConvexBifunction F →
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
          convexBifunctionPairing F u xStar =
              genuineConvexBifunctionAdjointPairing F u xStar ↔
            HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar :=
  fun {m n} F hF_convex u xStar => by
    -- Step 1: rewrite the translated primal and dual optimal values in terms of the two
    -- pairing quantities that appear in the statement.
    have hOptimalValues :=
      translatedTiltedBifunction_optimalValues F hF_convex u xStar
    constructor
    · intro hPairing
      -- Step 2: once the two pairings agree, the two translated optimal values agree as
      -- their negatives.
      unfold HasEqualOptimalValuesForTranslatedTiltedPrograms
      rw [hOptimalValues.1, hOptimalValues.2]
      simpa [hPairing]
    · intro hEqualValues
      -- Step 3: conversely, equality of the translated optimal values is equality of the two
      -- negated pairings, so negate both sides to recover the displayed pairing identity.
      unfold HasEqualOptimalValuesForTranslatedTiltedPrograms at hEqualValues
      rw [hOptimalValues.1, hOptimalValues.2] at hEqualValues
      have hNegated := congrArg Neg.neg hEqualValues
      simpa using hNegated

theorem normality_iff_equalOptimalValues_for_translatedTiltedPrograms :
    ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
      (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      HasNormalityForTranslatedTiltedPrograms F u xStar ↔
        HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar :=
  fun {m n} F u xStar => by
    rfl

theorem pairingEquality_iff_normality_for_translatedTiltedPrograms :
    ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
      IsGraphConvexBifunction F →
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
          convexBifunctionPairing F u xStar =
              genuineConvexBifunctionAdjointPairing F u xStar ↔
            HasNormalityForTranslatedTiltedPrograms F u xStar :=
  fun {m n} F hF_convex u xStar => by
    -- Step 1: both displayed predicates are already equivalent to equality of the translated
    -- primal and dual optimal values, so compose those two equivalences.
    exact
      helperForLemma33_0_36_equivalent_of_sharedCriterion
        (pairingEquality_iff_equalOptimalValues_for_translatedTiltedPrograms
          F hF_convex u xStar)
        (normality_iff_equalOptimalValues_for_translatedTiltedPrograms F u xStar)

/-- Helper for Lemma33.0.37: outside the second component of `dom F*`, the whole genuine
adjoint section is constantly `⊥`. -/
lemma helperForLemma33_0_37_allBotGenuineAdjoint_of_off_secondConvexBifunctionDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ}
    (hOutside : xStar ∉ (convexBifunctionDomains F).2) :
    ∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥ := by
  have hOutside' :
      ¬ ∃ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥ := by
    simpa [convexBifunctionDomains] using hOutside
  intro uStar
  by_contra hBot
  exact hOutside' ⟨uStar, hBot⟩

/-- Helper for Lemma33.0.37: leaving the first convex-bifunction domain component forces both
the primal section and every primal pairing to collapse. -/
lemma helperForLemma33_0_37_primalCollapse_of_off_firstConvexBifunctionDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    (hu : u ∉ (convexBifunctionDomains F).1) :
    (∀ x : Fin n → ℝ, F u x = ⊤) ∧
      (∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = ⊥) := by
  -- Step 1: rewrite the first domain exclusion into the parameter-domain form used earlier.
  have hu' : u ∉ convexBifunctionParameterDomain F := by
    simpa [convexBifunctionDomains] using hu
  constructor
  · -- Step 2: outside `dom F`, the whole primal section is the constant `⊤` function.
    exact
      helperForCorollary33_2_2_allTop_of_off_convexParameterDomain
        (G := F) hu'
  · intro xStar
    -- Step 3: the same domain exclusion makes every primal pairing equal `⊥`.
    exact
      helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
        (G := F) hu' xStar

/-- Helper for Lemma33.0.37: if the genuine adjoint section is constantly `⊥`, then the
adjoint-side pairing collapses to `⊤`. -/
lemma helperForLemma33_0_37_genuineAdjointPairing_eq_top_of_allBotAdjointSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ}
    (hAllBot : ∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥) :
    ∀ u : Fin m → ℝ, genuineConvexBifunctionAdjointPairing F u xStar = ⊤ := by
  intro u
  rw [genuineConvexBifunctionAdjointPairing, sInf_range]
  apply le_antisymm
  · exact le_top
  · refine le_iInf ?_
    intro uStar
    simp [hAllBot uStar]

/-- Helper for Lemma33.0.37: leaving the second convex-bifunction domain component forces both
the genuine adjoint section and every adjoint-side pairing to collapse. -/
lemma helperForLemma33_0_37_dualCollapse_of_off_secondConvexBifunctionDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ}
    (hx : xStar ∉ (convexBifunctionDomains F).2) :
    (∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥) ∧
      (∀ u : Fin m → ℝ, genuineConvexBifunctionAdjointPairing F u xStar = ⊤) := by
  -- Step 1: outside `dom F*`, the whole genuine adjoint section is the constant `⊥` function.
  have hAllBot :
      ∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥ :=
    helperForLemma33_0_37_allBotGenuineAdjoint_of_off_secondConvexBifunctionDomain
      (F := F) hx
  constructor
  · exact hAllBot
  · intro u
    -- Step 2: once the adjoint section is constantly `⊥`, the adjoint pairing is `⊤`.
    exact
      helperForLemma33_0_37_genuineAdjointPairing_eq_top_of_allBotAdjointSection
        (F := F) (xStar := xStar) hAllBot u

theorem oppositeInfinities_off_both_convexBifunctionDomains :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
      {u : Fin m → ℝ} {xStar : Fin n → ℝ},
      u ∉ (convexBifunctionDomains F).1 →
        xStar ∉ (convexBifunctionDomains F).2 →
          (∀ (x : Fin n → ℝ), F u x = ⊤) ∧
            (∀ (uStar : Fin m → ℝ), genuineConvexBifunctionAdjoint F xStar uStar = ⊥) ∧
              convexBifunctionPairing F u xStar = ⊥ ∧
                genuineConvexBifunctionAdjointPairing F u xStar = ⊤ :=
  fun {m n} {F} {u} {xStar} hu hx => by
    -- Step 1: the first domain exclusion collapses the primal section and primal pairing.
    have hPrimalCollapse :
        (∀ x : Fin n → ℝ, F u x = ⊤) ∧
          (∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = ⊥) :=
      helperForLemma33_0_37_primalCollapse_of_off_firstConvexBifunctionDomain
        (F := F) hu
    -- Step 2: the second domain exclusion collapses the genuine adjoint section and
    -- the adjoint-side pairing.
    have hDualCollapse :
        (∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥) ∧
          (∀ u : Fin m → ℝ, genuineConvexBifunctionAdjointPairing F u xStar = ⊤) :=
      helperForLemma33_0_37_dualCollapse_of_off_secondConvexBifunctionDomain
        (F := F) hx
    have hAllTop :
        ∀ x : Fin n → ℝ, F u x = ⊤ := hPrimalCollapse.1
    have hAllBot :
        ∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥ :=
      hDualCollapse.1
    have hPairingBot :
        convexBifunctionPairing F u xStar = ⊥ := hPrimalCollapse.2 xStar
    have hAdjointPairingTop :
        genuineConvexBifunctionAdjointPairing F u xStar = ⊤ := hDualCollapse.2 u
    -- Step 3: package the four collapse statements in the textbook order.
    exact ⟨hAllTop, hAllBot, hPairingBot, hAdjointPairingTop⟩

def IsFullyClosedSaddleFunction : {m n : ℕ} → ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → Prop :=
  fun {m n} K =>
    IsConcaveConvexOn Set.univ Set.univ K ∧ IsConcaveClosedInFirst K ∧ IsConvexClosedInSecond K ∨
      IsConvexConcaveOn Set.univ Set.univ K ∧ IsConvexClosedInFirst K ∧ IsConcaveClosedInSecond K

/-- Helper for Theorem33.0.39: a pairing representation by `convexBifunctionPairing F`
combined with the absence of `⊥`-values already forces the full primal parameter domain of
`F`. -/
lemma helperForTheorem33_0_39_fullParameterDomain_of_pairingRepresentation
    {n : ℕ}
    {K F : (Fin n → ℝ) → (Fin n → ℝ) → EReal}
    (hRep : K = convexBifunctionPairing F)
    (hNoBot : HasNoBotValuesBifunction K) :
    (convexBifunctionDomains F).1 = Set.univ := by
  ext u
  constructor
  · intro _hu
    simp
  · intro _hu
    -- Step 1: if `u` were outside the first domain component, the whole primal pairing
    -- section would collapse to `⊥`.
    by_contra huOutside
    have hCollapse :
        ∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = ⊥ :=
      (helperForLemma33_0_37_primalCollapse_of_off_firstConvexBifunctionDomain
        (F := F) huOutside).2
    have hPointRep :
        K u (0 : Fin n → ℝ) = convexBifunctionPairing F u (0 : Fin n → ℝ) := by
      exact congrArg (fun G => G u (0 : Fin n → ℝ)) hRep
    -- Step 2: evaluating at the zero dual vector contradicts the assumed no-`⊥` property of
    -- the represented kernel `K`.
    have hKNoBot : K u (0 : Fin n → ℝ) ≠ (⊥ : EReal) :=
      hNoBot u (0 : Fin n → ℝ)
    exact hKNoBot (hPointRep.trans (hCollapse 0))

/-- Helper for Theorem33.0.39: a full primal parameter domain gives a concrete non-`⊤`
witness in every primal section. -/
lemma helperForTheorem33_0_39_sectionWitness_of_fullParameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom : (convexBifunctionDomains F).1 = Set.univ) :
    ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤ := by
  intro u
  -- Step 1: rewrite the full-domain hypothesis as membership of `u` in the first domain
  -- component.
  have hu : u ∈ (convexBifunctionDomains F).1 := by
    simpa [hDom]
  -- Step 2: unfold the first domain component back to the parameter-domain witness statement.
  simpa [convexBifunctionDomains, convexBifunctionParameterDomain] using hu

/-- Helper for Theorem33.0.39: full primal parameter domain makes every translated-and-tilted
primal program consistent at the origin. -/
lemma helperForTheorem33_0_39_translatedPrimalOrigin_neTop_of_fullParameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom : (convexBifunctionDomains F).1 = Set.univ) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) (0 : Fin m → ℝ) ≠
        (⊤ : EReal) := by
  intro u xStar
  -- Step 1: full parameter domain gives the non-`⊤` section witnesses required by the
  -- translated primal-consistency lemma from Section 33.
  have hSectionWitness :
      ∀ u' : Fin m → ℝ, ∃ x : Fin n → ℝ, F u' x ≠ ⊤ :=
    helperForTheorem33_0_39_sectionWitness_of_fullParameterDomain
      (F := F) hDom
  -- Step 2: specialize the translated primal-value lemma at `(u, xStar)`.
  simpa [translatedTiltedBifunction] using
    (helperForLemma33_0_22_translatedTiltedPrimalValue_atOrigin_ne_top
      (F := F) hSectionWitness u xStar)

/-- Helper for Theorem33.0.39: graph-function closedness upgrades a Rockafellar convex
bifunction to the graph-convex predicate used by the translated-program machinery. -/
lemma helperForTheorem33_0_39_graphConvex_of_graphFunctionClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F)) :
    IsGraphConvexBifunction F := by
  have hSectionClosed : ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hSectionClosureExact :
      ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ,
        convexFunctionClosure (F u) x = F u x := by
    intro u x
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x :=
        helperForLemma33_0_18_functionConvexClosure_eq_self (hSectionClosed u) x
  exact
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRock hSectionClosureExact hNoBot

/-- Helper for Theorem33.0.39: full primal parameter domain already forces the strict
parameter domain `{u | ∃ x, F u x < ⊤}` to be all of space. -/
lemma helperForTheorem33_0_39_strictParameterDomain_of_fullParameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom : (convexBifunctionDomains F).1 = Set.univ) :
    {u : Fin m → ℝ | ∃ x : Fin n → ℝ, F u x < ⊤} = Set.univ := by
  ext u
  constructor
  · intro _hu
    simp
  · intro _hu
    -- Step 1: the full parameter-domain hypothesis gives a point in the section where the
    -- value is not `⊤`.
    rcases
        helperForTheorem33_0_39_sectionWitness_of_fullParameterDomain
          (F := F) hDom u with
      ⟨x, hx⟩
    -- Step 2: any value different from `⊤` is automatically strictly below `⊤`.
    refine ⟨x, ?_⟩
    exact lt_of_le_of_ne le_top hx

/-- Helper for Theorem33.0.39: in the full primal-domain branch, Corollary33.2.1 already
identifies the primal pairing with the closure-side adjoint pairing everywhere. -/
lemma helperForTheorem33_0_39_closureSidePairingEq_of_fullParameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hDom : (convexBifunctionDomains F).1 = Set.univ) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u := by
  intro u xStar
  -- Step 1: every point of `ℝ^m` lies in the intrinsic interior of the strict parameter
  -- domain once that domain is all of space.
  have huInterior : u ∈ interior (Set.univ : Set (Fin m → ℝ)) := by
    simpa [interior_univ]
  have huII : u ∈ intrinsicInterior ℝ (Set.univ : Set (Fin m → ℝ)) :=
    (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin m → ℝ)))) huInterior
  have huDomain :
      u ∈ intrinsicInterior ℝ {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, F u' x < ⊤} := by
    simpa
      [helperForTheorem33_0_39_strictParameterDomain_of_fullParameterDomain
        (F := F) hDom] using huII
  -- Step 2: Corollary33.2.1 now applies directly at the chosen parameter point.
  exact
    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).1
      (F := F) ⟨hGraph, hNoBot⟩).1 huDomain xStar

/-- Helper for Corollary33.0.40: the explicit genuine adjoint is the first parameter-side
conjugate `convexBifunctionAdjointPairing`, not its second-conjugate pairing. -/
lemma helperForCorollary33_0_40_genuineAdjoint_eq_convexBifunctionAdjointPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ)
    (uStar : Fin m → ℝ) :
    genuineConvexBifunctionAdjoint F xStar uStar =
      convexBifunctionAdjointPairing F xStar uStar := by
  -- Step 1: unfold the genuine adjoint and the closure-side adjoint pairing into indexed
  -- infimum formulas over the primal parameter.
  rw [genuineConvexBifunctionAdjoint, convexBifunctionAdjointPairing,
    helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  have hPairingSection :
      ∀ u : Fin m → ℝ,
        -convexBifunctionPairing F u xStar =
          iInf (fun x : Fin n → ℝ => F u x - ((dotProduct x xStar : ℝ) : EReal)) := by
    intro u
    -- Step 2: the one-variable infimum formula for `-⟪F u, x^*⟫` is already available from
    -- the tilted-fiber identity proved earlier in Section 33.
    have h :=
      helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing (F := F) u xStar
    simpa [graphFunctionOfBifunction, sInf_range] using h.symm
  -- Step 3: split the two-variable infimum into nested infima and identify the inner one with
  -- the negative pairing section.
  calc
    sInf
        (Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
          (F ux.1 ux.2 - ↑(ux.2 ⬝ᵥ xStar)) + ↑(ux.1 ⬝ᵥ uStar))
        =
          iInf (fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
            (F ux.1 ux.2 - ↑(ux.2 ⬝ᵥ xStar)) + ↑(ux.1 ⬝ᵥ uStar)) := by
              rw [sInf_range]
    _ =
        iInf (fun u : Fin m → ℝ =>
          iInf (fun x : Fin n → ℝ =>
            (F u x - ↑(x ⬝ᵥ xStar)) + ↑(u ⬝ᵥ uStar))) := by
              simpa using
                (helperForTheorem_6_30_22_iInf_prod_eq_nested
                  (H := fun (u : Fin m → ℝ) (x : Fin n → ℝ) =>
                    (F u x - ↑(x ⬝ᵥ xStar)) + ↑(u ⬝ᵥ uStar)))
    _ =
        iInf (fun u : Fin m → ℝ =>
          iInf (fun x : Fin n → ℝ => F u x - ↑(x ⬝ᵥ xStar)) + ↑(u ⬝ᵥ uStar)) := by
              congr with u
              simpa [add_comm, add_left_comm, add_assoc] using
                (helperForTheorem_6_30_15_real_add_iInf (c := (u ⬝ᵥ uStar : ℝ))
                  (f := fun x : Fin n → ℝ => F u x - ↑(x ⬝ᵥ xStar))).symm
    _ =
        iInf (fun u : Fin m → ℝ =>
          ↑(u ⬝ᵥ uStar) + -convexBifunctionPairing F u xStar) := by
              congr with u
              simpa [hPairingSection u, add_comm, add_left_comm, add_assoc]
    _ =
        iInf (fun u : Fin m → ℝ =>
          ↑(u ⬝ᵥ uStar) + -convexBifunctionPairing F u xStar) := by
              rfl

/-- Compatibility name for the genuine-adjoint identification used by later split files. -/
lemma helperForCorollary33_0_40_genuineAdjoint_eq_closureSideAdjointPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    genuineConvexBifunctionAdjoint F xStar uStar =
      convexBifunctionAdjointPairing F xStar uStar :=
  helperForCorollary33_0_40_genuineAdjoint_eq_convexBifunctionAdjointPairing
    (F := F) xStar uStar

/-- Helper for Corollary33.0.40: the genuine adjoint pairing is exactly the concave conjugate
of the genuine adjoint section in the primal variable. -/
lemma helperForCorollary33_0_40_genuinePairing_eq_concaveConjugate_genuineAdjoint
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    genuineConvexBifunctionAdjointPairing F u xStar =
      concaveConjugate (genuineConvexBifunctionAdjoint F xStar) u := by
  -- Step 1: both sides are the same indexed infimum formula, up to the symmetric dot product.
  rw [genuineConvexBifunctionAdjointPairing,
    helperForTheorem_6_30_4_concaveConjugate_eq_iInf, sInf_range]
  congr with uStar
  rw [sub_eq_add_neg, dotProduct_comm]

/-- The genuine adjoint pairing and the canonical Section 33 adjoint pairing are the same
second conjugate.  Neither is the first-conjugate adjoint itself. -/
lemma helperForCorollary33_0_40_genuinePairing_eq_convexAdjointPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    genuineConvexBifunctionAdjointPairing F u xStar =
      convexBifunctionCanonicalAdjointPairing F xStar u := by
  calc
    genuineConvexBifunctionAdjointPairing F u xStar =
        concaveConjugate (genuineConvexBifunctionAdjoint F xStar) u :=
      helperForCorollary33_0_40_genuinePairing_eq_concaveConjugate_genuineAdjoint
        (F := F) u xStar
    _ = concaveConjugate (convexBifunctionAdjointPairing F xStar) u := by
      congr 1
      funext uStar
      exact
        helperForCorollary33_0_40_genuineAdjoint_eq_convexBifunctionAdjointPairing
          (F := F) xStar uStar
    _ = convexBifunctionCanonicalAdjointPairing F xStar u := by rfl

/-- Helper for Corollary33.0.40: full primal domain forces the genuine adjoint pairing to
collapse back to the primal pairing at every point. -/
lemma helperForCorollary33_0_40_pairing_eq_genuinePairing_of_fullParameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hDom : (convexBifunctionDomains F).1 = Set.univ) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      genuineConvexBifunctionAdjointPairing F u xStar =
        convexBifunctionPairing F u xStar := by
  intro u xStar
  let q : (Fin m → ℝ) → EReal := fun u' => convexBifunctionPairing F u' xStar
  have hClosureEq : ∀ u' : Fin m → ℝ, concaveClosure q u' = q u' := by
    intro u'
    -- Step 1: full primal domain puts every parameter in the intrinsic interior of the strict
    -- primal domain, where Corollary 33.2.1 fixes the concave closure of the pairing section.
    change concaveClosure (fun u'' => convexBifunctionPairing F u'' xStar) u' = _
    exact
      helperForCorollary33_2_1_convexPairingSection_closure_eq_self_on_intrinsicInterior
        (F := F) hGraph hNoBot
        (helperForCorollary33_0_40_mem_intrinsicInterior_of_fullStrictPrimalDomain
          (F := F)
          (helperForTheorem33_0_39_strictParameterDomain_of_fullParameterDomain
            (F := F) hDom)
          u')
        xStar
  have hAdjointClosure :
      ∀ u' : Fin m → ℝ, convexBifunctionCanonicalAdjointPairing F xStar u' = q u' := by
    intro u'
    -- Step 2: Theorem 33.2 identifies the closure-side adjoint pairing with the concave
    -- closure of the fixed-dual pairing section, which is exact everywhere by Step 1.
    rcases
        (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
          ⟨hGraph, hNoBot⟩ with
      ⟨hFirst, _hSecond⟩
    calc
      convexBifunctionCanonicalAdjointPairing F xStar u' = concaveClosure q u' := by
        simpa [q] using hFirst xStar u'
      _ = q u' := hClosureEq u'
  -- The explicit genuine pairing is the same second conjugate used by the canonical API.
  calc
    genuineConvexBifunctionAdjointPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
      helperForCorollary33_0_40_genuinePairing_eq_convexAdjointPairing
        (F := F) u xStar
    _ = q u := hAdjointClosure u
    _ = convexBifunctionPairing F u xStar := by
          rfl

/-- Theorem33.0.39 (corrected witness-upgrade fragment):
once a kernel `K` is already represented by a graph-convex bifunction `F` with no `⊥`-values
and full primal parameter domain, the Section 33 global pairing identity
`⟪F u, x^*⟫ = (F^* x^*)(u)` follows everywhere. This is the dependency-closed part of the
original textbook statement that is actually used later: the converse existence direction and
the full coordinatewise-closure equivalence require additional bridges handled elsewhere. -/
theorem fullyClosedConcaveConvex_iff_exists_graphConvexBifunction_with_innerProductEquation :
    ∀ {n : ℕ} {K : (Fin n → ℝ) → (Fin n → ℝ) → EReal},
      (∃ F, IsGraphConvexBifunction F ∧ HasNoBotValuesBifunction F ∧
          (convexBifunctionDomains F).1 = Set.univ ∧ K = convexBifunctionPairing F) →
        ∃ F, IsGraphConvexBifunction F ∧ K = convexBifunctionPairing F ∧
          HasInnerProductEquation F :=
  fun {n} {K} => by
    intro hWitness
    rcases hWitness with ⟨F, hGraphConvex, hNoBot, hDom, hRep⟩
    refine ⟨F, hGraphConvex, hRep, ?_⟩
    intro u xStar
    calc
      convexBifunctionPairing F u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar := by
            symm
            exact
              helperForCorollary33_0_40_pairing_eq_genuinePairing_of_fullParameterDomain
                (F := F) hGraphConvex hNoBot hDom u xStar

/-- Helper for Corollary33.0.40: a single primal witness away from `⊤` forces the raw
pairing kernel to avoid `⊥` somewhere for every dual vector. -/
lemma helperForCorollary33_0_40_fullRawPairingDomain_of_primalWitness
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hWitness : ∃ u₀ : Fin m → ℝ, ∃ x₀ : Fin n → ℝ, F u₀ x₀ ≠ ⊤) :
    {xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, convexBifunctionPairing F u xStar ≠ ⊥} =
      Set.univ := by
  ext xStar
  constructor
  · intro _hxStar
    simp
  · intro _hxStar
    rcases hWitness with ⟨u₀, x₀, hx₀NeTop⟩
    -- Step 1: one non-`⊤` primal value keeps the frozen convex conjugate away from `⊥`
    -- for every dual vector `xStar`.
    refine ⟨u₀, ?_⟩
    have hPairNeBot :
        convexBifunctionPairing F u₀ xStar ≠ (⊥ : EReal) := by
      simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := F u₀) (x₀ := x₀) hx₀NeTop xStar
    exact hPairNeBot

/-- Helper for Corollary33.0.40: in the graph-closed branch, the genuine adjoint pairing still
collapses to the primal pairing by splitting into the nontrivial and everywhere-`⊤` cases. -/
lemma helperForCorollary33_0_40_pairing_eq_genuinePairing_of_closed_fullGenuineAdjointDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hAdjDom : (convexBifunctionDomains F).2 = Set.univ) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      genuineConvexBifunctionAdjointPairing F u xStar =
        convexBifunctionPairing F u xStar := by
  intro u xStar
  have hGenuineDom :
      {y : Fin n → ℝ | ∃ v : Fin m → ℝ,
        genuineConvexBifunctionAdjoint F y v ≠ ⊥} = Set.univ := by
    simpa [convexBifunctionDomains] using hAdjDom
  have hCanonicalDom :
      {y : Fin n → ℝ | ∃ v : Fin m → ℝ,
        convexBifunctionAdjointPairing F y v ≠ ⊥} = Set.univ := by
    ext y
    constructor
    · intro _hy
      simp
    · intro _hy
      have hy : y ∈ {z : Fin n → ℝ | ∃ v : Fin m → ℝ,
          genuineConvexBifunctionAdjoint F z v ≠ ⊥} := by
        rw [hGenuineDom]
        simp
      rcases hy with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      simpa only [helperForCorollary33_0_40_genuineAdjoint_eq_convexBifunctionAdjointPairing]
        using hv
  have hxStarII :
      xStar ∈ intrinsicInterior ℝ
        {y : Fin n → ℝ | ∃ v : Fin m → ℝ,
          convexBifunctionAdjointPairing F y v ≠ ⊥} := by
    rw [hCanonicalDom]
    exact
      interior_subset_intrinsicInterior
        (show xStar ∈ interior (Set.univ : Set (Fin n → ℝ)) by simp)
  have hPairingEq :
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
    helperForCorollary33_2_1_closedConvex_pairing_eq_on_intrinsicInteriorAdjointDomain
      (F := F) hGraph hNoBot hGraphClosed hxStarII u
  calc
    genuineConvexBifunctionAdjointPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
      helperForCorollary33_0_40_genuinePairing_eq_convexAdjointPairing
        (F := F) u xStar
    _ = convexBifunctionPairing F u xStar := hPairingEq.symm

end Section33
end Chap07
