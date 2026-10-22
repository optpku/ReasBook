/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part5

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart6 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}


/-- Helper for Text 34.1.4: at the primal origin, the translated-tilted genuine adjoint pairing
is just the original genuine adjoint pairing with the dual variable shifted by the tilt. -/


lemma helperForText_34_1_4_translatedTilted_genuineAdjointPairingAtZero_eq_shifted
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) (yStar : Fin n → ℝ) :
    genuineConvexBifunctionAdjointPairing
        (translatedTiltedBifunction F u xStar) (0 : Fin m → ℝ) yStar =
      genuineConvexBifunctionAdjointPairing F u (xStar + yStar) := by
  -- Unfold both pairings as infima over the same dual variable.
  rw [genuineConvexBifunctionAdjointPairing, genuineConvexBifunctionAdjointPairing,
    sInf_range, sInf_range]
  -- Rewrite the translated adjoint integrand through the explicit shift formula.
  congr with vStar
  rw [genuineConvexBifunctionAdjoint_translatedTiltedBifunction
    (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)]
  -- Expand the negated translated adjoint term back to the original pairing integrand.
  have hNegSub :
      -(genuineConvexBifunctionAdjoint F (xStar + yStar) vStar - ↑(u ⬝ᵥ vStar)) =
        -genuineConvexBifunctionAdjoint F (xStar + yStar) vStar + ↑(u ⬝ᵥ vStar) := by
    exact
      EReal.neg_sub
        (x := genuineConvexBifunctionAdjoint F (xStar + yStar) vStar)
        (y := ↑(u ⬝ᵥ vStar))
        (Or.inr (by simp))
        (Or.inr (by simp))
  rw [sub_eq_add_neg]
  rw [hNegSub]
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Helper for Text 34.1.4: the translated dual perturbation family is the negative of the
shifted genuine adjoint pairing. -/
lemma helperForText_34_1_4_translatedDualPerturbation_eq_neg_shiftedGenuineAdjointPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar)) :
    dualPerturbationFunctionOfConvexProgram
        ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ =
      fun yStar : Fin n → ℝ =>
        -genuineConvexBifunctionAdjointPairing F u (xStar + yStar) := by
  funext yStar
  -- Rewrite the dual perturbation as the supremum of the translated genuine adjoint section.
  calc
    dualPerturbationFunctionOfConvexProgram
        ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ yStar
        =
      sSup
        (Set.range fun vStar : Fin m → ℝ =>
          genuineConvexBifunctionAdjoint
            (translatedTiltedBifunction F u xStar) yStar vStar) := by
            simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith,
              adjointOfConvexBifunction, genuineConvexBifunctionAdjoint]
    -- Convert that supremum to the negative translated pairing at the primal origin.
    _ =
      -genuineConvexBifunctionAdjointPairing
        (translatedTiltedBifunction F u xStar) (0 : Fin m → ℝ) yStar := by
          exact
            helperForLemma33_0_35_genuineAdjointZeroSection_sSup_eq_negPairingAtZero
              (G := translatedTiltedBifunction F u xStar) (xStar := yStar)
    -- Finally identify the translated origin pairing with the shifted original pairing.
    _ = -genuineConvexBifunctionAdjointPairing F u (xStar + yStar) := by
          rw [helperForText_34_1_4_translatedTilted_genuineAdjointPairingAtZero_eq_shifted
            (F := F) (u := u) (xStar := xStar) (yStar := yStar)]

/-- Helper for Text 34.1.4: the translated primal perturbation family is the negative of the
shifted lower-closure pairing section attached to the fixed witness. -/
lemma helperForText_34_1_4_translatedPrimalValue_eq_neg_shiftedLowerClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) =
      fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar := by
  funext v
  have hLowerValue :
      lowerClosureConcaveConvex K h (u + v) xStar =
        convexBifunctionPairing F (u + v) xStar := by
    simpa using congrArg (fun G => G (u + v) xStar) hLowerRep
  -- Rewrite the translated primal value to the shifted negative pairing section.
  calc
    convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) v
        = -convexBifunctionPairing F (u + v) xStar := by
            simpa [translatedTiltedBifunction] using
              congrFun
                (helperForLemma33_0_22_translatedTiltedPrimalValue_eq_shiftedNegPairingSection
                  (F := F) u xStar)
                v
    -- Then replace the pairing by the represented lower closure at the shifted point.
    _ = -lowerClosureConcaveConvex K h (u + v) xStar := by
          rw [← hLowerValue]

/-- Helper for Text 34.1.4: after rewriting the translated Chapter 6 package through the fixed
lower self-representation, both the primal `liminf` and the dual `limsup` are statements about
the negative shifted lower-closure sections. -/
lemma helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    Filter.liminf
        (fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar)
        (nhds (0 : Fin m → ℝ)) =
        -lowerClosureConcaveConvex K h u xStar ∧
      Filter.limsup
          (fun yStar : Fin n → ℝ =>
            -lowerClosureConcaveConvex K h u (xStar + yStar))
          (nhds (0 : Fin n → ℝ)) =
        -lowerClosureConcaveConvex K h u xStar := by
  have hCor :
      Filter.liminf
          (convexProgramAssociatedWith (translatedTiltedBifunction F u xStar))
          (nhds (0 : Fin m → ℝ)) =
          dualPerturbationFunctionOfConvexProgram
            ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ 0 ∧
        Filter.limsup
            (dualPerturbationFunctionOfConvexProgram
              ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩)
            (nhds (0 : Fin n → ℝ)) =
          convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 := by
    -- Reuse the translated Chapter 6 package before replacing the two perturbation families.
    exact
      helperForText_34_1_4_translatedTilted_liminf_limsup_package
        (F := F) u xStar hGClosed hEqualValues
  have hPrimalEq :
      convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) =
        fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar :=
    helperForText_34_1_4_translatedPrimalValue_eq_neg_shiftedLowerClosure
      (K := K) (h := h) (F := F) u xStar hLowerRep
  have hDualEq :
      dualPerturbationFunctionOfConvexProgram
          ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ =
        fun yStar : Fin n → ℝ =>
          -lowerClosureConcaveConvex K h u (xStar + yStar) := by
    -- Rewrite the translated dual perturbation through the shifted genuine adjoint pairing,
    -- then apply the fixed lower self-representation.
    funext yStar
    rw [helperForText_34_1_4_translatedDualPerturbation_eq_neg_shiftedGenuineAdjointPairing
      (F := F) u xStar hGClosed]
    rw [hGenuineSelfRep u (xStar + yStar)]
  constructor
  · -- Replace the translated primal perturbation and dual origin value by the shifted
    -- lower-closure sections.
    calc
      Filter.liminf (fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar)
          (nhds (0 : Fin m → ℝ))
          =
        Filter.liminf
          (convexProgramAssociatedWith (translatedTiltedBifunction F u xStar))
          (nhds (0 : Fin m → ℝ)) := by
            rw [hPrimalEq]
      _ =
        dualPerturbationFunctionOfConvexProgram
          ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ 0 := hCor.1
      _ = -lowerClosureConcaveConvex K h u xStar := by
            simpa using congrFun hDualEq (0 : Fin n → ℝ)
  · -- Apply the same replacement on the dual `limsup` side and evaluate the translated
    -- primal section at the origin.
    calc
      Filter.limsup
          (fun yStar : Fin n → ℝ =>
            -lowerClosureConcaveConvex K h u (xStar + yStar))
          (nhds (0 : Fin n → ℝ))
          =
        Filter.limsup
          (dualPerturbationFunctionOfConvexProgram
            ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩)
          (nhds (0 : Fin n → ℝ)) := by
            rw [hDualEq]
      _ = convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 := hCor.2
      _ = -lowerClosureConcaveConvex K h u xStar := by
            simpa using congrFun hPrimalEq (0 : Fin m → ℝ)

/-- Helper for Text 34.1.4: the translated primal section of `underline(K)` has convex closure
at the origin equal to the negated lower-closure value at `(u, xStar)`. -/
lemma helperForText_34_1_4_shiftedPrimalSection_convexClosureAtZero
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    convexClosure
        (fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar)
        (0 : Fin m → ℝ) =
      -lowerClosureConcaveConvex K h u xStar := by
  let p : (Fin m → ℝ) → EReal := fun v => -lowerClosureConcaveConvex K h (u + v) xStar
  have hLiminf :
      Filter.liminf p (nhds (0 : Fin m → ℝ)) =
        -lowerClosureConcaveConvex K h u xStar := by
    -- Reuse the translated `liminf` package after naming the shifted first-variable section.
    simpa [p] using
      (helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hGClosed hLowerRep hGenuineSelfRep
        hEqualValues).1
  have hConvex : ConvexFunction p := by
    have hPrimalEq :
        convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) = p :=
      helperForText_34_1_4_translatedPrimalValue_eq_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hLowerRep
    -- The shifted section is exactly the primal value function of the translated program, and
    -- Chapter 6 already proves that such primal value functions are convex.
    simpa [hPrimalEq] using
      helperForTheorem_6_30_15_primalValueFunction_is_convex
        (F := ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩)
  have hNonExceptional :
      ¬ (p (0 : Fin m → ℝ) = (⊤ : EReal) ∧
          convexClosure p (0 : Fin m → ℝ) = (⊥ : EReal)) := by
    -- The base value of the shifted primal section is never `⊤` because `underline(K)` has no
    -- `⊥` values.
    intro hBad
    have hValueBot :
        lowerClosureConcaveConvex K h u xStar = (⊥ : EReal) := by
      simpa [p] using hBad.1
    exact hLowerNoBot u xStar hValueBot
  -- Corollary 6.30.3 converts the translated `liminf` identity into the desired closure
  -- identity at the origin.
  calc
    convexClosure p (0 : Fin m → ℝ) =
        Filter.liminf p (nhds (0 : Fin m → ℝ)) := by
          exact
            helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
              (p := p) hConvex hNonExceptional
    _ = -lowerClosureConcaveConvex K h u xStar := hLiminf

/-- Helper for Text 34.1.4: every second-variable section of `underline(K)` is already fixed by
the raw one-variable Section 33 convex closure operator. -/
lemma helperForText_34_1_4_lowerClosure_secondSection_isFunctionConvexClosed
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (u : Fin m → ℝ) :
    IsFunctionConvexClosed (fun y : Fin n → ℝ => lowerClosureConcaveConvex K h u y) := by
  have hLowerClosedSecond :
      IsConvexClosedInSecond (lowerClosureConcaveConvex K h) := by
    -- The outer `cl₂` in `underline(K) = cl₂ (cl₁ K)` already fixes every second-variable
    -- section, independently of the unresolved first-variable transport.
    rcases helperForText_34_0_1_outerClosure_fixedPoint_forms K h with ⟨hSecondFixed, -⟩
    simpa [IsConvexClosedInSecond, partialClosure₂] using hSecondFixed.symm
  unfold IsFunctionConvexClosed
  funext y
  -- Evaluate the second-variable fixed-point identity at the chosen first-variable section.
  have hPoint := congrArg (fun G => G u y) hLowerClosedSecond
  simpa [convexClosureInSecond, functionConvexClosure] using hPoint

/-- Helper for Text 34.1.4: the shifted dual section of `underline(K)` is already concave-closed
at the origin, so its concave closure returns the negated lower-closure value at `(u, xStar)`. -/
lemma helperForText_34_1_4_shiftedDualSection_concaveClosureAtZero
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (_hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (_hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (_hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (_hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    concaveClosure
        (fun yStar : Fin n → ℝ => -lowerClosureConcaveConvex K h u (xStar + yStar))
        (0 : Fin n → ℝ) =
      -lowerClosureConcaveConvex K h u xStar := by
  let f : (Fin n → ℝ) → EReal := fun y => lowerClosureConcaveConvex K h u y
  let q : (Fin n → ℝ) → EReal := fun y => lowerClosureConcaveConvex K h u (xStar + y)
  have hqLsc : LowerSemicontinuous q := by
    have hfLsc : LowerSemicontinuous f := by
      -- The unshifted second-variable section is already fixed by the raw convex closure, and
      -- that closure is automatically lower semicontinuous.
      change LowerSemicontinuous (fun y : Fin n → ℝ => lowerClosureConcaveConvex K h u y)
      rw [helperForText_34_1_4_lowerClosure_secondSection_isFunctionConvexClosed K h u]
      exact helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
    -- Lower semicontinuity is stable under translating the section by the fixed vector `xStar`.
    exact hfLsc.comp_continuous (continuous_const.add continuous_id)
  have hqClosed :
      q = functionConvexClosure q :=
    -- A lower semicontinuous section is already fixed by the raw Section 33 closure operator.
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hqLsc
  have hqNoBot : ∀ y, q y ≠ (⊥ : EReal) := by
    intro y hbot
    -- `underline(K)` never attains `⊥`, so neither does its shifted second-variable section.
    exact hLowerNoBot u (xStar + y) hbot
  have hqClosureEq : convexClosure q (0 : Fin n → ℝ) = q 0 := by
    -- The shifted section has no `⊥` values, so Chapter 6's convex closure agrees with the raw
    -- Section 33 closure, which has just been shown to fix `q`.
    calc
      convexClosure q (0 : Fin n → ℝ) = convexFunctionClosure q 0 := by
        rfl
      _ = functionConvexClosure q 0 := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (f := q) hqNoBot]
      _ = q 0 := by
        exact (congrArg (fun g => g 0) hqClosed).symm
  -- Rewrite the concave closure as the negative convex closure of the shifted lower-closure
  -- section, then use the closure fixed-point proved above.
  calc
    concaveClosure
        (fun yStar : Fin n → ℝ => -lowerClosureConcaveConvex K h u (xStar + yStar))
        (0 : Fin n → ℝ)
        = -convexClosure q (0 : Fin n → ℝ) := by
            simp [concaveClosure_eq_neg_convexClosure_neg, q]
    _ = -q 0 := by
          rw [hqClosureEq]
    _ = -lowerClosureConcaveConvex K h u xStar := by
          simp [q]

/-- Helper for Text 34.1.4: the neighborhood `limsup` of the shifted dual lower-closure section
can be written as an infimum of suprema over closed balls centered at `0`. -/
lemma helperForText_34_1_4_shiftedDualSection_limsup_eq_iInf_iSup_closedBall
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    Filter.limsup
        (fun yStar : Fin n → ℝ =>
          -lowerClosureConcaveConvex K h u (xStar + yStar))
        (nhds (0 : Fin n → ℝ))
      =
    (⨅ (ρ : {ρ : ℝ // 0 < ρ}),
      ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
        -lowerClosureConcaveConvex K h u (xStar + yStar.1)) := by
  let g : (Fin n → ℝ) → EReal :=
    fun yStar : Fin n → ℝ => -lowerClosureConcaveConvex K h u (xStar + yStar)
  -- Rewrite the neighborhood `limsup` through the closed-ball basis at the origin.
  calc
    Filter.limsup g (nhds (0 : Fin n → ℝ))
        =
      (⨅ (ρ : ℝ), ⨅ (_ : 0 < ρ),
        ⨆ yStar ∈ Metric.closedBall (0 : Fin n → ℝ) ρ, g yStar) := by
          simpa using
            (Filter.HasBasis.limsup_eq_iInf_iSup
              (u := g) (Metric.nhds_basis_closedBall (x := (0 : Fin n → ℝ))))
    _ =
      (⨅ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}), g yStar.1) := by
          simp [Metric.closedBall, dist_eq_norm, iInf_subtype, iSup_subtype]
    _ =
      (⨅ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1)) := by
            simp [g]

/-- Helper for Text 34.1.4: capping the positive closed-ball radii by a fixed `δ` only enlarges
the shifted dual envelope, so negating still yields a lower bound for `underline(K)(u, xStar)`.
-/
lemma helperForText_34_1_4_negRestrictedDualClosedBallEnvelope_le_lowerClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (δ : {δ : ℝ // 0 < δ})
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
      ≤
    lowerClosureConcaveConvex K h u xStar := by
  let g : (Fin n → ℝ) → EReal :=
    fun yStar : Fin n → ℝ => -lowerClosureConcaveConvex K h u (xStar + yStar)
  have hLimsupEq :
      Filter.limsup g (nhds (0 : Fin n → ℝ)) =
        -lowerClosureConcaveConvex K h u xStar := by
    -- Reuse the translated-tilted package already rewritten through the fixed witness.
    simpa [g] using
      (helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hGClosed hLowerRep hGenuineSelfRep
        hEqualValues).2
  have hLimsupLeRestricted :
      Filter.limsup g (nhds (0 : Fin n → ℝ)) ≤
        (⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
          ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}), g yStar.1) := by
    -- Any radius with `0 < ρ < δ` is one of the positive closed-ball basis neighborhoods.
    rw [helperForText_34_1_4_shiftedDualSection_limsup_eq_iInf_iSup_closedBall
      (K := K) (h := h) (u := u) (xStar := xStar)]
    refine le_iInf ?_
    intro ρ
    exact iInf_le_of_le ⟨ρ.1, ρ.2.1⟩ le_rfl
  -- Negating the restricted upper envelope gives the promised lower bound for the base value.
  have hNegLe :
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
          ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}), g yStar.1)
        ≤
      -Filter.limsup g (nhds (0 : Fin n → ℝ)) := by
    exact (EReal.neg_le_neg_iff).2 hLimsupLeRestricted
  calc
    -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
        =
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}), g yStar.1) := by
          simp [g]
    _ ≤ -Filter.limsup g (nhds (0 : Fin n → ℝ)) := hNegLe
    _ = lowerClosureConcaveConvex K h u xStar := by
          rw [hLimsupEq]
          simp

/-- Helper for Text 34.1.4: the neighborhood `liminf` of the shifted primal lower-closure
section can be written as a supremum of infima over closed balls centered at `0`. -/
lemma helperForText_34_1_4_shiftedPrimalSection_liminf_eq_iSup_iInf_closedBall
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    Filter.liminf
        (fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar)
        (nhds (0 : Fin m → ℝ))
      =
    (⨆ (ρ : {ρ : ℝ // 0 < ρ}),
      ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
        -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
  let p : (Fin m → ℝ) → EReal :=
    fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar
  -- Rewrite the neighborhood `liminf` through the closed-ball basis at the origin.
  calc
    Filter.liminf p (nhds (0 : Fin m → ℝ))
        =
      (⨆ (ρ : ℝ), ⨆ (_ : 0 < ρ),
        ⨅ v ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, p v) := by
          simpa using
            (Filter.HasBasis.liminf_eq_iSup_iInf
              (u := p) (Metric.nhds_basis_closedBall (x := (0 : Fin m → ℝ))))
    _ =
      (⨆ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}), p v.1) := by
          simp [Metric.closedBall, dist_eq_norm, iInf_subtype, iSup_subtype]
    _ =
      (⨆ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
            simp [p]

/-- Helper for Text 34.1.4: for a monotone positive-radius family, restricting the outer
infimum to radii below a fixed cap does not change its value.

The small-radius family `{ρ | 0 < ρ ∧ ρ < δ}` is cofinal among all positive radii, so the
infimum over all positive radii can be recovered by capping at any fixed `δ > 0`. -/
lemma helperForText_34_1_4_iInf_restrictedPositiveRadii_eq_iInf_of_monotone
    (δ : {δ : ℝ // 0 < δ})
    (g : {ρ : ℝ // 0 < ρ} → EReal)
    (hMono : Monotone g) :
    (⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}), g ⟨ρ.1, ρ.2.1⟩) =
      (⨅ (ρ : {ρ : ℝ // 0 < ρ}), g ρ) := by
  apply le_antisymm
  · -- Cap an arbitrary positive radius by `δ / 2`; monotonicity then compares the
    -- corresponding family values.
    refine le_iInf ?_
    intro ρ
    have hHalfPos : 0 < δ.1 / 2 := by
      linarith [δ.2]
    have hHalfLt : δ.1 / 2 < δ.1 := by
      linarith [δ.2]
    let ρcap : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1} :=
      ⟨min ρ.1 (δ.1 / 2), lt_min ρ.2 hHalfPos,
        lt_of_le_of_lt (min_le_right _ _) hHalfLt⟩
    have hCapLe : ρcap.1 ≤ ρ.1 := min_le_left _ _
    exact le_trans (iInf_le_of_le ρcap le_rfl) (hMono hCapLe)
  · -- The unrestricted infimum is below every capped term, hence below the capped infimum.
    refine le_iInf ?_
    intro ρ
    exact iInf_le_of_le ⟨ρ.1, ρ.2.1⟩ le_rfl

/-- Helper for Text 34.1.4: capping the positive closed-ball radii by a fixed `ε` only shrinks
the shifted primal envelope, so negating still leaves an upper bound for
`underline(K)(u, xStar)`. -/
lemma helperForText_34_1_4_lowerClosure_le_negRestrictedPrimalClosedBallEnvelope
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε})
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    lowerClosureConcaveConvex K h u xStar
      ≤
    -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
  let p : (Fin m → ℝ) → EReal :=
    fun v : Fin m → ℝ => -lowerClosureConcaveConvex K h (u + v) xStar
  have hLiminfEq :
      Filter.liminf p (nhds (0 : Fin m → ℝ)) =
        -lowerClosureConcaveConvex K h u xStar := by
    -- Reuse the translated-tilted package already rewritten through the fixed witness.
    simpa [p] using
      (helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hGClosed hLowerRep hGenuineSelfRep
        hEqualValues).1
  have hRestrictedLeLiminf :
      (⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}), p v.1)
        ≤
      Filter.liminf p (nhds (0 : Fin m → ℝ)) := by
    -- Every radius with `0 < ρ < ε` contributes one of the closed-ball basis lower bounds.
    rw [helperForText_34_1_4_shiftedPrimalSection_liminf_eq_iSup_iInf_closedBall
      (K := K) (h := h) (u := u) (xStar := xStar)]
    refine iSup_le ?_
    intro ρ
    exact le_iSup_of_le ⟨ρ.1, ρ.2.1⟩ le_rfl
  have hNegLe :
      -Filter.liminf p (nhds (0 : Fin m → ℝ))
        ≤
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}), p v.1) := by
    exact (EReal.neg_le_neg_iff).2 hRestrictedLeLiminf
  calc
    lowerClosureConcaveConvex K h u xStar = -Filter.liminf p (nhds (0 : Fin m → ℝ)) := by
      rw [hLiminfEq]
      simp
    _ ≤
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}), p v.1) := hNegLe
    _ =
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
          ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
            -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
              simp [p]

/-- Helper for Text 34.1.4: for an antitone positive-radius family, restricting the outer
supremum to radii below a fixed cap does not change its value.

As with the corresponding infimum lemma, the radii below a fixed positive cap form a cofinal
subfamily among all positive radii. -/
lemma helperForText_34_1_4_iSup_restrictedPositiveRadii_eq_iSup_of_antitone
    (ε : {ε : ℝ // 0 < ε})
    (g : {ρ : ℝ // 0 < ρ} → EReal)
    (hAnti : Antitone g) :
    (⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}), g ⟨ρ.1, ρ.2.1⟩) =
      (⨆ (ρ : {ρ : ℝ // 0 < ρ}), g ρ) := by
  apply le_antisymm
  · -- The capped supremum is taken over a smaller index set, so it lies below the unrestricted
    -- one.
    refine iSup_le ?_
    intro ρ
    exact le_iSup_of_le ⟨ρ.1, ρ.2.1⟩ le_rfl
  · -- Any positive radius can again be capped by `ε / 2`; antitonicity compares the family
    -- value at the original radius with the capped one.
    refine iSup_le ?_
    intro ρ
    have hHalfPos : 0 < ε.1 / 2 := by
      linarith [ε.2]
    have hHalfLt : ε.1 / 2 < ε.1 := by
      linarith [ε.2]
    let ρcap : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1} :=
      ⟨min ρ.1 (ε.1 / 2), lt_min ρ.2 hHalfPos,
        lt_of_le_of_lt (min_le_right _ _) hHalfLt⟩
    have hCapLe : ρcap.1 ≤ ρ.1 := min_le_left _ _
    exact le_trans (hAnti hCapLe) (le_iSup_of_le ρcap le_rfl)

/-- Helper for Text 34.1.4: once the translated-tilted package is available, capping the shifted
dual closed-ball envelope at any positive radius `δ` still gives exactly
`underline(K)(u, xStar)`.

This sharpens the earlier one-sided inequality by using the closed-ball neighborhood formula for
`limsup` together with the cofinality of the capped radius family. -/
lemma helperForText_34_1_4_negRestrictedDualClosedBallEnvelope_eq_lowerClosure
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (δ : {δ : ℝ // 0 < δ})
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
      =
    lowerClosureConcaveConvex K h u xStar := by
  let g : {ρ : ℝ // 0 < ρ} → EReal :=
    fun ρ =>
      ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
        -lowerClosureConcaveConvex K h u (xStar + yStar.1)
  have hMono : Monotone g := by
    intro ρ ρ' hρ
    -- Enlarging the closed ball in the dual variable only enlarges the corresponding
    -- supremum.
    refine iSup_le ?_
    intro yStar
    exact le_iSup_of_le ⟨yStar.1, le_trans yStar.2 hρ⟩ le_rfl
  have hRestrEq :
      (⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
        =
      (⨅ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1)) := by
    -- Cofinality of the capped radius family collapses the restricted infimum back to the full
    -- one.
    simpa [g] using
      helperForText_34_1_4_iInf_restrictedPositiveRadii_eq_iInf_of_monotone
        (δ := δ) g hMono
  have hLimsupEq :
      Filter.limsup
          (fun yStar : Fin n → ℝ =>
            -lowerClosureConcaveConvex K h u (xStar + yStar))
          (nhds (0 : Fin n → ℝ))
        =
      -lowerClosureConcaveConvex K h u xStar := by
    -- Reuse the translated-tilted `limsup` identity already rewritten through the fixed
    -- witness.
    simpa using
      (helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hGClosed hLowerRep hGenuineSelfRep
        hEqualValues).2
  calc
    -(⨅ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < δ.1}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1))
        =
      -(⨅ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨆ (yStar : {yStar : Fin n → ℝ // ‖yStar‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h u (xStar + yStar.1)) := by
            rw [hRestrEq]
    _ =
      -Filter.limsup
        (fun yStar : Fin n → ℝ =>
          -lowerClosureConcaveConvex K h u (xStar + yStar))
        (nhds (0 : Fin n → ℝ)) := by
          rw [← helperForText_34_1_4_shiftedDualSection_limsup_eq_iInf_iSup_closedBall
            (K := K) (h := h) (u := u) (xStar := xStar)]
    _ = lowerClosureConcaveConvex K h u xStar := by
          rw [hLimsupEq]
          simp

/-- Helper for Text 34.1.4: symmetrically, once the translated-tilted package is available,
capping the shifted primal closed-ball envelope at any positive radius `ε` still gives exactly
`underline(K)(u, xStar)`.

This is the `liminf` analogue of the previous dual-envelope identity. -/
lemma helperForText_34_1_4_lowerClosure_eq_negRestrictedPrimalClosedBallEnvelope
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε})
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    lowerClosureConcaveConvex K h u xStar
      =
    -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
  let g : {ρ : ℝ // 0 < ρ} → EReal :=
    fun ρ =>
      ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
        -lowerClosureConcaveConvex K h (u + v.1) xStar
  have hAnti : Antitone g := by
    intro ρ ρ' hρ
    -- Enlarging the closed ball in the primal variable only shrinks the corresponding
    -- infimum.
    refine le_iInf ?_
    intro v
    exact iInf_le_of_le ⟨v.1, le_trans v.2 hρ⟩ le_rfl
  have hRestrEq :
      (⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar)
        =
      (⨆ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
    -- Cofinality of the capped radius family collapses the restricted supremum back to the full
    -- one.
    simpa [g] using
      helperForText_34_1_4_iSup_restrictedPositiveRadii_eq_iSup_of_antitone
        (ε := ε) g hAnti
  have hLiminfEq :
      Filter.liminf
          (fun v : Fin m → ℝ =>
            -lowerClosureConcaveConvex K h (u + v) xStar)
          (nhds (0 : Fin m → ℝ))
        =
      -lowerClosureConcaveConvex K h u xStar := by
    -- Reuse the translated-tilted `liminf` identity already rewritten through the fixed
    -- witness.
    simpa using
      (helperForText_34_1_4_translatedTilted_liminf_limsup_as_neg_shiftedLowerClosure
        (K := K) (h := h) (F := F) u xStar hGClosed hLowerRep hGenuineSelfRep
        hEqualValues).1
  calc
    lowerClosureConcaveConvex K h u xStar
        =
      -Filter.liminf
        (fun v : Fin m → ℝ =>
          -lowerClosureConcaveConvex K h (u + v) xStar)
        (nhds (0 : Fin m → ℝ)) := by
          rw [hLiminfEq]
          simp
    _ =
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
            rw [helperForText_34_1_4_shiftedPrimalSection_liminf_eq_iSup_iInf_closedBall
              (K := K) (h := h) (u := u) (xStar := xStar)]
    _ =
      -(⨆ (ρ : {ρ : ℝ // 0 < ρ ∧ ρ < ε.1}),
        ⨅ (v : {v : Fin m → ℝ // ‖v‖ ≤ ρ.1}),
          -lowerClosureConcaveConvex K h (u + v.1) xStar) := by
            rw [hRestrEq]

/-- Helper for Text 34.1.4: at fixed radii, the open-ball minimax envelope of `K` dominates the
corresponding first partial-closure envelope. -/
lemma helperForText_34_1_4_restrictedFirstClosureEnvelope_le_leftOpenBallEnvelope
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      partialClosure₁ K u z.1)
      ≤
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
  -- Compare pointwise in `z`: `cl₁ K` is the infimum over all radii, so a fixed radius `ε`
  -- yields an upper bound for the corresponding section value.
  refine iInf_mono ?_
  intro z
  exact iInf_le_of_le ε le_rfl

/-- Helper for Text 34.1.4: at fixed radii, the open-ball maximin envelope of `K` lies below the
corresponding second partial-closure envelope. -/
lemma helperForText_34_1_4_rightOpenBallEnvelope_le_restrictedSecondClosureEnvelope
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      partialClosure₂ K w.1 xStar) := by
  -- Compare pointwise in `w`: the fixed-radius infimum is one candidate in the supremum
  -- defining `cl₂ K`.
  refine iSup_mono ?_
  intro w
  exact le_iSup_of_le δ le_rfl

/-- Helper for Text 34.1.4: the left open-ball minimax envelope of `K` dominates the same
restricted envelope built from the mixed upper closure `cl₁ cl₂ K`. -/
lemma helperForText_34_1_4_restrictedUpperMixedClosureEnvelope_le_leftOpenBallEnvelope
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      partialClosure₁ (partialClosure₂ K) u z.1)
      ≤
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
  -- First compare the mixed upper-closure envelope with the corresponding envelope for `cl₂ K`.
  have hUpperToSecond :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        partialClosure₁ (partialClosure₂ K) u z.1)
        ≤
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), partialClosure₂ K w.1 z.1) :=
    helperForText_34_1_4_restrictedFirstClosureEnvelope_le_leftOpenBallEnvelope
      (K := partialClosure₂ K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
  have hSecondToBase :
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), partialClosure₂ K w.1 z.1)
        ≤
      (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1) := by
    -- Use the pointwise estimate `cl₂ K ≤ K` inside the fixed-radius envelope.
    refine iInf_mono ?_
    intro z
    refine iSup_mono ?_
    intro w
    exact helperForText_34_0_1_partialClosure₂_le K w.1 z.1
  exact le_trans hUpperToSecond hSecondToBase

/-- Helper for Text 34.1.4: the right open-ball maximin envelope of `K` lies below the same
restricted envelope built from the mixed lower closure `cl₂ cl₁ K`. -/
lemma helperForText_34_1_4_rightOpenBallEnvelope_le_restrictedLowerMixedClosureEnvelope
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
      partialClosure₂ (partialClosure₁ K) w.1 xStar) := by
  have hBaseToFirst :
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1)
        ≤
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), partialClosure₁ K w.1 z.1) := by
    -- Use the pointwise estimate `K ≤ cl₁ K` inside the fixed-radius envelope.
    refine iSup_mono ?_
    intro w
    refine iInf_mono ?_
    intro z
    exact helperForText_34_0_1_le_partialClosure₁ K w.1 z.1
  have hFirstToLower :
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), partialClosure₁ K w.1 z.1)
        ≤
      (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        partialClosure₂ (partialClosure₁ K) w.1 xStar) :=
    helperForText_34_1_4_rightOpenBallEnvelope_le_restrictedSecondClosureEnvelope
      (K := partialClosure₁ K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
  exact le_trans hBaseToFirst hFirstToLower

/-- Helper for Text 34.1.4: the naive left transport
`fixed-ball minimax ≤ underline(K)(u, xStar)` is false in general.

For the one-dimensional coordinate kernel `K(w, z) = w₀`, the local minimax value on the unit
open balls around the origin is at least `1/2`, while the mixed lower closure at the origin is
still `0`. This rules out any replan that merely retries the current left-sandwich statement. -/
lemma helperForText_34_1_4_coordKernel_naiveLeftTransport_false :
    ¬ ((⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ < 1}),
          ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < 1}),
            helperForText_34_1_4_coordKernel w.1 z.1)
        ≤
      partialClosure₂ (partialClosure₁ helperForText_34_1_4_coordKernel) 0 0) := by
  have hLowerZero :
      partialClosure₂ (partialClosure₁ helperForText_34_1_4_coordKernel) 0 0 = 0 := by
    rw [partialClosure₂, convexClosureInSecond]
    have hFirstZero :
        ∀ z : Fin 1 → ℝ, partialClosure₁ helperForText_34_1_4_coordKernel 0 z = 0 := by
      intro z
      -- The one-variable section `w ↦ w₀` is continuous, so Section 33 fixes its concave
      -- closure exactly.
      let g : (Fin 1 → ℝ) → EReal := fun w => (((w 0 : ℝ)) : EReal)
      have hNegLsc : LowerSemicontinuous (fun w : Fin 1 → ℝ => -g w) := by
        have hcont : Continuous (fun w : Fin 1 → ℝ => (-((w 0 : ℝ)) : EReal)) := by
          exact continuous_coe_real_ereal.comp ((continuous_apply 0).neg)
        simpa [g] using hcont.lowerSemicontinuous
      have hNegClosed : IsFunctionConvexClosed (fun w : Fin 1 → ℝ => -g w) := by
        exact helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
      have hClosed : IsFunctionConcaveClosed g :=
        (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed).2
          hNegClosed
      have hPoint := congrArg (fun f => f 0) hClosed
      simpa [g, IsFunctionConcaveClosed, functionConcaveClosure, partialClosure₁,
        concaveClosureInFirst, helperForText_34_1_4_coordKernel] using hPoint.symm
    -- The second partial closure now acts on the constant zero section in the second variable.
    apply le_antisymm
    · refine iSup_le ?_
      intro ε
      refine iInf_le_of_le ⟨0, by simpa using ε.2⟩ ?_
      simpa using (hFirstZero (0 : Fin 1 → ℝ)).le
    · refine le_iSup_of_le ⟨1, by norm_num⟩ ?_
      refine le_iInf ?_
      intro z
      simpa [hFirstZero z.1]
  have hLeftHalf :
      (((1 / 2 : ℝ)) : EReal) ≤
        (⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ < 1}),
            ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < 1}),
              helperForText_34_1_4_coordKernel w.1 z.1) := by
    -- The local minimax value is at least `1/2`, witnessed by the constant vector `w = 1/2`.
    refine le_iInf ?_
    intro z
    refine le_iSup_of_le ⟨(fun _ => (1 / 2 : ℝ)),
      by
        simpa [Pi.norm_def, Real.norm_eq_abs] using
          (show |(1 / 2 : ℝ)| < 1 by norm_num)⟩ ?_
    simp [helperForText_34_1_4_coordKernel]
  intro hBad
  have : (((1 / 2 : ℝ)) : EReal) ≤ (0 : EReal) := by
    calc
      (((1 / 2 : ℝ)) : EReal) ≤
          (⨅ (z : {z : Fin 1 → ℝ // ‖z - (0 : Fin 1 → ℝ)‖ < 1}),
              ⨆ (w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < 1}),
                helperForText_34_1_4_coordKernel w.1 z.1) := hLeftHalf
      _ ≤ partialClosure₂ (partialClosure₁ helperForText_34_1_4_coordKernel) 0 0 := hBad
      _ = 0 := hLowerZero
  norm_num at this

end SaddleAmbient

end Section34
end Chap07
