/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part10

section Chap06
section Section30


/-- A convex program is normal when the convex closure of its perturbation-value function agrees
with the original value at the unperturbed point `u = 0`. -/
def IsNormalConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  convexClosure (convexProgramAssociatedWith F.1) 0 = convexProgramAssociatedWith F.1 0

/-- The dual concave program associated with a convex bifunction is normal when the concave
closure of its perturbation-value function agrees with the dual value at `x* = 0`. -/
def IsNormalDualProgramOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  concaveClosure (dualPerturbationFunctionOfConvexProgram F) 0 = dualProgramOfConvexProgram F

/-- Helper for Theorem 6.30.16: the closed improper witness from Corollary 6.30.1, packaged as
the convex-program datum used in the theorem. -/
noncomputable abbrev helperForTheorem_6_30_16_counterexampleConvexProgram :
    {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ConvexBifunction F} :=
  ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩

/-- Helper for Theorem 6.30.16: the same witness, packaged with its full closed-convex structure
so the false universal theorem can be specialized to it directly. -/
noncomputable abbrev helperForTheorem_6_30_16_counterexampleClosedConvexProgram :
    {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F} :=
  ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩

/-- Helper for Theorem 6.30.16: the closed improper witness still satisfies condition (b), since
its dual perturbation function and its concave closure both equal `⊥` at the origin. -/
lemma helperForTheorem_6_30_16_counterexample_dualProgramIsNormal :
    IsNormalDualProgramOfConvexProgram
      helperForTheorem_6_30_16_counterexampleConvexProgram := by
  -- Evaluate both sides of the dual normality identity at the witness-specific origin.
  unfold IsNormalDualProgramOfConvexProgram dualProgramOfConvexProgram
  rw [helperForCorollary_6_30_2_primalInconsistencyCounterexample_concaveClosure_dualAtZero_eq_bot]
  simpa [helperForTheorem_6_30_16_counterexampleConvexProgram] using
    (helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot
      (0 : Fin 0 → ℝ)).symm

/-- Helper for Theorem 6.30.16: the same witness falsifies condition (c), because the primal
value at `0` is `⊤` while the dual value at `0` is `⊥`. -/
lemma helperForTheorem_6_30_16_counterexample_valueEqualityFails :
    ¬ (convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        dualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram) := by
  intro hValueEquality
  have hPrimalTop :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_primalZero_eq_top
  have hDualBot :
      dualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram =
        (⊥ : EReal) := by
    -- Evaluating the dual program at `0` is enough because every dual slice is already `⊥`.
    unfold dualProgramOfConvexProgram
    simpa [helperForTheorem_6_30_16_counterexampleConvexProgram] using
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot
        (0 : Fin 0 → ℝ)
  -- Rewriting the witness-specific values reduces condition (c) to the contradiction `⊤ = ⊥`.
  rw [hPrimalTop, hDualBot] at hValueEquality
  exact top_ne_bot hValueEquality

/-- Helper for Theorem 6.30.16: the packaged closed improper witness simultaneously satisfies
condition `(b)` and falsifies condition `(c)`. -/
lemma helperForTheorem_6_30_16_counterexample_hasDualNormalityButNotValueEquality :
    IsNormalDualProgramOfConvexProgram
        helperForTheorem_6_30_16_counterexampleConvexProgram ∧
      ¬ (convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          dualProgramOfConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram) := by
  -- Collect the two witness-specific facts needed to contradict the implication `(b) → (c)`.
  constructor
  · exact helperForTheorem_6_30_16_counterexample_dualProgramIsNormal
  · exact helperForTheorem_6_30_16_counterexample_valueEqualityFails

/-- Helper for Theorem 6.30.16: for the closed improper witness, the implication `(b) → (c)`
already fails before any attempt to prove the full `List.TFAE`. -/
lemma helperForTheorem_6_30_16_counterexample_implicationBCFails :
    ¬ (IsNormalDualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram →
        convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          dualProgramOfConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram) := by
  intro hImplication
  -- Apply the claimed implication to the explicit witness normality from condition `(b)`.
  have hValueEquality :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        dualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram :=
    hImplication helperForTheorem_6_30_16_counterexample_dualProgramIsNormal
  -- The witness-specific value computation still rules out condition `(c)`.
  exact helperForTheorem_6_30_16_counterexample_valueEqualityFails hValueEquality

/-- Helper for Theorem 6.30.16: any `List.TFAE` proof for the closed improper witness would force
the impossible identity `⊤ = ⊥` by combining `(b) → (c)` with the explicit witness values. -/
lemma helperForTheorem_6_30_16_counterexample_tfaeForcesTopEqBot
    (hTFAE :
      List.TFAE
        [IsNormalConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram,
          IsNormalDualProgramOfConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram,
          convexProgramAssociatedWith
              helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
            dualProgramOfConvexProgram
              helperForTheorem_6_30_16_counterexampleConvexProgram]) :
    (⊤ : EReal) = (⊥ : EReal) := by
  -- Read the implication `(b) → (c)` from the claimed TFAE and apply it to the witness.
  have hValueEquality :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        dualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram :=
    (hTFAE.out 1 2).1 helperForTheorem_6_30_16_counterexample_dualProgramIsNormal
  have hPrimalTop :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_primalZero_eq_top
  have hDualBot :
      dualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram =
        (⊥ : EReal) := by
    -- The dual program value is already `⊥` because every dual slice equals `⊥`.
    unfold dualProgramOfConvexProgram
    simpa [helperForTheorem_6_30_16_counterexampleConvexProgram] using
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot
        (0 : Fin 0 → ℝ)
  -- Rewriting the witness values collapses the TFAE consequence to the absurd identity.
  rw [hPrimalTop, hDualBot] at hValueEquality
  exact hValueEquality

/-- Helper for Theorem 6.30.16: the closed improper witness from Corollary 6.30.1 already
refutes the claimed three-way equivalence, because its dual program is normal while the primal and
dual optimal values at `0` are `⊤` and `⊥`. -/
lemma helperForTheorem_6_30_16_counterexample_refutes_tfae :
    ¬ List.TFAE
      [IsNormalConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram,
        IsNormalDualProgramOfConvexProgram
          helperForTheorem_6_30_16_counterexampleConvexProgram,
        convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          dualProgramOfConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram] := by
  intro hTFAE
  -- Reading `(b) → (c)` from `List.TFAE.out 1 2` already contradicts the witness.
  exact helperForTheorem_6_30_16_counterexample_implicationBCFails (hTFAE.out 1 2).1

/-- Helper for Theorem 6.30.16: any universal proof of the stated TFAE theorem would already be
refuted by the closed improper witness from Corollary 6.30.1. -/
lemma helperForTheorem_6_30_16_universalTfaeClaimImpliesFalse
    (hUniversal :
      ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩,
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩,
              convexProgramAssociatedWith F.1 0 = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩]) :
    False := by
  -- Specialize the purported universal theorem to the already packaged closed improper witness.
  have hWitnessTFAE :
      List.TFAE
        [IsNormalConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram,
          IsNormalDualProgramOfConvexProgram
            helperForTheorem_6_30_16_counterexampleConvexProgram,
          convexProgramAssociatedWith
              helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
            dualProgramOfConvexProgram
              helperForTheorem_6_30_16_counterexampleConvexProgram] := by
    -- Unfolding the two witness packagings shows the universal claim specializes to the same list.
    simpa [helperForTheorem_6_30_16_counterexampleClosedConvexProgram,
      helperForTheorem_6_30_16_counterexampleConvexProgram] using
      hUniversal (m := 1) (n := 0)
        helperForTheorem_6_30_16_counterexampleClosedConvexProgram
  -- The witness-specific contradiction closes the argument immediately.
  exact helperForTheorem_6_30_16_counterexample_refutes_tfae hWitnessTFAE

/-- Helper for Theorem 6.30.16: the universal TFAE statement is false in the current
formalization, because the closed improper witness already contradicts it. -/
lemma helperForTheorem_6_30_16_targetStatementFalse :
    ¬ (∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩,
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩,
              convexProgramAssociatedWith F.1 0 = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩]) := by
  intro hUniversal
  -- The previous helper already turns any universal proof into the explicit counterexample.
  exact helperForTheorem_6_30_16_universalTfaeClaimImpliesFalse hUniversal

-- Route correction: the original closed-convex textbook statement is blocked by the explicit
-- closed-improper counterexample proved above, so the formalized positive theorem below works in
-- the closed proper regime where Corollary 6.30.2 supplies the required value identities.
-- Proof-status note: the textbook route combines Corollary 6.30.2 with the identities
-- `cl (inf F) (0) = sup F* 0` and `cl (sup F*) (0) = inf F 0` to identify all three conditions.
-- In the present formalization, the closed-improper witness above shows that the universal
-- closed-convex statement is too strong. The theorem is therefore stated in the closed proper
-- regime, where the Chapter 30 identities used in the proof are available.
/-- Theorem 6.30.16: let `F` be a closed proper convex bifunction from `ℝ^m` to `ℝ^n`, and let
`(P)` be the convex program associated with `F`. Then the following conditions are equivalent:
(a) `(P)` is normal;
(b) `(P*)` is normal;
(c) `inf F 0 = sup F* 0`, i.e. the optimal value in `(P)` equals the optimal value in `(P*)`. -/

theorem normality_tfae_for_primal_and_dual_convex_programs {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1) :
    List.TFAE
      [IsNormalConvexProgram ⟨F.1, F.2.1⟩,
        IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩,
        convexProgramAssociatedWith F.1 0 = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩] := by
  -- In the closed proper case, Corollary 6.30.2 identifies both normality conditions with the
  -- common primal-dual value equality at the origin. This is the exact textbook route.
  have hCor := corollary_6_30_2_2 (F := F)
  rcases hCor with ⟨hclP, hsup, hclD, hprimal, hweak⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hNormalP
      rw [IsNormalConvexProgram] at hNormalP
      rw [← hNormalP, hclP, hsup]
      simpa [dualProgramOfConvexProgram]
    · intro hValue
      rw [IsNormalConvexProgram]
      rw [hclP, hsup]
      calc
        sSup (Set.range fun uStar : Fin m → ℝ =>
            adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar)
            = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
                simpa [dualProgramOfConvexProgram]
        _ = convexProgramAssociatedWith F.1 0 := hValue.symm
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hNormalD
      rw [IsNormalDualProgramOfConvexProgram] at hNormalD
      rw [← hNormalD, hclD hProper]
    · intro hValue
      rw [IsNormalDualProgramOfConvexProgram]
      rw [hclD hProper]
      simpa [dualProgramOfConvexProgram] using hValue
  tfae_finish

/-- The primal convex program associated with a convex bifunction is consistent when its value at
the unperturbed parameter is not `+∞`. -/
def IsConsistentConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  convexProgramAssociatedWith F.1 0 ≠ (⊤ : EReal)

/-- The dual concave program associated with a convex bifunction is consistent when its optimal
value is not `-∞`. -/
def IsConsistentDualProgramOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  dualProgramOfConvexProgram F ≠ (⊥ : EReal)

/-- The primal convex program is strongly consistent when the origin lies in the relative interior
of the effective domain of its perturbation-value function and the unperturbed primal value is not
`+∞`. -/
def IsStronglyConsistentConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsConsistentConvexProgram F ∧
    (0 : Fin m → ℝ) ∈
      euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexProgramAssociatedWith F.1))

/-- The primal convex program is strictly consistent when the origin lies in the interior of the
effective domain of its perturbation-value function and the unperturbed primal value is not
`+∞`. -/
def IsStrictlyConsistentConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsConsistentConvexProgram F ∧
    (0 : Fin m → ℝ) ∈
      interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexProgramAssociatedWith F.1))

/-- The dual program is strongly consistent when the origin lies in the relative interior of the
effective domain `{x* | -∞ < g(x*)}` of the dual perturbation function and the dual value is not
`-∞`. -/
def IsStronglyConsistentDualProgramOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsConsistentDualProgramOfConvexProgram F ∧
    (0 : Fin n → ℝ) ∈
      euclideanRelativeInterior_fin n
        (extendedRealEffectiveDomain (dualPerturbationFunctionOfConvexProgram F))

/-- The dual program is strictly consistent when the origin lies in the interior of the effective
domain `{x* | -∞ < g(x*)}` of the dual perturbation function and the dual value is not `-∞`. -/
def IsStrictlyConsistentDualProgramOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsConsistentDualProgramOfConvexProgram F ∧
    (0 : Fin n → ℝ) ∈
      interior
        (extendedRealEffectiveDomain (dualPerturbationFunctionOfConvexProgram F))

/-- A dual vector is a Kuhn--Tucker vector for the primal convex program when the infimum of the
perturbed objective shifted by that vector is finite and equals the primal optimal value. -/
noncomputable def IsKuhnTuckerVectorForConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (uStar : Fin m → ℝ) : Prop :=
  let primalPerturbation := convexProgramAssociatedWith F.1
  let perturbationInf : EReal :=
    sInf (Set.range fun u : Fin m → ℝ => primalPerturbation u - (((u ⬝ᵥ uStar : ℝ) : EReal)))
  let bifunctionInf : EReal :=
    sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      F.1 p.1 p.2 - (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
  perturbationInf = bifunctionInf ∧ perturbationInf ≠ ⊤ ∧ perturbationInf ≠ ⊥ ∧
    perturbationInf = primalPerturbation 0

/-- The primal optimal value is finite when the unperturbed convex program value is neither
`+∞` nor `-∞`. -/
def HasFinitePrimalOptimalValueOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsFiniteEReal (convexProgramAssociatedWith F.1 0)

/-- The dual optimal value is finite when the dual program value is neither `+∞` nor `-∞`. -/
def HasFiniteDualOptimalValueOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  IsFiniteEReal (dualProgramOfConvexProgram F)

/-- The primal `α`-sublevel set consists of the points `x` with `F(0, x) ≤ α`. -/
def primalSublevelSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) (α : ℝ) :
    Set (Fin n → ℝ) :=
  sublevelSetEReal (F.1 0) α

/-- The dual `β`-superlevel set consists of the multipliers `u*` with `F*(0, u*) ≥ β`. -/
def dualSuperlevelSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) (β : ℝ) :
    Set (Fin m → ℝ) :=
  {uStar | (β : EReal) ≤ adjointOfConvexBifunction F 0 uStar}

/-- The optimal solution set of the primal convex program is the minimum set of the unperturbed
objective slice `x ↦ F(0, x)`. -/
def primalOptimalSolutionSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    Set (Fin n → ℝ) :=
  minimumSetEReal (F.1 0)

/-- The optimal solution set of the dual program consists of the multipliers `u*` attaining the
dual value `sup_{u*} F*(0, u*)`. -/
def dualOptimalSolutionSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    Set (Fin m → ℝ) :=
  {uStar | adjointOfConvexBifunction F 0 uStar = dualProgramOfConvexProgram F}

/-- The primal convex program has a unique optimal solution when its optimal solution set is a
singleton. -/
def HasUniquePrimalOptimalSolutionOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  ∃ x : Fin n → ℝ, primalOptimalSolutionSetOfConvexProgram F = ({x} : Set (Fin n → ℝ))

/-- The dual program has a unique optimal solution when its optimal solution set is a singleton. -/
def HasUniqueDualOptimalSolutionOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  ∃ uStar : Fin m → ℝ, dualOptimalSolutionSetOfConvexProgram F = ({uStar} : Set (Fin m → ℝ))

/-- The primal optimal solution set is nonempty and bounded. -/
def HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  (primalOptimalSolutionSetOfConvexProgram F).Nonempty ∧
    Bornology.IsBounded (primalOptimalSolutionSetOfConvexProgram F)

/-- The dual optimal solution set is nonempty and bounded. -/
def HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) : Prop :=
  (dualOptimalSolutionSetOfConvexProgram F).Nonempty ∧
    Bornology.IsBounded (dualOptimalSolutionSetOfConvexProgram F)

/-- The disjunction of conditions (a)–(j) that Rockafellar lists as sufficient for normality of a
closed convex program and its dual. -/
def SufficientForNormalityOfConvexProgramAndDual {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) : Prop :=
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  ProperConvexBifunction F.1 ∧
    (IsStronglyConsistentConvexProgram FCvx ∨
      IsStrictlyConsistentConvexProgram FCvx ∨
      IsStronglyConsistentDualProgramOfConvexProgram FCvx ∨
      IsStrictlyConsistentDualProgramOfConvexProgram FCvx ∨
      (HasFinitePrimalOptimalValueOfConvexProgram FCvx ∧
        ∃ uStar : Fin m → ℝ, IsKuhnTuckerVectorForConvexProgram FCvx uStar) ∨
      (HasFiniteDualOptimalValueOfConvexProgram FCvx ∧
        ∃ x : Fin n → ℝ, IsKuhnTuckerVectorForDualProgram FCvx x) ∨
      (PolyhedralConvexBifunction F.1 ∧ IsConsistentConvexProgram FCvx) ∨
      (PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction FCvx) ∧
        IsConsistentDualProgramOfConvexProgram FCvx) ∨
      (∃ α : ℝ, (primalSublevelSetOfConvexProgram FCvx α).Nonempty ∧
        Bornology.IsBounded (primalSublevelSetOfConvexProgram FCvx α)) ∨
      (∃ β : ℝ, (dualSuperlevelSetOfConvexProgram FCvx β).Nonempty ∧
        Bornology.IsBounded (dualSuperlevelSetOfConvexProgram FCvx β)) ∨
      HasUniquePrimalOptimalSolutionOfConvexProgram FCvx ∨
      HasNonemptyBoundedPrimalOptimalSolutionSetOfConvexProgram FCvx ∨
      HasUniqueDualOptimalSolutionOfConvexProgram FCvx ∨
      HasNonemptyBoundedDualOptimalSolutionSetOfConvexProgram FCvx)

-- Proof sketch: each listed sufficient condition implies the primal-dual value equality
-- `inf F 0 = sup F* 0`, either through interior/relative-interior criteria, existence of a
-- Kuhn--Tucker vector, polyhedral attainment, bounded level sets, or bounded/unique optimal
-- solution sets. Then apply Theorem 6.30.16 to convert this common value equality into normality
-- of both `(P)` and `(P*)`.
/-- Helper for Theorem 6.30.17: after building consistency into the strong/strict consistency
predicates, the old closed improper witness is excluded already at the dual-consistency level. -/
lemma helperForTheorem_6_30_17_counterexample_notDualConsistent :
    ¬ IsConsistentDualProgramOfConvexProgram
      helperForTheorem_6_30_16_counterexampleConvexProgram := by
  unfold IsConsistentDualProgramOfConvexProgram dualProgramOfConvexProgram
  simpa [helperForTheorem_6_30_16_counterexampleConvexProgram] using
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot
      (0 : Fin 0 → ℝ)

/-- Helper for Theorem 6.30.17: the old closed improper witness is no longer branch `(b)`-admissible
once dual strong consistency includes ordinary dual consistency. -/
lemma helperForTheorem_6_30_17_counterexample_notDualStronglyConsistent :
    ¬ IsStronglyConsistentDualProgramOfConvexProgram
      helperForTheorem_6_30_16_counterexampleConvexProgram := by
  intro h
  exact helperForTheorem_6_30_17_counterexample_notDualConsistent h.1

/-- Helper for Theorem 6.30.17: the same consistency repair also excludes the witness from the
dual strictly consistent branch. -/
lemma helperForTheorem_6_30_17_counterexample_notDualStrictlyConsistent :
    ¬ IsStrictlyConsistentDualProgramOfConvexProgram
      helperForTheorem_6_30_16_counterexampleConvexProgram := by
  intro h
  exact helperForTheorem_6_30_17_counterexample_notDualConsistent h.1

/-- Helper for Theorem 6.30.17: primal strong or strict consistency makes the primal
perturbation function agree with its convex closure at the origin, so the primal and dual values
coincide there. -/
lemma helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hCons :
      IsStronglyConsistentConvexProgram ⟨F.1, F.2.1⟩ ∨
        IsStrictlyConsistentConvexProgram ⟨F.1, F.2.1⟩) :
    convexProgramAssociatedWith F.1 0 =
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  have hpConv : ConvexFunction p := by
    -- The primal perturbation function is convex for every convex bifunction.
    simpa [p] using
      helperForTheorem_6_30_15_primalValueFunction_is_convex (F := ⟨F.1, F.2.1⟩)
  have hpConvOn : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p := by
    -- This is the `Set.univ`-restricted form needed by the closure-agreement lemmas.
    simpa [ConvexFunction, p] using hpConv
  have h0ri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
    -- Strong consistency gives relative interior directly, and strict consistency upgrades to it.
    rcases hCons with hStrong | hStrict
    · exact hStrong.2
    · exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hStrict.2
  have h0riEuclid :
      (0 : EuclideanSpace ℝ (Fin m)) ∈
        euclideanRelativeInterior m
          ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
    have hCoordSet :
        ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) =
          ((fun a : Fin m → ℝ => WithLp.toLp 2 a) ''
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
      ext y
      constructor
      · intro hy
        refine ⟨y.ofLp, hy, ?_⟩
        simp
      · rintro ⟨a, ha, rfl⟩
        simpa
    have h0riImage :
        (0 : EuclideanSpace ℝ (Fin m)) ∈
          euclideanRelativeInterior m
            (((fun a : Fin m → ℝ => WithLp.toLp 2 a) ''
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) p)) := by
      -- The finite-coordinate relative interior statement is the Euclidean one in coordinates.
      simpa using
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) p)
        (x := (0 : Fin m → ℝ))).1 h0ri
    simpa [hCoordSet] using h0riImage
  have hClosureEq :
      convexClosure p 0 = p 0 := by
    -- Closure agrees with a convex function on the relative interior of its effective domain.
    by_cases hpProper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p
    · exact
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := p) hpProper).2 0 h0riEuclid
    · have hpImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p := by
        exact ⟨hpConvOn, hpProper⟩
      exact
        convexFunctionClosure_agrees_on_ri_of_improper (f := p) hpImproper 0 h0riEuclid
  -- Rewriting the closure value through Corollary 6.30.2 gives the desired primal-dual equality.
  calc
    convexProgramAssociatedWith F.1 0 = convexClosure p 0 := hClosureEq.symm
    _ = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 :=
      helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)
    _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      simp [dualProgramOfConvexProgram]

/-- Helper for Theorem 6.30.17: the convex effective domain of the negated dual perturbation is
exactly the Chapter 30 effective domain `{x* | -∞ < g(x*)}` of the original dual perturbation. -/
lemma helperForTheorem_6_30_17_effectiveDomain_negDualPerturbation
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun xStar : Fin n → ℝ =>
          -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) =
      extendedRealEffectiveDomain
        (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) := by
  -- Unfold both domain notions and simplify `-g x < ⊤` to `⊥ < g x`.
  ext xStar
  simp [effectiveDomain_eq, extendedRealEffectiveDomain, lt_top_iff_ne_top,
    bot_lt_iff_ne_bot]

/-- Helper for Theorem 6.30.17: dual strong or strict consistency makes the dual perturbation
function agree with its concave closure at the origin, so the primal and dual values coincide
there. -/
lemma helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (_hProper : ProperConvexBifunction F.1)
    (hCons :
      IsStronglyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∨
        IsStrictlyConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) :
    convexProgramAssociatedWith F.1 0 =
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  let g : (Fin n → ℝ) → EReal := dualPerturbationFunctionOfConvexProgram FCvx
  let q : (Fin n → ℝ) → EReal := fun xStar => -g xStar
  have hDualCons : IsConsistentDualProgramOfConvexProgram FCvx := by
    -- Both dual qualification branches carry ordinary dual consistency as their first field.
    rcases hCons with hStrong | hStrict
    · exact hStrong.1
    · exact hStrict.1
  have hqConv : ConvexFunction q := by
    -- Negating the dual perturbation turns the concave side into a convex function.
    simpa [FCvx, g, q] using
      helperForCorollary_6_30_3_negDualPerturbation_is_convex (F := F)
  have hqConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
    -- The closure-agreement lemmas work with the `Set.univ`-restricted formulation.
    simpa [ConvexFunction, q] using hqConv
  have h0ri :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
    have h0riExtended :
        (0 : Fin n → ℝ) ∈
          euclideanRelativeInterior_fin n (extendedRealEffectiveDomain g) := by
      -- Strong consistency gives relative interior directly, and strict consistency upgrades to it.
      rcases hCons with hStrong | hStrict
      · exact hStrong.2
      · exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hStrict.2
    rw [helperForTheorem_6_30_17_effectiveDomain_negDualPerturbation (F := F)]
    simpa [FCvx, g, q] using h0riExtended
  have h0riEuclid :
      (0 : EuclideanSpace ℝ (Fin n)) ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
    have hCoordSet :
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) =
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
      ext y
      constructor
      · intro hy
        refine ⟨y.ofLp, hy, ?_⟩
        simp
      · rintro ⟨a, ha, rfl⟩
        simpa
    have h0riImage :
        (0 : EuclideanSpace ℝ (Fin n)) ∈
          euclideanRelativeInterior n
            (((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
      -- The finite-coordinate relative interior statement is the Euclidean one in coordinates.
      simpa using
        (mem_euclideanRelativeInterior_fin_iff
          (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)
          (x := (0 : Fin n → ℝ))).1 h0ri
    simpa [hCoordSet] using h0riImage
  have hClosureEq :
      convexClosure q 0 = q 0 := by
    -- As on the primal side, closure agreement at a relative-interior point follows in both the
    -- proper and improper convex branches.
    by_cases hqProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q
    · exact
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := q) hqProper).2 0 h0riEuclid
    · have hqImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
        exact ⟨hqConvOn, hqProper⟩
      exact
        convexFunctionClosure_agrees_on_ri_of_improper
          (f := q) hqImproper 0 h0riEuclid
  have hClosureG :
      concaveClosure g 0 = g 0 := by
    -- Translate the closure agreement for `q = -g` back to the concave closure of `g`.
    calc
      concaveClosure g 0 = -convexClosure q 0 := by
        simp [concaveClosure_eq_neg_convexClosure_neg, q, g]
      _ = -q 0 := by rw [hClosureEq]
      _ = g 0 := by simp [q, g]
  have hgNonExceptional :
      ¬ (g 0 = (⊥ : EReal) ∧ concaveClosure g 0 = (⊤ : EReal)) := by
    -- Dual consistency rules out the only exceptional pair in the limsup formula.
    intro hBad
    exact hDualCons (by simpa [FCvx, g, dualProgramOfConvexProgram] using hBad.1)
  have hgLimsup :
      concaveClosure g 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) :=
    helperForCorollary_6_30_3_concaveClosure_eq_limsup_nhds_at_zero_nonexceptional
      (g := g) hqConv hgNonExceptional
  have hNotBothInconsistent :
      ¬ (p 0 = (⊤ : EReal) ∧ dualProgramOfConvexProgram FCvx = (⊥ : EReal)) := by
    -- The same dual consistency also excludes the inconsistent primal-dual pair.
    intro hBad
    exact hDualCons hBad.2
  have hCor := corollary_6_30_2_3 (F := F) hNotBothInconsistent
  -- Combine closure agreement at the origin with Corollary 6.30.3's limsup identity.
  calc
    convexProgramAssociatedWith F.1 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) := by
      simpa [FCvx, p, g] using hCor.2.symm
    _ = concaveClosure g 0 := hgLimsup.symm
    _ = g 0 := hClosureG
    _ = dualProgramOfConvexProgram FCvx := by
      simp [FCvx, g, dualProgramOfConvexProgram]

/-- Helper for Theorem 6.30.17: once the primal value is finite, a primal Kuhn--Tucker witness
forces equality between the primal value and some dual slice, so weak duality upgrades that slice
equality to equality of the optimal values. -/
lemma helperForTheorem_6_30_17_valueEquality_of_finiteDualValue_and_dualKuhnTuckerVector
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hFinite : HasFiniteDualOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩)
    (hKT :
      ∃ x : Fin n → ℝ,
        IsKuhnTuckerVectorForDualProgram ⟨F.1, F.2.1⟩ x) :
    convexProgramAssociatedWith F.1 0 =
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  rcases hKT with ⟨x, hx⟩
  unfold IsKuhnTuckerVectorForDualProgram at hx
  dsimp only at hx
  rcases hx with ⟨hObjectiveNeTop, hObjectiveNeBot, hObjectiveEqDual⟩
  have hDualLePrimal :
      dualProgramOfConvexProgram FCvx ≤ convexProgramAssociatedWith F.1 0 := by
    -- Weak duality still bounds the dual optimum above by the primal optimum at the origin.
    simpa [FCvx, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
      concaveProgramAssociatedWith, convexProgramAssociatedWith] using
      helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  by_cases hProper : ProperConvexBifunction F.1
  · have hClosedBranch :=
      (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
        (F := FCvx)).2.2 ⟨F.2, hProper⟩
    have hObjectiveEqSlice :
        sSup (Set.range fun xStar : Fin n → ℝ =>
            (((x ⬝ᵥ xStar : ℝ) : EReal) +
              dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
          F.1 0 x := by
      -- Evaluate the Fenchel-conjugate formula at the Kuhn--Tucker witness and rewrite the
      -- conjugate back to the defining dual supremum.
      calc
        sSup (Set.range fun xStar : Fin n → ℝ =>
            (((x ⬝ᵥ xStar : ℝ) : EReal) +
              dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
            fenchelConjugate n
              (fun xStar => -(dualPerturbationFunctionOfConvexProgram FCvx xStar)) x := by
                simp [fenchelConjugate_eq_iSup, sSup_range, sub_eq_add_neg, dotProduct_comm]
        _ = F.1 0 x := by
              simpa using congrFun hClosedBranch.1 x
    have hPrimalLeDual :
        convexProgramAssociatedWith F.1 0 ≤ dualProgramOfConvexProgram FCvx := by
      -- The primal optimum is the infimum of the zero slice, so it is bounded above by the
      -- Kuhn--Tucker witness value, which already equals the dual optimum.
      calc
        convexProgramAssociatedWith F.1 0
            = sInf (Set.range fun y : Fin n → ℝ => F.1 0 y) := rfl
        _ ≤ F.1 0 x := sInf_le ⟨x, rfl⟩
        _ = sSup (Set.range fun xStar : Fin n → ℝ =>
              (((x ⬝ᵥ xStar : ℝ) : EReal) +
                dualPerturbationFunctionOfConvexProgram FCvx xStar)) := hObjectiveEqSlice.symm
        _ = dualProgramOfConvexProgram FCvx := hObjectiveEqDual
    -- The dual Kuhn--Tucker witness supplies the reverse inequality to weak duality.
    exact le_antisymm hPrimalLeDual hDualLePrimal
  · by_cases hGraphBot : ∃ u : Fin m → ℝ, ∃ y : Fin n → ℝ, F.1 u y = (⊥ : EReal)
    · rcases hGraphBot with ⟨u, y, hBot⟩
      have hDualZeroBot :
          dualPerturbationFunctionOfConvexProgram FCvx 0 = (⊥ : EReal) := by
        simpa [FCvx] using
          helperForCorollary_6_30_1_graphBot_forces_dualSlice_eq_bot
            (F := F) (u := u) (x := y) hBot (0 : Fin n → ℝ)
      have hDualBot :
          dualProgramOfConvexProgram FCvx = (⊥ : EReal) := by
        -- Evaluating the constant-`⊥` dual perturbation at the origin collapses the dual value.
        simpa [dualProgramOfConvexProgram] using hDualZeroBot
      exact False.elim (hFinite.2 hDualBot)
    · have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ y : Fin n → ℝ, F.1 u y ≠ (⊥ : EReal) := by
        intro u y hBot
        exact hGraphBot ⟨u, y, hBot⟩
      have hConstTop :
          F.1 = fun _ _ => (⊤ : EReal) :=
        helperForCorollary_6_30_1_closedNotProper_noGraphBot_eq_const_top
          (F := F) hProper hNoGraphBot
      have hDualZeroTop :
          dualPerturbationFunctionOfConvexProgram FCvx 0 = (⊤ : EReal) := by
        have hAdjTop :
            ∀ uStar : Fin m → ℝ,
              adjointOfConvexBifunction FCvx 0 uStar = (⊤ : EReal) := by
          intro uStar
          simp [FCvx, hConstTop, adjointOfConvexBifunction]
        -- Once the bifunction is constant `⊤`, every adjoint slice is also `⊤`.
        simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, hAdjTop]
      have hDualTop :
          dualProgramOfConvexProgram FCvx = (⊤ : EReal) := by
        -- The dual optimum is just the zero dual slice evaluated above.
        simpa [dualProgramOfConvexProgram] using hDualZeroTop
      exact False.elim (hFinite.1 hDualTop)

/-- Helper for Theorem 6.30.17: once the primal value is finite, a primal Kuhn--Tucker witness
forces equality between the primal value and some dual slice, so weak duality upgrades that slice
equality to equality of the optimal values. -/
lemma helperForTheorem_6_30_17_valueEquality_of_finitePrimalValue_and_primalKuhnTuckerVector
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (_hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩)
    (hKT :
      ∃ uStar : Fin m → ℝ,
        IsKuhnTuckerVectorForConvexProgram ⟨F.1, F.2.1⟩ uStar) :
    convexProgramAssociatedWith F.1 0 =
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  rcases hKT with ⟨uStar, huStar⟩
  unfold IsKuhnTuckerVectorForConvexProgram at huStar
  dsimp only at huStar
  rcases huStar with ⟨hShiftEqBifunction, _hShiftNeTop, _hShiftNeBot, hShiftEqPrimal⟩
  have hDualSliceEq :
      adjointOfConvexBifunction FCvx 0 (-uStar) =
        convexProgramAssociatedWith F.1 0 := by
    -- Unfold the dual slice at `-uStar` and rewrite it with the Kuhn--Tucker equalities.
    calc
      adjointOfConvexBifunction FCvx 0 (-uStar) =
          sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            F.1 p.1 p.2 - (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
              simp [FCvx, adjointOfConvexBifunction, sInf_range, sub_eq_add_neg, add_comm]
      _ =
          sInf (Set.range fun u : Fin m → ℝ =>
            convexProgramAssociatedWith F.1 u - (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
              exact hShiftEqBifunction.symm
      _ = convexProgramAssociatedWith F.1 0 := hShiftEqPrimal
  have hDualLePrimal :
      dualProgramOfConvexProgram FCvx ≤ convexProgramAssociatedWith F.1 0 := by
    -- Weak duality gives the universal upper bound of the dual value by the primal value.
    simpa [FCvx, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
      concaveProgramAssociatedWith, convexProgramAssociatedWith] using
      helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  have hPrimalLeDual :
      convexProgramAssociatedWith F.1 0 ≤ dualProgramOfConvexProgram FCvx := by
    -- The Kuhn--Tucker slice itself is a lower bound witness for the dual supremum.
    calc
      convexProgramAssociatedWith F.1 0 =
          adjointOfConvexBifunction FCvx 0 (-uStar) := hDualSliceEq.symm
      _ ≤ sSup (Set.range fun v : Fin m → ℝ =>
            adjointOfConvexBifunction FCvx 0 v) := by
              exact le_sSup ⟨-uStar, rfl⟩
      _ = dualProgramOfConvexProgram FCvx := by
            simp [FCvx, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
              concaveProgramAssociatedWith]
  -- Weak duality and the Kuhn--Tucker lower bound squeeze the two values together.
  exact le_antisymm hPrimalLeDual hDualLePrimal

/-- Helper for Theorem 6.30.17: finite primal value plus value equality gives both normality
identities, because the full-neighborhood closure formulas of Corollary 6.30.3 are
nonexceptional on both sides. -/
lemma helperForTheorem_6_30_17_normality_of_finiteValueEquality
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hFinite : HasFinitePrimalOptimalValueOfConvexProgram ⟨F.1, F.2.1⟩)
    (hValue :
      convexProgramAssociatedWith F.1 0 =
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  let g : (Fin n → ℝ) → EReal := dualPerturbationFunctionOfConvexProgram FCvx
  have hpFinite : IsFiniteEReal (p 0) := by
    -- This is exactly the branch `(c)` finiteness assumption.
    simpa [FCvx, p, HasFinitePrimalOptimalValueOfConvexProgram] using hFinite
  have hgFinite : IsFiniteEReal (dualProgramOfConvexProgram FCvx) := by
    -- Value equality transports primal finiteness to the dual value.
    rw [← hValue]
    exact hpFinite
  have hpConv : ConvexFunction p := by
    -- The primal perturbation function is convex, so the liminf closure formula applies.
    simpa [p] using
      helperForTheorem_6_30_15_primalValueFunction_is_convex (F := FCvx)
  have hgNegConv : ConvexFunction (fun xStar : Fin n → ℝ => -g xStar) := by
    -- Negating the dual perturbation function puts it in the convex-closure framework.
    simpa [FCvx, g] using
      helperForCorollary_6_30_3_negDualPerturbation_is_convex (F := F)
  have hNotBothInconsistent :
      ¬ (p 0 = (⊤ : EReal) ∧ dualProgramOfConvexProgram FCvx = (⊥ : EReal)) := by
    -- The primal value is finite, so the exceptional pair from Corollary 6.30.3 cannot occur.
    intro hBad
    exact hpFinite.1 hBad.1
  have hpNonExceptional :
      ¬ (p 0 = (⊤ : EReal) ∧ convexClosure p 0 = (⊥ : EReal)) := by
    -- Primal finiteness also excludes the exceptional pair for the convex-closure formula.
    intro hBad
    exact hpFinite.1 hBad.1
  have hgNonExceptional :
      ¬ (g 0 = (⊥ : EReal) ∧ concaveClosure g 0 = (⊤ : EReal)) := by
    -- The dual value is finite after rewriting by the primal-dual equality.
    intro hBad
    exact hgFinite.2 (by simpa [FCvx, g, dualProgramOfConvexProgram] using hBad.1)
  have hpLiminf :
      convexClosure p 0 = Filter.liminf p (nhds (0 : Fin m → ℝ)) :=
    helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
      (p := p) hpConv hpNonExceptional
  have hgLimsup :
      concaveClosure g 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) :=
    helperForCorollary_6_30_3_concaveClosure_eq_limsup_nhds_at_zero_nonexceptional
      (g := g) hgNegConv hgNonExceptional
  have hCor :=
    corollary_6_30_2_3 (F := F) hNotBothInconsistent
  constructor
  · -- Rewrite primal normality through the liminf formula and Corollary 6.30.3.
    unfold IsNormalConvexProgram
    calc
      convexClosure p 0 = Filter.liminf p (nhds (0 : Fin m → ℝ)) := hpLiminf
      _ = g 0 := by simpa [FCvx, g] using hCor.1
      _ = dualProgramOfConvexProgram FCvx := by
            simp [FCvx, g, dualProgramOfConvexProgram]
      _ = p 0 := hValue.symm
  · -- Rewrite dual normality through the limsup formula and the same primal-dual equality.
    unfold IsNormalDualProgramOfConvexProgram
    calc
      concaveClosure g 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) := hgLimsup
      _ = p 0 := hCor.2
      _ = dualProgramOfConvexProgram FCvx := hValue

/-- Helper for Theorem 6.30.17: dual consistency plus value equality gives both normality
identities, because the primal and dual closure formulas are nonexceptional in the full-neighborhood
version of Corollary 6.30.3. -/
lemma helperForTheorem_6_30_17_normality_of_valueEquality_and_dualConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hValue :
      convexProgramAssociatedWith F.1 0 =
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩)
    (hDualCons :
      IsConsistentDualProgramOfConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  let g : (Fin n → ℝ) → EReal := dualPerturbationFunctionOfConvexProgram FCvx
  have hpConv : ConvexFunction p := by
    -- The primal perturbation function is convex, so the liminf closure formula applies.
    simpa [p] using
      helperForTheorem_6_30_15_primalValueFunction_is_convex (F := FCvx)
  have hgNegConv : ConvexFunction (fun xStar : Fin n → ℝ => -g xStar) := by
    -- Negating the dual perturbation function puts it in the convex-closure framework.
    simpa [FCvx, g] using
      helperForCorollary_6_30_3_negDualPerturbation_is_convex (F := F)
  have hNotBothInconsistent :
      ¬ (p 0 = (⊤ : EReal) ∧ dualProgramOfConvexProgram FCvx = (⊥ : EReal)) := by
    -- Dual consistency already rules out the exceptional pair from Corollary 6.30.3.
    intro hBad
    exact hDualCons hBad.2
  have hpNonExceptional :
      ¬ (p 0 = (⊤ : EReal) ∧ convexClosure p 0 = (⊥ : EReal)) := by
    -- The primal exceptional pair would force the dual value to be `⊥`, contradicting consistency.
    intro hBad
    apply hDualCons
    calc
      dualProgramOfConvexProgram FCvx = g 0 := by
        simp [FCvx, g, dualProgramOfConvexProgram]
      _ = convexClosure p 0 := by
            exact (helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)).symm
      _ = (⊥ : EReal) := hBad.2
  have hgNonExceptional :
      ¬ (g 0 = (⊥ : EReal) ∧ concaveClosure g 0 = (⊤ : EReal)) := by
    -- Dual consistency also rules out the dual exceptional pair directly.
    intro hBad
    exact hDualCons (by simpa [FCvx, g, dualProgramOfConvexProgram] using hBad.1)
  have hpLiminf :
      convexClosure p 0 = Filter.liminf p (nhds (0 : Fin m → ℝ)) :=
    helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
      (p := p) hpConv hpNonExceptional
  have hgLimsup :
      concaveClosure g 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) :=
    helperForCorollary_6_30_3_concaveClosure_eq_limsup_nhds_at_zero_nonexceptional
      (g := g) hgNegConv hgNonExceptional
  have hCor :=
    corollary_6_30_2_3 (F := F) hNotBothInconsistent
  constructor
  · -- Rewrite primal normality through the liminf formula and Corollary 6.30.3.
    unfold IsNormalConvexProgram
    calc
      convexClosure p 0 = Filter.liminf p (nhds (0 : Fin m → ℝ)) := hpLiminf
      _ = g 0 := by simpa [FCvx, g] using hCor.1
      _ = dualProgramOfConvexProgram FCvx := by
            simp [FCvx, g, dualProgramOfConvexProgram]
      _ = p 0 := hValue.symm
  · -- Rewrite dual normality through the limsup formula and the same primal-dual equality.
    unfold IsNormalDualProgramOfConvexProgram
    calc
      concaveClosure g 0 = Filter.limsup g (nhds (0 : Fin n → ℝ)) := hgLimsup
      _ = p 0 := hCor.2
      _ = dualProgramOfConvexProgram FCvx := hValue

/-- Helper for Theorem 6.30.17: primal consistency plus primal-dual value equality already forces
both normality identities, by splitting into the proper branch and the two improper branches from
Corollary 6.30.3. -/
lemma helperForTheorem_6_30_17_normality_of_valueEquality_and_primalConsistency
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hValue :
      convexProgramAssociatedWith F.1 0 =
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩)
    (hPrimalCons :
      IsConsistentConvexProgram ⟨F.1, F.2.1⟩) :
    IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
      IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  let g : (Fin n → ℝ) → EReal := dualPerturbationFunctionOfConvexProgram FCvx
  have hNotBothInconsistent :
      ¬ (p 0 = (⊤ : EReal) ∧ dualProgramOfConvexProgram FCvx = (⊥ : EReal)) := by
    -- Primal consistency alone rules out the exceptional pair from Corollary 6.30.3.
    intro hBad
    exact hPrimalCons hBad.1
  by_cases hProper : ProperConvexBifunction F.1
  · -- In the proper branch, Theorem 6.30.16 turns value equality directly into both normalities.
    have hTFAE := normality_tfae_for_primal_and_dual_convex_programs (F := F) hProper
    constructor
    · -- Read `(c) → (a)` from the TFAE list `[a, b, c]`.
      exact (hTFAE.out 2 0).1 hValue
    · -- Read `(c) → (b)` from the same TFAE list.
      exact (hTFAE.out 2 1).1 hValue
  · by_cases hGraphBot : ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F.1 u x = (⊥ : EReal)
    · rcases
        helperForCorollary_6_30_3_nonproper_graphBot_branch
          (F := F) hProper hNotBothInconsistent hGraphBot with
        ⟨hDualConst, hPrimalBot⟩
      have hConcaveClosureBot :
          concaveClosure (fun _ : Fin n → ℝ => (⊥ : EReal)) 0 = (⊥ : EReal) := by
        -- The concave closure of the constant `⊥` function is still `⊥`.
        simpa [concaveClosure_eq_neg_convexClosure_neg] using
          congrArg Neg.neg (congrFun (convexFunctionClosure_const_top (n := n))
            (0 : Fin n → ℝ))
      have hDualZeroBot : g 0 = (⊥ : EReal) := by
        -- Evaluating the constant-`⊥` dual perturbation at the origin fixes the dual value.
        simpa [FCvx, g] using congrFun hDualConst (0 : Fin n → ℝ)
      have hConcaveClosureDualZeroBot :
          concaveClosure g 0 = (⊥ : EReal) := by
        -- Rewriting by the constant-`⊥` description reduces the closure value to the previous fact.
        simpa [FCvx, g, hDualConst] using hConcaveClosureBot
      constructor
      · -- The primal closure identity collapses to `⊥ = ⊥` in the graph-`⊥` improper branch.
        unfold IsNormalConvexProgram
        calc
          convexClosure p 0 = g 0 := by
            simpa [FCvx, p, g] using
              helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)
          _ = (⊥ : EReal) := hDualZeroBot
          _ = p 0 := by simpa [p] using hPrimalBot.symm
      · -- The dual perturbation is constant `⊥`, so its closure and value at `0` both equal `⊥`.
        unfold IsNormalDualProgramOfConvexProgram
        calc
          concaveClosure g 0 = (⊥ : EReal) := hConcaveClosureDualZeroBot
          _ = dualProgramOfConvexProgram FCvx := by
            simp [FCvx, dualProgramOfConvexProgram, hDualConst]
    · have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal) := by
        intro u x hBot
        exact hGraphBot ⟨u, x, hBot⟩
      have hConstTop :
          F.1 = fun _ _ => (⊤ : EReal) :=
        helperForCorollary_6_30_3_nonproper_noGraphBot_branch
          (F := F) hProper hNoGraphBot
      -- The remaining closed-improper branch is the constant-`⊤` bifunction, contradicting
      -- primal consistency at `u = 0`.
      exfalso
      apply hPrimalCons
      simp [convexProgramAssociatedWith, hConstTop]
end Section30
end Chap06
