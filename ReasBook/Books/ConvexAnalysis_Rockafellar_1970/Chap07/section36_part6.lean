/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part5

section Chap07
section Section36

-- Proof sketch: (→) Use the representation of a Lagrangian as an infimum of affine perturbations
-- of a closed convex bifunction `F` to obtain concavity/convexity and hypograph/epigraph
-- closedness. (←) Starting from an upper closed concave-convex `L`, reconstruct a closed convex
-- bifunction `F` (via an adjoint/conjugate construction in the sense of Theorem 33.3) whose
-- associated convex program has Lagrangian `L`.
-- Route correction: the remaining forward lower-closedness step is not just technically blocked.
-- Agent C traced it to Chapter 2's `projection_epigraph_not_closed_example`, which shows that the
-- current section-local hypothesis `IsEpigraphClosedConvexBifunction` is too weak to force the
-- fixed-`uStar` Lagrangian sections to be lower closed.
/-- Theorem 36.5, with the necessary projection-closedness qualification: for a bifunction `L`
that is lower closed in its second variable, being the Lagrangian of a convex program associated
with a closed convex bifunction is equivalent to being upper closed concave-convex, provided its
fixed-`x` concave slices are proper. -/
theorem lagrangian_iff_upperClosedConcaveConvex
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hLowerL : IsLowerClosedInSecond (m := m) (n := n) L)
    (hProperSlices :
      ∀ x : Fin n → ℝ, ProperConcaveERealFunction (fun uStar : Fin m → ℝ => L uStar x)) :
    (∃ (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
      (hFconv : IsEpigraphConvexBifunction (m := m) (n := n) F),
        IsEpigraphClosedConvexBifunction (m := m) (n := n) F ∧
          L = bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩) ↔
      IsUpperClosedConcaveConvex (m := m) (n := n) L :=
  by
    constructor
    · rintro ⟨F, hFconv, hFclosed, rfl⟩
      have hOrientation :
          IsConcaveInFirst (m := m) (n := n)
              (bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩) ∧
            IsConvexInSecond (m := m) (n := n)
              (bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩) :=
        -- The easy half of the theorem is the orientation statement already proved above.
        helperForTheorem_36_5_lagrangian_has_concaveConvex_orientation
          (F := ⟨F, hFconv⟩)
      refine ⟨?_, ?_, hOrientation.1, hOrientation.2⟩
      · intro x
        have hSectionClosed :
            IsFunctionConcaveClosed
              (fun uStar : Fin m → ℝ =>
                bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x) := by
          -- Rewrite the fixed-`x` slice as the textbook infimal pairing and use that every such
          -- pairing is automatically concave-closed.
          have hSectionEq :
              (fun uStar : Fin m → ℝ =>
                bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x) =
                fun uStar : Fin m → ℝ => infPairing (m := m) uStar (bifunctionInverse F x) := by
            funext uStar
            simp [bifunctionLagrangian, infPairing, bifunctionInverse]
          rw [hSectionEq]
          exact helperForTheorem_36_5_infPairing_isFunctionConcaveClosed (g := bifunctionInverse F x)
        have hNegClosed :
            IsFunctionConvexClosed
              (fun uStar : Fin m → ℝ =>
                -bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x) :=
          (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
            (g := fun uStar : Fin m → ℝ =>
              bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x)).1 hSectionClosed
        have hNegLsc :
            LowerSemicontinuous
              (fun uStar : Fin m → ℝ =>
                -bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x) := by
          -- The raw Section 33 closure is always lower semicontinuous, so a fixed point inherits
          -- lower semicontinuity directly.
          have hClosureLsc :
              LowerSemicontinuous
                (functionConvexClosure
                  (fun uStar : Fin m → ℝ =>
                    -bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x)) :=
            helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
              (f := fun uStar : Fin m → ℝ =>
                -bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x)
          exact hNegClosed ▸ hClosureLsc
        have hUpperSc :
            UpperSemicontinuous
              (fun uStar : Fin m → ℝ =>
                bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x) :=
          (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
            (g := fun uStar : Fin m → ℝ =>
              bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ uStar x)).2 hNegLsc
        have hClosedERealHypograph :
            IsClosed
              {p : (Fin m → ℝ) × EReal |
                p.2 ≤ bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ p.1 x} :=
          hUpperSc.IsClosed_hypograph
        let realToERealHeight : (Fin m → ℝ) × ℝ → (Fin m → ℝ) × EReal :=
          fun p => (p.1, (p.2 : EReal))
        have hRealToERealHeightCont : Continuous realToERealHeight := by
          -- Replace the real height by its `EReal` coercion to compare the two hypographs.
          simpa [realToERealHeight] using
            continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
        have hPreimage :
            realToERealHeight ⁻¹'
                {p : (Fin m → ℝ) × EReal |
                  p.2 ≤ bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ p.1 x} =
              {p : (Fin m → ℝ) × ℝ |
                (p.2 : EReal) ≤ bifunctionLagrangian (m := m) (n := n) ⟨F, hFconv⟩ p.1 x} := by
          ext p
          simp [realToERealHeight]
        -- Pull the `EReal`-height hypograph back along the continuous height coercion.
        rw [← hPreimage]
        exact hClosedERealHypograph.preimage hRealToERealHeightCont
      · exact hLowerL
    · intro hL
      rcases hL with ⟨hUpper, hLower, hConc, hConv⟩
      let Frec : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
        fun u x =>
          iSup fun uStar : Fin m → ℝ =>
            L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))
      have hFrec :
          IsEpigraphConvexBifunction (m := m) (n := n) Frec ∧
            IsEpigraphClosedConvexBifunction (m := m) (n := n) Frec :=
        helperForTheorem_36_5_reconstructedBifunction_closed_convex
          (L := L) hLower hConv
      have hClosedSlices :
          ∀ x : Fin n → ℝ, ClosedConcaveFunction (fun uStar : Fin m → ℝ => L uStar x) :=
        helperForTheorem_36_5_sliceClosedConcave_of_upperClosedConcave
          (L := L) hUpper hConc
      have hRecover :
          ∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
            bifunctionLagrangian (m := m) (n := n) ⟨Frec, hFrec.1⟩ uStar x = L uStar x :=
        helperForTheorem_36_5_reconstructedBifunction_recovers_L
          (L := L) hClosedSlices hProperSlices hFrec.1
      -- The pointwise conjugate reconstruction supplies the desired closed convex witness.
      refine ⟨Frec, hFrec.1, hFrec.2, ?_⟩
      funext uStar x
      exact (hRecover uStar x).symm

/-- The bifunction `F : ℝ^m → ℝ^n → [-∞, +∞]` obtained from a Lagrangian-type bifunction
`L(uStar, x)` by taking the pointwise Fenchel conjugate in the first variable:
`(F u) x = sup_{uStar} (L(uStar, x) - ⟨uStar, u⟩)`. -/
noncomputable def lagrangianToBifunction {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x =>
    iSup fun uStar : Fin m → ℝ =>
      L uStar x + (-((finDot (n := m) uStar u : ℝ) : EReal))

/-- The primal objective function associated to a Lagrangian-type bifunction `L(uStar, x)`:
`φ(x) = sup_{uStar} L(uStar, x)`. -/
noncomputable def primalObjectiveOfLagrangian {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => iSup fun uStar : Fin m → ℝ => L uStar x

/-- The dual objective function associated to a Lagrangian-type bifunction `L(uStar, x)`:
`ψ(uStar) = inf_x L(uStar, x)`. -/
noncomputable def dualObjectiveOfLagrangian {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : (Fin m → ℝ) → EReal :=
  fun uStar => iInf fun x : Fin n → ℝ => L uStar x

/-- Helper for Proposition 36.5.1: the dimension-one constant-zero kernel is an admissible
upper closed concave-convex Lagrangian. -/
lemma helperForProposition_36_5_1_constantZero_isUpperClosedConcaveConvex :
    IsUpperClosedConcaveConvex (m := 1) (n := 1) (fun _ _ => (0 : EReal)) := by
  constructor
  · intro _
    -- Each fixed-`x` hypograph is the closed lower half-space `t ≤ 0`.
    simpa using (isClosed_le continuous_snd continuous_const)
  constructor
  · intro _
    -- Each fixed-`uStar` epigraph is the closed upper half-space `0 ≤ t`.
    simpa using (isClosed_le continuous_const continuous_snd)
  constructor
  · intro _
    -- Concavity reduces to convexity of the scalar lower half-space.
    rintro p hp q hq a b ha hb hab
    change (((a • p + b • q).2 : ℝ) : EReal) ≤ (0 : EReal)
    exact_mod_cast (show (a • p + b • q).2 ≤ 0 by
      have hp' : p.2 ≤ 0 := by
        simpa using hp
      have hq' : q.2 ≤ 0 := by
        simpa using hq
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
        add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hp')
          (mul_nonpos_of_nonneg_of_nonpos hb hq'))
  · intro _
    -- Convexity reduces to convexity of the scalar upper half-space.
    rintro p hp q hq a b ha hb hab
    change (0 : EReal) ≤ (((a • p + b • q).2 : ℝ) : EReal)
    exact_mod_cast (show 0 ≤ (a • p + b • q).2 by
      have hp' : 0 ≤ p.2 := by
        simpa using hp
      have hq' : 0 ≤ q.2 := by
        simpa using hq
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
        add_nonneg (mul_nonneg ha hp') (mul_nonneg hb hq'))

/-- Helper for Proposition 36.5.1: the bifunction reconstructed from the dimension-one
constant-zero kernel takes the value `⊤` at the witness `(u, x) = (1, 0)`. -/
lemma helperForProposition_36_5_1_constantZero_lagrangianAtOneZero_eq_top :
    lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (⊤ : EReal) :=
  by
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    let uStarWitness : Fin 1 → ℝ := fun _ => -(y + 1)
    have hEval : ((y + 1 : ℝ) : EReal) ≤
        lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal))
          helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector := by
      -- Choosing `uStar = -(y + 1)` realizes the affine value `y + 1`.
      refine le_trans ?_ (le_iSup_of_le uStarWitness le_rfl)
      change ((y + 1 : ℝ) : EReal) ≤
        ((0 : EReal) + (-((finDot (n := 1) uStarWitness helperForProposition_36_4_3_oneVector : ℝ) : EReal)))
      have hDot :
          finDot (n := 1) uStarWitness helperForProposition_36_4_3_oneVector = -(y + 1) := by
        simp [uStarWitness, finDot, dotProduct, helperForProposition_36_4_3_oneVector]
      -- Rewriting the dot product turns the witness value into the explicit real number `y + 1`.
      refine le_of_eq ?_
      rw [hDot]
      rw [show -(((-(y + 1) : ℝ) : EReal)) = ((y + 1 : ℝ) : EReal) by
        rw [EReal.coe_neg]
        simp]
      simp
    -- Since the supremum dominates every real `y + 1`, it dominates `y` strictly.
    have hlt : (y : EReal) < ((y + 1 : ℝ) : EReal) := by
      exact_mod_cast (show y < y + 1 by linarith)
    exact lt_of_lt_of_le hlt hEval

/-- Helper for Proposition 36.5.1: after applying the repository's swap-and-negate inverse, the
same dimension-one witness yields the value `⊥`. -/
lemma helperForProposition_36_5_1_constantZero_inverseAtZeroOne_eq_bot :
    bifunctionInverse
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
      (⊥ : EReal) := by
  -- The inverse just negates the already computed `⊤` value.
  simp [bifunctionInverse, helperForProposition_36_5_1_constantZero_lagrangianAtOneZero_eq_top]

/-- Helper for Proposition 36.5.1: the displayed clause-(2) right-hand side evaluates to `0` at
the witness `xStar = 0`, `uStar = 1` for the dimension-one constant-zero kernel. -/
lemma helperForProposition_36_5_1_constantZero_displayedRightSideAtZeroOne_eq_zero :
    (iInf fun x : Fin 1 → ℝ =>
      (fun _ _ => (0 : EReal)) helperForProposition_36_4_3_oneVector x +
        (-((finDot (n := 1) helperForProposition_36_4_3_zeroVector x : ℝ) : EReal))) =
      (0 : EReal) := by
  -- Every term in this infimum is exactly `0`.
  simp [finDot, dotProduct, helperForProposition_36_4_3_zeroVector]

/-- Helper for Proposition 36.5.1: the textbook adjoint operator from `section36_part4`
does realize the displayed clause-(2) value `0` at the constant-zero witness
`xStar = 0`, `uStar = 1`. -/
lemma helperForProposition_36_5_1_constantZero_textbookAdjointAtZeroOne_eq_zero :
    bifunctionEuclideanAdjointTextbook
        (m := 1) (n := 1)
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
      (0 : EReal) := by
  rw [bifunctionEuclideanAdjointTextbook]
  apply le_antisymm
  · -- Choosing the outer witness `u = 0` makes the affine penalty vanish and realizes the value `0`.
    refine iInf_le_of_le helperForProposition_36_4_3_zeroVector ?_
    simp [lagrangianToBifunction, finDot, dotProduct, helperForProposition_36_4_3_oneVector,
      helperForProposition_36_4_3_zeroVector]
  · refine le_iInf ?_
    intro u
    -- The constant dual witness `uStar = -1` forces the inner supremum to dominate `u 0`.
    have hInnerLower : ((u 0 : ℝ) : EReal) ≤
        iSup (fun uStar : Fin 1 → ℝ =>
          (-((finDot (n := 1) uStar u : ℝ) : EReal))) := by
      let uStarWitness : Fin 1 → ℝ := fun _ => (-1 : ℝ)
      refine le_trans ?_ (le_iSup_of_le uStarWitness le_rfl)
      change ((u 0 : ℝ) : EReal) ≤ (-((finDot (n := 1) uStarWitness u : ℝ) : EReal))
      simp [uStarWitness, finDot, dotProduct]
    have hSumLower : (0 : EReal) ≤
        (-((u 0 : ℝ) : EReal)) + iSup (fun uStar : Fin 1 → ℝ =>
          (-((finDot (n := 1) uStar u : ℝ) : EReal))) := by
      have hAdd := add_le_add_left hInnerLower (-((u 0 : ℝ) : EReal))
      have hCancel : (-((u 0 : ℝ) : EReal)) + ((u 0 : ℝ) : EReal) = (0 : EReal) := by
        exact_mod_cast (show -(u 0 : ℝ) + u 0 = 0 by ring)
      have hRewritten :
          (-((u 0 : ℝ) : EReal)) + ((u 0 : ℝ) : EReal) ≤
            (-((u 0 : ℝ) : EReal)) + iSup (fun uStar : Fin 1 → ℝ =>
              (-((finDot (n := 1) uStar u : ℝ) : EReal))) := by
        simpa [add_comm, add_left_comm, add_assoc] using hAdd
      rw [hCancel] at hRewritten
      exact hRewritten
    -- After unfolding `lagrangianToBifunction`, the same lower bound holds for every `x`.
    refine le_iInf ?_
    intro x
    simpa [lagrangianToBifunction, finDot, dotProduct, helperForProposition_36_4_3_zeroVector,
      helperForProposition_36_4_3_oneVector] using hSumLower

/-- Helper for Proposition 36.5.1: at the explicit constant-zero witness, the displayed
clause-(2) right-hand side agrees with the textbook Euclidean adjoint from `section36_part4`. -/
lemma helperForProposition_36_5_1_constantZero_displayedRightSide_eq_textbookAdjointAtWitness :
    (iInf fun x : Fin 1 → ℝ =>
      (fun _ _ => (0 : EReal)) helperForProposition_36_4_3_oneVector x +
        (-((finDot (n := 1) helperForProposition_36_4_3_zeroVector x : ℝ) : EReal))) =
      bifunctionEuclideanAdjointTextbook
        (m := 1) (n := 1)
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector := by
  -- Both sides of the witness identity have already been computed explicitly as `0`.
  rw [helperForProposition_36_5_1_constantZero_displayedRightSideAtZeroOne_eq_zero,
    helperForProposition_36_5_1_constantZero_textbookAdjointAtZeroOne_eq_zero]

/-- Helper for Proposition 36.5.1: at the constant-zero witness, the theorem's current left-hand
side `bifunctionInverse F xStar uStar` differs from the textbook adjoint
`bifunctionEuclideanAdjointTextbook F xStar uStar`. -/
lemma helperForProposition_36_5_1_constantZero_inverseDiffersFromTextbookAdjointAtWitness :
    bifunctionInverse
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector ≠
      bifunctionEuclideanAdjointTextbook
        (m := 1) (n := 1)
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector := by
  -- The repository inverse gives `⊥`, while the textbook adjoint gives the displayed value `0`.
  rw [helperForProposition_36_5_1_constantZero_inverseAtZeroOne_eq_bot,
    helperForProposition_36_5_1_constantZero_textbookAdjointAtZeroOne_eq_zero]
  simp

/-- Helper for Proposition 36.5.1: any hypothetical clause-(2) equality at the explicit
dimension-one constant-zero witness would identify the repository inverse with the textbook
adjoint at that witness. -/
lemma helperForProposition_36_5_1_constantZero_clauseTwoAtWitness_forces_inverse_eq_textbookAdjoint
    (hClauseTwoAtWitness :
      bifunctionInverse
          (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
        (iInf fun x : Fin 1 → ℝ =>
          (fun _ _ => (0 : EReal)) helperForProposition_36_4_3_oneVector x +
            (-((finDot (n := 1) helperForProposition_36_4_3_zeroVector x : ℝ) : EReal)))) :
    bifunctionInverse
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
      bifunctionEuclideanAdjointTextbook
        (m := 1) (n := 1)
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector := by
  -- Replacing the displayed right-hand side by the textbook adjoint isolates the operator mismatch.
  exact hClauseTwoAtWitness.trans
    helperForProposition_36_5_1_constantZero_displayedRightSide_eq_textbookAdjointAtWitness

/-- Helper for Proposition 36.5.1: any hypothetical clause-(2) equality at the explicit
dimension-one constant-zero witness forces the impossible identity `⊥ = 0`. -/
lemma helperForProposition_36_5_1_constantZero_clauseTwoAtWitness_forces_bot_eq_zero
    (hClauseTwoAtWitness :
      bifunctionInverse
          (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
        (iInf fun x : Fin 1 → ℝ =>
          (fun _ _ => (0 : EReal)) helperForProposition_36_4_3_oneVector x +
            (-((finDot (n := 1) helperForProposition_36_4_3_zeroVector x : ℝ) : EReal)))) :
    (⊥ : EReal) = (0 : EReal) := by
  -- Evaluate the assumed witness identity using the explicit formulas for both sides.
  rw [helperForProposition_36_5_1_constantZero_inverseAtZeroOne_eq_bot,
    helperForProposition_36_5_1_constantZero_displayedRightSideAtZeroOne_eq_zero]
    at hClauseTwoAtWitness
  exact hClauseTwoAtWitness

/-- Helper for Proposition 36.5.1: the clause-(2) identity already fails at the explicit witness
`xStar = 0`, `uStar = 1` for the dimension-one constant-zero kernel. -/
lemma helperForProposition_36_5_1_constantZero_clauseTwoFailsAtZeroOne :
    bifunctionInverse
        (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector ≠
      (iInf fun x : Fin 1 → ℝ =>
        (fun _ _ => (0 : EReal)) helperForProposition_36_4_3_oneVector x +
          (-((finDot (n := 1) helperForProposition_36_4_3_zeroVector x : ℝ) : EReal))) := by
  intro hClauseTwoAtWitness
  -- Route correction: the clean contradiction is the operator mismatch, not just the endpoint values.
  have hInverseEqTextbook :
      bifunctionInverse
          (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
        bifunctionEuclideanAdjointTextbook
          (m := 1) (n := 1)
          (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector :=
    helperForProposition_36_5_1_constantZero_clauseTwoAtWitness_forces_inverse_eq_textbookAdjoint
      hClauseTwoAtWitness
  exact helperForProposition_36_5_1_constantZero_inverseDiffersFromTextbookAdjointAtWitness
    hInverseEqTextbook

/-- Helper for Proposition 36.5.1: the specialized clause-(2) cannot hold universally in the
dimension-one constant-zero example. -/
lemma helperForProposition_36_5_1_constantZero_forallClauseTwoFails :
    ¬ (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
      bifunctionInverse
          (lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          xStar uStar =
        iInf fun x : Fin 1 → ℝ =>
          (fun _ _ => (0 : EReal)) uStar x +
            (-((finDot (n := 1) xStar x : ℝ) : EReal))) := by
  intro hAdjoint
  -- Specialize the universal clause to the explicit witness where the two sides disagree.
  exact helperForProposition_36_5_1_constantZero_clauseTwoFailsAtZeroOne
    (hAdjoint helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector)

/-- Helper for Proposition 36.5.1: the specialized conclusion for the dimension-one constant-zero
kernel is empty because clause (2) equates `⊥` with `0` at the explicit witness. -/
lemma helperForProposition_36_5_1_constantZero_conclusion_empty :
    ¬ (let F := lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      IsEpigraphConvexBifunction (m := 1) (n := 1) F ∧
        IsEpigraphClosedConvexBifunction (m := 1) (n := 1) F ∧
        (∀ x : Fin 1 → ℝ,
          primalObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) x =
            iSup fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
        (minimaxValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) (fun _ _ => (0 : EReal)) =
          iInf fun x : Fin 1 → ℝ =>
            primalObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) x) ∧
        (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
          bifunctionInverse F xStar uStar =
            iInf fun x : Fin 1 → ℝ =>
              (fun _ _ => (0 : EReal)) uStar x +
                (-((finDot (n := 1) xStar x : ℝ) : EReal))) ∧
        (∀ uStar : Fin 1 → ℝ,
          dualObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) uStar =
            iInf fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
        (maximinValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) (fun _ _ => (0 : EReal)) =
          iSup fun uStar : Fin 1 → ℝ =>
            dualObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) uStar)) := by
  intro h
  dsimp only at h
  rcases h with ⟨_, _, _, _, hAdjoint, _, _⟩
  -- Extract clause (2) from the conjunction and apply the explicit witness refutation.
  exact helperForProposition_36_5_1_constantZero_forallClauseTwoFails hAdjoint

/-- Helper for Proposition 36.5.1: the current theorem statement has a concrete counterexample,
namely the dimension-one constant-zero Lagrangian. -/
lemma helperForProposition_36_5_1_hasCounterexample :
    ∃ L : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsUpperClosedConcaveConvex (m := 1) (n := 1) L ∧
      ¬ (let F := lagrangianToBifunction (m := 1) (n := 1) L
        IsEpigraphConvexBifunction (m := 1) (n := 1) F ∧
          IsEpigraphClosedConvexBifunction (m := 1) (n := 1) F ∧
          (∀ x : Fin 1 → ℝ,
            primalObjectiveOfLagrangian (m := 1) (n := 1) L x =
              iSup fun uStar : Fin 1 → ℝ => L uStar x) ∧
          (minimaxValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) L =
            iInf fun x : Fin 1 → ℝ =>
              primalObjectiveOfLagrangian (m := 1) (n := 1) L x) ∧
          (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
            bifunctionInverse F xStar uStar =
              iInf fun x : Fin 1 → ℝ =>
                L uStar x + (-((finDot (n := 1) xStar x : ℝ) : EReal))) ∧
          (∀ uStar : Fin 1 → ℝ,
            dualObjectiveOfLagrangian (m := 1) (n := 1) L uStar =
              iInf fun x : Fin 1 → ℝ => L uStar x) ∧
          (maximinValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) L =
            iSup fun uStar : Fin 1 → ℝ =>
              dualObjectiveOfLagrangian (m := 1) (n := 1) L uStar)) := by
  refine ⟨fun _ _ => (0 : EReal), ?_, ?_⟩
  · -- The constant-zero kernel satisfies the standing upper-closed concave-convex hypothesis.
    exact helperForProposition_36_5_1_constantZero_isUpperClosedConcaveConvex
  · -- The explicit witness computation already rules out the theorem conclusion in this case.
    simpa using helperForProposition_36_5_1_constantZero_conclusion_empty

/-- Helper for Proposition 36.5.1: any hypothetical proof of the full generic theorem statement
specializes to the explicit dimension-one constant-zero witness. -/
lemma helperForProposition_36_5_1_specializeGenericStatementToConstantZero
    (hGeneric : ∀ {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
        (_hL : IsUpperClosedConcaveConvex (m := m) (n := n) L),
        let F := lagrangianToBifunction (m := m) (n := n) L
        IsEpigraphConvexBifunction (m := m) (n := n) F ∧
          IsEpigraphClosedConvexBifunction (m := m) (n := n) F ∧
          (∀ x : Fin n → ℝ,
            primalObjectiveOfLagrangian (m := m) (n := n) L x =
              iSup fun uStar : Fin m → ℝ => L uStar x) ∧
          (minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
            iInf fun x : Fin n → ℝ =>
              primalObjectiveOfLagrangian (m := m) (n := n) L x) ∧
          (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
            bifunctionInverse F xStar uStar =
              iInf fun x : Fin n → ℝ =>
                L uStar x + (-((finDot (n := n) xStar x : ℝ) : EReal))) ∧
          (∀ uStar : Fin m → ℝ,
            dualObjectiveOfLagrangian (m := m) (n := n) L uStar =
              iInf fun x : Fin n → ℝ => L uStar x) ∧
          (maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
            iSup fun uStar : Fin m → ℝ =>
              dualObjectiveOfLagrangian (m := m) (n := n) L uStar)) :
    let F := lagrangianToBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal))
    IsEpigraphConvexBifunction (m := 1) (n := 1) F ∧
      IsEpigraphClosedConvexBifunction (m := 1) (n := 1) F ∧
      (∀ x : Fin 1 → ℝ,
        primalObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) x =
          iSup fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      (minimaxValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) (fun _ _ => (0 : EReal)) =
        iInf fun x : Fin 1 → ℝ =>
          primalObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) x) ∧
      (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
        bifunctionInverse F xStar uStar =
          iInf fun x : Fin 1 → ℝ =>
            (fun _ _ => (0 : EReal)) uStar x +
              (-((finDot (n := 1) xStar x : ℝ) : EReal))) ∧
      (∀ uStar : Fin 1 → ℝ,
        dualObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) uStar =
          iInf fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      (maximinValue (C := (Fin 1 → ℝ)) (D := (Fin 1 → ℝ)) (fun _ _ => (0 : EReal)) =
        iSup fun uStar : Fin 1 → ℝ =>
          dualObjectiveOfLagrangian (m := 1) (n := 1) (fun _ _ => (0 : EReal)) uStar) := by
  -- Specialize the hypothetical generic theorem to the explicit constant-zero witness.
  exact hGeneric (m := 1) (n := 1) (fun _ _ => (0 : EReal))
    helperForProposition_36_5_1_constantZero_isUpperClosedConcaveConvex

/-- Helper for Proposition 36.5.1: the full generic theorem statement is false, because
specializing it to the dimension-one constant-zero kernel recovers the explicit contradiction
proved above. -/
lemma helperForProposition_36_5_1_targetStatement_isFalse :
    ¬ (∀ {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
        (_hL : IsUpperClosedConcaveConvex (m := m) (n := n) L),
        let F := lagrangianToBifunction (m := m) (n := n) L
        IsEpigraphConvexBifunction (m := m) (n := n) F ∧
          IsEpigraphClosedConvexBifunction (m := m) (n := n) F ∧
          (∀ x : Fin n → ℝ,
            primalObjectiveOfLagrangian (m := m) (n := n) L x =
              iSup fun uStar : Fin m → ℝ => L uStar x) ∧
          (minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
            iInf fun x : Fin n → ℝ =>
              primalObjectiveOfLagrangian (m := m) (n := n) L x) ∧
          (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
            bifunctionInverse F xStar uStar =
              iInf fun x : Fin n → ℝ =>
                L uStar x + (-((finDot (n := n) xStar x : ℝ) : EReal))) ∧
          (∀ uStar : Fin m → ℝ,
            dualObjectiveOfLagrangian (m := m) (n := n) L uStar =
              iInf fun x : Fin n → ℝ => L uStar x) ∧
          (maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
            iSup fun uStar : Fin m → ℝ =>
              dualObjectiveOfLagrangian (m := m) (n := n) L uStar)) := by
  intro hGeneric
  -- Specialize the generic claim to the explicit dimension-one witness first.
  have hSpecialized :=
    helperForProposition_36_5_1_specializeGenericStatementToConstantZero hGeneric
  -- The generic claim collapses to the already refuted constant-zero special case.
  exact helperForProposition_36_5_1_constantZero_conclusion_empty hSpecialized

-- Proof sketch: (1) and (3) are by unfolding the definitions of the primal/dual objective
-- functions and of `maximinValue`/`minimaxValue`. (2) follows from the adjoint-relation calculus
-- for the closed convex bifunction `F` defined as the conjugate of `L` in the first variable,
-- rewriting the resulting expression into the displayed infimum formula.
/-- Proposition 36.5.1: Let `L` be an upper closed concave-convex function on `ℝ^m × ℝ^n`. Define
a (closed convex) bifunction `F` by

`(F u) x = sup_{uStar} (L(uStar, x) - ⟨uStar, u⟩)`.

Then:
(1) the primal objective function is `φ(x) = sup_{uStar} L(uStar, x)` and the primal optimal
value is `inf_x sup_{uStar} L(uStar, x)`;
(2) the textbook Euclidean adjoint of `F`, evaluated at the sign-corrected dual pair, satisfies
`F^*(-xStar, -uStar) = inf_x (L(uStar, x) - ⟨xStar, x⟩)`;
(3) the dual objective function is `ψ(uStar) = inf_x L(uStar, x)` and the dual optimal value is
`sup_{uStar} inf_x L(uStar, x)`. -/
theorem lagrangian_primal_dual_objective_and_adjoint_formulas
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hL : IsUpperClosedConcaveConvex (m := m) (n := n) L)
    (hProperSlices :
      ∀ x : Fin n → ℝ, ProperConcaveERealFunction (fun uStar : Fin m → ℝ => L uStar x)) :
    let F := lagrangianToBifunction (m := m) (n := n) L
    IsEpigraphConvexBifunction (m := m) (n := n) F ∧
      IsEpigraphClosedConvexBifunction (m := m) (n := n) F ∧
      (∀ x : Fin n → ℝ,
        primalObjectiveOfLagrangian (m := m) (n := n) L x = iSup fun uStar : Fin m → ℝ => L uStar x) ∧
      (minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
        iInf fun x : Fin n → ℝ => primalObjectiveOfLagrangian (m := m) (n := n) L x) ∧
      (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        bifunctionEuclideanAdjointTextbook (m := m) (n := n) F (-xStar) (-uStar) =
          iInf fun x : Fin n → ℝ =>
            L uStar x + (-((finDot (n := n) xStar x : ℝ) : EReal))) ∧
      (∀ uStar : Fin m → ℝ,
        dualObjectiveOfLagrangian (m := m) (n := n) L uStar =
          iInf fun x : Fin n → ℝ => L uStar x) ∧
      (maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L =
        iSup fun uStar : Fin m → ℝ => dualObjectiveOfLagrangian (m := m) (n := n) L uStar) :=
  -- Proof sketch: (1) and (3) are by unfolding the primal/dual objective functions and the
  -- maximin/minimax definitions. For (2), expand the sign-corrected textbook adjoint of `F`,
  -- commute the two infima, and use the reconstructed-Lagrangian identity from Theorem 36.5.
  by
    dsimp only
    rcases hL with ⟨hUpper, hLower, hConc, hConv⟩
    have hF :
        IsEpigraphConvexBifunction (m := m) (n := n)
            (lagrangianToBifunction (m := m) (n := n) L) ∧
          IsEpigraphClosedConvexBifunction (m := m) (n := n)
            (lagrangianToBifunction (m := m) (n := n) L) :=
      helperForTheorem_36_5_reconstructedBifunction_closed_convex hLower hConv
    have hClosedSlices :
        ∀ x : Fin n → ℝ, ClosedConcaveFunction (fun uStar : Fin m → ℝ => L uStar x) :=
      helperForTheorem_36_5_sliceClosedConcave_of_upperClosedConcave hUpper hConc
    have hRecover :
        ∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
          bifunctionLagrangian (m := m) (n := n)
              ⟨lagrangianToBifunction (m := m) (n := n) L, hF.1⟩ uStar x =
            L uStar x :=
      helperForTheorem_36_5_reconstructedBifunction_recovers_L
        hClosedSlices hProperSlices hF.1
    refine ⟨hF.1, hF.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rfl
    · rfl
    · intro xStar uStar
      calc
        bifunctionEuclideanAdjointTextbook (m := m) (n := n)
            (lagrangianToBifunction (m := m) (n := n) L) (-xStar) (-uStar) =
            iInf fun u : Fin m → ℝ => iInf fun x : Fin n → ℝ =>
              (-((finDot (n := n) xStar x : ℝ) : EReal)) +
                (((finDot (n := m) uStar u : ℝ) : EReal) +
                  lagrangianToBifunction (m := m) (n := n) L u x) := by
              simp [bifunctionEuclideanAdjointTextbook, finDot, dotProduct, sub_eq_add_neg,
                add_comm, add_assoc]
        _ = iInf fun x : Fin n → ℝ => iInf fun u : Fin m → ℝ =>
              (-((finDot (n := n) xStar x : ℝ) : EReal)) +
                (((finDot (n := m) uStar u : ℝ) : EReal) +
                  lagrangianToBifunction (m := m) (n := n) L u x) := by
              rw [iInf_comm]
        _ = iInf fun x : Fin n → ℝ =>
              bifunctionLagrangian (m := m) (n := n)
                  ⟨lagrangianToBifunction (m := m) (n := n) L, hF.1⟩ uStar x +
                (-((finDot (n := n) xStar x : ℝ) : EReal)) := by
              congr 1
              funext x
              rw [bifunctionLagrangian, add_comm]
              simpa [EReal.coe_neg, add_comm, add_left_comm, add_assoc] using
                (helperForTheorem_6_30_15_real_add_iInf
                  (c := -(finDot (n := n) xStar x))
                  (f := fun u : Fin m → ℝ =>
                    ((finDot (n := m) uStar u : ℝ) : EReal) +
                      lagrangianToBifunction (m := m) (n := n) L u x)).symm
        _ = iInf fun x : Fin n → ℝ =>
              L uStar x + (-((finDot (n := n) xStar x : ℝ) : EReal)) := by
              congr 1
              funext x
              rw [hRecover uStar x]
    · intro uStar
      rfl
    · rfl

/-- A dual vector `xStar` is a subgradient of an `EReal`-valued function `f` at `x` if for every
`z` one has `f z ≥ f x + ⟪xStar, z - x⟫`, expressed via evaluation of `xStar` on `z - x`. -/
def IsSubgradientAtEReal {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) : Prop :=
  ∀ z, f z ≥ f x + ((xStar (z - x) : ℝ) : EReal)

/-- The subdifferential of an `EReal`-valued function `f` at `x`, defined as the set of all
subgradients at `x`. -/
def subdifferentialAtEReal {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Set (Module.Dual ℝ (Fin n → ℝ)) :=
  {g | IsSubgradientAtEReal f x g}

/-- The partial subdifferential `∂₁ L(uStar, x)` in the first variable for a concave-convex
function `L(uStar, x)`, modeled as the (convex) subdifferential of `uStar ↦ -L(uStar, x)`. -/
def lagrangianPartialSubdifferentialInFirst {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    Set (Module.Dual ℝ (Fin m → ℝ)) :=
  subdifferentialAtEReal (n := m) (fun uStar' => -L uStar' x) uStar

/-- The partial subdifferential `∂₂ L(uStar, x)` in the second variable for a concave-convex
function `L(uStar, x)`, modeled as the (convex) subdifferential of `x ↦ L(uStar, x)`. -/
def lagrangianPartialSubdifferentialInSecond {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    Set (Module.Dual ℝ (Fin n → ℝ)) :=
  subdifferentialAtEReal (n := n) (fun x' => L uStar x') x

/-- The product subdifferential `∂ L(uStar, x)` for a concave-convex function `L`, modeled as
`∂₁ L(uStar, x) × ∂₂ L(uStar, x)`. -/
def lagrangianSaddleSubdifferential {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    Set (Module.Dual ℝ (Fin m → ℝ) × Module.Dual ℝ (Fin n → ℝ)) :=
  lagrangianPartialSubdifferentialInFirst (m := m) (n := n) L uStar x ×ˢ
    lagrangianPartialSubdifferentialInSecond (m := m) (n := n) L uStar x

/-- The Kuhn--Tucker condition for a concave-convex function `L` at the point `(uStar, x)`,
namely the inclusion `(0, 0) ∈ ∂ L(uStar, x)`. -/
def IsKuhnTuckerCondition {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (uStar : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ((0 : Module.Dual ℝ (Fin m → ℝ)), (0 : Module.Dual ℝ (Fin n → ℝ))) ∈
    lagrangianSaddleSubdifferential (m := m) (n := n) L uStar x

-- Proof sketch: For fixed `x̄`, interpret the left saddle inequality as optimality (maximization)
-- of the concave function `uStar ↦ L(uStar, x̄)`, equivalently minimization of the convex function
-- `uStar ↦ -L(uStar, x̄)`, and use the standard subgradient characterization `0 ∈ ∂` for a
-- minimizer. For fixed `ū*`, interpret the right saddle inequality as optimality (minimization)
-- of the convex function `x ↦ L(ū*, x)` and apply the same characterization. Combine the two
-- one-variable conditions.
/-- Helper for Proposition 36.5.2: zero belongs to the second partial subdifferential exactly
when the fixed-`uStar0` slice is minimized at `x0`. -/
lemma helperForProposition_36_5_2_zero_mem_second_partialSubdifferential_iff
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    0 ∈ lagrangianPartialSubdifferentialInSecond (m := m) (n := n) L uStar0 x0 ↔
      ∀ x : Fin n → ℝ, L uStar0 x0 ≤ L uStar0 x := by
  -- Unfold the second partial subdifferential so the zero dual term disappears.
  change IsSubgradientAtEReal (fun x' => L uStar0 x') x0 (0 : Module.Dual ℝ (Fin n → ℝ)) ↔
    ∀ x : Fin n → ℝ, L uStar0 x0 ≤ L uStar0 x
  -- What remains is exactly the pointwise optimality inequality for the `x`-slice.
  simp [IsSubgradientAtEReal, ge_iff_le]

/-- Helper for Proposition 36.5.2: the reflected first-slice inequality for `-L` is equivalent to
the original maximizing inequality for `L`. -/
lemma helperForProposition_36_5_2_reflected_firstSlice_inequality_iff
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    (∀ uStar : Fin m → ℝ, -L uStar0 x0 ≤ -L uStar x0) ↔
      ∀ uStar : Fin m → ℝ, L uStar x0 ≤ L uStar0 x0 := by
  constructor
  · intro hNeg uStar
    -- Undo the reflection to recover the original saddle inequality in the first variable.
    exact EReal.neg_le_neg_iff.mp (hNeg uStar)
  · intro hMax uStar
    -- Reapply the reflection so the inequality matches the convex subgradient convention.
    exact EReal.neg_le_neg_iff.mpr (hMax uStar)

/-- Helper for Proposition 36.5.2: zero belongs to the first partial subdifferential exactly
when the fixed-`x0` slice is maximized at `uStar0`. -/
lemma helperForProposition_36_5_2_zero_mem_first_partialSubdifferential_iff
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    0 ∈ lagrangianPartialSubdifferentialInFirst (m := m) (n := n) L uStar0 x0 ↔
      ∀ uStar : Fin m → ℝ, L uStar x0 ≤ L uStar0 x0 := by
  -- Unfold the first partial subdifferential as the subdifferential of the reflected slice.
  change IsSubgradientAtEReal (fun uStar' => -L uStar' x0) uStar0
      (0 : Module.Dual ℝ (Fin m → ℝ)) ↔
    ∀ uStar : Fin m → ℝ, L uStar x0 ≤ L uStar0 x0
  constructor
  · intro hSub
    -- First collapse the zero-subgradient condition to the reflected pointwise inequalities.
    have hNeg : ∀ uStar : Fin m → ℝ, -L uStar0 x0 ≤ -L uStar x0 := by
      intro uStar
      simpa [IsSubgradientAtEReal] using hSub uStar
    -- Then remove the reflection to recover the maximizing property of the `uStar`-slice.
    exact
      (helperForProposition_36_5_2_reflected_firstSlice_inequality_iff
        (L := L) (uStar0 := uStar0) (x0 := x0)).1 hNeg
  · intro hMax uStar
    -- Convert the maximizing property back to the reflected inequality used by subgradients.
    have hNeg : ∀ uStar : Fin m → ℝ, -L uStar0 x0 ≤ -L uStar x0 :=
      (helperForProposition_36_5_2_reflected_firstSlice_inequality_iff
        (L := L) (uStar0 := uStar0) (x0 := x0)).2 hMax
    -- Folding this pointwise inequality back proves zero-subgradient membership.
    simpa [IsSubgradientAtEReal] using hNeg uStar

/-- Helper for Proposition 36.5.2: the saddle-point inequalities are exactly the two
one-variable optimality conditions, ordered to match the partial subdifferentials. -/
lemma helperForProposition_36_5_2_saddle_iff_split_zero_partialSubdifferentials
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L uStar0 x0 ↔
      ((∀ x : Fin n → ℝ, L uStar0 x0 ≤ L uStar0 x) ∧
        (∀ uStar : Fin m → ℝ, L uStar x0 ≤ L uStar0 x0)) := by
  constructor
  · intro hSaddle
    rcases hSaddle with ⟨hLeft, hRight⟩
    -- Reorder the two saddle inequalities to line up with the theorem statement.
    exact ⟨hRight, hLeft⟩
  · intro hSplit
    rcases hSplit with ⟨hRight, hLeft⟩
    -- Repackage the two one-variable optimality conditions as a saddle point.
    exact ⟨hLeft, hRight⟩

/-- Proposition 36.5.2: Let `L` be a concave-convex function on `ℝ^m × ℝ^n`. A pair `(uStar0, x0)`
is a saddle-point of `L`, i.e. `L uStar x0 ≤ L uStar0 x0 ≤ L uStar0 x` for all `uStar` and `x`, if
and only if `0 ∈ ∂₂ L(uStar0, x0)` and `0 ∈ ∂₁ L(uStar0, x0)` (with `∂₁` modeled as the
subdifferential of `-L` in the first variable). Equivalently, `(0, 0) ∈ ∂ L(uStar0, x0) =
∂₁ L(uStar0, x0) × ∂₂ L(uStar0, x0)`, and this inclusion is called the Kuhn--Tucker condition. -/
theorem saddlePoint_iff_zero_mem_partialSubdifferentials
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hL : IsConcaveInFirst (m := m) (n := n) L ∧ IsConvexInSecond (m := m) (n := n) L)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L uStar0 x0 ↔
      (0 ∈ lagrangianPartialSubdifferentialInSecond (m := m) (n := n) L uStar0 x0 ∧
        0 ∈ lagrangianPartialSubdifferentialInFirst (m := m) (n := n) L uStar0 x0) :=
  -- In this formalization the convexity assumptions explain the context, but the equivalence
  -- itself is obtained by unfolding the saddle inequalities and the two zero-subgradient tests.
  by
    let _ := hL
    -- First rewrite the saddle-point condition as the pair of one-variable optimality clauses.
    rw [helperForProposition_36_5_2_saddle_iff_split_zero_partialSubdifferentials]
    -- Then identify each optimality clause with zero membership in the corresponding
    -- partial subdifferential.
    rw [helperForProposition_36_5_2_zero_mem_second_partialSubdifferential_iff,
      helperForProposition_36_5_2_zero_mem_first_partialSubdifferential_iff]

/-- Helper for Proposition 36.5.2: the Kuhn--Tucker condition is exactly the pair of zero
partial-subdifferential memberships appearing in the saddle-point characterization. -/
lemma helperForProposition_36_5_2_kuhnTuckerCondition_iff
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    IsKuhnTuckerCondition (m := m) (n := n) L uStar0 x0 ↔
      (0 ∈ lagrangianPartialSubdifferentialInSecond (m := m) (n := n) L uStar0 x0 ∧
        0 ∈ lagrangianPartialSubdifferentialInFirst (m := m) (n := n) L uStar0 x0) := by
  -- Unfold the product subdifferential so the Kuhn--Tucker pair-membership splits componentwise.
  simp only [IsKuhnTuckerCondition, lagrangianSaddleSubdifferential, Set.mem_prod]
  -- The textbook statement orders the second-variable condition before the first-variable one.
  exact and_comm

/-- Helper for Proposition 36.5.2: after packaging the two partial-subdifferential conditions
into the product subdifferential, saddle points are exactly Kuhn--Tucker points. -/
lemma helperForProposition_36_5_2_saddlePoint_iff_kuhnTuckerCondition
    {m n : ℕ} (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hL : IsConcaveInFirst (m := m) (n := n) L ∧ IsConvexInSecond (m := m) (n := n) L)
    (uStar0 : Fin m → ℝ) (x0 : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L uStar0 x0 ↔
      IsKuhnTuckerCondition (m := m) (n := n) L uStar0 x0 := by
  -- First expand the saddle-point condition into the two zero partial-subdifferential clauses.
  rw [saddlePoint_iff_zero_mem_partialSubdifferentials
    (L := L) (hL := hL) (uStar0 := uStar0) (x0 := x0)]
  -- Then fold those two clauses back into the product-subdifferential formulation.
  exact
    (helperForProposition_36_5_2_kuhnTuckerCondition_iff
      (L := L) (uStar0 := uStar0) (x0 := x0)).symm

/-- The associated convex program `(P)` of a convex bifunction `F` is *strongly consistent* in
the sense assumed in Rockafellar's Theorem 36.6, modeled here by attainment of a finite primal
optimal value for the program induced by `F`. -/
def IsStronglyConsistentAssociatedProgram {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∃ hF : IsEpigraphConvexBifunction (m := m) (n := n) F,
    ∃ x : Fin n → ℝ,
      let L := bifunctionLagrangian (m := m) (n := n) ⟨F, hF⟩
      let φ := primalObjectiveOfLagrangian (m := m) (n := n) L
      φ x = iInf (fun x' : Fin n → ℝ => φ x') ∧
        φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)

/-- The associated convex program `(P)` of a convex bifunction `F` is *strictly consistent* in
the sense assumed in Rockafellar's Theorem 36.6, modeled here by a Slater-type finite point for
the Lagrangian slices of the program induced by `F`. -/
def IsStrictlyConsistentAssociatedProgram {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∃ hF : IsEpigraphConvexBifunction (m := m) (n := n) F,
    ∃ x : Fin n → ℝ,
      let L := bifunctionLagrangian (m := m) (n := n) ⟨F, hF⟩
      let φ := primalObjectiveOfLagrangian (m := m) (n := n) L
      (∀ uStar : Fin m → ℝ, L uStar x ≠ (⊤ : EReal) ∧ L uStar x ≠ (⊥ : EReal)) ∧
        φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)

/-- The associated convex program `(P)` of a convex bifunction `F` is *polyhedral* in the sense
used in Rockafellar's Theorem 36.6, modeled here by polyhedrality of the induced primal objective
function. -/
def IsPolyhedralAssociatedProgram {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∃ hF : IsEpigraphConvexBifunction (m := m) (n := n) F,
    ∃ k l : ℕ,
      ∃ b : Fin (k + l) → Fin n → ℝ,
        ∃ β : Fin (k + l) → ℝ,
          primalObjectiveOfLagrangian (m := m) (n := n)
              (bifunctionLagrangian (m := m) (n := n) ⟨F, hF⟩) =
            (fun x =>
              ((sSup {r : ℝ |
                  ∃ i : Fin (k + l), (i : ℕ) < k ∧
                    r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
                if ∀ i : Fin (k + l), k ≤ (i : ℕ) →
                    (∑ j, x j * b i j) ≤ β i then
                  0
                else
                  (⊤ : EReal))

/-- The associated convex program `(P)` of a convex bifunction `F` is *consistent* in the sense
used in Rockafellar's Theorem 36.6, modeled here by existence of a primal point with finite
objective value for the program induced by `F`. -/
def IsConsistentAssociatedProgram {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∃ hF : IsEpigraphConvexBifunction (m := m) (n := n) F,
    ∃ x : Fin n → ℝ,
      let φ := primalObjectiveOfLagrangian (m := m) (n := n)
        (bifunctionLagrangian (m := m) (n := n) ⟨F, hF⟩)
      φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)

/-- A predicate expressing Rockafellar's qualification hypotheses in Theorem 36.6 for the convex
program `(P)` associated with a closed proper convex bifunction `F`: namely, that `(P)` is
strongly consistent, or strictly consistent, or polyhedral and consistent. -/
def AssociatedProgramQualifiesForKuhnTucker {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsStronglyConsistentAssociatedProgram (m := m) (n := n) F ∨
    IsStrictlyConsistentAssociatedProgram (m := m) (n := n) F ∨
      (IsPolyhedralAssociatedProgram (m := m) (n := n) F ∧
        IsConsistentAssociatedProgram (m := m) (n := n) F)

/-- A point `x` is a primal optimal solution for a Lagrangian `L(uStar, x)` if it attains the
primal value `inf_x sup_{uStar} L(uStar, x)`. -/
def IsPrimalOptimalSolutionOfLagrangian {m n : ℕ}
    (L : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Prop :=
  primalObjectiveOfLagrangian (m := m) (n := n) L x =
    iInf fun x' : Fin n → ℝ => primalObjectiveOfLagrangian (m := m) (n := n) L x'

/-- A point `x` is an optimal solution of the convex program `(P)` associated with a convex
bifunction `F`, expressed via the Lagrangian `bifunctionLagrangian F`. -/
def IsOptimalSolutionOfAssociatedProgram {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F})
    (x : Fin n → ℝ) : Prop :=
  IsPrimalOptimalSolutionOfLagrangian (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) x

/-- A Kuhn--Tucker vector `uStar` for the convex program associated with `F` at the primal point
`x`, meaning `(0,0) ∈ ∂ L(uStar, x)` for the Lagrangian `L = bifunctionLagrangian F`. -/
def IsKuhnTuckerVectorOfAssociatedProgram {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F})
    (x : Fin n → ℝ) (uStar : Fin m → ℝ) : Prop :=
  IsKuhnTuckerCondition (m := m) (n := n) (bifunctionLagrangian (m := m) (n := n) F) uStar x

-- Proof sketch: Under the stated consistency or polyhedrality hypotheses, the primal problem
-- for the convex program `(P)` associated with `F` has no duality gap and admits a saddle-point
-- characterization in terms of its Lagrangian `L`. Convert the saddle-point condition into
-- the product subdifferential inclusion `(0,0) ∈ ∂ L(uStar, x)` using Proposition 36.5.2.
-- The displayed condition is exactly the definition of a Kuhn--Tucker vector for the
-- associated program.
/-- Theorem 36.6: Let `(P)` be the convex program (Section 28) associated with a closed proper
convex bifunction `F : ℝ^m → ℝ^n → [-∞, +∞]`. Assume `(P)` is strongly (or strictly) consistent,
or that `(P)` is polyhedral and consistent. With the explicit additional qualification that the
dual value is attained with no gap, a vector `x̃ ∈ ℝ^n` is an optimal solution of `(P)` if and only
if there exists `ũ* ∈ ℝ^m` such that `(0,0) ∈ ∂ L(ũ*, x̃)`, where `L` is the Lagrangian of
`(P)`. The vectors `ũ*` satisfying this condition are exactly the Kuhn--Tucker vectors for `(P)`. -/
theorem optimalSolution_iff_exists_kuhnTuckerVector
    {m n : ℕ}
    (F :
      {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsEpigraphConvexBifunction (m := m) (n := n) F})
    (hFclosed : IsEpigraphClosedConvexBifunction (m := m) (n := n) F.1)
    (hFproper : IsEpigraphProperConvexBifunction (m := m) (n := n) F.1)
    (hQual : AssociatedProgramQualifiesForKuhnTucker (m := m) (n := n) F.1)
    (hDualAttain :
      ∃ uStar : Fin m → ℝ,
        dualObjectiveOfLagrangian (m := m) (n := n)
            (bifunctionLagrangian (m := m) (n := n) F) uStar =
          iInf fun x : Fin n → ℝ =>
            primalObjectiveOfLagrangian (m := m) (n := n)
              (bifunctionLagrangian (m := m) (n := n) F) x)
    (xTilde : Fin n → ℝ) :
    IsOptimalSolutionOfAssociatedProgram (m := m) (n := n) F xTilde ↔
      ∃ uStarTilde : Fin m → ℝ,
        IsKuhnTuckerVectorOfAssociatedProgram (m := m) (n := n) F xTilde uStarTilde :=
  by
    let _ := hFclosed
    let _ := hFproper
    let _ := hQual
    let L := bifunctionLagrangian (m := m) (n := n) F
    have hOrientation :
        IsConcaveInFirst (m := m) (n := n) L ∧ IsConvexInSecond (m := m) (n := n) L := by
      simpa [L] using
        helperForTheorem_36_5_lagrangian_has_concaveConvex_orientation (F := F)
    constructor
    · intro hx
      rcases hDualAttain with ⟨uStar, hDual⟩
      refine ⟨uStar, ?_⟩
      have hx' :
          primalObjectiveOfLagrangian (m := m) (n := n) L xTilde =
            iInf fun x : Fin n → ℝ =>
              primalObjectiveOfLagrangian (m := m) (n := n) L x := by
        simpa [IsOptimalSolutionOfAssociatedProgram, IsPrimalOptimalSolutionOfLagrangian, L]
          using hx
      have hDual' :
          dualObjectiveOfLagrangian (m := m) (n := n) L uStar =
            iInf fun x : Fin n → ℝ =>
              primalObjectiveOfLagrangian (m := m) (n := n) L x := by
        simpa [L] using hDual
      have hValueEq :
          dualObjectiveOfLagrangian (m := m) (n := n) L uStar =
            primalObjectiveOfLagrangian (m := m) (n := n) L xTilde :=
        hDual'.trans hx'.symm
      have hCenterEqPrimal :
          L uStar xTilde =
            primalObjectiveOfLagrangian (m := m) (n := n) L xTilde := by
        apply le_antisymm
        · exact le_iSup (fun u : Fin m → ℝ => L u xTilde) uStar
        · rw [← hValueEq]
          exact iInf_le (fun x : Fin n → ℝ => L uStar x) xTilde
      have hSaddle :
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L uStar xTilde := by
        constructor
        · intro u
          calc
            L u xTilde ≤ primalObjectiveOfLagrangian (m := m) (n := n) L xTilde :=
              le_iSup (fun v : Fin m → ℝ => L v xTilde) u
            _ = L uStar xTilde := hCenterEqPrimal.symm
        · intro x
          calc
            L uStar xTilde = dualObjectiveOfLagrangian (m := m) (n := n) L uStar :=
              hCenterEqPrimal.trans hValueEq.symm
            _ ≤ L uStar x := iInf_le (fun y : Fin n → ℝ => L uStar y) x
      have hKT : IsKuhnTuckerCondition (m := m) (n := n) L uStar xTilde :=
        (helperForProposition_36_5_2_saddlePoint_iff_kuhnTuckerCondition
          (L := L) hOrientation uStar xTilde).1 hSaddle
      simpa [IsKuhnTuckerVectorOfAssociatedProgram, L] using hKT
    · rintro ⟨uStar, hKT⟩
      have hKT' : IsKuhnTuckerCondition (m := m) (n := n) L uStar xTilde := by
        simpa [IsKuhnTuckerVectorOfAssociatedProgram, L] using hKT
      have hSaddle :
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L uStar xTilde :=
        (helperForProposition_36_5_2_saddlePoint_iff_kuhnTuckerCondition
          (L := L) hOrientation uStar xTilde).2 hKT'
      have hPrimalEqCenter :
          primalObjectiveOfLagrangian (m := m) (n := n) L xTilde = L uStar xTilde := by
        apply le_antisymm
        · exact iSup_le hSaddle.1
        · exact le_iSup (fun u : Fin m → ℝ => L u xTilde) uStar
      have hOptimal :
          primalObjectiveOfLagrangian (m := m) (n := n) L xTilde =
            iInf fun x : Fin n → ℝ =>
              primalObjectiveOfLagrangian (m := m) (n := n) L x := by
        rw [hPrimalEqCenter]
        apply le_antisymm
        · refine le_iInf ?_
          intro x
          exact le_trans (hSaddle.2 x)
            (le_iSup (fun u : Fin m → ℝ => L u x) uStar)
        · calc
            (iInf fun x : Fin n → ℝ =>
                primalObjectiveOfLagrangian (m := m) (n := n) L x) ≤
                primalObjectiveOfLagrangian (m := m) (n := n) L xTilde :=
              iInf_le
                (fun x : Fin n → ℝ =>
                  primalObjectiveOfLagrangian (m := m) (n := n) L x) xTilde
            _ = L uStar xTilde := hPrimalEqCenter
      simpa [IsOptimalSolutionOfAssociatedProgram, IsPrimalOptimalSolutionOfLagrangian, L]
        using hOptimal

end Section36
end Chap07

example :
    bifunctionInverseEuclideanAdjointTextbook (m := 0) (n := 0)
      (lagrangianToBifunction (m := 0) (n := 0) (fun _ _ => (1 : EReal))) 0 0 =
        (-1 : EReal) := by
  simp [bifunctionInverseEuclideanAdjointTextbook, bifunctionEuclideanAdjointTextbook,
    bifunctionInverse, lagrangianToBifunction, finDot]

example :
    (iInf fun x : Fin 0 → ℝ =>
      (fun _ _ => (1 : EReal)) (0 : Fin 0 → ℝ) x +
        (-((finDot (n := 0) (0 : Fin 0 → ℝ) x : ℝ) : EReal))) =
      (1 : EReal) := by
  simp [finDot]
