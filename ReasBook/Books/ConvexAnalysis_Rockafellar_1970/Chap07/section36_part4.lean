/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part3

section Chap07
section Section36

/-- The bifunction commonly denoted `F_*^*`, obtained by composing inverse (`_*`) and adjoint (`^*`):
`F_*^* := (F_*)^*`. -/
noncomputable def bifunctionInverseEuclideanAdjoint {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionInverse F)

/-- The biconjugate `F^{**}` of a bifunction `F`, defined as applying the adjoint operation twice. -/
noncomputable def bifunctionEuclideanBiconjugate {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionEuclideanAdjoint (m := m) (n := n) F)

/-- The textbook Euclidean adjoint on `Fin k → ℝ`, matching the Chapter 8 infimum convention
`F^*(x^*,u^*) = inf_{u,x} (⟨x^*,x⟩ - ⟨u^*,u⟩ + F(u,x))`. -/
noncomputable def bifunctionEuclideanAdjointTextbook {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    iInf fun u : Fin m → ℝ =>
      iInf fun x : Fin n → ℝ =>
        (((finDot (n := n) xStar x - finDot (n := m) uStar u : ℝ)) : EReal) + F u x

/-- The textbook object `F_*^* = (F_*)^*` formed from the Euclidean adjoint above. -/
noncomputable def bifunctionInverseEuclideanAdjointTextbook {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  bifunctionEuclideanAdjointTextbook (m := n) (n := m) (bifunctionInverse F)

/-- The textbook Euclidean biconjugate `F^{**}`. -/
noncomputable def bifunctionEuclideanBiconjugateTextbook {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  bifunctionEuclideanAdjointTextbook (m := n) (n := m)
    (bifunctionEuclideanAdjointTextbook (m := m) (n := n) F)

/-- Helper for Proposition 36.4.4: the first `_*^*` iterate of the dimension-one constant-zero
bifunction is already `⊤` at the witness `(1, 0)`. -/
lemma helperForProposition_36_4_4_constantZero_firstIterate_topAtWitness :
    bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (⊤ : EReal) :=
  by
    let H : EReal :=
      bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector
    have hLowerReal : ∀ r : ℝ, (r : EReal) ≤ H := by
      intro r
      let xWitness : Fin 1 → ℝ := fun _ => r
      -- Choosing `(u', x') = (0, r)` inside the defining suprema realizes the value `r`.
      refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
      refine le_iSup_of_le xWitness ?_
      simp [xWitness, bifunctionInverse, finDot, dotProduct, helperForProposition_36_4_3_oneVector,
        helperForProposition_36_4_3_zeroVector]
    -- The iterate dominates every real number, so it cannot be anything except `⊤`.
    apply top_unique
    by_contra htop
    have hneTop : H ≠ (⊤ : EReal) := by
      intro hH
      exact htop (hH ▸ le_rfl)
    have hupper : H ≤ (((H.toReal : ℝ)) : EReal) := by
      exact EReal.le_coe_toReal (x := H) hneTop
    have hlower : (((H.toReal + 1 : ℝ)) : EReal) ≤ H := by
      simpa [H] using hLowerReal (H.toReal + 1)
    have hlt : (((H.toReal : ℝ)) : EReal) < (((H.toReal + 1 : ℝ)) : EReal) := by
      exact_mod_cast (show (H.toReal : ℝ) < H.toReal + 1 by linarith)
    exact (not_le_of_gt hlt) (le_trans hlower hupper)

/-- Helper for Proposition 36.4.4: the second `_*^*` iterate of the dimension-one constant-zero
bifunction is also `⊤` at the same witness `(1, 0)`. -/
lemma helperForProposition_36_4_4_constantZero_secondIterate_topAtWitness :
    bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
        (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
      helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (⊤ : EReal) :=
  by
    let G : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal :=
      bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
    have hFirst :
        G helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector =
          (⊤ : EReal) := by
      simpa [G] using helperForProposition_36_4_4_constantZero_firstIterate_topAtWitness
    -- Reusing the swapped witness inside the outer adjoint turns the inner `⊤` value into another
    -- `⊤` contribution.
    apply top_unique
    refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
    refine le_iSup_of_le helperForProposition_36_4_3_oneVector ?_
    simpa [G, bifunctionInverse, finDot, helperForProposition_36_4_3_oneVector,
      helperForProposition_36_4_3_zeroVector, hFirst] using
      (EReal.add_top_of_ne_bot (x := (1 : EReal)) (EReal.coe_ne_bot (1 : ℝ)))

/-- Helper for Proposition 36.4.4: the Euclidean adjoint of the dimension-one constant-zero
bifunction vanishes at `(0, 0)`. -/
lemma helperForProposition_36_4_4_constantZero_adjoint_atZero_eq_zero :
    bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_zeroVector = (0 : EReal) :=
  by
    apply le_antisymm
    · -- Every term in the supremum is already `0`, so the adjoint cannot exceed `0`.
      refine iSup_le ?_
      intro u
      refine iSup_le ?_
      intro x
      simp [finDot, dotProduct, helperForProposition_36_4_3_zeroVector]
    · -- Taking the zero witnesses inside the supremum realizes the lower bound `0`.
      refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
      refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
      simp [finDot, dotProduct, helperForProposition_36_4_3_zeroVector]

/-- Helper for Proposition 36.4.4: every outer pairing term at the witness `(1, 0)` is dominated
by the Euclidean adjoint of the dimension-one constant-zero bifunction. -/
lemma helperForProposition_36_4_4_constantZero_outerPairing_le_adjoint
    (u x : Fin 1 → ℝ) :
    (((finDot (n := 1) helperForProposition_36_4_3_oneVector x +
        finDot (n := 1) helperForProposition_36_4_3_zeroVector u : ℝ)) : EReal) ≤
      bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)) u x :=
  by
    -- Choosing the witnesses `(1, 0)` inside the adjoint exposes exactly the outer pairing term.
    refine le_iSup_of_le helperForProposition_36_4_3_oneVector ?_
    refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
    simp [finDot, dotProduct, helperForProposition_36_4_3_oneVector,
      helperForProposition_36_4_3_zeroVector, add_comm]

/-- Helper for Proposition 36.4.4: the lower-semicontinuous hull of the dimension-one
constant-zero bifunction is still the constant-zero function. -/
lemma helperForProposition_36_4_4_constantZero_lowerSemicontinuousHull_eq_zero :
    erealLowerSemicontinuousHull
      (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)) =
      fun _ => (0 : EReal) :=
  by
    funext p
    unfold erealLowerSemicontinuousHull
    apply le_antisymm
    · -- Every admissible minorant lies below the zero function pointwise.
      refine iSup_le ?_
      intro h
      exact h.2.2 p
    · let hZero :
          {h : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → EReal //
            LowerSemicontinuous h ∧ h ≤ (fun _ => (0 : EReal))} :=
        ⟨fun _ => (0 : EReal), by
          constructor
          · -- The constant zero function is lower semicontinuous.
            simpa using
              (lowerSemicontinuous_const :
                LowerSemicontinuous (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)))
          · -- It is also an admissible minorant of itself.
            intro q
            rfl⟩
      -- The zero minorant contributes the matching lower bound.
      exact le_iSup_of_le hZero le_rfl

/-- Helper for Proposition 36.4.4: at the witness `(1, 0)`, both the biconjugate and the closure
of the dimension-one constant-zero bifunction equal `0`. -/
lemma helperForProposition_36_4_4_constantZero_biconjugate_and_closure_eq_zero :
    bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (0 : EReal) ∧
      bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (0 : EReal) :=
  by
    constructor
    · apply le_antisymm
      · -- Each term in the outer supremum is nonpositive because the inner adjoint already
        -- dominates the outer pairing.
        refine iSup_le ?_
        intro u
        refine iSup_le ?_
        intro x
        let a : ℝ :=
          finDot (n := 1) helperForProposition_36_4_3_oneVector x +
            finDot (n := 1) helperForProposition_36_4_3_zeroVector u
        have hdom :
            (a : EReal) ≤ bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)) u x := by
          simpa [a] using
            helperForProposition_36_4_4_constantZero_outerPairing_le_adjoint u x
        have hneg :
            -(bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)) u x) ≤
              -((a : EReal)) := by
          simpa using (EReal.neg_le_neg_iff.2 hdom)
        have hsum :
            (a : EReal) + -(bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)) u x) ≤
              (a : EReal) + -((a : EReal)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hneg (a : EReal)
        have hcancel : (a : EReal) + -((a : EReal)) = (0 : EReal) := by
          have hrealCancel : a + -a = 0 := by
            ring
          exact_mod_cast hrealCancel
        exact le_trans
          (by
            simpa [a, bifunctionEuclideanBiconjugate, bifunctionEuclideanAdjoint, finDot,
              helperForProposition_36_4_3_oneVector, helperForProposition_36_4_3_zeroVector] using hsum)
          (le_of_eq hcancel)
      · have hAdj0 :
            bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
              helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_zeroVector = (0 : EReal) :=
          helperForProposition_36_4_4_constantZero_adjoint_atZero_eq_zero
        -- The zero witnesses inside the outer supremum realize the lower bound `0`.
        refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
        refine le_iSup_of_le helperForProposition_36_4_3_zeroVector ?_
        simp [finDot, dotProduct, helperForProposition_36_4_3_zeroVector, hAdj0]
    · -- The closure reduces to the lower-semicontinuous hull, which stays equal to zero.
      simp [bifunctionClosure, erealFunctionClosure,
        helperForProposition_36_4_4_constantZero_lowerSemicontinuousHull_eq_zero]

/-- Helper for Proposition 36.4.4: evaluating the specialized equality branch at the witness
`(1, 0)` forces the impossible identity `⊤ = 0`. -/
lemma helperForProposition_36_4_4_constantZero_witness_forces_top_eq_zero
    (hIterateEq :
      bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
        bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
    (hClosureEq :
      bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
        bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))) :
    (⊤ : EReal) = (0 : EReal) :=
  by
    have hIterateEval := congrArg
      (fun G =>
        G helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector) hIterateEq
    have hClosureEval := congrArg
      (fun G =>
        G helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector) hClosureEq
    rcases helperForProposition_36_4_4_constantZero_biconjugate_and_closure_eq_zero with
      ⟨hBiconjugateZero, hClosureZero⟩
    -- The second iterate gives `⊤` at the witness, and the equalities transport that value to
    -- the closure, which is already known to be `0`.
    calc
      (⊤ : EReal) =
          bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
            helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector := by
              simpa using
                helperForProposition_36_4_4_constantZero_secondIterate_topAtWitness.symm
      _ = bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal))
            helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector := by
              simpa using hIterateEval
      _ = bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))
            helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector := by
              simpa using hClosureEval
      _ = (0 : EReal) := by
              simpa using hClosureZero

/-- Helper for Proposition 36.4.4: the equality branch of the dimension-one constant-zero
specialization already fails at the explicit witness `(1, 0)`. -/
lemma helperForProposition_36_4_4_constantZero_equalityBranch_fails :
    ¬ (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
        bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
      bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
        bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))) :=
  by
    intro hEqualities
    rcases hEqualities with ⟨hIterateEq, hClosureEq⟩
    -- The dedicated witness lemma packages the exact contradiction forced by the two equalities.
    have hTopEqZero : (⊤ : EReal) = (0 : EReal) :=
      helperForProposition_36_4_4_constantZero_witness_forces_top_eq_zero hIterateEq hClosureEq
    have hTopNeZero : (⊤ : EReal) ≠ (0 : EReal) := by
      simp
    exact hTopNeZero hTopEqZero

/-- Helper for Proposition 36.4.4: even the conclusion of the dimension-one constant-zero
specialization is empty, because its equality branch already forces `⊤ = 0`. -/
lemma helperForProposition_36_4_4_constantZero_conclusion_isEmpty :
    IsEmpty
      (IsEpigraphConvexBifunction (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) ∧
        bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
          bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
          bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
            bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))) :=
  by
    refine ⟨?_⟩
    intro hConclusion
    -- The convexity component is irrelevant here; projecting to the equality branch recovers the
    -- contradiction already proved at the witness `(1, 0)`.
    exact helperForProposition_36_4_4_constantZero_equalityBranch_fails
      ⟨hConclusion.2.1, hConclusion.2.2⟩

/-- Helper for Proposition 36.4.4: the specialized target statement already fails on the
dimension-one constant-zero bifunction, so the local theorem cannot be proved as written. -/
lemma helperForProposition_36_4_4_constantZero_target_fails :
    ¬ (IsEpigraphConvexBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
        IsEpigraphConvexBifunction (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) ∧
          bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
            bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
            bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
              bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))) :=
  by
    intro hTarget
    have hSpecialized :=
      hTarget (helperForProposition_36_4_3_constantZero_isEpigraphConvex (m := 1) (n := 1))
    -- The new conclusion-level emptiness lemma shows that the specialization already fails before
    -- using any additional structure of the theorem statement.
    exact helperForProposition_36_4_4_constantZero_conclusion_isEmpty.false hSpecialized

/-- Helper for Proposition 36.4.4: the specialized theorem type for the dimension-one
constant-zero bifunction is empty. -/
lemma helperForProposition_36_4_4_constantZero_targetType_isEmpty :
    IsEmpty
      (IsEpigraphConvexBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
        IsEpigraphConvexBifunction (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) ∧
          bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
            bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
            bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
              bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal))) :=
  by
    refine ⟨?_⟩
    intro hSpecialized
    -- The previous helper already proves that this exact specialized theorem type is uninhabited.
    exact helperForProposition_36_4_4_constantZero_target_fails hSpecialized

/-- Helper for Proposition 36.4.4: any universal proof of the displayed theorem would specialize
to the already disproved dimension-one constant-zero instance. -/
lemma helperForProposition_36_4_4_universalTarget_fails :
    ¬ (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsEpigraphConvexBifunction (m := m) (n := n) F →
            IsEpigraphConvexBifunction (m := m) (n := n)
              (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) ∧
              bifunctionInverseEuclideanAdjoint (m := m) (n := n)
                  (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) =
                bifunctionEuclideanBiconjugate (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugate (m := m) (n := n) F = bifunctionClosure F) :=
  by
    intro hUniversal
    have hSpecialized :
        IsEpigraphConvexBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
          IsEpigraphConvexBifunction (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) ∧
            bifunctionInverseEuclideanAdjoint (m := 1) (n := 1)
                (bifunctionInverseEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) =
              bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
              bifunctionEuclideanBiconjugate (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
                bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal)) :=
      hUniversal (m := 1) (n := 1) (fun _ _ => (0 : EReal))
    -- Specializing the universal theorem lands in the already empty constant-zero theorem type.
    exact helperForProposition_36_4_4_constantZero_targetType_isEmpty.false hSpecialized

/-- Helper for Proposition 36.4.4: the exact universal theorem type is empty under the current
section-local `_*^*` convention. -/
lemma helperForProposition_36_4_4_targetType_isEmpty :
    IsEmpty
      (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsEpigraphConvexBifunction (m := m) (n := n) F →
            IsEpigraphConvexBifunction (m := m) (n := n)
              (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) ∧
              bifunctionInverseEuclideanAdjoint (m := m) (n := n)
                  (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) =
                bifunctionEuclideanBiconjugate (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugate (m := m) (n := n) F = bifunctionClosure F) :=
  by
    refine ⟨?_⟩
    intro hUniversal
    -- The previous helper already shows that any inhabitant of the theorem type specializes to
    -- the dimension-one constant-zero contradiction.
    exact helperForProposition_36_4_4_universalTarget_fails hUniversal

/-- Helper for Proposition 36.4.4: the exact theorem signature with the convexity premise written
as an explicit argument is already empty under the current local `_*^*` convention. -/
lemma helperForProposition_36_4_4_exactTheoremSignature_isEmpty :
    IsEmpty
      (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
          (hF : IsEpigraphConvexBifunction (m := m) (n := n) F),
          IsEpigraphConvexBifunction (m := m) (n := n)
            (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) ∧
            bifunctionInverseEuclideanAdjoint (m := m) (n := n)
                (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) =
              bifunctionEuclideanBiconjugate (m := m) (n := n) F ∧
              bifunctionEuclideanBiconjugate (m := m) (n := n) F = bifunctionClosure F) :=
  by
    refine ⟨?_⟩
    intro hTheorem
    have hUniversal :
        ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsEpigraphConvexBifunction (m := m) (n := n) F →
            IsEpigraphConvexBifunction (m := m) (n := n)
              (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) ∧
              bifunctionInverseEuclideanAdjoint (m := m) (n := n)
                  (bifunctionInverseEuclideanAdjoint (m := m) (n := n) F) =
                bifunctionEuclideanBiconjugate (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugate (m := m) (n := n) F = bifunctionClosure F := by
      intro m n F hF
      -- Repackage the explicit-premise version into the implication-shaped theorem type.
      exact hTheorem (m := m) (n := n) F hF
    -- The implication-shaped theorem type is already empty by the specialized constant-zero
    -- contradiction above, so the exact theorem signature is empty as well.
    exact helperForProposition_36_4_4_targetType_isEmpty.false hUniversal

/-- Helper for Proposition 36.4.4: the textbook `_*^*` iterate of the dimension-one
constant-zero bifunction vanishes at the origin `(0, 0)`. -/
lemma helperForProposition_36_4_4_textbookZeroIterate_atOrigin_eq_zero :
    bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_zeroVector = (0 : EReal) :=
  by
    -- At the origin every term in the defining infimum simplifies to `0`.
    simp [bifunctionInverseEuclideanAdjointTextbook, bifunctionEuclideanAdjointTextbook,
      bifunctionInverse, finDot, dotProduct, helperForProposition_36_4_3_zeroVector]

/-- Helper for Proposition 36.4.4: the textbook `_*^*` iterate of the dimension-one
constant-zero bifunction already equals `⊥` at the witness `(1, 0)`. -/
lemma helperForProposition_36_4_4_textbookZeroIterate_atOneZero_eq_bot :
    bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector = (⊥ : EReal) :=
  by
    let H : EReal :=
      bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector
    rw [EReal.eq_bot_iff_forall_lt]
    intro y
    have hUpper : H ≤ ((y - 1 : ℝ) : EReal) := by
      -- Choosing the witness `x = y - 1` forces the infimum below any prescribed real bound.
      refine iInf_le_of_le helperForProposition_36_4_3_zeroVector ?_
      refine iInf_le_of_le (fun _ => y - 1) ?_
      simp [bifunctionInverse, finDot, dotProduct, helperForProposition_36_4_3_oneVector,
        helperForProposition_36_4_3_zeroVector]
    have hStrict : (((y - 1 : ℝ) : EReal)) < (y : EReal) := by
      exact_mod_cast (show y - 1 < y by linarith)
    exact lt_of_le_of_lt hUpper hStrict

/-- Helper for Proposition 36.4.4: the textbook `_*^*` iterate of the dimension-one
constant-zero bifunction also equals `⊥` at the witness `(-1, 0)`. -/
lemma helperForProposition_36_4_4_textbookZeroIterate_atNegOneZero_eq_bot :
    bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      (fun _ => (-1 : ℝ)) helperForProposition_36_4_3_zeroVector = (⊥ : EReal) :=
  by
    let H : EReal :=
      bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        (fun _ => (-1 : ℝ)) helperForProposition_36_4_3_zeroVector
    rw [EReal.eq_bot_iff_forall_lt]
    intro y
    have hUpper : H ≤ ((y - 1 : ℝ) : EReal) := by
      -- Choosing the witness `x = 1 - y` again pushes the infimum below every real number.
      refine iInf_le_of_le helperForProposition_36_4_3_zeroVector ?_
      refine iInf_le_of_le (fun _ => 1 - y) ?_
      simp [bifunctionInverse, finDot, dotProduct, helperForProposition_36_4_3_zeroVector]
    have hStrict : (((y - 1 : ℝ) : EReal)) < (y : EReal) := by
      exact_mod_cast (show y - 1 < y by linarith)
    exact lt_of_le_of_lt hUpper hStrict

/-- Helper for Proposition 36.4.4: the textbook `_*^*` iterate of the dimension-one
constant-zero bifunction does not have a convex epigraph. -/
lemma helperForProposition_36_4_4_textbookZeroIterate_epigraph_not_convex :
    ¬ IsEpigraphConvexBifunction (m := 1) (n := 1)
      (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal))) :=
  by
    intro hConv
    let negOneVector : Fin 1 → ℝ := fun _ => (-1 : ℝ)
    have hPos :
        (((helperForProposition_36_4_3_oneVector, helperForProposition_36_4_3_zeroVector),
            (-1 : ℝ))) ∈
          bifunctionEpigraph (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ => (0 : EReal))) := by
      -- Since the value is `⊥`, every real height lies in the epigraph above `(1, 0)`.
      simp [bifunctionEpigraph,
        helperForProposition_36_4_4_textbookZeroIterate_atOneZero_eq_bot]
    have hNeg :
        (((negOneVector, helperForProposition_36_4_3_zeroVector), (-1 : ℝ))) ∈
          bifunctionEpigraph (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ => (0 : EReal))) := by
      -- The symmetric witness `(-1, 0)` belongs for the same reason.
      simp [bifunctionEpigraph, negOneVector,
        helperForProposition_36_4_4_textbookZeroIterate_atNegOneZero_eq_bot]
    have hMid :=
      hConv hPos hNeg (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hMidNot :
        (((helperForProposition_36_4_3_zeroVector, helperForProposition_36_4_3_zeroVector),
            (-1 : ℝ))) ∉
          bifunctionEpigraph (m := 1) (n := 1)
            (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ => (0 : EReal))) := by
      -- At the midpoint `(0, 0)` the iterate equals `0`, so height `-1` falls below the epigraph.
      simp [bifunctionEpigraph,
        helperForProposition_36_4_4_textbookZeroIterate_atOrigin_eq_zero]
    have hMidEq :
        (1 / 2 : ℝ) •
            ((((helperForProposition_36_4_3_oneVector, helperForProposition_36_4_3_zeroVector),
                (-1 : ℝ))) :
              (((Fin 1 → ℝ) × (Fin 1 → ℝ)) × ℝ)) +
          (1 / 2 : ℝ) •
            ((((negOneVector, helperForProposition_36_4_3_zeroVector), (-1 : ℝ))) :
              (((Fin 1 → ℝ) × (Fin 1 → ℝ)) × ℝ)) =
          ((((helperForProposition_36_4_3_zeroVector, helperForProposition_36_4_3_zeroVector),
              (-1 : ℝ))) :
            (((Fin 1 → ℝ) × (Fin 1 → ℝ)) × ℝ)) := by
      -- Computing the weighted average of the two witness points gives the origin at height `-1`.
      dsimp [negOneVector]
      apply Prod.ext
      · apply Prod.ext
        · funext i
          fin_cases i
          norm_num [helperForProposition_36_4_3_oneVector,
            helperForProposition_36_4_3_zeroVector]
        · funext i
          fin_cases i
          norm_num [helperForProposition_36_4_3_zeroVector]
      · norm_num
    apply hMidNot
    -- The midpoint of the two witnesses is exactly `((0, 0), -1)`.
    exact hMidEq ▸ hMid

/-- Helper for Proposition 36.4.4: any implication-shaped universal proof of the textbook
`_*^*` theorem would already contradict the dimension-one constant-zero specialization. -/
lemma helperForProposition_36_4_4_textbookUniversalTarget_fails
    (hUniversal :
      ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
        IsEpigraphConvexBifunction (m := m) (n := n) F →
          IsEpigraphConvexBifunction (m := m) (n := n)
            (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) ∧
            bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n)
                (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) =
              bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F ∧
              bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F =
                bifunctionClosure F) :
    False :=
  by
    have hSpecialized :
        IsEpigraphConvexBifunction (m := 1) (n := 1)
          (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
            (fun _ _ => (0 : EReal))) ∧
          bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
                (fun _ _ => (0 : EReal))) =
            bifunctionEuclideanBiconjugateTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal)) ∧
            bifunctionEuclideanBiconjugateTextbook (m := 1) (n := 1) (fun _ _ => (0 : EReal)) =
              bifunctionClosure (fun _ _ : Fin 1 → ℝ => (0 : EReal)) :=
      hUniversal (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        (helperForProposition_36_4_3_constantZero_isEpigraphConvex (m := 1) (n := 1))
    -- Specializing the implication-shaped theorem still forces the disproved convexity branch.
    exact helperForProposition_36_4_4_textbookZeroIterate_epigraph_not_convex hSpecialized.1

/-- Helper for Proposition 36.4.4: the implication-shaped textbook theorem type is empty under
the current section-local `_*^*` convention. -/
lemma helperForProposition_36_4_4_textbookTargetType_isEmpty :
    IsEmpty
      (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsEpigraphConvexBifunction (m := m) (n := n) F →
            IsEpigraphConvexBifunction (m := m) (n := n)
              (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) ∧
              bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n)
                  (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) =
                bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F =
                  bifunctionClosure F) :=
  by
    refine ⟨?_⟩
    intro hUniversal
    -- The contradiction helper already packages the constant-zero specialization.
    exact helperForProposition_36_4_4_textbookUniversalTarget_fails hUniversal

/-- Helper for Proposition 36.4.4: the exact theorem signature with the convexity premise written
as an explicit argument is already empty under the current textbook `_*^*` convention. -/
lemma helperForProposition_36_4_4_textbookExactTheoremSignature_isEmpty :
    IsEmpty
      (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
          (hF : IsEpigraphConvexBifunction (m := m) (n := n) F),
          IsEpigraphConvexBifunction (m := m) (n := n)
            (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) ∧
            bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n)
                (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) =
              bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F =
                  bifunctionClosure F) :=
  by
    refine ⟨?_⟩
    intro hTheorem
    have hUniversal :
        ∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsEpigraphConvexBifunction (m := m) (n := n) F →
            IsEpigraphConvexBifunction (m := m) (n := n)
              (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) ∧
              bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n)
                  (bifunctionInverseEuclideanAdjointTextbook (m := m) (n := n) F) =
                bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F ∧
                bifunctionEuclideanBiconjugateTextbook (m := m) (n := n) F =
                  bifunctionClosure F := by
      intro m n F hF
      -- Repackage the explicit-premise theorem into the implication-shaped theorem type.
      exact hTheorem (m := m) (n := n) F hF
    -- The implication-shaped textbook theorem type is already empty by the same constant-zero
    -- counterexample, so the explicit-premise signature is empty as well.
    exact helperForProposition_36_4_4_textbookTargetType_isEmpty.false hUniversal

/-- Proposition 36.4.4: let `F` be a canonical convex bifunction and explicitly supply the
canonical concave orientation of its inverse `F_*`. Then
`F_*^* = adjointOfConcaveBifunction F_*` is convex. Moreover its inverse has a canonical concave
orientation for which the next adjoint is the canonical convex bifunction closure of `F`; this is
the packaged form of `(F_*^*)_*^* = F^{**} = cl F`. -/
theorem bifunctionInverseAdjoint_convex_and_iterate_eq_biconjugate_and_closure
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hFconv : ConvexBifunction F)
    (hInvConc : ConcaveBifunction (bifunctionInverse F)) :
    let H := adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩
    ConvexBifunction H ∧
      ∃ hHInvConc : ConcaveBifunction (bifunctionInverse H),
        adjointOfConcaveBifunction ⟨bifunctionInverse H, hHInvConc⟩ =
          convexBifunctionClosure F := by
  let H := adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩
  have hHConv : ConvexBifunction H := by
    exact (adjointOfConcaveBifunction_closedConvex ⟨bifunctionInverse F, hInvConc⟩).1
  have hComm :
      H = bifunctionInverse (adjointOfConvexBifunction ⟨F, hFconv⟩) := by
    exact (bifunctionInverse_adjoint_commutes F).1 hFconv hInvConc
  have hInverseH :
      bifunctionInverse H = adjointOfConvexBifunction ⟨F, hFconv⟩ := by
    rw [hComm]
    funext x u
    simp [bifunctionInverse]
  have hInverseHConc : ConcaveBifunction (bifunctionInverse H) := by
    rw [hInverseH]
    exact (adjointOfConvexBifunctionAsConcave ⟨F, hFconv⟩).2
  refine ⟨hHConv, hInverseHConc, ?_⟩
  have hBiadjoint :
      biadjointOfConvexBifunction ⟨F, hFconv⟩ = convexBifunctionClosure F :=
    helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle
      (F := F) hFconv
  rw [← hBiadjoint]
  unfold biadjointOfConvexBifunction
  congr 1
  exact Subtype.ext hInverseH

end Section36
end Chap07
