/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part14

section Chap06
section Section30

/-- The Lagrangian of a convex program associated with `F`, obtained by minimizing
`u ↦ F(u, x) + ⟪u, u*⟫` over perturbations `u`. -/
noncomputable def lagrangianOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar x =>
    sInf (Set.range fun u : Fin m → ℝ => F.1 u x + (((u ⬝ᵥ uStar : ℝ) : EReal)))

/-- A pair `(u*, x)` is a saddle point of the Lagrangian of the convex program associated with
`F` when `u*` maximizes `L(·, x)` and `x` minimizes `L(u*, ·)`. -/
def IsSaddlePointOfConvexProgramLagrangian {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ uStar' : Fin m → ℝ,
    lagrangianOfConvexProgram F uStar' x ≤ lagrangianOfConvexProgram F uStar x) ∧
    ∀ x' : Fin n → ℝ,
      lagrangianOfConvexProgram F uStar x ≤ lagrangianOfConvexProgram F uStar x'

-- Proof sketch: combine Theorem 6.30.16 with the saddle-point criterion from Section 29 and the
-- primal-dual value identities of Corollary 6.30.2. Normality plus optimality of `x̄` and `ū*`
-- identifies `F(0, x̄)` and `F*(0, ū*)` with the primal and dual values; the weak-duality
-- inequality then gives condition (c), and conversely condition (c) forces equality of the
-- values, yielding the final equality assertion as well as the normality and saddle-point
-- statements.
/-- Helper for Corollary 6.30.4: weak duality bounds each dual zero-slice value by each primal
zero-slice value. -/
lemma helperForCorollary_6_30_4_dualZeroSlice_le_primalZeroSlice
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ) :
    adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar ≤ F.1 0 xBar := by
  have hWeakDuality :=
    helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  -- Compare the chosen dual slice and primal slice through the global weak-duality sandwich.
  calc
    adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar ≤
        sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) := by
            exact le_sSup ⟨uBarStar, rfl⟩
    _ ≤ sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := hWeakDuality
    _ ≤ F.1 0 xBar := by
          exact sInf_le ⟨xBar, rfl⟩

/-- Helper for Corollary 6.30.4: the displayed inequality in clause `(c)` already forces
equality, because weak duality gives the opposite inequality. -/
lemma helperForCorollary_6_30_4_valueInequality_forces_equality
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ) :
    F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
      F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := by
  intro hForward
  have hBackward :
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar ≤ F.1 0 xBar :=
    helperForCorollary_6_30_4_dualZeroSlice_le_primalZeroSlice
      (F := F) xBar uBarStar
  -- Clause `(c)` provides one inequality, and weak duality supplies the reverse one.
  exact le_antisymm hForward hBackward

/-- Helper for Corollary 6.30.4: evaluating the Section 30.1 primal-inconsistency witness at
`u = 1` produces the range value `⊥` used to bound the Lagrangian infimum. -/
lemma helperForCorollary_6_30_4_counterexample_eval_at_one_eq_bot
    (uStar : Fin 1 → ℝ) (x : Fin 0 → ℝ) :
    helperForCorollary_6_30_1_primalInconsistencyCounterexample (fun _ : Fin 1 => (1 : ℝ)) x +
        (((((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ uStar : ℝ) : EReal))) = (⊥ : EReal) := by
  -- The witness is already `⊥` at any `u` with `u 0 ≥ 1`, and adding the finite dot-product
  -- term cannot change the bottom value in `EReal`.
  simp [helperForCorollary_6_30_1_primalInconsistencyCounterexample]

/-- Helper for Corollary 6.30.4: for the Section 30.1 primal-inconsistency witness, the convex
program Lagrangian is identically `⊥` at the unique primal point. -/
lemma helperForCorollary_6_30_4_counterexample_lagrangian_eq_bot
    (uStar : Fin 1 → ℝ) :
    lagrangianOfConvexProgram
        ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
        uStar (fun i : Fin 0 => False.elim (Fin.elim0 i)) = (⊥ : EReal) := by
  -- Evaluating the infimum at the graph point `u = 1`, where the witness already equals `⊥`,
  -- forces the whole Lagrangian value to `⊥`.
  apply le_antisymm
  · -- The range element at `u = 1` is already `⊥`, so the infimum cannot exceed `⊥`.
    refine sInf_le ?_
    refine ⟨(fun _ : Fin 1 => (1 : ℝ)), ?_⟩
    simpa using
      helperForCorollary_6_30_4_counterexample_eval_at_one_eq_bot
        (uStar := uStar) (x := (fun i : Fin 0 => False.elim (Fin.elim0 i)))
  · exact bot_le

/-- Helper for Corollary 6.30.4: the Section 30.1 primal-inconsistency witness has a saddle point
for the convex-program Lagrangian. -/
lemma helperForCorollary_6_30_4_counterexample_isSaddle :
    IsSaddlePointOfConvexProgramLagrangian
      ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
      (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)) := by
  constructor
  · intro uStar'
    -- The Lagrangian is already constantly `⊥`, so every multiplier satisfies the left saddle
    -- inequality.
    rw [helperForCorollary_6_30_4_counterexample_lagrangian_eq_bot uStar']
    rw [helperForCorollary_6_30_4_counterexample_lagrangian_eq_bot (fun _ : Fin 1 => (0 : ℝ))]
  · intro x'
    -- The same constant-`⊥` collapse makes the right saddle inequality automatic as well.
    rw [helperForCorollary_6_30_4_counterexample_lagrangian_eq_bot (fun _ : Fin 1 => (0 : ℝ))]
    have hx' :
        lagrangianOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            (fun _ : Fin 1 => (0 : ℝ)) x' = (⊥ : EReal) := by
      -- The same `u = 1` witness collapses every fixed-`x` Lagrangian value to `⊥`.
      apply le_antisymm
      · -- The infimum is bounded above by the range element at `u = 1`, which is `⊥`.
        refine sInf_le ?_
        refine ⟨(fun _ : Fin 1 => (1 : ℝ)), ?_⟩
        simpa using
          helperForCorollary_6_30_4_counterexample_eval_at_one_eq_bot
            (uStar := (fun _ : Fin 1 => (0 : ℝ))) (x := x')
      · exact bot_le
    rw [hx']

/-- Helper for Corollary 6.30.4: the Section 30.1 primal-inconsistency witness falsifies clause
`(c)`, since its primal zero-slice is `⊤` while every dual zero-slice is `⊥`. -/
lemma helperForCorollary_6_30_4_counterexample_valueInequality_fails :
    ¬ (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
          (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
        adjointOfConvexBifunction
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          0 (fun _ : Fin 1 => (0 : ℝ))) := by
  intro hIneq
  -- Rewriting the witness values turns clause `(c)` into the contradiction `⊤ ≤ ⊥`.
  simp [helperForCorollary_6_30_1_primalInconsistencyCounterexample] at hIneq
  have hGraphBot :
      helperForCorollary_6_30_1_primalInconsistencyCounterexample
          (fun _ : Fin 1 => (1 : ℝ)) (0 : Fin 0 → ℝ) = (⊥ : EReal) :=
    -- The counterexample bifunction was designed so its graph attains `⊥` at `u = 1`.
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_graph_attains_bot
  have hAdjBot :
      adjointOfConvexBifunction
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          0 (fun _ : Fin 1 => (0 : ℝ)) = (⊥ : EReal) :=
    helperForCorollary_6_30_1_graphBot_forces_adjoint_eq_bot
      (F := ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩)
      (u := fun _ : Fin 1 => (1 : ℝ)) (x := (0 : Fin 0 → ℝ))
      (hBot := hGraphBot)
      (0 : Fin 0 → ℝ) (fun _ : Fin 1 => (0 : ℝ))
  have hAdjBot' :
      adjointOfConvexBifunction
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          ![] (fun _ : Fin 1 => (0 : ℝ)) = (⊥ : EReal) := by
    simpa using hAdjBot
  rw [hAdjBot'] at hIneq
  simp at hIneq

/-- Helper for Corollary 6.30.4: the Section 30.1 primal-inconsistency witness realizes clause
`(b)` while simultaneously refuting clause `(c)`. -/
lemma helperForCorollary_6_30_4_counterexample_clauseB_and_not_clauseC :
    IsSaddlePointOfConvexProgramLagrangian
        ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
        (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∧
      ¬ (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))) := by
  constructor
  · -- The left conjunct records the explicit saddle witness already proved above.
    exact helperForCorollary_6_30_4_counterexample_isSaddle
  · -- The right conjunct packages the failure of clause `(c)` for the same witness.
    exact helperForCorollary_6_30_4_counterexample_valueInequality_fails

/-- Helper for Corollary 6.30.4: in any three-clause `List.TFAE`, the second clause cannot hold
while the third clause fails, because the `2 -> 3` edge is part of the package. -/
lemma helperForCorollary_6_30_4_not_tfae_of_secondClause_and_not_thirdClause
    {P Q R : Prop} (hSecond : Q) (hNotThird : ¬ R) :
    ¬ List.TFAE [P, Q, R] := by
  intro hTFAE
  -- Read the `Q -> R` edge from the `List.TFAE` package and contradict the assumed failure of
  -- the third clause.
  exact hNotThird ((hTFAE.out 1 2).1 hSecond)

/-- Helper for Corollary 6.30.4: any claimed `List.TFAE` for the Section 30.1
primal-inconsistency witness would force clause `(c)` from the explicit saddle witness in
clause `(b)`. -/
lemma helperForCorollary_6_30_4_counterexample_tfae_forces_clauseC
    (hTFAE : List.TFAE
      [IsNormalConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        IsNormalDualProgramOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
          primalOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun _ : Fin 1 => (0 : ℝ)) ∈
          dualOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
        IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))]) :
    helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
        (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
      adjointOfConvexBifunction
        ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
        0 (fun _ : Fin 1 => (0 : ℝ)) := by
  -- Read the `(b) → (c)` edge from the claimed `List.TFAE` and apply it to the explicit saddle
  -- witness already isolated above.
  exact (hTFAE.out 1 2).1 helperForCorollary_6_30_4_counterexample_isSaddle

/-- Helper for Corollary 6.30.4: on the Section 30.1 primal-inconsistency witness, the saddle
point condition from clause `(b)` does not imply the value inequality from clause `(c)`. -/
lemma helperForCorollary_6_30_4_counterexample_saddle_does_not_imply_clauseC :
    ¬ (IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)) →
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))) := by
  intro hImp
  have hClauseBandNotClauseC :
      IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∧
        ¬ (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ))) :=
    helperForCorollary_6_30_4_counterexample_clauseB_and_not_clauseC
  -- Applying the implication to the explicit saddle witness would force the impossible
  -- inequality `⊤ ≤ ⊥`.
  exact hClauseBandNotClauseC.2 (hImp hClauseBandNotClauseC.1)

/-- Helper for Corollary 6.30.4: the formalized `List.TFAE` statement is refuted by the existing
Section 30.1 primal-inconsistency witness, which has a saddle point but fails clause `(c)`. -/
lemma helperForCorollary_6_30_4_counterexample_refutes_tfae :
    ¬ List.TFAE
      [IsNormalConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        IsNormalDualProgramOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
          primalOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun _ : Fin 1 => (0 : ℝ)) ∈
          dualOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
        IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))] := by
  -- The counterexample already supplies clause `(b)` and refutes clause `(c)`, so the generic
  -- three-clause `List.TFAE` contradiction applies directly.
  exact
    helperForCorollary_6_30_4_not_tfae_of_secondClause_and_not_thirdClause
      helperForCorollary_6_30_4_counterexample_isSaddle
      helperForCorollary_6_30_4_counterexample_valueInequality_fails

/-- Helper for Corollary 6.30.4: even the universal `List.TFAE` package alone is false in the
current formalization, before adding the equality-after-inequality clause. -/
lemma helperForCorollary_6_30_4_universalTfaeFalse :
    ¬ (∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar]) := by
  intro hUniversal
  have hAtWitness :=
    hUniversal
      ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
      (fun i : Fin 0 => False.elim (Fin.elim0 i)) (fun _ : Fin 1 => (0 : ℝ))
  -- Specializing the universal `List.TFAE` claim to the explicit witness produces the same
  -- impossible `(b) → (c)` implication isolated by the counterexample lemmas above.
  exact helperForCorollary_6_30_4_counterexample_refutes_tfae hAtWitness

/-- Helper for Corollary 6.30.4: the full conclusion of the current corollary already fails at
the Section 30.1 primal-inconsistency witness, because its `List.TFAE` component is refuted by
the existing saddle-point counterexample. -/
lemma helperForCorollary_6_30_4_counterexample_refutes_fullConclusion :
    ¬ (List.TFAE
        [IsNormalConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          IsNormalDualProgramOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
            primalOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun _ : Fin 1 => (0 : ℝ)) ∈
            dualOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
          IsSaddlePointOfConvexProgramLagrangian
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ))] ∧
        (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ)) →
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) =
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ)))) := by
  intro hFull
  -- The equality-after-inequality clause is irrelevant once the `List.TFAE` package is already
  -- contradicted by the saddle-point witness.
  exact helperForCorollary_6_30_4_counterexample_refutes_tfae hFull.1

/-- Helper for Corollary 6.30.4: the exact conjunction claimed by the corollary already fails
when specialized to the Section 30.1 primal-inconsistency witness and the zero multiplier. -/
lemma helperForCorollary_6_30_4_counterexample_refutes_specializedConclusion :
    ¬ (List.TFAE
        [IsNormalConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          IsNormalDualProgramOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
            primalOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun _ : Fin 1 => (0 : ℝ)) ∈
            dualOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
          IsSaddlePointOfConvexProgramLagrangian
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ))] ∧
        (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ)) →
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) =
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ)))) := by
  -- This is exactly the previously isolated full-conclusion counterexample for Corollary 6.30.4.
  exact helperForCorollary_6_30_4_counterexample_refutes_fullConclusion

/-- Helper for Corollary 6.30.4: adjoining the equality-after-inequality implication cannot
repair a universally false `List.TFAE` package. -/
lemma helperForCorollary_6_30_4_universalTfaeFalse_forces_targetStatementFalse
    (hUniversalTfae :
      ¬ (∀ {m n : ℕ}
          (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
          (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
            List.TFAE
              [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
                IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
                xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
                uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
                IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
                F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar])) :
    ¬ (∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar] ∧
            (F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
              F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar)) := by
  intro hUniversalFull
  -- Forgetting the extra implication recovers the already-refuted universal `List.TFAE`
  -- statement, so the larger conjunction fails for the same witness.
  exact hUniversalTfae (fun {m n} F xBar uBarStar => (hUniversalFull F xBar uBarStar).1)

/-- Helper for Corollary 6.30.4: specializing the full corollary statement to the Section 30.1
primal-inconsistency witness reproduces the already isolated specialized conjunction. -/
lemma helperForCorollary_6_30_4_specialize_fullTarget_to_counterexample
    (hTarget :
      ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar] ∧
            (F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
              F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar)) :
    List.TFAE
      [IsNormalConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        IsNormalDualProgramOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
          primalOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun _ : Fin 1 => (0 : ℝ)) ∈
          dualOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
        IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))] ∧
      (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
          (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
        adjointOfConvexBifunction
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          0 (fun _ : Fin 1 => (0 : ℝ)) →
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) =
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))) := by
  -- Instantiating the universal theorem at the explicit witness gives the exact specialized
  -- statement already singled out by the counterexample lemmas.
  exact
    hTarget
      ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
      (fun i : Fin 0 => False.elim (Fin.elim0 i)) (fun _ : Fin 1 => (0 : ℝ))

/-- Helper for Corollary 6.30.4: any proof of the full universal corollary statement collapses
when specialized to the Section 30.1 primal-inconsistency witness. -/
lemma helperForCorollary_6_30_4_fullTarget_specialization_contradiction
    (hTarget :
      ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar] ∧
            (F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
              F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar)) :
    False := by
  have hSpecialized :
      List.TFAE
        [IsNormalConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          IsNormalDualProgramOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
            primalOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
          (fun _ : Fin 1 => (0 : ℝ)) ∈
            dualOptimalSolutionSetOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
          IsSaddlePointOfConvexProgramLagrangian
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ))] ∧
        (helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ)) →
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
              (fun i : Fin 0 => False.elim (Fin.elim0 i)) =
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 (fun _ : Fin 1 => (0 : ℝ))) :=
    helperForCorollary_6_30_4_specialize_fullTarget_to_counterexample hTarget
  -- The specialized conjunction is exactly the false witness already isolated above.
  exact helperForCorollary_6_30_4_counterexample_refutes_specializedConclusion hSpecialized

/-- Helper for Corollary 6.30.4: the universal target statement is false in the current
formalization, because the Section 30.1 primal-inconsistency witness satisfies clause `(b)` but
not clause `(c)`. -/
lemma helperForCorollary_6_30_4_targetStatementFalse :
    ¬ (∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar] ∧
            (F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
              F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar)) := by
  intro hTarget
  -- Specializing the full theorem to the explicit Section 30.1 witness reproduces the false
  -- specialized conjunction proved above, so the universal statement cannot hold.
  exact
    helperForCorollary_6_30_4_fullTarget_specialization_contradiction hTarget

/-- Helper for Corollary 6.30.4: the universal three-clause `List.TFAE` package asserted by the
naive formalization is refuted in-file by the Section 30.1 primal-inconsistency witness, so the
universal statement cannot hold as written. -/
lemma helperForCorollary_6_30_4_tfae_normality_saddle_value_inequality :
    ¬ (∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
        (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ),
          List.TFAE
            [IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
              IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
              uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩,
              IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar,
              F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar]) := by
  -- Route correction: the previous pointwise `List.TFAE` helper was unprovable because an explicit
  -- closed-convex counterexample satisfies clause `(b)` but refutes clause `(c)`. The file already
  -- packages this as `helperForCorollary_6_30_4_universalTfaeFalse`, so we record that fact here.
  exact helperForCorollary_6_30_4_universalTfaeFalse

/-- Helper for Corollary 6.30.4: the Section 30.1 primal-inconsistency witness refutes the
specialized three-clause `List.TFAE` package. -/
lemma helperForCorollary_6_30_4_counterexample_refutes_tfae_normality_saddle_value_inequality :
    ¬ List.TFAE
      [IsNormalConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        IsNormalDualProgramOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun i : Fin 0 => False.elim (Fin.elim0 i)) ∈
          primalOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ ∧
        (fun _ : Fin 1 => (0 : ℝ)) ∈
          dualOptimalSolutionSetOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩,
        IsSaddlePointOfConvexProgramLagrangian
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
          (fun _ : Fin 1 => (0 : ℝ)) (fun i : Fin 0 => False.elim (Fin.elim0 i)),
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0
            (fun i : Fin 0 => False.elim (Fin.elim0 i)) ≤
          adjointOfConvexBifunction
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
            0 (fun _ : Fin 1 => (0 : ℝ))] := by
  -- This is exactly the previously isolated `List.TFAE` refutation lemma.
  exact helperForCorollary_6_30_4_counterexample_refutes_tfae

/-- Corollary 6.30.4 (Corollary 30.5.1): let `F` be a closed convex bifunction from `ℝ^m` to
`ℝ^n`, and let `(P)` be the convex program associated with `F`. In the current formalization,
the universally quantified `TFAE` package from the textbook is too coarse because the saddle
clause admits a closed improper witness that violates the zero-slice inequality. The corrected
Lean boundary keeps the implications supported by the ordinary convex-program package:

* if normality holds for `(P)` and `(P*)` and `x̄`, `ū*` are primal and dual optimizers, then
  `(ū*, x̄)` is a saddle point of the Lagrangian of `(P)`;
* under the same optimality-and-normality assumptions, `F(0, x̄) ≤ F*(0, ū*)`;
* if the displayed inequality holds, then equality holds automatically by weak duality. -/
theorem optimal_primal_dual_pair_tfae_normality_saddle_value_inequality {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (xBar : Fin n → ℝ) (uBarStar : Fin m → ℝ) :
    ((IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
        IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) →
      IsSaddlePointOfConvexProgramLagrangian ⟨F.1, F.2.1⟩ uBarStar xBar) ∧
    ((IsNormalConvexProgram ⟨F.1, F.2.1⟩ ∧
        IsNormalDualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        xBar ∈ primalOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩ ∧
        uBarStar ∈ dualOptimalSolutionSetOfConvexProgram ⟨F.1, F.2.1⟩) →
      F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar) ∧
    (F.1 0 xBar ≤ adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar →
      F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hNormalOpt
    -- This is the saddle-point direction from the textbook corollary package.
    -- The present file isolates the false converse `(b) → (c)`, not this forward implication.
    rcases hNormalOpt with ⟨hNormalP, _hNormalD, hxOpt, huOpt⟩
    -- First identify the common primal-dual optimal value at `0` from primal normality.
    have hCor := corollary_6_30_2_2 (F := F)
    rcases hCor with ⟨hClosureEqDual, _hDualEqSup, _hClosedProperBranch, hPrimalEqInf, _hWeak⟩
    have hValueEq :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      -- Primal normality is exactly `cl p (0) = p (0)`, and Corollary 6.30.2 identifies
      -- `cl p (0)` with the dual program value at `0`.
      calc
        convexProgramAssociatedWith F.1 0 =
            convexClosure (convexProgramAssociatedWith F.1) 0 := by
              simpa [IsNormalConvexProgram] using hNormalP.symm
        _ = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := hClosureEqDual
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := rfl
    -- Next rewrite primal optimality of `xBar` as `F(0, xBar) = v(P)`.
    have hxLowerBound : ∀ x : Fin n → ℝ, F.1 0 xBar ≤ F.1 0 x := by
      have hxMin : xBar ∈ minimumSetEReal (F.1 0) := by
        simpa [primalOptimalSolutionSetOfConvexProgram] using hxOpt
      -- Membership in the minimum set means `xBar` is pointwise minimal.
      exact
        (helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound (f := F.1 0)
              (x := xBar)).1 hxMin
    have hxEqPrimalValue : F.1 0 xBar = convexProgramAssociatedWith F.1 0 := by
      -- Compare with the infimum formula for the primal value.
      have hxEqInf : F.1 0 xBar = sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
        apply le_antisymm
        · refine le_sInf ?_
          rintro y ⟨x, rfl⟩
          exact hxLowerBound x
        · refine sInf_le ?_
          exact ⟨xBar, rfl⟩
      calc
        F.1 0 xBar = sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := hxEqInf
        _ = convexProgramAssociatedWith F.1 0 := by
              simpa using hPrimalEqInf.symm
    -- Dual optimality of `uBarStar` is exactly `F*(0, uBarStar) = v(P*)`.
    have huEqDualValue :
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := huOpt
    -- Collect the common primal-dual value at the optimizing pair.
    have hObjectiveEqDualObjective :
        F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := by
      calc
        F.1 0 xBar = convexProgramAssociatedWith F.1 0 := hxEqPrimalValue
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := hValueEq
        _ = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := huEqDualValue.symm
    -- The saddle inequalities follow from squeezing the Lagrangian between the global adjoint
    -- value and the primal slice value at `0`.
    have hAdjLeLagrangian :
        ∀ x : Fin n → ℝ,
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar ≤
            lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar x := by
      intro x
      -- The adjoint is an infimum over all pairs `(u, x')`, hence it is bounded above by the
      -- restricted infimum over `u` at any fixed `x`.
      unfold adjointOfConvexBifunction lagrangianOfConvexProgram
      -- Compare the two `sInf` values by showing the adjoint infimum lies below every element
      -- in the restricted range.
      refine le_sInf ?_
      rintro y ⟨u, rfl⟩
      -- Witness the adjoint range at the specific pair `(u, x)`.
      have hmem :
          (F.1 u x - (((x ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal)) + (((u ⬝ᵥ uBarStar : ℝ) : EReal))) ∈
            Set.range (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              F.1 p.1 p.2 - (((p.2 ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal)) +
                (((p.1 ⬝ᵥ uBarStar : ℝ) : EReal))) := by
        refine ⟨(u, x), ?_⟩
        simp
      -- Now apply the defining property of `sInf` with that explicit range member.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (sInf_le hmem)
    have hLagrangianLePrimalSlice :
        ∀ (uStar : Fin m → ℝ) (x : Fin n → ℝ),
          lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uStar x ≤ F.1 0 x := by
      intro uStar x
      -- Testing the infimum at `u = 0` yields the upper bound by the unperturbed slice.
      unfold lagrangianOfConvexProgram
      have hmem :
          (F.1 (0 : Fin m → ℝ) x + (((0 : Fin m → ℝ) ⬝ᵥ uStar : ℝ) : EReal)) ∈
            Set.range (fun u : Fin m → ℝ => F.1 u x + (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
        refine ⟨(0 : Fin m → ℝ), rfl⟩
      simpa using (sInf_le hmem)
    have hLagrangianAtOpt :
        lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar = F.1 0 xBar := by
      -- The adjoint lower bound and the `u = 0` upper bound squeeze the Lagrangian to the
      -- common primal-dual objective value.
      apply le_antisymm
      · exact hLagrangianLePrimalSlice uBarStar xBar
      · calc
          F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar :=
            hObjectiveEqDualObjective
          _ ≤ lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar :=
            hAdjLeLagrangian xBar
    have hLagrangianAtOpt_eq_adjoint :
        lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar =
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := by
      calc
        lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar = F.1 0 xBar :=
          hLagrangianAtOpt
        _ = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar :=
          hObjectiveEqDualObjective
    -- Assemble the saddle point package from the two comparison inequalities.
    refine And.intro ?_ ?_
    · intro uBarStar'
      -- Any multiplier gives `L(u*', xBar) ≤ F(0, xBar) = L(uBarStar, xBar)`.
      calc
        lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar' xBar ≤ F.1 0 xBar := by
          exact hLagrangianLePrimalSlice uBarStar' xBar
        _ = lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar := by
          simpa using hLagrangianAtOpt.symm
    · intro x'
      -- The maximizing multiplier `uBarStar` pins the saddle value to the global adjoint value,
      -- which is a lower bound for `L(uBarStar, x')` at every `x'`.
      calc
        lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar xBar =
            adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := hLagrangianAtOpt_eq_adjoint
        _ ≤ lagrangianOfConvexProgram ⟨F.1, F.2.1⟩ uBarStar x' := hAdjLeLagrangian x'
  · intro hNormalOpt
    -- This is the value-inequality consequence of the optimality-and-normality hypotheses.
    -- The formal development still routes it through Theorems 6.30.17 and 6.30.19.
    rcases hNormalOpt with ⟨hNormalP, _hNormalD, hxOpt, huOpt⟩
    -- Under primal normality, Corollary 6.30.2 identifies `v(P)` with `v(P*)`.
    have hCor := corollary_6_30_2_2 (F := F)
    rcases hCor with ⟨hClosureEqDual, _hDualEqSup, _hClosedProperBranch, hPrimalEqInf, _hWeak⟩
    have hValueEq :
        convexProgramAssociatedWith F.1 0 =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := by
      calc
        convexProgramAssociatedWith F.1 0 =
            convexClosure (convexProgramAssociatedWith F.1) 0 := by
              simpa [IsNormalConvexProgram] using hNormalP.symm
        _ = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := hClosureEqDual
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := rfl
    -- Convert primal optimality into `F(0, xBar) = v(P)`.
    have hxLowerBound : ∀ x : Fin n → ℝ, F.1 0 xBar ≤ F.1 0 x := by
      have hxMin : xBar ∈ minimumSetEReal (F.1 0) := by
        simpa [primalOptimalSolutionSetOfConvexProgram] using hxOpt
      exact
        (helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound (f := F.1 0)
              (x := xBar)).1 hxMin
    have hxEqPrimalValue : F.1 0 xBar = convexProgramAssociatedWith F.1 0 := by
      have hxEqInf : F.1 0 xBar = sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
        apply le_antisymm
        · refine le_sInf ?_
          rintro y ⟨x, rfl⟩
          exact hxLowerBound x
        · refine sInf_le ?_
          exact ⟨xBar, rfl⟩
      calc
        F.1 0 xBar = sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := hxEqInf
        _ = convexProgramAssociatedWith F.1 0 := by
              simpa using hPrimalEqInf.symm
    -- Dual optimality says `F*(0, uBarStar) = v(P*)`.
    have huEqDualValue :
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar =
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := huOpt
    -- Putting the equalities together upgrades weak duality to the displayed inequality.
    have hEq : F.1 0 xBar = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := by
      calc
        F.1 0 xBar = convexProgramAssociatedWith F.1 0 := hxEqPrimalValue
        _ = dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ := hValueEq
        _ = adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uBarStar := huEqDualValue.symm
    exact le_of_eq hEq
  · exact
      helperForCorollary_6_30_4_valueInequality_forces_equality
        (F := F) xBar uBarStar

end Section30
end Chap06
