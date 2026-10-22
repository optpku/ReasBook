/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part8

section Chap06
section Section30


/-- Helper for Corollary 6.30.1: the dual program is inconsistent exactly when some primal slice
has value `⊥`. -/
lemma helperForCorollary_6_30_1_dualProgram_eq_bot_iff_exists_primalSlice_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) ↔
      ∃ u : Fin m → ℝ, convexProgramAssociatedWith F.1 u = (⊥ : EReal) := by
  constructor
  · intro hDualBot
    by_contra hNoSliceBot
    have hNoBot : ∀ u : Fin m → ℝ, convexProgramAssociatedWith F.1 u ≠ (⊥ : EReal) := by
      intro u hu
      exact hNoSliceBot ⟨u, hu⟩
    by_cases hProper : ProperConvexBifunction F.1
    · exact
        (helperForCorollary_6_30_1_dualProgram_ne_bot_of_closed_proper_no_primalSlice_bot
          (F := F) hProper hNoBot)
          hDualBot
    · exact
        (helperForCorollary_6_30_1_dualProgram_ne_bot_of_closed_not_proper_no_primalSlice_bot
          (F := F) hProper hNoBot)
          hDualBot
  · rintro ⟨u, hSliceBot⟩
    have hClosureBot :
        convexClosure (convexProgramAssociatedWith F.1) = fun _ => (⊥ : EReal) :=
      convexFunctionClosure_eq_bot_of_exists_bot
        (f := convexProgramAssociatedWith F.1) ⟨u, hSliceBot⟩
    have hdual :=
      helperForCorollary_6_30_1_dualProgram_eq_convexClosure_primalValue_at_zero (F := F)
    -- One primal `⊥` slice collapses the convex closure, hence also the dual program at `0`.
    calc
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩
          = convexClosure (convexProgramAssociatedWith F.1) 0 := hdual
      _ = (⊥ : EReal) := by simpa using congrFun hClosureBot 0

/-- Helper for Corollary 6.30.1: once the graph of a closed convex bifunction attains `⊥`, every
adjoint value is forced down to `⊥`. -/
lemma helperForCorollary_6_30_1_graphBot_forces_adjoint_eq_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hBot : F.1 u x = (⊥ : EReal)) :
    ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
      adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar = (⊥ : EReal) := by
  intro xStar uStar
  apply le_antisymm
  · -- Evaluate the defining infimum at the graph point where `F` already equals `⊥`.
    exact sInf_le ⟨(u, x), by simp [adjointOfConvexBifunction, hBot]⟩
  · -- The reverse inequality is automatic because `⊥` is the least `EReal` value.
    exact bot_le

/-- Helper for Corollary 6.30.1: a single graph-level `⊥` witness forces every dual slice to be
identically `⊥`. -/
lemma helperForCorollary_6_30_1_graphBot_forces_dualSlice_eq_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hBot : F.1 u x = (⊥ : EReal)) :
    ∀ xStar : Fin n → ℝ,
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar = (⊥ : EReal) := by
  intro xStar
  have hAdj :
      ∀ uStar : Fin m → ℝ,
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar = (⊥ : EReal) :=
    helperForCorollary_6_30_1_graphBot_forces_adjoint_eq_bot (F := F) hBot xStar
  -- Unfold the dual perturbation value and rewrite every adjoint term to `⊥`.
  simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, hAdj]

/-- Helper for Corollary 6.30.1: in the closed improper branch, excluding graph-level `⊥`
forces the bifunction to collapse to the constant `⊤` branch. -/
lemma helperForCorollary_6_30_1_closedNotProper_noGraphBot_eq_const_top
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNotProper : ¬ ProperConvexBifunction F.1)
    (hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal)) :
    F.1 = fun _ _ => (⊤ : EReal) := by
  funext u x
  -- Section 30.11 leaves only the `⊤` and `⊥` possibilities at each graph point.
  rcases
      helperForTheorem_6_30_11_convexGraph_values_top_or_bot_of_closed_not_proper
        (F := F.1) F.2 hNotProper (Fin.append u x) with
    hTop | hBot
  · simpa [bifunctionGraphFunction] using hTop
  · exact False.elim (hNoGraphBot u x (by simpa [bifunctionGraphFunction] using hBot))

/-- Helper for Corollary 6.30.1: a one-dimensional improper closed convex bifunction whose
zero slice is `⊤` but whose graph still attains `⊥`. -/
noncomputable def helperForCorollary_6_30_1_primalInconsistencyCounterexample :
    (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal :=
  fun u _ => if (1 : ℝ) ≤ u 0 then (⊥ : EReal) else (⊤ : EReal)

/-- Helper for Corollary 6.30.1: the graph of the bad-statement witness is the threshold profile
`u 0 ≥ 1 ? ⊥ : ⊤`. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_graph_eq
    (z : Fin (1 + 0) → ℝ) :
    bifunctionGraphFunction helperForCorollary_6_30_1_primalInconsistencyCounterexample z =
      if (1 : ℝ) ≤ z 0 then (⊥ : EReal) else (⊤ : EReal) := by
  -- Unfold the graph map and collapse the vacuous `Fin 0` block.
  simp [helperForCorollary_6_30_1_primalInconsistencyCounterexample, bifunctionGraphFunction]

/-- Helper for Corollary 6.30.1: the bad-statement witness is a closed convex bifunction. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex :
    ClosedConvexBifunction helperForCorollary_6_30_1_primalInconsistencyCounterexample := by
  have hConv :
      ConvexBifunction helperForCorollary_6_30_1_primalInconsistencyCounterexample := by
    -- The epigraph is exactly the closed half-space `{(u, μ) | 1 ≤ u 0}`.
    rw [ConvexBifunction, ConvexFunction]
    change
      Convex ℝ
        (epigraph (Set.univ : Set (Fin 1 → ℝ))
          (bifunctionGraphFunction helperForCorollary_6_30_1_primalInconsistencyCounterexample))
    have hlin : IsLinearMap ℝ (fun p : (Fin 1 → ℝ) × ℝ => p.1 0) := by
      refine ⟨?_, ?_⟩ <;> intro <;> simp
    have hEpigraph :
        epigraph (Set.univ : Set (Fin 1 → ℝ))
            (bifunctionGraphFunction helperForCorollary_6_30_1_primalInconsistencyCounterexample) =
          {p : (Fin 1 → ℝ) × ℝ | (1 : ℝ) ≤ p.1 0} := by
      ext p
      constructor
      · intro hpEpi
        by_cases hp : (1 : ℝ) ≤ p.1 0
        · exact hp
        · have hTopLe : (⊤ : EReal) ≤ (p.2 : EReal) := by
            simpa [epigraph, bifunctionGraphFunction,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample, hp] using hpEpi
          simp at hTopLe
      · intro hp
        have hp' : (1 : ℝ) ≤ p.1 0 := by simpa using hp
        refine ⟨by trivial, ?_⟩
        simp [bifunctionGraphFunction,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample, hp']
    rw [hEpigraph]
    exact convex_halfSpace_ge hlin (1 : ℝ)
  refine ⟨hConv, ?_⟩
  refine ⟨by simpa [ConvexBifunction] using hConv, ?_⟩
  -- Every real sublevel set is the same closed half-space `{u | 1 ≤ u 0}`.
  rw [lowerSemicontinuous_iff_closed_sublevel]
  intro α
  have hcont : Continuous (fun z : Fin 1 → ℝ => z 0) := continuous_apply 0
  have hSublevel :
      {z : Fin 1 → ℝ |
          bifunctionGraphFunction helperForCorollary_6_30_1_primalInconsistencyCounterexample z ≤
            (α : EReal)} =
        {z : Fin 1 → ℝ | (1 : ℝ) ≤ z 0} := by
    ext z
    constructor
    · intro hz
      by_cases hOne : (1 : ℝ) ≤ z 0
      · exact hOne
      · have hTopLe : (⊤ : EReal) ≤ (α : EReal) := by
          simpa [bifunctionGraphFunction,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample, hOne] using hz
        simp at hTopLe
    · intro hz
      have hz' : (1 : ℝ) ≤ z 0 := by simpa using hz
      simp [bifunctionGraphFunction,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample, hz']
  rw [hSublevel]
  simpa [Set.preimage, Set.mem_Ici] using
    (isClosed_Ici : IsClosed (Set.Ici (1 : ℝ))).preimage hcont

/-- Helper for Corollary 6.30.1: the bad-statement witness has primal value `⊤` at `u = 0`. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_primalZero_eq_top :
    convexProgramAssociatedWith
        helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
      (⊤ : EReal) := by
  -- There is only one `x : Fin 0 → ℝ`, and at `u = 0` the witness takes the value `⊤`.
  simp [convexProgramAssociatedWith, helperForCorollary_6_30_1_primalInconsistencyCounterexample]

/-- Helper for Corollary 6.30.1: the bad-statement witness attains `⊥` at the graph point
`u = 1`. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_graph_attains_bot :
    helperForCorollary_6_30_1_primalInconsistencyCounterexample
        (fun _ : Fin 1 => (1 : ℝ)) 0 =
      (⊥ : EReal) := by
  -- The threshold branch is active at `u 0 = 1`.
  simp [helperForCorollary_6_30_1_primalInconsistencyCounterexample]

/-- Helper for Corollary 6.30.1: every dual slice of the bad-statement witness is `⊥`. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot :
    ∀ xStar : Fin 0 → ℝ,
      dualPerturbationFunctionOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ xStar =
        (⊥ : EReal) := by
  intro xStar
  -- Reuse the general graph-bot lemma at the witness point `u = 1`.
  simpa using
    helperForCorollary_6_30_1_graphBot_forces_dualSlice_eq_bot
      (F := ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩)
      (u := fun _ : Fin 1 => (1 : ℝ)) (x := 0)
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_graph_attains_bot xStar

/-- Helper for Corollary 6.30.1: the second half of the corollary is false in the current
formalization, as witnessed by the improper closed bifunction above. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondHalf :
    ¬ (convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) ↔
        ∃ xStar : Fin 0 → ℝ,
          dualPerturbationFunctionOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ xStar =
            (⊤ : EReal)) := by
  intro hIff
  have hPrimalTop :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_primalZero_eq_top
  rcases hIff.mp hPrimalTop with ⟨xStar, hDualTop⟩
  have hDualBot :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot xStar
  rw [hDualTop] at hDualBot
  exact top_ne_bot hDualBot

/-- Helper for Corollary 6.30.1: the exact second conjunct of the corollary already fails for the
explicit improper closed witness. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondConjunct :
    ¬ (convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) ↔
        ∃ xStar : Fin 0 → ℝ,
          ¬ HasRealUpperBound
            (adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              xStar)) := by
  let FWitness :
      {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
  intro hSecond
  -- Convert the no-upper-bound statement back to the already-refuted `⊤`-slice formulation.
  apply helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondHalf
  constructor
  · intro hPrimalTop
    rcases hSecond.mp hPrimalTop with ⟨xStar, hNoUpper⟩
    refine ⟨xStar, ?_⟩
    exact
      (helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
        (F := FWitness) xStar).2 hNoUpper
  · rintro ⟨xStar, hDualTop⟩
    refine hSecond.mpr ⟨xStar, ?_⟩
    exact
      (helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
        (F := FWitness) xStar).1 hDualTop

/-- Helper for Corollary 6.30.1: the blocked slice-top characterization already fails for a
bundled closed convex bifunction witness in this file. -/
lemma helperForCorollary_6_30_1_exists_closedConvex_refuting_primalProgram_eq_top_iff_exists_dualSlice_top :
    ∃ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
      ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
          ∃ xStar : Fin 0 → ℝ,
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar = (⊤ : EReal)) := by
  -- Repackage the explicit counterexample in bundled closed-convex form.
  refine ⟨⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩, ?_⟩
  -- The previously proved refutation matches this bundled witness after simplification.
  simpa using
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondHalf

/-- Helper for Corollary 6.30.1: a bundled closed convex witness in this file already refutes the
exact second conjunct appearing in the main corollary. -/
lemma helperForCorollary_6_30_1_exists_closedConvex_refuting_secondConjunct :
    ∃ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
      ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
          ∃ xStar : Fin 0 → ℝ,
            ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar)) := by
  -- Package the explicit counterexample in the exact shape of the corollary's second conjunct.
  refine ⟨⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩, ?_⟩
  -- The new witness-specific refutation already matches the required bundled statement.
  simpa using helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondConjunct

/-- Helper for Corollary 6.30.1: the second conjunct is not universally valid for closed convex
bifunctions, because the bundled witness above already refutes it. -/
lemma helperForCorollary_6_30_1_secondConjunct_not_universally_valid :
    ¬ ∀ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
        (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
          ∃ xStar : Fin 0 → ℝ,
            ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar)) := by
  intro hUniversal
  -- Specialize the claimed universal equivalence to the bundled witness that already refutes it.
  rcases helperForCorollary_6_30_1_exists_closedConvex_refuting_secondConjunct with ⟨F, hRefutes⟩
  exact hRefutes (hUniversal F)

/-- Helper for Corollary 6.30.1: the explicit improper closed witness still satisfies the valid
first equivalence, so the obstruction is isolated to the second conjunct. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_firstConjunct_true_secondConjunct_false :
    (dualProgramOfConvexProgram
        ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ =
      (⊥ : EReal) ↔
      ∃ u : Fin 1 → ℝ,
        ¬ HasRealLowerBound
          (helperForCorollary_6_30_1_primalInconsistencyCounterexample u)) ∧
    ¬ (convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) ↔
        ∃ xStar : Fin 0 → ℝ,
          ¬ HasRealUpperBound
            (adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              xStar)) := by
  let FWitness :
      {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
  constructor
  · -- Specialize the valid first-half characterization to the explicit closed convex witness.
    constructor
    · intro hDualBot
      rcases
        (helperForCorollary_6_30_1_dualProgram_eq_bot_iff_exists_primalSlice_bot
          (F := FWitness)).1 hDualBot with
        ⟨u, hSliceBot⟩
      exact
        ⟨u,
          (helperForCorollary_6_30_1_primalSlice_eq_bot_iff_not_HasRealLowerBound
            (F := FWitness) u).1 hSliceBot⟩
    · rintro ⟨u, hNoLower⟩
      exact
        (helperForCorollary_6_30_1_dualProgram_eq_bot_iff_exists_primalSlice_bot
          (F := FWitness)).2
          ⟨u,
            (helperForCorollary_6_30_1_primalSlice_eq_bot_iff_not_HasRealLowerBound
              (F := FWitness) u).2 hNoLower⟩
  · -- The second conjunct is already refuted by the witness-specific obstruction above.
    exact helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_secondConjunct

/-- Helper for Corollary 6.30.1: the full corollary fails for the improper closed witness, so the
main theorem cannot be completed without repairing its second equivalence. -/
lemma helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_targetCorollary :
    ¬ ((dualProgramOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ =
          (⊥ : EReal) ↔
          ∃ u : Fin 1 → ℝ,
            ¬ HasRealLowerBound
              (helperForCorollary_6_30_1_primalInconsistencyCounterexample u)) ∧
        (convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          (⊤ : EReal) ↔
          ∃ xStar : Fin 0 → ℝ,
            ¬ HasRealUpperBound
              (adjointOfConvexBifunction
                ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                  helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
                xStar))) := by
  have hWitnessProfile :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_firstConjunct_true_secondConjunct_false
  intro hCorollary
  -- The witness isolates the obstruction: the first conjunct is valid, but the second is false.
  exact hWitnessProfile.2 hCorollary.2

/-- Helper for Corollary 6.30.1: there exists a bundled closed convex bifunction in this file
that refutes the full advertised conjunction of the corollary. -/
lemma helperForCorollary_6_30_1_exists_closedConvex_refuting_targetCorollary :
    ∃ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
      ¬ ((dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) ↔
            ∃ u : Fin 1 → ℝ, ¬ HasRealLowerBound (F.1 u)) ∧
          (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
            ∃ xStar : Fin 0 → ℝ,
              ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar))) := by
  -- Bundle the explicit threshold counterexample into the closed-convex sigma type.
  refine ⟨⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩, ?_⟩
  -- The previously proved refutation is exactly the negation needed for this bundled witness.
  simpa using helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_targetCorollary

/-- Helper for Corollary 6.30.1: the full advertised conjunction cannot hold for every closed
convex bifunction, because the bundled witness above already refutes the exact theorem shape. -/
lemma helperForCorollary_6_30_1_targetCorollary_not_universally_valid :
    ¬ ∀ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
        ((dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) ↔
            ∃ u : Fin 1 → ℝ, ¬ HasRealLowerBound (F.1 u)) ∧
          (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
            ∃ xStar : Fin 0 → ℝ,
              ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar))) := by
  intro hUniversal
  -- Specialize the universal corollary claim to the bundled counterexample from this file.
  rcases helperForCorollary_6_30_1_exists_closedConvex_refuting_targetCorollary with ⟨F, hRefutes⟩
  exact hRefutes (hUniversal F)

/-- Helper for Corollary 6.30.1: the advertised corollary shape is not dimension-uniformly valid,
because the same bundled closed convex counterexample already refutes the global statement when
specialized to `m = 1` and `n = 0`. -/
lemma helperForCorollary_6_30_1_globalTargetShape_not_universally_valid :
    ¬ ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}),
          ((dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) ↔
              ∃ u : Fin m → ℝ, ¬ HasRealLowerBound (F.1 u)) ∧
            (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
              ∃ xStar : Fin n → ℝ,
                ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar))) := by
  intro hUniversal
  let FWitness :
      {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
  -- Specialize the claimed dimension-uniform theorem to the explicit counterexample.
  have hAtWitness : ((dualProgramOfConvexProgram ⟨FWitness.1, FWitness.2.1⟩ = (⊥ : EReal) ↔
        ∃ u : Fin 1 → ℝ, ¬ HasRealLowerBound (FWitness.1 u)) ∧
      (convexProgramAssociatedWith FWitness.1 0 = (⊤ : EReal) ↔
        ∃ xStar : Fin 0 → ℝ,
          ¬ HasRealUpperBound
            (adjointOfConvexBifunction ⟨FWitness.1, FWitness.2.1⟩ xStar))) :=
    hUniversal FWitness
  -- The witness-specific refutation already contradicts the specialized global claim.
  simpa [FWitness] using
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_refutes_targetCorollary hAtWitness

-- Proof sketch: use Theorem 6.30.15 to identify the dual objective slice with the concave
-- conjugate of the primal perturbation function and, under closedness, the primal objective
-- slice with the Fenchel conjugate of the dual perturbation function. The dual value is `⊥`
-- exactly when some slice `x ↦ F(u, x)` has infimum `-∞`, i.e. no real lower bound; the primal
-- value at `u = 0` is `⊤` exactly when some adjoint slice `u* ↦ F*(x*, u*)` has supremum `⊤`,
-- i.e. no real upper bound.
/-- Corollary 6.30.1: let `F` be a closed convex bifunction from `ℝ^m` to `ℝ^n`, and let `(P)`
be the convex program associated with `F`. Then the dual program `(P*)` is inconsistent if and
only if there exists `u ∈ ℝ^m` such that the slice `x ↦ F(u, x)` has no real lower bound on
`ℝ^n`. If the graph function never takes the value `-∞`, then conversely `(P)` is inconsistent
if and only if there exists `x* ∈ ℝ^n` such that the adjoint slice `u* ↦ F*(x*, u*)` has no real
upper bound on `ℝ^m`. -/
theorem corollary_6_30_2_1 {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hGraphNeBot : ∀ z : Fin (m + n) → ℝ,
      bifunctionGraphFunction F.1 z ≠ (⊥ : EReal)) :
    (dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) ↔
      ∃ u : Fin m → ℝ, ¬ HasRealLowerBound (F.1 u)) ∧
      (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ↔
        ∃ xStar : Fin n → ℝ,
          ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar)) := by
  constructor
  · -- Convert dual inconsistency into a primal slice with no real lower bound, and conversely.
    constructor
    · intro hDualBot
      rcases
        (helperForCorollary_6_30_1_dualProgram_eq_bot_iff_exists_primalSlice_bot (F := F)).1
          hDualBot with
        ⟨u, hSliceBot⟩
      exact
        ⟨u,
          (helperForCorollary_6_30_1_primalSlice_eq_bot_iff_not_HasRealLowerBound
            (F := F) u).1 hSliceBot⟩
    · rintro ⟨u, hNoLower⟩
      exact
        (helperForCorollary_6_30_1_dualProgram_eq_bot_iff_exists_primalSlice_bot (F := F)).2
          ⟨u,
            (helperForCorollary_6_30_1_primalSlice_eq_bot_iff_not_HasRealLowerBound
              (F := F) u).2 hNoLower⟩
  · let FCvx :
        {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
      ⟨F.1, F.2.1⟩
    let q : (Fin n → ℝ) → EReal :=
      fun xStar => -(dualPerturbationFunctionOfConvexProgram FCvx xStar)
    have hPrimalSlice :
        fenchelConjugate n q = fun x => F.1 0 x := by
      simpa [FCvx, q] using
        helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation
          (F := FCvx) F.2 hGraphNeBot
    constructor
    · intro hPrimalTop
      by_cases hProper : ProperConvexBifunction F.1
      · by_contra hNoWitness
        have hqConv : ConvexFunction q := by
          simpa [q, FCvx, dualPerturbationFunctionOfConvexProgram] using
            (perturbationFunction_concave_and_effectiveDomain_eq_bifunctionDomain
              (G := adjointOfConvexBifunctionAsConcave FCvx)).1
        have hqNoBot : ∀ xStar : Fin n → ℝ, q xStar ≠ (⊥ : EReal) := by
          intro xStar hqBot
          have hDualTop :
              dualPerturbationFunctionOfConvexProgram FCvx xStar = (⊤ : EReal) := by
            have hNeg := congrArg Neg.neg hqBot
            simpa [q] using hNeg
          apply hNoWitness
          refine ⟨xStar, ?_⟩
          have hDualTopForF :
              dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar =
                (⊤ : EReal) := by
            simpa [FCvx] using hDualTop
          exact
            (helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
              (F := F) xStar).1 hDualTopForF
        have hAdjProper :
            ProperConcaveBifunction (m := n) (n := m)
              (adjointOfConvexBifunction FCvx) :=
          ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality F.1).1
            F.2.1).2.1.2 hProper
        rcases hAdjProper.2.1.2 with ⟨z, hz⟩
        let xStar : Fin n → ℝ := fun i => z (Fin.castAdd m i)
        let uStar : Fin m → ℝ := fun j => z (Fin.natAdd n j)
        have hAdjNegNeTop :
            -(adjointOfConvexBifunction FCvx xStar uStar) ≠ (⊤ : EReal) := by
          simpa [bifunctionGraphFunction, xStar, uStar] using hz
        have hqLeAdj : q xStar ≤ -(adjointOfConvexBifunction FCvx xStar uStar) := by
          have hAdjLe :
              adjointOfConvexBifunction FCvx xStar uStar ≤
                dualPerturbationFunctionOfConvexProgram FCvx xStar := by
            unfold dualPerturbationFunctionOfConvexProgram concaveProgramAssociatedWith
            exact le_sSup ⟨uStar, rfl⟩
          simpa [q] using (EReal.neg_le_neg_iff.2 hAdjLe)
        have hqNeTop : q xStar ≠ (⊤ : EReal) := by
          intro hqTop
          apply hAdjNegNeTop
          have hTopLeAdj :
              (⊤ : EReal) ≤ -(adjointOfConvexBifunction FCvx xStar uStar) := by
            simpa [hqTop] using hqLeAdj
          exact top_unique hTopLeAdj
        have hqProper :
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
          have hqConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
            simpa [ConvexFunction] using hqConv
          lift q xStar to ℝ using ⟨hqNeTop, hqNoBot xStar⟩ with r hr
          refine ⟨hqConvOn, ?_, ?_⟩
          · refine ⟨(xStar, r), ?_⟩
            have hqLeR : q xStar ≤ (r : EReal) := by
              simp [hr]
            exact (mem_epigraph_univ_iff (f := q)).2 hqLeR
          · intro y _hy
            exact hqNoBot y
        have hqStarProper :
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n q) :=
          proper_fenchelConjugate_of_proper (n := n) (f := q) hqProper
        have hSliceTop : ∀ x : Fin n → ℝ, F.1 0 x = (⊤ : EReal) := by
          intro x
          apply top_unique
          have hInfLe : convexProgramAssociatedWith F.1 0 ≤ F.1 0 x :=
            sInf_le ⟨x, rfl⟩
          simpa [hPrimalTop] using hInfLe
        rcases hqStarProper.2.1 with ⟨p, hp⟩
        have hpLe : fenchelConjugate n q p.1 ≤ (p.2 : EReal) :=
          (mem_epigraph_univ_iff (f := fenchelConjugate n q)).1 hp
        rw [hPrimalSlice] at hpLe
        change F.1 0 p.1 ≤ (p.2 : EReal) at hpLe
        rw [hSliceTop p.1] at hpLe
        exact (not_top_le_coe p.2) hpLe
      · have hNoGraphBot :
            ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal) := by
          intro u x hBot
          have hGraphBot :
              bifunctionGraphFunction F.1 (Fin.append u x) = (⊥ : EReal) := by
            simpa [bifunctionGraphFunction] using hBot
          exact hGraphNeBot (Fin.append u x) hGraphBot
        have hConstTop : F.1 = fun _ _ => (⊤ : EReal) :=
          helperForCorollary_6_30_1_closedNotProper_noGraphBot_eq_const_top
            (F := F) hProper hNoGraphBot
        have hAdjTop :
            ∀ uStar : Fin m → ℝ,
              adjointOfConvexBifunction FCvx 0 uStar = (⊤ : EReal) := by
          intro uStar
          simp [FCvx, hConstTop, adjointOfConvexBifunction]
        have hDualTop :
            dualPerturbationFunctionOfConvexProgram FCvx 0 = (⊤ : EReal) := by
          simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, hAdjTop]
        refine ⟨0, ?_⟩
        have hDualTopForF :
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 = (⊤ : EReal) := by
          simpa [FCvx] using hDualTop
        exact
          (helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
            (F := F) 0).1 hDualTopForF
    · rintro ⟨xStar, hNoUpper⟩
      have hDualTop :
          dualPerturbationFunctionOfConvexProgram FCvx xStar = (⊤ : EReal) := by
        simpa [FCvx] using
          (helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
            (F := F) xStar).2 hNoUpper
      have hSliceTop : ∀ x : Fin n → ℝ, F.1 0 x = (⊤ : EReal) := by
        intro x
        apply top_unique
        rw [← congrFun hPrimalSlice x]
        unfold fenchelConjugate
        have hTermTop : (((xStar ⬝ᵥ x : ℝ) : EReal) - q xStar) = (⊤ : EReal) := by
          simp [q, hDualTop]
        exact le_sSup ⟨xStar, hTermTop⟩
      apply top_unique
      rw [convexProgramAssociatedWith]
      apply le_sInf
      intro y hy
      rcases hy with ⟨x, rfl⟩
      simpa [hSliceTop x]

/-- Helper for Corollary 6.30.2: for the improper closed witness from Corollary 6.30.1, the dual
perturbation function is identically `⊥`, so its concave closure at `0` is still `⊥`. -/
lemma helperForCorollary_6_30_2_primalInconsistencyCounterexample_concaveClosure_dualAtZero_eq_bot :
    concaveClosure
        (dualPerturbationFunctionOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
      (⊥ : EReal) := by
  have hDualConst :
      dualPerturbationFunctionOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ =
        fun _ : Fin 0 → ℝ => (⊥ : EReal) := by
    -- Every dual slice of the witness was already shown to collapse to `⊥`.
    funext xStar
    exact helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot xStar
  -- Rewrite to the constant `⊥` function and evaluate its concave closure via sign change.
  rw [hDualConst]
  simpa [concaveClosure_eq_neg_convexClosure_neg] using
    congrArg Neg.neg (congrFun (convexFunctionClosure_const_top (n := 0)) (0 : Fin 0 → ℝ))

/-- Helper for Corollary 6.30.2: the improper closed witness already falsifies the theorem's
third displayed identity, since its dual-closure side is `⊥` while its primal value at `0` is
`⊤`. -/
lemma helperForCorollary_6_30_2_primalInconsistencyCounterexample_refutes_thirdConjunct :
    ¬ (concaveClosure
          (dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
        convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0) := by
  intro hThird
  have hConcaveBot :
      concaveClosure
          (dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
        (⊥ : EReal) :=
    helperForCorollary_6_30_2_primalInconsistencyCounterexample_concaveClosure_dualAtZero_eq_bot
  have hPrimalTop :
      convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
        (⊤ : EReal) :=
    helperForCorollary_6_30_1_primalInconsistencyCounterexample_primalZero_eq_top
  -- Substituting the witness-specific values turns the claimed identity into `⊥ = ⊤`.
  rw [hConcaveBot, hPrimalTop] at hThird
  exact top_ne_bot hThird.symm

/-- Helper for Corollary 6.30.2: the explicit closed witness is genuinely improper, because its
graph already attains the forbidden value `⊥`. -/
lemma helperForCorollary_6_30_2_primalInconsistencyCounterexample_not_proper :
    ¬ ProperConvexBifunction
        helperForCorollary_6_30_1_primalInconsistencyCounterexample := by
  intro hProper
  rcases hProper with ⟨_, hProperGraph⟩
  -- Properness forbids `⊥` on the graph, but the threshold witness reaches `⊥` at `u = 1`.
  exact
    (hProperGraph.1.1 (Fin.append (fun _ : Fin 1 => (1 : ℝ)) 0))
      (by
        simpa [bifunctionGraphFunction] using
          helperForCorollary_6_30_1_primalInconsistencyCounterexample_graph_attains_bot)

/-- Helper for Corollary 6.30.2: for the same improper closed witness, the full target
conjunction already fails because its third conjunct is impossible. -/
lemma helperForCorollary_6_30_2_primalInconsistencyCounterexample_refutes_fullTargetConjunction :
    ¬ (convexClosure
          (convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample) 0 =
        dualPerturbationFunctionOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 ∧
        dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 =
          sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) ∧
        concaveClosure
            (dualPerturbationFunctionOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
          convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 ∧
        convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x) ∧
        sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) ≤
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x)) := by
  intro hTarget
  -- The witness obstruction is localized at the third conjunct of the advertised theorem shape.
  exact
    helperForCorollary_6_30_2_primalInconsistencyCounterexample_refutes_thirdConjunct
      hTarget.2.2.1

/-- Helper for Corollary 6.30.2: for the packaged improper closed witness, the other four target
conjuncts are true, so the full conjunction is equivalent to the blocked third identity. -/
lemma helperForCorollary_6_30_2_primalInconsistencyCounterexample_targetConjunction_iff_thirdConjunct :
    (convexClosure
          (convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample) 0 =
        dualPerturbationFunctionOfConvexProgram
          ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
            helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 ∧
        dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 =
          sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) ∧
        concaveClosure
            (dualPerturbationFunctionOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
          convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 ∧
        convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x) ∧
        sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) ≤
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x)) ↔
      concaveClosure
          (dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩) 0 =
        convexProgramAssociatedWith
          helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 := by
  constructor
  · -- Any proof of the full target conjunction already contains the third identity as a component.
    intro hTarget
    exact hTarget.2.2.1
  · intro hThird
    have hFirst :
        convexClosure
            (convexProgramAssociatedWith
              helperForCorollary_6_30_1_primalInconsistencyCounterexample) 0 =
          dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 := by
      have hPrimalSliceBot :
          convexProgramAssociatedWith
              helperForCorollary_6_30_1_primalInconsistencyCounterexample
              (fun _ : Fin 1 => (1 : ℝ)) =
            (⊥ : EReal) := by
        -- At the threshold point `u = 1`, the primal slice is the unique `Fin 0` graph value `⊥`.
        simp [convexProgramAssociatedWith,
          helperForCorollary_6_30_1_primalInconsistencyCounterexample]
      have hClosureBot :
          convexClosure
              (convexProgramAssociatedWith
                helperForCorollary_6_30_1_primalInconsistencyCounterexample) =
            fun _ : Fin 1 → ℝ => (⊥ : EReal) :=
        convexFunctionClosure_eq_bot_of_exists_bot
          (f := convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample)
          ⟨fun _ : Fin 1 => (1 : ℝ), hPrimalSliceBot⟩
      have hDualAtZero :
          dualPerturbationFunctionOfConvexProgram
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 =
            (⊥ : EReal) :=
        helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot 0
      -- Both sides reduce to the same witness-specific `⊥` value at the origin.
      rw [hDualAtZero]
      simpa using congrFun hClosureBot (0 : Fin 1 → ℝ)
    have hSecond :
        dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
              helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩ 0 =
          sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) := by
      -- The second displayed identity is just the definition of the dual perturbation value at `0`.
      simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith]
    have hFourth :
        convexProgramAssociatedWith
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 =
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x) := by
      -- The fourth displayed identity is just the definition of the primal perturbation value at `0`.
      simp [convexProgramAssociatedWith]
    have hFifth :
        sSup (Set.range fun uStar : Fin 1 → ℝ =>
            adjointOfConvexBifunction
              ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
                helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex.1⟩
              0 uStar) ≤
          sInf (Set.range fun x : Fin 0 → ℝ =>
            helperForCorollary_6_30_1_primalInconsistencyCounterexample 0 x) := by
      -- After rewriting the dual side to the witness-specific `⊥`, weak duality is immediate.
      rw [← hSecond]
      rw [helperForCorollary_6_30_1_primalInconsistencyCounterexample_allDualSlices_eq_bot 0]
      exact bot_le
    -- Reassemble the full target conjunction from the four unconditional witness identities and
    -- the supplied third conjunct.
    exact ⟨hFirst, hSecond, hThird, hFourth, hFifth⟩

/-- Helper for Corollary 6.30.2: a bundled closed convex witness in this file already refutes the
exact conjunction claimed by the corollary. -/
lemma helperForCorollary_6_30_2_exists_closedConvex_refuting_targetCorollary :
    ∃ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
      ¬ (convexClosure (convexProgramAssociatedWith F.1) 0 =
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
            sSup (Set.range fun uStar : Fin 1 → ℝ =>
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
          concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
            convexProgramAssociatedWith F.1 0 ∧
          convexProgramAssociatedWith F.1 0 =
            sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x) ∧
      sSup (Set.range fun uStar : Fin 1 → ℝ =>
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
            sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x)) := by
  -- Repackage the existing improper closed witness in bundled form.
  refine ⟨⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩, ?_⟩
  -- The witness-specific full-target refutation now matches the bundled statement directly.
  simpa using
    helperForCorollary_6_30_2_primalInconsistencyCounterexample_refutes_fullTargetConjunction

/-- Helper for Corollary 6.30.2: even after restricting to the closed-improper branch singled out
by the theorem proof, the advertised target conjunction is still not universally valid. -/
lemma helperForCorollary_6_30_2_improperBranch_not_universally_valid :
    ¬ ∀ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
        ¬ ProperConvexBifunction F.1 →
          convexClosure (convexProgramAssociatedWith F.1) 0 =
              dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
              sSup (Set.range fun uStar : Fin 1 → ℝ =>
                adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
            concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
              convexProgramAssociatedWith F.1 0 ∧
            convexProgramAssociatedWith F.1 0 =
              sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x) ∧
            sSup (Set.range fun uStar : Fin 1 → ℝ =>
                adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
              sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x) := by
  intro hImproperBranch
  let FWitness :
      {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨helperForCorollary_6_30_1_primalInconsistencyCounterexample,
      helperForCorollary_6_30_1_primalInconsistencyCounterexample_closedConvex⟩
  have hWitnessNotProper : ¬ ProperConvexBifunction FWitness.1 :=
    helperForCorollary_6_30_2_primalInconsistencyCounterexample_not_proper
  have hWitnessTarget := hImproperBranch FWitness hWitnessNotProper
  -- The explicit closed improper witness already falsifies the full theorem conjunction.
  exact
    helperForCorollary_6_30_2_primalInconsistencyCounterexample_refutes_fullTargetConjunction
      hWitnessTarget

/-- Helper for Corollary 6.30.2: the exact target conjunction is not universally valid, already
in dimensions `(m, n) = (1, 0)`. -/
lemma helperForCorollary_6_30_2_targetShape_not_universally_valid :
    ¬ ∀ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
        convexClosure (convexProgramAssociatedWith F.1) 0 =
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
            sSup (Set.range fun uStar : Fin 1 → ℝ =>
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
          concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
            convexProgramAssociatedWith F.1 0 ∧
          convexProgramAssociatedWith F.1 0 =
            sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x) ∧
          sSup (Set.range fun uStar : Fin 1 → ℝ =>
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
            sInf (Set.range fun x : Fin 0 → ℝ => F.1 0 x) := by
  intro hUniversal
  rcases helperForCorollary_6_30_2_exists_closedConvex_refuting_targetCorollary with ⟨F, hRefute⟩
  -- Specializing the claimed universal theorem to the packaged witness contradicts the refutation.
  exact hRefute (hUniversal F)

/-- Helper for Corollary 6.30.2: the exact theorem shape is not dimension-uniformly valid,
because the same closed improper witness already refutes it when specialized to `(m, n) = (1, 0)`.
-/
lemma helperForCorollary_6_30_2_globalTargetShape_not_universally_valid :
    ¬ ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}),
          convexClosure (convexProgramAssociatedWith F.1) 0 =
              dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
            dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
              sSup (Set.range fun uStar : Fin m → ℝ =>
                adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
            concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
              convexProgramAssociatedWith F.1 0 ∧
            convexProgramAssociatedWith F.1 0 =
              sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) ∧
            sSup (Set.range fun uStar : Fin m → ℝ =>
                adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
              sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
  intro hUniversal
  -- Reuse the already-packaged bundled witness that falsifies the exact theorem conjunction.
  rcases helperForCorollary_6_30_2_exists_closedConvex_refuting_targetCorollary with
    ⟨F, hRefute⟩
  -- Specializing the fully polymorphic theorem shape to that witness yields the contradiction.
  exact hRefute (hUniversal F)

/-- Helper for Corollary 6.30.2: in the closed proper branch, Theorem 6.30.15 identifies the
dual closure at `0` with the primal value at `0`. -/
lemma helperForCorollary_6_30_2_thirdConjunct_of_closedProper
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1) :
    concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
      convexProgramAssociatedWith F.1 0 := by
  have hClosedBranch :=
    (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates
      (F := ⟨F.1, F.2.1⟩)).2.2 ⟨F.2, hProper⟩
  have hZeroConjugate :
      fenchelConjugate n (fun x : Fin n → ℝ => F.1 0 x) 0 =
        -(concaveClosure
            (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0) := by
    -- Evaluate the closed proper conjugacy formula at the origin in the dual variable.
    simpa using congrFun hClosedBranch.2 (0 : Fin n → ℝ)
  have hFenchelAtZero :
      fenchelConjugate n (fun x : Fin n → ℝ => F.1 0 x) 0 =
        -(convexProgramAssociatedWith F.1 0) := by
    -- At `0`, the Fenchel conjugate is the negative infimum of the primal objective slice.
    calc
      fenchelConjugate n (fun x : Fin n → ℝ => F.1 0 x) 0
          = -⨅ x : Fin n → ℝ, F.1 0 x := by
              simpa using
                (fenchelConjugate_zero_eq_neg_iInf n (fun x : Fin n → ℝ => F.1 0 x))
      _ = -(sInf (Set.range fun x : Fin n → ℝ => F.1 0 x)) := by
            simp [sInf_range]
      _ = -(convexProgramAssociatedWith F.1 0) := by
            rfl
  -- Compare the two descriptions of the same conjugate-at-zero value and cancel the outer sign.
  rw [hFenchelAtZero] at hZeroConjugate
  simpa using (congrArg Neg.neg hZeroConjugate).symm

/-- Helper for Corollary 6.30.2: Corollary 6.30.1 rewrites the closure of the primal value
function at `0` as the unperturbed dual objective value. -/
lemma helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    convexClosure (convexProgramAssociatedWith F.1) 0 =
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := by
  have hDual :=
    helperForCorollary_6_30_1_dualProgram_eq_convexClosure_primalValue_at_zero (F := F)
  -- Rewrite the dual program value back to the zero dual slice.
  simpa [dualProgramOfConvexProgram] using hDual.symm

/-- Helper for Corollary 6.30.2: the dual perturbation value at `x* = 0` is the supremum of the
adjoint zero-slice. -/
lemma helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
      sSup (Set.range fun uStar : Fin m → ℝ =>
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) := by
  -- Unfold the dual objective at the unperturbed dual parameter.
  simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith]

/-- Helper for Corollary 6.30.2: the primal perturbation value at `u = 0` is the infimum of the
primal zero-slice. -/
lemma helperForCorollary_6_30_2_primalSlice_eq_sInf_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    convexProgramAssociatedWith F.1 0 =
      sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
  -- Unfold the primal objective at the unperturbed primal parameter.
  simp [convexProgramAssociatedWith]

/-- Helper for Corollary 6.30.2: weak duality at `0` follows by comparing the convex closure of
the primal value function with the primal value itself. -/
lemma helperForCorollary_6_30_2_weakDuality_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    sSup (Set.range fun uStar : Fin m → ℝ =>
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
      sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
  let primalValue : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  have hFirst :=
    helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)
  have hSecond :=
    helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero (F := F)
  have hFourth :=
    helperForCorollary_6_30_2_primalSlice_eq_sInf_at_zero (F := F)
  -- Rewrite the dual value through the closure formula, then use that closures lie below the
  -- original convex function.
  calc
    sSup (Set.range fun uStar : Fin m → ℝ =>
        adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar)
        = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := hSecond.symm
    _ = convexClosure primalValue 0 := by
          simpa [primalValue] using hFirst.symm
    _ ≤ primalValue 0 := by
          simpa [convexClosure, primalValue] using
            (convexFunctionClosure_le_self (f := primalValue) (0 : Fin m → ℝ))
    _ = sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
          simpa [primalValue] using hFourth

/-- Helper for Corollary 6.30.2: the full textbook conjunction is derivable from the imported
conjugacy theorem in the closed proper branch. -/
lemma helperForCorollary_6_30_2_targetConjunction_of_closedProper
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1) :
    convexClosure (convexProgramAssociatedWith F.1) 0 =
        dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
      concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
        convexProgramAssociatedWith F.1 0 ∧
      convexProgramAssociatedWith F.1 0 =
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) ∧
      sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
  have hFirst :
      convexClosure (convexProgramAssociatedWith F.1) 0 =
        dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 :=
    helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)
  have hSecond :
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) :=
    helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero (F := F)
  have hThird :
      concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
        convexProgramAssociatedWith F.1 0 :=
    helperForCorollary_6_30_2_thirdConjunct_of_closedProper (F := F) hProper
  have hFourth :
      convexProgramAssociatedWith F.1 0 =
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) :=
    helperForCorollary_6_30_2_primalSlice_eq_sInf_at_zero (F := F)
  have hFifth :
      sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) :=
    helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  exact ⟨hFirst, hSecond, hThird, hFourth, hFifth⟩

-- Proof sketch: specialize Theorem 6.30.15 to a closed convex bifunction. The dual objective
-- slice at `x* = 0` is the concave conjugate of the negated primal perturbation function, so its
-- biconjugate identifies `sup F*` with `cl (inf F)`. Under closedness, the primal objective slice
-- at `u = 0` is likewise conjugate to the negated dual perturbation function, giving
-- `cl (sup F*) = inf F`. Evaluating at `0` and unfolding the definitions of the program values
-- yields the displayed equalities and weak duality inequality.
/-- Corollary 6.30.2: if `F` is a closed convex bifunction from `ℝ^m` to `ℝ^n` and `(P)` is the
convex program associated with `F`, then `(cl (inf F))(0) = (sup F*)(0) = sup F*0`. If `F` is
also proper, then `(cl (sup F*))(0) = (inf F)(0) = inf F0`. In particular, the primal value
dominates the dual value: `inf F0 ≥ sup F*0`. -/
theorem corollary_6_30_2_2 {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    convexClosure (convexProgramAssociatedWith F.1) 0 =
        dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ∧
      (ProperConvexBifunction F.1 →
        concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
          convexProgramAssociatedWith F.1 0) ∧
      convexProgramAssociatedWith F.1 0 =
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) ∧
      sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) := by
  -- Route correction: the earlier closed-improper witness refutes the unconditional third
  -- displayed equality, so properness is assumed only for that branch.
  have hFirst :
      convexClosure (convexProgramAssociatedWith F.1) 0 =
        dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 :=
    helperForCorollary_6_30_2_convexClosure_eq_dualSlice_at_zero (F := F)
  have hSecond :
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) :=
    helperForCorollary_6_30_2_dualSlice_eq_sSup_at_zero (F := F)
  have hThird :
      ProperConvexBifunction F.1 →
        concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
          convexProgramAssociatedWith F.1 0 := by
    intro hProper
    exact helperForCorollary_6_30_2_thirdConjunct_of_closedProper (F := F) hProper
  have hFourth :
      convexProgramAssociatedWith F.1 0 =
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) :=
    helperForCorollary_6_30_2_primalSlice_eq_sInf_at_zero (F := F)
  have hFifth :
      sSup (Set.range fun uStar : Fin m → ℝ =>
          adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 uStar) ≤
        sInf (Set.range fun x : Fin n → ℝ => F.1 0 x) :=
    helperForCorollary_6_30_2_weakDuality_at_zero (F := F)
  exact ⟨hFirst, hSecond, hThird, hFourth, hFifth⟩


end Section30
end Chap06
