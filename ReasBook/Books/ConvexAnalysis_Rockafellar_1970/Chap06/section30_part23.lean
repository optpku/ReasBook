/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part22

open scoped BigOperators Pointwise

section Chap06
section Section30

/-- Helper for Theorem 6.30.24: specializing the current theorem body to the named wrong-sign
witness forces the witness dual objective to equal its own negation. This isolates the sign
error before rewriting the two sides to `⊥` and `⊤`. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_forces_selfNegDualObjective
    (hCurrentStatement :
      (∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                  -intermediateProgramDualObjective
                      helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
              (¬ intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram
              helperForTheorem_6_30_24_wrongSignWitnessData =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar}) :
    intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
      -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  -- The current theorem body forces the wrong-sign feasible-branch equality at the named
  -- witness.
  have hForcedEquality :
      adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
        -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter :=
    (hCurrentStatement.1 (0 : Fin 1 → ℝ)
      helperForTheorem_6_30_24_wrongSignWitnessDualParameter).1
        helperForTheorem_6_30_24_wrongSignWitness_feasible
  -- Comparing that forced equality with the already computed positive-sign equality isolates the
  -- sign error without yet unfolding the concrete `EReal` values.
  calc
    intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
          adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
              symm
              exact helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_dualObjective
    _ = -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter := hForcedEquality

/-- Helper for Theorem 6.30.24: specializing the current theorem body to the named wrong-sign
witness forces the impossible equality `⊥ = ⊤`. This isolates the exact computed contradiction
behind the bad feasible-branch sign. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_forces_bot_eq_top
    (hCurrentStatement :
      (∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                  -intermediateProgramDualObjective
                      helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
              (¬ intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram
              helperForTheorem_6_30_24_wrongSignWitnessData =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar}) :
    (⊥ : EReal) = (⊤ : EReal) := by
  -- The new self-negation helper isolates the sign bug before evaluating the witness values.
  have hSelfNeg :
      intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
        -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter :=
    helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_forces_selfNegDualObjective
      hCurrentStatement
  -- The explicit witness computations then evaluate the two sides to `⊥` and `⊤`.
  rw [helperForTheorem_6_30_24_wrongSignWitness_negDualObjective_eq_top] at hSelfNeg
  rw [helperForTheorem_6_30_24_wrongSignWitness_dualObjective_eq_bot] at hSelfNeg
  exact hSelfNeg

/-- Helper for Theorem 6.30.24: specializing the current theorem body to the named wrong-sign
witness yields `False`, since that specialization already forces `⊥ = ⊤`. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_false
    (hCurrentStatement :
      (∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                  -intermediateProgramDualObjective
                      helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
              (¬ intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram
              helperForTheorem_6_30_24_wrongSignWitnessData =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar}) :
    False := by
  -- The previous specialization helper already computes the contradiction as `⊥ = ⊤`.
  have hBotEqTop : (⊥ : EReal) = (⊤ : EReal) :=
    helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_forces_bot_eq_top
      hCurrentStatement
  -- Distinct `EReal` infinities cannot coincide.
  exact bot_ne_top hBotEqTop

/-- Helper for Theorem 6.30.24: the exact theorem body specialized to the named wrong-sign datum
is empty, because every inhabitant already specializes to the contradiction `⊥ = ⊤`. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_theoremBody_isEmpty :
    IsEmpty
      (((∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                  -intermediateProgramDualObjective
                      helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
              (¬ intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram
              helperForTheorem_6_30_24_wrongSignWitnessData =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar})) := by
  -- Any inhabitant is exactly the specialized theorem body already refuted above.
  refine ⟨?_⟩
  intro hCurrentStatement
  exact
    helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_false
      hCurrentStatement

/-- Helper for Theorem 6.30.24: at the named witness, the positive-sign repair already yields an
inhabited specialized theorem body, while the current negative-sign specialization is empty. This
packages the exact upstream pivot needed to repair the theorem header. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_specializedConclusions_compare :
    helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusionProp ∧
      IsEmpty helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusionProp := by
  constructor
  · -- The corrected positive-sign specialization was already proved by direct computation.
    exact helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusion
  · -- The current negative-sign specialization remains empty by the same witness contradiction.
    refine ⟨?_⟩
    intro hCurrentSpecialized
    exact
      helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusion_false
        hCurrentSpecialized

/-- Helper for Theorem 6.30.24: at the named witness, the corrected specialized theorem body is
true while the current specialized theorem body is false. This repackages the sign mismatch in
the exact `Prop`/`¬ Prop` form needed for the current retry. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_correctedTrue_currentFalse :
    helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusionProp ∧
      ¬ helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusionProp := by
  constructor
  · -- The corrected positive-sign specialization is already inhabited by the direct witness
    -- calculation.
    exact helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusion
  · -- The current negative-sign specialization remains impossible by the same witness
    -- contradiction.
    exact helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusion_false

/-- Helper for Theorem 6.30.24: specializing the current theorem body to the named wrong-sign
witness already yields a contradiction. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_refutesTheoremBody :
    ¬ ((∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                  -intermediateProgramDualObjective
                      helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
              (¬ intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
                adjointOfIntermediateProgram
                    helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram
              helperForTheorem_6_30_24_wrongSignWitnessData =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible
                    helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar}) := by
  intro hCurrentStatement
  -- The stronger specialization helper now collapses the full specialized theorem body directly
  -- to `False`, so the contradiction no longer needs to be routed through a separate negation
  -- lemma.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_targetSpecialization_false
      hCurrentStatement

/-- Helper for Theorem 6.30.24: the current theorem statement already has a concrete
counterexample, because its feasible-branch negative sign is refuted by the witness above. -/
lemma helperForTheorem_6_30_24_fullHeader_hasCounterexample :
    ∃ (data : IntermediateProgramData 0 1 1 (fun i => Fin.elim0 i))
      (_hh0 : IsClosedProperConvexERealFunction data.h0)
      (_hh : ∀ i : Fin 0, IsClosedProperConvexERealFunction (data.h i)),
      ¬ ((∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar =
                  -intermediateProgramDualObjective data wStar) ∧
      (¬ intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible data (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective data wStar}) := by
  -- Package the named witness datum together with its regularity hypotheses.
  refine ⟨helperForTheorem_6_30_24_wrongSignWitnessData,
    helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex,
    helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex, ?_⟩
  -- The specialized theorem body is already refuted by the named witness computation.
  exact helperForTheorem_6_30_24_wrongSignWitness_refutesTheoremBody

/-- Helper for Theorem 6.30.24: the current theorem statement already has a concrete
counterexample, because its feasible-branch negative sign is refuted by the witness above. -/
lemma helperForTheorem_6_30_24_currentStatement_hasCounterexample :
    ∃ (data : IntermediateProgramData 0 1 1 (fun i => Fin.elim0 i)),
      ¬ ((∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar =
                  -intermediateProgramDualObjective data wStar) ∧
              (¬ intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar :
              IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
                intermediateProgramDualFeasible data (0 : Fin 1 → ℝ) wStar ∧
                  v = intermediateProgramDualObjective data wStar}) := by
  rcases helperForTheorem_6_30_24_fullHeader_hasCounterexample with
    ⟨data, _hh0, _hh, hCurrentStatementFails⟩
  -- Forgetting the satisfiable regularity assumptions leaves the same theorem-body counterexample.
  exact ⟨data, hCurrentStatementFails⟩

/-- Helper for Theorem 6.30.24: the first branch-formula component already has a concrete
counterexample, so the sign error is present even before the dual-program-value identity is
considered. -/
lemma helperForTheorem_6_30_24_firstComponent_hasCounterexample :
    ∃ (data : IntermediateProgramData 0 1 1 (fun i => Fin.elim0 i)),
      ¬ (∀ xStar : Fin 1 → ℝ,
            ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              (intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar =
                  -intermediateProgramDualObjective data wStar) ∧
              (¬ intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) := by
  -- The named wrong-sign witness already refutes the first branch-formula package by itself.
  refine ⟨helperForTheorem_6_30_24_wrongSignWitnessData, ?_⟩
  intro hFirstComponent
  exact
    helperForTheorem_6_30_24_wrongSignWitness_branchFormulas_false
      hFirstComponent

/-- Helper for Theorem 6.30.24: if the current theorem header were valid uniformly for all
intermediate-program data, specializing it to the explicit wrong-sign witness would contradict the
counterexample computed above. -/
lemma helperForTheorem_6_30_24_universalTargetHeader_false :
    ¬ (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) := by
  intro hUniversal
  -- Specializing the universal claim to the named one-dimensional witness recovers the already
  -- refuted theorem body.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_refutesTheoremBody
      (hUniversal helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex
        helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex)

/-- Helper for Theorem 6.30.24: any candidate global proof of the current theorem header forces
the impossible negative-sign equality at the named witness. This extracts the exact feasible-branch
equation that fails in the counterexample. -/
lemma helperForTheorem_6_30_24_targetCandidate_forces_wrongSignEquality
    (hTarget :
      ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) :
    adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
        (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
      -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  -- Specializing the candidate theorem to the named one-dimensional witness datum recovers the
  -- branch formulas and dual-value clause in exactly the shape used by the counterexample.
  have hSpecialized :
      (∀ xStar : Fin 1 → ℝ,
          ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
            (intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                -intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
            (¬ intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram
          helperForTheorem_6_30_24_wrongSignWitnessData =
        sSup {v : EReal | ∃ wStar :
          IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
            intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
              v = intermediateProgramDualObjective
                helperForTheorem_6_30_24_wrongSignWitnessData wStar} :=
    hTarget helperForTheorem_6_30_24_wrongSignWitnessData
      helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex
      helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex
  -- Feeding in the feasible witness parameter isolates the exact negative-sign equality forced by
  -- the current theorem header.
  exact
    (hSpecialized.1 (0 : Fin 1 → ℝ)
      helperForTheorem_6_30_24_wrongSignWitnessDualParameter).1
        helperForTheorem_6_30_24_wrongSignWitness_feasible

/-- Helper for Theorem 6.30.24: any function that returns the current theorem conclusion for
every admissible datum would contradict the explicit wrong-sign witness. This repackages the
universal contradiction in the same dependent-function shape as the target theorem. -/
lemma helperForTheorem_6_30_24_targetStatementFunction_false
    (hTarget :
      ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) :
    False := by
  -- The extracted witness equality is exactly the impossible negative-sign formula already
  -- refuted by the direct adjoint and dual-objective computations.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_adjoint_ne_negDualObjective
      (helperForTheorem_6_30_24_targetCandidate_forces_wrongSignEquality hTarget)

/-- Helper for Theorem 6.30.24: the full dependent function type demanded by the current theorem
header is empty, because every inhabitant specializes to the named wrong-sign witness and
contradicts the computed `⊥ = ⊤` obstruction. -/
lemma helperForTheorem_6_30_24_targetStatementFunctionType_isEmpty :
    IsEmpty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) := by
  -- Any inhabitant of the target dependent function type would specialize through the explicit
  -- wrong-sign witness and recover the already packaged theorem-header contradiction.
  refine ⟨?_⟩
  intro hTarget
  exact helperForTheorem_6_30_24_targetStatementFunction_false hTarget

/-- Helper for Theorem 6.30.24: the full dependent function type demanded by the current theorem
header is not even nonempty. This restates the wrong-sign obstruction in the exact `Nonempty`
form that any attempted global proof term would induce. -/
lemma helperForTheorem_6_30_24_targetStatementFunctionType_not_nonempty :
    ¬ Nonempty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) := by
  rintro ⟨hTarget⟩
  -- Any purported global theorem term specializes to the same explicit wrong-sign contradiction.
  exact helperForTheorem_6_30_24_targetStatementFunction_false hTarget

/-- Helper for Theorem 6.30.24: the full universal proposition asserted by the current theorem
header is equivalent to `False`. The wrong-sign witness gives the forward implication, and the
reverse implication is vacuous. -/
lemma helperForTheorem_6_30_24_targetStatementFunction_iff_false :
    (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
      (data : IntermediateProgramData m n n0 ni)
      (_hh0 : IsClosedProperConvexERealFunction data.h0)
      (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
        (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
          (intermediateProgramDualFeasible data xStar wStar →
            adjointOfIntermediateProgram data xStar wStar =
              -intermediateProgramDualObjective data wStar) ∧
          (¬ intermediateProgramDualFeasible data xStar wStar →
            adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
        dualProgramValueOfIntermediateProgram data =
          sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
            intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
              v = intermediateProgramDualObjective data wStar}) ↔ False := by
  constructor
  · intro hTarget
    -- The earlier theorem-header contradiction already collapses any inhabitant to `False`.
    exact helperForTheorem_6_30_24_targetStatementFunction_false hTarget
  · intro hFalse
    -- The reverse implication is vacuous because `False` has no inhabitants.
    exact False.elim hFalse

/-- Helper for Theorem 6.30.24: even before adjoining the dual-program-value clause, any global
proof of the theorem's first branch-formula component would already contradict the named
wrong-sign witness. This isolates the blocker at the exact first component left in the theorem
proof below. -/
lemma helperForTheorem_6_30_24_firstComponentFunction_false
    (hFirstComponent :
      ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          ∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) :
    False := by
  -- Specializing the purported first-component proof to the named witness recovers the already
  -- refuted branch-formula package.
  have hSpecialized :
      ∀ xStar : Fin 1 → ℝ,
        ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
          (intermediateProgramDualFeasible
              helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
            adjointOfIntermediateProgram
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
              -intermediateProgramDualObjective
                  helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
          (¬ intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
            adjointOfIntermediateProgram
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal)) :=
    hFirstComponent helperForTheorem_6_30_24_wrongSignWitnessData
      helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex
      helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex
  -- The specialized branch formulas contradict the direct computation at the feasible witness.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_branchFormulas_false
      hSpecialized

/-- Helper for Theorem 6.30.24: the dependent function type for the theorem's first component is
already empty. The obstruction is therefore present before the dual-program-value clause is even
considered. -/
lemma helperForTheorem_6_30_24_firstComponentFunctionType_isEmpty :
    IsEmpty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          ∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) := by
  -- Any inhabitant of the first-component function type specializes to the named branch-formula
  -- contradiction packaged above.
  refine ⟨?_⟩
  intro hFirstComponent
  exact helperForTheorem_6_30_24_firstComponentFunction_false hFirstComponent

/-- Helper for Theorem 6.30.24: the theorem's first-component dependent function type is not even
nonempty. This restates the same wrong-sign obstruction in the `Nonempty` form that any attempted
global proof would have to produce. -/
lemma helperForTheorem_6_30_24_firstComponentFunctionType_not_nonempty :
    ¬ Nonempty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          ∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                -intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) := by
  rintro ⟨hFirstComponent⟩
  -- Any purported inhabitant of the first-component function type specializes to the named
  -- wrong-sign witness and reproduces the packaged contradiction.
  exact helperForTheorem_6_30_24_firstComponentFunction_false hFirstComponent

/-- Helper for Theorem 6.30.24: the theorem's first-component universal function proposition is
equivalent to `False`. The wrong-sign witness gives the forward implication, and the reverse
implication is vacuous. -/
lemma helperForTheorem_6_30_24_firstComponentFunction_iff_false :
    (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
      (data : IntermediateProgramData m n n0 ni)
      (_hh0 : IsClosedProperConvexERealFunction data.h0)
      (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
        ∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
          (intermediateProgramDualFeasible data xStar wStar →
            adjointOfIntermediateProgram data xStar wStar =
              -intermediateProgramDualObjective data wStar) ∧
          (¬ intermediateProgramDualFeasible data xStar wStar →
            adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ↔ False := by
  constructor
  · intro hFirstComponent
    -- The packaged first-component contradiction already collapses any inhabitant to `False`.
    exact helperForTheorem_6_30_24_firstComponentFunction_false hFirstComponent
  · intro hFalse
    -- The reverse implication is vacuous because `False` has no inhabitants.
    exact False.elim hFalse

/-- Helper for Theorem 6.30.24: the named witness already exhibits the positive-sign specialized
repair, while the full current theorem type remains empty. This packages the exact theorem-level
header correction needed before the main proof can be completed. -/
lemma helperForTheorem_6_30_24_currentHeaderNeedsPositiveSignRepair :
    helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusionProp ∧
      ¬ Nonempty
        (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
          (data : IntermediateProgramData m n n0 ni)
          (_hh0 : IsClosedProperConvexERealFunction data.h0)
          (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
            (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
              (intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar =
                  -intermediateProgramDualObjective data wStar) ∧
              (¬ intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
            dualProgramValueOfIntermediateProgram data =
              sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
                intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                  v = intermediateProgramDualObjective data wStar}) := by
  constructor
  · -- The repaired positive-sign specialization was already computed directly at the named
    -- witness.
    exact helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusion
  · -- The current negative-sign theorem type is empty by the explicit wrong-sign witness.
    exact helperForTheorem_6_30_24_targetStatementFunctionType_not_nonempty

/-- Helper for Theorem 6.30.24: the zero-multiplier restricted-domain counterexample datum with
one indicator constraint. -/
noncomputable def helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData :
    IntermediateProgramData 1 1 1 (fun _ : Fin 1 => 1) :=
  { h0 := fun _ : Fin 1 → ℝ => (0 : EReal)
    A0 := 0
    a0 := 0
    a0Star := 0
    α0 := 0
    h := fun _ : Fin 1 => indicatorFunction ({0} : Set (Fin 1 → ℝ))
    A := fun _ : Fin 1 => 0
    a := fun _ : Fin 1 => 0
    aStar := fun _ : Fin 1 => 0
    α := fun _ : Fin 1 => 0 }

/-- Helper for Theorem 6.30.24: the dual parameter with zero multiplier, zero `p₀*`, and nonzero
constraint covector used in the restricted-domain counterexample. -/
def helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter :
    IntermediateProgramDualParameter 1 1 1 (fun _ : Fin 1 => 1) :=
  { vStar := fun _ : Fin 1 => 0
    p0 := 0
    p := fun _ : Fin 1 => (fun _ : Fin 1 => (1 : ℝ)) }

/-- Helper for Theorem 6.30.24: the primal perturbation parameter with all coordinates zero used
to realize the adjoint value `0` at the restricted-domain witness. -/
def helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessPrimalParameter :
    IntermediateProgramParameter 1 1 1 (fun _ : Fin 1 => 1) :=
  { v := fun _ : Fin 1 => 0
    p0 := 0
    p := fun _ : Fin 1 => 0 }

/-- Helper for Theorem 6.30.24: the head datum of the restricted-domain witness is again the
constant-zero function, so the previously constructed closed proper convex witness still applies. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_h0_closedProperConvex :
    IsClosedProperConvexERealFunction
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData.h0 := by
  -- The new datum reuses exactly the same constant-zero head block as the earlier one-dimensional
  -- witness.
  simpa [helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
    helperForTheorem_6_30_24_wrongSignWitnessData] using
    helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex

/-- Helper for Theorem 6.30.24: the unique constraint block in the restricted-domain witness is
the indicator of `{0}`, hence closed proper convex. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_h_closedProperConvex :
    ∀ i : Fin 1,
      IsClosedProperConvexERealFunction
        (helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData.h i) := by
  intro i
  fin_cases i
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (indicatorFunction ({0} : Set (Fin 1 → ℝ))) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (by simp) (by simp)
  have hproper :
      ProperConvexERealFunction (F := Fin 1 → ℝ)
        (indicatorFunction ({0} : Set (Fin 1 → ℝ))) :=
    helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn hproperOn
  have hclosedIndicator :
      ClosedConvexFunction (indicatorFunction ({0} : Set (Fin 1 → ℝ))) := by
    have hIndicator :=
      closedConvexFunction_indicator_neg (n := 1) (C := ({0} : Set (Fin 1 → ℝ)))
        (by simp) isClosed_singleton (by simp)
    -- Negating the singleton `{0}` leaves it unchanged, so the closed-indicator theorem applies
    -- without any further translation.
    simpa [Set.neg_singleton] using hIndicator.1
  -- The unique indexed constraint is definitionally the singleton indicator.
  simpa [helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData] using
    (show IsClosedProperConvexERealFunction
        (indicatorFunction ({0} : Set (Fin 1 → ℝ))) from ⟨hproper, hclosedIndicator⟩)

/-- Helper for Theorem 6.30.24: the zero-multiplier restricted-domain witness satisfies the
displayed dual-feasibility conditions. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_dualFeasible :
    intermediateProgramDualFeasible
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
      (0 : Fin 1 → ℝ)
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter := by
  -- Every affine datum vanishes, so feasibility reduces to the trivial equations `0 ≤ 0` and
  -- `0 = 0`.
  simp [intermediateProgramDualFeasible,
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter]

/-- Helper for Theorem 6.30.24: multiplying the singleton-indicator constraint by the zero
multiplier collapses it to the constant-zero function. This is exactly the loss of domain
information that breaks the universal formula. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_scaledConstraint_eq_zero :
    (fun y =>
      (((helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter.vStar 0 : ℝ) :
          EReal) *
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData.h 0 y)) =
      (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
  funext y
  -- The multiplier is zero, so every value of the scaled constraint term vanishes.
  simp [helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter]

/-- Helper for Theorem 6.30.24: at the zero-multiplier restricted-domain witness, the explicit
dual objective evaluates to `-∞`. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_dualObjective_eq_bot :
    intermediateProgramDualObjective
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter =
      (⊥ : EReal) := by
  have hOneNeZero :
      (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    -- The unique coordinate of the witness covector is `1`, so it cannot be the zero function.
    intro hone
    have hcoord := congrFun hone 0
    norm_num at hcoord
  -- The head conjugate is the indicator of `{0}` at `0`, while the zero-scaled constraint
  -- conjugate is the same indicator evaluated at the nonzero covector `1`.
  rw [intermediateProgramDualObjective]
  simp_rw [helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter]
  have hscaled :
      (fun y : Fin 1 → ℝ =>
        ((((0 : ℝ) : EReal)) * indicatorFunction ({0} : Set (Fin 1 → ℝ)) y)) =
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    funext y
    -- After simplification, the zero scalar annihilates both the `0` and `⊤` values of the
    -- singleton indicator.
    simp
  rw [hscaled]
  rw [section16_fenchelConjugate_const_zero]
  simp [indicatorFunction_singleton_simp, hOneNeZero]

/-- Helper for Theorem 6.30.24: for the restricted-domain witness, feasibility of a primal point
forces the translated singleton-indicator argument to be zero, equivalently `p₁ = 0`, and then
the threshold inequality is exactly `0 ≤ v₁`. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_mem_feasibleSet_iff
    (w : IntermediateProgramParameter 1 1 1 (fun _ : Fin 1 => 1))
    (x : Fin 1 → ℝ) :
    x ∈ intermediateProgramFeasibleSet
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData w ↔
      w.p 0 = 0 ∧ 0 ≤ w.v 0 := by
  constructor
  · intro hx
    have hineq :
        indicatorFunction ({0} : Set (Fin 1 → ℝ)) (-w.p 0) ≤ (((w.v 0 : ℝ) : EReal)) := by
      simpa [intermediateProgramFeasibleSet,
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData] using hx 0
    have hpzero : w.p 0 = 0 := by
      by_contra hpzero
      have hneg_ne_zero : -w.p 0 ≠ (0 : Fin 1 → ℝ) := by
        simpa using neg_ne_zero.mpr hpzero
      have hindicator_top :
          indicatorFunction ({0} : Set (Fin 1 → ℝ)) (-w.p 0) = (⊤ : EReal) := by
        simp [indicatorFunction_singleton_simp, hneg_ne_zero]
      -- A nonzero shift makes the singleton indicator equal `⊤`, contradicting the finite
      -- threshold bound.
      rw [hindicator_top] at hineq
      simp at hineq
    have hvnonneg :
        0 ≤ w.v 0 := by
      have hzero_le :
          (0 : EReal) ≤ (((w.v 0 : ℝ) : EReal)) := by
        simpa [intermediateProgramFeasibleSet,
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
          hpzero, indicatorFunction_singleton_simp] using hx 0
      exact_mod_cast hzero_le
    exact ⟨hpzero, hvnonneg⟩
  · rintro ⟨hpzero, hvnonneg⟩ i
    fin_cases i
    -- Once `p₁ = 0`, the singleton indicator contributes `0`, so feasibility is exactly the
    -- nonnegativity of `v₁`.
    simpa [intermediateProgramFeasibleSet,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
      hpzero, indicatorFunction_singleton_simp] using hvnonneg

/-- Helper for Theorem 6.30.24: every term in the defining adjoint infimum for the
zero-multiplier restricted-domain witness is at least `0`. Feasible points force `p₁ = 0`,
while infeasible points contribute `+∞` through the indicator. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_integrand_nonneg
    (q : IntermediateProgramParameter 1 1 1 (fun _ : Fin 1 => 1) × (Fin 1 → ℝ)) :
    (0 : EReal) ≤
      intermediateProgramBifunction
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData q.1 q.2 -
        (((q.2 ⬝ᵥ (0 : Fin 1 → ℝ) : ℝ) : EReal)) +
        (((intermediateProgramDualPairing q.1
            helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter : ℝ) :
          EReal)) := by
  rcases q with ⟨w, x⟩
  by_cases hx :
      x ∈ intermediateProgramFeasibleSet
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData w
  · rcases
      (helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_mem_feasibleSet_iff
        w x).1 hx with ⟨hpzero, _hvnonneg⟩
    have hIndicatorZero :
        indicatorFunction
            (intermediateProgramFeasibleSet
              helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData w) x =
          (0 : EReal) := by
      -- Membership in the feasible set makes the outer indicator vanish.
      simp [indicatorFunction, hx]
    -- On the feasible branch, the indicator term vanishes and the same feasibility condition has
    -- already forced the dual pairing contribution `p₁` to be zero.
    rw [intermediateProgramBifunction, hIndicatorZero]
    simp [intermediateProgramDualPairing,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter,
      hpzero]
  · -- Outside the feasible set the bifunction is `+∞`, so the whole integrand is `+∞`.
    have hIndicatorTop :
        indicatorFunction
            (intermediateProgramFeasibleSet
              helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData w) x =
          (⊤ : EReal) := by
      -- Non-membership in the feasible set makes the outer indicator equal `⊤`.
      simp [indicatorFunction, hx]
    rw [intermediateProgramBifunction, hIndicatorTop]
    simp [intermediateProgramDualPairing,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter]

/-- Helper for Theorem 6.30.24: at the zero-multiplier restricted-domain witness, the adjoint is
exactly `0`. The infimum is attained by the all-zero primal perturbation parameter, and every
other admissible integrand value is at least `0`. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_adjoint_eq_zero :
    adjointOfIntermediateProgram
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter =
      (0 : EReal) := by
  refine le_antisymm ?_ ?_
  · rw [adjointOfIntermediateProgram]
    -- The zero perturbation parameter and zero primal point realize the value `0` inside the
    -- defining infimum.
    refine sInf_le ?_
    refine ⟨(helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessPrimalParameter,
      (0 : Fin 1 → ℝ)), ?_⟩
    simp [intermediateProgramBifunction, intermediateProgramDualPairing,
      intermediateProgramFeasibleSet, indicatorFunction,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter,
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessPrimalParameter]
  · rw [adjointOfIntermediateProgram]
    -- The previous nonnegativity computation shows that `0` is a lower bound for the entire
    -- infimum range.
    refine le_sInf ?_
    rintro _ ⟨q, rfl⟩
    exact
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_integrand_nonneg q

/-- Helper for Theorem 6.30.24: the restricted-domain witness is dual-feasible but still breaks
the positive-sign feasible branch, since the adjoint stays `0` while the explicit dual objective
has already collapsed to `-∞`. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_adjoint_ne_dualObjective :
    adjointOfIntermediateProgram
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter ≠
      intermediateProgramDualObjective
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter := by
  -- The two closed-form computations reduce the contradiction to `0 ≠ -∞`.
  rw [helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_adjoint_eq_zero,
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_dualObjective_eq_bot]
  simp

/-- Helper for Theorem 6.30.24: even the repaired positive-sign feasible branch fails for the
restricted-domain witness with zero multiplier, so the remaining obstruction is not a sign issue
but a genuinely false theorem statement. -/
lemma helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_feasibleBranch_false :
    ¬ (intermediateProgramDualFeasible
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
          (0 : Fin 1 → ℝ)
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter →
        adjointOfIntermediateProgram
            helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
            (0 : Fin 1 → ℝ)
            helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter =
          intermediateProgramDualObjective
            helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
            helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter) := by
  intro hFeasibleBranch
  have hForcedEquality :
      adjointOfIntermediateProgram
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
          (0 : Fin 1 → ℝ)
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter =
        intermediateProgramDualObjective
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter :=
    hFeasibleBranch
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_dualFeasible
  -- The explicit witness computation already shows that this forced feasible-branch equality is
  -- impossible.
  exact
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_adjoint_ne_dualObjective
      hForcedEquality

/-- Helper for Theorem 6.30.24: any candidate global proof of the current positive-sign theorem
header specializes to the zero-multiplier restricted-domain witness and forces the impossible
feasible-branch equality computed above. -/
lemma helperForTheorem_6_30_24_targetCandidate_forces_zeroMultiplierRestrictedDomainEquality
    (hTarget :
      ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) :
    adjointOfIntermediateProgram
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter =
      intermediateProgramDualObjective
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter := by
  -- Specializing the candidate theorem to the restricted-domain witness isolates exactly the
  -- feasible-branch equality that fails when the multiplier coordinate is zero.
  have hSpecialized :
      (∀ xStar : Fin 1 → ℝ,
          ∀ wStar : IntermediateProgramDualParameter 1 1 1 (fun _ : Fin 1 => 1),
            (intermediateProgramDualFeasible
                helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData xStar wStar =
                intermediateProgramDualObjective
                    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData wStar) ∧
            (¬ intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData xStar wStar =
                (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram
          helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData =
        sSup {v : EReal | ∃ wStar :
          IntermediateProgramDualParameter 1 1 1 (fun _ : Fin 1 => 1),
            intermediateProgramDualFeasible
                helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
                (0 : Fin 1 → ℝ) wStar ∧
              v = intermediateProgramDualObjective
                helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData wStar} :=
    hTarget helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessData
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_h0_closedProperConvex
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_h_closedProperConvex
  -- Feeding in the named feasible dual parameter recovers the exact equality contradicted by the
  -- explicit adjoint and dual-objective computations.
  exact
    (hSpecialized.1 (0 : Fin 1 → ℝ)
      helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitnessDualParameter).1
        helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_dualFeasible

/-- Helper for Theorem 6.30.24: the full dependent theorem type with the current positive-sign
feasible branch is empty, because any inhabitant specializes to the zero-multiplier restricted-
domain witness and contradicts the computed adjoint-versus-objective mismatch. -/
lemma helperForTheorem_6_30_24_currentTargetStatementFunction_false
    (hTarget :
      ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) :
    False := by
  -- The packaged specialization helper extracts the impossible equality at the restricted-domain
  -- witness, so the whole dependent theorem type is inconsistent as written.
  exact
    helperForTheorem_6_30_24_zeroMultiplierRestrictedDomainWitness_adjoint_ne_dualObjective
      (helperForTheorem_6_30_24_targetCandidate_forces_zeroMultiplierRestrictedDomainEquality
        hTarget)


end Section30
end Chap06
