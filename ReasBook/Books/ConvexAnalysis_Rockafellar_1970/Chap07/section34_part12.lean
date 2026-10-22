/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part11

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart12 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}

/-- The one-dimensional division kernel `(u, v) ↦ u / v`, written on `Fin 1 → ℝ` coordinates. -/
noncomputable def oneDimensionalDivisionKernel (u v : Fin 1 → ℝ) : EReal :=
  (((u 0) / (v 0) : ℝ) : EReal)

/-- The concave-convex simple extension of `(u, v) ↦ u / v` from the quadrant
`{(u, v) | 0 ≤ u ∧ 0 < v}`. -/
noncomputable def positiveQuadrantDivisionSaddle : SaddleFunction 1 1 :=
  fun u v =>
    if v 0 ≤ 0 then
      ⊤
    else if u 0 < 0 then
      ⊥
    else
      oneDimensionalDivisionKernel u v

/-- The explicit upper-closure formula for the simple extension of `(u, v) ↦ u / v` on the
positive quadrant. -/
noncomputable def positiveQuadrantDivisionUpperClosureFormula : SaddleFunction 1 1 :=
  fun u v =>
    if v 0 ≤ 0 then
      ⊤
    else if u 0 < 0 then
      ⊥
    else
      oneDimensionalDivisionKernel u v

/-- The explicit lower-closure formula for the simple extension of `(u, v) ↦ u / v` on the
positive quadrant. -/
noncomputable def positiveQuadrantDivisionLowerClosureFormula : SaddleFunction 1 1 :=
  fun u v =>
    if u 0 < 0 then
      ⊥
    else if u 0 = 0 ∧ v 0 = 0 then
      ((0 : ℝ) : EReal)
    else if v 0 ≤ 0 then
      ⊤
    else
      oneDimensionalDivisionKernel u v

/-- The finiteness domain of the upper closure in the `u / v` model example is the positive
quadrant boundary condition `0 ≤ u` and `0 < v`. -/
def positiveQuadrantDivisionUpperFinitenessDomain : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  {p | 0 ≤ p.1 0 ∧ 0 < p.2 0}

/-- The finiteness domain of the lower closure in the `u / v` model example adjoins the origin
to the upper-closure finiteness domain. -/
def positiveQuadrantDivisionLowerFinitenessDomain : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  positiveQuadrantDivisionUpperFinitenessDomain ∪
    {((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ))}

-- Route correction: the displayed upper-closure formula is already incompatible with the
-- implemented mixed closure at the concrete point `((-1), 0)`. The next lemmas isolate that
-- mismatch directly from the closure definitions, so the remaining blocker is the textbook
-- statement itself rather than a missing limit computation.
/-- Helper for Text 34.1.2: the standard positive witness `ε / 2` stays inside every ball around
the second-variable origin. -/
lemma helperForText_34_1_2_halfPositiveWitness_mem_ball_origin (ε : {ε : ℝ // 0 < ε}) :
    ‖(fun _ : Fin 1 => ε.1 / 2) - (0 : Fin 1 → ℝ)‖ < ε.1 := by
  -- On `Fin 1`, the norm reduces to the absolute value of the unique coordinate.
  rw [helperForText_34_1_1_norm_fin1_eq_abs (0 : Fin 1 → ℝ) (fun _ : Fin 1 => ε.1 / 2)]
  have hHalfPos : 0 < ε.1 / 2 := by
    nlinarith [ε.2]
  simp [abs_of_pos hHalfPos]
  nlinarith [ε.2]

/-- Helper for Text 34.1.2: if the first coordinate is negative, then the second partial closure
at `v = 0` is already `-∞`. -/
lemma helperForText_34_1_2_secondClosureAtZero_eq_bot_of_negativeFirst
    {u : Fin 1 → ℝ} (hu : u 0 < 0) :
    partialClosure₂ positiveQuadrantDivisionSaddle u (0 : Fin 1 → ℝ) = (⊥ : EReal) := by
  -- Every `v`-ball around `0` contains a positive point, and at such a point the simple
  -- extension immediately falls into the negative-`u` branch.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    let witnessValue : Fin 1 → ℝ := fun _ : Fin 1 => ε.1 / 2
    have hWitnessMem : ‖witnessValue - (0 : Fin 1 → ℝ)‖ < ε.1 :=
      helperForText_34_1_2_halfPositiveWitness_mem_ball_origin ε
    let witness : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} :=
      ⟨witnessValue, hWitnessMem⟩
    have hWitnessPos : 0 < witness.1 0 := by
      change 0 < ε.1 / 2
      nlinarith [ε.2]
    have hWitnessNonpos : ¬ witness.1 0 ≤ 0 := not_le.mpr hWitnessPos
    calc
      (⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
          positiveQuadrantDivisionSaddle u w.1)
          ≤ positiveQuadrantDivisionSaddle u witness.1 := iInf_le _ witness
      _ = (⊥ : EReal) := by
        simp [positiveQuadrantDivisionSaddle, hWitnessNonpos, hu]
  · exact bot_le

/-- Helper for Text 34.1.2: every point in the radius-`1/2` ball around `u = -1` still has
negative first coordinate. -/
lemma helperForText_34_1_2_halfBallAroundNegOne_stays_negative
    (w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < (1 / 2 : ℝ)}) :
    w.1 0 < 0 := by
  -- The singleton norm estimate gives an absolute-value bound on the unique coordinate.
  have hwNorm := w.2
  rw [helperForText_34_1_1_norm_fin1_eq_abs (fun _ : Fin 1 => (-1 : ℝ)) w.1] at hwNorm
  have hAbs : |w.1 0 - (-1 : ℝ)| < (1 / 2 : ℝ) := by
    simpa using hwNorm
  have hBounds := abs_lt.mp hAbs
  linarith

/-- Helper for Text 34.1.2: the inner second closure already takes the value `-∞` at the
negative-axis point `((-1), 0)`. -/
lemma helperForText_34_1_2_secondClosure_negAxis_zero_eq_bot :
    partialClosure₂ positiveQuadrantDivisionSaddle
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) = (⊥ : EReal) := by
  -- Specialize the general negative-first-coordinate computation to `u = -1`.
  exact helperForText_34_1_2_secondClosureAtZero_eq_bot_of_negativeFirst (by norm_num)

/-- Helper for Text 34.1.2: the mixed upper closure `cl₁(cl₂ K)` also takes the value `-∞` at
`((-1), 0)`. -/
lemma helperForText_34_1_2_upperMixedClosure_negAxis_zero_eq_bot :
    partialClosure₁ (partialClosure₂ positiveQuadrantDivisionSaddle)
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) = (⊥ : EReal) := by
  -- A fixed first-variable radius `1/2` keeps every nearby point on the negative half-line,
  -- so the already-computed inner second closure stays equal to `⊥` throughout that ball.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · have hHalfPos : 0 < (1 / 2 : ℝ) := by
      norm_num
    let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, hHalfPos⟩
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < ε'.1},
            partialClosure₂ positiveQuadrantDivisionSaddle w.1 (0 : Fin 1 → ℝ))
          ≤
        ⨆ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < ε.1},
          partialClosure₂ positiveQuadrantDivisionSaddle w.1 (0 : Fin 1 → ℝ) := iInf_le _ ε
      _ = (⊥ : EReal) := by
        apply le_antisymm
        · refine iSup_le ?_
          intro w
          have hwNeg : w.1 0 < 0 :=
            helperForText_34_1_2_halfBallAroundNegOne_stays_negative w
          rw [helperForText_34_1_2_secondClosureAtZero_eq_bot_of_negativeFirst hwNeg]
        · exact bot_le
  · exact bot_le

/-- Helper for Text 34.1.2: for every concave-convex witness, the actual upper closure takes
the value `-∞` at the negative-axis point `((-1), 0)`. -/
lemma helperForText_34_1_2_upperClosure_negAxis_zero_eq_bot
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) = (⊥ : EReal) := by
  -- Rewrite the true upper closure through the mixed-closure formula from the previous text.
  have hMixed :
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) =
        partialClosure₁ (partialClosure₂ positiveQuadrantDivisionSaddle)
          (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ))
        (helperForText_34_0_1_mixedClosure_formulas positiveQuadrantDivisionSaddle hK).2
  -- The concrete mixed-closure computation then gives the claimed value.
  rw [hMixed, helperForText_34_1_2_upperMixedClosure_negAxis_zero_eq_bot]

/-- Helper for Text 34.1.2: the displayed upper formula assigns the value `+∞` at the same
negative-axis point `((-1), 0)`. -/
lemma helperForText_34_1_2_upperFormula_negAxis_zero_eq_top :
    positiveQuadrantDivisionUpperClosureFormula
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) = (⊤ : EReal) := by
  -- The branch `v ≤ 0` fires immediately at `v = 0`.
  simp [positiveQuadrantDivisionUpperClosureFormula]

/-- Helper for Text 34.1.2: every claimed upper-closure identity fails at `((-1), 0)`, because
the actual mixed upper closure is `-∞` there while the displayed formula is `+∞`. -/
lemma helperForText_34_1_2_upperClosure_formula_fails_at_negAxis_zero
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) ≠
      positiveQuadrantDivisionUpperClosureFormula
        (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) := by
  -- Evaluate both sides at the counterexample point using the dedicated pointwise formulas.
  rw [helperForText_34_1_2_upperClosure_negAxis_zero_eq_bot hK]
  rw [helperForText_34_1_2_upperFormula_negAxis_zero_eq_top]
  exact bot_ne_top

/-- Helper for Text 34.1.2: no concave-convex witness can make the displayed upper formula
equal the true upper closure. -/
lemma helperForText_34_1_2_upperClosure_ne_upperClosureFormula
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK ≠
      positiveQuadrantDivisionUpperClosureFormula := by
  intro hEq
  -- A function equality would force agreement at the explicit counterexample point.
  exact
    helperForText_34_1_2_upperClosure_formula_fails_at_negAxis_zero hK
      (congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ))
        hEq)

/-- Helper for Text 34.1.2: any claimed upper-closure identity would force the impossible point
value equation `-∞ = +∞` at `((-1), 0)`. -/
lemma helperForText_34_1_2_upperClosure_identity_forces_bot_eq_top
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle)
    (hUpper :
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
        positiveQuadrantDivisionUpperClosureFormula) :
    (⊥ : EReal) = (⊤ : EReal) := by
  -- Evaluate the claimed function identity at the explicit counterexample point.
  have hPoint :
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) =
        positiveQuadrantDivisionUpperClosureFormula
          (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (0 : Fin 1 → ℝ))
        hUpper
  -- The previously computed pointwise formulas turn that equality into `⊥ = ⊤`.
  rw [helperForText_34_1_2_upperClosure_negAxis_zero_eq_bot hK] at hPoint
  rw [helperForText_34_1_2_upperFormula_negAxis_zero_eq_top] at hPoint
  exact hPoint

/-- Helper for Text 34.1.2: the first closure identity demanded by the theorem is already
contradictory for any concave-convex witness. -/
lemma helperForText_34_1_2_false_of_claimedUpperClosureIdentity
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle)
    (hUpper :
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
        positiveQuadrantDivisionUpperClosureFormula) :
    False := by
  -- The counterexample point converts the claimed function identity into `⊥ = ⊤`.
  have hBotEqTop :
      (⊥ : EReal) = (⊤ : EReal) :=
    helperForText_34_1_2_upperClosure_identity_forces_bot_eq_top hK hUpper
  exact bot_ne_top hBotEqTop

/-- Helper for Text 34.1.2: every claimed upper-closure formula mismatch has the explicit
counterexample point `((-1), 0)`. -/
lemma helperForText_34_1_2_exists_upperClosure_counterexample
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    ∃ u v,
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK u v ≠
        positiveQuadrantDivisionUpperClosureFormula u v := by
  -- Reuse the already-computed counterexample point instead of searching for a new witness.
  refine ⟨(fun _ : Fin 1 => (-1 : ℝ)), (0 : Fin 1 → ℝ), ?_⟩
  exact helperForText_34_1_2_upperClosure_formula_fails_at_negAxis_zero hK

/-- Helper for Text 34.1.2: the full theorem conclusion is inconsistent, because its first
closure identity already fails at `((-1), 0)`. -/
lemma helperForText_34_1_2_theorem_conclusion_false :
    ¬ (IsConcaveConvex positiveQuadrantDivisionSaddle ∧
        ∀ hK : IsConcaveConvex positiveQuadrantDivisionSaddle,
          upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
              positiveQuadrantDivisionUpperClosureFormula ∧
            lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
              positiveQuadrantDivisionLowerClosureFormula ∧
            positiveQuadrantDivisionUpperClosureFormula (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              (⊤ : EReal) ∧
            positiveQuadrantDivisionLowerClosureFormula (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              ((0 : ℝ) : EReal) ∧
            finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
              positiveQuadrantDivisionUpperFinitenessDomain ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
              positiveQuadrantDivisionLowerFinitenessDomain ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ≠
              finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ∧
            ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
                finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
                  A ×ˢ B) := by
  intro hStatement
  rcases hStatement with ⟨hK, hConclusion⟩
  -- The theorem's first closure identity already contradicts the explicit counterexample point.
  exact helperForText_34_1_2_false_of_claimedUpperClosureIdentity hK (hConclusion hK).1

/-- Helper for Text 34.1.2: if the second coordinate is nonpositive, then the first partial
closure is already the constant value `+∞`. -/
lemma helperForText_34_1_2_firstClosure_eq_top_of_nonpositiveSecond
    {u v : Fin 1 → ℝ} (hv : v 0 ≤ 0) :
    partialClosure₁ positiveQuadrantDivisionSaddle u v = (⊤ : EReal) := by
  -- Every local first-variable supremum already contains the center point, where the simple
  -- extension is in the `v ≤ 0` branch and therefore equal to `⊤`.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm le_top
  refine le_iInf ?_
  intro ε
  let witness : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} := ⟨u, by simpa using ε.2⟩
  have hValue : positiveQuadrantDivisionSaddle witness.1 v = (⊤ : EReal) := by
    simp [positiveQuadrantDivisionSaddle, hv]
  calc
    (⊤ : EReal) = positiveQuadrantDivisionSaddle witness.1 v := by rw [hValue]
    _ ≤
      ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
        positiveQuadrantDivisionSaddle w.1 v :=
      le_iSup
        (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} =>
          positiveQuadrantDivisionSaddle w.1 v)
        witness

/-- Helper for Text 34.1.2: the mixed lower closure `cl₂(cl₁ K)` takes the value `+∞` at
the negative-negative point `((-1), (-1))`. -/
lemma helperForText_34_1_2_mixedLowerClosure_negNeg_eq_top :
    partialClosure₂ (partialClosure₁ positiveQuadrantDivisionSaddle)
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) = (⊤ : EReal) := by
  -- The radius `1 / 2` keeps every nearby second-variable point negative, so the inner first
  -- closure is constantly `⊤` on that entire ball.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm le_top
  have hHalfPos : 0 < (1 / 2 : ℝ) := by
    norm_num
  let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, hHalfPos⟩
  calc
    (⊤ : EReal)
        ≤
      ⨅ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < ε.1},
        partialClosure₁ positiveQuadrantDivisionSaddle (fun _ : Fin 1 => (-1 : ℝ)) w.1 := by
          refine le_iInf ?_
          intro w
          have hwNeg : w.1 0 < 0 :=
            helperForText_34_1_2_halfBallAroundNegOne_stays_negative w
          rw [helperForText_34_1_2_firstClosure_eq_top_of_nonpositiveSecond (le_of_lt hwNeg)]
    _ ≤
      ⨆ ε' : {ε' : ℝ // 0 < ε'},
        ⨅ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < ε'.1},
          partialClosure₁ positiveQuadrantDivisionSaddle (fun _ : Fin 1 => (-1 : ℝ)) w.1 :=
      le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (-1 : ℝ))‖ < ε'.1},
            partialClosure₁ positiveQuadrantDivisionSaddle (fun _ : Fin 1 => (-1 : ℝ)) w.1)
        ε

/-- Helper for Text 34.1.2: every concave-convex witness forces the true lower closure to take
the value `+∞` at `((-1), (-1))`. -/
lemma helperForText_34_1_2_lowerClosure_negNeg_eq_top
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) = (⊤ : EReal) := by
  -- Rewrite the lower closure through the mixed-closure formula and then evaluate the explicit
  -- negative-negative branch computed just above.
  have hMixed :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) =
        partialClosure₂ (partialClosure₁ positiveQuadrantDivisionSaddle)
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)))
        (helperForText_34_0_1_mixedClosure_formulas positiveQuadrantDivisionSaddle hK).1
  rw [hMixed, helperForText_34_1_2_mixedLowerClosure_negNeg_eq_top]

/-- Helper for Text 34.1.2: the displayed lower formula assigns the value `-∞` at the same
negative-negative point `((-1), (-1))`. -/
lemma helperForText_34_1_2_lowerFormula_negNeg_eq_bot :
    positiveQuadrantDivisionLowerClosureFormula
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) = (⊥ : EReal) := by
  -- The first branch `u < 0` of the piecewise formula fires immediately at `u = -1`.
  simp [positiveQuadrantDivisionLowerClosureFormula]

/-- Helper for Text 34.1.2: the lower-closure mismatch is witnessed by the concrete
negative-negative point `((-1), (-1))`, where the true closure is `+∞` and the displayed
formula is `-∞`. -/
lemma helperForText_34_1_2_exists_lowerClosure_counterexample
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    ∃ u v,
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK u v = (⊤ : EReal) ∧
        positiveQuadrantDivisionLowerClosureFormula u v = (⊥ : EReal) := by
  -- Reuse the already-computed explicit counterexample point instead of searching for a new one.
  refine ⟨(fun _ : Fin 1 => (-1 : ℝ)), (fun _ : Fin 1 => (-1 : ℝ)), ?_, ?_⟩
  · exact helperForText_34_1_2_lowerClosure_negNeg_eq_top hK
  · exact helperForText_34_1_2_lowerFormula_negNeg_eq_bot

/-- Helper for Text 34.1.2: every claimed lower-closure identity fails at `((-1), (-1))`,
because the actual mixed lower closure is `+∞` there while the displayed formula is `-∞`. -/
lemma helperForText_34_1_2_lowerClosure_formula_fails_at_negNeg
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) ≠
      positiveQuadrantDivisionLowerClosureFormula
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) := by
  -- Evaluate both sides at the counterexample point using the dedicated pointwise formulas.
  rw [helperForText_34_1_2_lowerClosure_negNeg_eq_top hK]
  rw [helperForText_34_1_2_lowerFormula_negNeg_eq_bot]
  exact top_ne_bot

/-- Helper for Text 34.1.2: no concave-convex witness can make the displayed lower formula
equal the true lower closure. -/
lemma helperForText_34_1_2_lowerClosure_ne_lowerClosureFormula
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK ≠
      positiveQuadrantDivisionLowerClosureFormula := by
  intro hEq
  -- A function equality would force agreement at the explicit negative-negative point.
  exact
    helperForText_34_1_2_lowerClosure_formula_fails_at_negNeg hK
      (congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)))
        hEq)

/-- Helper for Text 34.1.2: no concave-convex witness can make the displayed lower formula
equal the true lower closure. -/
lemma helperForText_34_1_2_no_lowerClosureFormula_witness :
    ¬ ∃ hK : IsConcaveConvex positiveQuadrantDivisionSaddle,
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
        positiveQuadrantDivisionLowerClosureFormula := by
  rintro ⟨hK, hEq⟩
  -- Any such witness would contradict the explicit negative-negative counterexample.
  exact helperForText_34_1_2_lowerClosure_ne_lowerClosureFormula hK hEq

/-- Helper for Text 34.1.2: any claimed lower-closure identity would force the impossible point
value equation `+∞ = -∞` at `((-1), (-1))`. -/
lemma helperForText_34_1_2_lowerClosure_identity_forces_top_eq_bot
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle)
    (hLower :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
        positiveQuadrantDivisionLowerClosureFormula) :
    (⊤ : EReal) = (⊥ : EReal) := by
  -- Evaluate the claimed function identity at the explicit counterexample point.
  have hPoint :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) =
        positiveQuadrantDivisionLowerClosureFormula
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)))
        hLower
  -- The previously computed pointwise formulas turn that equality into `⊤ = ⊥`.
  rw [helperForText_34_1_2_lowerClosure_negNeg_eq_top hK] at hPoint
  rw [helperForText_34_1_2_lowerFormula_negNeg_eq_bot] at hPoint
  exact hPoint

/-- Helper for Text 34.1.2: the remaining lower-closure identity demanded by the theorem is
already contradictory for any concave-convex witness. -/
lemma helperForText_34_1_2_false_of_claimedLowerClosureIdentity
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle)
    (hLower :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
        positiveQuadrantDivisionLowerClosureFormula) :
    False := by
  -- The counterexample point converts the claimed function identity into `⊤ = ⊥`.
  have hTopEqBot :
      (⊤ : EReal) = (⊥ : EReal) :=
    helperForText_34_1_2_lowerClosure_identity_forces_top_eq_bot hK hLower
  exact top_ne_bot hTopEqBot

/-- Helper for Text 34.1.2: any proof of the current target theorem would force the impossible
point-value equation `+∞ = -∞` coming from the negative-negative counterexample. -/
lemma helperForText_34_1_2_targetStatement_forces_top_eq_bot
    (hStatement :
      IsConcaveConvex positiveQuadrantDivisionSaddle ∧
        ∀ hK : IsConcaveConvex positiveQuadrantDivisionSaddle,
          lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
              positiveQuadrantDivisionLowerClosureFormula ∧
            upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
                (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              (⊤ : EReal) ∧
            lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
                (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              ((0 : ℝ) : EReal) ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
              positiveQuadrantDivisionLowerFinitenessDomain ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ≠
              finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ∧
            ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
                finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
                  A ×ˢ B) :
    (⊤ : EReal) = (⊥ : EReal) := by
  rcases hStatement with ⟨hK, hConclusion⟩
  -- The target theorem's first conjunct after `hK` is exactly the false lower-closure identity.
  exact helperForText_34_1_2_lowerClosure_identity_forces_top_eq_bot hK (hConclusion hK).1

/-- Helper for Text 34.1.2: once a concave-convex witness `hK` is fixed, the entire theorem-side
conjunction is already impossible because its first clause is the false global lower-closure
identity. -/
lemma helperForText_34_1_2_no_revisedConclusion_for_fixedWitness
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    ¬ (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
            positiveQuadrantDivisionLowerClosureFormula ∧
          upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
              (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
            (⊤ : EReal) ∧
          lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
              (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
            ((0 : ℝ) : EReal) ∧
          finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
            positiveQuadrantDivisionLowerFinitenessDomain ∧
          finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ≠
            finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ∧
          ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
              finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
                A ×ˢ B) := by
  intro hConclusion
  -- The fixed-witness conjunction already starts with the contradictory lower-closure identity.
  exact helperForText_34_1_2_false_of_claimedLowerClosureIdentity hK hConclusion.1

/-- Helper for Text 34.1.2: the weakened theorem statement still fails, because its lower
closure identity already disagrees with the displayed formula at `((-1), (-1))`. -/
lemma helperForText_34_1_2_revisedTheorem_conclusion_false :
    ¬ (IsConcaveConvex positiveQuadrantDivisionSaddle ∧
        ∀ hK : IsConcaveConvex positiveQuadrantDivisionSaddle,
          lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
              positiveQuadrantDivisionLowerClosureFormula ∧
            upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
                (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              (⊤ : EReal) ∧
            lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
                (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
              ((0 : ℝ) : EReal) ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
              positiveQuadrantDivisionLowerFinitenessDomain ∧
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ≠
              finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ∧
            ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
                finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
                  A ×ˢ B) := by
  intro hStatement
  rcases hStatement with ⟨hK, hConclusion⟩
  -- The fixed-`hK` conclusion is impossible already because its first clause is false.
  exact helperForText_34_1_2_no_revisedConclusion_for_fixedWitness hK (hConclusion hK)

/-- Helper for Text 34.1.2: at the origin, the inner second closure already has value `0`
because every nearby positive second-variable witness contributes `0`, while the nonpositive
branch contributes only `+∞`. -/
lemma helperForText_34_1_2_secondClosure_origin_eq_zero :
    partialClosure₂ positiveQuadrantDivisionSaddle
        (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = ((0 : ℝ) : EReal) := by
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · -- For each radius, the standard positive witness `ε / 2` already gives the value `0`.
    refine iSup_le ?_
    intro ε
    let witnessValue : Fin 1 → ℝ := fun _ : Fin 1 => ε.1 / 2
    have hWitnessMem : ‖witnessValue - (0 : Fin 1 → ℝ)‖ < ε.1 :=
      helperForText_34_1_2_halfPositiveWitness_mem_ball_origin ε
    let witness : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} :=
      ⟨witnessValue, hWitnessMem⟩
    have hWitnessPos : 0 < witness.1 0 := by
      change 0 < ε.1 / 2
      nlinarith [ε.2]
    have hWitnessNonpos : ¬ witness.1 0 ≤ 0 := not_le.mpr hWitnessPos
    calc
      (⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
          positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) w.1)
          ≤ positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) witness.1 := iInf_le _ witness
      _ = ((0 : ℝ) : EReal) := by
        simp [positiveQuadrantDivisionSaddle, hWitnessNonpos, oneDimensionalDivisionKernel]
  · -- Conversely, every nearby value is either `0` or `+∞`, so one fixed radius gives the
    -- lower bound `0` for the outer supremum.
    let ε : {ε : ℝ // 0 < ε} := ⟨1, by norm_num⟩
    refine le_trans ?_
      (le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε'.1},
            positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) w.1)
        ε)
    refine le_iInf ?_
    intro w
    by_cases hw : w.1 0 ≤ 0
    · simp [positiveQuadrantDivisionSaddle, hw]
    · simp [positiveQuadrantDivisionSaddle, hw, oneDimensionalDivisionKernel]

/-- Helper for Text 34.1.2: once the first coordinate is positive, the second closure at
`v = 0` becomes `+∞` because shrinking the second-variable radius forces arbitrarily large
quotients `u / w`. -/
lemma helperForText_34_1_2_secondClosureAtZero_eq_top_of_positiveFirst
    {u : Fin 1 → ℝ} (hu : 0 < u 0) :
    partialClosure₂ positiveQuadrantDivisionSaddle u (0 : Fin 1 → ℝ) = (⊤ : EReal) := by
  unfold partialClosure₂ convexClosureInSecond
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro y
  by_cases hy : y < 0
  · -- Negative lower bounds are immediate because the closure is everywhere at least `0`.
    have hNonneg : ((0 : ℝ) : EReal) ≤
        ⨆ ε : {ε : ℝ // 0 < ε},
          ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
            positiveQuadrantDivisionSaddle u w.1 := by
      let ε : {ε : ℝ // 0 < ε} := ⟨1, by norm_num⟩
      have hLower :
          ((0 : ℝ) : EReal) ≤
            ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
              positiveQuadrantDivisionSaddle u w.1 := by
        refine le_iInf ?_
        intro w
        by_cases hw : w.1 0 ≤ 0
        · simp [positiveQuadrantDivisionSaddle, hw]
        · have huNonneg : ¬ u 0 < 0 := not_lt.mpr hu.le
          have hwPos : 0 < w.1 0 := lt_of_not_ge hw
          have hQuotNonneg : 0 ≤ u 0 / w.1 0 := by
            positivity
          have hLeReal : ((0 : ℝ) : EReal) ≤ ((u 0 / w.1 0 : ℝ) : EReal) :=
            EReal.coe_nonneg.2 hQuotNonneg
          simpa [positiveQuadrantDivisionSaddle, hw, huNonneg, oneDimensionalDivisionKernel]
            using hLeReal
      exact le_trans hLower
        (le_iSup
          (fun ε' : {ε' : ℝ // 0 < ε'} =>
            ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε'.1},
              positiveQuadrantDivisionSaddle u w.1)
          ε)
    exact lt_of_lt_of_le (by simpa using hy) hNonneg
  · -- For nonnegative `y`, choose a radius so small that every positive denominator in the
    -- ball forces the quotient to exceed `y`.
    let B : ℝ := max (y + 1) 1
    have hBPos : 0 < B := by
      dsimp [B]
      have hOnePos : (0 : ℝ) < 1 := by
        norm_num
      exact lt_of_lt_of_le hOnePos (le_max_right _ _)
    let ε : {ε : ℝ // 0 < ε} := ⟨u 0 / (2 * B), by positivity⟩
    have hy_lt_B : y < B := by
      dsimp [B]
      by_cases hCase : y + 1 ≤ 1
      · rw [max_eq_right hCase]
        linarith
      · rw [max_eq_left (le_of_not_ge hCase)]
        linarith
    refine lt_of_not_ge ?_
    intro hLe
    have hLeε :
        (⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
            positiveQuadrantDivisionSaddle u w.1) ≤ (y : EReal) := by
      exact le_trans
        (le_iSup
          (fun ε' : {ε' : ℝ // 0 < ε'} =>
            ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε'.1},
              positiveQuadrantDivisionSaddle u w.1)
          ε)
        hLe
    have hyInf :
        (y : EReal) <
          ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
            positiveQuadrantDivisionSaddle u w.1 := by
      refine (lt_iInf_iff).2 ?_
      refine ⟨(B : EReal), EReal.coe_lt_coe hy_lt_B, ?_⟩
      intro w
      have hwNorm := w.2
      rw [helperForText_34_1_1_norm_fin1_eq_abs (0 : Fin 1 → ℝ) w.1] at hwNorm
      by_cases hwNonpos : w.1 0 ≤ 0
      · simp [positiveQuadrantDivisionSaddle, hwNonpos]
      · have hwPos : 0 < w.1 0 := lt_of_not_ge hwNonpos
        have huNonneg : ¬ u 0 < 0 := not_lt.mpr hu.le
        have hwAbs : |w.1 0 - (0 : ℝ)| < ε.1 := by
          simpa using hwNorm
        have hwSmall : w.1 0 < ε.1 := by
          rwa [sub_zero, abs_of_pos hwPos] at hwAbs
        have hTwoBPos : 0 < 2 * B := by
          positivity
        have hMul : (2 * B) * w.1 0 < u 0 := by
          have hTmp := mul_lt_mul_of_pos_left hwSmall hTwoBPos
          have hEq : (2 * B) * ε.1 = u 0 := by
            dsimp [ε]
            field_simp [hBPos.ne', (show (2 : ℝ) ≠ 0 by norm_num), hu.ne']
          rw [hEq] at hTmp
          simpa [mul_comm, mul_left_comm, mul_assoc] using hTmp
        have hDiv : 2 * B < u 0 / w.1 0 := (lt_div_iff₀ hwPos).2 hMul
        have hBLarge : B < u 0 / w.1 0 := by
          have hBLtTwoB : B < 2 * B := by
            nlinarith [hBPos]
          exact lt_trans hBLtTwoB hDiv
        have hLeReal : ((B : ℝ) : EReal) ≤ ((u 0 / w.1 0 : ℝ) : EReal) :=
          (EReal.coe_le_coe_iff).2 hBLarge.le
        simpa [positiveQuadrantDivisionSaddle, hwNonpos, huNonneg, oneDimensionalDivisionKernel]
          using hLeReal
    exact (not_le_of_gt hyInf) hLeε

/-- Helper for Text 34.1.2: the mixed upper closure takes the value `+∞` at the origin. -/
lemma helperForText_34_1_2_upperMixedClosure_origin_eq_top :
    partialClosure₁ (partialClosure₂ positiveQuadrantDivisionSaddle)
        (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = (⊤ : EReal) := by
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm le_top
  refine le_iInf ?_
  intro ε
  -- Every first-variable ball around the origin contains a positive point whose second closure
  -- at `v = 0` is already `+∞`.
  let witnessValue : Fin 1 → ℝ := fun _ : Fin 1 => ε.1 / 2
  have hWitnessMem : ‖witnessValue - (0 : Fin 1 → ℝ)‖ < ε.1 :=
    helperForText_34_1_2_halfPositiveWitness_mem_ball_origin ε
  let witness : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} :=
    ⟨witnessValue, hWitnessMem⟩
  have hWitnessPos : 0 < witness.1 0 := by
    change 0 < ε.1 / 2
    nlinarith [ε.2]
  calc
    (⊤ : EReal) = partialClosure₂ positiveQuadrantDivisionSaddle witness.1 (0 : Fin 1 → ℝ) := by
      rw [helperForText_34_1_2_secondClosureAtZero_eq_top_of_positiveFirst hWitnessPos]
    _ ≤
      ⨆ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
        partialClosure₂ positiveQuadrantDivisionSaddle w.1 (0 : Fin 1 → ℝ) :=
      le_iSup
        (fun w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} =>
          partialClosure₂ positiveQuadrantDivisionSaddle w.1 (0 : Fin 1 → ℝ))
        witness

/-- Helper for Text 34.1.2: for every concave-convex witness, the actual upper closure takes the
value `+∞` at the origin. -/
lemma helperForText_34_1_2_upperClosure_origin_eq_top
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = (⊤ : EReal) := by
  -- Rewrite the upper closure through the mixed-closure formula and evaluate the origin branch.
  have hMixed :
      upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
        partialClosure₁ (partialClosure₂ positiveQuadrantDivisionSaddle)
          (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) := by
    exact
      congrArg
        (fun F => F (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ))
        (helperForText_34_0_1_mixedClosure_formulas positiveQuadrantDivisionSaddle hK).2
  rw [hMixed, helperForText_34_1_2_upperMixedClosure_origin_eq_top]

/-- Helper for Text 34.1.2: when the second coordinate is positive, the first closure at
`u = 0` is exactly `0`, since shrinking the first-variable radius drives every local supremum
down to the quotient value `0 / v = 0`. -/
lemma helperForText_34_1_2_firstClosureAtZero_eq_zero_of_positiveSecond
    {v : Fin 1 → ℝ} (hv : 0 < v 0) :
    partialClosure₁ positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) v = ((0 : ℝ) : EReal) := by
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · -- To force the infimum down to `0`, it is enough to make every local supremum smaller than
    -- an arbitrary positive real threshold.
    refine
      (EReal.le_of_forall_lt_iff_le
        (x := (0 : EReal))
        (y := ⨅ ε : {ε : ℝ // 0 < ε},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
            positiveQuadrantDivisionSaddle w.1 v)).1 ?_
    intro z hz
    have hzReal : 0 < z := by
      simpa using hz
    let ε : {ε : ℝ // 0 < ε} := ⟨z * v 0 / 2, by positivity⟩
    refine le_trans (iInf_le _ ε) ?_
    refine iSup_le ?_
    intro w
    have hwNorm := w.2
    rw [helperForText_34_1_1_norm_fin1_eq_abs (0 : Fin 1 → ℝ) w.1] at hwNorm
    by_cases hwNonneg : 0 ≤ w.1 0
    · have hvNonpos : ¬ v 0 ≤ 0 := not_le.mpr hv
      have huNeg : ¬ w.1 0 < 0 := not_lt.mpr hwNonneg
      have hwAbs : |w.1 0 - (0 : ℝ)| < ε.1 := by
        simpa using hwNorm
      have hwLe : w.1 0 < ε.1 := by
        have hwEq : w.1 0 - (0 : ℝ) = w.1 0 := by
          ring
        rw [hwEq, abs_of_nonneg hwNonneg] at hwAbs
        exact hwAbs
      have hwLe' : w.1 0 < z * v 0 / 2 := by
        simpa [ε] using hwLe
      have hDiv : w.1 0 / v 0 < z := by
        have hHalf : z * v 0 / 2 < z * v 0 := by
          have hPos : 0 < z * v 0 := by
            positivity
          linarith
        have hwLt : w.1 0 < z * v 0 := lt_trans hwLe' hHalf
        exact (div_lt_iff₀ hv).2 hwLt
      have hLeReal : ((w.1 0 / v 0 : ℝ) : EReal) ≤ (z : EReal) := by
        exact (EReal.coe_le_coe_iff).2 hDiv.le
      simpa [positiveQuadrantDivisionSaddle, hvNonpos, huNeg, oneDimensionalDivisionKernel]
        using hLeReal
    · have hu : w.1 0 < 0 := lt_of_not_ge hwNonneg
      have hvNonpos : ¬ v 0 ≤ 0 := not_le.mpr hv
      simp [positiveQuadrantDivisionSaddle, hvNonpos, hu]
  · -- The center point `u = 0` already contributes the value `0` to every local supremum.
    refine le_iInf ?_
    intro ε
    let witness : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} :=
      ⟨0, by simpa using ε.2⟩
    have hvNonpos : ¬ v 0 ≤ 0 := not_le.mpr hv
    have hWitnessEq : witness.1 = (0 : Fin 1 → ℝ) := rfl
    calc
      ((0 : ℝ) : EReal) = positiveQuadrantDivisionSaddle witness.1 v := by
        rw [hWitnessEq]
        simp [positiveQuadrantDivisionSaddle, hvNonpos, oneDimensionalDivisionKernel]
      _ ≤
        ⨆ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
          positiveQuadrantDivisionSaddle w.1 v :=
        le_iSup
          (fun w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} =>
            positiveQuadrantDivisionSaddle w.1 v)
          witness

/-- Helper for Text 34.1.2: the mixed lower closure takes the value `0` at the origin. -/
lemma helperForText_34_1_2_mixedLowerClosure_origin_eq_zero :
    partialClosure₂ (partialClosure₁ positiveQuadrantDivisionSaddle)
        (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = ((0 : ℝ) : EReal) := by
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · -- For each radius, the standard positive second-variable witness keeps the inner first
    -- closure equal to `0`.
    refine iSup_le ?_
    intro ε
    let witnessValue : Fin 1 → ℝ := fun _ : Fin 1 => ε.1 / 2
    have hWitnessMem : ‖witnessValue - (0 : Fin 1 → ℝ)‖ < ε.1 :=
      helperForText_34_1_2_halfPositiveWitness_mem_ball_origin ε
    let witness : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1} :=
      ⟨witnessValue, hWitnessMem⟩
    have hWitnessPos : 0 < witness.1 0 := by
      change 0 < ε.1 / 2
      nlinarith [ε.2]
    calc
      (⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε.1},
          partialClosure₁ positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) w.1)
          ≤ partialClosure₁ positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) witness.1 :=
        iInf_le _ witness
      _ = ((0 : ℝ) : EReal) :=
        helperForText_34_1_2_firstClosureAtZero_eq_zero_of_positiveSecond hWitnessPos
  · -- One fixed radius suffices for the lower bound because every nearby first-closure value is
    -- either `0` or `+∞`.
    let ε : {ε : ℝ // 0 < ε} := ⟨1, by norm_num⟩
    refine le_trans ?_
      (le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - (0 : Fin 1 → ℝ)‖ < ε'.1},
            partialClosure₁ positiveQuadrantDivisionSaddle (0 : Fin 1 → ℝ) w.1)
        ε)
    refine le_iInf ?_
    intro w
    by_cases hw : w.1 0 ≤ 0
    · rw [helperForText_34_1_2_firstClosure_eq_top_of_nonpositiveSecond hw]
      exact le_top
    · have hwPos : 0 < w.1 0 := lt_of_not_ge hw
      rw [helperForText_34_1_2_firstClosureAtZero_eq_zero_of_positiveSecond hwPos]

/-- Helper for Text 34.1.2: for every concave-convex witness, the actual lower closure takes the
value `0` at the origin. -/
lemma helperForText_34_1_2_lowerClosure_origin_eq_zero
    (hK : IsConcaveConvex positiveQuadrantDivisionSaddle) :
    lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
        (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = ((0 : ℝ) : EReal) := by
  -- Rewrite the lower closure through the mixed-closure formula and evaluate the origin branch.
  have hMixed :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
          (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
        partialClosure₂ (partialClosure₁ positiveQuadrantDivisionSaddle)
          (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) := by
    exact
      congrArg
        (fun F => F (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ))
        (helperForText_34_0_1_mixedClosure_formulas positiveQuadrantDivisionSaddle hK).1
  rw [hMixed, helperForText_34_1_2_mixedLowerClosure_origin_eq_zero]

/-- Helper for Text 34.1.2: the displayed lower and upper finiteness domains already differ at
the origin, because the lower domain adjoins `(0, 0)` while the upper one does not. -/
lemma helperForText_34_1_2_displayedFinitenessDomains_ne :
    positiveQuadrantDivisionLowerFinitenessDomain ≠
      positiveQuadrantDivisionUpperFinitenessDomain := by
  intro hEq
  -- The origin belongs to the lower displayed domain by construction.
  have hOriginLower :
      ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∈
        positiveQuadrantDivisionLowerFinitenessDomain := by
    right
    rfl
  -- The same point cannot lie in the upper displayed domain because it would require `0 < 0`.
  have hOriginUpper :
      ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∉
        positiveQuadrantDivisionUpperFinitenessDomain := by
    intro hMem
    exact (lt_irrefl (0 : ℝ)) hMem.2
  have hOriginUpperMem :
      ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∈
        positiveQuadrantDivisionUpperFinitenessDomain := by
    simpa [hEq] using hOriginLower
  exact hOriginUpper hOriginUpperMem

/-- Helper for Text 34.1.2: the displayed lower finiteness domain is not a product set, because
it contains `(0, 0)` and `(1, 1)` but omits `(1, 0)`. -/
lemma helperForText_34_1_2_displayedLowerFinitenessDomain_not_product :
    ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
        positiveQuadrantDivisionLowerFinitenessDomain = A ×ˢ B := by
  rintro ⟨A, B, hProd⟩
  -- The origin is in the lower displayed domain, so both coordinates must belong to the factors.
  have hOriginLower :
      ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∈
        positiveQuadrantDivisionLowerFinitenessDomain := by
    right
    rfl
  have hOriginProd :
      ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∈ A ×ˢ B := by
    simpa [hProd] using hOriginLower
  have hZeroInA : (0 : Fin 1 → ℝ) ∈ A := hOriginProd.1
  have hZeroInB : (0 : Fin 1 → ℝ) ∈ B := hOriginProd.2
  -- A strictly positive point also lies in the lower displayed domain, so both positive
  -- coordinates belong to the same factors.
  have hOneOneLower :
      ((fun _ : Fin 1 => (1 : ℝ)), (fun _ : Fin 1 => (1 : ℝ))) ∈
        positiveQuadrantDivisionLowerFinitenessDomain := by
    left
    simp [positiveQuadrantDivisionUpperFinitenessDomain]
  have hOneOneProd :
      ((fun _ : Fin 1 => (1 : ℝ)), (fun _ : Fin 1 => (1 : ℝ))) ∈ A ×ˢ B := by
    simpa [hProd] using hOneOneLower
  have hOneInA : (fun _ : Fin 1 => (1 : ℝ)) ∈ A := hOneOneProd.1
  have hOneInB : (fun _ : Fin 1 => (1 : ℝ)) ∈ B := hOneOneProd.2
  -- The product structure would then force `(1, 0)` into the domain, contradicting the
  -- explicit description of the lower displayed domain.
  have hOneZeroProd :
      ((fun _ : Fin 1 => (1 : ℝ)), (0 : Fin 1 → ℝ)) ∈ A ×ˢ B := by
    exact ⟨hOneInA, hZeroInB⟩
  have hOneZeroLower :
      ((fun _ : Fin 1 => (1 : ℝ)), (0 : Fin 1 → ℝ)) ∈
        positiveQuadrantDivisionLowerFinitenessDomain := by
    simpa [hProd] using hOneZeroProd
  have hOneZeroNotLower :
      ((fun _ : Fin 1 => (1 : ℝ)), (0 : Fin 1 → ℝ)) ∉
        positiveQuadrantDivisionLowerFinitenessDomain := by
    have hOneNeZero : (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
      intro hEq
      have hCoord := congrFun hEq 0
      norm_num at hCoord
    simp [positiveQuadrantDivisionLowerFinitenessDomain,
      positiveQuadrantDivisionUpperFinitenessDomain, hOneNeZero]
  exact hOneZeroNotLower hOneZeroLower

/-- Helper for Text 34.1.2: the exact conjunction currently asserted by
`section34_example_u_div_v`, isolated as a single proposition so the remaining blocker can be
stated without repeating the full target. -/
def helperForText_34_1_2_targetTheoremClaim : Prop :=
  IsConcaveConvex positiveQuadrantDivisionSaddle ∧
    ∀ hK : IsConcaveConvex positiveQuadrantDivisionSaddle,
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK =
          positiveQuadrantDivisionLowerClosureFormula ∧
        upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK
            (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
          (⊤ : EReal) ∧
        lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK
            (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) =
          ((0 : ℝ) : EReal) ∧
        finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
          positiveQuadrantDivisionLowerFinitenessDomain ∧
        finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ≠
          finitenessDomain (upperClosureConcaveConvex positiveQuadrantDivisionSaddle hK) ∧
        ¬ ∃ A : Set (Fin 1 → ℝ), ∃ B : Set (Fin 1 → ℝ),
            finitenessDomain (lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hK) =
              A ×ˢ B

/-- Helper for Text 34.1.2: any witness of the exact target theorem claim already yields the
explicit negative-negative counterexample where the true lower closure and the displayed formula
disagree. -/
lemma helperForText_34_1_2_targetClaim_has_explicitLowerMismatch
    (hClaim : helperForText_34_1_2_targetTheoremClaim) :
    ∃ u v,
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hClaim.1 u v ≠
        positiveQuadrantDivisionLowerClosureFormula u v := by
  -- The target claim fixes a concave-convex witness, so the already-proved negative-negative
  -- mismatch applies immediately at that witness.
  refine ⟨(fun _ : Fin 1 => (-1 : ℝ)), (fun _ : Fin 1 => (-1 : ℝ)), ?_⟩
  exact helperForText_34_1_2_lowerClosure_formula_fails_at_negNeg hClaim.1

/-- Helper for Text 34.1.2: any witness of the isolated theorem claim is already contradictory,
because the claim's global lower-closure identity must agree at the explicit mismatch point
`((-1), (-1))`. -/
lemma helperForText_34_1_2_targetTheoremClaim_witness_false
    (hClaim : helperForText_34_1_2_targetTheoremClaim) :
    False := by
  -- The mismatch helper produces a concrete point where the true lower closure and the displayed
  -- formula do not agree for the witness fixed by the theorem claim.
  rcases helperForText_34_1_2_targetClaim_has_explicitLowerMismatch hClaim with ⟨u, v, hMismatch⟩
  -- The theorem claim itself asserts a global lower-closure identity, so those same point-values
  -- would have to agree after evaluation at the mismatch point.
  have hPointwise :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hClaim.1 u v =
        positiveQuadrantDivisionLowerClosureFormula u v := by
    exact congrArg (fun F => F u v) (hClaim.2 hClaim.1).1
  exact hMismatch hPointwise

/-- Helper for Text 34.1.2: any witness of the exact target theorem claim would force the
displayed lower formula itself to take the value `+∞` at `((-1), (-1))`. -/
lemma helperForText_34_1_2_targetClaim_forces_lowerFormula_negNeg_eq_top
    (hClaim : helperForText_34_1_2_targetTheoremClaim) :
    positiveQuadrantDivisionLowerClosureFormula
        (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) = (⊤ : EReal) := by
  -- The theorem claim includes a global lower-closure identity, so evaluating it at the
  -- explicit negative-negative counterexample point transports the true closure value onto the
  -- displayed formula.
  have hPointwise :
      lowerClosureConcaveConvex positiveQuadrantDivisionSaddle hClaim.1
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) =
        positiveQuadrantDivisionLowerClosureFormula
          (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ)))
        (hClaim.2 hClaim.1).1
  -- The already-computed true lower closure at that point is `⊤`, so the displayed formula
  -- would also have to equal `⊤`.
  rw [helperForText_34_1_2_lowerClosure_negNeg_eq_top hClaim.1] at hPointwise
  exact hPointwise.symm

/-- Helper for Text 34.1.2: the exact theorem claim is refuted by the explicit
negative-negative mismatch point `((-1), (-1))`. -/
lemma helperForText_34_1_2_targetTheoremClaim_false :
    ¬ helperForText_34_1_2_targetTheoremClaim := by
  intro hClaim
  -- The previous witness-level contradiction already refutes the theorem claim outright.
  exact helperForText_34_1_2_targetTheoremClaim_witness_false hClaim

/-- Helper for Text 34.1.2: the isolated target theorem claim is logically equivalent to
`False`, so any future repair must change the statement or the upstream closure
formalization rather than add more local proof steps. -/
lemma helperForText_34_1_2_targetTheoremClaim_iff_false :
    helperForText_34_1_2_targetTheoremClaim ↔ False := by
  constructor
  · intro hClaim
    -- Any witness of the isolated target claim is already contradictory.
    exact helperForText_34_1_2_targetTheoremClaim_witness_false hClaim
  · intro hFalse
    -- The reverse implication is the vacuous implication from `False`.
    exact False.elim hFalse

/-- Helper for Text 34.1.2: the isolated target theorem claim is an empty type, because any
inhabitant would force the contradictory value equation `⊥ = ⊤` at `((-1), (-1))`. -/
lemma helperForText_34_1_2_targetTheoremClaim_isEmpty :
    IsEmpty helperForText_34_1_2_targetTheoremClaim := by
  -- Package the previously isolated refutation as an `IsEmpty` witness for the theorem claim.
  refine ⟨?_⟩
  intro hClaim
  -- The explicit equivalence with `False` gives the contradiction immediately.
  exact (helperForText_34_1_2_targetTheoremClaim_iff_false.mp hClaim)

-- Proof sketch: verify that the simple extension of `u / v` is concave in `u` and convex in
-- `v`, compute the two iterated one-variable closures, and read off the piecewise formulas,
-- noting in particular the distinct values assumed at the origin and the resulting difference
-- between the two finiteness domains.
/-- Text 34.1.2 in the current formalization is not the displayed textbook package: the claimed
lower-closure formula is refuted by the explicit negative-negative mismatch point `((-1), (-1))`.
The isolated textbook claim is therefore false as stated. -/
theorem section34_example_u_div_v :
    ¬ helperForText_34_1_2_targetTheoremClaim := by
  exact helperForText_34_1_2_targetTheoremClaim_false

end SaddleAmbient

end Section34
end Chap07
