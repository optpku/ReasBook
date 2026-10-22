/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part3
open scoped BigOperators Pointwise
section Chap06
section Section28
/-- Helper for Theorem 6.28.3: convex combinations of feasible points for two perturbed problems
remain feasible for the convexly combined perturbation. -/
lemma helperForTheorem_6_28_3_convexCombination_mem_perturbedFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    {u1 u2 : Fin m → ℝ} {x1 x2 : Fin n → ℝ} {t : ℝ}
    (hx1 : x1 ∈ (P.perturbedProblem u1).feasibleSet)
    (hx2 : x2 ∈ (P.perturbedProblem u2).feasibleSet)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x1 + t • x2 ∈
      (P.perturbedProblem ((1 - t) • u1 + t • u2)).feasibleSet := by
  rcases hx1 with ⟨hx1C, hx1Ineq, hx1Eq⟩
  rcases hx2 with ⟨hx2C, hx2Ineq, hx2Eq⟩
  -- First keep the segment point inside the ambient convex constraint set.
  have hxComboC :
      (1 - t) • x1 + t • x2 ∈ P.constraintSet :=
    P.convex_constraintSet hx1C hx2C (sub_nonneg.mpr ht1) ht0 (by ring)
  refine ⟨hxComboC, ?_, ?_⟩
  · intro i
    -- Convexity of the `i`-th inequality constraint transports the two perturbed bounds to the
    -- segment point.
    have hx1Ineq' :
        P.inequalityConstraint i x1 ≤ P.inequalityPerturbation u1 i := by
      exact sub_nonpos.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hx1Ineq i)
    have hx2Ineq' :
        P.inequalityConstraint i x2 ≤ P.inequalityPerturbation u2 i := by
      exact sub_nonpos.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hx2Ineq i)
    have hconstraint :
        P.inequalityConstraint i ((1 - t) • x1 + t • x2) ≤
          (1 - t) * P.inequalityConstraint i x1 + t * P.inequalityConstraint i x2 := by
      simpa [smul_eq_mul] using
        (P.inequalityConstraint_convexOn i).2 hx1C hx2C (sub_nonneg.mpr ht1) ht0 (by ring)
    have hperturb :
        P.inequalityPerturbation ((1 - t) • u1 + t • u2) i =
          (1 - t) * P.inequalityPerturbation u1 i + t * P.inequalityPerturbation u2 i := by
      simp [BookOrdinaryConvexProgram.inequalityPerturbation, Function.comp, smul_eq_mul]
    have hle :
        P.inequalityConstraint i ((1 - t) • x1 + t • x2) ≤
          P.inequalityPerturbation ((1 - t) • u1 + t • u2) i := by
      rw [hperturb]
      nlinarith
    exact sub_nonpos.mpr hle
  · intro j
    -- Affinity of the `j`-th equality constraint keeps exact equalities compatible with taking
    -- convex combinations.
    have hx1Eq' :
        P.equalityConstraint j x1 = P.equalityPerturbation u1 j := by
      exact sub_eq_zero.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hx1Eq j)
    have hx2Eq' :
        P.equalityConstraint j x2 = P.equalityPerturbation u2 j := by
      exact sub_eq_zero.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hx2Eq j)
    rcases P.equalityConstraint_affineOn j with ⟨a, ha⟩
    have hconstraint :
        P.equalityConstraint j ((1 - t) • x1 + t • x2) =
          (1 - t) * P.equalityConstraint j x1 + t * P.equalityConstraint j x2 := by
      calc
        P.equalityConstraint j ((1 - t) • x1 + t • x2)
            = a ((1 - t) • x1 + t • x2) := by
              simpa using ha hxComboC
        _ = (1 - t) * a x1 + t * a x2 := by
              simpa [smul_eq_mul] using
                (Convex.combo_affine_apply
                  (x := x1) (y := x2) (a := 1 - t) (b := t) (f := a) (by ring))
        _ = (1 - t) * P.equalityConstraint j x1 + t * P.equalityConstraint j x2 := by
              rw [← ha hx1C, ← ha hx2C]
    have hperturb :
        P.equalityPerturbation ((1 - t) • u1 + t • u2) j =
          (1 - t) * P.equalityPerturbation u1 j + t * P.equalityPerturbation u2 j := by
      simp [BookOrdinaryConvexProgram.equalityPerturbation, Function.comp, smul_eq_mul]
    calc
      P.equalityConstraint j ((1 - t) • x1 + t • x2) -
          P.equalityPerturbation ((1 - t) • u1 + t • u2) j
          = ((1 - t) * P.equalityConstraint j x1 + t * P.equalityConstraint j x2) -
              ((1 - t) * P.equalityPerturbation u1 j + t * P.equalityPerturbation u2 j) := by
                rw [hconstraint, hperturb]
      _ = 0 := by
            rw [hx1Eq', hx2Eq']
            ring

/-- Helper for Theorem 6.28.3: a perturbation belongs to the effective domain of the perturbation
function exactly when the corresponding perturbed problem has a feasible point. -/
lemma helperForTheorem_6_28_3_mem_effectiveDomain_perturbationFunction_iff_nonempty_perturbedFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) :
    u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction ↔
      Set.Nonempty ((P.perturbedProblem u).feasibleSet) := by
  -- Rewrite effective-domain membership into finiteness of the perturbation value.
  rw [effectiveDomain_eq]
  constructor
  · rintro ⟨_, huFinite⟩
    by_contra hfeasible_empty
    -- If the perturbed feasible set were empty, the defining infimum would be `⊤`.
    have hfeasibleSet :
        (P.perturbedProblem u).feasibleSet = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hfeasible_empty
    have hperturb_top : P.perturbationFunction u = (⊤ : EReal) := by
      simp [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue,
        hfeasibleSet]
    simpa [hperturb_top] using huFinite
  · intro hfeasible
    rcases hfeasible with ⟨x, hxFeasible⟩
    refine ⟨by simp, ?_⟩
    -- Any perturbed feasible point gives a finite upper bound on the infimum.
    have hsInf_le :
        P.perturbationFunction u ≤ ((P.objective x : ℝ) : EReal) := by
      rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
      exact sInf_le ⟨x, hxFeasible, rfl⟩
    exact lt_of_le_of_lt hsInf_le (by simp)

/-- Helper for Theorem 6.28.3: a strict upper bound on the perturbation value can be realized by
an actual perturbed-feasible point whose objective lies below the same real threshold. -/
lemma helperForTheorem_6_28_3_exists_perturbedFeasiblePoint_of_perturbationFunction_lt
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {u : Fin m → ℝ} {a : ℝ}
    (hu : P.perturbationFunction u < (a : EReal)) :
    ∃ x : Fin n → ℝ, x ∈ (P.perturbedProblem u).feasibleSet ∧ P.objective x < a := by
  -- First rule out the empty feasible-set case, since an empty infimum would be `⊤`.
  by_cases hfeasible_empty : (P.perturbedProblem u).feasibleSet = ∅
  · have htop : P.perturbationFunction u = (⊤ : EReal) := by
      simp [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue,
        hfeasible_empty]
    rw [htop] at hu
    simp at hu
  · have hfeasible_nonempty : ((fun x => ((P.objective x : ℝ) : EReal)) '' (P.perturbedProblem u).feasibleSet).Nonempty := by
      rcases Set.nonempty_iff_ne_empty.mpr hfeasible_empty with ⟨x, hx⟩
      exact ⟨((P.objective x : ℝ) : EReal), ⟨x, hx, rfl⟩⟩
    -- Unfold the perturbation value and extract an image point lying below the chosen threshold.
    rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue] at hu
    rcases exists_lt_of_csInf_lt hfeasible_nonempty hu with ⟨z, hzMem, hzlt⟩
    rcases hzMem with ⟨x, hxFeasible, rfl⟩
    exact ⟨x, hxFeasible, EReal.coe_lt_coe_iff.1 hzlt⟩

/-- Helper for Theorem 6.28.3: feasible points for opposite perturbations can be convexly
combined to recover an unperturbed feasible point once the perturbations cancel. -/
lemma helperForTheorem_6_28_3_feasibleSet_mem_of_balancedPerturbationCombination
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    {u : Fin m → ℝ} {xPlus xMinus : Fin n → ℝ} {t s a b : ℝ}
    (hxPlus : xPlus ∈ (P.perturbedProblem (t • u)).feasibleSet)
    (hxMinus : xMinus ∈ (P.perturbedProblem (-s • u)).feasibleSet)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hbalance : a * t = b * s) :
    a • xPlus + b • xMinus ∈ P.feasibleSet := by
  -- The earlier convex-combination lemma already gives feasibility for the combined
  -- perturbation, so it remains only to show that the balanced perturbations sum to zero.
  have ha_eq : a = 1 - b := by
    linarith
  have hsegment :
      (1 - b) • xPlus + b • xMinus ∈
        (P.perturbedProblem ((1 - b) • (t • u) + b • (-s • u))).feasibleSet := by
    have hb_le_one : b ≤ 1 := by linarith
    simpa [sub_eq_add_neg] using
      (helperForTheorem_6_28_3_convexCombination_mem_perturbedFeasibleSet
        P hxPlus hxMinus hb hb_le_one)
  have hsegment' :
      a • xPlus + b • xMinus ∈
        (P.perturbedProblem (a • (t • u) + b • (-s • u))).feasibleSet := by
    simpa [ha_eq, smul_smul, mul_assoc] using hsegment
  have hperturb_zero : a • (t • u) + b • (-s • u) = 0 := by
    ext i
    have hscaled : a * (t * u i) = b * (s * u i) := by
      simpa [mul_assoc] using congrArg (fun z : ℝ => z * u i) hbalance
    simp [smul_eq_mul, hscaled]
  rcases hsegment' with ⟨hyC, hyIneq, hyEq⟩
  refine ⟨hyC, ?_, ?_⟩
  · intro i
    have hyIneq' :
        P.inequalityConstraint i (a • xPlus + b • xMinus) ≤
          P.inequalityPerturbation (a • (t • u) + b • (-s • u)) i := by
      exact sub_nonpos.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hyIneq i)
    have hperturbIneqZero :
        P.inequalityPerturbation (a • (t • u) + b • (-s • u)) i = 0 := by
      simpa [BookOrdinaryConvexProgram.inequalityPerturbation, Function.comp] using
        congrArg (fun w : Fin m → ℝ => P.inequalityPerturbation w i) hperturb_zero
    rw [hperturbIneqZero] at hyIneq'
    simpa using hyIneq'
  · intro j
    have hyEq' :
        P.equalityConstraint j (a • xPlus + b • xMinus) =
          P.equalityPerturbation (a • (t • u) + b • (-s • u)) j := by
      exact sub_eq_zero.mp (by simpa [BookOrdinaryConvexProgram.perturbedProblem] using hyEq j)
    have hperturbEqZero :
        P.equalityPerturbation (a • (t • u) + b • (-s • u)) j = 0 := by
      simpa [BookOrdinaryConvexProgram.equalityPerturbation, Function.comp] using
        congrArg (fun w : Fin m → ℝ => P.equalityPerturbation w j) hperturb_zero
    rw [hperturbEqZero] at hyEq'
    simpa using hyEq'

/-- Helper for Theorem 6.28.3: the objective at the balanced perturbation combination is bounded
above by the corresponding convex combination of endpoint objectives. -/
lemma helperForTheorem_6_28_3_objective_le_of_balancedPerturbationCombination
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    {u : Fin m → ℝ} {xPlus xMinus : Fin n → ℝ} {t s a b : ℝ}
    (hxPlus : xPlus ∈ (P.perturbedProblem (t • u)).feasibleSet)
    (hxMinus : xMinus ∈ (P.perturbedProblem (-s • u)).feasibleSet)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    P.objective (a • xPlus + b • xMinus) ≤
      a * P.objective xPlus + b * P.objective xMinus := by
  -- Apply convexity of the objective on the common ambient constraint set of the perturbed
  -- problems.
  have hxPlusC : xPlus ∈ P.constraintSet := hxPlus.1
  have hxMinusC : xMinus ∈ P.constraintSet := hxMinus.1
  simpa [smul_eq_mul] using
    (P.objective_convexOn.2 hxPlusC hxMinusC ha hb hab)

/-- Helper for Theorem 6.28.3: the direct generalized-program route uses the bifunction whose
finite values are exactly the objective values on perturbed feasible points. -/
noncomputable def helperForTheorem_6_28_3_directPerturbationBifunctionData
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x =>
    open scoped Classical in
    if x ∈ (P.perturbedProblem u).feasibleSet then
      ((P.objective x : ℝ) : EReal)
    else
      (⊤ : EReal)

/-- Helper for Theorem 6.28.3: the direct perturbation bifunction is convex because feasible
segment points stay feasible for convexly combined perturbations, and the objective is convex on
the ambient constraint set. -/
lemma helperForTheorem_6_28_3_directPerturbationBifunction_isConvex
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    IsConvexBifunction (helperForTheorem_6_28_3_directPerturbationBifunctionData P) := by
  intro p q a b ha hb hab
  rcases p with ⟨u1, x1⟩
  rcases q with ⟨u2, x2⟩
  by_cases hx1 : x1 ∈ (P.perturbedProblem u1).feasibleSet
  · by_cases hx2 : x2 ∈ (P.perturbedProblem u2).feasibleSet
    · -- When both endpoints are perturbed-feasible, convexity of the objective controls the
      -- direct bifunction along the corresponding segment in `(u, x)`-space.
      have hb_le_one : b ≤ 1 := by linarith
      have hsegment_feasible :
          (1 - b) • x1 + b • x2 ∈
            (P.perturbedProblem ((1 - b) • u1 + b • u2)).feasibleSet :=
        helperForTheorem_6_28_3_convexCombination_mem_perturbedFeasibleSet
          P hx1 hx2 hb hb_le_one
      have ha_eq : a = 1 - b := by linarith
      have hx1C : x1 ∈ P.constraintSet := hx1.1
      have hx2C : x2 ∈ P.constraintSet := hx2.1
      have hobjective_le :
          P.objective (a • x1 + b • x2) ≤ a * P.objective x1 + b * P.objective x2 := by
        have hconv :=
          P.objective_convexOn.2 hx1C hx2C ha hb hab
        simpa [smul_eq_mul] using hconv
      have hsegment_feasible' :
          a • x1 + b • x2 ∈ (P.perturbedProblem (a • u1 + b • u2)).feasibleSet := by
        simpa [ha_eq] using hsegment_feasible
      have hreal :
          helperForTheorem_6_28_3_directPerturbationBifunctionData P (a • u1 + b • u2)
              (a • x1 + b • x2) ≤
            ((a : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u1 x1 +
              ((b : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u2 x2 := by
        rw [helperForTheorem_6_28_3_directPerturbationBifunctionData,
          helperForTheorem_6_28_3_directPerturbationBifunctionData,
          helperForTheorem_6_28_3_directPerturbationBifunctionData,
          if_pos hsegment_feasible', if_pos hx1, if_pos hx2]
        exact_mod_cast hobjective_le
      simpa [graphFunction] using hreal
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        -- If the infeasible endpoint has coefficient `0`, the convex combination reduces to the
        -- feasible endpoint and the inequality is an equality.
        simp [graphFunction, helperForTheorem_6_28_3_directPerturbationBifunctionData,
          hx1, hx2, hb0, ha1]
      · have hb0' : 0 ≠ b := by
          intro hbEq
          exact hb0 hbEq.symm
        have hbpos : 0 < b := lt_of_le_of_ne hb hb0'
        have hbEpos : (0 : EReal) < ((b : ℝ) : EReal) := by
          exact_mod_cast hbpos
        -- A positive coefficient on an infeasible endpoint makes the right-hand side `⊤`.
        have hright_top :
            ((a : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u1 x1 +
              ((b : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u2 x2 =
              (⊤ : EReal) := by
          rw [helperForTheorem_6_28_3_directPerturbationBifunctionData,
            helperForTheorem_6_28_3_directPerturbationBifunctionData, if_pos hx1, if_neg hx2]
          rw [EReal.mul_top_of_pos hbEpos]
          exact EReal.add_top_of_ne_bot (by simp [EReal.mul_ne_bot])
        have hleft_le_top :
            graphFunction (helperForTheorem_6_28_3_directPerturbationBifunctionData P)
              (a • (u1, x1) + b • (u2, x2)) ≤ (⊤ : EReal) :=
          le_top
        simpa [graphFunction, hright_top] using hleft_le_top
  · by_cases hx2 : x2 ∈ (P.perturbedProblem u2).feasibleSet
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        -- Symmetrically, if the infeasible endpoint has coefficient `0`, the convex combination
        -- reduces to the feasible endpoint.
        simp [graphFunction, helperForTheorem_6_28_3_directPerturbationBifunctionData,
          hx1, hx2, ha0, hb1]
      · have ha0' : 0 ≠ a := by
          intro haEq
          exact ha0 haEq.symm
        have hapos : 0 < a := lt_of_le_of_ne ha ha0'
        have haEpos : (0 : EReal) < ((a : ℝ) : EReal) := by
          exact_mod_cast hapos
        -- A positive coefficient on an infeasible endpoint again forces the right-hand side to be
        -- `⊤`, so the convexity inequality is automatic.
        have hright_top :
            ((a : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u1 x1 +
              ((b : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u2 x2 =
              (⊤ : EReal) := by
          rw [helperForTheorem_6_28_3_directPerturbationBifunctionData,
            helperForTheorem_6_28_3_directPerturbationBifunctionData, if_neg hx1, if_pos hx2]
          rw [EReal.mul_top_of_pos haEpos]
          exact EReal.top_add_of_ne_bot (by simp [EReal.mul_ne_bot])
        have hleft_le_top :
            graphFunction (helperForTheorem_6_28_3_directPerturbationBifunctionData P)
              (a • (u1, x1) + b • (u2, x2)) ≤ (⊤ : EReal) :=
          le_top
        simpa [graphFunction, hright_top] using hleft_le_top
    · -- If both endpoints are infeasible, the right-hand side is already `⊤`.
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [graphFunction, helperForTheorem_6_28_3_directPerturbationBifunctionData,
          hx1, hx2, ha0, hb1]
      · have ha0' : 0 ≠ a := by
          intro haEq
          exact ha0 haEq.symm
        have hapos : 0 < a := lt_of_le_of_ne ha ha0'
        have haEpos : (0 : EReal) < ((a : ℝ) : EReal) := by
          exact_mod_cast hapos
        have hright_top :
            ((a : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u1 x1 +
              ((b : ℝ) : EReal) *
                helperForTheorem_6_28_3_directPerturbationBifunctionData P u2 x2 =
              (⊤ : EReal) := by
          rw [helperForTheorem_6_28_3_directPerturbationBifunctionData,
            helperForTheorem_6_28_3_directPerturbationBifunctionData, if_neg hx1, if_neg hx2]
          rw [EReal.mul_top_of_pos haEpos]
          exact EReal.top_add_of_ne_bot (by simp [EReal.mul_ne_bot, hb])
        have hleft_le_top :
            graphFunction (helperForTheorem_6_28_3_directPerturbationBifunctionData P)
              (a • (u1, x1) + b • (u2, x2)) ≤ (⊤ : EReal) :=
          le_top
        simpa [graphFunction, hright_top] using hleft_le_top

/-- Helper for Theorem 6.28.3: bundle the direct perturbation bifunction so that the generalized
Section 29 perturbation machinery can be applied without forcing a global indexed-program
adapter. -/
noncomputable def helperForTheorem_6_28_3_directPerturbationConvexBifunction
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    BundledConvexBifunction m n :=
  ⟨helperForTheorem_6_28_3_directPerturbationBifunctionData P,
    helperForTheorem_6_28_3_directPerturbationBifunction_isConvex P⟩

/-- Helper for Theorem 6.28.3: the generalized perturbation function of the direct bifunction is
exactly the textbook perturbation function `p(u) = val(P_u)`. -/
lemma helperForTheorem_6_28_3_generalizedPerturbationFunction_eq_perturbationFunction
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    generalizedConvexProgramPerturbationFunction
        (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) =
      P.perturbationFunction := by
  funext u
  -- Unfold both perturbation-value definitions into infima over the same feasible/indicator data.
  change
    sInf (Set.range (helperForTheorem_6_28_3_directPerturbationBifunctionData P u)) =
      sInf (((fun x => ((P.objective x : ℝ) : EReal)) '' (P.perturbedProblem u).feasibleSet))
  apply le_antisymm
  · refine le_sInf ?_
    rintro z ⟨x, hxFeasible, hxz⟩
    have hsInf_le :
        sInf (Set.range (helperForTheorem_6_28_3_directPerturbationBifunctionData P u)) ≤
          helperForTheorem_6_28_3_directPerturbationBifunctionData P u x :=
      sInf_le ⟨x, rfl⟩
    have hzObj : ((P.objective x : ℝ) : EReal) = z := by
      simpa [BookOrdinaryConvexProgram.perturbedProblem] using hxz
    calc
      sInf (Set.range (helperForTheorem_6_28_3_directPerturbationBifunctionData P u))
          ≤ helperForTheorem_6_28_3_directPerturbationBifunctionData P u x := hsInf_le
      _ = ((P.objective x : ℝ) : EReal) := by
            simp [helperForTheorem_6_28_3_directPerturbationBifunctionData, hxFeasible]
      _ = z := hzObj
  · refine le_sInf ?_
    rintro z ⟨x, hxz⟩
    by_cases hxFeasible : x ∈ (P.perturbedProblem u).feasibleSet
    · have hsInf_le :
          sInf (((fun x => ((P.objective x : ℝ) : EReal)) '' (P.perturbedProblem u).feasibleSet)) ≤
            ((P.objective x : ℝ) : EReal) :=
        sInf_le ⟨x, hxFeasible, rfl⟩
      have hzObj : z = ((P.objective x : ℝ) : EReal) := by
        simpa [helperForTheorem_6_28_3_directPerturbationBifunctionData, hxFeasible] using hxz.symm
      exact hzObj.symm ▸ hsInf_le
    · have hzTop : z = (⊤ : EReal) := by
        simpa [helperForTheorem_6_28_3_directPerturbationBifunctionData, hxFeasible] using hxz.symm
      simpa [hzTop] using
        (show
          sInf (((fun x => ((P.objective x : ℝ) : EReal)) '' (P.perturbedProblem u).feasibleSet)) ≤
            (⊤ : EReal) from
          le_top)

/-- Helper for Theorem 6.28.3: after identifying the direct bifunction perturbation function with
`P.perturbationFunction`, the corresponding effective domains coincide as well. -/
lemma helperForTheorem_6_28_3_effectiveDomain_directPerturbationConvexBifunction_eq_effectiveDomain_perturbationFunction
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    bifunctionEffectiveDomain
        (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1 =
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hsection29 :=
    generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F
  have hdom :
      erealDom (generalizedConvexProgramPerturbationFunction F) =
        bifunctionEffectiveDomain F.1 :=
    hsection29.2.1
  have hperturb :
      generalizedConvexProgramPerturbationFunction F = P.perturbationFunction :=
    helperForTheorem_6_28_3_generalizedPerturbationFunction_eq_perturbationFunction P
  ext u
  constructor
  · intro hu
    have hu' : u ∈ erealDom (generalizedConvexProgramPerturbationFunction F) := by
      simpa [hdom] using hu
    simpa [erealDom, effectiveDomain_eq, hperturb] using hu'
  · intro hu
    have hu' : u ∈ erealDom (generalizedConvexProgramPerturbationFunction F) := by
      simpa [erealDom, effectiveDomain_eq, hperturb] using hu
    simpa [hdom] using hu'

/-- Helper for Theorem 6.28.3: the direct perturbation effective domain is exactly the set of
perturbation vectors whose perturbed feasible sets are nonempty. -/
def helperForTheorem_6_28_3_directPerturbationEffectiveDomain
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) : Set (Fin m → ℝ) :=
  {u | Set.Nonempty ((P.perturbedProblem u).feasibleSet)}

/-- Helper for Theorem 6.28.3: rewriting the direct bifunction effective domain through the
perturbation function identifies it with the explicit nonempty-feasible-set domain. -/
lemma helperForTheorem_6_28_3_directPerturbationEffectiveDomain_eq_bifunctionEffectiveDomain
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    helperForTheorem_6_28_3_directPerturbationEffectiveDomain P =
      bifunctionEffectiveDomain (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1 := by
  ext u
  constructor
  · intro hu
    -- The explicit feasible-set witness is exactly the effective-domain criterion for the
    -- perturbation function, which we then transport to the direct bifunction.
    have huPerturb :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction :=
      (helperForTheorem_6_28_3_mem_effectiveDomain_perturbationFunction_iff_nonempty_perturbedFeasibleSet
        P u).2 hu
    have hdom :
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction =
          bifunctionEffectiveDomain
            (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1 :=
      (helperForTheorem_6_28_3_effectiveDomain_directPerturbationConvexBifunction_eq_effectiveDomain_perturbationFunction
        P).symm
    exact hdom ▸ huPerturb
  · intro hu
    -- Conversely, every direct-bifunction domain point yields a finite perturbation value, hence
    -- a perturbed-feasible point for the same perturbation.
    have huPerturb :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction := by
      have hdom :
          bifunctionEffectiveDomain
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1 =
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction :=
        helperForTheorem_6_28_3_effectiveDomain_directPerturbationConvexBifunction_eq_effectiveDomain_perturbationFunction
          P
      exact hdom ▸ hu
    exact
      (helperForTheorem_6_28_3_mem_effectiveDomain_perturbationFunction_iff_nonempty_perturbedFeasibleSet
        P u).1 huPerturb

/-- Helper for Theorem 6.28.3: Proposition 6.29.2 makes the explicit direct perturbation domain
convex. -/
lemma helperForTheorem_6_28_3_directPerturbationEffectiveDomain_convex
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    Convex ℝ (helperForTheorem_6_28_3_directPerturbationEffectiveDomain P) := by
  -- The direct perturbation bifunction is convex, so its effective domain is convex as well.
  have hconv :
      Convex ℝ
        (bifunctionEffectiveDomain (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1) :=
    (proposition_29_2
      (F := (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).1)
      (helperForTheorem_6_28_3_directPerturbationConvexBifunction P).2).2.2
  rw [helperForTheorem_6_28_3_directPerturbationEffectiveDomain_eq_bifunctionEffectiveDomain P]
  exact hconv

/-- Helper for Theorem 6.28.3: the direct Section 29 strong-consistency target is exactly
origin-membership in the relative interior of the explicit direct perturbation domain. -/
lemma helperForTheorem_6_28_3_directPerturbationStrongConsistency_iff_zero_mem_relativeInterior_directPerturbationEffectiveDomain
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    generalizedConvexProgramStronglyConsistent
        (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) ↔
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (helperForTheorem_6_28_3_directPerturbationEffectiveDomain P) := by
  -- Unfold strong consistency and rewrite `dom F` by the explicit feasible-set description.
  unfold generalizedConvexProgramStronglyConsistent
  rw [← helperForTheorem_6_28_3_directPerturbationEffectiveDomain_eq_bifunctionEffectiveDomain P]

/-- Helper for Theorem 6.28.3: a nonaffine-strict feasible point already shows that the origin
belongs to the explicit direct perturbation domain, even before proving the stronger relative-
interior statement. -/
lemma helperForTheorem_6_28_3_zero_mem_directPerturbationEffectiveDomain_of_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    (0 : Fin m → ℝ) ∈ helperForTheorem_6_28_3_directPerturbationEffectiveDomain P := by
  rcases hstrict_feasible with ⟨x, _hxri, hxFeasible, _⟩
  -- The zero perturbation recovers the original problem, so the given feasible witness remains
  -- feasible for the direct perturbation domain at the origin.
  exact ⟨x, by
    simpa [BookOrdinaryConvexProgram.perturbedProblem, BookOrdinaryConvexProgram.feasibleSet,
      BookOrdinaryConvexProgram.inequalityPerturbation, BookOrdinaryConvexProgram.equalityPerturbation]
      using hxFeasible⟩

/-- Helper for Theorem 6.28.3: the direct perturbation bifunction has the same optimal value as
the original ordinary convex program. -/
lemma helperForTheorem_6_28_3_directPerturbationOptimalValue_eq_optimalValue
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    generalizedConvexProgramOptimalValue
        (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) =
      P.optimalValue := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  -- Compare both optimal values through the common perturbation slice at the origin.
  calc
    generalizedConvexProgramOptimalValue F =
        generalizedConvexProgramPerturbationFunction F 0 :=
      helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F
    _ = P.perturbationFunction 0 := by
      simpa [F] using
        congrArg (fun p : (Fin m → ℝ) → EReal => p 0)
          (helperForTheorem_6_28_3_generalizedPerturbationFunction_eq_perturbationFunction P)
    _ = P.optimalValue :=
      helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P

/-- Helper for Theorem 6.28.3: finite primal value and a strict feasible point force finiteness
of the direct perturbation generalized-program optimal value. -/
lemma helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    IsFiniteEReal
      (generalizedConvexProgramOptimalValue
        (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) := by
  have hopt_eq :
      generalizedConvexProgramOptimalValue
          (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) =
        P.optimalValue :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_eq_optimalValue P
  have hopt_ne_top : P.optimalValue ≠ (⊤ : EReal) := by
    -- A feasible point for the unperturbed problem bounds the primal value above by a real number.
    simpa [helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P] using
      helperForTheorem_6_28_3_perturbationFunction_zero_ne_top P hstrict_feasible
  constructor
  · -- Transport the upper finiteness from the primal optimal value.
    simpa [hopt_eq] using hopt_ne_top
  · -- The hypothesis `P.optimalValue ≠ ⊥` transfers verbatim to the direct perturbation program.
    simpa [hopt_eq] using hoptimal_ne_bot

/-- Helper for Theorem 6.28.3: a bilateral `-∞` directional witness for the direct perturbation
function forces the opposite right-ray quotient to tend to `+∞`. -/
lemma helperForTheorem_6_28_3_leftRay_bot_witness_reformulation
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices)
    {u : Fin m → ℝ}
    (hRight :
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)))
    (hLeft :
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal))) :
    Filter.Tendsto
        (directionalDifferenceQuotientAt
          (generalizedConvexProgramPerturbationFunction
            (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 (-u))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊤ : EReal)) := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
      P hoptimal_ne_bot hstrict_feasible
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) := by
    -- Finite perturbation value at the origin is the input required for the Section 23
    -- sign-change identity.
    simpa [F, p] using helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hbilat : HasBilateralDirectionalDerivativeAt p 0 u := by
    -- Package the two one-sided limits into the bilateral derivative datum expected by the
    -- sign-reversal theorem.
    exact ⟨(⊥ : EReal), by simpa [p] using hRight, by simpa [p] using hLeft⟩
  rcases
      ((bilateralDirectionalDerivative_iff_exists_neg_direction
        (f := p) (x := 0) (y := u) hpFinite).2).1 hbilat with
    ⟨L, hRightL, hNegRight⟩
  have hEq : L = (⊥ : EReal) := by
    -- Uniqueness of limits identifies the bilateral value with the already known right limit.
    exact tendsto_nhds_unique hRightL (by simpa [p] using hRight)
  -- Rewriting `-L` with `L = ⊥` yields the promised `+∞` growth on the opposite ray.
  simpa [p, hEq] using hNegRight

/-- Helper for Theorem 6.28.3: an inequality index outside the nonaffine block already has a
global affine representative agreeing with the original constraint on `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_exists_affineRepresentative_of_affineInequalityIndex
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {i : Fin r}
    (hi : i ∉ P.nonaffineInequalityIndices) :
    ∃ a : (Fin n → ℝ) →ᵃ[ℝ] ℝ, Set.EqOn (P.inequalityConstraint i) a P.constraintSet := by
  -- Leaving the nonaffine block means exactly that the corresponding inequality is affine on the
  -- ambient constraint set.
  have hAffine :
      IsAffineOnFiniteDimensional P.constraintSet (P.inequalityConstraint i) := by
    by_contra hNotAffine
    exact hi (by simpa [BookOrdinaryConvexProgram.nonaffineInequalityIndices] using hNotAffine)
  simpa [IsAffineOnFiniteDimensional] using hAffine

/-- Helper for Theorem 6.28.3: choose a global affine representative for each affine inequality
index outside `P.nonaffineInequalityIndices`. -/
noncomputable def helperForTheorem_6_28_3_affineInequalityRepresentative
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}) :
    (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
  Classical.choose
    (helperForTheorem_6_28_3_exists_affineRepresentative_of_affineInequalityIndex P i.2)

/-- Helper for Theorem 6.28.3: the chosen affine inequality representative agrees with the
original inequality constraint on `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}) :
    Set.EqOn (P.inequalityConstraint i.1)
      (helperForTheorem_6_28_3_affineInequalityRepresentative P i) P.constraintSet := by
  -- The chosen representative was defined precisely from the affine witness above.
  exact Classical.choose_spec
    (helperForTheorem_6_28_3_exists_affineRepresentative_of_affineInequalityIndex P i.2)

/-- Helper for Theorem 6.28.3: choose a global affine representative for each equality
constraint. -/
noncomputable def helperForTheorem_6_28_3_equalityConstraintRepresentative
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (j : Fin (m - r)) :
    (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
  Classical.choose (P.equalityConstraint_affineOn j)

/-- Helper for Theorem 6.28.3: the chosen equality representative agrees with the original
equality constraint on `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (j : Fin (m - r)) :
    Set.EqOn (P.equalityConstraint j)
      (helperForTheorem_6_28_3_equalityConstraintRepresentative P j) P.constraintSet := by
  -- This is the defining property of the chosen affine equality representative.
  exact Classical.choose_spec (P.equalityConstraint_affineOn j)

/-- Helper for Theorem 6.28.3: the strict-feasible witness can be rewritten using the chosen
global affine representatives for the affine inequality block and the equality block. -/
lemma helperForTheorem_6_28_3_exists_point_strict_on_nonaffine_and_weak_on_chosenAffineBlocks
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ x : Fin n → ℝ,
      x ∈ P.constraintSet ∧
        (∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0) ∧
          (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
              (∀ j : Fin (m - r),
                helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
  rcases
      helperForTheorem_6_28_3_exists_point_strict_on_nonaffine_and_weak_on_affine_blocks
        P hstrict_feasible with
    ⟨x, hxC, hstrict, hweak, heq⟩
  refine ⟨x, hxC, hstrict, ?_, ?_⟩
  · intro i
    -- On `P.constraintSet`, the chosen affine representative equals the original affine
    -- inequality, so the weak feasible inequality transfers unchanged.
    have hEq :
        P.inequalityConstraint i.1 x =
          helperForTheorem_6_28_3_affineInequalityRepresentative P i x :=
      helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn P i hxC
    simpa [hEq] using hweak i.1
  · intro j
    -- The equality representative also agrees with the original equality constraint on `C`.
    have hEq :
        P.equalityConstraint j x =
          helperForTheorem_6_28_3_equalityConstraintRepresentative P j x :=
      helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn P j hxC
    simpa [hEq] using heq j

/-- Helper for Theorem 6.28.3: once the optimal value is the finite real `v`, there is no point
in the ambient constraint set with objective value below `v` that also satisfies the full
constraint block. -/
lemma helperForTheorem_6_28_3_not_exists_point_below_optimalValue_with_fullConstraintBlock
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hoptimal : P.optimalValue = (v : EReal)) :
    ¬ ∃ x : Fin n → ℝ,
      x ∈ P.constraintSet ∧
        P.objective x < v ∧
          (∀ i : Fin r, P.inequalityConstraint i x ≤ 0) ∧
            (∀ j : Fin (m - r), P.equalityConstraint j x = 0) := by
  intro hbad
  rcases hbad with ⟨x, hxC, hxObj, hineq, heq⟩
  -- The ambient-set point with the full weak/equality block is simply a feasible point of `P`.
  have hxFeasible : x ∈ P.feasibleSet := ⟨hxC, hineq, heq⟩
  exact
    (helperForTheorem_6_28_3_not_exists_feasiblePoint_with_objective_lt_optimalValue P hoptimal)
      ⟨x, hxFeasible, hxObj⟩

/-- Helper for Theorem 6.28.3: after splitting the inequality block into strict nonaffine and
weak affine pieces, the objective-gap system still has no primal witness below the optimal
value. -/
lemma helperForTheorem_6_28_3_not_exists_point_below_optimalValue_with_chosenAffineBlocks
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hoptimal : P.optimalValue = (v : EReal)) :
    ¬ ∃ x : Fin n → ℝ,
      x ∈ P.constraintSet ∧
        P.objective x < v ∧
          (∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0) ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
                (∀ j : Fin (m - r),
                  helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
  intro hbad
  rcases hbad with ⟨x, hxC, hxObj, hstrict, hAffine, hEq⟩
  have hineq : ∀ i : Fin r, P.inequalityConstraint i x ≤ 0 := by
    intro i
    by_cases hi : i ∈ P.nonaffineInequalityIndices
    · -- On the nonaffine block, the assumed strict inequality is stronger than feasibility.
      exact le_of_lt (hstrict i hi)
    · -- Outside that block, the chosen affine representative agrees with the original inequality.
      let iAffine : {i : Fin r // i ∉ P.nonaffineInequalityIndices} := ⟨i, hi⟩
      have hEqAffine :
          P.inequalityConstraint i x =
            helperForTheorem_6_28_3_affineInequalityRepresentative P iAffine x :=
        helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn P iAffine hxC
      simpa [iAffine, hEqAffine] using hAffine iAffine
  have hEqOriginal : ∀ j : Fin (m - r), P.equalityConstraint j x = 0 := by
    intro j
    -- Equality representatives transfer the zero equalities back to the original program data.
    have hEqRep :
        P.equalityConstraint j x =
          helperForTheorem_6_28_3_equalityConstraintRepresentative P j x :=
      helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn P j hxC
    simpa [hEqRep] using hEq j
  exact
    (helperForTheorem_6_28_3_not_exists_point_below_optimalValue_with_fullConstraintBlock
      P hoptimal) ⟨x, hxC, hxObj, hineq, hEqOriginal⟩

/-- Helper for Theorem 6.28.3: finite perturbation value at the origin already identifies the
ordinary program optimal value with a real number. -/
lemma helperForTheorem_6_28_3_exists_real_optimalValue_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ v : ℝ, P.optimalValue = (v : EReal) := by
  rcases
      helperForTheorem_6_28_3_exists_real_perturbationFunction_zero
        P hoptimal_ne_bot hstrict_feasible with
    ⟨v, hv⟩
  -- Rewrite the finite perturbation value `p(0)` back as the original optimal value.
  refine ⟨v, ?_⟩
  calc
    P.optimalValue = P.perturbationFunction 0 := by
      symm
      exact helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P
    _ = (v : EReal) := hv

/-- Helper for Theorem 6.28.3: a point of the Euclidean relative interior of a subset of `ℝ^n`
already lies in that subset. -/
lemma helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ euclideanRelativeInterior_fin n C) :
    x ∈ C := by
  let e := euclideanEquiv n
  -- Move to the ambient Euclidean coordinates where the standard relative-interior lemma is
  -- already available.
  have hx' : e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) := by
    exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hx
  have hxImg : e.symm x ∈ e.symm '' C :=
    (euclideanRelativeInterior_subset_closure n (e.symm '' C)).1 hx'
  rcases hxImg with ⟨y, hyC, hyEq⟩
  -- Apply the coordinate equivalence back to identify the image witness with `x`.
  have hyEq' : y = x := by
    apply_fun e at hyEq
    simpa using hyEq
  simpa [hyEq'] using hyC

/-- Helper for Theorem 6.28.3: the Chapter 21 route uses the standard indicator extension of a
real-valued branch on the ambient set `C`. -/
noncomputable def helperForTheorem_6_28_3_indicatorExtension
    {n : ℕ} (C : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → EReal := by
  classical
  exact fun x => if x ∈ C then g x else ⊤

/-- Helper for Theorem 6.28.3: a convex real-valued branch on a nonempty ambient convex set
becomes a proper convex function after indicator extension to all of `ℝ^n`. -/
lemma helperForTheorem_6_28_3_proper_indicatorExtension_of_convexOn
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC_nonempty : C.Nonempty)
    {g : (Fin n → ℝ) → ℝ} (hg : ConvexOn ℝ C g) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_6_28_3_indicatorExtension C g) := by
  classical
  have hext_eq :
      helperForTheorem_6_28_3_indicatorExtension C g =
        fun x => if x ∈ C then (g x : EReal) else ⊤ := by
    funext x
    simp [helperForTheorem_6_28_3_indicatorExtension]
  have hext_conv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_6_28_3_indicatorExtension C g) := by
    -- Convexity is exactly the standard `if-top` extension of a convex-on branch.
    rw [hext_eq]
    simpa using (convexFunctionOn_univ_if_top (C := C) (g := g) hg)
  refine ⟨hext_conv, ?_, ?_⟩
  · rcases hC_nonempty with ⟨x0, hx0C⟩
    -- A point of `C` provides a finite epigraph witness for the extended function.
    refine ⟨(x0, g x0), ?_⟩
    refine
      (mem_epigraph_univ_iff
        (f := helperForTheorem_6_28_3_indicatorExtension C g)).2 ?_
    rw [hext_eq]
    simp [hx0C]
  · intro x _hx
    rw [hext_eq]
    -- The indicator extension takes finite real values on `C` and `⊤` off `C`, never `⊥`.
    by_cases hxC : x ∈ C
    · simp [hxC]
    · simp [hxC]

/-- Helper for Theorem 6.28.3: the shifted objective branch used in the Chapter 21 reduction. -/
noncomputable def helperForTheorem_6_28_3_objectiveGapIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ) :
    (Fin n → ℝ) → EReal :=
  helperForTheorem_6_28_3_indicatorExtension P.constraintSet (fun x => P.objective x - v)

/-- Helper for Theorem 6.28.3: the shifted objective branch already gives a proper convex
function on all of `ℝ^n`. -/
lemma helperForTheorem_6_28_3_proper_objectiveGapIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ)
    (hconstraint_nonempty : P.constraintSet.Nonempty) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v) := by
  have hobjective_gap_convexOn :
      ConvexOn ℝ P.constraintSet (fun x => P.objective x - v) := by
    -- Subtracting a fixed constant is the same as adding the constant `-v`.
    simpa [sub_eq_add_neg] using P.objective_convexOn.add_const (-v)
  -- Subtracting the fixed scalar `v` preserves convexity of the objective branch on `C`.
  simpa [helperForTheorem_6_28_3_objectiveGapIndicatorExtension] using
    (helperForTheorem_6_28_3_proper_indicatorExtension_of_convexOn
      (C := P.constraintSet) hconstraint_nonempty hobjective_gap_convexOn)

/-- Helper for Theorem 6.28.3: each inequality constraint has the corresponding proper convex
indicator extension needed for the selected-subfamily Chapter 21 route. -/
noncomputable def helperForTheorem_6_28_3_inequalityIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (i : Fin r) :
    (Fin n → ℝ) → EReal :=
  helperForTheorem_6_28_3_indicatorExtension P.constraintSet (P.inequalityConstraint i)

/-- Helper for Theorem 6.28.3: every inequality indicator extension is a proper convex function
on `ℝ^n`. -/
lemma helperForTheorem_6_28_3_proper_inequalityIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (i : Fin r)
    (hconstraint_nonempty : P.constraintSet.Nonempty) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_6_28_3_inequalityIndicatorExtension P i) := by
  -- This is the same indicator-extension argument applied to the `i`th convex inequality branch.
  simpa [helperForTheorem_6_28_3_inequalityIndicatorExtension] using
    (helperForTheorem_6_28_3_proper_indicatorExtension_of_convexOn
      (C := P.constraintSet) hconstraint_nonempty (P.inequalityConstraint_convexOn i))

/-- Helper for Theorem 6.28.3: on the ambient constraint set, strict negativity of the shifted
objective indicator extension is exactly the assertion that the objective lies below the finite
value `v`. -/
lemma helperForTheorem_6_28_3_objectiveGapIndicatorExtension_lt_zero_iff_of_mem_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ P.constraintSet) :
    helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v x < (0 : EReal) ↔
      P.objective x < v := by
  constructor
  · intro hlt
    -- On `P.constraintSet`, the indicator extension is just the shifted real objective branch.
    have hlt' : (((P.objective x - v : ℝ) : EReal) < (0 : EReal)) := by
      simpa [helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hx] using hlt
    have hreal : P.objective x - v < 0 := by
      exact_mod_cast hlt'
    linarith
  · intro hlt
    -- Repackage the strict real inequality back into the indicator-extension formulation.
    have hreal : P.objective x - v < 0 := by
      linarith
    have hlt' : (((P.objective x - v : ℝ) : EReal) < (0 : EReal)) := by
      exact_mod_cast hreal
    simpa [helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hx] using hlt'

/-- Helper for Theorem 6.28.3: on the ambient constraint set, strict negativity of an
inequality indicator extension is exactly strict negativity of the original inequality
constraint. -/
lemma helperForTheorem_6_28_3_inequalityIndicatorExtension_lt_zero_iff_of_mem_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (i : Fin r) {x : Fin n → ℝ}
    (hx : x ∈ P.constraintSet) :
    helperForTheorem_6_28_3_inequalityIndicatorExtension P i x < (0 : EReal) ↔
      P.inequalityConstraint i x < 0 := by
  constructor
  · intro hlt
    -- On `P.constraintSet`, the inequality indicator extension coincides with the real branch.
    have hlt' : (((P.inequalityConstraint i x : ℝ) : EReal) < (0 : EReal)) := by
      simpa [helperForTheorem_6_28_3_inequalityIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hx] using hlt
    exact_mod_cast hlt'
  · intro hlt
    -- Convert the strict real inequality back to the extended-real indicator formulation.
    have hlt' : (((P.inequalityConstraint i x : ℝ) : EReal) < (0 : EReal)) := by
      exact_mod_cast hlt
    simpa [helperForTheorem_6_28_3_inequalityIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hx] using hlt'

/-- Helper for Theorem 6.28.3: the already-proved optimal-value contradiction rules out the
selected Chapter 21 primal witness once the strict branches are written as indicator
extensions on `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_not_exists_indicatorExtensionWitness_below_zero_with_chosenAffineBlocks
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hoptimal : P.optimalValue = (v : EReal)) :
    ¬ ∃ x : Fin n → ℝ,
      x ∈ P.constraintSet ∧
        helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v x < (0 : EReal) ∧
          (∀ i ∈ P.nonaffineInequalityIndices,
            helperForTheorem_6_28_3_inequalityIndicatorExtension P i x < (0 : EReal)) ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
              (∀ j : Fin (m - r),
                helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
  intro hbad
  rcases hbad with ⟨x, hxC, hobjGap, hstrict, hAffine, hEq⟩
  have hobj : P.objective x < v :=
    (helperForTheorem_6_28_3_objectiveGapIndicatorExtension_lt_zero_iff_of_mem_constraintSet
      P (v := v) (x := x) hxC).1 hobjGap
  have hstrict' :
      ∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0 := by
    intro i hi
    -- Each strict inequality indicator is equivalent to the original strict inequality on `C`.
    exact
      (helperForTheorem_6_28_3_inequalityIndicatorExtension_lt_zero_iff_of_mem_constraintSet
        P i (x := x) hxC).1 (hstrict i hi)
  -- The contradiction is exactly the previously isolated no-primal-gap statement.
  exact
    (helperForTheorem_6_28_3_not_exists_point_below_optimalValue_with_chosenAffineBlocks
      P hoptimal) ⟨x, hxC, hobj, hstrict', hAffine, hEq⟩

/-- Helper for Theorem 6.28.3: once the optimal value is the finite real `v`, the local mixed
strict/affine contradiction package on `P.constraintSet` is already available from the
nonaffine strict-feasibility hypothesis. -/
lemma helperForTheorem_6_28_3_selectedAffineContradictionPackage_of_realOptimalValue_and_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    (hoptimal : P.optimalValue = (v : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    P.constraintSet.Nonempty ∧
      (∃ x : Fin n → ℝ,
        x ∈ P.constraintSet ∧
          (∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0) ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
                (∀ j : Fin (m - r),
                  helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) ∧
      (¬ ∃ x : Fin n → ℝ,
        x ∈ P.constraintSet ∧
          helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v x < (0 : EReal) ∧
            (∀ i ∈ P.nonaffineInequalityIndices,
              helperForTheorem_6_28_3_inequalityIndicatorExtension P i x < (0 : EReal)) ∧
              (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
                helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
                  (∀ j : Fin (m - r),
                    helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) := by
  rcases
      helperForTheorem_6_28_3_exists_point_strict_on_nonaffine_and_weak_on_chosenAffineBlocks
        P hstrict_feasible with
    ⟨x, hxC, hstrict, hAffine, hEq⟩
  have hno_indicator_witness :
      ¬ ∃ x : Fin n → ℝ,
        x ∈ P.constraintSet ∧
          helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v x < (0 : EReal) ∧
            (∀ i ∈ P.nonaffineInequalityIndices,
              helperForTheorem_6_28_3_inequalityIndicatorExtension P i x < (0 : EReal)) ∧
              (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
                helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
                  (∀ j : Fin (m - r),
                    helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
    -- Reuse the already-isolated indicator-extension contradiction at the chosen finite value.
    exact
      helperForTheorem_6_28_3_not_exists_indicatorExtensionWitness_below_zero_with_chosenAffineBlocks
        P hoptimal
  refine ⟨?_, ?_, hno_indicator_witness⟩
  · -- The strict-feasible witness already certifies that the ambient constraint set is nonempty.
    exact ⟨x, hxC⟩
  · -- Record the same witness in the split strict/affine format expected downstream.
    exact ⟨x, hxC, hstrict, hAffine, hEq⟩
end Section28
end Chap06
