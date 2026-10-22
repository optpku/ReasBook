/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part4

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.3: once the ambient constraint set is nonempty, the objective-gap
indicator extension and every inequality indicator extension are proper convex functions on
`ℝ^n`. -/
lemma helperForTheorem_6_28_3_indicatorExtensionBranches_proper_of_nonemptyConstraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ)
    (hconstraint_nonempty : P.constraintSet.Nonempty) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v) ∧
      (∀ i : Fin r,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_6_28_3_inequalityIndicatorExtension P i)) := by
  constructor
  · -- The shifted objective branch is proper convex once `P.constraintSet` has a point.
    exact helperForTheorem_6_28_3_proper_objectiveGapIndicatorExtension P v hconstraint_nonempty
  · intro i
    -- The same indicator-extension argument applies to each convex inequality branch.
    exact helperForTheorem_6_28_3_proper_inequalityIndicatorExtension P i hconstraint_nonempty

/-- Helper for Theorem 6.28.3: the affine weak inequalities and equality block define the
selected ambient set obtained by absorbing the weak part of the mixed system into the objective
domain. -/
noncomputable def helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    x ∈ P.constraintSet ∧
      (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
        helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
        (∀ j : Fin (m - r),
          helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)}

/-- Helper for Theorem 6.28.3: the selected affine/equality feasible set is convex because it is
the intersection of `P.constraintSet` with affine half-spaces and affine zero sets. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_convex
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    Convex ℝ (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) := by
  intro x hx y hy α β hα hβ hαβ
  refine ⟨?_, ?_, ?_⟩
  · -- The ambient constraint set is already convex in the program data.
    exact P.convex_constraintSet hx.1 hy.1 hα hβ hαβ
  · intro i
    -- Affine representatives preserve convex combinations, so weak inequalities remain weak.
    have hcombo :
        helperForTheorem_6_28_3_affineInequalityRepresentative P i (α • x + β • y) =
          α * helperForTheorem_6_28_3_affineInequalityRepresentative P i x +
            β * helperForTheorem_6_28_3_affineInequalityRepresentative P i y := by
      simpa [smul_eq_mul] using
        (Convex.combo_affine_apply
          (x := x) (y := y) (a := α) (b := β)
          (f := helperForTheorem_6_28_3_affineInequalityRepresentative P i) hαβ)
    rw [hcombo]
    nlinarith [hx.2.1 i, hy.2.1 i]
  · intro j
    -- The affine equality representatives still vanish on convex combinations.
    have hcombo :
        helperForTheorem_6_28_3_equalityConstraintRepresentative P j (α • x + β • y) =
          α * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x +
            β * helperForTheorem_6_28_3_equalityConstraintRepresentative P j y := by
      simpa [smul_eq_mul] using
        (Convex.combo_affine_apply
          (x := x) (y := y) (a := α) (b := β)
          (f := helperForTheorem_6_28_3_equalityConstraintRepresentative P j) hαβ)
    rw [hcombo, hx.2.2 j, hy.2.2 j]
    ring

/-- Helper for Theorem 6.28.3: the strict-feasible witness already lies in the selected
affine/equality feasible set obtained by absorbing the weak block into the objective. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_nonempty_of_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P).Nonempty := by
  rcases
      helperForTheorem_6_28_3_exists_point_strict_on_nonaffine_and_weak_on_chosenAffineBlocks
        P hstrict_feasible with
    ⟨x, hxC, _hstrict, hAffine, hEq⟩
  -- Reuse the same witness after dropping the strict nonaffine inequalities from the data.
  exact ⟨x, hxC, hAffine, hEq⟩

/-- Helper for Theorem 6.28.3: the absorbed affine/equality feasible slice has a relative-
interior point of its own because it is convex and nonempty under the nonaffine strict-
feasibility hypothesis. -/
lemma helperForTheorem_6_28_3_exists_selectedAffineWeakRiPoint_of_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ x : Fin n → ℝ,
      x ∈ euclideanRelativeInterior_fin n
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) ∧
        x ∈ P.constraintSet ∧
          (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
            (∀ j : Fin (m - r),
              helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
  rcases
      helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P)
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_convex P)
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_nonempty_of_nonaffineStrictFeasibility
          P hstrict_feasible) with
    ⟨x, hxri⟩
  have hxSelected :
      x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P :=
    helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hxri
  -- Unpack the selected-slice relative-interior witness into the ambient-set data used later.
  exact ⟨x, hxri, hxSelected.1, hxSelected.2.1, hxSelected.2.2⟩

/-- Helper for Theorem 6.28.3: absorb the weak affine/equality block into the objective by adding
its indicator to the shifted objective branch. -/
noncomputable def helperForTheorem_6_28_3_selectedStrictObjective
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v x +
      indicatorFunction (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) x

/-- Helper for Theorem 6.28.3: the reduced strict-only objective obtained by absorbing the affine
weak/equality block still has a selected feasible witness where its value is finite. -/
lemma helperForTheorem_6_28_3_exists_selectedAffineWeakWitness_with_selectedStrictObjective_lt_top
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P ∧
        helperForTheorem_6_28_3_selectedStrictObjective P v x0 < (⊤ : EReal) := by
  rcases
      helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_nonempty_of_nonaffineStrictFeasibility
        P hstrict_feasible with
    ⟨x0, hx0⟩
  have hx0C : x0 ∈ P.constraintSet := hx0.1
  have hindicator_zero :
      indicatorFunction (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) x0 = 0 := by
    -- The absorbed-block indicator vanishes on the chosen selected-feasible witness.
    simpa [indicatorFunction] using hx0
  have hobjective_gap_top :
      (((P.objective x0 - v : ℝ)) : EReal) < (⊤ : EReal) := by
    -- The shifted objective branch is finite at every point of `P.constraintSet`.
    have hobjective_ne_top : (((P.objective x0 : ℝ)) : EReal) ≠ (⊤ : EReal) := by
      simp
    have hneg_ne_top : (((-v : ℝ)) : EReal) ≠ (⊤ : EReal) := by
      simp
    have hsum_lt_top :
        (((P.objective x0 : ℝ)) : EReal) + (((-v : ℝ)) : EReal) < (⊤ : EReal) :=
      EReal.add_lt_top hobjective_ne_top hneg_ne_top
    simpa [sub_eq_add_neg, EReal.coe_neg] using hsum_lt_top
  have hx0_top :
      helperForTheorem_6_28_3_selectedStrictObjective P v x0 < (⊤ : EReal) := by
    -- At the same witness, the reduced strict-only objective is the finite shifted objective plus
    -- the vanishing selected-set indicator.
    simpa [helperForTheorem_6_28_3_selectedStrictObjective,
      helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hx0C, hindicator_zero] using
      hobjective_gap_top
  exact ⟨x0, hx0, hx0_top⟩

/-- Helper for Theorem 6.28.3: after absorbing the affine weak/equality block into an indicator,
the reduced strict-only objective is still proper convex on `ℝ^n`. -/
lemma helperForTheorem_6_28_3_proper_selectedStrictObjective_of_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v : ℝ)
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_6_28_3_selectedStrictObjective P v) := by
  classical
  rcases
      helperForTheorem_6_28_3_exists_selectedAffineWeakWitness_with_selectedStrictObjective_lt_top
        P v hstrict_feasible with
    ⟨x0, hx0, hx0_top⟩
  have hobjective_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v) := by
    -- The selected witness still lies in `P.constraintSet`, so the shifted objective branch is
    -- proper on the ambient space.
    exact helperForTheorem_6_28_3_proper_objectiveGapIndicatorExtension P v ⟨x0, hx0.1⟩
  have hindicator_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P)) := by
    -- The indicator is proper convex because the absorbed affine/equality feasible set is convex
    -- and nonempty.
    exact
      properConvexFunctionOn_indicator_of_convex_of_nonempty
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_convex P)
        ⟨x0, hx0⟩
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i =>
      Fin.cases
        (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v)
        (fun _ => indicatorFunction (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P)) i
  have hproperTwo :
      ∀ i : Fin 2,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hobjective_proper
    · simpa [fTwo] using hindicator_proper
  have hsum_top :
      (∑ i : Fin 2, fTwo i x0) < (⊤ : EReal) := by
    simpa [helperForTheorem_6_28_3_selectedStrictObjective, fTwo, Fin.sum_univ_two] using hx0_top
  -- The reduced strict-only objective is the two-term sum of the shifted objective branch and the
  -- absorbed affine/equality indicator, with a common finite witness `x0`.
  simpa [helperForTheorem_6_28_3_selectedStrictObjective, fTwo, Fin.sum_univ_two] using
    (properConvexFunctionOn_sum_of_exists_ne_top
      (f := fTwo) hproperTwo ⟨x0, (lt_top_iff_ne_top.mp hsum_top)⟩)

/-- Helper for Theorem 6.28.3: any positive scalar multiple of the desired supporting
inequality on `P.constraintSet` can already be repackaged as the multiplier lower-bound
certificate used downstream. -/
lemma helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_positiveScaledKuhnTuckerSupport
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    (hoptimal : P.optimalValue = (v : EReal))
    (ht_pos : 0 < t)
    (alpha : Fin r → ℝ) (eta : Fin (m - r) → ℝ)
    (halpha_nonneg : ∀ i : Fin r, 0 ≤ alpha i)
    (hglobal :
      ∀ x : Fin n → ℝ, x ∈ P.constraintSet →
        0 ≤ t * (P.objective x - v) +
          (∑ i : Fin r, alpha i * P.inequalityConstraint i x) +
            ∑ j : Fin (m - r), eta j * P.equalityConstraint j x) :
    ∃ lambda : Fin m → ℝ,
      P.optimalValue = (v : EReal) ∧
        (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
          (∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) := by
  let lambda : Fin m → ℝ :=
    (Fin.append (fun i : Fin r => alpha i / t) (fun j : Fin (m - r) => eta j / t)) ∘
      Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount).symm
  have hineqCoeff :
      ∀ i : Fin r, P.inequalityMultipliers lambda i = alpha i / t := by
    intro i
    -- The first `r` coordinates of `lambda` are exactly the normalized inequality coefficients.
    simp [BookOrdinaryConvexProgram.inequalityMultipliers, lambda]
  have heqCoeff :
      ∀ j : Fin (m - r), P.equalityMultipliers lambda j = eta j / t := by
    intro j
    -- The remaining coordinates of `lambda` are exactly the normalized equality coefficients.
    simp [BookOrdinaryConvexProgram.equalityMultipliers, lambda]
  have hlambda_nonneg :
      ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i := by
    intro i
    -- Positivity of the scaling factor preserves nonnegativity of the inequality block.
    rw [hineqCoeff]
    exact div_nonneg (halpha_nonneg i) (le_of_lt ht_pos)
  refine ⟨lambda, hoptimal, hlambda_nonneg, ?_⟩
  intro x hx
  have hineq_scaled :
      t * (∑ i : Fin r, (alpha i / t) * P.inequalityConstraint i x) =
        ∑ i : Fin r, alpha i * P.inequalityConstraint i x := by
    -- Clearing the positive denominator recovers the original inequality-coefficient sum.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    field_simp [ht_ne]
  have heq_scaled :
      t * (∑ j : Fin (m - r), (eta j / t) * P.equalityConstraint j x) =
        ∑ j : Fin (m - r), eta j * P.equalityConstraint j x := by
    -- The same denominator-clearing step works for the equality block.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    field_simp [ht_ne]
  have hscaled :
      0 ≤ t * (P.kuhnTuckerObjective lambda x - v) := by
    -- Rewrite the scaled Kuhn--Tucker gap into the supplied supporting inequality.
    calc
      0 ≤ t * (P.objective x - v) +
            (∑ i : Fin r, alpha i * P.inequalityConstraint i x) +
              ∑ j : Fin (m - r), eta j * P.equalityConstraint j x :=
        hglobal x hx
      _ = t * (P.kuhnTuckerObjective lambda x - v) := by
        calc
          t * (P.objective x - v) +
              (∑ i : Fin r, alpha i * P.inequalityConstraint i x) +
                ∑ j : Fin (m - r), eta j * P.equalityConstraint j x
            = t * (P.objective x - v) +
                t * (∑ i : Fin r,
                  P.inequalityMultipliers lambda i * P.inequalityConstraint i x) +
                  t * (∑ j : Fin (m - r),
                    P.equalityMultipliers lambda j * P.equalityConstraint j x) := by
                  simp [hineqCoeff, heqCoeff]
                  rw [hineq_scaled, heq_scaled]
          _ = t * (P.kuhnTuckerObjective lambda x - v) := by
                unfold BookOrdinaryConvexProgram.kuhnTuckerObjective
                ring
  have hgap_nonneg : 0 ≤ P.kuhnTuckerObjective lambda x - v :=
    (mul_nonneg_iff_of_pos_left ht_pos).1 hscaled
  -- A nonnegative Kuhn--Tucker gap is exactly the claimed lower bound by `v`.
  linarith

/-- Helper for Theorem 6.28.3: after absorbing the affine weak/equality block into
`helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P`, Theorem 21.1 already yields a
positive-scaled support inequality on that selected set. -/
lemma helperForTheorem_6_28_3_exists_positiveScaledSupport_on_selectedAffineWeakFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (hoptimal : P.optimalValue = (v : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ t : ℝ,
      ∃ alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ,
        0 < t ∧
          (∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i) ∧
            (∀ x : Fin n → ℝ,
              x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
                0 ≤ t * (P.objective x - v) +
                  ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                    alpha i * P.inequalityConstraint i.1 x) := by
  classical
  rcases
      helperForTheorem_6_28_3_selectedAffineContradictionPackage_of_realOptimalValue_and_nonaffineStrictFeasibility
        P hoptimal hstrict_feasible with
    ⟨hconstraint_nonempty, hchosen_blocks, hno_indicator_witness⟩
  let C := helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P
  let I : Type := {i : Fin r // i ∈ P.nonaffineInequalityIndices}
  let J : Type := Option I
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let fStrict : Fin (Fintype.card J) → (Fin n → ℝ) → EReal :=
    fun k =>
      match eJ.symm k with
      | none => helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v
      | some i => helperForTheorem_6_28_3_inequalityIndicatorExtension P i.1
  have hC_convex : Convex ℝ C := by
    -- The absorbed affine/equality block is convex by construction.
    simpa [C] using helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_convex P
  have hC_nonempty : C.Nonempty := by
    -- The original strict-feasible point already belongs to the absorbed selected set.
    simpa [C] using
      helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_nonempty_of_nonaffineStrictFeasibility
        P hstrict_feasible
  have hfStrict :
      ∀ k : Fin (Fintype.card J),
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict k) := by
    intro k
    cases hk : eJ.symm k with
    | none =>
        -- The objective-gap indicator branch is proper convex on the ambient space.
        simpa [fStrict, hk] using
          helperForTheorem_6_28_3_proper_objectiveGapIndicatorExtension P v
            hconstraint_nonempty
    | some i =>
        -- Every nonaffine inequality branch has the same proper-convex indicator extension.
        simpa [fStrict, hk] using
          helperForTheorem_6_28_3_proper_inequalityIndicatorExtension P i.1
            hconstraint_nonempty
  have hdomStrict :
      ∀ k : Fin (Fintype.card J),
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict k) := by
    intro k x hxri
    have hxC_selected : x ∈ C :=
      helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hxri
    have hxSelected :
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
      simpa [C] using hxC_selected
    rcases hxSelected with ⟨hxConstraint, _, _⟩
    cases hk : eJ.symm k with
    | none =>
        -- On the selected set, the objective-gap indicator branch is finite because points stay
        -- inside `P.constraintSet`.
        have hdom_obj :
            x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v) := by
          change
            ∃ μ,
              (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
                (helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v)
          refine ⟨P.objective x - v, ?_⟩
          refine
            (mem_epigraph_univ_iff
              (f := helperForTheorem_6_28_3_objectiveGapIndicatorExtension P v)).2 ?_
          simp [helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
            helperForTheorem_6_28_3_indicatorExtension, hxConstraint]
        simpa [fStrict, hk] using hdom_obj
    | some i =>
        -- The same finiteness argument works for each nonaffine inequality branch.
        have hdom_ineq :
            x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_6_28_3_inequalityIndicatorExtension P i.1) := by
          change
            ∃ μ,
              (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
                (helperForTheorem_6_28_3_inequalityIndicatorExtension P i.1)
          refine ⟨P.inequalityConstraint i.1 x, ?_⟩
          refine
            (mem_epigraph_univ_iff
              (f := helperForTheorem_6_28_3_inequalityIndicatorExtension P i.1)).2 ?_
          simp [helperForTheorem_6_28_3_inequalityIndicatorExtension,
            helperForTheorem_6_28_3_indicatorExtension, hxConstraint]
        simpa [fStrict, hk] using hdom_ineq
  have hAlt :=
    theorem21_convex_inequality_alternative
      C hC_convex (Fintype.card_pos_iff.mpr ⟨none⟩) fStrict hfStrict hdomStrict
  rw [xor_def] at hAlt
  have hnot_primal :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ k : Fin (Fintype.card J), fStrict k x < (0 : EReal) := by
    intro hprimal
    rcases hprimal with ⟨x, hxC, hxstrict⟩
    have hxSelected :
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
      simpa [C] using hxC
    rcases hxSelected with ⟨hxConstraint, hAffine, hEq⟩
    refine hno_indicator_witness ?_
    refine ⟨x, hxConstraint, ?_, ?_, hAffine, hEq⟩
    · -- The `none` branch of the strict family is exactly the objective-gap inequality.
      have hxobjective : fStrict (eJ none) x < (0 : EReal) := hxstrict (eJ none)
      simpa [fStrict, helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hxConstraint] using hxobjective
    · intro i hi
      -- Every `some i` branch is the corresponding nonaffine inequality indicator extension.
      have hxi : fStrict (eJ (some ⟨i, hi⟩)) x < (0 : EReal) := hxstrict (eJ (some ⟨i, hi⟩))
      simpa [fStrict, helperForTheorem_6_28_3_inequalityIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hxConstraint] using hxi
  rcases hchosen_blocks with ⟨x0, hx0Constraint, hstrict0, hAffine0, hEq0⟩
  have hx0C : x0 ∈ C := by
    -- The chosen strict/weak witness belongs to the selected set by definition.
    simpa [C] using
      (show
          x0 ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P from
        ⟨hx0Constraint, hAffine0, hEq0⟩)
  rcases hAlt with hprimal | hdual
  · exact False.elim (hnot_primal hprimal.1)
  · rcases hdual.1 with ⟨l, hl_nonneg, hl_nonzero, hmargin⟩
    let t : ℝ := l (eJ none)
    let alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ :=
      fun i => l (eJ (some i))
    have ht_pos : 0 < t := by
      have ht_nonneg : 0 ≤ t := by
        simpa [t] using hl_nonneg (eJ none)
      by_contra ht_not_pos
      have ht_zero : t = 0 := by linarith
      have hsome_nonzero :
          ∃ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, l (eJ (some i)) ≠ 0 := by
        rcases hl_nonzero with ⟨k, hk_nonzero⟩
        cases hk : eJ.symm k with
        | none =>
            have hk_eq : k = eJ none := by
              apply_fun eJ at hk
              simpa using hk
            have : l k = 0 := by simpa [hk_eq, t, ht_zero]
            exact False.elim (hk_nonzero this)
        | some i =>
            have hk_eq : k = eJ (some i) := by
              apply_fun eJ at hk
              simpa using hk
            exact ⟨i, by simpa [hk_eq] using hk_nonzero⟩
      rcases hsome_nonzero with ⟨i0, hi0_nonzero⟩
      let realTerm : Fin (Fintype.card J) → ℝ :=
        fun k =>
          match eJ.symm k with
          | none => l k * (P.objective x0 - v)
          | some i => l k * P.inequalityConstraint i.1 x0
      have hsum_coe :
          (((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal) =
            ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x0 := by
        calc
          ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal))
              = ∑ k : Fin (Fintype.card J), (((realTerm k : ℝ) : EReal)) := by
                  exact
                    helperForTheorem_21_1_coe_finset_sum_real
                      (s := (Finset.univ : Finset (Fin (Fintype.card J))))
                      (g := realTerm)
          _ = ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x0 := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                cases hk' : eJ.symm k with
                | none =>
                    simp [realTerm, fStrict, hk', t, helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
                      helperForTheorem_6_28_3_indicatorExtension, hx0Constraint, EReal.coe_mul]
                | some i =>
                    simp [realTerm, fStrict, hk',
                      helperForTheorem_6_28_3_inequalityIndicatorExtension,
                      helperForTheorem_6_28_3_indicatorExtension, hx0Constraint, EReal.coe_mul]
      have hsum_nonneg : 0 ≤ ∑ k : Fin (Fintype.card J), realTerm k := by
        have hsum_nonnegE :
            (0 : EReal) ≤ ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal)) := by
          calc
            (0 : EReal) ≤ ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x0 :=
              hmargin x0 hx0C
            _ = ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal)) := by
                  symm
                  exact hsum_coe
        exact_mod_cast hsum_nonnegE
      have hterms_nonpos :
          ∀ k : Fin (Fintype.card J), realTerm k ≤ 0 := by
        intro k
        cases hk : eJ.symm k with
        | none =>
            have hk_eq : k = eJ none := by
              apply_fun eJ at hk
              simpa using hk
            simpa [realTerm, hk_eq, t, ht_zero]
        | some i =>
            have hk_eq : k = eJ (some i) := by
              apply_fun eJ at hk
              simpa using hk
            simpa [realTerm, hk_eq] using
              (mul_nonpos_of_nonneg_of_nonpos (hl_nonneg k) (le_of_lt (hstrict0 i.1 i.2)))
      have hi0_pos : 0 < l (eJ (some i0)) :=
        lt_of_le_of_ne (hl_nonneg (eJ (some i0))) (by simpa [eq_comm] using hi0_nonzero)
      have hterm_neg : realTerm (eJ (some i0)) < 0 := by
        -- The chosen strict-feasible point makes every nonaffine inequality branch negative.
        simpa [realTerm] using
          (mul_neg_of_pos_of_neg hi0_pos (hstrict0 i0.1 i0.2))
      have hrest_nonpos :
          Finset.sum (Finset.univ.erase (eJ (some i0))) realTerm ≤ 0 := by
        refine Finset.sum_nonpos ?_
        intro k hk
        exact hterms_nonpos k
      have hsplit :
          (∑ k : Fin (Fintype.card J), realTerm k) =
            realTerm (eJ (some i0)) +
              Finset.sum (Finset.univ.erase (eJ (some i0))) realTerm := by
        rw [add_comm]
        exact
          (Finset.sum_erase_add
            (s := Finset.univ)
            (a := eJ (some i0))
            (f := realTerm)
            (Finset.mem_univ (eJ (some i0)))).symm
      have hsum_neg : (∑ k : Fin (Fintype.card J), realTerm k) < 0 := by
        rw [hsplit]
        linarith
      exact not_lt_of_ge hsum_nonneg hsum_neg
    have halpha_nonneg :
        ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i := by
      intro i
      -- The nonaffine multipliers are inherited from the nonnegative Theorem 21.1 certificate.
      simpa [alpha] using hl_nonneg (eJ (some i))
    refine ⟨t, alpha, ht_pos, halpha_nonneg, ?_⟩
    intro x hxC
    have hxSelected :
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
      simpa [C] using hxC
    rcases hxSelected with ⟨hxConstraint, _, _⟩
    let realTerm : Fin (Fintype.card J) → ℝ :=
      fun k =>
        match eJ.symm k with
        | none => l k * (P.objective x - v)
        | some i => l k * P.inequalityConstraint i.1 x
    have hsum_coe :
        (((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal) =
          ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x := by
      calc
        ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal))
            = ∑ k : Fin (Fintype.card J), (((realTerm k : ℝ) : EReal)) := by
                exact
                  helperForTheorem_21_1_coe_finset_sum_real
                    (s := (Finset.univ : Finset (Fin (Fintype.card J))))
                    (g := realTerm)
        _ = ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              cases hk' : eJ.symm k with
              | none =>
                  simp [realTerm, fStrict, hk', helperForTheorem_6_28_3_objectiveGapIndicatorExtension,
                    helperForTheorem_6_28_3_indicatorExtension, hxConstraint, EReal.coe_mul]
              | some i =>
                  simp [realTerm, fStrict, hk', helperForTheorem_6_28_3_inequalityIndicatorExtension,
                    helperForTheorem_6_28_3_indicatorExtension, hxConstraint, EReal.coe_mul]
    have hsum_nonneg : 0 ≤ ∑ k : Fin (Fintype.card J), realTerm k := by
      have hsum_nonnegE :
          (0 : EReal) ≤ ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal)) := by
        calc
          (0 : EReal) ≤ ∑ k : Fin (Fintype.card J), ((l k : ℝ) : EReal) * fStrict k x :=
            hmargin x hxC
          _ = ((((∑ k : Fin (Fintype.card J), realTerm k : ℝ) : ℝ) : EReal)) := by
                symm
                exact hsum_coe
      exact_mod_cast hsum_nonnegE
    have hsum_split :
        (∑ k : Fin (Fintype.card J), realTerm k) =
          t * (P.objective x - v) +
            ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              alpha i * P.inequalityConstraint i.1 x := by
      calc
        (∑ k : Fin (Fintype.card J), realTerm k)
            = ∑ j : J,
                match j with
                | none => t * (P.objective x - v)
                | some i => alpha i * P.inequalityConstraint i.1 x := by
                    exact
                      Fintype.sum_equiv eJ.symm
                        realTerm
                        (fun j : J =>
                          match j with
                          | none => t * (P.objective x - v)
                          | some i => alpha i * P.inequalityConstraint i.1 x)
                        (by
                          intro k
                          cases h : eJ.symm k with
                          | none =>
                              have hk_eq : k = eJ none := by
                                apply_fun eJ at h
                                simpa using h
                              simp [realTerm, t, hk_eq]
                          | some i =>
                              have hk_eq : k = eJ (some i) := by
                                apply_fun eJ at h
                                simpa using h
                              simp [realTerm, alpha, hk_eq])
        _ = t * (P.objective x - v) +
              ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                alpha i * P.inequalityConstraint i.1 x := by
              change
                (∑ j : Option I,
                  match j with
                  | none => t * (P.objective x - v)
                  | some i => alpha i * P.inequalityConstraint i.1 x) =
                    t * (P.objective x - v) +
                      ∑ i : I, alpha i * P.inequalityConstraint i.1 x
              exact
                Fintype.sum_option
                  (f := fun j : Option I =>
                    match j with
                    | none => t * (P.objective x - v)
                    | some i => alpha i * P.inequalityConstraint i.1 x)
    -- Rewrite the Theorem 21.1 certificate on the selected set into the real-valued support
    -- inequality used by the later multiplier packaging step.
    rw [hsum_split] at hsum_nonneg
    exact hsum_nonneg

/-- Helper for Theorem 6.28.3: package the strict-branch support expression produced on the
selected affine/equality feasible set as a reusable real-valued function on `P.constraintSet`. -/
noncomputable def helperForTheorem_6_28_3_selectedSupportExpression
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v t : ℝ)
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    t * (P.objective x - v) +
      ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
        alpha i * P.inequalityConstraint i.1 x

/-- Helper for Theorem 6.28.3: the selected-set strict support expression is convex on the
ambient constraint set once the scaling factor and nonaffine coefficients are nonnegative. -/
lemma helperForTheorem_6_28_3_selectedSupportExpression_convexOn_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (ht_nonneg : 0 ≤ t)
    (halpha_nonneg :
      ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i) :
    ConvexOn ℝ P.constraintSet
      (helperForTheorem_6_28_3_selectedSupportExpression P v t alpha) := by
  have hobjective_gap_convexOn :
      ConvexOn ℝ P.constraintSet (fun x => P.objective x - v) := by
    -- Subtracting the fixed scalar `v` preserves convexity of the objective branch on `C`.
    simpa [sub_eq_add_neg] using P.objective_convexOn.add_const (-v)
  have hscaled_objective_gap :
      ConvexOn ℝ P.constraintSet (fun x => t * (P.objective x - v)) := by
    -- A nonnegative scalar multiple of the shifted objective stays convex on `C`.
    simpa [smul_eq_mul] using
      (ConvexOn.smul (c := t) (hc := ht_nonneg) hobjective_gap_convexOn)
  have hineq_term :
      ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
        ConvexOn ℝ P.constraintSet (fun x => alpha i * P.inequalityConstraint i.1 x) := by
    intro i
    -- Each nonaffine inequality branch stays convex after nonnegative scaling.
    simpa [smul_eq_mul] using
      (ConvexOn.smul (c := alpha i) (hc := halpha_nonneg i)
        (P.inequalityConstraint_convexOn i.1))
  have hineq_sum :
      ConvexOn ℝ P.constraintSet
        (fun x =>
          ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            alpha i * P.inequalityConstraint i.1 x) := by
    classical
    have hs :
        ∀ s : Finset {i : Fin r // i ∈ P.nonaffineInequalityIndices},
          ConvexOn ℝ P.constraintSet
            (fun x =>
              Finset.sum s (fun i => alpha i * P.inequalityConstraint i.1 x)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simpa using (convexOn_const (s := P.constraintSet) (c := (0 : ℝ)) P.convex_constraintSet)
      | @insert i s hi hs =>
          simpa [Finset.sum_insert hi] using ConvexOn.add (hineq_term i) hs
    simpa using hs Finset.univ
  -- The selected support expression is exactly the sum of the scaled objective gap and the
  -- nonaffine weighted inequality block.
  change
    ConvexOn ℝ P.constraintSet
      ((fun x => t * (P.objective x - v)) +
        fun x =>
          ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            alpha i * P.inequalityConstraint i.1 x)
  simpa [helperForTheorem_6_28_3_selectedSupportExpression] using
    ConvexOn.add hscaled_objective_gap hineq_sum

/-- Helper for Theorem 6.28.3: indicator-extend the selected-set strict support expression from
`P.constraintSet` to all of `ℝ^n` so the remaining affine/equality extension step can be phrased
as a Chapter 21 mixed strict/affine separation problem. -/
noncomputable def helperForTheorem_6_28_3_selectedSupportIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (v t : ℝ)
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ) :
    (Fin n → ℝ) → EReal :=
  helperForTheorem_6_28_3_indicatorExtension P.constraintSet
    (helperForTheorem_6_28_3_selectedSupportExpression P v t alpha)

/-- Helper for Theorem 6.28.3: the indicator-extended selected support branch is already a
proper convex function on `ℝ^n`, so only the affine/equality-extension argument remains. -/
lemma helperForTheorem_6_28_3_proper_selectedSupportIndicatorExtension
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (hconstraint_nonempty : P.constraintSet.Nonempty)
    (ht_nonneg : 0 ≤ t)
    (halpha_nonneg :
      ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha) := by
  have hconv :
      ConvexOn ℝ P.constraintSet
        (helperForTheorem_6_28_3_selectedSupportExpression P v t alpha) :=
    helperForTheorem_6_28_3_selectedSupportExpression_convexOn_constraintSet
      P alpha ht_nonneg halpha_nonneg
  -- The remaining affine/equality block can now be treated as a separate mixed-alternative
  -- problem over this proper convex strict branch.
  simpa [helperForTheorem_6_28_3_selectedSupportIndicatorExtension] using
    (helperForTheorem_6_28_3_proper_indicatorExtension_of_convexOn
      (C := P.constraintSet) hconstraint_nonempty hconv)

/-- Helper for Theorem 6.28.3: once the absorbed affine weak/equality block has a witness in
`ri P.constraintSet`, the selected-set support inequality extends to a global Kuhn--Tucker
multiplier lower-bound certificate on all of `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_selectedSupportFamily_notPrimal
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (hselected_support :
      ∀ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
          0 ≤ t * (P.objective x - v) +
            ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              alpha i * P.inequalityConstraint i.1 x) :
    ¬ ∃ x : Fin n → ℝ,
        helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha x < (0 : EReal) ∧
          (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
            (∀ j : Fin (m - r),
              helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0) := by
  intro hprimal
  rcases hprimal with ⟨x, hstrict_neg, hAffine, hEq⟩
  have hxC : x ∈ P.constraintSet := by
    -- A negative value of the indicator-extended strict branch can only occur on `P.constraintSet`.
    by_contra hxC
    simpa [helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hxC] using hstrict_neg
  have hxSelected : x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
    -- The affine and equality side conditions say exactly that `x` lies in the selected slice.
    exact ⟨hxC, hAffine, hEq⟩
  have hxSupportNeg :
      helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x < 0 := by
    -- On `P.constraintSet`, the indicator extension agrees with the real-valued support
    -- expression.
    have hxSupportNegE :
        (((helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x : ℝ) : EReal)) <
          (0 : EReal) := by
      simpa [helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hxC] using hstrict_neg
    exact_mod_cast hxSupportNegE
  have hxSupportNonneg :
      0 ≤ helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x := by
    -- The selected-slice support inequality forbids a negative strict-branch value.
    simpa [helperForTheorem_6_28_3_selectedSupportExpression] using hselected_support x hxSelected
  linarith

/-- Helper for Theorem 6.28.3: an ambient witness satisfying the affine weak inequalities and
equality block already belongs to the absorbed selected affine weak feasible set. -/
lemma helperForTheorem_6_28_3_mem_selectedAffineWeakFeasibleSet_of_affineWitness
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {x : Fin n → ℝ}
    (hx :
      x ∈ P.constraintSet ∧
        (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
          helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
          (∀ j : Fin (m - r),
            helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) :
    x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
  -- This helper just repackages the ambient affine witness into the absorbed feasible-slice
  -- predicate used by the selected-support reduction.
  exact hx

/-- Helper for Theorem 6.28.3: any ambient affine/equality witness makes the absorbed selected
affine weak feasible set nonempty. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_nonempty_of_affineWitness
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hselected_affine_feasible :
      ∃ x : Fin n → ℝ,
        x ∈ P.constraintSet ∧
          (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
            (∀ j : Fin (m - r),
              helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) :
    (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P).Nonempty := by
  rcases hselected_affine_feasible with ⟨x, hxC, hAffine, hEq⟩
  -- The same ambient witness is already a point of the absorbed affine/equality slice.
  exact ⟨x,
    helperForTheorem_6_28_3_mem_selectedAffineWeakFeasibleSet_of_affineWitness
      P ⟨hxC, hAffine, hEq⟩⟩

/-- Helper for Theorem 6.28.3: bundle the affine weak inequalities and the two-sided equality
block into one affine family on `ℝ^n`. -/
abbrev helperForTheorem_6_28_3_selectedAffineWeakAuxIndex
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) : Type :=
  Sum {i : Fin r // i ∉ P.nonaffineInequalityIndices}
    (Sum (Fin (m - r)) (Fin (m - r)))

/-- Helper for Theorem 6.28.3: the combined affine family attached to the absorbed selected
slice, with one branch for each affine weak inequality and two branches for each equality. -/
noncomputable def helperForTheorem_6_28_3_selectedAffineWeakAuxFamily
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) :
    helperForTheorem_6_28_3_selectedAffineWeakAuxIndex P → (Fin n → ℝ) → ℝ :=
  fun j x =>
    match j with
    | Sum.inl i => helperForTheorem_6_28_3_affineInequalityRepresentative P i x
    | Sum.inr (Sum.inl q) => helperForTheorem_6_28_3_equalityConstraintRepresentative P q x
    | Sum.inr (Sum.inr q) => -helperForTheorem_6_28_3_equalityConstraintRepresentative P q x

/-- Helper for Theorem 6.28.3: every component of the combined selected-slice affine family is
represented by a global affine map. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_isAffine
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (j : helperForTheorem_6_28_3_selectedAffineWeakAuxIndex P) :
    ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      helperForTheorem_6_28_3_selectedAffineWeakAuxFamily P j = g := by
  -- Each branch of the combined family is one of the already chosen affine representatives.
  cases j with
  | inl i =>
      refine ⟨helperForTheorem_6_28_3_affineInequalityRepresentative P i, ?_⟩
      ext x
      simp [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily]
  | inr s =>
      cases s with
      | inl q =>
          refine ⟨helperForTheorem_6_28_3_equalityConstraintRepresentative P q, ?_⟩
          ext x
          simp [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily]
      | inr q =>
          refine ⟨-helperForTheorem_6_28_3_equalityConstraintRepresentative P q, ?_⟩
          ext x
          simp [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily]

/-- Helper for Theorem 6.28.3: membership in the absorbed selected slice is exactly the statement
that every component of the combined affine family is nonpositive there. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_nonpos_of_mem_selectedAffineWeakFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {x : Fin n → ℝ}
    (hx : x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) :
    ∀ j : helperForTheorem_6_28_3_selectedAffineWeakAuxIndex P,
      helperForTheorem_6_28_3_selectedAffineWeakAuxFamily P j x ≤ 0 := by
  rcases hx with ⟨_hxC, hAffine, hEq⟩
  intro j
  -- Unpack the branch index and read off the corresponding stored inequality or equality.
  cases j with
  | inl i =>
      simpa [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily] using hAffine i
  | inr s =>
      cases s with
      | inl q =>
          simpa [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily, hEq q]
      | inr q =>
          simp [helperForTheorem_6_28_3_selectedAffineWeakAuxFamily, hEq q]

/-- Helper for Theorem 6.28.3: the selected-slice relative-interior witness already supplies the
full affine-feasible data for the combined affine family on the absorbed selected set. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_feasRi_of_selectedAffineWeakRiPoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hri_selected :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
          (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) ∧
          x ∈ P.constraintSet ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
              (∀ j : Fin (m - r),
                helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) :
    ∃ x : Fin n → ℝ,
      x ∈ euclideanRelativeInterior_fin n
        (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) ∧
        ∀ j : helperForTheorem_6_28_3_selectedAffineWeakAuxIndex P,
          helperForTheorem_6_28_3_selectedAffineWeakAuxFamily P j x ≤ 0 := by
  rcases hri_selected with ⟨x, hxri, hxC, hAffine, hEq⟩
  have hxSelected : x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
    -- Repackage the stored ambient witness as a point of the absorbed selected slice.
    exact ⟨hxC, hAffine, hEq⟩
  refine ⟨x, hxri, ?_⟩
  -- The selected-slice witness satisfies every branch of the combined affine family.
  exact
    helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_nonpos_of_mem_selectedAffineWeakFeasibleSet
      P hxSelected

/-- Helper for Theorem 6.28.3: the selected-set support inequality already excludes any point of
the absorbed selected slice where the selected strict branch is negative. -/
lemma helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_notPrimal_of_selectedSupport
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (hselected_support :
      ∀ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
          0 ≤ t * (P.objective x - v) +
            ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              alpha i * P.inequalityConstraint i.1 x) :
    ¬ ∃ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P ∧
          helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha x < (0 : EReal) := by
  intro hprimal
  rcases hprimal with ⟨x, hxSelected, hxStrict⟩
  -- A negative strict-branch value on the selected slice contradicts the already isolated
  -- no-primal statement for the selected-support family.
  exact
    (helperForTheorem_6_28_3_selectedSupportFamily_notPrimal P alpha hselected_support)
      ⟨x, hxStrict, hxSelected.2.1, hxSelected.2.2⟩


end Section28
end Chap06
