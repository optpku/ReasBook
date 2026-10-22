/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part6

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.3: once the absorbed affine weak/equality block has a witness in
`ri P.constraintSet`, the selected-set support inequality extends to a global Kuhn--Tucker
multiplier lower-bound certificate on all of `P.constraintSet`. -/
lemma helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_positiveScaledSupport_and_affineWeakRiFeasiblePoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (hoptimal : P.optimalValue = (v : EReal))
    (ht_pos : 0 < t)
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (halpha_nonneg :
      ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i)
    (hselected_support :
      ∀ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
          0 ≤ t * (P.objective x - v) +
            ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              alpha i * P.inequalityConstraint i.1 x)
    (hri_affine_feasible :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n P.constraintSet ∧
          (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
            (∀ j : Fin (m - r),
              helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) :
    ∃ lambda : Fin m → ℝ,
      P.optimalValue = (v : EReal) ∧
        (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
          (∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) := by
  classical
  let A : Type := {i : Fin r // i ∉ P.nonaffineInequalityIndices}
  let J : Type := Sum A (Sum (Fin (m - r)) (Fin (m - r)))
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let fStrict : Fin 1 → (Fin n → ℝ) → EReal :=
    fun _ => helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha
  let fAffine : Fin (Fintype.card J) → (Fin n → ℝ) → ℝ :=
    fun k x =>
      match eJ.symm k with
      | Sum.inl i => helperForTheorem_6_28_3_affineInequalityRepresentative P i x
      | Sum.inr (Sum.inl j) => helperForTheorem_6_28_3_equalityConstraintRepresentative P j x
      | Sum.inr (Sum.inr j) => -helperForTheorem_6_28_3_equalityConstraintRepresentative P j x
  rcases hri_affine_feasible with ⟨x0, hx0ri, hAffine0, hEq0⟩
  have hx0C : x0 ∈ P.constraintSet :=
    helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hx0ri
  have hconstraint_nonempty : P.constraintSet.Nonempty := ⟨x0, hx0C⟩
  have hfStrict :
      ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i
    fin_cases i
    -- The selected support branch is proper convex after indicator extension to `ℝ^n`.
    simpa [fStrict] using
      helperForTheorem_6_28_3_proper_selectedSupportIndicatorExtension
        P alpha hconstraint_nonempty (le_of_lt ht_pos) halpha_nonneg
  have hdomStrict :
      ∀ i : Fin 1,
        euclideanRelativeInterior_fin n P.constraintSet ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i x hxri
    fin_cases i
    have hxC : x ∈ P.constraintSet :=
      helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hxri
    -- Points of `ri P.constraintSet` stay in `P.constraintSet`, so the indicator extension is
    -- finite there.
    change
      ∃ μ, (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha)
    refine ⟨helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x, ?_⟩
    refine
      (mem_epigraph_univ_iff
        (f := helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha)).2 ?_
    simp [helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hxC]
  have hAffine :
      ∀ j : Fin (Fintype.card J), ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g := by
    intro j
    cases hj : eJ.symm j with
    | inl i =>
        refine ⟨helperForTheorem_6_28_3_affineInequalityRepresentative P i, ?_⟩
        ext x
        simp [fAffine, hj]
    | inr s =>
        cases s with
        | inl q =>
            refine ⟨helperForTheorem_6_28_3_equalityConstraintRepresentative P q, ?_⟩
            ext x
            simp [fAffine, hj]
        | inr q =>
            refine ⟨-helperForTheorem_6_28_3_equalityConstraintRepresentative P q, ?_⟩
            ext x
            simp [fAffine, hj]
  have hFeasRi :
      ∃ x, x ∈ euclideanRelativeInterior_fin n P.constraintSet ∧
        ∀ j : Fin (Fintype.card J), fAffine j x ≤ 0 := by
    refine ⟨x0, hx0ri, ?_⟩
    intro j
    cases hj : eJ.symm j with
    | inl i =>
        -- The affine weak inequalities are part of the assumed `ri` witness.
        simpa [fAffine, hj] using hAffine0 i
    | inr s =>
        cases s with
        | inl q =>
            -- The equality block contributes both `g ≤ 0` and `-g ≤ 0`.
            simpa [fAffine, hj, hEq0 q]
        | inr q =>
            simpa [fAffine, hj, hEq0 q]
  have hnot_primal :
      ¬ ∃ x, x ∈ P.constraintSet ∧
          (∀ i : Fin 1, fStrict i x < (0 : EReal)) ∧
            (∀ j : Fin (Fintype.card J), fAffine j x ≤ 0) := by
    intro hprimal
    rcases hprimal with ⟨x, hxC, hxStrict, hxAffine⟩
    have hfamily_not_primal :
        ¬ ∃ y : Fin n → ℝ,
            helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha y <
                (0 : EReal) ∧
              (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
                helperForTheorem_6_28_3_affineInequalityRepresentative P i y ≤ 0) ∧
                (∀ j : Fin (m - r),
                  helperForTheorem_6_28_3_equalityConstraintRepresentative P j y = 0) := by
      -- Reuse the extracted selected-support contradiction instead of rebuilding it locally.
      exact
        helperForTheorem_6_28_3_selectedSupportFamily_notPrimal
          P alpha hselected_support
    apply hfamily_not_primal
    refine ⟨x, ?_, ?_, ?_⟩
    · -- On `P.constraintSet`, the strict family is exactly the selected support indicator branch.
      simpa [fStrict, helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
        helperForTheorem_6_28_3_indicatorExtension, hxC] using hxStrict 0
    · intro i
      have hAffine_i : fAffine (eJ (Sum.inl i)) x ≤ 0 := hxAffine (eJ (Sum.inl i))
      simpa [fAffine] using hAffine_i
    · intro j
      have hEqLe : fAffine (eJ (Sum.inr (Sum.inl j))) x ≤ 0 :=
        hxAffine (eJ (Sum.inr (Sum.inl j)))
      have hNegEqLe : fAffine (eJ (Sum.inr (Sum.inr j))) x ≤ 0 :=
        hxAffine (eJ (Sum.inr (Sum.inr j)))
      have hEqRep_le :
          helperForTheorem_6_28_3_equalityConstraintRepresentative P j x ≤ 0 := by
        simpa [fAffine] using hEqLe
      have hEqRep_ge :
          0 ≤ helperForTheorem_6_28_3_equalityConstraintRepresentative P j x := by
        have hneg_nonpos :
            -helperForTheorem_6_28_3_equalityConstraintRepresentative P j x ≤ 0 := by
          simpa [fAffine] using hNegEqLe
        linarith
      exact le_antisymm hEqRep_le hEqRep_ge
  have hAlt :=
    theorem21_mixed_convex_affine_alternative
      P.constraintSet P.convex_constraintSet
      fStrict hfStrict hdomStrict fAffine hAffine hFeasRi
  rw [xor_def] at hAlt
  rcases hAlt with hprimal | hdual
  · exact False.elim (hnot_primal hprimal.1)
  · rcases hdual.1 with
      ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero, hmargin⟩
    let μ : ℝ := lamStrict 0
    let beta : A → ℝ := fun i => lamAffine (eJ (Sum.inl i))
    let etaPos : Fin (m - r) → ℝ := fun j => lamAffine (eJ (Sum.inr (Sum.inl j)))
    let etaNeg : Fin (m - r) → ℝ := fun j => lamAffine (eJ (Sum.inr (Sum.inr j)))
    have hμ_ne : μ ≠ 0 := by
      rcases hStrictNonzero with ⟨i, hi⟩
      fin_cases i
      simpa [μ] using hi
    have hμ_pos : 0 < μ := lt_of_le_of_ne (hlamStrictNonneg 0) (by simpa [eq_comm, μ] using hμ_ne)
    let eta : Fin (m - r) → ℝ := fun j => etaPos j - etaNeg j
    let alphaFull : Fin r → ℝ := fun i =>
      if hi : i ∈ P.nonaffineInequalityIndices then μ * alpha ⟨i, hi⟩ else beta ⟨i, hi⟩
    have halphaFull_nonneg : ∀ i : Fin r, 0 ≤ alphaFull i := by
      intro i
      by_cases hi : i ∈ P.nonaffineInequalityIndices
      · -- The nonaffine coefficients are the old ones scaled by the positive strict weight.
        simp [alphaFull, hi, halpha_nonneg, hμ_pos.le, mul_nonneg]
      · -- The affine weak coefficients come directly from the mixed-alternative multiplier.
        simp [alphaFull, hi, beta, hlamAffineNonneg]
    have hglobal :
        ∀ x : Fin n → ℝ, x ∈ P.constraintSet →
          0 ≤ μ * t * (P.objective x - v) +
            (∑ i : Fin r, alphaFull i * P.inequalityConstraint i x) +
              ∑ j : Fin (m - r), eta j * P.equalityConstraint j x := by
      intro x hxC
      let affineRealTerm : J → ℝ := fun u =>
        match u with
        | Sum.inl i => beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x
        | Sum.inr (Sum.inl j) =>
            etaPos j * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x
        | Sum.inr (Sum.inr j) =>
            etaNeg j * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P j x)
      have hstrictSum :
          (∑ i : Fin 1, ((lamStrict i : ℝ) : EReal) * fStrict i x) =
            (((μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x : ℝ)) : EReal) := by
        -- The single strict multiplier scales the selected support branch.
        simp [fStrict, μ, helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
          helperForTheorem_6_28_3_indicatorExtension, hxC, EReal.coe_mul]
      have hAffineSum :
          (∑ j : Fin (Fintype.card J), ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) =
            ((((∑ u : J, affineRealTerm u : ℝ) : ℝ) : EReal)) := by
        have hToJ :
            (∑ j : Fin (Fintype.card J), ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) =
              ∑ u : J, (((affineRealTerm u : ℝ) : EReal)) := by
          refine Fintype.sum_equiv eJ.symm
            (fun j : Fin (Fintype.card J) => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal))
            (fun u : J => (((affineRealTerm u : ℝ) : EReal))) ?_
          intro j
          cases hj : eJ.symm j with
          | inl i =>
              have hj_eq : j = eJ (Sum.inl i) := by
                apply_fun eJ at hj
                simpa using hj
              simp [affineRealTerm, fAffine, beta, hj_eq, EReal.coe_mul]
          | inr s =>
              cases s with
              | inl q =>
                  have hj_eq : j = eJ (Sum.inr (Sum.inl q)) := by
                    apply_fun eJ at hj
                    simpa using hj
                  simp [affineRealTerm, fAffine, etaPos, hj_eq, EReal.coe_mul]
              | inr q =>
                  have hj_eq : j = eJ (Sum.inr (Sum.inr q)) := by
                    apply_fun eJ at hj
                    simpa using hj
                  simp [affineRealTerm, fAffine, etaNeg, hj_eq, EReal.coe_mul]
        calc
          (∑ j : Fin (Fintype.card J), ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) =
              ∑ u : J, (((affineRealTerm u : ℝ) : EReal)) := hToJ
          _ = ((((∑ u : J, affineRealTerm u : ℝ) : ℝ) : EReal)) := by
                symm
                exact
                  helperForTheorem_21_1_coe_finset_sum_real
                    (s := (Finset.univ : Finset J))
                    (g := affineRealTerm)
      have hmarginE :
          (0 : EReal) ≤
            (((μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x : ℝ)) : EReal) +
              ((((∑ u : J, affineRealTerm u : ℝ) : ℝ) : EReal)) := by
        calc
          (0 : EReal) ≤
              (∑ i : Fin 1, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                ∑ j : Fin (Fintype.card J), ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal) :=
            hmargin x hxC
          _ =
              (((μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x : ℝ)) : EReal) +
                ((((∑ u : J, affineRealTerm u : ℝ) : ℝ) : EReal)) := by
                rw [hstrictSum, hAffineSum]
      have hmarginReal :
          0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
            ∑ u : J, affineRealTerm u := by
        have hmarginRealE :
            (0 : EReal) ≤
              (((μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
                ∑ u : J, affineRealTerm u : ℝ) : ℝ) : EReal) := by
          simpa using hmarginE
        exact_mod_cast hmarginRealE
      have hAffineRealSplit :
          (∑ u : J, affineRealTerm u) =
            (∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
              (∑ j : Fin (m - r),
                etaPos j * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) +
                ∑ j : Fin (m - r),
                  etaNeg j * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) := by
        -- Split the mixed affine block into affine inequalities and the two equality directions.
        calc
          (∑ u : J, affineRealTerm u) =
              (∑ i : A, affineRealTerm (Sum.inl i)) +
                ∑ s : Sum (Fin (m - r)) (Fin (m - r)), affineRealTerm (Sum.inr s) := by
                simpa [J] using
                  (Fintype.sum_sum_type
                    (f := affineRealTerm) (α := A) (β := Sum (Fin (m - r)) (Fin (m - r))))
          _ =
              (∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
                ((∑ j : Fin (m - r), affineRealTerm (Sum.inr (Sum.inl j))) +
                  ∑ j : Fin (m - r), affineRealTerm (Sum.inr (Sum.inr j))) := by
                    congr 1
                    simpa using
                      (Fintype.sum_sum_type
                        (f := fun s : Sum (Fin (m - r)) (Fin (m - r)) =>
                          affineRealTerm (Sum.inr s))
                        (α := Fin (m - r)) (β := Fin (m - r)))
          _ =
              (∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
                (∑ j : Fin (m - r),
                  etaPos j * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) +
                  ∑ j : Fin (m - r),
                    etaNeg j * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) := by
                      simp [affineRealTerm, add_assoc]
      have hWithOriginalData :
          0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
            (∑ i : A, beta i * P.inequalityConstraint i.1 x) +
              (∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x) := by
        have hConverted :
            0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
              ((∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
                (∑ j : Fin (m - r),
                  etaPos j * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) +
                  ∑ j : Fin (m - r),
                    etaNeg j * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P j x)) := by
          simpa [hAffineRealSplit, add_assoc] using hmarginReal
        have hAffineRepSum :
            (∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) =
              ∑ i : A, beta i * P.inequalityConstraint i.1 x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn P i hxC]
        have hEqPosRepSum :
            (∑ j : Fin (m - r),
              etaPos j * helperForTheorem_6_28_3_equalityConstraintRepresentative P j x) =
                ∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn P j hxC]
        have hEqNegRepSum :
            (∑ j : Fin (m - r),
              etaNeg j * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P j x)) =
                ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn P j hxC]
        -- Replace the chosen affine representatives by the original program data on `C`.
        rw [hAffineRepSum, hEqPosRepSum, hEqNegRepSum] at hConverted
        simpa [add_assoc] using hConverted
      have hselectedExpanded :
          μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x =
            μ * t * (P.objective x - v) +
              ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                (μ * alpha i) * P.inequalityConstraint i.1 x := by
        -- Expand the selected support expression so the affine and nonaffine blocks can be merged.
        rw [helperForTheorem_6_28_3_selectedSupportExpression, mul_add, Finset.mul_sum]
        have hObj :
            μ * (t * (P.objective x - v)) = μ * t * (P.objective x - v) := by
          ring
        rw [hObj]
        refine congrArg (fun s =>
          μ * t * (P.objective x - v) + s) ?_
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      have hnonaffineFilter :
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            (μ * alpha i) * P.inequalityConstraint i.1 x) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∈ P.nonaffineInequalityIndices),
              alphaFull i * P.inequalityConstraint i x := by
        calc
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              (μ * alpha i) * P.inequalityConstraint i.1 x) =
              ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                alphaFull i.1 * P.inequalityConstraint i.1 x := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hi_mem : i.1 ∈ P.nonaffineInequalityIndices := i.2
                  simp [alphaFull, hi_mem]
          _ =
              ∑ i ∈ Finset.subtype (fun i : Fin r => i ∈ P.nonaffineInequalityIndices)
                (Finset.univ : Finset (Fin r)),
                alphaFull i.1 * P.inequalityConstraint i.1 x := by
                  simp
          _ =
              ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∈ P.nonaffineInequalityIndices),
                alphaFull i * P.inequalityConstraint i x := by
                  exact
                    (Finset.sum_subtype_eq_sum_filter
                      (s := (Finset.univ : Finset (Fin r)))
                      (p := fun i : Fin r => i ∈ P.nonaffineInequalityIndices)
                      (f := fun i : Fin r => alphaFull i * P.inequalityConstraint i x))
      have hAffineFilter :
          (∑ i : A, beta i * P.inequalityConstraint i.1 x) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∉ P.nonaffineInequalityIndices),
              alphaFull i * P.inequalityConstraint i x := by
        calc
          (∑ i : A, beta i * P.inequalityConstraint i.1 x) =
              ∑ i : A, alphaFull i.1 * P.inequalityConstraint i.1 x := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hi_not : i.1 ∉ P.nonaffineInequalityIndices := i.2
                simp [alphaFull, hi_not, beta]
          _ =
              ∑ i ∈ Finset.subtype (fun i : Fin r => i ∉ P.nonaffineInequalityIndices)
                (Finset.univ : Finset (Fin r)),
                alphaFull i.1 * P.inequalityConstraint i.1 x := by
                  simpa [A]
          _ =
              ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∉ P.nonaffineInequalityIndices),
                alphaFull i * P.inequalityConstraint i x := by
                  exact
                    (Finset.sum_subtype_eq_sum_filter
                      (s := (Finset.univ : Finset (Fin r)))
                      (p := fun i : Fin r => i ∉ P.nonaffineInequalityIndices)
                      (f := fun i : Fin r => alphaFull i * P.inequalityConstraint i x))
      have hineqSplit :
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            (μ * alpha i) * P.inequalityConstraint i.1 x) +
            ∑ i : A, beta i * P.inequalityConstraint i.1 x =
              ∑ i : Fin r, alphaFull i * P.inequalityConstraint i x := by
        calc
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              (μ * alpha i) * P.inequalityConstraint i.1 x) +
              ∑ i : A, beta i * P.inequalityConstraint i.1 x
            =
              (∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∈ P.nonaffineInequalityIndices),
                alphaFull i * P.inequalityConstraint i x) +
                ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∉ P.nonaffineInequalityIndices),
                  alphaFull i * P.inequalityConstraint i x := by
                    rw [hnonaffineFilter, hAffineFilter]
          _ = ∑ i : Fin r, alphaFull i * P.inequalityConstraint i x := by
                simpa using
                  (Finset.sum_filter_add_sum_filter_not
                    (s := (Finset.univ : Finset (Fin r)))
                    (p := fun i : Fin r => i ∈ P.nonaffineInequalityIndices)
                    (f := fun i : Fin r => alphaFull i * P.inequalityConstraint i x))
      have hEqNegRewrite :
          (∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x)) =
            ∑ j : Fin (m - r), (-etaNeg j) * P.equalityConstraint j x := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      have hEqSplit :
          (∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
            ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x) =
              ∑ j : Fin (m - r), eta j * P.equalityConstraint j x := by
        rw [hEqNegRewrite, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [eta]
        ring
      have hGlobalForm :
          0 ≤ μ * t * (P.objective x - v) +
            ((∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                (μ * alpha i) * P.inequalityConstraint i.1 x) +
              ∑ i : A, beta i * P.inequalityConstraint i.1 x) +
              ((∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x)) := by
        have hExpandedData :
            0 ≤ μ * t * (P.objective x - v) +
              (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                (μ * alpha i) * P.inequalityConstraint i.1 x) +
                (∑ i : A, beta i * P.inequalityConstraint i.1 x) +
                  (∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                    ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x) := by
          rwa [hselectedExpanded] at hWithOriginalData
        have hAssoc :
            μ * t * (P.objective x - v) +
              ((∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                  (μ * alpha i) * P.inequalityConstraint i.1 x) +
                ∑ i : A, beta i * P.inequalityConstraint i.1 x) +
                ((∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                  ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x)) =
              μ * t * (P.objective x - v) +
                (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                  (μ * alpha i) * P.inequalityConstraint i.1 x) +
                  (∑ i : A, beta i * P.inequalityConstraint i.1 x) +
                    (∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                      ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x) := by
          ac_rfl
        rw [hAssoc]
        exact hExpandedData
      calc
        0 ≤ μ * t * (P.objective x - v) +
            ((∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                (μ * alpha i) * P.inequalityConstraint i.1 x) +
              ∑ i : A, beta i * P.inequalityConstraint i.1 x) +
              ((∑ j : Fin (m - r), etaPos j * P.equalityConstraint j x) +
                ∑ j : Fin (m - r), etaNeg j * (-P.equalityConstraint j x)) :=
          hGlobalForm
        _ = μ * t * (P.objective x - v) +
              (∑ i : Fin r, alphaFull i * P.inequalityConstraint i x) +
                ∑ j : Fin (m - r), eta j * P.equalityConstraint j x := by
              rw [hineqSplit, hEqSplit]
    -- Normalize the mixed-alternative support inequality into the textbook multiplier format.
    exact
      helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_positiveScaledKuhnTuckerSupport
        P hoptimal (mul_pos hμ_pos ht_pos) alphaFull eta halphaFull_nonneg hglobal

/-- Helper for Theorem 6.28.3: the direct remaining prerequisite is the Section 29 statement
that the selected-slice Chapter 21 local-dual-margin package already rules out a bilateral
`-∞` directional witness for the direct perturbation bifunction. -/
lemma helperForTheorem_6_28_3_no_bilateralDirectionalDerivative_of_directPerturbationKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hfinite :
      IsFiniteEReal
        (generalizedConvexProgramOptimalValue
          (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)))
    {lambda : Fin m → ℝ}
    (hKT_F :
      IsKuhnTuckerVector (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) lambda) :
    ¬ ∃ u : Fin m → ℝ,
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) := by
  intro hbilat
  -- Corollary 6.29.2 converts the bilateral `-∞` witness into nonexistence of generalized
  -- Kuhn--Tucker vectors, contradicting the supplied direct perturbation certificate.
  exact
    (generalizedConvexProgram_noKuhnTuckerVector_iff_exists_bilateralDirectionalDerivative_eq_bot
      (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) hfinite).2 hbilat
      ⟨lambda, hKT_F⟩

/-- Helper for Theorem 6.28.3: finite optimal value and strict feasibility on the nonaffine
inequality block yield a multiplier certificate once the selected-slice Chapter 21 margin data is
converted into the direct Section 29 no-bilateral-obstruction statement. -/
lemma helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ v : ℝ, ∃ lambda : Fin m → ℝ,
      P.optimalValue = (v : EReal) ∧
        (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
          (∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) := by
  rcases
      helperForTheorem_6_28_3_exists_real_optimalValue_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
        P hoptimal_ne_bot hstrict_feasible with
    ⟨v, hoptimal⟩
  refine ⟨v, ?_⟩
  let _ : Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices} := Fintype.ofFinite _
  let _ : Fintype {i : Fin r // i ∉ P.nonaffineInequalityIndices} := Fintype.ofFinite _
  have hselected_support :
      ∃ t : ℝ,
        ∃ alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ,
          0 < t ∧
            (∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i) ∧
              (∀ x : Fin n → ℝ,
                x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
                  0 ≤ t * (P.objective x - v) +
                    ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
                      alpha i * P.inequalityConstraint i.1 x) := by
    -- Theorem 21.1 already produces a positive scaled support inequality once the affine weak
    -- and equality block has been absorbed into the selected ambient set.
    exact
      helperForTheorem_6_28_3_exists_positiveScaledSupport_on_selectedAffineWeakFeasibleSet
        P hoptimal hstrict_feasible
  rcases hselected_support with ⟨t, alpha, ht_pos, halpha_nonneg, hselected_support⟩
  rcases hstrict_feasible with ⟨x0, hx0ri, hx0Feasible, _hstrict0⟩
  rcases hx0Feasible with ⟨hx0C, hineq0, heq0⟩
  have hAffine0 :
      ∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
        helperForTheorem_6_28_3_affineInequalityRepresentative P i x0 ≤ 0 := by
    intro i
    have hEq :
        P.inequalityConstraint i.1 x0 =
          helperForTheorem_6_28_3_affineInequalityRepresentative P i x0 :=
      helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn P i hx0C
    simpa [← hEq] using hineq0 i.1
  have hEq0 :
      ∀ j : Fin (m - r),
        helperForTheorem_6_28_3_equalityConstraintRepresentative P j x0 = 0 := by
    intro j
    have hEq :
        P.equalityConstraint j x0 =
          helperForTheorem_6_28_3_equalityConstraintRepresentative P j x0 :=
      helperForTheorem_6_28_3_equalityConstraintRepresentative_eqOn P j hx0C
    simpa [← hEq] using heq0 j
  exact
    helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_positiveScaledSupport_and_affineWeakRiFeasiblePoint
      P hoptimal ht_pos alpha halpha_nonneg hselected_support ⟨x0, hx0ri, hAffine0, hEq0⟩

end Section28
end Chap06
