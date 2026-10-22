/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part5
open scoped BigOperators Pointwise
section Chap06
section Section28
/-- Helper for Theorem 6.28.3: the mixed convex/affine alternative on the absorbed selected
slice already yields a positive strict coefficient and a local dual margin on that slice. -/
lemma helperForTheorem_6_28_3_exists_selectedAffineWeakSlice_localDualMargin_of_positiveScaledSupport_and_selectedAffineWeakRiPoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    [Fintype {i : Fin r // i ∉ P.nonaffineInequalityIndices}]
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
    (hri_selected :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
          (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) ∧
          x ∈ P.constraintSet ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
              (∀ j : Fin (m - r),
                helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0)) :
    ∃ μ : ℝ,
      ∃ beta : {i : Fin r // i ∉ P.nonaffineInequalityIndices} → ℝ,
        ∃ etaPos etaNeg : Fin (m - r) → ℝ,
          0 < μ ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}, 0 ≤ beta i) ∧
            (∀ j : Fin (m - r), 0 ≤ etaPos j) ∧
            (∀ j : Fin (m - r), 0 ≤ etaNeg j) ∧
            (∀ x : Fin n → ℝ,
              x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
                0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
                  (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
                    beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
                  (∑ q : Fin (m - r),
                    etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) +
                  ∑ q : Fin (m - r),
                    etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x)) := by
  classical
  let C := helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P
  let J := helperForTheorem_6_28_3_selectedAffineWeakAuxIndex P
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let fStrict : Fin 1 → (Fin n → ℝ) → EReal :=
    fun _ => helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha
  let fAffine : Fin (Fintype.card J) → (Fin n → ℝ) → ℝ :=
    fun k x => helperForTheorem_6_28_3_selectedAffineWeakAuxFamily P (eJ.symm k) x
  rcases hri_selected with ⟨x0, hx0ri_selected, hx0C, hAffine0, hEq0⟩
  have hconstraint_nonempty : P.constraintSet.Nonempty := ⟨x0, hx0C⟩
  have hfStrict :
      ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i
    fin_cases i
    -- The selected-support strict branch is proper convex on the ambient space.
    simpa [fStrict] using
      helperForTheorem_6_28_3_proper_selectedSupportIndicatorExtension
        P alpha hconstraint_nonempty (le_of_lt ht_pos) halpha_nonneg
  have hdomStrict :
      ∀ i : Fin 1,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i x hxri
    fin_cases i
    have hxSelected : x ∈ C :=
      helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hxri
    have hxConstraint : x ∈ P.constraintSet := hxSelected.1
    -- Every point of the selected slice still lies in `P.constraintSet`, so the indicator
    -- extension is finite there.
    change
      ∃ μ, (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha)
    refine ⟨helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x, ?_⟩
    refine
      (mem_epigraph_univ_iff
        (f := helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha)).2 ?_
    simp [helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
      helperForTheorem_6_28_3_indicatorExtension, hxConstraint]
  have hAffine :
      ∀ j : Fin (Fintype.card J), ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g := by
    intro j
    -- Reindex the pre-packaged combined affine family through `Fin`.
    simpa [fAffine] using
      helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_isAffine P (eJ.symm j)
  have hFeasRi_selected :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n C ∧
          ∀ j : Fin (Fintype.card J), fAffine j x ≤ 0 := by
    rcases
        helperForTheorem_6_28_3_selectedAffineWeakAuxFamily_feasRi_of_selectedAffineWeakRiPoint
          P ⟨x0, hx0ri_selected, hx0C, hAffine0, hEq0⟩ with
      ⟨x, hxri, hxAffine⟩
    refine ⟨x, hxri, ?_⟩
    intro j
    simpa [fAffine] using hxAffine (eJ.symm j)
  have hC_convex : Convex ℝ C := by
    -- The absorbed selected slice is convex because it is cut out by affine weak/equality data.
    simpa [C] using helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_convex P
  have hnot_primal :
      ¬ ∃ x : Fin n → ℝ,
          x ∈ C ∧
            (∀ i : Fin 1, fStrict i x < (0 : EReal)) ∧
              (∀ j : Fin (Fintype.card J), fAffine j x ≤ 0) := by
    intro hprimal
    rcases hprimal with ⟨x, hxC, hxStrict, _hxAffine⟩
    have hnot_selected :
        ¬ ∃ y : Fin n → ℝ,
            y ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P ∧
              helperForTheorem_6_28_3_selectedSupportIndicatorExtension P v t alpha y <
                (0 : EReal) := by
      -- The selected-slice support inequality already forbids the strict branch from being
      -- negative anywhere on the absorbed slice.
      exact
        helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet_notPrimal_of_selectedSupport
          P alpha hselected_support
    apply hnot_selected
    refine ⟨x, ?_, ?_⟩
    · simpa [C] using hxC
    · simpa [fStrict] using hxStrict 0
  have hAlt :=
    theorem21_mixed_convex_affine_alternative
      C hC_convex fStrict hfStrict hdomStrict fAffine hAffine hFeasRi_selected
  rw [xor_def] at hAlt
  rcases hAlt with hprimal | hdual
  · exact False.elim (hnot_primal hprimal.1)
  · rcases hdual.1 with
      ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero, hmargin⟩
    let μ : ℝ := lamStrict 0
    let beta : {i : Fin r // i ∉ P.nonaffineInequalityIndices} → ℝ :=
      fun i => lamAffine (eJ (Sum.inl i))
    let etaPos : Fin (m - r) → ℝ := fun j => lamAffine (eJ (Sum.inr (Sum.inl j)))
    let etaNeg : Fin (m - r) → ℝ := fun j => lamAffine (eJ (Sum.inr (Sum.inr j)))
    have hμ_ne : μ ≠ 0 := by
      rcases hStrictNonzero with ⟨i, hi⟩
      fin_cases i
      simpa [μ] using hi
    have hμ_pos : 0 < μ := by
      exact lt_of_le_of_ne (hlamStrictNonneg 0) (by simpa [eq_comm, μ] using hμ_ne)
    have hbeta_nonneg :
        ∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}, 0 ≤ beta i := by
      intro i
      simpa [beta] using hlamAffineNonneg (eJ (Sum.inl i))
    have hetaPos_nonneg : ∀ j : Fin (m - r), 0 ≤ etaPos j := by
      intro j
      simpa [etaPos] using hlamAffineNonneg (eJ (Sum.inr (Sum.inl j)))
    have hetaNeg_nonneg : ∀ j : Fin (m - r), 0 ≤ etaNeg j := by
      intro j
      simpa [etaNeg] using hlamAffineNonneg (eJ (Sum.inr (Sum.inr j)))
    have hselected_margin :
        ∀ x : Fin n → ℝ, x ∈ C →
          0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
            ∑ u : J,
              match u with
              | Sum.inl i =>
                  beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x
              | Sum.inr (Sum.inl q) =>
                  etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x
              | Sum.inr (Sum.inr q) =>
                  etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) := by
      intro x hxC
      have hxSelected : x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
        simpa [C] using hxC
      have hxConstraint : x ∈ P.constraintSet := hxSelected.1
      let affineRealTerm : J → ℝ := fun u =>
        match u with
        | Sum.inl i =>
            beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x
        | Sum.inr (Sum.inl q) =>
            etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x
        | Sum.inr (Sum.inr q) =>
            etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x)
      have hstrictSum :
          (∑ i : Fin 1, ((lamStrict i : ℝ) : EReal) * fStrict i x) =
            (((μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x : ℝ)) : EReal) := by
        -- The single strict multiplier scales the selected-support branch on the selected slice.
        simp [fStrict, μ, helperForTheorem_6_28_3_selectedSupportIndicatorExtension,
          helperForTheorem_6_28_3_indicatorExtension, hxConstraint, EReal.coe_mul]
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
              simp [affineRealTerm, fAffine, beta,
                helperForTheorem_6_28_3_selectedAffineWeakAuxFamily, hj_eq, EReal.coe_mul]
          | inr s =>
              cases s with
              | inl q =>
                  have hj_eq : j = eJ (Sum.inr (Sum.inl q)) := by
                    apply_fun eJ at hj
                    simpa using hj
                  simp [affineRealTerm, fAffine, etaPos,
                    helperForTheorem_6_28_3_selectedAffineWeakAuxFamily, hj_eq, EReal.coe_mul]
              | inr q =>
                  have hj_eq : j = eJ (Sum.inr (Sum.inr q)) := by
                    apply_fun eJ at hj
                    simpa using hj
                  simp [affineRealTerm, fAffine, etaNeg,
                    helperForTheorem_6_28_3_selectedAffineWeakAuxFamily, hj_eq, EReal.coe_mul]
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
      exact hmarginReal
    refine ⟨μ, beta, etaPos, etaNeg, hμ_pos, hbeta_nonneg, hetaPos_nonneg, hetaNeg_nonneg, ?_⟩
    intro x hxSelected
    let affineRealTerm : J → ℝ := fun u =>
      match u with
      | Sum.inl i =>
          beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x
      | Sum.inr (Sum.inl q) =>
          etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x
      | Sum.inr (Sum.inr q) =>
          etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x)
    have hAffineRealSplit :
        (∑ u : J, affineRealTerm u) =
          (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
            beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
            (∑ q : Fin (m - r),
              etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) +
              ∑ q : Fin (m - r),
                etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) := by
      -- Split the auxiliary sum back into the affine-inequality and two equality directions.
      calc
        (∑ u : J, affineRealTerm u) =
            (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}, affineRealTerm (Sum.inl i)) +
              ∑ s : Sum (Fin (m - r)) (Fin (m - r)), affineRealTerm (Sum.inr s) := by
                have hsum :
                    (∑ z : Sum {i : Fin r // i ∉ P.nonaffineInequalityIndices}
                      (Sum (Fin (m - r)) (Fin (m - r))), affineRealTerm z) =
                      (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
                        affineRealTerm (Sum.inl i)) +
                        ∑ s : Sum (Fin (m - r)) (Fin (m - r)), affineRealTerm (Sum.inr s) :=
                  Fintype.sum_sum_type (f := affineRealTerm)
                simpa [J] using hsum
        _ =
            (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
              ((∑ q : Fin (m - r), affineRealTerm (Sum.inr (Sum.inl q))) +
                ∑ q : Fin (m - r), affineRealTerm (Sum.inr (Sum.inr q))) := by
                  congr 1
                  simpa using
                    (Fintype.sum_sum_type
                      (f := fun s : Sum (Fin (m - r)) (Fin (m - r)) =>
                        affineRealTerm (Sum.inr s))
                      (α₁ := Fin (m - r)) (α₂ := Fin (m - r)))
        _ =
            (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
              (∑ q : Fin (m - r),
                etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) +
                ∑ q : Fin (m - r),
                  etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) := by
                    simp [affineRealTerm, add_assoc]
    have hLocalMargin :
        0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
          ∑ u : J, affineRealTerm u := by
      simpa [C, affineRealTerm] using hselected_margin x hxSelected
    rw [hAffineRealSplit] at hLocalMargin
    simpa [add_assoc] using hLocalMargin

/-- Helper for Theorem 6.28.3: the exact remaining semantic gap is to turn the selected-slice
local dual margin into a global positive-scaled Kuhn--Tucker support inequality on
`P.constraintSet`. -/
lemma helperForTheorem_6_28_3_selectedSliceLocalDualMargin_implies_positiveScaledSupport_on_selectedAffineWeakFeasibleSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    [Fintype {i : Fin r // i ∉ P.nonaffineInequalityIndices}]
    (ht_pos : 0 < t)
    (alpha : {i : Fin r // i ∈ P.nonaffineInequalityIndices} → ℝ)
    (halpha_nonneg :
      ∀ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices}, 0 ≤ alpha i)
    (μ : ℝ)
    (beta : {i : Fin r // i ∉ P.nonaffineInequalityIndices} → ℝ)
    (etaPos etaNeg : Fin (m - r) → ℝ)
    (hμ_pos : 0 < μ)
    (hbeta_nonneg :
      ∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices}, 0 ≤ beta i)
    (hselected_margin :
      ∀ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
          0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
            (∑ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) +
            (∑ q : Fin (m - r),
              etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) +
            ∑ q : Fin (m - r),
              etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x)) :
    ∃ alphaFull : Fin r → ℝ,
      ∃ eta : Fin (m - r) → ℝ,
        0 < μ * t ∧
          (∀ i : Fin r, 0 ≤ alphaFull i) ∧
            (∀ x : Fin n → ℝ,
              x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
                0 ≤ μ * t * (P.objective x - v) +
                  (∑ i : Fin r, alphaFull i * P.inequalityConstraint i x) +
                    ∑ j : Fin (m - r), eta j * P.equalityConstraint j x) := by
  classical
  let A : Type := {i : Fin r // i ∉ P.nonaffineInequalityIndices}
  let eta : Fin (m - r) → ℝ := fun _ => 0
  let alphaFull : Fin r → ℝ := fun i =>
    if hi : i ∈ P.nonaffineInequalityIndices then μ * alpha ⟨i, hi⟩ else beta ⟨i, hi⟩
  have halphaFull_nonneg : ∀ i : Fin r, 0 ≤ alphaFull i := by
    intro i
    by_cases hi : i ∈ P.nonaffineInequalityIndices
    · -- On the nonaffine block, positivity comes from scaling the original selected-support
      -- coefficients by the positive strict multiplier.
      simp [alphaFull, hi, halpha_nonneg, hμ_pos.le, mul_nonneg]
    · -- On the affine block, the mixed-alternative multiplier already supplies nonnegativity.
      simp [alphaFull, hi, hbeta_nonneg]
  refine ⟨alphaFull, eta, mul_pos hμ_pos ht_pos, halphaFull_nonneg, ?_⟩
  intro x hxSelected
  have hxC : x ∈ P.constraintSet := hxSelected.1
  have hEqPosZero :
      (∑ q : Fin (m - r),
        etaPos q * helperForTheorem_6_28_3_equalityConstraintRepresentative P q x) = 0 := by
    -- The selected slice already enforces the equality representatives to vanish.
    refine Finset.sum_eq_zero ?_
    intro q hq
    simp [hxSelected.2.2 q]
  have hEqNegZero :
      (∑ q : Fin (m - r),
        etaNeg q * (-helperForTheorem_6_28_3_equalityConstraintRepresentative P q x)) = 0 := by
    -- The same vanishing argument removes the negative equality branch as well.
    refine Finset.sum_eq_zero ?_
    intro q hq
    simp [hxSelected.2.2 q]
  have hLocalSelected :
      0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
        ∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x := by
    -- On the selected slice, the equality terms vanish, so only the strict branch and the affine
    -- weak-inequality block remain.
    have hLocalRaw := hselected_margin x hxSelected
    rw [hEqPosZero, hEqNegZero, add_assoc, add_zero, add_zero] at hLocalRaw
    simpa [A] using hLocalRaw
  have hAffineRepSum :
      (∑ i : A, beta i * helperForTheorem_6_28_3_affineInequalityRepresentative P i x) =
        ∑ i : A, beta i * P.inequalityConstraint i.1 x := by
    -- Inside `P.constraintSet`, the chosen affine representatives agree with the original
    -- affine inequality data.
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← helperForTheorem_6_28_3_affineInequalityRepresentative_eqOn P i hxC]
  have hWithOriginalData :
      0 ≤ μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
        ∑ i : A, beta i * P.inequalityConstraint i.1 x := by
    rw [hAffineRepSum] at hLocalSelected
    exact hLocalSelected
  have hselectedExpanded :
      μ * helperForTheorem_6_28_3_selectedSupportExpression P v t alpha x +
        ∑ i : A, beta i * P.inequalityConstraint i.1 x =
          μ * t * (P.objective x - v) +
            (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              (μ * alpha i) * P.inequalityConstraint i.1 x) +
            ∑ i : A, beta i * P.inequalityConstraint i.1 x := by
    -- Expand the selected support expression so the nonaffine and affine inequality blocks are
    -- visible with the original program data.
    rw [helperForTheorem_6_28_3_selectedSupportExpression, mul_add, Finset.mul_sum]
    have hObj :
        μ * (t * (P.objective x - v)) = μ * t * (P.objective x - v) := by
      ring
    have hScaledSum :
        (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
          μ * (alpha i * P.inequalityConstraint i.1 x)) =
            ∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              (μ * alpha i) * P.inequalityConstraint i.1 x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hObj]
    rw [hScaledSum]
  have hnonaffineFilter :
      (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
        (μ * alpha i) * P.inequalityConstraint i.1 x) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin r => i ∈ P.nonaffineInequalityIndices),
            alphaFull i * P.inequalityConstraint i x := by
    -- Rewrite the nonaffine subtype sum as the filtered ambient inequality sum.
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
    -- Rewrite the affine subtype sum as the complementary filtered ambient inequality sum.
    calc
      (∑ i : A, beta i * P.inequalityConstraint i.1 x) =
          ∑ i : A, alphaFull i.1 * P.inequalityConstraint i.1 x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_not : i.1 ∉ P.nonaffineInequalityIndices := i.2
            simp [alphaFull, hi_not]
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
    -- The nonaffine and affine filtered sums partition the full inequality block.
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
  have hglobalSelected :
      0 ≤ μ * t * (P.objective x - v) +
        ∑ i : Fin r, alphaFull i * P.inequalityConstraint i x := by
    have hExpandedData :
        0 ≤ μ * t * (P.objective x - v) +
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            (μ * alpha i) * P.inequalityConstraint i.1 x) +
          ∑ i : A, beta i * P.inequalityConstraint i.1 x := by
      rwa [hselectedExpanded] at hWithOriginalData
    -- The selected-slice support inequality now has the exact full-inequality form needed later.
    calc
      0 ≤ μ * t * (P.objective x - v) +
          (∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
            (μ * alpha i) * P.inequalityConstraint i.1 x) +
          ∑ i : A, beta i * P.inequalityConstraint i.1 x := hExpandedData
      _ = μ * t * (P.objective x - v) +
            ((∑ i : {i : Fin r // i ∈ P.nonaffineInequalityIndices},
              (μ * alpha i) * P.inequalityConstraint i.1 x) +
              ∑ i : A, beta i * P.inequalityConstraint i.1 x) := by
            simp [add_assoc]
      _ = μ * t * (P.objective x - v) +
            ∑ i : Fin r, alphaFull i * P.inequalityConstraint i x := by
            rw [hineqSplit]
  -- The selected-slice certificate uses no equality term, so we keep the equality block at `0`.
  simpa [eta] using hglobalSelected

/-- Helper for Theorem 6.28.3: a selected-slice relative-interior witness already gives a
concrete point of the absorbed affine/equality slice where the selected support inequality can be
evaluated. -/
lemma helperForTheorem_6_28_3_exists_selectedAffineWeakFeasiblePoint_with_selectedSupport_of_selectedAffineWeakRi
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v t μ : ℝ}
    [Fintype {i : Fin r // i ∈ P.nonaffineInequalityIndices}]
    (alphaFull : Fin r → ℝ)
    (eta : Fin (m - r) → ℝ)
    (hri_selected :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
          (helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P) ∧
          x ∈ P.constraintSet ∧
            (∀ i : {i : Fin r // i ∉ P.nonaffineInequalityIndices},
              helperForTheorem_6_28_3_affineInequalityRepresentative P i x ≤ 0) ∧
              (∀ j : Fin (m - r),
                helperForTheorem_6_28_3_equalityConstraintRepresentative P j x = 0))
    (hselected_global :
      ∀ x : Fin n → ℝ,
        x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P →
          0 ≤ μ * t * (P.objective x - v) +
            (∑ i : Fin r, alphaFull i * P.inequalityConstraint i x) +
              ∑ j : Fin (m - r), eta j * P.equalityConstraint j x) :
    ∃ x : Fin n → ℝ,
      x ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P ∧
        0 ≤ μ * t * (P.objective x - v) +
          (∑ i : Fin r, alphaFull i * P.inequalityConstraint i x) +
            ∑ j : Fin (m - r), eta j * P.equalityConstraint j x := by
  rcases hri_selected with ⟨x0, _hx0ri, hx0C, hAffine0, hEq0⟩
  have hx0Selected : x0 ∈ helperForTheorem_6_28_3_selectedAffineWeakFeasibleSet P := by
    -- The side conditions attached to the selected-slice witness are exactly the defining
    -- constraints of the absorbed affine/equality slice.
    exact ⟨hx0C, hAffine0, hEq0⟩
  refine ⟨x0, hx0Selected, ?_⟩
  -- Once the witness is recognized as a point of the selected slice, the selected support
  -- inequality can be evaluated there directly.
  exact hselected_global x0 hx0Selected

/-- Helper for Theorem 6.28.3: a global perturbation-support inequality for `lambda` already
forces the affine lower bound `v ≤ f₀(x) + ⟪lambda, u⟫` on every point feasible for the perturbed
problem `(P_u)`. -/
lemma helperForTheorem_6_28_3_lowerBound_on_all_perturbedFeasiblePoints_of_perturbationSupport
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ} (lambda : Fin m → ℝ)
    (hp0_eq_v : P.perturbationFunction 0 = (v : EReal))
    (hsupport :
      ∀ u : Fin m → ℝ,
        P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≥
          P.perturbationFunction 0) :
    ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ,
      x ∈ (P.perturbedProblem u).feasibleSet →
        v ≤ P.objective x + ∑ i : Fin m, lambda i * u i := by
  intro u x hx
  have hu_le : P.perturbationFunction u ≤ ((P.objective x : ℝ) : EReal) := by
    -- Any point feasible for `(P_u)` contributes an upper bound to the infimum defining
    -- `P.perturbationFunction u`.
    rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨x, hx, rfl⟩
  have hupper :
      P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≤
        (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
    -- Add the same perturbation pairing to the objective upper bound coming from `x`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (show P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≤
          ((P.objective x : ℝ) : EReal) + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) from by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right hu_le ((((∑ i : Fin m, lambda i * u i) : ℝ)) : EReal))
  have hv_le :
      (v : EReal) ≤ (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
    -- Chain the support inequality with the infimum upper bound contributed by the chosen
    -- perturbed-feasible point.
    calc
      (v : EReal) = P.perturbationFunction 0 := hp0_eq_v.symm
      _ ≤ P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
          simpa using hsupport u
      _ ≤ (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := hupper
  exact EReal.coe_le_coe_iff.1 hv_le

/-- Helper for Theorem 6.28.3: to prove the perturbation-support inequality for `lambda`, it
suffices to show that the same affine functional lower-bounds the primal objective at every
perturbed-feasible point. -/
lemma helperForTheorem_6_28_3_perturbationSupport_of_lowerBound_on_all_perturbedFeasiblePoints
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ} (lambda : Fin m → ℝ)
    (hp0_eq_v : P.perturbationFunction 0 = (v : EReal))
    (hlower :
      ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ,
        x ∈ (P.perturbedProblem u).feasibleSet →
          v ≤ P.objective x + ∑ i : Fin m, lambda i * u i) :
    ∀ u : Fin m → ℝ,
      P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≥
        P.perturbationFunction 0 := by
  intro u
  let c : ℝ := ∑ i : Fin m, lambda i * u i
  have hshift : ((v - c : ℝ) : EReal) ≤ P.perturbationFunction u := by
    -- Show that `v - ⟪lambda, u⟫` is a lower bound for every objective value attained on the
    -- perturbed feasible set, then pass to the infimum.
    rw [BookOrdinaryConvexProgram.perturbationFunction, BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hreal : v - c ≤ P.objective x := by
      have hreal' : v ≤ P.objective x + c := by
        simpa [c] using hlower u x hx
      linarith
    change ((v - c : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal)
    exact_mod_cast hreal
  have hv_le : (v : EReal) ≤ P.perturbationFunction u + (c : EReal) := by
    -- Adding the pairing back recovers the desired affine lower support at the perturbation `u`.
    have htmp :
        (((v - c : ℝ) : EReal) + (c : EReal)) ≤ P.perturbationFunction u + (c : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hshift (c : EReal)
    have hleft : (((v - c : ℝ) : EReal) + (c : EReal)) = (v : EReal) := by
      exact_mod_cast sub_add_cancel v c
    rw [hleft] at htmp
    exact htmp
  calc
    P.perturbationFunction 0 = (v : EReal) := hp0_eq_v
    _ ≤ P.perturbationFunction u + (c : EReal) := hv_le
    _ = P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) := by
        rfl

/-- Helper for Theorem 6.28.3: the canonical multiplier built from `alphaFull`, `eta`, and the
positive scale `s` has nonnegative inequality coordinates because the numerator coefficients are
already nonnegative. -/
lemma helperForTheorem_6_28_3_canonicalMultiplier_nonneg
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {s : ℝ}
    (alphaFull : Fin r → ℝ) (eta : Fin (m - r) → ℝ)
    (hs_pos : 0 < s)
    (halphaFull_nonneg : ∀ i : Fin r, 0 ≤ alphaFull i) :
    let lambda : Fin m → ℝ :=
      (Fin.append (fun i : Fin r => alphaFull i / s) (fun j : Fin (m - r) => eta j / s)) ∘
        Fin.cast (Nat.add_sub_of_le P.inequalityCount_le_constraintCount).symm
    ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i := by
  intro lambda i
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  -- The first `r` coordinates of the canonical multiplier are exactly `alphaFull i / s`.
  simpa [BookOrdinaryConvexProgram.inequalityMultipliers, lambda] using
    div_nonneg (halphaFull_nonneg i) hs_nonneg

/-- Helper for Theorem 6.28.3: once the canonical multiplier already gives a global lower bound
for the ordinary Kuhn--Tucker objective on `P.constraintSet`, Section 6.28.2 turns that ambient
support statement into the desired lower bound on every perturbed-feasible point. -/
lemma helperForTheorem_6_28_3_lowerBound_on_all_perturbedFeasiblePoints_of_kuhnTuckerObjective_lowerBound
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ} (lambda : Fin m → ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hobjective_lower :
      ∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) :
    ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ,
      x ∈ (P.perturbedProblem u).feasibleSet →
        v ≤ P.objective x + ∑ i : Fin m, lambda i * u i := by
  intro u x hx
  have hkuhn_lower : v ≤ P.kuhnTuckerObjective lambda x := hobjective_lower x hx.1
  have hkuhn_upperE :
      ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤
        (((P.objective x + ∑ i : Fin m, lambda i * u i) : ℝ) : EReal) :=
    helperForTheorem_6_28_2_kuhnTuckerObjective_le_objective_plus_pairing_of_perturbedFeasible
      P lambda hx hlambda_nonneg
  have hkuhn_upper :
      P.kuhnTuckerObjective lambda x ≤ P.objective x + ∑ i : Fin m, lambda i * u i :=
    EReal.coe_le_coe_iff.1 hkuhn_upperE
  -- Combine the ambient lower bound with the perturbed-feasibility upper estimate.
  exact le_trans hkuhn_lower hkuhn_upper

end Section28
end Chap06
