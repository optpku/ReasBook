/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.section02_part1

open scoped BigOperators

section Chap07
section Section02

/-- Helper for Proposition 7.2: thickening each side of a closed box by `ε` gives
an explicit upper bound for `boxOuterMeasure`. -/
lemma helperForProposition_7_2_closedBox_outer_le_thickened
    {d : ℕ} (a b : Fin (d + 1) → ℝ) (h : ∀ i, a i ≤ b i)
    {ε : ℝ} (hε : 0 < ε) :
    boxOuterMeasure (d + 1) (Set.Icc a b) ≤
      ENNReal.ofReal (∏ i : Fin (d + 1), ((b i - a i) + 2 * ε)) := by
  have hLowerUpper : ∀ i : Fin (d + 1), a i - ε ≤ b i + ε := by
    intro i
    linarith [h i, hε]
  let EpsBox : OpenBox (d + 1) := {
    lower := fun i => a i - ε
    upper := fun i => b i + ε
    lower_le_upper := hLowerUpper
  }
  let Z : OpenBox (d + 1) := helperForProposition_7_1_zeroVolumeOpenBox d
  let C : ℕ → OpenBox (d + 1) := fun j => if j = 0 then EpsBox else Z
  have hcoverC : IsCoveredByBoxes (Set.Icc a b) C := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨0, ?_⟩
    have hxInEps : x ∈ EpsBox.toSet := by
      intro i
      have hleft : a i ≤ x i := hx.1 i
      have hright : x i ≤ b i := hx.2 i
      have hltLeft : a i - ε < x i := by
        linarith [hleft, hε]
      have hltRight : x i < b i + ε := by
        linarith [hright, hε]
      exact ⟨hltLeft, hltRight⟩
    simpa [C] using hxInEps
  have hEpsVolume :
      EpsBox.volume = ∏ i : Fin (d + 1), ((b i - a i) + 2 * ε) := by
    unfold OpenBox.volume
    refine Finset.prod_congr rfl ?_
    intro i hi
    ring
  have hsumC :
      (∑' j, ENNReal.ofReal ((C j).volume)) =
        ENNReal.ofReal (∏ i : Fin (d + 1), ((b i - a i) + 2 * ε)) := by
    rw [tsum_eq_single 0]
    · simp [C, Z, hEpsVolume]
    · intro j hj
      simp [C, hj, Z, helperForProposition_7_1_zeroVolumeOpenBox_volume]
  have hCoverCostUpper :
      boxOuterMeasureCoverCost (d + 1) (Set.Icc a b) ≤
        ENNReal.ofReal (∏ i : Fin (d + 1), ((b i - a i) + 2 * ε)) := by
    by_cases hIcc : Set.Icc a b = ∅
    · simp [boxOuterMeasureCoverCost, hIcc]
    · simp only [boxOuterMeasureCoverCost, hIcc]
      refine sInf_le ?_
      exact ⟨C, hcoverC, hsumC.symm⟩
  have hOfLe :
      boxOuterMeasure (d + 1) (Set.Icc a b) ≤
        boxOuterMeasureCoverCost (d + 1) (Set.Icc a b) := by
    simpa [boxOuterMeasure] using
      (MeasureTheory.OuterMeasure.ofFunction_le
        (m := boxOuterMeasureCoverCost (d + 1))
        (m_empty := boxOuterMeasureCoverCost_empty (d + 1))
        (s := Set.Icc a b))
  exact le_trans hOfLe hCoverCostUpper

/-- Helper for Proposition 7.2: removing the thickening parameter yields the sharp
closed-box upper bound for `boxOuterMeasure` in positive dimension. -/
lemma helperForProposition_7_2_closedBox_outer_le_volume
    {d : ℕ} (a b : Fin (d + 1) → ℝ) (h : ∀ i, a i ≤ b i) :
    boxOuterMeasure (d + 1) (Set.Icc a b) ≤
      ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro η hη _hfinite
  let f : ℝ → ℝ := fun t => ∏ i : Fin (d + 1), ((b i - a i) + 2 * t)
  have hfCont : Continuous f := by
    continuity
  have hηReal : 0 < (η : ℝ) := by
    exact_mod_cast hη
  have hMetricCont : ∀ ε' > 0, ∃ δ > 0, ∀ x : ℝ, dist x 0 < δ → dist (f x) (f 0) < ε' :=
    Metric.continuousAt_iff.mp hfCont.continuousAt
  rcases hMetricCont (η : ℝ) hηReal with ⟨δ, hδPos, hδClose⟩
  have hHalfPos : 0 < δ / 2 := by
    linarith
  have hHalfLt : dist (δ / 2) 0 < δ := by
    have hDistEq : dist (δ / 2) 0 = δ / 2 := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hHalfPos]
    rw [hDistEq]
    linarith
  have hDistBound : dist (f (δ / 2)) (f 0) < (η : ℝ) := hδClose (δ / 2) hHalfLt
  have hRealLe : f (δ / 2) ≤ f 0 + (η : ℝ) := by
    have hAbsLe : |f (δ / 2) - f 0| < (η : ℝ) := by
      simpa [Real.dist_eq] using hDistBound
    linarith [abs_lt.mp hAbsLe |>.2]
  have hOuterLeThick :
      boxOuterMeasure (d + 1) (Set.Icc a b) ≤ ENNReal.ofReal (f (δ / 2)) := by
    simpa [f] using
      helperForProposition_7_2_closedBox_outer_le_thickened
        (a := a) (b := b) h (ε := δ / 2) hHalfPos
  have hProdNonneg : 0 ≤ ∏ i : Fin (d + 1), (b i - a i) := by
    refine Finset.prod_nonneg ?_
    intro i hi
    exact sub_nonneg.mpr (h i)
  have hOfRealLe :
      ENNReal.ofReal (f (δ / 2)) ≤
        ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) + η := by
    have hRealLe' :
        f (δ / 2) ≤ (∏ i : Fin (d + 1), (b i - a i)) + (η : ℝ) := by
      simpa [f] using hRealLe
    calc
      ENNReal.ofReal (f (δ / 2))
          ≤ ENNReal.ofReal ((∏ i : Fin (d + 1), (b i - a i)) + (η : ℝ)) :=
            ENNReal.ofReal_le_ofReal hRealLe'
      _ = ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) + η := by
            simpa using
              (ENNReal.ofReal_add hProdNonneg (show 0 ≤ (η : ℝ) by exact η.2))
  exact le_trans hOuterLeThick hOfRealLe

/-- Proposition 7.2 (Outer measure of a closed box, positive dimension): if
`B = ∏ i, [a i, b i] ⊆ ℝ^n` with `0 < n` and `a i ≤ b i` for all `i`,
then the box outer measure satisfies `m*(B) = ∏ i, (b i - a i)`. -/
theorem proposition_7_2
    (n : ℕ) (_hn : 0 < n) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i)) := by
  rcases helperForProposition_7_2_positiveDim_eq_succ _hn with ⟨d, hd⟩
  subst hd
  exact le_antisymm
    (helperForProposition_7_2_closedBox_outer_le_volume (a := a) (b := b) h)
    (helperForProposition_7_2_closedBox_outer_ge_volume (a := a) (b := b) h)

/-- Helper for Theorem 7.2: in dimension `0`, strict order between functions is impossible. -/
lemma helperForTheorem_7_2_zeroDim_not_lt (a b : Fin 0 → ℝ) : ¬ a < b := by
  intro hlt
  have hab : a = b := by
    funext i
    exact Fin.elim0 i
  exact lt_irrefl b (hab ▸ hlt)

/-- Helper for Theorem 7.2: in dimension `0`, every open box `Set.Ioo a b` is empty. -/
lemma helperForTheorem_7_2_zeroDim_Ioo_eq_empty (a b : Fin 0 → ℝ) :
    (Set.Ioo a b : Set (Fin 0 → ℝ)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact (helperForTheorem_7_2_zeroDim_not_lt (a := a) (b := x) hx.1).elim
  · intro hx
    exact False.elim (Set.notMem_empty x hx)

/-- Helper for Theorem 7.2: in dimension `0`, the open-box outer measure is zero. -/
lemma helperForTheorem_7_2_zeroDim_outer_eq_zero (a b : Fin 0 → ℝ) :
    (boxOuterMeasure 0) (Set.Ioo a b) = (0 : ENNReal) := by
  simp

/-- Helper for Theorem 7.2: in dimension `0`, the right-hand side product equals one. -/
lemma helperForTheorem_7_2_zeroDim_rhs_eq_one (a b : Fin 0 → ℝ) :
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) = (1 : ENNReal) := by
  simp

/-- Helper for Theorem 7.2: in dimension `0`, the left side is strictly smaller than
the right side in the target equality. -/
lemma helperForTheorem_7_2_zeroDim_outer_lt_rhs (a b : Fin 0 → ℝ) :
    (boxOuterMeasure 0) (Set.Ioo a b) < ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  calc
    (boxOuterMeasure 0) (Set.Ioo a b) = (0 : ENNReal) :=
      helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)
    _ < (1 : ENNReal) := by simp
    _ = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
      (helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)).symm

/-- Helper for Theorem 7.2: in dimension `0`, the right-hand side minus the left-hand
side equals `1`, quantitatively witnessing the gap in the target formula. -/
lemma helperForTheorem_7_2_zeroDim_rhs_sub_outer_eq_one (a b : Fin 0 → ℝ) :
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) -
      (boxOuterMeasure 0) (Set.Ioo a b) = (1 : ENNReal) := by
  calc
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) - (boxOuterMeasure 0) (Set.Ioo a b)
        = (1 : ENNReal) - (0 : ENNReal) := by
          rw [helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b),
            helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)]
    _ = (1 : ENNReal) := by simp

/-- Helper for Theorem 7.2: in dimension `0`, the right-hand side product is nonzero. -/
lemma helperForTheorem_7_2_zeroDim_rhs_ne_zero (a b : Fin 0 → ℝ) :
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) ≠ (0 : ENNReal) := by
  rw [helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)]
  exact one_ne_zero

/-- Helper for Theorem 7.2: in dimension `0`, the target equality is equivalent
to the right-hand side being `0`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_iff_rhs_eq_zero (a b : Fin 0 → ℝ) :
    ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) ↔
      (ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) = (0 : ENNReal)) := by
  constructor
  · intro hEq
    calc
      ENNReal.ofReal (∏ i : Fin 0, (b i - a i))
          = (boxOuterMeasure 0) (Set.Ioo a b) := hEq.symm
      _ = 0 := helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)
  · intro hRhsZero
    calc
      (boxOuterMeasure 0) (Set.Ioo a b) = 0 :=
        helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)
      _ = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := hRhsZero.symm

/-- Helper for Theorem 7.2: the zero-dimensional specialization of the open-box
formula is false for the current outer-measure model. -/
lemma helperForTheorem_7_2_zeroDim_formula_false (a b : Fin 0 → ℝ) :
    (boxOuterMeasure 0) (Set.Ioo a b) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  exact ne_of_lt (helperForTheorem_7_2_zeroDim_outer_lt_rhs (a := a) (b := b))

/-- Helper for Theorem 7.2: there is an explicit zero-dimensional pair `(a, b)`
satisfying the order hypothesis while refuting the target open-box equality. -/
lemma helperForTheorem_7_2_zeroDim_counterexample :
    ∃ a b : Fin 0 → ℝ,
      (∀ i : Fin 0, a i ≤ b i) ∧
      ((boxOuterMeasure 0) (Set.Ioo a b) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  let a : Fin 0 → ℝ := fun i => Fin.elim0 i
  let b : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨a, b, ?_⟩
  constructor
  · intro i
    exact Fin.elim0 i
  · exact helperForTheorem_7_2_zeroDim_formula_false (a := a) (b := b)

/-- Helper for Theorem 7.2: any claimed zero-dimensional open-box equality yields a
contradiction in the current normalization. -/
lemma helperForTheorem_7_2_zeroDim_eq_implies_false
    (a b : Fin 0 → ℝ)
    (hEq : (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    False := by
  exact (helperForTheorem_7_2_zeroDim_formula_false (a := a) (b := b)) hEq

/-- Helper for Theorem 7.2: in dimension `0`, the hypothesis `a i ≤ b i` is vacuous. -/
lemma helperForTheorem_7_2_zeroDim_le_vacuous (a b : Fin 0 → ℝ) :
    ∀ i : Fin 0, a i ≤ b i := by
  intro i
  exact Fin.elim0 i

/-- Helper for Theorem 7.2: in dimension `0`, the coordinatewise order hypothesis
is equivalent to `True`. -/
lemma helperForTheorem_7_2_zeroDim_le_iff_true (a b : Fin 0 → ℝ) :
    (∀ i : Fin 0, a i ≤ b i) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact helperForTheorem_7_2_zeroDim_le_vacuous (a := a) (b := b)

/-- Helper for Theorem 7.2: in dimension `0`, a formula claiming the target open-box
equality for every pair `(a, b)` is inconsistent with the model. -/
lemma helperForTheorem_7_2_zeroDim_forallAB_formula_false :
    ¬ (∀ a b : Fin 0 → ℝ, (∀ i : Fin 0, a i ≤ b i) →
      (boxOuterMeasure 0 (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)))) := by
  intro hAll
  rcases helperForTheorem_7_2_zeroDim_counterexample with ⟨a, b, hLe, hNe⟩
  exact hNe (hAll a b hLe)

/-- Helper for Theorem 7.2: any fully quantified open-box formula forces
`(0 : ENNReal) = 1` by specializing to dimension `0`. -/
lemma helperForTheorem_7_2_global_formula_implies_zero_eq_one
    (hAll : ∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (0 : ENNReal) = 1 := by
  let a : Fin 0 → ℝ := fun i => Fin.elim0 i
  let b : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hEqZero :
      (boxOuterMeasure 0) (Set.Ioo a b) =
        ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
    hAll 0 a b (helperForTheorem_7_2_zeroDim_le_vacuous (a := a) (b := b))
  calc
    (0 : ENNReal) = (boxOuterMeasure 0) (Set.Ioo a b) :=
      (helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)).symm
    _ = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := hEqZero
    _ = 1 := helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)

/-- Helper for Theorem 7.2: the fully quantified open-box formula is impossible in
the current model because the `n = 0` instance contradicts `0 ≠ 1`. -/
lemma helperForTheorem_7_2_global_formula_false :
    ¬ (∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hAll
  exact helperForTheorem_7_2_zeroDim_forallAB_formula_false (fun a b hab => hAll 0 a b hab)

/-- Helper for Theorem 7.2: in positive dimension, the self-difference product vanishes. -/
lemma helperForTheorem_7_2_positiveDim_selfSub_prod_eq_zero
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ENNReal.ofReal (∏ i, (a i - a i)) = 0 := by
  rcases helperForProposition_7_2_positiveDim_eq_succ hn with ⟨d, hd⟩
  subst hd
  simp

/-- Helper for Theorem 7.2: in positive dimension, each singleton has `boxOuterMeasure` zero. -/
lemma helperForTheorem_7_2_positiveDim_singleton_outer_eq_zero
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    boxOuterMeasure n ({x} : Set (Fin n → ℝ)) = 0 := by
  have hIcc : ({x} : Set (Fin n → ℝ)) = Set.Icc x x := by
    simpa using (Set.Icc_self x).symm
  calc
    boxOuterMeasure n ({x} : Set (Fin n → ℝ))
        = boxOuterMeasure n (Set.Icc x x) := by rw [hIcc]
    _ = ENNReal.ofReal (∏ i, (x i - x i)) := by
      exact proposition_7_2 n hn x x (fun i => le_rfl)
    _ = 0 := helperForTheorem_7_2_positiveDim_selfSub_prod_eq_zero hn x

/-- Helper for Theorem 7.2: in positive dimension, removing the two endpoints
`a` and `b` costs zero outer measure. -/
lemma helperForTheorem_7_2_positiveDim_endpoints_outer_eq_zero
    {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) :
    boxOuterMeasure n (({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ))) = 0 := by
  have hA : boxOuterMeasure n ({a} : Set (Fin n → ℝ)) = 0 :=
    helperForTheorem_7_2_positiveDim_singleton_outer_eq_zero hn a
  have hB : boxOuterMeasure n ({b} : Set (Fin n → ℝ)) = 0 :=
    helperForTheorem_7_2_positiveDim_singleton_outer_eq_zero hn b
  have hUnionLe :
      boxOuterMeasure n (({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ))) ≤
        boxOuterMeasure n ({a} : Set (Fin n → ℝ)) +
          boxOuterMeasure n ({b} : Set (Fin n → ℝ)) :=
    MeasureTheory.measure_union_le (μ := boxOuterMeasure n)
      ({a} : Set (Fin n → ℝ)) ({b} : Set (Fin n → ℝ))
  have hUnionLeZero :
      boxOuterMeasure n (({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ))) ≤ 0 := by
    simpa [hA, hB] using hUnionLe
  exact le_antisymm hUnionLeZero bot_le

/-- Helper for Theorem 7.2: every point of `Set.Icc a b` is either in `Set.Ioo a b`
or is one of the two endpoints. -/
lemma helperForTheorem_7_2_Icc_subset_Ioo_union_endpoints
    {n : ℕ} (a b : Fin n → ℝ) :
    Set.Icc a b ⊆ Set.Ioo a b ∪ (({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ))) := by
  intro x hxIcc
  by_cases hxEnds : x ∈ (({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ)))
  · exact Or.inr hxEnds
  · have hax : a ≤ x := hxIcc.1
    have hxb : x ≤ b := hxIcc.2
    have hx_ne_a : x ≠ a := by
      intro hxa
      exact hxEnds (Or.inl hxa)
    have hx_ne_b : x ≠ b := by
      intro hxbEq
      exact hxEnds (Or.inr hxbEq)
    have ha_ne_x : a ≠ x := by
      simpa [eq_comm] using hx_ne_a
    have hax_lt : a < x := lt_of_le_of_ne hax ha_ne_x
    have hxb_lt : x < b := lt_of_le_of_ne hxb hx_ne_b
    exact Or.inl ⟨hax_lt, hxb_lt⟩

/-- Helper for Theorem 7.2: monotonicity gives the easy inequality
`boxOuterMeasure n (Set.Ioo a b) ≤ boxOuterMeasure n (Set.Icc a b)`. -/
lemma helperForTheorem_7_2_outer_Ioo_le_outer_Icc
    {n : ℕ} (a b : Fin n → ℝ) :
    boxOuterMeasure n (Set.Ioo a b) ≤ boxOuterMeasure n (Set.Icc a b) := by
  exact (boxOuterMeasure n).mono Set.Ioo_subset_Icc_self

/-- Helper for Theorem 7.2: in positive dimension, `Set.Ioo a b` and `Set.Icc a b`
have the same box outer measure. -/
lemma helperForTheorem_7_2_positiveDim_outer_Ioo_eq_outer_Icc
    {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) :
    boxOuterMeasure n (Set.Ioo a b) = boxOuterMeasure n (Set.Icc a b) := by
  let E : Set (Fin n → ℝ) := ({a} : Set (Fin n → ℝ)) ∪ ({b} : Set (Fin n → ℝ))
  have hIooLeIcc :
      boxOuterMeasure n (Set.Ioo a b) ≤ boxOuterMeasure n (Set.Icc a b) :=
    helperForTheorem_7_2_outer_Ioo_le_outer_Icc (a := a) (b := b)
  have hIccSubset :
      Set.Icc a b ⊆ Set.Ioo a b ∪ E := by
    intro x hx
    have hx' :=
      helperForTheorem_7_2_Icc_subset_Ioo_union_endpoints (a := a) (b := b) hx
    simpa [E] using hx'
  have hIccLeUnion :
      boxOuterMeasure n (Set.Icc a b) ≤
        boxOuterMeasure n (Set.Ioo a b ∪ E) :=
    (boxOuterMeasure n).mono hIccSubset
  have hUnionLe :
      boxOuterMeasure n (Set.Ioo a b ∪ E) ≤
        boxOuterMeasure n (Set.Ioo a b) + boxOuterMeasure n E :=
    MeasureTheory.measure_union_le (μ := boxOuterMeasure n) (Set.Ioo a b) E
  have hEZero : boxOuterMeasure n E = 0 := by
    simpa [E] using
      helperForTheorem_7_2_positiveDim_endpoints_outer_eq_zero (hn := hn) (a := a) (b := b)
  have hIccLeIoo :
      boxOuterMeasure n (Set.Icc a b) ≤ boxOuterMeasure n (Set.Ioo a b) := by
    calc
      boxOuterMeasure n (Set.Icc a b)
          ≤ boxOuterMeasure n (Set.Ioo a b ∪ E) :=
            hIccLeUnion
      _ ≤ boxOuterMeasure n (Set.Ioo a b) + boxOuterMeasure n E := hUnionLe
      _ = boxOuterMeasure n (Set.Ioo a b) := by simp [hEZero]
  exact le_antisymm hIooLeIcc hIccLeIoo

/-- Helper for Theorem 7.2: the open-box outer-measure formula holds in positive dimension. -/
lemma helperForTheorem_7_2_positiveDim_openBox_eq
    {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i)) := by
  calc
    boxOuterMeasure n (Set.Ioo a b) = boxOuterMeasure n (Set.Icc a b) :=
      helperForTheorem_7_2_positiveDim_outer_Ioo_eq_outer_Icc (hn := hn) (a := a) (b := b)
    _ = ENNReal.ofReal (∏ i, (b i - a i)) := proposition_7_2 n hn a b h

/-- Helper for Theorem 7.2: in dimension `0`, the target open-box equality is
equivalent to the impossible equality `0 = 1` in `ENNReal`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_iff_zero_eq_one (a b : Fin 0 → ℝ) :
    ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) ↔
      ((0 : ENNReal) = 1) := by
  constructor
  · intro hEq
    calc
      (0 : ENNReal) = (boxOuterMeasure 0) (Set.Ioo a b) :=
        (helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)).symm
      _ = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := hEq
      _ = 1 := helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)
  · intro hZeroOne
    calc
      (boxOuterMeasure 0) (Set.Ioo a b) = 0 :=
        helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)
      _ = 1 := hZeroOne
      _ = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
        (helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)).symm

/-- Helper for Theorem 7.2: in dimension `0`, the target open-box equality is equivalent to `False`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_iff_false (a b : Fin 0 → ℝ) :
    ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) ↔ False := by
  constructor
  · intro hEq
    have hZeroOne : (0 : ENNReal) = 1 := by
      exact (helperForTheorem_7_2_zeroDim_targetEq_iff_zero_eq_one (a := a) (b := b)).mp hEq
    exact zero_ne_one hZeroOne
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.2: in dimension `0`, any proof of the target equality
forces the contradictory identity `0 = 1` in `ENNReal`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_implies_zero_eq_one (a b : Fin 0 → ℝ)
    (hEq : (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    (0 : ENNReal) = 1 := by
  exact (helperForTheorem_7_2_zeroDim_targetEq_iff_zero_eq_one (a := a) (b := b)).mp hEq

/-- Helper for Theorem 7.2: in dimension `0`, any proof of the target equality
forces the quantitative gap `rhs - lhs` to be simultaneously `0` and `1`,
hence impossible. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_implies_false_via_sub
    (a b : Fin 0 → ℝ)
    (hEq : (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    False := by
  have hSubZero :
      ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) - (boxOuterMeasure 0) (Set.Ioo a b) = 0 := by
    rw [← hEq, tsub_self]
  have hSubOne :
      ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) - (boxOuterMeasure 0) (Set.Ioo a b) = 1 :=
    helperForTheorem_7_2_zeroDim_rhs_sub_outer_eq_one (a := a) (b := b)
  have hZeroEqOne : (0 : ENNReal) = 1 := by
    calc
      (0 : ENNReal) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) - (boxOuterMeasure 0) (Set.Ioo a b) :=
        hSubZero.symm
      _ = 1 := hSubOne
  exact zero_ne_one hZeroEqOne

/-- Helper for Theorem 7.2: in dimension `0`, the target equality is refutable. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_not (a b : Fin 0 → ℝ) :
    ¬ ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hEq
  have hRhsZero :
      ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) = (0 : ENNReal) :=
    (helperForTheorem_7_2_zeroDim_targetEq_iff_rhs_eq_zero (a := a) (b := b)).mp hEq
  exact helperForTheorem_7_2_zeroDim_rhs_ne_zero (a := a) (b := b) hRhsZero

/-- Helper for Theorem 7.2: even with the vacuous order hypothesis in dimension
`0`, the target open-box equality cannot be obtained. -/
lemma helperForTheorem_7_2_zeroDim_hypothesis_does_not_rescue_target
    (a b : Fin 0 → ℝ) :
    ¬ ((∀ i : Fin 0, a i ≤ b i) →
      ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)))) := by
  intro hImp
  have hLe : ∀ i : Fin 0, a i ≤ b i :=
    helperForTheorem_7_2_zeroDim_le_vacuous (a := a) (b := b)
  exact helperForTheorem_7_2_zeroDim_targetEq_not (a := a) (b := b) (hImp hLe)

/-- Helper for Theorem 7.2: in dimension `0`, combining the vacuous order
hypothesis with the target equality yields a contradiction. -/
lemma helperForTheorem_7_2_zeroDim_le_and_targetEq_implies_false
    (a b : Fin 0 → ℝ)
    (hLe : ∀ i : Fin 0, a i ≤ b i)
    (hEq : (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    False := by
  have hImp :
      (∀ i : Fin 0, a i ≤ b i) →
        ((boxOuterMeasure 0) (Set.Ioo a b) =
          ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
    intro _
    exact hEq
  have hEqFromLe :
      (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
    hImp hLe
  exact helperForTheorem_7_2_zeroDim_targetEq_not (a := a) (b := b) hEqFromLe

/-- Helper for Theorem 7.2: in dimension `0`, under the order hypothesis,
the target open-box equality is equivalent to `False`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_iff_false_of_le
    (a b : Fin 0 → ℝ) (h : ∀ i : Fin 0, a i ≤ b i) :
    ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) ↔ False := by
  constructor
  · intro hEq
    exact helperForTheorem_7_2_zeroDim_le_and_targetEq_implies_false (a := a) (b := b) h hEq
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.2: in dimension `0`, the order hypothesis implies the
target open-box equality is impossible. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_not_of_le
    (a b : Fin 0 → ℝ) (h : ∀ i : Fin 0, a i ≤ b i) :
    ¬ ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hEq
  exact (helperForTheorem_7_2_zeroDim_targetEq_iff_false_of_le (a := a) (b := b) h).mp hEq

/-- Helper for Theorem 7.2: in dimension `0`, the conjunction of the order
hypothesis and the target equality is equivalent to `False`. -/
lemma helperForTheorem_7_2_zeroDim_le_and_targetEq_iff_false
    (a b : Fin 0 → ℝ) :
    ((∀ i : Fin 0, a i ≤ b i) ∧
      ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)))) ↔
      False := by
  constructor
  · intro hPair
    exact helperForTheorem_7_2_zeroDim_le_and_targetEq_implies_false
      (a := a) (b := b) hPair.1 hPair.2
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.2: in dimension `0`, no pair of endpoints can satisfy
both the order hypothesis and the target equality. -/
lemma helperForTheorem_7_2_zeroDim_no_box_satisfies_hypothesis_and_targetEq :
    ¬ ∃ a b : Fin 0 → ℝ,
      (∀ i : Fin 0, a i ≤ b i) ∧
      ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hExists
  rcases hExists with ⟨a, b, hPair⟩
  exact (helperForTheorem_7_2_zeroDim_le_and_targetEq_iff_false (a := a) (b := b)).mp hPair

/-- Helper for Theorem 7.2: for fixed `a, b : Fin 0 → ℝ`, there is no witness
`h : ∀ i, a i ≤ b i` for which the target open-box equality holds. -/
lemma helperForTheorem_7_2_zeroDim_no_hypothesis_witness_for_targetEq
    (a b : Fin 0 → ℝ) :
    ¬ ∃ _h : ∀ i : Fin 0, a i ≤ b i,
      ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hExists
  rcases hExists with ⟨hLe, hEq⟩
  exact helperForTheorem_7_2_zeroDim_targetEq_not_of_le (a := a) (b := b) (h := hLe) hEq

/-- Helper for Theorem 7.2: in dimension `0`, once witness nonexistence is known,
any fixed order hypothesis immediately rules out the target equality. -/
lemma helperForTheorem_7_2_zeroDim_not_targetEq_of_noWitness
    (a b : Fin 0 → ℝ)
    (h : ∀ i : Fin 0, a i ≤ b i)
    (hNoWitness :
      ¬ ∃ _h' : ∀ i : Fin 0, a i ≤ b i,
        ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)))) :
    ¬ ((boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hEq
  exact hNoWitness ⟨h, hEq⟩

/-- Helper for Theorem 7.2: any proof of the fully quantified open-box formula
immediately yields a contradiction in this model. -/
lemma helperForTheorem_7_2_universal_target_statement_implies_false
    (hAll : ∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact helperForTheorem_7_2_global_formula_false hAll

/-- Helper for Theorem 7.2: in dimension `0`, any proof of the target equality
forces the contradiction `(1 : ENNReal) = 0`. -/
lemma helperForTheorem_7_2_zeroDim_targetEq_implies_one_eq_zero
    (a b : Fin 0 → ℝ)
    (hEq : (boxOuterMeasure 0) (Set.Ioo a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    (1 : ENNReal) = 0 := by
  rw [← helperForTheorem_7_2_zeroDim_rhs_eq_one (a := a) (b := b)]
  rw [hEq.symm]
  exact helperForTheorem_7_2_zeroDim_outer_eq_zero (a := a) (b := b)

/-- Helper for Theorem 7.2: the fully quantified open-box target statement is
false in this model. -/
lemma helperForTheorem_7_2_universal_target_statement_not :
    ¬ (∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hAll
  exact helperForTheorem_7_2_universal_target_statement_implies_false hAll

/-- Helper for Theorem 7.2: if the ambient dimension is identified with `0`,
the target open-box equality is impossible under the coordinatewise order
hypothesis. -/
lemma helperForTheorem_7_2_targetEq_not_of_eq_zero_dim
    {n : ℕ} (hn : n = 0) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    ¬ (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  subst hn
  exact helperForTheorem_7_2_zeroDim_targetEq_not_of_le (a := a) (b := b) (h := h)

/-- Helper for Theorem 7.2: if the ambient dimension is not positive, then in fact
the left side is strictly smaller than the right side in the target formula. -/
lemma helperForTheorem_7_2_targetLt_of_not_pos_dim
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) :
    boxOuterMeasure n (Set.Ioo a b) < ENNReal.ofReal (∏ i, (b i - a i)) := by
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst hn0
  exact helperForTheorem_7_2_zeroDim_outer_lt_rhs (a := a) (b := b)

/-- Helper for Theorem 7.2: in nonpositive dimension, the quantitative gap
`rhs - lhs` in the target formula equals `1`. -/
lemma helperForTheorem_7_2_target_rhs_sub_outer_eq_one_of_not_pos_dim
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) :
    ENNReal.ofReal (∏ i, (b i - a i)) - boxOuterMeasure n (Set.Ioo a b) = (1 : ENNReal) := by
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst hn0
  exact helperForTheorem_7_2_zeroDim_rhs_sub_outer_eq_one (a := a) (b := b)

/-- Helper for Theorem 7.2: in nonpositive dimension, the quantitative gap
`rhs - lhs` in the target formula is nonzero. -/
lemma helperForTheorem_7_2_target_rhs_sub_outer_ne_zero_of_not_pos_dim
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) :
    ENNReal.ofReal (∏ i, (b i - a i)) - boxOuterMeasure n (Set.Ioo a b) ≠ 0 := by
  rw [helperForTheorem_7_2_target_rhs_sub_outer_eq_one_of_not_pos_dim
    (hn := hn) (a := a) (b := b)]
  exact one_ne_zero

/-- Helper for Theorem 7.2: in nonpositive dimension, any claimed target equality
forces a contradiction via `rhs - lhs = 0` versus `rhs - lhs = 1`. -/
lemma helperForTheorem_7_2_targetEq_implies_false_of_not_pos_dim_via_sub
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ)
    (hEq : boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  have hSubZero :
      ENNReal.ofReal (∏ i, (b i - a i)) - boxOuterMeasure n (Set.Ioo a b) = 0 := by
    rw [← hEq, tsub_self]
  have hSubOne :
      ENNReal.ofReal (∏ i, (b i - a i)) - boxOuterMeasure n (Set.Ioo a b) = 1 :=
    helperForTheorem_7_2_target_rhs_sub_outer_eq_one_of_not_pos_dim
      (hn := hn) (a := a) (b := b)
  have hZeroEqOne : (0 : ENNReal) = 1 := by
    calc
      (0 : ENNReal) =
          ENNReal.ofReal (∏ i, (b i - a i)) - boxOuterMeasure n (Set.Ioo a b) :=
        hSubZero.symm
      _ = 1 := hSubOne
  exact zero_ne_one hZeroEqOne

/-- Helper for Theorem 7.2: if the ambient dimension is not positive, then the
target open-box equality is impossible under the coordinatewise order
hypothesis. -/
lemma helperForTheorem_7_2_targetEq_not_of_not_pos_dim
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    ¬ (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  let _ := h
  intro hEq
  exact helperForTheorem_7_2_targetEq_implies_false_of_not_pos_dim_via_sub
    (hn := hn) (a := a) (b := b) hEq

/-- Helper for Theorem 7.2: in nonpositive dimension, the order hypothesis and
the target open-box equality are jointly equivalent to `False`. -/
lemma helperForTheorem_7_2_not_pos_dim_le_and_targetEq_iff_false
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) :
    ((∀ i, a i ≤ b i) ∧
      (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i)))) ↔ False := by
  constructor
  · intro hPair
    exact (helperForTheorem_7_2_targetEq_not_of_not_pos_dim
      (hn := hn) (a := a) (b := b) (h := hPair.1)) hPair.2
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.2: in nonpositive dimension, there is no order-hypothesis
`h` witnessing the target open-box equality. -/
lemma helperForTheorem_7_2_not_pos_dim_no_hypothesis_witness_for_targetEq
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) :
    ¬ ∃ _h : ∀ i, a i ≤ b i,
      (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hExists
  rcases hExists with ⟨hLe, hEq⟩
  exact (helperForTheorem_7_2_not_pos_dim_le_and_targetEq_iff_false
    (hn := hn) (a := a) (b := b)).mp ⟨hLe, hEq⟩

/-- Helper for Theorem 7.2: for fixed endpoints satisfying the order hypothesis,
the target open-box equality holds exactly in positive dimension. -/
lemma helperForTheorem_7_2_targetEq_iff_pos_dim
    {n : ℕ} (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) ↔ 0 < n := by
  constructor
  · intro hEq
    by_contra hn
    exact (helperForTheorem_7_2_targetEq_not_of_not_pos_dim
      (hn := hn) (a := a) (b := b) (h := h)) hEq
  · intro hn
    exact helperForTheorem_7_2_positiveDim_openBox_eq (hn := hn) (a := a) (b := b) h

/-- Helper for Theorem 7.2: in nonpositive dimension, the target open-box
equality is equivalent to `False`. -/
lemma helperForTheorem_7_2_targetEq_iff_false_of_not_pos_dim
    {n : ℕ} (hn : ¬ 0 < n) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    (boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i))) ↔ False := by
  constructor
  · intro hEq
    exact (helperForTheorem_7_2_targetEq_not_of_not_pos_dim
      (hn := hn) (a := a) (b := b) (h := h)) hEq
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.2: a nonpositive ambient dimension must be zero. -/
lemma helperForTheorem_7_2_dim_eq_zero_of_not_pos
    {n : ℕ} (hn : ¬ 0 < n) : n = 0 := by
  exact Nat.eq_zero_of_not_pos hn

/-- Helper for Theorem 7.2: corrected positive-dimensional form of the open-box
outer-measure identity. -/
theorem boxOuterMeasure_openBox_eq_posDim
    (n : ℕ) (a b : Fin n → ℝ) (hn : 0 < n) (h : ∀ i, a i ≤ b i) :
    boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i)) := by
  exact helperForTheorem_7_2_positiveDim_openBox_eq (hn := hn) (a := a) (b := b) h

/-- Theorem 7.2 (Outer measure of an open box): in positive dimension and under
`a i ≤ b i`, the open box `∏ i, (a i, b i) ⊆ ℝ^n` has outer measure
`∏ i, (b i - a i)`. -/
theorem boxOuterMeasure_openBox_eq
    (n : ℕ) (a b : Fin n → ℝ) (hn : 0 < n) (h : ∀ i, a i ≤ b i) :
    boxOuterMeasure n (Set.Ioo a b) = ENNReal.ofReal (∏ i, (b i - a i)) := by
  exact boxOuterMeasure_openBox_eq_posDim (n := n) (a := a) (b := b) (hn := hn) h

attribute [local instance] Classical.propDecidable

/-- Interval length on subsets of `ℝ`: for sets equal to an open interval `(a,b)`,
the value is `b - a`, and it is `+∞` otherwise. -/
noncomputable def intervalLength (s : Set ℝ) : ENNReal :=
  if hIoo : ∃ p : ℝ × ℝ, s = Set.Ioo p.1 p.2 then
    let p := Classical.choose hIoo
    ENNReal.ofReal (p.2 - p.1)
  else
    ⊤

/-- The interval-length function sends the empty set to zero. -/
lemma intervalLength_empty : intervalLength (∅ : Set ℝ) = 0 := by
  let hIoo : ∃ p : ℝ × ℝ, (∅ : Set ℝ) = Set.Ioo p.1 p.2 := ⟨(0, 0), by simp⟩
  rw [intervalLength, dif_pos hIoo]
  let p : ℝ × ℝ := Classical.choose hIoo
  have hp : (∅ : Set ℝ) = Set.Ioo p.1 p.2 := by
    simpa [p] using (Classical.choose_spec hIoo)
  have hle : p.2 ≤ p.1 := by
    exact not_lt.mp ((Set.Ioo_eq_empty_iff.mp hp.symm))
  have hnonpos : p.2 - p.1 ≤ 0 := sub_nonpos.mpr hle
  have hofReal : ENNReal.ofReal (p.2 - p.1) = 0 := ENNReal.ofReal_eq_zero.mpr hnonpos
  simpa [p] using hofReal

/-- The one-dimensional outer measure on `ℝ`, defined from open-interval length
as in the infimum-over-open-covers construction. -/
noncomputable def oneDimensionalOuterMeasure : MeasureTheory.OuterMeasure ℝ :=
  MeasureTheory.OuterMeasure.ofFunction intervalLength intervalLength_empty

/-- Helper for Proposition 7.3: the outer measure induced by Lebesgue volume on `ℝ`
is pointwise bounded above by `intervalLength`. -/
lemma helperForProposition_7_3_volume_le_intervalLength
    (s : Set ℝ) :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure s) ≤ intervalLength s := by
  by_cases hIoo : ∃ p : ℝ × ℝ, s = Set.Ioo p.1 p.2
  · let p : ℝ × ℝ := Classical.choose hIoo
    have hs : s = Set.Ioo p.1 p.2 := Classical.choose_spec hIoo
    have hEq : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure s) = intervalLength s := by
      calc
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure s)
            = ENNReal.ofReal (p.2 - p.1) := by
              rw [MeasureTheory.Measure.toOuterMeasure_apply, hs, Real.volume_Ioo]
        _ = intervalLength s := by
              rw [intervalLength, dif_pos hIoo]
    exact hEq.le
  · rw [intervalLength, dif_neg hIoo]
    exact le_top

/-- Helper for Proposition 7.3: the outer measure from Lebesgue volume is bounded
above by the one-dimensional interval-cover outer measure. -/
lemma helperForProposition_7_3_volumeOuter_le_oneDimOuter :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) ≤ oneDimensionalOuterMeasure := by
  rw [oneDimensionalOuterMeasure]
  exact (MeasureTheory.OuterMeasure.le_ofFunction).2
    helperForProposition_7_3_volume_le_intervalLength

/-- Helper for Proposition 7.3: Lebesgue volume viewed as an outer measure gives
infinite mass to `ℝ`. -/
lemma helperForProposition_7_3_volumeOuter_univ :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.univ : Set ℝ) = ⊤ := by
  rw [MeasureTheory.Measure.toOuterMeasure_apply, Real.volume_univ]

/-- Proposition 7.3: if `m*` denotes the one-dimensional outer measure on `ℝ`
defined by countable interval covers and interval length, then `m*(ℝ) = +∞`. -/
theorem proposition_7_3 :
    oneDimensionalOuterMeasure (Set.univ : Set ℝ) = ⊤ := by
  apply top_unique
  calc
    ⊤ = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure (Set.univ : Set ℝ)) := by
      symm
      exact helperForProposition_7_3_volumeOuter_univ
    _ ≤ oneDimensionalOuterMeasure (Set.univ : Set ℝ) :=
      helperForProposition_7_3_volumeOuter_le_oneDimOuter (Set.univ : Set ℝ)

/-- Helper for Proposition 7.4: `intervalLength` agrees with `Real.volume` on open intervals. -/
lemma helperForProposition_7_4_intervalLength_Ioo
    (a b : ℝ) :
    intervalLength (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  let hIoo : ∃ p : ℝ × ℝ, Set.Ioo a b = Set.Ioo p.1 p.2 := ⟨(a, b), rfl⟩
  let p : ℝ × ℝ := Classical.choose hIoo
  have hp : Set.Ioo a b = Set.Ioo p.1 p.2 := Classical.choose_spec hIoo
  calc
    intervalLength (Set.Ioo a b) = ENNReal.ofReal (p.2 - p.1) := by
      rw [intervalLength, dif_pos hIoo]
    _ = (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioo p.1 p.2) := by
      rw [Real.volume_Ioo]
    _ = (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioo a b) := by
      rw [← hp]
    _ = ENNReal.ofReal (b - a) := by
      rw [Real.volume_Ioo]

/-- Helper for Proposition 7.4: each singleton has arbitrarily small
one-dimensional outer-measure upper bounds. -/
lemma helperForProposition_7_4_singleton_outer_le_of_pos
    (x ε : ℝ) (hε : 0 < ε) :
    oneDimensionalOuterMeasure ({x} : Set ℝ) ≤ ENNReal.ofReal ε := by
  have hSubset : ({x} : Set ℝ) ⊆ Set.Ioo (x - ε / 2) (x + ε / 2) := by
    intro y hy
    have hyx : y = x := by simpa using hy
    subst hyx
    constructor <;> linarith
  have hMono :
      oneDimensionalOuterMeasure ({x} : Set ℝ) ≤
        oneDimensionalOuterMeasure (Set.Ioo (x - ε / 2) (x + ε / 2)) :=
    oneDimensionalOuterMeasure.mono hSubset
  have hOfFunctionLe :
      oneDimensionalOuterMeasure (Set.Ioo (x - ε / 2) (x + ε / 2)) ≤
        intervalLength (Set.Ioo (x - ε / 2) (x + ε / 2)) := by
    rw [oneDimensionalOuterMeasure]
    exact MeasureTheory.OuterMeasure.ofFunction_le
      (m := intervalLength) (m_empty := intervalLength_empty)
      (Set.Ioo (x - ε / 2) (x + ε / 2))
  have hInterval :
      intervalLength (Set.Ioo (x - ε / 2) (x + ε / 2)) = ENNReal.ofReal ε := by
    calc
      intervalLength (Set.Ioo (x - ε / 2) (x + ε / 2))
          = ENNReal.ofReal ((x + ε / 2) - (x - ε / 2)) :=
            helperForProposition_7_4_intervalLength_Ioo (x - ε / 2) (x + ε / 2)
      _ = ENNReal.ofReal ε := by
        congr 1
        ring
  exact le_trans hMono (hOfFunctionLe.trans_eq hInterval)

/-- Helper for Proposition 7.4: every singleton has zero one-dimensional outer measure. -/
lemma helperForProposition_7_4_singleton_outer_eq_zero
    (x : ℝ) :
    oneDimensionalOuterMeasure ({x} : Set ℝ) = 0 := by
  have hLeZero : oneDimensionalOuterMeasure ({x} : Set ℝ) ≤ 0 := by
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _hfinite
    have hεReal : (0 : ℝ) < ε := by
      exact_mod_cast hε
    have hLeEps :
        oneDimensionalOuterMeasure ({x} : Set ℝ) ≤ ENNReal.ofReal (ε : ℝ) :=
      helperForProposition_7_4_singleton_outer_le_of_pos x ε hεReal
    calc
      oneDimensionalOuterMeasure ({x} : Set ℝ) ≤ ENNReal.ofReal (ε : ℝ) := hLeEps
      _ = (ε : ENNReal) := by simp
      _ = (0 : ENNReal) + (ε : ENNReal) := by simp
  exact le_antisymm hLeZero bot_le

/-- Helper for Proposition 7.4: every countable subset of `ℝ` has zero
one-dimensional outer measure. -/
lemma helperForProposition_7_4_countable_outer_eq_zero
    (A : Set ℝ) (hA : A.Countable) :
    oneDimensionalOuterMeasure A = 0 := by
  refine (MeasureTheory.measure_null_iff_singleton
    (μ := oneDimensionalOuterMeasure) hA).2 ?_
  intro x hx
  exact helperForProposition_7_4_singleton_outer_eq_zero x

/-- Proposition 7.4: if `A ⊆ ℝ` is countable, then the one-dimensional Lebesgue outer
measure satisfies `m*(A) = 0`. In particular, `m*(ℚ) = 0`. -/
theorem proposition_7_4 :
    (∀ A : Set ℝ, A.Countable → oneDimensionalOuterMeasure A = 0) ∧
      oneDimensionalOuterMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
  constructor
  · intro A hA
    exact helperForProposition_7_4_countable_outer_eq_zero A hA
  · exact helperForProposition_7_4_countable_outer_eq_zero
      (Set.range ((↑) : ℚ → ℝ))
      (Set.countable_range (f := ((↑) : ℚ → ℝ)))


end Section02
end Chap07
