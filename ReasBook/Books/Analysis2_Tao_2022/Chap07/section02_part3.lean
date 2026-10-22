/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.section02_part2

open scoped BigOperators

section Chap07
section Section02

/-- Proposition 7.5: for the one-dimensional outer measure `m*` on `ℝ`,
`m*(ℝ \ ℚ) = +∞` and `m*([0,1] \ ℚ) = 1`. -/
theorem proposition_7_5 :
    oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Set.range ((↑) : ℚ → ℝ)) = ⊤ ∧
      oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Set.range ((↑) : ℚ → ℝ)) = 1 := by
  let Q : Set ℝ := Set.range ((↑) : ℚ → ℝ)
  have hCountQ : Q.Countable := by
    simpa [Q] using (Set.countable_range (f := ((↑) : ℚ → ℝ)))
  have hQZero : oneDimensionalOuterMeasure Q = 0 := by
    exact (proposition_7_4.1) Q hCountQ
  have hUnivDiffEqTop : oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) = ⊤ := by
    have hUnivUnion :
        ((Set.univ : Set ℝ) \ Q) ∪ ((Set.univ : Set ℝ) ∩ Q) = (Set.univ : Set ℝ) := by
      simpa using (Set.diff_union_inter (s := (Set.univ : Set ℝ)) (t := Q))
    have hUnivLe :
        oneDimensionalOuterMeasure (Set.univ : Set ℝ) ≤
          oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) +
            oneDimensionalOuterMeasure ((Set.univ : Set ℝ) ∩ Q) := by
      calc
        oneDimensionalOuterMeasure (Set.univ : Set ℝ)
            = oneDimensionalOuterMeasure (((Set.univ : Set ℝ) \ Q) ∪ ((Set.univ : Set ℝ) ∩ Q)) := by
              rw [hUnivUnion]
        _ ≤ oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) +
              oneDimensionalOuterMeasure ((Set.univ : Set ℝ) ∩ Q) :=
            MeasureTheory.measure_union_le
              (μ := oneDimensionalOuterMeasure) ((Set.univ : Set ℝ) \ Q) ((Set.univ : Set ℝ) ∩ Q)
    have hUnivLeDiff : oneDimensionalOuterMeasure (Set.univ : Set ℝ) ≤
        oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) := by
      calc
        oneDimensionalOuterMeasure (Set.univ : Set ℝ)
            ≤ oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) +
                oneDimensionalOuterMeasure ((Set.univ : Set ℝ) ∩ Q) := hUnivLe
        _ = oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) + oneDimensionalOuterMeasure Q := by
              simp
        _ = oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) + 0 := by
              rw [hQZero]
        _ = oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) := by
              simp
    have hTopLeDiff : (⊤ : ENNReal) ≤ oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) := by
      calc
        (⊤ : ENNReal) = oneDimensionalOuterMeasure (Set.univ : Set ℝ) := by
          symm
          exact proposition_7_3
        _ ≤ oneDimensionalOuterMeasure ((Set.univ : Set ℝ) \ Q) := hUnivLeDiff
    exact top_unique hTopLeDiff
  have hIccOuterEqOne : oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
    have hLower : (1 : ENNReal) ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) := by
      calc
        (1 : ENNReal)
            = (MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure (Set.Icc (0 : ℝ) 1) := by
              rw [MeasureTheory.Measure.toOuterMeasure_apply, Real.volume_Icc]
              norm_num
        _ ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) :=
          helperForProposition_7_3_volumeOuter_le_oneDimOuter (Set.Icc (0 : ℝ) 1)
    have hUpper : oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) ≤ 1 := by
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hε _hfinite
      have hεRealPos : (0 : ℝ) < ε := by
        exact_mod_cast hε
      have hIccSubset :
          Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2) := by
        intro x hx
        constructor
        · linarith [hx.1, hεRealPos]
        · linarith [hx.2, hεRealPos]
      have hMono :
          oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) ≤
            oneDimensionalOuterMeasure (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) :=
        oneDimensionalOuterMeasure.mono hIccSubset
      have hOfFunctionLe :
          oneDimensionalOuterMeasure (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) ≤
            intervalLength (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) := by
        rw [oneDimensionalOuterMeasure]
        exact MeasureTheory.OuterMeasure.ofFunction_le
          (m := intervalLength) (m_empty := intervalLength_empty)
          (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2))
      have hInterval :
          intervalLength (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) =
            ENNReal.ofReal (1 + (ε : ℝ)) := by
        calc
          intervalLength (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2))
              = ENNReal.ofReal ((1 + (ε : ℝ) / 2) - (-(ε : ℝ) / 2)) :=
                helperForProposition_7_4_intervalLength_Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)
          _ = ENNReal.ofReal (1 + (ε : ℝ)) := by
                congr 1
                ring
      have hRealNonneg : 0 ≤ (ε : ℝ) := by exact_mod_cast (show (0 : NNReal) ≤ ε from le_of_lt hε)
      have hOneNonneg : 0 ≤ (1 : ℝ) := by positivity
      have hAddOfReal :
          ENNReal.ofReal (1 + (ε : ℝ)) = (1 : ENNReal) + ε := by
        calc
          ENNReal.ofReal (1 + (ε : ℝ))
              = ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal (ε : ℝ) := by
                rw [ENNReal.ofReal_add hOneNonneg hRealNonneg]
          _ = (1 : ENNReal) + ENNReal.ofReal (ε : ℝ) := by simp
          _ = (1 : ENNReal) + ε := by simp
      calc
        oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1)
            ≤ oneDimensionalOuterMeasure (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) := hMono
        _ ≤ intervalLength (Set.Ioo (-(ε : ℝ) / 2) (1 + (ε : ℝ) / 2)) := hOfFunctionLe
        _ = ENNReal.ofReal (1 + (ε : ℝ)) := hInterval
        _ = (1 : ENNReal) + ε := hAddOfReal
    exact le_antisymm hUpper hLower
  have hIccRatInterZero :
      oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 ∩ Q) = 0 := by
    have hSubsetIccRat : Set.Icc (0 : ℝ) 1 ∩ Q ⊆ Q := by
      intro x hx
      exact hx.2
    have hCountIccRat : (Set.Icc (0 : ℝ) 1 ∩ Q).Countable := hCountQ.mono hSubsetIccRat
    exact (proposition_7_4.1) (Set.Icc (0 : ℝ) 1 ∩ Q) hCountIccRat
  have hIccDiffEqOne : oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) = 1 := by
    have hSubsetIccDiff : Set.Icc (0 : ℝ) 1 \ Q ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact hx.1
    have hUpper : oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) ≤ 1 := by
      calc
        oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q)
            ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) :=
              oneDimensionalOuterMeasure.mono hSubsetIccDiff
        _ = 1 := hIccOuterEqOne
    have hIccUnion :
        (Set.Icc (0 : ℝ) 1 \ Q) ∪ (Set.Icc (0 : ℝ) 1 ∩ Q) = Set.Icc (0 : ℝ) 1 := by
      simpa using (Set.diff_union_inter (s := Set.Icc (0 : ℝ) 1) (t := Q))
    have hIccLe :
        oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) ≤
          oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) +
            oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 ∩ Q) := by
      calc
        oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1)
            = oneDimensionalOuterMeasure ((Set.Icc (0 : ℝ) 1 \ Q) ∪ (Set.Icc (0 : ℝ) 1 ∩ Q)) := by
              rw [hIccUnion]
        _ ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) +
              oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 ∩ Q) :=
            MeasureTheory.measure_union_le
              (μ := oneDimensionalOuterMeasure) (Set.Icc (0 : ℝ) 1 \ Q) (Set.Icc (0 : ℝ) 1 ∩ Q)
    have hLower : (1 : ENNReal) ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) := by
      calc
        (1 : ENNReal) = oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1) := hIccOuterEqOne.symm
        _ ≤ oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) +
              oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 ∩ Q) := hIccLe
        _ = oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) + 0 := by
              rw [hIccRatInterZero]
        _ = oneDimensionalOuterMeasure (Set.Icc (0 : ℝ) 1 \ Q) := by
              simp
    exact le_antisymm hUpper hLower
  constructor
  · simpa [Q] using hUnivDiffEqTop
  · simpa [Q] using hIccDiffEqOne

/-- Helper for Proposition 7.6: identify the segment image with a product set. -/
lemma helperForProposition_7_6_segmentImage_eq_Icc_prodSingleton :
    ((fun x : ℝ => (x, (0 : ℝ))) '' Set.Icc (0 : ℝ) 1) =
      Set.Icc (0 : ℝ) 1 ×ˢ ({(0 : ℝ)} : Set ℝ) := by
  ext p
  rcases p with ⟨x, y⟩
  simp [Set.mem_prod, eq_comm]

/-- Helper for Proposition 7.6: identify the horizontal line as `univ × {0}`. -/
lemma helperForProposition_7_6_range_eq_univ_prodSingleton :
    Set.range (fun x : ℝ => (x, (0 : ℝ))) =
      Set.univ ×ˢ ({(0 : ℝ)} : Set ℝ) := by
  ext p
  rcases p with ⟨x, y⟩
  simp [Set.mem_prod, eq_comm]

/-- Helper for Proposition 7.6: every horizontal slice `s × {0}` has outer measure zero. -/
lemma helperForProposition_7_6_outerMeasure_prodSingleton_zero (s : Set ℝ) :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).toOuterMeasure)
      (s ×ˢ ({(0 : ℝ)} : Set ℝ)) = 0 := by
  rw [MeasureTheory.Measure.toOuterMeasure_apply]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.Measure.prod_prod]
  simp

/-- Proposition 7.6: for two-dimensional Lebesgue outer measure on `ℝ²`, the horizontal
segment `{(x,0) : 0 ≤ x ≤ 1}` has outer measure `0`; consequently the full horizontal line
`{(x,0) : x ∈ ℝ}` also has outer measure `0`. -/
theorem proposition_7_6 :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).toOuterMeasure)
        ((fun x : ℝ => (x, (0 : ℝ))) '' Set.Icc (0 : ℝ) 1) = 0 ∧
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).toOuterMeasure)
        (Set.range (fun x : ℝ => (x, (0 : ℝ)))) = 0 := by
  constructor
  · rw [helperForProposition_7_6_segmentImage_eq_Icc_prodSingleton]
    exact helperForProposition_7_6_outerMeasure_prodSingleton_zero (Set.Icc (0 : ℝ) 1)
  · rw [helperForProposition_7_6_range_eq_univ_prodSingleton]
    exact helperForProposition_7_6_outerMeasure_prodSingleton_zero Set.univ

/-- Helper for Proposition 7.7: coordinatewise lower-upper compatibility for the product box. -/
lemma helperForProposition_7_7_productOpenBox_lower_le_upper
    {n m : ℕ} (U : OpenBox n) (V : OpenBox m) :
    ∀ i : Fin (n + m), Fin.append U.lower V.lower i ≤ Fin.append U.upper V.upper i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [Fin.append_left] using U.lower_le_upper j
  · intro j
    simpa [Fin.append_right] using V.lower_le_upper j

/-- Helper for Proposition 7.7: product construction on open boxes in dimensions `n` and `m`. -/
def helperForProposition_7_7_productOpenBox
    {n m : ℕ} (U : OpenBox n) (V : OpenBox m) : OpenBox (n + m) :=
  { lower := Fin.append U.lower V.lower
    upper := Fin.append U.upper V.upper
    lower_le_upper := helperForProposition_7_7_productOpenBox_lower_le_upper U V }

/-- Helper for Proposition 7.7: the set of the product box is the preimage of the Cartesian
product under coordinate splitting. -/
lemma helperForProposition_7_7_productOpenBox_toSet
    {n m : ℕ} (U : OpenBox n) (V : OpenBox m) :
    (helperForProposition_7_7_productOpenBox U V).toSet =
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (U.toSet ×ˢ V.toSet)) := by
  ext x
  constructor
  · intro hx
    change (Fin.appendEquiv n m).symm x ∈ U.toSet ×ˢ V.toSet
    refine ⟨?_, ?_⟩
    · intro i
      simpa [helperForProposition_7_7_productOpenBox, OpenBox.toSet, Fin.append_left] using
        hx (Fin.castAdd m i)
    · intro i
      simpa [helperForProposition_7_7_productOpenBox, OpenBox.toSet, Fin.append_right] using
        hx (Fin.natAdd n i)
  · intro hx
    change (Fin.appendEquiv n m).symm x ∈ U.toSet ×ˢ V.toSet at hx
    rcases hx with ⟨hxU, hxV⟩
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [helperForProposition_7_7_productOpenBox, OpenBox.toSet, Fin.append_left] using hxU j
    · intro j
      simpa [helperForProposition_7_7_productOpenBox, OpenBox.toSet, Fin.append_right] using hxV j

/-- Helper for Proposition 7.7: volume of a product box factors as the product of volumes. -/
lemma helperForProposition_7_7_productOpenBox_volume_mul
    {n m : ℕ} (U : OpenBox n) (V : OpenBox m) :
    ENNReal.ofReal ((helperForProposition_7_7_productOpenBox U V).volume) =
      ENNReal.ofReal U.volume * ENNReal.ofReal V.volume := by
  unfold OpenBox.volume helperForProposition_7_7_productOpenBox
  rw [Fin.prod_univ_add]
  rw [ENNReal.ofReal_mul]
  · simp [Fin.append_left, Fin.append_right]
  · exact Finset.prod_nonneg (fun i _ => by
      have hle :
          Fin.append U.lower V.lower (Fin.castAdd m i) ≤
            Fin.append U.upper V.upper (Fin.castAdd m i) := by
        simpa [Fin.append_left] using U.lower_le_upper i
      exact sub_nonneg.mpr hle)

/-- Helper for Proposition 7.7: paired-index covering sums for product boxes factor as a product
of covering sums. -/
lemma helperForProposition_7_7_tsum_unpair_productCover
    {n m : ℕ} (C : ℕ → OpenBox n) (D : ℕ → OpenBox m) :
    (∑' k : ℕ,
      ENNReal.ofReal
        ((helperForProposition_7_7_productOpenBox (C k.unpair.1) (D k.unpair.2)).volume)) =
      (∑' i : ℕ, ENNReal.ofReal ((C i).volume)) *
        (∑' j : ℕ, ENNReal.ofReal ((D j).volume)) := by
  calc
    (∑' k : ℕ,
      ENNReal.ofReal
        ((helperForProposition_7_7_productOpenBox (C k.unpair.1) (D k.unpair.2)).volume))
        = ∑' p : ℕ × ℕ,
            ENNReal.ofReal ((helperForProposition_7_7_productOpenBox (C p.1) (D p.2)).volume) := by
          simpa [Nat.pairEquiv_symm_apply] using
            (Equiv.tsum_eq Nat.pairEquiv.symm
              (fun p : ℕ × ℕ =>
                ENNReal.ofReal ((helperForProposition_7_7_productOpenBox (C p.1) (D p.2)).volume)))
    _ = ∑' i : ℕ, ∑' j : ℕ,
          ENNReal.ofReal ((helperForProposition_7_7_productOpenBox (C i) (D j)).volume) := by
          simpa using
            (ENNReal.tsum_prod (f := fun i j : ℕ =>
              ENNReal.ofReal ((helperForProposition_7_7_productOpenBox (C i) (D j)).volume)))
    _ = ∑' i : ℕ,
          ENNReal.ofReal ((C i).volume) *
            (∑' j : ℕ, ENNReal.ofReal ((D j).volume)) := by
          refine tsum_congr ?_
          intro i
          have hmul :
              (∑' j : ℕ,
                ENNReal.ofReal ((helperForProposition_7_7_productOpenBox (C i) (D j)).volume)) =
                ∑' j : ℕ, ENNReal.ofReal ((C i).volume) * ENNReal.ofReal ((D j).volume) := by
            refine tsum_congr ?_
            intro j
            simpa using helperForProposition_7_7_productOpenBox_volume_mul (U := C i) (V := D j)
          rw [hmul, ENNReal.tsum_mul_left]
    _ = (∑' i : ℕ, ENNReal.ofReal ((C i).volume)) *
          (∑' j : ℕ, ENNReal.ofReal ((D j).volume)) := by
          rw [ENNReal.tsum_mul_right]

/-- Helper for Proposition 7.7: fixed box covers of `A` and `B` induce a product-cover bound for
`A × B` (viewed in `ℝ^(n+m)` via `Fin.appendEquiv`). -/
lemma helperForProposition_7_7_fixedCovers_bound
    {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (C : ℕ → OpenBox n) (D : ℕ → OpenBox m)
    (hA : IsCoveredByBoxes A C) (hB : IsCoveredByBoxes B D) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) ≤
      (∑' i : ℕ, ENNReal.ofReal ((C i).volume)) *
        (∑' j : ℕ, ENNReal.ofReal ((D j).volume)) := by
  let E : ℕ → OpenBox (n + m) :=
    fun k => helperForProposition_7_7_productOpenBox (C k.unpair.1) (D k.unpair.2)
  have hUnionEq :
      (⋃ k : ℕ, (E k).toSet) =
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          ((⋃ i : ℕ, (C i).toSet) ×ˢ (⋃ j : ℕ, (D j).toSet))) := by
    calc
      (⋃ k : ℕ, (E k).toSet)
          = ⋃ k : ℕ,
              ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
                (((C k.unpair.1).toSet) ×ˢ ((D k.unpair.2).toSet))) := by
            refine Set.iUnion_congr ?_
            intro k
            simp [E, helperForProposition_7_7_productOpenBox_toSet]
      _ = ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
            (⋃ k : ℕ, ((C k.unpair.1).toSet ×ˢ (D k.unpair.2).toSet))) := by
            simp [Set.preimage_iUnion]
      _ = ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
            ((⋃ i : ℕ, (C i).toSet) ×ˢ (⋃ j : ℕ, (D j).toSet))) := by
            have hUnpair :
                (⋃ k : ℕ, (C k.unpair.1).toSet ×ˢ (D k.unpair.2).toSet) =
                  (⋃ i : ℕ, (C i).toSet) ×ˢ (⋃ j : ℕ, (D j).toSet) := by
              simpa using
                (Set.iUnion_unpair_prod
                  (s := fun i : ℕ => (C i).toSet)
                  (t := fun j : ℕ => (D j).toSet))
            simpa [hUnpair]
  have hcoverE : IsCoveredByBoxes
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) E := by
    intro x hx
    rw [hUnionEq]
    change (Fin.appendEquiv n m).symm x ∈ (⋃ i : ℕ, (C i).toSet) ×ˢ (⋃ j : ℕ, (D j).toSet)
    refine ⟨?_, ?_⟩
    · exact hA hx.1
    · exact hB hx.2
  have hInfBound :
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (A ×ˢ B)) ≤
        sInf
          {r : ENNReal |
            ∃ T : ℕ → OpenBox (n + m),
              IsCoveredByBoxes
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
                  (A ×ˢ B)) T ∧
                r = ∑' j, ENNReal.ofReal ((T j).volume)} :=
    helperForProposition_7_1_infimumBound
      (Ω := ((Fin.appendEquiv n m :
        (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B)))
  have hSInfLe :
      sInf
          {r : ENNReal |
            ∃ T : ℕ → OpenBox (n + m),
              IsCoveredByBoxes
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
                  (A ×ˢ B)) T ∧
                r = ∑' j, ENNReal.ofReal ((T j).volume)} ≤
        (∑' i : ℕ, ENNReal.ofReal ((C i).volume)) *
          (∑' j : ℕ, ENNReal.ofReal ((D j).volume)) := by
    refine sInf_le ?_
    refine ⟨E, hcoverE, ?_⟩
    exact (helperForProposition_7_7_tsum_unpair_productCover (C := C) (D := D)).symm
  exact le_trans hInfBound hSInfLe

/-- Helper for Proposition 7.7: if the infimum of a set in `ENNReal` is not `⊤`, then the set
contains a non-`⊤` element. -/
lemma helperForProposition_7_7_exists_nonTop_of_sInf_ne_top
    (S : Set ENNReal) (hS : sInf S ≠ ⊤) :
    ∃ x ∈ S, x ≠ ⊤ := by
  by_contra hNo
  push_neg at hNo
  apply hS
  apply top_unique
  refine le_sInf ?_
  intro x hx
  simpa [hNo x hx]

/-- Helper for Proposition 7.7: from pointwise rectangle bounds and finite witnesses on both
factors, one obtains the bound by products of infima. -/
lemma helperForProposition_7_7_sInfProduct_of_rectBounds_finiteWitness
    {a : ENNReal} {SA SB : Set ENNReal}
    (hRect : ∀ r ∈ SA, ∀ s ∈ SB, a ≤ r * s)
    (hAfinite : ∃ r ∈ SA, r ≠ ⊤)
    (hBfinite : ∃ s ∈ SB, s ≠ ⊤) :
    a ≤ sInf SA * sInf SB := by
  rcases hAfinite with ⟨r0, hr0S, hr0Top⟩
  rcases hBfinite with ⟨s0, hs0S, hs0Top⟩
  let f : SA → ENNReal := fun r => (r : ENNReal)
  let g : SB → ENNReal := fun s => (s : ENNReal)
  have hf : ∃ i : SA, f i ≠ ⊤ := by
    exact ⟨⟨r0, hr0S⟩, hr0Top⟩
  have hg : ∃ j : SB, g j ≠ ⊤ := by
    exact ⟨⟨s0, hs0S⟩, hs0Top⟩
  have hfg : ∀ i j, a ≤ f i * g j := by
    intro i j
    exact hRect i i.2 j j.2
  have hMain : a ≤ (⨅ i, f i) * ⨅ j, g j :=
    ENNReal.le_iInf_mul_iInf hf hg hfg
  simpa [f, g, sInf_eq_iInf, iInf_subtype] using hMain

/-- Helper for Proposition 7.7: rewrite the `sInf` over all set-cover costs as the corresponding
double `iInf` over covers. -/
lemma helperForProposition_7_7_sInf_setCoverCost_eq_iInf
    {d : ℕ} (Ω : Set (Fin d → ℝ)) :
    sInf
        {r : ENNReal | ∃ S : ℕ → Set (Fin d → ℝ), Ω ⊆ ⋃ i : ℕ, S i ∧
          r = ∑' i : ℕ, boxOuterMeasureCoverCost d (S i)}
      = ⨅ S : ℕ → Set (Fin d → ℝ), ⨅ (_ : Ω ⊆ ⋃ i : ℕ, S i),
          ∑' i : ℕ, boxOuterMeasureCoverCost d (S i) := by
  apply le_antisymm
  · refine le_iInf ?_
    intro S
    refine le_iInf ?_
    intro hS
    refine sInf_le ?_
    exact ⟨S, hS, rfl⟩
  · refine le_sInf ?_
    intro r hr
    rcases hr with ⟨S, hS, hrEq⟩
    rw [hrEq]
    exact iInf_le_of_le S (iInf_le_of_le hS le_rfl)

/-- Auxiliary cast-membership transport for `Fin`-indexed sets. -/
lemma helperForProposition_7_7_mem_cast_set_iff_aux
    {a b : ℕ} (h : a = b) (s : Set (Fin a → ℝ)) (x : Fin b → ℝ) :
    x ∈ cast (congrArg (fun t => Set (Fin t → ℝ)) h) s ↔
      (fun i : Fin a => x (Fin.cast h i)) ∈ s := by
  cases h
  rfl

/-- Auxiliary cast transport for `boxOuterMeasure`. -/
lemma helperForProposition_7_7_boxOuterMeasure_cast_eq_aux
    {a b : ℕ} (h : a = b) (s : Set (Fin a → ℝ)) :
    boxOuterMeasure b (cast (congrArg (fun t => Set (Fin t → ℝ)) h) s) =
      boxOuterMeasure a s := by
  cases h
  rfl

/-- Auxiliary zero-left-dimension transport under `Fin.appendEquiv`. -/
lemma helperForProposition_7_7_zeroLeftDim_preimage_univ_prod_aux
    (m : ℕ) (B : Set (Fin m → ℝ)) :
    boxOuterMeasure (0 + m)
      ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
        ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) =
      boxOuterMeasure m B := by
  let hm : m = 0 + m := (Nat.zero_add m).symm
  have hSet :
      ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
        ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) =
        cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B := by
    ext x
    constructor
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff_aux (h := hm)]
      simpa [Fin.natAdd_zero] using hx.2
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff_aux (h := hm)] at hx
      have hUniv : ((Fin.appendEquiv 0 m).symm x).1 ∈ (Set.univ : Set (Fin 0 → ℝ)) := by
        simp
      have hMemB : ((Fin.appendEquiv 0 m).symm x).2 ∈ B := by
        simpa [Fin.natAdd_zero] using hx
      exact And.intro hUniv hMemB
  have hCastMeasure :
      boxOuterMeasure (0 + m) (cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B) =
        boxOuterMeasure m B :=
    helperForProposition_7_7_boxOuterMeasure_cast_eq_aux (h := hm) (s := B)
  calc
    boxOuterMeasure (0 + m)
        ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
          ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B))
      = boxOuterMeasure (0 + m) (cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B) := by
          rw [hSet]
    _ = boxOuterMeasure m B := hCastMeasure

/-- Auxiliary zero-right-dimension transport under `Fin.appendEquiv`. -/
lemma helperForProposition_7_7_zeroRightDim_preimage_prod_univ_aux
    (n : ℕ) (A : Set (Fin n → ℝ)) :
    boxOuterMeasure (n + 0)
      ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
        (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) =
      boxOuterMeasure n A := by
  let hn : n = n + 0 := (Nat.add_zero n).symm
  have hSet :
      ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
        (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) =
        cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A := by
    ext x
    constructor
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff_aux (h := hn)]
      simpa [Fin.castAdd_zero] using hx.1
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff_aux (h := hn)] at hx
      have hMemA : ((Fin.appendEquiv n 0).symm x).1 ∈ A := by
        simpa [Fin.castAdd_zero] using hx
      have hUniv : ((Fin.appendEquiv n 0).symm x).2 ∈ (Set.univ : Set (Fin 0 → ℝ)) := by
        simp
      exact And.intro hMemA hUniv
  have hCastMeasure :
      boxOuterMeasure (n + 0) (cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A) =
        boxOuterMeasure n A :=
    helperForProposition_7_7_boxOuterMeasure_cast_eq_aux (h := hn) (s := A)
  calc
    boxOuterMeasure (n + 0)
        ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
          (A ×ˢ (Set.univ : Set (Fin 0 → ℝ))))
      = boxOuterMeasure (n + 0) (cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A) := by
          rw [hSet]
    _ = boxOuterMeasure n A := hCastMeasure

/-- Auxiliary coordinatewise bounds for `(-(k+1), k+1)`. -/
lemma helperForProposition_7_7_standardOpenBox_lower_le_upper_aux
    (k : ℕ) :
    -((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.zero_le k)
  linarith

/-- Auxiliary standard box in positive dimension. -/
def helperForProposition_7_7_standardOpenBox_aux (d k : ℕ) : OpenBox (d + 1) :=
  { lower := fun _ => -((k : ℝ) + 1)
    upper := fun _ => (k : ℝ) + 1
    lower_le_upper := fun _ => helperForProposition_7_7_standardOpenBox_lower_le_upper_aux k }

/-- Auxiliary cover of `ℝ^(d+1)` by standard boxes. -/
lemma helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim_aux
    (d : ℕ) :
    (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆
      ⋃ k : ℕ, (helperForProposition_7_7_standardOpenBox_aux d k).toSet := by
  intro x hx
  let k : ℕ := Nat.ceil (∑ i : Fin (d + 1), |x i|)
  refine Set.mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  intro i
  have hAbsLeSum : |x i| ≤ ∑ j : Fin (d + 1), |x j| := by
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ |x j| := by
      intro j hj
      exact abs_nonneg (x j)
    have hi : i ∈ (Finset.univ : Finset (Fin (d + 1))) := by
      simp
    simpa using (Finset.single_le_sum hnonneg hi)
  have hSumLeCeil : ∑ j : Fin (d + 1), |x j| ≤ k := by
    exact Nat.le_ceil (∑ j : Fin (d + 1), |x j|)
  have hAbsLeK : |x i| ≤ (k : ℝ) := by
    exact le_trans hAbsLeSum (by exact_mod_cast hSumLeCeil)
  have hKlt : (k : ℝ) < (k : ℝ) + 1 := by
    linarith
  have hAbsLt : |x i| < (k : ℝ) + 1 := by
    exact lt_of_le_of_lt hAbsLeK hKlt
  simpa [helperForProposition_7_7_standardOpenBox_aux] using (abs_lt.mp hAbsLt)

/-- Auxiliary union lemma (right-slice form). -/
lemma helperForProposition_7_7_union_of_zeroProductSlices_zero_right_aux
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (S : ℕ → Set (Fin n → ℝ))
    (hAcover : A ⊆ ⋃ k : ℕ, S k)
    (hSlices : ∀ k : ℕ,
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (S k ×ˢ B)) = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  let e : (Fin (n + m) → ℝ) ≃ (Fin n → ℝ) × (Fin m → ℝ) :=
    (Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm
  have hSubset : e ⁻¹' (A ×ˢ B) ⊆ ⋃ k : ℕ, e ⁻¹' (S k ×ˢ B) := by
    intro x hx
    have hxAB : e x ∈ A ×ˢ B := hx
    rcases hxAB with ⟨hxA, hxB⟩
    rcases Set.mem_iUnion.mp (hAcover hxA) with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k, ?_⟩
    exact ⟨hk, hxB⟩
  have hMono :
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤
        boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) :=
    (boxOuterMeasure (n + m)).mono hSubset
  have hUnion :
      boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) ≤
        ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) := by
    simpa using
      (MeasureTheory.measure_iUnion_le
        (μ := boxOuterMeasure (n + m))
        (s := fun k : ℕ => e ⁻¹' (S k ×ˢ B)))
  have hSliceEq : ∀ k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) = 0 := by
    intro k
    simpa [e] using hSlices k
  have hTsumZero : (∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B))) = 0 := by
    simp [hSliceEq]
  have hLeZero : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B))
          ≤ boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) := hMono
      _ ≤ ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) := hUnion
      _ = 0 := hTsumZero
  have hZeroLe : 0 ≤ boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [e] using hEq

/-- Auxiliary union lemma (left-slice form). -/
lemma helperForProposition_7_7_union_of_zeroProductSlices_zero_left_aux
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (T : ℕ → Set (Fin m → ℝ))
    (hBcover : B ⊆ ⋃ k : ℕ, T k)
    (hSlices : ∀ k : ℕ,
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (A ×ˢ T k)) = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  let e : (Fin (n + m) → ℝ) ≃ (Fin n → ℝ) × (Fin m → ℝ) :=
    (Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm
  have hSubset : e ⁻¹' (A ×ˢ B) ⊆ ⋃ k : ℕ, e ⁻¹' (A ×ˢ T k) := by
    intro x hx
    have hxAB : e x ∈ A ×ˢ B := hx
    rcases hxAB with ⟨hxA, hxB⟩
    rcases Set.mem_iUnion.mp (hBcover hxB) with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k, ?_⟩
    exact ⟨hxA, hk⟩
  have hMono :
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤
        boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) :=
    (boxOuterMeasure (n + m)).mono hSubset
  have hUnion :
      boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) ≤
        ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) := by
    simpa using
      (MeasureTheory.measure_iUnion_le
        (μ := boxOuterMeasure (n + m))
        (s := fun k : ℕ => e ⁻¹' (A ×ˢ T k)))
  have hSliceEq : ∀ k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) = 0 := by
    intro k
    simpa [e] using hSlices k
  have hTsumZero : (∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k))) = 0 := by
    simp [hSliceEq]
  have hLeZero : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B))
          ≤ boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) := hMono
      _ ≤ ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) := hUnion
      _ = 0 := hTsumZero
  have hZeroLe : 0 ≤ boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [e] using hEq

/-- Auxiliary slice-zero lemma: right factor has zero cover-cost, left factor is a
positive-dimensional open box. -/
lemma helperForProposition_7_7_productSlice_zero_of_rightCoverCostZero_and_finiteLeftBox_aux
    (d m : ℕ) (U : OpenBox (d + 1)) (B : Set (Fin m → ℝ))
    (hBcost0 : boxOuterMeasureCoverCost m B = 0) :
    boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (U.toSet ×ˢ B)) = 0 := by
  let A : Set (Fin (d + 1) → ℝ) := U.toSet
  let Z : OpenBox (d + 1) := helperForProposition_7_1_zeroVolumeOpenBox d
  let C : ℕ → OpenBox (d + 1) := fun j => if j = 0 then U else Z
  have hCcover : IsCoveredByBoxes A C := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨0, ?_⟩
    simpa [A, C] using hx
  have hsumC : (∑' j, ENNReal.ofReal ((C j).volume)) = ENNReal.ofReal (U.volume) := by
    rw [tsum_eq_single 0]
    · simp [C]
    · intro j hj
      simp [C, hj, Z, helperForProposition_7_1_zeroVolumeOpenBox_volume]
  by_cases hBempty : B = ∅
  · subst hBempty
    simp
  · let SB : Set ENNReal :=
      {s : ENNReal | ∃ D : ℕ → OpenBox m, IsCoveredByBoxes B D ∧
        s = ∑' j, ENNReal.ofReal ((D j).volume)}
    have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hBempty
    have hBraw : boxOuterMeasureCoverCost m B = sInf SB := by
      simpa [SB] using
        boxOuterMeasureCoverCost_eq_rawInf_of_nonempty (d := m) (Ω := B) (hΩ := hBne)
    have hSBzero : sInf SB = 0 := by
      simpa [hBraw] using hBcost0
    have hSB_top : sInf SB ≠ ⊤ := by
      rw [hSBzero]
      simp
    have hBfinite : ∃ s ∈ SB, s ≠ ⊤ :=
      helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SB hSB_top
    have hRect : ∀ s ∈ SB,
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
            ≤ ENNReal.ofReal U.volume * s := by
      intro s hs
      rcases hs with ⟨D, hD, hsEq⟩
      have hBound :=
        helperForProposition_7_7_fixedCovers_bound (A := A) (B := B) (C := C) (D := D) hCcover hD
      rw [hsumC, ← hsEq] at hBound
      simpa [A] using hBound
    let f : Unit → ENNReal := fun _ => ENNReal.ofReal U.volume
    let g : SB → ENNReal := fun s => (s : ENNReal)
    have hf : ∃ i : Unit, f i ≠ ⊤ := by
      refine ⟨(), ?_⟩
      simp [f]
    have hg : ∃ j : SB, g j ≠ ⊤ := by
      rcases hBfinite with ⟨s, hs, hsTop⟩
      exact ⟨⟨s, hs⟩, hsTop⟩
    have hMain :
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ (⨅ i, f i) * ⨅ j, g j := by
      refine ENNReal.le_iInf_mul_iInf hf hg ?_
      intro i j
      simpa [f, g, mul_comm] using hRect j j.2
    have hLe :
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ ENNReal.ofReal U.volume * sInf SB := by
      simpa [f, g, sInf_eq_iInf, iInf_subtype, mul_comm] using hMain
    have hLeZero :
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ 0 := by
      calc
        boxOuterMeasure ((d + 1) + m)
            ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
                (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
            ≤ ENNReal.ofReal U.volume * sInf SB := hLe
        _ = ENNReal.ofReal U.volume * 0 := by rw [hSBzero]
        _ = 0 := by simp
    have hZeroLe :
        0 ≤ boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) := by
      exact bot_le
    have hEq :
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
      le_antisymm hLeZero hZeroLe
    simpa [A] using hEq

/-- Auxiliary slice-zero lemma: left factor has zero cover-cost, right factor is a
positive-dimensional open box. -/
lemma helperForProposition_7_7_productSlice_zero_of_leftCoverCostZero_and_finiteRightBox_aux
    (n d : ℕ) (A : Set (Fin n → ℝ)) (V : OpenBox (d + 1))
    (hAcost0 : boxOuterMeasureCoverCost n A = 0) :
    boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ V.toSet)) = 0 := by
  let B : Set (Fin (d + 1) → ℝ) := V.toSet
  let Z : OpenBox (d + 1) := helperForProposition_7_1_zeroVolumeOpenBox d
  let D : ℕ → OpenBox (d + 1) := fun j => if j = 0 then V else Z
  have hDcover : IsCoveredByBoxes B D := by
    intro y hy
    refine Set.mem_iUnion.mpr ?_
    refine ⟨0, ?_⟩
    simpa [B, D] using hy
  have hsumD : (∑' j, ENNReal.ofReal ((D j).volume)) = ENNReal.ofReal (V.volume) := by
    rw [tsum_eq_single 0]
    · simp [D]
    · intro j hj
      simp [D, hj, Z, helperForProposition_7_1_zeroVolumeOpenBox_volume]
  by_cases hAempty : A = ∅
  · subst hAempty
    simp
  · let SA : Set ENNReal :=
      {r : ENNReal | ∃ C : ℕ → OpenBox n, IsCoveredByBoxes A C ∧
        r = ∑' j, ENNReal.ofReal ((C j).volume)}
    have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
    have hAraw : boxOuterMeasureCoverCost n A = sInf SA := by
      simpa [SA] using
        boxOuterMeasureCoverCost_eq_rawInf_of_nonempty (d := n) (Ω := A) (hΩ := hAne)
    have hSAzero : sInf SA = 0 := by
      simpa [hAraw] using hAcost0
    have hSA_top : sInf SA ≠ ⊤ := by
      rw [hSAzero]
      simp
    have hAfinite : ∃ r ∈ SA, r ≠ ⊤ :=
      helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SA hSA_top
    have hRect : ∀ r ∈ SA,
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
            ≤ r * ENNReal.ofReal V.volume := by
      intro r hr
      rcases hr with ⟨C, hC, hrEq⟩
      have hBound :=
        helperForProposition_7_7_fixedCovers_bound (A := A) (B := B) (C := C) (D := D) hC hDcover
      rw [← hrEq, hsumD] at hBound
      simpa [B] using hBound
    let f : SA → ENNReal := fun r => (r : ENNReal)
    let g : Unit → ENNReal := fun _ => ENNReal.ofReal V.volume
    have hf : ∃ i : SA, f i ≠ ⊤ := by
      rcases hAfinite with ⟨r, hr, hrTop⟩
      exact ⟨⟨r, hr⟩, hrTop⟩
    have hg : ∃ j : Unit, g j ≠ ⊤ := by
      refine ⟨(), ?_⟩
      simp [g]
    have hMain :
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ (⨅ i, f i) * ⨅ j, g j := by
      refine ENNReal.le_iInf_mul_iInf hf hg ?_
      intro i j
      simpa [f, g] using hRect i i.2
    have hLe :
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ sInf SA * ENNReal.ofReal V.volume := by
      simpa [f, g, sInf_eq_iInf, iInf_subtype] using hMain
    have hLeZero :
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ 0 := by
      calc
        boxOuterMeasure (n + (d + 1))
            ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
                (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
            ≤ sInf SA * ENNReal.ofReal V.volume := hLe
        _ = 0 * ENNReal.ofReal V.volume := by rw [hSAzero]
        _ = 0 := by simp
    have hZeroLe :
        0 ≤ boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) := by
      exact bot_le
    have hEq :
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
      le_antisymm hLeZero hZeroLe
    simpa [B] using hEq

/-- Auxiliary product-zero result from zero right cover-cost. -/
lemma helperForProposition_7_7_rightFactor_zero_product_of_coverCostZero_aux
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (hBcost0 : boxOuterMeasureCoverCost m B = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  cases n with
  | zero =>
      have hOuterLeCost : boxOuterMeasure m B ≤ boxOuterMeasureCoverCost m B := by
        simpa [boxOuterMeasure] using
          (MeasureTheory.OuterMeasure.ofFunction_le
            (m := boxOuterMeasureCoverCost m)
            (m_empty := boxOuterMeasureCoverCost_empty m)
            (s := B))
      have hBzero : boxOuterMeasure m B = 0 := by
        have hLeZero : boxOuterMeasure m B ≤ 0 := by
          simpa [hBcost0] using hOuterLeCost
        exact le_antisymm hLeZero bot_le
      have hSubset :
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ⊆
            ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
              ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) := by
        intro x hx
        exact ⟨by simp, hx.2⟩
      have hMono :
          boxOuterMeasure (0 + m)
            ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
              (A ×ˢ B)) ≤
            boxOuterMeasure (0 + m)
              ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) :=
        (boxOuterMeasure (0 + m)).mono hSubset
      have hLeZero : boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ≤ 0 := by
        calc
          boxOuterMeasure (0 + m)
              ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                (A ×ˢ B))
              ≤ boxOuterMeasure (0 + m)
                  ((Fin.appendEquiv 0 m :
                      (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                    ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) := hMono
          _ = boxOuterMeasure m B :=
            helperForProposition_7_7_zeroLeftDim_preimage_univ_prod_aux m B
          _ = 0 := hBzero
      have hZeroLe : 0 ≤ boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) := by
        exact bot_le
      have hEq : boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) = 0 :=
        le_antisymm hLeZero hZeroLe
      simpa [Nat.zero_add] using hEq
  | succ d =>
      let S : ℕ → Set (Fin (d + 1) → ℝ) :=
        fun k => (helperForProposition_7_7_standardOpenBox_aux d k).toSet
      have hCoverUniv :
          (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆ ⋃ k : ℕ, S k := by
        simpa [S] using helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim_aux d
      have hCoverA : A ⊆ ⋃ k : ℕ, S k := by
        intro x hxA
        exact hCoverUniv (by simp)
      have hSlices : ∀ k : ℕ,
          boxOuterMeasure ((d + 1) + m)
            ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
                (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (S k ×ˢ B)) = 0 := by
        intro k
        simpa [S] using
          helperForProposition_7_7_productSlice_zero_of_rightCoverCostZero_and_finiteLeftBox_aux
            d m (helperForProposition_7_7_standardOpenBox_aux d k) B hBcost0
      simpa using
        helperForProposition_7_7_union_of_zeroProductSlices_zero_right_aux
          (n := d + 1) (m := m) (A := A) (B := B) (S := S) hCoverA hSlices

/-- Auxiliary product-zero result from zero left cover-cost. -/
lemma helperForProposition_7_7_leftFactor_zero_product_of_coverCostZero_aux
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (hAcost0 : boxOuterMeasureCoverCost n A = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  cases m with
  | zero =>
      have hOuterLeCost : boxOuterMeasure n A ≤ boxOuterMeasureCoverCost n A := by
        simpa [boxOuterMeasure] using
          (MeasureTheory.OuterMeasure.ofFunction_le
            (m := boxOuterMeasureCoverCost n)
            (m_empty := boxOuterMeasureCoverCost_empty n)
            (s := A))
      have hAzero : boxOuterMeasure n A = 0 := by
        have hLeZero : boxOuterMeasure n A ≤ 0 := by
          simpa [hAcost0] using hOuterLeCost
        exact le_antisymm hLeZero bot_le
      have hSubset :
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ⊆
            ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
              (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) := by
        intro x hx
        exact ⟨hx.1, by simp⟩
      have hMono :
          boxOuterMeasure (n + 0)
            ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
              (A ×ˢ B)) ≤
            boxOuterMeasure (n + 0)
              ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) :=
        (boxOuterMeasure (n + 0)).mono hSubset
      have hLeZero : boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ≤ 0 := by
        calc
          boxOuterMeasure (n + 0)
              ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                (A ×ˢ B))
              ≤ boxOuterMeasure (n + 0)
                  ((Fin.appendEquiv n 0 :
                      (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                    (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) := hMono
          _ = boxOuterMeasure n A :=
            helperForProposition_7_7_zeroRightDim_preimage_prod_univ_aux n A
          _ = 0 := hAzero
      have hZeroLe : 0 ≤ boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) := by
        exact bot_le
      have hEq : boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) = 0 :=
        le_antisymm hLeZero hZeroLe
      simpa [Nat.add_zero] using hEq
  | succ d =>
      let T : ℕ → Set (Fin (d + 1) → ℝ) :=
        fun k => (helperForProposition_7_7_standardOpenBox_aux d k).toSet
      have hCoverUniv :
          (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆ ⋃ k : ℕ, T k := by
        simpa [T] using helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim_aux d
      have hCoverB : B ⊆ ⋃ k : ℕ, T k := by
        intro y hyB
        exact hCoverUniv (by simp)
      have hSlices : ∀ k : ℕ,
          boxOuterMeasure (n + (d + 1))
            ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
                (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ T k)) = 0 := by
        intro k
        simpa [T] using
          helperForProposition_7_7_productSlice_zero_of_leftCoverCostZero_and_finiteRightBox_aux
            n d A (helperForProposition_7_7_standardOpenBox_aux d k) hAcost0
      simpa using
        helperForProposition_7_7_union_of_zeroProductSlices_zero_left_aux
          (n := n) (m := d + 1) (A := A) (B := B) (T := T) hCoverB hSlices

/-- Helper for Proposition 7.7: rectangle preimages are bounded by the product of the
box-cover costs of the two factors. -/
lemma helperForProposition_7_7_coverCost_rect_bound
    {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) ≤
      boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
  by_cases hA : A = ∅
  · subst hA
    simp [boxOuterMeasureCoverCost_empty]
  · by_cases hB : B = ∅
    · subst hB
      simp [boxOuterMeasureCoverCost_empty]
    · let SA : Set ENNReal :=
        {r : ENNReal | ∃ C : ℕ → OpenBox n, IsCoveredByBoxes A C ∧
          r = ∑' j, ENNReal.ofReal ((C j).volume)}
      let SB : Set ENNReal :=
        {r : ENNReal | ∃ D : ℕ → OpenBox m, IsCoveredByBoxes B D ∧
          r = ∑' j, ENNReal.ofReal ((D j).volume)}
      have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
      have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB
      have hAraw : boxOuterMeasureCoverCost n A = sInf SA := by
        simpa [SA] using
          boxOuterMeasureCoverCost_eq_rawInf_of_nonempty (d := n) (Ω := A) (hΩ := hAne)
      have hBraw : boxOuterMeasureCoverCost m B = sInf SB := by
        simpa [SB] using
          boxOuterMeasureCoverCost_eq_rawInf_of_nonempty (d := m) (Ω := B) (hΩ := hBne)
      have hRect :
          ∀ r ∈ SA, ∀ s ∈ SB,
            boxOuterMeasure (n + m)
              ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                  (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ r * s := by
        intro r hr s hs
        rcases hr with ⟨C, hC, hrEq⟩
        rcases hs with ⟨D, hD, hsEq⟩
        rw [hrEq, hsEq]
        exact helperForProposition_7_7_fixedCovers_bound (A := A) (B := B) (C := C) (D := D) hC hD
      by_cases hSA_top : sInf SA = ⊤
      · have hCostA_top : boxOuterMeasureCoverCost n A = ⊤ := by
          simpa [hAraw] using hSA_top
        by_cases hCostB_zero : boxOuterMeasureCoverCost m B = 0
        · have hRectZero :
            boxOuterMeasure (n + m)
              ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                  (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
            helperForProposition_7_7_rightFactor_zero_product_of_coverCostZero_aux
              n m A B hCostB_zero
          calc
            boxOuterMeasure (n + m)
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                    (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
                = 0 := hRectZero
            _ ≤ boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
                simpa [hCostB_zero]
        · have hMulTop :
            boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B = ⊤ := by
            simpa [hCostA_top] using (ENNReal.top_mul hCostB_zero)
          calc
            boxOuterMeasure (n + m)
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                    (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
                ≤ ⊤ := le_top
            _ = boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
                symm
                exact hMulTop
      · by_cases hSB_top : sInf SB = ⊤
        · have hCostB_top : boxOuterMeasureCoverCost m B = ⊤ := by
            simpa [hBraw] using hSB_top
          by_cases hCostA_zero : boxOuterMeasureCoverCost n A = 0
          · have hRectZero :
              boxOuterMeasure (n + m)
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                    (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
              helperForProposition_7_7_leftFactor_zero_product_of_coverCostZero_aux
                n m A B hCostA_zero
            calc
              boxOuterMeasure (n + m)
                  ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                      (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
                  = 0 := hRectZero
              _ ≤ boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
                  simpa [hCostA_zero]
          · have hMulTop :
              boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B = ⊤ := by
              simpa [hCostB_top] using (ENNReal.mul_top hCostA_zero)
            calc
              boxOuterMeasure (n + m)
                  ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                      (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
                  ≤ ⊤ := le_top
              _ = boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
                  symm
                  exact hMulTop
        · have hAfinite : ∃ r ∈ SA, r ≠ ⊤ :=
            helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SA hSA_top
          have hBfinite : ∃ s ∈ SB, s ≠ ⊤ :=
            helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SB hSB_top
          have hBound : boxOuterMeasure (n + m)
              ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                  (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ sInf SA * sInf SB :=
            helperForProposition_7_7_sInfProduct_of_rectBounds_finiteWitness hRect hAfinite hBfinite
          calc
            boxOuterMeasure (n + m)
                ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
                    (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
                ≤ sInf SA * sInf SB := hBound
            _ = boxOuterMeasureCoverCost n A * boxOuterMeasureCoverCost m B := by
                rw [hAraw, hBraw]

/-- Helper for Proposition 7.7: fixed covers by arbitrary sets induce the corresponding
box-cover-cost product bound for rectangle preimages. -/
lemma helperForProposition_7_7_setCovers_bound
    {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (S : ℕ → Set (Fin n → ℝ)) (T : ℕ → Set (Fin m → ℝ))
    (hA : A ⊆ ⋃ i : ℕ, S i) (hB : B ⊆ ⋃ j : ℕ, T j) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) ≤
      (∑' i : ℕ, boxOuterMeasureCoverCost n (S i)) *
        (∑' j : ℕ, boxOuterMeasureCoverCost m (T j)) := by
  let P : ℕ → Set (Fin (n + m) → ℝ) := fun k =>
    ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
        (Fin (n + m) → ℝ)).symm ⁻¹' (S k.unpair.1 ×ˢ T k.unpair.2))
  have hSubset :
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) ⊆ ⋃ k : ℕ, P k := by
    intro x hx
    rcases Set.mem_iUnion.mp (hA hx.1) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp (hB hx.2) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Nat.pair i j, ?_⟩
    change (Fin.appendEquiv n m).symm x ∈
      S (Nat.unpair (Nat.pair i j)).1 ×ˢ T (Nat.unpair (Nat.pair i j)).2
    simpa using And.intro hi hj
  have hMono :
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (A ×ˢ B)) ≤
        boxOuterMeasure (n + m) (⋃ k : ℕ, P k) :=
    (boxOuterMeasure (n + m)).mono hSubset
  have hUnion :
      boxOuterMeasure (n + m) (⋃ k : ℕ, P k) ≤
        ∑' k : ℕ, boxOuterMeasure (n + m) (P k) :=
    MeasureTheory.measure_iUnion_le (μ := boxOuterMeasure (n + m)) (s := P)
  have hCell :
      ∀ k : ℕ, boxOuterMeasure (n + m) (P k) ≤
        boxOuterMeasureCoverCost n (S k.unpair.1) *
          boxOuterMeasureCoverCost m (T k.unpair.2) := by
    intro k
    simpa [P] using helperForProposition_7_7_coverCost_rect_bound
      (n := n) (m := m) (A := S k.unpair.1) (B := T k.unpair.2)
  have hSumLe :
      (∑' k : ℕ, boxOuterMeasure (n + m) (P k)) ≤
        ∑' k : ℕ, boxOuterMeasureCoverCost n (S k.unpair.1) *
          boxOuterMeasureCoverCost m (T k.unpair.2) := by
    exact ENNReal.tsum_le_tsum hCell
  have hPair :
      (∑' k : ℕ, boxOuterMeasureCoverCost n (S k.unpair.1) *
          boxOuterMeasureCoverCost m (T k.unpair.2))
        = ∑' p : ℕ × ℕ, boxOuterMeasureCoverCost n (S p.1) *
            boxOuterMeasureCoverCost m (T p.2) := by
    simpa [Nat.pairEquiv_symm_apply] using
      (Equiv.tsum_eq Nat.pairEquiv.symm
        (fun p : ℕ × ℕ =>
          boxOuterMeasureCoverCost n (S p.1) * boxOuterMeasureCoverCost m (T p.2)))
  have hProd :
      (∑' p : ℕ × ℕ, boxOuterMeasureCoverCost n (S p.1) *
          boxOuterMeasureCoverCost m (T p.2))
        = ∑' i : ℕ, ∑' j : ℕ,
            boxOuterMeasureCoverCost n (S i) * boxOuterMeasureCoverCost m (T j) := by
    simpa using
      (ENNReal.tsum_prod (f := fun i j : ℕ =>
        boxOuterMeasureCoverCost n (S i) * boxOuterMeasureCoverCost m (T j)))
  have hMul :
      (∑' i : ℕ, ∑' j : ℕ,
          boxOuterMeasureCoverCost n (S i) * boxOuterMeasureCoverCost m (T j))
        = (∑' i : ℕ, boxOuterMeasureCoverCost n (S i)) *
            (∑' j : ℕ, boxOuterMeasureCoverCost m (T j)) := by
    calc
      (∑' i : ℕ, ∑' j : ℕ,
          boxOuterMeasureCoverCost n (S i) * boxOuterMeasureCoverCost m (T j))
          = ∑' i : ℕ,
              boxOuterMeasureCoverCost n (S i) *
                (∑' j : ℕ, boxOuterMeasureCoverCost m (T j)) := by
            refine tsum_congr ?_
            intro i
            rw [ENNReal.tsum_mul_left]
      _ = (∑' i : ℕ, boxOuterMeasureCoverCost n (S i)) *
            (∑' j : ℕ, boxOuterMeasureCoverCost m (T j)) := by
            rw [ENNReal.tsum_mul_right]
  calc
    boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃
            (Fin (n + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
        ≤ boxOuterMeasure (n + m) (⋃ k : ℕ, P k) := hMono
    _ ≤ ∑' k : ℕ, boxOuterMeasure (n + m) (P k) := hUnion
    _ ≤ ∑' k : ℕ, boxOuterMeasureCoverCost n (S k.unpair.1) *
          boxOuterMeasureCoverCost m (T k.unpair.2) := hSumLe
    _ = ∑' p : ℕ × ℕ, boxOuterMeasureCoverCost n (S p.1) *
          boxOuterMeasureCoverCost m (T p.2) := hPair
    _ = ∑' i : ℕ, ∑' j : ℕ,
          boxOuterMeasureCoverCost n (S i) * boxOuterMeasureCoverCost m (T j) := hProd
    _ = (∑' i : ℕ, boxOuterMeasureCoverCost n (S i)) *
          (∑' j : ℕ, boxOuterMeasureCoverCost m (T j)) := hMul

/-- Helper for Proposition 7.7: coordinatewise bounds for the standard box `(-(k+1), k+1)`. -/
lemma helperForProposition_7_7_standardOpenBox_lower_le_upper
    (k : ℕ) :
    -((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.zero_le k)
  linarith

/-- Helper for Proposition 7.7: the standard box `(-(k+1), k+1)^(d+1)` in positive dimension. -/
def helperForProposition_7_7_standardOpenBox (d k : ℕ) : OpenBox (d + 1) :=
  { lower := fun _ => -((k : ℝ) + 1)
    upper := fun _ => (k : ℝ) + 1
    lower_le_upper := fun _ => helperForProposition_7_7_standardOpenBox_lower_le_upper k }

/-- Helper for Proposition 7.7: standard positive-dimensional boxes cover all of `ℝ^(d+1)`. -/
lemma helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim
    (d : ℕ) :
    (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆
      ⋃ k : ℕ, (helperForProposition_7_7_standardOpenBox d k).toSet := by
  intro x hx
  let k : ℕ := Nat.ceil (∑ i : Fin (d + 1), |x i|)
  refine Set.mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  intro i
  have hAbsLeSum : |x i| ≤ ∑ j : Fin (d + 1), |x j| := by
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ |x j| := by
      intro j hj
      exact abs_nonneg (x j)
    have hi : i ∈ (Finset.univ : Finset (Fin (d + 1))) := by
      simp
    simpa using (Finset.single_le_sum hnonneg hi)
  have hSumLeCeil : ∑ j : Fin (d + 1), |x j| ≤ k := by
    exact Nat.le_ceil (∑ j : Fin (d + 1), |x j|)
  have hAbsLeK : |x i| ≤ (k : ℝ) := by
    exact le_trans hAbsLeSum (by exact_mod_cast hSumLeCeil)
  have hKlt : (k : ℝ) < (k : ℝ) + 1 := by
    linarith
  have hAbsLt : |x i| < (k : ℝ) + 1 := by
    exact lt_of_le_of_lt hAbsLeK hKlt
  simpa [helperForProposition_7_7_standardOpenBox] using (abs_lt.mp hAbsLt)

/-- Helper for Proposition 7.7: zero on each left-slice of a cover implies zero on the full
product set. -/
lemma helperForProposition_7_7_union_of_zeroProductSlices_zero_right
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (S : ℕ → Set (Fin n → ℝ))
    (hAcover : A ⊆ ⋃ k : ℕ, S k)
    (hSlices : ∀ k : ℕ,
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (S k ×ˢ B)) = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  let e : (Fin (n + m) → ℝ) ≃ (Fin n → ℝ) × (Fin m → ℝ) :=
    (Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm
  have hSubset : e ⁻¹' (A ×ˢ B) ⊆ ⋃ k : ℕ, e ⁻¹' (S k ×ˢ B) := by
    intro x hx
    have hxAB : e x ∈ A ×ˢ B := hx
    rcases hxAB with ⟨hxA, hxB⟩
    rcases Set.mem_iUnion.mp (hAcover hxA) with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k, ?_⟩
    exact ⟨hk, hxB⟩
  have hMono :
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤
        boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) :=
    (boxOuterMeasure (n + m)).mono hSubset
  have hUnion :
      boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) ≤
        ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) := by
    simpa using
      (MeasureTheory.measure_iUnion_le
        (μ := boxOuterMeasure (n + m))
        (s := fun k : ℕ => e ⁻¹' (S k ×ˢ B)))
  have hSliceEq : ∀ k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) = 0 := by
    intro k
    simpa [e] using hSlices k
  have hTsumZero : (∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B))) = 0 := by
    simp [hSliceEq]
  have hLeZero : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B))
          ≤ boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (S k ×ˢ B)) := hMono
      _ ≤ ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (S k ×ˢ B)) := hUnion
      _ = 0 := hTsumZero
  have hZeroLe : 0 ≤ boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [e] using hEq

/-- Helper for Proposition 7.7: zero on each right-slice of a cover implies zero on the full
product set. -/
lemma helperForProposition_7_7_union_of_zeroProductSlices_zero_left
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (T : ℕ → Set (Fin m → ℝ))
    (hBcover : B ⊆ ⋃ k : ℕ, T k)
    (hSlices : ∀ k : ℕ,
      boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (A ×ˢ T k)) = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  let e : (Fin (n + m) → ℝ) ≃ (Fin n → ℝ) × (Fin m → ℝ) :=
    (Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm
  have hSubset : e ⁻¹' (A ×ˢ B) ⊆ ⋃ k : ℕ, e ⁻¹' (A ×ˢ T k) := by
    intro x hx
    have hxAB : e x ∈ A ×ˢ B := hx
    rcases hxAB with ⟨hxA, hxB⟩
    rcases Set.mem_iUnion.mp (hBcover hxB) with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k, ?_⟩
    exact ⟨hxA, hk⟩
  have hMono :
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤
        boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) :=
    (boxOuterMeasure (n + m)).mono hSubset
  have hUnion :
      boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) ≤
        ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) := by
    simpa using
      (MeasureTheory.measure_iUnion_le
        (μ := boxOuterMeasure (n + m))
        (s := fun k : ℕ => e ⁻¹' (A ×ˢ T k)))
  have hSliceEq : ∀ k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) = 0 := by
    intro k
    simpa [e] using hSlices k
  have hTsumZero : (∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k))) = 0 := by
    simp [hSliceEq]
  have hLeZero : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B))
          ≤ boxOuterMeasure (n + m) (⋃ k : ℕ, e ⁻¹' (A ×ˢ T k)) := hMono
      _ ≤ ∑' k : ℕ, boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ T k)) := hUnion
      _ = 0 := hTsumZero
  have hZeroLe : 0 ≤ boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure (n + m) (e ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [e] using hEq

/-- Helper for Proposition 7.7: if the right factor has zero outer measure, then every
positive-dimensional finite-box slice has zero product outer measure. -/
lemma helperForProposition_7_7_productSlice_zero_of_rightZero_and_finiteLeftBox
    (d m : ℕ) (U : OpenBox (d + 1)) (B : Set (Fin m → ℝ))
    (hBzero : boxOuterMeasure m B = 0) :
    boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (U.toSet ×ˢ B)) = 0 := by
  let A : Set (Fin (d + 1) → ℝ) := U.toSet
  let SA : Set ENNReal :=
    {r : ENNReal | ∃ S : ℕ → Set (Fin (d + 1) → ℝ), A ⊆ ⋃ i : ℕ, S i ∧
      r = ∑' i : ℕ, boxOuterMeasureCoverCost (d + 1) (S i)}
  let SB : Set ENNReal :=
    {r : ENNReal | ∃ T : ℕ → Set (Fin m → ℝ), B ⊆ ⋃ j : ℕ, T j ∧
      r = ∑' j : ℕ, boxOuterMeasureCoverCost m (T j)}
  have hAeq : boxOuterMeasure (d + 1) A = sInf SA := by
    calc
      boxOuterMeasure (d + 1) A
          = ⨅ S : ℕ → Set (Fin (d + 1) → ℝ), ⨅ (_ : A ⊆ ⋃ i : ℕ, S i),
              ∑' i : ℕ, boxOuterMeasureCoverCost (d + 1) (S i) := by
            simpa using boxOuterMeasure_apply (d + 1) A
      _ = sInf SA := by
            simpa [SA] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := d + 1) (Ω := A)).symm
  have hBeq : boxOuterMeasure m B = sInf SB := by
    calc
      boxOuterMeasure m B
          = ⨅ T : ℕ → Set (Fin m → ℝ), ⨅ (_ : B ⊆ ⋃ j : ℕ, T j),
              ∑' j : ℕ, boxOuterMeasureCoverCost m (T j) := by
            simpa using boxOuterMeasure_apply m B
      _ = sInf SB := by
            simpa [SB] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := m) (Ω := B)).symm
  have hRect :
      ∀ r ∈ SA, ∀ s ∈ SB,
        boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ r * s := by
    intro r hr s hs
    rcases hr with ⟨S, hS, hrEq⟩
    rcases hs with ⟨T, hT, hsEq⟩
    rw [hrEq, hsEq]
    exact helperForProposition_7_7_setCovers_bound (A := A) (B := B) (S := S) (T := T) hS hT
  have hAouter : boxOuterMeasure (d + 1) A = ENNReal.ofReal U.volume := by
    simpa [A] using helperForProposition_7_1_openBoxOuterEqVolume d U
  have hA_top : boxOuterMeasure (d + 1) A ≠ ⊤ := by
    rw [hAouter]
    exact ENNReal.ofReal_ne_top
  have hSA_top : sInf SA ≠ ⊤ := by
    simpa [hAeq] using hA_top
  have hAfinite : ∃ r ∈ SA, r ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SA hSA_top
  have hSB_top : sInf SB ≠ ⊤ := by
    rw [← hBeq, hBzero]
    simp
  have hBfinite : ∃ s ∈ SB, s ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SB hSB_top
  have hBound : boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤
        sInf SA * sInf SB :=
    helperForProposition_7_7_sInfProduct_of_rectBounds_finiteWitness hRect hAfinite hBfinite
  have hSBzero : sInf SB = 0 := by
    simpa [hBeq] using hBzero
  have hLeZero : boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure ((d + 1) + m)
          ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
              (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ sInf SA * sInf SB := hBound
      _ = sInf SA * 0 := by rw [hSBzero]
      _ = 0 := by simp
  have hZeroLe : 0 ≤ boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure ((d + 1) + m)
      ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
          (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [A] using hEq

/-- Helper for Proposition 7.7: if the left factor has zero outer measure, then every
positive-dimensional finite-box slice has zero product outer measure. -/
lemma helperForProposition_7_7_productSlice_zero_of_leftZero_and_finiteRightBox
    (n d : ℕ) (A : Set (Fin n → ℝ)) (V : OpenBox (d + 1))
    (hAzero : boxOuterMeasure n A = 0) :
    boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ V.toSet)) = 0 := by
  let SA : Set ENNReal :=
    {r : ENNReal | ∃ S : ℕ → Set (Fin n → ℝ), A ⊆ ⋃ i : ℕ, S i ∧
      r = ∑' i : ℕ, boxOuterMeasureCoverCost n (S i)}
  let B : Set (Fin (d + 1) → ℝ) := V.toSet
  let SB : Set ENNReal :=
    {r : ENNReal | ∃ T : ℕ → Set (Fin (d + 1) → ℝ), B ⊆ ⋃ j : ℕ, T j ∧
      r = ∑' j : ℕ, boxOuterMeasureCoverCost (d + 1) (T j)}
  have hAeq : boxOuterMeasure n A = sInf SA := by
    calc
      boxOuterMeasure n A
          = ⨅ S : ℕ → Set (Fin n → ℝ), ⨅ (_ : A ⊆ ⋃ i : ℕ, S i),
              ∑' i : ℕ, boxOuterMeasureCoverCost n (S i) := by
            simpa using boxOuterMeasure_apply n A
      _ = sInf SA := by
            simpa [SA] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := n) (Ω := A)).symm
  have hBeq : boxOuterMeasure (d + 1) B = sInf SB := by
    calc
      boxOuterMeasure (d + 1) B
          = ⨅ T : ℕ → Set (Fin (d + 1) → ℝ), ⨅ (_ : B ⊆ ⋃ j : ℕ, T j),
              ∑' j : ℕ, boxOuterMeasureCoverCost (d + 1) (T j) := by
            simpa using boxOuterMeasure_apply (d + 1) B
      _ = sInf SB := by
            simpa [SB] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := d + 1) (Ω := B)).symm
  have hRect :
      ∀ r ∈ SA, ∀ s ∈ SB,
        boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ r * s := by
    intro r hr s hs
    rcases hr with ⟨S, hS, hrEq⟩
    rcases hs with ⟨T, hT, hsEq⟩
    rw [hrEq, hsEq]
    exact helperForProposition_7_7_setCovers_bound (A := A) (B := B) (S := S) (T := T) hS hT
  have hBouter : boxOuterMeasure (d + 1) B = ENNReal.ofReal V.volume := by
    simpa [B] using helperForProposition_7_1_openBoxOuterEqVolume d V
  have hB_top : boxOuterMeasure (d + 1) B ≠ ⊤ := by
    rw [hBouter]
    exact ENNReal.ofReal_ne_top
  have hSB_top : sInf SB ≠ ⊤ := by
    simpa [hBeq] using hB_top
  have hBfinite : ∃ s ∈ SB, s ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SB hSB_top
  have hSA_top : sInf SA ≠ ⊤ := by
    rw [← hAeq, hAzero]
    simp
  have hAfinite : ∃ r ∈ SA, r ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SA hSA_top
  have hBound : boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤
        sInf SA * sInf SB :=
    helperForProposition_7_7_sInfProduct_of_rectBounds_finiteWitness hRect hAfinite hBfinite
  have hSAzero : sInf SA = 0 := by
    simpa [hAeq] using hAzero
  have hLeZero : boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) ≤ 0 := by
    calc
      boxOuterMeasure (n + (d + 1))
          ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
              (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B))
          ≤ sInf SA * sInf SB := hBound
      _ = 0 * sInf SB := by rw [hSAzero]
      _ = 0 := by simp
  have hZeroLe : 0 ≤ boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) := by
    exact bot_le
  have hEq : boxOuterMeasure (n + (d + 1))
      ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
          (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ B)) = 0 :=
    le_antisymm hLeZero hZeroLe
  simpa [B] using hEq

/-- Helper for Proposition 7.7: transport membership through a type cast of
`Fin`-indexed sets. -/
lemma helperForProposition_7_7_mem_cast_set_iff
    {a b : ℕ} (h : a = b) (s : Set (Fin a → ℝ)) (x : Fin b → ℝ) :
    x ∈ cast (congrArg (fun t => Set (Fin t → ℝ)) h) s ↔
      (fun i : Fin a => x (Fin.cast h i)) ∈ s := by
  cases h
  rfl

/-- Helper for Proposition 7.7: transport `boxOuterMeasure` across a type cast
of `Fin`-indexed ambient spaces. -/
lemma helperForProposition_7_7_boxOuterMeasure_cast_eq
    {a b : ℕ} (h : a = b) (s : Set (Fin a → ℝ)) :
    boxOuterMeasure b (cast (congrArg (fun t => Set (Fin t → ℝ)) h) s) =
      boxOuterMeasure a s := by
  cases h
  rfl

/-- Helper for Proposition 7.7: in zero left dimension, the preimage of `univ × B` under
`Fin.appendEquiv` has the same outer measure as `B`. -/
lemma helperForProposition_7_7_zeroLeftDim_preimage_univ_prod
    (m : ℕ) (B : Set (Fin m → ℝ)) :
    boxOuterMeasure (0 + m)
      ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
        ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) =
      boxOuterMeasure m B := by
  let hm : m = 0 + m := (Nat.zero_add m).symm
  have hSet :
      ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
        ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) =
        cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B := by
    ext x
    constructor
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff (h := hm)]
      simpa [Fin.natAdd_zero] using hx.2
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff (h := hm)] at hx
      have hUniv : ((Fin.appendEquiv 0 m).symm x).1 ∈ (Set.univ : Set (Fin 0 → ℝ)) := by
        simp
      have hMemB : ((Fin.appendEquiv 0 m).symm x).2 ∈ B := by
        simpa [Fin.natAdd_zero] using hx
      exact And.intro hUniv hMemB
  have hCastMeasure :
      boxOuterMeasure (0 + m) (cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B) =
        boxOuterMeasure m B :=
    helperForProposition_7_7_boxOuterMeasure_cast_eq (h := hm) (s := B)
  calc
    boxOuterMeasure (0 + m)
        ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
          ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B))
      = boxOuterMeasure (0 + m) (cast (congrArg (fun t => Set (Fin t → ℝ)) hm) B) := by
          rw [hSet]
    _ = boxOuterMeasure m B := hCastMeasure

/-- Helper for Proposition 7.7: in zero right dimension, the preimage of `A × univ` under
`Fin.appendEquiv` has the same outer measure as `A`. -/
lemma helperForProposition_7_7_zeroRightDim_preimage_prod_univ
    (n : ℕ) (A : Set (Fin n → ℝ)) :
    boxOuterMeasure (n + 0)
      ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
        (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) =
      boxOuterMeasure n A := by
  let hn : n = n + 0 := (Nat.add_zero n).symm
  have hSet :
      ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
        (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) =
        cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A := by
    ext x
    constructor
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff (h := hn)]
      simpa [Fin.castAdd_zero] using hx.1
    · intro hx
      rw [helperForProposition_7_7_mem_cast_set_iff (h := hn)] at hx
      have hMemA : ((Fin.appendEquiv n 0).symm x).1 ∈ A := by
        simpa [Fin.castAdd_zero] using hx
      have hUniv : ((Fin.appendEquiv n 0).symm x).2 ∈ (Set.univ : Set (Fin 0 → ℝ)) := by
        simp
      exact And.intro hMemA hUniv
  have hCastMeasure :
      boxOuterMeasure (n + 0) (cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A) =
        boxOuterMeasure n A :=
    helperForProposition_7_7_boxOuterMeasure_cast_eq (h := hn) (s := A)
  calc
    boxOuterMeasure (n + 0)
        ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
          (A ×ˢ (Set.univ : Set (Fin 0 → ℝ))))
      = boxOuterMeasure (n + 0) (cast (congrArg (fun t => Set (Fin t → ℝ)) hn) A) := by
          rw [hSet]
    _ = boxOuterMeasure n A := hCastMeasure

/-- Helper for Proposition 7.7: if the right factor has zero box outer measure, then the product
set has zero box outer measure. -/
lemma helperForProposition_7_7_rightFactor_zero_product
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (hBzero : boxOuterMeasure m B = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  cases n with
  | zero =>
      have hSubset :
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ⊆
            ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
              ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) := by
        intro x hx
        exact ⟨by simp, hx.2⟩
      have hMono :
          boxOuterMeasure (0 + m)
            ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
              (A ×ˢ B)) ≤
            boxOuterMeasure (0 + m)
              ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) :=
        (boxOuterMeasure (0 + m)).mono hSubset
      have hLeZero : boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ≤ 0 := by
        calc
          boxOuterMeasure (0 + m)
              ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                (A ×ˢ B))
              ≤ boxOuterMeasure (0 + m)
                  ((Fin.appendEquiv 0 m :
                      (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
                    ((Set.univ : Set (Fin 0 → ℝ)) ×ˢ B)) := hMono
          _ = boxOuterMeasure m B :=
            helperForProposition_7_7_zeroLeftDim_preimage_univ_prod m B
          _ = 0 := hBzero
      have hZeroLe : 0 ≤ boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) := by
        exact bot_le
      have hEq : boxOuterMeasure (0 + m)
          ((Fin.appendEquiv 0 m : (Fin 0 → ℝ) × (Fin m → ℝ) ≃ (Fin (0 + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) = 0 :=
        le_antisymm hLeZero hZeroLe
      simpa [Nat.zero_add] using hEq
  | succ d =>
      let S : ℕ → Set (Fin (d + 1) → ℝ) :=
        fun k => (helperForProposition_7_7_standardOpenBox d k).toSet
      have hCoverUniv :
          (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆ ⋃ k : ℕ, S k := by
        simpa [S] using helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim d
      have hCoverA : A ⊆ ⋃ k : ℕ, S k := by
        intro x hxA
        have hxUniv : x ∈ (Set.univ : Set (Fin (d + 1) → ℝ)) := by
          simp
        exact hCoverUniv hxUniv
      have hSlices : ∀ k : ℕ,
          boxOuterMeasure ((d + 1) + m)
            ((Fin.appendEquiv (d + 1) m : (Fin (d + 1) → ℝ) × (Fin m → ℝ) ≃
                (Fin ((d + 1) + m) → ℝ)).symm ⁻¹' (S k ×ˢ B)) = 0 := by
        intro k
        simpa [S] using
          helperForProposition_7_7_productSlice_zero_of_rightZero_and_finiteLeftBox
            d m (helperForProposition_7_7_standardOpenBox d k) B hBzero
      simpa using
        helperForProposition_7_7_union_of_zeroProductSlices_zero_right
          (n := d + 1) (m := m) (A := A) (B := B) (S := S) hCoverA hSlices

/-- Helper for Proposition 7.7: if the left factor has zero box outer measure, then the product
set has zero box outer measure. -/
lemma helperForProposition_7_7_leftFactor_zero_product
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ))
    (hAzero : boxOuterMeasure n A = 0) :
    boxOuterMeasure (n + m)
      ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
        (A ×ˢ B)) = 0 := by
  cases m with
  | zero =>
      have hSubset :
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ⊆
            ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
              (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) := by
        intro x hx
        exact ⟨hx.1, by simp⟩
      have hMono :
          boxOuterMeasure (n + 0)
            ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
              (A ×ˢ B)) ≤
            boxOuterMeasure (n + 0)
              ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) :=
        (boxOuterMeasure (n + 0)).mono hSubset
      have hLeZero : boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ≤ 0 := by
        calc
          boxOuterMeasure (n + 0)
              ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                (A ×ˢ B))
              ≤ boxOuterMeasure (n + 0)
                  ((Fin.appendEquiv n 0 :
                      (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
                    (A ×ˢ (Set.univ : Set (Fin 0 → ℝ)))) := hMono
          _ = boxOuterMeasure n A :=
            helperForProposition_7_7_zeroRightDim_preimage_prod_univ n A
          _ = 0 := hAzero
      have hZeroLe : 0 ≤ boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) := by
        exact bot_le
      have hEq : boxOuterMeasure (n + 0)
          ((Fin.appendEquiv n 0 : (Fin n → ℝ) × (Fin 0 → ℝ) ≃ (Fin (n + 0) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) = 0 :=
        le_antisymm hLeZero hZeroLe
      simpa [Nat.add_zero] using hEq
  | succ d =>
      let T : ℕ → Set (Fin (d + 1) → ℝ) :=
        fun k => (helperForProposition_7_7_standardOpenBox d k).toSet
      have hCoverUniv :
          (Set.univ : Set (Fin (d + 1) → ℝ)) ⊆ ⋃ k : ℕ, T k := by
        simpa [T] using helperForProposition_7_7_standardOpenBoxes_cover_univ_posDim d
      have hCoverB : B ⊆ ⋃ k : ℕ, T k := by
        intro y hyB
        have hyUniv : y ∈ (Set.univ : Set (Fin (d + 1) → ℝ)) := by
          simp
        exact hCoverUniv hyUniv
      have hSlices : ∀ k : ℕ,
          boxOuterMeasure (n + (d + 1))
            ((Fin.appendEquiv n (d + 1) : (Fin n → ℝ) × (Fin (d + 1) → ℝ) ≃
                (Fin (n + (d + 1)) → ℝ)).symm ⁻¹' (A ×ˢ T k)) = 0 := by
        intro k
        simpa [T] using
          helperForProposition_7_7_productSlice_zero_of_leftZero_and_finiteRightBox
            n d A (helperForProposition_7_7_standardOpenBox d k) hAzero
      simpa using
        helperForProposition_7_7_union_of_zeroProductSlices_zero_left
          (n := n) (m := d + 1) (A := A) (B := B) (T := T) hCoverB hSlices

/-- Helper for Proposition 7.7: in the non-`⊤` branch for both factors, the rectangle bounds imply
the target product inequality. -/
lemma helperForProposition_7_7_nonTop_branch_finish
    {a : ENNReal} {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    {SA SB : Set ENNReal}
    (hAeq : boxOuterMeasure n A = sInf SA)
    (hBeq : boxOuterMeasure m B = sInf SB)
    (hRect : ∀ r ∈ SA, ∀ s ∈ SB, a ≤ r * s)
    (hA_top : boxOuterMeasure n A ≠ ⊤)
    (hB_top : boxOuterMeasure m B ≠ ⊤) :
    a ≤ boxOuterMeasure n A * boxOuterMeasure m B := by
  have hSA_top : sInf SA ≠ ⊤ := by
    simpa [hAeq] using hA_top
  have hSB_top : sInf SB ≠ ⊤ := by
    simpa [hBeq] using hB_top
  have hAfinite : ∃ r ∈ SA, r ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SA hSA_top
  have hBfinite : ∃ s ∈ SB, s ≠ ⊤ :=
    helperForProposition_7_7_exists_nonTop_of_sInf_ne_top SB hSB_top
  have hBound : a ≤ sInf SA * sInf SB :=
    helperForProposition_7_7_sInfProduct_of_rectBounds_finiteWitness hRect hAfinite hBfinite
  simpa [hAeq, hBeq] using hBound

/-- Proposition 7.7: for `A ⊆ ℝ^n` and `B ⊆ ℝ^m`, the box outer measure satisfies
`m*_{n+m}(A × B) ≤ m*_n(A) * m*_m(B)`, where `A × B` is viewed inside `ℝ^(n+m)` via the
canonical splitting equivalence of coordinates, and with the usual `ENNReal` conventions for
products involving `+∞` (in particular `0 * +∞ = 0`). -/
theorem proposition_7_7
    (n m : ℕ) (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    boxOuterMeasure (n + m)
        ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
          (A ×ˢ B)) ≤
      boxOuterMeasure n A * boxOuterMeasure m B := by
  let SA : Set ENNReal :=
    {r : ENNReal | ∃ S : ℕ → Set (Fin n → ℝ), A ⊆ ⋃ i : ℕ, S i ∧
      r = ∑' i : ℕ, boxOuterMeasureCoverCost n (S i)}
  let SB : Set ENNReal :=
    {r : ENNReal | ∃ T : ℕ → Set (Fin m → ℝ), B ⊆ ⋃ j : ℕ, T j ∧
      r = ∑' j : ℕ, boxOuterMeasureCoverCost m (T j)}
  have hAeq : boxOuterMeasure n A = sInf SA := by
    calc
      boxOuterMeasure n A
          = ⨅ S : ℕ → Set (Fin n → ℝ), ⨅ (_ : A ⊆ ⋃ i : ℕ, S i),
              ∑' i : ℕ, boxOuterMeasureCoverCost n (S i) := by
            simpa using boxOuterMeasure_apply n A
      _ = sInf SA := by
            simpa [SA] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := n) (Ω := A)).symm
  have hBeq : boxOuterMeasure m B = sInf SB := by
    calc
      boxOuterMeasure m B
          = ⨅ T : ℕ → Set (Fin m → ℝ), ⨅ (_ : B ⊆ ⋃ j : ℕ, T j),
              ∑' j : ℕ, boxOuterMeasureCoverCost m (T j) := by
            simpa using boxOuterMeasure_apply m B
      _ = sInf SB := by
            simpa [SB] using
              (helperForProposition_7_7_sInf_setCoverCost_eq_iInf (d := m) (Ω := B)).symm
  have hRect :
      ∀ r ∈ SA, ∀ s ∈ SB,
        boxOuterMeasure (n + m)
          ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) ≤ r * s := by
    intro r hr s hs
    rcases hr with ⟨S, hS, hrEq⟩
    rcases hs with ⟨T, hT, hsEq⟩
    rw [hrEq, hsEq]
    exact helperForProposition_7_7_setCovers_bound (A := A) (B := B) (S := S) (T := T) hS hT
  by_cases hAzero : boxOuterMeasure n A = 0
  · have hLeftZero :
        boxOuterMeasure (n + m)
          ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
            (A ×ˢ B)) = 0 :=
      helperForProposition_7_7_leftFactor_zero_product n m A B hAzero
    rw [hAzero, zero_mul]
    exact hLeftZero.le
  · by_cases hBzero : boxOuterMeasure m B = 0
    · have hRightZero :
          boxOuterMeasure (n + m)
            ((Fin.appendEquiv n m : (Fin n → ℝ) × (Fin m → ℝ) ≃ (Fin (n + m) → ℝ)).symm ⁻¹'
              (A ×ˢ B)) = 0 :=
        helperForProposition_7_7_rightFactor_zero_product n m A B hBzero
      rw [hBzero, mul_zero]
      exact hRightZero.le
    · by_cases hAtop : boxOuterMeasure n A = ⊤
      · rw [hAtop, ENNReal.top_mul hBzero]
        exact le_top
      · by_cases hBtop : boxOuterMeasure m B = ⊤
        · rw [hBtop, ENNReal.mul_top hAzero]
          exact le_top
        · exact helperForProposition_7_7_nonTop_branch_finish
            (hAeq := hAeq) (hBeq := hBeq) (hRect := hRect) hAtop hBtop

end Section02
end Chap07
