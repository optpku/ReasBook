/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap05.section04_part1

section Chap05
section Section04

/-- Helper for Lemma 5.4.6: Fejér polynomial on `AddCircle (1 : ℝ)` with frequency
cutoff `N`. -/
noncomputable def helperForLemma_5_4_6_fejerPolynomial (N : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun k =>
      ((((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ))) • fourierCharacter k)

/-- Helper for Lemma 5.4.6: the Fejér polynomial is a trigonometric polynomial. -/
lemma helperForLemma_5_4_6_fejer_isTrig (N : ℕ) :
    IsTrigonometricPolynomial (helperForLemma_5_4_6_fejerPolynomial N) := by
  refine ⟨N, ?_, ?_⟩
  · intro k
    exact (((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ))
  · rfl

/-- Helper for Lemma 5.4.6: character integral on `[0,1]` is `1` at frequency `0`
and vanishes at nonzero frequencies. -/
lemma helperForLemma_5_4_6_intervalIntegral_fourierCharacter_eq_ite (k : ℤ) :
    (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ)))
      = (if k = 0 then (1 : ℂ) else 0) := by
  by_cases hk : k = 0
  · subst hk
    rw [show (fourierCharacter (0 : ℤ)) = (1 : C(AddCircle (1 : ℝ), ℂ)) by
          ext x
          simp [fourierCharacter]]
    simp
  · have hnonzero :
        (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ))) = 0 := by
      calc
        (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ)))
            = ∫ y in Set.Ioc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ)) := by
              rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        _ = ∫ y : AddCircle (1 : ℝ), fourierCharacter k y := by
              simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
                (f := fun z : AddCircle (1 : ℝ) => fourierCharacter k z))
        _ = 0 := by
            have hShift :
                ∀ x : AddCircle (1 : ℝ),
                  fourierCharacter k (x + (↑((1 : ℝ) / 2 / (k : ℝ)) : AddCircle (1 : ℝ)))
                    = - fourierCharacter k x := by
              intro x
              simpa [fourierCharacter, mul_comm, mul_left_comm, mul_assoc] using
                (fourier_add_half_inv_index (T := (1 : ℝ)) hk (by norm_num : (0 : ℝ) < 1) x)
            have hzero :
                (∫ x : AddCircle (1 : ℝ), fourierCharacter k x
                    ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) = 0 :=
              MeasureTheory.integral_eq_zero_of_add_right_eq_neg
                (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) hShift
            simpa [AddCircle.volume_eq_smul_haarAddCircle] using hzero
    simp [hk, hnonzero]

/-- Helper for Lemma 5.4.6: rewrite the Fejér mass integral as a weighted finite
character-integral sum. -/
lemma helperForLemma_5_4_6_fejerIntegral_as_weightedCharacterSum (N : ℕ) :
    (∫ y in Set.Icc (0 : ℝ) 1, helperForLemma_5_4_6_fejerPolynomial N (y : AddCircle (1 : ℝ)))
      = Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k =>
            ((((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
              (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ))))) := by
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let a : ℤ → ℂ := fun k => (((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ))
  have hInt :
      ∀ k ∈ s,
        MeasureTheory.Integrable
          (fun y : ℝ => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ)))
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro k hk
    have hcont :
        Continuous (fun y : ℝ => fourierCharacter k (y : AddCircle (1 : ℝ))) :=
      (fourierCharacter k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
    have hcontSmul :
        Continuous (fun y : ℝ => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ))) :=
      continuous_const.smul hcont
    have hIntOn :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ)))
          (Set.Icc (0 : ℝ) 1) (MeasureTheory.volume) :=
      hcontSmul.continuousOn.integrableOn_compact (μ := MeasureTheory.volume) isCompact_Icc
    simpa [MeasureTheory.IntegrableOn] using hIntOn
  have hsum :
      (∫ y in Set.Icc (0 : ℝ) 1,
          Finset.sum s (fun k => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ))))
        =
      Finset.sum s
        (fun k => ∫ y in Set.Icc (0 : ℝ) 1, (a k) • fourierCharacter k (y : AddCircle (1 : ℝ))) := by
    simpa using
      (MeasureTheory.integral_finset_sum
        (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        (s := s)
        (f := fun k : ℤ =>
          fun y : ℝ => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ)))
        hInt)
  calc
    (∫ y in Set.Icc (0 : ℝ) 1, helperForLemma_5_4_6_fejerPolynomial N (y : AddCircle (1 : ℝ)))
        =
      (∫ y in Set.Icc (0 : ℝ) 1,
        Finset.sum s (fun k => (a k) • fourierCharacter k (y : AddCircle (1 : ℝ)))) := by
          simp [helperForLemma_5_4_6_fejerPolynomial, s, a]
    _ = Finset.sum s
          (fun k => ∫ y in Set.Icc (0 : ℝ) 1, (a k) • fourierCharacter k (y : AddCircle (1 : ℝ))) :=
          hsum
    _ = Finset.sum s
          (fun k =>
            ((a k) * (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ))))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [MeasureTheory.integral_smul]
          simp [smul_eq_mul]
    _ = Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k =>
            ((((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
              (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ))))) := by
          simp [s, a]

/-- Helper for Lemma 5.4.6: the Fejér polynomial has total mass `1` on `[0,1]`. -/
lemma helperForLemma_5_4_6_fejer_mass_one (N : ℕ) :
    (∫ y in Set.Icc (0 : ℝ) 1, helperForLemma_5_4_6_fejerPolynomial N (y : AddCircle (1 : ℝ)))
      = (1 : ℂ) := by
  rw [helperForLemma_5_4_6_fejerIntegral_as_weightedCharacterSum]
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp
  calc
    (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k =>
        (((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter k (y : AddCircle (1 : ℝ)))))
        = (((N + 1 - Int.natAbs (0 : ℤ) : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
            (∫ y in Set.Icc (0 : ℝ) 1, fourierCharacter (0 : ℤ) (y : AddCircle (1 : ℝ))) := by
          refine Finset.sum_eq_single 0 ?_ ?_
          · intro k hk hk0
            rw [helperForLemma_5_4_6_intervalIntegral_fourierCharacter_eq_ite]
            simp [hk0]
          · intro h0notmem
            exact (h0notmem h0mem).elim
    _ = (((N + 1 - Int.natAbs (0 : ℤ) : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) * (1 : ℂ) := by
          rw [helperForLemma_5_4_6_intervalIntegral_fourierCharacter_eq_ite]
          simp
    _ = (1 : ℂ) := by
          have hN1 : ((N : ℂ) + 1) ≠ 0 := by
            exact_mod_cast (Nat.succ_ne_zero N)
          have hdiv : ((N : ℂ) + 1) / ((N : ℂ) + 1) = (1 : ℂ) := div_self hN1
          simpa [Nat.cast_add, Nat.cast_one] using hdiv

/-- Helper for Lemma 5.4.6: Archimedean index choice turning an `O((N+1)⁻¹)` bound
into a strict `< ε` estimate. -/
lemma helperForLemma_5_4_6_chooseIndexFromTailBound
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C) :
    ∃ N : ℕ, C / (N + 1 : ℝ) < ε := by
  have hεC : 0 < ε / C := div_pos hε hC
  rcases exists_nat_one_div_lt hεC with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hmul : C * (1 / ((N : ℝ) + 1)) < C * (ε / C) :=
    mul_lt_mul_of_pos_left hN hC
  calc
    C / (N + 1 : ℝ) = C * (1 / ((N : ℝ) + 1)) := by ring
    _ < C * (ε / C) := hmul
    _ = ε := by field_simp [hC.ne']

/-- Helper for Lemma 5.4.6: convert an integer-difference equation between
natural numbers into a nonnegative shift equation. -/
lemma helperForLemma_5_4_6_intDiff_eq_natShift (i j m : ℕ) :
    ((i : ℤ) - (j : ℤ) = (m : ℤ)) ↔ i = j + m := by
  omega

/-- Helper for Lemma 5.4.6: convert an integer-difference equation between
natural numbers into a negative shift equation. -/
lemma helperForLemma_5_4_6_intDiff_eq_negNatShift (i j m : ℕ) :
    ((i : ℤ) - (j : ℤ) = - (m : ℤ)) ↔ j = i + m := by
  omega

/-- Helper for Lemma 5.4.6: count pairs `(i,j)` in `range (N+1) × range (N+1)`
with `i = j + m`. -/
lemma helperForLemma_5_4_6_pairCount_nonnegShift (N m : ℕ) :
    ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => p.1 = p.2 + m)).card = N + 1 - m := by
  classical
  have hst :
      ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
        (fun p : ℕ × ℕ => p.1 = p.2 + m))
        = Finset.image (fun j : ℕ => (j + m, j)) (Finset.range (N + 1 - m)) := by
    ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hp
      have hp' : (i < N + 1 ∧ j < N + 1) ∧ i = j + m := by
        simpa [Finset.mem_filter, Finset.mem_product] using hp
      rcases hp' with ⟨hijRange, hij⟩
      rcases hijRange with ⟨hi, hj⟩
      have hjm : j + m < N + 1 := by simpa [hij] using hi
      have hjlt : j < N + 1 - m := (lt_tsub_iff_right).2 hjm
      refine Finset.mem_image.mpr ?_
      refine ⟨j, by simpa using hjlt, ?_⟩
      simp [hij]
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨a, ha, hEq⟩
      have ha_lt : a < N + 1 - m := by simpa using ha
      have hEq1 : a + m = i := by
        have := congrArg Prod.fst hEq
        simpa using this
      have hEq2 : a = j := by
        have := congrArg Prod.snd hEq
        simpa using this
      have haj : a + m < N + 1 := (lt_tsub_iff_right).1 ha_lt
      have hi : i < N + 1 := by simpa [hEq1] using haj
      have hj : j < N + 1 := by
        have haN1 : a < N + 1 := lt_of_lt_of_le ha_lt (Nat.sub_le (N + 1) m)
        simpa [hEq2] using haN1
      have hij : i = j + m := by omega
      have hi' : i ≤ N := by omega
      have hj' : j ≤ N := by omega
      simpa [Finset.mem_filter, Finset.mem_product] using And.intro ⟨hi', hj'⟩ hij
  have hinj : Function.Injective (fun j : ℕ => (j + m, j)) := by
    intro a b h
    have hsnd : a = b := by
      have := congrArg Prod.snd h
      simpa using this
    exact hsnd
  calc
    ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => p.1 = p.2 + m)).card
        = (Finset.image (fun j : ℕ => (j + m, j)) (Finset.range (N + 1 - m))).card := by
            rw [hst]
    _ = (Finset.range (N + 1 - m)).card := Finset.card_image_of_injective _ hinj
    _ = N + 1 - m := by simp

/-- Helper for Lemma 5.4.6: count pairs `(i,j)` in `range (N+1) × range (N+1)`
with `j = i + m`. -/
lemma helperForLemma_5_4_6_pairCount_nonnegShift_swapped (N m : ℕ) :
    ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => p.2 = p.1 + m)).card = N + 1 - m := by
  classical
  have hst :
      ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
        (fun p : ℕ × ℕ => p.2 = p.1 + m))
        = Finset.image (fun i : ℕ => (i, i + m)) (Finset.range (N + 1 - m)) := by
    ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hp
      have hp' : (i < N + 1 ∧ j < N + 1) ∧ j = i + m := by
        simpa [Finset.mem_filter, Finset.mem_product] using hp
      rcases hp' with ⟨hijRange, hij⟩
      rcases hijRange with ⟨hi, hj⟩
      have him : i + m < N + 1 := by simpa [hij] using hj
      have hilt : i < N + 1 - m := (lt_tsub_iff_right).2 him
      refine Finset.mem_image.mpr ?_
      refine ⟨i, by simpa using hilt, ?_⟩
      simp [hij]
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨a, ha, hEq⟩
      have ha_lt : a < N + 1 - m := by simpa using ha
      have hEq1 : a = i := by
        have := congrArg Prod.fst hEq
        simpa using this
      have hEq2 : a + m = j := by
        have := congrArg Prod.snd hEq
        simpa using this
      have haj : a + m < N + 1 := (lt_tsub_iff_right).1 ha_lt
      have hj : j < N + 1 := by simpa [hEq2] using haj
      have hi : i < N + 1 := by
        have haN1 : a < N + 1 := lt_of_lt_of_le ha_lt (Nat.sub_le (N + 1) m)
        simpa [hEq1] using haN1
      have hij : j = i + m := by omega
      have hi' : i ≤ N := by omega
      have hj' : j ≤ N := by omega
      simpa [Finset.mem_filter, Finset.mem_product] using And.intro ⟨hi', hj'⟩ hij
  have hinj : Function.Injective (fun i : ℕ => (i, i + m)) := by
    intro a b h
    have hfst : a = b := by
      have := congrArg Prod.fst h
      simpa using this
    exact hfst
  calc
    ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => p.2 = p.1 + m)).card
        = (Finset.image (fun i : ℕ => (i, i + m)) (Finset.range (N + 1 - m))).card := by
            rw [hst]
    _ = (Finset.range (N + 1 - m)).card := Finset.card_image_of_injective _ hinj
    _ = N + 1 - m := by simp

/-- Helper for Lemma 5.4.6: the number of pairs in `range (N+1) × range (N+1)`
with integer difference `k` is `N+1-|k|`. -/
lemma helperForLemma_5_4_6_pairCount_eq_weight (N : ℕ) (k : ℤ) :
    ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ) = k))).card = N + 1 - Int.natAbs k := by
  classical
  by_cases hk0 : 0 ≤ k
  · have hk : k = (Int.natAbs k : ℤ) := by
      symm
      exact Int.ofNat_natAbs_of_nonneg hk0
    have hfilter :
        ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
          (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ) = k)))
        = ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
            (fun p : ℕ × ℕ => p.1 = p.2 + Int.natAbs k)) := by
      ext p
      rcases p with ⟨i, j⟩
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hmem, hEq⟩
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        have hEq' : ((i : ℤ) - (j : ℤ) = (Int.natAbs k : ℤ)) := hEq.trans hk
        exact (helperForLemma_5_4_6_intDiff_eq_natShift i j (Int.natAbs k)).1 hEq'
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hmem, hEq⟩
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        have hEq' : ((i : ℤ) - (j : ℤ) = (Int.natAbs k : ℤ)) :=
          (helperForLemma_5_4_6_intDiff_eq_natShift i j (Int.natAbs k)).2 hEq
        exact hEq'.trans hk.symm
    rw [hfilter, helperForLemma_5_4_6_pairCount_nonnegShift]
  · have hk_nonpos : k ≤ 0 := le_of_not_ge hk0
    have hk : k = -((Int.natAbs k : ℕ) : ℤ) := by
      have hnat : ((Int.natAbs k : ℕ) : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk_nonpos
      linarith
    have hfilter :
        ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
          (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ) = k)))
        = ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
            (fun p : ℕ × ℕ => p.2 = p.1 + Int.natAbs k)) := by
      ext p
      rcases p with ⟨i, j⟩
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hmem, hEq⟩
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        have hEq' : ((i : ℤ) - (j : ℤ) = -((Int.natAbs k : ℕ) : ℤ)) := hEq.trans hk
        exact (helperForLemma_5_4_6_intDiff_eq_negNatShift i j (Int.natAbs k)).1 hEq'
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hmem, hEq⟩
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        have hEq' : ((i : ℤ) - (j : ℤ) = -((Int.natAbs k : ℕ) : ℤ)) :=
          (helperForLemma_5_4_6_intDiff_eq_negNatShift i j (Int.natAbs k)).2 hEq
        exact hEq'.trans hk.symm
    rw [hfilter, helperForLemma_5_4_6_pairCount_nonnegShift_swapped]

/-- Helper for Lemma 5.4.6: integer differences of indices from `range (N+1)`
lie in the symmetric interval `[-N, N]`. -/
lemma helperForLemma_5_4_6_diff_mem_Icc
    (N i j : ℕ)
    (hi : i ∈ Finset.range (N + 1))
    (hj : j ∈ Finset.range (N + 1)) :
    ((i : ℤ) - (j : ℤ)) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  have hi' : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hj' : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hBounds : (-(N : ℤ) ≤ (i : ℤ) - (j : ℤ)) ∧ ((i : ℤ) - (j : ℤ) ≤ (N : ℤ)) := by
    omega
  simpa [Finset.mem_Icc] using hBounds

/-- Helper for Lemma 5.4.6: group the double range sum by fixed difference
`k = i - j`. -/
lemma helperForLemma_5_4_6_doubleRangeSum_groupByDifference
    (N : ℕ) (z : ℂ) :
    Finset.sum (Finset.range (N + 1))
      (fun i => Finset.sum (Finset.range (N + 1)) (fun j => z ^ i * star (z ^ j)))
      =
    Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k =>
        Finset.sum
          ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = k))
          (fun p => z ^ p.1 * star (z ^ p.2))) := by
  classical
  let s : Finset (ℕ × ℕ) := Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))
  let t : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let g : ℕ × ℕ → ℤ := fun p => (p.1 : ℤ) - (p.2 : ℤ)
  let f : ℕ × ℕ → ℂ := fun p => z ^ p.1 * star (z ^ p.2)
  have hmaps : ∀ p ∈ s, g p ∈ t := by
    intro p hp
    have hp' : p ∈ Finset.product (Finset.range (N + 1)) (Finset.range (N + 1)) := by
      simpa [s] using hp
    rcases Finset.mem_product.mp hp' with ⟨hi, hj⟩
    simpa [s, t, g] using helperForLemma_5_4_6_diff_mem_Icc N p.1 p.2 hi hj
  have hfiber :
      Finset.sum t (fun k => Finset.sum (s.filter (fun p => g p = k)) f)
        = Finset.sum s f :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := t) (g := g) hmaps f
  calc
    Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1)) (fun j => z ^ i * star (z ^ j)))
        = Finset.sum s f := by
          simp [s, f, Finset.sum_product]
    _ = Finset.sum t (fun k => Finset.sum (s.filter (fun p => g p = k)) f) := by
          simpa using hfiber.symm
    _ = Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k =>
            Finset.sum
              ((Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
                (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = k))
              (fun p => z ^ p.1 * star (z ^ p.2))) := by
          simp [s, t, g, f]

/-- Helper for Lemma 5.4.6: on the fiber where `i - j = k`, the term
`z^i * conj(z^j)` with `z = exp(i 2π x)` collapses to the `k`-mode exponential. -/
lemma helperForLemma_5_4_6_expTerm_onDifferenceFiber
    (x : ℝ) (i j : ℕ) (k : ℤ)
    (hDiff : ((i : ℤ) - (j : ℤ) = k)) :
    let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))
    z ^ i * star (z ^ j)
      = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
  intro z
  have hstarExp : ∀ w : ℂ, star (Complex.exp w) = Complex.exp (star w) := by
    intro w
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.map_exp (𝔸 := ℂ) (𝔹 := ℂ) (f := starRingEnd ℂ) continuous_star w)
  have hzpowi : z ^ i = Complex.exp ((i : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) := by
    calc
      z ^ i = Complex.exp (Complex.I * (2 * Real.pi * (x : ℂ))) ^ i := by rfl
      _ = Complex.exp ((i : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) := by
            simpa [mul_comm] using
              (Complex.exp_nat_mul (Complex.I * (2 * Real.pi * (x : ℂ))) i).symm
  have hzpowj : z ^ j = Complex.exp ((j : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) := by
    calc
      z ^ j = Complex.exp (Complex.I * (2 * Real.pi * (x : ℂ))) ^ j := by rfl
      _ = Complex.exp ((j : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) := by
            simpa [mul_comm] using
              (Complex.exp_nat_mul (Complex.I * (2 * Real.pi * (x : ℂ))) j).symm
  have hstarPowj :
      star (z ^ j) = Complex.exp ((j : ℂ) * (-Complex.I * (2 * Real.pi * (x : ℂ)))) := by
    calc
      star (z ^ j) = star (Complex.exp ((j : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ))))) := by
        rw [hzpowj]
      _ = Complex.exp (star ((j : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ))))) := by
        rw [hstarExp]
      _ = Complex.exp ((j : ℂ) * (-Complex.I * (2 * Real.pi * (x : ℂ)))) := by
        simp [mul_assoc]
  calc
    z ^ i * star (z ^ j)
        = Complex.exp ((i : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) *
            Complex.exp ((j : ℂ) * (-Complex.I * (2 * Real.pi * (x : ℂ)))) := by
              rw [hzpowi, hstarPowj]
    _ = Complex.exp (((i : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ)))) +
          ((j : ℂ) * (-Complex.I * (2 * Real.pi * (x : ℂ))))) := by
          rw [← Complex.exp_add]
    _ = Complex.exp (2 * Real.pi * Complex.I * (((i : ℤ) - (j : ℤ)) : ℂ) * (x : ℂ)) := by
          congr 1
          have h1 :
              ((i : ℂ) * (Complex.I * (2 * Real.pi * (x : ℂ))) +
                (j : ℂ) * (-Complex.I * (2 * Real.pi * (x : ℂ))))
                = ((i : ℂ) - (j : ℂ)) * (Complex.I * (2 * Real.pi * (x : ℂ))) := by
            ring
          rw [h1]
          have h2 : ((i : ℂ) - (j : ℂ)) = (((i : ℤ) - (j : ℤ)) : ℂ) := by
            norm_num [Int.cast_sub]
          rw [h2]
          ring
    _ = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
          have h2 : (((i : ℤ) - (j : ℤ)) : ℂ) = (k : ℂ) := by exact_mod_cast hDiff
          rw [h2]


/-- Helper for Lemma 5.4.6: convert the weighted `k`-sum on `[-N,N]` into the
double-range geometric sum. -/
lemma helperForLemma_5_4_6_weightedIccSum_eq_doubleRangeSum
    (N : ℕ) (x : ℝ) :
    let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))
    Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k =>
        (((N + 1 - Int.natAbs k : ℕ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))))
      = Finset.sum (Finset.range (N + 1))
          (fun i => Finset.sum (Finset.range (N + 1))
            (fun j => z ^ i * star (z ^ j))) := by
  intro z
  have hgroup := helperForLemma_5_4_6_doubleRangeSum_groupByDifference N z
  rw [hgroup]
  refine Finset.sum_congr rfl ?_
  intro k hk
  let s : Finset (ℕ × ℕ) :=
    (Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ) = k))
  have hinnerConst :
      Finset.sum s (fun p => z ^ p.1 * star (z ^ p.2))
        = Finset.sum s (fun _ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : p ∈ (Finset.product (Finset.range (N + 1)) (Finset.range (N + 1))).filter
      (fun q : ℕ × ℕ => ((q.1 : ℤ) - (q.2 : ℤ) = k)) := by
      simpa [s] using hp
    have hpEq : ((p.1 : ℤ) - (p.2 : ℤ) = k) := (Finset.mem_filter.mp hp').2
    simpa [z] using helperForLemma_5_4_6_expTerm_onDifferenceFiber x p.1 p.2 k hpEq
  have hcard : s.card = N + 1 - Int.natAbs k := by
    simpa [s] using helperForLemma_5_4_6_pairCount_eq_weight N k
  calc
    (((N + 1 - Int.natAbs k : ℕ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))
        = ((s.card : ℕ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
            simp [hcard]
    _ = Finset.sum s (fun _ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) := by
          symm
          simpa [nsmul_eq_mul] using
            (Finset.sum_const (s := s) (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))))
    _ = Finset.sum s (fun p => z ^ p.1 * star (z ^ p.2) ) := by
          symm
          exact hinnerConst

/-- Helper for Lemma 5.4.6: rewrite the weighted Fourier-coefficient sum for
the Fejér kernel value into a normalized double geometric sum. -/
lemma helperForLemma_5_4_6_fejerCoeff_weightedSum_eq_doubleGeomSum
    (N : ℕ) (x : ℝ) :
    let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))
    let D : ℂ := ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
      (Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1))
          (fun j => z ^ i * star (z ^ j))) )
    helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ)) = D := by
  intro z D
  have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero N)
  have hweighted :
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k =>
          (((N + 1 - Int.natAbs k : ℕ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))))
        = Finset.sum (Finset.range (N + 1))
            (fun i => Finset.sum (Finset.range (N + 1))
              (fun j => z ^ i * star (z ^ j))) := by
    simpa [z] using helperForLemma_5_4_6_weightedIccSum_eq_doubleRangeSum N x
  calc
    helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))
        = Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun k =>
              ((((N + 1 - Int.natAbs k : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ)) *
                Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))) := by
            simp [helperForLemma_5_4_6_fejerPolynomial, smul_eq_mul, fourierCharacter_apply,
              mul_assoc, mul_left_comm, mul_comm]
    _ = ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun k =>
              (((N + 1 - Int.natAbs k : ℕ) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          field_simp [hN1]
    _ = ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
          Finset.sum (Finset.range (N + 1))
            (fun i => Finset.sum (Finset.range (N + 1))
              (fun j => z ^ i * star (z ^ j))) := by
          rw [hweighted]
    _ = D := by rfl

/-- Helper for Lemma 5.4.6: the normalized double geometric sum equals the
normalized squared geometric-sum norm, with vanishing imaginary part. -/
lemma helperForLemma_5_4_6_doubleGeomSum_eq_normSq_geomSum
    (N : ℕ) (z : ℂ) :
    let S : ℂ := Finset.sum (Finset.range (N + 1)) (fun j => z ^ j)
    let D : ℂ := ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
      (Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1))
          (fun j => z ^ i * star (z ^ j))) )
    D.re = ((1 : ℝ) / (N + 1 : ℝ)) * ‖S‖ ^ 2 ∧ D.im = 0 := by
  intro S D
  have hdouble :
      Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1))
          (fun j => z ^ i * star (z ^ j)))
        = S * star S := by
    calc
      Finset.sum (Finset.range (N + 1))
          (fun i => Finset.sum (Finset.range (N + 1)) (fun j => z ^ i * star (z ^ j)))
          = Finset.sum (Finset.range (N + 1))
              (fun i => z ^ i * Finset.sum (Finset.range (N + 1)) (fun j => star (z ^ j))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
    _ = (Finset.sum (Finset.range (N + 1)) (fun i => z ^ i)) *
          (Finset.sum (Finset.range (N + 1)) (fun j => star (z ^ j))) := by
          rw [Finset.sum_mul]
    _ = S * star S := by
          simp [S]
  have hcoeff : ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) = ((1 : ℝ) / (N + 1 : ℝ) : ℂ) := by
    norm_num [Nat.cast_add, Nat.cast_one]
  have hmul : S * star S = ((Complex.normSq S : ℝ) : ℂ) := by
    simpa using (Complex.mul_conj S)
  have hNnonneg : 0 ≤ (N + 1 : ℝ) := by positivity
  have hnormC : ‖((N : ℂ) + 1)‖ = (N + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, Real.norm_eq_abs, abs_of_nonneg hNnonneg] using
      (Complex.norm_real (N + 1 : ℝ))
  constructor
  · change ((((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
      (Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1))
          (fun j => z ^ i * star (z ^ j))))).re
      = ((1 : ℝ) / (N + 1 : ℝ)) * ‖S‖ ^ 2)
    rw [hdouble, hcoeff, hmul]
    simpa [Complex.normSq_eq_norm_sq, hnormC, pow_two]
  · change ((((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
      (Finset.sum (Finset.range (N + 1))
        (fun i => Finset.sum (Finset.range (N + 1))
          (fun j => z ^ i * star (z ^ j))))).im = 0)
    rw [hdouble, hcoeff, hmul]
    simp

/-- Helper for Lemma 5.4.6: Fejér-kernel evaluation at a real point as a
normalized squared geometric-sum norm, with vanishing imaginary part. -/
lemma helperForLemma_5_4_6_fejer_eval_eq_normSqGeometricSum
    (N : ℕ) (x : ℝ) :
    (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re
      = ((1 : ℝ) / (N + 1 : ℝ)) *
          ‖Finset.sum (Finset.range (N + 1))
            (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ ^ 2 ∧
    (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).im = 0 := by
  let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))
  let S : ℂ := Finset.sum (Finset.range (N + 1)) (fun j => z ^ j)
  let D : ℂ := ((1 : ℂ) / ((N + 1 : ℕ) : ℂ)) *
    (Finset.sum (Finset.range (N + 1))
      (fun i => Finset.sum (Finset.range (N + 1))
        (fun j => z ^ i * star (z ^ j))) )
  have hbridge :
      helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ)) = D := by
    simpa [z, D] using helperForLemma_5_4_6_fejerCoeff_weightedSum_eq_doubleGeomSum N x
  have hdouble :
      D.re = ((1 : ℝ) / (N + 1 : ℝ)) * ‖S‖ ^ 2 ∧ D.im = 0 := by
    simpa [S, D] using helperForLemma_5_4_6_doubleGeomSum_eq_normSq_geomSum N z
  constructor
  · have hre₁ :
      (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re = D.re := by
      simpa [hbridge]
    have hre₂ :
        D.re = ((1 : ℝ) / (N + 1 : ℝ)) *
          ‖Finset.sum (Finset.range (N + 1))
            (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ ^ 2 := by
      simpa [S, z] using hdouble.1
    exact hre₁.trans hre₂
  · have him₁ :
      (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).im = D.im := by
      simpa [hbridge]
    exact him₁.trans hdouble.2

/-- Helper for Lemma 5.4.6: geometric-sum norm bound away from the resonance
`exp(2πix) = 1`. -/
lemma helperForLemma_5_4_6_geomSum_norm_le_two_div_normExpSubOne
    (N : ℕ) (x : ℝ)
    (hx : Complex.exp (Complex.I * (2 * Real.pi * x)) ≠ 1) :
    ‖Finset.sum (Finset.range (N + 1))
      (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖
      ≤ 2 / ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ := by
  let z : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hmul : (Finset.sum (Finset.range (N + 1)) (fun j => z ^ j)) * (z - 1) = z ^ (N + 1) - 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      geom_sum_mul z (N + 1)
  have hnorm_mul :
      ‖Finset.sum (Finset.range (N + 1)) (fun j => z ^ j)‖ * ‖z - 1‖ = ‖z ^ (N + 1) - 1‖ := by
    simpa [norm_mul] using congrArg norm hmul
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp
  have hpow_norm : ‖z ^ (N + 1)‖ = 1 := by
    simpa [norm_pow, hzNorm]
  have hnum : ‖z ^ (N + 1) - 1‖ ≤ 2 := by
    calc
      ‖z ^ (N + 1) - 1‖ ≤ ‖z ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [hpow_norm]
        norm_num
  have hden_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hzsub
  have hmul_le : ‖Finset.sum (Finset.range (N + 1)) (fun j => z ^ j)‖ * ‖z - 1‖ ≤ 2 := by
    simpa [hnorm_mul] using hnum
  have hdiv := (le_div_iff₀ hden_pos).2 hmul_le
  simpa [z, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Lemma 5.4.6: on the annulus `δ ≤ |x| ≤ 1 - δ` with `0 < δ < 1/2`,
the denominator `‖exp(2πix) - 1‖` is uniformly bounded below by a positive
constant. -/
lemma helperForLemma_5_4_6_annulus_expSubOne_lowerBound
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < (1 / 2 : ℝ)) :
    ∃ mδ > 0,
      ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 - δ →
        mδ ≤ ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ := by
  let S : Set ℝ := {x : ℝ | δ ≤ |x| ∧ |x| ≤ 1 - δ}
  let f : ℝ → ℝ := fun x => ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖
  have hSclosed : IsClosed S := by
    refine (isClosed_le continuous_const continuous_abs).inter ?_
    exact isClosed_le continuous_abs continuous_const
  have hSsubset : S ⊆ Metric.closedBall (0 : ℝ) (1 - δ) := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hx.2
  have hScompact : IsCompact S := by
    exact (isCompact_closedBall (0 : ℝ) (1 - δ)).of_isClosed_subset hSclosed hSsubset
  have hSnonempty : S.Nonempty := by
    refine ⟨δ, ?_⟩
    constructor
    · simpa [abs_of_nonneg hδ₀.le] using le_rfl
    · have hδ_le : δ ≤ 1 - δ := by linarith [hδ₁]
      simpa [abs_of_nonneg hδ₀.le] using hδ_le
  have hfcont : Continuous f := by
    unfold f
    continuity
  obtain ⟨x0, hx0S, hx0min⟩ := hScompact.exists_isMinOn hSnonempty hfcont.continuousOn
  have hx0_nonzero : f x0 ≠ 0 := by
    intro hx0zero
    have hnorm0 : ‖2 * Real.sin ((2 * Real.pi * x0) / 2)‖ = 0 := by
      rw [← Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x0)]
      simpa [f] using hx0zero
    have hsin_mul_zero_aux : 2 * Real.sin ((2 * Real.pi * x0) / 2) = 0 :=
      norm_eq_zero.mp hnorm0
    have hsin_mul_zero : 2 * Real.sin (Real.pi * x0) = 0 := by
      convert hsin_mul_zero_aux using 1
      ring_nf
    have hsin_zero : Real.sin (Real.pi * x0) = 0 := by
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hsin_mul_zero).resolve_left htwo
    rcases (Real.sin_eq_zero_iff.mp hsin_zero) with ⟨n, hn⟩
    have hx0eqn : x0 = (n : ℝ) := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hn' : (n : ℝ) * Real.pi = x0 * Real.pi := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hn
      exact (mul_right_cancel₀ hpi hn').symm
    have hnabs_lt_one : |(n : ℝ)| < 1 := by
      have hx0_lt_one : |x0| < 1 := by linarith [hx0S.2, hδ₀]
      simpa [hx0eqn] using hx0_lt_one
    have hn_bounds : (-1 : ℤ) < n ∧ n < 1 := by
      constructor
      · exact_mod_cast (abs_lt.mp hnabs_lt_one).1
      · exact_mod_cast (abs_lt.mp hnabs_lt_one).2
    have hn_zero : n = 0 := by omega
    have : δ ≤ (0 : ℝ) := by
      simpa [hx0eqn, hn_zero] using hx0S.1
    linarith
  have hm_pos : 0 < f x0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0_nonzero)
  refine ⟨f x0, hm_pos, ?_⟩
  intro x hxδ hx1δ
  have hxS : x ∈ S := ⟨hxδ, hx1δ⟩
  have hmin : f x0 ≤ f x := hx0min hxS
  simpa [f] using hmin

/-- Helper for Lemma 5.4.6: combining the norm-square Fejér formula,
geometric-sum denominator estimate, and annulus denominator lower bound gives
the quantitative tail estimate. -/
lemma helperForLemma_5_4_6_fejer_tailBound_from_formula
    {δ mδ : ℝ} (hmδ : 0 < mδ)
    (hLower : ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 - δ →
      mδ ≤ ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖)
    (N : ℕ) (x : ℝ) (hxδ : δ ≤ |x|) (hx1 : |x| ≤ 1 - δ) :
    ‖helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))‖
      ≤ (4 / (mδ ^ 2)) / (N + 1 : ℝ) := by
  have hden_ge : mδ ≤ ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ := hLower x hxδ hx1
  have hden_pos : 0 < ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ :=
    lt_of_lt_of_le hmδ hden_ge
  have hxne : Complex.exp (Complex.I * (2 * Real.pi * x)) ≠ 1 := by
    intro hEq
    have : ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ = 0 := by
      simpa [hEq]
    exact (ne_of_gt hden_pos) this
  have hgeom := helperForLemma_5_4_6_geomSum_norm_le_two_div_normExpSubOne N x hxne
  rcases helperForLemma_5_4_6_fejer_eval_eq_normSqGeometricSum N x with ⟨hre, him⟩
  have hreal_nonneg : 0 ≤ (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re := by
    rw [hre]
    positivity
  have hnorm_eq_re :
      ‖helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))‖
        = (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re := by
    have hEq :
        helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))
          = ((helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hEq]
    simpa [Real.norm_eq_abs, abs_of_nonneg hreal_nonneg] using
      (Complex.norm_real ((helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re))
  have hmδ_ne : mδ ≠ 0 := ne_of_gt hmδ
  have hdiv_le : 2 / ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ ≤ 2 / mδ := by
    have h1 : 1 / ‖Complex.exp (Complex.I * (2 * Real.pi * x)) - 1‖ ≤ 1 / mδ :=
      one_div_le_one_div_of_le hmδ hden_ge
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (2 : ℝ) by norm_num)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2
  have hA_nonneg :
      0 ≤ ‖Finset.sum (Finset.range (N + 1))
        (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ :=
    norm_nonneg _
  have hB_nonneg : 0 ≤ 2 / mδ := by positivity
  have hAB :
      ‖Finset.sum (Finset.range (N + 1))
        (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖
        ≤ 2 / mδ :=
    le_trans hgeom hdiv_le
  have hsq_le :
      ‖Finset.sum (Finset.range (N + 1))
        (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ ^ 2
        ≤ (2 / mδ) ^ 2 := by
    calc
      ‖Finset.sum (Finset.range (N + 1))
        (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ ^ 2
          = ‖Finset.sum (Finset.range (N + 1))
              (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ *
            ‖Finset.sum (Finset.range (N + 1))
              (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ := by ring
      _ ≤ (2 / mδ) *
            ‖Finset.sum (Finset.range (N + 1))
              (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ :=
            mul_le_mul_of_nonneg_right hAB hA_nonneg
      _ ≤ (2 / mδ) * (2 / mδ) :=
            mul_le_mul_of_nonneg_left hAB hB_nonneg
      _ = (2 / mδ) ^ 2 := by ring
  have hsq_eq : (2 / mδ) ^ 2 = 4 / (mδ ^ 2) := by
    field_simp [hmδ_ne]
    ring
  have hsq_bound :
      ‖Finset.sum (Finset.range (N + 1))
        (fun j => (Complex.exp (Complex.I * (2 * Real.pi * x))) ^ j)‖ ^ 2
        ≤ 4 / (mδ ^ 2) := by
    exact hsq_le.trans (by simpa [hsq_eq])
  have hNfac_nonneg : 0 ≤ (1 : ℝ) / (N + 1 : ℝ) := by positivity
  have hre_bound :
      (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re
        ≤ ((1 : ℝ) / (N + 1 : ℝ)) * (4 / (mδ ^ 2)) := by
    rw [hre]
    exact mul_le_mul_of_nonneg_left hsq_bound hNfac_nonneg
  calc
    ‖helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))‖
        = (helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))).re := hnorm_eq_re
    _ ≤ ((1 : ℝ) / (N + 1 : ℝ)) * (4 / (mδ ^ 2)) := hre_bound
    _ = (4 / (mδ ^ 2)) / (N + 1 : ℝ) := by ring

/-- Helper for Lemma 5.4.6: Fejér kernels are pointwise real/nonnegative and satisfy
uniform annulus decay `‖F_N(x)‖ ≤ Cδ/(N+1)` when `δ ≤ |x| ≤ 1-δ`. -/
lemma helperForLemma_5_4_6_fejer_real_nonneg_and_tailBound
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < (1 / 2 : ℝ)) :
    (∀ N : ℕ,
      ∀ x : AddCircle (1 : ℝ),
        (helperForLemma_5_4_6_fejerPolynomial N x).im = 0 ∧
          0 ≤ (helperForLemma_5_4_6_fejerPolynomial N x).re) ∧
      ∃ Cδ > 0,
        ∀ N : ℕ,
        ∀ x : ℝ,
          δ ≤ |x| → |x| ≤ 1 - δ →
            ‖helperForLemma_5_4_6_fejerPolynomial N (x : AddCircle (1 : ℝ))‖
              ≤ Cδ / (N + 1 : ℝ) := by
  constructor
  · intro N x
    have hsurj : Function.Surjective (fun t : ℝ => (t : AddCircle (1 : ℝ))) := by
      simpa [AddCircle] using
        (QuotientAddGroup.mk_surjective (α := ℝ) (s := AddSubgroup.zmultiples (1 : ℝ)))
    rcases hsurj x with ⟨t, rfl⟩
    rcases helperForLemma_5_4_6_fejer_eval_eq_normSqGeometricSum N t with ⟨hre, him⟩
    refine ⟨?_, ?_⟩
    · simpa using him
    · rw [hre]
      positivity
  · rcases helperForLemma_5_4_6_annulus_expSubOne_lowerBound hδ₀ hδ₁ with
      ⟨mδ, hmδpos, hLower⟩
    refine ⟨4 / (mδ ^ 2), ?_, ?_⟩
    · positivity
    · intro N x hxδ hx1
      simpa using
        helperForLemma_5_4_6_fejer_tailBound_from_formula hmδpos hLower N x hxδ hx1

/-- Helper for Lemma 5.4.6: quantitative Fejér-kernel concentration yields a periodic
`(ε, δ)` approximation to the identity for some index. -/
lemma helperForLemma_5_4_6_exists_fejerPeriodicApproximation
    (ε δ : ℝ) (hε : 0 < ε) (hδ₀ : 0 < δ) (hδ₁ : δ < (1 / 2 : ℝ)) :
    ∃ N : ℕ, IsPeriodicApproximationToIdentity ε δ (helperForLemma_5_4_6_fejerPolynomial N) := by
  rcases helperForLemma_5_4_6_fejer_real_nonneg_and_tailBound hδ₀ hδ₁ with
    ⟨hRealNonneg, Cδ, hCδpos, hTailBound⟩
  rcases helperForLemma_5_4_6_chooseIndexFromTailBound hε hCδpos with ⟨N, hNchoice⟩
  refine ⟨N, ?_⟩
  refine ⟨hε, hδ₀, hδ₁, hRealNonneg N, helperForLemma_5_4_6_fejer_mass_one N, ?_⟩
  intro x hx₀ hx₁
  have hBound := hTailBound N x hx₀ hx₁
  exact lt_of_le_of_lt hBound hNchoice

/-- Lemma 5.4.6: for every `ε > 0` and `0 < δ < 1/2`, there exists a
trigonometric polynomial `P` that is a periodic `(ε, δ)` approximation to the
identity. -/
lemma exists_trigonometricPolynomial_isPeriodicApproximationToIdentity
    (ε δ : ℝ) (hε : 0 < ε) (hδ₀ : 0 < δ) (hδ₁ : δ < (1 / 2 : ℝ)) :
    ∃ P : C(AddCircle (1 : ℝ), ℂ),
      IsTrigonometricPolynomial P ∧ IsPeriodicApproximationToIdentity ε δ P := by
  rcases helperForLemma_5_4_6_exists_fejerPeriodicApproximation ε δ hε hδ₀ hδ₁ with ⟨N, hN⟩
  refine ⟨helperForLemma_5_4_6_fejerPolynomial N, ?_, hN⟩
  exact helperForLemma_5_4_6_fejer_isTrig N

end Section04
end Chap05
