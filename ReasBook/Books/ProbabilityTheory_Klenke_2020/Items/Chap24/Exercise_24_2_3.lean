/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_60

open MeasureTheory
open Filter
open scoped Topology

noncomputable section

namespace ProbabilityTheory

-- Semantic recall note: `lean_leansearch` did not surface a ready-made owner for this exact
-- negative-binomial stochastic-order criterion, so the file keeps the source-facing statement in
-- the chapter's public nat-law embedding `ProbabilityMeasure.toFin1Real`.
/-- Helper for Exercise 24.2.3: the singleton mass of `negativeBinomialMeasure r p hr hp hp_le_one`
is the textbook negative-binomial mass `negativeBinomialMass r p k`. -/
private lemma negativeBinomialMeasure_apply_singleton
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) (k : ℕ) :
    negativeBinomialMeasure r p hr hp hp_le_one ({k} : Set ℕ) =
      ENNReal.ofReal (negativeBinomialMass r p k) := by
  -- Proof comment: rewrite `negativeBinomialMeasure` as the measure attached to the canonical PMF.
  simpa [negativeBinomialMeasure, negativeBinomialPMF_apply] using
    (PMF.toMeasure_apply_singleton (negativeBinomialPMF r p hr hp hp_le_one) k
      (measurableSet_singleton k))

/-- Helper for Exercise 24.2.3: taking `toReal` of a singleton atom in
`negativeBinomialMeasure r p hr hp hp_le_one` removes the `ENNReal.ofReal` wrapper. -/
private lemma negativeBinomialMeasure_apply_singleton_toReal
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) (k : ℕ) :
    (negativeBinomialMeasure r p hr hp hp_le_one ({k} : Set ℕ)).toReal =
      negativeBinomialMass r p k := by
  -- Proof comment: the admissible parameters make every singleton mass nonnegative.
  rw [negativeBinomialMeasure_apply_singleton, ENNReal.toReal_ofReal
    (negativeBinomialMass_nonneg hr hp hp_le_one k)]

/-- Helper for Exercise 24.2.3: the first nontrivial nat upper tail is the complement of the
atom at `0`. -/
private lemma natMeasure_tail_Ici_one_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (μ (Set.Ici 1)).toReal = 1 - (μ ({0} : Set ℕ)).toReal := by
  have hcompl : ((Set.Ici (1 : ℕ))ᶜ : Set ℕ) = ({0} : Set ℕ) := by
    ext n
    simp
  have hsplit :
      μ.real (Set.Ici 1) + μ.real ({0} : Set ℕ) = 1 := by
    calc
      μ.real (Set.Ici 1) + μ.real ({0} : Set ℕ)
          = μ.real (Set.Ici 1) + μ.real ((Set.Ici (1 : ℕ))ᶜ) := by
              rw [hcompl]
      _ = μ.real Set.univ := by
            simpa using
              (MeasureTheory.measureReal_add_measureReal_compl
                (μ := μ) (s := Set.Ici (1 : ℕ)) measurableSet_Ici)
      _ = 1 := by simp [Measure.real_def]
  have htail : μ.real (Set.Ici 1) = 1 - μ.real ({0} : Set ℕ) := by
    linarith
  simpa [Measure.real_def] using htail

/-- Helper for Exercise 24.2.3: for any probability measure on `ℕ`, the tail `μ([k, ∞))` is the
complement of the finite prefix `{0, ..., k - 1}`. -/
private lemma natMeasure_tail_Ici_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (μ (Set.Ici k)).toReal = 1 - ∑ i ∈ Finset.range k, (μ ({i} : Set ℕ)).toReal := by
  have hcompl : ((Set.Ici k : Set ℕ)ᶜ) = (((Finset.range k : Finset ℕ) : Set ℕ)) := by
    -- Proof comment: on `ℕ`, being outside `Ici k` means lying in the first `k` values.
    ext i
    simp
  have hsplit :
      μ.real (Set.Ici k) + ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ) = 1 := by
    -- Proof comment: split the total mass into the tail and its finite complement.
    calc
      μ.real (Set.Ici k) + ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ)
          = μ.real (Set.Ici k) + μ.real (((Finset.range k : Finset ℕ) : Set ℕ)) := by
              rw [← MeasureTheory.sum_measureReal_singleton (μ := μ) (s := Finset.range k)]
      _ = μ.real (Set.Ici k) + μ.real ((Set.Ici k : Set ℕ)ᶜ) := by
            rw [hcompl]
      _ = μ.real Set.univ := by
            simpa using
              (MeasureTheory.measureReal_add_measureReal_compl
                (μ := μ) (s := (Set.Ici k : Set ℕ)) measurableSet_Ici)
      _ = 1 := by
            simp [Measure.real_def]
  have htail : μ.real (Set.Ici k) = 1 - ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ) := by
    -- Proof comment: isolate the tail term from the partition identity.
    linarith
  simpa [Measure.real_def] using htail

/-- Helper for Exercise 24.2.3: each nat tail splits into its first singleton atom and the next
tail. -/
private lemma natTail_succ_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (μ (Set.Ici n)).toReal = (μ ({n} : Set ℕ)).toReal + (μ (Set.Ici (n + 1))).toReal := by
  have hdisj : Disjoint ({n} : Set ℕ) (Set.Ici (n + 1)) := by
    rw [Set.disjoint_singleton_left]
    simp
  have hunion : ({n} : Set ℕ) ∪ Set.Ici (n + 1) = Set.Ici n := by
    -- Proof comment: a point in `Ici n` is either exactly `n` or lies in the shifted tail.
    ext k
    simp
    omega
  -- Proof comment: rewrite the tail as a disjoint union and take `toReal`.
  rw [← Measure.real_def, ← Measure.real_def, ← Measure.real_def]
  rw [← hunion, MeasureTheory.measureReal_union hdisj measurableSet_Ici]

/-- Helper for Exercise 24.2.3: the upper tails of a probability measure on `ℕ` vanish at
infinity. -/
private lemma natTail_toReal_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Filter.Tendsto (fun n : ℕ ↦ (μ (Set.Ici n)).toReal) Filter.atTop (nhds 0) := by
  have hanti : Antitone (fun n : ℕ ↦ (Set.Ici n : Set ℕ)) := by
    intro m n hmn
    exact Set.Ici_subset_Ici.mpr hmn
  have hempty : (⋂ n : ℕ, (Set.Ici n : Set ℕ)) = ∅ := by
    -- Proof comment: no natural number lies in every upper tail.
    apply Set.eq_empty_iff_forall_notMem.2
    intro k hk
    have hall : ∀ n : ℕ, n ≤ k := by
      simpa [Set.mem_iInter, Set.mem_Ici] using hk
    exact Nat.not_succ_le_self k (hall (k + 1))
  have htail :
      Filter.Tendsto (fun n : ℕ ↦ μ (Set.Ici n : Set ℕ)) Filter.atTop
        (nhds (μ (⋂ n : ℕ, (Set.Ici n : Set ℕ)))) := by
    exact
      tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ by measurability) hanti
        ⟨0, measure_ne_top μ (Set.Ici 0)⟩
  have htail_zero :
      Filter.Tendsto (fun n : ℕ ↦ μ (Set.Ici n : Set ℕ)) Filter.atTop (nhds 0) := by
    simpa [hempty] using htail
  -- Proof comment: the tails are finite, so continuity of `toReal` at `0` finishes.
  simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail_zero

/-- Helper for Exercise 24.2.3: eventual singleton domination on a nat tail forces nonnegative
tail differences from that point onward. -/
private lemma natTail_difference_nonneg_of_eventualSingletonLE
    (μ₁ μ₂ : Measure ℕ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {N : ℕ}
    (hright : ∀ n ≥ N, (μ₁ ({n} : Set ℕ)).toReal ≤ (μ₂ ({n} : Set ℕ)).toReal) :
    ∀ n ≥ N, 0 ≤ (μ₂ (Set.Ici n)).toReal - (μ₁ (Set.Ici n)).toReal := by
  let d : ℕ → ℝ := fun n ↦ (μ₂ (Set.Ici n)).toReal - (μ₁ (Set.Ici n)).toReal
  have hdLimit : Filter.Tendsto d Filter.atTop (nhds 0) := by
    -- Proof comment: both tail sequences tend to `0`, hence so does their difference.
    simpa [d] using (natTail_toReal_tendsto_zero μ₂).sub (natTail_toReal_tendsto_zero μ₁)
  have hdAnti : Antitone (fun m : ℕ ↦ d (m + N)) := by
    refine antitone_nat_of_succ_le ?_
    intro m
    have hatom :
        (μ₁ ({m + N} : Set ℕ)).toReal ≤ (μ₂ ({m + N} : Set ℕ)).toReal := by
      exact hright (m + N) (by omega)
    -- Proof comment: one tail step subtracts the same singleton on both sides.
    dsimp [d]
    rw [natTail_succ_toReal (μ := μ₁) (n := m + N), natTail_succ_toReal (μ := μ₂) (n := m + N)]
    ring_nf
    linarith
  intro n hn
  have hdShift : Filter.Tendsto (fun m : ℕ ↦ d (m + N)) Filter.atTop (nhds 0) := by
    simpa [Function.comp, add_comm, add_left_comm, add_assoc] using
      hdLimit.comp (tendsto_add_atTop_nat N)
  have hnonnegShift : 0 ≤ d ((n - N) + N) := hdAnti.le_of_tendsto hdShift (n - N)
  simpa [Nat.sub_add_cancel hn, d] using hnonnegShift

/-- Helper for Exercise 24.2.3: a single-crossing comparison of singleton masses implies the
corresponding upper-tail comparison for probability measures on `ℕ`. -/
private lemma natUpperTail_le_of_singleCrossing
    (μ₁ μ₂ : Measure ℕ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {N : ℕ}
    (hleft : ∀ n < N, (μ₂ ({n} : Set ℕ)).toReal ≤ (μ₁ ({n} : Set ℕ)).toReal)
    (hright : ∀ n ≥ N, (μ₁ ({n} : Set ℕ)).toReal ≤ (μ₂ ({n} : Set ℕ)).toReal) :
    ∀ k : ℕ, μ₁ (Set.Ici k) ≤ μ₂ (Set.Ici k) := by
  intro k
  by_cases hk : N ≤ k
  · have hnonneg :
        0 ≤ (μ₂ (Set.Ici k)).toReal - (μ₁ (Set.Ici k)).toReal :=
      natTail_difference_nonneg_of_eventualSingletonLE μ₁ μ₂ hright k hk
    have htail_real :
        (μ₁ (Set.Ici k)).toReal ≤ (μ₂ (Set.Ici k)).toReal := by
      linarith
    exact
      (ENNReal.toReal_le_toReal (measure_ne_top μ₁ (Set.Ici k))
        (measure_ne_top μ₂ (Set.Ici k))).1 htail_real
  · have hk' : k < N := Nat.lt_of_not_ge hk
    have hprefix :
        ∑ i ∈ Finset.range k, (μ₂ ({i} : Set ℕ)).toReal ≤
          ∑ i ∈ Finset.range k, (μ₁ ({i} : Set ℕ)).toReal := by
      -- Proof comment: before the crossing index, the singleton comparison is termwise.
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hleft i (lt_trans (Finset.mem_range.mp hi) hk')
    have htail_real :
        (μ₁ (Set.Ici k)).toReal ≤ (μ₂ (Set.Ici k)).toReal := by
      rw [natMeasure_tail_Ici_toReal (μ := μ₁) k, natMeasure_tail_Ici_toReal (μ := μ₂) k]
      linarith
    exact
      (ENNReal.toReal_le_toReal (measure_ne_top μ₁ (Set.Ici k))
        (measure_ne_top μ₂ (Set.Ici k))).1 htail_real

/-- Helper for Exercise 24.2.3: the canonical negative-binomial mass at `0` is `p ^ r`. -/
private lemma negativeBinomialMass_zero_local
    (r p : ℝ) :
    negativeBinomialMass r p 0 = p ^ r := by
  -- Proof comment: the zeroth binomial coefficient and all zeroth powers simplify to `1`.
  simp [negativeBinomialMass]

/-- Helper for Exercise 24.2.3: the zero atom of `negativeBinomialMeasure r p hr hp hp_le_one`
is `p ^ r`. -/
private lemma negativeBinomialMeasure_apply_zero_toReal
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    (negativeBinomialMeasure r p hr hp hp_le_one ({0} : Set ℕ)).toReal = p ^ r := by
  -- Proof comment: specialize the singleton-mass identity at `0`.
  rw [negativeBinomialMeasure_apply_singleton_toReal]
  simpa using negativeBinomialMass_zero_local r p

/-- Helper for Exercise 24.2.3: when `p = 1`, the negative-binomial law is concentrated at `0`. -/
private lemma negativeBinomialMeasure_eq_dirac_zero_of_one
    (r : ℝ) (hr : 0 < r) :
    negativeBinomialMeasure r 1 hr zero_lt_one le_rfl = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  cases n with
  | zero =>
      -- Proof comment: the atom at `0` is exactly `1`.
      rw [negativeBinomialMeasure_apply_singleton]
      simp [negativeBinomialMass_zero_local]
  | succ k =>
      -- Proof comment: every positive atom vanishes because the factor `(1 - p)^(k + 1)` is `0`.
      rw [negativeBinomialMeasure_apply_singleton]
      have hmass : negativeBinomialMass r 1 (k + 1) = 0 := by
        simp [negativeBinomialMass]
      rw [hmass]
      simp

/-- Helper for Exercise 24.2.3: the negative-binomial mass is the multichoose factor times the
success and failure powers. -/
private lemma negativeBinomialMass_eq_multichoose
    (r p : ℝ) (k : ℕ) :
    negativeBinomialMass r p k =
      Ring.multichoose r k * p ^ r * (1 - p) ^ k := by
  -- Proof comment: `Ring.choose_neg'` rewrites the signed binomial coefficient into
  -- `Ring.multichoose`, and the two `(-1)^k` factors cancel.
  rw [negativeBinomialMass, Ring.choose_neg']
  have hzsmul :
      (k : ℤ).negOnePow • Ring.multichoose r k = (-1 : ℝ) ^ k * Ring.multichoose r k := by
    rcases Nat.even_or_odd k with hEven | hOdd
    · rcases hEven with ⟨m, rfl⟩
      rw [Int.negOnePow_even _ ((Int.even_coe_nat (m + m)).2 (Even.add_self m))]
      simp
    · rcases hOdd with ⟨m, rfl⟩
      rw [Int.negOnePow_odd _ ((Int.odd_coe_nat (2 * m + 1)).2 (odd_two_mul_add_one m))]
      simp [pow_add]
  have hsign : (((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k) = 1 := by
    rw [← mul_pow]
    simp
  rw [hzsmul]
  calc
    (((-1 : ℝ) ^ k * Ring.multichoose r k) * (-1 : ℝ) ^ k) * p ^ r * (1 - p) ^ k
        = ((((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k) * Ring.multichoose r k) * p ^ r * (1 - p) ^ k := by
            ring
    _ = ((1 * Ring.multichoose r k) * p ^ r) * (1 - p) ^ k := by
          rw [hsign]
    _ = Ring.multichoose r k * p ^ r * (1 - p) ^ k := by
          ring

/-- Helper for Exercise 24.2.3: the multichoose coefficients satisfy the standard one-step
ratio formula. -/
private lemma multichoose_succ_ratio
    (r : ℝ) (k : ℕ) :
    Ring.multichoose r (k + 1) =
      Ring.multichoose r k * (((k : ℝ) + r) / (k + 1)) := by
  have hraw :
      ((Nat.choose (k + 1) 1 : ℝ)) * Ring.choose (r + k) (k + 1) =
        Ring.choose (r + k) 1 * Ring.choose (r + k - 1) k := by
    simpa [nsmul_eq_mul] using
      (Ring.choose_smul_choose (r := r + k) (n := k + 1) (k := 1) (by omega : 1 ≤ k + 1))
  have hchoose :
      ((k + 1 : ℝ)) * Ring.multichoose r (k + 1) =
        ((k : ℝ) + r) * Ring.multichoose r k := by
    -- Proof comment: the textbook ratio is the `k = 1` instance of the generic binomial-ring
    -- identity `choose_smul_choose`.
    have harg : r + ((k + 1 : ℕ) : ℝ) - 1 = r + k := by
      rw [Nat.cast_add]
      ring
    calc
      ((k + 1 : ℝ)) * Ring.multichoose r (k + 1)
          = ((Nat.choose (k + 1) 1 : ℝ)) * Ring.choose (r + k) (k + 1) := by
              rw [Ring.multichoose_eq, harg]
              norm_num
      _ = Ring.choose (r + k) 1 * Ring.choose (r + k - 1) k := hraw
      _ = ((k : ℝ) + r) * Ring.multichoose r k := by
            simp [Ring.multichoose_eq, Ring.choose_one_right, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  calc
    Ring.multichoose r (k + 1)
        = (((k : ℝ) + r) * Ring.multichoose r k) / (k + 1) := by
            apply (eq_div_iff hk).2
            simpa [mul_assoc, mul_left_comm, mul_comm] using hchoose
    _ = Ring.multichoose r k * (((k : ℝ) + r) / (k + 1)) := by
          field_simp [hk]

/-- Helper for Exercise 24.2.3: successive negative-binomial masses differ by the canonical
ratio `((k + r) / (k + 1)) * (1 - p)`. -/
private lemma negativeBinomialMass_succ_ratio
    (r p : ℝ) (k : ℕ) :
    negativeBinomialMass r p (k + 1) =
      negativeBinomialMass r p k * (((k : ℝ) + r) / (k + 1)) * (1 - p) := by
  -- Proof comment: rewrite both masses in multichoose form and isolate the extra `(1 - p)`
  -- factor coming from the power at `k + 1`.
  calc
    negativeBinomialMass r p (k + 1)
        = Ring.multichoose r (k + 1) * p ^ r * (1 - p) ^ (k + 1) := by
            rw [negativeBinomialMass_eq_multichoose]
    _ = (Ring.multichoose r k * (((k : ℝ) + r) / (k + 1))) * p ^ r * ((1 - p) ^ k * (1 - p)) := by
          rw [multichoose_succ_ratio, pow_succ]
    _ = (Ring.multichoose r k * p ^ r * (1 - p) ^ k) * (((k : ℝ) + r) / (k + 1)) * (1 - p) := by
          ring
    _ = negativeBinomialMass r p k * (((k : ℝ) + r) / (k + 1)) * (1 - p) := by
          rw [negativeBinomialMass_eq_multichoose]

/-- Helper for Exercise 24.2.3: in the nondegenerate regime `0 < p < 1`, every negative-binomial
singleton mass is strictly positive. -/
private lemma negativeBinomialMass_pos_of_lt_one
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_lt_one : p < 1) (k : ℕ) :
    0 < negativeBinomialMass r p k := by
  induction k with
  | zero =>
      -- Proof comment: the zeroth atom is `p ^ r`, which is positive on `(0, ∞)`.
      rw [negativeBinomialMass_zero_local]
      exact Real.rpow_pos_of_pos hp r
  | succ k hk =>
      -- Proof comment: the recurrence multiplies the previous positive atom by three positive
      -- factors.
      rw [negativeBinomialMass_succ_ratio]
      have hratio : 0 < (((k : ℝ) + r) / (k + 1)) := by
        positivity
      have hfail : 0 < 1 - p := sub_pos.mpr hp_lt_one
      exact mul_pos (mul_pos hk hratio) hfail

/-- Helper for Exercise 24.2.3: dividing the one-step mass recurrences yields the canonical
ratio recursion for negative-binomial singleton masses. -/
private lemma negativeBinomialMassRatio_succ
    (r₁ r₂ p₁ p₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₁_lt_one : p₁ < 1) (hp₂_lt_one : p₂ < 1)
    (n : ℕ) :
    negativeBinomialMass r₁ p₁ (n + 1) / negativeBinomialMass r₂ p₂ (n + 1) =
      (negativeBinomialMass r₁ p₁ n / negativeBinomialMass r₂ p₂ n) *
        ((((n : ℝ) + r₁) / ((n : ℝ) + r₂)) * ((1 - p₁) / (1 - p₂))) := by
  have hm₁ : 0 < negativeBinomialMass r₁ p₁ n :=
    negativeBinomialMass_pos_of_lt_one r₁ p₁ hr₁ hp₁ hp₁_lt_one n
  have hm₂ : 0 < negativeBinomialMass r₂ p₂ n :=
    negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n
  have hfail₁ : 0 < 1 - p₁ := sub_pos.mpr hp₁_lt_one
  have hfail₂ : 0 < 1 - p₂ := sub_pos.mpr hp₂_lt_one
  have hnr : 0 < ((n : ℝ) + r₂) := by positivity
  have hnp1 : (0 : ℝ) < n + 1 := by positivity
  rw [negativeBinomialMass_succ_ratio, negativeBinomialMass_succ_ratio]
  field_simp [hm₁.ne', hm₂.ne', hfail₂.ne', hnr.ne', hnp1.ne']

/-- Helper for Exercise 24.2.3: the rational factor `((n + r₁) / (n + r₂))` is monotone in `n`
when `r₁ ≤ r₂`. -/
private lemma negativeBinomialMassRatioFactor_monotone
    (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hrr : r₁ ≤ r₂) :
    Monotone (fun n : ℕ ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂))) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  have hden₁ : 0 < ((n : ℝ) + r₂) := by positivity
  have hden₂ : 0 < (((n + 1 : ℕ) : ℝ) + r₂) := by positivity
  let a : ℝ := (((n : ℝ) + r₁) / ((n : ℝ) + r₂))
  let b : ℝ := ((((n + 1 : ℕ) : ℝ) + r₁) / ((((n + 1 : ℕ) : ℝ) + r₂)))
  let denom : ℝ := (((n : ℝ) + r₂) * ((((n + 1 : ℕ) : ℝ) + r₂)))
  -- Proof comment: after clearing the positive denominators, the remaining inequality is exactly
  -- `r₁ ≤ r₂`.
  have hdiff : 0 ≤ b - a := by
    have hmul : (b - a) * denom = r₂ - r₁ := by
      dsimp [a, b, denom]
      field_simp [hden₁.ne', hden₂.ne']
      norm_num [Nat.cast_add]
      ring
    have hprod : 0 < denom := by
      dsimp [denom]
      positivity
    nlinarith [hmul, hrr, hprod]
  exact sub_nonneg.mp hdiff

/-- Helper for Exercise 24.2.3: the same rational factor is antitone in `n` when `r₂ ≤ r₁`. -/
private lemma negativeBinomialMassRatioFactor_antitone
    (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hrr : r₂ ≤ r₁) :
    Antitone (fun n : ℕ ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂))) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  have hden₁ : 0 < ((n : ℝ) + r₂) := by positivity
  have hden₂ : 0 < (((n + 1 : ℕ) : ℝ) + r₂) := by positivity
  let a : ℝ := (((n : ℝ) + r₁) / ((n : ℝ) + r₂))
  let b : ℝ := ((((n + 1 : ℕ) : ℝ) + r₁) / ((((n + 1 : ℕ) : ℝ) + r₂)))
  let denom : ℝ := (((n : ℝ) + r₂) * ((((n + 1 : ℕ) : ℝ) + r₂)))
  -- Proof comment: the same cleared-denominator identity reverses when `r₂ ≤ r₁`.
  have hdiff : 0 ≤ a - b := by
    have hmul : (a - b) * denom = r₁ - r₂ := by
      dsimp [a, b, denom]
      field_simp [hden₁.ne', hden₂.ne']
      norm_num [Nat.cast_add]
      ring
    have hprod : 0 < denom := by
      dsimp [denom]
      positivity
    nlinarith [hmul, hrr, hprod]
  exact sub_nonneg.mp hdiff

/-- Helper for Exercise 24.2.3: eventual strict domination of singleton masses on a nat tail
forces strict domination of the corresponding upper-tail mass. -/
private lemma natTail_lt_of_eventualSingletonLt
    (μ₁ μ₂ : Measure ℕ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {N : ℕ}
    (hstrict : ∀ n ≥ N, (μ₂ ({n} : Set ℕ)).toReal < (μ₁ ({n} : Set ℕ)).toReal) :
    (μ₂ (Set.Ici N)).toReal < (μ₁ (Set.Ici N)).toReal := by
  have htail_next :
      0 ≤ (μ₁ (Set.Ici (N + 1))).toReal - (μ₂ (Set.Ici (N + 1))).toReal := by
    have hle_next :
        ∀ n ≥ N + 1, (μ₂ ({n} : Set ℕ)).toReal ≤ (μ₁ ({n} : Set ℕ)).toReal := by
      intro n hn
      exact (hstrict n (by omega)).le
    simpa using
      natTail_difference_nonneg_of_eventualSingletonLE μ₂ μ₁ hle_next (N + 1) le_rfl
  have hatomN :
      (μ₂ ({N} : Set ℕ)).toReal < (μ₁ ({N} : Set ℕ)).toReal := hstrict N le_rfl
  -- Proof comment: the tail step at `N` is the strict singleton gap plus the nonnegative
  -- remaining-tail gap.
  rw [natTail_succ_toReal (μ := μ₁) (n := N), natTail_succ_toReal (μ := μ₂) (n := N)]
  linarith

/-- Helper for Exercise 24.2.3: the normalized step factor in the negative-binomial mass ratio
converges to the ratio of the failure probabilities. -/
private lemma negativeBinomialMassRatioFactor_tendsto
    (r₁ r₂ p₁ p₂ : ℝ) (hr₂ : 0 < r₂) :
    Tendsto
      (fun n : ℕ ↦
        (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) * ((1 - p₁) / (1 - p₂)))
      atTop
      (nhds ((1 - p₁) / (1 - p₂))) := by
  have hdiv_zero :
      Tendsto (fun n : ℕ ↦ (r₁ - r₂) / ((n : ℝ) + r₂)) atTop (nhds 0) := by
    have hinv :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + r₂)) atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ r₂ tendsto_natCast_atTop_atTop))
    -- Proof comment: multiplying the reciprocal tail by the fixed numerator still tends to `0`.
    simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      hinv.const_mul (r₁ - r₂)
  have hfactor_eq :
      ∀ n : ℕ,
        (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) =
          1 + (r₁ - r₂) / ((n : ℝ) + r₂) := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + r₂ := by positivity
    field_simp [hden.ne']
    ring
  have hfirst :
      Tendsto (fun n : ℕ ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂))) atTop (nhds 1) := by
    -- Proof comment: the rational factor is `1` plus a vanishing correction term.
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hfactor_eq n).symm) ?_
    simpa using tendsto_const_nhds.add hdiv_zero
  -- Proof comment: the full step factor is the previous rational term times a fixed constant.
  simpa [one_mul] using hfirst.mul tendsto_const_nhds

/-- Helper for Exercise 24.2.3: if `p₁ < p₂ < 1`, then the normalized step factor is eventually
bounded by some constant strictly below `1`. -/
private lemma negativeBinomialMassRatioFactor_eventually_le_const_of_ltParameter
    (r₁ r₂ p₁ p₂ : ℝ) (hr₁ : 0 < r₁) (_hr₂ : 0 < r₂)
    (hp₁ : 0 < p₁) (_hp₂ : 0 < p₂)
    (hp₁_lt_p₂ : p₁ < p₂) (hp₂_lt_one : p₂ < 1) :
    ∃ c : ℝ, ∃ N : ℕ,
      0 < c ∧ c < 1 ∧
        ∀ n ≥ N,
          (((n : ℝ) + r₂) / ((n : ℝ) + r₁)) * ((1 - p₂) / (1 - p₁)) ≤ c := by
  let q : ℝ := (1 - p₂) / (1 - p₁)
  let c : ℝ := (q + 1) / 2
  have hp₁_lt_one : p₁ < 1 := lt_trans hp₁_lt_p₂ hp₂_lt_one
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hp₂_lt_one) (sub_pos.mpr hp₁_lt_one)
  have hq_lt_one : q < 1 := by
    have hden : 0 < 1 - p₁ := sub_pos.mpr hp₁_lt_one
    exact (div_lt_one hden).2 (by linarith)
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hc_lt_one : c < 1 := by
    dsimp [c]
    linarith
  have hq_lt_c : q < c := by
    dsimp [c]
    linarith
  have hfactor_tendsto :
      Tendsto
        (fun n : ℕ ↦
          (((n : ℝ) + r₂) / ((n : ℝ) + r₁)) * ((1 - p₂) / (1 - p₁)))
        atTop
        (nhds q) := by
    simpa [q] using negativeBinomialMassRatioFactor_tendsto r₂ r₁ p₂ p₁ hr₁
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        (((n : ℝ) + r₂) / ((n : ℝ) + r₁)) * ((1 - p₂) / (1 - p₁)) ≤ c :=
    hfactor_tendsto.eventually_le_const hq_lt_c
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  exact ⟨c, N, hc_pos, hc_lt_one, hN⟩

/-- Helper for Exercise 24.2.3: once an antitone ratio sequence drops below `1`, that first
crossing index yields the full single-crossing decomposition. -/
private lemma singleCrossing_of_antitone_ratio
    {a : ℕ → ℝ} (ha_anti : Antitone a) (hcross : ∃ N : ℕ, a N ≤ 1) :
    ∃ N : ℕ, (∀ n < N, 1 < a n) ∧ (∀ n ≥ N, a n ≤ 1) := by
  let N := Nat.find hcross
  refine ⟨N, ?_, ?_⟩
  · intro n hn
    have hnot : ¬ a n ≤ 1 := by
      intro hle
      exact Nat.not_lt_of_ge (Nat.find_min' hcross hle) hn
    exact lt_of_not_ge hnot
  · intro n hn
    exact (ha_anti hn).trans (Nat.find_spec hcross)

/-- Helper for Exercise 24.2.3: if `p₁ < p₂`, then the first negative-binomial law eventually
dominates the second one on singleton atoms. -/
private lemma negativeBinomialEventualAtomDomination_of_ltParameter
    (r₁ r₂ p₁ p₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hp₁_lt_p₂ : p₁ < p₂) (hp₂_lt_one : p₂ < 1) :
    ∃ N, ∀ n ≥ N, negativeBinomialMass r₂ p₂ n < negativeBinomialMass r₁ p₁ n := by
  let a : ℕ → ℝ :=
    fun n ↦ negativeBinomialMass r₂ p₂ n / negativeBinomialMass r₁ p₁ n
  let f : ℕ → ℝ :=
    fun n ↦ (((n : ℝ) + r₂) / ((n : ℝ) + r₁)) * ((1 - p₂) / (1 - p₁))
  have hp₁_lt_one : p₁ < 1 := lt_trans hp₁_lt_p₂ hp₂_lt_one
  have ha_pos : ∀ n : ℕ, 0 < a n := by
    intro n
    dsimp [a]
    exact
      div_pos
        (negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n)
        (negativeBinomialMass_pos_of_lt_one r₁ p₁ hr₁ hp₁ hp₁_lt_one n)
  have ha_nonneg : ∀ n : ℕ, 0 ≤ a n := fun n ↦ (ha_pos n).le
  have hstep : ∀ n : ℕ, a (n + 1) = a n * f n := by
    intro n
    -- Proof comment: the ratio recurrence is exactly the normalized singleton-mass recursion.
    simpa [a, f] using
      negativeBinomialMassRatio_succ r₂ r₁ p₂ p₁ hr₂ hr₁ hp₂ hp₁ hp₂_lt_one hp₁_lt_one n
  obtain ⟨c, N₀, hc_pos, hc_lt_one, hN₀⟩ :=
    negativeBinomialMassRatioFactor_eventually_le_const_of_ltParameter
      r₁ r₂ p₁ p₂ hr₁ hr₂ hp₁ hp₂ hp₁_lt_p₂ hp₂_lt_one
  have hgeom :
      ∀ m : ℕ, a (N₀ + m) ≤ a N₀ * c ^ m := by
    intro m
    induction m with
    | zero =>
        -- Proof comment: the geometric comparison starts with equality at the base index.
        simp
    | succ m hm =>
        -- Proof comment: one more ratio step multiplies by a factor bounded by `c`.
        calc
          a (N₀ + (m + 1)) = a (N₀ + m) * f (N₀ + m) := by
            simpa [Nat.add_assoc] using hstep (N₀ + m)
          _ ≤ a (N₀ + m) * c := by
            exact mul_le_mul_of_nonneg_left (hN₀ (N₀ + m) (by omega)) (ha_nonneg _)
          _ ≤ (a N₀ * c ^ m) * c := by
            exact mul_le_mul_of_nonneg_right hm hc_pos.le
          _ = a N₀ * c ^ (m + 1) := by
            rw [pow_succ]
            ring
  have hgeom_tendsto :
      Tendsto (fun m : ℕ ↦ a N₀ * c ^ m) atTop (nhds 0) := by
    -- Proof comment: the explicit geometric upper bound decays to zero because `0 ≤ c < 1`.
    simpa using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc_pos.le hc_lt_one))
  have hEventuallySmall : ∀ᶠ m : ℕ in atTop, a N₀ * c ^ m < 1 :=
    hgeom_tendsto.eventually_lt_const zero_lt_one
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hEventuallySmall
  refine ⟨N₀ + M₀, ?_⟩
  intro n hn
  have hN₀_le_n : N₀ ≤ n := by omega
  have hm_ge : M₀ ≤ n - N₀ := by omega
  have hbound : a n ≤ a N₀ * c ^ (n - N₀) := by
    simpa [Nat.add_sub_of_le hN₀_le_n] using hgeom (n - N₀)
  have ha_lt_one : a n < 1 := lt_of_le_of_lt hbound (hM₀ (n - N₀) hm_ge)
  have hden_pos : 0 < negativeBinomialMass r₁ p₁ n :=
    negativeBinomialMass_pos_of_lt_one r₁ p₁ hr₁ hp₁ hp₁_lt_one n
  -- Proof comment: positivity of the denominator turns the ratio estimate back into an atom
  -- comparison.
  exact (div_lt_one hden_pos).1 (by simpa [a] using ha_lt_one)

/-- Helper for Exercise 24.2.3: in the difficult branch `r₂ < r₁`, the atom ratio still has a
single crossing because the step factor is antitone and eventually contracts below `1`. -/
private lemma negativeBinomialSingletonSingleCrossing_of_monotoneFactor
    (r₁ r₂ p₁ p₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hp₂_lt_p₁ : p₂ < p₁) (hp₁_lt_one : p₁ < 1)
    (hpow : p₂ ^ r₂ ≤ p₁ ^ r₁) (hrlt : r₂ < r₁) :
    ∃ N : ℕ,
      (∀ n < N, negativeBinomialMass r₂ p₂ n ≤ negativeBinomialMass r₁ p₁ n) ∧
      (∀ n ≥ N, negativeBinomialMass r₁ p₁ n ≤ negativeBinomialMass r₂ p₂ n) := by
  let a : ℕ → ℝ :=
    fun n ↦ negativeBinomialMass r₁ p₁ n / negativeBinomialMass r₂ p₂ n
  let f : ℕ → ℝ :=
    fun n ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) * ((1 - p₁) / (1 - p₂))
  have hp₂_lt_one : p₂ < 1 := lt_trans hp₂_lt_p₁ hp₁_lt_one
  have ha_pos : ∀ n : ℕ, 0 < a n := by
    intro n
    dsimp [a]
    exact
      div_pos
        (negativeBinomialMass_pos_of_lt_one r₁ p₁ hr₁ hp₁ hp₁_lt_one n)
        (negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n)
  have ha_nonneg : ∀ n : ℕ, 0 ≤ a n := fun n ↦ (ha_pos n).le
  have hstep : ∀ n : ℕ, a (n + 1) = a n * f n := by
    intro n
    -- Proof comment: the atom ratio follows the canonical one-step recurrence with factor `f`.
    simpa [a, f] using
      negativeBinomialMassRatio_succ r₁ r₂ p₁ p₂ hr₁ hr₂ hp₁ hp₂ hp₁_lt_one hp₂_lt_one n
  have hbase_anti :
      Antitone (fun n : ℕ ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂))) :=
    negativeBinomialMassRatioFactor_antitone r₁ r₂ hr₂ hrlt.le
  have hratio_nonneg : 0 ≤ (1 - p₁) / (1 - p₂) := by
    have hnum_nonneg : 0 ≤ 1 - p₁ := by
      linarith
    have hden_pos : 0 < 1 - p₂ := sub_pos.mpr hp₂_lt_one
    exact div_nonneg hnum_nonneg hden_pos.le
  have hf_anti : Antitone f := by
    intro m n hmn
    dsimp [f]
    exact mul_le_mul_of_nonneg_right (hbase_anti hmn) hratio_nonneg
  have hratio_lt_one : ((1 - p₁) / (1 - p₂)) < 1 := by
    have hden : 0 < 1 - p₂ := sub_pos.mpr hp₂_lt_one
    exact (div_lt_one hden).2 (by linarith)
  have hf_tendsto : Tendsto f atTop (nhds ((1 - p₁) / (1 - p₂))) := by
    simpa [f] using negativeBinomialMassRatioFactor_tendsto r₁ r₂ p₁ p₂ hr₂
  have hEventuallyFactor : ∀ᶠ n : ℕ in atTop, f n ≤ 1 :=
    hf_tendsto.eventually_le_const hratio_lt_one
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hEventuallyFactor
  obtain ⟨N₀, hprefix_f, htail_f⟩ :=
    singleCrossing_of_antitone_ratio hf_anti ⟨N₁, hN₁ N₁ le_rfl⟩
  have hzero : 1 ≤ a 0 := by
    have hden_pos : 0 < p₂ ^ r₂ := Real.rpow_pos_of_pos hp₂ r₂
    -- Proof comment: the zero atom already has the correct orientation by the hypothesis
    -- `p₂ ^ r₂ ≤ p₁ ^ r₁`.
    simpa [a, negativeBinomialMass_zero_local] using (one_le_div hden_pos).2 hpow
  have ha_prefix : ∀ n < N₀, 1 ≤ a n := by
    intro n hn
    induction n with
    | zero =>
        exact hzero
    | succ n ih =>
        have hprev : 1 ≤ a n := ih (by omega)
        have hfactor : 1 ≤ f n := (hprefix_f n (by omega)).le
        -- Proof comment: before the factor crosses below `1`, each step preserves the ratio
        -- inequality `a n ≥ 1`.
        calc
          1 ≤ a n * f n := by
            have hmul : 1 * 1 ≤ a n * f n :=
              mul_le_mul hprev hfactor (by positivity) (ha_pos n).le
            simpa using hmul
          _ = a (n + 1) := by
            symm
            simpa using hstep n
  obtain ⟨M, hM⟩ :=
    negativeBinomialEventualAtomDomination_of_ltParameter
      r₂ r₁ p₂ p₁ hr₂ hr₁ hp₂ hp₁ hp₂_lt_p₁ hp₁_lt_one
  let aTail : ℕ → ℝ := fun m ↦ a (N₀ + m)
  have haTail_anti : Antitone aTail := by
    refine antitone_nat_of_succ_le ?_
    intro m
    -- Proof comment: after the first factor crossing, every later step multiplies by at most `1`.
    calc
      aTail (m + 1) = aTail m * f (N₀ + m) := by
        dsimp [aTail]
        simpa [Nat.add_assoc] using hstep (N₀ + m)
      _ ≤ aTail m * 1 := by
        exact mul_le_mul_of_nonneg_left (htail_f (N₀ + m) (by omega)) (ha_nonneg _)
      _ = aTail m := by
        ring
  have hcross_tail : ∃ K : ℕ, aTail K ≤ 1 := by
    refine ⟨max M N₀ - N₀, ?_⟩
    have hlt : a (max M N₀) < 1 := by
      have hmass_lt :
          negativeBinomialMass r₁ p₁ (max M N₀) <
            negativeBinomialMass r₂ p₂ (max M N₀) :=
        hM (max M N₀) (le_max_left _ _)
      have hden_pos :
          0 < negativeBinomialMass r₂ p₂ (max M N₀) :=
        negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one (max M N₀)
      exact (div_lt_one hden_pos).2 hmass_lt
    have hEq : N₀ + (max M N₀ - N₀) = max M N₀ := Nat.add_sub_of_le (le_max_right _ _)
    simpa [aTail, hEq] using hlt.le
  obtain ⟨K, hprefix_tail, htail_tail⟩ :=
    singleCrossing_of_antitone_ratio haTail_anti hcross_tail
  have hleft_of_ratio :
      ∀ {n : ℕ}, 1 ≤ a n → negativeBinomialMass r₂ p₂ n ≤ negativeBinomialMass r₁ p₁ n := by
    intro n hn
    have hden_pos : 0 < negativeBinomialMass r₂ p₂ n :=
      negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n
    exact (one_le_div hden_pos).1 (by simpa [a] using hn)
  have hright_of_ratio :
      ∀ {n : ℕ}, a n ≤ 1 → negativeBinomialMass r₁ p₁ n ≤ negativeBinomialMass r₂ p₂ n := by
    intro n hn
    have hden_pos : 0 < negativeBinomialMass r₂ p₂ n :=
      negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n
    exact (div_le_one hden_pos).1 (by simpa [a] using hn)
  refine ⟨N₀ + K, ?_⟩
  constructor
  · intro n hn
    by_cases hn₀ : n < N₀
    · -- Proof comment: before the first factor crossing, the atom ratio stays at least `1`.
      exact hleft_of_ratio (ha_prefix n hn₀)
    · have hN₀_le_n : N₀ ≤ n := Nat.le_of_not_gt hn₀
      have hm_lt : n - N₀ < K := by omega
      have hEq : N₀ + (n - N₀) = n := Nat.add_sub_of_le hN₀_le_n
      have hratio : 1 ≤ a n := by
        simpa [aTail, hEq] using (hprefix_tail (n - N₀) hm_lt).le
      exact hleft_of_ratio hratio
  · intro n hn
    have hN₀_le_n : N₀ ≤ n := by omega
    have hm_ge : K ≤ n - N₀ := by omega
    have hEq : N₀ + (n - N₀) = n := Nat.add_sub_of_le hN₀_le_n
    -- Proof comment: once the shifted tail ratio crosses below `1`, every later atom comparison
    -- has the reversed orientation.
    have hratio : a n ≤ 1 := by
      simpa [aTail, hEq] using htail_tail (n - N₀) hm_ge
    exact hright_of_ratio hratio

/-- Helper for Exercise 24.2.3: when the success parameter is fixed, the singleton masses still
have a single crossing in the shape parameter. -/
private lemma negativeBinomialMass_singleCrossing_of_eqParameter
    (r₁ r₂ p : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp : 0 < p) (hp_lt_one : p < 1)
    (hpow : p ^ r₁ ≥ p ^ r₂) :
    ∃ N : ℕ,
      (∀ n < N, negativeBinomialMass r₂ p n ≤ negativeBinomialMass r₁ p n) ∧
      (∀ n ≥ N, negativeBinomialMass r₁ p n ≤ negativeBinomialMass r₂ p n) := by
  let a : ℕ → ℝ :=
    fun n ↦ negativeBinomialMass r₁ p n / negativeBinomialMass r₂ p n
  have hpow' : p ^ r₂ ≤ p ^ r₁ := by
    simpa [ge_iff_le] using hpow
  have hrr : r₁ ≤ r₂ := by
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hp hp_lt_one).1 hpow'
  have ha_pos : ∀ n : ℕ, 0 < a n := by
    intro n
    dsimp [a]
    exact
      div_pos
        (negativeBinomialMass_pos_of_lt_one r₁ p hr₁ hp hp_lt_one n)
        (negativeBinomialMass_pos_of_lt_one r₂ p hr₂ hp hp_lt_one n)
  have hstep : ∀ n : ℕ,
      a (n + 1) = a n * (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) := by
    intro n
    -- Proof comment: with common `p`, only the rational shape factor remains in the ratio
    -- recurrence.
    have hfail_ne : (1 - p : ℝ) ≠ 0 := by
      linarith
    simpa [a, hfail_ne] using
      negativeBinomialMassRatio_succ r₁ r₂ p p hr₁ hr₂ hp hp hp_lt_one hp_lt_one n
  have ha_anti : Antitone a := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hfactor_le : (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) ≤ 1 := by
      have hden : 0 < (n : ℝ) + r₂ := by
        positivity
      exact (div_le_one hden).2 (by linarith)
    -- Proof comment: since `r₁ ≤ r₂`, every ratio step multiplies by at most `1`.
    calc
      a (n + 1) = a n * (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) := by
        simpa using hstep n
      _ ≤ a n * 1 := by
        exact mul_le_mul_of_nonneg_left hfactor_le (ha_pos n).le
      _ = a n := by
        ring
  have hzero : 1 ≤ a 0 := by
    have hden_pos : 0 < p ^ r₂ := Real.rpow_pos_of_pos hp r₂
    -- Proof comment: the zeroth atom comparison is exactly the assumed power inequality.
    simpa [a, negativeBinomialMass_zero_local] using (one_le_div hden_pos).2 hpow'
  have hcross : ∃ N : ℕ, a N ≤ 1 := by
    by_contra hNoCross
    have hall : ∀ n : ℕ, 1 < a n := by
      intro n
      exact lt_of_not_ge (fun hn ↦ hNoCross ⟨n, hn⟩)
    have hmass_lt :
        ∀ n : ℕ, negativeBinomialMass r₂ p n < negativeBinomialMass r₁ p n := by
      intro n
      have hden_pos : 0 < negativeBinomialMass r₂ p n :=
        negativeBinomialMass_pos_of_lt_one r₂ p hr₂ hp hp_lt_one n
      exact (one_lt_div hden_pos).1 (by simpa [a] using hall n)
    have hsum_lt :
        ∑' n : ℕ, negativeBinomialMass r₂ p n <
          ∑' n : ℕ, negativeBinomialMass r₁ p n := by
      exact
        Summable.tsum_lt_tsum_of_nonneg
          (fun n ↦ negativeBinomialMass_nonneg hr₂ hp hp_lt_one.le n)
          (fun n ↦ (hmass_lt n).le)
          (hmass_lt 0)
          (negativeBinomialMass_hasSum hr₁ hp hp_lt_one.le).summable
    have hsum₂ : ∑' n : ℕ, negativeBinomialMass r₂ p n = 1 :=
      (negativeBinomialMass_hasSum hr₂ hp hp_lt_one.le).tsum_eq
    have hsum₁ : ∑' n : ℕ, negativeBinomialMass r₁ p n = 1 :=
      (negativeBinomialMass_hasSum hr₁ hp hp_lt_one.le).tsum_eq
    linarith
  obtain ⟨N, hprefix, htail⟩ := singleCrossing_of_antitone_ratio ha_anti hcross
  have hleft_of_ratio :
      ∀ {n : ℕ}, 1 ≤ a n → negativeBinomialMass r₂ p n ≤ negativeBinomialMass r₁ p n := by
    intro n hn
    have hden_pos : 0 < negativeBinomialMass r₂ p n :=
      negativeBinomialMass_pos_of_lt_one r₂ p hr₂ hp hp_lt_one n
    exact (one_le_div hden_pos).1 (by simpa [a] using hn)
  have hright_of_ratio :
      ∀ {n : ℕ}, a n ≤ 1 → negativeBinomialMass r₁ p n ≤ negativeBinomialMass r₂ p n := by
    intro n hn
    have hden_pos : 0 < negativeBinomialMass r₂ p n :=
      negativeBinomialMass_pos_of_lt_one r₂ p hr₂ hp hp_lt_one n
    exact (div_le_one hden_pos).1 (by simpa [a] using hn)
  refine ⟨N, ?_⟩
  constructor
  · intro n hn
    exact hleft_of_ratio ((hprefix n hn).le)
  · intro n hn
    exact hright_of_ratio (htail n hn)

/-- Exercise 24.2.3: the negative-binomial law `b^-_{r₁,p₁}` is stochastically dominated by
`b^-_{r₂,p₂}` if and only if `p₁ ≥ p₂` and `p₁ ^ r₁ ≥ p₂ ^ r₂`. -/
theorem negativeBinomial_stochasticLE_iff
    (r₁ r₂ p₁ p₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hp₁_le_one : p₁ ≤ 1) (hp₂_le_one : p₂ ≤ 1) :
    StochasticLE
        (ProbabilityMeasure.toFin1Real
          (⟨negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one, inferInstance⟩ :
            ProbabilityMeasure ℕ))
        (ProbabilityMeasure.toFin1Real
          (⟨negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one, inferInstance⟩ :
            ProbabilityMeasure ℕ)) ↔
      (p₁ ≥ p₂ ∧ p₁ ^ r₁ ≥ p₂ ^ r₂) := by
  let ν₁ : ProbabilityMeasure ℕ :=
    ⟨negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one, inferInstance⟩
  let ν₂ : ProbabilityMeasure ℕ :=
    ⟨negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one, inferInstance⟩
  change StochasticLE ν₁.toFin1Real ν₂.toFin1Real ↔ (p₁ ≥ p₂ ∧ p₁ ^ r₁ ≥ p₂ ^ r₂)
  constructor
  · intro hst
    have htail_one :
        (ν₁ : Measure ℕ) (Set.Ici 1) ≤ (ν₂ : Measure ℕ) (Set.Ici 1) :=
      ProbabilityTheory.StochasticLE.upper_tail_nat (μ₁ := ν₁) (μ₂ := ν₂) hst 1
    have htail_one_real :
        ((ν₁ : Measure ℕ) (Set.Ici 1)).toReal ≤ ((ν₂ : Measure ℕ) (Set.Ici 1)).toReal := by
      exact
        (ENNReal.toReal_le_toReal
          (measure_ne_top (ν₁ : Measure ℕ) (Set.Ici 1))
          (measure_ne_top (ν₂ : Measure ℕ) (Set.Ici 1))).2 htail_one
    have hpow_forward : p₂ ^ r₂ ≤ p₁ ^ r₁ := by
      -- Proof comment: the first nontrivial tail is the complement of the zero atom, so the
      -- upper-tail comparison immediately compares `p₁ ^ r₁` and `p₂ ^ r₂`.
      have hzero₁ :
          ((ν₁ : Measure ℕ) ({0} : Set ℕ)).toReal = p₁ ^ r₁ := by
        simpa [ν₁] using negativeBinomialMeasure_apply_zero_toReal r₁ p₁ hr₁ hp₁ hp₁_le_one
      have hzero₂ :
          ((ν₂ : Measure ℕ) ({0} : Set ℕ)).toReal = p₂ ^ r₂ := by
        simpa [ν₂] using negativeBinomialMeasure_apply_zero_toReal r₂ p₂ hr₂ hp₂ hp₂_le_one
      rw [natMeasure_tail_Ici_one_toReal (μ := (ν₁ : Measure ℕ)),
        natMeasure_tail_Ici_one_toReal (μ := (ν₂ : Measure ℕ)), hzero₁, hzero₂] at htail_one_real
      linarith
    have hp_ge : p₁ ≥ p₂ := by
      by_contra hp_not_ge
      have hp₁_lt_p₂ : p₁ < p₂ := lt_of_not_ge hp_not_ge
      by_cases hp₂_eq_one : p₂ = 1
      · have hp₁_lt_one : p₁ < 1 := by
          simpa [hp₂_eq_one] using hp₁_lt_p₂
        have hpow_lt : p₁ ^ r₁ < p₂ ^ r₂ := by
          simpa [hp₂_eq_one] using Real.rpow_lt_one hp₁.le hp₁_lt_one hr₁
        exact not_lt_of_ge hpow_forward hpow_lt
      · have hp₂_lt_one : p₂ < 1 := lt_of_le_of_ne hp₂_le_one hp₂_eq_one
        obtain ⟨N, hN⟩ :=
          negativeBinomialEventualAtomDomination_of_ltParameter
            r₁ r₂ p₁ p₂ hr₁ hr₂ hp₁ hp₂ hp₁_lt_p₂ hp₂_lt_one
        have hN' :
            ∀ n ≥ N,
              ((negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one) ({n} : Set ℕ)).toReal <
                ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal := by
          intro n hn
          simpa [negativeBinomialMeasure_apply_singleton_toReal] using hN n hn
        have htail_lt_real :
            ((ν₂ : Measure ℕ) (Set.Ici N)).toReal < ((ν₁ : Measure ℕ) (Set.Ici N)).toReal := by
          -- Proof comment: eventual strict atom domination forces a strict upper-tail gap.
          simpa [ν₁, ν₂] using
            natTail_lt_of_eventualSingletonLt
              (μ₁ := negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one)
              (μ₂ := negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one)
              hN'
        have htail_lt :
            (ν₂ : Measure ℕ) (Set.Ici N) < (ν₁ : Measure ℕ) (Set.Ici N) := by
          exact
            (ENNReal.toReal_lt_toReal
              (measure_ne_top (ν₂ : Measure ℕ) (Set.Ici N))
              (measure_ne_top (ν₁ : Measure ℕ) (Set.Ici N))).1 htail_lt_real
        exact not_lt_of_ge (ProbabilityTheory.StochasticLE.upper_tail_nat (μ₁ := ν₁) (μ₂ := ν₂) hst N)
          htail_lt
    exact ⟨hp_ge, hpow_forward⟩
  · rintro ⟨hp_ge, hpow⟩
    rw [ProbabilityTheory.stochasticLE_toFin1Real_iff_upper_tail ν₁ ν₂]
    by_cases hp₁_eq_one : p₁ = 1
    · subst p₁
      intro k
      -- Proof comment: if `p₁ = 1`, the first law is the Dirac mass at `0`, so every nontrivial
      -- upper tail is zero.
      have hdirac : (ν₁ : Measure ℕ) = Measure.dirac 0 := by
        simpa [ν₁] using negativeBinomialMeasure_eq_dirac_zero_of_one r₁ hr₁
      rw [hdirac]
      cases k with
      | zero =>
          have hIci0_set : (Set.Ici (0 : ℕ) : Set ℕ) = Set.univ := by
            ext n
            simp
          have hIci0 : (ν₂ : Measure ℕ) (Set.Ici 0) = 1 := by
            rw [hIci0_set]
            simp
          rw [hIci0]
          simp
      | succ k =>
          simp
    · have hp₁_lt_one : p₁ < 1 := lt_of_le_of_ne hp₁_le_one hp₁_eq_one
      by_cases hp_eq : p₁ = p₂
      · subst p₂
        obtain ⟨N, hleft, hright⟩ :=
          negativeBinomialMass_singleCrossing_of_eqParameter
            r₁ r₂ p₁ hr₁ hr₂ hp₁ hp₁_lt_one hpow
        have hleft' :
            ∀ n < N,
              ((negativeBinomialMeasure r₂ p₁ hr₂ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal ≤
                ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal := by
          intro n hn
          simpa [negativeBinomialMeasure_apply_singleton_toReal] using hleft n hn
        have hright' :
            ∀ n ≥ N,
              ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal ≤
                ((negativeBinomialMeasure r₂ p₁ hr₂ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal := by
          intro n hn
          simpa [negativeBinomialMeasure_apply_singleton_toReal] using hright n hn
        intro k
        -- Proof comment: in the equal-parameter branch, the singleton masses cross exactly once.
        simpa [ν₁, ν₂] using
          natUpperTail_le_of_singleCrossing
            (μ₁ := negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one)
            (μ₂ := negativeBinomialMeasure r₂ p₁ hr₂ hp₁ hp₁_le_one)
            hleft' hright' k
      · have hp₂_ne_p₁ : p₂ ≠ p₁ := by
          intro h
          exact hp_eq h.symm
        have hp₂_lt_p₁ : p₂ < p₁ := lt_of_le_of_ne hp_ge hp₂_ne_p₁
        have hp₂_lt_one : p₂ < 1 := lt_trans hp₂_lt_p₁ hp₁_lt_one
        by_cases hrr : r₁ ≤ r₂
        · let a : ℕ → ℝ :=
            fun n ↦ negativeBinomialMass r₁ p₁ n / negativeBinomialMass r₂ p₂ n
          let f : ℕ → ℝ :=
            fun n ↦ (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) * ((1 - p₁) / (1 - p₂))
          have ha_pos : ∀ n : ℕ, 0 < a n := by
            intro n
            dsimp [a]
            exact
              div_pos
                (negativeBinomialMass_pos_of_lt_one r₁ p₁ hr₁ hp₁ hp₁_lt_one n)
                (negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n)
          have hstep : ∀ n : ℕ, a (n + 1) = a n * f n := by
            intro n
            -- Proof comment: the easy branch still reduces to the canonical atom-ratio
            -- recurrence.
            simpa [a, f] using
              negativeBinomialMassRatio_succ r₁ r₂ p₁ p₂ hr₁ hr₂ hp₁ hp₂ hp₁_lt_one hp₂_lt_one n
          have ha_anti : Antitone a := by
            refine antitone_nat_of_succ_le ?_
            intro n
            have hfactor_le : f n ≤ 1 := by
              have hden : 0 < (1 - p₂) := sub_pos.mpr hp₂_lt_one
              have hratio_le :
                  (((n : ℝ) + r₁) / ((n : ℝ) + r₂)) ≤ 1 := by
                have hden' : 0 < (n : ℝ) + r₂ := by
                  positivity
                exact (div_le_one hden').2 (by linarith)
              have hfail_le :
                  ((1 - p₁) / (1 - p₂)) ≤ 1 := by
                exact (div_le_one hden).2 (by linarith)
              have hfail_nonneg : 0 ≤ (1 - p₁) / (1 - p₂) := by
                exact div_nonneg (by linarith) hden.le
              exact mul_le_one₀ hratio_le hfail_nonneg hfail_le
            -- Proof comment: when `r₁ ≤ r₂`, every step factor is already at most `1`.
            calc
              a (n + 1) = a n * f n := by
                simpa using hstep n
              _ ≤ a n * 1 := by
                exact mul_le_mul_of_nonneg_left hfactor_le (ha_pos n).le
              _ = a n := by
                ring
          have hzero : 1 ≤ a 0 := by
            have hden_pos : 0 < p₂ ^ r₂ := Real.rpow_pos_of_pos hp₂ r₂
            -- Proof comment: the zero atoms are ordered by the assumed power inequality.
            simpa [a, negativeBinomialMass_zero_local] using (one_le_div hden_pos).2 hpow
          obtain ⟨M, hM⟩ :=
            negativeBinomialEventualAtomDomination_of_ltParameter
              r₂ r₁ p₂ p₁ hr₂ hr₁ hp₂ hp₁ hp₂_lt_p₁ hp₁_lt_one
          have hcross : ∃ N : ℕ, a N ≤ 1 := by
            refine ⟨M, ?_⟩
            have hmass_lt :
                negativeBinomialMass r₁ p₁ M < negativeBinomialMass r₂ p₂ M := hM M le_rfl
            have hden_pos : 0 < negativeBinomialMass r₂ p₂ M :=
              negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one M
            exact (div_lt_one hden_pos).2 hmass_lt |>.le
          obtain ⟨N, hprefix, htail⟩ := singleCrossing_of_antitone_ratio ha_anti hcross
          have hleft :
              ∀ n < N, negativeBinomialMass r₂ p₂ n ≤ negativeBinomialMass r₁ p₁ n := by
            intro n hn
            have hden_pos : 0 < negativeBinomialMass r₂ p₂ n :=
              negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n
            exact (one_le_div hden_pos).1 (by simpa [a] using (hprefix n hn).le)
          have hright :
              ∀ n ≥ N, negativeBinomialMass r₁ p₁ n ≤ negativeBinomialMass r₂ p₂ n := by
            intro n hn
            have hden_pos : 0 < negativeBinomialMass r₂ p₂ n :=
              negativeBinomialMass_pos_of_lt_one r₂ p₂ hr₂ hp₂ hp₂_lt_one n
            exact (div_le_one hden_pos).1 (by simpa [a] using htail n hn)
          have hleft' :
              ∀ n < N,
                ((negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one) ({n} : Set ℕ)).toReal ≤
                  ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal := by
            intro n hn
            simpa [negativeBinomialMeasure_apply_singleton_toReal] using hleft n hn
          have hright' :
              ∀ n ≥ N,
                ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal ≤
                  ((negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one) ({n} : Set ℕ)).toReal := by
            intro n hn
            simpa [negativeBinomialMeasure_apply_singleton_toReal] using hright n hn
          intro k
          simpa [ν₁, ν₂] using
            natUpperTail_le_of_singleCrossing
              (μ₁ := negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one)
              (μ₂ := negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one)
              hleft' hright' k
        · have hrlt : r₂ < r₁ := lt_of_not_ge hrr
          obtain ⟨N, hleft, hright⟩ :=
            negativeBinomialSingletonSingleCrossing_of_monotoneFactor
              r₁ r₂ p₁ p₂ hr₁ hr₂ hp₁ hp₂ hp₂_lt_p₁ hp₁_lt_one hpow hrlt
          have hleft' :
              ∀ n < N,
                ((negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one) ({n} : Set ℕ)).toReal ≤
                  ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal := by
            intro n hn
            simpa [negativeBinomialMeasure_apply_singleton_toReal] using hleft n hn
          have hright' :
              ∀ n ≥ N,
                ((negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one) ({n} : Set ℕ)).toReal ≤
                  ((negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one) ({n} : Set ℕ)).toReal := by
            intro n hn
            simpa [negativeBinomialMeasure_apply_singleton_toReal] using hright n hn
          intro k
          -- Proof comment: the hard branch is the one place where the factor itself crosses once
          -- before the ratio does.
          simpa [ν₁, ν₂] using
            natUpperTail_le_of_singleCrossing
              (μ₁ := negativeBinomialMeasure r₁ p₁ hr₁ hp₁ hp₁_le_one)
              (μ₂ := negativeBinomialMeasure r₂ p₂ hr₂ hp₂ hp₂_le_one)
              hleft' hright' k

end ProbabilityTheory
