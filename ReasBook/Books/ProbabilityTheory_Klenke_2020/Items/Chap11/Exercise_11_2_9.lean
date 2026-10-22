/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Equation_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

noncomputable section

local notation "unitIntervalLebesgue" => volume.restrict (Set.Icc (0 : ℝ) 1)

local instance : IsProbabilityMeasure unitIntervalLebesgue := by
  refine ⟨by
    simp [Real.volume_Icc]
  ⟩

/-- The `k`-th dyadic half-open subinterval of `[0,1)` at level `n`. -/
def dyadicInterval (n : ℕ) (k : Fin (2 ^ n)) : Set ℝ :=
  Set.Ico ((k : ℝ) / (2 : ℝ) ^ n) (((k : ℕ) + 1 : ℕ) / (2 : ℝ) ^ n)

private def dyadicCompletionResidualSet (n : ℕ) : Set ℝ :=
  (⋃ k : Fin (2 ^ n), dyadicInterval n k)ᶜ

private def dyadicCompletionAtom (n : ℕ) : Option (Fin (2 ^ n)) → Set ℝ
  | some k => dyadicInterval n k
  | none => dyadicCompletionResidualSet n

private theorem measurableSet_dyadicInterval (n : ℕ) (k : Fin (2 ^ n)) :
    MeasurableSet (dyadicInterval n k) := by
  simp [dyadicInterval]

private theorem measurableSet_dyadicCompletionResidualSet (n : ℕ) :
    MeasurableSet (dyadicCompletionResidualSet n) := by
  rw [dyadicCompletionResidualSet]
  exact (MeasurableSet.iUnion fun k ↦ measurableSet_dyadicInterval n k).compl

private theorem measurableSet_dyadicCompletionAtom (n : ℕ) (i : Option (Fin (2 ^ n))) :
    MeasurableSet (dyadicCompletionAtom n i) := by
  cases i with
  | none =>
      simpa [dyadicCompletionAtom] using measurableSet_dyadicCompletionResidualSet n
  | some k =>
      simpa [dyadicCompletionAtom] using measurableSet_dyadicInterval n k

private theorem measurableSet_dyadicCompletionResidualSet_generateFrom (n : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom (Set.range (dyadicInterval n))]
      (dyadicCompletionResidualSet n) := by
  rw [dyadicCompletionResidualSet]
  refine (MeasurableSet.iUnion fun k ↦ ?_).compl
  exact MeasurableSpace.measurableSet_generateFrom
    (show dyadicInterval n k ∈ Set.range (dyadicInterval n) from ⟨k, rfl⟩)

private theorem generateFrom_dyadicCompletionAtom_eq (n : ℕ) :
    MeasurableSpace.generateFrom (Set.range (dyadicCompletionAtom n)) =
      MeasurableSpace.generateFrom (Set.range (dyadicInterval n)) := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    cases i with
    | none =>
        exact measurableSet_dyadicCompletionResidualSet_generateFrom n
    | some k =>
        exact MeasurableSpace.measurableSet_generateFrom
          (show dyadicInterval n k ∈ Set.range (dyadicInterval n) from ⟨k, rfl⟩)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨k, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      (show dyadicCompletionAtom n (Option.some k) ∈ Set.range (dyadicCompletionAtom n) from
        ⟨Option.some k, rfl⟩)

/-- Helper for Exercise 11.2.9: every dyadic atom lies inside the closed unit interval. -/
private theorem dyadicInterval_subset_unitInterval (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicInterval n k ⊆ Set.Icc (0 : ℝ) 1 := by
  -- The left endpoint is nonnegative and the right endpoint is at most `1`.
  intro x hx
  constructor
  · have hleft : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n := by positivity
    exact hleft.trans hx.1
  · have hk : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.succ_le_of_lt k.2
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hright : (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
      have := (strictMono_div_right_of_pos hpow).monotone hk
      simpa [hpow.ne'] using this
    exact hx.2.le.trans hright

/-- Helper for Exercise 11.2.9: the floor-selected dyadic index stays in range on `[0,1)`. -/
private theorem floorIndex_lt_twoPow {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ⌊x * (2 : ℝ) ^ n⌋₊ < 2 ^ n := by
  -- Multiply the strict upper bound `x < 1` by `2^n` before applying `Nat.floor_lt`.
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hx_scaled_lt : x * (2 : ℝ) ^ n < ((2 ^ n : ℕ) : ℝ) := by
    simpa using (mul_lt_mul_of_pos_right hx.2 hpow)
  simpa using
    (Nat.floor_lt' (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))).2 hx_scaled_lt

/-- Helper for Exercise 11.2.9: the floor-selected index picks the dyadic cell containing `x`. -/
private theorem mem_dyadicInterval_floorIndex {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    x ∈ Set.Ico ((⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n)
      (((((⌊x * (2 : ℝ) ^ n⌋₊ : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)) := by
  -- Convert the floor bounds back to interval bounds by dividing through by `2^n`.
  let kNat : ℕ := ⌊x * (2 : ℝ) ^ n⌋₊
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hmul_nonneg : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx.1 hpow.le
  have hk_le : (kNat : ℝ) ≤ x * (2 : ℝ) ^ n := by
    simpa [kNat] using (Nat.floor_le hmul_nonneg)
  have hk_succ : x * (2 : ℝ) ^ n < (kNat : ℝ) + 1 := by
    simpa [kNat] using (Nat.lt_floor_add_one (x * (2 : ℝ) ^ n))
  constructor
  · change (kNat : ℝ) / (2 : ℝ) ^ n ≤ x
    rw [div_le_iff₀ hpow]
    simpa [kNat, mul_comm] using hk_le
  · change x < (((kNat + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)
    rw [lt_div_iff₀ hpow]
    simpa [kNat, mul_comm, mul_left_comm, mul_assoc] using hk_succ

/-- Helper for Exercise 11.2.9: the dyadic atoms at level `n` cover `[0,1)`. -/
private theorem iUnion_dyadicInterval_eq_Ico (n : ℕ) :
    (⋃ k : Fin (2 ^ n), dyadicInterval n k) = Set.Ico (0 : ℝ) 1 := by
  -- Use the floor of `x * 2^n` to locate the unique dyadic cell containing `x`.
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hk⟩
    constructor
    · have hleft : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n := by positivity
      exact hleft.trans hk.1
    · have hk' : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast Nat.succ_le_of_lt k.2
      have hpow : 0 < (2 : ℝ) ^ n := by positivity
      have : (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
        have := (strictMono_div_right_of_pos hpow).monotone hk'
        simpa [hpow.ne'] using this
      exact lt_of_lt_of_le hk.2 this
  · intro hx
    let k : Fin (2 ^ n) := ⟨⌊x * (2 : ℝ) ^ n⌋₊, floorIndex_lt_twoPow (n := n) hx⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simpa [dyadicInterval, k] using mem_dyadicInterval_floorIndex (n := n) hx

/-- Helper for Exercise 11.2.9: different dyadic atoms at the same level are disjoint. -/
private theorem dyadicInterval_disjoint {n : ℕ} {k l : Fin (2 ^ n)} (hkl : k ≠ l) :
    Disjoint (dyadicInterval n k) (dyadicInterval n l) := by
  rcases lt_or_gt_of_ne fun h => hkl (Fin.ext h) with hlt | hlt
  · refine Set.disjoint_left.2 ?_
    intro x hxk hxl
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hsep : (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ (l : ℝ) / (2 : ℝ) ^ n := by
      have hkl' : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ l := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      exact (strictMono_div_right_of_pos hpow).monotone hkl'
    exact not_lt_of_ge (hsep.trans hxl.1) hxk.2
  · exact (dyadicInterval_disjoint (k := l) (l := k) hkl.symm).symm

/-- Helper for Exercise 11.2.9: the completed dyadic partition is pairwise disjoint. -/
private theorem pairwiseDisjoint_dyadicCompletionAtom (n : ℕ) :
    Pairwise fun i j : Option (Fin (2 ^ n)) ↦ Disjoint (dyadicCompletionAtom n i) (dyadicCompletionAtom n j) := by
  -- The residual atom is the complement of the dyadic union, so it is disjoint from every cell.
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => cases hij rfl
      | some k =>
          refine Set.disjoint_left.2 ?_
          intro x hx₁ hx₂
          exact hx₁ (Set.mem_iUnion.2 ⟨k, hx₂⟩)
  | some k =>
      cases j with
      | none =>
          refine Set.disjoint_left.2 ?_
          intro x hx₁ hx₂
          exact hx₂ (Set.mem_iUnion.2 ⟨k, hx₁⟩)
      | some l =>
          have hkl : k ≠ l := by
            intro h
            apply hij
            simpa [h]
          simpa [dyadicCompletionAtom] using dyadicInterval_disjoint hkl

/-- Helper for Exercise 11.2.9: each dyadic cell has the expected length under
`unitIntervalLebesgue`. -/
private theorem dyadicInterval_measureReal (n : ℕ) (k : Fin (2 ^ n)) :
    (unitIntervalLebesgue).real (dyadicInterval n k) = ((2 : ℝ) ^ n)⁻¹ := by
  -- Restriction does not change the measure on subsets of `[0,1]`.
  have hsubset := dyadicInterval_subset_unitInterval n k
  rw [measureReal_def]
  rw [Measure.restrict_apply (μ := volume) (s := Set.Icc (0 : ℝ) 1)
      (t := dyadicInterval n k) (ht := measurableSet_dyadicInterval n k),
    Set.inter_eq_left.mpr hsubset, dyadicInterval, Real.volume_Ico]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hlength :
      ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - (k : ℝ) / (2 : ℝ) ^ n =
        ((2 : ℝ) ^ n)⁻¹ := by
    field_simp [hpow.ne']
    norm_num
  have hlength_nonneg :
      0 ≤ ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - (k : ℝ) / (2 : ℝ) ^ n := by
    rw [hlength]
    positivity
  rw [ENNReal.toReal_ofReal hlength_nonneg, hlength]

/-- Helper for Exercise 11.2.9: the dyadic coefficient is the set average on the cell. -/
private theorem dyadicInterval_setAverage_eq_scaledIntegral (f : ℝ → ℝ) (n : ℕ)
    (k : Fin (2 ^ n)) :
    ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue =
      ((2 : ℝ) ^ n) * ∫ y in dyadicInterval n k, f y ∂unitIntervalLebesgue := by
  -- The cell has measure `2^{-n}`, so inverting the measure multiplies by `2^n`.
  rw [setAverage_eq, dyadicInterval_measureReal n k]
  simp [smul_eq_mul]

/-- Helper for Exercise 11.2.9: each dyadic atom is the union of its two successors. -/
private theorem dyadicInterval_split_succ (n : ℕ) (k : Fin (2 ^ n)) :
    let k₀ : Fin (2 ^ (n + 1)) := ⟨2 * (k : ℕ), by
      have hk : 2 * (k : ℕ) < 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_left k.2 (by omega)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk⟩
    let k₁ : Fin (2 ^ (n + 1)) := ⟨2 * (k : ℕ) + 1, by
      have hk : 2 * (k : ℕ) + 1 < 2 * 2 ^ n := by omega
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk⟩
    dyadicInterval n k = dyadicInterval (n + 1) k₀ ∪ dyadicInterval (n + 1) k₁ := by
  -- Rewrite the endpoints of the successor cells and use the standard adjacent-interval union law.
  dsimp [dyadicInterval]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow_succ : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hk₀ :
      (((2 * (k : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) = (k : ℝ) / (2 : ℝ) ^ n := by
    calc
      (((2 * (k : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
          = ((2 : ℝ) * k) / (2 : ℝ) ^ (n + 1) := by norm_num
      _ = (k : ℝ) / (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp [hpow.ne']
  have hk₂ :
      (((2 * (k : ℕ) + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) =
        (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
    calc
      (((2 * (k : ℕ) + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
          = ((2 : ℝ) * k + 2) / (2 : ℝ) ^ (n + 1) := by norm_num
      _ = (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp [hpow.ne']
        norm_num
  rw [hk₀, hk₂, Set.Ico_union_Ico_eq_Ico]
  · have hmid_left' :
        (((2 * (k : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) ≤
          (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
        exact (strictMono_div_right_of_pos hpow_succ).monotone
          (by exact_mod_cast Nat.le_succ (2 * (k : ℕ)))
    have hmid_left : ((k : ℝ) / (2 : ℝ) ^ n) ≤
        (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
      calc
        (k : ℝ) / (2 : ℝ) ^ n
            = (((2 * (k : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := hk₀.symm
        _ ≤ (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := hmid_left'
    simpa using hmid_left
  · have hmid_right' :
        (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) ≤
          (((2 * (k : ℕ) + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
        exact (strictMono_div_right_of_pos hpow_succ).monotone
          (by exact_mod_cast Nat.le_succ (2 * (k : ℕ) + 1))
    have hmid_right :
        (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) ≤
          ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
      calc
        (((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
            ≤ (((2 * (k : ℕ) + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := hmid_right'
        _ = ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := hk₂
    simpa using hmid_right

private theorem dyadicFiltration_mono :
    Monotone fun n : ℕ ↦ MeasurableSpace.generateFrom (Set.range (dyadicInterval n)) := by
  intro i j hij
  induction hij with
  | refl =>
      exact le_rfl
  | @step j hij hmono =>
      refine le_trans hmono (MeasurableSpace.generateFrom_le ?_)
      rintro s ⟨k, rfl⟩
      rcases dyadicInterval_split_succ j k with hsplit
      rw [hsplit]
      exact (MeasurableSpace.measurableSet_generateFrom
          (show dyadicInterval (j + 1) _ ∈ Set.range (dyadicInterval (j + 1)) from ⟨_, rfl⟩)).union
        (MeasurableSpace.measurableSet_generateFrom
          (show dyadicInterval (j + 1) _ ∈ Set.range (dyadicInterval (j + 1)) from ⟨_, rfl⟩))

/-- The canonical filtration whose `n`-th stage is generated by the level-`n` dyadic intervals on
`[0,1)`. -/
def dyadicFiltration : Filtration ℕ (borel ℝ) where
  seq n := MeasurableSpace.generateFrom (Set.range (dyadicInterval n))
  mono' := dyadicFiltration_mono
  le' n := MeasurableSpace.generateFrom_le fun s hs ↦ by
    rcases hs with ⟨k, rfl⟩
    exact measurableSet_dyadicInterval n k

/-- The `n`-th dyadic averaging approximation of a function on `[0,1]`, extended by `0` off the
level-`n` dyadic cells. -/
def dyadicAverageApproximation (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x ↦
    ∑ k : Fin (2 ^ n),
      Set.indicator
        (dyadicInterval n k)
        (fun _ ↦
          ((2 : ℝ) ^ n) *
            (∫ y in dyadicInterval n k, f y ∂unitIntervalLebesgue))
        x

/-- The textbook dyadic approximation agrees with the owner-style partition formula obtained by
taking the `unitIntervalLebesgue`-average of `f` on each dyadic atom. -/
theorem dyadicAverageApproximation_eq_partitionFormula (f : ℝ → ℝ) (n : ℕ) :
    dyadicAverageApproximation f n =
      fun x ↦
        ∑ k : Fin (2 ^ n),
          Set.indicator (dyadicInterval n k)
            (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
  -- Rewrite every coefficient in the finite sum using the set-average formula.
  funext x
  simp [dyadicAverageApproximation, dyadicInterval_setAverage_eq_scaledIntegral]

/-- The dyadic averaging approximation is the source-facing realization of the canonical
conditional expectation onto the σ-algebra generated by the level-`n` dyadic intervals. -/
theorem dyadicAverageApproximation_ae_eq_condExp {f : ℝ → ℝ}
    (hf : Integrable f unitIntervalLebesgue) (n : ℕ) :
    dyadicAverageApproximation f n =ᵐ[unitIntervalLebesgue]
      unitIntervalLebesgue[f | dyadicFiltration n] := by
  rw [dyadicAverageApproximation_eq_partitionFormula]
  have h_formula' :
      unitIntervalLebesgue[f |
          MeasurableSpace.generateFrom (Set.range (dyadicCompletionAtom n))] =ᵐ[unitIntervalLebesgue]
        fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    simpa [dyadicCompletionAtom, dyadicCompletionResidualSet, dyadicInterval] using
      (condExp_generateFrom_ae_eq_countable_partition_formula
        unitIntervalLebesgue (dyadicCompletionAtom n)
        (by
          intro i
          exact measurableSet_dyadicCompletionAtom n i)
        (pairwiseDisjoint_dyadicCompletionAtom n)
        (by
          ext x
          constructor
          · intro _
            simp
          · intro _
            by_cases hx : x ∈ ⋃ k : Fin (2 ^ n), dyadicInterval n k
            · rcases Set.mem_iUnion.1 hx with ⟨k, hk⟩
              exact Set.mem_iUnion.2 ⟨Option.some k, by simpa [dyadicCompletionAtom] using hk⟩
            · have hx_residual : x ∈ dyadicCompletionResidualSet n := by
                simpa [dyadicCompletionResidualSet] using hx
              exact Set.mem_iUnion.2 ⟨Option.none, by
                simpa [dyadicCompletionAtom] using hx_residual⟩)
        hf)
  have h_formula :
      unitIntervalLebesgue[f | dyadicFiltration n] =ᵐ[unitIntervalLebesgue]
        fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    simpa [dyadicFiltration, generateFrom_dyadicCompletionAtom_eq n] using h_formula'
  have h_residual :
      (fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x) =ᵐ[unitIntervalLebesgue]
        fun x ↦
          ∑ k : Fin (2 ^ n),
            Set.indicator (dyadicInterval n k)
              (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    have h_mem_Ico : ∀ᵐ x ∂unitIntervalLebesgue, x ∈ Set.Ico (0 : ℝ) 1 := by
      change ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1), x ∈ Set.Ico (0 : ℝ) 1
      rw [← restrict_Ico_eq_restrict_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)]
      exact ae_restrict_mem measurableSet_Ico
    filter_upwards [h_mem_Ico] with x hx
    have hnot_mem_residual : x ∉ dyadicCompletionResidualSet n := by
      simpa [dyadicCompletionResidualSet, iUnion_dyadicInterval_eq_Ico n] using hx
    simp [hnot_mem_residual]
  exact (h_formula.trans h_residual).symm

/-- Helper for Exercise 11.2.9: on its containing dyadic cell, the partition formula collapses to
that cell's average. -/
private theorem dyadicAverageApproximation_eq_setAverage_of_mem {f : ℝ → ℝ} {n : ℕ}
    {k : Fin (2 ^ n)} {x : ℝ} (hx : x ∈ dyadicInterval n k) :
    dyadicAverageApproximation f n x = ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue := by
  -- Rewrite by the partition formula and keep only the unique dyadic atom containing `x`.
  rw [dyadicAverageApproximation_eq_partitionFormula]
  change
      (∑ j : Fin (2 ^ n),
        Set.indicator (dyadicInterval n j)
          (fun _ ↦ ⨍ y in dyadicInterval n j, f y ∂unitIntervalLebesgue) x) =
        ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue
  classical
  rw [Finset.sum_eq_single k]
  · simp [hx]
  · intro j _ hjk
    have hxj : x ∉ dyadicInterval n j := by
      intro hx'
      exact (Set.disjoint_left.mp <| dyadicInterval_disjoint (n := n) (k := j) (l := k) hjk) hx' hx
    simp [hxj]
  · simp

/-- Helper for Exercise 11.2.9: after removing the ambient restriction, the dyadic half-open cell
can be replaced by its closed version when averaging the truncated function. -/
private theorem dyadicInterval_setAverage_eq_closedCellAverage_indicator (f : ℝ → ℝ) (n : ℕ)
    (k : Fin (2 ^ n)) :
    let g := Set.indicator (Set.Icc (0 : ℝ) 1) f
    ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue =
      ⨍ y in Set.Icc ((k : ℝ) / (2 : ℝ) ^ n) ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n),
        g y ∂volume := by
  -- First replace the restricted measure by `volume`, then close the right endpoint a.e.
  dsimp
  let s := dyadicInterval n k
  have hsubset : s ⊆ Set.Icc (0 : ℝ) 1 := dyadicInterval_subset_unitInterval n k
  have hrestrict : Measure.restrict unitIntervalLebesgue s = volume.restrict s := by
    change (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict s = volume.restrict s
    exact Measure.restrict_restrict_of_subset hsubset
  have hmeasure : unitIntervalLebesgue s = volume s := by
    simpa [Measure.restrict_apply_univ] using congrArg (fun μ : Measure ℝ ↦ μ Set.univ) hrestrict
  calc
    ⨍ y in s, f y ∂unitIntervalLebesgue = ⨍ y in s, f y ∂volume := by
      rw [setAverage_eq', setAverage_eq', hmeasure, hrestrict]
    _ = ⨍ y in s, (Set.indicator (Set.Icc (0 : ℝ) 1) f) y ∂volume := by
      apply (setAverage_congr_fun (measurableSet_dyadicInterval n k) ?_).symm
      exact Eventually.of_forall fun y hy ↦ by
        simp [hsubset hy]
    _ =
        ⨍ y in Set.Icc ((k : ℝ) / (2 : ℝ) ^ n) ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n),
          (Set.indicator (Set.Icc (0 : ℝ) 1) f) y ∂volume := by
      apply setAverage_congr
      simpa [s, dyadicInterval] using
        (Ico_ae_eq_Icc (μ := volume) (a := (k : ℝ) / (2 : ℝ) ^ n)
          (b := (((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n))

/-- Helper for Exercise 11.2.9: the closed dyadic cell is the closed ball with midpoint center and
dyadic radius. -/
private theorem dyadicClosedCell_eq_closedBall (n : ℕ) (k : Fin (2 ^ n)) :
    Set.Icc ((k : ℝ) / (2 : ℝ) ^ n) ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
      Metric.closedBall ((((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)))
        (((2 : ℝ) ^ (n + 1))⁻¹) := by
  -- Normalize the midpoint and radius in `Real.Icc_eq_closedBall`.
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcenter :
      (((k : ℝ) / (2 : ℝ) ^ n) +
          ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)) / 2 =
        ((((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))) := by
    rw [pow_succ]
    field_simp [hpow.ne']
    norm_num
    ring
  have hradius :
      (((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - (k : ℝ) / (2 : ℝ) ^ n) / 2 =
        (((2 : ℝ) ^ (n + 1))⁻¹) := by
    rw [pow_succ]
    field_simp [hpow.ne']
    norm_num
  rw [Real.Icc_eq_closedBall, hcenter, hradius]

/-- Helper for Exercise 11.2.9: specialize the closed-ball differentiation theorem to `ℕ`. -/
private theorem aeTendstoAverageClosedBallNat {g : ℝ → ℝ}
    (hg_loc : LocallyIntegrable g volume) :
    ∀ᵐ x ∂volume, ∀ (w δ : ℕ → ℝ),
      Tendsto δ atTop (𝓝[>] 0) →
      (∀ᶠ n in atTop, x ∈ Metric.closedBall (w n) (1 * δ n)) →
      Tendsto (fun n ↦ ⨍ y in Metric.closedBall (w n) (δ n), g y ∂volume) atTop (𝓝 (g x)) := by
  -- Pin down the indexing filter so the final theorem does not rely on polymorphic inference.
  filter_upwards
      [(IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume) (K := (1 : ℝ))
        (f := g) hg_loc)] with x hx w δ hδ hmem
  exact hx (ι := ℕ) (l := atTop) w δ hδ hmem

/-- Helper for Exercise 11.2.9: the dyadic approximation at a point is the ambient-volume average
of the truncated function on the matching closed dyadic ball. -/
private theorem dyadicApproximation_eq_closedBallAverage_of_mem {f : ℝ → ℝ} {n : ℕ}
    {k : Fin (2 ^ n)} {x : ℝ} (hx : x ∈ dyadicInterval n k) :
    let g := Set.indicator (Set.Icc (0 : ℝ) 1) f
    dyadicAverageApproximation f n x =
      ⨍ y in Metric.closedBall ((((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)))
          (((2 : ℝ) ^ (n + 1))⁻¹), g y ∂volume := by
  -- Package the dyadic closed cell as the closed ball expected by differentiation theory.
  dsimp
  calc
    dyadicAverageApproximation f n x =
        ⨍ y in Set.Icc ((k : ℝ) / (2 : ℝ) ^ n) ((((k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n),
          (Set.indicator (Set.Icc (0 : ℝ) 1) f) y ∂volume := by
      rw [dyadicAverageApproximation_eq_setAverage_of_mem hx,
        dyadicInterval_setAverage_eq_closedCellAverage_indicator (f := f) (n := n) (k := k)]
    _ =
        ⨍ y in Metric.closedBall ((((2 * (k : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)))
            (((2 : ℝ) ^ (n + 1))⁻¹), (Set.indicator (Set.Icc (0 : ℝ) 1) f) y ∂volume := by
      rw [dyadicClosedCell_eq_closedBall n k]

-- Proof sketch: the source-facing dyadic filtration records the σ-algebras generated by the
-- dyadic interval families. The preceding bridge identifies `dyadicAverageApproximation f n` with
-- `𝔼[f | dyadicFiltration n]`, and the dyadic σ-algebras increase to the full Borel σ-algebra on
-- `[0,1]`. Lévy's upward theorem in the form `Integrable.tendsto_ae_condExp` then yields
-- almost-everywhere convergence to `f`.
/-- Exercise 11.2.9: for an integrable function on `[0,1]`, the dyadic interval averages converge
almost everywhere to the original function. -/
theorem ae_tendsto_dyadicAverageApproximation_of_integrable {f : ℝ → ℝ}
    (hf : Integrable f unitIntervalLebesgue) :
    ∀ᵐ x ∂unitIntervalLebesgue,
      Tendsto (fun n ↦ dyadicAverageApproximation f n x) atTop (𝓝 (f x)) := by
  -- Route correction: the conditional-expectation closure needs `f` to be strongly measurable on
  -- the dyadic supremum, which is the wrong interface for an arbitrary `f : ℝ → ℝ`.
  -- Route correction: rewrite each dyadic value as a closed-ball average of the ambient-volume
  -- truncation `g`, then apply the closed-ball differentiation theorem.
  let g : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) f
  have hg_int : Integrable g volume := by
    -- `hf` is exactly integrability of `f` on the restricted unit interval.
    dsimp [g]
    rw [integrable_indicator_iff measurableSet_Icc]
    simpa [IntegrableOn] using hf
  have hg_loc : LocallyIntegrable g volume := hg_int.locallyIntegrable
  have hdiff :
      ∀ᵐ x ∂volume, ∀ (w δ : ℕ → ℝ),
        Tendsto δ atTop (𝓝[>] 0) →
        (∀ᶠ n in atTop, x ∈ Metric.closedBall (w n) (1 * δ n)) →
        Tendsto (fun n ↦ ⨍ y in Metric.closedBall (w n) (δ n), g y ∂volume) atTop
          (𝓝 (g x)) :=
    aeTendstoAverageClosedBallNat (g := g) hg_loc
  have hmem_Ico : ∀ᵐ x ∂unitIntervalLebesgue, x ∈ Set.Ico (0 : ℝ) 1 := by
    -- The restricted measure only sees interior points of `[0,1]` up to the null endpoint `{1}`.
    change ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1), x ∈ Set.Ico (0 : ℝ) 1
    rw [← restrict_Ico_eq_restrict_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)]
    exact ae_restrict_mem measurableSet_Ico
  filter_upwards [ae_restrict_of_ae hdiff, hmem_Ico] with x hx_diff hxIco
  have hkx_lt (n : ℕ) : ⌊x * (2 : ℝ) ^ n⌋₊ < 2 ^ n := by
    -- Reuse the floor-index range lemma instead of replaying the arithmetic here.
    exact floorIndex_lt_twoPow (n := n) hxIco
  let kx : ∀ n : ℕ, Fin (2 ^ n) := fun n ↦ ⟨⌊x * (2 : ℝ) ^ n⌋₊, hkx_lt n⟩
  have hx_mem_kx (n : ℕ) : x ∈ dyadicInterval n (kx n) := by
    -- Reuse the stable bridge from the floor-selected index to the dyadic cell membership.
    simpa [dyadicInterval, kx] using mem_dyadicInterval_floorIndex (n := n) hxIco
  let center : ℕ → ℝ :=
    fun n ↦ (((2 * ((kx n : Fin (2 ^ n)) : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
  let radius : ℕ → ℝ := fun n ↦ ((2 : ℝ) ^ (n + 1))⁻¹
  have hradius : Tendsto radius atTop (𝓝[>] 0) := by
    -- The dyadic radii are the reciprocals of a sequence tending to `+∞`.
    simpa [radius] using
      (tendsto_inv_atTop_nhdsGT_zero.comp <|
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1))
  have hx_closedBall :
      ∀ᶠ n in atTop, x ∈ Metric.closedBall (center n) (1 * radius n) := by
    -- Each chosen dyadic cell yields a closed ball that still contains `x`.
    exact Eventually.of_forall fun n ↦ by
      have hx_cell : x ∈
          Set.Icc (((kx n : Fin (2 ^ n)) : ℝ) / (2 : ℝ) ^ n)
            (((((kx n : Fin (2 ^ n)) : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
        exact ⟨(hx_mem_kx n).1, (hx_mem_kx n).2.le⟩
      have hx_ball :
          x ∈ Metric.closedBall
              ((((2 * ((kx n : Fin (2 ^ n)) : ℕ) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)))
              (((2 : ℝ) ^ (n + 1))⁻¹) := by
        rwa [← dyadicClosedCell_eq_closedBall n (kx n)]
      simpa [center, radius, one_mul] using hx_ball
  have hclosedBall :
      Tendsto (fun n ↦ ⨍ y in Metric.closedBall (center n) (radius n), g y ∂volume) atTop
        (𝓝 (g x)) := hx_diff center radius hradius hx_closedBall
  have hrewrite :
      (fun n ↦ dyadicAverageApproximation f n x) =ᶠ[atTop]
        fun n ↦ ⨍ y in Metric.closedBall (center n) (radius n), g y ∂volume := by
    -- The dyadic approximation agrees pointwise with the closed-ball average interface.
    exact Eventually.of_forall fun n ↦
      dyadicApproximation_eq_closedBallAverage_of_mem (f := f) (x := x) (k := kx n)
        (hx_mem_kx n)
  have hdyadic : Tendsto (fun n ↦ dyadicAverageApproximation f n x) atTop (𝓝 (g x)) := by
    exact Tendsto.congr' hrewrite.symm hclosedBall
  -- On `[0,1)`, the indicator truncation `g` agrees with the original function `f`.
  simpa [g, hxIco.1, hxIco.2.le] using hdyadic

end

end MeasureTheory
