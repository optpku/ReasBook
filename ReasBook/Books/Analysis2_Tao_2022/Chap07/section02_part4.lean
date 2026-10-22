/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap07
section Section02

/-- Proposition 7.8: if `(A_j)_{j≥1}` is an increasing sequence of Lebesgue measurable subsets
of `ℝ^n`, then `m(⋃ j, A_j)` is the limit of `m(A_j)` as `j → ∞`. -/
theorem proposition_7_8
    (n : ℕ) (A : ℕ → Set (Fin n → ℝ))
    (h_measurable : ∀ j,
      MeasureTheory.NullMeasurableSet (A j)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
    (h_step : ∀ j, A j ⊆ A (j + 1)) :
    Filter.Tendsto
      (fun j : ℕ => (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (A j))
      Filter.atTop
      (nhds ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (⋃ j, A j))) := by
  let _ := h_measurable
  have h_mono : Monotone A := monotone_nat_of_le_succ h_step
  simpa [Function.comp] using
    (MeasureTheory.tendsto_measure_iUnion_atTop
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) h_mono)

/-- Proposition 7.9: if `(A_j)_{j≥1}` is a decreasing sequence of Lebesgue measurable subsets
of `ℝ^n` and the first set has finite measure, then `m(⋂ j, A_j)` is the limit of `m(A_j)` as
`j → ∞` (with `A 0` representing `A_1`). -/
theorem proposition_7_9
    (n : ℕ)
    (A : ℕ → Set
      (MeasureTheory.NullMeasurableSpace (Fin n → ℝ)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))))
    (h_measurable : ∀ j, MeasurableSet (A j))
    (h_step : ∀ j, A (j + 1) ⊆ A j)
    (h_finite : MeasureTheory.volume.completion (A 0) < ⊤) :
    Filter.Tendsto
      (fun j : ℕ => MeasureTheory.volume.completion (A j))
      Filter.atTop
      (nhds (MeasureTheory.volume.completion (⋂ j, A j))) := by
  have h_antitone : Antitone A := antitone_nat_of_succ_le h_step
  have h_null :
      ∀ j,
        MeasureTheory.NullMeasurableSet (A j)
          (MeasureTheory.volume.completion :
            MeasureTheory.Measure
              (MeasureTheory.NullMeasurableSpace (Fin n → ℝ)
                (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))) :=
    fun j => (h_measurable j).nullMeasurableSet
  have h_exists_finite :
      ∃ i,
        (MeasureTheory.volume.completion :
            MeasureTheory.Measure
              (MeasureTheory.NullMeasurableSpace (Fin n → ℝ)
                (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))) (A i) ≠ ⊤ :=
    ⟨0, ne_of_lt h_finite⟩
  simpa [Function.comp] using
    (MeasureTheory.tendsto_measure_iInter_atTop
      (μ := (MeasureTheory.volume.completion :
        MeasureTheory.Measure
          (MeasureTheory.NullMeasurableSpace (Fin n → ℝ)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))))
      h_null h_antitone h_exists_finite)

/-- Helper for Proposition 7.10: in dimension `0`, the interval
`Set.Ioo (0-vector) ((q : ℝ)⁻¹-vector)` is empty. -/
lemma helperForProposition_7_10_ioo_finZero_eq_empty (q : ℤ) :
    Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹) =
      (∅ : Set (Fin 0 → ℝ)) := by
  ext x
  constructor
  · intro hx
    have hx_le_zero : x ≤ fun _ : Fin 0 => (0 : ℝ) := by
      intro i
      exact Fin.elim0 i
    exact (not_lt_of_ge hx_le_zero) hx.1
  · intro hx
    exact False.elim (Set.notMem_empty x hx)

/-- Helper for Proposition 7.10: in dimension `0`, the closed interval
`Set.Icc (0-vector) ((q : ℝ)⁻¹-vector)` is all of `Fin 0 → ℝ`. -/
lemma helperForProposition_7_10_icc_finZero_eq_univ (q : ℤ) :
    Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹) =
      (Set.univ : Set (Fin 0 → ℝ)) := by
  ext x
  simp [Set.mem_Icc]

/-- Helper for Proposition 7.10: in dimension `0`, the coordinatewise open box
encoding via `Set.pi` is all of `Fin 0 → ℝ` (vacuous coordinate conditions). -/
lemma helperForProposition_7_10_piOpen_finZero_eq_univ (q : ℤ) :
    Set.pi (Set.univ : Set (Fin 0))
        (fun _ : Fin 0 => Set.Ioo (0 : ℝ) ((q : ℝ)⁻¹)) =
      (Set.univ : Set (Fin 0 → ℝ)) := by
  ext x
  simp

/-- Helper for Proposition 7.10: in dimension `0`, the function-order interval
`Set.Ioo` does not match the coordinatewise-open-box encoding by `Set.pi`. -/
lemma helperForProposition_7_10_ioo_ne_piOpen_finZero (q : ℤ) :
    Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹) ≠
      Set.pi (Set.univ : Set (Fin 0))
        (fun _ : Fin 0 => Set.Ioo (0 : ℝ) ((q : ℝ)⁻¹)) := by
  rw [helperForProposition_7_10_ioo_finZero_eq_empty (q := q),
    helperForProposition_7_10_piOpen_finZero_eq_univ (q := q)]
  intro hEq
  have hMem :
      (fun i : Fin 0 => (Fin.elim0 i : ℝ)) ∈ (∅ : Set (Fin 0 → ℝ)) := by
    simpa [hEq]
  exact Set.notMem_empty _ hMem

/-- Helper for Proposition 7.10: the volume of the `n = 0` open box encoded by
`Set.Ioo (0-vector) ((q : ℝ)⁻¹-vector)` is `0`. -/
lemma helperForProposition_7_10_volume_ioo_finZero (q : ℤ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 0 := by
  rw [helperForProposition_7_10_ioo_finZero_eq_empty (q := q), MeasureTheory.measure_empty]

/-- Helper for Proposition 7.10: the right-hand side at `n = 0` is `1`. -/
lemma helperForProposition_7_10_rhs_at_zero (q : ℤ) :
    ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))) = 1 := by
  simp

/-- Helper for Proposition 7.10: at `n = 0`, the open-box equality goal is
equivalent to `0 = 1`. -/
lemma helperForProposition_7_10_openGoal_finZero_iff_zero_eq_one (q : ℤ) :
    ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ↔ ((0 : ENNReal) = 1) := by
  constructor
  · intro hEq
    have hLhs :
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 0 :=
      helperForProposition_7_10_volume_ioo_finZero (q := q)
    have hRhs : ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) = 1 := by
      simpa using helperForProposition_7_10_rhs_at_zero (q := q)
    calc
      (0 : ENNReal) =
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
              (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) := by
            symm
            exact hLhs
      _ = ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := hEq
      _ = 1 := hRhs
  · intro hZeroEqOne
    have hLhs :
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 0 :=
      helperForProposition_7_10_volume_ioo_finZero (q := q)
    have hRhs : ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) = 1 := by
      simpa using helperForProposition_7_10_rhs_at_zero (q := q)
    calc
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 0 := hLhs
      _ = 1 := hZeroEqOne
      _ = ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := by
            symm
            exact hRhs

/-- Helper for Proposition 7.10: in dimension `0`, the open-box equality in the
current encoding is false. -/
lemma helperForProposition_7_10_openGoal_finZero_false (q : ℤ) :
    ¬ ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) := by
  intro hGoal
  have hZeroEqOne :
      (0 : ENNReal) = 1 :=
    (helperForProposition_7_10_openGoal_finZero_iff_zero_eq_one (q := q)).1 hGoal
  have hZeroNeOne : (0 : ENNReal) ≠ 1 := by
    simp
  exact hZeroNeOne hZeroEqOne

/-- Helper for Proposition 7.10: in dimension `0`, the closed-box equality
in the current encoding is true. -/
lemma helperForProposition_7_10_closedGoal_finZero_true (q : ℤ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := by
  calc
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
      ∏ i : Fin 0,
        ENNReal.ofReal
          (((fun _ : Fin 0 => (q : ℝ)⁻¹) i - (fun _ : Fin 0 => (0 : ℝ)) i) : ℝ) := by
        simpa using
          (Real.volume_Icc_pi (a := (fun _ : Fin 0 => (0 : ℝ)))
            (b := (fun _ : Fin 0 => (q : ℝ)⁻¹)))
    _ = 1 := by
        simp
    _ = ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := by
        simp

/-- Helper for Proposition 7.10: in dimension `0`, the full conjunction is
equivalent to the open-box equality since the closed-box equality is automatic. -/
lemma helperForProposition_7_10_conj_finZero_iff_openGoal (q : ℤ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))))) ↔
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))))) := by
  constructor
  · intro hConj
    exact hConj.1
  · intro hOpen
    refine ⟨hOpen, ?_⟩
    exact helperForProposition_7_10_closedGoal_finZero_true (q := q)

/-- Helper for Proposition 7.10: in dimension `0`, the full conjunction in the
current encoding is false because the open-box equality already fails. -/
lemma helperForProposition_7_10_conj_finZero_false (q : ℤ) :
    ¬ (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ∧
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))))) := by
  intro hConj
  exact helperForProposition_7_10_openGoal_finZero_false (q := q)
    ((helperForProposition_7_10_conj_finZero_iff_openGoal (q := q)).1 hConj)

/-- Helper for Proposition 7.10: in dimension `0`, the open-interval expression
has strictly smaller volume than the closed-interval expression. -/
lemma helperForProposition_7_10_volume_ioo_lt_volume_icc_finZero (q : ℤ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) <
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
        (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) := by
  have hOpen :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 0 :=
    helperForProposition_7_10_volume_ioo_finZero (q := q)
  have hClosed :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) = 1 := by
    calc
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))) := by
          simpa using helperForProposition_7_10_closedGoal_finZero_true (q := q)
      _ = 1 := by
          simp
  rw [hOpen, hClosed]
  simp

/-- Helper for Proposition 7.10: in dimension `0`, the exact theorem-shaped
conjunction is impossible since it would force equal open/closed volumes. -/
lemma helperForProposition_7_10_targetBranch_finZero_false_via_strictVolumes
    (q : ℤ) :
    ¬ ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  intro hConj
  have hEqVol :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) := by
    exact hConj.1.trans hConj.2.symm
  have hLt :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) <
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) :=
    helperForProposition_7_10_volume_ioo_lt_volume_icc_finZero (q := q)
  exact (lt_irrefl _ ) (hEqVol ▸ hLt)

/-- Helper for Proposition 7.10: at `n = 0`, the full conjunction in the current
encoding is equivalent to `False`. -/
lemma helperForProposition_7_10_conj_finZero_iff_false (q : ℤ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))))) ↔ False) := by
  constructor
  · intro hConj
    exact helperForProposition_7_10_conj_finZero_false (q := q) hConj
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.10: the `n = 0` branch in the exact target shape of
`proposition_7_10` is equivalent to `False`. -/
lemma helperForProposition_7_10_targetBranch_finZero_iff_false (q : ℤ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) ↔ False) := by
  simpa using helperForProposition_7_10_conj_finZero_iff_false (q := q)

/-- Helper for Proposition 7.10: in the exact theorem-shaped `n = 0` branch,
the conjunction would force `(0 : ENNReal) = 1`. -/
lemma helperForProposition_7_10_targetBranch_finZero_implies_zero_eq_one (q : ℤ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) →
      ((0 : ENNReal) = 1)) := by
  intro hConj
  have hOpen :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := by
    simpa using hConj.1
  exact (helperForProposition_7_10_openGoal_finZero_iff_zero_eq_one (q := q)).1 hOpen

/-- Helper for Proposition 7.10: in the exact theorem-shaped `n = 0` branch,
the conjunction is equivalent to `(0 : ENNReal) = 1`. -/
lemma helperForProposition_7_10_targetBranch_finZero_iff_zero_eq_one (q : ℤ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) ↔
      ((0 : ENNReal) = 1)) := by
  constructor
  · intro hConj
    exact helperForProposition_7_10_targetBranch_finZero_implies_zero_eq_one (q := q) hConj
  · intro hZeroEqOne
    have hOpen :
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))) := by
      simpa using
        (helperForProposition_7_10_openGoal_finZero_iff_zero_eq_one (q := q)).2 hZeroEqOne
    have hClosed :
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))) := by
      simpa using helperForProposition_7_10_closedGoal_finZero_true (q := q)
    exact ⟨hOpen, hClosed⟩

/-- Helper for Proposition 7.10: in the exact theorem-shaped `n = 0` branch,
the open-box equality is impossible. -/
lemma helperForProposition_7_10_targetOpenGoal_finZero_false (q : ℤ) :
    ¬ ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) := by
  intro hOpen
  have hOpenNat :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))) := by
    simpa using hOpen
  exact helperForProposition_7_10_openGoal_finZero_false (q := q) hOpenNat

/-- Helper for Proposition 7.10: in the exact theorem-shaped `n = 0` branch,
the full conjunction is impossible because the open-box equality already fails. -/
lemma helperForProposition_7_10_targetBranch_finZero_false_via_openGoal (q : ℤ) :
    ¬ ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  intro hConj
  exact helperForProposition_7_10_targetOpenGoal_finZero_false (q := q) hConj.1

/-- Helper for Proposition 7.10: in the exact theorem-shaped `n = 0` branch,
the conjunction is impossible. -/
lemma helperForProposition_7_10_targetBranch_finZero_false_via_zero_ne_one (q : ℤ) :
    ¬ ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  exact helperForProposition_7_10_targetBranch_finZero_false_via_openGoal (q := q)

/-- Helper for Proposition 7.10: there exists an admissible integer `q > 1`
for which the current `n = 0` conjunction is false. -/
lemma helperForProposition_7_10_exists_admissible_finZero_counterexample :
    ∃ q : ℤ,
      1 < q ∧
      ¬ (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ))))) := by
  have hTwoGtOne : (1 : ℤ) < 2 := by
    norm_num
  refine ⟨2, hTwoGtOne, ?_⟩
  simpa using helperForProposition_7_10_conj_finZero_false (q := (2 : ℤ))

/-- Helper for Proposition 7.10: in dimension `0`, the conjunction cannot hold
for every integer `q > 1` in the current encoding. -/
lemma helperForProposition_7_10_not_forall_q_gt_one_finZero :
    ¬ (∀ q : ℤ,
        1 < q →
          (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
                (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))) ∧
            ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
                (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-((0 : ℕ) : ℤ)))))) := by
  intro hAll
  have hTwoGtOne : (1 : ℤ) < 2 := by
    norm_num
  exact helperForProposition_7_10_conj_finZero_false (q := (2 : ℤ)) (hAll 2 hTwoGtOne)

/-- Helper for Proposition 7.10: in dimension `0`, there is no admissible
integer `q > 1` for which the exact target-shaped conjunction can hold. -/
lemma helperForProposition_7_10_no_admissible_q_for_targetBranch_finZero :
    ¬ ∃ q : ℤ,
      1 < q ∧
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) := by
  intro hExists
  rcases hExists with ⟨q, _hq, hConj⟩
  exact helperForProposition_7_10_targetBranch_finZero_false_via_zero_ne_one (q := q) hConj

/-- Helper for Proposition 7.10: for each admissible `q > 1`, the exact
`n = 0` branch of the current target statement is false. -/
lemma helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    ¬ (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) := by
  intro hTarget
  exact helperForProposition_7_10_no_admissible_q_for_targetBranch_finZero
    ⟨q, hq, hTarget⟩

/-- Helper for Proposition 7.10: for every admissible integer `q > 1`, the exact
`n = 0` target branch in the current encoding is refutable. -/
lemma helperForProposition_7_10_forall_gt_one_targetBranch_finZero_false :
    ∀ q : ℤ, 1 < q →
      ¬ (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) := by
  intro q hq
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one (q := q) hq

/-- Helper for Proposition 7.10: for fixed admissible `q > 1`, the exact
target-shaped conjunction cannot hold for every `n`; the `n = 0` branch
already contradicts the current encoding. -/
lemma helperForProposition_7_10_not_forall_n_targetConj_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    ¬ (∀ n : ℕ,
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) := by
  intro hAllN
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := q) hq (hAllN 0)

/-- Helper for Proposition 7.10: if the fully quantified current encoding held,
specializing to `n = 0` and `q = 2` would force `(0 : ENNReal) = 1`. -/
lemma helperForProposition_7_10_universal_currentEncoding_implies_zero_eq_one
    (hAll : ∀ n : ℕ, ∀ q : ℤ, 1 < q →
          (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
                (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
            ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
                (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    (0 : ENNReal) = 1 := by
  have hTwoGtOne : (1 : ℤ) < 2 := by
    norm_num
  have hAtTwo :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ))
              (fun _ : Fin 0 => ((2 : ℤ) : ℝ)⁻¹)) =
          ENNReal.ofReal (((2 : ℤ) : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ))
              (fun _ : Fin 0 => ((2 : ℤ) : ℝ)⁻¹)) =
          ENNReal.ofReal (((2 : ℤ) : ℝ) ^ (-(0 : ℤ))))) := by
    simpa using hAll 0 (2 : ℤ) hTwoGtOne
  exact
    (helperForProposition_7_10_targetBranch_finZero_iff_zero_eq_one (q := (2 : ℤ))).1
      hAtTwo

/-- Helper for Proposition 7.10: the fully quantified current encoding of the
statement is false, witnessed by the `n = 0`, `q = 2` branch. -/
lemma helperForProposition_7_10_universal_currentEncoding_false :
    ¬ (∀ n : ℕ, ∀ q : ℤ, 1 < q →
          (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
                (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
            ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
                (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
              ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) := by
  intro hAll
  have hZeroEqOne : (0 : ENNReal) = 1 :=
    helperForProposition_7_10_universal_currentEncoding_implies_zero_eq_one hAll
  have hZeroNeOne : (0 : ENNReal) ≠ 1 := by
    simp
  exact hZeroNeOne hZeroEqOne

/-- Helper for Proposition 7.10: the closed-box identity
`m([0, 1 / q]^n) = q^{-n}` in the current encoding. -/
lemma helperForProposition_7_10_volume_icc_eq_rhs
    (n : ℕ) (q : ℤ) (hq : 1 < q) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
  have hqRpos : 0 < (q : ℝ) := by
    exact_mod_cast (lt_trans Int.zero_lt_one hq)
  calc
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ∏ i : Fin n,
        ENNReal.ofReal
          (((fun _ : Fin n => (q : ℝ)⁻¹) i - (fun _ : Fin n => (0 : ℝ)) i) : ℝ) := by
        simpa using
          (Real.volume_Icc_pi (a := (fun _ : Fin n => (0 : ℝ)))
            (b := (fun _ : Fin n => (q : ℝ)⁻¹)))
    _ = ENNReal.ofReal ((q : ℝ)⁻¹) ^ n := by
        simp
    _ = ENNReal.ofReal (((q : ℝ)⁻¹) ^ n) := by
        symm
        exact ENNReal.ofReal_pow (inv_nonneg.mpr hqRpos.le) n
    _ = ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
        congr 1
        calc
          ((q : ℝ)⁻¹) ^ n = ((q : ℝ) ^ n)⁻¹ := by
            rw [inv_pow]
          _ = (q : ℝ) ^ (-(n : ℤ)) := by
            rw [zpow_neg, zpow_natCast]

/-- Helper for Proposition 7.10: when `n ≠ 0`, the open-interval expression
`Set.Ioo (0-vector) ((q : ℝ)⁻¹-vector)` has the same volume as the closed box. -/
lemma helperForProposition_7_10_volume_ioo_eq_volume_icc_of_ne_zero
    (n : ℕ) (q : ℤ) (hn : n ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  exact MeasureTheory.measure_congr
    (MeasureTheory.Ioo_ae_eq_Icc
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))))

/-- Helper for Proposition 7.10: when `n ≠ 0`, the open-interval expression
`Set.Ioo (0-vector) ((q : ℝ)⁻¹-vector)` has the same volume as the closed box,
so it also has measure `q^{-n}`. -/
lemma helperForProposition_7_10_volume_ioo_eq_rhs_of_ne_zero
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : n ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
  calc
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) :=
      helperForProposition_7_10_volume_ioo_eq_volume_icc_of_ne_zero n q hn
    _ = ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) :=
      helperForProposition_7_10_volume_icc_eq_rhs n q hq

/-- Helper for Proposition 7.10: when `n ≠ 0`, both the open-box and closed-box
volume identities hold in the current encoding. -/
lemma helperForProposition_7_10_conj_of_ne_zero
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : n ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) ∧
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
  refine ⟨?_, ?_⟩
  · exact helperForProposition_7_10_volume_ioo_eq_rhs_of_ne_zero n q hq hn
  · exact helperForProposition_7_10_volume_icc_eq_rhs n q hq

/-- Helper for Proposition 7.10: in the `n = 0` branch of the current encoding,
any target-shaped conjunction contradicts the admissibility hypothesis `q > 1`. -/
lemma helperForProposition_7_10_targetBranch_finZero_contradiction_of_gt_one
    (q : ℤ) (hq : 1 < q)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) :
    False := by
  exact
    (helperForProposition_7_10_forall_gt_one_targetBranch_finZero_false q hq) hConj

/-- Helper for Proposition 7.10: with `q > 1`, the exact `n = 0` target branch
of `proposition_7_10` is equivalent to `False` in the current encoding. -/
lemma helperForProposition_7_10_targetBranch_finZero_iff_false_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) ↔ False) := by
  constructor
  · intro hConj
    exact helperForProposition_7_10_targetBranch_finZero_contradiction_of_gt_one
      (q := q) hq hConj
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.10: in the current encoding, any witness of the
exact target-shaped conjunction forces `n ≠ 0`, independently of hypotheses on
`q`. -/
lemma helperForProposition_7_10_targetConj_implies_ne_zero
    (n : ℕ) (q : ℤ)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    n ≠ 0 := by
  intro hn
  subst hn
  exact helperForProposition_7_10_targetBranch_finZero_false_via_zero_ne_one
    (q := q) hConj

/-- Helper for Proposition 7.10: for `q > 1`, any witness of the exact target
conjunction must come from a nonzero dimension. -/
lemma helperForProposition_7_10_targetConj_implies_ne_zero_of_gt_one
    (n : ℕ) (q : ℤ) (hq : 1 < q)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    n ≠ 0 := by
  have _ : 1 < q := hq
  exact helperForProposition_7_10_targetConj_implies_ne_zero
    (n := n) (q := q) hConj

/-- Helper for Proposition 7.10: for `q > 1`, even the open-box equality alone
in the current encoding forces the dimension to be nonzero. -/
lemma helperForProposition_7_10_targetOpenEq_implies_ne_zero_of_gt_one
    (n : ℕ) (q : ℤ) (hq : 1 < q)
    (hOpen :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) :
    n ≠ 0 := by
  have _ : 1 < q := hq
  intro hn
  subst hn
  exact helperForProposition_7_10_openGoal_finZero_false (q := q) hOpen

/-- Helper for Proposition 7.10: if the exact target-shaped conjunction holds
and one also assumes `n = 0`, this yields a contradiction. -/
lemma helperForProposition_7_10_targetConj_false_of_eq_zero
    (n : ℕ) (q : ℤ) (hn : n = 0)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    False := by
  exact
    (helperForProposition_7_10_targetConj_implies_ne_zero
      (n := n) (q := q) hConj) hn

/-- Helper for Proposition 7.10: for `q > 1`, the exact target-shaped conjunction
in dimension `n` is equivalent to `n ≠ 0` in the current encoding. -/
lemma helperForProposition_7_10_targetConj_iff_ne_zero_of_gt_one
    (n : ℕ) (q : ℤ) (hq : 1 < q) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))))) ↔ n ≠ 0) := by
  constructor
  · intro hConj
    exact helperForProposition_7_10_targetConj_implies_ne_zero_of_gt_one
      (n := n) (q := q) hq hConj
  · intro hn
    exact helperForProposition_7_10_conj_of_ne_zero n q hq hn

/-- Helper for Proposition 7.10: if `n = 0` and `q > 1`, the target-shaped
conjunction for dimension `n` yields a contradiction in the current encoding. -/
lemma helperForProposition_7_10_targetConj_false_of_eq_zero_of_gt_one
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : n = 0)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
            (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    False := by
  have _ : 1 < q := hq
  exact
    helperForProposition_7_10_targetConj_false_of_eq_zero
      (n := n) (q := q) hn hConj

/-- Helper for Proposition 7.10: if `n = 0` and `q > 1`, the exact target-shaped
conjunction for dimension `n` is equivalent to `False` in the current encoding. -/
lemma helperForProposition_7_10_targetConj_iff_false_of_eq_zero_of_gt_one
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : n = 0) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
          (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))))) ↔ False) := by
  constructor
  · intro hConj
    exact helperForProposition_7_10_targetConj_false_of_eq_zero_of_gt_one
      (n := n) (q := q) hq hn hConj
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.10: for every admissible `q > 1`, the exact
theorem-shaped `n = 0` conjunction is unsatisfiable in the current encoding. -/
lemma helperForProposition_7_10_not_targetBranch_finZero_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    ¬ ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  intro hConj
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one (q := q) hq hConj

/-- Helper for Proposition 7.10: in dimension `0`, the open-box equality in the
current encoding fails, while the closed-box equality holds. -/
lemma helperForProposition_7_10_targetBranch_finZero_openFalse_closedTrue
    (q : ℤ) :
    (¬ ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ))))) ∧
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
          (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) := by
  refine ⟨?_, ?_⟩
  · exact helperForProposition_7_10_targetOpenGoal_finZero_false (q := q)
  · simpa using helperForProposition_7_10_closedGoal_finZero_true (q := q)

/-- Helper for Proposition 7.10: in dimension `0`, any witness of the exact
theorem-shaped conjunction forces the arithmetic constraint `q ≤ 1`. -/
lemma helperForProposition_7_10_targetBranch_finZero_implies_q_le_one
    (q : ℤ)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) :
    q ≤ 1 := by
  by_contra hNotLe
  have hq : 1 < q := lt_of_not_ge hNotLe
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := q) hq hConj

/-- Helper for Proposition 7.10: any witness of the exact theorem-shaped
`n = 0` branch forces failure of the admissibility condition `q > 1`. -/
lemma helperForProposition_7_10_targetBranch_finZero_implies_not_gt_one
    (q : ℤ)
    (hConj :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) :
    ¬ (1 < q) := by
  intro hq
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := q) hq hConj

/-- Helper for Proposition 7.10: for each admissible `q > 1`, the exact
`n = 0` conjunction required by the current target statement is not inhabited. -/
lemma helperForProposition_7_10_targetBranch_finZero_not_nonempty_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    ¬ Nonempty
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  intro hNonempty
  rcases hNonempty with ⟨hConj⟩
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := q) hq hConj

/-- Helper for Proposition 7.10: the fully quantified theorem-shaped statement in
the current encoding is inconsistent, witnessed by `n = 0` and `q = 2`. -/
lemma helperForProposition_7_10_forallTargetConj_false
    (hAll :
      ∀ n (q : ℤ), 1 < q →
        (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
              (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
            ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
              (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
            ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ)))))) :
    False := by
  have hqTwo : (1 : ℤ) < 2 := by norm_num
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := 2) hqTwo (hAll 0 2 hqTwo)

/-- Helper for Proposition 7.10: when `q > 1`, the exact theorem-shaped
`n = 0` branch type is empty in the current encoding. -/
lemma helperForProposition_7_10_targetBranch_finZero_isEmpty_of_gt_one
    (q : ℤ) (hq : 1 < q) :
    IsEmpty
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Ioo (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))
            (Set.Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (q : ℝ)⁻¹)) =
          ENNReal.ofReal ((q : ℝ) ^ (-(0 : ℤ)))))) := by
  refine ⟨?_⟩
  intro hConj
  exact helperForProposition_7_10_targetBranch_finZero_false_of_gt_one
    (q := q) hq hConj

/-- Helper for Proposition 7.10: in positive dimension, the target conjunction
follows from the nonzero-dimension case. -/
lemma helperForProposition_7_10_conj_of_pos
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : 0 < n) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) ∧
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
  exact helperForProposition_7_10_conj_of_ne_zero n q hq (Nat.ne_of_gt hn)

/-- Proposition 7.10: for positive dimension `n` and `q ∈ ℤ` with `q > 1`, the
open box `(0, 1 / q)^n = {x : ℝ^n | 0 < x_j < 1 / q for all j}` and the closed
box `[0, 1 / q]^n = {x : ℝ^n | 0 ≤ x_j ≤ 1 / q for all j}` have Lebesgue
measure `q^{-n}`. -/
theorem proposition_7_10
    (n : ℕ) (q : ℤ) (hq : 1 < q) (hn : 0 < n) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Ioo (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
      ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) ∧
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (q : ℝ)⁻¹)) =
        ENNReal.ofReal ((q : ℝ) ^ (-(n : ℤ))) := by
  exact helperForProposition_7_10_conj_of_pos n q hq hn

/-- Proposition 7.11: for an axis-parallel closed box
`B = ∏ i, [a i, b i] ⊆ ℝ^n` with `a i ≤ b i`, the set `B` is Lebesgue measurable and
its Lebesgue measure equals its box volume `∏ i, (b i - a i)`. -/
theorem proposition_7_11
    (n : ℕ) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i) :
    MeasurableSet (Set.Icc a b) ∧
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (Set.Icc a b) =
        ENNReal.ofReal (∏ i, (b i - a i)) := by
  have hMeasurable : MeasurableSet (Set.Icc a b) := by
    exact isClosed_Icc.measurableSet
  have hNonneg : ∀ i : Fin n, 0 ≤ b i - a i := by
    intro i
    exact sub_nonneg.mpr (h i)
  have hVolumeIcc :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (Set.Icc a b) =
        ∏ i : Fin n, ENNReal.ofReal (b i - a i) := by
    simpa using (Real.volume_Icc_pi (a := a) (b := b))
  have hProdOfReal :
      (∏ i : Fin n, ENNReal.ofReal (b i - a i)) =
        ENNReal.ofReal (∏ i : Fin n, (b i - a i)) := by
    have hAux :
        ENNReal.ofReal (∏ i : Fin n, (b i - a i)) =
          ∏ i : Fin n, ENNReal.ofReal (b i - a i) := by
      simpa using
        (ENNReal.ofReal_prod_of_nonneg
          (s := Finset.univ) (f := fun i : Fin n => b i - a i)
          (by
            intro i hi
            exact hNonneg i))
    exact hAux.symm
  have hVolume :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (Set.Icc a b) =
        ENNReal.ofReal (∏ i : Fin n, (b i - a i)) := by
    calc
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) (Set.Icc a b) =
          ∏ i : Fin n, ENNReal.ofReal (b i - a i) := hVolumeIcc
      _ = ENNReal.ofReal (∏ i : Fin n, (b i - a i)) := hProdOfReal
  exact And.intro hMeasurable hVolume

end Section02
end Chap07
