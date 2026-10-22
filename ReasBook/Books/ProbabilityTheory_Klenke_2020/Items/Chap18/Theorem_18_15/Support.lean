/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_3
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

section Metropolis

variable (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞)
variable (hq : IsStochasticMatrix q)
variable (hπ_pos : ∀ x : E, 0 < (π : Measure E) ({x} : Set E))
variable (h_support_symm : ∀ x y : E, 0 < q x y ↔ 0 < q y x)
variable [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]

/-- Helper for Theorem 18.15: evaluating `discreteMatrixKernel p` on a singleton recovers the
corresponding matrix entry. -/
private theorem discreteMatrixKernel_apply_singleton_eq_entry
    (p : E → E → ℝ≥0∞) (x y : E) :
    discreteMatrixKernel p y ({x} : Set E) = p y x := by
  -- Proof comment: expand the row measure into weighted Dirac masses and keep only `{x}`.
  rw [discreteMatrixKernel_apply]
  simp +contextual [tsum_eq_single x]

/-- Helper for Theorem 18.15: an irreducible count-measure kernel lives on a countable state
space, because every state appears in the countable union of the positive singleton supports of the
iterated laws from one reference point. -/
private theorem countableOfIrreducibleCountKernel
    (κ : Kernel E E) [IsMarkovKernel κ] [Kernel.IsIrreducible (Measure.count : Measure E) κ] :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E := fun n ↦ {y : E | 0 < (κ ^ n) x₀ ({y} : Set E)}
    have hreachable_countable : ∀ n, (reachable n).Countable := by
      intro n
      let μ : Measure E := (κ ^ n) x₀
      have hμ_univ : μ Set.univ = 1 := by
        dsimp [μ]
        induction n with
        | zero =>
            change (Kernel.id x₀) Set.univ = 1
            simp [Kernel.id_apply]
        | succ n ihn =>
            rw [Kernel.pow_succ_apply_eq_lintegral κ n x₀ MeasurableSet.univ]
            simp [ihn]
      letI : IsFiniteMeasure μ := ⟨by simp [hμ_univ]⟩
      -- Proof comment: each `n`-step law is a probability measure, so only countably many
      -- singleton masses can be positive.
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
          simp
        -- Proof comment: irreducibility reaches every singleton with positive counting mass.
        rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
            (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x₀ with
          ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa [reachable] using hn⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

include hq hπ_pos h_support_symm

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: evaluating the Metropolis kernel on a singleton returns the
corresponding Metropolis matrix entry. -/
private theorem metropolisKernel_apply_singleton
    (x y : E) :
    metropolisKernel π q x ({y} : Set E) =
      metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q x y := by
  -- Proof comment: unfold the kernel once and evaluate the discrete matrix row on the singleton.
  rw [metropolisKernel_def, discreteMatrixKernel_apply_singleton_eq_entry]

omit [DiscreteMeasurableSpace E] hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: if the proposal matrix has a positive diagonal entry at `x`, then
the Metropolis matrix also has a positive diagonal entry there. -/
private theorem metropolisDiagonal_pos_of_proposalDiagonal_pos
    (x : E) (hxx : 0 < q x x) :
    0 <
      metropolisMatrix
        (fun z : E ↦ (π : Measure E) ({z} : Set E)) q x x := by
  classical
  let w : E → ℝ≥0∞ := fun z : E ↦ (π : Measure E) ({z} : Set E)
  set S : ℝ≥0∞ := ∑' z : E, metropolisOffDiagonalEntry w q x z
  set T : ℝ≥0∞ := ∑' z : E, ite (z = x) 0 (q x z)
  have hqxx_le_one : q x x ≤ 1 := by
    calc
      q x x ≤ ∑' z : E, q x z := ENNReal.le_tsum x
      _ = 1 := hq x
  have hS_le_T : S ≤ T := by
    -- Proof comment: every off-diagonal Metropolis entry is bounded by the corresponding proposal
    -- entry, while the diagonal term is zero in both sums.
    refine ENNReal.tsum_le_tsum ?_
    intro z
    by_cases hz : z = x
    · simp [hz, metropolisOffDiagonalEntry]
    · calc
        metropolisOffDiagonalEntry w q x z ≤ q x z :=
          metropolisOffDiagonalEntry_le_proposal w q x z
        _ = ite (z = x) 0 (q x z) := by simp [hz]
  have hT_add : T + q x x = 1 := by
    calc
      T + q x x = q x x + T := by rw [add_comm]
      _ = ∑' z : E, q x z := by
            simpa [T] using (ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ q x z) x).symm
      _ = 1 := hq x
  have hT_le_one : T ≤ 1 := by
    calc
      T ≤ T + q x x := by
        exact le_add_of_nonneg_right (zero_le _)
      _ = 1 := hT_add
  have hT_ne_one : T ≠ 1 := by
    intro hT_one
    have hqxx_zero : q x x = 0 := by
      simpa [hT_one] using hT_add
    exact (ne_of_gt hxx) hqxx_zero
  have hT_lt_one : T < 1 := by
    exact lt_of_le_of_ne hT_le_one hT_ne_one
  have hS_lt_one : S < 1 := lt_of_le_of_lt hS_le_T hT_lt_one
  -- Proof comment: the Metropolis diagonal is the remaining row mass after the off-diagonal sum.
  rw [metropolisMatrix_apply_diag]
  simpa [S] using (tsub_pos_iff_lt.mpr hS_lt_one)

omit [DiscreteMeasurableSpace E]
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: away from the diagonal, the Metropolis matrix has positive mass
exactly on the positive-support edges of the proposal matrix. -/
private theorem metropolisMatrix_apply_offDiag_pos_iff
    {x y : E} (hxy : x ≠ y) :
    0 <
      metropolisMatrix
        (fun z : E ↦ (π : Measure E) ({z} : Set E)) q x y ↔
      0 < q x y := by
  constructor
  · intro hmet
    by_cases hqxy : q x y = 0
    · -- Proof comment: if the proposal edge vanishes, the off-diagonal Metropolis edge vanishes
      -- as well, contradicting the assumed positivity.
      have : False := by
        simp [metropolisMatrix_apply_offDiag_of_eq_zero
          (π := fun z : E ↦ (π : Measure E) ({z} : Set E)) (q := q) hxy hqxy] at hmet
      exact False.elim this
    · exact pos_iff_ne_zero.mpr hqxy
  · intro hqxy
    let w : E → ℝ≥0∞ := fun z : E ↦ (π : Measure E) ({z} : Set E)
    have hwx_lt_top : w x < ∞ := by
      calc
        w x ≤ (π : Measure E) Set.univ := by
          exact measure_mono (by simp)
        _ = 1 := by simp
        _ < ∞ := ENNReal.one_lt_top
    have hqxy_le_one : q x y ≤ 1 := by
      calc
        q x y ≤ ∑' z : E, q x z := ENNReal.le_tsum y
        _ = 1 := hq x
    have hqxy_lt_top : q x y < ∞ :=
      lt_of_le_of_lt hqxy_le_one ENNReal.one_lt_top
    have hqyx_pos : 0 < q y x := (h_support_symm x y).mp hqxy
    have hratio_pos :
        0 < w y * q y x / (w x * q x y) := by
      have hnum_pos : 0 < w y * q y x :=
        ENNReal.mul_pos (hπ_pos y).ne' hqyx_pos.ne'
      have hden_lt_top : w x * q x y < ∞ :=
        ENNReal.mul_lt_top hwx_lt_top hqxy_lt_top
      exact ENNReal.div_pos_iff.2 ⟨hnum_pos.ne', hden_lt_top.ne⟩
    have hmin_pos : 0 < min 1 (w y * q y x / (w x * q x y)) :=
      lt_min (by simp) hratio_pos
    -- Proof comment: once the proposal edge is positive, the acceptance factor is positive too,
    -- so the Metropolis off-diagonal mass is positive.
    rw [metropolisMatrix_apply_offDiag_of_pos (π := w) (q := q) hxy hqxy]
    exact ENNReal.mul_pos hqxy.ne' hmin_pos.ne'

omit [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: a positive proposal singleton transition stays positive after the
Metropolis acceptance step. -/
private theorem metropolisKernel_pos_of_proposalKernel_pos
    {x y : E}
    (hxy : 0 < discreteMatrixKernel q x ({y} : Set E)) :
    0 < metropolisKernel π q x ({y} : Set E) := by
  rw [discreteMatrixKernel_apply_singleton_eq_entry (p := q) (x := y) (y := x)] at hxy
  rw [metropolisKernel_apply_singleton (π := π) (q := q) (x := x) (y := y)]
  by_cases hdiag : x = y
  · subst hdiag
    -- Proof comment: on the diagonal, positive proposal mass forces positive leftover row mass.
    exact metropolisDiagonal_pos_of_proposalDiagonal_pos
      (π := π) (q := q) (hq := hq) x hxy
  · -- Proof comment: off the diagonal, positivity is exactly the support-positivity equivalence
    -- proved above.
    exact (metropolisMatrix_apply_offDiag_pos_iff
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) hdiag).2 hxy

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: a positive `(n + 1)`-step singleton transition factors through an
intermediate state hit after `n` steps followed by a positive one-step transition. -/
private theorem existsPositiveTransitionMidpoint [Countable E]
    {κ : Kernel E E} {n : ℕ} {x z : E}
    (hxz : 0 < (κ ^ (n + 1)) x ({z} : Set E)) :
    ∃ y : E, 0 < (κ ^ n) x ({y} : Set E) ∧ 0 < κ y ({z} : Set E) := by
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)] at hxz
  have htsum_pos :
      0 <
        ∑' u : E,
          κ u ({z} : Set E) * ((κ ^ n) x) ({u} : Set E) := by
    simpa [MeasureTheory.lintegral_countable', mul_comm] using hxz
  classical
  by_contra hmid
  have hterm_zero :
      ∀ u : E, κ u ({z} : Set E) * ((κ ^ n) x) ({u} : Set E) = 0 := by
    intro u
    by_cases hxu : 0 < (κ ^ n) x ({u} : Set E)
    · have huz : ¬ 0 < κ u ({z} : Set E) := by
        intro huz
        exact hmid ⟨u, hxu, huz⟩
      have huz_zero : κ u ({z} : Set E) = 0 := bot_unique (not_lt.mp huz)
      simp [huz_zero]
    · have hxu_zero : (κ ^ n) x ({u} : Set E) = 0 := bot_unique (not_lt.mp hxu)
      simp [hxu_zero]
  have htsum_zero :
      ∑' u : E,
        κ u ({z} : Set E) * ((κ ^ n) x) ({u} : Set E) = 0 := by
    exact ENNReal.tsum_eq_zero.mpr hterm_zero
  exact htsum_pos.ne' htsum_zero

omit [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: every positive singleton transition probability for a proposal
iterate remains positive for the Metropolis iterate of the same length. -/
private theorem metropolisPowerSingletonPos_of_proposalPowerSingletonPos [Countable E] :
    ∀ ⦃n : ℕ⦄ ⦃x y : E⦄,
      0 < ((discreteMatrixKernel q) ^ n) x ({y} : Set E) →
        0 < ((metropolisKernel π q) ^ n) x ({y} : Set E) := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : IsMarkovKernel (metropolisKernel π q) := metropolisKernel_isMarkovKernel π q hq
  intro n x y hxy
  induction n generalizing x y with
  | zero =>
      -- Proof comment: at time zero both kernels are the identity kernel.
      simpa [pow_zero] using hxy
  | succ n ih =>
      -- Proof comment: extract a positive midpoint for the proposal path, transport the tail by
      -- induction and the last step by the one-step Metropolis positivity bridge, then compose.
      rcases existsPositiveTransitionMidpoint
          (κ := discreteMatrixKernel q) (x := x) (z := y) (hxz := hxy) with
        ⟨z, hxz, hzy⟩
      have hxz_met :
          0 < ((metropolisKernel π q) ^ n) x ({z} : Set E) :=
        ih (x := x) (y := z) hxz
      have hzy_met :
          0 < metropolisKernel π q z ({y} : Set E) :=
        metropolisKernel_pos_of_proposalKernel_pos
          (π := π) (q := q) hq hπ_pos h_support_symm hzy
      -- Proof comment: keep the positive singleton contribution of the midpoint `z` in the
      -- Chapman-Kolmogorov formula for the Metropolis kernel.
      rw [Kernel.pow_succ_apply_eq_lintegral (metropolisKernel π q) n x (measurableSet_singleton y)]
      have hsingleton :
          0 < ∫⁻ b in ({z} : Set E), (metropolisKernel π q) b ({y} : Set E) ∂
            (((metropolisKernel π q) ^ n) x) := by
        rw [MeasureTheory.lintegral_singleton]
        exact ENNReal.mul_pos hzy_met.ne' hxz_met.ne'
      have hmono :
          ∫⁻ b in ({z} : Set E), (metropolisKernel π q) b ({y} : Set E) ∂
            (((metropolisKernel π q) ^ n) x) ≤
            ∫⁻ b in Set.univ, (metropolisKernel π q) b ({y} : Set E) ∂
              (((metropolisKernel π q) ^ n) x) :=
        MeasureTheory.lintegral_mono_set
          (show ({z} : Set E) ⊆ Set.univ from Set.subset_univ _)
      exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: on a countable discrete space, the `μ`-flow from `A` to `B` through
`discreteMatrixKernel p` expands as the double countable sum of `p x y * μ {x}` over `A × B`. -/
private theorem discreteMatrixKernel_flow [Countable E]
    {p : E → E → ℝ≥0∞} {μ : Measure E}
    (A B : Set E) (hB : MeasurableSet B) :
    ∫⁻ x in A, discreteMatrixKernel p x B ∂μ =
      ∑' x : E,
        Set.indicator A
          (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ p x y * μ ({x} : Set E)) y) x := by
  classical
  -- Proof comment: expand the restricted integral against `μ.restrict A`, then rewrite the
  -- restricted singleton masses explicitly.
  rw [MeasureTheory.lintegral_countable']
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · have hrestrict :
        (μ.restrict A) ({x} : Set E) = μ ({x} : Set E) := by
        rw [Measure.restrict_apply (MeasurableSet.singleton x)]
        simp [hx]
    rw [Set.indicator_of_mem hx]
    rw [discreteMatrixKernel_apply, hrestrict, Measure.sum_apply _ hB, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      simp [Measure.smul_apply, hy]
    · rw [Set.indicator_of_notMem hy]
      simp [Measure.smul_apply, hy, zero_mul]
  · have hrestrict :
        (μ.restrict A) ({x} : Set E) = 0 := by
        rw [Measure.restrict_apply (MeasurableSet.singleton x)]
        simp [hx]
    rw [Set.indicator_of_notMem hx, hrestrict]
    simp

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: a countable discrete kernel is reversible once its singleton masses
satisfy detailed balance. -/
private theorem discreteMatrixKernel_isReversible_of_detailedBalance [Countable E]
    {p : E → E → ℝ≥0∞} {μ : Measure E}
    (hbal : ∀ x y : E, p x y * μ ({x} : Set E) = p y x * μ ({y} : Set E)) :
    Kernel.IsReversible (discreteMatrixKernel p) μ := by
  classical
  intro A B hA hB
  let flowTerm : E → E → ℝ≥0∞ := fun x y ↦
    if x ∈ A ∧ y ∈ B then p x y * μ ({x} : Set E) else 0
  have hflow_left :
      ∑' x : E,
        Set.indicator A
          (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ p x y * μ ({x} : Set E)) y) x
        = ∑' x : E, ∑' y : E, flowTerm x y := by
    -- Proof comment: package the two membership tests into one indicator on `A × B`.
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      refine tsum_congr fun y ↦ ?_
      by_cases hy : y ∈ B
      · simp [flowTerm, hx, hy]
      · simp [flowTerm, hx, hy]
    · rw [Set.indicator_of_notMem hx]
      symm
      exact ENNReal.tsum_eq_zero.mpr (fun y ↦ by simp [flowTerm, hx])
  have hflow_right :
      ∑' y : E,
        Set.indicator B
          (fun y ↦ ∑' x : E, Set.indicator A (fun x ↦ p y x * μ ({y} : Set E)) x) y
        = ∑' y : E, ∑' x : E, flowTerm x y := by
    -- Proof comment: after swapping the variables, detailed balance turns the reversed edge
    -- weight back into the forward one.
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      refine tsum_congr fun x ↦ ?_
      by_cases hx : x ∈ A
      · simp [flowTerm, hx, hy, hbal y x]
      · simp [flowTerm, hx, hy]
    · rw [Set.indicator_of_notMem hy]
      symm
      exact ENNReal.tsum_eq_zero.mpr (fun x ↦ by simp [flowTerm, hy])
  calc
    ∫⁻ x in A, discreteMatrixKernel p x B ∂μ
      = ∑' x : E,
        Set.indicator A
          (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ p x y * μ ({x} : Set E)) y) x :=
        discreteMatrixKernel_flow
          (p := p) (μ := μ) A B hB
    _ = ∑' x : E, ∑' y : E, flowTerm x y := hflow_left
    _ = ∑' y : E, ∑' x : E, flowTerm x y := ENNReal.tsum_comm
    _ = ∑' y : E,
        Set.indicator B
          (fun y ↦ ∑' x : E, Set.indicator A (fun x ↦ p y x * μ ({y} : Set E)) x) y :=
          hflow_right.symm
    _ = ∫⁻ x in B, discreteMatrixKernel p x A ∂μ :=
        (discreteMatrixKernel_flow
          (p := p) (μ := μ) B A hA).symm

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: positive singleton transitions compose across kernel powers. -/
private theorem positiveSingletonComp [Countable E]
    {κ : Kernel E E} {m n : ℕ} {x y z : E}
    (hxy : 0 < (κ ^ m) x ({y} : Set E))
    (hyz : 0 < (κ ^ n) y ({z} : Set E)) :
    0 < (κ ^ (m + n)) x ({z} : Set E) := by
  -- Proof comment: expand the Chapman-Kolmogorov integral and keep the positive contribution
  -- coming from the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton :
      0 < ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set
      (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

omit [DiscreteMeasurableSpace E] hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: for a positive finite `a`, the Metropolis acceptance factor turns
`a * min 1 (b / a)` into the symmetric quantity `min a b`. -/
private theorem mul_min_one_div_eq_min
    {a b : ℝ≥0∞} (ha_pos : 0 < a) (ha_lt_top : a < ∞) :
    a * min 1 (b / a) = min a b := by
  -- Proof comment: distribute `a` over the minimum and then cancel the `a` in the quotient term.
  rw [mul_min_of_nonneg _ _ ha_pos.le, mul_one, ENNReal.mul_div_cancel ha_pos.ne' ha_lt_top.ne]

omit [DiscreteMeasurableSpace E]
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: the Metropolis matrix satisfies detailed balance with respect to the
singleton masses of `π`. -/
private theorem metropolisMatrix_detailedBalance
    (x y : E) :
    metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q x y *
        (π : Measure E) ({x} : Set E) =
      metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q y x *
        (π : Measure E) ({y} : Set E) := by
  classical
  let w : E → ℝ≥0∞ := fun z : E ↦ (π : Measure E) ({z} : Set E)
  by_cases hxy : x = y
  · subst hxy
    rfl
  · have hyx : y ≠ x := fun hyx ↦ hxy hyx.symm
    by_cases hqxy : q x y = 0
    · have hqyx : q y x = 0 := by
        by_contra hqyx
        have hqyx_pos : 0 < q y x := pos_iff_ne_zero.mpr hqyx
        have hqxy_pos : 0 < q x y := (h_support_symm x y).mpr hqyx_pos
        exact hqxy_pos.ne' hqxy
      -- Proof comment: if the proposal edge vanishes in one direction, support symmetry forces it
      -- to vanish in the other direction as well, so both weighted entries are zero.
      rw [metropolisMatrix_apply_offDiag_of_eq_zero (π := w) (q := q) hxy hqxy]
      rw [metropolisMatrix_apply_offDiag_of_eq_zero (π := w) (q := q) hyx hqyx]
      simp
    · have hqxy_pos : 0 < q x y := pos_iff_ne_zero.mpr hqxy
      have hqyx_pos : 0 < q y x := (h_support_symm x y).mp hqxy_pos
      have hwx_lt_top : w x < ∞ := by
        calc
          w x ≤ (π : Measure E) Set.univ := by
            exact measure_mono (by simp)
          _ = 1 := by simp
          _ < ∞ := ENNReal.one_lt_top
      have hwy_lt_top : w y < ∞ := by
        calc
          w y ≤ (π : Measure E) Set.univ := by
            exact measure_mono (by simp)
          _ = 1 := by simp
          _ < ∞ := ENNReal.one_lt_top
      have hqxy_lt_top : q x y < ∞ := by
        calc
          q x y ≤ ∑' z : E, q x z := ENNReal.le_tsum y
          _ = 1 := hq x
          _ < ∞ := ENNReal.one_lt_top
      have hqyx_lt_top : q y x < ∞ := by
        calc
          q y x ≤ ∑' z : E, q y z := ENNReal.le_tsum x
          _ = 1 := hq y
          _ < ∞ := ENNReal.one_lt_top
      have ha_pos : 0 < w x * q x y := ENNReal.mul_pos (hπ_pos x).ne' hqxy
      have hb_pos : 0 < w y * q y x := ENNReal.mul_pos (hπ_pos y).ne' hqyx_pos.ne'
      have ha_lt_top : w x * q x y < ∞ := ENNReal.mul_lt_top hwx_lt_top hqxy_lt_top
      have hb_lt_top : w y * q y x < ∞ := ENNReal.mul_lt_top hwy_lt_top hqyx_lt_top
      -- Proof comment: both off-diagonal directions reduce to the same symmetric `min` normal
      -- form, so detailed balance is just `min_comm`.
      calc
        metropolisMatrix w q x y * w x
          = (w x * q x y) * min 1 (w y * q y x / (w x * q x y)) := by
              rw [metropolisMatrix_apply_offDiag_of_pos (π := w) (q := q) hxy hqxy_pos]
              simp [w, mul_assoc, mul_left_comm, mul_comm]
        _ = min (w x * q x y) (w y * q y x) :=
              mul_min_one_div_eq_min
                (a := w x * q x y) (b := w y * q y x) ha_pos ha_lt_top
        _ = min (w y * q y x) (w x * q x y) := by rw [min_comm]
        _ = (w y * q y x) * min 1 (w x * q x y / (w y * q y x)) :=
              (mul_min_one_div_eq_min
                (a := w y * q y x) (b := w x * q x y) hb_pos hb_lt_top).symm
        _ = metropolisMatrix w q y x * w y := by
              rw [metropolisMatrix_apply_offDiag_of_pos (π := w) (q := q) hyx hqyx_pos]
              simp [w, mul_assoc, mul_left_comm, mul_comm]

omit [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: the Metropolis kernel is reversible with respect to `π`. -/
private theorem metropolisKernel_isReversible [Countable E] :
    Kernel.IsReversible (metropolisKernel π q) (π : Measure E) := by
  -- Proof comment: the singleton detailed-balance identity is exactly the entrywise hypothesis of
  -- the countable discrete owner theorem.
  simpa [metropolisKernel_def] using
    (discreteMatrixKernel_isReversible_of_detailedBalance
      (p := metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q)
      (μ := (π : Measure E))
      (hbal := metropolisMatrix_detailedBalance
        (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
        (h_support_symm := h_support_symm)))

omit hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: if every Metropolis diagonal entry vanishes, then the Metropolis
matrix agrees pointwise with the proposal matrix. -/
private theorem metropolisMatrix_eq_proposal_of_zero_diag [Countable E]
    (hdiag : ∀ x : E, metropolisKernel π q x ({x} : Set E) = 0) :
    metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q = q := by
  classical
  let w : E → ℝ≥0∞ := fun z : E ↦ (π : Measure E) ({z} : Set E)
  funext x y
  have hdiag_matrix : metropolisMatrix w q x x = 0 := by
    rw [← metropolisKernel_apply_singleton
      (π := π) (q := q) (x := x) (y := x)]
    simpa [w] using hdiag x
  let f : E → ℝ≥0∞ := fun z ↦ ite (z = x) 0 (metropolisMatrix w q x z)
  let g : E → ℝ≥0∞ := fun z ↦ ite (z = x) 0 (q x z)
  have hmet_row : ∑' z : E, metropolisMatrix w q x z = 1 :=
    metropolisMatrix_isStochasticMatrix w q hq x
  have hq_row : ∑' z : E, q x z = 1 := hq x
  have hmet_offdiag : ∑' z : E, f z = 1 := by
    have hsplit := (ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ metropolisMatrix w q x z) x).symm
    simpa [f, hdiag_matrix, hmet_row] using hsplit
  have hfg : ∀ z : E, f z ≤ g z := by
    intro z
    by_cases hzx : z = x
    · simp [f, g, hzx]
    · have hxz : x ≠ z := fun hxz ↦ hzx hxz.symm
      simp only [f, g, if_neg hzx]
      rw [metropolisMatrix_apply_offDiag (π := w) (q := q) hxz]
      exact metropolisOffDiagonalEntry_le_proposal w q x z
  have hq_offdiag_le : ∑' z : E, g z ≤ 1 := by
    calc
      ∑' z : E, g z ≤ q x x + ∑' z : E, g z := by
        exact le_add_of_nonneg_left (show 0 ≤ q x x by simp)
      _ = ∑' z : E, q x z := by
            simpa [g, add_comm] using
              (ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ q x z) x).symm
      _ = 1 := hq_row
  have hq_offdiag_eq : ∑' z : E, g z = 1 := by
    refine le_antisymm hq_offdiag_le ?_
    simpa [hmet_offdiag] using (ENNReal.tsum_le_tsum hfg)
  have hqxx_zero : q x x = 0 := by
    have hsplit := (ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ q x z) x).symm
    have hsum : q x x + ∑' z : E, g z = 1 := by
      simpa [g, hq_row, add_comm] using hsplit
    simpa [hq_offdiag_eq] using hsum
  by_cases hxy : x = y
  · subst hxy
    simpa [hdiag_matrix, hqxx_zero]
  · have hle : metropolisMatrix w q x y ≤ q x y := by
      rw [metropolisMatrix_apply_offDiag (π := w) (q := q) hxy]
      exact metropolisOffDiagonalEntry_le_proposal w q x y
    have hnot_lt : ¬ metropolisMatrix w q x y < q x y := by
      intro hlt
      have hyx : y ≠ x := fun hyx ↦ hxy hyx.symm
      have hy_lt : f y < g y := by
        simpa [f, g, hyx] using hlt
      have hsum_lt :
          ∑' z : E, f z < ∑' z : E, g z :=
        ENNReal.tsum_lt_tsum (by simp [hmet_offdiag]) hfg hy_lt
      simp [hmet_offdiag, hq_offdiag_eq] at hsum_lt
    exact le_antisymm hle (le_of_not_gt hnot_lt)

-- Proof sketch: use the support symmetry hypothesis to show that every positive-probability
-- proposal edge for `q` remains a positive-probability Metropolis edge, because the acceptance
-- factor is strictly positive once the singleton masses of `π` are positive. Any positive
-- counting-measure set reachable from an irreducible proposal kernel is therefore still reachable
-- for the Metropolis kernel.
/-- First conclusion of the Metropolis theorem in this section: if the proposal matrix `q` is
stochastic and irreducible,
the support of `q` is symmetric, and the target distribution `π` has strictly positive singleton
masses, then the Metropolis kernel built from `q` and `π` is irreducible with respect to counting
measure. -/
private theorem metropolisKernel_isIrreducible_of_irreducible_proposal :
    Kernel.IsIrreducible (Measure.count : Measure E) (metropolisKernel π q) := by
  classical
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : IsMarkovKernel (metropolisKernel π q) := metropolisKernel_isMarkovKernel π q hq
  let _ : Countable E := countableOfIrreducibleCountKernel (κ := discreteMatrixKernel q)
  constructor
  intro A hA hApos x
  obtain ⟨y, hyA⟩ : A.Nonempty := by
    exact MeasureTheory.nonempty_of_measure_ne_zero
      (μ := Measure.count) (ne_of_gt hApos)
  have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by simp
  let hirr : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q) :=
    inferInstance
  rcases hirr.irreducible (MeasurableSet.singleton y) hy_pos x with
    ⟨n, hn⟩
  have hn_met :
      0 < ((metropolisKernel π q) ^ n) x ({y} : Set E) :=
    metropolisPowerSingletonPos_of_proposalPowerSingletonPos
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) hn
  -- Proof comment: reach a positive singleton first and then enlarge the target from `{y}` to `A`.
  refine ⟨n, lt_of_lt_of_le hn_met ?_⟩
  exact measure_mono (Set.singleton_subset_iff.mpr hyA)

omit [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: period `1` for the proposal kernel at a state transfers to period
`1` for the Metropolis kernel at the same state. -/
private theorem metropolisStatePeriodOne_of_proposalStatePeriodOne
    [Countable E]
    (x : E) (hx_period_q : statePeriod (discreteMatrixKernel q) x = 1) :
    statePeriod (metropolisKernel π q) x = 1 := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : IsMarkovKernel (metropolisKernel π q) := metropolisKernel_isMarkovKernel π q hq
  rcases eventually_positive_self_return_probability_at_period_multiples
      (κ := discreteMatrixKernel q) x with ⟨n₀, hn₀⟩
  have hret₀_q :
      0 < ((discreteMatrixKernel q) ^ n₀) x ({x} : Set E) := by
    -- Proof comment: period `1` gives a positive return at the first eventual multiple.
    simpa [hx_period_q, mem_positiveTransitionStepSet_iff] using hn₀ le_rfl
  have hret₁_q :
      0 < ((discreteMatrixKernel q) ^ (n₀ + 1)) x ({x} : Set E) := by
    -- Proof comment: the next multiple gives a second positive return time one step later.
    simpa [hx_period_q, mem_positiveTransitionStepSet_iff] using hn₀ (Nat.le_succ n₀)
  have hret₀_met :
      n₀ ∈ positiveTransitionStepSet (metropolisKernel π q) x x := by
    -- Proof comment: transport the positive `n₀`-step singleton return through the Metropolis
    -- kernel power comparison.
    rw [mem_positiveTransitionStepSet_iff]
    exact metropolisPowerSingletonPos_of_proposalPowerSingletonPos
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) hret₀_q
  have hret₁_met :
      n₀ + 1 ∈ positiveTransitionStepSet (metropolisKernel π q) x x := by
    -- Proof comment: the same transport works for the consecutive return time `n₀ + 1`.
    rw [mem_positiveTransitionStepSet_iff]
    exact metropolisPowerSingletonPos_of_proposalPowerSingletonPos
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) hret₁_q
  have hdvd₀ :
      statePeriod (metropolisKernel π q) x ∣ n₀ :=
    statePeriod_dvd_of_mem_positiveTransitionStepSet (metropolisKernel π q) x hret₀_met
  have hdvd₁ :
      statePeriod (metropolisKernel π q) x ∣ n₀ + 1 :=
    statePeriod_dvd_of_mem_positiveTransitionStepSet (metropolisKernel π q) x hret₁_met
  have hdvd_one : statePeriod (metropolisKernel π q) x ∣ 1 := by
    -- Proof comment: divisibility of two consecutive return times forces the period to divide `1`.
    simpa using Nat.dvd_sub hdvd₁ hdvd₀
  exact Nat.eq_one_of_dvd_one hdvd_one

omit hq hπ_pos h_support_symm
  [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)] in
/-- Helper for Theorem 18.15: one positive self-loop in an irreducible Markov kernel forces
aperiodicity. -/
private theorem isAperiodic_of_irreducible_existsPositiveSelfLoop
    {κ : Kernel E E} [IsMarkovKernel κ]
    [Kernel.IsIrreducible (Measure.count : Measure E) κ]
    (hloop : ∃ x : E, 0 < κ x ({x} : Set E)) :
    IsAperiodic κ := by
  rw [isAperiodic_iff_hasPeriod_one]
  rcases hloop with ⟨x, hx⟩
  have hself : 1 ∈ positiveTransitionStepSet κ x x := by
    -- Proof comment: a positive one-step self-loop is exactly membership of time `1` in the
    -- positive transition-step set.
    rw [mem_positiveTransitionStepSet_iff]
    simpa [pow_one] using hx
  have hx_period : statePeriod κ x = 1 := by
    -- Proof comment: the state period must divide the positive return time `1`.
    exact Nat.eq_one_of_dvd_one <|
      statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hself
  intro y
  -- Proof comment: irreducibility identifies all state periods, so period `1` propagates to every
  -- state.
  simpa [hx_period] using (statePeriod_eq (κ := κ) x y).symm

/-- Helper for Theorem 18.15: if every Metropolis diagonal entry vanishes, then the proposal
kernel is reversible with respect to `π`. -/
theorem proposalReversible_of_zeroMetropolisDiagonal
    (hdiag : ∀ x : E, metropolisKernel π q x ({x} : Set E) = 0) :
    Kernel.IsReversible (discreteMatrixKernel q) (π : Measure E) := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : Countable E := countableOfIrreducibleCountKernel (κ := discreteMatrixKernel q)
  have hmatrix_eq :
      metropolisMatrix (fun z : E ↦ (π : Measure E) ({z} : Set E)) q = q :=
    metropolisMatrix_eq_proposal_of_zero_diag
      (π := π) (q := q) (hq := hq) hdiag
  -- Proof comment: vanishing Metropolis diagonals force the whole Metropolis matrix back to the
  -- proposal matrix, so reversibility of the Metropolis kernel transfers directly to the proposal.
  simpa [metropolisKernel_def, hmatrix_eq] using
    (metropolisKernel_isReversible
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm))

/-- Helper for Theorem 18.15: proposal aperiodicity transfers to the Metropolis kernel by
transporting period `1` at each state. -/
theorem metropolisKernel_isAperiodic_of_proposalAperiodic
    (haperiodic : IsAperiodic (discreteMatrixKernel q)) :
    IsAperiodic (metropolisKernel π q) := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : IsMarkovKernel (metropolisKernel π q) := metropolisKernel_isMarkovKernel π q hq
  let _ : Countable E := countableOfIrreducibleCountKernel (κ := discreteMatrixKernel q)
  rw [isAperiodic_iff_hasPeriod_one] at haperiodic
  rw [isAperiodic_iff_hasPeriod_one]
  intro x
  -- Proof comment: the proposal branch closes pointwise through the period-transport lemma that
  -- preserves singleton return positivity under the Metropolis acceptance step.
  exact metropolisStatePeriodOne_of_proposalStatePeriodOne
    (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
    (h_support_symm := h_support_symm) x (haperiodic x)

/-- Helper for Theorem 18.15: if the proposal kernel is not reversible with respect to `π`, then
the Metropolis kernel is aperiodic. -/
theorem metropolisKernel_isAperiodic_of_notProposalReversible
    (hnonreversible : ¬ Kernel.IsReversible (discreteMatrixKernel q) (π : Measure E)) :
    IsAperiodic (metropolisKernel π q) := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  let _ : IsMarkovKernel (metropolisKernel π q) := metropolisKernel_isMarkovKernel π q hq
  let _ : Countable E := countableOfIrreducibleCountKernel (κ := discreteMatrixKernel q)
  let _ : Kernel.IsIrreducible (Measure.count : Measure E) (metropolisKernel π q) :=
    metropolisKernel_isIrreducible_of_irreducible_proposal
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm)
  have hloop : ∃ x : E, 0 < metropolisKernel π q x ({x} : Set E) := by
    classical
    by_contra hnone
    have hdiag : ∀ x : E, metropolisKernel π q x ({x} : Set E) = 0 := by
      intro x
      exact le_antisymm (le_of_not_gt (fun hx ↦ hnone ⟨x, hx⟩)) bot_le
    have hproposal_reversible :
        Kernel.IsReversible (discreteMatrixKernel q) (π : Measure E) :=
      proposalReversible_of_zeroMetropolisDiagonal
        (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
        (h_support_symm := h_support_symm) hdiag
    exact hnonreversible hproposal_reversible
  -- Proof comment: once a positive self-loop exists, irreducibility upgrades it to period `1`
  -- everywhere by the generic self-loop criterion.
  exact isAperiodic_of_irreducible_existsPositiveSelfLoop
    (κ := metropolisKernel π q) hloop

end Metropolis

end ProbabilityTheory
