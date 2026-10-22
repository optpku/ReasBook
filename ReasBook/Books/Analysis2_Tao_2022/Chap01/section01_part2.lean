/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap01.section01_part1

section Chap01
section Section01

/-- Proposition 1.9 (prop:1.9): the sequence `(1/n)_{n≥1}` viewed as a map
`ℕ → [0,1]`. -/
noncomputable def oneOverNatSeqInUnitInterval :
    ℕ → {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
  fun n =>
    if h : n = 0 then
      ⟨1, (zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one).2⟩
    else
      ⟨(1 : ℝ) / (n : ℝ), one_div_mem_Icc_zero_one_of_nat_pos n h⟩

/-- Proposition 1.9 (prop:1.9): the point `1` in the closed unit interval. -/
def unitIntervalOne : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
  ⟨1, (zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one).2⟩

/-- Proposition 1.9 (prop:1.9): the point `0` in the closed unit interval. -/
def unitIntervalZero : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
  ⟨0, (zero_mem_Icc_zero_one_and_one_mem_Icc_zero_one).1⟩

/-- Proposition 1.9 (prop:1.9): explicit values of `swapEndpointsOnUnitInterval`. -/
lemma swapEndpointsOnUnitInterval_apply_simp :
    (swapEndpointsOnUnitInterval unitIntervalOne = unitIntervalZero) ∧
    (swapEndpointsOnUnitInterval unitIntervalZero = unitIntervalOne) ∧
    (∀ x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1},
      ((x : ℝ) ≠ 0) → ((x : ℝ) ≠ 1) → swapEndpointsOnUnitInterval x = x) := by
  refine And.intro ?_ ?_
  · simp [swapEndpointsOnUnitInterval, unitIntervalOne, unitIntervalZero]
  · refine And.intro ?_ ?_
    · simp [swapEndpointsOnUnitInterval, unitIntervalOne, unitIntervalZero]
    · intro x hx0 hx1
      simp [swapEndpointsOnUnitInterval, hx0, hx1]

/-- Proposition 1.9 (prop:1.9): coercions and interior points of the sequence. -/
lemma oneOverNatSeqInUnitInterval_coe_succ_and_interior :
    (∀ n, ((oneOverNatSeqInUnitInterval (Nat.succ n) :
      {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) =
        (1 : ℝ) / (Nat.succ n : ℝ)) ∧
    (∀ n ≥ 2,
      ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 0 ∧
      ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 1) := by
  refine And.intro ?_ ?_
  · intro n
    simp [oneOverNatSeqInUnitInterval]
  · intro n hn
    have hpos_nat : 0 < n := lt_of_lt_of_le (Nat.succ_pos 1) hn
    have hgt_nat : 1 < n := lt_of_lt_of_le (Nat.lt_succ_self 1) hn
    have hpos_real : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hpos_nat
    have hgt_real : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hgt_nat
    have hn0 : n ≠ 0 := ne_of_gt hpos_nat
    have hcoe :
        ((oneOverNatSeqInUnitInterval n :
          {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) =
          (1 : ℝ) / (n : ℝ) := by
      simp [oneOverNatSeqInUnitInterval, hn0]
    have hpos_div : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := by
      exact one_div_pos.mpr hpos_real
    have hlt_one : (1 : ℝ) / (n : ℝ) < (1 : ℝ) := by
      exact (div_lt_one hpos_real).2 hgt_real
    refine And.intro ?_ ?_
    · have hne_zero : (1 : ℝ) / (n : ℝ) ≠ 0 := ne_of_gt hpos_div
      simpa [hcoe] using hne_zero
    · have hne_one : (1 : ℝ) / (n : ℝ) ≠ (1 : ℝ) := ne_of_lt hlt_one
      simpa [hcoe] using hne_one

/-- Proposition 1.9 (prop:1.9): the swapped metric on the sequence near `1`. -/
lemma swapEndpointsMetric_oneOverNatSeq_unitIntervalOne :
    ∀ n ≥ 2,
      swapEndpointsMetric (oneOverNatSeqInUnitInterval n) unitIntervalOne =
        (1 : ℝ) / (n : ℝ) := by
  intro n hn
  have hinterior :
      ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 0 ∧
      ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 1 :=
    (oneOverNatSeqInUnitInterval_coe_succ_and_interior).2 n hn
  have hxne0 : ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 0 := hinterior.1
  have hxne1 : ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) ≠ 1 := hinterior.2
  have hswap_x :
      swapEndpointsOnUnitInterval (oneOverNatSeqInUnitInterval n) =
        oneOverNatSeqInUnitInterval n :=
    (swapEndpointsOnUnitInterval_apply_simp).2.2 _ hxne0 hxne1
  have hswap_one : swapEndpointsOnUnitInterval unitIntervalOne = unitIntervalZero :=
    (swapEndpointsOnUnitInterval_apply_simp).1
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (Nat.succ_pos 1) hn)
  have hcoe :
      ((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) =
        (1 : ℝ) / (n : ℝ) := by
    simp [oneOverNatSeqInUnitInterval, hn0]
  have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by
    exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  calc
    swapEndpointsMetric (oneOverNatSeqInUnitInterval n) unitIntervalOne =
        |(swapEndpointsOnUnitInterval (oneOverNatSeqInUnitInterval n) : ℝ) -
          (swapEndpointsOnUnitInterval unitIntervalOne : ℝ)| := rfl
    _ = |((oneOverNatSeqInUnitInterval n :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : ℝ) - (unitIntervalZero : ℝ)| := by
      simp [hswap_x, hswap_one]
    _ = |(1 : ℝ) / (n : ℝ) - 0| := by
      simp [hcoe, unitIntervalZero]
    _ = |(1 : ℝ) / (n : ℝ)| := by
      simp
    _ = (1 : ℝ) / (n : ℝ) := by
      exact abs_of_nonneg hnonneg

/-- Proposition 1.9: let `X = [0,1]` with the usual metric `d(x,y)=|x-y|`,
let `f` swap `0` and `1` and fix all `x ∈ (0,1)`, and define
`d'(x,y)=|f(x)-f(y)|`. Then the sequence `(1/n)_{n≥1}` converges to `1`
with respect to `d'`. -/
theorem oneOverNat_converges_to_one_swapEndpointsMetric :
    SeqConvergesFromWith (d := swapEndpointsMetric)
      oneOverNatSeqInUnitInterval 1 unitIntervalOne := by
  unfold SeqConvergesFromWith
  intro ε hε
  rcases Real.exists_nat_pos_inv_lt hε with ⟨N0, hN0pos, hN0inv⟩
  have hN0inv' : (1 : ℝ) / (N0 : ℝ) < ε := by
    simpa [one_div] using hN0inv
  let N : ℕ := max 2 N0
  refine ⟨N, ?_, ?_⟩
  · have h1 : (1 : ℕ) ≤ 2 := by decide
    exact le_trans h1 (le_max_left 2 N0)
  · intro n hn
    have hge2 : 2 ≤ n := le_trans (le_max_left 2 N0) hn
    have hgeN0 : N0 ≤ n := le_trans (le_max_right 2 N0) hn
    have hdist :
        swapEndpointsMetric (oneOverNatSeqInUnitInterval n) unitIntervalOne =
          (1 : ℝ) / (n : ℝ) :=
      swapEndpointsMetric_oneOverNatSeq_unitIntervalOne n hge2
    have hN0pos_real : (0 : ℝ) < (N0 : ℝ) := by
      exact_mod_cast hN0pos
    have hN0le_real : (N0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hgeN0
    have hle :
        (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (N0 : ℝ) :=
      one_div_le_one_div_of_le hN0pos_real hN0le_real
    have hle' : (1 : ℝ) / (n : ℝ) ≤ ε :=
      le_trans hle (le_of_lt hN0inv')
    simpa [hdist] using hle'

/-- Helper for Proposition 1.10: bound the difference of distances by a sum. -/
lemma helperForProposition_1_10_abs_dist_dist_le {X : Type*} [MetricSpace X]
    (a b c d : X) :
    |dist a b - dist c d| ≤ dist a c + dist b d := by
  simpa [Real.dist_eq] using (dist_dist_dist_le a b c d)

/-- Helper for Proposition 1.10: combine two eventual bounds past a max index. -/
lemma helperForProposition_1_10_max_index_eventually {P Q : ℕ → Prop} {N1 N2 : ℕ}
    (hP : ∀ n ≥ N1, P n) (hQ : ∀ n ≥ N2, Q n) :
    ∀ n ≥ max N1 N2, P n ∧ Q n := by
  intro n hn
  have hN1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn
  have hN2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn
  exact ⟨hP n hN1, hQ n hN2⟩

/-- Proposition 1.10: if `x_n → x` and `y_n → y` in a metric space, then
`d(x_n,y_n)` converges to `d(x,y)`. -/
theorem dist_seq_converges_of_converges {X : Type*} [MetricSpace X]
    (x y : ℕ → X) (x0 y0 : X) :
    SeqConvergesFromWith (d := dist) x 1 x0 →
      SeqConvergesFromWith (d := dist) y 1 y0 →
      RealSeqConvergesFrom (fun n => dist (x n) (y n)) 1 (dist x0 y0) := by
  intro hx hy
  unfold RealSeqConvergesFrom
  intro ε hε
  unfold SeqConvergesFromWith at hx hy
  have hε2 : 0 < ε / 2 := by
    exact half_pos hε
  rcases hx (ε / 2) hε2 with ⟨N1, hN1, hxN1⟩
  rcases hy (ε / 2) hε2 with ⟨N2, hN2, hyN2⟩
  refine ⟨max N1 N2, ?_, ?_⟩
  · exact le_trans hN1 (le_max_left N1 N2)
  · intro n hn
    have hboth :
        dist (x n) x0 ≤ ε / 2 ∧ dist (y n) y0 ≤ ε / 2 :=
      helperForProposition_1_10_max_index_eventually
        (P := fun n => dist (x n) x0 ≤ ε / 2)
        (Q := fun n => dist (y n) y0 ≤ ε / 2)
        (N1 := N1) (N2 := N2) hxN1 hyN2 n hn
    rcases hboth with ⟨hxN, hyN⟩
    have hxN' : dist x0 (x n) ≤ ε / 2 := by
      simpa [dist_comm] using hxN
    have hyN' : dist y0 (y n) ≤ ε / 2 := by
      simpa [dist_comm] using hyN
    have hdist :
        |dist x0 y0 - dist (x n) (y n)| ≤ dist x0 (x n) + dist y0 (y n) :=
      helperForProposition_1_10_abs_dist_dist_le x0 y0 (x n) (y n)
    have hsum :
        dist x0 (x n) + dist y0 (y n) ≤ ε / 2 + ε / 2 :=
      add_le_add hxN' hyN'
    have hle :
        |dist x0 y0 - dist (x n) (y n)| ≤ ε / 2 + ε / 2 :=
      le_trans hdist hsum
    simpa [add_halves] using hle

/-- Proposition 1.30 (Comparison of ℓ^1 and ℓ^2 metrics): let `n ≥ 1` and
`x,y ∈ ℝ^n`. Then `d_{ℓ^2}(x,y) ≤ d_{ℓ^1}(x,y) ≤ √n * d_{ℓ^2}(x,y)`. -/
theorem l2Distance_le_l1Distance_le_sqrt_n_l2Distance_prop
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    l2Distance n x y ≤ taxicabMetric n x y ∧
      taxicabMetric n x y ≤ Real.sqrt (n : ℝ) * l2Distance n x y := by
  simpa using l2Distance_le_l1Distance_le_sqrt_n_l2Distance n hn x y

/-- Proposition 1.31 (Comparison of ℓ^2 and ℓ^∞ metrics): let `n ≥ 1` and
`x,y ∈ ℝ^n`. Then `(1/√n) d_{ℓ^2}(x,y) ≤ d_{ℓ^∞}(x,y) ≤ d_{ℓ^2}(x,y)`. -/
theorem one_div_sqrt_n_l2Distance_le_supNormMetric_le_l2Distance_prop
    (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → ℝ) :
    (1 / Real.sqrt (n : ℝ)) * l2Distance n x y ≤ supNormMetric n x y ∧
      supNormMetric n x y ≤ l2Distance n x y := by
  simpa using one_div_sqrt_n_l2Distance_le_supNormMetric_le_l2Distance n hn x y

/-- Proposition 1.32 (Equivalence of `ℓ^1`, `ℓ^2`, `ℓ^∞` metrics): let `n ≥ 1`.
A sequence in `ℝ^n` converges to `x` with respect to one of these metrics iff
it converges to `x` with respect to each of the other two metrics. -/
theorem l1_l2_linf_convergence_equiv_Rn_metrics
    (n : ℕ) (hn : 1 ≤ n) (x : ℕ → Fin n → ℝ) (x0 : Fin n → ℝ) :
    SeqConvergesFromWith (taxicabMetric n) x 1 x0 ↔
      (SeqConvergesFromWith (l2Distance n) x 1 x0 ∧
        SeqConvergesFromWith (supNormMetric n) x 1 x0) := by
  constructor
  · intro h_l1
    have h_l2 : SeqConvergesFromWith (l2Distance n) x 1 x0 := by
      have hle : ∀ u v, l2Distance n u v ≤ taxicabMetric n u v := by
        intro u v
        exact (l2Distance_le_l1Distance_le_sqrt_n_l2Distance_prop n hn u v).1
      exact seqConvergesFromWith_of_le hle h_l1
    have h_linf : SeqConvergesFromWith (supNormMetric n) x 1 x0 := by
      have hle : ∀ u v, supNormMetric n u v ≤ l2Distance n u v := by
        intro u v
        exact
          (one_div_sqrt_n_l2Distance_le_supNormMetric_le_l2Distance_prop n hn u v).2
      exact seqConvergesFromWith_of_le hle h_l2
    exact And.intro h_l2 h_linf
  · intro h
    have h_l2 : SeqConvergesFromWith (l2Distance n) x 1 x0 := h.1
    have hnpos_nat : 0 < n := (Nat.succ_le_iff.mp hn)
    have hnpos : 0 < (n : ℝ) := (Nat.cast_pos).2 hnpos_nat
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := (Real.sqrt_pos).2 hnpos
    have hle :
        ∀ u v, taxicabMetric n u v ≤ Real.sqrt (n : ℝ) * l2Distance n u v := by
      intro u v
      exact (l2Distance_le_l1Distance_le_sqrt_n_l2Distance_prop n hn u v).2
    exact
      seqConvergesFromWith_of_le_mul (C := Real.sqrt (n : ℝ)) hsqrt_pos hle h_l2

end Section01
end Chap01
