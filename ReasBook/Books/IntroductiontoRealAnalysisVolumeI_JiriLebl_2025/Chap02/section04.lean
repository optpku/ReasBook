/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03

section Chap02
section Section04

/-- Definition 2.4.1: A real sequence `{xₙ}` is called a *Cauchy sequence* if
for every `ε > 0` there exists `M ∈ ℕ` such that for all `n, k ≥ M` we have
`|x n - x k| < ε`. -/
def CauchySequence (x : RealSequence) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ ⦃n k : ℕ⦄, M ≤ n → M ≤ k → |x n - x k| < ε

/-- The book's notion of a Cauchy sequence of real numbers coincides with the
standard `CauchySeq` predicate from mathlib. -/
lemma cauchySequence_iff_cauchySeq (x : RealSequence) :
    CauchySequence x ↔ CauchySeq x := by
  constructor
  · intro hx
    refine (Metric.cauchySeq_iff (u := x)).2 ?_
    intro ε hε
    rcases hx ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n hn k hk
    simpa [Real.dist_eq] using hM hn hk
  · intro hx
    have hx' := (Metric.cauchySeq_iff (u := x)).1 hx
    intro ε hε
    rcases hx' ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n k hn hk
    simpa [Real.dist_eq] using hM n hn k hk

/-- Example 2.4.2: The sequence `1 / n` (with indexing starting at `n = 1`) is
Cauchy. -/
lemma example_242_one_div_nat_cauchy :
    CauchySequence (fun n : ℕ => (1 : ℝ) / (n.succ)) := by
  refine (cauchySequence_iff_cauchySeq _).2 ?_
  refine (Metric.cauchySeq_iff (u := fun n : ℕ => (1 : ℝ) / n.succ)).2 ?_
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  refine ⟨M, ?_⟩
  intro n hn k hk
  have hM1lt : (2 / ε) < (M + 1 : ℝ) := by nlinarith
  have hposM1 : 0 < (M + 1 : ℝ) := by nlinarith
  have hpos : 0 < (2 / ε) := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    exact div_pos htwo hε
  have hdiv : (1 : ℝ) / (2 / ε) = ε / 2 := by
    field_simp [hε.ne']
  have hsmallM : (1 : ℝ) / (M + 1) < ε / 2 := by
    have h := one_div_lt_one_div_of_lt hpos hM1lt
    simpa [hdiv] using h
  have hle_n : (1 : ℝ) / n.succ ≤ (1 : ℝ) / (M + 1) := by
    have hle : (M + 1 : ℝ) ≤ n.succ := by
      exact_mod_cast Nat.succ_le_succ hn
    exact one_div_le_one_div_of_le hposM1 hle
  have hle_k : (1 : ℝ) / k.succ ≤ (1 : ℝ) / (M + 1) := by
    have hle : (M + 1 : ℝ) ≤ k.succ := by
      exact_mod_cast Nat.succ_le_succ hk
    exact one_div_le_one_div_of_le hposM1 hle
  have hlt_n : (1 : ℝ) / n.succ < ε / 2 := lt_of_le_of_lt hle_n hsmallM
  have hlt_k : (1 : ℝ) / k.succ < ε / 2 := lt_of_le_of_lt hle_k hsmallM
  have hnorm_n : |(1 : ℝ) / n.succ| < ε / 2 := by
    have hnonneg : 0 ≤ (1 : ℝ) / n.succ := by positivity
    calc
      |(1 : ℝ) / n.succ| = (1 : ℝ) / n.succ := abs_of_nonneg hnonneg
      _ < ε / 2 := hlt_n
  have hnorm_k : |(1 : ℝ) / k.succ| < ε / 2 := by
    have hnonneg : 0 ≤ (1 : ℝ) / k.succ := by positivity
    calc
      |(1 : ℝ) / k.succ| = (1 : ℝ) / k.succ := abs_of_nonneg hnonneg
      _ < ε / 2 := hlt_k
  have hsum : |(1 : ℝ) / n.succ| + |(1 : ℝ) / k.succ| < ε := by
    nlinarith
  have htriangle :
      |(1 : ℝ) / n.succ - (1 : ℝ) / k.succ| ≤
        |(1 : ℝ) / n.succ| + |(1 : ℝ) / k.succ| := by
    simpa using
      (abs_sub_le ((1 : ℝ) / n.succ) 0 ((1 : ℝ) / k.succ))
  exact lt_of_le_of_lt htriangle hsum

/-- Explicit values of consecutive even and odd powers of `-1`. -/
lemma neg_one_pow_even_odd (m : ℕ) :
    (-1 : ℝ) ^ (2 * m) = 1 ∧ (-1 : ℝ) ^ (2 * m + 1) = -1 := by
  have hneg1sq : (-1 : ℝ) ^ 2 = (1 : ℝ) := by norm_num
  have h_even : (-1 : ℝ) ^ (2 * m) = 1 := by
    simp [pow_mul, hneg1sq]
  have h_odd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    calc
      (-1 : ℝ) ^ (2 * m + 1) = (-1 : ℝ) ^ (2 * m) * (-1) := by
        simp [pow_succ]
      _ = -1 := by
        simp [h_even]
  exact ⟨h_even, h_odd⟩

/-- The absolute difference of consecutive powers of `-1` is `2`. -/
lemma neg_one_pow_consecutive_abs (m : ℕ) :
    |(-1 : ℝ) ^ (2 * m) - (-1 : ℝ) ^ (2 * m + 1)| = 2 := by
  obtain ⟨h_even, h_odd⟩ := neg_one_pow_even_odd m
  norm_num [h_even, h_odd]

/-- Example 2.4.3: The sequence `{ (-1)^n }_{n = 1}^∞` is not Cauchy. -/
lemma example_243_neg_one_pow_not_cauchy :
    ¬ CauchySequence (fun n : ℕ => (-1 : ℝ) ^ n.succ) := by
  intro h
  have hpos : (0 : ℝ) < 1 := by norm_num
  rcases h 1 hpos with ⟨M, hM⟩
  let n : ℕ := 2 * M + 1
  let k : ℕ := 2 * M + 2
  have hMn : M ≤ 2 * M := by
    have h : 1 ≤ 2 := by decide
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left M h)
  have hn : M ≤ n := by
    dsimp [n]
    exact Nat.le_trans hMn (Nat.le_succ _)
  have hk : M ≤ k := by
    dsimp [k]
    have h1 : 2 * M ≤ 2 * M + 1 := Nat.le_succ _
    have h2 : 2 * M + 1 ≤ 2 * M + 2 := Nat.le_succ _
    exact Nat.le_trans hMn (Nat.le_trans h1 h2)
  have hineq := hM (n := n) (k := k) hn hk
  have habs : |(-1 : ℝ) ^ n.succ - (-1 : ℝ) ^ k.succ| = 2 := by
    have h := neg_one_pow_even_odd (M + 1)
    have hn_succ : n.succ = 2 * (M + 1) := by
      dsimp [n]
      calc
        Nat.succ (2 * M + 1) = 2 * M + 1 + 1 := by
          simp [Nat.succ_eq_add_one, add_comm]
        _ = 2 * M + 2 := by ring
        _ = 2 * (M + 1) := by ring
    have hk_succ : k.succ = 2 * (M + 1) + 1 := by
      dsimp [k]
      calc
        Nat.succ (2 * M + 2) = 2 * M + 2 + 1 := by
          simp [Nat.succ_eq_add_one, add_comm]
        _ = 2 * M + 3 := by ring
        _ = 2 * (M + 1) + 1 := by ring
    have hn_val : (-1 : ℝ) ^ n.succ = 1 := by
      rw [hn_succ]
      exact h.left
    have hk_val : (-1 : ℝ) ^ k.succ = -1 := by
      rw [hk_succ]
      exact h.right
    norm_num [hn_val, hk_val]
  linarith

/-- Proposition 2.4.4: Every Cauchy real sequence is bounded. -/
lemma cauchySequence_bounded {x : RealSequence} (hx : CauchySequence x) :
    BoundedSequence x := by
  classical
  obtain ⟨M, hM⟩ := hx 1 (by norm_num)
  have htail : ∀ ⦃n⦄, M ≤ n → |x n| ≤ |x M| + 1 := by
    intro n hn
    have hdiff : |x n - x M| < 1 := hM hn le_rfl
    have htriangle : |(x n - x M) + x M| ≤ |x n - x M| + |x M| := by
      simpa using (abs_add_le (x n - x M) (x M))
    have hdiff_le : |x n - x M| ≤ 1 := le_of_lt hdiff
    calc
      |x n| = |(x n - x M) + x M| := by ring_nf
      _ ≤ |x n - x M| + |x M| := htriangle
      _ ≤ |x M| + 1 := by nlinarith
  have hne : (Finset.range (M + 1)).Nonempty := ⟨0, by simp⟩
  let B :=
    max (|x M| + 1) ((Finset.range (M + 1)).sup' hne (fun n => |x n|))
  refine ⟨B, ?_⟩
  intro n
  by_cases hlt : n < M
  · have hn_mem : n ∈ Finset.range (M + 1) := by
      exact Finset.mem_range.mpr (lt_of_lt_of_le hlt (Nat.le_succ _))
    have hprefix :
        |x n| ≤ (Finset.range (M + 1)).sup' hne (fun m => |x m|) :=
      by
        classical
        simpa using
          ((Finset.le_sup' (s := Finset.range (M + 1)) (f := fun m => |x m|)
              (b := n)) hn_mem)
    have : |x n| ≤
        max (|x M| + 1) ((Finset.range (M + 1)).sup' hne (fun n => |x n|)) :=
      le_max_of_le_right hprefix
    simpa [B] using this
  · have hge : M ≤ n := le_of_not_gt hlt
    have htail' : |x n| ≤ |x M| + 1 := htail hge
    have : |x n| ≤
        max (|x M| + 1) ((Finset.range (M + 1)).sup' hne (fun n => |x n|)) :=
      le_trans htail' (le_max_left _ _)
    simpa [B] using this

/-- A convergent real sequence is Cauchy (ε/2 argument). -/
lemma convergentSequence_cauchySequence {x : RealSequence} :
    ConvergentSequence x → CauchySequence x := by
  intro hx
  rcases hx with ⟨l, hl⟩
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases hl (ε / 2) hε2 with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n k hn hk
  have hn' := hM n hn
  have hk' := hM k hk
  have htriangle :
      |x n - x k| ≤ |x n - l| + |x k - l| := by
    calc
      |x n - x k| = |(x n - l) + (l - x k)| := by ring_nf
      _ ≤ |x n - l| + |l - x k| := by
        simpa using (abs_add_le (x n - l) (l - x k))
      _ = |x n - l| + |x k - l| := by
        simp [abs_sub_comm]
  have hsum : |x n - l| + |x k - l| < ε := by nlinarith
  exact lt_of_le_of_lt htriangle hsum

/-- A Cauchy real sequence converges by completeness of `ℝ`. -/
lemma cauchySequence_convergentSequence {x : RealSequence} :
    CauchySequence x → ConvergentSequence x := by
  intro hx
  have hcx : CauchySeq x := (cauchySequence_iff_cauchySeq x).1 hx
  rcases cauchySeq_tendsto_of_complete hcx with ⟨l, hl⟩
  exact ⟨l, (convergesTo_iff_tendsto x l).2 hl⟩

/-- Theorem 2.4.5: A sequence of real numbers is Cauchy if and only if it
converges (using completeness of `ℝ`). -/
theorem cauchySequence_iff_convergentSequence (x : RealSequence) :
    CauchySequence x ↔ ConvergentSequence x := by
  constructor
  · exact cauchySequence_convergentSequence
  · exact convergentSequence_cauchySequence
end Section04
end Chap02
