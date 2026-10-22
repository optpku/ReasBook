/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {m : ℕ} [NeZero m]

/-- Helper for Proposition 8.9: the finite maximum of a nonnegative family is bounded by its sum. -/
lemma sup'_le_sum_univ (a : Fin m → NNReal) :
    Finset.univ.sup' Finset.univ_nonempty a ≤ ∑ i, a i := by
  -- Choose an index where the finite supremum is attained.
  rcases
      Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
        Finset.univ_nonempty a with
    ⟨i, -, hi⟩
  rw [hi]
  -- The selected term is one summand of the full sum.
  simpa using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin m)))
      (f := a)
      (fun j _ ↦ show 0 ≤ a j from bot_le)
      (Finset.mem_univ i))

/-- Helper for Proposition 8.9: the sum of a finite nonnegative family is at most its cardinality
times its maximum. -/
lemma sum_le_card_nsmul_sup'_univ (a : Fin m → NNReal) :
    ∑ i, a i ≤
      ((Finset.univ : Finset (Fin m)).card : ℕ) •
        Finset.univ.sup' Finset.univ_nonempty a := by
  -- Bound each summand by the finite supremum and sum those pointwise bounds.
  simpa using
    (Finset.sum_le_card_nsmul
      (s := (Finset.univ : Finset (Fin m)))
      (f := a)
      (n := Finset.univ.sup' Finset.univ_nonempty a)
      (fun i _ ↦
        Finset.le_sup' (s := (Finset.univ : Finset (Fin m))) (f := a)
          (Finset.mem_univ i)))

-- Proof sketch: let `M = max_i α_i = Finset.univ.sup' Finset.univ_nonempty a`. The lower bound
-- `1 ≤ (∑ i, a i) / M` comes from `M ≤ ∑ i, a i`, using `Finset.single_le_sum` on an index
-- attaining the maximum. The upper bound comes from `∑ i, a i ≤ m • M`, obtained by
-- `Finset.sum_le_card_nsmul`, and then divide through by the positive quantity `M`.
/-- Proposition 8.9: for `m` nonnegative numbers with positive maximum, the ratio
`β = (∑ i, α_i) / max_i α_i` lies between `1` and `m`. -/
theorem sum_div_max_mem_Icc
    (a : Fin m → NNReal)
    (hmax_pos : 0 < Finset.univ.sup' Finset.univ_nonempty a) :
    (∑ i, a i) / (Finset.univ.sup' Finset.univ_nonempty a) ∈ Set.Icc (1 : NNReal) m := by
  rw [Set.mem_Icc]
  constructor
  · -- Divide the lower sandwich bound `M ≤ ∑ i, a i` by the positive maximum `M`.
    rw [one_le_div hmax_pos]
    exact sup'_le_sum_univ a
  · -- Divide the upper sandwich bound `∑ i, a i ≤ m * M` by the same positive maximum `M`.
    rw [div_le_iff₀ hmax_pos]
    calc
      ∑ i, a i ≤
          ((Finset.univ : Finset (Fin m)).card : ℕ) •
            Finset.univ.sup' Finset.univ_nonempty a :=
        sum_le_card_nsmul_sup'_univ a
      _ =
          (((Finset.univ : Finset (Fin m)).card : NNReal) *
            Finset.univ.sup' Finset.univ_nonempty a) := by
            rw [nsmul_eq_mul]
      _ = (m : NNReal) * Finset.univ.sup' Finset.univ_nonempty a := by
            simp [Finset.card_univ, Fintype.card_fin]

end
