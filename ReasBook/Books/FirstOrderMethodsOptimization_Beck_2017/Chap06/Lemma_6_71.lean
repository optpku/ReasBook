/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_51
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace (toDualMap)
open WithLp (toLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/- Lemma 6.71 is `bridge/view`: the sparse-set owner `C_[s]` already lives in
`Definition_6_12`, but the projection owner `P[...]` for this textbook `ℝ^n` result must live on
the Euclidean `ℓ²` owner `E = EuclideanSpace ℝ ι`, not on the raw function space `ι → ℝ`. The
left-hand side therefore uses the canonical transport `toLp 2 '' C_[s]`, while the right-hand side
uses the same transport on the masked coordinate vectors. Example 6.51 already owns the
source-facing function `sum_k_largest_abs` for the sum of the `s` largest absolute coordinates, so
no new sparse-vector owner should be introduced here. -/

-- Proof sketch: write `C_[s]` as the union of the coordinate subspaces supported on subsets
-- `S ⊆ ι` of cardinality `s`. For each such `S`, the projection of `x` onto that subspace is
-- `(↑S : Set ι).indicator x`, and its squared distance to `x` is the sum of the
-- squared absolute values off `S`. Minimizing that residual is equivalent to maximizing
-- `∑ i in S, |x i|`, so the minimizing supports are exactly those whose absolute-value sum equals
-- `sum_k_largest_abs s x`. The resulting projection set is therefore the image of the
-- set of optimal supports under `S ↦ (↑S : Set ι).indicator x`.
/-- Helper for Lemma 6.71: `support_mask S x` keeps the coordinates of `x` on `S` and zeros out
the complement. -/
private def support_mask (S : Finset ι) (x : E) : E :=
  toLp 2 ((↑S : Set ι).indicator x.ofLp)

/-- Helper for Lemma 6.71: `support_indicator S` is the `0/1` vector of the support `S`. -/
private def support_indicator (S : Finset ι) : E :=
  toLp 2 fun i ↦ if i ∈ S then (1 : ℝ) else 0

/-- Helper for Lemma 6.71: a point belongs to the transported sparse set exactly when it vanishes
outside some support of size `s`. -/
private lemma mem_sparse_image_iff_exists_card_eq_zero_off_support {s : ℕ}
    (hs : s ≤ Fintype.card ι) {z : E} :
    z ∈ (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) ↔
      ∃ S : Finset ι, S.card = s ∧ ∀ i, i ∉ S → z i = 0 := by
  classical
  constructor
  · rintro ⟨f, hf, rfl⟩
    let T0 : Finset ι := Finset.univ.filter fun i ↦ f i ≠ 0
    have hT0_le : T0.card ≤ s := by
      have hf' : hammingNorm f ≤ s :=
        (mem_sSparseVectors_iff_hammingNorm_le (ι := ι) (α := ℝ) s f).mp hf
      simpa [T0, hammingNorm] using hf'
    obtain ⟨S, hT0S, hS⟩ := Finset.exists_superset_card_eq hT0_le hs
    refine ⟨S, hS, ?_⟩
    intro i hiS
    by_cases hfi : f i = 0
    · simpa using hfi
    · have hiT0 : i ∈ T0 := by simp [T0, hfi]
      exact (hiS (hT0S hiT0)).elim
  · rintro ⟨S, hS, hz⟩
    refine ⟨z.ofLp, ?_, by simp⟩
    have hT0_subset : (Finset.univ.filter fun i ↦ z i ≠ 0) ⊆ S := by
      intro i hi
      by_contra hiS
      have hiz : z i = 0 := hz i hiS
      simp [hiz] at hi
    have hT0_le : (Finset.univ.filter fun i ↦ z i ≠ 0).card ≤ s := by
      calc
        (Finset.univ.filter fun i ↦ z i ≠ 0).card ≤ S.card := Finset.card_le_card hT0_subset
        _ = s := hS
    exact
      (mem_sSparseVectors_iff_hammingNorm_le (ι := ι) (α := ℝ) s z.ofLp).2 <| by
        simpa [hammingNorm] using hT0_le

/-- Helper for Lemma 6.71: the `0/1` support indicator of a size-`s` set lies in the capped
simplex owner from Example 6.50. -/
private lemma support_indicator_mem_constraint {s : ℕ} (S : Finset ι) (hS : S.card = s) :
    support_indicator (ι := ι) S ∈
      sum_of_k_largest_constraint_set ι s := by
  -- The support indicator has exactly `s` ones and every coordinate lies in `[0, 1]`.
  rw [mem_sum_of_k_largest_constraint_set_iff]
  constructor
  · simpa [support_indicator, hS]
  · intro i
    by_cases hi : i ∈ S
    · simp [support_indicator, hi]
    · simp [support_indicator, hi]

/-- Helper for Lemma 6.71: any fixed support contributes at most the top-`s` absolute-value sum. -/
private lemma sum_abs_le_sum_k_largest_abs_of_card_eq {s : ℕ}
    (S : Finset ι) (x : E) (hS : S.card = s) :
    S.sum (fun i ↦ |x i|) ≤ sum_k_largest_abs s x := by
  let absx : E := toLp 2 fun i ↦ |x i|
  have hs : s ≤ Fintype.card ι := by
    calc
      s = S.card := hS.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ S
  have habs :
      (sum_k_largest_abs s x : EReal) =
        support_function (sum_of_k_largest_constraint_set ι s) (toDualMap ℝ E absx) := by
    -- Rewrite the source-facing top-`s` absolute sum through the capped-simplex owner on `|x|`.
    simpa [sum_k_largest_abs, absx] using
      (sum_of_k_largest_values_eq_support_function_constraint_set (ι := ι) hs absx)
  have hmem : support_indicator (ι := ι) S ∈ sum_of_k_largest_constraint_set ι s :=
    support_indicator_mem_constraint (ι := ι) S hS
  have hle :
      (((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ) : EReal) ≤
        support_function (sum_of_k_largest_constraint_set ι s) (toDualMap ℝ E absx) := by
    rw [support_function_apply]
    exact le_sSup ⟨support_indicator (ι := ι) S, hmem, rfl⟩
  have hpair :
      ((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ) =
        S.sum (fun i ↦ |x i|) := by
    -- Pairing `|x|` with the support indicator is exactly the support sum.
    calc
      ((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ)
          = ∑ i : ι, absx i * support_indicator (ι := ι) S i := by
              simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
                (EuclideanSpace.inner_toLp_toLp absx.ofLp
                  (support_indicator (ι := ι) S).ofLp)
      _ = ∑ i : ι, |x i| * support_indicator (ι := ι) S i := by
            simp [absx]
      _ = S.sum (fun i ↦ |x i|) := by
            classical
            simp [support_indicator]
  have hleR :
      ((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ) ≤ sum_k_largest_abs s x := by
    have hleE :
        ((((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ)) : EReal) ≤
          sum_k_largest_abs s x := by
      calc
        ((((toDualMap ℝ E absx) (support_indicator (ι := ι) S) : ℝ)) : EReal)
            ≤ support_function (sum_of_k_largest_constraint_set ι s) (toDualMap ℝ E absx) := hle
        _ = sum_k_largest_abs s x := by rw [← habs]
    exact_mod_cast hleE
  simpa [hpair] using hleR

/-- Helper for Lemma 6.71: equal-cardinality supports have equal numbers of exchanged indices. -/
private lemma sdiff_card_eq_of_card_eq (S T : Finset ι) (hcard : S.card = T.card) :
    (S \ T).card = (T \ S).card := by
  have hs : (S \ T).card = S.card - (S ∩ T).card := by
    simpa [Finset.inter_comm] using (Finset.card_sdiff (s := T) (t := S))
  have ht : (T \ S).card = T.card - (S ∩ T).card := by
    simpa using (Finset.card_sdiff (s := S) (t := T))
  rw [hs, ht, hcard]

/-- Helper for Lemma 6.71: if every exchanged element of `S` dominates every exchanged element of
`T`, then the exchanged sum of `T` is no larger than the exchanged sum of `S`. -/
private lemma sum_sdiff_le_of_pairwise_le (w : ι → ℝ) (S T : Finset ι)
    (hcard : (S \ T).card = (T \ S).card)
    (hle : ∀ i ∈ S \ T, ∀ j ∈ T \ S, w j ≤ w i) :
    (T \ S).sum w ≤ (S \ T).sum w := by
  classical
  by_cases hST : (S \ T).Nonempty
  · have hTS : (T \ S).Nonempty := by
      apply Finset.card_pos.mp
      rw [← hcard]
      exact Finset.card_pos.mpr hST
    let m : ℝ := ((S \ T).image w).min' (by
      rcases hST with ⟨i, hi⟩
      exact ⟨w i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
    have hm_mem : m ∈ (S \ T).image w := Finset.min'_mem _ _
    have hm_le_right : ∀ i ∈ S \ T, m ≤ w i := by
      intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hleft : ∀ j ∈ T \ S, w j ≤ m := by
      intro j hj
      rcases Finset.mem_image.mp hm_mem with ⟨i, hi, him⟩
      simpa [m, him] using hle i hi j hj
    have hsum_left : (T \ S).sum w ≤ (T \ S).card • m :=
      Finset.sum_le_card_nsmul _ _ _ hleft
    have hsum_right : (T \ S).card • m ≤ (S \ T).sum w := by
      simpa [hcard] using (Finset.card_nsmul_le_sum (S \ T) w m hm_le_right)
    exact le_trans hsum_left hsum_right
  · have hST0 : S \ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hST
    have hTS0 : T \ S = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [← hcard, Finset.card_eq_zero.mpr hST0]
    simp [hST0, hTS0]

/-- Helper for Lemma 6.71: the no-beneficial-swap condition upgrades to global maximality among
supports of the same cardinality. -/
private lemma sum_le_of_exchange_property (w : ι → ℝ) (S T : Finset ι)
    (hcard : S.card = T.card)
    (hle : ∀ i ∈ S, ∀ j, j ∉ S → w j ≤ w i) :
    T.sum w ≤ S.sum w := by
  classical
  have hdiff : (S \ T).card = (T \ S).card := sdiff_card_eq_of_card_eq S T hcard
  have hsdiff : (T \ S).sum w ≤ (S \ T).sum w := by
    refine sum_sdiff_le_of_pairwise_le w S T hdiff ?_
    intro i hi j hj
    exact hle i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
  have hsumS : S.sum w = (S ∩ T).sum w + (S \ T).sum w := by
    have hsplit :=
      Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) (f := w) Finset.inter_subset_left
    simpa [add_comm, Finset.inter_comm] using hsplit.symm
  have hsumT : T.sum w = (S ∩ T).sum w + (T \ S).sum w := by
    have hsplit :=
      Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := T) (f := w) Finset.inter_subset_right
    simpa [add_comm, Finset.inter_comm] using hsplit.symm
  rw [hsumS, hsumT]
  linarith

/-- Helper for Lemma 6.71: on a fixed support, the squared distance splits into the on-support
error plus the off-support residual of the mask. -/
private lemma mask_distance_sq_decomposition (S : Finset ι) (x y : E)
    (hy : ∀ i, i ∉ S → y i = 0) :
    ‖y - x‖ ^ (2 : ℕ) =
      ‖y - support_mask S x‖ ^ (2 : ℕ) + ‖x - support_mask S x‖ ^ (2 : ℕ) := by
  -- Rewrite all three squared norms coordinatewise and split by `i ∈ S`.
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi_univ
  by_cases hi : i ∈ S
  · simp [support_mask, hi, Set.indicator_of_mem]
  · have hyi : y i = 0 := hy i hi
    simp [support_mask, hi, hyi, Set.indicator_of_notMem]

/-- Helper for Lemma 6.71: the residual of masking on `S` is the total square minus the square
mass captured on `S`. -/
private lemma mask_residual_sq_total (S : Finset ι) (x : E) :
    ‖x - support_mask S x‖ ^ (2 : ℕ) =
      (∑ i : ι, |x i| ^ (2 : ℕ)) - S.sum (fun i ↦ |x i| ^ (2 : ℕ)) := by
  let w : ι → ℝ := fun i ↦ |x i| ^ (2 : ℕ)
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs]
  calc
    ∑ i : ι, |(x - support_mask S x) i| ^ (2 : ℕ)
        = ∑ i : ι, (w i - if i ∈ S then w i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi_univ
            by_cases hi : i ∈ S
            · simp [w, support_mask, hi, Set.indicator_of_mem]
            · simp [w, support_mask, hi, Set.indicator_of_notMem]
    _ = (∑ i : ι, w i) - ∑ i : ι, if i ∈ S then w i else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i : ι, w i) - S.sum w := by
          exact congrArg (fun t : ℝ ↦ (∑ i : ι, w i) - t) (Finset.sum_ite_mem_eq S w)

/-- Helper for Lemma 6.71: if swapping `i ∈ S` for `j ∉ S` cannot decrease the residual, then the
`j`th absolute coordinate is no larger than the `i`th. -/
private lemma abs_le_of_swapped_residual_sq_le (S : Finset ι) (x : E) {i j : ι}
    (hi : i ∈ S) (hj : j ∉ S)
    (hmin :
      ‖x - support_mask S x‖ ^ (2 : ℕ) ≤
        ‖x - support_mask (insert j (S.erase i)) x‖ ^ (2 : ℕ)) :
    |x j| ≤ |x i| := by
  let w : ι → ℝ := fun k ↦ |x k| ^ (2 : ℕ)
  have hres :
      (∑ k : ι, w k) - S.sum w ≤
        (∑ k : ι, w k) - (insert j (S.erase i)).sum w := by
    simpa [w, mask_residual_sq_total] using hmin
  have hsumS : S.sum w = (S.erase i).sum w + w i := by
    -- Split off the exchanged coordinate `i` from the original support sum.
    simpa [w, add_comm] using (Finset.sum_erase_add (s := S) (f := w) hi).symm
  have hsumT : (insert j (S.erase i)).sum w = (S.erase i).sum w + w j := by
    -- The swapped support adds the new coordinate `j` to the erased support.
    simp [w, hj, add_comm]
  have hw : w j ≤ w i := by
    rw [hsumS, hsumT] at hres
    linarith
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hw

/-- Helper for Lemma 6.71: if `S` already attains the top-`s` absolute-value sum, then swapping an
outside coordinate into `S` cannot improve that sum. -/
private lemma abs_le_of_top_sum_swap {s : ℕ} (S : Finset ι) (x : E)
    (hScard : S.card = s)
    (hSsum : S.sum (fun k ↦ |x k|) = sum_k_largest_abs s x)
    {i j : ι} (hi : i ∈ S) (hj : j ∉ S) :
    |x j| ≤ |x i| := by
  let T : Finset ι := insert j (S.erase i)
  have hTcard : T.card = s := by
    -- Swapping one inside index for one outside index preserves the support size.
    calc
      T.card = (S.erase i).card + 1 := by simp [T, hj]
      _ = S.card := by
            rw [Finset.card_erase_of_mem hi]
            exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨i, hi⟩)
      _ = s := hScard
  have hTsum :
      T.sum (fun k ↦ |x k|) ≤ sum_k_largest_abs s x :=
    sum_abs_le_sum_k_largest_abs_of_card_eq (S := T) x hTcard
  rw [← hSsum] at hTsum
  have hsumS :
      S.sum (fun k ↦ |x k|) = (S.erase i).sum (fun k ↦ |x k|) + |x i| := by
    -- Split off the exchanged coordinate `i` from the original support sum.
    simpa [add_comm] using
      (Finset.sum_erase_add (s := S) (f := fun k ↦ |x k|) hi).symm
  have hsumT :
      T.sum (fun k ↦ |x k|) = (S.erase i).sum (fun k ↦ |x k|) + |x j| := by
    -- The swapped support adds the new coordinate `j` to the erased support.
    simp [T, hj, add_comm]
  rw [hsumS, hsumT] at hTsum
  linarith

/-- Helper for Lemma 6.71: a support satisfying the no-beneficial-swap condition already realizes
the top-`s` absolute-value sum. -/
private lemma sum_k_largest_abs_le_support_sum_of_swap_condition {s : ℕ}
    (S : Finset ι) (x : E) (hScard : S.card = s)
    (hle : ∀ i ∈ S, ∀ j, j ∉ S → |x j| ≤ |x i|) :
    sum_k_largest_abs s x ≤ S.sum (fun i ↦ |x i|) := by
  classical
  by_cases hSempty : S = ∅
  · have hs0 : s = 0 := by simpa [hSempty] using hScard.symm
    subst hs0
    simp [sum_k_largest_abs, sum_of_k_largest_values, hSempty]
  let absx : E := toLp 2 fun i ↦ |x i|
  have hs : s ≤ Fintype.card ι := by
    calc
      s = S.card := hScard.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ S
  have habs :
      (sum_k_largest_abs s x : EReal) =
        support_function (sum_of_k_largest_constraint_set ι s) (toDualMap ℝ E absx) := by
    -- Rewrite the source-facing absolute-value sum through the capped-simplex owner on `|x|`.
    simpa [sum_k_largest_abs, absx] using
      (sum_of_k_largest_values_eq_support_function_constraint_set (ι := ι) hs absx)
  have hsupport :
      support_function (sum_of_k_largest_constraint_set ι s) (toDualMap ℝ E absx) ≤
        S.sum (fun i ↦ |x i|) := by
    rw [support_function_apply]
    apply sSup_le
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_sum_of_k_largest_constraint_set_iff] at hy
    let w : ι → ℝ := fun i ↦ |x i|
    have himage_nonempty : (S.image w).Nonempty := by
      rcases Finset.nonempty_iff_ne_empty.mpr hSempty with ⟨i, hi⟩
      exact ⟨w i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let m : ℝ := (S.image w).min' himage_nonempty
    have hm_le : ∀ i ∈ S, m ≤ w i := by
      intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have houtside_le : ∀ j, j ∉ S → w j ≤ m := by
      intro j hj
      exact Finset.le_min' (s := S.image w) (H := himage_nonempty) (x := w j) (by
        intro b hb
        rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
        exact hle i hi j hj)
    have hpair :
        ((toDualMap ℝ E absx) y : ℝ) = ∑ i : ι, w i * y i := by
      -- Rewrite the Euclidean pairing with `|x|` as the coordinate sum.
      calc
        ((toDualMap ℝ E absx) y : ℝ)
            = ∑ i : ι, absx i * y i := by
                simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
                  (EuclideanSpace.inner_toLp_toLp absx.ofLp y.ofLp)
        _ = ∑ i : ι, w i * y i := by
              simp [absx, w]
    have hsplit :
        (Finset.univ \ S).sum (fun i ↦ y i) + S.sum y = s := by
      -- Split the simplex mass into the chosen support and its complement.
      calc
        (Finset.univ \ S).sum (fun i ↦ y i) + S.sum y = ∑ i : ι, y i := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ) (f := y)
                (Finset.subset_univ S))
        _ = s := hy.1
    have hmass :
        (Finset.univ \ S).sum (fun i ↦ y i) = S.sum (fun i ↦ 1 - y i) := by
      -- The outside mass equals the total missing mass on the chosen support.
      have hsum_ones : S.sum (fun _ ↦ (1 : ℝ)) = s := by
        simpa [hScard]
      have hdef :
          S.sum (fun i ↦ 1 - y i) = S.sum (fun _ ↦ (1 : ℝ)) - S.sum y := by
        simpa using (Finset.sum_sub_distrib : S.sum (fun i ↦ (1 : ℝ) - y i) =
          S.sum (fun _ ↦ (1 : ℝ)) - S.sum y)
      rw [hdef]
      linarith
    have houtside :
        (Finset.univ \ S).sum (fun i ↦ w i * y i) ≤
          S.sum (fun i ↦ w i * (1 - y i)) := by
      have houtside_to_m :
          (Finset.univ \ S).sum (fun i ↦ w i * y i) ≤ m * (Finset.univ \ S).sum (fun i ↦ y i) := by
        calc
          (Finset.univ \ S).sum (fun i ↦ w i * y i)
              ≤ (Finset.univ \ S).sum (fun i ↦ m * y i) := by
                  refine Finset.sum_le_sum ?_
                  intro i hi
                  have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
                  have hyi : 0 ≤ y i := (hy.2 i).1
                  exact mul_le_mul_of_nonneg_right (houtside_le i hiS) hyi
          _ = m * (Finset.univ \ S).sum (fun i ↦ y i) := by
                rw [Finset.mul_sum]
      have hm_to_inside :
          m * (Finset.univ \ S).sum (fun i ↦ y i) ≤
            S.sum (fun i ↦ w i * (1 - y i)) := by
        calc
          m * (Finset.univ \ S).sum (fun i ↦ y i)
              = S.sum (fun i ↦ m * (1 - y i)) := by rw [hmass, Finset.mul_sum]
          _ ≤ S.sum (fun i ↦ w i * (1 - y i)) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hyi1 : y i ≤ 1 := (hy.2 i).2
                have hdef : 0 ≤ 1 - y i := by linarith
                exact mul_le_mul_of_nonneg_right (hm_le i hi) hdef
      exact le_trans houtside_to_m hm_to_inside
    have hsum_split :
        ∑ i : ι, w i * y i =
          S.sum (fun i ↦ w i * y i) + (Finset.univ \ S).sum (fun i ↦ w i * y i) := by
      -- Split the pairing sum into the chosen support and the complement.
      symm
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ) (f := fun i ↦ w i * y i)
          (Finset.subset_univ S))
    have hreal :
        ((toDualMap ℝ E absx) y : ℝ) ≤ S.sum (fun i ↦ w i) := by
      calc
        ((toDualMap ℝ E absx) y : ℝ) = ∑ i : ι, w i * y i := hpair
        _ = S.sum (fun i ↦ w i * y i) + (Finset.univ \ S).sum (fun i ↦ w i * y i) := by
              rw [hsum_split]
        _ ≤ S.sum (fun i ↦ w i * y i) + S.sum (fun i ↦ w i * (1 - y i)) := by
              gcongr
        _ = S.sum (fun i ↦ w i) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
    have hreal' : ((toDualMap ℝ E absx) y : ℝ) ≤ S.sum (fun i ↦ |x i|) := by
      simpa [w] using hreal
    have hrealE :
        ((((toDualMap ℝ E absx) y : ℝ)) : EReal) ≤ (((S.sum (fun i ↦ |x i|) : ℝ)) : EReal) :=
      EReal.coe_le_coe_iff.mpr hreal'
    simpa using hrealE
  have hleE : (sum_k_largest_abs s x : EReal) ≤ S.sum (fun i ↦ |x i|) := by
    rw [habs]
    exact hsupport
  exact_mod_cast hleE

/-- Lemma 6.71: if `s ≤ Fintype.card ι`, then the Euclidean projection set onto the transported
set `toLp 2 '' C_s` of `s`-sparse vectors is exactly the image of the optimal support sets under
the transported masking map `S ↦ toLp 2 ((↑S : Set ι).indicator x.ofLp)`, where `S` has
cardinality `s` and captures the `s` largest absolute coordinates of `x` through the owner
`sum_k_largest_abs`. Specializing to `ι = Fin n` recovers the textbook `ℝ^n` statement. -/
theorem projection_mapping_sSparseVectors_eq_top_abs_coordinate_projections
    {s : ℕ} (hs : s ≤ Fintype.card ι) (x : E) :
    P[(toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E)] x =
      (fun S : Finset ι ↦ toLp 2 ((↑S : Set ι).indicator x.ofLp)) ''
        {S : Finset ι |
          S.card = s ∧
          S.sum (fun i ↦ |x i|) = sum_k_largest_abs s x} := by
  classical
  ext y
  constructor
  · intro hy
    have hy_mem : y ∈ (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) :=
      (mem_projection_mapping_iff.mp hy).1
    have hy_min : IsMinOn (fun z ↦ ‖z - x‖)
        (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) y :=
      (mem_projection_mapping_iff.mp hy).2
    rcases (mem_sparse_image_iff_exists_card_eq_zero_off_support (ι := ι) (s := s) hs).mp hy_mem with
      ⟨S, hScard, hy_zero⟩
    have hmask_zero : ∀ i, i ∉ S → support_mask S x i = 0 := by
      intro i hi
      simp [support_mask, hi, Set.indicator_of_notMem]
    have hmask_mem :
        support_mask S x ∈ (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) :=
      (mem_sparse_image_iff_exists_card_eq_zero_off_support (ι := ι) (s := s) hs).2
        ⟨S, hScard, hmask_zero⟩
    have hy_le_mask : ‖y - x‖ ≤ ‖support_mask S x - x‖ :=
      (isMinOn_iff.mp hy_min) _ hmask_mem
    have hy_sq :
        ‖y - x‖ ^ (2 : ℕ) ≤ ‖support_mask S x - x‖ ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy_le_mask
    have hdecomp := mask_distance_sq_decomposition S x y hy_zero
    have hy_eq_mask : y = support_mask S x := by
      have hmask_sq : ‖support_mask S x - x‖ ^ (2 : ℕ) = ‖x - support_mask S x‖ ^ (2 : ℕ) := by
        simp [norm_sub_rev]
      have hnorm : ‖y - support_mask S x‖ ^ (2 : ℕ) ≤ 0 := by
        rw [hdecomp, hmask_sq] at hy_sq
        linarith
      have hzero : ‖y - support_mask S x‖ = 0 := by
        nlinarith [sq_nonneg ‖y - support_mask S x‖, hnorm]
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
    have hswap : ∀ i ∈ S, ∀ j, j ∉ S → |x j| ≤ |x i| := by
      intro i hi j hj
      let T : Finset ι := insert j (S.erase i)
      have hTcard : T.card = s := by
        calc
          T.card = (S.erase i).card + 1 := by simp [T, hj]
          _ = S.card := by
                rw [Finset.card_erase_of_mem hi]
                exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨i, hi⟩)
          _ = s := hScard
      have hTzero : ∀ k, k ∉ T → support_mask T x k = 0 := by
        intro k hk
        simp [support_mask, hk]
      have hTmem :
          support_mask T x ∈ (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) :=
        (mem_sparse_image_iff_exists_card_eq_zero_off_support (ι := ι) (s := s) hs).2
          ⟨T, hTcard, hTzero⟩
      have hmask_le_T : ‖support_mask S x - x‖ ≤ ‖support_mask T x - x‖ := by
        simpa [hy_eq_mask] using (isMinOn_iff.mp hy_min) _ hTmem
      have hmask_sq_le_T :
          ‖x - support_mask S x‖ ^ (2 : ℕ) ≤ ‖x - support_mask T x‖ ^ (2 : ℕ) := by
        have hsq :
            ‖support_mask S x - x‖ ^ (2 : ℕ) ≤ ‖support_mask T x - x‖ ^ (2 : ℕ) :=
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmask_le_T
        simpa [norm_sub_rev, T] using hsq
      exact abs_le_of_swapped_residual_sq_le S x hi hj hmask_sq_le_T
    have hsum_ge :
        sum_k_largest_abs s x ≤ S.sum (fun i ↦ |x i|) :=
      sum_k_largest_abs_le_support_sum_of_swap_condition S x hScard hswap
    have hsum_le :
        S.sum (fun i ↦ |x i|) ≤ sum_k_largest_abs s x :=
      sum_abs_le_sum_k_largest_abs_of_card_eq S x hScard
    refine ⟨S, ⟨hScard, le_antisymm hsum_le hsum_ge⟩, ?_⟩
    simpa [support_mask] using hy_eq_mask.symm
  · rintro ⟨S, hS, rfl⟩
    rcases hS with ⟨hScard, hSsum⟩
    have hmask_zero : ∀ i, i ∉ S → support_mask S x i = 0 := by
      intro i hi
      simp [support_mask, hi, Set.indicator_of_notMem]
    have hmask_mem :
        support_mask S x ∈ (toLp 2 '' (C_[s] : Set (ι → ℝ)) : Set E) :=
      (mem_sparse_image_iff_exists_card_eq_zero_off_support (ι := ι) (s := s) hs).2
        ⟨S, hScard, hmask_zero⟩
    have hswap : ∀ i ∈ S, ∀ j, j ∉ S → |x j| ≤ |x i| := by
      intro i hi j hj
      exact abs_le_of_top_sum_swap S x hScard hSsum hi hj
    rw [mem_projection_mapping_iff, isMinOn_iff]
    constructor
    · exact hmask_mem
    · intro z hz
      rcases (mem_sparse_image_iff_exists_card_eq_zero_off_support (ι := ι) (s := s) hs).mp hz with
        ⟨T, hTcard, hz_zero⟩
      have hsumT_sq :
          T.sum (fun i ↦ |x i| ^ (2 : ℕ)) ≤ S.sum (fun i ↦ |x i| ^ (2 : ℕ)) := by
        refine sum_le_of_exchange_property (w := fun i ↦ |x i| ^ (2 : ℕ)) S T
          (hScard.trans hTcard.symm) ?_
        intro i hi j hj
        have hij : |x j| ≤ |x i| := hswap i hi j hj
        exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hij
      have hres_sq :
          ‖x - support_mask S x‖ ^ (2 : ℕ) ≤ ‖x - support_mask T x‖ ^ (2 : ℕ) := by
        rw [mask_residual_sq_total, mask_residual_sq_total]
        linarith
      have hres :
          ‖x - support_mask S x‖ ≤ ‖x - support_mask T x‖ :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hres_sq
      have hdecompT := mask_distance_sq_decomposition T x z hz_zero
      have hmaskT_sq :
          ‖x - support_mask T x‖ ^ (2 : ℕ) ≤ ‖z - x‖ ^ (2 : ℕ) := by
        have hnorm : 0 ≤ ‖z - support_mask T x‖ ^ (2 : ℕ) := sq_nonneg _
        linarith [hdecompT]
      have hmaskT :
          ‖x - support_mask T x‖ ≤ ‖z - x‖ :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hmaskT_sq
      simpa [support_mask, norm_sub_rev] using le_trans hres hmaskT

end
