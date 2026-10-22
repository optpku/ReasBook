/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix

noncomputable section

section

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "𝕊" => selfAdjoint.submodule ℝ (Mₙ)

/-- Helper for Theorem 7.1: the eigenvalue lists of two Hermitian matrices monovary because they
come from the same reindexing of the decreasing `eigenvalues₀` lists. -/
lemma hermitian_eigenvalues_monovary {A B : Mₙ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Monovary hA.eigenvalues hB.eigenvalues := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  -- The sorted `eigenvalues₀` lists are antitone, hence they monovary.
  have hAB : Monovary hA.eigenvalues₀ hB.eigenvalues₀ :=
    hA.eigenvalues₀_antitone.monovary hB.eigenvalues₀_antitone
  -- Reindexing both lists by the same equivalence preserves monovariance.
  simpa [Matrix.IsHermitian.eigenvalues, e] using hAB.comp_right e

/-- Helper for Theorem 7.1: the ordered Hermitian eigenvalue list on `Fin n`, obtained from
mathlib's decreasing `eigenvalues₀` by the canonical `Fin.cast` reindexing. -/
noncomputable def ordered_hermitian_eigenvalues (A : Mₙ) (hA : A.IsHermitian) : Fin n → ℝ :=
  fun i ↦ hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- Helper for Theorem 7.1: the ordered Hermitian eigenvalue list is antitone on `Fin n`. -/
lemma ordered_hermitian_eigenvalues_antitone (A : Mₙ) (hA : A.IsHermitian) :
    Antitone (ordered_hermitian_eigenvalues A hA) := by
  intro i j hij
  -- Rewrite to the canonical ordered spectrum and then reuse mathlib's antitonicity theorem.
  rw [ordered_hermitian_eigenvalues, ordered_hermitian_eigenvalues]
  exact hA.eigenvalues₀_antitone (by simpa using hij)

/-- Helper for Theorem 7.1: the theorem's `eigenvalues` coordinates differ from the ordered
`eigenvalues₀` coordinates by a single fixed permutation of `Fin n`. -/
lemma exists_ordered_hermitian_eigenvalues_reindex_perm :
    ∃ σ : Equiv.Perm (Fin n), ∀ {A : Mₙ} (hA : A.IsHermitian),
      hA.eigenvalues = ordered_hermitian_eigenvalues A hA ∘ σ := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    { toFun := Fin.cast (Fintype.card_fin n).symm
      invFun := Fin.cast (Fintype.card_fin n)
      left_inv := by
        intro i
        simp
      right_inv := by
        intro i
        simp }
  refine ⟨e.trans c.symm, ?_⟩
  intro A hA
  -- Rewrite both coordinate systems to the same `eigenvalues₀` list.
  ext i
  simp [Matrix.IsHermitian.eigenvalues, ordered_hermitian_eigenvalues, e, c, Function.comp_def]

/-- Helper for Theorem 7.1: squaring the entries of an orthogonal matrix produces a doubly
stochastic matrix. -/
lemma orthogonal_entrywise_sq_mem_doubly_stochastic
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (fun i j : Fin n => (Q i j)^2 : Mₙ) ∈ doublyStochastic ℝ (Fin n) := by
  -- The row and column sums are the diagonal entries of `Q Qᵀ` and `Qᵀ Q`.
  exact (mem_doublyStochastic_iff_sum).2 <| by
    constructor
    · intro i j
      positivity
    constructor
    · intro i
      have hQQT : ((Q : Mₙ) * (Q : Mₙ)ᵀ) i i = (1 : Mₙ) i i := by
        simpa using congrFun
          (congrFun ((Matrix.mem_orthogonalGroup_iff (A := (Q : Mₙ)) (R := ℝ)).1 Q.2) i) i
      simpa [Matrix.mul_apply, pow_two] using hQQT
    · intro j
      have hQTQ : (((Q : Mₙ)ᵀ) * (Q : Mₙ)) j j = (1 : Mₙ) j j := by
        simpa using congrFun
          (congrFun ((Matrix.mem_orthogonalGroup_iff' (A := (Q : Mₙ)) (R := ℝ)).1 Q.2) j) j
      simpa [Matrix.mul_apply, pow_two, mul_comm] using hQTQ

/-- Helper for Theorem 7.1: the diagonal entries of an orthogonal conjugate of a diagonal matrix
are weighted by squared entries of the orthogonal matrix. -/
lemma diagonal_conj_entry (y : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    (((Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) = ∑ j, (Q i j)^2 * y j := by
  -- Unfold the diagonal matrix and normalize the finite sum.
  rw [mul_assoc]
  simp [Matrix.diagonal, Matrix.mul_apply]
  ring_nf

/-- Helper for Theorem 7.1: after diagonalizing both matrices, the trace pairing becomes the dot
product against the doubly stochastic matrix of squared orthogonal entries. -/
lemma orthogonal_trace_reduction (x y : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    trace (diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) =
      dotProduct x ((fun i j : Fin n => (Q i j)^2 : Mₙ) *ᵥ y) := by
  calc
    trace (diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ))
      = ∑ i, x i * ∑ j, (Q i j)^2 * y j := by
          rw [Matrix.trace]
          apply Finset.sum_congr rfl
          intro i hi
          change ((diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) = _
          -- The left diagonal factor contributes the scalar `x i`.
          have hmul : ((diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)).diag i) =
              x i * (((Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) := by
            rw [show (diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)).diag i
                = ((diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) by rfl]
            rw [mul_assoc]
            simp [Matrix.diagonal, Matrix.mul_apply]
            ring_nf
            simpa [mul_assoc] using
              (Finset.mul_sum Finset.univ (fun j : Fin n => (Q i j)^2 * y j) (x i)).symm
          have hmul' : ((diagonal x * (Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) =
              x i * (((Q : Mₙ) * diagonal y * ((Q : Mₙ)ᵀ)) i i) := by
            simpa [Matrix.diag] using hmul
          rw [hmul', diagonal_conj_entry y Q i]
    _ = dotProduct x ((fun i j : Fin n => (Q i j)^2 : Mₙ) *ᵥ y) := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 7.1: a doubly stochastic matrix does not increase the dot product of two
monovarying real vectors. -/
lemma doubly_stochastic_dotProduct_le_of_monovary (x y : Fin n → ℝ) (P : Mₙ)
    (hxy : Monovary x y) (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    dotProduct x (P *ᵥ y) ≤ dotProduct x y := by
  obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  calc
    dotProduct x (P *ᵥ y)
      = dotProduct x (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ y) := by
          rw [hwP]
    _ = dotProduct x (∑ σ, w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ y)) := by
          rw [sum_mulVec]
          congr
          ext σ
          rw [smul_mulVec]
    _ = ∑ σ, dotProduct x (w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ y)) := by
          rw [dotProduct_sum]
    _ = ∑ σ, w σ * ∑ i, x i * y (σ i) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [dotProduct_smul]
          simp [Matrix.permMatrix_mulVec, dotProduct]
    _ ≤ ∑ σ, w σ * dotProduct x y := by
          apply Finset.sum_le_sum
          intro σ hσ
          exact mul_le_mul_of_nonneg_left (hxy.sum_mul_comp_perm_le_sum_mul) (hw_nonneg σ)
    _ = (∑ σ, w σ) * dotProduct x y := by
          simp [Finset.sum_mul]
    _ = dotProduct x y := by
          rw [hw_sum, one_mul]

/-- Helper for Theorem 7.1: equality in the Birkhoff expansion forces each permutation with
positive weight to be an equality case of the rearrangement inequality. -/
lemma fan_equality_implies_positive_weight_perm_monovary (x y : Fin n → ℝ)
    (w : Equiv.Perm (Fin n) → ℝ) (hw_nonneg : ∀ σ, 0 ≤ w σ) (hw_sum : ∑ σ, w σ = 1)
    (hxy : Monovary x y)
    (hEq : dotProduct x (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ y) = dotProduct x y) :
    ∀ σ, 0 < w σ → Monovary x (y ∘ σ) := by
  intro σ hσ
  by_contra hσ_mono
  have hsum :
      dotProduct x (((∑ τ, w τ • τ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ y) =
        ∑ τ, w τ * ∑ i, x i * y (τ i) := by
    -- Expand the Birkhoff combination into the weighted sum of permutation pairings.
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [smul_mulVec, dotProduct_smul]
    simp [Matrix.permMatrix_mulVec, dotProduct]
  have hweighted :
      ∑ τ, w τ * ∑ i, x i * y (τ i) = ∑ τ, w τ * dotProduct x y := by
    -- Rewrite the equality hypothesis so both sides are expressed with the same convex weights.
    calc
      ∑ τ, w τ * ∑ i, x i * y (τ i)
        = dotProduct x (((∑ τ, w τ • τ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ y) := by
            simp [hsum]
      _ = dotProduct x y := hEq
      _ = (∑ τ, w τ) * dotProduct x y := by rw [hw_sum, one_mul]
      _ = ∑ τ, w τ * dotProduct x y := by rw [Finset.sum_mul]
  have hle :
      ∀ τ, w τ * ∑ i, x i * y (τ i) ≤ w τ * dotProduct x y := by
    intro τ
    -- Each weighted permutation term is bounded by the rearrangement inequality.
    simpa [dotProduct] using
      mul_le_mul_of_nonneg_left (hxy.sum_mul_comp_perm_le_sum_mul (σ := τ)) (hw_nonneg τ)
  have hltσ_sum : ∑ i, x i * y (σ i) < dotProduct x y := by
    -- A positive-weight permutation that is not a monovary equality case would be strictly worse.
    simpa [dotProduct] using (hxy.sum_mul_comp_perm_lt_sum_mul_iff (σ := σ)).2 hσ_mono
  have hltσ :
      w σ * ∑ i, x i * y (σ i) < w σ * dotProduct x y := by
    exact mul_lt_mul_of_pos_left hltσ_sum hσ
  have hsum_lt :
      ∑ τ, w τ * ∑ i, x i * y (τ i) < ∑ τ, w τ * dotProduct x y := by
    -- One strict deficit at positive weight makes the whole convex combination strictly smaller.
    refine Finset.sum_lt_sum (fun τ hτ ↦ hle τ) ?_
    exact ⟨σ, Finset.mem_univ σ, hltσ⟩
  rw [hweighted] at hsum_lt
  exact (lt_irrefl _ hsum_lt).elim

/-- Helper for Theorem 7.1: if a permutation preserves equality in the rearrangement step, then
every strict spectral cut of `y` is sent to an upward-closed set for the `x`-order. -/
lemma positive_weight_perm_preserves_strict_y_cuts
    {x y : Fin n → ℝ} (hy : Antitone y) {σ : Equiv.Perm (Fin n)}
    (hmono : Monovary x (y ∘ σ)) (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgap : y m > y ⟨m.1 + 1, hm⟩) {i j : Fin n}
    (hi : σ i ≤ m) (hj : ⟨m.1 + 1, hm⟩ ≤ σ j) :
    x i ≥ x j := by
  -- A strict `y`-gap forces the top-cut images to carry larger `y`-values than the bottom ones.
  have hyi_ge : y (σ i) ≥ y m := hy hi
  have hyj_le : y (σ j) ≤ y ⟨m.1 + 1, hm⟩ := hy hj
  have hyij_lt : y (σ j) < y (σ i) := by
    exact lt_of_le_of_lt hyj_le (lt_of_lt_of_le hgap hyi_ge)
  -- Monovariance then transfers that strict `y`-ordering back to the corresponding `x`-ordering.
  exact hmono (i := j) (j := i) hyij_lt

/-- Helper for Theorem 7.1: for a strict `y`-cut, the corresponding prefix-indicator along a
permutation is itself monovary with `x`. -/
lemma strict_y_cut_indicator_monovary
    {x y : Fin n → ℝ} (hy : Antitone y) {σ : Equiv.Perm (Fin n)}
    (hmono : Monovary x (y ∘ σ)) (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgap : y m > y ⟨m.1 + 1, hm⟩) :
    Monovary x (fun i => if σ i ≤ m then (1 : ℝ) else 0) := by
  intro i j hij
  -- A strict increase of the indicator means that `j` lands in the prefix cut while `i` does not.
  have htop : σ j ≤ m := by
    by_contra hj
    by_cases hi : σ i ≤ m
    · simp [hi, hj] at hij
      norm_num at hij
    · simp [hi, hj] at hij
  have hbottom : ¬ σ i ≤ m := by
    by_contra hi
    simp [hi, htop] at hij
  have hsucc : ⟨m.1 + 1, hm⟩ ≤ σ i := by
    exact Nat.succ_le_of_lt (lt_of_not_ge hbottom)
  -- Apply the cut-order lemma with the top-cut row first and the bottom-cut row second.
  exact positive_weight_perm_preserves_strict_y_cuts hy hmono m hm hgap htop hsucc

/-- Helper for Theorem 7.1: if a permutation preserves equality at a strict `y`-cut, then the
corresponding `0/1` prefix indicator has the same pairing with `x` as the unpermuted indicator. -/
lemma strict_y_cut_indicator_dotProduct_eq
    {x y : Fin n → ℝ} (hy : Antitone y) (hxy : Monovary x y) {σ : Equiv.Perm (Fin n)}
    (hmono : Monovary x (y ∘ σ)) (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgap : y m > y ⟨m.1 + 1, hm⟩) :
    ∑ i, x i * (if σ i ≤ m then (1 : ℝ) else 0) =
      dotProduct x (fun i => if i ≤ m then (1 : ℝ) else 0) := by
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  -- First show that the unpermuted prefix indicator is itself a rearrangement equality case.
  have hxe : Monovary x e := by
    simpa [e, Function.comp_apply] using
      (strict_y_cut_indicator_monovary (σ := Equiv.refl (Fin n)) hy hxy m hm hgap)
  -- Then transport the same strict-cut argument through the permutation `σ`.
  have hxeσ : Monovary x (e ∘ σ) := by
    simpa [e, Function.comp_apply] using
      (strict_y_cut_indicator_monovary (σ := σ) hy hmono m hm hgap)
  -- Equality in the rearrangement inequality for the binary indicator gives the desired sum.
  have hEq :
      ∑ i, x i * e (σ i) = ∑ i, x i * e i := by
    exact (hxe.sum_mul_comp_perm_eq_sum_mul_iff (σ := σ)).2 hxeσ
  simpa [e, dotProduct] using hEq

/-- Helper for Theorem 7.1: the Birkhoff convex combination preserves equality for every strict
binary prefix indicator coming from a strict spectral gap of `y`. -/
lemma strict_y_cut_prefix_indicator_equality
    {x y : Fin n → ℝ} (w : Equiv.Perm (Fin n) → ℝ) (hw_nonneg : ∀ σ, 0 ≤ w σ)
    (hw_sum : ∑ σ, w σ = 1) (hxy : Monovary x y)
    (hPermMonovary : ∀ σ, 0 < w σ → Monovary x (y ∘ σ))
    (hy : Antitone y) (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgap : y m > y ⟨m.1 + 1, hm⟩) :
    dotProduct x
        (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ
          (fun i => if i ≤ m then (1 : ℝ) else 0)) =
      dotProduct x (fun i => if i ≤ m then (1 : ℝ) else 0) := by
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  -- Expand the convex combination into weighted permutation pairings against the indicator.
  calc
    dotProduct x (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ e)
      = dotProduct x (∑ σ, w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ e)) := by
          rw [sum_mulVec]
          congr
          ext σ
          rw [smul_mulVec]
    _ = ∑ σ, dotProduct x (w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ e)) := by
          rw [dotProduct_sum]
    _ = ∑ σ, w σ * dotProduct x e := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [dotProduct_smul]
          by_cases hwσ : 0 < w σ
          · -- Positive weights inherit the strict-cut equality from the
            -- rearrangement equality case.
            have hEqσ :
                ∑ i, x i * (if σ i ≤ m then (1 : ℝ) else 0) = dotProduct x e := by
              simpa [e] using strict_y_cut_indicator_dotProduct_eq hy hxy
                (hPermMonovary σ hwσ) m hm hgap
            simpa [Matrix.permMatrix_mulVec, dotProduct, e] using congrArg (fun t => w σ * t) hEqσ
          · -- Zero weights contribute nothing to the convex sum.
            have hwσ0 : w σ = 0 := le_antisymm (le_of_not_gt hwσ) (hw_nonneg σ)
            simp [hwσ0]
    _ = (∑ σ, w σ) * dotProduct x e := by
          simp [Finset.sum_mul]
    _ = dotProduct x e := by
          rw [hw_sum, one_mul]

/-- Helper for Theorem 7.1: after conjugating the permutation support by the common reindexing
that identifies the theorem-level `eigenvalues` with the ordered `eigenvalues₀` coordinates,
every positive-weight permutation remains a rearrangement equality case in the ordered basis. -/
lemma fan_equality_implies_positive_weight_perm_monovary_ordered
    {X Y : Mₙ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (w : Equiv.Perm (Fin n) → ℝ) (σ₀ : Equiv.Perm (Fin n))
    (hX_reindex : hX.eigenvalues = ordered_hermitian_eigenvalues X hX ∘ σ₀)
    (hY_reindex : hY.eigenvalues = ordered_hermitian_eigenvalues Y hY ∘ σ₀)
    (hPermMonovary : ∀ σ, 0 < w σ → Monovary hX.eigenvalues (hY.eigenvalues ∘ σ)) :
    ∀ π, 0 < w (σ₀.symm.permCongr π) →
      Monovary (ordered_hermitian_eigenvalues X hX) (ordered_hermitian_eigenvalues Y hY ∘ π) := by
  intro π hπ
  let xOrd := ordered_hermitian_eigenvalues X hX
  let yOrd := ordered_hermitian_eigenvalues Y hY
  have hraw : Monovary hX.eigenvalues (hY.eigenvalues ∘ (σ₀.symm.permCongr π)) :=
    hPermMonovary (σ₀.symm.permCongr π) hπ
  have hraw' : Monovary (xOrd ∘ σ₀) ((yOrd ∘ σ₀) ∘ (σ₀.symm.permCongr π)) := by
    -- Rewrite the theorem-level eigenvalue coordinates into the ordered coordinates.
    simpa [xOrd, yOrd, hX_reindex, hY_reindex, Function.comp_assoc] using hraw
  -- Reindex the inequality witnesses pointwise by `σ₀.symm` to land in the ordered coordinates.
  intro i j hij
  have hij' :
      ((yOrd ∘ σ₀) ∘ (σ₀.symm.permCongr π)) (σ₀.symm i) <
        ((yOrd ∘ σ₀) ∘ (σ₀.symm.permCongr π)) (σ₀.symm j) := by
    simpa [Function.comp_assoc] using hij
  have hle := hraw' hij'
  simpa [Function.comp_assoc] using hle

/-- Helper for Theorem 7.1: the initial segment `{i | i ≤ r}` in `Fin n` has cardinal `r + 1`. -/
lemma fin_prefix_card (r : Fin n) :
    (Finset.univ.filter fun i : Fin n => i ≤ r).card = r.1 + 1 := by
  have h := Fin.card_filter_val_lt (n := n) (m := r.1 + 1)
  have h' : (Finset.univ.filter fun i : Fin n => i ≤ r).card = min n (r.1 + 1) := by
    simpa only [Fin.le_iff_val_le_val, Nat.lt_succ_iff] using h
  have hr : r.1 + 1 ≤ n := Nat.succ_le_of_lt r.2
  omega

/-- Helper for Theorem 7.1: a permutation sends exactly `m + 1` indices into the first
`m + 1` positions. -/
lemma perm_prefix_preimage_card (π : Equiv.Perm (Fin n)) (m : Fin n) :
    (Finset.univ.filter fun i : Fin n => π i ≤ m).card = m.1 + 1 := by
  classical
  have hs :
      (Finset.univ.filter fun i : Fin n => π i ≤ m) =
        (Finset.univ.filter fun j : Fin n => j ≤ m).map π.symm.toEmbedding := by
    ext i
    simp
  rw [hs, Finset.card_map, fin_prefix_card]

/-- Helper for Theorem 7.1: a strict gap in an antitone sequence separates all indices across the
corresponding cut. -/
lemma antitone_strict_cut_separates
    {x : Fin n → ℝ} (hx : Antitone x)
    (r : Fin n) (hr : (r : ℕ) + 1 < n)
    (hgap : x r > x ⟨r.1 + 1, hr⟩) {i j : Fin n}
    (hi : i ≤ r) (hj : r < j) :
    x i > x j := by
  -- Compare `i` and `j` to the two sides of the strict gap at `r`.
  have hxi : x i ≥ x r := by
    simpa using hx hi
  have hsucc_le : (⟨r.1 + 1, hr⟩ : Fin n) ≤ j := by
    exact Nat.succ_le_of_lt hj
  have hxj : x ⟨r.1 + 1, hr⟩ ≥ x j := hx hsucc_le
  calc
    x i ≥ x r := hxi
    _ > x ⟨r.1 + 1, hr⟩ := hgap
    _ ≥ x j := hxj

/-- Helper for Theorem 7.1: a positive-weight permutation in the ordered equality case can only
cross a strict `x`/`y` cut in the direction allowed by the counting argument. -/
lemma ordered_positive_weight_perm_cut_support
    {x y : Fin n → ℝ} (hx : Antitone x) (hy : Antitone y)
    {π : Equiv.Perm (Fin n)} (hmono : Monovary x (y ∘ π))
    (m : Fin n) (hm : (m : ℕ) + 1 < n) (hgap_y : y m > y ⟨m.1 + 1, hm⟩)
    (r : Fin n) (hr : (r : ℕ) + 1 < n) (hgap_x : x r > x ⟨r.1 + 1, hr⟩) :
    ((m ≤ r → ∀ ⦃i : Fin n⦄, r < i → ¬ π i ≤ m) ∧
      (r < m → ∀ ⦃i : Fin n⦄, i ≤ r → ¬ m < π i)) := by
  constructor
  · intro hmr i hi hiprefix
    by_cases hcross : ∃ j : Fin n, j ≤ r ∧ m < π j
    · rcases hcross with ⟨j, hj, hjπ⟩
      -- A crossing from below to the `y`-prefix forces the opposite-side row to have larger
      -- `x`, contradicting the strict `x`-gap at `r`.
      have hmono_cut :
          x i ≥ x j := by
        have hsucc : (⟨m.1 + 1, hm⟩ : Fin n) ≤ π j := Nat.succ_le_of_lt hjπ
        exact positive_weight_perm_preserves_strict_y_cuts hy hmono m hm hgap_y hiprefix hsucc
      have hsep : x j > x i := antitone_strict_cut_separates hx r hr hgap_x hj hi
      exact not_le_of_gt hsep hmono_cut
    · -- If no top row exits the `y`-prefix, then the lower crossing row makes the prefix preimage
      -- strictly larger than allowed by cardinality.
      have hsub :
          Finset.univ.filter (fun j : Fin n => j ≤ r) ⊆
            Finset.univ.filter (fun j : Fin n => π j ≤ m) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_contra hjπ
        exact hcross ⟨j, hj, lt_of_not_ge hjπ⟩
      have hstrict :
          Finset.univ.filter (fun j : Fin n => j ≤ r) ⊂
            Finset.univ.filter (fun j : Fin n => π j ≤ m) := by
        refine ⟨hsub, ?_⟩
        intro hts
        have hi_mem :
            i ∈ Finset.univ.filter (fun j : Fin n => π j ≤ m) := by
          simp [hiprefix]
        have : i ∈ Finset.univ.filter (fun j : Fin n => j ≤ r) := hts hi_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact (not_le_of_gt hi) this
      have hcard_lt := Finset.card_lt_card hstrict
      rw [fin_prefix_card, perm_prefix_preimage_card] at hcard_lt
      omega
  · intro hrm i hi hsuffix
    have hcross : ∃ j : Fin n, r < j ∧ π j ≤ m := by
      by_contra hcross
      -- Otherwise every preimage of the `y`-prefix would lie above the strict `x`-cut, but there
      -- are too many such preimages when `r < m`.
      have hsub :
          Finset.univ.filter (fun j : Fin n => π j ≤ m) ⊆
            Finset.univ.filter (fun j : Fin n => j ≤ r) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        have : ¬ r < j := by
          intro hrj
          exact hcross ⟨j, hrj, hj⟩
        exact le_of_not_gt this
      have hcard_le := Finset.card_le_card hsub
      rw [perm_prefix_preimage_card, fin_prefix_card] at hcard_le
      omega
    rcases hcross with ⟨j, hj, hjπ⟩
    -- A crossing from the `x`-prefix to the `y`-suffix is incompatible with the forced lower row
    -- landing back in the `y`-prefix.
    have hmono_cut :
        x j ≥ x i := by
      have hsucc : (⟨m.1 + 1, hm⟩ : Fin n) ≤ π i := Nat.succ_le_of_lt hsuffix
      exact positive_weight_perm_preserves_strict_y_cuts hy hmono m hm hgap_y hjπ hsucc
    have hsep : x i > x j := antitone_strict_cut_separates hx r hr hgap_x hi hj
    exact not_le_of_gt hsep hmono_cut

/-- Helper for Theorem 7.1: summing the positive-weight cut-support restrictions over the ordered
Birkhoff decomposition yields the one-sided zero pattern needed for the equality case. -/
lemma ordered_strict_cut_birkhoff_zero_pattern
    {x y : Fin n → ℝ} (hx : Antitone x) (hy : Antitone y)
    (w : Equiv.Perm (Fin n) → ℝ) (hw_nonneg : ∀ π, 0 ≤ w π)
    (hPermMonovary : ∀ π, 0 < w π → Monovary x (y ∘ π))
    (m : Fin n) (hm : (m : ℕ) + 1 < n) (hgap_y : y m > y ⟨m.1 + 1, hm⟩)
    (r : Fin n) (hr : (r : ℕ) + 1 < n) (hgap_x : x r > x ⟨r.1 + 1, hr⟩) :
    ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
        (((∑ π, w π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
      (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
        (((∑ π, w π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)) := by
  constructor
  · intro hmr i j hi hj
    -- Each permutation term vanishes because a positive weight cannot send the lower row `i`
    -- into the `y`-prefix, and a zero weight contributes nothing.
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro π hπ
    by_cases hwπ : 0 < w π
    · have hno :
          ¬ π i ≤ m :=
        (ordered_positive_weight_perm_cut_support hx hy (hPermMonovary π hwπ)
          m hm hgap_y r hr hgap_x).1 hmr hi
      by_cases hEq : π i = j
      · exfalso
        exact hno (by simpa [hEq] using hj)
      · simp [Matrix.smul_apply, Equiv.Perm.permMatrix, hEq]
    · have hwπ0 : w π = 0 := le_antisymm (le_of_not_gt hwπ) (hw_nonneg π)
      simp [Matrix.smul_apply, hwπ0]
  · intro hrm i j hi hj
    -- The symmetric argument uses the upper-right forbidden rectangle from the split support
    -- statement.
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro π hπ
    by_cases hwπ : 0 < w π
    · have hno :
          ¬ m < π i :=
        (ordered_positive_weight_perm_cut_support hx hy (hPermMonovary π hwπ)
          m hm hgap_y r hr hgap_x).2 hrm hi
      by_cases hEq : π i = j
      · exfalso
        exact hno (by simpa [hEq] using hj)
      · simp [Matrix.smul_apply, Equiv.Perm.permMatrix, hEq]
    · have hwπ0 : w π = 0 := le_antisymm (le_of_not_gt hwπ) (hw_nonneg π)
      simp [Matrix.smul_apply, hwπ0]

/-- Helper for Theorem 7.1: after transporting both eigenbases by the common reindexing
permutation, the ordered Birkhoff matrix is exactly the orthostochastic matrix of the ordered
relative orthogonal matrix. -/
lemma ordered_birkhoff_matrix_eq_orthostochastic_conjugate
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (w : Equiv.Perm (Fin n) → ℝ) (σ₀ : Equiv.Perm (Fin n))
    (hwP : ((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) = fun i j : Fin n => (Q i j)^2) :
    let wOrd : Equiv.Perm (Fin n) → ℝ := fun π ↦ w (σ₀.symm.permCongr π)
    let QOrd : Mₙ := fun i j ↦ Q (σ₀.symm i) (σ₀.symm j)
    ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j)^2 := by
  dsimp
  ext i j
  -- Reindex the Birkhoff sum by conjugation so the ordered coordinates become explicit.
  calc
    ((∑ π, w (σ₀.symm.permCongr π) • π.permMatrix ℝ : Mₙ) i j)
      = ∑ π, w (σ₀.symm.permCongr π) * ((π.permMatrix ℝ) i j) := by
          simp [Matrix.sum_apply]
    _ = ∑ τ, w τ * (((σ₀.permCongr τ).permMatrix ℝ) i j) := by
          refine Fintype.sum_equiv σ₀.symm.permCongr
            (fun π : Equiv.Perm (Fin n) ↦
              w (σ₀.symm.permCongr π) * ((π.permMatrix ℝ) i j))
            (fun τ : Equiv.Perm (Fin n) ↦
              w τ * (((σ₀.permCongr τ).permMatrix ℝ) i j)) ?_
          intro π
          simp
    _ = ∑ τ, w τ * ((τ.permMatrix ℝ) (σ₀.symm i) (σ₀.symm j)) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          have hentry :
              ((σ₀.permCongr τ) i = j) ↔ τ (σ₀.symm i) = σ₀.symm j := by
            constructor
            · intro hij
              apply σ₀.injective
              simpa using hij
            · intro hij
              simpa using congrArg σ₀ hij
          by_cases h : τ (σ₀.symm i) = σ₀.symm j
          · have hij : (σ₀.permCongr τ) i = j := hentry.mpr h
            simp [Equiv.Perm.permMatrix, h]
          · have hij : (σ₀.permCongr τ) i ≠ j := by
              intro hij
              exact h (hentry.mp hij)
            have hneq : σ₀ (τ (σ₀.symm i)) ≠ j := by
              intro hEq
              apply h
              apply σ₀.injective
              simpa using hEq
            simp [Equiv.Perm.permMatrix, h, hneq]
    _ = ((∑ τ, w τ • τ.permMatrix ℝ : Mₙ) (σ₀.symm i) (σ₀.symm j)) := by
          simp [Matrix.sum_apply]
    _ = (Q (σ₀.symm i) (σ₀.symm j))^2 := by
          simpa using congrFun (congrFun hwP (σ₀.symm i)) (σ₀.symm j)

/-- Helper for Theorem 7.1: reindexing the relative orthogonal matrix by the common permutation
preserves the left orthogonality relation `QOrd QOrdᵀ = 1`. -/
lemma ordered_relative_orthogonal_left
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (σ₀ : Equiv.Perm (Fin n)) :
    let QOrd : Mₙ := Matrix.reindex σ₀ σ₀ (Q : Mₙ)
    QOrd * QOrdᵀ = 1 := by
  dsimp
  -- Reindex the already-known identity `Q Qᵀ = 1` into the ordered coordinates.
  calc
    Matrix.reindex σ₀ σ₀ (Q : Mₙ) * (Matrix.reindex σ₀ σ₀ (Q : Mₙ))ᵀ
        = Matrix.reindex σ₀ σ₀ ((Q : Mₙ) * (Q : Mₙ)ᵀ) := by
            rw [show (Matrix.reindex σ₀ σ₀ (Q : Mₙ))ᵀ =
                Matrix.reindex σ₀ σ₀ ((Q : Mₙ)ᵀ) by
                  simp [Matrix.transpose_submatrix]]
            symm
            simpa using
              (Matrix.reindexLinearEquiv_mul ℝ ℝ σ₀ σ₀ σ₀ (Q : Mₙ) ((Q : Mₙ)ᵀ))
    _ = Matrix.reindex σ₀ σ₀ (1 : Mₙ) := by
          rw [show (Q : Mₙ) * (Q : Mₙ)ᵀ = (1 : Mₙ) by
            exact (Matrix.mem_orthogonalGroup_iff (A := (Q : Mₙ)) (R := ℝ)).1 Q.2]
    _ = 1 := by
          simp

/-- Helper for Theorem 7.1: reindexing the relative orthogonal matrix by the common permutation
preserves the right orthogonality relation `QOrdᵀ QOrd = 1`. -/
lemma ordered_relative_orthogonal_right
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (σ₀ : Equiv.Perm (Fin n)) :
    let QOrd : Mₙ := Matrix.reindex σ₀ σ₀ (Q : Mₙ)
    QOrdᵀ * QOrd = 1 := by
  dsimp
  -- Reindex the companion identity `Qᵀ Q = 1` into the same ordered basis.
  calc
    (Matrix.reindex σ₀ σ₀ (Q : Mₙ))ᵀ * Matrix.reindex σ₀ σ₀ (Q : Mₙ)
        = Matrix.reindex σ₀ σ₀ (((Q : Mₙ)ᵀ) * (Q : Mₙ)) := by
            rw [show (Matrix.reindex σ₀ σ₀ (Q : Mₙ))ᵀ =
                Matrix.reindex σ₀ σ₀ ((Q : Mₙ)ᵀ) by
                  simp [Matrix.transpose_submatrix]]
            symm
            simpa using
              (Matrix.reindexLinearEquiv_mul ℝ ℝ σ₀ σ₀ σ₀ ((Q : Mₙ)ᵀ) (Q : Mₙ))
    _ = Matrix.reindex σ₀ σ₀ (1 : Mₙ) := by
          rw [show ((Q : Mₙ)ᵀ) * (Q : Mₙ) = (1 : Mₙ) by
            exact (Matrix.mem_orthogonalGroup_iff' (A := (Q : Mₙ)) (R := ℝ)).1 Q.2]
    _ = 1 := by
          simp

/-- Helper for Theorem 7.1: the ordered orthostochastic identity upgrades a zero entry of the
transported Birkhoff matrix into an actual zero entry of the ordered relative orthogonal matrix. -/
lemma ordered_orthostochastic_entry_eq_zero_of_zero_pattern
    (wOrd : Equiv.Perm (Fin n) → ℝ) (QOrd : Mₙ)
    (hPOrd : ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2)
    {i j : Fin n}
    (hzero : (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) :
    QOrd i j = 0 := by
  -- Over `ℝ`, a squared matrix entry vanishes exactly when the entry itself vanishes.
  have hsquare : (QOrd i j) ^ 2 = 0 := by
    simpa [hPOrd] using hzero
  exact sq_eq_zero_iff.mp hsquare

/-- Helper for Theorem 7.1: distinct ordered rows of the reindexed relative orthogonal matrix are
orthogonal, so their entrywise inner product is zero. -/
lemma ordered_relative_row_inner_eq_zero
    (QOrd : Mₙ) (hQOrd_left : QOrd * QOrdᵀ = 1) {i j : Fin n} (hij : i ≠ j) :
    ∑ k, QOrd i k * QOrd j k = 0 := by
  -- Read the `(i,j)` entry of `QOrd QOrdᵀ = 1`.
  have hij_entry : (QOrd * QOrdᵀ) i j = (1 : Mₙ) i j := by
    exact congrFun (congrFun hQOrd_left i) j
  simpa [Matrix.mul_apply, hij] using hij_entry

/-- Helper for Theorem 7.1: a matrix commutes with a real diagonal matrix exactly when its entries
vanish across indices with distinct diagonal values. -/
lemma diagonal_commute_iff_off_block_zero (x : Fin n → ℝ) (A : Mₙ) :
    Commute (diagonal x) A ↔ ∀ i j, x i ≠ x j → A i j = 0 := by
  constructor
  · intro hcomm i j hij
    -- Compare the `(i,j)` entries of the two products to isolate the off-block coefficient.
    have hij_entry : ((diagonal x) * A) i j = (A * diagonal x) i j := by
      exact congrFun (congrFun hcomm.eq i) j
    have hmul : x i * A i j = A i j * x j := by
      simpa [Matrix.mul_apply, Matrix.diagonal] using hij_entry
    have hsub : (x i - x j) * A i j = 0 := by
      linarith
    by_contra hAij
    have hx : x i - x j ≠ 0 := sub_ne_zero.mpr hij
    exact hAij ((mul_eq_zero.mp hsub).resolve_left hx)
  · intro hzero
    -- Entrywise, either the diagonal values agree or the off-block entry is zero.
    ext i j
    by_cases hij : x i = x j
    · simp [Matrix.mul_apply, Matrix.diagonal, hij, mul_comm]
    · have hAij : A i j = 0 := hzero i j hij
      simp [Matrix.mul_apply, Matrix.diagonal, hAij, mul_comm]

/-- Helper for Theorem 7.1: the ordered prefix projector obtained by conjugating a diagonal
`0/1` prefix indicator has the expected entrywise expansion against the rows of `QOrd`. -/
lemma ordered_prefix_projector_entry
    (QOrd : Mₙ) (m i j : Fin n) :
    ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j) =
      ∑ k, (if k ≤ m then (1 : ℝ) else 0) * QOrd i k * QOrd j k := by
  -- Expand the conjugated diagonal projector entrywise so the prefix weights are explicit.
  simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

/-- Helper for Theorem 7.1: if an antitone ordered list takes different values at `i < j`, then
some adjacent pair strictly drops between `i` and `j`. -/
lemma antitone_distinct_values_have_strict_cut_between
    {x : Fin n → ℝ} (hx : Antitone x) {i j : Fin n} (hij : i < j) (hneq : x i ≠ x j) :
    ∃ r : Fin n, ∃ hr : (r : ℕ) + 1 < n, i ≤ r ∧ r < j ∧ x r > x ⟨r.1 + 1, hr⟩ := by
  -- The antitone ordering turns the endpoint inequality into a strict drop from `i` down to `j`.
  have hij_lt : x i > x j := by
    have hij_le : x j ≤ x i := by simpa using hx (show i ≤ j from le_of_lt hij)
    exact lt_of_le_of_ne hij_le (Ne.symm hneq)
  let P : ℕ → Prop := fun k ↦ ∃ hk : k < j.1, x ⟨k, lt_trans hk j.2⟩ > x j
  have hPi : P i.1 := by
    refine ⟨hij, ?_⟩
    simpa using hij_lt
  let rNat := Nat.findGreatest P j.1
  have hPr : P rNat := Nat.findGreatest_spec (show i.1 ≤ j.1 from Nat.le_of_lt hij) hPi
  have hirNat : i.1 ≤ rNat := Nat.le_findGreatest (show i.1 ≤ j.1 from Nat.le_of_lt hij) hPi
  rcases hPr with ⟨hrNat_lt_j, hPr_val⟩
  have hrNat_lt_n : rNat < n := lt_trans hrNat_lt_j j.2
  have hrNat_succ_lt_n : rNat + 1 < n := by
    omega
  have hnext_le : x ⟨rNat + 1, hrNat_succ_lt_n⟩ ≤ x j := by
    by_cases hnext_eq : rNat + 1 = j.1
    · simpa [hnext_eq]
    · have hnext_lt_j : rNat + 1 < j.1 := by omega
      have hnotP : ¬ P (rNat + 1) :=
        Nat.findGreatest_is_greatest (show rNat < rNat + 1 by omega) (show rNat + 1 ≤ j.1 by omega)
      have hnot_gt : ¬ x ⟨rNat + 1, lt_trans hnext_lt_j j.2⟩ > x j := by
        intro hgt
        exact hnotP ⟨hnext_lt_j, hgt⟩
      exact by
        simpa using le_of_not_gt hnot_gt
  let r : Fin n := ⟨rNat, hrNat_lt_n⟩
  refine ⟨r, hrNat_succ_lt_n, ?_, ?_, ?_⟩
  · simpa [r] using hirNat
  · simpa [r] using hrNat_lt_j
  · have hPr_val' : x r > x j := by
        simpa [r] using hPr_val
    simpa [r] using lt_of_le_of_lt hnext_le hPr_val'

/-- Helper for Theorem 7.1: the ordered prefix projector is symmetric in its row and column
indices. -/
lemma ordered_prefix_projector_entry_symm
    (QOrd : Mₙ) (m i j : Fin n) :
    ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j) =
      ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) j i) := by
  -- The entrywise expansion is unchanged after swapping the two row factors.
  rw [ordered_prefix_projector_entry, ordered_prefix_projector_entry]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Helper for Theorem 7.1: once a strict `xOrd`-cut `r` and a strict `yOrd`-cut `m` are fixed,
the transported Birkhoff zero pattern forces the ordered prefix projector to vanish across the
corresponding off-block rectangles. -/
lemma ordered_zero_pattern_to_prefix_projector_off_block_zero_of_strict_cut
    (wOrd : Equiv.Perm (Fin n) → ℝ) (xOrd yOrd : Fin n → ℝ)
    (hZeroPatternOrd :
      ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
            ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
              (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)))
    (QOrd : Mₙ)
    (hQOrd_left : QOrd * QOrdᵀ = 1)
    (hPOrd : ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2)
    (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩)
    (hgapX : xOrd r > xOrd ⟨r.1 + 1, hr⟩) :
    ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
        ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j) = 0) ∧
      (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → r < j →
        ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j) = 0)) := by
  constructor
  · intro hmr i j hi hj
    -- On the lower-left forbidden rectangle, each prefix summand already vanishes entrywise.
    rw [ordered_prefix_projector_entry]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkm : k ≤ m
    · have hPzero : (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i k) = 0 :=
        (hZeroPatternOrd m r hm hr hgapY hgapX).1 hmr hi hkm
      have hQzero : QOrd i k = 0 :=
        ordered_orthostochastic_entry_eq_zero_of_zero_pattern wOrd QOrd hPOrd hPzero
      simp [hkm, hQzero]
    · simp [hkm]
  · intro hrm i j hi hj
    -- On the upper-right rectangle, the tail entries of row `i` vanish, so the prefix projector
    -- equals the full row inner product, which is zero for distinct orthogonal rows.
    rw [ordered_prefix_projector_entry]
    calc
      ∑ k, (if k ≤ m then (1 : ℝ) else 0) * QOrd i k * QOrd j k
        = ∑ k, QOrd i k * QOrd j k := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkm : k ≤ m
            · simp [hkm]
            · have hmk : m < k := lt_of_not_ge hkm
              have hPzero : (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i k) = 0 :=
                (hZeroPatternOrd m r hm hr hgapY hgapX).2 hrm hi hmk
              have hQzero : QOrd i k = 0 :=
                ordered_orthostochastic_entry_eq_zero_of_zero_pattern wOrd QOrd hPOrd hPzero
              simp [hkm, hQzero]
      _ = 0 := by
            have hij : i ≠ j := by
              intro hijEq
              subst hijEq
              exact not_lt_of_ge hi hj
            exact ordered_relative_row_inner_eq_zero QOrd hQOrd_left hij

/-- Helper for Theorem 7.1: fixing a strict `yOrd`-cut upgrades the transported Birkhoff support
to full off-block vanishing for the corresponding ordered prefix projector across distinct
`xOrd`-levels. -/
lemma ordered_zero_pattern_to_prefix_projector_off_block_zero
    (wOrd : Equiv.Perm (Fin n) → ℝ) (xOrd yOrd : Fin n → ℝ)
    (hxOrd : Antitone xOrd)
    (hZeroPatternOrd :
      ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
            ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
              (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)))
    (QOrd : Mₙ)
    (hQOrd_left : QOrd * QOrdᵀ = 1)
    (hPOrd : ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2)
    (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩) :
    ∀ i j, xOrd i ≠ xOrd j →
      ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j) = 0 := by
  intro i j hij
  by_cases hij_lt : i < j
  · obtain ⟨r, hr, hir, hrj, hgapX⟩ :=
      antitone_distinct_values_have_strict_cut_between hxOrd hij_lt hij
    by_cases hrm : r < m
    · -- When the strict `xOrd`-cut lies before `m`, the existing projector rectangle already
      -- contains the off-block entry `(i,j)`.
      exact (ordered_zero_pattern_to_prefix_projector_off_block_zero_of_strict_cut
        wOrd xOrd yOrd hZeroPatternOrd QOrd hQOrd_left hPOrd m r hm hr hgapY hgapX).2 hrm
          hir hrj
    · have hmr : m ≤ r := le_of_not_gt hrm
      -- When `m ≤ r`, every prefix column of row `j` already vanishes in the orthostochastic
      -- matrix, so the full projector entry `(i,j)` is zero termwise.
      rw [ordered_prefix_projector_entry]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hkm : k ≤ m
      · have hPzero :
            (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) j k) = 0 :=
          (hZeroPatternOrd m r hm hr hgapY hgapX).1 hmr hrj hkm
        have hQzero : QOrd j k = 0 :=
          ordered_orthostochastic_entry_eq_zero_of_zero_pattern wOrd QOrd hPOrd hPzero
        simp [hkm, hQzero]
      · simp [hkm]
  · have hne_ij : i ≠ j := by
        intro hEq
        apply hij
        simpa [hEq]
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij_lt) (Ne.symm hne_ij)
    obtain ⟨r, hr, hjr, hri, hgapX⟩ :=
      antitone_distinct_values_have_strict_cut_between hxOrd hji hij.symm
    by_cases hrm : r < m
    · have hzero_ji :
          ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) j i) = 0 :=
        (ordered_zero_pattern_to_prefix_projector_off_block_zero_of_strict_cut
          wOrd xOrd yOrd hZeroPatternOrd QOrd hQOrd_left hPOrd m r hm hr hgapY hgapX).2
            hrm hjr hri
      simpa [ordered_prefix_projector_entry_symm QOrd m j i] using hzero_ji
    · have hmr : m ≤ r := le_of_not_gt hrm
      -- In the complementary case, the prefix columns of row `i` vanish termwise.
      rw [ordered_prefix_projector_entry]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hkm : k ≤ m
      · have hPzero :
            (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i k) = 0 :=
          (hZeroPatternOrd m r hm hr hgapY hgapX).1 hmr hri hkm
        have hQzero : QOrd i k = 0 :=
          ordered_orthostochastic_entry_eq_zero_of_zero_pattern wOrd QOrd hPOrd hPzero
        simp [hkm, hQzero]
      · simp [hkm]

/-- Helper for Theorem 7.1: every strict `yOrd` prefix projector commutes with `diagonal xOrd`
once the ordered equality support has been upgraded to full off-block vanishing. -/
lemma ordered_prefix_projector_commutes_with_diagonal
    (wOrd : Equiv.Perm (Fin n) → ℝ) (xOrd yOrd : Fin n → ℝ)
    (hxOrd : Antitone xOrd)
    (hZeroPatternOrd :
      ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
            ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
              (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)))
    (QOrd : Mₙ)
    (hQOrd_left : QOrd * QOrdᵀ = 1)
    (hPOrd : ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2)
    (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩) :
    Commute (diagonal xOrd)
      (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) := by
  -- Package the entrywise off-block vanishing into the clean commutation interface.
  refine (diagonal_commute_iff_off_block_zero xOrd
    (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ)).2 ?_
  intro i j hij
  exact ordered_zero_pattern_to_prefix_projector_off_block_zero
    wOrd xOrd yOrd hxOrd hZeroPatternOrd QOrd hQOrd_left hPOrd m hm hgapY i j hij

/-- Helper for Theorem 7.1: the strict-prefix equality data rewrites the trace pairing against an
ordered prefix projector as the expected ordered prefix sum of `xOrd`. -/
lemma ordered_prefix_projector_trace_eq_prefix_sum
    (wOrd : Equiv.Perm (Fin n) → ℝ) (xOrd yOrd : Fin n → ℝ)
    (QOrd : Mₙ)
    (hPOrd : ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2)
    (hIndicatorEqOrd :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          dotProduct xOrd
              (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ
                (fun i => if i ≤ m then (1 : ℝ) else 0)) =
            dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0))
    (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩) :
    trace (diagonal xOrd *
        (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ)) =
      dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0) := by
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  -- Expand the trace against the projector entrywise so the orthostochastic weights become
  -- visible and can be rewritten by the transported Birkhoff identity.
  calc
    trace (diagonal xOrd * (QOrd * diagonal e * QOrdᵀ))
      = ∑ i, xOrd i * ∑ k, e k * (QOrd i k) ^ 2 := by
          rw [Matrix.trace]
          apply Finset.sum_congr rfl
          intro i hi
          have hentry :
              ((QOrd * diagonal e * QOrdᵀ) i i) = ∑ k, e k * (QOrd i k) ^ 2 := by
            rw [ordered_prefix_projector_entry]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          have hmul :
              ((diagonal xOrd * (QOrd * diagonal e * QOrdᵀ)) i i) =
                xOrd i * ((QOrd * diagonal e * QOrdᵀ) i i) := by
            simp [Matrix.mul_apply, Matrix.diagonal]
          rw [show (diagonal xOrd * (QOrd * diagonal e * QOrdᵀ)).diag i =
              ((diagonal xOrd * (QOrd * diagonal e * QOrdᵀ)) i i) by rfl,
            hmul, hentry]
    _ = dotProduct xOrd (((fun i j : Fin n => (QOrd i j) ^ 2 : Mₙ) *ᵥ e)) := by
          simp [Matrix.mulVec, dotProduct, e, mul_assoc, Finset.mul_sum]
    _ = dotProduct xOrd ((((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ e)) := by
          rw [hPOrd]
    _ = dotProduct xOrd e := hIndicatorEqOrd m hm hgapY

/-- Helper for Theorem 7.1: conjugating `diagonal xOrd` by the ordered relative orthogonal matrix
turns the strict-prefix commutation data into genuine commutation with `diagonal yOrd`. -/
lemma ordered_conjugate_commutes_with_ordered_y_diagonal
    (xOrd yOrd : Fin n → ℝ) (QOrd : Mₙ)
    (hyOrd_antitone : Antitone yOrd)
    (hQOrd_right : QOrdᵀ * QOrd = 1)
    (hPrefixCommute :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          Commute (diagonal xOrd)
            (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ)) :
    Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd) := by
  let C : Mₙ := QOrdᵀ * diagonal xOrd * QOrd
  have hdiag : Commute (diagonal yOrd) C :=
    (diagonal_commute_iff_off_block_zero yOrd C).2 <| by
      intro i j hij
      by_cases hij_lt : i < j
      · -- A strict drop of `yOrd` between `i` and `j` is detected by one strict prefix cut.
        obtain ⟨m, hm, him, hmj, hgap⟩ :=
          antitone_distinct_values_have_strict_cut_between hyOrd_antitone hij_lt hij
        let e : Fin n → ℝ := fun k => if k ≤ m then (1 : ℝ) else 0
        have hcommE : Commute C (diagonal e) := by
          -- Conjugate the proven prefix-projector commutation identity back to the ordered basis.
          dsimp [C]
          calc
            (QOrdᵀ * diagonal xOrd * QOrd) * diagonal e
              = QOrdᵀ * (diagonal xOrd * (QOrd * diagonal e * QOrdᵀ)) * QOrd := by
                  simp [Matrix.mul_assoc, hQOrd_right]
            _ = QOrdᵀ * ((QOrd * diagonal e * QOrdᵀ) * diagonal xOrd) * QOrd := by
                  rw [(hPrefixCommute m hm hgap).eq]
            _ = ((QOrdᵀ * QOrd) * diagonal e) * (QOrdᵀ * diagonal xOrd * QOrd) := by
                  simp [Matrix.mul_assoc]
            _ = diagonal e * (QOrdᵀ * diagonal xOrd * QOrd) := by
                  simp [hQOrd_right]
        exact (diagonal_commute_iff_off_block_zero e C).1 hcommE.symm i j (by
          simp [e, him, not_le_of_gt hmj])
      · have hne : i ≠ j := by
          intro hEq
          apply hij
          simp [hEq]
        have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij_lt) (Ne.symm hne)
        -- Swapping the indices reduces the second case to the same strict-cut argument.
        obtain ⟨m, hm, hjm, hmi, hgap⟩ :=
          antitone_distinct_values_have_strict_cut_between hyOrd_antitone hji hij.symm
        let e : Fin n → ℝ := fun k => if k ≤ m then (1 : ℝ) else 0
        have hcommE : Commute C (diagonal e) := by
          -- The same conjugation identity handles the reversed off-block position.
          dsimp [C]
          calc
            (QOrdᵀ * diagonal xOrd * QOrd) * diagonal e
              = QOrdᵀ * (diagonal xOrd * (QOrd * diagonal e * QOrdᵀ)) * QOrd := by
                  simp [Matrix.mul_assoc, hQOrd_right]
            _ = QOrdᵀ * ((QOrd * diagonal e * QOrdᵀ) * diagonal xOrd) * QOrd := by
                  rw [(hPrefixCommute m hm hgap).eq]
            _ = ((QOrdᵀ * QOrd) * diagonal e) * (QOrdᵀ * diagonal xOrd * QOrd) := by
                  simp [Matrix.mul_assoc]
            _ = diagonal e * (QOrdᵀ * diagonal xOrd * QOrd) := by
                  simp [hQOrd_right]
        exact (diagonal_commute_iff_off_block_zero e C).1 hcommE.symm i j (by
          simp [e, hjm, not_le_of_gt hmi])
  exact hdiag.symm

/-- Helper for Theorem 7.1: a symmetric operator that commutes with another operator preserves
each eigenspace of the latter, and its restriction to that eigenspace remains symmetric. -/
lemma symmetric_restrict_eigenspace_of_commute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C D : E →ₗ[ℝ] E} (hC : C.IsSymmetric) (hCD : Commute C D) (μ : ℝ) :
    let hInv : ∀ v ∈ Module.End.eigenspace D μ, C v ∈ Module.End.eigenspace D μ :=
      fun _ hv => Module.End.mapsTo_genEigenspace_of_comm hCD.symm μ 1 hv
    (C.restrict hInv).IsSymmetric := by
  dsimp
  -- Commutation gives eigenspace invariance, so the symmetric operator restricts cleanly.
  exact hC.restrict_invariant (fun v hv =>
    Module.End.mapsTo_genEigenspace_of_comm hCD.symm μ 1 hv)

/-- Helper for Theorem 7.1: commuting matrices induce commuting linear maps on Euclidean space. -/
lemma matrix_toEuclideanLin_commute_of_commute
    (A B : Mₙ) (hAB : Commute A B) :
    Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
  ext v i
  -- Expand both compositions to matrix-vector multiplication and use the matrix commutation.
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hAB.eq]

/-- Helper for Theorem 7.1: a real diagonal matrix acts symmetrically on Euclidean space. -/
lemma diagonal_toEuclideanLin_isSymmetric (y : Fin n → ℝ) :
    (Matrix.toEuclideanLin (diagonal y : Mₙ)).IsSymmetric := by
  apply (Matrix.isSymmetric_toEuclideanLin_iff).2
  -- A real diagonal matrix is Hermitian because its conjugate transpose is itself.
  ext i j
  by_cases h : i = j
  · simp [Matrix.diagonal, Matrix.conjTranspose, h]
  · simp [Matrix.diagonal, Matrix.conjTranspose, h, eq_comm]

/-- Helper for Theorem 7.1: the ordered conjugate `QOrdᵀ * diagonal xOrd * QOrd` acts
symmetrically on Euclidean space. -/
lemma conjugate_diagonal_toEuclideanLin_isSymmetric (xOrd : Fin n → ℝ) (QOrd : Mₙ) :
    (Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)).IsSymmetric := by
  apply (Matrix.isSymmetric_toEuclideanLin_iff).2
  -- The transpose of `QOrdᵀ * diagonal xOrd * QOrd` returns the same matrix.
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Helper for Theorem 7.1: once the ordered conjugate commutes with `diagonal yOrd`, the
restriction of the ordered conjugate to any `yOrd`-eigenspace is a symmetric operator. -/
lemma ordered_y_block_restriction_symmetric
    (xOrd yOrd : Fin n → ℝ) (QOrd : Mₙ)
    (hComm : Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd)) (μ : ℝ) :
    let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
    let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
    let hInv : ∀ v ∈ Module.End.eigenspace D μ, C v ∈ Module.End.eigenspace D μ :=
      fun _ hv => Module.End.mapsTo_genEigenspace_of_comm
        (matrix_toEuclideanLin_commute_of_commute _ _ hComm).symm μ 1 hv
    (C.restrict hInv).IsSymmetric := by
  dsimp
  -- This is the invariant-block bridge needed for the blockwise spectral theorem.
  exact symmetric_restrict_eigenspace_of_commute
    (conjugate_diagonal_toEuclideanLin_isSymmetric xOrd QOrd)
    (matrix_toEuclideanLin_commute_of_commute _ _ hComm) μ

/-- Helper for Theorem 7.1: after commuting the ordered conjugate with `diagonal yOrd`, one can
diagonalize the ordered conjugate separately on each finite-dimensional `yOrd`-eigenspace and
collect those block eigenbases into a simultaneous orthonormal eigenbasis. -/
lemma ordered_y_block_collected_simultaneous_basis
    (xOrd yOrd : Fin n → ℝ) (QOrd : Mₙ)
    (hComm : Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd)) :
    let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
    let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
    ∃ (b : OrthonormalBasis
        ((μ : Module.End.Eigenvalues D) ×
          Fin (Module.finrank ℝ (Module.End.eigenspace D μ)))
        ℝ (EuclideanSpace ℝ (Fin n)))
      (z : ((μ : Module.End.Eigenvalues D) ×
          Fin (Module.finrank ℝ (Module.End.eigenspace D μ))) → ℝ),
      (∀ a, D (b a) = ((a.1 : Module.End.Eigenvalues D) : ℝ) • b a) ∧
      ∀ a, C (b a) = z a • b a := by
  dsimp
  let hD := diagonal_toEuclideanLin_isSymmetric yOrd
  let hInt := hD.direct_sum_isInternal
  let hOrth := hD.orthogonalFamily_eigenspaces'
  let hInv :
      ∀ μ, ∀ v ∈ Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ,
        Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ) v ∈
          Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ :=
    fun μ _ hv =>
      Module.End.mapsTo_genEigenspace_of_comm
        (matrix_toEuclideanLin_commute_of_commute _ _ hComm).symm μ 1 hv
  let Cμ :
      ∀ μ : Module.End.Eigenvalues (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)),
        Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ →ₗ[ℝ]
          Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ :=
    fun μ => (Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)).restrict (hInv μ)
  let hCμ :
      ∀ μ : Module.End.Eigenvalues (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)),
        (Cμ μ).IsSymmetric :=
    fun μ => ordered_y_block_restriction_symmetric xOrd yOrd QOrd hComm μ
  let bμ :
      ∀ μ : Module.End.Eigenvalues (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)),
        OrthonormalBasis
          (Fin (Module.finrank ℝ
            (Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ)))
          ℝ (Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ) :=
    fun μ => (hCμ μ).eigenvectorBasis rfl
  let b := hInt.collectedOrthonormalBasis hOrth bμ
  let z :
      ((μ : Module.End.Eigenvalues (Matrix.toEuclideanLin (diagonal yOrd : Mₙ))) ×
          Fin (Module.finrank ℝ
            (Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) μ))) →
        ℝ :=
    fun a => (hCμ a.1).eigenvalues rfl a.2
  refine ⟨b, z, ?_, ?_⟩
  · intro a
    -- Each collected basis vector still lies in its original `yOrd`-eigenspace.
    have hmem :
        b a ∈ Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) a.1 := by
      simpa [b] using hInt.collectedOrthonormalBasis_mem hOrth bμ a
    simpa using (Module.End.mem_eigenspace_iff.mp hmem)
  · intro a
    -- Inside each `yOrd` block, the chosen basis diagonalizes the restricted ordered conjugate.
    have hb :
        b a =
          (bμ a.1 a.2 :
            Module.End.eigenspace (Matrix.toEuclideanLin (diagonal yOrd : Mₙ)) a.1) := by
      simp [b, DirectSum.IsInternal.collectedOrthonormalBasis]
    have happlySubtype : Cμ a.1 (bμ a.1 a.2) = z a • bμ a.1 a.2 := by
      change Cμ a.1 ((hCμ a.1).eigenvectorBasis rfl a.2) =
          ((hCμ a.1).eigenvalues rfl a.2 : ℝ) • ((hCμ a.1).eigenvectorBasis rfl a.2)
      simpa [bμ, z] using (hCμ a.1).apply_eigenvectorBasis rfl a.2
    simpa [hb, Cμ, z] using congrArg Subtype.val happlySubtype

/-- Helper for Theorem 7.1: commuting the ordered conjugate with `diagonal yOrd` forces every
entry across different `yOrd`-values to vanish. -/
lemma ordered_conjugate_off_block_zero_of_y_distinct
    (xOrd yOrd : Fin n → ℝ) (QOrd : Mₙ)
    (hComm : Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd)) :
    let C : Mₙ := QOrdᵀ * diagonal xOrd * QOrd
    ∀ i j : Fin n, yOrd i ≠ yOrd j → C i j = 0 := by
  intro C i j hij
  -- Turn the matrix commutation statement directly into the entrywise off-block vanishing claim.
  exact (diagonal_commute_iff_off_block_zero yOrd C).1 hComm.symm i j hij

/-- Helper for Theorem 7.1: the sigma-indexed simultaneous eigenbasis can be reindexed to a
`Fin n` common orthonormal eigenbasis while keeping track of the `yOrd` eigenspace label attached
to each coordinate. -/
lemma ordered_y_block_common_eigenbasis_fin
    (xOrd yOrd : Fin n → ℝ) (QOrd : Mₙ)
    (hComm : Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd)) :
    let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
    let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
    ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (z : Fin n → ℝ) (μidx : Fin n → Module.End.Eigenvalues D),
      (∀ i, D (b i) = ((μidx i : Module.End.Eigenvalues D) : ℝ) • b i) ∧
      ∀ i, C (b i) = z i • b i := by
  dsimp
  let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
  let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
  let hD := diagonal_toEuclideanLin_isSymmetric yOrd
  let hInt := hD.direct_sum_isInternal
  let hOrth := hD.orthogonalFamily_eigenspaces'
  rcases ordered_y_block_collected_simultaneous_basis xOrd yOrd QOrd hComm with
    ⟨bSigma, zSigma, hDbSigma, hCbSigma⟩
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simpa using finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin n)
  let e := hInt.sigmaOrthonormalBasisIndexEquiv hn hOrth
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := bSigma.reindex e
  let z : Fin n → ℝ := fun i => zSigma (e.symm i)
  let μidx : Fin n → Module.End.Eigenvalues D := fun i => (e.symm i).1
  refine ⟨b, z, μidx, ?_, ?_⟩
  · intro i
    -- Reindex the sigma-index eigenvalue equation along the canonical `Fin n` equivalence.
    simpa [b, μidx] using hDbSigma (e.symm i)
  · intro i
    -- The same reindexing keeps the ordered conjugate diagonal in the transported basis.
    simpa [b, z] using hCbSigma (e.symm i)

/-- Helper for Theorem 7.1: conjugating a real diagonal matrix by a matrix satisfying
`Q * Qᵀ = 1` preserves its characteristic polynomial. -/
lemma orthogonal_conjugate_diagonal_charpoly_eq
    (x : Fin n → ℝ) (Q : Mₙ) (hQ : Q * Qᵀ = 1) :
    (Qᵀ * diagonal x * Q : Mₙ).charpoly = (diagonal x : Mₙ).charpoly := by
  -- Cyclically commute the factors inside the characteristic polynomial until the orthogonal
  -- cancellation `Q * Qᵀ = 1` becomes visible.
  calc
    (Qᵀ * diagonal x * Q : Mₙ).charpoly = ((diagonal x * Q) * Qᵀ).charpoly := by
      rw [show Qᵀ * diagonal x * Q = Qᵀ * (diagonal x * Q) by simp [Matrix.mul_assoc]]
      simpa [Matrix.mul_assoc] using Matrix.charpoly_mul_comm Qᵀ (diagonal x * Q)
    _ = ((diagonal x) * (Q * Qᵀ)).charpoly := by
      simp [Matrix.mul_assoc]
    _ = (diagonal x : Mₙ).charpoly := by
      simp [hQ]

/-- Helper for Theorem 7.1: any orthogonal diagonalization of the ordered conjugate
`QOrdᵀ * diagonal xOrd * QOrd` has the same diagonal multiset as `xOrd`. -/
lemma ordered_simultaneous_diagonal_multiset_eq
    (xOrd z : Fin n → ℝ) (QOrd : Mₙ)
    (hQOrd_left : QOrd * QOrdᵀ = 1)
    (S : Matrix.orthogonalGroup (Fin n) ℝ)
    (hDiag : (QOrdᵀ * diagonal xOrd * QOrd : Mₙ) =
      (S : Mₙ) * diagonal z * ((S : Mₙ)ᵀ)) :
    Multiset.map z Finset.univ.val = Multiset.map xOrd Finset.univ.val := by
  have hS_right : ((S : Mₙ)ᵀ) * (((S : Mₙ)ᵀ)ᵀ) = 1 := by
    -- The transpose of an orthogonal matrix still satisfies the cancellation identity needed by
    -- the characteristic-polynomial comparison.
    simpa using (Matrix.mem_orthogonalGroup_iff' (A := (S : Mₙ)) (R := ℝ)).1 S.2
  have hCharX :
      (QOrdᵀ * diagonal xOrd * QOrd : Mₙ).charpoly = (diagonal xOrd : Mₙ).charpoly :=
    orthogonal_conjugate_diagonal_charpoly_eq xOrd QOrd hQOrd_left
  have hCharZ :
      ((S : Mₙ) * diagonal z * ((S : Mₙ)ᵀ) : Mₙ).charpoly = (diagonal z : Mₙ).charpoly := by
    -- The witness matrix `S` contributes only an orthogonal similarity, so the diagonal part keeps
    -- the same characteristic polynomial.
    simpa using orthogonal_conjugate_diagonal_charpoly_eq z ((S : Mₙ)ᵀ) hS_right
  have hCharDiag : (diagonal z : Mₙ).charpoly = (diagonal xOrd : Mₙ).charpoly := by
    -- Compare both diagonalizations through the common ordered conjugate.
    rw [← hCharZ, ← hDiag, hCharX]
  have hRoots :
      (diagonal z : Mₙ).charpoly.roots = (diagonal xOrd : Mₙ).charpoly.roots := by
    rw [hCharDiag]
  -- For diagonal matrices the characteristic-polynomial roots are exactly the diagonal entries,
  -- counted with multiplicity.
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod,
    Matrix.charpoly_diagonal, Polynomial.roots_prod] at hRoots
  · simpa using hRoots
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Helper for Theorem 7.1: a common orthonormal eigenbasis for two real matrices produces a
single orthogonal matrix that diagonalizes both matrices with the recorded eigenvalue lists. -/
lemma common_eigenbasis_orthogonal_diagonalization
    (A B : Mₙ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (z μ : Fin n → ℝ)
    (hA : ∀ i, Matrix.toEuclideanLin A (b i) = z i • b i)
    (hB : ∀ i, Matrix.toEuclideanLin B (b i) = μ i • b i) :
    ∃ S : Matrix.orthogonalGroup (Fin n) ℝ,
      A = (S : Mₙ) * diagonal z * ((S : Mₙ)ᵀ) ∧
      B = (S : Mₙ) * diagonal μ * ((S : Mₙ)ᵀ) := by
  have hSorth :
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b.toBasis ∈
        Matrix.orthogonalGroup (Fin n) ℝ := by
    -- The matrix with columns `b i` is orthogonal because `b` is an orthonormal basis.
    simpa using
      (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
  let S : Matrix.orthogonalGroup (Fin n) ℝ :=
    ⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b.toBasis, hSorth⟩
  refine ⟨S, ?_, ?_⟩
  · have hAS : A * (S : Mₙ) = (S : Mₙ) * diagonal z := by
      ext i j
      -- Read the `j`-th eigenvector equation in the standard coordinates.
      have hAij := congrArg (fun v => v i) (hA j)
      simp [Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.diagonal, S,
        Module.Basis.toMatrix_apply] at hAij ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using hAij
    have hSleft : (S : Mₙ) * ((S : Mₙ)ᵀ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff (A := (S : Mₙ)) (R := ℝ)).1 S.2
    -- Multiply by `Sᵀ` on the right to turn the eigenvector relation into a diagonalization.
    calc
      A = A * 1 := by simp
      _ = A * ((S : Mₙ) * ((S : Mₙ)ᵀ)) := by rw [hSleft]
      _ = (A * (S : Mₙ)) * ((S : Mₙ)ᵀ) := by simp [Matrix.mul_assoc]
      _ = (S : Mₙ) * diagonal z * ((S : Mₙ)ᵀ) := by rw [hAS]
  · have hBS : B * (S : Mₙ) = (S : Mₙ) * diagonal μ := by
      ext i j
      -- The same basis diagonalizes the second matrix with the eigenvalue list `μ`.
      have hBij := congrArg (fun v => v i) (hB j)
      simp [Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.diagonal, S,
        Module.Basis.toMatrix_apply] at hBij ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using hBij
    have hSleft : (S : Mₙ) * ((S : Mₙ)ᵀ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff (A := (S : Mₙ)) (R := ℝ)).1 S.2
    -- Reuse the same orthogonal basis matrix for the second diagonalization.
    calc
      B = B * 1 := by simp
      _ = B * ((S : Mₙ) * ((S : Mₙ)ᵀ)) := by rw [hSleft]
      _ = (B * (S : Mₙ)) * ((S : Mₙ)ᵀ) := by simp [Matrix.mul_assoc]
      _ = (S : Mₙ) * diagonal μ * ((S : Mₙ)ᵀ) := by rw [hBS]

/-- Helper for Theorem 7.1: once two matrices are diagonalized by the same orthogonal matrix,
their trace pairing is the dot product of the two diagonal lists. -/
lemma common_eigenbasis_trace_eq_dotProduct
    (A B : Mₙ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (z μ : Fin n → ℝ)
    (hA : ∀ i, Matrix.toEuclideanLin A (b i) = z i • b i)
    (hB : ∀ i, Matrix.toEuclideanLin B (b i) = μ i • b i) :
    trace (A * B) = dotProduct z μ := by
  obtain ⟨S, hDiagA, hDiagB⟩ :=
    common_eigenbasis_orthogonal_diagonalization A B b z μ hA hB
  have hS : ((S : Mₙ)ᵀ * (S : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (S : Mₙ)) (R := ℝ)).1 S.2
  -- Substitute the common orthogonal diagonalizations and cancel the middle factor `Sᵀ S`.
  conv_lhs => rw [hDiagA, hDiagB]
  rw [show (((S : Mₙ) * diagonal z * (S : Mₙ)ᵀ) *
      ((S : Mₙ) * diagonal μ * (S : Mₙ)ᵀ))
      = (S : Mₙ) * (diagonal z * diagonal μ) * (S : Mₙ)ᵀ by
        calc
          (((S : Mₙ) * diagonal z * (S : Mₙ)ᵀ) * ((S : Mₙ) * diagonal μ * (S : Mₙ)ᵀ))
            = (S : Mₙ) * diagonal z * (((S : Mₙ)ᵀ * (S : Mₙ)) * diagonal μ) * (S : Mₙ)ᵀ := by
                simp [Matrix.mul_assoc]
          _ = (S : Mₙ) * (diagonal z * diagonal μ) * (S : Mₙ)ᵀ := by
                simp [hS, Matrix.mul_assoc]]
  rw [Matrix.trace_mul_cycle (S : Mₙ) (diagonal z * diagonal μ) ((S : Mₙ)ᵀ)]
  simp [hS, Matrix.trace_diagonal, dotProduct]

/-- Helper for Theorem 7.1: if `diagonal yOrd` is diagonalized by an orthogonal matrix `S` with
diagonal entries `μ`, then the `j`-th column of `S` is supported on the `yOrd`-fiber of `μ j`. -/
lemma ordered_common_diagonalizer_column_support_on_y_fiber
    (yOrd μ : Fin n → ℝ)
    (S : Matrix.orthogonalGroup (Fin n) ℝ)
    (hDiagD : (diagonal yOrd : Mₙ) = (S : Mₙ) * diagonal μ * ((S : Mₙ)ᵀ)) :
    ∀ i j : Fin n, yOrd i ≠ μ j → (S : Mₙ) i j = 0 := by
  have hSright : ((S : Mₙ)ᵀ * (S : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (S : Mₙ)) (R := ℝ)).1 S.2
  have hMul :
      (diagonal yOrd : Mₙ) * (S : Mₙ) = (S : Mₙ) * diagonal μ := by
    -- Multiply the diagonalization on the right by `S` so the orthogonal cancellation isolates the
    -- diagonal eigenvalue relation for the columns of `S`.
    calc
      (diagonal yOrd : Mₙ) * (S : Mₙ)
        = ((S : Mₙ) * diagonal μ * (S : Mₙ)ᵀ) * (S : Mₙ) := by rw [hDiagD]
      _ = (S : Mₙ) * diagonal μ * (((S : Mₙ)ᵀ) * (S : Mₙ)) := by
            simp [Matrix.mul_assoc]
      _ = (S : Mₙ) * diagonal μ := by simp [hSright, Matrix.mul_assoc]
  intro i j hij
  have hijEntry : ((diagonal yOrd : Mₙ) * (S : Mₙ)) i j = ((S : Mₙ) * diagonal μ) i j := by
    simpa using congrArg (fun M : Mₙ => M i j) hMul
  have hEq :
      yOrd i * (S : Mₙ) i j = (S : Mₙ) i j * μ j := by
    -- Reading the `(i,j)` entry gives the scalar eigenvalue equation for the `j`-th column.
    simpa [Matrix.mul_apply, Matrix.diagonal, Finset.mul_sum] using hijEntry
  have hEq' : (S : Mₙ) i j * yOrd i = (S : Mₙ) i j * μ j := by
    simpa [mul_comm] using hEq
  have hZero : (S : Mₙ) i j * (yOrd i - μ j) = 0 := by
    calc
      (S : Mₙ) i j * (yOrd i - μ j)
        = (S : Mₙ) i j * yOrd i - (S : Mₙ) i j * μ j := by ring
      _ = 0 := by rw [hEq', sub_self]
  rcases mul_eq_zero.mp hZero with hEntry | hCoeff
  · exact hEntry
  · exact (hij <| sub_eq_zero.mp hCoeff).elim

/-- Helper for Theorem 7.1: two antitone finite tuples with the same multiset of entries agree
pointwise. -/
lemma antitone_eq_of_multiset_eq
    {α : Type*} [LinearOrder α]
    {f g : Fin n → α}
    (hf : Antitone f) (hg : Antitone g)
    (hfg : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    f = g := by
  have hperm : List.Perm (List.ofFn f) (List.ofFn g) := by
    have hLists : ((List.ofFn f : List α) : Multiset α) = (List.ofFn g : List α) := by
      simpa [Fin.univ_val_map] using hfg
    exact Multiset.coe_eq_coe.mp hLists
  -- Antitone tuples are the unique decreasing representatives of their common multiset.
  exact List.ofFn_injective <|
    hperm.eq_of_pairwise' hf.sortedGE_ofFn.pairwise hg.sortedGE_ofFn.pairwise

/-- Helper for Theorem 7.1: sorting a tuple in decreasing order recovers the unique antitone
representative of its multiset. -/
lemma sort_toDual_eq_of_antitone_multiset_eq
    {α : Type*} [LinearOrder α]
    {f g : Fin n → α}
    (hg : Antitone g)
    (hfg : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    f ∘ Tuple.sort (OrderDual.toDual ∘ f) = g := by
  have hsorted : Antitone (f ∘ Tuple.sort (OrderDual.toDual ∘ f)) := by
    -- Sorting `toDual ∘ f` in increasing order is the same as sorting `f` in decreasing order.
    simpa [Function.comp_assoc] using
      (Tuple.monotone_sort (OrderDual.toDual ∘ f) : Monotone
        (((OrderDual.toDual ∘ f) ∘ Tuple.sort (OrderDual.toDual ∘ f))))
  have hperm :
      List.Perm (List.ofFn (f ∘ Tuple.sort (OrderDual.toDual ∘ f))) (List.ofFn f) := by
    exact (Tuple.sort (OrderDual.toDual ∘ f)).ofFn_comp_perm f
  have hsortedMultiset :
      Multiset.map (f ∘ Tuple.sort (OrderDual.toDual ∘ f)) Finset.univ.val =
        Multiset.map f Finset.univ.val := by
    have hLists :
        ((List.ofFn (f ∘ Tuple.sort (OrderDual.toDual ∘ f)) : List α) : Multiset α) =
          (List.ofFn f : List α) := by
      exact Multiset.coe_eq_coe.mpr hperm
    simpa [Fin.univ_val_map] using hLists
  -- The decreasingly sorted tuple and the target antitone tuple are two antitone representatives
  -- of the same multiset, hence they agree pointwise.
  exact antitone_eq_of_multiset_eq hsorted hg (hsortedMultiset.trans hfg)

/-- Helper for Theorem 7.1: composing a finite tuple with a permutation preserves the multiset of
its entries. -/
lemma multiset_map_comp_perm
    {α : Type*} (f : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    Multiset.map (f ∘ σ) Finset.univ.val = Multiset.map f Finset.univ.val := by
  have hperm : List.Perm (List.ofFn (f ∘ σ)) (List.ofFn f) := σ.ofFn_comp_perm f
  have hLists :
      ((List.ofFn (f ∘ σ) : List α) : Multiset α) = (List.ofFn f : List α) := by
    exact Multiset.coe_eq_coe.mpr hperm
  -- Reading the tuple as a multiset forgets only the order, so permutation leaves it unchanged.
  simpa [Fin.univ_val_map] using hLists

/-- Helper for Theorem 7.1: reindexing a common eigenbasis by the decreasing lexicographic order
of `(μ, z)` produces a common orthogonal diagonalizer whose `D`-diagonal is exactly `yOrd`, while
the `C`-diagonal is already antitone inside each equal-`yOrd` block. -/
lemma ordered_reindexed_common_diagonalization
    (C D : Mₙ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (z μ yOrd : Fin n → ℝ)
    (hyOrd_antitone : Antitone yOrd)
    (hDb : ∀ i, Matrix.toEuclideanLin D (b i) = μ i • b i)
    (hCb : ∀ i, Matrix.toEuclideanLin C (b i) = z i • b i)
    (hμMultiset : Multiset.map μ Finset.univ.val = Multiset.map yOrd Finset.univ.val) :
    ∃ (SOrd : Matrix.orthogonalGroup (Fin n) ℝ) (zOrd : Fin n → ℝ),
      C = (SOrd : Mₙ) * diagonal zOrd * ((SOrd : Mₙ)ᵀ) ∧
      D = (SOrd : Mₙ) * diagonal yOrd * ((SOrd : Mₙ)ᵀ) ∧
      Multiset.map zOrd Finset.univ.val = Multiset.map z Finset.univ.val ∧
      ∀ ⦃i j : Fin n⦄, i ≤ j → yOrd i = yOrd j → zOrd i ≥ zOrd j := by
  let key : Fin n → Lex (OrderDual ℝ × OrderDual ℝ) :=
    fun i ↦ toLex (OrderDual.toDual (μ i), OrderDual.toDual (z i))
  let τ : Equiv.Perm (Fin n) := Tuple.sort key
  let zOrd : Fin n → ℝ := z ∘ τ
  have hμAntitone : Antitone (μ ∘ τ) := by
    intro i j hij
    -- The first coordinate of the lexicographically sorted key is decreasing.
    have hmono : key (τ i) ≤ key (τ j) := (Tuple.monotone_sort key) hij
    rcases Prod.Lex.toLex_le_toLex.mp hmono with hlt | hEq
    · simpa using le_of_lt hlt
    · simpa using hEq.1.symm.ge
  have hμ_sorted : μ ∘ τ = yOrd := by
    -- The sorted `μ`-tuple and `yOrd` are antitone representatives of the same multiset.
    refine antitone_eq_of_multiset_eq hμAntitone hyOrd_antitone ?_
    exact (multiset_map_comp_perm μ τ).trans hμMultiset
  let bOrd : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := b.reindex τ.symm
  obtain ⟨SOrd, hDiagCOrd, hDiagDOrd⟩ :=
    common_eigenbasis_orthogonal_diagonalization C D bOrd zOrd yOrd
      (by
        intro i
        -- Reindex the common `C`-eigenbasis along the lexicographic sort.
        simpa [bOrd, zOrd] using hCb (τ i))
      (by
        intro i
        -- The same reindexing turns the `D`-eigenvalue list into the theorem-order tuple `yOrd`.
        have hμi : μ (τ i) = yOrd i := by
          simpa [Function.comp_apply] using congrFun hμ_sorted i
        simpa [bOrd, hμi] using hDb (τ i))
  refine ⟨SOrd, zOrd, hDiagCOrd, hDiagDOrd, multiset_map_comp_perm z τ, ?_⟩
  intro i j hij hEq
  -- The second coordinate of the sorted lexicographic key orders `zOrd` inside each equal block.
  have hmono : key (τ i) ≤ key (τ j) := (Tuple.monotone_sort key) hij
  rcases Prod.Lex.toLex_le_toLex.mp hmono with hlt | hLex
  · exfalso
    have hμi : μ (τ i) = yOrd i := by
      simpa [Function.comp_apply] using congrFun hμ_sorted i
    have hμj : μ (τ j) = yOrd j := by
      simpa [Function.comp_apply] using congrFun hμ_sorted j
    have hylt : yOrd j < yOrd i := by
      simpa [hμi, hμj] using hlt
    have hneq : yOrd j ≠ yOrd i := ne_of_lt hylt
    exact hneq hEq.symm
  · simpa [zOrd] using hLex.2

/-- Helper for Theorem 7.1: the `0/1` indicator of a prefix in `Fin n` is antitone in the
ambient order. -/
lemma prefix_indicator_antitone (m : Fin n) :
    Antitone (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) := by
  intro i j hij
  by_cases hj : j ≤ m
  · have hi : i ≤ m := le_trans hij hj
    simp [hi, hj]
  · by_cases hi : i ≤ m
    · simp [hi, hj]
    · simp [hi, hj]

/-- Helper for Theorem 7.1: a strict `yOrd` prefix projector commutes with any matrix whose
entries vanish across different `yOrd` fibers. -/
lemma strict_cut_prefix_projector_commutes_with_supported_matrix
    (yOrd : Fin n → ℝ) (A : Mₙ)
    (hyOrd_antitone : Antitone yOrd)
    (hSupport : ∀ i j : Fin n, yOrd i ≠ yOrd j → A i j = 0)
    (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩) :
    Commute (diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0)) A := by
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  refine (diagonal_commute_iff_off_block_zero e A).2 ?_
  intro i j hij
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ m
    · simp [e, hi, hj] at hij
    · have hyi_ge : yOrd m ≤ yOrd i := by
        simpa using hyOrd_antitone hi
      have hsucc_le_j : (⟨m.1 + 1, hm⟩ : Fin n) ≤ j := by
        exact Nat.succ_le_of_lt (lt_of_not_ge hj)
      have hyj_le : yOrd j ≤ yOrd ⟨m.1 + 1, hm⟩ := hyOrd_antitone hsucc_le_j
      have hyij : yOrd i ≠ yOrd j := by
        apply ne_of_gt
        exact lt_of_lt_of_le (lt_of_le_of_lt hyj_le hgapY) hyi_ge
      exact hSupport i j hyij
  · by_cases hj : j ≤ m
    · have hyj_ge : yOrd m ≤ yOrd j := by
        simpa using hyOrd_antitone hj
      have hsucc_le_i : (⟨m.1 + 1, hm⟩ : Fin n) ≤ i := by
        exact Nat.succ_le_of_lt (lt_of_not_ge hi)
      have hyi_le : yOrd i ≤ yOrd ⟨m.1 + 1, hm⟩ := hyOrd_antitone hsucc_le_i
      have hyij : yOrd i ≠ yOrd j := by
        apply ne_of_lt
        exact lt_of_le_of_lt hyi_le (lt_of_lt_of_le hgapY hyj_ge)
      exact hSupport i j hyij
    · simp [e, hi, hj] at hij

/-- Helper for Theorem 7.1: once the theorem-order common diagonalizer respects every strict
`yOrd` fiber, tracing against a strict prefix projector reads off the corresponding prefix sum of
`zOrd`. -/
lemma ordered_reindexed_common_diagonalizer_prefix_trace
    (C : Mₙ) (zOrd yOrd : Fin n → ℝ)
    (SOrd : Matrix.orthogonalGroup (Fin n) ℝ)
    (hDiagCOrd : C = (SOrd : Mₙ) * diagonal zOrd * ((SOrd : Mₙ)ᵀ))
    (hyOrd_antitone : Antitone yOrd)
    (hSupportOrd : ∀ i j : Fin n, yOrd i ≠ yOrd j → (SOrd : Mₙ) i j = 0)
    (m : Fin n) (hm : (m : ℕ) + 1 < n)
    (hgapY : yOrd m > yOrd ⟨m.1 + 1, hm⟩) :
    trace (C * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0)) =
      dotProduct zOrd (fun i => if i ≤ m then (1 : ℝ) else 0) := by
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  have hComm :
      Commute (diagonal e) (SOrd : Mₙ) :=
    strict_cut_prefix_projector_commutes_with_supported_matrix
      yOrd (SOrd : Mₙ) hyOrd_antitone hSupportOrd m hm hgapY
  have hS_right : ((SOrd : Mₙ)ᵀ) * (SOrd : Mₙ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (SOrd : Mₙ)) (R := ℝ)).1 SOrd.2
  have hConj :
      ((SOrd : Mₙ)ᵀ) * diagonal e * (SOrd : Mₙ) = diagonal e := by
    calc
      ((SOrd : Mₙ)ᵀ) * diagonal e * (SOrd : Mₙ)
          = (SOrd : Mₙ)ᵀ * (diagonal e * (SOrd : Mₙ)) := by
              simp [Matrix.mul_assoc]
      _ = (SOrd : Mₙ)ᵀ * ((SOrd : Mₙ) * diagonal e) := by
            rw [hComm.eq]
      _ = (((SOrd : Mₙ)ᵀ) * (SOrd : Mₙ)) * diagonal e := by
            simp [Matrix.mul_assoc]
      _ = diagonal e := by simp [hS_right]
  -- Commute the strict prefix projector through the orthogonal diagonalization of `C`.
  calc
    trace (C * diagonal e)
      = trace (((SOrd : Mₙ) * diagonal zOrd * ((SOrd : Mₙ)ᵀ)) * diagonal e) := by
          rw [hDiagCOrd]
    _ = trace ((SOrd : Mₙ) * diagonal zOrd * (((SOrd : Mₙ)ᵀ) * diagonal e)) := by
          simp [Matrix.mul_assoc]
    _ = trace ((((SOrd : Mₙ)ᵀ) * diagonal e) * (SOrd : Mₙ) * diagonal zOrd) := by
          rw [Matrix.trace_mul_cycle (SOrd : Mₙ) (diagonal zOrd) (((SOrd : Mₙ)ᵀ) * diagonal e)]
    _ = trace ((((SOrd : Mₙ)ᵀ) * diagonal e * (SOrd : Mₙ)) * diagonal zOrd) := by
          simp [Matrix.mul_assoc]
    _ = trace (diagonal e * diagonal zOrd) := by
          rw [hConj]
    _ = dotProduct zOrd e := by
          simp [Matrix.trace_diagonal, dotProduct, e, mul_comm]

/-- Helper for Theorem 7.1: if a prefix of `z` already attains the same pairing with the binary
prefix indicator as the decreasing rearrangement `x`, then no larger entry of `z` can sit past
that cut. -/
lemma prefix_sum_eq_of_antitone_multiset_eq_forces_no_cross_inversion
    (x z : Fin n → ℝ)
    (hx : Antitone x)
    (hzx : Multiset.map z Finset.univ.val = Multiset.map x Finset.univ.val)
    (m : Fin n)
    (hPrefixEq :
      dotProduct z (fun i => if i ≤ m then (1 : ℝ) else 0) =
        dotProduct x (fun i => if i ≤ m then (1 : ℝ) else 0)) :
    ∀ ⦃i j : Fin n⦄, i ≤ m → m < j → z i ≥ z j := by
  let τ : Equiv.Perm (Fin n) := Tuple.sort (OrderDual.toDual ∘ z)
  let e : Fin n → ℝ := fun i => if i ≤ m then (1 : ℝ) else 0
  have hxz_sorted : z ∘ τ = x := sort_toDual_eq_of_antitone_multiset_eq hx hzx
  have hxz_eval : ∀ k : Fin n, x k = z (τ k) := by
    intro k
    simpa [Function.comp_apply] using (congrFun hxz_sorted k).symm
  have hxe : Monovary x e := hx.monovary (prefix_indicator_antitone m)
  have hEqτ : ∑ k, x k * e (τ k) = dotProduct x e := by
    -- Rewrite the sorted tuple back to `z`, then reindex the sum along the sorting permutation.
    calc
      ∑ k, x k * e (τ k) = ∑ k, z (τ k) * e (τ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hxz_eval]
      _ = ∑ k, z k * e k := by
        simpa using (Equiv.sum_comp τ (fun k : Fin n => z k * e k))
      _ = dotProduct z e := by
        simp [dotProduct]
      _ = dotProduct x e := hPrefixEq
  have hxeτ : Monovary x (e ∘ τ) :=
    (hxe.sum_mul_comp_perm_eq_sum_mul_iff (σ := τ)).1 hEqτ
  intro i j hi hj
  -- Equality in the prefix bound forces the original cut to already be decreasing across it.
  have hlt : (e ∘ τ) (τ.symm j) < (e ∘ τ) (τ.symm i) := by
    simp [e, Function.comp_apply, hi, not_le_of_gt hj]
  have hle : x (τ.symm j) ≤ x (τ.symm i) := hxeτ hlt
  have hleft : x (τ.symm j) = z j := by
    simpa [Function.comp_apply] using (congrFun hxz_sorted (τ.symm j)).symm
  have hright : x (τ.symm i) = z i := by
    simpa [Function.comp_apply] using (congrFun hxz_sorted (τ.symm i)).symm
  linarith

/-- Helper for Theorem 7.1: blockwise monotonicity inside equal `y`-fibers, together with
strict-cut monotonicity across every strict `y`-gap, upgrades to global antitonicity. -/
lemma blockwise_and_strict_cut_antitone_implies_antitone
    (y z : Fin n → ℝ)
    (hy : Antitone y)
    (hBlock : ∀ ⦃i j : Fin n⦄, i ≤ j → y i = y j → z i ≥ z j)
    (hCut :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        y m > y ⟨m.1 + 1, hm⟩ →
          ∀ ⦃i j : Fin n⦄, i ≤ m → m < j → z i ≥ z j) :
    Antitone z := by
  intro i j hij
  by_cases hEq : y i = y j
  · exact hBlock hij hEq
  · by_cases hijEq : i = j
    · subst hijEq
      exact le_rfl
    · have hij_lt : i < j := lt_of_le_of_ne hij hijEq
      -- A strict drop of `y` between `i` and `j` is witnessed by one adjacent strict cut.
      obtain ⟨m, hm, him, hmj, hgap⟩ :=
        antitone_distinct_values_have_strict_cut_between hy hij_lt hEq
      exact hCut m hm hgap him hmj

/-- Helper for Theorem 7.1: strict-cut prefix equalities force the theorem-order diagonal
`zOrd` to equal the decreasing ordered spectrum `xOrd`. -/
lemma ordered_reindexed_diagonal_eq_xOrd_of_prefix_traces
    (xOrd yOrd zOrd : Fin n → ℝ)
    (hxOrd_antitone : Antitone xOrd)
    (hyOrd_antitone : Antitone yOrd)
    (hZOrdMultiset : Multiset.map zOrd Finset.univ.val = Multiset.map xOrd Finset.univ.val)
    (hBlockAntitone : ∀ ⦃i j : Fin n⦄, i ≤ j → yOrd i = yOrd j → zOrd i ≥ zOrd j)
    (hPrefixEq :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          dotProduct zOrd (fun i => if i ≤ m then (1 : ℝ) else 0) =
            dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0)) :
    zOrd = xOrd := by
  have hCut :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          ∀ ⦃i j : Fin n⦄, i ≤ m → m < j → zOrd i ≥ zOrd j := by
    intro m hm hgap
    -- Each strict `yOrd` cut is rigid because the prefix sum of `zOrd` already matches the
    -- decreasing rearrangement `xOrd` at that cut.
    exact prefix_sum_eq_of_antitone_multiset_eq_forces_no_cross_inversion
      xOrd zOrd hxOrd_antitone hZOrdMultiset m (hPrefixEq m hm hgap)
  have hzOrd_antitone : Antitone zOrd :=
    blockwise_and_strict_cut_antitone_implies_antitone
      yOrd zOrd hyOrd_antitone hBlockAntitone hCut
  -- Once `zOrd` is antitone, it is the same decreasing representative of the common multiset.
  exact antitone_eq_of_multiset_eq hzOrd_antitone hxOrd_antitone hZOrdMultiset

/-- Helper for Theorem 7.1: conjugating a reindexed matrix by the permutation matrix of the
reindexing permutation recovers the original matrix. -/
lemma permMatrix_conj_reindex
    (σ : Equiv.Perm (Fin n)) (A : Mₙ) :
    (σ.permMatrix ℝ) * Matrix.reindex σ σ A * ((σ.permMatrix ℝ)ᵀ) = A := by
  have hleft :
      (σ.permMatrix ℝ) * Matrix.reindex σ σ A = (Matrix.reindex σ σ A).submatrix σ id := by
    simpa [Equiv.Perm.permMatrix] using
      (PEquiv.toMatrix_toPEquiv_mul (α := ℝ) (f := σ) (M := Matrix.reindex σ σ A))
  -- Multiply once on the left and once on the right to undo both reindexings.
  rw [show (σ.permMatrix ℝ) * Matrix.reindex σ σ A * ((σ.permMatrix ℝ)ᵀ) =
      ((σ.permMatrix ℝ) * Matrix.reindex σ σ A) * ((σ⁻¹).permMatrix ℝ) by
        simp]
  rw [hleft]
  ext i j
  rw [PEquiv.mul_toMatrix_apply,
    show ((Equiv.toPEquiv (σ⁻¹)).symm j) = some (σ j) by rfl]
  simp [Matrix.reindex_apply]

/-- Helper for Theorem 7.1: conjugating a diagonal matrix by a permutation matrix reindexes the
diagonal entries by that permutation. -/
lemma permMatrix_conj_diagonal
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (σ.permMatrix ℝ) * diagonal x * ((σ.permMatrix ℝ)ᵀ) = diagonal (x ∘ σ) := by
  have hleft :
      (σ.permMatrix ℝ) * diagonal x = (diagonal x).submatrix σ id := by
    simpa [Equiv.Perm.permMatrix] using
      (PEquiv.toMatrix_toPEquiv_mul (α := ℝ) (f := σ) (M := diagonal x))
  -- The permutation matrix just reindexes the diagonal labels.
  rw [show (σ.permMatrix ℝ) * diagonal x * ((σ.permMatrix ℝ)ᵀ) =
      ((σ.permMatrix ℝ) * diagonal x) * ((σ⁻¹).permMatrix ℝ) by
        simp]
  rw [hleft]
  ext i j
  rw [PEquiv.mul_toMatrix_apply,
    show ((Equiv.toPEquiv (σ⁻¹)).symm j) = some (σ j) by rfl]
  simp [Matrix.diagonal]

/-- Helper for Theorem 7.1: permutation matrices are orthogonal over `ℝ`. -/
private lemma permMatrix_mem_orthogonalGroup
    (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℝ : Mₙ) ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  refine (Matrix.mem_orthogonalGroup_iff (A := (σ.permMatrix ℝ : Mₙ)) (R := ℝ)).2 ?_
  rw [Matrix.transpose_permMatrix]
  calc
    σ.permMatrix ℝ * (σ⁻¹).permMatrix ℝ = ((σ⁻¹) * σ).permMatrix ℝ :=
      (Matrix.permMatrix_mul (R := ℝ) (σ := σ⁻¹) (τ := σ)).symm
    _ = 1 := by simp

/-- Helper for Theorem 7.1: an ordered common diagonalization of the reindexed relative conjugate
transports back to a theorem-coordinate common diagonalization of `X` and `Y`. -/
lemma ordered_transport_common_diagonalization_to_theorem_coordinates
    (X Y : 𝕊)
    (hX : (X : Mₙ).IsHermitian) (hY : (Y : Mₙ).IsHermitian)
    (U W Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hQ : (Q : Mₙ) = (U : Mₙ)ᵀ * (W : Mₙ))
    (hdiagX : (X : Mₙ) = (U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ)
    (hdiagY : (Y : Mₙ) = (W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ)
    (σ₀ : Equiv.Perm (Fin n))
    (xOrd yOrd : Fin n → ℝ)
    (hX_reindex : hX.eigenvalues = xOrd ∘ σ₀)
    (hY_reindex : hY.eigenvalues = yOrd ∘ σ₀)
    (QOrd : Mₙ)
    (hQOrd_def : QOrd = Matrix.reindex σ₀ σ₀ (Q : Mₙ))
    (SOrd : Matrix.orthogonalGroup (Fin n) ℝ)
    (hDiagCOrd : (QOrdᵀ * diagonal xOrd * QOrd : Mₙ) =
      (SOrd : Mₙ) * diagonal xOrd * ((SOrd : Mₙ)ᵀ))
    (hDiagDOrd : (diagonal yOrd : Mₙ) =
      (SOrd : Mₙ) * diagonal yOrd * ((SOrd : Mₙ)ᵀ)) :
    ∃ V : orthogonalGroup (Fin n) ℝ,
      (X : Mₙ) = (V : Mₙ) * diagonal hX.eigenvalues * (V : Mₙ)ᵀ ∧
        (Y : Mₙ) = (V : Mₙ) * diagonal hY.eigenvalues * (V : Mₙ)ᵀ := by
  let Pmat : Mₙ := σ₀.permMatrix ℝ
  let Pperm : Matrix.orthogonalGroup (Fin n) ℝ := ⟨Pmat, permMatrix_mem_orthogonalGroup σ₀⟩
  let T : Matrix.orthogonalGroup (Fin n) ℝ := Pperm * SOrd * Pperm⁻¹
  let V : Matrix.orthogonalGroup (Fin n) ℝ := W * T
  have hPmat_diagX : Pmat * diagonal xOrd * Pmatᵀ = diagonal hX.eigenvalues := by
    -- The theorem-order diagonal is the permutation conjugate of the ordered one.
    simpa [Pmat, hX_reindex, Function.comp_apply] using permMatrix_conj_diagonal σ₀ xOrd
  have hPmat_diagY : Pmat * diagonal yOrd * Pmatᵀ = diagonal hY.eigenvalues := by
    -- The same permutation transport identifies the theorem-order `Y` diagonal.
    simpa [Pmat, hY_reindex, Function.comp_apply] using permMatrix_conj_diagonal σ₀ yOrd
  have hPmat_QOrd : Pmat * QOrd * Pmatᵀ = (Q : Mₙ) := by
    -- Conjugating the reindexed relative orthogonal matrix returns the original `Q`.
    simpa [Pmat, hQOrd_def] using permMatrix_conj_reindex σ₀ (Q : Mₙ)
  have hPmat_QOrd_t : Pmat * QOrdᵀ * Pmatᵀ = (Q : Mₙ)ᵀ := by
    -- The same permutation transport applies to the transposed relative matrix.
    simpa [Pmat, hQOrd_def, Matrix.transpose_submatrix] using
      permMatrix_conj_reindex σ₀ ((Q : Mₙ)ᵀ)
  have hT_matrix : (T : Mₙ) = Pmat * (SOrd : Mₙ) * Pmatᵀ := by
    -- Unfold the orthogonal-group conjugation into the underlying matrix product.
    simp [T, Pperm, Pmat, Matrix.star_eq_conjTranspose, Matrix.transpose_permMatrix,
      Matrix.mul_assoc]
  have hPmat_right : Pmatᵀ * Pmat = (1 : Mₙ) := by
    -- The permutation matrix also satisfies the right orthogonality relation.
    dsimp [Pmat]
    rw [Matrix.transpose_permMatrix]
    calc
      (σ₀⁻¹).permMatrix ℝ * σ₀.permMatrix ℝ =
          (σ₀ * σ₀⁻¹).permMatrix ℝ :=
        (Matrix.permMatrix_mul (R := ℝ) (σ := σ₀) (τ := σ₀⁻¹)).symm
      _ = 1 := by simp
  have hQt : (Q : Mₙ)ᵀ = (W : Mₙ)ᵀ * (U : Mₙ) := by
    -- Transpose the relative-basis identity `Q = Uᵀ W`.
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hQ
  have hQ_diagX :
      (Q : Mₙ)ᵀ * diagonal hX.eigenvalues * (Q : Mₙ) = (W : Mₙ)ᵀ * (X : Mₙ) * (W : Mₙ) := by
    -- In the `W` basis, `X` is exactly the relative conjugate by `Q = Uᵀ W`.
    calc
      (Q : Mₙ)ᵀ * diagonal hX.eigenvalues * (Q : Mₙ)
        = ((W : Mₙ)ᵀ * (U : Mₙ)) * diagonal hX.eigenvalues * ((U : Mₙ)ᵀ * (W : Mₙ)) := by
            rw [hQt, hQ]
      _ = (W : Mₙ)ᵀ * ((U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ) * (W : Mₙ) := by
            simp [Matrix.mul_assoc]
      _ = (W : Mₙ)ᵀ * (X : Mₙ) * (W : Mₙ) := by
            simpa [hdiagX]
  have hTdiagY :
      diagonal hY.eigenvalues = (T : Mₙ) * diagonal hY.eigenvalues * ((T : Mₙ)ᵀ) := by
    -- Transport the ordered `Y` diagonalization through the fixed theorem-order permutation.
    rw [hT_matrix]
    refine Eq.symm ?_
    calc
      (Pmat * (SOrd : Mₙ) * Pmatᵀ) * diagonal hY.eigenvalues *
          ((Pmat * (SOrd : Mₙ) * Pmatᵀ)ᵀ)
        = (Pmat * (SOrd : Mₙ) * Pmatᵀ) * (Pmat * diagonal yOrd * Pmatᵀ) *
            ((Pmat * (SOrd : Mₙ) * Pmatᵀ)ᵀ) := by
            rw [hPmat_diagY.symm]
      _ = Pmat * (SOrd : Mₙ) * (Pmatᵀ * Pmat) * diagonal yOrd * (Pmatᵀ * Pmat) *
            ((SOrd : Mₙ)ᵀ) * Pmatᵀ := by
            simp [Matrix.mul_assoc]
      _ = Pmat * ((SOrd : Mₙ) * diagonal yOrd * ((SOrd : Mₙ)ᵀ)) * Pmatᵀ := by
            simp [Matrix.mul_assoc, hPmat_right]
      _ = diagonal hY.eigenvalues := by
            rw [← hDiagDOrd, hPmat_diagY]
  have hTdiagX :
      (Q : Mₙ)ᵀ * diagonal hX.eigenvalues * (Q : Mₙ) =
        (T : Mₙ) * diagonal hX.eigenvalues * ((T : Mₙ)ᵀ) := by
    -- The ordered common diagonalizer for `QOrdᵀ diag(xOrd) QOrd` transports to the theorem
    -- coordinates by the same permutation conjugation.
    rw [hT_matrix]
    refine Eq.symm ?_
    calc
      (Pmat * (SOrd : Mₙ) * Pmatᵀ) * diagonal hX.eigenvalues *
          ((Pmat * (SOrd : Mₙ) * Pmatᵀ)ᵀ)
        = (Pmat * (SOrd : Mₙ) * Pmatᵀ) * (Pmat * diagonal xOrd * Pmatᵀ) *
            ((Pmat * (SOrd : Mₙ) * Pmatᵀ)ᵀ) := by
            rw [hPmat_diagX.symm]
      _ = Pmat * (SOrd : Mₙ) * (Pmatᵀ * Pmat) * diagonal xOrd * (Pmatᵀ * Pmat) *
            ((SOrd : Mₙ)ᵀ) * Pmatᵀ := by
            simp [Matrix.mul_assoc]
      _ = Pmat * ((SOrd : Mₙ) * diagonal xOrd * ((SOrd : Mₙ)ᵀ)) * Pmatᵀ := by
            simp [Matrix.mul_assoc, hPmat_right]
      _ = Pmat * (QOrdᵀ * diagonal xOrd * QOrd) * Pmatᵀ := by
            rw [← hDiagCOrd]
      _ = Pmat * QOrdᵀ * (Pmatᵀ * Pmat) * diagonal xOrd * (Pmatᵀ * Pmat) * QOrd * Pmatᵀ := by
            simp [Matrix.mul_assoc, hPmat_right]
      _ = (Pmat * QOrdᵀ * Pmatᵀ) * (Pmat * diagonal xOrd * Pmatᵀ) * (Pmat * QOrd * Pmatᵀ) := by
            simp [Matrix.mul_assoc]
      _ = (Pmat * QOrdᵀ * Pmatᵀ) * diagonal hX.eigenvalues * (Pmat * QOrd * Pmatᵀ) := by
            rw [hPmat_diagX]
      _ = (Q : Mₙ)ᵀ * diagonal hX.eigenvalues * (Q : Mₙ) := by
            rw [hPmat_QOrd_t, hPmat_QOrd]
  refine ⟨V, ?_, ?_⟩
  · -- Substitute the transported `T`-diagonalization into the `W`-basis formula for `X`.
    calc
      (X : Mₙ) = (W : Mₙ) * ((W : Mₙ)ᵀ * (X : Mₙ) * (W : Mₙ)) * (W : Mₙ)ᵀ := by
            have hW_left : (W : Mₙ) * (W : Mₙ)ᵀ = 1 :=
              (Matrix.mem_orthogonalGroup_iff (A := (W : Mₙ)) (R := ℝ)).1 W.2
            calc
              (X : Mₙ) = (1 : Mₙ) * (X : Mₙ) * (1 : Mₙ) := by simp
              _ = ((W : Mₙ) * (W : Mₙ)ᵀ) * (X : Mₙ) * ((W : Mₙ) * (W : Mₙ)ᵀ) := by
                    rw [hW_left]
              _ = (W : Mₙ) * ((W : Mₙ)ᵀ * (X : Mₙ) * (W : Mₙ)) * (W : Mₙ)ᵀ := by
                    simp [Matrix.mul_assoc]
      _ = (W : Mₙ) * ((Q : Mₙ)ᵀ * diagonal hX.eigenvalues * (Q : Mₙ)) * (W : Mₙ)ᵀ := by
            rw [hQ_diagX.symm]
      _ = (W : Mₙ) * ((T : Mₙ) * diagonal hX.eigenvalues * ((T : Mₙ)ᵀ)) * (W : Mₙ)ᵀ := by
            rw [hTdiagX]
      _ = (V : Mₙ) * diagonal hX.eigenvalues * ((V : Mₙ)ᵀ) := by
            simp [V, T, Matrix.mul_assoc]
  · -- The same transported theorem-order diagonalization of `Y` gives the final common witness.
    calc
      (Y : Mₙ) = (W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ := hdiagY
      _ = (W : Mₙ) * ((T : Mₙ) * diagonal hY.eigenvalues * ((T : Mₙ)ᵀ)) * (W : Mₙ)ᵀ := by
            rw [hTdiagY.symm]
      _ = (V : Mₙ) * diagonal hY.eigenvalues * ((V : Mₙ)ᵀ) := by
            simp [V, T, Matrix.mul_assoc]

/-- Helper for Theorem 7.1: once the ordered equality frontier is upgraded to the projector
commutation and block-diagonalization statements, it yields the theorem-level common orthogonal
diagonalization after transporting through the fixed reindexing permutation. -/
lemma ordered_fan_equality_common_diagonalization
    (X Y : 𝕊)
    (hX : (X : Mₙ).IsHermitian) (hY : (Y : Mₙ).IsHermitian)
    (U W : Matrix.orthogonalGroup (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hQ : (Q : Mₙ) = (U : Mₙ)ᵀ * (W : Mₙ))
    (hdiagX : (X : Mₙ) = (U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ)
    (hdiagY : (Y : Mₙ) = (W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ)
    (σ₀ : Equiv.Perm (Fin n))
    (hσ₀ : ∀ {A : Mₙ} (hA : A.IsHermitian),
      hA.eigenvalues = ordered_hermitian_eigenvalues A hA ∘ σ₀)
    (wOrd : Equiv.Perm (Fin n) → ℝ)
    (xOrd : Fin n → ℝ) (yOrd : Fin n → ℝ)
    (hX_reindex : hX.eigenvalues = xOrd ∘ σ₀)
    (hY_reindex : hY.eigenvalues = yOrd ∘ σ₀)
    (hxOrd_antitone : Antitone xOrd)
    (hyOrd_antitone : Antitone yOrd)
    (hIndicatorEqOrd :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          dotProduct xOrd
              (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ
                (fun i => if i ≤ m then (1 : ℝ) else 0)) =
            dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0))
    (hZeroPatternOrd :
      ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
            ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
              (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)))
    (QOrd : Mₙ)
    (hQOrd_def : QOrd = Matrix.reindex σ₀ σ₀ (Q : Mₙ))
    (hQOrd_left : QOrd * QOrdᵀ = 1)
    (hQOrd_right : QOrdᵀ * QOrd = 1)
    (hPOrd :
      ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j) ^ 2) :
    ∃ V : orthogonalGroup (Fin n) ℝ,
      (X : Mₙ) = (V : Mₙ) * diagonal hX.eigenvalues * (V : Mₙ)ᵀ ∧
        (Y : Mₙ) = (V : Mₙ) * diagonal hY.eigenvalues * (V : Mₙ)ᵀ := by
  -- Route correction: the remaining work is no longer the Birkhoff transport. The missing step is
  -- to turn `hZeroPatternOrd` and `hPOrd` into commutation of ordered prefix projectors with
  -- `diagonal xOrd`, then diagonalize the ordered conjugate blockwise on the equal-`yOrd` blocks
  -- and transport the resulting ordered witness back through `σ₀`.
  have hPrefixCut :
      ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
            ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j)
                  = 0) ∧
              (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → r < j →
                ((QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) i j)
                  = 0)) := by
    intro m r hm hr hgapY hgapX
    -- This is the proved projector bridge at a fixed strict `xOrd`-cut and strict `yOrd`-cut.
    exact ordered_zero_pattern_to_prefix_projector_off_block_zero_of_strict_cut
      wOrd xOrd yOrd hZeroPatternOrd QOrd hQOrd_left hPOrd m r hm hr hgapY hgapX
  have hPrefixCommute :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          Commute (diagonal xOrd)
            (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ) := by
    intro m hm hgapY
    -- The separator lemma upgrades the fixed-cut zero pattern to full commutation with
    -- `diagonal xOrd` for each strict `yOrd` prefix projector.
    exact ordered_prefix_projector_commutes_with_diagonal
      wOrd xOrd yOrd hxOrd_antitone hZeroPatternOrd QOrd hQOrd_left hPOrd m hm hgapY
  have hPrefixTrace :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          trace (diagonal xOrd *
            (QOrd * diagonal (fun k : Fin n => if k ≤ m then (1 : ℝ) else 0) * QOrdᵀ)) =
            dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0) := by
    intro m hm hgapY
    -- The transported strict-prefix equality data now matches the trace against the ordered
    -- prefix projector exactly.
    exact ordered_prefix_projector_trace_eq_prefix_sum
      wOrd xOrd yOrd QOrd hPOrd hIndicatorEqOrd m hm hgapY
  have hOrderedConjugateCommute :
      Commute (QOrdᵀ * diagonal xOrd * QOrd) (diagonal yOrd) := by
    -- This is the proved bridge from strict-prefix commutation to full commutation with the
    -- ordered `yOrd` diagonal.
    exact ordered_conjugate_commutes_with_ordered_y_diagonal
      xOrd yOrd QOrd hyOrd_antitone hQOrd_right hPrefixCommute
  have hOrderedOffBlockZero :
      ∀ i j : Fin n, yOrd i ≠ yOrd j → (QOrdᵀ * diagonal xOrd * QOrd : Mₙ) i j = 0 := by
    -- The commutation frontier now yields the concrete theorem-order block decomposition.
    exact ordered_conjugate_off_block_zero_of_y_distinct
      xOrd yOrd QOrd hOrderedConjugateCommute
  have hOrderedBlockRestrictSymm :
      ∀ μ : ℝ,
        let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
        let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
        let hInv : ∀ v ∈ Module.End.eigenspace D μ, C v ∈ Module.End.eigenspace D μ :=
          fun _ hv => Module.End.mapsTo_genEigenspace_of_comm
            (matrix_toEuclideanLin_commute_of_commute _ _ hOrderedConjugateCommute).symm μ 1 hv
        (C.restrict hInv).IsSymmetric := by
    intro μ
    -- The commutation frontier now provides the symmetric restricted operators on each `yOrd`
    -- eigenspace, which is exactly the local input for the blockwise spectral theorem.
    exact ordered_y_block_restriction_symmetric xOrd yOrd QOrd hOrderedConjugateCommute μ
  have hCollectedBasis :
      let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
      let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
      ∃ (b : OrthonormalBasis
          ((μ : Module.End.Eigenvalues D) ×
            Fin (Module.finrank ℝ (Module.End.eigenspace D μ)))
          ℝ (EuclideanSpace ℝ (Fin n)))
        (z : ((μ : Module.End.Eigenvalues D) ×
            Fin (Module.finrank ℝ (Module.End.eigenspace D μ))) → ℝ),
        (∀ a, D (b a) = ((a.1 : Module.End.Eigenvalues D) : ℝ) • b a) ∧
        ∀ a, C (b a) = z a • b a := by
    -- The finite `yOrd`-block route is now fully realized: we have a sigma-indexed common
    -- orthonormal eigenbasis for the commuting symmetric pair.
    exact ordered_y_block_collected_simultaneous_basis xOrd yOrd QOrd hOrderedConjugateCommute
  have hFiniteCommonBasis :
      let C := Matrix.toEuclideanLin (QOrdᵀ * diagonal xOrd * QOrd : Mₙ)
      let D := Matrix.toEuclideanLin (diagonal yOrd : Mₙ)
      ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
        (z : Fin n → ℝ) (μidx : Fin n → Module.End.Eigenvalues D),
        (∀ i, D (b i) = ((μidx i : Module.End.Eigenvalues D) : ℝ) • b i) ∧
        ∀ i, C (b i) = z i • b i := by
    -- Reindex the sigma-index common eigenbasis to a genuine `Fin n` basis for the remaining
    -- theorem-order transport step.
    exact ordered_y_block_common_eigenbasis_fin xOrd yOrd QOrd hOrderedConjugateCommute
  let C : Mₙ := QOrdᵀ * diagonal xOrd * QOrd
  let D : Mₙ := diagonal yOrd
  rcases hFiniteCommonBasis with ⟨b, z, μidx, hDb, hCb⟩
  let μ : Fin n → ℝ := fun i ↦ ((μidx i : Module.End.Eigenvalues (Matrix.toEuclideanLin D)) : ℝ)
  obtain ⟨S, hDiagC, hDiagD⟩ :=
    common_eigenbasis_orthogonal_diagonalization C D b z μ
      (by
        intro i
        -- The `Fin n` common eigenbasis diagonalizes the ordered conjugate `C`.
        simpa [C] using hCb i)
      (by
        intro i
        -- The same basis records the `diagonal yOrd` eigenvalue attached to each basis vector.
        simpa [D, μ] using hDb i)
  have hZMultiset : Multiset.map z Finset.univ.val = Multiset.map xOrd Finset.univ.val := by
    -- The diagonal of the ordered conjugate must be a permutation of the ordered `xOrd` list.
    simpa [C] using
      ordered_simultaneous_diagonal_multiset_eq xOrd z QOrd hQOrd_left S hDiagC
  have hμMultiset : Multiset.map μ Finset.univ.val = Multiset.map yOrd Finset.univ.val := by
    have hDiagD' : (((1 : Mₙ)ᵀ) * diagonal yOrd * (1 : Mₙ) : Mₙ) =
        (S : Mₙ) * diagonal μ * ((S : Mₙ)ᵀ) := by
      simpa [D] using hDiagD
    -- The `D`-eigenvalue labels on the common basis are exactly the `yOrd` entries as a multiset.
    simpa [μ] using
      ordered_simultaneous_diagonal_multiset_eq yOrd μ (1 : Mₙ) (by simp) S hDiagD'
  have hColumnSupport :
      ∀ i j : Fin n, yOrd i ≠ μ j → (S : Mₙ) i j = 0 := by
    -- The explicit common diagonalizer now comes with the concrete fiber-support control needed
    -- for the reindexing-to-theorem-order step.
    simpa [D] using
      ordered_common_diagonalizer_column_support_on_y_fiber yOrd μ S hDiagD
  let τμ : Equiv.Perm (Fin n) := Tuple.sort (OrderDual.toDual ∘ μ)
  have hμ_sorted : μ ∘ τμ = yOrd := by
    -- The canonical decreasing sort of `μ` is already forced to be the theorem-order tuple
    -- `yOrd`, because both are antitone representatives of the same multiset.
    exact sort_toDual_eq_of_antitone_multiset_eq hyOrd_antitone hμMultiset
  have hTraceCommon : trace (C * D) = dotProduct z μ := by
    -- After passing to the common eigenbasis, the trace pairing becomes the diagonal dot product.
    exact common_eigenbasis_trace_eq_dotProduct C D b z μ
      (by
        intro i
        simpa [C] using hCb i)
      (by
        intro i
        simpa [D, μ] using hDb i)
  obtain ⟨SOrd, zOrd, hDiagCOrd, hDiagDOrd, hZOrdMultiset, hBlockAntitone⟩ :=
    ordered_reindexed_common_diagonalization C D b z μ yOrd hyOrd_antitone
      (by
        intro i
        simpa [D, μ] using hDb i)
      (by
        intro i
        simpa [C] using hCb i)
      hμMultiset
  have hSupportOrd :
      ∀ i j : Fin n, yOrd i ≠ yOrd j → (SOrd : Mₙ) i j = 0 := by
    -- The theorem-order common diagonalizer keeps each column inside the matching `yOrd` fiber.
    simpa using ordered_common_diagonalizer_column_support_on_y_fiber yOrd yOrd SOrd hDiagDOrd
  have hZOrdMultisetX :
      Multiset.map zOrd Finset.univ.val = Multiset.map xOrd Finset.univ.val :=
    hZOrdMultiset.trans hZMultiset
  -- The remaining work is now purely the ordered-uniqueness step for `zOrd = xOrd`, followed by
  -- the theorem-coordinate transport through `σ₀` and the original `W` basis.
  let _ := hQ
  let _ := hPrefixCut
  let _ := hPrefixCommute
  let _ := hPrefixTrace
  let _ := hOrderedConjugateCommute
  let _ := hOrderedOffBlockZero
  let _ := hOrderedBlockRestrictSymm
  let _ := hCollectedBasis
  let _ := hDiagC
  let _ := hDiagD
  let _ := hZMultiset
  let _ := hμMultiset
  let _ := hColumnSupport
  let _ := hTraceCommon
  let _ := SOrd
  let _ := zOrd
  let _ := hDiagCOrd
  let _ := hDiagDOrd
  let _ := hZOrdMultiset
  let _ := hBlockAntitone
  let _ := hSupportOrd
  let _ := hyOrd_antitone
  let _ := hQOrd_right
  have hPrefixTraceOrd :
      ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
        yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
          dotProduct zOrd (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) =
            dotProduct xOrd (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) := by
    intro m hm hgapY
    -- Compare the strict-prefix trace identity coming from the ordered common diagonalizer with
    -- the one transported directly from the Birkhoff equality case.
    calc
      dotProduct zOrd (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0)
        = trace (C * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0)) := by
            symm
            exact ordered_reindexed_common_diagonalizer_prefix_trace
              C zOrd yOrd SOrd hDiagCOrd hyOrd_antitone hSupportOrd m hm hgapY
      _ = dotProduct xOrd (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) := by
            calc
              trace (C * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0))
                = trace (diagonal xOrd *
                    (QOrd * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) * QOrdᵀ)) := by
                      calc
                        trace (C * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0))
                          = trace ((QOrdᵀ * diagonal xOrd) *
                              (QOrd * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0))) := by
                                  simp [C, Matrix.mul_assoc]
                        _ = trace ((QOrd * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) *
                              QOrdᵀ) * diagonal xOrd) := by
                                  simpa [Matrix.mul_assoc] using
                                    (Matrix.trace_mul_cycle QOrdᵀ (diagonal xOrd)
                                      (QOrd * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0)))
                        _ = trace (diagonal xOrd *
                              (QOrd * diagonal (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) * QOrdᵀ)) := by
                                  rw [Matrix.trace_mul_comm]
              _ = dotProduct xOrd (fun i : Fin n => if i ≤ m then (1 : ℝ) else 0) :=
                    hPrefixTrace m hm hgapY
  have hzx : zOrd = xOrd :=
    ordered_reindexed_diagonal_eq_xOrd_of_prefix_traces
      xOrd yOrd zOrd hxOrd_antitone hyOrd_antitone hZOrdMultisetX hBlockAntitone hPrefixTraceOrd
  have hDiagCOrdX :
      C = (SOrd : Mₙ) * diagonal xOrd * ((SOrd : Mₙ)ᵀ) := by
    -- Rewrite the ordered common diagonalization using the now-identified `zOrd = xOrd`.
    simpa [hzx] using hDiagCOrd
  -- The final step is pure permutation transport from the ordered common diagonalizer back to the
  -- theorem-coordinate basis determined by `σ₀`, `W`, and the relative matrix identity `Q = Uᵀ W`.
  exact ordered_transport_common_diagonalization_to_theorem_coordinates
    X Y hX hY U W Q hQ hdiagX hdiagY σ₀ xOrd yOrd hX_reindex hY_reindex
    QOrd hQOrd_def SOrd (by simpa [C] using hDiagCOrdX) hDiagDOrd

/-- Helper for Theorem 7.1: a common orthogonal diagonalization with the ordered eigenvalue lists
forces equality in Fan's inequality. -/
lemma common_orthogonal_diagonalization_implies_fan_equality (X Y : 𝕊)
    (h : ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
      (X : Mₙ) = (V : Mₙ) * diagonal X.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ ∧
        (Y : Mₙ) = (V : Mₙ) * diagonal Y.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ) :
    trace ((X : Mₙ) * (Y : Mₙ)) =
      dotProduct X.property.isHermitian.eigenvalues Y.property.isHermitian.eigenvalues := by
  rcases h with ⟨V, hX, hY⟩
  have hV : ((V : Mₙ)ᵀ * (V : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (V : Mₙ)) (R := ℝ)).1 V.2
  -- Substitute the common diagonalization and cancel the orthogonal middle factor.
  conv_lhs => rw [hX, hY]
  rw [show (((V : Mₙ) * diagonal X.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ) *
      ((V : Mₙ) * diagonal Y.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ))
      = (V : Mₙ) *
          (diagonal X.property.isHermitian.eigenvalues *
            diagonal Y.property.isHermitian.eigenvalues) *
          (V : Mₙ)ᵀ by
        calc
          (((V : Mₙ) * diagonal X.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ) *
              ((V : Mₙ) * diagonal Y.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ))
            = (V : Mₙ) * diagonal X.property.isHermitian.eigenvalues *
                (((V : Mₙ)ᵀ * (V : Mₙ)) * diagonal Y.property.isHermitian.eigenvalues) *
                (V : Mₙ)ᵀ := by
                  simp [mul_assoc]
          _ = (V : Mₙ) *
                (diagonal X.property.isHermitian.eigenvalues *
                  diagonal Y.property.isHermitian.eigenvalues) *
                (V : Mₙ)ᵀ := by
                  simp [hV, mul_assoc]]
  rw [Matrix.trace_mul_cycle (V : Mₙ)
    (diagonal X.property.isHermitian.eigenvalues * diagonal Y.property.isHermitian.eigenvalues)
    ((V : Mₙ)ᵀ)]
  simp [hV, Matrix.trace_diagonal, dotProduct]

-- Proof sketch: write `X` and `Y` in orthogonal eigenbases using Proposition 7.1, reduce
-- `Tr (X Y)` to `xᵀ P y` for a doubly stochastic matrix `P`, and then apply the rearrangement
-- inequality to the decreasing eigenvalue lists.
/-- Theorem 7.1: Fan's inequality for real symmetric matrices states that the trace pairing
`Tr(XY)` is bounded above by the Euclidean pairing of the ordered eigenvalue vectors
`λ(X)` and `λ(Y)`. -/
theorem fan_inequality_trace_le_dotProduct_eigenvalues (X Y : 𝕊) :
    let hX := X.property.isHermitian
    let hY := Y.property.isHermitian
    trace ((X : Mₙ) * (Y : Mₙ)) ≤ dotProduct hX.eigenvalues hY.eigenvalues := by
  dsimp
  let hX : (X : Mₙ).IsHermitian := X.property.isHermitian
  let hY : (Y : Mₙ).IsHermitian := Y.property.isHermitian
  let U : Matrix.orthogonalGroup (Fin n) ℝ := hX.eigenvectorUnitary
  let W : Matrix.orthogonalGroup (Fin n) ℝ := hY.eigenvectorUnitary
  let Q : Matrix.orthogonalGroup (Fin n) ℝ := star U * W
  have hQ : ((Q : Mₙ)) = (U : Mₙ)ᵀ * (W : Mₙ) := by
    change star (U : Mₙ) * (W : Mₙ) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hQt : ((Q : Mₙ)ᵀ) = (W : Mₙ)ᵀ * (U : Mₙ) := by
    change ((star (U : Mₙ) * (W : Mₙ))ᵀ) = _
    rw [Matrix.transpose_mul]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp
  have hdiagX : (X : Mₙ) = (U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ := by
    -- Use the Hermitian spectral theorem in real coordinates.
    simpa [hX, U, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_apply, mul_assoc] using hX.spectral_theorem
  have hdiagY : (Y : Mₙ) = (W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ := by
    -- The same diagonalization applies to `Y`.
    simpa [hY, W, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_apply, mul_assoc] using hY.spectral_theorem
  have htrace : trace ((X : Mₙ) * (Y : Mₙ)) =
      trace (diagonal hX.eigenvalues * (Q : Mₙ) * diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) := by
    -- Cycle the trace so that the orthogonal factors combine into `Q = Uᵀ W`.
    conv_lhs => rw [hdiagX, hdiagY]
    rw [show trace ((U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ *
        ((W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ))
        = trace (((U : Mₙ) * diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)) *
            (diagonal hY.eigenvalues * (W : Mₙ)ᵀ)) by
          simp [mul_assoc]]
    rw [Matrix.trace_mul_cycle ((U : Mₙ) * diagonal hX.eigenvalues) ((U : Mₙ)ᵀ * (W : Mₙ))
      (diagonal hY.eigenvalues * (W : Mₙ)ᵀ)]
    rw [show trace ((diagonal hY.eigenvalues * (W : Mₙ)ᵀ) *
        ((U : Mₙ) * diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)))
        = trace ((diagonal hY.eigenvalues * ((W : Mₙ)ᵀ * (U : Mₙ))) *
            (diagonal hX.eigenvalues * ((U : Mₙ)ᵀ * (W : Mₙ)))) by
          simp [mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [hQ, mul_assoc]
  calc
    trace ((X : Mₙ) * (Y : Mₙ))
      = trace (diagonal hX.eigenvalues * (Q : Mₙ) * diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) :=
          htrace
    _ = dotProduct hX.eigenvalues ((fun i j : Fin n => (Q i j)^2 : Mₙ) *ᵥ hY.eigenvalues) :=
          orthogonal_trace_reduction hX.eigenvalues hY.eigenvalues Q
    _ ≤ dotProduct hX.eigenvalues hY.eigenvalues :=
          doubly_stochastic_dotProduct_le_of_monovary _ _ _
            (hermitian_eigenvalues_monovary hX hY)
            (orthogonal_entrywise_sq_mem_doubly_stochastic Q)

-- Proof sketch: the forward direction refines the doubly-stochastic proof of Fan's inequality to
-- the equality case, forcing the same orthogonal basis to diagonalize both matrices with the
-- ordered eigenvalues on the diagonal. The reverse direction is immediate from cyclicity of trace
-- after substituting the common orthogonal diagonalizations.
/-- Equality in Fan's inequality holds exactly when the two symmetric matrices admit a common
orthogonal diagonalization whose diagonal entries are their ordered eigenvalue lists. -/
theorem fan_inequality_trace_eq_iff_exists_orthogonal_diagonalization (X Y : 𝕊) :
    let hX := X.property.isHermitian
    let hY := Y.property.isHermitian
    trace ((X : Mₙ) * (Y : Mₙ)) = dotProduct hX.eigenvalues hY.eigenvalues ↔
      ∃ V : orthogonalGroup (Fin n) ℝ,
        (X : Mₙ) = (V : Mₙ) * diagonal hX.eigenvalues * (V : Mₙ)ᵀ ∧
          (Y : Mₙ) = (V : Mₙ) * diagonal hY.eigenvalues * (V : Mₙ)ᵀ := by
  dsimp
  constructor
  · intro hEq
    let hX : (X : Mₙ).IsHermitian := X.property.isHermitian
    let hY : (Y : Mₙ).IsHermitian := Y.property.isHermitian
    let U : Matrix.orthogonalGroup (Fin n) ℝ := hX.eigenvectorUnitary
    let W : Matrix.orthogonalGroup (Fin n) ℝ := hY.eigenvectorUnitary
    let Q : Matrix.orthogonalGroup (Fin n) ℝ := star U * W
    let P : Mₙ := fun i j : Fin n => (Q i j)^2
    have hQ : ((Q : Mₙ)) = (U : Mₙ)ᵀ * (W : Mₙ) := by
      change star (U : Mₙ) * (W : Mₙ) = _
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have hdiagX : (X : Mₙ) = (U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ := by
      -- Use the Hermitian spectral theorem in real coordinates.
      simpa [hX, U, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
        Function.comp_apply, mul_assoc] using hX.spectral_theorem
    have hdiagY : (Y : Mₙ) = (W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ := by
      -- The same diagonalization applies to `Y`.
      simpa [hY, W, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
        Function.comp_apply, mul_assoc] using hY.spectral_theorem
    have htrace : trace ((X : Mₙ) * (Y : Mₙ)) =
        trace (diagonal hX.eigenvalues * (Q : Mₙ) * diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) := by
      -- Cycle the trace so the relative orthogonal matrix `Q = Uᵀ W` appears explicitly.
      conv_lhs => rw [hdiagX, hdiagY]
      rw [show trace ((U : Mₙ) * diagonal hX.eigenvalues * (U : Mₙ)ᵀ *
          ((W : Mₙ) * diagonal hY.eigenvalues * (W : Mₙ)ᵀ))
          = trace (((U : Mₙ) * diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)) *
              (diagonal hY.eigenvalues * (W : Mₙ)ᵀ)) by
            simp [mul_assoc]]
      rw [Matrix.trace_mul_cycle ((U : Mₙ) * diagonal hX.eigenvalues) ((U : Mₙ)ᵀ * (W : Mₙ))
        (diagonal hY.eigenvalues * (W : Mₙ)ᵀ)]
      rw [show trace ((diagonal hY.eigenvalues * (W : Mₙ)ᵀ) *
          ((U : Mₙ) * diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)))
          = trace ((diagonal hY.eigenvalues * ((W : Mₙ)ᵀ * (U : Mₙ))) *
              (diagonal hX.eigenvalues * ((U : Mₙ)ᵀ * (W : Mₙ)))) by
            simp [mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp [hQ, mul_assoc]
    have hP_ds : P ∈ doublyStochastic ℝ (Fin n) := by
      -- The squared orthogonal entries form the doubly stochastic matrix from the proof.
      simpa [P] using orthogonal_entrywise_sq_mem_doubly_stochastic Q
    obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP_ds
    have hEqP : dotProduct hX.eigenvalues (P *ᵥ hY.eigenvalues) =
        dotProduct hX.eigenvalues hY.eigenvalues := by
      -- Rewrite the trace equality into the doubly stochastic pairing equality.
      calc
        dotProduct hX.eigenvalues (P *ᵥ hY.eigenvalues)
          = trace (diagonal hX.eigenvalues * (Q : Mₙ) * diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) := by
              simpa [P] using (orthogonal_trace_reduction hX.eigenvalues hY.eigenvalues Q).symm
        _ = trace ((X : Mₙ) * (Y : Mₙ)) := by rw [htrace]
        _ = dotProduct hX.eigenvalues hY.eigenvalues := hEq
    have hEqBirkhoff :
        dotProduct hX.eigenvalues
          (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ hY.eigenvalues) =
            dotProduct hX.eigenvalues hY.eigenvalues := by
      -- Substitute the Birkhoff decomposition of the squared-entry matrix.
      simpa [P, hwP] using hEqP
    have hPermMonovary :
        ∀ σ, 0 < w σ → Monovary hX.eigenvalues (hY.eigenvalues ∘ σ) := by
      -- Equality forces every positive-weight permutation to be a rearrangement equality case.
      exact fan_equality_implies_positive_weight_perm_monovary
        hX.eigenvalues hY.eigenvalues w hw_nonneg hw_sum
        (hermitian_eigenvalues_monovary hX hY) hEqBirkhoff
    let xOrd : Fin n → ℝ := ordered_hermitian_eigenvalues (X : Mₙ) hX
    let yOrd : Fin n → ℝ := ordered_hermitian_eigenvalues (Y : Mₙ) hY
    have hxOrd_antitone : Antitone xOrd := ordered_hermitian_eigenvalues_antitone _ hX
    have hyOrd_antitone : Antitone yOrd := ordered_hermitian_eigenvalues_antitone _ hY
    obtain ⟨σ₀, hσ₀⟩ := exists_ordered_hermitian_eigenvalues_reindex_perm (n := n)
    have hX_reindex : hX.eigenvalues = xOrd ∘ σ₀ := hσ₀ hX
    have hY_reindex : hY.eigenvalues = yOrd ∘ σ₀ := hσ₀ hY
    -- Route correction: the strict-cut API must run on the ordered coordinates `xOrd` and `yOrd`,
    -- not directly on mathlib's arbitrary `eigenvalues` indexing from the theorem statement.
    let wOrd : Equiv.Perm (Fin n) → ℝ := fun π ↦ w (σ₀.symm.permCongr π)
    have hw_nonnegOrd : ∀ π, 0 ≤ wOrd π := by
      intro π
      exact hw_nonneg (σ₀.symm.permCongr π)
    have hw_sumOrd : ∑ π, wOrd π = 1 := by
      -- Reindex the Birkhoff weights by conjugation into the ordered coordinate basis.
      simpa [wOrd] using (Equiv.sum_comp (σ₀.symm.permCongr) w).trans hw_sum
    have hPermMonovaryOrd :
        ∀ π, 0 < wOrd π → Monovary xOrd (yOrd ∘ π) := by
      intro π hπ
      -- Transport the positive-weight rearrangement equality cases through the fixed reindexing.
      exact fan_equality_implies_positive_weight_perm_monovary_ordered
        hX hY w σ₀ hX_reindex hY_reindex hPermMonovary π hπ
    have hxyOrd : Monovary xOrd yOrd := hxOrd_antitone.monovary hyOrd_antitone
    have hIndicatorEqOrd :
        ∀ (m : Fin n) (hm : (m : ℕ) + 1 < n),
          yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
            dotProduct xOrd
                (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ
                  (fun i => if i ≤ m then (1 : ℝ) else 0)) =
              dotProduct xOrd (fun i => if i ≤ m then (1 : ℝ) else 0) := by
      intro m hm hgap
      -- The strict-cut equality characterization now holds entirely in the ordered coordinates.
      exact strict_y_cut_prefix_indicator_equality wOrd hw_nonnegOrd hw_sumOrd
        hxyOrd hPermMonovaryOrd hyOrd_antitone m hm hgap
    have hZeroPatternOrd :
        ∀ (m r : Fin n) (hm : (m : ℕ) + 1 < n) (hr : (r : ℕ) + 1 < n),
          yOrd m > yOrd ⟨m.1 + 1, hm⟩ →
            xOrd r > xOrd ⟨r.1 + 1, hr⟩ →
              ((m ≤ r → ∀ ⦃i j : Fin n⦄, r < i → j ≤ m →
                  (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0) ∧
                (r < m → ∀ ⦃i j : Fin n⦄, i ≤ r → m < j →
                  (((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) i j) = 0)) := by
      intro m r hm hr hgapY hgapX
      -- Route correction: the equality support is now upgraded directly to the split one-sided
      -- ordered zero pattern from the positive-weight permutation geometry.
      exact ordered_strict_cut_birkhoff_zero_pattern hxOrd_antitone hyOrd_antitone
        wOrd hw_nonnegOrd hPermMonovaryOrd m hm hgapY r hr hgapX
    let QOrd : Mₙ := Matrix.reindex σ₀ σ₀ (Q : Mₙ)
    have hQOrd_left : QOrd * QOrdᵀ = 1 := by
      -- Reindexing the relative orthogonal matrix preserves `QOrd QOrdᵀ = 1`.
      simpa [QOrd] using ordered_relative_orthogonal_left Q σ₀
    have hQOrd_right : QOrdᵀ * QOrd = 1 := by
      -- The companion orthogonality identity survives the same reindexing.
      simpa [QOrd] using ordered_relative_orthogonal_right Q σ₀
    have hPOrd :
        ((∑ π, wOrd π • π.permMatrix ℝ : Mₙ) : Mₙ) = fun i j => (QOrd i j)^2 := by
      -- Route correction: the transported zero-pattern statements now land on the actual ordered
      -- relative orthogonal matrix rather than only on an abstract conjugated Birkhoff sum.
      simpa [QOrd, Matrix.reindex_apply] using
        ordered_birkhoff_matrix_eq_orthostochastic_conjugate Q w σ₀ hwP
    -- Route correction: the last step is now isolated as an ordered common-diagonalization
    -- problem. The Birkhoff transport is finished; what remains is the projector/block argument.
    exact ordered_fan_equality_common_diagonalization X Y hX hY U W Q hQ
      hdiagX hdiagY σ₀ hσ₀ wOrd xOrd yOrd hX_reindex hY_reindex
      hxOrd_antitone hyOrd_antitone hIndicatorEqOrd hZeroPatternOrd
      QOrd rfl hQOrd_left hQOrd_right hPOrd
  · intro hDiag
    -- Substituting a common orthogonal diagonalization reduces the trace to the diagonal pairing.
    exact common_orthogonal_diagonalization_implies_fan_equality X Y hDiag

end
