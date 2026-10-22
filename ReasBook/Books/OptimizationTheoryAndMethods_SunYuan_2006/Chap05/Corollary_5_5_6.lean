/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_5_5

open Matrix

noncomputable section

-- Semantic recall: Corollary 5.5.6 is a source-facing bridge over the ordered-eigenvalue
-- interlacing API already established in Theorem 5.5.5 for `ssvmInverseUpdate R r r φ γ`.
-- The reusable companion theorem records the interval form `μ_i^φ ∈ Set.uIcc 1 λ_i` for the
-- `γ = 1` specialization, and the labeled corollary then becomes the standard absolute-value
-- consequence `|μ_i^φ - 1| ≤ |λ_i - 1|`.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter05 Corollary 5.5.6: a finite real sequence whose first value is above `1`
and whose last value is at most `1` has a first adjacent crossing of the level `1`. -/
private lemma endpointCrossingIndex
    {f : Fin n → ℝ} (hn : 0 < n)
    (hLast : f ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ≤ 1)
    (hFirst : ¬ f ⟨0, hn⟩ ≤ 1) :
    ∃ k : ℕ, ∃ hk : k + 1 < n, f ⟨k + 1, hk⟩ ≤ 1 ∧
      1 ≤ f ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  let P : ℕ → Prop := fun m => ∃ hm : m < n, f ⟨m, hm⟩ ≤ 1
  have hExists : ∃ m : ℕ, P m := by
    -- The last index already witnesses that the sequence eventually reaches `≤ 1`.
    refine ⟨n - 1, ?_⟩
    exact ⟨Nat.sub_lt hn (Nat.succ_pos 0), hLast⟩
  let m := Nat.find hExists
  have hmSpec : P m := Nat.find_spec hExists
  rcases hmSpec with ⟨hm_lt, hm_le⟩
  have hm_pos : 0 < m := by
    -- The first qualifying index cannot be `0`, because the initial value is still above `1`.
    by_contra hm_not_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not_pos
    have hm_lt_zero : 0 < n := by
      simpa [hm_zero] using hm_lt
    have hm_le_zero : f ⟨0, hm_lt_zero⟩ ≤ 1 := by
      simpa [hm_zero] using hm_le
    have hm_index_eq : (⟨0, hm_lt_zero⟩ : Fin n) = ⟨0, hn⟩ := by
      ext
      rfl
    exact hFirst (by simpa [hm_index_eq] using hm_le_zero)
  have hk : (m - 1) + 1 < n := by
    -- The predecessor sits immediately before the first crossing index.
    have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    simpa [hm_eq] using hm_lt
  refine ⟨m - 1, hk, ?_, ?_⟩
  · -- The first qualifying index already lies on the `≤ 1` side.
    have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    simpa [hm_eq] using hm_le
  · -- Minimality forces the predecessor value to remain on the `≥ 1` side.
    have hPrevLt : m - 1 < n := by
      exact lt_of_lt_of_le
        (Nat.sub_lt (Nat.succ_le_of_lt hm_pos) (Nat.succ_pos 0))
        hm_lt.le
    have hPrevNotLe : ¬ f ⟨m - 1, hPrevLt⟩ ≤ 1 := by
      intro hPrevLe
      have hFindLe : m ≤ m - 1 :=
        Nat.find_min' hExists ⟨hPrevLt, hPrevLe⟩
      have hPrevLtSelf : m - 1 < m :=
        Nat.sub_lt (Nat.succ_le_of_lt hm_pos) (Nat.succ_pos 0)
      exact (Nat.not_le_of_gt hPrevLtSelf) hFindLe
    exact le_of_lt (lt_of_not_ge hPrevNotLe)

/-- Helper for Chapter05 Corollary 5.5.6: every updated eigenvalue on the left side of the
crossing stays between `1` and the corresponding ordered eigenvalue of the original matrix. -/
private theorem leftTailMemUiccOfCrossing
    {m : ℕ} {lam mu : Fin (m + 1) → ℝ} {k : ℕ} (hk : k + 1 < m + 1)
    (hLeft : ∀ j : ℕ, ∀ hj : j < k,
      lam ⟨j + 1, Nat.lt_trans (Nat.succ_lt_succ hj) hk⟩ ≤
          mu ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩ ∧
        mu ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩ ≤
          lam ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩)
    (hCrossLower : 1 ≤ mu ⟨k, Nat.lt_of_succ_lt hk⟩)
    (hCrossUpper : mu ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ lam ⟨k, Nat.lt_of_succ_lt hk⟩)
    (i : Fin (m + 1)) (hi : i.1 ≤ k) :
    mu i ∈ Set.uIcc 1 (lam i) := by
  have hBounds :
      ∀ j : ℕ, j ≤ k →
        ∃ hjm : j < m + 1, 1 ≤ mu ⟨j, hjm⟩ ∧ mu ⟨j, hjm⟩ ≤ lam ⟨j, hjm⟩ := by
    intro j hj
    induction hj using Nat.decreasingInduction with
    | self =>
        -- The crossing index itself is one of the two explicit theorem outputs.
        refine ⟨Nat.lt_of_succ_lt hk, ?_, ?_⟩
        · simpa using hCrossLower
        · simpa using hCrossUpper
    | of_succ j hj ih =>
        -- Move one step left using the adjacent interval supplied by the crossing theorem.
        rcases ih with ⟨hjm, hjLower, hjUpper⟩
        have hStep := hLeft j hj
        have hStepLower :
            lam ⟨j + 1, hjm⟩ ≤
              mu ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩ := by
          simpa using hStep.1
        have hStepUpper :
            mu ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩ ≤
              lam ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk)⟩ := by
          simpa using hStep.2
        refine ⟨Nat.lt_of_succ_lt (Nat.lt_trans (Nat.succ_lt_succ hj) hk), ?_, hStepUpper⟩
        exact le_trans (le_trans hjLower hjUpper) hStepLower
  rcases hBounds i.1 hi with ⟨hi_lt, hiLower, hiUpper⟩
  have hi_eq : (⟨i.1, hi_lt⟩ : Fin (m + 1)) = i := by
    ext
    rfl
  -- Convert the directed bounds into unordered-interval membership at the requested index.
  simpa [hi_eq] using Set.mem_uIcc_of_le hiLower hiUpper

/-- Helper for Chapter05 Corollary 5.5.6: every updated eigenvalue on the right side of the
crossing stays between the corresponding ordered eigenvalue of the original matrix and `1`. -/
private theorem rightTailMemUiccOfCrossing
    {m : ℕ} {lam mu : Fin (m + 1) → ℝ} {k : ℕ} (hk : k + 1 < m + 1)
    (hCrossLower : lam ⟨k + 1, hk⟩ ≤ mu ⟨k + 1, hk⟩)
    (hCrossUpper : mu ⟨k + 1, hk⟩ ≤ 1)
    (hRight : ∀ j : ℕ, ∀ _ : k < j, ∀ hj_upper : j < m,
      lam ⟨j + 1, Nat.succ_lt_succ hj_upper⟩ ≤
          mu ⟨j + 1, Nat.succ_lt_succ hj_upper⟩ ∧
        mu ⟨j + 1, Nat.succ_lt_succ hj_upper⟩ ≤
          lam ⟨j, Nat.lt_trans hj_upper (Nat.lt_succ_self m)⟩)
    (i : Fin (m + 1)) (hi : k + 1 ≤ i.1) :
    mu i ∈ Set.uIcc 1 (lam i) := by
  have hBounds :
      ∀ j : ℕ, k + 1 ≤ j →
        ∀ hjm : j < m + 1, lam ⟨j, hjm⟩ ≤ mu ⟨j, hjm⟩ ∧ mu ⟨j, hjm⟩ ≤ 1 := by
    intro j hjLower
    induction j, hjLower using Nat.le_induction with
    | base =>
        intro hjm
        -- The first index on the right side is the second explicit crossing output.
        constructor
        · simpa using hCrossLower
        · simpa using hCrossUpper
    | succ j hjLower ih =>
        intro hjm
        -- Move one step right using the adjacent interval supplied by the crossing theorem.
        have hjPrev : j < m := by
          omega
        have hPrev := ih (by omega)
        have hStep := hRight j (lt_of_lt_of_le (Nat.lt_succ_self k) hjLower) hjPrev
        constructor
        · simpa using hStep.1
        · exact le_trans (by simpa using hStep.2) (le_trans hPrev.1 hPrev.2)
  have hiBounds := hBounds i.1 hi i.isLt
  -- Convert the directed bounds into unordered-interval membership at the requested index.
  exact Set.mem_uIcc_of_ge hiBounds.1 hiBounds.2

/-- Helper for Chapter05 Corollary 5.5.6: in the mixed-spectrum case of Theorem 5.5.5, every
updated ordered eigenvalue still lies in `Set.uIcc 1 λ_i`. -/
private theorem memUiccOneOfCrossingCase
    {m : ℕ} {R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hR : R.IsHermitian)
    (r : EuclideanSpace ℝ (Fin (m + 1)))
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hLast : hR.eigenvalues (Fin.last m) ≤ 1)
    (hFirst : 1 < hR.eigenvalues 0) (i : Fin (m + 1)) :
    (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues i ∈
      Set.uIcc 1 (hR.eigenvalues i) :=
by
  -- Route correction: stay on the public owner `hR.eigenvalues` and use the crossing theorem's
  -- native adjacent-index output instead of transporting through a separate antitonicity bridge.
  have hn : 0 < m + 1 := Nat.succ_pos m
  let hRφ : (ssvmInverseUpdate R r r φ 1).IsHermitian :=
    ssvmInverseUpdate_self_one_isHermitian hR r φ
  have hLast' :
      (1 : ℝ) * hR.eigenvalues ⟨m, Nat.lt_succ_self m⟩ ≤ 1 := by
    have hLastFin : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
      ext
      rfl
    simpa [hLastFin] using hLast
  have hFirst' :
      1 ≤ (1 : ℝ) * hR.eigenvalues ⟨0, hn⟩ := by
    simpa using le_of_lt hFirst
  rcases endpointCrossingIndex
      (f := fun j : Fin (m + 1) ↦ hR.eigenvalues j) hn hLast (not_le_of_gt hFirst) with
    ⟨k, hk, hCrossLower, hCrossUpper⟩
  have hCrossLower' : (1 : ℝ) * hR.eigenvalues ⟨k + 1, hk⟩ ≤ 1 := by
    simpa using hCrossLower
  have hCrossUpper' :
      1 ≤ (1 : ℝ) * hR.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩ := by
    simpa using hCrossUpper
  have hCase := by
    -- Specialize the mixed crossing theorem at `γ = 1` and normalize the owner once.
    simpa [one_mul, hRφ] using
      ssvmInverseUpdate_self_eigenvalues_case_crossing_one
        hR r hrr hrRr (φ := φ) (γ := 1) hn hφ zero_lt_one
        hLast' hFirst' k hk hCrossLower' hCrossUpper'
  rcases hCase with
    ⟨hLeft, hCrossTopLower, hCrossTopUpper, hCrossBottomLower, hCrossBottomUpper, hRight, _⟩
  by_cases hi : i.1 ≤ k
  · -- Indices at or to the left of the crossing satisfy the `1 ≤ μ_i ≤ λ_i` orientation.
    exact leftTailMemUiccOfCrossing hk hLeft hCrossTopLower hCrossTopUpper i hi
  · -- Indices to the right of the crossing satisfy the `λ_i ≤ μ_i ≤ 1` orientation.
    have hiRight : k + 1 ≤ i.1 := by
      omega
    exact rightTailMemUiccOfCrossing hk hCrossBottomLower hCrossBottomUpper hRight i hiRight

/-- Chapter05 Corollary 5.5.6: if `φ ∈ Set.Icc (0 : ℝ) 1`, then for the `γ_k = 1`
self-scaling SSVM representative update the corresponding ordered eigenvalue `μ_i^φ` lies in the
unordered closed interval between `1` and the corresponding ordered eigenvalue `λ_i` of `R`. This
is the source-facing interval form of Theorem 5.5.5 specialized to `γ = 1`. -/
theorem ssvmUpdatedEigenvalue_mem_uIcc_one
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues i ∈
      Set.uIcc 1 (hR.eigenvalues i) := by
  -- This is the `γ = 1` interval consequence of the three ordered-eigenvalue cases in
  -- `ssvmInverseUpdate_self_eigenvalues_case_ge_one`,
  -- `ssvmInverseUpdate_self_eigenvalues_case_le_one`, and
  -- `ssvmInverseUpdate_self_eigenvalues_case_crossing_one`.
  cases n with
  | zero =>
      -- In dimension zero there are no eigenvalue indices to check.
      exact Fin.elim0 i
  | succ m =>
      by_cases hLast : 1 ≤ hR.eigenvalues (Fin.last m)
      · -- If the smallest ordered eigenvalue is already above `1`, the first case theorem gives
        -- the required interval membership.
        have hLastFin : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
          apply Fin.ext
          rfl
        have hLastCast : 1 ≤ hR.eigenvalues ⟨m, Nat.lt_succ_self m⟩ := by
          simpa [hLastFin] using hLast
        have hLast' :
            1 ≤ (1 : ℝ) * hR.eigenvalues ⟨m, Nat.lt_succ_self m⟩ := by
          simpa using hLastCast
        have hCase := by
          -- Normalize the `γ = 1` case theorem before splitting the `Fin` index.
          simpa [one_mul] using
            ssvmInverseUpdate_self_eigenvalues_case_ge_one
              hR r hrr hrRr (φ := φ) (γ := 1) (Nat.succ_pos m) hφ zero_lt_one hLast'
        rcases hCase with ⟨hLastEq, hRest⟩
        have hLastEqCast :
            (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues ⟨m, Nat.lt_succ_self m⟩ =
              1 := by
          simpa using hLastEq
        have hLastEq' :
            (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues (Fin.last m) = 1 := by
          simpa [hLastFin] using hLastEqCast
        cases i using Fin.lastCases with
        | last =>
            -- The last updated eigenvalue is exactly `1`.
            rw [hLastEq']
            exact Set.mem_uIcc_of_le le_rfl hLast
        | cast j =>
            -- Every earlier eigenvalue lies between two ordered eigenvalues that are both at
            -- least `1`.
            have hBounds := hRest j.1 j.2
            have hSuccEq : (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) = j.succ := by
              apply Fin.ext
              rfl
            have hCastEq : (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (m + 1)) = j.castSucc := by
              apply Fin.ext
              rfl
            have hLowerEig : 1 ≤ hR.eigenvalues j.succ := by
              simpa [hSuccEq] using hBounds.1
            have hMiddle :
                hR.eigenvalues j.succ ≤
                  (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues j.castSucc := by
              simpa [hSuccEq, hCastEq] using hBounds.2.1
            have hUpper :
                (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues j.castSucc ≤
                  hR.eigenvalues j.castSucc := by
              simpa [hCastEq] using hBounds.2.2
            exact Set.mem_uIcc_of_le (le_trans hLowerEig hMiddle) hUpper
      · by_cases hFirst : hR.eigenvalues 0 ≤ 1
        · -- If the largest ordered eigenvalue is already at most `1`, the second case theorem
          -- gives the required interval membership.
          have hFirst' : (1 : ℝ) * hR.eigenvalues ⟨0, Nat.succ_pos m⟩ ≤ 1 := by
            simpa using hFirst
          have hCase := by
            -- Normalize the `γ = 1` case theorem before splitting the `Fin` index.
            simpa [one_mul] using
              ssvmInverseUpdate_self_eigenvalues_case_le_one
                hR r hrr hrRr (φ := φ) (γ := 1) (Nat.succ_pos m) hφ zero_lt_one hFirst'
          rcases hCase with ⟨hFirstEq, hRest⟩
          have hFirstEq' :
              (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues 0 = 1 := by
            simpa using hFirstEq
          cases i using Fin.cases with
          | zero =>
              -- The first updated eigenvalue is exactly `1`.
              rw [hFirstEq']
              exact Set.mem_uIcc_of_ge hFirst le_rfl
          | succ j =>
              -- Every later eigenvalue lies between two ordered eigenvalues that are both at
              -- most `1`.
              have hBounds := hRest j.1 j.2
              have hSuccEq : (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (m + 1)) = j.succ := by
                apply Fin.ext
                rfl
              have hCastEq : (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (m + 1)) = j.castSucc := by
                apply Fin.ext
                rfl
              have hLower :
                  hR.eigenvalues j.succ ≤
                    (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues j.succ := by
                simpa [hSuccEq] using hBounds.1
              have hUpperStep :
                  (ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues j.succ ≤
                    hR.eigenvalues j.castSucc := by
                simpa [hSuccEq, hCastEq] using hBounds.2.1
              have hUpperEig : hR.eigenvalues j.castSucc ≤ 1 := by
                simpa [hCastEq] using hBounds.2.2
              exact Set.mem_uIcc_of_ge hLower (le_trans hUpperStep hUpperEig)
        · -- Route correction: when the ordered eigenvalues straddle `1`, extract the first
          -- crossing index and feed the mixed case theorem instead of forcing a direct rewrite.
          have hLastLe : hR.eigenvalues (Fin.last m) ≤ 1 := le_of_not_ge hLast
          have hFirstGt : 1 < hR.eigenvalues 0 := lt_of_not_ge hFirst
          exact memUiccOneOfCrossingCase hR r hrr hrRr hφ hLastLe hFirstGt i

/-- Chapter05 Corollary 5.5.6: if `φ ∈ Set.Icc (0 : ℝ) 1`, then for the `γ_k = 1`
self-scaling SSVM representative update the corresponding ordered eigenvalues `μ_i^φ` and `λ_i`
of `ssvmInverseUpdate R r r φ 1` and `R` satisfy
`|μ_i^φ - 1| ≤ |λ_i - 1|`. -/
theorem ssvmUpdatedEigenvalue_abs_sub_one_le
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    |(ssvmInverseUpdate_self_one_isHermitian hR r φ).eigenvalues i - 1| ≤
      |hR.eigenvalues i - 1| := by
  simpa [abs_sub_comm] using
    Set.abs_sub_left_of_mem_uIcc
      (ssvmUpdatedEigenvalue_mem_uIcc_one hR r hrr hrRr hφ i)

end
