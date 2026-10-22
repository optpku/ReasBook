/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Remark_2_31

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An asymptotic orthonormal subsequence of `x` is a strictly monotone reindexing of `x`
together with an orthonormal sequence that approximates the reindexed sequence in norm. -/
private structure AsymptoticOrthonormalSubsequence (x : ℕ → H) where
  /-- The subsequence extraction map. -/
  subseq : ℕ → ℕ
  /-- The extraction map is strictly monotone. -/
  strictMono_subseq : StrictMono subseq
  /-- The orthonormal comparison sequence. -/
  orthonormalSeq : ℕ → H
  /-- The comparison sequence is orthonormal. -/
  orthonormal_orthonormalSeq : Orthonormal ℝ orthonormalSeq
  /-- The reindexed sequence is asymptotic in norm to the orthonormal comparison sequence. -/
  tendsto_sub_orthonormalSeq :
    Tendsto (fun n ↦ x (subseq n) - orthonormalSeq n) atTop (nhds (0 : H))

/-- Helper for Proposition 2.49: every fixed inner-product coordinate of a weakly null sequence
also tends to `0`. -/
-- Proof sketch: apply the weak-topology characterization to the Fréchet-Riesz functional
-- represented by the testing vector.
private lemma weak_tendsto_zero_inner_right (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H))) (u : H) :
    Tendsto (fun n ↦ inner ℝ u (x n)) atTop (nhds 0) := by
  -- Evaluate weak convergence through the canonical inner-product characterization of Remark 2.31.
  have hx' : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (toWeakSpace ℝ H (0 : H))) := by
    simpa using hx
  have hu :
      Tendsto (fun n ↦ inner ℝ (x n) u) atTop (nhds (inner ℝ (0 : H) u)) :=
    (weakConvergence_iff_forall_tendsto_inner_right x (0 : H)).1 hx' u
  simpa [real_inner_comm] using hu

/-- Helper for Proposition 2.49: for a finite family of test vectors, weak convergence yields a far
tail index where all inner products are simultaneously small. -/
-- Proof sketch: bundle the finitely many coordinates into a single map
-- `ℕ → (Fin (n + 1) → ℝ)`, use convergence to `0` in the finite product, then read each
-- coordinate bound from the norm bound.
private lemma exists_far_index_with_small_inner_family (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (y : Fin (n + 1) → H) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m > N, ∀ i, |inner ℝ (y i) (x m)| < δ := by
  have hall : ∀ᶠ m in atTop, ∀ i, |inner ℝ (y i) (x m)| < δ := by
    -- Build the simultaneous estimate by induction on the finite index family.
    induction n with
    | zero =>
        have hcoord : Tendsto (fun m ↦ inner ℝ (y 0) (x m)) atTop (nhds 0) :=
          weak_tendsto_zero_inner_right x hx (y 0)
        have habs : Tendsto (fun m ↦ |inner ℝ (y 0) (x m)|) atTop (nhds 0) := by
          simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).1 hcoord
        filter_upwards [habs.eventually (eventually_lt_nhds hδ)] with m hm i
        fin_cases i
        simpa using hm
    | succ n ih =>
        have hlast_coord :
            Tendsto (fun m ↦ inner ℝ (y (Fin.last (n + 1))) (x m)) atTop (nhds 0) :=
          weak_tendsto_zero_inner_right x hx (y (Fin.last (n + 1)))
        have hlast_abs :
            Tendsto (fun m ↦ |inner ℝ (y (Fin.last (n + 1))) (x m)|) atTop (nhds 0) := by
          simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).1 hlast_coord
        have hinit :
            ∀ᶠ m in atTop, ∀ i : Fin (n + 1), |inner ℝ ((Fin.init y) i) (x m)| < δ :=
          ih (Fin.init y)
        filter_upwards [hlast_abs.eventually (eventually_lt_nhds hδ), hinit] with m hm_last hm_init i
        cases i using Fin.lastCases with
        | last =>
            simpa using hm_last
        | cast j =>
            simpa using hm_init j
  rcases (hall.and (eventually_gt_atTop N)).exists with ⟨m, hm_small, hm_gt⟩
  exact ⟨m, hm_gt, hm_small⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: normalizing a nonzero vector perturbs a unit vector by at most
twice the pre-normalization error. -/
-- Proof sketch: first compare `x` to the unnormalized vector `v`, then compare `v` to its
-- normalization using the reverse triangle inequality on the norms.
private lemma norm_sub_normalized_block_le_twice {x v : H} (hx : ‖x‖ = 1) (hv : v ≠ 0) :
    ‖x - (‖v‖)⁻¹ • v‖ ≤ 2 * ‖x - v‖ := by
  let y : H := (‖v‖)⁻¹ • v
  have hy_norm : ‖y‖ = 1 := by
    -- The normalization has unit norm because `v` is nonzero.
    calc
      ‖y‖ = |‖v‖⁻¹| * ‖v‖ := by
        simpa [y] using (norm_smul (‖v‖⁻¹) v)
      _ = 1 := by
        rw [abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hv_eq : v = ‖v‖ • y := by
    -- Recover `v` by scaling its normalization back by its norm.
    calc
      v = (‖v‖ * ‖v‖⁻¹) • v := by
        rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
      _ = ‖v‖ • y := by
        simp [y, smul_smul]
  have hcol : v - y = (‖v‖ - 1) • y := by
    -- The vector `v - y` stays on the same line as `y`.
    calc
      v - y = ‖v‖ • y - y := by
        simpa using congrArg (fun z => z - y) hv_eq
      _ = ‖v‖ • y - 1 • y := by rw [one_smul]
      _ = (‖v‖ - 1) • y := by
        simpa using (sub_smul ‖v‖ (1 : ℝ) y).symm
  have hvy : ‖v - y‖ = |‖v‖ - 1| := by
    -- Since `v` and `y` are positively collinear, their distance is the norm defect.
    calc
      ‖v - y‖ = ‖(‖v‖ - 1) • y‖ := by
        rw [hcol]
      _ = |‖v‖ - 1| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = |‖v‖ - 1| := by simp [hy_norm]
  have hnorm_defect : |‖v‖ - 1| ≤ ‖x - v‖ := by
    -- The reverse triangle inequality controls the norm defect by the ambient distance.
    calc
      |‖v‖ - 1| ≤ ‖v - x‖ := by simpa [hx] using abs_norm_sub_norm_le v x
      _ = ‖x - v‖ := by rw [norm_sub_rev]
  calc
    ‖x - y‖ ≤ ‖x - v‖ + ‖v - y‖ := by
      -- Split the error into the truncation part and the normalization part.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (norm_add_le (x - v) (v - y))
    _ = ‖x - v‖ + |‖v‖ - 1| := by rw [hvy]
    _ ≤ ‖x - v‖ + ‖x - v‖ := by gcongr
    _ = 2 * ‖x - v‖ := by ring

/-- Helper for Proposition 2.49: a finite stage of the asymptotic orthonormal subsequence
construction records a finite subsequence, an orthonormal comparison family, and the stagewise
approximation bounds. -/
private structure AlmostOrthonormalState (x : ℕ → H) (ε : ℕ → ℝ) (n : ℕ) where
  /-- The finite extraction map at stage `n`. -/
  k : Fin (n + 1) → ℕ
  /-- The finite orthonormal comparison family at stage `n`. -/
  y : Fin (n + 1) → H
  /-- The finite extraction map is strictly monotone. -/
  strictMono_k : StrictMono k
  /-- The finite comparison family is orthonormal. -/
  orthonormal_y : Orthonormal ℝ y
  /-- Each extracted vector is close to its comparison vector. -/
  close : ∀ i, ‖x (k i) - y i‖ ≤ ε i

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: the finite linear combination built from the inner products
against an orthonormal family has norm controlled by the sum of the coefficient bounds. -/
-- Proof sketch: estimate the norm of the sum by the sum of the norms and then use the unit norm of
-- each orthonormal vector.
private lemma norm_sum_inner_smul_le {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y) (z : H)
    {δ : ℝ} (hsmall : ∀ i, |inner ℝ (y i) z| ≤ δ) :
    ‖∑ i : Fin (n + 1), inner ℝ (y i) z • y i‖ ≤ (n + 1 : ℝ) * δ := by
  have hterm : ∀ i : Fin (n + 1), ‖inner ℝ (y i) z • y i‖ = |inner ℝ (y i) z| := by
    intro i
    rw [norm_smul, hy.norm_eq_one i, mul_one, Real.norm_eq_abs]
  calc
    ‖∑ i : Fin (n + 1), inner ℝ (y i) z • y i‖ ≤
        ∑ i : Fin (n + 1), ‖inner ℝ (y i) z • y i‖ := by
      exact norm_sum_le _ _
    _ = ∑ i : Fin (n + 1), |inner ℝ (y i) z| := by
      simp [hterm]
    _ ≤ ∑ i : Fin (n + 1), δ := by
      exact Finset.sum_le_sum fun i _ ↦ hsmall i
    _ = (n + 1 : ℝ) * δ := by
      simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: subtracting the finite inner-product expansion makes the residual
orthogonal to each member of the orthonormal family. -/
-- Proof sketch: the orthonormal expansion reproduces the chosen coordinate, so the coordinate of
-- the residual vanishes after subtraction.
private lemma inner_residual_eq_zero {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y) (z : H)
    (i : Fin (n + 1)) :
    inner ℝ (y i) (z - ∑ j : Fin (n + 1), inner ℝ (y j) z • y j) = 0 := by
  rw [inner_sub_right, hy.inner_right_fintype, sub_self]

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: adjoining the normalized residual of an orthonormal finite family
preserves orthonormality when the residual is orthogonal to the old family and nonzero. -/
-- Proof sketch: old-old pairs stay orthonormal, old-new and new-old pairs vanish by the residual
-- orthogonality, and the normalized residual has norm one.
private lemma orthonormal_snoc_normalized {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y)
    {v : H}
    (hv : ∀ i, inner ℝ (y i) v = 0) (hv_ne : v ≠ 0) :
    Orthonormal ℝ (Fin.snoc y ((‖v‖)⁻¹ • v)) := by
  constructor
  · intro i
    cases i using Fin.lastCases with
    | last =>
        -- The new vector is normalized by the inverse of its norm.
        have hnorm : ‖(‖v‖)⁻¹ • v‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
            inv_mul_cancel₀ (norm_ne_zero_iff.2 hv_ne)]
        simpa [Fin.snoc_last] using hnorm
    | cast i =>
        -- The old entries keep their unit norm.
        simpa using hy.norm_eq_one i
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            exact (hij rfl).elim
        | cast j =>
            -- The new vector is orthogonal to every old entry by assumption.
            have hv' : inner ℝ v (y j) = 0 := by
              simpa [real_inner_comm] using hv j
            simp [Fin.snoc_last, Fin.snoc_castSucc, hv', inner_smul_left]
    | cast i =>
        cases j using Fin.lastCases with
        | last =>
            -- The old vector is orthogonal to the new residual.
            simp [Fin.snoc_last, Fin.snoc_castSucc, hv i, inner_smul_right]
        | cast j =>
            -- Old-old pairs inherit orthogonality from the previous stage.
            have hneq : i ≠ j := by
              intro hij'
              apply hij
              simp [hij']
            simpa [Fin.snoc_castSucc] using hy.inner_eq_zero hneq

/-- Helper for Proposition 2.49: one finite almost-orthonormal stage can be extended by choosing a
later vector that is nearly orthogonal to the old family and normalizing its residual. -/
-- Proof sketch: choose a far index with uniformly small inner products against the old orthonormal
-- family, subtract the finite orthogonal expansion, normalize the residual, and append the new
-- data by `Fin.snoc`.
private lemma extend_almost_orthonormal_state (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (hx_norm : ∀ n : ℕ, ‖x n‖ = 1) {ε : ℕ → ℝ} {n : ℕ}
    (s : AlmostOrthonormalState x ε n) (hε_pos : 0 < ε (n + 1)) (hε_small : ε (n + 1) < 1 / 2) :
    ∃ s' : AlmostOrthonormalState x ε (n + 1),
      (∀ i : Fin (n + 1), s'.k i.castSucc = s.k i) ∧
      (∀ i : Fin (n + 1), s'.y i.castSucc = s.y i) := by
  let δ : ℝ := ε (n + 1) / (2 * (n + 1 : ℝ))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases exists_far_index_with_small_inner_family x hx s.y (s.k (Fin.last n)) hδ_pos with
    ⟨m, hm_gt, hm_small⟩
  let p : H := ∑ i : Fin (n + 1), inner ℝ (s.y i) (x m) • s.y i
  let v : H := x m - p
  let yNew : H := (‖v‖)⁻¹ • v
  have hp_norm_le : ‖p‖ ≤ (n + 1 : ℝ) * δ := by
    -- The old coordinates are all small, so the finite orthogonal expansion is small as well.
    exact norm_sum_inner_smul_le s.orthonormal_y (x m) fun i ↦
      le_of_lt (hm_small i)
  have hp_half : ‖p‖ ≤ ε (n + 1) / 2 := by
    -- The chosen threshold makes the whole projection error at most `ε (n+1) / 2`.
    have hcard_pos : (0 : ℝ) < n + 1 := by positivity
    have hδ_mul : (n + 1 : ℝ) * δ = ε (n + 1) / 2 := by
      dsimp [δ]
      field_simp [hcard_pos.ne']
    calc
      ‖p‖ ≤ (n + 1 : ℝ) * δ := hp_norm_le
      _ = ε (n + 1) / 2 := hδ_mul
  have hxv : x m - v = p := by
    -- By construction, `v` is the residual after removing the finite orthogonal expansion.
    simp [v, p, sub_eq_add_neg, add_comm]
  have hv_dist : ‖x m - v‖ ≤ ε (n + 1) / 2 := by
    simpa [hxv] using hp_half
  have hv_ne : v ≠ 0 := by
    -- If the residual vanished, the unit vector `x m` would lie too close to `0`.
    intro hv_zero
    have hhalf_lt_one : ε (n + 1) / 2 < 1 := by
      nlinarith
    have : (1 : ℝ) ≤ ε (n + 1) / 2 := by
      calc
        (1 : ℝ) = ‖x m‖ := by simp [hx_norm m]
        _ = ‖x m - v‖ := by simp [hv_zero]
        _ ≤ ε (n + 1) / 2 := hv_dist
    linarith
  refine ⟨
    { k := Fin.snoc s.k m
      y := Fin.snoc s.y yNew
      strictMono_k := ?_
      orthonormal_y := ?_
      close := ?_ },
    ?_,
    ?_⟩
  · -- Appending a strictly later index preserves the strict monotonicity of the extraction map.
    intro i j hij
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last =>
            exact (lt_irrefl _ hij).elim
        | cast i =>
            have hi_le : s.k i ≤ s.k (Fin.last n) := by
              by_cases hi_last : i = Fin.last n
              · simp [hi_last]
              · exact le_of_lt (s.strictMono_k (lt_of_le_of_ne (Fin.le_last i) hi_last))
            simpa [Fin.snoc_castSucc, Fin.snoc_last] using lt_of_le_of_lt hi_le hm_gt
    | cast j =>
        cases i using Fin.lastCases with
        | last =>
            exact (not_lt_of_ge (Fin.le_last _)) hij |>.elim
        | cast i =>
            simpa [Fin.snoc_castSucc] using s.strictMono_k (Fin.castSucc_lt_castSucc_iff.1 hij)
  · -- The new comparison vector is the normalized residual, hence orthonormal to the old family.
    apply orthonormal_snoc_normalized s.orthonormal_y
    · intro i
      simpa [v, p] using inner_residual_eq_zero s.orthonormal_y (x m) i
    · exact hv_ne
  · intro i
    cases i using Fin.lastCases with
    | last =>
        -- The last error estimate comes from the residual approximation and the normalization bound.
        have hnormalize :
            ‖x m - yNew‖ ≤ 2 * ‖x m - v‖ := by
          simpa [yNew] using
            norm_sub_normalized_block_le_twice (hx_norm m) hv_ne
        simpa [Fin.snoc_last] using
          (calc
            ‖x m - yNew‖ ≤ 2 * ‖x m - v‖ := hnormalize
            _ ≤ 2 * (ε (n + 1) / 2) := by gcongr
            _ = ε (n + 1) := by ring)
    | cast i =>
        -- The old error bounds are preserved on the old coordinates.
        simpa [Fin.snoc_castSucc] using s.close i
  · intro i
    simp [Fin.snoc_castSucc]
  · intro i
    simp [Fin.snoc_castSucc]

/-- Proposition 2.49: a weakly null sequence of unit vectors in a real Hilbert space admits a
subsequence that is asymptotic in norm to an orthonormal sequence. -/
-- Proof sketch: choose a Hilbert basis of the closed span of the sequence and inductively extract
-- a subsequence whose low-frequency and high-frequency Fourier tails are both small on successive
-- disjoint blocks. The block truncations form an orthogonal sequence; normalizing them gives an
-- orthonormal sequence, and the truncation error tends to `0`.
theorem exists_subseq_tendsto_zero_sub_orthonormal_of_tendsto_zero_weakly_of_norm_eq_one
    (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (hx_norm : ∀ n : ℕ, ‖x n‖ = 1) :
    ∃ subseq : ℕ → ℕ, ∃ orthonormalSeq : ℕ → H,
      StrictMono subseq ∧
        Orthonormal ℝ orthonormalSeq ∧
          Tendsto (fun n ↦ x (subseq n) - orthonormalSeq n) atTop (nhds (0 : H)) := by
  classical
  let ε : ℕ → ℝ := fun n ↦ ((n : ℝ) + 4)⁻¹
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε_small : ∀ n, ε n < 1 / 2 := by
    intro n
    have hn : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have htwo : (2 : ℝ) < (n : ℝ) + 4 := by
      nlinarith
    simpa [ε] using one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) htwo
  have hbase : AlmostOrthonormalState x ε 0 := by
    refine
      { k := fun _ ↦ 0
        y := fun _ ↦ x 0
        strictMono_k := ?_
        orthonormal_y := ?_
        close := ?_ }
    · intro i j hij
      fin_cases i
      fin_cases j
      exact (lt_irrefl _ hij).elim
    · -- The first stage consists of the singleton unit vector `x 0`.
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i
      fin_cases j
      simp [hx_norm 0]
    · -- The singleton stage has zero approximation error.
      intro i
      fin_cases i
      simpa [ε] using (show (0 : ℝ) ≤ ε 0 from le_of_lt (hε_pos 0))
  let states : ∀ n, AlmostOrthonormalState x ε n :=
    fun n ↦
      Nat.rec hbase
        (fun n s ↦
          Classical.choose <|
            extend_almost_orthonormal_state x hx hx_norm s (hε_pos (n + 1))
              (hε_small (n + 1)))
        n
  have hstates_prefix :
      ∀ n,
        (∀ i : Fin (n + 1), (states (n + 1)).k i.castSucc = (states n).k i) ∧
        (∀ i : Fin (n + 1), (states (n + 1)).y i.castSucc = (states n).y i) := by
    intro n
    simpa [states] using
      (Classical.choose_spec <|
        extend_almost_orthonormal_state x hx hx_norm (states n) (hε_pos (n + 1))
          (hε_small (n + 1)))
  let subseq : ℕ → ℕ := fun n ↦ (states n).k (Fin.last n)
  let orthSeq : ℕ → H := fun n ↦ (states n).y (Fin.last n)
  have hstate_value :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (states n).y ⟨m, Nat.lt_succ_of_le hmn⟩ = orthSeq m := by
    intro m n hmn
    induction n with
    | zero =>
        have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
        subst hm
        simp [orthSeq]
    | succ n ihn =>
        by_cases hmn_eq : m = n + 1
        · subst hmn_eq
          have hlast :
              (⟨n + 1, Nat.lt_succ_of_le hmn⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
            ext
            rfl
          simp [orthSeq, hlast]
        · have hmn' : m ≤ n := by
            exact Nat.le_of_lt_succ (lt_of_le_of_ne hmn hmn_eq)
          have hpref := (hstates_prefix n).2
          calc
            (states (n + 1)).y ⟨m, Nat.lt_succ_of_le hmn⟩
                = (states n).y ⟨m, Nat.lt_succ_of_le hmn'⟩ := by
                    have hindex :
                        (⟨m, Nat.lt_succ_of_le hmn⟩ : Fin (n + 2)) =
                          (⟨m, Nat.lt_succ_of_le hmn'⟩ : Fin (n + 1)).castSucc := by
                      ext
                      rfl
                    rw [hindex]
                    exact hpref _
            _ = orthSeq m := ihn hmn'
  have hsubseq_strict : StrictMono subseq := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    have hlast :
        (states (n + 1)).k (Fin.castSucc (Fin.last n)) < (states (n + 1)).k (Fin.last (n + 1)) :=
      (states (n + 1)).strictMono_k (by simpa using (Fin.castSucc_lt_last (Fin.last n)))
    simpa [subseq, (hstates_prefix n).1 (Fin.last n)] using hlast
  have horthSeq : Orthonormal ℝ orthSeq := by
    constructor
    · intro n
      simpa [orthSeq] using (states n).orthonormal_y.norm_eq_one (Fin.last n)
    · intro i j hij
      rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
      · have hi_state :
            orthSeq i = (states j).y ⟨i, Nat.lt_succ_of_lt hij_lt⟩ := by
          symm
          exact hstate_value (Nat.le_of_lt hij_lt)
        calc
          inner ℝ (orthSeq i) (orthSeq j)
              = inner ℝ ((states j).y ⟨i, Nat.lt_succ_of_lt hij_lt⟩)
                  ((states j).y (Fin.last j)) := by
                    simp [orthSeq, hi_state]
          _ = 0 := by
            apply (states j).orthonormal_y.inner_eq_zero
            exact Fin.ne_of_lt (by simpa using hij_lt)
      · have hj_state :
            orthSeq j = (states i).y ⟨j, Nat.lt_succ_of_lt hij_gt⟩ := by
          symm
          exact hstate_value (Nat.le_of_lt hij_gt)
        calc
          inner ℝ (orthSeq i) (orthSeq j)
              = inner ℝ (orthSeq j) (orthSeq i) := by rw [real_inner_comm]
          _ = inner ℝ ((states i).y ⟨j, Nat.lt_succ_of_lt hij_gt⟩)
                ((states i).y (Fin.last i)) := by
                  simp [orthSeq, hj_state]
          _ = 0 := by
            apply (states i).orthonormal_y.inner_eq_zero
            exact Fin.ne_of_lt (by simpa using hij_gt)
  have hclose : ∀ n, ‖x (subseq n) - orthSeq n‖ ≤ ε n := by
    intro n
    simpa [subseq, orthSeq] using (states n).close (Fin.last n)
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 4) atTop atTop :=
      tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
    simpa [ε] using tendsto_inv_atTop_zero.comp hshift
  refine ⟨subseq, orthSeq, hsubseq_strict, horthSeq, ?_⟩
  -- The stagewise error bounds are dominated by the explicit sequence `ε n → 0`.
  exact squeeze_zero_norm hclose hε_tendsto
