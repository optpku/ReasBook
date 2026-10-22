/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Filter
open scoped BigOperators

section Chap01
section Section05

/-- The partial sum `D n` of the decimal expansion determined by `digits`. -/
noncomputable def decimalPrefix (digits : ℕ → Fin 10) (n : ℕ) : ℝ :=
  (Finset.range n).sum fun i => (digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1)

/-- The decimal digits `digits` approximate `x` with the bounds `D n ≤ x ≤ D n + 1/10^n`. -/
def decimalBounds (digits : ℕ → Fin 10) (x : ℝ) : Prop :=
  ∀ n : ℕ, decimalPrefix digits n ≤ x ∧ x ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n

/-- The decimal digits `digits` approximate `x` with strict lower bounds `D n < x`
and start with a leading `0` digit. -/
def decimalBoundsStrict (digits : ℕ → Fin 10) (x : ℝ) : Prop :=
  digits 0 = 0 ∧
    ∀ n : ℕ, decimalPrefix digits n < x ∧ x ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n

/-- Expanding one more digit in the decimal prefix. -/
lemma decimalPrefix_succ (digits : ℕ → Fin 10) (n : ℕ) :
    decimalPrefix digits (n + 1) =
      decimalPrefix digits n + (digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1) := by
  unfold decimalPrefix
  simp [Finset.sum_range_succ, add_comm]

lemma decimalPrefix_nonneg (digits : ℕ → Fin 10) (n : ℕ) :
    0 ≤ decimalPrefix digits n := by
  classical
  unfold decimalPrefix
  have hterm_nonneg :
      ∀ i, 0 ≤ (digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1) := by
    intro i
    have hdig : 0 ≤ (digits (i + 1) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hpow : 0 < (10 : ℝ) ^ (i + 1) := pow_pos (by norm_num) _
    exact div_nonneg hdig (le_of_lt hpow)
  exact Finset.sum_nonneg (by
    intro i hi
    exact hterm_nonneg i)

lemma decimalPrefix_le_succ (digits : ℕ → Fin 10) (n : ℕ) :
    decimalPrefix digits n ≤ decimalPrefix digits (n + 1) := by
  have hterm_nonneg :
      0 ≤ (digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1) := by
    have hdig : 0 ≤ (digits (n + 1) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hpow : 0 < (10 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    exact div_nonneg hdig (le_of_lt hpow)
  have h := decimalPrefix_succ digits n
  linarith

lemma decimalPrefix_monotone (digits : ℕ → Fin 10) :
    Monotone (decimalPrefix digits) := by
  intro m n hmn
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  clear hmn
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep : decimalPrefix digits (m + k) ≤ decimalPrefix digits (m + k + 1) :=
        decimalPrefix_le_succ digits (m + k)
      have htrans : decimalPrefix digits m ≤ decimalPrefix digits (m + k + 1) :=
        le_trans ih hstep
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

/-- Bounding the tail of the decimal prefix by a geometric sum. -/
lemma decimalPrefix_tail_le (digits : ℕ → Fin 10) (n k : ℕ) :
    decimalPrefix digits (n + k) ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n := by
  classical
  -- Expand the tail of the prefix.
  have hdecomp :
      decimalPrefix digits (n + k) =
        decimalPrefix digits n +
          (Finset.range k).sum
            (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          decimalPrefix digits (n + k.succ)
              = decimalPrefix digits (n + k) +
                  (digits (n + k.succ) : ℝ) / (10 : ℝ) ^ (n + k.succ) := by
                    have := decimalPrefix_succ digits (n + k)
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
          _ =
              decimalPrefix digits n +
                (Finset.range k).sum
                    (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) +
                (digits (n + k.succ) : ℝ) / (10 : ℝ) ^ (n + k.succ) := by
                    simp [ih, add_comm, add_left_comm]
          _ =
              decimalPrefix digits n +
                (Finset.range (k + 1)).sum
                    (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) := by
                    simp [Finset.sum_range_succ, add_comm, add_left_comm]
  have hdigit_le_nine : ∀ i, (digits (n + 1 + i) : ℝ) ≤ 9 := by
    intro i
    have hlt : (digits (n + 1 + i)).val < 10 := (digits (n + 1 + i)).is_lt
    have hle : (digits (n + 1 + i)).val ≤ 9 := Nat.lt_succ_iff.mp hlt
    exact_mod_cast hle
  have htail_le :
      (Finset.range k).sum
          (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) ≤
        (Finset.range k).sum
          (fun i => 9 / (10 : ℝ) ^ (n + 1 + i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hden_pos : 0 < (10 : ℝ) ^ (n + 1 + i) := pow_pos (by norm_num) _
    have hden_nonneg : 0 ≤ (10 : ℝ) ^ (n + 1 + i) := le_of_lt hden_pos
    have hd := hdigit_le_nine i
    have : (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i) ≤
        9 / (10 : ℝ) ^ (n + 1 + i) :=
      div_le_div_of_nonneg_right hd hden_nonneg
    simpa using this
  -- Compare the geometric majorant with its infinite sum.
  have hgeom_summable : Summable (fun i : ℕ => (1 / (10 : ℝ)) ^ i) :=
    summable_geometric_of_abs_lt_one (by norm_num : |(1 / (10 : ℝ))| < 1)
  have hgeom_tsum : ∑' i : ℕ, (1 / (10 : ℝ)) ^ i = (10 / 9 : ℝ) := by
    have htsum := tsum_geometric_of_abs_lt_one (by norm_num : |(1 / (10 : ℝ))| < 1)
    have htsum' : ∑' i : ℕ, (1 / (10 : ℝ)) ^ i = (1 - (1 / 10 : ℝ))⁻¹ := htsum
    norm_num [one_div] at htsum'
    exact htsum'
  have hgeom_bound :
      (Finset.range k).sum (fun i => (1 / (10 : ℝ)) ^ i) ≤ (10 / 9 : ℝ) :=
    by
      have h :=
        Summable.sum_le_tsum (s := Finset.range k)
          (f := fun i => (1 / (10 : ℝ)) ^ i)
          (by
            intro i hi
            positivity)
          hgeom_summable
      have htsum := hgeom_tsum
      have h' :
          (Finset.range k).sum (fun i => (1 / (10 : ℝ)) ^ i) ≤ (10 / 9 : ℝ) := by
        linarith
      exact h'
  have hgeom_factor :
      (Finset.range k).sum (fun i => 9 / (10 : ℝ) ^ (n + 1 + i)) =
        9 / (10 : ℝ) ^ (n + 1) *
          (Finset.range k).sum (fun i => (1 / (10 : ℝ)) ^ i) := by
    calc
      (Finset.range k).sum (fun i => 9 / (10 : ℝ) ^ (n + 1 + i))
          = (Finset.range k).sum
              (fun i => 9 / (10 : ℝ) ^ (n + 1) * (1 / (10 : ℝ)) ^ i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [pow_add, div_eq_mul_inv, mul_assoc, mul_comm]
      _ =
          9 / (10 : ℝ) ^ (n + 1) *
            (Finset.range k).sum (fun i => (1 / (10 : ℝ)) ^ i) := by
                simp [Finset.mul_sum]
  have hgeom_le :
      (Finset.range k).sum
          (fun i => 9 / (10 : ℝ) ^ (n + 1 + i)) ≤
        (9 / (10 : ℝ) ^ (n + 1)) * (10 / 9 : ℝ) := by
    have hconst_nonneg : 0 ≤ 9 / (10 : ℝ) ^ (n + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hgeom_bound hconst_nonneg
    simpa [hgeom_factor] using this
  have hgeom_le' :
      (Finset.range k).sum
          (fun i => 9 / (10 : ℝ) ^ (n + 1 + i)) ≤
        1 / (10 : ℝ) ^ n := by
    have hrewrite : (9 / (10 : ℝ) ^ (n + 1)) * (10 / 9 : ℝ) = 1 / (10 : ℝ) ^ n := by
      ring_nf
    have hbound : (9 / (10 : ℝ) ^ (n + 1)) * (10 / 9 : ℝ) ≤ 1 / (10 : ℝ) ^ n := by
      simp [hrewrite]
    exact hgeom_le.trans hbound
  have htail_bound :
      (Finset.range k).sum
          (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) ≤
        1 / (10 : ℝ) ^ n := by
    calc
      (Finset.range k).sum
          (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i))
          ≤ (Finset.range k).sum
              (fun i => 9 / (10 : ℝ) ^ (n + 1 + i)) := htail_le
      _ ≤ 1 / (10 : ℝ) ^ n := hgeom_le'
  -- Combine the decomposition with the tail bound.
  calc
    decimalPrefix digits (n + k)
        = decimalPrefix digits n +
            (Finset.range k).sum
              (fun i => (digits (n + 1 + i) : ℝ) / (10 : ℝ) ^ (n + 1 + i)) := hdecomp
    _ ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n := by
          have := htail_bound
          linarith

/-- Each decimal prefix is bounded above by `1`. -/
lemma decimalPrefix_le_one (digits : ℕ → Fin 10) (n : ℕ) :
    decimalPrefix digits n ≤ 1 := by
  have h := decimalPrefix_tail_le digits 0 n
  simp [decimalPrefix] at h
  exact h

/-- A global bound on any prefix in terms of the `n`-th prefix. -/
lemma decimalPrefix_le_prefix_add (digits : ℕ → Fin 10) (n m : ℕ) :
    decimalPrefix digits m ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n := by
  classical
  rcases le_total m n with hmn | hnm
  · have hmono := decimalPrefix_monotone digits hmn
    have hpos : 0 ≤ 1 / (10 : ℝ) ^ n := by
      have hpow : 0 ≤ (10 : ℝ) ^ n := pow_nonneg (by norm_num) _
      exact one_div_nonneg.mpr hpow
    have hle : decimalPrefix digits n ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n :=
      le_add_of_nonneg_right hpos
    exact le_trans hmono hle
  · rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
    have htail := decimalPrefix_tail_le digits n k
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail

/-- Powers `1/10^n` can be made arbitrarily small. -/
lemma one_div_pow_ten_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 1 / (10 : ℝ) ^ n < ε := by
  have hlimit :
      Tendsto (fun n : ℕ => (1 / (10 : ℝ)) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / (10 : ℝ))| < 1)
  have hsmall := (tendsto_order.1 hlimit).2 ε hε
  rcases (eventually_atTop.1 hsmall) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hN' := hN N le_rfl
  -- `((1/10)^N) = 1 / 10^N`.
  simpa [one_div, inv_pow] using hN'

/-- Using the supremum of decimal prefixes gives an `x` satisfying the decimal bounds. -/
lemma exists_sup_decimalBounds (digits : ℕ → Fin 10) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, decimalBounds digits x := by
  classical
  let S : Set ℝ := Set.range (decimalPrefix digits)
  have hnonempty : S.Nonempty := ⟨decimalPrefix digits 0, ⟨0, rfl⟩⟩
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨m, rfl⟩
    exact decimalPrefix_le_one digits m
  let x := sSup S
  have hx_nonneg : 0 ≤ x := by
    have hx := le_csSup hbounded (by exact ⟨0, rfl⟩)
    simpa [x, decimalPrefix] using hx
  have hx_le_one : x ≤ 1 := by
    have hx := csSup_le hnonempty (by
      intro y hy
      rcases hy with ⟨m, rfl⟩
      exact decimalPrefix_le_one digits m)
    simpa [x] using hx
  refine ⟨x, ⟨hx_nonneg, hx_le_one⟩, ?_⟩
  intro n
  constructor
  · exact le_csSup hbounded ⟨n, rfl⟩
  · have hbound :=
      csSup_le hnonempty (by
        intro y hy
        rcases hy with ⟨m, rfl⟩
        exact decimalPrefix_le_prefix_add digits n m)
    simpa [x] using hbound

/-- The value determined by a given digit stream satisfying decimal bounds is unique. -/
lemma decimalBounds_value_unique (digits : ℕ → Fin 10) {x y : ℝ}
    (hx : decimalBounds digits x) (hy : decimalBounds digits y) : x = y := by
  classical
  by_contra hxy
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨n, hn⟩ := one_div_pow_ten_lt hpos
  have hx' := hx n
  have hy' := hy n
  have hle1 : x - y ≤ 1 / (10 : ℝ) ^ n := by linarith
  have hle2 : y - x ≤ 1 / (10 : ℝ) ^ n := by linarith
  have hge : -(1 / (10 : ℝ) ^ n) ≤ x - y := by linarith
  have habs : |x - y| ≤ 1 / (10 : ℝ) ^ n := by
    exact abs_le.mpr ⟨hge, hle1⟩
  have hcontr : |x - y| < |x - y| := lt_of_le_of_lt habs hn
  exact lt_irrefl _ hcontr

lemma decimalBounds_strict_of_pos_digits {digits : ℕ → Fin 10} {x : ℝ}
    (hzero : digits 0 = 0) (hpos : ∀ n, 0 < (digits (n + 1) : ℝ))
    (h : decimalBounds digits x) : decimalBoundsStrict digits x := by
  refine ⟨hzero, ?_⟩
  intro n
  have hsucc := decimalPrefix_succ digits n
  have hpow_pos : 0 < (10 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hterm_pos : 0 < (digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1) :=
    div_pos (hpos n) hpow_pos
  have hlt_prefix :
      decimalPrefix digits n < decimalPrefix digits (n + 1) := by
    have hrewrite := hsucc
    linarith
  have hx_ge : decimalPrefix digits (n + 1) ≤ x := (h (n + 1)).1
  have hx_lt : decimalPrefix digits n < x := lt_of_lt_of_le hlt_prefix hx_ge
  exact ⟨hx_lt, (h n).2⟩

lemma diagonal_digits_value (digits : ℕ → Fin 10)
    (hzero : digits 0 = 0) (hpos : ∀ n, 0 < (digits (n + 1) : ℝ)) :
    ∃! y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 ∧ decimalBoundsStrict digits y := by
  classical
  rcases exists_sup_decimalBounds digits with ⟨x, hxIcc, hxbounds⟩
  have hxstrict : decimalBoundsStrict digits x :=
    decimalBounds_strict_of_pos_digits hzero hpos hxbounds
  refine ⟨x, ⟨hxIcc, hxstrict⟩, ?_⟩
  intro y hy
  have hdec_y : decimalBounds digits y := by
    intro n
    have hstrict := hy.2.2 n
    exact ⟨le_of_lt hstrict.1, hstrict.2⟩
  have hdec_x : decimalBounds digits x := hxbounds
  have hy_eq : y = x :=
    decimalBounds_value_unique (digits := digits) (x := y) (y := x) hdec_y hdec_x
  simp [hy_eq]

lemma exists_digits_decimalBoundsStrict {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ digits : ℕ → Fin 10, decimalBoundsStrict digits x := by
  classical
  -- Updating a digit beyond the `n`-th place does not change the first `n` prefixes.
  have decimalPrefix_update (digits : ℕ → Fin 10) (d : Fin 10) (n : ℕ) :
      decimalPrefix (Function.update digits (n + 1) d) n =
        decimalPrefix digits n := by
    unfold decimalPrefix
    -- All indices in the range `0..n-1` are different from `n+1`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hne : i ≠ n := ne_of_lt hi_lt
    simp [Function.update, hne]
  -- One greedy step: extend `n` digits satisfying the strict bounds by one more digit.
  have extend_digits :
      ∀ (digits : ℕ → Fin 10) (n : ℕ),
          decimalPrefix digits n < x ∧ x ≤ decimalPrefix digits n + 1 / (10 : ℝ) ^ n →
            ∃ dnext : Fin 10,
              decimalPrefix (Function.update digits (n + 1) dnext) (n + 1) < x ∧
                x ≤
                  decimalPrefix (Function.update digits (n + 1) dnext) (n + 1) +
                    1 / (10 : ℝ) ^ (n + 1) := by
    intro digits n hbound
    -- Let `y = (x - D_n) * 10^{n+1}`.
    set y : ℝ := (x - decimalPrefix digits n) * (10 : ℝ) ^ (n + 1)
    have hpos_pow : 0 < (10 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    have hpos : 0 < y := by
      have hx_gt : 0 < x - decimalPrefix digits n := by linarith
      have hy : 0 < (10 : ℝ) ^ (n + 1) := hpos_pow
      nlinarith
    have hy_le : y ≤ 10 := by
      have hx_upper : x - decimalPrefix digits n ≤ 1 / (10 : ℝ) ^ n := by linarith
      have hmul :
          y ≤ (1 / (10 : ℝ) ^ n) * (10 : ℝ) ^ (n + 1) := by
        have hmul' := mul_le_mul_of_nonneg_right hx_upper (le_of_lt hpos_pow)
        simpa [y, mul_comm, mul_left_comm, mul_assoc] using hmul'
      have hpow_ne : (10 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have hpow_simpl :
          (1 / (10 : ℝ) ^ n) * (10 : ℝ) ^ (n + 1) = (10 : ℝ) := by
        field_simp [hpow_ne]
        ring
      linarith
    -- Choose the least natural `j` with `y ≤ j`.
    let hnonempty : ∃ j : ℕ, y ≤ (j : ℝ) := ⟨10, by simpa using hy_le⟩
    let j : ℕ := Nat.find hnonempty
    have hj_spec : y ≤ (j : ℝ) := Nat.find_spec hnonempty
    have hj_le_ten : j ≤ 10 := Nat.find_min' hnonempty hy_le
    have hj_ne_zero : j ≠ 0 := by
      have : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le hpos hj_spec
      exact Nat.ne_of_gt (by exact_mod_cast this)
    have hj_pos : 0 < j := Nat.pos_of_ne_zero hj_ne_zero
    -- Define the next digit.
    let digitNat : ℕ := j - 1
    have hj_pred_lt : (digitNat : ℝ) < y := by
      -- If `y ≤ j-1`, minimality of `j` would force `j ≤ j-1`.
      have hmin : ∀ k : ℕ, y ≤ (k : ℝ) → j ≤ k := fun k hk =>
        Nat.find_min' hnonempty hk
      by_contra hle
      have hle' : y ≤ (digitNat : ℝ) := le_of_not_gt hle
      have hcontr : j ≤ digitNat := hmin digitNat hle'
      have hlt : digitNat < j := by
        have := Nat.pred_lt hj_ne_zero
        simpa [digitNat] using this
      have hlt' : digitNat < digitNat := lt_of_lt_of_le hlt hcontr
      exact (lt_irrefl _ hlt').elim
    have hdigit_lt : digitNat < 10 := by
      have hlt : digitNat < j := by
        simpa [digitNat] using (Nat.pred_lt hj_ne_zero)
      exact lt_of_lt_of_le hlt hj_le_ten
    let dnext : Fin 10 := ⟨digitNat, hdigit_lt⟩
    -- Compute the new prefix.
    have hprefix_eq :
        decimalPrefix (Function.update digits (n + 1) dnext) n =
          decimalPrefix digits n := decimalPrefix_update digits dnext n
    have hsucc :
        decimalPrefix (Function.update digits (n + 1) dnext) (n + 1) =
          decimalPrefix digits n + (dnext : ℝ) / (10 : ℝ) ^ (n + 1) := by
      simp [decimalPrefix_succ, hprefix_eq, Function.update]
    -- Establish the strict bounds for the extended prefix.
    refine ⟨dnext, ?_, ?_⟩
    · have hlt :
          (dnext : ℝ) / (10 : ℝ) ^ (n + 1) <
            (x - decimalPrefix digits n) := by
        have : (digitNat : ℝ) < y := by simpa [digitNat] using hj_pred_lt
        have hdiv :
            (digitNat : ℝ) / (10 : ℝ) ^ (n + 1) <
              y / (10 : ℝ) ^ (n + 1) := by
          have hpos_den : 0 < (10 : ℝ) ^ (n + 1) := hpos_pow
          exact div_lt_div_of_pos_right this hpos_den
        have hy_def : y / (10 : ℝ) ^ (n + 1) = x - decimalPrefix digits n := by
          have hpow_ne : (10 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          field_simp [y, hpow_ne]
          ring
        have hdigit_cast : (dnext : ℝ) = (digitNat : ℝ) := rfl
        simpa [hy_def, hdigit_cast] using hdiv
      have hD : decimalPrefix digits n < x := hbound.1
      have hD' : decimalPrefix digits n + (dnext : ℝ) / (10 : ℝ) ^ (n + 1) < x := by
        linarith
      simpa [hsucc]
    · have hle :
          (x - decimalPrefix digits n) ≤ (j : ℝ) / (10 : ℝ) ^ (n + 1) := by
        have hdiv := div_le_div_of_nonneg_right hj_spec (le_of_lt hpos_pow)
        have hy_def : y / (10 : ℝ) ^ (n + 1) = x - decimalPrefix digits n := by
          have hpow_ne : (10 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          field_simp [y, hpow_ne]
          ring
        simpa [hy_def] using hdiv
      have hdigit_cast : (dnext : ℝ) = (digitNat : ℝ) := rfl
      have hle' :
          x ≤ decimalPrefix digits n +
              (digitNat : ℝ) / (10 : ℝ) ^ (n + 1) + 1 / (10 : ℝ) ^ (n + 1) := by
        have hj_nat : j = digitNat + 1 := by
          have h := Nat.succ_pred_eq_of_pos hj_pos
          -- `digitNat = Nat.pred j`.
          have hpred : Nat.pred j = digitNat := by
            simp [digitNat, Nat.pred_eq_sub_one]
          have h' : digitNat.succ = j := by simpa [hpred] using h
          simpa [Nat.succ_eq_add_one] using h'.symm
        have hj_eq : (j : ℝ) = (digitNat : ℝ) + 1 := by exact_mod_cast hj_nat
        have hj_le' : (j : ℝ) / (10 : ℝ) ^ (n + 1) =
            (digitNat : ℝ) / (10 : ℝ) ^ (n + 1) + 1 / (10 : ℝ) ^ (n + 1) := by
          have hpow_ne : (10 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          calc
            (j : ℝ) / (10 : ℝ) ^ (n + 1)
                = ((digitNat : ℝ) + 1) / (10 : ℝ) ^ (n + 1) := by
                    simp [hj_eq, add_comm]
            _ =
                (digitNat : ℝ) / (10 : ℝ) ^ (n + 1) + 1 / (10 : ℝ) ^ (n + 1) := by
              field_simp [hpow_ne]
        linarith
      have hprefix :
          x ≤ decimalPrefix (Function.update digits (n + 1) dnext) (n + 1) +
              1 / (10 : ℝ) ^ (n + 1) := by
        have hsucc' :
            decimalPrefix (Function.update digits (n + 1) dnext) (n + 1) =
              decimalPrefix digits n + (digitNat : ℝ) / (10 : ℝ) ^ (n + 1) := by
          simp [hsucc, hdigit_cast]
        linarith
        -- This is the desired upper bound.
      exact hprefix
  classical
  choose extendDigit hExtendDigit using extend_digits
  -- Build an infinite sequence of digits by recursion.
  let approx :
      ∀ n : ℕ,
        {d : ℕ → Fin 10 //
          decimalPrefix d n < x ∧ x ≤ decimalPrefix d n + 1 / (10 : ℝ) ^ n} :=
    Nat.rec
      (⟨fun _ => 0, by simpa [decimalPrefix] using hx⟩)
      (fun n prev =>
        let d := prev.1
        let hd := prev.2
        ⟨Function.update d (n + 1) (extendDigit d n hd),
          hExtendDigit d n hd⟩)
  -- Stability: later updates do not change earlier digits.
  have approx_agree :
      ∀ {m n : ℕ}, m ≤ n → (approx n).1 m = (approx m).1 m := by
    intro m n hmn
    induction n generalizing m with
    | zero =>
        have hm : m = 0 := le_antisymm hmn (Nat.zero_le _)
        subst hm
        simp [approx]
    | succ n ih =>
        by_cases hm : m = n.succ
        · subst hm; simp [approx]
        · have hle : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hmn hm)
          have ih' := ih hle
          -- Use the recursive definition of `approx` at `n.succ`.
          have hupdate :
              (approx n.succ).1 m = (approx n).1 m := by
            simp [approx, hm]
          simpa [hupdate] using ih'
  -- Final digit stream.
  let digits : ℕ → Fin 10 := fun n => (approx n).1 n
  -- The prefixes of `digits` coincide with the constructed approximations.
  have digits_prefix :
      ∀ n : ℕ, decimalPrefix digits n = decimalPrefix (approx n).1 n := by
    intro n
    unfold decimalPrefix digits
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hle : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hagree := approx_agree hle
    -- Replace the digit at position `i+1`.
    simp [hagree.symm] 
  -- Finally, the strict decimal bounds follow from the construction.
  refine ⟨digits, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The leading digit is `0` by construction.
    simp [digits, approx]
  · intro n
    have hbound := (approx n).2
    have hprefix := digits_prefix n
    simpa [hprefix] using hbound

lemma decimalBoundsStrict_digits_unique {x : ℝ} {digits₁ digits₂ : ℕ → Fin 10}
    (h₁ : decimalBoundsStrict digits₁ x) (h₂ : decimalBoundsStrict digits₂ x) :
    digits₁ = digits₂ := by
  classical
  -- Agreement on the leading digit.
  have hzero : digits₁ 0 = digits₂ 0 := by
    have h₁' := h₁.1
    have h₂' := h₂.1
    simp [h₁', h₂']
  -- Helper: if the first `k` digits coincide, the `k`-th prefix coincides.
  have prefix_eq :
      ∀ k,
        (∀ i < k, digits₁ (i + 1) = digits₂ (i + 1)) →
          decimalPrefix digits₁ k = decimalPrefix digits₂ k := by
    intro k hdig
    unfold decimalPrefix
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have h := hdig i hi_lt
    simp [h]
  -- One-step digit comparison using the strict bounds.
  have digit_step :
      ∀ k,
        (∀ i < k, digits₁ (i + 1) = digits₂ (i + 1)) →
          digits₁ (k + 1) = digits₂ (k + 1) := by
    intro k hdig
    have hprefix_eq : decimalPrefix digits₁ k = decimalPrefix digits₂ k :=
      prefix_eq k hdig
    have h₁k := h₁.2 (k + 1)
    have h₂k := h₂.2 (k + 1)
    have hpow_pos : 0 < (10 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
    set D : ℝ := decimalPrefix digits₁ k
    have hD₂ : decimalPrefix digits₂ k = D := by simpa [D] using hprefix_eq.symm
    -- Lower and upper bounds for `(x - D) * 10^{k+1}` coming from `digits₁`.
    have h₁_lower :
        (digits₁ (k + 1) : ℝ) <
          (x - D) * (10 : ℝ) ^ (k + 1) := by
      have hsucc := decimalPrefix_succ digits₁ k
      have hx : decimalPrefix digits₁ (k + 1) < x := h₁k.1
      have hineq' :
          D + (digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) < x := by
        simpa [hsucc, D] using hx
      have hineq :
          (digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) < x - D := by
        linarith
      have hmul := mul_lt_mul_of_pos_right hineq hpow_pos
      have hpow_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hpow_pos
      have hcancel :
          (digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) * (10 : ℝ) ^ (k + 1) =
            (digits₁ (k + 1) : ℝ) := by field_simp [hpow_ne]
      simpa [D, hcancel, mul_comm, mul_left_comm, mul_assoc] using hmul
    have h₁_upper :
        (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₁ (k + 1) : ℝ) + 1 := by
      have hsucc := decimalPrefix_succ digits₁ k
      have hx : x ≤ decimalPrefix digits₁ (k + 1) + 1 / (10 : ℝ) ^ (k + 1) := h₁k.2
      have hineq :
          x - D ≤
            (digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1) := by
        have hineq' :
            x ≤ D + (digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1) := by
          simpa [hsucc, D] using hx
        linarith
      have hmul := mul_le_mul_of_nonneg_right hineq (le_of_lt hpow_pos)
      have hpow_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hpow_pos
      have hrewrite :
          ((digits₁ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1)) *
            (10 : ℝ) ^ (k + 1) =
              (digits₁ (k + 1) : ℝ) + 1 := by
        field_simp [hpow_ne]
      have hmul' : (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₁ (k + 1) : ℝ) + 1 := by
        nlinarith [hmul, hrewrite]
      simpa [D] using hmul'
    -- Bounds coming from `digits₂`.
    have h₂_lower :
        (digits₂ (k + 1) : ℝ) <
          (x - D) * (10 : ℝ) ^ (k + 1) := by
      have hsucc := decimalPrefix_succ digits₂ k
      have hx : decimalPrefix digits₂ (k + 1) < x := h₂k.1
      have hineq' :
          decimalPrefix digits₂ k +
              (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) < x := by
        simpa [hsucc] using hx
      have hineq :
          (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) < x - decimalPrefix digits₂ k := by
        linarith
      have hineq'' : (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) < x - D := by
        simpa [hD₂] using hineq
      have hmul := mul_lt_mul_of_pos_right hineq'' hpow_pos
      have hpow_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hpow_pos
      have hcancel :
          (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) * (10 : ℝ) ^ (k + 1) =
            (digits₂ (k + 1) : ℝ) := by field_simp [hpow_ne]
      simpa [D, hcancel, mul_comm, mul_left_comm, mul_assoc] using hmul
    have h₂_upper :
        (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₂ (k + 1) : ℝ) + 1 := by
      have hsucc := decimalPrefix_succ digits₂ k
      have hx : x ≤ decimalPrefix digits₂ (k + 1) + 1 / (10 : ℝ) ^ (k + 1) := h₂k.2
      have hineq :
          x - decimalPrefix digits₂ k ≤
            (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1) := by
        have hineq' :
            x ≤ decimalPrefix digits₂ k +
              (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1) := by
          simpa [hsucc] using hx
        linarith
      have hineq' : x - D ≤
          (digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
            1 / (10 : ℝ) ^ (k + 1) := by simpa [hD₂] using hineq
      have hmul := mul_le_mul_of_nonneg_right hineq' (le_of_lt hpow_pos)
      have hpow_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hpow_pos
      have hrewrite :
          ((digits₂ (k + 1) : ℝ) / (10 : ℝ) ^ (k + 1) +
              1 / (10 : ℝ) ^ (k + 1)) *
            (10 : ℝ) ^ (k + 1) =
              (digits₂ (k + 1) : ℝ) + 1 := by
        field_simp [hpow_ne]
      have hmul' : (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₂ (k + 1) : ℝ) + 1 := by
        nlinarith [hmul, hrewrite]
      simpa [D] using hmul'
    -- Compare the integer parts of the shared interval.
    have hle12 : (digits₁ (k + 1)).val ≤ (digits₂ (k + 1)).val := by
      by_contra hlt
      have hlt' : (digits₂ (k + 1)).val < (digits₁ (k + 1)).val := Nat.lt_of_not_ge hlt
      have hle' :
          (digits₂ (k + 1) : ℝ) + 1 ≤ (digits₁ (k + 1) : ℝ) := by
        have hsucc_le : (digits₂ (k + 1)).val + 1 ≤ (digits₁ (k + 1)).val :=
          Nat.succ_le_of_lt hlt'
        exact_mod_cast hsucc_le
      have hle'' : (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₁ (k + 1) : ℝ) :=
        le_trans h₂_upper hle'
      have hcontr : (digits₁ (k + 1) : ℝ) < (digits₁ (k + 1) : ℝ) :=
        lt_of_lt_of_le h₁_lower hle''
      exact (lt_irrefl _ hcontr).elim
    have hle21 : (digits₂ (k + 1)).val ≤ (digits₁ (k + 1)).val := by
      by_contra hlt
      have hlt' : (digits₁ (k + 1)).val < (digits₂ (k + 1)).val := Nat.lt_of_not_ge hlt
      have hle' :
          (digits₁ (k + 1) : ℝ) + 1 ≤ (digits₂ (k + 1) : ℝ) := by
        have hsucc_le : (digits₁ (k + 1)).val + 1 ≤ (digits₂ (k + 1)).val :=
          Nat.succ_le_of_lt hlt'
        exact_mod_cast hsucc_le
      have hle'' : (x - D) * (10 : ℝ) ^ (k + 1) ≤ (digits₂ (k + 1) : ℝ) :=
        le_trans h₁_upper hle'
      have hcontr : (digits₂ (k + 1) : ℝ) < (digits₂ (k + 1) : ℝ) :=
        lt_of_lt_of_le h₂_lower hle''
      exact (lt_irrefl _ hcontr).elim
    have hval_eq : (digits₁ (k + 1)).val = (digits₂ (k + 1)).val :=
      le_antisymm hle12 hle21
    exact Fin.ext (by simpa using hval_eq)
  -- Strong induction on the digit position.
  have hdigit_all : ∀ k, ∀ i ≤ k, digits₁ (i + 1) = digits₂ (i + 1) := by
    refine Nat.rec ?base ?step
    · intro i hi
      have hi0 : i = 0 := le_antisymm hi (Nat.zero_le _)
      subst hi0
      have hdig : ∀ j < 0, digits₁ (j + 1) = digits₂ (j + 1) := by
        intro j hj
        have : False := (Nat.not_lt_zero _) hj
        exact this.elim
      simpa using digit_step 0 hdig
    · intro k ih i hi
      rcases lt_or_eq_of_le hi with hlt | hEq
      · -- Use the induction hypothesis for `i ≤ k`.
        have hle : i ≤ k := Nat.lt_succ_iff.mp hlt
        exact ih _ hle
      · -- The next digit follows from the step lemma.
        subst hEq
        have hdig : ∀ j < k + 1, digits₁ (j + 1) = digits₂ (j + 1) := by
          intro j hj
          exact ih j (Nat.lt_succ_iff.mp hj)
        simpa [Nat.succ_eq_add_one] using digit_step (k + 1) hdig
  -- Conclude by extensionality.
  funext n
  cases n with
  | zero => simpa using hzero
  | succ k =>
      have := hdigit_all k k le_rfl
      simpa [Nat.succ_eq_add_one] using this

/-- Proposition 1.5.1.
(i) Every infinite sequence of digits `0.d1d2d3…` represents a unique real number
`x ∈ [0, 1]` such that `D n ≤ x ≤ D n + 1/10^n` for all `n ∈ ℕ`, where `D n` is
the partial sum of the first `n` digits.
(ii) For every `x ∈ (0, 1]` there exists an infinite sequence of digits
representing `x`, and there is a unique representation satisfying
`D n < x ≤ D n + 1/10^n` for all `n ∈ ℕ`. -/
theorem decimal_expansion_properties :
    (∀ digits : ℕ → Fin 10, ∃! x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ decimalBounds digits x) ∧
      ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
        (∃ digits : ℕ → Fin 10, decimalBounds digits x) ∧
          ∃! digits : ℕ → Fin 10, decimalBoundsStrict digits x := by
  classical
  constructor
  · intro digits
    rcases exists_sup_decimalBounds digits with ⟨x, hxIcc, hxbounds⟩
    refine ⟨x, ?_, ?_⟩
    · exact ⟨hxIcc, hxbounds⟩
    · intro y hy
      exact decimalBounds_value_unique (digits := digits) (x := y) (y := x) hy.2 hxbounds
  · intro x hx
    -- Existence and uniqueness of a (strict) decimal expansion for `x`.
    rcases exists_digits_decimalBoundsStrict hx with ⟨digits, hdigits⟩
    have hdigits_nonstrict : decimalBounds digits x := by
      intro n
      have h := hdigits.2 n
      exact ⟨le_of_lt h.1, h.2⟩
    refine ⟨⟨digits, hdigits_nonstrict⟩, ?_⟩
    refine ⟨digits, hdigits, ?_⟩
    intro digits' h'
    exact decimalBoundsStrict_digits_unique h' hdigits

/-- Diagonal number built from an enumeration of `(0, 1]` differs from every entry. -/
lemma diagonal_not_in_enumeration (f : ℕ → Set.Ioc (0 : ℝ) 1) :
    ∃ y ∈ Set.Ioc (0 : ℝ) 1, ∀ n : ℕ, y ≠ (f n : ℝ) := by
  classical
  have hdigits :
      ∀ n, ∃ digits : ℕ → Fin 10,
        decimalBoundsStrict digits (f n : ℝ) := by
    intro n
    simpa using
      (exists_digits_decimalBoundsStrict (x := (f n : ℝ)) (hx := (f n).property))
  choose digits hdigits using hdigits
  -- Diagonal digit stream: differs from the `n`-th expansion at digit `n+1`.
  let diag : ℕ → Fin 10
    | 0 => 0
    | n + 1 => if h : digits n (n + 1) = 1 then (2 : Fin 10) else 1
  have hdiag_zero : diag 0 = 0 := rfl
  have hdiag_pos : ∀ n, 0 < (diag (n + 1) : ℝ) := by
    intro n
    dsimp [diag]
    split_ifs <;> norm_num
  rcases diagonal_digits_value (digits := diag) hdiag_zero hdiag_pos with
    ⟨y, ⟨hyIcc, hystrict⟩, huniq⟩
  have hy_pos : 0 < y := by
    have h := (hystrict.2 0).1
    simpa [decimalPrefix] using h
  have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy_pos, hyIcc.2⟩
  refine ⟨y, hyIoc, ?_⟩
  intro n
  have hneq_digit : diag (n + 1) ≠ digits n (n + 1) := by
    dsimp [diag]
    by_cases h : digits n (n + 1) = 1
    · simp [h]
    · simp [h, ne_comm]
  intro hy_eq
  have hdigits_n : decimalBoundsStrict (digits n) y := by simpa [hy_eq] using hdigits n
  have hdiag_eq : diag = digits n :=
    decimalBoundsStrict_digits_unique (x := y) hystrict hdigits_n
  exact hneq_digit (by simp [hdiag_eq])

/-- Theorem 1.5.2 (Cantor): The set `(0, 1]` is uncountable. -/
theorem cantor_uncountable_Ioc :
    ¬ Set.Countable (Set.Ioc (0 : ℝ) 1) := by
  intro hcount
  classical
  have hnonempty : (Set.Ioc (0 : ℝ) 1).Nonempty := ⟨1, by constructor <;> norm_num⟩
  obtain ⟨f, hf⟩ :=
    (Set.countable_iff_exists_surjective (s := Set.Ioc (0 : ℝ) 1) hnonempty).1 hcount
  rcases diagonal_not_in_enumeration (f := f) with ⟨y, hyIoc, hy_ne⟩
  rcases hf ⟨y, hyIoc⟩ with ⟨n, hfn⟩
  have hy_eq : (f n : ℝ) = y := by
    simpa using congrArg Subtype.val hfn
  exact hy_ne n hy_eq.symm

/-- Proposition 1.5.3: If a rational number `x ∈ (0, 1]` has decimal expansion
`0.d₁d₂d₃…`, then its digits eventually repeat, i.e., there exist positive
integers `N` and `P` such that `dₙ = dₙ₊ₚ` for all `n ≥ N`. -/
theorem rational_decimal_digits_eventually_periodic
    (x : ℚ) (digits : ℕ → Fin 10) (_hx : (x : ℝ) ∈ Set.Ioc (0 : ℝ) 1)
    (hx_digits : decimalBounds digits (x : ℝ)) :
    ∃ N P : ℕ, 0 < N ∧ 0 < P ∧ ∀ {n}, N ≤ n → digits n = digits (n + P) := by
  classical
  -- A convenient closed form for `10^n • D n`.
  have decimalPrefix_mul_pow (n : ℕ) :
      (10 : ℝ) ^ n * decimalPrefix digits n =
        (Finset.range n).sum
          (fun i => (digits (i + 1) : ℝ) * (10 : ℝ) ^ (n - (i + 1))) := by
    unfold decimalPrefix
    -- Pull the factor `(10^n)` inside the sum and cancel powers.
    have hpow_ne : (10 : ℝ) ≠ 0 := by norm_num
    have hpow_ne' : (10 : ℝ) ^ n ≠ 0 := pow_ne_zero _ hpow_ne
    calc
      (10 : ℝ) ^ n *
          (Finset.range n).sum (fun i => (digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1)) =
          (Finset.range n).sum
            (fun i => (10 : ℝ) ^ n * ((digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1))) := by
            simp [Finset.mul_sum]
      _ =
          (Finset.range n).sum
            (fun i => (digits (i + 1) : ℝ) * (10 : ℝ) ^ (n - (i + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hle : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
            have hpow :
                (10 : ℝ) ^ n = (10 : ℝ) ^ (n - (i + 1)) * (10 : ℝ) ^ (i + 1) := by
              have := pow_add (10 : ℝ) (n - (i + 1)) (i + 1)
              have hsum : n - (i + 1) + (i + 1) = n := Nat.sub_add_cancel hle
              simpa [hsum, mul_comm, mul_left_comm, mul_assoc] using this
            have hpow_ne'' : (10 : ℝ) ^ (i + 1) ≠ 0 := pow_ne_zero _ hpow_ne
            calc
              (10 : ℝ) ^ n * ((digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1))
                  = ((10 : ℝ) ^ (n - (i + 1)) * (10 : ℝ) ^ (i + 1)) *
                      ((digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1)) := by
                    simp [hpow]
              _ = (10 : ℝ) ^ (n - (i + 1)) *
                    ((10 : ℝ) ^ (i + 1) * ((digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1))) :=
                    by ring
              _ = (10 : ℝ) ^ (n - (i + 1)) * (digits (i + 1) : ℝ) := by
                    have hcancel :
                        (10 : ℝ) ^ (i + 1) * ((digits (i + 1) : ℝ) / (10 : ℝ) ^ (i + 1)) =
                          (digits (i + 1) : ℝ) := by
                      have hne : (10 : ℝ) ^ (i + 1) ≠ 0 := hpow_ne''
                      field_simp [hne]
                    simp [hcancel]
              _ = (digits (i + 1) : ℝ) * (10 : ℝ) ^ (n - (i + 1)) := by ring
  -- Denominator and basic positivity facts.
  let q : ℕ := x.den
  have hq_pos : 0 < q := x.den_pos
  -- Long-division remainders: `r n = q * 10^n * (x - D n)`.
  let r : ℕ → ℝ := fun n => (q : ℝ) * (10 : ℝ) ^ n * ((x : ℝ) - decimalPrefix digits n)
  have hr_bounds : ∀ n, r n ∈ Set.Icc (0 : ℝ) q := by
    intro n
    have hx' := hx_digits n
    have hpow_nonneg : 0 ≤ (10 : ℝ) ^ n :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ)) _
    have hmul_nonneg : 0 ≤ (q : ℝ) * (10 : ℝ) ^ n := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact mul_nonneg hq_nonneg hpow_nonneg
    constructor
    · -- Lower bound `0 ≤ r n`.
      have hx_lower : 0 ≤ (x : ℝ) - decimalPrefix digits n := sub_nonneg.mpr hx'.1
      have h := mul_nonneg hmul_nonneg hx_lower
      simpa [r] using h
    · -- Upper bound `r n ≤ q`.
      have hx_upper : (x : ℝ) - decimalPrefix digits n ≤ 1 / (10 : ℝ) ^ n := by linarith
      have h := mul_le_mul_of_nonneg_left hx_upper hmul_nonneg
      have hpow_ne : (10 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have : r n ≤ (q : ℝ) := by
        calc
          r n = (q : ℝ) * (10 : ℝ) ^ n * ((x : ℝ) - decimalPrefix digits n) := rfl
          _ ≤ (q : ℝ) * (10 : ℝ) ^ n * (1 / (10 : ℝ) ^ n) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using h
          _ = (q : ℝ) := by
            field_simp [hpow_ne]
      exact this
  -- Exact recursion on the remainders.
  have hr_rec :
      ∀ n, r (n + 1) = 10 * r n - (q : ℝ) * (digits (n + 1) : ℝ) := by
    intro n
    have hpow : (10 : ℝ) ^ (n + 1) = (10 : ℝ) * (10 : ℝ) ^ n := by
      simp [pow_succ, mul_comm]
    calc
      r (n + 1)
          = (q : ℝ) * (10 : ℝ) ^ (n + 1) *
              ((x : ℝ) - decimalPrefix digits (n + 1)) := rfl
      _ = (q : ℝ) * (10 : ℝ) ^ (n + 1) *
              ((x : ℝ) - (decimalPrefix digits n +
                (digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1))) := by
            simp [decimalPrefix_succ]
      _ =
          (q : ℝ) * (10 : ℝ) ^ (n + 1) * ((x : ℝ) - decimalPrefix digits n) -
            (q : ℝ) * (10 : ℝ) ^ (n + 1) *
              ((digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1)) := by
            ring
      _ = 10 * r n - (q : ℝ) * (digits (n + 1) : ℝ) := by
        have term1 :
            (q : ℝ) * (10 : ℝ) ^ (n + 1) * ((x : ℝ) - decimalPrefix digits n) =
              10 * r n := by
          calc
            (q : ℝ) * (10 : ℝ) ^ (n + 1) * ((x : ℝ) - decimalPrefix digits n)
                = (q : ℝ) * ((10 : ℝ) * (10 : ℝ) ^ n) *
                    ((x : ℝ) - decimalPrefix digits n) := by simp [hpow]
            _ = 10 * ((q : ℝ) * (10 : ℝ) ^ n * ((x : ℝ) - decimalPrefix digits n)) := by
              ring
            _ = 10 * r n := rfl
        have term2 :
            (q : ℝ) * (10 : ℝ) ^ (n + 1) *
              ((digits (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1)) =
              (q : ℝ) * (digits (n + 1) : ℝ) := by
          have hpow_ne : (10 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          field_simp [hpow_ne]
        simp [term1, term2]
  -- Each remainder is an integer between `0` and `q`.
  have hr_int : ∀ n, ∃ k : ℕ, r n = k := by
    intro n
    have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq_pos)
    -- Express `r n` as a difference of integers.
    -- Integer remainder before taking `toNat`.
    let z : ℤ :=
      ((10 : ℤ) ^ n) * x.num -
        (q : ℤ) *
          (Finset.range n).sum
            (fun i => (digits (i + 1)).val * (10 : ℤ) ^ (n - (i + 1)))
    have hr_eq :
        r n = (z : ℝ) := by
      have hcast :
          ((10 : ℤ) ^ n : ℝ) = (10 : ℝ) ^ n := by norm_cast
      have hcast' :
          ((q : ℤ) : ℝ) = (q : ℝ) := by norm_cast
      have hcast'' :
          ((Finset.range n).sum
              (fun i => (digits (i + 1)).val * (10 : ℤ) ^ (n - (i + 1))) : ℝ) =
            (Finset.range n).sum
              (fun i => (digits (i + 1) : ℝ) * (10 : ℝ) ^ (n - (i + 1))) := by
        refine (Finset.sum_congr rfl ?_)
        intro i hi
        norm_cast
      calc
        r n =
            (q : ℝ) * (10 : ℝ) ^ n *
              ((x.num : ℝ) / (q : ℝ) - decimalPrefix digits n) := by
              simp [r, Rat.cast_def, q]
        _ =
            (q : ℝ) * (10 : ℝ) ^ n * ((x.num : ℝ) / (q : ℝ)) -
              (q : ℝ) * (10 : ℝ) ^ n * decimalPrefix digits n := by ring
        _ =
            (10 : ℝ) ^ n * (x.num : ℝ) -
              (q : ℝ) * (10 : ℝ) ^ n * decimalPrefix digits n := by
                have hcancel : (q : ℝ) * ((x.num : ℝ) / (q : ℝ)) = (x.num : ℝ) := by
                  field_simp [hq_ne]
                have hrew :
                    (q : ℝ) * (10 : ℝ) ^ n * ((x.num : ℝ) / (q : ℝ)) =
                      (10 : ℝ) ^ n * (x.num : ℝ) := by
                  calc
                    (q : ℝ) * (10 : ℝ) ^ n * ((x.num : ℝ) / (q : ℝ)) =
                        (10 : ℝ) ^ n * ((q : ℝ) * ((x.num : ℝ) / (q : ℝ))) := by
                          ring
                    _ = (10 : ℝ) ^ n * (x.num : ℝ) := by simp [hcancel]
                simp [hrew]
        _ =
            (10 : ℝ) ^ n * (x.num : ℝ) -
              (q : ℝ) *
                (Finset.range n).sum
                  (fun i => (digits (i + 1) : ℝ) * (10 : ℝ) ^ (n - (i + 1))) := by
                have hprefix := decimalPrefix_mul_pow n
                calc
                  (10 : ℝ) ^ n * (x.num : ℝ) -
                      (q : ℝ) * (10 : ℝ) ^ n * decimalPrefix digits n
                      =
                        (10 : ℝ) ^ n * (x.num : ℝ) -
                          (q : ℝ) *
                            ((Finset.range n).sum
                              (fun i => (digits (i + 1) : ℝ) *
                                (10 : ℝ) ^ (n - (i + 1)))) := by
                            simp [hprefix, mul_assoc]
                  _ =
                      (10 : ℝ) ^ n * (x.num : ℝ) -
                        (q : ℝ) *
                          (Finset.range n).sum
                            (fun i => (digits (i + 1) : ℝ) *
                              (10 : ℝ) ^ (n - (i + 1))) := rfl
        _ = (z : ℝ) := by
          simp [z]
    have hz_nonneg : 0 ≤ z := by
      have hnonneg : 0 ≤ r n := (hr_bounds n).1
      have : (0 : ℝ) ≤ (z : ℝ) := by simpa [hr_eq] using hnonneg
      exact_mod_cast this
    refine ⟨Int.toNat z, ?_⟩
    have hz_nat : (Int.toNat z : ℝ) = (z : ℝ) := by
      have hz' : (Int.toNat z : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      exact_mod_cast hz'
    -- Final rewriting.
    simp [hr_eq, hz_nat]
  -- Remainders take only finitely many values in `[0,q]`; a pigeonhole argument
  -- together with the recursion yields the desired period.
  -- Details of the deterministic step and pigeonhole propagation are deferred.
  classical
  -- Pick natural-valued remainders.
  choose rNat hr_nat_spec using hr_int
  -- Bounds for the natural remainders.
  have hr_nat_le : ∀ n, rNat n ≤ q := by
    intro n
    have hle : r n ≤ (q : ℝ) := (hr_bounds n).2
    have hcast : (rNat n : ℝ) ≤ q := by simpa [hr_nat_spec n] using hle
    exact_mod_cast hcast
  -- A natural-number recursion for the remainders.
  have hr_rec_nat : ∀ n, 10 * rNat n = q * (digits (n + 1)).val + rNat (n + 1) := by
    intro n
    have h := hr_rec n
    have h' : (rNat (n + 1) : ℝ) =
        10 * (rNat n : ℝ) - (q : ℝ) * (digits (n + 1) : ℝ) := by
      simpa [hr_nat_spec (n + 1), hr_nat_spec n] using h
    have h'' : (rNat (n + 1) : ℝ) + (q : ℝ) * (digits (n + 1) : ℝ) =
        10 * (rNat n : ℝ) := by linarith
    have hdigits :
        (digits (n + 1) : ℝ) = (digits (n + 1)).val := by norm_cast
    have h''' :
        (rNat (n + 1) + q * (digits (n + 1)).val : ℝ) =
          (10 * rNat n : ℝ) := by
      simpa [hdigits, Nat.cast_mul, Nat.cast_add] using h''
    have h'''' :
        10 * rNat n = rNat (n + 1) + q * (digits (n + 1)).val := by
      exact_mod_cast h'''.symm
    simpa [Nat.add_comm] using h''''
  -- If a remainder ever hits `q`, the digits become repeating 9s from that point on.
  by_cases hhit : ∃ n, rNat n = q
  · rcases hhit with ⟨n, hnq⟩
    -- One-step propagation when the remainder equals `q`.
    have step_remainder_q :
        ∀ t, rNat t = q → rNat (t + 1) = q ∧ digits (t + 1) = (9 : Fin 10) := by
      intro t htq
      have hrec_q : q * (digits (t + 1)).val + rNat (t + 1) = 10 * q := by
        have h := hr_rec_nat t
        have h' : 10 * q = q * (digits (t + 1)).val + rNat (t + 1) := by
          simpa [htq] using h
        exact h'.symm
      have hr_le : rNat (t + 1) ≤ q := hr_nat_le (t + 1)
      -- The digit cannot be ≤ 8, otherwise the sum would be too small.
      have hge9 : 9 ≤ (digits (t + 1)).val := by
        by_contra hlt9
        have hd_le8 : (digits (t + 1)).val ≤ 8 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt9)
        have hsum_le :
            q * (digits (t + 1)).val + rNat (t + 1) ≤ q * 8 + q :=
          add_le_add (Nat.mul_le_mul_left _ hd_le8) hr_le
        have hlt : q * 8 + q < 10 * q := by
          have hrewrite : q * 8 + q = q * 9 := by
            simpa using (Nat.mul_succ q 8).symm
          have hlt' : q * 9 < q * 10 := by nlinarith [hq_pos]
          have hcomm : q * 10 = 10 * q := Nat.mul_comm _ _
          have hlt'' : q * 9 < 10 * q := by simpa [hcomm] using hlt'
          simpa [hrewrite] using hlt''
        have hlt' :
            q * (digits (t + 1)).val + rNat (t + 1) < 10 * q :=
          lt_of_le_of_lt hsum_le hlt
        have hcontr := hlt'
        rw [hrec_q] at hcontr
        exact (lt_irrefl _ hcontr)
      have hval_le9 : (digits (t + 1)).val ≤ 9 :=
        Nat.le_of_lt_succ (digits (t + 1)).is_lt
      have hval_eq : (digits (t + 1)).val = 9 := by
        exact le_antisymm hval_le9 hge9
      have hrec' : q * 9 + rNat (t + 1) = 10 * q := by
        simpa [hval_eq] using hrec_q
      have hten : q * 9 + q = 10 * q := by
        have h := Nat.mul_succ q 9
        have hcomm : q * 10 = 10 * q := Nat.mul_comm _ _
        have h' : q * 9 + q = q * 10 := h.symm
        simpa [hcomm] using h'
      have hrem : rNat (t + 1) = q := by
        have hsum : q * 9 + rNat (t + 1) = q * 9 + q := by linarith
        exact Nat.add_left_cancel hsum
      have hdigit : digits (t + 1) = (9 : Fin 10) := by
        apply Fin.ext
        simp [hval_eq]
      exact ⟨hrem, hdigit⟩
    -- All subsequent remainders stay at `q`, hence digits are constantly `9`.
    have rNat_const_q : ∀ k, rNat (n + k) = q := by
      intro k
      induction k with
      | zero => simpa using hnq
      | succ k ih =>
          have hstep := step_remainder_q (n + k) ih
          simpa [Nat.add_assoc] using hstep.1
    have digits_nine : ∀ k, digits (n + k + 1) = (9 : Fin 10) := by
      intro k
      have hrem := rNat_const_q k
      have hstep := step_remainder_q (n + k) hrem
      simpa [Nat.add_assoc] using hstep.2
    refine ⟨n + 1, 1, Nat.succ_pos _, by decide, ?_⟩
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hd1 : digits (n + 1 + k) = (9 : Fin 10) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using digits_nine k
    have hd2 : digits (n + 1 + k + 1) = (9 : Fin 10) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using digits_nine (k + 1)
    exact hd1.trans hd2.symm
  -- Otherwise all remainders stay strictly below `q`.
  · have hnoq : ¬ ∃ n, rNat n = q := hhit
    have hAll_lt : ∀ n, rNat n < q := by
      intro n
      have hle := hr_nat_le n
      have hneq : rNat n ≠ q := by
        intro h
        exact hnoq ⟨n, h⟩
      exact lt_of_le_of_ne hle hneq
    -- Deterministic step when remainders are below `q`.
    have det_step :
        ∀ n m, rNat n = rNat m →
          rNat (n + 1) = rNat (m + 1) ∧ digits (n + 1) = digits (m + 1) := by
      intro n m hrem
      have h1 : q * (digits (n + 1)).val + rNat (n + 1) = 10 * rNat n := by
        simpa using (hr_rec_nat n).symm
      have h2 : q * (digits (m + 1)).val + rNat (m + 1) = 10 * rNat m := by
        simpa using (hr_rec_nat m).symm
      have hEq :
          q * (digits (n + 1)).val + rNat (n + 1) =
            q * (digits (m + 1)).val + rNat (m + 1) := by
        calc
          q * (digits (n + 1)).val + rNat (n + 1) = 10 * rNat n := h1
          _ = 10 * rNat m := by simp [hrem]
          _ = q * (digits (m + 1)).val + rNat (m + 1) := h2.symm
      have hr1_lt : rNat (n + 1) < q := hAll_lt (n + 1)
      have hr2_lt : rNat (m + 1) < q := hAll_lt (m + 1)
      have hrem_eq : rNat (n + 1) = rNat (m + 1) := by
        have hmod := congrArg (fun t => t % q) hEq
        simp [Nat.add_mod, Nat.mod_eq_of_lt hr1_lt, Nat.mod_eq_of_lt hr2_lt] at hmod
        exact hmod
      have hEq' : q * (digits (n + 1)).val = q * (digits (m + 1)).val := by
        have hEq'' :
            q * (digits (n + 1)).val + rNat (m + 1) =
              q * (digits (m + 1)).val + rNat (m + 1) := by
          simpa [hrem_eq] using hEq
        exact Nat.add_right_cancel hEq''
      have hdigits_val_eq : (digits (n + 1)).val = (digits (m + 1)).val := by
        by_contra hneq
        rcases lt_or_gt_of_ne hneq with hlt | hlt
        · have hlt' :
            q * (digits (n + 1)).val < q * (digits (m + 1)).val := by
            nlinarith [hq_pos]
          exact (ne_of_lt hlt') hEq'
        · have hlt' :
            q * (digits (m + 1)).val < q * (digits (n + 1)).val := by
            nlinarith [hq_pos]
          exact (ne_of_lt hlt') hEq'.symm
      have hdigits_eq : digits (n + 1) = digits (m + 1) := by
        apply Fin.ext
        simpa using hdigits_val_eq
      exact ⟨hrem_eq, hdigits_eq⟩
    -- Pigeonhole principle on the first `q + 1` remainders.
    let f : Fin (q + 1) → Fin q := fun i => ⟨rNat i, hAll_lt i⟩
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have hcard := Fintype.card_le_of_injective f hinj
      have hcard' : q.succ ≤ q := by
        convert hcard using 1 <;> simp [Nat.succ_eq_add_one]
      exact (Nat.not_succ_le_self q) hcard'
    have hpair : ∃ i j : Fin (q + 1), i ≠ j ∧ f i = f j := by
      have h := hnotinj
      unfold Function.Injective at h
      push_neg at h
      rcases h with ⟨i, j, hfeq, hne⟩
      exact ⟨i, j, hne, hfeq⟩
    -- Extract natural indices with `i0 < j0`.
    obtain ⟨i0, j0, hlt, hj_le, hrem_eq0⟩ :
        ∃ i0 j0 : ℕ, i0 < j0 ∧ j0 ≤ q ∧ rNat i0 = rNat j0 := by
      rcases hpair with ⟨i, j, hne, hfeq⟩
      let iNat : ℕ := i
      let jNat : ℕ := j
      have hrem_eq : rNat iNat = rNat jNat := by
        have hval := congrArg Fin.val hfeq
        simpa [iNat, jNat] using hval
      have hij_ne : iNat ≠ jNat := by
        intro h
        apply hne
        apply Fin.ext
        simp [iNat, jNat, h]
      rcases lt_or_gt_of_ne hij_ne with hlt | hlt
      · refine ⟨iNat, jNat, hlt, ?_, hrem_eq⟩
        exact Nat.le_of_lt_succ j.isLt
      · refine ⟨jNat, iNat, hlt, ?_, hrem_eq.symm⟩
        exact Nat.le_of_lt_succ i.isLt
    have hle : i0 ≤ j0 := Nat.le_of_lt hlt
    -- Equality of remainders propagates forward.
    have rem_eq_all : ∀ k, rNat (i0 + k) = rNat (j0 + k) := by
      intro k
      induction k with
      | zero => simpa using hrem_eq0
      | succ k ih =>
          have hstep := det_step (i0 + k) (j0 + k) ih
          simpa [Nat.add_assoc] using hstep.1
    have digits_eq_all : ∀ k, digits (i0 + 1 + k) = digits (j0 + 1 + k) := by
      intro k
      have hstep := det_step (i0 + k) (j0 + k) (rem_eq_all k)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.2
    refine ⟨i0 + 1, j0 - i0, Nat.succ_pos _, Nat.sub_pos_of_lt hlt, ?_⟩
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hdigits := digits_eq_all k
    have hrewrite :
        i0 + 1 + k + (j0 - i0) = j0 + 1 + k := by
      have hsub : i0 + (j0 - i0) = j0 := by
        have h' : j0 - i0 + i0 = j0 := Nat.sub_add_cancel hle
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
      calc
        i0 + 1 + k + (j0 - i0) = (i0 + (j0 - i0)) + (1 + k) := by
          ac_rfl
        _ = j0 + (1 + k) := by simp [hsub]
        _ = j0 + 1 + k := by ac_rfl
    simpa [hrewrite] using hdigits

/-- Triangular numbers: `triangle n = 1 + 2 + … + n`. -/
def Nat.triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.triangle n + (n + 1)

@[simp] lemma Nat.triangle_zero : Nat.triangle 0 = 0 := rfl
lemma Nat.triangle_succ' (n : ℕ) :
    Nat.triangle (n + 1) = Nat.triangle n + (n + 1) := rfl

/-- Digits for Example 1.5.4: `1` at triangular indices and `0` otherwise. -/
noncomputable def digitsInc : ℕ → Fin 10 :=
  fun n => by
    classical
    exact if ∃ k, n = Nat.triangle (k + 1) then (1 : Fin 10) else 0

lemma digitsInc_triangle (k : ℕ) : digitsInc (Nat.triangle (k + 1)) = 1 := by
  classical
  have h : ∃ k', Nat.triangle (k' + 1) = Nat.triangle (k + 1) := ⟨k, rfl⟩
  have h' : ∃ k', Nat.triangle (k + 1) = Nat.triangle (k' + 1) := by
    rcases h with ⟨k', hk'⟩
    exact ⟨k', hk'.symm⟩
  simp [digitsInc, h']

lemma digitsInc_zero {n : ℕ} (h : ¬ ∃ k, n = Nat.triangle (k + 1)) :
    digitsInc n = 0 := by
  classical
  simp [digitsInc, h]

lemma digitsInc_le_one (n : ℕ) : (digitsInc n : ℝ) ≤ 1 := by
  classical
  by_cases h : ∃ k, n = Nat.triangle (k + 1) <;> simp [digitsInc, h]

lemma triangle_strictMono : StrictMono Nat.triangle := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have hpos : 0 < n + 1 := Nat.succ_pos _
  have hlt : Nat.triangle n < Nat.triangle n + (n + 1) :=
    Nat.lt_add_of_pos_right hpos
  simpa [Nat.triangle_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

lemma le_triangle_succ (k : ℕ) : k ≤ Nat.triangle (k + 1) := by
  have hk : k ≤ Nat.triangle k + k := Nat.le_add_left _ _
  have hk' : k + 1 ≤ Nat.triangle k + k + 1 := Nat.succ_le_succ hk
  have hrew : Nat.triangle k + k + 1 = Nat.triangle (k + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.triangle_succ' k).symm
  have hk'' : k + 1 ≤ Nat.triangle (k + 1) := by simpa [hrew] using hk'
  exact Nat.le_trans (Nat.le_succ _) hk''

lemma digitsInc_nonperiodic_gap :
    ∀ N P, 0 < P → ∃ n ≥ N, digitsInc n = 1 ∧ digitsInc (n + P) = 0 := by
  intro N P hPpos
  classical
  -- Choose a triangular index well beyond `N` and `P`.
  let k := Nat.max N P
  have hkN : N ≤ k := Nat.le_max_left _ _
  have hkP : P ≤ k := Nat.le_max_right _ _
  let n := Nat.triangle (k + 1)
  have hk_le_n : k ≤ n := by
    dsimp [n]
    simpa using le_triangle_succ k
  have hnN : N ≤ n := le_trans hkN hk_le_n
  have hnp : digitsInc n = 1 := by
    dsimp [n]; simpa using digitsInc_triangle k
  -- Next triangular number is at distance `k + 2`.
  have hnext : Nat.triangle (k + 2) = n + k + 2 := by
    simp [n, Nat.triangle_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hlt_next : n + P < Nat.triangle (k + 2) := by
    have hnk : n + P ≤ n + k := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using add_le_add_right hkP n
    have hlt : n + k < n + k + 2 := by nlinarith
    have hlt' : n + P < n + k + 2 := lt_of_le_of_lt hnk hlt
    simpa [hnext] using hlt'
  have hgt_prev : Nat.triangle (k + 1) < n + P := by
    have : n < n + P := by nlinarith
    simpa [n] using this
  have hno_triangle :
      ¬ ∃ t, n + P = Nat.triangle (t + 1) := by
    intro h
    rcases h with ⟨t, ht⟩
    have hgt : k + 1 < t + 1 := by
      have hlt' : Nat.triangle (k + 1) < Nat.triangle (t + 1) := by
        have hlt'' : Nat.triangle (k + 1) < Nat.triangle (k + 1) + P :=
          Nat.lt_add_of_pos_right hPpos
        have hrewrite : Nat.triangle (k + 1) + P = Nat.triangle (t + 1) := by
          simpa [n, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
        simpa [hrewrite] using hlt''
      exact (triangle_strictMono.lt_iff_lt).1 hlt'
    have hlt : t + 1 < k + 2 := by
      have hlt' : Nat.triangle (t + 1) < Nat.triangle (k + 2) := by
        simpa [ht] using hlt_next
      exact (triangle_strictMono.lt_iff_lt).1 hlt'
    have hle : t + 1 ≤ k + 1 := Nat.lt_succ_iff.mp hlt
    have hcontr : k + 1 < k + 1 := lt_of_lt_of_le hgt hle
    exact (lt_irrefl _ hcontr).elim
  have hnp_zero : digitsInc (n + P) = 0 := digitsInc_zero hno_triangle
  exact ⟨n, hnN, hnp, hnp_zero⟩

/-- Example 1.5.4: The real number with decimal expansion `0.101001000100001…`,
whose `1`s occur at the positions `1, 3, 6, 10, …` (each separated by an
increasing block of zeros), is irrational. -/
noncomputable def decimalWithIncreasingZeroBlocks : ℝ :=
  ∑' n : ℕ, (digitsInc (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1)

lemma decimalWithIncreasingZeroBlocks_bounds :
    decimalBoundsStrict digitsInc decimalWithIncreasingZeroBlocks := by
  classical
  -- Series terms for the decimal expansion.
  let f : ℕ → ℝ := fun m => (digitsInc (m + 1) : ℝ) / (10 : ℝ) ^ (m + 1)
  have hdef : decimalWithIncreasingZeroBlocks = ∑' m, f m := rfl
  -- Basic bounds on the terms.
  have hnonneg : ∀ m, 0 ≤ f m := by
    intro m
    have hpow : 0 ≤ (10 : ℝ) ^ (m + 1) := le_of_lt (pow_pos (by norm_num) _)
    have hpos : 0 ≤ (digitsInc (m + 1) : ℝ) := by positivity
    have : 0 ≤ (digitsInc (m + 1) : ℝ) / (10 : ℝ) ^ (m + 1) :=
      div_nonneg hpos hpow
    simpa [f] using this
  have hle_one : ∀ m, f m ≤ (1 : ℝ) / (10 : ℝ) ^ (m + 1) := by
    intro m
    have hpow : 0 < (10 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
    have hdigit : (digitsInc (m + 1) : ℝ) ≤ 1 := digitsInc_le_one (m + 1)
    have hpow' : 0 ≤ (10 : ℝ) ^ (m + 1) := le_of_lt hpow
    have : (digitsInc (m + 1) : ℝ) / (10 : ℝ) ^ (m + 1) ≤
        1 / (10 : ℝ) ^ (m + 1) := by
      have hmul :
          ((10 : ℝ) ^ (m + 1))⁻¹ * (digitsInc (m + 1) : ℝ) ≤
            ((10 : ℝ) ^ (m + 1))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hdigit (inv_nonneg.mpr hpow')
      simpa [div_eq_mul_inv, mul_comm] using hmul
    simpa [f] using this
  -- The geometric series bounds.
  have hgeom_base : Summable (fun m : ℕ => (1 : ℝ) / (10 : ℝ) ^ m) := by
    have hr : |(10 : ℝ)⁻¹| < 1 := by norm_num
    have h := summable_geometric_of_abs_lt_one hr
    simpa [one_div, inv_pow] using h
  have hgeom : Summable (fun m : ℕ => (1 : ℝ) / (10 : ℝ) ^ (m + 1)) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (10 : ℝ) ^ m) 1).2 hgeom_base
  have hsum : Summable f := Summable.of_nonneg_of_le hnonneg hle_one hgeom
  refine ⟨?_, ?_⟩
  · -- Leading digit is `0`.
    have hfalse : ¬ ∃ k, 0 = Nat.triangle (k + 1) := by
      intro h
      rcases h with ⟨k, hk⟩
      have hpos : 0 < Nat.triangle (k + 1) := by
        have hkpos : 0 < k + 1 := Nat.succ_pos _
        have hnonneg : 0 ≤ Nat.triangle k := Nat.zero_le _
        nlinarith [Nat.triangle_succ' k]
      exact (ne_of_gt hpos) hk.symm
    exact digitsInc_zero hfalse
  · intro n
    -- Split the series at position `n`.
    have hsplit :
        decimalWithIncreasingZeroBlocks =
          decimalPrefix digitsInc n + ∑' m, f (m + n) := by
      calc
        decimalWithIncreasingZeroBlocks = ∑' m, f m := hdef
        _ = (Finset.range n).sum f + ∑' m, f (m + n) :=
          (Summable.sum_add_tsum_nat_add n hsum).symm
        _ = decimalPrefix digitsInc n + ∑' m, f (m + n) := by
          simp [decimalPrefix, f]
    -- The tail is strictly positive since there is a future `1`.
    have htail_pos : 0 < ∑' m, f (m + n) := by
      obtain ⟨j, hj, hj1, _⟩ := digitsInc_nonperiodic_gap (N := n + 1) (P := 1) (by decide)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
      have hpos_term : 0 < f (m + n) := by
        have hpow : 0 < (10 : ℝ) ^ (m + n + 1) := pow_pos (by norm_num) _
        have hdig : digitsInc (m + n + 1) = 1 := by
          have hcomm : m + n + 1 = n + 1 + m := by ac_rfl
          simpa [hcomm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj1
        have hpos :
            0 < (digitsInc (m + n + 1) : ℝ) / (10 : ℝ) ^ (m + n + 1) := by
          have hdig' : (digitsInc (m + n + 1) : ℝ) = 1 := by
            simpa using congrArg (fun x : Fin 10 => (x : ℝ)) hdig
          have hdiv : 0 < (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) :=
            div_pos (by norm_num) hpow
          have hdiv' :
              (digitsInc (m + n + 1) : ℝ) / (10 : ℝ) ^ (m + n + 1) =
                (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) := by
            simp [hdig']
          exact hdiv'.symm ▸ hdiv
        simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos
      have hshift_summable : Summable (fun i : ℕ => f (i + n)) :=
        hsum.comp_injective (by intro i j h; exact Nat.add_right_cancel h)
      have hsum_ge :
          (Finset.range (m + 1)).sum (fun i => f (i + n)) ≤ ∑' i, f (i + n) :=
        Summable.sum_le_tsum (s := Finset.range (m + 1))
          (hs := by
            intro i hi
            exact hnonneg (i + n)) hshift_summable
      have hterm_le :
          f (m + n) ≤ (Finset.range (m + 1)).sum (fun i => f (i + n)) :=
        by
          have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
          exact Finset.single_le_sum (fun i _ => hnonneg (i + n)) hmem
      have : f (m + n) ≤ ∑' i, f (i + n) := le_trans hterm_le hsum_ge
      exact lt_of_lt_of_le hpos_term this
    -- Upper bound on the tail via the geometric series.
    have htail_le :
        ∑' m, f (m + n) ≤ 1 / (10 : ℝ) ^ n := by
      -- Compare with the pure geometric tail.
      have hgeom_tail :
          Summable (fun m : ℕ => (1 : ℝ) / (10 : ℝ) ^ (m + n + 1)) :=
        hgeom.comp_injective (by intro i j h; exact Nat.add_right_cancel h)
      have hbound :
          ∀ m, f (m + n) ≤ (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) := fun m => hle_one (m + n)
      have hsum_tail : Summable (fun m : ℕ => f (m + n)) :=
        hsum.comp_injective (by intro i j h; exact Nat.add_right_cancel h)
      have htsum_le :
          ∑' m, f (m + n) ≤ ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) :=
        Summable.tsum_le_tsum hbound hsum_tail hgeom_tail
      have hgeom_eval :
          ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) =
            (1 / (10 : ℝ) ^ (n + 1)) * (10 / 9) := by
        have hr : |(10 : ℝ)⁻¹| < 1 := by norm_num
        have hgeom_sum_pow :
            ∑' m, ((10 : ℝ) ^ m)⁻¹ = (10 / 9 : ℝ) := by
          have h := tsum_geometric_of_abs_lt_one hr
          have h' : (1 - (10 : ℝ)⁻¹)⁻¹ = (10 / 9 : ℝ) := by norm_num
          have h'' : ∑' m, ((10 : ℝ)⁻¹) ^ m = (10 / 9 : ℝ) := h.trans h'
          simpa [inv_pow] using h''
        have hfun :
            (fun m : ℕ => ((10 : ℝ) ^ (m + n + 1))⁻¹) =
              fun m : ℕ => ((10 : ℝ) ^ (n + 1))⁻¹ * ((10 : ℝ) ^ m)⁻¹ := by
          funext m
          simp [pow_add, mul_comm, mul_assoc]
        have hsum_geom : Summable (fun m : ℕ => ((10 : ℝ) ^ m)⁻¹) := by
          simpa [inv_pow] using summable_geometric_of_abs_lt_one hr
        calc
          ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1)
              = ∑' m, ((10 : ℝ) ^ (n + 1))⁻¹ * ((10 : ℝ) ^ m)⁻¹ := by
                  simp [hfun, one_div]
          _ = ((10 : ℝ) ^ (n + 1))⁻¹ * ∑' m, ((10 : ℝ) ^ m)⁻¹ :=
                hsum_geom.tsum_mul_left _
          _ = (1 / (10 : ℝ) ^ (n + 1)) * (10 / 9) := by
                simp [one_div, hgeom_sum_pow]
      have hrewrite :
          (1 / (10 : ℝ) ^ (n + 1)) * (10 / 9) = (1 / 9) * (1 / (10 : ℝ) ^ n) := by
        calc
          (1 / (10 : ℝ) ^ (n + 1)) * (10 / 9)
              = (1 / (10 : ℝ) ^ n) * ((1 / 10) * (10 / 9)) := by
                  simp [pow_succ, one_div, mul_comm, mul_assoc]
          _ = (1 / (10 : ℝ) ^ n) * (1 / 9) := by norm_num
          _ = (1 / 9) * (1 / (10 : ℝ) ^ n) := by ring
      have hgeom_le :
          ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) ≤ 1 / (10 : ℝ) ^ n := by
        have hnonneg_pow : 0 ≤ 1 / (10 : ℝ) ^ n := by positivity
        have hgeom_val :
            ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1) =
              (1 / 9 : ℝ) * (1 / (10 : ℝ) ^ n) :=
          hgeom_eval.trans hrewrite
        calc
          ∑' m, (1 : ℝ) / (10 : ℝ) ^ (m + n + 1)
              = (1 / 9 : ℝ) * (1 / (10 : ℝ) ^ n) := hgeom_val
          _ ≤ 1 * (1 / (10 : ℝ) ^ n) := by
                have hle1 : (1 / 9 : ℝ) ≤ 1 := by norm_num
                exact mul_le_mul_of_nonneg_right hle1 hnonneg_pow
          _ = 1 / (10 : ℝ) ^ n := by ring
      exact le_trans htsum_le hgeom_le
    constructor
    · -- strict lower bound
      have htail_eq :
          ∑' m, f (m + n) =
            decimalWithIncreasingZeroBlocks - decimalPrefix digitsInc n := by
        have := hsplit
        linarith
      have hpos := htail_pos
      have hsub : decimalWithIncreasingZeroBlocks - decimalPrefix digitsInc n > 0 := by
        simpa [htail_eq] using hpos
      linarith
    · -- upper bound with the geometric tail
      linarith [hsplit, htail_le]

/-- The number `decimalWithIncreasingZeroBlocks` from Example 1.5.4 is irrational. -/
theorem irrational_decimalWithIncreasingZeroBlocks :
    Irrational decimalWithIncreasingZeroBlocks := by
  classical
  -- Decimal bounds coming from the series definition.
  have hbounds_strict := decimalWithIncreasingZeroBlocks_bounds
  have hbounds :
      decimalBounds digitsInc decimalWithIncreasingZeroBlocks := by
    intro n
    have h := hbounds_strict.2 n
    exact ⟨le_of_lt h.1, h.2⟩
  have hpos : 0 < decimalWithIncreasingZeroBlocks :=
    (hbounds_strict.2 0).1
  have hone : decimalWithIncreasingZeroBlocks ≤ 1 := by
    have h := (hbounds_strict.2 0).2
    simpa [decimalPrefix, one_div] using h
  have hx : (decimalWithIncreasingZeroBlocks : ℝ) ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨hpos, hone⟩
  intro hrat
  rcases hrat with ⟨q, hq⟩
  have hxq : (q : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by simpa [hq] using hx
  have hbounds_q : decimalBounds digitsInc (q : ℝ) := by simpa [hq] using hbounds
  -- Rational decimals are eventually periodic.
  obtain ⟨N, P, hNpos, hPpos, hper⟩ :=
    rational_decimal_digits_eventually_periodic q digitsInc hxq hbounds_q
  -- But our digits have arbitrarily long zero blocks, contradicting periodicity.
  obtain ⟨n, hnN, hn1, hn0⟩ := digitsInc_nonperiodic_gap N P hPpos
  have hcontr := hper hnN
  have hones : digitsInc n = (1 : Fin 10) := by simpa using hn1
  have hzeros : digitsInc (n + P) = (0 : Fin 10) := hn0
  have hneq : (1 : Fin 10) ≠ 0 := by decide
  have hcontr' : (1 : Fin 10) = 0 := by
    convert hcontr using 1 <;> simp [hones, hzeros]
  exact hneq hcontr'

end Section05
end Chap01
