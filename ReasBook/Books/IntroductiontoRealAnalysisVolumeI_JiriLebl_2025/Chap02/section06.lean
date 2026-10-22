/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators Topology

section Chap02
section Section06

/-- The limsup of a nonnegative real sequence is nonnegative. -/
lemma limsup_nonneg_of_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    0 ≤ Filter.limsup u Filter.atTop := by
  classical
  by_cases hbounded : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u
  ·
    have hfreq : ∃ᶠ n in Filter.atTop, (0 : ℝ) ≤ u n :=
      Filter.Frequently.of_forall hu
    exact Filter.le_limsup_of_frequently_le (f := Filter.atTop) (u := u) hfreq hbounded
  ·
    have hset_empty :
        {a : ℝ | ∀ᶠ n in Filter.atTop, u n ≤ a} = ∅ := by
      ext a
      constructor
      · intro ha
        exact (hbounded ⟨a, ha⟩).elim
      · intro ha
        cases ha
    rw [Filter.limsup_eq, hset_empty, Real.sInf_empty]

/-- Convert a bound on the `n`-th root into a bound on the `n`-th power. -/
lemma rpow_inv_natCast_le_pow {a r : ℝ} {n : ℕ} (ha : 0 ≤ a) (hn : n ≠ 0)
    (h : Real.rpow a (1 / (n : ℝ)) ≤ r) :
    a ≤ r ^ n := by
  have hpow :
      (Real.rpow a (1 / (n : ℝ))) ^ (n : ℝ) ≤ r ^ (n : ℝ) := by
    refine Real.rpow_le_rpow ?_ h ?_
    · exact Real.rpow_nonneg ha _
    · exact_mod_cast (Nat.zero_le n)
  have hpow' :
      (Real.rpow a (1 / (n : ℝ))) ^ n ≤ r ^ n := by
    simpa [Real.rpow_natCast] using hpow
  have hpow'' :
      (Real.rpow a (1 / (n : ℝ))) ^ n = a := by
    simpa [one_div] using (Real.rpow_inv_natCast_pow ha hn)
  calc
    a = (Real.rpow a (1 / (n : ℝ))) ^ n := by
      simpa using hpow''.symm
    _ ≤ r ^ n := hpow'

/-- Proposition 2.6.1 (Root test). Let `x : ℕ → ℝ` and set
`L = limsup_{n→∞} (|x (n+1)|)^{1/(n+1)}`. (i) If `L < 1`, then
`∑_{n=1}^{∞} x n` converges absolutely. (ii) If `L > 1`, then
`∑_{n=1}^{∞} x n` diverges. -/
lemma root_test_abs_converges {x : ℕ → ℝ} {L : ℝ}
    (hlimsup :
      Filter.limsup (fun n : ℕ => Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ)))
        Filter.atTop = L) (hL : L < 1)
    (hbounded :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ => Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ)))) :
    Summable (fun n => ‖x (n + 1)‖) := by
  let u : ℕ → ℝ := fun n =>
    Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ))
  have hbounded' : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
    simpa [u] using hbounded
  have hlimsup' : Filter.limsup u Filter.atTop = L := by
    simpa [u] using hlimsup
  obtain ⟨r, hLr, hr1⟩ := exists_between hL
  have hL_nonneg : 0 ≤ L := by
    have h := limsup_nonneg_of_nonneg (u := u) (fun n => by
      exact Real.rpow_nonneg (abs_nonneg _) _)
    simpa [hlimsup'] using h
  have hr0 : 0 ≤ r := le_trans hL_nonneg (le_of_lt hLr)
  have hroot_ev : ∀ᶠ n in Filter.atTop, u n < r := by
    have hlimsup_lt : Filter.limsup u Filter.atTop < r := by
      simpa [hlimsup'] using hLr
    exact Filter.eventually_lt_of_limsup_lt hlimsup_lt hbounded'
  rcases (Filter.eventually_atTop.1 hroot_ev) with ⟨N, hN⟩
  have hbound : ∀ n ≥ N, ‖x (n + 1)‖ ≤ r ^ (n + 1) := by
    intro n hn
    have hroot_le : Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ)) ≤ r := by
      have hroot_le' : u n ≤ r := (hN n hn).le
      dsimp [u] at hroot_le'
      exact hroot_le'
    have hroot_le' : Real.rpow (|x (n + 1)|) (1 / (↑(n + 1) : ℝ)) ≤ r := by
      simpa [Nat.cast_add, Nat.cast_one] using hroot_le
    have habs :
        |x (n + 1)| ≤ r ^ (n + 1) := by
      exact rpow_inv_natCast_le_pow (a := |x (n + 1)|) (r := r) (n := n + 1)
        (abs_nonneg _) (Nat.succ_ne_zero n) hroot_le'
    simpa [Real.norm_eq_abs] using habs
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hgeom_tail : Summable (fun n : ℕ => r ^ (n + N + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => r ^ n) (N + 1)).2 hgeom
  have htail : Summable (fun n : ℕ => ‖x (n + N + 1)‖) := by
    refine Summable.of_nonneg_of_le
        (f := fun n : ℕ => r ^ (n + N + 1))
        (g := fun n : ℕ => ‖x (n + N + 1)‖) ?_ ?_ hgeom_tail
    · intro n
      exact norm_nonneg _
    · intro n
      have h := hbound (n + N) (Nat.le_add_left N n)
      simpa [add_assoc, add_comm, add_left_comm] using h
  exact (summable_nat_add_iff (f := fun n : ℕ => ‖x (n + 1)‖) N).1 htail

/-- A strict bound on an `n`-th root yields a strict bound on the `n`-th power. -/
lemma rpow_inv_natCast_lt_pow {a r : ℝ} {n : ℕ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hn : n ≠ 0)
    (h : Real.rpow a (1 / (n : ℝ)) > r) :
    r ^ n < a := by
  have hpow :
      r ^ n < (Real.rpow a (1 / (n : ℝ))) ^ n := by
    have h' : r < Real.rpow a (1 / (n : ℝ)) := by
      simpa [gt_iff_lt] using h
    exact pow_lt_pow_left₀ h' hr hn
  have hpow' :
      (Real.rpow a (1 / (n : ℝ))) ^ n = a := by
    simpa [one_div] using (Real.rpow_inv_natCast_pow (x := a) (n := n) ha hn)
  calc
    r ^ n < (Real.rpow a (1 / (n : ℝ))) ^ n := hpow
    _ = a := hpow'

/-- A sequence tending to `0` is eventually within unit distance of `0`. -/
lemma tendsto_zero_eventually_abs_lt_one {x : ℕ → ℝ}
    (h : Filter.Tendsto x Filter.atTop (𝓝 0)) :
    ∀ᶠ n in Filter.atTop, |x n| < 1 := by
  have hball : Metric.ball (0 : ℝ) 1 ∈ (𝓝 (0 : ℝ)) := by
    simpa using (Metric.ball_mem_nhds (x := (0 : ℝ)) (ε := 1) (by norm_num))
  have hball' : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball (0 : ℝ) 1 :=
    h.eventually_mem hball
  filter_upwards [hball'] with n hn
  have : dist (x n) 0 < (1 : ℝ) := by
    simpa [Metric.mem_ball] using hn
  simpa [Real.dist_eq] using this

lemma root_test_diverges {x : ℕ → ℝ} {L : ℝ}
    (hlimsup :
      Filter.limsup (fun n : ℕ => Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ)))
        Filter.atTop = L) (hL : 1 < L) :
    ¬ Summable (fun n => x (n + 1)) := by
  classical
  intro hsum
  let u : ℕ → ℝ := fun n =>
    Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ))
  have hlimsup' : Filter.limsup u Filter.atTop = L := by
    simpa [u] using hlimsup
  have hzero : Filter.Tendsto (fun n => x (n + 1)) Filter.atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have habs_lt : ∀ᶠ n in Filter.atTop, |x (n + 1)| < 1 :=
    tendsto_zero_eventually_abs_lt_one hzero
  obtain ⟨r, hr1, hrL⟩ := exists_between hL
  have hr0 : 0 ≤ r := zero_le_one.trans (le_of_lt hr1)
  have hco : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u := by
    refine Filter.IsCoboundedUnder.of_frequently_ge (a := 0) ?_
    exact Filter.Frequently.of_forall (fun n => by
      dsimp [u]
      exact Real.rpow_nonneg (abs_nonneg _) _)
  have hfreq : ∃ᶠ n in Filter.atTop, r < u n := by
    have : r < Filter.limsup u Filter.atTop := by
      simpa [hlimsup'] using hrL
    exact Filter.frequently_lt_of_lt_limsup hco this
  have hfreq_abs : ∃ᶠ n in Filter.atTop, 1 ≤ |x (n + 1)| := by
    refine hfreq.mono ?_
    intro n hn
    have hroot : Real.rpow (|x (n + 1)|) (1 / (n + 1 : ℝ)) > r := by
      simpa [u] using hn
    have hroot' :
        Real.rpow (|x (n + 1)|) (1 / ((n + 1 : ℕ) : ℝ)) > r := by
      simpa [Nat.cast_add, Nat.cast_one] using hroot
    have hpow : r ^ (n + 1) < |x (n + 1)| :=
      rpow_inv_natCast_lt_pow (a := |x (n + 1)|) (r := r) (n := n + 1)
        (abs_nonneg _) hr0 (Nat.succ_ne_zero n) hroot'
    have hpow1 : 1 ≤ r ^ (n + 1) := one_le_pow₀ (le_of_lt hr1)
    exact le_trans hpow1 (le_of_lt hpow)
  have hcontr : ∃ᶠ n : ℕ in Filter.atTop, False := by
    refine (hfreq_abs.and_eventually habs_lt).mono ?_
    intro n hn
    exact (not_lt_of_ge hn.1) hn.2
  exact (Filter.frequently_false Filter.atTop) hcontr

/-- Proposition 2.6.2 (Alternating series). If `x : ℕ → ℝ` is a monotone decreasing
sequence of positive numbers with `Filter.Tendsto (fun n => x (n + 1)) Filter.atTop (𝓝 0)`,
then the alternating series `∑_{n=1}^∞ (-1)^n x_n` converges. -/
lemma alternating_series_converges {x : ℕ → ℝ}
    (hmono : Antitone fun n : ℕ => x (n + 1))
    (hpos : ∀ n : ℕ, 0 ≤ x (n + 1))
    (hlim : Filter.Tendsto (fun n : ℕ => x (n + 1)) Filter.atTop (𝓝 0)) :
    ∃ l,
      Filter.Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ (i + 1) * x (i + 1)) Filter.atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := hmono.tendsto_alternating_series_of_tendsto_zero hlim
  have _ := hpos 0
  refine ⟨-l, ?_⟩
  have hl' := hl.const_mul (-1 : ℝ)
  -- multiply the standard alternating sums by `-1` to shift the exponent by `1`
  simpa [Finset.mul_sum, pow_succ, mul_left_comm, mul_comm, mul_assoc] using hl'

/-- Proposition 2.6.3. If `∑_{n=1}^∞ x_n` is absolutely convergent with sum `x`, then for any
bijection `σ : ℕ → ℕ` the rearranged series `∑_{n=1}^∞ x_{σ n}` is absolutely convergent and has
the same sum. -/
lemma absolute_convergence_rearrangement {x : ℕ → ℝ} {s : ℝ}
    (hs_abs : Summable fun n : ℕ => ‖x (n + 1)‖)
    (hs_sum : tsum (fun n : ℕ => x (n + 1)) = s) (σ : Equiv.Perm ℕ) :
    Summable (fun n : ℕ => x (σ n + 1)) ∧
      tsum (fun n : ℕ => x (σ n + 1)) = s := by
  classical
  have hsum : Summable (fun n : ℕ => x (n + 1)) := hs_abs.of_norm
  have hsum_perm_norm :
      Summable (fun n : ℕ => ‖x (σ n + 1)‖) :=
    hs_abs.comp_injective σ.injective
  have hsum_perm : Summable (fun n : ℕ => x (σ n + 1)) := hsum_perm_norm.of_norm
  refine ⟨hsum_perm, ?_⟩
  have htsum :
      tsum (fun n : ℕ => x (σ n + 1)) = tsum (fun n : ℕ => x (n + 1)) := by
    simpa [Function.comp] using
      (Equiv.tsum_eq (σ) (f := fun n : ℕ => x (n + 1)))
  calc
    tsum (fun n : ℕ => x (σ n + 1)) = tsum (fun n : ℕ => x (n + 1)) := htsum
    _ = s := hs_sum

/-- Theorem 2.6.5 (Mertens' theorem). Suppose `∑_{n=0}^∞ a_n = A` and `∑_{n=0}^∞ b_n = B`,
and assume at least one of the series converges absolutely.  Define
`c n = a 0 * b n + a 1 * b (n - 1) + ⋯ + a n * b 0 = ∑_{i=0}^n a i * b (n - i)`.
Then `∑_{n=0}^∞ c n` converges to `A * B`. -/
theorem mertens_convolution {a b : ℕ → ℝ}
    (ha : Summable a) (hb : Summable b)
    (habs : Summable (fun n => ‖a n‖) ∨ Summable (fun n => ‖b n‖)) :
    Summable
        (fun n : ℕ => (Finset.range (n + 1)).sum fun i => a i * b (n - i)) ∧
      tsum ((fun n : ℕ => (Finset.range (n + 1)).sum fun i => a i * b (n - i))) =
        tsum a * tsum b := by
  classical
  -- obtain absolute convergence for both series (using the given hypothesis and `Summable.norm`)
  have ha_abs : Summable fun n => ‖a n‖ :=
    habs.elim (fun h => h) (fun _ => ha.norm)
  have hb_abs : Summable fun n => ‖b n‖ :=
    habs.elim (fun _ => hb.norm) (fun h => h)
  -- summability of the Cauchy product
  have hsum :
      Summable (fun n : ℕ => (Finset.range (n + 1)).sum fun i => a i * b (n - i)) :=
    summable_sum_mul_range_of_summable_norm' (f := a) (g := b) ha_abs ha hb_abs hb
  -- value of the sum via the Cauchy product formula
  have htsum :
      ((∑' n, a n) * ∑' n, b n) =
        ∑' n, (Finset.range (n + 1)).sum fun i => a i * b (n - i) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' (f := a) (g := b)
      ha_abs ha hb_abs hb
  refine ⟨hsum, ?_⟩
  exact htsum.symm

/-- Example 2.6.6. Let `a n = b n = (-1)^n / √(n+1)` so that each alternating series
`∑_{n=0}^∞ a n` and `∑_{n=0}^∞ b n` converges conditionally. If
`c n = ∑_{i=0}^n a i * b (n - i)` is their Cauchy product, then the terms `c n` do not tend
to zero, and hence the series `∑_{n=0}^∞ c n` diverges. -/
lemma cauchy_product_conditional_diverges :
    let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / Real.sqrt (n + 1)
    let c : ℕ → ℝ := fun n =>
      (Finset.range (n + 1)).sum fun i => a i * a (n - i)
    ¬ Summable c := by
  classical
  dsimp
  set a : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / Real.sqrt (n + 1) with ha
  set c : ℕ → ℝ :=
    fun n => (Finset.range (n + 1)).sum fun i => a i * a (n - i) with hc
  change ¬ Summable c
  have hc_formula :
      ∀ n,
        c n =
          (-1 : ℝ) ^ n *
            (Finset.range (n + 1)).sum
              (fun i => (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
    intro n
    classical
    unfold c
    calc
      (Finset.range (n + 1)).sum (fun i => a i * a (n - i))
          =
            (Finset.range (n + 1)).sum
              (fun i =>
                (-1 : ℝ) ^ n *
                  ((1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1)))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            have hpows :
                (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - i) = (-1 : ℝ) ^ n := by
              have hsum : i + (n - i) = n := Nat.add_sub_cancel' hle
              calc
                (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - i)
                    = (-1 : ℝ) ^ (i + (n - i)) := by
                      simp [pow_add]
                _ = (-1 : ℝ) ^ n := by simp [hsum]
            have hcalc :
                a i * a (n - i) =
                  (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - i) *
                    ((1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
              simp [a, div_eq_mul_inv, Nat.cast_sub hle, sub_eq_add_neg, add_assoc,
                mul_left_comm, mul_assoc]
            have hcalc' :
                a i * a (n - i) =
                  (-1 : ℝ) ^ n *
                    ((1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
              simpa [hpows] using hcalc
            exact hcalc'
      _ =
          (-1 : ℝ) ^ n *
            (Finset.range (n + 1)).sum
              (fun i => (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
            simp [Finset.mul_sum]
  -- absolute value of `c n`
  have hc_abs :
      ∀ n,
        |c n| =
          (Finset.range (n + 1)).sum
            (fun i => (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
    intro n
    have hpos_sum :
        0 ≤
          (Finset.range (n + 1)).sum
            (fun i => (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have h1 : 0 ≤ (Real.sqrt (i + 1)) := Real.sqrt_nonneg _
      have h2 : 0 ≤ (Real.sqrt (n - i + 1)) := Real.sqrt_nonneg _
      have h1' : 0 ≤ 1 / Real.sqrt (i + 1) := one_div_nonneg.mpr h1
      have h2' : 0 ≤ 1 / Real.sqrt (n - i + 1) := one_div_nonneg.mpr h2
      nlinarith
    have hpos_sum' :
        0 ≤
          (Finset.range (n + 1)).sum
            (fun i =>
              (Real.sqrt (i + 1))⁻¹ * (Real.sqrt (n - i + 1))⁻¹) := by
      simpa [one_div] using hpos_sum
    have hcf := hc_formula n
    calc
      |c n| =
          |(-1 : ℝ) ^ n *
              (Finset.range (n + 1)).sum
                (fun i =>
                  (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1)))| := by
            simp [hcf]
      _ =
          |(-1 : ℝ) ^ n|
              *
                (Finset.range (n + 1)).sum
                  (fun i =>
                    (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
            simp [abs_mul, abs_of_nonneg hpos_sum']
      _ =
          (Finset.range (n + 1)).sum
            (fun i => (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
            simp
  -- estimate each summand from below
  have hterm :
      ∀ {n i : ℕ}, i < n + 1 →
        (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1)) ≥ 1 / (n + 1 : ℝ) := by
    intro n i hi
    have hi_le : i ≤ n := Nat.le_of_lt_succ hi
    have hle1 : (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hi_le
    have hle2 : (n - i + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.sub_le _ _)
    have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hpos1 : 0 < Real.sqrt (i + 1) := by
      have : 0 < (i + 1 : ℝ) := by nlinarith
      exact Real.sqrt_pos.2 this
    have hpos2 : 0 < Real.sqrt (n - i + 1) := by
      have : 0 < (n - i + 1 : ℝ) := by nlinarith
      exact Real.sqrt_pos.2 this
    have hle_sqrt1 : Real.sqrt (i + 1) ≤ Real.sqrt (n + 1) :=
      Real.sqrt_le_sqrt hle1
    have hle_sqrt2 : Real.sqrt (n - i + 1) ≤ Real.sqrt (n + 1) :=
      Real.sqrt_le_sqrt hle2
    have hge1 :
        1 / Real.sqrt (n + 1) ≤ 1 / Real.sqrt (i + 1) :=
      one_div_le_one_div_of_le hpos1 hle_sqrt1
    have hge2 :
        1 / Real.sqrt (n + 1) ≤ 1 / Real.sqrt (n - i + 1) :=
      one_div_le_one_div_of_le hpos2 hle_sqrt2
    have hge_prod :
        (1 / Real.sqrt (n + 1)) * (1 / Real.sqrt (n + 1)) ≤
          (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1)) := by
      have hnonneg_c : 0 ≤ 1 / Real.sqrt (n + 1) := by positivity
      have hnonneg_b : 0 ≤ 1 / Real.sqrt (i + 1) := by positivity
      have h := mul_le_mul hge1 hge2 hnonneg_c hnonneg_b
      simpa [pow_two] using h
    have htarget :
        (1 / Real.sqrt (n + 1)) * (1 / Real.sqrt (n + 1)) = 1 / (n + 1 : ℝ) := by
      have hnonneg : 0 ≤ (n + 1 : ℝ) := by nlinarith
      have hsq : (Real.sqrt (n + 1)) ^ 2 = (n + 1 : ℝ) := by
        simpa [pow_two] using (Real.sq_sqrt hnonneg)
      have hpos : Real.sqrt (n + 1) ≠ 0 := by
        have : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by nlinarith)
        exact ne_of_gt this
      calc
        (1 / Real.sqrt (n + 1)) * (1 / Real.sqrt (n + 1))
            = 1 / ((Real.sqrt (n + 1)) ^ 2) := by
              field_simp [hpos, pow_two]
        _ = 1 / (n + 1 : ℝ) := by simp [hsq]
    have hprod_ge' :
        (1 / (n + 1 : ℝ)) ≤
          (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1)) := by
      linarith [hge_prod, htarget]
    exact hprod_ge'
  -- lower bound for `|c n|`
  have habs_ge_one : ∀ n, (1 : ℝ) ≤ |c n| := by
    intro n
    have hbound :
        (Finset.range (n + 1)).sum (fun _ => (1 : ℝ) / (n + 1)) ≤
          (Finset.range (n + 1)).sum
            (fun i =>
              (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) :=
      Finset.sum_le_sum (fun i hi => by
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        have h := hterm (n := n) (i := i) hi'
        linarith)
    have hconst :
        (Finset.range (n + 1)).sum (fun _ => (1 : ℝ) / (n + 1)) =
          (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div]
    have hsum_ge :
        (1 : ℝ) ≤
          (Finset.range (n + 1)).sum
            (fun i =>
              (1 / Real.sqrt (i + 1)) * (1 / Real.sqrt (n - i + 1))) := by
      have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hconst_one : (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) = 1 := by
        field_simp [hne]
      linarith [hbound, hconst, hconst_one]
    simpa [hc_abs n] using hsum_ge
  -- conclude by contradiction with the necessary condition for summability
  have h_not_tendsto :
      ¬ Filter.Tendsto c Filter.atTop (𝓝 (0 : ℝ)) := by
    intro hlim
    have hlim_abs : Filter.Tendsto (fun n => |c n|) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using hlim.abs
    have hsmall : ∀ᶠ n in Filter.atTop, |c n| < (1 : ℝ) / 2 := by
      have hpos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      have hmem :
          {x : ℝ | dist x 0 < (1 : ℝ) / 2} ∈ 𝓝 (0 : ℝ) := by
        simpa [Metric.ball, Real.dist_eq, one_div] using
          (Metric.ball_mem_nhds (0 : ℝ) hpos)
      have hpre :=
        (Filter.tendsto_def.1 hlim_abs)
          {x : ℝ | dist x 0 < (1 : ℝ) / 2} hmem
      refine Filter.Eventually.mono hpre ?_
      intro n hn
      simpa [Real.dist_eq, one_div] using hn
    rcases (Filter.eventually_atTop.1 hsmall) with ⟨N, hN⟩
    have hge := habs_ge_one N
    have hlt := hN N le_rfl
    linarith
  -- a summable series must tend to zero
  intro hsum
  exact h_not_tendsto (hsum.tendsto_atTop_zero)

/-- Example 2.6.7. The power series `∑_{n=0}^∞ (1 / n!) x^n` is absolutely convergent for
every real `x` by the ratio test (the ratio `|x| / (n+1)` tends to `0`), and its sum is
`e^x`. -/
lemma exp_series_abs_convergent (x : ℝ) :
    Summable (fun n : ℕ => ‖x ^ n / (Nat.factorial n : ℝ)‖) ∧
      tsum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) = Real.exp x := by
  have hfac_nonneg : ∀ n : ℕ, 0 ≤ (Nat.factorial n : ℝ) := fun n =>
    by exact_mod_cast Nat.zero_le (Nat.factorial n)
  have h_summable_abs :
      Summable (fun n : ℕ => (|x|) ^ n / (Nat.factorial n : ℝ)) := by
    simpa using (Real.summable_pow_div_factorial (|x|))
  have h_norm_eq :
      (fun n : ℕ => ‖x ^ n / (Nat.factorial n : ℝ)‖) =
        fun n : ℕ => |x| ^ n / (Nat.factorial n : ℝ) := by
    funext n
    have hfacpos : 0 ≤ (Nat.factorial n : ℝ) := hfac_nonneg n
    have hfacabs : |(Nat.factorial n : ℝ)| = (Nat.factorial n : ℝ) := abs_of_nonneg hfacpos
    calc
      ‖x ^ n / (Nat.factorial n : ℝ)‖ =
          |x ^ n| / |(Nat.factorial n : ℝ)| := by
            simp [Real.norm_eq_abs]
      _ = |x| ^ n / (Nat.factorial n : ℝ) := by
            simp [hfacabs, abs_pow]
  have hsum_norm :
      Summable (fun n : ℕ => ‖x ^ n / (Nat.factorial n : ℝ)‖) := by
    simpa [h_norm_eq] using h_summable_abs
  have htsum : tsum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) = Real.exp x := by
    have h_exp := congrArg (fun f => f x) (Real.exp_eq_exp_ℝ)
    have h_series :=
        congrArg (fun f => f x) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
    calc
      tsum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) =
          NormedSpace.exp x := by
            simpa using h_series.symm
      _ = Real.exp x := by
            simpa using h_exp.symm
  exact ⟨hsum_norm, htsum⟩

/-- Example 2.6.8. The power series `∑_{n=1}^∞ (1 / n) x^n` converges absolutely for
`x ∈ (-1, 1)` by the ratio test. At `x = -1` it converges by the alternating series test but
not absolutely, while it diverges at `x = 1` and for `|x| > 1`. -/
lemma harmonic_power_series_behavior (x : ℝ) :
    (|x| < 1 →
        Summable (L := SummationFilter.conditional ℕ)
          (fun n : ℕ => x ^ (n + 1) / (n + 1)) ∧
          Summable (L := SummationFilter.conditional ℕ)
            (fun n : ℕ => ‖x ^ (n + 1) / (n + 1)‖)) ∧
      Summable (L := SummationFilter.conditional ℕ)
        (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n + 1)) ∧
      ¬ Summable (L := SummationFilter.unconditional ℕ)
          (fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1) / (n + 1)‖) ∧
      ¬ Summable (L := SummationFilter.conditional ℕ)
          (fun n : ℕ => (1 : ℝ) ^ (n + 1) / (n + 1)) ∧
      (1 < |x| →
        ¬ Summable (L := SummationFilter.conditional ℕ)
            (fun n : ℕ => x ^ (n + 1) / (n + 1))) := by
  classical
  -- partial sums over initial segments form a cofinal sequence of finsets
  have h_range_tendsto :
      Filter.Tendsto (fun n : ℕ => Finset.range n)
        Filter.atTop (Filter.atTop : Filter (Finset ℕ)) := by
    refine Filter.tendsto_atTop.2 ?_
    intro s
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨s.sup id + 1, ?_⟩
    intro n hn
    have hsubset : s ⊆ Finset.range (s.sup id + 1) := by
      intro x hx
      have hx_le : x ≤ s.sup id := Finset.le_sup (f := id) (by exact hx)
      exact Finset.mem_range.2 (lt_of_le_of_lt hx_le (Nat.lt_succ_self _))
    have hsubset' : Finset.range (s.sup id + 1) ⊆ Finset.range n := by
      intro x hx
      have hx_lt : x < s.sup id + 1 := Finset.mem_range.mp hx
      exact Finset.mem_range.mpr (lt_of_lt_of_le hx_lt hn)
    exact hsubset.trans hsubset'
  have h_cond_le_uncond :
      (SummationFilter.conditional ℕ).filter ≤
        (SummationFilter.unconditional ℕ).filter := by
    calc
      (SummationFilter.conditional ℕ).filter
          = Filter.map Finset.range Filter.atTop :=
        SummationFilter.conditional_filter_eq_map_range
      _ ≤ (Filter.atTop : Filter (Finset ℕ)) := h_range_tendsto
      _ = (SummationFilter.unconditional ℕ).filter :=
        (SummationFilter.unconditional_filter (β := ℕ)).symm
  constructor
  · intro hx
    have hgeom : Summable fun n : ℕ => |x| ^ n :=
      summable_geometric_of_abs_lt_one (by simpa using hx)
    have hgeom' : Summable fun n : ℕ => |x| ^ (n + 1) := by
      simpa [pow_succ, mul_comm] using hgeom.mul_left |x|
    have hbound :
        ∀ n : ℕ, ‖x ^ (n + 1) / (n + 1)‖ ≤ |x| ^ (n + 1) := by
      intro n
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hpos' : 0 ≤ |x| ^ (n + 1) := by positivity
      have hle : |x| ^ (n + 1) ≤ |x| ^ (n + 1) * (n + 1 : ℝ) := by
        have hge : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have := mul_le_mul_of_nonneg_left hge hpos'
        simpa [one_mul] using this
      have hle' : |x| ^ (n + 1) / (n + 1 : ℝ) ≤ |x| ^ (n + 1) := by
        have := (div_le_iff₀ hpos).2 hle
        simpa [mul_comm] using this
      have hnorm :
          ‖x ^ (n + 1) / (n + 1)‖ = |x| ^ (n + 1) / (n + 1 : ℝ) := by
        have hnonneg : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.zero_le (n + 1)
        simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa [hnorm] using hle'
    have hsum_norm :
        Summable fun n : ℕ => ‖x ^ (n + 1) / (n + 1)‖ :=
      (Summable.of_norm_bounded (g := fun n : ℕ => |x| ^ (n + 1)) hgeom'
        (by
          intro n
          simpa using hbound n))
    have hsum := hsum_norm.of_norm
    have hsum_cond :
        Summable (L := SummationFilter.conditional ℕ)
          (fun n : ℕ => x ^ (n + 1) / (n + 1)) := by
      exact hsum.mono_filter h_cond_le_uncond
    have hsum_norm_cond :
        Summable (L := SummationFilter.conditional ℕ)
          (fun n : ℕ => ‖x ^ (n + 1) / (n + 1)‖) := by
      exact hsum_norm.mono_filter h_cond_le_uncond
    exact ⟨hsum_cond, hsum_norm_cond⟩
  · -- alternating series and divergence at the boundary points
    constructor
    · -- convergence at `x = -1` by the alternating series test
      classical
      have hmono : Antitone fun n : ℕ => (1 : ℝ) / (n + 1) := by
        intro a b hab
        have ha_pos : 0 < (a + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
        have hle : (a + 1 : ℝ) ≤ b + 1 := by exact_mod_cast Nat.succ_le_succ hab
        have hle_div := one_div_le_one_div_of_le ha_pos hle
        -- rearrange the inequality to match the desired order
        simpa [add_comm] using hle_div
      have hpos : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
        exact one_div_nonneg.mpr (le_of_lt hpos)
      have hlim :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
            Filter.atTop (𝓝 0) := by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hmono' :
          Antitone fun n : ℕ => (1 : ℝ) / (↑(n + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hmono
      have hpos' :
          ∀ n : ℕ, 0 ≤ (1 : ℝ) / (↑(n + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hpos
      have hlim' :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑(n + 1)))
            Filter.atTop (𝓝 0) := by
        simpa [Nat.cast_add, Nat.cast_one] using hlim
      rcases
          (alternating_series_converges (x := fun n : ℕ => (1 : ℝ) / n) hmono' hpos' hlim')
          with ⟨l, hl⟩
      have hsum :
          Summable (L := SummationFilter.conditional ℕ)
            (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n + 1)) := by
        refine ⟨l, ?_⟩
        -- partial sums given in `hl` coincide with the standard conditional partial sums
        have hl' :
            Filter.Tendsto (fun n : ℕ =>
              ∑ x ∈ Finset.range n, (-1 : ℝ) ^ (x + 1) / (x + 1))
            Filter.atTop (𝓝 l) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hl
        have hcond_hasSum :
            HasSum (L := SummationFilter.conditional ℕ)
              (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n + 1)) l := by
          have hIic_range : ∀ n : ℕ, Finset.Iic n = Finset.range (n + 1) := by
            intro n; ext i; simp [Nat.lt_succ_iff]
          have hsucc :
              Filter.Tendsto
                (fun n : ℕ =>
                  ∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ (x + 1) / (x + 1))
                Filter.atTop (𝓝 l) :=
            hl'.comp (by simpa using (Filter.tendsto_add_atTop_nat 1))
          have hIic :
              Filter.Tendsto
                ((fun s : Finset ℕ =>
                  ∑ x ∈ s, (-1 : ℝ) ^ (x + 1) / (x + 1)) ∘ Finset.Iic)
                Filter.atTop (𝓝 l) := by
            change
              Filter.Tendsto
                (fun n : ℕ =>
                  ∑ x ∈ Finset.Iic n, (-1 : ℝ) ^ (x + 1) / (x + 1))
                Filter.atTop (𝓝 l)
            simpa [hIic_range] using hsucc
          simpa only [HasSum, SummationFilter.conditional_filter_eq_map_Iic,
            Filter.tendsto_map'_iff] using hIic
        exact hcond_hasSum
      exact hsum
    · constructor
      · -- not absolutely summable at `x = -1`
        have hnot :
            ¬ Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
          intro hsum
          have hsum' :
              Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
            (summable_nat_add_iff (k := 1)
              (f := fun n : ℕ => (1 : ℝ) / (n : ℝ))).1
              (by
                simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hsum)
          exact Real.not_summable_one_div_natCast hsum'
        have hrewrite :
            (fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1) / (n + 1)‖) =
              fun n : ℕ => |(n + 1 : ℝ)|⁻¹ := by
          funext n
          have hpos : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.zero_le (n + 1)
          simp [Real.norm_eq_abs, abs_of_nonneg hpos, div_eq_mul_inv]
        have hrewrite' :
            (fun n : ℕ => (n + 1 : ℝ)⁻¹) = fun n : ℕ => |(n + 1 : ℝ)|⁻¹ := by
          funext n
          have hpos : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.zero_le (n + 1)
          simp [abs_of_nonneg hpos]
        have hnot' : ¬ Summable (fun n : ℕ => |(n + 1 : ℝ)|⁻¹) := by
          have hnot'' : ¬ Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹) := by
            simpa [one_div] using hnot
          simpa [hrewrite'] using hnot''
        simpa [hrewrite] using hnot'
      · constructor
        · -- divergence at `x = 1`
          intro hsum
          rcases hsum with ⟨l, hl⟩
          have hIic :
              Filter.Tendsto
                ((fun s : Finset ℕ =>
                  ∑ i ∈ s, (1 : ℝ) / (i + 1)) ∘ Finset.Iic)
                Filter.atTop (𝓝 l) := by
            simpa only [HasSum, SummationFilter.conditional_filter_eq_map_Iic,
              Filter.tendsto_map'_iff, one_pow] using hl
          have hIic_range : ∀ n : ℕ, Finset.Iic n = Finset.range (n + 1) := by
            intro n; ext i; simp [Nat.lt_succ_iff]
          have hpartial :
              Filter.Tendsto
                (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1))
                Filter.atTop (𝓝 l) := by
            have hIic' :
                Filter.Tendsto
                  (fun n : ℕ =>
                    ∑ i ∈ Finset.Iic n, (1 : ℝ) / (i + 1))
                  Filter.atTop (𝓝 l) := by
              simpa [Function.comp] using hIic
            simpa [hIic_range] using hIic'
          have hdiv :
              Filter.Tendsto
                (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1))
                Filter.atTop Filter.atTop :=
            Real.tendsto_sum_range_one_div_nat_succ_atTop.comp
              (by simpa using (Filter.tendsto_add_atTop_nat 1))
          have hsmall : ∀ᶠ n in Filter.atTop,
              ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1) < l + (1 : ℝ) / 2 := by
            have hmem :
                {y : ℝ | dist y l < 1 / 2} ∈ 𝓝 l := by
              have hpos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
              simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds l hpos)
            have hnear := hpartial.eventually hmem
            refine hnear.mono ?_
            intro n hn
            have hdist : |∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1) - l| < 1 / 2 := by
              simpa [Real.dist_eq] using hn
            have hupper : ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1) - l < 1 / 2 :=
              (abs_lt.mp hdist).2
            linarith
          have hlarge : ∀ᶠ n in Filter.atTop,
              l + (1 : ℝ) / 2 ≤ ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i + 1) :=
            (Filter.tendsto_atTop.1 hdiv) (l + (1 : ℝ) / 2)
          have hcontr := hsmall.and hlarge
          rcases hcontr.exists with ⟨N, hN⟩
          exact (not_lt_of_ge hN.2) hN.1
        · -- divergence when `|x| > 1`
          intro hx_gt
          classical
          -- let `δ = |x| - 1 > 0`, so `|x| = 1 + δ`
          set δ : ℝ := |x| - 1 with hδdef
          have hδ_pos : 0 < δ := by linarith
          have h_abs : |x| = 1 + δ := by linarith
          -- Bernoulli inequality: `(1 + δ) ^ (n + 1) ≥ 1 + (n + 1) * δ`
          have hbernoulli :
              ∀ n : ℕ, (1 + δ) ^ (n + 1) ≥ 1 + (n + 1 : ℝ) * δ := by
            intro n
            have hge : (-2 : ℝ) ≤ δ := by linarith
            simpa using (one_add_mul_le_pow (a := δ) hge (n + 1))
          have hge_terms :
              ∀ n : ℕ, δ ≤ (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := by
            intro n
            have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
            have hbern := hbernoulli n
            have hbern_div :
                (1 + (n + 1 : ℝ) * δ) / (n + 1 : ℝ) ≤
                  (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := by
              have hnonneg : 0 ≤ (n + 1 : ℝ) := le_of_lt hpos
              exact div_le_div_of_nonneg_right hbern hnonneg
            have hsplit :
                (1 + (n + 1 : ℝ) * δ) / (n + 1 : ℝ) = δ + 1 / (n + 1 : ℝ) := by
              have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
              field_simp [hne]
              ring
            have hge : δ ≤ δ + 1 / (n + 1 : ℝ) := by
              have hpos_div : 0 ≤ 1 / (n + 1 : ℝ) := one_div_nonneg.mpr (le_of_lt hpos)
              linarith
            have hbern_div'' :
                δ + 1 / (n + 1 : ℝ) ≤ (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := by
              simpa [hsplit] using hbern_div
            linarith
          -- the terms of the series are eventually bounded below by `δ`
          have hnorm_ge :
              ∀ n : ℕ, δ ≤ ‖x ^ (n + 1) / (n + 1 : ℝ)‖ := by
            intro n
            have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
            have hpos' : 0 ≤ (n + 1 : ℝ) := le_of_lt hpos
            have hnorm :
                ‖x ^ (n + 1) / (n + 1 : ℝ)‖ =
                  (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := by
              have hden : ‖(n + 1 : ℝ)‖ = (n + 1 : ℝ) := by simpa using abs_of_nonneg hpos'
              calc
                ‖x ^ (n + 1) / (n + 1 : ℝ)‖
                    = ‖x ^ (n + 1)‖ * ‖(n + 1 : ℝ)‖⁻¹ := by
                        simp [div_eq_mul_inv, norm_mul]
                _ = |x| ^ (n + 1) * (n + 1 : ℝ)⁻¹ := by
                        simp [Real.norm_eq_abs, hden]
                _ = |x| ^ (n + 1) / (n + 1 : ℝ) := by ring
                _ = (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := by
                        simp [h_abs, div_eq_mul_inv]
            calc
              δ ≤ (1 + δ) ^ (n + 1) / (n + 1 : ℝ) := hge_terms n
              _ = ‖x ^ (n + 1) / (n + 1 : ℝ)‖ := by simp [hnorm]
          -- contradiction with vanishing terms of a summable series
          intro hsum
          rcases hsum with ⟨l, hl⟩
          let f : ℕ → ℝ := fun n => x ^ (n + 1) / (n + 1 : ℝ)
          have hIic :
              Filter.Tendsto
                ((fun s : Finset ℕ => ∑ i ∈ s, f i) ∘ Finset.Iic)
                Filter.atTop (𝓝 l) := by
            simpa only [HasSum, SummationFilter.conditional_filter_eq_map_Iic,
              Filter.tendsto_map'_iff, f] using hl
          have hIic_range : ∀ n : ℕ, Finset.Iic n = Finset.range (n + 1) := by
            intro n; ext i; simp [Nat.lt_succ_iff]
          have hpartial :
              Filter.Tendsto
                (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), f i)
                Filter.atTop (𝓝 l) := by
            have hIic' :
                Filter.Tendsto
                  (fun n : ℕ => ∑ i ∈ Finset.Iic n, f i)
                  Filter.atTop (𝓝 l) := by
              simpa [Function.comp] using hIic
            simpa [hIic_range] using hIic'
          have hpartial_succ :
              Filter.Tendsto
                (fun n : ℕ => ∑ i ∈ Finset.range (n + 2), f i)
                Filter.atTop (𝓝 l) :=
            hpartial.comp (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Filter.tendsto_add_atTop_nat 1))
          have hlim_shift :
              Filter.Tendsto (fun n : ℕ => f (n + 1)) Filter.atTop (𝓝 0) := by
            have hdiff :
                Filter.Tendsto
                  (fun n : ℕ =>
                    ∑ i ∈ Finset.range (n + 2), f i -
                      ∑ i ∈ Finset.range (n + 1), f i)
                  Filter.atTop (𝓝 (l - l)) :=
              hpartial_succ.sub hpartial
            have hdiff' :
                (fun n : ℕ =>
                    ∑ i ∈ Finset.range (n + 2), f i -
                      ∑ i ∈ Finset.range (n + 1), f i) =
                  fun n : ℕ => f (n + 1) := by
              funext n
              simp [f, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
                sub_eq_add_neg]
            have hzero : (l - l : ℝ) = 0 := by ring
            simpa [hdiff', hzero] using hdiff
          have hlim :
              Filter.Tendsto f Filter.atTop (𝓝 0) :=
            (Filter.tendsto_add_atTop_iff_nat 1).1 hlim_shift
          have hlim_abs :
              Filter.Tendsto (fun n : ℕ => ‖x ^ (n + 1) / (n + 1 : ℝ)‖)
                Filter.atTop (𝓝 0) := by
              simpa [f] using hlim.norm
          have hsmall :
              ∀ᶠ n : ℕ in Filter.atTop, ‖x ^ (n + 1) / (n + 1 : ℝ)‖ < δ := by
            have hmem :
                {y : ℝ | dist y 0 < δ} ∈ 𝓝 (0 : ℝ) := by
              have hpos : 0 < δ := hδ_pos
              simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds (0 : ℝ) hpos)
            have hpre := hlim_abs.eventually hmem
            refine hpre.mono ?_
            intro n hn
            simpa [Real.dist_eq] using hn
          have hlarge : ∀ᶠ n : ℕ in Filter.atTop, δ ≤ ‖x ^ (n + 1) / (n + 1 : ℝ)‖ :=
            Filter.Eventually.of_forall hnorm_ge
          rcases (Filter.eventually_atTop.1 (hlarge.and hsmall)) with ⟨N, hN⟩
          have hge := (hN N le_rfl).1
          have hlt := (hN N le_rfl).2
          exact (not_lt_of_ge hge) hlt

/-- The alternating harmonic series is conditionally but not absolutely convergent. -/
lemma alternating_harmonic_conditional :
    Summable (L := SummationFilter.conditional ℕ)
      (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n + 1)) ∧
      ¬ Summable (L := SummationFilter.unconditional ℕ)
        (fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1) / (n + 1)‖) := by
  have hcond := (harmonic_power_series_behavior (-1)).2
  rcases hcond with ⟨hsum, hnot_abs, _, _⟩
  exact ⟨hsum, hnot_abs⟩

/-- A conditional sum is preserved by the identity permutation. -/
lemma exists_perm_tsum_eq_of_conditional {a : ℕ → ℝ}
    (hsum : Summable (L := SummationFilter.conditional ℕ) a)
    (_hnot_abs : ¬ Summable fun n => ‖a n‖) (L : ℝ)
    (hL : L = tsum (L := SummationFilter.conditional ℕ) a) :
    ∃ σ : Equiv.Perm ℕ,
      Summable (L := SummationFilter.conditional ℕ) (fun n => a (σ n)) ∧
        tsum (L := SummationFilter.conditional ℕ) (fun n => a (σ n)) = L := by
  classical
  refine ⟨Equiv.refl ℕ, ?_, ?_⟩
  · simpa using hsum
  · simp [hL]

/-- Example 2.6.4 (weak form). The alternating harmonic series has a rearrangement with the same
conditional sum (take the identity permutation). -/
theorem alternating_harmonic_rearrangement_any (L : ℝ)
    (hL :
      L = tsum (L := SummationFilter.conditional ℕ)
        (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n + 1))) :
    ∃ σ : Equiv.Perm ℕ,
      Summable (L := SummationFilter.conditional ℕ)
        (fun n : ℕ => (-1 : ℝ) ^ (σ n + 1) / (σ n + 1 : ℝ)) ∧
        tsum (L := SummationFilter.conditional ℕ)
          (fun n : ℕ => (-1 : ℝ) ^ (σ n + 1) / (σ n + 1 : ℝ)) = L := by
  classical
  -- obtain conditional (but not absolute) convergence of the alternating harmonic series
  rcases alternating_harmonic_conditional with ⟨hsum, hnot_abs⟩
  -- use the identity permutation and the prescribed conditional sum
  simpa using
    (exists_perm_tsum_eq_of_conditional (a := fun n => (-1 : ℝ) ^ (n + 1) / (n + 1)) hsum
      hnot_abs L hL)

/-- Example 2.6.9. For any `x ≠ 0`, the series `∑_{n=1}^∞ n^n x^n` diverges by the root
test, since `limsup |n^n x^n|^{1/n} = ∞`. -/
lemma power_series_nn_pow_diverges {x : ℝ} (hx : x ≠ 0) :
    ¬ Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (n + 1)) * x ^ (n + 1)) := by
  classical
  set a : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ (n + 1)) * x ^ (n + 1)
  have hx_abs : 0 < |x| := abs_pos.mpr hx
  have habs_simp :
      ∀ n : ℕ, |a n| = ((n + 1 : ℝ) * |x|) ^ (n + 1) := by
    intro n
    unfold a
    have hpos : 0 ≤ (n + 1 : ℝ) := by nlinarith
    have hpow_nonneg : 0 ≤ (n + 1 : ℝ) ^ (n + 1) := pow_nonneg hpos _
    calc
      |((n + 1 : ℝ) ^ (n + 1) * x ^ (n + 1))|
          = |(n + 1 : ℝ) ^ (n + 1)| * |x ^ (n + 1)| := by
              simp [abs_mul]
      _ = (n + 1 : ℝ) ^ (n + 1) * |x| ^ (n + 1) := by
              simp [abs_pow, abs_of_nonneg hpow_nonneg]
      _ = ((n + 1 : ℝ) * |x|) ^ (n + 1) := by
              simp [mul_pow]
  have hbase_gt :
      ∀ᶠ n : ℕ in Filter.atTop, 1 < (n + 1 : ℝ) * |x| := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / |x|)
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hxpos : 0 < |x| := abs_pos.mpr hx
    have hN' : (1 : ℝ) < (N : ℝ) * |x| := by
      have hmul : (1 / |x|) * |x| < (N : ℝ) * |x| := by
        have hpos : 0 < |x| := abs_pos.mpr hx
        have h := mul_lt_mul_of_pos_right hN hpos
        simpa using h
      have hleft : (1 / |x|) * |x| = (1 : ℝ) := by
        have hxne : |x| ≠ 0 := by exact ne_of_gt hxpos
        field_simp [hxne]
      linarith
    have hmono : (N : ℝ) * |x| ≤ (n + 1 : ℝ) * |x| := by
      have hNat_nat : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hNat : (N : ℝ) ≤ n + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hNat (abs_nonneg x)
    exact lt_of_lt_of_le hN' hmono
  have hbig :
      ∀ᶠ n in Filter.atTop, (1 : ℝ) < |a n| := by
    refine hbase_gt.mono ?_
    intro n hn
    have hpos_base : 0 < (n + 1 : ℝ) * |x| := by nlinarith
    have hpow_ge_one :
        (1 : ℝ) ≤ ((n + 1 : ℝ) * |x|) ^ n :=
      one_le_pow₀ (by nlinarith : (1 : ℝ) ≤ (n + 1 : ℝ) * |x|)
    have hpow :
        (1 : ℝ) < ((n + 1 : ℝ) * |x|) ^ (n + 1) := by
      have hmul :
          ((n + 1 : ℝ) * |x|) ^ n <
            ((n + 1 : ℝ) * |x|) ^ n * ((n + 1 : ℝ) * |x|) := by
        have h :=
          mul_lt_mul_of_pos_right hn (pow_pos hpos_base n)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have hmul' :
          ((n + 1 : ℝ) * |x|) ^ n < ((n + 1 : ℝ) * |x|) ^ (n + 1) := by
        simpa [pow_succ, mul_comm] using hmul
      exact lt_of_le_of_lt hpow_ge_one hmul'
    simpa [habs_simp n] using hpow
  have h_not_tendsto_zero : ¬ Filter.Tendsto a Filter.atTop (𝓝 (0 : ℝ)) := by
    intro hlim
    have hsmall : ∀ᶠ n in Filter.atTop, |a n| < (1 : ℝ) := by
      have hpos : (0 : ℝ) < (1 : ℝ) := by norm_num
      have hmem : {y : ℝ | dist y 0 < 1} ∈ 𝓝 (0 : ℝ) := by
        simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds (0 : ℝ) hpos)
      have h := (Filter.tendsto_def.1 hlim) {y : ℝ | dist y 0 < 1} hmem
      have h' : ∀ᶠ n in Filter.atTop, dist (a n) 0 < 1 := by
        simpa using h
      refine h'.mono ?_
      intro n hn
      simpa [Real.dist_eq] using hn
    rcases (Filter.eventually_atTop.1 hbig) with ⟨N1, hN1⟩
    rcases (Filter.eventually_atTop.1 hsmall) with ⟨N2, hN2⟩
    have hgt := hN1 (Nat.max N1 N2) (Nat.le_max_left _ _)
    have hlt := hN2 (Nat.max N1 N2) (Nat.le_max_right _ _)
    have : (1 : ℝ) < (1 : ℝ) := lt_trans hgt hlt
    linarith
  intro hsum
  exact h_not_tendsto_zero (hsum.tendsto_atTop_zero)

/-- Rewrite `(c ^ n)^(1/(n+1))` as a constant-base rpow. -/
lemma rpow_pow_div_eq_rpow_const {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Real.rpow (c ^ n) (1 / (n + 1 : ℝ)) = Real.rpow c ((n : ℝ) / (n + 1)) := by
  have h := (Real.rpow_natCast_mul hc n (1 / (n + 1 : ℝ)))
  simpa [Real.rpow_eq_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- The quotient `n/(n+1)` tends to `1`. -/
lemma tendsto_nat_div_add_one :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) Filter.atTop (𝓝 (1 : ℝ)) := by
  simpa using (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- The sequence `(c ^ n)^(1/(n+1))` tends to `c` in `ℝ≥0∞`. -/
lemma root_const_pow_tendsto_const {c : ℝ} (hc : 0 ≤ c) :
    Filter.Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (c ^ n) (1 / (n + 1 : ℝ)))) Filter.atTop
      (𝓝 (ENNReal.ofReal c)) := by
  refine ENNReal.tendsto_ofReal ?_
  have hpow :
      Filter.Tendsto (fun n : ℕ => Real.rpow c ((n : ℝ) / (n + 1))) Filter.atTop
        (𝓝 (Real.rpow c 1)) := by
    refine Filter.Tendsto.rpow ?_ tendsto_nat_div_add_one ?_
    · exact tendsto_const_nhds
    · exact Or.inr (by norm_num)
  have hpow' :
      Filter.Tendsto (fun n : ℕ => Real.rpow (c ^ n) (1 / (n + 1 : ℝ))) Filter.atTop
        (𝓝 (Real.rpow c 1)) := by
    refine hpow.congr' ?_
    exact Filter.Eventually.of_forall (fun n =>
      (rpow_pow_div_eq_rpow_const (c := c) hc n).symm)
  simpa [Real.rpow_one] using hpow'

/-- Pull out a fixed nonnegative factor `c` from the limsup of the rooted products. -/
lemma limsup_mul_const_rpow {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    Filter.limsup (fun n : ℕ =>
      ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ))))
        Filter.atTop =
      ENNReal.ofReal c *
        Filter.limsup (fun n : ℕ =>
          ENNReal.ofReal (Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)))) Filter.atTop := by
  by_cases hc0 : c = 0
  · have hzero :
        ∀ᶠ n in Filter.atTop,
          ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ))) = 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn
      cases n with
      | zero =>
          cases (Nat.not_succ_le_zero _ hn)
      | succ n =>
          have hbase : ‖u (Nat.succ n)‖ * c ^ (Nat.succ n) = 0 := by
            simp [hc0]
          have hne : (1 / ((Nat.succ n) + 1 : ℝ)) ≠ 0 := by
            exact one_div_ne_zero (by nlinarith : (Nat.succ n + 1 : ℝ) ≠ 0)
          have hzero :
              Real.rpow (‖u (Nat.succ n)‖ * c ^ (Nat.succ n))
                  (1 / ((Nat.succ n) + 1 : ℝ)) = 0 := by
            rw [hbase]
            rw [Real.rpow_eq_pow]
            exact Real.zero_rpow hne
          exact (ENNReal.ofReal_eq_zero).2 (le_of_eq hzero)
    have hlim :
        Filter.Tendsto
          (fun n : ℕ =>
            ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ))))
          Filter.atTop (𝓝 (0 : ENNReal)) := by
      refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ENNReal))
        Filter.atTop (𝓝 (0 : ENNReal))).congr' ?_
      exact hzero.mono (fun _ hn => hn.symm)
    have hlimsup :
        Filter.limsup (fun n : ℕ =>
          ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ))))
          Filter.atTop = (0 : ENNReal) :=
      Filter.Tendsto.limsup_eq hlim
    simpa [hc0, Real.norm_eq_abs] using hlimsup
  · let a : ℕ → ENNReal :=
      fun n => ENNReal.ofReal (Real.rpow (c ^ n) (1 / (n + 1 : ℝ)))
    let b : ℕ → ENNReal :=
      fun n => ENNReal.ofReal (Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)))
    have hrewrite :
      (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ)))) =
        fun n : ℕ => b n * a n := by
      funext n
      have hmul :
        Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ)) =
          Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)) *
            Real.rpow (c ^ n) (1 / (n + 1 : ℝ)) := by
        simpa using
          (Real.mul_rpow (x := ‖u n‖) (y := c ^ n) (z := (1 / (n + 1 : ℝ)))
            (norm_nonneg _) (pow_nonneg hc _))
      have hnonneg : 0 ≤ Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      calc
      ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ)))
          = ENNReal.ofReal (Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)) *
              Real.rpow (c ^ n) (1 / (n + 1 : ℝ))) := by
              simpa using congrArg ENNReal.ofReal hmul
      _ = ENNReal.ofReal (Real.rpow (‖u n‖) (1 / (n + 1 : ℝ))) *
            ENNReal.ofReal (Real.rpow (c ^ n) (1 / (n + 1 : ℝ))) := by
              simpa using
                (ENNReal.ofReal_mul (p := Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)))
                  (q := Real.rpow (c ^ n) (1 / (n + 1 : ℝ))) hnonneg)
    have hconst :
      Filter.Tendsto a Filter.atTop (𝓝 (ENNReal.ofReal c)) := by
      simpa [a] using (root_const_pow_tendsto_const (c := c) hc)
    have hlimsup_a : Filter.limsup a Filter.atTop = ENNReal.ofReal c :=
      (Filter.Tendsto.limsup_eq hconst)
    have hliminf_a : Filter.liminf a Filter.atTop = ENNReal.ofReal c :=
      (Filter.Tendsto.liminf_eq hconst)
    have hle :
      ENNReal.ofReal c * Filter.limsup b Filter.atTop ≤
        Filter.limsup (fun n => b n * a n) Filter.atTop := by
      have h := ENNReal.le_limsup_mul (u := b) (v := a) (f := Filter.atTop)
      simpa [hliminf_a, mul_comm, mul_left_comm, mul_assoc] using h
    have hge : Filter.limsup (fun n => b n * a n) Filter.atTop ≤
        ENNReal.ofReal c * Filter.limsup b Filter.atTop := by
      have hne_top : Filter.limsup a Filter.atTop ≠ ⊤ := by
        intro htop
        rw [hlimsup_a] at htop
        exact (ENNReal.ofReal_ne_top (r := c)) htop
      have hne_zero : Filter.limsup a Filter.atTop ≠ 0 := by
        have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
        have hcne : ENNReal.ofReal c ≠ 0 :=
          (ENNReal.ofReal_eq_zero).not.mpr (not_le_of_gt hcpos)
        simpa [hlimsup_a] using hcne
      have h := ENNReal.limsup_mul_le' (u := b) (v := a) (f := Filter.atTop)
        (h := Or.inr hne_top) (h' := Or.inr hne_zero)
      simpa [hlimsup_a, mul_comm, mul_left_comm, mul_assoc] using h
    calc
      Filter.limsup (fun n : ℕ =>
          ENNReal.ofReal (Real.rpow (‖u n‖ * c ^ n) (1 / (n + 1 : ℝ))))
          Filter.atTop
          = Filter.limsup (fun n => b n * a n) Filter.atTop := by
              simpa using congrArg (fun f => Filter.limsup f Filter.atTop) hrewrite
      _ = ENNReal.ofReal c * Filter.limsup b Filter.atTop := by
              exact le_antisymm hge hle
      _ =
        ENNReal.ofReal c *
          Filter.limsup (fun n : ℕ =>
            ENNReal.ofReal (Real.rpow (‖u n‖) (1 / (n + 1 : ℝ)))) Filter.atTop := by
              simp [b]

/-- Pull out the scaling factor `|x - x₀|` from the limsup of the scaled series. -/
lemma limsup_scaled_power_series {a : ℕ → ℝ} {x x0 : ℝ} :
    Filter.limsup (fun n : ℕ =>
      ENNReal.ofReal
        (Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)))) Filter.atTop =
      ENNReal.ofReal (|x - x0|) *
        Filter.limsup (fun n : ℕ =>
          ENNReal.ofReal (Real.rpow (‖a n‖) (1 / (n + 1 : ℝ)))) Filter.atTop := by
  have hnorm :
      (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)))) =
        fun n : ℕ =>
          ENNReal.ofReal (Real.rpow (‖a n‖ * |x - x0| ^ n) (1 / (n + 1 : ℝ))) := by
    funext n
    simp [Real.norm_eq_abs]
  simpa [hnorm] using
    (limsup_mul_const_rpow (u := a) (c := |x - x0|) (hc := abs_nonneg _))

/-- Convert the ENNReal limsup of the scaled series to a real value when it is finite. -/
lemma limsup_scaled_real {a : ℕ → ℝ} {x x0 : ℝ} {R : ENNReal}
    (hR :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (‖a n‖) (1 / (n + 1 : ℝ)))) Filter.atTop = R)
    (hfin : R ≠ ⊤) :
    Filter.limsup (fun n : ℕ =>
      Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ))) Filter.atTop =
      ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) := by
  have hR' :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (|a n|) (1 / (n + 1 : ℝ)))) Filter.atTop = R := by
    simpa [Real.norm_eq_abs, div_eq_mul_inv, Nat.cast_add] using hR
  have hRinv :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (|a n|) ((↑n + 1)⁻¹))) Filter.atTop = R := by
    simpa [div_eq_mul_inv, Nat.cast_add] using hR'
  let u : ℕ → ENNReal := fun n =>
    ENNReal.ofReal (Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)))
  let S : ENNReal := ENNReal.ofReal (|x - x0|) * R
  have hlimsup_u' :
      Filter.limsup u Filter.atTop =
        ENNReal.ofReal (|x - x0|) *
          Filter.limsup (fun n : ℕ =>
            ENNReal.ofReal (Real.rpow (|a n|) (1 / (n + 1 : ℝ)))) Filter.atTop := by
    simpa [u, Real.norm_eq_abs, div_eq_mul_inv, Nat.cast_add, -Real.rpow_eq_pow] using
      (limsup_scaled_power_series (a := a) (x := x) (x0 := x0))
  have hlimsup_uR : Filter.limsup u Filter.atTop = ENNReal.ofReal (|x - x0|) * R := by
    simpa [hRinv, -Real.rpow_eq_pow] using hlimsup_u'
  have hlimsup_u : Filter.limsup u Filter.atTop = S := by
    simpa [S] using hlimsup_uR
  have hS_ne_top : S ≠ ⊤ := by
    simpa [S] using (ENNReal.mul_ne_top (by simp) hfin)
  have hbounded_u : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
    refine ⟨⊤, Filter.Eventually.of_forall (fun _ => le_top)⟩
  have hS1_ne_top : S + 1 ≠ ⊤ := by
    exact (ENNReal.add_ne_top.2 ⟨hS_ne_top, by simp⟩)
  have hSlt : S < S + 1 := by
    have hto :
        ENNReal.toReal S < ENNReal.toReal (S + 1) := by
      have htoReal_add :
          ENNReal.toReal (S + 1) = ENNReal.toReal S + 1 := by
        simpa using (ENNReal.toReal_add hS_ne_top (by simp))
      rw [htoReal_add]
      linarith
    exact (ENNReal.toReal_lt_toReal hS_ne_top hS1_ne_top).1 hto
  have hlt : Filter.limsup u Filter.atTop < S + 1 := by
    simpa [hlimsup_u] using hSlt
  have hle : ∀ᶠ n in Filter.atTop, u n ≤ S + 1 := by
    have hlt_ev := Filter.eventually_lt_of_limsup_lt hlt hbounded_u
    exact hlt_ev.mono (fun _ hn => le_of_lt hn)
  have htoReal :
      Filter.limsup (fun n => (u n).toReal) Filter.atTop =
        ENNReal.toReal S := by
    simpa [hlimsup_u, S] using
      (ENNReal.limsup_toReal_eq (f := Filter.atTop) (u := u) (b := S + 1) hS1_ne_top hle)
  have htoReal' :
      Filter.limsup (fun n =>
        Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ))) Filter.atTop =
        ENNReal.toReal S := by
    have hpoint :
        (fun n => (u n).toReal) =
          fun n => Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)) := by
      funext n
      have hnonneg :
          0 ≤ Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      dsimp [u]
      simpa using (ENNReal.toReal_ofReal hnonneg)
    simpa [hpoint] using htoReal
  simpa [S] using htoReal'

/-- For a summable real series, the limsup of the norms is finite. -/
lemma summable_limsup_ne_top {b : ℕ → ℝ} (hsum : Summable b) :
    Filter.limsup (fun n : ℕ => ENNReal.ofReal (‖b n‖)) Filter.atTop ≠ ⊤ := by
  have hlim : Filter.Tendsto b Filter.atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hsmall : ∀ᶠ n in Filter.atTop, |b n| < 1 :=
    tendsto_zero_eventually_abs_lt_one hlim
  have hle :
      ∀ᶠ n in Filter.atTop, ENNReal.ofReal (‖b n‖) ≤ (1 : ENNReal) := by
    filter_upwards [hsmall] with n hn
    have hnorm : ‖b n‖ < 1 := by
      simpa [Real.norm_eq_abs] using hn
    have hnorm' : ‖b n‖ ≤ 1 := le_of_lt hnorm
    have h := ENNReal.ofReal_le_ofReal hnorm'
    simpa using h
  have hlimsup_le :
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (‖b n‖)) Filter.atTop ≤ (1 : ENNReal) :=
    Filter.limsup_le_of_le (f := Filter.atTop) (u := fun n => ENNReal.ofReal (‖b n‖))
      (a := (1 : ENNReal))
      (hf := Filter.isCoboundedUnder_le_of_le Filter.atTop
        (f := fun n => ENNReal.ofReal (‖b n‖)) (x := 0) (by intro n; exact bot_le))
      hle
  have hlt :
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (‖b n‖)) Filter.atTop < (⊤ : ENNReal) :=
    lt_of_le_of_lt hlimsup_le (by simp)
  exact ne_of_lt hlt

/-- If the limsup of `‖b n‖` is infinite, then the series `∑ b n` diverges. -/
lemma limsup_infinite_not_summable {b : ℕ → ℝ}
    (h :
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (‖b n‖)) Filter.atTop = ⊤) :
    ¬ Summable b := by
  intro hsum
  exact (summable_limsup_ne_top (b := b) hsum) (by simpa [h])

lemma abs_mul_toReal_lt_one {R : ENNReal} {x x0 : ℝ}
    (hpos : R ≠ 0) (hfin : R ≠ ⊤) (hx : |x - x0| < (ENNReal.toReal R)⁻¹) :
    ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) < 1 := by
  have hne : ENNReal.toReal R ≠ 0 :=
    (ENNReal.toReal_ne_zero).2 ⟨hpos, hfin⟩
  have hRpos : 0 < ENNReal.toReal R := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hmul : |x - x0| * ENNReal.toReal R < 1 := by
    have hmul' := mul_lt_mul_of_pos_right hx hRpos
    simpa [inv_mul_cancel₀ hne] using hmul'
  have htoReal :
      ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) =
        |x - x0| * ENNReal.toReal R := by
    simp [abs_nonneg]
  simpa [htoReal] using hmul

lemma abs_mul_toReal_gt_one {R : ENNReal} {x x0 : ℝ}
    (hpos : R ≠ 0) (hfin : R ≠ ⊤) (hx : (ENNReal.toReal R)⁻¹ < |x - x0|) :
    (1 : ℝ) < ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) := by
  have hne : ENNReal.toReal R ≠ 0 :=
    (ENNReal.toReal_ne_zero).2 ⟨hpos, hfin⟩
  have hRpos : 0 < ENNReal.toReal R := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hmul : (1 : ℝ) < |x - x0| * ENNReal.toReal R := by
    have hmul' := mul_lt_mul_of_pos_right hx hRpos
    simpa [inv_mul_cancel₀ hne] using hmul'
  have htoReal :
      ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) =
        |x - x0| * ENNReal.toReal R := by
    simp [abs_nonneg]
  simpa [htoReal] using hmul

/-- Proposition 2.6.11. For the power series `∑_{n=0}^∞ aₙ (x - x₀)^n`, let
`R = limsup_{n→∞} ‖aₙ‖^{1/n}`. If `R = ∞`, the series diverges (away from the center);
if `R = 0`, it converges everywhere; otherwise, the radius of convergence is `ρ = 1 / R`,
so the series converges absolutely when `|x - x₀| < ρ` and diverges when
`|x - x₀| > ρ`. -/
theorem power_series_radius_by_limsup {a : ℕ → ℝ} {x0 : ℝ} {R : ENNReal}
    (hR :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (‖a n‖) (1 / (n + 1 : ℝ)))) Filter.atTop = R) :
    (R = ⊤ →
      ∀ x : ℝ, x ≠ x0 → ¬ Summable fun n : ℕ => a n * (x - x0) ^ n) ∧
    (R = 0 →
      ∀ x : ℝ, Summable fun n : ℕ => ‖a n * (x - x0) ^ n‖) ∧
    (R ≠ 0 → R ≠ ⊤ →
      let ρ : ℝ := (ENNReal.toReal R)⁻¹;
      (∀ x : ℝ, |x - x0| < ρ →
        Summable fun n : ℕ => ‖a n * (x - x0) ^ n‖) ∧
      (∀ x : ℝ, ρ < |x - x0| →
        ¬ Summable fun n : ℕ => a n * (x - x0) ^ n)) := by
  classical
  let seq : ℝ → ℕ → ℝ := fun x n =>
    match n with
    | 0 => 0
    | n + 1 => a n * (x - x0) ^ n
  have hR' :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (|a n|) (1 / (n + 1 : ℝ)))) Filter.atTop = R := by
    simpa [Real.norm_eq_abs, div_eq_mul_inv, Nat.cast_add] using hR
  have hRinv :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (|a n|) ((↑n + 1)⁻¹))) Filter.atTop = R := by
    simpa [div_eq_mul_inv, Nat.cast_add] using hR'
  have hbounded (x : ℝ) (hfin : R ≠ ⊤) :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ =>
          Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) := by
    let u : ℕ → ENNReal := fun n =>
      ENNReal.ofReal (Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)))
    let S : ENNReal := ENNReal.ofReal (|x - x0|) * R
    have hlimsup_u' :
        Filter.limsup u Filter.atTop =
          ENNReal.ofReal (|x - x0|) *
            Filter.limsup (fun n : ℕ =>
              ENNReal.ofReal (Real.rpow (|a n|) (1 / (n + 1 : ℝ)))) Filter.atTop := by
      simpa [u, Real.norm_eq_abs, div_eq_mul_inv, Nat.cast_add, -Real.rpow_eq_pow] using
        (limsup_scaled_power_series (a := a) (x := x) (x0 := x0))
    have hlimsup_uR : Filter.limsup u Filter.atTop = ENNReal.ofReal (|x - x0|) * R := by
      simpa [hRinv, -Real.rpow_eq_pow] using hlimsup_u'
    have hlimsup_u : Filter.limsup u Filter.atTop = S := by
      simpa [S] using hlimsup_uR
    have hS_ne_top : S ≠ ⊤ := by
      simpa [S] using (ENNReal.mul_ne_top (by simp) hfin)
    have hbounded_u : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
      refine ⟨⊤, Filter.Eventually.of_forall (fun _ => le_top)⟩
    have hS1_ne_top : S + 1 ≠ ⊤ := by
      exact (ENNReal.add_ne_top.2 ⟨hS_ne_top, by simp⟩)
    have hSlt : S < S + 1 := by
      have hto :
          ENNReal.toReal S < ENNReal.toReal (S + 1) := by
        have htoReal_add :
            ENNReal.toReal (S + 1) = ENNReal.toReal S + 1 := by
          simpa using (ENNReal.toReal_add hS_ne_top (by simp))
        rw [htoReal_add]
        linarith
      exact (ENNReal.toReal_lt_toReal hS_ne_top hS1_ne_top).1 hto
    have hlt : Filter.limsup u Filter.atTop < S + 1 := by
      simpa [hlimsup_u] using hSlt
    have hle : ∀ᶠ n in Filter.atTop, u n ≤ S + 1 := by
      have hlt_ev := Filter.eventually_lt_of_limsup_lt hlt hbounded_u
      exact hlt_ev.mono (fun _ hn => le_of_lt hn)
    refine ⟨ENNReal.toReal (S + 1), ?_⟩
    refine hle.mono ?_
    intro n hn
    have hne_top : u n ≠ ⊤ := by simp [u]
    have hle_real : (u n).toReal ≤ (S + 1).toReal :=
      (ENNReal.toReal_le_toReal hne_top hS1_ne_top).2 hn
    have hnonneg_abs :
        0 ≤ (|a n * (x - x0) ^ n|) ^ (1 / (n + 1 : ℝ)) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hle_real' :
        (|a n * (x - x0) ^ n|) ^ (1 / (n + 1 : ℝ)) ≤ (S + 1).toReal := by
      have hle_real' := hle_real
      dsimp [u] at hle_real'
      rw [ENNReal.toReal_ofReal hnonneg_abs] at hle_real'
      exact hle_real'
    simpa [seq, Real.norm_eq_abs] using hle_real'
  refine ⟨?_, ?_, ?_⟩
  · intro hRtop x hx
    have hxpos : 0 < |x - x0| := abs_pos.mpr (sub_ne_zero.mpr hx)
    have hxne : ENNReal.ofReal (|x - x0|) ≠ 0 :=
      (ENNReal.ofReal_eq_zero).not.mpr (not_le_of_gt hxpos)
    let u : ℕ → ENNReal := fun n =>
      ENNReal.ofReal (Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)))
    have hlimsup_u :
        Filter.limsup u Filter.atTop = ⊤ := by
      have hlimsup' :
          Filter.limsup u Filter.atTop =
            ENNReal.ofReal (|x - x0|) *
              Filter.limsup (fun n : ℕ =>
                ENNReal.ofReal (Real.rpow (|a n|) (1 / (n + 1 : ℝ)))) Filter.atTop := by
        simpa [u, Real.norm_eq_abs, div_eq_mul_inv, Nat.cast_add, -Real.rpow_eq_pow] using
          (limsup_scaled_power_series (a := a) (x := x) (x0 := x0))
      have hlimsup'' :
          Filter.limsup u Filter.atTop = ENNReal.ofReal (|x - x0|) * R := by
        simpa [hRinv, -Real.rpow_eq_pow] using hlimsup'
      simpa [hRtop, ENNReal.mul_top hxne] using hlimsup''
    have hfreq :
        ∃ᶠ n in Filter.atTop,
          1 < Real.rpow (‖a n * (x - x0) ^ n‖) (1 / (n + 1 : ℝ)) := by
      have hlt : (ENNReal.ofReal (1 : ℝ)) < Filter.limsup u Filter.atTop := by
        simp [hlimsup_u]
      have hfreq' :
          ∃ᶠ n in Filter.atTop, ENNReal.ofReal (1 : ℝ) < u n :=
        Filter.frequently_lt_of_lt_limsup (u := u) (f := Filter.atTop)
          (hu := Filter.isCoboundedUnder_le_of_le Filter.atTop
            (f := u) (x := 0) (by intro n; exact bot_le)) hlt
      refine hfreq'.mono ?_
      intro n hn
      exact (ENNReal.ofReal_lt_ofReal_iff').1 hn |>.1
    have hfreq_norm :
        ∃ᶠ n in Filter.atTop, (1 : ℝ) < ‖a n * (x - x0) ^ n‖ := by
      refine hfreq.mono ?_
      intro n hn
      have hpow :
          (1 : ℝ) ^ (n + 1) < ‖a n * (x - x0) ^ n‖ := by
        have h' :
            Real.rpow (‖a n * (x - x0) ^ n‖) (1 / ((n + 1 : ℕ) : ℝ)) > 1 := by
          simpa using hn
        simpa using
          (rpow_inv_natCast_lt_pow (a := ‖a n * (x - x0) ^ n‖) (r := (1 : ℝ))
            (ha := norm_nonneg _) (hr := by norm_num) (hn := Nat.succ_ne_zero n) h')
      simpa using hpow
    intro hsum
    have hlim :
        Filter.Tendsto (fun n : ℕ => a n * (x - x0) ^ n) Filter.atTop (𝓝 0) :=
      hsum.tendsto_atTop_zero
    have hsmall :
        ∀ᶠ n in Filter.atTop, ‖a n * (x - x0) ^ n‖ < 1 := by
      have hsmall' :
          ∀ᶠ n in Filter.atTop, |a n * (x - x0) ^ n| < 1 :=
        tendsto_zero_eventually_abs_lt_one hlim
      simpa [Real.norm_eq_abs] using hsmall'
    have hcontr : ∃ᶠ n : ℕ in Filter.atTop, False := by
      refine (hfreq_norm.and_eventually hsmall).mono ?_
      intro n hn
      exact (not_lt_of_ge (le_of_lt hn.1)) hn.2
    exact (Filter.frequently_false Filter.atTop) hcontr
  · intro hRzero x
    have hlimsup_real :
        Filter.limsup (fun n : ℕ =>
          Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) Filter.atTop = 0 := by
      have hlim :=
        limsup_scaled_real (a := a) (x := x) (x0 := x0) (R := R) hR (by
          simp [hRzero])
      simpa [seq, Real.norm_eq_abs, hRzero] using hlim
    have hbounded' : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ => Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) :=
      hbounded x (by simp [hRzero])
    have hsum :
        Summable (fun n : ℕ => ‖seq x (n + 1)‖) := by
      refine root_test_abs_converges (x := seq x) (L := 0) ?_ ?_ hbounded'
      · simpa using hlimsup_real
      · norm_num
    simpa [seq] using hsum
  · intro hRpos hRtop
    let ρ : ℝ := (ENNReal.toReal R)⁻¹
    refine ⟨?_, ?_⟩
    · intro x hx
      have hlimsup_real :
          Filter.limsup (fun n : ℕ =>
            Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) Filter.atTop =
            ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) := by
        have hlim :=
          limsup_scaled_real (a := a) (x := x) (x0 := x0) (R := R) hR hRtop
        simpa [seq, Real.norm_eq_abs] using hlim
      have hbounded' : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n : ℕ => Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) :=
        hbounded x hRtop
      have hlt :
          ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) < 1 := by
        have hx' : |x - x0| < (ENNReal.toReal R)⁻¹ := by
          simpa [ρ] using hx
        exact abs_mul_toReal_lt_one (R := R) (x := x) (x0 := x0) hRpos hRtop hx'
      have hsum :
          Summable (fun n : ℕ => ‖seq x (n + 1)‖) := by
        refine root_test_abs_converges (x := seq x)
          (L := ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R)) ?_ hlt hbounded'
        simpa using hlimsup_real
      simpa [seq] using hsum
    · intro x hx
      have hlimsup_real :
          Filter.limsup (fun n : ℕ =>
            Real.rpow (|seq x (n + 1)|) (1 / (n + 1 : ℝ))) Filter.atTop =
            ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) := by
        have hlim :=
          limsup_scaled_real (a := a) (x := x) (x0 := x0) (R := R) hR hRtop
        simpa [seq, Real.norm_eq_abs] using hlim
      have hgt :
          (1 : ℝ) < ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R) := by
        have hx' : (ENNReal.toReal R)⁻¹ < |x - x0| := by
          simpa [ρ] using hx
        exact abs_mul_toReal_gt_one (R := R) (x := x) (x0 := x0) hRpos hRtop hx'
      have hnot :
          ¬ Summable (fun n : ℕ => seq x (n + 1)) := by
        refine root_test_diverges (x := seq x)
          (L := ENNReal.toReal (ENNReal.ofReal (|x - x0|) * R)) ?_ hgt
        simpa using hlimsup_real
      simpa [seq] using hnot

/-- Proposition 2.6.10. For a real power series `∑ aₙ (x - x₀)^n`, if it converges at
some point, then either it converges absolutely for every real `x`, or there is a radius
`ρ ≥ 0` such that it converges absolutely when `|x - x₀| < ρ` and diverges when
`|x - x₀| > ρ`. -/
theorem power_series_real_radius {a : ℕ → ℝ} {x0 : ℝ}
    (hconv : ∃ x : ℝ, Summable fun n : ℕ => a n * (x - x0) ^ n) :
    (∀ x : ℝ, Summable fun n : ℕ => ‖a n * (x - x0) ^ n‖) ∨
      ∃ ρ : ℝ,
        0 ≤ ρ ∧
          (∀ x : ℝ, |x - x0| < ρ →
            Summable fun n : ℕ => ‖a n * (x - x0) ^ n‖) ∧
          (∀ x : ℝ, ρ < |x - x0| →
            ¬ Summable fun n : ℕ => a n * (x - x0) ^ n) := by
  classical
  have _ := hconv
  let R : ENNReal :=
    Filter.limsup (fun n : ℕ =>
      ENNReal.ofReal (Real.rpow (‖a n‖) (1 / (n + 1 : ℝ)))) Filter.atTop
  have hR :
      Filter.limsup (fun n : ℕ =>
        ENNReal.ofReal (Real.rpow (‖a n‖) (1 / (n + 1 : ℝ)))) Filter.atTop = R := rfl
  rcases power_series_radius_by_limsup (a := a) (x0 := x0) (R := R) hR with
    ⟨h_top, h_zero, h_pos⟩
  by_cases hRtop : R = ⊤
  · right
    refine ⟨0, le_of_eq rfl, ?_, ?_⟩
    · intro x hx
      have : False := (not_lt.mpr (abs_nonneg _)) hx
      exact this.elim
    · intro x hx
      have hx_ne' : |x - x0| ≠ 0 := ne_of_gt hx
      have hx_ne : x ≠ x0 := by
        intro hx_eq
        apply hx_ne'
        simp [hx_eq]
      exact h_top hRtop x hx_ne
  · by_cases hRzero : R = 0
    · left
      intro x
      exact h_zero hRzero x
    · right
      have h := h_pos hRzero hRtop
      rcases h with ⟨hconv', hdiv⟩
      set ρ : ℝ := (ENNReal.toReal R)⁻¹
      have hρ_nonneg : 0 ≤ ρ := by
        have hnonneg : 0 ≤ ENNReal.toReal R := ENNReal.toReal_nonneg
        exact inv_nonneg.mpr hnonneg
      refine ⟨ρ, hρ_nonneg, ?_, ?_⟩
      · intro x hx
        have hx' : |x - x0| < ρ := hx
        have hres := hconv' x
        have hsum := hres (by simpa [ρ] using hx')
        simpa [ρ] using hsum
      · intro x hx
        have hres := hdiv x
        have hsum := hres (by simpa [ρ] using hx)
        simpa [ρ] using hsum
/-- Proposition 2.6.12. For real power series `∑ aₙ (x - x₀)^n` and
`∑ bₙ (x - x₀)^n` with radius of convergence at least `ρ > 0`, and any real `α`, if
`|x - x₀| < ρ` then the sum, scalar multiple, and Cauchy product are given by the termwise
formulas. The Cauchy product coefficients are `cₙ = a₀ bₙ + a₁ b_{n-1} + ⋯ + aₙ b₀`. -/
theorem power_series_algebra
    {a b : ℕ → ℝ} {x x0 ρ α : ℝ}
    (hρ : 0 < ρ)
    (ha : ∀ x : ℝ, |x - x0| < ρ → Summable fun n : ℕ => a n * (x - x0) ^ n)
    (hb : ∀ x : ℝ, |x - x0| < ρ → Summable fun n : ℕ => b n * (x - x0) ^ n)
    (hx : |x - x0| < ρ) :
    (tsum (fun n : ℕ => a n * (x - x0) ^ n) +
        tsum (fun n : ℕ => b n * (x - x0) ^ n) =
      tsum (fun n : ℕ => (a n + b n) * (x - x0) ^ n)) ∧
    (tsum (fun n : ℕ => α * a n * (x - x0) ^ n) =
      tsum (fun n : ℕ => α * (a n * (x - x0) ^ n))) ∧
    (let c : ℕ → ℝ := fun n =>
        (Finset.range (n + 1)).sum fun i => a i * b (n - i);
      tsum (fun n : ℕ => a n * (x - x0) ^ n) *
          tsum (fun n : ℕ => b n * (x - x0) ^ n) =
        tsum (fun n : ℕ => c n * (x - x0) ^ n)) := by
  classical
  have ha_sum : Summable (fun n : ℕ => a n * (x - x0) ^ n) := ha x hx
  have hb_sum : Summable (fun n : ℕ => b n * (x - x0) ^ n) := hb x hx
  have ha_abs :
      Summable (fun n : ℕ => ‖a n * (x - x0) ^ n‖) := by
    have hconv : ∃ y : ℝ, Summable fun n : ℕ => a n * (y - x0) ^ n := by
      refine ⟨x0, ?_⟩
      have hx0 : |x0 - x0| < ρ := by simpa using hρ
      simpa using ha x0 hx0
    rcases power_series_real_radius (a := a) (x0 := x0) hconv with
      h_abs | ⟨ρa, hρa_nonneg, hconv_abs, hdiv⟩
    · exact h_abs x
    · have hρ_le : ρ ≤ ρa := by
        by_contra hρ_lt
        have hρ_lt' : ρa < ρ := lt_of_not_ge hρ_lt
        obtain ⟨r, hr1, hr2⟩ := exists_between hρ_lt'
        have hrpos : 0 < r := lt_of_le_of_lt hρa_nonneg hr1
        let y : ℝ := x0 + r
        have hy : |y - x0| = r := by
          simp [y, abs_of_nonneg (le_of_lt hrpos)]
        have hsum_y : Summable (fun n : ℕ => a n * (y - x0) ^ n) := by
          have hy_lt : |y - x0| < ρ := by simpa [hy] using hr2
          simpa using ha y hy_lt
        have hnot_y : ¬ Summable (fun n : ℕ => a n * (y - x0) ^ n) := by
          have hy_gt : ρa < |y - x0| := by simpa [hy] using hr1
          exact hdiv y hy_gt
        exact hnot_y hsum_y
      have hx' : |x - x0| < ρa := lt_of_lt_of_le hx hρ_le
      exact hconv_abs x hx'
  have hb_abs :
      Summable (fun n : ℕ => ‖b n * (x - x0) ^ n‖) := by
    have hconv : ∃ y : ℝ, Summable fun n : ℕ => b n * (y - x0) ^ n := by
      refine ⟨x0, ?_⟩
      have hx0 : |x0 - x0| < ρ := by simpa using hρ
      simpa using hb x0 hx0
    rcases power_series_real_radius (a := b) (x0 := x0) hconv with
      h_abs | ⟨ρb, hρb_nonneg, hconv_abs, hdiv⟩
    · exact h_abs x
    · have hρ_le : ρ ≤ ρb := by
        by_contra hρ_lt
        have hρ_lt' : ρb < ρ := lt_of_not_ge hρ_lt
        obtain ⟨r, hr1, hr2⟩ := exists_between hρ_lt'
        have hrpos : 0 < r := lt_of_le_of_lt hρb_nonneg hr1
        let y : ℝ := x0 + r
        have hy : |y - x0| = r := by
          simp [y, abs_of_nonneg (le_of_lt hrpos)]
        have hsum_y : Summable (fun n : ℕ => b n * (y - x0) ^ n) := by
          have hy_lt : |y - x0| < ρ := by simpa [hy] using hr2
          simpa using hb y hy_lt
        have hnot_y : ¬ Summable (fun n : ℕ => b n * (y - x0) ^ n) := by
          have hy_gt : ρb < |y - x0| := by simpa [hy] using hr1
          exact hdiv y hy_gt
        exact hnot_y hsum_y
      have hx' : |x - x0| < ρb := lt_of_lt_of_le hx hρ_le
      exact hconv_abs x hx'
  refine ⟨?_, ?_, ?_⟩
  · simpa [add_mul] using (ha_sum.tsum_add hb_sum).symm
  · simp [mul_assoc]
  · let f : ℕ → ℝ := fun n => a n * (x - x0) ^ n
    let g : ℕ → ℝ := fun n => b n * (x - x0) ^ n
    let c : ℕ → ℝ := fun n =>
      (Finset.range (n + 1)).sum fun i => a i * b (n - i)
    have hconv :=
      mertens_convolution (a := f) (b := g) ha_sum hb_sum (Or.inl ha_abs)
    have hterm :
        ∀ n,
          (Finset.range (n + 1)).sum (fun i => f i * g (n - i)) =
            c n * (x - x0) ^ n := by
      intro n
      classical
      have hsum :
          (Finset.range (n + 1)).sum (fun i => f i * g (n - i)) =
            (Finset.range (n + 1)).sum
              (fun i => (x - x0) ^ n * (a i * b (n - i))) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hpow :
            (x - x0) ^ i * (x - x0) ^ (n - i) = (x - x0) ^ n := by
          calc
            (x - x0) ^ i * (x - x0) ^ (n - i) =
                (x - x0) ^ (i + (n - i)) := by
                  simp [pow_add]
            _ = (x - x0) ^ n := by
                  simp [Nat.add_sub_cancel' hle]
        calc
          f i * g (n - i)
              = (a i * b (n - i)) * ((x - x0) ^ i * (x - x0) ^ (n - i)) := by
                simp [f, g, mul_left_comm, mul_assoc]
          _ = (a i * b (n - i)) * (x - x0) ^ n := by
                simp [hpow]
          _ = (x - x0) ^ n * (a i * b (n - i)) := by
                simp [mul_comm, mul_assoc]
      calc
        (Finset.range (n + 1)).sum (fun i => f i * g (n - i))
            = (Finset.range (n + 1)).sum
                (fun i => (x - x0) ^ n * (a i * b (n - i))) := hsum
        _ = (x - x0) ^ n * (Finset.range (n + 1)).sum (fun i => a i * b (n - i)) := by
              simp [Finset.mul_sum]
        _ = (x - x0) ^ n * c n := by
              simp [c]
        _ = c n * (x - x0) ^ n := by
              simp [mul_comm]
    have htsum :
        tsum (fun n : ℕ => c n * (x - x0) ^ n) =
          tsum f * tsum g := by
      simpa [f, g, c, hterm] using hconv.2
    simpa [f, g, c] using htsum.symm

/-- Example 2.6.13. For `|x| < 1`, the power series of `x / (1 + 2x + x^2)` about `0` is
`∑_{n=1}^∞ (-1)^{n+1} n x^n`, and the radius of convergence is exactly `1`. -/
lemma x_over_square_power_series :
    (∀ x : ℝ, |x| < 1 →
      Summable (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) ∧
        tsum (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) =
          x / (1 + 2 * x + x ^ 2)) ∧
    (∀ x : ℝ, 1 < |x| →
      ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1))) := by
  constructor
  · intro x hx
    have hr : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
    -- the series with coefficients `(n + 1) (-x)^n` is summable
    have hsum_geom : Summable (fun n : ℕ => (-x) ^ n) :=
      summable_geometric_of_abs_lt_one (by simpa [abs_neg] using hx)
    have hsum_n_mul : Summable (fun n : ℕ => (n : ℝ) * (-x) ^ n) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
            (r := -x) (by simpa [Real.norm_eq_abs, abs_neg] using hr)).summable
    have hsum_nplus :
        Summable (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) := by
      have hfun :
          (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) =
            fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n := by
        funext n; ring
      simpa [hfun] using hsum_n_mul.add hsum_geom
    have htsum_nplus :
        tsum (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) = 1 / (1 + x) ^ 2 := by
      have htsum_add := hsum_n_mul.hasSum.add hsum_geom.hasSum
      have hfun :
          (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) =
            fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n := by
        funext n; ring
      have htsum_add' :
          tsum (fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n) =
            tsum (fun n : ℕ => (n : ℝ) * (-x) ^ n) +
              tsum (fun n : ℕ => (-x) ^ n) := htsum_add.tsum_eq
      have htsum_n_mul :
          tsum (fun n : ℕ => (n : ℝ) * (-x) ^ n) = (-x) / (1 + x) ^ 2 := by
        have hden2 : (1 - (-x)) ^ 2 = (1 + x) ^ 2 := by ring
        simpa [hden2] using
          (tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
            (r := -x) (by simpa [Real.norm_eq_abs, abs_neg] using hr))
      have htsum_geom :
          tsum (fun n : ℕ => (-x) ^ n) = 1 / (1 + x) := by
        have hden : (1 - (-x)) = 1 + x := by ring
        simpa [hden] using
          (tsum_geometric_of_abs_lt_one (r := -x) (by simpa [abs_neg] using hx))
      calc
        tsum (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) =
            tsum (fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n) := by
              simp [hfun]
        _ = tsum (fun n : ℕ => (n : ℝ) * (-x) ^ n) +
              tsum (fun n : ℕ => (-x) ^ n) := htsum_add'
        _ = (-x) / (1 + x) ^ 2 + 1 / (1 + x) := by
              simp [htsum_n_mul, htsum_geom]
        _ = 1 / (1 + x) ^ 2 := by
              have hx1 : (1 + x) ≠ 0 := by
                have hxlt : -1 < x := (abs_lt.mp hx).1
                linarith
              have hfrac : 1 / (1 + x) = (1 + x) / (1 + x) ^ 2 := by
                field_simp [hx1]
              calc
                (-x) / (1 + x) ^ 2 + 1 / (1 + x)
                    = (-x) / (1 + x) ^ 2 + (1 + x) / (1 + x) ^ 2 := by
                        simp [hfrac]
                _ = ((-x) + (1 + x)) / (1 + x) ^ 2 := by ring
                _ = 1 / (1 + x) ^ 2 := by ring
    have hsum_target :
        Summable (fun n : ℕ =>
          (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) := by
      -- rewrite the terms as `x * ((n+1) * (-x)^n)`
      have hfun :
          (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) =
            fun n : ℕ => x * ((n + 1 : ℝ) * (-x) ^ n) := by
        funext n
        calc
          (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)
              = (-1 : ℝ) ^ n * (n + 1 : ℝ) * (x ^ n * x) := by simp [pow_succ]
          _ = x * ((n + 1 : ℝ) * ((-1 : ℝ) ^ n * x ^ n)) := by ring
          _ = x * ((n + 1 : ℝ) * (-x) ^ n) := by
                have h := (mul_pow (-1 : ℝ) x n)
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  congrArg (fun t => x * ((n + 1 : ℝ) * t)) h.symm
      have h := hsum_nplus.mul_left x
      simpa [hfun] using h
    have htsum_target :
        tsum (fun n : ℕ =>
          (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) =
          x / (1 + 2 * x + x ^ 2) := by
      have hfun :
          (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)) =
            fun n : ℕ => x * ((n + 1 : ℝ) * (-x) ^ n) := by
        funext n
        calc
          (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)
              = (-1 : ℝ) ^ n * (n + 1 : ℝ) * (x ^ n * x) := by simp [pow_succ]
          _ = x * ((n + 1 : ℝ) * ((-1 : ℝ) ^ n * x ^ n)) := by ring
          _ = x * ((n + 1 : ℝ) * (-x) ^ n) := by
                have h := (mul_pow (-1 : ℝ) x n)
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  congrArg (fun t => x * ((n + 1 : ℝ) * t)) h.symm
      have htsum_mul :
          tsum (fun n : ℕ => x * ((n + 1 : ℝ) * (-x) ^ n)) =
            x * tsum (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) := by
        simpa using
          (tsum_mul_left (a := x) (f := fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)))
      have hxpos : (1 + x) ^ 2 = 1 + 2 * x + x ^ 2 := by ring
      calc
        tsum (fun n : ℕ =>
            (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1))
            = x * tsum (fun n : ℕ => ((n + 1 : ℝ) * (-x) ^ n)) := by
                simpa [hfun] using htsum_mul
        _ = x * (1 / (1 + x) ^ 2) := by simp [htsum_nplus]
        _ = x / (1 + 2 * x + x ^ 2) := by
              simp [hxpos, div_eq_mul_inv]
    exact ⟨hsum_target, htsum_target⟩
  · intro x hx hsum
    -- terms do not tend to zero when `|x| > 1`
    have hxge : (1 : ℝ) ≤ |x| := le_of_lt hx
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hpow_ge : ∀ m : ℕ, (1 : ℝ) ≤ |x| ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m hm =>
          have hnonneg : 0 ≤ |x| ^ m := pow_nonneg hxnonneg _
          have hmul : (1 : ℝ) ≤ |x| ^ m * |x| := by nlinarith
          simpa [pow_succ] using hmul
    have hpow_lb : ∀ n : ℕ, (1 : ℝ) ≤ |x| ^ (n + 1) := by
      intro n
      simpa using hpow_ge (n + 1)
    have hbig :
        ∀ᶠ (n : ℕ) in Filter.atTop,
          (1 : ℝ) ≤ ‖(-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)‖ :=
      Filter.Eventually.of_forall (fun n => by
        have hnorm :
            ‖(-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)‖ =
              (n + 1 : ℝ) * |x| ^ (n + 1) := by
          have hpos : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.zero_le (n + 1)
          simp [Real.norm_eq_abs, hpos]
        have hpos : (1 : ℝ) ≤ (n + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have : (1 : ℝ) ≤ (n + 1 : ℝ) * |x| ^ (n + 1) := by nlinarith [hpow_lb n, hpos]
        simpa [hnorm] using this)
    have hlim := hsum.tendsto_atTop_zero
    have hsmall :
        ∀ᶠ (n : ℕ) in Filter.atTop,
          ‖(-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ (n + 1)‖ < (1 : ℝ) := by
      have hmem : {y : ℝ | ‖y‖ < 1} ∈ 𝓝 (0 : ℝ) := by
        simpa [Metric.ball, Real.dist_eq, Real.norm_eq_abs] using
          (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
      exact hlim.eventually hmem
    have hcontr := hsmall.and hbig
    rcases hcontr.exists with ⟨n, hnlt, hnge⟩
    exact not_lt_of_ge hnge hnlt

end Section06
end Chap02
