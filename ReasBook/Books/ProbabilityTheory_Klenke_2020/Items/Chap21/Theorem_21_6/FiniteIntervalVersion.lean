/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.ProbabilisticCore

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Theorem 21.6: choose a concrete row after which all dyadic rows are good. -/
noncomputable def eventualGoodRowStart
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω}
    (hgood : ∀ᶠ n in Filter.atTop, ω ∉ dyadicRowBadEvent (X := X) T q n) : ℕ :=
  Classical.choose (Filter.eventually_atTop.mp hgood)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.6: every row at or beyond the chosen starting index is good. -/
lemma eventualGoodRowStart_spec
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω}
    (hgood : ∀ᶠ n in Filter.atTop, ω ∉ dyadicRowBadEvent (X := X) T q n) :
    ∀ n ≥ eventualGoodRowStart (X := X) (T := T) (q := q) hgood,
      ω ∉ dyadicRowBadEvent (X := X) T q n :=
  Classical.choose_spec (Filter.eventually_atTop.mp hgood)

/-- Helper for Theorem 21.6: after fixing a good-row starting index `N`, define the candidate
limit path by the shifted clipped dyadic approximants. -/
private noncomputable def goodRowLimitPath
    (X : NNReal → Ω → ℝ) (T : ℝ≥0) (ω : Ω) (N : ℕ) (t : NNReal) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ X (clippedDyadicApprox T t (n + N)) ω)

/-- Helper for Theorem 21.6: once every dyadic row from `N` onward is good at `ω`, successive
shifted clipped approximants are bounded by a fixed geometric sequence. -/
private lemma clippedDyadicApprox_step_le_geometric_of_rowGoodFrom
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ} {t : NNReal}
    (_hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q n)
    (htT : t ≤ T) :
    ∀ n : ℕ,
      dist (X (clippedDyadicApprox T t (n + N)) ω)
          (X (clippedDyadicApprox T t (n + N + 1)) ω) ≤
        ((2 : ℝ) ^ (-(q : ℝ))) ^ (N + 1) * ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
  intro n
  have hgood : ω ∉ dyadicRowBadEvent (X := X) T q (n + N + 1) := by
    exact hrows (n + N + 1) (by omega)
  have hstep :=
    clippedDyadicApprox_step_le_of_rowGood
      (X := X) (T := T) (q := q) (t := t) (n := n + N) htT hgood
  have hpow :
      dyadicStepThreshold q (n + N + 1) =
        ((2 : ℝ) ^ (-(q : ℝ))) ^ (N + 1) * ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
    rw [dyadicStepThreshold_eq_geomRatio_pow]
    have hadd : n + N + 1 = (N + 1) + n := by omega
    rw [hadd, pow_add]
  -- Proof comment: the good-row step estimate is exactly the geometric decay `2^{-q(N+1)} r^n`.
  rw [hpow] at hstep
  simpa [Nat.add_assoc, dist_comm] using hstep

/-- Helper for Theorem 21.6: if every dyadic row from `N` onward is good at `ω`, then the shifted
clipped approximants form a Cauchy sequence. -/
private lemma cauchySeq_clippedDyadicApprox_of_rowGoodFrom
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ} {t : NNReal}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q n)
    (htT : t ≤ T) :
    CauchySeq (fun n ↦ X (clippedDyadicApprox T t (n + N)) ω) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq0
  have hr : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  -- Proof comment: every successive jump is bounded by one geometric step, so the standard
  -- geometric Cauchy criterion applies to the shifted sequence.
  exact
    cauchySeq_of_le_geometric
      (r := r)
      (C := r ^ (N + 1))
      hr
      (by
        intro n
        have hadd : n + N + 1 = n + 1 + N := by omega
        simpa [r, hadd] using
          clippedDyadicApprox_step_le_geometric_of_rowGoodFrom
            (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows htT n)

/-- Helper for Theorem 21.6: the shifted clipped approximants converge to the good-row limit
path. -/
private lemma tendsto_goodRowLimitPath_of_rowGoodFrom
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ} {t : NNReal}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q n)
    (htT : t ≤ T) :
    Filter.Tendsto
      (fun n ↦ X (clippedDyadicApprox T t (n + N)) ω)
      Filter.atTop
      (nhds (goodRowLimitPath X T ω N t)) := by
  -- Proof comment: the candidate limit path was defined as the `limUnder` of this Cauchy
  -- sequence, so convergence is immediate from completeness of `ℝ`.
  simpa [goodRowLimitPath] using
    (cauchySeq_clippedDyadicApprox_of_rowGoodFrom
      (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows htT).tendsto_limUnder

/-- Helper for Theorem 21.6: from a good-row start `N`, the row-`n` clipped approximant stays
within the geometric tail `2^{-q(n+1)} / (1 - 2^{-q})` of the limit path. -/
private lemma dist_clippedDyadicApprox_goodRowLimitPath_le
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ} {t : NNReal}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q n)
    (htT : t ≤ T)
    {n : ℕ} (hn : N ≤ n) :
    dist (X (clippedDyadicApprox T t n) ω) (goodRowLimitPath X T ω N t) ≤
      ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) / (1 - (2 : ℝ) ^ (-(q : ℝ))) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hr : r < 1 := by
    -- Proof comment: the geometric ratio is `2^{-q}`, which is strictly below `1` because
    -- `q > 0`.
    have hq_real : 0 < (q : ℝ) := by
      exact_mod_cast hq0
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  let f : ℕ → ℝ := fun m ↦ X (clippedDyadicApprox T t (m + N)) ω
  have hstep :
      ∀ m : ℕ, dist (f m) (f (m + 1)) ≤ r ^ (N + 1) * r ^ m := by
    -- Proof comment: the shifted dyadic approximants inherit the geometric step estimate from
    -- the good-row hypothesis.
    intro m
    simpa [f, r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      clippedDyadicApprox_step_le_geometric_of_rowGoodFrom
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows htT m
  have hlim :
      Filter.Tendsto f Filter.atTop (nhds (goodRowLimitPath X T ω N t)) := by
    -- Proof comment: the good-row limit path was defined as the limit of this shifted sequence.
    simpa [f] using
      tendsto_goodRowLimitPath_of_rowGoodFrom
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows htT
  have hshift :
      dist (X (clippedDyadicApprox T t n) ω) (goodRowLimitPath X T ω N t) ≤
        r ^ (N + 1) * r ^ (n - N) / (1 - r) := by
    -- Proof comment: apply the standard geometric-tail estimate at the shifted index `n - N`.
    simpa [f, Nat.sub_add_cancel hn] using
      dist_le_of_le_geometric_of_tendsto
        (r := r)
        (C := r ^ (N + 1))
        (f := f)
        hr
        hstep
        hlim
        (n - N)
  have hpow :
      r ^ (N + 1) * r ^ (n - N) = r ^ (n + 1) := by
    -- Proof comment: the shifted tail exponent collapses to the original row number.
    rw [← pow_add]
    congr 1
    omega
  calc
    dist (X (clippedDyadicApprox T t n) ω) (goodRowLimitPath X T ω N t)
        ≤ r ^ (N + 1) * r ^ (n - N) / (1 - r) := hshift
    _ = r ^ (n + 1) / (1 - r) := by rw [hpow]
    _ = ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) / (1 - (2 : ℝ) ^ (-(q : ℝ))) := by rfl

/-- Helper for Theorem 21.6: on a small dyadic scale, the good-row limit path is controlled by
the row-`n` geometric bound. -/
private lemma dist_goodRowLimitPath_le_smallScale
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    {n : ℕ}
    (hq0 : 0 < q)
    (hrows : ∀ m ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q m)
    (hn : N ≤ n)
    {s t : NNReal}
    (hs : s ∈ Set.Icc (0 : NNReal) T)
    (ht : t ∈ Set.Icc (0 : NNReal) T)
    (hst : s ≤ t)
    (hd : dist s t ≤ (1 / 2 : ℝ) ^ n) :
    dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
      ((1 + (2 : ℝ) ^ (-(q : ℝ))) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
        ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: the dyadic ratio `2^{-q}` is strictly less than `1` because `q > 0`.
    have hq_real : 0 < (q : ℝ) := by
      exact_mod_cast hq0
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  have hden_pos : 0 < 1 - r := by
    linarith
  have hmesh :
      (1 : ℝ) / (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← dyadicMesh_eq_halfPow n]
    rw [Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ)), Real.rpow_natCast]
    simp [one_div]
  have hgood : ω ∉ dyadicRowBadEvent (X := X) T q n := hrows n hn
  have hclose :
      dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    simpa [hmesh] using hd
  let xs : ℝ := X (clippedDyadicApprox T s n) ω
  let xt : ℝ := X (clippedDyadicApprox T t n) ω
  let gs : ℝ := goodRowLimitPath X T ω N s
  let gt : ℝ := goodRowLimitPath X T ω N t
  have hs_tail :
      dist gs xs ≤ r ^ (n + 1) / (1 - r) := by
    -- Proof comment: each limit point is within the geometric tail of its row-`n`
    -- approximant.
    simpa [gs, xs, r, dist_comm] using
      dist_clippedDyadicApprox_goodRowLimitPath_le
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := s) hq0 hrows hs.2 hn
  have ht_tail :
      dist xt gt ≤ r ^ (n + 1) / (1 - r) := by
    simpa [gt, xt, r] using
      dist_clippedDyadicApprox_goodRowLimitPath_le
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows ht.2 hn
  have hrow :
      dist xs xt ≤ r ^ n := by
    -- Proof comment: on a good row, two row-`n` approximants within one mesh differ by at most
    -- one threshold jump.
    simpa [xs, xt, r, dyadicStepThreshold_eq_geomRatio_pow, dist_comm] using
      clippedDyadicApprox_pair_le_of_rowGood_of_dist_le
        (X := X) (T := T) (q := q) (s := s) (t := t) (n := n) (ω := ω)
        hs.2 ht.2 hst hclose hgood
  have htriangle :
      dist gs gt ≤ dist gs xs + dist xs xt + dist xt gt := by
    -- Proof comment: insert the two row-`n` approximants between the two limit values.
    calc
      dist gs gt ≤ dist gs xs + dist xs gt := dist_triangle _ _ _
      _ ≤ dist gs xs + (dist xs xt + dist xt gt) := by
            gcongr
            exact dist_triangle _ _ _
      _ = dist gs xs + dist xs xt + dist xt gt := by ring
  calc
    dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
        ≤ dist gs xs + dist xs xt + dist xt gt := by simpa [gs, gt] using htriangle
    _ ≤ r ^ (n + 1) / (1 - r) + r ^ n + r ^ (n + 1) / (1 - r) := by
          gcongr
    _ = ((1 + r) / (1 - r)) * r ^ n := by
          have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
          rw [pow_succ]
          field_simp [hden_ne]
          ring
    _ = ((1 + (2 : ℝ) ^ (-(q : ℝ))) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
          ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
          simp [r, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 21.6: on the coarse branch `dist s t > 2^{-N}`, the good-row limit path is
controlled by the fixed row-`N` chain estimate. -/
private lemma dist_goodRowLimitPath_le_coarseScale
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    (hq0 : 0 < q)
    (hrows : ∀ m ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q m)
    {s t : NNReal}
    (hs : s ∈ Set.Icc (0 : NNReal) T)
    (ht : t ∈ Set.Icc (0 : NNReal) T)
    (hst : s ≤ t)
    (hd : (1 / 2 : ℝ) ^ N < dist s t) :
    dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
      ((dyadicCutoff T N : ℝ) + 2 * (2 : ℝ) ^ (-(q : ℝ)) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
        ((2 : ℝ) ^ (-(q : ℝ))) ^ N := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  let i : ℕ := Nat.ceil ((s : ℝ) * (2 : ℝ) ^ N)
  let j : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ N)
  let xs : ℝ := X (clippedDyadicApprox T s N) ω
  let xt : ℝ := X (clippedDyadicApprox T t N) ω
  let gs : ℝ := goodRowLimitPath X T ω N s
  let gt : ℝ := goodRowLimitPath X T ω N t
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    have hq_real : 0 < (q : ℝ) := by
      exact_mod_cast hq0
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  have hden_pos : 0 < 1 - r := by
    linarith
  have hij : i ≤ j := by
    dsimp [i, j]
    refine Nat.ceil_mono ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hst) (by positivity)
  have hj_cutoff : j ≤ dyadicCutoff T N := by
    simpa [j] using dyadicRightApprox_index_le_cutoff (t := t) (T := T) ht.2 N
  have hgoodN : ω ∉ dyadicRowBadEvent (X := X) T q N := hrows N le_rfl
  let row : ℕ → ℝ := fun m ↦ X (dyadicPointUpTo T N m) ω
  have hrow_step :
      ∀ {m : ℕ}, i ≤ m → m < j → dist (row m) (row (m + 1)) ≤ r ^ N := by
    intro m him hmj
    have hm_cutoff : m < dyadicCutoff T N := lt_of_lt_of_le hmj hj_cutoff
    -- Proof comment: every adjacent row-`N` increment is bounded by one threshold jump on a good
    -- row.
    simpa [row, r, dyadicStepThreshold_eq_geomRatio_pow, dist_comm] using
      dist_le_dyadicStepThreshold_of_notMem_dyadicRowBadEvent
        (X := X) (T := T) (q := q) (n := N) (ω := ω) hgoodN hm_cutoff
  have hrow_chain :
      dist (row i) (row j) ≤ (dyadicCutoff T N : ℝ) * r ^ N := by
    have hsum :
        dist (row i) (row j) ≤ ∑ m ∈ Finset.Ico i j, r ^ N := by
      refine dist_le_Ico_sum_of_dist_le hij ?_
      intro m him hmj
      exact hrow_step him hmj
    have hcard_le : (Finset.Ico i j).card ≤ dyadicCutoff T N := by
      rw [Nat.card_Ico]
      omega
    calc
      dist (row i) (row j) ≤ ∑ m ∈ Finset.Ico i j, r ^ N := hsum
      _ = ((Finset.Ico i j).card : ℝ) * r ^ N := by simp
      _ ≤ (dyadicCutoff T N : ℝ) * r ^ N := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
  have hs_tail :
      dist gs xs ≤ r ^ (N + 1) / (1 - r) := by
    -- Proof comment: the row-`N` clipped approximant sits within the geometric tail of the limit
    -- path.
    simpa [gs, xs, r, dist_comm] using
      dist_clippedDyadicApprox_goodRowLimitPath_le
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := s) hq0 hrows hs.2 le_rfl
  have ht_tail :
      dist xt gt ≤ r ^ (N + 1) / (1 - r) := by
    simpa [gt, xt, r] using
      dist_clippedDyadicApprox_goodRowLimitPath_le
        (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows ht.2 le_rfl
  have hmid :
      dist xs xt ≤ (dyadicCutoff T N : ℝ) * r ^ N := by
    -- Proof comment: chain the row-`N` clipped approximants along the good dyadic row.
    simpa [xs, xt, row, i, j, clippedDyadicApprox] using hrow_chain
  have htriangle :
      dist gs gt ≤ dist gs xs + dist xs xt + dist xt gt := by
    calc
      dist gs gt ≤ dist gs xs + dist xs gt := dist_triangle _ _ _
      _ ≤ dist gs xs + (dist xs xt + dist xt gt) := by
            gcongr
            exact dist_triangle _ _ _
      _ = dist gs xs + dist xs xt + dist xt gt := by ring
  -- Proof comment: insert the two row-`N` approximants between the limit values and then collect
  -- the two geometric tails with the row-chain bound.
  calc
    dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
        ≤ dist gs xs + dist xs xt + dist xt gt := by
          simpa [gs, gt] using htriangle
    _ ≤ r ^ (N + 1) / (1 - r) + (dyadicCutoff T N : ℝ) * r ^ N + r ^ (N + 1) / (1 - r) := by
          gcongr
    _ = ((dyadicCutoff T N : ℝ) + 2 * r / (1 - r)) * r ^ N := by
          have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
          rw [pow_succ]
          field_simp [hden_ne]
          ring
    _ = ((dyadicCutoff T N : ℝ) + 2 * (2 : ℝ) ^ (-(q : ℝ)) / (1 - (2 : ℝ) ^ (-(q : ℝ)))) *
          ((2 : ℝ) ^ (-(q : ℝ))) ^ N := by
          simp [r]

/-- Helper for Theorem 21.6: a path whose dyadic rows are all good from level `N` onward admits a
global `q`-Hölder bound on `[0,T]` after passing to the dyadic limit path. -/
private lemma holderOnWith_goodRowLimitPath_of_rowGoodFrom
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ dyadicRowBadEvent (X := X) T q n) :
    ∃ K : ℝ≥0,
      HolderOnWith K q (fun t : NNReal ↦ goodRowLimitPath X T ω N t) (Set.Icc (0 : NNReal) T) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  let Ksmall : ℝ := (1 + r) / (r * (1 - r))
  let Klarge : ℝ := (dyadicCutoff T N : ℝ) + 2 * r / (1 - r)
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq0
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  have hden_pos : 0 < 1 - r := by
    linarith
  let K : ℝ≥0 := ⟨max Ksmall Klarge, by
    dsimp [Ksmall, Klarge]
    positivity⟩
  have hordered :
      ∀ {s t : NNReal},
        s ∈ Set.Icc (0 : NNReal) T →
        t ∈ Set.Icc (0 : NNReal) T →
        s ≤ t →
        dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
          (K : ℝ) * dist s t ^ (q : ℝ) := by
    intro s t hs ht hst
    by_cases hzero : dist s t = 0
    · -- Proof comment: zero distance in the parameter collapses the target to a trivial equality.
      have hst_eq : s = t := dist_eq_zero.mp hzero
      have hnonneg : 0 ≤ (K : ℝ) * dist s t ^ (q : ℝ) := by positivity
      simpa [hst_eq] using hnonneg
    · by_cases hsmall : dist s t ≤ (1 / 2 : ℝ) ^ N
      · let x : ℝ := dist s t / ((1 / 2 : ℝ) ^ N)
        have hx_pos : 0 < x := by
          dsimp [x]
          positivity
        have hx_le_one : x ≤ 1 := by
          dsimp [x]
          have hpow_pos : 0 < ((1 / 2 : ℝ) ^ N) := by positivity
          have hsmall' : dist s t ≤ 1 * ((1 / 2 : ℝ) ^ N) := by simpa using hsmall
          exact (div_le_iff₀ hpow_pos).2 hsmall'
        obtain ⟨m, hm_lt, hm_le⟩ :=
          exists_nat_pow_near_of_lt_one
            hx_pos
            hx_le_one
            (show 0 < (1 / 2 : ℝ) by norm_num)
            (show (1 / 2 : ℝ) < 1 by norm_num)
        let n : ℕ := N + m
        have hn : N ≤ n := Nat.le_add_right _ _
        have hupper : dist s t ≤ (1 / 2 : ℝ) ^ n := by
          have hpow_pos : 0 < ((1 / 2 : ℝ) ^ N) := by positivity
          have hmul := (div_le_iff₀ hpow_pos).mp hm_le
          dsimp [x, n] at hmul ⊢
          calc
            dist s t ≤ ((1 / 2 : ℝ) ^ m) * ((1 / 2 : ℝ) ^ N) := hmul
            _ = (1 / 2 : ℝ) ^ (N + m) := by
                  rw [mul_comm, ← pow_add]
        have hlower : (1 / 2 : ℝ) ^ (n + 1) < dist s t := by
          have hpow_pos : 0 < ((1 / 2 : ℝ) ^ N) := by positivity
          have hmul := (lt_div_iff₀ hpow_pos).mp hm_lt
          dsimp [x, n] at hmul ⊢
          calc
            ((1 / 2 : ℝ) ^ (N + m + 1))
                = ((1 / 2 : ℝ) ^ (m + 1)) * ((1 / 2 : ℝ) ^ N) := by
                    rw [show N + m + 1 = (m + 1) + N by omega, pow_add]
            _ < dist s t := hmul
        have hsmall_row :
            dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
              ((1 + r) / (1 - r)) * r ^ n := by
          simpa [r, n] using
            dist_goodRowLimitPath_le_smallScale
              (X := X) (T := T) (q := q) (ω := ω) (N := N) (n := n)
              hq0 hrows hn hs ht hst hupper
        have hpow_lt :
            r ^ (n + 1) < dist s t ^ (q : ℝ) := by
          have hpow_lt' :
              ((1 / 2 : ℝ) ^ (n + 1)) ^ (q : ℝ) < dist s t ^ (q : ℝ) :=
            Real.rpow_lt_rpow (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 1)) hlower hq_real
          calc
            r ^ (n + 1) = ((1 / 2 : ℝ) ^ (n + 1)) ^ (q : ℝ) := by
              rw [← dyadicStepThreshold_eq_geomRatio_pow (q := q) (n := n + 1),
                ← dyadicStepThreshold_eq_meshRpow (q := q) (n := n + 1)]
            _ < dist s t ^ (q : ℝ) := hpow_lt'
        have hrn_le :
            r ^ n ≤ dist s t ^ (q : ℝ) / r := by
          refine (le_div_iff₀ hr_pos).2 ?_
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hpow_lt.le
        have hsmall_final :
            dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
              Ksmall * dist s t ^ (q : ℝ) := by
          calc
            dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
                ≤ ((1 + r) / (1 - r)) * r ^ n := hsmall_row
            _ ≤ ((1 + r) / (1 - r)) * (dist s t ^ (q : ℝ) / r) := by
                  gcongr
            _ = Ksmall * dist s t ^ (q : ℝ) := by
                  dsimp [Ksmall]
                  have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
                  field_simp [hr_pos.ne', hden_ne]
        calc
          dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
              ≤ Ksmall * dist s t ^ (q : ℝ) := hsmall_final
          _ ≤ (K : ℝ) * dist s t ^ (q : ℝ) := by
                exact mul_le_mul_of_nonneg_right
                  (by simpa [K] using (le_max_left Ksmall Klarge))
                  (by positivity)
      · have hcoarse_row :
            dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
              Klarge * r ^ N := by
          simpa [Klarge, r] using
            dist_goodRowLimitPath_le_coarseScale
              (X := X) (T := T) (q := q) (ω := ω) (N := N) hq0 hrows hs ht hst
              (lt_of_not_ge hsmall)
        have hpow_lt :
            r ^ N < dist s t ^ (q : ℝ) := by
          have hpow_lt' :
              ((1 / 2 : ℝ) ^ N) ^ (q : ℝ) < dist s t ^ (q : ℝ) :=
            Real.rpow_lt_rpow (by positivity : 0 ≤ (1 / 2 : ℝ) ^ N) (lt_of_not_ge hsmall) hq_real
          calc
            r ^ N = ((1 / 2 : ℝ) ^ N) ^ (q : ℝ) := by
              rw [← dyadicStepThreshold_eq_geomRatio_pow (q := q) (n := N),
                ← dyadicStepThreshold_eq_meshRpow (q := q) (n := N)]
            _ < dist s t ^ (q : ℝ) := hpow_lt'
        calc
          dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
              ≤ Klarge * r ^ N := hcoarse_row
          _ ≤ Klarge * dist s t ^ (q : ℝ) := by
                gcongr
          _ ≤ (K : ℝ) * dist s t ^ (q : ℝ) := by
                exact mul_le_mul_of_nonneg_right
                  (by simpa [K] using (le_max_right Ksmall Klarge))
                  (by positivity)
  refine ⟨K, ?_⟩
  intro s hs t ht
  by_cases hst : s ≤ t
  · have hdist := hordered hs ht hst
    -- Proof comment: cast the real Hölder estimate into `ENNReal` and normalize the distance term
    -- to the `edist` power expected by `HolderOnWith`.
    have hEdist :
        edist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
          (K : ℝ≥0∞) * edist s t ^ (q : ℝ) := by
      have hpow :
          ENNReal.ofReal (dist s t ^ (q : ℝ)) =
            ENNReal.ofReal (dist s t) ^ (q : ℝ) := by
        exact (ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist s t) q.2).symm
      calc
        edist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
            = ENNReal.ofReal (dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)) := by
                rw [edist_dist]
        _ ≤ ENNReal.ofReal ((K : ℝ) * dist s t ^ (q : ℝ)) := ENNReal.ofReal_le_ofReal hdist
        _ = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
        _ = (K : ℝ≥0∞) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
              rw [ENNReal.ofReal_coe_nnreal]
        _ = (K : ℝ≥0∞) * (ENNReal.ofReal (dist s t) ^ (q : ℝ)) := by
              exact congrArg (fun z : ℝ≥0∞ ↦ (K : ℝ≥0∞) * z) hpow
        _ = (K : ℝ≥0∞) * edist s t ^ (q : ℝ) := by
              rw [edist_dist]
    exact hEdist
  · have hts : t ≤ s := le_of_not_ge hst
    have hdist :
        dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
          (K : ℝ) * dist s t ^ (q : ℝ) := by
      calc
        dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
            = dist (goodRowLimitPath X T ω N t) (goodRowLimitPath X T ω N s) := by
                rw [dist_comm]
        _ ≤ (K : ℝ) * dist t s ^ (q : ℝ) := hordered ht hs hts
        _ = (K : ℝ) * dist s t ^ (q : ℝ) := by rw [dist_comm]
    -- Proof comment: after symmetrizing the ordered estimate, cast it into `ENNReal` exactly as
    -- in the forward branch.
    have hEdist :
        edist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t) ≤
          (K : ℝ≥0∞) * edist s t ^ (q : ℝ) := by
      have hpow :
          ENNReal.ofReal (dist s t ^ (q : ℝ)) =
            ENNReal.ofReal (dist s t) ^ (q : ℝ) := by
        exact (ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist s t) q.2).symm
      calc
        edist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)
            = ENNReal.ofReal (dist (goodRowLimitPath X T ω N s) (goodRowLimitPath X T ω N t)) := by
                rw [edist_dist]
        _ ≤ ENNReal.ofReal ((K : ℝ) * dist s t ^ (q : ℝ)) := ENNReal.ofReal_le_ofReal hdist
        _ = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
        _ = (K : ℝ≥0∞) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
              rw [ENNReal.ofReal_coe_nnreal]
        _ = (K : ℝ≥0∞) * (ENNReal.ofReal (dist s t) ^ (q : ℝ)) := by
              exact congrArg (fun z : ℝ≥0∞ ↦ (K : ℝ≥0∞) * z) hpow
        _ = (K : ℝ≥0∞) * edist s t ^ (q : ℝ) := by
              rw [edist_dist]
    exact hEdist

/-- Helper for Theorem 21.6: package the interval-local good-row version into a single symbol so
the main finite-horizon theorem does not repeatedly unfold the same `if`-construction. -/
private noncomputable def goodRowVersion
    (X : NNReal → Ω → ℝ) (T q : ℝ≥0) (t : NNReal) (ω : Ω) : ℝ :=
  letI : Decidable (∀ᶠ n in Filter.atTop, ω ∉ dyadicRowBadEvent (X := X) T q n) :=
    Classical.propDecidable _
  if hgood : ∀ᶠ n in Filter.atTop, ω ∉ dyadicRowBadEvent (X := X) T q n then
    goodRowLimitPath X T ω (eventualGoodRowStart (X := X) (T := T) (q := q) hgood) t
  else
    0

/-- Helper for Theorem 21.6: on almost every path, the clipped dyadic approximants converge to the
packaged good-row version at each fixed time `t ≤ T`. -/
private lemma ae_tendsto_clippedDyadicApprox_to_goodRowVersion
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0} {t : NNReal}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq0 : 0 < q)
    (hq : (q : ℝ) < β / α)
    (htT : t ≤ T) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n ↦ X (clippedDyadicApprox T t n) ω) Filter.atTop
        (nhds (goodRowVersion X T q t ω)) := by
  let bad : ℕ → Set Ω := fun n ↦ dyadicRowBadEvent (X := X) T q n
  have hsumBad : Summable (fun n : ℕ ↦ μ.real (bad n)) :=
    summable_measureReal_dyadicRowBadEvent
      (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) h hq
  have hgood_ae : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ bad n :=
    ae_eventually_notMem_of_summable_measureReal (μ := μ) (s := bad) hsumBad
  filter_upwards [hgood_ae] with ω hgood
  let N : ℕ := eventualGoodRowStart (X := X) (T := T) (q := q) hgood
  have hrows : ∀ n ≥ N, ω ∉ bad n :=
    eventualGoodRowStart_spec (X := X) (T := T) (q := q) hgood
  have hshift :
      Filter.Tendsto
        (fun n ↦ X (clippedDyadicApprox T t (n + N)) ω)
        Filter.atTop
        (nhds (goodRowLimitPath X T ω N t)) :=
    tendsto_goodRowLimitPath_of_rowGoodFrom
      (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows htT
  have hfull :
      Filter.Tendsto
        (fun n ↦ X (clippedDyadicApprox T t n) ω)
        Filter.atTop
        (nhds (goodRowLimitPath X T ω N t)) := by
    -- Proof comment: once the shifted sequence converges, the original sequence converges to the
    -- same limit because dropping finitely many initial dyadic levels does not change the limit.
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := fun n ↦ X (clippedDyadicApprox T t n) ω) N).mp <| by
        simpa [N] using hshift
  simpa [goodRowVersion, bad, hgood, N] using hfull

/-- Helper for Theorem 21.6: for each fixed `t ≤ T`, the clipped dyadic approximants converge in
measure to the original process value `X t`. -/
private lemma tendstoInMeasure_clippedDyadicApprox_to_original
    {X : NNReal → Ω → ℝ} {T α β C : ℝ≥0} {t : NNReal}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (htT : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ X (clippedDyadicApprox T t n) ω) Filter.atTop (fun ω ↦ X t ω) := by
  refine (tendstoInMeasure_iff_measureReal_dist).2 ?_
  intro ε hε
  have hβpow_pos : 0 < 1 + (β : ℝ) := by
    have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast h.beta_pos
    linarith
  have hpointwise :
      ∀ n : ℕ,
        μ.real {ω | ε ≤ dist (X (clippedDyadicApprox T t n) ω) (X t ω)} ≤
          ((C : ℝ) / ε ^ (α : ℝ)) *
            dist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ)) := by
    intro n
    -- Proof comment: the fixed-time Markov estimate turns the moment control into a real-valued
    -- probability bound for the clipped approximation error at level `n`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      measureReal_clippedDyadicApprox_dist_ge_le
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (t := t) (n := n)
        (ε := ε) h htT hε
  have hdist :
      Filter.Tendsto (fun n ↦ dist (clippedDyadicApprox T t n) t) Filter.atTop (nhds 0) := by
    -- Proof comment: the clipped dyadic times themselves converge to `t`, so their real distance
    -- from `t` vanishes.
    have hdist' :
        Filter.Tendsto (fun n ↦ dist (clippedDyadicApprox T t n) t) Filter.atTop (nhds (dist t t)) :=
      (tendsto_clippedDyadicApprox htT).dist tendsto_const_nhds
    simpa using hdist'
  have hpow :
      Filter.Tendsto
        (fun n ↦ dist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ)))
        Filter.atTop
        (nhds 0) := by
    -- Proof comment: positive real powers preserve the convergence of the dyadic mesh to `0`.
    simpa [Real.zero_rpow hβpow_pos.ne'] using hdist.rpow_const (Or.inr hβpow_pos.le)
  have hupper :
      Filter.Tendsto
        (fun n ↦ ((C : ℝ) / ε ^ (α : ℝ)) *
          dist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ)))
        Filter.atTop
        (nhds 0) := by
    simpa [zero_mul] using tendsto_const_nhds.mul hpow
  exact
    squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg)
      (Filter.Eventually.of_forall hpointwise)
      hupper

/-- Helper for Theorem 21.6: at each fixed `t ≤ T`, the packaged good-row version agrees almost
everywhere with the original process value. -/
private lemma aeEq_original_of_goodRowVersionAt
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0} {t : NNReal}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq0 : 0 < q)
    (hq : (q : ℝ) < β / α)
    (htT : t ≤ T) :
    X t =ᵐ[μ] goodRowVersion X T q t := by
  have hd_meas :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ X (clippedDyadicApprox T t n) ω) μ := by
    intro n
    have hmem : clippedDyadicApprox T t n ∈ Set.Icc (0 : NNReal) T :=
      clippedDyadicApprox_mem_Icc T t n
    simpa using
      (h.isKolmogorovProcess.measurable
        ⟨clippedDyadicApprox T t n, hmem⟩).aestronglyMeasurable
  -- Proof comment: both the dyadic extension and the original process are limits in measure of
  -- the same clipped dyadic approximants.
  exact
    aeEq_original_of_dyadicExtension
      (μ := μ)
      (X := X)
      (Y := goodRowVersion X T q)
      (t := t)
      (d := clippedDyadicApprox T t)
      hd_meas
      (ae_tendsto_clippedDyadicApprox_to_goodRowVersion
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) (t := t)
        h hq0 hq htT)
      (tendstoInMeasure_clippedDyadicApprox_to_original
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (t := t) h htT)

/-- Helper for Theorem 21.6: the missing finite-horizon Kolmogorov--Chentsov package should turn a
moment bound on `[0,T]` into a modification with pathwise Hölder control on that interval. -/
lemma exists_holderVersion_of_isKolmogorovProcessOnIcc
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq0 : 0 < q)
    (hq : (q : ℝ) < β / α) :
    ∃ Y : NNReal → Ω → ℝ,
      (∀ t : NNReal, t ≤ T → X t =ᵐ[μ] Y t) ∧
      (∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K q (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)) := by
  -- Route correction: the global patching layer below is now separated from the finite-horizon
  -- Kolmogorov--Chentsov step, so the only remaining source-facing gap is this interval-local
  -- construction.
  let bad : ℕ → Set Ω := fun n ↦ dyadicRowBadEvent (X := X) T q n
  let Y : NNReal → Ω → ℝ := goodRowVersion X T q
  refine ⟨Y, ?_, ?_⟩
  · intro t htT
    -- Proof comment: fixed-time almost-sure equality is delegated to the extracted dyadic
    -- extension helper for the packaged version.
    simpa [Y] using
      aeEq_original_of_goodRowVersionAt
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) (t := t)
        h hq0 hq htT
  · intro ω
    by_cases hgood : ∀ᶠ n in Filter.atTop, ω ∉ bad n
    · let N : ℕ := eventualGoodRowStart (X := X) (T := T) (q := q) hgood
      have hrows : ∀ n ≥ N, ω ∉ bad n :=
        eventualGoodRowStart_spec (X := X) (T := T) (q := q) hgood
      rcases
        holderOnWith_goodRowLimitPath_of_rowGoodFrom
          (X := X) (T := T) (q := q) (ω := ω) (N := N) hq0 hrows with
        ⟨K, hK⟩
      refine ⟨K, ?_⟩
      simpa [Y, goodRowVersion, bad, hgood, N] using hK
    · refine ⟨0, ?_⟩
      -- Proof comment: on the exceptional branch the packaged version is identically zero.
      intro s hs t ht
      simp [Y, goodRowVersion, bad, hgood]
