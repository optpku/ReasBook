/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Filter

section Chap03
section Section05

/-- Definition 3.5.1. `∞` is a cluster point of `S ⊆ ℝ` if for every real `M` there exists
`x ∈ S` with `x ≥ M`; similarly `-∞` is a cluster point if for every `M` there is `x ∈ S` with
`x ≤ M`. For a function `f : S → ℝ` with `∞` (resp. `-∞`) a cluster point of `S`, the limit
`lim_{x → ∞} f = L` (resp. `lim_{x → -∞} f = L`) means that for every `ε > 0` there exists
`M ∈ ℝ` such that for all `x ∈ S` with `x ≥ M` (resp. `x ≤ M`) one has `|f x - L| < ε`. -/
def book_clusterPoint_atTop (S : Set ℝ) : Prop :=
  ∀ M : ℝ, ∃ x ∈ S, M ≤ x

/-- Definition 3.5.1. `-∞` is a cluster point of `S ⊆ ℝ` if every real bound is exceeded below
by some `x ∈ S`. -/
def book_clusterPoint_atBot (S : Set ℝ) : Prop :=
  ∀ M : ℝ, ∃ x ∈ S, x ≤ M

/-- The book notion that `∞` is a cluster point of a subset of `ℝ` is equivalent to the set being
unbounded above. -/
lemma book_clusterPoint_atTop_iff_not_bddAbove {S : Set ℝ} :
    book_clusterPoint_atTop S ↔ ¬ BddAbove S := by
  constructor
  · intro hS
    refine (not_bddAbove_iff).2 ?_
    intro M
    obtain ⟨x, hxS, hxge⟩ := hS (M + 1)
    refine ⟨x, hxS, ?_⟩
    have hlt : M < M + 1 := by linarith
    exact lt_of_lt_of_le hlt hxge
  · intro hS
    have hS' : ∀ M, ∃ x ∈ S, M < x := (not_bddAbove_iff).1 hS
    intro M
    obtain ⟨x, hxS, hxlt⟩ := hS' M
    exact ⟨x, hxS, le_of_lt hxlt⟩

/-- The book notion that `-∞` is a cluster point of a subset of `ℝ` is equivalent to the set being
unbounded below. -/
lemma book_clusterPoint_atBot_iff_not_bddBelow {S : Set ℝ} :
    book_clusterPoint_atBot S ↔ ¬ BddBelow S := by
  constructor
  · intro hS
    refine (not_bddBelow_iff).2 ?_
    intro M
    obtain ⟨x, hxS, hxle⟩ := hS (M - 1)
    refine ⟨x, hxS, ?_⟩
    have hlt : M - 1 < M := by linarith
    exact lt_of_le_of_lt hxle hlt
  · intro hS
    have hS' : ∀ M, ∃ x ∈ S, x < M := (not_bddBelow_iff).1 hS
    intro M
    obtain ⟨x, hxS, hxlt⟩ := hS' M
    exact ⟨x, hxS, le_of_lt hxlt⟩

/-- Definition 3.5.1. A function `f : S → ℝ` converges to `L` as `x → ∞` if for every `ε > 0`
there exists `M ∈ ℝ` such that whenever `x ∈ S` satisfies `x ≥ M`, then `|f x - L| < ε`. -/
def book_tendsto_atTop (S : Set ℝ) (f : S → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ x : S, M ≤ (x : ℝ) → |f x - L| < ε

/-- Definition 3.5.1. A function `f : S → ℝ` converges to `L` as `x → -∞` if for every `ε > 0`
there exists `M ∈ ℝ` such that whenever `x ∈ S` satisfies `x ≤ M`, then `|f x - L| < ε`. -/
def book_tendsto_atBot (S : Set ℝ) (f : S → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ x : S, (x : ℝ) ≤ M → |f x - L| < ε

/-- Assuming `∞` is a cluster point of `S`, the book limit at `∞` coincides with the standard
`Tendsto` formulation along `Filter.atTop` for functions on the subtype domain. -/
lemma book_tendsto_atTop_iff_tendsto {S : Set ℝ} {f : S → ℝ} {L : ℝ}
    (hS : book_clusterPoint_atTop S) :
    book_tendsto_atTop S f L ↔ Tendsto f atTop (nhds L) := by
  haveI : Nonempty S := by
    rcases hS 0 with ⟨x, hxS, _⟩
    exact ⟨⟨x, hxS⟩⟩
  constructor
  · intro h
    refine (tendsto_iff_forall_eventually_mem.2 ?_)
    intro s hs
    rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
    rcases h ε hε with ⟨M, hM⟩
    obtain ⟨a, haS, hMa⟩ := hS M
    refine (eventually_atTop.2 ?_)
    refine ⟨⟨a, haS⟩, ?_⟩
    intro b hb
    have hMb : M ≤ (b : ℝ) := le_trans hMa hb
    have hdist : |f b - L| < ε := hM b hMb
    have hmem : f b ∈ Metric.ball L ε := by
      have hdist' : dist (f b) L < ε := by
        simpa [Real.dist_eq] using hdist
      exact (Metric.mem_ball.2 hdist')
    exact hball hmem
  · intro h ε hε
    have hε' : ∀ᶠ x in atTop, f x ∈ Metric.ball L ε := by
      have hball : Metric.ball L ε ∈ (nhds L) := Metric.ball_mem_nhds L hε
      exact (tendsto_iff_forall_eventually_mem.1 h) _ hball
    obtain ⟨a, ha⟩ := (eventually_atTop.1 hε')
    refine ⟨(a : ℝ), ?_⟩
    intro x hx
    have hx' : a ≤ x := by simpa using hx
    have hmem : f x ∈ Metric.ball L ε := ha x hx'
    have hdist : dist (f x) L < ε := Metric.mem_ball.1 hmem
    simpa [Real.dist_eq] using hdist

/-- The book limit at `-∞` coincides with the standard `Tendsto` formulation along `Filter.atBot`
for functions on the subtype domain. -/
lemma book_tendsto_atBot_iff_tendsto {S : Set ℝ} {f : S → ℝ} {L : ℝ}
    (hS : book_clusterPoint_atBot S) :
    book_tendsto_atBot S f L ↔ Tendsto f atBot (nhds L) := by
  haveI : Nonempty S := by
    rcases hS 0 with ⟨x, hxS, _⟩
    exact ⟨⟨x, hxS⟩⟩
  constructor
  · intro h
    refine (tendsto_iff_forall_eventually_mem.2 ?_)
    intro s hs
    rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
    rcases h ε hε with ⟨M, hM⟩
    obtain ⟨a, haS, hMa⟩ := hS M
    refine (eventually_atBot.2 ?_)
    refine ⟨⟨a, haS⟩, ?_⟩
    intro b hb
    have hMb : (b : ℝ) ≤ M := le_trans hb hMa
    have hdist : |f b - L| < ε := hM b hMb
    have hmem : f b ∈ Metric.ball L ε := by
      have hdist' : dist (f b) L < ε := by
        simpa [Real.dist_eq] using hdist
      exact (Metric.mem_ball.2 hdist')
    exact hball hmem
  · intro h ε hε
    have hε' : ∀ᶠ x in atBot, f x ∈ Metric.ball L ε := by
      have hball : Metric.ball L ε ∈ (nhds L) := Metric.ball_mem_nhds L hε
      exact (tendsto_iff_forall_eventually_mem.1 h) _ hball
    obtain ⟨a, ha⟩ := (eventually_atBot.1 hε')
    refine ⟨(a : ℝ), ?_⟩
    intro x hx
    have hx' : x ≤ a := by simpa using hx
    have hmem : f x ∈ Metric.ball L ε := ha x hx'
    have hdist : dist (f x) L < ε := Metric.mem_ball.1 hmem
    simpa [Real.dist_eq] using hdist

/-- Proposition 3.5.2. If a function has a limit at `∞` (resp. `-∞`) in the sense above, that
limit value is unique. -/
lemma limit_atTop_unique {S : Set ℝ} {f : S → ℝ} {L₁ L₂ : ℝ}
    (hS : book_clusterPoint_atTop S)
    (h₁ : book_tendsto_atTop S f L₁) (h₂ : book_tendsto_atTop S f L₂) : L₁ = L₂ := by
  haveI : Nonempty S := by
    rcases hS 0 with ⟨x, hxS, _⟩
    exact ⟨⟨x, hxS⟩⟩
  have h₁' : Tendsto f atTop (nhds L₁) :=
    (book_tendsto_atTop_iff_tendsto hS).1 h₁
  have h₂' : Tendsto f atTop (nhds L₂) :=
    (book_tendsto_atTop_iff_tendsto hS).1 h₂
  exact tendsto_nhds_unique h₁' h₂'

/-- Proposition 3.5.2. If a function has a limit at `-∞` in the sense above, that limit value is
unique. -/
lemma limit_atBot_unique {S : Set ℝ} {f : S → ℝ} {L₁ L₂ : ℝ}
    (hS : book_clusterPoint_atBot S)
    (h₁ : book_tendsto_atBot S f L₁) (h₂ : book_tendsto_atBot S f L₂) : L₁ = L₂ := by
  haveI : Nonempty S := by
    rcases hS 0 with ⟨x, hxS, _⟩
    exact ⟨⟨x, hxS⟩⟩
  have h₁' : Tendsto f atBot (nhds L₁) :=
    (book_tendsto_atBot_iff_tendsto hS).1 h₁
  have h₂' : Tendsto f atBot (nhds L₂) :=
    (book_tendsto_atBot_iff_tendsto hS).1 h₂
  exact tendsto_nhds_unique h₁' h₂'

/-- Example 3.5.3. The function `f x = 1 / (|x| + 1)` satisfies
`lim_{x → ∞} f x = 0` and `lim_{x → -∞} f x = 0`. -/
lemma example_3_5_3 :
    Tendsto (fun x : ℝ => (1 : ℝ) / (|x| + 1)) atTop (nhds 0) ∧
      Tendsto (fun x : ℝ => (1 : ℝ) / (|x| + 1)) atBot (nhds 0) := by
  constructor
  · have h_abs : Tendsto (fun x : ℝ => |x|) atTop atTop := tendsto_abs_atTop_atTop
    have h_abs_add_one : Tendsto (fun x : ℝ => |x| + 1) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro B
      have h_event := (Filter.tendsto_atTop.1 h_abs) (B - 1)
      refine Filter.mem_of_superset h_event ?_
      intro x hx
      have hx' := add_le_add_right hx (1 : ℝ)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    have h_inv := tendsto_inv_atTop_zero.comp h_abs_add_one
    simpa [one_div] using h_inv
  · have h_abs : Tendsto (fun x : ℝ => |x|) atBot atTop := tendsto_abs_atBot_atTop
    have h_abs_add_one : Tendsto (fun x : ℝ => |x| + 1) atBot atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro B
      have h_event := (Filter.tendsto_atTop.1 h_abs) (B - 1)
      refine Filter.mem_of_superset h_event ?_
      intro x hx
      have hx' := add_le_add_right hx (1 : ℝ)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    have h_inv := tendsto_inv_atTop_zero.comp h_abs_add_one
    simpa [one_div] using h_inv

/-- The affine sequence `n ↦ 2n + c` diverges to `∞`. -/
lemma tendsto_linear_shift_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ) + c) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro B
  obtain ⟨N, hN⟩ := exists_nat_ge ((B - c) / 2)
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  have hNreal : (B - c) / 2 ≤ (n : ℝ) := by
    have hN' : (B - c) / 2 ≤ (N : ℝ) := by exact_mod_cast hN
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hN'.trans hn'
  have hmul : B - c ≤ (2 : ℝ) * (n : ℝ) := by
    have :=
        mul_le_mul_of_nonneg_left hNreal (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have : B ≤ (2 : ℝ) * (n : ℝ) + c := by
    have := add_le_add_right hmul c
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  simpa using this

/-- Exact value of `sin (π (2n + 1/2))`. -/
lemma sin_pi_two_n_add_half (n : ℕ) :
    Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2)) = 1 := by
  have hcos_even : Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ))) = 1 := by
    have h := Real.cos_nat_mul_pi (2 * n)
    have hpow' : ((-1 : ℝ) ^ 2) ^ n = 1 := by simp [pow_two]
    have hpow := (pow_mul (-1 : ℝ) 2 n).trans hpow'
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc, hpow] using h
  have hsin_add :
      Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ)) + Real.pi / 2) =
        Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ))) := by
    have := Real.sin_add (Real.pi * ((2 : ℝ) * (n : ℝ))) (Real.pi / 2)
    simpa [Real.sin_pi_div_two, Real.cos_pi_div_two, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc, zero_mul, zero_add,
      one_mul] using this
  have hpi : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by
    simp [div_eq_mul_inv]
  have harg :
      Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2)) =
        Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ)) + Real.pi / 2) := by
    have harg_eq :
        Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2) =
          Real.pi * ((2 : ℝ) * (n : ℝ)) + Real.pi / 2 := by
      simpa [hpi] using
        (mul_add Real.pi ((2 : ℝ) * (n : ℝ)) (1 / 2))
    exact congrArg Real.sin harg_eq
  calc
    Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2))
        = Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ)) + Real.pi / 2) := harg
    _ = Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ))) := hsin_add
    _ = 1 := hcos_even

/-- Exact value of `sin (π (2n + 3/2))`. -/
lemma sin_pi_two_n_add_three_halves (n : ℕ) :
    Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2)) = -1 := by
  have hcos_int : Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ) + 1)) = -1 := by
    have h := Real.cos_nat_mul_pi (2 * n + 1)
    have hpow_even : (-1 : ℝ) ^ (2 * n) = 1 := by
      have hpow' : ((-1 : ℝ) ^ 2) ^ n = 1 := by simp [pow_two]
      exact (pow_mul (-1 : ℝ) 2 n).trans hpow'
    have hpow_odd' : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
      simpa [Nat.succ_eq_add_one, hpow_even] using
        (pow_succ (-1 : ℝ) (2 * n))
    have hpow_odd : (-1 : ℝ) ^ (n * 2 + 1) = -1 := by
      simpa [Nat.mul_comm] using hpow_odd'
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm,
      mul_assoc, Nat.mul_comm, hpow_odd] using h
  have hcos_pi_two : Real.cos (Real.pi / 2) = 0 := by
    simp
  have hsin_pi_two : Real.sin (Real.pi / 2) = 1 := by
    simp
  have hsin_add :
      Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1) + Real.pi / 2) =
        Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ) + 1)) := by
    have := Real.sin_add (Real.pi * ((2 : ℝ) * (n : ℝ) + 1)) (Real.pi / 2)
    simpa [Real.sin_pi_div_two, Real.cos_pi_div_two, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc, zero_mul, zero_add,
      one_mul] using this
  have hpi : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by
    simp [div_eq_mul_inv]
  have harg :
      Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2)) =
        Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1) + Real.pi / 2) := by
    have hthree :
        (2 : ℝ) * (n : ℝ) + 3 / 2 =
          ((2 : ℝ) * (n : ℝ) + 1) + 1 / 2 := by
      ring
    have hmul :
        Real.pi * (((2 : ℝ) * (n : ℝ) + 1) + 1 / 2) =
          Real.pi * ((2 : ℝ) * (n : ℝ) + 1) + Real.pi / 2 := by
      simpa [hpi] using
        (mul_add Real.pi ((2 : ℝ) * (n : ℝ) + 1) (1 / 2))
    have harg_eq :
        Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2) =
          Real.pi * ((2 : ℝ) * (n : ℝ) + 1) + Real.pi / 2 := by
      simpa [hthree] using hmul
    exact congrArg Real.sin harg_eq
  calc
    Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2))
        = Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1) + Real.pi / 2) := harg
    _ = Real.cos (Real.pi * ((2 : ℝ) * (n : ℝ) + 1)) := hsin_add
    _ = -1 := hcos_int

/-- Example 3.5.4. For `f x = sin (π x)`, the limit `lim_{x → ∞} f x` does not exist, while the
sequence limit `lim_{n → ∞} sin (π n)` equals `0`; this illustrates the distinction between limits
of continuous variables and limits of sequences. -/
lemma example_3_5_4_limit_does_not_exist :
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ => Real.sin (Real.pi * x)) atTop (nhds L) := by
  intro h
  obtain ⟨L, hL⟩ := h
  have h_seq₁ :
      Tendsto (fun n : ℕ => Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2)))
        atTop (nhds L) :=
    hL.comp (tendsto_linear_shift_atTop (1 / 2))
  have h_const_seq₁ :
      (fun n : ℕ => Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 1 / 2))) =
        fun _ : ℕ => (1 : ℝ) := by
    funext n; exact sin_pi_two_n_add_half n
  have h_one_to_L :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds L) :=
    h_const_seq₁ ▸ h_seq₁
  have h_one_const : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have hL_eq_one :
      (1 : ℝ) = L :=
    tendsto_nhds_unique (f := fun _ : ℕ => (1 : ℝ)) h_one_const h_one_to_L
  have h_seq₂ :
      Tendsto (fun n : ℕ => Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2)))
        atTop (nhds L) :=
    hL.comp (tendsto_linear_shift_atTop (3 / 2))
  have h_const_seq₂ :
      (fun n : ℕ => Real.sin (Real.pi * ((2 : ℝ) * (n : ℝ) + 3 / 2))) =
        fun _ : ℕ => (-1 : ℝ) := by
    funext n; exact sin_pi_two_n_add_three_halves n
  have h_neg_one_to_L :
      Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds L) :=
    h_const_seq₂ ▸ h_seq₂
  have h_neg_one_const :
      Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds (-1 : ℝ)) :=
    tendsto_const_nhds
  have hL_eq_neg_one :
      (-1 : ℝ) = L :=
    tendsto_nhds_unique (f := fun _ : ℕ => (-1 : ℝ))
      h_neg_one_const h_neg_one_to_L
  have : (1 : ℝ) = (-1 : ℝ) := hL_eq_one.trans hL_eq_neg_one.symm
  exact (by norm_num : (1 : ℝ) ≠ -1) this

/-- Example 3.5.4. The sequence `sin (π n)` converges to `0` as `n → ∞`. -/
lemma example_3_5_4_sequence_limit :
    Tendsto (fun n : ℕ => Real.sin (Real.pi * n)) atTop (nhds 0) := by
  have hconst :
      (fun n : ℕ => Real.sin (Real.pi * n)) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    simpa [mul_comm] using Real.sin_nat_mul_pi n
  exact hconst.symm ▸
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Lemma 3.5.5. If `f : S → ℝ`, `∞` is a cluster point of `S ⊆ ℝ`, and `L ∈ ℝ`, then
`lim_{x → ∞} f x = L` if and only if for every sequence `xₙ ∈ S` with `xₙ → ∞` one has
`lim_{n → ∞} f (xₙ) = L`. -/
lemma lemma_3_5_5 {S : Set ℝ} {f : S → ℝ} {L : ℝ}
    (_hS : book_clusterPoint_atTop S) :
    book_tendsto_atTop S f L ↔
      ∀ x : ℕ → S, Tendsto (fun n => (x n : ℝ)) atTop atTop →
        Tendsto (fun n => f (x n)) atTop (nhds L) := by
  constructor
  · intro hf x hx
    unfold Filter.Tendsto
    intro s hs
    obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨M, hM⟩ := hf ε εpos
    have hM_event : ∀ᶠ n : ℕ in atTop, M ≤ (x n : ℝ) :=
      (Filter.tendsto_atTop.1 hx) M
    have hball : ∀ᶠ n : ℕ in atTop, f (x n) ∈ Metric.ball L ε := by
      refine hM_event.mono ?_
      intro n hn
      have hlt : |f (x n) - L| < ε := hM (x n) hn
      simpa [Metric.mem_ball, Real.dist_eq] using hlt
    refine hball.mono ?_
    intro n hn
    exact hε hn
  · intro hseq
    classical
    by_contra hf
    unfold book_tendsto_atTop at hf
    push_neg at hf
    obtain ⟨ε, εpos, hε⟩ := hf
    have hforall : ∀ n : ℕ, ∃ x : S, (n : ℝ) ≤ (x : ℝ) ∧ ε ≤ |f x - L| := by
      intro n
      simpa using hε (n : ℝ)
    choose x hx using hforall
    have hx_tendsto : Tendsto (fun n => (x n : ℝ)) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro M
      obtain ⟨N, hN⟩ := exists_nat_ge M
      have hNreal : M ≤ (N : ℝ) := by exact_mod_cast hN
      refine Filter.eventually_atTop.2 ?_
      refine ⟨N, ?_⟩
      intro n hn
      have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hMle : M ≤ (n : ℝ) := hNreal.trans hnreal
      have hle : (n : ℝ) ≤ (x n : ℝ) := (hx n).1
      exact hMle.trans hle
    have hx_far : ∀ n, ε ≤ |f (x n) - L| := fun n => (hx n).2
    have hlimit := hseq x hx_tendsto
    have hball := hlimit.eventually (Metric.ball_mem_nhds _ εpos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hball
    have hmem : f (x N) ∈ Metric.ball L ε := hN N (le_rfl)
    have hlt : dist (f (x N)) L < ε := by
      simpa [Metric.mem_ball] using hmem
    have hge : ε ≤ dist (f (x N)) L := by
      simpa [Real.dist_eq] using hx_far N
    exact (not_lt_of_ge hge) hlt

/-- Definition 3.5.6. If `S ⊆ ℝ` has `∞` as a cluster point, a function `f : S → ℝ` is said to
diverge to `∞` as `x → ∞` provided that for every real bound `N` there is some `M` such that
whenever `x ∈ S` with `x ≥ M`, we have `f x > N`; this is written as `lim_{x → ∞} f x = ∞`. -/
def book_tendsto_atTop_top (S : Set ℝ) (f : S → ℝ) : Prop :=
  ∀ N : ℝ, ∃ M : ℝ, ∀ x : S, M ≤ (x : ℝ) → N < f x

/-- The book notion that a function diverges to `∞` agrees with the standard `Tendsto` formulation
to the filter `atTop` on `ℝ`. -/
lemma book_tendsto_atTop_top_iff_tendsto {S : Set ℝ} {f : S → ℝ}
    (hS : book_clusterPoint_atTop S) :
    book_tendsto_atTop_top S f ↔ Tendsto f atTop (atTop : Filter ℝ) := by
  haveI : Nonempty S := by
    rcases hS 0 with ⟨x, hxS, _⟩
    exact ⟨⟨x, hxS⟩⟩
  constructor
  · intro h
    refine (Filter.tendsto_atTop_atTop.2 ?_)
    intro b
    rcases h b with ⟨M, hM⟩
    obtain ⟨a, haS, hMa⟩ := hS M
    refine ⟨⟨a, haS⟩, ?_⟩
    intro x hx
    have hMx : M ≤ (x : ℝ) := le_trans hMa hx
    have hlt : b < f x := hM x hMx
    exact le_of_lt hlt
  · intro h N
    rcases (Filter.tendsto_atTop_atTop.1 h) (N + 1) with ⟨i, hi⟩
    refine ⟨(i : ℝ), ?_⟩
    intro x hx
    have hx' : i ≤ x := by simpa using hx
    have hle : N + 1 ≤ f x := hi x hx'
    have hNlt : N < N + 1 := by linarith
    exact hNlt.trans_le hle

/-- Helper for Example 3.5.7: for `x ≥ 1`, `(1 + x^2) / (1 + x)` dominates `x / 2`. -/
lemma example_3_5_7_lower_bound {x : ℝ} (hx : 1 ≤ x) :
    (1 + x ^ 2) / (1 + x) ≥ x / 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hxquad' : 0 ≤ (x - 1 / 2) ^ 2 + 7 / 4 :=
    add_nonneg (sq_nonneg _) (by norm_num)
  have hxquad : 0 ≤ x ^ 2 - x + 2 := by
    convert hxquad' using 1
    · ring
  have hdiff : 2 * (1 + x ^ 2) - x * (1 + x) = x ^ 2 - x + 2 := by ring
  have hxineq : x * (1 + x) ≤ 2 * (1 + x ^ 2) := by
    have hnonneg : 0 ≤ 2 * (1 + x ^ 2) - x * (1 + x) := by
      simpa [hdiff] using hxquad
    exact sub_nonneg.mp hnonneg
  have hxhalf : (x / 2) * (1 + x) ≤ 1 + x ^ 2 := by
    have hxmul :=
      (mul_le_mul_of_nonneg_right hxineq (by norm_num : (0 : ℝ) ≤ (1 / 2)))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hxmul
  have hne : (1 + x) ≠ 0 := ne_of_gt hpos
  have hxhalf' :
      (x / 2) * (1 + x) ≤ ((1 + x ^ 2) / (1 + x)) * (1 + x) := by
    simpa [div_eq_mul_inv, hne, mul_comm, mul_left_comm, mul_assoc] using hxhalf
  exact le_of_mul_le_mul_right hxhalf' hpos

/-- Helper for Example 3.5.7: `x / 2` diverges to `∞`. -/
lemma example_3_5_7_half_eventually (N : ℝ) :
    (∀ᶠ x : ℝ in atTop, N < x / 2) := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2 * (N + 1), ?_⟩
  intro x hx
  have hx_half : N + 1 ≤ x / 2 := by
    have hx_mul : (N + 1) * 2 ≤ x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hx
    have hx_mul' :
        ((N + 1) * 2) * (1 / 2) ≤ x * (1 / 2) :=
      mul_le_mul_of_nonneg_right hx_mul (by norm_num : (0 : ℝ) ≤ (1 / 2))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hx_mul'
  have hNlt : N < N + 1 := by linarith
  exact hNlt.trans_le hx_half

/-- Example 3.5.7. The limit of `(1 + x^2) / (1 + x)` as `x → ∞` diverges to `∞`. -/
lemma example_3_5_7 :
    Tendsto (fun x : ℝ => (1 + x ^ 2) / (1 + x)) atTop (atTop : Filter ℝ) := by
  refine Filter.tendsto_atTop.2 ?_
  intro N
  have h_ge_one : ∀ᶠ x : ℝ in atTop, 1 ≤ x := by
    refine Filter.eventually_atTop.2 ?_
    exact ⟨1, fun x hx => hx⟩
  have h_half := example_3_5_7_half_eventually N
  have hNlt : ∀ᶠ x : ℝ in atTop, N < (1 + x ^ 2) / (1 + x) := by
    refine (h_ge_one.and h_half).mono ?_
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hx_lower := example_3_5_7_lower_bound hx1
    exact hx2.trans_le hx_lower
  refine hNlt.mono ?_
  intro x hx
  exact le_of_lt hx

/-- Proposition 3.5.8. Let `f : A → B` and `g : B → ℝ` with `A, B ⊆ ℝ`, where `a` is a cluster
point of `A` and `b` is a cluster point of `B`. Assume `lim_{x → a} f x = b` and
`lim_{y → b} g y = c` for some `c ∈ ℝ ∪ {±∞}`; if moreover `b ∈ B`, suppose `g b = c`. Then
`lim_{x → a} g (f x) = c`. -/
lemma proposition_3_5_8 {A B : Set ℝ} {f : ℝ → ℝ} {g : ℝ → EReal}
    {a b : ℝ} {c : EReal}
    (_ha : ClusterPt a (Filter.principal A)) (_hb : ClusterPt b (Filter.principal B))
    (hf_map : Set.MapsTo f A B)
    (hf : Tendsto f (nhdsWithin a A) (nhds b))
    (hg : Tendsto g (nhdsWithin b B) (nhds c))
    (_hbmem : b ∈ B → g b = c) :
    Tendsto (fun x => g (f x)) (nhdsWithin a A) (nhds c) := by
  have hA : ∀ᶠ x in nhdsWithin a A, x ∈ A :=
    (mem_inf_of_right (f := nhds a) (g := 𝓟 A) (s := A) (by
      simp))
  have hB : ∀ᶠ x in nhdsWithin a A, f x ∈ B := by
    refine hA.mono ?_
    intro x hx
    exact hf_map hx
  have hfB : Tendsto f (nhdsWithin a A) (𝓟 B) :=
    (tendsto_principal.2 hB)
  have hf' : Tendsto f (nhdsWithin a A) (nhdsWithin b B) :=
    (tendsto_inf.2 ⟨hf, hfB⟩)
  exact hg.comp hf'

/-- For any real bound `M`, the quadratic expression `-x^2 + x` is eventually below `M`
along `Filter.atTop`. -/
lemma neg_quad_eventually_le (M : ℝ) :
    (∀ᶠ x : ℝ in atTop, -x ^ 2 + x ≤ M) := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨|M| + 1, ?_⟩
  intro x hx
  have h_abs_le : |M| ≤ x - 1 := by
    have hx' := sub_le_sub_right hx (1 : ℝ)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
  have hx_nonneg : 0 ≤ x := by
    have hB : 0 ≤ |M| + 1 := by
      exact add_nonneg (abs_nonneg M) (by norm_num)
    exact hB.trans hx
  have hx_mul₁ :
      (|M| + 1) * |M| ≤ x * |M| :=
    mul_le_mul_of_nonneg_right hx (abs_nonneg M)
  have hx_mul₂ :
      x * |M| ≤ x * (x - 1) :=
    mul_le_mul_of_nonneg_left h_abs_le hx_nonneg
  have h_mul : (|M| + 1) * |M| ≤ x * (x - 1) := hx_mul₁.trans hx_mul₂
  have h_abs_le_mul : |M| ≤ (|M| + 1) * |M| := by
    have h_abs_nonneg : 0 ≤ |M| := abs_nonneg M
    have h_one_le : (1 : ℝ) ≤ |M| + 1 := by
      have := h_abs_nonneg
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left h_one_le h_abs_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hx_sq : |M| ≤ x ^ 2 - x := by
    calc
      |M| ≤ (|M| + 1) * |M| := h_abs_le_mul
      _ ≤ x * (x - 1) := h_mul
      _ = x ^ 2 - x := by ring
  have hx_neg : -x ^ 2 + x ≤ -|M| := by
    have := neg_le_neg hx_sq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact hx_neg.trans (neg_abs_le M)

/-- The quadratic polynomial `-x^2 + x` tends to `-∞` along `Filter.atTop`. -/
lemma tendsto_neg_quad_atTop_atBot :
    Tendsto (fun x : ℝ => -x ^ 2 + x) atTop atBot := by
  refine Filter.tendsto_atBot.2 ?_
  intro M
  exact neg_quad_eventually_le M

/-- Example 3.5.9. For `h x = e ^ (-x^2 + x)`, we have `lim_{x → ∞} h x = 0`, using that
`-x^2 + x → -∞` and `e^y → 0` as `y → -∞`. -/
lemma example_3_5_9 :
    Tendsto (fun x : ℝ => Real.exp (-x ^ 2 + x)) atTop (nhds 0) := by
  exact Real.tendsto_exp_atBot.comp tendsto_neg_quad_atTop_atBot

end Section05
end Chap03
