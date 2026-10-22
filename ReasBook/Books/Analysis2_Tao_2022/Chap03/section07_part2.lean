/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap03.section07_part1

section Chap03
section Section07

/-- Theorem 3.10: if `f_n : [a,b] → ℝ` are differentiable with continuous derivatives,
the series `∑ ‖f_n'‖∞` (equation (3.u126)) is convergent, and `∑ f_n(x0)` converges for
some `x0 ∈ [a,b]`, then the series `∑ f_n` converges uniformly on `[a,b]` to a differentiable
function `f`, and for all `x ∈ [a,b]` one has equation (3.u127):
`f'(x) = d/dx (∑ f_n(x)) = ∑ f_n'(x)`. -/
theorem uniformLimit_of_summable_deriv_supNorm
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff : ∀ n : ℕ, DifferentiableOn ℝ (f (n + 1)) (Set.Icc a b))
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (h_summable :
      Summable
        (fun n : ℕ =>
          supNormOn (Set.Icc a b) (fun x => deriv (f (n + 1)) x)))
    (hx0 : ∃ x0 ∈ Set.Icc a b, Summable (fun n : ℕ => f (n + 1) x0)) :
    ∃ f_lim : ℝ → ℝ,
      DifferentiableOn ℝ f_lim (Set.Icc a b) ∧
        TendstoUniformlyOn
          (fun N x => (Finset.range N).sum (fun n => f (n + 1) x)) f_lim
          Filter.atTop (Set.Icc a b) ∧
        ∀ x ∈ Set.Icc a b,
          deriv f_lim x = tsum (fun n : ℕ => deriv (f (n + 1)) x) :=
  by
    rcases hx0 with ⟨x0, hx0_mem, hx0_summable⟩
    let g : ℝ → ℝ := fun x => tsum (fun n : ℕ => deriv (f (n + 1)) x)
    have h_unif_derivSeries :
        TendstoUniformlyOn
          (fun N x => (Finset.range N).sum (fun n => deriv (f (n + 1)) x))
          g Filter.atTop (Set.Icc a b) := by
      simpa [g] using
        helperForTheorem_3_10_tendstoUniformlyOn_derivSeries f h_diff_cont h_summable
    let F : ℕ → ℝ → ℝ := fun N => helperForTheorem_3_10_liftedPartialSum ha f x0 N
    have h_diff_F : ∀ n, 1 ≤ n → DifferentiableOn ℝ (F n) (Set.Icc a b) := by
      intro n hn
      simpa [F] using
        (helperForTheorem_3_10_differentiableOn_liftedPartialSum
          (a := a) (b := b) (ha := ha) (f := f)
          h_diff_cont x0 n)
    have h_diff_cont_F :
        ∀ n, 1 ≤ n → ContinuousOn (fun x => deriv (F n) x) (Set.Icc a b) := by
      intro n hn
      simpa [F] using
        (helperForTheorem_3_10_continuousOn_deriv_liftedPartialSum
          (a := a) (b := b) (ha := ha) (f := f)
          h_diff_cont x0 n)
    have h_unif_F :
        TendstoUniformlyOn (fun n x => deriv (F n) x) g Filter.atTop (Set.Icc a b) := by
      refine Metric.tendstoUniformlyOn_iff.mpr ?_
      intro ε hε
      have hraw :
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ x ∈ Set.Icc a b,
              dist (g x) ((Finset.range n).sum (fun k => deriv (f (k + 1)) x)) < ε :=
        (Metric.tendstoUniformlyOn_iff.mp h_unif_derivSeries) ε hε
      filter_upwards [hraw] with n hn x hx
      have hderiv_eq :
          deriv (F n) x = (Finset.range n).sum (fun k => deriv (f (k + 1)) x) := by
        simpa [F] using
          (helperForTheorem_3_10_deriv_liftedPartialSum_on_Icc
            (a := a) (b := b) (ha := ha) (f := f)
            h_diff_cont x0 n hx)
      simpa [hderiv_eq] using hn x hx
    have hx0_tendsto :
        ∃ x0' ∈ Set.Icc a b, ∃ l,
          Filter.Tendsto (fun n => F n x0') Filter.atTop (nhds l) := by
      refine ⟨x0, hx0_mem, tsum (fun n : ℕ => f (n + 1) x0), ?_⟩
      simpa [F, helperForTheorem_3_10_liftedPartialSum] using
        (hx0_summable.hasSum.tendsto_sum_nat)
    rcases
      uniformLimit_of_uniformlyConvergentDerivatives
        (a := a) (b := b) ha F g h_diff_F h_diff_cont_F h_unif_F hx0_tendsto with
      ⟨f_lim, h_diff_lim, h_unif_lifted, h_deriv_lim⟩
    refine ⟨f_lim, h_diff_lim, ?_, ?_⟩
    · refine Metric.tendstoUniformlyOn_iff.mpr ?_
      intro ε hε
      have hlift :
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ x ∈ Set.Icc a b,
              dist (f_lim x) (F n x) < ε :=
        (Metric.tendstoUniformlyOn_iff.mp h_unif_lifted) ε hε
      filter_upwards [hlift] with n hn x hx
      have hEq :
          F n x = (Finset.range n).sum (fun k => f (k + 1) x) := by
        simpa [F] using
          (helperForTheorem_3_10_lifted_eq_rawPartialSum_on_Icc
            (a := a) (b := b) (ha := ha) (f := f)
            h_diff h_diff_cont hx0_mem hx n)
      simpa [hEq] using hn x hx
    · intro x hx
      simpa [g] using h_deriv_lim x hx

/-- Definition 3.11: the Weierstrass function `f : ℝ → ℝ` defined by
`f(x) = ∑_{n=1}^{∞} 4^{-n} cos(32^n π x)`. -/
noncomputable def weierstrassFunction (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((4 : ℝ) ^ (n + 1))⁻¹ * Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)

/-- Helper for Proposition 3.21: each Weierstrass summand is continuous. -/
lemma helperForProposition_3_21_termContinuous (n : ℕ) :
    Continuous
      (fun x : ℝ =>
        ((4 : ℝ) ^ (n + 1))⁻¹ *
          Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)) := by
  have hlin :
      Continuous (fun x : ℝ => (((32 : ℝ) ^ (n + 1)) * Real.pi) * x) :=
    continuous_const.mul continuous_id
  have hcos :
      Continuous
        (fun x : ℝ => Real.cos ((((32 : ℝ) ^ (n + 1)) * Real.pi) * x)) :=
    Real.continuous_cos.comp hlin
  simpa [mul_assoc] using (continuous_const.mul hcos)

/-- Helper for Proposition 3.21: rewrite Weierstrass coefficients as geometric powers. -/
lemma helperForProposition_3_21_coeffRewrite (n : ℕ) :
    ((4 : ℝ) ^ (n + 1))⁻¹ = (1 / 4 : ℝ) ^ (n + 1) := by
  calc
    ((4 : ℝ) ^ (n + 1))⁻¹ = ((4 : ℝ)⁻¹) ^ (n + 1) := by
      simpa using (inv_pow (4 : ℝ) (n + 1)).symm
    _ = (1 / 4 : ℝ) ^ (n + 1) := by norm_num [one_div]

/-- Helper for Proposition 3.21: the geometric majorant for Weierstrass coefficients is summable. -/
lemma helperForProposition_3_21_majorantSummable :
    Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hgeom.mul_left (1 / 4 : ℝ)

/-- Helper for Proposition 3.21: each Weierstrass summand is bounded by the geometric majorant. -/
lemma helperForProposition_3_21_termNormBound (n : ℕ) (x : ℝ) :
    ‖((4 : ℝ) ^ (n + 1))⁻¹ *
        Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)‖ ≤
      (1 / 4 : ℝ) ^ (n + 1) := by
  have hcos :
      ‖Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)‖ ≤ (1 : ℝ) := by
    simpa [Real.norm_eq_abs] using
      (Real.abs_cos_le_one (((32 : ℝ) ^ (n + 1)) * Real.pi * x))
  have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ (n + 1) := by positivity
  calc
    ‖((4 : ℝ) ^ (n + 1))⁻¹ * Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)‖
        = ‖(1 / 4 : ℝ) ^ (n + 1) * Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)‖ := by
            rw [helperForProposition_3_21_coeffRewrite]
    _ = ‖(1 / 4 : ℝ) ^ (n + 1)‖ * ‖Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)‖ :=
          by rw [norm_mul]
    _ ≤ ‖(1 / 4 : ℝ) ^ (n + 1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
    _ = (1 / 4 : ℝ) ^ (n + 1) := by
          simp [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]

/-- Proposition 3.21: the Weierstrass function `f` of Definition 3.11 is continuous on `ℝ`. -/
theorem proposition_3_21 : Continuous weierstrassFunction :=
  by
    simpa [weierstrassFunction] using
      (continuous_tsum
        (fun n : ℕ => helperForProposition_3_21_termContinuous n)
        helperForProposition_3_21_majorantSummable
        (fun n x => helperForProposition_3_21_termNormBound n x))

/-- Helper for Proposition 3.22: quarter-turn cosine increments at a phase `θ` rewrite in
terms of `sin θ` and `cos θ`. -/
lemma helperForProposition_3_22_cosQuarterTurns (θ : ℝ) :
    (Real.cos (θ + Real.pi / 2) - Real.cos θ = -(Real.sin θ + Real.cos θ)) ∧
      (Real.cos (θ + 3 * Real.pi / 2) - Real.cos θ = Real.sin θ - Real.cos θ) := by
  constructor
  · calc
      Real.cos (θ + Real.pi / 2) - Real.cos θ = -Real.sin θ - Real.cos θ := by
        rw [Real.cos_add_pi_div_two]
      _ = -(Real.sin θ + Real.cos θ) := by ring_nf
  · have hcos : Real.cos (θ + 3 * Real.pi / 2) = Real.sin θ := by
      calc
        Real.cos (θ + 3 * Real.pi / 2) = Real.cos ((θ + Real.pi) + Real.pi / 2) := by ring_nf
        _ = -Real.sin (θ + Real.pi) := by
              simpa using Real.cos_add_pi_div_two (θ + Real.pi)
        _ = Real.sin θ := by simp [Real.sin_add_pi]
    calc
      Real.cos (θ + 3 * Real.pi / 2) - Real.cos θ = Real.sin θ - Real.cos θ := by
        rw [hcos]

/-- Helper for Proposition 3.22: for every phase `θ`, one of the shifts by `π/2` or `3π/2`
changes cosine by at least `1` in absolute value. -/
lemma helperForProposition_3_22_phaseChoiceCore (θ : ℝ) :
    ∃ j ∈ ({1, 3} : Set ℕ),
      1 ≤ |Real.cos (θ + (j : ℝ) * Real.pi / 2) - Real.cos θ| := by
  rcases helperForProposition_3_22_cosQuarterTurns θ with ⟨hquarter, hthreeQuarter⟩
  let u : ℝ := |Real.sin θ + Real.cos θ|
  let v : ℝ := |Real.sin θ - Real.cos θ|
  have hsum : u ^ 2 + v ^ 2 = 2 := by
    have hu_sq : u ^ 2 = (Real.sin θ + Real.cos θ) ^ 2 := by
      simp [u, sq_abs]
    have hv_sq : v ^ 2 = (Real.sin θ - Real.cos θ) ^ 2 := by
      simp [v, sq_abs]
    rw [hu_sq, hv_sq]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hmax : 1 ≤ max u v := by
    by_contra h
    have hlt : max u v < 1 := lt_of_not_ge h
    have hu_lt : u < 1 := lt_of_le_of_lt (le_max_left u v) hlt
    have hv_lt : v < 1 := lt_of_le_of_lt (le_max_right u v) hlt
    have hu_sq_lt : u ^ 2 < 1 := by
      have hu_nonneg : 0 ≤ u := by
        simp [u]
      nlinarith
    have hv_sq_lt : v ^ 2 < 1 := by
      have hv_nonneg : 0 ≤ v := by
        simp [v]
      nlinarith
    have hsum_lt : u ^ 2 + v ^ 2 < 2 := by
      nlinarith
    linarith
  by_cases huv : u ≤ v
  · have hv_ge : 1 ≤ v := by
      calc
        1 ≤ max u v := hmax
        _ = v := max_eq_right huv
    refine ⟨3, by simp, ?_⟩
    have hrewrite :
        |Real.cos (θ + (3 : ℝ) * Real.pi / 2) - Real.cos θ| = v := by
      calc
        |Real.cos (θ + (3 : ℝ) * Real.pi / 2) - Real.cos θ|
            = |Real.cos (θ + 3 * Real.pi / 2) - Real.cos θ| := by ring_nf
        _ = |Real.sin θ - Real.cos θ| := by rw [hthreeQuarter]
        _ = v := by simp [v]
    simpa [hrewrite] using hv_ge
  · have hvu : v ≤ u := le_of_not_ge huv
    have hu_ge : 1 ≤ u := by
      calc
        1 ≤ max u v := hmax
        _ = u := max_eq_left hvu
    refine ⟨1, by simp, ?_⟩
    have hrewrite :
        |Real.cos (θ + Real.pi / 2) - Real.cos θ| = u := by
      calc
        |Real.cos (θ + Real.pi / 2) - Real.cos θ| = |-Real.sin θ - Real.cos θ| := by
          rw [Real.cos_add_pi_div_two]
        _ = |-(Real.sin θ + Real.cos θ)| := by ring_nf
        _ = |Real.sin θ + Real.cos θ| := by simpa using abs_neg (Real.sin θ + Real.cos θ)
        _ = u := by simp [u]
    have hu_goal : 1 ≤ |Real.cos (θ + Real.pi / 2) - Real.cos θ| := by
      simpa [hrewrite] using hu_ge
    simpa using hu_goal

/-- Helper for Proposition 3.22: instantiate the phase-choice lemma at Weierstrass scale `N`. -/
lemma helperForProposition_3_22_phaseChoice (x : ℝ) (N : ℕ) :
    ∃ j ∈ ({1, 3} : Set ℕ),
      1 ≤
        |Real.cos ((((32 : ℝ) ^ (N + 1)) * Real.pi * x) + (j : ℝ) * Real.pi / 2) -
            Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x)| := by
  simpa using
    helperForProposition_3_22_phaseChoiceCore (((32 : ℝ) ^ (N + 1)) * Real.pi * x)

/-- Helper for Proposition 3.22: choose a phase index `j_N(x) ∈ {1,3}` at each scale `N`. -/
noncomputable def helperForProposition_3_22_phaseIndex (x : ℝ) (N : ℕ) : ℕ :=
  Classical.choose (helperForProposition_3_22_phaseChoice x N)

/-- Helper for Proposition 3.22: the chosen phase index lies in `{1,3}`. -/
lemma helperForProposition_3_22_phaseIndex_mem (x : ℝ) (N : ℕ) :
    helperForProposition_3_22_phaseIndex x N ∈ ({1, 3} : Set ℕ) := by
  exact (Classical.choose_spec (helperForProposition_3_22_phaseChoice x N)).1

/-- Helper for Proposition 3.22: the chosen phase index forces a unit-sized cosine increment. -/
lemma helperForProposition_3_22_phaseIndex_largeCosIncrement (x : ℝ) (N : ℕ) :
    1 ≤
      |Real.cos
            ((((32 : ℝ) ^ (N + 1)) * Real.pi * x) +
              (helperForProposition_3_22_phaseIndex x N : ℝ) * Real.pi / 2) -
          Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x)| := by
  exact (Classical.choose_spec (helperForProposition_3_22_phaseChoice x N)).2

/-- Helper for Proposition 3.22: the chosen phase index is positive. -/
lemma helperForProposition_3_22_phaseIndex_pos (x : ℝ) (N : ℕ) :
    0 < (helperForProposition_3_22_phaseIndex x N : ℝ) := by
  have hmem := helperForProposition_3_22_phaseIndex_mem x N
  have hcases :
      helperForProposition_3_22_phaseIndex x N = 1 ∨
        helperForProposition_3_22_phaseIndex x N = 3 := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hcases with h1 | h3
  · norm_num [h1]
  · norm_num [h3]

/-- Helper for Proposition 3.22: define the scale `h_N(x) = j_N(x)/(2·32^(N+1))`. -/
noncomputable def helperForProposition_3_22_scale (x : ℝ) (N : ℕ) : ℝ :=
  (helperForProposition_3_22_phaseIndex x N : ℝ) / (2 * (32 : ℝ) ^ (N + 1))

/-- Helper for Proposition 3.22: all chosen scales are positive. -/
lemma helperForProposition_3_22_scale_pos (x : ℝ) (N : ℕ) :
    0 < helperForProposition_3_22_scale x N := by
  unfold helperForProposition_3_22_scale
  refine div_pos (helperForProposition_3_22_phaseIndex_pos x N) ?_
  positivity

/-- Helper for Proposition 3.22: the chosen phase index is either `1` or `3`. -/
lemma helperForProposition_3_22_phaseIndex_eq_one_or_three (x : ℝ) (N : ℕ) :
    helperForProposition_3_22_phaseIndex x N = 1 ∨
      helperForProposition_3_22_phaseIndex x N = 3 := by
  have hmem := helperForProposition_3_22_phaseIndex_mem x N
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

/-- Helper for Proposition 3.22: the chosen phase index is at most `3`. -/
lemma helperForProposition_3_22_phaseIndex_le_three (x : ℝ) (N : ℕ) :
    (helperForProposition_3_22_phaseIndex x N : ℝ) ≤ 3 := by
  rcases helperForProposition_3_22_phaseIndex_eq_one_or_three x N with h1 | h3
  · norm_num [h1]
  · norm_num [h3]

/-- Helper for Proposition 3.22: each chosen scale is bounded by `3/(2·32^(N+1))`. -/
lemma helperForProposition_3_22_scale_le_three_div (x : ℝ) (N : ℕ) :
    helperForProposition_3_22_scale x N ≤ (3 : ℝ) / (2 * (32 : ℝ) ^ (N + 1)) := by
  unfold helperForProposition_3_22_scale
  refine div_le_div_of_nonneg_right ?_ ?_
  · exact helperForProposition_3_22_phaseIndex_le_three x N
  · positivity

/-- Helper for Proposition 3.22: the model upper bound `3/(2·32^(N+1))` tends to `0`. -/
lemma helperForProposition_3_22_threeDivPow_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => (3 : ℝ) / (2 * (32 : ℝ) ^ (N + 1)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hpow0 :
      Filter.Tendsto (fun N : ℕ => (1 / 32 : ℝ) ^ N) Filter.atTop (nhds (0 : ℝ)) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hpow1 :
      Filter.Tendsto (fun N : ℕ => (1 / 32 : ℝ) ^ (N + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hpow0.comp (Filter.tendsto_add_atTop_nat 1)
  have hmul :
      Filter.Tendsto (fun N : ℕ => (3 / 2 : ℝ) * ((1 / 32 : ℝ) ^ (N + 1)))
        Filter.atTop (nhds ((3 / 2 : ℝ) * 0)) :=
    (tendsto_const_nhds.mul hpow1)
  have hEq :
      (fun N : ℕ => (3 : ℝ) / (2 * (32 : ℝ) ^ (N + 1))) =
        (fun N : ℕ => (3 / 2 : ℝ) * ((1 / 32 : ℝ) ^ (N + 1))) := by
    funext N
    have hpow_ne : (32 : ℝ) ^ (N + 1) ≠ 0 := by positivity
    calc
      (3 : ℝ) / (2 * (32 : ℝ) ^ (N + 1)) = (3 / 2 : ℝ) * ((32 : ℝ) ^ (N + 1))⁻¹ := by
        field_simp [div_eq_mul_inv, hpow_ne]
      _ = (3 / 2 : ℝ) * ((1 / 32 : ℝ) ^ (N + 1)) := by
        simp [one_div, inv_pow]
  rw [hEq]
  simpa using hmul

/-- Helper for Proposition 3.22: the chosen scales tend to `0`. -/
lemma helperForProposition_3_22_scale_tendsto_zero (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => helperForProposition_3_22_scale x N)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hconst0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hconst0
    helperForProposition_3_22_threeDivPow_tendsto_zero ?_ ?_
  · exact fun N => le_of_lt (helperForProposition_3_22_scale_pos x N)
  · exact fun N => helperForProposition_3_22_scale_le_three_div x N

/-- Helper for Proposition 3.22: the chosen scales approach `0` through positive values. -/
lemma helperForProposition_3_22_scale_tendsto_nhdsWithin_zero (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => helperForProposition_3_22_scale x N)
      Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.2 ?_
  exact ⟨
    helperForProposition_3_22_scale_tendsto_zero x,
    Filter.Eventually.of_forall (fun N => helperForProposition_3_22_scale_pos x N)
  ⟩

/-- Helper for Proposition 3.22: any real sequence with exponential lower bound
`(8^N ≤ |q_N|)` cannot converge to a finite real limit. -/
lemma helperForProposition_3_22_notTendsto_of_absLowerBound
    {q : ℕ → ℝ} (hbound : ∀ N : ℕ, (8 : ℝ) ^ N ≤ |q N|) (L : ℝ) :
    ¬ Filter.Tendsto q Filter.atTop (nhds L) := by
  intro hq
  have hball : ∀ᶠ N : ℕ in Filter.atTop, q N ∈ Metric.ball L 1 := by
    have hmem : Metric.ball L 1 ∈ nhds L := by
      exact Metric.ball_mem_nhds L (by norm_num)
    exact Filter.Tendsto.eventually hq hmem
  have hupper : ∀ᶠ N : ℕ in Filter.atTop, |q N| ≤ |L| + 1 := by
    filter_upwards [hball] with N hN
    have hdist : dist (q N) L < 1 := hN
    have hsub : |q N - L| < 1 := by
      simpa [Real.dist_eq] using hdist
    have hqle : |q N| ≤ |q N - L| + |L| := by
      have habs : |(q N - L) + L| ≤ |q N - L| + |L| := by
        simpa [Real.norm_eq_abs] using (norm_add_le (q N - L) L)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using habs
    have hlt : |q N| < |L| + 1 := by
      linarith
    exact le_of_lt hlt
  have hpow :
      Filter.Tendsto (fun N : ℕ => (8 : ℝ) ^ N) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop, |L| + 2 ≤ (8 : ℝ) ^ N :=
    (Filter.tendsto_atTop.1 hpow) (|L| + 2)
  rcases Filter.eventually_atTop.1 hupper with ⟨N1, hN1⟩
  rcases Filter.eventually_atTop.1 hlarge with ⟨N2, hN2⟩
  let N : ℕ := max N1 N2
  have hpowLower : |L| + 2 ≤ (8 : ℝ) ^ N := hN2 N (le_max_right _ _)
  have hqUpper : |q N| ≤ |L| + 1 := hN1 N (le_max_left _ _)
  have hqLower : (8 : ℝ) ^ N ≤ |q N| := hbound N
  linarith

/-- Helper for Proposition 3.22: the basic Weierstrass summand at index `n`. -/
noncomputable def helperForProposition_3_22_term (n : ℕ) (x : ℝ) : ℝ :=
  ((4 : ℝ) ^ (n + 1))⁻¹ * Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x)

/-- Helper for Proposition 3.22: each Weierstrass term sequence is summable at fixed `x`. -/
lemma helperForProposition_3_22_termSummable (x : ℝ) :
    Summable (fun n : ℕ => helperForProposition_3_22_term n x) := by
  have hsummable_norm :
      Summable (fun n : ℕ => ‖helperForProposition_3_22_term n x‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1))
      (g := fun n : ℕ => ‖helperForProposition_3_22_term n x‖)
      (fun n => by positivity)
      ?_
      helperForProposition_3_21_majorantSummable
    intro n
    simpa [helperForProposition_3_22_term] using
      helperForProposition_3_21_termNormBound n x
  exact (summable_norm_iff.mp hsummable_norm)

/-- Helper for Proposition 3.22: at chosen scale, all modes `n > N` cancel exactly. -/
lemma helperForProposition_3_22_tailCosCancellationAtChosenScale
    (x : ℝ) (N n : ℕ) (hn : N < n) :
    Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * (x + helperForProposition_3_22_scale x N)) =
      Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x) := by
  rcases Nat.exists_eq_add_of_lt hn with ⟨k, hk⟩
  have hshift :
      ((32 : ℝ) ^ (n + 1)) * Real.pi * helperForProposition_3_22_scale x N =
        ((helperForProposition_3_22_phaseIndex x N * 8 * 32 ^ k : ℕ) : ℝ) *
          (2 * Real.pi) := by
    have hn1 : n + 1 = (N + 1) + (k + 1) := by omega
    have hpowN_ne : ((32 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
    calc
      ((32 : ℝ) ^ (n + 1)) * Real.pi * helperForProposition_3_22_scale x N
          = ((32 : ℝ) ^ ((N + 1) + (k + 1))) * Real.pi *
              helperForProposition_3_22_scale x N := by simpa [hn1]
      _ = ((32 : ℝ) ^ (N + 1) * (32 : ℝ) ^ (k + 1)) * Real.pi *
            helperForProposition_3_22_scale x N := by rw [pow_add]
      _ = (((helperForProposition_3_22_phaseIndex x N : ℝ) * (32 : ℝ) ^ (k + 1)) *
            Real.pi / 2) := by
            unfold helperForProposition_3_22_scale
            field_simp [hpowN_ne]
      _ = ((helperForProposition_3_22_phaseIndex x N * 8 * 32 ^ k : ℕ) : ℝ) *
            (2 * Real.pi) := by
            calc
              (((helperForProposition_3_22_phaseIndex x N : ℝ) * (32 : ℝ) ^ (k + 1)) *
                  Real.pi / 2)
                  = ((helperForProposition_3_22_phaseIndex x N : ℝ) * 8 * ((32 : ℝ) ^ k)) *
                      (2 * Real.pi) := by
                        ring_nf
              _ = ((helperForProposition_3_22_phaseIndex x N * 8 * 32 ^ k : ℕ) : ℝ) *
                    (2 * Real.pi) := by
                      norm_num [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * (x + helperForProposition_3_22_scale x N))
        = Real.cos ((((32 : ℝ) ^ (n + 1)) * Real.pi * x) +
            (((32 : ℝ) ^ (n + 1)) * Real.pi * helperForProposition_3_22_scale x N)) := by
            ring_nf
    _ = Real.cos ((((32 : ℝ) ^ (n + 1)) * Real.pi * x) +
          (((helperForProposition_3_22_phaseIndex x N * 8 * 32 ^ k : ℕ) : ℝ) *
            (2 * Real.pi))) := by rw [hshift]
    _ = Real.cos (((32 : ℝ) ^ (n + 1)) * Real.pi * x) := by
          simpa [add_assoc] using
            Real.cos_add_nat_mul_two_pi
              ((((32 : ℝ) ^ (n + 1)) * Real.pi * x))
              (helperForProposition_3_22_phaseIndex x N * 8 * 32 ^ k)

/-- Helper for Proposition 3.22: ratio identity `32^(N+1)/4^(N+1)=8^(N+1)`. -/
lemma helperForProposition_3_22_powRatio (N : ℕ) :
    ((4 : ℝ) ^ (N + 1))⁻¹ * ((32 : ℝ) ^ (N + 1)) = (8 : ℝ) ^ (N + 1) := by
  calc
    ((4 : ℝ) ^ (N + 1))⁻¹ * ((32 : ℝ) ^ (N + 1))
        = ((32 : ℝ) ^ (N + 1)) / ((4 : ℝ) ^ (N + 1)) := by ring
    _ = ((32 : ℝ) / (4 : ℝ)) ^ (N + 1) := by
          simpa using (div_pow (32 : ℝ) 4 (N + 1)).symm
    _ = (8 : ℝ) ^ (N + 1) := by norm_num

/-- Helper for Proposition 3.22: a single scaled term-difference quotient is bounded by `π·8^(n+1)`. -/
lemma helperForProposition_3_22_termDifferenceQuotientBound
    (n : ℕ) (x h : ℝ) (hh : 0 < h) :
    |((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)| ≤
      Real.pi * (8 : ℝ) ^ (n + 1) := by
  let c : ℝ := ((32 : ℝ) ^ (n + 1)) * Real.pi
  have hterm_xh :
      helperForProposition_3_22_term n (x + h) =
        ((4 : ℝ) ^ (n + 1))⁻¹ * Real.cos (c * (x + h)) := by
    simp [helperForProposition_3_22_term, c, mul_assoc, mul_left_comm, mul_comm]
  have hterm_x :
      helperForProposition_3_22_term n x =
        ((4 : ℝ) ^ (n + 1))⁻¹ * Real.cos (c * x) := by
    simp [helperForProposition_3_22_term, c, mul_assoc, mul_left_comm, mul_comm]
  have hterm_diff :
      helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x =
        ((4 : ℝ) ^ (n + 1))⁻¹ * (Real.cos (c * (x + h)) - Real.cos (c * x)) := by
    rw [hterm_xh, hterm_x]
    ring
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcoeff_nonneg : 0 ≤ ((4 : ℝ) ^ (n + 1))⁻¹ := by positivity
  have hcos : |Real.cos (c * (x + h)) - Real.cos (c * x)| ≤ |c * (x + h) - c * x| :=
    Real.abs_cos_sub_cos_le (c * (x + h)) (c * x)
  calc
    |((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)|
        = |(((4 : ℝ) ^ (n + 1))⁻¹ * (Real.cos (c * (x + h)) - Real.cos (c * x))) / h| := by
            rw [hterm_diff]
    _ =
        |((4 : ℝ) ^ (n + 1))⁻¹ * (Real.cos (c * (x + h)) - Real.cos (c * x))| / |h| := by
          rw [abs_div]
    _ = (((4 : ℝ) ^ (n + 1))⁻¹ * |Real.cos (c * (x + h)) - Real.cos (c * x)|) / h := by
          rw [abs_mul, abs_of_nonneg hcoeff_nonneg, abs_of_pos hh]
    _ ≤ (((4 : ℝ) ^ (n + 1))⁻¹ * |c * (x + h) - c * x|) / h := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcos hcoeff_nonneg)
            (le_of_lt hh)
    _ = (((4 : ℝ) ^ (n + 1))⁻¹ * (c * h)) / h := by
          congr 1
          have hlin : c * (x + h) - c * x = c * h := by ring
          rw [hlin, abs_of_nonneg (mul_nonneg hc_nonneg (le_of_lt hh))]
    _ = ((4 : ℝ) ^ (n + 1))⁻¹ * c := by field_simp [hh.ne']
    _ = Real.pi * (8 : ℝ) ^ (n + 1) := by
          dsimp [c]
          calc
            ((4 : ℝ) ^ (n + 1))⁻¹ * (((32 : ℝ) ^ (n + 1)) * Real.pi)
                = (((4 : ℝ) ^ (n + 1))⁻¹ * ((32 : ℝ) ^ (n + 1))) * Real.pi := by ring
            _ = ((8 : ℝ) ^ (n + 1)) * Real.pi := by
                  rw [helperForProposition_3_22_powRatio n]
            _ = Real.pi * (8 : ℝ) ^ (n + 1) := by ring

/-- Helper for Proposition 3.22: geometric bound for the low-frequency remainder weights. -/
lemma helperForProposition_3_22_geometricBound (N : ℕ) :
    (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1)) ≤ (8 / 7 : ℝ) * (8 : ℝ) ^ N := by
  have hsum :
      (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1))
        = (8 : ℝ) * (∑ n ∈ Finset.range N, (8 : ℝ) ^ n) := by
    calc
      (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1))
          = (∑ n ∈ Finset.range N, (8 : ℝ) ^ n * 8) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [pow_succ, mul_comm]
      _ = (∑ n ∈ Finset.range N, 8 * (8 : ℝ) ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = (8 : ℝ) * (∑ n ∈ Finset.range N, (8 : ℝ) ^ n) := by
            simp [Finset.mul_sum]
  have hgeom :
      (∑ n ∈ Finset.range N, (8 : ℝ) ^ n) = (((8 : ℝ) ^ N) - 1) / 7 := by
    calc
      (∑ n ∈ Finset.range N, (8 : ℝ) ^ n) = (((8 : ℝ) ^ N) - 1) / ((8 : ℝ) - 1) := by
        simpa using (geom_sum_eq (x := (8 : ℝ)) (by norm_num : (8 : ℝ) ≠ 1) N)
      _ = (((8 : ℝ) ^ N) - 1) / 7 := by norm_num
  have hdiv : ((((8 : ℝ) ^ N) - 1) / 7) ≤ (((8 : ℝ) ^ N) / 7) := by
    have hsub : ((8 : ℝ) ^ N) - 1 ≤ (8 : ℝ) ^ N := by linarith
    exact div_le_div_of_nonneg_right hsub (by norm_num)
  calc
    (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1))
        = (8 : ℝ) * ((((8 : ℝ) ^ N) - 1) / 7) := by rw [hsum, hgeom]
    _ ≤ (8 : ℝ) * (((8 : ℝ) ^ N) / 7) := by
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = (8 / 7 : ℝ) * (8 : ℝ) ^ N := by ring

/-- Helper for Proposition 3.22: coefficient/scale algebra at phase index `j`. -/
lemma helperForProposition_3_22_coeffOverScale (N j : ℕ) (hjpos : 0 < (j : ℝ)) :
    ((4 : ℝ) ^ (N + 1))⁻¹ / ((j : ℝ) / (2 * (32 : ℝ) ^ (N + 1))) =
      ((16 : ℝ) / j) * (8 : ℝ) ^ N := by
  have hpow4_ne : ((4 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
  have hpow32_ne : ((32 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
  have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
  have hpow32 : (32 : ℝ) ^ N = (4 : ℝ) ^ N * (8 : ℝ) ^ N := by
    calc
      (32 : ℝ) ^ N = ((4 : ℝ) * (8 : ℝ)) ^ N := by norm_num
      _ = (4 : ℝ) ^ N * (8 : ℝ) ^ N := by rw [mul_pow]
  field_simp [hpow4_ne, hpow32_ne, hj_ne]
  rw [pow_succ, pow_succ, hpow32]
  ring

/-- Helper for Proposition 3.22: split the chosen-scale difference quotient into dominant
`n = N` term and low-frequency remainder (`n < N`). -/
lemma helperForProposition_3_22_differenceQuotientSplitAtScale (x : ℝ) (N : ℕ) :
    let h := helperForProposition_3_22_scale x N
    ((weierstrassFunction (x + h) - weierstrassFunction x) / h)
      =
      (((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
        +
        ∑ n ∈ Finset.range N,
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)) := by
  let h := helperForProposition_3_22_scale x N
  have hs1 : Summable (fun n : ℕ => helperForProposition_3_22_term n (x + h)) :=
    helperForProposition_3_22_termSummable (x + h)
  have hs2 : Summable (fun n : ℕ => helperForProposition_3_22_term n x) :=
    helperForProposition_3_22_termSummable x
  have hscale_ne : h ≠ 0 := by
    exact ne_of_gt (by simpa [h] using helperForProposition_3_22_scale_pos x N)
  have htsub :
      (∑' n : ℕ,
          (helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x))
        =
        (∑' n : ℕ, helperForProposition_3_22_term n (x + h))
          -
          (∑' n : ℕ, helperForProposition_3_22_term n x) := by
    simpa using (Summable.tsum_sub hs1 hs2)
  have hmul :
      (∑' n : ℕ,
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h))
        =
        ((∑' n : ℕ,
            (helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x)) / h) :=
      by
        have hsdiff :
            Summable
              (fun n : ℕ =>
                helperForProposition_3_22_term n (x + h) -
                  helperForProposition_3_22_term n x) :=
          hs1.sub hs2
        have hpoint :
            (fun n : ℕ =>
              (helperForProposition_3_22_term n (x + h) -
                  helperForProposition_3_22_term n x) / h)
              =
              (fun n : ℕ =>
                h⁻¹ *
                  (helperForProposition_3_22_term n (x + h) -
                    helperForProposition_3_22_term n x)) := by
              funext n
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        rw [hpoint]
        calc
          (∑' n : ℕ,
              h⁻¹ *
                (helperForProposition_3_22_term n (x + h) -
                  helperForProposition_3_22_term n x))
              = h⁻¹ *
                  (∑' n : ℕ,
                    (helperForProposition_3_22_term n (x + h) -
                      helperForProposition_3_22_term n x)) := by
                    simpa using (Summable.tsum_mul_left h⁻¹ hsdiff)
          _ =
              ((∑' n : ℕ,
                  (helperForProposition_3_22_term n (x + h) -
                    helperForProposition_3_22_term n x)) / h) := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have htail_zero :
      ∀ m : ℕ,
        ((helperForProposition_3_22_term (m + (N + 1)) (x + h) -
            helperForProposition_3_22_term (m + (N + 1)) x) / h) = 0 := by
    intro m
    have hn : N < m + (N + 1) := by omega
    have hcosEq :
        Real.cos (((32 : ℝ) ^ ((m + (N + 1)) + 1)) * Real.pi * (x + h))
          =
          Real.cos (((32 : ℝ) ^ ((m + (N + 1)) + 1)) * Real.pi * x) := by
      simpa [h] using
        helperForProposition_3_22_tailCosCancellationAtChosenScale x N (m + (N + 1)) hn
    simp [helperForProposition_3_22_term, hcosEq]
  have hsplit :
      (∑' n : ℕ,
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h))
        =
        (∑ n ∈ Finset.range (N + 1),
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)) :=
      by
        refine (tsum_eq_sum (s := Finset.range (N + 1)) ?_)
        intro n hn
        have hle : N + 1 ≤ n := by
          exact Nat.not_lt.mp (by simpa [Finset.mem_range] using hn)
        have hEq := htail_zero (n - (N + 1))
        have hindex : n - (N + 1) + (N + 1) = n := Nat.sub_add_cancel hle
        simpa [hindex, add_comm, add_left_comm, add_assoc] using hEq
  have hsplit2 :
      (∑ n ∈ Finset.range (N + 1),
        ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h))
        =
        (((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
          +
          ∑ n ∈ Finset.range N,
            ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) /
              h)) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
  calc
    ((weierstrassFunction (x + h) - weierstrassFunction x) / h)
        =
        (((∑' n : ℕ, helperForProposition_3_22_term n (x + h)) -
            (∑' n : ℕ, helperForProposition_3_22_term n x)) / h) := by
              simp [weierstrassFunction, helperForProposition_3_22_term]
    _ =
        (∑' n : ℕ,
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)) :=
          by rw [hmul, htsub]
    _ =
        (∑ n ∈ Finset.range (N + 1),
          ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)) :=
          hsplit
    _ =
        (((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
          +
          ∑ n ∈ Finset.range N,
            ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)) :=
          hsplit2

/-- Helper for Proposition 3.22: the dominant (`n = N`) increment has size at least
`(16/3)·8^N` at the chosen scale. -/
lemma helperForProposition_3_22_dominantTermLowerBoundAtScale (x : ℝ) (N : ℕ) :
    let h := helperForProposition_3_22_scale x N
    ((16 / 3 : ℝ) * (8 : ℝ) ^ N) ≤
      |((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)| := by
  let j : ℕ := helperForProposition_3_22_phaseIndex x N
  let h : ℝ := helperForProposition_3_22_scale x N
  let delta : ℝ :=
    Real.cos ((((32 : ℝ) ^ (N + 1)) * Real.pi * x) + (j : ℝ) * Real.pi / 2) -
      Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x)
  have hj_cases : j = 1 ∨ j = 3 := by
    simpa [j] using helperForProposition_3_22_phaseIndex_eq_one_or_three x N
  have hj_pos : 0 < (j : ℝ) := by
    simpa [j] using helperForProposition_3_22_phaseIndex_pos x N
  have hinc : 1 ≤ |delta| := by
    simpa [delta, j] using helperForProposition_3_22_phaseIndex_largeCosIncrement x N
  have harg : ((32 : ℝ) ^ (N + 1)) * Real.pi * h = (j : ℝ) * Real.pi / 2 := by
    dsimp [h, j, helperForProposition_3_22_scale]
    have hpow_ne : ((32 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
    field_simp [hpow_ne]
  have hcos_rewrite :
      Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * (x + h)) -
          Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x) =
        delta := by
    have hlin :
        ((32 : ℝ) ^ (N + 1)) * Real.pi * (x + h)
          = (((32 : ℝ) ^ (N + 1)) * Real.pi * x) +
              (((32 : ℝ) ^ (N + 1)) * Real.pi * h) := by
      ring
    dsimp [delta]
    rw [hlin, harg]
  have hcoef : ((4 : ℝ) ^ (N + 1))⁻¹ / h = ((16 : ℝ) / j) * (8 : ℝ) ^ N := by
    dsimp [h, j]
    exact helperForProposition_3_22_coeffOverScale N (helperForProposition_3_22_phaseIndex x N)
      (helperForProposition_3_22_phaseIndex_pos x N)
  have hterm_rewrite :
      ((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
        = (((16 : ℝ) / j) * (8 : ℝ) ^ N) * delta := by
    have hterm_xh :
        helperForProposition_3_22_term N (x + h)
          = ((4 : ℝ) ^ (N + 1))⁻¹ *
              Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * (x + h)) := by
      simp [helperForProposition_3_22_term]
    have hterm_x :
        helperForProposition_3_22_term N x
          = ((4 : ℝ) ^ (N + 1))⁻¹ *
              Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x) := by
      simp [helperForProposition_3_22_term]
    calc
      ((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
          = ((((4 : ℝ) ^ (N + 1))⁻¹ *
              (Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * (x + h)) -
                Real.cos (((32 : ℝ) ^ (N + 1)) * Real.pi * x))) / h) := by
                rw [hterm_xh, hterm_x]
                ring
      _ = ((((4 : ℝ) ^ (N + 1))⁻¹ * delta) / h) := by rw [hcos_rewrite]
      _ = (((4 : ℝ) ^ (N + 1))⁻¹ / h) * delta := by ring
      _ = (((16 : ℝ) / j) * (8 : ℝ) ^ N) * delta := by rw [hcoef]
  have hcoef_ge : (16 / 3 : ℝ) ≤ (16 : ℝ) / j := by
    rcases hj_cases with h1 | h3
    · norm_num [h1]
    · norm_num [h3]
  have hcoef_nonneg : 0 ≤ (16 : ℝ) / j := by
    rcases hj_cases with h1 | h3
    · norm_num [h1]
    · norm_num [h3]
  have hpow_nonneg : 0 ≤ (8 : ℝ) ^ N := by positivity
  have hmain : ((16 / 3 : ℝ) * (8 : ℝ) ^ N) ≤ ((16 : ℝ) / j) * (8 : ℝ) ^ N := by
    exact mul_le_mul_of_nonneg_right hcoef_ge hpow_nonneg
  have hprod :
      ((16 / 3 : ℝ) * (8 : ℝ) ^ N) * 1 ≤ (((16 : ℝ) / j) * (8 : ℝ) ^ N) * |delta| := by
    exact mul_le_mul hmain hinc (by norm_num) (mul_nonneg hcoef_nonneg hpow_nonneg)
  have hcoef_abs :
      |(((16 : ℝ) / j) * (8 : ℝ) ^ N * delta)| = (((16 : ℝ) / j) * (8 : ℝ) ^ N) * |delta| := by
    calc
      |(((16 : ℝ) / j) * (8 : ℝ) ^ N * delta)|
          = |((16 : ℝ) / j) * (8 : ℝ) ^ N| * |delta| := by rw [abs_mul]
      _ = (((16 : ℝ) / j) * (8 : ℝ) ^ N) * |delta| := by
            rw [abs_of_nonneg (mul_nonneg hcoef_nonneg hpow_nonneg)]
  calc
    ((16 / 3 : ℝ) * (8 : ℝ) ^ N)
        = ((16 / 3 : ℝ) * (8 : ℝ) ^ N) * 1 := by ring
    _ ≤ (((16 : ℝ) / j) * (8 : ℝ) ^ N) * |delta| := hprod
    _ = |(((16 : ℝ) / j) * (8 : ℝ) ^ N * delta)| := by
          exact hcoef_abs.symm
    _ = |((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)| := by
          rw [hterm_rewrite]

/-- Helper for Proposition 3.22: the low-frequency remainder (`n < N`) is bounded by
`(8π/7)·8^N` at the chosen scale. -/
lemma helperForProposition_3_22_remainderBoundAtScale (x : ℝ) (N : ℕ) :
    let h := helperForProposition_3_22_scale x N
    |∑ n ∈ Finset.range N,
        ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)|
      ≤ (8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N := by
  let h : ℝ := helperForProposition_3_22_scale x N
  have hpos : 0 < h := by simpa [h] using helperForProposition_3_22_scale_pos x N
  have hsum_bound :
      (∑ n ∈ Finset.range N,
        |((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)|)
        ≤
        (∑ n ∈ Finset.range N, Real.pi * (8 : ℝ) ^ (n + 1)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact helperForProposition_3_22_termDifferenceQuotientBound n x h hpos
  have hgeom :
      (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1)) ≤ (8 / 7 : ℝ) * (8 : ℝ) ^ N :=
    helperForProposition_3_22_geometricBound N
  have hpi_nonneg : 0 ≤ Real.pi := by positivity
  calc
    |∑ n ∈ Finset.range N,
        ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)|
        ≤
        ∑ n ∈ Finset.range N,
          |((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ n ∈ Finset.range N, Real.pi * (8 : ℝ) ^ (n + 1)) := hsum_bound
    _ = Real.pi * (∑ n ∈ Finset.range N, (8 : ℝ) ^ (n + 1)) := by
          simp [Finset.mul_sum]
    _ ≤ Real.pi * ((8 / 7 : ℝ) * (8 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left hgeom hpi_nonneg
    _ = (8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N := by ring

/-- Helper for Proposition 3.22: the chosen-scale difference quotients have exponential
lower bound. -/
lemma helperForProposition_3_22_differenceQuotientLowerBoundAtChosenScale (x : ℝ) :
    ∀ N : ℕ,
      (8 : ℝ) ^ N ≤
        |(weierstrassFunction (x + helperForProposition_3_22_scale x N) -
            weierstrassFunction x) /
          helperForProposition_3_22_scale x N| := by
  intro N
  let h : ℝ := helperForProposition_3_22_scale x N
  let dominant : ℝ :=
    ((helperForProposition_3_22_term N (x + h) - helperForProposition_3_22_term N x) / h)
  let remainder : ℝ :=
    ∑ n ∈ Finset.range N,
      ((helperForProposition_3_22_term n (x + h) - helperForProposition_3_22_term n x) / h)
  let dq : ℝ :=
    (weierstrassFunction (x + h) - weierstrassFunction x) / h
  have hsplit : dq = dominant + remainder := by
    simpa [h, dominant, remainder, dq] using
      helperForProposition_3_22_differenceQuotientSplitAtScale x N
  have hdominant : ((16 / 3 : ℝ) * (8 : ℝ) ^ N) ≤ |dominant| := by
    simpa [h, dominant] using helperForProposition_3_22_dominantTermLowerBoundAtScale x N
  have hrem : |remainder| ≤ (8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N := by
    simpa [h, remainder] using helperForProposition_3_22_remainderBoundAtScale x N
  have hreverse : |dominant| - |remainder| ≤ |dq| := by
    have hdom_le : |dominant| ≤ |dq| + |remainder| := by
      have hdom_eq : dominant = dq - remainder := by linarith [hsplit]
      calc
        |dominant| = |dq - remainder| := by rw [hdom_eq]
        _ ≤ |dq| + |remainder| := abs_sub dq remainder
    linarith
  have hdom_minus_bound :
      ((16 / 3 : ℝ) * (8 : ℝ) ^ N) - ((8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N) ≤ |dq| := by
    linarith [hdominant, hrem, hreverse]
  have hconst : (1 : ℝ) ≤ (16 / 3 : ℝ) - (8 * Real.pi / 7 : ℝ) := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith
  have hpow_nonneg : 0 ≤ (8 : ℝ) ^ N := by positivity
  have hscaled :
      (8 : ℝ) ^ N ≤
        ((16 / 3 : ℝ) * (8 : ℝ) ^ N) - ((8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N) := by
    have hm :
        (1 : ℝ) * (8 : ℝ) ^ N ≤ ((16 / 3 : ℝ) - (8 * Real.pi / 7 : ℝ)) * (8 : ℝ) ^ N :=
      mul_le_mul_of_nonneg_right hconst hpow_nonneg
    have hm' :
        (8 : ℝ) ^ N ≤ ((16 / 3 : ℝ) - (8 * Real.pi / 7 : ℝ)) * (8 : ℝ) ^ N := by
      simpa using hm
    calc
      (8 : ℝ) ^ N ≤ ((16 / 3 : ℝ) - (8 * Real.pi / 7 : ℝ)) * (8 : ℝ) ^ N := hm'
      _ = ((16 / 3 : ℝ) * (8 : ℝ) ^ N) - ((8 * Real.pi / 7 : ℝ) * (8 : ℝ) ^ N) := by ring
  have htarget : (8 : ℝ) ^ N ≤ |dq| := le_trans hscaled hdom_minus_bound
  simpa [dq, h] using htarget

/-- Helper for Proposition 3.22: chosen-scale difference quotients do not converge
to any finite limit. -/
lemma helperForProposition_3_22_notTendstoAlongChosenScales (x L : ℝ) :
    ¬ Filter.Tendsto
      (fun N : ℕ =>
        (weierstrassFunction (x + helperForProposition_3_22_scale x N) -
            weierstrassFunction x) /
          helperForProposition_3_22_scale x N)
      Filter.atTop (nhds L) := by
  exact helperForProposition_3_22_notTendsto_of_absLowerBound
    (q :=
      fun N : ℕ =>
        (weierstrassFunction (x + helperForProposition_3_22_scale x N) -
            weierstrassFunction x) /
          helperForProposition_3_22_scale x N)
    (helperForProposition_3_22_differenceQuotientLowerBoundAtChosenScale x)
    L

/-- Helper for Proposition 3.22: differentiability at `x` implies convergence of chosen-scale
difference quotients to some finite real limit. -/
lemma helperForProposition_3_22_differentiableAt_imp_tendstoAlongChosenScales
    (x : ℝ) (hx : DifferentiableAt ℝ weierstrassFunction x) :
    ∃ L : ℝ,
      Filter.Tendsto
        (fun N : ℕ =>
          (weierstrassFunction (x + helperForProposition_3_22_scale x N) -
              weierstrassFunction x) /
            helperForProposition_3_22_scale x N)
        Filter.atTop (nhds L) := by
  refine ⟨deriv weierstrassFunction x, ?_⟩
  have hslope :
      Filter.Tendsto
        (fun h : ℝ => h⁻¹ • (weierstrassFunction (x + h) - weierstrassFunction x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv weierstrassFunction x)) :=
    hx.hasDerivAt.tendsto_slope_zero_right
  have hslope' :
      Filter.Tendsto
        (fun h : ℝ => (weierstrassFunction (x + h) - weierstrassFunction x) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv weierstrassFunction x)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hslope
  exact hslope'.comp (helperForProposition_3_22_scale_tendsto_nhdsWithin_zero x)

/-- Proposition 3.22: the Weierstrass function `f` of Definition 3.11 is nowhere
differentiable on `ℝ`, i.e., for every `x ∈ ℝ` the limit
`lim_{h→0} (f(x+h)-f(x))/h` does not exist. -/
theorem proposition_3_22 :
    ∀ x : ℝ, ¬ DifferentiableAt ℝ weierstrassFunction x :=
  by
    intro x hx
    rcases helperForProposition_3_22_differentiableAt_imp_tendstoAlongChosenScales x hx with
      ⟨L, hL⟩
    exact helperForProposition_3_22_notTendstoAlongChosenScales x L hL

end Section07
end Chap03
