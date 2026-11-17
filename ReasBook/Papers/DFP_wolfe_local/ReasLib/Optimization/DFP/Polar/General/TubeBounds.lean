module

public import ReasLib.Optimization.DFP.Polar.General.Scale
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.General.TubeBounds

/-- Helper for lem:polar-continuation: the slow barrier exponent lies strictly
between zero and one for every prescribed Hessian exponent. -/
theorem slowExponent_mem_Ioo {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    slowExponent β ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact slowExponent_pos hβ hβone
  · have hrate : 2 / (1 + β) < (2 : ℝ) := by
      apply (div_lt_iff₀ (add_pos zero_lt_one hβ)).mpr
      linarith
    linarith [restoringRate_sub_slowExponent hβ]

/-- Helper for lem:polar-continuation: Bernoulli's lower estimate for the negative
slow exponent follows from concavity of the corresponding positive power. -/
theorem negativeRpow_one_add_lower {d n : ℝ} (hd : 0 ≤ d) (hdone : d ≤ 1)
    (hn : 0 < n) (hdn : d ≤ n) :
    1 - d / n ≤ (1 + n⁻¹) ^ (-d) := by
  have hbase : 0 < 1 + n⁻¹ := by
    positivity
  have hleft : 0 ≤ 1 - d / n := by
    exact sub_nonneg.mpr ((div_le_one hn).mpr hdn)
  have hinv : -1 ≤ n⁻¹ := by
    have hnonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hn.le
    linarith
  have hconcave := rpow_one_add_le_one_add_mul_self hinv hd hdone
  have hproduct := mul_le_mul_of_nonneg_left hconcave hleft
  rw [Real.rpow_neg hbase.le, inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hbase d)).mpr
  simp only [div_eq_mul_inv] at hproduct ⊢
  nlinarith [sq_nonneg (d * n⁻¹)]

/-- Helper for lem:polar-continuation: one unit of index growth reduces a negative
power by at most its first-order tangent decrement. -/
theorem negativeRpow_succ_lower {d n : ℝ} (hd : 0 ≤ d) (hdone : d ≤ 1)
    (hn : 0 < n) (hdn : d ≤ n) :
    n ^ (-d) * (1 - d / n) ≤ (n + 1) ^ (-d) := by
  have hnext : n + 1 = n * (1 + n⁻¹) := by
    rw [mul_add, mul_one, mul_inv_cancel₀ hn.ne']
  have hbase : 0 ≤ 1 + n⁻¹ := by
    positivity
  rw [hnext, Real.mul_rpow hn.le hbase]
  exact mul_le_mul_of_nonneg_left (negativeRpow_one_add_lower hd hdone hn hdn)
    (Real.rpow_nonneg hn.le (-d))

/-- Helper for lem:polar-continuation: the source slow radius loses no more than
`d/n` of its current value at a successor cycle. -/
theorem slowRadius_succ_lower {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scale β j0 j ^ (1 - β) *
        (1 - slowExponent β / ((j0 + j : ℕ) : ℝ)) ≤
      scale β j0 (j + 1) ^ (1 - β) := by
  have hd := slowExponent_mem_Ioo hβ hβone
  have hn : (0 : ℝ) < ((j0 + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  have hnOne : (1 : ℝ) ≤ ((j0 + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  have hdn : slowExponent β ≤ ((j0 + j : ℕ) : ℝ) := hd.2.le.trans hnOne
  have hbound := negativeRpow_succ_lower hd.1.le hd.2.le hn hdn
  simpa only [scale_rpow_one_sub, Nat.cast_add, Nat.cast_one, add_assoc] using hbound

/-- Helper for lem:polar-continuation: a fixed fast width absorbs the two source
forcing terms and quadratic error once the index exceeds one explicit threshold. -/
theorem fastBarrier {q C N n u uNext s : ℝ}
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hN : 0 ≤ N) (hn : 0 < n)
    (hu : 0 ≤ u) (huN : u ≤ N / n) (hs : s ≤ 1 / n)
    (hmargin : C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * n)
    (hupdate : uNext ≤ q * u + C * (1 / n + s) + C * u ^ 2) :
    uNext ≤ N / (n + 1) := by
  have hquadratic : u ^ 2 ≤ (N / n) ^ 2 := pow_le_pow_left₀ hu huN 2
  have hlinear := mul_le_mul_of_nonneg_left huN hq
  have hsquare := mul_le_mul_of_nonneg_left hquadratic hC
  have hforcing := mul_le_mul_of_nonneg_left (add_le_add_left hs (1 / n)) hC
  have hbound : uNext ≤ q * (N / n) + C * (1 / n + 1 / n) + C * (N / n) ^ 2 := by
    linarith
  have hnormal : q * (N / n) + C * (1 / n + 1 / n) + C * (N / n) ^ 2 =
      (q * N * n + 2 * C * n + C * N ^ 2) / n ^ 2 := by
    field_simp [hn.ne']
    ring
  have hnumerator : q * N * n + 2 * C * n + C * N ^ 2 ≤ N * n - N := by
    nlinarith
  have hnext : 0 < n + 1 := by
    positivity
  calc
    uNext ≤ (q * N * n + 2 * C * n + C * N ^ 2) / n ^ 2 := by
      rwa [hnormal] at hbound
    _ ≤ (N * n - N) / n ^ 2 :=
      div_le_div_of_nonneg_right hnumerator (sq_nonneg n)
    _ ≤ N / (n + 1) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hn) hnext).mpr
      nlinarith

/-- Helper for lem:polar-continuation: a restoring rate exceeding the barrier
exponent by one absorbs a slow forcing coefficient below the chosen width. -/
theorem slowBarrier {a d M K n r rNext b bNext : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hn : 0 < n) (ha : a ≤ n)
    (hgap : a - d = 1) (hKM : K ≤ M) (hb : |b| ≤ M * r)
    (hrNext : r * (1 - d / n) ≤ rNext)
    (herror : |bNext - (1 - a / n) * b| ≤ K / n * r) :
    |bNext| ≤ M * rNext := by
  have hcoefficient : 0 ≤ 1 - a / n :=
    sub_nonneg.mpr ((div_le_one hn).mpr ha)
  have htriangle : |bNext| ≤ |bNext - (1 - a / n) * b| + |(1 - a / n) * b| := by
    simpa only [sub_add_cancel] using
      abs_add_le (bNext - (1 - a / n) * b) ((1 - a / n) * b)
  have hcontract : |(1 - a / n) * b| = (1 - a / n) * |b| := by
    rw [abs_mul, abs_of_nonneg hcoefficient]
  have hslow := mul_le_mul_of_nonneg_left hb hcoefficient
  have hforcingBound : K / n * r ≤ M / n * r := by
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hKM hn.le) hr
  have hidentity : M / n * r + (1 - a / n) * (M * r) =
      M * (r * (1 - d / n)) := by
    have haeq : a = d + 1 := by
      linarith
    rw [haeq]
    ring
  have hpre : |bNext| ≤ M * (r * (1 - d / n)) := by
    rw [← hidentity]
    linarith [htriangle, herror, hcontract]
  exact hpre.trans (mul_le_mul_of_nonneg_left hrNext hM)

/-- Helper for lem:polar-continuation: fix the fast width with the source's strict
margin before choosing any slow width or starting index. -/
theorem existsFastWidth {q C : ℝ} (hq : q < 1) (hC : 0 ≤ C) :
    ∃ N > 0, 4 * C / (1 - q) < N ∧ 0 < (1 - q) * N - 2 * C := by
  let N := (4 * C + 1) / (1 - q)
  have hden : 0 < 1 - q := sub_pos.mpr hq
  have hnum : 0 < 4 * C + 1 := by
    linarith
  have hN : 0 < N := div_pos hnum hden
  have hidentity : (1 - q) * N = 4 * C + 1 := by
    dsimp only [N]
    field_simp [hden.ne']
  refine ⟨N, hN, ?_, ?_⟩
  · apply (div_lt_iff₀ hden).mpr
    nlinarith
  · linarith

/-- Helper for lem:polar-continuation: after fixing the fast width, the slow width
can exceed the associated forcing coefficient with a strict positive margin. -/
theorem existsSlowWidth (K : ℝ) : ∃ M > 0, K < M := by
  refine ⟨max K 0 + 1, ?_, ?_⟩
  · linarith [le_max_right K 0]
  · linarith [le_max_left K 0]

/-- Helper for lem:polar-continuation: after the fast and slow widths are fixed,
one index threshold absorbs the fast quadratic error and puts both barriers in
their prescribed neighborhoods. -/
theorem existsStartingIndex {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (C N M q r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (hmargin : 0 < (1 - q) * N - 2 * C) :
    ∃ J : ℕ, 0 < J ∧ ∀ n : ℕ, J ≤ n →
      2 / (1 + β) ≤ (n : ℝ) ∧
      C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * (n : ℝ) ∧
      N / (n : ℝ) ≤ ρ ∧ M * (n : ℝ) ^ (-slowExponent β) ≤ r := by
  have hfastRadius : Tendsto (fun n : ℕ ↦ N / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hd := (slowExponent_mem_Ioo hβ hβone).1
  have hslowRadius : Tendsto
      (fun n : ℕ ↦ M * (n : ℝ) ^ (-slowExponent β)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop).const_mul M
  have hrate : ∀ᶠ n : ℕ in atTop, 2 / (1 + β) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hfastMargin : ∀ᶠ n : ℕ in atTop,
      (C * N ^ 2 + N) / ((1 - q) * N - 2 * C) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have heventually : ∀ᶠ n : ℕ in atTop,
      2 / (1 + β) ≤ (n : ℝ) ∧
      C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * (n : ℝ) ∧
      N / (n : ℝ) ≤ ρ ∧ M * (n : ℝ) ^ (-slowExponent β) ≤ r := by
    filter_upwards [hrate, hfastMargin, hfastRadius.eventually (Iio_mem_nhds hρ),
      hslowRadius.eventually (Iio_mem_nhds hr)] with n hn hmarginN hfast hslow
    refine ⟨hn, ?_, hfast.le, hslow.le⟩
    nlinarith [(div_le_iff₀ hmargin).mp hmarginN]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp heventually
  refine ⟨max J 1, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right J 1)
  · intro n hn
    exact hJ n ((le_max_left J 1).trans hn)

/-- Helper for lem:polar-continuation: the general source fast and slow update
estimates preserve both barriers at one cycle of every sufficiently large start. -/
theorem tubeBarrier {β q C N M K : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hN : 0 ≤ N) (hM : 0 ≤ M) (hKM : K ≤ M)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ)
    (ha : 2 / (1 + β) ≤ ((j0 + j : ℕ) : ℝ))
    (hmargin : C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * ((j0 + j : ℕ) : ℝ))
    {u uNext b bNext : ℝ} (hu : 0 ≤ u) (huN : u ≤ N / ((j0 + j : ℕ) : ℝ))
    (hb : |b| ≤ M * scale β j0 j ^ (1 - β))
    (hfast : uNext ≤ q * u + C * (1 / ((j0 + j : ℕ) : ℝ) +
      scale β j0 j ^ 2) + C * u ^ 2)
    (hslow : |bNext - (1 - (2 / (1 + β)) / ((j0 + j : ℕ) : ℝ)) * b| ≤
      K * scale β j0 j ^ 2) :
    uNext ≤ N / ((j0 + (j + 1) : ℕ) : ℝ) ∧
      |bNext| ≤ M * scale β j0 (j + 1) ^ (1 - β) := by
  have hn : (0 : ℝ) < ((j0 + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  constructor
  · have hscale : scale β j0 j ^ 2 ≤ 1 / ((j0 + j : ℕ) : ℝ) := by
      simpa only [one_div] using scale_sq_le_inv hβ hβone hstart j
    have hbound := fastBarrier hq hC hN hn hu huN hscale hmargin hfast
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hbound
  · have hslowError :
        |bNext - (1 - (2 / (1 + β)) / ((j0 + j : ℕ) : ℝ)) * b| ≤
          K / ((j0 + j : ℕ) : ℝ) * scale β j0 j ^ (1 - β) := by
      rw [← inv_mul_scale_rpow_one_sub hβ hstart j] at hslow
      simpa only [div_eq_mul_inv, mul_assoc] using hslow
    exact slowBarrier hM (Real.rpow_nonneg (scale_nonneg β j0 j) _) hn ha
      (restoringRate_sub_slowExponent hβ) hKM hb
      (slowRadius_succ_lower hβ hβone hstart j) hslowError

/-- Helper for lem:polar-continuation: explicit source update estimates and the
initial tube bounds imply all subsequent tube bounds by induction. -/
theorem tubeBounds_of_updateEstimates {β q C N M K : ℝ}
    (hβ : 0 < β) (hβone : β < 1) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hKM : K ≤ M)
    {j0 : ℕ} (hstart : 0 < j0)
    (hindices : ∀ j : ℕ,
      2 / (1 + β) ≤ ((j0 + j : ℕ) : ℝ) ∧
      C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * ((j0 + j : ℕ) : ℝ))
    (u b : ℕ → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hu0 : u 0 ≤ N / ((j0 + 0 : ℕ) : ℝ))
    (hb0 : |b 0| ≤ M * scale β j0 0 ^ (1 - β))
    (hfast : ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
      |b j| ≤ M * scale β j0 j ^ (1 - β) →
      u (j + 1) ≤ q * u j + C * (1 / ((j0 + j : ℕ) : ℝ) +
        scale β j0 j ^ 2) + C * u j ^ 2)
    (hslow : ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
      |b j| ≤ M * scale β j0 j ^ (1 - β) →
      |b (j + 1) - (1 - (2 / (1 + β)) / ((j0 + j : ℕ) : ℝ)) * b j| ≤
        K * scale β j0 j ^ 2) :
    ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) ∧
      |b j| ≤ M * scale β j0 j ^ (1 - β) := by
  intro j
  induction j with
  | zero => exact ⟨hu0, hb0⟩
  | succ j hj =>
    exact tubeBarrier hβ hβone hq hC hN hM hKM hstart j
      (hindices j).1 (hindices j).2 (hu j) hj.1 hj.2
      (hfast j hj.1 hj.2) (hslow j hj.1 hj.2)

/-- Helper for lem:polar-continuation: (general source barriers). Choose the fast width `N`,
then the slow width `M`, and finally a common starting index `J`. For every
`j0 ≥ J`, every sequence satisfying the source update estimates and the initial
tube bounds remains in both barriers at every cycle, inside the fixed compact
neighborhoods. The slow forcing coefficient may depend on `N` throughout. -/
theorem existsInvariantTubeConstants {β q C : ℝ}
    (hβ : 0 < β) (hβone : β < 1) (hq : 0 ≤ q) (hqone : q < 1) (hC : 0 ≤ C)
    (slowError : ℝ → ℝ) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    ∃ N > 0, 4 * C / (1 - q) < N ∧
      ∃ M > 0, slowError N < M ∧
        ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
          (∀ j : ℕ, N / ((j0 + j : ℕ) : ℝ) ≤ ρ ∧
            M * scale β j0 j ^ (1 - β) ≤ r) ∧
          ∀ u b : ℕ → ℝ, (∀ j, 0 ≤ u j) →
            u 0 ≤ N / ((j0 + 0 : ℕ) : ℝ) →
            |b 0| ≤ M * scale β j0 0 ^ (1 - β) →
            (∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
              |b j| ≤ M * scale β j0 j ^ (1 - β) →
              u (j + 1) ≤ q * u j + C * (1 / ((j0 + j : ℕ) : ℝ) +
                scale β j0 j ^ 2) + C * u j ^ 2) →
            (∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
              |b j| ≤ M * scale β j0 j ^ (1 - β) →
              |b (j + 1) - (1 - (2 / (1 + β)) / ((j0 + j : ℕ) : ℝ)) * b j| ≤
                slowError N * scale β j0 j ^ 2) →
            ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) ∧
              |b j| ≤ M * scale β j0 j ^ (1 - β) := by
  obtain ⟨N, hN, hNchoice, hmargin⟩ := existsFastWidth hqone hC
  obtain ⟨M, hM, hMchoice⟩ := existsSlowWidth (slowError N)
  obtain ⟨J, hJ, hthreshold⟩ :=
    existsStartingIndex hβ hβone C N M q r ρ hr hρ hmargin
  refine ⟨N, hN, hNchoice, M, hM, hMchoice, J, hJ, ?_⟩
  intro j0 hj0
  have hstart : 0 < j0 := hJ.trans_le hj0
  have hindices : ∀ j : ℕ,
      2 / (1 + β) ≤ ((j0 + j : ℕ) : ℝ) ∧
      C * N ^ 2 + N ≤ ((1 - q) * N - 2 * C) * ((j0 + j : ℕ) : ℝ) := by
    intro j
    have hbound := hthreshold (j0 + j) (hj0.trans (Nat.le_add_right j0 j))
    exact ⟨hbound.1, hbound.2.1⟩
  constructor
  · intro j
    have hbound := hthreshold (j0 + j) (hj0.trans (Nat.le_add_right j0 j))
    constructor
    · exact hbound.2.2.1
    · simpa only [scale_rpow_one_sub] using hbound.2.2.2
  · intro u b hu hu0 hb0 hfast hslow
    exact tubeBounds_of_updateEstimates hβ hβone hq hC hN.le hM.le hMchoice.le
      hstart hindices u b hu hu0 hb0 hfast hslow

end DFP.Polar.General.TubeBounds
