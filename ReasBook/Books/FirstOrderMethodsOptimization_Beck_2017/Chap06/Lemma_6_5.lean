/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Lemma 6.5 is `source-facing`: the core/canonical owner is the set-valued proximal mapping
`prox[...]` from Definition 6.1. Domain sampling shows that the relevant scalar ingredients
already owned upstream are Chapter 2's `extendedIndicator`, Chapter 4's `negative_log_barrier`,
and Chapter 6's soft-thresholding operator `𝒯[λ]`. Accordingly, this file keeps only the
genuinely source-facing scalar penalties as local owners, defines the positive-ray ones through
the Chapter 2 indicator owner, and states the interval-indicator and log-barrier items directly
on those existing owners instead of introducing parallel wrappers. -/

/-- The scalar penalty `x ↦ μ x` on the nonnegative ray and `∞` on the negative ray. -/
def nonnegative_linear_penalty (mu : ℝ) : ℝ → EReal :=
  extendedIndicator (Set.Ici (0 : ℝ)) + Real.toEReal ∘ fun x ↦ mu * x

/-- Evaluating the nonnegative linear penalty gives its piecewise finite/`∞` formula. -/
@[simp] theorem nonnegative_linear_penalty_apply (mu x : ℝ) :
    nonnegative_linear_penalty mu x =
      if 0 ≤ x then ((mu * x : ℝ) : EReal) else ⊤ := by
  by_cases hx : 0 ≤ x
  · simp [nonnegative_linear_penalty, extendedIndicator, hx]
  · calc
      nonnegative_linear_penalty mu x = ⊤ + (((mu * x : ℝ) : EReal)) := by
        have hx' : x ∈ Set.Iio (0 : ℝ) := by simpa using hx
        simp [nonnegative_linear_penalty, extendedIndicator, hx', EReal.coe_mul]
      _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      _ = if 0 ≤ x then ((mu * x : ℝ) : EReal) else ⊤ := by simp [hx]

/-- The nonnegative linear penalty is proper: it never equals `-∞` and it is finite at `0`. -/
theorem isProper_nonnegative_linear_penalty (mu : ℝ) :
    IsProperExtendedRealFunction (nonnegative_linear_penalty mu) := by
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hx : 0 ≤ x
    · rw [nonnegative_linear_penalty_apply, if_pos hx, EReal.coe_mul]
      exact EReal.coe_ne_bot _
    · simp [nonnegative_linear_penalty_apply, hx]
  · refine ⟨0, ?_⟩
    rw [mem_effective_domain]
    simp [nonnegative_linear_penalty_apply]

/-- The scalar penalty `x ↦ λ |x|`. -/
def absolute_value_penalty (lam : ℝ) : ℝ → EReal :=
  Real.toEReal ∘ fun x ↦ lam * |x|

/-- Evaluating the absolute-value penalty gives the scalar value `λ |x|`. -/
@[simp] theorem absolute_value_penalty_apply (lam x : ℝ) :
    absolute_value_penalty lam x = ((lam * |x| : ℝ) : EReal) :=
  rfl

/-- The scalar penalty `x ↦ λ x^3` on the nonnegative ray and `∞` on the negative ray. -/
def nonnegative_cubic_penalty (lam : ℝ) : ℝ → EReal :=
  extendedIndicator (Set.Ici (0 : ℝ)) + Real.toEReal ∘ fun x ↦ lam * x ^ 3

/-- Evaluating the nonnegative cubic penalty gives its piecewise finite/`∞` formula. -/
@[simp] theorem nonnegative_cubic_penalty_apply (lam x : ℝ) :
    nonnegative_cubic_penalty lam x =
      if 0 ≤ x then ((lam * x ^ 3 : ℝ) : EReal) else ⊤ := by
  by_cases hx : 0 ≤ x
  · simp [nonnegative_cubic_penalty, extendedIndicator, hx]
  · calc
      nonnegative_cubic_penalty lam x = ⊤ + (((lam * x ^ 3 : ℝ) : EReal)) := by
        have hx' : x ∈ Set.Iio (0 : ℝ) := by simpa using hx
        simp [nonnegative_cubic_penalty, extendedIndicator, hx', EReal.coe_mul, EReal.coe_pow]
      _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      _ = if 0 ≤ x then ((lam * x ^ 3 : ℝ) : EReal) else ⊤ := by simp [hx]

/-- The nonnegative cubic penalty is proper: it never equals `-∞` and it is finite at `0`. -/
theorem isProper_nonnegative_cubic_penalty (lam : ℝ) :
    IsProperExtendedRealFunction (nonnegative_cubic_penalty lam) := by
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hx : 0 ≤ x
    · rw [nonnegative_cubic_penalty_apply, if_pos hx, EReal.coe_mul, EReal.coe_pow]
      exact EReal.coe_ne_bot _
    · simp [nonnegative_cubic_penalty_apply, hx]
  · refine ⟨0, ?_⟩
    rw [mem_effective_domain]
    simp [nonnegative_cubic_penalty_apply]

/-- Helper for Lemma 6.5: the positive cubic prox candidate satisfies the first-order quadratic
equation `3 λ r² + r - x = 0`. -/
theorem nonnegative_cubic_candidate_root_eq
    (lam x : ℝ) (hlam : 0 < lam) (hx : 0 < x) :
    3 * lam * (((-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam)) ^ 2) +
        ((-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam)) - x = 0 := by
  -- Solve the displayed quadratic by first isolating the square root and then squaring.
  have hlin :
      6 * lam * (((-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam))) + 1 =
        Real.sqrt (1 + 12 * lam * x) := by
    have hden : (6 : ℝ) * lam ≠ 0 := by
      nlinarith
    field_simp [hden]
    ring_nf
  have hsq :
      (6 * lam * (((-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam))) + 1) ^ 2 =
        1 + 12 * lam * x := by
    rw [hlin]
    exact Real.sq_sqrt (by nlinarith [hlam, hx])
  nlinarith [hsq]

/-- Helper for Lemma 6.5: once `r` solves `3 λ r² + r - x = 0`, the cubic proximal objective gap
factors into a square times a nonnegative coefficient. -/
theorem nonnegative_cubic_objective_gap
    (lam x r u : ℝ) (hroot : 3 * lam * r ^ 2 + r - x = 0) :
    lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 -
        (lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2) =
      (u - r) ^ 2 * (lam * (u + 2 * r) + 1 / 2) := by
  -- Substitute the root equation to expose the square factor `(u - r)^2`.
  have hx : x = 3 * lam * r ^ 2 + r := by
    linarith
  rw [hx]
  ring

/-- Helper for Lemma 6.5: the log-barrier prox candidate is strictly positive. -/
theorem scalar_log_barrier_candidate_pos
    (lam x : ℝ) (hlam : 0 < lam) :
    0 < (x + Real.sqrt (x ^ 2 + 4 * lam)) / 2 := by
  -- The square-root term strictly dominates `-x`, so the numerator is positive.
  have hsqrt : -x < Real.sqrt (x ^ 2 + 4 * lam) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [hlam]
  have hnum : 0 < x + Real.sqrt (x ^ 2 + 4 * lam) := by
    nlinarith
  exact div_pos hnum (by norm_num)

/-- Helper for Lemma 6.5: the log-barrier prox candidate satisfies `r² - x r - λ = 0`. -/
theorem scalar_log_barrier_candidate_root_eq
    (lam x : ℝ) (hlam : 0 < lam) :
    ((x + Real.sqrt (x ^ 2 + 4 * lam)) / 2) ^ 2 -
        x * ((x + Real.sqrt (x ^ 2 + 4 * lam)) / 2) - lam = 0 := by
  -- Squaring the defining quadratic-root expression gives the claimed identity.
  have hsq : (Real.sqrt (x ^ 2 + 4 * lam)) ^ 2 = x ^ 2 + 4 * lam := by
    apply Real.sq_sqrt
    nlinarith [hlam]
  field_simp
  nlinarith [hsq]

/-- Helper for Lemma 6.5: if `r² - x r - λ = 0`, then the log-barrier proximal objective gap is
the sum of the standard `t - 1 - log t` term and a square term. -/
theorem scalar_log_barrier_objective_gap
    (lam x r u : ℝ) (hroot : r ^ 2 - x * r - lam = 0) (hu : 0 < u) (hr : 0 < r) :
    -lam * Real.log u + (1 / 2 : ℝ) * (u - x) ^ 2 -
        (-lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2) =
      lam * ((u / r) - 1 - Real.log (u / r)) + (1 / 2 : ℝ) * (u - r) ^ 2 := by
  -- Rewrite the logarithm through `log (u / r)` and then use the root identity to cancel the
  -- linear terms.
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hlog : Real.log (u / r) = Real.log u - Real.log r := by
    rw [Real.log_div hu.ne' hr_ne]
  have hlam : lam = r ^ 2 - x * r := by
    linarith
  rw [hlog, hlam]
  field_simp [hr_ne]
  ring

-- Proof sketch: minimize `u ↦ μ u + (1 / 2) (u - x)^2` over the feasible ray `u ≥ 0`. The
-- unconstrained minimizer is `x - μ`, and projecting it onto `[0, ∞)` yields `(x - μ)⁺`.
/-- Lemma 6.5 (1): for the penalty `g₁(x) = μ x` on `[0, ∞)` and `∞` on `(-∞, 0)`, the proximal
mapping is the singleton `{(x - μ)⁺}`. -/
theorem prox_nonnegative_linear_penalty_eq_singleton_posPart_sub (mu x : ℝ) :
    prox[nonnegative_linear_penalty mu] x = {(x - mu)⁺} := by
  let c := (x - mu)⁺
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using posPart_nonneg (x - mu)
  have hc_value :
      proximal_objective (nonnegative_linear_penalty mu) x c =
        (((mu * c + (1 / 2 : ℝ) * (c - x) ^ 2 : ℝ)) : EReal) := by
    -- The candidate lies on the feasible ray, so the proximal objective is finite there.
    simp [proximal_objective_apply, nonnegative_linear_penalty_apply, hc_nonneg]
  have hc_mem : c ∈ prox[nonnegative_linear_penalty mu] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro u
    by_cases hu : 0 ≤ u
    · have hu_value :
          proximal_objective (nonnegative_linear_penalty mu) x u =
            (((mu * u + (1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
        simp [proximal_objective_apply, nonnegative_linear_penalty_apply, hu]
      by_cases hx : mu ≤ x
      · have hc_eq : c = x - mu := by
          simp [c, hx]
        -- On the interior branch, complete the square around the unconstrained minimizer `x - μ`.
        have hmain :
            mu * c + (1 / 2 : ℝ) * (c - x) ^ 2 ≤
              mu * u + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          rw [hc_eq]
          nlinarith [sq_nonneg (u - (x - mu))]
        rw [hc_value, hu_value]
        exact_mod_cast hmain
      · have hx' : x < mu := lt_of_not_ge hx
        have hc_eq : c = 0 := by
          simp [c, le_of_lt hx']
        -- When `x < μ`, the boundary point `0` is optimal on the feasible ray.
        have hmain :
            mu * c + (1 / 2 : ℝ) * (c - x) ^ 2 ≤
              mu * u + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          rw [hc_eq]
          nlinarith [sq_nonneg u]
        rw [hc_value, hu_value]
        exact_mod_cast hmain
    · have htop : proximal_objective (nonnegative_linear_penalty mu) x u = ⊤ := by
        -- Outside the feasible ray, the indicator part forces the objective to `⊤`.
        calc
          proximal_objective (nonnegative_linear_penalty mu) x u
              = ⊤ + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                  simp [proximal_objective_apply, nonnegative_linear_penalty_apply, hu]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop]
      simp
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · exact hc_mem
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hc_mem
    have hy_le :
        proximal_objective (nonnegative_linear_penalty mu) x y ≤
          proximal_objective (nonnegative_linear_penalty mu) x c := hy c
    have hc_le :
        proximal_objective (nonnegative_linear_penalty mu) x c ≤
          proximal_objective (nonnegative_linear_penalty mu) x y := hc_mem y
    have hc_finite : proximal_objective (nonnegative_linear_penalty mu) x c < ⊤ := by
      rw [hc_value]
      exact EReal.coe_lt_top _
    have hy_nonneg : 0 ≤ y := by
      by_contra hy_neg
      have htop : proximal_objective (nonnegative_linear_penalty mu) x y = ⊤ := by
        calc
          proximal_objective (nonnegative_linear_penalty mu) x y
              = ⊤ + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                  simp [proximal_objective_apply, nonnegative_linear_penalty_apply, hy_neg]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop] at hy_le
      exact (not_le_of_gt hc_finite) hy_le
    have hy_value :
        proximal_objective (nonnegative_linear_penalty mu) x y =
          (((mu * y + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
      simp [proximal_objective_apply, nonnegative_linear_penalty_apply, hy_nonneg]
    by_cases hx : mu ≤ x
    · have hc_eq : c = x - mu := by
        simp [c, hx]
      -- Equality of the objective values forces the completed square to vanish.
      have hcy :
          (mu * y + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ) =
            mu * c + (1 / 2 : ℝ) * (c - x) ^ 2 := by
        rw [hy_value, hc_value] at hy_le hc_le
        exact_mod_cast le_antisymm hy_le hc_le
      rw [hc_eq] at hcy
      nlinarith [sq_nonneg (y - (x - mu))]
    · have hx' : x < mu := lt_of_not_ge hx
      have hc_eq : c = 0 := by
        simp [c, le_of_lt hx']
      -- On the boundary branch, equality can only happen at `0`.
      have hcy :
          (mu * y + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ) =
            mu * c + (1 / 2 : ℝ) * (c - x) ^ 2 := by
        rw [hy_value, hc_value] at hy_le hc_le
        exact_mod_cast le_antisymm hy_le hc_le
      rw [hc_eq] at hcy
      nlinarith [sq_nonneg y]

-- Proof sketch: split the scalar minimization of `u ↦ λ |u| + (1 / 2) (u - x)^2` into the three
-- regimes `x > λ`, `|x| ≤ λ`, and `x < -λ`, and identify the resulting minimizer with the
-- soft-thresholding operator `𝒯[λ]`.
/-- Helper for Lemma 6.5: on the branch `x > λ`, the absolute-value proximal objective gap at the
soft-threshold candidate `x - λ` splits into a square term plus the nonnegative defect
`λ (|u| - u)`. -/
theorem absolute_value_penalty_objective_gap_pos
    (lam x u : ℝ) (hx : lam < x) :
    lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
        (lam * |x - lam| + (1 / 2 : ℝ) * ((x - lam) - x) ^ 2) =
      (1 / 2 : ℝ) * (u - (x - lam)) ^ 2 + lam * (|u| - u) := by
  -- The positive branch makes the candidate `x - λ` nonnegative, so its absolute value unwraps.
  have hpos : 0 < x - lam := by
    linarith
  rw [abs_of_pos hpos]
  ring

/-- Helper for Lemma 6.5: on the middle branch `|x| ≤ λ`, the objective gap from the candidate
`0` is the sum of the quadratic term `(1/2) u²` and the linear remainder `λ |u| - x u`. -/
theorem absolute_value_penalty_objective_gap_mid (lam x u : ℝ) :
    lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
        (lam * |(0 : ℝ)| + (1 / 2 : ℝ) * ((0 : ℝ) - x) ^ 2) =
      (1 / 2 : ℝ) * u ^ 2 + lam * |u| - x * u := by
  -- Expanding the square at the origin gives the exact middle-branch objective gap.
  simp
  ring

/-- Helper for Lemma 6.5: on the branch `x < -λ`, the absolute-value proximal objective gap at the
soft-threshold candidate `x + λ` splits into a square term plus the nonnegative defect
`λ (|u| + u)`. -/
theorem absolute_value_penalty_objective_gap_neg
    (lam x u : ℝ) (hx : x < -lam) :
    lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
        (lam * |x + lam| + (1 / 2 : ℝ) * ((x + lam) - x) ^ 2) =
      (1 / 2 : ℝ) * (u - (x + lam)) ^ 2 + lam * (|u| + u) := by
  -- The negative branch makes the candidate `x + λ` nonpositive, so its absolute value unwraps.
  have hneg : x + lam < 0 := by
    linarith
  rw [abs_of_neg hneg]
  ring

/-- Lemma 6.5 (2): for the penalty `g₂(x) = λ |x|` with `0 ≤ λ`, the proximal mapping is the
singleton `{𝒯[λ] x}`, equivalently the usual soft-thresholding piecewise formula. -/
theorem prox_absolute_value_penalty_eq_singleton_soft_thresholding
    (lam : ℝ) (hlam : 0 ≤ lam) (x : ℝ) :
    prox[absolute_value_penalty lam] x = {𝒯[lam] x} := by
  let c := 𝒯[lam] x
  have hc_value :
      proximal_objective (absolute_value_penalty lam) x c =
        (((lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2 : ℝ)) : EReal) := by
    -- The absolute-value penalty is finite everywhere, so the proximal objective is a real value.
    simp [proximal_objective_apply, absolute_value_penalty_apply]
  have hc_mem : c ∈ prox[absolute_value_penalty lam] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro u
    have hu_value :
        proximal_objective (absolute_value_penalty lam) x u =
          (((lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
      simp [proximal_objective_apply, absolute_value_penalty_apply]
    by_cases hx_pos : lam < x
    · have hc_eq : c = x - lam := by
        -- On the positive branch, soft thresholding subtracts `λ`.
        rw [show c = 𝒯[lam] x by rfl, soft_thresholding_eq_piecewise hlam x]
        simp [le_of_lt hx_pos]
      have hextra_nonneg : 0 ≤ lam * (|u| - u) := by
        have habs_sub : 0 ≤ |u| - u := sub_nonneg.mpr (le_abs_self u)
        nlinarith
      have hsub :
          0 ≤ lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
              (lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2) := by
        rw [hc_eq]
        rw [absolute_value_penalty_objective_gap_pos lam x u hx_pos]
        nlinarith
      have hmain :
          lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2 ≤
            lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 := by
        linarith
      rw [hc_value, hu_value]
      exact_mod_cast hmain
    · by_cases hx_neg : x < -lam
      · have hc_eq : c = x + lam := by
          -- On the negative branch, soft thresholding adds `λ`.
          rw [show c = 𝒯[lam] x by rfl, soft_thresholding_eq_piecewise hlam x]
          have hnot_le : ¬ lam ≤ x := by
            linarith
          have habs_not_lt : ¬ |x| < lam := by
            have hge : lam ≤ |x| := by
              calc
                lam ≤ -x := by linarith
                _ = |x| := by rw [abs_of_neg (by linarith)]
            exact not_lt_of_ge hge
          simp [hnot_le, habs_not_lt]
        have hextra_nonneg : 0 ≤ lam * (|u| + u) := by
          have habs_add : 0 ≤ |u| + u := by
            nlinarith [neg_le_abs u]
          nlinarith
        have hsub :
            0 ≤ lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
                (lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2) := by
          rw [hc_eq]
          rw [absolute_value_penalty_objective_gap_neg lam x u hx_neg]
          nlinarith
        have hmain :
            lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2 ≤
              lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          linarith
        rw [hc_value, hu_value]
        exact_mod_cast hmain
      · have hmid : |x| ≤ lam := by
          rw [abs_le]
          constructor
          · linarith
          · linarith
        have hc_eq : c = 0 := by
          -- In the middle regime, the positive-part factor vanishes, so the threshold is zero.
          simp [c, posPart_of_nonpos (sub_nonpos.mpr hmid)]
        have hxy_le : x * u ≤ lam * |u| := by
          calc
            x * u ≤ |x * u| := le_abs_self (x * u)
            _ = |x| * |u| := by rw [abs_mul]
            _ ≤ lam * |u| := mul_le_mul_of_nonneg_right hmid (abs_nonneg u)
        have hterm_nonneg : 0 ≤ lam * |u| - x * u := by
          nlinarith
        have hsub :
            0 ≤ lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 -
                (lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2) := by
          rw [hc_eq]
          rw [absolute_value_penalty_objective_gap_mid lam x u]
          nlinarith [sq_nonneg u, hterm_nonneg]
        have hmain :
            lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2 ≤
              lam * |u| + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          linarith
        rw [hc_value, hu_value]
        exact_mod_cast hmain
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · exact hc_mem
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hc_mem
    have hy_le :
        proximal_objective (absolute_value_penalty lam) x y ≤
          proximal_objective (absolute_value_penalty lam) x c := hy c
    have hc_le :
        proximal_objective (absolute_value_penalty lam) x c ≤
          proximal_objective (absolute_value_penalty lam) x y := hc_mem y
    have hy_value :
        proximal_objective (absolute_value_penalty lam) x y =
          (((lam * |y| + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
      simp [proximal_objective_apply, absolute_value_penalty_apply]
    have hcy :
        (lam * |y| + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ) =
          lam * |c| + (1 / 2 : ℝ) * (c - x) ^ 2 := by
      rw [hy_value, hc_value] at hy_le hc_le
      exact_mod_cast le_antisymm hy_le hc_le
    by_cases hx_pos : lam < x
    · have hc_eq : c = x - lam := by
        -- The unique positive-branch minimizer is the shifted point `x - λ`.
        rw [show c = 𝒯[lam] x by rfl, soft_thresholding_eq_piecewise hlam x]
        simp [le_of_lt hx_pos]
      have hextra_nonneg : 0 ≤ lam * (|y| - y) := by
        have habs_sub : 0 ≤ |y| - y := sub_nonneg.mpr (le_abs_self y)
        nlinarith
      have hsum_zero :
          (1 / 2 : ℝ) * (y - (x - lam)) ^ 2 + lam * (|y| - y) = 0 := by
        rw [hc_eq] at hcy
        rw [← absolute_value_penalty_objective_gap_pos lam x y hx_pos, hcy]
        ring
      have hsqhalf : (1 / 2 : ℝ) * (y - (x - lam)) ^ 2 = 0 := by
        nlinarith [hsum_zero, hextra_nonneg]
      have hsquare : (y - (x - lam)) ^ 2 = 0 := by
        nlinarith [hsqhalf]
      have hy_eq : y = x - lam := by
        nlinarith [hsquare]
      exact hy_eq.trans hc_eq.symm
    · by_cases hx_neg : x < -lam
      · have hc_eq : c = x + lam := by
          -- The unique negative-branch minimizer is the shifted point `x + λ`.
          rw [show c = 𝒯[lam] x by rfl, soft_thresholding_eq_piecewise hlam x]
          have hnot_le : ¬ lam ≤ x := by
            linarith
          have habs_not_lt : ¬ |x| < lam := by
            have hge : lam ≤ |x| := by
              calc
                lam ≤ -x := by linarith
                _ = |x| := by rw [abs_of_neg (by linarith)]
            exact not_lt_of_ge hge
          simp [hnot_le, habs_not_lt]
        have hextra_nonneg : 0 ≤ lam * (|y| + y) := by
          have habs_add : 0 ≤ |y| + y := by
            nlinarith [neg_le_abs y]
          nlinarith
        have hsum_zero :
            (1 / 2 : ℝ) * (y - (x + lam)) ^ 2 + lam * (|y| + y) = 0 := by
          rw [hc_eq] at hcy
          rw [← absolute_value_penalty_objective_gap_neg lam x y hx_neg, hcy]
          ring
        have hsqhalf : (1 / 2 : ℝ) * (y - (x + lam)) ^ 2 = 0 := by
          nlinarith [hsum_zero, hextra_nonneg]
        have hsquare : (y - (x + lam)) ^ 2 = 0 := by
          nlinarith [hsqhalf]
        have hy_eq : y = x + lam := by
          nlinarith [hsquare]
        exact hy_eq.trans hc_eq.symm
      · have hmid : |x| ≤ lam := by
          rw [abs_le]
          constructor
          · linarith
          · linarith
        have hc_eq : c = 0 := by
          -- Inside the threshold window, the unique minimizer is the origin.
          simp [c, posPart_of_nonpos (sub_nonpos.mpr hmid)]
        have hxy_le : x * y ≤ lam * |y| := by
          calc
            x * y ≤ |x * y| := le_abs_self (x * y)
            _ = |x| * |y| := by rw [abs_mul]
            _ ≤ lam * |y| := mul_le_mul_of_nonneg_right hmid (abs_nonneg y)
        have hterm_nonneg : 0 ≤ lam * |y| - x * y := by
          nlinarith
        have hsum_zero :
            (1 / 2 : ℝ) * y ^ 2 + lam * |y| - x * y = 0 := by
          rw [hc_eq] at hcy
          rw [← absolute_value_penalty_objective_gap_mid lam x y, hcy]
          ring
        have hsqhalf : (1 / 2 : ℝ) * y ^ 2 = 0 := by
          nlinarith [hsum_zero, hterm_nonneg]
        have hsquare : y ^ 2 = 0 := by
          nlinarith [hsqhalf]
        have hy_eq : y = 0 := sq_eq_zero_iff.mp hsquare
        exact hy_eq.trans hc_eq.symm

-- Proof sketch: minimize `u ↦ λ u^3 + (1 / 2) (u - x)^2` on `u ≥ 0`. For `x ≤ 0`, the minimum is
-- attained at the boundary point `0`. For `x > 0`, strict convexity gives the first-order
-- equation `3 λ u^2 + u - x = 0`, whose nonnegative root is the displayed value.
/-- Lemma 6.5 (3): for the penalty `g₃(x) = λ x^3` on `[0, ∞)` and `∞` on `(-∞, 0)`, with
`0 < λ`, the proximal mapping is `0` on `(-∞, 0]` and otherwise the positive quadratic root
`(-1 + √(1 + 12 λ x)) / (6 λ)`. -/
theorem prox_nonnegative_cubic_penalty_eq_singleton
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    prox[nonnegative_cubic_penalty lam] x =
      {if 0 < x then (-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam) else 0} := by
  let r : ℝ := if 0 < x then (-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam) else 0
  have hr_nonneg : 0 ≤ r := by
    by_cases hx : 0 < x
    · have hsqrt_ge : 1 ≤ Real.sqrt (1 + 12 * lam * x) := by
        apply (Real.one_le_sqrt).2
        nlinarith [hlam, hx]
      have hden : 0 < 6 * lam := by
        nlinarith
      simp [r, hx]
      exact div_nonneg (by nlinarith) hden.le
    · simp [r, hx]
  have hr_value :
      proximal_objective (nonnegative_cubic_penalty lam) x r =
        (((lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2 : ℝ)) : EReal) := by
    -- The candidate is feasible, so the indicator contributes `0`.
    simp [proximal_objective_apply, nonnegative_cubic_penalty_apply, hr_nonneg]
  have hr_mem : r ∈ prox[nonnegative_cubic_penalty lam] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro u
    by_cases hu : 0 ≤ u
    · have hu_value :
          proximal_objective (nonnegative_cubic_penalty lam) x u =
            (((lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
        simp [proximal_objective_apply, nonnegative_cubic_penalty_apply, hu]
      by_cases hx : 0 < x
      · have hr_eq :
            r = (-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam) := by
          simp [r, hx]
        have hroot : 3 * lam * r ^ 2 + r - x = 0 := by
          simpa [hr_eq] using nonnegative_cubic_candidate_root_eq lam x hlam hx
        -- On the positive branch, the objective gap factors into a square times a nonnegative
        -- coefficient.
        have hgap :
            lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 -
                (lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2) =
              (u - r) ^ 2 * (lam * (u + 2 * r) + 1 / 2) := by
          exact nonnegative_cubic_objective_gap lam x r u hroot
        have hcoef : 0 ≤ lam * (u + 2 * r) + 1 / 2 := by
          nlinarith [hlam, hu, hr_nonneg]
        have hsub :
            0 ≤ lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 -
                (lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2) := by
          rw [hgap]
          positivity
        have hmain :
            lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2 ≤
              lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          linarith
        rw [hr_value, hu_value]
        exact_mod_cast hmain
      · have hx_nonpos : x ≤ 0 := le_of_not_gt hx
        have hr_eq : r = 0 := by
          simp [r, hx]
        -- For `x ≤ 0`, the feasible boundary point `0` beats every `u ≥ 0`.
        have hy3 : 0 ≤ u ^ 3 := by
          positivity
        have hmain :
            lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2 ≤
              lam * u ^ 3 + (1 / 2 : ℝ) * (u - x) ^ 2 := by
          rw [hr_eq]
          nlinarith [hy3, hlam, hu, hx_nonpos]
        rw [hr_value, hu_value]
        exact_mod_cast hmain
    · have htop : proximal_objective (nonnegative_cubic_penalty lam) x u = ⊤ := by
        -- Outside `[0, ∞)`, the indicator makes the objective infinite.
        calc
          proximal_objective (nonnegative_cubic_penalty lam) x u
              = ⊤ + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                  simp [proximal_objective_apply, nonnegative_cubic_penalty_apply, hu]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop]
      simp
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · exact hr_mem
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hr_mem
    have hy_le :
        proximal_objective (nonnegative_cubic_penalty lam) x y ≤
          proximal_objective (nonnegative_cubic_penalty lam) x r := hy r
    have hr_le :
        proximal_objective (nonnegative_cubic_penalty lam) x r ≤
          proximal_objective (nonnegative_cubic_penalty lam) x y := hr_mem y
    have hr_finite : proximal_objective (nonnegative_cubic_penalty lam) x r < ⊤ := by
      rw [hr_value]
      exact EReal.coe_lt_top _
    have hy_nonneg : 0 ≤ y := by
      by_contra hy_neg
      have htop : proximal_objective (nonnegative_cubic_penalty lam) x y = ⊤ := by
        calc
          proximal_objective (nonnegative_cubic_penalty lam) x y
              = ⊤ + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                  simp [proximal_objective_apply, nonnegative_cubic_penalty_apply, hy_neg]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop] at hy_le
      exact (not_le_of_gt hr_finite) hy_le
    have hy_value :
        proximal_objective (nonnegative_cubic_penalty lam) x y =
          (((lam * y ^ 3 + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
      simp [proximal_objective_apply, nonnegative_cubic_penalty_apply, hy_nonneg]
    by_cases hx : 0 < x
    · have hr_eq :
          r = (-1 + Real.sqrt (1 + 12 * lam * x)) / (6 * lam) := by
        simp [r, hx]
      have hroot : 3 * lam * r ^ 2 + r - x = 0 := by
        simpa [hr_eq] using nonnegative_cubic_candidate_root_eq lam x hlam hx
      have hcy :
          lam * y ^ 3 + (1 / 2 : ℝ) * (y - x) ^ 2 =
            lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2 := by
        rw [hy_value, hr_value] at hy_le hr_le
        exact_mod_cast le_antisymm hy_le hr_le
      -- Equality of the objective values forces the square factor in the gap identity to vanish.
      have hgap :
          lam * y ^ 3 + (1 / 2 : ℝ) * (y - x) ^ 2 -
              (lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2) =
            (y - r) ^ 2 * (lam * (y + 2 * r) + 1 / 2) := by
        exact nonnegative_cubic_objective_gap lam x r y hroot
      have hprod_zero : (y - r) ^ 2 * (lam * (y + 2 * r) + 1 / 2) = 0 := by
        rw [← hgap, hcy]
        ring
      have hcoef_pos : 0 < lam * (y + 2 * r) + 1 / 2 := by
        nlinarith [hlam, hy_nonneg, hr_nonneg]
      have hsquare : (y - r) ^ 2 = 0 := by
        exact Or.resolve_right (mul_eq_zero.mp hprod_zero) (ne_of_gt hcoef_pos)
      have hyr : y - r = 0 := sq_eq_zero_iff.mp hsquare
      linarith
    · have hx_nonpos : x ≤ 0 := le_of_not_gt hx
      have hr_eq : r = 0 := by
        simp [r, hx]
      have hcy :
          lam * y ^ 3 + (1 / 2 : ℝ) * (y - x) ^ 2 =
            lam * r ^ 3 + (1 / 2 : ℝ) * (r - x) ^ 2 := by
        rw [hy_value, hr_value] at hy_le hr_le
        exact_mod_cast le_antisymm hy_le hr_le
      rw [hr_eq] at hcy
      -- On the boundary branch, every term is nonnegative, so equality forces `y = 0`.
      have hy3 : 0 ≤ y ^ 3 := by
        positivity
      have hxy : 0 ≤ -y * x := by
        nlinarith [hy_nonneg, hx_nonpos]
      nlinarith [hy3, hxy, hcy, hlam]

-- Proof sketch: this is the proximal formula for the positive-ray function obtained by scaling
-- the Chapter 4 owner `negative_log_barrier` by `λ` on its finite branch. Minimize
-- `u ↦ -λ log u + (1 / 2) (u - x)^2` on `(0, ∞)`; strict convexity gives the first-order
-- equation `u^2 - x u - λ = 0`, and the unique feasible root is the positive one.
/-- Lemma 6.5 (4): for the positive-ray scaling of the Chapter 4 owner `negative_log_barrier`,
namely `g₄(x) = -λ log x` on `(0, ∞)` and `∞` on `(-∞, 0]`, with `0 < λ`, the proximal mapping is
the singleton `{(x + √(x^2 + 4 λ)) / 2}`. -/
theorem prox_scalar_log_barrier_penalty_eq_singleton
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    prox[(lam : EReal) • negative_log_barrier] x =
      {(x + Real.sqrt (x ^ 2 + 4 * lam)) / 2} := by
  let r : ℝ := (x + Real.sqrt (x ^ 2 + 4 * lam)) / 2
  have hr_pos : 0 < r := by
    simpa [r] using scalar_log_barrier_candidate_pos lam x hlam
  have hr_value :
      proximal_objective ((lam : EReal) • negative_log_barrier) x r =
        (((-lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2 : ℝ)) : EReal) := by
    -- The candidate lies in the positive domain of the barrier.
    simp [proximal_objective_apply, negative_log_barrier, hr_pos, Pi.smul_apply, smul_eq_mul]
  have hr_root : r ^ 2 - x * r - lam = 0 := by
    simpa [r] using scalar_log_barrier_candidate_root_eq lam x hlam
  have hr_mem : r ∈ prox[(lam : EReal) • negative_log_barrier] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro u
    by_cases hu : 0 < u
    · have hu_value :
          proximal_objective ((lam : EReal) • negative_log_barrier) x u =
            (((-lam * Real.log u + (1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
        simp [proximal_objective_apply, negative_log_barrier, hu, Pi.smul_apply, smul_eq_mul]
      -- Use the canonical `t - 1 - log t` nonnegativity after normalizing by the root `r`.
      have hgap :
          -lam * Real.log u + (1 / 2 : ℝ) * (u - x) ^ 2 -
              (-lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2) =
            lam * ((u / r) - 1 - Real.log (u / r)) + (1 / 2 : ℝ) * (u - r) ^ 2 := by
        exact scalar_log_barrier_objective_gap lam x r u hr_root hu hr_pos
      have hlog_nonneg : 0 ≤ (u / r) - 1 - Real.log (u / r) := by
        have hratio : 0 < u / r := div_pos hu hr_pos
        have hineq := Real.log_le_sub_one_of_pos hratio
        nlinarith
      have hsub :
          0 ≤ -lam * Real.log u + (1 / 2 : ℝ) * (u - x) ^ 2 -
              (-lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2) := by
        rw [hgap]
        positivity
      have hmain :
          -lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2 ≤
            -lam * Real.log u + (1 / 2 : ℝ) * (u - x) ^ 2 := by
        linarith
      rw [hr_value, hu_value]
      exact_mod_cast hmain
    · have hlamE : (0 : EReal) < (lam : EReal) := by
        exact_mod_cast hlam
      have htop : proximal_objective ((lam : EReal) • negative_log_barrier) x u = ⊤ := by
        -- At nonpositive points the barrier is `⊤`, and positive scaling preserves `⊤`.
        calc
          proximal_objective ((lam : EReal) • negative_log_barrier) x u
              = ((lam : EReal) * ⊤) +
                  ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                    simp [proximal_objective_apply, negative_log_barrier, hu, Pi.smul_apply,
                      smul_eq_mul]
          _ = ⊤ + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                rw [EReal.mul_top_of_pos hlamE]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop]
      simp
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · exact hr_mem
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hr_mem
    have hy_le :
        proximal_objective ((lam : EReal) • negative_log_barrier) x y ≤
          proximal_objective ((lam : EReal) • negative_log_barrier) x r := hy r
    have hr_le :
        proximal_objective ((lam : EReal) • negative_log_barrier) x r ≤
          proximal_objective ((lam : EReal) • negative_log_barrier) x y := hr_mem y
    have hr_finite : proximal_objective ((lam : EReal) • negative_log_barrier) x r < ⊤ := by
      rw [hr_value]
      exact EReal.coe_lt_top _
    have hy_pos : 0 < y := by
      by_contra hy_nonpos
      have hlamE : (0 : EReal) < (lam : EReal) := by
        exact_mod_cast hlam
      have htop : proximal_objective ((lam : EReal) • negative_log_barrier) x y = ⊤ := by
        calc
          proximal_objective ((lam : EReal) • negative_log_barrier) x y
              = ((lam : EReal) * ⊤) +
                  ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                    simp [proximal_objective_apply, negative_log_barrier, hy_nonpos, Pi.smul_apply,
                      smul_eq_mul]
          _ = ⊤ + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                rw [EReal.mul_top_of_pos hlamE]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      rw [htop] at hy_le
      exact (not_le_of_gt hr_finite) hy_le
    have hy_value :
        proximal_objective ((lam : EReal) • negative_log_barrier) x y =
          (((-lam * Real.log y + (1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
      simp [proximal_objective_apply, negative_log_barrier, hy_pos, Pi.smul_apply, smul_eq_mul]
    have hcy :
        -lam * Real.log y + (1 / 2 : ℝ) * (y - x) ^ 2 =
          -lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2 := by
      rw [hy_value, hr_value] at hy_le hr_le
      exact_mod_cast le_antisymm hy_le hr_le
    -- Equality in the normalized objective gap forces the square term to vanish.
    have hgap :
        -lam * Real.log y + (1 / 2 : ℝ) * (y - x) ^ 2 -
            (-lam * Real.log r + (1 / 2 : ℝ) * (r - x) ^ 2) =
          lam * ((y / r) - 1 - Real.log (y / r)) + (1 / 2 : ℝ) * (y - r) ^ 2 := by
      exact scalar_log_barrier_objective_gap lam x r y hr_root hy_pos hr_pos
    have hsum_zero :
        lam * ((y / r) - 1 - Real.log (y / r)) + (1 / 2 : ℝ) * (y - r) ^ 2 = 0 := by
      rw [← hgap, hcy]
      ring
    have hlog_nonneg : 0 ≤ (y / r) - 1 - Real.log (y / r) := by
      have hratio : 0 < y / r := div_pos hy_pos hr_pos
      have hineq := Real.log_le_sub_one_of_pos hratio
      nlinarith
    have hterm_nonneg : 0 ≤ lam * ((y / r) - 1 - Real.log (y / r)) := by
      nlinarith [hlam, hlog_nonneg]
    have hsqhalf : (1 / 2 : ℝ) * (y - r) ^ 2 = 0 := by
      nlinarith [hsum_zero, hterm_nonneg]
    have hsquare : (y - r) ^ 2 = 0 := by
      nlinarith [hsqhalf]
    have hyr : y - r = 0 := sq_eq_zero_iff.mp hsquare
    have hy_eq_r : y = r := sub_eq_zero.mp hyr
    simpa [r] using hy_eq_r

-- Proof sketch: the canonical owner is the Chapter 2 indicator `extendedIndicator` of the
-- feasible interval `[0, η] ∩ ℝ`, with the nonnegative interval bound carried directly by the
-- chapter's `ENNReal` owner. The proximal objective reduces to Euclidean projection onto that
-- interval. The minimizer is the truncation of `x` to the interval, with the `η = ∞` branch
-- reducing to projection onto `[0, ∞)`.
/-- Helper for Lemma 6.5: in the finite-`η` branch, the Chapter 2 feasibility condition
`0 ≤ y ∧ (y : EReal) ≤ η` is exactly membership in the real interval `[0, η.toReal]`. -/
theorem nonnegative_interval_mem_iff_mem_Icc_toReal
    (eta : ENNReal) (hfin : eta ≠ ⊤) (y : ℝ) :
    (0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)) ↔ y ∈ Set.Icc 0 eta.toReal := by
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [← EReal.coe_ennreal_toReal hfin] at hy
    exact EReal.coe_le_coe_iff.mp hy.2
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [← EReal.coe_ennreal_toReal hfin]
    exact_mod_cast hy.2

/-- Helper for Lemma 6.5: projection onto a closed interval minimizes the squared distance to the
base point. -/
theorem nonnegative_interval_projection_gap
    (b x u : ℝ) (hb : 0 ≤ b) (hu : u ∈ Set.Icc 0 b) :
    ((((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ) - x) ^ 2) ≤ (u - x) ^ 2 := by
  -- Split according to whether the projection lands on the left endpoint, in the interval, or on
  -- the right endpoint.
  by_cases hx0 : x ≤ 0
  · have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = 0 := by
      rw [Set.coe_projIcc]
      simp [hx0]
    rw [hc_eq]
    nlinarith [hu.1, hx0]
  · have hxpos : 0 < x := lt_of_not_ge hx0
    by_cases hxin : x ≤ b
    · have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = x := by
        rw [Set.coe_projIcc]
        simp [le_of_lt hxpos, hxin]
      rw [hc_eq]
      nlinarith [sq_nonneg (u - x)]
    · have hxb : b < x := lt_of_not_ge hxin
      have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = b := by
        rw [Set.coe_projIcc]
        simp [hb, le_of_lt hxb]
      rw [hc_eq]
      nlinarith [hu.2, hxb]

/-- Helper for Lemma 6.5: equality in the interval projection distance comparison forces the point
to equal the projection itself. -/
theorem nonnegative_interval_projection_eq_of_sq_eq
    (b x u : ℝ) (hb : 0 ≤ b) (hu : u ∈ Set.Icc 0 b)
    (heq :
      (u - x) ^ 2 = ((((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ) - x) ^ 2)) :
    u = ((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ) := by
  -- The same three projection regimes show that equality is possible only at the projected point.
  by_cases hx0 : x ≤ 0
  · have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = 0 := by
      rw [Set.coe_projIcc]
      simp [hx0]
    rw [hc_eq] at heq ⊢
    nlinarith [hu.1, hx0]
  · have hxpos : 0 < x := lt_of_not_ge hx0
    by_cases hxin : x ≤ b
    · have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = x := by
        rw [Set.coe_projIcc]
        simp [le_of_lt hxpos, hxin]
      rw [hc_eq] at heq ⊢
      nlinarith
    · have hxb : b < x := lt_of_not_ge hxin
      have hc_eq : (((Set.projIcc 0 b hb x : Set.Icc 0 b) : ℝ)) = b := by
        rw [Set.coe_projIcc]
        simp [hb, le_of_lt hxb]
      rw [hc_eq] at heq ⊢
      nlinarith [hu.2, hxb]

/-- Helper for Lemma 6.5: projection onto the nonnegative ray minimizes the squared distance to
the base point. -/
theorem nonnegative_ray_projection_gap (x u : ℝ) (hu : 0 ≤ u) :
    ((max x 0 - x) ^ 2) ≤ (u - x) ^ 2 := by
  -- The projection is `0` to the left of the ray and `x` on the ray itself.
  by_cases hx0 : x ≤ 0
  · have hc_eq : max x 0 = 0 := by
      simp [hx0]
    rw [hc_eq]
    nlinarith [hu, hx0]
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hc_eq : max x 0 = x := by
      simp [le_of_lt hxpos]
    rw [hc_eq]
    nlinarith [sq_nonneg (u - x)]

/-- Helper for Lemma 6.5: equality in the nonnegative-ray projection distance comparison forces
the point to equal the projection itself. -/
theorem nonnegative_ray_projection_eq_of_sq_eq
    (x u : ℝ) (hu : 0 ≤ u) (heq : (u - x) ^ 2 = (max x 0 - x) ^ 2) :
    u = max x 0 := by
  -- Equality is only possible at the endpoint `0` or at the interior point `x`.
  by_cases hx0 : x ≤ 0
  · have hc_eq : max x 0 = 0 := by
      simp [hx0]
    rw [hc_eq] at heq ⊢
    nlinarith [hu, hx0]
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hc_eq : max x 0 = x := by
      simp [le_of_lt hxpos]
    rw [hc_eq] at heq ⊢
    nlinarith

/-- Lemma 6.5 (5): for the Chapter 2 indicator of the interval `[0, η]`, with `η ∈ [0, ∞]`, the
proximal mapping is the singleton given by truncation to the interval: `min (max x 0) η` in the
finite case and `max x 0` when `η = ∞`. -/
theorem prox_nonnegative_interval_indicator_eq_singleton (eta : ENNReal) (x : ℝ) :
    prox[extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}] x =
      {if htop : eta = ⊤ then max x 0 else min (max x 0) eta.toReal} := by
  by_cases htop : eta = ⊤
  · subst eta
    let c := max x 0
    have hc_nonneg : 0 ≤ c := by
      exact le_max_right x 0
    have hsingle : prox[extendedIndicator {y : ℝ | 0 ≤ y}] x = {max x 0} := by
      have hc_value :
          proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x c =
            ((((1 / 2 : ℝ) * (c - x) ^ 2 : ℝ)) : EReal) := by
        -- On the ray branch, the indicator vanishes exactly at nonnegative points.
        simp [proximal_objective_apply, extendedIndicator, c, hc_nonneg]
      have hc_mem : c ∈ prox[extendedIndicator {y : ℝ | 0 ≤ y}] x := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro u
        by_cases hu : 0 ≤ u
        · have hu_value :
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x u =
                ((((1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
            simp [proximal_objective_apply, extendedIndicator, hu]
          have hmain : (1 / 2 : ℝ) * (c - x) ^ 2 ≤ (1 / 2 : ℝ) * (u - x) ^ 2 := by
            have hgap : (c - x) ^ 2 ≤ (u - x) ^ 2 := by
              simpa [c] using nonnegative_ray_projection_gap x u hu
            exact mul_le_mul_of_nonneg_left hgap (by norm_num)
          rw [hc_value, hu_value]
          exact_mod_cast hmain
        · have htop_obj :
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x u = ⊤ := by
            calc
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x u
                  = ⊤ + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                      simp [proximal_objective_apply, extendedIndicator, hu]
              _ = ⊤ := by
                    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
          rw [htop_obj]
          simp
      refine Set.eq_singleton_iff_unique_mem.2 ?_
      constructor
      · simpa [c] using hc_mem
      · intro y hy
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hc_mem
        have hy_le :
            proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x y ≤
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x c := hy c
        have hc_le :
            proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x c ≤
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x y := hc_mem y
        have hc_finite :
            proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x c < ⊤ := by
          rw [hc_value]
          exact EReal.coe_lt_top _
        have hy_nonneg : 0 ≤ y := by
          by_contra hy_neg
          have htop_obj :
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x y = ⊤ := by
            calc
              proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x y
                  = ⊤ + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                      simp [proximal_objective_apply, extendedIndicator, hy_neg]
              _ = ⊤ := by
                    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
          rw [htop_obj] at hy_le
          exact (not_le_of_gt hc_finite) hy_le
        have hy_value :
            proximal_objective (extendedIndicator {y : ℝ | 0 ≤ y}) x y =
              ((((1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
          simp [proximal_objective_apply, extendedIndicator, hy_nonneg]
        have hsqhalf :
            (1 / 2 : ℝ) * (y - x) ^ 2 = (1 / 2 : ℝ) * (c - x) ^ 2 := by
          rw [hy_value, hc_value] at hy_le hc_le
          exact_mod_cast le_antisymm hy_le hc_le
        have hsq : (y - x) ^ 2 = (c - x) ^ 2 := by
          nlinarith [hsqhalf]
        have hy_eq : y = c := by
          simpa [c] using nonnegative_ray_projection_eq_of_sq_eq x y hy_nonneg hsq
        simpa [c] using hy_eq
    simpa using hsingle
  · let c : ℝ := ((Set.projIcc 0 eta.toReal (by positivity) x : Set.Icc 0 eta.toReal) : ℝ)
    have hc_mem_Icc : c ∈ Set.Icc 0 eta.toReal := by
      simpa [c] using (Set.projIcc 0 eta.toReal (by positivity) x).property
    have hc_feasible : 0 ≤ c ∧ (c : EReal) ≤ (eta : EReal) := by
      exact (nonnegative_interval_mem_iff_mem_Icc_toReal eta htop c).2 hc_mem_Icc
    have hc_value :
        proximal_objective
            (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x c =
          ((((1 / 2 : ℝ) * (c - x) ^ 2 : ℝ)) : EReal) := by
      -- On the finite interval branch, the indicator vanishes exactly on `[0, η.toReal]`.
      simp [proximal_objective_apply, extendedIndicator, hc_feasible]
    have hc_mem :
        c ∈ prox[extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}] x := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro u
      by_cases hu_feasible : 0 ≤ u ∧ (u : EReal) ≤ (eta : EReal)
      · have hu_Icc : u ∈ Set.Icc 0 eta.toReal := by
          exact (nonnegative_interval_mem_iff_mem_Icc_toReal eta htop u).1 hu_feasible
        have hu_value :
            proximal_objective
                (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x u =
              ((((1 / 2 : ℝ) * (u - x) ^ 2 : ℝ)) : EReal) := by
          simp [proximal_objective_apply, extendedIndicator, hu_feasible]
        have hmain : (1 / 2 : ℝ) * (c - x) ^ 2 ≤ (1 / 2 : ℝ) * (u - x) ^ 2 := by
          have hgap : (c - x) ^ 2 ≤ (u - x) ^ 2 := by
            simpa [c] using
              nonnegative_interval_projection_gap eta.toReal x u ENNReal.toReal_nonneg hu_Icc
          exact mul_le_mul_of_nonneg_left hgap (by norm_num)
        rw [hc_value, hu_value]
        exact_mod_cast hmain
      · have htop_obj :
            proximal_objective
                (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x u = ⊤ := by
          calc
            proximal_objective
                (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x u
                = ⊤ + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                    simp [proximal_objective_apply, extendedIndicator, hu_feasible]
            _ = ⊤ := by
                  rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
        rw [htop_obj]
        simp
    have hc_target : c = min (max x 0) eta.toReal := by
      -- The interval projection rewrites to the usual clamp formula.
      calc
        c = max 0 (min eta.toReal x) := by
          rw [show c = ((Set.projIcc 0 eta.toReal (by positivity) x : Set.Icc 0 eta.toReal) : ℝ) by
            rfl]
          rw [Set.coe_projIcc]
        _ = min (max 0 eta.toReal) (max 0 x) := by
          rw [max_min_distrib_left]
        _ = min eta.toReal (max 0 x) := by
          rw [max_eq_right ENNReal.toReal_nonneg]
        _ = min (max x 0) eta.toReal := by
          rw [max_comm, min_comm]
    refine Set.eq_singleton_iff_unique_mem.2 ?_
    constructor
    · simpa [htop, hc_target] using hc_mem
    · intro y hy
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hc_mem
      have hy_le :
          proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x y ≤
            proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x c := hy c
      have hc_le :
          proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x c ≤
            proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x y := hc_mem y
      have hc_finite :
          proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x c < ⊤ := by
        rw [hc_value]
        exact EReal.coe_lt_top _
      have hy_feasible : 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal) := by
        by_contra hy_not_feasible
        have htop_obj :
            proximal_objective
                (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x y = ⊤ := by
          calc
            proximal_objective
                (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x y
                = ⊤ + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                    simp [proximal_objective_apply, extendedIndicator, hy_not_feasible]
            _ = ⊤ := by
                  rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
        rw [htop_obj] at hy_le
        exact (not_le_of_gt hc_finite) hy_le
      have hy_Icc : y ∈ Set.Icc 0 eta.toReal := by
        exact (nonnegative_interval_mem_iff_mem_Icc_toReal eta htop y).1 hy_feasible
      have hy_value :
          proximal_objective
              (extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (eta : EReal)}) x y =
            ((((1 / 2 : ℝ) * (y - x) ^ 2 : ℝ)) : EReal) := by
        simp [proximal_objective_apply, extendedIndicator, hy_feasible]
      have hsqhalf :
          (1 / 2 : ℝ) * (y - x) ^ 2 = (1 / 2 : ℝ) * (c - x) ^ 2 := by
        rw [hy_value, hc_value] at hy_le hc_le
        exact_mod_cast le_antisymm hy_le hc_le
      have hsq : (y - x) ^ 2 = (c - x) ^ 2 := by
        nlinarith [hsqhalf]
      have hy_eq : y = c := by
        simpa [c] using
          nonnegative_interval_projection_eq_of_sq_eq
            eta.toReal x y ENNReal.toReal_nonneg hy_Icc hsq
      simpa [htop, hc_target] using hy_eq
