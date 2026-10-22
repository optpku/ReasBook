/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_2.Rate
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_2.Majorant

noncomputable section

open Filter

universe u

section ConvergenceRates

variable {E : Type u} [NormedAddCommGroup E]

/-- Helper for Chapter01 Definition 1.5-extra-2: a positive multiple of a geometric sequence
with ratio `β ∈ (0, 1)` converges `Q`-linearly to `0`. -/
private theorem scaledGeometric_hasQLinearConvergenceTo_zero
    {C β : ℝ} (hC : 0 < C) (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasQLinearConvergenceTo (fun k : ℕ ↦ C * β ^ (k + 1)) 0 := by
  refine ⟨β, hβ1, ?_⟩
  refine
    { one_le := ?_
      beta_pos := ?_
      tendsto := ?_
      ratio_tendsto := ?_ }
  · norm_num
  · exact hβ0
  · -- The geometric witness tends to zero because `β ^ n → 0`.
    have hpow : Tendsto (fun n : ℕ ↦ β ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul (C * β)
  · -- The first-order `Q`-ratio is constantly `β`.
    have hratio :
        qErrorRatio (fun k : ℕ ↦ C * β ^ (k + 1)) 0 1 = fun _ : ℕ ↦ β := by
      funext k
      have hkpow : C * β ^ (k + 1) ≠ 0 := by positivity
      calc
        qErrorRatio (fun k : ℕ ↦ C * β ^ (k + 1)) 0 1 k
            = (C * β ^ (k + 2)) / (C * β ^ (k + 1)) := by
                rw [qErrorRatio_apply]
                simp [abs_of_nonneg, hC.le, hβ0.le]
        _ = β := by
          rw [pow_succ']
          field_simp [hkpow]
    rw [hratio]
    simp

/-- Helper for Chapter01 Definition 1.5-extra-2: a positive multiple of a dyadic-geometric
sequence with ratio `β ∈ (0, 1)` converges `Q`-quadratically to `0`. -/
private theorem scaledDyadicGeometric_hasQQuadraticConvergenceTo_zero
    {C β : ℝ} (hC : 0 < C) (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasQQuadraticConvergenceTo (fun k : ℕ ↦ C * β ^ (2 ^ (k + 1 : ℕ))) 0 := by
  refine ⟨C⁻¹, ?_⟩
  refine
    { one_le := by norm_num
      beta_pos := by positivity
      tendsto := ?_
      ratio_tendsto := ?_ }
  · -- The dyadic-geometric witness tends to zero because the exponent `2^(k+1)` diverges.
    have hpow : Tendsto (fun n : ℕ ↦ β ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have hexp : Tendsto (fun n : ℕ ↦ 2 ^ (n + 1 : ℕ)) atTop atTop := by
      exact
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
          (Filter.tendsto_add_atTop_nat 1)
    simpa using (hpow.comp hexp).const_mul C
  · -- The second-order `Q`-ratio is the positive constant `C⁻¹`.
    have hratio :
        qErrorRatio (fun k : ℕ ↦ C * β ^ (2 ^ (k + 1 : ℕ))) 0 2 =
          fun _ : ℕ ↦ C⁻¹ := by
      funext k
      have hkpow : β ^ (2 ^ (k + 1 : ℕ)) ≠ 0 := by
        positivity
      calc
        qErrorRatio (fun k : ℕ ↦ C * β ^ (2 ^ (k + 1 : ℕ))) 0 2 k
            = (C * β ^ (2 ^ (k + 2 : ℕ))) /
                ((C * β ^ (2 ^ (k + 1 : ℕ))) ^ 2) := by
                  rw [qErrorRatio_apply]
                  simp [abs_of_nonneg, hC.le, hβ0.le]
        _ = C⁻¹ := by
          rw [show 2 ^ (k + 2 : ℕ) = 2 ^ (k + 1 : ℕ) * 2 by
            rw [pow_succ']
            ring]
          rw [pow_mul]
          field_simp [hC.ne', hkpow]
    rw [hratio]
    simp

/-- Helper for Chapter01 Definition 1.5-extra-2: a nonnegative scalar sequence that converges
`Q`-linearly to `0` has first `R`-rate strictly below `1`. -/
private theorem rRate_one_lt_one_of_nonneg_hasQLinearConvergenceTo
    {q : ℕ → ℝ} (hqNonneg : ∀ k : ℕ, 0 ≤ q k)
    (hq : HasQLinearConvergenceTo q 0) :
    R[1] q 0 < 1 := by
  rcases hq with ⟨β, hβ1, hβOrder⟩
  obtain ⟨γ, hβγ, hγ1⟩ := exists_between hβ1
  have hγ0 : 0 < γ := lt_trans hβOrder.beta_pos hβγ
  have hratioEvent :
      ∀ᶠ k in atTop, qErrorRatio q 0 1 k < γ :=
    hβOrder.ratio_tendsto.eventually (Iio_mem_nhds hβγ)
  have hnonzeroEvent : ∀ᶠ k in atTop, q k ≠ 0 := hβOrder.eventually_ne
  rcases (eventually_atTop.1 (hratioEvent.and hnonzeroEvent)) with ⟨N, hN⟩
  let A : ℝ := q N / γ ^ (N + 1)
  have hgeom : ∀ m : ℕ, q (N + m) ≤ A * γ ^ (N + m + 1) := by
    intro m
    induction m with
    | zero =>
        have hγpow_ne : γ ^ (N + 1) ≠ 0 := by positivity
        dsimp [A]
        have : q N = q N / γ ^ (N + 1) * γ ^ (N + 1) := by
          field_simp [hγpow_ne]
        simpa using this.le
    | succ m hm =>
        rcases hN (N + m) (Nat.le_add_right N m) with ⟨hkRatio, hkNe⟩
        have hkPos : 0 < q (N + m) := lt_of_le_of_ne (hqNonneg _) (Ne.symm hkNe)
        have hstep : q (N + m + 1) ≤ γ * q (N + m) := by
          have hkRatio' :
              q (N + m + 1) / q (N + m) < γ := by
            simpa [qErrorRatio_apply, abs_of_nonneg, hqNonneg (N + m), hqNonneg (N + m + 1)]
              using hkRatio
          exact (div_lt_iff₀ hkPos).1 hkRatio' |>.le
        calc
          q (N + (m + 1)) = q (N + m + 1) := by simp [Nat.add_assoc]
          _ ≤ γ * q (N + m) := hstep
          _ ≤ γ * (A * γ ^ (N + m + 1)) := by
                gcongr
          _ = A * γ ^ (N + m + 2) := by
                calc
                  γ * (A * γ ^ (N + m + 1))
                      = A * (γ * γ ^ (N + m + 1)) := by ring
                  _ = A * γ ^ (N + m + 2) := by rw [← pow_succ']
          _ = A * γ ^ (N + (m + 1) + 1) := by simp [Nat.add_assoc]
  obtain ⟨η, hγη, hη1⟩ := exists_between hγ1
  have hη0 : 0 < η := lt_trans hγ0 hγη
  have hbase : 1 < η / γ := by
    have hγpos : 0 < γ := hγ0
    field_simp [hγpos.ne']
    linarith
  have hpowTop :
      Tendsto (fun n : ℕ ↦ (η / γ) ^ (N + n + 1)) atTop atTop := by
    convert
      (tendsto_pow_atTop_atTop_of_one_lt hbase).comp (Filter.tendsto_add_atTop_nat (N + 1))
        using 1
    ext n
    simp [Nat.add_assoc, Nat.add_left_comm]
  have hAbsorb :
      ∀ᶠ n in atTop, A ≤ (η / γ) ^ (N + n + 1) := by
    exact (hpowTop.eventually_gt_atTop A).mono fun _ hn ↦ hn.le
  have hEtaBound :
      ∀ᶠ n in atTop, q n ≤ η ^ (n + 1) := by
    rcases (eventually_atTop.1 hAbsorb) with ⟨M, hM⟩
    refine eventually_atTop.2 ⟨N + M, ?_⟩
    intro n hn
    have hNn : N ≤ n := le_trans (Nat.le_add_right N M) hn
    have hMn : M ≤ n - N := by
      have hn' : M + N ≤ n := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      exact (Nat.le_sub_iff_add_le hNn).2 hn'
    have hA : A ≤ (η / γ) ^ (N + (n - N) + 1) := hM (n - N) hMn
    calc
      q n = q (N + (n - N)) := by rw [Nat.add_sub_of_le hNn]
      _ ≤ A * γ ^ (N + (n - N) + 1) := hgeom (n - N)
      _ ≤ ((η / γ) ^ (N + (n - N) + 1)) * γ ^ (N + (n - N) + 1) := by
            gcongr
      _ = η ^ (N + (n - N) + 1) := by
            have hγpow_ne : γ ^ (N + (n - N) + 1) ≠ 0 := by
              exact pow_ne_zero _ hγ0.ne'
            rw [div_pow, div_eq_mul_inv, mul_assoc]
            field_simp [hγpow_ne]
      _ = η ^ (n + 1) := by rw [Nat.add_sub_of_le hNn]
  have hRootLeEvent :
      ∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 1 n) ≤ η := by
    filter_upwards [hEtaBound] with n hn
    have hrootLe :
        Real.rpow (q n) ((n + 1 : ℝ)⁻¹) ≤ η := by
      exact
        (Real.rpow_inv_le_iff_of_pos (hqNonneg n) hη0.le (by positivity)).2
          (by
            have hpowEq : η ^ ((n : ℝ) + 1) = η ^ (n + 1 : ℕ) := by
              rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast]
            rw [hpowEq]
            exact hn)
    simpa [rRateExponent_eq, one_div, abs_of_nonneg (hqNonneg n)] using hrootLe
  have hRateLe : R[1] q 0 ≤ η := by
    rw [rRate_eq_limsup]
    have hCobounded :
        Filter.IsCoboundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 1 n)) := by
      change
        ∃ b : ℝ,
          ∀ a : ℝ,
            (∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 1 n) ≤ a) → b ≤ a
      refine ⟨0, ?_⟩
      intro a ha
      rcases ha.exists with ⟨n, hn⟩
      exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) hn
    have hBounded :
        Filter.IsBoundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 1 n)) := ⟨η, hRootLeEvent⟩
    refine (limsup_le_iff hCobounded hBounded).2 ?_
    · intro y hy
      filter_upwards [hRootLeEvent] with n hn
      exact lt_of_le_of_lt hn hy
  exact lt_of_le_of_lt hRateLe hη1

/-- A linear companion to Chapter01 Definition 1.5-extra-2: the sequence `x` is `R`-linearly
convergent in the
source's broader reformulation precisely when there is a nonnegative scalar majorant sequence
`q` with `‖x k - xStar‖ ≤ q k` for all `k` and `q` converging `Q`-linearly to `0`. -/
theorem rAtLeastLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant
    (x : ℕ → E) (xStar : E) :
    rAtLeastLinearConvergenceTo x xStar ↔
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQLinearConvergenceTo q 0 := by
  constructor
  · rintro ⟨hxTendsto, hRlt⟩
    obtain ⟨β, hβ0, hRβ, hβ1⟩ : ∃ β : ℝ, 0 < β ∧ R[1] x xStar < β ∧ β < 1 := by
      have hmax : max 0 (R[1] x xStar) < 1 := by
        exact max_lt_iff.mpr ⟨zero_lt_one, hRlt⟩
      obtain ⟨β, hβleft, hβ1⟩ := exists_between hmax
      refine ⟨β, lt_of_le_of_lt (le_max_left _ _) hβleft, ?_, hβ1⟩
      exact lt_of_le_of_lt (le_max_right _ _) hβleft
    have hrootLimsup :
        Filter.limsup
            (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k))
            atTop < β := by
      simpa [rRate_eq_limsup] using hRβ
    have hxNorm :
        Tendsto (fun k : ℕ ↦ ‖x k - xStar‖) atTop (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hxTendsto
      exact hxTendsto
    have hrootBound :
        Filter.IsBoundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k)) := by
      change
        ∃ b : ℝ,
          ∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) ≤ b
      refine ⟨1, ?_⟩
      have hltOne : ∀ᶠ k in atTop, ‖x k - xStar‖ < 1 :=
        hxNorm.eventually (Iio_mem_nhds zero_lt_one)
      filter_upwards [hltOne] with k hk
      exact Real.rpow_le_one (norm_nonneg _) hk.le (rRateExponent_nonneg 1 k)
    have hrootEvent :
        ∀ᶠ k in atTop,
          Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) < β :=
      eventually_lt_of_limsup_lt hrootLimsup hrootBound
    rcases (eventually_atTop.1 hrootEvent) with ⟨N, hN⟩
    let s : ℝ :=
      (Finset.range (N + 1)).sup' (by simp) (fun k ↦ ‖x k - xStar‖ / β ^ (k + 1))
    let C : ℝ := max 1 s
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 s)
    refine ⟨fun k : ℕ ↦ C * β ^ (k + 1), ?_⟩
    refine ⟨?_, scaledGeometric_hasQLinearConvergenceTo_zero hC hβ0 hβ1⟩
    constructor
    · intro k
      positivity
    · intro k
      by_cases hk : k ≤ N
      · have hk_mem : k ∈ Finset.range (N + 1) := by
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
        have hs_le :
            ‖x k - xStar‖ / β ^ (k + 1) ≤ s := by
          simpa [s] using
            (Finset.le_sup' (fun j ↦ ‖x j - xStar‖ / β ^ (j + 1)) hk_mem :
              ‖x k - xStar‖ / β ^ (k + 1) ≤
                (Finset.range (N + 1)).sup' (by simp) (fun j ↦ ‖x j - xStar‖ / β ^ (j + 1)))
        have hβpow_pos : 0 < β ^ (k + 1) := by
          exact pow_pos hβ0 _
        have hsC : s ≤ C := le_max_right 1 s
        calc
          ‖x k - xStar‖
              ≤ s * β ^ (k + 1) := by
                  exact (div_le_iff₀ hβpow_pos).mp hs_le
          _ ≤ C * β ^ (k + 1) := by
                  gcongr
      · have hk_ge : N ≤ k := Nat.le_of_lt (lt_of_not_ge hk)
        have hrootk :
            Real.rpow (‖x k - xStar‖) ((k + 1 : ℝ)⁻¹) < β := by
          simpa [rRateExponent_eq, one_div] using hN k hk_ge
        have hnorm_lt : ‖x k - xStar‖ < β ^ (k + 1 : ℝ) := by
          exact
            (Real.rpow_inv_lt_iff_of_pos (norm_nonneg _) hβ0.le (by positivity)).1 hrootk
        calc
          ‖x k - xStar‖ ≤ β ^ ((k + 1 : ℕ) : ℝ) := by
            simpa [Nat.cast_add] using le_of_lt hnorm_lt
          _ = β ^ (k + 1 : ℕ) := by rw [Real.rpow_natCast]
          _ = 1 * β ^ (k + 1) := by ring
          _ ≤ C * β ^ (k + 1) := by
            gcongr
            exact le_max_left 1 s
  · rintro ⟨q, hqMajorant, hqLinear⟩
    refine ⟨?_, ?_⟩
    · exact
        tendsto_of_isNonnegErrorMajorant_tendsto_zero
          hqMajorant hqLinear.tendsto_zero
    · have hxRate : R[1] x xStar ≤ R[1] q 0 :=
        rRate_le_of_isNonnegErrorMajorant hqMajorant hqLinear.tendsto_zero
      rcases hqMajorant with ⟨hqNonneg, _⟩
      have hqRate : R[1] q 0 < 1 :=
        rRate_one_lt_one_of_nonneg_hasQLinearConvergenceTo hqNonneg hqLinear
      exact lt_of_le_of_lt hxRate hqRate

/-- Exact-owner corollary: strict `R`-linear convergence is the source's broader majorant
reformulation together with the additional positivity clause `0 < R[1] x xStar`. -/
theorem rLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant
    (x : ℕ → E) (xStar : E) :
    rLinearConvergenceTo x xStar ↔
      (0 < R[1] x xStar ∧
        ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQLinearConvergenceTo q 0) := by
  constructor
  · intro hx
    have hAtLeast : rAtLeastLinearConvergenceTo x xStar := ⟨hx.1, hx.2.2⟩
    refine ⟨hx.2.1, ?_⟩
    exact (rAtLeastLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant x xStar).1 hAtLeast
  · rintro ⟨hRpos, hq⟩
    rcases (rAtLeastLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant x xStar).2 hq with
      ⟨hxTendsto, hxlt⟩
    exact ⟨hxTendsto, hRpos, hxlt⟩

@[simp] theorem rLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant_aux
    {x : ℕ → E} {xStar : E} (hRpos : 0 < R[1] x xStar) :
    (0 < R[1] x xStar ∧
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant x xStar q ∧
          HasQLinearConvergenceTo q 0) ↔
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQLinearConvergenceTo q 0 :=
  and_iff_right hRpos

/-- Helper for Chapter01 Definition 1.5-extra-2: a nonnegative scalar sequence that converges
`Q`-quadratically to `0` has second `R`-rate strictly below `1`. -/
private theorem rRate_two_lt_one_of_nonneg_hasQQuadraticConvergenceTo
    {q : ℕ → ℝ} (hqNonneg : ∀ k : ℕ, 0 ≤ q k)
    (hq : HasQQuadraticConvergenceTo q 0) :
    R[2] q 0 < 1 := by
  rcases hq with ⟨β, hβOrder⟩
  rcases hβOrder.hasEventualRpowErrorEstimateTo with ⟨C, hCpos, hEstimate⟩
  let B : ℝ := max 1 C
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hBgeOne : 1 ≤ B := le_max_left 1 C
  have hBgeC : C ≤ B := le_max_right 1 C
  have hScaledTendstoZero : Tendsto (fun k : ℕ ↦ B * q k) atTop (nhds 0) := by
    simpa [B] using (tendsto_const_nhds.mul hβOrder.tendsto)
  have hQuadraticEvent :
      ∀ᶠ k in atTop, q (k + 1) ≤ B * (q k) ^ 2 := by
    filter_upwards [hEstimate] with k hk
    have hk' : q (k + 1) ≤ C * (q k) ^ 2 := by
      simpa [abs_of_nonneg, hqNonneg k, hqNonneg (k + 1), Real.rpow_natCast] using hk
    calc
      q (k + 1) ≤ C * (q k) ^ 2 := hk'
      _ ≤ B * (q k) ^ 2 := by
        gcongr
  have hSmallEvent : ∀ᶠ k in atTop, B * q k < 1 := by
    exact hScaledTendstoZero.eventually (Iio_mem_nhds zero_lt_one)
  rcases (eventually_atTop.1 (hQuadraticEvent.and hSmallEvent)) with ⟨N, hN⟩
  let γ : ℝ := B * q N
  have hγNonneg : 0 ≤ γ := by
    exact mul_nonneg hBpos.le (hqNonneg N)
  have hγLtOne : γ < 1 := by
    simpa [γ] using (hN N le_rfl).2
  have hScaledBound : ∀ m : ℕ, B * q (N + m) ≤ γ ^ (2 ^ m : ℕ) := by
    intro m
    induction m with
    | zero =>
        -- The base case records the chosen small tail value.
        simp [γ]
    | succ m hm =>
        have hstep : q (N + m + 1) ≤ B * (q (N + m)) ^ 2 := by
          simpa [Nat.add_assoc] using (hN (N + m) (Nat.le_add_right N m)).1
        have hscaledStep : B * q (N + m + 1) ≤ (B * q (N + m)) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hstep hBpos.le
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
        calc
          B * q (N + (m + 1)) = B * q (N + m + 1) := by simp [Nat.add_assoc]
          _ ≤ (B * q (N + m)) ^ 2 := hscaledStep
          _ ≤ (γ ^ (2 ^ m : ℕ)) ^ 2 := by
                exact pow_le_pow_left₀ (mul_nonneg hBpos.le (hqNonneg (N + m))) hm 2
          _ = γ ^ (2 ^ (m + 1) : ℕ) := by
                rw [show 2 ^ (m + 1 : ℕ) = 2 ^ m * 2 by rw [pow_succ']; ring, pow_mul]
  have hGeomBound : ∀ m : ℕ, q (N + m) ≤ γ ^ (2 ^ m : ℕ) := by
    intro m
    have hscale := hScaledBound m
    have hle : q (N + m) ≤ B * q (N + m) := by
      nlinarith [hqNonneg (N + m), hBgeOne]
    exact le_trans hle hscale
  let δ : ℝ := Real.rpow γ (((2 : ℝ) ^ (N + 1 : ℕ))⁻¹)
  have hδLtOne : δ < 1 := by
    have hExpPos : 0 < (((2 : ℝ) ^ (N + 1 : ℕ))⁻¹) := by positivity
    exact Real.rpow_lt_one hγNonneg hγLtOne hExpPos
  have hRootLeEvent :
      ∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 2 n) ≤ δ := by
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hNn : N ≤ n := hn
    have hqGeom : q n ≤ γ ^ (2 ^ (n - N) : ℕ) := by
      rw [show n = N + (n - N) by exact (Nat.add_sub_of_le hNn).symm]
      simpa [Nat.add_sub_of_le hNn] using hGeomBound (n - N)
    have hRootLe :
        Real.rpow (q n) (rRateExponent 2 n) ≤
          Real.rpow (γ ^ (2 ^ (n - N) : ℕ)) (rRateExponent 2 n) := by
      exact Real.rpow_le_rpow (hqNonneg n) hqGeom (rRateExponent_nonneg 2 n)
    have hRootEq :
        Real.rpow (γ ^ (2 ^ (n - N) : ℕ)) (rRateExponent 2 n) = δ := by
      have hr2 : rRateExponent 2 n = (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹) := by
        simp [rRateExponent_eq]
      rw [hr2]
      calc
        Real.rpow (γ ^ (2 ^ (n - N) : ℕ)) (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹)
            = Real.rpow γ (((2 ^ (n - N) : ℕ) : ℝ) * (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹)) := by
                rw [show γ ^ (2 ^ (n - N) : ℕ) = Real.rpow γ (((2 ^ (n - N) : ℕ) : ℝ)) by
                  simpa using (Real.rpow_natCast γ (2 ^ (n - N : ℕ))).symm]
                symm
                exact
                  Real.rpow_mul hγNonneg (((2 ^ (n - N) : ℕ) : ℝ))
                    (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹)
        _ = Real.rpow γ (((2 : ℝ) ^ (N + 1 : ℕ))⁻¹) := by
              congr 2
              have hsum : N + 1 + (n - N) = n + 1 := by
                omega
              have hpowEq :
                  (2 : ℝ) ^ (n + 1 : ℕ) =
                    (2 : ℝ) ^ (N + 1 : ℕ) * (2 : ℝ) ^ (n - N : ℕ) := by
                rw [← pow_add, hsum]
              have hpowNNe : (2 : ℝ) ^ (N + 1 : ℕ) ≠ 0 := by positivity
              have hpowTailNe : (2 : ℝ) ^ (n - N : ℕ) ≠ 0 := by positivity
              calc
                (((2 ^ (n - N) : ℕ) : ℝ) : ℝ) * (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹)
                    = (2 : ℝ) ^ (n - N : ℕ) * (((2 : ℝ) ^ (n + 1 : ℕ))⁻¹) := by simp
                _ = (2 : ℝ) ^ (n - N : ℕ) *
                      (((2 : ℝ) ^ (N + 1 : ℕ) * (2 : ℝ) ^ (n - N : ℕ))⁻¹) := by
                      rw [hpowEq]
                _ = (((2 : ℝ) ^ (N + 1 : ℕ))⁻¹) := by
                      field_simp [hpowNNe, hpowTailNe]
        _ = δ := by rfl
    simpa [rRateExponent_eq, abs_of_nonneg (hqNonneg n)] using hRootLe.trans_eq hRootEq
  have hRateLe : R[2] q 0 ≤ δ := by
    rw [rRate_eq_limsup]
    have hCobounded :
        Filter.IsCoboundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 2 n)) := by
      change
        ∃ b : ℝ,
          ∀ a : ℝ,
            (∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 2 n) ≤ a) → b ≤ a
      refine ⟨0, ?_⟩
      intro a ha
      rcases ha.exists with ⟨n, hn⟩
      exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) hn
    have hBounded :
        Filter.IsBoundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 2 n)) := ⟨δ, hRootLeEvent⟩
    exact (limsup_le_iff hCobounded hBounded).2 fun y hy ↦ by
      filter_upwards [hRootLeEvent] with n hn
      exact lt_of_le_of_lt hn hy
  exact lt_of_le_of_lt hRateLe hδLtOne

/-- Helper for Chapter01 Definition 1.5-extra-2: along a convergent sequence, the textbook
`R`-rate is nonnegative because the defining root sequence is eventually bounded above and
pointwise nonnegative. -/
private theorem rRate_nonneg_of_tendsto
    {x : ℕ → E} {xStar : E} (p : RRateOrder)
    (hxTendsto : Tendsto x atTop (nhds xStar)) :
    0 ≤ R[p] x xStar := by
  have hxNorm :
      Tendsto (fun k : ℕ ↦ ‖x k - xStar‖) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hxTendsto
    exact hxTendsto
  have hrootBound :
      Filter.IsBoundedUnder
        (fun a b : ℝ ↦ a ≤ b)
        atTop
        (fun k : ℕ ↦ Real.rpow (‖x k - xStar‖) (rRateExponent p k)) := by
    change
      ∃ b : ℝ,
        ∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent p k) ≤ b
    refine ⟨1, ?_⟩
    have hltOne : ∀ᶠ k in atTop, ‖x k - xStar‖ < 1 :=
      hxNorm.eventually (Iio_mem_nhds zero_lt_one)
    filter_upwards [hltOne] with k hk
    exact Real.rpow_le_one (norm_nonneg _) hk.le (rRateExponent_nonneg p k)
  -- Rewrite to the defining limsup and use the pointwise nonnegativity of the root terms.
  rw [rRate_eq_limsup]
  refine le_limsup_of_le hrootBound ?_
  · intro a ha
    rcases ha.exists with ⟨n, hn⟩
    exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) hn

/-- Helper for Chapter01 Definition 1.5-extra-2: if `R[1] x xStar = 0`, then the root-error
sequence used in the textbook limsup formula tends to `0`. -/
private theorem rootErrorRpow_tendsto_zero_of_rRate_one_eq_zero
    {x : ℕ → E} {xStar : E}
    (hxTendsto : Tendsto x atTop (nhds xStar))
    (hR0 : R[1] x xStar = 0) :
    Tendsto (fun k : ℕ ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k)) atTop (nhds 0) := by
  have hxNorm :
      Tendsto (fun k : ℕ ↦ ‖x k - xStar‖) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hxTendsto
    exact hxTendsto
  have hrootBound :
      Filter.IsBoundedUnder
        (fun a b : ℝ ↦ a ≤ b)
        atTop
        (fun k : ℕ ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k)) := by
    change
      ∃ b : ℝ,
        ∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) ≤ b
    refine ⟨1, ?_⟩
    have hltOne : ∀ᶠ k in atTop, ‖x k - xStar‖ < 1 :=
      hxNorm.eventually (Iio_mem_nhds zero_lt_one)
    filter_upwards [hltOne] with k hk
    exact Real.rpow_le_one (norm_nonneg _) hk.le (rRateExponent_nonneg 1 k)
  -- Convert `R[1] = 0` into eventual smallness of the root-error sequence.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hrootEvent :
      ∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) < ε := by
    have hlimsup : R[1] x xStar < ε := by simpa [hR0] using hε
    exact eventually_lt_of_limsup_lt (by simpa [rRate_eq_limsup] using hlimsup) hrootBound
  rcases (eventually_atTop.1 hrootEvent) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  have hrootk : Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) < ε := hN k hk
  have hnonneg : 0 ≤ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k) :=
    Real.rpow_nonneg (norm_nonneg _) _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hrootk

/-- Helper for Chapter01 Definition 1.5-extra-2: a nonnegative scalar sequence with
denominator-safe first-order `Q`-ratio converging to `0` has first `R`-rate equal to `0`. -/
private theorem rRate_one_eq_zero_of_nonneg_hasQRatioConvergenceTo_zero
    {q : ℕ → ℝ} (hqNonneg : ∀ k : ℕ, 0 ≤ q k)
    (hq : HasQRatioConvergenceTo q 0 1 0) :
    R[1] q 0 = 0 := by
  have hRateUpper : ∀ η : ℝ, 0 < η → R[1] q 0 ≤ η := by
    intro η hη
    obtain ⟨γ, hγpos, hγη, hγ1⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < η ∧ γ < 1 := by
      refine ⟨min (η / 2) (1 / 2), ?_, ?_, ?_⟩
      · positivity
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let δ : ℝ := γ * ((2 : ℝ)⁻¹)
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδltγ : δ < γ := by
      dsimp [δ]
      nlinarith
    have hratioEvent :
        ∀ᶠ k in atTop, qErrorRatio q 0 1 k < δ :=
      hq.ratio_tendsto.eventually (Iio_mem_nhds hδpos)
    have hnonzeroEvent : ∀ᶠ k in atTop, q k ≠ 0 := hq.eventually_ne
    rcases (eventually_atTop.1 (hratioEvent.and hnonzeroEvent)) with ⟨N, hN⟩
    have hgeom : ∀ m : ℕ, q (N + m) ≤ q N * δ ^ m := by
      intro m
      induction m with
      | zero =>
          simp
      | succ m hm =>
          rcases hN (N + m) (Nat.le_add_right N m) with ⟨hkRatio, hkNe⟩
          have hkPos : 0 < q (N + m) := lt_of_le_of_ne (hqNonneg _) (Ne.symm hkNe)
          have hstep : q (N + m + 1) ≤ δ * q (N + m) := by
            have hkRatio' :
                q (N + m + 1) / q (N + m) < δ := by
              simpa [qErrorRatio_apply, abs_of_nonneg, hqNonneg (N + m), hqNonneg (N + m + 1)]
                using hkRatio
            exact (div_lt_iff₀ hkPos).1 hkRatio' |>.le
          calc
            q (N + (m + 1)) = q (N + m + 1) := by simp [Nat.add_assoc]
            _ ≤ δ * q (N + m) := hstep
            _ ≤ δ * (q N * δ ^ m) := by
                  gcongr
            _ = q N * δ ^ (m + 1) := by
                  calc
                    δ * (q N * δ ^ m) = q N * (δ * δ ^ m) := by ring
                    _ = q N * δ ^ (m + 1) := by rw [← pow_succ']
    have hhalfTendsto : Tendsto (fun m : ℕ ↦ q N * ((2 : ℝ)⁻¹) ^ m) atTop (nhds 0) := by
      have hpow : Tendsto (fun m : ℕ ↦ ((2 : ℝ)⁻¹) ^ m) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
      simpa using hpow.const_mul (q N)
    have hgammaPowPos : 0 < γ ^ (N + 1) := by positivity
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hhalfTendsto (γ ^ (N + 1)) hgammaPowPos
    have hRootLeEvent :
        ∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 1 n) ≤ γ := by
      refine eventually_atTop.2 ⟨N + M, ?_⟩
      intro n hn
      have hNn : N ≤ n := le_trans (Nat.le_add_right N M) hn
      have hMn : M ≤ n - N := by
        have hsum : M + N ≤ n := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
        exact (Nat.le_sub_iff_add_le hNn).2 hsum
      have hqHalf : q N * ((2 : ℝ)⁻¹) ^ (n - N) ≤ γ ^ (N + 1) := by
        have hdist : dist (q N * ((2 : ℝ)⁻¹) ^ (n - N)) 0 < γ ^ (N + 1) := hM (n - N) hMn
        have hnonneg :
            0 ≤ q N * ((2 : ℝ)⁻¹) ^ (n - N) := by
          exact mul_nonneg (hqNonneg N) (by positivity)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hdist
        exact hdist.le
      have hqBound : q n ≤ γ ^ (n + 1 : ℕ) := by
        calc
          q n = q (N + (n - N)) := by rw [Nat.add_sub_of_le hNn]
          _ ≤ q N * δ ^ (n - N) := hgeom (n - N)
          _ = (q N * ((2 : ℝ)⁻¹) ^ (n - N)) * γ ^ (n - N) := by
                dsimp [δ]
                rw [mul_pow]
                ring
          _ ≤ γ ^ (N + 1) * γ ^ (n - N) := by gcongr
          _ = γ ^ (n + 1 : ℕ) := by
                have hsum : N + 1 + (n - N) = n + 1 := by omega
                rw [← pow_add, hsum]
      have hpowEq : γ ^ ((n : ℝ) + 1) = γ ^ (n + 1 : ℕ) := by
        rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast]
      have hrootLe :
          Real.rpow (q n) ((n + 1 : ℝ)⁻¹) ≤ γ := by
        exact
          (Real.rpow_inv_le_iff_of_pos (hqNonneg n) hγpos.le (by positivity)).2
            (by simpa [hpowEq] using hqBound)
      simpa [rRateExponent_eq, one_div, abs_of_nonneg (hqNonneg n)] using hrootLe
    have hRateLe : R[1] q 0 ≤ γ := by
      rw [rRate_eq_limsup]
      have hCobounded :
          Filter.IsCoboundedUnder
            (fun a b : ℝ ↦ a ≤ b)
            atTop
            (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 1 n)) := by
        change
          ∃ b : ℝ,
            ∀ a : ℝ,
              (∀ᶠ n in atTop, Real.rpow (‖q n - 0‖) (rRateExponent 1 n) ≤ a) → b ≤ a
        refine ⟨0, ?_⟩
        intro a ha
        rcases ha.exists with ⟨n, hn⟩
        exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) hn
      have hBounded :
          Filter.IsBoundedUnder
            (fun a b : ℝ ↦ a ≤ b)
            atTop
            (fun n ↦ Real.rpow (‖q n - 0‖) (rRateExponent 1 n)) := ⟨γ, hRootLeEvent⟩
      refine (limsup_le_iff hCobounded hBounded).2 ?_
      intro y hy
      filter_upwards [hRootLeEvent] with n hn
      exact lt_of_le_of_lt hn hy
    exact le_trans hRateLe hγη.le
  have hRateLeZero : R[1] q 0 ≤ 0 := by
    by_contra hpos
    have hRatePos : 0 < R[1] q 0 := lt_of_not_ge hpos
    have hRateSmall := hRateUpper (R[1] q 0 / 2) (by linarith)
    linarith
  exact le_antisymm hRateLeZero (rRate_nonneg_of_tendsto 1 hq.tendsto)

/-- Chapter01 Definition 1.5-extra-2 (2): `R`-superlinear convergence is equivalently described
by a
nonnegative scalar majorant sequence whose first-order `Q`-ratio converges to `0`
through the denominator-safe bridge owner. -/
theorem rSuperlinearConvergenceTo_iff_exists_nonneg_qSuperlinearMajorant
    (x : ℕ → E) (xStar : E) :
    rSuperlinearConvergenceTo x xStar ↔
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQRatioConvergenceTo q 0 1 0 := by
  constructor
  · rintro ⟨hxTendsto, hR0⟩
    let root : ℕ → ℝ := fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 1 k)
    have hrootTendsto : Tendsto root atTop (nhds 0) := by
      -- The forward direction starts by converting `R[1] = 0` into vanishing root errors.
      simpa [root] using rootErrorRpow_tendsto_zero_of_rRate_one_eq_zero hxTendsto hR0
    have hgeomTendsto :
        Tendsto (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (k + 1)) atTop (nhds 0) := by
      have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
      simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hpow.const_mul ((2 : ℝ)⁻¹)
    let g : ℕ → ℝ := fun k ↦ max (root k) (((2 : ℝ)⁻¹) ^ (k + 1))
    have hgTendsto : Tendsto g atTop (nhds 0) := by
      -- Add a geometric floor so the later majorant stays strictly positive.
      simpa [g] using hrootTendsto.max hgeomTendsto
    have hgNonneg : ∀ k : ℕ, 0 ≤ g k := by
      intro k
      exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) (le_max_left _ _)
    have hgLtOne : ∀ᶠ k in atTop, g k < 1 := by
      exact hgTendsto.eventually (Iio_mem_nhds zero_lt_one)
    rcases (eventually_atTop.1 hgLtOne) with ⟨N, hN⟩
    let B : ℝ := max 1 ((Finset.range (N + 1)).sup' (by simp) g)
    have hBge : ∀ n : ℕ, g n ≤ B := by
      intro n
      by_cases hn : n ≤ N
      · have hn_mem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
        have hsup :
            g n ≤ (Finset.range (N + 1)).sup' (by simp) g := by
          exact Finset.le_sup' g hn_mem
        exact le_trans hsup (le_max_right 1 _)
      · have hNn : N ≤ n := Nat.le_of_lt (lt_of_not_ge hn)
        exact le_trans (le_of_lt (hN n hNn)) (le_max_left 1 _)
    let b : ℕ → ℝ := fun k ↦ sSup (g '' Set.Ici k)
    have hbBdd : ∀ k : ℕ, BddAbove (g '' Set.Ici k) := by
      intro k
      refine ⟨B, ?_⟩
      intro y hy
      rcases hy with ⟨n, hn, rfl⟩
      exact hBge n
    have hbNonempty : ∀ k : ℕ, (g '' Set.Ici k).Nonempty := by
      intro k
      exact ⟨g k, ⟨k, (by simp : k ∈ Set.Ici k), rfl⟩⟩
    have hb_ge : ∀ {k n : ℕ}, k ≤ n → g n ≤ b k := by
      intro k n hkn
      exact le_csSup (hbBdd k) ⟨n, hkn, rfl⟩
    have hb_mono : Antitone b := by
      intro k l hkl
      have hsubset : g '' Set.Ici l ⊆ g '' Set.Ici k := by
        intro y hy
        rcases hy with ⟨n, hn, rfl⟩
        exact ⟨n, le_trans hkl hn, rfl⟩
      refine csSup_le (hbNonempty l) ?_
      intro y hy
      exact le_csSup (hbBdd k) (hsubset hy)
    have hb_pos : ∀ k : ℕ, 0 < b k := by
      intro k
      have hfloor_le_g : ((2 : ℝ)⁻¹) ^ (k + 1) ≤ g k := by
        exact le_max_right _ _
      have hfloor_le_b : ((2 : ℝ)⁻¹) ^ (k + 1) ≤ b k := le_trans hfloor_le_g (hb_ge le_rfl)
      exact lt_of_lt_of_le (by positivity) hfloor_le_b
    have hbTendsto : Tendsto b atTop (nhds 0) := by
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      have hhalf : 0 < ε / 2 := by linarith
      have hgHalf : ∀ᶠ k in atTop, g k < ε / 2 :=
        hgTendsto.eventually (Iio_mem_nhds hhalf)
      rcases (eventually_atTop.1 hgHalf) with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro n hn
      have hb_le_half : b n ≤ ε / 2 := by
        refine csSup_le (hbNonempty n) ?_
        intro y hy
        rcases hy with ⟨m, hm, rfl⟩
        exact (hM m (le_trans hn hm)).le
      have hb_nonneg : 0 ≤ b n := le_of_lt (hb_pos n)
      have hb_lt : b n < ε := lt_of_le_of_lt hb_le_half (by linarith)
      simpa [Real.dist_eq, abs_of_nonneg hb_nonneg] using hb_lt
    let q : ℕ → ℝ := fun k ↦ b k ^ (k + 1)
    have hqMajorant : IsNonnegErrorMajorant x xStar q := by
      constructor
      · intro k
        exact pow_nonneg (le_of_lt (hb_pos k)) _
      · intro k
        -- Convert the tail-envelope bound on the root sequence back to the original error norm.
        have hroot_le_b : root k ≤ b k := by
          exact le_trans (le_max_left _ _) (hb_ge le_rfl)
        have hnorm_le :
            ‖x k - xStar‖ ≤ b k ^ ((k + 1 : ℝ)) := by
          have hroot_le_b' : Real.rpow (‖x k - xStar‖) ((k + 1 : ℝ)⁻¹) ≤ b k := by
            simpa [root, rRateExponent_eq, one_div] using hroot_le_b
          exact
            (Real.rpow_inv_le_iff_of_pos
              (norm_nonneg _) (le_of_lt (hb_pos k)) (by positivity)).1 hroot_le_b'
        calc
          ‖x k - xStar‖ ≤ b k ^ (((k + 1 : ℕ) : ℝ)) := by
                simpa [Nat.cast_add] using hnorm_le
          _ = b k ^ (k + 1 : ℕ) := by rw [Real.rpow_natCast]
          _ = q k := by rfl
    have hqTendsto : Tendsto q atTop (nhds 0) := by
      have hbLtOne : ∀ᶠ k in atTop, b k < 1 :=
        hbTendsto.eventually (Iio_mem_nhds zero_lt_one)
      have hqLe :
          ∀ᶠ k in atTop, q k ≤ b k := by
        filter_upwards [hbLtOne] with k hk
        have hb_nonneg : 0 ≤ b k := le_of_lt (hb_pos k)
        have hpow :
            b k ^ (((k + 1 : ℕ) : ℝ)) ≤ b k := by
          simpa [Nat.cast_add] using
            (Real.rpow_le_self_of_le_one hb_nonneg hk.le
              (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))))
        calc
          q k = b k ^ (k + 1 : ℕ) := by rfl
          _ = b k ^ (((k + 1 : ℕ) : ℝ)) := by rw [← Real.rpow_natCast]
          _ ≤ b k := hpow
      exact
        squeeze_zero'
          (Eventually.of_forall fun k ↦ pow_nonneg (le_of_lt (hb_pos k)) _)
          hqLe hbTendsto
    have hqEventuallyNe : ∀ᶠ k in atTop, q k ≠ 0 := by
      exact Eventually.of_forall fun k ↦ by
        exact (pow_pos (hb_pos k) _).ne'
    have hqRatioLe : ∀ k : ℕ, qErrorRatio q 0 1 k ≤ b (k + 1) := by
      intro k
      have hb_nonneg : 0 ≤ b k := le_of_lt (hb_pos k)
      have hb_succ_nonneg : 0 ≤ b (k + 1) := le_of_lt (hb_pos (k + 1))
      have hq_nonneg : 0 ≤ q k := by positivity
      have hq_succ_nonneg : 0 ≤ q (k + 1) := by positivity
      have hmono : b (k + 1) ≤ b k := hb_mono (Nat.le_succ k)
      have hpow_le :
          b (k + 1) ^ (k + 1) ≤ b k ^ (k + 1) := by
        exact pow_le_pow_left₀ hb_succ_nonneg hmono (k + 1)
      have hnum_le :
          b (k + 1) ^ (k + 2) ≤ b (k + 1) * b k ^ (k + 1) := by
        calc
          b (k + 1) ^ (k + 2) = b (k + 1) * b (k + 1) ^ (k + 1) := by rw [pow_succ']
          _ ≤ b (k + 1) * b k ^ (k + 1) := by
                gcongr
      have hden_pos : 0 < b k ^ (k + 1) := pow_pos (hb_pos k) _
      have hratioEq : qErrorRatio q 0 1 k = q (k + 1) / q k := by
        rw [qErrorRatio_apply]
        have hqk_nonneg : 0 ≤ q k := pow_nonneg (le_of_lt (hb_pos k)) _
        have hqk1_nonneg : 0 ≤ q (k + 1) := pow_nonneg (le_of_lt (hb_pos (k + 1))) _
        simp [abs_of_nonneg hqk_nonneg, abs_of_nonneg hqk1_nonneg]
      calc
        qErrorRatio q 0 1 k = b (k + 1) ^ (k + 2) / b k ^ (k + 1) := by
          simpa [q] using hratioEq
        _ ≤ b (k + 1) := by
          exact
            (div_le_iff₀ hden_pos).2 <|
              by
                simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hnum_le
    have hqRatioTendsto : Tendsto (qErrorRatio q 0 1) atTop (nhds 0) := by
      have hbShift : Tendsto (fun k : ℕ ↦ b (k + 1)) atTop (nhds 0) :=
        hbTendsto.comp (Filter.tendsto_add_atTop_nat 1)
      have hratioNonneg :
          ∀ᶠ k in atTop, 0 ≤ qErrorRatio q 0 1 k := by
        exact Eventually.of_forall fun k ↦ by
          rw [qErrorRatio_apply]
          exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      exact squeeze_zero' hratioNonneg (Eventually.of_forall hqRatioLe) hbShift
    refine ⟨q, hqMajorant, ?_⟩
    exact
      { tendsto := hqTendsto
        eventually_ne := hqEventuallyNe
        ratio_tendsto := hqRatioTendsto }
  · rintro ⟨q, hqMajorant, hqRatio⟩
    refine ⟨?_, ?_⟩
    · exact tendsto_of_isNonnegErrorMajorant_tendsto_zero hqMajorant hqRatio.tendsto
    · have hxTendsto : Tendsto x atTop (nhds xStar) :=
          tendsto_of_isNonnegErrorMajorant_tendsto_zero hqMajorant hqRatio.tendsto
      have hqNonneg : ∀ k : ℕ, 0 ≤ q k := hqMajorant.1
      have hxRate : R[1] x xStar ≤ R[1] q 0 :=
        rRate_le_of_isNonnegErrorMajorant hqMajorant hqRatio.tendsto
      have hqRate : R[1] q 0 = 0 :=
        rRate_one_eq_zero_of_nonneg_hasQRatioConvergenceTo_zero hqNonneg hqRatio
      have hxRateLeZero : R[1] x xStar ≤ 0 := by simpa [hqRate] using hxRate
      exact le_antisymm hxRateLeZero (rRate_nonneg_of_tendsto 1 hxTendsto)

/-- A quadratic companion to Chapter01 Definition 1.5-extra-2: the sequence `x` is
`R`-quadratically convergent in
the source's broader reformulation precisely when there is a nonnegative scalar majorant
sequence converging `Q`-quadratically to `0`. -/
theorem rAtLeastQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant
    (x : ℕ → E) (xStar : E) :
    rAtLeastQuadraticConvergenceTo x xStar ↔
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQQuadraticConvergenceTo q 0 := by
  constructor
  · rintro ⟨hxTendsto, hRlt⟩
    obtain ⟨β, hβ0, hRβ, hβ1⟩ : ∃ β : ℝ, 0 < β ∧ R[2] x xStar < β ∧ β < 1 := by
      have hmax : max 0 (R[2] x xStar) < 1 := by
        exact max_lt_iff.mpr ⟨zero_lt_one, hRlt⟩
      obtain ⟨β, hβleft, hβ1⟩ := exists_between hmax
      refine ⟨β, lt_of_le_of_lt (le_max_left _ _) hβleft, ?_, hβ1⟩
      exact lt_of_le_of_lt (le_max_right _ _) hβleft
    have hrootLimsup :
        Filter.limsup
            (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 2 k))
            atTop < β := by
      simpa [rRate_eq_limsup] using hRβ
    have hxNorm :
        Tendsto (fun k : ℕ ↦ ‖x k - xStar‖) atTop (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hxTendsto
      exact hxTendsto
    have hrootBound :
        Filter.IsBoundedUnder
          (fun a b : ℝ ↦ a ≤ b)
          atTop
          (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent 2 k)) := by
      change
        ∃ b : ℝ,
          ∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent 2 k) ≤ b
      refine ⟨1, ?_⟩
      have hltOne : ∀ᶠ k in atTop, ‖x k - xStar‖ < 1 :=
        hxNorm.eventually (Iio_mem_nhds zero_lt_one)
      filter_upwards [hltOne] with k hk
      exact Real.rpow_le_one (norm_nonneg _) hk.le (rRateExponent_nonneg 2 k)
    have hrootEvent :
        ∀ᶠ k in atTop,
          Real.rpow (‖x k - xStar‖) (rRateExponent 2 k) < β :=
      eventually_lt_of_limsup_lt hrootLimsup hrootBound
    rcases (eventually_atTop.1 hrootEvent) with ⟨N, hN⟩
    let s : ℝ :=
      (Finset.range (N + 1)).sup' (by simp) (fun k ↦ ‖x k - xStar‖ / β ^ (2 ^ (k + 1 : ℕ)))
    let C : ℝ := max 1 s
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 s)
    refine ⟨fun k : ℕ ↦ C * β ^ (2 ^ (k + 1 : ℕ)), ?_⟩
    refine ⟨?_, scaledDyadicGeometric_hasQQuadraticConvergenceTo_zero hC hβ0 hβ1⟩
    constructor
    · intro k
      positivity
    · intro k
      by_cases hk : k ≤ N
      · have hk_mem : k ∈ Finset.range (N + 1) := by
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
        have hs_le :
            ‖x k - xStar‖ / β ^ (2 ^ (k + 1 : ℕ)) ≤ s := by
          simpa [s] using
            (Finset.le_sup' (fun j ↦ ‖x j - xStar‖ / β ^ (2 ^ (j + 1 : ℕ))) hk_mem :
              ‖x k - xStar‖ / β ^ (2 ^ (k + 1 : ℕ)) ≤
                (Finset.range (N + 1)).sup' (by simp)
                  (fun j ↦ ‖x j - xStar‖ / β ^ (2 ^ (j + 1 : ℕ))))
        have hβpow_pos : 0 < β ^ (2 ^ (k + 1 : ℕ)) := by
          exact pow_pos hβ0 _
        have hsC : s ≤ C := le_max_right 1 s
        calc
          ‖x k - xStar‖ ≤ s * β ^ (2 ^ (k + 1 : ℕ)) := by
            exact (div_le_iff₀ hβpow_pos).mp hs_le
          _ ≤ C * β ^ (2 ^ (k + 1 : ℕ)) := by
            gcongr
      · have hk_ge : N ≤ k := Nat.le_of_lt (lt_of_not_ge hk)
        have hrootk :
            Real.rpow (‖x k - xStar‖) (((2 : ℝ) ^ (k + 1 : ℕ))⁻¹) < β := by
          simpa [rRateExponent_eq] using hN k hk_ge
        have hnorm_lt : ‖x k - xStar‖ < β ^ (2 ^ (k + 1 : ℕ) : ℝ) := by
          exact
            (Real.rpow_inv_lt_iff_of_pos (norm_nonneg _) hβ0.le (by positivity)).1 hrootk
        calc
          ‖x k - xStar‖ ≤ β ^ ((2 ^ (k + 1 : ℕ) : ℕ) : ℝ) := by
            simpa using le_of_lt hnorm_lt
          _ = β ^ (2 ^ (k + 1 : ℕ)) := by rw [Real.rpow_natCast]
          _ = 1 * β ^ (2 ^ (k + 1 : ℕ)) := by ring
          _ ≤ C * β ^ (2 ^ (k + 1 : ℕ)) := by
            gcongr
            exact le_max_left 1 s
  · rintro ⟨q, hqMajorant, hqQuadratic⟩
    refine ⟨?_, ?_⟩
    · exact
        tendsto_of_isNonnegErrorMajorant_tendsto_zero
          hqMajorant hqQuadratic.tendsto_zero
    · have hxRate : R[2] x xStar ≤ R[2] q 0 :=
        rRate_le_of_isNonnegErrorMajorant hqMajorant hqQuadratic.tendsto_zero
      rcases hqMajorant with ⟨hqNonneg, _⟩
      have hqRate : R[2] q 0 < 1 :=
        rRate_two_lt_one_of_nonneg_hasQQuadraticConvergenceTo hqNonneg hqQuadratic
      exact lt_of_le_of_lt hxRate hqRate

/-- Exact-owner corollary: strict `R`-quadratic convergence is the source's broader majorant
reformulation together with the additional positivity clause `0 < R[2] x xStar`. -/
theorem rQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant
    (x : ℕ → E) (xStar : E) :
    rQuadraticConvergenceTo x xStar ↔
      (0 < R[2] x xStar ∧
        ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQQuadraticConvergenceTo q 0) := by
  constructor
  · intro hx
    have hAtLeast : rAtLeastQuadraticConvergenceTo x xStar := ⟨hx.1, hx.2.2⟩
    refine ⟨hx.2.1, ?_⟩
    exact (rAtLeastQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant x xStar).1 hAtLeast
  · rintro ⟨hRpos, hq⟩
    rcases (rAtLeastQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant x xStar).2 hq with
      ⟨hxTendsto, hxlt⟩
    exact ⟨hxTendsto, hRpos, hxlt⟩

@[simp] theorem rQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant_aux
    {x : ℕ → E} {xStar : E} (hRpos : 0 < R[2] x xStar) :
    (0 < R[2] x xStar ∧
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant x xStar q ∧
          HasQQuadraticConvergenceTo q 0) ↔
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQQuadraticConvergenceTo q 0 :=
  and_iff_right hRpos

/-- Helper: the constant sequence at `xStar` has first `R`-rate equal to `0`. -/
private theorem rRate_one_const_eq_zero (xStar : E) :
    R[(1 : RRateOrder)] (fun _ : ℕ ↦ xStar) xStar = 0 := by
  -- Rewrite the limsup sequence pointwise to the constant zero sequence.
  rw [rRate_eq_limsup]
  have hzero :
      (fun k : ℕ ↦
        Real.rpow (‖(fun _ : ℕ ↦ xStar) k - xStar‖) (rRateExponent 1 k)) =
        fun _ : ℕ ↦ (0 : ℝ) := by
    funext k
    have hk : ((k : ℝ) + 1)⁻¹ ≠ 0 := by
      apply inv_ne_zero
      positivity
    simp [rRateExponent_eq, Real.zero_rpow, hk]
  rw [hzero]
  simp

/-- Helper: the constant sequence at `xStar` has second `R`-rate equal to `0`. -/
private theorem rRate_two_const_eq_zero (xStar : E) :
    R[(2 : RRateOrder)] (fun _ : ℕ ↦ xStar) xStar = 0 := by
  -- Rewrite the limsup sequence pointwise to the constant zero sequence.
  rw [rRate_eq_limsup]
  have hzero :
      (fun k : ℕ ↦
        Real.rpow (‖(fun _ : ℕ ↦ xStar) k - xStar‖) (rRateExponent 2 k)) =
        fun _ : ℕ ↦ (0 : ℝ) := by
    funext k
    have hk : ((2 : ℝ) ^ (k + 1 : ℕ))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      positivity
    simp [rRateExponent_eq, Real.zero_rpow, hk]
  rw [hzero]
  simp

/-- Helper: the geometric sequence `k ↦ (2⁻¹)^(k+1)` is `Q`-linearly convergent to `0`. -/
private theorem geometricHalf_hasQLinearConvergenceTo_zero :
    HasQLinearConvergenceTo (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (k + 1)) 0 := by
  refine ⟨(2 : ℝ)⁻¹, by norm_num, ?_⟩
  refine
    { one_le := by norm_num
      beta_pos := by norm_num
      tendsto := ?_
      ratio_tendsto := ?_ }
  · -- The geometric sequence tends to `0`.
    have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hpow.const_mul ((2 : ℝ)⁻¹)
  · -- Its first-order `Q`-ratio is the constant value `2⁻¹`.
    have hratio :
        qErrorRatio (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (k + 1)) 0 1 =
          fun _ : ℕ ↦ ((2 : ℝ)⁻¹) := by
      funext k
      have hkpow : ((2 : ℝ)⁻¹) ^ (k + 1) ≠ 0 := by
        positivity
      calc
        qErrorRatio (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (k + 1)) 0 1 k
            = (((2 : ℝ)⁻¹) ^ (k + 2)) / (((2 : ℝ)⁻¹) ^ (k + 1)) := by
                rw [qErrorRatio_apply]
                simp
        _ = ((2 : ℝ)⁻¹) := by
          rw [pow_succ']
          field_simp [hkpow]
    rw [hratio]
    simp

/-- Helper: the dyadic-geometric sequence `k ↦ (2⁻¹)^(2^(k+1))` is `Q`-quadratically
convergent to `0`. -/
private theorem dyadicGeometricHalf_hasQQuadraticConvergenceTo_zero :
    HasQQuadraticConvergenceTo (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ))) 0 := by
  refine ⟨1, ?_⟩
  refine
    { one_le := by norm_num
      beta_pos := by norm_num
      tendsto := ?_
      ratio_tendsto := ?_ }
  · -- Compose the geometric decay `((2 : ℝ)⁻¹)^n → 0` with the diverging dyadic exponent.
    have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hexp : Tendsto (fun n : ℕ ↦ 2 ^ (n + 1 : ℕ)) atTop atTop := by
      exact
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
          (Filter.tendsto_add_atTop_nat 1)
    convert hpow.comp hexp using 1
    ext n
    simp
  · -- The second-order `Q`-ratio is constantly `1`.
    have hratio :
        qErrorRatio (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ))) 0 2 =
          fun _ : ℕ ↦ (1 : ℝ) := by
      funext k
      have hkpow : ((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ)) ≠ 0 := by
        positivity
      calc
        qErrorRatio (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ))) 0 2 k
            = (((2 : ℝ)⁻¹) ^ (2 ^ (k + 2 : ℕ))) /
                ((((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ))) ^ 2) := by
                  rw [qErrorRatio_apply]
                  simp
        _ = (1 : ℝ) := by
          rw [show 2 ^ (k + 2 : ℕ) = 2 ^ (k + 1 : ℕ) * 2 by
            rw [pow_succ']
            ring]
          rw [pow_mul]
          field_simp [hkpow]
    rw [hratio]
    simp

/-- The textbook exact `R`-linear reformulation is false as written on the constant
sequence `fun _ ↦ xStar`. -/
private theorem exactRLinearMajorantCharacterizationFalse
    (xStar : E) :
    ¬ (rLinearConvergenceTo (fun _ ↦ xStar) xStar ↔
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant (fun _ ↦ xStar) xStar q ∧
          HasQLinearConvergenceTo q 0) := by
  intro hExact
  -- The constant sequence admits an explicit geometric `Q`-linear majorant.
  have hMajorant :
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant (fun _ : ℕ ↦ xStar) xStar q ∧
        HasQLinearConvergenceTo q 0 := by
    refine ⟨fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (k + 1), ?_⟩
    refine ⟨?_, geometricHalf_hasQLinearConvergenceTo_zero⟩
    constructor
    · intro k
      positivity
    · intro k
      simp
  have hLinear : rLinearConvergenceTo (fun _ : ℕ ↦ xStar) xStar := hExact.mpr hMajorant
  -- But the constant sequence has `R[1] = 0`, so it cannot satisfy the strict positivity clause.
  rcases hLinear with ⟨_, hpos, _⟩
  rw [rRate_one_const_eq_zero xStar] at hpos
  exact (lt_irrefl 0) hpos

/-- The exact `R`-linear owner still implies the existence of a nonnegative
scalar majorant sequence `q` with `‖x k - xStar‖ ≤ q k` for all `k` and `q`
converging `Q`-linearly to `0`. -/
theorem rLinearConvergenceTo_imp_exists_nonneg_qLinearMajorant
    (x : ℕ → E) (xStar : E) :
    rLinearConvergenceTo x xStar →
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQLinearConvergenceTo q 0 := by
  intro hx
  have hMajorant :
      0 < R[1] x xStar ∧
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant x xStar q ∧
          HasQLinearConvergenceTo q 0 := by
    simpa [rLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant x xStar] using hx
  exact hMajorant.2

/-- The analogous exact `R`-quadratic majorant characterization is also false:
the constant sequence `fun _ ↦ xStar` is not `rQuadraticConvergenceTo`, but it
still admits nonnegative scalar majorants converging `Q`-quadratically to `0`.
The honest repair is the broader equivalence
`rAtLeastQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant` together
with the exact-owner forward implication below. -/
private theorem exactRQuadraticMajorantCharacterizationFalse
    (xStar : E) :
    ¬ (rQuadraticConvergenceTo (fun _ ↦ xStar) xStar ↔
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant (fun _ ↦ xStar) xStar q ∧
          HasQQuadraticConvergenceTo q 0) := by
  intro hExact
  -- The constant sequence admits an explicit dyadic-geometric `Q`-quadratic majorant.
  have hMajorant :
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant (fun _ : ℕ ↦ xStar) xStar q ∧
        HasQQuadraticConvergenceTo q 0 := by
    refine ⟨fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ (2 ^ (k + 1 : ℕ)), ?_⟩
    refine ⟨?_, dyadicGeometricHalf_hasQQuadraticConvergenceTo_zero⟩
    constructor
    · intro k
      positivity
    · intro k
      simp
  have hQuadratic : rQuadraticConvergenceTo (fun _ : ℕ ↦ xStar) xStar := hExact.mpr hMajorant
  -- But the constant sequence has `R[2] = 0`, so it cannot satisfy the strict positivity clause.
  rcases hQuadratic with ⟨_, hpos, _⟩
  rw [rRate_two_const_eq_zero xStar] at hpos
  exact (lt_irrefl 0) hpos

/-- The exact `R`-quadratic owner still implies the existence of a nonnegative
scalar majorant sequence converging `Q`-quadratically to `0`. -/
theorem rQuadraticConvergenceTo_imp_exists_nonneg_qQuadraticMajorant
    (x : ℕ → E) (xStar : E) :
    rQuadraticConvergenceTo x xStar →
      ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧
        HasQQuadraticConvergenceTo q 0 := by
  intro hx
  have hMajorant :
      0 < R[2] x xStar ∧
        ∃ q : ℕ → ℝ,
          IsNonnegErrorMajorant x xStar q ∧
          HasQQuadraticConvergenceTo q 0 := by
    simpa [rQuadraticConvergenceTo_iff_exists_nonneg_qQuadraticMajorant x xStar] using hx
  exact hMajorant.2

end ConvergenceRates
