/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section02_part3

open Classical

section Chap04
section Section02

/-- Proposition 4.2.13: assume the hypotheses and notation of the shifted
power-series setup centered at `a`, and let
`d m = ∑' n, ((n+m)!/(m!n!)) * (b-a)^n * c (n+m)`, with this defining series
convergent for each `m`.
Then for every `ε` with `0 < ε < s`, there exists `C > 0` such that
`|d m| ≤ C * (s - ε)^{-m}` for all integers `m ≥ 0` (encoded as `m : ℕ`). -/
theorem shifted_coefficients_norm_le_of_subradius
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (d : ℕ → ℝ)
    (hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)))
    (hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m))
    (ε : ℝ) (hε0 : 0 < ε) (hεs : ε < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, |d m| ≤ C * ((s - ε)⁻¹) ^ m := by
  have hCenter :=
    center_distance_le_radius_subradius_of_interval_subset
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub
  have hDistLe : |b - (a : ℝ)| ≤ r - s := by
    simpa [abs_sub_comm] using hCenter.1
  let δ : ℝ := ε / 2
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith
  have hδs : δ < s := by
    dsimp [δ]
    linarith
  have hs_le_r : s ≤ r := by
    linarith [hDistLe, abs_nonneg (b - (a : ℝ))]
  have hδr : δ < r := lt_of_lt_of_le hδs hs_le_r
  have hρ0 : 0 < r - δ := sub_pos.mpr hδr
  let ρ : ℝ := r - δ
  let x : ℝ := |b - (a : ℝ)|
  have hxnonneg : 0 ≤ x := by
    simp [x]
  have hxle : x ≤ r - s := by
    simpa [x] using hDistLe
  have hxltρ : x < ρ := by
    have hrs : r - s < r - δ := by
      linarith [hδs]
    exact lt_of_le_of_lt (by simpa [x] using hDistLe) (by simpa [ρ] using hrs)
  have hρpos : 0 < ρ := by
    simpa [ρ] using hρ0
  have hxAbs : |x| < ρ := by
    simpa [abs_of_nonneg hxnonneg] using hxltρ
  have hsε0 : 0 < s - ε := sub_pos.mpr hεs
  have hGap : s - ε ≤ ρ - x := by
    have hFirst : s - ε ≤ s - δ := by
      dsimp [δ]
      linarith
    have hSecond : s - δ ≤ ρ - x := by
      linarith [hxle]
    exact le_trans hFirst hSecond
  obtain ⟨K, hK0, hKbound⟩ :=
    powerSeries_coeff_norm_le_of_subradius
      a f hanalytic hr c hI hsummable hpowerSeries δ hδ0 hδr
  have hAbsSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            |((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)|) :=
    shifted_coeffSeries_absSummable_of_interval_subset
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub
  refine ⟨K * ρ * (s - ε)⁻¹, ?_, ?_⟩
  · exact mul_pos (mul_pos hK0 hρpos) (inv_pos.mpr hsε0)
  · intro m
    let term : ℕ → ℝ :=
      fun n =>
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)
    let major : ℕ → ℝ :=
      fun n =>
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            x ^ n * (ρ⁻¹) ^ (n + m)
    have hMajorNonneg : ∀ n : ℕ, 0 ≤ major n := by
      intro n
      dsimp [major]
      positivity
    have hScaled :=
      scaledGeometricSeries_higherDerivative_tsum_and_absConvergence
        ρ x m hρpos hxAbs
    have hMajorSummable : Summable major := by
      have hSummableAbs : Summable (fun n : ℕ => |major n|) := by
        simpa [major] using hScaled.2
      have hAbsEq : (fun n : ℕ => |major n|) = major := by
        funext n
        exact abs_of_nonneg (hMajorNonneg n)
      rw [hAbsEq] at hSummableAbs
      exact hSummableAbs
    have hPointwise : ∀ n : ℕ, |term n| ≤ K * major n := by
      intro n
      have hCoeff : |c (n + m)| ≤ K * (ρ⁻¹) ^ (n + m) := by
        simpa [ρ] using hKbound (n + m)
      have hRatioNonneg :
          0 ≤
            ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) := by
        positivity
      have hAbsMain :
          |((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
              (b - (a : ℝ)) ^ n| =
            ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) * x ^ n := by
        rw [abs_mul, abs_of_nonneg hRatioNonneg, abs_pow]
      calc
        |term n|
            =
              |((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  (b - (a : ℝ)) ^ n| * |c (n + m)| := by
                dsimp [term]
                rw [abs_mul]
        _ ≤
              |((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  (b - (a : ℝ)) ^ n| * (K * (ρ⁻¹) ^ (n + m)) := by
              exact mul_le_mul_of_nonneg_left hCoeff (abs_nonneg _)
        _ = K *
              (((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  x ^ n * (ρ⁻¹) ^ (n + m)) := by
              rw [hAbsMain]
              ring
        _ = K * major n := by
              rfl
    have hTermAbsSummable : Summable (fun n : ℕ => |term n|) := by
      simpa [term, mul_assoc] using hAbsSummable m
    have hMajorScaledSummable : Summable (fun n : ℕ => K * major n) :=
      hMajorSummable.mul_left K
    have hTsumBound : (∑' n : ℕ, |term n|) ≤ ∑' n : ℕ, K * major n := by
      exact Summable.tsum_le_tsum hPointwise hTermAbsSummable hMajorScaledSummable
    have hMajorClosed :
        (∑' n : ℕ, major n) = ρ / (ρ - x) ^ (m + 1) := by
      simpa [major] using hScaled.1.symm
    have hDmajor :
        |d m| ≤ K * (ρ / (ρ - x) ^ (m + 1)) := by
      calc
        |d m| = |∑' n : ℕ, term n| := by
          simpa [term] using congrArg abs (hd m)
        _ ≤ ∑' n : ℕ, |term n| := by
          have hNormSummable : Summable (fun n : ℕ => ‖term n‖) := by
            simpa [Real.norm_eq_abs] using hTermAbsSummable
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hNormSummable
        _ ≤ ∑' n : ℕ, K * major n := hTsumBound
        _ = K * (∑' n : ℕ, major n) := by
          rw [tsum_mul_left]
        _ = K * (ρ / (ρ - x) ^ (m + 1)) := by
          rw [hMajorClosed]
    have hGapPos : 0 < ρ - x := sub_pos.mpr hxltρ
    have hInvCompare : (ρ - x)⁻¹ ≤ (s - ε)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hsε0 hGap
    have hPowCompare :
        ((ρ - x)⁻¹) ^ (m + 1) ≤ ((s - ε)⁻¹) ^ (m + 1) := by
      exact pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hGapPos)) hInvCompare (m + 1)
    have hKρNonneg : 0 ≤ K * ρ := mul_nonneg (le_of_lt hK0) (le_of_lt hρpos)
    calc
      |d m| ≤ K * (ρ / (ρ - x) ^ (m + 1)) := hDmajor
      _ = (K * ρ) * ((ρ - x)⁻¹) ^ (m + 1) := by
            simp [div_eq_mul_inv, mul_assoc, inv_pow]
      _ ≤ (K * ρ) * ((s - ε)⁻¹) ^ (m + 1) :=
            mul_le_mul_of_nonneg_left hPowCompare hKρNonneg
      _ = K * ρ * (s - ε)⁻¹ * ((s - ε)⁻¹) ^ m := by
            rw [pow_succ]
            ring
      _ = (K * ρ * (s - ε)⁻¹) * ((s - ε)⁻¹) ^ m := by
            ring

/-- Helper for Proposition 4.2.14: for a point in `(b-s, b+s)`, one can choose
`ε` with `0 < ε < s` and still keep a strict gap `|x-b| < s-ε`. -/
lemma helperForProposition_4_2_14_exists_subradius_gap_at_point
    {b s x : ℝ} (hs : 0 < s)
    (hx : x ∈ Set.Ioo (b - s) (b + s)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < s ∧ |x - b| < s - ε := by
  have hxAbs : |x - b| < s := by
    rcases hx with ⟨hxL, hxR⟩
    have hxLeft : -s < x - b := by linarith
    have hxRight : x - b < s := by linarith
    exact abs_lt.2 ⟨hxLeft, hxRight⟩
  refine ⟨(s - |x - b|) / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith [abs_nonneg (x - b)]
  · linarith

/-- Helper for Proposition 4.2.14: the shifted series is absolutely summable at
every point of `(b-s, b+s)`. -/
lemma helperForProposition_4_2_14_absSummable_shifted_series_at_point
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (d : ℕ → ℝ)
    (hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)))
    (hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)) :
    ∀ x (hx : x ∈ Set.Ioo (b - s) (b + s)),
      Summable (fun m : ℕ => |d m * (x - b) ^ m|) := by
  intro x hx
  obtain ⟨ε, hε0, hεs, hxGap⟩ :=
    helperForProposition_4_2_14_exists_subradius_gap_at_point hs hx
  obtain ⟨C, hC0, hCbound⟩ :=
    shifted_coefficients_norm_le_of_subradius
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub d hdSummable hd ε hε0 hεs
  have hsε0 : 0 < s - ε := sub_pos.mpr hεs
  let q : ℝ := |x - b| * (s - ε)⁻¹
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqLtOne : q < 1 := by
    have hDiv : |x - b| / (s - ε) < 1 := (div_lt_one hsε0).2 hxGap
    simpa [q, div_eq_mul_inv] using hDiv
  have hqAbsLtOne : |q| < 1 := by
    simpa [abs_of_nonneg hqNonneg] using hqLtOne
  have hMajorantSummable : Summable (fun m : ℕ => C * q ^ m) := by
    have hGeom : Summable (fun m : ℕ => q ^ m) :=
      summable_geometric_of_abs_lt_one hqAbsLtOne
    exact hGeom.mul_left C
  have hPointwise :
      ∀ m : ℕ, |d m * (x - b) ^ m| ≤ C * q ^ m := by
    intro m
    have hDmBound : |d m| ≤ C * ((s - ε)⁻¹) ^ m := hCbound m
    have hPowNonneg : 0 ≤ |x - b| ^ m := by positivity
    have hMulBound :
        |d m| * |x - b| ^ m ≤ (C * ((s - ε)⁻¹) ^ m) * |x - b| ^ m := by
      exact mul_le_mul_of_nonneg_right hDmBound hPowNonneg
    calc
      |d m * (x - b) ^ m| = |d m| * |(x - b) ^ m| := by rw [abs_mul]
      _ = |d m| * |x - b| ^ m := by rw [abs_pow]
      _ ≤ (C * ((s - ε)⁻¹) ^ m) * |x - b| ^ m := hMulBound
      _ = C * (((s - ε)⁻¹) ^ m * |x - b| ^ m) := by rw [mul_assoc]
      _ = C * (((s - ε)⁻¹ * |x - b|) ^ m) := by rw [← mul_pow]
      _ = C * ((|x - b| * (s - ε)⁻¹) ^ m) := by
          congr 1
          rw [mul_comm]
      _ = C * q ^ m := by rfl
  have hTargetNonneg : ∀ m : ℕ, 0 ≤ |d m * (x - b) ^ m| := by
    intro m
    exact abs_nonneg _
  exact hMajorantSummable.of_nonneg_of_le hTargetNonneg hPointwise

/-- Helper for Proposition 4.2.14: expand the original power series around `a`
at a point `x ∈ (b-s, b+s)` into a triangular finite sum in powers of
`(x - b)`. -/
lemma helperForProposition_4_2_14_expand_original_series_termwise
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (x : ℝ) (hx : x ∈ Set.Ioo (b - s) (b + s)) :
    f ⟨x, hI (hsub hx)⟩ =
      ∑' n : ℕ,
        Finset.sum (Finset.range (n + 1)) (fun m =>
          ((Nat.factorial n : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
              (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m) := by
  have hxSub : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := hsub hx
  calc
    f ⟨x, hI (hsub hx)⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := hpowerSeries x hxSub
    _ =
        ∑' n : ℕ,
          c n *
            (Finset.sum (Finset.range (n + 1))
              (fun m =>
                ((Nat.factorial n : ℝ) /
                      ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
                    (b - (a : ℝ)) ^ (n - m) * (x - b) ^ m)) := by
          refine congrArg tsum ?_
          funext n
          rw [shiftedPower_eq_sum_factorial_ratio_mul_shiftedPowers (a : ℝ) b n x]
    _ =
        ∑' n : ℕ,
          Finset.sum (Finset.range (n + 1)) (fun m =>
            c n *
              (((Nat.factorial n : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
                  (b - (a : ℝ)) ^ (n - m) * (x - b) ^ m)) := by
          refine congrArg tsum ?_
          funext n
          rw [Finset.mul_sum]
    _ =
        ∑' n : ℕ,
          Finset.sum (Finset.range (n + 1)) (fun m =>
            ((Nat.factorial n : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
                (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m) := by
          refine congrArg tsum ?_
          funext n
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring

/-- Helper for Proposition 4.2.14: each row sum in the triangular rearrangement
is exactly `d m * (x - b)^m`. -/
lemma helperForProposition_4_2_14_row_tsum_eq_d_times_shiftedPower
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (d : ℕ → ℝ)
    (hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)))
    (hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m))
    (x : ℝ) (m : ℕ) :
    (∑' n : ℕ,
        (((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)) *
          (x - b) ^ m) =
      d m * (x - b) ^ m := by
  calc
    (∑' n : ℕ,
        (((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)) *
          (x - b) ^ m) =
        (∑' n : ℕ,
          ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
              (b - (a : ℝ)) ^ n * c (n + m)) *
          (x - b) ^ m := by
          rw [tsum_mul_right]
    _ = d m * (x - b) ^ m := by
          rw [hd m]

/-- Helper for Proposition 4.2.14: if a kernel on `ℕ × ℕ` is summable, then
the triangular range-indexed `tsum` can be rewritten as the corresponding
product-indexed `tsum` via antidiagonal reindexing. -/
lemma helperForProposition_4_2_14_triangular_reindex_tsum_via_prod
    (K : ℕ → ℕ → ℝ)
    (hK : Summable (fun p : ℕ × ℕ => K p.1 p.2)) :
    (∑' n : ℕ, Finset.sum (Finset.range (n + 1)) (fun m => K m (n - m))) =
      ∑' p : ℕ × ℕ, K p.1 p.2 := by
  let F : (Σ n : ℕ, ↥(Finset.antidiagonal n)) → ℝ :=
    fun x => K x.2.1.1 x.2.1.2
  have hSigma : Summable F := by
    have hComp :
        Summable ((fun p : ℕ × ℕ => K p.1 p.2) ∘ Finset.sigmaAntidiagonalEquivProd) := by
      exact (Finset.sigmaAntidiagonalEquivProd.summable_iff).2 hK
    simpa [F] using hComp
  have hRows :
      ∀ n : ℕ, Summable (fun ij : ↥(Finset.antidiagonal n) => K ij.1.1 ij.1.2) := by
    intro n
    exact (hasSum_fintype (fun ij : ↥(Finset.antidiagonal n) => K ij.1.1 ij.1.2)).summable
  have hOuterSigma :
      (∑' n : ℕ, ∑' ij : ↥(Finset.antidiagonal n), K ij.1.1 ij.1.2) =
        ∑' x : (Σ n : ℕ, ↥(Finset.antidiagonal n)), K x.2.1.1 x.2.1.2 := by
    simpa [F] using (hSigma.tsum_sigma' hRows).symm
  have hSigmaProd :
      (∑' x : (Σ n : ℕ, ↥(Finset.antidiagonal n)), K x.2.1.1 x.2.1.2) =
        ∑' p : ℕ × ℕ, K p.1 p.2 := by
    simpa [F] using
      (Finset.sigmaAntidiagonalEquivProd.tsum_eq (fun p : ℕ × ℕ => K p.1 p.2))
  have hInner :
      (fun n : ℕ => ∑' ij : ↥(Finset.antidiagonal n), K ij.1.1 ij.1.2) =
        fun n : ℕ => Finset.sum (Finset.range (n + 1)) (fun m => K m (n - m)) := by
    funext n
    calc
      ∑' ij : ↥(Finset.antidiagonal n), K ij.1.1 ij.1.2
          = ∑ ij : ↥(Finset.antidiagonal n), K ij.1.1 ij.1.2 := by
              rw [tsum_fintype]
      _ = ∑ ij ∈ Finset.antidiagonal n, K ij.1 ij.2 := by
            simpa using
              (Finset.sum_finset_coe
                (f := fun ij : ℕ × ℕ => K ij.1 ij.2)
                (s := Finset.antidiagonal n))
      _ = ∑ m ∈ Finset.range (n + 1), K m (n - m) := by
            simpa using
              (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m k => K m k) n)
  have hInner' :
      (fun n : ℕ => Finset.sum (Finset.range (n + 1)) (fun m => K m (n - m))) =
        fun n : ℕ => ∑' ij : ↥(Finset.antidiagonal n), K ij.1.1 ij.1.2 := by
    simpa using hInner.symm
  rw [hInner', hOuterSigma, hSigmaProd]

/-- Helper for Proposition 4.2.14: once a product-indexed kernel is summable,
its `tsum` can be identified with the shifted-coefficient series by evaluating
row `tsum`s. -/
lemma helperForProposition_4_2_14_prod_rows_to_shifted_coeff_tsum
    (K : ℕ → ℕ → ℝ) (d : ℕ → ℝ) (x b : ℝ)
    (hK : Summable (fun p : ℕ × ℕ => K p.1 p.2))
    (hRows : ∀ m : ℕ, (∑' n : ℕ, K m n) = d m * (x - b) ^ m) :
    (∑' p : ℕ × ℕ, K p.1 p.2) = ∑' m : ℕ, d m * (x - b) ^ m := by
  calc
    (∑' p : ℕ × ℕ, K p.1 p.2) = ∑' m : ℕ, ∑' n : ℕ, K m n := by
      simpa using hK.tsum_prod
    _ = ∑' m : ℕ, d m * (x - b) ^ m := by
      refine congrArg tsum ?_
      funext m
      exact hRows m

/-- Helper for Proposition 4.2.14: for fixed `x ∈ (b-s, b+s)`, the product
kernel
`(m,k) ↦ ((m+k)!/(m!k!)) * (b-a)^k * c (m+k) * (x-b)^m`
is summable on `ℕ × ℕ`. -/
lemma helperForProposition_4_2_14_summable_prod_shifted_kernel_at_point
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (x : ℝ) (hx : x ∈ Set.Ioo (b - s) (b + s)) :
    Summable
      (fun p : ℕ × ℕ =>
        ((Nat.factorial (p.1 + p.2) : ℝ) /
              ((Nat.factorial p.1 : ℝ) * (Nat.factorial p.2 : ℝ))) *
            (b - (a : ℝ)) ^ p.2 * c (p.1 + p.2) * (x - b) ^ p.1) := by
  let K : ℕ → ℕ → ℝ :=
    fun m n =>
      ((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          (b - (a : ℝ)) ^ n * c (n + m) * (x - b) ^ m
  have hCenter :=
    center_distance_le_radius_subradius_of_interval_subset
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub
  have hDistLe : |b - (a : ℝ)| ≤ r - s := by
    simpa [abs_sub_comm] using hCenter.1
  obtain ⟨ε, hε0, hεs, hxGap⟩ :=
    helperForProposition_4_2_14_exists_subradius_gap_at_point hs hx
  let δ : ℝ := ε / 2
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith
  have hδs : δ < s := by
    dsimp [δ]
    linarith
  have hs_le_r : s ≤ r := by
    linarith [hDistLe, abs_nonneg (b - (a : ℝ))]
  have hδr : δ < r := lt_of_lt_of_le hδs hs_le_r
  have hρ0 : 0 < r - δ := sub_pos.mpr hδr
  let ρ : ℝ := r - δ
  let y : ℝ := |b - (a : ℝ)|
  have hyNonneg : 0 ≤ y := by
    simp [y]
  have hyle : y ≤ r - s := by
    simpa [y] using hDistLe
  have hyltρ : y < ρ := by
    have hrs : r - s < r - δ := by
      linarith [hδs]
    exact lt_of_le_of_lt (by simpa [y] using hDistLe) (by simpa [ρ] using hrs)
  have hρpos : 0 < ρ := by
    simpa [ρ] using hρ0
  have hyAbs : |y| < ρ := by
    simpa [abs_of_nonneg hyNonneg] using hyltρ
  have hsε0 : 0 < s - ε := sub_pos.mpr hεs
  have hGap : s - ε ≤ ρ - y := by
    have hFirst : s - ε ≤ s - δ := by
      dsimp [δ]
      linarith
    have hSecond : s - δ ≤ ρ - y := by
      linarith [hyle]
    exact le_trans hFirst hSecond
  obtain ⟨C, hC0, hCbound⟩ :=
    powerSeries_coeff_norm_le_of_subradius
      a f hanalytic hr c hI hsummable hpowerSeries δ hδ0 hδr
  have hAbsSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            |((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)|) :=
    shifted_coeffSeries_absSummable_of_interval_subset
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub
  let q : ℝ := |x - b| * (s - ε)⁻¹
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqLtOne : q < 1 := by
    have hDiv : |x - b| / (s - ε) < 1 := (div_lt_one hsε0).2 hxGap
    simpa [q, div_eq_mul_inv] using hDiv
  have hqAbsLtOne : |q| < 1 := by
    simpa [abs_of_nonneg hqNonneg] using hqLtOne
  have hRowSummable : ∀ m : ℕ, Summable (fun n : ℕ => |K m n|) := by
    intro m
    have hScaled :
        Summable
          (fun n : ℕ =>
            |((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)| * |(x - b) ^ m|) := by
      exact (hAbsSummable m).mul_right |(x - b) ^ m|
    have hEq :
        (fun n : ℕ => |K m n|) =
          (fun n : ℕ =>
            |((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)| * |(x - b) ^ m|) := by
      funext n
      dsimp [K]
      rw [abs_mul]
    rw [hEq]
    exact hScaled
  have hRowsBound :
      ∀ m : ℕ,
        (∑' n : ℕ, |K m n|) ≤ (C * ρ * (s - ε)⁻¹) * q ^ m := by
    intro m
    let term : ℕ → ℝ :=
      fun n =>
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)
    let major : ℕ → ℝ :=
      fun n =>
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            y ^ n * (ρ⁻¹) ^ (n + m)
    have hMajorNonneg : ∀ n : ℕ, 0 ≤ major n := by
      intro n
      dsimp [major]
      positivity
    have hScaled :=
      scaledGeometricSeries_higherDerivative_tsum_and_absConvergence
        ρ y m hρpos hyAbs
    have hMajorSummable : Summable major := by
      have hSummableAbs : Summable (fun n : ℕ => |major n|) := by
        simpa [major] using hScaled.2
      have hAbsEq : (fun n : ℕ => |major n|) = major := by
        funext n
        exact abs_of_nonneg (hMajorNonneg n)
      rw [hAbsEq] at hSummableAbs
      exact hSummableAbs
    have hPointwiseTerm : ∀ n : ℕ, |term n| ≤ C * major n := by
      intro n
      have hCoeff : |c (n + m)| ≤ C * (ρ⁻¹) ^ (n + m) := by
        simpa [ρ] using hCbound (n + m)
      have hRatioNonneg :
          0 ≤
            ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) := by
        positivity
      have hAbsMain :
          |((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
              (b - (a : ℝ)) ^ n| =
            ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) * y ^ n := by
        rw [abs_mul, abs_of_nonneg hRatioNonneg, abs_pow]
      calc
        |term n|
            =
              |((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  (b - (a : ℝ)) ^ n| * |c (n + m)| := by
                dsimp [term]
                rw [abs_mul]
        _ ≤
              |((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  (b - (a : ℝ)) ^ n| * (C * (ρ⁻¹) ^ (n + m)) := by
              exact mul_le_mul_of_nonneg_left hCoeff (abs_nonneg _)
        _ = C *
              (((Nat.factorial (n + m) : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                  y ^ n * (ρ⁻¹) ^ (n + m)) := by
              rw [hAbsMain]
              ring
        _ = C * major n := by
              rfl
    have hTermAbsSummable : Summable (fun n : ℕ => |term n|) := by
      simpa [term, mul_assoc] using hAbsSummable m
    have hMajorScaledSummable : Summable (fun n : ℕ => C * major n) :=
      hMajorSummable.mul_left C
    have hTsumBound : (∑' n : ℕ, |term n|) ≤ ∑' n : ℕ, C * major n := by
      exact
        Summable.tsum_le_tsum hPointwiseTerm hTermAbsSummable
          hMajorScaledSummable
    have hMajorClosed :
        (∑' n : ℕ, major n) = ρ / (ρ - y) ^ (m + 1) := by
      simpa [major] using hScaled.1.symm
    have hTermBound :
        (∑' n : ℕ, |term n|) ≤ C * (ρ / (ρ - y) ^ (m + 1)) := by
      calc
        (∑' n : ℕ, |term n|) ≤ ∑' n : ℕ, C * major n := hTsumBound
        _ = C * (∑' n : ℕ, major n) := by
              rw [tsum_mul_left]
        _ = C * (ρ / (ρ - y) ^ (m + 1)) := by
              rw [hMajorClosed]
    have hPowNonneg : 0 ≤ |x - b| ^ m := by
      positivity
    have hGapPos : 0 < ρ - y := sub_pos.mpr hyltρ
    have hInvCompare : (ρ - y)⁻¹ ≤ (s - ε)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hsε0 hGap
    have hPowCompare :
        ((ρ - y)⁻¹) ^ (m + 1) ≤ ((s - ε)⁻¹) ^ (m + 1) := by
      exact
        pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hGapPos))
          hInvCompare (m + 1)
    have hCρNonneg : 0 ≤ C * ρ :=
      mul_nonneg (le_of_lt hC0) (le_of_lt hρpos)
    have hEqRow :
        (∑' n : ℕ, |K m n|) = (∑' n : ℕ, |term n|) * |x - b| ^ m := by
      have hEqFun :
          (fun n : ℕ => |K m n|) =
            (fun n : ℕ => |term n| * |x - b| ^ m) := by
        funext n
        dsimp [K, term]
        rw [abs_mul, abs_pow]
      rw [hEqFun, tsum_mul_right]
    calc
      (∑' n : ℕ, |K m n|) = (∑' n : ℕ, |term n|) * |x - b| ^ m := hEqRow
      _ ≤ (C * (ρ / (ρ - y) ^ (m + 1))) * |x - b| ^ m :=
            mul_le_mul_of_nonneg_right hTermBound hPowNonneg
      _ = (C * ρ) * ((ρ - y)⁻¹) ^ (m + 1) * |x - b| ^ m := by
            simp [div_eq_mul_inv, mul_assoc, inv_pow]
      _ ≤ (C * ρ) * ((s - ε)⁻¹) ^ (m + 1) * |x - b| ^ m := by
            exact
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hPowCompare hCρNonneg)
                hPowNonneg
      _ = C * ρ * (s - ε)⁻¹ * (((s - ε)⁻¹) ^ m * |x - b| ^ m) := by
            rw [pow_succ]
            ring
      _ = C * ρ * (s - ε)⁻¹ * (|x - b| * (s - ε)⁻¹) ^ m := by
            rw [← mul_pow]
            ring
      _ = (C * ρ * (s - ε)⁻¹) * q ^ m := by
            simp [q, mul_assoc, mul_left_comm, mul_comm]
  have hMajorantSummable : Summable (fun m : ℕ => (C * ρ * (s - ε)⁻¹) * q ^ m) := by
    have hGeom : Summable (fun m : ℕ => q ^ m) :=
      summable_geometric_of_abs_lt_one hqAbsLtOne
    exact hGeom.mul_left (C * ρ * (s - ε)⁻¹)
  have hRowsTsumSummable : Summable (fun m : ℕ => ∑' n : ℕ, |K m n|) := by
    have hRowTsumNonneg : ∀ m : ℕ, 0 ≤ ∑' n : ℕ, |K m n| := by
      intro m
      exact tsum_nonneg (fun n => abs_nonneg (K m n))
    exact hMajorantSummable.of_nonneg_of_le hRowTsumNonneg hRowsBound
  have hAbsProd : Summable (fun p : ℕ × ℕ => |K p.1 p.2|) := by
    have hNonneg : 0 ≤ fun p : ℕ × ℕ => |K p.1 p.2| := by
      intro p
      exact abs_nonneg (K p.1 p.2)
    exact (summable_prod_of_nonneg hNonneg).2 ⟨hRowSummable, hRowsTsumSummable⟩
  have hProd : Summable (fun p : ℕ × ℕ => K p.1 p.2) := Summable.of_abs hAbsProd
  simpa [K, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using hProd

/-- Helper for Proposition 4.2.14: the triangular expansion obtained from the
original series can be reordered into the shifted coefficient series. -/
lemma helperForProposition_4_2_14_triangular_tsum_to_shifted_coeff_tsum
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (d : ℕ → ℝ)
    (hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)))
    (hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m))
    (x : ℝ) (hx : x ∈ Set.Ioo (b - s) (b + s)) :
    (∑' n : ℕ,
        Finset.sum (Finset.range (n + 1)) (fun m =>
          ((Nat.factorial n : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
              (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m)) =
      ∑' m : ℕ, d m * (x - b) ^ m := by
  let K : ℕ → ℕ → ℝ :=
    fun m k =>
      ((Nat.factorial (m + k) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial k : ℝ))) *
          (b - (a : ℝ)) ^ k * c (m + k) * (x - b) ^ m
  have hRangeToK :
      (fun n : ℕ =>
        Finset.sum (Finset.range (n + 1)) (fun m =>
          ((Nat.factorial n : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
              (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m)) =
      (fun n : ℕ => Finset.sum (Finset.range (n + 1)) (fun m => K m (n - m))) := by
    funext n
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hmn : m + (n - m) = n := Nat.add_sub_of_le hmle
    simp [K, hmn, mul_assoc, mul_left_comm, mul_comm]
  have hRows : ∀ m : ℕ, (∑' n : ℕ, K m n) = d m * (x - b) ^ m := by
    intro m
    simpa [K, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
      (helperForProposition_4_2_14_row_tsum_eq_d_times_shiftedPower
        a f hanalytic hr c hI hsummable hpowerSeries hs hsub d hdSummable hd x m)
  have hK : Summable (fun p : ℕ × ℕ => K p.1 p.2) := by
    simpa [K, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
      (helperForProposition_4_2_14_summable_prod_shifted_kernel_at_point
        a f hanalytic hr c hI hsummable hpowerSeries hs hsub x hx)
  calc
    (∑' n : ℕ,
        Finset.sum (Finset.range (n + 1)) (fun m =>
          ((Nat.factorial n : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
              (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m))
        = ∑' n : ℕ, Finset.sum (Finset.range (n + 1)) (fun m => K m (n - m)) := by
          refine congrArg tsum ?_
          exact hRangeToK
    _ = ∑' p : ℕ × ℕ, K p.1 p.2 :=
      helperForProposition_4_2_14_triangular_reindex_tsum_via_prod K hK
    _ = ∑' m : ℕ, d m * (x - b) ^ m :=
      helperForProposition_4_2_14_prod_rows_to_shifted_coeff_tsum K d x b hK hRows

/-- Proposition 4.2.14: assume the hypotheses and notation of the shifted
power-series setup (with coefficients `d`). Then for every
`x ∈ (b-s, b+s)`, the power series `∑' m, d m * (x-b)^m` is absolutely
convergent, and one has
`f(x) = ∑' m, d m * (x-b)^m` on that interval. -/
theorem shifted_powerSeries_absConvergent_and_eq_on_interval
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
    (d : ℕ → ℝ)
    (hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)))
    (hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)) :
    ∀ x (hx : x ∈ Set.Ioo (b - s) (b + s)),
      Summable (fun m : ℕ => |d m * (x - b) ^ m|) ∧
        f ⟨x, hI (hsub hx)⟩ =
          ∑' m : ℕ, d m * (x - b) ^ m := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact
      helperForProposition_4_2_14_absSummable_shifted_series_at_point
        a f hanalytic hr c hI hsummable hpowerSeries hs hsub d hdSummable hd x hx
  ·
    calc
      f ⟨x, hI (hsub hx)⟩ =
          ∑' n : ℕ,
            Finset.sum (Finset.range (n + 1)) (fun m =>
              ((Nat.factorial n : ℝ) /
                    ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
                  (b - (a : ℝ)) ^ (n - m) * c n * (x - b) ^ m) :=
        helperForProposition_4_2_14_expand_original_series_termwise
          a f hanalytic hr c hI hsummable hpowerSeries hs hsub x hx
      _ = ∑' m : ℕ, d m * (x - b) ^ m :=
        helperForProposition_4_2_14_triangular_tsum_to_shifted_coeff_tsum
          a f hanalytic hr c hI hsummable hpowerSeries hs hsub d hdSummable hd x hx

/-- Proposition 4.2.15: assume the hypotheses and notation of the local
power-series setup centered at `a`. Then `f` is real analytic at every
`b ∈ (a-r, a+r)`. -/
theorem realAnalyticAt_every_point_of_localPowerSeriesInterval
    {E : Set ℝ} (a : E) (f : E → ℝ)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n) :
    ∀ b (hb : b ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
      IsRealAnalyticAt E f ⟨b, hI hb⟩ := by
  have hseriesAtA :
      ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := by
    intro x hx
    exact ⟨hsummable x hx, hpowerSeries x hx⟩
  have hLeftA : (a : ℝ) - r < (a : ℝ) := by
    linarith [hr]
  have hRightA : (a : ℝ) < (a : ℝ) + r := by
    linarith [hr]
  have hIooNhdsA : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ∈ nhds (a : ℝ) :=
    Ioo_mem_nhds hLeftA hRightA
  have hEnhdsA : E ∈ nhds (a : ℝ) :=
    Filter.mem_of_superset hIooNhdsA hI
  have haInterior : (a : ℝ) ∈ interior E :=
    mem_interior_iff_mem_nhds.2 hEnhdsA
  have hanalytic : IsRealAnalyticAt E f a :=
    helperForTheorem_4_2_3_isRealAnalyticAt_of_intervalSeriesData
      f a haInterior hr hI c hseriesAtA
  intro b hb
  let s : ℝ := min (b - ((a : ℝ) - r)) (((a : ℝ) + r) - b)
  have hs : 0 < s := by
    have hbLeft : (a : ℝ) - r < b := hb.1
    have hbRight : b < (a : ℝ) + r := hb.2
    dsimp [s]
    exact lt_min (by linarith) (by linarith)
  have hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := by
    intro x hx
    have hsLeft : s ≤ b - ((a : ℝ) - r) := by
      dsimp [s]
      exact min_le_left _ _
    have hsRight : s ≤ ((a : ℝ) + r) - b := by
      dsimp [s]
      exact min_le_right _ _
    have hLower : (a : ℝ) - r ≤ b - s := by
      linarith [hsLeft]
    have hUpper : b + s ≤ (a : ℝ) + r := by
      linarith [hsRight]
    refine Set.mem_Ioo.mpr ?_
    constructor
    · exact lt_of_le_of_lt hLower hx.1
    · exact lt_of_lt_of_le hx.2 hUpper
  let hIb : Set.Ioo (b - s) (b + s) ⊆ E := fun x hx => hI (hsub hx)
  have hLeftB : b - s < b := by
    linarith [hs]
  have hRightB : b < b + s := by
    linarith [hs]
  have hIooNhdsB : Set.Ioo (b - s) (b + s) ∈ nhds b :=
    Ioo_mem_nhds hLeftB hRightB
  have hEnhdsB : E ∈ nhds b :=
    Filter.mem_of_superset hIooNhdsB hIb
  have hbInterior : b ∈ interior E :=
    mem_interior_iff_mem_nhds.2 hEnhdsB
  let d : ℕ → ℝ :=
    fun m =>
      ∑' n : ℕ,
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)
  have hdSummable :
      ∀ m : ℕ,
        Summable
          (fun n : ℕ =>
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m)) := by
    intro m
    let term : ℕ → ℝ :=
      fun n =>
        ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)
    have hAbs :
        Summable (fun n : ℕ => |term n|) := by
      simpa [term] using
        (shifted_coeffSeries_absSummable_of_interval_subset
          a f hanalytic hr c hI hsummable hpowerSeries hs hsub m)
    have hNorm : Summable (fun n : ℕ => ‖term n‖) := by
      simpa [Real.norm_eq_abs] using hAbs
    have hTermSummable : Summable term := Summable.of_norm hNorm
    simpa [term] using hTermSummable
  have hd :
      ∀ m : ℕ,
        d m =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                  ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
                (b - (a : ℝ)) ^ n * c (n + m) := by
    intro m
    rfl
  have hShifted :
      ∀ x (hx : x ∈ Set.Ioo (b - s) (b + s)),
        Summable (fun m : ℕ => |d m * (x - b) ^ m|) ∧
          f ⟨x, hI (hsub hx)⟩ = ∑' m : ℕ, d m * (x - b) ^ m :=
    shifted_powerSeries_absConvergent_and_eq_on_interval
      a f hanalytic hr c hI hsummable hpowerSeries hs hsub d hdSummable hd
  have hseriesAtB :
      ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo (b - s) (b + s),
        Summable (fun m : ℕ => d m * (x - b) ^ m) ∧
          f ⟨x, hIb hx⟩ = ∑' m : ℕ, d m * (x - b) ^ m := by
    intro x hx
    have hShiftedAtx := hShifted x hx
    have hNorm : Summable (fun m : ℕ => ‖d m * (x - b) ^ m‖) := by
      simpa [Real.norm_eq_abs] using hShiftedAtx.1
    have hSummable : Summable (fun m : ℕ => d m * (x - b) ^ m) :=
      summable_norm_iff.mp hNorm
    refine ⟨hSummable, ?_⟩
    simpa [hIb] using hShiftedAtx.2
  exact
    helperForTheorem_4_2_3_isRealAnalyticAt_of_intervalSeriesData
      f ⟨b, hI hb⟩ hbInterior hs hIb d hseriesAtB


end Section02
end Chap04
