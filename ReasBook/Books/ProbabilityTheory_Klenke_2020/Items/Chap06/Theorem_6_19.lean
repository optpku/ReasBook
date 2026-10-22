/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter Set
open scoped ENNReal NNReal

universe u v

/-- Helper for Theorem 6.19: superlinear growth yields an eventual linear lower bound. -/
private lemma eventually_mul_le_of_superlinear {H : ℝ≥0 → ℝ≥0}
    (hH : Tendsto (fun x : ℝ≥0 ↦ (H x : ℝ) / (x : ℝ)) atTop atTop) (R : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ ⦃x : ℝ≥0⦄, A ≤ x → R * x ≤ H x := by
  have hR : ∀ᶠ x : ℝ≥0 in atTop, (R : ℝ) ≤ (H x : ℝ) / (x : ℝ) :=
    tendsto_atTop.mp hH (R : ℝ)
  rcases Filter.mem_atTop_sets.mp hR with ⟨A0, hA0⟩
  refine ⟨max A0 1, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ≥0) ≤ x := le_trans (le_max_right A0 1) hx
  have hx0 : (0 : ℝ) < x := by
    exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x by exact_mod_cast hx1)
  have hratio : (R : ℝ) ≤ (H x : ℝ) / (x : ℝ) := hA0 x (le_trans (le_max_left A0 1) hx)
  have hmul_real : (R : ℝ) * x ≤ H x := by
    exact (le_div_iff₀ hx0).mp hratio
  exact_mod_cast hmul_real

/-- Helper for Theorem 6.19: truncated excess is bounded by the corresponding tail indicator. -/
private lemma nnreal_sub_le_indicator_self (a y : ℝ≥0) :
    y - a ≤ ({t : ℝ≥0 | a ≤ t}.indicator id y) := by
  by_cases hay : a ≤ y
  · simp [Set.indicator, hay]
  · simp [Set.indicator, hay, tsub_eq_zero_of_le (le_of_not_ge hay)]

/-- Helper for Theorem 6.19: on `[0, ∞)`, `ℝ≥0` subtraction matches the real bump `max (x - a) 0`. -/
private lemma nnreal_sub_eq_max {x : ℝ} (hx : 0 ≤ x) (a : ℝ≥0) :
    (((x.toNNReal - a : ℝ≥0) : ℝ)) = max (x - a) 0 := by
  by_cases hxa : a ≤ x.toNNReal
  · have hxa' : (a : ℝ) ≤ x := by
      simpa [Real.toNNReal_of_nonneg hx] using hxa
    rw [max_eq_left (sub_nonneg.mpr hxa')]
    rw [NNReal.coe_sub hxa]
    simp [Real.toNNReal_of_nonneg hx]
  · have hxale : x ≤ (a : ℝ) := by
      by_contra hlt
      exact hxa (by simpa [Real.toNNReal_of_nonneg hx] using (lt_of_not_ge hlt).le)
    rw [max_eq_right (by linarith)]
    have hxa' : x.toNNReal ≤ a := by
      simpa [Real.toNNReal_of_nonneg hx] using hxale
    simp [tsub_eq_zero_of_le hxa']

/-- Helper for Theorem 6.19: because the cutoff sequence dominates the identity on `ℕ`, the
de la Vallée-Poussin series is actually a finite sum at every point. -/
private lemma de_la_Vallee_Poussin_series_eq_sum {a : ℕ → ℝ≥0}
    (ha_lower : ∀ n : ℕ, (n : ℝ≥0) ≤ a n) (x : ℝ≥0) {N : ℕ} (hN : x < N) :
    (∑' n : ℕ, (x - a n)) = ∑ n ∈ Finset.range N, (x - a n) := by
  refine tsum_eq_sum (fun n hn ↦ ?_)
  have hn' : N ≤ n := Nat.not_lt.mp (by simpa [Finset.mem_range] using hn)
  have hxlt : x < (n : ℝ≥0) := lt_of_lt_of_le hN (by exact_mod_cast hn')
  exact tsub_eq_zero_of_le (hxlt.le.trans (ha_lower n))

/-- Helper for Theorem 6.19: each bump function `x ↦ max (x - c) 0` is convex on `[0, ∞)`. -/
private lemma de_la_Vallee_Poussin_bump_convex (c : ℝ≥0) :
    ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ ↦ max (x - c) 0) := by
  simpa [Pi.sup_apply, sub_eq_add_neg] using
    (((convexOn_id (convex_Ici (0 : ℝ))).add_const (-(c : ℝ))).sup
      (convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))))

/-- Helper for Theorem 6.19: finite sums of the bump functions remain convex on `[0, ∞)`. -/
private lemma de_la_Vallee_Poussin_partial_sum_convex (a : ℕ → ℝ≥0) :
    ∀ N : ℕ,
      ConvexOn ℝ (Ici (0 : ℝ))
        (fun x : ℝ ↦ ∑ n ∈ Finset.range N, max (x - a n) 0) := by
  intro N
  induction N with
  | zero =>
      simpa using convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))
  | succ N ih =>
      simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
        ih.add (de_la_Vallee_Poussin_bump_convex (a N))

/-- Helper for Theorem 6.19: from uniform integrability one can choose an increasing cutoff
sequence with geometric control of the truncated excess integrals. -/
private lemma exists_monotone_cutoff_sequence
    {α : Type u} {ι : Type v} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ι → α → ℝ} (hUI : UniformIntegrable f 1 μ) :
    ∃ a : ℕ → ℝ≥0,
      Monotone a ∧
      (∀ n : ℕ, (n : ℝ≥0) ≤ a n) ∧
      ∀ n i,
        ∫⁻ x, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) ∂μ ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hspec :
      ∀ n : ℕ, ∃ C : ℝ≥0, ∀ i,
        eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := fun n ↦
    hUI.spec one_ne_zero ENNReal.one_ne_top (show 0 < (1 / 2 : ℝ) ^ (n + 1) by positivity)
  let c : ℕ → ℝ≥0 := fun n ↦
    Classical.choose (hspec n)
  let a : ℕ → ℝ≥0 := fun n ↦ (n : ℝ≥0) + (Finset.range (n + 1)).sup c
  refine ⟨a, ?_, ?_, ?_⟩
  · -- The finite supremum term and the linear term are both increasing.
    intro m n hmn
    refine add_le_add (by exact_mod_cast hmn) ?_
    exact Finset.sup_mono fun k hk ↦
      Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hmn)
  · intro n
    exact le_add_of_nonneg_right bot_le
  · intro n i
    have hc :
        eLpNorm ({x | c n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) :=
      (Classical.choose_spec (hspec n)) i
    have hca : c n ≤ a n := by
      refine le_trans ?_ (le_add_of_nonneg_left bot_le)
      exact Finset.le_sup (by simp)
    have hpoint :
        ∀ x, (‖f i x‖₊ - a n : ℝ≥0) ≤
          ({y : α | c n ≤ ‖f i y‖₊}.indicator (fun y ↦ ‖f i y‖₊) x) := by
      intro x
      exact (tsub_le_tsub_left hca _).trans <| nnreal_sub_le_indicator_self (c n) ‖f i x‖₊
    calc
      ∫⁻ x, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) ∂μ ≤
          ∫⁻ x, (({y : α | c n ≤ ‖f i y‖₊}.indicator (fun y ↦ ‖f i y‖₊) x : ℝ≥0) : ℝ≥0∞) ∂μ := by
            refine lintegral_mono fun x ↦ ?_
            exact ENNReal.coe_le_coe.2 (hpoint x)
      _ = eLpNorm ({x | c n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ := by
            rw [eLpNorm_one_eq_lintegral_enorm]
            simp_rw [enorm_eq_nnnorm, nnnorm_indicator_eq_indicator_nnnorm]
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := hc

/-- Helper for Theorem 6.19: the de la Vallée-Poussin series is monotone and convex. -/
private lemma de_la_Vallee_Poussin_series_mono_convex {a : ℕ → ℝ≥0}
    (ha_lower : ∀ n : ℕ, (n : ℝ≥0) ≤ a n) :
    Monotone (fun x : ℝ≥0 ↦ ∑' n : ℕ, (x - a n)) ∧
      ConvexOn ℝ (Ici (0 : ℝ))
        (fun x ↦ ((∑' n : ℕ, (x.toNNReal - a n) : ℝ≥0) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- Compare the common finite truncation at a level beyond `y`.
    intro x y hxy
    let N : ℕ := Nat.floor y + 1
    have hyN : y < N := by
      simpa [N] using Nat.lt_floor_add_one y
    have hxN : x < N := lt_of_le_of_lt hxy hyN
    have hxsum := de_la_Vallee_Poussin_series_eq_sum ha_lower x hxN
    have hysum := de_la_Vallee_Poussin_series_eq_sum ha_lower y hyN
    simpa [hxsum, hysum] using
      (Finset.sum_le_sum fun n hn ↦ tsub_le_tsub_right hxy _)
  · refine ⟨convex_Ici (0 : ℝ), ?_⟩
    intro x hx y hy a₁ b₁ ha₁ hb₁ hab
    let N : ℕ := Nat.floor (max x y) + 1
    have hmaxN : max x y < N := by
      simpa [N] using Nat.lt_floor_add_one (max x y)
    have hxN : x.toNNReal < N := by
      simpa [Real.toNNReal_of_nonneg hx] using lt_of_le_of_lt (le_max_left x y) hmaxN
    have hyN : y.toNNReal < N := by
      simpa [Real.toNNReal_of_nonneg hy] using lt_of_le_of_lt (le_max_right x y) hmaxN
    have hcombo_nonneg : 0 ≤ a₁ * x + b₁ * y := add_nonneg (mul_nonneg ha₁ hx) (mul_nonneg hb₁ hy)
    have hcombo_le : a₁ * x + b₁ * y ≤ max x y := Convex.combo_le_max x y ha₁ hb₁ hab
    have hcomboN : (a₁ * x + b₁ * y).toNNReal < N := by
      simpa [Real.toNNReal_of_nonneg hcombo_nonneg] using lt_of_le_of_lt hcombo_le hmaxN
    have hxsum :
        ((∑' n : ℕ, (x.toNNReal - a n) : ℝ≥0) : ℝ) =
          ∑ n ∈ Finset.range N, max (x - a n) 0 := by
      simpa [nnreal_sub_eq_max hx] using
        congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) (de_la_Vallee_Poussin_series_eq_sum ha_lower x.toNNReal hxN)
    have hysum :
        ((∑' n : ℕ, (y.toNNReal - a n) : ℝ≥0) : ℝ) =
          ∑ n ∈ Finset.range N, max (y - a n) 0 := by
      simpa [nnreal_sub_eq_max hy] using
        congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) (de_la_Vallee_Poussin_series_eq_sum ha_lower y.toNNReal hyN)
    have hcombosum :
        ((∑' n : ℕ, (((a₁ * x + b₁ * y).toNNReal) - a n) : ℝ≥0) : ℝ) =
          ∑ n ∈ Finset.range N, max (a₁ * x + b₁ * y - a n) 0 := by
      simpa [nnreal_sub_eq_max hcombo_nonneg] using
        congrArg (fun t : ℝ≥0 ↦ (t : ℝ))
          (de_la_Vallee_Poussin_series_eq_sum ha_lower (a₁ * x + b₁ * y).toNNReal hcomboN)
    -- Reduce the infinite series to one common finite convex partial sum.
    simpa [hxsum, hysum, hcombosum] using
      (de_la_Vallee_Poussin_partial_sum_convex a N).2 hx hy ha₁ hb₁ hab

/-- Helper for Theorem 6.19: the de la Vallée-Poussin series has superlinear growth. -/
private lemma de_la_Vallee_Poussin_series_superlinear {a : ℕ → ℝ≥0}
    (ha_mono : Monotone a) (ha_lower : ∀ n : ℕ, (n : ℝ≥0) ≤ a n) :
    Tendsto (fun x : ℝ≥0 ↦ ((∑' n : ℕ, (x - a n) : ℝ≥0) : ℝ) / (x : ℝ)) atTop atTop := by
  refine tendsto_atTop.mpr ?_
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * R)
  let A : ℝ≥0 := max 1 (2 * a n)
  filter_upwards [Filter.eventually_ge_atTop A] with x hx
  have hx1 : (1 : ℝ≥0) ≤ x := le_trans (le_max_left 1 (2 * a n)) hx
  have hx0 : (0 : ℝ) < x := by
    exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x by exact_mod_cast hx1)
  have hx2 : 2 * a n ≤ x := le_trans (le_max_right 1 (2 * a n)) hx
  let N : ℕ := Nat.floor x + 1
  have hxN : x < N := by
    simpa [N] using Nat.lt_floor_add_one x
  have hNle : n + 1 ≤ N := by
    have hxn : (n : ℝ≥0) ≤ x := by
      exact le_trans (ha_lower n) <| by
        have : a n ≤ x := by
          have hx2' : a n + a n ≤ x := by simpa [two_mul] using hx2
          exact le_trans (le_add_of_nonneg_left bot_le) hx2'
        exact this
    have hxn' : n < N := by
      exact_mod_cast (lt_of_le_of_lt hxn hxN : (n : ℝ≥0) < N)
    exact Nat.succ_le_of_lt hxn'
  have hsum_eq := de_la_Vallee_Poussin_series_eq_sum ha_lower x hxN
  have hterm :
      ∀ k ∈ Finset.range (n + 1), (x / 2 : ℝ≥0) ≤ x - a k := by
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hak : a k ≤ a n := ha_mono hk'
    have hanx : a n ≤ x := by
      have hx2' : a n + a n ≤ x := by simpa [two_mul] using hx2
      exact le_trans (le_add_of_nonneg_left bot_le) hx2'
    have hakx : a k ≤ x := le_trans hak hanx
    have hxk_real : (x : ℝ) / 2 ≤ x - a k := by
      have hx2_real : (2 : ℝ) * a n ≤ x := by exact_mod_cast hx2
      have hak_real : (a k : ℝ) ≤ a n := by exact_mod_cast hak
      nlinarith
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sub hakx]
    simpa using hxk_real
  have hpartial :
      ((n + 1 : ℝ≥0) * (x / 2)) ≤
        ∑ k ∈ Finset.range N, (x - a k) := by
    calc
      ((n + 1 : ℝ≥0) * (x / 2)) = ∑ k ∈ Finset.range (n + 1), (x / 2 : ℝ≥0) := by
        simp
      _ ≤ ∑ k ∈ Finset.range (n + 1), (x - a k) := by
        exact Finset.sum_le_sum fun k hk ↦ hterm k hk
      _ ≤ ∑ k ∈ Finset.range N, (x - a k) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset.mpr fun k hk ↦ Finset.mem_range.mpr (lt_of_lt_of_le hk hNle))
          (fun k hk hkn ↦ bot_le)
  have hratio :
      ((n + 1 : ℝ) / 2) ≤ ((∑' m : ℕ, (x - a m) : ℝ≥0) : ℝ) / (x : ℝ) := by
    have hsum_real :
        ((∑' m : ℕ, (x - a m) : ℝ≥0) : ℝ) =
          ∑ k ∈ Finset.range N, ((x - a k : ℝ≥0) : ℝ) := by
      simpa using congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) hsum_eq
    have hpartial' : ((n + 1 : ℝ) * (x / 2)) ≤ ((∑' m : ℕ, (x - a m) : ℝ≥0) : ℝ) := by
      have hpartial_real : (((n + 1 : ℝ≥0) * (x / 2) : ℝ≥0) : ℝ) ≤
          ((∑ k ∈ Finset.range N, (x - a k) : ℝ≥0) : ℝ) := by
        exact_mod_cast hpartial
      simpa [hsum_real] using hpartial_real
    have hmul : (((n + 1 : ℝ) / 2) * x) ≤ ((∑' m : ℕ, (x - a m) : ℝ≥0) : ℝ) := by
      nlinarith
    exact (le_div_iff₀ hx0).mpr hmul
  exact le_trans (by nlinarith) hratio

/-- Helper for Theorem 6.19: the de la Vallée-Poussin series has uniformly bounded integrals under
the geometric tail estimates for the cutoff sequence. -/
private lemma de_la_Vallee_Poussin_series_lintegral_bound
    {α : Type u} {ι : Type v} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ι → α → ℝ} (hf : ∀ i, Integrable (f i) μ) {a : ℕ → ℝ≥0}
    (ha_lower : ∀ n : ℕ, (n : ℝ≥0) ≤ a n)
    (ha_tail : ∀ n i,
      ∫⁻ x, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1))) :
    ∃ C : ℝ≥0, ∀ i,
      ∫⁻ x, ((∑' n : ℕ, (‖f i x‖₊ - a n) : ℝ≥0) : ℝ≥0∞) ∂μ ≤ C := by
  refine ⟨1, ?_⟩
  intro i
  -- Apply monotone convergence termwise to the nonnegative series defining `H`.
  have hseries :
      (fun x ↦ ((∑' n : ℕ, (‖f i x‖₊ - a n) : ℝ≥0) : ℝ≥0∞)) =
        fun x ↦ ∑' n : ℕ, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) := by
    funext x
    let N : ℕ := Nat.floor ‖f i x‖₊ + 1
    have hxN : ‖f i x‖₊ < N := by
      simpa [N] using Nat.lt_floor_add_one ‖f i x‖₊
    have hsumNN := de_la_Vallee_Poussin_series_eq_sum ha_lower ‖f i x‖₊ hxN
    have hsumEN :
        (∑' n : ℕ, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞)) =
          ∑ n ∈ Finset.range N, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) := by
      refine tsum_eq_sum (fun n hn ↦ ?_)
      have hn' : N ≤ n := Nat.not_lt.mp (by simpa [Finset.mem_range] using hn)
      have hxlt : ‖f i x‖₊ < (n : ℝ≥0) := lt_of_lt_of_le hxN (by exact_mod_cast hn')
      simp [tsub_eq_zero_of_le (hxlt.le.trans (ha_lower n))]
    rw [hsumEN]
    simpa using congrArg (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) hsumNN
  calc
    ∫⁻ x, ((∑' n : ℕ, (‖f i x‖₊ - a n) : ℝ≥0) : ℝ≥0∞) ∂μ =
        ∑' n : ℕ, ∫⁻ x, ((‖f i x‖₊ - a n : ℝ≥0) : ℝ≥0∞) ∂μ := by
          rw [hseries]
          rw [lintegral_tsum fun n ↦
            (((hf i).aestronglyMeasurable.nnnorm.aemeasurable).sub_const (a n)).coe_nnreal_ennreal]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
          exact ENNReal.tsum_le_tsum (ha_tail · i)
    _ = 1 := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_tsum_of_nonneg]
          · have hsum : Summable (fun n : ℕ ↦ ((1 / 2 : ℝ) ^ n)) := summable_geometric_two
            have hshift : (∑' n : ℕ, ((1 / 2 : ℝ) ^ (n + 1))) = 1 := by
              have hzeroadd := hsum.tsum_eq_zero_add
              rw [tsum_geometric_two, show ((1 / 2 : ℝ) ^ 0) = 1 by norm_num] at hzeroadd
              linarith
            simpa using hshift
          · intro n
            positivity
          · exact (summable_nat_add_iff 1).2 summable_geometric_two

/-- Theorem 6.19: on a finite measure space, an integrable family is uniformly integrable if and
only if it admits a de la Vallée Poussin test function with superlinear growth; this test function
may be chosen monotone on `[0, ∞)` and convex on `[0, ∞)`. -/
-- Proof sketch: For the forward direction, use the superlinear lower bound on `H x / x` for large
-- `x` to bound the tails of `‖f i‖` uniformly. For the reverse direction, choose a sequence
-- `aₙ → ∞` from uniform integrability and sum the convex tail functions `x ↦ max (x - aₙ) 0`.
theorem uniformIntegrable_iff_exists_de_la_Vallee_Poussin_function
    {α : Type u} {ι : Type v} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ι → α → ℝ} (hf : ∀ i, Integrable (f i) μ) :
    UniformIntegrable f 1 μ ↔
      ∃ H : ℝ≥0 → ℝ≥0,
        Monotone H ∧
        ConvexOn ℝ (Ici (0 : ℝ)) (fun x ↦ (H x.toNNReal : ℝ)) ∧
        Tendsto (fun x : ℝ≥0 ↦ (H x : ℝ) / (x : ℝ)) atTop atTop ∧
        ∃ C : ℝ≥0, ∀ i, ∫⁻ x, (H ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ C := by
  constructor
  · intro hUI
    rcases exists_monotone_cutoff_sequence hUI with ⟨a, ha_mono, ha_lower, ha_tail⟩
    let H : ℝ≥0 → ℝ≥0 := fun x ↦ ∑' n : ℕ, (x - a n)
    obtain ⟨hH_mono, hH_convex⟩ := de_la_Vallee_Poussin_series_mono_convex ha_lower
    have hH_growth :
        Tendsto (fun x : ℝ≥0 ↦ (H x : ℝ) / (x : ℝ)) atTop atTop :=
      de_la_Vallee_Poussin_series_superlinear ha_mono ha_lower
    rcases de_la_Vallee_Poussin_series_lintegral_bound hf ha_lower ha_tail with ⟨C, hC⟩
    refine ⟨H, hH_mono, hH_convex, hH_growth, C, fun i ↦ ?_⟩
    simpa [H] using hC i
  · intro hH
    rcases hH with ⟨H, _, _, hH_growth, C, hC⟩
    refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun i ↦ (hf i).aestronglyMeasurable) ?_
    intro ε hε
    let εnn : ℝ≥0 := ⟨ε, hε.le⟩
    let R : ℝ≥0 := (C + 1) * εnn⁻¹
    obtain ⟨A, hA⟩ := eventually_mul_le_of_superlinear hH_growth R
    refine ⟨A, fun i ↦ ?_⟩
    let s : Set α := {x | A ≤ ‖f i x‖₊}
    -- Use the superlinear lower bound to dominate the tail by the `H`-integral.
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      ∫⁻ x, ‖s.indicator (f i) x‖ₑ ∂μ ≤
          ∫⁻ x, ENNReal.ofReal (ε / ((C : ℝ) + 1)) * (H ‖f i x‖₊ : ℝ≥0∞) ∂μ := by
            refine lintegral_mono fun x ↦ ?_
            by_cases hx : x ∈ s
            · rw [enorm_eq_nnnorm, nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
              have hdom : R * ‖f i x‖₊ ≤ H ‖f i x‖₊ := hA hx
              have hdom_real : (((C : ℝ) + 1) * ε⁻¹) * ‖f i x‖₊ ≤ H ‖f i x‖₊ := by
                change ((R : ℝ) * ‖f i x‖₊ ≤ H ‖f i x‖₊)
                simpa [R, εnn]
                  using (show ((R : ℝ≥0) * ‖f i x‖₊ ≤ H ‖f i x‖₊) from hdom)
              have hC1 : 0 < (C : ℝ) + 1 := by positivity
              have hmul :=
                mul_le_mul_of_nonneg_left hdom_real (show 0 ≤ ε / ((C : ℝ) + 1) by positivity)
              have hcancel :
                  (ε / ((C : ℝ) + 1)) * ((((C : ℝ) + 1) * ε⁻¹) * ‖f i x‖₊) = ‖f i x‖₊ := by
                field_simp [hε.ne', hC1.ne']
              have hscaled_real :
                  ‖f i x‖₊ ≤ (ε / ((C : ℝ) + 1)) * H ‖f i x‖₊ := by
                rw [← hcancel]
                simpa [mul_assoc] using hmul
              have hscaled_real_abs :
                  |f i x| ≤ (ε / ((C : ℝ) + 1)) * H ‖f i x‖₊ := by
                simpa [coe_nnnorm, Real.norm_eq_abs] using hscaled_real
              have hlhs :
                  ((‖f i x‖₊ : ℝ≥0∞)) = ENNReal.ofReal |f i x| := by
                rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg (f i x))]
                apply congrArg (fun t : ℝ≥0 ↦ (t : ℝ≥0∞))
                apply Subtype.ext
                simp [Real.norm_eq_abs]
              have hscaled :
                  ENNReal.ofReal |f i x| ≤
                    ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * H ‖f i x‖₊) := by
                exact ENNReal.ofReal_le_ofReal hscaled_real_abs
              have hscaled' :
                  ((‖f i x‖₊ : ℝ≥0∞)) ≤
                    ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * H ‖f i x‖₊) := by
                simpa [hlhs] using hscaled
              have hprod :
                  ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * H ‖f i x‖₊) =
                    ENNReal.ofReal (ε / ((C : ℝ) + 1)) * (H ‖f i x‖₊ : ℝ≥0∞) := by
                have hprod' :
                    ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * (H ‖f i x‖₊ : ℝ)) =
                      ENNReal.ofReal (ε / ((C : ℝ) + 1)) *
                        ENNReal.ofReal (H ‖f i x‖₊ : ℝ) :=
                  ENNReal.ofReal_mul (show 0 ≤ ε / ((C : ℝ) + 1) by positivity)
                simpa using hprod'
              rw [hprod] at hscaled'
              exact hscaled'
            · rw [enorm_eq_nnnorm, nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_notMem hx]
              simp
      _ ≤ ENNReal.ofReal ε := by
        calc
          ∫⁻ x, ENNReal.ofReal (ε / ((C : ℝ) + 1)) * (H ‖f i x‖₊ : ℝ≥0∞) ∂μ =
              ENNReal.ofReal (ε / ((C : ℝ) + 1)) * ∫⁻ x, (H ‖f i x‖₊ : ℝ≥0∞) ∂μ := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (ε / ((C : ℝ) + 1)) * C := by
                gcongr
                exact hC i
        _ ≤ ENNReal.ofReal ε := by
                have hmul :
                    ENNReal.ofReal (ε / ((C : ℝ) + 1)) * (C : ℝ≥0∞) =
                      ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * (C : ℝ)) := by
                  have hmul' :
                      ENNReal.ofReal ((ε / ((C : ℝ) + 1)) * (C : ℝ)) =
                        ENNReal.ofReal (ε / ((C : ℝ) + 1)) * ENNReal.ofReal (C : ℝ) :=
                    ENNReal.ofReal_mul (show 0 ≤ ε / ((C : ℝ) + 1) by positivity)
                  simpa using hmul'.symm
                rw [hmul]
                exact ENNReal.ofReal_le_ofReal <| by
                  have hC1 : 0 < (C : ℝ) + 1 := by positivity
                  have hscale : ε / ((C : ℝ) + 1) * (C : ℝ) ≤
                      ε / ((C : ℝ) + 1) * ((C : ℝ) + 1) := by
                    have hcoef : 0 ≤ ε / ((C : ℝ) + 1) := by positivity
                    refine mul_le_mul_of_nonneg_left ?_ hcoef
                    nlinarith
                  have hEq : ε / ((C : ℝ) + 1) * ((C : ℝ) + 1) = ε := by
                    field_simp [hC1.ne']
                  exact hscale.trans_eq hEq
