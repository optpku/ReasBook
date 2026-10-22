/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10Core
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_11Shim

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 23.10: package independence and one-base-coordinate identical distribution
into the chapter's `IsIID` shorthand. -/
theorem isIID_of_iIndepFun_identDistribBase
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) :
    IsIID X P := by
  -- Proof comment: retain the independence hypothesis and compare any two coordinates through the
  -- common reference variable `X 0`.
  refine ⟨hindep, ?_⟩
  intro i j
  exact (hident i).trans (hident j).symm

/-- Helper for Example 23.10: an i.i.d. real family is almost everywhere measurable in each
coordinate, which is the measurability package needed by the owner empirical-mean API. -/
theorem aemeasurable_of_isIID
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hIID : IsIID X P) :
    ∀ n, AEMeasurable (X n) P := by
  -- Proof comment: each coordinate has the same law as `X 0`, so the standard
  -- `IdentDistrib.aemeasurable_fst` projection gives the required a.e.-measurability.
  intro n
  exact (hIID.identDistrib n 0).aemeasurable_fst

/-- Helper for Example 23.10: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`limsup` along `atTop`. -/
theorem limsup_succPNat_eq
    {α : Type*} [ConditionallyCompleteLattice α] [OrderBot α]
    (f : ℕ+ → α) :
    Filter.limsup (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.limsup f atTop := by
  -- Proof comment: `Nat.succPNat` is the order-isomorphism from `ℕ` onto `ℕ+`, so it preserves
  -- the `atTop` filter and therefore the `limsup`.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.limsup_comp]
  simpa using congrArg (Filter.limsup f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Example 23.10: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`liminf` along `atTop`. -/
theorem liminf_succPNat_eq
    {α : Type*} [ConditionallyCompleteLattice α] [OrderTop α]
    (f : ℕ+ → α) :
    Filter.liminf (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.liminf f atTop := by
  -- Proof comment: the same order-isomorphism argument works for `liminf`.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.liminf_comp]
  simpa using congrArg (Filter.liminf f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Example 23.10: the Legendre-transform rate function is nonnegative because the
distinguished tilt `t = 0` contributes the value `0` to the defining supremum. -/
theorem legendreCgfRateFunction_nonneg
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (x : ℝ) :
    (0 : EReal) ≤ legendreCgfRateFunction X P x := by
  -- Proof comment: evaluate the supremum-defining family at `t = 0` and use `cgf X P 0 = 0`.
  rw [legendreCgfRateFunction]
  let f : ℝ → EReal := fun t ↦ ((t * x - cgf X P t : ℝ) : EReal)
  have hmem : f 0 ∈ Set.range f := ⟨0, rfl⟩
  have hzero : f 0 = 0 := by
    simp [f, cgf_zero]
  simpa [hzero] using (le_sSup hmem)

/-- Helper for Example 23.10: finite exponential moments on all of `ℝ` put `0` in the interior of
the exponential-integrability domain, hence the variable is integrable. -/
theorem integrable_of_allExponentialMoments
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P) :
    Integrable Y P := by
  -- Proof comment: the all-tilts assumption makes the exponential-integrability set equal to
  -- `univ`, so `0` lies in its interior and the standard moment theorem yields integrability.
  have hzero_mem : (0 : ℝ) ∈ interior (integrableExpSet Y P) := by
    simp [integrableExpSet, hmgf]
  exact ProbabilityTheory.integrable_of_mem_interior_integrableExpSet hzero_mem

/-- Helper for Example 23.10: the common coordinate `X 0` is integrable once every exponential
moment exists. -/
theorem integrable_X0_of_allExponentialMoments
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) :
    Integrable (X 0) P := by
  -- Proof comment: this is the coordinate-specialized instance of the generic integrability
  -- criterion above.
  simpa using integrable_of_allExponentialMoments (P := P) (Y := X 0) hmgf

/-- Helper for Example 23.10: Jensen's inequality gives the affine lower bound
`t * P[Y] ≤ cgf Y P t` for every real tilt `t`. -/
theorem expectation_mul_le_cgf
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    (t : ℝ) :
    t * P[Y] ≤ cgf Y P t := by
  -- Proof comment: apply Jensen to the convex function `exp` and the tilted variable `t * Y`,
  -- then take logarithms on both sides.
  have hY_int : Integrable Y P := integrable_of_allExponentialMoments (P := P) (Y := Y) hmgf
  have hMul_int : Integrable (fun ω ↦ t * Y ω) P := hY_int.const_mul t
  have hJensen :
      Real.exp (∫ ω, t * Y ω ∂P) ≤ ∫ ω, Real.exp (t * Y ω) ∂P := by
    simpa using
      (ConvexOn.map_integral_le (μ := P) (s := Set.univ)
        (f := fun ω ↦ t * Y ω) (g := Real.exp)
        convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
        hMul_int (hmgf t))
  have hmgf_pos : 0 < mgf Y P t := mgf_pos (hmgf t)
  rw [cgf]
  rw [Real.le_log_iff_exp_le hmgf_pos]
  calc
    Real.exp (t * P[Y]) = Real.exp (∫ ω, t * Y ω ∂P) := by
      rw [← MeasureTheory.integral_const_mul]
    _ ≤ ∫ ω, Real.exp (t * Y ω) ∂P := hJensen
    _ = mgf Y P t := rfl

/-- Helper for Example 23.10: when the mean is zero, the Legendre-transform rate vanishes at
`0`. -/
theorem legendreCgfRateFunction_zero_of_mean_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    (hmean0 : P[Z] = 0) :
    legendreCgfRateFunction Z P 0 = 0 := by
  -- Proof comment: Jensen shows every affine summand at `x = 0` is nonpositive, while the zero
  -- tilt still forces the Legendre supremum to be nonnegative.
  apply le_antisymm
  · rw [legendreCgfRateFunction]
    refine sSup_le ?_
    rintro _ ⟨t, rfl⟩
    have hcgf_nonneg : 0 ≤ cgf Z P t := by
      simpa [hmean0] using expectation_mul_le_cgf (P := P) (Y := Z) hmgf t
    have hsummand :
        t * (0 : ℝ) - cgf Z P t = -cgf Z P t := by
      ring
    -- Proof comment: rewrite the `x = 0` affine summand to the plain negative cumulant term
    -- before casting the real inequality into `EReal`.
    have hsummand_nonpos : t * (0 : ℝ) - cgf Z P t ≤ 0 := by
      rw [hsummand]
      exact neg_nonpos.mpr hcgf_nonneg
    have hcast : (((t * (0 : ℝ) - cgf Z P t : ℝ)) : EReal) ≤ 0 := by
      exact_mod_cast hsummand_nonpos
    simpa using hcast
  · simpa using legendreCgfRateFunction_nonneg (P := P) (X := Z) (0 : ℝ)

/-- Helper for Example 23.10: if the mean of `Y` lies strictly below `x`, then the rate at `x`
is already attained from nonnegative tilts. -/
theorem legendreCgfRateFunction_le_nonnegTiltSup_of_mean_lt
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    {x : ℝ} (hx : P[Y] < x) :
    legendreCgfRateFunction Y P x ≤
      ⨆ t : Set.Ici (0 : ℝ), (((((t : ℝ) * x) - cgf Y P (t : ℝ) : ℝ)) : EReal) := by
  -- Proof comment: negative tilts cannot beat the value `0` once `x` lies to the right of the
  -- mean, so restricting the Legendre supremum to `t ≥ 0` loses no mass.
  let f : Set.Ici (0 : ℝ) → EReal := fun t ↦
    (((((t : ℝ) * x) - cgf Y P (t : ℝ) : ℝ)) : EReal)
  have hf_bdd : BddAbove (Set.range f) := ⟨⊤, by
    rintro _ ⟨t, rfl⟩
    simp [f]⟩
  rw [legendreCgfRateFunction]
  refine sSup_le ?_
  rintro _ ⟨t, rfl⟩
  by_cases ht : 0 ≤ t
  · simpa [f] using (le_ciSup hf_bdd ⟨t, ht⟩ : f ⟨t, ht⟩ ≤ ⨆ s : Set.Ici (0 : ℝ), f s)
  · have hlinear : t * P[Y] ≤ cgf Y P t := expectation_mul_le_cgf (P := P) (Y := Y) hmgf t
    have ht_lt : t < 0 := lt_of_not_ge ht
    have hnonpos : t * x - cgf Y P t ≤ 0 := by
      -- Proof comment: Jensen bounds the affine summand by `t * (x - P[Y])`, which is nonpositive
      -- for negative `t` when `x` is to the right of the mean.
      calc
        t * x - cgf Y P t ≤ t * x - t * P[Y] := by linarith
        _ = t * (x - P[Y]) := by ring
        _ ≤ 0 := by nlinarith
    have hcast : (((t * x - cgf Y P t : ℝ)) : EReal) ≤ 0 := by
      exact_mod_cast hnonpos
    have hzero_le : (0 : EReal) ≤ ⨆ s : Set.Ici (0 : ℝ), f s := by
      have hzero_mem : f (⟨0, by simp⟩ : Set.Ici (0 : ℝ)) ≤ ⨆ s : Set.Ici (0 : ℝ), f s :=
        le_ciSup hf_bdd ⟨0, by simp⟩
      have hzero_eval : f (⟨0, by simp⟩ : Set.Ici (0 : ℝ)) = 0 := by
        change (((0 : ℝ) * x - cgf Y P 0 : ℝ) : EReal) = 0
        simp [cgf_zero]
      rwa [hzero_eval] at hzero_mem
    exact hcast.trans hzero_le

/-- Helper for Example 23.10: every nonnegative tilt contributes an affine lower bound to the rate
function at any larger point. -/
theorem affineSummand_le_legendreCgfRateFunction_of_nonnegTilt
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} {x y t : ℝ}
    (ht : 0 ≤ t) (hxy : x ≤ y) :
    (((t * x - cgf Y P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Y P y := by
  -- Proof comment: monotonicity of the affine summand in the space variable reduces the claim to
  -- the defining Legendre-supremum bound at `y`.
  have hmono : t * x - cgf Y P t ≤ t * y - cgf Y P t := by
    nlinarith
  have hpoint :
      (((t * y - cgf Y P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Y P y := by
    rw [legendreCgfRateFunction]
    exact le_sSup ⟨t, rfl⟩
  exact le_trans (by exact_mod_cast hmono) hpoint

/-- Helper for Example 23.10: once `x` lies to the right of the mean, the Legendre-transform rate
is monotone on `Set.Ici x`. -/
theorem legendreCgfRateFunction_monoOn_Ici_of_mean_lt
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    {x y : ℝ} (hx : P[Y] < x) (hxy : x ≤ y) :
    legendreCgfRateFunction Y P x ≤ legendreCgfRateFunction Y P y := by
  -- Proof comment: first restrict the Legendre supremum at `x` to nonnegative tilts, then compare
  -- each such tilt directly at the larger point `y`.
  let f : Set.Ici (0 : ℝ) → EReal := fun t ↦
    (((((t : ℝ) * x) - cgf Y P (t : ℝ) : ℝ)) : EReal)
  have hx_nonneg :
      legendreCgfRateFunction Y P x ≤ ⨆ t : Set.Ici (0 : ℝ), f t := by
    simpa [f] using
      legendreCgfRateFunction_le_nonnegTiltSup_of_mean_lt (P := P) (Y := Y) hmgf hx
  have hsSup_le : (⨆ t : Set.Ici (0 : ℝ), f t) ≤ legendreCgfRateFunction Y P y := by
    refine ciSup_le ?_
    intro t
    simpa [f] using
      affineSummand_le_legendreCgfRateFunction_of_nonnegTilt
        (P := P) (Y := Y) (x := x) (y := y) (t := (t : ℝ)) t.property hxy
  exact le_trans hx_nonneg hsSup_le

/-- Helper for Example 23.10: shifting the closed upper-tail event by `x` turns it into the
nonnegative centered partial-sum event for the sequence `i ↦ X i - x`. -/
theorem shiftedUpperTailEvent_eq_nonnegativeCenteredEvent
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) :
    P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω} =
      P {ω | 0 ≤ partialSum (fun i ω ↦ X i ω - x) (n + 1) ω} := by
  -- Proof comment: rewrite the centered partial sum as `partialSum X - x * (n + 1)` and then
  -- move the threshold across the subtraction.
  congr 1
  ext ω
  have hsum_shift :
      partialSum (fun i ω ↦ X i ω - x) (n + 1) ω =
        partialSum X (n + 1) ω - x * (n + 1 : ℝ) := by
    calc
      partialSum (fun i ω ↦ X i ω - x) (n + 1) ω
          = ∑ i ∈ Finset.range (n + 1), (X i ω - x) := by
              simp [partialSum]
      _ = (∑ i ∈ Finset.range (n + 1), X i ω) - ∑ _i ∈ Finset.range (n + 1), x := by
            rw [Finset.sum_sub_distrib]
      _ = partialSum X (n + 1) ω - x * (n + 1 : ℝ) := by
            simp [partialSum, mul_comm]
  change x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω ↔
    0 ≤ partialSum (fun i ω ↦ X i ω - x) (n + 1) ω
  rw [hsum_shift]
  constructor <;> intro h <;> linarith

/-- Helper for Example 23.10: if a centered marginal is not almost everywhere nonpositive, then
some strictly positive level set has positive mass. -/
theorem exists_positiveLevel_posMeasure_of_not_ae_nonpos
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0) :
    ∃ a > 0, 0 < P {ω | a ≤ Z ω} := by
  let levelSet : ℕ → Set Ω := fun n ↦ {ω | (1 / (n + 1 : ℝ)) ≤ Z ω}
  have hIoi_ne_zero : P {ω | 0 < Z ω} ≠ 0 := by
    -- Proof comment: failing the a.e.-nonpositive branch means the strictly positive set has
    -- nonzero measure.
    rw [← MeasureTheory.frequently_ae_iff]
    simpa [not_le] using hZ_not_nonpos
  have hIoi_eq : {ω | 0 < Z ω} = ⋃ n : ℕ, levelSet n := by
    -- Proof comment: every positive real dominates `1 / (n + 1)` for some `n`.
    ext ω
    constructor
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < Z ω from hω)
      exact Set.mem_iUnion.2 ⟨n, hn.le⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      have hpos : 0 < (1 / (n + 1 : ℝ)) := by positivity
      exact lt_of_lt_of_le hpos hn
  obtain ⟨n, hn⟩ :=
    MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null
      (μ := P) (s := levelSet) (by simpa [hIoi_eq] using hIoi_ne_zero)
  refine ⟨1 / (n + 1 : ℝ), by positivity, ?_⟩
  simpa [levelSet] using hn

/-- Helper for Example 23.10: a strictly negative mean forces some strictly negative level set to
carry positive mass. -/
theorem exists_negativeLevel_posMeasure_of_mean_lt_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmean : P[Z] < 0) :
    ∃ b > 0, 0 < P {ω | Z ω ≤ -b} := by
  have hNotAeNonneg : ¬ ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    -- Proof comment: an almost everywhere nonnegative variable cannot have negative mean.
    intro hAeNonneg
    have hMeanNonneg : 0 ≤ P[Z] := by
      simpa using integral_nonneg_of_ae hAeNonneg
    linarith
  have hNotAeNonposNeg : ¬ ∀ᵐ ω ∂P, -Z ω ≤ 0 := by
    -- Proof comment: apply the previous contradiction to the negated variable.
    intro hAeNonposNeg
    apply hNotAeNonneg
    simpa using hAeNonposNeg
  obtain ⟨b, hb_pos, hb_mass⟩ :=
    exists_positiveLevel_posMeasure_of_not_ae_nonpos (P := P) (Z := fun ω ↦ -Z ω)
      hNotAeNonposNeg
  refine ⟨b, hb_pos, ?_⟩
  have hSet : {ω | b ≤ -Z ω} = {ω | Z ω ≤ -b} := by
    -- Proof comment: the positive lower level set for `-Z` is exactly the negative upper level
    -- set for `Z`.
    ext ω
    constructor
    · intro h
      change b ≤ -Z ω at h
      change Z ω ≤ -b
      linarith
    · intro h
      change Z ω ≤ -b at h
      change b ≤ -Z ω
      linarith
  simpa [hSet] using hb_mass

/-- Helper for Example 23.10: the normalized partial-sum map is a.e.-measurable once every
coordinate is. -/
theorem aemeasurable_normalizedPartialSum
    {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P)
    (n : ℕ+) :
    AEMeasurable (fun ω ↦ partialRealSum X n ω / (n : ℝ)) P := by
  -- Proof comment: the numerator is a finite sum of a.e.-measurable coordinates, and dividing by
  -- the constant `n` is just constant multiplication.
  have hsum' : AEMeasurable (∑ i ∈ Finset.range (n : ℕ), X i) P := by
    simpa using
      Finset.aemeasurable_sum (Finset.range (n : ℕ)) fun i _ ↦ hXae i
  have hsum : AEMeasurable (partialRealSum X n) P := by
    refine hsum'.congr ?_
    filter_upwards with ω
    simp [partialRealSum, Finset.sum_apply]
  simpa [div_eq_mul_inv, mul_comm] using hsum.mul_const ((n : ℝ)⁻¹)

/-- Helper for Example 23.10: measurable events under the `n + 1`st normalized partial-sum law are
the corresponding preimage events for the explicit `0`-based empirical mean. -/
theorem normalizedPartialSumLaw_mapApply_zeroBasedAverage
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P)
    {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) s =
      P {ω |
        Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ) ∈ s} := by
  -- Proof comment: rewrite the normalized law as the relevant pushforward and then apply
  -- `Measure.map_apply` to expose the source event.
  have hmap :
      normalizedPartialSumLaw X P (Nat.succPNat n) =
        Measure.map
          (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
    simpa using normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage P X n
  have hAvg :
      AEMeasurable
        (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
    have hsum : AEMeasurable (∑ i ∈ Finset.range (n + 1), X i) P := by
      exact Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ ↦ hXae i
    simpa [div_eq_mul_inv, mul_comm] using hsum.mul_const ((n + 1 : ℝ)⁻¹)
  rw [hmap]
  rw [Measure.map_apply_of_aemeasurable hAvg hs]
  rfl

/-- Helper for Example 23.10: the positive-indexed normalized partial-sum law assigns the closed
half-line `Set.Ici x` exactly the source-facing upper-tail event for `partialSum X (n + 1)`. -/
theorem normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ici x) =
      P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω} := by
  -- Proof comment: specialize the generic pushforward bridge to the closed ray and clear the
  -- positive denominator `n + 1`.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (P := P) (X := X) hXae measurableSet_Ici]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by positivity
  simp [partialSum, le_div_iff₀ hn]

/-- Helper for Example 23.10: the positive-indexed normalized partial-sum law assigns the open
half-line `Set.Ioi x` exactly the strict source-facing upper-tail event for `partialSum X (n + 1)`.
-/
theorem normalizedPartialSumLaw_openHalfline_eq_strictUpperTailEvent
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ioi x) =
      P {ω | x * (n + 1 : ℝ) < partialSum X (n + 1) ω} := by
  -- Proof comment: the open-ray case is the same transport, now with the strict inequality after
  -- clearing the positive denominator.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (P := P) (X := X) hXae measurableSet_Ioi]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by positivity
  simp [partialSum, lt_div_iff₀ hn]

/-- Helper for Example 23.10: the positive-indexed normalized partial-sum law assigns the closed
left half-line `Set.Iic x` exactly the source-facing lower-tail event for `partialSum X (n + 1)`.
-/
theorem normalizedPartialSumLaw_closedLeftHalfline_eq_lowerTailEvent
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Iic x) =
      P {ω | partialSum X (n + 1) ω ≤ x * (n + 1 : ℝ)} := by
  -- Proof comment: specialize the pushforward bridge to the closed left ray and clear the
  -- positive denominator `n + 1`.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (P := P) (X := X) hXae measurableSet_Iic]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by positivity
  simp [partialSum, div_le_iff₀ hn]

/-- Helper for Example 23.10: the positive-indexed normalized partial-sum law assigns the open
left half-line `Set.Iio x` exactly the strict source-facing lower-tail event for `partialSum X
(n + 1)`. -/
theorem normalizedPartialSumLaw_openLeftHalfline_eq_strictLowerTailEvent
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Iio x) =
      P {ω | partialSum X (n + 1) ω < x * (n + 1 : ℝ)} := by
  -- Proof comment: the open left-ray case is the same pushforward identity, now with the strict
  -- inequality after clearing the positive denominator.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (P := P) (X := X) hXae measurableSet_Iio]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by positivity
  simp [partialSum, div_lt_iff₀ hn]

/-- Helper for Example 23.10: recentering each coordinate by `m` translates the normalized
partial-sum law by the same constant. -/
theorem normalizedPartialSumLaw_sub_const_eq_map_add_const
    {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXae : ∀ n, AEMeasurable (X n) P)
    (m : ℝ) (n : ℕ+) :
    normalizedPartialSumLaw X P n =
      Measure.map (fun y : ℝ ↦ y + m)
        (normalizedPartialSumLaw (fun k ω ↦ X k ω - m) P n) := by
  -- Proof comment: the centered partial sum is `partialRealSum X n - n * m`, so dividing by `n`
  -- and adding back `m` recovers the original normalized sum.
  have hYae : ∀ k, AEMeasurable (fun ω ↦ X k ω - m) P := by
    intro k
    simpa using (hXae k).sub measurable_const.aemeasurable
  have hYnorm :
      AEMeasurable
        (fun ω ↦ partialRealSum (fun k ω ↦ X k ω - m) n ω / (n : ℝ)) P :=
    aemeasurable_normalizedPartialSum (P := P) (X := fun k ω ↦ X k ω - m) hYae n
  rw [normalizedPartialSumLaw, normalizedPartialSumLaw]
  calc
    Measure.map (fun ω ↦ partialRealSum X n ω / (n : ℝ)) P
        =
      Measure.map
        ((fun y : ℝ ↦ y + m) ∘ fun ω ↦ partialRealSum (fun k ω ↦ X k ω - m) n ω / (n : ℝ)) P := by
          congr 1
          ext ω
          have hsum_shift :
              partialRealSum (fun k ω ↦ X k ω - m) n ω =
                partialRealSum X n ω - (n : ℝ) * m := by
            calc
              partialRealSum (fun k ω ↦ X k ω - m) n ω
                  = ∑ i ∈ Finset.range (n : ℕ), (X i ω - m) := by
                      simp [partialRealSum]
              _ = (∑ i ∈ Finset.range (n : ℕ), X i ω) - ∑ _i ∈ Finset.range (n : ℕ), m := by
                    rw [Finset.sum_sub_distrib]
              _ = partialRealSum X n ω - (n : ℝ) * m := by
                    simp [partialRealSum, mul_comm]
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast (show (n : ℕ) ≠ 0 from ne_of_gt n.2)
          rw [show
            ((fun y : ℝ ↦ y + m) ∘ fun ω ↦ partialRealSum (fun k ω ↦ X k ω - m) n ω / (n : ℝ)) ω =
              (partialRealSum X n ω - (n : ℝ) * m) / (n : ℝ) + m by
                rw [Function.comp_apply, hsum_shift]]
          field_simp [hn0]
          ring
    _ =
      Measure.map (fun y : ℝ ↦ y + m)
        (Measure.map (fun ω ↦ partialRealSum (fun k ω ↦ X k ω - m) n ω / (n : ℝ)) P) := by
          simpa [Function.comp] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := P) ((measurable_id.add measurable_const).aemeasurable) hYnorm).symm

/-- Helper for Example 23.10: shifting the coordinate by `m` shifts the Legendre-transform rate by
the same amount on the space variable. -/
theorem shiftedCoordinate_rate_eq_originalRate_add
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    (m z : ℝ) :
    legendreCgfRateFunction (fun ω ↦ X 0 ω - m) P z =
      legendreCgfRateFunction (X 0) P (z + m) := by
  -- Proof comment: rewrite the shifted cumulant-generating function via `mgf_const_add`, then the
  -- affine summands in the two Legendre transforms coincide term by term.
  rw [legendreCgfRateFunction, legendreCgfRateFunction]
  congr 1
  ext t
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    have hcgf :
        cgf (fun ω ↦ X 0 ω - m) P u = cgf (X 0) P u - u * m := by
      calc
        cgf (fun ω ↦ X 0 ω - m) P u = cgf (fun ω ↦ (-m) + X 0 ω) P u := by
          congr 1
          ext ω
          ring
        _ = Real.log (Real.exp (u * (-m)) * mgf (X 0) P u) := by
          rw [cgf, mgf_const_add]
        _ = u * (-m) + cgf (X 0) P u := by
          rw [Real.log_mul (Real.exp_pos _).ne' (mgf_pos (hmgf u)).ne', Real.log_exp, cgf]
        _ = cgf (X 0) P u - u * m := by
          ring
    have hreal :
        u * z - cgf (fun ω ↦ X 0 ω - m) P u =
          u * (z + m) - cgf (X 0) P u := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    have hcgf :
        cgf (fun ω ↦ X 0 ω - m) P u = cgf (X 0) P u - u * m := by
      calc
        cgf (fun ω ↦ X 0 ω - m) P u = cgf (fun ω ↦ (-m) + X 0 ω) P u := by
          congr 1
          ext ω
          ring
        _ = Real.log (Real.exp (u * (-m)) * mgf (X 0) P u) := by
          rw [cgf, mgf_const_add]
        _ = u * (-m) + cgf (X 0) P u := by
          rw [Real.log_mul (Real.exp_pos _).ne' (mgf_pos (hmgf u)).ne', Real.log_exp, cgf]
        _ = cgf (X 0) P u - u * m := by
          ring
    have hreal :
        u * (z + m) - cgf (X 0) P u =
          u * z - cgf (fun ω ↦ X 0 ω - m) P u := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm

/-- Helper for Example 23.10: the shifted rate identity specialized to the `x - m` coordinate form
used by the translation step. -/
theorem shiftedCoordinate_rate_sub_eq_originalRate
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    (m x : ℝ) :
    legendreCgfRateFunction (fun ω ↦ X 0 ω - m) P (x - m) =
      legendreCgfRateFunction (X 0) P x := by
  -- Proof comment: this is the previous shift lemma evaluated at `z = x - m`.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    shiftedCoordinate_rate_eq_originalRate_add (P := P) (X := X) hmgf m (x - m)

/-- Helper for Example 23.10: negating the coordinate and the space variable leaves the
Legendre-transform rate unchanged. -/
theorem legendreCgfRateFunction_negArg_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} (x : ℝ) :
    legendreCgfRateFunction (fun ω ↦ -Y ω) P (-x) =
      legendreCgfRateFunction Y P x := by
  -- Proof comment: `cgf (-Y)` is `cgf Y` at the negated tilt, so the Legendre-transform summands
  -- match after the change of variables `t ↦ -t`.
  rw [legendreCgfRateFunction, legendreCgfRateFunction]
  congr 1
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    have hcgf : cgf (fun ω ↦ -Y ω) P t = cgf Y P (-t) := by
      simpa using (cgf_neg (X := Y) (μ := P) (t := t))
    have hreal :
        t * (-x) - cgf (fun ω ↦ -Y ω) P t = (-t) * x - cgf Y P (-t) := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    have hcgf : cgf (fun ω ↦ -Y ω) P (-t) = cgf Y P t := by
      simpa using (cgf_neg (X := Y) (μ := P) (t := -t))
    have hreal :
        t * x - cgf Y P t = (-t) * (-x) - cgf (fun ω ↦ -Y ω) P (-t) := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm

/-- Helper for Example 23.10: translating a set by `m` and precomposing the rate with `x ↦ x - m`
produce the same image set under the rate function. -/
theorem image_rateSubConst_eq_image_preimage_addConst
    (I : ℝ → EReal) (s : Set ℝ) (m : ℝ) :
    (fun x ↦ I (x - m)) '' s = I '' ((fun y : ℝ ↦ y + m) ⁻¹' s) := by
  -- Proof comment: the witnesses are transported back and forth by the inverse translation
  -- `x ↦ x - m`.
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - m, ?_, rfl⟩
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y + m, ?_, ?_⟩
    · simpa using hy
    · simp

/-- Helper for Example 23.10: an LDP is invariant under translating every law by a fixed
constant, with the rate precomposed by the inverse translation. -/
theorem SatisfiesLargeDeviationPrinciple.map_add_const
    {μ : ℕ+ → Measure ℝ} {I : ℝ → EReal}
    (hLDP : SatisfiesLargeDeviationPrinciple μ I)
    (m : ℝ) :
    SatisfiesLargeDeviationPrinciple
      (fun n ↦ Measure.map (fun y : ℝ ↦ y + m) (μ n))
      (fun x ↦ I (x - m)) := by
  -- Proof comment: closed and open sets are pulled back along the homeomorphism `x ↦ x + m`,
  -- while the rate images match by the inverse translation on witnesses.
  refine ⟨?_, ?_⟩
  · intro s hs
    have hsPre : IsClosed ((fun y : ℝ ↦ y + m) ⁻¹' s) := by
      exact hs.preimage (continuous_id.add continuous_const)
    have hUpper := (SatisfiesLargeDeviationPrinciple.upper hLDP) _ hsPre
    have hMass :
        ∀ n : ℕ+, (Measure.map (fun y : ℝ ↦ y + m) (μ n)) s =
          μ n ((fun y : ℝ ↦ y + m) ⁻¹' s) := by
      intro n
      simpa using
        (Measure.map_apply (μ := μ n) (f := fun y : ℝ ↦ y + m)
          (s := s) (measurable_id.add measurable_const) hs.measurableSet)
    have hSeq :
        (fun n : ℕ+ ↦ ENNReal.log ((Measure.map (fun y : ℝ ↦ y + m) (μ n)) s) / (n : EReal)) =
          (fun n : ℕ+ ↦ ENNReal.log (μ n ((fun y : ℝ ↦ y + m) ⁻¹' s)) / (n : EReal)) := by
      funext n
      simp [hMass n]
    calc
      Filter.limsup
          (fun n : ℕ+ ↦ ENNReal.log ((Measure.map (fun y : ℝ ↦ y + m) (μ n)) s) / (n : EReal))
          atTop
          =
        Filter.limsup
          (fun n : ℕ+ ↦ ENNReal.log (μ n ((fun y : ℝ ↦ y + m) ⁻¹' s)) / (n : EReal))
          atTop := by simp [hSeq]
      _ ≤ -sInf (I '' ((fun y : ℝ ↦ y + m) ⁻¹' s)) := hUpper
      _ = -sInf ((fun x ↦ I (x - m)) '' s) := by
            rw [image_rateSubConst_eq_image_preimage_addConst (I := I) (s := s) (m := m)]
  · intro s hs
    have hsPre : IsOpen ((fun y : ℝ ↦ y + m) ⁻¹' s) := by
      exact hs.preimage (continuous_id.add continuous_const)
    have hLower := (SatisfiesLargeDeviationPrinciple.lower hLDP) _ hsPre
    have hMass :
        ∀ n : ℕ+, (Measure.map (fun y : ℝ ↦ y + m) (μ n)) s =
          μ n ((fun y : ℝ ↦ y + m) ⁻¹' s) := by
      intro n
      simpa using
        (Measure.map_apply (μ := μ n) (f := fun y : ℝ ↦ y + m)
          (s := s) (measurable_id.add measurable_const) hs.measurableSet)
    have hSeq :
        (fun n : ℕ+ ↦ ENNReal.log ((Measure.map (fun y : ℝ ↦ y + m) (μ n)) s) / (n : EReal)) =
          (fun n : ℕ+ ↦ ENNReal.log (μ n ((fun y : ℝ ↦ y + m) ⁻¹' s)) / (n : EReal)) := by
      funext n
      simp [hMass n]
    calc
      -sInf ((fun x ↦ I (x - m)) '' s)
          = -sInf (I '' ((fun y : ℝ ↦ y + m) ⁻¹' s)) := by
              rw [image_rateSubConst_eq_image_preimage_addConst (I := I) (s := s) (m := m)]
      _ ≤
        Filter.liminf
          (fun n : ℕ+ ↦ ENNReal.log (μ n ((fun y : ℝ ↦ y + m) ⁻¹' s)) / (n : EReal))
          atTop := hLower
      _ =
        Filter.liminf
          (fun n : ℕ+ ↦ ENNReal.log ((Measure.map (fun y : ℝ ↦ y + m) (μ n)) s) / (n : EReal))
          atTop := by simp [hSeq]

/-- Helper for Example 23.10: the strong law forces mean-zero normalized partial sums eventually
into every open interval around `0`. -/
theorem ae_eventually_normalizedPartialSum_mem_Ioo_of_mean_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hindep : iIndepFun Y P)
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P P)
    (hmean0 : P[Y 0] = 0)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P)
    {x : ℝ} (hx : 0 < x) :
    ∀ᵐ ω ∂P,
      ∀ᶠ n : ℕ in atTop,
        partialRealSum Y (Nat.succPNat n) ω / ((Nat.succPNat n : ℕ+) : ℝ) ∈ Set.Ioo (-x) x := by
  have hY0_int : Integrable (Y 0) P :=
    integrable_of_allExponentialMoments (P := P) (Y := Y 0) hmgf
  have hpairwise : Pairwise fun i j ↦ Y i ⟂ᵢ[P] Y j := by
    -- Proof comment: pairwise independence is the two-coordinate shadow of the given
    -- `iIndepFun` hypothesis.
    intro i j hij
    exact hindep.indepFun hij
  have hslln := ProbabilityTheory.strong_law_ae_real Y hY0_int hpairwise hident
  filter_upwards [hslln] with ω hω
  have hω0 : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [hmean0] using hω
  have hAtZero : (0 : ℝ) ∈ Set.Ioo (-x) x := by
    constructor <;> linarith
  have hEventually :
      ∀ᶠ m : ℕ in atTop, (∑ i ∈ Finset.range m, Y i ω) / (m : ℝ) ∈ Set.Ioo (-x) x := by
    -- Proof comment: apply the strong law at the neighborhood `(-x, x)` of the mean `0`.
    exact hω0.eventually (Ioo_mem_nhds (show -x < (0 : ℝ) by linarith) hx)
  have hShifted :
      ∀ᶠ n : ℕ in atTop, (∑ i ∈ Finset.range (n + 1), Y i ω) / (n + 1 : ℝ) ∈ Set.Ioo (-x) x :=
    by
      simpa [Nat.cast_add] using (Filter.tendsto_add_atTop_nat 1).eventually hEventually
  -- Proof comment: rewrite the shifted Cesàro averages back into the chapter's positive-indexed
  -- `partialRealSum` notation.
  simpa [partialRealSum, Nat.succPNat_coe] using hShifted

/-- Helper for Example 23.10: negating the sequence turns the closed right ray at `-x` into the
closed left ray at `x`. -/
theorem normalizedPartialSumLaw_neg_closedHalfline_eq_closedLeftHalfline
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hYae : ∀ n, AEMeasurable (Y n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw (fun k ω ↦ -Y k ω) P (Nat.succPNat n)) (Set.Ici (-x)) =
      (normalizedPartialSumLaw Y P (Nat.succPNat n)) (Set.Iic x) := by
  have hNegAe : ∀ k, AEMeasurable (fun ω ↦ -Y k ω) P := by
    -- Proof comment: almost-everywhere measurability is preserved by pointwise negation.
    intro k
    simpa using (hYae k).neg
  rw [normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent
    (P := P) (X := fun k ω ↦ -Y k ω) hNegAe (-x) n]
  rw [normalizedPartialSumLaw_closedLeftHalfline_eq_lowerTailEvent
    (P := P) (X := Y) hYae x n]
  congr 1
  ext ω
  have hsum_neg :
      partialSum (fun k ω ↦ -Y k ω) (n + 1) ω = -partialSum Y (n + 1) ω := by
    -- Proof comment: summing the negated coordinates is the negation of the original partial sum.
    simp [partialSum, Finset.sum_neg_distrib]
  change (-x) * (n + 1 : ℝ) ≤ partialSum (fun k ω ↦ -Y k ω) (n + 1) ω ↔
    partialSum Y (n + 1) ω ≤ x * (n + 1 : ℝ)
  rw [hsum_neg]
  constructor <;> intro h <;> linarith

/-- Helper for Example 23.10: a closed set avoiding `0` is contained in two closed rays that are
separated from the origin by a positive gap. -/
theorem subset_leftRightRays_of_isClosed_zero_not_mem
    {s : Set ℝ} (hsClosed : IsClosed s) (h0s : 0 ∉ s) :
    ∃ δ > 0, s ⊆ Set.Iic (-δ) ∪ Set.Ici δ := by
  have hsOpen : IsOpen sᶜ := hsClosed.isOpen_compl
  have h0mem : 0 ∈ sᶜ := h0s
  rcases Metric.isOpen_iff.mp hsOpen 0 h0mem with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  by_cases hxLeft : x ≤ -δ
  · exact Or.inl hxLeft
  by_cases hxRight : δ ≤ x
  · exact Or.inr hxRight
  -- Proof comment: otherwise `x` lies in the open interval `(-δ, δ)`, hence in the ball around
  -- `0` that is contained in `sᶜ`, contradicting `x ∈ s`.
  have hxgt : -δ < x := lt_of_not_ge hxLeft
  have hxlt : x < δ := lt_of_not_ge hxRight
  have hxBall : x ∈ Metric.ball (0 : ℝ) δ := by
    show dist x 0 < δ
    simpa [Real.dist_eq, abs_lt] using And.intro hxgt hxlt
  have hxComp : x ∈ sᶜ := hball hxBall
  exact False.elim (hxComp hx)

/-- Helper for Example 23.10: every point of an open set is contained in an open interval that
still lies inside the set. -/
theorem exists_Ioo_subset_of_isOpen_mem
    {s : Set ℝ} (hsOpen : IsOpen s) {x : ℝ} (hx : x ∈ s) :
    ∃ δ > 0, Set.Ioo (x - δ) (x + δ) ⊆ s := by
  rcases Metric.isOpen_iff.mp hsOpen x hx with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  apply hball
  -- Proof comment: points of the interval satisfy `|y - x| < δ`, so they belong to the metric
  -- ball furnished by openness.
  show dist y x < δ
  have habs : |y - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  simpa [Real.dist_eq] using habs

/-- Helper for Example 23.10: under finite exponential moments, the owner Legendre-Fenchel rate
from Theorem 23.11 agrees, as an `EReal`-valued function, with `legendreCgfRateFunction`. -/
theorem ereal_ownerLegendreFenchelRate_eq_legendreCgfRateFunction
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P) :
    (fun x ↦
        (((legendreFenchelRateFunction (Λ(Y; P)) x).toENNReal : ENNReal) : EReal)) =
      legendreCgfRateFunction Y P := by
  -- Proof comment: first identify the two rate functions in `EReal`, then remove the owner
  -- `toENNReal` coercion using nonnegativity of the Cramér rate.
  funext x
  have hRatePoint :
      legendreFenchelRateFunction (Λ(Y; P)) x = legendreCgfRateFunction Y P x := by
    simpa using
      congrArg (fun f : ℝ → EReal ↦ f x)
        (legendreFenchelRateFunction_extendedLogMomentGeneratingFunction_eq_legendreCgfRateFunction
          (X := Y) (P := P) hmgf)
  rw [hRatePoint]
  exact EReal.coe_toENNReal (legendreCgfRateFunction_nonneg (P := P) (X := Y) x)

/-- Helper for Example 23.10: the owner scaled logarithmic mass of an arbitrary set rewrites to
the chapter's `ℕ+`-indexed normalized-partial-sum logarithmic mass. -/
private theorem ownerScaledLogMass_eq_normalizedLogMass
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hYae : ∀ n, AEMeasurable (Y n) P) (s : Set ℝ) :
    scaledLogMassAlong
        (fun n ↦ (empiricalMeanLaw Y P hYae n : Measure ℝ))
        (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
          have hn : 0 < (n + 1 : ℝ) := by
            positivity
          simpa using inv_pos.mpr hn⟩)
        s =
      (fun n : ℕ ↦
        ENNReal.log ((normalizedPartialSumLaw Y P (Nat.succPNat n)) s) /
          ((Nat.succPNat n : ℕ+) : EReal)) := by
  funext n
  -- Proof comment: first identify the owner law with the chapter's `n + 1`st normalized law, then
  -- rewrite the speed factor `((n + 1) : ℝ)⁻¹` as division by `Nat.succPNat n`.
  rw [scaledLogMassAlong_def,
    empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw (P := P) (X := Y) hYae n]
  simp [Nat.succPNat_coe, div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Example 23.10: the shim owner theorem transports directly to the chapter's
closed-set upper bound for centered normalized partial sums. -/
private theorem centeredClosedUpperBound_of_ownerLDP
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hindep : iIndepFun Y P)
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P) :
    HasLargeDeviationUpperBound (normalizedPartialSumLaw Y P)
      (legendreCgfRateFunction (Y 0) P) := by
  let hIID : IsIID Y P := isIID_of_iIndepFun_identDistribBase hindep hident
  let hYae : ∀ n, AEMeasurable (Y n) P := aemeasurable_of_isIID hIID
  let hOwner :=
    cramer_empiricalMean_largeDeviationPrinciple (P := P) (X := Y) hIID
  intro C hC
  have hUpper :
      Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw Y P hYae n : Measure ℝ))
            (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
              have hn : 0 < (n + 1 : ℝ) := by
                positivity
              simpa using inv_pos.mpr hn⟩)
            C)
          atTop ≤
        -sInf
          ((fun x ↦
              ((((legendreFenchelRateFunction (Λ(Y 0; P)) x).toENNReal : ENNReal) : EReal))) '' C) :=
    hOwner.closed_upper_bound hC
  -- Proof comment: the generic normalization lemma handles the reindexing, and the rate-side
  -- coercion bridge replaces the owner Legendre-Fenchel rate by the chapter's `legendreCgfRate`.
  rw [ownerScaledLogMass_eq_normalizedLogMass (P := P) (Y := Y) hYae C] at hUpper
  rw [limsup_succPNat_eq
    (f := fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw Y P n) C) / (n : EReal))] at hUpper
  rw [ereal_ownerLegendreFenchelRate_eq_legendreCgfRateFunction
    (P := P) (Y := Y 0) hmgf] at hUpper
  exact hUpper

/-- Helper for Example 23.10: the shim owner theorem transports directly to the chapter's
open-set lower bound for centered normalized partial sums. -/
private theorem centeredOpenLowerBound_of_ownerLDP
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hindep : iIndepFun Y P)
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P) :
    HasLargeDeviationLowerBound (normalizedPartialSumLaw Y P)
      (legendreCgfRateFunction (Y 0) P) := by
  let hIID : IsIID Y P := isIID_of_iIndepFun_identDistribBase hindep hident
  let hYae : ∀ n, AEMeasurable (Y n) P := aemeasurable_of_isIID hIID
  let hOwner :=
    cramer_empiricalMean_largeDeviationPrinciple (P := P) (X := Y) hIID
  intro U hU
  have hLower :
      -sInf
          ((fun x ↦
              ((((legendreFenchelRateFunction (Λ(Y 0; P)) x).toENNReal : ENNReal) : EReal))) '' U) ≤
        Filter.liminf
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw Y P hYae n : Measure ℝ))
            (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
              have hn : 0 < (n + 1 : ℝ) := by
                positivity
              simpa using inv_pos.mpr hn⟩)
            U)
          atTop :=
    hOwner.open_lower_bound hU
  -- Proof comment: this is the same transport as in the closed-set branch, but now for the
  -- owner open-set lower bound.
  rw [ownerScaledLogMass_eq_normalizedLogMass (P := P) (Y := Y) hYae U] at hLower
  rw [liminf_succPNat_eq
    (f := fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw Y P n) U) / (n : EReal))] at hLower
  rw [ereal_ownerLegendreFenchelRate_eq_legendreCgfRateFunction
    (P := P) (Y := Y 0) hmgf] at hLower
  exact hLower

/-- Helper for Example 23.10: the remaining proof burden is the mean-zero version assembled from
the centered half-line bounds and the standard open/closed-set reductions. -/
private theorem centeredNormalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hindep : iIndepFun Y P)
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P P)
    (hmean0 : P[Y 0] = 0)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P) :
    SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw Y P)
      (legendreCgfRateFunction (Y 0) P) := by
  -- Route correction: instead of rebuilding the exact half-line theorem inside this file, transport
  -- the shim owner's open/closed bounds once and assemble the centered LDP directly.
  refine ⟨?_, ?_⟩
  · -- Proof comment: the closed-set branch is the owner theorem's upper bound rewritten in the
    -- chapter's `ℕ+` normal form.
    exact centeredClosedUpperBound_of_ownerLDP
      (P := P) (Y := Y) hindep hident hmgf
  · -- Proof comment: the open-set branch is transported in the same normalized coordinates.
    exact centeredOpenLowerBound_of_ownerLDP
      (P := P) (Y := Y) hindep hident hmgf

-- Proof sketch: combine Cramér's theorem for half-lines with the monotonicity and convexity of
-- the Legendre-transform rate function, use the law of large numbers to control intervals
-- containing `0`, and then pass from intervals to arbitrary closed and open sets by the standard
-- reduction arguments from the example.
/-- Example 23.10: the laws of the normalized partial sums of an i.i.d. real sequence with finite
exponential moments satisfy the large deviation principle on `ℝ`, with rate function given by the
Legendre transform of the cumulant-generating function of the common law. -/
theorem normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) :
    SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw X P)
      (legendreCgfRateFunction (X 0) P) := by
  -- Route correction: the proof now isolates the true remaining blocker in the centered textbook
  -- argument. The recentering transport from the mean-zero case back to the original sequence is
  -- carried out completely inside this file.
  let hIID : IsIID X P := isIID_of_iIndepFun_identDistribBase hindep hident
  let m : ℝ := P[X 0]
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X n ω - m
  have hYindep : iIndepFun Y P := by
    -- Proof comment: independence is stable under the fixed measurable shift `z ↦ z - m`.
    simpa [Y, Function.comp] using
      hIID.iIndepFun.comp (fun _ ↦ fun z : ℝ ↦ z - m)
        (fun _ ↦ measurable_id.sub measurable_const)
  have hYident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    -- Proof comment: identical distribution is preserved by the same measurable shift.
    intro n
    simpa [Y, Function.comp] using
      (hident n).comp (measurable_id.sub measurable_const)
  have hYmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P := by
    -- Proof comment: the exponential moment of the centered coordinate differs from the original
    -- one only by the harmless constant factor `exp (-t * m)`.
    intro t
    have hscaled :
        Integrable (fun ω ↦ Real.exp (-t * m) * Real.exp (t * X 0 ω)) P := by
      exact (hmgf t).const_mul (Real.exp (-t * m))
    convert hscaled using 1
    ext ω
    have hmul : t * (Y 0 ω) = -t * m + t * X 0 ω := by
      simp [Y]
      ring
    rw [hmul, Real.exp_add]
  have hX0_int : Integrable (X 0) P :=
    integrable_X0_of_allExponentialMoments (P := P) (X := X) hmgf
  have hYmean0 : P[Y 0] = 0 := by
    -- Proof comment: subtracting the mean centers the first coordinate by construction.
    calc
      P[Y 0] = ∫ ω, X 0 ω + (-m) ∂P := by
        simp [Y, sub_eq_add_neg]
      _ = P[X 0] + ∫ _ : Ω, (-m) ∂P := by
        rw [MeasureTheory.integral_add hX0_int (integrable_const (-m))]
      _ = P[X 0] - m := by
        have hconst : ∫ _ : Ω, (-m) ∂P = -m := by
          simp
        rw [hconst]
        ring
      _ = 0 := by
        simp [m]
  have hCentered :
      SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw Y P)
        (legendreCgfRateFunction (Y 0) P) :=
    centeredNormalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
      (P := P) (Y := Y) hYindep hYident hYmean0 hYmgf
  have hTransported :
      SatisfiesLargeDeviationPrinciple
        (fun n ↦ Measure.map (fun y : ℝ ↦ y + m) (normalizedPartialSumLaw Y P n))
        (fun x ↦ legendreCgfRateFunction (Y 0) P (x - m)) :=
    SatisfiesLargeDeviationPrinciple.map_add_const hCentered m
  have hLaw :
      (fun n ↦ normalizedPartialSumLaw X P n) =
        (fun n ↦ Measure.map (fun y : ℝ ↦ y + m) (normalizedPartialSumLaw Y P n)) := by
    -- Proof comment: the normalized law of `X` is exactly the translate of the centered
    -- normalized law of `Y`.
    funext n
    exact normalizedPartialSumLaw_sub_const_eq_map_add_const
      (P := P) (X := X) (aemeasurable_of_isIID hIID) m n
  have hRate :
      (fun x ↦ legendreCgfRateFunction (Y 0) P (x - m)) =
        legendreCgfRateFunction (X 0) P := by
    -- Proof comment: the centered rate is the original rate evaluated after undoing the shift.
    funext x
    simpa [Y] using
      shiftedCoordinate_rate_sub_eq_originalRate (P := P) (X := X) hmgf m x
  simpa [hLaw, hRate] using hTransported

end ProbabilityTheory
