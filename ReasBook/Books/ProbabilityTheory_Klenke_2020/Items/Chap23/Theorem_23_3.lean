/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

variable {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Helper for Theorem 23.3: the `n + 1`st normalized partial-sum law is the pushforward of `P`
by the `0`-based empirical mean `ω ↦ (∑ i ∈ range (n + 1), X i ω) / (n + 1)`. -/
private theorem normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    normalizedPartialSumLaw X P ⟨n + 1, Nat.succ_pos _⟩ =
      Measure.map
        (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  -- Proof comment: unfold the chapter definition and identify `partialRealSum` with the explicit
  -- `0`-based finite sum.
  rw [normalizedPartialSumLaw]
  congr 1
  ext ω
  simp [partialRealSum]

/-- Helper for Theorem 23.3: the `0`-based empirical mean over the first `n + 1` coordinates is
almost everywhere measurable once the coordinates are. -/
private theorem empiricalMean_aemeasurable
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    AEMeasurable
      (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  -- Proof comment: finite sums preserve almost-everywhere measurability, and division by the
  -- positive scalar `n + 1` is a constant multiplication.
  have hsum : AEMeasurable (∑ i ∈ Finset.range (n + 1), X i) P := by
    exact Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ ↦ hXae i
  simpa [div_eq_mul_inv, mul_comm] using hsum.mul_const ((n + 1 : ℝ)⁻¹)

/-- Helper for Theorem 23.3: an i.i.d. family is coordinatewise almost-everywhere measurable. -/
private theorem iidAEMeasurable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    ∀ n, AEMeasurable (X n) P :=
  fun n ↦ (hX_iid.identDistrib n 0).aemeasurable_fst

/-- Helper for Theorem 23.3: every measurable event under the `n + 1`st normalized partial-sum law
is the corresponding preimage event for the `0`-based empirical mean. -/
private lemma normalizedPartialSumLaw_mapApply_zeroBasedAverage
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P) {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) s =
      P {ω |
        Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ) ∈ s} := by
  -- Proof comment: unfold the normalized law into the empirical-mean pushforward and then read
  -- off the event by `Measure.map_apply`.
  have hmap :
      normalizedPartialSumLaw X P (Nat.succPNat n) =
        Measure.map
          (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
    simpa using normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage P X n
  rw [hmap]
  rw [Measure.map_apply_of_aemeasurable
    (empiricalMean_aemeasurable P X (iidAEMeasurable P X hX_iid) n) hs]
  rfl

/-- Helper for Theorem 23.3: the positive-indexed normalized partial-sum law assigns the closed
half-line `Set.Ici x` exactly the source-facing upper-tail event for `partialSum X (n + 1)`. -/
private lemma normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ici x) =
      P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω} := by
  -- Proof comment: specialize the generic pushforward bridge to `Set.Ici x`, then clear the
  -- positive denominator `n + 1`.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (X := X) (P := P) hX_iid
    measurableSet_Ici]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by
    positivity
  simp [partialSum, (le_div_iff₀ hn)]

/-- Helper for Theorem 23.3: the positive-indexed normalized partial-sum law assigns the open
half-line `Set.Ioi x` exactly the strict source-facing upper-tail event for `partialSum X (n + 1)`.
-/
private lemma normalizedPartialSumLaw_openHalfline_eq_strictUpperTailEvent
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ioi x) =
      P {ω | x * (n + 1 : ℝ) < partialSum X (n + 1) ω} := by
  -- Proof comment: the open-halfline case is the same transport, with a strict inequality after
  -- clearing the positive denominator.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage (X := X) (P := P) hX_iid
    measurableSet_Ioi]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by
    positivity
  simp [partialSum, (lt_div_iff₀ hn)]

/-- Helper for Theorem 23.3: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`limsup` along `atTop`. -/
private lemma limsup_succPNat_eq {α : Type*} [ConditionallyCompleteLattice α] [OrderBot α]
    (f : ℕ+ → α) :
    Filter.limsup (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.limsup f atTop := by
  -- Proof comment: `Nat.succPNat` is an order isomorphism from `ℕ` onto `ℕ+`, so reindexing only
  -- changes the presentation of the `atTop` filter.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.limsup_comp]
  simpa using congrArg (Filter.limsup f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Theorem 23.3: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`liminf` along `atTop`. -/
private lemma liminf_succPNat_eq {α : Type*} [ConditionallyCompleteLattice α] [OrderTop α]
    (f : ℕ+ → α) :
    Filter.liminf (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.liminf f atTop := by
  -- Proof comment: the same order-isomorphism argument applies to `liminf`.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.liminf_comp]
  simpa using congrArg (Filter.liminf f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Theorem 23.3: finite exponential moments on all of `ℝ` imply integrability. -/
private lemma integrable_of_allExponentialMoments
    [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P) :
    Integrable Y P := by
  -- Proof comment: if every real tilt is admissible, then `0` belongs to the interior of
  -- `integrableExpSet`, and the standard moment theorem gives integrability.
  have hzero_mem : (0 : ℝ) ∈ interior (integrableExpSet Y P) := by
    simp [integrableExpSet, hmgf]
  exact ProbabilityTheory.integrable_of_mem_interior_integrableExpSet hzero_mem

/-- Helper for Theorem 23.3: finite exponential moments on all of `ℝ` put `0` in the interior of
the exponential-integrability domain, hence `X 0` is integrable. -/
private lemma integrable_X0_of_allExponentialMoments
    [IsProbabilityMeasure P]
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) :
    Integrable (X 0) P := by
  -- Proof comment: this is the coordinate-specialized instance of the generic exponential-moment
  -- integrability lemma above.
  simpa using integrable_of_allExponentialMoments (P := P) (Y := X 0) hmgf

/-- Helper for Theorem 23.3: Jensen's inequality gives the affine lower bound
`t * P[Y] ≤ cgf Y P t` for every real tilt `t`. -/
private lemma expectation_mul_le_cgf
    [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    (t : ℝ) :
    t * P[Y] ≤ cgf Y P t := by
  have hY_int : Integrable Y P := integrable_of_allExponentialMoments (P := P) (Y := Y) hmgf
  have hMul_int : Integrable (fun ω ↦ t * Y ω) P := hY_int.const_mul t
  have hJensen :
      Real.exp (∫ ω, t * Y ω ∂P) ≤ ∫ ω, Real.exp (t * Y ω) ∂P := by
    -- Proof comment: apply Jensen to the convex function `exp` and the tilted variable `t * Y`.
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

/-- Helper for Theorem 23.3: shifting the coordinate by the constant `x` moves the rate from the
boundary point `0` back to the original evaluation point `x`. -/
private lemma shiftedCoordinate_rateAtZero_eq_originalRate
    [IsProbabilityMeasure P]
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    (x : ℝ) :
    legendreCgfRateFunction (fun ω ↦ X 0 ω - x) P 0 =
      legendreCgfRateFunction (X 0) P x := by
  -- Proof comment: rewrite the cumulant-generating function of the shifted coordinate via the
  -- multiplicative `mgf_add_const` formula, then simplify the affine summands in the Legendre
  -- transform.
  rw [legendreCgfRateFunction, legendreCgfRateFunction]
  congr 1
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    have hcgf :
        cgf (fun ω ↦ X 0 ω - x) P t = cgf (X 0) P t - t * x := by
      calc
        cgf (fun ω ↦ X 0 ω - x) P t = cgf (fun ω ↦ (-x) + X 0 ω) P t := by
          congr 1
          ext ω
          ring
        _ = Real.log (Real.exp (t * (-x)) * mgf (X 0) P t) := by
          rw [cgf, mgf_const_add]
        _ = t * (-x) + cgf (X 0) P t := by
          rw [Real.log_mul (Real.exp_pos _).ne' (mgf_pos (hmgf t)).ne', Real.log_exp, cgf]
        _ = cgf (X 0) P t - t * x := by
          ring
    have hreal :
        t * (0 : ℝ) - cgf (fun ω ↦ X 0 ω - x) P t = t * x - cgf (X 0) P t := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    have hcgf :
        cgf (fun ω ↦ X 0 ω - x) P t = cgf (X 0) P t - t * x := by
      calc
        cgf (fun ω ↦ X 0 ω - x) P t = cgf (fun ω ↦ (-x) + X 0 ω) P t := by
          congr 1
          ext ω
          ring
        _ = Real.log (Real.exp (t * (-x)) * mgf (X 0) P t) := by
          rw [cgf, mgf_const_add]
        _ = t * (-x) + cgf (X 0) P t := by
          rw [Real.log_mul (Real.exp_pos _).ne' (mgf_pos (hmgf t)).ne', Real.log_exp, cgf]
        _ = cgf (X 0) P t - t * x := by
          ring
    have hreal :
        t * x - cgf (X 0) P t = t * (0 : ℝ) - cgf (fun ω ↦ X 0 ω - x) P t := by
      rw [hcgf]
      ring
    exact congrArg (fun y : ℝ ↦ (y : EReal)) hreal.symm

/-- Helper for Theorem 23.3: if the mean of `Y` lies strictly below `x`, then the Legendre-transform
rate at `x` is already attained from nonnegative tilts. -/
private lemma legendreCgfRateFunction_le_nonnegTiltSup_of_mean_lt
    [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    {x : ℝ} (hx : P[Y] < x) :
    legendreCgfRateFunction Y P x ≤
      ⨆ t : Set.Ici (0 : ℝ), (((((t : ℝ) * x) - cgf Y P (t : ℝ) : ℝ)) : EReal) := by
  let f : Set.Ici (0 : ℝ) → EReal := fun t ↦
    (((((t : ℝ) * x) - cgf Y P (t : ℝ) : ℝ)) : EReal)
  have hf_bdd : BddAbove (Set.range f) := ⟨⊤, by
    rintro _ ⟨t, rfl⟩
    simp [f]⟩
  rw [legendreCgfRateFunction]
  refine sSup_le ?_
  rintro _ ⟨t, rfl⟩
  by_cases ht : 0 ≤ t
  · -- Proof comment: nonnegative tilts already belong to the restricted supremum family.
    simpa [f] using (le_ciSup hf_bdd ⟨t, ht⟩ : f ⟨t, ht⟩ ≤ ⨆ s : Set.Ici (0 : ℝ), f s)
  · have hlinear : t * P[Y] ≤ cgf Y P t := expectation_mul_le_cgf (P := P) (Y := Y) hmgf t
    have ht_lt : t < 0 := lt_of_not_ge ht
    have hnonpos : t * x - cgf Y P t ≤ 0 := by
      -- Proof comment: for negative tilts, Jensen bounds the affine summand by
      -- `t * (x - P[Y]) ≤ 0`, so restricting to `t ≥ 0` loses no mass in the supremum.
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

/-- Helper for Theorem 23.3: every nonnegative tilt contributes an affine lower bound to the rate
function at any larger point. -/
private lemma affineSummand_le_legendreCgfRateFunction_of_nonnegTilt
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {x y t : ℝ}
    (ht : 0 ≤ t) (hxy : x ≤ y) :
    (((t * x - cgf Y P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Y P y := by
  have hmono : t * x - cgf Y P t ≤ t * y - cgf Y P t := by
    nlinarith
  have hpoint :
      (((t * y - cgf Y P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Y P y := by
    rw [legendreCgfRateFunction]
    exact le_sSup ⟨t, rfl⟩
  exact le_trans (by exact_mod_cast hmono) hpoint

/-- Helper for Theorem 23.3: once `x` lies to the right of the mean, the Legendre-transform rate is
monotone on `Set.Ici x`. -/
private lemma legendreCgfRateFunction_monoOn_Ici_of_mean_lt
    [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P)
    {x y : ℝ} (hx : P[Y] < x) (hxy : x ≤ y) :
    legendreCgfRateFunction Y P x ≤ legendreCgfRateFunction Y P y := by
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

/-- Helper for Theorem 23.3: the shifted upper-tail sequence already satisfies the `limsup`
half of the desired asymptotic. -/
private lemma upperTail_shifted_limsup_le_neg_rate
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    {x : ℝ} (hx : P[X 0] < x) :
    Filter.limsup
        (fun n : ℕ ↦ ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1))
        atTop ≤
      -legendreCgfRateFunction (X 0) P x := by
  let I : ℝ → EReal := legendreCgfRateFunction (X 0) P
  have hUpper :
      Filter.limsup
          (fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw X P n) (Set.Ici x)) / (n : EReal))
          atTop ≤
        -sInf (I '' Set.Ici x) := by
    exact
      (SatisfiesLargeDeviationPrinciple.upper
        (normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
          (P := P) (X := X) hX_iid.iIndepFun (fun i ↦ (hX_iid.identDistrib i 0)) hmgf))
        (Set.Ici x) isClosed_Ici
  rw [← limsup_succPNat_eq
    (f := fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw X P n) (Set.Ici x)) / (n : EReal))]
    at hUpper
  have hseq :
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1)) =
        (fun n : ℕ ↦ ENNReal.log ((normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ici x)) /
          ((n + 1 : ℝ) : EReal)) := by
    funext n
    rw [normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent (X := X) (P := P) hX_iid x n]
    simp
  have hRate_le :
      I x ≤ sInf (I '' Set.Ici x) := by
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    exact legendreCgfRateFunction_monoOn_Ici_of_mean_lt
      (P := P) (Y := X 0) hmgf hx hy
  calc
    Filter.limsup
        (fun n : ℕ ↦ ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1))
        atTop ≤
        -sInf (I '' Set.Ici x) := by
          simpa [hseq] using hUpper
    _ ≤ -(I x) := by
          exact (EReal.neg_le_neg_iff.2 hRate_le)
    _ = -legendreCgfRateFunction (X 0) P x := by
          simp [I]

/-- Helper for Theorem 23.3: shifting by `x` turns the closed upper-tail event for `X` into the
nonnegative centered event for `Y i ω = X i ω - x`. -/
private lemma shiftedUpperTailEvent_eq_nonnegativeCenteredEvent
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

/-- Helper for Theorem 23.3: if the centered coordinates are a.e. nonpositive, then the
nonnegative partial-sum event is exactly the event that every coordinate in the prefix equals `0`.
-/
private lemma nonpositiveCenteredTail_eq_zeroEventPow
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ i, IdentDistrib (Y 0) (Y i) P P)
    (hY_nonpos : ∀ᵐ ω ∂P, Y 0 ω ≤ 0)
    (n : ℕ) :
    P {ω | 0 ≤ partialSum Y (n + 1) ω} = (P {ω | Y 0 ω = 0}) ^ (n + 1) := by
  have hYi_nonpos : ∀ i, ∀ᵐ ω ∂P, Y i ω ≤ 0 := by
    intro i
    exact (hY_ident i).ae_mem_snd measurableSet_Iic hY_nonpos
  have hEventEq :
      {ω | 0 ≤ partialSum Y (n + 1) ω} =ᵐ[P]
        ⋂ i ∈ Finset.range (n + 1), {ω | Y i ω = 0} := by
    have hAllNonpos :
        ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (n + 1), Y i ω ≤ 0 := by
      refine (Finset.eventually_all (Finset.range (n + 1))).2 ?_
      intro i hi
      exact hYi_nonpos i
    filter_upwards [hAllNonpos] with ω hω
    apply propext
    constructor
    · intro hsum
      have hsum_nonpos : partialSum Y (n + 1) ω ≤ 0 := by
        simpa [partialSum] using Finset.sum_nonpos (fun i hi ↦ hω i hi)
      have hsum_zero : partialSum Y (n + 1) ω = 0 := le_antisymm hsum_nonpos hsum
      have hneg_sum_zero :
          ∑ j ∈ Finset.range (n + 1), -Y j ω = 0 := by
        simpa [partialSum, Finset.sum_neg_distrib] using congrArg Neg.neg hsum_zero
      have hzero_each :=
          (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range (n + 1))
            fun j hj ↦ neg_nonneg.mpr (hω j hj)).1 hneg_sum_zero
      refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro hi
      have : -Y i ω = 0 := hzero_each i hi
      simpa using this
    · intro hzero
      have hzero' : ∀ i ∈ Finset.range (n + 1), Y i ω = 0 := by
        intro i hi
        simpa using (Set.mem_iInter.1 (Set.mem_iInter.1 hzero i) hi)
      have hsum_zero : partialSum Y (n + 1) ω = 0 := by
        calc
          partialSum Y (n + 1) ω = ∑ i ∈ Finset.range (n + 1), Y i ω := by
            simp [partialSum]
          _ = ∑ _i ∈ Finset.range (n + 1), (0 : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact hzero' i hi
          _ = 0 := by simp
      change 0 ≤ partialSum Y (n + 1) ω
      simp [hsum_zero]
  calc
    P {ω | 0 ≤ partialSum Y (n + 1) ω} =
        P (⋂ i ∈ Finset.range (n + 1), {ω | Y i ω = 0}) := by
          exact measure_congr hEventEq
    _ = ∏ i ∈ Finset.range (n + 1), P (Y i ⁻¹' ({0} : Set ℝ)) := by
          simpa using
            hY_indep.measure_inter_preimage_eq_mul (S := Finset.range (n + 1))
              (sets := fun _ ↦ ({0} : Set ℝ))
              (fun _ _ ↦ by simp)
    _ = ∏ i ∈ Finset.range (n + 1), P {ω | Y 0 ω = 0} := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          simpa using
            ((hY_ident i).measure_preimage_eq (measurableSet_singleton (x := (0 : ℝ)))).symm
    _ = (P {ω | Y 0 ω = 0}) ^ (n + 1) := by
          simp

/-- Helper for Theorem 23.3: in the a.e.-nonpositive centered branch, the remaining lower-bound
work is the rate identity at `0` coming from the zero-mass of the one-dimensional law. -/
private lemma nonpositiveCenteredTail_liminf_ge_neg_rate
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ i, IdentDistrib (Y 0) (Y i) P P)
    (hYmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P)
    (hY_nonpos : ∀ᵐ ω ∂P, Y 0 ω ≤ 0) :
    -legendreCgfRateFunction (Y 0) P 0 ≤
      Filter.liminf
        (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
        atTop := by
  let eventZero : Set Ω := {ω | Y 0 ω = 0}
  let p0 := P eventZero
  have hSeq :
      (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1)) =ᶠ[atTop]
        fun _ : ℕ ↦ ENNReal.log p0 := by
    -- Proof comment: the prefix event is exactly the zero-event power, and the logarithm divided
    -- by `n + 1` cancels the exponent.
    filter_upwards with n
    have hn_bot : ((n + 1 : ℝ) : EReal) ≠ ⊥ := by
      simpa using (EReal.coe_ne_bot (n + 1 : ℝ))
    have hn_top : ((n + 1 : ℝ) : EReal) ≠ ⊤ := by
      simpa using (EReal.coe_ne_top (n + 1 : ℝ))
    have hn_zero : ((n + 1 : ℝ) : EReal) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    rw [nonpositiveCenteredTail_eq_zeroEventPow hY_indep hY_ident hY_nonpos n]
    calc
      ENNReal.log ((P {ω | Y 0 ω = 0}) ^ (n + 1)) / (n + 1) =
          (((n + 1 : EReal) * ENNReal.log p0) / (n + 1 : EReal)) := by
            simp [p0, eventZero, ENNReal.log_pow]
      _ = ENNReal.log p0 := by
            rw [mul_div_assoc]
            exact EReal.mul_div_cancel hn_bot hn_top hn_zero
  have hLiminf :
      Filter.liminf
          (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
          atTop =
        ENNReal.log p0 := by
    rw [Filter.liminf_congr hSeq]
    simp
  have hYae : AEMeasurable (Y 0) P := (hY_ident 0).aemeasurable_fst
  have hEventZero_nm : NullMeasurableSet eventZero P := by
    simpa [eventZero] using
      hYae.nullMeasurableSet_preimage (measurableSet_singleton (x := (0 : ℝ)))
  let F : ℕ → Ω → ℝ := fun n ω ↦ Real.exp ((n : ℝ) * Y 0 ω)
  let G : Ω → ℝ := Set.indicator eventZero (fun _ ↦ (1 : ℝ))
  have hBound :
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (1 : ℝ) := by
    intro n
    -- Proof comment: on the a.e.-nonpositive branch every integer tilt stays below the constant
    -- bound `1`, so dominated convergence applies with the integrable bound `1`.
    filter_upwards [hY_nonpos] with ω hω
    have hmul_nonpos : (n : ℝ) * Y 0 ω ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (n : ℝ) by positivity) hω
    have hexp_nonneg : 0 ≤ Real.exp ((n : ℝ) * Y 0 ω) := Real.exp_nonneg _
    simpa [F, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg] using
      (Real.exp_le_one_iff.mpr hmul_nonpos)
  have hLim :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ F n ω) atTop (𝓝 (G ω)) := by
    -- Proof comment: for a nonpositive point, the exponential tilt converges either to `1`
    -- on the zero fiber or to `0` on the strictly negative fiber.
    filter_upwards [hY_nonpos] with ω hω
    by_cases hzero : Y 0 ω = 0
    · simp [F, G, eventZero, hzero]
    · have hy_neg : Y 0 ω < 0 := by
        refine lt_of_le_of_ne hω ?_
        simpa using hzero
      have hMul : Tendsto (fun n : ℕ ↦ (n : ℝ) * Y 0 ω) atTop atBot := by
        simpa [mul_comm] using
          (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hy_neg)
      have hExp : Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * Y 0 ω)) atTop (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_atBot.comp hMul
      simpa [F, G, eventZero, hzero] using hExp
  have hG_int : ∫ ω, G ω ∂P = p0.toReal := by
    -- Proof comment: the limit function is the indicator of the zero fiber, whose integral is
    -- exactly the mass of that fiber.
    calc
      ∫ ω, G ω ∂P = ∫ ω in eventZero, (1 : ℝ) ∂P := by
        exact MeasureTheory.integral_indicator₀ hEventZero_nm
      _ = P.real eventZero := by
        simp
      _ = p0.toReal := by
        simp [p0, eventZero, measureReal_def]
  have hMgfNat :
      Tendsto (fun n : ℕ ↦ mgf (Y 0) P (n : ℝ)) atTop (𝓝 p0.toReal) := by
    -- Proof comment: dominated convergence identifies the integer-tilt mgf limit with the zero
    -- mass from the previous step.
    simpa [ProbabilityTheory.mgf, F, hG_int] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence (μ := P) (bound := fun _ ↦ (1 : ℝ))
        (fun n ↦ (hYmgf (n : ℝ)).aestronglyMeasurable) (integrable_const (1 : ℝ)) hBound hLim)
  have hRateLeNat :
      ∀ n : ℕ, -legendreCgfRateFunction (Y 0) P 0 ≤ (cgf (Y 0) P (n : ℝ) : EReal) := by
    intro n
    -- Proof comment: every single integer tilt contributes one candidate to the Legendre
    -- supremum at `0`, so negating the supremum bounds the rate from above by that candidate's
    -- cumulant.
    have hPoint :
        (((-cgf (Y 0) P (n : ℝ) : ℝ)) : EReal) ≤ legendreCgfRateFunction (Y 0) P 0 := by
      rw [legendreCgfRateFunction]
      refine le_csSup (OrderTop.bddAbove _) ?_
      refine ⟨(n : ℝ), ?_⟩
      simp
    exact (EReal.neg_le.2 hPoint)
  rw [hLiminf]
  by_cases hp0 : p0 = 0
  · have hMgfZero :
        Tendsto (fun n : ℕ ↦ mgf (Y 0) P (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa [p0, hp0, measureReal_def] using hMgfNat
    have hMgfNhdsGT :
        Tendsto (fun n : ℕ ↦ mgf (Y 0) P (n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
      rw [nhdsWithin]
      exact tendsto_inf.2 ⟨hMgfZero, tendsto_principal.2 <|
        Filter.Eventually.of_forall fun n ↦ mgf_pos (hYmgf (n : ℝ))⟩
    have hCgfBot :
        Tendsto (fun n : ℕ ↦ (cgf (Y 0) P (n : ℝ) : EReal)) atTop (𝓝 (⊥ : EReal)) := by
      rw [EReal.tendsto_coe_nhds_bot_iff]
      simpa [ProbabilityTheory.cgf] using
        (Real.tendsto_log_nhdsGT_zero.comp hMgfNhdsGT)
    have hRateBot :
        -legendreCgfRateFunction (Y 0) P 0 ≤ (⊥ : EReal) := by
      exact ge_of_tendsto' hCgfBot hRateLeNat
    simpa [hp0]
      using hRateBot
  · have hp0_top : p0 ≠ ⊤ := measure_ne_top P eventZero
    have hp0_toReal_pos : 0 < p0.toReal := ENNReal.toReal_pos hp0 hp0_top
    have hCgfReal :
        Tendsto (fun n : ℕ ↦ cgf (Y 0) P (n : ℝ)) atTop (𝓝 (Real.log p0.toReal)) := by
      simpa [ProbabilityTheory.cgf] using
        ((Real.continuousAt_log hp0_toReal_pos.ne').tendsto.comp hMgfNat)
    have hCgfEReal :
        Tendsto (fun n : ℕ ↦ (cgf (Y 0) P (n : ℝ) : EReal)) atTop
          (𝓝 ((Real.log p0.toReal : ℝ) : EReal)) := by
      exact (EReal.tendsto_coe).2 hCgfReal
    have hRateReal :
        -legendreCgfRateFunction (Y 0) P 0 ≤ ((Real.log p0.toReal : ℝ) : EReal) := by
      exact ge_of_tendsto' hCgfEReal hRateLeNat
    rw [ENNReal.log_pos_real hp0 hp0_top]
    exact hRateReal

/-- Helper for Theorem 23.3: if the centered marginal is not almost surely nonpositive, then some
strictly positive level set has positive mass. -/
private lemma exists_positiveLevel_posMeasure_of_not_ae_nonpos
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0) :
    ∃ a > 0, 0 < P {ω | a ≤ Z ω} := by
  let levelSet : ℕ → Set Ω := fun n ↦ {ω | (1 / (n + 1 : ℝ)) ≤ Z ω}
  have hIoi_ne_zero : P {ω | 0 < Z ω} ≠ 0 := by
    -- Proof comment: failing the a.e.-nonpositive branch means the positive set appears
    -- frequently, hence has nonzero measure.
    rw [← MeasureTheory.frequently_ae_iff]
    simpa [not_le] using hZ_not_nonpos
  have hIoi_eq : {ω | 0 < Z ω} = ⋃ n : ℕ, levelSet n := by
    -- Proof comment: a positive real lies above `1 / (n + 1)` for some `n`, so the positive set
    -- is the countable union of these fixed closed-halfline level sets.
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

/-- Helper for Theorem 23.3: a strictly negative mean forces some strictly negative level set to
have positive mass. -/
private lemma exists_negativeLevel_posMeasure_of_mean_lt_zero
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmean : P[Z] < 0) :
    ∃ b > 0, 0 < P {ω | Z ω ≤ -b} := by
  have hNotAeNonneg : ¬ ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    intro hAeNonneg
    have hMeanNonneg : 0 ≤ P[Z] := by
      simpa using integral_nonneg_of_ae hAeNonneg
    linarith
  have hNotAeNonposNeg : ¬ ∀ᵐ ω ∂P, -Z ω ≤ 0 := by
    intro hAeNonposNeg
    apply hNotAeNonneg
    simpa using hAeNonposNeg
  obtain ⟨b, hb_pos, hb_mass⟩ :=
    exists_positiveLevel_posMeasure_of_not_ae_nonpos (P := P) (Z := fun ω ↦ -Z ω)
      hNotAeNonposNeg
  refine ⟨b, hb_pos, ?_⟩
  have hSet : {ω | b ≤ -Z ω} = {ω | Z ω ≤ -b} := by
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

/-- Helper for Theorem 23.3: positive mass above the level `a` gives a lower bound on the
`cgf` along nonnegative tilts. -/
private lemma cgf_lowerBound_of_positiveLevelMass
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    {a : ℝ} (ha_mass : 0 < P {ω | a ≤ Z ω}) :
    ∀ {t : ℝ}, 0 ≤ t →
      Real.log (P.real {ω | a ≤ Z ω}) + t * a ≤ cgf Z P t := by
  intro t ht
  let A : Set Ω := {ω | a ≤ Z ω}
  have hZae : AEMeasurable Z P :=
    (integrable_of_allExponentialMoments (P := P) (Y := Z) hZmgf).aemeasurable
  have hA_nm : NullMeasurableSet A P := by
    simpa [A] using hZae.nullMeasurableSet_preimage measurableSet_Ici
  have hp_pos : 0 < P.real A := by
    simpa [A, MeasureTheory.measureReal_def] using
      ENNReal.toReal_pos ha_mass.ne' (measure_ne_top P A)
  have hIndInt :
      Integrable (A.indicator (fun _ : Ω ↦ Real.exp (t * a)) : Ω → ℝ) P := by
    exact (integrable_const (Real.exp (t * a))).indicator₀ hA_nm
  have hPoint :
      ∀ᵐ ω ∂P, A.indicator (fun _ : Ω ↦ Real.exp (t * a)) ω ≤ Real.exp (t * Z ω) := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · have hMul : t * a ≤ t * Z ω := mul_le_mul_of_nonneg_left hω ht
      simpa [A, Set.indicator_of_mem hω] using Real.exp_le_exp.mpr hMul
    · simpa only [Set.indicator_of_notMem hω] using (Real.exp_nonneg (t * Z ω))
  have hLower :
      P.real A * Real.exp (t * a) ≤ mgf Z P t := by
    calc
      P.real A * Real.exp (t * a)
          = ∫ ω, A.indicator (fun _ : Ω ↦ Real.exp (t * a)) ω ∂P := by
              rw [integral_indicator₀ hA_nm, MeasureTheory.setIntegral_const]
              simp [A, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω, Real.exp (t * Z ω) ∂P := by
            exact MeasureTheory.integral_mono_ae hIndInt (hZmgf t) hPoint
      _ = mgf Z P t := rfl
  have hProd_pos : 0 < P.real A * Real.exp (t * a) := mul_pos hp_pos (Real.exp_pos _)
  rw [cgf]
  have hLog := Real.log_le_log hProd_pos hLower
  simpa [A, Real.log_mul hp_pos.ne' (Real.exp_pos _).ne', add_comm, add_left_comm, add_assoc]
    using hLog

/-- Helper for Theorem 23.3: positive mass below the level `-b` gives a lower bound on the
`cgf` along nonpositive tilts. -/
private lemma cgf_lowerBound_of_negativeLevelMass
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    {b : ℝ} (hb_mass : 0 < P {ω | Z ω ≤ -b}) :
    ∀ {t : ℝ}, t ≤ 0 →
      Real.log (P.real {ω | Z ω ≤ -b}) - t * b ≤ cgf Z P t := by
  intro t ht
  let B : Set Ω := {ω | Z ω ≤ -b}
  have hZae : AEMeasurable Z P :=
    (integrable_of_allExponentialMoments (P := P) (Y := Z) hZmgf).aemeasurable
  have hB_nm : NullMeasurableSet B P := by
    simpa [B] using hZae.nullMeasurableSet_preimage measurableSet_Iic
  have hq_pos : 0 < P.real B := by
    simpa [B, MeasureTheory.measureReal_def] using
      ENNReal.toReal_pos hb_mass.ne' (measure_ne_top P B)
  have hIndInt :
      Integrable (B.indicator (fun _ : Ω ↦ Real.exp (-(t * b))) : Ω → ℝ) P := by
    exact (integrable_const (Real.exp (-(t * b)))).indicator₀ hB_nm
  have hPoint :
      ∀ᵐ ω ∂P, B.indicator (fun _ : Ω ↦ Real.exp (-(t * b))) ω ≤ Real.exp (t * Z ω) := by
    filter_upwards with ω
    by_cases hω : ω ∈ B
    · have hMul : t * (-b) ≤ t * Z ω := by
        exact mul_le_mul_of_nonpos_left hω ht
      simpa [B, Set.indicator_of_mem hω, neg_mul] using Real.exp_le_exp.mpr hMul
    · simpa only [Set.indicator_of_notMem hω] using (Real.exp_nonneg (t * Z ω))
  have hLower :
      P.real B * Real.exp (-(t * b)) ≤ mgf Z P t := by
    calc
      P.real B * Real.exp (-(t * b))
          = ∫ ω, B.indicator (fun _ : Ω ↦ Real.exp (-(t * b))) ω ∂P := by
              rw [integral_indicator₀ hB_nm, MeasureTheory.setIntegral_const]
              simp [B, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω, Real.exp (t * Z ω) ∂P := by
            exact MeasureTheory.integral_mono_ae hIndInt (hZmgf t) hPoint
      _ = mgf Z P t := rfl
  have hProd_pos : 0 < P.real B * Real.exp (-(t * b)) := mul_pos hq_pos (Real.exp_pos _)
  rw [cgf]
  have hLog := Real.log_le_log hProd_pos hLower
  simpa [B, Real.log_mul hq_pos.ne' (Real.exp_pos _).ne', add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg, neg_mul] using hLog

/-- Helper for Theorem 23.3: at finite endpoint values, the Legendre-transform rate at a convex
combination is bounded by the corresponding convex combination of the endpoint rates. -/
private theorem legendreCgfRateFunction_convexCombo_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    {x y r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx_top : legendreCgfRateFunction Z P x ≠ ⊤)
    (hy_top : legendreCgfRateFunction Z P y ≠ ⊤) :
    legendreCgfRateFunction Z P ((1 - r) * x + r * y) ≤
      ((((1 - r) * (legendreCgfRateFunction Z P x).toReal +
          r * (legendreCgfRateFunction Z P y).toReal : ℝ) : EReal)) := by
  rw [legendreCgfRateFunction]
  refine sSup_le ?_
  rintro _ ⟨t, rfl⟩
  have hx_bound :
      (((t * x - cgf Z P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Z P x := by
    rw [legendreCgfRateFunction]
    exact le_sSup ⟨t, rfl⟩
  have hy_bound :
      (((t * y - cgf Z P t : ℝ)) : EReal) ≤ legendreCgfRateFunction Z P y := by
    rw [legendreCgfRateFunction]
    exact le_sSup ⟨t, rfl⟩
  have hx_ne_bot : (((t * x - cgf Z P t : ℝ)) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hy_ne_bot : (((t * y - cgf Z P t : ℝ)) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hx_real : t * x - cgf Z P t ≤ (legendreCgfRateFunction Z P x).toReal := by
    exact EReal.toReal_le_toReal hx_bound hx_ne_bot hx_top
  have hy_real : t * y - cgf Z P t ≤ (legendreCgfRateFunction Z P y).toReal := by
    exact EReal.toReal_le_toReal hy_bound hy_ne_bot hy_top
  have hreal :
      t * ((1 - r) * x + r * y) - cgf Z P t ≤
        (1 - r) * (legendreCgfRateFunction Z P x).toReal +
          r * (legendreCgfRateFunction Z P y).toReal := by
    -- Proof comment: each affine summand is linear in the space variable, so the endpoint bounds
    -- combine directly under the convex weights `1 - r` and `r`.
    nlinarith
  change (((t * ((1 - r) * x + r * y) - cgf Z P t : ℝ)) : EReal) ≤
    ((((1 - r) * (legendreCgfRateFunction Z P x).toReal +
      r * (legendreCgfRateFunction Z P y).toReal : ℝ) : EReal))
  exact_mod_cast hreal

/-- Helper for Theorem 23.3: in the mixed-sign centered branch, positive right-hand rate values can
be controlled on a neighborhood of `0` by a finite constant. -/
private lemma legendreCgfRateFunction_boundedNearZero_of_mean_neg_mixedSign
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    (hZmean : P[Z] < 0)
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0) :
    ∃ a > 0, ∃ M : ℝ, ∀ {y : ℝ}, 0 ≤ y → y ≤ a → legendreCgfRateFunction Z P y ≤ (M : EReal) := by
  let I : ℝ → EReal := legendreCgfRateFunction Z P
  obtain ⟨a, ha_pos, ha_mass⟩ :=
    exists_positiveLevel_posMeasure_of_not_ae_nonpos (P := P) (Z := Z) hZ_not_nonpos
  obtain ⟨b, hb_pos, hb_mass⟩ :=
    exists_negativeLevel_posMeasure_of_mean_lt_zero (P := P) (Z := Z) hZmean
  let p : ℝ := P.real {ω | a ≤ Z ω}
  let q : ℝ := P.real {ω | Z ω ≤ -b}
  have hcgf_lower_pos :
      ∀ {t : ℝ}, 0 ≤ t → Real.log p + t * a ≤ cgf Z P t := by
    intro t ht
    simpa [p] using cgf_lowerBound_of_positiveLevelMass
      (P := P) (Z := Z) hZmgf (a := a) ha_mass ht
  have hcgf_lower_neg :
      ∀ {t : ℝ}, t ≤ 0 → Real.log q - t * b ≤ cgf Z P t := by
    intro t ht
    simpa [q] using cgf_lowerBound_of_negativeLevelMass
      (P := P) (Z := Z) hZmgf (b := b) hb_mass ht
  let M : ℝ := max (-Real.log p) (-Real.log q)
  have hRate_le_M :
      ∀ {y : ℝ}, 0 ≤ y → y ≤ a → I y ≤ (M : EReal) := by
    intro y hy_nonneg hy_le
    change legendreCgfRateFunction Z P y ≤ (M : EReal)
    rw [legendreCgfRateFunction]
    refine sSup_le ?_
    rintro _ ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · have hLower : Real.log p + t * a ≤ cgf Z P t := hcgf_lower_pos (t := t) ht
      have hty_le : t * y ≤ t * a := mul_le_mul_of_nonneg_left hy_le ht
      have hAff : t * y - cgf Z P t ≤ -Real.log p := by
        linarith
      have hAffE : (((t * y - cgf Z P t : ℝ)) : EReal) ≤ (((-Real.log p : ℝ)) : EReal) := by
        exact_mod_cast hAff
      have hMax : (((-Real.log p : ℝ)) : EReal) ≤ (M : EReal) := by
        exact_mod_cast (le_max_left (-Real.log p) (-Real.log q))
      exact le_trans hAffE hMax
    · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
      have hLower : Real.log q - t * b ≤ cgf Z P t := hcgf_lower_neg (t := t) ht'
      have hty_le : t * y ≤ -t * b := by
        have hy_nonpos : t * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht' hy_nonneg
        have htb_nonneg : 0 ≤ -t * b := by
          have ht_nonneg : 0 ≤ -t := by
            linarith
          exact mul_nonneg ht_nonneg (le_of_lt hb_pos)
        linarith
      have hAff : t * y - cgf Z P t ≤ -Real.log q := by
        linarith
      have hAffE : (((t * y - cgf Z P t : ℝ)) : EReal) ≤ (((-Real.log q : ℝ)) : EReal) := by
        exact_mod_cast hAff
      have hMax : (((-Real.log q : ℝ)) : EReal) ≤ (M : EReal) := by
        exact_mod_cast (le_max_right (-Real.log p) (-Real.log q))
      exact le_trans hAffE hMax
  exact ⟨a, ha_pos, M, fun hy_nonneg hy_le ↦ hRate_le_M hy_nonneg hy_le⟩

/-- Helper for Theorem 23.3: in the mixed-sign centered branch, positive right-hand rate values can
approximate the boundary rate at `0` from above. -/
private lemma exists_positiveRate_near_boundary_of_mean_neg_mixedSign
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    (hZmean : P[Z] < 0)
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y > 0,
      legendreCgfRateFunction Z P y ≤
        (((legendreCgfRateFunction Z P 0).toReal + ε : ℝ) : EReal) := by
  let I : ℝ → EReal := legendreCgfRateFunction Z P
  obtain ⟨a, ha_pos, M, hRate_le_M⟩ :=
    legendreCgfRateFunction_boundedNearZero_of_mean_neg_mixedSign
      (P := P) (Z := Z) hZmgf hZmean hZ_not_nonpos
  have hI0_ne_top : I 0 ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (hRate_le_M (y := 0) le_rfl (le_of_lt ha_pos))
  let y1 : ℝ := a / 2
  have hy1_pos : 0 < y1 := by
    positivity
  have hy1_le_a : y1 ≤ a := by
    have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
    dsimp [y1]
    nlinarith
  have hIy1_ne_top : I y1 ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by simp) (hRate_le_M (y := y1) (le_of_lt hy1_pos) hy1_le_a)
  let K : ℝ := max 0 ((I y1).toReal - (I 0).toReal)
  let r : ℝ := min (1 / 2 : ℝ) (ε / (K + 1))
  let y : ℝ := r * y1
  have hK_add_pos : 0 < K + 1 := by
    have hK_nonneg : 0 ≤ K := by
      simp [K]
    linarith
  have hr_nonneg : 0 ≤ r := by
    have hfrac_nonneg : 0 ≤ ε / (K + 1) := by
      exact le_of_lt (div_pos hε hK_add_pos)
    exact le_min (by norm_num) hfrac_nonneg
  have hr_pos : 0 < r := by
    have hfrac_pos : 0 < ε / (K + 1) := by
      exact div_pos hε hK_add_pos
    exact lt_min_iff.2 ⟨by norm_num, hfrac_pos⟩
  have hr_le_one : r ≤ 1 := by
    calc
      r ≤ (1 / 2 : ℝ) := min_le_left _ _
      _ ≤ 1 := by norm_num
  have hy_pos : 0 < y := by
    exact mul_pos hr_pos hy1_pos
  have hConv :
      I y ≤ ((((1 - r) * (I 0).toReal + r * (I y1).toReal : ℝ) : EReal)) := by
    have hy_repr : y = (1 - r) * 0 + r * y1 := by
      simp [y]
    rw [hy_repr]
    simpa [I] using
      legendreCgfRateFunction_convexCombo_le (P := P) (Z := Z)
        (x := 0) (y := y1) (r := r) hr_nonneg hr_le_one hI0_ne_top hIy1_ne_top
  have hr_le_frac : r ≤ ε / (K + 1) := by
    exact min_le_right _ _
  have hrK : r * K ≤ ε := by
    have h1 : r * K ≤ r * (K + 1) := by
      nlinarith
    have h2 : r * (K + 1) ≤ (ε / (K + 1)) * (K + 1) := by
      exact mul_le_mul_of_nonneg_right hr_le_frac (le_of_lt hK_add_pos)
    have h3 : (ε / (K + 1)) * (K + 1) = ε := by
      field_simp [hK_add_pos.ne']
    nlinarith [h1, h2, h3]
  have hDiff_le_K : (I y1).toReal - (I 0).toReal ≤ K := by
    simp [K]
  have hMulDiff : r * ((I y1).toReal - (I 0).toReal) ≤ ε := by
    have h1 : r * ((I y1).toReal - (I 0).toReal) ≤ r * K := by
      nlinarith
    exact le_trans h1 hrK
  have hAffineBound :
      (1 - r) * (I 0).toReal + r * (I y1).toReal ≤ (I 0).toReal + ε := by
    have hRewrite :
        (1 - r) * (I 0).toReal + r * (I y1).toReal =
          (I 0).toReal + r * ((I y1).toReal - (I 0).toReal) := by
      ring
    rw [hRewrite]
    linarith
  refine ⟨y, hy_pos, ?_⟩
  exact le_trans hConv (by exact_mod_cast hAffineBound)

/-- Helper for Theorem 23.3: the Legendre-transform rate is always nonnegative because the
zero tilt contributes the value `0`. -/
private lemma legendreCgfRateFunction_nonneg
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (x : ℝ) :
    (0 : EReal) ≤ legendreCgfRateFunction Z P x := by
  -- Proof comment: evaluate the Legendre supremum at tilt `t = 0`.
  rw [legendreCgfRateFunction]
  refine le_sSup ?_
  refine ⟨0, ?_⟩
  simp [cgf_zero]

/-- Helper for Theorem 23.3: right-sided epsilon-approximations force the boundary infimum over
`Set.Ioi 0` to lie below the boundary value. -/
private lemma sInfImageIoiZero_le_of_rightApprox
    {I : ℝ → EReal}
    (hI0_nonbot : I 0 ≠ ⊥) (hI0_ne_top : I 0 ≠ ⊤)
    (hnonneg : ∀ {y : ℝ}, 0 < y → (0 : EReal) ≤ I y)
    (happrox : ∀ ε > 0, ∃ y > 0, I y ≤ (((I 0).toReal + ε : ℝ) : EReal)) :
    sInf (I '' Set.Ioi (0 : ℝ)) ≤ I 0 := by
  -- Proof comment: a positive witness gives finiteness on the right, and then the boundary
  -- comparison is a pure `toReal` epsilon argument.
  have hsInf_nonbot : sInf (I '' Set.Ioi (0 : ℝ)) ≠ ⊥ := by
    have hsInf_nonneg : (0 : EReal) ≤ sInf (I '' Set.Ioi (0 : ℝ)) := by
      refine le_sInf ?_
      rintro _ ⟨y, hy_pos, rfl⟩
      exact hnonneg hy_pos
    exact ne_of_gt <| lt_of_lt_of_le (by simp) hsInf_nonneg
  have hsInf_ne_top : sInf (I '' Set.Ioi (0 : ℝ)) ≠ ⊤ := by
    obtain ⟨y, hy_pos, hy_bound⟩ := happrox 1 zero_lt_one
    have hsInf_le_y : sInf (I '' Set.Ioi (0 : ℝ)) ≤ I y := by
      exact sInf_le ⟨y, hy_pos, rfl⟩
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (le_trans hsInf_le_y hy_bound)
  have hsInf_toReal_le :
      ∀ ε : ℝ, 0 < ε → (sInf (I '' Set.Ioi (0 : ℝ))).toReal ≤ (I 0).toReal + ε := by
    intro ε hε
    obtain ⟨y, hy_pos, hy_bound⟩ := happrox ε hε
    have hsInf_le_eps :
        sInf (I '' Set.Ioi (0 : ℝ)) ≤ (((I 0).toReal + ε : ℝ) : EReal) := by
      exact le_trans (sInf_le ⟨y, hy_pos, rfl⟩) hy_bound
    exact EReal.toReal_le_toReal hsInf_le_eps hsInf_nonbot (EReal.coe_ne_top _)
  have hsInf_toReal_le_I0 : (sInf (I '' Set.Ioi (0 : ℝ))).toReal ≤ (I 0).toReal := by
    exact le_of_forall_pos_le_add hsInf_toReal_le
  calc
    sInf (I '' Set.Ioi (0 : ℝ)) ≤ ((((sInf (I '' Set.Ioi (0 : ℝ))).toReal : ℝ)) : EReal) := by
      exact EReal.le_coe_toReal hsInf_ne_top
    _ ≤ (((I 0).toReal : ℝ) : EReal) := by
      exact_mod_cast hsInf_toReal_le_I0
    _ = I 0 := EReal.coe_toReal hI0_ne_top hI0_nonbot

/-- Helper for Theorem 23.3: in the mixed-sign centered branch, the infimum of the positive-side
rate values lies below the boundary rate at `0`. -/
private lemma boundaryRateInf_le_zero_of_mean_neg_mixedSign
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    (hZmean : P[Z] < 0)
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0) :
    sInf (legendreCgfRateFunction Z P '' Set.Ioi (0 : ℝ)) ≤ legendreCgfRateFunction Z P 0 := by
  -- Proof comment: combine the existing right-boundary approximation lemma with monotonicity from
  -- the negative mean and the pure `EReal` order bridge above.
  let I : ℝ → EReal := legendreCgfRateFunction Z P
  obtain ⟨y₁, hy₁_pos, hy₁_bound⟩ :=
    exists_positiveRate_near_boundary_of_mean_neg_mixedSign
      (P := P) (Z := Z) hZmgf hZmean hZ_not_nonpos (ε := (1 : ℝ)) zero_lt_one
  have hI0_nonbot : I 0 ≠ ⊥ := by
    have hI0_nonneg : (0 : EReal) ≤ I 0 := by
      simpa [I] using legendreCgfRateFunction_nonneg (P := P) (Z := Z) (0 : ℝ)
    exact ne_of_gt <| lt_of_lt_of_le (by simp) hI0_nonneg
  have hI0_ne_top : I 0 ≠ ⊤ := by
    have hI0_le_y₁ : I 0 ≤ I y₁ := by
      simpa [I] using
        legendreCgfRateFunction_monoOn_Ici_of_mean_lt
          (P := P) (Y := Z) hZmgf hZmean (le_of_lt hy₁_pos)
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (le_trans hI0_le_y₁ hy₁_bound)
  refine sInfImageIoiZero_le_of_rightApprox (I := I) hI0_nonbot hI0_ne_top ?_ ?_
  · intro y hy_pos
    simpa [I] using legendreCgfRateFunction_nonneg (P := P) (Z := Z) y
  · intro ε hε
    simpa [I] using
      exists_positiveRate_near_boundary_of_mean_neg_mixedSign
        (P := P) (Z := Z) hZmgf hZmean hZ_not_nonpos (ε := ε) hε

/-- Helper for Theorem 23.3: negating the positive-side boundary comparison gives the rate
inequality needed in the mixed-sign lower-bound proof. -/
private lemma mixedSignCenteredBoundaryRate_neg
    [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Z ω)) P)
    (hZmean : P[Z] < 0)
    (hZ_not_nonpos : ¬ ∀ᵐ ω ∂P, Z ω ≤ 0) :
    -legendreCgfRateFunction Z P 0 ≤
      -sInf (legendreCgfRateFunction Z P '' Set.Ioi (0 : ℝ)) := by
  -- Proof comment: negate the un-signed boundary inequality once, instead of threading signs
  -- through the entire order proof.
  exact
    (EReal.neg_le_neg_iff.2 <|
      boundaryRateInf_le_zero_of_mean_neg_mixedSign
        (P := P) (Z := Z) hZmgf hZmean hZ_not_nonpos)

/-- Helper for Theorem 23.3: the canonical owner LDP already gives the lower bound for every
strict centered upper-tail event `partialSum Y (n + 1) > a (n + 1)`. -/
private lemma strictUpperTail_liminf_ge_neg_openRateInf
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ i, IdentDistrib (Y 0) (Y i) P P)
    (hYmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P)
    (a : ℝ) :
    -sInf (legendreCgfRateFunction (Y 0) P '' Set.Ioi a) ≤
      Filter.liminf
        (fun n : ℕ ↦ ENNReal.log (P {ω | a * (n + 1 : ℝ) < partialSum Y (n + 1) ω}) / (n + 1))
        atTop := by
  have hY_iid : IsIID Y P := by
    refine ⟨hY_indep, ?_⟩
    intro i j
    exact (hY_ident i).symm.trans (hY_ident j)
  have hOpenLower :
      -sInf (legendreCgfRateFunction (Y 0) P '' Set.Ioi a) ≤
        Filter.liminf
          (fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw Y P n) (Set.Ioi a)) / (n : EReal))
          atTop := by
    -- Proof comment: this is exactly the open-set lower bound from the canonical owner LDP for
    -- the normalized partial-sum laws.
    exact
      (SatisfiesLargeDeviationPrinciple.lower
        (normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
          (P := P) (X := Y) hY_indep (fun i ↦ (hY_ident i).symm) hYmgf))
        (Set.Ioi a) isOpen_Ioi
  rw [← liminf_succPNat_eq
    (f := fun n : ℕ+ ↦ ENNReal.log ((normalizedPartialSumLaw Y P n) (Set.Ioi a)) / (n : EReal))]
    at hOpenLower
  simpa [normalizedPartialSumLaw_openHalfline_eq_strictUpperTailEvent (X := Y) (P := P) hY_iid a]
    using hOpenLower

/-- Helper for Theorem 23.3: in the genuinely mixed-sign centered branch, the lower bound comes
from the owner open-set LDP plus the boundary comparison `I(0) ≤ inf_{y > 0} I(y)`. -/
private lemma mixedSignCenteredTail_liminf_ge_neg_rate
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ i, IdentDistrib (Y 0) (Y i) P P)
    (hYmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P)
    (hYmean : P[Y 0] < 0)
    (hY_not_nonpos : ¬ ∀ᵐ ω ∂P, Y 0 ω ≤ 0) :
    -legendreCgfRateFunction (Y 0) P 0 ≤
      Filter.liminf
        (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
        atTop := by
  -- Route correction: the old monolithic centered proof mixed optimizer existence,
  -- change-of-measure normalization, and the CLT window in one block. The stable frontier is now
  -- smaller: the owner LDP already supplies the strict-tail lower bound, so only the boundary-rate
  -- comparison `I(0) ≤ inf_{y > 0} I(y)` remains to pass from `Set.Ioi 0` to `Set.Ici 0`.
  have hStrictTail :
      -sInf (legendreCgfRateFunction (Y 0) P '' Set.Ioi (0 : ℝ)) ≤
        Filter.liminf
          (fun n : ℕ ↦ ENNReal.log (P {ω | 0 < partialSum Y (n + 1) ω}) / (n + 1))
          atTop := by
    -- Proof comment: the owner open-set LDP applies directly to the strict half-line `(0, ∞)`.
    simpa [zero_mul] using
      strictUpperTail_liminf_ge_neg_openRateInf hY_indep hY_ident hYmgf (0 : ℝ)
  have hStrictLeNonneg :
      Filter.liminf
          (fun n : ℕ ↦ ENNReal.log (P {ω | 0 < partialSum Y (n + 1) ω}) / (n + 1))
          atTop ≤
        Filter.liminf
          (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
          atTop := by
    refine Filter.liminf_le_liminf <| Filter.Eventually.of_forall ?_
    intro n
    have hSubset :
        {ω | 0 < partialSum Y (n + 1) ω} ⊆ {ω | 0 ≤ partialSum Y (n + 1) ω} := by
      intro ω hω
      change 0 < partialSum Y (n + 1) ω at hω
      exact le_of_lt hω
    have hLog :
        ENNReal.log (P {ω | 0 < partialSum Y (n + 1) ω}) ≤
          ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) := by
      exact ENNReal.log_monotone (measure_mono hSubset)
    have hInvNonneg : (0 : EReal) ≤ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast inv_nonneg.mpr (show (0 : ℝ) ≤ n + 1 by positivity)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hLog hInvNonneg)
  have hOpenToClosed :
      -sInf (legendreCgfRateFunction (Y 0) P '' Set.Ioi (0 : ℝ)) ≤
        Filter.liminf
          (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
          atTop := by
    exact le_trans hStrictTail hStrictLeNonneg
  have hBoundaryRate :
      -legendreCgfRateFunction (Y 0) P 0 ≤
        -sInf (legendreCgfRateFunction (Y 0) P '' Set.Ioi (0 : ℝ)) := by
    -- Proof comment: this is exactly the extracted one-sided boundary comparison.
    exact mixedSignCenteredBoundaryRate_neg
      (P := P) (Z := Y 0) hYmgf hYmean hY_not_nonpos
  exact le_trans hBoundaryRate hOpenToClosed

private lemma upperTail_shifted_liminf_ge_neg_rate
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    {x : ℝ} (hx : P[X 0] < x) :
    -legendreCgfRateFunction (X 0) P x ≤
      Filter.liminf
        (fun n : ℕ ↦ ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1))
        atTop := by
  -- Route correction: the upper-tail transport layer is now stable, so the remaining lower-bound
  -- work should proceed on the centered law `Y i ω = X i ω - x`, use
  -- `shiftedCoordinate_rateAtZero_eq_originalRate hmgf x`, and then split into the positive-support
  -- and a.e.-nonpositive boundary branches from the textbook proof.
  let Y : ℕ → Ω → ℝ := fun i ω ↦ X i ω - x
  have hY_indep : iIndepFun Y P := by
    -- Proof comment: independence is stable under the fixed measurable shift `z ↦ z - x`.
    simpa [Y, Function.comp] using
      hX_iid.iIndepFun.comp (fun _ ↦ fun z : ℝ ↦ z - x)
        (fun _ ↦ measurable_id.sub measurable_const)
  have hY_ident : ∀ i, IdentDistrib (Y 0) (Y i) P P := by
    -- Proof comment: identical distribution is preserved by the same measurable shift.
    intro i
    simpa [Y, Function.comp] using
      (hX_iid.identDistrib 0 i).comp (measurable_id.sub measurable_const)
  have hYmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y 0 ω)) P := by
    -- Proof comment: the exponential moment of the shifted coordinate is the original one times a
    -- harmless constant factor `exp (-t * x)`.
    intro t
    have hscaled :
        Integrable (fun ω ↦ Real.exp (-t * x) * Real.exp (t * X 0 ω)) P := by
      exact (hmgf t).const_mul (Real.exp (-t * x))
    convert hscaled using 1
    ext ω
    have hmul :
        t * (Y 0 ω) = -t * x + t * X 0 ω := by
      simp [Y]
      ring
    rw [hmul, Real.exp_add]
  have hX0_int : Integrable (X 0) P := integrable_X0_of_allExponentialMoments (P := P) (X := X) hmgf
  have hYmean : P[Y 0] < 0 := by
    have hmean_eq : P[Y 0] = P[X 0] - x := by
      calc
        P[Y 0] = ∫ ω, X 0 ω + (-x) ∂P := by
          simp [Y, sub_eq_add_neg]
        _ = P[X 0] + ∫ _ : Ω, (-x) ∂P := by
          rw [MeasureTheory.integral_add hX0_int (integrable_const (-x))]
        _ = P[X 0] - x := by
          have hconst : ∫ _ : Ω, (-x) ∂P = -x := by
            simp
          rw [hconst]
          ring
    rw [hmean_eq]
    linarith
  have hShiftedRate :
      -legendreCgfRateFunction (Y 0) P 0 = -legendreCgfRateFunction (X 0) P x := by
    simpa using congrArg Neg.neg
      (shiftedCoordinate_rateAtZero_eq_originalRate (X := X) (P := P) hmgf x)
  have hShiftedSeq :
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1)) =
        (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1)) := by
    -- Proof comment: after centering at `x`, the tail event is exactly the nonnegative partial-sum
    -- event for `Y`.
    funext n
    rw [shiftedUpperTailEvent_eq_nonnegativeCenteredEvent (P := P) (X := X) (x := x) (n := n)]
  by_cases hY_nonpos : ∀ᵐ ω ∂P, Y 0 ω ≤ 0
  · have hLower :
        -legendreCgfRateFunction (Y 0) P 0 ≤
          Filter.liminf
            (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
            atTop := nonpositiveCenteredTail_liminf_ge_neg_rate hY_indep hY_ident hYmgf hY_nonpos
    rw [hShiftedRate, ← hShiftedSeq] at hLower
    exact hLower
  · have hLower :
        -legendreCgfRateFunction (Y 0) P 0 ≤
          Filter.liminf
            (fun n : ℕ ↦ ENNReal.log (P {ω | 0 ≤ partialSum Y (n + 1) ω}) / (n + 1))
            atTop := mixedSignCenteredTail_liminf_ge_neg_rate hY_indep hY_ident hYmgf hYmean
              hY_nonpos
    rw [hShiftedRate, ← hShiftedSeq] at hLower
    exact hLower

-- `bridge/view` layer: the canonical owner in this chapter is the large-deviation principle for
-- `normalizedPartialSumLaw`, available upstream as
-- `normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple`.
-- The present theorem keeps the textbook upper-tail event phrasing `P[Sₙ ≥ x n]`
-- as a source-facing consequence of that owner API.
--
-- Proof sketch: rewrite the upper-tail event as the half-line `{y | x ≤ y}` for the normalized
-- partial-sum law, then read off the rate from the canonical Cramér LDP owner theorem.
/-- Theorem 23.3: Cramér's theorem for the upper tail of i.i.d. real partial sums with finite
exponential moments under a probability measure. Using the chapter's `0`-based partial sums
`partialSum X n = X₀ + ⋯ + Xₙ₋₁`, the logarithmic asymptotic of `P[Sₙ ≥ x n]` converges to the
negative of the Legendre transform of the cumulant generating function of the common law. -/
theorem cramer_partialSum_largeDeviation_upperTail
    [IsProbabilityMeasure P]
    (hX_iid : IsIID X P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P)
    {x : ℝ} (hx : P[X 0] < x) :
    Tendsto
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * n ≤ partialSum X n ω}) / n)
      atTop
      (nhds (-legendreCgfRateFunction (X 0) P x)) := by
  -- Proof comment: prove the asymptotic for the shifted sequence `n + 1`, where the empirical-mean
  -- owner theorem applies directly, then shift back by `tendsto_add_atTop_iff_nat`.
  let u : ℕ → EReal := fun n ↦
    ENNReal.log (P {ω | x * (n + 1 : ℝ) ≤ partialSum X (n + 1) ω}) / (n + 1)
  have hu_tendsto : Tendsto u atTop (nhds (-legendreCgfRateFunction (X 0) P x)) := by
    -- Proof comment: the `liminf` and `limsup` bounds for `u` squeeze it to the desired rate.
    refine tendsto_of_le_liminf_of_limsup_le
      (upperTail_shifted_liminf_ge_neg_rate (X := X) (P := P) hX_iid hmgf hx)
      (upperTail_shifted_limsup_le_neg_rate (X := X) (P := P) hX_iid hmgf hx)
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  refine hu_tendsto.congr' ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    simp [u]

end ProbabilityTheory
