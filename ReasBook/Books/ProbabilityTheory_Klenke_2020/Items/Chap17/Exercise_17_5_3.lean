/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Lemma_2_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_38.PositiveVisitNormalization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_10
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section LocalBridges

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/-- Helper for Exercise 17.5.3: the full diagonal Green value splits into the deterministic
time-`0` visit and the positive-time tail. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
    [IsMarkovProcessRealization κ P X] (x : E) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    -- Proof comment: under `P x`, the process starts from `x` at time `0`.
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
        = ((P x : Measure Ω).map (X 0)) ({x} : Set E) := by
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
      _ = Measure.dirac x ({x} : Set E) := by
            rw [hReal.initial_eq x]
      _ = 1 := by
            simp
  -- Proof comment: split off the time-`0` summand in the full Green series and rewrite the rest
  -- as the positive-time Green tail.
  calc
    (G[P, X]) x x = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} := by
      rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
    _ = (P x : Measure Ω) {ω | X 0 ω = x} +
        ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
          classical
          simpa [eq_comm] using
            (ENNReal.tsum_eq_add_tsum_ite
              (f := fun n : ℕ ↦ (P x : Measure Ω) {ω | X n ω = x}) 0)
    _ = 1 + ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
          simp [hzero]
    _ = 1 + ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = x} := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = 1 + (G[P, X; 1]) x x := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x x]

/-- Helper for Exercise 17.5.3: a shifted geometric series of `ℝ≥0∞` casts stays finite when the
ratio lies in `[0,1)`. -/
private lemma ennrealOfRealTsumGeometricSucc_lt_top_general {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: summability in `ℝ` keeps the pointwise `ℝ≥0∞` casts finite because all terms
  -- are nonnegative.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Exercise 17.5.3: Theorem 17.29 specialized to `(x, x)` turns the iterated entrance
probability series into the shifted power series of `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeriesLocal
    [IsMarkovProcessRealization κ P X] (x : E) :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: replace each entrance-time probability by the Theorem 17.29 formula, then
  -- reindex the `ℕ+`-sum to `ℕ` through `Equiv.pnatEquivNat`.
  calc
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
        ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := P) (X := X) x x k)
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n)))
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]

/-- Helper for Exercise 17.5.3: the positive-time diagonal Green function is the shifted power
series of the return probability. -/
private lemma greenFunctionFromOneSelf_eq_tsum_selfPowers_general
    [IsMarkovProcessRealization κ P X] (x : E) :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: rewrite the positive-time Green tail through the iterated entrance-time
  -- expansion, then reindex as an `ℕ`-series.
  exact
    (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
      (κ := κ) (P := P) (X := X) x).trans
      (iteratedEntranceProbabilitySeries_eq_selfPowerSeriesLocal
        (κ := κ) (P := P) (X := X) x)

/-- Helper for Exercise 17.5.3: an infinite diagonal Green value forces recurrence of the
corresponding state. -/
private lemma isRecurrentState_of_greenFunctionSelf_eq_top_general
    [IsMarkovProcessRealization κ P X] (x : E) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
  have hq_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: if the return probability were strictly below `1`, the shifted geometric
  -- series for the positive-time tail would stay finite, contradicting the infinite Green value.
  by_contra htrans
  have hq_lt_one : (F[P, X]) x x < 1 := by
    rw [IsRecurrentState] at htrans
    exact lt_of_le_of_ne hq_le_one (by simpa [eq_comm] using htrans)
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) < ⊤ :=
    ennrealOfRealTsumGeometricSucc_lt_top_general hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
          (κ := κ) (P := P) (X := X)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [greenFunctionFromOneSelf_eq_tsum_selfPowers_general
          (κ := κ) (P := P) (X := X)]
      _ < ⊤ := by
        exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Exercise 17.5.3: recurrence of a state forces the diagonal Green value to be
infinite. -/
private lemma greenFunctionSelf_eq_top_of_isRecurrentState_general
    [IsMarkovProcessRealization κ P X] (x : E) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  -- Proof comment: recurrence forces every positive-time return-probability power to equal `1`,
  -- so the positive-time Green tail is already the divergent series of ones.
  calc
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
      rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
        (P := P) (X := X) (κ := κ)]
    _ = 1 + ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
          rw [greenFunctionFromOneSelf_eq_tsum_selfPowers_general
            (P := P) (X := X) (κ := κ)]
          rw [IsRecurrentState] at hx
          simpa [hx]
    _ = ⊤ := by
          simp

end LocalBridges

/-- Helper for Exercise 17.5.3: the singleton-mass step matrix extracted from a planar
convolution kernel. -/
private def latticeConvolutionStepMatrix {d : ℕ} (ν : PMF (LatticePoint d)) :
    LatticePoint d → LatticePoint d → ENNReal :=
  fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}

/-- Helper for Exercise 17.5.3: the discrete matrix kernel of the local step matrix is the
original convolution kernel. -/
private lemma latticeConvolutionStepMatrixKernel_eq {d : ℕ} (ν : PMF (LatticePoint d)) :
    discreteMatrixKernel (latticeConvolutionStepMatrix ν) =
      dirac_convolution_kernel ν.toMeasure := by
  -- Proof comment: on the discrete lattice, equality of kernels is determined by singleton
  -- masses, and both singleton masses are the same translated PMF value.
  ext x s hs
  have hrow :
      discreteMatrixKernel (latticeConvolutionStepMatrix ν) x =
        dirac_convolution_kernel ν.toMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [latticeConvolutionStepMatrix]
    · intro z hz
      simp [latticeConvolutionStepMatrix, hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Exercise 17.5.3: a PMF measure is the counting measure weighted by its point
masses. -/
private lemma pmf_toMeasure_eq_count_withDensity
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] (p : PMF α) :
    p.toMeasure = Measure.count.withDensity p := by
  -- Proof comment: both measures evaluate a measurable set by summing the point masses over it.
  refine Measure.ext fun s hs ↦ ?_
  rw [p.toMeasure_apply hs, withDensity_apply _ hs]
  rw [← lintegral_indicator hs (fun x ↦ p x), lintegral_count]

/-- Helper for Exercise 17.5.3: integrability under a PMF is equivalent to weighted summability of
the pointwise norms. -/
private lemma integrable_iff_summable_norm_smul_pmf
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF α) (f : α → E) :
    Integrable f p.toMeasure ↔ Summable (fun x : α ↦ ‖(p x).toReal • f x‖) := by
  have hp_finite : ∀ᵐ x ∂(Measure.count : Measure α), p x < ⊤ :=
    Filter.Eventually.of_forall fun x ↦ p.apply_lt_top x
  have hp_meas : Measurable p := Measurable.of_discrete
  -- Proof comment: rewrite the PMF measure as a weighted counting measure and then apply the
  -- counting-measure characterization of integrability.
  rw [pmf_toMeasure_eq_count_withDensity p,
    integrable_withDensity_iff_integrable_smul' (μ := (Measure.count : Measure α))
      (f := p) hp_meas hp_finite,
    integrable_count_iff]

/-- Helper for Exercise 17.5.3: the planar quadratic moment hypothesis makes the weighted real
quadratic series summable. -/
private lemma planarSecondMomentSummable
    (ν : PMF (LatticePoint 2))
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    Summable (fun x : LatticePoint 2 ↦ ‖latticeEmbedding x‖ ^ 2 * (ν x).toReal) := by
  have hsum_ne_top :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x ≠ ⊤ :=
    ne_of_lt hsecond
  -- Proof comment: take real parts of the finite `ℝ≥0∞` series termwise.
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using
    (ENNReal.summable_toReal hsum_ne_top)

/-- Helper for Exercise 17.5.3: the coordinatewise lattice embedding preserves the additive
origin. -/
private lemma latticeEmbedding_zero (d : ℕ) :
    latticeEmbedding (0 : LatticePoint d) = (0 : EuclideanSpace ℝ (Fin d)) := by
  -- Proof comment: every coordinate of the embedded origin is zero.
  ext i
  simp [latticeEmbedding]

/-- Helper for Exercise 17.5.3: the coordinatewise lattice embedding is additive. -/
private lemma latticeEmbedding_add {d : ℕ} (x y : LatticePoint d) :
    latticeEmbedding (x + y) = latticeEmbedding x + latticeEmbedding y := by
  -- Proof comment: the embedding acts coordinatewise, so addition is checked on each coordinate.
  ext i
  simp [latticeEmbedding]

/-- Helper for Exercise 17.5.3: the lattice embedding is available as an additive homomorphism
for convolution-to-characteristic-function rewrites. -/
private def latticeEmbeddingAddMonoidHom (d : ℕ) :
    LatticePoint d →+ EuclideanSpace ℝ (Fin d) :=
  { toFun := latticeEmbedding
    map_zero' := latticeEmbedding_zero d
    map_add' := latticeEmbedding_add }

/-- Helper for Exercise 17.5.3: composing the translation convolution kernel generated by `ν`
with a measure `μ` is exactly convolution by `ν`. -/
private lemma diracConvolutionKernel_comp_measure_eq_conv_local
    {E : Type*} [AddMonoid E] [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableAdd₂ E]
    (μ ν : Measure E) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  have hconst :=
    congrArg
      (fun κ : Kernel E E ↦ κ (0 : E))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  -- Proof comment: evaluate the kernel identity at the origin to recover the corresponding
  -- measure-level convolution formula.
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Exercise 17.5.3: the translation kernel generated by a lattice PMF is Markov. -/
private lemma latticeDiracConvolutionKernel_isMarkov
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsMarkovKernel (dirac_convolution_kernel ν.toMeasure) := by
  -- Proof comment: each kernel row is `δ_x ∗ ν`, hence a probability measure.
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Exercise 17.5.3: every power of the translation kernel generated by a lattice PMF
is again Markov. -/
private lemma latticeDiracConvolutionKernel_pow_isMarkov
    {d n : ℕ} (ν : PMF (LatticePoint d)) :
    IsMarkovKernel (dirac_convolution_kernel ν.toMeasure ^ n) := by
  -- Proof comment: the zero power is the identity kernel, and the successor power is a
  -- composition of Markov kernels.
  induction n with
  | zero =>
      simpa using
        (inferInstance :
          IsMarkovKernel (Kernel.id : Kernel (LatticePoint d) (LatticePoint d)))
  | succ n hn =>
      letI : IsMarkovKernel (dirac_convolution_kernel ν.toMeasure ^ n) := hn
      letI : IsMarkovKernel (dirac_convolution_kernel ν.toMeasure) :=
        latticeDiracConvolutionKernel_isMarkov ν
      simpa [pow_succ] using
        (inferInstance :
          IsMarkovKernel
            ((dirac_convolution_kernel ν.toMeasure ^ n) ∘ₖ
              dirac_convolution_kernel ν.toMeasure))

/-- Helper for Exercise 17.5.3: the characteristic function of the `n`-step origin law is the
`n`th power of the one-step characteristic function. -/
-- TODO: Port the exact `Exercise_17_5_1` Fourier rewrite shape, including the map/convolution
-- normal-form bridges.
private lemma latticeOriginLaw_charFunPow
    {d n : ℕ} (ν : PMF (LatticePoint d)) (t : EuclideanSpace ℝ (Fin d)) :
    charFun ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d)).map
      latticeEmbedding)) t =
      charFun (ν.toMeasure.map latticeEmbedding) t ^ n := by
  letI : IsMarkovKernel (dirac_convolution_kernel ν.toMeasure) :=
    latticeDiracConvolutionKernel_isMarkov ν
  induction n with
  | zero =>
      -- Proof comment: the zero-step origin law is the Dirac mass at the origin, so the
      -- characteristic function is constantly `1`.
      change charFun (Measure.map latticeEmbedding
        (((Kernel.id : Kernel (LatticePoint d) (LatticePoint d))) (0 : LatticePoint d))) t = 1
      rw [Kernel.id_apply, Measure.map_dirac]
      simpa [latticeEmbedding_zero] using
        (MeasureTheory.charFun_dirac (x := latticeEmbedding (0 : LatticePoint d)) t)
  | succ n hn =>
      let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      letI : IsMarkovKernel (κ ^ n) := by
        simpa [κ] using latticeDiracConvolutionKernel_pow_isMarkov (ν := ν) (n := n)
      -- Proof comment: rewrite the successor origin law as one more convolution by `ν`, map it
      -- through the additive embedding, and use multiplicativity of `charFun`.
      calc
        charFun ((((κ ^ (n + 1)) (0 : LatticePoint d)).map latticeEmbedding)) t
            = charFun (((κ ∘ₘ ((κ ^ n) (0 : LatticePoint d))).map latticeEmbedding)) t := by
                rw [hpow, Kernel.comp_apply]
        _ = charFun (((((κ ^ n) (0 : LatticePoint d)) ∗ ν.toMeasure).map latticeEmbedding)) t := by
              rw [show κ ∘ₘ ((κ ^ n) (0 : LatticePoint d)) =
                (((κ ^ n) (0 : LatticePoint d)) ∗ ν.toMeasure) by
                  simpa [κ] using
                    (diracConvolutionKernel_comp_measure_eq_conv_local
                      (μ := ((κ ^ n) (0 : LatticePoint d))) (ν := ν.toMeasure))]
        _ = charFun ((((κ ^ n) (0 : LatticePoint d)).map latticeEmbedding)) t *
              charFun (ν.toMeasure.map latticeEmbedding) t := by
                letI : IsFiniteMeasure (((κ ^ n) (0 : LatticePoint d))) := by infer_instance
                letI : IsFiniteMeasure
                    (Measure.map latticeEmbedding (((κ ^ n) (0 : LatticePoint d)))) := by
                      infer_instance
                rw [show Measure.map latticeEmbedding ((((κ ^ n) (0 : LatticePoint d)) ∗
                    ν.toMeasure)) =
                  (Measure.map latticeEmbedding (((κ ^ n) (0 : LatticePoint d)))) ∗
                    Measure.map latticeEmbedding ν.toMeasure by
                      simpa using
                        (Measure.map_conv_addMonoidHom
                          (μ := ((κ ^ n) (0 : LatticePoint d)))
                          (ν := ν.toMeasure)
                          (latticeEmbeddingAddMonoidHom d) (by fun_prop))]
                rw [MeasureTheory.charFun_conv]
        _ = charFun (ν.toMeasure.map latticeEmbedding) t ^ n *
              charFun (ν.toMeasure.map latticeEmbedding) t := by
                rw [hn]
        _ = charFun (ν.toMeasure.map latticeEmbedding) t ^ (n + 1) := by
              simp [pow_succ]

/-- Helper for Exercise 17.5.3: the `n`-step origin mass is the normalized Fourier-cube integral
of the `n`th power of the planar characteristic function. -/
-- TODO: Reapply discrete Fourier inversion after restoring the `n`-step characteristic-function
-- identity and finite-measure instance.
private lemma planarOriginMass_eq_fourierIntegral
    (ν : PMF (LatticePoint 2)) (n : ℕ) :
    ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
      ({0} : Set (LatticePoint 2)) : ℂ)) =
      (((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ) *
        ∫ t in latticeFrequencyCube 2,
          charFun (ν.toMeasure.map latticeEmbedding) t ^ n ∂volume := by
  let κ : Kernel (LatticePoint 2) (LatticePoint 2) := dirac_convolution_kernel ν.toMeasure
  letI : IsMarkovKernel κ := by simpa [κ] using latticeDiracConvolutionKernel_isMarkov (ν := ν)
  letI : IsMarkovKernel (κ ^ n) := by
    simpa [κ] using latticeDiracConvolutionKernel_pow_isMarkov (ν := ν) (n := n)
  letI : IsFiniteMeasure ((κ ^ n) (0 : LatticePoint 2)) := by infer_instance
  have hFourier :=
    _root_.discreteFourierInversionFormula
      (d := 2)
      (μ := ((κ ^ n) (0 : LatticePoint 2)))
      (x := (0 : LatticePoint 2))
  -- Proof comment: at the origin the Fourier phase is trivial, so inversion reduces to the
  -- integral of the `n`-step characteristic function.
  simpa [κ, latticeEmbedding_zero,
    latticeOriginLaw_charFunPow (ν := ν) (n := n)] using hFourier

/-- Helper for Exercise 17.5.3: for `r ∈ [0,1)`, the geometric ratio `r * φ(t)` stays inside the
open unit disk because characteristic functions have norm at most `1`. -/
-- TODO: Restore the probability-measure instance plumbing for the mapped planar step law.
private lemma planarCharFun_mul_norm_lt_one
    (ν : PMF (LatticePoint 2)) {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (t : EuclideanSpace ℝ (Fin 2)) :
    ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ < 1 := by
  letI : IsProbabilityMeasure (ν.toMeasure.map latticeEmbedding) := by
    simpa using
      Measure.isProbabilityMeasure_map
        (μ := ν.toMeasure)
        (f := latticeEmbedding)
        (Measurable.of_discrete.aemeasurable :
          AEMeasurable latticeEmbedding ν.toMeasure)
  have hφ_norm_le :
      ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one (μ := ν.toMeasure.map latticeEmbedding) t
  have hr_norm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_of_nonneg hr_nonneg]
  -- Proof comment: the characteristic-function factor has norm at most `1`, so the product norm
  -- is bounded by `r`, which lies strictly below `1`.
  calc
    ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖
      = ‖(r : ℂ)‖ * ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
          rw [norm_mul]
    _ ≤ r := by
          rw [hr_norm]
          exact mul_le_of_le_one_right (by positivity) hφ_norm_le
    _ < 1 := hr_lt_one

/-- Helper for Exercise 17.5.3: the geometric ratio `r * φ(t)` is pointwise bounded by `r`. -/
private lemma planarCharFun_mul_norm_le
    (ν : PMF (LatticePoint 2)) {r : ℝ} (hr_nonneg : 0 ≤ r)
    (t : EuclideanSpace ℝ (Fin 2)) :
    ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ r := by
  letI : IsProbabilityMeasure (ν.toMeasure.map latticeEmbedding) := by
    simpa using
      Measure.isProbabilityMeasure_map
        (μ := ν.toMeasure)
        (f := latticeEmbedding)
        (Measurable.of_discrete.aemeasurable :
          AEMeasurable latticeEmbedding ν.toMeasure)
  have hφ_norm_le :
      ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one (μ := ν.toMeasure.map latticeEmbedding) t
  have hr_norm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_of_nonneg hr_nonneg]
  -- Proof comment: the characteristic-function factor has norm at most `1`, so the product norm
  -- stays below the scalar factor `r`.
  calc
    ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖
      = ‖(r : ℂ)‖ * ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
          rw [norm_mul]
    _ ≤ r := by
          rw [hr_norm]
          exact mul_le_of_le_one_right (by positivity) hφ_norm_le

/-- Helper for Exercise 17.5.3: after `n` steps, the law started from `x` for the convolution
kernel driven by `ν` is the translate of the origin law by `x`. -/
-- TODO: Restore the translated-origin-law recursion using the current convolution-kernel API.
lemma latticeKernelPow_apply_eq_diracConv_originLawLocal
    {d n : ℕ} (ν : PMF (LatticePoint d)) (x : LatticePoint d) :
    ((dirac_convolution_kernel ν.toMeasure ^ n) x) =
      Measure.dirac x ∗
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d)) := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the kernel row is the starting Dirac mass.
      change Measure.dirac x = Measure.dirac x ∗ Measure.dirac (0 : LatticePoint d)
      simp
  | succ n ih =>
      let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      -- Proof comment: evolve the translated `n`-step origin law by one extra convolution step
      -- and reassociate the resulting convolutions.
      calc
        (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
          rw [hpow, Kernel.comp_apply]
        _ = ((κ ^ n) x) ∗ ν.toMeasure := by
          simpa [κ] using
            (diracConvolutionKernel_comp_measure_eq_conv_local
              (μ := (κ ^ n) x) (ν := ν.toMeasure))
        _ = (Measure.dirac x ∗ ((κ ^ n) (0 : LatticePoint d))) ∗ ν.toMeasure := by
          rw [ih]
        _ = Measure.dirac x ∗ (((κ ^ n) (0 : LatticePoint d)) ∗ ν.toMeasure) := by
          rw [Measure.conv_assoc]
        _ = Measure.dirac x ∗ ((κ ^ (n + 1)) (0 : LatticePoint d)) := by
          congr 1
          calc
            ((κ ^ n) (0 : LatticePoint d)) ∗ ν.toMeasure = κ ∘ₘ ((κ ^ n) (0 : LatticePoint d)) := by
              symm
              simpa [κ] using
                (diracConvolutionKernel_comp_measure_eq_conv_local
                  (μ := (κ ^ n) (0 : LatticePoint d)) (ν := ν.toMeasure))
            _ = (κ ∘ₖ (κ ^ n)) (0 : LatticePoint d) := by
              rw [Kernel.comp_apply]
            _ = (κ ^ (n + 1)) (0 : LatticePoint d) := by
              rw [← hpow]

/-- Helper for Exercise 17.5.3: the `n`-step return mass at the start state equals the `n`-step
return mass at the origin for a convolution-kernel walk on `ℤ^d`. -/
-- TODO: Recover the singleton pullback along lattice translation once the translated-origin-law
-- recursion above is restored.
lemma latticeKernelPow_apply_singleton_self_eq_originMassLocal
    {d n : ℕ} (ν : PMF (LatticePoint d)) (x : LatticePoint d) :
    ((dirac_convolution_kernel ν.toMeasure ^ n) x) ({x} : Set (LatticePoint d)) =
      ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d))
        ({0} : Set (LatticePoint d)) := by
  -- Proof comment: rewrite the `x`-row as a translated origin law and evaluate the translated
  -- singleton at displacement `x - x = 0`.
  rw [latticeKernelPow_apply_eq_diracConv_originLawLocal (ν := ν) (n := n) x]
  rw [Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({x} : Set (LatticePoint d)) = ({0} : Set (LatticePoint d)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      have hz' : x + z - x = x - x := by
        exact congrArg (fun w : LatticePoint d => w - x) hz
      simpa using hz'
    · intro hz
      simpa [hz]
  rw [hpreimage]

/-- Helper for Exercise 17.5.3: the origin diagonal Green value of a lattice convolution walk is
the series of the origin singleton masses of the `n`-step kernels. -/
private lemma latticeWalk_greenFunction_zero_zero_eq_tsum_originMassLocal
    {d : ℕ} (ν : PMF (LatticePoint d))
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X] :
    (G[P, X]) (0 : LatticePoint d) 0 =
      ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d))
        ({0} : Set (LatticePoint d)) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: rewrite each time-`n` visit probability at the origin through the
  -- realization identity for the convolution kernel.
  rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
  refine tsum_congr fun n ↦ ?_
  have htransition :=
    congrArg
      (fun μ : Measure (LatticePoint d) ↦ μ ({0} : Set (LatticePoint d)))
      (hReal.transition_eq (0 : LatticePoint d) n)
  simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : LatticePoint d))] using
    htransition

/-- Helper for Exercise 17.5.3: for a planar convolution-kernel walk, the diagonal Green value is
translation invariant. -/
lemma planarWalkGreenFunctionSelf_eq_origin
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (x : LatticePoint 2) :
    (G[P, X]) x x = (G[P, X]) 0 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand both diagonal Green values into the visit-probability series and then
  -- identify each time-`n` marginal with the corresponding kernel row.
  calc
    (G[P, X]) x x =
        ∑' n : ℕ,
          ((dirac_convolution_kernel ν.toMeasure ^ n) x) ({x} : Set (LatticePoint 2)) := by
          rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
          refine tsum_congr fun n ↦ ?_
          have htransition :=
            congrArg
              (fun μ : Measure (LatticePoint 2) ↦ μ ({x} : Set (LatticePoint 2)))
              (hReal.transition_eq x n)
          simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton x)] using
            htransition
    _ = ∑' n : ℕ,
          ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
            ({0} : Set (LatticePoint 2)) := by
          refine tsum_congr fun n ↦ ?_
          exact latticeKernelPow_apply_singleton_self_eq_originMassLocal (ν := ν) (n := n) x
    _ = (G[P, X]) 0 0 := by
          rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
          refine (tsum_congr fun n ↦ ?_).symm
          have htransition :=
            congrArg
              (fun μ : Measure (LatticePoint 2) ↦ μ ({0} : Set (LatticePoint 2)))
              (hReal.transition_eq (0 : LatticePoint 2) n)
          simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : LatticePoint 2))] using
            htransition

/-- Helper for Exercise 17.5.3: on `ℤ²`, an infinite diagonal Green value forces recurrence of the
corresponding state. -/
lemma planarWalkGreenFunctionSelf_eq_top_of_isRecurrentState
    {κ : ℕ → Kernel (LatticePoint 2) (LatticePoint 2)}
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint 2) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  -- Proof comment: this is the generic diagonal Green divergence criterion specialized to `ℤ²`.
  exact greenFunctionSelf_eq_top_of_isRecurrentState_general (κ := κ) (P := P) (X := X) x hx

/-- Helper for Exercise 17.5.3: on `ℤ²`, an infinite diagonal Green value forces recurrence of the
corresponding state. -/
lemma planarWalkIsRecurrentState_of_greenFunctionSelf_eq_top
    {κ : ℕ → Kernel (LatticePoint 2) (LatticePoint 2)}
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint 2) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  -- Proof comment: an infinite diagonal Green value forces recurrence already at the generic
  -- state-space level.
  exact isRecurrentState_of_greenFunctionSelf_eq_top_general (κ := κ) (P := P) (X := X) x hx

/-- Helper for Exercise 17.5.3: the additive support span of the planar step law. -/
private abbrev supportSpan (ν : PMF (LatticePoint 2)) : Submodule ℤ (LatticePoint 2) :=
  Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}

/-- Helper for Exercise 17.5.3: the support submodule of a planar step law has either rank at
most `1` or full rank `2`. -/
lemma supportSpan_finrank_le_one_or_eq_two
    (ν : PMF (LatticePoint 2)) :
    let H : Submodule ℤ (LatticePoint 2) := Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}
    Module.finrank ℤ H ≤ 1 ∨ Module.finrank ℤ H = 2 := by
  intro H
  have hH_le : Module.finrank ℤ H ≤ Module.finrank ℤ (LatticePoint 2) :=
    Submodule.finrank_le H
  have hH_le_two : Module.finrank ℤ H ≤ 2 := by
    simpa using hH_le
  -- Proof comment: a submodule of `ℤ²` cannot have any intermediate finite rank beyond `0`, `1`,
  -- or `2`, so the ambient rank bound immediately yields the required dichotomy.
  omega

/-- Helper for Exercise 17.5.3: a rank-two support span has the same `ℤ`-module finrank as the
ambient lattice `ℤ²`. -/
lemma supportSpan_finrank_eq_ambient_of_finrank_eq_two
    (ν : PMF (LatticePoint 2))
    (hH :
      Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) = 2) :
    Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) =
      Module.finrank ℤ (LatticePoint 2) := by
  -- Proof comment: `LatticePoint 2` is just `Fin 2 → ℤ`, whose ambient `ℤ`-module finrank is `2`.
  simpa [LatticePoint] using hH.trans (Module.finrank_fin_fun (R := ℤ) (n := 2)).symm

/-- Helper for Exercise 17.5.3: rewriting the rank-two hypothesis through `supportSpan` preserves
the same `ℤ`-module finrank. -/
private lemma supportSpan_finrank_eq_two
    (ν : PMF (LatticePoint 2))
    (hH :
      Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) = 2) :
    Module.finrank ℤ (supportSpan ν) = 2 := by
  -- Proof comment: this is just the given rank hypothesis rewritten through the local
  -- abbreviation `supportSpan`.
  simpa [supportSpan] using hH

/-- Helper for Exercise 17.5.3: if the support span is trivial, then the step law is concentrated
at the origin. -/
lemma stepLaw_eq_pure_zero_of_supportSpan_eq_bot
    (ν : PMF (LatticePoint 2))
    (hH : Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0} = ⊥) :
    ν = PMF.pure (0 : LatticePoint 2) := by
  have hsupp_sub : ν.support ⊆ ({0} : Set (LatticePoint 2)) := by
    intro x hx
    -- Proof comment: if `x` has positive mass, then `x` lies in the support span, which is
    -- trivial by hypothesis.
    exact (Submodule.span_eq_bot.mp hH) x hx
  have hzero_mem : (0 : LatticePoint 2) ∈ ν.support := by
    rcases ν.support_nonempty with ⟨x, hx⟩
    have hx0 : x = 0 := hsupp_sub hx
    simpa [hx0] using hx
  have hsupp : ν.support = ({0} : Set (LatticePoint 2)) :=
    Set.Subset.antisymm hsupp_sub (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hzero_mem)
  ext x
  by_cases hx : x = 0
  · subst hx
    -- Proof comment: once the support is exactly `{0}`, the origin carries total mass `1`.
    simpa [hsupp] using (ν.apply_eq_one_iff (0 : LatticePoint 2)).2 hsupp
  · -- Proof comment: off the support singleton, both PMFs vanish.
    simp [hx, (ν.apply_eq_zero_iff x).2 (by simpa [hsupp, hx])]

/-- Helper for Exercise 17.5.3: the convolution walk driven by the zero step law stays at its
starting point at every deterministic time. -/
lemma latticeKernelPow_apply_eq_dirac_of_pure_zero
    {d n : ℕ} (x : LatticePoint d) :
    ((dirac_convolution_kernel (PMF.pure (0 : LatticePoint d)).toMeasure ^ n) x) =
      Measure.dirac x := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the kernel row is the starting Dirac mass.
      change Measure.dirac x = Measure.dirac x
      rfl
  | succ n ih =>
      let κ : Kernel (LatticePoint d) (LatticePoint d) :=
        dirac_convolution_kernel (PMF.pure (0 : LatticePoint d)).toMeasure
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      -- Proof comment: one more step convolves the inductive Dirac law with the zero increment,
      -- which leaves the starting Dirac mass unchanged.
      calc
        (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
          rw [hpow, Kernel.comp_apply]
        _ = ((κ ^ n) x) ∗ (PMF.pure (0 : LatticePoint d)).toMeasure := by
          simpa [κ] using
            (diracConvolutionKernel_comp_measure_eq_conv_local
              (μ := ((κ ^ n) x))
              (ν := (PMF.pure (0 : LatticePoint d)).toMeasure))
        _ = Measure.dirac x := by
          rw [ih]
          simpa [PMF.toMeasure_pure] using (Measure.conv_dirac_zero (Measure.dirac x))

/-- Helper for Exercise 17.5.3: if every increment is `0`, then the origin Green value is already
the divergent series of ones. -/
lemma planarWalk_originGreen_eq_top_of_stepLaw_eq_pure_zero
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (hν : ν = PMF.pure (0 : LatticePoint 2)) :
    (G[P, X]) (0 : LatticePoint 2) 0 = ⊤ := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand the origin Green value into return masses and use that the pure-zero
  -- step law keeps the walk at the origin at every deterministic time.
  calc
    (G[P, X]) (0 : LatticePoint 2) 0
      = ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) := by
            rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
            refine tsum_congr fun n ↦ ?_
            have htransition :=
              congrArg
                (fun μ : Measure (LatticePoint 2) ↦ μ ({0} : Set (LatticePoint 2)))
                (hReal.transition_eq (0 : LatticePoint 2) n)
            simpa
              [Measure.map_apply (hReal.measurable_process n)
                (measurableSet_singleton (0 : LatticePoint 2))] using htransition
    _ = ⊤ := by
          let a : ℕ → ENNReal := fun n ↦
            (((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
              ({0} : Set (LatticePoint 2)))
          have ha : a = fun _ : ℕ ↦ (1 : ENNReal) := by
            funext n
            dsimp [a]
            rw [hν, latticeKernelPow_apply_eq_dirac_of_pure_zero (d := 2) (n := n)
              (x := (0 : LatticePoint 2))]
            simp
          simpa [a, ha] using
            (ENNReal.tsum_const_eq_top_of_ne_zero (a := (1 : ENNReal)) one_ne_zero)

/-- Helper for Exercise 17.5.3: restricting the ambient step law to its support span still gives a
probability mass function because points outside the span already have zero mass. -/
private lemma supportSpanStepPMF_hasSum
    (ν : PMF (LatticePoint 2)) :
    HasSum (fun x : supportSpan ν ↦ ν x.1) 1 := by
  have hsupp : Function.support ν ⊆ supportSpan ν := by
    intro x hx
    exact Submodule.subset_span hx
  -- Proof comment: summing over the support-span subtype is the same as summing over the ambient
  -- lattice because every nonzero-mass point already lies in the span.
  have htsum : ∑' x : supportSpan ν, ν x.1 = 1 := by
    calc
      ∑' x : supportSpan ν, ν x.1 = ∑' x : LatticePoint 2, ν x := by
        simpa [supportSpan] using tsum_subtype_eq_of_support_subset hsupp
      _ = 1 := PMF.tsum_coe ν
  exact ENNReal.summable.hasSum_iff.mpr htsum

/-- Helper for Exercise 17.5.3: the planar step law viewed as a PMF on its support span. -/
private noncomputable def supportSpanStepPMF
    (ν : PMF (LatticePoint 2)) : PMF (supportSpan ν) :=
  ⟨fun x ↦ ν x.1, supportSpanStepPMF_hasSum ν⟩

/-- Helper for Exercise 17.5.3: mapping a subtype-valued PMF along `Subtype.val` rewrites to the
corresponding fiber sum on the ambient type. -/
private lemma pmfMapSubtypeVal_apply
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (s : Set α) [DecidablePred (fun x : α ↦ x ∈ s)] (p : PMF s) (y : α) :
    PMF.map (Subtype.val : s → α) p y = if hy : y ∈ s then p ⟨y, hy⟩ else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hy : y ∈ s
  · -- Proof comment: when `y ∈ s`, the fiber of `Subtype.val` over `y` is the singleton
    -- `⟨y, hy⟩`, so the pushforward mass collapses to that one term.
    refine (tsum_eq_single ⟨y, hy⟩ ?_).trans ?_
    · intro x hx
      by_cases hxy : y = x.1
      · exact (hx (Subtype.ext hxy.symm)).elim
      · simp [hxy]
    · simpa [hy]
  · -- Proof comment: when `y ∉ s`, the fiber is empty, so every term in the pushforward sum
    -- vanishes.
    have hzero : ∑' a : s, (if y = ↑a then p a else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      have hxy : y ≠ x.1 := by
        intro hxy
        exact hy (hxy ▸ x.2)
      simp [hxy]
    simpa [hy] using hzero

/-- Helper for Exercise 17.5.3: mapping the support-span step PMF by the subtype inclusion
recovers the original planar step law. -/
private lemma supportSpanStepPMF_map_subtype_eq
    (ν : PMF (LatticePoint 2)) :
    PMF.map (supportSpan ν).subtype (supportSpanStepPMF ν) = ν := by
  classical
  ext y
  have hmap :
      PMF.map (Subtype.val : supportSpan ν → LatticePoint 2) (supportSpanStepPMF ν) y =
        if hy : y ∈ supportSpan ν then (supportSpanStepPMF ν) ⟨y, hy⟩ else 0 :=
    pmfMapSubtypeVal_apply (s := supportSpan ν) (p := supportSpanStepPMF ν) y
  by_cases hy : y ∈ supportSpan ν
  · -- Proof comment: inside the support span, the subtype pushforward reads off the same mass.
    simpa [hy, supportSpanStepPMF] using hmap
  · have hy_zero : ν y = 0 := by
      by_contra hν
      exact hy (Submodule.subset_span hν)
    -- Proof comment: outside the support span, the ambient PMF already vanishes.
    simpa [hy, supportSpanStepPMF, hy_zero] using hmap

/-- Helper for Exercise 17.5.3: viewed inside the support subgroup itself, the restricted step
law has literal full support span. -/
private lemma supportSpanStepPMF_supportSpan_eq_top
    (ν : PMF (LatticePoint 2)) :
    Submodule.span ℤ (((supportSpanStepPMF ν).support : Set (supportSpan ν))) = ⊤ := by
  apply (Submodule.map_injective_of_injective
    (show Function.Injective
      (((supportSpan ν).subtype : supportSpan ν →ₗ[ℤ] LatticePoint 2)) from
        Subtype.coe_injective))
  rw [Submodule.map_span, Submodule.map_subtype_top]
  have hsupp :
      ((supportSpan ν).subtype : supportSpan ν → LatticePoint 2) ''
          (supportSpanStepPMF ν).support = ν.support := by
    calc
      ((supportSpan ν).subtype : supportSpan ν → LatticePoint 2) ''
          (supportSpanStepPMF ν).support =
          (PMF.map (supportSpan ν).subtype (supportSpanStepPMF ν)).support := by
            symm
            simpa using
              (PMF.support_map (f := (supportSpan ν).subtype) (p := supportSpanStepPMF ν))
      _ = ν.support := by
            rw [supportSpanStepPMF_map_subtype_eq (ν := ν)]
  -- Proof comment: after pushing the restricted support back to `ℤ²`, we recover exactly the
  -- ambient support generating `supportSpan ν`.
  rw [hsupp]
  rfl

/-- Helper for Exercise 17.5.3: pushing the support-span step PMF back to `ℤ²` along the subtype
inclusion recovers the original step law. -/
private lemma supportSpanStepPMF_toMeasure_map_subtype_eq
    (ν : PMF (LatticePoint 2)) :
    Measure.map (supportSpan ν).subtype (supportSpanStepPMF ν).toMeasure = ν.toMeasure := by
  -- Route correction: prove the subtype pushforward first at the PMF layer, then convert to
  -- measures with `PMF.toMeasure_map`.
  rw [PMF.toMeasure_map (p := supportSpanStepPMF ν) (f := (supportSpan ν).subtype)
    (hf := Measurable.of_discrete)]
  simpa using congrArg PMF.toMeasure (supportSpanStepPMF_map_subtype_eq (ν := ν))

/-- Helper for Exercise 17.5.3: the origin law of the ambient walk is the pushforward of the
origin law on the actual support span. -/
-- TODO: Restore the support-span origin-law transport after the additive-convolution rewrite
-- shapes are synchronized.
private lemma supportSpanOriginLaw_map_subtype_eq
    (ν : PMF (LatticePoint 2)) :
    ∀ n : ℕ,
      Measure.map (supportSpan ν).subtype
          (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
            (0 : supportSpan ν))) =
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
  | 0 => by
      -- Proof comment: at time `0`, both laws are Dirac masses at the additive origin.
      change Measure.map (supportSpan ν).subtype (Measure.dirac (0 : supportSpan ν)) =
        Measure.dirac (0 : LatticePoint 2)
      simpa using Measure.map_dirac' (by fun_prop) (0 : supportSpan ν)
  | n + 1 => by
      let κsub : Kernel (supportSpan ν) (supportSpan ν) :=
        dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure
      let κ : Kernel (LatticePoint 2) (LatticePoint 2) := dirac_convolution_kernel ν.toMeasure
      have hpowSub : κsub ^ (n + 1) = κsub ∘ₖ (κsub ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κsub 1 n)
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      have hconvSub :
          κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν)) =
            ((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure := by
        simpa [κsub] using
          (diracConvolutionKernel_comp_measure_eq_conv_local
            (μ := ((κsub ^ n) (0 : supportSpan ν)))
            (ν := (supportSpanStepPMF ν).toMeasure))
      -- Proof comment: rewrite the successor origin law as one more convolution, push that
      -- convolution through the subtype inclusion, and then use the inductive origin-law bridge.
      calc
        Measure.map (supportSpan ν).subtype (((κsub ^ (n + 1)) (0 : supportSpan ν)))
          = Measure.map (supportSpan ν).subtype (κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν))) := by
              rw [hpowSub, Kernel.comp_apply]
        _ = Measure.map (supportSpan ν).subtype
              (((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure) := by
              rw [hconvSub]
        _ = Measure.map (supportSpan ν).subtype (((κsub ^ n) (0 : supportSpan ν))) ∗
              Measure.map (supportSpan ν).subtype (supportSpanStepPMF ν).toMeasure := by
              simpa using
                (Measure.map_conv_addMonoidHom
                  (μ := ((κsub ^ n) (0 : supportSpan ν)))
                  (ν := (supportSpanStepPMF ν).toMeasure)
                  ((supportSpan ν).subtype.toAddMonoidHom) (by fun_prop))
        _ = ((κ ^ n) (0 : LatticePoint 2)) ∗ ν.toMeasure := by
              rw [supportSpanOriginLaw_map_subtype_eq (ν := ν) n,
                supportSpanStepPMF_toMeasure_map_subtype_eq (ν := ν)]
        _ = κ ∘ₘ ((κ ^ n) (0 : LatticePoint 2)) := by
              symm
              simpa [κ] using
                (diracConvolutionKernel_comp_measure_eq_conv_local
                  (μ := ((κ ^ n) (0 : LatticePoint 2))) (ν := ν.toMeasure))
        _ = (κ ∘ₖ (κ ^ n)) (0 : LatticePoint 2) := by
              rw [Kernel.comp_apply]
        _ = (κ ^ (n + 1)) (0 : LatticePoint 2) := by
              rw [← hpow]

/-- Helper for Exercise 17.5.3: a linear equivalence from the rank-one support span to `ℤ`
transports the support-span origin laws to the corresponding integer-walk origin laws. -/
-- TODO: Restore the rank-one linear-equivalence transport after the measure-map/convolution
-- normal forms are synchronized.
private lemma supportSpanOriginLaw_map_equiv_eq_integerOriginLaw
    (ν : PMF (LatticePoint 2))
    (e : ℤ ≃ₗ[ℤ] supportSpan ν) :
    ∀ n : ℕ,
      Measure.map e.symm
          (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
            (0 : supportSpan ν))) =
        ((dirac_convolution_kernel
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n) (0 : ℤ))
  | 0 => by
      -- Proof comment: at time `0`, the linear equivalence also sends the support-span origin to
      -- the integer origin.
      change Measure.map e.symm (Measure.dirac (0 : supportSpan ν)) = Measure.dirac (0 : ℤ)
      simpa using Measure.map_dirac' (by fun_prop) (0 : supportSpan ν)
  | n + 1 => by
      let κsub : Kernel (supportSpan ν) (supportSpan ν) :=
        dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure
      let κZ : Kernel ℤ ℤ :=
        dirac_convolution_kernel (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure
      have hpowSub : κsub ^ (n + 1) = κsub ∘ₖ (κsub ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κsub 1 n)
      have hpowZ : κZ ^ (n + 1) = κZ ∘ₖ (κZ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κZ 1 n)
      have hconvSub :
          κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν)) =
            ((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure := by
        simpa [κsub] using
          (diracConvolutionKernel_comp_measure_eq_conv_local
            (μ := ((κsub ^ n) (0 : supportSpan ν)))
            (ν := (supportSpanStepPMF ν).toMeasure))
      have hmapStep :
          Measure.map e.symm (supportSpanStepPMF ν).toMeasure =
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure := by
        simpa using
          (PMF.toMeasure_map (p := supportSpanStepPMF ν) (f := e.symm.toEquiv)
            (hf := Measurable.of_discrete))
      -- Proof comment: rewrite the successor law as a convolution, push that convolution through
      -- the linear equivalence, and then identify the pushed-forward step law with the mapped PMF.
      calc
        Measure.map e.symm (((κsub ^ (n + 1)) (0 : supportSpan ν)))
          = Measure.map e.symm (κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν))) := by
              rw [hpowSub, Kernel.comp_apply]
        _ = Measure.map e.symm (((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure) := by
              rw [hconvSub]
        _ = Measure.map e.symm (((κsub ^ n) (0 : supportSpan ν))) ∗
              Measure.map e.symm (supportSpanStepPMF ν).toMeasure := by
              simpa using
                (Measure.map_conv_addMonoidHom
                  (μ := ((κsub ^ n) (0 : supportSpan ν)))
                  (ν := (supportSpanStepPMF ν).toMeasure)
                  (e.symm.toAddMonoidHom) (by fun_prop))
        _ = ((κZ ^ n) (0 : ℤ)) ∗ (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure := by
              rw [supportSpanOriginLaw_map_equiv_eq_integerOriginLaw (ν := ν) (e := e) n,
                hmapStep]
        _ = κZ ∘ₘ ((κZ ^ n) (0 : ℤ)) := by
              symm
              simpa [κZ] using
                (diracConvolutionKernel_comp_measure_eq_conv_local
                  (μ := ((κZ ^ n) (0 : ℤ)))
                  (ν := (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure))
        _ = (κZ ∘ₖ (κZ ^ n)) (0 : ℤ) := by
              rw [Kernel.comp_apply]
        _ = (κZ ^ (n + 1)) (0 : ℤ) := by
              rw [← hpowZ]

/-- Helper for Exercise 17.5.3: after passing through the support span and then a rank-one linear
equivalence, the ambient origin return masses agree with the integer-walk origin return masses. -/
-- TODO: Restore the singleton evaluation of the support-span and rank-one transport identities.
private lemma supportSpanOriginMass_eq_integerOriginMass
    (ν : PMF (LatticePoint 2))
    (e : ℤ ≃ₗ[ℤ] supportSpan ν) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) =
        ((dirac_convolution_kernel
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n) (0 : ℤ))
          ({0} : Set ℤ)
  | n => by
      -- Proof comment: evaluate the two transport identities on singleton origins; the relevant
      -- preimages are the singleton origins because both maps preserve zero.
      calc
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
            ({0} : Set (LatticePoint 2)) =
          Measure.map (supportSpan ν).subtype
            (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
              (0 : supportSpan ν)))
            ({0} : Set (LatticePoint 2)) := by
              rw [supportSpanOriginLaw_map_subtype_eq (ν := ν) n]
        _ = (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
              (0 : supportSpan ν))) ({0} : Set (supportSpan ν)) := by
              rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : LatticePoint 2))]
              have hpreimage :
                  (supportSpan ν).subtype ⁻¹' ({0} : Set (LatticePoint 2)) =
                    ({0} : Set (supportSpan ν)) := by
                ext z
                simp
              rw [hpreimage]
        _ = Measure.map e.symm
              (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
                (0 : supportSpan ν))) ({0} : Set ℤ) := by
              symm
              rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℤ))]
              have hpreimage :
                  e.symm ⁻¹' ({0} : Set ℤ) = ({0} : Set (supportSpan ν)) := by
                ext z
                simp [LinearEquiv.map_eq_zero_iff]
              rw [hpreimage]
        _ = ((dirac_convolution_kernel
              (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n) (0 : ℤ))
              ({0} : Set ℤ) := by
              rw [supportSpanOriginLaw_map_equiv_eq_integerOriginLaw (ν := ν) e n]

/-- Helper for Exercise 17.5.3: a rank-two support subgroup of `ℤ²` is linearly equivalent to
`ℤ²`. -/
private lemma supportSpan_nonemptyLinearEquivLatticePointTwo
    (ν : PMF (LatticePoint 2))
    (hHtwo : Module.finrank ℤ (supportSpan ν) = 2) :
    Nonempty (LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) := by
  -- Proof comment: over `ℤ`, every free rank-two module is abstractly isomorphic to `ℤ²`.
  refine ⟨LinearEquiv.ofFinrankEq (LatticePoint 2) (supportSpan ν) ?_⟩
  simpa [LatticePoint] using hHtwo.symm

/-- Helper for Exercise 17.5.3: a linear equivalence from the rank-two support span to `ℤ²`
transports the support-span origin laws to the corresponding planar origin laws. -/
private lemma mappedPlanarStepLaw_supportSpan_eq_top_of_supportSpanEquiv
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    supportSpan (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)) = ⊤ := by
  let μ : PMF (LatticePoint 2) := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  apply (Submodule.map_injective_of_injective e.injective)
  rw [Submodule.map_top, LinearEquiv.range, Submodule.map_span]
  change
    Submodule.span ℤ (((e : LatticePoint 2 → supportSpan ν) '' μ.support)) = ⊤
  have hsupp :
      ((e : LatticePoint 2 → supportSpan ν) '' μ.support) =
        (supportSpanStepPMF ν).support := by
    calc
      ((e : LatticePoint 2 → supportSpan ν) '' μ.support) =
          ((e : LatticePoint 2 → supportSpan ν) ''
            (e.symm.toEquiv '' (supportSpanStepPMF ν).support)) := by
              simp [μ, PMF.support_map]
      _ = (supportSpanStepPMF ν).support := by
            ext x
            constructor
            · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
              simpa using hz
            · intro hx
              refine ⟨e.symm x, ?_, by simp⟩
              exact ⟨x, hx, by simp⟩
  -- Proof comment: the forward equivalence `e` identifies the transported support with the full
  -- support of the support-span law, whose span is already all of `supportSpan ν`.
  simpa [hsupp] using supportSpanStepPMF_supportSpan_eq_top (ν := ν)

/-- Helper for Exercise 17.5.3: a linear equivalence from the rank-two support span to `ℤ²`
transports the support-span origin laws to the corresponding planar origin laws. -/
private lemma supportSpanOriginLaw_map_equiv_eq_latticeOriginLaw
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    ∀ n : ℕ,
      Measure.map e.symm
          (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
            (0 : supportSpan ν))) =
        ((dirac_convolution_kernel
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n)
          (0 : LatticePoint 2))
  | 0 => by
      -- Proof comment: at time `0`, the linear equivalence also sends the support-span origin to
      -- the planar origin.
      change Measure.map e.symm (Measure.dirac (0 : supportSpan ν)) =
        Measure.dirac (0 : LatticePoint 2)
      simpa using Measure.map_dirac' (by fun_prop) (0 : supportSpan ν)
  | n + 1 => by
      let κsub : Kernel (supportSpan ν) (supportSpan ν) :=
        dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure
      let κL : Kernel (LatticePoint 2) (LatticePoint 2) :=
        dirac_convolution_kernel (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure
      have hpowSub : κsub ^ (n + 1) = κsub ∘ₖ (κsub ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κsub 1 n)
      have hpowL : κL ^ (n + 1) = κL ∘ₖ (κL ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κL 1 n)
      have hconvSub :
          κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν)) =
            ((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure := by
        simpa [κsub] using
          (diracConvolutionKernel_comp_measure_eq_conv_local
            (μ := ((κsub ^ n) (0 : supportSpan ν)))
            (ν := (supportSpanStepPMF ν).toMeasure))
      have hmapStep :
          Measure.map e.symm (supportSpanStepPMF ν).toMeasure =
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure := by
        simpa using
          (PMF.toMeasure_map (p := supportSpanStepPMF ν) (f := e.symm.toEquiv)
            (hf := Measurable.of_discrete))
      -- Proof comment: rewrite the successor law as a convolution, push that convolution through
      -- the linear equivalence, and then identify the pushed-forward step law with the mapped PMF.
      calc
        Measure.map e.symm (((κsub ^ (n + 1)) (0 : supportSpan ν)))
          = Measure.map e.symm (κsub ∘ₘ ((κsub ^ n) (0 : supportSpan ν))) := by
              rw [hpowSub, Kernel.comp_apply]
        _ = Measure.map e.symm
              (((κsub ^ n) (0 : supportSpan ν)) ∗ (supportSpanStepPMF ν).toMeasure) := by
              rw [hconvSub]
        _ = Measure.map e.symm (((κsub ^ n) (0 : supportSpan ν))) ∗
              Measure.map e.symm (supportSpanStepPMF ν).toMeasure := by
              simpa using
                (Measure.map_conv_addMonoidHom
                  (μ := ((κsub ^ n) (0 : supportSpan ν)))
                  (ν := (supportSpanStepPMF ν).toMeasure)
                  (e.symm.toAddMonoidHom) (by fun_prop))
        _ = ((κL ^ n) (0 : LatticePoint 2)) ∗
              (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure := by
              rw [supportSpanOriginLaw_map_equiv_eq_latticeOriginLaw (ν := ν) (e := e) n, hmapStep]
        _ = κL ∘ₘ ((κL ^ n) (0 : LatticePoint 2)) := by
              symm
              simpa [κL] using
                (diracConvolutionKernel_comp_measure_eq_conv_local
                  (μ := ((κL ^ n) (0 : LatticePoint 2)))
                  (ν := (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure))
        _ = (κL ∘ₖ (κL ^ n)) (0 : LatticePoint 2) := by
              rw [Kernel.comp_apply]
        _ = (κL ^ (n + 1)) (0 : LatticePoint 2) := by
              rw [← hpowL]

/-- Helper for Exercise 17.5.3: after passing through the support span and then a rank-two linear
equivalence, the ambient origin return masses agree with the transported planar origin masses. -/
private lemma supportSpanOriginMass_eq_latticeOriginMass
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) =
        ((dirac_convolution_kernel
            (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n)
          (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2))
  | n => by
      -- Proof comment: evaluate the subtype and linear-equivalence transport identities on the
      -- singleton origin; both maps preserve `0`, so the relevant preimages are singleton origins.
      calc
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
            ({0} : Set (LatticePoint 2)) =
          Measure.map (supportSpan ν).subtype
            (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
              (0 : supportSpan ν)))
            ({0} : Set (LatticePoint 2)) := by
              rw [supportSpanOriginLaw_map_subtype_eq (ν := ν) n]
        _ = (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
              (0 : supportSpan ν))) ({0} : Set (supportSpan ν)) := by
              rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : LatticePoint 2))]
              have hpreimage :
                  (supportSpan ν).subtype ⁻¹' ({0} : Set (LatticePoint 2)) =
                    ({0} : Set (supportSpan ν)) := by
                ext z
                simp
              rw [hpreimage]
        _ = Measure.map e.symm
              (((dirac_convolution_kernel (supportSpanStepPMF ν).toMeasure ^ n)
                (0 : supportSpan ν))) ({0} : Set (LatticePoint 2)) := by
              symm
              rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : LatticePoint 2))]
              have hpreimage :
                  e.symm ⁻¹' ({0} : Set (LatticePoint 2)) = ({0} : Set (supportSpan ν)) := by
                ext z
                simp [LinearEquiv.map_eq_zero_iff]
              rw [hpreimage]
        _ = ((dirac_convolution_kernel
              (PMF.map e.symm.toEquiv (supportSpanStepPMF ν)).toMeasure ^ n)
              (0 : LatticePoint 2))
              ({0} : Set (LatticePoint 2)) := by
              rw [supportSpanOriginLaw_map_equiv_eq_latticeOriginLaw (ν := ν) e n]

/-- Helper for Exercise 17.5.3: a rank-one support subgroup of `ℤ²` is linearly equivalent to
`ℤ`. -/
private lemma supportSpan_nonemptyLinearEquivInt
    (ν : PMF (LatticePoint 2))
    (hHone :
      Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) = 1) :
    Nonempty
      (ℤ ≃ₗ[ℤ] Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) := by
  -- Proof comment: over `ℤ`, a rank-one free submodule is abstractly isomorphic to `ℤ`.
  refine ⟨LinearEquiv.ofFinrankEq ℤ _ ?_⟩
  simpa using hHone.symm

/-- Helper for Exercise 17.5.3: every lattice coordinate is controlled by the Euclidean
square norm up to an additive constant. -/
private lemma latticeCoordinate_abs_le_normSq_add_one
    (x : LatticePoint 2) (i : Fin 2) :
    |(x i : ℝ)| ≤ ‖latticeEmbedding x‖ ^ 2 + 1 := by
  have hcoord_sq_le : ‖(latticeEmbedding x) i‖ ^ 2 ≤ ‖latticeEmbedding x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg ‖(latticeEmbedding x) j‖)
        (Finset.mem_univ i)
  have hcoord_abs_le : |(x i : ℝ)| ≤ ‖latticeEmbedding x‖ := by
    have hsq : |(x i : ℝ)| ^ 2 ≤ ‖latticeEmbedding x‖ ^ 2 := by
      simpa [latticeEmbedding, sq_abs] using hcoord_sq_le
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq
  have hnorm_le : ‖latticeEmbedding x‖ ≤ ‖latticeEmbedding x‖ ^ 2 + 1 := by
    -- Proof comment: for a nonnegative real `r`, the elementary inequality `(r - 1)^2 ≥ 0`
    -- rearranges to `r ≤ r^2 + 1`.
    nlinarith [sq_nonneg (‖latticeEmbedding x‖ - 1)]
  -- Proof comment: combine the coordinate-vs-norm bound with the scalar inequality
  -- `r ≤ r^2 + 1`.
  exact le_trans hcoord_abs_le hnorm_le

/-- Helper for Exercise 17.5.3: every lattice coordinate is bounded by the Euclidean norm. -/
private lemma latticeCoordinate_abs_le_norm
    (x : LatticePoint 2) (i : Fin 2) :
    |(x i : ℝ)| ≤ ‖latticeEmbedding x‖ := by
  have hcoord_sq_le : ‖(latticeEmbedding x) i‖ ^ 2 ≤ ‖latticeEmbedding x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg ‖(latticeEmbedding x) j‖)
        (Finset.mem_univ i)
  have hsq : |(x i : ℝ)| ^ 2 ≤ ‖latticeEmbedding x‖ ^ 2 := by
    simpa [latticeEmbedding, sq_abs] using hcoord_sq_le
  -- Proof comment: compare the squared coordinate norm with the full squared Euclidean norm and
  -- then take square roots through monotonicity on nonnegative reals.
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq

/-- Helper for Exercise 17.5.3: each ambient coordinate of the planar step law has finite first
moment under the quadratic-moment hypothesis. -/
private lemma planarCoordinate_integrable_of_planarSecondMoment
    (ν : PMF (LatticePoint 2)) (i : Fin 2)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    Integrable (fun x : LatticePoint 2 ↦ (x i : ℝ)) ν.toMeasure := by
  -- Route correction: a single coordinate-vs-norm bound is enough here; no coordinate expansion
  -- of `‖latticeEmbedding x‖²` is needed.
  rw [integrable_iff_summable_norm_smul_pmf]
  have hquad :
      Summable (fun x : LatticePoint 2 ↦ ‖latticeEmbedding x‖ ^ 2 * (ν x).toReal) :=
    planarSecondMomentSummable ν hsecond
  have hmass : Summable (fun x : LatticePoint 2 ↦ (ν x).toReal) := by
    simpa using ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)
  have hdom :
      Summable (fun x : LatticePoint 2 ↦
        ‖latticeEmbedding x‖ ^ 2 * (ν x).toReal + (ν x).toReal) :=
    hquad.add hmass
  -- Proof comment: compare the weighted coordinate series against the summable quadratic-moment
  -- series plus the summable total-mass series.
  refine Summable.of_nonneg_of_le (fun x ↦ norm_nonneg _) ?_ hdom
  intro x
  have hν : 0 ≤ (ν x).toReal := ENNReal.toReal_nonneg
  calc
    ‖(ν x).toReal • (x i : ℝ)‖ = (ν x).toReal * |(x i : ℝ)| := by
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hν]
    _ ≤ (ν x).toReal * (‖latticeEmbedding x‖ ^ 2 + 1) := by
      exact mul_le_mul_of_nonneg_left (latticeCoordinate_abs_le_normSq_add_one x i) hν
    _ = ‖latticeEmbedding x‖ ^ 2 * (ν x).toReal + (ν x).toReal := by
      ring

/-- Helper for Exercise 17.5.3: each coordinate of the support-span step law has finite first
moment under the planar quadratic-moment hypothesis. -/
private lemma supportSpanCoordinate_integrable_of_planarSecondMoment
    (ν : PMF (LatticePoint 2)) (i : Fin 2)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    Integrable (fun x : supportSpan ν ↦ (x.1 i : ℝ)) (supportSpanStepPMF ν).toMeasure := by
  have hamb :
      Summable (fun x : LatticePoint 2 ↦ ‖(ν x).toReal • (x i : ℝ)‖) := by
    simpa [integrable_iff_summable_norm_smul_pmf] using
      (planarCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := i) hsecond)
  -- Proof comment: the support-span PMF is the ambient PMF restricted to the subtype, so the
  -- needed summability is just the ambient summable series restricted to `supportSpan ν`.
  rw [integrable_iff_summable_norm_smul_pmf]
  simpa [supportSpanStepPMF] using hamb.subtype (supportSpan ν)

/-- Helper for Exercise 17.5.3: the support-span step law inherits the planar zero-drift
coordinate identities. -/
private lemma supportSpanCoordinate_integral_eq_zero
    (ν : PMF (LatticePoint 2)) (i : Fin 2)
    (hmean : ∀ j : Fin 2, ∑' x : LatticePoint 2, (x j : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    ∫ x, (x.1 i : ℝ) ∂(supportSpanStepPMF ν).toMeasure = 0 := by
  have hambient_integrable :
      Integrable (fun x : LatticePoint 2 ↦ (x i : ℝ)) ν.toMeasure :=
    planarCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := i) hsecond
  -- Proof comment: transport the subtype integral to the ambient step law, then evaluate the
  -- ambient PMF integral by its weighted sum and insert the zero-drift hypothesis.
  calc
    ∫ x, (x.1 i : ℝ) ∂(supportSpanStepPMF ν).toMeasure
      = ∫ y, (y i : ℝ) ∂Measure.map (supportSpan ν).subtype
          (supportSpanStepPMF ν).toMeasure := by
            symm
            simpa using
              (integral_map
                (μ := (supportSpanStepPMF ν).toMeasure)
                (φ := (supportSpan ν).subtype)
                (f := fun y : LatticePoint 2 ↦ (y i : ℝ))
                (Measurable.of_discrete.aemeasurable)
                (Measurable.of_discrete.aestronglyMeasurable))
    _ = ∫ y, (y i : ℝ) ∂ν.toMeasure := by
          rw [supportSpanStepPMF_toMeasure_map_subtype_eq (ν := ν)]
    _ = ∑' x : LatticePoint 2, (ν x).toReal • (x i : ℝ) := by
          exact PMF.integral_eq_tsum ν (fun y : LatticePoint 2 ↦ (y i : ℝ)) hambient_integrable
    _ = 0 := by
          simpa [smul_eq_mul, mul_comm] using hmean i

/-- Helper for Exercise 17.5.3: in the rank-one case, the induced integer step law inherits finite
first moment and zero mean from a nonzero ambient coordinate. -/
private lemma integerStepLaw_integrable_mean_zero_of_planarRankOne
    (ν : PMF (LatticePoint 2))
    (e : ℤ ≃ₗ[ℤ] supportSpan ν)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    let μZ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
    Integrable (fun z : ℤ ↦ (z : ℝ)) μZ.toMeasure ∧
      ∫ z, (z : ℝ) ∂μZ.toMeasure = 0 := by
  let u : supportSpan ν := e 1
  have hu_ne : u ≠ 0 := by
    intro hu
    have hone : (1 : ℤ) = 0 := by
      exact e.injective (by simpa [u] using hu)
    exact one_ne_zero hone
  have hu_coord_nonzero : ∃ i : Fin 2, u.1 i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu_ne
    ext i
    exact h i
  rcases hu_coord_nonzero with ⟨i, hi⟩
  have hi_real : ((u.1 i : ℝ)) ≠ 0 := by
    exact_mod_cast hi
  have hcoord_repr :
      ∀ x : supportSpan ν, (e.symm x : ℝ) = ((u.1 i : ℝ)⁻¹) * (x.1 i : ℝ) := by
    intro x
    have hx_eq : x = (e.symm x) • u := by
      calc
        x = e (e.symm x) := by simp
        _ = e ((e.symm x) • (1 : ℤ)) := by simp
        _ = (e.symm x) • e 1 := by
              simpa using e.toAddMonoidHom.map_zsmul (1 : ℤ) (e.symm x)
        _ = (e.symm x) • u := by rfl
    have hx_coord : (x.1 i : ℝ) = (e.symm x : ℝ) * (u.1 i : ℝ) := by
      have hx_coord_int : x.1 i = (e.symm x) * u.1 i := by
        simpa [zsmul_eq_mul] using congrArg (fun y : supportSpan ν ↦ y.1 i) hx_eq
      exact_mod_cast hx_coord_int
    have hdiv : (e.symm x : ℝ) = (x.1 i : ℝ) / (u.1 i : ℝ) := by
      apply (eq_div_iff hi_real).2
      simpa [mul_comm] using hx_coord.symm
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hsupport_integrable :
      Integrable (fun x : supportSpan ν ↦ (e.symm x : ℝ)) (supportSpanStepPMF ν).toMeasure := by
    have hcoord_int :
        Integrable (fun x : supportSpan ν ↦ (x.1 i : ℝ)) (supportSpanStepPMF ν).toMeasure :=
      supportSpanCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := i) hsecond
    -- Proof comment: once a nonzero coordinate of the generator is fixed, the integer coordinate
    -- `e.symm x` is a constant multiple of the ambient `i`th coordinate.
    rw [show (fun x : supportSpan ν ↦ (e.symm x : ℝ)) =
      fun x : supportSpan ν ↦ ((u.1 i : ℝ)⁻¹) * (x.1 i : ℝ) by
        funext x
        exact hcoord_repr x]
    exact hcoord_int.const_mul ((u.1 i : ℝ)⁻¹)
  have hsupport_mean_zero :
      ∫ x, (e.symm x : ℝ) ∂(supportSpanStepPMF ν).toMeasure = 0 := by
    -- Proof comment: the same coordinate identity transports the ambient zero-drift condition to
    -- the induced integer coordinate.
    rw [show (fun x : supportSpan ν ↦ (e.symm x : ℝ)) =
      fun x : supportSpan ν ↦ ((u.1 i : ℝ)⁻¹) * (x.1 i : ℝ) by
        funext x
        exact hcoord_repr x]
    rw [integral_const_mul]
    simp [supportSpanCoordinate_integral_eq_zero (ν := ν) (i := i) hmean hsecond]
  let μZ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  have hmapStep :
      Measure.map e.symm (supportSpanStepPMF ν).toMeasure = μZ.toMeasure := by
    simpa [μZ] using
      (PMF.toMeasure_map (p := supportSpanStepPMF ν) (f := e.symm.toEquiv)
        (hf := Measurable.of_discrete))
  constructor
  · rw [← hmapStep]
    exact
      (integrable_map_measure
        (μ := (supportSpanStepPMF ν).toMeasure)
        (f := e.symm)
        (g := fun z : ℤ ↦ (z : ℝ))
        Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 hsupport_integrable
  · rw [← hmapStep]
    calc
      ∫ z, (z : ℝ) ∂Measure.map e.symm (supportSpanStepPMF ν).toMeasure
        = ∫ x, (e.symm x : ℝ) ∂(supportSpanStepPMF ν).toMeasure := by
            simpa using
              (integral_map
                (μ := (supportSpanStepPMF ν).toMeasure)
                (φ := e.symm)
                (f := fun z : ℤ ↦ (z : ℝ))
                (Measurable.of_discrete.aemeasurable)
                (Measurable.of_discrete.aestronglyMeasurable))
      _ = 0 := hsupport_mean_zero

/-- Helper for Exercise 17.5.3: the two transported standard basis vectors in `supportSpan ν`
form the columns of the rank-two change-of-basis matrix attached to `e`. -/
private abbrev supportSpanEquivBasisVector
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) (i : Fin 2) : supportSpan ν :=
  e (Pi.single i (1 : ℤ))

/-- Helper for Exercise 17.5.3: the determinant of the ambient `2 × 2` matrix whose columns are
the transported basis vectors of `e`. -/
private abbrev supportSpanEquivMatrix
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j ↦ (supportSpanEquivBasisVector e j).1 i

/-- Helper for Exercise 17.5.3: the determinant of the ambient `2 × 2` matrix whose columns are
the transported basis vectors of `e`. -/
private abbrev supportSpanEquivDet
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) : ℤ :=
  Matrix.det (supportSpanEquivMatrix e)

/-- Helper for Exercise 17.5.3: the integer matrix of `e` acts on lattice points as the ambient
inclusion of the support-span equivalence. -/
private noncomputable def supportSpanEquivIntLinearMap
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    LatticePoint 2 →ₗ[ℤ] LatticePoint 2 :=
  Matrix.toLin' (supportSpanEquivMatrix e)

/-- Helper for Exercise 17.5.3: the integer change-of-basis map is exactly `subtype ∘ e`. -/
private lemma supportSpanEquivIntLinearMap_eq_subtype_comp
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    supportSpanEquivIntLinearMap e =
      (supportSpan ν).subtype.comp (e : LatticePoint 2 →ₗ[ℤ] supportSpan ν) := by
  -- Proof comment: both linear maps send the standard basis of `ℤ²` to the transported support
  -- basis vectors, so basis extensionality identifies them.
  apply (Pi.basisFun ℤ (Fin 2)).ext
  intro i
  ext j
  simp [supportSpanEquivIntLinearMap, supportSpanEquivMatrix, supportSpanEquivBasisVector]

/-- Helper for Exercise 17.5.3: the transported basis vectors of `e` have nonzero determinant, so
their ambient images form a real basis of `ℝ²`. -/
private lemma supportSpanEquiv_det_ne_zero
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    supportSpanEquivDet e ≠ 0 := by
  have hA_injective : Function.Injective (supportSpanEquivIntLinearMap e) := by
    -- Proof comment: the integer matrix map is definitionally `subtype ∘ e`, hence injective.
    have hsubtype_injective :
        Function.Injective ((supportSpan ν).subtype : supportSpan ν → LatticePoint 2) := by
      intro x y hxy
      exact Subtype.ext hxy
    simpa [supportSpanEquivIntLinearMap_eq_subtype_comp (ν := ν) e] using
      (hsubtype_injective.comp e.injective)
  have hA_ker :
      LinearMap.ker (supportSpanEquivIntLinearMap e) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hA_injective
  intro hdet
  have hdetA : LinearMap.det (supportSpanEquivIntLinearMap e) = 0 := by
    simpa [supportSpanEquivDet, supportSpanEquivIntLinearMap] using hdet
  have hA_ker_ne :
      LinearMap.ker (supportSpanEquivIntLinearMap e) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := supportSpanEquivIntLinearMap e)).mp hdetA
  -- Proof comment: a zero determinant would force a nontrivial kernel in `ℤ²`, but `A` is the
  -- injective composition `subtype ∘ e`.
  exact hA_ker_ne hA_ker

/-- Helper for Exercise 17.5.3: the real matrix obtained by casting the integer support-span
change-of-basis matrix is nonsingular. -/
private lemma supportSpanEquiv_realMatrix_det_ne_zero
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    Matrix.det ((Int.castRingHom ℝ).mapMatrix (supportSpanEquivMatrix e)) ≠ 0 := by
  -- Proof comment: determinant commutes with the integer-to-real cast, and the integer
  -- determinant is already known to be nonzero.
  rw [← RingHom.map_det]
  exact Int.cast_ne_zero.mpr (supportSpanEquiv_det_ne_zero (ν := ν) e)

/-- Helper for Exercise 17.5.3: the standard coordinate linear equivalence identifies
`EuclideanSpace ℝ (Fin 2)` with ordinary `ℝ²` functions. -/
private noncomputable abbrev euclideanCoordinateLinearEquiv :
    EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] Fin 2 → ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv

/-- Helper for Exercise 17.5.3: the rank-two support-span equivalence defines a real linear map
whose columns are the embedded transported basis vectors. -/
private noncomputable def supportSpanEquivRealLinearMap
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin ((Int.castRingHom ℝ).mapMatrix (supportSpanEquivMatrix e))

/-- Helper for Exercise 17.5.3: the real linear map attached to `e` sends the embedded inverse
coordinates back to the ambient support-span point. -/
private lemma supportSpanEquivRealLinearMap_apply_latticeEmbedding_symm
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν)
    (x : supportSpan ν) :
    supportSpanEquivRealLinearMap e (latticeEmbedding (e.symm x)) = latticeEmbedding x.1 := by
  have hInt :
      supportSpanEquivIntLinearMap e (e.symm x) = x.1 := by
    -- Proof comment: over `ℤ²`, the matrix map is exactly `subtype ∘ e`, so applying it to the
    -- inverse image `e.symm x` gives back the ambient support-span point.
    rw [supportSpanEquivIntLinearMap_eq_subtype_comp (ν := ν) e]
    simp
  ext j
  -- Proof comment: pass to the coordinate model of `toEuclideanLin`, rewrite the cast matrix
  -- product with `RingHom.map_mulVec`, and finish from the integer matrix identity above.
  rw [supportSpanEquivRealLinearMap, latticeEmbedding, Matrix.toEuclideanLin_apply_piLp_toLp]
  change
    Matrix.mulVec ((Int.castRingHom ℝ).mapMatrix (supportSpanEquivMatrix e))
        (fun i ↦ ((e.symm x i : ℤ) : ℝ)) j =
      (x.1 j : ℝ)
  have hcoord :
      Matrix.mulVec (supportSpanEquivMatrix e) (e.symm x) j = x.1 j := by
    simpa [supportSpanEquivIntLinearMap, Matrix.toLin'_apply] using
      congrArg (fun y : LatticePoint 2 ↦ y j) hInt
  calc
    Matrix.mulVec ((Int.castRingHom ℝ).mapMatrix (supportSpanEquivMatrix e))
        (fun i ↦ ((e.symm x i : ℤ) : ℝ)) j
      = ((Matrix.mulVec (supportSpanEquivMatrix e) (e.symm x) j : ℤ) : ℝ) := by
          symm
          exact RingHom.map_mulVec (Int.castRingHom ℝ) (supportSpanEquivMatrix e) (e.symm x) j
    _ = (x.1 j : ℝ) := by
          exact_mod_cast hcoord

/-- Helper for Exercise 17.5.3: the real change-of-basis map attached to `e` is injective. -/
private lemma supportSpanEquivRealLinearMap_injective
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    Function.Injective (supportSpanEquivRealLinearMap e) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    (Int.castRingHom ℝ).mapMatrix (supportSpanEquivMatrix e)
  have hA_unit : IsUnit (Matrix.det A) :=
    isUnit_iff_ne_zero.mpr (supportSpanEquiv_realMatrix_det_ne_zero (ν := ν) e)
  have hker :
      LinearMap.ker (supportSpanEquivRealLinearMap e) = ⊥ := by
    -- Proof comment: the cast support-span matrix has nonzero determinant, so its Euclidean
    -- linear map has trivial kernel.
    change LinearMap.ker (Matrix.toEuclideanLin A) = ⊥
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact
      Matrix.ker_toLin_eq_bot
        (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A hA_unit
  exact LinearMap.ker_eq_bot.mp hker

/-- Helper for Exercise 17.5.3: the real change-of-basis map induced by `e` is a linear
equivalence of `ℝ²`. -/
private noncomputable def supportSpanEquivRealLinearEquiv
    {ν : PMF (LatticePoint 2)}
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.ofInjectiveEndo
    (supportSpanEquivRealLinearMap e)
    (supportSpanEquivRealLinearMap_injective (ν := ν) e)

/-- Helper for Exercise 17.5.3: each transported coordinate of `e.symm x` is a fixed real linear
form in the ambient coordinates of `x`. -/
private lemma supportSpanEquiv_coordinateLinearForm
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν)
    (i : Fin 2) :
    ∃ a : Fin 2 → ℝ, ∀ x : supportSpan ν,
      ((e.symm x i : ℤ) : ℝ) = ∑ j : Fin 2, a j * (x.1 j : ℝ) := by
  let B := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let ℓ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.projₗ i).comp (supportSpanEquivRealLinearEquiv e).symm.toLinearMap
  refine ⟨fun j ↦ ℓ (B j), ?_⟩
  intro x
  have hsymm :
      (supportSpanEquivRealLinearEquiv e).symm (latticeEmbedding x.1) =
        latticeEmbedding (e.symm x) := by
    -- Proof comment: the inverse real linear equivalence recovers the embedded inverse lattice
    -- point because the forward map was already identified on `latticeEmbedding (e.symm x)`.
    apply (supportSpanEquivRealLinearEquiv e).symm_apply_eq.mpr
    simpa [supportSpanEquivRealLinearEquiv] using
      (supportSpanEquivRealLinearMap_apply_latticeEmbedding_symm (ν := ν) (e := e) x).symm
  calc
    ((e.symm x i : ℤ) : ℝ) = (latticeEmbedding (e.symm x)) i := by
      simp [latticeEmbedding]
    _ = ((supportSpanEquivRealLinearEquiv e).symm (latticeEmbedding x.1)) i := by
      rw [hsymm]
    _ = ℓ (latticeEmbedding x.1) := by
      rfl
    _ = ∑ j : Fin 2, (B.repr (latticeEmbedding x.1) j) * ℓ (B j) := by
      -- Proof comment: expand the linear functional on the Euclidean standard basis and collect
      -- the basis coefficients of `latticeEmbedding x.1`.
      rw [← B.sum_repr (latticeEmbedding x.1), map_sum]
      simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ j : Fin 2, ℓ (B j) * (x.1 j : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [B, latticeEmbedding, mul_comm]

/-- Helper for Exercise 17.5.3: a rank-two support-span equivalence has an inverse bounded by a
fixed multiple of the ambient Euclidean norm. -/
private lemma supportSpanEquiv_inverseNormBound
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    ∃ K > 0, ∀ x : supportSpan ν,
      ‖latticeEmbedding (e.symm x)‖ ≤ K * ‖latticeEmbedding x.1‖ := by
  let A := supportSpanEquivRealLinearMap e
  have hA_ker : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact supportSpanEquivRealLinearMap_injective (ν := ν) e
  obtain ⟨K, hK_pos, hK⟩ := A.exists_antilipschitzWith hA_ker
  refine ⟨K, hK_pos, ?_⟩
  intro x
  have hforward :
      A (latticeEmbedding (e.symm x)) = latticeEmbedding x.1 := by
    exact supportSpanEquivRealLinearMap_apply_latticeEmbedding_symm (ν := ν) (e := e) x
  -- Proof comment: the embedded inverse image is recovered by applying the anti-Lipschitz bound
  -- to the real change-of-basis map at the support-span point.
  calc
    ‖latticeEmbedding (e.symm x)‖ ≤ (K : ℝ) * ‖A (latticeEmbedding (e.symm x))‖ := by
          exact ZeroHomClass.bound_of_antilipschitz A hK (latticeEmbedding (e.symm x))
    _ = (K : ℝ) * ‖latticeEmbedding x.1‖ := by rw [hforward]

/-- Helper for Exercise 17.5.3: a rank-two support-span equivalence distorts the ambient
Euclidean square norm by at most a fixed multiplicative constant. -/
private lemma supportSpanEquiv_normSqBound
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν) :
    ∃ C > 0, ∀ x : supportSpan ν,
      ‖latticeEmbedding (e.symm x)‖ ^ 2 ≤ C * ‖latticeEmbedding x.1‖ ^ 2 := by
  obtain ⟨K, hK_pos, hK⟩ := supportSpanEquiv_inverseNormBound (ν := ν) e
  refine ⟨K ^ (2 : ℕ), by positivity, ?_⟩
  intro x
  have hK_nonneg : 0 ≤ K := le_of_lt hK_pos
  have hnorm_nonneg : 0 ≤ ‖latticeEmbedding (e.symm x)‖ := norm_nonneg _
  have hspan_nonneg : 0 ≤ ‖latticeEmbedding x.1‖ := norm_nonneg _
  have hbase : ‖latticeEmbedding (e.symm x)‖ ≤ K * ‖latticeEmbedding x.1‖ := hK x
  nlinarith

/-- Helper for Exercise 17.5.3: mapping a PMF along an equivalence rewrites the target mass by
the inverse point. -/
private lemma pmfMap_apply_of_equiv
    {α β : Type*} (p : PMF α) (e : α ≃ β) (b : β) :
    PMF.map e p b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    by_cases hba : b = e a
    · exfalso
      exact ha (by simpa using congrArg e.symm hba.symm)
    · simp [hba]

/-- Helper for Exercise 17.5.3: each coordinate of the transported planar law has finite first
moment and zero mean. -/
private lemma mappedPlanarCoordinate_integrable_mean_zero_of_supportSpanEquiv
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤)
    (i : Fin 2) :
    let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
    Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) μ.toMeasure ∧
      ∫ z, (z i : ℝ) ∂μ.toMeasure = 0 := by
  let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  change
    Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) μ.toMeasure ∧
      ∫ z, (z i : ℝ) ∂μ.toMeasure = 0
  obtain ⟨a, hcoord_repr⟩ := supportSpanEquiv_coordinateLinearForm (ν := ν) e i
  have hterm_integrable (j : Fin 2) :
      Integrable (fun x : supportSpan ν ↦ a j * (x.1 j : ℝ))
        (supportSpanStepPMF ν).toMeasure := by
    -- Proof comment: each transported coordinate is a fixed scalar multiple of one ambient
    -- support-span coordinate, so its integrability comes from the coordinate first moment.
    exact
      (supportSpanCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := j) hsecond).const_mul
        (a j)
  have hsupport_integrable :
      Integrable (fun x : supportSpan ν ↦ ((e.symm x i : ℤ) : ℝ))
        (supportSpanStepPMF ν).toMeasure := by
    -- Proof comment: replace the transported coordinate by the fixed linear form supplied by the
    -- inverse real change-of-basis map and sum the two coordinate integrability facts.
    have hrewrite :
        (fun x : supportSpan ν ↦ ((e.symm x i : ℤ) : ℝ)) =
          fun x : supportSpan ν ↦ ∑ j : Fin 2, a j * (x.1 j : ℝ) := by
      funext x
      simpa using hcoord_repr x
    rw [hrewrite]
    exact integrable_finset_sum Finset.univ fun j _ ↦ hterm_integrable j
  have hsupport_mean_zero :
      ∫ x, ((e.symm x i : ℤ) : ℝ) ∂(supportSpanStepPMF ν).toMeasure = 0 := by
    -- Proof comment: the same linear-form rewrite reduces the transported mean to the sum of the
    -- two already vanishing support-span coordinate means.
    calc
      ∫ x, ((e.symm x i : ℤ) : ℝ) ∂(supportSpanStepPMF ν).toMeasure
        = ∫ x, ∑ j : Fin 2, a j * (x.1 j : ℝ) ∂(supportSpanStepPMF ν).toMeasure := by
            congr 1
            funext x
            simpa using hcoord_repr x
      _ = ∑ j : Fin 2,
            ∫ x, a j * (x.1 j : ℝ) ∂(supportSpanStepPMF ν).toMeasure := by
            exact integral_finset_sum Finset.univ fun j _ ↦ hterm_integrable j
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j hj
            rw [integral_const_mul]
            simp [supportSpanCoordinate_integral_eq_zero (ν := ν) (i := j) hmean hsecond]
  have hmapStep :
      Measure.map e.symm (supportSpanStepPMF ν).toMeasure = μ.toMeasure := by
    simpa [μ] using
      (PMF.toMeasure_map (p := supportSpanStepPMF ν) (f := e.symm.toEquiv)
        (hf := Measurable.of_discrete))
  constructor
  · rw [← hmapStep]
    exact
      (integrable_map_measure
        (μ := (supportSpanStepPMF ν).toMeasure)
        (f := e.symm)
        (g := fun z : LatticePoint 2 ↦ (z i : ℝ))
        Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 hsupport_integrable
  · rw [← hmapStep]
    calc
      ∫ z, (z i : ℝ) ∂Measure.map e.symm (supportSpanStepPMF ν).toMeasure
        = ∫ x, ((e.symm x i : ℤ) : ℝ) ∂(supportSpanStepPMF ν).toMeasure := by
            simpa using
              (integral_map
                (μ := (supportSpanStepPMF ν).toMeasure)
                (φ := e.symm)
                (f := fun z : LatticePoint 2 ↦ (z i : ℝ))
                (Measurable.of_discrete.aemeasurable)
                (Measurable.of_discrete.aestronglyMeasurable))
      _ = 0 := hsupport_mean_zero

/-- Helper for Exercise 17.5.3: the transported planar law keeps a summable quadratic moment. -/
private lemma mappedPlanarSecondMomentSummable_of_supportSpanEquiv
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
    Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
  let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  change Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal)
  obtain ⟨C, hC_pos, hC⟩ := supportSpanEquiv_normSqBound (ν := ν) e
  have hsupport_quad :
      Summable
        (fun x : supportSpan ν ↦ ‖latticeEmbedding x.1‖ ^ 2 * ((supportSpanStepPMF ν) x).toReal) := by
    simpa [supportSpanStepPMF] using
      (planarSecondMomentSummable ν hsecond).subtype (supportSpan ν)
  have hdom :
      Summable
        (fun z : LatticePoint 2 ↦
          C * (‖latticeEmbedding (e z).1‖ ^ 2 * ((supportSpanStepPMF ν) (e z)).toReal)) := by
    simpa using (e.toEquiv.summable_iff).2 (hsupport_quad.mul_left C)
  refine Summable.of_nonneg_of_le (fun z ↦ ?_) (fun z ↦ ?_) hdom
  · exact mul_nonneg (sq_nonneg ‖latticeEmbedding z‖) ENNReal.toReal_nonneg
  · have hμ :
        μ z = (supportSpanStepPMF ν) (e z) := by
          simpa [μ] using
            pmfMap_apply_of_equiv (p := supportSpanStepPMF ν) (e := e.symm.toEquiv) z
    have hCz :
        ‖latticeEmbedding z‖ ^ 2 ≤ C * ‖latticeEmbedding (e z).1‖ ^ 2 := by
      simpa using hC (e z)
    have hmass_nonneg : 0 ≤ ((supportSpanStepPMF ν) (e z)).toReal := ENNReal.toReal_nonneg
    calc
      ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal
        = ‖latticeEmbedding z‖ ^ 2 * ((supportSpanStepPMF ν) (e z)).toReal := by
            rw [hμ]
      _ ≤ (C * ‖latticeEmbedding (e z).1‖ ^ 2) * ((supportSpanStepPMF ν) (e z)).toReal := by
            exact mul_le_mul_of_nonneg_right hCz hmass_nonneg
      _ = C * (‖latticeEmbedding (e z).1‖ ^ 2 * ((supportSpanStepPMF ν) (e z)).toReal) := by
            ring

/-- Helper for Exercise 17.5.3: after transporting the support-span step law through a rank-two
linear equivalence, the induced planar law still has zero coordinate means and finite quadratic
moment. -/
private lemma mappedPlanarStepLaw_transportHypotheses_of_supportSpanEquiv
    (ν : PMF (LatticePoint 2))
    (e : LatticePoint 2 ≃ₗ[ℤ] supportSpan ν)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
    (∀ i : Fin 2, Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) μ.toMeasure ∧
        ∫ z, (z i : ℝ) ∂μ.toMeasure = 0) ∧
      Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
  let μ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  change
    (∀ i : Fin 2, Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) μ.toMeasure ∧
        ∫ z, (z i : ℝ) ∂μ.toMeasure = 0) ∧
      Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal)
  refine ⟨?_, ?_⟩
  · intro i
    -- Proof comment: the coordinate transport is now isolated in a dedicated helper, so this
    -- lemma only packages the two first-moment facts together with the second moment.
    simpa [μ] using
      mappedPlanarCoordinate_integrable_mean_zero_of_supportSpanEquiv
        (ν := ν) (e := e) hmean hsecond i
  · simpa [μ] using
      mappedPlanarSecondMomentSummable_of_supportSpanEquiv
        (ν := ν) (e := e) hsecond

/-- Helper for Exercise 17.5.3: the lattice embedding `ℤ² → ℝ²` is injective. -/
private lemma latticeEmbedding_injective :
    Function.Injective (latticeEmbedding : LatticePoint 2 → EuclideanSpace ℝ (Fin 2)) := by
  intro x y hxy
  -- Proof comment: equality in `ℝ²` is coordinatewise, and each coordinate is the usual cast
  -- from `ℤ` to `ℝ`.
  ext i
  have hcoord : (x i : ℝ) = (y i : ℝ) := by
    simpa [latticeEmbedding] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v i) hxy
  exact_mod_cast hcoord

/-- Helper for Exercise 17.5.3: the lattice embedding sends the `i`th unit lattice vector to the
corresponding Euclidean single-coordinate vector. -/
private lemma latticeEmbedding_single_eq_single (i : Fin 2) :
    latticeEmbedding (Pi.single i (1 : ℤ) : LatticePoint 2) =
      EuclideanSpace.single i (1 : ℝ) := by
  -- Proof comment: both vectors have coordinate `1` at `i` and `0` elsewhere.
  ext j
  by_cases hij : j = i
  · subst hij
    simp
  · simp [latticeEmbedding, EuclideanSpace.basisFun_apply, hij]

/-- Helper for Exercise 17.5.3: the lattice embedding commutes with integer scalar
multiplication. -/
private lemma latticeEmbedding_zsmul
    (n : ℤ) (x : LatticePoint 2) :
    latticeEmbedding (n • x) = (n : ℝ) • latticeEmbedding x := by
  -- Proof comment: the embedding is coordinatewise, so integer scalar multiplication commutes
  -- with the cast into `ℝ²`.
  ext i
  simp [latticeEmbedding, zsmul_eq_mul]

/-- Helper for Exercise 17.5.3: the Chapter 15 period set is closed under addition. -/
private lemma add_mem_charFunPeriodSet
    {x y t : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ charFunPeriodSet t) (hy : y ∈ charFunPeriodSet t) :
    x + y ∈ charFunPeriodSet t := by
  -- Proof comment: translate both membership hypotheses to integral `2π` phases and add the
  -- resulting identities.
  rcases mem_charFunPeriodSet_iff_exists_int.mp hx with ⟨m, hm⟩
  rcases mem_charFunPeriodSet_iff_exists_int.mp hy with ⟨n, hn⟩
  rw [mem_charFunPeriodSet_iff_exists_int]
  refine ⟨m + n, ?_⟩
  calc
    inner ℝ (x + y) t = inner ℝ x t + inner ℝ y t := by rw [inner_add_left]
    _ = (2 * Real.pi : ℝ) * m + (2 * Real.pi : ℝ) * n := by rw [hm, hn]
    _ = (2 * Real.pi : ℝ) * ((m : ℝ) + n) := by ring
    _ = (2 * Real.pi : ℝ) * (((m + n : ℤ) : ℝ)) := by
          have hcast : (((m + n : ℤ) : ℝ)) = (m : ℝ) + n := by
            exact_mod_cast (show (m + n : ℤ) = m + n by rfl)
          rw [hcast]

/-- Helper for Exercise 17.5.3: the Chapter 15 period set is closed under integer scalar
multiplication. -/
private lemma zsmul_mem_charFunPeriodSet
    {x t : EuclideanSpace ℝ (Fin 2)} (n : ℤ)
    (hx : x ∈ charFunPeriodSet t) :
    n • x ∈ charFunPeriodSet t := by
  rcases mem_charFunPeriodSet_iff_exists_int.mp hx with ⟨m, hm⟩
  rw [mem_charFunPeriodSet_iff_exists_int]
  refine ⟨n * m, ?_⟩
  calc
    inner ℝ (n • x) t = inner ℝ ((n : ℝ) • x) t := by
      rw [Int.cast_smul_eq_zsmul ℝ]
    _ = (n : ℝ) * inner ℝ x t := by
      rw [real_inner_smul_left]
    _ = (n : ℝ) * ((2 * Real.pi : ℝ) * m) := by
      rw [hm]
    _ = (2 * Real.pi : ℝ) * (((n * m : ℤ) : ℝ)) := by
      simp [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 17.5.3: any support point of the planar step law lies in the Chapter 15
period set whenever the step-law characteristic function equals `1` at frequency `t`. -/
private lemma support_mem_charFunPeriodSet_of_charFun_eq_one
    (ν : PMF (LatticePoint 2)) {t : EuclideanSpace ℝ (Fin 2)}
    (hφ : charFun (ν.toMeasure.map latticeEmbedding) t = 1) {z : LatticePoint 2}
    (hz : z ∈ ν.support) :
    latticeEmbedding z ∈ charFunPeriodSet t := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := ν.toMeasure.map latticeEmbedding
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using
      Measure.isProbabilityMeasure_map
        (μ := ν.toMeasure)
        (f := latticeEmbedding)
        (Measurable.of_discrete.aemeasurable :
          AEMeasurable latticeEmbedding ν.toMeasure)
  have hperiod : μ (charFunPeriodSet t) = 1 := by
    simpa [μ] using measure_charFunPeriodSet_eq_one_of_charFun_eq_one (μ := μ) hφ
  have hperiod_meas : MeasurableSet (charFunPeriodSet t) := by
    have hcont :
        Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦
          Complex.exp ((((inner ℝ x t : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    simpa [charFunPeriodSet] using
      (isClosed_eq hcont continuous_const).measurableSet
  by_contra hzperiod
  have hcompl_zero : μ ((charFunPeriodSet t)ᶜ) = 0 := by
    simpa [hperiod] using measure_compl (μ := μ) hperiod_meas
  have hsingle_subset :
      ({latticeEmbedding z} : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (charFunPeriodSet t)ᶜ := by
    intro x hx
    have hxz : x = latticeEmbedding z := by simpa using hx
    simpa [hxz, hzperiod]
  have hsingle_zero :
      μ ({latticeEmbedding z} : Set (EuclideanSpace ℝ (Fin 2))) = 0 :=
    measure_mono_null hsingle_subset hcompl_zero
  have hz_mass :
      0 < μ ({latticeEmbedding z} : Set (EuclideanSpace ℝ (Fin 2))) := by
    dsimp [μ]
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton (latticeEmbedding z))]
    have hpreimage :
        latticeEmbedding ⁻¹' ({latticeEmbedding z} : Set (EuclideanSpace ℝ (Fin 2))) =
          ({z} : Set (LatticePoint 2)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact latticeEmbedding_injective hx
      · intro hx
        simpa [hx]
    rw [hpreimage, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
    exact bot_lt_iff_ne_bot.mpr ((PMF.mem_support_iff ν z).1 hz)
  exact (ne_of_gt hz_mass) hsingle_zero

/-- Helper for Exercise 17.5.3: if the planar step-law characteristic function equals `1`, then
every vector in the additive support span has phase in the Chapter 15 period set. -/
private lemma supportSpan_mem_charFunPeriodSet_of_charFun_eq_one
    (ν : PMF (LatticePoint 2)) {t : EuclideanSpace ℝ (Fin 2)}
    (hφ : charFun (ν.toMeasure.map latticeEmbedding) t = 1) :
    ∀ {x : LatticePoint 2}, x ∈ supportSpan ν → latticeEmbedding x ∈ charFunPeriodSet t := by
  intro x hx
  -- Proof comment: the support span is generated by support atoms, and the period set is stable
  -- under `0`, addition, and integer scalar multiplication.
  induction hx using Submodule.span_induction with
  | mem y hy =>
      exact support_mem_charFunPeriodSet_of_charFun_eq_one
        (ν := ν) (hφ := hφ) ((PMF.mem_support_iff ν y).2 hy)
  | zero =>
      rw [mem_charFunPeriodSet_iff_exists_int]
      refine ⟨0, ?_⟩
      simp [latticeEmbedding_zero]
  | add y w _ _ hy hw =>
      simpa [latticeEmbedding_add] using add_mem_charFunPeriodSet hy hw
  | smul n y _ hy =>
      rw [latticeEmbedding_zsmul]
      simpa [Int.cast_smul_eq_zsmul ℝ] using
        zsmul_mem_charFunPeriodSet (t := t) n hy

/-- Helper for Exercise 17.5.3: when the planar support span is all of `ℤ²`, the characteristic
function can equal `1` inside `(-π, π)^2` only at the origin. -/
private lemma planarCharFun_eq_one_only_at_zero_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤)
    {t : EuclideanSpace ℝ (Fin 2)}
    (ht : ∀ i : Fin 2, |t i| < Real.pi)
    (hφ : charFun (ν.toMeasure.map latticeEmbedding) t = 1) :
    t = 0 := by
  ext i
  have hi_mem :
      latticeEmbedding (Pi.single i (1 : ℤ) : LatticePoint 2) ∈ charFunPeriodSet t := by
    apply supportSpan_mem_charFunPeriodSet_of_charFun_eq_one (ν := ν) (hφ := hφ)
    simpa [hspan] using
      (show (Pi.single i (1 : ℤ) : LatticePoint 2) ∈ (⊤ : Submodule ℤ (LatticePoint 2)) from
        Submodule.mem_top)
  have hi_period : EuclideanSpace.single i (1 : ℝ) ∈ charFunPeriodSet t := by
    simpa [latticeEmbedding_single_eq_single i] using hi_mem
  obtain ⟨m, hm⟩ := mem_charFunPeriodSet_iff_exists_int.mp hi_period
  have hcoord : t i = (2 * Real.pi : ℝ) * m := by
    calc
      t i = inner ℝ (EuclideanSpace.single i (1 : ℝ)) t := by
        simpa using (EuclideanSpace.inner_single_left (i := i) (1 : ℝ) t).symm
      _ = (2 * Real.pi : ℝ) * m := hm
  have hcoord_abs : |((2 * Real.pi : ℝ) * (m : ℝ))| < Real.pi := by
    simpa [hcoord] using ht i
  have hm_zero : m = 0 := by
    by_contra hm_ne
    have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hm_ne
    have hlarge : Real.pi < |((2 * Real.pi : ℝ) * (m : ℝ))| := by
      rw [abs_mul, abs_of_pos]
      · nlinarith [Real.pi_pos, hmabs]
      · positivity
    exact (not_lt_of_ge (le_of_lt hlarge)) hcoord_abs
  -- Proof comment: the coordinate lies in `(-π, π)` and is also an integral multiple of `2π`,
  -- so only the zero multiple is possible.
  simp [hcoord, hm_zero]

/-- Helper for Exercise 17.5.3: once the unique singularity is isolated at the origin, the
Abelized Chung--Fuchs denominator stays nonzero on every punctured open `π`-cube shell. -/
private lemma one_sub_mul_planarCharFun_ne_zero_of_shell
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤)
    {δ r : ℝ} (hδ : 0 < δ) (hr : r ∈ Set.Icc (1 / 2 : ℝ) 1)
    {t : EuclideanSpace ℝ (Fin 2)}
    (ht : ∀ i : Fin 2, |t i| < Real.pi)
    (hδt : δ ≤ ‖t‖) :
    (1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t ≠ 0 := by
  letI : IsProbabilityMeasure (ν.toMeasure.map latticeEmbedding) := by
    simpa using
      Measure.isProbabilityMeasure_map
        (μ := ν.toMeasure)
        (f := latticeEmbedding)
        (Measurable.of_discrete.aemeasurable : AEMeasurable latticeEmbedding ν.toMeasure)
  -- Proof comment: if the denominator vanished, norm bounds would force `r = 1` and then
  -- `charFun = 1`, contradicting that the shell stays away from the unique singular point `0`.
  intro hzero
  have hφ_norm_le :
      ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one (μ := ν.toMeasure.map latticeEmbedding) t
  have hr_norm_le : ‖(r : ℂ)‖ ≤ 1 := by
    have hr_le_one : r ≤ 1 := hr.2
    have hr_nonneg : 0 ≤ r := le_trans (by norm_num) hr.1
    simpa [Complex.norm_real, Real.norm_of_nonneg hr_nonneg] using hr_le_one
  have hnorm_mul_eq_one : ‖(r : ℂ)‖ * ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ = 1 := by
    have hz : (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    calc
      ‖(r : ℂ)‖ * ‖charFun (ν.toMeasure.map latticeEmbedding) t‖
          = ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
              symm
              exact norm_mul _ _
      _ = ‖(1 : ℂ)‖ := by rw [hz]
      _ = 1 := by simp
  have hr_norm_ge_one : 1 ≤ ‖(r : ℂ)‖ := by
    have hmul_le_self :
        ‖(r : ℂ)‖ * ‖charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ ‖(r : ℂ)‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _) hφ_norm_le
    linarith
  have hr_norm_eq_one : ‖(r : ℂ)‖ = 1 :=
    le_antisymm hr_norm_le hr_norm_ge_one
  have hr_eq_one : r = 1 := by
    have hr_nonneg : 0 ≤ r := le_trans (by norm_num) hr.1
    simpa [Complex.norm_real, Real.norm_of_nonneg hr_nonneg] using hr_norm_eq_one
  have hφ_eq_one :
      charFun (ν.toMeasure.map latticeEmbedding) t = 1 := by
    have hz : (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    simpa [hr_eq_one] using hz
  have ht_zero :
      t = 0 :=
    planarCharFun_eq_one_only_at_zero_of_supportSpan_eq_top (ν := ν) hspan ht hφ_eq_one
  have : δ ≤ 0 := by
    simpa [ht_zero] using hδt
  linarith

/-- Helper for Exercise 17.5.3: full support span on `ℤ²` implies that the embedded support atoms
already span the whole Euclidean frequency space. -/
private lemma supportImageSpan_eq_top_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤) :
    Submodule.span ℝ (latticeEmbedding '' ν.support) = ⊤ := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := latticeEmbedding '' ν.support
  have hmem :
      ∀ {x : LatticePoint 2}, x ∈ supportSpan ν → latticeEmbedding x ∈ Submodule.span ℝ S := by
    intro x hx
    -- Proof comment: every support atom maps into the real span by definition, and the span is
    -- closed under `0`, addition, and integer scalar multiplication after casting to `ℝ`.
    induction hx using Submodule.span_induction with
    | mem y hy =>
        exact Submodule.subset_span ⟨y, (PMF.mem_support_iff ν y).2 hy, rfl⟩
    | zero =>
        simpa [S, latticeEmbedding_zero] using
          (Submodule.zero_mem (Submodule.span ℝ S))
    | add y z _ _ hy hz =>
        simpa [S, latticeEmbedding_add] using
          (Submodule.add_mem (Submodule.span ℝ S) hy hz)
    | smul n y _ hy =>
        -- Proof comment: the `ℤ`-span induction step is multiplication on `LatticePoint 2`;
        -- rewrite it back to `zsmul` before using the embedding's scalar-compatibility lemma.
        change latticeEmbedding (n • y) ∈ Submodule.span ℝ S
        rw [latticeEmbedding_zsmul]
        exact Submodule.smul_mem (Submodule.span ℝ S) (n : ℝ) hy
  have hbasis :
      ∀ i : Fin 2,
        EuclideanSpace.basisFun (Fin 2) ℝ i ∈ Submodule.span ℝ S := by
    intro i
    have hsingle :
        (Pi.single i (1 : ℤ) : LatticePoint 2) ∈ supportSpan ν := by
      simpa [hspan] using
        (show (Pi.single i (1 : ℤ) : LatticePoint 2) ∈ (⊤ : Submodule ℤ (LatticePoint 2)) from
          Submodule.mem_top)
    -- Proof comment: full support span puts each lattice basis vector in the support span, so
    -- their Euclidean images lie in the real span of the embedded support atoms.
    simpa [S, EuclideanSpace.basisFun_apply, latticeEmbedding_single_eq_single i] using
      hmem hsingle
  have htop_le : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) ≤ Submodule.span ℝ S := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.span_eq]
    exact Submodule.span_le.mpr <| by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hbasis i
  exact top_unique htop_le

/-- Helper for Exercise 17.5.3: from full support span we can extract finitely many embedded
support atoms that still span `ℝ²`. -/
private lemma existsFiniteSupportImageSpanningSet_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (↑s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ latticeEmbedding '' ν.support ∧
      Submodule.span ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := latticeEmbedding '' ν.support
  have hS_top : Submodule.span ℝ S = ⊤ :=
    supportImageSpan_eq_top_of_supportSpan_eq_top (ν := ν) hspan
  have hbasis_mem :
      ∀ i : Fin 2,
        EuclideanSpace.basisFun (Fin 2) ℝ i ∈ Submodule.span ℝ S := by
    intro i
    rw [hS_top]
    exact Submodule.mem_top
  choose T hTsub hTmem using
    fun i : Fin 2 ↦
      Submodule.mem_span_finite_of_mem_span (hbasis_mem i)
  let s : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.biUnion T
  have hs_subset : (↑s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ S := by
    intro x hx
    simp only [s, Finset.mem_coe, Finset.mem_biUnion] at hx
    rcases hx with ⟨i, -, hxi⟩
    exact hTsub i (by simpa using hxi)
  have hbasis_span :
      ∀ i : Fin 2,
        EuclideanSpace.basisFun (Fin 2) ℝ i ∈ Submodule.span ℝ (s : Set _) := by
    intro i
    exact
      (Submodule.span_mono (by
        intro x hx
        simp only [s, Finset.mem_coe, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i, hx⟩)) (hTmem i)
  have htop_le : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) ≤
      Submodule.span ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.span_eq]
    exact Submodule.span_le.mpr <| by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hbasis_span i
  refine ⟨s, ?_, top_unique htop_le⟩
  simpa [S] using hs_subset

/-- Helper for Exercise 17.5.3: if the embedded support spans `ℝ²`, two actual support atoms
already suffice to span `ℝ²`. -/
private lemma existsSupportPair_spanTop_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤) :
    ∃ x y : LatticePoint 2,
      x ∈ ν.support ∧
      y ∈ ν.support ∧
      Submodule.span ℝ ({latticeEmbedding x, latticeEmbedding y} :
        Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
  classical
  have himage_top :
      Submodule.span ℝ (latticeEmbedding '' ν.support) = ⊤ :=
    supportImageSpan_eq_top_of_supportSpan_eq_top (ν := ν) hspan
  -- Route correction: instead of extracting a finite basis, pick one nonzero support atom and a
  -- second support atom outside its line; in dimension `2`, that pair already spans `ℝ²`.
  have hnonzero :
      ∃ x ∈ ν.support,
        latticeEmbedding x ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
    by_contra h
    push_neg at h
    have hspan_bot :
        Submodule.span ℝ (latticeEmbedding '' ν.support) = ⊥ := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        simpa [h x hx]
      · exact bot_le
    have htop_bot : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) = ⊥ := by
      simpa [himage_top] using hspan_bot
    exact top_ne_bot htop_bot
  obtain ⟨x, hx, hx0⟩ := hnonzero
  have hsecond_atom :
      ∃ y ∈ ν.support,
        latticeEmbedding y ∉ Submodule.span ℝ ({latticeEmbedding x} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
    by_contra h
    push_neg at h
    have hline :
        Submodule.span ℝ (latticeEmbedding '' ν.support) ≤
          Submodule.span ℝ ({latticeEmbedding x} : Set (EuclideanSpace ℝ (Fin 2))) := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact h y hy
    have hsingleton_top :
        Submodule.span ℝ ({latticeEmbedding x} :
          Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      exact top_unique (by simpa [himage_top] using hline)
    have hsingleton_finrank :
        Module.finrank ℝ
          (Submodule.span ℝ ({latticeEmbedding x} :
            Set (EuclideanSpace ℝ (Fin 2)))) = 1 := by
      simpa using finrank_span_singleton hx0
    have hambient_finrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
      simpa using (Module.finrank_fin_fun (R := ℝ) (n := 2))
    have : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank ℝ
              (Submodule.span ℝ ({latticeEmbedding x} :
                Set (EuclideanSpace ℝ (Fin 2)))) := hsingleton_finrank.symm
        _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
              rw [hsingleton_top, finrank_top]
        _ = 2 := hambient_finrank
    omega
  obtain ⟨y, hy, hy_line⟩ := hsecond_atom
  have hlin :
      LinearIndependent ℝ ![latticeEmbedding x, latticeEmbedding y] :=
    (LinearIndependent.pair_iff' hx0).2 <| by
      intro a hxy
      exact hy_line (Submodule.mem_span_singleton.mpr ⟨a, hxy⟩)
  have hpair_top :
      Submodule.span ℝ (Set.range ![latticeEmbedding x, latticeEmbedding y]) = ⊤ := by
    exact
      LinearIndependent.span_eq_top_of_card_eq_finrank' hlin (by simp)
  have hpair_range :
      Set.range ![latticeEmbedding x, latticeEmbedding y] =
        ({latticeEmbedding x, latticeEmbedding y} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hpair_top' :
      Submodule.span ℝ ({latticeEmbedding x, latticeEmbedding y} :
        Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
    simpa [hpair_range] using hpair_top
  exact ⟨x, y, hx, hy, hpair_top'⟩

/-- Helper for Exercise 17.5.3: a finite spanning family with positive weights gives a quadratic
coercivity bound for the corresponding weighted inner products. -/
private lemma weightedInnerSqCoercive_of_spanTop
    {D : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin D)) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ c > 0, ∀ t : EuclideanSpace ℝ (Fin D),
      c * ‖t‖ ^ (2 : ℕ) ≤ ∑ i, w i * (inner ℝ (v i) t) ^ (2 : ℕ) := by
  classical
  let B : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] (ι → ℝ) :=
    LinearMap.pi fun i ↦
      { toFun := fun t ↦ Real.sqrt (w i) * inner ℝ (v i) t
        map_add' := by
          intro x y
          simp [inner_add_right, mul_add, add_mul]
        map_smul' := by
          intro a t
          simp [inner_smul_right, mul_assoc, mul_left_comm, mul_comm] }
  let A : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp B
  have hA_ker : LinearMap.ker A = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro t ht
    have hBt : B t = 0 := by
      simpa [A] using congrArg (WithLp.linearEquiv 2 ℝ (ι → ℝ)) ht
    have hcoord_zero : ∀ i, inner ℝ (v i) t = 0 := by
      intro i
      have hAi : B t i = 0 := by
        simpa using congrFun hBt i
      have hsqrt_ne : Real.sqrt (w i) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 (hw i))
      have : Real.sqrt (w i) * inner ℝ (v i) t = 0 := by
        simpa [B] using hAi
      exact (mul_eq_zero.mp this).resolve_left hsqrt_ne
    have horth : ∀ x ∈ Submodule.span ℝ (Set.range v), inner ℝ x t = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨i, rfl⟩
          exact hcoord_zero i
      | zero =>
          simp
      | add x y _ _ hx hy =>
          simp [inner_add_left, hx, hy]
      | smul a x _ hx =>
          simp [inner_smul_left, hx]
    have ht_mem : t ∈ Submodule.span ℝ (Set.range v) := by
      rw [hspan]
      exact Submodule.mem_top
    have hself : inner ℝ t t = 0 := horth t ht_mem
    have hnorm_sq : ‖t‖ ^ (2 : ℕ) = 0 := by
      simpa using hself
    have hnorm : ‖t‖ = 0 := by
      nlinarith [hnorm_sq]
    exact norm_eq_zero.mp hnorm
  obtain ⟨K, hK_pos, hK⟩ := A.exists_antilipschitzWith hA_ker
  refine ⟨((((K : ℝ) ^ (2 : ℕ)) + 1)⁻¹), by positivity, ?_⟩
  intro t
  have hbound : ‖t‖ ≤ (K : ℝ) * ‖A t‖ := by
    exact ZeroHomClass.bound_of_antilipschitz A hK t
  have hsq :
      ‖t‖ ^ (2 : ℕ) ≤ (((K : ℝ) ^ (2 : ℕ)) + 1) * ‖A t‖ ^ (2 : ℕ) := by
    have hK_real_nonneg : 0 ≤ (K : ℝ) := by
      exact_mod_cast (le_of_lt hK_pos)
    have hsq0 : ‖t‖ ^ (2 : ℕ) ≤ (K : ℝ) ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
      have ht_nonneg : 0 ≤ ‖t‖ := norm_nonneg t
      have hA_nonneg : 0 ≤ ‖A t‖ := norm_nonneg (A t)
      nlinarith [hbound, hK_real_nonneg, ht_nonneg, hA_nonneg]
    nlinarith [hsq0, sq_nonneg ‖A t‖]
  have hbound_sq :
      ((((K : ℝ) ^ (2 : ℕ)) + 1)⁻¹) * ‖t‖ ^ (2 : ℕ) ≤ ‖A t‖ ^ (2 : ℕ) := by
    have hfac_nonneg : 0 ≤ ((((K : ℝ) ^ (2 : ℕ)) + 1)⁻¹ : ℝ) := by
      positivity
    have hfac_ne : (((K : ℝ) ^ (2 : ℕ)) + 1 : ℝ) ≠ 0 := by
      positivity
    calc
      ((((K : ℝ) ^ (2 : ℕ)) + 1)⁻¹) * ‖t‖ ^ (2 : ℕ)
          ≤ ((((K : ℝ) ^ (2 : ℕ)) + 1)⁻¹) *
              ((((K : ℝ) ^ (2 : ℕ)) + 1) * ‖A t‖ ^ (2 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left hsq hfac_nonneg
      _ = ‖A t‖ ^ (2 : ℕ) := by
            field_simp [hfac_ne]
  have hA_norm_sq :
      ‖A t‖ ^ (2 : ℕ) = ∑ i, w i * (inner ℝ (v i) t) ^ (2 : ℕ) := by
    calc
      ‖A t‖ ^ (2 : ℕ) = ∑ i, ‖A t i‖ ^ (2 : ℕ) := by
        simpa using (EuclideanSpace.norm_sq_eq (A t))
      _ = ∑ i, w i * (inner ℝ (v i) t) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hwi : 0 ≤ w i := le_of_lt (hw i)
        have hAi : A t i = Real.sqrt (w i) * inner ℝ (v i) t := by
          simpa [A, B] using show B t i = Real.sqrt (w i) * inner ℝ (v i) t by simp [B]
        rw [hAi, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hwi]
  simpa [hA_norm_sq] using hbound_sq

/-- Helper for Exercise 17.5.3: the planar characteristic function is represented by the
PMF-weighted exponential series over the step law. -/
private lemma planarCharFunExpSeriesSummable
    (ν : PMF (LatticePoint 2)) (t : EuclideanSpace ℝ (Fin 2)) :
    Summable (fun z : LatticePoint 2 ↦
      (ν z).toReal •
        Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)) := by
  have hmass : Summable (fun z : LatticePoint 2 ↦ (ν z).toReal) := by
    simpa using ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)
  -- Proof comment: each exponential phase has norm `1`, so the complex series is dominated by
  -- the summable PMF mass series.
  refine Summable.of_norm_bounded hmass ?_
  intro z
  exact le_of_eq <| by
    calc
      ‖(ν z).toReal • Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)‖
          = ‖(((ν z).toReal : ℂ) *
              Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I))‖ := by
                simp [smul_eq_mul]
      _ = ‖((ν z).toReal : ℂ)‖ *
            ‖Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)‖ := by
              rw [norm_mul]
      _ = (ν z).toReal := by
            simp [Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
              abs_of_nonneg ENNReal.toReal_nonneg]

/-- Helper for Exercise 17.5.3: the planar characteristic function equals the PMF-weighted
Fourier series of the step phases. -/
private lemma planarCharFun_eq_tsum_exp
    (ν : PMF (LatticePoint 2)) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun (ν.toMeasure.map latticeEmbedding) t =
      ∑' z : LatticePoint 2,
        (ν z).toReal •
          Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I) := by
  have hs_exp := planarCharFunExpSeriesSummable ν t
  have hInt :
      Integrable
        (fun z : LatticePoint 2 ↦
          Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I))
        ν.toMeasure := by
    rw [integrable_iff_summable_norm_smul_pmf]
    exact hs_exp.norm
  have hphase_meas :
      Measurable (fun y : EuclideanSpace ℝ (Fin 2) ↦
        Complex.exp ((((inner ℝ y t : ℝ)) : ℂ) * Complex.I)) := by
    fun_prop
  -- Proof comment: transport the characteristic-function integral back along
  -- `latticeEmbedding`, then collapse the discrete PMF integral to its weighted series.
  rw [MeasureTheory.charFun_apply]
  rw [show
      ∫ y, Complex.exp ((((inner ℝ y t : ℝ)) : ℂ) * Complex.I) ∂(ν.toMeasure.map latticeEmbedding) =
        ∫ z : LatticePoint 2,
          Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I) ∂ν.toMeasure by
        simpa using
          (integral_map
            (μ := ν.toMeasure)
            (φ := latticeEmbedding)
            (f := fun y : EuclideanSpace ℝ (Fin 2) ↦
              Complex.exp ((((inner ℝ y t : ℝ)) : ℂ) * Complex.I))
            (Measurable.of_discrete.aemeasurable)
            hphase_meas.aestronglyMeasurable)]
  simpa using
    (PMF.integral_eq_tsum ν
      (fun z : LatticePoint 2 ↦
        Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I))
      hInt)

/-- Helper for Exercise 17.5.3: the planar lattice inner product is the coordinate sum against the
frequency vector. -/
private lemma planarInner_eq_sum_coords
    (z : LatticePoint 2) (t : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (latticeEmbedding z) t = ∑ i : Fin 2, (z i : ℝ) * t i := by
  -- Proof comment: on Euclidean space, the inner product is the finite coordinate sum.
  rw [PiLp.inner_apply (𝕜 := ℝ) (f := fun _ : Fin 2 ↦ ℝ) (x := latticeEmbedding z) (y := t)]
  rw [Fin.sum_univ_two]
  rw [show inner ℝ ((latticeEmbedding z).ofLp 0) (t.ofLp 0) =
        t.ofLp 0 * (latticeEmbedding z).ofLp 0 by rfl]
  rw [show inner ℝ ((latticeEmbedding z).ofLp 1) (t.ofLp 1) =
        t.ofLp 1 * (latticeEmbedding z).ofLp 1 by rfl]
  simp [latticeEmbedding, mul_comm]

/-- Helper for Exercise 17.5.3: the zero-drift hypothesis kills the weighted planar inner product
against any fixed frequency vector. -/
private lemma planarInnerIntegral_eq_zero_of_meanZero
    (ν : PMF (LatticePoint 2))
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤)
    (t : EuclideanSpace ℝ (Fin 2)) :
    ∫ z, inner ℝ (latticeEmbedding z) t ∂ν.toMeasure = 0 := by
  have hcoordInt :
      ∀ i : Fin 2, Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) ν.toMeasure := by
    intro i
    exact planarCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := i) hsecond
  have hcoordZero :
      ∀ i : Fin 2, ∫ z, (z i : ℝ) ∂ν.toMeasure = 0 := by
    intro i
    calc
      ∫ z, (z i : ℝ) ∂ν.toMeasure
          = ∑' z : LatticePoint 2, (ν z).toReal • (z i : ℝ) := by
              exact PMF.integral_eq_tsum ν (fun z : LatticePoint 2 ↦ (z i : ℝ)) (hcoordInt i)
      _ = 0 := by
            simpa [smul_eq_mul, mul_comm] using hmean i
  -- Proof comment: rewrite the inner product as the sum of the two coordinate projections, then
  -- pull the integral through that finite sum and insert the zero-drift identities.
  calc
    ∫ z, inner ℝ (latticeEmbedding z) t ∂ν.toMeasure
      = ∫ z, ∑ i : Fin 2, (z i : ℝ) * t i ∂ν.toMeasure := by
          congr with z
          exact planarInner_eq_sum_coords z t
    _ = ∑ i : Fin 2, ∫ z, (z i : ℝ) * t i ∂ν.toMeasure := by
          rw [MeasureTheory.integral_finset_sum]
          intro i hi
          exact (hcoordInt i).mul_const (t i)
    _ = ∑ i : Fin 2, t i * ∫ z, (z i : ℝ) ∂ν.toMeasure := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa [mul_comm] using
            (integral_mul_const (t i) fun z : LatticePoint 2 ↦ (z i : ℝ))
    _ = 0 := by
          simp [hcoordZero]

/-- Helper for Exercise 17.5.3: the planar quadratic-moment hypothesis makes every fixed
frequency inner product integrable under the step law. -/
private lemma planarInnerIntegrable_of_planarSecondMoment
    (ν : PMF (LatticePoint 2))
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤)
    (t : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun z : LatticePoint 2 ↦ inner ℝ (latticeEmbedding z) t) ν.toMeasure := by
  have hcoord0 :
      Integrable (fun z : LatticePoint 2 ↦ (z 0 : ℝ)) ν.toMeasure :=
    planarCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := 0) hsecond
  have hcoord1 :
      Integrable (fun z : LatticePoint 2 ↦ (z 1 : ℝ)) ν.toMeasure :=
    planarCoordinate_integrable_of_planarSecondMoment (ν := ν) (i := 1) hsecond
  -- Proof comment: in dimension `2`, the inner product is the sum of the two coordinate
  -- projections scaled by the fixed frequency coordinates.
  simpa [planarInner_eq_sum_coords, Fin.sum_univ_two] using
    (hcoord0.mul_const (t 0)).add (hcoord1.mul_const (t 1))

/-- Helper for Exercise 17.5.3: the centered oscillatory remainder on the imaginary axis is
globally dominated by a quadratic polynomial. -/
private lemma expMulIRemainder_norm_le_quadratic (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖ ≤ 3 * u ^ (2 : ℕ) := by
  by_cases hu : |u| ≤ 1
  · have hz : ‖((u : ℂ) * Complex.I)‖ ≤ 1 := by
      simpa [Complex.norm_mul, RCLike.norm_ofReal] using hu
    have hquad :
        ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖ ≤
          ‖((u : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
      -- Proof comment: inside the unit ball, the standard complex Taylor remainder estimate
      -- gives a direct quadratic bound in the norm of the imaginary argument.
      simpa using (Complex.norm_exp_sub_one_sub_id_le hz)
    calc
      ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖
          ≤ ‖((u : ℂ) * Complex.I)‖ ^ (2 : ℕ) := hquad
      _ = |u| ^ (2 : ℕ) := by
            simp [Complex.norm_mul, RCLike.norm_ofReal]
      _ = u ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ 3 * u ^ (2 : ℕ) := by
            nlinarith [sq_nonneg u]
  · have hlarge : 1 < |u| := lt_of_not_ge hu
    have hbound :
        ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖ ≤ 2 + |u| := by
      -- Proof comment: away from the unit ball, a coarse triangle-inequality bound is already
      -- enough because `2 + |u|` is dominated by a multiple of `u²`.
      calc
        ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖
            ≤ ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ + ‖((u : ℂ) * Complex.I)‖ := by
              simpa using norm_sub_le (Complex.exp ((u : ℂ) * Complex.I) - 1) ((u : ℂ) * Complex.I)
        _ ≤ 2 + |u| := by
            gcongr
            · calc
                ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖
                    ≤ ‖Complex.exp ((u : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                _ = 2 := by
                      rw [Complex.norm_exp_ofReal_mul_I]
                      norm_num
            · simp [Complex.norm_mul, RCLike.norm_ofReal]
    calc
      ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - ((u : ℂ) * Complex.I)‖ ≤ 2 + |u| := hbound
      _ ≤ 3 * |u| ^ (2 : ℕ) := by
            nlinarith [le_of_lt hlarge, sq_nonneg |u|]
      _ = 3 * u ^ (2 : ℕ) := by rw [sq_abs]

/-- Helper for Exercise 17.5.3: the real-part defect of the planar characteristic function is the
PMF-weighted cosine defect series. -/
private lemma planarCharFun_reDefect_eq_tsum_one_sub_cos
    (ν : PMF (LatticePoint 2)) (t : EuclideanSpace ℝ (Fin 2)) :
    1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re =
      ∑' z : LatticePoint 2,
        (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t)) := by
  have hs_exp := planarCharFunExpSeriesSummable ν t
  have hmassSummable : Summable (fun z : LatticePoint 2 ↦ (ν z).toReal) := by
    simpa using ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)
  have hmass :
      ∑' z : LatticePoint 2, (ν z).toReal = 1 := by
    have hmass_ofReal : ENNReal.ofReal (∑' z : LatticePoint 2, (ν z).toReal) = 1 := by
      calc
        ENNReal.ofReal (∑' z : LatticePoint 2, (ν z).toReal)
            = ∑' z : LatticePoint 2, ENNReal.ofReal ((ν z).toReal) := by
                rw [ENNReal.ofReal_tsum_of_nonneg]
                · intro z
                  exact ENNReal.toReal_nonneg
                · exact ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)
        _ = ∑' z : LatticePoint 2, ν z := by
              refine tsum_congr fun z ↦ ?_
              exact ENNReal.ofReal_toReal (PMF.apply_lt_top ν z).ne
        _ = 1 := PMF.tsum_coe ν
    have hsum_nonneg : 0 ≤ ∑' z : LatticePoint 2, (ν z).toReal := by
      exact tsum_nonneg fun z ↦ ENNReal.toReal_nonneg
    exact
      (ENNReal.ofReal_eq_ofReal_iff hsum_nonneg zero_le_one).mp (by
        simpa using hmass_ofReal)
  have hterm_re :
      ∀ z : LatticePoint 2,
        (((ν z).toReal •
            Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re) =
          (ν z).toReal * Real.cos (inner ℝ (latticeEmbedding z) t) := by
    intro z
    change ((((ν z).toReal : ℂ) *
        Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re) =
      (ν z).toReal * Real.cos (inner ℝ (latticeEmbedding z) t)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hs_re :
      Summable
        (fun z : LatticePoint 2 ↦
          (((ν z).toReal •
              Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re)) := by
    simpa using (Complex.hasSum_re hs_exp.hasSum).summable
  -- Proof comment: take real parts termwise in the exponential series and replace each real part
  -- by the corresponding cosine phase.
  calc
    1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re
      = 1 -
          (∑' z : LatticePoint 2,
            (ν z).toReal •
              Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re := by
            rw [planarCharFun_eq_tsum_exp]
    _ = 1 -
          ∑' z : LatticePoint 2,
            (((ν z).toReal •
                Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re) := by
          rw [Complex.re_tsum hs_exp]
    _ = (∑' z : LatticePoint 2, (ν z).toReal) -
          ∑' z : LatticePoint 2,
            (((ν z).toReal •
                Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re) := by
          rw [hmass]
    _ =
        ∑' z : LatticePoint 2,
          ((ν z).toReal -
            (((ν z).toReal •
                Complex.exp ((((inner ℝ (latticeEmbedding z) t : ℝ)) : ℂ) * Complex.I)).re)) := by
          rw [hmassSummable.tsum_sub hs_re]
    _ =
        ∑' z : LatticePoint 2,
          (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t)) := by
          refine tsum_congr fun z ↦ ?_
          rw [hterm_re z]
          ring

/-- Helper for Exercise 17.5.3: finite quadratic moment gives a global quadratic upper bound on
the real-part defect of the planar characteristic function. -/
private lemma planarCharFunReDefect_le_quadratic
    (ν : PMF (LatticePoint 2))
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    ∃ C > 0, ∀ t : EuclideanSpace ℝ (Fin 2),
      1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re ≤ C * ‖t‖ ^ (2 : ℕ) := by
  let moment : ℝ := ∑' x : LatticePoint 2, ‖latticeEmbedding x‖ ^ (2 : ℕ) * (ν x).toReal
  let C : ℝ := (1 / 2 : ℝ) * moment + 1
  have hmomentSummable :
      Summable (fun x : LatticePoint 2 ↦ ‖latticeEmbedding x‖ ^ (2 : ℕ) * (ν x).toReal) :=
    planarSecondMomentSummable ν hsecond
  have hmoment_nonneg : 0 ≤ moment := by
    dsimp [moment]
    exact tsum_nonneg fun x ↦ mul_nonneg (sq_nonneg ‖latticeEmbedding x‖) ENNReal.toReal_nonneg
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC_pos, ?_⟩
  intro t
  let upper : LatticePoint 2 → ℝ :=
    fun z ↦ ((1 / 2 : ℝ) * (‖latticeEmbedding z‖ ^ (2 : ℕ) * (ν z).toReal)) * ‖t‖ ^ (2 : ℕ)
  have hupperSummable : Summable upper := by
    dsimp [upper]
    exact (hmomentSummable.mul_left (1 / 2 : ℝ)).mul_right (‖t‖ ^ (2 : ℕ))
  have hterm_nonneg :
      ∀ z : LatticePoint 2,
        0 ≤ (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t)) := by
    intro z
    exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
  have hterm_le :
      ∀ z : LatticePoint 2,
        (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t)) ≤ upper z := by
    intro z
    let u : ℝ := inner ℝ (latticeEmbedding z) t
    have hcos_quad : 1 - Real.cos u ≤ u ^ (2 : ℕ) / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := u)]
    have habs_u : |u| ≤ ‖latticeEmbedding z‖ * ‖t‖ := by
      simpa [u, Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (latticeEmbedding z) t)
    have hu_sq :
        u ^ (2 : ℕ) ≤ ‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ) := by
      have hsq :
          u ^ (2 : ℕ) ≤ (‖latticeEmbedding z‖ * ‖t‖) ^ (2 : ℕ) := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using habs_u)
      calc
        u ^ (2 : ℕ) ≤ (‖latticeEmbedding z‖ * ‖t‖) ^ (2 : ℕ) := hsq
        _ = ‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ) := by ring
    have hp_nonneg : 0 ≤ (ν z).toReal := ENNReal.toReal_nonneg
    have hu_div :
        u ^ (2 : ℕ) / 2 ≤ (‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ)) / 2 := by
      exact div_le_div_of_nonneg_right hu_sq (by positivity : (0 : ℝ) ≤ 2)
    -- Proof comment: `1 - cos u` is bounded by `u² / 2`, and Cauchy--Schwarz converts `u²` into
    -- the second-moment weight times `‖t‖²`.
    calc
      (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t))
        = (ν z).toReal * (1 - Real.cos u) := by rfl
      _ ≤ (ν z).toReal * (u ^ (2 : ℕ) / 2) := by
            exact mul_le_mul_of_nonneg_left hcos_quad hp_nonneg
      _ ≤ (ν z).toReal * ((‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ)) / 2) := by
            exact mul_le_mul_of_nonneg_left hu_div hp_nonneg
      _ = upper z := by
            dsimp [upper]
            ring
  have htermSummable :
      Summable
        (fun z : LatticePoint 2 ↦
          (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t))) :=
    Summable.of_nonneg_of_le hterm_nonneg hterm_le hupperSummable
  have hbase :
      1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re ≤
        ((1 / 2 : ℝ) * moment) * ‖t‖ ^ (2 : ℕ) := by
    rw [planarCharFun_reDefect_eq_tsum_one_sub_cos]
    calc
      ∑' z : LatticePoint 2, (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t))
        ≤ ∑' z : LatticePoint 2, upper z :=
            Summable.tsum_le_tsum hterm_le htermSummable hupperSummable
      _ = ((1 / 2 : ℝ) * moment) * ‖t‖ ^ (2 : ℕ) := by
            dsimp [upper, moment]
            rw [tsum_mul_right, tsum_mul_left]
  have ht_nonneg : 0 ≤ ‖t‖ ^ (2 : ℕ) := by positivity
  -- Proof comment: enlarge the coefficient by `1` so the existential witness stays strictly
  -- positive even for the degenerate zero-step law.
  calc
    1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re
      ≤ ((1 / 2 : ℝ) * moment) * ‖t‖ ^ (2 : ℕ) := hbase
    _ ≤ C * ‖t‖ ^ (2 : ℕ) := by
          dsimp [C]
          nlinarith

/-- Helper for Exercise 17.5.3: after removing the linear term using the zero-drift condition,
the full complex characteristic-function defect is quadratically small. -/
private lemma planarCharFunComplexDefect_le_quadratic_of_meanZero
    (ν : PMF (LatticePoint 2))
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    ∃ C > 0, ∀ t : EuclideanSpace ℝ (Fin 2),
      ‖1 - charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ C * ‖t‖ ^ (2 : ℕ) := by
  let moment : ℝ := ∑' z : LatticePoint 2, ‖latticeEmbedding z‖ ^ (2 : ℕ) * (ν z).toReal
  let C : ℝ := 3 * moment + 1
  have hmomentSummable :
      Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ (2 : ℕ) * (ν z).toReal) :=
    planarSecondMomentSummable ν hsecond
  have hmoment_nonneg : 0 ≤ moment := by
    dsimp [moment]
    exact tsum_nonneg fun z ↦ mul_nonneg (sq_nonneg ‖latticeEmbedding z‖) ENNReal.toReal_nonneg
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC_pos, ?_⟩
  intro t
  let phase : LatticePoint 2 → ℂ := fun z ↦
    (((inner ℝ (latticeEmbedding z) t : ℝ) : ℂ) * Complex.I)
  let oneTerm : LatticePoint 2 → ℂ := fun z ↦ (ν z).toReal • (1 : ℂ)
  let linearTerm : LatticePoint 2 → ℂ := fun z ↦ (ν z).toReal • phase z
  let remainderTerm : LatticePoint 2 → ℂ := fun z ↦
    (ν z).toReal • (Complex.exp (phase z) - 1 - phase z)
  let upper : LatticePoint 2 → ℝ := fun z ↦
    (3 * (‖latticeEmbedding z‖ ^ (2 : ℕ) * (ν z).toReal)) * ‖t‖ ^ (2 : ℕ)
  have hmassSummable : Summable (fun z : LatticePoint 2 ↦ (ν z).toReal) := by
    simpa using ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)
  have honeSummable : Summable oneTerm := by
    -- Proof comment: the constant complex series is controlled by the PMF mass series.
    refine Summable.of_norm_bounded hmassSummable ?_
    intro z
    simp [oneTerm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hinnerIntegrable :
      Integrable (fun z : LatticePoint 2 ↦ inner ℝ (latticeEmbedding z) t) ν.toMeasure :=
    planarInnerIntegrable_of_planarSecondMoment ν hsecond t
  have hphaseIntegrable : Integrable phase ν.toMeasure := by
    -- Proof comment: the complex linear phase is just the real inner product embedded in `ℂ`
    -- and multiplied by the constant `I`.
    simpa [phase] using hinnerIntegrable.ofReal.mul_const Complex.I
  have hlinearNormSummable :
      Summable (fun z : LatticePoint 2 ↦ ‖linearTerm z‖) := by
    simpa [linearTerm, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg] using
      (integrable_iff_summable_norm_smul_pmf ν phase).mp hphaseIntegrable
  have hlinearSummable : Summable linearTerm := hlinearNormSummable.of_norm
  have hone :
      ∑' z : LatticePoint 2, oneTerm z = 1 := by
    -- Proof comment: summing the constant term recovers the total PMF mass.
    calc
      ∑' z : LatticePoint 2, oneTerm z = ∫ z, (1 : ℂ) ∂ν.toMeasure := by
        symm
        exact PMF.integral_eq_tsum ν (fun _ : LatticePoint 2 ↦ (1 : ℂ)) (by simp)
      _ = 1 := by simp
  have hlinear :
      ∑' z : LatticePoint 2, linearTerm z = 0 := by
    -- Proof comment: the zero-drift hypothesis kills the linear phase term after rewriting it
    -- as the integral of the planar inner product.
    calc
      ∑' z : LatticePoint 2, linearTerm z = ∫ z, phase z ∂ν.toMeasure := by
        symm
        exact PMF.integral_eq_tsum ν phase hphaseIntegrable
      _ = (∫ z, (((inner ℝ (latticeEmbedding z) t : ℝ) : ℂ)) ∂ν.toMeasure) * Complex.I := by
        simpa [phase] using
          (integral_mul_const Complex.I
            (fun z : LatticePoint 2 ↦ (((inner ℝ (latticeEmbedding z) t : ℝ) : ℂ))))
      _ = (((∫ z, inner ℝ (latticeEmbedding z) t ∂ν.toMeasure : ℝ)) : ℂ) * Complex.I := by
        rw [integral_complex_ofReal]
      _ = 0 := by
        rw [planarInnerIntegral_eq_zero_of_meanZero ν hmean hsecond t]
        simp
  have hupperSummable : Summable upper := by
    dsimp [upper]
    exact (hmomentSummable.mul_left 3).mul_right (‖t‖ ^ (2 : ℕ))
  have hremNormLe :
      ∀ z : LatticePoint 2, ‖remainderTerm z‖ ≤ upper z := by
    intro z
    let u : ℝ := inner ℝ (latticeEmbedding z) t
    have hu_norm :
        ‖phase z‖ = |u| := by
      simp [phase, u, Complex.norm_mul, RCLike.norm_ofReal]
    have hu_abs :
        |u| ≤ ‖latticeEmbedding z‖ * ‖t‖ := by
      simpa [u, Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (latticeEmbedding z) t)
    have hu_sq :
        u ^ (2 : ℕ) ≤ ‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ) := by
      have hsq :
          u ^ (2 : ℕ) ≤ (‖latticeEmbedding z‖ * ‖t‖) ^ (2 : ℕ) := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hu_abs)
      calc
        u ^ (2 : ℕ) ≤ (‖latticeEmbedding z‖ * ‖t‖) ^ (2 : ℕ) := hsq
        _ = ‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ) := by ring
    have hcoeff_nonneg : 0 ≤ (ν z).toReal := ENNReal.toReal_nonneg
    -- Proof comment: the centered exponential remainder is `O(u²)`, and Cauchy--Schwarz turns
    -- `u²` into the second-moment weight times `‖t‖²`.
    calc
      ‖remainderTerm z‖
        = (ν z).toReal * ‖Complex.exp (phase z) - 1 - phase z‖ := by
            simp [remainderTerm, Real.norm_of_nonneg hcoeff_nonneg, mul_comm, mul_left_comm,
              mul_assoc]
      _ ≤ (ν z).toReal * (3 * u ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [phase, u, hu_norm, sq_abs] using expMulIRemainder_norm_le_quadratic u)
              hcoeff_nonneg
      _ ≤ (ν z).toReal * (3 * (‖latticeEmbedding z‖ ^ (2 : ℕ) * ‖t‖ ^ (2 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hu_sq (by positivity : (0 : ℝ) ≤ 3))
              hcoeff_nonneg
      _ = upper z := by
            dsimp [upper]
            ring
  have hremNormSummable :
      Summable (fun z : LatticePoint 2 ↦ ‖remainderTerm z‖) :=
    Summable.of_nonneg_of_le (fun z ↦ norm_nonneg _) hremNormLe hupperSummable
  have hremSummable : Summable remainderTerm := hremNormSummable.of_norm
  have hchar :
      charFun (ν.toMeasure.map latticeEmbedding) t =
        1 + ∑' z : LatticePoint 2, remainderTerm z := by
    -- Proof comment: expand the characteristic function into constant, linear, and remainder
    -- pieces, then remove the linear term with the mean-zero identity.
    calc
      charFun (ν.toMeasure.map latticeEmbedding) t
        = ∑' z : LatticePoint 2,
            (oneTerm z + (linearTerm z + remainderTerm z)) := by
              rw [planarCharFun_eq_tsum_exp]
              refine tsum_congr fun z ↦ ?_
              simp [oneTerm, linearTerm, remainderTerm, phase, smul_eq_mul]
              ring
      _ = (∑' z : LatticePoint 2, oneTerm z) +
            ∑' z : LatticePoint 2, (linearTerm z + remainderTerm z) := by
              rw [honeSummable.tsum_add (hlinearSummable.add hremSummable)]
      _ = (∑' z : LatticePoint 2, oneTerm z) +
            ((∑' z : LatticePoint 2, linearTerm z) +
              ∑' z : LatticePoint 2, remainderTerm z) := by
              rw [hlinearSummable.tsum_add hremSummable]
      _ = 1 + ∑' z : LatticePoint 2, remainderTerm z := by
              rw [hone, hlinear]
              simp
  have hdefect :
      1 - charFun (ν.toMeasure.map latticeEmbedding) t =
        -(∑' z : LatticePoint 2, remainderTerm z) := by
    rw [hchar]
    ring
  have ht_nonneg : 0 ≤ ‖t‖ ^ (2 : ℕ) := by positivity
  -- Proof comment: the remainder series is absolutely summable and dominated by the quadratic
  -- moment series, so its norm is controlled by a uniform quadratic coefficient.
  calc
    ‖1 - charFun (ν.toMeasure.map latticeEmbedding) t‖
      = ‖-(∑' z : LatticePoint 2, remainderTerm z)‖ := by rw [hdefect]
    _ = ‖∑' z : LatticePoint 2, remainderTerm z‖ := by rw [norm_neg]
    _ ≤ ∑' z : LatticePoint 2, ‖remainderTerm z‖ := by
          exact norm_tsum_le_tsum_norm hremNormSummable
    _ ≤ ∑' z : LatticePoint 2, upper z := by
          exact hremNormSummable.tsum_le_tsum hremNormLe hupperSummable
    _ = (3 * moment) * ‖t‖ ^ (2 : ℕ) := by
          dsimp [upper, moment]
          rw [tsum_mul_right, tsum_mul_left]
    _ ≤ C * ‖t‖ ^ (2 : ℕ) := by
          dsimp [C]
          nlinarith

/-- Helper for Exercise 17.5.3: two support atoms spanning `ℝ²` force a quadratic lower bound on
the real-part defect of the planar characteristic function near the origin. -/
private lemma planarCharFunReDefectLowerBoundNearZeroOfSupportPairSpanTop
    (ν : PMF (LatticePoint 2))
    {x y : LatticePoint 2}
    (hx : x ∈ ν.support) (hy : y ∈ ν.support)
    (hxy_span :
      Submodule.span ℝ ({latticeEmbedding x, latticeEmbedding y} :
        Set (EuclideanSpace ℝ (Fin 2))) = ⊤) :
    ∃ c > 0, ∃ δ > 0, ∀ t : EuclideanSpace ℝ (Fin 2), ‖t‖ ≤ δ →
      c * ‖t‖ ^ (2 : ℕ) ≤ 1 - (charFun (ν.toMeasure.map latticeEmbedding) t).re := by
  classical
  let v : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![latticeEmbedding x, latticeEmbedding y]
  let w : Fin 2 → ℝ := ![(ν x).toReal, (ν y).toReal]
  let α : ℝ := 2 / Real.pi ^ 2
  have hx_mass_pos : 0 < (ν x).toReal := by
    exact ENNReal.toReal_pos ((PMF.mem_support_iff ν x).1 hx) (PMF.apply_lt_top ν x).ne
  have hy_mass_pos : 0 < (ν y).toReal := by
    exact ENNReal.toReal_pos ((PMF.mem_support_iff ν y).1 hy) (PMF.apply_lt_top ν y).ne
  have hw : ∀ i : Fin 2, 0 < w i := by
    intro i
    fin_cases i
    · simpa [w] using hx_mass_pos
    · simpa [w] using hy_mass_pos
  have hv_range :
      Set.range v =
        ({latticeEmbedding x, latticeEmbedding y} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [v]
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨0, by simp [v]⟩
      · exact ⟨1, by simp [v]⟩
  have hcoercive_span : Submodule.span ℝ (Set.range v) = ⊤ := by
    simpa [hv_range] using hxy_span
  obtain ⟨c0, hc0_pos, hc0_bound⟩ :=
    weightedInnerSqCoercive_of_spanTop v w hw hcoercive_span
  let δx : ℝ := Real.pi / max ‖latticeEmbedding x‖ 1
  let δy : ℝ := Real.pi / max ‖latticeEmbedding y‖ 1
  let δ : ℝ := min δx δy
  have hα_pos : 0 < α := by
    positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ, δx, δy]
    positivity
  have hxy_ne : x ≠ y := by
    intro hxy
    subst hxy
    have hsingle :
        Submodule.span ℝ ({latticeEmbedding x} :
          Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      have hpair_single :
          ({latticeEmbedding x, latticeEmbedding x} :
            Set (EuclideanSpace ℝ (Fin 2))) =
            ({latticeEmbedding x} : Set (EuclideanSpace ℝ (Fin 2))) := by
        ext z
        simp
      simpa [hpair_single] using hxy_span
    have hx_embed_ne_zero :
        latticeEmbedding x ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
      intro hx0
      have htop_bot : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) = ⊥ := by
        calc
          (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
              = Submodule.span ℝ ({latticeEmbedding x} :
                  Set (EuclideanSpace ℝ (Fin 2))) := hsingle.symm
          _ = ⊥ := by
                simp [hx0]
      exact top_ne_bot htop_bot
    have hsingle_finrank :
        Module.finrank ℝ
          (Submodule.span ℝ ({latticeEmbedding x} :
            Set (EuclideanSpace ℝ (Fin 2)))) = 1 := by
      simpa using finrank_span_singleton hx_embed_ne_zero
    have hambient_finrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
      simpa using (Module.finrank_fin_fun (R := ℝ) (n := 2))
    have : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank ℝ
              (Submodule.span ℝ ({latticeEmbedding x} :
                Set (EuclideanSpace ℝ (Fin 2)))) := hsingle_finrank.symm
        _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
              rw [hsingle, finrank_top]
        _ = 2 := hambient_finrank
    omega
  refine ⟨α * c0, mul_pos hα_pos hc0_pos, δ, hδ_pos, ?_⟩
  intro t ht
  let defect : LatticePoint 2 → ℝ := fun z ↦
    (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t))
  have hdefect_nonneg : ∀ z : LatticePoint 2, 0 ≤ defect z := by
    intro z
    exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
  have hmassSummable : Summable (fun z : LatticePoint 2 ↦ 2 * (ν z).toReal) := by
    simpa using (ENNReal.summable_toReal (PMF.tsum_coe_ne_top ν)).mul_left (2 : ℝ)
  have hdefect_le : ∀ z : LatticePoint 2, defect z ≤ 2 * (ν z).toReal := by
    intro z
    have hcos_lower : -1 ≤ Real.cos (inner ℝ (latticeEmbedding z) t) :=
      Real.neg_one_le_cos _
    have hmass_nonneg : 0 ≤ (ν z).toReal := ENNReal.toReal_nonneg
    dsimp [defect]
    nlinarith
  have hdefectSummable : Summable defect :=
    Summable.of_nonneg_of_le hdefect_nonneg hdefect_le hmassSummable
  have htx : ‖t‖ ≤ δx := le_trans ht (min_le_left _ _)
  have hty : ‖t‖ ≤ δy := le_trans ht (min_le_right _ _)
  have hinner_abs_le_pi_x :
      |inner ℝ (latticeEmbedding x) t| ≤ Real.pi := by
    have hinner :
        |inner ℝ (latticeEmbedding x) t| ≤ ‖latticeEmbedding x‖ * ‖t‖ := by
      simpa [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (latticeEmbedding x) t)
    have hprod :
        ‖latticeEmbedding x‖ * ‖t‖ ≤ Real.pi := by
      have hmul :
          ‖latticeEmbedding x‖ * ‖t‖ ≤ ‖latticeEmbedding x‖ * δx := by
        exact mul_le_mul_of_nonneg_left htx (norm_nonneg _)
      have hmax_le : ‖latticeEmbedding x‖ ≤ max ‖latticeEmbedding x‖ 1 := le_max_left _ _
      have hmax_ne : max ‖latticeEmbedding x‖ 1 ≠ 0 := by
        positivity
      have hpi :
          ‖latticeEmbedding x‖ * δx ≤ Real.pi := by
        calc
          ‖latticeEmbedding x‖ * δx
              = ‖latticeEmbedding x‖ * (Real.pi / max ‖latticeEmbedding x‖ 1) := by
                  rfl
          _ ≤ max ‖latticeEmbedding x‖ 1 * (Real.pi / max ‖latticeEmbedding x‖ 1) := by
                exact mul_le_mul_of_nonneg_right hmax_le (by positivity)
          _ = Real.pi := by
                field_simp [δx, hmax_ne]
      exact hmul.trans hpi
    exact hinner.trans hprod
  have hinner_abs_le_pi_y :
      |inner ℝ (latticeEmbedding y) t| ≤ Real.pi := by
    have hinner :
        |inner ℝ (latticeEmbedding y) t| ≤ ‖latticeEmbedding y‖ * ‖t‖ := by
      simpa [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (latticeEmbedding y) t)
    have hprod :
        ‖latticeEmbedding y‖ * ‖t‖ ≤ Real.pi := by
      have hmul :
          ‖latticeEmbedding y‖ * ‖t‖ ≤ ‖latticeEmbedding y‖ * δy := by
        exact mul_le_mul_of_nonneg_left hty (norm_nonneg _)
      have hmax_le : ‖latticeEmbedding y‖ ≤ max ‖latticeEmbedding y‖ 1 := le_max_left _ _
      have hmax_ne : max ‖latticeEmbedding y‖ 1 ≠ 0 := by
        positivity
      have hpi :
          ‖latticeEmbedding y‖ * δy ≤ Real.pi := by
        calc
          ‖latticeEmbedding y‖ * δy
              = ‖latticeEmbedding y‖ * (Real.pi / max ‖latticeEmbedding y‖ 1) := by
                  rfl
          _ ≤ max ‖latticeEmbedding y‖ 1 * (Real.pi / max ‖latticeEmbedding y‖ 1) := by
                exact mul_le_mul_of_nonneg_right hmax_le (by positivity)
          _ = Real.pi := by
                field_simp [δy, hmax_ne]
      exact hmul.trans hpi
    exact hinner.trans hprod
  have hx_cos :
      α * (inner ℝ (latticeEmbedding x) t) ^ (2 : ℕ) ≤
        1 - Real.cos (inner ℝ (latticeEmbedding x) t) := by
    have hcos :=
      Real.cos_le_one_sub_mul_cos_sq
        (x := inner ℝ (latticeEmbedding x) t) hinner_abs_le_pi_x
    dsimp [α]
    nlinarith [hcos, sq_nonneg (inner ℝ (latticeEmbedding x) t), Real.pi_pos]
  have hy_cos :
      α * (inner ℝ (latticeEmbedding y) t) ^ (2 : ℕ) ≤
        1 - Real.cos (inner ℝ (latticeEmbedding y) t) := by
    have hcos :=
      Real.cos_le_one_sub_mul_cos_sq
        (x := inner ℝ (latticeEmbedding y) t) hinner_abs_le_pi_y
    dsimp [α]
    nlinarith [hcos, sq_nonneg (inner ℝ (latticeEmbedding y) t), Real.pi_pos]
  have hx_defect :
      α * ((ν x).toReal * (inner ℝ (latticeEmbedding x) t) ^ (2 : ℕ)) ≤ defect x := by
    have hmass_nonneg : 0 ≤ (ν x).toReal := ENNReal.toReal_nonneg
    dsimp [defect]
    nlinarith [hx_cos]
  have hy_defect :
      α * ((ν y).toReal * (inner ℝ (latticeEmbedding y) t) ^ (2 : ℕ)) ≤ defect y := by
    have hmass_nonneg : 0 ≤ (ν y).toReal := ENNReal.toReal_nonneg
    dsimp [defect]
    nlinarith [hy_cos]
  have hweighted :
      c0 * ‖t‖ ^ (2 : ℕ) ≤
        (ν x).toReal * (inner ℝ (latticeEmbedding x) t) ^ (2 : ℕ) +
          (ν y).toReal * (inner ℝ (latticeEmbedding y) t) ^ (2 : ℕ) := by
    simpa [v, w] using hc0_bound t
  have hpair_lower :
      (α * c0) * ‖t‖ ^ (2 : ℕ) ≤ defect x + defect y := by
    have hscaled :
        (α * c0) * ‖t‖ ^ (2 : ℕ) ≤
          α * ((ν x).toReal * (inner ℝ (latticeEmbedding x) t) ^ (2 : ℕ) +
            (ν y).toReal * (inner ℝ (latticeEmbedding y) t) ^ (2 : ℕ)) := by
      have := mul_le_mul_of_nonneg_left hweighted (le_of_lt hα_pos)
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    have hterms :
        α * ((ν x).toReal * (inner ℝ (latticeEmbedding x) t) ^ (2 : ℕ) +
            (ν y).toReal * (inner ℝ (latticeEmbedding y) t) ^ (2 : ℕ)) ≤
          defect x + defect y := by
      nlinarith [hx_defect, hy_defect]
    exact hscaled.trans hterms
  have hpair_tsum :
      defect x + defect y ≤ ∑' z : LatticePoint 2, defect z := by
    let s : Finset (LatticePoint 2) := {x, y}
    calc
      defect x + defect y = Finset.sum s defect := by
        simp [s, hxy_ne, add_comm]
      _ ≤ ∑' z : LatticePoint 2, defect z := by
        exact hdefectSummable.sum_le_tsum s
          (fun z hz ↦ hdefect_nonneg z)
  -- Proof comment: the two selected atoms already contribute a coercive weighted-inner-product
  -- sum, and on the small ball each cosine defect dominates the corresponding quadratic phase.
  rw [planarCharFun_reDefect_eq_tsum_one_sub_cos]
  calc
    (α * c0) * ‖t‖ ^ (2 : ℕ) ≤ defect x + defect y := hpair_lower
    _ ≤ ∑' z : LatticePoint 2, defect z := hpair_tsum
    _ = ∑' z : LatticePoint 2, (ν z).toReal * (1 - Real.cos (inner ℝ (latticeEmbedding z) t)) := by
          simp [defect]

/-- Helper for Exercise 17.5.3: on a small ball and for `1 / 2 ≤ r < 1`, the real part of the
Abelized reciprocal denominator dominates the model singularity `((1 - r) + ‖t‖²)⁻¹`. -/
private lemma planarReciprocalRealPart_lowerBound_smallBall
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    ∃ c > 0, ∃ δ > 0, ∀ r : ℝ, (1 / 2 : ℝ) ≤ r → r < 1 →
      ∀ t : EuclideanSpace ℝ (Fin 2), ‖t‖ ≤ δ →
        c / ((1 - r) + ‖t‖ ^ (2 : ℕ)) ≤
          Complex.re
            ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) := by
  -- Route correction: instead of reopening the shell argument, work directly with
  -- `Re ((1 - r * φ(t))⁻¹) = Re (1 - r * φ(t)) / ‖1 - r * φ(t)‖²`.
  obtain ⟨C, hC_pos, hC⟩ :=
    planarCharFunComplexDefect_le_quadratic_of_meanZero (ν := ν) hmean hsecond
  obtain ⟨x, y, hx, hy, hxy_span⟩ :=
    existsSupportPair_spanTop_of_supportSpan_eq_top (ν := ν) hspan
  obtain ⟨c0, hc0_pos, δ, hδ_pos, hsmallBall⟩ :=
    planarCharFunReDefectLowerBoundNearZeroOfSupportPairSpanTop
      (ν := ν) hx hy hxy_span
  let m : ℝ := min 1 (c0 / 2)
  let K : ℝ := (1 + C) ^ (2 : ℕ)
  have hm_pos : 0 < m := by
    dsimp [m]
    refine lt_min zero_lt_one ?_
    positivity
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨m / K, div_pos hm_pos hK_pos, δ, hδ_pos, ?_⟩
  intro r hr_half hr_lt t ht
  let φ : ℂ := charFun (ν.toMeasure.map latticeEmbedding) t
  let a : ℝ := (1 - r) + ‖t‖ ^ (2 : ℕ)
  let z : ℂ := 1 - (r : ℂ) * φ
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num) hr_half
  have hr_le_one : r ≤ 1 := le_of_lt hr_lt
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith [sq_nonneg ‖t‖, hr_lt]
  have hz_re_eq : z.re = (1 - r) + r * (1 - φ.re) := by
    calc
      z.re = 1 - r * φ.re := by
        simp [z, φ, Complex.mul_re]
      _ = (1 - r) + r * (1 - φ.re) := by ring
  have hz_eq :
      z = (((1 - r : ℝ) : ℂ) + (r : ℂ) * (1 - φ)) := by
    refine Complex.ext ?_ ?_
    · simp [z, φ]
      ring
    · simp [z, φ]
  have hz_norm_le :
      ‖z‖ ≤ (1 - r) + C * ‖t‖ ^ (2 : ℕ) := by
    calc
      ‖z‖ = ‖(((1 - r : ℝ) : ℂ) + (r : ℂ) * (1 - φ))‖ := by rw [hz_eq]
      _ ≤ ‖((1 - r : ℝ) : ℂ)‖ + ‖(r : ℂ) * (1 - φ)‖ := norm_add_le _ _
      _ = |1 - r| + ‖(r : ℂ)‖ * ‖1 - φ‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul]
      _ ≤ (1 - r) + ‖1 - φ‖ := by
            have hr_norm_le : ‖(r : ℂ)‖ ≤ 1 := by
              simpa [Complex.norm_real, Real.norm_of_nonneg hr_nonneg] using hr_le_one
            have h1r_nonneg : 0 ≤ 1 - r := sub_nonneg.mpr hr_le_one
            have hφ_nonneg : 0 ≤ ‖1 - φ‖ := norm_nonneg _
            have hmul_le : ‖(r : ℂ)‖ * ‖1 - φ‖ ≤ ‖1 - φ‖ := by
              simpa using mul_le_mul_of_nonneg_right hr_norm_le hφ_nonneg
            rw [abs_of_nonneg h1r_nonneg]
            linarith
      _ ≤ (1 - r) + C * ‖t‖ ^ (2 : ℕ) := by
            gcongr
            simpa [φ] using hC t
  have hz_normSq_le : Complex.normSq z ≤ K * a ^ (2 : ℕ) := by
    have hKa_nonneg : 0 ≤ (1 + C) * a := by
      positivity
    have hz_norm_le' : ‖z‖ ≤ (1 + C) * a := by
      calc
        ‖z‖ ≤ (1 - r) + C * ‖t‖ ^ (2 : ℕ) := hz_norm_le
        _ ≤ (1 + C) * a := by
              dsimp [a]
              nlinarith [sq_nonneg ‖t‖, hC_pos, hr_le_one]
    rw [Complex.normSq_eq_norm_sq]
    have hsq :
        ‖z‖ ^ (2 : ℕ) ≤ ((1 + C) * a) ^ (2 : ℕ) := by
      nlinarith [norm_nonneg z, hz_norm_le', hKa_nonneg]
    calc
      ‖z‖ ^ (2 : ℕ) ≤ ((1 + C) * a) ^ (2 : ℕ) := hsq
      _ = K * a ^ (2 : ℕ) := by
            dsimp [K]
            ring
  have hm_le_one : m ≤ 1 := by
    dsimp [m]
    exact min_le_left _ _
  have hm_le_halfc : m ≤ c0 / 2 := by
    dsimp [m]
    exact min_le_right _ _
  have hdefect_lower :
      c0 * ‖t‖ ^ (2 : ℕ) ≤ 1 - φ.re := by
    simpa [φ] using hsmallBall t ht
  have hr_defect_lower :
      (c0 / 2) * ‖t‖ ^ (2 : ℕ) ≤ r * (1 - φ.re) := by
    have hhalf_mul :
        (1 / 2 : ℝ) * (c0 * ‖t‖ ^ (2 : ℕ)) ≤ r * (c0 * ‖t‖ ^ (2 : ℕ)) := by
      have hterm_nonneg : 0 ≤ c0 * ‖t‖ ^ (2 : ℕ) := by positivity
      exact mul_le_mul_of_nonneg_right hr_half hterm_nonneg
    calc
      (c0 / 2) * ‖t‖ ^ (2 : ℕ) = (1 / 2 : ℝ) * (c0 * ‖t‖ ^ (2 : ℕ)) := by ring
      _ ≤ r * (c0 * ‖t‖ ^ (2 : ℕ)) := hhalf_mul
      _ ≤ r * (1 - φ.re) := by
            exact mul_le_mul_of_nonneg_left hdefect_lower hr_nonneg
  have hz_re_lower : m * a ≤ z.re := by
    calc
      m * a = m * (1 - r) + m * (‖t‖ ^ (2 : ℕ)) := by
        dsimp [a]
        ring
      _ ≤ 1 * (1 - r) + (c0 / 2) * (‖t‖ ^ (2 : ℕ)) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_right hm_le_one (sub_nonneg.mpr hr_le_one)
            · exact mul_le_mul_of_nonneg_right hm_le_halfc (by positivity)
      _ ≤ (1 - r) + r * (1 - φ.re) := by
            nlinarith
      _ = z.re := hz_re_eq.symm
  have hz_re_pos : 0 < z.re := by
    exact lt_of_lt_of_le (mul_pos hm_pos ha_pos) hz_re_lower
  have hz_ne_zero : z ≠ 0 := by
    intro hz0
    have : z.re = 0 := by simpa [hz0]
    exact hz_re_pos.ne' this
  have hz_normSq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne_zero
  have hcore :
      ((m / K) / a) * Complex.normSq z ≤ z.re := by
    calc
      ((m / K) / a) * Complex.normSq z ≤ ((m / K) / a) * (K * a ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hz_normSq_le (by positivity)
      _ = m * a := by
            field_simp [hK_pos.ne', ha_pos.ne']
      _ ≤ z.re := hz_re_lower
  -- Proof comment: the denominator has positive real part, so `Complex.inv_re` reduces the
  -- reciprocal estimate to a single quadratic real-part lower bound and norm-square upper bound.
  rw [Complex.inv_re, le_div_iff₀ hz_normSq_pos]
  simpa [a, z, φ] using hcore

/-- Helper for Exercise 17.5.3: a one-dimensional zero-drift walk with finite first moment has
divergent origin return-mass series. -/
-- Route correction: the direct `Theorem_17_39` import is blocked because its `.olean` is missing
-- in the current Lake state, so this proof reuses the compiled public one-dimensional recurrence
-- theorem from `Theorem_17_40` on the canonical product-start realization.
private lemma integerOriginMass_tsum_eq_top_of_integrable_mean_zero
    (μ : PMF ℤ)
    (hμ_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) μ.toMeasure)
    (hμ_mean_zero : ∫ z, (z : ℝ) ∂μ.toMeasure = 0) :
    ∑' n : ℕ, ((dirac_convolution_kernel μ.toMeasure ^ n) (0 : ℤ)) ({0} : Set ℤ) = ⊤ := by
  let ν : ProbabilityMeasure ℤ := ⟨μ.toMeasure, by infer_instance⟩
  obtain ⟨Ω', hΩ', Q, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :
      ∃ Ω' : Type, ∃ _ : MeasurableSpace Ω', ∃ Q : Measure Ω', ∃ Zlift : ULift ℕ → Ω' → ℤ,
        (∀ i : ULift ℕ, Measurable (Zlift i)) ∧
          (∀ i : ULift ℕ, HasLaw (Zlift i) (ν : Measure ℤ) Q) ∧
          iIndepFun Zlift Q ∧ IsProbabilityMeasure Q := by
    simpa using ProbabilityTheory.exists_iid (ULift ℕ) (ν : Measure ℤ)
  let Qprob : ProbabilityMeasure Ω' := ⟨Q, hQ_prob⟩
  let Z : ℕ → Ω' → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZ_meas' : ∀ n : ℕ, Measurable (Z n) := by
    intro n
    simpa [Z] using hZ_meas ⟨n⟩
  have hp_stochastic : IsStochasticMatrix (convolutionStepMatrix ν) :=
    convolutionStepMatrix_isStochastic ν
  have hp_translation : IsTranslationInvariantStepMatrix (convolutionStepMatrix ν) :=
    convolutionStepMatrix_isTranslationInvariant ν
  have horiginRow : discreteMatrixKernel (convolutionStepMatrix ν) 0 = (ν : Measure ℤ) :=
    convolutionStepMatrix_originRow_eq ν
  have hZ_law' :
      ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel (convolutionStepMatrix ν) 0) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob, horiginRow] using hZ_law ⟨n⟩
  have hZ_indep' : iIndepFun Z (Qprob : Measure Ω') := by
    simpa [Z, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  let hdisc :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (convolutionStepMatrix ν) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) :=
    productStartRandomWalk_isMarkovProcessRealization
      (convolutionStepMatrix ν) hp_stochastic hp_translation Qprob Z hZ_meas' hZ_indep' hZ_law'
  let hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := by
    simpa [convolutionStepMatrixKernel_eq ν] using hdisc
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := hconv
  have hrecurrent :
      IsRecurrentMarkovChain (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Z) :=
    (integerRandomWalk_recurrent_iff_zero_stepLawMean
      (ν := ν)
      (P := productStartRandomWalkMeasure Qprob)
      (X := productStartRandomWalk Z)
      (by simpa [ν] using hμ_integrable)).2
      (by simpa [ν] using hμ_mean_zero)
  have hgreen :
      (G[productStartRandomWalkMeasure Qprob, productStartRandomWalk Z]) (0 : ℤ) 0 = ⊤ := by
    -- Proof comment: the imported one-dimensional recurrence theorem makes the origin state
    -- recurrent for the canonical product-start realization, so the diagonal Green value diverges.
    exact
      greenFunctionSelf_eq_top_of_isRecurrentState_general
        (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (P := productStartRandomWalkMeasure Qprob)
        (X := productStartRandomWalk Z)
        0 (hrecurrent 0)
  -- Proof comment: rewrite the canonical origin Green value back to the convolution-kernel
  -- origin-mass series.
  rw [integerWalk_greenFunction_zero_zero_eq_tsum_originMass
    (ν := ν) (P := productStartRandomWalkMeasure Qprob) (X := productStartRandomWalk Z)] at hgreen
  simpa [ν] using hgreen

/-- Helper for Exercise 17.5.3: the genuine rank-one branch reduces to a one-dimensional walk
along a linear equivalence `ℤ ≃ₗ[ℤ] H`. -/
-- Route correction: the support-span transport already closes, so the rank-one branch now
-- rewrites the ambient origin Green series to the induced integer law and invokes the preceding
-- one-dimensional divergence helper.
lemma planarWalk_originGreen_eq_top_of_supportRank_one
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (hHone :
      Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) = 1)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    (G[P, X]) (0 : LatticePoint 2) 0 = ⊤ := by
  rcases supportSpan_nonemptyLinearEquivInt (ν := ν) hHone with ⟨e⟩
  let μZ : PMF ℤ := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  have hμZ :
      Integrable (fun z : ℤ ↦ (z : ℝ)) μZ.toMeasure ∧
        ∫ z, (z : ℝ) ∂μZ.toMeasure = 0 := by
    simpa [μZ] using
      integerStepLaw_integrable_mean_zero_of_planarRankOne
        (ν := ν) (e := e) hmean hsecond
  have horiginMass :
      ∑' n : ℕ, ((dirac_convolution_kernel μZ.toMeasure ^ n) (0 : ℤ)) ({0} : Set ℤ) = ⊤ :=
    integerOriginMass_tsum_eq_top_of_integrable_mean_zero μZ hμZ.1 hμZ.2
  -- Proof comment: the ambient origin Green series transports through the support span and the
  -- rank-one linear equivalence to the induced integer walk, whose origin series diverges.
  calc
    (G[P, X]) (0 : LatticePoint 2) 0 =
        ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) := by
            exact latticeWalk_greenFunction_zero_zero_eq_tsum_originMassLocal
              (ν := ν) (P := P) (X := X)
    _ = ∑' n : ℕ, ((dirac_convolution_kernel μZ.toMeasure ^ n) (0 : ℤ)) ({0} : Set ℤ) := by
          refine tsum_congr fun n ↦ ?_
          simpa [μZ] using supportSpanOriginMass_eq_integerOriginMass (ν := ν) (e := e) n
    _ = ⊤ := horiginMass

/-- Helper for Exercise 17.5.3: summing the exact Fourier inversion identities before taking real
parts rewrites the Abelized planar origin series as a reciprocal Fourier integral. -/
private lemma planarAbelizedOriginMass_eq_complexReciprocalIntegral
    (ν : PMF (LatticePoint 2)) {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    (∑' n : ℕ,
      (((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
        ({0} : Set (LatticePoint 2))) * r ^ n : ℝ) : ℂ)) =
      (((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ) *
        ∫ t in latticeFrequencyCube 2,
          ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (latticeFrequencyCube 2)
  let φ : EuclideanSpace ℝ (Fin 2) → ℂ :=
    fun t ↦ charFun (ν.toMeasure.map latticeEmbedding) t
  let F : ℕ → EuclideanSpace ℝ (Fin 2) → ℂ := fun n t ↦ ((r : ℂ) * φ t) ^ n
  let c : ℂ := (((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ)
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, measurableSet_latticeFrequencyCube, volume_latticeFrequencyCube]
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) μ := by
    intro n
    dsimp [F, φ]
    fun_prop
  have hF_bound :
      ∀ n : ℕ, ∀ t : EuclideanSpace ℝ (Fin 2), ‖F n t‖ ≤ r ^ n := by
    intro n t
    -- Proof comment: on the Fourier cube, the geometric ratio has norm at most `r`.
    calc
      ‖F n t‖ = ‖(r : ℂ) * φ t‖ ^ n := by
        simp [F]
      _ ≤ r ^ n := by
        gcongr
        exact planarCharFun_mul_norm_le (ν := ν) hr_nonneg t
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    refine Integrable.mono' (g := fun _ ↦ r ^ n) ?_ (hF_meas n) ?_
    · simpa using (integrable_const (μ := μ) (r ^ n : ℝ))
    · filter_upwards [] with t
      exact hF_bound n t
  have hF_sum : Summable (fun n : ℕ ↦ ∫ t, ‖F n t‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_)
      ((summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left (μ.real Set.univ))
    calc
      ∫ t, ‖F n t‖ ∂μ ≤ ∫ t, r ^ n ∂μ := by
        refine integral_mono_of_nonneg ?_ (integrable_const (μ := μ) (r ^ n : ℝ)) ?_
        · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
        · filter_upwards [] with t
          exact hF_bound n t
      _ = μ.real Set.univ * r ^ n := by
        rw [integral_const]
        simp [smul_eq_mul, mul_comm]
  -- Proof comment: rewrite each coefficient through Fourier inversion, interchange the geometric
  -- series with the cube integral, and only then sum the geometric series in `ℂ`.
  calc
    (∑' n : ℕ,
      (((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
        ({0} : Set (LatticePoint 2))) * r ^ n : ℝ) : ℂ)) =
        ∑' n : ℕ, c * ∫ t, F n t ∂μ := by
          refine tsum_congr fun n ↦ ?_
          have hmass := planarOriginMass_eq_fourierIntegral (ν := ν) n
          calc
            (((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
              ({0} : Set (LatticePoint 2))) * r ^ n : ℝ) : ℂ)
                = (r : ℂ) ^ n *
                    ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
                      ({0} : Set (LatticePoint 2)) : ℝ) : ℂ) := by
                        simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (r : ℂ) ^ n *
                (c * ∫ t in latticeFrequencyCube 2, φ t ^ n ∂volume) := by
                  rw [hmass]
            _ = c * ((r : ℂ) ^ n * ∫ t in latticeFrequencyCube 2, φ t ^ n ∂volume) := by
                  ring
            _ = c * ∫ t in latticeFrequencyCube 2, (r : ℂ) ^ n * φ t ^ n ∂volume := by
                  congr 1
                  simpa [smul_eq_mul] using
                    (integral_const_mul ((r : ℂ) ^ n)
                      (fun t : EuclideanSpace ℝ (Fin 2) ↦ φ t ^ n)).symm
            _ = c * ∫ t, F n t ∂μ := by
                  congr 1
                  refine integral_congr_ae ?_
                  filter_upwards [] with t
                  simpa [F] using (mul_pow (r : ℂ) (φ t) n).symm
    _ = c * ∑' n : ℕ, ∫ t, F n t ∂μ := by
          rw [tsum_mul_left]
    _ = c * ∫ t, ∑' n : ℕ, F n t ∂μ := by
          rw [integral_tsum_of_summable_integral_norm hF_int hF_sum]
    _ = c * ∫ t in latticeFrequencyCube 2,
          ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [] with t
          simpa [F, φ] using
            (tsum_geometric_of_norm_lt_one
              (planarCharFun_mul_norm_lt_one (ν := ν) hr_nonneg hr_lt_one t))

/-- Helper for Exercise 17.5.3: the Abelized planar origin-mass series is the real part of the
reciprocal Fourier integral once the geometric series is summed in `ℂ`. -/
private lemma planarAbelizedOriginMass_eq_reciprocalIntegral
    (ν : PMF (LatticePoint 2)) {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    ∑' n : ℕ,
      ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
        ({0} : Set (LatticePoint 2))) * r ^ n) =
      ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
        ∫ t in latticeFrequencyCube 2,
          Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (latticeFrequencyCube 2)
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, measurableSet_latticeFrequencyCube, volume_latticeFrequencyCube]
  have hRecipMeas :
      AEStronglyMeasurable
        (fun t : EuclideanSpace ℝ (Fin 2) ↦
          (1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) μ := by
    have hBase :
        AEMeasurable
          (fun t : EuclideanSpace ℝ (Fin 2) ↦
            (1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t) μ := by
      dsimp [μ]
      fun_prop
    exact hBase.inv.aestronglyMeasurable
  have hRecipInt :
      Integrable
        (fun t : EuclideanSpace ℝ (Fin 2) ↦
          (1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) μ := by
    refine Integrable.mono' (g := fun _ ↦ (1 - r)⁻¹) ?_ hRecipMeas ?_
    · simpa using (integrable_const (μ := μ) ((1 - r)⁻¹ : ℝ))
    · filter_upwards [] with t
      have hratio_le :
          ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ r :=
        planarCharFun_mul_norm_le (ν := ν) hr_nonneg t
      have hratio_lt :
          ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ < 1 :=
        planarCharFun_mul_norm_lt_one (ν := ν) hr_nonneg hr_lt_one t
      have hsub :
          1 - ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤
            ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
        simpa using
          (norm_sub_norm_le (1 : ℂ)
            ((r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t))
      have hlower :
          1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
        linarith
      have hpos : 0 < 1 - r := sub_pos.mpr hr_lt_one
      calc
        ‖((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)‖
          = 1 / ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
              simp [norm_inv]
        _ ≤ 1 / (1 - r) := by
              exact one_div_le_one_div_of_le hpos hlower
        _ = (1 - r)⁻¹ := by rw [one_div]
  have hcomplex :
      (((∑' n : ℕ,
          ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
            ({0} : Set (LatticePoint 2))) * r ^ n)) : ℝ) : ℂ) =
        (((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ) *
          ∫ t in latticeFrequencyCube 2,
            ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
    simpa [Complex.ofReal_tsum] using
      planarAbelizedOriginMass_eq_complexReciprocalIntegral
        (ν := ν) hr_nonneg hr_lt_one
  -- Proof comment: only after the complex geometric series has been summed do we take real parts
  -- and commute `Complex.re` with the cube integral.
  calc
    ∑' n : ℕ,
        ((((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
          ({0} : Set (LatticePoint 2))) * r ^ n) =
        Complex.re
          ((((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ) *
            ∫ t in latticeFrequencyCube 2,
              ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume) := by
            simpa using congrArg Complex.re hcomplex
    _ = ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
          ∫ t in latticeFrequencyCube 2,
            Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
            have hIntRe :
                ∫ t in latticeFrequencyCube 2,
                    Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
                      ∂volume =
                  (∫ t in latticeFrequencyCube 2,
                      ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume).re := by
              simpa [μ] using integral_re hRecipInt
            change
              ((((2 * Real.pi : ℝ) ^ 2)⁻¹ : ℂ) *
                  ∫ t in latticeFrequencyCube 2,
                    ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume).re =
                ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
                  ∫ t in latticeFrequencyCube 2,
                    Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
                      ∂volume
            let z : ℂ :=
              ∫ t in latticeFrequencyCube 2,
                ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume
            have hz : z =
                ∫ t in latticeFrequencyCube 2,
                  ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := rfl
            have hzRe :
                z.re =
                  ∫ t in latticeFrequencyCube 2,
                    Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
                      ∂volume := by
              rw [hz]
              exact hIntRe.symm
            have hmain :
                ((((2 * Real.pi : ℂ) ^ 2)⁻¹ : ℂ) * z).re =
                  ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
                    ∫ t in latticeFrequencyCube 2,
                      Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
                        ∂volume := by
              calc
                ((((2 * Real.pi : ℂ) ^ 2)⁻¹ : ℂ) * z).re
                    = ((2 * Real.pi : ℝ) ^ 2)⁻¹ * z.re := by
                      rw [Complex.mul_re, Complex.inv_re, Complex.inv_im]
                      simp [Complex.normSq, pow_two]
                _ = ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
                      ∫ t in latticeFrequencyCube 2,
                        Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
                          ∂volume := by
                      rw [hzRe]
            simpa [z] using hmain

/-- Helper for Exercise 17.5.3: the reciprocal Fourier integrand is real-nonnegative on the full
frequency cube whenever `0 ≤ r < 1`. -/
private lemma planarReciprocalRealPart_nonneg
    (ν : PMF (LatticePoint 2)) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (t : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) := by
  let φ : ℂ := charFun (ν.toMeasure.map latticeEmbedding) t
  let z : ℂ := 1 - (r : ℂ) * φ
  have hφ_norm_le : ‖φ‖ ≤ 1 := by
    simpa [φ] using
      planarCharFun_mul_norm_le (ν := ν) (r := (1 : ℝ)) (hr_nonneg := by positivity) t
  have hφ_re_le_one : φ.re ≤ 1 := by
    calc
      φ.re ≤ ‖φ‖ := by
        simpa using (RCLike.re_le_norm φ)
      _ ≤ 1 := by
        exact hφ_norm_le
  have hφ_defect_nonneg : 0 ≤ 1 - φ.re := sub_nonneg.mpr hφ_re_le_one
  have hz_re_eq : z.re = (1 - r) + r * (1 - φ.re) := by
    calc
      z.re = 1 - r * φ.re := by
        simp [z, φ, Complex.mul_re]
      _ = (1 - r) + r * (1 - φ.re) := by
        ring
  have hz_re_pos : 0 < z.re := by
    rw [hz_re_eq]
    nlinarith [hφ_defect_nonneg, hr_nonneg, hr_lt_one]
  -- Proof comment: `Complex.inv_re` reduces the sign to the positivity of the real part of the
  -- denominator and the nonnegativity of its norm square.
  have hz_normSq_nonneg : 0 ≤ Complex.normSq z := by
    simpa [Complex.normSq, pow_two] using add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)
  rw [Complex.inv_re]
  exact div_nonneg (le_of_lt hz_re_pos) hz_normSq_nonneg

/-- Helper for Exercise 17.5.3: the reciprocal Fourier real part is integrable on the frequency
cube for every `0 ≤ r < 1`. -/
private lemma planarReciprocalRealPart_integrableOnCube
    (ν : PMF (LatticePoint 2)) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    Integrable
      (fun t : EuclideanSpace ℝ (Fin 2) ↦
        Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹))
      (volume.restrict (latticeFrequencyCube 2)) := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (latticeFrequencyCube 2)
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, measurableSet_latticeFrequencyCube, volume_latticeFrequencyCube]
  have hRecipMeas :
      AEStronglyMeasurable
        (fun t : EuclideanSpace ℝ (Fin 2) ↦
          (1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) μ := by
    have hBase :
        AEMeasurable
          (fun t : EuclideanSpace ℝ (Fin 2) ↦
            (1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t) μ := by
      dsimp [μ]
      fun_prop
    exact hBase.inv.aestronglyMeasurable
  have hRecipInt :
      Integrable
        (fun t : EuclideanSpace ℝ (Fin 2) ↦
          (1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) μ := by
    refine Integrable.mono' (g := fun _ ↦ (1 - r)⁻¹) ?_ hRecipMeas ?_
    · simpa using (integrable_const (μ := μ) ((1 - r)⁻¹ : ℝ))
    · filter_upwards [] with t
      have hratio_le :
          ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤ r :=
        planarCharFun_mul_norm_le (ν := ν) hr_nonneg t
      have hsub :
          1 - ‖(r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ ≤
            ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
        simpa using
          (norm_sub_norm_le (1 : ℂ)
            ((r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t))
      have hlower :
          1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
        linarith
      have hpos : 0 < 1 - r := sub_pos.mpr hr_lt_one
      calc
        ‖((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)‖
          = 1 / ‖(1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t‖ := by
              simp [norm_inv]
        _ ≤ 1 / (1 - r) := by
              exact one_div_le_one_div_of_le hpos hlower
        _ = (1 - r)⁻¹ := by
              rw [one_div]
  -- Proof comment: the complex reciprocal is integrable by the geometric denominator bound, and
  -- taking real parts preserves integrability.
  exact hRecipInt.re

/-- Helper for Exercise 17.5.3: because the reciprocal Fourier real part is nonnegative on the
whole cube, the whole-cube integral dominates its small-ball restriction. -/
private lemma planarReciprocalIntegral_ge_smallBall
    (ν : PMF (LatticePoint 2)) {r δ : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    ∫ t in (latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}),
      Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume
      ≤
        ∫ t in latticeFrequencyCube 2,
          Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹) ∂volume := by
  let smallBall : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}
  let cube : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun t ↦
    Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
  have hsmall_subset : smallBall ⊆ cube := by
    intro t ht
    exact ht.1
  have hf_nonneg : 0 ≤ᵐ[volume.restrict cube] f := by
    exact Filter.Eventually.of_forall fun t ↦
      planarReciprocalRealPart_nonneg (ν := ν) hr_nonneg hr_lt_one t
  have hf_int : Integrable f (volume.restrict cube) :=
    planarReciprocalRealPart_integrableOnCube (ν := ν) hr_nonneg hr_lt_one
  -- Proof comment: monotonicity in the restricted measure is enough because the integrand never
  -- changes sign on the cube.
  simpa [smallBall, cube, f] using
    (integral_mono_measure
      (μ := volume.restrict smallBall)
      (ν := volume.restrict cube)
      (Measure.restrict_mono_set volume hsmall_subset) hf_nonneg hf_int)

/-- Helper for Exercise 17.5.3: each coordinate of a vector in `ℝ²` is bounded by its Euclidean
norm. -/
private lemma euclideanCoordinate_abs_le_norm
    (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |t i| ≤ ‖t‖ := by
  have hcoord_sq_le : (t i) ^ (2 : Nat) ≤ ‖t‖ ^ (2 : Nat) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (t j))
        (Finset.mem_univ i)
  -- Proof comment: compare the chosen coordinate square with the full squared norm and then
  -- take square roots through monotonicity on nonnegative reals.
  exact
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
      (by simpa [sq_abs] using hcoord_sq_le)

/-- Helper for Exercise 17.5.3: for every fixed `r < 1`, the model singularity
`((1 - r) + ‖t‖²)⁻¹` is integrable on any bounded small ball in the frequency cube. -/
private lemma planarModelIntegrableOnSmallBall
    {δ r : ℝ} (hδ_nonneg : 0 ≤ δ) (hr_lt_one : r < 1) :
    IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin 2) ↦ (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹)
      (latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}) volume := by
  let smallBall : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun t ↦ (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹
  have hsmall_meas : MeasurableSet smallBall := by
    refine (measurableSet_latticeFrequencyCube 2).inter ?_
    exact (isClosed_le continuous_norm continuous_const).measurableSet
  have hsmall_lt_top : volume smallBall < ⊤ := by
    calc
      volume smallBall ≤ volume (latticeFrequencyCube 2) := by
        exact measure_mono fun t ht ↦ ht.1
      _ < ⊤ := by
        simpa [volume_latticeFrequencyCube]
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict smallBall
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, hsmall_meas] using hsmall_lt_top
  have hf_meas : AEMeasurable f μ := by
    dsimp [μ, f, smallBall]
    fun_prop
  -- Proof comment: on the fixed small ball the model integrand is trapped between `0` and
  -- `(1 - r)⁻¹`, so finite measure is enough to deduce integrability.
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((1 - r)⁻¹) hf_meas ?_
  filter_upwards [] with t
  have hpos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hdenom_pos : 0 < (1 - r) + ‖t‖ ^ (2 : Nat) := by
    exact add_pos_of_pos_of_nonneg hpos (by positivity)
  constructor
  · exact inv_nonneg.mpr hdenom_pos.le
  ·
    have hdenom_ge : 1 - r ≤ (1 - r) + ‖t‖ ^ (2 : Nat) := by
      exact le_add_of_nonneg_right (sq_nonneg ‖t‖)
    calc
      f t = ((1 - r) + ‖t‖ ^ (2 : Nat))⁻¹ := by
        rfl
      _ ≤ (1 - r)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpos hdenom_ge

/-- Helper for Exercise 17.5.3: every point in the `k`th geometric model box has norm at most
`3 * (4 : ℝ)^k * √a`. -/
private lemma planarModelGeometricBox_norm_le
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    let s : ℝ := (4 : ℝ) ^ k * Real.sqrt a
    ∀ {u : Fin 2 → ℝ},
      u ∈ Set.Icc ![s, 0] ![2 * s, s] →
        ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ≤ 3 * s := by
  let s : ℝ := (4 : ℝ) ^ k * Real.sqrt a
  change
    ∀ {u : Fin 2 → ℝ},
      u ∈ Set.Icc ![s, 0] ![2 * s, s] →
        ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ≤ 3 * s
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  intro u hu
  have hu0_lower : s ≤ u 0 := by
    simpa [s] using hu.1 0
  have hu0_upper : u 0 ≤ 2 * s := by
    simpa [s] using hu.2 0
  have hu1_lower : 0 ≤ u 1 := by
    simpa [s] using hu.1 1
  have hu1_upper : u 1 ≤ s := by
    simpa [s] using hu.2 1
  have hu0_abs : |u 0| ≤ 2 * s := by
    have hu0_nonneg : 0 ≤ u 0 := le_trans hs_nonneg hu0_lower
    simpa [abs_of_nonneg hu0_nonneg] using hu0_upper
  have hu1_abs : |u 1| ≤ s := by
    simpa [abs_of_nonneg hu1_lower] using hu1_upper
  have hu0_sq : (u 0) ^ (2 : Nat) ≤ (2 * s) ^ (2 : Nat) := by
    nlinarith [hu0_abs, hs_nonneg]
  have hu1_sq : (u 1) ^ (2 : Nat) ≤ s ^ (2 : Nat) := by
    nlinarith [hu1_abs, hs_nonneg]
  have hsq : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) ≤ (3 * s) ^ (2 : Nat) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith [hu0_sq, hu1_sq, hs_nonneg]
  -- Proof comment: the geometric box controls each coordinate separately, so the squared norm is
  -- bounded by the square of the coarse `3 * s` envelope.
  exact
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * s)).mp
      (by simpa [pow_two] using hsq)

/-- Helper for Exercise 17.5.3: each geometric box contributes a fixed positive amount to the
model integral. -/
private lemma planarModelGeometricBoxIntegral_ge_oneTenth
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    let s : ℝ := (4 : ℝ) ^ k * Real.sqrt a
    let coordBox : Set (Fin 2 → ℝ) := Set.Icc ![s, 0] ![2 * s, s]
    let box : Set (EuclideanSpace ℝ (Fin 2)) := (WithLp.toLp 2) '' coordBox
    (1 / 10 : ℝ) ≤
      ∫ t in box, ((a + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume := by
  let s : ℝ := (4 : ℝ) ^ k * Real.sqrt a
  let coordBox : Set (Fin 2 → ℝ) := Set.Icc ![s, 0] ![2 * s, s]
  let box : Set (EuclideanSpace ℝ (Fin 2)) := (WithLp.toLp 2) '' coordBox
  change (1 / 10 : ℝ) ≤ ∫ t in box, ((a + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume
  let coordIntegrand : (Fin 2 → ℝ) → ℝ := fun u ↦
    ((a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat)) : ℝ)⁻¹
  let c : ℝ := (10 * s ^ (2 : Nat))⁻¹
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hs_sq_pos : 0 < s ^ (2 : Nat) := by
    positivity
  have hcoord_le : (![s, 0] : Fin 2 → ℝ) ≤ ![2 * s, s] := by
    intro i
    fin_cases i
    · have hs_le : s ≤ 2 * s := by
        nlinarith [hs_nonneg]
      simpa using hs_le
    · simpa using hs_nonneg
  have hcoord_ne_top : volume coordBox ≠ ⊤ := by
    have hcoord_lt_top : volume coordBox < ⊤ := by
      change volume (Set.Icc (![s, 0] : Fin 2 → ℝ) ![2 * s, s]) < ⊤
      rw [Real.volume_Icc_pi]
      simpa using
        (ENNReal.mul_lt_top
          (a := ENNReal.ofReal (2 * s - s))
          (b := ENNReal.ofReal s)
          ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    exact ne_of_lt hcoord_lt_top
  have hcoord_cont : Continuous coordIntegrand := by
    have hbase_cont :
        Continuous (fun u : Fin 2 → ℝ ↦
          (a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) : ℝ)) := by
      fun_prop
    have hbase_ne :
        ∀ u : Fin 2 → ℝ,
          (a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) : ℝ) ≠ 0 := by
      intro u
      have hpos : 0 < (a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) : ℝ) := by
        positivity
      linarith
    simpa [coordIntegrand] using hbase_cont.inv₀ hbase_ne
  have hcoord_int : IntegrableOn coordIntegrand coordBox volume := by
    simpa [coordBox] using Continuous.integrableOn_Icc hcoord_cont
  have hs_sq :
      s ^ (2 : Nat) = (16 : ℝ) ^ k * a := by
    calc
      s ^ (2 : Nat) = ((4 : ℝ) ^ k) ^ (2 : Nat) * (Real.sqrt a) ^ (2 : Nat) := by
        dsimp [s]
        ring
      _ = (16 : ℝ) ^ k * a := by
        rw [Real.sq_sqrt (le_of_lt ha)]
        calc
          ((4 : ℝ) ^ k) ^ (2 : Nat) * a = (4 : ℝ) ^ (k * 2) * a := by
            rw [pow_mul]
          _ = (4 : ℝ) ^ (2 * k) * a := by
            rw [Nat.mul_comm]
          _ = (16 : ℝ) ^ k * a := by
            have hpow16 : (4 : ℝ) ^ (2 * k) = (16 : ℝ) ^ k := by
              calc
                (4 : ℝ) ^ (2 * k) = ((4 : ℝ) ^ 2) ^ k := by
                  rw [pow_mul]
                _ = (16 : ℝ) ^ k := by
                  norm_num
            rw [hpow16]
  have ha_le_ssq : a ≤ s ^ (2 : Nat) := by
    rw [hs_sq]
    have hpow_ge_one : (1 : ℝ) ≤ (16 : ℝ) ^ k := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 16)
    nlinarith
  have hconst_le :
      ∀ u ∈ coordBox, c ≤ coordIntegrand u := by
    intro u hu
    have hnorm : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ≤ 3 * s := by
      simpa [s] using planarModelGeometricBox_norm_le (a := a) ha k hu
    have hnorm_sq : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) ≤ 9 * s ^ (2 : Nat) := by
      have hsq :
          ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ *
              ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ≤
            (3 * s) * (3 * s) := by
        nlinarith [hnorm, norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2)), hs_nonneg]
      nlinarith [hsq]
    have hdenom_pos : 0 < a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) := by
      positivity
    have hdenom_le :
        a + ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : Nat) ≤
          10 * s ^ (2 : Nat) := by
      nlinarith [ha_le_ssq, hnorm_sq]
    -- Proof comment: the box geometry gives the coarse denominator bound
    -- `a + ‖t‖² ≤ 10 s²`, so the reciprocal dominates the corresponding constant.
    simpa [c, coordIntegrand] using one_div_le_one_div_of_le hdenom_pos hdenom_le
  have hcoord_volume :
      volume.real coordBox = s ^ (2 : Nat) := by
    calc
      volume.real coordBox = (2 * s - s) * s := by
        simpa [coordBox] using
          (Real.volume_Icc_pi_toReal (a := (![s, 0] : Fin 2 → ℝ)) (b := ![2 * s, s]) hcoord_le)
      _ = s ^ (2 : Nat) := by
        ring
  have hcoord_lower :
      c * volume.real coordBox ≤ ∫ u in coordBox, coordIntegrand u ∂volume := by
    exact
      MeasureTheory.setIntegral_ge_of_const_le_real
        (s := coordBox) (μ := volume)
        (by simp [coordBox]) hcoord_ne_top hconst_le hcoord_int
  have htransfer :
      ∫ u in coordBox, coordIntegrand u ∂volume =
        ∫ t in box, ((a + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume := by
    symm
    simpa [box, coordBox, coordIntegrand] using
      (MeasurePreserving.setIntegral_image_emb
        (h₁ := PiLp.volume_preserving_toLp (ι := Fin 2))
        (h₂ := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding)
        (g := fun t : EuclideanSpace ℝ (Fin 2) ↦ ((a + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹)
        (s := coordBox))
  calc
    (1 / 10 : ℝ) = c * volume.real coordBox := by
      rw [hcoord_volume]
      dsimp [c]
      field_simp [hs_sq_pos.ne']
    _ ≤ ∫ u in coordBox, coordIntegrand u ∂volume := hcoord_lower
    _ = ∫ t in box, ((a + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume := htransfer

/-- Helper for Exercise 17.5.3: for each prescribed height, finitely many disjoint geometric boxes
fit inside the model small ball when `r` is sufficiently close to `1`. -/
private lemma planarModelSmallBallIntegral_eventually_ge_nat
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_pi : δ ≤ Real.pi / 2) (N : ℕ) :
    Filter.Eventually
      (fun r : ℝ ↦
        (N : ℝ) / 10 ≤
          ∫ t in (latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}),
            (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
  let A : ℝ := 3 * (4 : ℝ) ^ N
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hIoo :
      Set.Ioo (1 - (δ / A) ^ (2 : Nat)) 1 ∈ 𝓝[<] (1 : ℝ) := by
    refine Ioo_mem_nhdsLT ?_
    have : 0 < (δ / A) ^ (2 : Nat) := by
      positivity
    nlinarith
  refine Filter.mem_of_superset hIoo ?_
  intro r hr
  let a : ℝ := 1 - r
  let s : Fin N → ℝ := fun k ↦ (4 : ℝ) ^ k.1 * Real.sqrt a
  let coordBox : Fin N → Set (Fin 2 → ℝ) :=
    fun k ↦ Set.Icc ![s k, 0] ![2 * s k, s k]
  let box : Fin N → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun k ↦ (WithLp.toLp 2) '' coordBox k
  let smallBall : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun t ↦ (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr hr.2
  have hδ_lt_pi : δ < Real.pi := by
    nlinarith [Real.pi_pos, hδ_pi]
  have ha_lt : a < (δ / A) ^ (2 : Nat) := by
    dsimp [a]
    nlinarith [hr.1]
  have hsqrt_lt : Real.sqrt a < δ / A := by
    exact (Real.sqrt_lt' (by positivity : 0 < δ / A)).2 ha_lt
  have hA_sqrt_lt : A * Real.sqrt a < δ := by
    have hmul : A * Real.sqrt a < A * (δ / A) :=
      mul_lt_mul_of_pos_left hsqrt_lt hA_pos
    calc
      A * Real.sqrt a < A * (δ / A) := hmul
      _ = δ := by
            field_simp [hA_pos.ne']
  have hs_bound (k : Fin N) : 3 * s k ≤ δ := by
    have hkpow : (4 : ℝ) ^ k.1 ≤ (4 : ℝ) ^ N := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.le_of_lt k.2)
    calc
      3 * s k = (3 * (4 : ℝ) ^ k.1) * Real.sqrt a := by
        dsimp [s]
        ring
      _ ≤ (3 * (4 : ℝ) ^ N) * Real.sqrt a := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hkpow (by positivity : 0 ≤ (3 : ℝ)))
            (Real.sqrt_nonneg _)
      _ ≤ δ := le_of_lt hA_sqrt_lt
  have hbox_subset : ∀ k : Fin N, box k ⊆ smallBall := by
    intro k t ht
    rcases ht with ⟨u, hu, rfl⟩
    have hnorm_le : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2))‖ ≤ δ := by
      exact le_trans
        (by simpa [a, s] using planarModelGeometricBox_norm_le (a := a) ha k.1 hu)
        (hs_bound k)
    refine ⟨?_, hnorm_le⟩
    rw [mem_latticeFrequencyCube_iff]
    intro i
    have hcoord_abs :
        |((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2)) i)| ≤ δ := by
      exact le_trans (euclideanCoordinate_abs_le_norm _ i) hnorm_le
    have hcoord_lt_pi :
        |((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2)) i)| < Real.pi :=
      lt_of_le_of_lt hcoord_abs hδ_lt_pi
    have hcoord_mem :
        -Real.pi < ((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2)) i) ∧
          ((WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 2)) i) < Real.pi := by
      simpa [abs_lt] using hcoord_lt_pi
    exact ⟨le_of_lt hcoord_mem.1, hcoord_mem.2⟩
  have hbox_disjoint_of_lt :
      ∀ {i j : Fin N}, i.1 < j.1 → Disjoint (box i) (box j) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro t hti htj
    rcases hti with ⟨u, hu, rfl⟩
    rcases htj with ⟨v, hv, huv⟩
    have huv_eq : u = v := WithLp.toLp_injective 2 huv.symm
    subst huv_eq
    have hpow_lt : 2 * (4 : ℝ) ^ i.1 < (4 : ℝ) ^ j.1 := by
      calc
        2 * (4 : ℝ) ^ i.1 < 4 * (4 : ℝ) ^ i.1 := by
          have hpow_pos : 0 < (4 : ℝ) ^ i.1 := by positivity
          nlinarith
        _ = (4 : ℝ) ^ (i.1 + 1) := by
          rw [pow_succ]
          ring
        _ ≤ (4 : ℝ) ^ j.1 := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.succ_le_of_lt hij)
    have hsep : 2 * s i < s j := by
      have hmul := mul_lt_mul_of_pos_right hpow_lt (Real.sqrt_pos.2 ha)
      simpa [s, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hu_upper : u 0 ≤ 2 * s i := by
      simpa [coordBox, s] using hu.2 0
    have hv_lower : s j ≤ u 0 := by
      simpa [coordBox, s] using hv.1 0
    linarith
  have hbox_pairwise : Pairwise (fun i j ↦ Disjoint (box i) (box j)) := by
    intro i j hij
    have hij_val : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Fin.ext h
    rcases lt_or_gt_of_ne hij_val with hij_lt | hij_gt
    · exact hbox_disjoint_of_lt hij_lt
    · exact (hbox_disjoint_of_lt hij_gt).symm
  have hf_int_small : IntegrableOn f smallBall volume := by
    simpa [a, f, smallBall] using
      planarModelIntegrableOnSmallBall (δ := δ) (r := r) (le_of_lt hδ_pos) hr.2
  have hf_nonneg_small : 0 ≤ᵐ[volume.restrict smallBall] f := by
    refine Filter.Eventually.of_forall ?_
    intro t
    dsimp [f, a]
    positivity
  have hbox_int : ∀ k : Fin N, IntegrableOn f (box k) volume := by
    intro k
    exact hf_int_small.mono_set (hbox_subset k)
  have hsmall_dominates :
      ∫ t in ⋃ k, box k, f t ∂volume ≤ ∫ t in smallBall, f t ∂volume := by
    exact
      MeasureTheory.setIntegral_mono_set hf_int_small hf_nonneg_small
        (Filter.Eventually.of_forall fun t ht ↦ by
          rcases Set.mem_iUnion.mp ht with ⟨k, hk⟩
          exact hbox_subset k hk)
  have hsum_lower :
      (N : ℝ) / 10 ≤ ∑ k : Fin N, ∫ t in box k, f t ∂volume := by
    calc
      (N : ℝ) / 10 = ∑ k : Fin N, (1 / 10 : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ k : Fin N, ∫ t in box k, f t ∂volume := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        simpa [a, f, box, s] using planarModelGeometricBoxIntegral_ge_oneTenth (a := a) ha k.1
  -- Proof comment: once the finitely many boxes are packed into the small ball, their uniform
  -- `1 / 10` contributions add up and force the whole small-ball integral above `N / 10`.
  calc
    (N : ℝ) / 10 ≤ ∑ k : Fin N, ∫ t in box k, f t ∂volume := hsum_lower
    _ = ∫ t in ⋃ k, box k, f t ∂volume := by
      symm
      exact
        MeasureTheory.integral_iUnion_fintype
          (fun k ↦
            (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding.measurableSet_image.2 <| by
              simp [box, coordBox])
          hbox_pairwise hbox_int
    _ ≤ ∫ t in smallBall, f t ∂volume := hsmall_dominates
    _ = ∫ t in (latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}),
          (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume := rfl

/-- Helper for Exercise 17.5.3: the model small-ball integral diverges to `atTop` as `r → 1-`. -/
private lemma planarModelSmallBallIntegral_tendsto_top
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_pi : δ ≤ Real.pi / 2) :
    Filter.Tendsto
      (fun r : ℝ ↦
        (∫ t in (latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ}),
          (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (10 * b)
  filter_upwards [planarModelSmallBallIntegral_eventually_ge_nat hδ_pos hδ_pi N] with r hr
  have hbN : b ≤ (N : ℝ) / 10 := by
    nlinarith
  exact le_trans hbN hr

/-- Helper for Exercise 17.5.3: in the full-rank branch, it remains to compare the Abelized
reciprocal Fourier integral with the model logarithmic divergence near the origin. -/
private lemma planarAbelizedOriginMass_tendsto_top_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    Filter.Tendsto
      (fun r : ℝ ↦
        ∑' n : ℕ,
          (((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
            ({0} : Set (LatticePoint 2)) * r ^ n))
      (𝓝[<] (1 : ℝ)) Filter.atTop := by
  obtain ⟨crecip, hcrecip_pos, δrecip, hδrecip_pos, hrecip⟩ :=
    planarReciprocalRealPart_lowerBound_smallBall
      (ν := ν) hspan hmean hsecond
  let δ0 : ℝ := min δrecip (Real.pi / 2)
  have hδ0_pos : 0 < δ0 := by
    exact lt_min hδrecip_pos (by positivity)
  have _ := crecip
  have _ := hcrecip_pos
  have _ := δ0
  have _ := hδ0_pos
  have _ := hrecip
  let smallBall : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2 ∩ {t | ‖t‖ ≤ δ0}
  let model : ℝ → ℝ := fun r ↦
    ∫ t in smallBall, (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹ ∂volume
  let c0 : ℝ := ((2 * Real.pi : ℝ) ^ 2)⁻¹ * crecip
  have hc0_pos : 0 < c0 := by
    dsimp [c0]
    positivity
  have hmodel_top : Filter.Tendsto model (𝓝[<] (1 : ℝ)) Filter.atTop := by
    -- Proof comment: the geometric model integral is exactly the divergence statement already
    -- proved for the truncated frequency ball.
    simpa [model, smallBall] using
      planarModelSmallBallIntegral_tendsto_top hδ0_pos (min_le_right _ _)
  have habel_lower :
      (fun r : ℝ ↦ c0 * model r) ≤ᶠ[𝓝[<] (1 : ℝ)]
        (fun r : ℝ ↦
          ∑' n : ℕ,
            (((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
              ({0} : Set (LatticePoint 2)) * r ^ n)) := by
    refine Filter.mem_of_superset (Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)) ?_
    intro r hr
    let recip : EuclideanSpace ℝ (Fin 2) → ℝ := fun t ↦
      Complex.re ((1 - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹)
    let modelIntegrand : EuclideanSpace ℝ (Fin 2) → ℝ := fun t ↦
      (((1 - r) + ‖t‖ ^ (2 : Nat)) : ℝ)⁻¹
    have hr_nonneg : 0 ≤ r := le_trans (by norm_num) hr.1.le
    have hr_lt_one : r < 1 := hr.2
    have hsmall_meas : MeasurableSet smallBall := by
      refine (measurableSet_latticeFrequencyCube 2).inter ?_
      exact (isClosed_le continuous_norm continuous_const).measurableSet
    have hmodel_int : IntegrableOn modelIntegrand smallBall volume := by
      -- Proof comment: the model singularity is integrable on each fixed truncated ball for
      -- every `r < 1`, so the comparison integral is well-formed.
      simpa [modelIntegrand, smallBall] using
        planarModelIntegrableOnSmallBall (δ := δ0) (r := r) (le_of_lt hδ0_pos) hr_lt_one
    have hrecip_int : IntegrableOn recip smallBall volume := by
      let cube : Set (EuclideanSpace ℝ (Fin 2)) := latticeFrequencyCube 2
      have hcube_int : IntegrableOn recip cube volume := by
        simpa [cube, recip] using
          planarReciprocalRealPart_integrableOnCube (ν := ν) hr_nonneg hr_lt_one
      exact hcube_int.mono_set (by
        intro t ht
        exact ht.1)
    have hscaled_model_int :
        IntegrableOn (fun t ↦ crecip * modelIntegrand t) smallBall volume := by
      exact hmodel_int.const_mul crecip
    have hsmall_compare :
        ∫ t in smallBall, crecip * modelIntegrand t ∂volume
          ≤ ∫ t in smallBall, recip t ∂volume := by
      -- Proof comment: the small-ball reciprocal lower bound upgrades pointwise control to a
      -- set-integral comparison on the same domain.
      refine MeasureTheory.setIntegral_mono_on hscaled_model_int hrecip_int hsmall_meas ?_
      intro t ht
      have htRecip : ‖t‖ ≤ δrecip := by
        exact le_trans ht.2 (min_le_left _ _)
      simpa [modelIntegrand, recip, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        hrecip r (le_of_lt hr.1) hr.2 t htRecip
    have hcube_compare :
        ∫ t in smallBall, recip t ∂volume ≤
          ∫ t in latticeFrequencyCube 2, recip t ∂volume := by
      simpa [smallBall, recip] using
        planarReciprocalIntegral_ge_smallBall (ν := ν) hr_nonneg hr_lt_one (δ := δ0)
    -- Proof comment: the Abelized series equals the whole-cube reciprocal integral, so the
    -- small-ball model lower bound feeds directly into a monotone comparison chain.
    calc
      c0 * model r
        = ((2 * Real.pi : ℝ) ^ 2)⁻¹ *
            ∫ t in smallBall, crecip * modelIntegrand t ∂volume := by
              dsimp [c0, model]
              rw [integral_const_mul]
              ring
      _ ≤ ((2 * Real.pi : ℝ) ^ 2)⁻¹ * ∫ t in smallBall, recip t ∂volume := by
            exact mul_le_mul_of_nonneg_left hsmall_compare (by positivity)
      _ ≤ ((2 * Real.pi : ℝ) ^ 2)⁻¹ * ∫ t in latticeFrequencyCube 2, recip t ∂volume := by
            exact mul_le_mul_of_nonneg_left hcube_compare (by positivity)
      _ =
          ∑' n : ℕ,
            (((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)).real
              ({0} : Set (LatticePoint 2)) * r ^ n) := by
            simpa [recip] using
              (planarAbelizedOriginMass_eq_reciprocalIntegral
                (ν := ν) hr_nonneg hr_lt_one).symm
  have hscaled_top :
      Filter.Tendsto (fun r : ℝ ↦ c0 * model r) (𝓝[<] (1 : ℝ)) Filter.atTop :=
    hmodel_top.const_mul_atTop hc0_pos
  exact Filter.tendsto_atTop_mono' (𝓝[<] (1 : ℝ)) habel_lower hscaled_top

/-- Helper for Exercise 17.5.3: if the Abelized real power series attached to a nonnegative
`ℝ≥0∞` sequence tends to `atTop` as `r → 1-`, then the original `ℝ≥0∞` series cannot be finite. -/
private lemma ennrealTsum_eq_top_of_realAbelizedTendstoAtTop
    (a : ℕ → ENNReal)
    (habel :
      Filter.Tendsto (fun r : ℝ ↦ ∑' n : ℕ, (a n).toReal * r ^ n) (𝓝[<] 1) Filter.atTop) :
    ∑' n : ℕ, a n = ⊤ := by
  by_contra hfinite
  have hsummable : Summable (fun n : ℕ ↦ (a n).toReal) :=
    ENNReal.summable_toReal (f := a) hfinite
  have hfiniteAbel :
      Filter.Tendsto (fun r : ℝ ↦ ∑' n : ℕ, (a n).toReal * r ^ n) (𝓝[<] 1)
        (𝓝 (∑' n : ℕ, (a n).toReal)) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hsummable.hasSum.tendsto_sum_nat
  -- Proof comment: a function that tends to `atTop` cannot simultaneously converge to a finite
  -- real limit along the same filter.
  exact (not_tendsto_nhds_of_tendsto_atTop habel _) hfiniteAbel

/-- Helper for Exercise 17.5.3: the remaining rank-two branch is the pure top-support planar
Fourier/Abelized recurrence statement. -/
private lemma planarOriginMass_tsum_eq_top_of_supportSpan_eq_top
    (ν : PMF (LatticePoint 2))
    (hspan : supportSpan ν = ⊤)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
      ({0} : Set (LatticePoint 2)) = ⊤ := by
  let a : ℕ → ENNReal := fun n ↦
    ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2)) ({0} : Set (LatticePoint 2))
  have habelizedTop :
      Filter.Tendsto
        (fun r : ℝ ↦ ∑' n : ℕ, (a n).toReal * r ^ n) (𝓝[<] 1) Filter.atTop := by
    -- Proof comment: the Fourier/Abelized rewrite is now separated from the remaining small-ball
    -- analysis, so the public divergence lemma consumes only the stabilized final interface.
    simpa [a] using
      planarAbelizedOriginMass_tendsto_top_of_supportSpan_eq_top
        (ν := ν) hspan hmean hsecond
  -- Proof comment: once the Abelized real power series diverges to `atTop`, Abel's theorem rules
  -- out any finite value for the underlying `ℝ≥0∞` origin-mass series.
  exact ennrealTsum_eq_top_of_realAbelizedTendstoAtTop a habelizedTop

/-- Helper for Exercise 17.5.3: the full-rank branch reduces to the canonical irreducible
Chung--Fuchs owner criterion from Theorem 17.41. -/
lemma planarWalk_originGreen_eq_top_of_supportRank_eq_two
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (hHtwo :
      Module.finrank ℤ (Submodule.span ℤ {x : LatticePoint 2 | ν x ≠ 0}) = 2)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    (G[P, X]) (0 : LatticePoint 2) 0 = ⊤ := by
  have hsupport_rank : Module.finrank ℤ (supportSpan ν) = 2 :=
    supportSpan_finrank_eq_two (ν := ν) hHtwo
  rcases supportSpan_nonemptyLinearEquivLatticePointTwo (ν := ν) hsupport_rank with ⟨e⟩
  let μ : PMF (LatticePoint 2) := PMF.map e.symm.toEquiv (supportSpanStepPMF ν)
  have horiginMass :
      ∀ n : ℕ,
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
            ({0} : Set (LatticePoint 2)) =
          ((dirac_convolution_kernel μ.toMeasure ^ n) (0 : LatticePoint 2))
            ({0} : Set (LatticePoint 2)) := by
    intro n
    simpa [μ] using supportSpanOriginMass_eq_latticeOriginMass (ν := ν) (e := e) n
  have hμspan : supportSpan μ = ⊤ := by
    -- Proof comment: after transporting along the support-span equivalence, the new planar law
    -- has literal full support span, so the remaining work is purely analytic on `μ`.
    simpa [μ] using mappedPlanarStepLaw_supportSpan_eq_top_of_supportSpanEquiv (ν := ν) (e := e)
  have hμtransport :
      (∀ i : Fin 2, Integrable (fun z : LatticePoint 2 ↦ (z i : ℝ)) μ.toMeasure ∧
          ∫ z, (z i : ℝ) ∂μ.toMeasure = 0) ∧
        Summable (fun z : LatticePoint 2 ↦ ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
    -- Proof comment: package the mean and quadratic-moment transport once so the remaining
    -- argument can treat `μ` as an ordinary centered planar step law with literal full span.
    simpa [μ] using
      mappedPlanarStepLaw_transportHypotheses_of_supportSpanEquiv
        (ν := ν) (e := e) hmean hsecond
  have hμmean :
      ∀ i : Fin 2, ∑' z : LatticePoint 2, (z i : ℝ) * (μ z).toReal = 0 := by
    intro i
    -- Proof comment: rewrite each transported coordinate mean as the corresponding PMF integral.
    calc
      ∑' z : LatticePoint 2, (z i : ℝ) * (μ z).toReal
        = ∫ z, (z i : ℝ) ∂μ.toMeasure := by
            symm
            simpa [smul_eq_mul, mul_comm] using
              (PMF.integral_eq_tsum μ (fun z : LatticePoint 2 ↦ (z i : ℝ)) (hμtransport.1 i).1)
      _ = 0 := (hμtransport.1 i).2
  have hμsecond :
      ∑' z : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding z‖ ^ 2) * μ z < ⊤ := by
    have hterm :
        ∀ z : LatticePoint 2,
          ENNReal.ofReal (‖latticeEmbedding z‖ ^ 2) * μ z =
            ENNReal.ofReal (‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
      intro z
      rw [show μ z = ENNReal.ofReal (μ z).toReal by
        exact (ENNReal.ofReal_toReal (PMF.apply_lt_top μ z).ne).symm]
      simpa using
        (ENNReal.ofReal_mul (p := ‖latticeEmbedding z‖ ^ 2) (q := (μ z).toReal) (sq_nonneg _)).symm
    calc
      ∑' z : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding z‖ ^ 2) * μ z
        = ∑' z : LatticePoint 2,
            ENNReal.ofReal (‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
              refine tsum_congr fun z ↦ ?_
              exact hterm z
      _ = ENNReal.ofReal
            (∑' z : LatticePoint 2, ‖latticeEmbedding z‖ ^ 2 * (μ z).toReal) := by
              rw [ENNReal.ofReal_tsum_of_nonneg]
              · intro z
                exact mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
              · exact hμtransport.2
      _ < ⊤ := by
            simp
  have hμoriginMass :
      ∑' n : ℕ, ((dirac_convolution_kernel μ.toMeasure ^ n) (0 : LatticePoint 2))
        ({0} : Set (LatticePoint 2)) = ⊤ :=
    planarOriginMass_tsum_eq_top_of_supportSpan_eq_top
      (ν := μ) hμspan hμmean hμsecond
  -- Route correction: `supportSpan ν = ⊤` is false for proper full-rank sublattices of `ℤ²`, so
  -- the remaining proof must first transport the walk from `supportSpan ν` to a planar law with
  -- literal `supportSpan = ⊤`, and only then apply the analytic top-support branch there.
  calc
    (G[P, X]) (0 : LatticePoint 2) 0 =
        ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) := by
            exact latticeWalk_greenFunction_zero_zero_eq_tsum_originMassLocal
              (ν := ν) (P := P) (X := X)
    _ = ∑' n : ℕ, ((dirac_convolution_kernel μ.toMeasure ^ n) (0 : LatticePoint 2))
          ({0} : Set (LatticePoint 2)) := by
            refine tsum_congr fun n ↦ ?_
            exact horiginMass n
    _ = ⊤ := hμoriginMass

/- Layering for Exercise 17.5.3:
- core/canonical owner: a planar step law `ν : PMF (LatticePoint 2)` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law;
- source-facing conclusion: zero mean and finite second moment force recurrence in dimension `2`. -/

-- Proof sketch: apply the two-dimensional Chung--Fuchs recurrence criterion to the canonical step
-- law `ν`; the coordinatewise vanishing first moments and the finite quadratic moment of
-- `latticeEmbedding` are exactly the standard planar hypotheses.
/-- Exercise 17.5.3 at the owner layer: a random walk on `ℤ²` with step law `ν`, zero drift, and
finite second moment is recurrent. The public statement is organized around the intrinsic
increment law rather than a chosen translation-invariant matrix presentation. -/
-- TODO: Reassemble the owner theorem once the rank-one and full-rank branch closures are repaired.
theorem planarRandomWalk_isRecurrent_of_zeroMean_of_finiteSecondMoment
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    IsRecurrentMarkovChain P X := by
  intro x
  let H : Submodule ℤ (LatticePoint 2) := supportSpan ν
  have hsplit : Module.finrank ℤ H ≤ 1 ∨ Module.finrank ℤ H = 2 := by
    simpa [H, supportSpan] using supportSpan_finrank_le_one_or_eq_two (ν := ν)
  have horigin : (G[P, X]) (0 : LatticePoint 2) 0 = ⊤ := by
    rcases hsplit with hle_one | htwo
    · have hzero_or_one : Module.finrank ℤ H = 0 ∨ Module.finrank ℤ H = 1 := by
        omega
      rcases hzero_or_one with hzero | hone
      · have hbot : H = ⊥ := Submodule.finrank_eq_zero.1 hzero
        have hν_zero : ν = PMF.pure (0 : LatticePoint 2) := by
          simpa [H, supportSpan] using stepLaw_eq_pure_zero_of_supportSpan_eq_bot (ν := ν) hbot
        exact
          planarWalk_originGreen_eq_top_of_stepLaw_eq_pure_zero
            (ν := ν) (P := P) (X := X) hν_zero
      · exact
          planarWalk_originGreen_eq_top_of_supportRank_one
            (ν := ν) (P := P) (X := X) (by simpa [H, supportSpan] using hone) hmean hsecond
    · exact
        planarWalk_originGreen_eq_top_of_supportRank_eq_two
          (ν := ν) (P := P) (X := X) (by simpa [H, supportSpan] using htwo) hmean hsecond
  have hdiag : (G[P, X]) x x = ⊤ := by
    calc
      (G[P, X]) x x = (G[P, X]) (0 : LatticePoint 2) 0 := by
        exact planarWalkGreenFunctionSelf_eq_origin (ν := ν) (P := P) (X := X) x
      _ = ⊤ := horigin
  exact
    planarWalkIsRecurrentState_of_greenFunctionSelf_eq_top
      (κ := fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n)
      (P := P) (X := X) x hdiag

-- Proof sketch: if the transition matrix is translation invariant, the common increment law is
-- encoded by the row at the origin,
-- so the owner theorem above reads directly in this matrix presentation.
/-- Bridge form of Exercise 17.5.3: a translation-invariant random walk on `ℤ²` whose common
increment law `p 0` has zero mean and finite second moment is recurrent. -/
-- TODO: Reassemble the translation-invariant bridge once the owner theorem and the discrete-kernel
-- convolution identification are repaired.
theorem translationInvariant_planarRandomWalk_isRecurrent_of_zeroMean_of_finiteSecondMoment
    (p : LatticePoint 2 → LatticePoint 2 → ENNReal)
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (p 0 x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * p 0 x < ⊤) :
    IsRecurrentMarkovChain P X := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hp_stochastic : IsStochasticMatrix p := by
    intro x
    calc
      ∑' y : LatticePoint 2, p x y
        = ((P x : Measure Ω).map (X 1)) Set.univ := by
            symm
            simpa [pow_one, discreteMatrixKernel_apply] using
              congrArg (fun μ : Measure (LatticePoint 2) ↦ μ Set.univ) (hReal.transition_eq x 1)
      _ = 1 := by
            rw [Measure.map_apply (hReal.measurable_process 1) MeasurableSet.univ]
            simp
  let ν : PMF (LatticePoint 2) :=
    ⟨fun y : LatticePoint 2 ↦ p 0 y, ENNReal.summable.hasSum_iff.2 (hp_stochastic 0)⟩
  have hp_eq : p = latticeConvolutionStepMatrix ν := by
    funext x y
    calc
      p x y = p 0 (y - x) := hp x y
      _ = ν (y - x) := rfl
      _ = latticeConvolutionStepMatrix ν x y := by
            change ν (y - x) = dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint 2))
            rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
            rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
            have hpreimage :
                (fun z : LatticePoint 2 ↦ x + z) ⁻¹' ({y} : Set (LatticePoint 2)) =
                  {y - x} := by
              ext z
              simp only [Set.mem_preimage, Set.mem_singleton_iff]
              constructor
              · intro hz
                exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
              · intro hz
                exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
            rw [hpreimage]
            simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (y - x))]
  let hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := by
    simpa [hp_eq, latticeConvolutionStepMatrixKernel_eq ν] using
      (inferInstance :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := hconv
  have hmeanν : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0 := by
    intro i
    simpa [ν] using hmean i
  have hsecondν :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤ := by
    simpa [ν] using hsecond
  -- Proof comment: package the origin row as the common increment law and rewrite the given
  -- translation-invariant realization into the canonical convolution-kernel presentation.
  exact
    planarRandomWalk_isRecurrent_of_zeroMean_of_finiteSecondMoment
      (ν := ν) (P := P) (X := X) hmeanν hsecondν

end ProbabilityTheory
