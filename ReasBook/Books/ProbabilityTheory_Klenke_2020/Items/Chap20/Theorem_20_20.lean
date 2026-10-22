/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_19

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

variable {Ω : Type u}

/-- The event that the Chapter 20 random-walk partial sums of `X` visit `0` infinitely often. -/
def partialSumsReturnToZeroInfinitelyOften (X : ℕ → Ω → ℤ) : Set Ω :=
  {ω | Filter.Frequently (fun n : ℕ ↦ randomWalkPathPartialSum (fun k ↦ X k ω) (n + 1) = 0) atTop}

-- Proof sketch: unfold `partialSumsReturnToZeroInfinitelyOften`; the statement is exactly its
-- defining filter-event formulation.
/- Expanding `partialSumsReturnToZeroInfinitelyOften` gives the event that the `0`-based partial
sums hit `0` for infinitely many times. -/
theorem partialSumsReturnToZeroInfinitelyOften_def (X : ℕ → Ω → ℤ) :
    partialSumsReturnToZeroInfinitelyOften X =
      {ω |
        Filter.Frequently
          (fun n : ℕ ↦ randomWalkPathPartialSum (fun k ↦ X k ω) (n + 1) = 0)
          atTop} := by
  rfl

variable [MeasurableSpace Ω]
variable {P : Measure Ω}
variable {X : ℕ → Ω → ℤ}

local instance : MeasurableSpace (Stream' ℤ) :=
  inferInstanceAs (MeasurableSpace (ℕ → ℤ))

local notation "ℐ" => MeasurableSpace.invariants Stream'.tail
-- Semantic recall note: `MeasurableSpace.invariants` is the canonical tail `σ`-algebra owner,
-- and `canonical_process_stationary_iff_measurePreserving_tail` is the path-space stationarity
-- bridge used below.

/-- Helper for Theorem 20.20: the path law of a stationary process is stationary for the
canonical coordinate process. -/
lemma canonicalPathLaw_stationary
    (hstationary : IsStationaryProcess X P) :
    let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
    let Q : Measure (ℕ → ℤ) := Measure.map ψ P
    IsStationaryProcess Function.eval Q := by
  let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
  let Q : Measure (ℕ → ℤ) := Measure.map ψ P
  have htailMeas : Measurable (Stream'.tail : Stream' ℤ → Stream' ℤ) := by
    -- Proof comment: each shifted coordinate is a coordinate projection, so the tail map is
    -- measurable on path space.
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))
  have htailMap : Measure.map Stream'.tail Q = Q := by
    -- Proof comment: stationarity identifies the shifted path map with the original path map in
    -- distribution.
    calc
      Measure.map Stream'.tail Q = Measure.map (Stream'.tail ∘ ψ) P := by
        simpa [Q] using
          (AEMeasurable.map_map_of_aemeasurable
            htailMeas.aemeasurable
            (by simpa [ψ] using (hstationary.identDistrib 0).aemeasurable_snd))
      _ = Measure.map (fun ω t ↦ X (1 + t) ω) P := by
        congr 1
        ext ω t
        change X (t + 1) ω = X (1 + t) ω
        rw [Nat.add_comm]
      _ = Measure.map ψ P := by
        simpa [Q, ψ] using (hstationary.identDistrib 1).map_eq
      _ = Q := by rfl
  -- Proof comment: the canonical path-space characterization rewrites stationarity as
  -- tail-invariance of the path law.
  exact
    (canonical_process_stationary_iff_measurePreserving_tail Q).mpr
      ⟨htailMeas, htailMap⟩

/-- Helper for Theorem 20.20: on path space, the Birkhoff average of the zeroth coordinate is the
normalized partial sum. -/
lemma birkhoffAverage_evalZero_eq_partialSumDiv (ω : ℕ → ℤ) (n : ℕ) :
    birkhoffAverage ℝ Stream'.tail (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) n ω =
      ((randomWalkPathPartialSum ω n : ℤ) : ℝ) / n := by
  -- Proof comment: expand the Birkhoff sum, rewrite each shifted zeroth coordinate as the
  -- corresponding path increment, and identify the resulting finite sum with the partial sum.
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul, div_eq_mul_inv]
  have hsum :
      ∑ k ∈ Finset.range n, (((Stream'.tail^[k]) ω 0 : ℤ) : ℝ) =
        ((randomWalkPathPartialSum ω n : ℤ) : ℝ) := by
    calc
      ∑ k ∈ Finset.range n, (((Stream'.tail^[k]) ω 0 : ℤ) : ℝ) =
          ∑ k ∈ Finset.range n, (ω k : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        simpa using (iterateTail_apply ω k 0)
      _ = ((randomWalkPathPartialSum ω n : ℤ) : ℝ) := by
        simp [randomWalkPathPartialSum]
  rw [hsum]
  ring

/-- Helper for Theorem 20.20: the prefix maximum of the absolute values of the integer partial
sums up to time `n`. -/
noncomputable def prefixMaxNatAbs (ω : ℕ → ℤ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero _))
    (fun k ↦ Int.natAbs (randomWalkPathPartialSum ω k))

/-- Helper for Theorem 20.20: every visited partial sum up to time `n` lies in the symmetric
integer interval determined by the prefix maximum. -/
lemma randomWalkPathPartialSum_mem_Icc_prefixMaxNatAbs (ω : ℕ → ℤ) {k n : ℕ} (hkn : k ≤ n) :
    randomWalkPathPartialSum ω k ∈
      Set.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ) := by
  -- Proof comment: the defining supremum controls the absolute value of each earlier partial
  -- sum, and the absolute-value bound is equivalent to membership in the symmetric interval.
  have hk_mem : k ∈ Finset.range (n + 1) := by
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hkn)
  have hk_le :
      Int.natAbs (randomWalkPathPartialSum ω k) ≤ prefixMaxNatAbs ω n := by
    simpa [prefixMaxNatAbs] using
      (Finset.le_sup' (fun j ↦ Int.natAbs (randomWalkPathPartialSum ω j)) hk_mem)
  have hk_le' :
      ((Int.natAbs (randomWalkPathPartialSum ω k) : ℕ) : ℤ) ≤
        (prefixMaxNatAbs ω n : ℤ) := by
    exact_mod_cast hk_le
  have hk_abs :
      |randomWalkPathPartialSum ω k| ≤ (prefixMaxNatAbs ω n : ℤ) := by
    simpa [Int.natCast_natAbs] using hk_le'
  simpa [Set.mem_Icc] using abs_le.mp hk_abs

/-- Helper for Theorem 20.20: the number of visited partial sums up to time `n` is bounded by the
cardinality of the symmetric interval cut out by the prefix maximum. -/
lemma randomWalkPathRangeCount_le_twicePrefixMaxNatAbs_add_one (ω : ℕ → ℤ) (n : ℕ) :
    randomWalkPathRangeCount ω n ≤ 2 * prefixMaxNatAbs ω n + 1 := by
  let visited : Set ℤ := Set.range fun k : Fin (n + 1) ↦ randomWalkPathPartialSum ω k
  have hsubset :
      visited ⊆ Set.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ) := by
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact
      randomWalkPathPartialSum_mem_Icc_prefixMaxNatAbs ω (Nat.lt_succ_iff.mp k.2)
  have hcard :
      visited.ncard ≤
        (Set.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ)).ncard := by
    -- Proof comment: the visited-value set is a subset of one concrete finite interval.
    exact Set.ncard_le_ncard hsubset
  have hinterval :
      (Set.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ)).ncard =
        2 * prefixMaxNatAbs ω n + 1 := by
    -- Proof comment: the symmetric interval `[-M, M]` contains exactly `2 * M + 1` integers.
    have hintervalNat :
        (Finset.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ)).card =
          2 * prefixMaxNatAbs ω n + 1 := by
      rw [Int.card_Icc]
      omega
    simpa [Set.ncard_eq_toFinset_card', Set.toFinset_Icc] using hintervalNat
  calc
    randomWalkPathRangeCount ω n = visited.ncard := rfl
    _ ≤ (Set.Icc (-(prefixMaxNatAbs ω n : ℤ)) (prefixMaxNatAbs ω n : ℤ)).ncard := hcard
    _ = 2 * prefixMaxNatAbs ω n + 1 := hinterval

/-- Helper for Theorem 20.20: if the normalized partial sums tend to `0`, then the normalized
prefix maxima of their absolute values also tend to `0`. -/
lemma prefixMaxNatAbsPartialSum_div_tendsto_zero_of_partialSumAverage_zero (ω : ℕ → ℤ)
    (hpartial :
      Tendsto (fun n : ℕ ↦ ((randomWalkPathPartialSum ω n : ℤ) : ℝ) / n) atTop
        (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (prefixMaxNatAbs ω n : ℝ) / n) atTop (nhds 0) := by
  -- Proof comment: fix `ε > 0`, split the index attaining the prefix maximum into a finite
  -- prefix part and a tail part, and control the two pieces separately.
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  rcases Metric.tendsto_atTop.1 hpartial (ε / 2) (half_pos hε) with ⟨N0, hN0⟩
  let m : ℕ := max 1 N0
  let C : ℕ := prefixMaxNatAbs ω m
  have hCzero : Tendsto (fun n : ℕ ↦ (C : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rcases Metric.tendsto_atTop.1 hCzero (ε / 2) (half_pos hε) with ⟨N1, hN1⟩
  refine ⟨max m N1, ?_⟩
  intro n hn
  have hm_le_n : m ≤ n := le_trans (le_max_left _ _) hn
  have hN1_le_n : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos_nat : 0 < n := by
    have h1_le_n : 1 ≤ n := le_trans (le_max_left 1 N0) hm_le_n
    exact Nat.succ_le_iff.mp h1_le_n
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  obtain ⟨k, hk_mem, hk_max⟩ :=
    (Finset.range (n + 1)).exists_mem_eq_sup' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero _))
      (fun j ↦ Int.natAbs (randomWalkPathPartialSum ω j))
  have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk_mem)
  have hk_max' : prefixMaxNatAbs ω n = Int.natAbs (randomWalkPathPartialSum ω k) := by
    simpa [prefixMaxNatAbs] using hk_max
  have hk_max_real :
      (prefixMaxNatAbs ω n : ℝ) = |((randomWalkPathPartialSum ω k : ℤ) : ℝ)| := by
    calc
      (prefixMaxNatAbs ω n : ℝ) =
          (((Int.natAbs (randomWalkPathPartialSum ω k) : ℕ) : ℤ) : ℝ) := by
            exact_mod_cast hk_max'
      _ = |((randomWalkPathPartialSum ω k : ℤ) : ℝ)| := by
            rw [Int.natCast_natAbs, Int.cast_abs]
  have hhalf_lt : ε / 2 < ε := by linarith
  by_cases hkm : k ≤ m
  · have hk_le_C :
        Int.natAbs (randomWalkPathPartialSum ω k) ≤ C := by
      simpa [C, m, prefixMaxNatAbs] using
        (Finset.le_sup' (fun j ↦ Int.natAbs (randomWalkPathPartialSum ω j))
          (Finset.mem_range.2 (Nat.lt_succ_of_le hkm)))
    have hk_le_C_real : (prefixMaxNatAbs ω n : ℝ) ≤ (C : ℝ) := by
      rw [hk_max']
      exact_mod_cast hk_le_C
    have hCsmall : (C : ℝ) / n < ε / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (C : ℝ) / n)] using hN1 n hN1_le_n
    have hratio :
        dist ((prefixMaxNatAbs ω n : ℝ) / n) 0 < ε / 2 := by
      have hratio' :
          (prefixMaxNatAbs ω n : ℝ) / n < ε / 2 := by
        exact lt_of_le_of_lt
          (div_le_div_of_nonneg_right hk_le_C_real (by positivity))
          hCsmall
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (prefixMaxNatAbs ω n : ℝ) / n)] using
        hratio'
    exact lt_trans hratio hhalf_lt
  · have hm_lt_k : m < k := lt_of_not_ge hkm
    have hN0_le_k : N0 ≤ k := le_trans (le_max_right 1 N0) (Nat.le_of_lt hm_lt_k)
    have hk_pos : (0 : ℝ) < k := by
      have hk_pos_nat : 0 < k := by omega
      exact_mod_cast hk_pos_nat
    have hk_small :
        |((randomWalkPathPartialSum ω k : ℤ) : ℝ)| / k < ε / 2 := by
      simpa [Real.dist_eq, abs_div, abs_of_nonneg hk_pos.le] using hN0 k hN0_le_k
    have hk_small' :
        |((randomWalkPathPartialSum ω k : ℤ) : ℝ)| < (ε / 2) * k := by
      exact (div_lt_iff₀ hk_pos).mp hk_small
    have hk_lt :
        (prefixMaxNatAbs ω n : ℝ) < (ε / 2) * n := by
      calc
        (prefixMaxNatAbs ω n : ℝ) =
            |((randomWalkPathPartialSum ω k : ℤ) : ℝ)| := hk_max_real
        _ < (ε / 2) * k := hk_small'
        _ ≤ (ε / 2) * n := by
          gcongr
    have hratio :
        dist ((prefixMaxNatAbs ω n : ℝ) / n) 0 < ε / 2 := by
      have hratio' :
          (prefixMaxNatAbs ω n : ℝ) / n < ε / 2 := by
        exact (div_lt_iff₀ hn_pos).2 hk_lt
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (prefixMaxNatAbs ω n : ℝ) / n)] using
        hratio'
    exact lt_trans hratio hhalf_lt

variable [IsProbabilityMeasure P]

/-- Helper for Theorem 20.20: when the canonical path map is measurable, the centered
conditional-expectation hypothesis on `Ω` transports to the stationary path law. -/
lemma pathLawEvalZeroCondExp_ae_eq_zero_of_measurablePathMap
    (hX0_integrable : Integrable (fun ω ↦ (X 0 ω : ℝ)) P)
    (hcentered :
      P[(fun ω ↦ (X 0 ω : ℝ)) |
          MeasurableSpace.comap
            (fun ω ↦ fun n ↦ X n ω)
            (MeasurableSpace.invariants Stream'.tail)] =ᵐ[P] 0)
    (hψ_meas : Measurable (fun ω ↦ fun n ↦ X n ω)) :
    let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
    let Q : Measure (ℕ → ℤ) := Measure.map ψ P
    Q[(fun ξ ↦ (ξ 0 : ℝ)) |
        MeasurableSpace.invariants (Stream'.tail : (ℕ → ℤ) → (ℕ → ℤ))] =ᵐ[Q] 0 := by
  let mPath : MeasurableSpace (ℕ → ℤ) := inferInstanceAs (MeasurableSpace (ℕ → ℤ))
  let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
  let Q : Measure (ℕ → ℤ) := Measure.map ψ P
  let _ : IsProbabilityMeasure Q := by
    exact Measure.isProbabilityMeasure_map hψ_meas.aemeasurable
  let _ : IsFiniteMeasure Q := by infer_instance
  have hψ_aemeas : AEMeasurable ψ P := hψ_meas.aemeasurable
  have hℐle : ℐ ≤ mPath :=
    MeasurableSpace.invariants_le (Stream'.tail : (ℕ → ℤ) → (ℕ → ℤ))
  have hsf : SigmaFinite (Q.trim hℐle) := by
    letI : IsFiniteMeasure (Q.trim hℐle) := by infer_instance
    exact IsFiniteMeasure.toSigmaFinite (Q.trim hℐle)
  haveI : SigmaFinite (Q.trim hℐle) := hsf
  have hψℐ_meas : Measurable[‹MeasurableSpace Ω›, ℐ] ψ := hψ_meas.mono le_rfl hℐle
  have hmComap : MeasurableSpace.comap ψ ℐ ≤ ‹MeasurableSpace Ω› := hψℐ_meas.comap_le
  have hEval0_meas :
      AEStronglyMeasurable (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) Q := by
    exact
      (((measurable_of_countable ((↑) : ℤ → ℝ)).comp
          (measurable_pi_apply 0)).aestronglyMeasurable)
  have hEval0_int : Integrable (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) Q := by
    refine (integrable_map_measure hEval0_meas hψ_aemeas).2 ?_
    simpa [Function.comp, ψ] using hX0_integrable
  have hPathCond_meas :
      AEStronglyMeasurable (fun ξ : ℕ → ℤ ↦ Q[(fun η ↦ (η 0 : ℝ)) | ℐ] ξ) Q := by
    let hCondStrong : StronglyMeasurable[ℐ] (Q[(fun η ↦ (η 0 : ℝ)) | ℐ]) :=
      stronglyMeasurable_condExp
    exact (hCondStrong.mono hℐle).aestronglyMeasurable
  have hPullbackCond_int :
      Integrable (fun ω ↦ Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] (ψ ω)) P := by
    exact (integrable_map_measure hPathCond_meas hψ_aemeas).1 integrable_condExp
  have hPullbackCond_meas :
      AEStronglyMeasurable[MeasurableSpace.comap ψ ℐ]
        (fun ω ↦ Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] (ψ ω)) P := by
    let hCondStrong : StronglyMeasurable[ℐ] (Q[(fun η ↦ (η 0 : ℝ)) | ℐ]) :=
      stronglyMeasurable_condExp
    exact
      (hCondStrong.comp_measurable (comap_measurable ψ)).aestronglyMeasurable
  have hPullbackCondEq :
      (fun ω ↦ Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] (ψ ω)) =ᵐ[P]
        P[(fun ω ↦ (X 0 ω : ℝ)) | MeasurableSpace.comap ψ ℐ] := by
    -- Proof comment: on each pulled-back invariant test set, move the path-space conditional
    -- expectation integral to `Q`, use the path-space owner theorem there, and push the zeroth
    -- coordinate integral back to `Ω`.
    refine ae_eq_condExp_of_forall_setIntegral_eq hmComap hX0_integrable
      (fun _ _ _ ↦ hPullbackCond_int.integrableOn) ?_ hPullbackCond_meas
    intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have ht_ambient : MeasurableSet t := hℐle t ht
    calc
      ∫ ω in ψ ⁻¹' t, Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] (ψ ω) ∂P =
          ∫ ξ in t, Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] ξ ∂Q := by
        simpa [Q, ψ] using
          (setIntegral_map ht_ambient hPathCond_meas hψ_aemeas).symm
      _ = ∫ ξ in t, (ξ 0 : ℝ) ∂Q := by
        exact
          @setIntegral_condExp
            (ℕ → ℤ) ℝ ℐ mPath Q (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) t
            _ _ _ hℐle hsf hEval0_int ht
      _ = ∫ ω in ψ ⁻¹' t, (X 0 ω : ℝ) ∂P := by
        simpa [Q, ψ] using
          (setIntegral_map ht_ambient hEval0_meas hψ_aemeas)
  have hPullbackZero :
      ∀ᵐ ω ∂P, Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] (ψ ω) = 0 := by
    -- Proof comment: once the pulled-back path-space conditional expectation is identified with
    -- the source conditional expectation, the centeredness hypothesis closes it immediately.
    exact hPullbackCondEq.trans hcentered
  have hZeroSet :
      MeasurableSet {ξ : ℕ → ℤ | Q[(fun η ↦ (η 0 : ℝ)) | ℐ] ξ = 0} := by
    let hCondStrong : StronglyMeasurable[ℐ] (Q[(fun η ↦ (η 0 : ℝ)) | ℐ]) :=
      stronglyMeasurable_condExp
    simpa using
      (hCondStrong.mono hℐle).measurableSet_eq_fun stronglyMeasurable_zero
  have hZeroAeQ :
      ∀ᵐ ξ ∂Q, Q[(fun η ↦ (η 0 : ℝ)) | ℐ] ξ = 0 := by
    have hZeroAeP :
        ∀ᵐ ω ∂P, ψ ω ∈ {ξ : ℕ → ℤ | Q[(fun η ↦ (η 0 : ℝ)) | ℐ] ξ = 0} := by
      simpa [Set.mem_setOf_eq] using hPullbackZero
    exact (ae_map_iff hψ_aemeas hZeroSet).2 hZeroAeP
  simpa [Q] using hZeroAeQ

/-- Helper for Theorem 20.20: the centered conditional-expectation hypothesis on `Ω` transports
to the path law of the stationary process once the canonical path map is measurable. -/
lemma pathLawEvalZeroCondExp_ae_eq_zero
    (hψ_meas : Measurable (fun ω ↦ fun n ↦ X n ω))
    (hX0_integrable : Integrable (fun ω ↦ (X 0 ω : ℝ)) P)
    (hcentered :
      P[(fun ω ↦ (X 0 ω : ℝ)) |
          MeasurableSpace.comap
            (fun ω ↦ fun n ↦ X n ω)
            (MeasurableSpace.invariants Stream'.tail)] =ᵐ[P] 0) :
    let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
    let Q : Measure (ℕ → ℤ) := Measure.map ψ P
    Q[(fun ξ ↦ (ξ 0 : ℝ)) |
        MeasurableSpace.invariants (Stream'.tail : (ℕ → ℤ) → (ℕ → ℤ))] =ᵐ[Q] 0 := by
  let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
  -- Proof comment: this is just the measurable-path-map transport lemma under the now-explicit
  -- hypothesis required for the pullback invariant `σ`-algebra to sit below the ambient one.
  simpa [ψ] using
    (pathLawEvalZeroCondExp_ae_eq_zero_of_measurablePathMap
      hX0_integrable hcentered hψ_meas)

/-- Helper for Theorem 20.20: sublinear partial sums force a sublinear range count for an
integer-valued path. -/
lemma rangeCountRatio_tendsto_zero_of_partialSumAverage_zero (ω : ℕ → ℤ)
    (hpartial :
      Tendsto (fun n : ℕ ↦ ((randomWalkPathPartialSum ω n : ℤ) : ℝ) / n) atTop
        (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (randomWalkPathRangeCount ω n : ℝ) / n) atTop (nhds 0) := by
  -- Proof comment: squeeze the range-count ratio between `0` and the interval-count bound coming
  -- from the prefix maximum, then invoke the prefix-maximum asymptotic lemma.
  have hprefix :
      Tendsto (fun n : ℕ ↦ (prefixMaxNatAbs ω n : ℝ) / n) atTop (nhds 0) :=
    prefixMaxNatAbsPartialSum_div_tendsto_zero_of_partialSumAverage_zero ω hpartial
  have hone :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper :
      Tendsto
        (fun n : ℕ ↦ 2 * ((prefixMaxNatAbs ω n : ℝ) / n) + (1 : ℝ) / n)
        atTop
        (nhds 0) := by
    simpa using (hprefix.const_mul 2).add hone
  refine squeeze_zero (fun n ↦ by positivity) ?_ hupper
  intro n
  have hcount :
      (randomWalkPathRangeCount ω n : ℝ) ≤ 2 * (prefixMaxNatAbs ω n : ℝ) + 1 := by
    exact_mod_cast randomWalkPathRangeCount_le_twicePrefixMaxNatAbs_add_one ω n
  calc
    (randomWalkPathRangeCount ω n : ℝ) / n ≤
        (2 * (prefixMaxNatAbs ω n : ℝ) + 1) / n := by
      exact div_le_div_of_nonneg_right hcount (by positivity)
    _ = 2 * ((prefixMaxNatAbs ω n : ℝ) / n) + (1 : ℝ) / n := by
      ring

/-- Helper for Theorem 20.20: if every shifted path revisits its current partial sum in the
future, then the partial sums return to `0` infinitely often. -/
lemma frequently_zero_of_revisitEveryShift (ω : ℕ → ℤ)
    (hrevisit :
      ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
        randomWalkPathPartialSum ω (n + j) = randomWalkPathPartialSum ω n) :
    Filter.Frequently
      (fun n : ℕ ↦ randomWalkPathPartialSum ω (n + 1) = 0) atTop := by
  have hreturnAfter :
      ∀ N : ℕ, ∃ m : ℕ, N < m ∧ randomWalkPathPartialSum ω m = 0 := by
    intro N
    induction N with
    | zero =>
        rcases hrevisit 0 with ⟨j, hjpos, hjEq⟩
        refine ⟨j, hjpos, ?_⟩
        simpa [randomWalkPathPartialSum_zero] using hjEq
    | succ N ih =>
        rcases ih with ⟨m, hmgt, hmzero⟩
        rcases hrevisit m with ⟨j, hjpos, hjEq⟩
        refine ⟨m + j, ?_, ?_⟩
        · omega
        · simpa [hmzero] using hjEq
  rw [frequently_atTop']
  intro a
  rcases hreturnAfter (a + 1) with ⟨m, hmgt, hmzero⟩
  refine ⟨m - 1, ?_, ?_⟩
  · omega
  · have hmpos : 0 < m := lt_trans (Nat.succ_pos a) hmgt
    have hidx : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
    simpa [hidx] using hmzero

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 20.20: pulling back the full-measure complement of the no-return event
along a shifted path map yields an almost-sure nonmembership statement on the original space. -/
lemma ae_shiftedPath_not_neverReturnsToOriginEvent
    {ψ : Ω → ℕ → ℤ} {Q : Measure (ℕ → ℤ)} (n : ℕ)
    (hNoReturnNull : Q neverReturnsToOriginEvent = 0)
    (hshiftLaw : Measure.map ((Stream'.tail^[n]) ∘ ψ) P = Q)
    (hshiftAemeas : AEMeasurable (((Stream'.tail^[n]) ∘ ψ)) P) :
    ∀ᵐ ω ∂P, ((Stream'.tail^[n]) (ψ ω)) ∉ neverReturnsToOriginEvent := by
  -- Proof comment: transport the complement event from the shifted path law back to `Ω` via
  -- `ae_map_iff`, avoiding any per-`n` measure computation on preimages.
  have hNotMemAeQ : ∀ᵐ ξ ∂Q, ξ ∉ neverReturnsToOriginEvent := by
    exact compl_mem_ae_iff.2 hNoReturnNull
  have hNotMemAeMap :
      ∀ᵐ ξ ∂Measure.map (((Stream'.tail^[n]) ∘ ψ)) P,
        ξ ∉ neverReturnsToOriginEvent := by
    simpa [hshiftLaw] using hNotMemAeQ
  exact
    (ae_map_iff hshiftAemeas measurableSet_neverReturnsToOriginEvent.compl).1 <| by
      simpa [Function.comp_apply] using hNotMemAeMap

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 20.20: if every shifted path avoids the no-return event almost surely,
then almost every sample path revisits its current partial sum after every time. -/
lemma ae_revisitCurrentPartialSum_everyShift
    {ψ : Ω → ℕ → ℤ}
    (hshifted :
      ∀ n : ℕ,
        ∀ᵐ ω ∂P, ((Stream'.tail^[n]) (ψ ω)) ∉ neverReturnsToOriginEvent) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
      randomWalkPathPartialSum (ψ ω) (n + j) = randomWalkPathPartialSum (ψ ω) n := by
  -- Proof comment: bundle the per-shift full-measure statements with `ae_all_iff`, then rewrite
  -- the path-space event using the Chapter 20.19 iterate-tail characterization.
  refine ae_all_iff.2 fun n ↦ ?_
  filter_upwards [hshifted n] with ω hω
  have hnotNever : (Stream'.tail^[n]) (ψ ω) ∉ neverReturnsToOriginEvent := hω
  rw [mem_neverReturnsToOriginEvent_iterateTail_iff] at hnotNever
  push Not at hnotNever
  simpa using hnotNever

/-- Helper for Theorem 20.20: an almost-sure universal revisit property admits a measurable
full-measure subset on which the pointwise revisit statement holds. -/
lemma measurableFullMeasureSubset_of_aeRevisitEveryShift
    {ψ : Ω → ℕ → ℤ}
    (hRevisitAe :
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
        randomWalkPathPartialSum (ψ ω) (n + j) = randomWalkPathPartialSum (ψ ω) n) :
    ∃ B : Set Ω, MeasurableSet B ∧ P B = 1 ∧
      B ⊆
        {ω | ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
          randomWalkPathPartialSum (ψ ω) (n + j) = randomWalkPathPartialSum (ψ ω) n} := by
  let C : Set Ω := {ω | ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
    randomWalkPathPartialSum (ψ ω) (n + j) = randomWalkPathPartialSum (ψ ω) n}
  have hCae : C ∈ ae P := by
    -- Proof comment: the raw universal revisit set is exactly the almost-sure property encoded
    -- by `hRevisitAe`.
    simpa [C] using hRevisitAe
  have hCcomplZero : P Cᶜ = 0 := by
    have hCcomplComplAe : Cᶜᶜ ∈ ae P := by
      simpa using hCae
    exact compl_mem_ae_iff.1 hCcomplComplAe
  obtain ⟨N, hCcomplSubset, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hCcomplZero
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · -- Proof comment: the complement of a measurable null set has probability one.
    exact (mem_ae_iff_prob_eq_one hNmeas.compl).1 (compl_mem_ae_iff.2 hNzero)
  · -- Proof comment: outside the measurable exceptional superset `N`, one cannot lie in `Cᶜ`.
    intro ω hω
    have hωnotN : ω ∉ N := by
      simpa using hω
    by_contra hωC
    have hωN : ω ∈ N := hCcomplSubset hωC
    exact hωnotN hωN

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 20.20: a path that revisits each current partial sum later must return to
`0` infinitely often. -/
lemma revisitEveryShift_subset_partialSumsReturnToZeroInfinitelyOften
    (ω : Ω)
    (hrevisit :
      ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
        randomWalkPathPartialSum (fun k ↦ X k ω) (n + j) =
          randomWalkPathPartialSum (fun k ↦ X k ω) n) :
    ω ∈ partialSumsReturnToZeroInfinitelyOften X := by
  -- Proof comment: this is the deterministic return-time recursion already encoded in
  -- `frequently_zero_of_revisitEveryShift`.
  simpa [partialSumsReturnToZeroInfinitelyOften] using
    (frequently_zero_of_revisitEveryShift (fun k ↦ X k ω) hrevisit)

/- Theorem 20.20 is `source-facing`: it stays on an arbitrary stationary process `X` on `Ω`.
Its canonical owner for the textbook invariant `σ`-algebra `𝒯` is still the shift-invariant
`σ`-algebra `MeasurableSpace.invariants Stream'.tail` on path space. The theorem therefore uses
the thin `bridge/view` obtained by pulling that owner back along the canonical path map
`ω ↦ (n ↦ X n ω)`, rather than introducing a free ambient `σ`-algebra parameter. -/

-- Proof sketch: pull back the canonical shift-invariant `σ`-algebra from path space along the
-- path map `ω ↦ (n ↦ X n ω)`. Stationarity identifies each coordinate `X n` with `X 0` in law, so
-- integrability of `X 0` supplies the coordinatewise integrability needed to apply the
-- ergodic-theoretic recurrence criterion from the previous theorem to the induced stationary path
-- law. Then transfer the resulting almost-sure statement back to the original process.
/-- Theorem 20.20: if `X` is an integer-valued stationary process, the sample-path map
`ω ↦ (n ↦ X n ω)` is measurable, the real-valued process `(fun ω ↦ (X 0 ω : ℝ))` is integrable,
and the first coordinate has conditional expectation `0` with respect to the pullback along that
path map of the invariant `σ`-algebra `MeasurableSpace.invariants Stream'.tail` of the one-sided
shift, then the partial sums return to `0` infinitely often with probability `1`. Stationarity
makes the remaining coordinates integrable automatically by identical distribution. In the
`0`-based indexing used here, the partial sum at time `n + 1` is `∑_{k < n + 1} X k`. -/
theorem stationary_integer_process_partialSums_returnToZero_infinitelyOften
    (hstationary : IsStationaryProcess X P)
    (hpath_meas : Measurable (fun ω ↦ fun n ↦ X n ω))
    (hX0_integrable : Integrable (fun ω ↦ (X 0 ω : ℝ)) P)
    (hcentered :
    P[(fun ω ↦ (X 0 ω : ℝ)) |
          MeasurableSpace.comap
            (fun ω ↦ fun n ↦ X n ω)
    (MeasurableSpace.invariants Stream'.tail)] =ᵐ[P] 0) :
    P (partialSumsReturnToZeroInfinitelyOften X) = 1 := by
  classical
  let ψ : Ω → (ℕ → ℤ) := fun ω n ↦ X n ω
  let Q : Measure (ℕ → ℤ) := Measure.map ψ P
  let mPath : MeasurableSpace (ℕ → ℤ) := inferInstanceAs (MeasurableSpace (ℕ → ℤ))
  letI : IsProbabilityMeasure Q := by
    exact
      Measure.isProbabilityMeasure_map
        (by simpa [ψ] using (hstationary.identDistrib 0).aemeasurable_snd)
  letI : IsFiniteMeasure Q := by infer_instance
  have hℐle : ℐ ≤ mPath :=
    MeasurableSpace.invariants_le (Stream'.tail : (ℕ → ℤ) → (ℕ → ℤ))
  have hsf : SigmaFinite (Q.trim hℐle) := by
    letI : IsFiniteMeasure (Q.trim hℐle) := by infer_instance
    exact IsFiniteMeasure.toSigmaFinite (Q.trim hℐle)
  haveI : SigmaFinite (Q.trim hℐle) := hsf
  have htailMeas : Measurable (Stream'.tail : Stream' ℤ → Stream' ℤ) := by
    -- Proof comment: the one-step shift is coordinatewise measurable on the path space.
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))
  have hpathStationary : IsStationaryProcess Function.eval Q := by
    -- Proof comment: the pushforward path law inherits stationarity from the original process.
    simpa [ψ, Q] using
      (canonicalPathLaw_stationary hstationary)
  have hshiftLaw :
      ∀ n : ℕ, Measure.map ((Stream'.tail^[n]) ∘ ψ) P = Q := by
    intro n
    -- Proof comment: after `n` shifts, the path map records the shifted process
    -- `t ↦ X (n + t)`, whose law equals the original one by stationarity.
    calc
      Measure.map ((Stream'.tail^[n]) ∘ ψ) P = Measure.map (fun ω t ↦ X (n + t) ω) P := by
        congr 1
        ext ω t
        simpa [Function.comp_apply, ψ] using (iterateTail_apply (ψ ω) n t)
      _ = Q := by
        simpa [ψ, Q] using (hstationary.identDistrib n).map_eq
  have hNoReturnNull : Q neverReturnsToOriginEvent = 0 := by
    let A : Set (ℕ → ℤ) := neverReturnsToOriginEvent
    have htailPresQ : MeasurePreserving Stream'.tail Q Q :=
      (canonical_process_stationary_iff_measurePreserving_tail Q).mp hpathStationary
    have hQcentered :
        Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] =ᵐ[Q] 0 := by
      -- Proof comment: the source conditional-expectation hypothesis survives pushforward to
      -- the stationary path law.
      simpa [ψ, Q] using
        (pathLawEvalZeroCondExp_ae_eq_zero_of_measurablePathMap
          hX0_integrable hcentered hpath_meas)
    have hEval0_meas :
        AEStronglyMeasurable (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) Q := by
      exact
        (((measurable_of_countable ((↑) : ℤ → ℝ)).comp
            (measurable_pi_apply 0)).aestronglyMeasurable)
    have hEval0_int : Integrable (fun ξ : ℕ → ℤ ↦ (ξ 0 : ℝ)) Q := by
      refine (integrable_map_measure hEval0_meas
        (by simpa [ψ] using (hstationary.identDistrib 0).aemeasurable_snd)).2 ?_
      simpa [Function.comp, ψ] using hX0_integrable
    have hPartialZero :
        ∀ᵐ ξ ∂Q,
          Tendsto (fun n : ℕ ↦ ((randomWalkPathPartialSum ξ n : ℤ) : ℝ) / n) atTop
            (nhds 0) := by
      have hBirkhoff :
          ∀ᵐ ξ ∂Q,
            Tendsto
              (fun n : ℕ ↦
                birkhoffAverage ℝ Stream'.tail (fun η : ℕ → ℤ ↦ (η 0 : ℝ)) n ξ)
              atTop
              (nhds ((Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ]) ξ)) :=
        @birkhoffAverage_tendsto_ae_condExp_invariants
          (ℕ → ℤ) inferInstance Q inferInstance Stream'.tail
          (fun η : ℕ → ℤ ↦ (η 0 : ℝ)) htailPresQ hEval0_int
      filter_upwards [hBirkhoff, hQcentered] with ξ hξ hξcentered
      have hξcentered' : Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ] ξ = 0 := by
        simpa using hξcentered
      have hξ' :
          Tendsto
            (fun n : ℕ ↦ ((randomWalkPathPartialSum ξ n : ℤ) : ℝ) / n)
            atTop
            (nhds ((Q[(fun ξ ↦ (ξ 0 : ℝ)) | ℐ]) ξ)) := by
        refine hξ.congr' ?_
        exact Filter.Eventually.of_forall fun n ↦ by
          simpa using (birkhoffAverage_evalZero_eq_partialSumDiv ξ n)
      convert hξ' using 1
      simp [hξcentered']
    have hRangeZero :
        ∀ᵐ ξ ∂Q,
          Tendsto (fun n : ℕ ↦ (randomWalkPathRangeCount ξ n : ℝ) / n) atTop
            (nhds 0) := by
      filter_upwards [hPartialZero] with ξ hξ
      exact rangeCountRatio_tendsto_zero_of_partialSumAverage_zero ξ hξ
    have hCondProbZero :
        (Q⟦A | ℐ⟧) =ᵐ[Q] 0 := by
      have hRangeCond :
          ∀ᵐ ξ ∂Q,
            Tendsto (fun n : ℕ ↦ (randomWalkPathRangeCount ξ n : ℝ) / n) atTop
              (nhds ((Q⟦A | ℐ⟧) ξ)) :=
        randomWalkPathRangeCount_tendsto_ae_condProb_invariants Q hpathStationary
      filter_upwards [hRangeCond, hRangeZero] with ξ hξCond hξZero
      exact tendsto_nhds_unique hξCond hξZero
    have hIntegralZero :
        ∫ ξ, (Q⟦A | ℐ⟧) ξ ∂Q = 0 := by
      calc
        ∫ ξ, (Q⟦A | ℐ⟧) ξ ∂Q = ∫ ξ, (0 : ℝ) ∂Q := by
          exact integral_congr_ae hCondProbZero
        _ = 0 := by simp
    have hTotalProb :
        ∫ ξ, (Q⟦A | ℐ⟧) ξ ∂Q = Q.real A := by
      calc
        ∫ ξ, (Q⟦A | ℐ⟧) ξ ∂Q = ∫ ξ, Set.indicator A (fun _ ↦ (1 : ℝ)) ξ ∂Q := by
          exact
            (@integral_condExp
              (ℕ → ℤ) ℝ ℐ mPath Q (Set.indicator A (fun _ ↦ (1 : ℝ))) _ _ _ hℐle hsf)
        _ = Q.real A := by
          simpa [A] using
            (integral_indicator_one measurableSet_neverReturnsToOriginEvent)
    have hNoReturnReal : Q.real A = 0 := hTotalProb.symm.trans hIntegralZero
    rw [Measure.real_def, ENNReal.toReal_eq_zero_iff] at hNoReturnReal
    exact hNoReturnReal.resolve_right (by simp)
  have hShiftedNotNever :
      ∀ n : ℕ, ∀ᵐ ω ∂P, ((Stream'.tail^[n]) (ψ ω)) ∉ neverReturnsToOriginEvent := by
    intro n
    -- Proof comment: each shifted path has the same law `Q`, so the full-measure complement of
    -- the no-return event transfers back along the shifted path map.
    exact
      ae_shiftedPath_not_neverReturnsToOriginEvent
        n hNoReturnNull (hshiftLaw n)
        ((htailMeas.iterate n).aemeasurable.comp_aemeasurable
          (by simpa [ψ] using (hstationary.identDistrib 0).aemeasurable_snd))
  have hRevisitAe :
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ j : ℕ, 0 < j ∧
        randomWalkPathPartialSum (fun k ↦ X k ω) (n + j) =
          randomWalkPathPartialSum (fun k ↦ X k ω) n := by
    -- Route correction: the old proof pushed null sets through a countable family `bad/N/B`.
    -- The new route bundles the shifted complements at the `ae` level first and only then does
    -- one measurable full-measure cleanup.
    simpa [ψ] using
      (ae_revisitCurrentPartialSum_everyShift hShiftedNotNever)
  obtain ⟨B, hBmeas, hBprob, hBsubsetRevisit⟩ :=
    measurableFullMeasureSubset_of_aeRevisitEveryShift hRevisitAe
  have hBsubset : B ⊆ partialSumsReturnToZeroInfinitelyOften X := by
    intro ω hω
    -- Proof comment: on the measurable full-measure set, the pointwise revisit property is now
    -- available directly, so the deterministic return lemma closes the target event.
    exact
      revisitEveryShift_subset_partialSumsReturnToZeroInfinitelyOften
        ω (hBsubsetRevisit hω)
  have hLower : 1 ≤ P (partialSumsReturnToZeroInfinitelyOften X) := by
    calc
      1 = P B := hBprob.symm
      _ ≤ P (partialSumsReturnToZeroInfinitelyOften X) := P.mono hBsubset
  have hUpper : P (partialSumsReturnToZeroInfinitelyOften X) ≤ 1 := by
    have hmono : P (partialSumsReturnToZeroInfinitelyOften X) ≤ P Set.univ :=
      measure_mono (by intro ω hω; exact Set.mem_univ ω)
    simpa using hmono
  exact le_antisymm hUpper hLower
