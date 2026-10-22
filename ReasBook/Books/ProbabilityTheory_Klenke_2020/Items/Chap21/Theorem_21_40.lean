/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

universe u

local notation "PathSpace" => BrownianPathSpace

-- Use the canonical Borel measurable structure on the continuous path space `C([0, ∞), ℝ)`.
local instance theorem2140PathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _

-- The local measurable structure on `PathSpace` is its Borel `σ`-algebra.
local instance theorem2140PathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

-- Open sets in the path space are measurable for the canonical Borel structure.
local instance theorem2140PathSpaceOpensMeasurableSpace : OpensMeasurableSpace PathSpace := by
  infer_instance

/-- Helper for Theorem 21.40: the admissible oscillation values on `[0, N]` at mesh `δ`. -/
def compactIntervalOscillationValues (N : ℕ) (ω : PathSpace) (δ : NNReal) : Set NNReal :=
  {r | ∃ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) t ≤ δ ∧ r = ‖ω s - ω t‖₊}

/-- Helper for Theorem 21.40: the maximal oscillation of one path on `[0, N]` at mesh `δ`. -/
def compactIntervalOscillation (N : ℕ) (ω : PathSpace) (δ : NNReal) : NNReal :=
  sSup (compactIntervalOscillationValues N ω δ)

/-- Helper for Theorem 21.40: the admissible oscillation values form a bounded-above set. -/
lemma compactIntervalOscillationValues_bddAbove (N : ℕ) (ω : PathSpace) (δ : NNReal) :
    BddAbove (compactIntervalOscillationValues N ω δ) := by
  let admissiblePairs : Set (Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N) :=
    {p | dist (p.1 : NNReal) p.2 ≤ δ}
  let oscillationValue : Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N → NNReal :=
    fun p ↦ ‖ω p.1 - ω p.2‖₊
  have hClosedPairs : IsClosed admissiblePairs := by
    -- Proof comment: the mesh condition is the inverse image of the closed ray `(-∞, δ]`.
    have hDistCont :
        Continuous fun p : Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N ↦
          dist (p.1 : NNReal) p.2 :=
      continuous_fst.subtype_val.dist continuous_snd.subtype_val
    simpa [admissiblePairs] using isClosed_le hDistCont continuous_const
  have hCompactPairs : IsCompact admissiblePairs := by
    -- Proof comment: the admissible-pair set is closed inside the compact square interval.
    simpa [admissiblePairs] using
      (isCompact_univ : IsCompact
        (Set.univ : Set (Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N))).inter_right
        hClosedPairs
  have hCompactImage : IsCompact (oscillationValue '' admissiblePairs) := by
    -- Proof comment: the oscillation value depends continuously on the chosen pair.
    refine hCompactPairs.image ?_
    continuity
  have hImageEq :
      oscillationValue '' admissiblePairs = compactIntervalOscillationValues N ω δ := by
    ext r
    constructor
    · rintro ⟨⟨s, t⟩, hp, rfl⟩
      exact ⟨s, t, hp, rfl⟩
    · rintro ⟨s, t, hst, rfl⟩
      exact ⟨⟨s, t⟩, hst, rfl⟩
  simpa [hImageEq] using hCompactImage.bddAbove

/-- Helper for Theorem 21.40: pointwise control on all admissible pairs bounds the corresponding
compact-interval oscillation. -/
lemma compactIntervalOscillation_le_of_forall (N : ℕ) (ω : PathSpace) (δ η : NNReal)
    (hη : ∀ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) t ≤ δ → ‖ω s - ω t‖₊ ≤ η) :
    compactIntervalOscillation N ω δ ≤ η := by
  -- Proof comment: every admissible oscillation value is bounded by `η`, hence so is the supremum.
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨⟨0, by simp⟩, ⟨0, by simp⟩, by simp, by simp⟩
  · intro r hr
    rcases hr with ⟨s, t, hst, rfl⟩
    exact hη s t hst

/-- Helper for Theorem 21.40: each admissible increment on `[0, N]` is bounded by the maximal
oscillation at the same mesh. -/
lemma nnnorm_sub_le_compactIntervalOscillation (N : ℕ) (ω : PathSpace) (δ : NNReal)
    (s t : Set.Icc (0 : NNReal) N) (hst : dist (s : NNReal) t ≤ δ) :
    ‖ω s - ω t‖₊ ≤ compactIntervalOscillation N ω δ := by
  -- Proof comment: the chosen increment is one of the values entering the supremum.
  refine le_csSup (compactIntervalOscillationValues_bddAbove N ω δ) ?_
  exact ⟨s, t, hst, rfl⟩

/-- Helper for Theorem 21.40: a real norm bound yields the corresponding `NNReal` norm bound. -/
lemma nnnorm_le_of_norm_le {x : ℝ} {η : NNReal} (h : ‖x‖ ≤ η) : ‖x‖₊ ≤ η := by
  exact_mod_cast h

/-- Tightness of the family of initial-value laws attached to a family of path laws. -/
def initial_value_laws_tight {ι : Type u} (P : ι → ProbabilityMeasure PathSpace) : Prop :=
  IsTightMeasureSet (Set.range fun i ↦
    (((P i).map (continuous_eval_const (0 : NNReal)).aemeasurable : ProbabilityMeasure ℝ) :
      Measure ℝ))

/-- Tightness of the initial-value laws is equivalent to the textbook tail estimate
`P_i {|ω(0)| > K} ≤ ε` uniformly in `i`. -/
-- Proof sketch: apply the characterization of `IsTightMeasureSet` by compact sets to the family
-- of pushforwards on `ℝ`, replace compact sets by large closed intervals `[-K, K]`, and then use
-- `ProbabilityMeasure.map_apply` for evaluation at `0` to rewrite the complements as the events
-- `{ω | K < |ω 0|}`.
theorem initial_value_laws_tight_iff {ι : Type u} (P : ι → ProbabilityMeasure PathSpace) :
    initial_value_laws_tight P ↔
      ∀ ε : NNReal, 0 < ε → ∃ K : NNReal, 0 < K ∧ ∀ i, P i {ω | K < |ω 0|} ≤ ε := by
  let evalZero : PathSpace → ℝ := fun ω ↦ ω 0
  have hEvalMeas (i : ι) : AEMeasurable evalZero (P i) :=
    (continuous_eval_const (0 : NNReal)).measurable.aemeasurable
  have hTailMeas (K : NNReal) : MeasurableSet {x : ℝ | K < |x|} := by
    exact measurableSet_Ioi.preimage measurable_abs
  constructor
  · intro hTight
    rw [initial_value_laws_tight,
      MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hTight
    intro ε hε
    obtain ⟨A, hACompact, hACompl⟩ := hTight (ε : ℝ≥0∞) (by exact_mod_cast hε)
    -- Enlarge the compact witness to a closed ball centered at `0`.
    obtain ⟨R, hR⟩ := hACompact.isBounded.subset_closedBall (0 : ℝ)
    let K : NNReal := ⟨max R 1, by positivity⟩
    refine ⟨K, show 0 < K by
      change (0 : ℝ) < max R 1
      positivity, ?_⟩
    intro i
    have hA_sub_ball : A ⊆ Metric.closedBall (0 : ℝ) K := by
      intro x hx
      have hxR : x ∈ Metric.closedBall (0 : ℝ) R := hR hx
      simp [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] at hxR ⊢
      exact le_trans hxR (le_max_left _ _)
    have hTail_sub_compl : {x : ℝ | K < |x|} ⊆ Aᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxA
      have hxBall : x ∈ Metric.closedBall (0 : ℝ) K := hA_sub_ball hxA
      have hxNotBall : x ∉ Metric.closedBall (0 : ℝ) K := by
        simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, not_le] using hx
      exact hxNotBall hxBall
    -- Rewrite the pushforward tail event back to the path-space event at time `0`.
    have hTailBound :
        (((P i).map (hEvalMeas i) : ProbabilityMeasure ℝ) : Measure ℝ) {x : ℝ | K < |x|}
          ≤ (ε : ℝ≥0∞) := calc
            (((P i).map (hEvalMeas i) : ProbabilityMeasure ℝ) : Measure ℝ) {x : ℝ | K < |x|}
                ≤ (((P i).map (hEvalMeas i) : ProbabilityMeasure ℝ) : Measure ℝ) Aᶜ := by
                    exact measure_mono hTail_sub_compl
            _ ≤ (ε : ℝ≥0∞) := hACompl _ ⟨i, rfl⟩
    exact ENNReal.coe_le_coe.mp <| by
      simpa [evalZero] using
        ((MeasureTheory.ProbabilityMeasure.map_apply' (P i) (hEvalMeas i) (hTailMeas K)).symm.trans_le
          hTailBound)
  · intro hTail
    rw [initial_value_laws_tight,
      MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεTop : ε = ∞
    · refine ⟨∅, isCompact_empty, ?_⟩
      intro μ hμ
      simp [hεTop]
    · lift ε to NNReal using hεTop with ε'
      have hε' : 0 < ε' := by exact_mod_cast hε
      obtain ⟨K, hKPos, hKTail⟩ := hTail ε' hε'
      refine ⟨Metric.closedBall (0 : ℝ) K, isCompact_closedBall (0 : ℝ) K, ?_⟩
      intro μ hμ
      rcases hμ with ⟨i, rfl⟩
      -- The complement of the closed ball is exactly the textbook tail event.
      have hSet :
          (Metric.closedBall (0 : ℝ) K)ᶜ = {x : ℝ | K < |x|} := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, not_le]
      have hBallCompl :
          (((P i).map (hEvalMeas i) : ProbabilityMeasure ℝ) : Measure ℝ)
              (Metric.closedBall (0 : ℝ) K)ᶜ =
            (P i {ω | K < |ω 0|} : ℝ≥0∞) := by
        rw [hSet]
        simpa [evalZero] using
          (MeasureTheory.ProbabilityMeasure.map_apply' (P i) (hEvalMeas i) (hTailMeas K))
      rw [hBallCompl]
      exact ENNReal.coe_le_coe.mpr (hKTail i)

/-- Uniform control of compact-interval oscillation probabilities for a family of path laws. -/
def uniformly_small_compact_interval_path_oscillation_probabilities {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) : Prop :=
  ∀ η ε : NNReal, 0 < η → 0 < ε → ∀ N : ℕ,
    ∃ δ : NNReal, 0 < δ ∧
      ∀ i, P i {ω | η < compactIntervalOscillation N ω δ} ≤ ε

/-- Helper for Theorem 21.40: the dyadic Arzelà--Ascoli control set used in the reverse
implication. -/
def ascoliControlSet (K0 : NNReal) (δ : ℕ → ℕ → NNReal) : Set PathSpace :=
  {ω | |ω 0| ≤ K0 ∧ ∀ N k, compactIntervalOscillation N ω (δ N k) ≤ ((1 / 2 : NNReal) ^ k)}

/-- Helper for Theorem 21.40: a compact set of paths has uniformly bounded values at time `0`. -/
lemma exists_evalZeroBound_of_isCompact (K : Set PathSpace) (hK : IsCompact K) :
    ∃ K0 : NNReal, 0 < K0 ∧ ∀ ω ∈ K, |ω 0| ≤ K0 := by
  -- Proof comment: evaluate the compact family at time `0` and bound the compact image in `ℝ`
  -- by a positive closed ball centered at `0`.
  have hImageCompact : IsCompact ((fun ω : PathSpace ↦ ω 0) '' K) := by
    simpa using hK.image (continuous_eval_const (0 : NNReal))
  obtain ⟨R, hRPos, hR⟩ := hImageCompact.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  refine ⟨⟨R, hRPos.le⟩, hRPos, ?_⟩
  intro ω hω
  have hωImage : ω 0 ∈ Metric.closedBall (0 : ℝ) R := by
    exact hR ⟨ω, hω, rfl⟩
  simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hωImage

/-- Helper for Theorem 21.40: every compact subset of `NNReal` is contained in some interval
`[0, N]`. -/
lemma exists_nat_Icc_superset_of_isCompact {K : Set NNReal} (hK : IsCompact K) :
    ∃ N : ℕ, K ⊆ Set.Icc (0 : NNReal) N := by
  -- Proof comment: compact subsets of the ordered space `NNReal` are bounded above, so one
  -- ceiling bound gives a single compact interval containing the whole set.
  rcases hK.bddAbove with ⟨b, hb⟩
  refine ⟨Nat.ceil (b : ℝ), ?_⟩
  intro x hx
  refine ⟨x.2, ?_⟩
  change (x : ℝ) ≤ Nat.ceil (b : ℝ)
  exact le_trans (by exact_mod_cast hb hx) (Nat.le_ceil (b : ℝ))

/-- Helper for Theorem 21.40: consecutive points in the linear subdivision differ by exactly one
mesh step. -/
lemma dist_mul_succ_eq_step (k : ℕ) (step : NNReal) :
    dist ((k : NNReal) * step) ((((k + 1 : ℕ) : NNReal) * step)) = step := by
  -- Proof comment: swap the endpoints so the absolute value sees a nonnegative difference, then
  -- simplify the arithmetic of one extra mesh step.
  rw [dist_comm, NNReal.dist_eq, abs_of_nonneg]
  · simp [Nat.cast_add, add_mul, one_mul]
  · change 0 ≤ ((((k + 1 : ℕ) : NNReal) * step : NNReal) : ℝ) -
        ((((k : NNReal) * step : NNReal) : ℝ))
    simp [Nat.cast_add, add_mul, one_mul]

/-- Helper for Theorem 21.40: every `t ∈ [0, N]` admits a finite subdivision from `0` to `t`
whose successive mesh sizes are all `< δ`. -/
lemma existsSubdivisionChain_zero_to (N : ℕ) (t δ : NNReal)
    (ht : t ∈ Set.Icc (0 : NNReal) N) (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ u : ℕ → Set.Icc (0 : NNReal) N,
      (u 0 : NNReal) = 0 ∧
      (u m : NNReal) = t ∧
      ∀ k < m, dist (u k : NNReal) (u (k + 1) : NNReal) < δ := by
  let n : ℕ := Nat.ceil ((t : ℝ) / δ)
  let m : ℕ := n + 1
  let step : NNReal := t / m
  have hm_ne : (m : NNReal) ≠ 0 := by
    dsimp [m]
    exact_mod_cast Nat.succ_ne_zero n
  have hm_mul_step : (m : NNReal) * step = t := by
    -- Proof comment: the chosen mesh is the exact linear subdivision step `t / m`.
    simpa [step, mul_comm] using (div_mul_cancel₀ t hm_ne)
  have hcover : (t : ℝ) ≤ n * δ := by
    have hdiv : (t : ℝ) / δ ≤ n := Nat.le_ceil ((t : ℝ) / δ)
    exact (div_le_iff₀ (show 0 < (δ : ℝ) by exact hδ)).mp hdiv
  have hstep_lt : step < δ := by
    -- Proof comment: using one more segment than `Nat.ceil (t / δ)` forces the subdivision mesh
    -- to be strictly smaller than `δ`.
    change (t : ℝ) / (m : ℝ) < (δ : ℝ)
    have hm_pos : 0 < (m : ℝ) := by
      dsimp [m]
      positivity
    have hδreal : 0 < (δ : ℝ) := hδ
    refine (div_lt_iff₀ hm_pos).2 ?_
    have hmul_lt : (n : ℝ) * δ < (n + 1 : ℝ) * δ := by
      have hnlt : (n : ℝ) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      exact mul_lt_mul_of_pos_right hnlt hδreal
    exact (lt_of_le_of_lt hcover hmul_lt).trans_eq (by
      simp [m, mul_comm])
  let u : ℕ → Set.Icc (0 : NNReal) N := fun k ↦
    ⟨(min k m : NNReal) * step, by
      refine ⟨by positivity, ?_⟩
      calc
        (min k m : NNReal) * step ≤ (m : NNReal) * step := by
          gcongr
          exact_mod_cast Nat.min_le_right k m
        _ = t := hm_mul_step
        _ ≤ N := ht.2⟩
  refine ⟨m, u, ?_, ?_, ?_⟩
  · -- Proof comment: the subdivision starts at the left endpoint `0`.
    simp [u]
  · -- Proof comment: the final subdivision point lands exactly at `t`.
    simpa [u, hm_mul_step]
  · -- Proof comment: consecutive subdivision points differ by exactly one mesh step.
    intro k hk
    have hdist_lt :
        dist ((min k m : NNReal) * step) ((min (k + 1) m : NNReal) * step) < δ := by
      have hkmin : min k m = k := Nat.min_eq_left (Nat.le_of_lt hk)
      have hk1min : min (k + 1) m = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
      have hkmin' : (min k m : NNReal) = k := by
        exact_mod_cast hkmin
      have hk1min' : (min (k + 1) m : NNReal) = k + 1 := by
        exact_mod_cast hk1min
      have hdist_eq : dist ((k : NNReal) * step) ((k + 1 : NNReal) * step) = step := by
        simpa [Nat.cast_add, add_mul, one_mul] using dist_mul_succ_eq_step k step
      have hdist_min :
          dist ((min k m : NNReal) * step) ((min (k + 1) m : NNReal) * step) = step := by
        simpa [hkmin', hk1min'] using hdist_eq
      rw [hdist_min]
      exact hstep_lt
    simpa [u] using hdist_lt

/-- Helper for Theorem 21.40: bounded time-zero evaluations plus uniform equicontinuity on
`[0, N]` imply bounded evaluations at each fixed `t ∈ [0, N]`. -/
lemma pointwiseBoundedEval_of_boundedEvalZero_and_uniformEquicontinuousOnIcc
    (A : Set PathSpace) (N : ℕ)
    (h0 : Bornology.IsBounded ((fun ω : PathSpace ↦ ω 0) '' A))
    (hEq : UniformEquicontinuousOn ((↑) : A → NNReal → ℝ) (Set.Icc (0 : NNReal) N))
    {t : NNReal} (ht : t ∈ Set.Icc (0 : NNReal) N) :
    Bornology.IsBounded ((fun ω : PathSpace ↦ ω t) '' A) := by
  obtain ⟨R, hR⟩ := h0.subset_closedBall (0 : ℝ)
  have hEqMetric := hEq
  rw [← uniformEquicontinuous_restrict_iff ((↑) : A → NNReal → ℝ)] at hEqMetric
  rw [Metric.uniformEquicontinuous_iff] at hEqMetric
  obtain ⟨δ₀, hδ₀Pos, hδ₀Small⟩ := hEqMetric 1 zero_lt_one
  let δ : NNReal := ⟨δ₀ / 2, by positivity⟩
  have hδPos : 0 < δ := by
    change 0 < δ₀ / 2
    positivity
  have hδLt : (δ : ℝ) < δ₀ := by
    change δ₀ / 2 < δ₀
    nlinarith
  rcases existsSubdivisionChain_zero_to N t δ ht hδPos with ⟨m, u, hu0, hum, huStep⟩
  -- Proof comment: a single time-zero bound and the common mesh bound telescope along the
  -- subdivision chain to control every `ω t`.
  have hImageSubset : ((fun ω : PathSpace ↦ ω t) '' A) ⊆ Metric.closedBall (0 : ℝ) (R + m) := by
    rintro y ⟨ω, hω, rfl⟩
    have hω0Ball : ω 0 ∈ Metric.closedBall (0 : ℝ) R := hR ⟨ω, hω, rfl⟩
    have hωBound : ∀ n ≤ m, |ω (u n)| ≤ R + n := by
      intro n hn
      induction n with
      | zero =>
          -- Proof comment: the first subdivision node is exactly `0`, so the given time-zero bound
          -- already controls the base case.
          simpa [hu0, Metric.mem_closedBall, Real.dist_eq] using hω0Ball
      | succ n ih =>
          have hnle : n ≤ m := Nat.le_of_succ_le hn
          have hprev : |ω (u n)| ≤ R + n := ih hnle
          have hmesh : dist (u n : NNReal) (u (n + 1) : NNReal) < δ :=
            huStep n (Nat.lt_of_succ_le hn)
          have hinc : |ω (u (n + 1)) - ω (u n)| < 1 := by
            have hdist := hδ₀Small (u n) (u (n + 1)) (lt_trans hmesh hδLt) ⟨ω, hω⟩
            simpa [Real.dist_eq, abs_sub_comm] using hdist
          have hsplit : ω (u (n + 1)) = (ω (u (n + 1)) - ω (u n)) + ω (u n) := by
            ring
          rw [hsplit]
          calc
            |(ω (u (n + 1)) - ω (u n)) + ω (u n)| ≤
                |ω (u (n + 1)) - ω (u n)| + |ω (u n)| := abs_add_le _ _
            _ ≤ 1 + (R + n) := by linarith
            _ = R + ↑n + 1 := by ring
            _ = R + ↑(n + 1) := by
              simp [Nat.cast_add, add_assoc]
    have hωt : |ω t| ≤ R + m := by
      simpa [hum] using hωBound m le_rfl
    simpa [Metric.mem_closedBall, Real.dist_eq] using hωt
  exact Metric.isBounded_closedBall.subset hImageSubset

/-- Helper for Theorem 21.40: compact convergence embeds `PathSpace` as a closed subset of the
ambient `UniformOnFun` space. -/
lemma pathSpace_isClosedEmbedding_toUniformOnFun :
    Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set NNReal | IsCompact K} ∘
        ((↑) : PathSpace → NNReal → ℝ)) := by
  -- Proof comment: use the compact-convergence embedding together with the closedness of the set
  -- of continuous functions inside `UniformOnFun`.
  refine ⟨?_, ?_⟩
  · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp] using
      (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        (α := NNReal) (β := ℝ)).isEmbedding
  · change
      IsClosed
        (Set.range
          (ContinuousMap.toUniformOnFunIsCompact :
            PathSpace → UniformOnFun NNReal ℝ {K : Set NNReal | IsCompact K}))
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    change
      IsClosed
        {f : UniformOnFun NNReal ℝ {K : Set NNReal | IsCompact K} |
          Continuous (UniformOnFun.toFun {K : Set NNReal | IsCompact K} f)}
    exact UniformOnFun.isClosed_setOf_continuous
      (𝔖 := {K : Set NNReal | IsCompact K}) (β := ℝ)
      CompactlyCoherentSpace.isCoherentWith

/-- Helper for Theorem 21.40: the dyadic control set is uniformly equicontinuous on each compact
interval. -/
lemma ascoliControlSet_uniformEquicontinuousOnIcc (K0 : NNReal) (δ : ℕ → ℕ → NNReal)
    (hδ : ∀ N k, 0 < δ N k) (N : ℕ) :
    UniformEquicontinuousOn ((↑) : ascoliControlSet K0 δ → NNReal → ℝ)
      (Set.Icc (0 : NNReal) N) := by
  rw [← uniformEquicontinuous_restrict_iff ((↑) : ascoliControlSet K0 δ → NNReal → ℝ)]
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hGeom :
      Tendsto (fun k : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ k) atTop (nhds (0 : ℝ≥0∞)) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  -- Proof comment: use strict eventual smallness of the dyadic tail so the final coercion back to
  -- `ℝ` can use `ENNReal.ofReal_lt_ofReal_iff`.
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 <|
    hGeom.eventually_lt_const (ENNReal.ofReal_pos.mpr hε)
  have hkε : (((1 / 2 : NNReal) ^ k : NNReal) : ℝ) < ε := by
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp <| by
      simpa [one_div, ENNReal.inv_pow] using hk k le_rfl
  refine ⟨δ N k, hδ N k, ?_⟩
  intro x y hxy i
  have hxy_le : dist (x : NNReal) y ≤ δ N k := by
    exact le_of_lt <| by simpa using hxy
  have hdist_le :
      ‖i.1 x - i.1 y‖₊ ≤ ((1 / 2 : NNReal) ^ k) := by
    exact (nnnorm_sub_le_compactIntervalOscillation N i.1 (δ N k) x y hxy_le).trans (i.2.2 N k)
  have hdist_lt : ((‖i.1 x - i.1 y‖₊ : NNReal) : ℝ) < ε := lt_of_le_of_lt hdist_le hkε
  simpa [Real.dist_eq] using hdist_lt

/-- Helper for Theorem 21.40: a compact family of paths admits a uniform compact-interval
oscillation modulus on each fixed interval `[0, N]`. -/
lemma isCompact_uniformCompactIntervalOscillation (K : Set PathSpace) (hK : IsCompact K) :
    ∀ N : ℕ, ∀ η : NNReal, 0 < η → ∃ δ : NNReal, 0 < δ ∧
      ∀ ω ∈ K, compactIntervalOscillation N ω δ ≤ η := by
  intro N η hη
  letI : PseudoMetricSpace PathSpace :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric PathSpace
  letI : UniformSpace (PathSpace × NNReal) := PseudoMetricSpace.toUniformSpace
  let evalOnInterval : PathSpace × NNReal → ℝ := fun p ↦ p.1 p.2
  have hEvalUC :
      UniformContinuousOn evalOnInterval (K ×ˢ Set.Icc (0 : NNReal) N) := by
    -- Proof comment: the evaluation map is continuous on the compact product `K × [0, N]`.
    refine (hK.prod isCompact_Icc).uniformContinuousOn_of_continuous ?_
    simpa [evalOnInterval] using
      (continuous_eval : Continuous fun p : PathSpace × NNReal ↦ p.1 p.2).continuousOn
  have hEvalMetric :
      ∀ ε' > 0, ∃ δReal > 0, ∀ x ∈ K ×ˢ Set.Icc (0 : NNReal) N,
        ∀ y ∈ K ×ˢ Set.Icc (0 : NNReal) N,
          dist x y ≤ δReal → dist (evalOnInterval x) (evalOnInterval y) ≤ ε' :=
    Metric.uniformContinuousOn_iff_le.mp hEvalUC
  rcases hEvalMetric η hη with ⟨δReal, hδRealPos, hδclose⟩
  have hδNonneg : 0 ≤ δReal / 2 := by
    positivity
  let δ : NNReal := ⟨δReal / 2, hδNonneg⟩
  have hδPos : 0 < δ := by
    change 0 < δReal / 2
    positivity
  have hδLt : (δ : ℝ) < δReal := by
    change δReal / 2 < δReal
    nlinarith
  refine ⟨δ, hδPos, ?_⟩
  intro ω hω
  refine compactIntervalOscillation_le_of_forall N ω δ η ?_
  intro s t hst
  have hProdDist : dist (ω, (s : NNReal)) (ω, (t : NNReal)) ≤ δReal := by
    -- Proof comment: the product distance collapses to the time-coordinate distance because the
    -- path coordinate is fixed at `ω`.
    have hProdDistEq :
        dist (ω, (s : NNReal)) (ω, (t : NNReal)) = dist (s : NNReal) t := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    have hProdDist' : dist (ω, (s : NNReal)) (ω, (t : NNReal)) ≤ (δ : ℝ) := by
      rw [hProdDistEq]
      exact hst
    exact le_trans hProdDist' hδLt.le
  -- Proof comment: apply the compact-product modulus to the two ambient pairs with their
  -- membership proofs in `K × [0, N]`.
  have hEvalClose :
      dist (evalOnInterval (ω, (s : NNReal))) (evalOnInterval (ω, (t : NNReal))) ≤ η :=
    hδclose (ω, (s : NNReal)) ⟨hω, s.2⟩ (ω, (t : NNReal)) ⟨hω, t.2⟩ hProdDist
  have hNormClose : ‖ω s - ω t‖ ≤ η := by
    simpa [evalOnInterval, Real.dist_eq] using hEvalClose
  exact nnnorm_le_of_norm_le hNormClose

/-- Helper for Theorem 21.40: the dyadic control set has compact closure once every mesh is
strictly positive. -/
lemma isCompact_closure_ascoliControlSet (K0 : NNReal) (δ : ℕ → ℕ → NNReal)
    (hδ : ∀ N k, 0 < δ N k) :
    IsCompact (closure (ascoliControlSet K0 δ)) := by
  have h0 :
      Bornology.IsBounded ((fun ω : PathSpace ↦ ω 0) '' ascoliControlSet K0 δ) := by
    have hEvalSub :
        ((fun ω : PathSpace ↦ ω 0) '' ascoliControlSet K0 δ) ⊆ Metric.closedBall (0 : ℝ) K0 := by
      rintro x ⟨ω, hω, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hω.1
    exact Metric.isBounded_closedBall.subset hEvalSub
  -- Proof comment: apply Arzelà--Ascoli directly to the dyadic control family, using the explicit
  -- dyadic oscillation bounds for equicontinuity and the time-zero bound for pointwise compactness.
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (ι := PathSpace) (X := NNReal) (α := ℝ)
    (F := ((↑) : PathSpace → NNReal → ℝ))
    (𝔖 := {K : Set NNReal | IsCompact K}) ?_ pathSpace_isClosedEmbedding_toUniformOnFun
    (s := ascoliControlSet K0 δ) ?_ ?_
  · intro K hK
    exact hK
  · intro K hK
    rcases exists_nat_Icc_superset_of_isCompact hK with ⟨N, hKN⟩
    have hEqIcc := ascoliControlSet_uniformEquicontinuousOnIcc K0 δ hδ N
    simpa [Function.comp] using (hEqIcc.mono hKN).equicontinuousOn
  · intro K hK x hx
    rcases exists_nat_Icc_superset_of_isCompact hK with ⟨N, hKN⟩
    have hEqIcc := ascoliControlSet_uniformEquicontinuousOnIcc K0 δ hδ N
    have hBound :=
      pointwiseBoundedEval_of_boundedEvalZero_and_uniformEquicontinuousOnIcc
        (A := ascoliControlSet K0 δ) N h0 hEqIcc (hKN hx)
    obtain ⟨R, hR⟩ := hBound.subset_closedBall (0 : ℝ)
    refine ⟨Metric.closedBall (0 : ℝ) R, isCompact_closedBall (0 : ℝ) R, ?_⟩
    intro ω hω
    exact hR ⟨ω, hω, rfl⟩
/-- Helper for Theorem 21.40: a countable family with the dyadic bound
`μ (s n) ≤ ε / 2^(n+1)` has total union measure at most `ε`. -/
lemma measure_iUnion_nat_le_of_dyadic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ε : ℝ≥0∞) (s : ℕ → Set α)
    (hs : ∀ n : ℕ, μ (s n) ≤ ε / 2 ^ (n + 1)) :
    μ (⋃ n, s n) ≤ ε := by
  -- Proof comment: dominate the union by the series of the dyadic bounds, then sum the geometric
  -- series explicitly.
  calc
    μ (⋃ n, s n) ≤ ∑' n : ℕ, μ (s n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ε / 2 ^ (n + 1) := ENNReal.tsum_le_tsum hs
    _ = ∑' n : ℕ, ε * ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
      congr with n
      simp [div_eq_mul_inv, ENNReal.inv_pow]
    _ = ε * ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
      rw [ENNReal.tsum_mul_left]
    _ = ε := by
      have hGeom :
          ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) = ((2 : ℝ≥0∞)⁻¹) * 2 := by
        simpa only [ENNReal.one_sub_inv_two, inv_inv] using
          (ENNReal.tsum_geometric_add_one ((2 : ℝ≥0∞)⁻¹))
      rw [hGeom]
      have hOne : ((2 : ℝ≥0∞)⁻¹) * 2 = 1 := by
        simpa using ENNReal.inv_mul_cancel
          (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
          (show (2 : ℝ≥0∞) ≠ ∞ by simp)
      simp [hOne]

/-- Helper for Theorem 21.40: the double dyadic error budget
`ε / 2^(N+k+3)` controls the measure of the full bad-event union by `ε / 2`. -/
lemma measure_iUnion_nat_nat_le_of_dyadic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ε : ℝ≥0∞) (s : ℕ → ℕ → Set α)
    (hs : ∀ N k : ℕ, μ (s N k) ≤ ε / 2 ^ (N + k + 3)) :
    μ (⋃ N, ⋃ k, s N k) ≤ ε / 2 := by
  -- Proof comment: first sum the inner dyadic budget in `k`, leaving the outer dyadic budget in
  -- `N`, and then apply the one-parameter estimate a second time.
  refine measure_iUnion_nat_le_of_dyadic (ε := ε / 2) (s := fun N ↦ ⋃ k, s N k) ?_
  intro N
  have hinner :
      μ (⋃ k, s N k) ≤ ε / 2 ^ (N + 2) := by
    refine measure_iUnion_nat_le_of_dyadic (ε := ε / 2 ^ (N + 2)) (s := s N) ?_
    intro k
    calc
      μ (s N k) ≤ ε / 2 ^ (N + k + 3) := hs N k
      _ = (ε / 2 ^ (N + 2)) / 2 ^ (k + 1) := by
        have hNat : N + k + 3 = (N + 2) + (k + 1) := by
          omega
        rw [hNat, pow_add]
        simp [div_eq_mul_inv, ENNReal.mul_inv, mul_left_comm, mul_comm]
  calc
    μ (⋃ k, s N k) ≤ ε / 2 ^ (N + 2) := hinner
    _ = (ε / 2) / 2 ^ (N + 1) := by
      have hNat : N + 2 = 1 + (N + 1) := by
        omega
      rw [hNat, pow_add]
      simp [div_eq_mul_inv, ENNReal.mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 21.40: leaving the dyadic control set means either the initial value or one
oscillation bound fails. -/
lemma compl_ascoliControlSet_subset_badUnion (K0 : NNReal) (δ : ℕ → ℕ → NNReal) :
    (ascoliControlSet K0 δ)ᶜ ⊆
      {ω | K0 < |ω 0|} ∪
        ⋃ N, ⋃ k, {ω | ((1 / 2 : NNReal) ^ k) < compactIntervalOscillation N ω (δ N k)} := by
  -- Proof comment: unpack the negation of the defining conjunction for `ascoliControlSet`.
  intro ω hω
  by_cases h0 : K0 < |ω 0|
  · exact Or.inl h0
  · right
    have h0' : |ω 0| ≤ K0 := not_lt.mp h0
    have hFail : ¬ ∀ N k, compactIntervalOscillation N ω (δ N k) ≤ ((1 / 2 : NNReal) ^ k) := by
      intro hAll
      exact hω ⟨h0', hAll⟩
    classical
    have hFailN := not_forall.mp hFail
    rcases hFailN with ⟨N, hFailN⟩
    have hFailK := not_forall.mp hFailN
    rcases hFailK with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨N, mem_iUnion.2 ⟨k, not_le.mp hk⟩⟩

/-- Helper for Theorem 21.40: compact closure of the path-law family yields one compact path-space
witness with uniformly small complement measure. -/
lemma exists_pathCompact_measure_compl_le_of_isCompact_closure_path_measure_family {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) (hCompact : IsCompact (closure (Set.range P))) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K : Set PathSpace, IsCompact K ∧ ∀ i, ((P i : Measure PathSpace) Kᶜ ≤ ε) := by
  intro ε hε
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable PathSpace
  have htight :
      IsTightMeasureSet
        ((((↑) : ProbabilityMeasure PathSpace → Measure PathSpace) '' Set.range P)) := by
    -- Proof comment: Prokhorov tightness applies directly to the compact closure of the family in
    -- `ProbabilityMeasure PathSpace`.
    simpa only [Set.mem_image, exists_exists_and_eq_and] using
      (MeasureTheory.isTightMeasureSet_of_isCompact_closure (S := Set.range P) hCompact)
  obtain ⟨K, hKCompact, hKBound⟩ :=
    (MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight) ε hε
  refine ⟨K, hKCompact, ?_⟩
  intro i
  -- Proof comment: specialize the uniform tightness witness to the measure `(P i : Measure _)`.
  exact hKBound _ ⟨P i, ⟨i, rfl⟩, rfl⟩

/-- Helper for Theorem 21.40: a probability-measure bound can be read as the corresponding
measure-theoretic bound after coercion to `Measure`. -/
lemma probabilityMeasureBoundToMeasureBound {α : Type*} [MeasurableSpace α]
    (μ : ProbabilityMeasure α) {s : Set α} {r : NNReal} (h : μ s ≤ r) :
    ((μ : Measure α) s ≤ (r : ℝ≥0∞)) := by
  -- Proof comment: the coercion from `ProbabilityMeasure` to `Measure` preserves evaluation on
  -- measurable sets, so the bound is just an `ENNReal` coercion.
  simpa using (show ((μ s : NNReal) : ℝ≥0∞) ≤ (r : ℝ≥0∞) from ENNReal.coe_le_coe.mpr h)

/-- Helper for Theorem 21.40: relative compactness of the path-law family implies tightness of the
initial-value laws. -/
lemma initial_value_laws_tight_of_isCompact_closure_path_measure_family {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) (hCompact : IsCompact (closure (Set.range P))) :
    initial_value_laws_tight P := by
  refine (initial_value_laws_tight_iff P).2 ?_
  intro ε hε
  -- Proof comment: choose one compact path set capturing all but `ε` mass, then bound the bad
  -- time-zero event by the complement of that compact set.
  obtain ⟨K, hKCompact, hKBound⟩ :=
    exists_pathCompact_measure_compl_le_of_isCompact_closure_path_measure_family P hCompact
      (ε : ℝ≥0∞) (by exact_mod_cast hε)
  obtain ⟨K0, hK0Pos, hK0Bound⟩ := exists_evalZeroBound_of_isCompact K hKCompact
  refine ⟨K0, hK0Pos, ?_⟩
  intro i
  have hBadSubset : {ω | (K0 : ℝ) < |ω 0|} ⊆ Kᶜ := by
    intro ω hω
    rw [Set.mem_compl_iff]
    intro hωK
    exact (not_lt_of_ge (hK0Bound ω hωK)) (by simpa using hω)
  have hBadMeasure :
      ((P i : Measure PathSpace) {ω | (K0 : ℝ) < |ω 0|}) ≤ (ε : ℝ≥0∞) := by
    calc
      ((P i : Measure PathSpace) {ω | (K0 : ℝ) < |ω 0|})
          ≤ ((P i : Measure PathSpace) Kᶜ) := measure_mono hBadSubset
      _ ≤ (ε : ℝ≥0∞) := hKBound i
  have hBadMeasure' : (((P i {ω | (K0 : ℝ) < |ω 0|} : NNReal) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) := by
    simpa using hBadMeasure
  exact ENNReal.coe_le_coe.mp hBadMeasure'

/-- Helper for Theorem 21.40: relative compactness of the path-law family implies uniformly small
compact-interval oscillation probabilities. -/
lemma oscillation_probabilities_of_isCompact_closure_path_measure_family {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) (hCompact : IsCompact (closure (Set.range P))) :
    uniformly_small_compact_interval_path_oscillation_probabilities P := by
  intro η ε hη hε N
  -- Proof comment: the same compact witness controls oscillations on `[0,N]`, so the bad
  -- oscillation event again sits inside the compact complement.
  obtain ⟨K, hKCompact, hKBound⟩ :=
    exists_pathCompact_measure_compl_le_of_isCompact_closure_path_measure_family P hCompact
      (ε : ℝ≥0∞) (by exact_mod_cast hε)
  obtain ⟨δ, hδPos, hδBound⟩ := isCompact_uniformCompactIntervalOscillation K hKCompact N η hη
  refine ⟨δ, hδPos, ?_⟩
  intro i
  have hBadSubset : {ω | η < compactIntervalOscillation N ω δ} ⊆ Kᶜ := by
    intro ω hω
    rw [Set.mem_compl_iff]
    intro hωK
    exact (not_lt_of_ge (hδBound ω hωK)) hω
  have hBadMeasure :
      ((P i : Measure PathSpace) {ω | η < compactIntervalOscillation N ω δ}) ≤ (ε : ℝ≥0∞) := by
    calc
      ((P i : Measure PathSpace) {ω | η < compactIntervalOscillation N ω δ})
          ≤ ((P i : Measure PathSpace) Kᶜ) := measure_mono hBadSubset
      _ ≤ (ε : ℝ≥0∞) := hKBound i
  have hBadMeasure' :
      (((P i {ω | η < compactIntervalOscillation N ω δ} : NNReal) : ℝ≥0∞) ≤
        (ε : ℝ≥0∞)) := by
    simpa using hBadMeasure
  exact ENNReal.coe_le_coe.mp hBadMeasure'

/-- Helper for Theorem 21.40: relative compactness of the path-law family yields the two textbook
control conditions. -/
lemma controls_of_isCompact_closure_path_measure_family {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) (hCompact : IsCompact (closure (Set.range P))) :
    initial_value_laws_tight P ∧
      uniformly_small_compact_interval_path_oscillation_probabilities P := by
  -- Proof comment: combine the separate compact-witness consequences for time `0` and oscillation.
  exact ⟨initial_value_laws_tight_of_isCompact_closure_path_measure_family P hCompact,
    oscillation_probabilities_of_isCompact_closure_path_measure_family P hCompact⟩

/-- Helper for Theorem 21.40: the two textbook control conditions imply relative compactness of
the path-law family. -/
lemma isCompact_closure_path_measure_family_of_controls {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace)
    (hInit : initial_value_laws_tight P)
    (hOsc : uniformly_small_compact_interval_path_oscillation_probabilities P) :
    IsCompact (closure (Set.range P)) := by
  refine isCompact_closure_of_isTightMeasureSet (S := Set.range P) ?_
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεTop : ε = ∞
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro μ hμ
    simp [hεTop]
  lift ε to NNReal using hεTop with ε'
  have hε' : 0 < ε' := by
    exact_mod_cast hε
  have hInit' := (initial_value_laws_tight_iff P).mp hInit
  obtain ⟨K0, hK0Pos, hK0Bound⟩ := hInit' (ε' / 2) (by positivity)
  have hOscChoice :
      ∀ N k : ℕ, ∃ δ : NNReal, 0 < δ ∧
        ∀ i, P i {ω | ((1 / 2 : NNReal) ^ k) < compactIntervalOscillation N ω δ} ≤
          ε' / 2 ^ (N + k + 3) := by
    intro N k
    exact hOsc ((1 / 2 : NNReal) ^ k) (ε' / 2 ^ (N + k + 3)) (by positivity) (by positivity) N
  choose δ hδPos hδBound using hOscChoice
  let badOsc : ℕ → ℕ → Set PathSpace := fun N k ↦
    {ω | ((1 / 2 : NNReal) ^ k) < compactIntervalOscillation N ω (δ N k)}
  let controlSet : Set PathSpace := ascoliControlSet K0 δ
  have hControlCompact : IsCompact (closure controlSet) := by
    -- Proof comment: the dyadic mesh choices are designed exactly so the imported
    -- Arzelà--Ascoli criterion applies to the control set.
    simpa [controlSet] using isCompact_closure_ascoliControlSet K0 δ hδPos
  refine ⟨closure controlSet, hControlCompact, ?_⟩
  intro μ hμ
  rcases hμ with ⟨ν, hνRange, rfl⟩
  rcases hνRange with ⟨i, rfl⟩
  have hInitBoundMeasure :
      ((P i : Measure PathSpace) {ω | K0 < |ω 0|}) ≤ (ε' : ℝ≥0∞) / 2 := by
    simpa using probabilityMeasureBoundToMeasureBound (P i) (s := {ω | K0 < |ω 0|})
      (r := ε' / 2) (hK0Bound i)
  have hOscUnionBound :
      ((P i : Measure PathSpace) (⋃ N, ⋃ k, badOsc N k)) ≤ (ε' : ℝ≥0∞) / 2 := by
    -- Proof comment: sum the dyadic oscillation error budget first in `k` and then in `N`.
    refine measure_iUnion_nat_nat_le_of_dyadic (μ := (P i : Measure PathSpace))
      (ε := (ε' : ℝ≥0∞)) (s := badOsc) ?_
    intro N k
    simpa [badOsc] using
      probabilityMeasureBoundToMeasureBound (P i) (s := badOsc N k)
        (r := ε' / 2 ^ (N + k + 3)) (hδBound N k i)
  have hControlCompl :
      ((P i : Measure PathSpace) controlSetᶜ) ≤ (ε' : ℝ≥0∞) := by
    calc
      ((P i : Measure PathSpace) controlSetᶜ)
          ≤ ((P i : Measure PathSpace) ({ω | K0 < |ω 0|} ∪ ⋃ N, ⋃ k, badOsc N k)) := by
            refine measure_mono ?_
            simpa [controlSet, badOsc] using compl_ascoliControlSet_subset_badUnion K0 δ
      _ ≤ ((P i : Measure PathSpace) {ω | K0 < |ω 0|}) +
            ((P i : Measure PathSpace) (⋃ N, ⋃ k, badOsc N k)) :=
          measure_union_le _ _
      _ ≤ (ε' : ℝ≥0∞) / 2 + (ε' : ℝ≥0∞) / 2 := add_le_add hInitBoundMeasure hOscUnionBound
      _ = (ε' : ℝ≥0∞) := by
        calc
          (ε' : ℝ≥0∞) / 2 + (ε' : ℝ≥0∞) / 2
              = (((ε' / 2 : NNReal) + ε' / 2 : NNReal) : ℝ≥0∞) := by simp
          _ = (ε' : ℝ≥0∞) := by
            have hHalfAddHalf : ((ε' / 2 : NNReal) + ε' / 2 : NNReal) = ε' := add_halves ε'
            rw [hHalfAddHalf]
  calc
    ((P i : Measure PathSpace) (closure controlSet)ᶜ)
        ≤ ((P i : Measure PathSpace) controlSetᶜ) :=
          measure_mono (compl_subset_compl.mpr subset_closure)
    _ ≤ (ε' : ℝ≥0∞) := hControlCompl

/-- Theorem 21.40: a family of probability measures on `C([0,∞))`, represented here by
`ContinuousMap NNReal ℝ`, is weakly relatively compact iff the initial-value laws are tight and
the compact-interval oscillation probabilities are uniformly small. -/
-- Proof sketch: for the forward implication, combine Prokhorov tightness with the compact-set
-- characterization of relatively compact subsets of the continuous path space via Arzelà--Ascoli.
-- For the reverse implication, use the two stated bounds to build compact subsets capturing all
-- but `ε` mass uniformly in the family, and conclude by Prokhorov's theorem.
theorem continuous_path_measure_family_weakly_relatively_compact_iff {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) :
    IsCompact (closure (Set.range P)) ↔
      initial_value_laws_tight P ∧
        uniformly_small_compact_interval_path_oscillation_probabilities P := by
  -- Route correction: use the canonical Arzelà--Ascoli criterion from Theorem 21.39 instead of
  -- the earlier local fallback copy, then keep the proof entirely at the compact-witness level.
  constructor
  · exact controls_of_isCompact_closure_path_measure_family P
  · rintro ⟨hInit, hOsc⟩
    exact isCompact_closure_path_measure_family_of_controls P hInit hOsc
