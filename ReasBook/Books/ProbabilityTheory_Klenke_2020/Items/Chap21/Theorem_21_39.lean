/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30

open Filter Set
open scoped ENNReal Topology

noncomputable section

local notation "PathSpace" => BrownianPathSpace

/-- Helper for Theorem 21.39: the admissible oscillation values on `[0, N]` at mesh `δ`. -/
def compactIntervalOscillationValues (N : ℕ) (ω : PathSpace) (δ : NNReal) : Set NNReal :=
  {r | ∃ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) t ≤ δ ∧ r = ‖ω s - ω t‖₊}

/-- Helper for Theorem 21.39: the maximal oscillation of one path on `[0, N]` at mesh `δ`. -/
def compactIntervalOscillation (N : ℕ) (ω : PathSpace) (δ : NNReal) : NNReal :=
  sSup (compactIntervalOscillationValues N ω δ)

/-- Helper for Theorem 21.39: every admissible pair contributes its oscillation value to the
compact-interval oscillation value set. -/
lemma mem_compactIntervalOscillationValues (N : ℕ) (ω : PathSpace) (δ : NNReal)
    (s t : Set.Icc (0 : NNReal) N) (hst : dist (s : NNReal) t ≤ δ) :
    ‖ω s - ω t‖₊ ∈ compactIntervalOscillationValues N ω δ := by
  -- Proof comment: unfold the defining existential and package the chosen pair `(s, t)`.
  exact ⟨s, t, hst, rfl⟩

/-- Helper for Theorem 21.39: the admissible oscillation values form a bounded-above set. -/
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

/-- Helper for Theorem 21.39: the family supremum of compact-interval oscillations. -/
def compactIntervalOscillationSup (A : Set PathSpace) (N : ℕ) (δ : NNReal) : ℝ≥0∞ :=
  ⨆ ω : A, ENNReal.ofReal (compactIntervalOscillation N ω.1 δ)

/-- Helper for Theorem 21.39: pointwise control on all admissible pairs bounds the corresponding
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

/-- Helper for Theorem 21.39: each admissible increment on `[0, N]` is dominated by the maximal
oscillation at the same mesh. -/
lemma nnnorm_sub_le_compactIntervalOscillation (N : ℕ) (ω : PathSpace) (δ : NNReal)
    (s t : Set.Icc (0 : NNReal) N) (hst : dist (s : NNReal) t ≤ δ) :
    ‖ω s - ω t‖₊ ≤ compactIntervalOscillation N ω δ := by
  -- Proof comment: the increment is one of the values entering the supremum.
  refine le_csSup (compactIntervalOscillationValues_bddAbove N ω δ) ?_
  exact mem_compactIntervalOscillationValues N ω δ s t hst

/-- Helper for Theorem 21.39: a uniform pointwise oscillation bound on a family controls the family
supremum. -/
lemma compactIntervalOscillationSup_le_of_forall (A : Set PathSpace) (N : ℕ) (δ η : NNReal)
    (hη : ∀ ω ∈ A, compactIntervalOscillation N ω δ ≤ η) :
    compactIntervalOscillationSup A N δ ≤ ENNReal.ofReal η := by
  -- Proof comment: bound each summand in the family `iSup` and then pass to the supremum.
  simpa [compactIntervalOscillationSup] using
    (iSup_le fun ω : A ↦ ENNReal.ofReal_le_ofReal (hη ω.1 ω.2))

/-- Helper for Theorem 21.39: decay of the family oscillation modulus on `[0, N]` yields uniform
equicontinuity on that compact interval. -/
lemma uniformEquicontinuousOnIcc_of_tendsto_compactIntervalOscillationSup
    (A : Set PathSpace) (N : ℕ)
    (hA : Tendsto (fun δ : NNReal ↦ compactIntervalOscillationSup A N δ)
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ≥0∞))) :
    UniformEquicontinuousOn ((↑) : A → NNReal → ℝ) (Set.Icc (0 : NNReal) N) := by
  -- Proof comment: rewrite to the metric `ε-δ` criterion on the interval restriction and use the
  -- oscillation supremum as the common modulus for all paths in `A`.
  rw [← uniformEquicontinuous_restrict_iff ((↑) : A → NNReal → ℝ)]
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  let η : NNReal := ⟨ε / 2, by positivity⟩
  have hηpos : 0 < η := by
    change 0 < ε / 2
    positivity
  have hηlt : (η : ℝ) < ε := by
    change ε / 2 < ε
    nlinarith
  have hSmall :
      {δ : NNReal | compactIntervalOscillationSup A N δ < ENNReal.ofReal η} ∈
        nhdsWithin (0 : NNReal) (Ioi 0) := by
    exact hA (Iio_mem_nhds (by
      simpa [η] using ENNReal.ofReal_pos.mpr (show 0 < ε / 2 by positivity)))
  rw [Metric.mem_nhdsWithin_iff] at hSmall
  rcases hSmall with ⟨δ₀, hδ₀pos, hδ₀small⟩
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro x y hxy i
  by_cases hxy0 : dist x y = 0
  · have hxyEq : x = y := dist_eq_zero.mp hxy0
    subst hxyEq
    simpa using hε
  · let δxy : NNReal := ⟨dist x y, dist_nonneg⟩
    have hδxy_mem : δxy ∈ Metric.ball (0 : NNReal) δ₀ ∩ Ioi (0 : NNReal) := by
      refine ⟨?_, ?_⟩
      · simpa [Metric.mem_ball, δxy, NNReal.dist_eq, abs_of_nonneg dist_nonneg] using hxy
      · have hxyNe : x ≠ y := by
          simpa [dist_eq_zero] using hxy0
        have hxyPos : 0 < dist x y := dist_pos.mpr hxyNe
        change (0 : ℝ) < δxy
        simpa [δxy] using hxyPos
    have hSupSmall : compactIntervalOscillationSup A N δxy < ENNReal.ofReal η :=
      hδ₀small hδxy_mem
    have hPathSmall :
        compactIntervalOscillation N i.1 δxy < η := by
      have hle :
          ENNReal.ofReal (compactIntervalOscillation N i.1 δxy) ≤
            compactIntervalOscillationSup A N δxy := by
        unfold compactIntervalOscillationSup
        exact le_iSup_of_le i le_rfl
      exact (ENNReal.ofReal_lt_ofReal_iff hηpos).mp (lt_of_le_of_lt hle hSupSmall)
    have hdist_le :
        ‖i.1 x - i.1 y‖₊ ≤ compactIntervalOscillation N i.1 δxy := by
      have hxy_le : dist (x : NNReal) y ≤ δxy := by
        change dist (x : NNReal) y ≤ dist x y
        exact le_rfl
      exact nnnorm_sub_le_compactIntervalOscillation N i.1 δxy x y hxy_le
    have hdist_lt : (‖i.1 x - i.1 y‖₊ : ℝ) < ε := by
      exact lt_trans (lt_of_le_of_lt hdist_le hPathSmall) hηlt
    simpa [Real.dist_eq] using hdist_lt

/-- Helper for Theorem 21.39: a compact family of paths admits a uniform compact-interval
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
      simpa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    have hProdDist' : dist (ω, (s : NNReal)) (ω, (t : NNReal)) ≤ (δ : ℝ) := by
      rw [hProdDistEq]
      exact hst
    exact le_trans hProdDist' hδLt.le
  -- Proof comment: apply the compact-product modulus to the two ambient pairs with their
  -- membership proofs in `K × [0, N]`.
  change ((‖ω s - ω t‖₊ : NNReal) : ℝ) ≤ η
  simpa [evalOnInterval, Real.dist_eq] using
    hδclose (ω, (s : NNReal)) ⟨hω, s.2⟩ (ω, (t : NNReal)) ⟨hω, t.2⟩ hProdDist

/-- Helper for Theorem 21.39: a compact ambient family gives a vanishing family oscillation
modulus on each fixed compact interval. -/
lemma tendsto_compactIntervalOscillationSup_of_isCompact_subset
    (K A : Set PathSpace) (hK : IsCompact K) (hAK : A ⊆ K) (N : ℕ) :
    Tendsto (fun δ : NNReal ↦ compactIntervalOscillationSup A N δ)
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
  -- Proof comment: use the metric neighborhood criterion at `0`, extracting one good positive mesh
  -- from the compact-family oscillation modulus on `K`.
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hεTop : ε = ∞
  · simp [hεTop]
  · lift ε to NNReal using hεTop with η
    have hηpos : 0 < η := by
      exact_mod_cast hε
    obtain ⟨δ, hδPos, hδBound⟩ := isCompact_uniformCompactIntervalOscillation K hK N η hηpos
    have hSmall :
        {δ' : NNReal | compactIntervalOscillationSup A N δ' ≤ ENNReal.ofReal η} ∈
          nhdsWithin (0 : NNReal) (Ioi 0) := by
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨δ, hδPos, ?_⟩
      intro δ' hδ'
      refine compactIntervalOscillationSup_le_of_forall A N δ' η ?_
      intro ω hω
      have hδ'lt : δ' < δ := by
        simpa [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg δ'.2] using hδ'.1
      refine compactIntervalOscillation_le_of_forall N ω δ' η ?_
      intro s t hst
      have hst' : dist (s : NNReal) t ≤ δ := le_trans hst hδ'lt.le
      exact
        (nnnorm_sub_le_compactIntervalOscillation N ω δ s t hst').trans
          (hδBound ω (hAK hω))
    simpa using hSmall

/-- Helper for Theorem 21.39: every compact subset of `NNReal` is contained in some interval
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

/-- Helper for Theorem 21.39: consecutive points in the linear subdivision differ by exactly one
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

/-- Helper for Theorem 21.39: every `t ∈ [0, N]` admits a finite subdivision from `0` to `t`
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

/-- Helper for Theorem 21.39: bounded time-zero evaluations plus uniform equicontinuity on
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
      induction' n with n ih
      · -- Proof comment: the first subdivision node is exactly `0`, so the given time-zero bound
        -- already controls the base case.
        simpa [hu0, Metric.mem_closedBall, Real.dist_eq] using hω0Ball
      · have hnle : n ≤ m := Nat.le_of_succ_le hn
        have hprev : |ω (u n)| ≤ R + n := ih hnle
        have hmesh : dist (u n : NNReal) (u (n + 1) : NNReal) < δ := huStep n (Nat.lt_of_succ_le hn)
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
            simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    have hωt : |ω t| ≤ R + m := by
      simpa [hum] using hωBound m le_rfl
    simpa [Metric.mem_closedBall, Real.dist_eq] using hωt
  exact Metric.isBounded_closedBall.subset hImageSubset

/-- Helper for Theorem 21.39: bounded time-zero evaluations and vanishing compact-interval
oscillation moduli imply the pointwise compactness input required by Arzelà--Ascoli. -/
lemma pointwiseCompactOnCompacts_of_boundedEvalZero_and_tendsto_compactIntervalOscillationSup
    (A : Set PathSpace)
    (h0 : Bornology.IsBounded ((fun ω : PathSpace ↦ ω 0) '' A))
    (hmod : ∀ N : ℕ, Tendsto (fun δ : NNReal ↦ compactIntervalOscillationSup A N δ)
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ≥0∞))) :
    ∀ K : Set NNReal, IsCompact K → ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧ ∀ ω ∈ A, ω x ∈ Q := by
  intro K hK x hx
  rcases exists_nat_Icc_superset_of_isCompact hK with ⟨N, hKN⟩
  have hEqIcc :=
    uniformEquicontinuousOnIcc_of_tendsto_compactIntervalOscillationSup A N (hmod N)
  have hBound :=
    pointwiseBoundedEval_of_boundedEvalZero_and_uniformEquicontinuousOnIcc A N h0 hEqIcc
      (hKN hx)
  obtain ⟨R, hR⟩ := hBound.subset_closedBall (0 : ℝ)
  -- Proof comment: once the evaluation image at `x` is bounded, one closed ball gives the compact
  -- witness needed by the Ascoli pointwise-compactness hypothesis.
  refine ⟨Metric.closedBall (0 : ℝ) R, isCompact_closedBall (0 : ℝ) R, ?_⟩
  intro ω hω
  exact hR ⟨ω, hω, rfl⟩

/-- Helper for Theorem 21.39: compact convergence embeds `PathSpace` as a closed subset of the
ambient `UniformOnFun` space. -/
lemma pathSpace_isClosedEmbedding_toUniformOnFun :
    Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set NNReal | IsCompact K} ∘
        ((↑) : PathSpace → NNReal → ℝ)) := by
  -- Proof comment: compact convergence on continuous maps gives a closed embedding into the
  -- corresponding `UniformOnFun` space.
  letI : T2Space (UniformOnFun NNReal ℝ {K : Set NNReal | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (β := ℝ) <| by
      ext x
      constructor
      · intro _
        simp
      · intro _
        exact mem_sUnion.2 ⟨{x}, by simp, by simp⟩
  simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp] using
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
      (α := NNReal) (β := ℝ)).isClosedEmbedding

/-- Helper for Theorem 21.39: bounded time-zero evaluations and vanishing compact-interval
oscillation moduli imply compactness of `closure A`. -/
lemma isCompact_closure_of_boundedEvalZero_and_tendsto_compactIntervalOscillationSup
    (A : Set PathSpace)
    (h0 : Bornology.IsBounded ((fun ω : PathSpace ↦ ω 0) '' A))
    (hmod : ∀ N : ℕ, Tendsto (fun δ : NNReal ↦ compactIntervalOscillationSup A N δ)
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ≥0∞))) :
    IsCompact (closure A) := by
  -- Proof comment: apply Arzelà--Ascoli with the compact cover by all compact subsets of
  -- `NNReal`, reducing each compact set to one interval `[0, N]`.
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (ι := PathSpace) (X := NNReal) (α := ℝ)
    (F := ((↑) : PathSpace → NNReal → ℝ))
    (𝔖 := {K : Set NNReal | IsCompact K}) ?_ pathSpace_isClosedEmbedding_toUniformOnFun
    (s := A) ?_ ?_
  · intro K hK
    exact hK
  · intro K hK
    rcases exists_nat_Icc_superset_of_isCompact hK with ⟨N, hKN⟩
    have hEqIcc :=
      uniformEquicontinuousOnIcc_of_tendsto_compactIntervalOscillationSup A N (hmod N)
    simpa [Function.comp] using (hEqIcc.mono hKN).equicontinuousOn
  · intro K hK x hx
    exact pointwiseCompactOnCompacts_of_boundedEvalZero_and_tendsto_compactIntervalOscillationSup
      A h0 hmod K hK x hx

/-- Theorem 21.39: a family of paths is relatively compact exactly when its time-zero values are
bounded and its compact-interval oscillation moduli vanish uniformly as `δ ↓ 0`. -/
theorem brownianPathSpace_relativelyCompact_iff_arzelaAscoli (A : Set PathSpace) :
    IsCompact (closure A) ↔
      Bornology.IsBounded ((fun ω : PathSpace ↦ ω 0) '' A) ∧
        ∀ N : ℕ, Tendsto (fun δ : NNReal ↦ compactIntervalOscillationSup A N δ)
          (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
  -- Route correction: the earlier subtype-closure proof route is an expensive normal form here.
  -- Proof comment: use the direct closed-embedding form of Arzelà--Ascoli on `PathSpace`,
  -- reducing equicontinuity on compact sets to the interval estimates already established above.
  constructor
  · intro hCompact
    refine ⟨?_, ?_⟩
    · have hImageCompact : IsCompact ((fun ω : PathSpace ↦ ω 0) '' closure A) := by
        simpa using hCompact.image (continuous_eval_const (0 : NNReal))
      -- Proof comment: the time-zero evaluation image of `A` sits inside the compact evaluation
      -- image of `closure A`, hence it is bounded as well.
      refine hImageCompact.isBounded.subset ?_
      rintro x ⟨ω, hω, rfl⟩
      exact ⟨ω, subset_closure hω, rfl⟩
    · intro N
      -- Proof comment: compactness of the ambient family gives a uniform continuity modulus on
      -- `closure A × [0, N]`, which restricts to the subfamily `A`.
      exact tendsto_compactIntervalOscillationSup_of_isCompact_subset (closure A) A hCompact
        subset_closure N
  · intro hA
    rcases hA with ⟨h0, hmod⟩
    exact
      isCompact_closure_of_boundedEvalZero_and_tendsto_compactIntervalOscillationSup A h0 hmod
