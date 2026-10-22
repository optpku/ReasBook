/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E]

/-- The closed cube `[-T, T]^d` in `ℝ^d`, viewed as a subset of `EuclideanSpace ℝ (Fin d)`. -/
def euclideanClosedCube (d : ℕ) (T : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc (-T) T}

-- Proof sketch: unfold `euclideanClosedCube`; membership is defined coordinatewise by the
-- condition that every component belongs to `[-T, T]`.
/-- Membership in `euclideanClosedCube d T` means that every coordinate lies in `[-T, T]`. -/
theorem mem_euclideanClosedCube_iff {d : ℕ} {T : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ euclideanClosedCube d T ↔ ∀ i : Fin d, x i ∈ Set.Icc (-T) T :=
  Iff.rfl

/-- The source-facing multidimensional Kolmogorov condition on the cube `[-T, T]^d`: after
restricting the index space to the cube subtype, the process is a
`ProbabilityTheory.IsKolmogorovProcess` with exponent `d + β`. This is the thin bridge from the
textbook cube formulation to the canonical owner abstraction. -/
def IsKolmogorovProcessOnEuclideanClosedCube
    (μ : Measure Ω) {d : ℕ} (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T α β C : ℝ≥0) : Prop :=
  IsKolmogorovProcess (fun t : euclideanClosedCube d (T : ℝ) ↦ X t) μ (α : ℝ)
    (((d : ℝ≥0) + β : ℝ)) C

/-- A cube-restricted Kolmogorov process gives the stated increment estimate for points of
`[-T, T]^d`. -/
theorem IsKolmogorovProcessOnEuclideanClosedCube.increment_lintegral_le
    {μ : Measure Ω} {d : ℕ} {X : EuclideanSpace ℝ (Fin d) → Ω → E}
    {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    {s t : EuclideanSpace ℝ (Fin d)}
    (hs : s ∈ euclideanClosedCube d (T : ℝ))
    (ht : t ∈ euclideanClosedCube d (T : ℝ)) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (((d : ℝ≥0) + β : ℝ)) := by
  simpa [edist_comm] using h.kolmogorovCondition ⟨s, hs⟩ ⟨t, ht⟩

-- Semantic recall note: `lean_leansearch` timed out here; the local Chapter 21 owner theorems use
-- the complete, second-countable metric hypotheses for the displayed metric.

/-- A Hölder exponent `γ` is admissible for a process on `ℝ≥0` if every finite interval admits a
Kolmogorov bound with `γ < β / α`. -/
private def IsFiniteIntervalHolderAdmissible
    (μ : Measure Ω) (X : NNReal → Ω → E) (γ : ℝ≥0) : Prop :=
  ∀ T : NNReal, ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C ∧ (γ : ℝ) < β / α

/-- Auxiliary package for Remark 21.7 (1): a single modification carries both the local Hölder
path conclusion for every admissible exponent and the intervalwise high-probability Hölder bound. -/
private def HasRemark21_7_1Conclusions
    (μ : Measure Ω) (X Xtilde : NNReal → Ω → E) : Prop :=
  (∀ γ : ℝ≥0, 0 < γ →
    IsFiniteIntervalHolderAdmissible μ X γ →
      ∀ ω : Ω, LocallyHolderWith γ (fun t : NNReal ↦ Xtilde t ω)) ∧
  ∀ (T α β C γ : ℝ≥0),
    IsKolmogorovProcessOnIcc μ X T α β C →
    0 < γ →
      (γ : ℝ) < β / α →
        ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0,
          ENNReal.ofReal (1 - ε) ≤
            μ {ω | HolderOnWith K γ (fun t : NNReal ↦ Xtilde t ω) (Set.Icc (0 : NNReal) T)}

/-- Helper for Remark 21.7: two finite-horizon versions of the same `E`-valued process agree
almost surely on their common interval. -/
lemma aeEq_on_overlap_of_versionsMetric
    {μ : Measure Ω}
    {X Y Z : NNReal → Ω → E} {S T : NNReal}
    (hXY : ∀ t : NNReal, t ≤ S → X t =ᵐ[μ] Y t)
    (hXZ : ∀ t : NNReal, t ≤ T → X t =ᵐ[μ] Z t) :
    ∀ t : NNReal, t ≤ min S T → Y t =ᵐ[μ] Z t := by
  let _ : MetricSpace E := inferInstance
  intro t ht
  -- Proof comment: both versions agree almost surely with the same source process on the overlap
  -- interval, so they agree almost surely with each other there.
  filter_upwards [hXY t (le_trans ht (min_le_left _ _)), hXZ t (le_trans ht (min_le_right _ _))]
    with ω hY hZ
  exact hY.symm.trans hZ

/-- Helper for Remark 21.7: Hölder control on `[0,T] ⊆ ℝ≥0` induces a Hölder map on the
corresponding real interval subtype after composing with `Real.toNNReal`. -/
lemma holderWith_realSubtypeIcc_of_holderOnWithMetric
    {T K γ : ℝ≥0} {f : NNReal → E}
    (h : HolderOnWith K γ f (Set.Icc (0 : NNReal) T)) :
    HolderWith K γ (fun t : Set.Icc (0 : ℝ) (T : ℝ) ↦ f t.1.toNNReal) := by
  intro s t
  have hs : s.1.toNNReal ∈ Set.Icc (0 : NNReal) T := by
    constructor
    · simp
    · simpa using Real.toNNReal_mono s.2.2
  have ht : t.1.toNNReal ∈ Set.Icc (0 : NNReal) T := by
    constructor
    · simp
    · simpa using Real.toNNReal_mono t.2.2
  have hdist :
      edist s.1.toNNReal t.1.toNNReal ≤ edist s t := by
    have hdist_real : dist s.1.toNNReal t.1.toNNReal ≤ dist s t := by
      simpa using Real.lipschitzWith_toNNReal.dist_le_mul s.1 t.1
    simpa [edist_dist] using ENNReal.ofReal_le_ofReal hdist_real
  calc
    edist (f s.1.toNNReal) (f t.1.toNNReal) ≤ K * edist s.1.toNNReal t.1.toNNReal ^ (γ : ℝ) :=
      h s.1.toNNReal hs t.1.toNNReal ht
    _ ≤ K * edist s t ^ (γ : ℝ) := by
      gcongr

/-- Helper for Remark 21.7: pathwise Hölder control on `[0,T]` gives the right continuity on the
real interval subtype needed for overlap indistinguishability. -/
lemma continuousWithinAt_realSubtypeIcc_of_holderOnWithMetric
    {T K γ : ℝ≥0} {f : NNReal → E}
    (hγ : 0 < γ)
    (h : HolderOnWith K γ f (Set.Icc (0 : NNReal) T))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ContinuousWithinAt (fun s : Set.Icc (0 : ℝ) (T : ℝ) ↦ f s.1.toNNReal) (Set.Ici t) t := by
  -- Proof comment: the induced map on the real interval subtype is globally Hölder, hence
  -- continuous and therefore continuous within every right neighborhood.
  have hcont :
      Continuous (fun s : Set.Icc (0 : ℝ) (T : ℝ) ↦ f s.1.toNNReal) :=
    (holderWith_realSubtypeIcc_of_holderOnWithMetric h).continuous hγ
  exact hcont.continuousAt.continuousWithinAt

/-- Helper for Remark 21.7: if two `E`-valued paths agree off a null set on `Set.Icc (0,T)`,
then the corresponding Hölder events agree almost surely. -/
lemma holderEvent_congr_of_eqOnIcc_offNullMetric
    {μ : Measure Ω}
    {Y Z : NNReal → Ω → E} {T K γ : ℝ≥0} {N : Set Ω}
    (hN : μ N = 0)
    (hEq :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        Set.EqOn (fun t : NNReal ↦ Y t ω) (fun t : NNReal ↦ Z t ω) (Set.Icc (0 : NNReal) T)) :
    {ω | HolderOnWith K γ (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)} =ᵐ[μ]
      {ω | HolderOnWith K γ (fun t : NNReal ↦ Z t ω) (Set.Icc (0 : NNReal) T)} := by
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
    rw [ae_iff]
    simpa using hN
  -- Proof comment: outside the null exceptional set, the two path restrictions coincide pointwise
  -- on the full interval, so the Hölder predicate is equivalent there.
  filter_upwards [hNae] with ω hω
  have hωeq := hEq hω
  apply propext
  constructor
  · intro hHolder s hs t ht
    have hsEq : Y s ω = Z s ω := hωeq (x := s) hs
    have htEq : Y t ω = Z t ω := hωeq (x := t) ht
    simpa [hsEq, htEq] using hHolder s hs t ht
  · intro hHolder s hs t ht
    have hsEq : Y s ω = Z s ω := hωeq (x := s) hs
    have htEq : Y t ω = Z t ω := hωeq (x := t) ht
    simpa [hsEq, htEq] using hHolder s hs t ht

/-- Helper for Remark 21.7: two finite-horizon Hölder versions of the same `E`-valued process are
indistinguishable on their overlap. -/
lemma indistinguishable_on_overlap_of_holderVersionsMetric
    {μ : Measure Ω}
    {X Y Z : NNReal → Ω → E} {S T rY rZ : ℝ≥0}
    (hXY : ∀ t : NNReal, t ≤ S → X t =ᵐ[μ] Y t)
    (hXZ : ∀ t : NNReal, t ≤ T → X t =ᵐ[μ] Z t)
    (hrY : 0 < rY) (hrZ : 0 < rZ)
    (hY :
      ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K rY (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) S))
    (hZ :
      ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K rZ (fun t : NNReal ↦ Z t ω) (Set.Icc (0 : NNReal) T)) :
    AreIndistinguishable μ
      (fun t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) ↦ Y t.1.toNNReal)
      (fun t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) ↦ Z t.1.toNNReal) := by
  let Yoverlap : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) → Ω → E :=
    fun t ω ↦ Y t.1.toNNReal ω
  let Zoverlap : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) → Ω → E :=
    fun t ω ↦ Z t.1.toNNReal ω
  -- Proof comment: first identify the two versions almost surely at each overlap time, then use
  -- Hölder control to obtain the right continuity required by Lemma 21.5.
  have hmod : AreModifications μ Yoverlap Zoverlap := by
    intro t
    have htle : (t : ℝ) ≤ ((min S T : NNReal) : ℝ) := t.2.2
    have ht : t.1.toNNReal ≤ min S T := by
      refine le_min ?_ ?_
      · have hts : (t : ℝ) ≤ (S : ℝ) := htle.trans (min_le_left _ _)
        simpa [Real.toNNReal_coe] using Real.toNNReal_mono hts
      · have htt : (t : ℝ) ≤ (T : ℝ) := htle.trans (min_le_right _ _)
        simpa [Real.toNNReal_coe] using Real.toNNReal_mono htt
    simpa [Yoverlap, Zoverlap] using
      aeEq_on_overlap_of_versionsMetric (μ := μ) hXY hXZ t.1.toNNReal ht
  have hYrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ),
          ContinuousWithinAt (processPath Yoverlap ω) (Set.Ici t) t := by
    -- Proof comment: each `Y` path is Hölder on `[0,S]`, so the restriction to the smaller
    -- overlap interval remains Hölder and hence right-continuous.
    filter_upwards with ω
    intro t
    rcases hY ω with ⟨K, hK⟩
    have hKoverlap :
        HolderOnWith K rY (fun s : NNReal ↦ Y s ω) (Set.Icc (0 : NNReal) (min S T)) :=
      hK.mono <| by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩
    simpa [Yoverlap, processPath_apply] using
      continuousWithinAt_realSubtypeIcc_of_holderOnWithMetric (T := min S T) hrY hKoverlap t
  have hZrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ),
          ContinuousWithinAt (processPath Zoverlap ω) (Set.Ici t) t := by
    -- Proof comment: the same overlap restriction argument applies to `Z`.
    filter_upwards with ω
    intro t
    rcases hZ ω with ⟨K, hK⟩
    have hKoverlap :
        HolderOnWith K rZ (fun s : NNReal ↦ Z s ω) (Set.Icc (0 : NNReal) (min S T)) :=
      hK.mono <| by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 (min_le_right _ _)⟩
    simpa [Zoverlap, processPath_apply] using
      continuousWithinAt_realSubtypeIcc_of_holderOnWithMetric (T := min S T) hrZ hKoverlap t
  exact
    ProbabilityTheory.indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
      (Ω := Ω)
      (E := E)
      (μ := μ)
      (I := Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ))
      (X := Yoverlap)
      (Y := Zoverlap)
      hmod Set.ordConnected_Icc hYrc hZrc

/-- Helper for Remark 21.7: a countable family of finite-horizon `E`-valued Hölder versions can
be patched outside one measurable null set so that all family members agree on every common
overlap interval. -/
lemma exists_masterPatchNullSet_of_holderVersionsMetric
    {μ : Measure Ω}
    {ι : Type*} [Countable ι]
    {X : NNReal → Ω → E} {T : ι → NNReal} {r : ι → ℝ≥0}
    {Y : ι → NNReal → Ω → E}
    (hmod : ∀ i, ∀ t : NNReal, t ≤ T i → X t =ᵐ[μ] Y i t)
    (hr : ∀ i, 0 < r i)
    (hY :
      ∀ i, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (r i) (fun t : NNReal ↦ Y i t ω) (Set.Icc (0 : NNReal) (T i))) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : ι, ∀ t : NNReal, t ≤ min (T i) (T j) → Y i t ω = Y j t ω := by
  have hpair :
      ∀ i j : ι, ∃ Nij : Set Ω, MeasurableSet Nij ∧ μ Nij = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ Nij →
          ∀ t : NNReal, t ≤ min (T i) (T j) → Y i t ω = Y j t ω := by
    intro i j
    rcases
      indistinguishable_on_overlap_of_holderVersionsMetric
        (μ := μ)
        (X := X)
        (Y := Y i)
        (Z := Y j)
        (S := T i)
        (T := T j)
        (rY := r i)
        (rZ := r j)
        (hXY := hmod i)
        (hXZ := hmod j)
        (hrY := hr i)
        (hrZ := hr j)
        (hY := hY i)
        (hZ := hY j) with
      ⟨Nij, hNij_meas, hNij_zero, hNij_sub⟩
    refine ⟨Nij, hNij_meas, hNij_zero, ?_⟩
    intro ω hω t ht
    -- Proof comment: the overlap indistinguishability witness already controls every common time,
    -- so outside its null set the two versions coincide pointwise on the overlap interval.
    by_contra hneq
    exact hω <| hNij_sub ⟨(t : ℝ), by simpa using ht⟩ <| by
      simpa using hneq
  let N : Set Ω := ⋃ ij : ι × ι, Classical.choose (hpair ij.1 ij.2)
  refine ⟨N, ?_, ?_, ?_⟩
  · -- Proof comment: the master bad set is a countable union of measurable pairwise-overlap null
    -- sets, so it is measurable.
    refine MeasurableSet.iUnion ?_
    intro ij
    exact (Classical.choose_spec (hpair ij.1 ij.2)).1
  · -- Proof comment: countability of the witness family keeps the union null.
    simpa [N] using
      measure_iUnion_null
        (μ := μ)
        (s := fun ij : ι × ι ↦ Classical.choose (hpair ij.1 ij.2))
        (fun ij ↦ (Classical.choose_spec (hpair ij.1 ij.2)).2.1)
  · intro ω hω i j t ht
    have hωpair : ω ∉ Classical.choose (hpair i j) := by
      intro hmem
      exact hω <| Set.mem_iUnion.2 ⟨(i, j), hmem⟩
    exact (Classical.choose_spec (hpair i j)).2.2 hωpair t ht

/-- Helper for Remark 21.7: pathwise Hölder control on `[0,T]` yields a deterministic Hölder
constant on a set of probability at least `1 - ε` in the metric-valued setting. -/
lemma exists_deterministicHolderConstant_of_pathwiseHolderOnIccMetric
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : NNReal → Ω → E} {T q γ : ℝ≥0}
    (hγq : γ ≤ q)
    (hY :
      ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K q (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℝ≥0,
      ENNReal.ofReal (1 - ε) ≤
        μ {ω | HolderOnWith K γ (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)} := by
  let A : ℕ → Set Ω := fun n ↦
    {ω | HolderOnWith (n : ℝ≥0) γ (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)}
  have hAmono : Monotone A := by
    intro n m hnm ω hω
    exact hω.mono_const (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm)
  have hAuniv : (⋃ n, A n) = Set.univ := by
    ext ω
    constructor
    · intro _
      simp
    · intro _
      rcases hY ω with ⟨Kq, hKq⟩
      rcases
        HolderOnWith.exists_holderOnWith_of_le
          (f := fun t : NNReal ↦ Y t ω)
          (r := q)
          (s := γ)
          (A := Set.Icc (0 : NNReal) T)
          ⟨Kq, hKq⟩
          hγq
          (Metric.isBounded_Icc (0 : NNReal) T) with
        ⟨Kγ, hKγ⟩
      let n : ℕ := Nat.ceil (Kγ : ℝ)
      have hKγn : Kγ ≤ n := by
        exact_mod_cast Nat.le_ceil (Kγ : ℝ)
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      exact hKγ.mono_const hKγn
  have htarget_lt : ENNReal.ofReal (1 - ε) < ⨆ n, μ (A n) := by
    rw [← hAmono.measure_iUnion (μ := μ), hAuniv, measure_univ]
    by_cases hε1 : ε ≤ 1
    · rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith)
    · have hneg : 1 - ε < 0 := by
        linarith
      simp [ENNReal.ofReal_eq_zero.2 hneg.le]
  rcases lt_iSup_iff.mp htarget_lt with ⟨n, hn⟩
  exact ⟨n, hn.le⟩

-- Proof sketch: unwrap the cube-owner predicate into the raw increment estimate required by
-- Exercise 21.1.1 by observing that the coordinate bounds `|x i| ≤ T` are exactly the cube
-- membership condition.
/-- Helper for Remark 21.7: a Kolmogorov bound on every closed cube `[-T, T]^d` yields the raw
moment estimate required by Exercise 21.1.1. -/
lemma momentBound_of_isKolmogorovProcessOnEuclideanClosedCube
    (μ : Measure Ω)
    {d : ℕ} {α β : ℝ≥0}
    {X : EuclideanSpace ℝ (Fin d) → Ω → E}
    (hX :
      ∀ T : ℝ≥0, 0 < T → ∃ C : ℝ≥0, IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∀ T : ℝ, 0 < T →
      ∃ C : ℝ≥0, ∀ s t : EuclideanSpace ℝ (Fin d),
        (∀ i : Fin d, |s i| ≤ T) →
        (∀ i : Fin d, |t i| ≤ T) →
          ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
            (C : ℝ≥0∞) * (ENNReal.ofReal ‖t - s‖) ^ (((d : ℝ≥0) + β : ℝ)) := by
  intro T hT
  rcases hX (Real.toNNReal T) (Real.toNNReal_pos.mpr hT) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro s t hs ht
  have hsCube : s ∈ euclideanClosedCube d (Real.toNNReal T : ℝ) := by
    -- Proof comment: the coordinatewise absolute-value bound is exactly the closed-cube
    -- membership predicate.
    simpa [euclideanClosedCube, Set.mem_Icc, abs_le, Real.toNNReal_of_nonneg hT.le] using hs
  have htCube : t ∈ euclideanClosedCube d (Real.toNNReal T : ℝ) := by
    -- Proof comment: the same coordinatewise rewriting identifies `t` with a cube point.
    simpa [euclideanClosedCube, Set.mem_Icc, abs_le, Real.toNNReal_of_nonneg hT.le] using ht
  -- Proof comment: once the points are recognized as cube elements, the owner increment estimate
  -- is already the desired raw moment bound after rewriting `edist` as `‖t - s‖`.
  simpa [edist_dist, dist_eq_norm, norm_sub_rev] using
    hC.increment_lintegral_le hsCube htCube

-- Proof sketch: translate the cube hypothesis to the Euclidean moment-bound theorem
-- `exists_locallyHolderWith_version_of_euclidean_moment_bound`, which already packages the
-- path-regularity conclusion via the owner predicate `HasLocallyHolderPaths`.
/-- Helper for Remark 21.7: for an `ℝ^d`-indexed process with values in a complete separable
metric space, if every cube restriction `[-T, T]^d` satisfies the multidimensional Kolmogorov
condition with exponents `α` and `d + β`, then for every Hölder exponent `γ < β / α` there exists
a version whose sample paths are locally Hölder-continuous of order `γ`. -/
theorem exists_locallyHolderContinuous_version_of_moment_bound_on_euclideanSpace
    (μ : Measure Ω) [IsProbabilityMeasure μ] [CompleteSpace E] [SecondCountableTopology E]
    {d : ℕ} {α β : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β)
    (γ : ℝ≥0) (hγ₀ : 0 < γ) (hγ : γ < β / α)
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (hX : ∀ T : ℝ≥0, 0 < T → ∃ C : ℝ≥0, IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      AreModifications μ X Y ∧
      HasLocallyHolderPaths γ Y := by
  -- Proof comment: Exercise 21.1.1 already gives the required Euclidean-space modification once
  -- the cube hypothesis is translated into the raw moment estimate format it expects.
  rcases
      exists_locallyHolderWith_version_of_euclidean_moment_bound
        (μ := μ)
        (X := X)
        (hα := hα)
        (hβ := hβ)
        (hγ₀ := hγ₀)
        (hγ := hγ)
        (hMoment :=
          momentBound_of_isKolmogorovProcessOnEuclideanClosedCube
            (μ := μ)
            (α := α)
            (β := β)
            (X := X)
            hX) with
    ⟨Y, hmod, hHolder⟩
  -- Proof comment: `AreModifications` is exactly the pointwise almost-everywhere equality package
  -- returned by Exercise 21.1.1.
  exact ⟨Y, hmod, hHolder⟩

section FiniteIntervalMetricVersion

variable {μ : Measure Ω} [IsProbabilityMeasure μ] [CompleteSpace E] [SecondCountableTopology E]

/-- Helper for Remark 21.7: a locally Hölder map of positive exponent between metric spaces is
continuous. -/
private lemma continuous_of_locallyHolderWithMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ≥0} {f : X → Y}
    (hq : 0 < q)
    (hf : LocallyHolderWith q f) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases hf x with ⟨s, hs, C, hC⟩
  -- Proof comment: a local Hölder witness is continuous on its neighborhood, so continuity at the
  -- center follows immediately.
  have hx : x ∈ s := mem_of_mem_nhds hs
  exact (hC.continuousOn hq x hx).continuousAt hs

/-- Helper for Remark 21.7: on a compact metric space, local Hölder control can be made uniform on
small distances for metric-valued maps. -/
private lemma exists_uniformLocalHolderBound_of_compactMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y] [CompactSpace X] [Nonempty X]
    {q : ℝ≥0} {f : X → Y}
    (hf : LocallyHolderWith q f) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ x y, dist x y < δ →
      dist (f x) (f y) ≤ C * dist x y ^ (q : ℝ) := by
  classical
  choose ε hε C hC using fun x => hf.exists_holderOnWith_ball x
  let U : X → Set X := fun x ↦ Metric.ball x (ε x / 2)
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    exact Metric.mem_ball_self (half_pos (hε x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i : {x // x ∈ t}, U i.1 := by
    intro x hx
    rcases Set.mem_iUnion.1 (ht hx) with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hxi with ⟨hi, hxU⟩
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxU⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun _ => Metric.isOpen_ball) hcover'
  let C₀ : ℝ≥0 := t.sup C
  refine ⟨δ, hδpos, C₀, ?_⟩
  intro x y hxy
  -- Proof comment: the Lebesgue radius places both points in one witness ball, and the finite
  -- supremum of the local constants yields a uniform small-scale estimate.
  have hxδ : x ∈ Metric.ball x δ := Metric.mem_ball_self hδpos
  rcases hδ x (by simp) with ⟨i, hi⟩
  have hxU : x ∈ U i.1 := hi hxδ
  have hyU : y ∈ U i.1 := hi <| by
    simpa [dist_comm] using Metric.mem_ball.2 hxy
  have hhalf_le : ε i.1 / 2 ≤ ε i.1 := by
    nlinarith [hε i.1]
  have hxBall : x ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hxU).trans_le hhalf_le
  have hyBall : y ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hyU).trans_le hhalf_le
  have hlocal : dist (f x) (f y) ≤ C i.1 * dist x y ^ (q : ℝ) := by
    have hlocal' :
        ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (C i.1 * dist x y ^ (q : ℝ)) := by
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using
        hC i.1 x hxBall y hyBall
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlocal'
  have hCi : C i.1 ≤ C₀ := Finset.le_sup i.2
  calc
    dist (f x) (f y) ≤ C i.1 * dist x y ^ (q : ℝ) := hlocal
    _ ≤ C₀ * dist x y ^ (q : ℝ) := by
          gcongr

/-- Helper for Remark 21.7: on a compact metric space, positive local Hölder control upgrades to a
global Hölder estimate for metric-valued maps. -/
private lemma exists_holderWith_of_isCompactMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ≥0} {f : X → Y}
    (hq : 0 < q)
    [CompactSpace X] :
    LocallyHolderWith q f → ∃ C : ℝ≥0, HolderWith C q f := by
  intro hf
  classical
  by_cases h_nonempty : Nonempty X
  · letI := h_nonempty
    have hcont : Continuous f := continuous_of_locallyHolderWithMetric hq hf
    obtain ⟨δ, hδpos, Cnear, hnear⟩ := exists_uniformLocalHolderBound_of_compactMetric hf
    let D : ℝ := Metric.diam (Set.range f)
    have hdiam : ∀ x y : X, dist (f x) (f y) ≤ D := by
      intro x y
      exact Metric.dist_le_diam_of_mem (isCompact_range hcont).isBounded ⟨x, rfl⟩ ⟨y, rfl⟩
    let Cfar : ℝ≥0 := ⟨D / δ ^ (q : ℝ), by positivity⟩
    refine ⟨max Cnear Cfar, ?_⟩
    intro x y
    -- Proof comment: nearby points use the uniform compactness estimate, while far points are
    -- controlled by the diameter of the compact image.
    by_cases hxy : dist x y < δ
    · have hlocal : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
        exact (hnear x y hxy).trans <| by
          gcongr
          exact le_max_left _ _
      have hlocal' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (q : ℝ)) :=
        ENNReal.ofReal_le_ofReal hlocal
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hlocal'
    · have hδle : δ ≤ dist x y := le_of_not_gt hxy
      have hδpow_pos : 0 < δ ^ (q : ℝ) := by
        positivity
      have hpow : δ ^ (q : ℝ) ≤ dist x y ^ (q : ℝ) := by
        gcongr
      have hfar : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
        calc
          dist (f x) (f y) ≤ D := hdiam x y
          _ = (D / δ ^ (q : ℝ)) * δ ^ (q : ℝ) := by
                field_simp [hδpow_pos.ne']
          _ ≤ (D / δ ^ (q : ℝ)) * dist x y ^ (q : ℝ) := by
                gcongr
          _ = Cfar * dist x y ^ (q : ℝ) := by
                simp [Cfar]
          _ ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
                gcongr
                exact le_max_right _ _
      have hfar' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (q : ℝ)) :=
        ENNReal.ofReal_le_ofReal hfar
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hfar'
  · letI : IsEmpty X := ⟨fun x ↦ h_nonempty ⟨x⟩⟩
    exact ⟨0, HolderWith.of_isEmpty⟩

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Remark 21.7: the ambient Euclidean distance on a closed-cube subtype agrees with
the subtype distance. -/
private lemma edist_euclideanClosedCubeSubtype_eq
    {R : ℝ≥0} (s t : euclideanClosedCube 1 (R : ℝ)) :
    edist ((s : E1)) ((t : E1)) = edist s t := by
  rfl

/-- Helper for Remark 21.7: embed `ℝ` into `ℝ¹` along the unique coordinate axis. -/
private noncomputable def realToEuclidean1 : ℝ → E1 :=
  fun t ↦ EuclideanSpace.single 0 t

/-- Helper for Remark 21.7: the one-dimensional Euclidean embedding preserves distance. -/
private lemma dist_realToEuclidean1 (x y : ℝ) :
    dist (realToEuclidean1 x) (realToEuclidean1 y) = dist x y := by
  simp [realToEuclidean1]

/-- Helper for Remark 21.7: every point of `ℝ¹` is the image of its unique coordinate. -/
private lemma euclidean1_eq_realToEuclidean1 (x : E1) :
    x = realToEuclidean1 (x 0) := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp [realToEuclidean1]

/-- Helper for Remark 21.7: in dimension one, the ambient Euclidean distance is exactly the
distance of the unique coordinate. -/
private lemma dist_coord_zero_eq_dist (x y : E1) :
    dist (x 0) (y 0) = dist x y := by
  rw [euclidean1_eq_realToEuclidean1 x, euclidean1_eq_realToEuclidean1 y]
  simpa using (dist_realToEuclidean1 (x 0) (y 0)).symm

/-- Helper for Remark 21.7: clip a real time into the finite interval `[0,T]`. -/
private noncomputable def clipRealToIcc (T : NNReal) (x : ℝ) : ℝ :=
  max 0 (min (T : ℝ) x)

/-- Helper for Remark 21.7: the clipped real time, viewed as an element of `ℝ≥0`. -/
private noncomputable def clipToIcc (T : NNReal) (x : ℝ) : NNReal :=
  Real.toNNReal (clipRealToIcc T x)

/-- Helper for Remark 21.7: the clipping map lands in the target interval `[0,T]`. -/
private lemma clipToIcc_mem_Icc (T : NNReal) (x : ℝ) :
    clipToIcc T x ∈ Set.Icc (0 : NNReal) T := by
  constructor
  · simp [clipToIcc]
  · have hclip_le : clipRealToIcc T x ≤ (T : ℝ) := by
      unfold clipRealToIcc
      exact max_le (by exact_mod_cast (zero_le T)) (min_le_left _ _)
    simpa [clipToIcc] using Real.toNNReal_mono hclip_le

/-- Helper for Remark 21.7: clipping fixes times that already lie in `[0,T]`. -/
private lemma clipToIcc_eq_of_le {T t : NNReal} (ht : t ≤ T) :
    clipToIcc T (t : ℝ) = t := by
  unfold clipToIcc clipRealToIcc
  have hmin : min (T : ℝ) (t : ℝ) = t := min_eq_right ht
  simp [hmin]

/-- Helper for Remark 21.7: clipping to `[0,T]` is 1-Lipschitz. -/
private lemma dist_clipToIcc_le (T : NNReal) (x y : ℝ) :
    dist (clipToIcc T x) (clipToIcc T y) ≤ dist x y := by
  have hclipReal :
      LipschitzWith 1 (clipRealToIcc T) := by
    unfold clipRealToIcc
    exact (LipschitzWith.id.const_min (T : ℝ)).const_max 0
  have htoNN :
      dist (clipToIcc T x) (clipToIcc T y) ≤
        dist (clipRealToIcc T x) (clipRealToIcc T y) := by
    simpa [clipToIcc] using
      Real.lipschitzWith_toNNReal.dist_le_mul (clipRealToIcc T x) (clipRealToIcc T y)
  exact htoNN.trans <| by
    simpa using hclipReal.dist_le_mul x y

/-- Helper for Remark 21.7: a finite-interval Kolmogorov bound for an `E`-valued process produces
a finite-horizon version whose sample paths are Hölder on `[0,T]`. -/
lemma exists_holderVersion_of_isKolmogorovProcessOnIccMetric
    {X : NNReal → Ω → E} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq0 : 0 < q)
    (hq : (q : ℝ) < β / α) :
    ∃ Y : NNReal → Ω → E,
      (∀ t : NNReal, t ≤ T → X t =ᵐ[μ] Y t) ∧
      (∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K q (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)) := by
  let Xclip : E1 → Ω → E := fun z ω ↦ X (clipToIcc T (z 0)) ω
  have hclipCube :
      ∀ R : ℝ≥0, 0 < R → ∃ C' : ℝ≥0,
        IsKolmogorovProcessOnEuclideanClosedCube μ Xclip R α β C' := by
    intro R hR
    refine ⟨C, ?_⟩
    refine
      { measurablePair := ?_
        kolmogorovCondition := ?_
        p_pos := ?_
        q_pos := ?_ }
    · intro s t
      have hsIcc := clipToIcc_mem_Icc T (s.1 0)
      have htIcc := clipToIcc_mem_Icc T (t.1 0)
      -- Proof comment: the clipped one-dimensional process is measured by evaluating the original
      -- interval-restricted Kolmogorov process at the clipped times.
      simpa [Xclip] using
        h.isKolmogorovProcess.measurablePair
          ⟨clipToIcc T (s.1 0), hsIcc⟩
          ⟨clipToIcc T (t.1 0), htIcc⟩
    · intro s t
      have hsIcc := clipToIcc_mem_Icc T (s.1 0)
      have htIcc := clipToIcc_mem_Icc T (t.1 0)
      have hclipdist :
          edist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ≤ edist (s : E1) (t : E1) := by
        have hclipdist' :
            dist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ≤ dist (s : E1) (t : E1) := by
          calc
              dist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ≤ dist (s.1 0) (t.1 0) :=
                dist_clipToIcc_le T (s.1 0) (t.1 0)
            _ = dist (s : E1) (t : E1) := dist_coord_zero_eq_dist s t
        simpa [edist_dist] using ENNReal.ofReal_le_ofReal hclipdist'
      have hclipdist_sub :
          edist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ≤ edist s t := by
        simpa [edist_euclideanClosedCubeSubtype_eq] using hclipdist
      have hclipdist_pow :
          edist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ^ (((1 : ℝ≥0) : ℝ) + (β : ℝ)) ≤
            edist s t ^ (((1 : ℝ≥0) : ℝ) + (β : ℝ)) := by
        exact ENNReal.rpow_le_rpow hclipdist_sub (by positivity)
      -- Proof comment: the clipped coordinate map is 1-Lipschitz, so the original interval
      -- increment estimate upgrades directly to the one-dimensional cube estimate.
      have hFinal :
          ∫⁻ ω, edist (Xclip s ω) (Xclip t ω) ^ (α : ℝ) ∂μ ≤
            (C : ℝ≥0∞) * edist s t ^ (((1 : ℝ≥0) : ℝ) + (β : ℝ)) := by
        calc
          ∫⁻ ω, edist (Xclip s ω) (Xclip t ω) ^ (α : ℝ) ∂μ
              ≤ (C : ℝ≥0∞) *
                  edist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ^ (((1 : ℝ≥0) + β : ℝ)) := by
                    simpa [Xclip, edist_comm] using
                      h.increment_lintegral_le
                        (s := clipToIcc T (s.1 0))
                        (t := clipToIcc T (t.1 0))
                        hsIcc.2
                        htIcc.2
          _ = (C : ℝ≥0∞) *
                edist (clipToIcc T (s.1 0)) (clipToIcc T (t.1 0)) ^
                  (((1 : ℝ≥0) : ℝ) + (β : ℝ)) := by
                rfl
          _ ≤ (C : ℝ≥0∞) * edist s t ^ (((1 : ℝ≥0) : ℝ) + (β : ℝ)) := by
                simpa [mul_comm] using
                  mul_le_mul_left hclipdist_pow (C : ℝ≥0∞)
      simpa using hFinal
    · exact_mod_cast h.alpha_pos
    · have hβ : 0 < (β : ℝ) := by
        exact_mod_cast h.beta_pos
      linarith
  rcases
    exists_locallyHolderContinuous_version_of_moment_bound_on_euclideanSpace
      (μ := μ)
      (d := 1)
      (α := α)
      (β := β)
      (hα := h.alpha_pos)
      (hβ := h.beta_pos)
      (γ := q)
      (hγ₀ := hq0)
      (hγ := hq)
      (X := Xclip)
      hclipCube with
    ⟨YEuclid, hmodEuclid, hHolderEuclid⟩
  let Y : NNReal → Ω → E := fun t ω ↦ YEuclid (realToEuclidean1 (t : ℝ)) ω
  refine ⟨Y, ?_, ?_⟩
  · intro t htT
    -- Proof comment: on `[0,T]`, the clipped one-dimensional process agrees with the original
    -- process, so the Euclidean modification restricts back to a finite-horizon version.
    have hclipEq : clipToIcc T (t : ℝ) = t := clipToIcc_eq_of_le htT
    simpa [Y, Xclip, realToEuclidean1, hclipEq] using
      hmodEuclid (realToEuclidean1 (t : ℝ))
  · intro ω
    let fω : Set.Icc (0 : NNReal) T → E :=
      fun t ↦ YEuclid (realToEuclidean1 ((t : NNReal) : ℝ)) ω
    have hlocEuclid : LocallyHolderWith q (fun z : E1 ↦ YEuclid z ω) := by
      intro z
      simpa using hHolderEuclid ω z
    have hlocIcc : LocallyHolderWith q fω := by
      intro x
      rcases hlocEuclid.exists_holderOnWith_ball
          (realToEuclidean1 ((x : NNReal) : ℝ)) with
        ⟨ε, hε, C, hC⟩
      refine ⟨Metric.ball x ε, Metric.ball_mem_nhds _ hε, C, ?_⟩
      intro u hu v hv
      have huE :
          realToEuclidean1 ((u : NNReal) : ℝ) ∈
            Metric.ball (realToEuclidean1 ((x : NNReal) : ℝ)) ε := by
        exact Metric.mem_ball.2 <| by
          simpa [dist_realToEuclidean1] using Metric.mem_ball.1 hu
      have hvE :
          realToEuclidean1 ((v : NNReal) : ℝ) ∈
            Metric.ball (realToEuclidean1 ((x : NNReal) : ℝ)) ε := by
        exact Metric.mem_ball.2 <| by
          simpa [dist_realToEuclidean1] using Metric.mem_ball.1 hv
      -- Proof comment: the map `t ↦ (t)` from the interval subtype into `ℝ¹` is an isometry, so
      -- the Euclidean local Hölder estimate transfers verbatim to the interval subtype.
      simpa [fω, edist_dist, dist_realToEuclidean1] using
        hC
          (realToEuclidean1 ((u : NNReal) : ℝ))
          huE
          (realToEuclidean1 ((v : NNReal) : ℝ))
          hvE
    letI : CompactSpace (Set.Icc (0 : NNReal) T) := by
      refine isCompact_iff_compactSpace.mp ?_
      simpa using (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T))
    rcases exists_holderWith_of_isCompactMetric (q := q) hq0 hlocIcc with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    -- Proof comment: a global Hölder estimate on the interval subtype is exactly the desired
    -- `HolderOnWith` statement on `[0,T]`.
    intro s hs t ht
    simpa [Y, fω] using hK ⟨s, hs⟩ ⟨t, ht⟩

end FiniteIntervalMetricVersion

section MetricPatchedProcess

variable {μ : Measure Ω} [IsProbabilityMeasure μ] [CompleteSpace E] [SecondCountableTopology E]

/-- Helper for Remark 21.7: a probability space cannot be empty. -/
private lemma nonempty_of_isProbabilityMeasure
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Nonempty Ω := by
  by_contra hΩ
  letI : IsEmpty Ω := not_nonempty_iff.mp hΩ
  have hUnivEmpty : (Set.univ : Set Ω) = ∅ := by
    ext x
    exact False.elim (isEmptyElim x)
  have h0 : μ Set.univ = 0 := by
    simp [hUnivEmpty]
  have h1 : μ Set.univ = 1 := by
    simp
  simp [h0] at h1

/-- Helper for Remark 21.7: choose a fallback value for the patched process from the original
process at time `0`. -/
private noncomputable def defaultValueOfProcess
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : NNReal → Ω → E) : E :=
  X 0 (Classical.choice (nonempty_of_isProbabilityMeasure (μ := μ)))

/-- Helper for Remark 21.7: metric-valued witness slots record an integer horizon, a positive
rational exponent, and the corresponding finite-horizon Kolmogorov data. -/
private def WitnessSlotMetric (μ : Measure Ω) (X : NNReal → Ω → E) : Type :=
  {iq : ℕ × PositiveRatExponent //
    ∃ α β C : ℝ≥0,
      IsKolmogorovProcessOnIcc μ X iq.1 α β C ∧ ((positiveRatExponent iq.2 : ℝ)) < β / α}

/-- Helper for Remark 21.7: the patched metric family is indexed by baseline integer horizons and
admissible witness slots. -/
private abbrev FamilyIndexMetric (μ : Measure Ω) (X : NNReal → Ω → E) :=
  Sum ℕ (WitnessSlotMetric μ X)

/-- Helper for Remark 21.7: admissible metric witness slots form a countable type. -/
private instance witnessSlotMetricCountable {X : NNReal → Ω → E} :
    Countable (WitnessSlotMetric μ X) := by
  classical
  change Countable {iq : ℕ × PositiveRatExponent //
    ∃ α β C : ℝ≥0,
      IsKolmogorovProcessOnIcc μ X iq.1 α β C ∧ ((positiveRatExponent iq.2 : ℝ)) < β / α}
  infer_instance

/-- Helper for Remark 21.7: the metric patched-family index type is countable. -/
private instance familyIndexMetricCountable {X : NNReal → Ω → E} :
    Countable (FamilyIndexMetric μ X) := by
  classical
  infer_instance

/-- Helper for Remark 21.7: each metric family index carries the interval on which its version is
defined. -/
private def familyHorizonMetric {X : NNReal → Ω → E} : FamilyIndexMetric μ X → NNReal :=
  Sum.elim (fun n ↦ n) (fun w ↦ w.1.1)

/-- Helper for Remark 21.7: each metric family index carries the Hölder exponent of its version. -/
private def familyExponentMetric {X : NNReal → Ω → E} (rBase : ℕ → ℝ≥0) :
    FamilyIndexMetric μ X → ℝ≥0 :=
  Sum.elim rBase (fun w ↦ positiveRatExponent w.1.2)

/-- Helper for Remark 21.7: evaluate the baseline or witness version attached to a metric family
index. -/
private def familyVersionMetric {X : NNReal → Ω → E}
    (YBase : ℕ → NNReal → Ω → E)
    (YWitness : WitnessSlotMetric μ X → NNReal → Ω → E) :
    FamilyIndexMetric μ X → NNReal → Ω → E :=
  Sum.elim YBase YWitness

/-- Helper for Remark 21.7: the baseline metric family member used to define the patched process
at time `t`. -/
private def baseIndexOfMetric {X : NNReal → Ω → E} (t : NNReal) : FamilyIndexMetric μ X :=
  Sum.inl (Nat.ceil (t : ℝ))

/-- Helper for Remark 21.7: set membership is classically decidable in the metric patched-process
branching definition. -/
private local instance decidableMemSetMetric (N : Set Ω) :
    DecidablePred (fun ω : Ω ↦ ω ∈ N) :=
  Classical.decPred _

/-- Helper for Remark 21.7: the global `E`-valued process obtained by patching the baseline family
outside one master null set. -/
private def patchedProcessMetric {X : NNReal → Ω → E}
    (default : E)
    (YBase : ℕ → NNReal → Ω → E)
    (YWitness : WitnessSlotMetric μ X → NNReal → Ω → E)
    (N : Set Ω) :
    NNReal → Ω → E :=
  fun t ω ↦
    if ω ∈ N then
      default
    else
      familyVersionMetric (μ := μ) (X := X) YBase YWitness
        (baseIndexOfMetric (μ := μ) (X := X) t) t ω

/-- Helper for Remark 21.7: package the baseline metric family together with the countable
admissible witness family. -/
private structure HolderFamiliesDataMetric (μ : Measure Ω) (X : NNReal → Ω → E) where
  rBase : ℕ → ℝ≥0
  YBase : ℕ → NNReal → Ω → E
  YWitness : WitnessSlotMetric μ X → NNReal → Ω → E
  hrBasePos : ∀ n : ℕ, 0 < rBase n
  hYBaseMod : ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t
  hYBaseHolder :
    ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n)
  hYWitnessMod :
    ∀ w : WitnessSlotMetric μ X, ∀ t : NNReal, t ≤ w.1.1 → X t =ᵐ[μ] YWitness w t
  hYWitnessHolder :
    ∀ w : WitnessSlotMetric μ X, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (positiveRatExponent w.1.2)
        (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)

/-- Helper for Remark 21.7: package the patched metric modification and the overlap API needed for
the final theorem. -/
private structure PatchedProcessDataMetric (μ : Measure Ω) (X : NNReal → Ω → E) where
  default : E
  rBase : ℕ → ℝ≥0
  YBase : ℕ → NNReal → Ω → E
  YWitness : WitnessSlotMetric μ X → NNReal → Ω → E
  N : Set Ω
  hrBasePos : ∀ n : ℕ, 0 < rBase n
  hYBaseMod : ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t
  hYBaseHolder :
    ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n)
  hYWitnessHolder :
    ∀ w : WitnessSlotMetric μ X, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (positiveRatExponent w.1.2)
        (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)
  hBaseIndexLe :
    ∀ t : NNReal,
      t ≤ familyHorizonMetric (μ := μ) (X := X) (baseIndexOfMetric (μ := μ) (X := X) t)
  hNZero : μ N = 0
  hModXtilde :
    AreModifications μ X (patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N)
  hPatch :
    ∀ ⦃ω : Ω⦄, ω ∉ N →
      ∀ i j : FamilyIndexMetric (μ := μ) X, ∀ t : NNReal,
        t ≤ min (familyHorizonMetric (μ := μ) (X := X) i)
          (familyHorizonMetric (μ := μ) (X := X) j) →
          familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω =
            familyVersionMetric (μ := μ) (X := X) YBase YWitness j t ω

/-- Helper for Remark 21.7: package the finite-horizon metric versions needed for the patched
construction. -/
private noncomputable def exists_holderFamilies_of_kolmogorovBoundsMetric
    {X : NNReal → Ω → E}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    HolderFamiliesDataMetric (μ := μ) X := by
  classical
  let αBase : ℕ → ℝ≥0 := fun n ↦ Classical.choose (hbound n)
  let βBase : ℕ → ℝ≥0 := fun n ↦ Classical.choose (Classical.choose_spec (hbound n))
  let CBase : ℕ → ℝ≥0 := fun n ↦
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hbound n)))
  have hKolBase : ∀ n : ℕ, IsKolmogorovProcessOnIcc μ X n (αBase n) (βBase n) (CBase n) := by
    intro n
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hbound n)))
  let rBase : ℕ → ℝ≥0 := fun n ↦ βBase n / (2 * αBase n)
  have hrBasePos : ∀ n : ℕ, 0 < rBase n := by
    intro n
    -- Proof comment: the baseline exponent is a fixed positive fraction of `β / α`.
    dsimp [rBase]
    have hα : 0 < αBase n := (hKolBase n).alpha_pos
    have hβ : 0 < βBase n := (hKolBase n).beta_pos
    positivity
  have hrBaseLt : ∀ n : ℕ, ((rBase n : ℝ≥0) : ℝ) < βBase n / αBase n := by
    intro n
    -- Proof comment: dividing by `2 * α` keeps the baseline exponent below the admissible
    -- threshold `β / α`.
    have hα : 0 < (αBase n : ℝ) := by
      exact_mod_cast (hKolBase n).alpha_pos
    have hβ : 0 < (βBase n : ℝ) := by
      exact_mod_cast (hKolBase n).beta_pos
    have htwoα : 0 < (((2 : ℝ≥0) * αBase n : ℝ)) := by
      positivity
    have hαlt : (αBase n : ℝ) < (((2 : ℝ≥0) * αBase n : ℝ)) := by
      calc
        (αBase n : ℝ) < (αBase n : ℝ) + (αBase n : ℝ) := by linarith
        _ = (((2 : ℝ≥0) * αBase n : ℝ)) := by
          norm_num [two_mul]
    change (βBase n : ℝ) / ((2 : ℝ≥0) * αBase n) < (βBase n : ℝ) / (αBase n : ℝ)
    exact (div_lt_div_iff_of_pos_left hβ htwoα hα).2 hαlt
  let YBase : ℕ → NNReal → Ω → E := fun n ↦
    Classical.choose <|
      exists_holderVersion_of_isKolmogorovProcessOnIccMetric
        (μ := μ)
        (X := X)
        (T := n)
        (α := αBase n)
        (β := βBase n)
        (C := CBase n)
        (q := rBase n)
        (hKolBase n)
        (hrBasePos n)
        (hrBaseLt n)
  have hYBaseSpec :
      ∀ n : ℕ,
        (∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t) ∧
          (∀ ω : Ω, ∃ K : ℝ≥0,
            HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n)) := by
    intro n
    -- Proof comment: each baseline family member is the finite-horizon metric version produced
    -- at the baseline exponent `β / (2α)`.
    exact Classical.choose_spec <|
      exists_holderVersion_of_isKolmogorovProcessOnIccMetric
        (μ := μ)
        (X := X)
        (T := n)
        (α := αBase n)
        (β := βBase n)
        (C := CBase n)
        (q := rBase n)
        (hKolBase n)
        (hrBasePos n)
        (hrBaseLt n)
  let witnessAlpha : WitnessSlotMetric (μ := μ) X → ℝ≥0 := fun w ↦ Classical.choose w.2
  let witnessBeta : WitnessSlotMetric (μ := μ) X → ℝ≥0 := fun w ↦
    Classical.choose (Classical.choose_spec w.2)
  let witnessC : WitnessSlotMetric (μ := μ) X → ℝ≥0 := fun w ↦
    Classical.choose (Classical.choose_spec (Classical.choose_spec w.2))
  have hWitnessData :
      ∀ w : WitnessSlotMetric (μ := μ) X,
        IsKolmogorovProcessOnIcc μ X w.1.1 (witnessAlpha w) (witnessBeta w) (witnessC w) ∧
          ((positiveRatExponent w.1.2 : ℝ)) < witnessBeta w / witnessAlpha w := by
    intro w
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec w.2))
  let YWitness : WitnessSlotMetric (μ := μ) X → NNReal → Ω → E := fun w ↦
    Classical.choose <|
      exists_holderVersion_of_isKolmogorovProcessOnIccMetric
        (μ := μ)
        (X := X)
        (T := w.1.1)
        (α := witnessAlpha w)
        (β := witnessBeta w)
        (C := witnessC w)
        (q := positiveRatExponent w.1.2)
        (hWitnessData w).1
        (positiveRatExponent_pos w.1.2)
        (hWitnessData w).2
  have hYWitnessSpec :
      ∀ w : WitnessSlotMetric (μ := μ) X,
        (∀ t : NNReal, t ≤ w.1.1 → X t =ᵐ[μ] YWitness w t) ∧
          (∀ ω : Ω, ∃ K : ℝ≥0,
            HolderOnWith K (positiveRatExponent w.1.2)
              (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)) := by
    intro w
    -- Proof comment: witness family members use the positive rational exponent stored in the
    -- witness slot itself.
    exact Classical.choose_spec <|
      exists_holderVersion_of_isKolmogorovProcessOnIccMetric
        (μ := μ)
        (X := X)
        (T := w.1.1)
        (α := witnessAlpha w)
        (β := witnessBeta w)
        (C := witnessC w)
        (q := positiveRatExponent w.1.2)
        (hWitnessData w).1
        (positiveRatExponent_pos w.1.2)
        (hWitnessData w).2
  refine
    { rBase := rBase
      YBase := YBase
      YWitness := YWitness
      hrBasePos := hrBasePos
      hYBaseMod := fun n ↦ (hYBaseSpec n).1
      hYBaseHolder := fun n ↦ (hYBaseSpec n).2
      hYWitnessMod := fun w ↦ (hYWitnessSpec w).1
      hYWitnessHolder := fun w ↦ (hYWitnessSpec w).2 }

/-- Helper for Remark 21.7: a countable family of finite-horizon metric-valued Hölder versions
patches into one global modification outside a master null set. -/
private noncomputable def exists_masterPatch_of_holderFamiliesMetric
    {X : NNReal → Ω → E}
    (data : HolderFamiliesDataMetric (μ := μ) X) :
    PatchedProcessDataMetric (μ := μ) X := by
  classical
  let Y := familyVersionMetric (μ := μ) (X := X) data.YBase data.YWitness
  let r := familyExponentMetric (μ := μ) (X := X) data.rBase
  let default := defaultValueOfProcess (μ := μ) X
  have hmod :
      ∀ i : FamilyIndexMetric (μ := μ) X,
        ∀ t : NNReal, t ≤ familyHorizonMetric (μ := μ) (X := X) i → X t =ᵐ[μ] Y i t := by
    intro i t ht
    -- Proof comment: each metric family index is either a baseline horizon or a witness slot,
    -- so the modification property is read from the corresponding packaged field.
    cases i with
    | inl n =>
        simpa [Y, familyVersionMetric, familyHorizonMetric] using data.hYBaseMod n t ht
    | inr w =>
        simpa [Y, familyVersionMetric, familyHorizonMetric] using data.hYWitnessMod w t ht
  have hr :
      ∀ i : FamilyIndexMetric (μ := μ) X, 0 < r i := by
    intro i
    cases i with
    | inl n =>
        simpa [r, familyExponentMetric] using data.hrBasePos n
    | inr w =>
        simpa [r, familyExponentMetric] using positiveRatExponent_pos w.1.2
  have hY :
      ∀ i : FamilyIndexMetric (μ := μ) X, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (r i) (fun t : NNReal ↦ Y i t ω)
          (Set.Icc (0 : NNReal) (familyHorizonMetric (μ := μ) (X := X) i)) := by
    intro i ω
    cases i with
    | inl n =>
        simpa [Y, r, familyVersionMetric, familyExponentMetric, familyHorizonMetric] using
          data.hYBaseHolder n ω
    | inr w =>
        simpa [Y, r, familyVersionMetric, familyExponentMetric, familyHorizonMetric] using
          data.hYWitnessHolder w ω
  let patchWitness :=
    exists_masterPatchNullSet_of_holderVersionsMetric
      (μ := μ)
      (X := X)
      (T := familyHorizonMetric (μ := μ) (X := X))
      (r := r)
      (Y := Y)
      hmod
      hr
      hY
  let N : Set Ω := Classical.choose patchWitness
  have hNZero : μ N = 0 := (Classical.choose_spec patchWitness).2.1
  have hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndexMetric (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizonMetric (μ := μ) (X := X) i)
            (familyHorizonMetric (μ := μ) (X := X) j) →
            Y i t ω = Y j t ω :=
    (Classical.choose_spec patchWitness).2.2
  refine
    { default := default
      rBase := data.rBase
      YBase := data.YBase
      YWitness := data.YWitness
      N := N
      hrBasePos := data.hrBasePos
      hYBaseMod := data.hYBaseMod
      hYBaseHolder := data.hYBaseHolder
      hYWitnessHolder := data.hYWitnessHolder
      hBaseIndexLe := ?_
      hNZero := hNZero
      hModXtilde := ?_
      hPatch := ?_ }
  · intro t
    -- Proof comment: `baseIndexOfMetric t` is the ceiling horizon, which always contains `t`.
    change t ≤ (Nat.ceil (t : ℝ) : NNReal)
    exact_mod_cast Nat.le_ceil (t : ℝ)
  · intro t
    -- Proof comment: off the master null set, the patched metric process equals the baseline
    -- family member at the ceiling horizon, which is already a version of `X`.
    have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
      rw [ae_iff]
      simpa using hNZero
    have hceil : t ≤ (Nat.ceil (t : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil (t : ℝ)
    filter_upwards [hNae, data.hYBaseMod (Nat.ceil (t : ℝ)) t hceil] with ω hω hXt
    have hpatched :
        patchedProcessMetric (μ := μ) (X := X) default data.YBase data.YWitness N t ω =
          data.YBase (Nat.ceil (t : ℝ)) t ω := by
      simp [patchedProcessMetric, hω, familyVersionMetric, baseIndexOfMetric]
    exact hXt.trans hpatched.symm
  · intro ω hω i j t ht
    simpa [Y] using hPatch hω i j t ht

/-- Helper for Remark 21.7: construct the countable patched metric modification together with the
baseline and witness families used in the final local Hölder and deterministic-event arguments. -/
private noncomputable def exists_patchedProcessDataMetric
    {X : NNReal → Ω → E}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    PatchedProcessDataMetric (μ := μ) X := by
  -- Proof comment: first package the finite-horizon metric families, then apply the one-time
  -- master patching construction.
  exact
    exists_masterPatch_of_holderFamiliesMetric
      (μ := μ)
      (X := X)
      (exists_holderFamilies_of_kolmogorovBoundsMetric (μ := μ) (X := X) hbound)

/-- Helper for Remark 21.7: outside the master null set, the patched metric process is already in
the baseline normal form indexed by `baseIndexOfMetric t`. -/
private lemma patchedProcessMetric_eq_familyVersion_baseIndex_offNull
    {X : NNReal → Ω → E}
    {default : E}
    {YBase : ℕ → NNReal → Ω → E}
    {YWitness : WitnessSlotMetric (μ := μ) X → NNReal → Ω → E}
    {N : Set Ω} {ω : Ω}
    (hω : ω ∉ N)
    (t : NNReal) :
    patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω =
      familyVersionMetric (μ := μ) (X := X) YBase YWitness
        (baseIndexOfMetric (μ := μ) (X := X) t) t ω := by
  let _ : IsProbabilityMeasure μ := inferInstance
  let _ : CompleteSpace E := inferInstance
  let _ : SecondCountableTopology E := inferInstance
  -- Proof comment: the metric patch definition only branches on membership in the master null
  -- set.
  simp [patchedProcessMetric, hω]

/-- Helper for Remark 21.7: outside the master null set, the patched metric process agrees with
any family member on that member's time interval. -/
private lemma patchedProcessMetric_eqOn_familyMember_offNull
    {X : NNReal → Ω → E}
    {default : E}
    {YBase : ℕ → NNReal → Ω → E}
    {YWitness : WitnessSlotMetric (μ := μ) X → NNReal → Ω → E}
    {N : Set Ω}
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizonMetric (μ := μ) (X := X) (baseIndexOfMetric (μ := μ) (X := X) t))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndexMetric (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizonMetric (μ := μ) (X := X) i)
            (familyHorizonMetric (μ := μ) (X := X) j) →
            familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersionMetric (μ := μ) (X := X) YBase YWitness j t ω)
    {ω : Ω}
    (hω : ω ∉ N)
    (i : FamilyIndexMetric (μ := μ) X) :
    Set.EqOn
      (fun t : NNReal ↦ patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω)
      (fun t : NNReal ↦ familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω)
      (Set.Icc (0 : NNReal) (familyHorizonMetric (μ := μ) (X := X) i)) := by
  -- Proof comment: normalize the patched process to its baseline branch and then use the overlap
  -- equality furnished by the master null-set construction.
  intro t ht
  calc
    patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω =
        familyVersionMetric (μ := μ) (X := X) YBase YWitness
          (baseIndexOfMetric (μ := μ) (X := X) t) t ω :=
      patchedProcessMetric_eq_familyVersion_baseIndex_offNull (μ := μ) (X := X) hω t
    _ = familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω :=
      hPatch hω (baseIndexOfMetric (μ := μ) (X := X) t) i t <|
        le_min (hBaseIndexLe t) ht.2

/-- Helper for Remark 21.7: outside the master null set, the patched metric process is locally
`γ`-Hölder once an admissible finite-horizon witness exponent is chosen. -/
lemma locallyHolderWith_patchedProcessMetric
    {X : NNReal → Ω → E}
    {default : E}
    {YBase : ℕ → NNReal → Ω → E}
    {YWitness : WitnessSlotMetric (μ := μ) X → NNReal → Ω → E}
    {N : Set Ω}
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizonMetric (μ := μ) (X := X) (baseIndexOfMetric (μ := μ) (X := X) t))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndexMetric (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizonMetric (μ := μ) (X := X) i)
            (familyHorizonMetric (μ := μ) (X := X) j) →
            familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersionMetric (μ := μ) (X := X) YBase YWitness j t ω)
    (hYWitnessHolder :
      ∀ w : WitnessSlotMetric (μ := μ) X, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (positiveRatExponent w.1.2)
          (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1))
    {γ : ℝ≥0}
    (hγ0 : 0 < γ)
    (hAdmissible :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C ∧ (γ : ℝ) < β / α)
    {ω : Ω}
    (hω : ω ∉ N)
    (t : NNReal) :
    LocallyHolderWith γ
      (fun s : NNReal ↦ patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N s ω) := by
  let _ := t
  intro x
  let n : ℕ := Nat.ceil (x : ℝ) + 1
  have hxlt : x < (n : NNReal) := by
    -- Proof comment: the witness horizon is chosen strictly above the current time.
    have hxceil : x ≤ (Nat.ceil (x : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil (x : ℝ)
    have hceilSucc : (Nat.ceil (x : ℝ) : NNReal) < n := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil (x : ℝ))
    exact lt_of_le_of_lt hxceil hceilSucc
  rcases hAdmissible (n : NNReal) with ⟨α, β, C, hKol, hγlt⟩
  obtain ⟨q, hγq, hqβ⟩ := exists_rat_btwn hγlt
  have hγ0R : 0 < (γ : ℝ) := by
    exact_mod_cast hγ0
  have hq0R : 0 < (q : ℝ) := lt_trans hγ0R hγq
  have hq0 : 0 < q := by
    exact_mod_cast hq0R
  let qPos : PositiveRatExponent := ⟨q, by exact_mod_cast hq0⟩
  let w : WitnessSlotMetric (μ := μ) X :=
    ⟨(n, qPos), ⟨α, β, C, hKol, by simpa [qPos, positiveRatExponent] using hqβ⟩⟩
  rcases hYWitnessHolder w ω with ⟨Kq, hKq⟩
  have hγleq : γ ≤ positiveRatExponent qPos := by
    exact_mod_cast le_of_lt hγq
  rcases
    HolderOnWith.exists_holderOnWith_of_le
      (f := fun s : NNReal ↦ YWitness w s ω)
      (r := positiveRatExponent w.1.2)
      (s := γ)
      (A := Set.Icc (0 : NNReal) w.1.1)
      ⟨Kq, hKq⟩
      hγleq
      (Metric.isBounded_Icc (0 : NNReal) w.1.1) with
    ⟨Kγ, hKγ⟩
  have hEqOn :=
    patchedProcessMetric_eqOn_familyMember_offNull
      (μ := μ)
      (X := X)
      (default := default)
      (YBase := YBase)
      (YWitness := YWitness)
      (N := N)
      hBaseIndexLe
      hPatch
      hω
      (Sum.inr w)
  refine ⟨Set.Iio (n : NNReal), Iio_mem_nhds hxlt, Kγ, ?_⟩
  intro s hs u hu
  -- Proof comment: on the neighborhood `Iio n`, the patched process agrees with the chosen
  -- witness path, so the interval Hölder estimate transfers directly.
  have hsIcc : s ∈ Set.Icc (0 : NNReal) w.1.1 := ⟨zero_le _, hs.le⟩
  have huIcc : u ∈ Set.Icc (0 : NNReal) w.1.1 := ⟨zero_le _, hu.le⟩
  have hsEq :
      patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N s ω = YWitness w s ω := by
    simpa [familyVersionMetric, familyHorizonMetric] using hEqOn hsIcc
  have huEq :
      patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N u ω = YWitness w u ω := by
    simpa [familyVersionMetric, familyHorizonMetric] using hEqOn huIcc
  simpa [hsEq, huEq] using hKγ s hsIcc u huIcc

/-- Helper for Remark 21.7: the deterministic Hölder event for a finite-horizon metric witness can
be transferred to the patched global process outside the master overlap null set. -/
lemma exists_deterministicHolderConstant_of_patchedProcessMetric
    {X : NNReal → Ω → E}
    {default : E}
    {YBase : ℕ → NNReal → Ω → E}
    {YWitness : WitnessSlotMetric (μ := μ) X → NNReal → Ω → E}
    {N : Set Ω}
    {rBase : ℕ → ℝ≥0}
    (hNZero : μ N = 0)
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizonMetric (μ := μ) (X := X) (baseIndexOfMetric (μ := μ) (X := X) t))
    (hrBasePos : ∀ n : ℕ, 0 < rBase n)
    (hYBaseMod :
      ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t)
    (hYBaseHolder :
      ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndexMetric (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizonMetric (μ := μ) (X := X) i)
            (familyHorizonMetric (μ := μ) (X := X) j) →
            familyVersionMetric (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersionMetric (μ := μ) (X := X) YBase YWitness j t ω)
    {T α β C γ : ℝ≥0}
    (hKol : IsKolmogorovProcessOnIcc μ X T α β C)
    (hγ0 : 0 < γ)
    (hγlt : (γ : ℝ) < β / α)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℝ≥0,
      ENNReal.ofReal (1 - ε) ≤
        μ {
          ω |
            HolderOnWith K γ
              (fun t : NNReal ↦ patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω)
              (Set.Icc (0 : NNReal) T)
        } := by
  let n : ℕ := Nat.ceil (T : ℝ)
  have hTceil : T ≤ (n : NNReal) := by
    exact_mod_cast Nat.le_ceil (T : ℝ)
  rcases
    exists_holderVersion_of_isKolmogorovProcessOnIccMetric
      (μ := μ)
      (X := X)
      (T := T)
      (α := α)
      (β := β)
      (C := C)
      (q := γ)
      hKol
      hγ0
      hγlt with
    ⟨YT, hYTMod, hYTHolder⟩
  rcases
    exists_deterministicHolderConstant_of_pathwiseHolderOnIccMetric
      (μ := μ)
      (Y := YT)
      (T := T)
      (q := γ)
      (γ := γ)
      le_rfl
      hYTHolder
      ε
      hε with
    ⟨K, hK⟩
  have hmin : min (n : NNReal) T = T := min_eq_right hTceil
  rcases
    indistinguishable_on_overlap_of_holderVersionsMetric
      (μ := μ)
      (X := X)
      (Y := YBase n)
      (Z := YT)
      (S := n)
      (T := T)
      (rY := rBase n)
      (rZ := γ)
      (hXY := hYBaseMod n)
      (hXZ := hYTMod)
      (hrY := hrBasePos n)
      (hrZ := hγ0)
      (hY := hYBaseHolder n)
      (hZ := hYTHolder) with
    ⟨Noverlap, _, hNoverlapZero, hNoverlapSub⟩
  have hBaseFreshEq :
      ∀ ⦃ω : Ω⦄, ω ∉ Noverlap →
        Set.EqOn (fun t : NNReal ↦ YBase n t ω) (fun t : NNReal ↦ YT t ω)
          (Set.Icc (0 : NNReal) T) := by
    intro ω hω t ht
    by_contra hneq
    exact hω <|
      hNoverlapSub ⟨(t : ℝ), by simpa [hmin] using ht⟩ <| by
        simpa [Real.toNNReal_coe, hmin] using hneq
  have hUnionZero : μ (N ∪ Noverlap) = 0 := measure_union_null hNZero hNoverlapZero
  have hEq :
      ∀ ⦃ω : Ω⦄, ω ∉ N ∪ Noverlap →
        Set.EqOn
          (fun t : NNReal ↦ YT t ω)
          (fun t : NNReal ↦
            patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω)
          (Set.Icc (0 : NNReal) T) := by
    intro ω hω t ht
    have hωN : ω ∉ N := fun hNmem ↦ hω (Or.inl hNmem)
    have hωOverlap : ω ∉ Noverlap := fun hNmem ↦ hω (Or.inr hNmem)
    have hPatchBase :=
      patchedProcessMetric_eqOn_familyMember_offNull
        (μ := μ)
        (X := X)
        (default := default)
        (YBase := YBase)
        (YWitness := YWitness)
        (N := N)
        hBaseIndexLe
        hPatch
        hωN
        (Sum.inl n)
    have hPatchBaseAt :
        patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω = YBase n t ω := by
      simpa [familyVersionMetric, familyHorizonMetric] using hPatchBase ⟨ht.1, ht.2.trans hTceil⟩
    have hBaseFreshAt : YBase n t ω = YT t ω := hBaseFreshEq hωOverlap ht
    exact hBaseFreshAt.symm.trans hPatchBaseAt.symm
  have hEventEq :=
    holderEvent_congr_of_eqOnIcc_offNullMetric
      (μ := μ)
      (Y := YT)
      (Z := fun t : NNReal ↦ patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t)
      (T := T)
      (K := K)
      (γ := γ)
      (N := N ∪ Noverlap)
      hUnionZero
      hEq
  refine ⟨K, ?_⟩
  calc
    ENNReal.ofReal (1 - ε) ≤
        μ {ω | HolderOnWith K γ (fun t : NNReal ↦ YT t ω) (Set.Icc (0 : NNReal) T)} := hK
    _ =
        μ {
          ω |
            HolderOnWith K γ
              (fun t : NNReal ↦ patchedProcessMetric (μ := μ) (X := X) default YBase YWitness N t ω)
              (Set.Icc (0 : NNReal) T)
        } := by
          simpa using measure_congr hEventEq

-- Proof sketch: on each finite interval `[0,T]`, build countably many metric-valued Hölder
-- versions at baseline and rational witness exponents, patch them outside one master null set,
-- and then transfer both the local Hölder and deterministic-event conclusions from the finite
-- witnesses to the patched process.
omit [CompleteSpace E] [SecondCountableTopology E]

/-- Remark 21.7 (1): Theorem 21.6 remains valid for processes with values in an
arbitrary Polish metric space. -/
theorem exists_modification_with_locally_holder_paths_polishSpace
    (μ : Measure Ω) [IsProbabilityMeasure μ] [CompleteSpace E] [SecondCountableTopology E]
    (X : NNReal → Ω → E)
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    ∃ Xtilde : NNReal → Ω → E,
      AreModifications μ X Xtilde ∧
        HasRemark21_7_1Conclusions μ X Xtilde := by
  -- Route correction: the finite-interval metric theorem is now stable, so the remaining work is
  -- the codomain-generic patched-family replay of Theorem 21.6 rather than more cube transport.
  let data := exists_patchedProcessDataMetric (μ := μ) (X := X) hbound
  refine
    ⟨patchedProcessMetric (μ := μ) (X := X) data.default data.YBase data.YWitness data.N,
      data.hModXtilde,
      ?_⟩
  constructor
  · intro γ hγ0 hAdmissible ω
    by_cases hω : ω ∈ data.N
    · -- Proof comment: on the exceptional null set, the patched path is constant at the chosen
      -- fallback value.
      intro x
      refine ⟨Set.univ, Filter.univ_mem, 0, ?_⟩
      intro s _ t _
      simp [patchedProcessMetric, hω]
    · -- Proof comment: off the master null set, use the witness-family transfer lemma.
      simpa using
        locallyHolderWith_patchedProcessMetric
          (μ := μ)
          (X := X)
          (default := data.default)
          (YBase := data.YBase)
          (YWitness := data.YWitness)
          (N := data.N)
          data.hBaseIndexLe
          data.hPatch
          data.hYWitnessHolder
          hγ0
          hAdmissible
          hω
          0
  · intro T α β C γ hKol hγ0 hγlt ε hε
    -- Proof comment: the deterministic Hölder event estimate is the finite-horizon transfer lemma
    -- applied to the packaged metric patched process.
    simpa using
      exists_deterministicHolderConstant_of_patchedProcessMetric
        (μ := μ)
        (X := X)
        (default := data.default)
        (YBase := data.YBase)
        (YWitness := data.YWitness)
        (N := data.N)
        (rBase := data.rBase)
        data.hNZero
        data.hBaseIndexLe
        data.hrBasePos
        data.hYBaseMod
        data.hYBaseHolder
        data.hPatch
        hKol
        hγ0
        hγlt
        ε
        hε

end MetricPatchedProcess

end ProbabilityTheory
