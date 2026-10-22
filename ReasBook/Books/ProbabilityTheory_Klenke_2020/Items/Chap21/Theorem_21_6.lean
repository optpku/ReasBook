/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.FiniteIntervalVersion

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Theorem 21.6: positive rational exponents used to index the countable admissible
witness family. -/
abbrev PositiveRatExponent := {q : ℚ // 0 < q}

/-- Helper for Theorem 21.6: a positive rational exponent has nonnegative real coercion. -/
lemma positiveRatExponent_nonneg (q : PositiveRatExponent) : 0 ≤ (q.1 : ℝ) := by
  exact le_of_lt <| by exact_mod_cast q.2

/-- Helper for Theorem 21.6: interpret a positive rational exponent as an element of `ℝ≥0`. -/
def positiveRatExponent (q : PositiveRatExponent) : ℝ≥0 :=
  ⟨q.1, positiveRatExponent_nonneg q⟩

/-- Helper for Theorem 21.6: a witness slot records an integer horizon, a positive rational
exponent, and finite-horizon Kolmogorov data for that exponent. -/
def WitnessSlot (μ : Measure Ω) (X : NNReal → Ω → ℝ) : Type :=
  {iq : ℕ × PositiveRatExponent //
    ∃ α β C : ℝ≥0,
      IsKolmogorovProcessOnIcc μ X iq.1 α β C ∧ ((positiveRatExponent iq.2 : ℝ)) < β / α}

/-- Helper for Theorem 21.6: the patched family is indexed by the baseline integer horizons and
the admissible witness slots. -/
abbrev FamilyIndex (μ : Measure Ω) (X : NNReal → Ω → ℝ) := Sum ℕ (WitnessSlot μ X)

/-- Helper for Theorem 21.6: positive rational witness exponents form a countable type. -/
instance : Countable PositiveRatExponent := inferInstance

/-- Helper for Theorem 21.6: admissible witness slots form a countable type. -/
instance witnessSlotCountable {X : NNReal → Ω → ℝ} : Countable (WitnessSlot μ X) := by
  classical
  change Countable {iq : ℕ × PositiveRatExponent //
    ∃ α β C : ℝ≥0,
      IsKolmogorovProcessOnIcc μ X iq.1 α β C ∧ ((positiveRatExponent iq.2 : ℝ)) < β / α}
  infer_instance

/-- Helper for Theorem 21.6: the sum of baseline horizons and witness slots is countable. -/
instance familyIndexCountable {X : NNReal → Ω → ℝ} : Countable (FamilyIndex μ X) := by
  classical
  infer_instance

/-- Helper for Theorem 21.6: each family index carries the finite interval on which its version is
defined. -/
def familyHorizon {X : NNReal → Ω → ℝ} : FamilyIndex μ X → NNReal :=
  Sum.elim (fun n ↦ n) (fun w ↦ w.1.1)

/-- Helper for Theorem 21.6: each family index carries the Hölder exponent of its associated
version. -/
def familyExponent {X : NNReal → Ω → ℝ} (rBase : ℕ → ℝ≥0) :
    FamilyIndex μ X → ℝ≥0 :=
  Sum.elim rBase (fun w ↦ positiveRatExponent w.1.2)

/-- Helper for Theorem 21.6: evaluate the baseline or witness version attached to a family index.
-/
def familyVersion {X : NNReal → Ω → ℝ}
    (YBase : ℕ → NNReal → Ω → ℝ)
    (YWitness : WitnessSlot μ X → NNReal → Ω → ℝ) :
    FamilyIndex μ X → NNReal → Ω → ℝ :=
  Sum.elim YBase YWitness

/-- Helper for Theorem 21.6: the integer family member used to define the global patched version at
time `t`. -/
def baseIndexOf {X : NNReal → Ω → ℝ} (t : NNReal) : FamilyIndex μ X :=
  Sum.inl (Nat.ceil (t : ℝ))

/-- Helper for Theorem 21.6: set membership is classically decidable in the patched-process
branching definition. -/
local instance decidableMemSet (N : Set Ω) : DecidablePred (fun ω : Ω ↦ ω ∈ N) :=
  Classical.decPred _

/-- Helper for Theorem 21.6: the global process obtained by patching the baseline family outside a
master null set. -/
def patchedProcess {X : NNReal → Ω → ℝ}
    (YBase : ℕ → NNReal → Ω → ℝ)
    (YWitness : WitnessSlot μ X → NNReal → Ω → ℝ)
    (N : Set Ω) :
    NNReal → Ω → ℝ :=
  fun t ω ↦
    if hω : ω ∈ N then
      0
    else
      familyVersion (μ := μ) (X := X) YBase YWitness (baseIndexOf (μ := μ) (X := X) t) t ω

/-- Helper for Theorem 21.6: package the baseline integer family together with the countable
admissible witness family. -/
structure HolderFamiliesData (μ : Measure Ω) (X : NNReal → Ω → ℝ) where
  rBase : ℕ → ℝ≥0
  YBase : ℕ → NNReal → Ω → ℝ
  YWitness : WitnessSlot μ X → NNReal → Ω → ℝ
  hrBasePos : ∀ n : ℕ, 0 < rBase n
  hYBaseMod : ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t
  hYBaseHolder :
    ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n)
  hYWitnessMod :
    ∀ w : WitnessSlot μ X, ∀ t : NNReal, t ≤ w.1.1 → X t =ᵐ[μ] YWitness w t
  hYWitnessHolder :
    ∀ w : WitnessSlot μ X, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (positiveRatExponent w.1.2)
        (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)

/-- Helper for Theorem 21.6: package the patched global modification and the overlap API needed
for the final theorem. -/
structure PatchedProcessData (μ : Measure Ω) (X : NNReal → Ω → ℝ) where
  rBase : ℕ → ℝ≥0
  YBase : ℕ → NNReal → Ω → ℝ
  YWitness : WitnessSlot μ X → NNReal → Ω → ℝ
  N : Set Ω
  hrBasePos : ∀ n : ℕ, 0 < rBase n
  hYBaseMod : ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t
  hYBaseHolder :
    ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n)
  hYWitnessHolder :
    ∀ w : WitnessSlot μ X, ∀ ω : Ω, ∃ K : ℝ≥0,
      HolderOnWith K (positiveRatExponent w.1.2)
        (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)
  hBaseIndexLe :
    ∀ t : NNReal, t ≤ familyHorizon (μ := μ) (X := X) (baseIndexOf (μ := μ) (X := X) t)
  hNZero : μ N = 0
  hModXtilde : AreModifications μ X (patchedProcess (μ := μ) (X := X) YBase YWitness N)
  hPatch :
    ∀ ⦃ω : Ω⦄, ω ∉ N →
      ∀ i j : FamilyIndex (μ := μ) X, ∀ t : NNReal,
        t ≤ min (familyHorizon (μ := μ) (X := X) i) (familyHorizon (μ := μ) (X := X) j) →
          familyVersion (μ := μ) (X := X) YBase YWitness i t ω =
            familyVersion (μ := μ) (X := X) YBase YWitness j t ω

/-- Helper for Theorem 21.6: positive rational witness exponents are strictly positive as
nonnegative reals. -/
lemma positiveRatExponent_pos (q : PositiveRatExponent) : 0 < positiveRatExponent q := by
  change (0 : ℝ) < (positiveRatExponent q : ℝ)
  simpa [positiveRatExponent] using (show (0 : ℝ) < (q.1 : ℝ) from by exact_mod_cast q.2)

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: two finite-horizon versions of the same process agree almost surely on
their common interval. -/
lemma aeEq_on_overlap_of_versions
    {X Y Z : NNReal → Ω → ℝ} {S T : NNReal}
    (hXY : ∀ t : NNReal, t ≤ S → X t =ᵐ[μ] Y t)
    (hXZ : ∀ t : NNReal, t ≤ T → X t =ᵐ[μ] Z t) :
    ∀ t : NNReal, t ≤ min S T → Y t =ᵐ[μ] Z t := by
  intro t ht
  -- Proof comment: on the overlap `[0, min S T]`, both versions agree almost surely with the
  -- same original process `X`, so they agree almost surely with each other.
  filter_upwards [hXY t (le_trans ht (min_le_left _ _)), hXZ t (le_trans ht (min_le_right _ _))]
    with ω hY hZ
  exact hY.symm.trans hZ

/-- Helper for Theorem 21.6: Hölder control on `Set.Icc (0 : NNReal) T` induces a Hölder map on
the interval subtype itself. -/
lemma holderWith_subtypeIcc_of_holderOnWith
    {T K γ : ℝ≥0} {f : NNReal → ℝ}
    (h : HolderOnWith K γ f (Set.Icc (0 : NNReal) T)) :
    HolderWith K γ (fun t : Set.Icc (0 : NNReal) T ↦ f t.1) := by
  -- Proof comment: restricting the ambient domain to the interval subtype turns the local
  -- `HolderOnWith` estimate into a global `HolderWith` estimate on that subtype.
  rw [← holderOnWith_univ]
  intro s _ t _
  exact h s.1 s.2 t.1 t.2

/-- Helper for Theorem 21.6: pathwise Hölder control on `Set.Icc (0 : NNReal) T` yields
continuity at every interval-subtype time. -/
lemma continuousWithinAt_subtypeIcc_of_holderOnWith
    {T K γ : ℝ≥0} {f : NNReal → ℝ}
    (hγ : 0 < γ)
    (h : HolderOnWith K γ f (Set.Icc (0 : NNReal) T))
    (t : Set.Icc (0 : NNReal) T) :
    ContinuousWithinAt (fun s : Set.Icc (0 : NNReal) T ↦ f s.1) (Set.Ici t) t := by
  -- Proof comment: after passing to the interval subtype, Hölder control gives global continuity,
  -- hence continuity within the right-half neighborhood `Set.Ici t`.
  have hcont :
      Continuous (fun s : Set.Icc (0 : NNReal) T ↦ f s.1) :=
    (holderWith_subtypeIcc_of_holderOnWith h).continuous hγ
  exact hcont.continuousAt.continuousWithinAt

/-- Helper for Theorem 21.6: Hölder control on `[0,T] ⊆ ℝ≥0` induces a Hölder map on the
corresponding real interval after composing with `Real.toNNReal`. -/
lemma holderWith_realSubtypeIcc_of_holderOnWith
    {T K γ : ℝ≥0} {f : NNReal → ℝ}
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

/-- Helper for Theorem 21.6: pathwise Hölder control on `[0,T] ⊆ ℝ≥0` yields right continuity on
the corresponding real interval subtype required by Lemma 21.5. -/
lemma continuousWithinAt_realSubtypeIcc_of_holderOnWith
    {T K γ : ℝ≥0} {f : NNReal → ℝ}
    (hγ : 0 < γ)
    (h : HolderOnWith K γ f (Set.Icc (0 : NNReal) T))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ContinuousWithinAt (fun s : Set.Icc (0 : ℝ) (T : ℝ) ↦ f s.1.toNNReal) (Set.Ici t) t := by
  -- Proof comment: the composed map is globally Hölder on the real interval subtype, hence
  -- continuous and therefore continuous within every right-neighborhood.
  have hcont :
      Continuous (fun s : Set.Icc (0 : ℝ) (T : ℝ) ↦ f s.1.toNNReal) :=
    (holderWith_realSubtypeIcc_of_holderOnWith h).continuous hγ
  exact hcont.continuousAt.continuousWithinAt

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: if two paths agree off a null set on `Set.Icc (0 : NNReal) T`, then
the corresponding Hölder events agree almost surely. -/
lemma holderEvent_congr_of_eqOnIcc_offNull
    {Y Z : NNReal → Ω → ℝ} {T K γ : ℝ≥0} {N : Set Ω}
    (hN : μ N = 0)
    (hEq :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        Set.EqOn (fun t : NNReal ↦ Y t ω) (fun t : NNReal ↦ Z t ω) (Set.Icc (0 : NNReal) T)) :
    {ω | HolderOnWith K γ (fun t : NNReal ↦ Y t ω) (Set.Icc (0 : NNReal) T)} =ᵐ[μ]
      {ω | HolderOnWith K γ (fun t : NNReal ↦ Z t ω) (Set.Icc (0 : NNReal) T)} := by
  -- Proof comment: outside the null exceptional set, the two path restrictions are identical on
  -- the interval, so the Hölder predicate is equivalent pointwise there.
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
    rw [ae_iff]
    simpa using hN
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

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: two finite-horizon Hölder versions of the same process are
indistinguishable on their overlap. -/
lemma indistinguishable_on_overlap_of_holderVersions
    {X Y Z : NNReal → Ω → ℝ} {S T rY rZ : ℝ≥0}
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
  let Yoverlap : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) → Ω → ℝ :=
    fun t ω ↦ Y t.1.toNNReal ω
  let Zoverlap : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ) → Ω → ℝ :=
    fun t ω ↦ Z t.1.toNNReal ω
  -- Proof comment: first identify the two versions almost surely at each overlap time, then apply
  -- Lemma 21.5 using the pathwise Hölder control to obtain right continuity on the overlap
  -- interval subtype.
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
      aeEq_on_overlap_of_versions (μ := μ) hXY hXZ t.1.toNNReal ht
  have hYrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ),
          ContinuousWithinAt
            (processPath Yoverlap ω)
            (Set.Ici t) t := by
    -- Proof comment: every path is Hölder on `[0,S]`, hence also on the smaller overlap interval.
    filter_upwards with ω
    intro t
    rcases hY ω with ⟨K, hK⟩
    have hKoverlap :
        HolderOnWith K rY (fun s : NNReal ↦ Y s ω) (Set.Icc (0 : NNReal) (min S T)) :=
      hK.mono <| by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩
    simpa [Yoverlap, processPath_apply] using
      continuousWithinAt_realSubtypeIcc_of_holderOnWith (T := min S T) hrY hKoverlap t
  have hZrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ),
          ContinuousWithinAt
            (processPath Zoverlap ω)
            (Set.Ici t) t := by
    -- Proof comment: the same restriction argument applies to the `Z` version.
    filter_upwards with ω
    intro t
    rcases hZ ω with ⟨K, hK⟩
    have hKoverlap :
        HolderOnWith K rZ (fun s : NNReal ↦ Z s ω) (Set.Icc (0 : NNReal) (min S T)) :=
      hK.mono <| by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 (min_le_right _ _)⟩
    simpa [Zoverlap, processPath_apply] using
      continuousWithinAt_realSubtypeIcc_of_holderOnWith (T := min S T) hrZ hKoverlap t
  exact
    ProbabilityTheory.indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
      (Ω := Ω)
      (E := ℝ)
      (μ := μ)
      (I := Set.Icc (0 : ℝ) ((min S T : NNReal) : ℝ))
      (X := Yoverlap)
      (Y := Zoverlap)
      hmod Set.ordConnected_Icc hYrc hZrc

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: a countable family of finite-horizon Hölder versions can be patched
outside one measurable null set so that all family members agree on every common overlap time. -/
lemma exists_masterPatchNullSet_of_holderVersions
    {ι : Type*} [Countable ι]
    {X : NNReal → Ω → ℝ} {T : ι → NNReal} {r : ι → ℝ≥0}
    {Y : ι → NNReal → Ω → ℝ}
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
      indistinguishable_on_overlap_of_holderVersions
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
    -- Proof comment: the overlap indistinguishability witness already controls every common time;
    -- outside its null set, the two versions therefore agree pointwise on the overlap interval.
    by_contra hneq
    exact hω <| hNij_sub ⟨(t : ℝ), by simpa using ht⟩ <| by
      simpa using hneq
  let N : Set Ω := ⋃ ij : ι × ι, Classical.choose (hpair ij.1 ij.2)
  refine ⟨N, ?_, ?_, ?_⟩
  · -- Proof comment: the master bad set is a countable union of measurable pairwise overlap null
    -- sets, so it remains measurable.
    refine MeasurableSet.iUnion ?_
    intro ij
    exact (Classical.choose_spec (hpair ij.1 ij.2)).1
  · -- Proof comment: countability of the index family preserves nullity under the union.
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

/-- Helper for Theorem 21.6: finite-horizon Kolmogorov bounds produce a baseline integer family
and a countable admissible rational witness family of Hölder versions. -/
def exists_holderFamilies_of_kolmogorovBounds
    {X : NNReal → Ω → ℝ}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    HolderFamiliesData (μ := μ) X := by
  classical
  let αBase : ℕ → ℝ≥0 := fun n ↦ Classical.choose (hbound n)
  let βBase : ℕ → ℝ≥0 := fun n ↦ Classical.choose (Classical.choose_spec (hbound n))
  let CBase : ℕ → ℝ≥0 := fun n ↦
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hbound n)))
  have hKolBase :
      ∀ n : ℕ, IsKolmogorovProcessOnIcc μ X n (αBase n) (βBase n) (CBase n) := by
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
    -- Proof comment: dividing by `2 * α` keeps the exponent strictly below the admissible
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
  let YBase : ℕ → NNReal → Ω → ℝ := fun n ↦
    Classical.choose <|
      exists_holderVersion_of_isKolmogorovProcessOnIcc
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
    -- Proof comment: each baseline family member is exactly the finite-horizon version produced
    -- by the interval-local Kolmogorov--Chentsov theorem at the chosen baseline exponent.
    exact Classical.choose_spec <|
      exists_holderVersion_of_isKolmogorovProcessOnIcc
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
  let witnessAlpha : WitnessSlot (μ := μ) X → ℝ≥0 := fun w ↦ Classical.choose w.2
  let witnessBeta : WitnessSlot (μ := μ) X → ℝ≥0 := fun w ↦
    Classical.choose (Classical.choose_spec w.2)
  let witnessC : WitnessSlot (μ := μ) X → ℝ≥0 := fun w ↦
    Classical.choose (Classical.choose_spec (Classical.choose_spec w.2))
  have hWitnessData :
      ∀ w : WitnessSlot (μ := μ) X,
        IsKolmogorovProcessOnIcc μ X w.1.1 (witnessAlpha w) (witnessBeta w) (witnessC w) ∧
          ((positiveRatExponent w.1.2 : ℝ)) < witnessBeta w / witnessAlpha w := by
    intro w
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec w.2))
  let YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ := fun w ↦
    Classical.choose <|
      exists_holderVersion_of_isKolmogorovProcessOnIcc
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
      ∀ w : WitnessSlot (μ := μ) X,
        (∀ t : NNReal, t ≤ w.1.1 → X t =ᵐ[μ] YWitness w t) ∧
          (∀ ω : Ω, ∃ K : ℝ≥0,
            HolderOnWith K (positiveRatExponent w.1.2)
              (fun t : NNReal ↦ YWitness w t ω) (Set.Icc (0 : NNReal) w.1.1)) := by
    intro w
    -- Proof comment: witness family members use the admissible positive rational exponents stored
    -- in `WitnessSlot`.
    exact Classical.choose_spec <|
      exists_holderVersion_of_isKolmogorovProcessOnIcc
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

/-- Helper for Theorem 21.6: a countable family of finite-horizon Hölder versions patches into a
global modification outside one master null set. -/
def exists_masterPatch_of_holderFamilies
    {X : NNReal → Ω → ℝ}
    (data : HolderFamiliesData (μ := μ) X) :
    PatchedProcessData (μ := μ) X := by
  classical
  let Y := familyVersion (μ := μ) (X := X) data.YBase data.YWitness
  let r := familyExponent (μ := μ) (X := X) data.rBase
  have hmod :
      ∀ i : FamilyIndex (μ := μ) X,
        ∀ t : NNReal, t ≤ familyHorizon (μ := μ) (X := X) i → X t =ᵐ[μ] Y i t := by
    intro i t ht
    -- Proof comment: each patched-family index is either a baseline horizon or a witness slot,
    -- so we can read off the modification property from the corresponding packaged field.
    cases i with
    | inl n =>
        simpa [Y, familyVersion, familyHorizon] using data.hYBaseMod n t ht
    | inr w =>
        simpa [Y, familyVersion, familyHorizon] using data.hYWitnessMod w t ht
  have hr :
      ∀ i : FamilyIndex (μ := μ) X, 0 < r i := by
    intro i
    cases i with
    | inl n =>
        simpa [r, familyExponent] using data.hrBasePos n
    | inr w =>
        simpa [r, familyExponent] using positiveRatExponent_pos w.1.2
  have hY :
      ∀ i : FamilyIndex (μ := μ) X, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (r i) (fun t : NNReal ↦ Y i t ω)
          (Set.Icc (0 : NNReal) (familyHorizon (μ := μ) (X := X) i)) := by
    intro i ω
    cases i with
    | inl n =>
        simpa [Y, r, familyVersion, familyExponent, familyHorizon] using data.hYBaseHolder n ω
    | inr w =>
        simpa [Y, r, familyVersion, familyExponent, familyHorizon] using data.hYWitnessHolder w ω
  let patchWitness :=
    exists_masterPatchNullSet_of_holderVersions
      (μ := μ)
      (X := X)
      (T := familyHorizon (μ := μ) (X := X))
      (r := r)
      (Y := Y)
      hmod
      hr
      hY
  let N : Set Ω := Classical.choose patchWitness
  have hNMeas : MeasurableSet N := (Classical.choose_spec patchWitness).1
  have hNZero : μ N = 0 := (Classical.choose_spec patchWitness).2.1
  have hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndex (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizon (μ := μ) (X := X) i) (familyHorizon (μ := μ) (X := X) j) →
            Y i t ω = Y j t ω :=
    (Classical.choose_spec patchWitness).2.2
  refine
    { rBase := data.rBase
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
    -- Proof comment: `baseIndexOf t` uses the ceiling horizon, which always contains `t`.
    change t ≤ (Nat.ceil (t : ℝ) : NNReal)
    exact_mod_cast Nat.le_ceil (t : ℝ)
  · intro t
    -- Proof comment: off the master null set, the patched process equals the baseline family
    -- member at the ceiling horizon, and that family member is already a modification of `X`.
    have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
      rw [ae_iff]
      simpa using hNZero
    have hceil : t ≤ (Nat.ceil (t : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil (t : ℝ)
    filter_upwards [hNae, data.hYBaseMod (Nat.ceil (t : ℝ)) t hceil] with ω hω hXt
    have hpatched :
        patchedProcess (μ := μ) (X := X) data.YBase data.YWitness N t ω =
          data.YBase (Nat.ceil (t : ℝ)) t ω := by
      simp [patchedProcess, hω, familyVersion, baseIndexOf]
    exact hXt.trans hpatched.symm
  · intro ω hω i j t ht
    simpa [Y] using hPatch hω i j t ht

/-- Helper for Theorem 21.6: construct the countable patched modification together with the
baseline and witness families needed for the local Hölder and deterministic-event arguments. -/
def exists_patchedProcessData
    {X : NNReal → Ω → ℝ}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    PatchedProcessData (μ := μ) X := by
  -- Proof comment: first package the finite-horizon family, then apply the one-time master
  -- patching construction.
  exact
    exists_masterPatch_of_holderFamilies
      (μ := μ)
      (X := X)
      (exists_holderFamilies_of_kolmogorovBounds (μ := μ) (X := X) hbound)

/-- Helper for Theorem 21.6: increasing the Hölder constant preserves `HolderOnWith`. -/
lemma holderOnWith_mono_constant
    {X : Type*} [PseudoMetricSpace X]
    {K L r : ℝ≥0} {f : X → ℝ} {s : Set X}
    (hKL : K ≤ L)
    (hK : HolderOnWith K r f s) :
    HolderOnWith L r f s := by
  -- Proof comment: enlarge only the prefactor in the Hölder bound and keep the same exponent.
  intro x hx y hy
  calc
    edist (f x) (f y) ≤ K * edist x y ^ (r : ℝ) := hK x hx y hy
    _ ≤ L * edist x y ^ (r : ℝ) := by
          gcongr

/-- Helper for Theorem 21.6: outside the master null set, the patched process is already in the
baseline normal form indexed by `baseIndexOf t`. -/
lemma patchedProcess_eq_familyVersion_baseIndex_offNull
    {X : NNReal → Ω → ℝ}
    {YBase : ℕ → NNReal → Ω → ℝ}
    {YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ}
    {N : Set Ω} {ω : Ω}
    (hω : ω ∉ N)
    (t : NNReal) :
    patchedProcess (μ := μ) (X := X) YBase YWitness N t ω =
      familyVersion (μ := μ) (X := X) YBase YWitness
        (baseIndexOf (μ := μ) (X := X) t) t ω := by
  -- Proof comment: the patch definition only branches on membership in the master null set.
  simp [patchedProcess, hω]

/-- Helper for Theorem 21.6: outside the master null set, the patched process agrees with any
family member on that member's time interval. -/
lemma patchedProcess_eqOn_familyMember_offNull
    {X : NNReal → Ω → ℝ}
    {YBase : ℕ → NNReal → Ω → ℝ}
    {YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ}
    {N : Set Ω}
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizon (μ := μ) (X := X) (baseIndexOf (μ := μ) (X := X) t))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndex (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizon (μ := μ) (X := X) i) (familyHorizon (μ := μ) (X := X) j) →
            familyVersion (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersion (μ := μ) (X := X) YBase YWitness j t ω)
    {ω : Ω}
    (hω : ω ∉ N)
    (i : FamilyIndex (μ := μ) X) :
    Set.EqOn
      (fun t : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N t ω)
      (fun t : NNReal ↦ familyVersion (μ := μ) (X := X) YBase YWitness i t ω)
      (Set.Icc (0 : NNReal) (familyHorizon (μ := μ) (X := X) i)) := by
  -- Proof comment: normalize the patched process to its base index and then use the overlap API
  -- at time `t`.
  intro t ht
  calc
    patchedProcess (μ := μ) (X := X) YBase YWitness N t ω
        = familyVersion (μ := μ) (X := X) YBase YWitness
            (baseIndexOf (μ := μ) (X := X) t) t ω :=
      patchedProcess_eq_familyVersion_baseIndex_offNull (μ := μ) (X := X) hω t
    _ = familyVersion (μ := μ) (X := X) YBase YWitness i t ω :=
      hPatch hω (baseIndexOf (μ := μ) (X := X) t) i t <|
        le_min (hBaseIndexLe t) ht.2

/-- Helper for Theorem 21.6: any family member is a modification of the original process on its
own horizon. -/
lemma familyVersion_modification
    {X : NNReal → Ω → ℝ}
    {YBase : ℕ → NNReal → Ω → ℝ}
    {YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ}
    (hYBaseMod :
      ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t)
    (hYWitnessMod :
      ∀ w : WitnessSlot (μ := μ) X, ∀ t : NNReal, t ≤ w.1.1 → X t =ᵐ[μ] YWitness w t)
    (i : FamilyIndex (μ := μ) X)
    (t : NNReal)
    (ht :
      t ≤ familyHorizon (μ := μ) (X := X) i) :
    X t =ᵐ[μ] familyVersion (μ := μ) (X := X) YBase YWitness i t := by
  -- Proof comment: split into the baseline and witness branches of the family index.
  cases i with
  | inl n =>
      simpa [familyHorizon, familyVersion] using hYBaseMod n t ht
  | inr w =>
      simpa [familyHorizon, familyVersion] using hYWitnessMod w t ht

/-- Helper for Theorem 21.6: pathwise Hölder control on `[0,T]` yields a deterministic Hölder
constant on a set of probability at least `1 - ε`. -/
lemma exists_deterministicHolderConstant_of_pathwiseHolderOnIcc
    {Y : NNReal → Ω → ℝ} {T q γ : ℝ≥0}
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
    exact holderOnWith_mono_constant (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm) hω
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
      exact holderOnWith_mono_constant hKγn hKγ
  have htarget_lt : ENNReal.ofReal (1 - ε) < ⨆ n, μ (A n) := by
    rw [← hAmono.measure_iUnion (μ := μ), hAuniv, measure_univ]
    by_cases hε1 : ε ≤ 1
    · rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith)
    · have hneg : 1 - ε < 0 := by
        linarith
      simp [ENNReal.ofReal_eq_zero.2 hneg.le]
  rcases lt_iSup_iff.mp htarget_lt with ⟨n, hn⟩
  refine ⟨n, hn.le⟩

/-- Helper for Theorem 21.6: outside the master null set, the patched process is locally
`γ`-Hölder at every time once an admissible finite-horizon witness exponent is chosen. -/
lemma locallyHolderWith_patchedProcess
    {X : NNReal → Ω → ℝ}
    {YBase : ℕ → NNReal → Ω → ℝ}
    {YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ}
    {N : Set Ω}
    {rBase : ℕ → ℝ≥0}
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizon (μ := μ) (X := X) (baseIndexOf (μ := μ) (X := X) t))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndex (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizon (μ := μ) (X := X) i) (familyHorizon (μ := μ) (X := X) j) →
            familyVersion (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersion (μ := μ) (X := X) YBase YWitness j t ω)
    (hYWitnessHolder :
      ∀ w : WitnessSlot (μ := μ) X, ∀ ω : Ω, ∃ K : ℝ≥0,
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
      (fun s : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N s ω) := by
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
  let w : WitnessSlot (μ := μ) X :=
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
    patchedProcess_eqOn_familyMember_offNull
      (μ := μ)
      (X := X)
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
  -- witness path, so the interval Hölder estimate transfers verbatim.
  have hsIcc : s ∈ Set.Icc (0 : NNReal) w.1.1 := ⟨zero_le _, hs.le⟩
  have huIcc : u ∈ Set.Icc (0 : NNReal) w.1.1 := ⟨zero_le _, hu.le⟩
  have hsEq :
      patchedProcess (μ := μ) (X := X) YBase YWitness N s ω = YWitness w s ω := by
    simpa [familyVersion, familyHorizon] using hEqOn hsIcc
  have huEq :
      patchedProcess (μ := μ) (X := X) YBase YWitness N u ω = YWitness w u ω := by
    simpa [familyVersion, familyHorizon] using hEqOn huIcc
  simpa [hsEq, huEq] using hKγ s hsIcc u huIcc

/-- Helper for Theorem 21.6: the deterministic Hölder event for a finite-horizon witness can be
transferred to the patched global process outside the master overlap null set. -/
lemma exists_deterministicHolderConstant_of_patchedProcess
    {X : NNReal → Ω → ℝ}
    {YBase : ℕ → NNReal → Ω → ℝ}
    {YWitness : WitnessSlot (μ := μ) X → NNReal → Ω → ℝ}
    {N : Set Ω}
    {rBase : ℕ → ℝ≥0}
    (hNZero : μ N = 0)
    (hBaseIndexLe :
      ∀ t : NNReal,
        t ≤ familyHorizon (μ := μ) (X := X) (baseIndexOf (μ := μ) (X := X) t))
    (hrBasePos : ∀ n : ℕ, 0 < rBase n)
    (hYBaseMod :
      ∀ n : ℕ, ∀ t : NNReal, t ≤ n → X t =ᵐ[μ] YBase n t)
    (hYBaseHolder :
      ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderOnWith K (rBase n) (fun t : NNReal ↦ YBase n t ω) (Set.Icc (0 : NNReal) n))
    (hPatch :
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        ∀ i j : FamilyIndex (μ := μ) X, ∀ t : NNReal,
          t ≤ min (familyHorizon (μ := μ) (X := X) i) (familyHorizon (μ := μ) (X := X) j) →
            familyVersion (μ := μ) (X := X) YBase YWitness i t ω =
              familyVersion (μ := μ) (X := X) YBase YWitness j t ω)
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
              (fun t : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N t ω)
              (Set.Icc (0 : NNReal) T)
        } := by
  let n : ℕ := Nat.ceil (T : ℝ)
  have hTceil : T ≤ (n : NNReal) := by
    exact_mod_cast Nat.le_ceil (T : ℝ)
  rcases
    exists_holderVersion_of_isKolmogorovProcessOnIcc
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
    exists_deterministicHolderConstant_of_pathwiseHolderOnIcc
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
    indistinguishable_on_overlap_of_holderVersions
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
          (fun t : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N t ω)
          (Set.Icc (0 : NNReal) T) := by
    intro ω hω t ht
    have hωN : ω ∉ N := fun hNmem ↦ hω (Or.inl hNmem)
    have hωOverlap : ω ∉ Noverlap := fun hNmem ↦ hω (Or.inr hNmem)
    have hPatchBase :=
      patchedProcess_eqOn_familyMember_offNull
        (μ := μ)
        (X := X)
        (YBase := YBase)
        (YWitness := YWitness)
        (N := N)
        hBaseIndexLe
        hPatch
        hωN
        (Sum.inl n)
    have hPatchBaseAt :
        patchedProcess (μ := μ) (X := X) YBase YWitness N t ω = YBase n t ω := by
      simpa [familyVersion, familyHorizon] using hPatchBase ⟨ht.1, ht.2.trans hTceil⟩
    have hBaseFreshAt : YBase n t ω = YT t ω := hBaseFreshEq hωOverlap ht
    exact hBaseFreshAt.symm.trans hPatchBaseAt.symm
  have hEventEq :=
    holderEvent_congr_of_eqOnIcc_offNull
      (μ := μ)
      (Y := YT)
      (Z := fun t : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N t)
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
              (fun t : NNReal ↦ patchedProcess (μ := μ) (X := X) YBase YWitness N t ω)
              (Set.Icc (0 : NNReal) T)
        } := by
          simpa using measure_congr hEventEq

-- Proof sketch: on each finite interval `[0,T]`, apply the Kolmogorov--Chentsov construction for
-- every admissible exponent `γ < β / α`, then patch the finite-interval modifications together
-- using indistinguishability on overlaps to obtain one global modification on `[0,∞)`. The same
-- modification also satisfies the deterministic Hölder-constant probability estimate from part
-- (ii) on each fixed interval.
/-- Theorem 21.6: if every finite interval `[0,T]` admits a Kolmogorov--Chentsov moment bound,
then the process has a single modification `Xtilde` such that:

1. every exponent `γ > 0` that is admissible on each finite interval yields locally
   `γ`-Hölder sample paths on `ℝ≥0`;
2. for the same `Xtilde`, on every fixed interval `[0,T]` and for every `ε > 0`, there is a
   deterministic Hölder constant `K` such that the path is `γ`-Hölder on `[0,T]` with
   probability at least `1 - ε`. -/
theorem exists_modification_with_locally_holder_paths
    {X : NNReal → Ω → ℝ}
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    ∃ Xtilde : NNReal → Ω → ℝ,
      AreModifications μ X Xtilde ∧
        (∀ γ : ℝ≥0, 0 < γ →
          (∀ T : NNReal,
            ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C ∧ (γ : ℝ) < β / α) →
              ∀ ω : Ω, LocallyHolderWith γ (fun t : NNReal ↦ Xtilde t ω)) ∧
        ∀ (T α β C γ : ℝ≥0),
          IsKolmogorovProcessOnIcc μ X T α β C →
          0 < γ →
            (γ : ℝ) < β / α →
              ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0,
                ENNReal.ofReal (1 - ε) ≤
                  μ {
                    ω | HolderOnWith K γ (fun t : NNReal ↦ Xtilde t ω) (Set.Icc (0 : NNReal) T)
                  } := by
  let data := exists_patchedProcessData (μ := μ) (X := X) hbound
  refine
    ⟨patchedProcess (μ := μ) (X := X) data.YBase data.YWitness data.N,
      data.hModXtilde,
      ?_,
      ?_⟩
  · intro γ hγ0 hAdmissible ω
    by_cases hω : ω ∈ data.N
    · -- Proof comment: on the exceptional null set, the patched path is identically zero.
      intro x
      refine ⟨Set.univ, Filter.univ_mem, 0, ?_⟩
      intro s _ t _
      simp [patchedProcess, hω]
    · -- Proof comment: off the master null set, use the witness-family transfer lemma.
      simpa using
        locallyHolderWith_patchedProcess
          (μ := μ)
          (X := X)
          (YBase := data.YBase)
          (YWitness := data.YWitness)
          (N := data.N)
          (rBase := data.rBase)
          data.hBaseIndexLe
          data.hPatch
          data.hYWitnessHolder
          hγ0
          hAdmissible
          hω
          0
  · intro T α β C γ hKol hγ0 hγlt ε hε
    -- Proof comment: the deterministic event estimate is the finite-horizon transfer lemma applied
    -- to the packaged patched process.
    simpa using
      exists_deterministicHolderConstant_of_patchedProcess
        (μ := μ)
        (X := X)
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
