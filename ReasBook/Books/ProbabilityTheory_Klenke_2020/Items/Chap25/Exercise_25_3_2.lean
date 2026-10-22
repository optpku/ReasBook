/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Remark_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Topology

noncomputable section

universe u

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Domain-style sampling for the scalar pathwise Stratonovich layer:
* primary domain: pathwise stochastic integration along admissible partition sequences;
* primitive data: `partitionStratonovichApproximationUpTo`;
* source-facing owner: `HasPathwiseStratonovichIntegralAlong`;
* core/canonical bridge: `pathwiseStratonovichIntegralAlong`;
* square-variation owner abstraction: `HasContinuousSquareVariationAlongPartition`;
* source-facing set view: `𝒞_qvAlong`;
* chosen square-variation bridge: `HasSquareVariationAlongPartition`;
* relevant chapter owners in the same domain: `HasPathwiseItoIntegralAlong`,
  `pathwiseItoIntegralAlong`, and `IsContinuousLocalMartingale`. -/

/-- Helper for Exercise 25.3.2: the weighted quadratic partition sum of a path on `[0, T]` along
the `n`-th row of an admissible partition sequence. -/
def weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2

/-- Helper for Exercise 25.3.2: unfolding
`weightedPartitionQuadraticVariationApproximationUpTo` exposes the defining weighted sum. -/
@[simp] theorem weightedPartitionQuadraticVariationApproximationUpTo_def
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := rfl

/-- Helper for Exercise 25.3.2: every partition point strictly before the truncation index lies
strictly below the terminal time. -/
lemma partitionPoint_lt_time_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin :
        partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Exercise 25.3.2: every partition point that contributes to the truncated quadratic
sum up to `T` belongs to `Set.Icc 0 T`. -/
lemma partitionPoint_mem_Icc_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k ∈ Set.Icc 0 T := by
  constructor
  · exact bot_le
  · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)

/-- Helper for Exercise 25.3.2: constant weight `1` rewrites the weighted quadratic partition sum
as the square-variation partition sum from Definition 21.58. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n =
      partitionPVariationSum P 2 X T n := by
  rw [weightedPartitionQuadraticVariationApproximationUpTo_def, partitionPVariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [sq_abs]

/-- Helper for Exercise 25.3.2: if a path has square variation `V` along `P`, then the
constant-weight quadratic partition sums converge to `V`. -/
lemma tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
      atTop
      (nhds (V T)) := by
  convert HasSquareVariationAlongPartition.tendsto_partition_sum hX T using 1
  ext n
  exact weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum X P T n

/-- Helper for Exercise 25.3.2: the constant-weight quadratic partition sums are eventually
bounded by `|V T| + 1` once they converge to `V T`. -/
lemma eventually_le_weightedPartitionQuadraticVariationApproximationUpTo_one_abs_add_one
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    ∀ᶠ n in atTop,
      weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ≤
        |V T| + 1 := by
  have hconst :
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
        atTop
        (nhds (V T)) :=
    tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX T
  filter_upwards [hconst (Metric.ball_mem_nhds _ zero_lt_one)] with n hn
  have hupper : weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n <
      V T + 1 := by
    have hball :
        V T <
            1 + weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ∧
          weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n - V T <
            1 := by
      simpa [Metric.ball, Real.dist_eq, abs_lt] using hn
    linarith
  have hV_abs : V T + 1 ≤ |V T| + 1 := by
    gcongr
    exact le_abs_self (V T)
  exact le_of_lt (lt_of_lt_of_le hupper hV_abs)

/-- Helper for Exercise 25.3.2: if `k` lies before the truncation index, then the clipped
interval from `P n k` to `partitionNextPointUpTo P n k T` has size at most one mesh width. -/
lemma edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    edist (P n k) (partitionNextPointUpTo P n k T) ≤ partitionMesh P n := by
  have hleft : P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((instStrictMono_of_isAdmissiblePartitionSequence (P := P) n)
        (Nat.lt_succ_self k))
    · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)
  have hright : partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc : P n k < P n (k + 1) := by
      exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self k)
    rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
      tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc), max_eq_right, max_eq_right]
    · exact_mod_cast tsub_le_tsub_right hright _
    · simp
    · simp
  calc
    edist (P n k) (partitionNextPointUpTo P n k T)
        ≤ edist (P n k) (P n (k + 1)) := hdist
    _ ≤ partitionMesh P n := by
      rw [partitionMesh]
      exact le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k

/-- Helper for Exercise 25.3.2: covariance is unchanged after almost-everywhere replacement of
both real-valued coordinates. -/
lemma covariance_congr_ae
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Exercise 25.3.2: the exceptional set of Brownian paths that fail to be continuous.
-/
def brownianDiscontinuitySet
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (_hB : IsBrownianMotion μ B) : Set Ω :=
  {ω | ¬ Continuous (fun t : NNReal ↦ B t ω)}

/-- Helper for Exercise 25.3.2: the Brownian discontinuity set is null. -/
lemma brownianDiscontinuitySet_null
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    μ (_root_.brownianDiscontinuitySet (μ := μ) (B := B) hB) = 0 := by
  have hcont_ae : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB.continuous_paths
  simpa [_root_.brownianDiscontinuitySet] using (ae_iff.mp hcont_ae)

/-- Helper for Exercise 25.3.2: choose a measurable null superset of the Brownian discontinuity
set. -/
lemma brownianContinuousVersionExceptionSet_exists
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ∃ N : Set Ω,
      _root_.brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆ N ∧ MeasurableSet N ∧ μ N = 0 := by
  exact exists_measurable_superset_of_null
    (_root_.brownianDiscontinuitySet_null (μ := μ) (B := B) hB)

/-- Helper for Exercise 25.3.2: the measurable null exceptional set used to patch Brownian sample
paths. -/
def brownianContinuousVersionExceptionSet
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) : Set Ω :=
  Classical.choose (_root_.brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)

/-- Helper for Exercise 25.3.2: the Brownian discontinuity set is contained in the chosen
exceptional set. -/
lemma brownianDiscontinuitySet_subset_exceptionSet
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    _root_.brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆
      _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB :=
  (Classical.choose_spec
    (_root_.brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).1

/-- Helper for Exercise 25.3.2: the chosen Brownian exceptional set is measurable. -/
lemma brownianContinuousVersionExceptionSet_measurable
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    MeasurableSet (_root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) :=
  (Classical.choose_spec
    (_root_.brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.1

/-- Helper for Exercise 25.3.2: the chosen Brownian exceptional set is null. -/
lemma brownianContinuousVersionExceptionSet_null
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    μ (_root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) = 0 :=
  (Classical.choose_spec
    (_root_.brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.2

/-- Helper for Exercise 25.3.2: patch the Brownian motion by forcing it to be `0` on the chosen
measurable null exceptional set. -/
def brownianContinuousVersion
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    NNReal → Ω → ℝ :=
  letI : DecidablePred
      (fun ω' ↦ ω' ∈ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) :=
    Classical.decPred _
  fun t ω ↦
    if ω ∈ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then
      0
    else
      B t ω

/-- Helper for Exercise 25.3.2: each deterministic-time slice of the patched Brownian process is
measurable. -/
lemma brownianContinuousVersion_measurable
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ∀ t, Measurable (_root_.brownianContinuousVersion (μ := μ) (B := B) hB t) := by
  classical
  intro t
  simpa [_root_.brownianContinuousVersion] using
      (Measurable.ite
      (_root_.brownianContinuousVersionExceptionSet_measurable (μ := μ) (B := B) hB)
      measurable_const
      ((hB.stronglyMeasurable t).measurable))

/-- Helper for Exercise 25.3.2: every sample path of the patched Brownian process is continuous.
-/
lemma brownianContinuousVersion_continuous
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ∀ ω, Continuous (fun t ↦ _root_.brownianContinuousVersion (μ := μ) (B := B) hB t ω) := by
  classical
  intro ω
  by_cases hω : ω ∈ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
  · simpa [_root_.brownianContinuousVersion, hω] using
      (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · have hcont : Continuous (fun t : NNReal ↦ B t ω) := by
      by_contra hnot
      exact hω <|
        _root_.brownianDiscontinuitySet_subset_exceptionSet (μ := μ) (B := B) hB
          (by simpa [_root_.brownianDiscontinuitySet] using hnot)
    simpa [_root_.brownianContinuousVersion, hω] using hcont

/-- Helper for Exercise 25.3.2: away from the exceptional null set, the patched Brownian process
agrees with the original one at every time. -/
lemma brownianContinuousVersion_ae_eq
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      _root_.brownianContinuousVersion (μ := μ) (B := B) hB t ω = B t ω := by
  have hN_ae :
      ∀ᵐ ω ∂μ,
        ω ∉ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB := by
    exact compl_mem_ae_iff.mpr
      (_root_.brownianContinuousVersionExceptionSet_null (μ := μ) (B := B) hB)
  filter_upwards [hN_ae] with ω hω t
  simp [_root_.brownianContinuousVersion, hω]

/-- Helper for Exercise 25.3.2: the patched Brownian process is a modification of the original
Brownian motion. -/
lemma brownianContinuousVersion_areModifications
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    AreModifications μ B (_root_.brownianContinuousVersion (μ := μ) (B := B) hB) := by
  intro t
  filter_upwards [_root_.brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  simpa using (hω t).symm

/-- Helper for Exercise 25.3.2: Brownian increments over ordered times belong to `L²`. -/
lemma brownianIncrement_memLp_two
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {s t : NNReal} (_hst : s ≤ t) :
    MemLp (fun ω ↦ B t ω - B s ω) 2 μ := by
  exact (brownianEval_memLp_two hB t).sub (brownianEval_memLp_two hB s)

/-- Helper for Exercise 25.3.2: the time-`s` natural filtration is exactly the σ-algebra
generated by the full past path `u ↦ B u` on `Set.Iic s`. -/
lemma naturalFiltration_eq_pastPath
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (s : NNReal) :
    Filtration.natural B hB.stronglyMeasurable s =
      MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi := by
  change (⨆ j, ⨆ (_ : j ≤ s), MeasurableSpace.comap (B j) Real.measurableSpace) =
    MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le ?_
    intro j hj
    exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  · refine iSup_le ?_
    intro u
    exact le_iSup_of_le (u : NNReal) <| le_iSup_of_le u.2 le_rfl

/-- Helper for Exercise 25.3.2: the future Brownian increment is independent of the full past
path up to time `s`. -/
lemma brownianIncrement_indepFun_pastPath
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {s t : NNReal} (hst : s ≤ t) :
    IndepFun
      (fun ω (_ : Unit) ↦ B t ω - B s ω)
      (fun ω (u : Set.Iic s) ↦ B u ω)
      μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  have hJoint :
      IsGaussianProcess
        (Sum.elim
          (fun _ : Unit => fun ω ↦ B t ω - B s ω)
          (fun u : Set.Iic s => fun ω ↦ B u ω))
        μ := by
    refine hGaussian.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl _ =>
        refine ⟨{s, t}, ContinuousLinearMap.proj ⟨t, by simp⟩ - ContinuousLinearMap.proj ⟨s, by simp⟩, ?_⟩
        intro ω
        simp
    | inr u =>
        refine ⟨{(u : NNReal)}, ContinuousLinearMap.proj ⟨(u : NNReal), by simp⟩, ?_⟩
        intro ω
        simp
  refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hJoint ?_ ?_ ?_
  · intro _
    exact (hB.stronglyMeasurable t).aemeasurable.sub (hB.stronglyMeasurable s).aemeasurable
  · intro u
    exact (hB.stronglyMeasurable u).aemeasurable
  · intro _ u
    have hs_mem : MemLp (B s) 2 μ := brownianEval_memLp_two hB s
    have ht_mem : MemLp (B t) 2 μ := brownianEval_memLp_two hB t
    have hu_mem : MemLp (B u) 2 μ := brownianEval_memLp_two hB u
    have hu_le_s : (u : NNReal) ≤ s := u.2
    have hu_le_t : (u : NNReal) ≤ t := le_trans hu_le_s hst
    have ht_cov : cov[B t, B u; μ] = ((u : NNReal) : ℝ) := by
      simpa [inf_eq_right.mpr hu_le_t] using IsBrownianMotion.covariance_eq hB t u
    have hs_cov : cov[B s, B u; μ] = ((u : NNReal) : ℝ) := by
      simpa [inf_eq_right.mpr hu_le_s] using IsBrownianMotion.covariance_eq hB s u
    rw [covariance_fun_sub_left ht_mem hs_mem hu_mem, ht_cov, hs_cov]
    ring

/-- Helper for Exercise 25.3.2: the future Brownian increment is independent of the natural
filtration up to the starting time. -/
lemma brownianIncrement_indep_naturalFiltration
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {s t : NNReal} (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ))
      (Filtration.natural B hB.stronglyMeasurable s)
      μ := by
  let hIndep :
      Indep
        (MeasurableSpace.comap (fun ω (_ : Unit) ↦ B t ω - B s ω) MeasurableSpace.pi)
        (MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi)
        μ :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mp
      (_root_.brownianIncrement_indepFun_pastPath hB hst)
  simpa [_root_.naturalFiltration_eq_pastPath hB s, MeasurableSpace.pi] using hIndep

/-- Helper for Exercise 25.3.2: Brownian motion is a martingale in its natural filtration. -/
lemma brownianMartingale_natural
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    Martingale B (Filtration.natural B hB.stronglyMeasurable) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ℱB := Filtration.natural B hB.stronglyMeasurable
  have hB_adapted : StronglyAdapted ℱB B :=
    Filtration.stronglyAdapted_natural (u := B) hB.stronglyMeasurable
  refine ⟨hB_adapted, ?_⟩
  intro s t hst
  have hInc_meas : Measurable (fun ω ↦ B t ω - B s ω) :=
    (hB.stronglyMeasurable t).measurable.sub (hB.stronglyMeasurable s).measurable
  have hInc_stronglyMeas :
      StronglyMeasurable[
        MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ)]
        (fun ω ↦ B t ω - B s ω) :=
    (comap_measurable (fun ω ↦ B t ω - B s ω)).stronglyMeasurable
  have hInc_indep :
      Indep
        (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ))
        (ℱB s)
        μ :=
    _root_.brownianIncrement_indep_naturalFiltration hB hst
  have hInc_mean_zero : ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
    simpa using (brownianIncrement_hasLaw hB hst).integral_eq
  have hBs_int : Integrable (B s) μ :=
    (brownianEval_memLp_two hB s).integrable (by norm_num)
  have hInc_int : Integrable (fun ω ↦ B t ω - B s ω) μ :=
    (_root_.brownianIncrement_memLp_two hB hst).integrable (by norm_num)
  have hSplit : (fun ω ↦ B t ω) = fun ω ↦ B s ω + (B t ω - B s ω) := by
    funext ω
    ring
  have hInc_condExp_zero :
      μ[(fun ω ↦ B t ω - B s ω) | ℱB s] =ᵐ[μ] 0 := by
    refine
      (MeasureTheory.condExp_indep_eq
        hInc_meas.comap_le (ℱB.le s) hInc_stronglyMeas hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  calc
    μ[B t | ℱB s]
        =ᵐ[μ] μ[(fun ω ↦ B s ω + (B t ω - B s ω)) | ℱB s] := by
            exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[B s | ℱB s] + μ[(fun ω ↦ B t ω - B s ω) | ℱB s] := by
          exact condExp_add hBs_int hInc_int _
    _ =ᵐ[μ] B s + 0 := by
          filter_upwards
            [Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable (ℱB.le s) (hB_adapted s) hBs_int), hInc_condExp_zero]
            with ω hωs hωinc
          simp [hωs, hωinc]
    _ =ᵐ[μ] B s := by
          simp

/-- Helper for Exercise 25.3.2: timewise almost-everywhere equality preserves the martingale
property once the target process is already known to be strongly adapted. -/
lemma martingale_congr_ae
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration NNReal mΩ} {M N : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hN_stronglyAdapted : StronglyAdapted ℱ N) (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (hMN t)).symm.trans ((hM.condExp_ae_eq hst).trans (hMN s))

/-- Helper for Exercise 25.3.2: deterministic stopping at time `n` is just time clipping by
`min t n`. -/
lemma stoppedProcess_constTime_eq_min
    {Ω : Type u} [MeasurableSpace Ω] {M : NNReal → Ω → ℝ} (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t = M (min t n) := by
  ext ω
  rw [stoppedProcess]
  change M ((min (t : ENNReal) n).untopA) ω = M (min t n) ω
  by_cases ht : t ≤ n
  · have hmin : min (t : ENNReal) n = t := by
      exact min_eq_left (by exact_mod_cast ht)
    have htop : (t : ENNReal) ≠ ⊤ := by simp
    rw [hmin]
    have hUntop : WithTop.untop (t : ENNReal) htop = t := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (t : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_left ht]
  · have hnle : n ≤ t := le_of_not_ge ht
    have hmin : min (t : ENNReal) n = n := by
      exact min_eq_right (by exact_mod_cast hnle)
    have htop : (n : ENNReal) ≠ ⊤ := by simp
    rw [hmin]
    have hUntop : WithTop.untop (n : ENNReal) htop = n := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (n : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_right hnle]

/-- Helper for Exercise 25.3.2: conditioning the fixed terminal value `M n` along the clipped
filtration `ℱ_{t ∧ n}` gives a martingale in the original filtration. -/
lemma martingale_condExp_constTime
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (fun t ω ↦ μ[M n | ℱ (min t n)] ω) ℱ μ := by
  refine ⟨?_, ?_⟩
  · intro t
    exact stronglyMeasurable_condExp.mono (ℱ.mono (min_le_left t n))
  · intro s t hst
    by_cases hs : s ≤ n
    · have hsle : s ≤ min t n := le_min hst hs
      simpa [min_eq_left hs] using
        (condExp_condExp_of_le (ℱ.mono hsle) (ℱ.le (min t n)) :
          μ[μ[M n | ℱ (min t n)] | ℱ s] =ᵐ[μ] μ[M n | ℱ s])
    · have hnle : n ≤ s := le_of_not_ge hs
      have hnt : n ≤ t := hnle.trans hst
      have hnn :
          μ[M n | ℱ n] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
      have hEqt : (fun ω ↦ μ[M n | ℱ (min t n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnt] using hnn)
      have hEqs : (fun ω ↦ μ[M n | ℱ (min s n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnle] using hnn)
      have hconds :
          μ[M n | ℱ s] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le s)
          ((hM.stronglyMeasurable n).mono (ℱ.mono hnle)) (hM.integrable n)
      have hleft :
          μ[(fun ω ↦ μ[M n | ℱ (min t n)] ω) | ℱ s] =ᵐ[μ] μ[M n | ℱ s] :=
        condExp_congr_ae hEqt
      have hright :
          μ[M n | ℱ s] =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min s n)] ω := by
        exact (Filter.EventuallyEq.of_eq hconds).trans hEqs.symm
      exact hleft.trans hright

/-- Helper for Exercise 25.3.2: the process stopped at the deterministic time `n` agrees almost
everywhere with the conditional-expectation martingale built from `M n`. -/
lemma stoppedProcess_constTime_ae_eq_condExp
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min t n)] ω := by
  by_cases ht : t ≤ n
  · simpa [stoppedProcess_constTime_eq_min, min_eq_left ht] using (hM.condExp_ae_eq ht).symm
  · have hnle : n ≤ t := le_of_not_ge ht
    have hnn :
        μ[M n | ℱ n] = M n :=
      condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
    exact Filter.EventuallyEq.of_eq (by
      simpa [stoppedProcess_constTime_eq_min, min_eq_right hnle] using hnn.symm)

/-- Helper for Exercise 25.3.2: on a finite measure space, stopping a martingale at a deterministic
time gives a uniformly integrable martingale. -/
lemma martingale_uniformIntegrable_stoppedProcess_constTime
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ ∧
      UniformIntegrable (stoppedProcess M (fun _ ↦ (n : ENNReal))) 1 μ := by
  let N : NNReal → Ω → ℝ := fun t ω ↦ μ[M n | ℱ (min t n)] ω
  have hN_mart : Martingale N ℱ μ := martingale_condExp_constTime hM n
  have hStopped_strong : StronglyAdapted ℱ (stoppedProcess M (fun _ ↦ (n : ENNReal))) := by
    intro t
    simpa [N, stoppedProcess_constTime_eq_min] using
      ((hM.stronglyMeasurable (min t n)).mono (ℱ.mono (min_le_left t n)))
  have hStopped_eq :
      ∀ t : NNReal,
        N t =ᵐ[μ] stoppedProcess M (fun _ ↦ (n : ENNReal)) t := by
    intro t
    exact (stoppedProcess_constTime_ae_eq_condExp hM n t).symm
  have hStopped_mart :
      Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ :=
    martingale_congr_ae hN_mart hStopped_strong hStopped_eq
  letI : SigmaFinite μ := by infer_instance
  have hUI_N : UniformIntegrable N 1 μ := by
    simpa [N] using
      (hM.integrable n).uniformIntegrable_condExp fun t : NNReal ↦ ℱ.le (min t n)
  exact ⟨hStopped_mart, hUI_N.ae_eq hStopped_eq⟩

/-- Helper for Exercise 25.3.2: on a finite-measure space, deterministic times `τₙ ≡ n`
localize any martingale. -/
lemma martingale_isLocalMartingale_of_isFiniteMeasure
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using martingale_uniformIntegrable_stoppedProcess_constTime (μ := μ) (ℱ := ℱ) hM
      (n := (n : NNReal))

/-- Helper for Exercise 25.3.2: patching a Brownian motion on a measurable null set preserves the
Brownian owner and yields an everywhere-continuous version. -/
lemma brownianContinuousVersion_isBrownianMotion
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (_root_.brownianContinuousVersion (μ := μ) (B := B) hB) := by
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases hω : ω ∈ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
    · simp [_root_.brownianContinuousVersion, hω]
    · simp [_root_.brownianContinuousVersion, hω, hB.zero]
  · exact
      (IsBrownianMotion.isGaussianProcess hB).congr
        (fun t ↦ _root_.brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (_root_.brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.mean_zero hB t)
  · intro s t
    exact
      (covariance_congr_ae
        (_root_.brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (_root_.brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.covariance_eq hB s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      _root_.brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 25.3.2: the everywhere-continuous Brownian patch is a continuous local
martingale for its natural filtration. -/
lemma brownianContinuousVersion_isContinuousLocalMartingaleNatural
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsContinuousLocalMartingale
      (Filtration.natural
        (_root_.brownianContinuousVersion (μ := μ) (B := B) hB)
        (brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB).stronglyMeasurable)
      μ
      (_root_.brownianContinuousVersion (μ := μ) (B := B) hB) := by
  let Bc := _root_.brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB
  let ℱ := Filtration.natural Bc hBc.stronglyMeasurable
  have hMart : Martingale Bc ℱ μ :=
    _root_.brownianMartingale_natural (hB := hBc)
  refine
    { local_martingale := martingale_isLocalMartingale_of_isFiniteMeasure hMart
      continuous := ?_ }
  intro ω
  simpa [Bc] using _root_.brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 25.3.2: every positive-time Brownian marginal hits `0` with probability
zero. -/
lemma brownianFixedTime_zero_prob_eq_zero
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht : 0 < t) :
    μ {ω | B t.toNNReal ω = 0} = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have ht_nnreal_pos : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
  have hLaw : HasLaw (B t.toNNReal) (gaussianReal 0 t.toNNReal) μ :=
    hB.gaussian_marginal ht_nnreal_pos
  have hMeas : Measurable (B t.toNNReal) := (hB.stronglyMeasurable _).measurable
  calc
    μ {ω | B t.toNNReal ω = 0}
        = μ.map (B t.toNNReal) ({0} : Set ℝ) := by
            symm
            rw [Measure.map_apply hMeas (MeasurableSet.singleton 0)]
            rfl
    _ = gaussianReal 0 t.toNNReal ({0} : Set ℝ) := by rw [hLaw.map_eq]
    _ = 0 := by
          exact (noAtoms_gaussianReal (ne_of_gt ht_nnreal_pos)).measure_singleton 0

/-- The midpoint partition sum on `[0,T]` for the pathwise Stratonovich integral of the integrand
`f (X)` along the admissible partition sequence `P`. -/
def partitionStratonovichApproximationUpTo
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
      (X (partitionNextPointUpTo P n k T) - X (P n k))

-- Proof sketch: unfold `partitionStratonovichApproximationUpTo`; this is exactly the finite
-- midpoint Riemann sum over the truncated `n`-th partition row.
/-- Expanding `partitionStratonovichApproximationUpTo` gives the midpoint partition sum on
`[0,T]`. -/
theorem partitionStratonovichApproximationUpTo_def
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    partitionStratonovichApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
          (X (partitionNextPointUpTo P n k T) - X (P n k)) := rfl

/-- `HasPathwiseStratonovichIntegralAlong f X P I` means that the midpoint partition sums of `f`
against `X` along the admissible partition sequence `P` converge pointwise to the function `I`. -/
def HasPathwiseStratonovichIntegralAlong
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (I : NNReal → ℝ) : Prop :=
  ∀ T : NNReal,
    Tendsto (partitionStratonovichApproximationUpTo f X P T) atTop (nhds (I T))

-- Proof sketch: evaluate the defining predicate `HasPathwiseStratonovichIntegralAlong` at the
-- time horizon `T`.
/-- A pathwise Stratonovich integral realization yields convergence of the midpoint partition sums
at each fixed time horizon. -/
theorem HasPathwiseStratonovichIntegralAlong.tendsto
    {f : ℝ → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseStratonovichIntegralAlong f X P I) (T : NNReal) :
    Tendsto (partitionStratonovichApproximationUpTo f X P T) atTop (nhds (I T)) :=
  hI T

/-- The canonical bridge/view `pathwiseStratonovichIntegralAlong f X P` is the pointwise
`limUnder` realization of the midpoint partition sums. -/
noncomputable def pathwiseStratonovichIntegralAlong
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦ limUnder atTop (partitionStratonovichApproximationUpTo f X P T)

/-- Any chosen realization of the midpoint partition sums agrees with the canonical `limUnder`
bridge `pathwiseStratonovichIntegralAlong f X P`. -/
theorem HasPathwiseStratonovichIntegralAlong.eq_pathwiseStratonovichIntegralAlong
    {f : ℝ → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {I : NNReal → ℝ}
    (hI : HasPathwiseStratonovichIntegralAlong f X P I) :
    pathwiseStratonovichIntegralAlong f X P = I := by
  ext T
  simpa [pathwiseStratonovichIntegralAlong] using (hI T).limUnder_eq

namespace ProbabilityTheory

/-- Helper for Exercise 25.3.2: a concrete fixed-horizon limit identifies the canonical
`limUnder` value defining `pathwiseStratonovichIntegralAlong`. -/
theorem pathwiseStratonovichIntegralAlong_eq_of_tendsto
    {f : ℝ → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P]
    (T : NNReal) {L : ℝ}
    (hlim : Tendsto (partitionStratonovichApproximationUpTo f X P T) atTop (nhds L)) :
    pathwiseStratonovichIntegralAlong f X P T = L := by
  -- Proof comment: `pathwiseStratonovichIntegralAlong` is defined pointwise as the `limUnder`
  -- of the midpoint sums, so a concrete `Tendsto` witness computes that limit.
  simpa [pathwiseStratonovichIntegralAlong] using hlim.limUnder_eq

/-- Helper for Exercise 25.3.2: summing the clipped path increments over one partition row
telescopes to the total increment on `[0,T]`. -/
theorem partitionIncrementSum_eq_increment
    (G : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
        G (partitionNextPointUpTo P n k T) - G (P n k)) =
      G T - G 0 := by
  let m := partitionBoundIndex P n T
  -- Proof comment: split off the last clipped increment; every earlier successor is the genuine
  -- partition successor and telescopes, while the final clipped endpoint is exactly `T`.
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hm0 : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    rw [hm0, Finset.sum_range_zero, hT0]
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hkm : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hsum :
        ∀ r : ℕ,
          (Finset.sum (Finset.range r) fun j ↦ G (P n (j + 1)) - G (P n j)) =
            G (P n r) - G (P n 0) := by
      intro r
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          rw [Finset.sum_range_succ, ihr]
          abel
    rw [hkm, Finset.sum_range_succ]
    have hprefix :
        (Finset.sum (Finset.range k) fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
          G (P n k) - G (P n 0) := by
      -- Proof comment: before the last contributing index, truncation is inactive.
      have hraw :
          (Finset.sum (Finset.range k) fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
            Finset.sum (Finset.range k) fun j ↦ G (P n (j + 1)) - G (P n j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [m, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hnext : partitionNextPointUpTo P n j T = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_lt)
        rw [hnext]
      exact hraw.trans (hsum k)
    have hlast : G (partitionNextPointUpTo P n k T) - G (P n k) = G T - G (P n k) := by
      -- Proof comment: the last clipped successor is the time horizon itself.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hk] using le_partitionBoundIndex_time P n T
      rw [hnext]
    rw [hprefix, hlast]
    simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]

/-- Helper for Exercise 25.3.2: for the identity integrand, every midpoint partition row
telescopes exactly to the square increment, so no limit passage is needed. -/
theorem partitionStratonovichApproximationUpTo_id_eq_square_increment
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    partitionStratonovichApproximationUpTo id X P T n = ((X T) ^ 2 - (X 0) ^ 2) / 2 := by
  let m := partitionBoundIndex P n T
  -- Proof comment: split off the last truncated interval and telescope the genuine successor
  -- increments on the earlier partition points.
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hm0 : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    rw [partitionStratonovichApproximationUpTo_def, hm0, Finset.sum_range_zero, hT0]
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hkm : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hsum :
        ∀ r : ℕ,
          (Finset.sum (Finset.range r) fun j ↦
              ((X (P n (j + 1)) + X (P n j)) / 2) * (X (P n (j + 1)) - X (P n j))) =
            ((X (P n r)) ^ 2 - (X (P n 0)) ^ 2) / 2 := by
      intro r
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          rw [Finset.sum_range_succ, ihr]
          ring
    rw [partitionStratonovichApproximationUpTo_def, hkm, Finset.sum_range_succ]
    have hprefix :
        (Finset.sum (Finset.range k) fun j ↦
            id ((X (partitionNextPointUpTo P n j T) + X (P n j)) / 2) *
              (X (partitionNextPointUpTo P n j T) - X (P n j))) =
          ((X (P n k)) ^ 2 - (X (P n 0)) ^ 2) / 2 := by
      -- Proof comment: before the last index, truncation is inactive, so the prefix is the raw
      -- telescoping sum on the partition row.
      have hraw :
          (Finset.sum (Finset.range k) fun j ↦
              id ((X (partitionNextPointUpTo P n j T) + X (P n j)) / 2) *
                (X (partitionNextPointUpTo P n j T) - X (P n j))) =
            Finset.sum (Finset.range k) fun j ↦
              ((X (P n (j + 1)) + X (P n j)) / 2) * (X (P n (j + 1)) - X (P n j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [m, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hnext : partitionNextPointUpTo P n j T = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_lt)
        rw [hnext]
        rfl
      exact hraw.trans (hsum k)
    have hlast :
        id ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
            (X (partitionNextPointUpTo P n k T) - X (P n k)) =
          ((X T) ^ 2 - (X (P n k)) ^ 2) / 2 := by
      -- Proof comment: the final truncated successor is exactly the terminal time `T`.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hk] using le_partitionBoundIndex_time P n T
      rw [hnext]
      dsimp
      ring_nf
    rw [hprefix, hlast]
    simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]
    ring

/-- Helper for Exercise 25.3.2: the identity-integrand midpoint sums define the square increment
realization on every path and every admissible partition sequence. -/
theorem hasPathwiseStratonovichIntegralAlong_id
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    HasPathwiseStratonovichIntegralAlong
      id
      X
      P
      (fun T ↦ ((X T) ^ 2 - (X 0) ^ 2) / 2) := by
  intro T
  -- Proof comment: the midpoint sums are already constant in `n` by the exact telescoping
  -- identity above.
  have hconst :
      partitionStratonovichApproximationUpTo id X P T =
        fun _ : ℕ ↦ ((X T) ^ 2 - (X 0) ^ 2) / 2 := by
    funext n
    exact partitionStratonovichApproximationUpTo_id_eq_square_increment X P T n
  rw [hconst]
  exact tendsto_const_nhds

/-- Helper for Exercise 25.3.2: if `a < b`, then the midpoint linearization error of `F` on
`[a,b]` is controlled by the oscillation of `iteratedDeriv 2 F` on `Set.uIcc a b`. -/
theorem midpointTaylorIncrementError_le_of_lt
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    {a b ε : ℝ} (hab : a < b) (hε : 0 ≤ ε)
    (hosc :
      ∀ x ∈ Set.uIcc a b, ∀ y ∈ Set.uIcc a b,
        |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε) :
    |F b - F a - deriv F ((a + b) / 2) * (b - a)| ≤ ε * (b - a) ^ 2 := by
  let m : ℝ := (a + b) / 2
  have htwoε_nonneg : 0 ≤ 2 * ε := by
    nlinarith [hε]
  have ham : a < m := by
    dsimp [m]
    nlinarith
  have hm_mem_ab : m ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    constructor <;> dsimp [m] <;> nlinarith
  obtain ⟨ξ₁, hξ₁, hTaylor₁⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := F) (x₀ := a) (x := b) (n := 1) hab hF.contDiffOn
  have hTaylor₁' :
      F b - F a - deriv F a * (b - a) =
        iteratedDeriv 2 F ξ₁ * (b - a) ^ 2 / 2 := by
    -- Proof comment: rewrite the first-order Taylor polynomial at `a` through the ordinary
    -- derivative because `F` is differentiable on all of `ℝ`.
    have hTaylorEval :
        taylorWithinEval F 1 (Set.Icc a b) a b = F a + deriv F a * (b - a) := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval]
      have hderivWithin :
          derivWithin F (Set.Icc a b) a = deriv F a := by
        exact
          (hF.differentiable (by norm_num) a).derivWithin
            ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ⟨le_rfl, hab.le⟩)
      rw [iteratedDerivWithin_one, hderivWithin, smul_eq_mul]
      ring_nf
    rw [hTaylorEval] at hTaylor₁
    linarith
  have hDeriv : ContDiff ℝ 1 (deriv F) := by
    simpa using (hF.deriv' : ContDiff ℝ 1 (deriv F))
  obtain ⟨ξ₂, hξ₂, hTaylor₂⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := deriv F) (x₀ := a) (x := m) (n := 0) ham hDeriv.contDiffOn
  have hTaylor₂' :
      deriv F m - deriv F a = iteratedDeriv 2 F ξ₂ * (m - a) := by
    -- Proof comment: the zeroth-order Taylor remainder for `deriv F` is the first derivative of
    -- `deriv F`, which is `iteratedDeriv 2 F`.
    rw [taylor_within_zero_eval] at hTaylor₂
    simpa [m, iteratedDeriv_eq_iterate] using hTaylor₂
  have hξ₁_mem : ξ₁ ∈ Set.uIcc a b := by
    simp [Set.uIcc_of_le hab.le, hξ₁.1.le, hξ₁.2.le]
  have hξ₂_mem : ξ₂ ∈ Set.uIcc a b := by
    have hξ₂b : ξ₂ < b := lt_of_lt_of_le hξ₂.2 (show m ≤ b by
      dsimp [m]
      nlinarith)
    simp [Set.uIcc_of_le hab.le, hξ₂.1.le, hξ₂b.le]
  have hmain :
      F b - F a - deriv F m * (b - a) =
        (iteratedDeriv 2 F ξ₁ - iteratedDeriv 2 F ξ₂) * (b - a) ^ 2 / 2 := by
    have hmid : m - a = (b - a) / 2 := by
      dsimp [m]
      ring
    have hderivMul :
        deriv F m * (b - a) =
          deriv F a * (b - a) + iteratedDeriv 2 F ξ₂ * (b - a) ^ 2 / 2 := by
      have hderivEq :
          deriv F m = deriv F a + iteratedDeriv 2 F ξ₂ * (m - a) := by
        linarith [hTaylor₂']
      calc
        deriv F m * (b - a)
            = (deriv F a + iteratedDeriv 2 F ξ₂ * (m - a)) * (b - a) := by
                rw [hderivEq]
        _ = deriv F a * (b - a) + iteratedDeriv 2 F ξ₂ * (b - a) ^ 2 / 2 := by
              rw [hmid]
              ring
    nlinarith [hTaylor₁', hderivMul]
  calc
    |F b - F a - deriv F ((a + b) / 2) * (b - a)|
        = |(iteratedDeriv 2 F ξ₁ - iteratedDeriv 2 F ξ₂) * (b - a) ^ 2 / 2| := by
            simpa [m] using congrArg abs hmain
    _ = |iteratedDeriv 2 F ξ₁ - iteratedDeriv 2 F ξ₂| * (b - a) ^ 2 / 2 := by
          rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (b - a))]
          ring_nf
    _ ≤ ε * (b - a) ^ 2 := by
          have hbound : |iteratedDeriv 2 F ξ₁ - iteratedDeriv 2 F ξ₂| ≤ 2 * ε :=
            hosc ξ₁ hξ₁_mem ξ₂ hξ₂_mem
          have hsq_nonneg : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
          nlinarith [hbound, htwoε_nonneg, hsq_nonneg]

/-- Helper for Exercise 25.3.2: the midpoint linearization error of `F` on one interval is
controlled by the oscillation of `iteratedDeriv 2 F` on that interval, independently of the
order of the endpoints. -/
theorem midpointTaylorIncrementError_le
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    {a b ε : ℝ} (hε : 0 ≤ ε)
    (hosc :
      ∀ x ∈ Set.uIcc a b, ∀ y ∈ Set.uIcc a b,
        |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε) :
    |F b - F a - deriv F ((a + b) / 2) * (b - a)| ≤ ε * (b - a) ^ 2 := by
  by_cases hab : a = b
  · subst hab
    simp
  · rcases lt_or_gt_of_ne hab with hab_lt | hab_gt
    · exact midpointTaylorIncrementError_le_of_lt F hF hab_lt hε hosc
    · -- Proof comment: swap the endpoints to reduce to the ordered case.
      have hosc' :
          ∀ x ∈ Set.uIcc b a, ∀ y ∈ Set.uIcc b a,
            |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε := by
        simpa [Set.uIcc_comm] using hosc
      have hswap :=
        midpointTaylorIncrementError_le_of_lt F hF hab_gt hε hosc'
      have habs :
          |F b - F a - deriv F ((a + b) / 2) * (b - a)| =
            |F a - F b - deriv F ((b + a) / 2) * (a - b)| := by
        have hneg :
            F b - F a - deriv F ((a + b) / 2) * (b - a) =
              -(F a - F b - deriv F ((b + a) / 2) * (a - b)) := by
          ring
        rw [hneg, abs_neg]
      calc
        |F b - F a - deriv F ((a + b) / 2) * (b - a)|
            = |F a - F b - deriv F ((b + a) / 2) * (a - b)| := habs
        _ ≤ ε * (a - b) ^ 2 := hswap
        _ = ε * (b - a) ^ 2 := by ring

/-- Helper for Exercise 25.3.2: if every contributing partition interval sees only a small
oscillation of `iteratedDeriv 2 F`, then the whole midpoint row is close to the telescoping
increment `F (X T) - F (X 0)`. -/
theorem stratonovichMidpointIncrementError_le
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc :
      ∀ k ∈ Finset.range (partitionBoundIndex P n T),
        ∀ x ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
          ∀ y ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
            |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε) :
    |partitionStratonovichApproximationUpTo (deriv F) X P T n - (F (X T) - F (X 0))| ≤
      ε * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
  let FX : PathSpace :=
    ⟨fun t ↦ F (X t), hF.continuous.comp X.continuous⟩
  have hdecomp :
      partitionStratonovichApproximationUpTo (deriv F) X P T n - (F (X T) - F (X 0)) =
        Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
          deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) -
            (F (X (partitionNextPointUpTo P n k T)) - F (X (P n k))) := by
    -- Proof comment: subtract the telescoping increment row termwise from the midpoint row.
    have htel :
        Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
            FX (partitionNextPointUpTo P n k T) - FX (P n k)) =
          FX T - FX 0 := by
      simpa using
        (partitionIncrementSum_eq_increment (G := FX) (P := P) (T := T) (n := n))
    calc
      partitionStratonovichApproximationUpTo (deriv F) X P T n - (F (X T) - F (X 0))
          = partitionStratonovichApproximationUpTo (deriv F) X P T n - (FX T - FX 0) := by
              rfl
      _ =
            Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
                deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
                    (X (partitionNextPointUpTo P n k T) - X (P n k))) -
              Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
                FX (partitionNextPointUpTo P n k T) - FX (P n k)) := by
              rw [partitionStratonovichApproximationUpTo_def, htel]
      _ =
            Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
              deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
                  (X (partitionNextPointUpTo P n k T) - X (P n k)) -
                (FX (partitionNextPointUpTo P n k T) - FX (P n k)) := by
              rw [← Finset.sum_sub_distrib]
      _ =
            Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
              deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
                  (X (partitionNextPointUpTo P n k T) - X (P n k)) -
                (F (X (partitionNextPointUpTo P n k T)) - F (X (P n k))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [FX]
  calc
    |partitionStratonovichApproximationUpTo (deriv F) X P T n - (F (X T) - F (X 0))|
        = |Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
            deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
                (X (partitionNextPointUpTo P n k T) - X (P n k)) -
              (F (X (partitionNextPointUpTo P n k T)) - F (X (P n k))))| := by
            rw [hdecomp]
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
          |deriv F ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) -
            (F (X (partitionNextPointUpTo P n k T)) - F (X (P n k)))|) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
          ε * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          rw [abs_sub_comm]
          simpa [add_comm] using midpointTaylorIncrementError_le F hF hε (hosc k hk)
    _ = ε * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
          rw [weightedPartitionQuadraticVariationApproximationUpTo_def, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp

/-- Helper for Exercise 25.3.2: every truncated successor attached to a contributing partition
interval still lies in the fixed time interval `Set.Icc 0 T`. -/
theorem partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (_hk : k < partitionBoundIndex P n T) :
    partitionNextPointUpTo P n k T ∈ Set.Icc 0 T := by
  -- Proof comment: `partitionNextPointUpTo` is the truncating minimum with `T`, so its right
  -- endpoint stays below `T` and remains nonnegative in `NNReal`.
  constructor
  · exact bot_le
  · simp [partitionNextPointUpTo]

/-- Helper for Exercise 25.3.2: the second derivative of `F` has arbitrarily small oscillation on
every contributing partition interval once the partition mesh is small enough. -/
theorem eventually_midpointTaylorOscillation_on_partitionIntervals
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (partitionBoundIndex P n T),
        ∀ x ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
          ∀ y ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
            |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε := by
  let S : Set ℝ := X '' Set.uIcc (0 : NNReal) T
  have hScompact : IsCompact S := by
    -- Proof comment: the path range on the compact time interval `[[0, T]]` is compact.
    dsimp [S]
    exact isCompact_uIcc.image_of_continuousOn X.continuous.continuousOn
  have hSimage : S = Set.uIcc (sInf S) (sSup S) := by
    -- Proof comment: a continuous image of an interval in `ℝ` is again an interval.
    dsimp [S]
    simpa using (X.continuous.continuousOn.image_uIcc (a := (0 : NNReal)) (b := T))
  have hSecondUC : UniformContinuousOn (iteratedDeriv 2 F) S := by
    -- Proof comment: the compact path range lets us upgrade continuity of `F''` to uniform
    -- continuity there.
    exact hScompact.uniformContinuousOn_of_continuous
      (hF.continuous_iteratedDeriv' 2).continuousOn
  have hXPathUC : UniformContinuousOn X (Set.uIcc (0 : NNReal) T) := by
    -- Proof comment: the path itself is uniformly continuous on the compact time interval.
    exact isCompact_uIcc.uniformContinuousOn_of_continuous X.continuous.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hSecondUC) (2 * ε) (by linarith) with
    ⟨δ, hδ, hδ_spec⟩
  rcases (Metric.uniformContinuousOn_iff_le.mp hXPathUC) δ hδ with
    ⟨η, hη, hη_spec⟩
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh P n ≤ ENNReal.ofReal η := by
    -- Proof comment: admissibility makes the partition mesh eventually smaller than the time
    -- modulus obtained from uniform continuity of `X`.
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P)))
          (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη) with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  filter_upwards [hmesh] with n hn k hk x hx y hy
  have hk_lt : k < partitionBoundIndex P n T := Finset.mem_range.mp hk
  have hPk : P n k ∈ Set.uIcc (0 : NNReal) T := by
    exact Set.Icc_subset_uIcc
      (partitionPoint_mem_Icc_of_lt_partitionBoundIndex P n k T hk_lt)
  have hNk : partitionNextPointUpTo P n k T ∈ Set.uIcc (0 : NNReal) T := by
    exact Set.Icc_subset_uIcc
      (partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex P n k T hk_lt)
  have hleftS : X (P n k) ∈ S := by
    exact ⟨P n k, hPk, rfl⟩
  have hrightS : X (partitionNextPointUpTo P n k T) ∈ S := by
    exact ⟨partitionNextPointUpTo P n k T, hNk, rfl⟩
  have htime :
      dist (P n k) (partitionNextPointUpTo P n k T) ≤ η := by
    -- Proof comment: the time gap on each contributing interval is bounded by one mesh width.
    have hedist :
        edist (P n k) (partitionNextPointUpTo P n k T) ≤ ENNReal.ofReal η := by
      exact
        (edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh P n k T hk_lt).trans hn
    exact (edist_le_ofReal (le_of_lt hη)).1 hedist
  have hendpoint :
      dist (X (P n k)) (X (partitionNextPointUpTo P n k T)) ≤ δ := by
    -- Proof comment: once the time gap is within the mesh modulus, the path values are within the
    -- spatial modulus required for `F''`.
    exact hη_spec (P n k) hPk (partitionNextPointUpTo P n k T) hNk htime
  have hinterval :
      Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)) ⊆ S := by
    -- Proof comment: because the path range `S` is an interval containing both endpoints, it also
    -- contains the whole unordered interval between them.
    rw [hSimage] at hleftS hrightS ⊢
    exact Set.uIcc_subset_uIcc hleftS hrightS
  have hxS : x ∈ S := hinterval hx
  have hyS : y ∈ S := hinterval hy
  have hxy : dist x y ≤ δ := by
    -- Proof comment: every point inside the unordered interval between the endpoint values is at
    -- most the endpoint distance apart.
    exact (Real.dist_le_of_mem_uIcc hx hy).trans hendpoint
  simpa [Real.dist_eq] using hδ_spec x hxS y hyS hxy

/-- Helper for Exercise 25.3.2: the midpoint sums for `F' (X)` converge at a fixed horizon `T`
to the telescoping increment `F (X T) - F (X 0)`. -/
theorem tendsto_partitionStratonovichApproximationUpTo_deriv_to_increment
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] {V : PathwiseProcess}
    (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    Tendsto
      (partitionStratonovichApproximationUpTo (deriv F) X P T)
      atTop
      (nhds (F (X T) - F (X 0))) := by
  -- Route correction: the main theorem no longer reasons through `limUnder` directly. The
  -- remaining work is only the fixed-horizon compact-range uniform-continuity step that makes the
  -- rowwise midpoint error from `stratonovichMidpointIncrementError_le` arbitrarily small.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let ε' : ℝ := ε / (2 * (|V T| + 1))
  have hden_pos : 0 < 2 * (|V T| + 1) := by
    positivity
  have hmass_factor_ne : |V T| + 1 ≠ 0 := by
    positivity
  have hε' : 0 < ε' := by
    -- Proof comment: the quadratic-mass bound is positive, so the rescaled midpoint error budget
    -- is positive as well.
    dsimp [ε']
    exact div_pos hε hden_pos
  have hosc :
      ∀ᶠ n in atTop,
        ∀ k ∈ Finset.range (partitionBoundIndex P n T),
          ∀ x ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
            ∀ y ∈ Set.uIcc (X (P n k)) (X (partitionNextPointUpTo P n k T)),
              |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ 2 * ε' :=
    eventually_midpointTaylorOscillation_on_partitionIntervals F hF X P T hε'
  have hmass :
      ∀ᶠ n in atTop,
        weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ≤
          |V T| + 1 :=
    eventually_le_weightedPartitionQuadraticVariationApproximationUpTo_one_abs_add_one X P hX T
  have hfinal :
      ∀ᶠ n in atTop,
        dist
            (partitionStratonovichApproximationUpTo (deriv F) X P T n)
            (F (X T) - F (X 0)) < ε := by
    filter_upwards [hosc, hmass] with n hosc_n hmass_n
    have herr :
        |partitionStratonovichApproximationUpTo (deriv F) X P T n - (F (X T) - F (X 0))| ≤
          ε' * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
      -- Proof comment: the eventual oscillation control activates the rowwise midpoint Taylor
      -- estimate.
      exact stratonovichMidpointIncrementError_le F hF X P T n (le_of_lt hε') hosc_n
    have hscaled :
        ε' * weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) X P T n < ε := by
      -- Proof comment: the chosen rescaling `ε'` turns the eventual quadratic-mass bound into a
      -- strict `ε`-bound.
      calc
        ε' * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n
            ≤ ε' * (|V T| + 1) := by
                gcongr
        _ = ε / 2 := by
              have hhalf : ε' * (|V T| + 1) = ε / 2 := by
                dsimp [ε']
                field_simp [hmass_factor_ne]
              exact hhalf
        _ < ε := by
              linarith
    exact lt_of_le_of_lt
      (by simpa [Real.dist_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using herr)
      hscaled
  rcases Filter.eventually_atTop.1 hfinal with ⟨N, hN⟩
  exact ⟨N, hN⟩

-- Proof sketch: compare the midpoint sums with the left-point Itô sums and use a second-order
-- Taylor expansion of `F` along each partition interval. The quadratic-variation convergence of
-- `X` along `P` controls the correction term and yields convergence of the midpoint sums.
/-- If `V` is a chosen square-variation process of `X` along `P` and `F ∈ C²(ℝ)`, then the
midpoint sums for `F' (X)` admit the canonical pathwise Stratonovich-integral realization
`pathwiseStratonovichIntegralAlong (deriv F) X P`. -/
theorem hasPathwiseStratonovichIntegralAlong_deriv_of_hasSquareVariationAlongPartition
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] {V : PathwiseProcess}
    (hX : HasSquareVariationAlongPartition X P V) :
    HasPathwiseStratonovichIntegralAlong
      (deriv F)
      X
      P
      (pathwiseStratonovichIntegralAlong (deriv F) X P) := by
  intro T
  -- Proof comment: the public owner statement is now just the fixed-horizon convergence theorem.
  have hlim :=
    tendsto_partitionStratonovichApproximationUpTo_deriv_to_increment F hF X P hX T
  have hEq :
      pathwiseStratonovichIntegralAlong (deriv F) X P T = F (X T) - F (X 0) :=
    pathwiseStratonovichIntegralAlong_eq_of_tendsto T hlim
  simpa [hEq] using hlim

/-- For `X ∈ 𝒞_qv^P` and `F ∈ C²(ℝ)`, the midpoint sums for `F' (X)` admit the canonical
pathwise Stratonovich-integral realization `pathwiseStratonovichIntegralAlong (deriv F) X P`. -/
theorem hasPathwiseStratonovichIntegralAlong_deriv
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    HasPathwiseStratonovichIntegralAlong
      (deriv F)
      X
      P
      (pathwiseStratonovichIntegralAlong (deriv F) X P) := by
  rcases hX with ⟨V, hV⟩
  exact
    hasPathwiseStratonovichIntegralAlong_deriv_of_hasSquareVariationAlongPartition
      F hF X P hV

-- Proof sketch: apply the canonical realization from
-- `hasPathwiseStratonovichIntegralAlong_deriv` and rewrite the integrand using `hf`.
/-- Exercise 25.3.2 (1): if `P` is admissible, `X ∈ 𝒞_qv^P`, `F ∈ C²(ℝ)`, and `f = F'`, then the
midpoint partition sums defining the Stratonovich integral of `f (X)` admit a pathwise
realization on every interval `[0,T]`. -/
theorem exists_pathwiseStratonovichIntegralAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong f X P I := by
  simpa [hf] using
    (show
      ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong (deriv F) X P I from
        ⟨pathwiseStratonovichIntegralAlong (deriv F) X P,
          hasPathwiseStratonovichIntegralAlong_deriv F hF X P hX⟩)

/-- Source-facing `𝒞_qv^P` form of Exercise 25.3.2 (1). -/
theorem exists_pathwiseStratonovichIntegralAlong_of_mem_𝒞_qvAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P) :
    ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong f X P I := by
  simpa [mem_𝒞_qvAlong_iff] using
    exists_pathwiseStratonovichIntegralAlong f F hF hf X P
      ((mem_𝒞_qvAlong_iff X).1 hX)

-- Proof sketch: telescope the midpoint Taylor expansion
-- `F(X_{t'}) - F(X_t) = F'((X_t + X_{t'}) / 2) (X_{t'} - X_t) + o(|X_{t'} - X_t|²)`, sum over the
-- partition row, and use the quadratic-variation control to show that the remainder vanishes.
/-- If `V` is a chosen square-variation process of `X` along `P` and `F ∈ C²(ℝ)`, then the
canonical pathwise Stratonovich integral realization of `F' (X)` along `P` satisfies the
classical substitution rule on `[0,T]`. -/
theorem pathwiseStratonovich_substitution_formula_of_hasSquareVariationAlongPartition
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] {V : PathwiseProcess}
    (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := by
  -- Proof comment: compute the canonical `limUnder` value from the concrete fixed-horizon limit.
  symm
  exact pathwiseStratonovichIntegralAlong_eq_of_tendsto T
    (tendsto_partitionStratonovichApproximationUpTo_deriv_to_increment F hF X P hX T)

/-- For `X ∈ 𝒞_qv^P` and `F ∈ C²(ℝ)`, the canonical pathwise Stratonovich integral realization of
`F' (X)` along `P` satisfies the classical substitution rule on `[0,T]`. -/
theorem pathwiseStratonovich_substitution_formula
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := by
  rcases hX with ⟨V, hV⟩
  exact
    pathwiseStratonovich_substitution_formula_of_hasSquareVariationAlongPartition
      F hF X P hV T

/-- Source-facing `𝒞_qv^P` form of the pathwise Stratonovich substitution formula. -/
theorem pathwiseStratonovich_substitution_formula_of_mem_𝒞_qvAlong
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := by
  simpa [mem_𝒞_qvAlong_iff] using
    pathwiseStratonovich_substitution_formula F hF X P
      ((mem_𝒞_qvAlong_iff X).1 hX) T

/-- Every chosen realization of the midpoint sums for `F' (X)` agrees with the canonical bridge
`pathwiseStratonovichIntegralAlong`, so the substitution formula also holds in the textbook form
for an arbitrary pathwise Stratonovich-integral realization `I`. -/
theorem pathwiseStratonovich_substitution_formula_of_hasPathwiseStratonovichIntegralAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    {I : NNReal → ℝ} (hI : HasPathwiseStratonovichIntegralAlong f X P I)
    (T : NNReal) :
    F (X T) - F (X 0) = I T := by
  rw [← hI.eq_pathwiseStratonovichIntegralAlong]
  simpa [hf] using pathwiseStratonovich_substitution_formula F hF X P hX T

-- Proof sketch: take a nonconstant continuous local martingale, for instance Brownian motion,
-- and realize its Stratonovich self-integral along an admissible partition sequence. Applying the
-- substitution formula to `F(x) = x^2 / 2` identifies the canonical self-integral on a
-- full-measure set of sample paths with the explicit square process
-- `t ↦ (M_t^2 - M_0^2) / 2`, which is not a local martingale in general because the Itô
-- correction coming from the quadratic variation has been absorbed.
/-- Exercise 25.3.2 (3): in contrast with the Itô integral, the Stratonovich integral with
respect to a continuous local martingale is not a local martingale in general; concretely, there
exists a filtered probability space carrying a continuous local martingale whose square process,
equivalently its Stratonovich self-integral on an almost-sure set of sample paths, fails to be a
local martingale. -/
theorem exists_continuousLocalMartingale_with_non_localMartingale_stratonovich_square :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (Q : ProbabilityMeasure Ω')
      (ℱ : Filtration NNReal mΩ') (M : NNReal → Ω' → ℝ) (P : ℕ → ℕ → NNReal),
        ∃ (_ : IsAdmissiblePartitionSequence P)
          (hM : IsContinuousLocalMartingale ℱ (Q : Measure Ω') M),
            (∀ᵐ ω ∂(Q : Measure Ω'),
              HasPathwiseStratonovichIntegralAlong
                id
                ⟨fun t ↦ M t ω, hM.continuous ω⟩
                P
                (fun t ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2)) ∧
            ¬ IsLocalMartingale
              ℱ
              (Q : Measure Ω')
              (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) := by
  let μstd : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hμstd_mean_zero : ∫ x, x ∂(μstd : Measure ℝ) = 0 := by
    change ∫ x, x ∂gaussianReal (0 : ℝ) (1 : NNReal) = 0
    exact integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hμstd_memLp : MemLp id 2 (μstd : Measure ℝ) := by
    simpa [μstd] using (IsGaussian.memLp_two_id (μ := gaussianReal 0 1))
  rcases exists_skorohod_embedding_in_natural_filtration μstd hμstd_mean_zero hμstd_memLp with
    ⟨Ω', mΩ', Q, W, hW, _τ, _, _, _⟩
  letI : MeasurableSpace Ω' := mΩ'
  let μ : Measure Ω' := (Q : Measure Ω')
  letI : IsProbabilityMeasure μ := inferInstance
  let M : NNReal → Ω' → ℝ := _root_.brownianContinuousVersion (μ := μ) (B := W) hW
  have hMBrownian : IsBrownianMotion μ M := by
    simpa [M] using brownianContinuousVersion_isBrownianMotion (μ := μ) (B := W) hW
  let ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω') :=
    Filtration.natural M hMBrownian.stronglyMeasurable
  have hM : IsContinuousLocalMartingale ℱ μ M := by
    simpa [M, ℱ] using
      brownianContinuousVersion_isContinuousLocalMartingaleNatural (μ := μ) (B := W) hW
  refine
    ⟨Ω', mΩ', Q, ℱ, M, Definition2158.dyadicPartitionSequence,
      Definition2158.dyadicPartitionSequence_isAdmissible, hM, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω ↦ by
      -- Proof comment: for the self-integrand `id`, the midpoint partition sums telescope on every
      -- path, so the Stratonovich identity is exact row by row.
      simpa [M] using
        hasPathwiseStratonovichIntegralAlong_id
          (X := (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace))
          (P := Definition2158.dyadicPartitionSequence)
  · intro hsq
    rcases
        (isLocalMartingale_iff
          (ℱ := ℱ)
          (μ := μ)
          (M := fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2)).1 hsq with
      ⟨_, τSeq, hτSeq⟩
    have hM0 : ∀ ω : Ω', M 0 ω = 0 := by
      classical
      intro ω
      by_cases hω : ω ∈ _root_.brownianContinuousVersionExceptionSet (μ := μ) (B := W) hW
      · simp [M, _root_.brownianContinuousVersion, hω]
      · simp [M, _root_.brownianContinuousVersion, hω, hW.zero]
    have hstopped_zero :
        ∀ n : ℕ,
          stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 =ᵐ[μ] 0 := by
      intro n
      rcases
          (isLocalizingSequence_iff
            (ℱ := ℱ)
            (μ := μ)
            (M := fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2)
            (τs := τSeq)).1 hτSeq with
        ⟨_, _, hmart⟩
      have hEq :
          ∫ ω, stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω ∂μ =
            ∫ ω, stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 0 ω ∂μ := by
        simpa using
          ((hmart n).1.setIntegral_eq (show (0 : NNReal) ≤ 1 by norm_num)
            (show MeasurableSet[ℱ 0] (Set.univ : Set Ω') by simp)).symm
      have hInt :
          Integrable
            (stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1) μ :=
        ((hmart n).1.integrable 1)
      have hnonneg :
          0 ≤ᵐ[μ] stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 := by
        exact Filter.Eventually.of_forall fun ω ↦ by
          dsimp [stoppedProcess]
          have h0ω : M 0 ω = 0 := hM0 ω
          simp [h0ω]
          positivity
      have hzeroInt :
          ∫ ω, stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω ∂μ = 0 := by
        have hzero0 :
            ∫ ω, stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 0 ω ∂μ = 0 := by
          simp [stoppedProcess]
        exact hEq.trans hzero0
      exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).1 hzeroInt
    have hstopped_zero_all :
        ∀ᵐ ω ∂μ,
          ∀ n : ℕ,
            stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω = 0 := by
      exact ae_all_iff.mpr hstopped_zero
    have htendsto :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n ↦
              stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω)
            atTop
            (𝓝 (((M 1 ω) ^ 2 - (M 0 ω) ^ 2) / 2)) :=
      ae_tendsto_stoppedProcess_at_time_of_localizingSequence hτSeq 1
    have hsq_one_zero :
        ∀ᵐ ω ∂μ, ((M 1 ω) ^ 2 - (M 0 ω) ^ 2) / 2 = 0 := by
      filter_upwards [hstopped_zero_all, htendsto] with ω hω hlim
      have hconst :
          Tendsto
            (fun n ↦
              stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω)
            atTop
            (𝓝 0) := by
          have hzero :
              (fun n ↦
                stoppedProcess (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) (τSeq n) 1 ω) =
                fun _ : ℕ ↦ 0 := by
            funext n
            simp [hω]
          rw [hzero]
          exact tendsto_const_nhds
      simpa using tendsto_nhds_unique hlim hconst
    have hM1zero : ∀ᵐ ω ∂μ, M 1 ω = 0 := by
      filter_upwards [hsq_one_zero] with ω hω
      have h0ω : M 0 ω = 0 := hM0 ω
      nlinarith [hω]
    have hmeas : MeasurableSet {ω | M 1 ω = 0} := by
      simpa only [Set.setOf_eq_eq_singleton] using
        (hMBrownian.stronglyMeasurable 1).measurable (MeasurableSet.singleton 0)
    have hprob_one : μ {ω | M 1 ω = 0} = 1 :=
      (mem_ae_iff_prob_eq_one hmeas).1 hM1zero
    have hprob_zero : μ {ω | M 1 ω = 0} = 0 := by
      simpa using brownianFixedTime_zero_prob_eq_zero (μ := μ) (B := M) hMBrownian
        (t := (1 : ℝ)) (by norm_num)
    have hzero_one : False := by
      have htmp := hprob_one
      simp [hprob_zero] at htmp
    exact hzero_one

end ProbabilityTheory
