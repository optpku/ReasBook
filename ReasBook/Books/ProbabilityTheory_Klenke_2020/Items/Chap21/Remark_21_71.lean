/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The canonical square-variation process of a continuous local martingale `M`, obtained by
choosing the unique witness supplied by Theorem 21.70. -/
abbrev continuousSquareVariationProcess
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    NNReal → Ω → ℝ :=
  Classical.choose (existsUnique_continuousSquareVariationProcess hM)

/-- `HasPathwiseQuadraticVariationAlongSubsequence μ M P φ A` means that, for almost every sample
point, the quadratic partition sums of `M` along the partition-row subsequence `φ` converge at
every time `T` to the path `A`. -/
def HasPathwiseQuadraticVariationAlongSubsequence
    (μ : Measure Ω) (M : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (φ : ℕ → ℕ) (A : NNReal → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ T : NNReal,
    Tendsto
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ n))
      atTop
      (𝓝 (A T ω))

-- Proof sketch: unfold `HasPathwiseQuadraticVariationAlongSubsequence`; the statement is exactly
-- the almost-sure simultaneous convergence of the partition-square sums along the subsequence `φ`.
/-- Unfolding `HasPathwiseQuadraticVariationAlongSubsequence` says that along the subsequence `φ`,
the quadratic partition sums converge almost surely for every time horizon to the comparison
process `A`. -/
theorem hasPathwiseQuadraticVariationAlongSubsequence_iff
    (μ : Measure Ω) (M : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (φ : ℕ → ℕ) (A : NNReal → Ω → ℝ) :
    HasPathwiseQuadraticVariationAlongSubsequence μ M P φ A ↔
      ∀ᵐ ω ∂μ, ∀ T : NNReal,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ n))
          atTop
          (𝓝 (A T ω)) :=
  Iff.rfl

/-- Helper for Remark 21.71: the chosen bracket
`continuousSquareVariationProcess hM` satisfies the square-variation owner predicate from
Theorem 21.70. -/
lemma continuousSquareVariationProcess_spec
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousSquareVariationProcess ℱ μ M (continuousSquareVariationProcess hM) := by
  -- Proof comment: `continuousSquareVariationProcess hM` is defined by choosing the witness from
  -- `existsUnique_continuousSquareVariationProcess`.
  exact
    (Classical.choose_spec
      (existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hM)).1

/-- Helper for Remark 21.71: along any strict-mono partition-row subsequence, the omitted boundary
square tends to `0` by continuity of the sample path and vanishing mesh size. -/
lemma boundarySquare_tendsto_zero_alongSubsequence
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} {P : ℕ → ℕ → NNReal} [hP : IsAdmissiblePartitionSequence P]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (ω : Ω) (T : NNReal) :
    Tendsto
      (fun n ↦
        (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω) ^ 2)
      atTop
      (𝓝 0) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmesh
      (fun n ↦ bot_le) ?_
    intro n
    simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P (φ n) T
  have hpath :
      Tendsto
        (fun n ↦ M (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hpred
  have hdiff :
      Tendsto
        (fun n ↦ M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 (M T ω - M T ω)) := by
    -- Proof comment: continuity transports the predecessor-time convergence to vanishing path
    -- increments.
    exact tendsto_const_nhds.sub hpath
  -- Proof comment: squaring preserves the convergence of the vanishing boundary increment.
  simpa [pow_two] using hdiff.mul hdiff

/-- Helper for Remark 21.71: if the full quadratic sums converge at every nonnegative rational
horizon to a continuous monotone path, then the same holds at every horizon `T : NNReal`. -/
lemma tendsto_allTimes_of_ratConvergence_fullSums
    {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {Aω : NNReal → ℝ} (hAcont : Continuous Aω)
    (X : C(NNReal, ℝ)) {φ : ℕ → ℕ}
    (hRat :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum X P (q : NNReal) (φ n))
          atTop
          (𝓝 (Aω q))) :
    ∀ T : NNReal,
      Tendsto
        (fun n ↦ partitionSquareVariationFullSum X P T (φ n))
        atTop
        (𝓝 (Aω T)) := by
  intro T
  by_cases hT0 : T = 0
  · -- Proof comment: at time `0`, the target is already one of the rational-time limits.
    subst hT0
    simpa using hRat (0 : ℚ≥0)
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    by_cases ha_neg : a < 0
    · filter_upwards with n
      have hnonneg :
          0 ≤ partitionSquareVariationFullSum X P T (φ n) := by
        rw [partitionSquareVariationFullSum]
        refine Finset.sum_nonneg ?_
        intro k hk
        by_cases hle : P (φ n) (k + 1) ≤ T
        · simp [hle, sq_nonneg]
        · simp [hle]
      exact lt_of_lt_of_le ha_neg hnonneg
    · have hU :
        {t : NNReal | a < Aω t} ∈ 𝓝 T :=
        (hAcont.isOpen_preimage _ isOpen_Ioi).mem_nhds ha
      have hUleft : {t : NNReal | a < Aω t} ∈ 𝓝[<] T :=
        mem_nhdsWithin_of_mem_nhds hU
      have hTpos : (0 : NNReal) < T := pos_iff_ne_zero.mpr hT0
      rcases (mem_nhdsLT_iff_exists_Ioo_subset' hTpos).mp hUleft with
        ⟨l, hlT, hsubset⟩
      rcases (NNReal.lt_iff_exists_rat_btwn l T).mp hlT with ⟨q, hq0, hlq, hqT⟩
      let qNN : ℚ≥0 := ⟨q, hq0⟩
      have haq :
          a < Aω qNN := by
        exact hsubset ⟨by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hlq, by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT⟩
      have hqEventually :
          ∀ᶠ n : ℕ in atTop,
            a < partitionSquareVariationFullSum X P (qNN : NNReal) (φ n) :=
        ((tendsto_order.1 (hRat qNN)).1) a <| by
          simpa [qNN] using haq
      filter_upwards [hqEventually] with n hn
      exact lt_of_lt_of_le hn <|
        partitionSquareVariationFullSum_monotone X P (φ n) (le_of_lt <| by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT)
  · intro b hb
    have hU :
        {t : NNReal | Aω t < b} ∈ 𝓝 T :=
      (hAcont.isOpen_preimage _ isOpen_Iio).mem_nhds hb
    have hUright : {t : NNReal | Aω t < b} ∈ 𝓝[>] T :=
      mem_nhdsWithin_of_mem_nhds hU
    have hTsucc : T < T + 1 := by
      simpa using lt_add_of_pos_right T (show (0 : NNReal) < 1 by norm_num)
    rcases (mem_nhdsGT_iff_exists_Ioo_subset' hTsucc).mp hUright with ⟨u, hTu, hsubset⟩
    rcases (NNReal.lt_iff_exists_rat_btwn T u).mp hTu with ⟨q, hq0, hTq, hqu⟩
    let qNN : ℚ≥0 := ⟨q, hq0⟩
    have hqb :
        Aω qNN < b := by
      exact hsubset ⟨by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hTq, by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqu⟩
    have hqEventually :
        ∀ᶠ n : ℕ in atTop,
          partitionSquareVariationFullSum X P (qNN : NNReal) (φ n) < b :=
      ((tendsto_order.1 (hRat qNN)).2) b <| by
        simpa [qNN] using hqb
    filter_upwards [hqEventually] with n hn
    exact lt_of_le_of_lt
      (partitionSquareVariationFullSum_monotone X P (φ n) (le_of_lt <| by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hTq))
      hn

/-- Helper for Remark 21.71: the stage-`n` diagonal construction stores the current strict-mono
row subsequence after processing the first `n` encoded indices. -/
noncomputable def diagonalStageData
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) :
    ℕ → {φ : ℕ → ℕ // StrictMono φ}
  | 0 => ⟨id, strictMono_id⟩
  | n + 1 =>
      let prev := diagonalStageData f g hfg n
      match hdecode : Encodable.decode (α := ι) n with
      | some i =>
          ⟨prev.1 ∘
              Classical.choose (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae),
            prev.2.comp
              (Classical.choose_spec
                (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae)).1⟩
      | none =>
          ⟨prev.1 ∘ Nat.succ, prev.2.comp (strictMono_id.add_const 1)⟩

/-- Helper for Remark 21.71: the `n`th stage-refinement map is the strict-mono subsequence chosen
when the construction processes the encoded index `n`. -/
noncomputable def diagonalStageStepData
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    {φ : ℕ → ℕ // StrictMono φ} :=
  let prev := diagonalStageData f g hfg n
  match hdecode : Encodable.decode (α := ι) n with
  | some i =>
      let hs := ((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae
      ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩
  | none =>
      ⟨Nat.succ, strictMono_id.add_const 1⟩

/-- Helper for Remark 21.71: the stage-`n` subsequence extracted by the recursive diagonal
construction. -/
noncomputable def diagonalStageSubseq
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) : ℕ → ℕ :=
  (diagonalStageData f g hfg n).1

/-- Helper for Remark 21.71: the stage-`n` refinement step used by the recursive diagonal
construction. -/
noncomputable def diagonalStageStep
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) : ℕ → ℕ :=
  (diagonalStageStepData f g hfg n).1

/-- Helper for Remark 21.71: every stage subsequence in the recursive diagonal construction is
strictly increasing. -/
lemma diagonalStageSubseq_strictMono
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    StrictMono (diagonalStageSubseq f g hfg n) :=
  (diagonalStageData f g hfg n).2

/-- Helper for Remark 21.71: every single stage-refinement chosen by the recursive diagonal
construction is strictly increasing. -/
lemma diagonalStageStep_strictMono
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    StrictMono (diagonalStageStep f g hfg n) :=
  (diagonalStageStepData f g hfg n).2

/-- Helper for Remark 21.71: pointwise, the first projection of stage `n + 1` is obtained by
evaluating stage `n` at the chosen stage-`n` refinement. -/
lemma diagonalStageSubseq_succ_apply
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n m : ℕ) :
    diagonalStageSubseq f g hfg (n + 1) m =
      diagonalStageSubseq f g hfg n (diagonalStageStep f g hfg n m) := by
  classical
  -- Route correction: prove the successor identity on values, not by fighting definitional
  -- equality between the bundled subtype terms in `diagonalStageData` and `diagonalStageStepData`.
  -- Proof comment: after splitting on the decoded index at stage `n`, both sides simplify to the
  -- same value-level composition.
  cases hdecode : Encodable.decode (α := ι) n with
  | none =>
      have hstage :
          diagonalStageSubseq f g hfg (n + 1) =
            diagonalStageSubseq f g hfg n ∘ Nat.succ := by
        -- Proof comment: in the `none` branch, the recursion refines by the fixed successor map.
        funext k
        unfold diagonalStageSubseq
        rw [diagonalStageData, hdecode]
      have hstep : diagonalStageStep f g hfg n = Nat.succ := by
        -- Proof comment: the stored stage step is exactly the successor map in the `none` branch.
        funext k
        unfold diagonalStageStep diagonalStageStepData
        rw [hdecode]
      calc
        diagonalStageSubseq f g hfg (n + 1) m
            = (diagonalStageSubseq f g hfg n ∘ Nat.succ) m := by rw [hstage]
        _ = diagonalStageSubseq f g hfg n (diagonalStageStep f g hfg n m) := by
              rw [hstep]
              rfl
  | some i =>
      let prev := diagonalStageData f g hfg n
      let step :=
        Classical.choose (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae)
      have hstage :
          diagonalStageSubseq f g hfg (n + 1) =
            diagonalStageSubseq f g hfg n ∘ step := by
        -- Proof comment: in the decoded branch, the recursion composes with the chosen
        -- almost-surely convergent refinement.
        funext k
        unfold diagonalStageSubseq
        rw [diagonalStageData, hdecode]
      have hstep : diagonalStageStep f g hfg n = step := by
        -- Proof comment: the stored stage step is the same chosen refinement map.
        funext k
        unfold diagonalStageStep diagonalStageStepData
        rw [hdecode]
      calc
        diagonalStageSubseq f g hfg (n + 1) m
            = (diagonalStageSubseq f g hfg n ∘ step) m := by rw [hstage]
        _ = diagonalStageSubseq f g hfg n (diagonalStageStep f g hfg n m) := by
              rw [hstep]
              rfl

/-- Helper for Remark 21.71: each new stage is obtained by composing the previous stage with the
newly chosen strict-mono refinement. -/
lemma diagonalStageSubseq_succ
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    diagonalStageSubseq f g hfg (n + 1) =
      diagonalStageSubseq f g hfg n ∘ diagonalStageStep f g hfg n := by
  -- Proof comment: the function-level identity is the extensional wrapper around the pointwise
  -- stage-successor bridge.
  funext m
  exact diagonalStageSubseq_succ_apply f g hfg n m

/-- Helper for Remark 21.71: when stage `n` processes the encoded index `i`, the resulting stage
already has almost-sure pointwise convergence for that coordinate. -/
lemma diagonalStageSubseq_tendsto_decoded
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i))
    {n : ℕ} {i : ι} (hdecode : Encodable.decode (α := ι) n = some i) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun m ↦ f i (diagonalStageSubseq f g hfg (n + 1) m) ω) atTop (𝓝 (g i ω)) := by
  -- Proof comment: the stage update at index `n` is chosen by applying
  -- `exists_seq_tendsto_ae` to the already reindexed coordinate family.
  let prev := diagonalStageData f g hfg n
  rw [diagonalStageSubseq_succ]
  have hstep :
      (diagonalStageStepData f g hfg n).1 =
        Classical.choose (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae) := by
    unfold diagonalStageStepData
    rw [hdecode]
  simpa [diagonalStageSubseq, diagonalStageStep, hstep, prev, Function.comp] using
    (Classical.choose_spec (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae)).2

/-- Helper for Remark 21.71: for a family of stage refinements `τ`, the diagonal tail indexed from
`k` is obtained by recursively composing the later refinements. -/
def diagonalTailIndex (τ : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, n + 1 => τ k (diagonalTailIndex τ (k + 1) n)

/-- Helper for Remark 21.71: if each stage refinement `τ k` is strict mono, then the diagonal tail
indices increase at every successor step. -/
lemma diagonalTailIndex_lt_succ
    (τ : ℕ → ℕ → ℕ) (hτ : ∀ k : ℕ, StrictMono (τ k)) :
    ∀ n k : ℕ, diagonalTailIndex τ k n < diagonalTailIndex τ k (n + 1)
  | 0, k => by
      exact lt_of_le_of_lt (hτ k).le_apply (by simpa [diagonalTailIndex] using hτ k (Nat.lt_succ_self k))
  | n + 1, k => by
      simpa [diagonalTailIndex] using hτ k (diagonalTailIndex_lt_succ τ hτ n (k + 1))

/-- Helper for Remark 21.71: every fixed diagonal tail is a strict-mono map once the stage
refinements are strict mono. -/
lemma diagonalTailIndex_strictMono
    (τ : ℕ → ℕ → ℕ) (hτ : ∀ k : ℕ, StrictMono (τ k)) (k : ℕ) :
    StrictMono (diagonalTailIndex τ k) := by
  -- Proof comment: the explicit successor-step inequality is exactly the criterion for strict
  -- monotonicity on `ℕ`.
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  exact diagonalTailIndex_lt_succ τ hτ n k

/-- Helper for Remark 21.71: the diagonal subsequence is obtained by evaluating the `n`th stage
subsequence at the diagonal index `n`. -/
noncomputable def diagonalSubseq
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) : ℕ → ℕ :=
  fun n ↦ diagonalStageSubseq f g hfg n n

/-- Helper for Remark 21.71: every tail of the diagonal subsequence factors through each earlier
stage subsequence by the explicit `diagonalTailIndex`. -/
lemma diagonalSubseq_factorization
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) :
    ∀ k n : ℕ,
      diagonalSubseq f g hfg (k + n) =
        diagonalStageSubseq f g hfg k
          (diagonalTailIndex (diagonalStageStep f g hfg) k n)
  | k, 0 => by
      simp [diagonalSubseq, diagonalTailIndex]
  | k, n + 1 => by
      calc
        diagonalSubseq f g hfg (k + (n + 1))
            = diagonalSubseq f g hfg ((k + 1) + n) := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = diagonalStageSubseq f g hfg (k + 1)
              (diagonalTailIndex (diagonalStageStep f g hfg) (k + 1) n) :=
              diagonalSubseq_factorization f g hfg (k + 1) n
        _ = diagonalStageSubseq f g hfg k
              ((diagonalStageStep f g hfg k)
                (diagonalTailIndex (diagonalStageStep f g hfg) (k + 1) n)) := by
              rw [diagonalStageSubseq_succ]
              simp [Function.comp]
        _ = diagonalStageSubseq f g hfg k
              (diagonalTailIndex (diagonalStageStep f g hfg) k (n + 1)) := by
              simp [diagonalTailIndex]

/-- Helper for Remark 21.71: the diagonal subsequence of the recursive stage construction is
strictly increasing. -/
lemma diagonalSubseq_strictMono
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) :
    StrictMono (diagonalSubseq f g hfg) := by
  have hdiag :
      diagonalSubseq f g hfg = diagonalTailIndex (diagonalStageStep f g hfg) 0 := by
    funext n
    simpa [diagonalSubseq, diagonalStageSubseq, diagonalStageData] using
      diagonalSubseq_factorization f g hfg 0 n
  rw [hdiag]
  exact
    diagonalTailIndex_strictMono (diagonalStageStep f g hfg)
      (fun k ↦ diagonalStageStep_strictMono f g hfg k) 0

/-- Helper for Remark 21.71: a countable family of convergence-in-measure statements admits one
strict-mono subsequence along which every coordinate converges almost surely. -/
lemma existsStrictMonoSubsequence_tendstoAeOnEncodableFamily
    {μ : Measure Ω} {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      ∀ᵐ ω ∂μ, ∀ i : ι,
        Tendsto (fun n ↦ f i (φ.1 n) ω) atTop (𝓝 (g i ω)) := by
  -- Route correction: instead of packaging one global bad-event family, build nested stagewise
  -- subsequences and pass to the diagonal tail for each encoded coordinate separately.
  let φ : ℕ → ℕ := diagonalSubseq f g hfg
  have hφ : StrictMono φ := diagonalSubseq_strictMono f g hfg
  refine ⟨⟨φ, hφ⟩, ?_⟩
  rw [ae_all_iff]
  intro i
  let e : ℕ := Encodable.encode i
  have hstage :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ f i (diagonalStageSubseq f g hfg (e + 1) n) ω) atTop (𝓝 (g i ω)) := by
    -- Proof comment: stage `e + 1` is exactly the stage at which the encoded coordinate `i` is
    -- processed.
    exact
      diagonalStageSubseq_tendsto_decoded f g hfg
        (n := e) (i := i) (by simpa [e] using Encodable.encodek i)
  filter_upwards [hstage] with ω hω
  have htail :
      Tendsto (fun n ↦ f i (φ (n + (e + 1))) ω) atTop (𝓝 (g i ω)) := by
    have hEq :
        (fun n ↦ f i (φ (n + (e + 1))) ω) =
          fun n ↦
            f i
              (diagonalStageSubseq f g hfg (e + 1)
                (diagonalTailIndex (diagonalStageStep f g hfg) (e + 1) n))
              ω := by
      funext n
      simpa [φ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (fun m ↦ f i m ω) (diagonalSubseq_factorization f g hfg (e + 1) n)
    rw [hEq]
    exact
      hω.comp
        ((diagonalTailIndex_strictMono (diagonalStageStep f g hfg)
          (fun k ↦ diagonalStageStep_strictMono f g hfg k) (e + 1)).tendsto_atTop)
  -- Proof comment: convergence along a tail of a sequence is equivalent to convergence of the
  -- whole sequence at `atTop`.
  rw [← tendsto_add_atTop_iff_nat (e + 1)]
  simpa [φ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail

/-- Helper for Remark 21.71: one strict-mono subsequence of partition rows gives almost-sure
convergence at every nonnegative rational horizon simultaneously. -/
lemma existsStrictMonoSubsequence_tendstoAeOnNNRat
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      ∀ᵐ ω ∂μ, ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P (q : NNReal) (φ.1 n))
          atTop
          (𝓝 (continuousSquareVariationProcess hM q ω)) := by
  -- Route correction: use the generic encodable-family diagonal subsequence helper instead of
  -- trying to package all rational bad events into one Borel-Cantelli argument.
  let A := continuousSquareVariationProcess hM
  let g : ℚ≥0 → Ω → ℝ := fun q ω ↦ A q ω
  let f : ℚ≥0 → ℕ → Ω → ℝ := fun q n ω ↦
    weightedPartitionQuadraticVariationApproximationUpTo
      (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P (q : NNReal) n
  have hA := continuousSquareVariationProcess_spec hM
  have hfg : ∀ q : ℚ≥0, TendstoInMeasure μ (f q) atTop (g q) := by
    intro q
    simpa [f, g, A] using
      tendstoInMeasure_partitionQuadraticVariationApproximationUpTo
        (hM := hM) (hA := hA) (P := P) (T := (q : NNReal))
  simpa [f, g, A] using existsStrictMonoSubsequence_tendstoAeOnEncodableFamily f g hfg

-- Proof sketch: apply Theorem 21.70 (3) to the canonical bracket
-- `continuousSquareVariationProcess hM` to get fixed-time convergence in probability of the full
-- partition sequence, recursively extract subsequences with almost-sure convergence at each
-- nonnegative rational time, and then use the monotonicity and continuity of `T ↦ U_T^n` and
-- `T ↦ continuousSquareVariationProcess hM T` to upgrade convergence from `ℚ≥0` to all `T ≥ 0`.
/-- Remark 21.71: if `M` is a continuous local martingale, then there is a single subsequence of
partition rows for which the quadratic partition sums converge almost surely for every `T ≥ 0` to
the canonical square-variation process `continuousSquareVariationProcess hM`. -/
theorem exists_partition_subsequence_with_ae_pathwise_quadratic_variation
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      ∀ᵐ ω ∂μ, ∀ T : NNReal,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ.1 n))
          atTop
          (𝓝 (continuousSquareVariationProcess hM T ω)) := by
  -- Route correction: first settle one almost-sure event carrying every rational-time limit along
  -- a single diagonal subsequence, then transport those limits to all times through the
  -- clipped/full-sum comparison.
  obtain ⟨φ, hRat⟩ :=
    existsStrictMonoSubsequence_tendstoAeOnNNRat (P := P) (μ := μ) (ℱ := ℱ) hM
  refine ⟨φ, ?_⟩
  let A := continuousSquareVariationProcess hM
  have hA := continuousSquareVariationProcess_spec hM
  filter_upwards [hRat] with ω hω
  intro T
  let Xω : C(NNReal, ℝ) := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  have hAcont : Continuous fun t : NNReal ↦ A t ω := hA.continuous ω
  have hRatFull :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum Xω P (q : NNReal) (φ.1 n))
          atTop
          (𝓝 (A q ω)) := by
    intro q
    have hclip :
        Tendsto
          (fun n ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) Xω P (q : NNReal) (φ.1 n))
          atTop
          (𝓝 (A q ω)) := by
      simpa [Xω, A] using hω q
    have hboundary :=
      boundarySquare_tendsto_zero_alongSubsequence
        (μ := μ) (ℱ := ℱ) (P := P) hM φ.2 ω (q : NNReal)
    have hdiff :
        Tendsto
          (fun n ↦
            weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) Xω P (q : NNReal) (φ.1 n) -
              partitionSquareVariationFullSum Xω P (q : NNReal) (φ.1 n))
          atTop
          (𝓝 0) := by
      -- Proof comment: the clipped/full-sum discrepancy is squeezed by the vanishing boundary
      -- square.
      refine squeeze_zero ?_ ?_ hboundary
      · intro n
        rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
        exact
          (partitionSquareVariationSum_sub_fullSum_le_boundary
            Xω P (q : NNReal) (φ.1 n)).1
      · intro n
        rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
        exact
          (partitionSquareVariationSum_sub_fullSum_le_boundary
            Xω P (q : NNReal) (φ.1 n)).2
    -- Proof comment: subtract the vanishing boundary discrepancy from the rational clipped limits
    -- to recover rational full-sum convergence.
    simpa [A, sub_eq_add_neg, sub_sub_cancel] using hclip.sub hdiff
  have hAllFull :
      ∀ S : NNReal,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum Xω P S (φ.1 n))
          atTop
          (𝓝 (A S ω)) :=
    tendsto_allTimes_of_ratConvergence_fullSums hAcont Xω hRatFull
  have hboundaryT :=
    boundarySquare_tendsto_zero_alongSubsequence
      (μ := μ) (ℱ := ℱ) (P := P) hM φ.2 ω T
  have hdiffT :
      Tendsto
        (fun n ↦
          weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) Xω P T (φ.1 n) -
            partitionSquareVariationFullSum Xω P T (φ.1 n))
        atTop
        (𝓝 0) := by
    -- Proof comment: the same clipped/full-sum estimate works at the final horizon `T`.
    refine squeeze_zero ?_ ?_ hboundaryT
    · intro n
      rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
      exact (partitionSquareVariationSum_sub_fullSum_le_boundary Xω P T (φ.1 n)).1
    · intro n
      rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
      exact (partitionSquareVariationSum_sub_fullSum_le_boundary Xω P T (φ.1 n)).2
  have hEqClip :
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ.1 n)) =
        fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) Xω P T (φ.1 n) := by
    funext n
    rfl
  have hEq :
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) Xω P T (φ.1 n)) =
        fun n ↦
          partitionSquareVariationFullSum Xω P T (φ.1 n) +
            (weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) Xω P T (φ.1 n) -
              partitionSquareVariationFullSum Xω P T (φ.1 n)) := by
    funext n
    ring
  -- Proof comment: add back the vanishing boundary discrepancy to move from full sums to the
  -- original clipped quadratic sums at the arbitrary horizon `T`.
  rw [hEqClip, hEq]
  simpa [A] using (hAllFull T).add hdiffT

end ProbabilityTheory
