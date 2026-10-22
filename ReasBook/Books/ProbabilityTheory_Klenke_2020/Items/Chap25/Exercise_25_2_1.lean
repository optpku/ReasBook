/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.ContinuousMap.Algebra
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21.Approximation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Lemma_25_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}

local notation "PathSpace" => C(NNReal, ℝ)

namespace BrownianItoIntegral

/-- Helper for Exercise 25.2.1: namespace alias for the deterministic-time Brownian truncation
process attached to a closure point. -/
noncomputable abbrev brownianItoIntegralTruncatedProcess
    {M : NNReal → Ω → ℝ} [BrownianItoIntegral μ ℱ M]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    NNReal → Ω → ℝ :=
  ProbabilityTheory.brownianItoIntegralTruncatedProcess (μ := μ) (ℱ := ℱ) M H

end BrownianItoIntegral

/-- Helper for Exercise 25.2.1: finite bracket energy means progressive measurability together
with almost-sure square integrability against the bracket density on every finite horizon. -/
def HasFiniteBracketEnergy
    {M : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : Prop :=
  ProgMeasurable ℱ H ∧
    ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦
          (H s.toNNReal ω) ^ 2 *
            (squareVariationDensity hbr s.toNNReal ω : ℝ))
        (Set.Icc (0 : ℝ) (T : ℝ))

/-- Helper for Exercise 25.2.1: finite bracket energy gives the exact finite-horizon
bracket-density integrability statement needed by the fixed-horizon Itô approximation route. -/
lemma finiteBracketEnergy_integrableOn_bracketDensity
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦
          (H s.toNNReal ω) ^ 2 *
            (squareVariationDensity hbr s.toNNReal ω : ℝ))
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: `HasFiniteBracketEnergy` is local square integrability of the Brownian-side
  -- coefficient, and the preceding square identity rewrites that condition into the source-side
  -- bracket-density form.
  filter_upwards [hFiniteEnergy.2 T] with ω hω
  exact hω

/-- Helper for Exercise 25.2.1: squaring the Brownian-side coefficient
`H * sqrt (d⟨M⟩ / dt)` recovers the source bracket-density integrand. -/
private lemma brownianRepresentationItoIntegrand_sq
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (t : NNReal) (ω : Ω) :
    (brownianRepresentationItoIntegrand hbr H t ω) ^ 2 =
      (H t ω) ^ 2 * (squareVariationDensity hbr t ω : ℝ) := by
  -- Proof comment: expand the Brownian-side coefficient and use `sqrt(a)^2 = a` for the
  -- nonnegative square-variation density.
  calc
    (brownianRepresentationItoIntegrand hbr H t ω) ^ 2
        = (H t ω) ^ 2 * (Real.sqrt (squareVariationDensity hbr t ω : ℝ)) ^ 2 := by
            simp [brownianRepresentationItoIntegrand, squareVariationDensityRoot, pow_two, mul_assoc,
              mul_left_comm, mul_comm]
    _ = (H t ω) ^ 2 * (squareVariationDensity hbr t ω : ℝ) := by
          rw [Real.sq_sqrt]
          positivity

/-- Helper for Exercise 25.2.1: `brownianRepresentationItoIntegrand` is linear in the source
integrand. -/
private lemma brownianRepresentationItoIntegrand_sub
    {M H K : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    brownianRepresentationItoIntegrand hbr (fun t ω ↦ H t ω - K t ω) =
      fun t ω ↦
        brownianRepresentationItoIntegrand hbr H t ω -
          brownianRepresentationItoIntegrand hbr K t ω := by
  funext t ω
  simp [brownianRepresentationItoIntegrand, sub_mul]

/-- Helper for Exercise 25.2.1: progressive measurability of `H` gives measurability of its
time-space representative `MeasureTheory.processToTimeSpaceFun H`. -/
private theorem measurable_processToTimeSpaceFun_of_progMeasurable
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H) :
    Measurable (MeasureTheory.processToTimeSpaceFun H) := by
  have huncurry : Measurable (Function.uncurry H) := hH_prog.measurable_uncurry
  have hswap : Measurable fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1) := by
    exact measurable_snd.real_toNNReal.prodMk measurable_fst
  -- Proof comment: `processToTimeSpaceFun H` is the measurable uncurry of `H` after the standard
  -- `(ω, t) ↦ (t.toNNReal, ω)` swap.
  simpa [MeasureTheory.processToTimeSpaceFun, Function.uncurry] using huncurry.comp hswap

/-- Helper for Exercise 25.2.1: a source-facing owner from the built `Theorem_25_21`
approximation submodule agrees almost everywhere at each deterministic time with the canonical
dyadic Itô value of the same integrand. -/
private theorem sourceOwner_aeEq_canonicalAtFixedTime
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hOwner :
      IsContinuousLocalMartingaleItoIntegralSourceOwner (hM := hM) H N)
    (t : NNReal) :
    N t =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H t := by
  rcases hOwner.indistinguishable_canonical with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
  -- Proof comment: the owner predicate already gives one null set controlling disagreement with
  -- the canonical process at every deterministic time, so the chosen time slice follows
  -- immediately.
  refine ae_iff.2 ?_
  exact measure_mono_null (hbad_sub t) hbad_null

/-- Helper for Exercise 25.2.1: any public Chapter 25 owner process agrees almost everywhere at
each deterministic time with the canonical dyadic Itô value of the same integrand. -/
private theorem itoIntegralOwner_aeEq_canonicalAtFixedTime
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hOwner :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegralOwner
        (μ := μ) (ℱ := ℱ) (hM := hM) H N)
    (t : NNReal) :
    N t =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H t := by
  rcases hOwner.indistinguishable_canonical with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
  -- Proof comment: the public owner predicate uses the same indistinguishability surface as the
  -- source-owner wrapper, so one fixed deterministic time again reduces to the stored null set.
  refine ae_iff.2 ?_
  exact measure_mono_null (hbad_sub t) hbad_null

/-- Helper for Exercise 25.2.1(i): almost-everywhere equality of measurable base-space functions
descends through a measure-preserving lift. -/
private lemma aeEq_descend_of_measurePreserving_local
    {Ω' : Type*} [MeasurableSpace Ω']
    (law : Measure Ω') (lift : Ω' → Ω)
    (hlift : MeasurePreserving lift law μ)
    {f g : Ω → ℝ}
    (hf : Measurable f)
    (hg : Measurable g)
    (hfg :
      (fun ω' ↦ f (lift ω')) =ᵐ[law]
        (fun ω' ↦ g (lift ω'))) :
    f =ᵐ[μ] g := by
  let s : Set Ω := {ω | f ω ≠ g ω}
  have hs : MeasurableSet s := by
    -- Proof comment: the disagreement set is measurable because both base-space functions are.
    change MeasurableSet {ω | ¬ f ω = g ω}
    exact (measurableSet_eq_fun hf hg).compl
  have hpre :
      {ω' | f (lift ω') ≠ g (lift ω')} = lift ⁻¹' s := by
    rfl
  have hpre_null : law (lift ⁻¹' s) = 0 := by
    -- Proof comment: the pulled-back disagreement set is exactly the witness-space exceptional
    -- set from the assumed almost-everywhere equality.
    rw [← hpre]
    exact (ae_iff.1 hfg)
  -- Proof comment: measure preservation turns the null preimage back into a null disagreement set
  -- on the base space.
  refine ae_iff.2 ?_
  calc
    μ s = Measure.map lift law s := by rw [hlift.map_eq]
    _ = law (lift ⁻¹' s) := by rw [Measure.map_apply hlift.measurable hs]
    _ = 0 := hpre_null

/-- Helper for Exercise 25.2.1(i): convergence in measure on a witness space descends through a
measure-preserving lift once the approximating functions and the limit are genuinely measurable on
the base space. -/
private lemma tendstoInMeasure_descend_of_measurePreserving
    {Ω' : Type*} [MeasurableSpace Ω']
    (law : Measure Ω') (lift : Ω' → Ω)
    (hlift : MeasurePreserving lift law μ)
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n : ℕ, Measurable (f n))
    (hg : Measurable g)
    (hfg :
      TendstoInMeasure law
        (fun n ω' ↦ f n (lift ω'))
        atTop
        (fun ω' ↦ g (lift ω'))) :
    TendstoInMeasure μ f atTop g := by
  intro ε hε
  have hpull := hfg ε hε
  have hEq :
      (fun n ↦
        law {ω' | ε ≤ edist (f n (lift ω')) (g (lift ω'))}) =
        (fun n ↦
          μ {ω | ε ≤ edist (f n ω) (g ω)}) := by
    funext n
    let s : Set Ω := {ω | ε ≤ edist (f n ω) (g ω)}
    have hs : MeasurableSet s := by
      -- Proof comment: the descending event is measurable because both the stage and the limit
      -- are measurable real-valued functions.
      exact measurableSet_le measurable_const ((hf n).edist hg)
    calc
      law {ω' | ε ≤ edist (f n (lift ω')) (g (lift ω'))}
          = law (lift ⁻¹' s) := by
              rfl
      _ = Measure.map lift law s := by rw [Measure.map_apply hlift.measurable hs]
      _ = μ s := by rw [hlift.map_eq]
      _ = μ {ω | ε ≤ edist (f n ω) (g ω)} := by
            rfl
  -- Proof comment: after identifying each witness-space error event as the pullback of the base
  -- error event, the witness-space convergence statement is literally the desired base one.
  simpa [hEq] using hpull

/-- Helper for Exercise 25.2.1(i): every fixed partition row is measurable in the sample point
once the coefficient and integrator are adapted. -/
private lemma measurable_partitionPathwiseItoApproximationUpTo_local
    {M H : NNReal → Ω → ℝ}
    (hHadapted : Adapted ℱ H)
    (hMadapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (row : ℕ) :
    Measurable fun ω ↦
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM_cont ω⟩ : PathSpace)
        P
        T
        row := by
  simp [partitionPathwiseItoApproximationUpTo]
  refine Finset.measurable_sum (Finset.range (partitionBoundIndex P row T)) ?_
  intro k hk
  have hCoeffMeas : Measurable fun ω ↦ H (P row k) ω := by
    exact hHadapted.measurable (i := P row k)
  have hNextMeas :
      Measurable fun ω ↦ M (partitionNextPointUpTo P row k T) ω := by
    exact hMadapted.measurable (i := partitionNextPointUpTo P row k T)
  have hLeftMeas : Measurable fun ω ↦ M (P row k) ω := by
    exact hMadapted.measurable (i := P row k)
  -- Proof comment: each summand is a product of measurable deterministic-time evaluations of the
  -- coefficient and integrator.
  simpa using hCoeffMeas.mul (hNextMeas.sub hLeftMeas)

/-- Helper for Exercise 25.2.1(i): at one deterministic horizon, the canonical dyadic Itô value
is measurable in the sample point. -/
private lemma measurable_canonicalItoIntegral_fixedTime_local
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (T : NNReal) :
    Measurable fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω := by
  have hH_adapted : Adapted ℱ H := hH_prog.stronglyAdapted.adapted
  have hM_adapted : Adapted ℱ M := hM.adapted
  have hStrong :
      StronglyMeasurable fun ω ↦
        limUnder atTop (fun row ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            Definition2158.dyadicPartitionSequence
            T
            row) := by
    -- Proof comment: each dyadic row is measurable in `ω`, so the pointwise `limUnder`
    -- defining the canonical fixed-time value is measurable as well.
    exact
      MeasureTheory.StronglyMeasurable.limUnder
        (l := atTop)
        (f := fun row ω ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            Definition2158.dyadicPartitionSequence
            T
            row)
        (hf := fun row ↦
          (measurable_partitionPathwiseItoApproximationUpTo_local
            (ℱ := ℱ)
            (M := M)
            (H := H)
            hH_adapted
            hM_adapted
            (fun ω ↦ hM.continuous ω)
            Definition2158.dyadicPartitionSequence
            T
            row).stronglyMeasurable)
  -- Proof comment: unfold the canonical fixed-time process once so the preceding `limUnder`
  -- measurability statement matches the target exactly.
  simpa [continuousLocalMartingaleItoIntegralProcess, pathwiseItoIntegralAlong] using
    hStrong.measurable

/-- Helper for Exercise 25.2.1(i): pulling a fixed partition row back along a sample-space map is
just evaluation of the base-space row function at the lifted sample point. -/
private lemma partitionPathwiseItoApproximationUpTo_pullback_eq_local
    {Ω' : Type*} [MeasurableSpace Ω']
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (lift : Ω' → Ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (row : ℕ) (ω' : Ω') :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t (lift ω'))
        (⟨fun t ↦ M t (lift ω'), hM.continuous (lift ω')⟩ : PathSpace)
        P
        T
        row =
      (fun ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          row)
        (lift ω') := by
  -- Proof comment: both sides are the same finite partition sum after beta-reducing the lifted
  -- sample point on the base-space row function.
  rfl

/-- Helper for Exercise 25.2.1(i): evaluating the canonical fixed-time dyadic Itô value after a
sample-space lift is the same as pulling back the base-space fixed-time value. -/
private lemma continuousLocalMartingaleItoIntegralProcess_pullback_eq_local
    {Ω' : Type*} [MeasurableSpace Ω']
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (lift : Ω' → Ω)
    (T : NNReal) (ω' : Ω') :
    pathwiseItoIntegralAlong
        (fun t ↦ H t (lift ω'))
        (⟨fun t ↦ M t (lift ω'), hM.continuous (lift ω')⟩ : PathSpace)
        Definition2158.dyadicPartitionSequence
        T =
      (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω) (lift ω') := by
  -- Proof comment: `continuousLocalMartingaleItoIntegralProcess` is defined pointwise as this
  -- canonical dyadic `pathwiseItoIntegralAlong`, so evaluation after `lift` is definitional.
  rfl

/-- Helper for Exercise 25.2.1(i): once witness-space convergence in measure has been obtained at
one fixed horizon, the remaining work is just measure-preserving descent plus the final almost-
everywhere identification of the target limit on the base space. -/
private theorem fixedHorizonPartitionApproximation_descend
    {Ω' : Type*} [MeasurableSpace Ω']
    (law : Measure Ω') (lift : Ω' → Ω)
    (hlift : MeasurePreserving lift law μ)
    {f : ℕ → Ω → ℝ} {N g : Ω → ℝ}
    (hf : ∀ n : ℕ, Measurable (f n))
    (hN_meas : Measurable N)
    (hWitness :
      TendstoInMeasure law
        (fun n ω' ↦ f n (lift ω'))
        atTop
        (fun ω' ↦ N (lift ω')))
    (hEq : N =ᵐ[μ] g) :
    TendstoInMeasure μ f atTop g := by
  have hBase :
      TendstoInMeasure μ f atTop N :=
    tendstoInMeasure_descend_of_measurePreserving
      (μ := μ) law lift hlift hf hN_meas hWitness
  -- Proof comment: after the witness-side convergence has been descended to the base space, the
  -- last identification is the fixed-time almost-everywhere equality of the two target versions.
  exact TendstoInMeasure.congr_right hEq hBase

/-- Helper for Exercise 25.2.1: the recursive diagonal stage data packages the strict-mono
subsequence available after processing the first `n` encoded coordinates. -/
private noncomputable def diagonalStageData
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
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

/-- Helper for Exercise 25.2.1: the stage-`n` refinement step used by the local diagonal
construction. -/
private noncomputable def diagonalStageStepData
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
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

/-- Helper for Exercise 25.2.1: the stage-`n` subsequence extracted by the recursive diagonal
construction. -/
private noncomputable def diagonalStageSubseq
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) : ℕ → ℕ :=
  (diagonalStageData f g hfg n).1

/-- Helper for Exercise 25.2.1: the stage-`n` refinement map stored by the recursive diagonal
construction. -/
private noncomputable def diagonalStageStep
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) : ℕ → ℕ :=
  (diagonalStageStepData f g hfg n).1

/-- Helper for Exercise 25.2.1: every stage subsequence in the recursive diagonal construction is
strictly increasing. -/
private lemma diagonalStageSubseq_strictMono
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    StrictMono (diagonalStageSubseq f g hfg n) :=
  (diagonalStageData f g hfg n).2

/-- Helper for Exercise 25.2.1: every one-step refinement chosen by the recursive diagonal
construction is strictly increasing. -/
private lemma diagonalStageStep_strictMono
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    StrictMono (diagonalStageStep f g hfg n) :=
  (diagonalStageStepData f g hfg n).2

/-- Helper for Exercise 25.2.1: pointwise, the first projection of stage `n + 1` is obtained by
evaluating stage `n` at the chosen stage-`n` refinement. -/
private lemma diagonalStageSubseq_succ_apply
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n m : ℕ) :
    diagonalStageSubseq f g hfg (n + 1) m =
      diagonalStageSubseq f g hfg n (diagonalStageStep f g hfg n m) := by
  classical
  -- Route correction: prove the successor identity on values instead of relying on a brittle
  -- bundled-subsequence definitional equality.
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

/-- Helper for Exercise 25.2.1: each new stage is obtained by composing the previous stage with
the newly chosen strict-mono refinement. -/
private lemma diagonalStageSubseq_succ
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) (n : ℕ) :
    diagonalStageSubseq f g hfg (n + 1) =
      diagonalStageSubseq f g hfg n ∘ diagonalStageStep f g hfg n := by
  -- Proof comment: the function-level identity is the extensional wrapper around the pointwise
  -- stage-successor bridge.
  funext m
  exact diagonalStageSubseq_succ_apply f g hfg n m

/-- Helper for Exercise 25.2.1: when stage `n` processes the encoded index `i`, the resulting
stage already has almost-sure pointwise convergence for that coordinate. -/
private lemma diagonalStageSubseq_tendsto_decoded
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i))
    {n : ℕ} {i : ι} (hdecode : Encodable.decode (α := ι) n = some i) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun m ↦ f i (diagonalStageSubseq f g hfg (n + 1) m) ω) atTop (𝓝 (g i ω)) := by
  -- Proof comment: stage `n + 1` is chosen by applying `exists_seq_tendsto_ae` to the reindexed
  -- coordinate family coming from the previous stage.
  let prev := diagonalStageData f g hfg n
  rw [diagonalStageSubseq_succ]
  have hstep :
      (diagonalStageStepData f g hfg n).1 =
        Classical.choose (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae) := by
    unfold diagonalStageStepData
    rw [hdecode]
  simpa [diagonalStageSubseq, diagonalStageStep, hstep, prev, Function.comp] using
    (Classical.choose_spec (((hfg i).comp prev.2.tendsto_atTop).exists_seq_tendsto_ae)).2

/-- Helper for Exercise 25.2.1: for a family of stage refinements `τ`, the diagonal tail indexed
from `k` is obtained by recursively composing the later refinements. -/
private def diagonalTailIndex (τ : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, n + 1 => τ k (diagonalTailIndex τ (k + 1) n)

/-- Helper for Exercise 25.2.1: if each stage refinement `τ k` is strict mono, then the diagonal
tail indices increase at every successor step. -/
private lemma diagonalTailIndex_lt_succ
    (τ : ℕ → ℕ → ℕ) (hτ : ∀ k : ℕ, StrictMono (τ k)) :
    ∀ n k : ℕ, diagonalTailIndex τ k n < diagonalTailIndex τ k (n + 1)
  | 0, k => by
      exact lt_of_le_of_lt (hτ k).le_apply (by simpa [diagonalTailIndex] using hτ k (Nat.lt_succ_self k))
  | n + 1, k => by
      simpa [diagonalTailIndex] using hτ k (diagonalTailIndex_lt_succ τ hτ n (k + 1))

/-- Helper for Exercise 25.2.1: every fixed diagonal tail is a strict-mono map once the stage
refinements are strict mono. -/
private lemma diagonalTailIndex_strictMono
    (τ : ℕ → ℕ → ℕ) (hτ : ∀ k : ℕ, StrictMono (τ k)) (k : ℕ) :
    StrictMono (diagonalTailIndex τ k) := by
  -- Proof comment: the explicit successor-step inequality is exactly the strict-monotonicity
  -- criterion on `ℕ`.
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  exact diagonalTailIndex_lt_succ τ hτ n k

/-- Helper for Exercise 25.2.1: the diagonal subsequence is obtained by evaluating the `n`th
stage subsequence at the diagonal index `n`. -/
private noncomputable def diagonalSubseq
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) : ℕ → ℕ :=
  fun n ↦ diagonalStageSubseq f g hfg n n

/-- Helper for Exercise 25.2.1: every tail of the diagonal subsequence factors through each
earlier stage subsequence by the explicit tail index. -/
private lemma diagonalSubseq_factorization
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
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

/-- Helper for Exercise 25.2.1: the diagonal subsequence of the recursive stage construction is
strictly increasing. -/
private lemma diagonalSubseq_strictMono
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
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

/-- Helper for Exercise 25.2.1: a countable family of convergence-in-measure statements admits
one strict-mono subsequence along which every coordinate converges almost surely. -/
private lemma existsStrictMonoSubsequence_tendstoAeOnEncodableFamily
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E)
    (hfg : ∀ i : ι, TendstoInMeasure μ (f i) atTop (g i)) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      ∀ᵐ ω ∂μ, ∀ i : ι,
        Tendsto (fun n ↦ f i (φ.1 n) ω) atTop (𝓝 (g i ω)) := by
  -- Proof comment: build the nested stagewise subsequences and then pass to the diagonal tail
  -- for each encoded coordinate separately.
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

/-- Helper for Exercise 25.2.1(ii): a countable family of pointwise convergent scalar sequences
admits one strict-mono subsequence with simultaneous convergence on every coordinate. -/
private theorem existsStrictMonoSubsequence_tendstoOnEncodableFamily
    {ι : Type*} [Encodable ι] {E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → E) (g : ι → E)
    (hfg : ∀ i : ι, Tendsto (fun n ↦ f i n) atTop (𝓝 (g i))) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      ∀ i : ι, Tendsto (fun n ↦ f i (φ.1 n)) atTop (𝓝 (g i)) := by
  let F : ι → ℕ → Unit → E := fun i n _ ↦ f i n
  let G : ι → Unit → E := fun i _ ↦ g i
  have hFG :
      ∀ i : ι, TendstoInMeasure (Measure.dirac ()) (F i) atTop (G i) := by
    intro i
    -- Proof comment: on the one-point probability space, convergence in measure is exactly the
    -- given pointwise convergence of the scalar sequence.
    exact
      tendstoInMeasure_of_tendsto_ae
        (fun _ ↦ aestronglyMeasurable_const)
        (Filter.Eventually.of_forall fun _ : Unit ↦ hfg i)
  obtain ⟨φ, hφ⟩ :=
    existsStrictMonoSubsequence_tendstoAeOnEncodableFamily
      (μ := Measure.dirac ()) F G hFG
  refine ⟨φ, ?_⟩
  have hpoint :
      ∀ i : ι,
        Tendsto (fun n ↦ F i (φ.1 n) ()) atTop (𝓝 (G i ())) := by
    have hdirac :
        ∀ᵐ _u ∂(Measure.dirac ()),
          ∀ i : ι, Tendsto (fun n ↦ F i (φ.1 n) _u) atTop (𝓝 (G i _u)) := hφ
    simpa using hdirac
  intro i
  simpa [F, G] using hpoint i

/-- Helper for Exercise 25.2.1(ii): from a countable family of convergent real sequences, one can
choose a strict-mono diagonal subsequence whose `n`th term simultaneously controls the first
`n + 1` rows at accuracy `1 / (n + 1)`. -/
private theorem existsStrictMono_diagonalControl
    {u : ℕ → ℕ → ℝ} {l : ℕ → ℝ}
    (hu : ∀ i : ℕ, Tendsto (fun n ↦ u i n) atTop (𝓝 (l i))) :
    ∃ ρ : ℕ → ℕ,
      StrictMono ρ ∧
        ∀ n : ℕ, ∀ i ≤ n, |u i (ρ n) - l i| < 1 / (n + 1 : ℝ) := by
  have hrow :
      ∀ n i : ℕ,
        ∃ N : ℕ, ∀ m ≥ N, |u i m - l i| < 1 / (n + 1 : ℝ) := by
    intro n i
    have hε : 0 < (1 : ℝ) / (n + 1 : ℝ) := by
      positivity
    have hball :
        ∀ᶠ m in atTop,
          u i m ∈ Metric.ball (l i) ((1 : ℝ) / (n + 1 : ℝ)) :=
      (hu i).eventually (Metric.ball_mem_nhds _ hε)
    have habs :
        ∀ᶠ m in atTop, |u i m - l i| < 1 / (n + 1 : ℝ) := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    rcases Filter.eventually_atTop.1 habs with ⟨N, hN⟩
    exact ⟨N, fun m hm ↦ hN m hm⟩
  choose B hB using hrow
  let ρ : ℕ → ℕ :=
    Nat.rec
      (B 0 0)
      (fun n ρn ↦ max (ρn + 1) ((Finset.range (n + 2)).sup fun i ↦ B (n + 1) i))
  have hρ : StrictMono ρ := by
    -- Proof comment: every new diagonal index is forced to lie strictly above the previous one.
    refine strictMono_nat_of_lt_succ ?_
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (ρ n)) (le_max_left _ _)
  have hρbound :
      ∀ n i : ℕ, i ≤ n → B n i ≤ ρ n := by
    intro n
    cases n with
    | zero =>
        intro i hi
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst hi0
        simp [ρ]
    | succ n =>
        intro i hi
        have hi_mem : i ∈ Finset.range (n + 2) := by
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
        have hsup :
            B (n + 1) i ≤ (Finset.range (n + 2)).sup fun j ↦ B (n + 1) j :=
          Finset.le_sup hi_mem
        exact le_trans hsup (le_max_right _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro n i hi
  -- Proof comment: stage `n` was chosen beyond the threshold of every row `i ≤ n`, so the
  -- corresponding row error is at most `1 / (n + 1)`.
  exact hB n i (ρ n) (hρbound n i hi)

/-- Helper for Exercise 25.2.1(ii): convergence on a finite family of rows can be made uniform on
one common tail. -/
private theorem eventually_forall_mem_finset_abs_sub_lt_of_tendsto
    {ι : Type*} [DecidableEq ι]
    {u : ι → ℕ → ℝ} {l : ι → ℝ}
    (S : Finset ι)
    (hu : ∀ i ∈ S, Tendsto (fun n ↦ u i n) atTop (𝓝 (l i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i ∈ S, |u i n - l i| < ε := by
  classical
  revert hu
  refine Finset.induction_on S ?_ ?_
  · intro _
    -- Proof comment: the empty control family imposes no inequalities.
    exact Filter.Eventually.of_forall fun _ i hi ↦ (Finset.notMem_empty i hi).elim
  · intro a S haS hInd huInsert
    have ha :
        ∀ᶠ n in atTop, |u a n - l a| < ε := by
      have hball :
          ∀ᶠ n in atTop, u a n ∈ Metric.ball (l a) ε :=
        (huInsert a (Finset.mem_insert_self a S)).eventually (Metric.ball_mem_nhds _ hε)
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have htail :
        ∀ᶠ n in atTop, ∀ i ∈ S, |u i n - l i| < ε := by
      have hTailHu : ∀ i ∈ S, Tendsto (fun n ↦ u i n) atTop (𝓝 (l i)) := by
        intro i hi
        exact huInsert i (Finset.mem_insert_of_mem hi)
      exact hInd hTailHu
    filter_upwards [ha, htail] with n hn htailn i hi
    rcases Finset.mem_insert.mp hi with rfl | hiS
    · exact hn
    · exact htailn i hiS

/-- Helper for Exercise 25.2.1(ii): a countable family of convergent real sequences admits a
strict-mono diagonal subsequence whose `n`th term simultaneously controls any prescribed finite
row set at stage `n`. -/
private theorem existsStrictMono_diagonalControlOnFiniteSets
    {ι : Type*} [DecidableEq ι]
    {u : ι → ℕ → ℝ} {l : ι → ℝ}
    (S : ℕ → Finset ι)
    (hu : ∀ i : ι, Tendsto (fun n ↦ u i n) atTop (𝓝 (l i))) :
    ∃ ρ : ℕ → ℕ,
      StrictMono ρ ∧
        ∀ n : ℕ, ∀ i ∈ S n, |u i (ρ n) - l i| < 1 / (n + 1 : ℝ) := by
  have hrow :
      ∀ n : ℕ,
        ∃ N : ℕ, ∀ m ≥ N, ∀ i ∈ S n, |u i m - l i| < 1 / (n + 1 : ℝ) := by
    intro n
    have hε : 0 < (1 : ℝ) / (n + 1 : ℝ) := by
      positivity
    have hEventual :
        ∀ᶠ m in atTop, ∀ i ∈ S n, |u i m - l i| < 1 / (n + 1 : ℝ) :=
      eventually_forall_mem_finset_abs_sub_lt_of_tendsto
        (S n) (fun i hi ↦ hu i) hε
    rcases Filter.eventually_atTop.1 hEventual with ⟨N, hN⟩
    exact ⟨N, fun m hm i hi ↦ hN m hm i hi⟩
  choose B hB using hrow
  let ρ : ℕ → ℕ :=
    Nat.rec
      (B 0)
      (fun n ρn ↦ max (ρn + 1) (B (n + 1)))
  have hρ : StrictMono ρ := by
    -- Proof comment: every new diagonal index is chosen past the previous one and past the next
    -- finite-set threshold.
    refine strictMono_nat_of_lt_succ ?_
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (ρ n)) (le_max_left _ _)
  have hρbound : ∀ n : ℕ, B n ≤ ρ n := by
    intro n
    cases n with
    | zero =>
        simp [ρ]
    | succ n =>
        exact le_max_right _ _
  refine ⟨ρ, hρ, ?_⟩
  intro n i hi
  -- Proof comment: the chosen stage `ρ n` lies beyond the common tail controlling the finite set
  -- `S n`, so every member of `S n` satisfies the required error estimate there.
  exact hB n (ρ n) (hρbound n) i hi

/-- Helper for Exercise 25.2.1(ii): a countable family of convergent real sequences admits a
strict-mono diagonal subsequence along which the self-indexed row errors tend to `0`. -/
private theorem existsStrictMono_diagonalSelfError
    {u : ℕ → ℕ → ℝ} {l : ℕ → ℝ}
    (hu : ∀ i : ℕ, Tendsto (fun n ↦ u i n) atTop (𝓝 (l i))) :
    ∃ ρ : ℕ → ℕ,
      StrictMono ρ ∧
        Tendsto (fun n ↦ u n (ρ n) - l n) atTop (𝓝 0) := by
  let S : ℕ → Finset ℕ := fun n ↦ {n}
  rcases existsStrictMono_diagonalControlOnFiniteSets S hu with ⟨ρ, hρ, hρcontrol⟩
  refine ⟨ρ, hρ, ?_⟩
  have hdiag :
      ∀ n : ℕ, |u n (ρ n) - l n| < 1 / (n + 1 : ℝ) := by
    intro n
    simpa [S] using hρcontrol n n (by simp [S])
  have hrate :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)) using 1
    funext n
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  have habs :
      Tendsto (fun n ↦ |u n (ρ n) - l n|) atTop (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        hrate
        (fun n ↦ abs_nonneg _)
        (fun n ↦ by simpa [one_div] using le_of_lt (hdiag n))
  -- Proof comment: the diagonal errors are squeezed by a deterministic rate that tends to `0`.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- Helper for Exercise 25.2.1: pass from fixed-horizon convergence in measure to one strict-mono
subsequence that converges almost surely at every nonnegative rational time. -/
theorem existsStrictMonoSubsequence_tendstoAeOnNNRat_partitionItoApproximation
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    {I : NNReal → Ω → ℝ} (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hApprox :
      ∀ T : NNReal,
        TendstoInMeasure μ
          (fun n ω ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              T
              n)
          atTop
          (I T)) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ q : ℚ≥0,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (q : NNReal)
                (φ n))
            atTop
            (𝓝 (I q ω)) := by
  -- Proof comment: the restored file now delegates the countable diagonal step to the existing
  -- encodable-family subsequence theorem from Remark 21.71.
  let f : ℚ≥0 → ℕ → Ω → ℝ := fun q n ω ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (q : NNReal)
      n
  let g : ℚ≥0 → Ω → ℝ := fun q ω ↦ I q ω
  have hfg : ∀ q : ℚ≥0, TendstoInMeasure μ (f q) atTop (g q) := by
    intro q
    simpa [f, g] using hApprox (q : NNReal)
  rcases existsStrictMonoSubsequence_tendstoAeOnEncodableFamily f g hfg with
    ⟨⟨φ, hφ⟩, hφae⟩
  exact ⟨φ, hφ, by simpa [f, g] using hφae⟩

/-- Helper for Exercise 25.2.1(ii): convergence at `atTop` follows once every strict-mono
subsequence admits a further strict-mono refinement converging to the same limit. -/
private theorem tendsto_of_refinedRowMapCriterion_local
    {α : Type*} [TopologicalSpace α] {u : ℕ → α} {a : α}
    (hRefine :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun n ↦ u (φ (ψ n))) atTop (𝓝 a)) :
    Tendsto u atTop (𝓝 a) := by
  -- Proof comment: use the standard subsequence criterion after replacing an arbitrary
  -- `atTop`-tending row map by a strict-mono extraction.
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ, hlim⟩ := hRefine (ns ∘ φ) hnsφ
  refine ⟨φ ∘ ψ, ?_⟩
  -- Proof comment: the extracted refinement `φ ∘ ψ` is exactly the subsequence required by
  -- `tendsto_of_subseq_tendsto`.
  simpa [Function.comp] using hlim

/-- Helper for Exercise 25.2.1: along any strict-mono row family, the predecessor horizon tends to
the target horizon because the partition mesh tends to zero. -/
lemma partitionPredecessorPointEarly_tendsto_alongStrictMonoRows
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hmesh
      (fun n ↦ bot_le)
      ?_
  intro n
  -- Proof comment: the predecessor point always sits within one mesh width of the target
  -- horizon, so shrinking mesh forces the predecessor horizon to converge to `T`.
  simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P (φ n) T

/-- Helper for Exercise 25.2.1(i): if a random stop `β ω` lies strictly before the target time
`t`, then along every strict-mono row family the predecessor point is eventually already beyond
that stop. -/
private lemma eventually_lt_partitionPredecessorPointEarly_of_lt
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {β : Ω → ENNReal} {ω : Ω} {t : NNReal}
    (hβt : β ω < (t : ENNReal)) :
    ∀ᶠ n in atTop, β ω < (partitionPredecessorPointEarly P (φ n) t : ENNReal) := by
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) t) atTop (𝓝 t) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows P hφ t
  have hβfin : β ω < ∞ := lt_of_lt_of_le hβt (by simp)
  have hβnn : (β ω).toNNReal < t := by
    exact ENNReal.toNNReal_lt_of_lt_coe hβt
  have hEventually :
      ∀ᶠ n in atTop, (β ω).toNNReal < partitionPredecessorPointEarly P (φ n) t :=
    hpred (Ioi_mem_nhds hβnn)
  filter_upwards [hEventually] with n hn
  have hβeq : (((β ω).toNNReal : NNReal) : ENNReal) = β ω := by
    exact ENNReal.coe_toNNReal hβfin.ne
  rw [← hβeq]
  exact_mod_cast hn

/-- Helper for Exercise 25.2.1(i): before the stopping time, `processBeforeStoppingTime` returns
the original process value. -/
private lemma processBeforeStoppingTime_apply_eq_self_of_le
    {H : NNReal → Ω → ℝ} {β : Ω → ENNReal} {t : NNReal} {ω : Ω}
    (htβ : (t : ENNReal) ≤ β ω) :
    processBeforeStoppingTime H β t ω = H t ω := by
  -- Proof comment: on the active branch of the stopping indicator, the stopped process is
  -- definitionally the original process.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htβ]

/-- Helper for Exercise 25.2.1(i): after the stopping time, `processBeforeStoppingTime` vanishes.
-/
private lemma processBeforeStoppingTime_apply_eq_zero_of_lt
    {H : NNReal → Ω → ℝ} {β : Ω → ENNReal} {t : NNReal} {ω : Ω}
    (hβt : β ω < (t : ENNReal)) :
    processBeforeStoppingTime H β t ω = 0 := by
  have htβ : ¬ (t : ENNReal) ≤ β ω := not_le_of_gt hβt
  -- Proof comment: once the sampled time is strictly after the stopping time, the stopped
  -- process takes its zero branch.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htβ]

/-- Helper for Exercise 25.2.1: along any strict-mono row family, the predecessor horizon tends to
the target horizon, so continuity of the canonical Itô integral transfers to predecessor times.
-/
theorem canonicalItoIntegral_predecessorPoint_tendsto_of_continuous
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (H : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (T : NNReal) :
    Tendsto
      (fun n ↦
        continuousLocalMartingaleItoIntegralProcess hM H
          (partitionPredecessorPointEarly P (φ n) T) ω)
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows P hφ T
  -- Proof comment: continuity of the canonical Itô path upgrades the predecessor-time convergence
  -- to convergence of the canonical values.
  simpa using hωCont.continuousAt.tendsto.comp hpred

/-- Helper for Exercise 25.2.1: the last boundary increment disappears along a strict-mono row
subsequence when the coefficient path is continuous. -/
theorem partitionItoBoundaryTerm_tendsto_zero_alongSubsequence
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω) (T : NNReal) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) ω *
          (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω))
      atTop
      (𝓝 0) := by
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows P hφ T
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 (H T ω)) :=
    hHωCont.continuousAt.tendsto.comp hpred
  have hPath :
      Tendsto
        (fun n ↦ M (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hpred
  have hIncrement :
      Tendsto
        (fun n ↦ M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ M T ω) atTop (𝓝 (M T ω)) :=
      tendsto_const_nhds
    have hSub :
        Tendsto
          (fun n ↦ M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω)
          atTop
          (𝓝 (M T ω - M T ω)) :=
      hConst.sub hPath
    simpa using hSub
  -- Proof comment: one factor converges to `H_T(ω)` and the boundary increment converges to `0`,
  -- so their product vanishes.
  simpa using hCoeff.mul hIncrement

/-- Helper for Exercise 25.2.1(ii): the target-horizon partition sum splits into the shorter
predecessor-horizon sum plus the single boundary increment on the last cell. -/
lemma partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {ω : Ω} {n : ℕ} {T : NNReal} :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        T
        n
      =
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        (partitionPredecessorPointEarly P n T)
        n
      +
        H (partitionPredecessorPointEarly P n T) ω *
          (M T ω - M (partitionPredecessorPointEarly P n T) ω) := by
  let X : PathSpace := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0 : T ≤ 0 := by
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
      exact le_antisymm hle0 bot_le
    -- Proof comment: when the truncation index is `0`, both sums are empty and the boundary
    -- increment vanishes because the horizon and predecessor point are both `0`.
    subst hT0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hpred : partitionPredecessorPointEarly P n T = P n k := by
      -- Proof comment: for a positive truncation index, the predecessor point is the last left
      -- endpoint before `T`.
      simp [partitionPredecessorPointEarly, hk]
    have hpredIdx :
        partitionBoundIndex P n (partitionPredecessorPointEarly P n T) = k := by
      -- Proof comment: the predecessor horizon is itself the partition point `P n k`.
      rw [hpred, partitionBoundIndex_eq_of_partitionPoint]
    have hnext :
        partitionNextPointUpTo P n k T = T := by
      -- Proof comment: at the final contributing index, the clipped successor reaches the target
      -- horizon.
      rw [partitionNextPointUpTo, min_eq_right]
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hprefix :
        ∑ x ∈ Finset.range k,
            H (P n x) ω * (M (partitionNextPointUpTo P n x T) ω - M (P n x) ω) =
          ∑ x ∈ Finset.range k,
            H (P n x) ω * (M (partitionNextPointUpTo P n x (P n k)) ω - M (P n x) ω) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ltT : j + 1 < partitionBoundIndex P n T := by
        simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hnextT : partitionNextPointUpTo P n j T = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_ltT)
      have hnextPred : partitionNextPointUpTo P n j (P n k) = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact
          ((IsAdmissiblePartitionSequence.strictMono (P := P) n).monotone)
            (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      rw [hnextT, hnextPred]
    calc
      partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          X
          P
          T
          n
          =
        ∑ x ∈ Finset.range k,
          H (P n x) ω * (M (partitionNextPointUpTo P n x T) ω - M (P n x) ω) +
            H (P n k) ω * (M T ω - M (P n k) ω) := by
              rw [partitionPathwiseItoApproximationUpTo, hk, Finset.sum_range_succ, hnext]
              simp [X]
      _ =
        ∑ x ∈ Finset.range k,
          H (P n x) ω * (M (partitionNextPointUpTo P n x (P n k)) ω - M (P n x) ω) +
            H (P n k) ω * (M T ω - M (P n k) ω) := by
              rw [hprefix]
      _ =
        partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            X
            P
            (partitionPredecessorPointEarly P n T)
            n +
          H (partitionPredecessorPointEarly P n T) ω * (M T ω - M (partitionPredecessorPointEarly P n T) ω) := by
              rw [partitionPathwiseItoApproximationUpTo, hpredIdx, hpred]
              simp [X]

/-- Helper for Exercise 25.2.1(ii): if two horizons lie in the same cell of one partition row,
then the corresponding partition sums differ only by the final boundary increment. -/
lemma partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {ω : Ω} {n : ℕ} {S T : NNReal} (hST : S ≤ T)
    (hSame : partitionBoundIndex P n S = partitionBoundIndex P n T) :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        T
        n
      =
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        S
        n
      +
        H (partitionPredecessorPointEarly P n T) ω *
          (M T ω - M S ω) := by
  let X : PathSpace := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  let m := partitionBoundIndex P n T
  have hmS : partitionBoundIndex P n S = m := by
    -- Proof comment: the same-cell hypothesis identifies both truncation indices with the same
    -- final contributing index.
    simpa [m] using hSame
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hS0 : S = 0 := by
      exact le_antisymm (le_trans hST (by simpa [hT0])) bot_le
    have hmT : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    have hmS0 : partitionBoundIndex P n S = 0 := by
      simpa [hm] using hmS
    -- Proof comment: when the common truncation index is `0`, both sums are empty and the
    -- boundary increment vanishes because `S = T = 0`.
    subst hT0
    subst hS0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hmT : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hmS' : partitionBoundIndex P n S = k.succ := by
      exact hmS.trans hk
    have hprefix :
        Finset.sum (Finset.range k) (fun j ↦
            H (P n j) ω * (X (partitionNextPointUpTo P n j T) - X (P n j))) =
          Finset.sum (Finset.range k) (fun j ↦
            H (P n j) ω * (X (partitionNextPointUpTo P n j S) - X (P n j))) := by
      -- Proof comment: before the common last contributing index, both truncated successors are
      -- the genuine next partition point, so the prefix sums agree termwise.
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ltT : j + 1 < partitionBoundIndex P n T := by
        simpa [hmT] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hj_ltS : j + 1 < partitionBoundIndex P n S := by
        simpa [hmS'] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hnextT : partitionNextPointUpTo P n j T = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_ltT)
      have hnextS : partitionNextPointUpTo P n j S = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) S hj_ltS)
      rw [hnextT, hnextS]
    have hlastT :
        H (P n k) ω * (X (partitionNextPointUpTo P n k T) - X (P n k)) =
          H (P n k) ω * (X T - X (P n k)) := by
      -- Proof comment: at the last contributing index, the clipped successor equals the target
      -- horizon `T`.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [hmT] using le_partitionBoundIndex_time P n T
      rw [hnext]
    have hlastS :
        H (P n k) ω * (X (partitionNextPointUpTo P n k S) - X (P n k)) =
          H (P n k) ω * (X S - X (P n k)) := by
      -- Proof comment: the same argument identifies the last clipped successor on the shorter
      -- horizon with `S`.
      have hnext : partitionNextPointUpTo P n k S = S := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [hmS'] using le_partitionBoundIndex_time P n S
      rw [hnext]
    have hpredT : partitionPredecessorPointEarly P n T = P n k := by
      -- Proof comment: the shared predecessor point is exactly the last left endpoint.
      simp [partitionPredecessorPointEarly, hmT]
    rw [partitionPathwiseItoApproximationUpTo, hmT, Finset.sum_range_succ]
    rw [partitionPathwiseItoApproximationUpTo, hmS', Finset.sum_range_succ]
    rw [hprefix, hlastT, hlastS, hpredT]
    simp [X]
    ring

/-- Helper for Exercise 25.2.1(ii): if a horizon `S` lies strictly after `P n k` but not beyond
`P n (k + 1)`, then `S` has truncation index `k + 1` in the `n`-th partition row. -/
lemma partitionBoundIndex_eq_succ_of_lt_of_le
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) {S : NNReal} (hkS : P n k < S) (hSsucc : S ≤ P n (k + 1)) :
    partitionBoundIndex P n S = k + 1 := by
  apply Nat.le_antisymm
  · -- Proof comment: `k + 1` already reaches the horizon, so minimality bounds the truncation
    -- index from above.
    simpa [partitionBoundIndex] using
      (Nat.find_min' (exists_partition_index_le_time P n S) hSsucc)
  · -- Proof comment: the left endpoint `P n k` lies strictly before `S`, so the truncation index
    -- must lie beyond `k`.
    exact Nat.succ_le_of_lt (lt_partitionBoundIndex_of_partitionPoint_lt_time P n k S hkS)

/-- Helper for Exercise 25.2.1(ii): every positive horizon contains a nonnegative rational point
in the same partition cell of a fixed row. -/
lemma existsSameCellNNRatPoint
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) {T : NNReal} (hT : 0 < T) :
    ∃ q : ℚ≥0,
      partitionBoundIndex P n (q : NNReal) = partitionBoundIndex P n T ∧
        (q : NNReal) < T := by
  have hidx_ne_zero : partitionBoundIndex P n T ≠ 0 := by
    intro hzero
    have hT_le_zero : T ≤ 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hzero] using le_partitionBoundIndex_time P n T
      simpa [hP.zero_eq n] using hle
    exact (not_lt_of_ge hT_le_zero) hT
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hidx_ne_zero
  have hk_lt : k < partitionBoundIndex P n T := by
    simpa [hk] using Nat.lt_succ_self k
  have hk_time : P n k < T :=
    partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk_lt
  have hT_next : T ≤ P n (k + 1) := by
    simpa [hk] using le_partitionBoundIndex_time P n T
  have hk_real : ((P n k : NNReal) : ℝ) < (T : ℝ) := by
    exact_mod_cast hk_time
  obtain ⟨q, hq_left, hq_right⟩ := exists_rat_btwn hk_real
  have hq_nonneg : 0 ≤ q := by
    have hPk_nonneg : 0 ≤ ((P n k : NNReal) : ℝ) := by positivity
    have hq_nonneg_real : (0 : ℝ) ≤ q := le_trans hPk_nonneg (le_of_lt hq_left)
    exact_mod_cast hq_nonneg_real
  let qNN : ℚ≥0 := ⟨q, hq_nonneg⟩
  have hq_gt : P n k < (qNN : NNReal) := by
    exact_mod_cast hq_left
  have hq_lt : (qNN : NNReal) < T := by
    exact_mod_cast hq_right
  have hq_idx :
      partitionBoundIndex P n (qNN : NNReal) = k + 1 :=
    partitionBoundIndex_eq_succ_of_lt_of_le P n k hq_gt (le_trans (le_of_lt hq_lt) hT_next)
  refine ⟨qNN, ?_, hq_lt⟩
  rw [hq_idx, hk]

/-- Helper for Exercise 25.2.1(ii): along a strict-mono family of partition rows and a positive
horizon `T`, one can choose row-dependent rational points that stay in the same cell as `T` and
still converge to `T`. -/
lemma existsSameCellApproximationDataAlongStrictMonoRows
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {T : NNReal} (hT : 0 < T) :
    ∃ q : ℕ → ℚ≥0,
      (∀ n : ℕ,
        partitionBoundIndex P (φ n) (q n : NNReal) = partitionBoundIndex P (φ n) T) ∧
      (∀ n : ℕ, (q n : NNReal) < T) ∧
      Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T) := by
  classical
  choose q hqSame hqLt using
    fun n ↦ existsSameCellNNRatPoint P (φ n) hT
  refine ⟨q, hqSame, hqLt, ?_⟩
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (by simpa using hmesh.add hmesh)
      (fun n ↦ bot_le)
      ?_
  intro n
  let row := φ n
  have hidx_ne_zero : partitionBoundIndex P row T ≠ 0 := by
    intro hzero
    have hT_le_zero : T ≤ 0 := by
      have hle : T ≤ P row 0 := by
        simpa [hzero] using le_partitionBoundIndex_time P row T
      simpa [hP.zero_eq row] using hle
    exact (not_lt_of_ge hT_le_zero) hT
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hidx_ne_zero
  have hqIdx : partitionBoundIndex P row (q n : NNReal) = k + 1 := by
    rw [hqSame n, hk]
  have hpredEq :
      partitionPredecessorPointEarly P row (q n : NNReal) =
        partitionPredecessorPointEarly P row T := by
    -- Proof comment: same-cell points share the same predecessor endpoint in the chosen row.
    simp [partitionPredecessorPointEarly, hk, hqIdx]
  have hqMesh :
      edist (partitionPredecessorPointEarly P row (q n : NNReal)) (q n : NNReal) ≤
        partitionMesh P row := by
    simpa [edist_comm] using
      partitionPredecessorPointWithinMeshEarly P row (q n : NNReal)
  have hTMesh :
      edist (partitionPredecessorPointEarly P row T) T ≤ partitionMesh P row :=
    partitionPredecessorPointWithinMeshEarly P row T
  calc
    edist ((q n : NNReal)) T
        ≤ edist ((q n : NNReal)) (partitionPredecessorPointEarly P row (q n : NNReal)) +
            edist (partitionPredecessorPointEarly P row (q n : NNReal)) T := by
              exact edist_triangle _ _ _
    _ = edist (partitionPredecessorPointEarly P row (q n : NNReal)) (q n : NNReal) +
          edist (partitionPredecessorPointEarly P row T) T := by
            rw [edist_comm, hpredEq]
    _ ≤ partitionMesh P row + partitionMesh P row := add_le_add hqMesh hTMesh

/-- Helper for Exercise 25.2.1(ii): along a strict-mono family of partition rows, positive moving
target times that converge to `T` admit same-cell rational selectors converging to the same
limit. -/
lemma existsSameCellApproximationDataAlongConvergentRowPoints
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ)
    {τ : ℕ → NNReal} {T : NNReal}
    (hτPos : ∀ n : ℕ, 0 < τ n)
    (hτT : Tendsto τ atTop (𝓝 T)) :
    ∃ q : ℕ → ℚ≥0,
      (∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n)) ∧
      (∀ n : ℕ, (q n : NNReal) < τ n) ∧
      Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T) := by
  classical
  choose q hqSame hqLt using fun n ↦ existsSameCellNNRatPoint P (χ n) (hτPos n)
  refine ⟨q, hqSame, hqLt, ?_⟩
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (χ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hχ.tendsto_atTop
  have hClose :
      Tendsto (fun n ↦ edist ((q n : NNReal)) (τ n)) atTop (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa using hmesh.add hmesh)
        (fun n ↦ bot_le)
        ?_
    intro n
    let row := χ n
    have hidx_ne_zero : partitionBoundIndex P row (τ n) ≠ 0 := by
      intro hzero
      have hτ_le_zero : τ n ≤ 0 := by
        have hle : τ n ≤ P row 0 := by
          simpa [hzero] using le_partitionBoundIndex_time P row (τ n)
        simpa [hP.zero_eq row] using hle
      exact (not_lt_of_ge hτ_le_zero) (hτPos n)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hidx_ne_zero
    have hqIdx : partitionBoundIndex P row (q n : NNReal) = k + 1 := by
      rw [hqSame n, hk]
    have hpredEq :
        partitionPredecessorPointEarly P row (q n : NNReal) =
          partitionPredecessorPointEarly P row (τ n) := by
      -- Proof comment: points in the same partition cell share the same predecessor endpoint.
      simp [partitionPredecessorPointEarly, hk, hqIdx]
    have hqMesh :
        edist (partitionPredecessorPointEarly P row (q n : NNReal)) (q n : NNReal) ≤
          partitionMesh P row := by
      simpa [edist_comm] using
        partitionPredecessorPointWithinMeshEarly P row (q n : NNReal)
    have hτMesh :
        edist (partitionPredecessorPointEarly P row (τ n)) (τ n) ≤ partitionMesh P row :=
      partitionPredecessorPointWithinMeshEarly P row (τ n)
    calc
      edist ((q n : NNReal)) (τ n)
          ≤ edist ((q n : NNReal)) (partitionPredecessorPointEarly P row (q n : NNReal)) +
              edist (partitionPredecessorPointEarly P row (q n : NNReal)) (τ n) := by
                exact edist_triangle _ _ _
      _ = edist (partitionPredecessorPointEarly P row (q n : NNReal)) (q n : NNReal) +
            edist (partitionPredecessorPointEarly P row (τ n)) (τ n) := by
              rw [edist_comm, hpredEq]
      _ ≤ partitionMesh P row + partitionMesh P row := add_le_add hqMesh hτMesh
  rw [tendsto_iff_edist_tendsto_0] at hτT ⊢
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (by simpa using hClose.add hτT)
      (fun n ↦ bot_le)
      ?_
  intro n
  exact edist_triangle _ _ _

/-- Helper for Exercise 25.2.1: the canonical dyadic Itô realization starts from `0`. -/
lemma continuousLocalMartingaleItoIntegralProcess_zero
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) (ω : Ω) :
    continuousLocalMartingaleItoIntegralProcess hM H 0 ω = 0 := by
  have hdyadicZero :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            Definition2158.dyadicPartitionSequence
            0
            n)
        atTop
        (𝓝 (0 : ℝ)) := by
    simpa [partitionPathwiseItoApproximationUpTo, partitionBoundIndex_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  -- Proof comment: the canonical process is defined by the dyadic row limit, and every row sum
  -- at horizon `0` is empty.
  simpa [continuousLocalMartingaleItoIntegralProcess] using hdyadicZero.limUnder_eq

/-- Helper for Exercise 25.2.1(ii): the compact-horizon maximal row-point error of one partition
row against the canonical Itô path. -/
noncomputable def rowPointMaxErrorUpTo
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (H : NNReal → Ω → ℝ)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R : NNReal) (row : ℕ) (ω : Ω) : ℝ :=
  ↑((Finset.range (partitionBoundIndex P row R)).sup fun k ↦
    ‖partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        (P row k)
        row -
      continuousLocalMartingaleItoIntegralProcess hM H (P row k) ω‖₊)

/-- Helper for Exercise 25.2.1(ii): enlarging the compact horizon can only enlarge the finite
row-point supremum. -/
private lemma rowPointMaxErrorUpTo_le_of_le
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {R S : NNReal} (hRS : R ≤ S) (row : ℕ) (ω : Ω) :
    rowPointMaxErrorUpTo hM H P R row ω ≤
      rowPointMaxErrorUpTo hM H P S row ω := by
  dsimp [rowPointMaxErrorUpTo]
  exact_mod_cast
    (Finset.sup_le fun k hk ↦
      Finset.le_sup <|
        Finset.mem_range.mpr <|
          lt_of_lt_of_le
            (Finset.mem_range.mp hk)
            (partitionBoundIndex_monotone P row hRS))

/-- Helper for Exercise 25.2.1(ii): if the predecessor point of `T` lies below the compact
horizon `R`, its row error is controlled by the maximal row-point error up to `R`. -/
lemma predecessorPointError_le_rowPointMaxErrorUpTo
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {T R : NNReal} (hTR : T ≤ R) (row : ℕ) (ω : Ω) :
    |partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        (partitionPredecessorPointEarly P row T)
        row -
      continuousLocalMartingaleItoIntegralProcess hM H
        (partitionPredecessorPointEarly P row T) ω| ≤
      rowPointMaxErrorUpTo hM H P R row ω := by
  by_cases hT0 : T = 0
  · subst hT0
    -- Proof comment: at horizon `0`, both the predecessor sum and the canonical Itô value are
    -- `0`, so the bound is immediate.
    simp [rowPointMaxErrorUpTo, partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) row,
      continuousLocalMartingaleItoIntegralProcess_zero]
  · have hT : 0 < T := bot_lt_iff_ne_bot.mpr hT0
    have hidx_ne_zero : partitionBoundIndex P row T ≠ 0 := by
      intro hzero
      have hT_le_zero : T ≤ 0 := by
        have hle : T ≤ P row 0 := by
          simpa [hzero] using le_partitionBoundIndex_time P row T
        simpa [hP.zero_eq row] using hle
      exact (not_lt_of_ge hT_le_zero) hT
    obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P row T = k + 1 :=
      ⟨partitionBoundIndex P row T - 1, (Nat.sub_add_cancel (Nat.pos_of_ne_zero hidx_ne_zero)).symm⟩
    have hk_lt_T : k < partitionBoundIndex P row T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hk_lt_R : k < partitionBoundIndex P row R := by
      exact lt_of_lt_of_le hk_lt_T (partitionBoundIndex_monotone P row hTR)
    have hpred : partitionPredecessorPointEarly P row T = P row k := by
      simp [partitionPredecessorPointEarly, hk]
    have hSup :
        ‖partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (P row k)
            row -
          continuousLocalMartingaleItoIntegralProcess hM H (P row k) ω‖₊ ≤
          (Finset.range (partitionBoundIndex P row R)).sup fun j ↦
            ‖partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (P row j)
                row -
              continuousLocalMartingaleItoIntegralProcess hM H (P row j) ω‖₊ := by
      exact
        Finset.le_sup
          (s := Finset.range (partitionBoundIndex P row R))
          (f := fun j ↦
            ‖partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (P row j)
                row -
              continuousLocalMartingaleItoIntegralProcess hM H (P row j) ω‖₊)
          (Finset.mem_range.mpr hk_lt_R)
    -- Proof comment: the predecessor horizon is itself one of the row points appearing in the
    -- compact-horizon supremum.
    have hSupReal :
        (‖partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (P row k)
              row -
            continuousLocalMartingaleItoIntegralProcess hM H (P row k) ω‖₊ : ℝ) ≤
          ↑((Finset.range (partitionBoundIndex P row R)).sup fun j ↦
            ‖partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (P row j)
                row -
              continuousLocalMartingaleItoIntegralProcess hM H (P row j) ω‖₊) := by
      exact_mod_cast hSup
    rw [hpred]
    simpa [rowPointMaxErrorUpTo, Real.norm_eq_abs] using hSupReal

/-- Helper for Exercise 25.2.1(ii): compact-horizon row-point control implies convergence of the
predecessor-horizon partition sums to the canonical Itô path at every fixed horizon. -/
lemma predecessorApproximation_tendsto_of_rowPointMax
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hMax :
      ∀ N : ℕ,
        Tendsto (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ n) ω) atTop (𝓝 0))
    (T : NNReal) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (partitionPredecessorPointEarly P (φ n) T)
          (φ n))
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  by_cases hT0 : T = 0
  · subst hT0
    -- Proof comment: the predecessor horizon of `0` is constantly `0`, so the row sums and the
    -- target canonical value are both constant.
    have hzero :
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P (φ n) 0)
            (φ n)) =
          fun _ : ℕ ↦ (0 : ℝ) := by
      funext n
      simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
        partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) (φ n)]
    rw [hzero]
    simpa [continuousLocalMartingaleItoIntegralProcess_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  · have hT : 0 < T := bot_lt_iff_ne_bot.mpr hT0
    rcases exists_nat_gt (T : ℝ) with ⟨N, hN⟩
    have hT_le : T ≤ (N + 1 : NNReal) := by
      have hT_lt_N : T < (N : NNReal) := by
        exact_mod_cast hN
      exact le_of_lt (lt_of_lt_of_le hT_lt_N (by exact_mod_cast Nat.le_succ N))
    let predecessorSums : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        (partitionPredecessorPointEarly P (φ n) T)
        (φ n)
    let predecessorTargets : ℕ → ℝ := fun n ↦
      continuousLocalMartingaleItoIntegralProcess hM H
        (partitionPredecessorPointEarly P (φ n) T) ω
    have hErrAbs :
        ∀ n : ℕ,
          |predecessorSums n - predecessorTargets n| ≤
            rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ n) ω := by
      intro n
      dsimp [predecessorSums, predecessorTargets]
      exact
        predecessorPointError_le_rowPointMaxErrorUpTo
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hT_le (φ n) ω
    have hUpper :
        Tendsto
          (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ n) ω)
          atTop
          (𝓝 0) :=
      hMax N
    have hLower :
        Tendsto
          (fun n ↦ -rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ n) ω)
          atTop
          (𝓝 0) := by
      simpa using hUpper.neg
    have hErr :
        Tendsto (fun n ↦ predecessorSums n - predecessorTargets n) atTop (𝓝 0) := by
      refine
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          hLower hUpper ?_ ?_
      · intro n
        exact (abs_le.mp (hErrAbs n)).1
      · intro n
        exact (abs_le.mp (hErrAbs n)).2
    have hTargets :
        Tendsto predecessorTargets atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      canonicalItoIntegral_predecessorPoint_tendsto_of_continuous
        (μ := μ) (ℱ := ℱ) (M := M) hM H P hφ hωCont T
    have hSum :
        Tendsto
          (fun n ↦ (predecessorSums n - predecessorTargets n) + predecessorTargets n)
          atTop
          (𝓝 (0 + continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      hErr.add hTargets
    -- Proof comment: the row-point error goes to `0`, while continuity transports the canonical
    -- predecessor values to the target horizon.
    simpa [predecessorSums, predecessorTargets, sub_add_cancel] using hSum

/-- Helper for Exercise 25.2.1(ii): continuity of the canonical Itô path transports a convergent
horizon selector to convergence of the canonical values. -/
lemma canonicalItoIntegral_selector_tendsto_of_continuous
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    {ω : Ω}
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    {T : NNReal} {τ : ℕ → NNReal}
    (hτ : Tendsto τ atTop (𝓝 T)) :
    Tendsto
      (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  -- Proof comment: evaluate the continuous canonical path along the convergent selector `τ`.
  simpa using hωCont.continuousAt.tendsto.comp hτ

/-- Helper for Exercise 25.2.1(ii): if every strict-mono subsequence admits a further refinement
along which the error `a_n - b_n` tends to `0`, then convergence of `b_n` to `L` forces
convergence of `a_n` to the same target. -/
private lemma tendsto_of_refinedErrorToTarget
    {a b : ℕ → ℝ} {L : ℝ}
    (hb : Tendsto b atTop (𝓝 L))
    (hRefine :
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
          Tendsto (fun n ↦ a (ψ (ρ n)) - b (ψ (ρ n))) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 L) := by
  refine tendsto_of_refinedRowMapCriterion_local ?_
  intro ψ hψ
  obtain ⟨ρ, hρ, hErr⟩ := hRefine ψ hψ
  refine ⟨ρ, hρ, ?_⟩
  have hbRef :
      Tendsto (fun n ↦ b (ψ (ρ n))) atTop (𝓝 L) :=
    hb.comp ((hψ.comp hρ).tendsto_atTop)
  have hSum :
      Tendsto
        (fun n ↦ (a (ψ (ρ n)) - b (ψ (ρ n))) + b (ψ (ρ n)))
        atTop
        (𝓝 (0 + L)) :=
    hErr.add hbRef
  -- Proof comment: after refining, the sequence `a` is the sum of a vanishing error and the
  -- already convergent target sequence `b`.
  simpa [sub_add_cancel] using hSum

/-- Helper for Exercise 25.2.1(ii): if the selected horizons converge to `T`, then the same-cell
boundary increment against the continuous path `M` disappears. -/
lemma partitionItoSelectorBoundaryTerm_tendsto_zero
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    {T : NNReal} {q : ℕ → ℚ≥0}
    (hq : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T)) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) ω *
          (M T ω - M (q n : NNReal) ω))
      atTop
      (𝓝 0) := by
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T) ω)
        atTop
        (𝓝 (H T ω)) := by
    -- Proof comment: the coefficient is sampled at predecessor points that converge to `T`.
    exact
      hHωCont.continuousAt.tendsto.comp
        (partitionPredecessorPointEarly_tendsto_alongStrictMonoRows P hφ T)
  have hPath :
      Tendsto
        (fun n ↦ M (q n : NNReal) ω)
        atTop
        (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hq
  have hIncrement :
      Tendsto
        (fun n ↦ M T ω - M (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ M T ω) atTop (𝓝 (M T ω)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of `M` at the selected horizons forces the boundary increment to
    -- vanish.
    simpa using hConst.sub hPath
  -- Proof comment: the coefficient tends to `H T ω` while the boundary increment tends to `0`,
  -- so the product disappears.
  simpa using hCoeff.mul hIncrement

/-- Helper for Exercise 25.2.1(ii): once the predecessor-horizon partition sums converge to the
target canonical value, adding the vanishing boundary increment recovers the target-horizon
convergence. -/
theorem pathwiseTargetFromPredecessorApproximation
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω) {T : NNReal}
    (hPred :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P (φ n) T)
            (φ n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω))) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          (φ n))
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  have hBoundary :
      Tendsto
        (fun n ↦
          H (partitionPredecessorPointEarly P (φ n) T) ω *
            (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω))
        atTop
        (𝓝 0) :=
    partitionItoBoundaryTerm_tendsto_zero_alongSubsequence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hφ hHωCont T
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          (φ n)) =
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P (φ n) T)
            (φ n) +
              H (partitionPredecessorPointEarly P (φ n) T) ω *
                (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω)) := by
    funext n
    -- Proof comment: each target-horizon row sum is exactly the predecessor-horizon row sum plus
    -- the last-cell boundary increment from the preceding lemma.
    exact
      partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
  have hSum :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P (φ n) T)
            (φ n) +
              H (partitionPredecessorPointEarly P (φ n) T) ω *
                (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω + 0)) :=
    hPred.add hBoundary
  have hSum' :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P (φ n) T)
            (φ n) +
              H (partitionPredecessorPointEarly P (φ n) T) ω *
                (M T ω - M (partitionPredecessorPointEarly P (φ n) T) ω))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    simpa using hSum
  rw [hEq]
  exact hSum'

/-- Helper for Exercise 25.2.1(ii): two continuous modifications on `NNReal` agree almost surely
at every deterministic time outside one common null set. -/
lemma aeAllEq_of_modifications_of_aeContinuous
    {X Y : NNReal → Ω → ℝ}
    (hXY : AreModifications μ X Y)
    (hXcont : HasAlmostSurelyContinuousPaths μ X)
    (hYcont : HasAlmostSurelyContinuousPaths μ Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω := by
  let toIci : Set.Ici (0 : ℝ) → NNReal := fun t ↦
    ⟨t.1.toNNReal, by simpa using t.2⟩
  let Xreal : Set.Ici (0 : ℝ) → Ω → ℝ := fun t ω ↦ X (toIci t) ω
  let Yreal : Set.Ici (0 : ℝ) → Ω → ℝ := fun t ω ↦ Y (toIci t) ω
  have hXYreal : AreModifications μ Xreal Yreal := by
    -- Proof comment: the modification relation is preserved by the standard reparameterization of
    -- `NNReal` as `Set.Ici (0 : ℝ)`.
    intro t
    exact hXY (toIci t)
  have hXrc :
      ∀ᵐ ω ∂μ, ∀ t : Set.Ici (0 : ℝ),
        ContinuousWithinAt (processPath Xreal ω) (Set.Ici t) t := by
    filter_upwards [hXcont] with ω hω t
    have hcont : Continuous fun s : Set.Ici (0 : ℝ) ↦ Xreal s ω := by
      -- Proof comment: restricting the continuous `NNReal` path along the canonical
      -- `Set.Ici (0 : ℝ)` parameterization preserves continuity.
      have hbase :
          Continuous fun s : Set.Ici (0 : ℝ) ↦ processPath X ω (Real.toNNReal s.1) := by
        exact hω.comp (continuous_real_toNNReal.comp continuous_subtype_val)
      simpa [processPath, Xreal, toIci] using hbase
    simpa [processPath] using hcont.continuousWithinAt
  have hYrc :
      ∀ᵐ ω ∂μ, ∀ t : Set.Ici (0 : ℝ),
        ContinuousWithinAt (processPath Yreal ω) (Set.Ici t) t := by
    filter_upwards [hYcont] with ω hω t
    have hcont : Continuous fun s : Set.Ici (0 : ℝ) ↦ Yreal s ω := by
      -- Proof comment: the same interval reparameterization works for the second modification.
      have hbase :
          Continuous fun s : Set.Ici (0 : ℝ) ↦ processPath Y ω (Real.toNNReal s.1) := by
        exact hω.comp (continuous_real_toNNReal.comp continuous_subtype_val)
      simpa [processPath, Yreal, toIci] using hbase
    simpa [processPath] using hcont.continuousWithinAt
  rcases
      ProbabilityTheory.indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
        μ Xreal Yreal hXYreal Set.ordConnected_Ici hXrc hYrc with
    ⟨N, hNmeas, hNnull, hNsub⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
    exact compl_mem_ae_iff.mpr hNnull
  filter_upwards [hNae] with ω hω t
  let tReal : Set.Ici (0 : ℝ) := ⟨(t : ℝ), by exact_mod_cast t.2⟩
  have htEq : Xreal tReal ω = Yreal tReal ω := by
    -- Proof comment: outside the common null set, the reparameterized processes coincide at every
    -- deterministic time, so translating back to `NNReal` gives the desired equality.
    by_contra hneq
    exact hω ((hNsub tReal) hneq)
  simpa [Xreal, Yreal, toIci, tReal, Real.toNNReal_coe] using htEq

/-- Helper for Exercise 25.2.1(ii): continuity on every integer interval `[0, N + 1]` upgrades
to continuity on all of `NNReal`. -/
private lemma continuous_of_continuousOnIntegerIntervals
    {β : Type*} [TopologicalSpace β] {f : NNReal → β}
    (hcont : ∀ N : ℕ, ContinuousOn f (Set.Icc (0 : NNReal) (N + 1 : NNReal))) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  by_cases ht0 : t = 0
  · subst ht0
    have hmem : Set.Icc (0 : NNReal) ((0 : ℕ) + 1 : NNReal) ∈ 𝓝 (0 : NNReal) := by
      refine mem_of_superset (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)) ?_
      intro x hx
      have hx' : x < ((0 : ℕ) + 1 : NNReal) := by
        simpa using hx
      exact Set.mem_Icc.mpr ⟨zero_le x, le_of_lt hx'⟩
    -- Proof comment: around `0`, the first compact interval already provides a neighborhood on
    -- which the continuity witness is available.
    exact (hcont 0).continuousAt hmem
  · rcases exists_nat_gt (t : ℝ) with ⟨N, hN⟩
    have ht_lower : (0 : NNReal) < t := bot_lt_iff_ne_bot.mpr ht0
    have ht_upper_nat : t < (N : NNReal) := by
      exact_mod_cast hN
    have ht_upper : t < (N + 1 : NNReal) := by
      exact lt_of_lt_of_le ht_upper_nat (by exact_mod_cast Nat.le_succ N)
    have hmem : Set.Icc (0 : NNReal) (N + 1 : NNReal) ∈ 𝓝 t :=
      Icc_mem_nhds ht_lower ht_upper
    -- Proof comment: for positive `t`, choose an integer interval strictly containing `t` and
    -- use the interval-wise continuity witness there.
    exact (hcont N).continuousAt hmem

/-- Helper for Exercise 25.2.1: on a finite-measure time-space localization, a bounded function
lies in `L²(processMeasure μ)`, and the ambient version is the corresponding indicator. -/
private lemma memLp_indicator_of_bound_of_finiteProcessMeasure
    (A : Set (Ω × ℝ)) (hA : MeasurableSet A)
    (hA_fin : MeasureTheory.processMeasure μ A < ∞)
    {f : Ω × ℝ → ℝ}
    (hf_aesm : AEStronglyMeasurable f ((MeasureTheory.processMeasure μ).restrict A))
    {C : ℝ}
    (hbound : ∀ ⦃x : Ω × ℝ⦄, x ∈ A → |f x| ≤ C) :
    MemLp (A.indicator f) (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  letI : Fact ((MeasureTheory.processMeasure μ) A < ∞) := ⟨hA_fin⟩
  rw [memLp_indicator_iff_restrict hA]
  have hbound_restrict :
      ∀ᵐ x ∂ (MeasureTheory.processMeasure μ).restrict A, ‖f x‖ ≤ C := by
    rw [ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall fun x hx ↦ by
      simpa [Real.norm_eq_abs] using hbound hx
  -- Proof comment: after restricting to the finite localization `A`, the uniform bound gives the
  -- `L²` estimate directly, and `memLp_indicator_iff_restrict` transports it back.
  exact MemLp.of_bound hf_aesm C hbound_restrict

/-- Helper for Exercise 25.2.1: everywhere path continuity implies almost-sure path continuity. -/
private theorem hasAlmostSurelyContinuousPaths_of_continuous_local
    {X : NNReal → Ω → ℝ}
    (hX : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω) :
    HasAlmostSurelyContinuousPaths μ X := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using hX ω

/-- Helper for Exercise 25.2.1(ii): the canonical Itô realization has almost surely continuous
paths, extracted one integer horizon at a time from the canonical finite-horizon witness. -/
lemma canonicalItoIntegral_hasAeContinuousPaths
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H) :
    ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω := by
  have hCanonical :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM H) := by
    -- Proof comment: Theorem 25.22 already upgrades the canonical dyadic realization to a
    -- genuine continuous local martingale once the finite-bracket-energy hypotheses are present.
    exact
      _root_.ProbabilityTheory.canonicalItoIntegralContinuousLocalMartingale
        (ℱ := ℱ) (μ := μ) hM hbr hH_prog hFiniteEnergy.2
  -- Proof comment: a genuinely continuous process has almost surely continuous paths.
  exact hasAlmostSurelyContinuousPaths_of_continuous_local (μ := μ) hCanonical.continuous

/-- Helper for Exercise 25.2.1(i): clip a real value to the deterministic interval `[-R, R]`. -/
private def clipRealAt (R : NNReal) (x : ℝ) : ℝ :=
  max (-((R : NNReal) : ℝ)) (min ((R : NNReal) : ℝ) x)

/-- Helper for Exercise 25.2.1(i): clip the coefficient process pointwise to the deterministic
interval `[-R, R]`. -/
private def clippedProcess
    (H : NNReal → Ω → ℝ) (R : NNReal) : NNReal → Ω → ℝ :=
  fun t ω ↦ clipRealAt R (H t ω)

/-- Helper for Exercise 25.2.1(i): clipping to `[-R, R]` is uniformly bounded by `R`. -/
private lemma abs_clipRealAt_le
    (R : NNReal) (x : ℝ) :
    |clipRealAt R x| ≤ (R : ℝ) := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Proof comment: the lower clamp forces the clipped value to stay above `-R`.
    exact le_max_left _ _
  · -- Proof comment: both branches of the outer `max` lie below `R`.
    refine max_le_iff.mpr ⟨?_, ?_⟩
    · have hR_nonneg : (0 : ℝ) ≤ (R : ℝ) := by positivity
      linarith
    · exact min_le_left _ _

/-- Helper for Exercise 25.2.1(i): if a value is already inside `[-R, R]`, clipping does not
change it. -/
private lemma clipRealAt_eq_self_of_abs_le
    {R : NNReal} {x : ℝ}
    (hx : |x| ≤ (R : ℝ)) :
    clipRealAt R x = x := by
  rcases abs_le.mp hx with ⟨hxLower, hxUpper⟩
  -- Proof comment: once both one-sided bounds are available, both clamps are inactive.
  rw [clipRealAt, min_eq_right hxUpper, max_eq_right hxLower]

/-- Helper for Exercise 25.2.1(i): the clipped coefficient process is pointwise bounded by `R`.
-/
private lemma abs_clippedProcess_le
    (H : NNReal → Ω → ℝ) (R : NNReal) (t : NNReal) (ω : Ω) :
    |clippedProcess H R t ω| ≤ (R : ℝ) := by
  -- Proof comment: apply the scalar clipping bound to the value `H t ω`.
  simpa [clippedProcess] using abs_clipRealAt_le R (H t ω)

/-- Helper for Exercise 25.2.1(i): clipping preserves values that were already inside `[-R, R]`.
-/
private lemma clippedProcess_eq_self_of_abs_le
    (H : NNReal → Ω → ℝ) {R : NNReal} {t : NNReal} {ω : Ω}
    (hHt : |H t ω| ≤ (R : ℝ)) :
    clippedProcess H R t ω = H t ω := by
  -- Proof comment: evaluate the pointwise clipping identity at the chosen coefficient value.
  simpa [clippedProcess] using clipRealAt_eq_self_of_abs_le hHt

/-- Helper for Exercise 25.2.1(i): clipping preserves samplewise continuity of the coefficient
path. -/
private lemma clippedProcess_continuous
    {H : NNReal → Ω → ℝ} (R : NNReal) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω) :
    Continuous fun t : NNReal ↦ clippedProcess H R t ω := by
  -- Proof comment: clipping is built from `min` and `max` against constants, so it preserves
  -- continuity of the sample path.
  simpa [clippedProcess, clipRealAt] using
    (continuous_const.max (continuous_const.min hHωCont))

/-- Helper for Exercise 25.2.1(i): clipping preserves progressive measurability because it is a
pointwise continuous transformation of the coefficient. -/
private lemma clippedProcess_progMeasurable
    {H : NNReal → Ω → ℝ} (R : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω) :
    ProgMeasurable ℱ (clippedProcess H R) := by
  have hH_adapted : Adapted ℱ H := hH_prog.stronglyAdapted.adapted
  have hClip_adapted : Adapted ℱ (clippedProcess H R) := by
    intro t
    -- Proof comment: each time slice is obtained by composing the measurable coefficient
    -- `H t` with the scalar clipping map `x ↦ max (-R) (min R x)`.
    dsimp [clippedProcess, clipRealAt]
    exact measurable_const.max (measurable_const.min (hH_adapted t))
  -- Proof comment: once the clipped process is adapted, the preserved path continuity upgrades it
  -- back to progressive measurability.
  exact hClip_adapted.stronglyAdapted.progMeasurable_of_continuous fun ω ↦
    clippedProcess_continuous (H := H) R (hH_cont ω)

/-- Helper for Exercise 25.2.1(i): the deterministically stopped clipped process is uniformly
bounded on time-space by the clipping radius. -/
private lemma norm_processToTimeSpaceFun_clippedConstCutoff_le
    {H : NNReal → Ω → ℝ}
    (R T : NNReal) :
    ∀ x : Ω × ℝ,
      |MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal))) x| ≤
        (R : ℝ) := by
  intro x
  rcases x with ⟨ω, t⟩
  by_cases ht : ((t.toNNReal : NNReal) : ENNReal) ≤ (T : ENNReal)
  · -- Proof comment: before the deterministic cutoff, the stopped process equals the clipped
    -- process itself, so the clipping bound applies immediately.
    have ht' : t.toNNReal ≤ T := by
      exact_mod_cast ht
    simpa [Function.uncurry, MeasureTheory.processToTimeSpaceFun,
      ProbabilityTheory.processBeforeStoppingTime_apply, ht, ht'] using
      abs_clippedProcess_le (H := H) R t.toNNReal ω
  · -- Proof comment: after the deterministic cutoff, the stopped process vanishes identically.
    have ht' : ¬ t.toNNReal ≤ T := by
      intro ht'
      exact ht (by exact_mod_cast ht')
    have hR_nonneg : (0 : ℝ) ≤ R := by
      exact_mod_cast (show (0 : NNReal) ≤ R from bot_le)
    simpa [Function.uncurry, MeasureTheory.processToTimeSpaceFun,
      ProbabilityTheory.processBeforeStoppingTime_apply, ht, ht', abs_of_nonneg hR_nonneg] using
      hR_nonneg

/-- Helper for Exercise 25.2.1(i): the deterministically stopped clipped process has finite
`L²(processMeasure μ)` norm because it is progressively measurable and uniformly bounded. -/
private lemma clippedConstCutoff_memLp
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (R T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal))))
      (2 : ℝ≥0∞)
      (MeasureTheory.processMeasure μ) := by
  have hClip_prog :
      ProgMeasurable ℱ (clippedProcess H R) :=
    clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont
  let A : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Iic (T : ℝ)
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Iic
  have hA_fin : MeasureTheory.processMeasure μ A < ∞ := by
    have hInter :
        Set.Iic (T : ℝ) ∩ Set.Ici (0 : ℝ) = Set.Icc (0 : ℝ) (T : ℝ) := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1⟩
    -- Proof comment: under `processMeasure μ`, the cutoff region `t ≤ T` reduces to the finite
    -- strip `[0,T]`.
    simp [MeasureTheory.processMeasure, A, Measure.restrict_apply, hA, hInter,
      measure_Icc_lt_top]
  have hClip_meas :
      Measurable (MeasureTheory.processToTimeSpaceFun (clippedProcess H R)) := by
    exact measurable_processToTimeSpaceFun_of_progMeasurable (ℱ := ℱ) hClip_prog
  have hIndicatorEq :
      MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal))) =
        A.indicator (MeasureTheory.processToTimeSpaceFun (clippedProcess H R)) := by
    have hAeq : A = {x : Ω × ℝ | x.2 ≤ (T : ℝ)} := by
      ext x
      rcases x with ⟨ω, t⟩
      simp [A]
    rw [BrownianItoIntegral.processBeforeStoppingTime_eq_cutoffBeforeDeterministicTime_local
      (H := clippedProcess H R) (t := T)]
    simpa [hAeq] using
      BrownianItoIntegral.processToTimeSpaceFun_cutoffBeforeDeterministicTime_local
        (Ω := Ω) T (clippedProcess H R)
  rw [hIndicatorEq]
  exact
    memLp_indicator_of_bound_of_finiteProcessMeasure
      (μ := μ) A hA hA_fin hClip_meas.aestronglyMeasurable
      (fun {_x} _hx ↦ by
        rcases _x with ⟨ω, t⟩
        simpa [MeasureTheory.processToTimeSpaceFun, Real.norm_eq_abs] using
          abs_clippedProcess_le (H := H) R t.toNNReal ω)

/-- Helper for Exercise 25.2.1(i): the truncated partition row times are the original left
endpoints, clamped only at the terminal horizon `T`. -/
private def constCutoffPartitionRowTimes
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal) :
    Fin (partitionBoundIndex P row T + 1) → NNReal :=
  fun j ↦ min (P row j) T

/-- Helper for Exercise 25.2.1(i): the truncated partition-row times still start at `0`. -/
private lemma constCutoffPartitionRowTimes_zero
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal) :
    constCutoffPartitionRowTimes P row T 0 = 0 := by
  -- Proof comment: the first partition point is `0`, and clamping `0` at `T` leaves it fixed.
  simp [constCutoffPartitionRowTimes, IsAdmissiblePartitionSequence.zero_eq (P := P) row]

/-- Helper for Exercise 25.2.1(i): every nonterminal truncated partition-row time is exactly the
original left endpoint, because those endpoints lie strictly before `T`. -/
private lemma constCutoffPartitionRowTimes_castSucc
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal)
    (i : Fin (partitionBoundIndex P row T)) :
    constCutoffPartitionRowTimes P row T i.castSucc = P row i := by
  -- Proof comment: indices strictly below the truncation index correspond to partition points
  -- lying strictly before `T`, so the outer `min` is inactive there.
  change min (P row i) T = P row i
  rw [min_eq_left]
  exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P row i T i.is_lt)

/-- Helper for Exercise 25.2.1(i): the successor truncated partition-row time is the clipped next
partition point `partitionNextPointUpTo`. -/
private lemma constCutoffPartitionRowTimes_succ
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal)
    (i : Fin (partitionBoundIndex P row T)) :
    constCutoffPartitionRowTimes P row T i.succ = partitionNextPointUpTo P row i T := by
  -- Proof comment: the row times were defined precisely by clamping each partition point at `T`.
  simp [constCutoffPartitionRowTimes, partitionNextPointUpTo]

/-- Helper for Exercise 25.2.1(i): the last truncated row time is the deterministic cutoff
horizon `T` itself. -/
private lemma constCutoffPartitionRowTimes_last
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal) :
    constCutoffPartitionRowTimes P row T (Fin.last (partitionBoundIndex P row T)) = T := by
  -- Proof comment: the final row time is `min (P row boundIndex) T`, and the truncation index is
  -- defined so that `P row boundIndex` has already reached `T`.
  simp [constCutoffPartitionRowTimes, min_eq_right, le_partitionBoundIndex_time]

/-- Helper for Exercise 25.2.1(i): the clamped row times remain strictly increasing, with the last
time possibly replaced by the terminal horizon `T`. -/
private lemma constCutoffPartitionRowTimes_strictMono
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (T : NNReal) :
    StrictMono (constCutoffPartitionRowTimes P row T) := by
  intro j k hjk
  have hk_le :
      (k : ℕ) ≤ partitionBoundIndex P row T :=
    Nat.le_of_lt_succ k.is_lt
  have hj_lt :
      (j : ℕ) < partitionBoundIndex P row T :=
    lt_of_lt_of_le hjk hk_le
  have hleft :
      constCutoffPartitionRowTimes P row T j = P row j := by
    rw [constCutoffPartitionRowTimes, min_eq_left]
    exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P row j T hj_lt)
  by_cases hk_lt : (k : ℕ) < partitionBoundIndex P row T
  · have hright :
        constCutoffPartitionRowTimes P row T k = P row k := by
      rw [constCutoffPartitionRowTimes, min_eq_left]
      exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P row k T hk_lt)
    -- Proof comment: before the terminal clamp becomes active, strict monotonicity is inherited
    -- directly from the partition row itself.
    rw [hleft, hright]
    exact (IsAdmissiblePartitionSequence.strictMono (P := P) row) hjk
  · have hk_eq :
        (k : ℕ) = partitionBoundIndex P row T := by
      exact le_antisymm hk_le (le_of_not_gt hk_lt)
    have hright :
        constCutoffPartitionRowTimes P row T k = T := by
      rw [constCutoffPartitionRowTimes, hk_eq, min_eq_right]
      exact le_partitionBoundIndex_time P row T
    -- Proof comment: once the right endpoint is the terminal clamp `T`, the earlier point is
    -- still strictly below `T` because its index lies strictly before the truncation index.
    rw [hleft, hright]
    exact partitionPoint_lt_time_of_lt_partitionBoundIndex P row j T hj_lt

/-- Helper for Exercise 25.2.1(i): each clipped left-endpoint coefficient on a fixed partition row
is deterministically bounded by the clipping radius `R`. -/
private lemma clippedConstCutoffPartitionRowCoeff_bounded
    {H : NNReal → Ω → ℝ}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal)
    (i : Fin (partitionBoundIndex P row T)) :
    ∃ C : ℝ, ∀ ω, |clippedProcess H R (P row i) ω| ≤ C := by
  refine ⟨R, ?_⟩
  intro ω
  exact abs_clippedProcess_le (H := H) R (P row i) ω

/-- Helper for Exercise 25.2.1(i): each clipped left-endpoint coefficient on a fixed partition row
is measurable with respect to the corresponding left-endpoint sigma-algebra. -/
private lemma clippedConstCutoffPartitionRowCoeff_measurable
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal)
    (i : Fin (partitionBoundIndex P row T)) :
    Measurable[ℱ ((constCutoffPartitionRowTimes P row T) i.castSucc)]
      (fun ω ↦ clippedProcess H R (P row i) ω) := by
  have hClip_prog :
      ProgMeasurable ℱ (clippedProcess H R) :=
    clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont
  have hClip_adapted : Adapted ℱ (clippedProcess H R) :=
    hClip_prog.stronglyAdapted.adapted
  -- Proof comment: the left-endpoint coefficient is sampled at the deterministic time
  -- `P row i`, which matches the corresponding clamped row time `times i.castSucc`.
  rw [constCutoffPartitionRowTimes_castSucc P row T i]
  simpa using hClip_adapted (P row i)

/-- Helper for Exercise 25.2.1(i): the clipped fixed-horizon partition row can be viewed as a
predictable-step representation with the same left-endpoint coefficients and terminal time `T`. -/
private noncomputable def clippedConstCutoffPartitionRowRepresentation
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    MeasureTheory.PredictableStepRepresentation ℱ :=
  { n := partitionBoundIndex P row T
    times := constCutoffPartitionRowTimes P row T
    coeff := fun i ω ↦ clippedProcess H R (P row i) ω
    times_zero := constCutoffPartitionRowTimes_zero P row T
    times_strictMono := constCutoffPartitionRowTimes_strictMono P row T
    coeff_bounded := clippedConstCutoffPartitionRowCoeff_bounded (H := H) P row R T
    coeff_measurable :=
      clippedConstCutoffPartitionRowCoeff_measurable
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T }

/-- Helper for Exercise 25.2.1(i): the terminal elementary integral of the clipped row
representation is exactly the concrete clipped partition sum on that row. -/
private lemma clippedConstCutoffPartitionRowElementaryIntegral_eq_partitionSum
    {H W : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) (ω : Ω)
    (hW_cont : Continuous fun t : NNReal ↦ W t ω) :
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
        (clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T)
        W
        ω
      =
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ clippedProcess H R t ω)
      (⟨fun t ↦ W t ω, hW_cont⟩ : PathSpace)
      P
      T
      row := by
  -- Proof comment: once the row representation is written with the clamped partition times,
  -- its terminal elementary integral is the same finite left-point increment sum by definition.
  simpa [partitionPathwiseItoApproximationUpTo, clippedConstCutoffPartitionRowRepresentation,
    constCutoffPartitionRowTimes, partitionNextPointUpTo] using
    (MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply
      (clippedConstCutoffPartitionRowRepresentation
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T)
      W
      ω)

/-- Helper for Exercise 25.2.1(i): on the active strip `(0, T]`, the clipped row step process
evaluates at the predecessor point of the same partition row. -/
private lemma clippedConstCutoffPartitionRow_toProcess_eq_predecessor
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) {ω : Ω} {t : ℝ}
    (ht_pos : 0 < t) (ht_le : t ≤ T) :
    MeasureTheory.processToTimeSpaceFun
        (clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toProcess
        (ω, t) =
      clippedProcess H R (partitionPredecessorPointEarly P row t.toNNReal) ω := by
  let data : MeasureTheory.PredictableStepRepresentation ℱ :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  have ht_pos_nnreal : 0 < t.toNNReal := by
    rw [Real.toNNReal_pos]
    exact ht_pos
  have ht_le_last : t.toNNReal ≤ data.times (Fin.last data.n) := by
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have htt : t.toNNReal ≤ T := by
      simpa [Real.toNNReal_of_nonneg ht_nonneg] using ht_le
    have hlast : data.times (Fin.last data.n) = T := by
      simpa [data] using constCutoffPartitionRowTimes_last P row T
    rw [hlast]
    exact htt
  obtain ⟨i, hti⟩ := data.exists_mem_interval_of_pos_le_last ht_pos_nnreal ht_le_last
  have hproc : data.toProcess t.toNNReal ω = data.coeff i ω :=
    data.toProcess_eq_coeff_of_mem_interval i hti ω
  have hleft : P row i < t.toNNReal := by
    have hcast : data.times i.castSucc = P row i := by
      simpa [data] using constCutoffPartitionRowTimes_castSucc P row T i
    rw [hcast] at hti
    exact hti.1
  have hright : t.toNNReal ≤ P row (i + 1) := by
    calc
      t.toNNReal ≤ data.times i.succ := hti.2
      _ = partitionNextPointUpTo P row i T := by
            simpa [data] using constCutoffPartitionRowTimes_succ P row T i
      _ ≤ P row (i + 1) := by
            simp [partitionNextPointUpTo]
  have hidx : partitionBoundIndex P row t.toNNReal = i + 1 :=
    partitionBoundIndex_eq_succ_of_lt_of_le P row i hleft hright
  have hpred : partitionPredecessorPointEarly P row t.toNNReal = P row i := by
    -- Proof comment: once the active strip index is identified, the predecessor point is exactly
    -- the corresponding left endpoint of the same partition row.
    simp [partitionPredecessorPointEarly, hidx]
  calc
    MeasureTheory.processToTimeSpaceFun data.toProcess (ω, t)
        = data.toProcess t.toNNReal ω := by
            simp [MeasureTheory.processToTimeSpaceFun]
    _ = data.coeff i ω := hproc
    _ = clippedProcess H R (P row i) ω := by
          rfl
    _ = clippedProcess H R (partitionPredecessorPointEarly P row t.toNNReal) ω := by
          rw [hpred]

/-- Helper for Exercise 25.2.1(i): on the active strip `(0, T]`, the clipped row step processes
converge pointwise to the deterministically cutoff clipped process. -/
private lemma tendsto_processToTimeSpaceFun_clippedConstCutoffPartitionRow_at_pos
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) {ω : Ω} {t : ℝ}
    (ht_pos : 0 < t) (ht_le : t ≤ T) :
    Tendsto
      (fun row ↦
        MeasureTheory.processToTimeSpaceFun
          (clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toProcess
          (ω, t))
      atTop
      (𝓝
        (MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
          (ω, t))) := by
  have hpred :
      Tendsto (fun row ↦ partitionPredecessorPointEarly P row t.toNNReal) atTop (𝓝 t.toNNReal) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows P strictMono_id t.toNNReal
  have htarget :
      Tendsto
        (fun row ↦ clippedProcess H R (partitionPredecessorPointEarly P row t.toNNReal) ω)
        atTop
        (𝓝 (clippedProcess H R t.toNNReal ω)) :=
    (clippedProcess_continuous (H := H) R (hH_cont ω)).continuousAt.tendsto.comp hpred
  have hrowEq :
      (fun row ↦
        MeasureTheory.processToTimeSpaceFun
          (clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toProcess
          (ω, t)) =
        fun row ↦ clippedProcess H R (partitionPredecessorPointEarly P row t.toNNReal) ω := by
    funext row
    exact
      clippedConstCutoffPartitionRow_toProcess_eq_predecessor
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T ht_pos ht_le
  have ht_cutoff :
      MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
          (ω, t) =
        clippedProcess H R t.toNNReal ω := by
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have htt : t.toNNReal ≤ T := by
      simpa [Real.toNNReal_of_nonneg ht_nonneg] using ht_le
    have ht_le_cutoff : ((t.toNNReal : NNReal) : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast htt
    change processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t.toNNReal ω =
      clippedProcess H R t.toNNReal ω
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos ht_le_cutoff]
  rw [hrowEq]
  simpa [ht_cutoff] using htarget

/-- Helper for Exercise 25.2.1(i): after the deterministic cutoff horizon `T`, every clipped row
stage vanishes in time-space coordinates. -/
private lemma clippedConstCutoffPartitionRow_timeSpace_eq_zero_of_gt
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) {ω : Ω} {t : ℝ}
    (hTt : T < t) :
    MeasureTheory.processToTimeSpaceFun
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ))
        (ω, t) = 0 := by
  let data :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  have ht_nonneg : 0 ≤ t := by
    exact le_trans (by exact_mod_cast (show (0 : NNReal) ≤ T from bot_le)) (le_of_lt hTt)
  have hlast : data.times (Fin.last data.n) = T := by
    simpa [data] using constCutoffPartitionRowTimes_last P row T
  have hafter : data.times (Fin.last data.n) < t.toNNReal := by
    rw [hlast, Real.toNNReal_of_nonneg ht_nonneg]
    exact hTt
  -- Proof comment: once the real time lies strictly past `T`, it is already past the last row
  -- time of the clipped representation, so the predictable-step process is identically zero.
  change data.toProcess t.toNNReal ω = 0
  exact data.toProcess_eq_zero_of_last_lt hafter ω

/-- Helper for Exercise 25.2.1(i): after the deterministic cutoff horizon `T`, the clipped target
process itself vanishes in time-space coordinates. -/
private lemma processBeforeStoppingTime_clippedConstCutoff_timeSpace_eq_zero_of_gt
    {H : NNReal → Ω → ℝ} (R T : NNReal) {ω : Ω} {t : ℝ}
    (hTt : T < t) :
    MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        (ω, t) = 0 := by
  have ht_nonneg : 0 ≤ t := by
    exact le_trans (by exact_mod_cast (show (0 : NNReal) ≤ T from bot_le)) (le_of_lt hTt)
  have ht_not_le : ¬ t.toNNReal ≤ T := by
    rw [Real.toNNReal_of_nonneg ht_nonneg]
    exact not_le_of_gt hTt
  have ht_not_cutoff : ¬ (((t.toNNReal : NNReal) : ENNReal) ≤ (T : ENNReal)) := by
    exact_mod_cast ht_not_le
  -- Proof comment: beyond the deterministic cutoff time, `processBeforeStoppingTime` takes the
  -- zero branch, so the time-space representative also vanishes.
  change processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t.toNNReal ω = 0
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg ht_not_cutoff]

/-- Helper for Exercise 25.2.1(i): on the deterministic strip `(-∞, T]`, every clipped
deterministic-cutoff partition row is uniformly bounded by the clipping radius `R`. -/
private lemma norm_processToTimeSpaceFun_clippedConstCutoffRow_le_of_le
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) {ω : Ω} {t : ℝ}
    (ht_le : t ≤ T) :
    |MeasureTheory.processToTimeSpaceFun
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ))
        (ω, t)| ≤ (R : ℝ) := by
  let data :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  by_cases ht_pos : 0 < t
  · -- Proof comment: on the active strip `(0, T]`, the row stage is the clipped predecessor
    -- coefficient, so the clipping radius gives the required uniform bound.
    have hproc :
        MeasureTheory.processToTimeSpaceFun
            (((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
                NNReal → Ω → ℝ))
            (ω, t) =
          clippedProcess H R (partitionPredecessorPointEarly P row t.toNNReal) ω := by
      simpa [MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe] using
        clippedConstCutoffPartitionRow_toProcess_eq_predecessor
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T ht_pos ht_le
    rw [hproc]
    exact abs_clippedProcess_le (H := H) R (partitionPredecessorPointEarly P row t.toNNReal) ω
  · have ht_nonpos : t ≤ 0 := le_of_not_gt ht_pos
    have ht0 : t.toNNReal = 0 := Real.toNNReal_of_nonpos ht_nonpos
    have hsum :
        ∑ i : Fin data.n,
            data.coeff i ω *
              Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
                (fun _ : NNReal ↦ (1 : ℝ)) 0 =
          0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_not :
          (0 : NNReal) ∉ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
        simp
      simp [Set.indicator_of_notMem hi_not]
    -- Proof comment: at nonpositive real times, `processToTimeSpaceFun` samples the row stage at
    -- `0`, and every `Ioc` cell of the predictable-step representation vanishes there.
    simpa [MeasureTheory.processToTimeSpaceFun, ht0, data,
      MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe,
      MeasureTheory.PredictableStepRepresentation.toProcess_apply, hsum] using
      (show |(0 : ℝ)| ≤ (R : ℝ) by
        have hR_nonneg : (0 : ℝ) ≤ R := by
          exact_mod_cast (show (0 : NNReal) ≤ R from bot_le)
        simpa [abs_of_nonneg hR_nonneg] using hR_nonneg)

/-- Helper for Exercise 25.2.1(i): on the finite strip `(0,T]`, the clipped deterministic-cutoff
partition rows converge to the deterministically stopped clipped process in square-integral
time-space norm. -/
private lemma lintegral_sqDiff_clippedConstCutoffPartitionRow_tendsto_zero
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    Tendsto
      (fun row ↦
        ∫⁻ x in ((Set.univ : Set Ω) ×ˢ Set.Ioc (0 : ℝ) (T : ℝ)),
          ‖MeasureTheory.processToTimeSpaceFun
              (((clippedConstCutoffPartitionRowRepresentation
                  (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
                  NNReal → Ω → ℝ))
              x -
            MeasureTheory.processToTimeSpaceFun
              (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
              x‖ₑ ^ (2 : ℕ)
          ∂ MeasureTheory.processMeasure μ)
      atTop
      (𝓝 0) := by
  let A : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Ioc (0 : ℝ) (T : ℝ)
  let μA : Measure (Ω × ℝ) := (MeasureTheory.processMeasure μ).restrict A
  let target : Ω × ℝ → ℝ := fun x ↦
    MeasureTheory.processToTimeSpaceFun
      (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
      x
  let stage : ℕ → Ω × ℝ → ℝ := fun row x ↦
    MeasureTheory.processToTimeSpaceFun
      (((clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
          NNReal → Ω → ℝ))
      x
  let bound : Ω × ℝ → ℝ≥0∞ := fun _ ↦ (ENNReal.ofReal (2 * (R : ℝ))) ^ (2 : ℕ)
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Ioc
  have hA_fin : MeasureTheory.processMeasure μ A < ∞ := by
    have hsubset : Set.Ioc (0 : ℝ) (T : ℝ) ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      exact le_of_lt ht.1
    -- Proof comment: the active strip `(0,T]` has finite `processMeasure μ`-mass because
    -- `processMeasure μ` is Lebesgue on time, restricted to `t ≥ 0`.
    simp [MeasureTheory.processMeasure, A, Set.inter_eq_left.mpr hsubset, measure_Ioc_lt_top]
  have hStageAemeas :
      ∀ row : ℕ, AEMeasurable (stage row) μA := by
    intro row
    let data :=
      clippedConstCutoffPartitionRowRepresentation
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
    have hProg :
        ProgMeasurable ℱ
          ((data.toPredictableSimpleProcess : NNReal → Ω → ℝ)) := by
      simpa using
        (PredictableSimpleProcess.isPredictable data.toPredictableSimpleProcess).progMeasurable
    exact
      (measurable_processToTimeSpaceFun_of_progMeasurable (ℱ := ℱ) hProg).aemeasurable
  have hTargetAemeas : AEMeasurable target μA := by
    have hCutStop :
        IsStoppingTime ℱ (fun _ ↦ (T : ENNReal)) := isStoppingTime_const ℱ T
    have hClip_prog :
        ProgMeasurable ℱ (clippedProcess H R) :=
      clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont
    exact
      (measurable_processToTimeSpaceFun_of_progMeasurable
        (ℱ := ℱ)
        (MeasureTheory.processBeforeStoppingTime_progMeasurable hClip_prog hCutStop)).aemeasurable
  have hBound :
      ∀ row : ℕ,
        (fun x ↦ ‖stage row x - target x‖ₑ ^ (2 : ℕ)) ≤ᵐ[μA] bound := by
    intro row
    change (fun x ↦ ‖stage row x - target x‖ₑ ^ (2 : ℕ)) ≤ᵐ[(MeasureTheory.processMeasure μ).restrict A] bound
    refine (ae_restrict_iff' hA).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hxA
    rcases x with ⟨ω, t⟩
    have ht_mem : t ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
      simpa [A] using hxA
    have hStageBound :
        ‖stage row (ω, t)‖ ≤ (R : ℝ) := by
      simpa [stage, Real.norm_eq_abs] using
        norm_processToTimeSpaceFun_clippedConstCutoffRow_le_of_le
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T (ω := ω) (t := t) ht_mem.2
    have hTargetBound :
        ‖target (ω, t)‖ ≤ (R : ℝ) := by
      simpa [target, Real.norm_eq_abs] using
        norm_processToTimeSpaceFun_clippedConstCutoff_le
          (H := H) R T (ω, t)
    have hDiffBound :
        ‖stage row (ω, t) - target (ω, t)‖ ≤ 2 * (R : ℝ) := by
      calc
        ‖stage row (ω, t) - target (ω, t)‖
            ≤ ‖stage row (ω, t)‖ + ‖target (ω, t)‖ := norm_sub_le _ _
        _ ≤ (R : ℝ) + (R : ℝ) := add_le_add hStageBound hTargetBound
        _ = 2 * (R : ℝ) := by ring
    have hEnormBound :
        ‖stage row (ω, t) - target (ω, t)‖ₑ ≤ ENNReal.ofReal (2 * (R : ℝ)) := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
        ENNReal.ofReal_le_ofReal hDiffBound
    calc
      ‖stage row (ω, t) - target (ω, t)‖ₑ ^ (2 : ℕ)
          ≤ (ENNReal.ofReal (2 * (R : ℝ))) ^ (2 : ℕ) := by
            exact pow_le_pow_left' hEnormBound 2
      _ = bound (ω, t) := by rfl
  have hFin :
      ∫⁻ x, bound x ∂ μA ≠ ∞ := by
    have hμA_fin : μA Set.univ < ∞ := by
      simpa [μA, hA] using hA_fin
    have hfin : ∫⁻ x, bound x ∂ μA < ∞ := by
      rw [lintegral_const]
      have hBase_lt_top : ENNReal.ofReal (2 * (R : ℝ)) < ∞ := ENNReal.ofReal_lt_top
      have hBound_lt_top : (ENNReal.ofReal (2 * (R : ℝ))) ^ (2 : ℕ) < ∞ := by
        simpa [pow_two] using
          ENNReal.mul_lt_top hBase_lt_top hBase_lt_top
      simpa [bound] using ENNReal.mul_lt_top hBound_lt_top hμA_fin
    exact ne_of_lt hfin
  have hLimit :
      ∀ᵐ x ∂ μA,
        Tendsto (fun row ↦ ‖stage row x - target x‖ₑ ^ (2 : ℕ)) atTop (𝓝 0) := by
    change ∀ᵐ x ∂ (MeasureTheory.processMeasure μ).restrict A,
        Tendsto (fun row ↦ ‖stage row x - target x‖ₑ ^ (2 : ℕ)) atTop (𝓝 0)
    refine (ae_restrict_iff' hA).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hxA
    rcases x with ⟨ω, t⟩
    have ht_mem : t ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
      simpa [A] using hxA
    have hStage :
        Tendsto (fun row ↦ stage row (ω, t)) atTop (𝓝 (target (ω, t))) := by
      -- Proof comment: on `(0,T]`, the explicit predecessor-row formula converges pointwise to
      -- the stopped clipped process.
      simpa [stage, target] using
        tendsto_processToTimeSpaceFun_clippedConstCutoffPartitionRow_at_pos
          (ℱ := ℱ) (H := H) hH_prog hH_cont P R T
          (ω := ω) (t := t) ht_mem.1 ht_mem.2
    have hDiff :
        Tendsto (fun row ↦ stage row (ω, t) - target (ω, t)) atTop (𝓝 0) := by
      have hConst :
          Tendsto (fun _ : ℕ ↦ target (ω, t)) atTop (𝓝 (target (ω, t))) :=
        tendsto_const_nhds
      simpa using hStage.sub hConst
    -- Proof comment: the square norm is a continuous scalar functional, so it preserves the
    -- pointwise row limit on the active strip.
    have hEnorm :
        Tendsto (fun row ↦ ‖stage row (ω, t) - target (ω, t)‖ₑ) atTop (𝓝 0) := by
      simpa using hDiff.enorm
    have hPow :
        Tendsto
          (fun row ↦ ‖stage row (ω, t) - target (ω, t)‖ₑ ^ (2 : ℕ))
          atTop
          (𝓝 0) := by
      simpa [ENNReal.rpow_natCast] using
        Filter.Tendsto.ennrpow_const (f := atTop)
          (m := fun row ↦ ‖stage row (ω, t) - target (ω, t)‖ₑ)
          (a := 0) (r := (2 : ℝ)) hEnorm
    exact hPow
  have hLintegral :
      Tendsto
        (fun row ↦ ∫⁻ x, ‖stage row x - target x‖ₑ ^ (2 : ℕ) ∂ μA)
        atTop
        (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂ μA)) := by
    exact
      MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        bound
        (fun row ↦ (hStageAemeas row).sub hTargetAemeas |>.enorm.pow_const 2)
        hBound
        hFin
        hLimit
  simpa [μA, A] using hLintegral

/-- Helper for Exercise 25.2.1(i): the nonpositive time slice has zero `processMeasure μ`-mass,
so later fixed-horizon `L²` reductions may ignore the boundary time `t = 0`. -/
private lemma processMeasure_univ_prod_Iic_zero :
    MeasureTheory.processMeasure μ ((Set.univ : Set Ω) ×ˢ Set.Iic (0 : ℝ)) = 0 := by
  let B : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Iic (0 : ℝ)
  have hB : MeasurableSet B := MeasurableSet.univ.prod measurableSet_Iic
  have hInter :
      Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) = ({0} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      have ht0 : t = 0 := le_antisymm ht.1 ht.2
      simpa [ht0]
    · intro ht
      rcases ht with rfl
      simpa using
        (show (0 : ℝ) ∈ Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) from ⟨le_rfl, le_rfl⟩)
  -- Proof comment: `processMeasure μ` is supported on `t ≥ 0`, so intersecting with `t ≤ 0`
  -- leaves only the singleton time slice `{0}`, which has Lebesgue measure `0`.
  simp [MeasureTheory.processMeasure, B, Measure.restrict_apply, hB, hInter, measure_singleton]

/-- Helper for Exercise 25.2.1(i): after extending the stripwise square-error theorem by the
zero-mass boundary slice and the vanishing `t > T` tail, the same row family converges globally
in square-integral time-space error. -/
private lemma globalLintegral_sqDiff_clippedConstCutoffPartitionRow_tendsto_zero
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    Tendsto
      (fun row ↦
        ∫⁻ x,
          ‖MeasureTheory.processToTimeSpaceFun
              (((clippedConstCutoffPartitionRowRepresentation
                  (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
                  NNReal → Ω → ℝ))
              x -
            MeasureTheory.processToTimeSpaceFun
              (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
              x‖ₑ ^ (2 : ℕ)
          ∂ MeasureTheory.processMeasure μ)
      atTop
      (𝓝 0) := by
  let A : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Ioc (0 : ℝ) (T : ℝ)
  let B : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Iic (0 : ℝ)
  let C : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Ioi (T : ℝ)
  let err : ℕ → Ω × ℝ → ℝ≥0∞ := fun row x ↦
    ‖MeasureTheory.processToTimeSpaceFun
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ))
        x -
      MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        x‖ₑ ^ (2 : ℕ)
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Ioc
  have hB : MeasurableSet B := MeasurableSet.univ.prod measurableSet_Iic
  have hC : MeasurableSet C := MeasurableSet.univ.prod measurableSet_Ioi
  have hCompl : Aᶜ = B ∪ C := by
    ext x
    rcases x with ⟨ω, t⟩
    constructor
    · intro hx
      by_cases ht_nonpos : t ≤ 0
      · left
        simp [B, ht_nonpos]
      · right
        have ht_pos : 0 < t := lt_of_not_ge ht_nonpos
        have hnot_mem : ¬ t ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
          intro ht_mem
          exact hx (by simp [A, ht_mem])
        have ht_not_le_T : ¬ t ≤ T := by
          intro ht_le_T
          exact hnot_mem ⟨ht_pos, ht_le_T⟩
        have hTt : T < t := lt_of_not_ge ht_not_le_T
        simp [C, hTt]
    · intro hx
      intro hxA
      rcases hx with hxB | hxC
      · have ht_nonpos : t ≤ 0 := by simpa [B] using hxB
        exact not_lt_of_ge ht_nonpos hxA.2.1
      · have hTt : T < t := by simpa [C] using hxC
        exact not_lt_of_ge hxA.2.2 hTt
  have hBC : Disjoint B C := by
    refine Set.disjoint_left.2 ?_
    intro x hxB hxC
    rcases x with ⟨ω, t⟩
    have ht_nonpos : t ≤ 0 := by
      simpa [B] using hxB
    have ht_gt : T < t := by
      simpa [C] using hxC
    have hT_nonneg : (0 : ℝ) ≤ T := by
      positivity
    have ht_le_T : t ≤ T := le_trans ht_nonpos hT_nonneg
    exact (not_lt_of_ge ht_le_T) ht_gt
  have hBzero :
      ∀ row : ℕ, ∫⁻ x in B, err row x ∂ MeasureTheory.processMeasure μ = 0 := by
    intro row
    have hBmeasure :
        MeasureTheory.processMeasure μ B = 0 := by
      simpa [B] using (processMeasure_univ_prod_Iic_zero (μ := μ))
    have hRestrict : (MeasureTheory.processMeasure μ).restrict B = 0 :=
      Measure.restrict_eq_zero.2 hBmeasure
    -- Proof comment: the nonpositive time slice carries no time-space mass, so every restricted
    -- square-error integral there vanishes automatically.
    simp [hRestrict]
  have hCzero :
      ∀ row : ℕ, ∫⁻ x in C, err row x ∂ MeasureTheory.processMeasure μ = 0 := by
    intro row
    refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
    refine (ae_restrict_iff' hC).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hxC
    rcases x with ⟨ω, t⟩
    have hTt : T < t := by
      simpa [C] using hxC
    have hStageZero :
        MeasureTheory.processToTimeSpaceFun
            (((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
                NNReal → Ω → ℝ))
            (ω, t) = 0 := by
      exact
        clippedConstCutoffPartitionRow_timeSpace_eq_zero_of_gt
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T (ω := ω) (t := t) hTt
    have hTargetZero :
        MeasureTheory.processToTimeSpaceFun
            (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
            (ω, t) = 0 := by
      exact
        processBeforeStoppingTime_clippedConstCutoff_timeSpace_eq_zero_of_gt
          (H := H) R T (ω := ω) (t := t) hTt
    -- Proof comment: after the deterministic cutoff horizon `T`, both the row stage and the
    -- stopped target are already zero pointwise.
    simpa [err, hStageZero, hTargetZero]
  have hGlobalEq :
      ∀ row : ℕ,
        ∫⁻ x, err row x ∂ MeasureTheory.processMeasure μ =
          ∫⁻ x in A, err row x ∂ MeasureTheory.processMeasure μ := by
    intro row
    have hComplZero :
        ∫⁻ x in Aᶜ, err row x ∂ MeasureTheory.processMeasure μ = 0 := by
      rw [hCompl, MeasureTheory.lintegral_union (μ := MeasureTheory.processMeasure μ)
        (f := err row) hC hBC, hBzero row, hCzero row]
      simp
    calc
      ∫⁻ x, err row x ∂ MeasureTheory.processMeasure μ =
          ∫⁻ x in A, err row x ∂ MeasureTheory.processMeasure μ +
            ∫⁻ x in Aᶜ, err row x ∂ MeasureTheory.processMeasure μ := by
              symm
              exact lintegral_add_compl (μ := MeasureTheory.processMeasure μ) (f := err row) hA
      _ = ∫⁻ x in A, err row x ∂ MeasureTheory.processMeasure μ := by
            rw [hComplZero, add_zero]
  -- Proof comment: the existing strip theorem already proves convergence on `A = (0,T]`; the
  -- previous support reductions show that the omitted complement contributes exactly `0`.
  exact
    Tendsto.congr' (Filter.Eventually.of_forall fun row ↦ (hGlobalEq row).symm)
      (lintegral_sqDiff_clippedConstCutoffPartitionRow_tendsto_zero
        (ℱ := ℱ) (H := H) hH_prog hH_cont P R T)

/-- Helper for Exercise 25.2.1(i): every clipped deterministic-cutoff partition row is a genuine
ambient `L²(processMeasure μ)` predictable simple stage. -/
private lemma clippedConstCutoffRow_memLp
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ)))
      (2 : ℝ≥0∞)
      (MeasureTheory.processMeasure μ) := by
  let data :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  let K : NNReal → Ω → ℝ := data.toPredictableSimpleProcess
  let A : Set (Ω × ℝ) := (Set.univ : Set Ω) ×ˢ Set.Ioc (0 : ℝ) (T : ℝ)
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Ioc
  have hA_fin : MeasureTheory.processMeasure μ A < ∞ := by
    have hsubset : Set.Ioc (0 : ℝ) (T : ℝ) ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      exact le_of_lt ht.1
    -- Proof comment: the row stage is supported on the deterministic strip `(0,T]`, whose
    -- `processMeasure μ`-mass is finite because `μ` is a probability measure.
    simp [MeasureTheory.processMeasure, A, Set.inter_eq_left.mpr hsubset, measure_Ioc_lt_top]
  have hK_prog : ProgMeasurable ℱ K := by
    -- Proof comment: the clipped row stage is already a predictable simple process, hence
    -- progressively measurable.
    have hPred : IsPredictable ℱ (data.toPredictableSimpleProcess : NNReal → Ω → ℝ) :=
      PredictableSimpleProcess.isPredictable data.toPredictableSimpleProcess
    simpa [K] using hPred.progMeasurable
  have hK_meas :
      Measurable (MeasureTheory.processToTimeSpaceFun K) := by
    exact measurable_processToTimeSpaceFun_of_progMeasurable (ℱ := ℱ) hK_prog
  have hIndicatorEq :
      A.indicator (MeasureTheory.processToTimeSpaceFun K) =
        MeasureTheory.processToTimeSpaceFun K := by
    funext x
    rcases x with ⟨ω, t⟩
    by_cases hmem : (ω, t) ∈ A
    · simp [A, hmem]
    · have hzero :
          MeasureTheory.processToTimeSpaceFun K (ω, t) = 0 := by
        have hnot_mem_time : ¬ t ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
          intro ht
          exact hmem (by simp [A, ht])
        have hnot_mem_time' : ¬ (0 < t ∧ t ≤ T) := by
          simpa [Set.mem_Ioc] using hnot_mem_time
        rcases not_and_or.mp hnot_mem_time' with ht_nonpos | ht_gt
        · have ht0 : t.toNNReal = 0 := Real.toNNReal_of_nonpos (le_of_not_gt ht_nonpos)
          have hsum :
              ∑ i : Fin data.n,
                  data.coeff i ω *
                    Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
                      (fun _ : NNReal ↦ (1 : ℝ)) 0 =
                0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            have hi_not :
                (0 : NNReal) ∉ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
              simp
            simp [Set.indicator_of_notMem hi_not]
          simpa [MeasureTheory.processToTimeSpaceFun, ht0, K,
            MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe,
            MeasureTheory.PredictableStepRepresentation.toProcess_apply, hsum]
        · have ht_pos : 0 ≤ t := le_trans (by exact_mod_cast (show (0 : NNReal) ≤ T from bot_le))
            (le_of_lt (lt_of_not_ge ht_gt))
          have hlast :
              data.times (Fin.last data.n) = T :=
            constCutoffPartitionRowTimes_last P row T
          have hafter :
              data.times (Fin.last data.n) < t.toNNReal := by
            rw [hlast, Real.toNNReal_of_nonneg ht_pos]
            exact lt_of_not_ge ht_gt
          simpa [MeasureTheory.processToTimeSpaceFun, K, Real.toNNReal_of_nonneg ht_pos,
            MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe] using
            data.toProcess_eq_zero_of_last_lt hafter ω
      simp [Set.indicator_of_notMem, hmem, hzero]
  rw [← hIndicatorEq, memLp_indicator_iff_restrict hA]
  letI : Fact (((MeasureTheory.processMeasure μ) A) < ∞) := ⟨hA_fin⟩
  have hK_aesm :
      AEStronglyMeasurable (MeasureTheory.processToTimeSpaceFun K)
        ((MeasureTheory.processMeasure μ).restrict A) :=
    hK_meas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ (MeasureTheory.processMeasure μ).restrict A,
        ‖MeasureTheory.processToTimeSpaceFun K x‖ ≤ (R : ℝ) := by
    rw [ae_restrict_iff' hA]
    filter_upwards with x hxA
    rcases x with ⟨ω, t⟩
    have ht_mem : t ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by simpa [A] using hxA
    -- Proof comment: the new stripwise bound packages exactly the predecessor-cell estimate
    -- used here, so the `MemLp` proof no longer needs to reconstruct the interval geometry.
    simpa [K, Real.norm_eq_abs] using
      norm_processToTimeSpaceFun_clippedConstCutoffRow_le_of_le
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T (ω := ω) (t := t) ht_mem.2
  -- Proof comment: after restricting to the finite strip `(0,T]`, the stage is measurable and
  -- uniformly bounded by `R`, so it lies in ambient `L²(processMeasure μ)`.
  exact MemLp.of_bound hK_aesm (R : ℝ) hbound

/-- Helper for Exercise 25.2.1(i): each clipped deterministic-cutoff partition row already gives
one canonical closure witness in `L²(processMeasure μ)`. -/
private lemma clippedConstCutoffPartitionRow_memPredictableStepProcessClosure
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (((clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
          NNReal → Ω → ℝ)) := by
  let K : MeasureTheory.PredictableSimpleProcess ℱ :=
    (clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess
  let hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ) :=
    clippedConstCutoffRow_memLp (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  -- Proof comment: a globally square-integrable predictable simple process is already one of the
  -- canonical generators of the predictable-step closure.
  exact ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩

/-- Helper for Exercise 25.2.1(i): the canonical closure point attached to one clipped
deterministic-cutoff partition row. -/
private noncomputable def clippedConstCutoffPartitionRowClosure
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
  _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure <|
    clippedConstCutoffPartitionRow_memPredictableStepProcessClosure
      (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T

/-- Helper for Exercise 25.2.1(i): the canonical closure point attached to the deterministic
cutoff of one closure member. -/
private noncomputable def constCutoffClosure
    {H : NNReal → Ω → ℝ}
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
  _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure <|
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
      (μ := μ) (ℱ := ℱ) hH_mem T

/-- Helper for Exercise 25.2.1(i): the canonical closure point attached to the deterministically
stopped clipped target process. -/
private noncomputable def clippedConstCutoffTargetClosure
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (R T : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
  _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure <|
    MeasureTheory.progMeasurable_memPredictableStepProcessClosure
      ℱ
      μ
      (MeasureTheory.processBeforeStoppingTime_progMeasurable
        (clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont)
        (isStoppingTime_const ℱ T))
      (clippedConstCutoff_memLp (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont R T)

/-- Helper for Exercise 25.2.1(i): each clipped deterministic-cutoff partition row vanishes after
the terminal horizon `T`, so later terminal-value comparisons can treat it as already cut off. -/
private lemma clippedConstCutoffPartitionRow_vanishesAfter
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u →
      ((clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
          NNReal → Ω → ℝ) u ω = 0 := by
  intro u ω hu
  let data :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  have hlast : data.times (Fin.last data.n) = T := by
    simpa [data] using constCutoffPartitionRowTimes_last P row T
  have hafter : data.times (Fin.last data.n) < u := by
    rw [hlast]
    exact hu
  -- Proof comment: the last time of the row representation is exactly `T`, so the predictable
  -- simple stage is identically zero at every later time.
  simpa [data, MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe] using
    data.toProcess_eq_zero_of_last_lt hafter ω

/-- Helper for Exercise 25.2.1(i): deterministically cutting off one clipped partition-row stage
at the same terminal horizon `T` leaves that predictable simple stage unchanged. -/
private lemma clippedConstCutoffPartitionRow_cutoffBefore_eq_self
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    ((BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local
        ((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
        T : MeasureTheory.PredictableSimpleProcess ℱ) :
        NNReal → Ω → ℝ) =
      ((clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
          NNReal → Ω → ℝ) := by
  let K : MeasureTheory.PredictableSimpleProcess ℱ :=
    (clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess
  funext u
  funext ω
  by_cases hu : u ≤ T
  · have hcut :
        (((BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
              MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ) u ω) =
          BrownianItoIntegral.cutoffBeforeDeterministicTime_local T (K : NNReal → Ω → ℝ) u ω := by
      simpa using
        congrArg (fun X : NNReal → Ω → ℝ => X u ω)
          (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local K T)
    -- Proof comment: before the deterministic cutoff time `T`, the cutoff stage keeps the
    -- original predictable-simple value unchanged.
    simpa [BrownianItoIntegral.cutoffBeforeDeterministicTime_local, hu] using hcut
  · have hzero :
      (K : NNReal → Ω → ℝ) u ω = 0 := by
      -- Proof comment: the clipped row stage is already supported inside `[0, T]`, so the value
      -- after `T` vanishes even before taking the explicit deterministic cutoff.
      exact
        clippedConstCutoffPartitionRow_vanishesAfter
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T (lt_of_not_ge hu)
    have hcut :
        (((BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
              MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ) u ω) =
          BrownianItoIntegral.cutoffBeforeDeterministicTime_local T (K : NNReal → Ω → ℝ) u ω := by
      simpa using
        congrArg (fun X : NNReal → Ω → ℝ => X u ω)
          (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local K T)
    -- Proof comment: after `T`, both the explicit cutoff and the original row stage are zero.
    calc
      (((BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
            MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ) u ω)
          = BrownianItoIntegral.cutoffBeforeDeterministicTime_local T (K : NNReal → Ω → ℝ) u ω := hcut
      _ = 0 := by
            simp [BrownianItoIntegral.cutoffBeforeDeterministicTime_local, hu]
      _ = (K : NNReal → Ω → ℝ) u ω := by
            symm
            exact hzero

/-- Helper for Exercise 25.2.1(i): the Brownian elementary integral of one clipped row at time
`T` is already the explicit clipped partition sum on that same row. -/
private lemma clippedConstCutoffPartitionRow_brownianIntegral_eq_partitionSum
    {H W : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) (ω : Ω)
    (hW_cont : Continuous fun t : NNReal ↦ W t ω) :
    MeasureTheory.brownianElementaryIntegral W
        ((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
        T
        ω =
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ clippedProcess H R t ω)
        (⟨fun t ↦ W t ω, hW_cont⟩ : PathSpace)
        P
        T
        row := by
  let data : MeasureTheory.PredictableStepRepresentation ℱ :=
    clippedConstCutoffPartitionRowRepresentation
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  let K : MeasureTheory.PredictableSimpleProcess ℱ := data.toPredictableSimpleProcess
  have hKrep : ((K : MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ) = data.toProcess := by
    simpa [K, data] using
      (MeasureTheory.PredictableStepRepresentation.toPredictableSimpleProcess_coe
        (representation := data))
  have hcutEq :
      (((BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
            MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ)) =
        (K : NNReal → Ω → ℝ) := by
    simpa [K, data] using
      clippedConstCutoffPartitionRow_cutoffBefore_eq_self
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  have hAtInfinityEq :
      MeasureTheory.brownianElementaryIntegralAtInfinity W
          (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T) =
        MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
    calc
      MeasureTheory.brownianElementaryIntegralAtInfinity W
          (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T)
          =
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
          data W := by
            exact
              MeasureTheory.brownianElementaryIntegralAtInfinity_spec
                W
                (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T)
                (hcutEq.trans hKrep)
      _ =
        MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
          symm
          exact MeasureTheory.brownianElementaryIntegralAtInfinity_spec W K hKrep
  calc
    MeasureTheory.brownianElementaryIntegral W K T ω
        =
      MeasureTheory.brownianElementaryIntegralAtInfinity W
        (BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T)
        ω := by
          exact
            congrFun
              (BrownianItoIntegral.brownianElementaryIntegral_predictableSimple_eq_cutoffTerminal_local
                K T)
              ω
    _ = MeasureTheory.brownianElementaryIntegralAtInfinity W K ω := by
          rw [hAtInfinityEq]
    _ =
      MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
        data W ω := by
          exact
            congrFun
              (MeasureTheory.brownianElementaryIntegralAtInfinity_spec W K hKrep)
              ω
    _ =
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ clippedProcess H R t ω)
        (⟨fun t ↦ W t ω, hW_cont⟩ : PathSpace)
        P
        T
        row := by
          simpa [data] using
            clippedConstCutoffPartitionRowElementaryIntegral_eq_partitionSum
              (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T ω hW_cont

/-- Helper for Exercise 25.2.1(i): deterministic stopping at time `T` does not change the
integrand on `Set.Icc 0 T`. -/
private lemma processBeforeStoppingTime_const_eqOn_Icc_local
    (H : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    Set.EqOn
      (fun t : NNReal ↦ ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
      (fun t : NNReal ↦ H t ω)
      (Set.Icc 0 T) := by
  intro t ht
  have htT : (t : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast ht.2
  -- Proof comment: inside the deterministic cutoff window, the stopped process is definitionally
  -- the original process.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htT]

/-- Helper for Exercise 25.2.1(i): deterministically cutting off the coefficient at the target
horizon does not change the left-point partition row up to that same horizon. -/
private lemma partitionPathwiseItoApproximationUpTo_congrOn_Icc_local
    {K L : NNReal → ℝ} {X : PathSpace}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} (hKL : Set.EqOn K L (Set.Icc 0 T)) (row : ℕ) :
    partitionPathwiseItoApproximationUpTo K X P T row =
      partitionPathwiseItoApproximationUpTo L X P T row := by
  -- Proof comment: every left endpoint used by the truncated row lies in `Set.Icc 0 T`, so the
  -- `EqOn` hypothesis rewrites the finite sum termwise.
  rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_mem :
      P row k ∈ Set.Icc 0 T :=
    partitionPoint_mem_Icc_of_lt_partitionBoundIndex P row k T (Finset.mem_range.mp hk)
  rw [hKL hk_mem]

/-- Helper for Exercise 25.2.1(i): if two coefficient paths already agree on `[0, T]`, then
their deterministic cutoffs at time `T` still agree on that same interval. -/
private lemma processBeforeStoppingTime_const_eqOn_Icc_of_eqOn_local
    {K L : NNReal → Ω → ℝ} {T : NNReal} {ω : Ω}
    (hKL : Set.EqOn (fun t : NNReal ↦ K t ω) (fun t ↦ L t ω) (Set.Icc 0 T)) :
    Set.EqOn
      (fun t : NNReal ↦ ProbabilityTheory.processBeforeStoppingTime K (fun _ ↦ (T : ENNReal)) t ω)
      (fun t : NNReal ↦ ProbabilityTheory.processBeforeStoppingTime L (fun _ ↦ (T : ENNReal)) t ω)
      (Set.Icc 0 T) := by
  intro t ht
  have htT : (t : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast ht.2
  -- Proof comment: on `[0, T]`, both deterministic cutoffs evaluate their original coefficients,
  -- so the comparison reduces to the input `EqOn` relation.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htT, hKL ht]

/-- Helper for Exercise 25.2.1(i): on a sample path that already stays inside the clip radius on
`[0, T]`, clipping does not change the coefficient on that interval. -/
private lemma clippedProcess_eqOn_Icc_of_abs_le_local
    {H : NNReal → Ω → ℝ} {R T : NNReal} {ω : Ω}
    (hbound : ∀ t : NNReal, t ∈ Set.Icc 0 T → |H t ω| ≤ R) :
    Set.EqOn
      (fun t : NNReal ↦ clippedProcess H R t ω)
      (fun t : NNReal ↦ H t ω)
      (Set.Icc 0 T) := by
  intro t ht
  -- Proof comment: the bounded-path hypothesis puts every point of `[0, T]` inside the clipping
  -- window `[-R, R]`.
  exact clippedProcess_eq_self_of_abs_le (H := H) (R := R) (t := t) (ω := ω) (hbound t ht)

/-- Helper for Exercise 25.2.1(i): on a bounded sample path, the clipped deterministic-cutoff row
sum agrees with the original deterministic-cutoff row sum at the same horizon. -/
private lemma partitionPathwiseItoApproximationUpTo_clippedConstCutoff_eq_of_abs_le
    {H : NNReal → Ω → ℝ} {X : PathSpace}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {R T : NNReal} {ω : Ω}
    (hbound : ∀ t : NNReal, t ∈ Set.Icc 0 T → |H t ω| ≤ R)
    (row : ℕ) :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
        X
        P
        T
        row =
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
        X
        P
        T
        row := by
  -- Proof comment: once both coefficients are deterministically cut off at `T`, the bounded-path
  -- hypothesis identifies them on every left endpoint contributing to the row sum.
  exact
    partitionPathwiseItoApproximationUpTo_congrOn_Icc_local
      (P := P) (X := X) (T := T)
      (hKL :=
        processBeforeStoppingTime_const_eqOn_Icc_of_eqOn_local
          (T := T) (ω := ω)
          (clippedProcess_eqOn_Icc_of_abs_le_local (H := H) (R := R) (T := T) (ω := ω) hbound))
      row

/-- Helper for Exercise 25.2.1(i): deterministically cutting off the coefficient at the target
horizon does not change the left-point partition row up to that same horizon. -/
private lemma partitionPathwiseItoApproximationUpTo_constCutoff_eq
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (ω : Ω) (row : ℕ) :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        T
        row =
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        T
        row := by
  -- Proof comment: every left endpoint in the truncated row lies in `Set.Icc 0 T`, where the
  -- deterministic cutoff coefficient agrees pointwise with the original coefficient.
  exact
    (partitionPathwiseItoApproximationUpTo_congrOn_Icc_local
      (P := P)
      (X := (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace))
      (T := T)
      (hKL := processBeforeStoppingTime_const_eqOn_Icc_local (H := H) T ω)
      row)

/-- Helper for Exercise 25.2.1(i): equality of two coefficients on `[0, T]` already identifies
their canonical fixed-time Itô values at time `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_of_eqOn_Icc_local
    {M K L : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    {T : NNReal} {ω : Ω}
    (hKL : Set.EqOn (fun t : NNReal ↦ K t ω) (fun t ↦ L t ω) (Set.Icc 0 T)) :
    continuousLocalMartingaleItoIntegralProcess hM K T ω =
      continuousLocalMartingaleItoIntegralProcess hM L T ω := by
  let X : PathSpace := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  have hRows :
      partitionPathwiseItoApproximationUpTo
          (fun t ↦ K t ω)
          X
          Definition2158.dyadicPartitionSequence
          T =
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ L t ω)
          X
          Definition2158.dyadicPartitionSequence
          T := by
    -- Proof comment: every dyadic left endpoint up to `T` lies in `[0, T]`, so the row family
    -- comparison is exactly the interval-wise coefficient comparison.
    funext row
    exact
      partitionPathwiseItoApproximationUpTo_congrOn_Icc_local
        (P := Definition2158.dyadicPartitionSequence)
        (X := X)
        (T := T)
        hKL
        row
  -- Proof comment: the canonical fixed-time value is defined as the `limUnder` of those dyadic
  -- rows, so equality of the whole row family identifies the two canonical values.
  rw [continuousLocalMartingaleItoIntegralProcess, continuousLocalMartingaleItoIntegralProcess,
    pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
  exact congrArg (limUnder atTop) hRows

/-- Helper for Exercise 25.2.1(i): at the fixed horizon `T`, the canonical Itô value of `H`
agrees pointwise with the canonical Itô value of the deterministic cutoff of `H` at `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (T : NNReal) (ω : Ω) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T ω =
      continuousLocalMartingaleItoIntegralProcess hM H T ω := by
  -- Proof comment: the deterministic cutoff already agrees with `H` on `[0, T]`, so the generic
  -- interval-identification lemma applies immediately.
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_of_eqOn_Icc_local
      (μ := μ) (ℱ := ℱ) (M := M)
      hM
      (T := T)
      (ω := ω)
      (processBeforeStoppingTime_const_eqOn_Icc_local (H := H) T ω)

/-- Helper for Exercise 25.2.1(i): any public Chapter 25 owner process also agrees almost
everywhere at the fixed horizon `T` with the deterministic-cutoff canonical Itô value of its
integrand. -/
private theorem itoIntegralOwner_aeEq_constCutoffCanonicalAtFixedTime
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hOwner :
      IsContinuousLocalMartingaleItoIntegralOwner
        (μ := μ) (ℱ := ℱ) (hM := hM) H N)
    (T : NNReal) :
    N T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T := by
  have hCanonical :
      N T =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H T :=
    itoIntegralOwner_aeEq_canonicalAtFixedTime
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (N := N) hOwner T
  have hCutoff :
      continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T :=
    Filter.Eventually.of_forall fun ω ↦
      continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM T ω
  -- Proof comment: first compare the owner with the unstopped canonical value, then rewrite that
  -- canonical value through the deterministic cutoff identity at the same horizon.
  exact hCanonical.trans hCutoff.symm

/-- Helper for Exercise 25.2.1(i): on a bounded sample path, the canonical fixed-time Itô value
of the clipped deterministic cutoff agrees with the original deterministic cutoff at time `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_clippedConstCutoff_value_of_abs_le
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    {R T : NNReal} {ω : Ω}
    (hbound : ∀ t : NNReal, t ∈ Set.Icc 0 T → |H t ω| ≤ R) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        T
        ω =
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T
        ω := by
  -- Proof comment: on the bounded-path event, the clipped and unclipped deterministic cutoffs
  -- agree on `[0, T]`, so their canonical fixed-time values coincide.
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_of_eqOn_Icc_local
      (μ := μ) (ℱ := ℱ) (M := M)
      hM
      (T := T)
      (ω := ω)
      (processBeforeStoppingTime_const_eqOn_Icc_of_eqOn_local
        (T := T) (ω := ω)
        (clippedProcess_eqOn_Icc_of_abs_le_local (H := H) (R := R) (T := T) (ω := ω) hbound))

/-- Helper for Exercise 25.2.1: if the coefficient is already bounded by `R` at every left
endpoint contributing to row `row`, then clipping does not change that partition row sum. -/
private lemma partitionPathwiseItoApproximationUpTo_clippedConstCutoff_eq_of_partitionPoint_bounds
    {H : NNReal → Ω → ℝ} {X : PathSpace}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {R T : NNReal} {ω : Ω} {row : ℕ}
    (hbound :
      ∀ k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ R) :
    partitionPathwiseItoApproximationUpTo
        (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
        X
        P
        T
        row =
      partitionPathwiseItoApproximationUpTo
        (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
        X
        P
        T
        row := by
  -- Proof comment: only the left endpoints `P row k` with `k < partitionBoundIndex P row T`
  -- contribute to the truncated row sum, so pointwise clipping identities at those endpoints are
  -- enough for a termwise rewrite.
  rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_lt : k < partitionBoundIndex P row T := Finset.mem_range.mp hk
  have hk_mem :
      P row k ∈ Set.Icc 0 T :=
    partitionPoint_mem_Icc_of_lt_partitionBoundIndex P row k T hk_lt
  have hk_cutoff :
      ((P row k : NNReal) : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast hk_mem.2
  have hclip :
      clippedProcess H R (P row k) ω = H (P row k) ω := by
    exact
      clippedProcess_eq_self_of_abs_le
        (H := H) (R := R) (t := P row k) (ω := ω) (hbound k hk_lt)
  -- Proof comment: after both deterministic cutoffs reduce to evaluation at `P row k`, the row
  -- summands match because clipping is inactive there.
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hk_cutoff]
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hk_cutoff]
  rw [hclip]

/-- Helper for Exercise 25.2.1: if the coefficient is already bounded by `R` on every dyadic left
endpoint below `T`, then clipping does not change the canonical fixed-time Itô value at `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_clippedConstCutoff_value_of_dyadicPoint_bounds
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    {R T : NNReal} {ω : Ω}
    (hbound :
      ∀ row k : ℕ,
        k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
          |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ R) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        T
        ω =
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T
        ω := by
  let X : PathSpace := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  have hRows :
      partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
          X
          Definition2158.dyadicPartitionSequence
          T =
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
          X
          Definition2158.dyadicPartitionSequence
          T := by
    -- Proof comment: every dyadic row uses only dyadic left endpoints below `T`, and the input
    -- hypothesis makes clipping inert at those countably many points.
    funext row
    exact
      partitionPathwiseItoApproximationUpTo_clippedConstCutoff_eq_of_partitionPoint_bounds
        (P := Definition2158.dyadicPartitionSequence)
        (X := X)
        (R := R)
        (T := T)
        (ω := ω)
        (row := row)
        (hbound := hbound row)
  -- Proof comment: the canonical Itô value at time `T` is the `limUnder` of those dyadic rows,
  -- so equality of the full dyadic row family identifies the two fixed-time values.
  rw [continuousLocalMartingaleItoIntegralProcess, continuousLocalMartingaleItoIntegralProcess,
    pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
  exact congrArg (limUnder atTop) hRows

/-- Helper for Exercise 25.2.1(i): almost every sample path of the continuous coefficient is
bounded on the compact interval `Set.Icc 0 T` by some natural clip radius. -/
private lemma ae_existsNatClipRadiusOnIcc
    {H : NNReal → Ω → ℝ}
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (T : NNReal) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ t : NNReal, t ∈ Set.Icc 0 T → |H t ω| ≤ (N : ℝ) := by
  filter_upwards with ω
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : NNReal) T, ‖H t ω‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      (hH_cont ω).continuousOn
  have hceil : C ≤ (Nat.ceil C : ℝ) := by
    exact_mod_cast Nat.le_ceil C
  refine ⟨Nat.ceil C, ?_⟩
  intro t ht
  -- Proof comment: compactness gives a real bound `C`; replacing it by `Nat.ceil C` produces a
  -- countable clip radius without changing the interval-wise bound.
  calc
    |H t ω| = ‖H t ω‖ := by simp [Real.norm_eq_abs]
    _ ≤ C := hC t ht
    _ ≤ (Nat.ceil C : ℝ) := hceil

/-- Helper for Exercise 25.2.1(i): almost every sample path of the continuous coefficient is
bounded on the compact interval `Set.Icc 0 T` by some deterministic clip radius. -/
private lemma ae_existsClipRadiusOnIcc
    {H : NNReal → Ω → ℝ}
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (T : NNReal) :
    ∀ᵐ ω ∂μ, ∃ R : NNReal, ∀ t : NNReal, t ∈ Set.Icc 0 T → |H t ω| ≤ R := by
  filter_upwards [ae_existsNatClipRadiusOnIcc (μ := μ) (H := H) hH_cont T] with ω hω
  rcases hω with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  -- Proof comment: the natural clip radius from the previous lemma is already an `NNReal`
  -- radius after coercion.
  simpa using hN t ht

/-- Helper for Exercise 25.2.1: almost every sample path admits one natural clip radius that
controls both the `P`-row left endpoints below `T` and the dyadic left endpoints below `T`. -/
private lemma ae_existsNatPartitionAndDyadicClipRadius
    {H : NNReal → Ω → ℝ}
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      ∃ N : ℕ,
        (∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)) ∧
        (∀ row k : ℕ,
          k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
            |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal)) := by
  filter_upwards [ae_existsNatClipRadiusOnIcc (μ := μ) (H := H) hH_cont T] with ω hω
  rcases hω with ⟨N, hN⟩
  refine ⟨N, ?_, ?_⟩
  · intro row k hk
    have hk_mem :
        P row k ∈ Set.Icc 0 T :=
      partitionPoint_mem_Icc_of_lt_partitionBoundIndex P row k T hk
    -- Proof comment: every active left endpoint of every `P`-row lies in `[0, T]`, so the
    -- compact-interval bound from `ae_existsNatClipRadiusOnIcc` applies directly.
    simpa using hN (P row k) hk_mem
  · intro row k hk
    have hk_mem :
        Definition2158.dyadicPartitionSequence row k ∈ Set.Icc 0 T :=
      partitionPoint_mem_Icc_of_lt_partitionBoundIndex
        Definition2158.dyadicPartitionSequence row k T hk
    -- Proof comment: the same compact-interval bound also controls the dyadic left endpoints
    -- used in the canonical fixed-time Itô realization.
    simpa using hN (Definition2158.dyadicPartitionSequence row k) hk_mem

/-- Helper for Exercise 25.2.1(i): at the fixed horizon `T`, the canonical Itô value of `H`
agrees almost surely with the canonical Itô value of the deterministic cutoff of `H` at `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_ae_eq_constCutoff_value
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (T : NNReal) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  -- Proof comment: the cutoff and original integrands agree pathwise on `[0, T]`, so the fixed
  -- dyadic Itô value at horizon `T` agrees for every sample point.
  filter_upwards with ω
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM T ω

/-- Helper for Exercise 25.2.1(i): the countable event controlling all active `P`-row and dyadic
left endpoints by one clip radius is measurable. -/
private lemma measurableSet_partitionAndDyadicClipBounds
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (N : ℕ) :
    MeasurableSet
      {ω |
        (∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)) ∧
        (∀ row k : ℕ,
          k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
            |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal))} := by
  have hH_eval_meas : ∀ t : NNReal, Measurable fun ω : Ω ↦ H t ω := by
    intro t
    -- Proof comment: progressive measurability already gives measurability of each time slice.
    exact ((hH_prog.stronglyAdapted t).mono (ℱ.le t)).measurable
  let sP : ℕ → ℕ → Set Ω := fun row k ↦
    if hk : k < partitionBoundIndex P row T then
      {ω | |H (P row k) ω| ≤ (N : NNReal)}
    else
      Set.univ
  let sD : ℕ → ℕ → Set Ω := fun row k ↦
    if hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T then
      {ω | |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal)}
    else
      Set.univ
  have hsP_meas : ∀ row k : ℕ, MeasurableSet (sP row k) := by
    intro row k
    by_cases hk : k < partitionBoundIndex P row T
    · have hmeas :
          Measurable fun ω : Ω ↦ |H (P row k) ω| :=
        (hH_eval_meas (P row k)).abs
      simp [sP, hk, measurableSet_le hmeas measurable_const]
    · simp [sP, hk]
  have hsD_meas : ∀ row k : ℕ, MeasurableSet (sD row k) := by
    intro row k
    by_cases hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T
    · have hmeas :
          Measurable fun ω : Ω ↦ |H (Definition2158.dyadicPartitionSequence row k) ω| :=
        (hH_eval_meas (Definition2158.dyadicPartitionSequence row k)).abs
      simp [sD, hk, measurableSet_le hmeas measurable_const]
    · simp [sD, hk]
  have hP_meas :
      MeasurableSet
        {ω |
          ∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)} := by
    have hInter :
        {ω |
          ∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)} =
          ⋂ row : ℕ, ⋂ k : ℕ, sP row k := by
      ext ω
      simp [sP]
    rw [hInter]
    refine MeasurableSet.iInter ?_
    intro row
    refine MeasurableSet.iInter ?_
    intro k
    exact hsP_meas row k
  have hD_meas :
      MeasurableSet
        {ω |
          ∀ row k : ℕ,
            k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
              |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal)} := by
    have hInter :
        {ω |
          ∀ row k : ℕ,
            k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
              |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal)} =
          ⋂ row : ℕ, ⋂ k : ℕ, sD row k := by
      ext ω
      simp [sD]
    rw [hInter]
    refine MeasurableSet.iInter ?_
    intro row
    refine MeasurableSet.iInter ?_
    intro k
    exact hsD_meas row k
  -- Proof comment: both countable endpoint-bound conditions are measurable separately, so their
  -- conjunction is measurable as an intersection.
  simpa [Set.setOf_and] using hP_meas.inter hD_meas

/-- Helper for Exercise 25.2.1(i): enlarging the clip radius preserves the endpoint-bound event
that controls all active `P`-row and dyadic left endpoints. -/
private lemma partitionAndDyadicClipBounds_mono
    {H : NNReal → Ω → ℝ}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    Monotone
      (fun N : ℕ ↦
        {ω |
          (∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)) ∧
          (∀ row k : ℕ,
            k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
              |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal))}) := by
  intro N M hNM ω hω
  rcases hω with ⟨hP, hD⟩
  have hNM' : (N : NNReal) ≤ (M : NNReal) := by
    exact_mod_cast hNM
  refine ⟨?_, ?_⟩
  · intro row k hk
    -- Proof comment: every endpoint bound for radius `N` remains valid after enlarging the
    -- radius to `M`.
    exact le_trans (hP row k hk) hNM'
  · intro row k hk
    -- Proof comment: the same monotonicity holds for the dyadic control event.
    exact le_trans (hD row k hk) hNM'

/-- Helper for Exercise 25.2.1(i): finite bracket-density integrability on `[0,T]` upgrades to
all horizons for the deterministically cutoff coefficient at time `T`. -/
private lemma processBeforeStoppingTime_const_integrableOn_bracketDensity_allHorizons_local
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∀ U : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦
          (processBeforeStoppingTime H
              (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
            (squareVariationDensity hbr s.toNNReal ω : ℝ))
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
  intro U
  filter_upwards [hH_sq] with ω hω
  let g : ℝ → ℝ := fun s ↦
    (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
      (squareVariationDensity hbr s.toNNReal ω : ℝ)
  have hBase : IntegrableOn g (Set.Icc (0 : ℝ) (T : ℝ)) := by
    -- Proof comment: on `[0,T]`, the deterministic cutoff leaves `H` unchanged pointwise.
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le : s.toNNReal ≤ T := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast hs_toNNReal_le
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs_cutoff]
  have hCut : IntegrableOn g (Set.Icc (0 : ℝ) (U : ℝ)) := by
    -- Proof comment: outside `[0,T]`, the deterministic cutoff is identically zero.
    refine IntegrableOn.of_forall_diff_eq_zero hBase measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le : ¬ s ≤ T := by
      intro hs_le
      exact hs.2 ⟨hs_nonneg, hs_le⟩
    have hs_not_cutoff :
        ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      intro hs_cutoff
      have hs_toNNReal_le : s.toNNReal ≤ T := by
        exact_mod_cast hs_cutoff
      have hs_le : s ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le
      exact hs_not_le hs_le
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs_not_cutoff]
    simp
  exact hCut

/-- Helper for Exercise 25.2.1(i): deterministic cutoff at time `T` preserves the finite
bracket-energy package needed by the fixed-horizon owner route. -/
private lemma processBeforeStoppingTime_const_hasFiniteBracketEnergy_local
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    HasFiniteBracketEnergy hbr
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: deterministic stopping preserves progressive measurability.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        (Ω := Ω) (ℱ := ℱ) (H := H) hH_prog (isStoppingTime_const ℱ T)
  · -- Proof comment: the preceding cutoff lemma upgrades the single finite-horizon integrability
    -- hypothesis to all horizons for the stopped coefficient.
    intro U
    exact
      processBeforeStoppingTime_const_integrableOn_bracketDensity_allHorizons_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hbr T hH_sq U

/-- Helper for Exercise 25.2.1(i): stopping a finite-bracket-energy integrand at a random time
bounded by `T` preserves finite bracket energy. -/
private lemma processBeforeStoppingTime_hasFiniteBracketEnergy_of_le_const
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    {β : Ω → ENNReal} (hβ : IsStoppingTime ℱ β)
    (T : NNReal)
    (hβ_le : ∀ ω : Ω, β ω ≤ (T : ENNReal)) :
    HasFiniteBracketEnergy hbr (processBeforeStoppingTime H β) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: stopping at a stopping time preserves progressive measurability.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        (Ω := Ω) (ℱ := ℱ) (H := H) hFiniteEnergy.1 hβ
  · intro U
    filter_upwards [hFiniteEnergy.2 T] with ω hω
    let f : ℝ → ℝ := fun s ↦
      (H s.toNNReal ω) ^ 2 *
        (squareVariationDensity hbr s.toNNReal ω : ℝ)
    let g : ℝ → ℝ := fun s ↦
      (processBeforeStoppingTime H β s.toNNReal ω) ^ 2 *
        (squareVariationDensity hbr s.toNNReal ω : ℝ)
    let S : Set ℝ := Set.Iic (β ω).toReal
    have hβ_fin : β ω < ∞ := by
      exact lt_of_le_of_lt (hβ_le ω) (by simp)
    have hBase :
        IntegrableOn g (Set.Icc (0 : ℝ) (T : ℝ)) := by
      have hIndicator :
          IntegrableOn (Set.indicator S f) (Set.Icc (0 : ℝ) (T : ℝ)) := by
        exact hω.indicator measurableSet_Iic
      refine hIndicator.congr_fun ?_ measurableSet_Icc
      intro s hs
      have hs_nonneg : 0 ≤ s := hs.1
      by_cases hsβ_real : s ≤ (β ω).toReal
      · have hs_cutoff :
            (((s.toNNReal : NNReal) : ENNReal) ≤ β ω) := by
          have hs_toNNReal_le : s.toNNReal ≤ (β ω).toNNReal := by
            exact (Real.toNNReal_le_iff_le_coe).2 hsβ_real
          have hs_cast :
              (((s.toNNReal : NNReal) : ENNReal) : ENNReal) ≤
                (((β ω).toNNReal : NNReal) : ENNReal) := by
            exact_mod_cast hs_toNNReal_le
          simpa [ENNReal.coe_toNNReal hβ_fin.ne] using hs_cast
        -- Proof comment: on `[0, T]`, before the random stopping time both integrands agree with
        -- the original bracket-density integrand.
        simp [g, f, S, ProbabilityTheory.processBeforeStoppingTime_apply, hs_cutoff, hsβ_real]
      · have hs_cutoff :
            ¬ (((s.toNNReal : NNReal) : ENNReal) ≤ β ω) := by
          intro hs_cutoff
          have hs_toReal :
              (((s.toNNReal : NNReal) : ENNReal)).toReal ≤ (β ω).toReal :=
            (ENNReal.toReal_le_toReal (by simp) (ne_of_lt hβ_fin)).2 hs_cutoff
          exact hsβ_real (by simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toReal)
        -- Proof comment: on the same finite horizon, after the random stopping time the stopped
        -- integrand vanishes, exactly as the indicatorized source integrand does.
        simp [g, f, S, ProbabilityTheory.processBeforeStoppingTime_apply, hs_cutoff, hsβ_real]
    refine hBase.of_forall_diff_eq_zero measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_gt_T : (T : ℝ) < s := by
      have hs_not_le_T : ¬ s ≤ (T : ℝ) := by
        intro hs_le_T
        exact hs.2 ⟨hs.1.1, hs_le_T⟩
      exact lt_of_not_ge hs_not_le_T
    have hs_toNNReal_gt_T : T < s.toNNReal := by
      simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_gt_T
    have hs_cutoff :
        ¬ (((s.toNNReal : NNReal) : ENNReal) ≤ β ω) := by
      intro hs_cutoff
      have hs_le_T : s.toNNReal ≤ T := by
        exact_mod_cast (le_trans hs_cutoff (hβ_le ω))
      exact (not_le_of_gt hs_toNNReal_gt_T) hs_le_T
    -- Proof comment: beyond the deterministic bound `T`, the bounded stopped stage is already
    -- zero, so integrability on `[0, U]` reduces to integrability on `[0, T]`.
    simp [g, ProbabilityTheory.processBeforeStoppingTime_apply, hs_cutoff]

/-- Helper for Exercise 25.2.1(i): if each deterministic cutoff of a locally square-integrable
process already lies in the predictable-step closure, the deterministic horizons localize that
same closure property to `∞`. -/
private theorem exists_localizingSequenceToInfinity_of_isLocallySquareIntegrableProcess
    {H : NNReal → Ω → ℝ}
    (_hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H)
    (_hClosure :
      ∀ n : ℕ,
        _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (processBeforeStoppingTime H (fun _ ↦ (n : ENNReal)))) :
    ∃ τSeq : ℕ → Ω → ENNReal,
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ (∞ : ENNReal)) ∧
        ∀ n : ℕ,
          _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
            (processBeforeStoppingTime H (τSeq n)) :=
  ⟨
    fun n _ ↦ (n : ENNReal),
    ⟨
      by
        intro t
        simp
      ,
      fun n ↦ by
        simpa using (isStoppingTime_const ℱ (n : NNReal)),
      Filter.Eventually.of_forall fun _ ↦
        ⟨fun _ _ hmn ↦ Nat.cast_le.2 hmn, ENNReal.tendsto_nat_nhds_top⟩
    ⟩,
    _hClosure
  ⟩

/-- Helper for Exercise 25.2.1(i): the deterministic horizons `T + n` form a stopping-time
approximation to `∞`. -/
private def deterministicConstCutoffLocalizingSeq
    (T : NNReal) : ℕ → Ω → ENNReal :=
  fun n _ ↦ ((T + n : NNReal) : ENNReal)

/-- Helper for Exercise 25.2.1(i): the deterministic localizing sequence `T + n` is increasing
and tends pointwise to `∞`. -/
private lemma deterministicConstCutoffLocalizingSeq_isStoppingTimeApproximation
    (T : NNReal) :
    IsStoppingTimeApproximationUpTo ℱ μ
      (deterministicConstCutoffLocalizingSeq (Ω := Ω) T)
      (fun _ ↦ (∞ : ENNReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the event `{∞ ≤ t}` is empty for every deterministic finite horizon `t`.
    intro t
    simp
  · intro n
    -- Proof comment: every deterministic horizon `T + n` is itself a stopping time.
    simpa [deterministicConstCutoffLocalizingSeq] using
      (isStoppingTime_const ℱ (T + n : NNReal))
  · filter_upwards with ω
    refine ⟨?_, ?_⟩
    · intro a b hab
      -- Proof comment: the deterministic horizons inherit monotonicity from the natural numbers.
      have hcast :
          (((T + a : NNReal) : ENNReal) ≤ ((T + b : NNReal) : ENNReal)) := by
        have hab' : (((a : NNReal) : ENNReal) ≤ (b : ENNReal)) := by
          exact_mod_cast hab
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hab' (T : ENNReal)
      simpa [deterministicConstCutoffLocalizingSeq] using hcast
    · have hconst :
          Tendsto (fun _ : ℕ ↦ (T : ENNReal)) atTop (𝓝 (T : ENNReal)) :=
        tendsto_const_nhds
      have hnat :
          Tendsto (fun n : ℕ ↦ (n : ENNReal)) atTop (𝓝 (∞ : ENNReal)) := by
        simpa using ENNReal.tendsto_nat_nhds_top
      -- Proof comment: adding the fixed cutoff horizon `T` does not change divergence to `∞`.
      simpa [deterministicConstCutoffLocalizingSeq, add_comm, add_left_comm, add_assoc] using
        hconst.add hnat

/-- Helper for Exercise 25.2.1(i): cutting off an already deterministically cutoff process at a
later deterministic horizon does not change it. -/
private lemma processBeforeStoppingTime_constCutoff_eq_self_of_le
    {H : NNReal → Ω → ℝ} {T U : NNReal} (hTU : T ≤ U) :
    processBeforeStoppingTime
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (fun _ ↦ (U : ENNReal)) =
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
  funext t ω
  have hTU' : (T : ENNReal) ≤ (U : ENNReal) := by
    exact_mod_cast hTU
  by_cases hU : (t : ENNReal) ≤ (U : ENNReal)
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · -- Proof comment: before the original cutoff time, both deterministic stops return `H t`.
      simp [processBeforeStoppingTime_apply, hU, hT]
    · -- Proof comment: between `T` and `U`, both deterministic stops already vanish.
      simp [processBeforeStoppingTime_apply, hU, hT]
  · have hT : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
      intro ht
      exact hU (le_trans ht hTU')
    -- Proof comment: after the later cutoff time, both sides vanish by definition.
    rw [processBeforeStoppingTime_apply, if_neg hU, processBeforeStoppingTime_apply, if_neg hT]

/-- Helper for Exercise 25.2.1(i): every stage of the deterministic localizing sequence leaves
the cutoff coefficient unchanged. -/
private lemma processBeforeStoppingTime_constCutoff_eq_self_localizingStage
    {H : NNReal → Ω → ℝ} (T : NNReal) (n : ℕ) :
    processBeforeStoppingTime
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (deterministicConstCutoffLocalizingSeq (Ω := Ω) T n) =
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
  have hle : T ≤ T + n := by
    exact le_add_of_nonneg_right (show (0 : NNReal) ≤ (n : NNReal) by positivity)
  simpa [deterministicConstCutoffLocalizingSeq] using
    processBeforeStoppingTime_constCutoff_eq_self_of_le (H := H) (T := T) (U := T + n) hle

/-- Helper for Exercise 25.2.1(i): once the deterministically cutoff coefficient already has
finite textbook `M`-norm, the deterministic horizons `T + n` form an Itô localizing sequence
for that cutoff process. -/
private lemma deterministicConstCutoffLocalizingSeq_isItoLocalizingSequence_of_hasFiniteItoIntegrandNorm
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hCutNorm :
      HasFiniteItoIntegrandNorm M hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))) :
    IsItoLocalizingSequence M hbr
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (fun n _ ↦ T + n) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the deterministic sequence `T + n` already gives the stopping-time
    -- approximation part of the Chapter 25.21 interface.
    simpa [deterministicConstCutoffLocalizingSeq] using
      deterministicConstCutoffLocalizingSeq_isStoppingTimeApproximation
        (Ω := Ω) (ℱ := ℱ) (μ := μ) T
  · intro n
    -- Proof comment: stopping the already cutoff coefficient at a later deterministic horizon
    -- does not change the integrand, so the same finite `M`-norm witness works for every stage.
    have hEq :
        processBeforeStoppingTime
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          (fun _ ↦ ((T + n : NNReal) : ENNReal)) =
        processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
      have hle : T ≤ T + n := by
        exact le_add_of_nonneg_right (show (0 : NNReal) ≤ (n : NNReal) by positivity)
      exact
        processBeforeStoppingTime_constCutoff_eq_self_of_le
          (Ω := Ω) (H := H) (T := T) (U := T + n) hle
    rw [hEq]
    exact hCutNorm

/-- Helper for Exercise 25.2.1(i): any predictable-simple approximation of the deterministically
cutoff coefficient also approximates every later deterministic localization stage of that same
cutoff coefficient. -/
private lemma constCutoffLocalizingStage_isPredictableSimpleItoApproximation
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    (T : NNReal)
    (hHs :
      IsPredictableSimpleItoApproximation M hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        Hs)
    (n : ℕ) :
    IsPredictableSimpleItoApproximation M hbr
      (processBeforeStoppingTime
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        (fun _ ↦ ((T + n : NNReal) : ENNReal)))
      Hs := by
  -- Proof comment: every deterministic localization stage is the same cutoff target, so the
  -- approximation family can be reused without any new analytic work.
  have hEq :
      processBeforeStoppingTime
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        (fun _ ↦ ((T + n : NNReal) : ENNReal)) =
      processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
    have hle : T ≤ T + n := by
      exact le_add_of_nonneg_right (show (0 : NNReal) ≤ (n : NNReal) by positivity)
    exact
      processBeforeStoppingTime_constCutoff_eq_self_of_le
        (Ω := Ω) (H := H) (T := T) (U := T + n) hle
  rw [hEq]
  exact hHs

/-- Helper for Exercise 25.2.1(i): if one row sequence converges in measure to a family of outer
limits and also to one common target, then each outer limit agrees almost everywhere with that
common target. -/
private lemma rowLimit_aeEq_of_constantApproximationFamily
    {f : ℕ → Ω → ℝ} {rowLimit : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hRows : ∀ n : ℕ, TendstoInMeasure μ f atTop (rowLimit n))
    (hTarget : TendstoInMeasure μ f atTop g) :
    ∀ n : ℕ, rowLimit n =ᵐ[μ] g := by
  intro n
  -- Proof comment: convergence in measure has an almost-everywhere unique limit, so the common
  -- inner row sequence identifies each outer limit with the same target.
  exact MeasureTheory.tendstoInMeasure_ae_unique (hRows n) hTarget

/-- Helper for Exercise 25.2.1(i): the outer limits produced from one constant approximation
family are pairwise almost everywhere equal. -/
private lemma rowLimit_pairwise_aeEq_of_constantApproximationFamily
    {f : ℕ → Ω → ℝ} {rowLimit : ℕ → Ω → ℝ}
    (hRows : ∀ n : ℕ, TendstoInMeasure μ f atTop (rowLimit n)) :
    ∀ n m : ℕ, rowLimit n =ᵐ[μ] rowLimit m := by
  intro n m
  -- Proof comment: both limits come from the same inner sequence, so the previous uniqueness
  -- bridge identifies them by comparing each one to the other's convergence statement.
  exact MeasureTheory.tendstoInMeasure_ae_unique (hRows n) (hRows m)

/-- Helper for Exercise 25.2.1(i): once the deterministically cutoff integrand has a source-side
double-approximation formula, any one constant predictable-simple approximation family already
converges in measure at the fixed horizon `T` to the canonical cutoff Itô value. -/
private theorem constCutoffApproximation_tendstoInMeasure_of_sourceApprox_local
    {M H N : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hApprox :
      HasApproximationFormula hM hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        N)
    (hOwner :
      IsContinuousLocalMartingaleItoIntegralSourceOwner
        (hM := hM)
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        N)
    (hCutNorm :
      HasFiniteItoIntegrandNorm M hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))))
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    (hHs :
      IsPredictableSimpleItoApproximation M hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        Hs) :
    TendstoInMeasure μ
      (fun m ω ↦
        continuousLocalMartingaleItoIntegralProcess hM
          (Hs m : NNReal → Ω → ℝ)
          T
          ω)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T) := by
  let τSeq : ℕ → Ω → NNReal := fun n _ ↦ T + n
  have hτ :
      IsItoLocalizingSequence M hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        τSeq := by
    -- Proof comment: the deterministic horizons `T + n` localize the already cutoff integrand
    -- because every later cutoff stage is literally the same process.
    simpa [τSeq] using
      deterministicConstCutoffLocalizingSeq_isItoLocalizingSequence_of_hasFiniteItoIntegrandNorm
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hbr T hCutNorm
  have hStage :
      ∀ n : ℕ,
        IsPredictableSimpleItoApproximation M hbr
          (processBeforeStoppingTime
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            (fun _ ↦ (((T + n : NNReal) : ENNReal))))
          Hs := by
    intro n
    -- Proof comment: the outer approximation formula only sees deterministic localizing stages of
    -- the cutoff integrand, and those stages are unchanged for the family `Hs`.
    exact
      constCutoffLocalizingStage_isPredictableSimpleItoApproximation
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr T hHs n
  rcases hApprox τSeq hτ (fun _ ↦ Hs) hStage T with ⟨rowLimit, hOuter, hRows⟩
  have hRowLimitEq :
      rowLimit 0 =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T := by
    have hEqToOwner :
        rowLimit 0 =ᵐ[μ] N T :=
      rowLimit_aeEq_of_constantApproximationFamily
        (μ := μ) (hRows := hRows) (hTarget := hOuter) 0
    have hOwnerEq :
        N T =ᵐ[μ]
          continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            T :=
      sourceOwner_aeEq_canonicalAtFixedTime
        (μ := μ) (ℱ := ℱ)
        (M := M)
        (H := processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        (N := N)
        hOwner
        T
    -- Proof comment: the constant-family row limits all identify with the owner value `N T`,
    -- and the source-owner clause then rewrites that owner value to the canonical cutoff target.
    exact hEqToOwner.trans hOwnerEq
  -- Proof comment: after collapsing the constant outer family, the `n = 0` inner convergence is
  -- already the desired fixed-horizon limit for the common predictable-simple sequence `Hs`.
  exact TendstoInMeasure.congr_right hRowLimitEq (hRows 0)

/-- Helper for Exercise 25.2.1(i): stopping the deterministic cutoff `H 1_[0,T]` once more at a
random time `τ` is the same as stopping `H` directly at the pointwise minimum `min τ T`. -/
private lemma processBeforeStoppingTime_constCutoff_eq_min
    {H : NNReal → Ω → ℝ}
    (T : NNReal) (τ : Ω → ENNReal) :
    processBeforeStoppingTime
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        τ =
      processBeforeStoppingTime H (fun ω ↦ min (τ ω) (T : ENNReal)) := by
  -- Proof comment: both sides keep `H t ω` exactly on the branch where the time lies below both
  -- the random horizon `τ ω` and the deterministic cutoff `T`.
  funext t ω
  by_cases hτ : (t : ENNReal) ≤ τ ω
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτ, hT, le_min_iff]
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτ, hT, le_min_iff]
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτ, hT, le_min_iff]
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτ, hT, le_min_iff]

/-- Helper for Exercise 25.2.1(i): once the deterministically cutoff partition sums converge in
measure to the deterministically cutoff canonical Itô value at the same horizon, the two cutoff
identifications transport that convergence back to the original integrand `H`. -/
private theorem tendstoInMeasure_partitionItoApproximationUpTo_of_constCutoff
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal)
    (hCut :
      TendstoInMeasure μ
        (fun n ω ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            n)
        atTop
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T)) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM H T) := by
  have hSeqEq :
      ∀ n : ℕ,
        (fun ω ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            n) =
          (fun ω ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              T
              n) := by
    intro n
    -- Proof comment: the deterministic cutoff agrees pointwise with `H` on the active partition
    -- row up to the same terminal horizon `T`.
    funext ω
    exact partitionPathwiseItoApproximationUpTo_constCutoff_eq
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P T ω n
  have hTargetEq :
      continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T :=
    continuousLocalMartingaleItoIntegralProcess_ae_eq_constCutoff_value
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM T
  -- Proof comment: first rewrite the approximating sequence termwise, then transport the limit
  -- across the fixed-time almost-sure cutoff identification.
  exact
    TendstoInMeasure.congr_right hTargetEq <|
      TendstoInMeasure.congr_left
        (fun n ↦ Filter.EventuallyEq.of_eq (hSeqEq n))
        hCut

/-- Helper for Exercise 25.2.1(i): the clipped deterministic-cutoff partition rows already
converge in `PredictableSimpleProcessL2Closure ℱ μ` to the deterministically stopped clipped
integrand. -/
private lemma clippedConstCutoffPartitionRowsTendstoToClosure
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    Tendsto
      (fun row ↦ clippedConstCutoffPartitionRowClosure
        (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T)
      atTop
      (nhds
        (clippedConstCutoffTargetClosure
          (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont R T)) := by
  let Hcut : NNReal → Ω → ℝ :=
    processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal))
  let Krow : ℕ → NNReal → Ω → ℝ := fun row ↦
    ((clippedConstCutoffPartitionRowRepresentation
        (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
        NNReal → Ω → ℝ)
  have hHcut_prog : ProgMeasurable ℱ Hcut := by
    -- Proof comment: deterministic stopping preserves progressive measurability of the clipped
    -- coefficient.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        (clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont)
        (isStoppingTime_const ℱ T)
  let hTargetClosure : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ Hcut :=
    MeasureTheory.progMeasurable_memPredictableStepProcessClosure
      ℱ
      μ
      hHcut_prog
      (clippedConstCutoff_memLp (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont R T)
  let hRowClosure :
      ∀ row : ℕ, _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ (Krow row) := fun row =>
    clippedConstCutoffPartitionRow_memPredictableStepProcessClosure
      (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T
  let hRowMemLp :
      ∀ row : ℕ,
        MemLp (MeasureTheory.processToTimeSpaceFun (Krow row)) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ) := fun row => by
    rcases hRowClosure row with ⟨hMem, _⟩
    exact hMem
  let hTargetMemLp :
      MemLp (MeasureTheory.processToTimeSpaceFun Hcut) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ) := by
    rcases hTargetClosure with ⟨hMem, _⟩
    exact hMem
  have hTwo_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hTwo_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hTwo_pos : 0 < (2 : ℝ) := by norm_num
  have hIntegral :
      Tendsto
        (fun row ↦
          ∫⁻ x,
            ‖(MeasureTheory.processToTimeSpaceFun (Krow row) -
                MeasureTheory.processToTimeSpaceFun Hcut) x‖ₑ ^ (2 : ℝ) ∂
              MeasureTheory.processMeasure μ)
        atTop
        (𝓝 0) := by
    -- Proof comment: the already proved global stripwise square-error theorem is exactly the
    -- ambient second-moment convergence needed for the closure limit.
    simpa [Hcut, Krow] using
      (globalLintegral_sqDiff_clippedConstCutoffPartitionRow_tendsto_zero
        (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P R T)
  have hELpNorm :
      Tendsto
        (fun row ↦
          eLpNorm
            (MeasureTheory.processToTimeSpaceFun (Krow row) -
              MeasureTheory.processToTimeSpaceFun Hcut)
            (2 : ℝ≥0∞)
            (MeasureTheory.processMeasure μ))
        atTop
        (𝓝 0) := by
    -- Proof comment: for `p = 2`, vanishing of the square integral is exactly vanishing of the
    -- ambient `L²(processMeasure μ)` distance.
    simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hTwo_ne_zero hTwo_ne_top]
    convert (ENNReal.continuous_rpow_const.tendsto (0 : ℝ≥0∞)).comp hIntegral
    simp
  have hAmbient :
      Tendsto
        (fun row ↦
          ((hRowMemLp row).toLp
            (MeasureTheory.processToTimeSpaceFun (Krow row)) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)))
        atTop
        (nhds
          ((hTargetMemLp.toLp
              (MeasureTheory.processToTimeSpaceFun Hcut)) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ))) := by
    -- Proof comment: package the vanishing `L²` distance as convergence in the ambient `Lp`
    -- space before lifting back to the realized closure subtype.
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun row ↦ MeasureTheory.processToTimeSpaceFun (Krow row))
        (fun row ↦ hRowMemLp row)
        (MeasureTheory.processToTimeSpaceFun Hcut)
        hTargetMemLp).2 hELpNorm
  refine tendsto_subtype_rng.2 ?_
  -- Proof comment: coercing both closure points to ambient `L²(processMeasure μ)` recovers the
  -- exact `Lp` classes from the previous step.
  simpa [clippedConstCutoffPartitionRowClosure, clippedConstCutoffTargetClosure,
    MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure] using
    hAmbient

/-- Helper for Exercise 25.2.1(i): a Brownian-side truncation slice at `T` is the terminal
Brownian-Itô class of the deterministically cut off closure point. -/
private theorem brownianTruncatedClosure_ae_eq_constCutoffTerminal_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
      (M := M)
      (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem) T =ᵐ[μ]
      hIto.toContinuousLinearMap (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) := by
  -- Proof comment: this is exactly the deterministic-cutoff normalization from Lemma 25.13,
  -- rewritten through the local `constCutoffClosure` abbreviation.
  simpa [constCutoffClosure] using
    (deterministicCutoffTerminal_eq_truncated_local
      (μ := μ) (ℱ := ℱ) (W := M) (hH := hH_mem) T).symm

/-- Helper for Exercise 25.2.1: if an admissible integrand already vanishes after `T`, then its
terminal Brownian-Itô class agrees almost everywhere with its Brownian truncation slice at time
`T`. -/
private theorem terminalBrownianIto_eq_truncated_of_vanishesAfter_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → H u ω = 0) :
    hIto.toContinuousLinearMap
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem) =ᵐ[μ]
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem) T := by
  let hCut_mem :
      _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
      (μ := μ) (ℱ := ℱ) hH_mem T
  have hDet :
      hIto.toContinuousLinearMap
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hCut_mem) =ᵐ[μ]
        BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem) T :=
    deterministicCutoffTerminal_eq_truncated_local
      (μ := μ) (ℱ := ℱ) (W := M) hH_mem T
  have hProcessEq :
      processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) = H := by
    funext u ω
    by_cases huT : (u : ENNReal) ≤ (T : ENNReal)
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, huT]
    · have hTu : T < u := ENNReal.coe_lt_coe.mp (lt_of_not_ge huT)
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, huT, hzero hTu]
  have hClosureEq :
      _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hCut_mem =
        _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem := by
    apply Subtype.ext
    apply Lp.ext
    have hLeft :=
        MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure hCut_mem
    have hRight :=
        MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure hH_mem
    -- Proof comment: once the deterministic cutoff leaves the integrand unchanged, both closure
    -- representatives are the same ambient `L²(processMeasure μ)` class.
    simpa [hProcessEq] using hLeft.trans hRight.symm
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hCut_mem) =
        hIto.toContinuousLinearMap
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem) := by
    exact congrArg hIto.toContinuousLinearMap hClosureEq
  -- Proof comment: normalize the already supported integrand back from its deterministic cutoff,
  -- then apply the fixed-time terminal-vs-truncation identity for the original closure point.
  exact (Filter.EventuallyEq.of_eq hTerminalEq).symm.trans hDet

/-- Helper for Exercise 25.2.1(i): the remaining fixed-time bridge is to compare the Brownian
truncation slice of the deterministically stopped closure point with the canonical dyadic Itô
value at the same horizon. -/
private theorem constCutoffTerminal_ae_eq_truncatedAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    hIto.toContinuousLinearMap (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T)
        T := by
  let hHcut_mem :
      _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hH_mem T
  -- Proof comment: the deterministic cutoff integrand already vanishes after `T`, so its
  -- terminal Brownian-Itô class coincides with its own time-`T` truncation slice.
  exact
    terminalBrownianIto_eq_truncated_of_vanishesAfter_local
      (μ := μ) (ℱ := ℱ) (M := M) hHcut_mem
      (T := T)
      (fun {_u} {_ω} hu ↦
        processBeforeStoppingTime_apply_eq_zero_of_lt
          (H := H)
          (β := fun _ ↦ (T : ENNReal))
          (t := _u)
          (ω := _ω)
          (by exact_mod_cast hu))

/-- Helper for Exercise 25.2.1: the deterministic cutoff of a globally square-integrable
predictable simple stage stays in `L²(processMeasure μ)`. -/
private theorem predictableSimpleCutoffBefore_memLp_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (((ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
            MeasureTheory.PredictableSimpleProcess ℱ) : NNReal → Ω → ℝ)))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  let hCutMem :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
            (K : NNReal → Ω → ℝ)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae
      (Filter.EventuallyEq.of_eq
        (BrownianItoIntegral.processToTimeSpaceFun_cutoffBeforeDeterministicTime_local
          T (K : NNReal → Ω → ℝ)).symm)).mp <|
      MeasureTheory.MemLp.indicator
        (show MeasurableSet ({x : Ω × ℝ | x.2 ≤ (T : ℝ)}) from
          measurableSet_le measurable_snd measurable_const)
        hK
  -- Proof comment: the explicit predictable-simple cutoff is just the deterministic strip cutoff
  -- of the original stage, so its ambient `L²(μ ⊗ dt)` bound is inherited verbatim.
  exact
    (memLp_congr_ae (Filter.EventuallyEq.of_eq <| by
      simpa using
        congrArg MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
            K T).symm)).mp hCutMem

/-- Helper for Exercise 25.2.1: the closure-side deterministic cutoff of a predictable simple
stage is the explicit predictable-simple cutoff object from Theorem 25.11. -/
private theorem predictableSimpleCutoffBefore_toClosure_eq_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    let hKstage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (K : NNReal → Ω → ℝ) :=
      ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩
    let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
    let hKcut :
        MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ) :=
      predictableSimpleCutoffBefore_memLp_local (μ := μ) (ℱ := ℱ) K hK T
    MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T) =
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
  let hKstage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (K : NNReal → Ω → ℝ) :=
    ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩
  let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
    ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
  let hKcut :
      MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ) :=
    predictableSimpleCutoffBefore_memLp_local (μ := μ) (ℱ := ℱ) K hK T
  -- Proof comment: normalize the closure-side deterministic cutoff through the public cutoff
  -- operator, then identify that cutoff with the explicit predictable-simple cutoff stage.
  calc
    MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T) =
        MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore T
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hKstage) := by
          symm
          simpa using
            MeasureTheory.MemPredictableStepProcessClosure.cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst
              (Ω := Ω) (ℱ := ℱ) (μ := μ) (H := (K : NNReal → Ω → ℝ)) hKstage T
    _ =
        ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
          simpa [Kcut, hKcut] using
            ProbabilityTheory.BrownianItoIntegral.cutoffBefore_predictableSimpleClosure_eq_local
              K hK T

/-- Helper for Exercise 25.2.1: a predictable-simple stage already identifies its fixed-time
Brownian elementary value with the terminal Brownian-Itô class of its deterministic cutoff. -/
private theorem predictableSimpleCutoff_terminal_ae_eq_brownianIntegral_local
    {M : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    let hKstage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (K : NNReal → Ω → ℝ) :=
      ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩
    MeasureTheory.brownianElementaryIntegral M K T =ᵐ[μ]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            hKstage T)) := by
  let hKstage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (K : NNReal → Ω → ℝ) :=
    ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩
  let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
    ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
  let hKcut :
      MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ) :=
    predictableSimpleCutoffBefore_memLp_local (μ := μ) (ℱ := ℱ) K hK T
  have hBrownianCutoff :
      MeasureTheory.brownianElementaryIntegral M K T =
        MeasureTheory.brownianElementaryIntegralAtInfinity M Kcut := by
    -- Proof comment: the finite-time elementary integral of `K` is exactly the terminal
    -- Brownian integral of the explicit deterministic cutoff stage `K · 1_[0,T]`.
    simpa [Kcut] using
      ProbabilityTheory.BrownianItoIntegral.brownianElementaryIntegral_predictableSimple_eq_cutoffTerminal_local
        (W := M) K T
  have hClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            hKstage T) =
        ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
    -- Proof comment: the deterministic cutoff closure point is the same `L²(μ ⊗ dt)` class as
    -- the explicit predictable-simple cutoff stage.
    calc
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            hKstage T) =
          MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore T
            (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hKstage) := by
              symm
              simpa using
                MeasureTheory.MemPredictableStepProcessClosure.cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst
                  (Ω := Ω) (ℱ := ℱ) (μ := μ) (H := (K : NNReal → Ω → ℝ)) hKstage T
      _ = ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
            simpa [Kcut, hKcut] using
              ProbabilityTheory.BrownianItoIntegral.cutoffBefore_predictableSimpleClosure_eq_local
                K hK T
  have hTerminalCutoff :
      hIto.toContinuousLinearMap
          (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut) =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegralAtInfinity M Kcut := by
    -- Proof comment: the Brownian-Itô terminal map agrees almost everywhere with the terminal
    -- Brownian elementary integral on every globally square-integrable predictable simple stage.
    simpa [Kcut,
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure] using
      hIto.ae_eq_brownianElementaryIntegralAtInfinity Kcut hKcut
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage T)) =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegralAtInfinity M Kcut := by
    -- Proof comment: rewrite the terminal Brownian-Itô map through the closure identification of
    -- the deterministic cutoff stage.
    exact (Filter.EventuallyEq.of_eq (congrArg hIto.toContinuousLinearMap hClosureEq)).trans
      hTerminalCutoff
  -- Proof comment: both sides are now normalized to the same terminal Brownian integral of the
  -- deterministic cutoff stage.
  exact (Filter.EventuallyEq.of_eq hBrownianCutoff).trans hTerminalEq.symm

/-- Helper for Exercise 25.2.1: on a predictable-simple stage, the canonical fixed-time value of
its deterministic cutoff should already agree almost everywhere with the Brownian elementary
integral at the same horizon. -/
private theorem predictableSimpleConstCutoffCanonicalValue_ae_eq_brownianIntegral_local
    {M : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : NNReal → Ω → ℝ))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    (fun ω ↦
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
        T
        ω) =ᵐ[μ]
      MeasureTheory.brownianElementaryIntegral M K T := by
  let hKstage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (K : NNReal → Ω → ℝ) :=
    ⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩
  have hBrownianTerminal :
      MeasureTheory.brownianElementaryIntegral M K T =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage T)) := by
    -- Proof comment: the Brownian side is already normalized by the deterministic-cutoff
    -- terminal identity for predictable simple stages.
    simpa [hKstage] using
      predictableSimpleCutoff_terminal_ae_eq_brownianIntegral_local
        (μ := μ) (ℱ := ℱ) (M := M) K hK T
  have hCutoffCanonical :
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
          T
          ω) =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage T)) := by
    let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
    let hKcut :
        MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : NNReal → Ω → ℝ)) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ) :=
      predictableSimpleCutoffBefore_memLp_local (μ := μ) (ℱ := ℱ) K hK T
    have hProcessEq :
        processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)) =
          (Kcut : NNReal → Ω → ℝ) := by
      -- Proof comment: switch once to the explicit predictable-simple cutoff object and keep the
      -- rest of the transport in that spelling world.
      funext u ω
      by_cases hu : u ≤ T
      · have hcut :
            ((Kcut : NNReal → Ω → ℝ) u ω) =
              ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                (K : NNReal → Ω → ℝ) u ω := by
          simpa [Kcut] using
            congrArg (fun X : NNReal → Ω → ℝ ↦ X u ω)
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
                K T)
        have hu' : (u : ENNReal) ≤ (T : ENNReal) := by
          exact_mod_cast hu
        calc
          processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)) u ω
              = (K : NNReal → Ω → ℝ) u ω := by
                  simp [ProbabilityTheory.processBeforeStoppingTime_apply, hu']
          _ = ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                (K : NNReal → Ω → ℝ) u ω := by
                  simp [ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local,
                    hu]
          _ = (Kcut : NNReal → Ω → ℝ) u ω := by
                simpa [Kcut] using hcut.symm
      · have hcut :
            ((Kcut : NNReal → Ω → ℝ) u ω) =
              ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                (K : NNReal → Ω → ℝ) u ω := by
          simpa [Kcut] using
            congrArg (fun X : NNReal → Ω → ℝ ↦ X u ω)
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
                K T)
        have hu' : ¬ (u : ENNReal) ≤ (T : ENNReal) := by
          exact fun h => hu (by exact_mod_cast h)
        calc
          processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)) u ω
              = 0 := by
                  simp [ProbabilityTheory.processBeforeStoppingTime_apply, hu']
          _ = ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                (K : NNReal → Ω → ℝ) u ω := by
                  simp [ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local,
                    hu]
          _ = (Kcut : NNReal → Ω → ℝ) u ω := by
                simpa [Kcut] using hcut.symm
    have hClosureEq :
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage T) =
          ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
      -- Proof comment: the closure-side deterministic cutoff of `K` is the canonical closure
      -- point attached to the explicit predictable-simple cutoff stage.
      calc
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage T) =
            MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore T
              (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hKstage) := by
                symm
                simpa using
                  MeasureTheory.MemPredictableStepProcessClosure.cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst
                    (Ω := Ω) (ℱ := ℱ) (μ := μ) (H := (K : NNReal → Ω → ℝ)) hKstage T
        _ = ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut := by
              simpa [Kcut, hKcut] using
                ProbabilityTheory.BrownianItoIntegral.cutoffBefore_predictableSimpleClosure_eq_local
                  K hK T
    have hExplicitCutoff :
        (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Kcut : NNReal → Ω → ℝ) T ω) =ᵐ[μ]
          hIto.toContinuousLinearMap
            (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut) := by
      let hKcut_stage : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (Kcut : NNReal → Ω → ℝ) :=
        ⟨hKcut, (MeasureTheory.predictableSimpleProcessToClosureLocal Kcut hKcut).2⟩
      have hKcut_prog : ProgMeasurable ℱ (Kcut : NNReal → Ω → ℝ) := by
        -- Proof comment: every predictable simple process is progressively measurable.
        exact (PredictableSimpleProcess.isPredictable Kcut).progMeasurable
      have hKcut_zero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (Kcut : NNReal → Ω → ℝ) u ω = 0 := by
        intro u ω hu
        -- Proof comment: the explicit cutoff stage is literally the deterministic stopping of
        -- `K`, so it vanishes on every time strictly beyond `T`.
        have hcut :
            ((Kcut : NNReal → Ω → ℝ) u ω) =
              ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                (K : NNReal → Ω → ℝ) u ω := by
          simpa [Kcut] using
            congrArg (fun X : NNReal → Ω → ℝ ↦ X u ω)
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
                K T)
        have hnot : ¬ u ≤ T := not_le_of_gt hu
        calc
          (Kcut : NNReal → Ω → ℝ) u ω
              = ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
                  (K : NNReal → Ω → ℝ) u ω := hcut
          _ = 0 := by
                simp [ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local,
                  hnot]
      have hTruncatedCanonical :
          BrownianItoIntegral.brownianItoIntegralTruncatedProcess
              (M := M)
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut)
              T =ᵐ[μ]
            (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Kcut : NNReal → Ω → ℝ) T ω) := by
        exact
          brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
            (μ := μ) (ℱ := ℱ) (M := M) (H := (Kcut : NNReal → Ω → ℝ))
            hM hKcut_prog hKcut_stage T
      have hTerminalTruncated :
          hIto.toContinuousLinearMap
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut) =ᵐ[μ]
            BrownianItoIntegral.brownianItoIntegralTruncatedProcess
              (M := M)
              (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessClosure Kcut hKcut)
              T := by
        exact
          terminalBrownianIto_eq_truncated_of_vanishesAfter_local
            (μ := μ) (ℱ := ℱ) (M := M) (H := (Kcut : NNReal → Ω → ℝ))
            hKcut_stage
            (T := T)
            (fun {_u} {_ω} hu ↦ hKcut_zero hu)
      -- Proof comment: the explicit cutoff stage sits on the common truncation surface, so the
      -- desired canonical-to-terminal bridge is just transitivity there.
      exact hTruncatedCanonical.symm.trans hTerminalTruncated.symm
    have hCanonicalEq :
        (fun ω ↦
          continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
            T
            ω) =ᵐ[μ]
          (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Kcut : NNReal → Ω → ℝ) T ω) := by
      -- Proof comment: after the one-time spelling switch, the deterministic cutoff canonical
      -- value is literally the canonical value of the explicit cutoff stage.
      exact Filter.EventuallyEq.of_eq <| by
        funext ω
        simp [hProcessEq]
    -- Proof comment: all closure transport is now explicit, so the unresolved frontier is the
    -- single explicit-cutoff predictable-simple statement above.
    exact hCanonicalEq.trans <|
      hExplicitCutoff.trans (Filter.EventuallyEq.of_eq (congrArg hIto.toContinuousLinearMap hClosureEq)).symm
  -- Proof comment: once the cutoff canonical value is identified with the terminal Brownian-Itô
  -- class, the Brownian elementary value is the same fixed-time object.
  exact hCutoffCanonical.trans hBrownianTerminal.symm

/-- Helper for Exercise 25.2.1(i): the remaining fixed-time bridge is to compare the Brownian
truncation slice of one closure point directly with the canonical Chapter 25 Itô value at the
same horizon. -/
private theorem constCutoffTerminal_ae_eq_canonicalConstCutoffAtFixedTime_seed_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            hH_mem T)) =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T := by
  -- Route correction: isolate the proof-cycle blocker as a standalone deterministic-cutoff
  -- seed theorem. Once this bridge is available, both the frontier theorem and the predictable-
  -- simple fixed-time wrapper become direct transitivity arguments.
  let hHcut_mem :
      _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hH_mem T
  obtain ⟨Ks, hKs_mem, hKs_tendsto⟩ :=
    MeasureTheory.existsPredictableSimpleApproximationOfClosurePointLocal
      (Ω := Ω) (ℱ := ℱ) (μ := μ)
      (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
  have hBrownian :
      TendstoInMeasure μ
        (fun n ω ↦ MeasureTheory.brownianElementaryIntegral M (Ks n) T ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T) := by
    have hLp :
        TendstoInLp 2 μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral M (Ks n) T)
          (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
            (M := M)
            (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
            T) := by
      -- Proof comment: Brownian fixed-time continuity applies directly to the predictable-simple
      -- approximants of the deterministic-cutoff closure point.
      simpa [BrownianItoIntegral.brownianItoIntegralTruncatedProcess] using
        (BrownianItoIntegral.brownianElementaryIntegral_timeSlice_tendstoInLp_two_local
          (μ := μ)
          (ℱ := ℱ)
          (W := M)
          (H := _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          (Hs := Ks)
          (hHs_mem := hKs_mem)
          (hHs_tendsto := hKs_tendsto)
          (t := T))
    exact MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  have hCommonCutoff :
      TendstoInMeasure μ
        (fun n ω ↦
          continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime (Ks n : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
            T
            ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T) := by
    -- Proof comment: the new predictable-simple cutoff bridge rewrites each stage directly on
    -- the deterministic-cutoff surface before Brownian-side closure continuity is applied.
    refine
      TendstoInMeasure.congr_left
        (fun n ↦
          predictableSimpleConstCutoffCanonicalValue_ae_eq_brownianIntegral_local
            (μ := μ) (ℱ := ℱ) (M := M) hM (Ks n) (hKs_mem n) T)
        hBrownian
  have hCommon :
      TendstoInMeasure μ
        (fun n ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Ks n : NNReal → Ω → ℝ) T ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T) := by
    -- Proof comment: at time `T`, cutting off the predictable-simple stages does not change
    -- their canonical fixed-time values.
    refine TendstoInMeasure.congr_left ?_ hCommonCutoff
    intro n
    filter_upwards with ω
    exact
      (continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
        (μ := μ) (ℱ := ℱ) (M := M) (H := (Ks n : NNReal → Ω → ℝ)) hM T ω).symm
  have hCanonical :
      TendstoInMeasure μ
        (fun n ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Ks n : NNReal → Ω → ℝ) T ω)
        atTop
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T) :=
    canonicalFixedTime_tendstoInMeasure_of_closureApprox_local
      (μ := μ) (ℱ := ℱ) (M := M)
      hM
      (MeasureTheory.processBeforeStoppingTime_progMeasurable hH_prog (isStoppingTime_const ℱ T))
      hHcut_mem hKs_tendsto T
  have hUnique :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T :=
    MeasureTheory.tendstoInMeasure_ae_unique hCommon hCanonical
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem) =ᵐ[μ]
        BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T :=
    constCutoffTerminal_ae_eq_truncatedAtFixedTime_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hH_mem T
  -- Proof comment: the same predictable-simple approximation sequence now gives both the
  -- Brownian truncation slice and the canonical cutoff value as limits in measure, so uniqueness
  -- closes the deterministic-cutoff seed theorem.
  exact hTerminalEq.trans hUnique

/-- Helper for Exercise 25.2.1(i): the remaining fixed-time bridge is to compare the Brownian
truncation slice of one closure point directly with the canonical Chapter 25 Itô value at the
same horizon. -/
private theorem brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_of_constCutoffCanonical_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal)
    (hConstCutoffCanonical :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hH_mem T)) =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  have hBrownianToTerminal :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hH_mem T)) :=
    brownianTruncatedClosure_ae_eq_constCutoffTerminal_local
      (μ := μ) (ℱ := ℱ) (M := M) hH_mem T
  have hCutoffValue :
      continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T :=
    continuousLocalMartingaleItoIntegralProcess_ae_eq_constCutoff_value
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM T
  -- Proof comment: once the deterministic cutoff terminal class is matched with the canonical
  -- cutoff value, the frontier is just the Brownian cutoff normalization followed by the
  -- canonical cutoff-removal identity at time `T`.
  exact hBrownianToTerminal.trans <| hConstCutoffCanonical.trans hCutoffValue

/-- Helper for Exercise 25.2.1(i): the remaining fixed-time bridge is to compare the Brownian
truncation slice of one closure point directly with the canonical Chapter 25 Itô value at the
same horizon. -/
private theorem brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  -- Route correction: all earlier fixed-time helper proofs now factor through this single
  -- truncation-to-canonical frontier, rather than re-entering the terminal-map cycle.
  have hConstCutoffCanonical :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hH_mem T)) =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T :=
    constCutoffTerminal_ae_eq_canonicalConstCutoffAtFixedTime_seed_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T
  -- Proof comment: after the deterministic-cutoff terminal bridge is isolated, the frontier is
  -- the fixed composition proved in the dedicated normalization helper above.
  exact
    brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_of_constCutoffCanonical_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_mem T hConstCutoffCanonical

/-- Helper for Exercise 25.2.1: on a predictable-simple stage, the canonical fixed-time Itô value
matches the Brownian elementary integral at the same horizon. -/
private theorem predictableSimpleCanonicalValue_ae_eq_brownianIntegral_local
    {M : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : NNReal → Ω → ℝ))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM (K : NNReal → Ω → ℝ) T ω) =ᵐ[μ]
      MeasureTheory.brownianElementaryIntegral M K T := by
  have hCutoffValue :
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
          T
          ω) =ᵐ[μ]
        (fun ω ↦ continuousLocalMartingaleItoIntegralProcess hM (K : NNReal → Ω → ℝ) T ω) := by
    -- Proof comment: deterministically cutting off a stage at the same terminal horizon does not
    -- change its canonical fixed-time Itô value.
    filter_upwards with ω
    exact
      continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
        (μ := μ) (ℱ := ℱ) (M := M) (H := (K : NNReal → Ω → ℝ)) hM T ω
  have hCutoffCanonical :
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime (K : NNReal → Ω → ℝ) (fun _ ↦ (T : ENNReal)))
          T
          ω) =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegral M K T := by
    -- Proof comment: the predictable-simple cutoff bridge is now the dedicated earlier theorem,
    -- so the general-stage wrapper no longer depends directly on the seed theorem.
    exact
      predictableSimpleConstCutoffCanonicalValue_ae_eq_brownianIntegral_local
        (μ := μ) (ℱ := ℱ) (M := M) hM K hK T
  -- Proof comment: once the deterministic-cutoff canonical value is identified with the terminal
  -- Brownian-Itô class, the original stage follows from the cutoff-removal identity at time `T`.
  exact hCutoffValue.symm.trans hCutoffCanonical

/-- Helper for Exercise 25.2.1: fixed-time canonical Itô values should be continuous in measure
along a predictable-simple approximation of one closure point. -/
private theorem canonicalFixedTime_tendstoInMeasure_of_closureApprox_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : NNReal → Ω → ℝ))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs_tendsto :
      Tendsto
        (fun n ↦ MeasureTheory.predictableSimpleProcessToClosureLocal (Hs n) (hHs_mem n))
        atTop
        (nhds _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem))
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Hs n : NNReal → Ω → ℝ) T ω)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM H T) := by
  -- Route correction: the old generic continuity statement was the wrong surface. With the
  -- Brownian fixed-time continuity theorem in hand, the only remaining step is the exact
  -- Brownian-versus-canonical frontier at the target closure point.
  have hBrownian :
      TendstoInMeasure μ
        (fun n ω ↦ MeasureTheory.brownianElementaryIntegral M (Hs n) T ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T) := by
    have hLp :
        TendstoInLp 2 μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral M (Hs n) T)
          (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
            (M := M)
            (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
            T) := by
      -- Proof comment: the Brownian fixed-time continuity theorem already identifies the
      -- deterministic-time slice of one closure approximation with the truncation process limit.
      simpa [BrownianItoIntegral.brownianItoIntegralTruncatedProcess] using
        (BrownianItoIntegral.brownianElementaryIntegral_timeSlice_tendstoInLp_two_local
          (μ := μ) (ℱ := ℱ) (W := M)
          (H := _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          (Hs := Hs) (hHs_mem := hHs_mem) (hHs_tendsto := hHs_tendsto) (t := T))
    exact MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  have hCanonicalToBrownian :
      TendstoInMeasure μ
        (fun n ω ↦ continuousLocalMartingaleItoIntegralProcess hM (Hs n : NNReal → Ω → ℝ) T ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T) := by
    -- Proof comment: stagewise predictable-simple canonical values are already reduced to the
    -- Brownian elementary surface, so the Brownian fixed-time continuity theorem gives the
    -- common limit in measure.
    refine
      TendstoInMeasure.congr_left
        (fun n ↦
          predictableSimpleCanonicalValue_ae_eq_brownianIntegral_local
            (μ := μ) (ℱ := ℱ) (M := M) hM (Hs n) (hHs_mem n) T)
        hBrownian
  have hFrontier :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T := by
    -- Proof comment: the only remaining target-side transport is the dedicated truncation-to-
    -- canonical frontier for this closure point.
    exact
      brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T
  -- Proof comment: once the exact fixed-time frontier is supplied for the target closure point,
  -- the canonical-stage sequence inherits the desired limit by transport of the Brownian limit.
  exact TendstoInMeasure.congr_right hFrontier hCanonicalToBrownian

/-- Helper for Exercise 25.2.1: closure approximation on the Brownian side gives convergence in
measure of the fixed-time Brownian elementary values to the fixed-time Brownian truncation slice.
-/
private theorem brownianTimeSlice_tendstoInMeasure_of_closureApprox_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : NNReal → Ω → ℝ))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs_tendsto :
      Tendsto
        (fun n ↦ MeasureTheory.predictableSimpleProcessToClosureLocal (Hs n) (hHs_mem n))
        atTop
        (nhds _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem))
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦ MeasureTheory.brownianElementaryIntegral M (Hs n) T ω)
      atTop
      (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        T) := by
  have hLp :
      TendstoInLp 2 μ
        (fun n ↦ MeasureTheory.brownianElementaryIntegral M (Hs n) T)
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T) := by
    -- Proof comment: the Brownian fixed-time continuity theorem already identifies the
    -- deterministic-time slice of one closure approximation with the truncation process limit.
    simpa [BrownianItoIntegral.brownianItoIntegralTruncatedProcess] using
      (BrownianItoIntegral.brownianElementaryIntegral_timeSlice_tendstoInLp_two_local
        (μ := μ) (ℱ := ℱ) (W := M) (H := _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        (Hs := Hs) (hHs_mem := hHs_mem) (hHs_tendsto := hHs_tendsto) (t := T))
  -- Proof comment: `L²` convergence at the fixed horizon already gives the desired convergence in
  -- measure to the same Brownian truncation slice.
  exact MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp

/-- Helper for Exercise 25.2.1(i): the terminal Brownian-Itô class of the deterministic cutoff
closure point should match the canonical fixed-time Itô value of that same deterministic cutoff. -/
private theorem constCutoffTerminal_ae_eq_canonicalConstCutoffAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    hIto.toContinuousLinearMap
        (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T := by
  -- Proof comment: the closure-approximation proof now lives in the seed theorem, so the later
  -- local theorem is just its stable wrapper.
  exact
    constCutoffTerminal_ae_eq_canonicalConstCutoffAtFixedTime_seed_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T

/-- Helper for Exercise 25.2.1(i): one fixed-horizon bracket-density integrability clause already
produces a deterministic-cutoff owner whose time-`T` value matches the canonical cutoff value. -/
private theorem constCutoffOwner_value_ae_eq_canonicalConstCutoffAtFixedTime_of_integrableOn_local
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (T : NNReal)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      IsContinuousLocalMartingaleItoIntegralOwner
        (μ := μ) (ℱ := ℱ) (hM := hM)
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) N ∧
        N T =ᵐ[μ]
          continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            T := by
  have hCutFiniteEnergy :
      HasFiniteBracketEnergy hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) :=
    processBeforeStoppingTime_const_hasFiniteBracketEnergy_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hbr T hH_prog hH_sq
  rcases
      exists_continuousLocalMartingaleItoIntegral
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        hM
        hbr
        hCutFiniteEnergy.1
        hCutFiniteEnergy.2 with
    ⟨N, hSpec⟩
  refine ⟨N, hSpec.itoIntegral, ?_⟩
  -- Proof comment: the owner returned by the single-horizon existence theorem already lives on
  -- the deterministic-cutoff surface, so the fixed-time owner-to-canonical comparison applies
  -- directly at horizon `T`.
  exact
    itoIntegralOwner_aeEq_canonicalAtFixedTime
      (μ := μ)
      (ℱ := ℱ)
      (M := M)
      (H := processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (N := N)
      hSpec.itoIntegral
      T

/-- Helper for Exercise 25.2.1(i): finite bracket energy gives a deterministic-cutoff owner
whose time-`T` value already agrees almost everywhere with the canonical fixed-time Itô value. -/
private theorem constCutoffOwner_value_ae_eq_canonicalAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (T : NNReal) :
    ∃ N : NNReal → Ω → ℝ,
      IsContinuousLocalMartingaleItoIntegralOwner
        (μ := μ) (ℱ := ℱ) (hM := hM)
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) N ∧
        N T =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H T := by
  have hH_sq :
      ∀ U : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) :=
    finiteBracketEnergy_integrableOn_bracketDensity
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr hFiniteEnergy
  obtain ⟨N, hOwner, hValue⟩ :=
    constCutoffOwner_value_ae_eq_canonicalConstCutoffAtFixedTime_of_integrableOn_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hbr hH_prog T (hH_sq T)
  refine ⟨N, hOwner, ?_⟩
  have hCutoffValue :
      continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T :=
    continuousLocalMartingaleItoIntegralProcess_ae_eq_constCutoff_value
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM T
  -- Proof comment: the new single-horizon owner helper lands on the deterministic-cutoff
  -- canonical value, and the cutoff-removal identity transports that fixed-time value back to
  -- the original integrand at the same horizon.
  exact hValue.trans hCutoffValue

private theorem brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_of_ownerValue_local
    {M H N : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal)
    (hOwnerValue :
      hIto.toContinuousLinearMap
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
        N T)
    (hCanonicalValue :
      N T =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H T) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  have hBrownianToTerminal :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T =ᵐ[μ]
        hIto.toContinuousLinearMap
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) :=
    brownianTruncatedClosure_ae_eq_constCutoffTerminal_local
      (μ := μ) (ℱ := ℱ) (M := M) hH_mem T
  -- Proof comment: the Brownian-side truncation slice is already the terminal class of the
  -- deterministically cutoff closure point, so only the owner-value bridge and the canonical
  -- time-`T` identification remain.
  exact hBrownianToTerminal.trans <| hOwnerValue.trans hCanonicalValue

private theorem constCutoffTerminal_ae_eq_canonicalAtFixedTime_direct_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    hIto.toContinuousLinearMap
        (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
        BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T := by
    -- Proof comment: the deterministic cutoff terminal map is exactly the fixed-time Brownian
    -- truncation slice of the original closure point.
    simpa using
      deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := M) hH_mem T
  have hCanonicalEq :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T := by
    -- Proof comment: the only unresolved work is the general fixed-time bridge from a closure
    -- truncation slice to the canonical Chapter 25 value.
    exact
      brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T
  -- Proof comment: after normalizing the deterministic cutoff terminal map to the truncation
  -- slice, the new frontier theorem supplies the canonical fixed-time identification.
  exact hTerminalEq.trans hCanonicalEq

private theorem constCutoffTruncated_ae_eq_canonicalAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T)
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  have hTruncEq :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T)
          T =ᵐ[μ]
        hIto.toContinuousLinearMap
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) := by
    -- Proof comment: the Brownian-side deterministic-cutoff normalization is now a standalone
    -- helper, so the wrapper theorem no longer reopens the vanishing-after-`T` transport.
    exact
      (constCutoffTerminal_ae_eq_truncatedAtFixedTime_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hH_mem T).symm
  have hCanonicalEq :
      hIto.toContinuousLinearMap
          (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H T := by
    -- Proof comment: the unresolved Brownian-to-canonical comparison now lives in one direct
    -- terminal-bridge helper for the deterministic cutoff closure point.
    exact
      constCutoffTerminal_ae_eq_canonicalAtFixedTime_direct_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T
  -- Proof comment: after normalizing the stopped closure point to its terminal Brownian-Itô
  -- class, only the direct terminal bridge to the canonical value remains.
  exact hTruncEq.trans hCanonicalEq

/-- Helper for Exercise 25.2.1(i): the terminal Brownian-Itô class of the deterministically cut
off closure point should agree almost everywhere with the canonical fixed-time Itô value. -/
private theorem constCutoffTerminal_ae_eq_canonicalAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    hIto.toContinuousLinearMap
        (constCutoffClosure (μ := μ) (ℱ := ℱ) hH_mem T) =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  -- Proof comment: the actual frontier is the direct terminal comparison for the deterministic
  -- cutoff closure point, so this theorem is now just that dedicated helper.
  exact
    constCutoffTerminal_ae_eq_canonicalAtFixedTime_direct_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T

/-- Helper for Exercise 25.2.1(i): a Brownian-side truncation slice coming from a closure point
agrees almost everywhere with the canonical fixed-time Itô value of the same integrand. -/
private theorem brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (T : NNReal) :
    BrownianItoIntegral.brownianItoIntegralTruncatedProcess
        (M := M)
        (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hH_mem)
        T =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM H T := by
  -- Proof comment: this theorem is now exactly the general fixed-time frontier theorem, kept as
  -- the canonical local API spelling for later row-closure arguments.
  exact
    brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_mem T

/-- Helper for Exercise 25.2.1(i): closure convergence of the clipped deterministic-cutoff row
stages should force convergence in measure of their Brownian elementary values. -/
private theorem clippedConstCutoffPartitionRows_brownianIntegral_tendstoInMeasure_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    TendstoInMeasure μ
      (fun row ω ↦
        MeasureTheory.brownianElementaryIntegral
          M
          ((clippedConstCutoffPartitionRowRepresentation
              (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
          T
          ω)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        T) := by
  let Hcut : NNReal → Ω → ℝ :=
    processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal))
  have hHcut_prog : ProgMeasurable ℱ Hcut := by
    -- Proof comment: deterministic stopping preserves progressive measurability of the clipped
    -- coefficient.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        (clippedProcess_progMeasurable (ℱ := ℱ) (H := H) R hH_prog hH_cont)
        (isStoppingTime_const ℱ T)
  let hHcut_mem : _root_.MeasureTheory.MemPredictableStepProcessClosure ℱ μ Hcut :=
    MeasureTheory.progMeasurable_memPredictableStepProcessClosure
      ℱ
      μ
      hHcut_prog
      (clippedConstCutoff_memLp (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont R T)
  have hLp :
      TendstoInLp 2 μ
        (fun row ↦
          MeasureTheory.brownianElementaryIntegral
            M
            ((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
            T)
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T) := by
    -- Proof comment: the row family already converges in the predictable-simple closure, so the
    -- Brownian-side fixed-time continuity theorem gives the corresponding `L²` convergence.
    simpa [Hcut, hHcut_mem] using
      (BrownianItoIntegral.brownianElementaryIntegral_timeSlice_tendstoInLp_two_local
        (μ := μ)
        (ℱ := ℱ)
        (W := M)
        (H := _root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
        (Hs := fun row ↦
          (clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
        (hHs_mem := fun row ↦
          clippedConstCutoffRow_memLp
            (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T)
        (hHs_tendsto :=
          clippedConstCutoffPartitionRowsTendstoToClosure
            (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P R T)
        (t := T))
  have hMeasure :
      TendstoInMeasure μ
        (fun row ω ↦
          MeasureTheory.brownianElementaryIntegral
            M
            ((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
            T
            ω)
        atTop
        (BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T) := by
    -- Proof comment: `L²` convergence at one deterministic time implies convergence in measure
    -- at that same time.
    exact MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  have hTargetEq :
      BrownianItoIntegral.brownianItoIntegralTruncatedProcess
          (M := M)
          (_root_.MeasureTheory.MemPredictableStepProcessClosure.toClosure hHcut_mem)
          T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM Hcut T :=
    brownianTruncatedClosure_ae_eq_canonicalAtFixedTime_frontier_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := Hcut) hM hHcut_prog hHcut_mem T
  -- Proof comment: after the Brownian fixed-time continuity step, only the single target
  -- identification between the Brownian truncation slice and the canonical cutoff value remains.
  exact TendstoInMeasure.congr_right hTargetEq hMeasure

/-- Helper for Exercise 25.2.1(i): on one clipped deterministic-cutoff row, the canonical
fixed-time Itô value should agree almost everywhere with the Brownian elementary integral of the
same predictable simple stage. -/
private theorem clippedConstCutoffPartitionRow_canonicalValue_ae_eq_brownianIntegral
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    (fun ω ↦
      continuousLocalMartingaleItoIntegralProcess hM
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ))
        T
        ω) =ᵐ[μ]
      (fun ω ↦
        MeasureTheory.brownianElementaryIntegral
          M
          ((clippedConstCutoffPartitionRowRepresentation
              (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
          T
          ω) := by
  -- Proof comment: the clipped row stage is already a globally square-integrable predictable
  -- simple process, so the general predictable-simple fixed-time bridge applies directly.
  simpa using
    predictableSimpleCanonicalValue_ae_eq_brownianIntegral_local
      (μ := μ)
      (ℱ := ℱ)
      (M := M)
      hM
      ((clippedConstCutoffPartitionRowRepresentation
          (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
      (clippedConstCutoffRow_memLp
        (μ := μ) (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T)
      T

/-- Helper for Exercise 25.2.1(i): closure convergence of the clipped deterministic-cutoff row
stages should force convergence in measure of their canonical fixed-time Itô values. -/
private theorem canonicalIto_timeSlice_tendstoInMeasure_of_clippedClosureApproximation_local
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    TendstoInMeasure μ
      (fun row ω ↦
        continuousLocalMartingaleItoIntegralProcess hM
          (((clippedConstCutoffPartitionRowRepresentation
              (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
              NNReal → Ω → ℝ))
          T
          ω)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        T) := by
  have hBrownian :
      TendstoInMeasure μ
        (fun row ω ↦
          MeasureTheory.brownianElementaryIntegral
            M
            ((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess)
            T
            ω)
        atTop
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
          T) := by
    -- Proof comment: the only remaining analytic input is the Brownian-side fixed-time
    -- continuity theorem for the closure-convergent clipped row family.
    exact
      clippedConstCutoffPartitionRows_brownianIntegral_tendstoInMeasure_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hH_cont hFiniteEnergy P R T
  -- Proof comment: once each row's canonical fixed-time value is identified with the matching
  -- Brownian elementary value, the desired convergence is exactly the Brownian-side limit above.
  refine
    TendstoInMeasure.congr_left
      (fun row ↦
        (clippedConstCutoffPartitionRow_canonicalValue_ae_eq_brownianIntegral
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_cont P row R T).symm)
      hBrownian

/-- Helper for Exercise 25.2.1(i): the canonical fixed-time Itô value of one clipped
deterministic-cutoff row should agree almost everywhere with the explicit partition sum on that
same row. -/
private theorem clippedConstCutoffPartitionRow_canonicalValue_ae_eq_partitionSum
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (row : ℕ) (R T : NNReal) :
    (fun ω ↦
      continuousLocalMartingaleItoIntegralProcess hM
        (((clippedConstCutoffPartitionRowRepresentation
            (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
            NNReal → Ω → ℝ))
        T
        ω) =ᵐ[μ]
      (fun ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          row) := by
  refine
    (clippedConstCutoffPartitionRow_canonicalValue_ae_eq_brownianIntegral
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_cont P row R T).trans ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  -- Proof comment: after the canonical-to-Brownian bridge, the clipped row representation already
  -- computes the explicit partition sum by the finite-step elementary-integral identity.
  have hcutoff :
      partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          row =
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ clippedProcess H R t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          row :=
    partitionPathwiseItoApproximationUpTo_constCutoff_eq
      (μ := μ) (ℱ := ℱ) (M := M) (H := clippedProcess H R) hM P T ω row
  simpa [hcutoff, ProbabilityTheory.processBeforeStoppingTime_const_eqOn_Icc_local] using
    clippedConstCutoffPartitionRow_brownianIntegral_eq_partitionSum
      (ℱ := ℱ) (H := H) (W := M) hH_prog hH_cont P row R T ω (hM.continuous ω)

/-- Helper for Exercise 25.2.1(i): for a fixed clip radius `R` and horizon `T`, the explicit
clipped partition rows should converge in measure directly to the deterministically cutoff
canonical Itô value, without passing through the false base-space `HasFiniteItoIntegrandNorm`
surface for each row. -/
private theorem clippedConstCutoffPartitionApproximation_tendstoInMeasure_direct
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (R T : NNReal) :
    TendstoInMeasure μ
      (fun row ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          row)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
        T) := by
  -- Route correction: isolate the remaining work into the two precise bridges that still have to
  -- be exported: closure-to-canonical fixed-time convergence, and canonical-row-value rewriting.
  have hCanonical :
      TendstoInMeasure μ
        (fun row ω ↦
          continuousLocalMartingaleItoIntegralProcess hM
            (((clippedConstCutoffPartitionRowRepresentation
                (ℱ := ℱ) (H := H) hH_prog hH_cont P row R T).toPredictableSimpleProcess :
                NNReal → Ω → ℝ))
            T
            ω)
        atTop
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
          T) := by
    -- Proof comment: this is exactly the missing Brownian-transport continuity statement for the
    -- clipped row family.
    exact
      canonicalIto_timeSlice_tendstoInMeasure_of_clippedClosureApproximation_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hbr hH_prog hH_cont hFiniteEnergy P R T
  -- Proof comment: once each row's canonical fixed-time value is rewritten to the explicit row
  -- sum, the remaining convergence is the canonical-value convergence just proved above.
  refine
    TendstoInMeasure.congr_left
      (fun row ↦
        clippedConstCutoffPartitionRow_canonicalValue_ae_eq_partitionSum
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hH_prog hH_cont P row R T)
      hCanonical

/-- Helper for Exercise 25.2.1(i): it is enough to prove the fixed-horizon convergence after
deterministically cutting off the coefficient at the same horizon. -/
private theorem constCutoffPartitionApproximation_tendstoInMeasure
    {M H : NNReal → Ω → ℝ}
    [hIto : BrownianItoIntegral μ ℱ M]
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T) := by
  let Hcut : NNReal → Ω → ℝ :=
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))
  have hH_sq :
      ∀ T' : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T' : ℝ)) :=
    finiteBracketEnergy_integrableOn_bracketDensity
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr hFiniteEnergy
  have hCutFiniteEnergy :
      HasFiniteBracketEnergy hbr Hcut := by
    -- Proof comment: the fixed deterministic cutoff inherits the same finite-energy package from
    -- the original coefficient on `[0, T]`.
    exact
      processBeforeStoppingTime_const_hasFiniteBracketEnergy_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hbr T hH_prog (hH_sq T)
  have hHcut_sq :
      ∀ U : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (Hcut s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) := by
    -- Proof comment: the cutoff coefficient now satisfies the all-horizons integrability clause
    -- required by the Itô-integral existence interface.
    intro U
    exact hCutFiniteEnergy.2 U
  have hCountableBounds :
      ∀ᵐ ω ∂μ,
        ∃ N : ℕ,
          (∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)) ∧
          (∀ row k : ℕ,
            k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
              |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal)) := by
    -- Proof comment: the compact-interval boundedness of almost every continuous sample path is
    -- already enough for all partition and dyadic left endpoints relevant to the unclipping step.
    exact
      ae_existsNatPartitionAndDyadicClipRadius
        (μ := μ) (H := H) hH_cont P T
  let _ := hHcut_sq
  let _ := hCountableBounds
  have hClipped :
      ∀ R : NNReal,
        TendstoInMeasure μ
          (fun n ω ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              T
              n)
          atTop
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
            T) := by
    intro R
    -- Proof comment: the direct clipped theorem is now the only fixed-horizon frontier; the
    -- unclipping argument below no longer depends on the false rowwise `M`-norm surface.
    simpa using
      clippedConstCutoffPartitionApproximation_tendstoInMeasure_direct
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hH_cont hFiniteEnergy P R T
  let origSeq : ℕ → Ω → ℝ := fun n ω ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      T
      n
  let origTarget : Ω → ℝ := fun ω ↦
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      T
      ω
  let clippedSeq : ℕ → ℕ → Ω → ℝ := fun R n ω ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)) t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      T
      n
  let clippedTarget : ℕ → Ω → ℝ := fun R ω ↦
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime (clippedProcess H R) (fun _ ↦ (T : ENNReal)))
      T
      ω
  let A : ℕ → Set Ω := fun N ↦
    {ω |
      (∀ row k : ℕ, k < partitionBoundIndex P row T → |H (P row k) ω| ≤ (N : NNReal)) ∧
      (∀ row k : ℕ,
        k < partitionBoundIndex Definition2158.dyadicPartitionSequence row T →
          |H (Definition2158.dyadicPartitionSequence row k) ω| ≤ (N : NNReal))}
  have hA_meas : ∀ N : ℕ, MeasurableSet (A N) := by
    intro N
    -- Proof comment: the countable endpoint-bound event is already packaged as a measurable set.
    simpa [A] using
      measurableSet_partitionAndDyadicClipBounds
        (ℱ := ℱ) (H := H) hH_prog P T N
  have hA_mono : Monotone A := by
    -- Proof comment: enlarging the clip radius only enlarges the endpoint-bound event.
    simpa [A] using
      partitionAndDyadicClipBounds_mono (H := H) (P := P) T
  have hA_aeUnion : ∀ᵐ ω ∂μ, ω ∈ ⋃ N : ℕ, A N := by
    filter_upwards [hCountableBounds] with ω hω
    rcases hω with ⟨N, hP, hD⟩
    exact Set.mem_iUnion.mpr ⟨N, by exact ⟨hP, hD⟩⟩
  have hAcompl_tendsto :
      Tendsto (fun N : ℕ ↦ μ ((A N)ᶜ)) atTop (𝓝 0) := by
    have hInterZero : μ (⋂ N : ℕ, (A N)ᶜ) = 0 := by
      have hEq :
          (⋂ N : ℕ, (A N)ᶜ) = (⋃ N : ℕ, A N)ᶜ := by
        ext ω
        simp
      rw [hEq]
      exact ae_iff.1 hA_aeUnion
    have hT :
        Tendsto (fun N : ℕ ↦ μ ((A N)ᶜ)) atTop (𝓝 (μ (⋂ N : ℕ, (A N)ᶜ))) := by
      exact
        tendsto_measure_iInter_atTop
          (s := fun N : ℕ ↦ (A N)ᶜ)
          (fun N ↦ (hA_meas N).nullMeasurableSet.compl)
          (by
            intro N M hNM
            exact Set.compl_subset_compl.mpr (hA_mono hNM))
          ⟨0, by simp⟩
    simpa [hInterZero] using hT
  have hSeqEqOn :
      ∀ N n : ℕ, Set.EqOn (origSeq n) (clippedSeq N n) (A N) := by
    intro N n ω hω
    -- Proof comment: on the countable endpoint-bound event `A N`, clipping is inactive on every
    -- left endpoint contributing to row `n`.
    simpa [origSeq, clippedSeq] using
      (partitionPathwiseItoApproximationUpTo_clippedConstCutoff_eq_of_partitionPoint_bounds
        (P := P)
        (X := (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace))
        (R := N)
        (T := T)
        (ω := ω)
        (row := n)
        (hbound := fun k hk ↦ hω.1 n k hk)).symm
  have hTargetEqOn :
      ∀ N : ℕ, Set.EqOn origTarget (clippedTarget N) (A N) := by
    intro N ω hω
    -- Proof comment: the same event also controls all dyadic left endpoints, so the canonical
    -- fixed-time Itô target is unchanged by clipping.
    simpa [origTarget, clippedTarget] using
      (continuousLocalMartingaleItoIntegralProcess_eq_clippedConstCutoff_value_of_dyadicPoint_bounds
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM
        (R := N)
        (T := T)
        (ω := ω)
        (hbound := hω.2)).symm
  -- Proof comment: the fixed-radius clipped convergence is already proved, and the increasing
  -- events `A N` eventually cover almost every sample path while forcing the original and clipped
  -- quantities to agree exactly. This reduces the final convergence-in-measure claim to one
  -- epsilon-delta estimate with a single clipped radius `N`.
  refine tendstoInMeasure_of_ne_top ?_
  intro ε hε hε_top
  have hAcompl_zero := hAcompl_tendsto
  rw [ENNReal.tendsto_atTop_zero] at hAcompl_zero ⊢
  intro δ hδ
  have hδ_half : 0 < δ / 2 := by
    exact ENNReal.div_pos_iff.2 ⟨hδ.ne', by simp⟩
  obtain ⟨N, hN⟩ := hAcompl_zero (δ / 2) hδ_half
  have hClipN :
      Tendsto
        (fun n ↦
          μ {ω | ε ≤ edist (clippedSeq N n ω) (clippedTarget N ω)})
        atTop
        (𝓝 0) := by
    simpa [clippedSeq, clippedTarget] using hClipped N ε hε
  rw [ENNReal.tendsto_atTop_zero] at hClipN
  obtain ⟨M, hM⟩ := hClipN (δ / 2) hδ_half
  refine ⟨M, ?_⟩
  intro n hn
  have hCompSmall : μ ((A N)ᶜ) ≤ δ / 2 := hN N le_rfl
  have hClipSmall :
      μ {ω | ε ≤ edist (clippedSeq N n ω) (clippedTarget N ω)} ≤ δ / 2 := hM n hn
  have hSubset :
      {ω | ε ≤ edist (origSeq n ω) (origTarget ω)} ⊆
        (A N)ᶜ ∪ {ω | ε ≤ edist (clippedSeq N n ω) (clippedTarget N ω)} := by
    intro ω hω
    by_cases hωA : ω ∈ A N
    · right
      have hSeqEq : origSeq n ω = clippedSeq N n ω := hSeqEqOn N n hωA
      have hTargetEq : origTarget ω = clippedTarget N ω := hTargetEqOn N hωA
      simpa [hSeqEq, hTargetEq] using hω
    · exact Or.inl hωA
  calc
    μ {ω | ε ≤ edist (origSeq n ω) (origTarget ω)}
        ≤ μ ((A N)ᶜ) + μ {ω | ε ≤ edist (clippedSeq N n ω) (clippedTarget N ω)} := by
          exact (measure_mono hSubset).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add hCompSmall hClipSmall
    _ = δ := ENNReal.add_halves δ

/-- Helper for Exercise 25.2.1(i): the public fixed-horizon theorem is reduced to one cutoff
convergence statement whose only missing input is the owner-to-approximation bridge for the
deterministically stopped integrand. -/
private theorem constCutoffPartitionApproximation_tendstoInMeasure_via_owner_local
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T) := by
  let Hcut : NNReal → Ω → ℝ :=
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))
  have hH_sq :
      ∀ U : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) :=
    finiteBracketEnergy_integrableOn_bracketDensity
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr hFiniteEnergy
  obtain ⟨N, hOwner, hValue⟩ :=
    constCutoffOwner_value_ae_eq_canonicalConstCutoffAtFixedTime_of_integrableOn_local
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hbr hH_prog T (hH_sq T)
  let _ := Hcut
  let _ := hOwner
  let _ := hValue
  -- Route correction: the unstable Brownian-instance search is replaced by one smaller frontier:
  -- construct a source-side approximation theorem for the deterministic cutoff and feed it into
  -- the already-proved owner-level wrapper `constCutoffApproximation_tendstoInMeasure_of_sourceApprox_local`.
  -- TODO: supply either a `HasApproximationFormula` witness for `Hcut` and `N`, or an equivalent
  -- Brownian-extension theorem that yields this cutoff convergence directly. After that, the proof
  -- is just `constCutoffApproximation_tendstoInMeasure_of_sourceApprox_local` plus `hValue`.
  sorry

/-- Helper for Exercise 25.2.1(i): at a fixed horizon, the partition sums converge in measure to
the canonical Itô integral value. -/
theorem tendstoInMeasure_partitionItoApproximationUpTo
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (continuousLocalMartingaleItoIntegralProcess hM H T) := by
  -- Proof comment: once the deterministic-cutoff convergence is isolated in one owner-side
  -- helper, the original fixed-horizon theorem is again only the cutoff-removal wrapper.
  exact
    tendstoInMeasure_partitionItoApproximationUpTo_of_constCutoff
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P T
      (constCutoffPartitionApproximation_tendstoInMeasure_via_owner_local
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hH_cont hFiniteEnergy P T)

/-- Helper for Exercise 25.2.1(ii): once one strict-mono row family already converges at the
target horizon `T`, the same-cell rational selector error tends to `0` along the same rows. -/
lemma sameCellSelectorError_tendsto_of_targetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hTarget :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            (χ n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω))) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (q n : NNReal)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
      atTop
      (𝓝 0) := by
  let targetSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      T
      (χ n)
  let rationalSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (q n : NNReal)
      (χ n)
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (partitionPredecessorPointEarly P (χ n) T) ω *
      (M T ω - M (q n : NNReal) ω)
  have hSameCell :
      ∀ n : ℕ, targetSums n = rationalSums n + boundaryTerms n := by
    intro n
    -- Proof comment: same-cell horizons differ only by the last clipped increment in row `χ n`.
    dsimp [targetSums, rationalSums, boundaryTerms]
    exact
      partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
        (le_of_lt (hqLt n)) (hqSame n)
  have hTargetErr :
      Tendsto
        (fun n ↦ targetSums n - continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℕ ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω)
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      tendsto_const_nhds
    -- Proof comment: subtract the constant target value from the assumed target-horizon limit.
    simpa [targetSums] using hTarget.sub hConst
  have hSelector :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hqT
  have hSelectorErr :
      Tendsto
        (fun n ↦
          continuousLocalMartingaleItoIntegralProcess hM H T ω -
            continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℕ ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω)
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of the canonical Itô path transports the selector `q n → T`.
    simpa using hConst.sub hSelector
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    -- Proof comment: the last same-cell increment vanishes because both paths are continuous.
    simpa [boundaryTerms] using
      partitionItoSelectorBoundaryTerm_tendsto_zero
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hχ hHωCont hqT
  have hErrorEq :
      (fun n ↦
        rationalSums n -
          continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω) =
        (fun n ↦
          (targetSums n - continuousLocalMartingaleItoIntegralProcess hM H T ω) -
            boundaryTerms n +
              (continuousLocalMartingaleItoIntegralProcess hM H T ω -
                continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)) := by
    funext n
    -- Proof comment: rewrite the moving-time error as target-horizon error minus the boundary
    -- term plus the canonical selector error.
    linarith [hSameCell n]
  rw [hErrorEq]
  -- Proof comment: each summand tends to `0`, so the whole same-cell selector error vanishes.
  simpa using (hTargetErr.sub hBoundary).add hSelectorErr

/-- Helper for Exercise 25.2.1(ii): if a same-cell rational selector already approximates the
canonical Itô value along one strict-mono row family, then adding back the vanishing boundary term
and the vanishing canonical selector mismatch recovers convergence at the target horizon `T`. -/
lemma targetConvergence_of_sameCellSelectorError
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (φ n) (q n : NNReal) = partitionBoundIndex P (φ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hSelectorErr :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            (φ n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          (φ n))
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  let targetSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      T
      (φ n)
  let rationalSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (q n : NNReal)
      (φ n)
  let selectorTargets : ℕ → ℝ := fun n ↦
    continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (partitionPredecessorPointEarly P (φ n) T) ω *
      (M T ω - M (q n : NNReal) ω)
  have hSameCell :
      ∀ n : ℕ, targetSums n = rationalSums n + boundaryTerms n := by
    intro n
    -- Proof comment: same-cell horizons differ only by the final clipped increment on the last
    -- partition cell.
    dsimp [targetSums, rationalSums, boundaryTerms]
    exact
      partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
        (le_of_lt (hqLt n)) (hqSame n)
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    -- Proof comment: continuity of both the coefficient path and the martingale path kills the
    -- last-cell boundary contribution.
    simpa [boundaryTerms] using
      partitionItoSelectorBoundaryTerm_tendsto_zero
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hφ hHωCont hqT
  have hTargets :
      Tendsto selectorTargets atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    -- Proof comment: the canonical Itô path is continuous, so the selector `q n → T` transports
    -- directly to the target canonical value.
    simpa [selectorTargets] using
      canonicalItoIntegral_selector_tendsto_of_continuous
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hqT
  have hTargetErr :
      Tendsto
        (fun n ↦ selectorTargets n -
          continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℕ ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω)
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      tendsto_const_nhds
    -- Proof comment: subtract the constant target canonical value from the moving selector limit.
    simpa [selectorTargets] using hTargets.sub hConst
  have hErrorEq :
      (fun n ↦ targetSums n - continuousLocalMartingaleItoIntegralProcess hM H T ω) =
        (fun n ↦
          boundaryTerms n +
            (rationalSums n -
                continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω) +
              (selectorTargets n -
                continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    funext n
    -- Proof comment: expand the target-horizon error into the same-cell boundary contribution,
    -- the selector error, and the canonical selector mismatch.
    linarith [hSameCell n]
  have hErr :
      Tendsto
        (fun n ↦ targetSums n - continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 0) := by
    rw [hErrorEq]
    simpa [add_assoc] using hBoundary.add (hSelectorErr.add hTargetErr)
  have hConst :
      Tendsto
        (fun _ : ℕ ↦ continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    tendsto_const_nhds
  have hSum :
      Tendsto
        (fun n ↦
          (targetSums n - continuousLocalMartingaleItoIntegralProcess hM H T ω) +
            continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 (0 + continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    hErr.add hConst
  -- Proof comment: the target-horizon sum is the sum of a vanishing error and the constant
  -- canonical target value.
  simpa [targetSums, sub_add_cancel] using hSum

/-- Helper for Exercise 25.2.1(ii): on one strict-mono row family, fixed-target convergence at
`T` is equivalent to the vanishing of the corresponding same-cell rational selector error. -/
lemma sameCellSelectorError_tendsto_iff_targetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (φ n) (q n : NNReal) = partitionBoundIndex P (φ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            (φ n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) ↔
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            (φ n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
  constructor
  · intro hTarget
    -- Proof comment: once the row family already converges at the target horizon `T`, the
    -- same-cell boundary decomposition turns that limit into the selector-error limit.
    exact
      sameCellSelectorError_tendsto_of_targetConvergence
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P hφ q hqSame hqLt hqT hHωCont hωCont hTarget
  · intro hSelector
    -- Proof comment: conversely, a vanishing selector error plus the same-cell decomposition
    -- recovers the target-horizon convergence.
    exact
      targetConvergence_of_sameCellSelectorError
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P hφ q hqSame hqLt hqT hHωCont hωCont hSelector

/-- Helper for Exercise 25.2.1(ii): if a moving same-cell rational selector already approximates
the canonical Itô value along one strict-mono row family, then the corresponding moving target
row-point error also tends to `0`. -/
lemma movingTargetConvergence_of_sameCellSelectorError
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal} (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hSelectorErr :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            (χ n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (τ n)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
      atTop
      (𝓝 0) := by
  let targetSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (τ n)
      (χ n)
  let selectorSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (q n : NNReal)
      (χ n)
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (partitionPredecessorPointEarly P (χ n) (τ n)) ω *
      (M (τ n) ω - M (q n : NNReal) ω)
  have hSameCell :
      ∀ n : ℕ, targetSums n = selectorSums n + boundaryTerms n := by
    intro n
    -- Proof comment: same-cell horizons differ only by the last increment on the active cell.
    dsimp [targetSums, selectorSums, boundaryTerms]
    exact
      partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
        (le_of_lt (hqLt n)) (hqSame n)
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (χ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hχ.tendsto_atTop
  have hPred :
      Tendsto
        (fun n ↦ partitionPredecessorPointEarly P (χ n) (τ n))
        atTop
        (𝓝 T) := by
    rw [tendsto_iff_edist_tendsto_0] at hτT ⊢
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa using hmesh.add hτT)
        (fun n ↦ bot_le)
        ?_
    intro n
    calc
      edist (partitionPredecessorPointEarly P (χ n) (τ n)) T
          ≤ edist (partitionPredecessorPointEarly P (χ n) (τ n)) (τ n) + edist (τ n) T := by
              exact edist_triangle _ _ _
      _ ≤ partitionMesh P (χ n) + edist (τ n) T := by
            exact add_le_add (partitionPredecessorPointWithinMeshEarly P (χ n) (τ n)) le_rfl
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (χ n) (τ n)) ω)
        atTop
        (𝓝 (H T ω)) := by
    -- Proof comment: the sampled coefficient path is evaluated at predecessor times converging to
    -- the same limit `T`.
    exact hHωCont.continuousAt.tendsto.comp hPred
  have hPathTau :
      Tendsto (fun n ↦ M (τ n) ω) atTop (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hτT
  have hPathQ :
      Tendsto (fun n ↦ M (q n : NNReal) ω) atTop (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hqT
  have hIncrement :
      Tendsto
        (fun n ↦ M (τ n) ω - M (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: both moving endpoints converge to `T`, so the boundary increment vanishes.
    simpa using hPathTau.sub hPathQ
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    -- Proof comment: the coefficient stays bounded near `T`, while the moving boundary increment
    -- itself tends to `0`.
    simpa [boundaryTerms] using hCoeff.mul hIncrement
  have hSelectorTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hqT
  have hTargetTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hτT
  have hCanonicalGap :
      Tendsto
        (fun n ↦
          continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: continuity of the canonical Itô path transports both moving horizons to the
    -- same limit `T`.
    simpa using hSelectorTargets.sub hTargetTargets
  have hErrorEq :
      (fun n ↦ targetSums n - continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω) =
        (fun n ↦
          (selectorSums n - continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω) +
            boundaryTerms n +
              (continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω -
                continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)) := by
    funext n
    -- Proof comment: the moving target error is the selector error plus the same-cell boundary
    -- term and the canonical moving-horizon correction.
    linarith [hSameCell n]
  rw [hErrorEq]
  -- Proof comment: each of the three summands tends to `0`, so the moving target error does too.
  simpa [add_assoc] using (hSelectorErr.add hBoundary).add hCanonicalGap

/-- Helper for Exercise 25.2.1(ii): if the moving target error already tends to `0` along one
strict-mono row family, then the corresponding same-cell selector error also tends to `0`. -/
lemma sameCellSelectorError_tendsto_of_movingTargetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (_hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal} (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hMove :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (τ n)
            (χ n) -
              continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (q n : NNReal)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
      atTop
      (𝓝 0) := by
  let targetSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (τ n)
      (χ n)
  let selectorSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (q n : NNReal)
      (χ n)
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (partitionPredecessorPointEarly P (χ n) (τ n)) ω *
      (M (τ n) ω - M (q n : NNReal) ω)
  have hSameCell :
      ∀ n : ℕ, targetSums n = selectorSums n + boundaryTerms n := by
    intro n
    -- Proof comment: same-cell horizons differ only by the final increment on the common cell.
    dsimp [targetSums, selectorSums, boundaryTerms]
    exact
      partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
        (le_of_lt (hqLt n)) (hqSame n)
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (χ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp _hχ.tendsto_atTop
  have hPred :
      Tendsto
        (fun n ↦ partitionPredecessorPointEarly P (χ n) (τ n))
        atTop
        (𝓝 T) := by
    rw [tendsto_iff_edist_tendsto_0] at hτT ⊢
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa using hmesh.add hτT)
        (fun n ↦ bot_le)
        ?_
    intro n
    calc
      edist (partitionPredecessorPointEarly P (χ n) (τ n)) T
          ≤ edist (partitionPredecessorPointEarly P (χ n) (τ n)) (τ n) + edist (τ n) T := by
              exact edist_triangle _ _ _
      _ ≤ partitionMesh P (χ n) + edist (τ n) T := by
            exact add_le_add (partitionPredecessorPointWithinMeshEarly P (χ n) (τ n)) le_rfl
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (χ n) (τ n)) ω)
        atTop
        (𝓝 (H T ω)) := by
    -- Proof comment: the sampled coefficient is evaluated at predecessor times converging to `T`.
    exact hHωCont.continuousAt.tendsto.comp hPred
  have hPathTau :
      Tendsto (fun n ↦ M (τ n) ω) atTop (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hτT
  have hPathQ :
      Tendsto (fun n ↦ M (q n : NNReal) ω) atTop (𝓝 (M T ω)) :=
    (hM.continuous ω).continuousAt.tendsto.comp hqT
  have hIncrement :
      Tendsto
        (fun n ↦ M (τ n) ω - M (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: both moving endpoints converge to the same horizon `T`.
    simpa using hPathTau.sub hPathQ
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    -- Proof comment: a bounded coefficient times a vanishing last-cell increment still vanishes.
    simpa [boundaryTerms] using hCoeff.mul hIncrement
  have hSelectorTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hqT
  have hTargetTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hτT
  have hCanonicalGap :
      Tendsto
        (fun n ↦
          continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω -
            continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: the two canonical moving horizons are both transported to `T`.
    simpa using hTargetTargets.sub hSelectorTargets
  have hErrorEq :
      (fun n ↦
        selectorSums n -
          continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω) =
        (fun n ↦
          (targetSums n - continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω) -
            boundaryTerms n +
              (continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω -
                continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)) := by
    funext n
    -- Proof comment: expand the selector error into the moving-target error minus the boundary
    -- term plus the canonical moving-horizon correction.
    linarith [hSameCell n]
  rw [hErrorEq]
  -- Proof comment: the moving-target error, the boundary term, and the canonical gap all vanish.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hMove.sub hBoundary).add hCanonicalGap

/-- Helper for Exercise 25.2.1(ii): if the compact-horizon maximal row-point error does not
converge to `0` along a strict-mono row family, then after refining the rows one can choose
positive row points in `[0, N + 1]` that converge and still carry a uniform positive error. -/
private theorem rowPointMaxError_badSubsequence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω} (N : ℕ)
    (hbad :
      ¬ Tendsto
        (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (χ n) ω)
        atTop
        (𝓝 0)) :
    ∃ ε > 0, ∃ T ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal),
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ τ : ℕ → NNReal,
        Tendsto τ atTop (𝓝 T) ∧
        (∀ n : ℕ, 0 < τ n) ∧
        (∀ n : ℕ, τ n ≤ (N + 1 : NNReal)) ∧
        (∀ n : ℕ,
          ε ≤
            |partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (τ n)
                (χ (ρ n)) -
              continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω|) := by
  let e : ℕ → ℝ := fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (χ n) ω
  have hnonneg : ∀ n : ℕ, 0 ≤ e n := by
    intro n
    dsimp [e, rowPointMaxErrorUpTo]
    exact_mod_cast
      (show
        (0 : NNReal) ≤
          (Finset.range (partitionBoundIndex P (χ n) (N + 1 : NNReal))).sup
            (fun k ↦
              ‖partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  (P (χ n) k)
                  (χ n) -
                continuousLocalMartingaleItoIntegralProcess hM H (P (χ n) k) ω‖₊) from
        bot_le)
  rw [Metric.tendsto_atTop] at hbad
  push_neg at hbad
  rcases hbad with ⟨ε, hε, hbadε⟩
  have hfreq : ∃ᶠ n in atTop, ε ≤ e n := by
    rw [frequently_atTop]
    intro m
    rcases hbadε m with ⟨n, hmn, hnε⟩
    refine ⟨n, hmn, ?_⟩
    have hdist : ε ≤ dist (e n) 0 := hnε
    simpa [e, Real.dist_eq, hnonneg n, abs_of_nonneg] using hdist
  obtain ⟨ρ₀, hρ₀, hρ₀ε⟩ := extraction_of_frequently_atTop hfreq
  let rowErrorNnnorm : ℕ → ℕ → NNReal := fun row k ↦
    ‖partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
        P
        (P row k)
        row -
      continuousLocalMartingaleItoIntegralProcess hM H (P row k) ω‖₊
  have hchoose :
      ∀ n : ℕ,
        ∃ k : ℕ,
          k ∈ Finset.range (partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal)) ∧
            (Finset.range (partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal))).sup
              (rowErrorNnnorm (χ (ρ₀ n))) =
              rowErrorNnnorm (χ (ρ₀ n)) k := by
    intro n
    have hidx_ne_zero : partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal) ≠ 0 := by
      intro hzero
      have hNsucc_pos : (0 : NNReal) < (N + 1 : NNReal) := by
        exact_mod_cast Nat.succ_pos N
      have hNsucc_le_zero : (N + 1 : NNReal) ≤ 0 := by
        have hle : (N + 1 : NNReal) ≤ P (χ (ρ₀ n)) 0 := by
          simpa [hzero] using
            le_partitionBoundIndex_time P (χ (ρ₀ n)) (N + 1 : NNReal)
        simpa [hP.zero_eq (χ (ρ₀ n))] using hle
      exact (not_lt_of_ge hNsucc_le_zero) hNsucc_pos
    have hnonempty :
        (Finset.range (partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal))).Nonempty :=
      Finset.nonempty_range_iff.2 hidx_ne_zero
    exact
      Finset.exists_mem_eq_sup
        (Finset.range (partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal)))
        hnonempty
        (rowErrorNnnorm (χ (ρ₀ n)))
  choose k hkMem hkSup using hchoose
  let τ₀ : ℕ → NNReal := fun n ↦ P (χ (ρ₀ n)) (k n)
  have hkLt :
      ∀ n : ℕ, k n < partitionBoundIndex P (χ (ρ₀ n)) (N + 1 : NNReal) := by
    intro n
    exact Finset.mem_range.mp (hkMem n)
  have hrowEq :
      ∀ n : ℕ, e (ρ₀ n) =
        |partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (τ₀ n)
            (χ (ρ₀ n)) -
          continuousLocalMartingaleItoIntegralProcess hM H (τ₀ n) ω| := by
    intro n
    -- Proof comment: the chosen row point realizes the finite supremum defining the compact
    -- row-point error.
    dsimp [e, τ₀, rowPointMaxErrorUpTo, rowErrorNnnorm]
    simpa [rowErrorNnnorm, Real.norm_eq_abs] using
      congrArg (fun x : NNReal ↦ (x : ℝ)) (hkSup n)
  have hτ₀_pos : ∀ n : ℕ, 0 < τ₀ n := by
    intro n
    have hk_nonzero : k n ≠ 0 := by
      intro hk0
      have hzeroVal : e (ρ₀ n) = 0 := by
        rw [hrowEq n]
        dsimp [τ₀]
        rw [hk0]
        simp [τ₀, partitionPathwiseItoApproximationUpTo,
          IsAdmissiblePartitionSequence.zero_eq (P := P) (χ (ρ₀ n)),
          partitionBoundIndex_zero, continuousLocalMartingaleItoIntegralProcess_zero]
      have : ε ≤ 0 := by simpa [hzeroVal] using hρ₀ε n
      exact (not_le_of_gt hε) this
    have hk_pos : 0 < k n := Nat.pos_of_ne_zero hk_nonzero
    have hPk :
        P (χ (ρ₀ n)) 0 < P (χ (ρ₀ n)) (k n) :=
      (hP.strictMono (χ (ρ₀ n))) hk_pos
    simpa [τ₀, hP.zero_eq (χ (ρ₀ n))] using hPk
  have hτ₀_mem :
      ∀ n : ℕ, τ₀ n ∈ Set.Icc (0 : NNReal) (N + 1 : NNReal) := by
    intro n
    refine ⟨le_of_lt (hτ₀_pos n), ?_⟩
    exact le_of_lt <|
      partitionPoint_lt_time_of_lt_partitionBoundIndex
        P (χ (ρ₀ n)) (k n) (N + 1 : NNReal) (hkLt n)
  obtain ⟨T, hTmem, σ, hσ, hτ₀T⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) (N + 1 : NNReal))).tendsto_subseq hτ₀_mem
  refine ⟨ε, hε, T, hTmem, ρ₀ ∘ σ, hρ₀.comp hσ, τ₀ ∘ σ, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the compactness refinement makes the selected row points converge.
    simpa [Function.comp] using hτ₀T
  · intro n
    simpa [Function.comp] using hτ₀_pos (σ n)
  · intro n
    exact (hτ₀_mem (σ n)).2
  · intro n
    have hεn : ε ≤ e (ρ₀ (σ n)) := hρ₀ε (σ n)
    rw [hrowEq (σ n)] at hεn
    simpa [Function.comp] using hεn

/-- Helper for Exercise 25.2.1(ii): once the stage-`n` selector is constrained to a finite set
already controlled on row `σ n`, the corresponding selector error tends to `0`. -/
private theorem selectorError_tendsto_of_finiteSelectorControl
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} {ω : Ω}
    (S : ℕ → Finset ℚ≥0) (q : ℕ → ℚ≥0)
    (hqMem : ∀ n : ℕ, q n ∈ S n)
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            (χ (σ n)) -
              continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
  let u : ℚ≥0 → ℕ → ℝ := fun r n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (r : NNReal)
      (χ n)
  let l : ℚ≥0 → ℝ := fun r ↦
    continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω
  have hu : ∀ r : ℚ≥0, Tendsto (fun n ↦ u r n) atTop (𝓝 (l r)) := by
    intro r
    -- Proof comment: the fixed-rational convergence hypothesis is exactly the convergence of the
    -- family `u r` to its canonical limit `l r`.
    simpa [u, l] using hRat r
  obtain ⟨σ, hσ, hσcontrol⟩ :=
    existsStrictMono_diagonalControlOnFiniteSets S hu
  refine ⟨σ, hσ, ?_⟩
  have hdiag :
      ∀ n : ℕ,
        |u (q n) (σ n) - l (q n)| < 1 / (n + 1 : ℝ) := by
    intro n
    exact hσcontrol n (q n) (hqMem n)
  have hrate :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)) using 1
    funext n
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  have habs :
      Tendsto (fun n ↦ |u (q n) (σ n) - l (q n)|) atTop (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        hrate
        (fun n ↦ abs_nonneg _)
        (fun n ↦ by simpa [one_div] using le_of_lt (hdiag n))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- Proof comment: the stagewise singleton selector is squeezed by the deterministic rate
  -- `1 / (n + 1)`, so its error tends to `0`.
  simpa [u, l, Real.norm_eq_abs] using habs

/-- Helper for Exercise 25.2.1(ii): pointwise rational-time convergence along one row family can
be refined once so that all rational horizons converge simultaneously on the refined rows. -/
private theorem existsStrictMono_rationalTargetConvergenceAlongRows
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} {ω : Ω}
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              ((χ ∘ σ) n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
  let f : ℚ≥0 → ℕ → ℝ := fun r n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (r : NNReal)
      (χ n)
  let g : ℚ≥0 → ℝ := fun r ↦
    continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω
  obtain ⟨σ, hσRat⟩ :=
    existsStrictMonoSubsequence_tendstoOnEncodableFamily f g (fun r ↦ hRat r)
  refine ⟨σ.1, σ.2, ?_⟩
  intro r
  -- Proof comment: the diagonal subsequence theorem already stores the refined rational-time
  -- convergence coordinatewise; unpack it on the concrete pathwise Itô family.
  simpa [f, g, Function.comp] using hσRat r

/-- Helper for Exercise 25.2.1(ii): after refining a convergent row family on a compact horizon,
one should be able to choose same-cell rational selectors whose selector error already tends to
`0` along the refined rows. -/
private theorem sameCellApproximationDataWithSingletonSelectors
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ)
    {τ : ℕ → NNReal} {T : NNReal}
    (hτPos : ∀ n : ℕ, 0 < τ n)
    (hτT : Tendsto τ atTop (𝓝 T)) :
    ∃ S : ℕ → Finset ℚ≥0, ∃ q : ℕ → ℚ≥0,
      (∀ n : ℕ, q n ∈ S n) ∧
      (∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n)) ∧
      (∀ n : ℕ, (q n : NNReal) < τ n) ∧
      Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T) := by
  obtain ⟨q, hqSame, hqLt, hqT⟩ :=
    existsSameCellApproximationDataAlongConvergentRowPoints P hχ hτPos hτT
  refine ⟨fun n ↦ {q n}, q, ?_, ?_, ?_, ?_⟩
  · intro n
    -- Proof comment: the stagewise selector family can be packaged as singleton finite sets.
    simp
  · exact hqSame
  · exact hqLt
  · exact hqT

/-- Helper for Exercise 25.2.1(ii): after refining a convergent row family on a compact horizon,
one should be able to choose same-cell rational selectors whose selector error already tends to
`0` along the refined rows. -/
private lemma sameCellSelector_le_of_target_le
    {τ : ℕ → NNReal} {q : ℕ → ℚ≥0} {R : NNReal}
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hτLe : ∀ n : ℕ, τ n ≤ R) :
    ∀ n : ℕ, (q n : NNReal) ≤ R := by
  intro n
  -- Proof comment: every same-cell selector lies strictly before its moving target, so the
  -- compact target bound also bounds the selector.
  exact le_trans (le_of_lt (hqLt n)) (hτLe n)

/-- Helper for Exercise 25.2.1(ii): after refining a convergent row family on a compact horizon,
the same-cell rational selectors can already be packaged inside that same compact interval. -/
private theorem existsFiniteRowAlignedSameCellSelectorFamily
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ)
    {τ : ℕ → NNReal} {T R : NNReal}
    (hτPos : ∀ n : ℕ, 0 < τ n)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hτLe : ∀ n : ℕ, τ n ≤ R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ S : ℕ → Finset ℚ≥0, ∃ q : ℕ → ℚ≥0,
        (∀ n : ℕ, q n ∈ S n) ∧
        (∀ n : ℕ,
          partitionBoundIndex P ((χ ∘ σ) n) (q n : NNReal) =
            partitionBoundIndex P ((χ ∘ σ) n) ((τ ∘ σ) n)) ∧
        (∀ n : ℕ, (q n : NNReal) < (τ ∘ σ) n) ∧
        (∀ n : ℕ, (q n : NNReal) ≤ R) ∧
        Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T) := by
  obtain ⟨S, q, hqMem, hqSame, hqLt, hqT⟩ :=
    sameCellApproximationDataWithSingletonSelectors P hχ hτPos hτT
  have hqLe : ∀ n : ℕ, (q n : NNReal) ≤ R :=
    sameCellSelector_le_of_target_le hqLt hτLe
  -- Proof comment: the singleton-selector package already lives on the original row family, so
  -- the finite-control interface is satisfied with the identity refinement, and the compact
  -- horizon bound on `τ` immediately bounds the selected rationals as well.
  refine ⟨id, strictMono_id, S, q, hqMem, ?_, ?_, ?_, hqT⟩
  · intro n
    simpa [Function.comp] using hqSame n
  · intro n
    simpa [Function.comp] using hqLt n
  · exact hqLe

/-- Helper for Exercise 25.2.1(ii): after one finite selector family has been fixed on a row
family, one still needs an aligned diagonal refinement whose selected selector errors are already
indexed on the same final rows. -/
private theorem misalignedSelectorErrorSubsequence_of_finiteSelectorControl
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} {ω : Ω}
    (S : ℕ → Finset ℚ≥0) (q : ℕ → ℚ≥0)
    (hqMem : ∀ n : ℕ, q n ∈ S n)
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
  -- Proof comment: the finite-family diagonal theorem does prove vanishing selector error, but
  -- only for the misaligned surface `q n` evaluated on a later row `χ (σ n)`.
  simpa [Function.comp] using
    selectorError_tendsto_of_finiteSelectorControl
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (χ := χ) (ω := ω) S q hqMem hRat

/-- Helper for Exercise 25.2.1(ii): same-cell selector data and selector convergence transport
through a strict-mono refinement of the row indices. -/
private lemma sameCellApproximationDataAlongRefinementEarly
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hσ : StrictMono σ)
    {τ : ℕ → NNReal} {T : NNReal} (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T)) :
    (∀ n : ℕ,
      partitionBoundIndex P ((χ ∘ σ) n) (q (σ n) : NNReal) =
        partitionBoundIndex P ((χ ∘ σ) n) ((τ ∘ σ) n)) ∧
    (∀ n : ℕ, (q (σ n) : NNReal) < (τ ∘ σ) n) ∧
    Tendsto (fun n ↦ (q (σ n) : NNReal)) atTop (𝓝 T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [Function.comp] using hqSame (σ n)
  · intro n
    simpa [Function.comp] using hqLt (σ n)
  · simpa [Function.comp] using hqT.comp hσ.tendsto_atTop

/-- Helper for Exercise 25.2.1(ii): rational-time convergence is preserved after refining the row
family by a strict-mono map. -/
private lemma rationalTargetConvergenceAlongRefinementEarly
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hσ : StrictMono σ) {ω : Ω}
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    ∀ r : ℚ≥0,
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (r : NNReal)
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
  intro r
  simpa [Function.comp] using (hRat r).comp hσ.tendsto_atTop

/-- Helper for Exercise 25.2.1(ii): one strict-mono refinement simultaneously transports the
same-cell selector data, the moving target, and the rational-time convergence hypotheses used by
the aligned selector-error argument. -/
private lemma movingSelectorDataAlongRefinementEarly
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hσ : StrictMono σ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal} (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    (∀ n : ℕ,
      partitionBoundIndex P ((χ ∘ σ) n) (q (σ n) : NNReal) =
        partitionBoundIndex P ((χ ∘ σ) n) ((τ ∘ σ) n)) ∧
    (∀ n : ℕ, (q (σ n) : NNReal) < (τ ∘ σ) n) ∧
    Tendsto (fun n ↦ (q (σ n) : NNReal)) atTop (𝓝 T) ∧
    Tendsto (τ ∘ σ) atTop (𝓝 T) ∧
    (∀ r : ℚ≥0,
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (r : NNReal)
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) := by
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinementEarly
      (P := P) (χ := χ) (σ := σ) hσ (τ := τ) q hqSame hqLt hqT
  refine ⟨hqSameRef, hqLtRef, hqTRef, ?_, ?_⟩
  · simpa [Function.comp] using hτT.comp hσ.tendsto_atTop
  · exact
      rationalTargetConvergenceAlongRefinementEarly
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P (χ := χ) (σ := σ) (ω := ω) hσ hRat

/-- Helper for Exercise 25.2.1(ii): on a compact horizon, simultaneous convergence at every
nonnegative rational target upgrades to convergence at a bounded moving target. -/
private theorem movingTargetConvergenceOnCompact_of_rationalTargetConvergenceEarly
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T R : NNReal}
    (hτLe : ∀ n : ℕ, τ n ≤ R)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (τ n)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
      atTop
      (𝓝 0) := by
  let predecessorTimes : ℕ → NNReal := fun n ↦ partitionPredecessorPointEarly P (χ n) (τ n)
  let predecessorSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (predecessorTimes n)
      (χ n)
  let predecessorTargets : ℕ → ℝ := fun n ↦
    continuousLocalMartingaleItoIntegralProcess hM H (predecessorTimes n) ω
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (predecessorTimes n) ω *
      (M (τ n) ω - M (predecessorTimes n) ω)
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (χ n)) atTop (𝓝 0) :=
    IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P) |>.comp hχ.tendsto_atTop
  have hPred :
      Tendsto predecessorTimes atTop (𝓝 T) := by
    rw [tendsto_iff_edist_tendsto_0] at hτT ⊢
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa [predecessorTimes] using hmesh.add hτT)
        (fun n ↦ bot_le)
        ?_
    intro n
    calc
      edist (predecessorTimes n) T
          ≤ edist (predecessorTimes n) (τ n) + edist (τ n) T := by
              exact edist_triangle _ _ _
      _ ≤ partitionMesh P (χ n) + edist (τ n) T := by
            exact add_le_add
              (by
                dsimp [predecessorTimes]
                exact partitionPredecessorPointWithinMeshEarly P (χ n) (τ n))
              le_rfl
  have hRowMax :
      Tendsto
        (fun n ↦ rowPointMaxErrorUpTo hM H P R (χ n) ω)
        atTop
        (𝓝 0) :=
    rowPointMaxErrorUpTo_tendsto_of_rationalTargetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ (ω := ω) (R := R) hRat hHωCont hωCont
  have hPredErrAbs :
      ∀ n : ℕ,
        |predecessorSums n - predecessorTargets n| ≤
          rowPointMaxErrorUpTo hM H P R (χ n) ω := by
    intro n
    dsimp [predecessorSums, predecessorTargets, predecessorTimes]
    exact
      predecessorPointError_le_rowPointMaxErrorUpTo
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P (hτLe n) (χ n) ω
  have hPredErr :
      Tendsto (fun n ↦ predecessorSums n - predecessorTargets n) atTop (𝓝 0) := by
    have hLower :
        Tendsto
          (fun n ↦ -rowPointMaxErrorUpTo hM H P R (χ n) ω)
          atTop
          (𝓝 0) := by
      simpa using hRowMax.neg
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        hLower hRowMax ?_ ?_
    · intro n
      exact (abs_le.mp (hPredErrAbs n)).1
    · intro n
      exact (abs_le.mp (hPredErrAbs n)).2
  have hPredTargets :
      Tendsto predecessorTargets atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    exact hωCont.continuousAt.tendsto.comp hPred
  have hPredSums :
      Tendsto predecessorSums atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    have hSum :
        Tendsto
          (fun n ↦
            (predecessorSums n - predecessorTargets n) + predecessorTargets n)
          atTop
          (𝓝 (0 + continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      hPredErr.add hPredTargets
    simpa [predecessorSums, predecessorTargets, sub_add_cancel] using hSum
  have hCoeff :
      Tendsto (fun n ↦ H (predecessorTimes n) ω) atTop (𝓝 (H T ω)) := by
    exact hHωCont.continuousAt.tendsto.comp hPred
  have hPathPred :
      Tendsto (fun n ↦ M (predecessorTimes n) ω) atTop (𝓝 (M T ω)) := by
    exact (hM.continuous ω).continuousAt.tendsto.comp hPred
  have hPathTau :
      Tendsto (fun n ↦ M (τ n) ω) atTop (𝓝 (M T ω)) := by
    exact (hM.continuous ω).continuousAt.tendsto.comp hτT
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    have hIncrement :
        Tendsto (fun n ↦ M (τ n) ω - M (predecessorTimes n) ω) atTop (𝓝 0) := by
      simpa [predecessorTimes] using hPathTau.sub hPathPred
    simpa [boundaryTerms] using hCoeff.mul hIncrement
  have hTargetTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hτT
  have hPredCentered :
      Tendsto
        (fun n ↦ predecessorSums n -
          continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 0) := by
    have hPredCentered' :
        Tendsto
          (fun n ↦ predecessorSums n -
            continuousLocalMartingaleItoIntegralProcess hM H T ω)
          atTop
          (𝓝
            (continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      hPredSums.sub tendsto_const_nhds
    simpa using hPredCentered'
  have hCanonicalGap :
      Tendsto
        (fun n ↦
          continuousLocalMartingaleItoIntegralProcess hM H T ω -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 0) := by
    have hCanonicalGap' :
        Tendsto
          (fun n ↦
            continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
          atTop
          (𝓝
            (continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      tendsto_const_nhds.sub hTargetTargets
    simpa using hCanonicalGap'
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (τ n)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω) =
        (fun n ↦
          (predecessorSums n -
            continuousLocalMartingaleItoIntegralProcess hM H T ω) +
              boundaryTerms n +
                (continuousLocalMartingaleItoIntegralProcess hM H T ω -
                  continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)) := by
    funext n
    have hDecomp :
        partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (τ n)
            (χ n) =
          predecessorSums n + boundaryTerms n := by
      dsimp [predecessorSums, predecessorTimes, boundaryTerms]
      exact
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
    linarith [hDecomp]
  rw [hEq]
  simpa [add_assoc] using (hPredCentered.add hBoundary).add hCanonicalGap

/-- Helper for Exercise 25.2.1(ii): the bad-subsequence contradiction needs an earlier aligned
selector-error subsequence theorem on the current row family, with the selector and the row both
refined by the same strict-mono map. -/
private theorem existsAlignedSelectorErrorSubsequenceAlongRows
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q (σ n) : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
        atTop
        (𝓝 0) := by
  obtain ⟨σRat, hσRat, hRatRef⟩ :=
    existsStrictMono_rationalTargetConvergenceAlongRows
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P (χ := χ) (ω := ω) hRat
  let χRef : ℕ → ℕ := χ ∘ σRat
  have hχRef : StrictMono χRef := hχ.comp hσRat
  obtain ⟨hqSameRef, hqLtRef, hqTRef, hτTRef, hRatRef'⟩ :=
    movingSelectorDataAlongRefinementEarly
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hσRat (χ := χ) (σ := σRat) (ω := ω) (τ := τ) (T := T) q
      hqSame hqLt hqT hτT hRat
  have hT_lt_T_add_one : T < T + 1 := by
    exact lt_add_of_pos_right T (show (0 : NNReal) < (1 : NNReal) by norm_num)
  have hEventuallyLe :
      ∀ᶠ n in atTop, (τ ∘ σRat) n ≤ T + 1 := by
    refine (hτTRef.eventually (Iio_mem_nhds hT_lt_T_add_one)).mono ?_
    intro n hn
    exact le_of_lt hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventuallyLe
  let σTail : ℕ → ℕ := fun n ↦ n + N
  have hσTail : StrictMono σTail := strictMono_id.add_const N
  let χTail : ℕ → ℕ := χRef ∘ σTail
  let qRef : ℕ → ℚ≥0 := q ∘ σRat
  let τRef : ℕ → NNReal := τ ∘ σRat
  have hRatTail :
      ∀ r : ℚ≥0,
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χTail n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
    have hTailPack :=
      movingSelectorDataAlongRefinementEarly
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P hσTail (χ := χRef) (σ := σTail) (ω := ω) (τ := τRef) (T := T) qRef
        hqSameRef hqLtRef hqTRef hτTRef hRatRef'
    -- Proof comment: once the rational-time convergence is synchronized on `χRef`, a further
    -- tail refinement preserves the same rational-time limits on the final rows.
    intro r
    exact hTailPack.2.2.2.2 r
  have hτTailLe : ∀ n : ℕ, (τRef ∘ σTail) n ≤ T + 1 := by
    intro n
    exact hN (σTail n) (by
      simpa [σTail, Nat.add_comm] using Nat.le_add_right N n)
  have hMove :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            ((τRef ∘ σTail) n)
            (χTail n) -
              continuousLocalMartingaleItoIntegralProcess hM H ((τRef ∘ σTail) n) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: after discarding a finite prefix, the moving targets stay in the compact
    -- interval `[0, T + 1]`, so the compact-horizon moving-target theorem applies.
    exact
      movingTargetConvergenceOnCompact_of_rationalTargetConvergenceEarly
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P (χ := χTail) (τ := τRef ∘ σTail) (T := T) (R := T + 1)
        (hχRef.comp hσTail) hτTailLe
        (hτTRef.comp hσTail.tendsto_atTop)
        hRatTail hHωCont hωCont
  obtain ⟨hqSameTail, hqLtTail, hqTTail, _hτTTail, _hRatTail⟩ :=
    movingSelectorDataAlongRefinementEarly
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hσTail (χ := χRef) (σ := σTail) (ω := ω) (τ := τRef) (T := T) qRef
      hqSameRef hqLtRef hqTRef hτTRef hRatRef'
  refine ⟨σRat ∘ σTail, hσRat.comp hσTail, ?_⟩
  -- Proof comment: the compact moving-target limit on the aligned tail rows converts back to the
  -- desired selector error by the previously proved same-cell transport lemma.
  simpa [χTail, χRef, qRef, τRef, Function.comp] using
    sameCellSelectorError_tendsto_of_movingTargetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχRef.comp hσTail) (q := qRef ∘ σTail)
      hqSameTail hqLtTail hqTTail
      (hτTRef.comp hσTail.tendsto_atTop)
      hHωCont hωCont hMove

/-- Helper for Exercise 25.2.1(ii): once fixed-target convergence at `T` is already available on
one refined row family, the same-cell selector error on that same refined family also tends to
`0`. -/
private theorem alignedSelectorError_tendsto_of_targetConvergenceOnRefinementEarly
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hχ : StrictMono χ) (hσ : StrictMono σ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hTarget :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω))) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (q (σ n) : NNReal)
          ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
      atTop
      (𝓝 0) := by
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinementEarly
      (P := P) (χ := χ) (σ := σ) hσ (τ := fun _ ↦ T) q
      hqSame hqLt hqT
  -- Proof comment: after composing both the selector and the row family with the same
  -- refinement, the already proved fixed-target same-cell selector theorem applies directly.
  simpa [Function.comp] using
    sameCellSelectorError_tendsto_of_targetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχ.comp hσ) (q := q ∘ σ)
      (hqSame := hqSameRef)
      (hqLt := hqLtRef)
      (hqT := hqTRef)
      hHωCont hωCont hTarget

/-- Helper for Exercise 25.2.1(ii): once an aligned selector-error subsequence is already
available on the final refined rows, the same-cell transport theorem upgrades it to the moving
target convergence needed in the bad-subsequence contradiction. -/
private lemma movingTargetConvergence_of_alignedSelectorErrorEarly
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hχ : StrictMono χ) (hσ : StrictMono σ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hSelectorErr :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q (σ n) : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          ((τ ∘ σ) n)
          ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω)
      atTop
      (𝓝 0) := by
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinementEarly
      (P := P) (χ := χ) (σ := σ) hσ (τ := τ) q hqSame hqLt hqT
  -- Proof comment: after transporting the same-cell data to the final refined rows, the earlier
  -- moving-target theorem applies directly with no further row bookkeeping.
  simpa [Function.comp] using
    movingTargetConvergence_of_sameCellSelectorError
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχ.comp hσ) (q := q ∘ σ)
      hqSameRef hqLtRef hqTRef
      (hτT.comp hσ.tendsto_atTop)
      hHωCont hωCont hSelectorErr

/-- Helper for Exercise 25.2.1(ii): the bad-subsequence contradiction only needs a final-row
moving-target limit on one refined row family, so the helper should target that surface directly
instead of first asking for an under-premised aligned selector-error theorem. -/
private theorem badSubsequenceMovingTargetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal}
    {R : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτLe : ∀ n : ℕ, τ n ≤ R)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            ((τ ∘ σ) n)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω)
        atTop
        (𝓝 0) := by
  obtain ⟨σ, hσ, hSelectorErr⟩ :=
    existsAlignedSelectorErrorSubsequenceAlongRows
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ (ω := ω) (τ := τ) (T := T) q hqSame hqLt hqT hτT hRat hHωCont hωCont
  refine ⟨σ, hσ, ?_⟩
  -- Proof comment: the new early refinement helper isolates the same-cell transport, so the bad
  -- subsequence proof only has to invoke the aligned selector-error theorem and this final
  -- moving-target upgrade.
  simpa [Function.comp] using
    movingTargetConvergence_of_alignedSelectorErrorEarly
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ hσ (q := q) hqSame hqLt hqT hτT hHωCont hωCont hSelectorErr

/-- Helper for Exercise 25.2.1(ii): same-cell selector data and selector convergence transport
through a strict-mono refinement of the row indices. -/
private lemma sameCellApproximationDataAlongRefinement
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hσ : StrictMono σ)
    {τ : ℕ → NNReal} {T : NNReal} (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T)) :
    (∀ n : ℕ,
      partitionBoundIndex P ((χ ∘ σ) n) (q (σ n) : NNReal) =
        partitionBoundIndex P ((χ ∘ σ) n) ((τ ∘ σ) n)) ∧
    (∀ n : ℕ, (q (σ n) : NNReal) < (τ ∘ σ) n) ∧
    Tendsto (fun n ↦ (q (σ n) : NNReal)) atTop (𝓝 T) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the same-cell index identity is stable under composing both the selector
    -- and the row map with the same strict-mono refinement.
    intro n
    simpa [Function.comp] using hqSame (σ n)
  · -- Proof comment: strict inequality of the selector against the moving horizon is pointwise,
    -- so refinement only reindexes the same statement.
    intro n
    simpa [Function.comp] using hqLt (σ n)
  · -- Proof comment: convergence of the selector sequence to `T` is preserved by any
    -- strict-mono subsequence.
    simpa [Function.comp] using hqT.comp hσ.tendsto_atTop

/-- Helper for Exercise 25.2.1(ii): once an aligned selector-error subsequence is already
available on the final refined rows, the same-cell transport theorem upgrades it to the moving
target convergence needed for the bad-subsequence contradiction. -/
private lemma movingTargetConvergence_of_alignedSelectorError
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hχ : StrictMono χ) (hσ : StrictMono σ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) =
          partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hSelectorErr :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q (σ n) : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          ((τ ∘ σ) n)
          ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω)
      atTop
      (𝓝 0) := by
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinement
      (P := P) (χ := χ) (σ := σ) hσ (τ := τ) q
      hqSame hqLt hqT
  -- Proof comment: after transporting the same-cell identities to the final refined rows, the
  -- previously proved same-cell moving-target theorem applies directly.
  simpa [Function.comp] using
    movingTargetConvergence_of_sameCellSelectorError
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχ.comp hσ) (q := q ∘ σ)
      hqSameRef hqLtRef hqTRef
      (hτT.comp hσ.tendsto_atTop)
      hHωCont hωCont hSelectorErr

/-- Helper for Exercise 25.2.1(ii): once a strict-mono refinement already converges at the fixed
target horizon `T`, the same-cell selector error on that refined row family also tends to `0`. -/
private theorem alignedSelectorError_tendsto_of_targetConvergenceOnRefinement
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hχ : StrictMono χ) (hσ : StrictMono σ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hTarget :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω))) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (q (σ n) : NNReal)
          ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
      atTop
      (𝓝 0) := by
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinement
      (P := P) (χ := χ) (σ := σ) hσ (τ := fun _ ↦ T) q
      hqSame hqLt hqT
  -- Proof comment: after composing both the selector and the row family with the same
  -- refinement, the earlier fixed-target same-cell selector theorem applies without any new
  -- transport work.
  simpa [Function.comp] using
    sameCellSelectorError_tendsto_of_targetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχ.comp hσ) (q := q ∘ σ)
      (hqSame := hqSameRef)
      (hqLt := hqLtRef)
      (hqT := hqTRef)
      hHωCont hωCont hTarget

/-- Helper for Exercise 25.2.1(ii): rational-time convergence is preserved after refining the row
family by a strict-mono map. -/
private lemma rationalTargetConvergenceAlongRefinement
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hσ : StrictMono σ) {ω : Ω}
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω))) :
    ∀ r : ℚ≥0,
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (r : NNReal)
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
  intro r
  -- Proof comment: refining the row family only composes the original rational-time convergence
  -- with the strict-mono tail map.
  simpa [Function.comp] using (hRat r).comp hσ.tendsto_atTop

/-- Helper for Exercise 25.2.1(ii): simultaneous rational-time convergence on one compact horizon
should force the row-point maximal error on that compact interval to vanish. -/
private theorem rowPointMaxErrorUpTo_tendsto_of_rationalTargetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω} {R : NNReal}
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    Tendsto
      (fun n ↦ rowPointMaxErrorUpTo hM H P R (χ n) ω)
      atTop
      (𝓝 0) := by
  let N : ℕ := Nat.ceil R
  have hRle : R ≤ (N + 1 : NNReal) := by
    have hRceil : R ≤ (N : NNReal) := by
      simpa [N] using (Nat.le_ceil R)
    exact le_trans hRceil (le_add_of_nonneg_right (show (0 : NNReal) ≤ 1 by norm_num))
  have hNonneg :
      ∀ n : ℕ, 0 ≤ rowPointMaxErrorUpTo hM H P R (χ n) ω := by
    intro n
    dsimp [rowPointMaxErrorUpTo]
    exact_mod_cast
      (show
        (0 : NNReal) ≤
          (Finset.range (partitionBoundIndex P (χ n) R)).sup
            (fun k ↦
              ‖partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  (P (χ n) k)
                  (χ n) -
                continuousLocalMartingaleItoIntegralProcess hM H (P (χ n) k) ω‖₊) from
        bot_le)
  have hLarge :
      Tendsto
        (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (χ n) ω)
        atTop
        (𝓝 0) := by
    by_contra hBad
    obtain ⟨ε, hε, T, hTmem, ρ, hρ, τ, hτT, hτPos, hτLe, hLower⟩ :=
      rowPointMaxError_badSubsequence
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P hχ (ω := ω) N hBad
    let χρ : ℕ → ℕ := χ ∘ ρ
    have hχρ : StrictMono χρ := hχ.comp hρ
    obtain ⟨σ, hσ, _, q, _, hqSame, hqLt, _, hqT⟩ :=
      existsFiniteRowAlignedSameCellSelectorFamily
        (P := P) (χ := χρ) hχρ hτPos hτT hτLe
    have hRatRef :
        ∀ r : ℚ≥0,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (r : NNReal)
                (((χρ ∘ σ) n)))
            atTop
            (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
      -- Proof comment: after passing to the bad-row subsequence `ρ` and then to the geometric
      -- refinement `σ`, rational-time convergence is preserved by the composed strict-mono row
      -- map.
      simpa [χρ, Function.comp] using
        rationalTargetConvergenceAlongRefinement
          (μ := μ) (ℱ := ℱ) (M := M) (H := H)
          hM P (χ := χ) (σ := ρ ∘ σ) (ω := ω) (hρ.comp hσ) hRat
    obtain ⟨ν, hν, hMove⟩ :=
      badSubsequenceMovingTargetConvergence
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P (((hχρ.comp hσ))) (χ := χρ ∘ σ) (ω := ω)
        (τ := τ ∘ σ) (T := T) (R := N + 1) q hqSame hqLt hqT
        (fun n ↦ hτLe (σ n))
        (hτT.comp hσ.tendsto_atTop) hRatRef hHωCont hωCont
    have hAbsMove :
        Tendsto
          (fun n ↦
            |partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (((τ ∘ σ) ∘ ν) n)
                (((χρ ∘ σ) ∘ ν) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (((τ ∘ σ) ∘ ν) n) ω|)
          atTop
          (𝓝 0) := by
      simpa [Real.norm_eq_abs] using hMove.norm
    have hLowerRef :
        ∀ n : ℕ,
          ε ≤
            |partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (((τ ∘ σ) ∘ ν) n)
                (((χρ ∘ σ) ∘ ν) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (((τ ∘ σ) ∘ ν) n) ω| := by
      intro n
      simpa [χρ, Function.comp] using hLower (σ (ν n))
    have hEventuallyBig :
        ∀ᶠ n in atTop,
          ε ≤
            |partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                (((τ ∘ σ) ∘ ν) n)
                (((χρ ∘ σ) ∘ ν) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (((τ ∘ σ) ∘ ν) n) ω| :=
      Filter.Eventually.of_forall hLowerRef
    have hEventuallySmall :
        ∀ᶠ n in atTop,
          |partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (((τ ∘ σ) ∘ ν) n)
              (((χρ ∘ σ) ∘ ν) n) -
            continuousLocalMartingaleItoIntegralProcess hM H (((τ ∘ σ) ∘ ν) n) ω| < ε :=
      hAbsMove.eventually (Iio_mem_nhds hε)
    have hFalse : ∀ᶠ n in atTop, False :=
      (hEventuallyBig.and hEventuallySmall).mono fun n hn ↦
        (not_lt_of_ge hn.1 hn.2).elim
    exact Filter.atTop_neBot.ne (Filter.eventually_false_iff_eq_bot.mp hFalse)
  have hLe :
      ∀ n : ℕ,
        rowPointMaxErrorUpTo hM H P R (χ n) ω ≤
          rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (χ n) ω := by
    intro n
    exact rowPointMaxErrorUpTo_le_of_le hM P hRle (χ n) ω
  -- Proof comment: first control the compact error on the larger integer horizon `N + 1`,
  -- where the bad-subsequence contradiction is available, and then squeeze the original compact
  -- horizon `R` underneath it.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hLarge
      hNonneg
      hLe

/-- Helper for Exercise 25.2.1(ii): after one geometric selector family `S, q` has been fixed on
one strict-mono row family, the remaining analytic frontier is a final-row-aligned diagonal
subsequence along which the selected rational `q (σ n)` is already controlled on that same final
row `χ (σ n)`. -/
private theorem sameCellSelectorError_tendsto_of_targetConvergenceAlongRefinement
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ σ : ℕ → ℕ} (hχ : StrictMono χ) (hσ : StrictMono σ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hTarget :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            ((χ ∘ σ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω))) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (q (σ n) : NNReal)
          ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
      atTop
      (𝓝 0) := by
  -- Proof comment: the dedicated refinement helper isolates exactly this fixed-target transport
  -- step, so the later compact-horizon argument can reuse it without repeating the same-cell
  -- bookkeeping.
  exact
    alignedSelectorError_tendsto_of_targetConvergenceOnRefinement
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ hσ q hqSame hqLt hqT hHωCont hωCont hTarget

/-- Helper for Exercise 25.2.1(ii): on a compact horizon, simultaneous convergence at every
nonnegative rational target should upgrade to convergence at a bounded moving target. -/
private theorem movingTargetConvergenceOnCompact_of_rationalTargetConvergence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T R : NNReal}
    (hτLe : ∀ n : ℕ, τ n ≤ R)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (τ n)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
      atTop
      (𝓝 0) := by
  let predecessorTimes : ℕ → NNReal := fun n ↦ partitionPredecessorPointEarly P (χ n) (τ n)
  let predecessorSums : ℕ → ℝ := fun n ↦
    partitionPathwiseItoApproximationUpTo
      (fun t ↦ H t ω)
      (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
      P
      (predecessorTimes n)
      (χ n)
  let predecessorTargets : ℕ → ℝ := fun n ↦
    continuousLocalMartingaleItoIntegralProcess hM H (predecessorTimes n) ω
  let boundaryTerms : ℕ → ℝ := fun n ↦
    H (predecessorTimes n) ω *
      (M (τ n) ω - M (predecessorTimes n) ω)
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (χ n)) atTop (𝓝 0) :=
    IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P) |>.comp hχ.tendsto_atTop
  have hPred :
      Tendsto predecessorTimes atTop (𝓝 T) := by
    -- Proof comment: predecessor times differ from the moving targets by at most one partition
    -- mesh, and the mesh disappears along every admissible row subsequence.
    rw [tendsto_iff_edist_tendsto_0] at hτT ⊢
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa [predecessorTimes] using hmesh.add hτT)
        (fun n ↦ bot_le)
        ?_
    intro n
    calc
      edist (predecessorTimes n) T
          ≤ edist (predecessorTimes n) (τ n) + edist (τ n) T := by
              exact edist_triangle _ _ _
      _ ≤ partitionMesh P (χ n) + edist (τ n) T := by
            exact add_le_add
              (by
                dsimp [predecessorTimes]
                exact partitionPredecessorPointWithinMeshEarly P (χ n) (τ n))
              le_rfl
  have hRowMax :
      Tendsto
        (fun n ↦ rowPointMaxErrorUpTo hM H P R (χ n) ω)
        atTop
        (𝓝 0) :=
    rowPointMaxErrorUpTo_tendsto_of_rationalTargetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ (ω := ω) (R := R) hRat hHωCont hωCont
  have hPredErrAbs :
      ∀ n : ℕ,
        |predecessorSums n - predecessorTargets n| ≤
          rowPointMaxErrorUpTo hM H P R (χ n) ω := by
    intro n
    dsimp [predecessorSums, predecessorTargets, predecessorTimes]
    exact
      predecessorPointError_le_rowPointMaxErrorUpTo
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P (hτLe n) (χ n) ω
  have hPredErr :
      Tendsto (fun n ↦ predecessorSums n - predecessorTargets n) atTop (𝓝 0) := by
    have hLower :
        Tendsto
          (fun n ↦ -rowPointMaxErrorUpTo hM H P R (χ n) ω)
          atTop
          (𝓝 0) := by
      simpa using hRowMax.neg
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        hLower hRowMax ?_ ?_
    · intro n
      exact (abs_le.mp (hPredErrAbs n)).1
    · intro n
      exact (abs_le.mp (hPredErrAbs n)).2
  have hPredTargets :
      Tendsto predecessorTargets atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    -- Proof comment: continuity of the canonical Itô path transports the predecessor horizons to
    -- the common target time `T`.
    exact hωCont.continuousAt.tendsto.comp hPred
  have hPredSums :
      Tendsto predecessorSums atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
    have hSum :
        Tendsto
          (fun n ↦
            (predecessorSums n - predecessorTargets n) + predecessorTargets n)
          atTop
          (𝓝 (0 + continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      hPredErr.add hPredTargets
    -- Proof comment: the predecessor approximation is the sum of a vanishing row-point error and
    -- the continuous canonical target along the predecessor times.
    simpa [predecessorSums, predecessorTargets, sub_add_cancel] using hSum
  have hCoeff :
      Tendsto (fun n ↦ H (predecessorTimes n) ω) atTop (𝓝 (H T ω)) := by
    -- Proof comment: the coefficient path is continuous and the predecessor times converge to `T`.
    exact hHωCont.continuousAt.tendsto.comp hPred
  have hPathPred :
      Tendsto (fun n ↦ M (predecessorTimes n) ω) atTop (𝓝 (M T ω)) := by
    exact (hM.continuous ω).continuousAt.tendsto.comp hPred
  have hPathTau :
      Tendsto (fun n ↦ M (τ n) ω) atTop (𝓝 (M T ω)) := by
    exact (hM.continuous ω).continuousAt.tendsto.comp hτT
  have hBoundary :
      Tendsto boundaryTerms atTop (𝓝 0) := by
    have hIncrement :
        Tendsto (fun n ↦ M (τ n) ω - M (predecessorTimes n) ω) atTop (𝓝 0) := by
      -- Proof comment: both path evaluations converge to `M T ω`, so the last-cell increment
      -- vanishes.
      simpa [predecessorTimes] using hPathTau.sub hPathPred
    -- Proof comment: the coefficient path stays continuous at the predecessor points while the
    -- last-cell increment itself tends to `0`.
    simpa [boundaryTerms] using hCoeff.mul hIncrement
  have hTargetTargets :
      Tendsto
        (fun n ↦ continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    canonicalItoIntegral_selector_tendsto_of_continuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hωCont hτT
  have hPredCentered :
      Tendsto
        (fun n ↦ predecessorSums n -
          continuousLocalMartingaleItoIntegralProcess hM H T ω)
        atTop
        (𝓝 0) := by
    have hPredCentered' :
        Tendsto
          (fun n ↦ predecessorSums n -
            continuousLocalMartingaleItoIntegralProcess hM H T ω)
          atTop
          (𝓝
            (continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      hPredSums.sub tendsto_const_nhds
    simpa using hPredCentered'
  have hCanonicalGap :
      Tendsto
        (fun n ↦
          continuousLocalMartingaleItoIntegralProcess hM H T ω -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: continuity of the canonical Itô path transports the moving horizons to the
    -- same deterministic target `T`.
    have hCanonicalGap' :
        Tendsto
          (fun n ↦
            continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)
          atTop
          (𝓝
            (continuousLocalMartingaleItoIntegralProcess hM H T ω -
              continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
      tendsto_const_nhds.sub hTargetTargets
    simpa using hCanonicalGap'
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          (τ n)
          (χ n) -
            continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω) =
        (fun n ↦
          (predecessorSums n -
            continuousLocalMartingaleItoIntegralProcess hM H T ω) +
              boundaryTerms n +
                (continuousLocalMartingaleItoIntegralProcess hM H T ω -
                  continuousLocalMartingaleItoIntegralProcess hM H (τ n) ω)) := by
    funext n
    have hDecomp :
        partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (τ n)
            (χ n) =
          predecessorSums n + boundaryTerms n := by
      -- Proof comment: each moving-target partition sum is the predecessor-horizon sum plus the
      -- last boundary contribution from the active cell.
      dsimp [predecessorSums, predecessorTimes, boundaryTerms]
      exact
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
    linarith [hDecomp]
  rw [hEq]
  -- Proof comment: predecessor error, boundary increment, and canonical horizon transport all
  -- vanish, so the compact moving-target error tends to `0`.
  simpa [add_assoc] using (hPredCentered.add hBoundary).add hCanonicalGap

/-- Helper for Exercise 25.2.1(ii): once the same-cell selector sequence `q n → T` is fixed on a
strict-mono row family `χ`, the real dense-time frontier is the moving-target version where the
same-cell identities are tracked against the convergent horizon sequence `τ`. -/
private theorem existsAlignedMovingSelectorErrorSubsequence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) (τ n))
    (hqLt : ∀ n : ℕ, (q n : NNReal) < τ n)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q (σ n) : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
        atTop
        (𝓝 0) := by
  obtain ⟨σRat, hσRat, hRatRef⟩ :=
    existsStrictMono_rationalTargetConvergenceAlongRows
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P (χ := χ) (ω := ω) hRat
  let χRef : ℕ → ℕ := χ ∘ σRat
  have hχRef : StrictMono χRef := hχ.comp hσRat
  obtain ⟨hqSameRef, hqLtRef, hqTRef, hτTRef, hRatRef'⟩ :=
    movingSelectorDataAlongRefinementEarly
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hσRat (χ := χ) (σ := σRat) (ω := ω) (τ := τ) (T := T) q
      hqSame hqLt hqT hτT hRat
  have hT_lt_T_add_one : T < T + 1 := by
    exact lt_add_of_pos_right T (show (0 : NNReal) < (1 : NNReal) by norm_num)
  have hEventuallyLe :
      ∀ᶠ n in atTop, (τ ∘ σRat) n ≤ T + 1 := by
    refine (hτTRef.eventually (Iio_mem_nhds hT_lt_T_add_one)).mono ?_
    intro n hn
    exact le_of_lt hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventuallyLe
  let σTail : ℕ → ℕ := fun n ↦ n + N
  have hσTail : StrictMono σTail := strictMono_id.add_const N
  let χTail : ℕ → ℕ := χRef ∘ σTail
  let qRef : ℕ → ℚ≥0 := q ∘ σRat
  let τRef : ℕ → NNReal := τ ∘ σRat
  have hRatTail :
      ∀ r : ℚ≥0,
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χTail n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
    have hTailPack :=
      movingSelectorDataAlongRefinementEarly
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P hσTail (χ := χRef) (σ := σTail) (ω := ω) (τ := τRef) (T := T) qRef
        hqSameRef hqLtRef hqTRef hτTRef hRatRef'
    -- Proof comment: once the rational-time convergence is synchronized on `χRef`, a further
    -- tail refinement preserves the same rational-time limits on the final rows.
    intro r
    exact hTailPack.2.2.2.2 r
  have hτTailLe : ∀ n : ℕ, (τRef ∘ σTail) n ≤ T + 1 := by
    intro n
    exact hN (σTail n) (by
      simpa [σTail, Nat.add_comm] using Nat.le_add_right N n)
  have hMove :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            ((τRef ∘ σTail) n)
            (χTail n) -
              continuousLocalMartingaleItoIntegralProcess hM H ((τRef ∘ σTail) n) ω)
        atTop
        (𝓝 0) := by
    -- Proof comment: after discarding a finite prefix, the moving targets stay in the compact
    -- interval `[0, T + 1]`, so the compact-horizon moving-target theorem applies.
    exact
      movingTargetConvergenceOnCompact_of_rationalTargetConvergenceEarly
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM P (χ := χTail) (τ := τRef ∘ σTail) (T := T) (R := T + 1)
        (hχRef.comp hσTail) hτTailLe
        (hτTRef.comp hσTail.tendsto_atTop)
        hRatTail hHωCont hωCont
  obtain ⟨hqSameTail, hqLtTail, hqTTail, _hτTTail, _hRatTail⟩ :=
    movingSelectorDataAlongRefinementEarly
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hσTail (χ := χRef) (σ := σTail) (ω := ω) (τ := τRef) (T := T) qRef
      hqSameRef hqLtRef hqTRef hτTRef hRatRef'
  refine ⟨σRat ∘ σTail, hσRat.comp hσTail, ?_⟩
  -- Proof comment: the compact moving-target limit on the aligned tail rows converts back to the
  -- desired selector error by the previously proved same-cell transport lemma.
  simpa [χTail, χRef, qRef, τRef, Function.comp] using
    sameCellSelectorError_tendsto_of_movingTargetConvergence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P (hχRef.comp hσTail) (q := qRef ∘ σTail)
      hqSameTail hqLtTail hqTTail
      (hτTRef.comp hσTail.tendsto_atTop)
      hHωCont hωCont hMove

/-- Helper for Exercise 25.2.1(ii): the fixed-target aligned selector theorem is now just the
constant-horizon specialization of the moving-target blocker above. -/
private theorem existsAlignedSelectorErrorSubsequence
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω} {T : NNReal}
    (q : ℕ → ℚ≥0)
    (hqSame :
      ∀ n : ℕ,
        partitionBoundIndex P (χ n) (q n : NNReal) = partitionBoundIndex P (χ n) T)
    (hqLt : ∀ n : ℕ, (q n : NNReal) < T)
    (hqT : Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T))
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q (σ n) : NNReal)
            ((χ ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H (q (σ n) : NNReal) ω)
        atTop
        (𝓝 0) := by
  -- Route correction: the finite-selector diagonal only controls `q n` on a later row, which is
  -- too weak for the same-cell transport API. The new moving-target theorem packages the missing
  -- aligned diagonal once and this fixed-`T` surface is now only a specialization.
  simpa using
    existsAlignedMovingSelectorErrorSubsequence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ (τ := fun _ ↦ T) q
      hqSame hqLt hqT tendsto_const_nhds hRat hHωCont hωCont

/-- Helper for Exercise 25.2.1(ii): after refining a convergent row family on a compact horizon,
the dense-time contradiction should be closed directly on the final aligned rows, using
continuity only at that last stage. -/
private theorem existsControlledSameCellSelectorErrorAlongConvergentRowPoints
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {χ : ℕ → ℕ} (hχ : StrictMono χ) {ω : Ω}
    {τ : ℕ → NNReal} {T R : NNReal}
    (hτPos : ∀ n : ℕ, 0 < τ n)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hτLe : ∀ n : ℕ, τ n ≤ R)
    (hRat :
      ∀ r : ℚ≥0,
        Tendsto
        (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (r : NNReal)
              (χ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)))
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ q : ℕ → ℚ≥0,
        (∀ n : ℕ,
          partitionBoundIndex P ((χ ∘ σ) n) (q n : NNReal) =
            partitionBoundIndex P ((χ ∘ σ) n) ((τ ∘ σ) n)) ∧
        (∀ n : ℕ, (q n : NNReal) < (τ ∘ σ) n) ∧
        Tendsto (fun n ↦ (q n : NNReal)) atTop (𝓝 T) ∧
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (q n : NNReal)
            ((χ ∘ σ) n) -
            continuousLocalMartingaleItoIntegralProcess hM H (q n : NNReal) ω)
        atTop
        (𝓝 0) := by
  -- Route correction: the old selector-only diagonal lived below the continuity hypotheses and
  -- therefore kept reintroducing the `q n` versus `q (σ n)` mismatch after the geometric
  -- refinement. The remaining work is now isolated in the aligned subsequence helper below.
  obtain ⟨q, hqSame, hqLt, hqT⟩ :=
    existsSameCellApproximationDataAlongConvergentRowPoints P hχ hτPos hτT
  obtain ⟨σ, hσ, hSelectorErr⟩ :=
    existsAlignedMovingSelectorErrorSubsequence
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hχ (τ := τ) q hqSame hqLt hqT hτT hRat hHωCont hωCont
  obtain ⟨hqSameRef, hqLtRef, hqTRef⟩ :=
    sameCellApproximationDataAlongRefinement
      (P := P) (χ := χ) (σ := σ) hσ (τ := τ) q
      hqSame hqLt hqT
  refine ⟨σ, hσ, q ∘ σ, hqSameRef, hqLtRef, hqTRef, ?_⟩
  -- Proof comment: after packaging the aligned selector as `q ∘ σ`, the extracted aligned
  -- selector-error limit already has exactly the statement shape required by the outer theorem.
  simpa [Function.comp] using hSelectorErr

/-- Helper for Exercise 25.2.1(ii): the samplewise dense-time frontier only needs continuity of
the coefficient path, continuity of the canonical Itô path, and rational-time convergence along
the base row subsequence `φ`. -/
private theorem refinedSubseq_rowPointMaxErrorUpTo_of_ratContinuous
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hωRat :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (q : NNReal)
              (φ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (q : NNReal) ω))) :
    ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
        ∀ N : ℕ,
          Tendsto
            (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ (ψ (ρ n))) ω)
            atTop
            (𝓝 0) := by
  intro ψ hψ
  let χ : ℕ → ℕ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  refine ⟨id, strictMono_id, ?_⟩
  intro N
  let e : ℕ → ℝ := fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (χ n) ω
  have hConv : Tendsto e atTop (𝓝 0) := by
    refine tendsto_of_refinedRowMapCriterion_local ?_
    intro η hη
    by_cases hηgood : Tendsto (fun n ↦ e (η n)) atTop (𝓝 0)
    · refine ⟨id, strictMono_id, ?_⟩
      simpa [e] using hηgood
    · exfalso
      obtain ⟨ε, hε, T, hTmem, ρ₀, hρ₀, τ, hτT, hτPos, hτLe, hLower⟩ :=
        rowPointMaxError_badSubsequence
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P
          ((hχ.comp hη)) N (by simpa [e, χ, Function.comp] using hηgood)
      have hχηρ : StrictMono (χ ∘ η ∘ ρ₀) := hχ.comp (hη.comp hρ₀)
      have hRatRef :
          ∀ r : ℚ≥0,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  (r : NNReal)
                  ((χ ∘ η ∘ ρ₀) n))
              atTop
              (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (r : NNReal) ω)) := by
        intro r
        have hψηρ : StrictMono (ψ ∘ η ∘ ρ₀) := hψ.comp (hη.comp hρ₀)
        simpa [χ, Function.comp] using (hωRat r).comp hψηρ.tendsto_atTop
      obtain ⟨σ, hσ, q, hqSame, hqLt, hqT, hSelectorErr⟩ :=
        existsControlledSameCellSelectorErrorAlongConvergentRowPoints
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hχηρ
          hτPos hτT hτLe hRatRef hHωCont hωCont
      have hχηρσ : StrictMono ((χ ∘ η ∘ ρ₀) ∘ σ) := hχηρ.comp hσ
      have hMove :
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                ((τ ∘ σ) n)
                (((χ ∘ η ∘ ρ₀) ∘ σ) n) -
                  continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω)
            atTop
            (𝓝 0) := by
        -- Proof comment: once the selector package is aligned with the final refined rows, the
        -- moving-target theorem turns the selector-error limit into the target-error limit.
        exact
          movingTargetConvergence_of_sameCellSelectorError
            (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hχηρσ q
            hqSame
            hqLt
            hqT
            (hτT.comp hσ.tendsto_atTop)
            hHωCont hωCont hSelectorErr
      have hAbs :
          Tendsto
            (fun n ↦
              |partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  ((τ ∘ σ) n)
                  (((χ ∘ η ∘ ρ₀) ∘ σ) n) -
                continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω|)
            atTop
            (𝓝 0) := by
        -- Proof comment: the contradiction uses the absolute-value form recorded by the bad
        -- subsequence extractor.
        simpa [Real.norm_eq_abs, Function.comp] using hMove.norm
      have hEventuallyLt :
          ∀ᶠ n in atTop,
            |partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                ((τ ∘ σ) n)
                (((χ ∘ η ∘ ρ₀) ∘ σ) n) -
              continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω| < ε := by
        -- Proof comment: convergence to `0` forces the absolute error below the fixed positive
        -- threshold `ε` eventually.
        have hBall :
            ∀ᶠ n in atTop,
              partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  ((τ ∘ σ) n)
                  (((χ ∘ η ∘ ρ₀) ∘ σ) n) -
                continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω ∈
                  Metric.ball 0 ε := by
          exact hMove.eventually (Metric.ball_mem_nhds _ hε)
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hBall
      have hEventuallyGe :
          ∀ᶠ n in atTop,
            ε ≤
              |partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  ((τ ∘ σ) n)
                  (((χ ∘ η ∘ ρ₀) ∘ σ) n) -
                continuousLocalMartingaleItoIntegralProcess hM H ((τ ∘ σ) n) ω| :=
        Filter.Eventually.of_forall fun n ↦ by
          simpa [Function.comp] using hLower (σ n)
      have hFalse : ∀ᶠ n in atTop, False :=
        (hEventuallyLt.and hEventuallyGe).mono fun n hn ↦
          (not_lt_of_ge hn.2) hn.1
      have hbot : (atTop : Filter ℕ) = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp hFalse
      exact Filter.atTop_neBot.ne hbot
  -- Proof comment: for each compact horizon `[0, N + 1]`, the bad-subsequence extractor and the
  -- moving-target transport reduce convergence to the single selector-alignment frontier above.
  simpa [e, χ, Function.comp] using hConv

/-- Helper for Exercise 25.2.1(ii): rational-time almost-sure convergence admits a refined
subsequence criterion whose compact-horizon row-point error vanishes on every integer interval. -/
theorem refinedSubseq_rowPointMaxErrorUpTo_ae
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hφRat :
      ∀ᵐ ω ∂μ, ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              (q : NNReal)
              (φ n))
          atTop
          (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H (q : NNReal) ω))) :
    ∀ᵐ ω ∂μ,
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
          ∀ N : ℕ,
            Tendsto
              (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ (ψ (ρ n))) ω)
              atTop
              (𝓝 0) := by
  have hItoCont :
      ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω := by
    -- Proof comment: the canonical Itô realization already has almost surely continuous paths.
    exact
      canonicalItoIntegral_hasAeContinuousPaths
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hFiniteEnergy
  filter_upwards [hItoCont, hφRat] with ω hωCont hωRat ψ hψ
  -- Proof comment: once the sample point `ω` carries both continuity witnesses and all rational-
  -- time limits along `φ`, the remaining dense-time step is the samplewise compact-horizon
  -- refinement theorem isolated above.
  exact
    refinedSubseq_rowPointMaxErrorUpTo_of_ratContinuous
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hφ (hH_cont ω) hωCont hωRat ψ hψ

/-- Helper for Exercise 25.2.1(ii): once every strict-mono subsequence admits a further
refinement with vanishing compact-horizon row-point error, the target-horizon partition sums
converge to the canonical Itô value at every deterministic time. -/
theorem pathwiseAllTimesPartitionApproximation_of_nnrat
    {M H : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ω : Ω}
    (hHωCont : Continuous fun t : NNReal ↦ H t ω)
    (hωCont : Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω)
    (hRowMax :
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
          ∀ N : ℕ,
            Tendsto
              (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ (ψ (ρ n))) ω)
              atTop
              (𝓝 0))
    (T : NNReal) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          (φ n))
      atTop
      (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  -- Proof comment: the repaired dense-time route avoids the broken moving-selector diagonal.
  -- Instead, every strict-mono subsequence is refined until the compact-horizon row-point error
  -- vanishes, and then the existing predecessor/boundary lemmas close the target horizon.
  refine tendsto_of_refinedRowMapCriterion_local ?_
  intro ψ hψ
  obtain ⟨ρ, hρ, hρMax⟩ := hRowMax ψ hψ
  have hRows : StrictMono (φ ∘ ψ ∘ ρ) := hφ.comp (hψ.comp hρ)
  have hPred :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            (partitionPredecessorPointEarly P ((φ ∘ ψ ∘ ρ) n) T)
            ((φ ∘ ψ ∘ ρ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    predecessorApproximation_tendsto_of_rowPointMax
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hRows hωCont
      (fun N ↦ hρMax N) T
  have hTarget :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            ((φ ∘ ψ ∘ ρ) n))
        atTop
        (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) :=
    pathwiseTargetFromPredecessorApproximation
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM P hRows hHωCont hPred
  refine ⟨ρ, hρ, ?_⟩
  simpa [Function.comp] using hTarget

/-- Exercise 25.2.1(ii): there is a strict-mono partition-row subsequence along which the
pathwise Itô left-point sums converge almost surely at every horizon to the canonical Itô
integral process. -/
theorem exists_partitionSubsequence_with_ae_pathwise_itoApproximation
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                T
                (φ n))
            atTop
            (𝓝 (continuousLocalMartingaleItoIntegralProcess hM H T ω)) := by
  -- Route correction: the restored proof first rebuilds the rational-time diagonal subsequence,
  -- then delegates the remaining frontiers to the two named helper theorems above.
  have hApprox :
      ∀ T : NNReal,
        TendstoInMeasure μ
          (fun n ω ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              P
              T
              n)
          atTop
          (continuousLocalMartingaleItoIntegralProcess hM H T) :=
    tendstoInMeasure_partitionItoApproximationUpTo
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM hbr hH_prog hH_cont hFiniteEnergy P
  obtain ⟨φ, hφ, hφRat⟩ :=
    existsStrictMonoSubsequence_tendstoAeOnNNRat_partitionItoApproximation
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      (I := continuousLocalMartingaleItoIntegralProcess hM H)
      hM P hApprox
  have hItoCont :
      ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ continuousLocalMartingaleItoIntegralProcess hM H t ω := by
    -- Proof comment: the canonical Chapter 25 owner surface already packages finite-horizon
    -- continuous local martingale witnesses; assembling those interval by interval yields global
    -- almost-sure continuity.
    exact
      canonicalItoIntegral_hasAeContinuousPaths
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hFiniteEnergy
  have hRowMax :
      ∀ᵐ ω ∂μ,
        ∀ ψ : ℕ → ℕ, StrictMono ψ →
          ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
            ∀ N : ℕ,
              Tendsto
                (fun n ↦ rowPointMaxErrorUpTo hM H P (N + 1 : NNReal) (φ (ψ (ρ n))) ω)
                atTop
                (𝓝 0) := by
    exact
      refinedSubseq_rowPointMaxErrorUpTo_ae
        (μ := μ) (ℱ := ℱ) (M := M) (H := H)
        hM hbr hH_prog hH_cont hFiniteEnergy P hφ hφRat
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hItoCont, hRowMax] with ω hωCont hωRowMax T
  -- Proof comment: once the canonical path is continuous and every subsequence has a refined
  -- compact-horizon row-max control, the repaired dense-time helper yields convergence at `T`.
  exact
    pathwiseAllTimesPartitionApproximation_of_nnrat
      (μ := μ) (ℱ := ℱ) (M := M) (H := H)
      hM P hφ (hH_cont ω) hωCont hωRowMax T

end ProbabilityTheory
