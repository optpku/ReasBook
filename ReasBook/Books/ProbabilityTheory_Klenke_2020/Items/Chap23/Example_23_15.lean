/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_13

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

/-- Helper for Example 23.15: the chapter's speed parameter `(n + 1)⁻¹` is strictly positive. -/
theorem finiteAlphabetSpeed_pos (n : ℕ) : 0 < ((n + 1 : ℝ)⁻¹) := by
  have hn : 0 < (n + 1 : ℝ) := by
    positivity
  simpa using inv_pos.mpr hn

/-- Helper for Example 23.15: package the chapter's speed `(n + 1)⁻¹` as a positive parameter. -/
def finiteAlphabetSpeed (n : ℕ) : PositiveParameter :=
  ⟨((n + 1 : ℝ)⁻¹), finiteAlphabetSpeed_pos n⟩

/-- The first-moment map on probability measures supported on a finite alphabet `α`, computed from
the coordinate realization `v : α → Fin d → ℝ`. -/
def finiteAlphabetFirstMoment {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {d : ℕ} [Fintype α] (v : α → Fin d → ℝ) (ν : ProbabilityMeasure α) : Fin d → ℝ :=
  fun i ↦ ∑ a, ((ν {a} : NNReal) : ℝ) * v a i

/-- The fiber of the first-moment map above the vector `x`. -/
def finiteAlphabetMomentFiber {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {d : ℕ} [Fintype α] (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    Set (ProbabilityMeasure α) :=
  {ν | finiteAlphabetFirstMoment v ν = x}

/-- The contraction rate obtained from Sanov's theorem by minimizing relative entropy over all
probability measures on `α` with prescribed first moment `x`. -/
def finiteAlphabetSanovRateFunction {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    ENNReal :=
  sInf ((fun ν : ProbabilityMeasure α ↦
    InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) '' finiteAlphabetMomentFiber v x)

/-- The logarithmic moment generating function `Λ` of a finite-alphabet law `μ` pushed forward by
the coordinate realization `v`. -/
def finiteAlphabetLogMomentGeneratingFunction {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) (t : Fin d → ℝ) : ℝ :=
  Real.log <| ∑ a, ((μ {a} : NNReal) : ℝ) * Real.exp (∑ i, t i * v a i)

/-- The Legendre-transform rate function `Λ*` attached to the finite-alphabet law `μ`. -/
def finiteAlphabetLegendreRateFunction {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) (x : Fin d → ℝ) : ENNReal :=
  ((sSup (Set.range fun t : Fin d → ℝ ↦
    (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal)))).toENNReal

/-- Expanding `finiteAlphabetLegendreRateFunction μ v x` gives the Legendre-transform supremum of
`⟨t, x⟩ - Λ(t)` over all `t ∈ ℝ^d`, encoded as `Fin d → ℝ`. -/
theorem finiteAlphabetLegendreRateFunction_def {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    finiteAlphabetLegendreRateFunction μ v x =
      ((sSup
        (Set.range fun t : Fin d → ℝ ↦
          (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) :
            EReal)))).toENNReal := by
  rfl

/-- The `0`-based partial sum of the vectors `v (X 0), …, v (X n)`. -/
def finiteAlphabetPartialSum {Ω : Type u} [MeasurableSpace Ω] {α : Type v} [MeasurableSpace α]
    {d : ℕ} (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) : Ω → Fin d → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (n + 1), v (X i ω)

/-- The empirical mean of the first `n + 1` variables in the chapter's `0`-based indexing. -/
def finiteAlphabetEmpiricalMean {Ω : Type u} [MeasurableSpace Ω] {α : Type v} [MeasurableSpace α]
    {d : ℕ} (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) : Ω → Fin d → ℝ :=
  fun ω ↦ (n + 1 : ℝ)⁻¹ • finiteAlphabetPartialSum v X n ω

/-- Expanding `finiteAlphabetEmpiricalMean v X n` gives the normalized `0`-based partial sum
`(n + 1)⁻¹ ∑_{i=0}^n v (X i)`. -/
theorem finiteAlphabetEmpiricalMean_apply {Ω : Type u} [MeasurableSpace Ω] {α : Type v}
    [MeasurableSpace α] {d : ℕ} (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    finiteAlphabetEmpiricalMean v X n ω =
      (n + 1 : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), v (X i ω) := by
  rfl

/-- The empirical mean map of a finite-alphabet sequence is a.e.-measurable under the reference
probability measure. -/
theorem finiteAlphabetEmpiricalMean_aemeasurable {Ω : Type u} [MeasurableSpace Ω] {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Finite α]
    (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω)) (n : ℕ) :
    AEMeasurable (finiteAlphabetEmpiricalMean v X n) (P : Measure Ω) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hv : Measurable v := measurable_of_finite v
  have hPartial :
      AEMeasurable (finiteAlphabetPartialSum v X n) (P : Measure Ω) := by
    simpa [finiteAlphabetPartialSum] using
      (Finset.range (n + 1)).aemeasurable_fun_sum fun i _ ↦
        hv.comp_aemeasurable (hXmeas i)
  simpa [finiteAlphabetEmpiricalMean] using hPartial.const_smul ((n + 1 : ℝ)⁻¹)

/-- The law of the empirical mean of the first `n + 1` variables. -/
def finiteAlphabetEmpiricalMeanLaw {Ω : Type u} [MeasurableSpace Ω] {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω)) (n : ℕ) :
    ProbabilityMeasure (Fin d → ℝ) :=
  P.map (finiteAlphabetEmpiricalMean_aemeasurable P v X hXmeas n)

/-- Helper for Example 23.15: an a.e.-measurable independent sequence with common law `μ` admits
a measurable version that preserves both independence and the one-coordinate laws. -/
theorem measurableIndependentVersionWithLaw {Ω : Type u} [MeasurableSpace Ω] {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : ProbabilityMeasure Ω)
    (μ : ProbabilityMeasure α) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω))
    (hindep : iIndepFun X (P : Measure Ω))
    (hLaw : ∀ n, Measure.map (X n) (P : Measure Ω) = (μ : Measure α)) :
    ∃ Y : ℕ → Ω → α,
      (∀ n, Measurable (Y n)) ∧
      (∀ n, X n =ᵐ[(P : Measure Ω)] Y n) ∧
      iIndepFun Y (P : Measure Ω) ∧
      (∀ n, Measure.map (Y n) (P : Measure Ω) = (μ : Measure α)) := by
  let Y : ℕ → Ω → α := fun n ↦ (hXmeas n).mk (X n)
  have hYmeas : ∀ n, Measurable (Y n) := by
    intro n
    exact (hXmeas n).measurable_mk
  have hYae : ∀ n, X n =ᵐ[(P : Measure Ω)] Y n := by
    intro n
    exact (hXmeas n).ae_eq_mk
  have hYindep : iIndepFun Y (P : Measure Ω) := by
    exact hindep.congr hYae
  have hYlaw : ∀ n, Measure.map (Y n) (P : Measure Ω) = (μ : Measure α) := by
    intro n
    calc
      Measure.map (Y n) (P : Measure Ω) = Measure.map (X n) (P : Measure Ω) := by
        simpa using (Measure.map_congr (hYae n).symm)
      _ = (μ : Measure α) := hLaw n
  exact ⟨Y, hYmeas, hYae, hYindep, hYlaw⟩

/-- Helper for Example 23.15: summing a weight against the empirical histogram of a finite word
recovers the corresponding sample sum. -/
theorem weightedEmpiricalCount_sum {α : Type v} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {n : ℕ} (x : Fin (n + 1) → α) :
    ∑ a, (empiricalCount (n + 1) x a : ℝ) * f a = ∑ i : Fin (n + 1), f (x i) := by
  classical
  -- Proof comment: rewrite each histogram weight as a sum over the corresponding fiber, then use
  -- the standard fiberwise summation identity.
  calc
    ∑ a, (empiricalCount (n + 1) x a : ℝ) * f a
        = ∑ a, ∑ _i : {i // x i = a}, f a := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            simp [empiricalCount, nsmul_eq_mul, mul_comm]
    _ = ∑ i : Fin (n + 1), f (x i) := by
          simpa using (Fintype.sum_fiberwise' x f)

/-- Helper for Example 23.15: taking the first moment of the empirical distribution gives the
empirical mean of the realized vectors. -/
theorem finiteAlphabetFirstMoment_empiricalDistribution_eq_empiricalMean
    {Ω : Type u} [MeasurableSpace Ω] {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (v : α → Fin d → ℝ)
    (Y : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    finiteAlphabetFirstMoment v (empiricalDistribution (Nat.succPNat n) (fun i ↦ Y i) ω) =
      finiteAlphabetEmpiricalMean v Y n ω := by
  classical
  ext i
  rw [finiteAlphabetFirstMoment, finiteAlphabetEmpiricalMean_apply, Pi.smul_apply]
  -- Proof comment: each singleton mass of the empirical distribution is a normalized count, so
  -- the first-moment sum collapses to the average of the observed coordinates.
  have hMass :
      ∀ a : α,
        (((empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω) {a} : NNReal) : ℝ) =
          (n + 1 : ℝ)⁻¹ *
            (empiricalCount (n + 1) (fun j : Fin (n + 1) ↦ Y j ω) a : ℝ) := by
    intro a
    have hApply :
        (empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω : Measure α) {a} =
          ((empiricalCount (n + 1) (fun j : Fin (n + 1) ↦ Y j ω) a : ℕ) : ENNReal) /
            ((n + 1 : ℕ) : ENNReal) := by
      simpa [Nat.succPNat, Nat.succ_eq_add_one] using
        empiricalWordDistribution_apply_singleton
          (S := α) (hn := Nat.succ_ne_zero n)
          (x := fun j : Fin (n + 1) ↦ Y j ω) a
    have hReal :
        ((empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω : Measure α) {a}).toReal =
          (n + 1 : ℝ)⁻¹ *
            (empiricalCount (n + 1) (fun j : Fin (n + 1) ↦ Y j ω) a : ℝ) := by
      simpa [div_eq_mul_inv, ENNReal.toReal_div, ENNReal.toReal_natCast, mul_comm, mul_left_comm,
        mul_assoc] using congrArg ENNReal.toReal hApply
    have hMeasureReal :
        ((empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω : Measure α) {a}).toReal =
          (((empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω) {a} : NNReal) : ℝ) := by
      simpa [Measure.real] using
        (ProbabilityMeasure.measureReal_eq_coe_coeFn
          (ν := empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω) ({a} : Set α)).symm
    exact hMeasureReal.symm.trans hReal
  calc
    ∑ a, (((empiricalDistribution (Nat.succPNat n) (fun j ↦ Y j) ω) {a} : NNReal) : ℝ) * v a i
        = ∑ a,
            ((n + 1 : ℝ)⁻¹ *
              (empiricalCount (n + 1) (fun j : Fin (n + 1) ↦ Y j ω) a : ℝ)) * v a i := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [hMass a]
    _ = (n + 1 : ℝ)⁻¹ *
          ∑ a, (empiricalCount (n + 1) (fun j : Fin (n + 1) ↦ Y j ω) a : ℝ) * v a i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            ring
    _ = (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1), v (Y j ω) i := by
          rw [weightedEmpiricalCount_sum (f := fun a ↦ v a i)
            (x := fun j : Fin (n + 1) ↦ Y j ω)]
    _ = (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1), v (Y j ω) i := by
          rw [← Fin.sum_univ_eq_sum_range]
    _ = ((n + 1 : ℝ)⁻¹ • ∑ j ∈ Finset.range (n + 1), v (Y j ω)) i := by
          simp [Pi.smul_apply]

/-- Helper for Example 23.15: replacing the sample sequence coordinatewise by an a.e.-equal
version preserves the law of each empirical mean. -/
theorem finiteAlphabetEmpiricalMeanLaw_congr_ae {Ω : Type u} [MeasurableSpace Ω] {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ)
    (X Y : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω))
    (hYmeas : ∀ n, AEMeasurable (Y n) (P : Measure Ω))
    (hXY : ∀ n, X n =ᵐ[(P : Measure Ω)] Y n) :
    ∀ n, finiteAlphabetEmpiricalMeanLaw P v X hXmeas n =
      finiteAlphabetEmpiricalMeanLaw P v Y hYmeas n := by
  intro n
  have hSumAe :
      (fun ω ↦ ∑ i ∈ Finset.range (n + 1), v (X i ω)) =ᵐ[(P : Measure Ω)]
        fun ω ↦ ∑ i ∈ Finset.range (n + 1), v (Y i ω) := by
    -- Proof comment: equality of the sample coordinates propagates through the finite prefix sum.
    induction n with
    | zero =>
        filter_upwards [hXY 0] with ω hω
        simp [hω]
    | succ n ih =>
        filter_upwards [ih, hXY (n + 1)] with ω hsum hcoord
        simp [Finset.sum_range_succ, hsum, hcoord]
  have hMeanAe :
      finiteAlphabetEmpiricalMean v X n =ᵐ[(P : Measure Ω)] finiteAlphabetEmpiricalMean v Y n := by
    -- Proof comment: scaling the equal prefix sums by the deterministic factor `(n + 1)⁻¹`
    -- preserves the a.e. equality.
    filter_upwards [hSumAe] with ω hω
    simp [finiteAlphabetEmpiricalMean_apply, hω]
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: pushforwards of a measure along a.e.-equal maps coincide.
  simpa [finiteAlphabetEmpiricalMeanLaw] using Measure.map_congr hMeanAe

/-- Helper for Example 23.15: the singleton mass of a probability measure varies continuously in
the weak topology on a finite discrete alphabet. -/
theorem continuousFiniteAlphabetSingletonMassReal {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]
    [Finite α] (a : α) :
    Continuous fun ν : ProbabilityMeasure α ↦ (ν : Measure α).real {a} := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let f : BoundedContinuousFunction α ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun x : α ↦ if x = a then 1 else 0) 1 <| by
        intro x
        by_cases hx : x = a
        · simp [hx]
        · simp [hx]
  have hEq :
      (fun ν : ProbabilityMeasure α ↦ (ν : Measure α).real {a}) =
        fun ν : ProbabilityMeasure α ↦ ∫ x, f x ∂(ν : Measure α) := by
    funext ν
    -- Proof comment: on a finite discrete alphabet, only the singleton `{a}` contributes to the
    -- integral of the indicator test function `f`.
    rw [MeasureTheory.integral_fintype (μ := (ν : Measure α)) (f := fun x : α ↦ f x)
      (BoundedContinuousFunction.integrable (ν : Measure α) f)]
    simp [f, smul_eq_mul]
  rw [hEq]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

/-- Helper for Example 23.15: the first-moment map is continuous on the finite-alphabet
probability-measure space. -/
theorem continuous_finiteAlphabetFirstMoment {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]
    {d : ℕ} [Fintype α] (v : α → Fin d → ℝ) :
    Continuous (finiteAlphabetFirstMoment v) := by
  -- Proof comment: each coordinate is a finite sum of continuous singleton-mass coordinates.
  refine continuous_pi fun i ↦ ?_
  have hCoord :
      Continuous fun ν : ProbabilityMeasure α ↦
        ∑ a, (ν : Measure α).real {a} * v a i := by
    refine continuous_finset_sum _ fun a _ ↦ ?_
    exact (continuousFiniteAlphabetSingletonMassReal (a := a)).mul continuous_const
  simpa [finiteAlphabetFirstMoment, Measure.real] using hCoord

/-- Helper for Example 23.15: the first-moment map is measurable for the Giry measurable space on
`ProbabilityMeasure α`. -/
theorem measurable_finiteAlphabetFirstMoment {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (v : α → Fin d → ℝ) :
    Measurable (finiteAlphabetFirstMoment v) := by
  -- Proof comment: each coordinate is a finite sum of measurable singleton-mass evaluations.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [finiteAlphabetFirstMoment, Measure.real] using
    (Finset.measurable_sum Finset.univ fun a _ =>
      (((Measure.measurable_coe (measurableSet_singleton a)).ennreal_toReal).comp
        measurable_subtype_coe).mul measurable_const)

/-- Helper for Example 23.15: evaluating the empirical-mean law on a measurable set is the same as
evaluating the empirical-measure law on the corresponding first-moment preimage. -/
theorem finiteAlphabetEmpiricalMeanLaw_apply_eq_empiricalMeasureLaw_preimage
    {Ω : Type u} [MeasurableSpace Ω] {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]
    {d : ℕ} [Fintype α] (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ)
    (Y : ℕ → Ω → α) (hYmeas : ∀ n, Measurable (Y n))
    (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) (n : ℕ) :
    ((finiteAlphabetEmpiricalMeanLaw P v Y (fun n ↦ (hYmeas n).aemeasurable) n :
        Measure (Fin d → ℝ)) s) =
      ((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n : Measure (ProbabilityMeasure α))
        ((finiteAlphabetFirstMoment v) ⁻¹' s)) := by
  have hPreimage :
      MeasurableSet ((finiteAlphabetFirstMoment v) ⁻¹' s) :=
    (measurable_finiteAlphabetFirstMoment (v := v)) hs
  -- Proof comment: rewrite both laws as pushforwards of `P` and identify the two preimages using
  -- the empirical-distribution/empirical-mean normalization lemma.
  calc
    ((finiteAlphabetEmpiricalMeanLaw P v Y (fun n ↦ (hYmeas n).aemeasurable) n :
        Measure (Fin d → ℝ)) s)
        = (P : Measure Ω) ((finiteAlphabetEmpiricalMean v Y n) ⁻¹' s) := by
            rw [finiteAlphabetEmpiricalMeanLaw]
            simpa using
              (ProbabilityMeasure.map_apply'
                P
                (finiteAlphabetEmpiricalMean_aemeasurable P v Y
                  (fun n ↦ (hYmeas n).aemeasurable) n)
                hs)
    _ = (P : Measure Ω)
          ((fun ω ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ Y i) ω) ⁻¹'
            ((finiteAlphabetFirstMoment v) ⁻¹' s)) := by
            congr 1
            ext ω
            change
              finiteAlphabetEmpiricalMean v Y n ω ∈ s ↔
                finiteAlphabetFirstMoment v
                    (empiricalDistribution (Nat.succPNat n) (fun i ↦ Y i) ω) ∈ s
            rw [finiteAlphabetFirstMoment_empiricalDistribution_eq_empiricalMean
              (v := v) (Y := Y) (n := n) (ω := ω)]
    _ = ((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n : Measure (ProbabilityMeasure α))
          ((finiteAlphabetFirstMoment v) ⁻¹' s)) := by
            rw [empiricalMeasureLaw_def]
            symm
            simpa using
              (ProbabilityMeasure.map_apply'
                ⟨(P : Measure Ω), inferInstance⟩
                (measurable_empiricalMeasure Y hYmeas n).aemeasurable
                hPreimage)

/-- Helper for Example 23.15: the Legendre-transform rate is lower semicontinuous because it is an
`iSup` of continuous affine functions followed by `EReal.toENNReal`. -/
theorem lowerSemicontinuous_finiteAlphabetLegendreRateFunction {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) :
    LowerSemicontinuous (finiteAlphabetLegendreRateFunction μ v) := by
  have hCore :
      LowerSemicontinuous fun x : Fin d → ℝ ↦
        ⨆ t : Fin d → ℝ,
          (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal) := by
    refine lowerSemicontinuous_iSup fun t ↦ ?_
    have hContReal :
        Continuous fun x : Fin d → ℝ ↦
          (∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t := by
      -- Proof comment: for fixed `t`, the Legendre summand is an affine continuous function of
      -- the point `x`.
      exact (continuous_finset_sum _ fun i _ ↦ continuous_const.mul (continuous_apply i)).sub
        continuous_const
    exact (continuous_coe_real_ereal.comp hContReal).lowerSemicontinuous
  -- Proof comment: compose the extended-real supremum with the monotone continuous map
  -- `EReal.toENNReal`.
  simpa [finiteAlphabetLegendreRateFunction, sSup_range] using
    Continuous.comp_lowerSemicontinuous EReal.continuous_toENNReal hCore
      (fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal hxy)

/-- Helper for Example 23.15: coercing an `sInf` of `ℝ≥0∞` values to `EReal` agrees with taking
the `sInf` after coercion. -/
theorem ereal_sInf_coe_ennreal_image (S : Set ENNReal) :
    sInf (((↑) : ENNReal → EReal) '' S) = ((sInf S : ENNReal) : EReal) := by
  have hImage :
      IsGLB (((↑) : ENNReal → EReal) '' S) ((sInf S : ENNReal) : EReal) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact_mod_cast (isGLB_sInf S).1 hx
    · intro z hz
      have hzENNReal : z.toENNReal ≤ sInf S := by
        refine (isGLB_sInf S).2 ?_
        intro x hx
        simpa using EReal.toENNReal_le_toENNReal (hz ⟨x, hx, rfl⟩)
      -- Proof comment: every lower bound of the coerced image is below its nonnegative
      -- truncation, and that truncation is a lower bound of `S`.
      calc
        z ≤ (z.toENNReal : EReal) := by
          rw [EReal.coe_toENNReal_eq_max]
          exact le_max_right _ _
        _ ≤ ((sInf S : ENNReal) : EReal) := by
          exact_mod_cast hzENNReal
  exact hImage.sInf_eq

/-- Helper for Example 23.15: the KL infimum over a first-moment preimage is bounded by the
infimum of the contracted Sanov rate over the target set. -/
theorem sInf_klDiv_firstMomentPreimage_le_sInf_sanovRate {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (s : Set (Fin d → ℝ)) :
    sInf ((fun ν : ProbabilityMeasure α ↦
      (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
        ((finiteAlphabetFirstMoment v) ⁻¹' s)) ≤
      sInf ((fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x : EReal)) '' s) := by
  -- Proof comment: rewrite the left-hand infimum back to the underlying `ENNReal` infimum, then
  -- compare it with each fiberwise Sanov infimum by the obvious subset inclusion.
  have hLeft :
      sInf ((fun ν : ProbabilityMeasure α ↦
        (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
          ((finiteAlphabetFirstMoment v) ⁻¹' s)) =
        ((sInf ((fun ν : ProbabilityMeasure α ↦
          InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
            ((finiteAlphabetFirstMoment v) ⁻¹' s)) : ENNReal) : EReal) := by
    have hImage :
        ((fun ν : ProbabilityMeasure α ↦
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
            ((finiteAlphabetFirstMoment v) ⁻¹' s)) =
          (((↑) : ENNReal → EReal) '' ((fun ν : ProbabilityMeasure α ↦
            InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
              ((finiteAlphabetFirstMoment v) ⁻¹' s))) := by
      ext y
      constructor
      · rintro ⟨ν, hν, rfl⟩
        exact ⟨InformationTheory.klDiv (ν : Measure α) (μ : Measure α), ⟨ν, hν, rfl⟩, rfl⟩
      · rintro ⟨r, ⟨ν, hν, hr⟩, rfl⟩
        exact ⟨ν, hν, by simpa using hr⟩
    rw [hImage, ereal_sInf_coe_ennreal_image]
  rw [hLeft]
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  change ((sInf ((fun ν : ProbabilityMeasure α ↦
      InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
        ((finiteAlphabetFirstMoment v) ⁻¹' s)) : ENNReal) : EReal) ≤
    (((sInf ((fun ν : ProbabilityMeasure α ↦
        InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
          finiteAlphabetMomentFiber v x)) : ENNReal) : EReal)
  have hENN :
      sInf ((fun ν : ProbabilityMeasure α ↦
        InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
          ((finiteAlphabetFirstMoment v) ⁻¹' s)) ≤
        sInf ((fun ν : ProbabilityMeasure α ↦
          InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
            finiteAlphabetMomentFiber v x) := by
    refine le_sInf ?_
    rintro _ ⟨ν, hνfiber, rfl⟩
    have hPreimage :
        ν ∈ (finiteAlphabetFirstMoment v) ⁻¹' s := by
      change finiteAlphabetFirstMoment v ν ∈ s
      have hνx : finiteAlphabetFirstMoment v ν = x := by
        simpa [finiteAlphabetMomentFiber] using hνfiber
      simpa [hνx] using hx
    exact sInf_le ⟨ν, hPreimage, rfl⟩
  exact_mod_cast hENN

/-- Helper for Example 23.15: every point in the first-moment preimage contributes an upper bound
for the contracted Sanov rate at its image. -/
theorem sInf_sanovRate_le_sInf_klDiv_firstMomentPreimage {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (s : Set (Fin d → ℝ)) :
    sInf ((fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x : EReal)) '' s) ≤
      sInf ((fun ν : ProbabilityMeasure α ↦
        (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
          ((finiteAlphabetFirstMoment v) ⁻¹' s)) := by
  refine le_sInf ?_
  rintro _ ⟨ν, hνs, rfl⟩
  have hFiber :
      ν ∈ finiteAlphabetMomentFiber v (finiteAlphabetFirstMoment v ν) := by
    simp [finiteAlphabetMomentFiber]
  have hPointwise :
      finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v ν) ≤
        InformationTheory.klDiv (ν : Measure α) (μ : Measure α) := by
    exact sInf_le ⟨ν, hFiber, rfl⟩
  -- Proof comment: evaluate the target infimum at the realized first moment of `ν`, then use the
  -- defining fiberwise infimum bound.
  exact
    le_trans
      (sInf_le ⟨finiteAlphabetFirstMoment v ν, hνs, rfl⟩)
      (by
        have hPointwiseE :
            (finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v ν) : EReal) ≤
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal) := by
          exact_mod_cast hPointwise
        exact hPointwiseE)

/-- Helper for Example 23.15: the effective support of `μ` is the convex hull of the vectors
attached to the atoms with positive `μ`-mass. -/
def finiteAlphabetSupportHull {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range fun a : {a // (μ : Measure α) {a} ≠ 0} ↦ v a.1)

/-- Helper for Example 23.15: the effective support hull is convex by construction. -/
theorem finiteAlphabetSupportHull_convex {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) :
    Convex ℝ (finiteAlphabetSupportHull μ v) := by
  simpa [finiteAlphabetSupportHull] using
    (convex_convexHull ℝ (Set.range fun a : {a // (μ : Measure α) {a} ≠ 0} ↦ v a.1))

/-- Helper for Example 23.15: the effective support hull is closed because it is the convex hull of
the finite positive-support image. -/
theorem finiteAlphabetSupportHull_isClosed {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) :
    IsClosed (finiteAlphabetSupportHull μ v) := by
  have hFinite :
      (Set.range fun a : {a // (μ : Measure α) {a} ≠ 0} ↦ v a.1).Finite :=
    Set.finite_range _
  simpa [finiteAlphabetSupportHull] using hFinite.isClosed_convexHull (𝕜 := ℝ)

/-- Helper for Example 23.15: a probability measure on a finite alphabet has at least one atom with
positive mass. -/
theorem finiteAlphabet_exists_positiveSingletonMass {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] (μ : ProbabilityMeasure α) :
    ∃ a : α, (μ : Measure α) {a} ≠ 0 := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  by_contra hNone
  push Not at hNone
  have hMass :
      (∑ a : α, (μ : Measure α) {a}) = (1 : ENNReal) := by
    rw [show (∑ a : α, (μ : Measure α) {a}) = ∑' a : α, (μ : Measure α) {a} by
      exact (tsum_fintype (f := fun a : α ↦ (μ : Measure α) {a})).symm]
    simpa only [Measure.toPMF_apply] using (PMF.tsum_coe ((μ : Measure α).toPMF))
  have hZero :
      (∑ a : α, (μ : Measure α) {a}) = (0 : ENNReal) := by
    simp [hNone]
  exact zero_ne_one (hZero.symm.trans hMass)

/-- Helper for Example 23.15: the singleton masses of a finite-alphabet probability measure sum to
`1` after coercion to `ℝ`. -/
theorem finiteAlphabet_sum_singletonMassReal {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] (μ : ProbabilityMeasure α) :
    ∑ a : α, (((μ {a} : NNReal) : ℝ)) = 1 := by
  have hMass :
      (∑ a : α, (μ : Measure α) {a}) = (1 : ENNReal) := by
    rw [show (∑ a : α, (μ : Measure α) {a}) = ∑' a : α, (μ : Measure α) {a} by
      exact (tsum_fintype (f := fun a : α ↦ (μ : Measure α) {a})).symm]
    simpa only [Measure.toPMF_apply] using (PMF.tsum_coe ((μ : Measure α).toPMF))
  -- Proof comment: on a finite alphabet, converting the total singleton mass from `ENNReal` to
  -- `ℝ` preserves the normalization `∑ μ {a} = 1`.
  have hMassReal := congrArg ENNReal.toReal hMass
  rw [ENNReal.toReal_sum (fun a _ ↦ measure_ne_top _ _), ENNReal.toReal_one] at hMassReal
  simpa using hMassReal

/-- Helper for Example 23.15: a continuous linear functional on `ℝ^d` is determined by its values
on the standard basis vectors. -/
theorem strongDual_apply_eq_sum_basisFun {d : ℕ} (l : StrongDual ℝ (Fin d → ℝ))
    (x : Fin d → ℝ) :
    l x = ∑ i, x i * l (fun j : Fin d ↦ if i = j then 1 else 0) := by
  -- Proof comment: decompose `x` into the standard basis and use linearity of `l` on each basis
  -- vector.
  simpa [smul_eq_mul] using
    (LinearMap.pi_apply_eq_sum_univ (f := l.toLinearMap) x)

/-- Helper for Example 23.15: an absolutely continuous finite-alphabet law has first moment inside
the convex hull of the positive-`μ` support. -/
theorem finiteAlphabetFirstMoment_memSupportHull_of_absolutelyContinuous {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ ν : ProbabilityMeasure α) (v : α → Fin d → ℝ)
    (h_ac : (ν : Measure α) ≪ (μ : Measure α)) :
    finiteAlphabetFirstMoment v ν ∈ finiteAlphabetSupportHull μ v := by
  classical
  obtain ⟨a₀, ha₀⟩ := finiteAlphabet_exists_positiveSingletonMass μ
  let z : α → Fin d → ℝ :=
    fun a ↦ if hμa : (μ : Measure α) {a} = 0 then v a₀ else v a
  have hz :
      ∀ a : α, z a ∈ Set.range fun b : {a // (μ : Measure α) {a} ≠ 0} ↦ v b.1 := by
    intro a
    by_cases hμa : (μ : Measure α) {a} = 0
    · exact ⟨⟨a₀, ha₀⟩, by simp [z, hμa]⟩
    · exact ⟨⟨a, hμa⟩, by simp [z, hμa]⟩
  have hx :
      ∑ a : α, (((ν {a} : NNReal) : ℝ)) • z a = finiteAlphabetFirstMoment v ν := by
    ext i
    have hzEq :
        ∀ a : α,
          (((ν {a} : NNReal) : ℝ)) * z a i =
            (((ν {a} : NNReal) : ℝ)) * v a i := by
      intro a
      by_cases hμa : (μ : Measure α) {a} = 0
      · have hνa : (ν : Measure α) {a} = 0 := h_ac hμa
        simp [z, hμa, hνa]
      · simp [z, hμa]
    -- Proof comment: the weights on `μ`-null atoms vanish under absolute continuity, so the
    -- modified support-only barycenter still computes the original first moment.
    calc
      (∑ a : α, (((ν {a} : NNReal) : ℝ)) • z a) i
          = ∑ a : α, (((ν {a} : NNReal) : ℝ)) * z a i := by
              simp [Pi.smul_apply]
      _ = ∑ a : α, (((ν {a} : NNReal) : ℝ)) * v a i := by
            refine Finset.sum_congr rfl fun a _ ↦ hzEq a
      _ = finiteAlphabetFirstMoment v ν i := by
            simp [finiteAlphabetFirstMoment]
  -- Proof comment: express the first moment as a convex combination of points from the positive
  -- support image of `μ`.
  refine mem_convexHull_of_exists_fintype
    (w := fun a : α ↦ (((ν {a} : NNReal) : ℝ))) (z := z) ?_ ?_ hz hx
  · intro a
    positivity
  · simpa using finiteAlphabet_sum_singletonMassReal ν

/-- Helper for Example 23.15: every fiber witness bounds the affine Legendre summand by its
relative entropy. This is the finite-alphabet Gibbs inequality obtained by comparing `ν` with the
tilted law of `μ`. -/
theorem finiteAlphabetAffineGap_le_klDiv_of_memFiber {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) {ν : ProbabilityMeasure α}
    {x : Fin d → ℝ} (hνx : ν ∈ finiteAlphabetMomentFiber v x) (t : Fin d → ℝ) :
    (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal) ≤
      (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal) := by
  let f : α → ℝ := fun a ↦ ∑ i, t i * v a i
  have hfν : Integrable f (ν : Measure α) := Integrable.of_finite
  have hExpμ : Integrable (fun a ↦ Real.exp (f a)) (μ : Measure α) := Integrable.of_finite
  by_cases hklTop : InformationTheory.klDiv (ν : Measure α) (μ : Measure α) = ⊤
  · -- Proof comment: if the KL divergence is already infinite, the affine gap bound is trivial.
    simp [hklTop]
  · have hklFinite : InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≠ ⊤ := hklTop
    rcases InformationTheory.klDiv_ne_top_iff.mp hklFinite with ⟨h_ac, h_int⟩
    have h_ac_tilted :
        (ν : Measure α) ≪ (μ : Measure α).tilted f := by
      exact h_ac.trans (MeasureTheory.absolutelyContinuous_tilted (μ := (μ : Measure α)) hExpμ)
    have h_int_tilted :
        Integrable (MeasureTheory.llr (ν : Measure α) ((μ : Measure α).tilted f))
          (ν : Measure α) := by
      exact MeasureTheory.integrable_llr_tilted_right h_ac hfν h_int hExpμ
    have hMoment : ∫ a, f a ∂(ν : Measure α) = ∑ i, t i * x i := by
      have hνx' : finiteAlphabetFirstMoment v ν = x := by
        simpa [finiteAlphabetMomentFiber] using hνx
      -- Proof comment: expand the finite integral and then rewrite each coordinate using the
      -- fiber identity `finiteAlphabetFirstMoment v ν = x`.
      rw [MeasureTheory.integral_fintype (μ := (ν : Measure α)) (f := f) hfν]
      simp only [f, smul_eq_mul]
      calc
        ∑ a, (ν : Measure α).real {a} * ∑ i, t i * v a i
            = ∑ a, ∑ i, (ν : Measure α).real {a} * (t i * v a i) := by
                refine Finset.sum_congr rfl fun a _ ↦ ?_
                rw [Finset.mul_sum]
        _ = ∑ i, ∑ a, (ν : Measure α).real {a} * (t i * v a i) := by
              rw [Finset.sum_comm]
        _ = ∑ i, t i * ∑ a, (ν : Measure α).real {a} * v a i := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              calc
                ∑ a, (ν : Measure α).real {a} * (t i * v a i)
                    = ∑ a, t i * ((ν : Measure α).real {a} * v a i) := by
                        refine Finset.sum_congr rfl fun a _ ↦ ?_
                        ring
                _ = t i * ∑ a, (ν : Measure α).real {a} * v a i := by
                      rw [Finset.mul_sum]
        _ = ∑ i, t i * x i := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              have hCoord : ∑ a, (ν : Measure α).real {a} * v a i = x i := by
                simpa [finiteAlphabetFirstMoment, Measure.real] using
                  congrArg (fun y : Fin d → ℝ ↦ y i) hνx'
              rw [hCoord]
    have hLogMgf :
        Real.log (∫ a, Real.exp (f a) ∂(μ : Measure α)) =
          finiteAlphabetLogMomentGeneratingFunction μ v t := by
      -- Proof comment: on the finite alphabet, the normalization constant of the tilt is exactly
      -- the chapter's log moment generating function.
      rw [MeasureTheory.integral_fintype (μ := (μ : Measure α)) (f := fun a ↦ Real.exp (f a))
        hExpμ]
      have hMass :
          ∀ a : α, (μ : Measure α).real {a} = (((μ {a} : NNReal) : ℝ)) := by
        intro a
        simpa [Measure.real] using
          (ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := μ) ({a} : Set α)).symm
      have hSumMass :
          ∑ a, (μ : Measure α).real {a} * Real.exp (f a) =
            ∑ a, (((μ {a} : NNReal) : ℝ)) * Real.exp (f a) := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [hMass a]
      calc
        Real.log (∑ a, (μ : Measure α).real {a} * Real.exp (f a))
            = Real.log (∑ a, (((μ {a} : NNReal) : ℝ)) * Real.exp (f a)) := by
                rw [hSumMass]
        _ = finiteAlphabetLogMomentGeneratingFunction μ v t := by
              simp [f, finiteAlphabetLogMomentGeneratingFunction]
    have hTiltedNonneg :
        0 ≤ (InformationTheory.klDiv (ν : Measure α) ((μ : Measure α).tilted f)).toReal := by
      exact ENNReal.toReal_nonneg
    have hRealFormula :
        (InformationTheory.klDiv (ν : Measure α) ((μ : Measure α).tilted f)).toReal =
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal -
            ∫ a, f a ∂(ν : Measure α) +
              Real.log (∫ a, Real.exp (f a) ∂(μ : Measure α)) := by
      have hUniv :
          (ν : Measure α) Set.univ = ((μ : Measure α).tilted f) Set.univ := by
        have hTiltedProb : IsProbabilityMeasure ((μ : Measure α).tilted f) :=
          MeasureTheory.isProbabilityMeasure_tilted hExpμ
        simp
      have hUnivBase : (ν : Measure α) Set.univ = (μ : Measure α) Set.univ := by
        simp
      rw [InformationTheory.toReal_klDiv_of_measure_eq h_ac_tilted hUniv]
      rw [InformationTheory.toReal_klDiv_of_measure_eq h_ac hUnivBase]
      exact MeasureTheory.integral_llr_tilted_right h_ac hfν hExpμ h_int
    have hReal :
        (∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t ≤
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal := by
      -- Proof comment: nonnegativity of the KL divergence against the tilted law rearranges to
      -- the desired affine-gap estimate.
      rw [hRealFormula, hMoment, hLogMgf] at hTiltedNonneg
      linarith
    have hEReal :
        (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal) ≤
          (((InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal : ℝ) : EReal) := by
      exact EReal.coe_le_coe hReal
    have hToRealLe :
        ((((InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal : ℝ)) : EReal) ≤
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal) := by
      have hENN :
          ENNReal.ofReal ((InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal) ≤
            InformationTheory.klDiv (ν : Measure α) (μ : Measure α) := by
        simpa using
          (ENNReal.ofReal_toReal_le
            (a := InformationTheory.klDiv (ν : Measure α) (μ : Measure α)))
      simpa using
        (show ((ENNReal.ofReal
            ((InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal)) : EReal) ≤
            (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal) from
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hENN)
    exact hEReal.trans hToRealLe

/-- Helper for Example 23.15: the Legendre-transform rate is always bounded above by the contracted
Sanov rate. This is the easy Jensen/Gibbs direction of the variational identity. -/
theorem finiteAlphabetLegendreRateFunction_le_sanovRateFunction {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    finiteAlphabetLegendreRateFunction μ v x ≤ finiteAlphabetSanovRateFunction μ v x := by
  rw [finiteAlphabetLegendreRateFunction_def]
  rw [finiteAlphabetSanovRateFunction]
  have hEReal :
      sSup
          (Set.range fun t : Fin d → ℝ ↦
            (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal)) ≤
        sInf
          (((↑) : ENNReal → EReal) ''
            ((fun ν : ProbabilityMeasure α ↦
              InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) ''
              finiteAlphabetMomentFiber v x)) := by
    refine sSup_le ?_
    rintro _ ⟨t, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨_, ⟨ν, hνx, rfl⟩, rfl⟩
    exact finiteAlphabetAffineGap_le_klDiv_of_memFiber (μ := μ) (v := v) hνx t
  simpa [ereal_sInf_coe_ennreal_image] using EReal.toENNReal_le_toENNReal hEReal

/-- Helper for Example 23.15: outside the effective support hull, the Legendre transform is `⊤`.
The separating functional grows linearly along a ray while the log moment generating function is
controlled by the separator on the positive support. -/
theorem finiteAlphabetLegendreRateFunction_eq_top_of_not_memSupportHull {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) {x : Fin d → ℝ}
    (hx : x ∉ finiteAlphabetSupportHull μ v) :
    finiteAlphabetLegendreRateFunction μ v x = ⊤ := by
  classical
  obtain ⟨l, u, hlu, hux⟩ :=
    geometric_hahn_banach_closed_point
      (s := finiteAlphabetSupportHull μ v) (x := x)
      (finiteAlphabetSupportHull_convex (μ := μ) (v := v))
      (finiteAlphabetSupportHull_isClosed (μ := μ) (v := v))
      hx
  let t : Fin d → ℝ := fun i ↦ l (fun j : Fin d ↦ if i = j then 1 else 0)
  have hSupportLt :
      ∀ a : α, (μ : Measure α) {a} ≠ 0 → ∑ i, t i * v a i < u := by
    intro a hμa
    have haHull : v a ∈ finiteAlphabetSupportHull μ v := by
      exact subset_convexHull ℝ _ ⟨⟨a, hμa⟩, rfl⟩
    have haLt : l (v a) < u := hlu _ haHull
    simpa [t, strongDual_apply_eq_sum_basisFun (l := l) (x := v a), mul_comm] using haLt
  have hxGt : u < ∑ i, t i * x i := by
    simpa [t, strongDual_apply_eq_sum_basisFun (l := l) (x := x), mul_comm] using hux
  have hδ : 0 < ∑ i, t i * x i - u := sub_pos.mpr hxGt
  have hScaleSum :
      ∀ (n : ℕ) (y : Fin d → ℝ),
        ∑ i, (((n : ℝ) * t i) * y i) = (n : ℝ) * ∑ i, t i * y i := by
    intro n y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hLogMgfLe :
      ∀ n : ℕ,
        finiteAlphabetLogMomentGeneratingFunction μ v (fun i ↦ (n : ℝ) * t i) ≤ (n : ℝ) * u := by
    intro n
    obtain ⟨a₀, ha₀⟩ := finiteAlphabet_exists_positiveSingletonMass μ
    let massTerm : α → ℝ :=
      fun a ↦ (((μ {a} : NNReal) : ℝ)) *
        Real.exp (∑ i, (((n : ℝ) * t i) * v a i))
    have hMassPos :
        0 < ∑ a : α, massTerm a := by
      have hμa₀_pos : 0 < (((μ {a₀} : NNReal) : ℝ)) := by
        exact ENNReal.toReal_pos (by simpa using ha₀) (measure_ne_top _ _)
      have hTermPos : 0 < massTerm a₀ := by
        have hExpPos :
            0 < Real.exp (∑ i, (((n : ℝ) * t i) * v a₀ i)) := Real.exp_pos _
        exact mul_pos hμa₀_pos hExpPos
      have hTermLe :
          massTerm a₀ ≤ ∑ a : α, massTerm a := by
        refine Finset.single_le_sum ?_ (by simp)
        intro a ha
        positivity
      exact lt_of_lt_of_le hTermPos hTermLe
    have hMassLe :
        ∑ a : α, massTerm a ≤ Real.exp ((n : ℝ) * u) := by
      calc
        ∑ a : α, massTerm a
            ≤ ∑ a : α, (((μ {a} : NNReal) : ℝ)) * Real.exp ((n : ℝ) * u) := by
                refine Finset.sum_le_sum fun a _ ↦ ?_
                by_cases hμa : (μ : Measure α) {a} = 0
                · have hWeightZero : (((μ {a} : NNReal) : ℝ)) = 0 := by
                    simp [hμa]
                  simp [massTerm, hWeightZero]
                · have hlt : ∑ i, t i * v a i < u := hSupportLt a hμa
                  have hle :
                      ∑ i, (((n : ℝ) * t i) * v a i) ≤ (n : ℝ) * u := by
                    rw [hScaleSum n (v a)]
                    exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
                  have hExpLe :
                      Real.exp (∑ i, (((n : ℝ) * t i) * v a i)) ≤ Real.exp ((n : ℝ) * u) :=
                    Real.exp_le_exp.mpr hle
                  have hWeightNonneg : 0 ≤ (((μ {a} : NNReal) : ℝ)) := by
                    positivity
                  exact mul_le_mul_of_nonneg_left hExpLe hWeightNonneg
        _ = Real.exp ((n : ℝ) * u) * ∑ a : α, (((μ {a} : NNReal) : ℝ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ ↦ ?_
              ring
        _ = Real.exp ((n : ℝ) * u) := by
              rw [finiteAlphabet_sum_singletonMassReal μ, mul_one]
    -- Proof comment: the separator bounds every positive-support contribution by `exp (n * u)`,
    -- so the whole logarithmic moment generating function stays below `n * u`.
    change Real.log (∑ a : α, massTerm a) ≤ (n : ℝ) * u
    exact (Real.log_le_iff_le_exp hMassPos).2 hMassLe
  have hGapLower :
      ∀ n : ℕ,
        (n : ℝ) * (∑ i, t i * x i - u) ≤
          (∑ i, (((n : ℝ) * t i) * x i)) -
            finiteAlphabetLogMomentGeneratingFunction μ v (fun i ↦ (n : ℝ) * t i) := by
    intro n
    rw [hScaleSum n x]
    linarith [hLogMgfLe n]
  have hCoreTop :
      sSup (Set.range fun s : Fin d → ℝ ↦
        (((∑ i, s i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v s : ℝ) :
          EReal)) = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt (y / (∑ i, t i * x i - u))
    have hy :
        y < (n : ℝ) * (∑ i, t i * x i - u) := by
      exact (_root_.div_lt_iff₀ hδ).1 hn
    have hWitness :
        (y : EReal) <
          (((∑ i, (((n : ℝ) * t i) * x i)) -
              finiteAlphabetLogMomentGeneratingFunction μ v (fun i ↦ (n : ℝ) * t i) : ℝ) :
            EReal) := by
      exact_mod_cast (lt_of_lt_of_le hy (hGapLower n))
    exact
      lt_of_lt_of_le hWitness <|
        le_sSup ⟨fun i ↦ (n : ℝ) * t i, rfl⟩
  -- Proof comment: the Legendre supremum is unbounded above on the separating ray, so its
  -- `toENNReal` image is `⊤`.
  rw [finiteAlphabetLegendreRateFunction_def, EReal.toENNReal_eq_top_iff]
  exact hCoreTop

/-- Helper for Example 23.15: on a finite alphabet, nullity of every `μ`-null singleton already
forces absolute continuity with respect to `μ`. -/
theorem absolutelyContinuous_of_forall_nullSingleton {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] {ν μ : Measure α}
    (hNull : ∀ a : α, μ ({a} : Set α) = 0 → ν ({a} : Set α) = 0) :
    ν ≪ μ := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  refine Measure.AbsolutelyContinuous.mk fun s _ hs0 ↦ ?_
  rw [MeasureTheory.measure_null_iff_singleton (Set.to_countable s)] at hs0 ⊢
  intro a ha
  exact hNull a (hs0 a ha)

/-- Helper for Example 23.15: each first-moment coordinate is the integral of the corresponding
coordinate function. -/
theorem finiteAlphabetFirstMoment_apply_eq_integral {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (v : α → Fin d → ℝ)
    (ν : ProbabilityMeasure α) (i : Fin d) :
    finiteAlphabetFirstMoment v ν i = ∫ a, v a i ∂(ν : Measure α) := by
  -- Proof comment: on a finite alphabet, the Bochner integral is the finite weighted singleton
  -- sum used in the definition of the first moment.
  rw [MeasureTheory.integral_fintype (μ := (ν : Measure α)) (f := fun a : α ↦ v a i)
    Integrable.of_finite]
  symm
  calc
    ∑ a, (ν : Measure α).real {a} * v a i = ∑ a, (((ν {a} : NNReal) : ℝ)) * v a i := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := ν) ({a} : Set α)]
    _ = finiteAlphabetFirstMoment v ν i := by
          simp [finiteAlphabetFirstMoment]

/-- Helper for Example 23.15: every point in the effective support hull has a first-moment witness
that is absolutely continuous with respect to `μ`. -/
theorem finiteAlphabetExistsMemAcFiber_of_memSupportHull {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) {x : Fin d → ℝ} (hx : x ∈ finiteAlphabetSupportHull μ v) :
    ∃ ν : ProbabilityMeasure α, ν ∈ finiteAlphabetMomentFiber v x ∧
      (ν : Measure α) ≪ (μ : Measure α) := by
  classical
  rw [finiteAlphabetSupportHull, mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
  choose a ha using hz
  let νm : Measure α := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i).1
  have hWeightSum : ∑ i, ENNReal.ofReal (w i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simpa using congrArg ENNReal.ofReal hw₁
    · intro i _
      exact hw₀ i
  have hνmProb : IsProbabilityMeasure νm := by
    refine ⟨?_⟩
    calc
      νm Set.univ = ∑ i, ENNReal.ofReal (w i) := by
        simp [νm]
      _ = 1 := hWeightSum
  let ν : ProbabilityMeasure α := ⟨νm, hνmProb⟩
  have hAc : (ν : Measure α) ≪ (μ : Measure α) := by
    refine absolutelyContinuous_of_forall_nullSingleton ?_
    intro b hb
    have hbNe : ∀ i, (a i).1 ≠ b := by
      intro i hab
      exact (hab ▸ (a i).2) hb
    -- Proof comment: every atom used in the convex representation already lies in the positive
    -- support of `μ`, so no `μ`-null singleton can receive mass under `ν`.
    change νm ({b} : Set α) = 0
    simp [νm, hbNe]
  have hMoment : finiteAlphabetFirstMoment v ν = x := by
    ext j
    calc
      finiteAlphabetFirstMoment v ν j = ∫ b, v b j ∂(ν : Measure α) := by
        rw [finiteAlphabetFirstMoment_apply_eq_integral (v := v) (ν := ν) (i := j)]
      _ = ∑ i, w i * v (a i).1 j := by
        change
          ∫ b, v b j ∂(∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i).1) =
            ∑ i, w i * v (a i).1 j
        rw [MeasureTheory.integral_finset_sum_measure]
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
          simp [smul_eq_mul, hw₀ i]
        · intro i _
          exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
      _ = ∑ i, w i * z i j := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [ha i]
      _ = x j := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun y : Fin d → ℝ ↦ y j) hx
  exact ⟨ν, by simpa [finiteAlphabetMomentFiber] using hMoment, hAc⟩

/-- Helper for Example 23.15: on the effective support hull, the contracted Sanov rate attains its
fiber minimum at an absolutely continuous witness. -/
theorem finiteAlphabetSanovRate_hasMinimizerOnFiber {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) {x : Fin d → ℝ} (hx : x ∈ finiteAlphabetSupportHull μ v) :
    ∃ ν : ProbabilityMeasure α, ν ∈ finiteAlphabetMomentFiber v x ∧
      (ν : Measure α) ≪ (μ : Measure α) ∧
      InformationTheory.klDiv (ν : Measure α) (μ : Measure α) =
        finiteAlphabetSanovRateFunction μ v x := by
  classical
  letI : TopologicalSpace α := ⊥
  letI : DiscreteTopology α := ⟨rfl⟩
  letI : BorelSpace α := inferInstance
  obtain ⟨ν₀, hν₀x, hν₀ac⟩ :=
    finiteAlphabetExistsMemAcFiber_of_memSupportHull (μ := μ) (v := v) hx
  have hFiberClosed : IsClosed (finiteAlphabetMomentFiber v x) := by
    -- Proof comment: the fiber is the preimage of the closed singleton `{x}` under the continuous
    -- first-moment map on the compact probability-measure space.
    simpa [finiteAlphabetMomentFiber] using
      (isClosed_singleton.preimage (continuous_finiteAlphabetFirstMoment (v := v)))
  have hFiberCompact : IsCompact (finiteAlphabetMomentFiber v x) := hFiberClosed.isCompact
  have hLscOn :
      LowerSemicontinuousOn
        (fun ν : ProbabilityMeasure α ↦ InformationTheory.klDiv (ν : Measure α) (μ : Measure α))
        (finiteAlphabetMomentFiber v x) :=
    (lowerSemicontinuous_relativeEntropyRate (μ := μ)).lowerSemicontinuousOn _
  obtain ⟨ν, hνx, hνmin⟩ :=
    hLscOn.exists_isMinOn ⟨ν₀, hν₀x⟩ hFiberCompact
  have hν₀Finite :
      InformationTheory.klDiv (ν₀ : Measure α) (μ : Measure α) ≠ ⊤ := by
    exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hν₀ac, Integrable.of_finite⟩
  have hνLe :
      InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≤
        InformationTheory.klDiv (ν₀ : Measure α) (μ : Measure α) := by
    have hνmin' :
        ∀ ρ ∈ finiteAlphabetMomentFiber v x,
          InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≤
            InformationTheory.klDiv (ρ : Measure α) (μ : Measure α) := by
      simpa [isMinOn_iff] using hνmin
    exact hνmin' ν₀ hν₀x
  have hνFinite :
      InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≠ ⊤ :=
    ne_top_of_le_ne_top hν₀Finite hνLe
  have hνac : (ν : Measure α) ≪ (μ : Measure α) := by
    exact (InformationTheory.klDiv_ne_top_iff.mp hνFinite).1
  have hEq :
      InformationTheory.klDiv (ν : Measure α) (μ : Measure α) =
        finiteAlphabetSanovRateFunction μ v x := by
    apply le_antisymm
    · rw [finiteAlphabetSanovRateFunction]
      refine le_sInf ?_
      rintro _ ⟨ρ, hρx, rfl⟩
      have hνmin' :
          ∀ ρ ∈ finiteAlphabetMomentFiber v x,
            InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≤
              InformationTheory.klDiv (ρ : Measure α) (μ : Measure α) := by
        simpa [isMinOn_iff] using hνmin
      exact hνmin' ρ hρx
    · rw [finiteAlphabetSanovRateFunction]
      exact sInf_le ⟨ν, hνx, rfl⟩
  exact ⟨ν, hνx, hνac, hEq⟩

/-- Helper for Example 23.15: on the effective support hull, the contracted Sanov rate is finite. -/
theorem finiteAlphabetSanovRate_ne_top_of_memSupportHull {α : Type v} [MeasurableSpace α]
    [MeasurableSingletonClass α] {d : ℕ} [Fintype α] (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) {x : Fin d → ℝ} (hx : x ∈ finiteAlphabetSupportHull μ v) :
    finiteAlphabetSanovRateFunction μ v x ≠ ⊤ := by
  obtain ⟨ν, hνx, hνac, hνEq⟩ :=
    finiteAlphabetSanovRate_hasMinimizerOnFiber (μ := μ) (v := v) hx
  -- Proof comment: the minimizing fiber witness is absolutely continuous, so its KL divergence is
  -- finite and therefore so is the contracted rate.
  rw [← hνEq]
  exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hνac, Integrable.of_finite⟩

/-- Helper for Example 23.15: the real-valued contracted Sanov rate is lower semicontinuous on the
effective support hull. -/
theorem lowerSemicontinuousOn_finiteAlphabetSanovRateReal_supportHull {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) :
    LowerSemicontinuousOn
      (fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x).toReal)
      (finiteAlphabetSupportHull μ v) := by
  classical
  letI : TopologicalSpace α := ⊥
  letI : DiscreteTopology α := ⟨rfl⟩
  letI : BorelSpace α := inferInstance
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro b
  by_cases hb : b < 0
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    constructor
    · rintro ⟨_, hxLe⟩
      -- Proof comment: the contracted rate is nonnegative, so no point can lie in a negative
      -- sublevel set.
      have hxLe' :
          (finiteAlphabetSanovRateFunction μ v x).toReal ≤ b := by
        simpa using hxLe
      have hnonneg :
          0 ≤ (finiteAlphabetSanovRateFunction μ v x).toReal := ENNReal.toReal_nonneg
      linarith
    · intro hx
      simp at hx
  · have hb0 : 0 ≤ b := le_of_not_gt hb
    let K : Set (ProbabilityMeasure α) :=
      {ν | InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≤ ENNReal.ofReal b}
    let V : Set (Fin d → ℝ) := finiteAlphabetFirstMoment v '' K
    have hKClosed : IsClosed K := by
      -- Proof comment: finite-alphabet relative entropy is lower semicontinuous, so each KL
      -- sublevel set in the compact probability-measure space is closed.
      simpa [K] using
        (lowerSemicontinuous_relativeEntropyRate (μ := μ)).isClosed_preimage (ENNReal.ofReal b)
    have hKCompact : IsCompact K := hKClosed.isCompact
    have hVClosed : IsClosed V := by
      -- Proof comment: the first-moment map is continuous, so the image of the compact KL sublevel
      -- set is compact and hence closed in `ℝ^d`.
      exact (hKCompact.image (continuous_finiteAlphabetFirstMoment (v := v))).isClosed
    refine ⟨V, hVClosed, ?_⟩
    ext x
    constructor
    · rintro ⟨hxHull, hxLe⟩
      obtain ⟨ν, hνx, hνac, hνEq⟩ :=
        finiteAlphabetSanovRate_hasMinimizerOnFiber (μ := μ) (v := v) hxHull
      have hRateNeTop :
          finiteAlphabetSanovRateFunction μ v x ≠ ⊤ :=
        finiteAlphabetSanovRate_ne_top_of_memSupportHull (μ := μ) (v := v) hxHull
      have hRateLe :
          finiteAlphabetSanovRateFunction μ v x ≤ ENNReal.ofReal b := by
        -- Proof comment: on the support hull, finiteness lets us convert the real sublevel
        -- condition back to an `ENNReal` bound.
        rw [← ENNReal.ofReal_toReal hRateNeTop]
        exact ENNReal.ofReal_le_ofReal hxLe
      have hKlLe :
          InformationTheory.klDiv (ν : Measure α) (μ : Measure α) ≤ ENNReal.ofReal b := by
        simpa [hνEq] using hRateLe
      refine ⟨hxHull, ?_⟩
      exact ⟨ν, hKlLe, by simpa [K, V, finiteAlphabetMomentFiber] using hνx⟩
    · rintro ⟨hxHull, hxV⟩
      rcases hxV with ⟨ν, hνK, hνx⟩
      have hRateLe :
          finiteAlphabetSanovRateFunction μ v x ≤
            InformationTheory.klDiv (ν : Measure α) (μ : Measure α) := by
        -- Proof comment: any fiber witness bounds the contracted rate from above by the defining
        -- infimum over that fiber.
        rw [finiteAlphabetSanovRateFunction]
        exact sInf_le ⟨ν, by simpa [finiteAlphabetMomentFiber] using hνx, rfl⟩
      exact ⟨hxHull, ENNReal.toReal_le_of_le_ofReal hb0 (hRateLe.trans hνK)⟩

/-- Helper for Example 23.15: if a nonnegative mass function sums to at most `1`, then each
coordinate is finite. -/
theorem pmfCoordinate_ne_top_of_tsum_le_one_local {E : Type*} (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Proof comment: each coordinate is bounded by the total mass, and the total mass is bounded
  -- by `1`.
  have hqLeOne : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hqLeOne ENNReal.one_lt_top)

/-- Helper for Example 23.15: a finite PMF can be rewritten as the counting measure weighted by a
comparison mass function `q`, followed by the density ratio `p / q`. -/
theorem pmfToMeasure_eq_withDensityRatio {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Finite E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    p.toMeasure = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let ν : Measure E := Measure.count.withDensity q
  calc
    p.toMeasure = Measure.count.withDensity (fun e ↦ (p e : ENNReal)) := by
      -- Proof comment: a PMF is the counting measure weighted by its point masses.
      refine Measure.ext fun s hs ↦ ?_
      rw [p.toMeasure_apply hs, withDensity_apply _ hs]
      rw [← lintegral_indicator hs (fun e ↦ (p e : ENNReal)), lintegral_count]
    _ = (Measure.count.withDensity q).withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      -- Proof comment: replace the PMF weights by `q * (p / q)`; the ratio is only used on the
      -- support of `p`, where `q` is nonzero.
      rw [← withDensity_mul (Measure.count : Measure E)]
      · refine withDensity_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro e
        by_cases hp : p e = 0
        · simp [hp]
        · have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
          have hqTop : q e ≠ ⊤ := pmfCoordinate_ne_top_of_tsum_le_one_local q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hqTop, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · exact measurable_of_finite q
      · exact measurable_of_finite (fun e ↦ (p e : ENNReal) / q e)
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Example 23.15: on a finite discrete alphabet, the KL divergence against a
comparison mass function is the sum of the pointwise KL gap terms. -/
theorem discreteKlDiv_eq_gapSeriesOfMassComparison {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Finite E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    InformationTheory.klDiv p.toMeasure ν =
      ∑' e : E,
        ENNReal.ofReal
          ((q e).toReal * InformationTheory.klFun (((p e : ENNReal) / q e).toReal)) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- Proof comment: the comparison measure has total mass at most `1`.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  have hpν : p.toMeasure ≪ ν := by
    rw [pmfToMeasure_eq_withDensityRatio p q hq hnozero]
    exact withDensity_absolutelyContinuous _ _
  change InformationTheory.klDiv p.toMeasure ν =
      ∑' e : E,
        ENNReal.ofReal
          ((q e).toReal * InformationTheory.klFun (((p e : ENNReal) / q e).toReal))
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hpν]
  have hrn : p.toMeasure.rnDeriv ν =ᵐ[ν] fun e ↦ (p e : ENNReal) / q e := by
    rw [pmfToMeasure_eq_withDensityRatio p q hq hnozero]
    exact Measure.rnDeriv_withDensity ν (measurable_of_finite _)
  have hfun :
      (fun x ↦
        ENNReal.ofReal
          (InformationTheory.klFun (p.toMeasure.rnDeriv ν x).toReal)) =ᵐ[ν]
        fun e ↦
          ENNReal.ofReal
            (InformationTheory.klFun (((p e : ENNReal) / q e).toReal)) := by
    -- Proof comment: replace the Radon-Nikodym derivative by its explicit finite density.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hqTop : q e ≠ ⊤ := pmfCoordinate_ne_top_of_tsum_le_one_local q hq e
    have hqRealNonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (InformationTheory.klFun (((p e : ENNReal) / q e).toReal))
          = ENNReal.ofReal (q e).toReal *
              ENNReal.ofReal (InformationTheory.klFun (((p e : ENNReal) / q e).toReal)) := by
              rw [ENNReal.ofReal_toReal hqTop]
      _ = ENNReal.ofReal
            ((q e).toReal * InformationTheory.klFun (((p e : ENNReal) / q e).toReal)) := by
            rw [← ENNReal.ofReal_mul hqRealNonneg]
  · fun_prop
  · fun_prop

/-- Helper for Example 23.15: on a finite alphabet, absolute continuity lets one rewrite the
real-valued KL divergence as the finite sum of the singleton gap terms
`μ {a} * klFun (ν {a} / μ {a})`. -/
theorem finiteAlphabetKlDivToReal_eq_sumGapSeries_of_absolutelyContinuous {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ ν : ProbabilityMeasure α) (h_ac : (ν : Measure α) ≪ (μ : Measure α)) :
    (InformationTheory.klDiv (ν : Measure α) (μ : Measure α)).toReal =
      ∑ a : α,
        ((μ : Measure α) {a}).toReal *
          InformationTheory.klFun
            ((((ν : Measure α) {a}) / ((μ : Measure α) {a})).toReal) := by
  classical
  let p : PMF α := (ν : Measure α).toPMF
  let q : α → ENNReal := fun a ↦ (μ : Measure α) {a}
  have hq : (∑' a : α, q a) ≤ 1 := by
    -- Proof comment: the comparison singleton masses are exactly the PMF weights of `μ`.
    exact le_of_eq <| by
      rw [show (∑' a : α, q a) = ∑' a : α, (((μ : Measure α).toPMF) a : ENNReal) by
        simp [q, Measure.toPMF_apply]]
      exact PMF.tsum_coe ((μ : Measure α).toPMF)
  have hnozero : ∀ a ∈ p.support, q a ≠ 0 := by
    -- Proof comment: positive `ν`-atoms sit over positive `μ`-atoms by absolute continuity.
    intro a ha hqa
    have hνa : (ν : Measure α) {a} = 0 := h_ac hqa
    exact (PMF.mem_support_iff p a).1 ha (by simpa [p, Measure.toPMF_apply] using hνa)
  have hqMeasure : Measure.count.withDensity q = (μ : Measure α) := by
    -- Proof comment: on a finite discrete alphabet, weighting counting measure by the singleton
    -- masses reconstructs the original probability measure.
    ext s hs
    rw [withDensity_apply _ hs, ← lintegral_indicator hs q, lintegral_count]
    simpa [q, Measure.toPMF_apply] using
      (((μ : Measure α).toPMF).toMeasure_apply_fintype s).symm
  have hterm_ne_top :
      ∀ a ∈ (Finset.univ : Finset α),
        ENNReal.ofReal
            (((μ : Measure α) {a}).toReal *
              InformationTheory.klFun
                ((((ν : Measure α) {a}) / ((μ : Measure α) {a})).toReal)) ≠ ⊤ := by
    intro a ha
    exact ENNReal.ofReal_ne_top
  have hklReal :=
    congrArg ENNReal.toReal <|
      calc
        InformationTheory.klDiv (ν : Measure α) (μ : Measure α)
          = ∑' a : α,
              ENNReal.ofReal
                ((q a).toReal *
                  InformationTheory.klFun (((p a : ENNReal) / q a).toReal)) := by
                simpa [p, q, Measure.toPMF_apply, hqMeasure] using
                  discreteKlDiv_eq_gapSeriesOfMassComparison p q hq hnozero
        _ = ∑ a : α,
              ENNReal.ofReal
                (((μ : Measure α) {a}).toReal *
                  InformationTheory.klFun
                    ((((ν : Measure α) {a}) / ((μ : Measure α) {a})).toReal)) := by
                rw [tsum_fintype]
                refine Finset.sum_congr rfl ?_
                intro a ha
                simp [p, q, Measure.toPMF_apply]
  -- Proof comment: convert the `ENNReal` sum to `ℝ`; each summand is an `ofReal`, so `toReal`
  -- removes the coercion pointwise.
  rw [ENNReal.toReal_sum hterm_ne_top] at hklReal
  refine hklReal.trans ?_
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg ENNReal.toReal_nonneg
    (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)

/-- Helper for Example 23.15: the finite-alphabet KL divergence is convex under convex
combinations of absolutely continuous probability-measure witnesses. -/
theorem finiteAlphabetKlDivToReal_convexCombination {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (μ ν₁ ν₂ : ProbabilityMeasure α)
    (hν₁ : (ν₁ : Measure α) ≪ (μ : Measure α))
    (hν₂ : (ν₂ : Measure α) ≪ (μ : Measure α))
    (p : Set.Icc (0 : ℝ) 1) :
    let νp : ProbabilityMeasure α :=
      ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
          unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
    (InformationTheory.klDiv (νp : Measure α) (μ : Measure α)).toReal ≤
      (p : ℝ) * (InformationTheory.klDiv (ν₁ : Measure α) (μ : Measure α)).toReal +
        (unitInterval.symm p : ℝ) *
          (InformationTheory.klDiv (ν₂ : Measure α) (μ : Measure α)).toReal := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let νp : ProbabilityMeasure α :=
    ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
        unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
  let a : ℝ := p
  let b : ℝ := unitInterval.symm p
  have ha : 0 ≤ a := p.2.1
  have hb : 0 ≤ b := by
    simpa [b, unitInterval.coe_symm_eq] using (unitInterval.symm p).2.1
  have hab : a + b = 1 := by
    -- Proof comment: the unit-interval weights `p` and `σ p` are complementary.
    have hWeights := congrArg (fun q : NNReal ↦ (q : ℝ))
      (unitInterval.toNNReal_add_toNNReal_symm p)
    simpa only [a, b, unitInterval.coe_symm_eq] using hWeights
  have hνp : (νp : Measure α) ≪ (μ : Measure α) := by
    -- Proof comment: absolute continuity is preserved by the convex combination of the two
    -- witnesses.
    refine absolutelyContinuous_of_forall_nullSingleton ?_
    intro x hμx
    have hν₁x : (ν₁ : Measure α) {x} = 0 := hν₁ hμx
    have hν₂x : (ν₂ : Measure α) {x} = 0 := hν₂ hμx
    change
      (unitInterval.toNNReal p • (ν₁ : Measure α) +
          unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α)) ({x} : Set α) = 0
    simp [Measure.add_apply, Measure.smul_apply, hν₁x, hν₂x]
  have hνpFormula :=
    finiteAlphabetKlDivToReal_eq_sumGapSeries_of_absolutelyContinuous (μ := μ) (ν := νp) hνp
  have hν₁Formula :=
    finiteAlphabetKlDivToReal_eq_sumGapSeries_of_absolutelyContinuous (μ := μ) (ν := ν₁) hν₁
  have hν₂Formula :=
    finiteAlphabetKlDivToReal_eq_sumGapSeries_of_absolutelyContinuous (μ := μ) (ν := ν₂) hν₂
  have hPointwise :
      ∀ x : α,
        ((μ : Measure α) {x}).toReal *
            InformationTheory.klFun ((((νp : Measure α) {x}) / ((μ : Measure α) {x})).toReal) ≤
          ((μ : Measure α) {x}).toReal *
            (a * InformationTheory.klFun
                  ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
              b * InformationTheory.klFun
                  ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal)) := by
    intro x
    by_cases hμx : (μ : Measure α) {x} = 0
    · have hν₁x : (ν₁ : Measure α) {x} = 0 := hν₁ hμx
      have hν₂x : (ν₂ : Measure α) {x} = 0 := hν₂ hμx
      have hνpx : (νp : Measure α) {x} = 0 := by
        change
          (unitInterval.toNNReal p • (ν₁ : Measure α) +
              unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α)) ({x} : Set α) = 0
        simp [Measure.add_apply, Measure.smul_apply, hν₁x, hν₂x]
      -- Proof comment: on a `μ`-null singleton, every absolutely continuous witness has zero
      -- mass, so the weighted KL summand vanishes.
      simp [hμx, hν₁x, hν₂x, hνpx]
    · have hνp_apply :
          (νp : Measure α) {x} =
            unitInterval.toNNReal p * (ν₁ : Measure α) {x} +
              unitInterval.toNNReal (unitInterval.symm p) * (ν₂ : Measure α) {x} := by
        simp [νp, Measure.add_apply, Measure.smul_apply]
      have hratio :
          ((((νp : Measure α) {x}) / ((μ : Measure α) {x})).toReal) =
            a * ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
              b * ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) := by
        have hμxReal :
            ((μ : Measure α) {x}).toReal ≠ 0 := by
          exact ENNReal.toReal_ne_zero.2 ⟨hμx, measure_ne_top _ _⟩
        rw [hνp_apply, ENNReal.toReal_div]
        rw [ENNReal.toReal_add
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))]
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div]
        simp [a, b, unitInterval.coe_symm_eq]
        field_simp [hμxReal]
      have hRatio₁Nonneg :
          0 ≤ ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) :=
        ENNReal.toReal_nonneg
      have hRatio₂Nonneg :
          0 ≤ ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) :=
        ENNReal.toReal_nonneg
      have hKl :
          InformationTheory.klFun ((((νp : Measure α) {x}) / ((μ : Measure α) {x})).toReal) ≤
            a * InformationTheory.klFun
                  ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
              b * InformationTheory.klFun
                  ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) := by
        -- Proof comment: after rewriting the mixed density ratio as the convex combination of the
        -- endpoint density ratios, convexity of `klFun` gives the one-point KL bound.
        rw [hratio]
        exact InformationTheory.convexOn_klFun.2
          (by simpa using hRatio₁Nonneg)
          (by simpa using hRatio₂Nonneg)
          ha hb hab
      exact mul_le_mul_of_nonneg_left hKl ENNReal.toReal_nonneg
  -- Proof comment: sum the pointwise convexity bound over the finite alphabet and factor the two
  -- weight coefficients back out of the finite sums.
  calc
    (InformationTheory.klDiv (νp : Measure α) (μ : Measure α)).toReal
        = ∑ x : α,
            ((μ : Measure α) {x}).toReal *
              InformationTheory.klFun
                ((((νp : Measure α) {x}) / ((μ : Measure α) {x})).toReal) := by
            simpa using hνpFormula
    _ ≤ ∑ x : α,
          ((μ : Measure α) {x}).toReal *
            (a * InformationTheory.klFun
                  ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
              b * InformationTheory.klFun
                  ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal)) := by
          exact Finset.sum_le_sum (fun x _ ↦ hPointwise x)
    _ = a * ∑ x : α,
          ((μ : Measure α) {x}).toReal *
            InformationTheory.klFun
              ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
        b * ∑ x : α,
          ((μ : Measure α) {x}).toReal *
            InformationTheory.klFun
              ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) := by
          calc
            ∑ x : α,
                ((μ : Measure α) {x}).toReal *
                  (a * InformationTheory.klFun
                        ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
                    b * InformationTheory.klFun
                        ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal))
                = ∑ x : α,
                    (a *
                        (((μ : Measure α) {x}).toReal *
                          InformationTheory.klFun
                            ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal)) +
                      b *
                        (((μ : Measure α) {x}).toReal *
                          InformationTheory.klFun
                            ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal))) := by
                    refine Finset.sum_congr rfl fun x _ ↦ ?_
                    ring
            _ = ∑ x : α,
                  a *
                    (((μ : Measure α) {x}).toReal *
                      InformationTheory.klFun
                        ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal)) +
                ∑ x : α,
                  b *
                    (((μ : Measure α) {x}).toReal *
                      InformationTheory.klFun
                        ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal)) := by
                  rw [Finset.sum_add_distrib]
            _ = a * ∑ x : α,
                  ((μ : Measure α) {x}).toReal *
                    InformationTheory.klFun
                      ((((ν₁ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) +
                b * ∑ x : α,
                  ((μ : Measure α) {x}).toReal *
                    InformationTheory.klFun
                      ((((ν₂ : Measure α) {x}) / ((μ : Measure α) {x})).toReal) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
    _ = a * (InformationTheory.klDiv (ν₁ : Measure α) (μ : Measure α)).toReal +
        b * (InformationTheory.klDiv (ν₂ : Measure α) (μ : Measure α)).toReal := by
          rw [hν₁Formula, hν₂Formula]
    _ = (p : ℝ) * (InformationTheory.klDiv (ν₁ : Measure α) (μ : Measure α)).toReal +
        (unitInterval.symm p : ℝ) *
          (InformationTheory.klDiv (ν₂ : Measure α) (μ : Measure α)).toReal := by
          rfl

/-- Helper for Example 23.15: the finite-alphabet first-moment map is affine on convex
combinations of probability measures. -/
theorem finiteAlphabetFirstMoment_convexCombination {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (v : α → Fin d → ℝ) (ν₁ ν₂ : ProbabilityMeasure α) (p : Set.Icc (0 : ℝ) 1) :
    let νp : ProbabilityMeasure α :=
      ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
          unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
    finiteAlphabetFirstMoment v νp =
      (p : ℝ) • finiteAlphabetFirstMoment v ν₁ +
        (unitInterval.symm p : ℝ) • finiteAlphabetFirstMoment v ν₂ := by
  let νp : ProbabilityMeasure α :=
    ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
        unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
  ext i
  -- Proof comment: after rewriting each coordinate as an integral, the mixed witness is handled
  -- by linearity of the Bochner integral in the measure argument.
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [finiteAlphabetFirstMoment_apply_eq_integral (v := v) (ν := νp),
    finiteAlphabetFirstMoment_apply_eq_integral (v := v) (ν := ν₁),
    finiteAlphabetFirstMoment_apply_eq_integral (v := v) (ν := ν₂)]
  change
    ∫ a, v a i ∂(unitInterval.toNNReal p • (ν₁ : Measure α) +
      unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α)) =
      (p : ℝ) * ∫ a, v a i ∂(ν₁ : Measure α) +
        (unitInterval.symm p : ℝ) * ∫ a, v a i ∂(ν₂ : Measure α)
  have hIntegralSmul₁ :
      ∫ a, v a i ∂unitInterval.toNNReal p • (ν₁ : Measure α) =
        (unitInterval.toNNReal p).toReal • ∫ a, v a i ∂(ν₁ : Measure α) := by
    simpa using
      (MeasureTheory.integral_smul_measure
        (f := fun a : α ↦ v a i) (μ := (ν₁ : Measure α)) (c := unitInterval.toNNReal p))
  have hIntegralSmul₂ :
      ∫ a, v a i ∂unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α) =
        (unitInterval.toNNReal (unitInterval.symm p)).toReal *
          ∫ a, v a i ∂(ν₂ : Measure α) := by
    simpa using
      (MeasureTheory.integral_smul_measure
        (f := fun a : α ↦ v a i) (μ := (ν₂ : Measure α))
        (c := unitInterval.toNNReal (unitInterval.symm p)))
  rw [MeasureTheory.integral_add_measure]
  · calc
      ∫ a, v a i ∂unitInterval.toNNReal p • (ν₁ : Measure α) +
          ∫ a, v a i ∂unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α)
          = (unitInterval.toNNReal p).toReal • ∫ a, v a i ∂(ν₁ : Measure α) +
              (unitInterval.toNNReal (unitInterval.symm p)).toReal •
                ∫ a, v a i ∂(ν₂ : Measure α) := by
                  rw [hIntegralSmul₁, hIntegralSmul₂]
                  simp [smul_eq_mul]
      _ = (p : ℝ) * ∫ a, v a i ∂(ν₁ : Measure α) +
            (unitInterval.symm p : ℝ) * ∫ a, v a i ∂(ν₂ : Measure α) := by
              simp
  · exact (Integrable.of_finite).smul_measure ENNReal.coe_ne_top
  · exact (Integrable.of_finite).smul_measure ENNReal.coe_ne_top

/-- Helper for Example 23.15: mixing two fiber witnesses stays in the corresponding mixed
first-moment fiber. -/
theorem finiteAlphabetMixedWitness_memMomentFiber {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (v : α → Fin d → ℝ) (ν₁ ν₂ : ProbabilityMeasure α) (x y : Fin d → ℝ)
    (p : Set.Icc (0 : ℝ) 1)
    (hν₁x : ν₁ ∈ finiteAlphabetMomentFiber v x)
    (hν₂y : ν₂ ∈ finiteAlphabetMomentFiber v y) :
    let νp : ProbabilityMeasure α :=
      ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
          unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
    νp ∈ finiteAlphabetMomentFiber v ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y) := by
  let νp : ProbabilityMeasure α :=
    ⟨unitInterval.toNNReal p • (ν₁ : Measure α) +
        unitInterval.toNNReal (unitInterval.symm p) • (ν₂ : Measure α), inferInstance⟩
  have hMoment₁ : finiteAlphabetFirstMoment v ν₁ = x := by
    simpa [finiteAlphabetMomentFiber] using hν₁x
  have hMoment₂ : finiteAlphabetFirstMoment v ν₂ = y := by
    simpa [finiteAlphabetMomentFiber] using hν₂y
  -- Proof comment: rewrite the mixed witness moment by the affine bridge and substitute the two
  -- endpoint fiber equalities.
  have hMixedMoment :
      finiteAlphabetFirstMoment v νp =
        (p : ℝ) • x + (unitInterval.symm p : ℝ) • y := by
    calc
      finiteAlphabetFirstMoment v νp =
          (p : ℝ) • finiteAlphabetFirstMoment v ν₁ +
            (unitInterval.symm p : ℝ) • finiteAlphabetFirstMoment v ν₂ := by
              simpa [νp] using
                (finiteAlphabetFirstMoment_convexCombination
                  (v := v) (ν₁ := ν₁) (ν₂ := ν₂) (p := p))
      _ = (p : ℝ) • x + (unitInterval.symm p : ℝ) • y := by
            rw [hMoment₁, hMoment₂]
  simpa [finiteAlphabetMomentFiber] using hMixedMoment

/-- Helper for Example 23.15: on the effective support hull, the real-valued contracted Sanov
rate is convex. -/
theorem convexOn_finiteAlphabetSanovRateReal_supportHull {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) :
    ConvexOn ℝ (finiteAlphabetSupportHull μ v)
      (fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x).toReal) := by
  refine ⟨finiteAlphabetSupportHull_convex (μ := μ) (v := v), ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨νx, hνxFiber, hνxAc, hνxEq⟩ :=
    finiteAlphabetSanovRate_hasMinimizerOnFiber (μ := μ) (v := v) hx
  obtain ⟨νy, hνyFiber, hνyAc, hνyEq⟩ :=
    finiteAlphabetSanovRate_hasMinimizerOnFiber (μ := μ) (v := v) hy
  let p : Set.Icc (0 : ℝ) 1 := ⟨a, ha, by linarith [hb, hab]⟩
  let νp : ProbabilityMeasure α :=
    ⟨unitInterval.toNNReal p • (νx : Measure α) +
        unitInterval.toNNReal (unitInterval.symm p) • (νy : Measure α), inferInstance⟩
  have hpSum : (p : ℝ) + (unitInterval.symm p : ℝ) = 1 := by
    have hWeights := congrArg (fun q : NNReal ↦ (q : ℝ))
      (unitInterval.toNNReal_add_toNNReal_symm p)
    simpa only [unitInterval.coe_symm_eq] using hWeights
  have hMixedHull :
      (p : ℝ) • x + (unitInterval.symm p : ℝ) • y ∈ finiteAlphabetSupportHull μ v := by
    exact (finiteAlphabetSupportHull_convex (μ := μ) (v := v)) hx hy p.2.1
      (unitInterval.symm p).2.1 hpSum
  have hνpFiber :
      νp ∈ finiteAlphabetMomentFiber v ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y) := by
    simpa [νp] using
      finiteAlphabetMixedWitness_memMomentFiber
        (v := v) (ν₁ := νx) (ν₂ := νy) (x := x) (y := y) (p := p) hνxFiber hνyFiber
  have hνpAc : (νp : Measure α) ≪ (μ : Measure α) := by
    refine absolutelyContinuous_of_forall_nullSingleton ?_
    intro z hμz
    have hνxz : (νx : Measure α) {z} = 0 := hνxAc hμz
    have hνyz : (νy : Measure α) {z} = 0 := hνyAc hμz
    change
      (unitInterval.toNNReal p • (νx : Measure α) +
          unitInterval.toNNReal (unitInterval.symm p) • (νy : Measure α)) ({z} : Set α) = 0
    simp [Measure.add_apply, Measure.smul_apply, hνxz, hνyz]
  have hνpFinite :
      InformationTheory.klDiv (νp : Measure α) (μ : Measure α) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top_iff.mpr ⟨hνpAc, Integrable.of_finite⟩
  have hMixedRateNeTop :
      finiteAlphabetSanovRateFunction μ v ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y) ≠ ⊤ :=
    finiteAlphabetSanovRate_ne_top_of_memSupportHull (μ := μ) (v := v) hMixedHull
  have hMixedRateLe :
      finiteAlphabetSanovRateFunction μ v ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y) ≤
        InformationTheory.klDiv (νp : Measure α) (μ : Measure α) := by
    exact sInf_le ⟨νp, hνpFiber, rfl⟩
  have hMixedToRealLe :
      (finiteAlphabetSanovRateFunction μ v
        ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y)).toReal ≤
        (InformationTheory.klDiv (νp : Measure α) (μ : Measure α)).toReal := by
    exact (ENNReal.toReal_le_toReal hMixedRateNeTop hνpFinite).2 hMixedRateLe
  have hKlConvex :
      (InformationTheory.klDiv (νp : Measure α) (μ : Measure α)).toReal ≤
        (p : ℝ) * (finiteAlphabetSanovRateFunction μ v x).toReal +
          (unitInterval.symm p : ℝ) *
            (finiteAlphabetSanovRateFunction μ v y).toReal := by
    -- Route correction: the previous proof stalled on the subtype-wrapped mixed witness, so the
    -- mixed-moment rewrite is now factored into dedicated helper lemmas before applying KL
    -- convexity.
    simpa [νp, hνxEq, hνyEq] using
      (finiteAlphabetKlDivToReal_convexCombination
        (μ := μ) (ν₁ := νx) (ν₂ := νy) hνxAc hνyAc p)
  have hSymmEq : (unitInterval.symm p : ℝ) = b := by
    have hSymmFormula : (unitInterval.symm p : ℝ) = 1 - a := by
      simp [p, unitInterval.coe_symm_eq]
    linarith [hab, hSymmFormula]
  have hMixedPointEq :
      a • x + b • y = (p : ℝ) • x + (unitInterval.symm p : ℝ) • y := by
    rw [← hSymmEq]
  have hCoeffEq :
      (p : ℝ) * (finiteAlphabetSanovRateFunction μ v x).toReal +
          (unitInterval.symm p : ℝ) * (finiteAlphabetSanovRateFunction μ v y).toReal =
        a * (finiteAlphabetSanovRateFunction μ v x).toReal +
          b * (finiteAlphabetSanovRateFunction μ v y).toReal := by
    rw [hSymmEq]
  -- Proof comment: `p` is only a packaged form of the convex coefficient `a`, so the mixed-point
  -- inequality above is exactly the `ConvexOn` inequality for the original coefficients `a` and
  -- `b`.
  calc
    (finiteAlphabetSanovRateFunction μ v (a • x + b • y)).toReal
        = (finiteAlphabetSanovRateFunction μ v
            ((p : ℝ) • x + (unitInterval.symm p : ℝ) • y)).toReal := by
              rw [hMixedPointEq]
    _ ≤ (p : ℝ) * (finiteAlphabetSanovRateFunction μ v x).toReal +
          (unitInterval.symm p : ℝ) *
            (finiteAlphabetSanovRateFunction μ v y).toReal := hMixedToRealLe.trans hKlConvex
    _ = a * (finiteAlphabetSanovRateFunction μ v x).toReal +
          b * (finiteAlphabetSanovRateFunction μ v y).toReal := by
            rw [hCoeffEq]

/-- Helper for Example 23.15: the KL divergence of the exponential tilt of `μ` is exactly the
affine Legendre gap `⟨t, m(ν_t)⟩ - Λ(t)`. -/
theorem finiteAlphabetTiltedKlDivToReal_eq_affineGap {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (t : Fin d → ℝ) :
    let f : α → ℝ := fun a ↦ ∑ i, t i * v a i
    let νt : ProbabilityMeasure α :=
      ⟨(μ : Measure α).tilted f, MeasureTheory.isProbabilityMeasure_tilted (Integrable.of_finite)⟩
    (InformationTheory.klDiv (νt : Measure α) (μ : Measure α)).toReal =
      (∑ i, t i * finiteAlphabetFirstMoment v νt i) -
        finiteAlphabetLogMomentGeneratingFunction μ v t := by
  classical
  let f : α → ℝ := fun a ↦ ∑ i, t i * v a i
  let νt : ProbabilityMeasure α :=
    ⟨(μ : Measure α).tilted f, MeasureTheory.isProbabilityMeasure_tilted (Integrable.of_finite)⟩
  have hExpμ : Integrable (fun a ↦ Real.exp (f a)) (μ : Measure α) := Integrable.of_finite
  have hνtAc : (νt : Measure α) ≪ (μ : Measure α) := by
    dsimp [νt]
    exact MeasureTheory.tilted_absolutelyContinuous (μ := (μ : Measure α)) f
  have hUniv :
      (νt : Measure α) Set.univ = (μ : Measure α) Set.univ := by
    simp
  have hMoment :
      ∫ a, f a ∂(νt : Measure α) = ∑ i, t i * finiteAlphabetFirstMoment v νt i := by
    rw [MeasureTheory.integral_fintype (μ := (νt : Measure α)) (f := f) Integrable.of_finite]
    simp only [f, smul_eq_mul]
    calc
      ∑ a, (νt : Measure α).real {a} * ∑ i, t i * v a i
          = ∑ a, ∑ i, (νt : Measure α).real {a} * (t i * v a i) := by
              refine Finset.sum_congr rfl fun a _ ↦ ?_
              rw [Finset.mul_sum]
      _ = ∑ i, ∑ a, (νt : Measure α).real {a} * (t i * v a i) := by
            rw [Finset.sum_comm]
      _ = ∑ i, t i * ∑ a, (νt : Measure α).real {a} * v a i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            calc
              ∑ a, (νt : Measure α).real {a} * (t i * v a i)
                  = ∑ a, t i * ((νt : Measure α).real {a} * v a i) := by
                      refine Finset.sum_congr rfl fun a _ ↦ ?_
                      ring
              _ = t i * ∑ a, (νt : Measure α).real {a} * v a i := by
                    rw [Finset.mul_sum]
      _ = ∑ i, t i * finiteAlphabetFirstMoment v νt i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have hCoord :
                ∑ a, (νt : Measure α).real {a} * v a i = finiteAlphabetFirstMoment v νt i := by
              rw [finiteAlphabetFirstMoment]
              refine Finset.sum_congr rfl fun a _ ↦ ?_
              rw [ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := νt) ({a} : Set α)]
            rw [hCoord]
  have hLogMgf :
      Real.log (∫ a, Real.exp (f a) ∂(μ : Measure α)) =
        finiteAlphabetLogMomentGeneratingFunction μ v t := by
    rw [MeasureTheory.integral_fintype (μ := (μ : Measure α)) (f := fun a ↦ Real.exp (f a))
      hExpμ]
    have hMass :
        ∀ a : α, (μ : Measure α).real {a} = (((μ {a} : NNReal) : ℝ)) := by
      intro a
      simpa [Measure.real] using
        (ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := μ) ({a} : Set α)).symm
    have hSumMass :
        ∑ a, (μ : Measure α).real {a} * Real.exp (f a) =
          ∑ a, (((μ {a} : NNReal) : ℝ)) * Real.exp (f a) := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hMass a]
    calc
      Real.log (∑ a, (μ : Measure α).real {a} * Real.exp (f a))
          = Real.log (∑ a, (((μ {a} : NNReal) : ℝ)) * Real.exp (f a)) := by
              rw [hSumMass]
      _ = finiteAlphabetLogMomentGeneratingFunction μ v t := by
            simp [f, finiteAlphabetLogMomentGeneratingFunction]
  have hSelf :
      ∫ a, MeasureTheory.llr (νt : Measure α) ((μ : Measure α).tilted f) a
          ∂(νt : Measure α) = 0 := by
    change ∫ a, MeasureTheory.llr (νt : Measure α) (νt : Measure α) a ∂(νt : Measure α) = 0
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.llr_self (νt : Measure α))]
    simp
  have hLlr :
      ∫ a, MeasureTheory.llr (νt : Measure α) (μ : Measure α) a ∂(νt : Measure α) =
        ∫ a, f a ∂(νt : Measure α) - Real.log (∫ a, Real.exp (f a) ∂(μ : Measure α)) := by
    have hTilt :=
      MeasureTheory.integral_llr_tilted_right
        (μ := (νt : Measure α)) (ν := (μ : Measure α)) (f := f)
        hνtAc Integrable.of_finite hExpμ Integrable.of_finite
    -- Proof comment: compare `ν_t` with its own tilt; the left-hand side vanishes, leaving the
    -- exact affine-gap identity for `KL(ν_t | μ)`.
    linarith
  calc
    (InformationTheory.klDiv (νt : Measure α) (μ : Measure α)).toReal
        = ∫ a, MeasureTheory.llr (νt : Measure α) (μ : Measure α) a ∂(νt : Measure α) := by
            rw [InformationTheory.toReal_klDiv_of_measure_eq hνtAc hUniv]
    _ = ∫ a, f a ∂(νt : Measure α) - Real.log (∫ a, Real.exp (f a) ∂(μ : Measure α)) := hLlr
    _ = (∑ i, t i * finiteAlphabetFirstMoment v νt i) -
          finiteAlphabetLogMomentGeneratingFunction μ v t := by
          rw [hMoment, hLogMgf]

/-- Helper for Example 23.15: on the effective support hull, the contracted Sanov rate is bounded
above by the Legendre-transform rate function. -/
theorem finiteAlphabetSanovRateFunction_le_legendreRateFunction_of_memSupportHull {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ finiteAlphabetSupportHull μ v) :
    finiteAlphabetSanovRateFunction μ v x ≤ finiteAlphabetLegendreRateFunction μ v x := by
  have hRateNeTop :
      finiteAlphabetSanovRateFunction μ v x ≠ ⊤ :=
    finiteAlphabetSanovRate_ne_top_of_memSupportHull (μ := μ) (v := v) hx
  have hLegLe :
      finiteAlphabetLegendreRateFunction μ v x ≤ finiteAlphabetSanovRateFunction μ v x :=
    finiteAlphabetLegendreRateFunction_le_sanovRateFunction (μ := μ) (v := v) (x := x)
  have hLegNeTop :
      finiteAlphabetLegendreRateFunction μ v x ≠ ⊤ :=
    ne_top_of_le_ne_top hRateNeTop hLegLe
  have hConvex :=
    convexOn_finiteAlphabetSanovRateReal_supportHull (μ := μ) (v := v)
  have hLsc :=
    lowerSemicontinuousOn_finiteAlphabetSanovRateReal_supportHull (μ := μ) (v := v)
  by_contra hNotLe
  have hRealLt :
      (finiteAlphabetLegendreRateFunction μ v x).toReal <
        (finiteAlphabetSanovRateFunction μ v x).toReal := by
    have hNotReal :
        ¬ (finiteAlphabetSanovRateFunction μ v x).toReal ≤
            (finiteAlphabetLegendreRateFunction μ v x).toReal := by
      intro hRealLe
      apply hNotLe
      rw [← ENNReal.ofReal_toReal hRateNeTop, ← ENNReal.ofReal_toReal hLegNeTop]
      exact ENNReal.ofReal_le_ofReal hRealLe
    exact lt_of_not_ge hNotReal
  let r : ℝ :=
    ((finiteAlphabetSanovRateFunction μ v x).toReal +
      (finiteAlphabetLegendreRateFunction μ v x).toReal) / 2
  have hrLt :
      r < (finiteAlphabetSanovRateFunction μ v x).toReal := by
    dsimp [r]
    linarith
  have hLegLtR : (finiteAlphabetLegendreRateFunction μ v x).toReal < r := by
    dsimp [r]
    linarith
  have hrPos : 0 < r := by
    linarith [ENNReal.toReal_nonneg (a := finiteAlphabetLegendreRateFunction μ v x), hLegLtR]
  obtain ⟨l, c, hlower, hlx⟩ :=
    hConvex.exists_affine_le_of_lt (𝕜 := ℝ) (x := x) (a := r) hx hrLt
      (finiteAlphabetSupportHull_isClosed (μ := μ) (v := v)) hLsc
  let t : Fin d → ℝ := fun i ↦ l (fun j : Fin d ↦ if i = j then 1 else 0)
  have hLinear (y : Fin d → ℝ) : l y = ∑ i, y i * t i := by
    simpa [t, smul_eq_mul] using (LinearMap.pi_apply_eq_sum_univ (f := l.toLinearMap) y)
  have hAffineLower :
      ∀ y ∈ finiteAlphabetSupportHull μ v,
        (∑ i, t i * y i) + c ≤ (finiteAlphabetSanovRateFunction μ v y).toReal := by
    intro y hy
    have hy' := hlower ⟨y, hy⟩
    simpa [hLinear y, mul_comm] using hy'
  have hAtX : r = (∑ i, t i * x i) + c := by
    have hlx' : (∑ i, x i * t i) + c = r := by
      simpa [hLinear x] using hlx
    simpa [mul_comm] using hlx'.symm
  let f : α → ℝ := fun a ↦ ∑ i, t i * v a i
  let νt : ProbabilityMeasure α :=
    ⟨(μ : Measure α).tilted f, MeasureTheory.isProbabilityMeasure_tilted (Integrable.of_finite)⟩
  have hνtAc : (νt : Measure α) ≪ (μ : Measure α) := by
    dsimp [νt]
    exact MeasureTheory.tilted_absolutelyContinuous (μ := (μ : Measure α)) f
  have hνtHull :
      finiteAlphabetFirstMoment v νt ∈ finiteAlphabetSupportHull μ v :=
    finiteAlphabetFirstMoment_memSupportHull_of_absolutelyContinuous
      (μ := μ) (ν := νt) (v := v) hνtAc
  have hνtFiber :
      νt ∈ finiteAlphabetMomentFiber v (finiteAlphabetFirstMoment v νt) := by
    simp [finiteAlphabetMomentFiber]
  have hRateAtTilt :
      finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v νt) ≤
        InformationTheory.klDiv (νt : Measure α) (μ : Measure α) := by
    rw [finiteAlphabetSanovRateFunction]
    exact sInf_le ⟨νt, hνtFiber, rfl⟩
  have hRateAtTiltNeTop :
      finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v νt) ≠ ⊤ :=
    finiteAlphabetSanovRate_ne_top_of_memSupportHull (μ := μ) (v := v) hνtHull
  have hKlAtTiltNeTop :
      InformationTheory.klDiv (νt : Measure α) (μ : Measure α) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top_iff.mpr ⟨hνtAc, Integrable.of_finite⟩
  have hRateAtTiltReal :
      (finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v νt)).toReal ≤
        (InformationTheory.klDiv (νt : Measure α) (μ : Measure α)).toReal := by
    exact (ENNReal.toReal_le_toReal hRateAtTiltNeTop hKlAtTiltNeTop).2 hRateAtTilt
  have hAffineAtTilt :
      (∑ i, t i * finiteAlphabetFirstMoment v νt i) + c ≤
        (finiteAlphabetSanovRateFunction μ v (finiteAlphabetFirstMoment v νt)).toReal :=
    hAffineLower (finiteAlphabetFirstMoment v νt) hνtHull
  have hTiltEq :=
    finiteAlphabetTiltedKlDivToReal_eq_affineGap (μ := μ) (v := v) (t := t)
  have hConst :
      c ≤ -finiteAlphabetLogMomentGeneratingFunction μ v t := by
    -- Proof comment: evaluate the affine minorant at the exponentially tilted law `ν_t`; the
    -- exact tilted-law KL identity turns the generic fiber bound into a bound on the constant
    -- term of the affine minorant.
    linarith [hAffineAtTilt, hRateAtTiltReal, hTiltEq]
  have hWitnessLe :
      r ≤ (∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t := by
    linarith [hAtX, hConst]
  have hWitnessENN :
      ENNReal.ofReal ((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t) ≤
        finiteAlphabetLegendreRateFunction μ v x := by
    rw [finiteAlphabetLegendreRateFunction_def]
    exact EReal.toENNReal_le_toENNReal <|
      show ((((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal)) ≤
          sSup
            (Set.range fun s : Fin d → ℝ ↦
              (((∑ i, s i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v s : ℝ) :
                EReal)) from
        le_sSup (Set.mem_range_self t)
  have hrLeLeg :
      r ≤ (finiteAlphabetLegendreRateFunction μ v x).toReal := by
    have hOfReal :
        ENNReal.ofReal r ≤ finiteAlphabetLegendreRateFunction μ v x := by
      exact (ENNReal.ofReal_le_ofReal hWitnessLe).trans hWitnessENN
    exact (ENNReal.ofReal_le_iff_le_toReal hLegNeTop).1 hOfReal
  exact (not_lt_of_ge hrLeLeg) hLegLtR

/-- Helper for Example 23.15: the contracted Sanov rate agrees with the
Legendre-transform rate function. -/
theorem finiteAlphabetSanovRateFunction_eq_legendreRateFunction {α : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    finiteAlphabetSanovRateFunction μ v x = finiteAlphabetLegendreRateFunction μ v x := by
  -- Route correction: the transport/law side is now isolated, so the only remaining work is the
  -- finite-alphabet variational identity `inf_{m(ν)=x} H(ν | μ) = sup_t (⟨t, x⟩ - Λ(t))` on the
  -- effective support hull; the outside-hull `⊤` branch is now separated into a dedicated helper.
  by_cases hxHull : x ∈ finiteAlphabetSupportHull μ v
  · have hEasy :
        finiteAlphabetLegendreRateFunction μ v x ≤ finiteAlphabetSanovRateFunction μ v x :=
      finiteAlphabetLegendreRateFunction_le_sanovRateFunction (μ := μ) (v := v) (x := x)
    have hHard :
        finiteAlphabetSanovRateFunction μ v x ≤ finiteAlphabetLegendreRateFunction μ v x :=
      finiteAlphabetSanovRateFunction_le_legendreRateFunction_of_memSupportHull
        (μ := μ) (v := v) hxHull
    exact le_antisymm hHard hEasy
  · -- Proof comment: outside the effective support hull, the Legendre transform already equals
    -- `⊤`; the easy inequality `Λ* ≤ I` therefore forces the contracted Sanov rate to be `⊤`.
    have hLegendre :
        finiteAlphabetLegendreRateFunction μ v x = ⊤ :=
      finiteAlphabetLegendreRateFunction_eq_top_of_not_memSupportHull
        (μ := μ) (v := v) hxHull
    have hEasy :
        finiteAlphabetLegendreRateFunction μ v x ≤ finiteAlphabetSanovRateFunction μ v x :=
      finiteAlphabetLegendreRateFunction_le_sanovRateFunction (μ := μ) (v := v) (x := x)
    have hSanov :
        finiteAlphabetSanovRateFunction μ v x = ⊤ := by
      rw [hLegendre] at hEasy
      exact le_antisymm le_top hEasy
    simp [hSanov, hLegendre]

-- Proof sketch: apply Sanov's theorem to the empirical measures of the finite-alphabet sequence,
-- push the resulting LDP forward along the continuous first-moment map, and identify the
-- contraction rate with the Legendre transform `Λ*`.
/-- Example 23.15: let `μ` be a probability measure on a finite alphabet `α`, let `X 0, X 1, …`
be independent `α`-valued random variables with common law `μ`, and let `v : α → Fin d → ℝ`
realize the alphabet as a finite subset of `ℝ^d`. Then the laws of the empirical means of the
vectors `v (X n)` satisfy a large deviations principle at speed `n + 1` with rate function `Λ*`,
the Legendre transform of the finite-alphabet log moment generating function. This is the chapter's
`0`-based version of the book's statement about `S_n / n`. -/
theorem finiteAlphabetEmpiricalMean_hasLargeDeviationsPrinciple {Ω : Type u} [MeasurableSpace Ω]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α] {d : ℕ} [Fintype α]
    (P : ProbabilityMeasure Ω) (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ)
    (X : ℕ → Ω → α) (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω)) :
    iIndepFun X (P : Measure Ω) →
      (∀ n, Measure.map (X n) (P : Measure Ω) = (μ : Measure α)) →
      HasLargeDeviationsPrincipleAlong
        (finiteAlphabetEmpiricalMeanLaw P v X hXmeas)
        finiteAlphabetSpeed
        atTop
        (finiteAlphabetLegendreRateFunction μ v) := by
  intro hindep hLaw
  classical
  letI : TopologicalSpace α := ⊥
  letI : DiscreteTopology α := ⟨rfl⟩
  letI : BorelSpace α := inferInstance
  obtain ⟨Y, hYmeas, hXY, hYindep, hYlaw⟩ :=
    measurableIndependentVersionWithLaw P μ X hXmeas hindep hLaw
  have hYae : ∀ n, AEMeasurable (Y n) (P : Measure Ω) := fun n ↦ (hYmeas n).aemeasurable
  have hMeanLaw :
      ∀ n,
        finiteAlphabetEmpiricalMeanLaw P v X hXmeas n =
          finiteAlphabetEmpiricalMeanLaw P v Y hYae n :=
    finiteAlphabetEmpiricalMeanLaw_congr_ae
      (P := P) (v := v) (X := X) (Y := Y) (hXmeas := hXmeas) (hYmeas := hYae) hXY
  have hMeanLawMeasure :
      (fun n ↦ (finiteAlphabetEmpiricalMeanLaw P v X hXmeas n : Measure (Fin d → ℝ))) =
        fun n ↦ (finiteAlphabetEmpiricalMeanLaw P v Y hYae n : Measure (Fin d → ℝ)) := by
    funext n
    exact congrArg (fun ρ : ProbabilityMeasure (Fin d → ℝ) ↦ (ρ : Measure (Fin d → ℝ)))
      (hMeanLaw n)
  have hident : ∀ n, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω) := by
    intro n
    refine
      { aemeasurable_fst := (hYmeas n).aemeasurable
        aemeasurable_snd := (hYmeas 0).aemeasurable
        map_eq := ?_ }
    rw [hYlaw n, hYlaw 0]
  have hμ :
      ProbabilityMeasure.map ⟨(P : Measure Ω), inferInstance⟩ (hYmeas 0).aemeasurable = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa using hYlaw 0
  have hSanov :=
    sanov_empiricalMeasure_largeDeviations
      (P := (P : Measure Ω)) (X := Y) (hX := hYmeas) (μ := μ) hYindep hident hμ
  have hRateEReal :
      ∀ x : Fin d → ℝ,
        (finiteAlphabetSanovRateFunction μ v x : EReal) =
          (finiteAlphabetLegendreRateFunction μ v x : EReal) := by
    intro x
    exact congrArg (fun r : ENNReal ↦ (r : EReal))
      (finiteAlphabetSanovRateFunction_eq_legendreRateFunction (μ := μ) (v := v) (x := x))
  refine
    { lowerSemicontinuous := lowerSemicontinuous_finiteAlphabetLegendreRateFunction μ v
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    have hPreimageOpen : IsOpen ((finiteAlphabetFirstMoment v) ⁻¹' U) :=
      IsOpen.preimage (continuous_finiteAlphabetFirstMoment (v := v)) hU
    have hLower :=
      hSanov.2 ((finiteAlphabetFirstMoment v) ⁻¹' U) hPreimageOpen
    have hScaled :
        scaledLogMassAlong
            (fun n ↦
              (finiteAlphabetEmpiricalMeanLaw P v Y hYae n : Measure (Fin d → ℝ)))
            finiteAlphabetSpeed
            U =
          fun n : ℕ ↦
            ((n + 1 : ℝ) : EReal)⁻¹ *
              ENNReal.log
                (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                    Measure (ProbabilityMeasure α))
                  ((finiteAlphabetFirstMoment v) ⁻¹' U))) := by
      funext n
      rw [scaledLogMassAlong_def,
        finiteAlphabetEmpiricalMeanLaw_apply_eq_empiricalMeasureLaw_preimage
          (P := P) (v := v) (Y := Y) (hYmeas := hYmeas)
          (s := U) (hs := hU.measurableSet) (n := n)]
      simp [finiteAlphabetSpeed, EReal.coe_inv]
    have hRateImageEq :
        ((fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x : EReal)) '' U) =
          ((fun x : Fin d → ℝ ↦ (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) := by
      ext y
      constructor
      · rintro ⟨x, hxU, rfl⟩
        exact ⟨x, hxU, (hRateEReal x).symm⟩
      · rintro ⟨x, hxU, rfl⟩
        exact ⟨x, hxU, hRateEReal x⟩
    have hInfLe :
        sInf ((fun ν : ProbabilityMeasure α ↦
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
            ((finiteAlphabetFirstMoment v) ⁻¹' U)) ≤
          sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) := by
      calc
        sInf ((fun ν : ProbabilityMeasure α ↦
          (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
            ((finiteAlphabetFirstMoment v) ⁻¹' U)) ≤
            sInf ((fun x : Fin d → ℝ ↦
              (finiteAlphabetSanovRateFunction μ v x : EReal)) '' U) :=
          sInf_klDiv_firstMomentPreimage_le_sInf_sanovRate (μ := μ) (v := v) (s := U)
        _ = sInf ((fun x : Fin d → ℝ ↦
          (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) := by
            rw [hRateImageEq]
    have hLowerExplicit :
        -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) ≤
          Filter.liminf
            (fun n : ℕ ↦
              ((n + 1 : ℝ) : EReal)⁻¹ *
                ENNReal.log
                  (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                      Measure (ProbabilityMeasure α))
                    ((finiteAlphabetFirstMoment v) ⁻¹' U))))
            atTop := by
      -- Proof comment: Sanov gives the lower bound on the first-moment preimage, and the
      -- set-level contraction comparison plus rate identification transports it to the empirical
      -- means of the measurable version `Y`.
      have hNeg :
          -sInf ((fun x : Fin d → ℝ ↦
              (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) ≤
            -sInf ((fun ν : ProbabilityMeasure α ↦
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
                ((finiteAlphabetFirstMoment v) ⁻¹' U)) := by
        rwa [EReal.neg_le_neg_iff]
      calc
        -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) ≤
            -sInf ((fun ν : ProbabilityMeasure α ↦
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
                ((finiteAlphabetFirstMoment v) ⁻¹' U)) := hNeg
        _ ≤
            Filter.liminf
              (fun n : ℕ ↦
                ((n + 1 : ℝ) : EReal)⁻¹ *
                  ENNReal.log
                    (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                        Measure (ProbabilityMeasure α))
                      ((finiteAlphabetFirstMoment v) ⁻¹' U))))
              atTop := hLower
    have hLowerY :
        -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' U) ≤
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦
                (finiteAlphabetEmpiricalMeanLaw P v Y hYae n : Measure (Fin d → ℝ)))
              finiteAlphabetSpeed
              U)
            atTop := by
      simpa [hScaled] using hLowerExplicit
    simpa [hMeanLawMeasure] using hLowerY
  · intro C hC
    have hPreimageClosed : IsClosed ((finiteAlphabetFirstMoment v) ⁻¹' C) :=
      IsClosed.preimage (continuous_finiteAlphabetFirstMoment (v := v)) hC
    have hUpper :=
      hSanov.1 ((finiteAlphabetFirstMoment v) ⁻¹' C) hPreimageClosed
    have hScaled :
        scaledLogMassAlong
            (fun n ↦
              (finiteAlphabetEmpiricalMeanLaw P v Y hYae n : Measure (Fin d → ℝ)))
            finiteAlphabetSpeed
            C =
          fun n : ℕ ↦
            ((n + 1 : ℝ) : EReal)⁻¹ *
              ENNReal.log
                (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                    Measure (ProbabilityMeasure α))
                  ((finiteAlphabetFirstMoment v) ⁻¹' C))) := by
      funext n
      rw [scaledLogMassAlong_def,
        finiteAlphabetEmpiricalMeanLaw_apply_eq_empiricalMeasureLaw_preimage
          (P := P) (v := v) (Y := Y) (hYmeas := hYmeas)
          (s := C) (hs := hC.measurableSet) (n := n)]
      simp [finiteAlphabetSpeed, EReal.coe_inv]
    have hRateImageEq :
        ((fun x : Fin d → ℝ ↦ (finiteAlphabetSanovRateFunction μ v x : EReal)) '' C) =
          ((fun x : Fin d → ℝ ↦ (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) := by
      ext y
      constructor
      · rintro ⟨x, hxC, rfl⟩
        exact ⟨x, hxC, (hRateEReal x).symm⟩
      · rintro ⟨x, hxC, rfl⟩
        exact ⟨x, hxC, hRateEReal x⟩
    have hInfLe :
        sInf ((fun x : Fin d → ℝ ↦
          (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) ≤
          sInf ((fun ν : ProbabilityMeasure α ↦
            (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
              ((finiteAlphabetFirstMoment v) ⁻¹' C)) := by
      calc
        sInf ((fun x : Fin d → ℝ ↦
          (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) =
            sInf ((fun x : Fin d → ℝ ↦
              (finiteAlphabetSanovRateFunction μ v x : EReal)) '' C) := by
                rw [← hRateImageEq]
        _ ≤
            sInf ((fun ν : ProbabilityMeasure α ↦
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
                ((finiteAlphabetFirstMoment v) ⁻¹' C)) :=
          sInf_sanovRate_le_sInf_klDiv_firstMomentPreimage (μ := μ) (v := v) (s := C)
    have hUpperExplicit :
        Filter.limsup
            (fun n : ℕ ↦
              ((n + 1 : ℝ) : EReal)⁻¹ *
                ENNReal.log
                  (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                      Measure (ProbabilityMeasure α))
                    ((finiteAlphabetFirstMoment v) ⁻¹' C))))
            atTop ≤
          -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) := by
      -- Proof comment: the closed bound uses the reverse set-level comparison, because negation
      -- reverses the order between the rate infima.
      have hNeg :
          -sInf ((fun ν : ProbabilityMeasure α ↦
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
                ((finiteAlphabetFirstMoment v) ⁻¹' C)) ≤
            -sInf ((fun x : Fin d → ℝ ↦
              (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) := by
        rwa [EReal.neg_le_neg_iff]
      calc
        Filter.limsup
            (fun n : ℕ ↦
              ((n + 1 : ℝ) : EReal)⁻¹ *
                ENNReal.log
                  (((empiricalMeasureLaw (P : Measure Ω) Y hYmeas n :
                      Measure (ProbabilityMeasure α))
                    ((finiteAlphabetFirstMoment v) ⁻¹' C))))
            atTop ≤
            -sInf ((fun ν : ProbabilityMeasure α ↦
              (InformationTheory.klDiv (ν : Measure α) (μ : Measure α) : EReal)) ''
                ((finiteAlphabetFirstMoment v) ⁻¹' C)) := hUpper
        _ ≤ -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) := hNeg
    have hUpperY :
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦
                (finiteAlphabetEmpiricalMeanLaw P v Y hYae n : Measure (Fin d → ℝ)))
              finiteAlphabetSpeed
              C)
            atTop ≤
          -sInf ((fun x : Fin d → ℝ ↦
            (finiteAlphabetLegendreRateFunction μ v x : EReal)) '' C) := by
      simpa [hScaled] using hUpperExplicit
    simpa [hMeanLawMeasure] using hUpperY

end ProbabilityTheory
