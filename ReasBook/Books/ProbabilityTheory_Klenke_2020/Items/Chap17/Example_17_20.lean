/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 17.20: Chapter 17's source-facing owner says that a process has the
natural Markov property under `μ` when each coordinate is measurable and conditioning a future
state event on the whole history agrees almost surely with conditioning only on the present
state. -/
def HasNaturalMarkovProperty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℕ) : Prop :=
  (∀ t : ℕ, Measurable (X t)) ∧
    ∀ ⦃s t : ℕ⦄, s ≤ t → ∀ ⦃A : Set ℕ⦄, MeasurableSet A →
      μ⟦X t ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[μ]
        μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) inferInstance⟧

/-- Helper for Example 17.20: the branching process started from `x` and driven by the offspring
array `Y`. -/
def branchingProcess (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ ↦ x
  | n + 1 => fun ω ↦ Finset.sum (Finset.range (branchingProcess x Y n ω)) (fun i ↦ Y n i ω)

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the branching process starts from the deterministic population `x`.
-/
theorem branchingProcess_zero (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    branchingProcess x Y 0 = fun _ ↦ x := rfl

end

/-- Helper for Example 17.20: if each offspring coordinate is measurable, then every generation
size in the branching process is measurable. -/
private lemma measurable_branchingProcess
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (hY_meas : ∀ n i, Measurable (Y n i)) :
    ∀ n, Measurable (branchingProcess x Y n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial population is the constant map `x`.
      simp [branchingProcess_zero]
  | succ n ih =>
      -- Proof comment: the successor generation is a measurable random sum of measurable
      -- offspring counts over the measurable parent-count variable.
      simpa [branchingProcess] using
        measurable_natRandomSum (branchingProcess x Y n) ih (fun i ↦ Y n i) (hY_meas n)

/-- Helper for Example 17.20: a finite history tuple is measurable once each process coordinate is
measurable. -/
private lemma measurable_historyTupleLocal {E : Type*} [MeasurableSpace E] {n : ℕ}
    (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ) (hX : ∀ t, Measurable (X t)) :
    Measurable (fun ω k ↦ X (times k) ω) := by
  -- Proof comment: a function into a finite product is measurable exactly when each coordinate is.
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact hX (times k)

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the finite history tuple is measurable with respect to the
generated filtration at its terminal time. -/
private lemma historyTuple_comap_le_generatedFiltrationSpaceLocal {E : Type*}
    [MeasurableSpace E] {n : ℕ} (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ)
    (htimes : StrictMono times) :
    MeasurableSpace.comap (fun ω k ↦ X (times k) ω)
      (inferInstance : MeasurableSpace (Fin (n + 1) → E)) ≤
      generatedFiltrationSpace X (times (Fin.last n)) := by
  let _ : MeasurableSpace Ω := generatedFiltrationSpace X (times (Fin.last n))
  have hmeas :
      Measurable[generatedFiltrationSpace X (times (Fin.last n))]
        (fun ω k ↦ X (times k) ω) := by
    -- Proof comment: every observed time `times k` lies below the terminal time `times (last n)`.
    refine measurable_pi_iff.2 fun k ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    exact le_iSup_of_le (times k) <| le_iSup_of_le
      (htimes.monotone (Fin.le_last k)) le_rfl
  simpa using hmeas.comap_le

end

/- Example 17.20 is `source-facing`: for an arbitrary initial population `x`, the branching
process `branchingProcess x Y` driven by an i.i.d. offspring array has one-step law
`p(x,y) = q_y^{*x}`. The primitive data is the recursive offspring-convolution family `q^{*x}`.
Its `core/canonical` one-step owner is the stochastic matrix
`branchingTransitionMatrix q : ℕ → ℕ → ℝ≥0∞` together with the associated discrete kernel
`branchingTransitionKernel q = discreteMatrixKernel (branchingTransitionMatrix q)`. The
real-valued singleton formula is only a `bridge/view` companion. At the process level, the
source-facing Chapter 17 owner is `HasNaturalMarkovProperty μ Z`, while the generated-filtration
surface `HasMarkovProperty (generatedFiltration Z hZ) μ Z` is the canonical bridge used to prove
it. The one-ancestor Chapter 3 owner `IsGaltonWatsonProcess Z μ q` is only a `bridge/view`
specialization for Example 17.20 after adding genuine measurability of the realized generations,
which rules out the null-set modifications excluded by the source's random-variable wording. -/

/-- The `x`-fold offspring law obtained by convolving the one-particle offspring distribution `q`
`x` times. This is the distribution denoted `q^{*x}` in the textbook. -/
def branchingOffspringPMF (q : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 =>
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l)

scoped notation:arg q "^{*" x "}" => branchingOffspringPMF q x

-- Proof sketch: unfold the recursive definition of `branchingOffspringPMF` at `0`.
/-- The zeroth offspring convolution is the Dirac mass at `0`. -/
theorem branchingOffspringPMF_zero (q : PMF ℕ) :
    branchingOffspringPMF q 0 = PMF.pure 0 := by
  -- Unfold the recursive definition at the initial generation.
  rfl

-- Proof sketch: unfold the recursive definition at `n + 1`; the next convolution adds one more
-- offspring variable with law `q`.
/-- The successor step of the offspring-convolution recursion. -/
theorem branchingOffspringPMF_succ (q : PMF ℕ) (n : ℕ) :
    branchingOffspringPMF q (n + 1) =
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l) := by
  -- Unfold the recursive definition at the successor generation.
  rfl

/-- The branching-process transition matrix `p(x,y) = q^{*x}_y` attached to the offspring
distribution `q`. This is the textbook matrix view of the recursive offspring law. -/
def branchingTransitionMatrix (q : PMF ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  fun x y ↦ branchingOffspringPMF q x y

-- Proof sketch: each row of `branchingTransitionMatrix q` is the PMF `q^{*x}`, so its total mass
-- is `1`.
/-- The branching-process transition matrix is stochastic. -/
theorem branchingTransitionMatrix_isStochasticMatrix (q : PMF ℕ) :
    IsStochasticMatrix (branchingTransitionMatrix q) := by
  intro x
  -- Each row is exactly the PMF `q^{*x}`, so its total mass is `1`.
  simp [branchingTransitionMatrix]

/-- The one-step transition kernel of the branching process associated with the offspring law `q`,
expressed through the canonical discrete-matrix kernel owner. -/
def branchingTransitionKernel (q : PMF ℕ) : Kernel ℕ ℕ :=
  discreteMatrixKernel (branchingTransitionMatrix q)

-- Proof sketch: `branchingTransitionMatrix q` was defined from the row PMFs `q^{*x}`.
/-- Evaluating the branching transition matrix at `(x,y)` gives the `y`-mass of the `x`-fold
offspring convolution. -/
theorem branchingTransitionMatrix_apply (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionMatrix q x y = (q^{*x}) y := rfl

-- Proof sketch: unfold `branchingTransitionKernel`; `discreteMatrixKernel` stores exactly the row
-- measures determined by the point masses `q^{*x}_y`, which is the PMF measure
-- `(branchingOffspringPMF q x).toMeasure`.
/-- Evaluating the branching transition kernel at `x` gives the measure associated with the
`x`-fold offspring PMF. -/
theorem branchingTransitionKernel_apply (q : PMF ℕ) (x : ℕ) :
    branchingTransitionKernel q x = (q^{*x}).toMeasure := by
  -- Compare the two measures on an arbitrary measurable set in the discrete state space `ℕ`.
  ext s hs
  rw [branchingTransitionKernel, discreteMatrixKernel_apply, Measure.sum_apply _ hs,
    PMF.toMeasure_apply _ hs]
  -- The row of the discrete kernel is the indicator expansion of the PMF measure.
  refine tsum_congr fun y ↦ ?_
  by_cases hy : y ∈ s
  · simp [Measure.smul_apply, smul_eq_mul, branchingTransitionMatrix_apply, hy]
  · simp [Measure.smul_apply, smul_eq_mul, branchingTransitionMatrix_apply, hy]

/-- Helper for Example 17.20: the discrete kernel associated with the branching transition matrix
evaluates singleton masses by the corresponding matrix entries. -/
private theorem branchingTransitionKernel_apply_singletonMass (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionKernel q x ({y} : Set ℕ) = branchingTransitionMatrix q x y := by
  rw [branchingTransitionKernel_apply, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton y), branchingTransitionMatrix_apply]

-- Proof sketch: evaluate `branchingTransitionKernel q x` via `branchingTransitionKernel_apply`
-- and then compute the singleton mass of the PMF `q^{*x}`.
/-- The singleton mass of the branching transition kernel is the corresponding stochastic-matrix
entry. -/
theorem branchingTransitionKernel_apply_singleton (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionKernel q x {y} = branchingTransitionMatrix q x y := by
  -- Reduce the singleton mass to the PMF value of `q^{*x}`.
  exact branchingTransitionKernel_apply_singletonMass q x y

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: a random finite sum of relatively measurable offspring counts is
again relatively measurable. -/
private lemma measurable_randomNatSum
    {mΩ : MeasurableSpace Ω} (T : Ω → ℕ) (hT : Measurable[mΩ] T) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, Measurable[mΩ] (X n)) :
    Measurable[mΩ] (fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)) := by
  -- Proof comment: this is exactly the Chapter 3 measurability theorem for `natRandomSum`.
  simpa [natRandomSum] using measurable_natRandomSum T hT X hX

end

/-- Helper for Example 17.20: the current offspring row restricted to its first `m` entries. -/
private def offspringRowPrefix (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) :
    Ω → Fin m → ℕ :=
  fun ω i ↦ Y n i ω

/-- Helper for Example 17.20: the sum of the first `m` offspring counts in row `n`. -/
private def offspringRowSum (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) : Ω → ℕ :=
  fun ω ↦ ∑ i : Fin m, offspringRowPrefix Y n m ω i

/-- Helper for Example 17.20: replace each offspring coordinate by a measurable representative
with the same law under `P`. -/
private def measurableOffspringArray
    (q : PMF ℕ) (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ℕ → ℕ → Ω → ℕ :=
  fun n i ↦ (hY_law n i).aemeasurable.mk (Y n i)

/-- Helper for Example 17.20: each coordinate of the measurable offspring array is measurable. -/
private lemma measurableOffspringArray_measurable
    (q : PMF ℕ) (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ∀ n i, Measurable (measurableOffspringArray q P Y hY_law n i) := by
  intro n i
  exact (hY_law n i).aemeasurable.measurable_mk

/-- Helper for Example 17.20: the measurable offspring array agrees almost everywhere with the
original offspring array coordinatewise. -/
private lemma measurableOffspringArray_ae_eq
    (q : PMF ℕ) (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ∀ n i,
      measurableOffspringArray q P Y hY_law n i =ᵐ[(P : Measure Ω)] Y n i := by
  intro n i
  exact (hY_law n i).aemeasurable.ae_eq_mk.symm

/-- Helper for Example 17.20: replacing the offspring coordinates by measurable representatives
preserves the `iIndepFun` hypothesis. -/
private lemma measurableOffspringArray_iIndep
    (q : PMF ℕ) (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    iIndepFun
      (fun ni : ℕ × ℕ ↦ measurableOffspringArray q P Y hY_law ni.1 ni.2)
      (P : Measure Ω) := by
  refine hY_indep.congr ?_
  intro ni
  exact (measurableOffspringArray_ae_eq q P Y hY_law ni.1 ni.2).symm

/-- Helper for Example 17.20: the measurable offspring array keeps the original offspring law at
every coordinate. -/
private lemma measurableOffspringArray_hasLaw
    (q : PMF ℕ) (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ∀ n i,
      HasLaw (measurableOffspringArray q P Y hY_law n i) q.toMeasure (P : Measure Ω) := by
  intro n i
  exact (hY_law n i).congr (measurableOffspringArray_ae_eq q P Y hY_law n i)

/-- Helper for Example 17.20: coordinatewise almost-everywhere equality of offspring arrays
propagates to almost-everywhere equality of every branching generation. -/
private lemma branchingProcess_congr_ae
    (μ : Measure Ω) (x : ℕ) {Y Z : ℕ → ℕ → Ω → ℕ}
    (hYZ : ∀ n i, Y n i =ᵐ[μ] Z n i) :
    ∀ n, branchingProcess x Y n =ᵐ[μ] branchingProcess x Z n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: both branching processes start from the same deterministic population.
      simp [branchingProcess_zero]
  | succ n ih =>
      have hrow : ∀ᵐ ω ∂μ, ∀ i, Y n i ω = Z n i ω := by
        rw [ae_all_iff]
        intro i
        exact hYZ n i
      -- Proof comment: once the previous generation sizes and the whole current offspring row
      -- agree, the successor-generation sums agree pointwise.
      filter_upwards [ih, hrow] with ω hprev hrowω
      simp [branchingProcess, hprev, hrowω]

/-- Helper for Example 17.20: the offspring-law assumptions suffice to make each branching
generation almost everywhere measurable via the measurable representative array. -/
private lemma aemeasurable_branchingProcess_of_hasLaw
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ∀ n, AEMeasurable (branchingProcess x Y n) (P : Measure Ω) := by
  let Y' : ℕ → ℕ → Ω → ℕ := measurableOffspringArray q P Y hY_law
  have hY'_meas : ∀ n i, Measurable (Y' n i) := by
    intro n i
    simpa [Y'] using measurableOffspringArray_measurable q P Y hY_law n i
  intro n
  have hbranch_ae :
      branchingProcess x Y' n =ᵐ[(P : Measure Ω)] branchingProcess x Y n :=
    branchingProcess_congr_ae (P : Measure Ω) x
      (fun n i ↦ measurableOffspringArray_ae_eq q P Y hY_law n i) n
  -- Proof comment: switch from the measurable representative process back to the original one
  -- through the almost-everywhere equality of all generations.
  exact (measurable_branchingProcess x Y' hY'_meas n).aemeasurable.congr hbranch_ae

/-- Helper for Example 17.20: the singleton mass of a convolution on `ℕ` is the finite
antidiagonal sum of the singleton masses of its two factors. -/
private lemma convolutionApplySingletonEqSumAntidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      ∑ p ∈ Finset.antidiagonal n, μ ({p.1} : Set ℕ) * ν ({p.2} : Set ℕ) := by
  -- Proof comment: rewrite convolution as the pushforward of the product law along addition.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  have hsum_singleton :
      ∑ p ∈ Finset.antidiagonal n, (μ.prod ν) ({p} : Set (ℕ × ℕ)) =
        (μ.prod ν) (Finset.antidiagonal n : Set (ℕ × ℕ)) := by
    exact MeasureTheory.sum_measure_singleton
  rw [hpreimage, ← hsum_singleton]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsingleton :
      ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ ({p.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases p
    simp
  rw [hsingleton]
  exact Measure.prod_prod ({p.1} : Set ℕ) ({p.2} : Set ℕ)

/-- Helper for Example 17.20: convolving the `n`-fold offspring law with one more copy of `q`
matches the recursive PMF successor. -/
private lemma branchingOffspringPMF_toMeasure_succ (q : PMF ℕ) (n : ℕ) :
    ((q^{*n}).toMeasure ∗ q.toMeasure) = (q^{*(n + 1)}).toMeasure := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  -- Proof comment: on the discrete state space `ℕ`, it is enough to compare singleton masses.
  rw [convolutionApplySingletonEqSumAntidiagonal]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b ↦ (q^{*n}).toMeasure ({a} : Set ℕ) * q.toMeasure ({b} : Set ℕ)) k]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [branchingOffspringPMF_succ, PMF.bind_apply]
  have htsum :
      (∑' a, (q^{*n}) a * (q.map (fun l : ℕ ↦ a + l)) k) =
        ∑ a ∈ Finset.range (k + 1), (q^{*n}) a * (q.map (fun l : ℕ ↦ a + l)) k := by
    exact tsum_eq_sum fun a ha ↦ by
      have hka : k < a := by
        have hnot : ¬ a < k + 1 := by
          simpa using ha
        omega
      have hzero : (q.map (fun l : ℕ ↦ a + l)) k = 0 := by
        rw [← PMF.toMeasure_apply_singleton
          (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
        rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
        have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = ∅ := by
          ext l
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          intro h
          exact (Nat.not_le_of_gt hka) <| h ▸ Nat.le_add_right a l
        simp [hpre]
      simp [hzero]
  rw [htsum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hak : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  congr 1
  rw [← PMF.toMeasure_apply_singleton
    (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
  rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
  have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = {k - a} := by
    ext l
    simp
    omega
  rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (k - a))]

/-- Helper for Example 17.20: the finite offspring-row sum has the recursive convolution law
`q^{*m}`. -/
private lemma offspringRowSum_hasLaw
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n m : ℕ) :
    HasLaw (fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω))
      (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
  induction m with
  | zero =>
      -- Proof comment: the empty offspring sum is the constant zero random variable.
      refine HasLaw.mk aemeasurable_const ?_
      ext s hs
      simp [branchingOffspringPMF_zero, PMF.toMeasure_pure]
  | succ m ih =>
      let rowSum : Ω → ℕ := fun ω ↦ Finset.sum (Finset.range m) (fun j ↦ Y n j ω)
      have hrowSum_eq : (∑ j ∈ Finset.range m, Y n j) = rowSum := by
        funext ω
        simp [rowSum]
      let g : ℕ → ℕ × ℕ := fun i ↦ (n, i)
      have hrow_indep' :
          iIndepFun ((fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) ∘ g) (P : Measure Ω) :=
        hY_indep.precomp <| by
          intro i j hij
          simpa [g] using congrArg Prod.snd hij
      have hrow_indep : iIndepFun (fun i : ℕ ↦ Y n i) (P : Measure Ω) := by
        simpa [g] using hrow_indep'
      have hsum_indep_base :
          IndepFun (∑ j ∈ Finset.range m, Y n j) (Y n m) (P : Measure Ω) := by
        exact
          (hrow_indep.indepFun_sum_range_succ₀
            (fun i ↦ (hY_law n i).aemeasurable) m)
      have hsum_indep :
          IndepFun rowSum (Y n m) (P : Measure Ω) :=
        hsum_indep_base.congr (Filter.EventuallyEq.of_eq hrowSum_eq) Filter.EventuallyEq.rfl
      have ihRow :
          HasLaw rowSum (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
        simpa [rowSum] using ih
      have hstep :
          HasLaw (fun ω ↦ rowSum ω + Y n m ω)
            (((branchingOffspringPMF q m).toMeasure) ∗ q.toMeasure) (P : Measure Ω) :=
        hsum_indep.hasLaw_add ihRow (hY_law n m)
      -- Proof comment: append one more independent offspring variable and normalize the
      -- resulting convolution with the recursive PMF law.
      simpa [rowSum, Finset.sum_range_succ, branchingOffspringPMF_toMeasure_succ] using hstep

/-- Helper for Example 17.20: the finite history tuple of `branchingProcess x Y` up to time `n`.
-/
private def branchingHistoryTuple (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    Ω → Fin (n + 1) → ℕ :=
  fun ω i ↦ branchingProcess x Y i ω

/-- Helper for Example 17.20: each finite branching history tuple is measurable. -/
private lemma measurable_branchingHistoryTuple
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (hY_meas : ∀ n i, Measurable (Y n i)) (n : ℕ) :
    Measurable (branchingHistoryTuple x Y n) := by
  let times : Fin (n + 1) → ℕ := fun i ↦ i
  have hX : ∀ t : ℕ, Measurable (branchingProcess x Y t) := by
    intro t
    exact measurable_branchingProcess x Y hY_meas t
  -- Proof comment: the history tuple is a finite product of measurable `ℕ`-valued coordinates.
  simpa [branchingHistoryTuple, times] using
    measurable_historyTupleLocal (branchingProcess x Y) times hX

/-- Helper for Example 17.20: coordinatewise almost-everywhere equality of offspring arrays also
propagates to almost-everywhere equality of each finite branching-history tuple. -/
private lemma branchingHistoryTuple_congr_ae
    (μ : Measure Ω) (x : ℕ) {Y Z : ℕ → ℕ → Ω → ℕ}
    (hYZ : ∀ n i, Y n i =ᵐ[μ] Z n i) :
    ∀ n, branchingHistoryTuple x Y n =ᵐ[μ] branchingHistoryTuple x Z n := by
  intro n
  have hall :
      ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), branchingProcess x Y i ω = branchingProcess x Z i ω := by
    rw [ae_all_iff]
    intro i
    exact branchingProcess_congr_ae μ x hYZ i
  -- Proof comment: a finite history tuple is equal exactly when each of its finitely many
  -- branching-generation coordinates is equal.
  filter_upwards [hall] with ω hω
  funext i
  exact hω i

/-- Helper for Example 17.20: the measurable-representative argument also makes each finite
branching-history tuple almost everywhere measurable. -/
private lemma aemeasurable_branchingHistoryTuple_of_hasLaw
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) (n : ℕ) :
    AEMeasurable (branchingHistoryTuple x Y n) (P : Measure Ω) := by
  let Y' : ℕ → ℕ → Ω → ℕ := measurableOffspringArray q P Y hY_law
  have hY'_meas : ∀ n i, Measurable (Y' n i) := by
    intro m i
    simpa [Y'] using measurableOffspringArray_measurable q P Y hY_law m i
  have hhistory_ae :
      branchingHistoryTuple x Y' n =ᵐ[(P : Measure Ω)] branchingHistoryTuple x Y n :=
    branchingHistoryTuple_congr_ae (P : Measure Ω) x
      (fun m i ↦ measurableOffspringArray_ae_eq q P Y hY_law m i) n
  -- Proof comment: the finite history tuple inherits almost-everywhere measurability from the
  -- measurable representative history tuple.
  exact (measurable_branchingHistoryTuple x Y' hY'_meas n).aemeasurable.congr hhistory_ae

/-- Helper for Example 17.20: the branching transition kernel is Markov because its rows are the
PMF measures `q^{*x}`. -/
private theorem branchingTransitionKernel_isMarkov (q : PMF ℕ) :
    IsMarkovKernel (branchingTransitionKernel q) :=
  discreteMatrixKernel_isMarkovKernel (branchingTransitionMatrix q)
    (branchingTransitionMatrix_isStochasticMatrix q)

/-- Helper for Example 17.20: the sigma-algebra generated by offspring rows strictly before
generation `n`. -/
private abbrev offspringPast
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 < n},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: enlarging the cutoff generation enlarges the past-offspring
sigma-algebra. -/
private lemma offspringPast_mono {Y : ℕ → ℕ → Ω → ℕ} :
    Monotone (offspringPast Y) := by
  intro n k hnk
  refine iSup_le ?_
  intro ij
  refine iSup_le ?_
  intro hij
  exact le_iSup_of_le ij <| le_iSup_of_le (lt_of_lt_of_le hij hnk) le_rfl

end

/-- Helper for Example 17.20: the first `m` offspring coordinates of row `n` generate their own
finite prefix sigma-algebra. -/
private abbrev currentOffspringPrefixSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 = n ∧ ij.2 < m},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: every generation size is measurable with respect to the offspring
rows revealed up to that generation. -/
private lemma branchingProcess_measurable_offspringPast_self
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ n, Measurable[offspringPast Y n] (branchingProcess x Y n) := by
  intro n
  have hPastMono : Monotone (offspringPast Y) := offspringPast_mono
  induction n with
  | zero =>
      -- Proof comment: the initial population is the deterministic constant `x`.
      simp [branchingProcess_zero]
  | succ n ih =>
      have hT :
          Measurable[offspringPast Y (n + 1)] (branchingProcess x Y n) :=
        Measurable.mono ih
          (hPastMono (show n ≤ n + 1 by omega)) le_rfl
      have hX :
          ∀ i, Measurable[offspringPast Y (n + 1)] (Y n i) := by
        intro i
        refine measurable_iff_comap_le.mpr ?_
        exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
      -- Proof comment: the next generation is a measurable random sum over the fresh row.
      simpa [branchingProcess] using
        measurable_randomNatSum (branchingProcess x Y n) hT (fun i ↦ Y n i) hX

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: any earlier generation is measurable with respect to any later
past-offspring sigma-algebra. -/
private lemma branchingProcess_measurable_offspringPast
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ {k n}, k ≤ n → Measurable[offspringPast Y n] (branchingProcess x Y k) := by
  intro k n hkn
  have hPastMono : Monotone (offspringPast Y) := offspringPast_mono
  -- Proof comment: monotonicity of `offspringPast` lets us weaken the relative measurability
  -- statement from generation `k` to any later cutoff `n`.
  exact Measurable.mono
    (branchingProcess_measurable_offspringPast_self x Y k) (hPastMono hkn) le_rfl

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the history tuple up to time `n` is measurable with respect to the
offspring rows revealed before generation `n`. -/
private lemma branchingHistoryTuple_comap_le_offspringPast
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
      offspringPast Y n := by
  let _ : MeasurableSpace Ω := offspringPast Y n
  have hmeas :
      Measurable[offspringPast Y n] (branchingHistoryTuple x Y n) := by
    -- Proof comment: each coordinate of the history tuple is one earlier branching generation.
    refine measurable_pi_iff.2 fun i ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    have hcoord :
        Measurable[offspringPast Y n] (branchingProcess x Y (i : ℕ)) :=
      branchingProcess_measurable_offspringPast x Y
        (show (i : ℕ) ≤ n by exact Nat.le_of_lt_succ i.2)
    simpa [branchingHistoryTuple] using hcoord.comap_le
  simpa using hmeas.comap_le

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the finite current-row tuple is measurable with respect to the
sigma-algebra generated by its coordinates. -/
private lemma offspringRowPrefix_comap_le_currentOffspringPrefixSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) :
    MeasurableSpace.comap (offspringRowPrefix Y n m) inferInstance ≤
      currentOffspringPrefixSpace Y n m := by
  let _ : MeasurableSpace Ω := currentOffspringPrefixSpace Y n m
  have hmeas :
      Measurable[currentOffspringPrefixSpace Y n m] (offspringRowPrefix Y n m) := by
    -- Proof comment: each coordinate of the prefix tuple is one of the generators of the current
    -- row prefix sigma-algebra.
    refine measurable_pi_iff.2 fun i ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp [i.2]) le_rfl
  simpa using hmeas.comap_le

end

/-- Helper for Example 17.20: the fresh row prefix is independent of all earlier offspring rows.
-/
private lemma currentOffspringPrefixSpace_indep_offspringPast
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n m : ℕ) :
    Indep (currentOffspringPrefixSpace Y n m)
      (offspringPast Y n) (P : Measure Ω) := by
  let mY : ℕ × ℕ → MeasurableSpace Ω := fun ij ↦
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance
  have hDisjoint :
      Disjoint {ij : ℕ × ℕ | ij.1 = n ∧ ij.2 < m} {ij : ℕ × ℕ | ij.1 < n} := by
    refine Set.disjoint_left.2 ?_
    intro ij hij hpast
    exact lt_irrefl n (hij.1 ▸ hpast)
  -- Proof comment: the fresh row coordinates and the older rows are indexed by disjoint blocks
  -- of the i.i.d. offspring array.
  simpa [mY, currentOffspringPrefixSpace, offspringPast] using
    ProbabilityTheory.indep_iSup_of_disjoint
      (fun ij ↦ (hY_meas ij.1 ij.2).comap_le) hY_indep.iIndep hDisjoint

/-- Helper for Example 17.20: the current row sum over `m` parents is independent of the whole
branching history up to time `n`. -/
private lemma branchingHistoryTuple_indep_offspringRowSum
    (P : ProbabilityMeasure Ω) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n m : ℕ) :
    IndepFun (branchingHistoryTuple x Y n)
      (offspringRowSum Y n m)
      (P : Measure Ω) := by
  have hsum_meas :
      Measurable[MeasurableSpace.comap (offspringRowPrefix Y n m) inferInstance]
        (offspringRowSum Y n m) := by
    -- Proof comment: the row sum is a measurable function of the finite current-row tuple.
    exact
      (Measurable.of_discrete : Measurable (fun f : Fin m → ℕ ↦ ∑ i : Fin m, f i)).comp
      (comap_measurable (offspringRowPrefix Y n m))
  have hrow_indep :
      Indep (MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance)
        (MeasurableSpace.comap (offspringRowSum Y n m) inferInstance)
        (P : Measure Ω) := by
    have hbase :
        Indep (currentOffspringPrefixSpace Y n m)
          (offspringPast Y n) (P : Measure Ω) :=
      currentOffspringPrefixSpace_indep_offspringPast
        P Y hY_meas hY_indep n m
    have hhistory :
        MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
          offspringPast Y n :=
      branchingHistoryTuple_comap_le_offspringPast x Y n
    have hsum :
        MeasurableSpace.comap (offspringRowSum Y n m) inferInstance ≤
          currentOffspringPrefixSpace Y n m := by
      exact hsum_meas.comap_le.trans
        (offspringRowPrefix_comap_le_currentOffspringPrefixSpace Y n m)
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hbase.symm hhistory) hsum
  exact (IndepFun_iff_Indep _ _ _).2 hrow_indep

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: on a history fiber with terminal population `h (Fin.last n)`, the
next branching state is the sum of that many fresh offspring variables from row `n`. -/
private lemma branchingProcess_succ_eq_offspringRowSum_of_history
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) {n : ℕ} {h : Fin (n + 1) → ℕ} {ω : Ω}
    (hω : branchingHistoryTuple x Y n ω = h) :
    branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
  have hlast : branchingProcess x Y n ω = h (Fin.last n) := by
    -- Proof comment: the last coordinate of the history tuple records the current population.
    simpa [branchingHistoryTuple] using
      congrArg (fun g : Fin (n + 1) → ℕ ↦ g (Fin.last n)) hω
  -- Proof comment: unfold the branching recursion and rewrite the terminal population with the
  -- value fixed by the history fiber.
  calc
    branchingProcess x Y (n + 1) ω
        = ∑ i ∈ Finset.range (branchingProcess x Y n ω), Y n i ω := by
            rfl
    _ = ∑ i ∈ Finset.range (h (Fin.last n)), Y n i ω := by rw [hlast]
    _ = offspringRowSum Y n (h (Fin.last n)) ω := by
      simpa [offspringRowSum, offspringRowPrefix] using
        (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Y n i ω) (h (Fin.last n))).symm

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the finite history tuple generates exactly the time-`n`
sigma-algebra of the branching process. -/
private lemma generatedFiltrationSpace_branchingProcess_eq_historyTupleComap
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    generatedFiltrationSpace (branchingProcess x Y) n =
      MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance := by
  let times : Fin (n + 1) → ℕ := fun i ↦ i
  have htimes : StrictMono times := fun i j hij ↦ hij
  have hleft :
      MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
        generatedFiltrationSpace (branchingProcess x Y) n := by
    -- Proof comment: the full history tuple is measurable for the natural filtration because
    -- each recorded time lies at most at `n`.
    simpa [branchingHistoryTuple, times] using
      historyTuple_comap_le_generatedFiltrationSpaceLocal (branchingProcess x Y) times htimes
  have hright :
      generatedFiltrationSpace (branchingProcess x Y) n ≤
        MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance := by
    -- Proof comment: each generator `branchingProcess x Y t` with `t ≤ n` is recovered by
    -- evaluating the history tuple at the coordinate `⟨t, t < n + 1⟩`.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (n + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance]
          (fun ω ↦ branchingHistoryTuple x Y n ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (branchingHistoryTuple x Y n))
    simpa [branchingHistoryTuple, i] using hCoord.comap_le
  exact le_antisymm hright hleft

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: on a fixed history singleton, the next-state rectangle event agrees
with the corresponding fresh-row-sum rectangle event. -/
private lemma branchingHistoryTuple_nextPairPreimage_eq_rowSumPairPreimage
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) {n : ℕ} (h : Fin (n + 1) → ℕ) (y : ℕ) :
    (fun ω ↦ (branchingHistoryTuple x Y n ω, branchingProcess x Y (n + 1) ω)) ⁻¹'
        ({h} ×ˢ ({y} : Set ℕ)) =
      (fun ω ↦
        (branchingHistoryTuple x Y n ω,
          offspringRowSum Y n (h (Fin.last n)) ω)) ⁻¹'
        ({h} ×ˢ ({y} : Set ℕ)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hHω, hnextω⟩
    have hrow :
        branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
      -- Proof comment: on the history fiber `branchingHistoryTuple x Y n = h`, the recursive
      -- next state is exactly the row sum indexed by the terminal population `h (Fin.last n)`.
      simpa using
        branchingProcess_succ_eq_offspringRowSum_of_history x Y hHω
    exact ⟨hHω, hrow ▸ hnextω⟩
  · rintro ⟨hHω, hrowω⟩
    have hrow :
        branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
      -- Proof comment: the same history-fiber identification converts the row-sum event back to
      -- the actual next-generation event.
      simpa using
        branchingProcess_succ_eq_offspringRowSum_of_history x Y hHω
    exact ⟨hHω, hrow.symm ▸ hrowω⟩

end

/-- Helper for Example 17.20: the joint law of the history tuple and the fresh row sum factors on
singleton rectangles into the history mass times the offspring transition row. -/
private lemma branchingHistoryTuple_rowSumPairMap_singleton
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) (h : Fin (n + 1) → ℕ) (y : ℕ) :
    (P : Measure Ω).map
        (fun ω ↦
          (branchingHistoryTuple x Y n ω,
            ∑ i : Fin (h (Fin.last n)), offspringRowPrefix Y n (h (Fin.last n)) ω i))
        ({h} ×ˢ ({y} : Set ℕ)) =
      (P : Measure Ω).map (branchingHistoryTuple x Y n) {h} *
        branchingTransitionKernel q (h (Fin.last n)) ({y} : Set ℕ) := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let m : ℕ := h (Fin.last n)
  let U : Ω → ℕ := offspringRowSum Y n m
  have hH_meas : Measurable H := by
    simpa [H] using measurable_branchingHistoryTuple x Y hY_meas n
  have hU_meas : Measurable U := by
    -- Proof comment: the row sum is a measurable function of the measurable finite row prefix.
    have hprefix_meas : Measurable (offspringRowPrefix Y n m) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact hY_meas n i
    exact
      (measurable_of_countable (fun f : Fin m → ℕ ↦ ∑ i : Fin m, f i)).comp hprefix_meas
  have hU_eq :
      U = fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω) := by
    funext ω
    simpa [U, offspringRowSum, offspringRowPrefix] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Y n i ω) m)
  have hU_law_range :
      HasLaw (fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω))
        (branchingOffspringPMF q m).toMeasure μ :=
    offspringRowSum_hasLaw P q Y hY_indep hY_law n m
  have hU_law : HasLaw U (branchingOffspringPMF q m).toMeasure μ :=
    hU_law_range.congr (Filter.EventuallyEq.of_eq hU_eq)
  have hHU_indep : IndepFun H U μ :=
    branchingHistoryTuple_indep_offspringRowSum P x Y hY_meas hY_indep n m
  have hmap_prod :
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (μ.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH_meas.aemeasurable hU_meas.aemeasurable).mp hHU_indep
  -- Proof comment: independence factors the joint law into the product of the history law and the
  -- fresh-row-sum law, and that row-sum law is the `m`-fold offspring convolution.
  calc
    μ.map (fun ω ↦ (H ω, U ω)) ({h} ×ˢ ({y} : Set ℕ))
        = ((μ.map H).prod (μ.map U)) ({h} ×ˢ ({y} : Set ℕ)) := by
            rw [hmap_prod]
    _ = μ.map H {h} * μ.map U ({y} : Set ℕ) := by
          rw [Measure.prod_prod]
    _ = μ.map H {h} * branchingTransitionKernel q m ({y} : Set ℕ) := by
          rw [hU_law.map_eq, ← branchingTransitionKernel_apply q m]

/-- Helper for Example 17.20: conditioning the next branching state on a non-null history fiber
returns the transition kernel row determined by the last observed population. -/
private lemma branchingHistoryTuple_nextPairMap_eq_compProd
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) :
    let μ : Measure Ω := (P : Measure Ω)
    let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
    let next : Ω → ℕ := branchingProcess x Y (n + 1)
    let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
      Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
        (by fun_prop)
    μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ κ := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let next : Ω → ℕ := branchingProcess x Y (n + 1)
  let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
    Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
      (by fun_prop)
  have hH_meas : Measurable H := by
    simpa [H] using measurable_branchingHistoryTuple x Y hY_meas n
  have hnext_meas : Measurable next := by
    simpa [next] using measurable_branchingProcess x Y hY_meas (n + 1)
  have hκ_apply :
      ∀ h : Fin (n + 1) → ℕ, κ h = branchingTransitionKernel q (h (Fin.last n)) := by
    intro h
    simp [κ]
  let _ : IsMarkovKernel (branchingTransitionKernel q) := branchingTransitionKernel_isMarkov q
  let _ : IsFiniteKernel κ := by infer_instance
  refine Measure.ext_of_singleton fun z ↦ ?_
  rcases z with ⟨h, y⟩
  let row : Ω → ℕ := offspringRowSum Y n (h (Fin.last n))
  have hsingleton :
      ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ)) = {h} ×ˢ ({y} : Set ℕ) := by
    ext z
    rcases z with ⟨h', y'⟩
    simp
  have hpairNext_meas : Measurable (fun ω ↦ (H ω, next ω)) := hH_meas.prodMk hnext_meas
  have hpairRow_meas :
      Measurable
        (fun ω ↦ (H ω, row ω)) := by
    have hrow_meas : Measurable row := by
      -- Proof comment: `row` is the measurable row sum for the fixed terminal population `h`.
      simpa [row] using
        ((measurable_of_countable (fun f : Fin (h (Fin.last n)) → ℕ ↦
            ∑ i : Fin (h (Fin.last n)), f i)).comp
          (measurable_pi_lambda _ fun i ↦ hY_meas n i))
    exact hH_meas.prodMk hrow_meas
  have hprod_meas : MeasurableSet ({h} ×ˢ ({y} : Set ℕ)) :=
    (measurableSet_singleton h).prod (measurableSet_singleton y)
  -- Proof comment: compare the joint law on singleton rectangles and then recognize the
  -- resulting factorization as the defining `compProd` law for the conditional kernel.
  calc
    μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ))
        = μ.map (fun ω ↦ (H ω, next ω)) ({h} ×ˢ ({y} : Set ℕ)) := by
            rw [hsingleton]
    _ = μ.map (fun ω ↦ (H ω, row ω)) ({h} ×ˢ ({y} : Set ℕ)) := by
          rw [Measure.map_apply hpairNext_meas hprod_meas]
          rw [Measure.map_apply hpairRow_meas hprod_meas]
          exact congrArg μ <|
            branchingHistoryTuple_nextPairPreimage_eq_rowSumPairPreimage
              x Y h y
    _ = μ.map H {h} * branchingTransitionKernel q (h (Fin.last n)) ({y} : Set ℕ) := by
          exact branchingHistoryTuple_rowSumPairMap_singleton
            P q x Y hY_meas hY_indep hY_law n h y
    _ = (μ.map H ⊗ₘ κ) ({h} ×ˢ ({y} : Set ℕ)) := by
          rw [Measure.compProd_apply_prod (measurableSet_singleton h) (measurableSet_singleton y)]
          simp [hκ_apply h]
    _ = (μ.map H ⊗ₘ κ) ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ)) := by
          rw [hsingleton]

/-- Helper for Example 17.20: conditioning the next branching state on a non-null history fiber
returns the transition kernel row determined by the last observed population. -/
private lemma branchingProcess_condDistrib_historyTuple_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) :
    condDistrib (branchingProcess x Y (n + 1)) (branchingHistoryTuple x Y n)
        (P : Measure Ω) =ᵐ[(P : Measure Ω).map (branchingHistoryTuple x Y n)]
      fun h ↦ branchingTransitionKernel q (h (Fin.last n)) := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let next : Ω → ℕ := branchingProcess x Y (n + 1)
  let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
    Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
      (by fun_prop)
  have hH_meas : Measurable H := by
    simpa [H] using measurable_branchingHistoryTuple x Y hY_meas n
  have hnext_meas : Measurable next := by
    simpa [next] using measurable_branchingProcess x Y hY_meas (n + 1)
  have hκ_apply :
      ∀ h : Fin (n + 1) → ℕ, κ h = branchingTransitionKernel q (h (Fin.last n)) := by
    intro h
    simp [κ]
  let _ : IsMarkovKernel (branchingTransitionKernel q) := branchingTransitionKernel_isMarkov q
  let _ : IsFiniteKernel κ := by infer_instance
  have hpair :
      μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ κ := by
    simpa [μ, H, next, κ] using
      branchingHistoryTuple_nextPairMap_eq_compProd P q x Y hY_meas hY_indep hY_law n
  have hcond : condDistrib next H μ =ᵐ[μ.map H] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd H hnext_meas.aemeasurable hpair
  exact hcond.trans <| Filter.Eventually.of_forall hκ_apply

/-- Helper for Example 17.20: the one-step conditional law formula follows directly once the
offspring array is globally measurable. -/
private theorem branchingProcess_one_step_conditionalProb_eq_transitionKernel_ofMeasurable
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' A | generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (branchingProcess x Y n ω)).real A := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  have hH_meas : Measurable H := by
    simpa [H] using measurable_branchingHistoryTuple x Y hY_meas n
  have hnext_meas : Measurable (branchingProcess x Y (n + 1)) := by
    simpa using measurable_branchingProcess x Y hY_meas (n + 1)
  have hcond :
      condDistrib (branchingProcess x Y (n + 1)) H μ =ᵐ[μ.map H]
        fun h ↦ branchingTransitionKernel q (h (Fin.last n)) :=
    branchingProcess_condDistrib_historyTuple_eq_transitionKernel
      P q x Y hY_meas hY_indep hY_law n
  have hcondexp :
      μ⟦(branchingProcess x Y (n + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib (branchingProcess x Y (n + 1)) H μ (H ω)).real A := by
    -- Route correction: use the measurable `condDistrib_ae_eq_condExp` API directly instead of
    -- descending conditional probability across AE-equal measurable representatives.
    -- Proof comment: identify the conditional probability with the conditional-distribution
    -- kernel evaluated at the observed history tuple.
    simpa using
      (condDistrib_ae_eq_condExp hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ω ↦ (condDistrib (branchingProcess x Y (n + 1)) H μ (H ω)).real A) =ᵐ[μ]
        fun ω ↦ (branchingTransitionKernel q (branchingProcess x Y n ω)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ω hω
    simpa [Function.comp] using congrArg (fun ν' : Measure ℕ ↦ ν'.real A) hω
  -- Proof comment: replace the generated history filtration by the history-tuple sigma-algebra.
  rw [generatedFiltrationSpace_branchingProcess_eq_historyTupleComap x Y n]
  exact hcondexp.trans hcond_comp

/-- Helper for Example 17.20: the standard `condDistrib`-to-conditional-probability identity is
available once both maps are genuinely measurable. -/
private lemma condDistribReal_ae_eq_conditionalProbability_ofMeasurable
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) {A : Set T} (hA : MeasurableSet A) :
    (fun ω ↦ (condDistrib Y X μ (X ω)).real A) =ᵐ[μ]
      μ⟦Y ⁻¹' A | MeasurableSpace.comap X inferInstance⟧ := by
  -- Proof comment: this is exactly the measurable-owner `condDistrib_ae_eq_condExp`.
  simpa using
    (condDistrib_ae_eq_condExp (μ := μ) (X := X) (Y := Y) hX hY hA)

/-- Helper for Example 17.20: move the deterministic initial population into the sample space so
Theorem 17.11 can be applied to one process family. -/
private def productStartBranchingProcess (Y : ℕ → ℕ → Ω → ℕ) :
    ℕ → (ℕ × Ω) → ℕ :=
  fun n s ↦ branchingProcess s.1 (fun k i t ↦ Y k i t.2) n s

/-- Helper for Example 17.20: the auxiliary product-start law fixes the first coordinate at `x`
and keeps the offspring randomness in the second coordinate. -/
private def productStartBranchingProcessMeasure (P : ProbabilityMeasure Ω) (x : ℕ) :
    ProbabilityMeasure (ℕ × Ω) :=
  ⟨(Measure.dirac x).prod (P : Measure Ω), inferInstance⟩

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the auxiliary branching process started under `δ_x ⊗ P` reduces to
the original fixed-start branching process after composing with `ω ↦ (x, ω)`. -/
private lemma productStartBranchingProcess_comp_prodMk
    (Y : ℕ → ℕ → Ω → ℕ) (x n : ℕ) :
    productStartBranchingProcess Y n ∘ (fun ω ↦ (x, ω)) =
      branchingProcess x Y n := by
  -- Proof comment: evaluating the auxiliary process at `(x, ω)` removes the sample-space start
  -- coordinate and leaves the original branching recursion.
  induction n with
  | zero =>
      funext ω
      simp [productStartBranchingProcess, branchingProcess_zero]
  | succ n ih =>
      funext ω
      change
        ∑ i ∈ Finset.range (branchingProcess x (fun k j t ↦ Y k j t.2) n (x, ω)), Y n i ω =
          ∑ i ∈ Finset.range (branchingProcess x Y n ω), Y n i ω
      rw [show branchingProcess x (fun k j t ↦ Y k j t.2) n (x, ω) = branchingProcess x Y n ω by
        simpa [productStartBranchingProcess] using congrFun ih ω]

end

/-- Helper for Example 17.20: the finite history tuple of the auxiliary product-start process. -/
private def productStartBranchingProcessHistoryTuple (Y : ℕ → ℕ → Ω → ℕ) (s : ℕ) :
    (ℕ × Ω) → Fin (s + 1) → ℕ :=
  fun ω i ↦ productStartBranchingProcess Y i ω

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: composing the auxiliary history tuple with the fixed-start embedding
recovers the original branching history tuple. -/
private lemma productStartBranchingProcessHistoryTuple_comp_prodMk
    (Y : ℕ → ℕ → Ω → ℕ) (x s : ℕ) :
    productStartBranchingProcessHistoryTuple Y s ∘ (fun ω ↦ (x, ω)) =
      branchingHistoryTuple x Y s := by
  -- Proof comment: every auxiliary history coordinate collapses to the corresponding
  -- fixed-start branching coordinate.
  funext ω
  funext i
  simpa [productStartBranchingProcessHistoryTuple, branchingHistoryTuple] using
    congrFun (productStartBranchingProcess_comp_prodMk Y x i) ω

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: at time `0` the auxiliary product-start process is just the first
projection. -/
private theorem productStartBranchingProcess_zero
    (Y : ℕ → ℕ → Ω → ℕ) :
    productStartBranchingProcess Y 0 = fun s ↦ s.1 := by
  -- Proof comment: before any offspring are sampled, the state is exactly the initial
  -- population stored in the first coordinate.
  funext s
  simp [productStartBranchingProcess, branchingProcess_zero]

end

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the auxiliary process satisfies the same branching recursion on the
product space. -/
private lemma productStartBranchingProcess_succ
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    productStartBranchingProcess Y (n + 1) =
      fun s ↦ ∑ i ∈ Finset.range (productStartBranchingProcess Y n s), Y n i s.2 := by
  -- Proof comment: unfold the product-start process once and rewrite the recursive branch size.
  funext s
  simp [productStartBranchingProcess, branchingProcess]

end

/-- Helper for Example 17.20: measurable offspring coordinates yield measurable auxiliary
product-start coordinates. -/
private lemma measurable_productStartBranchingProcess
    (Y : ℕ → ℕ → Ω → ℕ) (hY_meas : ∀ n i, Measurable (Y n i)) :
    ∀ n : ℕ, Measurable (productStartBranchingProcess Y n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: time zero is the measurable first projection.
      simpa [productStartBranchingProcess_zero] using measurable_fst
  | succ n ih =>
      -- Proof comment: the next auxiliary generation is a measurable random sum of the fresh row
      -- over the measurable current population.
      rw [productStartBranchingProcess_succ]
      exact measurable_natRandomSum
        (productStartBranchingProcess Y n) ih
        (fun i ↦ fun s ↦ Y n i s.2)
        (fun i ↦ (hY_meas n i).comp measurable_snd)

/-- Helper for Example 17.20: each auxiliary history tuple is measurable. -/
private lemma measurable_productStartBranchingProcessHistoryTuple
    (Y : ℕ → ℕ → Ω → ℕ) (hY_meas : ∀ n i, Measurable (Y n i)) (s : ℕ) :
    Measurable (productStartBranchingProcessHistoryTuple Y s) := by
  let times : Fin (s + 1) → ℕ := fun i ↦ i
  -- Proof comment: the auxiliary history tuple is a finite product of measurable coordinates.
  simpa [productStartBranchingProcessHistoryTuple, times] using
    measurable_historyTupleLocal (productStartBranchingProcess Y) times
      (measurable_productStartBranchingProcess Y hY_meas)

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: the natural filtration of the auxiliary product-start process is
generated by its finite history tuple. -/
private lemma generatedFiltrationSpace_productStartBranchingProcess_eq_historyTupleComap
    (Y : ℕ → ℕ → Ω → ℕ) (s : ℕ) :
    generatedFiltrationSpace (productStartBranchingProcess Y) s =
      MeasurableSpace.comap (productStartBranchingProcessHistoryTuple Y s) inferInstance := by
  let times : Fin (s + 1) → ℕ := fun i ↦ i
  have htimes : StrictMono times := fun i j hij ↦ hij
  have hleft :
      MeasurableSpace.comap (productStartBranchingProcessHistoryTuple Y s) inferInstance ≤
        generatedFiltrationSpace (productStartBranchingProcess Y) s := by
    -- Proof comment: the whole auxiliary history tuple is measurable for the natural filtration
    -- because all sampled times are at most `s`.
    simpa [productStartBranchingProcessHistoryTuple, times] using
      historyTuple_comap_le_generatedFiltrationSpaceLocal
        (productStartBranchingProcess Y) times htimes
  have hright :
      generatedFiltrationSpace (productStartBranchingProcess Y) s ≤
        MeasurableSpace.comap (productStartBranchingProcessHistoryTuple Y s) inferInstance := by
    -- Proof comment: each generator at time `t ≤ s` is recovered by evaluating the history tuple
    -- at the corresponding coordinate.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (s + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (productStartBranchingProcessHistoryTuple Y s) inferInstance]
          (fun ω ↦ productStartBranchingProcessHistoryTuple Y s ω i) := by
      exact (measurable_pi_apply i).comp
        (comap_measurable (productStartBranchingProcessHistoryTuple Y s))
    simpa [productStartBranchingProcessHistoryTuple, i] using hCoord.comap_le
  exact le_antisymm hright hleft

end

/-- Helper for Example 17.20: under `δ_x ⊗ P`, the auxiliary process starts from the deterministic
population `x`. -/
private lemma productStartBranchingProcess_initial
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ) (x : ℕ) :
    (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)).map
        (productStartBranchingProcess Y 0) = Measure.dirac x := by
  -- Proof comment: time zero is `Prod.fst`, so the first marginal of `δ_x ⊗ P` is `δ_x`.
  rw [productStartBranchingProcess_zero]
  simp [productStartBranchingProcessMeasure]

/-- Helper for Example 17.20: pulling a conditional probability back along the fixed-start
embedding `ω ↦ (x, ω)` reduces conditioning over a `comap` sigma-algebra on the auxiliary
product space to the corresponding conditional probability on the original space. -/
private lemma fixedStartConditionalProb_comap_transport
    (P : ProbabilityMeasure Ω) (x : ℕ) {S : Type*} [MeasurableSpace S]
    (H : (ℕ × Ω) → S) (X : (ℕ × Ω) → ℕ)
    (hH_meas : Measurable H) (hX_meas : Measurable X)
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) :
    (fun ω ↦
      ((productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))⟦X ⁻¹' A |
        MeasurableSpace.comap H inferInstance⟧) (x, ω)) =ᵐ[(P : Measure Ω)]
      (P : Measure Ω)⟦(X ∘ fun ω ↦ (x, ω)) ⁻¹' A |
        MeasurableSpace.comap (H ∘ fun ω ↦ (x, ω)) inferInstance⟧ := by
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let f : Ω → ℕ × Ω := fun ω ↦ (x, ω)
  have hμ_map : μ = (P : Measure Ω).map f := by
    -- Proof comment: `δ_x ⊗ P` is exactly the pushforward of `P` by the fixed-start embedding.
    change ((Measure.dirac x).prod (P : Measure Ω)) = (P : Measure Ω).map f
    rw [Measure.dirac_prod]
  have hmap :
      condDistrib X H μ =ᵐ[(P : Measure Ω).map (H ∘ f)]
        condDistrib (X ∘ f) (H ∘ f) (P : Measure Ω) := by
    simpa [μ, f, hμ_map] using
      (condDistrib_map hH_meas.aemeasurable hX_meas.aemeasurable
        measurable_prodMk_left.aemeasurable)
  have haux :
      (fun ω ↦ (μ⟦X ⁻¹' A | MeasurableSpace.comap H inferInstance⟧) (f ω)) =ᵐ[(P : Measure Ω)]
        fun ω ↦ (condDistrib X H μ (H (f ω))).real A := by
    have hcondexp :
        μ⟦X ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
          fun s ↦ (condDistrib X H μ (H s)).real A := by
      -- Proof comment: rewrite the conditional probability on the product space through the
      -- conditional-distribution kernel attached to `H`.
      simpa using
        (condDistrib_ae_eq_condExp hH_meas hX_meas hA).symm
    have hcondexp' :
        μ⟦X ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[(P : Measure Ω).map f]
          fun s ↦ (condDistrib X H μ (H s)).real A := by
      simpa [hμ_map] using hcondexp
    simpa [f, Function.comp] using ae_eq_comp measurable_prodMk_left.aemeasurable hcondexp'
  have hcomp :
      (fun ω ↦ (condDistrib X H μ (H (f ω))).real A) =ᵐ[(P : Measure Ω)]
        fun ω ↦ (condDistrib (X ∘ f) (H ∘ f) (P : Measure Ω) ((H ∘ f) ω)).real A := by
    -- Proof comment: compose the transported conditional-distribution identity with the fixed
    -- start map and evaluate both kernels at the pulled-back history point.
    filter_upwards [ae_eq_comp (hH_meas.comp measurable_prodMk_left).aemeasurable hmap] with ω hω
    simpa [f, Function.comp] using congrArg (fun ν : Measure ℕ ↦ ν.real A) hω
  have hsource :
      (P : Measure Ω)⟦(X ∘ f) ⁻¹' A | MeasurableSpace.comap (H ∘ f) inferInstance⟧ =ᵐ[
        (P : Measure Ω)]
        fun ω ↦ (condDistrib (X ∘ f) (H ∘ f) (P : Measure Ω) ((H ∘ f) ω)).real A := by
    -- Proof comment: identify the pulled-back conditional probability on `Ω` with the
    -- corresponding conditional-distribution kernel.
    simpa using
      (condDistrib_ae_eq_condExp
        (hH_meas.comp measurable_prodMk_left)
        (hX_meas.comp measurable_prodMk_left) hA).symm
  exact haux.trans <| hcomp.trans hsource.symm

/-- Helper for Example 17.20: the raw `condDistrib_map` transport step along the fixed-start
embedding `ω ↦ (x, ω)`. -/
private lemma productStartBranchingProcessCondDistribMap
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i)) (x s : ℕ) :
    condDistrib
        (productStartBranchingProcess Y (s + 1))
        (productStartBranchingProcessHistoryTuple Y s)
        (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)) =ᵐ[
          (P : Measure Ω).map
            ((productStartBranchingProcessHistoryTuple Y s) ∘ fun ω ↦ (x, ω))]
      condDistrib
        ((productStartBranchingProcess Y (s + 1)) ∘ fun ω ↦ (x, ω))
        ((productStartBranchingProcessHistoryTuple Y s) ∘ fun ω ↦ (x, ω))
        (P : Measure Ω) := by
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let H : (ℕ × Ω) → Fin (s + 1) → ℕ := productStartBranchingProcessHistoryTuple Y s
  let next : (ℕ × Ω) → ℕ := productStartBranchingProcess Y (s + 1)
  let f : Ω → ℕ × Ω := fun ω ↦ (x, ω)
  have hμ_map : μ = (P : Measure Ω).map f := by
    -- Proof comment: `δ_x ⊗ P` is the pushforward of `P` by the fixed-start embedding.
    change ((Measure.dirac x).prod (P : Measure Ω)) = (P : Measure Ω).map f
    rw [Measure.dirac_prod]
  have hH_meas : Measurable H := by
    simpa [H] using measurable_productStartBranchingProcessHistoryTuple Y hY_meas s
  have hnext_meas : Measurable next := by
    simpa [next] using measurable_productStartBranchingProcess Y hY_meas (s + 1)
  have hmap' :
      condDistrib next H μ =ᵐ[(P : Measure Ω).map (H ∘ f)]
        condDistrib (next ∘ f) (H ∘ f) (P : Measure Ω) := by
    simpa [hμ_map] using
      (condDistrib_map hH_meas.aemeasurable hnext_meas.aemeasurable
        measurable_prodMk_left.aemeasurable)
  simpa [μ, H, next] using hmap'

/-- Helper for Example 17.20: after fixing the deterministic start `x`, the auxiliary-history
conditional distribution becomes the original branching-history conditional distribution. -/
private lemma productStartBranchingProcessCondDistribTransport
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i)) (x s : ℕ) :
    condDistrib
        (productStartBranchingProcess Y (s + 1))
        (productStartBranchingProcessHistoryTuple Y s)
        (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)) =ᵐ[
          (P : Measure Ω).map (branchingHistoryTuple x Y s)]
      condDistrib
        (branchingProcess x Y (s + 1))
        (branchingHistoryTuple x Y s) (P : Measure Ω) := by
  have hmap := productStartBranchingProcessCondDistribMap P Y hY_meas x s
  have hH_comp :
      (productStartBranchingProcessHistoryTuple Y s) ∘ (fun ω ↦ (x, ω)) =
        branchingHistoryTuple x Y s := by
    simpa using productStartBranchingProcessHistoryTuple_comp_prodMk Y x s
  have hnext_comp :
      (productStartBranchingProcess Y (s + 1)) ∘ (fun ω ↦ (x, ω)) =
        branchingProcess x Y (s + 1) := by
    simpa using productStartBranchingProcess_comp_prodMk Y x (s + 1)
  -- Proof comment: the fixed-start embedding rewrites both the auxiliary next state and its
  -- auxiliary history tuple to the original branching objects.
  simpa [hH_comp, hnext_comp] using hmap

/-- Helper for Example 17.20: the auxiliary-history pushforward under `δ_x ⊗ P` agrees with the
fixed-start branching-history pushforward under `P`. -/
private lemma productStartBranchingProcessHistoryTuple_map_eq_branchingHistoryTuple_map
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i)) (x s : ℕ) :
    (P : Measure Ω).map (branchingHistoryTuple x Y s) =
      (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)).map
        (productStartBranchingProcessHistoryTuple Y s) := by
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let H : (ℕ × Ω) → Fin (s + 1) → ℕ := productStartBranchingProcessHistoryTuple Y s
  let f : Ω → ℕ × Ω := fun ω ↦ (x, ω)
  have hμ_map : μ = (P : Measure Ω).map f := by
    -- Proof comment: the auxiliary start law is the fixed-start pushforward of `P`.
    change ((Measure.dirac x).prod (P : Measure Ω)) = (P : Measure Ω).map f
    rw [Measure.dirac_prod]
  have hH_meas : Measurable H := by
    simpa [H] using measurable_productStartBranchingProcessHistoryTuple Y hY_meas s
  have hH_comp : H ∘ f = branchingHistoryTuple x Y s := by
    simpa [H, f] using productStartBranchingProcessHistoryTuple_comp_prodMk Y x s
  calc
    (P : Measure Ω).map (branchingHistoryTuple x Y s)
      = (P : Measure Ω).map (H ∘ f) := by rw [← hH_comp]
    _ = ((P : Measure Ω).map f).map H := by
          symm
          rw [Measure.map_map]
          · exact hH_meas
          · exact measurable_prodMk_left
    _ = μ.map H := by rw [hμ_map]
    _ = (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)).map
          (productStartBranchingProcessHistoryTuple Y s) := by
            simp [μ, H]

/-- Helper for Example 17.20: the auxiliary-history conditional distribution is the branching
transition kernel evaluated at the last observed population. -/
private lemma productStartBranchingProcess_condDistrib_historyTuple_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (x s : ℕ) :
    condDistrib
        (productStartBranchingProcess Y (s + 1))
        (productStartBranchingProcessHistoryTuple Y s)
        (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)) =ᵐ[
          (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)).map
            (productStartBranchingProcessHistoryTuple Y s)]
      fun h ↦ branchingTransitionKernel q (h (Fin.last s)) := by
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let H : (ℕ × Ω) → Fin (s + 1) → ℕ := productStartBranchingProcessHistoryTuple Y s
  have htransport :
      condDistrib
          (productStartBranchingProcess Y (s + 1))
          (productStartBranchingProcessHistoryTuple Y s)
          (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)) =ᵐ[
            (P : Measure Ω).map (branchingHistoryTuple x Y s)]
        condDistrib
          (branchingProcess x Y (s + 1))
          (branchingHistoryTuple x Y s) (P : Measure Ω) :=
    productStartBranchingProcessCondDistribTransport P Y hY_meas x s
  have hsource :
      condDistrib
          (branchingProcess x Y (s + 1))
          (branchingHistoryTuple x Y s) (P : Measure Ω) =ᵐ[
            (P : Measure Ω).map (branchingHistoryTuple x Y s)]
        fun h ↦ branchingTransitionKernel q (h (Fin.last s)) :=
    branchingProcess_condDistrib_historyTuple_eq_transitionKernel
      P q x Y hY_meas hY_indep hY_law s
  have hcond_aux :
      condDistrib
          (productStartBranchingProcess Y (s + 1))
          (productStartBranchingProcessHistoryTuple Y s)
          (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω)) =ᵐ[
            (P : Measure Ω).map (branchingHistoryTuple x Y s)]
        fun h ↦ branchingTransitionKernel q (h (Fin.last s)) :=
    htransport.trans hsource
  have hfilter :
      (P : Measure Ω).map (branchingHistoryTuple x Y s) = μ.map H :=
    productStartBranchingProcessHistoryTuple_map_eq_branchingHistoryTuple_map
      P Y hY_meas x s
  simpa [μ, H, hfilter] using hcond_aux

/-- Helper for Example 17.20: the auxiliary product-start process satisfies the required one-step
kernel identity under `δ_x ⊗ P`. -/
private theorem productStartBranchingProcess_oneStepConditionalProb_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    ∀ x : ℕ, ∀ ⦃A : Set ℕ⦄, MeasurableSet A → ∀ s : ℕ,
      (productStartBranchingProcessMeasure P x)⟦
          (productStartBranchingProcess Y (s + 1)) ⁻¹' A |
            generatedFiltrationSpace (productStartBranchingProcess Y) s⟧
        =ᵐ[(productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))]
          fun ω ↦
            (branchingTransitionKernel q (productStartBranchingProcess Y s ω)).real A := by
  intro x A hA s
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let H : (ℕ × Ω) → Fin (s + 1) → ℕ := productStartBranchingProcessHistoryTuple Y s
  let next : (ℕ × Ω) → ℕ := productStartBranchingProcess Y (s + 1)
  have hH_meas : Measurable H := by
    simpa [H] using measurable_productStartBranchingProcessHistoryTuple Y hY_meas s
  have hnext_meas : Measurable next := by
    simpa [next] using measurable_productStartBranchingProcess Y hY_meas (s + 1)
  have hcond :
      condDistrib next H μ =ᵐ[μ.map H]
        fun h ↦ branchingTransitionKernel q (h (Fin.last s)) := by
    -- Proof comment: reuse the auxiliary-history conditional-distribution bridge established
    -- above instead of redoing the transport inline.
    simpa [μ, H] using
      productStartBranchingProcess_condDistrib_historyTuple_eq_transitionKernel
        P q Y hY_meas hY_indep hY_law x s
  have hcondexp :
      μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib next H μ (H ω)).real A := by
    -- Proof comment: identify the conditional probability with the conditional-distribution
    -- kernel evaluated at the observed auxiliary history tuple.
    simpa using
      (condDistrib_ae_eq_condExp hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ω ↦ (condDistrib next H μ (H ω)).real A) =ᵐ[μ]
        fun ω ↦ (branchingTransitionKernel q (productStartBranchingProcess Y s ω)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ω hω
    simpa [H, productStartBranchingProcessHistoryTuple] using
      congrArg (fun ν : Measure ℕ ↦ ν.real A) hω
  rw [generatedFiltrationSpace_productStartBranchingProcess_eq_historyTupleComap Y s]
  exact hcondexp.trans hcond_comp

/-- Helper for Example 17.20: the auxiliary product-start process is an owner-level Markov
realization of the powers of the branching transition kernel. -/
private theorem productStartBranchingProcess_isMarkovProcessRealization
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ branchingTransitionKernel q ^ n)
      (productStartBranchingProcessMeasure P) (productStartBranchingProcess Y) := by
  let _ : IsMarkovKernel (branchingTransitionKernel q) := branchingTransitionKernel_isMarkov q
  -- Proof comment: Theorem 17.11 packages the auxiliary process once the deterministic start law
  -- and one-step conditional law have both been established.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (branchingTransitionKernel q)
    (productStartBranchingProcessMeasure P)
    (productStartBranchingProcess Y)
    (measurable_productStartBranchingProcess Y hY_meas)
    ?_
    ?_
  · intro x
    exact productStartBranchingProcess_initial P Y x
  · intro x A hA s
    exact productStartBranchingProcess_oneStepConditionalProb_eq_transitionKernel
      P q Y hY_meas hY_indep hY_law x hA s

/-- Helper for Example 17.20: once the offspring array is measurable, the branching process has
the natural Markov property. -/
private theorem branchingProcess_hasNaturalMarkovProperty_ofMeasurable
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    HasNaturalMarkovProperty (P : Measure Ω) (branchingProcess x Y) := by
  let μ : Measure (ℕ × Ω) := (productStartBranchingProcessMeasure P x : Measure (ℕ × Ω))
  let f : Ω → ℕ × Ω := fun ω ↦ (x, ω)
  have hreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ branchingTransitionKernel q ^ n)
        (productStartBranchingProcessMeasure P) (productStartBranchingProcess Y) :=
    productStartBranchingProcess_isMarkovProcessRealization P q Y hY_meas hY_indep hY_law
  refine ⟨measurable_branchingProcess x Y hY_meas, ?_⟩
  intro s u hsu A hA
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hsu
  have hμ_map : μ = (P : Measure Ω).map f := by
    -- Proof comment: the auxiliary product-start law is the pushforward of `P` by `ω ↦ (x, ω)`.
    change ((Measure.dirac x).prod (P : Measure Ω)) = (P : Measure Ω).map f
    rw [Measure.dirac_prod]
  let future : (ℕ × Ω) → ℕ := productStartBranchingProcess Y (s + t)
  let history : (ℕ × Ω) → Fin (s + 1) → ℕ := productStartBranchingProcessHistoryTuple Y s
  let present : (ℕ × Ω) → ℕ := productStartBranchingProcess Y s
  let g : (ℕ × Ω) → ℝ := fun ω ↦ ((branchingTransitionKernel q ^ t) (present ω)).real A
  have hsmall_le :
      MeasurableSpace.comap present (show MeasurableSpace ℕ from inferInstance) ≤
        MeasurableSpace.comap history
          (show MeasurableSpace (Fin (s + 1) → ℕ) from inferInstance) := by
    rw [← generatedFiltrationSpace_productStartBranchingProcess_eq_historyTupleComap Y s]
    change
      MeasurableSpace.comap (productStartBranchingProcess Y s)
          (show MeasurableSpace ℕ from inferInstance) ≤
        generatedFiltrationSpace (productStartBranchingProcess Y) s
    exact present_le_generatedFiltrationSpace (productStartBranchingProcess Y) s
  have hlarge_le :
      MeasurableSpace.comap history
          (show MeasurableSpace (Fin (s + 1) → ℕ) from inferInstance) ≤
        (show MeasurableSpace (ℕ × Ω) from inferInstance) := by
    rw [← generatedFiltrationSpace_productStartBranchingProcess_eq_historyTupleComap Y s]
    exact
      generatedFiltrationSpace_le_ambient
        (productStartBranchingProcess Y)
        (measurable_productStartBranchingProcess Y hY_meas) s
  have hg :
      AEStronglyMeasurable[MeasurableSpace.comap present inferInstance] g μ := by
    -- Proof comment: the auxiliary candidate depends only on the present state, so it is already
    -- measurable for the smaller present-state sigma-algebra.
    exact
      (((Kernel.measurable_coe (branchingTransitionKernel q ^ t) hA).ennreal_toReal).comp
        (comap_measurable present)).aestronglyMeasurable
  have hlarge :
      μ⟦future ⁻¹' A | MeasurableSpace.comap history inferInstance⟧ =ᵐ[μ] g := by
    -- Proof comment: this is the auxiliary arbitrary-gap Markov identity, rewritten to the
    -- explicit history-tuple sigma-algebra.
    simpa [μ, future, history, present, g, Nat.add_comm,
      generatedFiltrationSpace_productStartBranchingProcess_eq_historyTupleComap Y s] using
      hreal.markov_property x hA s t
  have hlarge' :
      μ[Set.indicator (future ⁻¹' A) (fun _ ↦ (1 : ℝ)) |
          MeasurableSpace.comap history inferInstance] =ᵐ[μ] g := by
    simpa using hlarge
  have hg_int : Integrable g μ := by
    exact (integrable_congr hlarge').1 integrable_condExp
  have hsmall' :
      μ[Set.indicator (future ⁻¹' A) (fun _ ↦ (1 : ℝ)) |
          MeasurableSpace.comap present inferInstance] =ᵐ[μ] g := by
    calc
      μ[Set.indicator (future ⁻¹' A) (fun _ ↦ (1 : ℝ)) |
          MeasurableSpace.comap present inferInstance] =ᵐ[μ]
          μ[μ[Set.indicator (future ⁻¹' A) (fun _ ↦ (1 : ℝ)) |
              MeasurableSpace.comap history inferInstance] |
            MeasurableSpace.comap present inferInstance] := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
      _ =ᵐ[μ] μ[g | MeasurableSpace.comap present inferInstance] := condExp_congr_ae hlarge'
      _ =ᵐ[μ] g := condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int
  have hsmall :
      μ⟦future ⁻¹' A | MeasurableSpace.comap present inferInstance⟧ =ᵐ[μ] g := by
    simpa using hsmall'
  have haux :
      μ⟦future ⁻¹' A | MeasurableSpace.comap history inferInstance⟧ =ᵐ[μ]
        μ⟦future ⁻¹' A | MeasurableSpace.comap present inferInstance⟧ := by
    exact hlarge.trans hsmall.symm
  have hpull :
      (fun ω ↦ (μ⟦future ⁻¹' A | MeasurableSpace.comap history inferInstance⟧) (f ω)) =ᵐ[
        (P : Measure Ω)]
        fun ω ↦ (μ⟦future ⁻¹' A | MeasurableSpace.comap present inferInstance⟧) (f ω) := by
    have haux' :
        μ⟦future ⁻¹' A | MeasurableSpace.comap history inferInstance⟧ =ᵐ[(P : Measure Ω).map f]
          μ⟦future ⁻¹' A | MeasurableSpace.comap present inferInstance⟧ := by
      simpa [hμ_map] using haux
    simpa [f] using ae_eq_comp measurable_prodMk_left.aemeasurable haux'
  have hleft :
      (fun ω ↦ (μ⟦future ⁻¹' A | MeasurableSpace.comap history inferInstance⟧) (f ω)) =ᵐ[
        (P : Measure Ω)]
        (P : Measure Ω)⟦branchingProcess x Y (s + t) ⁻¹' A |
          generatedFiltrationSpace (branchingProcess x Y) s⟧ := by
    have htransport :=
      fixedStartConditionalProb_comap_transport
        P x history future
        (measurable_productStartBranchingProcessHistoryTuple Y hY_meas s)
        (measurable_productStartBranchingProcess Y hY_meas (s + t)) hA
    -- Proof comment: after transporting along `ω ↦ (x, ω)`, the auxiliary history tuple and
    -- future coordinate collapse to the original branching history and future state.
    simpa [μ, f, future, history,
      productStartBranchingProcess_comp_prodMk Y x (s + t),
      productStartBranchingProcessHistoryTuple_comp_prodMk Y x s,
      generatedFiltrationSpace_branchingProcess_eq_historyTupleComap x Y s] using htransport
  have hright :
      (fun ω ↦ (μ⟦future ⁻¹' A | MeasurableSpace.comap present inferInstance⟧) (f ω)) =ᵐ[
        (P : Measure Ω)]
        (P : Measure Ω)⟦branchingProcess x Y (s + t) ⁻¹' A |
          MeasurableSpace.comap (branchingProcess x Y s) inferInstance⟧ := by
    have htransport :=
      fixedStartConditionalProb_comap_transport
        P x present future
        (measurable_productStartBranchingProcess Y hY_meas s)
        (measurable_productStartBranchingProcess Y hY_meas (s + t)) hA
    -- Proof comment: the present-state conditioning sigma-algebra also collapses under the
    -- fixed-start embedding to the sigma-algebra generated by `branchingProcess x Y s`.
    simpa [μ, f, future, present,
      productStartBranchingProcess_comp_prodMk Y x (s + t),
      productStartBranchingProcess_comp_prodMk Y x s] using htransport
  exact hleft.symm.trans <| hpull.trans hright

/-- Helper for Example 17.20: once the offspring array is measurable, the branching process has
the Markov property for its generated filtration. -/
private theorem branchingProcess_hasGeneratedFiltrationMarkovProperty
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    HasMarkovProperty
      (generatedFiltration (branchingProcess x Y)
        (measurable_branchingProcess x Y hY_meas))
      (P : Measure Ω) (branchingProcess x Y) := by
  have hNat :
      HasNaturalMarkovProperty (P : Measure Ω) (branchingProcess x Y) :=
    branchingProcess_hasNaturalMarkovProperty_ofMeasurable
      P q x Y hY_meas hY_indep hY_law
  refine ⟨?_, ?_⟩
  · intro s
    -- Proof comment: the generated filtration is adapted to the process by construction because
    -- the present coordinate is one of its generators.
    rw [generatedFiltration_apply]
    exact Measurable.of_comap_le (present_le_generatedFiltrationSpace (branchingProcess x Y) s)
  · intro A hA s t hst
    -- Proof comment: the natural-history conditional-probability identity becomes the
    -- `HasMarkovProperty` field once the generated filtration is unfolded.
    simpa [generatedFiltration_apply] using hNat.2 hst hA

-- Semantic recall: `lean_leansearch` only surfaced generic filtration/process APIs, so the
-- owner choice is verified from the local Chapter 17 owner `HasNaturalMarkovProperty`.
/-- Main source-facing theorem for Example 17.20: the branching process started from an arbitrary
population `x` and driven by an i.i.d. offspring array with common law `q` is a Markov chain on
`ℕ`; its one-step transition matrix is `p(x,y) = q^{*x}_y`, equivalently the transition kernel is
`branchingTransitionKernel q`.
-/
theorem branchingProcess_hasMarkovProperty
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω)) :
    HasNaturalMarkovProperty (P : Measure Ω) (branchingProcess x Y) := by
  refine ⟨measurable_branchingProcess x Y hY_meas, ?_⟩
  intro s t hst A hA
  have hMarkov :
      HasMarkovProperty
        (generatedFiltration (branchingProcess x Y)
          (measurable_branchingProcess x Y hY_meas))
        (P : Measure Ω) (branchingProcess x Y) :=
    branchingProcess_hasGeneratedFiltrationMarkovProperty P q x Y hY_meas hY_indep hY_law
  simpa [generatedFiltration_apply] using hMarkov.2 hA hst

/-- The branching process started from an arbitrary population `x` and driven by an i.i.d.
offspring array with common law `q` has one-step conditional law given by the branching kernel
whose matrix entries are `p(x,y) = q^{*x}_y`. -/
theorem branchingProcess_one_step_conditionalProb_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' A | generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (branchingProcess x Y n ω)).real A := by
  simpa using
    branchingProcess_one_step_conditionalProb_eq_transitionKernel_ofMeasurable
      P q x Y hY_meas hY_indep hY_law hA n

-- Proof sketch: specialize
-- `branchingProcess_one_step_conditionalProb_eq_transitionKernel` to the singleton set `{y}`
-- and rewrite the singleton kernel mass with `branchingTransitionKernel_apply_singleton`.
/-- The singleton-state form of the branching-process transition law is the textbook matrix formula
`P[Z_{n+1} = y | Z_n] = p(Z_n,y)` for the branching process started from `x`. -/
theorem branchingProcess_one_step_conditionalProb_eq_transitionMatrix
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n y : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' {y} |
        generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionMatrix q (branchingProcess x Y n ω) y).toReal := by
  -- Specialize the kernel statement to a singleton and rewrite the singleton kernel mass.
  simpa [Measure.real_def, branchingTransitionKernel_apply_singleton] using
    branchingProcess_one_step_conditionalProb_eq_transitionKernel
      P q x Y hY_meas hY_indep hY_law (measurableSet_singleton y) n

/-- Helper for Example 17.20: a singleton history fiber is preserved up to `μ`-almost-everywhere
equality when the history map is replaced by an a.e.-equal measurable representative. -/
private lemma branchingHistoryFiber_ae_eq_measurableRepresentativeFiber
    {μ : Measure Ω} {n : ℕ} {H H' : Ω → Fin (n + 1) → ℕ}
    (hH_ae : H =ᵐ[μ] H') (h : Fin (n + 1) → ℕ) :
    {ω | H ω = h} =ᵐ[μ] {ω | H' ω = h} := by
  -- Proof comment: pointwise equality of the two history maps identifies membership in the same
  -- singleton fiber.
  filter_upwards [hH_ae] with ω hω
  simpa [Set.mem_setOf_eq] using congrArg (fun t : Fin (n + 1) → ℕ ↦ t = h) hω

/-- Helper for Example 17.20: replacing the next-state map by an a.e.-equal measurable
representative preserves the indicator of the event `{ω | next ω ∈ A}`. -/
private lemma branchingNextEventIndicator_ae_eq_measurableRepresentative
    {μ : Measure Ω} {next next' : Ω → ℕ} {A : Set ℕ}
    (hnext_ae : next =ᵐ[μ] next') :
    Set.indicator (next ⁻¹' A) (fun _ => (1 : ℝ)) =ᵐ[μ]
      Set.indicator (next' ⁻¹' A) (fun _ => (1 : ℝ)) := by
  -- Proof comment: the two event indicators agree pointwise once the underlying next states are
  -- identified almost everywhere.
  filter_upwards [hnext_ae] with ω hω
  have hmem :
      (ω ∈ next ⁻¹' A) ↔ (ω ∈ next' ⁻¹' A) := by
    simp [Set.mem_preimage, hω]
  by_cases hleft : ω ∈ next ⁻¹' A
  · have hright : ω ∈ next' ⁻¹' A := hmem.mp hleft
    simp [Set.indicator, hleft, hright]
  · have hright : ω ∉ next' ⁻¹' A := by
      intro hright
      exact hleft (hmem.mpr hright)
    simp [Set.indicator, hleft, hright]

/-- Helper for Example 17.20: a fallback offspring row with only the first coordinate nonzero
still sums to that first coordinate over any nonempty prefix. -/
private lemma sum_range_fallbackRow_eq {a : ℕ} :
    ∀ k : ℕ, Finset.sum (Finset.range (k + 1)) (fun i ↦ if i = 0 then a else 0) = a
  | 0 => by simp
  | k + 1 => by
      -- Proof comment: peel off the last term until only the `i = 0` contribution remains.
      rw [Finset.sum_range_succ, sum_range_fallbackRow_eq k]
      simp

/-- Helper for Example 17.20: a Galton--Watson offspring witness admits a measurable
modification that preserves the branching recursion exactly. -/
private lemma galtonWatsonMeasurableOffspringModification
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ_meas : ∀ n, Measurable (Z n))
    {offspring : ℕ → ℕ → Ω → ℕ}
    (hsucc : ∀ n ω, Z (n + 1) ω =
      Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω))
    (hoffspring_indep : iIndepFun (fun ij : ℕ × ℕ ↦ offspring ij.1 ij.2) (P : Measure Ω))
    (hoffspring_law : ∀ n i, HasLaw (offspring n i) q.toMeasure (P : Measure Ω)) :
    ∃ offspringMeas : ℕ → ℕ → Ω → ℕ,
      (∀ n i, Measurable (offspringMeas n i)) ∧
      (∀ n ω,
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω)) ∧
      iIndepFun (fun ij : ℕ × ℕ ↦ offspringMeas ij.1 ij.2) (P : Measure Ω) ∧
      (∀ n i, HasLaw (offspringMeas n i) q.toMeasure (P : Measure Ω)) := by
  classical
  let μ : Measure Ω := (P : Measure Ω)
  let offspringAe : ℕ × ℕ → Ω → ℕ := fun ij ω ↦ offspring ij.1 ij.2 ω
  let hf : ∀ ij : ℕ × ℕ, AEMeasurable (offspringAe ij) μ := by
    intro ij
    exact (hoffspring_law ij.1 ij.2).aemeasurable
  let offspringSeq : ℕ × ℕ → Ω → ℕ := aeSeq hf (fun _ _ ↦ True)
  let goodSet : Set Ω := aeSeqSet hf (fun _ _ ↦ True)
  let offspringMeas : ℕ → ℕ → Ω → ℕ :=
    fun n i ω ↦
      if hω : ω ∈ goodSet then offspringSeq (n, i) ω else if i = 0 then Z (n + 1) ω else 0
  have hgood_meas : MeasurableSet goodSet := aeSeq.aeSeqSet_measurableSet
  have hgood_ae : ∀ᵐ ω ∂μ, ω ∈ goodSet := by
    -- Proof comment: `aeSeq` repairs the whole offspring array simultaneously outside one null
    -- set, so a single good set controls every coordinate.
    exact ae_iff.2 <|
      aeSeq.measure_compl_aeSeqSet_eq_zero hf (Filter.Eventually.of_forall fun _ ↦ trivial)
  have hoffspringSeq_meas : ∀ n i, Measurable (fun ω ↦ offspringSeq (n, i) ω) := by
    intro n i
    simpa [offspringSeq] using aeSeq.measurable hf (fun _ _ ↦ True) (n, i)
  have hoffspringMeas_meas : ∀ n i, Measurable (offspringMeas n i) := by
    intro n i
    -- Proof comment: on the null complement we replace the row by the fallback row, and each
    -- branch is measurable because `Z (n + 1)` is measurable.
    refine Measurable.ite hgood_meas (hoffspringSeq_meas n i) ?_
    by_cases hi : i = 0
    · simpa [offspringMeas, hi] using hZ_meas (n + 1)
    · simp [hi]
  have hsucc_meas :
      ∀ n ω,
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω) := by
    intro n ω
    by_cases hω : ω ∈ goodSet
    · -- Proof comment: on the full-measure good set, the measurable repair agrees pointwise with
      -- the original offspring array.
      have hEq : ∀ i : ℕ, offspringMeas n i ω = offspring n i ω := by
        intro i
        simp [offspringMeas, hω, offspringSeq, offspringAe,
          aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hω (n, i)]
      calc
        Z (n + 1) ω = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω) := hsucc n ω
        _ = Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspringMeas n i ω) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact (hEq i).symm
    · -- Proof comment: off the good set, the fallback row stores the whole next generation in
      -- the first coordinate and zeros elsewhere, so the recursion is forced exactly.
      by_cases hZn : Z n ω = 0
      · have hnext_zero : Z (n + 1) ω = 0 := by
          simpa [hZn] using hsucc n ω
        simp [offspringMeas, hω, hZn, hnext_zero]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hZn
        simp [offspringMeas, hω, hk]
  have hagree :
      ∀ᵐ ω ∂μ, ∀ n i, offspringMeas n i ω = offspring n i ω := by
    filter_upwards [hgood_ae] with ω hω n i
    simp [offspringMeas, hω, offspringSeq, offspringAe,
      aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hω (n, i)]
  have hoffspringMeas_indep :
      iIndepFun (fun ij : ℕ × ℕ ↦ offspringMeas ij.1 ij.2) μ := by
    refine hoffspring_indep.congr ?_
    intro ij
    filter_upwards [hagree] with ω hω
    exact (hω ij.1 ij.2).symm
  have hoffspringMeas_law :
      ∀ n i, HasLaw (offspringMeas n i) q.toMeasure μ := by
    intro n i
    refine (hoffspring_law n i).congr ?_
    filter_upwards [hagree] with ω hω
    exact hω n i
  exact ⟨offspringMeas, hoffspringMeas_meas, hsucc_meas, hoffspringMeas_indep,
    hoffspringMeas_law⟩

/-- Helper for Example 17.20: on the discrete state space `ℕ`, the branching-process one-step
conditional law is the measurable branching-process theorem once the offspring array itself is
measurable. -/
private theorem branchingProcess_one_step_conditionalProb_eq_transitionKernel_discrete
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ n i, Measurable (Y n i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦branchingProcess x Y (n + 1) ⁻¹' A | generatedFiltrationSpace (branchingProcess x Y) n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (branchingProcess x Y n ω)).real A := by
  -- Route correction: this private helper now stays at the measurable owner level instead of
  -- transporting conditional expectations across an only-a.e.-equal history map.
  simpa using
    branchingProcess_one_step_conditionalProb_eq_transitionKernel_ofMeasurable
      P q x Y hY_meas hY_indep hY_law hA n

section
omit [MeasurableSpace Ω]

/-- Helper for Example 17.20: a Galton--Watson process agrees with the one-ancestor branching
process built from the recovered offspring array. -/
private theorem galtonWatson_eq_branchingProcess
    (Z : ℕ → Ω → ℕ) (offspring : ℕ → ℕ → Ω → ℕ)
    (hZ0 : ∀ ω, Z 0 ω = 1)
    (hrec : ∀ n ω, Z (n + 1) ω =
      Finset.sum (Finset.range (Z n ω)) (fun i ↦ offspring n i ω)) :
    ∀ n ω, Z n ω = branchingProcess 1 offspring n ω := by
  intro n
  induction n with
  | zero =>
      intro ω
      -- Both processes start from one ancestor.
      simpa [branchingProcess_zero] using hZ0 ω
  | succ n ih =>
      intro ω
      -- Rewrite the next generation using the common branching recursion.
      rw [hrec, branchingProcess]
      simp_rw [ih ω]

end

-- Proof sketch: recover the offspring array from the Chapter 3 owner and identify `Z` with the
-- one-ancestor branching process `branchingProcess 1 offspring`; then apply the source-facing
-- branching-process theorem above.
/-- Example 17.20: the Chapter 3 one-ancestor Galton--Watson owner, together with genuine
measurability of the realized generations, specializes the source-facing branching transition law.
-/
theorem galtonWatsonProcess_one_step_conditionalProb_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ : IsGaltonWatsonProcess Z (P : Measure Ω) q)
    (hZ_meas : ∀ n, Measurable (Z n))
    ⦃A : Set ℕ⦄ (hA : MeasurableSet A) (n : ℕ) :
    P⟦Z (n + 1) ⁻¹' A | generatedFiltrationSpace Z n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionKernel q (Z n ω)).real A := by
  rcases hZ.exists_offspring with ⟨offspring, hrec, hoffspring_indep, hoffspring_law⟩
  rcases galtonWatsonMeasurableOffspringModification P q Z hZ_meas hrec
      hoffspring_indep hoffspring_law with
    ⟨offspringMeas, hoffspringMeas_meas, hrec_meas, hoffspringMeas_indep,
      hoffspringMeas_law⟩
  have hbranch :
      ∀ m ω, Z m ω = branchingProcess 1 offspringMeas m ω :=
    galtonWatson_eq_branchingProcess Z offspringMeas hZ.initial hrec_meas
  have hbranch_fun :
      ∀ m, Z m = branchingProcess 1 offspringMeas m :=
    fun m ↦ funext (hbranch m)
  have hfiltration :
      generatedFiltrationSpace Z n =
        generatedFiltrationSpace (branchingProcess 1 offspringMeas) n := by
    -- Proof comment: the two history filtrations agree because all time coordinates agree
    -- pointwise, so no AE-descent is needed here.
    simp only [generatedFiltrationSpace, hbranch_fun]
  -- Route correction: replace the nonmeasurable offspring witness by the measurable repair, then
  -- rewrite `Z` to that branching realization and invoke the measurable branching theorem.
  simpa only [hfiltration, hbranch_fun n, hbranch_fun (n + 1)] using
    (branchingProcess_one_step_conditionalProb_eq_transitionKernel_discrete
      P q 1 offspringMeas hoffspringMeas_meas hoffspringMeas_indep hoffspringMeas_law hA n)

-- Proof sketch: specialize the preceding bridge theorem to the singleton set `{y}` and rewrite
-- the singleton kernel mass with `branchingTransitionKernel_apply_singleton`.
/-- The Chapter 3 one-ancestor owner also yields the textbook singleton-matrix formula
`P[Z_{n+1} = y | Z_n] = p(Z_n,y)` once the generations are genuinely measurable random variables.
-/
theorem galtonWatsonProcess_one_step_conditionalProb_eq_transitionMatrix
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Z : ℕ → Ω → ℕ)
    (hZ : IsGaltonWatsonProcess Z (P : Measure Ω) q)
    (hZ_meas : ∀ n, Measurable (Z n))
    (n y : ℕ) :
    P⟦Z (n + 1) ⁻¹' {y} | generatedFiltrationSpace Z n⟧
      =ᵐ[(P : Measure Ω)]
        fun ω ↦ (branchingTransitionMatrix q (Z n ω) y).toReal := by
  -- Specialize the Galton--Watson kernel identity to the singleton `{y}`.
  simpa [Measure.real_def, branchingTransitionKernel_apply_singleton] using
    galtonWatsonProcess_one_step_conditionalProb_eq_transitionKernel
      P q Z hZ hZ_meas (measurableSet_singleton y) n

end ProbabilityTheory
