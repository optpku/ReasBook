/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.HasLawExists
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_16

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

/-- Helper for Theorem 24.12: on an empty measurable space every measure is zero. -/
private theorem measure_eq_zero_of_isEmpty
    {E : Type v} [MeasurableSpace E] [IsEmpty E] (μ : Measure E) :
    μ = 0 := by
  ext A hA
  have hA_empty : A = ∅ := by
    ext x
    exact isEmptyElim x
  -- Proof comment: there are no points in the ambient space, so every measurable set is empty.
  simp [hA_empty]

/-- Helper for Theorem 24.12: a constant family is independent under every probability law. -/
private theorem iIndepFun_const
    {Ω : Type u} [MeasurableSpace Ω] {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {P : Measure Ω} [IsProbabilityMeasure P]
    (c : ∀ i, β i) :
    iIndepFun (fun i : ι ↦ fun _ : Ω ↦ c i) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul (f := fun i : ι ↦ fun _ : Ω ↦ c i)]
  intro S sets hsets
  classical
  by_cases hempty : ∃ i ∈ S, c i ∉ sets i
  · rcases hempty with ⟨i, hiS, hi_not_mem⟩
    have hinter :
        (⋂ j ∈ S, (fun _ : Ω ↦ c j) ⁻¹' sets j) = ∅ := by
      rw [Set.iInter₂_eq_empty_iff]
      intro ω
      exact ⟨i, hiS, by simp [hi_not_mem]⟩
    -- Proof comment: one forbidden coordinate forces the whole intersection to be empty, and
    -- the product side has the corresponding zero factor.
    rw [hinter, measure_empty]
    symm
    refine Finset.prod_eq_zero hiS ?_
    change P ((fun _ : Ω ↦ c i) ⁻¹' sets i) = (0 : ENNReal)
    simp [hi_not_mem]
  · push Not at hempty
    have hinter :
        (⋂ j ∈ S, (fun _ : Ω ↦ c j) ⁻¹' sets j) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact hempty
    -- Proof comment: if every constant value lies in its target set, all preimages are `univ`.
    rw [hinter, measure_univ]
    symm
    calc
      ∏ i ∈ S, P ((fun _ : Ω ↦ c i) ⁻¹' sets i)
          = ∏ i ∈ S, (1 : ENNReal) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              simp [hempty i hi]
      _ = 1 := by simp

/-- Helper for Theorem 24.12: the constant zero `ENNReal` random variable has the pushed-forward
zero-rate Poisson law. -/
private theorem hasLawZeroMappedPoissonZero
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
    HasLaw (fun _ : Ω ↦ (0 : ENNReal))
      (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure 0)) P := by
  refine ⟨measurable_const.aemeasurable, ?_⟩
  -- Proof comment: both laws are the Dirac mass at `0`.
  rw [Measure.map_const]
  simp [poissonMeasureZeroEqDirac]

/-- Helper for Theorem 24.12: the first `n` marks determine the finite point measure obtained by
adding the corresponding Dirac masses. -/
private def prefixDiracSum
    {E : Type v} [MeasurableSpace E] (n : ℕ) (y : ℕ → E) : Measure E :=
  Finset.sum (Finset.range n) fun i ↦ Measure.dirac (y i)

/-- Helper for Theorem 24.12: evaluating the finite Dirac prefix on a measurable set is the finite
sum of the corresponding indicator counts. -/
private theorem prefixDiracSum_apply
    {E : Type v} [MeasurableSpace E] (n : ℕ) (y : ℕ → E) {A : Set E}
    (hA : MeasurableSet A) :
    prefixDiracSum n y A =
      Finset.sum (Finset.range n) fun i ↦ A.indicator (1 : E → ENNReal) (y i) := by
  -- Proof comment: expand the finite sum of Dirac masses and evaluate each Dirac measure on `A`.
  simp [prefixDiracSum, hA, Measure.dirac_apply']

/-- Helper for Theorem 24.12: for fixed prefix length, the finite Dirac-sum construction is
measurable as a measure-valued map. -/
private theorem prefixDiracSum_measurable
    {E : Type v} [MeasurableSpace E] (n : ℕ) :
    Measurable (fun y : ℕ → E ↦ prefixDiracSum n y) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro A hA
  have hterm :
      ∀ i : ℕ, Measurable fun y : ℕ → E ↦ A.indicator (1 : E → ENNReal) (y i) := by
    intro i
    -- Proof comment: each summand is the indicator of `A` evaluated at one measurable coordinate.
    exact (Measurable.indicator measurable_const hA).comp (measurable_pi_apply i)
  have hsum :
      Measurable fun y : ℕ → E ↦
        Finset.sum (Finset.range n) fun i ↦ A.indicator (1 : E → ENNReal) (y i) := by
    -- Proof comment: a finite sum of measurable coordinate indicators is measurable.
    exact (Finset.range n).measurable_fun_sum fun i _ ↦ hterm i
  have hEval :
      (fun y : ℕ → E ↦ prefixDiracSum n y A) =
        (fun y : ℕ → E ↦
          Finset.sum (Finset.range n) fun i ↦ A.indicator (1 : E → ENNReal) (y i)) := by
    funext y
    exact prefixDiracSum_apply n y hA
  -- Proof comment: the measurable evaluation formula upgrades to measurability of the
  -- measure-valued finite-prefix constructor.
  simpa [hEval] using hsum

/-- Helper for Theorem 24.12: every finite Dirac prefix gives finite mass to any measurable set. -/
private theorem prefixDiracSum_lt_top
    {E : Type v} [MeasurableSpace E] (n : ℕ) (y : ℕ → E) {A : Set E}
    (hA : MeasurableSet A) :
    prefixDiracSum n y A < ∞ := by
  calc
    prefixDiracSum n y A
        = Finset.sum (Finset.range n) fun i ↦ A.indicator (1 : E → ENNReal) (y i) := by
            rw [prefixDiracSum_apply n y hA]
    _ ≤ Finset.sum (Finset.range n) fun _ ↦ (1 : ENNReal) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          by_cases hiA : y i ∈ A
          · -- Proof comment: on the set `A`, each indicator summand contributes exactly `1`.
            simp [Set.indicator, hiA]
          · -- Proof comment: outside `A`, the indicator contribution vanishes.
            simp [Set.indicator, hiA]
    _ < ∞ := by
          simp

/-- Helper for Theorem 24.12: the finite marked prefix canonically defines a boundedly finite
point measure. -/
private def markedPrefixPointMeasure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] (ω : ℕ × (ℕ → E)) :
    BoundedlyFiniteMeasure E :=
  ⟨prefixDiracSum ω.1 ω.2, fun _ hA _ ↦ prefixDiracSum_lt_top ω.1 ω.2 hA⟩

/-- Helper for Theorem 24.12: evaluating the boundedly finite marked prefix reduces to the
corresponding finite Dirac-sum evaluation formula. -/
private theorem markedPrefixPointMeasure_apply
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] (ω : ℕ × (ℕ → E))
    {A : Set E} (hA : MeasurableSet A) :
    (markedPrefixPointMeasure ω : Measure E) A =
      Finset.sum (Finset.range ω.1) fun i ↦ A.indicator (1 : E → ENNReal) (ω.2 i) := by
  -- Proof comment: the boundedly finite wrapper does not change the underlying finite Dirac sum.
  exact prefixDiracSum_apply ω.1 ω.2 hA

/-- Helper for Theorem 24.12: the marked prefix count on a set is the nat-valued number of marks
among the first `ω.1` coordinates that land in `A`. -/
private def markedPrefixCount
    {E : Type v} [MeasurableSpace E] (ω : ℕ × (ℕ → E)) (A : Set E) : ℕ :=
  ∑ i ∈ Finset.range ω.1, A.indicator (1 : E → ℕ) (ω.2 i)

/-- Helper for Theorem 24.12: for a measurable test set, the marked-prefix count is measurable as
an ordinary nat-valued random variable. -/
private theorem measurable_markedPrefixCount
    {E : Type v} [MeasurableSpace E] {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun ω : ℕ × (ℕ → E) ↦ markedPrefixCount ω A) := by
  refine measurable_from_prod_countable_right ?_
  intro n
  have hterm :
      ∀ i : ℕ, Measurable fun y : ℕ → E ↦ A.indicator (1 : E → ℕ) (y i) := by
    intro i
    exact (Measurable.indicator measurable_const hA).comp (measurable_pi_apply i)
  -- Proof comment: on each fixed `n`-fiber, the count is a finite sum of measurable coordinate
  -- indicators.
  simpa [markedPrefixCount] using
    (Finset.range n).measurable_fun_sum fun i _ ↦ hterm i

/-- Helper for Theorem 24.12: evaluating the marked prefix point measure on a measurable set
recovers the nat-valued marked prefix count after the canonical cast to `ENNReal`. -/
private theorem markedPrefixCount_apply
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] (ω : ℕ × (ℕ → E))
    {A : Set E} (hA : MeasurableSet A) :
    (markedPrefixPointMeasure ω : Measure E) A = (markedPrefixCount ω A : ENNReal) := by
  -- Proof comment: each Dirac mass contributes exactly one unit when its mark lies in `A`,
  -- so the measure evaluation is the cast of the obvious nat-valued counting formula.
  rw [markedPrefixPointMeasure_apply ω hA, markedPrefixCount]
  calc
    ∑ i ∈ Finset.range ω.1, A.indicator (1 : E → ENNReal) (ω.2 i)
        = ∑ i ∈ Finset.range ω.1,
            (((A.indicator (1 : E → ℕ) (ω.2 i) : ℕ) : ENNReal)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hiA : ω.2 i ∈ A
              · simp [Set.indicator, hiA]
              · simp [Set.indicator, hiA]
    _ = (∑ i ∈ Finset.range ω.1, A.indicator (1 : E → ℕ) (ω.2 i) : ℕ) := by
          rw [Nat.cast_sum]
    _ = (markedPrefixCount ω A : ENNReal) := by
          simp [markedPrefixCount]

/-- Helper for Theorem 24.12: one mark contributes the coordinatewise indicator vector of the
chosen measurable cells. -/
private def markIndicatorVector
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E) (x : E) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ (As i).indicator (1 : E → ℝ) x)

/-- Helper for Theorem 24.12: the `k + 1`-st summand in the compound-Poisson route records the
indicator vector of the `k`-th mark, while index `0` is the dummy zero term. -/
private def markedPrefixIndicatorSequence
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E) :
    ℕ → (ℕ × (ℕ → E)) → EuclideanSpace ℝ (Fin d)
  | 0, _ => 0
  | k + 1, ω => markIndicatorVector As (ω.2 k)

/-- Helper for Theorem 24.12: the shifted textbook `Finset.Icc 1 N` sum of mark-indicator
vectors is the real-cast tuple of marked-prefix counts. -/
private theorem markedPrefixCountVector_eq_indicatorIccSum
    {E : Type v} [MeasurableSpace E] {d : ℕ} (As : Fin d → Set E)
    (ω : ℕ × (ℕ → E)) :
    (∑ j ∈ Finset.Icc 1 ω.1, markedPrefixIndicatorSequence As j ω) =
      fun i ↦ (markedPrefixCount ω (As i) : ℝ) := by
  ext i
  -- Proof comment: after evaluating the Euclidean-space sum coordinatewise, the shifted
  -- `Finset.Icc 1 N` textbook sum is exactly the nat-valued marked-prefix count cast to `ℝ`.
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hterm :
      ∀ c : ℕ, (markedPrefixIndicatorSequence As (1 + c) ω).ofLp i =
        (As i).indicator (1 : E → ℝ) (ω.2 c) := by
    intro c
    simpa [Nat.add_comm] using
      (show (markedPrefixIndicatorSequence As (c + 1) ω).ofLp i =
          (As i).indicator (1 : E → ℝ) (ω.2 c) by
        simp [markedPrefixIndicatorSequence, markIndicatorVector])
  have hcast :
      ∀ c : ℕ, (As i).indicator (1 : E → ℝ) (ω.2 c) =
        (((As i).indicator (1 : E → ℕ) (ω.2 c) : ℕ) : ℝ) := by
    intro c
    by_cases hcA : ω.2 c ∈ As i
    · simp [Set.indicator, hcA]
    · simp [Set.indicator, hcA]
  have hsum :
      (∑ c ∈ Finset.range (Order.succ ω.1 - 1),
        (markedPrefixIndicatorSequence As (1 + c) ω).ofLp i) =
        (markedPrefixCount ω (As i) : ℝ) := by
    calc
      ∑ c ∈ Finset.range (Order.succ ω.1 - 1), (markedPrefixIndicatorSequence As (1 + c) ω).ofLp i
          = ∑ c ∈ Finset.range ω.1, (As i).indicator (1 : E → ℝ) (ω.2 c) := by
              simp [hterm]
      _ = ∑ c ∈ Finset.range ω.1, (((As i).indicator (1 : E → ℕ) (ω.2 c) : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            exact hcast c
      _ = (markedPrefixCount ω (As i) : ℝ) := by
            simp [markedPrefixCount]
  simpa using hsum

/-- Helper for Theorem 24.12: the uncurried marked-prefix map is measurable as a
`Measure E`-valued random variable. -/
private theorem markedPrefixPointMeasureMeasurable
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] :
    Measurable (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E)) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro A hA
  refine measurable_from_prod_countable_right ?_
  intro n
  -- Proof comment: on each countable `n`-fiber the uncurried map is exactly the fixed-prefix
  -- constructor, whose measure-valued measurability was already proved.
  simpa [markedPrefixPointMeasure] using
    (Measure.measurable_coe hA).comp (prefixDiracSum_measurable (E := E) n)

/-- Helper for Theorem 24.12: the explicit marked-prefix construction is boundedly finite under
every ambient probability law, so later PPP work can focus on the count-law and independence
interfaces. -/
private theorem markedPrefixPointMeasure_isBoundedlyFiniteRandomMeasure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E]
    (P : ProbabilityMeasure (ℕ × (ℕ → E))) :
    IsBoundedlyFiniteRandomMeasure P
      (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E)) := by
  refine ⟨markedPrefixPointMeasureMeasurable, ?_⟩
  intro A hA hA_bdd
  -- Proof comment: every sample is already a boundedly finite measure, so bounded-set finiteness
  -- holds pointwise and therefore almost surely.
  exact Filter.Eventually.of_forall fun ω ↦
    (markedPrefixPointMeasure ω).2 hA hA_bdd

/-- Helper for Theorem 24.12: every bounded set is contained in some closed ball of integer
radius around a chosen center. -/
private theorem bounded_subset_closedBall_nat
    {E : Type v} [PseudoMetricSpace E] {A : Set E}
    (hA_bdd : Bornology.IsBounded A) (x0 : E) :
    ∃ N : ℕ, A ⊆ Metric.closedBall x0 N := by
  rcases hA_bdd.subset_closedBall x0 with ⟨r, hr⟩
  refine ⟨Nat.ceil r, ?_⟩
  intro x hx
  refine Metric.mem_closedBall.2 ?_
  exact le_trans (Metric.mem_closedBall.1 (hr hx)) (by exact_mod_cast Nat.le_ceil r)

/-- Helper for Theorem 24.12: the corrected shell partition uses the center ball at radius `0`
and the successive annuli between consecutive closed balls. -/
private def closedBallPiece
    {E : Type v} [PseudoMetricSpace E] (x0 : E) : ℕ → Set E
  | 0 => Metric.closedBall x0 0
  | n + 1 => Metric.closedBall x0 (n + 1 : ℝ) \ Metric.closedBall x0 (n : ℝ)

/-- Helper for Theorem 24.12: every corrected shell piece is measurable. -/
private theorem measurableSet_closedBallPiece
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (x0 : E) (n : ℕ) :
    MeasurableSet (closedBallPiece x0 n) := by
  cases n with
  | zero =>
      simpa [closedBallPiece] using measurableSet_closedBall
  | succ n =>
      simpa [closedBallPiece] using
        measurableSet_closedBall.diff measurableSet_closedBall

/-- Helper for Theorem 24.12: the `n`-th corrected shell piece stays inside the corresponding
closed ball of radius `n`. -/
private theorem closedBallPiece_subset_closedBall
    {E : Type v} [PseudoMetricSpace E] (x0 : E) (n : ℕ) :
    closedBallPiece x0 n ⊆ Metric.closedBall x0 (n : ℝ) := by
  cases n with
  | zero =>
      intro x hx
      simpa [closedBallPiece] using hx
  | succ n =>
      intro x hx
      simpa [Nat.cast_add] using hx.1

/-- Helper for Theorem 24.12: distinct corrected shell pieces are pairwise disjoint. -/
private theorem closedBallPiece_pairwiseDisjoint
    {E : Type v} [PseudoMetricSpace E] (x0 : E) :
    Pairwise fun m n ↦ Disjoint (closedBallPiece x0 m) (closedBallPiece x0 n) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hmn_lt | hnm_lt
  · cases n with
    | zero =>
        exact False.elim (Nat.not_lt_zero _ hmn_lt)
    | succ n =>
        refine Set.disjoint_left.2 ?_
        intro x hxm hxn
        have hxm_ball : x ∈ Metric.closedBall x0 (m : ℝ) :=
          closedBallPiece_subset_closedBall x0 m hxm
        have hmle : m ≤ n := Nat.le_sub_one_of_lt hmn_lt
        have hxm_prev : x ∈ Metric.closedBall x0 (n : ℝ) :=
          Metric.closedBall_subset_closedBall (by exact_mod_cast hmle) hxm_ball
        simpa [closedBallPiece] using hxn.2 hxm_prev
  · exact (closedBallPiece_pairwiseDisjoint x0 hnm_lt.ne).symm

/-- Helper for Theorem 24.12: the first `N + 1` corrected shell pieces partition
`Metric.closedBall x0 N`. -/
private theorem iUnion_closedBallPiece_range
    {E : Type v} [PseudoMetricSpace E] (x0 : E) (N : ℕ) :
    ⋃ n ∈ Finset.range (N + 1), closedBallPiece x0 n = Metric.closedBall x0 (N : ℝ) := by
  induction N with
  | zero =>
      ext x
      simp [closedBallPiece]
  | succ N ih =>
      ext x
      constructor
      · intro hx
        simp only [Set.mem_iUnion, Finset.mem_range] at hx
        rcases hx with ⟨n, hn, hxn⟩
        by_cases hlast : n = N + 1
        · subst hlast
          simpa [closedBallPiece] using hxn.1
        · have hn' : n < N + 1 := lt_of_le_of_ne (Nat.le_of_lt_succ hn) hlast
          have hxN : x ∈ Metric.closedBall x0 (N : ℝ) := by
            rw [← ih]
            exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨by simpa [Finset.mem_range] using hn', hxn⟩⟩
          exact Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.le_succ N) hxN
      · intro hx
        by_cases hxN : x ∈ Metric.closedBall x0 (N : ℝ)
        · rw [← ih] at hxN
          simp only [Set.mem_iUnion, Finset.mem_range] at hxN ⊢
          rcases hxN with ⟨n, hn, hxn⟩
          exact ⟨n, Nat.lt_succ_of_lt hn, hxn⟩
        · simp only [Set.mem_iUnion, Finset.mem_range]
          refine ⟨N + 1, by simp, ?_⟩
          simpa [closedBallPiece, Nat.cast_add] using And.intro hx hxN

/-- Helper for Theorem 24.12: once a measurable set is contained in `Metric.closedBall x0 N`, the
shell restrictions beyond `N` vanish on that set. -/
private theorem closedBallPiece_eventuallyZeroOnSubset
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {A : Set E} (hA : MeasurableSet A)
    {x0 : E} {N : ℕ} (hA_sub : A ⊆ Metric.closedBall x0 (N : ℝ)) :
    ∀ n > N, (μ.restrict (closedBallPiece x0 n)) A = 0 := by
  intro n hn
  rw [Measure.restrict_apply hA]
  have hEmpty : A ∩ closedBallPiece x0 n = ∅ := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ A := hx.1
      have hxBall : x ∈ Metric.closedBall x0 (N : ℝ) := hA_sub hxA
      cases n with
      | zero =>
          exact False.elim (Nat.not_lt_zero _ hn)
      | succ n =>
          have hNle : N ≤ n := Nat.le_sub_one_of_lt hn
          have hxPrev : x ∈ Metric.closedBall x0 (n : ℝ) :=
            Metric.closedBall_subset_closedBall (by exact_mod_cast hNle) hxBall
          exact False.elim <| hx.2.2 hxPrev
    · intro hx
      exact False.elim hx
  -- Proof comment: later shells are disjoint from any set already contained in the earlier ball.
  simp [hEmpty]

/-- Helper for Theorem 24.12: each corrected shell of a boundedly finite intensity has finite
total mass. -/
private theorem closedBallPieceRestriction_lt_top
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : BoundedlyFiniteMeasure E) (x0 : E) (n : ℕ) :
    ((μ : Measure E).restrict (closedBallPiece x0 n)) Set.univ < ∞ := by
  calc
    ((μ : Measure E).restrict (closedBallPiece x0 n)) Set.univ
        = (μ : Measure E) (closedBallPiece x0 n) := by
            rw [Measure.restrict_apply MeasurableSet.univ]
            simp
    _ ≤ (μ : Measure E) (Metric.closedBall x0 (n : ℝ)) := by
          exact measure_mono fun x hx ↦ closedBallPiece_subset_closedBall x0 n hx
    _ < ∞ := by
          exact BoundedlyFiniteMeasure.lt_top_of_isBounded μ
            measurableSet_closedBall Metric.isBounded_closedBall

/-- Helper for Theorem 24.12: on a bounded measurable set inside `Metric.closedBall x0 N`, the
mass of `μ` splits into the finite sum of its corrected shell restrictions. -/
private theorem closedBallPiece_prefix_sum_eq
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (x0 : E) {A : Set E} (hA : MeasurableSet A) {N : ℕ}
    (hA_sub : A ⊆ Metric.closedBall x0 (N : ℝ)) :
    μ A = Finset.sum (Finset.range (N + 1))
      (fun n ↦ ((μ.restrict (closedBallPiece x0 n)) A)) := by
  let T : Finset ℕ := Finset.range (N + 1)
  have hA_cover : A ⊆ ⋃ n ∈ T, closedBallPiece x0 n := by
    intro x hx
    have hxUnion : x ∈ ⋃ n ∈ Finset.range (N + 1), closedBallPiece x0 n := by
      rw [iUnion_closedBallPiece_range x0 N]
      exact hA_sub hx
    simpa [T] using hxUnion
  have hrestrict :
      μ.restrict (⋃ n ∈ T, closedBallPiece x0 n) =
        Measure.sum (fun i : T ↦ μ.restrict (closedBallPiece x0 i.1)) := by
    -- Proof comment: the first `N + 1` shell pieces form a measurable pairwise-disjoint finite
    -- partition of the closed ball, so restricting to their union is the sum of the restrictions.
    refine Measure.restrict_biUnion_finset ?_ ?_
    · intro i hi j hj hij
      exact closedBallPiece_pairwiseDisjoint x0 hij
    · intro n
      exact measurableSet_closedBallPiece x0 n
  -- Proof comment: since `A` lies inside the finite shell partition, evaluate `μ` on `A` by
  -- restricting to the union and then expand that restricted measure as a finite sum.
  calc
    μ A = μ (A ∩ ⋃ n ∈ T, closedBallPiece x0 n) := by
      rw [Set.inter_eq_left.2 hA_cover]
    _ = (μ.restrict (⋃ n ∈ T, closedBallPiece x0 n)) A := by
      rw [Measure.restrict_apply hA]
    _ = (Measure.sum (fun i : T ↦ μ.restrict (closedBallPiece x0 i.1))) A := by
      rw [hrestrict]
    _ = ∑' i : T, (μ.restrict (closedBallPiece x0 i.1)) A := by
      rw [Measure.sum_apply_of_countable]
    _ = ∑ i : T, (μ.restrict (closedBallPiece x0 i.1)) A := by
      rw [tsum_fintype]
    _ = Finset.sum T (fun n ↦ (μ.restrict (closedBallPiece x0 n)) A) := by
      exact T.sum_attach (fun n ↦ (μ.restrict (closedBallPiece x0 n)) A)
    _ = Finset.sum (Finset.range (N + 1))
          (fun n ↦ (μ.restrict (closedBallPiece x0 n)) A) := by
      simp [T]
  /-
  induction N with
  | zero =>
      have hAeq : A ∩ closedBallPiece x0 0 = A := by
        ext x
        simp [closedBallPiece, hA_sub]
      calc
        μ A = (μ.restrict (closedBallPiece x0 0)) A := by
                rw [Measure.restrict_apply hA, hAeq]
        _ = Finset.sum (Finset.range 1)
              (fun n ↦ ((μ.restrict (closedBallPiece x0 n)) A)) := by
                simp
  | succ N ih =>
      have hDecomp :
          A = (A ∩ Metric.closedBall x0 (N : ℝ)) ∪ (A ∩ closedBallPiece x0 (N + 1)) := by
        ext x
        constructor
        · intro hxA
          by_cases hxN : x ∈ Metric.closedBall x0 (N : ℝ)
          · exact Or.inl ⟨hxA, hxN⟩
          · have hxNp1 : x ∈ Metric.closedBall x0 (N + 1 : ℝ) := hA_sub hxA
            refine Or.inr ⟨hxA, ?_⟩
            simpa [closedBallPiece, Nat.cast_add] using And.intro hxNp1 hxN
        · intro hx
          rcases hx with hx | hx
          · exact hx.1
          · exact hx.1
      have hDisj :
          Disjoint (A ∩ Metric.closedBall x0 (N : ℝ)) (A ∩ closedBallPiece x0 (N + 1)) := by
        refine Set.disjoint_left.2 ?_
        intro x hx1 hx2
        exact hx2.2.2 hx1.2
      have hSubPrev : A ∩ Metric.closedBall x0 (N : ℝ) ⊆ Metric.closedBall x0 (N : ℝ) := by
        intro x hx
        exact hx.2
      calc
        μ A
            = μ (A ∩ Metric.closedBall x0 (N : ℝ)) +
                μ (A ∩ closedBallPiece x0 (N + 1)) := by
                  rw [hDecomp, measure_union hDisj]
        _ = Finset.sum (Finset.range (N + 1))
              (fun n ↦ ((μ.restrict (closedBallPiece x0 n)) (A ∩ Metric.closedBall x0 (N : ℝ)))) +
              (μ.restrict (closedBallPiece x0 (N + 1))) A := by
                rw [ih (hA_sub := hSubPrev), Measure.restrict_apply hA]
                simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        _ = Finset.sum (Finset.range (N + 2))
              (fun n ↦ ((μ.restrict (closedBallPiece x0 n)) A)) := by
                rw [Finset.sum_range_succ]
                refine congrArg (fun t ↦ t + (μ.restrict (closedBallPiece x0 (N + 1))) A) ?_
                refine Finset.sum_congr rfl ?_
                intro n hn
                rw [Measure.restrict_apply hA]
                have hTailZero :
                    A ∩ closedBallPiece x0 n = (A ∩ Metric.closedBall x0 (N : ℝ)) ∩
                      closedBallPiece x0 n := by
                  ext x
                  constructor
                  · intro hx
                    have hxA : x ∈ A := hx.1
                    have hxN : x ∈ Metric.closedBall x0 (N : ℝ) := by
                      exact Metric.closedBall_subset_closedBall
                        (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn))
                        (closedBallPiece_subset_closedBall x0 n hx.2)
                    exact ⟨⟨hxA, hxN⟩, hx.2⟩
                  · intro hx
                    exact ⟨hx.1.1, hx.2⟩
                rw [hTailZero]
                simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
  -/

/-- Helper for Theorem 24.12: sufficiently far closed-ball shells do not meet a fixed bounded
measurable set, so every shell restriction evaluates to zero there. -/
private theorem closedBallShellEventuallyZeroOnBoundedSet
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (x0 : E) :
    ∃ N : ℕ, ∀ n > N,
      (μ.restrict
        (Metric.closedBall x0 (n : ℝ) \ Metric.closedBall x0 ((n - 1 : ℕ) : ℝ))) A = 0 := by
  rcases bounded_subset_closedBall_nat hA_bdd x0 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [Measure.restrict_apply hA]
  have hinter :
      A ∩
          (Metric.closedBall x0 (n : ℝ) \ Metric.closedBall x0 ((n - 1 : ℕ) : ℝ)) = ∅ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxShell⟩
      have hxN : x ∈ Metric.closedBall x0 N := hN hxA
      have hNle : N ≤ n - 1 := Nat.le_sub_one_of_lt hn
      have hxNm1 : x ∈ Metric.closedBall x0 ((n - 1 : ℕ) : ℝ) :=
        Metric.closedBall_subset_closedBall (by exact_mod_cast hNle) hxN
      exact False.elim (hxShell.2 hxNm1)
    · intro hx
      exact False.elim hx
  -- Proof comment: once `A` sits inside a smaller closed ball, later shells are disjoint from it.
  simp [hinter]

/-- Helper for Theorem 24.12: each closed-ball shell of a boundedly finite intensity has finite
total mass, so it is eligible for the finite-intensity constructor. -/
private theorem closedBallShellRestriction_lt_top
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : BoundedlyFiniteMeasure E) (x0 : E) (n : ℕ) :
    ((μ : Measure E).restrict
      (Metric.closedBall x0 (n : ℝ) \ Metric.closedBall x0 ((n - 1 : ℕ) : ℝ))) Set.univ < ∞ := by
  rw [Measure.restrict_apply MeasurableSet.univ]
  -- Proof comment: each shell sits inside the ambient closed ball of radius `n`, and boundedly
  -- finite measures have finite mass on bounded measurable subsets.
  simpa [Set.univ_inter] using
    (lt_of_le_of_lt
      (measure_mono fun x hx ↦ hx.1)
      (BoundedlyFiniteMeasure.lt_top_of_isBounded μ
        (A := Metric.closedBall x0 (n : ℝ))
        measurableSet_closedBall
        Metric.isBounded_closedBall))

/-- Helper for Theorem 24.12: the sum of two independent Poisson counts is Poisson with the sum
of the rates. -/
private theorem hasLawPoissonAdd
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z W : Ω → ℕ} {r s : NNReal}
    (hZ : HasLaw Z (poissonMeasure r) P)
    (hW : HasLaw W (poissonMeasure s) P)
    (hZW : IndepFun Z W P) :
    HasLaw (fun ω ↦ Z ω + W ω) (poissonMeasure (r + s)) P := by
  -- Proof comment: independent sums push the two marginal laws through additive convolution, and
  -- Example 2.33 identifies the convolution of Poisson laws with the Poisson law of summed rate.
  simpa [poissonMeasure_conv_poissonMeasure] using hZW.hasLaw_add hZ hW

/-- Helper for Theorem 24.12: from independent vector-valued Poisson inputs, every coordinate of
the pointwise sum already has the expected scalar Poisson law. -/
private theorem hasLawPiPoisson_add_coordinate
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {Z W : Ω → Fin d → ℕ} {r s : Fin d → NNReal}
    (hZ : HasLaw Z (Measure.pi fun i ↦ poissonMeasure (r i)) P)
    (hW : HasLaw W (Measure.pi fun i ↦ poissonMeasure (s i)) P)
    (hZW : IndepFun Z W P)
    (i : Fin d) :
    HasLaw (fun ω ↦ Z ω i + W ω i) (poissonMeasure (r i + s i)) P := by
  have hZi : HasLaw (fun ω ↦ Z ω i) (poissonMeasure (r i)) P := by
    -- Proof comment: project the product law of `Z` to the `i`-th coordinate.
    let πi : (Fin d → ℕ) → ℕ := fun z ↦ z i
    have hπi :
        HasLaw πi (poissonMeasure (r i))
          (Measure.pi fun j ↦ poissonMeasure (r j)) := by
      refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
      simpa [πi] using
        (measurePreserving_eval (fun j : Fin d ↦ poissonMeasure (r j)) i).map_eq
    simpa [πi, Function.comp] using hπi.fun_comp hZ
  have hWi : HasLaw (fun ω ↦ W ω i) (poissonMeasure (s i)) P := by
    -- Proof comment: project the product law of `W` to the `i`-th coordinate.
    let πi : (Fin d → ℕ) → ℕ := fun z ↦ z i
    have hπi :
        HasLaw πi (poissonMeasure (s i))
          (Measure.pi fun j ↦ poissonMeasure (s j)) := by
      refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
      simpa [πi] using
        (measurePreserving_eval (fun j : Fin d ↦ poissonMeasure (s j)) i).map_eq
    simpa [πi, Function.comp] using hπi.fun_comp hW
  have hZiWi : IndepFun (fun ω ↦ Z ω i) (fun ω ↦ W ω i) P := by
    -- Proof comment: coordinate projections preserve independence of the vector-valued sources.
    simpa [Function.comp] using
      hZW.comp (measurable_pi_apply i) (measurable_pi_apply i)
  exact hasLawPoissonAdd hZi hWi hZiWi

/-- Helper for Theorem 24.12: rebuilding a finite nat-valued vector from its prefix block and last
coordinate transports the corresponding product law back to `Measure.pi`. -/
private theorem map_prod_snoc_eq_pi {m : ℕ} (μ : Fin (m + 1) → Measure ℕ)
    [∀ i, SigmaFinite (μ i)] :
    Measure.map (fun p : (Fin m → ℕ) × ℕ ↦ Fin.snoc p.1 p.2)
      ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m))) =
        Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℕ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hsnoc :
      (fun p : (Fin m → ℕ) × ℕ ↦ Fin.snoc p.1 p.2) = e.symm ∘ Prod.swap := by
    -- Proof comment: undoing the last-coordinate split reinserts the saved final coordinate in
    -- the `Fin.snoc` position.
    funext p
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.snoc_castSucc]
    · simp [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  -- Proof comment: rewrite the rebuild map as the inverse `piFinSuccAbove` transport followed by
  -- `Prod.swap`, then cancel it against the canonical split map.
  calc
    Measure.map (fun p : (Fin m → ℕ) × ℕ ↦ Fin.snoc p.1 p.2)
        ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)))
        = Measure.map e.symm
            (Measure.map Prod.swap
              ((Measure.pi fun i : Fin m ↦ μ i.castSucc).prod (μ (Fin.last m)))) := by
              rw [hsnoc, Measure.map_map e.symm.measurable measurable_swap]
    _ = Measure.map e.symm
          ((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ i.castSucc)) := by
            rw [Measure.prod_swap]
    _ = Measure.map e.symm
          ((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))) := by
            simp [Fin.succAbove_last]
    _ = Measure.pi μ := by
          rw [← hMapEq, MeasurableEquiv.map_symm_map]

/-- Helper for Theorem 24.12: adding the two tail coordinates in a product law leaves the prefix
block untouched and convolves the tail marginals. -/
private theorem map_prod_tailAdd_eq_prod_conv {m : ℕ} (μ : Measure (Fin m → ℕ))
    (ν ρ : Measure ℕ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    Measure.map (fun p : (Fin m → ℕ) × (ℕ × ℕ) ↦ (p.1, p.2.1 + p.2.2))
      (μ.prod (ν.prod ρ)) = μ.prod (ν ∗ ρ) := by
  -- Proof comment: this is `Measure.map_prod_map` with the identity on the prefix block and the
  -- addition map on the tail pair.
  simpa [Measure.conv] using
    (Measure.map_prod_map μ (ν.prod ρ) measurable_id measurable_add).symm

/-- Helper for Theorem 24.12: the convolution of two finite product Poisson laws is again the
product Poisson law with coordinatewise added rates. -/
private theorem poissonMeasurePi_conv
    {d : ℕ} (r s : Fin d → NNReal) :
    (Measure.pi (fun i ↦ poissonMeasure (r i))) ∗ (Measure.pi fun i ↦ poissonMeasure (s i)) =
      Measure.pi (fun i ↦ poissonMeasure (r i + s i)) := by
  let μ : Fin d → Measure ℕ := fun i ↦ poissonMeasure (r i)
  let ν : Fin d → Measure ℕ := fun i ↦ poissonMeasure (s i)
  let source : Measure (Fin d → ℕ × ℕ) := Measure.pi fun i ↦ (μ i).prod (ν i)
  let pairAdd : (Fin d → ℕ) × (Fin d → ℕ) → Fin d → ℕ := fun p i ↦ p.1 i + p.2 i
  let coordAdd : Fin d → (ℕ × ℕ) → ℕ := fun _ z ↦ z.1 + z.2
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin d)
  letI : ∀ i : Fin d, SigmaFinite (Measure.map (coordAdd i) ((μ i).prod (ν i))) := fun i ↦ by
    infer_instance
  have hpairAdd_comp : pairAdd ∘ e = fun x i ↦ (x i).1 + (x i).2 := by
    funext x
    ext i
    rfl
  -- Proof comment: rewrite the product of the two product laws as the pushforward of the
  -- coordinatewise pair law, then push addition through the finite product one coordinate at a
  -- time.
  calc
    (Measure.pi (fun i ↦ poissonMeasure (r i))) ∗ (Measure.pi fun i ↦ poissonMeasure (s i))
        = Measure.map pairAdd ((Measure.pi μ).prod (Measure.pi ν)) := by
            rfl
    _ = Measure.map pairAdd (Measure.map e source) := by
          rw [(measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin d) μ ν).map_eq]
    _ = Measure.map (fun x i ↦ (x i).1 + (x i).2) source := by
          simpa [source, hpairAdd_comp] using
            (Measure.map_map
              (μ := source)
              (f := e)
              (g := pairAdd)
              (by fun_prop)
              e.measurable)
    _ = Measure.pi (fun i ↦ Measure.map (coordAdd i) ((μ i).prod (ν i))) := by
          simpa [source, coordAdd] using
            (Measure.pi_map_pi
              (μ := fun i ↦ (μ i).prod (ν i))
              (f := coordAdd)
              (fun i ↦ measurable_add.aemeasurable))
    _ = Measure.pi (fun i ↦ poissonMeasure (r i + s i)) := by
          have hcoord :
              (fun i ↦ Measure.map (coordAdd i) ((μ i).prod (ν i))) =
                fun i ↦ poissonMeasure (r i + s i) := by
            funext i
            dsimp [coordAdd, μ, ν]
            simpa [Measure.conv] using poissonMeasure_conv_poissonMeasure (r i) (s i)
          exact congrArg Measure.pi hcoord

/-- Helper for Theorem 24.12: independent Poisson product laws are stable under coordinatewise
addition, with the rates adding coordinatewise as well. -/
private theorem hasLawPiPoisson_add
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {Z W : Ω → Fin d → ℕ} {r s : Fin d → NNReal}
    (hZ : HasLaw Z (Measure.pi fun i ↦ poissonMeasure (r i)) P)
    (hW : HasLaw W (Measure.pi fun i ↦ poissonMeasure (s i)) P)
    (hZW : IndepFun Z W P) :
    HasLaw (fun ω i ↦ Z ω i + W ω i)
      (Measure.pi fun i ↦ poissonMeasure (r i + s i)) P := by
  have hsum :
      HasLaw (fun ω ↦ Z ω + W ω)
        ((Measure.pi fun i ↦ poissonMeasure (r i)) ∗
          (Measure.pi fun i ↦ poissonMeasure (s i))) P := by
    -- Proof comment: `IndepFun.hasLaw_add` first gives the joint law of the pointwise sum as a
    -- convolution of the two product laws.
    simpa [Pi.add_apply] using hZW.hasLaw_add hZ hW
  -- Proof comment: the new product-law bridge identifies that convolution with the expected
  -- product Poisson law of rate `r + s`.
  simpa [poissonMeasurePi_conv (d := d) r s] using hsum

/-- Helper for Theorem 24.12: the normalized probability law of a nonzero finite intensity. -/
private def finiteMeasureOfLtTop
    {E : Type v} [MeasurableSpace E] (ν : Measure E) (hνfin : ν Set.univ < ∞) :
    FiniteMeasure E :=
  ⟨ν, ⟨hνfin⟩⟩

/-- Helper for Theorem 24.12: the normalized probability law of a nonzero finite intensity. -/
private noncomputable def normalizedFiniteMeasure
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) : ProbabilityMeasure E :=
  (finiteMeasureOfLtTop ν hνfin).normalize

/-- Helper for Theorem 24.12: a nonzero finite measure evaluates under normalization by dividing
by its total mass. -/
private theorem normalizedFiniteMeasure_apply
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) (hν_ne : ν ≠ 0) (A : Set E) :
    ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E) A =
      (ν Set.univ)⁻¹ * ν A := by
  have hfinite_ne : finiteMeasureOfLtTop ν hνfin ≠ 0 := by
    intro hzero
    apply hν_ne
    exact congrArg (fun ρ : FiniteMeasure E ↦ (ρ : Measure E)) hzero
  have hmass_ne : (finiteMeasureOfLtTop ν hνfin).mass ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff _).2 hfinite_ne
  have hnormalize :=
    (finiteMeasureOfLtTop ν hνfin).toMeasure_normalize_eq_of_nonzero hfinite_ne
  -- Proof comment: evaluate the normalized-measure identity on `A` and rewrite the finite-mass
  -- coercion back to the original measure.
  rw [normalizedFiniteMeasure]
  calc
    ((finiteMeasureOfLtTop ν hνfin).normalize : Measure E) A
        = (fun μ : Measure E ↦ μ A)
            ((finiteMeasureOfLtTop ν hνfin).mass⁻¹ • ↑(finiteMeasureOfLtTop ν hνfin)) := by
              exact congrArg (fun μ : Measure E ↦ μ A) hnormalize
    _ = ((((finiteMeasureOfLtTop ν hνfin).mass : NNReal) : ENNReal)⁻¹ *
          ((finiteMeasureOfLtTop ν hνfin : Measure E) A)) := by
          simpa [Measure.smul_apply, ENNReal.coe_inv hmass_ne]
    _ = ((((finiteMeasureOfLtTop ν hνfin).mass : NNReal) : ENNReal)⁻¹ * ν A) := by
          rfl
    _ = (ν Set.univ)⁻¹ * ν A := by
          have hmass :
              (((finiteMeasureOfLtTop ν hνfin).mass : NNReal) : ENNReal) = ν Set.univ := by
            simpa [finiteMeasureOfLtTop] using
              (FiniteMeasure.ennreal_mass (μ := finiteMeasureOfLtTop ν hνfin))
          have hmass_inv :
              ((((finiteMeasureOfLtTop ν hνfin).mass : NNReal) : ENNReal)⁻¹) =
                (ν Set.univ)⁻¹ := by
            rw [hmass]
          rw [hmass_inv]

/-- Helper for Theorem 24.12: the local finite-label map sends a point to the unique disjoint
cell containing it and to the outside label when no cell contains it. -/
private def disjointCellLabel
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E) (x : E) :
    Fin (d + 1) :=
  let _ : ∀ i : Fin d, Decidable (x ∈ As i) := Classical.decPred fun i : Fin d ↦ x ∈ As i
  if h : ∃ i, x ∈ As i then (Classical.choose h).castSucc else Fin.last d

/-- Helper for Theorem 24.12: points in a disjoint cell receive that cell's successor label. -/
private theorem disjointCellLabel_mem
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E)
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j))
    {x : E} {i : Fin d} (hx : x ∈ As i) :
    disjointCellLabel As x = i.castSucc := by
  classical
  have hex : ∃ j, x ∈ As j := ⟨i, hx⟩
  let j0 : Fin d := Classical.choose (p := fun j : Fin d ↦ x ∈ As j) hex
  have hchoose_mem : x ∈ As j0 :=
    Classical.choose_spec (p := fun j : Fin d ↦ x ∈ As j) hex
  have hchoose_eq : j0 = i := by
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj (i := j0) (j := i) hne)) hchoose_mem hx
  -- Proof comment: pairwise disjointness forces the chosen witness to be the given cell index.
  rw [disjointCellLabel, dif_pos hex]
  simpa [j0, hchoose_eq]

/-- Helper for Theorem 24.12: the disjoint-cell label map has the expected singleton fibers on
each cell and on the outside region. -/
private theorem disjointCellLabel_spec
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j)) :
    Measurable (disjointCellLabel As) ∧
      (∀ i, disjointCellLabel As ⁻¹' {i.castSucc} = As i) ∧
      disjointCellLabel As ⁻¹' {Fin.last d} = (⋃ i, As i)ᶜ := by
  classical
  have hsucc : ∀ i, disjointCellLabel As ⁻¹' {i.castSucc} = As i := by
    intro i
    ext x
    constructor
    · intro hx
      have hlabel : disjointCellLabel As x = i.castSucc := by
        simpa using hx
      by_cases hex : ∃ j, x ∈ As j
      · let j0 : Fin d := Classical.choose (p := fun j : Fin d ↦ x ∈ As j) hex
        have hchoose_eq : j0 = i := by
          apply Fin.castSucc_injective
          rw [disjointCellLabel, dif_pos hex] at hlabel
          simpa [j0] using hlabel
        simpa [j0, hchoose_eq] using
          (Classical.choose_spec (p := fun j : Fin d ↦ x ∈ As j) hex)
      · have hlast : disjointCellLabel As x = Fin.last d := by
          rw [disjointCellLabel, dif_neg hex]
        exact False.elim <| Fin.castSucc_ne_last i (hlabel.symm.trans hlast)
    · intro hx
      -- Proof comment: membership in `As i` lands in the `i.castSucc` fiber by the disjoint-cell
      -- selector definition.
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using
        disjointCellLabel_mem As hdisj hx
  have hlast :
      disjointCellLabel As ⁻¹' {Fin.last d} = (⋃ i, As i)ᶜ := by
    ext x
    constructor
    · intro hx
      have hlastx : disjointCellLabel As x = Fin.last d := by
        simpa using hx
      -- Proof comment: the outside label can occur only when `x` belongs to no cell.
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      intro i
      intro hxi
      have hlabel : disjointCellLabel As x = i.castSucc :=
        disjointCellLabel_mem As hdisj hxi
      exact Fin.castSucc_ne_last i (hlabel.symm.trans hlastx)
    · intro hx
      have hnone : ¬ ∃ i, x ∈ As i := by
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx
        exact fun h ↦ hx (Classical.choose h) (Classical.choose_spec h)
      -- Proof comment: if no cell contains `x`, the definition falls through to the outside
      -- label `Fin.last d`.
      simpa [disjointCellLabel, hnone]
  have hmeas : Measurable (disjointCellLabel As) := by
    -- Proof comment: on the finite codomain, measurability follows from measurable singleton
    -- fibers.
    refine measurable_to_countable' ?_
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · simpa [hsucc i] using hA i
    · simpa [hlast] using (MeasurableSet.iUnion hA).compl
  exact ⟨hmeas, hsucc, hlast⟩

/-- Helper for Theorem 24.12: the explicit marked one-point indicator vector is measurable once
the test sets are measurable. -/
private theorem measurable_markIndicatorVector
    {E : Type v} [MeasurableSpace E] {d : ℕ} (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i)) :
    Measurable (markIndicatorVector As) := by
  let indicatorTuple : E → Fin d → ℝ :=
    fun x i ↦ (As i).indicator (1 : E → ℝ) x
  have htuple : Measurable indicatorTuple := by
    exact measurable_pi_lambda _ fun i ↦
      (Measurable.indicator (f := fun _ : E ↦ (1 : ℝ)) measurable_const (hA i))
  -- Proof comment: each coordinate is the indicator of a measurable test set, and the Euclidean
  -- vector is assembled coordinatewise.
  simpa [markIndicatorVector, indicatorTuple] using
    (PiLp.volume_preserving_toLp (Fin d)).measurable.comp htuple

/-- Helper for Theorem 24.12: the canonical product law for a finite nonzero intensity combines a
Poisson count with an iid sequence of normalized marks. -/
private noncomputable def finiteIntensityBaseLaw
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) :
    ProbabilityMeasure (ℕ × (ℕ → E)) :=
  ⟨(poissonMeasure (ν Set.univ).toNNReal).prod
      (Measure.infinitePi fun _ : ℕ ↦
        ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)),
    inferInstance⟩

/-- Helper for Theorem 24.12: under the finite-intensity base law, the first coordinate has the
Poisson law with parameter `ν Set.univ`. -/
private theorem finiteIntensityBaseLaw_fst_hasLaw
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) :
    HasLaw Prod.fst (poissonMeasure (ν Set.univ).toNNReal)
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  -- Proof comment: the first projection of a product probability law recovers the Poisson count
  -- marginal.
  simpa [finiteIntensityBaseLaw] using
    (Measure.map_fst_prod
      (μ := poissonMeasure (ν Set.univ).toNNReal)
      (ν := Measure.infinitePi fun _ : ℕ ↦
        ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)))

/-- Helper for Theorem 24.12: under the finite-intensity base law, every mark coordinate has the
normalized finite-intensity law. -/
private theorem finiteIntensityBaseLaw_mark_hasLaw
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) (i : ℕ) :
    HasLaw (fun ω : ℕ × (ℕ → E) ↦ ω.2 i)
      ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  refine ⟨((measurable_pi_apply i).comp measurable_snd).aemeasurable, ?_⟩
  -- Proof comment: first project to the mark sequence, then evaluate the `i`-th coordinate in
  -- the infinite product of the normalized mark law.
  have hcomp :
      (fun ω : ℕ × (ℕ → E) ↦ ω.2 i) =
        (fun s : ℕ → E ↦ s i) ∘ Prod.snd := by
    rfl
  calc
    Measure.map (fun ω : ℕ × (ℕ → E) ↦ ω.2 i)
        (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E)))
        = Measure.map (fun s : ℕ → E ↦ s i)
            (Measure.map Prod.snd
              (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E)))) := by
              rw [hcomp, Measure.map_map (measurable_pi_apply i) measurable_snd]
    _ = Measure.map (fun s : ℕ → E ↦ s i)
          (Measure.infinitePi fun _ : ℕ ↦
            ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)) := by
            simpa [finiteIntensityBaseLaw] using
              (Measure.map_snd_prod
                (μ := poissonMeasure (ν Set.univ).toNNReal)
                (ν := Measure.infinitePi fun _ : ℕ ↦
                  ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)))
    _ = ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E) := by
          simpa using
            (measurePreserving_eval_infinitePi
              (fun _ : ℕ ↦
                ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E))
              i).map_eq

/-- Helper for Theorem 24.12: the Poisson count is independent of the full iid mark sequence
under the finite-intensity base law. -/
private theorem finiteIntensityBaseLaw_count_indep_marks
    {E : Type v} [Nonempty E] [MeasurableSpace E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) :
    IndepFun Prod.fst Prod.snd
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  -- Proof comment: the base law is literally the product of the Poisson count law and the iid
  -- mark-sequence law.
  simpa [finiteIntensityBaseLaw] using
    (ProbabilityTheory.indepFun_prod
      (μ := poissonMeasure (ν Set.univ).toNNReal)
      (ν := Measure.infinitePi fun _ : ℕ ↦
        ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E))
      measurable_id measurable_id)

/-- Helper for Theorem 24.12: the first `N ω` labels of a countable finite-label sequence form the
usual multinomial histogram. -/
private def poissonizedLabelCount
    {Ω : Type u} [MeasurableSpace Ω] {m : ℕ}
    (N : Ω → ℕ) (Y : ℕ → Ω → Fin (m + 1)) (ω : Ω) : Fin (m + 1) → ℕ :=
  Theorem535Local.multinomialCount
    (fun j : Fin (N ω) ↦ fun ω' ↦ Y (j + 1) ω') ω

/-- Helper for Theorem 24.12: once the random length is fixed, the random-prefix histogram is the
corresponding fixed-length multinomial count vector. -/
private theorem poissonizedLabelCount_eq_multinomialCount_of_length_eq
    {Ω : Type u} [MeasurableSpace Ω] {m n : ℕ}
    (N : Ω → ℕ) (Y : ℕ → Ω → Fin (m + 1)) {ω : Ω} (hNn : N ω = n) :
    poissonizedLabelCount N Y ω =
      Theorem535Local.multinomialCount
        (fun j : Fin n ↦ fun ω' ↦ Y (j + 1) ω') ω := by
  -- Proof comment: after substituting the realized length, both sides are definitionally the same
  -- fixed-prefix histogram.
  subst hNn
  rfl

/-- Helper for Theorem 24.12: the coordinates of the random-prefix histogram sum to the realized
prefix length. -/
private theorem sum_poissonizedLabelCount
    {Ω : Type u} [MeasurableSpace Ω] {m : ℕ}
    (N : Ω → ℕ) (Y : ℕ → Ω → Fin (m + 1)) (ω : Ω) :
    ∑ i, poissonizedLabelCount N Y ω i = N ω := by
  -- Proof comment: this is exactly the fixed-length multinomial-count sum identity applied at the
  -- random prefix length `N ω`.
  simpa [poissonizedLabelCount] using
    Theorem535Local.sum_multinomialCount
      (X := fun j : Fin (N ω) ↦ fun ω' ↦ Y (j + 1) ω') ω

/-- Helper for Theorem 24.12: the singleton event for the random-prefix histogram is the
intersection of the length event and the corresponding fixed-length multinomial-count event. -/
private theorem poissonizedLabelCount_preimage_singleton_eq_length_inter_multinomialCount
    {Ω : Type u} [MeasurableSpace Ω] {m : ℕ}
    (N : Ω → ℕ) (Y : ℕ → Ω → Fin (m + 1)) (k : Fin (m + 1) → ℕ) :
    poissonizedLabelCount N Y ⁻¹' {k} =
      {ω | N ω = ∑ i, k i} ∩
        {ω |
          Theorem535Local.multinomialCount
            (fun j : Fin (∑ i, k i) ↦ fun ω' ↦ Y (j + 1) ω') ω = k} := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    constructor
    · -- Proof comment: summing the histogram coordinates recovers the random prefix length.
      have hsum : ∑ i, poissonizedLabelCount N Y ω i = ∑ i, k i := by
        exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
      simpa [sum_poissonizedLabelCount (N := N) (Y := Y) ω] using hsum
    · have hNω : N ω = ∑ i, k i := by
        have hsum : ∑ i, poissonizedLabelCount N Y ω i = ∑ i, k i := by
          exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
        simpa [sum_poissonizedLabelCount (N := N) (Y := Y) ω] using hsum
      -- Proof comment: after fixing the length, the random-prefix histogram becomes the fixed
      -- multinomial count of the first `∑ i, k i` labels.
      simp only [Set.mem_setOf_eq]
      rw [← poissonizedLabelCount_eq_multinomialCount_of_length_eq
        (N := N) (Y := Y) hNω]
      exact hω
  · rintro ⟨hNω, hω⟩
    -- Proof comment: the fixed-length multinomial identity rewrites the target event back to the
    -- original random-prefix histogram event.
    simp only [Set.mem_setOf_eq] at hNω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [poissonizedLabelCount_eq_multinomialCount_of_length_eq (N := N) (Y := Y) hNω]
    exact hω

/-- Helper for Theorem 24.12: conditioning on the Poisson length identifies the singleton mass of
the random-prefix histogram with the textbook Poisson-times-multinomial expression. -/
private theorem poissonizedLabelCount_preimage_singleton_eq_multinomial_mul_poisson
    {Ω : Type u} [MeasurableSpace Ω] {m : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {α : NNReal} {N : Ω → ℕ} {Y : ℕ → Ω → Fin (m + 1)} {p : PMF (Fin (m + 1))}
    (hN : HasLaw N (poissonMeasure α) P)
    (hNY_indep : IndepFun N (fun ω ↦ fun n : ℕ ↦ Y (n + 1) ω) P)
    (hY_indep : iIndepFun (fun n ↦ Y (n + 1)) P)
    (hY_law : ∀ n, HasLaw (Y (n + 1)) p.toMeasure P)
    (k : Fin (m + 1) → ℕ) :
    P (poissonizedLabelCount N Y ⁻¹' {k}) =
      (poissonMeasure α) {∑ i, k i} *
        ((Nat.multinomial Finset.univ k : ENNReal) * ∏ i, p i ^ k i) := by
  let prefixY : Fin (∑ i, k i) → Ω → Fin (m + 1) :=
    fun j ↦ fun ω ↦ Y ((j : ℕ) + 1) ω
  let prefixMap : (ℕ → Fin (m + 1)) → Fin (∑ i, k i) → Fin (m + 1) :=
    fun y j ↦ y j
  let countMap : (Fin (∑ i, k i) → Fin (m + 1)) → Fin (m + 1) → ℕ :=
    fun y ↦ Theorem535Local.multinomialCount
      (fun j : Fin (∑ i, k i) ↦ fun _ : Fin (∑ i, k i) → Fin (m + 1) ↦ y j) y
  have hprefixMap_meas : Measurable prefixMap := by
    change Measurable (fun y : ℕ → Fin (m + 1) ↦ (fun j : Fin (∑ i, k i) ↦ y (j : ℕ)))
    refine measurable_pi_lambda (fun y : ℕ → Fin (m + 1) ↦
      (fun j : Fin (∑ i, k i) ↦ y (j : ℕ))) ?_
    intro j
    exact measurable_pi_apply (j : ℕ)
  let countFromSeq : (ℕ → Fin (m + 1)) → Fin (m + 1) → ℕ :=
    fun y ↦ countMap (prefixMap y)
  have h_indep_count :
      IndepFun N (fun ω ↦ Theorem535Local.multinomialCount prefixY ω) P := by
    -- Proof comment: the Poisson length is independent of every measurable function of the whole
    -- shifted mark sequence, in particular of the fixed-prefix histogram.
    have hcount_indep :
        IndepFun N (fun ω ↦ countFromSeq (fun n : ℕ ↦ Y (n + 1) ω)) P := by
      simpa [countFromSeq, prefixMap, countMap, Function.comp] using
        hNY_indep.comp measurable_id
          ((measurable_of_finite countMap).comp hprefixMap_meas)
    simpa [countFromSeq, prefixY, prefixMap, countMap] using hcount_indep
  have h_length_mass :
      P (N ⁻¹' ({∑ i, k i} : Set ℕ)) = (poissonMeasure α) {∑ i, k i} := by
    -- Proof comment: read the singleton length event directly from the Poisson law of `N`.
    rw [← Measure.map_apply_of_aemeasurable hN.aemeasurable (measurableSet_singleton _), hN.map_eq]
  have h_prefix_indep : iIndepFun prefixY P := by
    -- Proof comment: the fixed positive-index prefix inherits independence from the shifted iid
    -- family `n ↦ Y (n + 1)`.
    simpa [prefixY] using hY_indep.precomp Fin.val_injective
  have h_prefix_law : ∀ j, HasLaw (prefixY j) p.toMeasure P := by
    intro j
    simpa [prefixY] using hY_law j
  have h_count_mass :
      P ((fun ω ↦ Theorem535Local.multinomialCount prefixY ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) =
        (Nat.multinomial Finset.univ k : ENNReal) * ∏ i, p i ^ k i := by
    -- Proof comment: once the prefix length is fixed, the label histogram has the usual
    -- multinomial singleton mass.
    simpa [prefixY] using
      Theorem535Local.multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
        p prefixY h_prefix_indep h_prefix_law k rfl
  rw [poissonizedLabelCount_preimage_singleton_eq_length_inter_multinomialCount (N := N) (Y := Y) k]
  calc
    P ({ω | N ω = ∑ i, k i} ∩
        {ω | Theorem535Local.multinomialCount prefixY ω = k}) =
        P (N ⁻¹' ({∑ i, k i} : Set ℕ) ∩
          (fun ω ↦ Theorem535Local.multinomialCount prefixY ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) := by
          rfl
    _ = P (N ⁻¹' ({∑ i, k i} : Set ℕ)) *
          P ((fun ω ↦ Theorem535Local.multinomialCount prefixY ω) ⁻¹'
            ({k} : Set (Fin (m + 1) → ℕ))) := by
          exact h_indep_count.measure_inter_preimage_eq_mul
            ({∑ i, k i} : Set ℕ) ({k} : Set (Fin (m + 1) → ℕ))
            (measurableSet_singleton _) (measurableSet_singleton _)
    _ = (poissonMeasure α) {∑ i, k i} *
          ((Nat.multinomial Finset.univ k : ENNReal) * ∏ i, p i ^ k i) := by
          rw [h_length_mass, h_count_mass]

/-- Helper for Theorem 24.12: a Poisson number of iid finite labels has the product Poisson law on
its histogram vector. -/
private theorem poissonizedLabelCount_hasLawPiPoisson
    {Ω : Type u} [MeasurableSpace Ω] {m : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {α : NNReal} {N : Ω → ℕ} {Y : ℕ → Ω → Fin (m + 1)} {p : PMF (Fin (m + 1))}
    (hN : HasLaw N (poissonMeasure α) P)
    (hNY_indep : IndepFun N (fun ω ↦ fun n : ℕ ↦ Y (n + 1) ω) P)
    (hY_indep : iIndepFun (fun n ↦ Y (n + 1)) P)
    (hY_law : ∀ n, HasLaw (Y (n + 1)) p.toMeasure P) :
    HasLaw
      (poissonizedLabelCount N Y)
      (Measure.pi (fun i ↦ poissonMeasure (α * (p i).toNNReal))) P := by
  let f : Ω → Fin (m + 1) → ℕ := poissonizedLabelCount N Y
  have hnull : NullMeasurable f P := by
    refine measurable_to_countable' ?_
    intro k
    change NullMeasurableSet (f ⁻¹' {k}) P
    rw [show f ⁻¹' {k} = poissonizedLabelCount N Y ⁻¹' {k} by rfl]
    rw [poissonizedLabelCount_preimage_singleton_eq_length_inter_multinomialCount (N := N) (Y := Y) k]
    refine NullMeasurableSet.inter ?_ ?_
    · simpa [Set.preimage] using
        hN.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton (∑ i, k i))
    · let prefixTuple : Ω → Fin (∑ i, k i) → Fin (m + 1) :=
        fun ω j ↦ Y (j + 1) ω
      let countMap : (Fin (∑ i, k i) → Fin (m + 1)) → Fin (m + 1) → ℕ :=
        fun y ↦
          Theorem535Local.multinomialCount
            (fun j : Fin (∑ i, k i) ↦ fun y' : Fin (∑ i, k i) → Fin (m + 1) ↦ y' j) y
      have hprefix_aemeas : AEMeasurable prefixTuple P := by
        refine aemeasurable_pi_lambda _ ?_
        intro j
        simpa [prefixTuple] using (hY_law j).aemeasurable
      have hcount_aemeas : AEMeasurable (fun ω ↦ countMap (prefixTuple ω)) P := by
        exact (measurable_of_finite countMap).aemeasurable.comp_aemeasurable hprefix_aemeas
      simpa [prefixTuple, countMap, Set.preimage] using
        hcount_aemeas.nullMeasurableSet_preimage (measurableSet_singleton k)
  have hameas : AEMeasurable (poissonizedLabelCount N Y) P := by
    simpa [f] using hnull.aemeasurable
  refine ⟨hameas, ?_⟩
  refine Measure.ext_of_singleton
    (μ := P.map (poissonizedLabelCount N Y))
    (ν := Measure.pi (fun i ↦ poissonMeasure (α * (p i).toNNReal))) ?_
  intro k
  rw [Measure.map_apply_of_aemeasurable hameas (measurableSet_singleton k)]
  rw [poissonizedLabelCount_preimage_singleton_eq_multinomial_mul_poisson
    (hN := hN) (hNY_indep := hNY_indep) (hY_indep := hY_indep) (hY_law := hY_law)]
  rw [Measure.pi_singleton]
  exact poissonMultinomialMass_eq_prodPoissonMass (α := α) p k

/-- Helper for Theorem 24.12: the shifted mark-label sequence uses a dummy outside label at
index `0` and then records the disjoint-cell label of the `n`-th mark at index `n + 1`. -/
private def markedPrefixLabelSequence
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E) :
    ℕ → (ℕ × (ℕ → E)) → Fin (d + 1)
  | 0, _ => Fin.last d
  | n + 1, ω => disjointCellLabel As (ω.2 n)

/-- Helper for Theorem 24.12: every shifted mark-label coordinate is measurable once the
disjoint-cell label map is measurable. -/
private theorem measurable_markedPrefixLabelSequence
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j)) :
    ∀ n, Measurable (markedPrefixLabelSequence As n) := by
  intro n
  cases n with
  | zero =>
      -- Proof comment: the zeroth coordinate is the constant outside label.
      change Measurable (fun _ : ℕ × (ℕ → E) ↦ (Fin.last d : Fin (d + 1)))
      exact measurable_const
  | succ n =>
      have hlabel_meas : Measurable (disjointCellLabel As) :=
        (disjointCellLabel_spec As hA hdisj).1
      -- Proof comment: for positive indices, evaluate the `n`-th mark and then apply the
      -- measurable finite-label bridge.
      simpa [markedPrefixLabelSequence] using
        hlabel_meas.comp ((measurable_pi_apply n).comp measurable_snd)

/-- Helper for Theorem 24.12: every positive shifted label coordinate has the finite-label law
obtained by mapping the normalized intensity through the disjoint-cell label map. -/
private theorem markedPrefixLabelSequence_hasLaw
    {E : Type v} [Nonempty E] [MeasurableSpace E] {d : ℕ}
    (ν : Measure E) (hνfin : ν Set.univ < ∞) (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j))
    (n : ℕ) :
    HasLaw (markedPrefixLabelSequence As (n + 1))
      (Measure.map (disjointCellLabel As)
        (((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)))
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  have hlabel :
      HasLaw (disjointCellLabel As)
        (Measure.map (disjointCellLabel As)
          (((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)))
        (((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)) := by
    exact ⟨(disjointCellLabel_spec As hA hdisj).1.aemeasurable, rfl⟩
  -- Proof comment: transport the law of the `n`-th mark through the measurable finite-label map
  -- induced by the disjoint partition.
  simpa [markedPrefixLabelSequence, Function.comp] using
    hlabel.fun_comp (finiteIntensityBaseLaw_mark_hasLaw ν hνfin n)

/-- Helper for Theorem 24.12: the successor coordinates of the Poissonized histogram coincide
with the marked-prefix counting coordinates. -/
private theorem poissonizedLabelCount_castSucc_eq_markedPrefixCount
    {E : Type v} {d : ℕ} [MeasurableSpace E] (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j))
    (ω : ℕ × (ℕ → E)) (i : Fin d) :
    poissonizedLabelCount Prod.fst (markedPrefixLabelSequence As) ω i.castSucc =
      markedPrefixCount ω (As i) := by
  rw [poissonizedLabelCount, Theorem535Local.multinomialCount, markedPrefixCount]
  calc
    Finset.card
        (Finset.univ.filter
          fun j : Fin ω.1 ↦ markedPrefixLabelSequence As (j + 1) ω = i.castSucc)
        = ∑ j : Fin ω.1, if markedPrefixLabelSequence As (j + 1) ω = i.castSucc then 1 else 0 := by
            simpa using
              (Finset.sum_boole
                (fun j : Fin ω.1 ↦ markedPrefixLabelSequence As (j + 1) ω = i.castSucc)
                Finset.univ :
                  (∑ x ∈ Finset.univ,
                    if markedPrefixLabelSequence As (x + 1) ω = i.castSucc then (1 : ℕ) else 0) =
                    Finset.card
                      (Finset.univ.filter
                        fun x : Fin ω.1 ↦ markedPrefixLabelSequence As (x + 1) ω = i.castSucc)).symm
    _ = ∑ j ∈ Finset.range ω.1,
          if markedPrefixLabelSequence As (j + 1) ω = i.castSucc then 1 else 0 := by
            simpa using
              (Fin.sum_univ_eq_sum_range (n := ω.1)
                (fun j : ℕ ↦
                  if markedPrefixLabelSequence As (j + 1) ω = i.castSucc then (1 : ℕ) else 0))
    _ = ∑ j ∈ Finset.range ω.1, (As i).indicator (1 : E → ℕ) (ω.2 j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hmem :
              markedPrefixLabelSequence As (j + 1) ω = i.castSucc ↔ ω.2 j ∈ As i := by
            change disjointCellLabel As (ω.2 j) = i.castSucc ↔ ω.2 j ∈ As i
            change ω.2 j ∈ disjointCellLabel As ⁻¹' ({i.castSucc} : Set (Fin (d + 1))) ↔
              ω.2 j ∈ As i
            rw [(disjointCellLabel_spec As hA hdisj).2.1 i]
          by_cases hjA : ω.2 j ∈ As i
          · simp [Set.indicator, hmem, hjA]
          · simp [Set.indicator, hmem, hjA]

/-- Helper for Theorem 24.12: after splitting off the outside label from
`(Fin (d + 1) → ℕ)`, the second component is exactly the `Fin.castSucc` prefix. -/
private theorem piFinSuccAboveLast_snd_eq_castSuccNat {d : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℕ) (Fin.last d) =
      fun z : Fin (d + 1) → ℕ ↦ fun i : Fin d ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` reduces to `Fin.castSucc`, so the tail component
  -- is the full successor-coordinate prefix.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Theorem 24.12: projecting a finite product Poisson law to the successor coordinates
keeps exactly the corresponding successor product law. -/
private theorem poissonMeasurePi_map_castSucc
    {d : ℕ} (r : Fin (d + 1) → NNReal) :
    Measure.map (fun z : Fin (d + 1) → ℕ ↦ fun i : Fin d ↦ z i.castSucc)
      (Measure.pi fun i ↦ poissonMeasure (r i)) =
      Measure.pi fun i : Fin d ↦ poissonMeasure (r i.castSucc) := by
  have hsplit :
      (Measure.pi fun i ↦ poissonMeasure (r i)).map
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℕ) (Fin.last d)) =
        (poissonMeasure (r (Fin.last d))).prod
          (Measure.pi fun i : Fin d ↦ poissonMeasure (r ((Fin.last d).succAbove i))) := by
    -- Proof comment: `piFinSuccAbove` is the canonical last-coordinate split of the finite
    -- product law.
    simpa [Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove (fun i : Fin (d + 1) ↦ poissonMeasure (r i))
        (Fin.last d)).map_eq
  -- Proof comment: map through the canonical split, then forget the outside label by `Prod.snd`.
  calc
    Measure.map (fun z : Fin (d + 1) → ℕ ↦ fun i : Fin d ↦ z i.castSucc)
        (Measure.pi fun i ↦ poissonMeasure (r i))
        = Measure.map Prod.snd
            (Measure.map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℕ) (Fin.last d))
              (Measure.pi fun i ↦ poissonMeasure (r i))) := by
              rw [← piFinSuccAboveLast_snd_eq_castSuccNat,
                Measure.map_map measurable_snd
                  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℕ) (Fin.last d)).measurable]
    _ = Measure.map Prod.snd
          ((poissonMeasure (r (Fin.last d))).prod
            (Measure.pi fun i : Fin d ↦ poissonMeasure (r ((Fin.last d).succAbove i)))) := by
              rw [hsplit]
    _ = Measure.pi fun i : Fin d ↦ poissonMeasure (r ((Fin.last d).succAbove i)) := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.pi fun i : Fin d ↦ poissonMeasure (r i.castSucc) := by
          simp [Fin.succAbove_last]

/-- Helper for Theorem 24.12: a nonzero finite intensity already gives the disjoint increment law
for the marked-prefix model on the common sample space. -/
private theorem markedPrefixTuple_hasLawPiPoisson
    {E : Type v} [Nonempty E] [MeasurableSpace E] {d : ℕ}
    (ν : Measure E) (hνfin : ν Set.univ < ∞) (hν_ne : ν ≠ 0)
    (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j)) :
    HasLaw
      (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin d ↦ markedPrefixCount ω (As i))
      (Measure.pi fun i ↦ poissonMeasure ((ν (As i)).toNNReal))
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  let P : Measure (ℕ × (ℕ → E)) := finiteIntensityBaseLaw ν hνfin
  let hLabelMeas : Measurable (disjointCellLabel As) := (disjointCellLabel_spec As hA hdisj).1
  let pProb : ProbabilityMeasure (Fin (d + 1)) :=
    ProbabilityMeasure.map (normalizedFiniteMeasure ν hνfin) hLabelMeas.aemeasurable
  let p : PMF (Fin (d + 1)) := ((pProb : Measure (Fin (d + 1))).toPMF)
  let labelTail : (ℕ → E) → ℕ → Fin (d + 1) :=
    fun s n ↦ disjointCellLabel As (s n)
  have hMarksMeas : ∀ n, Measurable (fun ω : ℕ × (ℕ → E) ↦ ω.2 n) := by
    intro n
    exact (measurable_pi_apply n).comp measurable_snd
  have hMarksCoord :
      (fun n : ℕ ↦ Measure.map (fun ω : ℕ × (ℕ → E) ↦ ω.2 n) P) =
        fun _ : ℕ ↦ ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E) := by
    funext n
    exact (finiteIntensityBaseLaw_mark_hasLaw ν hνfin n).map_eq
  have hMarksIndep :
      iIndepFun (fun n : ℕ ↦ fun ω : ℕ × (ℕ → E) ↦ ω.2 n) P := by
    have hMarksMap :
        P.map (fun ω n ↦ ω.2 n) =
          Measure.infinitePi
            (fun _ : ℕ ↦ ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)) := by
      -- Proof comment: the mark sequence is literally the second coordinate of the base product
      -- law, so its joint law is the infinite product of the normalized intensity.
      simpa [P, finiteIntensityBaseLaw] using
        (Measure.map_snd_prod
          (μ := poissonMeasure (ν Set.univ).toNNReal)
          (ν := Measure.infinitePi
            (fun _ : ℕ ↦ ((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E))))
    refine (iIndepFun_iff_map_fun_eq_infinitePi_map hMarksMeas).2 ?_
    simpa [hMarksCoord] using hMarksMap
  have hLabelTailMeas : Measurable labelTail := by
    refine measurable_pi_lambda _ ?_
    intro n
    exact hLabelMeas.comp (measurable_pi_apply n)
  have hShiftedLabelIndep :
      iIndepFun (fun n : ℕ ↦ markedPrefixLabelSequence As (n + 1)) P := by
    -- Proof comment: the positive label coordinates are the iid mark coordinates composed with
    -- the measurable disjoint-cell selector.
    simpa [labelTail, markedPrefixLabelSequence] using
      hMarksIndep.comp (fun _ ↦ disjointCellLabel As) (fun _ ↦ hLabelMeas)
  have hCountLabelIndep :
      IndepFun Prod.fst (fun ω : ℕ × (ℕ → E) ↦ fun n : ℕ ↦ markedPrefixLabelSequence As (n + 1) ω)
        P := by
    -- Proof comment: the Poisson length is independent of the whole iid mark sequence, hence also
    -- of the shifted label sequence obtained from it by a measurable pointwise map.
    simpa [labelTail, markedPrefixLabelSequence, Function.comp] using
      (finiteIntensityBaseLaw_count_indep_marks ν hνfin).comp measurable_id hLabelTailMeas
  have hShiftedLabelLaw :
      ∀ n, HasLaw (markedPrefixLabelSequence As (n + 1)) p.toMeasure P := by
    intro n
    -- Proof comment: each positive label coordinate has the mapped normalized law, which is
    -- exactly `p.toMeasure` by the `toPMF` coercion.
    simpa [p, pProb, ProbabilityMeasure.map, Measure.toPMF_toMeasure] using
      markedPrefixLabelSequence_hasLaw ν hνfin As hA hdisj n
  have hFullLaw :
      HasLaw
        (poissonizedLabelCount Prod.fst (markedPrefixLabelSequence As))
        (Measure.pi fun i ↦ poissonMeasure ((ν Set.univ).toNNReal * (p i).toNNReal)) P := by
    -- Proof comment: the generic Poissonized-histogram theorem now applies directly to the finite
    -- label process generated by the disjoint-cell selector.
    exact poissonizedLabelCount_hasLawPiPoisson
      (hN := finiteIntensityBaseLaw_fst_hasLaw ν hνfin)
      (hNY_indep := hCountLabelIndep)
      (hY_indep := hShiftedLabelIndep)
      (hY_law := hShiftedLabelLaw)
  have hPrefixLaw :
      HasLaw
        (fun z : Fin (d + 1) → ℕ ↦ fun i : Fin d ↦ z i.castSucc)
        (Measure.pi
          fun i : Fin d ↦ poissonMeasure ((ν Set.univ).toNNReal * (p i.castSucc).toNNReal))
        (Measure.pi fun j ↦ poissonMeasure ((ν Set.univ).toNNReal * (p j).toNNReal)) := by
    refine ⟨(measurable_pi_lambda _ fun i : Fin d ↦ measurable_pi_apply i.castSucc).aemeasurable, ?_⟩
    -- Proof comment: forgetting the outside label is just the canonical successor-coordinate
    -- projection of the finite product law.
    simpa using
      poissonMeasurePi_map_castSucc
        (fun j : Fin (d + 1) ↦ (ν Set.univ).toNNReal * (p j).toNNReal)
  have hSuccLaw :
      HasLaw
        (fun ω : ℕ × (ℕ → E) ↦
          fun i : Fin d ↦ poissonizedLabelCount Prod.fst (markedPrefixLabelSequence As) ω i.castSucc)
        (Measure.pi
          fun i : Fin d ↦ poissonMeasure ((ν Set.univ).toNNReal * (p i.castSucc).toNNReal))
        P := by
    -- Proof comment: project the full histogram law to the genuine cell coordinates.
    simpa [Function.comp] using HasLaw.comp hPrefixLaw hFullLaw
  have hMassUniv_ne_zero : ν Set.univ ≠ 0 := by
    exact fun h0 ↦ hν_ne <| Measure.measure_univ_eq_zero.mp h0
  have hCellFinite : ∀ i : Fin d, ν (As i) < ∞ := by
    intro i
    exact lt_of_le_of_lt (measure_mono (by simp)) hνfin
  have hRate :
      (fun i : Fin d ↦ (ν Set.univ).toNNReal * (p i.castSucc).toNNReal) =
        fun i : Fin d ↦ (ν (As i)).toNNReal := by
    funext i
    have hLabelMass : p i.castSucc = (ν Set.univ)⁻¹ * ν (As i) := by
      calc
        p i.castSucc = ((pProb : Measure (Fin (d + 1))) : Measure (Fin (d + 1))) {i.castSucc} := by
            simp [p, Measure.toPMF_apply]
        _ = (((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E))
              (disjointCellLabel As ⁻¹' ({i.castSucc} : Set (Fin (d + 1)))) := by
              rw [ProbabilityMeasure.map_apply' (ν := normalizedFiniteMeasure ν hνfin)
                hLabelMeas.aemeasurable (measurableSet_singleton _)]
        _ = (((normalizedFiniteMeasure ν hνfin : ProbabilityMeasure E) : Measure E)) (As i) := by
              rw [(disjointCellLabel_spec As hA hdisj).2.1 i]
        _ = (ν Set.univ)⁻¹ * ν (As i) := by
              exact normalizedFiniteMeasure_apply ν hνfin hν_ne (As i)
    -- Proof comment: convert the left-hand side to the `toNNReal` of a single `ENNReal` product,
    -- then cancel the normalization factor before returning to `NNReal`.
    rw [← ENNReal.toNNReal_mul]
    simpa [hLabelMass, mul_assoc] using
      congrArg ENNReal.toNNReal
        (ENNReal.mul_inv_cancel_left (a := ν Set.univ) (b := ν (As i))
          hMassUniv_ne_zero hνfin.ne)
  have hMarkedEq :
      (fun ω : ℕ × (ℕ → E) ↦
        fun i : Fin d ↦ poissonizedLabelCount Prod.fst (markedPrefixLabelSequence As) ω i.castSucc)
        =ᵐ[P]
      (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin d ↦ markedPrefixCount ω (As i)) := by
    exact Filter.Eventually.of_forall fun ω ↦ funext fun i ↦
      poissonizedLabelCount_castSucc_eq_markedPrefixCount As hA hdisj ω i
  have hRateMeasure :
      Measure.pi
          (fun i : Fin d ↦ poissonMeasure ((ν Set.univ).toNNReal * (p i.castSucc).toNNReal)) =
        Measure.pi (fun i : Fin d ↦ poissonMeasure ((ν (As i)).toNNReal)) := by
    refine congrArg Measure.pi ?_
    funext i
    exact congrArg poissonMeasure (congrFun hRate i)
  -- Proof comment: replace the successor histogram coordinates by the actual marked-prefix counts,
  -- and rewrite the projected Poisson rates to the original cell masses.
  exact hRateMeasure ▸ (hSuccLaw.congr hMarkedEq.symm)

/-- Helper for Theorem 24.12: the finite-intensity marked-prefix tuple law remains valid without a
nonzero-intensity assumption, because the zero-intensity case collapses to the constant-zero
tuple. -/
private theorem markedPrefixTuple_hasLawPiPoisson_finite
    {E : Type v} [Nonempty E] [MeasurableSpace E] {d : ℕ}
    (ν : Measure E) (hνfin : ν Set.univ < ∞)
    (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j)) :
    HasLaw
      (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin d ↦ markedPrefixCount ω (As i))
      (Measure.pi fun i ↦ poissonMeasure ((ν (As i)).toNNReal))
      (finiteIntensityBaseLaw ν hνfin : Measure (ℕ × (ℕ → E))) := by
  by_cases hν_zero : ν = 0
  · let P : Measure (ℕ × (ℕ → E)) := finiteIntensityBaseLaw ν hνfin
    have hνuniv_zero : ν Set.univ = 0 := by
      exact Measure.measure_univ_eq_zero.mpr hν_zero
    have hfst_zero :
        HasLaw Prod.fst (poissonMeasure 0) P := by
      -- Proof comment: once the intensity is zero, the Poisson prefix length is almost surely
      -- zero under the base law.
      simpa [P, finiteIntensityBaseLaw, hνuniv_zero] using
        finiteIntensityBaseLaw_fst_hasLaw ν hνfin
    have hfst_zero_ae : ∀ᵐ ω ∂P, Prod.fst ω = 0 := by
      -- Proof comment: the zero-rate Poisson law is the Dirac mass at `0`, so the count
      -- coordinate vanishes almost surely.
      exact
        (hfst_zero.ae_iff
          (p := fun n : ℕ ↦ n = 0)
          (hp := measurable_id.eq measurable_const)).2 <|
          by simpa [poissonMeasureZeroEqDirac]
    have hcount_zero_ae :
        (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin d ↦ markedPrefixCount ω (As i)) =ᵐ[P]
          (fun _ : ℕ × (ℕ → E) ↦ fun _ : Fin d ↦ (0 : ℕ)) := by
      filter_upwards [hfst_zero_ae] with ω hω
      funext i
      -- Proof comment: with zero prefix length, every marked-prefix count is the empty sum.
      simp [markedPrefixCount, hω]
    have hzeroTuple :
        HasLaw
          (fun _ : ℕ ↦ fun _ : Fin d ↦ (0 : ℕ))
          (Measure.pi fun i : Fin d ↦ poissonMeasure 0)
          (poissonMeasure 0) := by
      refine ⟨by fun_prop, ?_⟩
      -- Proof comment: the constant-zero tuple is independent, and every coordinate has the
      -- zero-rate Poisson law.
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun _ : Fin d ↦ measurable_const.aemeasurable)).1
        (iIndepFun_const (P := poissonMeasure 0) (c := fun _ : Fin d ↦ (0 : ℕ)))]
      refine congrArg Measure.pi ?_
      funext i
      rw [Measure.map_const]
      simp [poissonMeasureZeroEqDirac]
    have hconstLaw :
        HasLaw
          (fun _ : ℕ × (ℕ → E) ↦ fun _ : Fin d ↦ (0 : ℕ))
          (Measure.pi fun i : Fin d ↦ poissonMeasure 0)
          P := by
      -- Proof comment: compose the constant-zero tuple law with the almost-surely zero Poisson
      -- prefix-length coordinate.
      simpa [Function.comp] using hzeroTuple.fun_comp hfst_zero
    have hrate_zero :
        (Measure.pi fun i : Fin d ↦ poissonMeasure ((ν (As i)).toNNReal)) =
          Measure.pi (fun i : Fin d ↦ poissonMeasure 0) := by
      refine congrArg Measure.pi ?_
      funext i
      have hAi_zero : ν (As i) = 0 := by
        rw [hν_zero]
        simp
      simp [hAi_zero]
    -- Proof comment: the actual count tuple agrees almost surely with the constant-zero tuple,
    -- and all target Poisson rates are zero.
    exact hrate_zero.symm ▸ hconstLaw.congr hcount_zero_ae
  · -- Proof comment: in the nonzero case, the already proved marked-prefix tuple law applies
    -- directly.
    exact markedPrefixTuple_hasLawPiPoisson ν hνfin hν_zero As hA hdisj

/-- Helper for Theorem 24.12: every finite intensity measure is realized on the common
marked-prefix sample space as a Poisson point process. -/
private theorem isPoissonPointProcess_markedPrefixOfFiniteMeasure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [Nonempty E]
    (ν : Measure E) (hνfin : ν Set.univ < ∞) :
    IsPoissonPointProcess ν (finiteIntensityBaseLaw ν hνfin)
      (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E)) := by
  let P : ProbabilityMeasure (ℕ × (ℕ → E)) := finiteIntensityBaseLaw ν hνfin
  refine
    (ProbabilityTheory.isPoissonPointProcess_iff
      ν P (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E))).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: the marked-prefix construction is already a boundedly finite random
    -- measure, and each sample value is boundedly finite and hence locally finite.
    refine ⟨markedPrefixPointMeasureMeasurable, ?_⟩
    exact Filter.Eventually.of_forall fun ω ↦ by
      letI :
          IsFiniteMeasureOnCompacts ((markedPrefixPointMeasure ω : BoundedlyFiniteMeasure E) :
            Measure E) := by
        refine ⟨fun K hK ↦ (markedPrefixPointMeasure ω).2 hK.measurableSet hK.isBounded⟩
      exact inferInstance
  · intro n As hA hdisj
    let tupleCount : (ℕ × (ℕ → E)) → Fin n → ℕ :=
      fun ω i ↦ markedPrefixCount ω (As i)
    let tupleEval : (ℕ × (ℕ → E)) → Fin n → ENNReal :=
      fun ω i ↦ (markedPrefixPointMeasure ω : Measure E) (As i)
    have hCountLaw :
        HasLaw tupleCount
          (Measure.pi fun i : Fin n ↦ poissonMeasure ((ν (As i)).toNNReal))
          (P : Measure (ℕ × (ℕ → E))) :=
      markedPrefixTuple_hasLawPiPoisson_finite ν hνfin As hA hdisj
    have hCastLaw :
        HasLaw
          (fun z : Fin n → ℕ ↦ fun i : Fin n ↦ (z i : ENNReal))
          (Measure.pi fun i : Fin n ↦
            Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)))
          (Measure.pi fun i : Fin n ↦ poissonMeasure ((ν (As i)).toNNReal)) := by
      have hNatCast : Measurable (fun k : ℕ ↦ (k : ENNReal)) :=
        show Measurable (fun k : ℕ ↦ (k : ENNReal)) from
          measurable_of_countable (f := fun k : ℕ ↦ (k : ENNReal))
      have hNatCastAe :
          ∀ i : Fin n, AEMeasurable (fun k : ℕ ↦ (k : ENNReal))
            (poissonMeasure ((ν (As i)).toNNReal)) := fun _ ↦ hNatCast.aemeasurable
      have hTupleCastMeas :
          AEMeasurable
            (fun z : Fin n → ℕ ↦ fun i : Fin n ↦ (z i : ENNReal))
            (Measure.pi fun i : Fin n ↦ poissonMeasure ((ν (As i)).toNNReal)) := by
        refine aemeasurable_pi_lambda _ ?_
        intro i
        exact hNatCast.aemeasurable.comp_aemeasurable (measurable_pi_apply i).aemeasurable
      refine ⟨hTupleCastMeas, ?_⟩
      -- Proof comment: coordinatewise casting from `ℕ` to `ENNReal` maps the product Poisson
      -- law to the corresponding product law of the evaluation counts.
      simpa using
        (Measure.pi_map_pi
          (μ := fun i : Fin n ↦ poissonMeasure ((ν (As i)).toNNReal))
          (f := fun _ : Fin n ↦ fun k : ℕ ↦ (k : ENNReal))
          hNatCastAe)
    have hEvalLaw :
        HasLaw tupleEval
          (Measure.pi fun i : Fin n ↦
            Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)))
          (P : Measure (ℕ × (ℕ → E))) := by
      have hCountCastLaw :
          HasLaw
            (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin n ↦ (tupleCount ω i : ENNReal))
            (Measure.pi fun i : Fin n ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)))
            (P : Measure (ℕ × (ℕ → E))) := by
        simpa [tupleCount, Function.comp] using hCastLaw.fun_comp hCountLaw
      have hEvalEq :
          tupleEval =ᵐ[(P : Measure (ℕ × (ℕ → E)))]
            (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin n ↦ (tupleCount ω i : ENNReal)) := by
        exact Filter.Eventually.of_forall fun ω ↦ funext fun i ↦
          markedPrefixCount_apply ω (hA i)
      -- Proof comment: after rewriting each coordinate evaluation as the `ENNReal` cast of the
      -- corresponding marked-prefix count, the tuple law becomes a product law immediately.
      exact hCountCastLaw.congr hEvalEq
    have hCoordMap :
        ∀ i : Fin n,
          (P : Measure (ℕ × (ℕ → E))).map (fun ω : ℕ × (ℕ → E) ↦ tupleEval ω i) =
            Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)) := by
      letI :
          ∀ i : Fin n,
            IsProbabilityMeasure
              (Measure.map (fun k : ℕ ↦ (k : ENNReal))
                (poissonMeasure ((ν (As i)).toNNReal))) := fun i ↦ by
                  let hNatCast : Measurable (fun k : ℕ ↦ (k : ENNReal)) :=
                    show Measurable (fun k : ℕ ↦ (k : ENNReal)) from
                      measurable_of_countable (f := fun k : ℕ ↦ (k : ENNReal))
                  exact Measure.isProbabilityMeasure_map hNatCast.aemeasurable
      intro i
      let πi : (Fin n → ENNReal) → ENNReal := fun z ↦ z i
      have hProjLaw :
          HasLaw πi
            (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)))
            (Measure.pi fun j : Fin n ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As j)).toNNReal))) := by
        refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
        simpa [πi] using
          (measurePreserving_eval
            (fun j : Fin n ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As j)).toNNReal)))
            i).map_eq
      have hCoordLaw :
          HasLaw (fun ω : ℕ × (ℕ → E) ↦ tupleEval ω i)
            (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)))
            (P : Measure (ℕ × (ℕ → E))) := by
        simpa [tupleEval, πi, Function.comp] using hProjLaw.fun_comp hEvalLaw
      exact hCoordLaw.map_eq
    have hTupleMap :
        (P : Measure (ℕ × (ℕ → E))).map (fun ω i ↦ tupleEval ω i) =
          Measure.pi fun i : Fin n ↦ (P : Measure (ℕ × (ℕ → E))).map (fun ω ↦ tupleEval ω i) := by
      calc
        (P : Measure (ℕ × (ℕ → E))).map (fun ω i ↦ tupleEval ω i)
            = Measure.pi fun i : Fin n ↦
                Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν (As i)).toNNReal)) := by
                  exact hEvalLaw.map_eq
        _ = Measure.pi fun i : Fin n ↦
              (P : Measure (ℕ × (ℕ → E))).map (fun ω ↦ tupleEval ω i) := by
              refine congrArg Measure.pi ?_
              funext i
              exact (hCoordMap i).symm
    -- Proof comment: for finite families, equality of the tuple law with the product law is
    -- exactly the `iIndepFun` criterion.
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n ↦
        ((Measure.measurable_coe (hA i)).comp markedPrefixPointMeasureMeasurable).aemeasurable)).2
      hTupleMap
  · -- Proof comment: a finite measure is locally finite on the ambient locally compact Polish
    -- space because it is finite on compacts.
    letI : IsFiniteMeasure ν := ⟨hνfin⟩
    infer_instance
  · intro A hA hA_bdd hA_finite
    let singleTuple : Fin 1 → Set E := fun _ ↦ A
    have hsingleDisj : Pairwise fun i j : Fin 1 ↦ Disjoint (singleTuple i) (singleTuple j) := by
      intro i j hij
      exact False.elim <| hij (Subsingleton.elim _ _)
    have hCountLaw :
        HasLaw
          (fun ω : ℕ × (ℕ → E) ↦ fun i : Fin 1 ↦ markedPrefixCount ω (singleTuple i))
          (Measure.pi fun i : Fin 1 ↦ poissonMeasure ((ν (singleTuple i)).toNNReal))
          (P : Measure (ℕ × (ℕ → E))) :=
      markedPrefixTuple_hasLawPiPoisson_finite ν hνfin singleTuple (fun _ ↦ hA) hsingleDisj
    let π0 : (Fin 1 → ℕ) → ℕ := fun z ↦ z 0
    have hProjLaw :
        HasLaw π0 (poissonMeasure ((ν A).toNNReal))
          (Measure.pi fun i : Fin 1 ↦ poissonMeasure ((ν (singleTuple i)).toNNReal)) := by
      refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
      simpa [π0, singleTuple] using
        (measurePreserving_eval
          (fun i : Fin 1 ↦ poissonMeasure ((ν (singleTuple i)).toNNReal)) 0).map_eq
    have hCountScalarLaw :
        HasLaw (fun ω : ℕ × (ℕ → E) ↦ markedPrefixCount ω A)
          (poissonMeasure ((ν A).toNNReal))
          (P : Measure (ℕ × (ℕ → E))) := by
      -- Proof comment: project the one-coordinate product law to the unique evaluation
      -- coordinate.
      simpa [π0, singleTuple, Function.comp] using hProjLaw.fun_comp hCountLaw
    have hCastLaw :
        HasLaw
          (fun k : ℕ ↦ (k : ENNReal))
          (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν A).toNNReal)))
          (poissonMeasure ((ν A).toNNReal)) := by
      have hNatCast : Measurable (fun k : ℕ ↦ (k : ENNReal)) :=
        show Measurable (fun k : ℕ ↦ (k : ENNReal)) from
          measurable_of_countable (f := fun k : ℕ ↦ (k : ENNReal))
      exact ⟨hNatCast.aemeasurable, rfl⟩
    have hEvalCastLaw :
        HasLaw
          (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixCount ω A : ENNReal))
          (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν A).toNNReal)))
          (P : Measure (ℕ × (ℕ → E))) := by
      simpa [Function.comp] using hCastLaw.fun_comp hCountScalarLaw
    have hEvalEq :
        (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E) A) =ᵐ[
            (P : Measure (ℕ × (ℕ → E)))]
          (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixCount ω A : ENNReal)) := by
      exact Filter.Eventually.of_forall fun ω ↦ markedPrefixCount_apply ω hA
    -- Proof comment: rewrite the measurable-set evaluation as the cast marked-prefix count and
    -- then read off the one-dimensional Poisson law.
    exact hEvalCastLaw.congr hEvalEq

/-- Helper for Theorem 24.12: on an empty ambient space the deterministic zero measure realizes
the unique Poisson point process law. -/
private theorem existsPoissonPointProcessWithIntensityMeasure_empty
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [IsEmpty E] (μ : BoundedlyFiniteMeasure E) :
    ∃ (Ω' : Type (max u v)) (_ : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω')
      (X : Ω' → Measure E), IsPoissonPointProcess (μ : Measure E) P' X := by
  let P' : ProbabilityMeasure (ULift.{max u v} PUnit) :=
    ⟨Measure.dirac (ULift.up PUnit.unit), inferInstance⟩
  let X : ULift.{max u v} PUnit → Measure E := fun _ ↦ 0
  have hμ_zero : (μ : Measure E) = 0 :=
    measure_eq_zero_of_isEmpty (μ := (μ : Measure E))
  refine ⟨ULift.{max u v} PUnit, inferInstance, P', X, ?_⟩
  refine (ProbabilityTheory.isPoissonPointProcess_iff (μ : Measure E) P' X).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: the zero-measure-valued map is measurable and locally finite everywhere.
    refine ⟨measurable_const, ?_⟩
    exact Filter.Eventually.of_forall fun _ ↦ by infer_instance
  · intro n A hA hdisj
    -- Proof comment: every increment of the deterministic zero process is the constant zero
    -- random variable, so the family is independent.
    simpa [X] using
      (iIndepFun_const
        (P := (P' : Measure (ULift.{max u v} PUnit)))
        (c := fun _ : Fin n ↦ (0 : ENNReal)))
  · -- Proof comment: the empty-space intensity measure is the zero measure.
    simpa [hμ_zero] using (inferInstance : IsLocallyFiniteMeasure (0 : Measure E))
  · intro A hA hA_bdd hA_finite
    -- Proof comment: every measurable-set evaluation is constantly zero, matching the zero-rate
    -- Poisson count law after the canonical `ℕ → ENNReal` transport.
    simpa [X, hμ_zero] using
      (hasLawZeroMappedPoissonZero
        (P := (P' : Measure (ULift.{max u v} PUnit))))

/-- Helper for Theorem 24.12: for zero intensity, the deterministic zero random measure is already
the desired Poisson point process. -/
private theorem existsPoissonPointProcessWithZeroIntensity
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] (ν : Measure E) (hν : ν = 0) :
    ∃ (Ω' : Type (max u v)) (_ : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω')
      (X : Ω' → Measure E), IsPoissonPointProcess ν P' X := by
  let P' : ProbabilityMeasure (ULift.{max u v} PUnit) :=
    ⟨Measure.dirac (ULift.up PUnit.unit), inferInstance⟩
  let X : ULift.{max u v} PUnit → Measure E := fun _ ↦ 0
  refine ⟨ULift.{max u v} PUnit, inferInstance, P', X, ?_⟩
  refine (ProbabilityTheory.isPoissonPointProcess_iff ν P' X).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: the zero-measure-valued map is measurable and locally finite everywhere.
    refine ⟨measurable_const, ?_⟩
    exact Filter.Eventually.of_forall fun _ ↦ by infer_instance
  · intro n A hA hdisj
    -- Proof comment: every increment of the deterministic zero process is constant, so the family
    -- of bounded evaluations is independent.
    simpa [X] using
      (iIndepFun_const
        (P := (P' : Measure (ULift.{max u v} PUnit)))
        (c := fun _ : Fin n ↦ (0 : ENNReal)))
  · -- Proof comment: the zero intensity measure is locally finite by the canonical zero instance.
    simpa [hν] using (inferInstance : IsLocallyFiniteMeasure (0 : Measure E))
  · intro A hA hA_bdd hA_finite
    -- Proof comment: each bounded measurable-set count is constantly zero, hence has the pushed
    -- forward zero-rate Poisson law.
    simpa [X, hν] using
      (hasLawZeroMappedPoissonZero
        (P := (P' : Measure (ULift.{max u v} PUnit))))

/-- Helper for Theorem 24.12: the `n`-th shell contributes the tuple of marked-prefix counts on
the disjoint test sets `As`. -/
private def shellTupleCount
    {Ω : Type u} {E : Type v} [MeasurableSpace E] {d : ℕ}
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E)) (As : Fin d → Set E) (n : ℕ) :
    Ω → Fin d → ℕ :=
  fun ω i ↦ markedPrefixCount (ΞNat n ω) (As i)

/-- Helper for Theorem 24.12: the first `N + 1` shells contribute the finite pointwise sum of
their tuple counts on the test sets `As`. -/
private def partialShellTupleCount
    {Ω : Type u} {E : Type v} [MeasurableSpace E] {d : ℕ}
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E)) (As : Fin d → Set E) (N : ℕ) :
    Ω → Fin d → ℕ :=
  fun ω i ↦ Finset.sum (Finset.range (N + 1)) fun n ↦ markedPrefixCount (ΞNat n ω) (As i)

/-- Helper for Theorem 24.12: the first `N + 1` shell rates add coordinatewise over the disjoint
test sets `As`. -/
private def partialShellRate
    {E : Type v} [MeasurableSpace E] {d : ℕ}
    (ν : ℕ → Measure E) (As : Fin d → Set E) (N : ℕ) :
    Fin d → NNReal :=
  fun i ↦ Finset.sum (Finset.range (N + 1)) fun n ↦ (ν n (As i)).toNNReal

/-- Helper for Theorem 24.12: each shell on the common Nat-indexed witness space already has the
expected finite product Poisson law on disjoint test sets. -/
private theorem shellTuple_hasLawPiPoisson_onNatFamily
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type v} [MeasurableSpace E] [Nonempty E]
    (ν : ℕ → Measure E) (hνfin : ∀ n, ν n Set.univ < ∞)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_law :
      ∀ n : ℕ,
        HasLaw (ΞNat n)
          (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) P)
    {d : ℕ} (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j))
    (n : ℕ) :
    HasLaw
      (shellTupleCount ΞNat As n)
      (Measure.pi fun i ↦ poissonMeasure ((ν n (As i)).toNNReal))
      P := by
  -- Proof comment: specialize the finite-intensity marked-prefix tuple law to the `n`-th shell
  -- and compose it with the selected shell coordinate on the common sample space.
  simpa [shellTupleCount, Function.comp] using
    (markedPrefixTuple_hasLawPiPoisson_finite (ν n) (hνfin n) As hA hdisj).fun_comp
      (hΞNat_law n)

/-- Helper for Theorem 24.12: the finite superposition of the first `N + 1` Nat-indexed shell
tuple counts already has the product Poisson law with the summed shell rates. -/
private theorem partialShellTuple_hasLawPiPoisson
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type v} [MeasurableSpace E] [Nonempty E]
    (ν : ℕ → Measure E) (hνfin : ∀ n, ν n Set.univ < ∞)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_meas : ∀ n : ℕ, Measurable (ΞNat n))
    (hΞNat_law :
      ∀ n : ℕ,
        HasLaw (ΞNat n)
          (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) P)
    (hΞNat_indep : iIndepFun ΞNat P)
    {d : ℕ} (As : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hdisj : Pairwise fun i j ↦ Disjoint (As i) (As j))
    (N : ℕ) :
    HasLaw
      (partialShellTupleCount ΞNat As N)
      (Measure.pi fun i ↦ poissonMeasure (partialShellRate ν As N i))
      P := by
  let shellTuple : ℕ → Ω → Fin d → ℕ := shellTupleCount ΞNat As
  have hShell_meas : ∀ n : ℕ, Measurable (shellTuple n) := by
    intro n
    -- Proof comment: measurability into the finite product is coordinatewise measurability.
    refine measurable_pi_iff.2 ?_
    intro i
    exact (measurable_markedPrefixCount (hA i)).comp (hΞNat_meas n)
  have hShell_law :
      ∀ n : ℕ,
        HasLaw (shellTuple n)
          (Measure.pi fun i ↦ poissonMeasure ((ν n (As i)).toNNReal))
          P := by
    intro n
    simpa [shellTuple] using
      shellTuple_hasLawPiPoisson_onNatFamily ν hνfin ΞNat hΞNat_law As hA hdisj n
  have hShell_indep : iIndepFun shellTuple P := by
    refine hΞNat_indep.comp
      (g := fun _ ω ↦ fun i : Fin d ↦ markedPrefixCount ω (As i)) ?_
    intro n
    -- Proof comment: independence is preserved under the common measurable shell-to-count-tuple
    -- map.
    refine measurable_pi_iff.2 ?_
    intro i
    exact measurable_markedPrefixCount (hA i)
  induction N with
  | zero =>
      -- Proof comment: with one shell there is nothing to add; this is the single-shell tuple law.
      simpa [partialShellTupleCount, partialShellRate, shellTuple, shellTupleCount] using
        hShell_law 0
  | succ N ih =>
      have hPartialTupleEq :
          partialShellTupleCount ΞNat As N =
            Finset.sum (Finset.range (N + 1)) shellTuple := by
        funext ω i
        simp [partialShellTupleCount, shellTuple, shellTupleCount]
      have hPrefixIndep :
          IndepFun
            (partialShellTupleCount ΞNat As N)
            (shellTuple (N + 1))
            P := by
        -- Proof comment: the already-summed prefix depends only on the first `N + 1` shells, so
        -- it stays independent of the next shell.
        rw [hPartialTupleEq]
        simpa [shellTuple, shellTupleCount] using
          hShell_indep.indepFun_finset_sum_of_notMem hShell_meas
            (i := N + 1) (s := Finset.range (N + 1)) Finset.notMem_range_self
      have hAddLaw :
          HasLaw
            (fun ω ↦ partialShellTupleCount ΞNat As N ω + shellTuple (N + 1) ω)
            (Measure.pi fun i ↦
              poissonMeasure (partialShellRate ν As N i + ((ν (N + 1) (As i)).toNNReal)))
            P := by
        -- Proof comment: the induction hypothesis gives the prefix law, the single-shell law gives
        -- the new summand law, and `hasLawPiPoisson_add` performs the Poisson superposition step.
        exact hasLawPiPoisson_add
          (Z := partialShellTupleCount ΞNat As N)
          (W := shellTuple (N + 1))
          (r := partialShellRate ν As N)
          (s := fun i ↦ ((ν (N + 1) (As i)).toNNReal))
          ih (hShell_law (N + 1)) hPrefixIndep
      have hPartialTupleSucc :
          partialShellTupleCount ΞNat As (N + 1) =
            fun ω ↦ partialShellTupleCount ΞNat As N ω + shellTuple (N + 1) ω := by
        funext ω i
        simp [partialShellTupleCount, shellTuple, shellTupleCount, Finset.sum_range_succ,
          add_comm, add_left_comm, add_assoc]
      have hPartialRateSucc :
          partialShellRate ν As (N + 1) =
            fun i ↦ partialShellRate ν As N i + ((ν (N + 1) (As i)).toNNReal) := by
        funext i
        simp [partialShellRate, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      -- Proof comment: rewrite the pointwise tuple addition and the rate sum in `range_succ`
      -- form to recover the claimed finite-shell law.
      simpa [hPartialTupleSucc, hPartialRateSucc]
        using hAddLaw

/-- Helper for Theorem 24.12: every shell process on the common Nat-indexed witness space is a
boundedly finite random measure. -/
private theorem shellProcess_isBoundedlyFiniteRandomMeasure
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E]
    (P : ProbabilityMeasure Ω)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_meas : ∀ n : ℕ, Measurable (ΞNat n))
    (n : ℕ) :
    IsBoundedlyFiniteRandomMeasure P
      (fun ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: shell-process measurability is just composition of the witness map with the
    -- measurable marked-prefix constructor.
    exact markedPrefixPointMeasureMeasurable.comp (hΞNat_meas n)
  · intro A hA hA_bdd
    -- Proof comment: each shell realization is already boundedly finite pointwise.
    exact Filter.Eventually.of_forall fun ω ↦
      (markedPrefixPointMeasure (ΞNat n ω)).2 hA hA_bdd

/-- Helper for Theorem 24.12: if one shell has zero intensity on a measurable bounded set, then
that shell contributes zero mass there almost surely. -/
private theorem shellProcess_eval_zero_ae_of_zeroRate
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [Nonempty E]
    (ν : ℕ → Measure E) (hνfin : ∀ n, ν n Set.univ < ∞)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_law :
      ∀ n : ℕ,
        HasLaw (ΞNat n)
          (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) P)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    {n : ℕ} (hZero : ν n A = 0) :
    ∀ᵐ ω ∂P, (markedPrefixPointMeasure (ΞNat n ω) : Measure E) A = 0 := by
  have hBaseEvalLaw :
      HasLaw
        (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E) A)
        (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure ((ν n A).toNNReal)))
        (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) := by
    have hPPP := isPoissonPointProcess_markedPrefixOfFiniteMeasure (ν n) (hνfin n)
    -- Proof comment: the finite-intensity shell constructor already gives the one-set Poisson law.
    exact
      ((ProbabilityTheory.isPoissonPointProcess_iff
          (ν n)
          (finiteIntensityBaseLaw (ν n) (hνfin n))
          (fun ω : ℕ × (ℕ → E) ↦ (markedPrefixPointMeasure ω : Measure E))).1 hPPP).2.2.2
        hA hA_bdd (by simpa [hZero])
  have hEvalLaw :
      HasLaw
        (fun ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E) A)
        (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure 0))
        P := by
    -- Proof comment: transport the shell evaluation law from the finite base space to the common
    -- witness space and rewrite the zero rate.
    simpa [Function.comp, hZero] using hBaseEvalLaw.fun_comp (hΞNat_law n)
  -- Proof comment: a zero-rate Poisson law is the Dirac mass at `0`, so the shell evaluation
  -- vanishes almost surely.
  exact
    (hEvalLaw.ae_iff
      (p := fun x : ENNReal ↦ x = 0)
      (hp := measurable_id.eq measurable_const)).2 <|
      by simpa [poissonMeasureZeroEqDirac]

/-- Helper for Theorem 24.12: once all shell rates beyond `N` vanish on `A`, the shell series
agrees almost surely with the finite shell prefix on that set. -/
private theorem shellSeries_apply_eq_partial_aeOnBounded
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [Nonempty E]
    (ν : ℕ → Measure E) (hνfin : ∀ n, ν n Set.univ < ∞)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_law :
      ∀ n : ℕ,
        HasLaw (ΞNat n)
          (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) P)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    {N : ℕ} (hTailZeroRate : ∀ n > N, ν n A = 0) :
    ∀ᵐ ω ∂P,
      weightedRandomMeasureSeries
          (fun _ ↦ 1)
          (fun n ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E))
          ω A =
        Finset.sum (Finset.range (N + 1))
          (fun n ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E) A) := by
  let shellProcess : ℕ → Ω → Measure E :=
    fun n ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E)
  let X : Ω → Measure E := weightedRandomMeasureSeries (fun _ ↦ 1) shellProcess
  have hTailZero :
      ∀ n > N, ∀ᵐ ω ∂P, shellProcess n ω A = 0 := by
    intro n hn
    -- Proof comment: every tail shell has zero intensity on `A`, so its evaluation is almost
    -- surely zero there.
    simpa [shellProcess] using
      shellProcess_eval_zero_ae_of_zeroRate ν hνfin ΞNat hΞNat_law hA hA_bdd
        (n := n) (hTailZeroRate n hn)
  have hTailAll :
      ∀ᵐ ω ∂P, ∀ n : ℕ, N < n → shellProcess n ω A = 0 := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N < n
    · filter_upwards [hTailZero n hn] with ω hω
      exact fun _ ↦ hω
    · exact Filter.Eventually.of_forall fun _ hn' ↦ False.elim (hn hn')
  filter_upwards [hTailAll] with ω hω
  rw [weightedRandomMeasureSeries_apply (weights := fun _ ↦ 1) (X := shellProcess) (ω := ω) hA]
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        (((fun _ ↦ (1 : NNReal)) n : NNReal) : ENNReal) * shellProcess n ω A = 0 := by
    intro n hn
    have hn_ge : N + 1 ≤ n := by
      simpa [Finset.mem_range] using hn
    have hn_gt : N < n := lt_of_lt_of_le (Nat.lt_succ_self N) hn_ge
    simpa using hω n hn_gt
  -- Proof comment: outside the first `N + 1` shells, every summand vanishes, so the series
  -- collapses to the finite prefix.
  rw [tsum_eq_sum (s := Finset.range (N + 1)) hzero]
  simp [shellProcess]

/-- Helper for Theorem 24.12: the shell series is a boundedly finite random measure once bounded
sets truncate to a finite shell prefix almost surely. -/
private theorem shellSeries_isBoundedlyFiniteRandomMeasure
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [Nonempty E]
    (P : ProbabilityMeasure Ω)
    (ν : ℕ → Measure E) (hνfin : ∀ n, ν n Set.univ < ∞)
    (ΞNat : ℕ → Ω → ℕ × (ℕ → E))
    (hΞNat_meas : ∀ n : ℕ, Measurable (ΞNat n))
    (hΞNat_law :
      ∀ n : ℕ,
        HasLaw (ΞNat n)
          (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E)))
          (P : Measure Ω))
    (hTailZeroRate :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        ∃ N : ℕ, ∀ n > N, ν n A = 0) :
    IsBoundedlyFiniteRandomMeasure P
      (weightedRandomMeasureSeries
        (fun _ ↦ 1)
        (fun n ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E))) := by
  let shellProcess : ℕ → Ω → Measure E :=
    fun n ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E)
  let X : Ω → Measure E := weightedRandomMeasureSeries (fun _ ↦ 1) shellProcess
  have hShellBF :
      ∀ n : ℕ, IsBoundedlyFiniteRandomMeasure P (shellProcess n) := by
    intro n
    simpa [shellProcess] using shellProcess_isBoundedlyFiniteRandomMeasure P ΞNat hΞNat_meas n
  refine
    (isBoundedlyFiniteRandomMeasure_weightedRandomMeasureSeries_iff_ae_lt_top_on_bounded
      P (fun _ ↦ 1) shellProcess hShellBF).2 ?_
  intro A hA hA_bdd
  obtain ⟨N, hTail⟩ := hTailZeroRate hA hA_bdd
  have hTrunc :
      ∀ᵐ ω ∂(P : Measure Ω),
        X ω A = Finset.sum (Finset.range (N + 1)) (fun n ↦ shellProcess n ω A) := by
    simpa [shellProcess, X] using
      shellSeries_apply_eq_partial_aeOnBounded ν hνfin ΞNat hΞNat_law hA hA_bdd hTail
  filter_upwards [hTrunc] with ω hω
  rw [hω]
  exact ENNReal.sum_lt_top.2 fun n _ ↦ (markedPrefixPointMeasure (ΞNat n ω)).2 hA hA_bdd

/-- Helper for Theorem 24.12: finiteness on the dense-sequence unit balls already implies local
finiteness of a measure on the ambient Polish space. -/
private theorem denseSeqUnitBallFinite_isLocallyFiniteMeasure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PolishSpace E] [Nonempty E]
    (μ : Measure E)
    (hμ :
      ∀ n, μ (Metric.ball (TopologicalSpace.denseSeq E n) 1) < ∞) :
    IsLocallyFiniteMeasure μ := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ :=
    Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq E) x (1 / 2 : ℝ) (by norm_num)
  refine ⟨Metric.ball (TopologicalSpace.denseSeq E n) 1, ?_, hμ n⟩
  have hxBall : x ∈ Metric.ball (TopologicalSpace.denseSeq E n) 1 := by
    rw [Metric.mem_ball]
    exact lt_trans hn (by norm_num)
  -- Proof comment: one dense-sequence ball of radius `1` contains `x`, so it gives a finite
  -- neighborhood.
  exact Metric.isOpen_ball.mem_nhds hxBall

/-- Helper for Theorem 24.12: almost-sure finiteness on the dense-sequence unit balls upgrades to
almost-sure local finiteness. -/
private theorem ae_isLocallyFiniteMeasure_of_denseSeqUnitBallFinite
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PolishSpace E] [Nonempty E]
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX :
      ∀ n, ∀ᵐ ω ∂(P : Measure Ω),
        X ω (Metric.ball (TopologicalSpace.denseSeq E n) 1) < ∞) :
    ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω) := by
  filter_upwards [ae_all_iff.2 hX] with ω hω
  exact denseSeqUnitBallFinite_isLocallyFiniteMeasure (μ := X ω) hω

/-- Helper for Theorem 24.12: for a finite `ENNReal`-valued family under a probability law,
factorization on all lower orthants already implies independence. -/
private theorem iIndepFun_of_jointIic_eq_prod
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Fin n → Ω → ENNReal)
    (hY : ∀ i, Measurable (Y i))
    (hIic :
      ∀ x : Fin n → ENNReal,
        P (⋂ i : Fin n, Y i ⁻¹' Set.Iic (x i)) =
          ∏ i : Fin n, P (Y i ⁻¹' Set.Iic (x i))) :
    iIndepFun Y P := by
  classical
  have hx :
      ∀ (J : Finset (Fin n)) (s : Fin n → Set Ω),
        (∀ i ∈ J, s i ∈ Set.preimage (Y i) '' Set.range (Set.Iic : ENNReal → Set ENNReal)) →
          ∀ i, i ∈ J → ∃ a : ENNReal, s i = Y i ⁻¹' Set.Iic a := by
    intro J s hs i hi
    rcases hs i hi with ⟨u, hu, hus⟩
    rcases hu with ⟨a, rfl⟩
    exact ⟨a, hus.symm⟩
  have hPreimage :
      iIndepSets
        (fun i : Fin n ↦ Set.preimage (Y i) '' Set.range (Set.Iic : ENNReal → Set ENNReal)) P := by
    rw [iIndepSets_iff]
    intro J s hs
    let x : Fin n → ENNReal := fun i ↦
      if hi : i ∈ J then
        Classical.choose (hx J s hs i hi)
      else ∞
    have hsx :
        ∀ i, i ∈ J → s i = Y i ⁻¹' Set.Iic (x i) := by
      intro i hi
      have hchoice : s i = Y i ⁻¹' Set.Iic (Classical.choose (hx J s hs i hi)) :=
        Classical.choose_spec (hx J s hs i hi)
      simpa [x, hi] using hchoice
    have hInter :
        (⋂ i ∈ J, s i) = ⋂ i : Fin n, Y i ⁻¹' Set.Iic (x i) := by
      ext ω
      constructor
      · intro hω
        have hω' : ∀ i, i ∈ J → ω ∈ s i := by
          simpa [Set.mem_iInter] using hω
        have : ∀ i : Fin n, ω ∈ Y i ⁻¹' Set.Iic (x i) := by
          intro i
          by_cases hi : i ∈ J
          · rw [← hsx i hi]
            exact hω' i hi
          · simp [x, hi]
        simpa [Set.mem_iInter] using this
      · intro hω
        have hω' : ∀ i : Fin n, ω ∈ Y i ⁻¹' Set.Iic (x i) := by
          simpa [Set.mem_iInter] using hω
        have : ∀ i, i ∈ J → ω ∈ s i := by
          intro i hi
          rw [hsx i hi]
          exact hω' i
        simpa [Set.mem_iInter] using this
    have hProd :
        (∏ i ∈ J, P (s i)) = ∏ i : Fin n, P (Y i ⁻¹' Set.Iic (x i)) := by
      calc
        ∏ i ∈ J, P (s i) = ∏ i ∈ J, P (Y i ⁻¹' Set.Iic (x i)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          rw [hsx i hi]
        _ = ∏ i : Fin n, P (Y i ⁻¹' Set.Iic (x i)) := by
          refine Finset.prod_subset (show J ⊆ Finset.univ by simp) ?_
          intro i _ hiJ
          have hUniv : Y i ⁻¹' Set.Iic (x i) = Set.univ := by
            simp [x, hiJ]
          simp [hUniv]
    -- Proof comment: on a finite index set, it is enough to encode a partial lower orthant by
    -- setting the unused coordinates to `∞`, whose lower interval is all of `ENNReal`.
    simpa [hInter, hProd] using hIic x
  -- Proof comment: the lower intervals form a generating π-system for `borel ENNReal`, so
  -- independence on those generators upgrades to full independence.
  exact
    iIndepFun_of_iIndepSets_preimage_generators
      P
      Y
      hY
      (fun _ : Fin n ↦ Set.range (Set.Iic : ENNReal → Set ENNReal))
      (fun _ ↦ isPiSystem_Iic)
      (fun _ ↦ by simpa using (borel_eq_generateFrom_Iic ENNReal).symm)
      hPreimage

/-- Helper for Theorem 24.12: the nonempty branch should follow the source-faithful route of a
finite-intensity marked construction plus a shell superposition argument. -/
private theorem existsPoissonPointProcessWithIntensityMeasure_nonempty
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] [Nonempty E] (μ : BoundedlyFiniteMeasure E) :
    ∃ (Ω' : Type (max u v)) (_ : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω')
      (X : Ω' → Measure E), IsPoissonPointProcess (μ : Measure E) P' X := by
  -- Route correction: the target theorem now lives in this file again. The remaining work is to
  -- execute the ambient `E` finite-measure constructor and then assemble the boundedly finite case
  -- by summing independent shell processes over closed-ball layers.
  by_cases hμ_zero : (μ : Measure E) = 0
  · -- Proof comment: the zero-intensity branch is already handled by the deterministic zero
    -- random measure, so the only genuine work is the positive finite-intensity/shell case.
    exact existsPoissonPointProcessWithZeroIntensity (ν := (μ : Measure E)) hμ_zero
  · let x0 : E := Classical.choice ‹Nonempty E›
    let ν : ℕ → Measure E := fun n ↦ (μ : Measure E).restrict (closedBallPiece x0 n)
    have hνfin : ∀ n : ℕ, ν n Set.univ < ∞ := fun n ↦
      closedBallPieceRestriction_lt_top μ x0 n
    obtain ⟨Ω', hΩ', P, Ξ, hΞ_meas, hΞ_law, hΞ_indep, hPprob⟩ :=
      ProbabilityTheory.exists_hasLaw_indepFun
        (ι := ULift.{u} ℕ)
        (𝓧 := fun _ : ULift.{u} ℕ ↦ ℕ × (ℕ → E))
        (μ := fun i : ULift.{u} ℕ ↦
          (finiteIntensityBaseLaw (ν i.down) (hνfin i.down) : Measure (ℕ × (ℕ → E))))
    let P' : ProbabilityMeasure Ω' := ⟨P, hPprob⟩
    let ΞNat : ℕ → Ω' → ℕ × (ℕ → E) := fun n ω ↦ Ξ (ULift.up n) ω
    have hΞNat_meas : ∀ n : ℕ, Measurable (ΞNat n) := by
      intro n
      simpa [ΞNat] using hΞ_meas (ULift.up n)
    have hΞNat_law :
        ∀ n : ℕ,
          HasLaw (ΞNat n)
            (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E))) P := by
      intro n
      simpa [ΞNat] using hΞ_law (ULift.up n)
    have hΞNat_indep : iIndepFun ΞNat P := by
      simpa [ΞNat] using hΞ_indep.precomp (g := ULift.up) ULift.up_injective
    have hPartialTupleLaw :
        ∀ {d : ℕ} (As : Fin d → Set E),
          (∀ i, MeasurableSet (As i)) →
          Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
          ∀ N : ℕ,
            HasLaw
              (partialShellTupleCount ΞNat As N)
              (Measure.pi fun i ↦ poissonMeasure (partialShellRate ν As N i))
              P := by
      intro d As hA hdisj N
      -- Proof comment: the repaired Nat-indexed shell family now feeds directly into the finite
      -- superposition lemma, with no sample-space transport left to manage.
      exact partialShellTuple_hasLawPiPoisson ν hνfin ΞNat hΞNat_meas hΞNat_law hΞNat_indep
        As hA hdisj N
    have hΞNat_law' :
        ∀ n : ℕ,
          HasLaw (ΞNat n)
            (finiteIntensityBaseLaw (ν n) (hνfin n) : Measure (ℕ × (ℕ → E)))
            (P' : Measure Ω') := by
      intro n
      simpa [P'] using hΞNat_law n
    let shellProcess : ℕ → Ω' → Measure E :=
      fun n ω ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E)
    let X : Ω' → Measure E := weightedRandomMeasureSeries (fun _ ↦ 1) shellProcess
    have hTailZeroRate :
        ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
          ∃ N : ℕ, ∀ n > N, ν n A = 0 := by
      intro A hA hA_bdd
      rcases bounded_subset_closedBall_nat hA_bdd x0 with ⟨N, hA_sub⟩
      refine ⟨N, ?_⟩
      intro n hn
      -- Proof comment: once `A` sits inside one closed ball, all later shell restrictions vanish
      -- on `A`.
      simpa [ν] using
        closedBallPiece_eventuallyZeroOnSubset (μ := (μ : Measure E)) hA hA_sub n hn
    have hX_bf : IsBoundedlyFiniteRandomMeasure P' X := by
      -- Proof comment: bounded sets only see finitely many shells almost surely, so the weighted
      -- shell series is boundedly finite.
      simpa [shellProcess, X] using
        shellSeries_isBoundedlyFiniteRandomMeasure
          P' ν hνfin ΞNat hΞNat_meas hΞNat_law' hTailZeroRate
    have hX_random : IsRandomMeasure P' X := by
      refine ⟨hX_bf.measurable, ?_⟩
      -- Proof comment: the boundedly finite shell series is finite on the countable dense-sequence
      -- unit balls almost surely, which is enough to recover local finiteness almost surely.
      exact
        ae_isLocallyFiniteMeasure_of_denseSeqUnitBallFinite
          (P := P') (X := X) fun n ↦
            hX_bf.ae_lt_top_apply
              (A := Metric.ball (TopologicalSpace.denseSeq E n) 1)
              Metric.isOpen_ball.measurableSet Metric.isBounded_ball
    have hμ_locfin : IsLocallyFiniteMeasure (μ : Measure E) := by
      letI : IsFiniteMeasureOnCompacts (μ : Measure E) :=
        ⟨fun K hK ↦ μ.lt_top_of_isBounded hK.measurableSet hK.isBounded⟩
      infer_instance
    have hBoundedTupleLaw :
        ∀ {d : ℕ} (As : Fin d → Set E),
          (∀ i, MeasurableSet (As i)) →
          (∀ i, Bornology.IsBounded (As i)) →
          Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
          HasLaw
            (fun ω : Ω' ↦ fun i : Fin d ↦ X ω (As i))
            (Measure.pi fun i : Fin d ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal))
                (poissonMeasure (((μ : Measure E) (As i)).toNNReal)))
            (P' : Measure Ω') := by
      intro d As hA hA_bdd hdisj
      have hUnion_bdd : Bornology.IsBounded (⋃ i ∈ Finset.univ, As i) := by
        exact (Bornology.isBounded_biUnion_finset (Finset.univ : Finset (Fin d))).2
          fun i _ ↦ hA_bdd i
      obtain ⟨N, hUnion_sub⟩ := bounded_subset_closedBall_nat hUnion_bdd x0
      have hAs_sub : ∀ i : Fin d, As i ⊆ Metric.closedBall x0 (N : ℝ) := by
        intro i x hx
        exact hUnion_sub <|
          Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, hx⟩⟩
      have hTupleEq :
          (fun ω : Ω' ↦ fun i : Fin d ↦ X ω (As i)) =ᵐ[(P' : Measure Ω')]
            (fun ω : Ω' ↦ fun i : Fin d ↦ (partialShellTupleCount ΞNat As N ω i : ENNReal)) := by
        have hCoordEq :
            ∀ i : Fin d,
              ∀ᵐ ω ∂(P' : Measure Ω'),
                X ω (As i) = (partialShellTupleCount ΞNat As N ω i : ENNReal) := by
          intro i
          have hTail :
              ∀ n > N, ν n (As i) = 0 := by
            intro n hn
            -- Proof comment: once `As i` lies in the first `N + 1` shells, every later shell
            -- restriction vanishes on that cell.
            simpa [ν] using
              closedBallPiece_eventuallyZeroOnSubset
                (μ := (μ : Measure E))
                (A := As i)
                (hA i)
                (hAs_sub i)
                n hn
          have hPartial :
              ∀ᵐ ω ∂(P' : Measure Ω'),
                X ω (As i) =
                  Finset.sum (Finset.range (N + 1))
                    (fun n ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E) (As i)) := by
            -- Proof comment: on a bounded cell, the full shell series truncates almost surely to
            -- the common finite shell prefix.
            simpa [P', shellProcess, X] using
              shellSeries_apply_eq_partial_aeOnBounded
                ν hνfin ΞNat hΞNat_law' (A := As i) (hA i) (hA_bdd i) hTail
          filter_upwards [hPartial] with ω hω
          calc
            X ω (As i)
                = Finset.sum (Finset.range (N + 1))
                    (fun n ↦ (markedPrefixPointMeasure (ΞNat n ω) : Measure E) (As i)) := hω
            _ = Finset.sum (Finset.range (N + 1))
                  (fun n ↦ ((markedPrefixCount (ΞNat n ω) (As i) : ℕ) : ENNReal)) := by
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    exact markedPrefixCount_apply (ΞNat n ω) (hA i)
            _ = (∑ n ∈ Finset.range (N + 1), markedPrefixCount (ΞNat n ω) (As i) : ℕ) := by
                  rw [Nat.cast_sum]
            _ = (partialShellTupleCount ΞNat As N ω i : ENNReal) := by
                  simp [partialShellTupleCount]
        have hAll :
            ∀ᵐ ω ∂(P' : Measure Ω'),
              ∀ i : Fin d, X ω (As i) = (partialShellTupleCount ΞNat As N ω i : ENNReal) := by
          rw [ae_all_iff]
          intro i
          exact hCoordEq i
        exact hAll.mono fun ω hω ↦ funext hω
      have hRateEq :
          partialShellRate ν As N = fun i : Fin d ↦ ((μ : Measure E) (As i)).toNNReal := by
        funext i
        have hMassEq :
            (μ : Measure E) (As i) =
              Finset.sum (Finset.range (N + 1)) fun n ↦ ν n (As i) := by
          simpa [ν] using
            closedBallPiece_prefix_sum_eq
              (μ := (μ : Measure E))
              x0
              (A := As i)
              (hA i)
              (N := N)
              (hAs_sub i)
        have hFiniteTerms :
            ∀ n ∈ Finset.range (N + 1), ν n (As i) ≠ ∞ := by
          intro n hn
          exact (lt_of_le_of_lt (measure_mono (by simp)) (hνfin n)).ne
        -- Proof comment: on a bounded cell, the shell rates add up to the original mass because
        -- the corrected shell partition covers the whole set inside the common closed ball.
        calc
          partialShellRate ν As N i
              = (Finset.sum (Finset.range (N + 1)) fun n ↦ ν n (As i)).toNNReal := by
                  simp [partialShellRate, ENNReal.toNNReal_sum hFiniteTerms]
          _ = ((μ : Measure E) (As i)).toNNReal := by
                simpa [hMassEq]
      have hCountLaw :
          HasLaw
            (partialShellTupleCount ΞNat As N)
            (Measure.pi fun i : Fin d ↦ poissonMeasure (((μ : Measure E) (As i)).toNNReal))
            (P' : Measure Ω') := by
        have hRaw :
            HasLaw
              (partialShellTupleCount ΞNat As N)
              (Measure.pi fun i : Fin d ↦ poissonMeasure (partialShellRate ν As N i))
              (P' : Measure Ω') := by
          simpa [P'] using hPartialTupleLaw As hA hdisj N
        have hRateMeasure :
            (Measure.pi fun i : Fin d ↦ poissonMeasure (partialShellRate ν As N i)) =
              Measure.pi fun i : Fin d ↦ poissonMeasure (((μ : Measure E) (As i)).toNNReal) := by
          refine congrArg Measure.pi ?_
          funext i
          exact congrArg poissonMeasure (congrFun hRateEq i)
        exact hRateMeasure ▸ hRaw
      have hCastLaw :
          HasLaw
            (fun z : Fin d → ℕ ↦ fun i : Fin d ↦ (z i : ENNReal))
            (Measure.pi fun i : Fin d ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal))
                (poissonMeasure (((μ : Measure E) (As i)).toNNReal)))
            (Measure.pi fun i : Fin d ↦ poissonMeasure (((μ : Measure E) (As i)).toNNReal)) := by
        have hNatCast : Measurable (fun k : ℕ ↦ (k : ENNReal)) :=
          show Measurable (fun k : ℕ ↦ (k : ENNReal)) from
            measurable_of_countable (f := fun k : ℕ ↦ (k : ENNReal))
        have hTupleCastMeas :
            AEMeasurable
              (fun z : Fin d → ℕ ↦ fun i : Fin d ↦ (z i : ENNReal))
              (Measure.pi fun i : Fin d ↦ poissonMeasure (((μ : Measure E) (As i)).toNNReal)) := by
          refine aemeasurable_pi_lambda _ ?_
          intro i
          exact hNatCast.aemeasurable.comp_aemeasurable (measurable_pi_apply i).aemeasurable
        refine ⟨hTupleCastMeas, ?_⟩
        -- Proof comment: coordinatewise casting from `ℕ` to `ENNReal` transports the product
        -- Poisson law to the evaluation-law surface used in Definition 24.10.
        simpa using
          (Measure.pi_map_pi
            (μ := fun i : Fin d ↦ poissonMeasure (((μ : Measure E) (As i)).toNNReal))
            (f := fun _ : Fin d ↦ fun k : ℕ ↦ (k : ENNReal))
            (fun _ : Fin d ↦ hNatCast.aemeasurable))
      have hEvalCastLaw :
          HasLaw
            (fun ω : Ω' ↦ fun i : Fin d ↦ (partialShellTupleCount ΞNat As N ω i : ENNReal))
            (Measure.pi fun i : Fin d ↦
              Measure.map (fun k : ℕ ↦ (k : ENNReal))
                (poissonMeasure (((μ : Measure E) (As i)).toNNReal)))
            (P' : Measure Ω') := by
        simpa [Function.comp] using hCastLaw.fun_comp hCountLaw
      -- Proof comment: rewrite the bounded shell-series tuple as the common finite shell prefix,
      -- then transport the finite-shell Nat-valued product law through the canonical cast.
      exact hEvalCastLaw.congr hTupleEq
    refine ⟨Ω', hΩ', P', X, ?_⟩
    refine (ProbabilityTheory.isPoissonPointProcess_iff (μ : Measure E) P' X).2 ?_
    refine ⟨hX_random, ?_, hμ_locfin, ?_⟩
    · -- TODO: the bounded-set truncation/random-measure part is now established. The remaining
      -- blocker is to convert the shell tuple laws into independent increments for the full shell
      -- series on arbitrary measurable disjoint families.
      intro n A hA hdisj
      let trunc : ℕ → Fin n → Set E := fun N i ↦ A i ∩ Metric.closedBall x0 (N : ℝ)
      have hTruncMeas : ∀ N : ℕ, ∀ i : Fin n, MeasurableSet (trunc N i) := by
        intro N i
        exact (hA i).inter measurableSet_closedBall
      have hTruncBounded : ∀ N : ℕ, ∀ i : Fin n, Bornology.IsBounded (trunc N i) := by
        intro N i
        exact Metric.isBounded_closedBall.subset Set.inter_subset_right
      have hTruncDisj :
          ∀ N : ℕ, Pairwise (fun i j : Fin n ↦ Disjoint (trunc N i) (trunc N j)) := by
        intro N i j hij
        exact (hdisj hij).mono_left Set.inter_subset_left |>.mono_right Set.inter_subset_left
      have hBoundedIndependent :
          ∀ {d : ℕ} (As : Fin d → Set E),
            (∀ i, MeasurableSet (As i)) →
            (∀ i, Bornology.IsBounded (As i)) →
            Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
            iIndepFun (fun i ω ↦ X ω (As i)) (P' : Measure Ω') := by
        intro d As hAs hAs_bdd hAs_disj
        let marginalLaw : Fin d → Measure ENNReal := fun i ↦
          Measure.map (fun k : ℕ ↦ (k : ENNReal))
            (poissonMeasure (((μ : Measure E) (As i)).toNNReal))
        have hTupleLaw :
            HasLaw
              (fun ω : Ω' ↦ fun i : Fin d ↦ X ω (As i))
              (Measure.pi marginalLaw)
              (P' : Measure Ω') := by
          -- Proof comment: the bounded tuple law already packages the full product law on the
          -- finite disjoint family `As`.
          simpa [marginalLaw] using hBoundedTupleLaw As hAs hAs_bdd hAs_disj
        have hCoordMap :
            ∀ i : Fin d,
              (P' : Measure Ω').map (fun ω ↦ X ω (As i)) = marginalLaw i := by
          intro i
          let πi : (Fin d → ENNReal) → ENNReal := fun z ↦ z i
          letI : ∀ i : Fin d, IsProbabilityMeasure (marginalLaw i) := by
            intro i
            let hNatCast : Measurable (fun k : ℕ ↦ (k : ENNReal)) :=
              show Measurable (fun k : ℕ ↦ (k : ENNReal)) from
                measurable_of_countable (f := fun k : ℕ ↦ (k : ENNReal))
            exact Measure.isProbabilityMeasure_map hNatCast.aemeasurable
          have hProjLaw :
              HasLaw πi (marginalLaw i) (Measure.pi marginalLaw) := by
            refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
            simpa [πi] using (measurePreserving_eval marginalLaw i).map_eq
          have hCoordLaw :
              HasLaw (fun ω : Ω' ↦ X ω (As i)) (marginalLaw i) (P' : Measure Ω') := by
            simpa [πi, Function.comp] using hProjLaw.fun_comp hTupleLaw
          exact hCoordLaw.map_eq
        have hTupleMap :
            (P' : Measure Ω').map (fun ω i ↦ X ω (As i)) =
              Measure.pi fun i : Fin d ↦
                (P' : Measure Ω').map (fun ω ↦ X ω (As i)) := by
          calc
            (P' : Measure Ω').map (fun ω i ↦ X ω (As i))
                = Measure.pi marginalLaw := by
                    exact hTupleLaw.map_eq
            _ = Measure.pi fun i : Fin d ↦
                  (P' : Measure Ω').map (fun ω ↦ X ω (As i)) := by
                    refine congrArg Measure.pi ?_
                    funext i
                    exact (hCoordMap i).symm
        -- Proof comment: equality of the tuple law with the product of its coordinate marginals
        -- is exactly the finite-dimensional independence criterion.
        exact
          (iIndepFun_iff_map_fun_eq_pi_map
            (fun i : Fin d ↦
              ((Measure.measurable_coe (hAs i)).comp hX_random.measurable).aemeasurable)).2
            hTupleMap
      have hTruncIndependent :
          ∀ N : ℕ, iIndepFun (fun i ω ↦ X ω (trunc N i)) (P' : Measure Ω') := by
        intro N
        exact hBoundedIndependent (trunc N) (hTruncMeas N) (hTruncBounded N) (hTruncDisj N)
      have hTruncMono : ∀ i : Fin n, Monotone fun N : ℕ ↦ trunc N i := by
        intro i N M hNM x hx
        refine ⟨hx.1, ?_⟩
        exact Metric.closedBall_subset_closedBall (by exact_mod_cast hNM) hx.2
      have hCoordEventEq :
          ∀ i : Fin n, ∀ x : Fin n → ENNReal,
            {ω : Ω' | X ω (A i) ≤ x i} = ⋂ N : ℕ, {ω : Ω' | X ω (trunc N i) ≤ x i} := by
        intro i x
        ext ω
        constructor
        · intro hω
          refine Set.mem_iInter.2 ?_
          intro N
          exact le_trans (measure_mono (Set.inter_subset_left : trunc N i ⊆ A i)) hω
        · intro hω
          have hEval :
              X ω (A i) = ⨆ N : ℕ, X ω (trunc N i) := by
            calc
              X ω (A i) = X ω (⋃ N : ℕ, trunc N i) := by
                rw [Metric.iUnion_inter_closedBall_nat (A i) x0]
              _ = ⨆ N : ℕ, X ω (trunc N i) := by
                exact (hTruncMono i).measure_iUnion
          change X ω (A i) ≤ x i
          rw [hEval]
          exact iSup_le fun N ↦ Set.mem_iInter.mp hω N
      have hJointEventEq :
          ∀ x : Fin n → ENNReal,
            (⋂ i : Fin n, {ω : Ω' | X ω (A i) ≤ x i}) =
              ⋂ N : ℕ, ⋂ i : Fin n, {ω : Ω' | X ω (trunc N i) ≤ x i} := by
        intro x
        ext ω
        constructor
        · intro hω
          refine Set.mem_iInter.2 ?_
          intro N
          refine Set.mem_iInter.2 ?_
          intro i
          exact le_trans (measure_mono (Set.inter_subset_left : trunc N i ⊆ A i))
            (Set.mem_iInter.mp hω i)
        · intro hω
          refine Set.mem_iInter.2 ?_
          intro i
          rw [hCoordEventEq i x]
          refine Set.mem_iInter.2 ?_
          intro N
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hω N) i
      have hTruncLowerOrthant :
          ∀ N : ℕ, ∀ x : Fin n → ENNReal,
            (P' : Measure Ω') (⋂ i : Fin n, {ω : Ω' | X ω (trunc N i) ≤ x i}) =
              ∏ i : Fin n, (P' : Measure Ω') {ω : Ω' | X ω (trunc N i) ≤ x i} := by
        intro N x
        simpa using
          (hTruncIndependent N).measure_inter_preimage_eq_mul
            (Finset.univ : Finset (Fin n))
            (sets := fun i : Fin n ↦ Set.Iic (x i))
            (fun i _ ↦ measurableSet_Iic)
      have hCoordLimit :
          ∀ i : Fin n, ∀ x : Fin n → ENNReal,
            Filter.Tendsto
              (fun N : ℕ ↦ (P' : Measure Ω') {ω : Ω' | X ω (trunc N i) ≤ x i})
              Filter.atTop
              (nhds ((P' : Measure Ω') {ω : Ω' | X ω (A i) ≤ x i})) := by
        intro i x
        rw [hCoordEventEq i x]
        refine tendsto_measure_iInter_atTop ?_ ?_ ?_
        · intro N
          exact
            (((Measure.measurable_coe (hTruncMeas N i)).comp hX_random.measurable)
              measurableSet_Iic).nullMeasurableSet
        · intro N M hNM ω hω
          exact le_trans (measure_mono (hTruncMono i hNM)) hω
        · exact ⟨0, measure_ne_top (P' : Measure Ω') _⟩
      have hJointLimit :
          ∀ x : Fin n → ENNReal,
            Filter.Tendsto
              (fun N : ℕ ↦
                (P' : Measure Ω') (⋂ i : Fin n, {ω : Ω' | X ω (trunc N i) ≤ x i}))
              Filter.atTop
              (nhds ((P' : Measure Ω') (⋂ i : Fin n, {ω : Ω' | X ω (A i) ≤ x i}))) := by
        intro x
        rw [hJointEventEq x]
        refine tendsto_measure_iInter_atTop ?_ ?_ ?_
        · intro N
          exact
            (MeasurableSet.iInter fun i : Fin n ↦
              ((Measure.measurable_coe (hTruncMeas N i)).comp hX_random.measurable)
                measurableSet_Iic).nullMeasurableSet
        · intro N M hNM ω hω
          refine Set.mem_iInter.2 ?_
          intro i
          exact le_trans (measure_mono (hTruncMono i hNM)) (Set.mem_iInter.mp hω i)
        · exact ⟨0, measure_ne_top (P' : Measure Ω') _⟩
      have hProductLimit :
          ∀ x : Fin n → ENNReal,
            Filter.Tendsto
              (fun N : ℕ ↦
                ∏ i : Fin n, (P' : Measure Ω') {ω : Ω' | X ω (trunc N i) ≤ x i})
              Filter.atTop
              (nhds (∏ i : Fin n, (P' : Measure Ω') {ω : Ω' | X ω (A i) ≤ x i})) := by
        intro x
        exact
          ENNReal.tendsto_finset_prod_of_ne_top
            Finset.univ
            (fun i _ ↦ hCoordLimit i x)
            (fun i _ ↦ measure_ne_top (P' : Measure Ω') _)
      have hLowerOrthant :
          ∀ x : Fin n → ENNReal,
            (P' : Measure Ω') (⋂ i : Fin n, {ω : Ω' | X ω (A i) ≤ x i}) =
              ∏ i : Fin n, (P' : Measure Ω') {ω : Ω' | X ω (A i) ≤ x i} := by
        intro x
        refine tendsto_nhds_unique (hJointLimit x) ?_
        exact
          (hProductLimit x).congr'
            (Filter.Eventually.of_forall fun N ↦ (hTruncLowerOrthant N x).symm)
      -- Proof comment: the bounded truncations are independent, and continuity from above on the
      -- lower-orthant events transfers that factorization to the full unbounded family.
      exact
        iIndepFun_of_jointIic_eq_prod
          (P := (P' : Measure Ω'))
          (Y := fun i ω ↦ X ω (A i))
          (fun i ↦ (Measure.measurable_coe (hA i)).comp hX_random.measurable)
          hLowerOrthant
    · -- TODO: after the bounded truncation rewrite is in place, the bounded scalar Poisson law
      -- should follow from the `Fin 1` shell tuple law and `closedBallPiece_prefix_sum_eq`.
      intro A hA hA_bdd hA_finite
      let singleTuple : Fin 1 → Set E := fun _ ↦ A
      let marginalLaw : Fin 1 → Measure ENNReal := fun i ↦
        Measure.map (fun k : ℕ ↦ (k : ENNReal))
          (poissonMeasure (((μ : Measure E) (singleTuple i)).toNNReal))
      have hsingleDisj : Pairwise fun i j : Fin 1 ↦ Disjoint (singleTuple i) (singleTuple j) := by
        intro i j hij
        exact False.elim <| hij (Subsingleton.elim _ _)
      have hTupleLaw :
          HasLaw
            (fun ω : Ω' ↦ fun i : Fin 1 ↦ X ω (singleTuple i))
            (Measure.pi marginalLaw)
            (P' : Measure Ω') := by
        -- Proof comment: the one-coordinate bounded evaluation law is the `Fin 1` specialization
        -- of the bounded tuple law established above.
        simpa [marginalLaw] using
          hBoundedTupleLaw singleTuple (fun _ ↦ hA) (fun _ ↦ hA_bdd) hsingleDisj
      let π0 : (Fin 1 → ENNReal) → ENNReal := fun z ↦ z 0
      have hProjLaw :
          HasLaw
            π0
            (Measure.map (fun k : ℕ ↦ (k : ENNReal)) (poissonMeasure (((μ : Measure E) A).toNNReal)))
            (Measure.pi marginalLaw) := by
        refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
        simpa [π0, singleTuple, marginalLaw] using
          (Measure.pi_map_eval (μ := marginalLaw) 0)
      -- Proof comment: project the unique coordinate of the bounded tuple law to recover the
      -- required scalar Poisson law.
      simpa [π0, singleTuple, Function.comp] using hProjLaw.fun_comp hTupleLaw

/-- Theorem 24.12: for every boundedly finite measure on the ambient locally compact Polish space
`E`, there exists a Poisson point process with that intensity measure. -/
theorem exists_poisson_point_process_with_intensity_measure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] (μ : BoundedlyFiniteMeasure E) :
    ∃ (Ω' : Type (max u v)) (_ : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω')
      (X : Ω' → Measure E), IsPoissonPointProcess (μ : Measure E) P' X := by
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    -- Proof comment: once the ambient space is nonempty, the source proof reduces the theorem to
    -- the finite-intensity constructor and shell superposition.
    exact existsPoissonPointProcessWithIntensityMeasure_nonempty μ
  · letI : IsEmpty E := not_nonempty_iff.mp hE
    -- Proof comment: on the empty space the deterministic zero process is the only possible
    -- point-process realization.
    exact existsPoissonPointProcessWithIntensityMeasure_empty μ

end ProbabilityTheory
