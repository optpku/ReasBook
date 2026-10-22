/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_57
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_58.OrderedKernel
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Helper for Theorem 17.58: an ordered coupling has mass `1` on the coordinatewise order set
exactly when the coordinatewise order holds almost everywhere. -/
lemma aeOrderedCoupling_iff_measure_eq_one {d : ℕ}
    (φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) :
    (∀ᵐ z ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))), z.1 ≤ z.2) ↔
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := by
  -- Proof comment: compare the almost-everywhere predicate with the corresponding measurable
  -- probability-one event.
  simpa using
    (MeasureTheory.ae_iff_prob_eq_one
      (μ := (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
      (p := fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦ z.1 ≤ z.2)
      measurable_le)

/-- Helper for Theorem 17.58: a bounded measurable test function stays integrable after
precomposing with either coordinate projection of a product-valued probability measure. -/
lemma integrable_compCoordinate_of_boundedRange {d : ℕ}
    (φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    {f : (Fin d → ℝ) → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_meas : Measurable f) :
    Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦ f z.1)
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ∧
      Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦ f z.2)
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
  obtain ⟨C, hC⟩ := hf_bdd.subset_closedBall 0
  have hfst_mem_Icc :
      ∀ z : (Fin d → ℝ) × (Fin d → ℝ), f z.1 ∈ Set.Icc (-C) C := by
    intro z
    have hzBall : f z.1 ∈ Metric.closedBall (0 : ℝ) C := hC ⟨z.1, rfl⟩
    have hzAbs : |f z.1| ≤ C := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hzBall
    simpa [Set.mem_Icc, abs_le] using hzAbs
  have hsnd_mem_Icc :
      ∀ z : (Fin d → ℝ) × (Fin d → ℝ), f z.2 ∈ Set.Icc (-C) C := by
    intro z
    have hzBall : f z.2 ∈ Metric.closedBall (0 : ℝ) C := hC ⟨z.2, rfl⟩
    have hzAbs : |f z.2| ≤ C := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hzBall
    simpa [Set.mem_Icc, abs_le] using hzAbs
  constructor
  · -- Proof comment: bound the first-coordinate pullback inside a fixed compact interval.
    refine MeasureTheory.Integrable.of_mem_Icc (-C) C
      ((hf_meas.comp measurable_fst).aemeasurable) ?_
    exact Filter.Eventually.of_forall hfst_mem_Icc
  · -- Proof comment: the same boundedness argument applies to the second coordinate.
    refine MeasureTheory.Integrable.of_mem_Icc (-C) C
      ((hf_meas.comp measurable_snd).aemeasurable) ?_
    exact Filter.Eventually.of_forall hsnd_mem_Icc

/-- Helper for Theorem 17.58: an ordered coupling forces the stochastic-order integral inequality
for every bounded measurable monotone test function. -/
lemma stochasticLE_of_isCoupling_of_aeOrdered {d : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    {φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))}
    (hCoupling : IsCoupling φ μ1 μ2)
    (hOrdered : ∀ᵐ z ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))), z.1 ≤ z.2) :
    StochasticLE μ1 μ2 := by
  intro f hf_mono hf_bdd hf_meas
  have hMarginals := (isCoupling_iff φ μ1 μ2).1 hCoupling
  rcases integrable_compCoordinate_of_boundedRange (φ := φ) hf_bdd hf_meas with
    ⟨hIntFst, hIntSnd⟩
  have hIntEqFst :
      ∫ x, f x ∂(μ1 : Measure (Fin d → ℝ)) =
        ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.1
          ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    -- Proof comment: rewrite the first marginal integral as an integral over the coupling.
    calc
      ∫ x, f x ∂(μ1 : Measure (Fin d → ℝ)) =
          ∫ x, f x
            ∂(((φ.map measurable_fst.aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
            simpa using
              congrArg
                (fun ν : ProbabilityMeasure (Fin d → ℝ) ↦
                  ∫ x, f x ∂(ν : Measure (Fin d → ℝ)))
                hMarginals.1.symm
      _ = ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.1
            ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
            simpa using
              (MeasureTheory.integral_map
                (μ := (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
                measurable_fst.aemeasurable
                (f := f)
                hf_meas.aestronglyMeasurable)
  have hIntEqSnd :
      ∫ x, f x ∂(μ2 : Measure (Fin d → ℝ)) =
        ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.2
          ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    -- Proof comment: rewrite the second marginal integral as an integral over the same coupling.
    calc
      ∫ x, f x ∂(μ2 : Measure (Fin d → ℝ)) =
          ∫ x, f x
            ∂(((φ.map measurable_snd.aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
            simpa using
              congrArg
                (fun ν : ProbabilityMeasure (Fin d → ℝ) ↦
                  ∫ x, f x ∂(ν : Measure (Fin d → ℝ)))
                hMarginals.2.symm
      _ = ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.2
            ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
            simpa using
              (MeasureTheory.integral_map
                (μ := (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
                measurable_snd.aemeasurable
                (f := f)
                hf_meas.aestronglyMeasurable)
  have hPointwise :
      (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦ f z.1)
        ≤ᵐ[(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))] fun z ↦ f z.2 := by
    -- Proof comment: push the almost-everywhere order support through monotonicity of `f`.
    filter_upwards [hOrdered] with z hz
    exact hf_mono hz
  calc
    ∫ x, f x ∂(μ1 : Measure (Fin d → ℝ)) =
        ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.1
          ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := hIntEqFst
    _ ≤ ∫ z : (Fin d → ℝ) × (Fin d → ℝ), f z.2
          ∂(φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) :=
        MeasureTheory.integral_mono_ae hIntFst hIntSnd hPointwise
    _ = ∫ x, f x ∂(μ2 : Measure (Fin d → ℝ)) := hIntEqSnd.symm

/-- Helper for Theorem 17.58: in dimension `0`, the product coupling is automatically supported
on the coordinatewise order relation because there are no coordinates to check. -/
lemma existsOrderedCoupling_finZero
    (μ1 μ2 : ProbabilityMeasure (Fin 0 → ℝ)) :
    ∃ φ : ProbabilityMeasure ((Fin 0 → ℝ) × (Fin 0 → ℝ)),
      IsCoupling φ μ1 μ2 ∧
        (φ : Measure ((Fin 0 → ℝ) × (Fin 0 → ℝ))) {z | z.1 ≤ z.2} = 1 := by
  let φ : ProbabilityMeasure ((Fin 0 → ℝ) × (Fin 0 → ℝ)) := μ1.prod μ2
  refine ⟨φ, ?_, ?_⟩
  · -- Proof comment: the canonical product measure already has the required marginals.
    simpa [φ] using isCoupling_prod μ1 μ2
  have hOrderedSet :
      ({z | z.1 ≤ z.2} : Set ((Fin 0 → ℝ) × (Fin 0 → ℝ))) = Set.univ := by
    -- Proof comment: functions on `Fin 0` are automatically ordered because the coordinate
    -- comparison has no indices.
    ext z
    simp
  -- Proof comment: once the order event is all of space, its probability is `1`.
  have hUniv :
      ((φ : Measure ((Fin 0 → ℝ) × (Fin 0 → ℝ))) Set.univ) = 1 := by
    simp
  rw [hOrderedSet]
  exact hUniv

/-- Helper for Theorem 17.58: the coordinatewise order set is measurable. -/
lemma measurableSet_orderedPairSet (d : ℕ) :
    MeasurableSet ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
      Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
  -- Proof comment: the pointwise order on `Fin d → ℝ` has closed graph, hence the associated
  -- subset of the product space is Borel.
  simpa using (measurableSet_le' (α := Fin d → ℝ))

/-- Helper for Theorem 17.58: the coordinatewise order set is closed. -/
lemma isClosed_orderedPairSet (d : ℕ) :
    IsClosed ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
      Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
  -- Proof comment: in the finite-dimensional product order, coordinatewise comparison is a
  -- closed relation.
  simpa using (OrderClosedTopology.isClosed_le' (α := Fin d → ℝ))

/-- Helper for Theorem 17.58: an ordered-mass-one coupling immediately yields stochastic order. -/
lemma stochasticLE_of_isCoupling_of_orderedMassOne {d : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    {φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))}
    (hCoupling : IsCoupling φ μ1 μ2)
    (hOrderedMass :
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1) :
    StochasticLE μ1 μ2 := by
  -- Proof comment: turn the mass-one support statement into an almost-everywhere order statement
  -- and reuse the coupling-to-stochastic-order lemma already established above.
  exact stochasticLE_of_isCoupling_of_aeOrdered hCoupling
    ((aeOrderedCoupling_iff_measure_eq_one φ).2 hOrderedMass)

/-- Helper for Theorem 17.58: any finite amount of `ENNReal` mass dominated by a finite sum can be
extracted as a pointwise subweight supported on the same finite set. -/
private lemma existsSubweightLeFinsetSum {α : Type*} (s : Finset α)
    (w : α → ENNReal) (m : ENNReal) (hm : m ≤ Finset.sum s w) :
    ∃ v : α → ENNReal,
      (∀ a, v a ≤ w a) ∧
      (∀ a, a ∉ s → v a = 0) ∧
      Finset.sum s v = m := by
  classical
  revert m
  refine s.induction_on ?_ ?_
  · intro m hm
    have hm0 : m = 0 := by
      simpa using hm
    refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
    · -- Proof comment: on the empty support the only admissible subweight is zero.
      intro a
      simp
    · -- Proof comment: outside the empty set the subweight is zero by definition.
      intro a _
      simp
    · -- Proof comment: the empty sum is zero, matching the extracted mass.
      simp [hm0]
  · intro a s ha ih m hm
    by_cases hma : m ≤ w a
    · refine ⟨fun b ↦ if b = a then m else 0, ?_, ?_, ?_⟩
      · -- Proof comment: when the head weight already dominates `m`, place all mass at `a`.
        intro b
        by_cases hb : b = a
        · simp [hb, hma]
        · simp [hb]
      · -- Proof comment: every point outside `insert a s` still receives zero mass.
        intro b hb
        have hba : b ≠ a := by
          intro hba
          subst hba
          exact hb (by simp [ha])
        simp [hba]
      · -- Proof comment: the extracted support consists only of the inserted point `a`.
        simp [ha]
    · have hwa : w a ≤ m := le_of_not_ge hma
      have hwa_ne_top : w a ≠ ⊤ := by
        intro htop
        exact hma (htop ▸ le_top)
      have hrest : m - w a ≤ Finset.sum s w := by
        -- Proof comment: after peeling the full mass at `a`, the remaining target mass is still
        -- bounded by the remaining tail sum.
        have hm' : w a + (m - w a) ≤ Finset.sum (insert a s) w := by
          rw [add_comm, tsub_add_cancel_of_le hwa]
          simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using hm
        simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using
          (ENNReal.le_sub_of_add_le_left hwa_ne_top hm')
      rcases ih (m - w a) hrest with ⟨v, hv_le, hv_out, hv_sum⟩
      refine ⟨fun b ↦ if b = a then w a else v b, ?_, ?_, ?_⟩
      · -- Proof comment: keep the full original mass at `a` and use the inductive extractor on
        -- the remaining support.
        intro b
        by_cases hb : b = a
        · simp [hb]
        · simp [hb, hv_le b]
      · -- Proof comment: outside `insert a s`, both the new head mass and the tail extractor
        -- vanish.
        intro b hb
        by_cases hb' : b = a
        · subst hb'
          simp at hb
        · simp [hb', hv_out b (by simpa [hb'] using hb)]
      · -- Proof comment: the new sum is `w a` plus the inductively extracted remainder, which
        -- reconstructs `m`.
        calc
          Finset.sum (insert a s) (fun b ↦ if b = a then w a else v b)
              = w a + Finset.sum s v := by
                  rw [Finset.sum_insert ha]
                  rw [if_pos rfl]
                  refine congrArg (fun t ↦ w a + t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  have hba : b ≠ a := by
                    intro hba
                    subst hba
                    exact ha hb
                  simp [hba]
          _ = w a + (m - w a) := by rw [hv_sum]
          _ = m := by
              simpa [add_comm] using (tsub_add_cancel_of_le hwa)

/-- Helper for Theorem 17.58: the raw finite extractor can be specialized to a principal upper
set without introducing any complement or normalization bookkeeping. -/
private lemma existsSubweightSupportedOnUpperClosure {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableRel (fun x y : α => x ≤ y)]
    (w : α → ENNReal) (a : α) (m : ENNReal)
    (hm : m ≤ Finset.sum (Finset.univ.filter fun b => a ≤ b) w) :
    ∃ v : α → ENNReal,
      (∀ b, v b ≤ w b) ∧
      (∀ b, ¬ a ≤ b → v b = 0) ∧
      Finset.sum Finset.univ v = m := by
  classical
  rcases existsSubweightLeFinsetSum (s := Finset.univ.filter fun b => a ≤ b) w m hm with
    ⟨v, hv_le, hv_out, hv_sum⟩
  refine ⟨v, hv_le, ?_, ?_⟩
  · -- Proof comment: the support condition is exactly membership in the filtered upper closure.
    intro b hb
    exact hv_out b (by simp [hb])
  · -- Proof comment: outside the principal upper set the extracted subweight is zero, so the sum
    -- over all points collapses to the filtered support sum.
    calc
      Finset.sum Finset.univ v = Finset.sum (Finset.univ.filter fun b => a ≤ b) v := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hb : a ≤ b
        · simp [hb]
        · simp [hb, hv_out b (by simp [hb])]
      _ = m := hv_sum

/-- Helper for Theorem 17.58: the raw finite extractor can also be specialized to a principal
lower closure, which is the first reusable piece in the finite lower-set route. -/
private lemma existsSubweightSupportedOnLowerClosure {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableRel (fun x y : α => x ≤ y)]
    (w : α → ENNReal) (b : α) (m : ENNReal)
    (hm : m ≤ Finset.sum (Finset.univ.filter fun a => a ≤ b) w) :
    ∃ v : α → ENNReal,
      (∀ a, v a ≤ w a) ∧
      (∀ a, ¬ a ≤ b → v a = 0) ∧
      Finset.sum Finset.univ v = m := by
  classical
  rcases existsSubweightLeFinsetSum (s := Finset.univ.filter fun a => a ≤ b) w m hm with
    ⟨v, hv_le, hv_out, hv_sum⟩
  refine ⟨v, hv_le, ?_, ?_⟩
  · -- Proof comment: the support condition is exactly membership in the filtered lower closure.
    intro a ha
    exact hv_out a (by simp [ha])
  · -- Proof comment: outside the principal lower closure the extracted subweight is zero, so the
    -- sum over the whole finite type collapses to the filtered support sum.
    calc
      Finset.sum Finset.univ v = Finset.sum (Finset.univ.filter fun a => a ≤ b) v := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro a _
        by_cases ha : a ≤ b
        · simp [ha]
        · simp [ha, hv_out a (by simp [ha])]
      _ = m := hv_sum

/-- Helper for Theorem 17.58: if `b` is minimal in the support of `q`, then the total `q`-mass on
its lower closure `Iic b` is already concentrated at `b`. -/
private lemma sum_lowerClosure_eq_of_support_minimal {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableRel (fun x y : α => x ≤ y)]
    (q : α → ENNReal) {b : α}
    (hmin : ∀ {a : α}, q a ≠ 0 → a ≤ b → a = b) :
    Finset.sum (Finset.univ.filter fun a => a ≤ b) q = q b := by
  classical
  have hb_mem : b ∈ Finset.univ.filter (fun a => a ≤ b) := by
    simp
  -- Proof comment: every other point in `Iic b` has zero `q`-mass by minimality of the support
  -- element `b`, so only the `b`-summand survives.
  refine Finset.sum_eq_single_of_mem b hb_mem ?_
  intro a ha hab
  by_cases haq : q a = 0
  · exact haq
  · exfalso
    exact hab (hmin haq (by simpa using (Finset.mem_filter.mp ha).2))

/-- Helper for Theorem 17.58: on a finite partial order, the mass of a principal lower closure is
the finite sum of singleton masses over that lower closure. -/
private lemma measure_lowerClosure_eq_sum_singleton
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] [PartialOrder α]
    [DecidableRel (fun x y : α => x ≤ y)]
    (μ : Measure α) (b : α) :
    μ {a | a ≤ b} =
      Finset.sum (Finset.univ.filter fun a => a ≤ b) (fun a ↦ μ {a}) := by
  classical
  calc
    μ {a | a ≤ b}
        = ∑ a : α, ({a | a ≤ b} : Set α).indicator (fun a ↦ μ {a}) a := by
            -- Proof comment: finite atomicity rewrites the lower-closure mass as a sum of
            -- singleton masses guarded by the lower-closure indicator.
            simpa using
              (Measure.tsum_indicator_apply_singleton
                (μ := μ) (s := {a | a ≤ b}) (Set.toFinite _).measurableSet).symm
    _ = Finset.sum (Finset.univ.filter fun a => a ≤ b) (fun a ↦ μ {a}) := by
          -- Proof comment: on the finite index type, the indicator sum is exactly the filtered
          -- sum over the principal lower closure.
          simpa [Set.indicator] using
            (Finset.sum_filter
              (s := Finset.univ)
              (f := fun a : α ↦ μ {a})
              (p := fun a ↦ a ≤ b)).symm

/-- Helper for Theorem 17.58: a finite nonzero weight function on a partial order has a
support-minimal positive atom. -/
private lemma existsSupportMinimalPositiveMass
    {α : Type*} [Fintype α] [PartialOrder α]
    (q : α → ENNReal) (hq : ∃ a, q a ≠ 0) :
    ∃ b, q b ≠ 0 ∧ ∀ {a : α}, q a ≠ 0 → a ≤ b → a = b := by
  classical
  let s : Finset α := Finset.univ.filter fun a ↦ q a ≠ 0
  have hs_nonempty : s.Nonempty := by
    rcases hq with ⟨a, ha⟩
    exact ⟨a, by simp [s, ha]⟩
  rcases Finset.exists_minimal (s := s) hs_nonempty with ⟨b, hbmin⟩
  rcases (minimal_iff.mp hbmin) with ⟨hbmem, hbmin'⟩
  refine ⟨b, (Finset.mem_filter.mp hbmem).2, ?_⟩
  intro a ha hab
  -- Proof comment: minimality inside the positive support says any smaller positive atom must
  -- already coincide with `b`.
  exact (hbmin' (by simp [s, ha]) hab).symm

/-- Helper for Theorem 17.58: a lower-set inequality lets us extract the whole mass of a
support-minimal target atom from the corresponding lower closure of the source singleton masses. -/
private lemma existsSubweightSupportedOnLowerClosure_of_lowerSetLE
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] [PartialOrder α]
    [DecidableRel (fun x y : α => x ≤ y)]
    {ν1 ν2 : ProbabilityMeasure α}
    (hLower :
      ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D)
    {b : α}
    (hmin : ∀ {a : α}, (ν2 : Measure α) {a} ≠ 0 → a ≤ b → a = b) :
    ∃ v : α → ENNReal,
      (∀ a, v a ≤ (ν1 : Measure α) {a}) ∧
      (∀ a, ¬ a ≤ b → v a = 0) ∧
      Finset.sum Finset.univ v = (ν2 : Measure α) {b} := by
  classical
  have hLowerIic :
      (ν2 : Measure α) {a | a ≤ b} ≤ (ν1 : Measure α) {a | a ≤ b} := by
    -- Proof comment: the principal lower closure `Iic b` is itself a lower set.
    exact hLower {a | a ≤ b} (by
      intro x y hxy hyb
      exact le_trans hxy hyb)
  have hMass :
      (ν2 : Measure α) {b} ≤
        Finset.sum (Finset.univ.filter fun a => a ≤ b) (fun a ↦ (ν1 : Measure α) {a}) := by
    calc
      (ν2 : Measure α) {b}
          = Finset.sum (Finset.univ.filter fun a => a ≤ b) (fun a ↦ (ν2 : Measure α) {a}) := by
              -- Proof comment: support minimality collapses the target lower-closure mass to the
              -- single atom at `b`.
              symm
              exact sum_lowerClosure_eq_of_support_minimal
                (q := fun a ↦ (ν2 : Measure α) {a}) hmin
      _ = (ν2 : Measure α) {a | a ≤ b} := by
            -- Proof comment: rewrite the filtered singleton sum back as the lower-closure mass.
            exact (measure_lowerClosure_eq_sum_singleton (μ := (ν2 : Measure α)) b).symm
      _ ≤ (ν1 : Measure α) {a | a ≤ b} := hLowerIic
      _ = Finset.sum (Finset.univ.filter fun a => a ≤ b) (fun a ↦ (ν1 : Measure α) {a}) := by
            -- Proof comment: the source lower-closure mass has the same finite singleton
            -- expansion.
            exact measure_lowerClosure_eq_sum_singleton (μ := (ν1 : Measure α)) b
  -- Proof comment: apply the already-proved raw extractor on the lower closure with target mass
  -- equal to the singleton mass at the minimal atom `b`.
  exact existsSubweightSupportedOnLowerClosure
    (w := fun a ↦ (ν1 : Measure α) {a}) (b := b) (m := (ν2 : Measure α) {b}) hMass

/-- Helper for Theorem 17.58: on a finite measurable space, the mass of a set is the sum of the
singleton masses over that set. -/
private lemma measure_apply_eq_sum_indicator_singleton
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (μ : Measure α) (s : Set α) :
    μ s = ∑ a : α, s.indicator (fun a ↦ μ {a}) a := by
  -- Proof comment: `Measure.tsum_indicator_apply_singleton` expands any countable atomic measure
  -- over the indicator of the target set, and the `Fintype` hypothesis turns the `tsum` into a
  -- finite sum.
  simpa using
    (Measure.tsum_indicator_apply_singleton
      (μ := μ) (s := s) (Set.toFinite s).measurableSet).symm

/-- Helper for Theorem 17.58: on a finite measurable space, a measure is reconstructed from its
singleton masses as a sum of Dirac masses. -/
private lemma measure_eq_sum_smul_dirac_fintype
    {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
    (μ : Measure α) :
    Measure.sum (fun a : α ↦ μ {a} • Measure.dirac a) = μ := by
  -- Proof comment: finite measures on a finite space are purely atomic, so the standard
  -- countable Dirac decomposition becomes an actual finite reconstruction formula.
  exact Measure.sum_smul_dirac (μ := μ)

/-- Helper for Theorem 17.58: on finite measurable spaces, a coupling is equivalent to matching
the row and column singleton masses of the joint law with the singleton masses of the marginals. -/
private lemma isCoupling_iff_singletonMass_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {ρ : ProbabilityMeasure (α × β)} {μ₁ : ProbabilityMeasure α} {μ₂ : ProbabilityMeasure β} :
    IsCoupling ρ μ₁ μ₂ ↔
      (∀ a : α, ∑ b : β, ((ρ : Measure (α × β)) {(a, b)}) = (μ₁ : Measure α) {a}) ∧
        (∀ b : β, ∑ a : α, ((ρ : Measure (α × β)) {(a, b)}) = (μ₂ : Measure β) {b}) := by
  constructor
  · intro hCoupling
    rcases (isCoupling_iff ρ μ₁ μ₂).1 hCoupling with ⟨hfst, hsnd⟩
    constructor
    · intro a
      -- Proof comment: evaluate the first marginal equality on the singleton `{a}` and rewrite
      -- the preimage of `{a}` under `Prod.fst` as the finite row sum of singleton masses.
      have hfstApply :
          (Measure.map Prod.fst (ρ : Measure (α × β))) {a} =
            ∑ b : β, ((ρ : Measure (α × β)) {(a, b)}) := by
        rw [Measure.map_apply measurable_fst (measurableSet_singleton a)]
        simpa using
          (MeasureTheory.measure_preimage_fst_singleton_eq_sum
            (μ := (ρ : Measure (α × β))) a)
      have hfstSingleton :=
        congrArg (fun ν : ProbabilityMeasure α ↦ ((ν : Measure α) {a})) hfst
      exact hfstApply.symm.trans hfstSingleton
    · intro b
      -- Proof comment: the second marginal equality gives the matching column sum identity.
      have hsndApply :
          (Measure.map Prod.snd (ρ : Measure (α × β))) {b} =
            ∑ a : α, ((ρ : Measure (α × β)) {(a, b)}) := by
        rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
        simpa using
          (MeasureTheory.measure_preimage_snd_singleton_eq_sum
            (μ := (ρ : Measure (α × β))) b)
      have hsndSingleton :=
        congrArg (fun ν : ProbabilityMeasure β ↦ ((ν : Measure β) {b})) hsnd
      exact hsndApply.symm.trans hsndSingleton
  · rintro ⟨hRows, hCols⟩
    rw [isCoupling_iff]
    constructor
    · -- Proof comment: a finite measure is determined by its singleton masses, so matching every
      -- row sum with the singleton masses of `μ₁` is enough to identify the first marginal.
      apply ProbabilityMeasure.toMeasure_injective
      calc
        Measure.map Prod.fst (ρ : Measure (α × β)) =
            Measure.sum (fun a : α ↦
              (Measure.map Prod.fst (ρ : Measure (α × β))) {a} • Measure.dirac a) := by
                simpa using
                  (measure_eq_sum_smul_dirac_fintype
                    (μ := Measure.map Prod.fst (ρ : Measure (α × β)))).symm
        _ = Measure.sum (fun a : α ↦ ((μ₁ : Measure α) {a}) • Measure.dirac a) := by
              exact congrArg Measure.sum <| funext fun a ↦ by
                have hfstApply :
                    (Measure.map Prod.fst (ρ : Measure (α × β))) {a} =
                      ∑ b : β, ((ρ : Measure (α × β)) {(a, b)}) := by
                  rw [Measure.map_apply measurable_fst (measurableSet_singleton a)]
                  simpa using
                    (MeasureTheory.measure_preimage_fst_singleton_eq_sum
                      (μ := (ρ : Measure (α × β))) a)
                rw [hfstApply, hRows a]
        _ = (μ₁ : Measure α) := measure_eq_sum_smul_dirac_fintype (μ := (μ₁ : Measure α))
    · -- Proof comment: the same atomic reconstruction on the second marginal turns the column
      -- identities into the desired equality with `μ₂`.
      apply ProbabilityMeasure.toMeasure_injective
      calc
        Measure.map Prod.snd (ρ : Measure (α × β)) =
            Measure.sum (fun b : β ↦
              (Measure.map Prod.snd (ρ : Measure (α × β))) {b} • Measure.dirac b) := by
                simpa using
                  (measure_eq_sum_smul_dirac_fintype
                    (μ := Measure.map Prod.snd (ρ : Measure (α × β)))).symm
        _ = Measure.sum (fun b : β ↦ ((μ₂ : Measure β) {b}) • Measure.dirac b) := by
              exact congrArg Measure.sum <| funext fun b ↦ by
                have hsndApply :
                    (Measure.map Prod.snd (ρ : Measure (α × β))) {b} =
                      ∑ a : α, ((ρ : Measure (α × β)) {(a, b)}) := by
                  rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
                  simpa using
                    (MeasureTheory.measure_preimage_snd_singleton_eq_sum
                      (μ := (ρ : Measure (α × β))) b)
                rw [hsndApply, hCols b]
        _ = (μ₂ : Measure β) := measure_eq_sum_smul_dirac_fintype (μ := (μ₂ : Measure β))

/-- Helper for Theorem 17.58: on a finite measurable space, the singleton masses of a probability
measure sum to `1`. -/
private lemma sum_singletonMass_eq_one_finite
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : ProbabilityMeasure α) :
    (∑ a : α, (ν : Measure α) {a}) = 1 := by
  -- Proof comment: a finite probability measure is the sum of its singleton masses over the whole
  -- space, and the mass of the whole space is `1`.
  calc
    ∑ a : α, (ν : Measure α) {a} = (ν : Measure α) Set.univ := by
      symm
      simpa using
        (measure_apply_eq_sum_indicator_singleton
          (μ := (ν : Measure α)) (s := Set.univ))
    _ = 1 := by simp

/-- Helper for Theorem 17.58: on a finite probability space, the real value of the mass of a set
is the sum of the real singleton masses over that set. -/
private lemma measure_apply_toReal_eq_sum_indicator_singleton_toReal
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : ProbabilityMeasure α) (s : Set α) :
    ((ν : Measure α) s).toReal =
      ∑ a : α, s.indicator (fun a ↦ ((ν : Measure α) {a}).toReal) a := by
  -- Proof comment: first expand the set mass into a finite sum of singleton masses in `ENNReal`,
  -- then convert that finite sum to `ℝ` termwise because every singleton mass is finite.
  rw [measure_apply_eq_sum_indicator_singleton (μ := (ν : Measure α)) (s := s)]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases hs : a ∈ s
    · simp [Set.indicator, hs]
    · simp [Set.indicator, hs]
  · intro a ha
    by_cases hs : a ∈ s
    · simpa [Set.indicator, hs] using
        (measure_ne_top (μ := (ν : Measure α)) ({a} : Set α))
    · simp [Set.indicator, hs]

/-- Helper for Theorem 17.58: on a finite probability space, the real singleton masses also sum
to `1`. -/
private lemma sum_singletonMass_toReal_eq_one_finite
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : ProbabilityMeasure α) :
    (∑ a : α, ((ν : Measure α) {a}).toReal) = 1 := by
  -- Proof comment: convert the already-proved `ENNReal` normalization identity to `ℝ` termwise.
  calc
    ∑ a : α, ((ν : Measure α) {a}).toReal =
        (∑ a : α, (ν : Measure α) {a}).toReal := by
          symm
          exact ENNReal.toReal_sum fun a _ ↦
            (measure_ne_top (μ := (ν : Measure α)) ({a} : Set α))
    _ = 1 := by simp [sum_singletonMass_eq_one_finite (ν := ν)]

/-- Helper for Theorem 17.58: weighting an upper-set indicator by the real singleton masses of a
finite probability law recovers the real mass of that upper set times the indicator height. -/
private lemma sum_singletonMass_toReal_mul_indicator
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : ProbabilityMeasure α) (s : Set α) (c : ℝ) :
    ∑ a : α, ((ν : Measure α) {a}).toReal * s.indicator (fun _ ↦ c) a =
      ((ν : Measure α) s).toReal * c := by
  -- Proof comment: pull the constant height `c` out of the finite singleton-mass expansion of
  -- the set mass.
  calc
    ∑ a : α, ((ν : Measure α) {a}).toReal * s.indicator (fun _ ↦ c) a =
        ∑ a : α, s.indicator (fun a ↦ ((ν : Measure α) {a}).toReal) a * c := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          by_cases hs : a ∈ s
          · simp [Set.indicator, hs, mul_assoc, mul_left_comm, mul_comm]
          · simp [Set.indicator, hs]
    _ = (∑ a : α, s.indicator (fun a ↦ ((ν : Measure α) {a}).toReal) a) * c := by
          rw [Finset.sum_mul]
    _ = ((ν : Measure α) s).toReal * c := by
          rw [measure_apply_toReal_eq_sum_indicator_singleton_toReal (ν := ν) (s := s)]

/-- Helper for Theorem 17.58: upper-set mass inequalities already control the real weighted
expectations of upper-set indicators on a finite probability space. -/
private lemma upperSetIndicatorExpectationLE_finiteReal
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hUpper : ∀ U : Set α, IsUpperSet U → (ν1 : Measure α) U ≤ (ν2 : Measure α) U)
    (U : Set α) (hU : IsUpperSet U) {c : ℝ} (hc : 0 ≤ c) :
    ∑ a : α, ((ν1 : Measure α) {a}).toReal * U.indicator (fun _ ↦ c) a ≤
      ∑ a : α, ((ν2 : Measure α) {a}).toReal * U.indicator (fun _ ↦ c) a := by
  -- Proof comment: rewrite both finite sums as the corresponding upper-set masses times the
  -- common nonnegative height `c`, then use monotonicity of `toReal` on finite masses.
  calc
    ∑ a : α, ((ν1 : Measure α) {a}).toReal * U.indicator (fun _ ↦ c) a =
        ((ν1 : Measure α) U).toReal * c := by
          simpa using sum_singletonMass_toReal_mul_indicator (ν := ν1) (s := U) (c := c)
    _ ≤ ((ν2 : Measure α) U).toReal * c := by
          exact mul_le_mul_of_nonneg_right
            (ENNReal.toReal_mono
              (measure_ne_top (μ := (ν2 : Measure α)) U)
              (hUpper U hU))
            hc
    _ =
        ∑ a : α, ((ν2 : Measure α) {a}).toReal * U.indicator (fun _ ↦ c) a := by
          simpa using
            (sum_singletonMass_toReal_mul_indicator (ν := ν2) (s := U) (c := c)).symm

/-- Helper for Theorem 17.58: on a finite partially ordered probability space, upper-set mass
inequalities imply the real expectation inequality for every monotone test function. -/
private lemma monotoneExpectationLE_of_upperSetLE_finiteReal
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hUpper : ∀ U : Set α, IsUpperSet U → (ν1 : Measure α) U ≤ (ν2 : Measure α) U)
    {g : α → ℝ} (hg_mono : Monotone g) :
    ∑ a : α, ((ν1 : Measure α) {a}).toReal * g a ≤
      ∑ a : α, ((ν2 : Measure α) {a}).toReal * g a := by
  classical
  letI : Nonempty α := ν1.nonempty
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty g
  let gShift : α → ℝ := fun a ↦ g a - m
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty gShift
  have hgShift_nonneg : ∀ a : α, 0 ≤ gShift a := by
    intro a
    -- Proof comment: subtract the minimum value of `g` on the finite alphabet to enter the
    -- nonnegative layer-cake regime.
    exact sub_nonneg.mpr (Finset.inf'_le (s := Finset.univ) (f := g) (by simp))
  have hgShift_le : ∀ a : α, gShift a ≤ M := by
    intro a
    -- Proof comment: the shifted test is bounded above by its finite supremum on `Finset.univ`.
    exact Finset.le_sup' (s := Finset.univ) (f := gShift) (by simp)
  have hgShift_mono : Monotone gShift := by
    intro a b hab
    -- Proof comment: subtracting a constant preserves monotonicity.
    exact sub_le_sub_right (hg_mono hab) m
  let tail1 : ℝ → ℝ := fun t ↦ (ν1 : Measure α).real {a | t ≤ gShift a}
  let tail2 : ℝ → ℝ := fun t ↦ (ν2 : Measure α).real {a | t ≤ gShift a}
  have htail_meas1 : Measurable tail1 := by
    -- Proof comment: superlevel masses are antitone in the threshold parameter.
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun s t hst ↦
      measure_mono fun _ ha ↦ le_trans hst ha
  have htail_meas2 : Measurable tail2 := by
    -- Proof comment: the same antitone measurability holds for the second law.
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun s t hst ↦
      measure_mono fun _ ha ↦ le_trans hst ha
  have htail_int1 : IntegrableOn tail1 (Set.Ioc 0 M) := by
    -- Proof comment: every tail mass is bounded by the total mass `1`, so the finite interval
    -- integral is automatically integrable.
    apply Measure.integrableOn_of_bounded (M := (ν1 : Measure α).real Set.univ)
      measure_Ioc_lt_top.ne
    · exact htail_meas1.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t ↦ by
        simpa [tail1, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
          (measureReal_mono (Set.subset_univ {a : α | t ≤ gShift a})
            (measure_ne_top (μ := (ν1 : Measure α)) Set.univ))
  have htail_int2 : IntegrableOn tail2 (Set.Ioc 0 M) := by
    -- Proof comment: the same bounded-tail argument applies to the second law.
    apply Measure.integrableOn_of_bounded (M := (ν2 : Measure α).real Set.univ)
      measure_Ioc_lt_top.ne
    · exact htail_meas2.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t ↦ by
        simpa [tail2, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
          (measureReal_mono (Set.subset_univ {a : α | t ≤ gShift a})
            (measure_ne_top (μ := (ν2 : Measure α)) Set.univ))
  have htail_le :
      tail1 ≤ᵐ[volume.restrict (Set.Ioc 0 M)] tail2 := by
    -- Proof comment: every positive shifted superlevel set is an upper set, so `hUpper`
    -- compares the two tail masses pointwise on the integration interval.
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hUpperSet : IsUpperSet {a : α | t ≤ gShift a} := by
      intro a b hab ha
      exact le_trans ha (hgShift_mono hab)
    exact ENNReal.toReal_mono
      (measure_ne_top (μ := (ν2 : Measure α)) {a : α | t ≤ gShift a})
      (hUpper {a : α | t ≤ gShift a} hUpperSet)
  have hShift_integral :
      ∫ a, gShift a ∂(ν1 : Measure α) ≤ ∫ a, gShift a ∂(ν2 : Measure α) := by
    have hLayer1 :
        ∫ a, gShift a ∂(ν1 : Measure α) =
          ∫ t in Set.Ioc 0 M, tail1 t := by
      -- Proof comment: layer cake rewrites the shifted expectation as the integral of its
      -- superlevel masses over the finite range `[0, M]`.
      exact
        (Integrable.of_finite (μ := (ν1 : Measure α)) (f := gShift)).integral_eq_integral_Ioc_meas_le
          (Filter.Eventually.of_forall hgShift_nonneg)
          (Filter.Eventually.of_forall hgShift_le)
    have hLayer2 :
        ∫ a, gShift a ∂(ν2 : Measure α) =
          ∫ t in Set.Ioc 0 M, tail2 t := by
      -- Proof comment: the second law has the identical layer-cake representation.
      exact
        (Integrable.of_finite (μ := (ν2 : Measure α)) (f := gShift)).integral_eq_integral_Ioc_meas_le
          (Filter.Eventually.of_forall hgShift_nonneg)
          (Filter.Eventually.of_forall hgShift_le)
    rw [hLayer1, hLayer2]
    exact setIntegral_mono_ae_restrict htail_int1 htail_int2 htail_le
  have hShift_sum :
      ∑ a : α, ((ν1 : Measure α) {a}).toReal * gShift a ≤
        ∑ a : α, ((ν2 : Measure α) {a}).toReal * gShift a := by
    -- Proof comment: on a finite alphabet, the Bochner integrals are exactly the weighted
    -- singleton-mass sums from the target statement.
    rw [MeasureTheory.integral_fintype (μ := (ν1 : Measure α)) (f := gShift) Integrable.of_finite,
      MeasureTheory.integral_fintype (μ := (ν2 : Measure α)) (f := gShift) Integrable.of_finite]
      at hShift_integral
    simpa [Measure.real_def, smul_eq_mul] using hShift_integral
  have hDecomp1 :
      ∑ a : α, ((ν1 : Measure α) {a}).toReal * g a =
        m + ∑ a : α, ((ν1 : Measure α) {a}).toReal * gShift a := by
    -- Proof comment: add back the common minimum value using the normalization
    -- `∑_a ν₁ {a} = 1`.
    calc
      ∑ a : α, ((ν1 : Measure α) {a}).toReal * g a
          = ∑ a : α, (((ν1 : Measure α) {a}).toReal * m +
              ((ν1 : Measure α) {a}).toReal * gShift a) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              dsimp [gShift]
              ring
      _ = (∑ a : α, ((ν1 : Measure α) {a}).toReal * m) +
            ∑ a : α, ((ν1 : Measure α) {a}).toReal * gShift a := by
              rw [Finset.sum_add_distrib]
      _ = m + ∑ a : α, ((ν1 : Measure α) {a}).toReal * gShift a := by
            rw [show ∑ a : α, ((ν1 : Measure α) {a}).toReal * m =
                (∑ a : α, ((ν1 : Measure α) {a}).toReal) * m by
                  rw [Finset.sum_mul]]
            rw [sum_singletonMass_toReal_eq_one_finite (ν := ν1), one_mul]
  have hDecomp2 :
      ∑ a : α, ((ν2 : Measure α) {a}).toReal * g a =
        m + ∑ a : α, ((ν2 : Measure α) {a}).toReal * gShift a := by
    -- Proof comment: the same decomposition holds for `ν₂`, with the same minimum shift `m`.
    calc
      ∑ a : α, ((ν2 : Measure α) {a}).toReal * g a
          = ∑ a : α, (((ν2 : Measure α) {a}).toReal * m +
              ((ν2 : Measure α) {a}).toReal * gShift a) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              dsimp [gShift]
              ring
      _ = (∑ a : α, ((ν2 : Measure α) {a}).toReal * m) +
            ∑ a : α, ((ν2 : Measure α) {a}).toReal * gShift a := by
              rw [Finset.sum_add_distrib]
      _ = m + ∑ a : α, ((ν2 : Measure α) {a}).toReal * gShift a := by
            rw [show ∑ a : α, ((ν2 : Measure α) {a}).toReal * m =
                (∑ a : α, ((ν2 : Measure α) {a}).toReal) * m by
                  rw [Finset.sum_mul]]
            rw [sum_singletonMass_toReal_eq_one_finite (ν := ν2), one_mul]
  calc
    ∑ a : α, ((ν1 : Measure α) {a}).toReal * g a =
        m + ∑ a : α, ((ν1 : Measure α) {a}).toReal * gShift a := hDecomp1
    _ ≤ m + ∑ a : α, ((ν2 : Measure α) {a}).toReal * gShift a := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hShift_sum m
    _ = ∑ a : α, ((ν2 : Measure α) {a}).toReal * g a := hDecomp2.symm

/-- Helper for Theorem 17.58: on a finite partial order, upper-set mass inequalities imply the
Hall neighborhood inequalities on finite subsets. -/
private lemma hallCondition_of_upperSetLE_finite
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hUpper : ∀ U : Set α, IsUpperSet U → (ν1 : Measure α) U ≤ (ν2 : Measure α) U)
    (A : Finset α) :
    Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) ≤
      (ν2 : Measure α) {b | ∃ a ∈ A, a ≤ b} := by
  let U : Set α := {b | ∃ a ∈ A, a ≤ b}
  have hU_upper : IsUpperSet U := by
    -- Proof comment: the upward neighborhood of `A` stays upward by transitivity of the order.
    intro x y hxy hx
    rcases hx with ⟨a, haA, hax⟩
    exact ⟨a, haA, le_trans hax hxy⟩
  have hA_subset : (A : Set α) ⊆ U := by
    -- Proof comment: every element of `A` lies in its own upward neighborhood.
    intro a haA
    exact ⟨a, haA, le_rfl⟩
  have hLeft :
      Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) = (ν1 : Measure α) (A : Set α) := by
    -- Proof comment: finite atomicity rewrites the mass of `A` as the sum of its singleton masses.
    let p : PMF α := ((ν1 : Measure α)).toPMF
    have hp : p.toMeasure = (ν1 : Measure α) := by
      simpa [p] using (Measure.toPMF_toMeasure (μ := (ν1 : Measure α)))
    calc
      Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) = ∑ a ∈ A, p a := by
        simp [p, Measure.toPMF_apply]
      _ = p.toMeasure A := by
        symm
        simpa using (PMF.toMeasure_apply_finset (p := p) A)
      _ = (ν1 : Measure α) (A : Set α) := by
        rw [hp]
  calc
    Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) = (ν1 : Measure α) (A : Set α) := hLeft
    _ ≤ (ν1 : Measure α) U := measure_mono hA_subset
    _ ≤ (ν2 : Measure α) U := hUpper U hU_upper
    _ = (ν2 : Measure α) {b | ∃ a ∈ A, a ≤ b} := rfl

/-- Helper for Theorem 17.58: once a finite weight matrix has the correct row and column sums and
vanishes off the order relation, it packages into an ordered coupling. -/
private lemma existsOrderedCoupling_of_weightMatrix
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (m : α → α → ENNReal)
    (hMass : (∑ a : α, ∑ b : α, m a b) = 1)
    (hRows : ∀ a : α, (∑ b : α, m a b) = (ν1 : Measure α) {a})
    (hCols : ∀ b : α, (∑ a : α, m a b) = (ν2 : Measure α) {b})
    (hSupport : ∀ a b : α, ¬ a ≤ b → m a b = 0) :
    ∃ ψ : ProbabilityMeasure (α × α),
      IsCoupling ψ ν1 ν2 ∧
        (ψ : Measure (α × α)) {z | z.1 ≤ z.2} = 1 := by
  classical
  let p : PMF (α × α) := PMF.ofFintype
    (fun z : α × α ↦ m z.1 z.2) (by simpa [Fintype.sum_prod_type] using hMass)
  let ψ : ProbabilityMeasure (α × α) := ⟨p.toMeasure, inferInstance⟩
  refine ⟨ψ, ?_, ?_⟩
  · -- Proof comment: the finite singleton-mass characterization turns the row and column sum
    -- identities of `m` directly into the coupling equations.
    refine (isCoupling_iff_singletonMass_finite (ρ := ψ) (μ₁ := ν1) (μ₂ := ν2)).2 ?_
    constructor
    · intro a
      calc
        ∑ b : α, ((ψ : Measure (α × α)) {(a, b)}) = ∑ b : α, m a b := by
          simp [ψ, p]
        _ = (ν1 : Measure α) {a} := hRows a
    · intro b
      calc
        ∑ a : α, ((ψ : Measure (α × α)) {(a, b)}) = ∑ a : α, m a b := by
          simp [ψ, p]
        _ = (ν2 : Measure α) {b} := hCols b
  · have hSupportSubset :
        p.support ⊆ ({z : α × α | z.1 ≤ z.2} : Set (α × α)) := by
      -- Proof comment: a pair outside the order relation has zero matrix weight, so it cannot lie
      -- in the support of the PMF induced by `m`.
      intro z hz
      by_contra hzOrder
      have hzMass : m z.1 z.2 ≠ 0 := by
        have hz' : p z ≠ 0 := by
          simpa [PMF.support] using hz
        simpa [p] using hz'
      exact hzMass (hSupport z.1 z.2 hzOrder)
    -- Proof comment: for PMFs, support containment in a measurable set is equivalent to that set
    -- having probability `1`.
    change p.toMeasure ({z : α × α | z.1 ≤ z.2} : Set (α × α)) = 1
    exact
      (PMF.toMeasure_apply_eq_one_iff
        (p := p)
        (s := ({z : α × α | z.1 ≤ z.2} : Set (α × α)))
        (hs := (Set.toFinite _).measurableSet)).2 hSupportSubset

/-- Helper for Theorem 17.58: a raw ordered row kernel with the correct real second marginal
packages into the existing finite `ENNReal` coupling interface. -/
private lemma existsOrderedCoupling_of_orderedRowKernel
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (K : α → α → ℝ)
    (hK : K ∈ orderedRowKernelSet (α := α))
    (hSecond :
      orderedSecondMarginalMap (fun a ↦ ((ν1 : Measure α) {a}).toReal) K =
        fun b ↦ ((ν2 : Measure α) {b}).toReal) :
    ∃ ψ : ProbabilityMeasure (α × α),
      IsCoupling ψ ν1 ν2 ∧
        (ψ : Measure (α × α)) {z | z.1 ≤ z.2} = 1 := by
  classical
  let p : α → ℝ := fun a ↦ ((ν1 : Measure α) {a}).toReal
  let m : α → α → ENNReal := fun a b ↦ ENNReal.ofReal (p a * K a b)
  have hRow_nonneg : ∀ a b, 0 ≤ K a b := by
    intro a b
    exact (mem_stdSimplex_of_mem_orderedRowKernelSet (hK := hK) a).1 b
  have hRows :
      ∀ a : α, (∑ b : α, m a b) = (ν1 : Measure α) {a} := by
    intro a
    -- Proof comment: each row is the singleton mass `p a` times a simplex row, so the row sum
    -- recovers the first marginal atom exactly.
    calc
      ∑ b : α, m a b = ∑ b : α, ENNReal.ofReal (p a * K a b) := by
        rfl
      _ = ENNReal.ofReal (∑ b : α, p a * K a b) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg fun b _ ↦
              mul_nonneg (by simp [p]) (hRow_nonneg a b)
      _ = ENNReal.ofReal (p a * ∑ b : α, K a b) := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal (p a) := by
            rw [(mem_stdSimplex_of_mem_orderedRowKernelSet (hK := hK) a).2, mul_one]
      _ = (ν1 : Measure α) {a} := by
            simp [p]
  have hCols :
      ∀ b : α, (∑ a : α, m a b) = (ν2 : Measure α) {b} := by
    intro b
    have hSecond_b :
        ∑ a : α, p a * K a b = ((ν2 : Measure α) {b}).toReal := by
      simpa [orderedSecondMarginalMap, p] using congrArg (fun f : α → ℝ ↦ f b) hSecond
    -- Proof comment: the prescribed real second marginal converts termwise to the target
    -- singleton mass because every summand is nonnegative.
    calc
      ∑ a : α, m a b = ∑ a : α, ENNReal.ofReal (p a * K a b) := by
        rfl
      _ = ENNReal.ofReal (∑ a : α, p a * K a b) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg fun a _ ↦
              mul_nonneg (by simp [p]) (hRow_nonneg a b)
      _ = ENNReal.ofReal (((ν2 : Measure α) {b}).toReal) := by rw [hSecond_b]
      _ = (ν2 : Measure α) {b} := by
            simp
  have hMass : (∑ a : α, ∑ b : α, m a b) = 1 := by
    -- Proof comment: summing the row identities reconstructs the full mass of `ν1`.
    calc
      ∑ a : α, ∑ b : α, m a b = ∑ a : α, (ν1 : Measure α) {a} := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        exact hRows a
      _ = 1 := sum_singletonMass_eq_one_finite (ν := ν1)
  have hSupport : ∀ a b : α, ¬ a ≤ b → m a b = 0 := by
    intro a b hab
    -- Proof comment: off the order relation the raw kernel already vanishes, so the packaged
    -- `ENNReal` matrix also vanishes.
    simp [m, eq_zero_of_mem_orderedRowKernelSet (hK := hK) hab]
  exact existsOrderedCoupling_of_weightMatrix
    (ν1 := ν1) (ν2 := ν2) m hMass hRows hCols hSupport

/-- Helper for Theorem 17.58: on a finite partial order, Hall inequalities on singleton masses
imply the equivalent lower-set mass inequalities. -/
private lemma lowerSetLE_of_hallSingletonMass_finite
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hHall :
      ∀ A : Finset α,
        Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) ≤
          (ν2 : Measure α) {b | ∃ a ∈ A, a ≤ b}) :
    ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D := by
  classical
  intro D hD
  let A : Finset α := Finset.univ.filter fun a ↦ a ∉ D
  have hUpperClosure :
      {b : α | ∃ a ∈ A, a ≤ b} = Dᶜ := by
    -- Proof comment: the complement of a lower set is upper, so its upward closure is itself.
    ext b
    constructor
    · intro hb
      rcases hb with ⟨a, haA, hab⟩
      have ha_not_mem : a ∉ D := (Finset.mem_filter.mp haA).2
      intro hbD
      exact ha_not_mem (hD hab hbD)
    · intro hb
      exact ⟨b, by simpa [A] using hb, le_rfl⟩
  have hHallComp :
      (ν1 : Measure α) Dᶜ ≤ (ν2 : Measure α) Dᶜ := by
    -- Proof comment: apply Hall to the finite complement of `D` and rewrite both sides using the
    -- atomic decomposition of finite probability measures.
    calc
      (ν1 : Measure α) Dᶜ
          = ∑ a : α, (Dᶜ).indicator (fun a ↦ (ν1 : Measure α) {a}) a := by
              rw [measure_apply_eq_sum_indicator_singleton (μ := (ν1 : Measure α)) (s := Dᶜ)]
      _ = Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) := by
          simpa [A, Set.indicator] using
            (Finset.sum_filter
              (s := Finset.univ)
              (f := fun a : α ↦ (ν1 : Measure α) {a})
              (p := fun a ↦ a ∉ D)).symm
      _ ≤ (ν2 : Measure α) {b | ∃ a ∈ A, a ≤ b} := hHall A
      _ = (ν2 : Measure α) Dᶜ := by rw [hUpperClosure]
  have hD_meas : MeasurableSet D := (Set.toFinite D).measurableSet
  have hD_compl_meas : MeasurableSet Dᶜ := hD_meas.compl
  -- Proof comment: complement probabilities sum to `1`, so the complement inequality reverses to
  -- the desired lower-set inequality.
  calc
    (ν2 : Measure α) D = 1 - (ν2 : Measure α) Dᶜ := by
      simpa [compl_compl] using
        (MeasureTheory.prob_compl_eq_one_sub (μ := (ν2 : Measure α)) (s := Dᶜ) hD_compl_meas)
    _ ≤ 1 - (ν1 : Measure α) Dᶜ := tsub_le_tsub_left hHallComp 1
    _ = (ν1 : Measure α) D := by
      simpa [compl_compl] using
        (MeasureTheory.prob_compl_eq_one_sub (μ := (ν1 : Measure α)) (s := Dᶜ) hD_compl_meas).symm

/-- Helper for Theorem 17.58: lower-set inequalities are equivalent, by complement, to the
corresponding upper-set inequalities on a finite probability space. -/
private lemma upperSetLE_of_lowerSetLE_finite
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hLower :
      ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D) :
    ∀ U : Set α, IsUpperSet U → (ν1 : Measure α) U ≤ (ν2 : Measure α) U := by
  intro U hU
  have hLowerCompl :
      (ν2 : Measure α) Uᶜ ≤ (ν1 : Measure α) Uᶜ := by
    -- Proof comment: the complement of an upper set is lower, so the given hypothesis applies
    -- directly after swapping to complements.
    exact hLower Uᶜ fun x y hxy hyU ↦ by
      intro hxU
      exact hyU (hU hxy hxU)
  have hU_meas : MeasurableSet U := (Set.toFinite U).measurableSet
  have hU_compl_meas : MeasurableSet Uᶜ := hU_meas.compl
  -- Proof comment: complement probabilities sum to `1`, so the lower-set inequality on `Uᶜ`
  -- reverses to the desired upper-set inequality on `U`.
  calc
    (ν1 : Measure α) U = 1 - (ν1 : Measure α) Uᶜ := by
      simpa [compl_compl] using
        (MeasureTheory.prob_compl_eq_one_sub (μ := (ν1 : Measure α)) (s := Uᶜ) hU_compl_meas)
    _ ≤ 1 - (ν2 : Measure α) Uᶜ := tsub_le_tsub_left hLowerCompl 1
    _ = (ν2 : Measure α) U := by
      simpa [compl_compl] using
        (MeasureTheory.prob_compl_eq_one_sub (μ := (ν2 : Measure α)) (s := Uᶜ) hU_compl_meas).symm

/-- Helper for Theorem 17.58: either a proper nonempty lower set is already tight, or every
proper nonempty lower set is strictly slack. -/
private lemma properTightLowerSet_or_allProperLowerSetsStrict
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hLower :
      ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D) :
    (∃ D : Set α,
        IsLowerSet D ∧ D.Nonempty ∧ D ≠ Set.univ ∧
          (ν2 : Measure α) D = (ν1 : Measure α) D) ∨
      ∀ D : Set α, IsLowerSet D → D.Nonempty → D ≠ Set.univ →
        (ν2 : Measure α) D < (ν1 : Measure α) D := by
  classical
  by_cases hTight :
      ∃ D : Set α,
        IsLowerSet D ∧ D.Nonempty ∧ D ≠ Set.univ ∧
          (ν2 : Measure α) D = (ν1 : Measure α) D
  · exact Or.inl hTight
  · refine Or.inr ?_
    intro D hD hDne hDproper
    have hle : (ν2 : Measure α) D ≤ (ν1 : Measure α) D := hLower D hD
    have hne :
        (ν2 : Measure α) D ≠ (ν1 : Measure α) D := by
      intro hEq
      exact hTight ⟨D, hD, hDne, hDproper, hEq⟩
    exact lt_of_le_of_ne hle hne

/-- Helper for Theorem 17.58: every coupling spends at least the lower-set mass gap on the
off-order region. -/
private lemma lowerSetGap_le_offOrderMass_of_isCoupling
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    {ψ : ProbabilityMeasure (α × α)}
    (hCoupling : IsCoupling ψ ν1 ν2)
    (D : Set α) (hD : IsLowerSet D) :
    (ν2 : Measure α) D ≤
      (ν1 : Measure α) D +
        (ψ : Measure (α × α)) {z | ¬ z.1 ≤ z.2} := by
  classical
  rcases (isCoupling_iff ψ ν1 ν2).1 hCoupling with ⟨hfst, hsnd⟩
  let B : Set (α × α) := {z | z.2 ∈ D}
  let A : Set (α × α) := {z | z.1 ∈ D}
  let Bad : Set (α × α) := {z | z.1 ∉ D ∧ z.2 ∈ D}
  have hA_meas : MeasurableSet A := (Set.toFinite A).measurableSet
  have hB_meas : MeasurableSet B := (Set.toFinite B).measurableSet
  have hBad_meas : MeasurableSet Bad := (Set.toFinite Bad).measurableSet
  have hA_union :
      B ⊆ A ∪ Bad := by
    intro z hz
    by_cases hzA : z.1 ∈ D
    · exact Or.inl hzA
    · exact Or.inr ⟨hzA, hz⟩
  have hBad_subset :
      Bad ⊆ ({z : α × α | ¬ z.1 ≤ z.2} : Set (α × α)) := by
    intro z hz
    rcases hz with ⟨hzNotD, hzD⟩
    intro hzle
    exact hzNotD (hD hzle hzD)
  have hfst_apply :
      (ν1 : Measure α) D = (ψ : Measure (α × α)) A := by
    -- Proof comment: rewrite the first marginal mass as the mass of the first-coordinate fiber.
    have hEq :
        Measure.map Prod.fst (ψ : Measure (α × α)) = (ν1 : Measure α) := by
      exact congrArg (fun ρ : ProbabilityMeasure α ↦ (ρ : Measure α)) hfst
    calc
      (ν1 : Measure α) D = Measure.map Prod.fst (ψ : Measure (α × α)) D := by rw [hEq.symm]
      _ = (ψ : Measure (α × α)) A := by
            rw [Measure.map_apply measurable_fst (Set.toFinite D).measurableSet]
            rfl
  have hsnd_apply :
      (ν2 : Measure α) D = (ψ : Measure (α × α)) B := by
    -- Proof comment: the same rewriting identifies the second marginal with the second-coordinate
    -- fiber over `D`.
    have hEq :
        Measure.map Prod.snd (ψ : Measure (α × α)) = (ν2 : Measure α) := by
      exact congrArg (fun ρ : ProbabilityMeasure α ↦ (ρ : Measure α)) hsnd
    calc
      (ν2 : Measure α) D = Measure.map Prod.snd (ψ : Measure (α × α)) D := by rw [hEq.symm]
      _ = (ψ : Measure (α × α)) B := by
            rw [Measure.map_apply measurable_snd (Set.toFinite D).measurableSet]
            rfl
  -- Proof comment: any point with second coordinate in `D` either already has first coordinate in
  -- `D`, or it contributes to the bad off-order region.
  calc
    (ν2 : Measure α) D = (ψ : Measure (α × α)) B := hsnd_apply
    _ ≤ (ψ : Measure (α × α)) A + (ψ : Measure (α × α)) Bad := by
          exact le_trans (measure_mono hA_union) (measure_union_le _ _)
    _ ≤ (ψ : Measure (α × α)) A +
          (ψ : Measure (α × α)) ({z : α × α | ¬ z.1 ≤ z.2} : Set (α × α)) := by
            exact add_le_add le_rfl (measure_mono hBad_subset)
    _ = (ν1 : Measure α) D +
          (ψ : Measure (α × α)) ({z : α × α | ¬ z.1 ≤ z.2} : Set (α × α)) := by
            rw [hfst_apply]

/-- Helper for Theorem 17.58: the finite core should now be solved directly in lower-set form,
which matches the compiled lower-closure extractor API. -/
private lemma existsOrderedCoupling_finite_of_lowerSetLE
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hLower :
      ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D) :
    ∃ ψ : ProbabilityMeasure (α × α),
      IsCoupling ψ ν1 ν2 ∧
        (ψ : Measure (α × α)) {z | z.1 ≤ z.2} = 1 := by
  classical
  have hUpper :
      ∀ U : Set α, IsUpperSet U → (ν1 : Measure α) U ≤ (ν2 : Measure α) U :=
    upperSetLE_of_lowerSetLE_finite (ν1 := ν1) (ν2 := ν2) hLower
  have hMonotoneReal :
      ∀ {g : α → ℝ}, Monotone g →
        ∑ a : α, ((ν1 : Measure α) {a}).toReal * g a ≤
          ∑ a : α, ((ν2 : Measure α) {a}).toReal * g a := by
    -- Proof comment: the finite owner proof has now been upgraded from indicator tests to all
    -- monotone real tests, which is the correct functional input for the convex-geometry route.
    intro g hg
    exact monotoneExpectationLE_of_upperSetLE_finiteReal
      (ν1 := ν1) (ν2 := ν2) hUpper hg
  let p : α → ℝ := fun a ↦ ((ν1 : Measure α) {a}).toReal
  let q : α → ℝ := fun b ↦ ((ν2 : Measure α) {b}).toReal
  have hq_nonneg : ∀ b, 0 ≤ q b := by
    intro b
    simp [q]
  have hMonotoneKernel :
      ∀ {g : α → ℝ}, Monotone g →
        ∑ a : α, p a * g a ≤ ∑ b : α, q b * g b := by
    intro g hg
    -- Proof comment: the previously established monotone real test inequality already has the
    -- exact singleton-mass form needed by the ordered-kernel support theorem.
    simpa [p, q] using hMonotoneReal (g := g) hg
  -- Route correction: the failed lower-closure subtraction route has been replaced by the compact
  -- ordered-kernel image route. The only remaining work is now short assembly: realize the raw
  -- kernel from monotone tests, then package it back into an `ENNReal` coupling.
  obtain ⟨K, hK, hSecond⟩ :=
    existsOrderedRowKernel_of_monotoneLE (α := α) p q hq_nonneg
      (by
        intro g hg
        exact hMonotoneKernel hg)
  -- Proof comment: once the raw kernel has the right second marginal and ordered support, the
  -- finite `ENNReal` packager produces the desired coupling immediately.
  exact existsOrderedCoupling_of_orderedRowKernel
    (ν1 := ν1) (ν2 := ν2) K hK (by simpa [p, q] using hSecond)

/-- Helper for Theorem 17.58: once the finite Hall inequalities are expressed on singleton masses,
the missing raw matrix theorem packages directly into a finite ordered coupling. -/
private lemma existsOrderedCoupling_finite_of_hall
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    [PartialOrder α]
    {ν1 ν2 : ProbabilityMeasure α}
    (hHall :
      ∀ A : Finset α,
        Finset.sum A (fun a ↦ (ν1 : Measure α) {a}) ≤
          (ν2 : Measure α) {b | ∃ a ∈ A, a ≤ b}) :
    ∃ ψ : ProbabilityMeasure (α × α),
      IsCoupling ψ ν1 ν2 ∧
        (ψ : Measure (α × α)) {z | z.1 ≤ z.2} = 1 := by
  classical
  have hLower :
      ∀ D : Set α, IsLowerSet D → (ν2 : Measure α) D ≤ (ν1 : Measure α) D :=
    lowerSetLE_of_hallSingletonMass_finite (ν1 := ν1) (ν2 := ν2) hHall
  -- Proof comment: the Hall inequalities are now normalized to the lower-set formulation that
  -- matches the compiled finite lower-closure API.
  exact existsOrderedCoupling_finite_of_lowerSetLE (ν1 := ν1) (ν2 := ν2) hLower

/-- Helper for Theorem 17.58: clip the floor mesh `(n + 1)⁻¹ ℤ` to the bounded interval
`[-(n + 1), n + 1]`. This keeps the scalar quantizer monotone while making its image finite. -/
private def scalarClipFloorQuantizer (n : ℕ) : ℝ → ℝ :=
  let m : ℕ := n + 1
  fun x ↦
    ((max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋) : ℤ) : ℝ) / m

/-- Helper for Theorem 17.58: the clipped scalar floor quantizer is measurable. -/
private lemma measurable_scalarClipFloorQuantizer (n : ℕ) :
    Measurable (scalarClipFloorQuantizer n) := by
  let m : ℕ := n + 1
  have hfloor : Measurable fun x : ℝ ↦ (⌊(m : ℝ) * x⌋ : ℤ) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_id)
  have hclip : Measurable fun x : ℝ ↦
      max (-((m : ℤ) * m)) (min ((m : ℤ) * m) (⌊(m : ℝ) * x⌋ : ℤ)) := by
    -- Proof comment: clamp the floor index between two fixed integer endpoints before casting.
    exact measurable_const.max (measurable_const.min hfloor)
  -- Proof comment: after clamping in the integer world, only the final cast and rescaling remain.
  simpa [scalarClipFloorQuantizer, m] using
    ((measurable_of_countable (fun k : ℤ ↦ (k : ℝ))).comp hclip).div_const m

/-- Helper for Theorem 17.58: the clipped scalar floor quantizer is monotone. -/
private lemma scalarClipFloorQuantizer_monotone (n : ℕ) :
    Monotone (scalarClipFloorQuantizer n) := by
  let m : ℕ := n + 1
  intro x y hxy
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hfloor :
      (⌊(m : ℝ) * x⌋ : ℤ) ≤ ⌊(m : ℝ) * y⌋ := by
    exact Int.floor_mono (mul_le_mul_of_nonneg_left hxy hm_nonneg)
  have hclamp :
      max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋) ≤
        max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * y⌋) := by
    -- Proof comment: both the integer clamp and the final rescaling preserve the order.
    exact max_le_max le_rfl (min_le_min le_rfl hfloor)
  have hclamp_real :
      (((max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋) : ℤ) : ℝ)) ≤
        (((max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * y⌋) : ℤ) : ℝ)) := by
    exact_mod_cast hclamp
  simpa [scalarClipFloorQuantizer, m] using
    (div_le_div_of_nonneg_right hclamp_real hm_nonneg)

/-- Helper for Theorem 17.58: the clipped scalar floor quantizer takes only finitely many values. -/
private lemma scalarClipFloorQuantizer_range_finite (n : ℕ) :
    (Set.range (scalarClipFloorQuantizer n)).Finite := by
  let m : ℕ := n + 1
  refine
    (Set.finite_Icc (-((m : ℤ) * m)) ((m : ℤ) * m)).image
      (fun k : ℤ ↦ (k : ℝ) / m) |>.subset ?_
  rintro y ⟨x, rfl⟩
  have hm_nonneg : 0 ≤ (m : ℤ) * m := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le m) (by exact_mod_cast Nat.zero_le m)
  refine ⟨max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋), ?_, ?_⟩
  · -- Proof comment: the integer clamp lands in the explicit finite interval by construction.
    refine Set.mem_Icc.mpr ⟨le_max_left _ _, ?_⟩
    refine max_le_iff.mpr ⟨?_, min_le_left _ _⟩
    linarith
  · rfl

/-- Helper for Theorem 17.58: quantize each coordinate separately using the monotone clipped floor
quantizer. -/
private def coordGridQuantizer (d n : ℕ) : (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x i ↦ scalarClipFloorQuantizer n (x i)

/-- Helper for Theorem 17.58: the coordinatewise quantizer is measurable. -/
private lemma measurable_coordGridQuantizer (d n : ℕ) :
    Measurable (coordGridQuantizer d n) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  -- Proof comment: each coordinate is just the scalar quantizer applied after evaluation.
  simpa [coordGridQuantizer] using
    (measurable_scalarClipFloorQuantizer n).comp (continuous_apply i).measurable

/-- Helper for Theorem 17.58: coordinatewise quantization preserves the product order. -/
private lemma coordGridQuantizer_monotone (d n : ℕ) :
    Monotone (coordGridQuantizer d n) := by
  intro x y hxy i
  -- Proof comment: monotonicity reduces coordinatewise to the scalar clipped floor quantizer.
  exact scalarClipFloorQuantizer_monotone n (hxy i)

/-- Helper for Theorem 17.58: the coordinatewise quantizer has finite image because each
coordinate has finite image. -/
private lemma coordGridQuantizer_range_finite (d n : ℕ) :
    (Set.range (coordGridQuantizer d n)).Finite := by
  let s : Fin d → Set ℝ := fun _ ↦ Set.range (scalarClipFloorQuantizer n)
  have hs : ∀ i, (s i).Finite := fun _ ↦ scalarClipFloorQuantizer_range_finite n
  refine (Set.Finite.pi hs).subset ?_
  rintro y ⟨x, rfl⟩
  simp [Set.mem_pi, s, coordGridQuantizer]

/-- Helper for Theorem 17.58: the finite image of the coordinate quantizer, viewed as a subtype.
-/
private abbrev quantizedRange (d n : ℕ) : Set (Fin d → ℝ) :=
  Set.range (coordGridQuantizer d n)

/-- Helper for Theorem 17.58: the coordinate quantizer can be viewed as a measurable map into its
finite image subtype. -/
private def quantizedRangeMap (d n : ℕ) (x : Fin d → ℝ) : quantizedRange d n :=
  ⟨coordGridQuantizer d n x, ⟨x, rfl⟩⟩

/-- Helper for Theorem 17.58: the subtype-valued quantizer is measurable. -/
private lemma measurable_quantizedRangeMap (d n : ℕ) :
    Measurable (quantizedRangeMap d n) := by
  -- Proof comment: this is just the measurable quantizer together with the tautological proof
  -- that its values land in the declared range subtype.
  simpa [quantizedRangeMap] using
    (measurable_coordGridQuantizer d n).subtype_mk (h := fun x ↦ ⟨x, rfl⟩)

/-- Helper for Theorem 17.58: forgetting the quantized-range subtype recovers the ambient
quantized pushforward law. -/
private lemma map_quantizedRangeLaw_val {d n : ℕ}
    (μ : ProbabilityMeasure (Fin d → ℝ)) :
    ((μ.map (measurable_quantizedRangeMap d n).aemeasurable).map
      measurable_subtype_coe.aemeasurable : ProbabilityMeasure (Fin d → ℝ)) =
      μ.map (measurable_coordGridQuantizer d n).aemeasurable := by
  -- Proof comment: after mapping into the range subtype, applying `Subtype.val` is literally the
  -- original coordinate quantizer again.
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Subtype.val
      (Measure.map (quantizedRangeMap d n) (μ : Measure (Fin d → ℝ))) =
    Measure.map (coordGridQuantizer d n) (μ : Measure (Fin d → ℝ))
  simpa [quantizedRangeMap, Function.comp] using
    (Measure.map_map measurable_subtype_coe (measurable_quantizedRangeMap d n)
      (μ := (μ : Measure (Fin d → ℝ))))

/-- Helper for Theorem 17.58: the indicator of an upper set is a monotone `{0,1}`-valued test
function. -/
private lemma monotone_indicator_one_of_isUpperSet {α : Type*} [Preorder α]
    {U : Set α} (hU : IsUpperSet U) :
    Monotone (U.indicator fun _ ↦ (1 : ℝ)) := by
  intro a b hab
  by_cases ha : a ∈ U
  · have hb : b ∈ U := hU hab ha
    simp [Set.indicator_of_mem, ha, hb]
  · have hnonneg : 0 ≤ U.indicator (fun _ ↦ (1 : ℝ)) b := by
      by_cases hb : b ∈ U
      · simp [Set.indicator_of_mem, hb]
      · simp [Set.indicator_of_notMem, hb]
    simpa [Set.indicator_of_notMem, ha] using hnonneg

/-- Helper for Theorem 17.58: stochastic order of the ambient quantized laws gives upper-set mass
inequalities on the finite quantized image subtype. -/
private lemma upperSetLE_of_stochasticLE_quantizedRange {d n : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    (hStochastic :
      StochasticLE
        (μ1.map (measurable_coordGridQuantizer d n).aemeasurable)
        (μ2.map (measurable_coordGridQuantizer d n).aemeasurable)) :
    let s := quantizedRange d n
    let ν1 : ProbabilityMeasure s := μ1.map (measurable_quantizedRangeMap d n).aemeasurable
    let ν2 : ProbabilityMeasure s := μ2.map (measurable_quantizedRangeMap d n).aemeasurable
    ∀ U : Set s, IsUpperSet U → (ν1 : Measure s) U ≤ (ν2 : Measure s) U := by
  intro s ν1 ν2 U hU
  letI : Fintype s := (coordGridQuantizer_range_finite d n).fintype
  let A : Set (Fin d → ℝ) := {x | ∃ u : s, u ∈ U ∧ (u : Fin d → ℝ) ≤ x}
  have hA_upper : IsUpperSet A := by
    -- Proof comment: once `x` dominates some `u ∈ U`, every larger `y` still dominates that same
    -- witness, so the ambient extension stays upper.
    intro x y hxy hx
    rcases hx with ⟨u, huU, hux⟩
    exact ⟨u, huU, le_trans hux hxy⟩
  have hA_meas : MeasurableSet A := by
    -- Proof comment: because the quantized range subtype is finite, the ambient upper extension
    -- is a finite union of closed upper orthants.
    have hA_union :
        A = ⋃ u ∈ U, Set.Ici (u : Fin d → ℝ) := by
      ext x
      simp [A]
    rw [hA_union]
    exact (Set.toFinite U).measurableSet_biUnion fun _ _ ↦ isClosed_Ici.measurableSet
  let f : (Fin d → ℝ) → ℝ := A.indicator (fun _ ↦ (1 : ℝ))
  have hf_mono : Monotone f := by
    -- Proof comment: the upper-set extension was chosen exactly so that its indicator is a valid
    -- monotone stochastic-order test function.
    simpa [f] using monotone_indicator_one_of_isUpperSet hA_upper
  have hf_bdd : Bornology.IsBounded (Set.range f) := by
    have hsubset : Set.range f ⊆ ({0, 1} : Set ℝ) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      by_cases hx : x ∈ A
      · simp [f, Set.indicator_of_mem, hx]
      · simp [f, Set.indicator_of_notMem, hx]
    exact (Set.toFinite ({0, 1} : Set ℝ)).isBounded.subset hsubset
  have hf_meas : Measurable f := by
    -- Proof comment: the indicator is measurable because the finite ambient upper extension is a
    -- measurable set.
    simpa [f] using measurable_const.indicator hA_meas
  have hIndicatorIneq := hStochastic hf_mono hf_bdd hf_meas
  have hpreimage :
      quantizedRangeMap d n ⁻¹' U = coordGridQuantizer d n ⁻¹' A := by
    -- Proof comment: on points in the quantized image, the ambient upper extension `A` records
    -- exactly the same membership information as the original subtype upper set `U`.
    ext x
    constructor
    · intro hx
      exact ⟨quantizedRangeMap d n x, hx, le_rfl⟩
    · intro hx
      rcases hx with ⟨u, huU, huqx⟩
      exact hU huqx huU
  have hApply1 :
      (ν1 : Measure s) U =
        (((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) A := by
    -- Proof comment: the subtype-valued quantized law and the ambient quantized law see the same
    -- event once `U` is replaced by its ambient upper extension.
    calc
      (ν1 : Measure s) U = (μ1 : Measure (Fin d → ℝ)) ((quantizedRangeMap d n) ⁻¹' U) := by
        rw [show (ν1 : Measure s) = Measure.map (quantizedRangeMap d n)
          (μ1 : Measure (Fin d → ℝ)) by rfl]
        rw [Measure.map_apply (measurable_quantizedRangeMap d n) ((Set.toFinite U).measurableSet)]
      _ = (μ1 : Measure (Fin d → ℝ)) ((coordGridQuantizer d n) ⁻¹' A) := by rw [hpreimage]
      _ =
          (((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) A := by
            rw [show
              (((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
                  ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) =
                Measure.map (coordGridQuantizer d n) (μ1 : Measure (Fin d → ℝ)) by
              rfl]
            symm
            rw [Measure.map_apply (measurable_coordGridQuantizer d n) hA_meas]
  have hApply2 :
      (ν2 : Measure s) U =
        (((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) A := by
    -- Proof comment: the same preimage computation identifies the second quantized law on `U`
    -- with the ambient upper-set event `A`.
    calc
      (ν2 : Measure s) U = (μ2 : Measure (Fin d → ℝ)) ((quantizedRangeMap d n) ⁻¹' U) := by
        rw [show (ν2 : Measure s) = Measure.map (quantizedRangeMap d n)
          (μ2 : Measure (Fin d → ℝ)) by rfl]
        rw [Measure.map_apply (measurable_quantizedRangeMap d n) ((Set.toFinite U).measurableSet)]
      _ = (μ2 : Measure (Fin d → ℝ)) ((coordGridQuantizer d n) ⁻¹' A) := by rw [hpreimage]
      _ =
          (((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) A := by
            rw [show
              (((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
                  ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) =
                Measure.map (coordGridQuantizer d n) (μ2 : Measure (Fin d → ℝ)) by
              rfl]
            symm
            rw [Measure.map_apply (measurable_coordGridQuantizer d n) hA_meas]
  have hIntegral1 :
      ∫ x, f x
        ∂(((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) =
        ((((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)) A).toReal) := by
    -- Proof comment: the `{0,1}`-valued indicator integral is exactly the mass of the target
    -- event for the first quantized law.
    rw [show f = A.indicator (fun _ ↦ (1 : ℝ)) by rfl]
    rw [integral_indicator_const (μ := (((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
      ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))) (1 : ℝ) hA_meas]
    simp [Measure.real_def]
  have hIntegral2 :
      ∫ x, f x
        ∂(((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) =
        ((((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)) A).toReal) := by
    -- Proof comment: the second quantized law has the same indicator-mass identity.
    rw [show f = A.indicator (fun _ ↦ (1 : ℝ)) by rfl]
    rw [integral_indicator_const (μ := (((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
      ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))) (1 : ℝ) hA_meas]
    simp [Measure.real_def]
  have hReal :
      ((ν1 : Measure s) U).toReal ≤ ((ν2 : Measure s) U).toReal := by
    calc
      ((ν1 : Measure s) U).toReal =
          ∫ x, f x
            ∂(((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
                ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
              rw [hApply1]
              exact hIntegral1.symm
      _ ≤ ∫ x, f x
            ∂(((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
                ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := hIndicatorIneq
      _ = ((ν2 : Measure s) U).toReal := by
            rw [hApply2]
            exact hIntegral2
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 hReal

/-- Helper for Theorem 17.58: pushing both marginals forward through the coordinatewise quantizer
preserves stochastic order. -/
private lemma stochasticLE_map_coordGridQuantizer {d n : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    (hStochastic : StochasticLE μ1 μ2) :
    StochasticLE
      (μ1.map (measurable_coordGridQuantizer d n).aemeasurable)
      (μ2.map (measurable_coordGridQuantizer d n).aemeasurable) := by
  intro f hf_mono hf_bdd hf_meas
  let g : (Fin d → ℝ) → ℝ := fun x ↦ f (coordGridQuantizer d n x)
  have hg_mono : Monotone g := by
    intro x y hxy
    exact hf_mono (coordGridQuantizer_monotone d n hxy)
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    refine hf_bdd.subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨coordGridQuantizer d n x, rfl⟩
  have hg_meas : Measurable g := hf_meas.comp (measurable_coordGridQuantizer d n)
  have hineq := hStochastic (f := g) hg_mono hg_bdd hg_meas
  -- Proof comment: stochastic order for the quantized laws is just the original inequality
  -- applied to tests precomposed with the monotone quantizer.
  calc
    ∫ x, f x
        ∂(((μ1.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) =
      ∫ x, g x ∂(μ1 : Measure (Fin d → ℝ)) := by
        simpa [g] using
          (MeasureTheory.integral_map
            (μ := (μ1 : Measure (Fin d → ℝ)))
            (measurable_coordGridQuantizer d n).aemeasurable
            (f := f)
            hf_meas.aestronglyMeasurable)
    _ ≤ ∫ x, g x ∂(μ2 : Measure (Fin d → ℝ)) := hineq
    _ =
      ∫ x, f x
        ∂(((μ2.map (measurable_coordGridQuantizer d n).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
        simpa [g] using
          (MeasureTheory.integral_map
            (μ := (μ2 : Measure (Fin d → ℝ)))
            (measurable_coordGridQuantizer d n).aemeasurable
            (f := f)
            hf_meas.aestronglyMeasurable).symm

/-- Helper for Theorem 17.58: forget the subtype coordinates of a pair by applying `Subtype.val`
to each component. -/
private def subtypeValPair {d : ℕ} {s : Set (Fin d → ℝ)} (z : s × s) :
    (Fin d → ℝ) × (Fin d → ℝ) :=
  (z.1.1, z.2.1)

/-- Helper for Theorem 17.58: the coordinatewise subtype-value pair map is measurable. -/
private lemma measurable_subtypeValPair {d : ℕ} {s : Set (Fin d → ℝ)} :
    Measurable (subtypeValPair (d := d) (s := s)) := by
  -- Proof comment: each coordinate is just `Subtype.val` composed with a product projection.
  exact (measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)

/-- Helper for Theorem 17.58: pushing a coupling on a subtype product through `Subtype.val`
preserves the coupling equations for the ambient pushforward laws. -/
private lemma isCoupling_map_subtypeValPair {d : ℕ} {s : Set (Fin d → ℝ)}
    {μ1 μ2 : ProbabilityMeasure s}
    {ψ : ProbabilityMeasure (s × s)}
    (hCoupling : IsCoupling ψ μ1 μ2) :
    IsCoupling
      (ψ.map measurable_subtypeValPair.aemeasurable)
      (μ1.map measurable_subtype_coe.aemeasurable)
      (μ2.map measurable_subtype_coe.aemeasurable) := by
  rw [isCoupling_iff] at hCoupling ⊢
  rcases hCoupling with ⟨hfst, hsnd⟩
  constructor
  · -- Proof comment: rewrite the first marginal as a composed pushforward and then use the
    -- coupling identity on the subtype-valued first coordinate.
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.fst (Measure.map (subtypeValPair (d := d) (s := s))
      (ψ : Measure (s × s))) =
        (((μ1.map measurable_subtype_coe.aemeasurable : ProbabilityMeasure (Fin d → ℝ)) :
          Measure (Fin d → ℝ)))
    rw [Measure.map_map measurable_fst measurable_subtypeValPair]
    calc
      Measure.map (fun z : s × s ↦ z.1.1) (ψ : Measure (s × s)) =
          Measure.map Subtype.val (Measure.map Prod.fst (ψ : Measure (s × s))) := by
            simpa [subtypeValPair, Function.comp] using
              (Measure.map_map
                (μ := (ψ : Measure (s × s)))
                measurable_subtype_coe measurable_fst).symm
      _ = (((ψ.map measurable_fst.aemeasurable).map measurable_subtype_coe.aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)) := by
            rfl
      _ = (((μ1.map measurable_subtype_coe.aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
            rw [hfst]
  · -- Proof comment: the second marginal is the same computation with `Prod.snd`.
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.snd (Measure.map (subtypeValPair (d := d) (s := s))
      (ψ : Measure (s × s))) =
        (((μ2.map measurable_subtype_coe.aemeasurable : ProbabilityMeasure (Fin d → ℝ)) :
          Measure (Fin d → ℝ)))
    rw [Measure.map_map measurable_snd measurable_subtypeValPair]
    calc
      Measure.map (fun z : s × s ↦ z.2.1) (ψ : Measure (s × s)) =
          Measure.map Subtype.val (Measure.map Prod.snd (ψ : Measure (s × s))) := by
            simpa [subtypeValPair, Function.comp] using
              (Measure.map_map
                (μ := (ψ : Measure (s × s)))
                measurable_subtype_coe measurable_snd).symm
      _ = (((ψ.map measurable_snd.aemeasurable).map measurable_subtype_coe.aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)) := by
            rfl
      _ = (((μ2.map measurable_subtype_coe.aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))) := by
            rw [hsnd]

/-- Helper for Theorem 17.58: forgetting subtype coordinates preserves full mass on the ordered
support event. -/
private lemma orderedMassOne_map_subtypeValPair {d : ℕ} {s : Set (Fin d → ℝ)}
    {ψ : ProbabilityMeasure (s × s)}
    (hOrdered :
      (ψ : Measure (s × s)) {z | z.1 ≤ z.2} = 1) :
    (((ψ.map measurable_subtypeValPair.aemeasurable :
        ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) :
          Measure ((Fin d → ℝ) × (Fin d → ℝ)))
      ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
        Set ((Fin d → ℝ) × (Fin d → ℝ)))) = 1 := by
  have hpreimage :
      subtypeValPair (d := d) (s := s) ⁻¹'
          ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
            Set ((Fin d → ℝ) × (Fin d → ℝ))) =
        ({z : s × s | z.1 ≤ z.2} : Set (s × s)) := by
    -- Proof comment: the subtype order is definitionally the ambient coordinatewise order.
    ext z
    simp [subtypeValPair]
  -- Proof comment: evaluate the mapped measure on the ambient ordered set and rewrite the
  -- corresponding preimage inside the subtype product.
  rw [show
      (((ψ.map measurable_subtypeValPair.aemeasurable :
          ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) : Measure _)
        ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ)))) =
        Measure.map (subtypeValPair (d := d) (s := s)) (ψ : Measure (s × s))
          ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
            Set ((Fin d → ℝ) × (Fin d → ℝ))) by
      rfl]
  rw [Measure.map_apply_of_aemeasurable measurable_subtypeValPair.aemeasurable
    (measurableSet_orderedPairSet d), hpreimage, hOrdered]

/-- Helper for Theorem 17.58: composing a measure on `α × β` with a kernel that only reads the
first coordinate is the same as composing the first marginal with the original kernel. -/
private lemma compProdMkRight_eq_comp_fst
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure (α × β)) (κ : Kernel α γ) :
    (Kernel.prodMkRight β κ) ∘ₘ μ = κ ∘ₘ μ.fst := by
  -- Proof comment: `prodMkRight` is the comap of `κ` along `Prod.fst`, so after reassociating the
  -- composition only the first marginal of `μ` remains.
  calc
    (Kernel.prodMkRight β κ) ∘ₘ μ
        = (κ ∘ₖ Kernel.deterministic Prod.fst measurable_fst) ∘ₘ μ := by
            rw [Kernel.prodMkRight, Kernel.comp_deterministic_eq_comap]
    _ = κ ∘ₘ ((Kernel.deterministic Prod.fst measurable_fst) ∘ₘ μ) := by
          rw [Measure.comp_assoc]
    _ = κ ∘ₘ μ.fst := by
          rw [Measure.deterministic_comp_eq_map]
          rfl

/-- Helper for Theorem 17.58: composing a measure on `α × β` with a kernel that only reads the
second coordinate is the same as composing the second marginal with the original kernel. -/
private lemma compProdMkLeft_eq_comp_snd
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure (α × β)) (κ : Kernel β γ) :
    (Kernel.prodMkLeft α κ) ∘ₘ μ = κ ∘ₘ μ.snd := by
  -- Proof comment: the left-product kernel is the same comap trick, now through `Prod.snd`.
  calc
    (Kernel.prodMkLeft α κ) ∘ₘ μ
        = (κ ∘ₖ Kernel.deterministic Prod.snd measurable_snd) ∘ₘ μ := by
            rw [Kernel.prodMkLeft, Kernel.comp_deterministic_eq_comap]
    _ = κ ∘ₘ ((Kernel.deterministic Prod.snd measurable_snd) ∘ₘ μ) := by
          rw [Measure.comp_assoc]
    _ = κ ∘ₘ μ.snd := by
          rw [Measure.deterministic_comp_eq_map]
          rfl

section finiteFiberLift

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Helper for Theorem 17.58: the normalized restriction of `μ` to the fiber `ρ ⁻¹' {a}`. -/
private def normalizedFiberLaw [Nonempty E]
    (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) : ProbabilityMeasure E :=
  (μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).normalize

/-- Helper for Theorem 17.58: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_apply
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t)
    {s : Set E} (hs : MeasurableSet s) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) *
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E) s)) =
      ((μ : Measure E).restrict (ρ ⁻¹' {a})) s := by
  -- Proof comment: apply the finite-measure identity `mass • normalize = self` on the measurable
  -- set `s`, so the normalization work is paid once at the apply level.
  simpa [normalizedFiberLaw, FiniteMeasure.restrict_measure_eq, hs, smul_eq_mul] using
    congrArg (fun ν : FiniteMeasure E ↦ ((ν : Measure E) s))
      ((MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize
        (μ := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a}))).symm)

/-- Helper for Theorem 17.58: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_eq_restrict
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E))) =
      (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
  -- Proof comment: the whole-measure statement is just extensionality after the apply-level
  -- normalization identity.
  ext s hs
  simpa [smul_eq_mul] using
    fiberMass_smul_normalizedFiberLaw_apply (μ := μ) (ρ := ρ) a hs

/-- Helper for Theorem 17.58: summing the fiberwise normalized restrictions with their fiber
masses reconstructs the original measure. -/
private theorem sum_smul_normalizedFiberLaw_eq
    [Nonempty E] {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) :
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
      (μ : Measure E) := by
  have hpairwise : (Set.univ : Set t).Pairwise
      (Function.onFun Disjoint fun a : t ↦ ρ ⁻¹' {a}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 ?_
    intro x hxa hxb
    have hxa' : ρ x = a := by simpa using hxa
    have hxb' : ρ x = b := by simpa using hxb
    exact hab (hxa'.symm.trans hxb')
  have hrestrict :
      ((μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a})) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
    simpa [FiniteMeasure.restrict_measure_eq] using
      congrArg (fun ν : FiniteMeasure E ↦ (ν : Measure E))
        (MeasureTheory.FiniteMeasure.restrict_biUnion_finset
          (μ := μ.toFiniteMeasure) (T := Finset.univ) (s := fun a : t ↦ ρ ⁻¹' {a})
          (by simpa using hpairwise)
          (fun a ↦ hρmeas (measurableSet_singleton a)))
  have hUnion :
      (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) = Set.univ := by
    ext x
    simp
  calc
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using fiberMass_smul_normalizedFiberLaw_eq_restrict (μ := μ) (ρ := ρ) a
    _ = (μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) := by
      simpa using hrestrict.symm
    _ = (μ : Measure E) := by
      rw [hUnion, Measure.restrict_univ]

/-- Helper for Theorem 17.58: a measurable finite-range map pushes a probability measure forward
to a probability measure on its finite image subtype. -/
private abbrev representativeMapLaw
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) :
    ProbabilityMeasure t :=
  μ.map (f := ρ) hρmeas.aemeasurable

/-- Helper for Theorem 17.58: the singleton masses of a finite coupling are the row and column
totals of its atom masses. -/
private theorem mapCouplingSingletonMarginals {t : Set E} [Fintype t]
    {P Q : ProbabilityMeasure E} {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    (∀ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a})) ∧
      (∀ b : t, ∑ a : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b})) := by
  rcases hν with ⟨hfst, hsnd⟩
  constructor
  · intro a
    -- Proof comment: evaluate the first marginal identity on `{a}` and rewrite the preimage
    -- under `Prod.fst` as the finite row sum of singleton masses.
    have hfstApply :
        (Measure.map Prod.fst (ν : Measure (t × t))) {a} =
          ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) := by
      rw [Measure.map_apply measurable_fst (measurableSet_singleton a)]
      simpa using
        (MeasureTheory.measure_preimage_fst_singleton_eq_sum
          (μ := (ν : Measure (t × t))) a)
    have hfstSingleton := congrArg (fun μ : Measure t ↦ μ {a}) hfst
    exact hfstApply.symm.trans hfstSingleton
  · intro b
    -- Proof comment: the second marginal identity gives the analogous column-sum formula.
    have hsndApply :
        (Measure.map Prod.snd (ν : Measure (t × t))) {b} =
          ∑ a : t, ((ν : Measure (t × t)) {(a, b)}) := by
      rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
      simpa using
        (MeasureTheory.measure_preimage_snd_singleton_eq_sum
          (μ := (ν : Measure (t × t))) b)
    have hsndSingleton := congrArg (fun μ : Measure t ↦ μ {b}) hsnd
    exact hsndApply.symm.trans hsndSingleton

/-- Helper for Theorem 17.58: the mass of a fiber equals the singleton mass of the pushforward
measure at the corresponding image point. -/
private theorem fiberMass_eq_mapSingleton
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
      (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
  -- Proof comment: the restricted finite measure has fiber mass equal to the singleton mass of
  -- the corresponding pushforward atom.
  calc
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
        ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
      simpa using congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
        ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))
    _ = (μ : Measure E) (ρ ⁻¹' {a}) := by
      simp
    _ = (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
      symm
      simpa [representativeMapLaw] using
        (MeasureTheory.ProbabilityMeasure.map_apply' (ν := μ) (f := ρ) hρmeas.aemeasurable
          (A := {a}) (measurableSet_singleton a))

/-- Helper for Theorem 17.58: a coupling of finite pushforwards induces a finite sum of product
fiber laws on `E × E`. -/
private def liftedMapCoupling [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) (ρ : E → t) (ν : ProbabilityMeasure (t × t)) :
    Measure (E × E) :=
  ∑ a : t, ∑ b : t,
    (((ν : Measure (t × t)) {(a, b)}) •
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))))

/-- Helper for Theorem 17.58: the lifted finite-cell coupling has first marginal `P`. -/
private theorem liftedMapCoupling_fst_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν) = (P : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, _⟩
  -- Proof comment: `Prod.fst` collapses each product cell to its first fiber because the second
  -- factor is a probability measure of total mass `1`.
  calc
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_fst_prod]
    _ = ∑ a : t, (∑ b : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ a : t, (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a}) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [hrows a]
    _ = ∑ a : t, (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a]
    _ = (P : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := P) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.58: the lifted finite-cell coupling has second marginal `Q`. -/
private theorem liftedMapCoupling_snd_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν) = (Q : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨_, hcols⟩
  -- Proof comment: the second marginal is the symmetric column-sum version of the first one.
  calc
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_snd_prod]
    _ = ∑ b : t, ∑ a : t,
          ((ν : Measure (t × t)) {(a, b)}) •
            (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [Finset.sum_comm]
    _ = ∑ b : t, (∑ a : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ b : t, (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b}) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [hcols b]
    _ = ∑ b : t, (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b]
    _ = (Q : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := Q) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.58: inside the fiber of `a`, the preimage of a set `s` containing `a`
is the whole fiber. -/
private theorem preimage_inter_fiber_eq_fiber_of_mem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∈ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = ρ ⁻¹' {a} := by
  -- Proof comment: every point in the fiber already maps to `a`, so membership in `s` is
  -- automatic once `a ∈ s`.
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hxEq : ρ x = a := by
      simpa using hx
    refine ⟨?_, hx⟩
    simpa [hxEq] using hsa

/-- Helper for Theorem 17.58: if `a ∉ s`, then the preimage of `s` is disjoint from the fiber of
`a`. -/
private theorem preimage_inter_fiber_eq_empty_of_notMem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∉ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = (∅ : Set E) := by
  -- Proof comment: a point cannot simultaneously map to `a` and to a set excluding `a`.
  ext x
  constructor
  · intro hx
    have hxEq : ρ x = a := by
      simpa using hx.2
    have ha_mem : a ∈ s := by
      simpa [hxEq] using hx.1
    exact (hsa ha_mem).elim
  · intro hx
    simp at hx

/-- Helper for Theorem 17.58: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    {s : Set t} (hs : MeasurableSet s) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) s =
      Measure.dirac a s := by
  let ν : FiniteMeasure E := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})
  have hmass :
      (μ : Measure E) (ρ ⁻¹' {a}) = ((ν.mass : ℝ≥0∞)) := by
    -- Proof comment: the fiber mass is exactly the mass of the restricted finite measure.
    calc
      (μ : Measure E) (ρ ⁻¹' {a}) = ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
        simp
      _ = ((ν.mass : ℝ≥0∞)) := by
        simpa [ν] using
          (congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
            ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))).symm
  have hν_ne : ν ≠ 0 := by
    -- Proof comment: positive fiber mass rules out the zero finite measure, so normalization
    -- reduces to inverse-mass scaling of the restricted fiber measure.
    intro hν
    have hν_mass_zero : ((ν.mass : ℝ≥0∞)) = 0 := by
      simpa [hν]
    exact ha <| by simpa [hmass] using hν_mass_zero
  rw [Measure.map_apply hρmeas hs]
  rw [normalizedFiberLaw, ν.toMeasure_normalize_eq_of_nonzero hν_ne, Measure.smul_apply]
  rw [show ((ν : Measure E) (ρ ⁻¹' s)) = ((μ : Measure E).restrict (ρ ⁻¹' {a}) (ρ ⁻¹' s)) by
        rfl]
  rw [Measure.restrict_apply (hρmeas hs)]
  by_cases hsa : a ∈ s
  · rw [preimage_inter_fiber_eq_fiber_of_mem hsa, hmass]
    have hν_mass_nnreal_ne : ν.mass ≠ 0 := by
      exact (MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne
    have hν_mass_ne : ((ν.mass : ℝ≥0∞)) ≠ 0 := by
      exact ENNReal.coe_ne_zero.2 ((MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne)
    have hν_univ_eq : ((ν : Measure E) Set.univ) = ((ν.mass : ℝ≥0∞)) := by
      simpa using (MeasureTheory.FiniteMeasure.ennreal_mass (μ := ν)).symm
    simp [hsa]
    rw [hν_univ_eq]
    rw [ENNReal.coe_inv hν_mass_nnreal_ne]
    exact ENNReal.inv_mul_cancel hν_mass_ne (by simp)
  · rw [preimage_inter_fiber_eq_empty_of_notMem hsa]
    simpa [hsa]

/-- Helper for Theorem 17.58: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) =
      Measure.dirac a := by
  -- Proof comment: this is the extensional wrapper around the apply-level normalized-fiber
  -- pushforward calculation.
  ext s hs
  simpa using map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    (μ := μ) (hρmeas := hρmeas) a ha hs

/-- Helper for Theorem 17.58: if both fiber masses are nonzero, then pushing the corresponding
product fiber law forward by the pair map gives the Dirac mass at that pair. -/
private theorem map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] {t : Set E} (P Q : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) (a b : t)
    (ha :
      (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    (hb :
      (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))) =
        Measure.dirac (a, b) := by
  have hmap :
      Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
          ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
              ProbabilityMeasure (E × E)) : Measure (E × E))) =
        (Measure.map ρ (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E))).prod
          (Measure.map ρ (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E))) := by
    -- Proof comment: rewrite the pair pushforward as the product of the two one-coordinate
    -- pushforwards before collapsing both factors to Dirac masses.
    simpa using
      (Measure.map_prod_map
        (μa := (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)))
        (μc := (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)))
        hρmeas hρmeas).symm
  rw [hmap]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := P) (hρmeas := hρmeas) a ha]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := Q) (hρmeas := hρmeas) b hb]
  exact Measure.dirac_prod_dirac

/-- Helper for Theorem 17.58: pushing the lifted finite-cell coupling forward by the pair map
recovers the original finite coupling. -/
private theorem liftedMapCoupling_map_representatives_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
      (ν : Measure (t × t)) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, hcols⟩
  have hpair_meas : Measurable (fun z : E × E ↦ (ρ z.1, ρ z.2)) := by
    fun_prop
  have hcell_zero_of_left_mass_zero :
      ∀ a b : t,
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b ha0
    -- Proof comment: if the `a`-fiber has zero mass, then the whole `a`-row of the coupling
    -- vanishes, so in particular the `(a,b)` coefficient is zero.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) := by
      exact Finset.single_le_sum
        (f := fun b' : t ↦ ((ν : Measure (t × t)) {(a, b')}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ b)
    have hrow0 :
        ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) = 0 := by
      rw [hrows a, ← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a, ha0]
    exact le_antisymm (by simpa [hrow0] using hle) bot_le
  have hcell_zero_of_right_mass_zero :
      ∀ a b : t,
        (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b hb0
    -- Proof comment: the same singleton-sum argument on columns kills cells whose `b`-fiber has
    -- zero `Q`-mass.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) := by
      exact Finset.single_le_sum
        (f := fun a' : t ↦ ((ν : Measure (t × t)) {(a', b)}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ a)
    have hcol0 :
        ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) = 0 := by
      rw [hcols b, ← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b, hb0]
    exact le_antisymm (by simpa [hcol0] using hle) bot_le
  have hcell :
      ∀ a b : t,
        Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
            ((((ν : Measure (t × t)) {(a, b)}) •
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))))) =
          ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
    intro a b
    by_cases ha0 :
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0
    · have hcoeff_zero := hcell_zero_of_left_mass_zero a b ha0
      have hmap_smul :
          Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
              ((((ν : Measure (t × t)) {(a, b)}) •
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))))) =
            ((ν : Measure (t × t)) {(a, b)}) •
              Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))) := by
        simpa using
          (Measure.map_smul
            (((ν : Measure (t × t)) {(a, b)}))
            ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                ProbabilityMeasure (E × E)) : Measure (E × E)))
            (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
      rw [hmap_smul]
      simp [hcoeff_zero]
    · by_cases hb0 :
          (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0
      · have hcoeff_zero := hcell_zero_of_right_mass_zero a b hb0
        have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        simp [hcoeff_zero]
      · have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        rw [map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
          (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) a b ha0 hb0]
  calc
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
        ∑ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
      -- Proof comment: map each finite cell separately, then rewrite every mapped cell as the
      -- corresponding weighted Dirac mass on `t × t`.
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro b hb
      simpa using hcell a b
    _ = ∑ p : t × t, ((ν : Measure (t × t)) {p}) • Measure.dirac p := by
      simpa [Fintype.sum_prod_type]
    _ = (ν : Measure (t × t)) := by
      simpa [Measure.sum_fintype] using
        (Measure.sum_smul_dirac (μ := (ν : Measure (t × t))))

end finiteFiberLift

/-- Helper for Theorem 17.58: a coupling of the quantized subtype laws can be lifted through the
quantizer fibers to an exact coupling of the original laws, while preserving full mass on the
quantized order event. -/
private lemma existsExactCoupling_of_quantizedCoupling {d n : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    {ψ : ProbabilityMeasure ((quantizedRange d n) × (quantizedRange d n))}
    (hCoupling :
      IsCoupling ψ
        (μ1.map (measurable_quantizedRangeMap d n).aemeasurable)
        (μ2.map (measurable_quantizedRangeMap d n).aemeasurable))
    (hOrdered :
      (ψ : Measure ((quantizedRange d n) × (quantizedRange d n))) {z | z.1 ≤ z.2} = 1) :
    ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
      IsCoupling φ μ1 μ2 ∧
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
          {z | coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} = 1 := by
  classical
  letI : Fintype (quantizedRange d n) := (coordGridQuantizer_range_finite d n).fintype
  let Λμ : Measure ((Fin d → ℝ) × (Fin d → ℝ)) :=
    liftedMapCoupling μ1 μ2 (quantizedRangeMap d n) ψ
  have hfst :
      Measure.map Prod.fst Λμ = (μ1 : Measure (Fin d → ℝ)) := by
    -- Proof comment: the local fiber-lift API recovers the first marginal of the ambient law.
    simpa [Λμ] using
      liftedMapCoupling_fst_eq
        (P := μ1) (Q := μ2) (ρ := quantizedRangeMap d n)
        (hρmeas := measurable_quantizedRangeMap d n) hCoupling
  have hsnd :
      Measure.map Prod.snd Λμ = (μ2 : Measure (Fin d → ℝ)) := by
    -- Proof comment: the same lifting package gives the second marginal.
    simpa [Λμ] using
      liftedMapCoupling_snd_eq
        (P := μ1) (Q := μ2) (ρ := quantizedRangeMap d n)
        (hρmeas := measurable_quantizedRangeMap d n) hCoupling
  have hprob : IsProbabilityMeasure Λμ := by
    refine ⟨?_⟩
    have hfstUniv :
        (Measure.map Prod.fst Λμ) Set.univ = ((μ1 : Measure (Fin d → ℝ)) Set.univ) := by
      exact congrArg (fun m : Measure (Fin d → ℝ) ↦ m Set.univ) hfst
    rw [Measure.map_apply measurable_fst (by simp : MeasurableSet (Set.univ : Set (Fin d → ℝ)))]
      at hfstUniv
    simpa using hfstUniv
  let φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) := ⟨Λμ, hprob⟩
  have hCouplingAmbient : IsCoupling φ μ1 μ2 := by
    constructor
    · simpa [φ, Λμ, Measure.fst] using hfst
    · simpa [φ, Λμ, Measure.snd] using hsnd
  have hpairMap :
      Measure.map
          (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦
            (quantizedRangeMap d n z.1, quantizedRangeMap d n z.2))
          (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) =
        (ψ : Measure ((quantizedRange d n) × (quantizedRange d n))) := by
    -- Proof comment: pushing the lifted ambient coupling back through the quantizer pair map
    -- recovers the original finite coupling `ψ`.
    simpa [φ, Λμ] using
      liftedMapCoupling_map_representatives_eq
        (P := μ1) (Q := μ2) (ρ := quantizedRangeMap d n)
        (hρmeas := measurable_quantizedRangeMap d n) hCoupling
  have hpairMeas :
      Measurable
        (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦
          (quantizedRangeMap d n z.1, quantizedRangeMap d n z.2)) := by
    -- Proof comment: the quantizer pair map is measurable coordinatewise.
    exact ((measurable_quantizedRangeMap d n).comp measurable_fst).prodMk
      ((measurable_quantizedRangeMap d n).comp measurable_snd)
  have hpreimage :
      (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦
          (quantizedRangeMap d n z.1, quantizedRangeMap d n z.2)) ⁻¹'
        ({z : (quantizedRange d n) × (quantizedRange d n) | z.1 ≤ z.2} :
          Set ((quantizedRange d n) × (quantizedRange d n))) =
        ({z : (Fin d → ℝ) × (Fin d → ℝ) |
            coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
    -- Proof comment: the subtype order event pulls back exactly to the ambient quantized-order
    -- event because `quantizedRangeMap` stores the quantizer value as its subtype coercion.
    ext z
    simp [quantizedRangeMap]
  refine ⟨φ, hCouplingAmbient, ?_⟩
  -- Proof comment: evaluate the recovered pushforward identity on the subtype order event and
  -- rewrite its preimage as the ambient quantized-order event.
  calc
    (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
        {z | coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} =
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
          ((fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦
              (quantizedRangeMap d n z.1, quantizedRangeMap d n z.2)) ⁻¹'
            ({z : (quantizedRange d n) × (quantizedRange d n) | z.1 ≤ z.2} :
              Set ((quantizedRange d n) × (quantizedRange d n)))) := by
            rw [hpreimage]
    _ =
        Measure.map
          (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦
            (quantizedRangeMap d n z.1, quantizedRangeMap d n z.2))
          (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
          ({z : (quantizedRange d n) × (quantizedRange d n) | z.1 ≤ z.2} :
            Set ((quantizedRange d n) × (quantizedRange d n))) := by
              symm
              rw [Measure.map_apply hpairMeas ((Set.toFinite _).measurableSet)]
    _ = (ψ : Measure ((quantizedRange d n) × (quantizedRange d n)))
          ({z : (quantizedRange d n) × (quantizedRange d n) | z.1 ≤ z.2} :
            Set ((quantizedRange d n) × (quantizedRange d n))) := by
              rw [hpairMap]
    _ = 1 := hOrdered

/-- Helper for Theorem 17.58: any coupling puts at most the sum of the marginal tail masses
outside a product set `K × K`. -/
private lemma measure_prodCompl_le_of_isCoupling
    {E : Type*} [MeasurableSpace E]
    {φ : ProbabilityMeasure (E × E)} {μ1 μ2 : ProbabilityMeasure E}
    (hCoupling : IsCoupling φ μ1 μ2) {K : Set E} (hK : MeasurableSet K) :
    (φ : Measure (E × E)) ((K ×ˢ K)ᶜ) ≤
      (μ1 : Measure E) Kᶜ + (μ2 : Measure E) Kᶜ := by
  have hfst :
      (φ : Measure (E × E)).fst = (μ1 : Measure E) := hCoupling.1
  have hsnd :
      (φ : Measure (E × E)).snd = (μ2 : Measure E) := hCoupling.2
  have hcompl :
      ((K ×ˢ K : Set (E × E))ᶜ) =
        (Prod.fst ⁻¹' Kᶜ) ∪ (Prod.snd ⁻¹' Kᶜ) := by
    -- Proof comment: leaving the product box means failing the `K`-condition in at least one
    -- coordinate.
    ext z
    by_cases hz1 : z.1 ∈ K <;> by_cases hz2 : z.2 ∈ K <;> simp [hz1, hz2]
  have hfstApply :
      (φ : Measure (E × E)) (Prod.fst ⁻¹' Kᶜ) = (μ1 : Measure E) Kᶜ := by
    -- Proof comment: the first-coordinate tail is exactly the first marginal tail.
    calc
      (φ : Measure (E × E)) (Prod.fst ⁻¹' Kᶜ) = (φ : Measure (E × E)).fst Kᶜ := by
        rw [Measure.fst_apply hK.compl]
      _ = (μ1 : Measure E) Kᶜ := by rw [hfst]
  have hsndApply :
      (φ : Measure (E × E)) (Prod.snd ⁻¹' Kᶜ) = (μ2 : Measure E) Kᶜ := by
    -- Proof comment: the second-coordinate tail is handled by the second marginal in the same
    -- way.
    calc
      (φ : Measure (E × E)) (Prod.snd ⁻¹' Kᶜ) = (φ : Measure (E × E)).snd Kᶜ := by
        rw [Measure.snd_apply hK.compl]
      _ = (μ2 : Measure E) Kᶜ := by rw [hsnd]
  calc
    (φ : Measure (E × E)) ((K ×ˢ K)ᶜ) =
        (φ : Measure (E × E)) ((Prod.fst ⁻¹' Kᶜ) ∪ (Prod.snd ⁻¹' Kᶜ)) := by
          rw [hcompl]
    _ ≤ (φ : Measure (E × E)) (Prod.fst ⁻¹' Kᶜ) +
          (φ : Measure (E × E)) (Prod.snd ⁻¹' Kᶜ) :=
        measure_union_le _ _
    _ = (μ1 : Measure E) Kᶜ + (μ2 : Measure E) Kᶜ := by
          rw [hfstApply, hsndApply]

/-- Helper for Theorem 17.58: read a `Fin 1 → ℝ` vector through its unique coordinate. -/
private def fin1Real (z : Fin 1 → ℝ) : ℝ :=
  z 0

/-- Helper for Theorem 17.58: regard a real number as a constant `Fin 1 → ℝ` vector. -/
private def realToFin1 (x : ℝ) : Fin 1 → ℝ :=
  fun _ ↦ x

/-- Helper for Theorem 17.58: evaluating the constant `Fin 1 → ℝ` vector at the unique coordinate
recovers the original real number. -/
private lemma fin1Real_realToFin1 (x : ℝ) :
    fin1Real (realToFin1 x) = x := by
  rfl

/-- Helper for Theorem 17.58: a `Fin 1 → ℝ` vector is determined by its unique coordinate. -/
private lemma realToFin1_fin1Real (z : Fin 1 → ℝ) :
    realToFin1 (fin1Real z) = z := by
  -- Proof comment: `Fin 1` has only one coordinate, so the constant tuple built from that
  -- coordinate agrees with the original vector.
  funext i
  fin_cases i
  rfl

/-- Helper for Theorem 17.58: the unique-coordinate evaluation on `Fin 1 → ℝ` is measurable. -/
private lemma measurable_fin1Real :
    Measurable fin1Real := by
  simpa [fin1Real] using (continuous_apply (0 : Fin 1)).measurable

/-- Helper for Theorem 17.58: the constant-vector embedding of `ℝ` into `Fin 1 → ℝ` is
measurable. -/
private lemma measurable_realToFin1 :
    Measurable realToFin1 := by
  -- Proof comment: the single coordinate of the constant vector is just the identity map on `ℝ`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  fin_cases i
  simpa [realToFin1] using measurable_id

/-- Helper for Theorem 17.58: pushing a `Fin 1 → ℝ` law along its unique coordinate gives the
corresponding real-valued law. -/
private abbrev fin1RealLaw (μ : ProbabilityMeasure (Fin 1 → ℝ)) :
    ProbabilityMeasure ℝ :=
  μ.map measurable_fin1Real.aemeasurable

/-- Helper for Theorem 17.58: transporting the pushed-forward real law back along the constant
embedding recovers the original `Fin 1 → ℝ` law. -/
private lemma map_realToFin1_fin1RealLaw (μ : ProbabilityMeasure (Fin 1 → ℝ)) :
    (fin1RealLaw μ).map measurable_realToFin1.aemeasurable = μ := by
  -- Proof comment: the back-transport cancels the unique-coordinate projection pointwise.
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map realToFin1 (Measure.map fin1Real (μ : Measure (Fin 1 → ℝ))) =
    (μ : Measure (Fin 1 → ℝ))
  rw [Measure.map_map measurable_realToFin1 measurable_fin1Real]
  calc
    Measure.map (realToFin1 ∘ fin1Real) (μ : Measure (Fin 1 → ℝ)) =
        Measure.map (fun z : Fin 1 → ℝ ↦ z) (μ : Measure (Fin 1 → ℝ)) := by
          exact Measure.map_congr (Filter.Eventually.of_forall realToFin1_fin1Real)
    _ = (μ : Measure (Fin 1 → ℝ)) := by
          simp

/-- Helper for Theorem 17.58: package the coordinatewise back-transport on `ℝ × ℝ`. -/
private def realPairToFin1Pair (z : ℝ × ℝ) : (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (realToFin1 z.1, realToFin1 z.2)

/-- Helper for Theorem 17.58: the coordinatewise back-transport on `ℝ × ℝ` is measurable. -/
private lemma measurable_realPairToFin1Pair :
    Measurable realPairToFin1Pair := by
  -- Proof comment: both coordinates are measurable copies of `realToFin1`.
  exact (measurable_realToFin1.comp measurable_fst).prodMk
    (measurable_realToFin1.comp measurable_snd)

/-- Helper for Theorem 17.58: transporting a real coupling through `realPairToFin1Pair` gives a
coupling of the original `Fin 1 → ℝ` marginals. -/
private lemma isCoupling_map_realPairToFin1Pair
    {μ1 μ2 : ProbabilityMeasure (Fin 1 → ℝ)}
    {ψ : ProbabilityMeasure (ℝ × ℝ)}
    (hCoupling : IsCoupling ψ (fin1RealLaw μ1) (fin1RealLaw μ2)) :
    IsCoupling (ψ.map measurable_realPairToFin1Pair.aemeasurable) μ1 μ2 := by
  rw [isCoupling_iff] at hCoupling ⊢
  rcases hCoupling with ⟨hfst, hsnd⟩
  constructor
  · -- Proof comment: rewrite the first marginal as a composed pushforward and cancel the
    -- coordinate projection against the back-transport.
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.fst (Measure.map realPairToFin1Pair (ψ : Measure (ℝ × ℝ))) =
      (μ1 : Measure (Fin 1 → ℝ))
    rw [Measure.map_map measurable_fst measurable_realPairToFin1Pair]
    calc
      Measure.map (fun z : ℝ × ℝ ↦ realToFin1 z.1) (ψ : Measure (ℝ × ℝ)) =
          Measure.map realToFin1 (Measure.map Prod.fst (ψ : Measure (ℝ × ℝ))) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := (ψ : Measure (ℝ × ℝ)))
                measurable_realToFin1 measurable_fst).symm
      _ = (((ψ.map measurable_fst.aemeasurable).map measurable_realToFin1.aemeasurable :
            ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
            rfl
      _ = (((fin1RealLaw μ1).map measurable_realToFin1.aemeasurable :
            ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
            rw [hfst]
      _ = (μ1 : Measure (Fin 1 → ℝ)) := by
            simpa using congrArg
              (fun ν : ProbabilityMeasure (Fin 1 → ℝ) ↦ (ν : Measure (Fin 1 → ℝ)))
              (map_realToFin1_fin1RealLaw μ1)
  · -- Proof comment: the second marginal is identical after swapping `Prod.fst` for `Prod.snd`.
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.snd (Measure.map realPairToFin1Pair (ψ : Measure (ℝ × ℝ))) =
      (μ2 : Measure (Fin 1 → ℝ))
    rw [Measure.map_map measurable_snd measurable_realPairToFin1Pair]
    calc
      Measure.map (fun z : ℝ × ℝ ↦ realToFin1 z.2) (ψ : Measure (ℝ × ℝ)) =
          Measure.map realToFin1 (Measure.map Prod.snd (ψ : Measure (ℝ × ℝ))) := by
            simpa [Function.comp] using
              (Measure.map_map
                (μ := (ψ : Measure (ℝ × ℝ)))
                measurable_realToFin1 measurable_snd).symm
      _ = (((ψ.map measurable_snd.aemeasurable).map measurable_realToFin1.aemeasurable :
            ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
            rfl
      _ = (((fin1RealLaw μ2).map measurable_realToFin1.aemeasurable :
            ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
            rw [hsnd]
      _ = (μ2 : Measure (Fin 1 → ℝ)) := by
            simpa using congrArg
              (fun ν : ProbabilityMeasure (Fin 1 → ℝ) ↦ (ν : Measure (Fin 1 → ℝ)))
              (map_realToFin1_fin1RealLaw μ2)

/-- Helper for Theorem 17.58: the coordinatewise back-transport on `ℝ × ℝ` preserves the ordered
support event. -/
private lemma orderedMassOne_map_realPairToFin1Pair
    {ψ : ProbabilityMeasure (ℝ × ℝ)}
    (hOrdered :
      (ψ : Measure (ℝ × ℝ)) {z | z.1 ≤ z.2} = 1) :
    (((ψ.map measurable_realPairToFin1Pair.aemeasurable :
        ProbabilityMeasure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) :
          Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
      ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} :
        Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)))) = 1 := by
  have hpreimage :
      realPairToFin1Pair ⁻¹' ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} :
        Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) =
        ({z : ℝ × ℝ | z.1 ≤ z.2} : Set (ℝ × ℝ)) := by
    -- Proof comment: in dimension `1`, coordinatewise comparison is just scalar comparison.
    ext z
    simp [realPairToFin1Pair, realToFin1, Pi.le_def]
  -- Proof comment: evaluate the mapped measure on the ordered event and rewrite the preimage.
  rw [show
      (((ψ.map measurable_realPairToFin1Pair.aemeasurable :
          ProbabilityMeasure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) : Measure _)
        ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} :
          Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)))) =
        Measure.map realPairToFin1Pair (ψ : Measure (ℝ × ℝ))
          ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} :
            Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) by
      rfl]
  rw [Measure.map_apply_of_aemeasurable measurable_realPairToFin1Pair.aemeasurable
    (measurableSet_orderedPairSet 1), hpreimage, hOrdered]

/-- Helper for Theorem 17.58: the restricted Lebesgue measure on `(0,1)` is a probability
measure. -/
private theorem isProbabilityMeasure_openUnitIntervalRestrict :
    IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) := by
  -- Proof comment: the open unit interval has Lebesgue measure `1`, so its restriction is a
  -- probability measure.
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  simp [Real.volume_Ioo]

/-- Helper for Theorem 17.58: use Lebesgue measure on `(0,1)` as the common source law for the
real quantile construction. -/
private def openUnitIntervalLaw : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1),
    isProbabilityMeasure_openUnitIntervalRestrict⟩

/-- Helper for Theorem 17.58: the real quantile is the infimum of the cdf superlevel set. -/
private def cdfQuantile (ν : ProbabilityMeasure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x}

/-- Helper for Theorem 17.58: for `u ∈ (0,1)`, the cdf superlevel set defining the quantile is
nonempty. -/
private lemma cdfQuantileSuperlevel_nonempty
    (ν : ProbabilityMeasure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Set.Nonempty {x : ℝ | u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x} := by
  -- Proof comment: because the cdf tends to `1` at `+∞`, some point reaches level `u`.
  have hmem : Set.Ioi u ∈ nhds (1 : ℝ) := Ioi_mem_nhds hu.2
  have hEventual :
      ∀ᶠ x in Filter.atTop, u < ProbabilityTheory.cdf (ν : Measure ℝ) x :=
    (ProbabilityTheory.tendsto_cdf_atTop (μ := (ν : Measure ℝ))) hmem
  obtain ⟨x, hx⟩ := Filter.Eventually.exists hEventual
  exact ⟨x, le_of_lt hx⟩

/-- Helper for Theorem 17.58: for `u ∈ (0,1)`, the cdf superlevel set defining the quantile is
bounded below. -/
private lemma cdfQuantileSuperlevel_bddBelow
    (ν : ProbabilityMeasure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    BddBelow {x : ℝ | u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x} := by
  -- Proof comment: because the cdf tends to `0` at `-∞`, a far-left point stays below level `u`
  -- and therefore lower-bounds the whole superlevel set by monotonicity.
  have hmem : Set.Iio u ∈ nhds (0 : ℝ) := Iio_mem_nhds hu.1
  have hEventual :
      ∀ᶠ x in Filter.atBot, ProbabilityTheory.cdf (ν : Measure ℝ) x < u :=
    (ProbabilityTheory.tendsto_cdf_atBot (μ := (ν : Measure ℝ))) hmem
  obtain ⟨x, hx⟩ := Filter.Eventually.exists hEventual
  refine ⟨x, ?_⟩
  intro y hy
  by_contra hxy
  have hyx : y < x := lt_of_not_ge hxy
  have hFy : u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) y := hy
  have hFyx :
      ProbabilityTheory.cdf (ν : Measure ℝ) y ≤
        ProbabilityTheory.cdf (ν : Measure ℝ) x :=
    (ProbabilityTheory.monotone_cdf (μ := (ν : Measure ℝ))) (le_of_lt hyx)
  exact not_lt_of_ge (hFy.trans hFyx) hx

/-- Helper for Theorem 17.58: the cdf at the real quantile still reaches the requested level. -/
private lemma cdfQuantile_level_le
    (ν : ProbabilityMeasure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) (cdfQuantile ν u) := by
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x}
  have hS_nonempty : S.Nonempty := by
    simpa [S] using cdfQuantileSuperlevel_nonempty ν hu
  have hS_bddBelow : BddBelow S := by
    simpa [S] using cdfQuantileSuperlevel_bddBelow ν hu
  have hcont :
      ContinuousWithinAt (ProbabilityTheory.cdf (ν : Measure ℝ)) S (sInf S) := by
    refine ((ProbabilityTheory.cdf (ν : Measure ℝ)).right_continuous (sInf S)).mono ?_
    intro x hx
    exact csInf_le hS_bddBelow hx
  have hmap :
      ProbabilityTheory.cdf (ν : Measure ℝ) (sInf S) =
        sInf ((ProbabilityTheory.cdf (ν : Measure ℝ)) '' S) :=
    MonotoneOn.map_csInf_of_continuousWithinAt hcont
      ((ProbabilityTheory.monotone_cdf (μ := (ν : Measure ℝ))).monotoneOn S)
      hS_nonempty hS_bddBelow
  have hu_le :
      u ≤ sInf ((ProbabilityTheory.cdf (ν : Measure ℝ)) '' S) := by
    refine le_csInf ?_ ?_
    · rcases hS_nonempty with ⟨x, hx⟩
      exact ⟨ProbabilityTheory.cdf (ν : Measure ℝ) x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
  simpa [cdfQuantile, S, hmap] using hu_le

/-- Helper for Theorem 17.58: every point whose cdf already reaches level `u` lies to the right
of the corresponding real quantile. -/
private lemma cdfQuantile_le_of_le
    (ν : ProbabilityMeasure ℝ) {u x : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hx : u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x) :
    cdfQuantile ν u ≤ x := by
  let S : Set ℝ := {y : ℝ | u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) y}
  have hS_bddBelow : BddBelow S := by
    simpa [S] using cdfQuantileSuperlevel_bddBelow ν hu
  -- Proof comment: since `x` itself belongs to the defining superlevel set, the infimum lies
  -- below `x`.
  change sInf S ≤ x
  exact csInf_le hS_bddBelow (by simpa [S] using hx)

/-- Helper for Theorem 17.58: the real quantile is monotone on `(0,1)`. -/
private lemma cdfQuantile_monotoneOn
    (ν : ProbabilityMeasure ℝ) :
    MonotoneOn (cdfQuantile ν) (Set.Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  -- Proof comment: the higher-level quantile already reaches level `v`, hence also the smaller
  -- level `u`.
  exact cdfQuantile_le_of_le ν hu (huv.trans (cdfQuantile_level_le ν hv))

/-- Helper for Theorem 17.58: the real quantile is almost everywhere measurable on the open unit
interval source law. -/
private lemma aemeasurable_cdfQuantile (ν : ProbabilityMeasure ℝ) :
    AEMeasurable (cdfQuantile ν) (openUnitIntervalLaw : Measure ℝ) := by
  -- Proof comment: monotonicity on `(0,1)` gives measurability after restricting Lebesgue
  -- measure to that interval.
  simpa [openUnitIntervalLaw] using
    (aemeasurable_restrict_of_monotoneOn
      (μ := (volume : Measure ℝ)) (s := Set.Ioo (0 : ℝ) 1) measurableSet_Ioo
      (cdfQuantile_monotoneOn ν))

/-- Helper for Theorem 17.58: on `(0,1)`, the real quantile is characterized by cdf comparison. -/
private lemma cdfQuantile_le_iff
    (ν : ProbabilityMeasure ℝ) {u x : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    cdfQuantile ν u ≤ x ↔
      u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x := by
  constructor
  · intro hqx
    calc
      u ≤ ProbabilityTheory.cdf (ν : Measure ℝ) (cdfQuantile ν u) :=
        cdfQuantile_level_le ν hu
      _ ≤ ProbabilityTheory.cdf (ν : Measure ℝ) x :=
        (ProbabilityTheory.monotone_cdf (μ := (ν : Measure ℝ))) hqx
  · intro hx
    exact cdfQuantile_le_of_le ν hu hx

/-- Helper for Theorem 17.58: intersecting `Ioc (0,y]` with the source interval `(0,1)` has
Lebesgue mass `y` whenever `0 ≤ y ≤ 1`. -/
private lemma volume_Ioc_inter_openUnitInterval
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (volume : Measure ℝ) (Set.Ioc (0 : ℝ) y ∩ Set.Ioo (0 : ℝ) 1) = ENNReal.ofReal y := by
  by_cases hy : y = 1
  · -- Proof comment: at the right endpoint, the intersection is exactly `(0,1)`.
    subst hy
    have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨⟨hx.1, hx.2.le⟩, hx⟩
    rw [hset, Real.volume_Ioo]
    norm_num
  · have hylt : y < 1 := lt_of_le_of_ne hy1 hy
    have hset : Set.Ioc (0 : ℝ) y ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioc (0 : ℝ) y := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        refine ⟨hx, ⟨hx.1, lt_of_le_of_lt hx.2 hylt⟩⟩
    -- Proof comment: away from the endpoint `1`, the intersection does not change the interval.
    rw [hset, Real.volume_Ioc]
    simp

/-- Helper for Theorem 17.58: pushing the open-unit-interval source law forward by the real
quantile recovers the target probability measure. -/
private lemma map_cdfQuantile_eq (ν : ProbabilityMeasure ℝ) :
    ((openUnitIntervalLaw.map (aemeasurable_cdfQuantile ν) : ProbabilityMeasure ℝ) :
      Measure ℝ) = (ν : Measure ℝ) := by
  apply MeasureTheory.Measure.eq_of_cdf
  ext x
  calc
    ProbabilityTheory.cdf
        ((openUnitIntervalLaw.map (aemeasurable_cdfQuantile ν) : ProbabilityMeasure ℝ) :
          Measure ℝ) x
        = ((openUnitIntervalLaw.map (aemeasurable_cdfQuantile ν) : ProbabilityMeasure ℝ)
            (Set.Iic x) : ℝ) := by
              rw [ProbabilityTheory.cdf_eq_real, ProbabilityMeasure.measureReal_eq_coe_coeFn]
    _ = (openUnitIntervalLaw ((cdfQuantile ν) ⁻¹' Set.Iic x) : ℝ) := by
          rw [ProbabilityMeasure.map_apply openUnitIntervalLaw (aemeasurable_cdfQuantile ν)
            measurableSet_Iic]
    _ = (openUnitIntervalLaw : Measure ℝ).real ((cdfQuantile ν) ⁻¹' Set.Iic x) := by
          rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    _ = (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).real
          ((cdfQuantile ν) ⁻¹' Set.Iic x)) := by
          rfl
    _ = (volume : Measure ℝ).real
          ((cdfQuantile ν) ⁻¹' Set.Iic x ∩ Set.Ioo (0 : ℝ) 1) := by
          rw [MeasureTheory.measureReal_restrict_apply' measurableSet_Ioo]
    _ = (volume : Measure ℝ).real
          (Set.Ioc (0 : ℝ) (ProbabilityTheory.cdf (ν : Measure ℝ) x) ∩ Set.Ioo (0 : ℝ) 1) := by
          have hset :
              (cdfQuantile ν) ⁻¹' Set.Iic x ∩ Set.Ioo (0 : ℝ) 1 =
                Set.Ioc (0 : ℝ) (ProbabilityTheory.cdf (ν : Measure ℝ) x) ∩
                  Set.Ioo (0 : ℝ) 1 := by
            ext u
            constructor
            · intro hu
              rcases hu with ⟨huQuantile, huIoo⟩
              refine ⟨⟨huIoo.1, ?_⟩, huIoo⟩
              exact (cdfQuantile_le_iff ν huIoo).1 huQuantile
            · intro hu
              rcases hu with ⟨huIoc, huIoo⟩
              refine ⟨(cdfQuantile_le_iff ν huIoo).2 huIoc.2, huIoo⟩
          rw [hset]
    _ = ProbabilityTheory.cdf (ν : Measure ℝ) x := by
          rw [MeasureTheory.measureReal_def,
            volume_Ioc_inter_openUnitInterval
              (ProbabilityTheory.cdf_nonneg (μ := (ν : Measure ℝ)) x)
              (ProbabilityTheory.cdf_le_one (μ := (ν : Measure ℝ)) x)]
          exact ENNReal.toReal_ofReal
            (ProbabilityTheory.cdf_nonneg (μ := (ν : Measure ℝ)) x)

/-- Helper for Theorem 17.58: cdf order implies pointwise quantile order on the common
open-unit-interval source law. -/
private lemma cdfQuantile_le_of_cdf_le
    {ν1 ν2 : ProbabilityMeasure ℝ}
    (hcdf : ∀ x : ℝ,
      ProbabilityTheory.cdf (ν2 : Measure ℝ) x ≤
        ProbabilityTheory.cdf (ν1 : Measure ℝ) x)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    cdfQuantile ν1 u ≤ cdfQuantile ν2 u := by
  -- Proof comment: the second quantile already reaches level `u` for `ν₂`, and the cdf order
  -- upgrades that same level bound to `ν₁`.
  apply cdfQuantile_le_of_le ν1 hu
  calc
    u ≤ ProbabilityTheory.cdf (ν2 : Measure ℝ) (cdfQuantile ν2 u) :=
      cdfQuantile_level_le ν2 hu
    _ ≤ ProbabilityTheory.cdf (ν1 : Measure ℝ) (cdfQuantile ν2 u) :=
      hcdf _

private theorem existsOrderedRealCoupling_of_cdf_le
    {ν1 ν2 : ProbabilityMeasure ℝ}
    (hcdf : ∀ x : ℝ,
      ProbabilityTheory.cdf (ν2 : Measure ℝ) x ≤
        ProbabilityTheory.cdf (ν1 : Measure ℝ) x) :
    ∃ ψ : ProbabilityMeasure (ℝ × ℝ),
      IsCoupling ψ ν1 ν2 ∧
        (ψ : Measure (ℝ × ℝ)) {z | z.1 ≤ z.2} = 1 := by
  -- Route correction: instead of importing the missing Chapter 13 quantile API, build the needed
  -- one-dimensional quantile facts directly from `cdf` inside this file and use the common source
  -- law `openUnitIntervalLaw`.
  let pairQuantile : ℝ → ℝ × ℝ := fun u ↦ (cdfQuantile ν1 u, cdfQuantile ν2 u)
  let ψ : ProbabilityMeasure (ℝ × ℝ) :=
    openUnitIntervalLaw.map ((aemeasurable_cdfQuantile ν1).prodMk
      (aemeasurable_cdfQuantile ν2))
  refine ⟨ψ, ?_, ?_⟩
  · rw [isCoupling_iff]
    constructor
    · -- Proof comment: the first marginal is the first quantile pushforward, which recovers `ν₁`.
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map Prod.fst (Measure.map pairQuantile (openUnitIntervalLaw : Measure ℝ)) =
        (ν1 : Measure ℝ)
      rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        ((aemeasurable_cdfQuantile ν1).prodMk (aemeasurable_cdfQuantile ν2))]
      simpa [pairQuantile, Function.comp] using map_cdfQuantile_eq ν1
    · -- Proof comment: the second marginal is identical after projecting to the other coordinate.
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map Prod.snd (Measure.map pairQuantile (openUnitIntervalLaw : Measure ℝ)) =
        (ν2 : Measure ℝ)
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        ((aemeasurable_cdfQuantile ν1).prodMk (aemeasurable_cdfQuantile ν2))]
      simpa [pairQuantile, Function.comp] using map_cdfQuantile_eq ν2
  · -- Proof comment: the cdf inequality gives pointwise quantile order on `(0,1)`, so the mapped
    -- coupling has full mass on the ordered set.
    rw [show (ψ : Measure (ℝ × ℝ)) =
      Measure.map pairQuantile (openUnitIntervalLaw : Measure ℝ) by rfl]
    have hOrderedSet :
        MeasurableSet ({z : ℝ × ℝ | z.1 ≤ z.2} : Set (ℝ × ℝ)) := by
      exact measurableSet_le measurable_fst measurable_snd
    rw [Measure.map_apply_of_aemeasurable
      ((aemeasurable_cdfQuantile ν1).prodMk (aemeasurable_cdfQuantile ν2)) hOrderedSet]
    have hsource :
        (openUnitIntervalLaw : Measure ℝ)
            (pairQuantile ⁻¹' ({z : ℝ × ℝ | z.1 ≤ z.2} : Set (ℝ × ℝ))) = 1 := by
      have hsubset :
          Set.Ioo (0 : ℝ) 1 ⊆
            pairQuantile ⁻¹' ({z : ℝ × ℝ | z.1 ≤ z.2} : Set (ℝ × ℝ)) := by
        intro u hu
        change cdfQuantile ν1 u ≤ cdfQuantile ν2 u
        exact cdfQuantile_le_of_cdf_le hcdf hu
      have hfull :
          (openUnitIntervalLaw : Measure ℝ) (Set.Ioo (0 : ℝ) 1) = 1 := by
        change ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) = 1
        rw [Measure.restrict_apply_self]
        simp [Real.volume_Ioo]
      refine le_antisymm MeasureTheory.prob_le_one ?_
      calc
        1 = (openUnitIntervalLaw : Measure ℝ) (Set.Ioo (0 : ℝ) 1) := hfull.symm
        _ ≤ (openUnitIntervalLaw : Measure ℝ)
              (pairQuantile ⁻¹' ({z : ℝ × ℝ | z.1 ≤ z.2} : Set (ℝ × ℝ))) :=
            measure_mono hsubset
    exact hsource

/-- Helper for Theorem 17.58: the unique-coordinate map sends an open upper tail on `ℝ` back to
the corresponding upper set in `Fin 1 → ℝ`. -/
private lemma preimage_fin1Real_Ioi (x : ℝ) :
    fin1Real ⁻¹' Set.Ioi x = Set.Ioi (realToFin1 x) := by
  -- Proof comment: in dimension `1`, strict coordinatewise comparison is just the strict order on
  -- the unique coordinate.
  ext z
  change z 0 > x ↔ realToFin1 x < z
  constructor
  · intro hz
    constructor
    · intro i
      fin_cases i
      exact le_of_lt hz
    · intro hzle
      have hz0 : z 0 ≤ x := by
        simpa [realToFin1] using hzle 0
      exact not_le_of_gt hz hz0
  · intro hz
    have hz0_le : x ≤ z 0 := by
      simpa [realToFin1] using hz.1 0
    have hz0_not_le : ¬ z 0 ≤ x := by
      intro hz0
      exact hz.2 (by
        intro i
        fin_cases i
        simpa [realToFin1] using hz0)
    exact lt_of_not_ge hz0_not_le

/-- Helper for Theorem 17.58: the unique-coordinate map sends a closed lower tail on `ℝ` back to
the corresponding lower set in `Fin 1 → ℝ`. -/
private lemma preimage_fin1Real_Iic (x : ℝ) :
    fin1Real ⁻¹' Set.Iic x = Set.Iic (realToFin1 x) := by
  -- Proof comment: the same one-coordinate identification transports the lower-orthant event.
  ext z
  change z 0 ≤ x ↔ z ≤ realToFin1 x
  constructor
  · intro hz i
    fin_cases i
    simpa [realToFin1] using hz
  · intro hz
    simpa [fin1Real, realToFin1] using hz 0

/-- Helper for Theorem 17.58: the pushed-forward real law assigns the same mass to `Ioi x`
as the original `Fin 1 → ℝ` law assigns to the corresponding upper set. -/
private lemma fin1RealLaw_apply_Ioi (μ : ProbabilityMeasure (Fin 1 → ℝ)) (x : ℝ) :
    fin1RealLaw μ (Set.Ioi x) =
      μ (Set.Ioi (realToFin1 x)) := by
  -- Proof comment: `fin1RealLaw μ` is a pushforward along `fin1Real`, so tail masses are related
  -- by the corresponding preimage formula.
  simpa [fin1RealLaw, preimage_fin1Real_Ioi] using
    (ProbabilityMeasure.map_apply
      (ν := μ) measurable_fin1Real.aemeasurable
      (A := Set.Ioi x) measurableSet_Ioi)

/-- Helper for Theorem 17.58: the pushed-forward real law assigns the same mass to `Iic x`
as the original `Fin 1 → ℝ` law assigns to the corresponding lower set. -/
private lemma fin1RealLaw_apply_Iic (μ : ProbabilityMeasure (Fin 1 → ℝ)) (x : ℝ) :
    fin1RealLaw μ (Set.Iic x) =
      μ (Set.Iic (realToFin1 x)) := by
  -- Proof comment: this is the lower-tail analogue of the preceding pushforward identity.
  simpa [fin1RealLaw, preimage_fin1Real_Iic] using
    (ProbabilityMeasure.map_apply
      (ν := μ) measurable_fin1Real.aemeasurable
      (A := Set.Iic x) measurableSet_Iic)

/-- Helper for Theorem 17.58: in dimension `1`, stochastic order compares all open upper tails of
the pushed-forward real laws. -/
private lemma measure_Ioi_le_of_stochasticLE_finOne
    {μ1 μ2 : ProbabilityMeasure (Fin 1 → ℝ)}
    (hStochastic : StochasticLE μ1 μ2) (x : ℝ) :
    fin1RealLaw μ1 (Set.Ioi x) ≤ fin1RealLaw μ2 (Set.Ioi x) := by
  let s : Set (Fin 1 → ℝ) := Set.Ioi (realToFin1 x)
  let tailIndicator : (Fin 1 → ℝ) → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  have hs_meas : MeasurableSet s := by
    dsimp [s]
    rw [← preimage_fin1Real_Ioi]
    exact measurable_fin1Real measurableSet_Ioi
  have hmono : Monotone tailIndicator := by
    -- Proof comment: `tailIndicator` is the indicator of an upper set, so once it is `1` at one
    -- point it stays `1` above that point.
    intro a b hab
    by_cases ha : a ∈ s
    · have hb : b ∈ s := by
        exact lt_of_lt_of_le ha hab
      simp [tailIndicator, s, ha, hb]
    · have hta : tailIndicator a = 0 := by simp [tailIndicator, s, ha]
      have htb_nonneg : 0 ≤ tailIndicator b := by
        by_cases hb : b ∈ s
        · simp [tailIndicator, s, hb]
        · simp [tailIndicator, s, hb]
      rw [hta]
      exact htb_nonneg
  have hbdd : Bornology.IsBounded (Set.range tailIndicator) := by
    have hsubset : Set.range tailIndicator ⊆ ({0, 1} : Set ℝ) := by
      intro y hy
      rcases hy with ⟨z, rfl⟩
      by_cases hz : z ∈ s
      · simp [tailIndicator, s, hz]
      · simp [tailIndicator, s, hz]
    exact (Set.toFinite {0, 1}).isBounded.subset hsubset
  have hmeas : Measurable tailIndicator := by
    -- Proof comment: the indicator is measurable because `s = Set.Ioi _` is measurable.
    simpa [tailIndicator, s] using measurable_const.indicator hs_meas
  have hIntegral :=
    hStochastic hmono hbdd hmeas
  -- Proof comment: the indicator integrals are exactly the corresponding upper-tail masses.
  rw [integral_indicator_const (μ := (μ1 : Measure (Fin 1 → ℝ))) (1 : ℝ) hs_meas,
    integral_indicator_const (μ := (μ2 : Measure (Fin 1 → ℝ))) (1 : ℝ) hs_meas] at hIntegral
  simpa [fin1RealLaw_apply_Ioi, tailIndicator, s] using hIntegral

/-- Helper for Theorem 17.58: in dimension `1`, stochastic order implies pointwise CDF order for
the pushed-forward real laws. -/
private lemma cdf_le_of_stochasticLE_finOne
    {μ1 μ2 : ProbabilityMeasure (Fin 1 → ℝ)}
    (hStochastic : StochasticLE μ1 μ2) (x : ℝ) :
    ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x ≤
      ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x := by
  have htail :=
    measure_Ioi_le_of_stochasticLE_finOne (μ1 := μ1) (μ2 := μ2) hStochastic x
  have htailReal :
      (fin1RealLaw μ1 (Set.Ioi x) : ℝ) ≤ (fin1RealLaw μ2 (Set.Ioi x) : ℝ) := by
    exact_mod_cast htail
  have hrealIoi1 :
      ((fin1RealLaw μ1 : Measure ℝ)).real (Set.Ioi x) =
        (fin1RealLaw μ1 (Set.Ioi x) : ℝ) := by
    simpa using (ProbabilityMeasure.measureReal_eq_coe_coeFn (fin1RealLaw μ1) (Set.Ioi x))
  have hrealIoi2 :
      ((fin1RealLaw μ2 : Measure ℝ)).real (Set.Ioi x) =
        (fin1RealLaw μ2 (Set.Ioi x) : ℝ) := by
    simpa using (ProbabilityMeasure.measureReal_eq_coe_coeFn (fin1RealLaw μ2) (Set.Ioi x))
  have hsplit1 :
      ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x +
          (fin1RealLaw μ1 (Set.Ioi x) : ℝ) = 1 := by
    -- Proof comment: split the unit total mass of `fin1RealLaw μ1` into the closed lower tail
    -- and the complementary open upper tail.
    have hcompl : ((Set.Iic x : Set ℝ)ᶜ) = Set.Ioi x := by
      ext y
      simp
    have hsplit1' :
        ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x +
            ((fin1RealLaw μ1 : Measure ℝ)).real (Set.Ioi x) = 1 := by
      rw [ProbabilityTheory.cdf_eq_real]
      calc
        ((fin1RealLaw μ1 : Measure ℝ)).real (Set.Iic x) +
            ((fin1RealLaw μ1 : Measure ℝ)).real (Set.Ioi x)
            = ((fin1RealLaw μ1 : Measure ℝ)).real Set.univ := by
                simpa [hcompl] using
                  (MeasureTheory.measureReal_add_measureReal_compl
                    (μ := (fin1RealLaw μ1 : Measure ℝ)) measurableSet_Iic)
        _ = 1 := by
              simpa using (ProbabilityMeasure.measureReal_eq_coe_coeFn (fin1RealLaw μ1) Set.univ)
    calc
      ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x +
          (fin1RealLaw μ1 (Set.Ioi x) : ℝ)
          = ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x +
              ((fin1RealLaw μ1 : Measure ℝ)).real (Set.Ioi x) := by
                rw [hrealIoi1]
      _ = 1 := hsplit1'
  have hsplit2 :
      ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x +
          (fin1RealLaw μ2 (Set.Ioi x) : ℝ) = 1 := by
    -- Proof comment: the same complement identity holds for the second pushed-forward law.
    have hcompl : ((Set.Iic x : Set ℝ)ᶜ) = Set.Ioi x := by
      ext y
      simp
    have hsplit2' :
        ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x +
            ((fin1RealLaw μ2 : Measure ℝ)).real (Set.Ioi x) = 1 := by
      rw [ProbabilityTheory.cdf_eq_real]
      calc
        ((fin1RealLaw μ2 : Measure ℝ)).real (Set.Iic x) +
            ((fin1RealLaw μ2 : Measure ℝ)).real (Set.Ioi x)
            = ((fin1RealLaw μ2 : Measure ℝ)).real Set.univ := by
                simpa [hcompl] using
                  (MeasureTheory.measureReal_add_measureReal_compl
                    (μ := (fin1RealLaw μ2 : Measure ℝ)) measurableSet_Iic)
        _ = 1 := by
              simpa using (ProbabilityMeasure.measureReal_eq_coe_coeFn (fin1RealLaw μ2) Set.univ)
    calc
      ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x +
          (fin1RealLaw μ2 (Set.Ioi x) : ℝ)
          = ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x +
              ((fin1RealLaw μ2 : Measure ℝ)).real (Set.Ioi x) := by
                rw [hrealIoi2]
      _ = 1 := hsplit2'
  linarith

/-- Helper for Theorem 17.58: inside the unclipped strip `(-(n + 1), n + 1)`, the scalar
quantizer is exactly the rescaled floor mesh. -/
private lemma scalarClipFloorQuantizer_eq_floor_div_of_abs_lt
    {n : ℕ} {x : ℝ} (hx : |x| < (n : ℝ) + 1) :
    scalarClipFloorQuantizer n x =
      ((⌊((n + 1 : ℕ) : ℝ) * x⌋ : ℤ) : ℝ) / (n + 1 : ℕ) := by
  let m : ℕ := n + 1
  have hm_pos : 0 < (m : ℝ) := by positivity
  have hx_lower : -((m : ℝ)) < x := by simpa [m] using (abs_lt.mp hx).1
  have hx_upper : x < (m : ℝ) := by simpa [m] using (abs_lt.mp hx).2
  have hlower :
      -((m : ℤ) * m) ≤ ⌊(m : ℝ) * x⌋ := by
    rw [Int.le_floor]
    have hmul : (m : ℝ) * (-(m : ℝ)) < (m : ℝ) * x :=
      mul_lt_mul_of_pos_left hx_lower hm_pos
    have hmul' : -((m : ℝ) * m) ≤ (m : ℝ) * x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.le
    exact_mod_cast hmul'
  have hupper :
      ⌊(m : ℝ) * x⌋ ≤ (m : ℤ) * m := by
    rw [Int.floor_le_iff]
    have hmul : (m : ℝ) * x < (m : ℝ) * (m : ℝ) :=
      mul_lt_mul_of_pos_left hx_upper hm_pos
    have hmul' : (m : ℝ) * x < (m : ℝ) * m + 1 := by
      have hsq : (m : ℝ) * (m : ℝ) < (m : ℝ) * m + 1 := by
        nlinarith
      exact hmul.trans hsq
    exact_mod_cast hmul'
  have hmin :
      min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋ = ⌊(m : ℝ) * x⌋ := min_eq_right hupper
  have hmax :
      max (-((m : ℤ) * m)) ⌊(m : ℝ) * x⌋ = ⌊(m : ℝ) * x⌋ := max_eq_right hlower
  -- Proof comment: on the bounded box, the clip bounds are inactive, so only the floor mesh
  -- remains.
  change (((max (-((m : ℤ) * m)) (min ((m : ℤ) * m) ⌊(m : ℝ) * x⌋) : ℤ) : ℝ) / m) =
      (((⌊(m : ℝ) * x⌋ : ℤ) : ℝ) / m)
  rw [hmin, hmax]

/-- Helper for Theorem 17.58: a coordinate gap larger than one mesh step forces the scalar
quantizer to become strictly ordered once clipping is inactive. -/
private lemma scalarClipFloorQuantizer_lt_of_meshGap
    {n : ℕ} {x y : ℝ}
    (hx : |x| < (n : ℝ) + 1)
    (hy : |y| < (n : ℝ) + 1)
    (hgap : y + ((n : ℝ) + 1)⁻¹ < x) :
    scalarClipFloorQuantizer n y < scalarClipFloorQuantizer n x := by
  have hm_pos : 0 < ((n : ℝ) + 1) := by positivity
  have hqx := scalarClipFloorQuantizer_eq_floor_div_of_abs_lt (n := n) hx
  have hqy := scalarClipFloorQuantizer_eq_floor_div_of_abs_lt (n := n) hy
  have hfloor :
      ⌊((n : ℝ) + 1) * y⌋ < ⌊((n : ℝ) + 1) * x⌋ := by
    rw [Int.lt_floor_iff]
    have hscaled : ((n : ℝ) + 1) * y + 1 < ((n : ℝ) + 1) * x := by
      have hmul := mul_lt_mul_of_pos_left hgap hm_pos
      have hinv : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := by
        field_simp [hm_pos.ne']
      simpa [mul_add, add_comm, add_left_comm, add_assoc, hinv] using hmul
    have hfloor_le : ((⌊((n : ℝ) + 1) * y⌋ : ℤ) : ℝ) ≤ ((n : ℝ) + 1) * y := Int.floor_le _
    linarith
  have hfloor_real :
      (((⌊((n : ℝ) + 1) * y⌋ : ℤ) : ℝ)) < (((⌊((n : ℝ) + 1) * x⌋ : ℤ) : ℝ)) := by
    exact_mod_cast hfloor
  -- Proof comment: after identifying both clipped floors with the plain floor mesh, strict
  -- inequality survives division by the positive scaling factor.
  calc
    scalarClipFloorQuantizer n y
        = (((⌊((n : ℝ) + 1) * y⌋ : ℤ) : ℝ)) / ((n : ℝ) + 1) := by simpa using hqy
    _ < (((⌊((n : ℝ) + 1) * x⌋ : ℤ) : ℝ)) / ((n : ℝ) + 1) :=
        div_lt_div_of_pos_right hfloor_real hm_pos
    _ = scalarClipFloorQuantizer n x := by simpa using hqx.symm

/-- Helper for Theorem 17.58: a bounded strict coordinate gap is an open witness that a pair lies
outside the coordinatewise order relation. -/
private def strictGapBoxSet (d m R : ℕ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {z | (∀ i, ‖z.1 i‖ < (R : ℝ) + 1 ∧ ‖z.2 i‖ < (R : ℝ) + 1) ∧
      ∃ i, z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i}

/-- Helper for Theorem 17.58: the strict-gap box witnesses form open subsets of the strict
complement of the order relation. -/
private lemma isOpen_strictGapBoxSet (d m R : ℕ) :
    IsOpen (strictGapBoxSet d m R) := by
  let c : ℝ := (R : ℝ) + 1
  have hbox :
      IsOpen {x : Fin d → ℝ | ∀ i, ‖x i‖ < c} := by
    simpa [Set.pi, c] using
      (isOpen_set_pi Set.finite_univ
        (fun _ _ ↦
          (isOpen_lt continuous_norm continuous_const :
            IsOpen {x : ℝ | ‖x‖ < c})))
  have hgap :
      IsOpen {z : (Fin d → ℝ) × (Fin d → ℝ) |
          ∃ i, z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i} := by
    have hgap' :
        {z : (Fin d → ℝ) × (Fin d → ℝ) |
            ∃ i, z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i} =
          ⋃ i : Fin d, {z : (Fin d → ℝ) × (Fin d → ℝ) |
            z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i} := by
      ext z
      simp
    rw [hgap']
    refine isOpen_iUnion fun i ↦ ?_
    simpa using
      isOpen_lt
        (((continuous_apply i).comp continuous_snd).add continuous_const)
        ((continuous_apply i).comp continuous_fst)
  have hshape :
      strictGapBoxSet d m R =
        {z : (Fin d → ℝ) × (Fin d → ℝ) | ∀ i, ‖z.1 i‖ < c} ∩
          ({z : (Fin d → ℝ) × (Fin d → ℝ) | ∀ i, ‖z.2 i‖ < c} ∩
            {z : (Fin d → ℝ) × (Fin d → ℝ) | ∃ i, z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i}) := by
    ext z
    simp [strictGapBoxSet, c, and_assoc, forall_and]
  -- Proof comment: the bounded box and the strict gap condition are both open, so their
  -- intersection is open as well.
  rw [hshape]
  exact (hbox.preimage continuous_fst).inter ((hbox.preimage continuous_snd).inter hgap)

/-- Helper for Theorem 17.58: every strict-gap witness set lies inside the strict complement of
the coordinatewise order relation. -/
private lemma strictGapBoxSet_subset_not_ordered (d m R : ℕ) :
    strictGapBoxSet d m R ⊆
      ({z : (Fin d → ℝ) × (Fin d → ℝ) | ¬ z.1 ≤ z.2} :
        Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
  intro z hz
  rcases hz.2 with ⟨i, hi⟩
  intro hle
  have hlt : z.2 i < z.1 i := by
    have hpos : 0 < ((m : ℝ) + 1)⁻¹ := by positivity
    linarith
  exact (not_lt_of_ge (hle i)) hlt

/-- Helper for Theorem 17.58: on a bounded strict-gap witness set, sufficiently fine quantization
forces failure of the quantized order relation. -/
private lemma strictGapBoxSet_imp_quantizer_not_le
    {d m R n : ℕ} (hmn : m ≤ n) (hRn : R ≤ n) :
    strictGapBoxSet d m R ⊆
      ({z : (Fin d → ℝ) × (Fin d → ℝ) |
          ¬ coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} :
        Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
  intro z hz
  rcases hz with ⟨hbox, i, hi⟩
  have hmesh :
      ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := by
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hmn
    simpa [one_div] using (one_div_le_one_div_of_le (by positivity) hmn')
  have hgap : z.2 i + ((n : ℝ) + 1)⁻¹ < z.1 i := by
    have hadd : z.2 i + ((n : ℝ) + 1)⁻¹ ≤ z.2 i + ((m : ℝ) + 1)⁻¹ := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmesh (z.2 i)
    exact lt_of_le_of_lt hadd hi
  have hbox1 : |z.1 i| < (n : ℝ) + 1 := by
    have hRn' : (R : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hRn
    exact lt_of_lt_of_le (hbox i).1 hRn'
  have hbox2 : |z.2 i| < (n : ℝ) + 1 := by
    have hRn' : (R : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hRn
    exact lt_of_lt_of_le (hbox i).2 hRn'
  have hlt :
      scalarClipFloorQuantizer n (z.2 i) <
        scalarClipFloorQuantizer n (z.1 i) :=
    scalarClipFloorQuantizer_lt_of_meshGap (x := z.1 i) (y := z.2 i)
      hbox1 hbox2 hgap
  intro hle
  exact (not_lt_of_ge (hle i)) hlt

/-- Helper for Theorem 17.58: every pair outside the coordinatewise order relation lies in some
bounded strict-gap witness set. -/
private lemma mem_iUnion_strictGapBoxSet_of_not_ordered {d : ℕ}
    {z : (Fin d → ℝ) × (Fin d → ℝ)} (hz : ¬ z.1 ≤ z.2) :
    z ∈ ⋃ m : ℕ, ⋃ R : ℕ, strictGapBoxSet d m R := by
  have hgapExists : ∃ i : Fin d, z.2 i < z.1 i := by
    simpa [Pi.le_def, not_forall] using hz
  rcases hgapExists with ⟨i, hi⟩
  have hdiff : 0 < z.1 i - z.2 i := sub_pos.mpr hi
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hdiff
  let R : ℕ :=
    (∑ j : Fin d, Nat.ceil ‖z.1 j‖) + ∑ j : Fin d, Nat.ceil ‖z.2 j‖
  have hR1 : ∀ j : Fin d, ‖z.1 j‖ < (R : ℝ) + 1 := by
    intro j
    have hj1 :
        Nat.ceil ‖z.1 j‖ ≤ ∑ k : Fin d, Nat.ceil ‖z.1 k‖ := by
      simpa using
        (Finset.single_le_sum
          (f := fun k : Fin d ↦ Nat.ceil ‖z.1 k‖)
          (s := Finset.univ)
          (fun k _ ↦ Nat.zero_le _)
          (Finset.mem_univ j))
    have hj2 : (Nat.ceil ‖z.1 j‖ : ℝ) ≤ R := by
      exact_mod_cast (le_trans hj1 (Nat.le_add_right _ _))
    have hzj : ‖z.1 j‖ ≤ (Nat.ceil ‖z.1 j‖ : ℝ) := Nat.le_ceil _
    linarith
  have hR2 : ∀ j : Fin d, ‖z.2 j‖ < (R : ℝ) + 1 := by
    intro j
    have hj1 :
        Nat.ceil ‖z.2 j‖ ≤ ∑ k : Fin d, Nat.ceil ‖z.2 k‖ := by
      simpa using
        (Finset.single_le_sum
          (f := fun k : Fin d ↦ Nat.ceil ‖z.2 k‖)
          (s := Finset.univ)
          (fun k _ ↦ Nat.zero_le _)
          (Finset.mem_univ j))
    have hj2 : (Nat.ceil ‖z.2 j‖ : ℝ) ≤ R := by
      exact_mod_cast (le_trans hj1 (Nat.le_add_left _ _))
    have hzj : ‖z.2 j‖ ≤ (Nat.ceil ‖z.2 j‖ : ℝ) := Nat.le_ceil _
    linarith
  have hgap : z.2 i + ((m : ℝ) + 1)⁻¹ < z.1 i := by
    have hm' : ((m : ℝ) + 1)⁻¹ < z.1 i - z.2 i := by simpa using hm
    linarith
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨R, ?_⟩⟩
  exact ⟨fun j ↦ ⟨hR1 j, hR2 j⟩, ⟨i, hgap⟩⟩

/-- Helper for Theorem 17.58: once exact couplings exist for every quantized order event, the
remaining work is a weak-limit closure step back to the true order relation. -/
private lemma existsOrderedCoupling_of_quantizedApproximants {d : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    (hQuantized :
      ∀ n : ℕ,
        ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
          IsCoupling φ μ1 μ2 ∧
            (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
              {z | coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} = 1) :
    ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
      IsCoupling φ μ1 μ2 ∧
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := by
  classical
  choose φSeq hφSeqCoupling hφSeqOrdered using hQuantized
  have hTightμ1 :
      MeasureTheory.IsTightMeasureSet
        {((μ1 : ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))} := by
    simpa using
      (MeasureTheory.isTightMeasureSet_singleton
        (μ := (μ1 : Measure (Fin d → ℝ))))
  have hTightμ2 :
      MeasureTheory.IsTightMeasureSet
        {((μ2 : ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ))} := by
    simpa using
      (MeasureTheory.isTightMeasureSet_singleton
        (μ := (μ2 : Measure (Fin d → ℝ))))
  have hTightRange :
      MeasureTheory.IsTightMeasureSet
        {((φSeq n : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) :
            Measure ((Fin d → ℝ) × (Fin d → ℝ))) | n} := by
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hTightμ1
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hTightμ2
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K1, hK1Compact, hK1Tail⟩ := hTightμ1 (ε / 2) (ENNReal.half_pos (ne_of_gt hε))
    obtain ⟨K2, hK2Compact, hK2Tail⟩ := hTightμ2 (ε / 2) (ENNReal.half_pos (ne_of_gt hε))
    let K : Set (Fin d → ℝ) := K1 ∪ K2
    refine ⟨K ×ˢ K, hK1Compact.union hK2Compact |>.prod (hK1Compact.union hK2Compact), ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    have hKMeas : MeasurableSet K := (hK1Compact.union hK2Compact).isClosed.measurableSet
    have hTail1 : (μ1 : Measure (Fin d → ℝ)) Kᶜ ≤ ε / 2 := by
      -- Proof comment: enlarging the compact set can only decrease the marginal tail mass.
      have hSubset : Kᶜ ⊆ K1ᶜ := by
        intro x hx hxK1
        exact hx (Or.inl hxK1)
      exact (measure_mono hSubset).trans (hK1Tail _ (by simp))
    have hTail2 : (μ2 : Measure (Fin d → ℝ)) Kᶜ ≤ ε / 2 := by
      -- Proof comment: the second marginal tail is handled in the same way using `K2`.
      have hSubset : Kᶜ ⊆ K2ᶜ := by
        intro x hx hxK2
        exact hx (Or.inr hxK2)
      exact (measure_mono hSubset).trans (hK2Tail _ (by simp))
    -- Proof comment: a common compact box controls every coupling because both marginals are
    -- fixed along the whole sequence.
    calc
      ((φSeq n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ((K ×ˢ K)ᶜ))
          ≤ (μ1 : Measure (Fin d → ℝ)) Kᶜ + (μ2 : Measure (Fin d → ℝ)) Kᶜ :=
        measure_prodCompl_le_of_isCoupling (hφSeqCoupling n) hKMeas
      _ ≤ ε / 2 + ε / 2 := add_le_add hTail1 hTail2
      _ = ε := ENNReal.add_halves ε
  have hCompactRange :
      IsCompact (closure (Set.range φSeq)) := by
    simpa using
      (isCompact_closure_of_isTightMeasureSet
        (S := Set.range φSeq)
        (by simpa using hTightRange))
  have hRangeClosure :
      ∀ n : ℕ, φSeq n ∈ closure (Set.range φSeq) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  rcases hCompactRange.tendsto_subseq hRangeClosure with ⟨φ, _, σ, hσmono, hσTendsto⟩
  have hClosedCoupling :
      IsClosed
        {π : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) | IsCoupling π μ1 μ2} := by
    let fstPush :
        ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) →
          ProbabilityMeasure (Fin d → ℝ) :=
      fun π ↦ π.map continuous_fst.measurable.aemeasurable
    let sndPush :
        ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) →
          ProbabilityMeasure (Fin d → ℝ) :=
      fun π ↦ π.map continuous_snd.measurable.aemeasurable
    have hfstCont : Continuous fstPush := ProbabilityMeasure.continuous_map continuous_fst
    have hsndCont : Continuous sndPush := ProbabilityMeasure.continuous_map continuous_snd
    have hDescr :
        {π : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) | IsCoupling π μ1 μ2} =
          fstPush ⁻¹' {μ1} ∩ sndPush ⁻¹' {μ2} := by
      ext π
      simp [fstPush, sndPush, isCoupling_iff]
    -- Proof comment: exact marginal constraints are closed because both coordinate pushforwards
    -- vary continuously in the weak topology.
    rw [hDescr]
    exact (isClosed_singleton.preimage hfstCont).inter
      (isClosed_singleton.preimage hsndCont)
  have hCouplingLimit : IsCoupling φ μ1 μ2 := by
    -- Proof comment: every measure in the subsequence is a coupling of the same marginals, so the
    -- weak limit stays inside the closed coupling set.
    exact hClosedCoupling.mem_of_tendsto hσTendsto
      (Filter.Eventually.of_forall fun n ↦ hφSeqCoupling (σ n))
  have hGapZero :
      ∀ m R : ℕ,
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R) = 0 := by
    intro m R
    have hEventuallyZero :
        ∀ᶠ k in Filter.atTop,
          ((φSeq (σ k) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R)) = 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨max m R, ?_⟩
      intro k hk
      have hkσ : k ≤ σ k := StrictMono.id_le hσmono k
      have hmσ : m ≤ σ k := by
        exact le_trans (le_max_left _ _) (le_trans hk hkσ)
      have hRσ : R ≤ σ k := by
        exact le_trans (le_max_right _ _) (le_trans hk hkσ)
      have hSubset :
          strictGapBoxSet d m R ⊆
            ({z : (Fin d → ℝ) × (Fin d → ℝ) |
                ¬ coordGridQuantizer d (σ k) z.1 ≤ coordGridQuantizer d (σ k) z.2} :
              Set ((Fin d → ℝ) × (Fin d → ℝ))) :=
        strictGapBoxSet_imp_quantizer_not_le (d := d) (m := m) (R := R) hmσ hRσ
      have hQuantizedMeas :
          MeasurableSet
            ({z : (Fin d → ℝ) × (Fin d → ℝ) |
                coordGridQuantizer d (σ k) z.1 ≤ coordGridQuantizer d (σ k) z.2} :
              Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
        let quantizedPair :
            ((Fin d → ℝ) × (Fin d → ℝ)) → ((Fin d → ℝ) × (Fin d → ℝ)) :=
          fun z ↦ (coordGridQuantizer d (σ k) z.1, coordGridQuantizer d (σ k) z.2)
        have hQuantizedPairMeas : Measurable quantizedPair := by
          exact ((measurable_coordGridQuantizer d (σ k)).comp measurable_fst).prodMk
            ((measurable_coordGridQuantizer d (σ k)).comp measurable_snd)
        -- Proof comment: the quantized order event is the preimage of the ambient ordered set
        -- under the measurable quantizer pair map.
        change MeasurableSet (quantizedPair ⁻¹'
          ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
            Set ((Fin d → ℝ) × (Fin d → ℝ))))
        exact (measurableSet_orderedPairSet d).preimage hQuantizedPairMeas
      have hNotQuantizedZero :
          ((φSeq (σ k) : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
              ({z : (Fin d → ℝ) × (Fin d → ℝ) |
                  ¬ coordGridQuantizer d (σ k) z.1 ≤ coordGridQuantizer d (σ k) z.2} :
                Set ((Fin d → ℝ) × (Fin d → ℝ)))) = 0 := by
        simpa using
          (MeasureTheory.prob_compl_eq_zero_iff hQuantizedMeas).2 (hφSeqOrdered (σ k))
      exact le_antisymm ((measure_mono hSubset).trans hNotQuantizedZero.le) bot_le
    have hGapLiminf :
        Filter.liminf
            (fun k ↦
              ((φSeq (σ k) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R)))
            Filter.atTop = 0 := by
      have hEventuallyEqZero :
          (fun k ↦
            ((φSeq (σ k) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R))) =ᶠ[Filter.atTop]
            fun _ ↦ (0 : ℝ≥0∞) := hEventuallyZero
      refine Filter.Tendsto.liminf_eq ?_
      exact tendsto_const_nhds.congr' hEventuallyEqZero.symm
    -- Proof comment: each strict-gap witness set is eventually excluded by sufficiently fine
    -- quantizers, so Portmanteau forces zero mass on that open witness in the limit.
    refine le_antisymm ?_ bot_le
    calc
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R)
          ≤ Filter.liminf
              (fun k ↦
                ((φSeq (σ k) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R)))
              Filter.atTop :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto
          (μ := φ) (μs := fun k ↦ φSeq (σ k)) hσTendsto
          (G := strictGapBoxSet d m R) (isOpen_strictGapBoxSet d m R)
      _ = 0 := hGapLiminf
  have hStrictComplement :
      ({z : (Fin d → ℝ) × (Fin d → ℝ) | ¬ z.1 ≤ z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ))) =
        ⋃ m : ℕ, ⋃ R : ℕ, strictGapBoxSet d m R := by
    ext z
    constructor
    · intro hz
      exact mem_iUnion_strictGapBoxSet_of_not_ordered hz
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨m, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨R, hz⟩
      exact strictGapBoxSet_subset_not_ordered d m R hz
  have hStrictComplementZero :
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
        ({z : (Fin d → ℝ) × (Fin d → ℝ) | ¬ z.1 ≤ z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ))) = 0 := by
    rw [hStrictComplement]
    refine le_antisymm ?_ bot_le
    calc
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (⋃ m : ℕ, ⋃ R : ℕ, strictGapBoxSet d m R)
          ≤ ∑' m : ℕ,
              (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (⋃ R : ℕ, strictGapBoxSet d m R) :=
        MeasureTheory.measure_iUnion_le (fun m ↦ ⋃ R : ℕ, strictGapBoxSet d m R)
      _ ≤ ∑' m : ℕ, ∑' R : ℕ,
            (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (strictGapBoxSet d m R) := by
          gcongr with m
          exact MeasureTheory.measure_iUnion_le (fun R ↦ strictGapBoxSet d m R)
      _ = 0 := by simp [hGapZero]
  have hOrderedComplement :
      (({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ)))ᶜ) =
        ({z : (Fin d → ℝ) × (Fin d → ℝ) | ¬ z.1 ≤ z.2} :
          Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
    ext z
    simp
  have hOrderedMass :
      (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := by
    have hOrderedComplZero :
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
          (({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
              Set ((Fin d → ℝ) × (Fin d → ℝ)))ᶜ) = 0 := by
      simpa [hOrderedComplement] using hStrictComplementZero
    have hComplEq :
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
            (({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
                Set ((Fin d → ℝ) × (Fin d → ℝ)))ᶜ) =
          1 -
            (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
              ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
                Set ((Fin d → ℝ) × (Fin d → ℝ))) :=
      MeasureTheory.prob_compl_eq_one_sub (μ := (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
        (measurableSet_orderedPairSet d)
    rw [hOrderedComplZero] at hComplEq
    have hOneLe :
        1 ≤
          (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
            ({z : (Fin d → ℝ) × (Fin d → ℝ) | z.1 ≤ z.2} :
              Set ((Fin d → ℝ) × (Fin d → ℝ))) := by
      exact (tsub_eq_zero_iff_le.mp hComplEq.symm)
    exact le_antisymm MeasureTheory.prob_le_one hOneLe
  exact ⟨φ, hCouplingLimit, hOrderedMass⟩

/-- Helper for Theorem 17.58: the positive-dimensional converse is the remaining Strassen
existence step. -/
lemma existsOrderedCoupling_of_stochasticLE_pos {d : ℕ}
    (hd : d ≠ 0) {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)}
    (hStochastic : StochasticLE μ1 μ2) :
    ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
      IsCoupling φ μ1 μ2 ∧
        (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := by
  -- Route correction: the zero-dimensional branch is already closed above, so the unresolved work
  -- is now isolated to the genuine positive-dimensional Strassen existence theorem.
  by_cases h1 : d = 1
  · subst h1
    have hcdf :
        ∀ x : ℝ,
          ProbabilityTheory.cdf (fin1RealLaw μ2 : Measure ℝ) x ≤
            ProbabilityTheory.cdf (fin1RealLaw μ1 : Measure ℝ) x := by
      -- Proof comment: in dimension `1`, `StochasticLE` already gives the required CDF order
      -- after reading singleton vectors by their unique coordinate.
      intro x
      exact cdf_le_of_stochasticLE_finOne (μ1 := μ1) (μ2 := μ2) hStochastic x
    rcases existsOrderedRealCoupling_of_cdf_le hcdf with ⟨ψ, hψCoupling, hψOrdered⟩
    refine ⟨ψ.map measurable_realPairToFin1Pair.aemeasurable, ?_, ?_⟩
    · -- Proof comment: the real ordered coupling transports back to the original `Fin 1 → ℝ`
      -- marginals coordinatewise.
      exact isCoupling_map_realPairToFin1Pair hψCoupling
    · -- Proof comment: the ordered support event is invariant under the same back-transport.
      exact orderedMassOne_map_realPairToFin1Pair hψOrdered
  · -- Proof comment: once `d ≠ 1`, the unresolved work is the genuinely multidimensional
    -- Strassen existence layer, not the one-dimensional CDF reduction just established.
    -- Route correction: the earlier upper-set residual route is no longer the right frontier.
    have hQuantizedUpper :
        ∀ n : ℕ,
          let s := quantizedRange d n
          let ν1 : ProbabilityMeasure s := μ1.map (measurable_quantizedRangeMap d n).aemeasurable
          let ν2 : ProbabilityMeasure s := μ2.map (measurable_quantizedRangeMap d n).aemeasurable
          ∀ U : Set s, IsUpperSet U → (ν1 : Measure s) U ≤ (ν2 : Measure s) U := by
      intro n
      -- Proof comment: the already-proved stochastic order on the ambient quantized laws is now
      -- repackaged as the finite upper-set invariant on the actual quantized image subtype.
      exact upperSetLE_of_stochasticLE_quantizedRange
        (d := d) (n := n) (μ1 := μ1) (μ2 := μ2)
        (stochasticLE_map_coordGridQuantizer (d := d) (n := n) hStochastic)
    have hQuantizedHall :
        ∀ n : ℕ,
          let s := quantizedRange d n
          let ν1 : ProbabilityMeasure s := μ1.map (measurable_quantizedRangeMap d n).aemeasurable
          let ν2 : ProbabilityMeasure s := μ2.map (measurable_quantizedRangeMap d n).aemeasurable
          ∀ A : Finset s,
            Finset.sum A (fun a ↦ (ν1 : Measure s) {a}) ≤
              (ν2 : Measure s) {b | ∃ a ∈ A, a ≤ b} := by
      intro n
      letI : Fintype (quantizedRange d n) := (coordGridQuantizer_range_finite d n).fintype
      -- Proof comment: the source-facing upper-set inequalities already imply the Hall
      -- neighborhood inequalities on singleton masses that the missing finite matrix theorem
      -- should consume.
      exact hallCondition_of_upperSetLE_finite
        (ν1 := μ1.map (measurable_quantizedRangeMap d n).aemeasurable)
        (ν2 := μ2.map (measurable_quantizedRangeMap d n).aemeasurable)
        (hUpper := hQuantizedUpper n)
    have hQuantizedCoupling :
        ∀ n : ℕ,
          ∃ ψ : ProbabilityMeasure ((quantizedRange d n) × (quantizedRange d n)),
            IsCoupling ψ
              (μ1.map (measurable_quantizedRangeMap d n).aemeasurable)
              (μ2.map (measurable_quantizedRangeMap d n).aemeasurable) ∧
              (ψ : Measure ((quantizedRange d n) × (quantizedRange d n)))
                {z | z.1 ≤ z.2} = 1 := by
      intro n
      letI : Fintype (quantizedRange d n) := (coordGridQuantizer_range_finite d n).fintype
      -- Proof comment: the quantized Hall inequalities now feed directly into the finite coupling
      -- adapter, so the remaining issue is no longer inside the subtype packaging layer.
      exact existsOrderedCoupling_finite_of_hall
        (ν1 := μ1.map (measurable_quantizedRangeMap d n).aemeasurable)
        (ν2 := μ2.map (measurable_quantizedRangeMap d n).aemeasurable)
        (hHall := hQuantizedHall n)
    have hAmbientQuantized :
        ∀ n : ℕ,
          ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
            IsCoupling φ μ1 μ2 ∧
              (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
                {z | coordGridQuantizer d n z.1 ≤ coordGridQuantizer d n z.2} = 1 := by
      intro n
      rcases hQuantizedCoupling n with ⟨ψ, hψCoupling, hψOrdered⟩
      -- Proof comment: the exact subtype-to-ambient lift is already stable, so each finite
      -- quantized ordered coupling produces an ambient coupling of `μ1` and `μ2`.
      exact existsExactCoupling_of_quantizedCoupling
        (μ1 := μ1) (μ2 := μ2) hψCoupling hψOrdered
    -- Proof comment: after the finite subtype theorem and the exact lift, the only frontier left
    -- is the weak-limit closure step from quantized order events to the true closed order set.
    exact existsOrderedCoupling_of_quantizedApproximants hAmbientQuantized

/-- Theorem 17.58 (Strassen): stochastic order is equivalent to the existence of a coupling
supported on the coordinatewise order relation. -/
theorem stochasticLE_iff_exists_ordered_coupling {d : ℕ}
    {μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)} :
    StochasticLE μ1 μ2 ↔
      ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
        IsCoupling φ μ1 μ2 ∧
          (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := by
  constructor
  · intro hStochastic
    by_cases h0 : d = 0
    · subst h0
      -- Proof comment: in dimension `0`, the product coupling is already ordered.
      exact existsOrderedCoupling_finZero μ1 μ2
    · -- Proof comment: delegate the genuine positive-dimensional existence step to the dedicated
      -- helper frontier above.
      exact existsOrderedCoupling_of_stochasticLE_pos h0 hStochastic
  · rintro ⟨φ, hCoupling, hOrderedMass⟩
    -- Proof comment: the reverse implication is the packaged coupling-to-order argument.
    exact stochasticLE_of_isCoupling_of_orderedMassOne hCoupling hOrderedMass

end ProbabilityTheory
