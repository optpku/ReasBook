/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff

namespace VariationalRegularization.LpDual

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (p : ENNReal) [Fact (1 ≤ p)]

/-- Indicators of measurable sets, extended by zero on nonmeasurable sets. -/
@[expose] def indicator (s : Set α) : Lp ℝ p μ := by
  classical
  exact if hs : MeasurableSet s then indicatorConstLp p hs (measure_ne_top μ s) 1 else 0

omit [Fact (1 ≤ p)] in
lemma indicator_of_measurable {s : Set α} (hs : MeasurableSet s) :
    indicator μ p s = indicatorConstLp p hs (measure_ne_top μ s) 1 := by
  simp only [indicator, dif_pos hs]

omit [Fact (1 ≤ p)] in
@[simp] lemma indicator_empty : indicator μ p ∅ = 0 := by
  rw [indicator_of_measurable μ p MeasurableSet.empty, indicatorConstLp_empty]

omit [Fact (1 ≤ p)] in
lemma indicator_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hd : Disjoint s t) : indicator μ p (s ∪ t) = indicator μ p s + indicator μ p t := by
  simp only [indicator_of_measurable μ p (hs.union ht), indicator_of_measurable μ p hs,
    indicator_of_measurable μ p ht]
  exact indicatorConstLp_disjoint_union hs ht (measure_ne_top μ s) (measure_ne_top μ t) hd 1

omit [Fact (1 ≤ p)] in
lemma indicator_finset_iUnion {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) (F : Finset ℕ) :
    indicator μ p (⋃ n ∈ F, s n) = ∑ n ∈ F, indicator μ p (s n) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert n F hn ih =>
    have hF : MeasurableSet (⋃ m ∈ F, s m) :=
      MeasurableSet.iUnion (fun m ↦ MeasurableSet.iUnion (fun _ ↦ hs m))
    rw [Finset.set_biUnion_insert, indicator_union μ p (hs n) hF]
    · rw [ih, Finset.sum_insert hn]
    · apply disjoint_iUnion₂_right.mpr
      intro m hm
      exact hd (ne_of_mem_of_not_mem hm hn).symm

/-- Disjoint indicators form an unconditionally convergent series in finite
`Lp`. This supplies countable additivity before applying a functional. -/
lemma hasSum_indicator {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) (hp : p ≠ ∞) :
    HasSum (fun n ↦ indicator μ p (s n)) (indicator μ p (⋃ n, s n)) := by
  classical
  let U : Finset ℕ → Set α := fun F ↦ ⋃ n ∈ F, s n
  let S : Set α := ⋃ n, s n
  have hU : ∀ F, MeasurableSet (U F) := fun F ↦
    MeasurableSet.iUnion (fun n ↦ MeasurableSet.iUnion (fun _ ↦ hs n))
  have hS : MeasurableSet S := MeasurableSet.iUnion hs
  have hUS : ∀ F, U F ⊆ S := fun F ↦ iUnion₂_subset_iUnion _ _
  have hmono : Monotone U := fun _ _ h ↦ biUnion_subset_biUnion_left h
  have hi : ⋂ F : Finset ℕ, S \ U F = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxS := (mem_iInter.mp hx ∅).1
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxS
    have hx' := (mem_iInter.mp hx {n}).2
    exact hx' (mem_iUnion₂.mpr ⟨n, Finset.mem_singleton_self n, hxn⟩)
  have htail : Tendsto (fun F : Finset ℕ ↦ μ (S \ U F)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun F ↦ (hS.diff (hU F)).nullMeasurableSet)
      (fun F G hFG x hx ↦ ⟨hx.1, fun hxF ↦ hx.2 (hmono hFG hxF)⟩)
      ⟨∅, measure_ne_top μ _⟩
    simpa only [Function.comp_def, hi, measure_empty] using h
  have hsymm : ∀ F, U F ∆ S = S \ U F := fun F ↦ symmDiff_of_le (hUS F)
  have hlim := tendsto_indicatorConstLp_set (μ := μ) (p := p) (c := (1 : ℝ))
    (ht := hU) (hs := hS) (hμt := fun F ↦ measure_ne_top μ (U F))
    (hμs := measure_ne_top μ S) hp (by simpa only [hsymm] using htail)
  change Tendsto (fun F : Finset ℕ ↦ ∑ n ∈ F, indicator μ p (s n)) atTop _
  convert hlim using 1
  · funext F
    rw [← indicator_finset_iUnion μ p hs hd]
    exact indicator_of_measurable μ p (hU F)
  · congr 1
    exact indicator_of_measurable μ p hS

/-- The signed measure determined by a bounded linear functional on `Lp`. -/
@[expose] def functionalMeasure (hp : p ≠ ∞) (ℓ : StrongDual ℝ (Lp ℝ p μ)) : SignedMeasure α where
  measureOf' s := ℓ (indicator μ p s)
  empty' := by simp
  not_measurable' s hs := by simp only [indicator, dif_neg hs, map_zero]
  m_iUnion' s hs hd := (hasSum_indicator μ p hs hd hp).mapL ℓ

lemma functionalMeasure_apply (hp : p ≠ ∞) (ℓ : StrongDual ℝ (Lp ℝ p μ))
    (s : Set α) : functionalMeasure μ p hp ℓ s = ℓ (indicator μ p s) := rfl

/-- Null sets have zero indicator in `Lp`, hence zero functional measure. -/
lemma functionalMeasure_absolutelyContinuous (hp : p ≠ ∞)
    (ℓ : StrongDual ℝ (Lp ℝ p μ)) :
    functionalMeasure μ p hp ℓ ≪ᵥ μ.toENNRealVectorMeasure := by
  intro s hs0
  by_cases hs : MeasurableSet s
  · have hμs : μ s = 0 := by simpa only [Measure.toENNRealVectorMeasure_apply_measurable hs] using hs0
    rw [functionalMeasure_apply, indicator_of_measurable μ p hs]
    have hi : indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ) = 0 := by
      have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one Fact.out
      have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
      apply norm_eq_zero.mp
      rw [norm_indicatorConstLp hp0.ne' hp]
      simp only [measureReal_def, hμs, ENNReal.toReal_zero, norm_one, one_mul]
      exact Real.zero_rpow (one_div_pos.mpr hpr).ne'
    rw [hi, map_zero]
  · exact VectorMeasure.not_measurable _ hs

/-- The integrable Radon--Nikodym density represents the functional on indicators. -/
theorem exists_integrable_density (hp : p ≠ ∞) (ℓ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧
      ∀ s, MeasurableSet s → ℓ (indicator μ p s) = ∫ x in s, g x ∂μ := by
  let ν := functionalMeasure μ p hp ℓ
  refine ⟨ν.rnDeriv μ, SignedMeasure.measurable_rnDeriv ν μ,
    SignedMeasure.integrable_rnDeriv ν μ, ?_⟩
  intro s hs
  have h := congrArg (fun v : SignedMeasure α ↦ v s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq ν μ (functionalMeasure_absolutelyContinuous μ p hp ℓ))
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv ν μ) hs] at h
  exact h.symm

end VariationalRegularization.LpDual
