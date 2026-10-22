/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap08
section Section01

/-- Definition 8.1 (Simple functions): for a function `f : Ω → ℝ` on a measurable-domain
subset `Ω ⊆ ℝ^n`, being simple means `Ω` is measurable, `f` is measurable, and `f` takes
only finitely many values (equivalently, `f(Ω)` is finite). -/
def IsSimpleFunction {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : Ω → ℝ) : Prop :=
  MeasurableSet Ω ∧ Measurable f ∧ (Set.range f).Finite

/-- Helper for Lemma 8.1: the range of a pointwise sum is contained in the image of the
sum-map on the product of ranges. -/
lemma helperForLemma_8_1_range_add_subset_image_prod {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : Ω → ℝ) :
    Set.range (fun x : Ω => f x + g x) ⊆
      (fun p : ℝ × ℝ => p.1 + p.2) '' ((Set.range f) ×ˢ (Set.range g)) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨(f x, g x), ?_, rfl⟩
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

/-- Helper for Lemma 8.1: finite range is preserved by pointwise addition. -/
lemma helperForLemma_8_1_range_add_finite {n : ℕ} {Ω : Set (Fin n → ℝ)} (f g : Ω → ℝ)
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) :
    (Set.range (fun x : Ω => f x + g x)).Finite := by
  have hprod : (((Set.range f) ×ˢ (Set.range g)) : Set (ℝ × ℝ)).Finite := hf.prod hg
  have himage :
      ((fun p : ℝ × ℝ => p.1 + p.2) '' ((Set.range f) ×ˢ (Set.range g))).Finite :=
    hprod.image (fun p : ℝ × ℝ => p.1 + p.2)
  exact himage.subset (helperForLemma_8_1_range_add_subset_image_prod f g)

/-- Helper for Lemma 8.1: finite range is preserved by scalar multiplication. -/
lemma helperForLemma_8_1_range_constMul_finite {n : ℕ} {Ω : Set (Fin n → ℝ)} (f : Ω → ℝ)
    (c : ℝ) (hf : (Set.range f).Finite) : (Set.range (fun x : Ω => c * f x)).Finite := by
  have himage : ((fun y : ℝ => c * y) '' (Set.range f)).Finite := hf.image (fun y : ℝ => c * y)
  refine himage.subset ?_
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, rfl⟩

namespace IsSimpleFunction

/-- Helper for Lemma 8.1: simple functions are closed under pointwise addition. -/
lemma add {n : ℕ} {Ω : Set (Fin n → ℝ)} {f g : Ω → ℝ}
    (hf : IsSimpleFunction Ω f) (hg : IsSimpleFunction Ω g) :
    IsSimpleFunction Ω (fun x : Ω => f x + g x) := by
  rcases hf with ⟨hΩ, hf_meas, hf_fin⟩
  rcases hg with ⟨_, hg_meas, hg_fin⟩
  exact ⟨hΩ, hf_meas.add hg_meas, helperForLemma_8_1_range_add_finite f g hf_fin hg_fin⟩

/-- Helper for Lemma 8.1: simple functions are closed under real scalar multiplication. -/
lemma const_mul {n : ℕ} {Ω : Set (Fin n → ℝ)} {f : Ω → ℝ}
    (hf : IsSimpleFunction Ω f) (c : ℝ) :
    IsSimpleFunction Ω (fun x : Ω => c * f x) := by
  rcases hf with ⟨hΩ, hf_meas, hf_fin⟩
  exact ⟨hΩ, hf_meas.const_mul c, helperForLemma_8_1_range_constMul_finite f c hf_fin⟩

end IsSimpleFunction

/-- Lemma 8.1: simple functions are closed under pointwise addition and scalar multiplication. -/
theorem lemma_8_1 {n : ℕ} {Ω : Set (Fin n → ℝ)} {f g : Ω → ℝ}
    (hf : IsSimpleFunction Ω f) (hg : IsSimpleFunction Ω g) :
    IsSimpleFunction Ω (fun x : Ω => f x + g x) ∧
      ∀ c : ℝ, IsSimpleFunction Ω (fun x : Ω => c * f x) := by
  constructor
  · exact IsSimpleFunction.add hf hg
  · intro c
    exact IsSimpleFunction.const_mul hf c

/-- Definition 8.2 (Characteristic function): for a measurable set `Ω ⊆ ℝ^n` and a
measurable subset `E ⊆ Ω`, the characteristic (indicator) function `χ_E : Ω → ℝ` is
`χ_E(x) = 1` for `x ∈ E` and `χ_E(x) = 0` for `x ∉ E`. -/
noncomputable def characteristicFunction {n : ℕ} (Ω : Set (Fin n → ℝ)) (E : Set Ω) : Ω → ℝ :=
  letI : DecidablePred (fun y : Ω => y ∈ E) := Classical.decPred (fun y : Ω => y ∈ E)
  fun x => if x ∈ E then 1 else 0

/-- Helper for Lemma 8.2: indexing coefficients by an equivalence with `Fin N`
is injective after coercing from `Set.range f` to `ℝ`. -/
lemma helperForLemma_8_2_coeffIndexing_injective {n N : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ℝ} (e : Fin N ≃ Set.range f) :
    Function.Injective (fun i : Fin N => (e i).1) := by
  intro i j hij
  apply e.injective
  apply Subtype.ext
  simpa using hij

/-- Helper for Lemma 8.2: the ambient-space fibers of a measurable `f : Ω → ℝ`
are measurable and lie inside `Ω`. -/
lemma helperForLemma_8_2_fiberSets_measurable_subset {n N : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ℝ} (hΩ : MeasurableSet Ω) (hf_meas : Measurable f) (c : Fin N → ℝ) :
    (∀ i : Fin N, MeasurableSet (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c i}))) ∧
      (∀ i : Fin N, (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c i})) ⊆ Ω) := by
  refine ⟨?_, ?_⟩
  · intro i
    have hpre : MeasurableSet (f ⁻¹' {c i}) := hf_meas (MeasurableSet.singleton (c i))
    exact MeasurableSet.subtype_image hΩ hpre
  · intro i x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property

/-- Helper for Lemma 8.2: for `x ∈ Ω`, membership in an ambient fiber is equivalent
to the corresponding value equation for `f`. -/
lemma helperForLemma_8_2_mem_fiberSet_iff {n N : ℕ} {Ω : Set (Fin n → ℝ)} {f : Ω → ℝ}
    (c : Fin N → ℝ) {x : Fin n → ℝ} (hx : x ∈ Ω) (i : Fin N) :
    x ∈ (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c i})) ↔ f ⟨x, hx⟩ = c i := by
  constructor
  · intro hxE
    rcases hxE with ⟨y, hy, hyx⟩
    have hyEq : y = ⟨x, hx⟩ := by
      apply Subtype.ext
      exact hyx
    have hyVal : f y = c i := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy
    simpa [hyEq] using hyVal
  · intro hfx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hfx

/-- Helper for Lemma 8.2: distinct fibers of coefficient values are disjoint. -/
lemma helperForLemma_8_2_pairwiseDisjoint_fiberSets {n N : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ℝ} (c : Fin N → ℝ) (hc_inj : Function.Injective c) :
    Pairwise
      (fun i j : Fin N =>
        Disjoint (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c i}))
          (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c j}))) := by
  intro i j hij
  refine Set.disjoint_left.2 ?_
  intro x hxi hxj
  rcases hxi with ⟨y, hy, rfl⟩
  have hfi : f y = c i := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy
  have hfj : f y = c j := by
    rcases hxj with ⟨z, hz, hzEq⟩
    have hzSub : z = y := by
      apply Subtype.ext
      exact hzEq
    have hzVal : f z = c j := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
    simpa [hzSub] using hzVal
  have hcoeff : c i = c j := by
    calc
      c i = f y := by simpa [hfi]
      _ = c j := hfj
  exact hij (hc_inj hcoeff)

/-- Helper for Lemma 8.2: at each `x ∈ Ω`, the finite coefficient/indicator sum
collapses to the unique index corresponding to the value `f x`. -/
lemma helperForLemma_8_2_pointwise_sum_representation {n N : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ℝ} (e : Fin N ≃ Set.range f) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    f ⟨x, hx⟩ =
      (Finset.univ : Finset (Fin N)).sum
        (fun i : Fin N =>
          (e i).1 *
            Set.indicator (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i).1}))
              (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
  let i0 : Fin N := e.symm ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  have hi0_eq : e i0 = ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
    simpa [i0] using e.apply_symm_apply ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  have hi0_val : (e i0).1 = f ⟨x, hx⟩ := congrArg Subtype.val hi0_eq
  have hi0_mem :
      x ∈ (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i0).1})) := by
    refine (helperForLemma_8_2_mem_fiberSet_iff (f := f) (c := fun i : Fin N => (e i).1)
        (hx := hx) (i := i0)).2 ?_
    exact hi0_val.symm
  have hsum :
      (Finset.univ : Finset (Fin N)).sum
        (fun i : Fin N =>
          (e i).1 *
            Set.indicator (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i).1}))
              (fun _ : Fin n → ℝ => (1 : ℝ)) x) =
        (e i0).1 *
          Set.indicator (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i0).1}))
            (fun _ : Fin n → ℝ => (1 : ℝ)) x := by
    refine Finset.sum_eq_single i0 ?_ ?_
    · intro j hj hjne
      have hx_not_mem :
          x ∉ (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e j).1})) := by
        intro hxj
        have hfj : f ⟨x, hx⟩ = (e j).1 :=
          (helperForLemma_8_2_mem_fiberSet_iff (f := f) (c := fun i : Fin N => (e i).1)
            (hx := hx) (i := j)).1 hxj
        have hcoeff : (e j).1 = (e i0).1 := by
          calc
            (e j).1 = f ⟨x, hx⟩ := hfj.symm
            _ = (e i0).1 := hi0_val.symm
        have hji : j = i0 := (helperForLemma_8_2_coeffIndexing_injective (f := f) e) hcoeff
        exact hjne hji
      simp [Set.indicator_of_notMem hx_not_mem]
    · intro hi0_not_mem
      exact False.elim (hi0_not_mem (Finset.mem_univ i0))
  calc
    f ⟨x, hx⟩ = (e i0).1 := hi0_val.symm
    _ = (e i0).1 *
          Set.indicator (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i0).1}))
            (fun _ : Fin n → ℝ => (1 : ℝ)) x := by
          simp [Set.indicator_of_mem hi0_mem]
    _ = (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            (e i).1 *
              Set.indicator (((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {(e i).1}))
                (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
          simpa using hsum.symm

/-- Lemma 8.2: if `f : Ω → ℝ` is simple, then there are `N : ℕ`, coefficients
`c : Fin N → ℝ`, and pairwise disjoint measurable sets `E i ⊆ Ω` such that
`f = ∑ i=1^N c_i χ_{E_i}` on `Ω`.

In this file, `IsSimpleFunction Ω f` (Definition 8.1) already packages that `Ω`
is measurable, `f` is measurable, and `f` has finite range; the book's phrase
"simple, i.e. finitely many values" is used as shorthand. -/
theorem lemma_8_2 {n : ℕ} {Ω : Set (Fin n → ℝ)} {f : Ω → ℝ}
    (hΩ : MeasurableSet Ω) (hf : IsSimpleFunction Ω f) :
    ∃ N : ℕ, ∃ c : Fin N → ℝ, ∃ E : Fin N → Set (Fin n → ℝ),
      (∀ i : Fin N, MeasurableSet (E i)) ∧
      (∀ i : Fin N, E i ⊆ Ω) ∧
      Pairwise (fun i j : Fin N => Disjoint (E i) (E j)) ∧
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        f ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
  rcases hf with ⟨_, hf_meas, hf_fin⟩
  classical
  letI : Fintype (Set.range f) := hf_fin.fintype
  let N : ℕ := Fintype.card (Set.range f)
  let e : Fin N ≃ Set.range f := (Fintype.equivFin (Set.range f)).symm
  let c : Fin N → ℝ := fun i : Fin N => (e i).1
  let E : Fin N → Set (Fin n → ℝ) :=
    fun i : Fin N => ((↑) : Ω → Fin n → ℝ) '' (f ⁻¹' {c i})
  refine ⟨N, c, E, ?_, ?_, ?_, ?_⟩
  · have hE := helperForLemma_8_2_fiberSets_measurable_subset (f := f) hΩ hf_meas c
    intro i
    simpa [E] using hE.1 i
  · have hE := helperForLemma_8_2_fiberSets_measurable_subset (f := f) hΩ hf_meas c
    intro i
    simpa [E] using hE.2 i
  · have hc_inj : Function.Injective c := by
      dsimp [c]
      exact helperForLemma_8_2_coeffIndexing_injective (f := f) e
    have hPair := helperForLemma_8_2_pairwiseDisjoint_fiberSets (f := f) c hc_inj
    simpa [E] using hPair
  · intro x hx
    have hpoint := helperForLemma_8_2_pointwise_sum_representation (f := f) e hx
    simpa [c, E] using hpoint

/-- A non-negative simple real-valued function on `Ω`. -/
def NonnegSimpleFunction {n : ℕ} (Ω : Set (Fin n → ℝ)) : Type _ :=
  { f : Ω → ℝ // IsSimpleFunction Ω f ∧ ∀ x : Ω, 0 ≤ f x }

/-- Definition 8.3 (Lebesgue integral of a non-negative simple function): for
`f : Ω → [0, ∞)` simple, define
`∫_Ω f dm = ∑_{λ ∈ f(Ω), λ > 0} λ * m({x ∈ Ω | f x = λ})`. -/
noncomputable def lebesgueIntegralNonnegSimple {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f : NonnegSimpleFunction Ω) : ENNReal :=
  (((f.2.1.2.2.toFinset).filter (fun r : ℝ => 0 < r)).sum (fun r : ℝ =>
    ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))))

/-- Helper for Proposition 8.1.1: the integral sum is zero exactly when each positive-value
fiber has zero ambient volume. -/
lemma helperForProposition_8_1_1_integral_eq_zero_iff_forall_posFiber_zero {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (f : NonnegSimpleFunction Ω) :
    (((f.2.1.2.2.toFinset).filter (fun r : ℝ => 0 < r)).sum (fun r : ℝ =>
      ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) = 0) ↔
      ∀ r ∈ ((f.2.1.2.2.toFinset).filter (fun r : ℝ => 0 < r)),
        MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) = 0 := by
  constructor
  · intro hsum r hr
    have hterm :
        ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) = 0 :=
      (Finset.sum_eq_zero_iff.mp hsum) r hr
    have hrpos : 0 < r := (Finset.mem_filter.mp hr).2
    have hofReal_ne_zero : ENNReal.ofReal r ≠ 0 := by
      intro hzero
      have hrle : r ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
      linarith
    exact (mul_eq_zero.mp hterm).resolve_left hofReal_ne_zero
  · intro hvol
    refine Finset.sum_eq_zero_iff.mpr ?_
    intro r hr
    simp [hvol r hr]

/-- Helper for Proposition 8.1.1: each positive-value fiber is contained in the ambient nonzero
image of `f`. -/
lemma helperForProposition_8_1_1_posFiber_subset_nonzeroImage {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (f : NonnegSimpleFunction Ω) {r : ℝ}
    (hr : r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t))) :
    (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) ⊆
      (((↑) : Ω → Fin n → ℝ) '' {x : Ω | f.1 x ≠ 0}) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hrpos : 0 < r := (Finset.mem_filter.mp hr).2
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hxr : f.1 x = r := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx
  have hxnz : f.1 x ≠ 0 := by
    simpa [hxr] using hrne
  exact ⟨x, hxnz, rfl⟩

/-- Helper for Proposition 8.1.1: every ambient nonzero point belongs to a positive-value fiber
from the finite range of `f`. -/
lemma helperForProposition_8_1_1_nonzeroImage_subset_iUnion_posFibers {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (f : NonnegSimpleFunction Ω) :
    (((↑) : Ω → Fin n → ℝ) '' {x : Ω | f.1 x ≠ 0}) ⊆
      (⋃ r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)),
        (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) := by
  classical
  intro y hy
  rcases hy with ⟨x, hxnonzero, rfl⟩
  let r : ℝ := f.1 x
  have hrange : r ∈ Set.range f.1 := ⟨x, rfl⟩
  have hrmem : r ∈ f.2.1.2.2.toFinset := (Set.Finite.mem_toFinset (f.2.1.2.2)).2 hrange
  have hrnonneg : 0 ≤ r := by
    simpa [r] using f.2.2 x
  have hrne : r ≠ 0 := by
    simpa [r] using hxnonzero
  have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hrne)
  have hrfilter : r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)) :=
    Finset.mem_filter.mpr ⟨hrmem, hrpos⟩
  have hxfiber : x ∈ f.1 ⁻¹' {r} := by
    simpa [r, Set.mem_preimage, Set.mem_singleton_iff]
  exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hrfilter, ⟨x, hxfiber, rfl⟩⟩⟩

/-- Helper for Proposition 8.1.1: a finite union has zero volume when each indexed piece has
zero volume. -/
lemma helperForProposition_8_1_1_union_volume_zero_of_fibers_zero {n : ℕ}
    (S : Finset ℝ) (F : ℝ → Set (Fin n → ℝ))
    (hvol : ∀ r ∈ S, MeasureTheory.volume (F r) = 0) :
    MeasureTheory.volume (⋃ r ∈ S, F r) = 0 := by
  classical
  have hSubtype : MeasureTheory.volume (⋃ i : {r // r ∈ S}, F i.1) = 0 := by
    exact MeasureTheory.measure_iUnion_null (fun i => hvol i.1 i.2)
  have hEq : (⋃ r ∈ S, F r) = ⋃ i : {r // r ∈ S}, F i.1 := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨r, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨hr, hxFr⟩
      exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, hxFr⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2 ⟨i.2, hxi⟩⟩
  simpa [hEq] using hSubtype

/-- Proposition 8.1.1: for a non-negative simple function `f` on `Ω`, one has
`0 ≤ ∫_Ω f dm ≤ ∞`; moreover `∫_Ω f dm = 0` iff `m({x ∈ Ω | f(x) ≠ 0}) = 0`. -/
theorem lebesgueIntegralNonnegSimple_nonneg_le_top_and_eq_zero_iff {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (f : NonnegSimpleFunction Ω) :
    (0 : ENNReal) ≤ lebesgueIntegralNonnegSimple f ∧
      lebesgueIntegralNonnegSimple f ≤ ⊤ ∧
      (lebesgueIntegralNonnegSimple f = 0 ↔
        MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' {x : Ω | f.1 x ≠ 0}) = 0) := by
  refine ⟨bot_le, le_top, ?_⟩
  constructor
  · intro hintegral_zero
    have hsum_zero :
        (((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)).sum (fun r : ℝ =>
          ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) = 0) := by
      simpa [lebesgueIntegralNonnegSimple] using hintegral_zero
    have hfiber_zero :
        ∀ r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)),
          MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) = 0 :=
      (helperForProposition_8_1_1_integral_eq_zero_iff_forall_posFiber_zero (f := f)).1
        hsum_zero
    have hunion_zero :
        MeasureTheory.volume
            (⋃ r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)),
              (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) = 0 :=
      helperForProposition_8_1_1_union_volume_zero_of_fibers_zero
        ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t))
        (fun r : ℝ => (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})))
        hfiber_zero
    have hsubset :
        (((↑) : Ω → Fin n → ℝ) '' {x : Ω | f.1 x ≠ 0}) ⊆
          (⋃ r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)),
            (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) :=
      helperForProposition_8_1_1_nonzeroImage_subset_iUnion_posFibers (f := f)
    exact MeasureTheory.measure_mono_null hsubset hunion_zero
  · intro hnonzero_zero
    have hfiber_zero :
        ∀ r ∈ ((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)),
          MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) = 0 := by
      intro r hr
      have hsubset :
          (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) ⊆
            (((↑) : Ω → Fin n → ℝ) '' {x : Ω | f.1 x ≠ 0}) :=
        helperForProposition_8_1_1_posFiber_subset_nonzeroImage (f := f) hr
      exact MeasureTheory.measure_mono_null hsubset hnonzero_zero
    have hsum_zero :
        (((f.2.1.2.2.toFinset).filter (fun t : ℝ => 0 < t)).sum (fun r : ℝ =>
          ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) = 0) :=
      (helperForProposition_8_1_1_integral_eq_zero_iff_forall_posFiber_zero (f := f)).2
        hfiber_zero
    simpa [lebesgueIntegralNonnegSimple] using hsum_zero

/-- Helper for Lemma 8.3: each approximation `x ↦ (eapprox f k x).toReal` is a simple function
on `Ω`. -/
lemma helperForLemma_8_3_isSimple_toReal_eapprox {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : MeasurableSet Ω) {f : Ω → ENNReal} (k : ℕ) :
    IsSimpleFunction Ω (fun x : Ω => (MeasureTheory.SimpleFunc.eapprox f k x).toReal) := by
  refine ⟨hΩ, ?_, ?_⟩
  · exact (MeasureTheory.SimpleFunc.eapprox f k).measurable.ennreal_toReal
  ·
    have hfinite :
        (Set.range (MeasureTheory.SimpleFunc.eapprox f k : Ω → ENNReal)).Finite :=
      (MeasureTheory.SimpleFunc.eapprox f k).finite_range
    have hrange :
        Set.range (fun x : Ω => (MeasureTheory.SimpleFunc.eapprox f k x).toReal) =
          (fun y : ENNReal => y.toReal) ''
            Set.range (MeasureTheory.SimpleFunc.eapprox f k : Ω → ENNReal) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨MeasureTheory.SimpleFunc.eapprox f k x, ⟨x, rfl⟩, rfl⟩
      · intro hy
        rcases hy with ⟨z, hz, hyz⟩
        rcases hz with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simpa [hx] using hyz
    simpa [hrange] using (hfinite.image (fun y : ENNReal => y.toReal))

/-- Helper for Lemma 8.3: `toReal ∘ eapprox` is pointwise nonnegative and monotone in the
approximation index. -/
lemma helperForLemma_8_3_nonneg_mono_toReal_eapprox {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ENNReal} (k : ℕ) (x : Ω) :
    0 ≤ (MeasureTheory.SimpleFunc.eapprox f k x).toReal ∧
      (MeasureTheory.SimpleFunc.eapprox f k x).toReal ≤
        (MeasureTheory.SimpleFunc.eapprox f (k + 1) x).toReal := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_mono (MeasureTheory.SimpleFunc.eapprox_lt_top f (k + 1) x).ne
    (MeasureTheory.SimpleFunc.monotone_eapprox f (Nat.le_succ k) x)

/-- Helper for Lemma 8.3: converting `eapprox` to `ℝ` and back with `ofReal` recovers the
original `ENNReal` value. -/
lemma helperForLemma_8_3_ofReal_toReal_eapprox {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ENNReal} (x : Ω) (k : ℕ) :
    ENNReal.ofReal ((MeasureTheory.SimpleFunc.eapprox f k x).toReal) =
      MeasureTheory.SimpleFunc.eapprox f k x := by
  exact ENNReal.ofReal_toReal (MeasureTheory.SimpleFunc.eapprox_lt_top f k x).ne

/-- Helper for Lemma 8.3: `ENNReal.ofReal` applied to `toReal ∘ eapprox` converges pointwise to
`f`. -/
lemma helperForLemma_8_3_tendsto_ofReal_toReal_eapprox {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {f : Ω → ENNReal} (hf : Measurable f) (x : Ω) :
    Filter.Tendsto
      (fun k : ℕ => ENNReal.ofReal ((MeasureTheory.SimpleFunc.eapprox f k x).toReal))
      Filter.atTop (nhds (f x)) := by
  simpa [helperForLemma_8_3_ofReal_toReal_eapprox (f := f) x] using
    (MeasureTheory.SimpleFunc.tendsto_eapprox hf x)

/-- Lemma 8.3: if `Ω ⊆ ℝ^n` is measurable and `f : Ω → [0, +∞]` is measurable, then there
exists a sequence `(f_n)` of nonnegative simple functions `f_n : Ω → ℝ` such that
(i) `0 ≤ f_n ≤ f_{n+1}` pointwise, and
(ii) for every `x ∈ Ω`, `f_n x` converges to `f x` in `[0, +∞]` (via `ENNReal.ofReal`). -/
theorem lemma_8_3 {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {f : Ω → ENNReal} (hf : Measurable f) :
    ∃ fSeq : ℕ → Ω → ℝ,
      (∀ n : ℕ, IsSimpleFunction Ω (fSeq n)) ∧
      (∀ n : ℕ, ∀ x : Ω, 0 ≤ fSeq n x ∧ fSeq n x ≤ fSeq (n + 1) x) ∧
      ∀ x : Ω, Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (fSeq n x)) Filter.atTop (nhds (f x)) := by
  let fSeq : ℕ → Ω → ℝ := fun k x => (MeasureTheory.SimpleFunc.eapprox f k x).toReal
  refine ⟨fSeq, ?_, ?_, ?_⟩
  · intro k
    simpa [fSeq] using helperForLemma_8_3_isSimple_toReal_eapprox hΩ (f := f) k
  · intro k x
    simpa [fSeq] using helperForLemma_8_3_nonneg_mono_toReal_eapprox (f := f) k x
  · intro x
    simpa [fSeq] using helperForLemma_8_3_tendsto_ofReal_toReal_eapprox (f := f) hf x

/-- Helper for Lemma 8.4: if `x` lies in none of the sets `E i`, then the
indicator expansion at `x` vanishes. -/
lemma helperForLemma_8_4_sum_indicator_eq_zero_of_not_mem {n N : ℕ}
    {E : Fin N → Set (Fin n → ℝ)} (c : Fin N → ℝ) {x : Fin n → ℝ}
    (hx : ∀ i : Fin N, x ∉ E i) :
    (Finset.univ : Finset (Fin N)).sum
      (fun i : Fin N => c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp [Set.indicator_of_notMem (hx i)]

/-- Helper for Lemma 8.4: if `x ∈ E i`, pairwise disjointness makes the
indicator expansion collapse to `c i`. -/
lemma helperForLemma_8_4_sum_indicator_eq_coeff_of_mem {n N : ℕ}
    {E : Fin N → Set (Fin n → ℝ)}
    (hE_disjoint : Pairwise (fun i j : Fin N => Disjoint (E i) (E j)))
    (c : Fin N → ℝ) {x : Fin n → ℝ} {i : Fin N} (hxi : x ∈ E i) :
    (Finset.univ : Finset (Fin N)).sum
      (fun j : Fin N => c j * Set.indicator (E j) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = c i := by
  calc
    (Finset.univ : Finset (Fin N)).sum
      (fun j : Fin N => c j * Set.indicator (E j) (fun _ : Fin n → ℝ => (1 : ℝ)) x) =
        c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro j hj hji
            have hij : i ≠ j := by
              intro hijEq
              exact hji hijEq.symm
            have hx_not_mem : x ∉ E j := by
              intro hxj
              exact (Set.disjoint_left.1 (hE_disjoint (i := i) (j := j) hij)) hxi hxj
            simp [Set.indicator_of_notMem hx_not_mem]
          · intro hi_not_mem
            exact False.elim (hi_not_mem (Finset.mem_univ i))
    _ = c i := by
          simp [Set.indicator_of_mem hxi]

/-- Helper for Lemma 8.4: for positive `r`, membership in the `r`-fiber is
equivalent to lying in some `E i` with coefficient `c i = r`. -/
lemma helperForLemma_8_4_value_pos_fiber_iff_exists_index {n N : ℕ}
    {Ω : Set (Fin n → ℝ)} {E : Fin N → Set (Fin n → ℝ)}
    (hE_disjoint : Pairwise (fun i j : Fin N => Disjoint (E i) (E j)))
    (c : Fin N → ℝ) (f : NonnegSimpleFunction Ω)
    (hf_repr : ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
      f.1 ⟨x, hx⟩ =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x))
    {r : ℝ} (hr_pos : 0 < r) {x : Fin n → ℝ} (hxΩ : x ∈ Ω) :
    x ∈ (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) ↔
      ∃ i : Fin N, x ∈ E i ∧ c i = r := by
  constructor
  · intro hxFiber
    have hfx : f.1 ⟨x, hxΩ⟩ = r := by
      rcases hxFiber with ⟨y, hy, hyx⟩
      have hyEq : y = ⟨x, hxΩ⟩ := by
        apply Subtype.ext
        simpa using hyx
      have hyVal : f.1 y = r := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy
      simpa [hyEq] using hyVal
    have hsumEq :
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = r := by
      calc
        (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x)
            = f.1 ⟨x, hxΩ⟩ := by
              symm
              exact hf_repr x hxΩ
        _ = r := hfx
    by_cases hex : ∃ i : Fin N, x ∈ E i
    · refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
      have hcollapse :
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) =
            c (Classical.choose hex) :=
        helperForLemma_8_4_sum_indicator_eq_coeff_of_mem (hE_disjoint := hE_disjoint) c
          (hxi := Classical.choose_spec hex)
      calc
        c (Classical.choose hex) =
            (Finset.univ : Finset (Fin N)).sum
              (fun i : Fin N =>
                c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
                  simpa using hcollapse.symm
        _ = r := hsumEq
    · have hnone : ∀ i : Fin N, x ∉ E i := by
        intro i hxi
        exact hex ⟨i, hxi⟩
      have hsumZero :
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = 0 :=
        helperForLemma_8_4_sum_indicator_eq_zero_of_not_mem c hnone
      have hr_zero : r = 0 := by
        linarith [hsumEq, hsumZero]
      have hr_not_pos : ¬ 0 < r := by
        simpa [hr_zero]
      exact False.elim (hr_not_pos hr_pos)
  · rintro ⟨i, hxi, hci⟩
    have hsumEq :
        (Finset.univ : Finset (Fin N)).sum
          (fun j : Fin N =>
            c j * Set.indicator (E j) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = c i :=
      helperForLemma_8_4_sum_indicator_eq_coeff_of_mem (hE_disjoint := hE_disjoint) c
        (hxi := hxi)
    have hfx : f.1 ⟨x, hxΩ⟩ = r := by
      calc
        f.1 ⟨x, hxΩ⟩
            = (Finset.univ : Finset (Fin N)).sum
                (fun j : Fin N =>
                  c j * Set.indicator (E j) (fun _ : Fin n → ℝ => (1 : ℝ)) x) :=
              hf_repr x hxΩ
        _ = c i := hsumEq
        _ = r := hci
    refine ⟨⟨x, hxΩ⟩, ?_, rfl⟩
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hfx

/-- Helper for Lemma 8.4: each positive fiber has measure equal to the sum of
the measures of those `E i` whose coefficients equal that value. -/
lemma helperForLemma_8_4_measure_pos_fiber_as_filtered_sum {n N : ℕ}
    {Ω : Set (Fin n → ℝ)} {E : Fin N → Set (Fin n → ℝ)}
    (hE_meas : ∀ i : Fin N, MeasurableSet (E i))
    (hE_subset : ∀ i : Fin N, E i ⊆ Ω)
    (hE_disjoint : Pairwise (fun i j : Fin N => Disjoint (E i) (E j)))
    (c : Fin N → ℝ) (f : NonnegSimpleFunction Ω)
    (hf_repr : ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
      f.1 ⟨x, hx⟩ =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x))
    {r : ℝ} (hr_pos : 0 < r) :
    MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) =
      (Finset.univ.filter (fun i : Fin N => c i = r)).sum
        (fun i : Fin N => MeasureTheory.volume (E i)) := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => c i = r)
  have hset :
      (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) = ⋃ i ∈ s, E i := by
    ext x
    constructor
    · intro hxFiber
      rcases hxFiber with ⟨y, hy, hyx⟩
      have hxΩ : x ∈ Ω := by
        simpa [hyx] using y.property
      have hxFiber' : x ∈ (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) := by
        exact ⟨y, hy, hyx⟩
      rcases (helperForLemma_8_4_value_pos_fiber_iff_exists_index
          (hE_disjoint := hE_disjoint) (c := c) (f := f) (hf_repr := hf_repr)
          (hr_pos := hr_pos) (hxΩ := hxΩ)).1 hxFiber' with ⟨i, hxi, hci⟩
      have hi_s : i ∈ s := by
        simp [s, hci]
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi_s, hxi⟩⟩
    · intro hxUnion
      rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxUnion'⟩
      rcases Set.mem_iUnion.1 hxUnion' with ⟨hi_s, hxi⟩
      have hci : c i = r := (Finset.mem_filter.1 hi_s).2
      have hxΩ : x ∈ Ω := hE_subset i hxi
      exact (helperForLemma_8_4_value_pos_fiber_iff_exists_index
          (hE_disjoint := hE_disjoint) (c := c) (f := f) (hf_repr := hf_repr)
          (hr_pos := hr_pos) (hxΩ := hxΩ)).2 ⟨i, hxi, hci⟩
  have hpair : (↑s : Set (Fin N)).PairwiseDisjoint E := by
    intro i hi j hj hij
    exact hE_disjoint (i := i) (j := j) hij
  calc
    MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))
        = MeasureTheory.volume (⋃ i ∈ s, E i) := by
            simpa [hset]
    _ = ∑ i ∈ s, MeasureTheory.volume (E i) :=
      MeasureTheory.measure_biUnion_finset hpair (fun i hi => hE_meas i)
    _ = (Finset.univ.filter (fun i : Fin N => c i = r)).sum
          (fun i : Fin N => MeasureTheory.volume (E i)) := by
            simp [s]

/-- Helper for Lemma 8.4: replacing positive values in the range of `f` by
positive values in the coefficient-image changes only zero terms. -/
lemma helperForLemma_8_4_range_to_coeff_image_on_positive_part {n N : ℕ}
    {Ω : Set (Fin n → ℝ)} {E : Fin N → Set (Fin n → ℝ)}
    (hE_disjoint : Pairwise (fun i j : Fin N => Disjoint (E i) (E j)))
    (c : Fin N → ℝ) (f : NonnegSimpleFunction Ω)
    (hf_repr : ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
      f.1 ⟨x, hx⟩ =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x)) :
    (f.2.1.2.2.toFinset.filter (fun r : ℝ => 0 < r)).sum
      (fun r : ℝ =>
        ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})))
      =
    ((Finset.univ.image c).filter (fun r : ℝ => 0 < r)).sum
      (fun r : ℝ =>
        ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) := by
  classical
  let A : Finset ℝ := f.2.1.2.2.toFinset.filter (fun r : ℝ => 0 < r)
  let B : Finset ℝ := (Finset.univ.image c).filter (fun r : ℝ => 0 < r)
  let term : ℝ → ENNReal := fun r : ℝ =>
    ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))
  have hsubset : A ⊆ B := by
    intro r hrA
    have hrA_mem : r ∈ f.2.1.2.2.toFinset := (Finset.mem_filter.1 hrA).1
    have hr_pos : 0 < r := (Finset.mem_filter.1 hrA).2
    have hrange : r ∈ Set.range f.1 := (Set.Finite.mem_toFinset f.2.1.2.2).1 hrA_mem
    rcases hrange with ⟨y, hy⟩
    have hxFiber : (y : Fin n → ℝ) ∈ (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r})) := by
      refine ⟨y, ?_, rfl⟩
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy
    rcases (helperForLemma_8_4_value_pos_fiber_iff_exists_index
        (hE_disjoint := hE_disjoint) (c := c) (f := f) (hf_repr := hf_repr)
        (hr_pos := hr_pos) (hxΩ := y.property)).1 hxFiber with ⟨i, _, hci⟩
    have hrB_mem_image : r ∈ Finset.univ.image c := by
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hci⟩
    exact Finset.mem_filter.2 ⟨hrB_mem_image, hr_pos⟩
  have hzero : ∀ r ∈ B, r ∉ A → term r = 0 := by
    intro r hrB hrA_not
    have hr_pos : 0 < r := (Finset.mem_filter.1 hrB).2
    have hr_not_toFinset : r ∉ f.2.1.2.2.toFinset := by
      intro hr_toFinset
      exact hrA_not (Finset.mem_filter.2 ⟨hr_toFinset, hr_pos⟩)
    have hr_not_range : r ∉ Set.range f.1 := by
      intro hrange
      exact hr_not_toFinset ((Set.Finite.mem_toFinset f.2.1.2.2).2 hrange)
    have hpreEmpty : f.1 ⁻¹' {r} = ∅ := by
      ext y
      constructor
      · intro hy
        have hrange : r ∈ Set.range f.1 := by
          refine ⟨y, ?_⟩
          simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy
        exact False.elim (hr_not_range hrange)
      · intro hy
        simp at hy
    simp [term, hpreEmpty]
  have hsum := Finset.sum_subset hsubset hzero
  simpa [A, B, term] using hsum

/-- Helper for Lemma 8.4: regrouping the coefficient-filtered double sum gives
the direct index-sum formula. -/
lemma helperForLemma_8_4_reindex_double_sum_to_index_sum {n N : ℕ}
    (c : Fin N → ℝ) (hc_nonneg : ∀ i : Fin N, 0 ≤ c i)
    (E : Fin N → Set (Fin n → ℝ)) :
    ((Finset.univ.image c).filter (fun r : ℝ => 0 < r)).sum
      (fun r : ℝ =>
        ENNReal.ofReal r *
          (Finset.univ.filter (fun i : Fin N => c i = r)).sum
            (fun i : Fin N => MeasureTheory.volume (E i)))
      =
    (Finset.univ : Finset (Fin N)).sum
      (fun i : Fin N => ENNReal.ofReal (c i) * MeasureTheory.volume (E i)) := by
  classical
  let S : Finset ℝ := (Finset.univ.image c).filter (fun r : ℝ => 0 < r)
  let T : ℝ → Finset (Fin N) := fun r : ℝ =>
    Finset.univ.filter (fun i : Fin N => c i = r)
  let F : Fin N → ENNReal := fun i : Fin N =>
    ENNReal.ofReal (c i) * MeasureTheory.volume (E i)
  have hrewrite :
      S.sum (fun r : ℝ => ENNReal.ofReal r * (T r).sum (fun i : Fin N => MeasureTheory.volume (E i))) =
        S.sum (fun r : ℝ => (T r).sum (fun i : Fin N => F i)) := by
    refine Finset.sum_congr rfl ?_
    intro r hrS
    calc
      ENNReal.ofReal r * (T r).sum (fun i : Fin N => MeasureTheory.volume (E i)) =
          (T r).sum (fun i : Fin N => ENNReal.ofReal r * MeasureTheory.volume (E i)) := by
            simpa using
              (Finset.mul_sum (s := T r) (f := fun i : Fin N => MeasureTheory.volume (E i))
                (a := ENNReal.ofReal r))
      _ = (T r).sum (fun i : Fin N => F i) := by
            refine Finset.sum_congr rfl ?_
            intro i hiT
            have hci : c i = r := (Finset.mem_filter.1 hiT).2
            simp [F, hci]
  have hpair : (↑S : Set ℝ).PairwiseDisjoint T := by
    intro r hrS s hsS hrs
    refine Finset.disjoint_left.2 ?_
    intro i hir his
    have hci_r : c i = r := (Finset.mem_filter.1 hir).2
    have hci_s : c i = s := (Finset.mem_filter.1 his).2
    exact hrs (hci_r.symm.trans hci_s)
  have hbiUnion :
      S.sum (fun r : ℝ => (T r).sum (fun i : Fin N => F i)) = (S.biUnion T).sum F := by
    have hsum := Finset.sum_biUnion (f := F) (s := S) (t := T) hpair
    simpa using hsum.symm
  have hbiUnionEq :
      S.biUnion T = (Finset.univ.filter (fun i : Fin N => 0 < c i)) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_biUnion.1 hi with ⟨r, hrS, hiT⟩
      have hr_pos : 0 < r := (Finset.mem_filter.1 hrS).2
      have hci : c i = r := (Finset.mem_filter.1 hiT).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i, by simpa [hci] using hr_pos⟩
    · intro hi
      have hi_pos : 0 < c i := (Finset.mem_filter.1 hi).2
      have hci_in_S : c i ∈ S := by
        refine Finset.mem_filter.2 ?_
        refine ⟨?_, hi_pos⟩
        exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
      have hi_in_T : i ∈ T (c i) := by
        exact Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩
      exact Finset.mem_biUnion.2 ⟨c i, hci_in_S, hi_in_T⟩
  have hremoveFilter :
      (Finset.univ.filter (fun i : Fin N => 0 < c i)).sum F =
        (Finset.univ : Finset (Fin N)).sum F := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      exact Finset.mem_univ i
    · intro i hi_univ hi_not_mem
      have hi_not_pos : ¬ 0 < c i := by
        intro hi_pos
        exact hi_not_mem (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi_pos⟩)
      have hci_zero : c i = 0 := le_antisymm (le_of_not_gt hi_not_pos) (hc_nonneg i)
      simp [hci_zero]
  calc
    ((Finset.univ.image c).filter (fun r : ℝ => 0 < r)).sum
      (fun r : ℝ =>
        ENNReal.ofReal r *
          (Finset.univ.filter (fun i : Fin N => c i = r)).sum
            (fun i : Fin N => MeasureTheory.volume (E i)))
      =
      S.sum (fun r : ℝ => ENNReal.ofReal r * (T r).sum (fun i : Fin N => MeasureTheory.volume (E i))) := by
            simp [S, T]
    _ = S.sum (fun r : ℝ => (T r).sum (fun i : Fin N => F i)) := hrewrite
    _ = (S.biUnion T).sum F := hbiUnion
    _ = (Finset.univ.filter (fun i : Fin N => 0 < c i)).sum F := by
          simpa [hbiUnionEq]
    _ = (Finset.univ : Finset (Fin N)).sum F := hremoveFilter
    _ = (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (c i) * MeasureTheory.volume (E i)) := by
            simp [F]

/-- Lemma 8.4: if a nonnegative simple function on `Ω` is represented by a finite
pairwise-disjoint indicator expansion `∑ c_i χ_{E_i}`, then its integral is
`∑ c_i m(E_i)`. -/
theorem lemma_8_4 {n N : ℕ} {Ω : Set (Fin n → ℝ)}
    (E : Fin N → Set (Fin n → ℝ))
    (hE_meas : ∀ i : Fin N, MeasurableSet (E i))
    (hE_subset : ∀ i : Fin N, E i ⊆ Ω)
    (hE_disjoint : Pairwise (fun i j : Fin N => Disjoint (E i) (E j)))
    (c : Fin N → ℝ) (hc_nonneg : ∀ i : Fin N, 0 ≤ c i)
    (f : NonnegSimpleFunction Ω)
    (hf_repr : ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
      f.1 ⟨x, hx⟩ =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            c i * Set.indicator (E i) (fun _ : Fin n → ℝ => (1 : ℝ)) x)) :
    lebesgueIntegralNonnegSimple f =
      (Finset.univ : Finset (Fin N)).sum
        (fun i : Fin N => ENNReal.ofReal (c i) * MeasureTheory.volume (E i)) := by
  classical
  calc
    lebesgueIntegralNonnegSimple f
        = (f.2.1.2.2.toFinset.filter (fun r : ℝ => 0 < r)).sum
            (fun r : ℝ =>
              ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) := by
              simp [lebesgueIntegralNonnegSimple]
    _ = ((Finset.univ.image c).filter (fun r : ℝ => 0 < r)).sum
          (fun r : ℝ =>
            ENNReal.ofReal r * MeasureTheory.volume (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {r}))) :=
      helperForLemma_8_4_range_to_coeff_image_on_positive_part
        (hE_disjoint := hE_disjoint) (c := c) (f := f) (hf_repr := hf_repr)
    _ = ((Finset.univ.image c).filter (fun r : ℝ => 0 < r)).sum
          (fun r : ℝ =>
            ENNReal.ofReal r *
              (Finset.univ.filter (fun i : Fin N => c i = r)).sum
                (fun i : Fin N => MeasureTheory.volume (E i))) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hr_pos : 0 < r := (Finset.mem_filter.1 hr).2
          rw [helperForLemma_8_4_measure_pos_fiber_as_filtered_sum
            (hE_meas := hE_meas) (hE_subset := hE_subset) (hE_disjoint := hE_disjoint)
            (c := c) (f := f) (hf_repr := hf_repr) (r := r) (hr_pos := hr_pos)]
    _ = (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (c i) * MeasureTheory.volume (E i)) :=
      helperForLemma_8_4_reindex_double_sum_to_index_sum (c := c) (hc_nonneg := hc_nonneg) (E := E)


end Section01
end Chap08
