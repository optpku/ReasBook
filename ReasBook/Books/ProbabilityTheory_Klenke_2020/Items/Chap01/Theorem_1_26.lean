/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Ω : Type u}

-- Proof sketch: `traceOn` is the pullback family along `Subtype.val`, while the measurable sets of
-- `m.comap Subtype.val` are definitionally the pullbacks of measurable sets of `m`.
/-- Helper for Theorem 1.26: restricting a σ-algebra to a subset `A` gives the σ-algebra on the
subtype `A` induced by `MeasurableSpace.comap`. -/
theorem traceOn_measurableSet_eq_comap (m : MeasurableSpace Ω) (A : Set Ω) :
    traceOn {s | MeasurableSet[m] s} A =
      {s | MeasurableSet[m.comap (Subtype.val : A → Ω)] s} := by
  ext s
  constructor
  · intro hs
    rcases mem_traceOn_iff.mp hs with ⟨t, ht, rfl⟩
    change MeasurableSet[m.comap (Subtype.val : A → Ω)] (Subtype.val ⁻¹' t)
    exact ⟨t, ht, rfl⟩
  · intro hs
    change MeasurableSet[m.comap (Subtype.val : A → Ω)] s at hs
    rcases hs with ⟨t, ht, hts⟩
    exact mem_traceOn_iff.mpr ⟨t, ht, hts.symm⟩

-- Proof sketch: pull back `∅`, complements, and binary unions along the subtype inclusion.
/-- Helper for Theorem 1.26: restricting an algebra of sets to a subset again yields an algebra of
sets, now on the subtype `A`. -/
theorem traceOn_isSetAlgebra (A : Set Ω) (C : Set (Set Ω)) (hC : IsSetAlgebra C) :
    IsSetAlgebra (traceOn C A) := by
  refine
    { empty_mem := ?_
      compl_mem := ?_
      union_mem := ?_ }
  · exact mem_traceOn_iff.mpr ⟨∅, hC.empty_mem, by ext x; simp⟩
  · intro s hs
    rcases mem_traceOn_iff.mp hs with ⟨t, ht, rfl⟩
    exact mem_traceOn_iff.mpr ⟨tᶜ, hC.compl_mem ht, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u ∪ v, hC.union_mem hu hv, by ext x; simp⟩

-- Proof sketch: pull back `∅`, differences, and unions along the subtype inclusion.
/-- Helper for Theorem 1.26: restricting a ring of sets to a subset again yields a ring of sets,
now on the subtype `A`. -/
theorem traceOn_isSetRing (A : Set Ω) (C : Set (Set Ω)) (hC : MeasureTheory.IsSetRing C) :
    MeasureTheory.IsSetRing (traceOn C A) := by
  refine
    { empty_mem := ?_
      diff_mem := ?_
      union_mem := ?_ }
  · exact mem_traceOn_iff.mpr ⟨∅, hC.empty_mem, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u ∪ v, hC.union_mem hu hv, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u \ v, hC.diff_mem hu hv, by ext x; simp⟩

-- Proof sketch: combine preservation of the ring-of-sets axioms under pullback with preservation
-- of countable unions.
/-- Helper for Theorem 1.26: restricting a sigma-ring of sets to a subset again yields a
sigma-ring of sets, now on the subtype `A`. -/
theorem traceOn_isSetSigmaRing (A : Set Ω) (C : Set (Set Ω)) (hC : IsSetSigmaRing C) :
    IsSetSigmaRing (traceOn C A) := by
  refine
    { traceOn_isSetRing A C hC.toIsSetRing with
      iUnion_mem := ?_ }
  intro s hs
  choose t htC hts using fun n ↦ mem_traceOn_iff.mp (hs n)
  exact mem_traceOn_iff.mpr ⟨⋃ n, t n, hC.iUnion_mem t htC, by
    ext x
    simp [hts]⟩

-- Proof sketch: semiring axioms are stable under pullback by any map, in particular by the
-- subtype inclusion.
/-- Helper for Theorem 1.26: pulling back along `Subtype.val` commutes with binary intersections. -/
lemma traceOn_inter_preimage (A : Set Ω) (u v : Set Ω) :
    (Subtype.val ⁻¹' u : Set A) ∩ Subtype.val ⁻¹' v = Subtype.val ⁻¹' (u ∩ v) := by
  -- Compare membership pointwise on the subtype.
  ext x
  simp

/-- Helper for Theorem 1.26: a finite semiring decomposition of `s \ t` pulls back to a finite
semiring decomposition in the trace family on `A`. -/
lemma traceOn_diffEq_sUnionFinset (A : Set Ω) {C : Set (Set Ω)}
    (hC : MeasureTheory.IsSetSemiring C) {s t : Set Ω} (hs : s ∈ C) (ht : t ∈ C) :
    ∃ J : Finset (Set A), ↑J ⊆ traceOn C A ∧ PairwiseDisjoint (J : Set (Set A)) id ∧
      Subtype.val ⁻¹' (s \ t) = ⋃₀ (↑J : Set (Set A)) := by
  classical
  -- Pull back the ambient finite partition supplied by the semiring axioms.
  obtain ⟨I, hIC, hI_disjoint, hdiff⟩ := hC.diff_eq_sUnion' s hs t ht
  let J : Finset (Set A) := I.image fun u => (Subtype.val ⁻¹' u : Set A)
  refine ⟨J, ?_, ?_, ?_⟩
  · -- Each pulled-back piece is itself a traced member.
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨v, hIC hv, rfl⟩
  · -- Pairwise disjointness is preserved under preimage.
    intro u hu v hv huv
    rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
    refine Disjoint.preimage _ (hI_disjoint hu' hv' ?_)
    intro huv'
    apply huv
    simp [huv']
  · -- The pullback of the ambient union is the union of the pulled-back pieces.
    calc
      Subtype.val ⁻¹' (s \ t) = Subtype.val ⁻¹' ⋃₀ (↑I : Set (Set Ω)) := by
        simp [hdiff]
      _ = ⋃₀ ((fun u : Set Ω ↦ (Subtype.val ⁻¹' u : Set A)) '' (↑I : Set (Set Ω))) := by
        exact Set.preimage_val_sUnion (A := A) (S := (↑I : Set (Set Ω)))
      _ = ⋃₀ (↑J : Set (Set A)) := by
        congr 1
        ext u
        simp [J]

/-- Theorem 1.26 (5): Restricting a semiring of sets to a subset again yields a semiring of sets,
now on the subtype `A`. -/
theorem traceOn_isSetSemiring (A : Set Ω) (C : Set (Set Ω))
    (hC : MeasureTheory.IsSetSemiring C) :
    MeasureTheory.IsSetSemiring (traceOn C A) := by
  refine
    { empty_mem := ?_
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- The empty set is the pullback of the ambient empty set.
    have hEmpty : (∅ : Set A) = Subtype.val ⁻¹' (∅ : Set Ω) := by
      ext x
      simp
    exact mem_traceOn_iff.mpr ⟨∅, hC.empty_mem, hEmpty⟩
  · intro s hs t ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    -- Intersections stay in the trace after one normalization step.
    rw [traceOn_inter_preimage]
    exact mem_traceOn_iff.mpr ⟨u ∩ v, hC.inter_mem u hu v hv, rfl⟩
  · intro s hs t ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    -- Reuse the pulled-back finite decomposition for the difference axiom.
    simpa using traceOn_diffEq_sUnionFinset A hC hu hv

-- Proof sketch: this is the negative existence statement from the textbook: there is some ambient
-- space, some nonempty subset, and some Dynkin system whose restriction is not again a Dynkin
-- system on the subset.
/-- Helper for Theorem 1.26: pairwise disjointness is preserved when a family is pulled back along
an equivalence. -/
lemma dynkinSystemPullback_pairwise {α β : Type*} (e : α ≃ β) {f : ℕ → Set β}
    (hf : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    Pairwise fun i j ↦ Disjoint (e ⁻¹' f i) (e ⁻¹' f j) := by
  intro i j hij
  exact Disjoint.preimage _ (hf hij)

/-- Helper for Theorem 1.26: the empty set belongs to the pullback of a Dynkin system along an
equivalence. -/
lemma dynkinSystemPullback_has_empty {α β : Type*} (e : α ≃ β)
    (d : MeasurableSpace.DynkinSystem α) :
    d.Has (e ⁻¹' (∅ : Set β)) := by
  simpa using d.has_empty

/-- Helper for Theorem 1.26: complements remain in the pullback of a Dynkin system along an
equivalence. -/
lemma dynkinSystemPullback_has_compl {α β : Type*} (e : α ≃ β)
    (d : MeasurableSpace.DynkinSystem α) {s : Set β} (hs : d.Has (e ⁻¹' s)) :
    d.Has (e ⁻¹' sᶜ) := by
  simpa [Set.preimage_compl] using d.has_compl hs

/-- Helper for Theorem 1.26: countable disjoint unions remain in the pullback of a Dynkin system
along an equivalence. -/
lemma dynkinSystemPullback_has_iUnion_nat {α β : Type*} (e : α ≃ β)
    (d : MeasurableSpace.DynkinSystem α) {f : ℕ → Set β}
    (hf : Pairwise fun i j ↦ Disjoint (f i) (f j)) (hs : ∀ n, d.Has (e ⁻¹' f n)) :
    d.Has (e ⁻¹' ⋃ n, f n) := by
  -- Rewrite the pullback of the union as the union of the pullbacks.
  simpa [Set.preimage_iUnion] using d.has_iUnion_nat (dynkinSystemPullback_pairwise e hf) hs

/-- Helper for Theorem 1.26: pull back a Dynkin system along an equivalence of ambient types. -/
def dynkinSystemPullback {α β : Type*} (e : α ≃ β)
    (d : MeasurableSpace.DynkinSystem α) : MeasurableSpace.DynkinSystem β :=
  { Has := fun s ↦ d.Has (e ⁻¹' s)
    has_empty := dynkinSystemPullback_has_empty e d
    has_compl := fun hs ↦ dynkinSystemPullback_has_compl e d hs
    has_iUnion_nat := fun hf hs ↦ dynkinSystemPullback_has_iUnion_nat e d hf hs }

/-- Helper for Theorem 1.26: the pullback Dynkin system tests membership by taking preimages along
the chosen equivalence. -/
@[simp] lemma dynkinSystemPullback_has_iff {α β : Type*} (e : α ≃ β)
    (d : MeasurableSpace.DynkinSystem α) {s : Set β} :
    (dynkinSystemPullback e d).Has s ↔ d.Has (e ⁻¹' s) :=
  Iff.rfl

/-- Helper for Theorem 1.26: among the six sets of `fourPointLambdaFamily`, any set containing
both `0` and `2` must also contain `1`. -/
lemma fourPointLambdaFamily_contains_one_of_zero_and_two {t : Set (Fin 4)}
    (ht : t ∈ fourPointLambdaFamily) (h0 : (0 : Fin 4) ∈ t) (h2 : (2 : Fin 4) ∈ t) :
    (1 : Fin 4) ∈ t := by
  -- Exhaust the explicit six ambient sets.
  simp only [fourPointLambdaFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h0 h2 ⊢

/-- Helper for Theorem 1.26: in contrast, restriction of a Dynkin system need not be a Dynkin
system on the subset, in general. -/
theorem exists_nonempty_subset_with_non_dynkin_trace :
    ∃ Ω' : Type u, ∃ A : Set Ω', A.Nonempty ∧ ∃ d : MeasurableSpace.DynkinSystem Ω',
      ¬ ∃ dA : MeasurableSpace.DynkinSystem A, dA.Has = traceOn d.Has A := by
  let e : Fin 4 ≃ ULift.{u} (Fin 4) := Equiv.ulift.symm
  let A0 : Set (Fin 4) := ({0, 1, 2} : Set (Fin 4))
  let A : Set (ULift.{u} (Fin 4)) := e '' A0
  let d0 : MeasurableSpace.DynkinSystem (Fin 4) :=
    MeasurableSpace.DynkinSystem.generate fourPointLambdaFamily
  let d : MeasurableSpace.DynkinSystem (ULift.{u} (Fin 4)) := dynkinSystemPullback e d0
  refine ⟨ULift.{u} (Fin 4), A, ?_, d, ?_⟩
  · -- The lifted point `0` witnesses that the traced subset is nonempty.
    have h0A0 : (0 : Fin 4) ∈ A0 := by
      simp [A0]
    have h0A : e 0 ∈ A := by
      refine ⟨0, h0A0, rfl⟩
    exact ⟨e 0, h0A⟩
  · intro hdA
    rcases hdA with ⟨dA, hdA⟩
    let t0 : Set (ULift.{u} (Fin 4)) := e '' ({0, 3} : Set (Fin 4))
    let t2 : Set (ULift.{u} (Fin 4)) := e '' ({2, 3} : Set (Fin 4))
    let s0 : Set A := Subtype.val ⁻¹' t0
    let s2 : Set A := Subtype.val ⁻¹' t2
    have hd0 :
        {s : Set (Fin 4) | d0.Has s} = fourPointLambdaFamily := by
      simpa [d0] using fourPointLambdaFamily_generatedDynkin_eq
    have ht0d0 : d0.Has ({0, 3} : Set (Fin 4)) := by
      -- Translate the finite generator membership through the explicit six-set family.
      have ht0d0' : ({0, 3} : Set (Fin 4)) ∈ {s : Set (Fin 4) | d0.Has s} := by
        rw [hd0]
        simp [fourPointLambdaFamily]
      exact ht0d0'
    have ht2d0 : d0.Has ({2, 3} : Set (Fin 4)) := by
      -- The second witness comes from the same explicit family.
      have ht2d0' : ({2, 3} : Set (Fin 4)) ∈ {s : Set (Fin 4) | d0.Has s} := by
        rw [hd0]
        simp [fourPointLambdaFamily]
      exact ht2d0'
    have ht0 : d.Has t0 := by
      -- Pull the ambient witness set to the lifted universe.
      simpa [d, t0] using ht0d0
    have ht2 : d.Has t2 := by
      -- Pull the second ambient witness set to the lifted universe.
      simpa [d, t2] using ht2d0
    have hs0Trace : s0 ∈ traceOn d.Has A := by
      exact mem_traceOn_iff.mpr ⟨t0, ht0, rfl⟩
    have hs2Trace : s2 ∈ traceOn d.Has A := by
      exact mem_traceOn_iff.mpr ⟨t2, ht2, rfl⟩
    have hsDisjoint : Disjoint s0 s2 := by
      -- Inside `A = {0,1,2}`, the lifted traces are just the singletons `{0}` and `{2}`.
      rw [Set.disjoint_left]
      intro x hx0 hx2
      rcases x.property with ⟨a, ha, hax⟩
      have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
        simpa [A0] using ha
      have hx0' : e a ∈ t0 := by
        simpa [s0, hax] using hx0
      have hx2' : e a ∈ t2 := by
        simpa [s2, hax] using hx2
      have hx0'' : a = 0 ∨ a = 3 := by
        simpa [t0] using hx0'
      have hx2'' : a = 2 ∨ a = 3 := by
        simpa [t2] using hx2'
      rcases ha' with rfl | rfl | rfl <;> simp at hx0'' hx2''
    have hs0Dynkin : dA.Has s0 := by
      rw [hdA]
      exact hs0Trace
    have hs2Dynkin : dA.Has s2 := by
      rw [hdA]
      exact hs2Trace
    have hsUnionDynkin : dA.Has (s0 ∪ s2) := by
      -- Any Dynkin system on the subtype must contain the union of disjoint members.
      exact dA.has_union hs0Dynkin hs2Dynkin hsDisjoint
    have hsUnionTrace : (s0 ∪ s2) ∈ traceOn d.Has A := by
      rw [← hdA]
      exact hsUnionDynkin
    rcases mem_traceOn_iff.mp hsUnionTrace with ⟨u, hu, hu_eq⟩
    have hu0 : e ⁻¹' u ∈ fourPointLambdaFamily := by
      -- Convert the lifted ambient member back to the explicit six-set family on `Fin 4`.
      have hu' : d0.Has (e ⁻¹' u) := by
        simpa [d] using hu
      rw [← hd0]
      exact hu'
    have h0A0 : (0 : Fin 4) ∈ A0 := by
      simp [A0]
    have h1A0 : (1 : Fin 4) ∈ A0 := by
      simp [A0]
    have h2A0 : (2 : Fin 4) ∈ A0 := by
      simp [A0]
    let x0 : A := ⟨e 0, ⟨0, h0A0, rfl⟩⟩
    let x1 : A := ⟨e 1, ⟨1, h1A0, rfl⟩⟩
    let x2 : A := ⟨e 2, ⟨2, h2A0, rfl⟩⟩
    have hx0Union : x0 ∈ s0 ∪ s2 := by
      simp [s0, s2, t0, t2, x0]
    have hx2Union : x2 ∈ s0 ∪ s2 := by
      simp [s0, s2, t0, t2, x2]
    have hx1Union : x1 ∉ s0 ∪ s2 := by
      simp [s0, s2, t0, t2, x1]
    have hx0u : x0 ∈ Subtype.val ⁻¹' u := by
      rw [← hu_eq]
      exact hx0Union
    have hx2u : x2 ∈ Subtype.val ⁻¹' u := by
      rw [← hu_eq]
      exact hx2Union
    have hx1u : x1 ∉ Subtype.val ⁻¹' u := by
      rw [← hu_eq]
      exact hx1Union
    have huContains0 : (0 : Fin 4) ∈ e ⁻¹' u := by
      -- Read membership of `x0` back in the original four-point space.
      simpa [x0] using hx0u
    have huContains2 : (2 : Fin 4) ∈ e ⁻¹' u := by
      -- The same translation works for the lifted point `2`.
      simpa [x2] using hx2u
    have huNotContains1 : (1 : Fin 4) ∉ e ⁻¹' u := by
      -- The trace union omits the lifted point `1`.
      simpa [x1] using hx1u
    have huContains1 : (1 : Fin 4) ∈ e ⁻¹' u := by
      -- The explicit six-set family has no member whose trace on `{0,1,2}` is `{0,2}`.
      exact fourPointLambdaFamily_contains_one_of_zero_and_two hu0 huContains0 huContains2
    exact huNotContains1 huContains1
