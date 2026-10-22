/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Exercise_14_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

universe u v

section

variable {I : Type u} {Ω : I → Type v}
variable [∀ i, MeasurableSpace (Ω i)] [∀ i, StandardBorelSpace (Ω i)]

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: every coordinate space is nonempty because its singleton marginal is
a probability measure. -/
lemma coordinateNonempty
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (i : I) : Nonempty (Ω i) := by
  classical
  by_contra hi
  haveI : IsEmpty (Ω i) := not_nonempty_iff.mp hi
  let _ : IsEmpty ((j : ({i} : Finset I)) → Ω ↑j) := by
    refine ⟨fun x ↦ ?_⟩
    exact isEmptyElim (x ⟨i, by simp⟩)
  have hzero : P ({i} : Finset I) = 0 := by
    simpa using (Measure.eq_zero_of_isEmpty (μ := P ({i} : Finset I)))
  have huniv : P ({i} : Finset I) Set.univ = 1 := by
    simp
  rw [hzero] at huniv
  simp at huniv

/-- Helper for Theorem 14.36: extend a configuration on a subsystem by default coordinates outside
that subsystem. -/
noncomputable def extendCoordinates
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)] :
    ((j : J) → Ω j) → (i : I) → Ω i :=
  fun x i ↦ if hi : J i then x ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty (Ω i))

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: restricting an extended configuration recovers the original
subsystem configuration. -/
lemma restrict_extendCoordinates
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)] (x : (j : J) → Ω j) :
    J.restrict (extendCoordinates (Ω := Ω) J x) = x := by
  -- Proof comment: on coordinates inside `J`, the extension uses the original subsystem values.
  funext j
  cases j with
  | mk i hi =>
      have hEq :
          extendCoordinates (Ω := Ω) J x i = x ⟨i, hi⟩ := by
        change
          dite (J i) (fun h => x ⟨i, h⟩)
              (fun _ => Classical.choice (inferInstance : Nonempty (Ω i))) = x ⟨i, hi⟩
        simpa using
          (dif_pos hi :
            dite (J i) (fun h => x ⟨i, h⟩)
              (fun _ => Classical.choice (inferInstance : Nonempty (Ω i))) = x ⟨i, hi⟩)
      simpa using hEq

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: the extension map is measurable because each coordinate is either a
subsystem evaluation or a constant default value. -/
lemma measurable_extendCoordinates
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)] :
    Measurable (extendCoordinates (Ω := Ω) J) := by
  -- Proof comment: check measurability coordinatewise and split on membership in `J`.
  rw [measurable_pi_iff]
  intro i
  by_cases hi : J i
  · have hEq :
        (fun x : ((j : J) → Ω j) ↦ extendCoordinates (Ω := Ω) J x i) =
          fun x : ((j : J) → Ω j) ↦ x (⟨i, hi⟩ : J) := by
        funext x
        simp [extendCoordinates, hi]
    rw [hEq]
    exact measurable_pi_apply (a := (⟨i, hi⟩ : J))
  · have hEq :
        (fun x : ((j : J) → Ω j) ↦ extendCoordinates (Ω := Ω) J x i) =
          fun _ : ((j : J) → Ω j) ↦ Classical.choice (inferInstance : Nonempty (Ω i)) := by
        funext x
        simp [extendCoordinates, hi]
    rw [hEq]
    exact measurable_const

/-- Helper for Theorem 14.36: a configuration on a larger subsystem `U` restricts canonically to
any smaller subsystem `J ⊆ U`. -/
def restrictToSubset
    {J U : Set I} (hJU : J ⊆ U) :
    ((u : U) → Ω u) → ((j : J) → Ω j) :=
  fun x j ↦ x ⟨j.1, hJU j.2⟩

/-- Helper for Theorem 14.36: restriction from a larger subsystem to a smaller subsystem is
measurable. -/
lemma measurable_restrictToSubset
    {J U : Set I} (hJU : J ⊆ U) :
    Measurable (restrictToSubset (Ω := Ω) hJU) := by
  -- Proof comment: each coordinate of the restricted configuration is one coordinate projection on
  -- the larger subsystem product.
  rw [measurable_pi_iff]
  intro j
  exact measurable_pi_apply (a := (⟨j.1, hJU j.2⟩ : U))

/-- Helper for Theorem 14.36: restricting an ambient configuration to `U` and then to `J ⊆ U`
agrees with the direct ambient restriction to `J`. -/
lemma restrictToSubset_comp_restrict
    {J U : Set I} (hJU : J ⊆ U) :
    restrictToSubset (Ω := Ω) hJU ∘ U.restrict = J.restrict := by
  -- Proof comment: both maps read the same ambient coordinate on each `j ∈ J`.
  funext x
  funext j
  rfl

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: pushing a subsystem measure forward by `extendCoordinates` evaluates
on `restrict`-preimages exactly as the original subsystem measure does. -/
lemma map_extendCoordinates_preimage_restrict
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)] (μ : Measure ((j : J) → Ω j))
    {A : Set ((j : J) → Ω j)} (hA : MeasurableSet A) :
    μ.map (extendCoordinates (Ω := Ω) J) (J.restrict ⁻¹' A) = μ A := by
  -- Proof comment: rewrite the mapped measure on the preimage and collapse the restriction of the
  -- extension with `restrict_extendCoordinates`.
  rw [Measure.map_apply (measurable_extendCoordinates (Ω := Ω) J)
      (hA.preimage (Set.measurable_restrict J))]
  change
    μ ((fun x : ((j : J) → Ω j) ↦ J.restrict (extendCoordinates (Ω := Ω) J x)) ⁻¹' A) = μ A
  have hrestrict :
      (fun x : ((j : J) → Ω j) ↦ J.restrict (extendCoordinates (Ω := Ω) J x)) = fun x ↦ x := by
    funext x
    exact restrict_extendCoordinates (Ω := Ω) J x
  simp [hrestrict]

/-- Helper for Theorem 14.36: if `A` is measurable in `cylinderEvents J` and `J ⊆ U`, then `A`
is also the pullback of a measurable set on the larger subsystem `U`. -/
lemma exists_restrict_preimage_of_subset_cylinderEvents
    {J U : Set I} (hJU : J ⊆ U) {A : Set ((i : I) → Ω i)}
    (hA : MeasurableSet[cylinderEvents J] A) :
    ∃ B : Set ((u : U) → Ω u), MeasurableSet B ∧ A = U.restrict ⁻¹' B := by
  -- Proof comment: first realize `A` as a `J.restrict`-preimage, then precompose the subsystem
  -- representative with the canonical restriction `U → J`.
  have hAJ :
      A ∈ {s : Set ((i : I) → Ω i) | ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧
        s = J.restrict ⁻¹' B} := by
    rw [← measurableSets_cylinderEvents_eq_restrict_preimages J]
    exact hA
  rcases hAJ with ⟨C, hC, hEq⟩
  refine ⟨restrictToSubset (Ω := Ω) hJU ⁻¹' C,
    hC.preimage (measurable_restrictToSubset (Ω := Ω) hJU), ?_⟩
  rw [hEq]
  ext x
  rfl

/-- Helper for Theorem 14.36: countably many cylinder-measurable sets can be enlarged to one
countable common support. -/
lemma exists_countable_cylinderSupport_forall
    (A : ℕ → Set ((i : I) → Ω i))
    (hA : ∀ n, ∃ J : Set I, J.Countable ∧ MeasurableSet[cylinderEvents J] (A n)) :
    ∃ J : Set I, J.Countable ∧ ∀ n, MeasurableSet[cylinderEvents J] (A n) := by
  classical
  choose J hJcount hJmeas using hA
  refine ⟨⋃ n, J n, Set.countable_iUnion hJcount, ?_⟩
  intro n
  -- Proof comment: enlarge the `n`th countable support into the single union support.
  exact
    (cylinderEvents_mono (show J n ⊆ ⋃ k, J k from by
      intro i hi
      exact Set.mem_iUnion.2 ⟨n, hi⟩)) _ (hJmeas n)

/-- Helper for Theorem 14.36: every measurable set is pulled back from a measurable set on some
countable subsystem. -/
lemma exists_countable_restrict_preimage_of_measurableSet
    {A : Set ((i : I) → Ω i)} (hA : MeasurableSet A) :
    ∃ J : Set I, J.Countable ∧
      ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧ A = J.restrict ⁻¹' B := by
  -- Proof comment: choose a countable cylinder support and then rewrite cylinder measurability by
  -- the `restrict`-preimage characterization from Remark 14.10.
  rcases (measurableSet_iff_exists_countable_cylinderEvents.mp hA) with ⟨J, hJ, hAJ⟩
  have hAJ' : ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧ A = J.restrict ⁻¹' B := by
    have hmem :
        A ∈ {s : Set ((i : I) → Ω i) | MeasurableSet[cylinderEvents J] s} := hAJ
    change A ∈ {s : Set ((i : I) → Ω i) | ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧
      s = J.restrict ⁻¹' B}
    rw [← measurableSets_cylinderEvents_eq_restrict_preimages J]
    exact hmem
  rcases hAJ' with ⟨B, hB, hEq⟩
  exact ⟨J, hJ, B, hB, hEq⟩

/-- Helper for Theorem 14.36: countably many measurable sets can be realized on one countable
subsystem by pulling measurable sets back along `restrict`. -/
lemma exists_countable_restrict_preimage_forall
    (A : ℕ → Set ((i : I) → Ω i)) (hA : ∀ n, MeasurableSet (A n)) :
    ∃ J : Set I, J.Countable ∧
      ∀ n, ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧ A n = J.restrict ⁻¹' B := by
  have hCylinder : ∀ n, ∃ J : Set I, J.Countable ∧ MeasurableSet[cylinderEvents J] (A n) := by
    intro n
    exact (measurableSet_iff_exists_countable_cylinderEvents.mp (hA n))
  rcases exists_countable_cylinderSupport_forall (A := A) hCylinder with ⟨J, hJ, hJmeas⟩
  refine ⟨J, hJ, ?_⟩
  intro n
  -- Proof comment: once the support is fixed, each set becomes a measurable subsystem preimage.
  have hAJ : MeasurableSet[cylinderEvents J] (A n) := hJmeas n
  have hAJ' : ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧ A n = J.restrict ⁻¹' B := by
    have hmem :
        A n ∈ {s : Set ((i : I) → Ω i) | MeasurableSet[cylinderEvents J] s} := hAJ
    change A n ∈ {s : Set ((i : I) → Ω i) | ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧
      s = J.restrict ⁻¹' B}
    rw [← measurableSets_cylinderEvents_eq_restrict_preimages J]
    exact hmem
  rcases hAJ' with ⟨B, hB, hEq⟩
  exact ⟨B, hB, hEq⟩

/-- Helper for Theorem 14.36: the union of countably many measurable sets is still pulled back
from one measurable set on a countable subsystem. -/
lemma exists_countable_restrict_preimage_iUnion
    (A : ℕ → Set ((i : I) → Ω i)) (hA : ∀ n, MeasurableSet (A n)) :
    ∃ J : Set I, J.Countable ∧
      ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧ (⋃ n, A n) = J.restrict ⁻¹' B := by
  rcases exists_countable_restrict_preimage_forall (A := A) hA with ⟨J, hJ, hJrepr⟩
  choose B hBmeas hBeq using hJrepr
  refine ⟨J, hJ, ⋃ n, B n, MeasurableSet.iUnion hBmeas, ?_⟩
  -- Proof comment: `restrict` commutes with countable unions, so the subsystem representatives
  -- glue by taking the union on the subsystem space.
  ext x
  simp [hBeq]

/-- Helper for Theorem 14.36: a decreasing sequence of sets agrees with the finite intersection of
its first `n + 1` terms. -/
lemma biInter_range_eq_of_antitone
    {α : Type*} (A : ℕ → Set α) (hA : Antitone A) (n : ℕ) :
    (⋂ m ∈ Finset.range (n + 1), A m) = A n := by
  ext x
  constructor
  · intro hx
    -- Proof comment: membership in the finite intersection includes the terminal index `n`.
    have hx' : ∀ m, m ∈ Finset.range (n + 1) → x ∈ A m := by
      simpa [Set.mem_iInter] using hx
    exact hx' n (by simp)
  · intro hx
    -- Proof comment: antitonicity pushes membership in `A n` down to every earlier set.
    simpa [Set.mem_iInter] using
      (fun m hm ↦ hA (Nat.le_of_lt_succ <| Finset.mem_range.mp hm) hx)

/-- Helper for Theorem 14.36: a measurable decreasing sequence can be realized on one countable
subsystem by a measurable decreasing sequence of subsystem sets. -/
lemma exists_countable_restrict_preimage_of_antitone
    (A : ℕ → Set ((i : I) → Ω i)) (hA : ∀ n, MeasurableSet (A n)) (hMono : Antitone A) :
    ∃ J : Set I, J.Countable ∧
      ∃ B : ℕ → Set ((j : J) → Ω j),
        (∀ n, MeasurableSet (B n)) ∧
          (∀ n, A n = J.restrict ⁻¹' B n) ∧
          Antitone B := by
  rcases exists_countable_restrict_preimage_forall (A := A) hA with ⟨J, hJ, hJrepr⟩
  choose B hB hEq using hJrepr
  let C : ℕ → Set ((j : J) → Ω j) := fun n ↦ ⋂ m ∈ Finset.range (n + 1), B m
  refine ⟨J, hJ, C, ?_, ?_, ?_⟩
  · intro n
    -- Proof comment: each `C n` is a finite intersection of measurable subsystem sets.
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦ hB m
  · intro n
    -- Proof comment: pull the finite intersection back along `restrict`, then collapse it with
    -- the antitone identity from `biInter_range_eq_of_antitone`.
    calc
      A n = ⋂ m ∈ Finset.range (n + 1), A m := by
        symm
        exact biInter_range_eq_of_antitone A hMono n
      _ = J.restrict ⁻¹' C n := by
        ext x
        simp [C, hEq]
  · intro n m hnm
    -- Proof comment: the later finite intersection contains every factor from the earlier one.
    intro x
    simp only [C, Set.mem_iInter]
    intro hx k hk
    exact hx k (Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hnm))

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: if an ambient antitone sequence is obtained by pulling subsystem
sets back along `restrict`, then emptiness of the ambient intersection forces emptiness of the
subsystem intersection as well. -/
lemma iInter_eq_empty_of_restrict_preimage
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)]
    (A : ℕ → Set ((i : I) → Ω i)) (B : ℕ → Set ((j : J) → Ω j))
    (hEq : ∀ n, A n = J.restrict ⁻¹' B n) (hEmpty : (⋂ n, A n) = ∅) :
    (⋂ n, B n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  have hxA : ∀ n, extendCoordinates (Ω := Ω) J x ∈ A n := by
    intro n
    rw [hEq n]
    -- Proof comment: extend a subsystem point to the ambient product and use that restriction
    -- of the extension is the original subsystem point.
    simpa [restrict_extendCoordinates (Ω := Ω) J x] using (Set.mem_iInter.mp hx n)
  have hLift : extendCoordinates (Ω := Ω) J x ∈ ⋂ n, A n :=
    Set.mem_iInter.2 hxA
  have : extendCoordinates (Ω := Ω) J x ∈ (∅ : Set ((i : I) → Ω i)) := by
    -- Proof comment: the lifted point would lie in the ambient empty intersection, contradiction.
    simpa [hEmpty] using hLift
  simpa using this

/-- Helper for Theorem 14.36: after realizing an antitone measurable sequence on one countable
subsystem, the subsystem sequence can also be chosen with empty intersection. -/
lemma exists_countable_restrict_preimage_of_antitone_empty
    [∀ i, Nonempty (Ω i)]
    (A : ℕ → Set ((i : I) → Ω i)) (hA : ∀ n, MeasurableSet (A n)) (hMono : Antitone A)
    (hEmpty : (⋂ n, A n) = ∅) :
    ∃ J : Set I, J.Countable ∧
      ∃ B : ℕ → Set ((j : J) → Ω j),
        (∀ n, MeasurableSet (B n)) ∧
          (∀ n, A n = J.restrict ⁻¹' B n) ∧
          Antitone B ∧
          (⋂ n, B n) = ∅ := by
  classical
  rcases exists_countable_restrict_preimage_of_antitone
      (Ω := Ω) A hA hMono with ⟨J, hJ, B, hB, hEq, hBmono⟩
  refine ⟨J, hJ, B, hB, hEq, hBmono, ?_⟩
  -- Proof comment: apply the subsystem-lifting contradiction once the ambient intersection is
  -- known to be empty.
  exact iInter_eq_empty_of_restrict_preimage (Ω := Ω) J A B hEq hEmpty

/-- Helper for Theorem 14.36: once a decreasing ambient sequence is represented on one subsystem,
continuity from above for a finite subsystem measure transfers to the lifted ambient measure. -/
lemma tendsto_zero_map_extendCoordinates_of_antitone
    (J : Set I) [DecidablePred J] [∀ i, Nonempty (Ω i)]
    (μ : Measure ((j : J) → Ω j)) [IsFiniteMeasure μ]
    (A : ℕ → Set ((i : I) → Ω i)) (B : ℕ → Set ((j : J) → Ω j))
    (hB : ∀ n, MeasurableSet (B n)) (hEq : ∀ n, A n = J.restrict ⁻¹' B n)
    (hMono : Antitone B) (hEmpty : (⋂ n, A n) = ∅) :
    Tendsto (fun n ↦ μ.map (extendCoordinates (Ω := Ω) J) (A n)) atTop (nhds 0) := by
  have hEmptyB : (⋂ n, B n) = ∅ :=
    iInter_eq_empty_of_restrict_preimage (Ω := Ω) J A B hEq hEmpty
  have hTendsto :
      Tendsto (fun n ↦ μ (B n)) atTop (nhds (μ (⋂ n, B n))) := by
    refine MeasureTheory.tendsto_measure_iInter_atTop ?_ hMono ?_
    · intro n
      exact (hB n).nullMeasurableSet
    · exact ⟨0, (measure_lt_top μ (B 0)).ne⟩
  have hTendstoZero :
      Tendsto (fun n ↦ μ (B n)) atTop (nhds 0) := by
    -- Proof comment: continuity from above collapses to zero because the subsystem intersection
    -- is already empty.
    simpa [hEmptyB] using hTendsto
  -- Proof comment: rewrite the lifted ambient sets back to the subsystem representatives and use
  -- the previous continuity statement there.
  convert hTendstoZero using 1
  ext n
  rw [hEq n, map_extendCoordinates_preimage_restrict (Ω := Ω) J μ (hB n)]

/-- Helper for Theorem 14.36: a finite subsystem cylinder on the restricted product can be viewed
as a finite subsystem cylinder on the ambient product by forgetting the subtype wrappers. -/
def pullbackToSubtypeSupport
    {J : Set I} (L : Finset J) :
    ((k : L.map ⟨Subtype.val, Subtype.val_injective⟩) → Ω k) → ((l : L) → Ω l.1) :=
  fun x l ↦ x ⟨l.1.1, Finset.mem_map.2 ⟨l.1, l.2, rfl⟩⟩

/-- Helper for Theorem 14.36: forgetting the subtype wrappers on a finite subsystem is measurable
coordinatewise. -/
lemma measurable_pullbackToSubtypeSupport
    {J : Set I} (L : Finset J) :
    Measurable (pullbackToSubtypeSupport (Ω := Ω) L) := by
  -- Proof comment: each restricted coordinate is one ambient coordinate projection on the mapped
  -- finite support.
  rw [measurable_pi_iff]
  intro l
  exact measurable_pi_apply
    (a := (⟨l.1.1, Finset.mem_map.2 ⟨l.1, l.2, rfl⟩⟩ :
      L.map ⟨Subtype.val, Subtype.val_injective⟩))

/-- Helper for Theorem 14.36: forgetting subtype wrappers identifies a finite subsystem `L` with
its ambient support `L.map Subtype.val`. -/
noncomputable def mappedSubtypeValEquiv
    {J : Set I} (L : Finset J) :
    L ≃ L.map ⟨Subtype.val, Subtype.val_injective⟩ :=
  Equiv.ofBijective
    (fun l ↦
      (⟨l.1.1, Finset.mem_map.2 ⟨l.1, l.2, rfl⟩⟩ :
        L.map ⟨Subtype.val, Subtype.val_injective⟩))
    (by
      constructor
      · intro l₁ l₂ h
        cases l₁ with
        | mk j₁ hj₁ =>
            cases l₂ with
            | mk j₂ hj₂ =>
                simp only [Subtype.mk.injEq] at h
                have hJ : j₁ = j₂ := by
                  apply Subtype.ext
                  exact h
                subst hJ
                rfl
      · intro k
        rcases Finset.mem_map.1 k.2 with ⟨j, hj, hjk⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        apply Subtype.ext
        simpa using hjk)

/-- Helper for Theorem 14.36: tuples on a finite subtype support are measurably equivalent to
tuples on the ambient finite support obtained by forgetting the subtype wrappers. -/
noncomputable def finiteSubtypeSupportMeasurableEquiv
    {J : Set I} (L : Finset J) :
    ((l : L) → Ω l.1) ≃ᵐ ((k : L.map ⟨Subtype.val, Subtype.val_injective⟩) → Ω k) :=
  -- Proof comment: `MeasurableEquiv.piCongrLeft` transports tuples along the support equivalence
  -- `mappedSubtypeValEquiv L`, whose coordinates are definitionally the same ambient indices.
  show ((l : L) → Ω ((mappedSubtypeValEquiv L l).1)) ≃ᵐ
      ((k : L.map ⟨Subtype.val, Subtype.val_injective⟩) → Ω k) from
    MeasurableEquiv.piCongrLeft
      (fun k : L.map ⟨Subtype.val, Subtype.val_injective⟩ ↦ Ω k)
      (mappedSubtypeValEquiv L)

/-- Helper for Theorem 14.36: the inverse direction of the finite-support measurable equivalence
is exactly the wrapper-forgetting map `pullbackToSubtypeSupport`. -/
lemma finiteSubtypeSupportMeasurableEquiv_symm_apply
    {J : Set I} (L : Finset J)
    (x : (k : L.map ⟨Subtype.val, Subtype.val_injective⟩) → Ω k) (l : L) :
    (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).symm x l =
      pullbackToSubtypeSupport (Ω := Ω) L x l := by
  rfl

/-- Helper for Theorem 14.36: after extending a subsystem tuple to the ambient product, restricting
to the mapped finite support agrees with first restricting to the subtype support and then
forgetting subtype wrappers. -/
lemma finiteSubtypeSupportMeasurableEquiv_comp_restrict_extendCoordinates
    {J : Set I} [DecidablePred J] [∀ i, Nonempty (Ω i)] (L : Finset J) :
    finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L ∘ L.restrict =
      (L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict ∘
        extendCoordinates (Ω := Ω) J := by
  funext x
  funext k
  rcases (mappedSubtypeValEquiv L).surjective k with ⟨l, rfl⟩
  -- Proof comment: every mapped ambient coordinate comes from a unique `l : L`, and both
  -- composites evaluate the original subsystem tuple `x` at that coordinate.
  have hleft :
      (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L)
          ((L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1)) x)
          ((mappedSubtypeValEquiv L) l) =
        ((L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1)) x) l := by
    simpa [finiteSubtypeSupportMeasurableEquiv] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := mappedSubtypeValEquiv L)
        (β := fun k : L.map ⟨Subtype.val, Subtype.val_injective⟩ ↦ Ω k)
        (x := (L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1)) x)
        (i := l))
  rw [Function.comp_apply, Function.comp_apply, hleft]
  change x l.1 = extendCoordinates (Ω := Ω) J x l.1.1
  simpa using (congrFun (restrict_extendCoordinates (Ω := Ω) J x) l).symm

/-- Helper for Theorem 14.36: pulling back a subtype cylinder along `restrict J` gives the
corresponding ambient cylinder on the same finite coordinates. -/
lemma preimage_restrict_cylinder_eq
    {J : Set I} (L : Finset J) {S : Set ((l : L) → Ω l.1)} :
    J.restrict ⁻¹' cylinder L S =
      cylinder (L.map ⟨Subtype.val, Subtype.val_injective⟩)
        (pullbackToSubtypeSupport (Ω := Ω) L ⁻¹' S) := by
  -- Proof comment: both sides say that the ambient point restricted to the finite base `L`
  -- belongs to `S`.
  ext x
  change L.restrict (J.restrict x) ∈ S ↔
    pullbackToSubtypeSupport (Ω := Ω) L
      ((L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict x) ∈ S
  rfl

/-- Helper for Theorem 14.36: an ambient measure is a subsystem owner on `J` if it is a
probability measure and it reproduces the prescribed finite marginals on every finite subset of
`J`. -/
def IsCountableAmbientOwner
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    (J : Set I) (ν : Measure ((i : I) → Ω i)) : Prop :=
  IsProbabilityMeasure ν ∧
    ∀ K : Finset I, (↑K : Set I) ⊆ J → ν.map K.restrict = P K

/-- Helper for Theorem 14.36: a subsystem owner evaluates every finite cylinder supported in the
subsystem by the prescribed marginal. -/
lemma IsCountableAmbientOwner.measure_cylinder
    {P : ∀ J : Finset I, Measure ((j : J) → Ω j)}
    {J : Set I} {ν : Measure ((i : I) → Ω i)}
    (hν : IsCountableAmbientOwner (Ω := Ω) P J ν)
    {K : Finset I} (hK : (↑K : Set I) ⊆ J)
    {S : Set ((j : K) → Ω j)} (hS : MeasurableSet S) :
    ν (cylinder K S) = P K S := by
  -- Proof comment: rewrite the cylinder through the finite restriction map and then apply the
  -- owner identity on the support `K`.
  rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _) hS, hν.2 K hK]

/-- Helper for Theorem 14.36: an owner on a larger subsystem is automatically an owner on each
smaller subsystem. -/
lemma IsCountableAmbientOwner.mono
    {P : ∀ J : Finset I, Measure ((j : J) → Ω j)}
    {J U : Set I} {ν : Measure ((i : I) → Ω i)}
    (hν : IsCountableAmbientOwner (Ω := Ω) P U ν) (hJU : J ⊆ U) :
    IsCountableAmbientOwner (Ω := Ω) P J ν := by
  refine ⟨hν.1, ?_⟩
  intro K hK
  exact hν.2 K (Set.Subset.trans hK hJU)

/-- Helper for Theorem 14.36: two subsystem owners with the same support agree on every finite
cylinder supported there. -/
lemma IsCountableAmbientOwner.eq_on_cylinder
    {P : ∀ J : Finset I, Measure ((j : J) → Ω j)}
    {J : Set I} {ν₁ ν₂ : Measure ((i : I) → Ω i)}
    (hν₁ : IsCountableAmbientOwner (Ω := Ω) P J ν₁)
    (hν₂ : IsCountableAmbientOwner (Ω := Ω) P J ν₂)
    {K : Finset I} (hK : (↑K : Set I) ⊆ J)
    {S : Set ((j : K) → Ω j)} (hS : MeasurableSet S) :
    ν₁ (cylinder K S) = ν₂ (cylinder K S) := by
  -- Proof comment: both owners reduce the same cylinder to the same finite-dimensional marginal
  -- `P K`.
  rw [hν₁.measure_cylinder hK hS, hν₂.measure_cylinder hK hS]

/-- Helper for Theorem 14.36: if two ambient owners are nested by supports, then their
pushforwards to the smaller restricted product coincide. -/
lemma IsCountableAmbientOwner.map_restrict_eq_of_subset
    {P : ∀ J : Finset I, Measure ((j : J) → Ω j)}
    {J U : Set I} {νJ νU : Measure ((i : I) → Ω i)}
    (hJU : J ⊆ U)
    (hνJ : IsCountableAmbientOwner (Ω := Ω) P J νJ)
    (hνU : IsCountableAmbientOwner (Ω := Ω) P U νU) :
    νJ.map J.restrict = νU.map J.restrict := by
  let μJ : Measure ((j : J) → Ω j) := νJ.map J.restrict
  let μU : Measure ((j : J) → Ω j) := νU.map J.restrict
  letI : IsProbabilityMeasure νJ := hνJ.1
  letI : IsProbabilityMeasure νU := hνU.1
  haveI : IsProbabilityMeasure μJ :=
    Measure.isProbabilityMeasure_map (Set.measurable_restrict J).aemeasurable
  haveI : IsProbabilityMeasure μU :=
    Measure.isProbabilityMeasure_map (Set.measurable_restrict J).aemeasurable
  refine ext_of_generate_finite
    (measurableCylinders (fun j : J ↦ Ω j))
    generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders
    ?_
    ?_
  · intro s hs
    rcases (mem_measurableCylinders s).mp hs with ⟨L, S, hS, rfl⟩
    let K : Finset I := L.map ⟨Subtype.val, Subtype.val_injective⟩
    let T : Set ((k : K) → Ω k) := pullbackToSubtypeSupport (Ω := Ω) L ⁻¹' S
    have hT : MeasurableSet T := hS.preimage (measurable_pullbackToSubtypeSupport (Ω := Ω) L)
    have hKJ : (↑K : Set I) ⊆ J := by
      intro i hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      exact j.2
    calc
      μJ (cylinder L S) = νJ (cylinder K T) := by
        rw [Measure.map_apply (Set.measurable_restrict J) hS.cylinder,
          preimage_restrict_cylinder_eq]
      _ = P K T := hνJ.measure_cylinder hKJ hT
      _ = νU (cylinder K T) := by
        symm
        exact hνU.measure_cylinder (Set.Subset.trans hKJ hJU) hT
      _ = μU (cylinder L S) := by
        rw [Measure.map_apply (Set.measurable_restrict J) hS.cylinder,
          preimage_restrict_cylinder_eq]
  · simpa [μJ, μU]

/-- Helper for Theorem 14.36: nested ambient owners agree on every event measurable with respect
to the smaller cylinder `σ`-algebra. -/
lemma IsCountableAmbientOwner.eq_on_cylinderEvents_of_subset
    {P : ∀ J : Finset I, Measure ((j : J) → Ω j)}
    {J U : Set I} {νJ νU : Measure ((i : I) → Ω i)}
    (hJU : J ⊆ U)
    (hνJ : IsCountableAmbientOwner (Ω := Ω) P J νJ)
    (hνU : IsCountableAmbientOwner (Ω := Ω) P U νU)
    {A : Set ((i : I) → Ω i)} (hA : MeasurableSet[cylinderEvents J] A) :
    νJ A = νU A := by
  rcases (show A ∈
      {s : Set ((i : I) → Ω i) | ∃ B : Set ((j : J) → Ω j), MeasurableSet B ∧
        s = J.restrict ⁻¹' B} from by
      rw [← measurableSets_cylinderEvents_eq_restrict_preimages J]
      exact hA) with ⟨B, hB, hEq⟩
  -- Proof comment: evaluate both ambient measures through the same restricted product event, then
  -- use equality of the restricted pushforwards.
  rw [hEq, ← Measure.map_apply (Set.measurable_restrict J) hB,
    ← Measure.map_apply (Set.measurable_restrict J) hB,
    hνJ.map_restrict_eq_of_subset hJU hνU]

/-- Helper for Theorem 14.36: a finite cylinder supported on `s` is measurable for the
countable-support sigma-algebra generated by the coordinates in `s`. -/
lemma measurableSet_cylinderEvents_cylinder
    (s : Finset I) {S : Set ((i : s) → Ω i)} (hS : MeasurableSet S) :
    MeasurableSet[cylinderEvents (X := Ω) (s : Set I)] (cylinder s S) := by
  -- Proof comment: a finite cylinder is the preimage of its base set under the restriction map to
  -- the same finite support.
  simpa [MeasureTheory.cylinder] using
    hS.preimage
      (MeasureTheory.measurable_restrict_cylinderEvents (X := Ω) (s : Set I))

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: extend a finite-coordinate tuple to the ambient product by filling
the missing coordinates with default points. -/
noncomputable def extendCoordinatesFinset
    (K : Finset I) [∀ i, Nonempty (Ω i)] :
    ((k : K) → Ω k) → (i : I) → Ω i :=
  let _ : DecidableEq I := Classical.decEq I
  fun x i ↦ if hi : i ∈ K then x ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty (Ω i))

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: the finite-coordinate extension map is measurable coordinatewise. -/
lemma measurable_extendCoordinatesFinset
    (K : Finset I) [∀ i, Nonempty (Ω i)] :
    Measurable (extendCoordinatesFinset (Ω := Ω) K) := by
  -- Proof comment: each ambient coordinate is either a finite-coordinate projection or a constant.
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ K
  · have hEq :
        (fun x : ((k : K) → Ω k) ↦ extendCoordinatesFinset (Ω := Ω) K x i) =
          fun x : ((k : K) → Ω k) ↦ x (⟨i, hi⟩ : K) := by
        funext x
        simp [extendCoordinatesFinset, hi]
    rw [hEq]
    exact measurable_pi_apply (a := (⟨i, hi⟩ : K))
  · have hEq :
        (fun x : ((k : K) → Ω k) ↦ extendCoordinatesFinset (Ω := Ω) K x i) =
          fun _ : ((k : K) → Ω k) ↦ Classical.choice (inferInstance : Nonempty (Ω i)) := by
        funext x
        simp [extendCoordinatesFinset, hi]
    rw [hEq]
    exact measurable_const

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Helper for Theorem 14.36: restricting a finite-coordinate extension back to its finite base
recovers the original tuple. -/
lemma restrict_extendCoordinatesFinset
    (K : Finset I) [∀ i, Nonempty (Ω i)] (x : (k : K) → Ω k) :
    K.restrict (extendCoordinatesFinset (Ω := Ω) K x) = x := by
  -- Proof comment: on each coordinate in `K`, the extension uses the original finite tuple.
  funext k
  cases k with
  | mk i hi =>
      have hEq :
          extendCoordinatesFinset (Ω := Ω) K x i = x ⟨i, hi⟩ := by
        simp [extendCoordinatesFinset, hi]
      simpa using hEq

/-- Helper for Theorem 14.36: restricting a finite-coordinate extension from `K` to a smaller
finite support `L ⊆ K` coincides with the canonical finite restriction map. -/
lemma restrict_comp_extendCoordinatesFinset
    {L K : Finset I} (hLK : L ⊆ K) [∀ i, Nonempty (Ω i)] :
    L.restrict ∘ extendCoordinatesFinset (Ω := Ω) K = Finset.restrict₂ hLK := by
  -- Proof comment: on each `l ∈ L`, the extension reads the original `K`-coordinate because
  -- `hLK` keeps the coordinate inside the finite base `K`.
  funext x
  funext l
  simp [Function.comp, extendCoordinatesFinset, hLK l.2]

/-- Helper for Theorem 14.36: finite supports already have ambient owners by extending the single
finite marginal to the ambient product. -/
lemma existsFiniteAmbientOwner
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) {J : Set I} (hJ : J.Finite) :
    ∃ ν : Measure ((i : I) → Ω i), IsCountableAmbientOwner (Ω := Ω) P J ν := by
  classical
  let K : Finset I := hJ.toFinset
  have hK : (K : Set I) = J := by
    ext i
    simp [K]
  letI : ∀ i, Nonempty (Ω i) := fun i ↦ coordinateNonempty (Ω := Ω) P i
  refine ⟨(P K).map (extendCoordinatesFinset (Ω := Ω) K), ?_⟩
  refine ⟨Measure.isProbabilityMeasure_map
    ((measurable_extendCoordinatesFinset (Ω := Ω) K).aemeasurable), ?_⟩
  intro L hLJ
  have hLK : L ⊆ K := by
    intro i hi
    have : i ∈ J := hLJ hi
    simpa [hK.symm] using this
  -- Proof comment: after extending the full finite tuple on `K`, restricting to `L` is exactly
  -- the finite projection `restrict₂ hLK`, so projectivity of `P` closes the marginal identity.
  calc
    ((P K).map (extendCoordinatesFinset (Ω := Ω) K)).map L.restrict
        = (P K).map (L.restrict ∘ extendCoordinatesFinset (Ω := Ω) K) := by
            rw [Measure.map_map (Finset.measurable_restrict L)
              (measurable_extendCoordinatesFinset (Ω := Ω) K)]
    _ = (P K).map (Finset.restrict₂ hLK) := by
          refine Measure.map_congr <| Filter.Eventually.of_forall fun x ↦ ?_
          ext l
          simp [Function.comp, extendCoordinatesFinset, hLK l.2]
    _ = P L := (hP K L hLK).symm

/-- Helper for Theorem 14.36: the first `n + 1` points of an enumeration of a countable support,
recorded as a finite subsystem of the subtype `J`. -/
noncomputable def prefixSupport
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) : Finset J :=
  Finset.univ.map
    ⟨fun i : Finset.Iic n ↦ e i, by
      intro a b hab
      exact Subtype.ext (e.injective hab)⟩

/-- Helper for Theorem 14.36: the ambient finite support obtained by forgetting the subtype
wrappers on `prefixSupport e n`. -/
noncomputable def prefixAmbientSupport
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) : Finset I :=
  (prefixSupport e n).map ⟨Subtype.val, Subtype.val_injective⟩

/-- Helper for Theorem 14.36: the finite prefix `Iic n` of `ℕ` is equivalent to the finite
subsystem consisting of the first `n + 1` enumerated points of `J`. -/
noncomputable def prefixSupportEquiv
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) : Finset.Iic n ≃ prefixSupport e n where
  toFun i := ⟨e i, by
    exact Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
  invFun j := ⟨e.symm j.1, by
    rcases Finset.mem_map.1 j.2 with ⟨i, -, hji⟩
    have hEq : e i = j.1 := by simpa using hji
    have hi : e.symm j.1 = i := by
      apply e.injective
      simpa [hEq]
    simpa [hi] using i.2⟩
  left_inv i := by
    -- Proof comment: the enumeration and its inverse cancel on the index `i`.
    apply Subtype.ext
    simpa using e.left_inv i
  right_inv j := by
    -- Proof comment: every point of the finite prefix support comes from a unique index in
    -- `Iic n`, so applying the inverse recovers that support point.
    apply Subtype.ext
    simpa using e.right_inv j.1

/-- Helper for Theorem 14.36: reindexing tuples from the finite subsystem `prefixSupport e n` to
the ordered prefix `Iic n` is a measurable equivalence. -/
noncomputable def prefixSupportMeasurableEquiv
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    ((j : prefixSupport e n) → Ω j.1) ≃ᵐ ((i : Finset.Iic n) → Ω ((e i).1)) :=
  -- Proof comment: keep the codomain in the `prefixSupportEquiv` spelling world so dependent
  -- tuple reindexing does not rely on elaborator normalization across equivalent index terms.
  show ((j : prefixSupport e n) → Ω j.1) ≃ᵐ
      ((i : Finset.Iic n) → Ω ((prefixSupportEquiv e n i).1)) from
    (MeasurableEquiv.piCongrLeft
      (fun j : prefixSupport e n ↦ Ω j.1) (prefixSupportEquiv e n)).symm

/-- Helper for Theorem 14.36: an enumeration of a countable support reindexes the whole subtype
product by `ℕ`. -/
noncomputable def countableProductMeasurableEquiv
    {J : Set I} (e : ℕ ≃ J) :
    ((j : J) → Ω j.1) ≃ᵐ ((n : ℕ) → Ω ((e n).1)) :=
  -- Proof comment: use the enumeration itself as the index equivalence for the whole product.
  (MeasurableEquiv.piCongrLeft (fun j : J ↦ Ω j.1) e).symm

/-- Helper for Theorem 14.36: after transporting the whole subtype product to an `ℕ`-indexed
product, restricting back to a finite prefix support is exactly the same as first taking the
ordered prefix and then transporting it back to that finite subtype support. -/
lemma prefixSupportRestrict_comp_countableProductMeasurableEquiv_symm
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    (prefixSupport e n).restrict ∘ (countableProductMeasurableEquiv (Ω := Ω) e).symm =
      (prefixSupportMeasurableEquiv (Ω := Ω) e n).symm ∘
        Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n := by
  funext x
  funext j
  -- Proof comment: every point of `prefixSupport e n` is represented by some `i : Iic n`, and
  -- both composites simply read the `i`-th coordinate of the `ℕ`-indexed tuple `x`.
  rcases Finset.mem_map.1 j.2 with ⟨i, -, hij⟩
  have hj :
      (⟨e i, Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩⟩ : prefixSupport e n) = j := by
    apply Subtype.ext
    simpa using hij
  cases hj
  have hwhole :
      ((countableProductMeasurableEquiv (Ω := Ω) e).symm x) (e i) = x i := by
    simpa [countableProductMeasurableEquiv] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := e) (β := fun j : J ↦ Ω j.1) (x := x) (i := i))
  have hprefix :
      ((prefixSupportMeasurableEquiv (Ω := Ω) e n).symm
          (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n x))
        ⟨e i, Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩⟩ =
          (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n x) i := by
    simpa [prefixSupportMeasurableEquiv] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := prefixSupportEquiv e n)
        (β := fun j : prefixSupport e n ↦ Ω j.1)
        (x := Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n x)
        (i := i))
  change ((countableProductMeasurableEquiv (Ω := Ω) e).symm x) (e i) =
    ((prefixSupportMeasurableEquiv (Ω := Ω) e n).symm
      (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n x))
      ⟨e i, Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
  rw [hwhole, hprefix]
  rfl

/-- Helper for Theorem 14.36: the enumerated finite prefix subsystem grows with the prefix length.
-/
lemma prefixSupport_mono
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    prefixSupport e n ⊆ prefixSupport e (n + 1) := by
  intro j hj
  -- Proof comment: the same enumerated point appears in the longer prefix because `Iic n`
  -- embeds into `Iic (n + 1)`.
  rcases Finset.mem_map.1 hj with ⟨i, -, rfl⟩
  exact Finset.mem_map.2
    ⟨⟨i.1, Finset.mem_Iic.mpr <|
        Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n)⟩, Finset.mem_univ _, rfl⟩

/-- Helper for Theorem 14.36: every coordinate in `prefixAmbientSupport e n` lies in the ambient
countable support `J`. -/
lemma prefixAmbientSupport_subset
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    (↑(prefixAmbientSupport e n) : Set I) ⊆ J := by
  intro i hi
  rcases Finset.mem_map.1 hi with ⟨j, -, rfl⟩
  exact j.2

/-- Helper for Theorem 14.36: forgetting subtype wrappers preserves monotonicity of the
enumerated prefix supports. -/
lemma prefixAmbientSupport_mono
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    prefixAmbientSupport e n ⊆ prefixAmbientSupport e (n + 1) := by
  intro i hi
  -- Proof comment: once the subtype-level prefix support is monotone, mapping by `Subtype.val`
  -- keeps the same witness in the longer ambient prefix support.
  rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
  exact Finset.mem_map.2 ⟨j, prefixSupport_mono e n hj, rfl⟩

/-- Helper for Theorem 14.36: transport an ambient finite-prefix tuple to the ordered `Iic n`
coordinates determined by the enumeration `e`. -/
noncomputable def prefixOrderedMap
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    ((k : prefixAmbientSupport e n) → Ω k) → ((i : Finset.Iic n) → Ω ((e i).1)) :=
  prefixSupportMeasurableEquiv (Ω := Ω) e n ∘
    pullbackToSubtypeSupport (Ω := Ω) (prefixSupport e n)

/-- Helper for Theorem 14.36: the ambient-prefix transport to ordered coordinates is measurable.
-/
lemma measurable_prefixOrderedMap
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    Measurable (prefixOrderedMap (Ω := Ω) e n) := by
  -- Proof comment: both stages are coordinatewise measurable, so their composition is measurable.
  exact (prefixSupportMeasurableEquiv (Ω := Ω) e n).measurable.comp
    (measurable_pullbackToSubtypeSupport (Ω := Ω) (prefixSupport e n))

/-- Helper for Theorem 14.36: mapping a finite subsystem of `J` by `Subtype.val` preserves subset
relations. -/
lemma mapSubtypeVal_subset
    {J : Set I} {L U : Finset J} (hLU : L ⊆ U) :
    L.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
      U.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  intro i hi
  -- Proof comment: a witness `j ∈ L` for membership in the mapped support remains a witness in
  -- `U` by the original subset relation.
  rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
  exact Finset.mem_map.mpr ⟨j, hLU hj, rfl⟩

/-- Helper for Theorem 14.36: finite restriction on ambient supports commutes with forgetting the
subtype wrappers on the same coordinates. -/
lemma pullbackToSubtypeSupport_comp_restrict₂
    {J : Set I} {L U : Finset J} (hLU : L ⊆ U) :
    pullbackToSubtypeSupport (Ω := Ω) L ∘
        Finset.restrict₂ (π := fun i : I ↦ Ω i) (mapSubtypeVal_subset hLU) =
      Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hLU ∘ pullbackToSubtypeSupport (Ω := Ω) U := by
  -- Proof comment: both composites read the same coordinate of the ambient tuple indexed by the
  -- underlying element of `L`.
  funext x
  funext l
  rfl

/-- Helper for Theorem 14.36: forgetting subtype wrappers turns any ambient projective family into
the canonical companion projective family on finite subsets of a fixed countable support. -/
lemma subtypeProjectiveFamily_of_ambientProjective
    (P : ∀ K : Finset I, Measure ((k : K) → Ω k))
    (hP : IsProjectiveMeasureFamily P) {J : Set I} :
    IsProjectiveMeasureFamily (α := fun j : J ↦ Ω j.1)
      (fun L : Finset J ↦
        show Measure ((l : L) → Ω l.1) from
          (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
            (pullbackToSubtypeSupport (Ω := Ω) L)) := by
  let Psub : ∀ L : Finset J, Measure ((l : L) → Ω l.1) :=
    fun L ↦
      show Measure ((l : L) → Ω l.1) from
        (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
          (pullbackToSubtypeSupport (Ω := Ω) L)
  intro U L hLU
  symm
  -- Proof comment: first push the large ambient marginal down to the smaller ambient support,
  -- then commute that restriction past the wrapper-forgetting map.
  calc
    (Psub U).map (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hLU)
        = (P (U.map ⟨Subtype.val, Subtype.val_injective⟩)).map
            (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hLU ∘
              pullbackToSubtypeSupport (Ω := Ω) U) := by
              simpa [Psub] using
                (Measure.map_map
                  (Finset.measurable_restrict₂ (X := fun j : J ↦ Ω j.1) hLU)
                  (measurable_pullbackToSubtypeSupport (Ω := Ω) U) :
                    ((P (U.map ⟨Subtype.val, Subtype.val_injective⟩)).map
                      (pullbackToSubtypeSupport (Ω := Ω) U)).map
                        (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hLU) =
                    _)
    _ = (P (U.map ⟨Subtype.val, Subtype.val_injective⟩)).map
          (pullbackToSubtypeSupport (Ω := Ω) L ∘
            Finset.restrict₂ (π := fun i : I ↦ Ω i) (mapSubtypeVal_subset hLU)) := by
              refine Measure.map_congr <| Filter.Eventually.of_forall fun x ↦ ?_
              exact (congrFun
                (pullbackToSubtypeSupport_comp_restrict₂ (Ω := Ω) hLU) x).symm
    _ = ((P (U.map ⟨Subtype.val, Subtype.val_injective⟩)).map
          (Finset.restrict₂ (π := fun i : I ↦ Ω i) (mapSubtypeVal_subset hLU))).map
            (pullbackToSubtypeSupport (Ω := Ω) L) := by
            simpa using
              (Measure.map_map
                (measurable_pullbackToSubtypeSupport (Ω := Ω) L)
                (Finset.measurable_restrict₂ (mapSubtypeVal_subset hLU)) :
                  ((P (U.map ⟨Subtype.val, Subtype.val_injective⟩)).map
                    (Finset.restrict₂ (π := fun i : I ↦ Ω i) (mapSubtypeVal_subset hLU))).map
                      (pullbackToSubtypeSupport (Ω := Ω) L) =
                  _).symm
    _ = Psub L := by
          simpa [Psub] using congrArg
            (fun ν : Measure ((i : L.map ⟨Subtype.val, Subtype.val_injective⟩) → Ω i) ↦
              ν.map (pullbackToSubtypeSupport (Ω := Ω) L))
            (hP (U.map ⟨Subtype.val, Subtype.val_injective⟩)
              (L.map ⟨Subtype.val, Subtype.val_injective⟩) (mapSubtypeVal_subset hLU)).symm

/-- Helper for Theorem 14.36: the ordered-prefix reindexing commutes with successor-prefix
restriction on the subtype supports. -/
lemma frestrictLe₂_prefixSupportMeasurableEquiv_succ
    {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    Preorder.frestrictLe₂ (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n) ∘
        prefixSupportMeasurableEquiv (Ω := Ω) e (n + 1) =
      prefixSupportMeasurableEquiv (Ω := Ω) e n ∘
        Finset.restrict₂ (π := fun j : J ↦ Ω j.1) (prefixSupport_mono e n) := by
  -- Proof comment: both sides reindex the same successor-prefix tuple and then delete the last
  -- coordinate, so they agree pointwise on every `i : Iic n`.
  funext x
  funext i
  rfl

/-- Helper for Theorem 14.36: the ordered prefix marginals built from the subtype companion
family satisfy the successor restriction identity needed for the countable route. -/
lemma countablePrefixOrderedMeasure_map_frestrictLe
    (P : ∀ K : Finset I, Measure ((k : K) → Ω k))
    (hP : IsProjectiveMeasureFamily P) {J : Set I} (e : ℕ ≃ J) (n : ℕ) :
    let Psub : ∀ L : Finset J, Measure ((l : L) → Ω l.1) :=
      fun L ↦
        show Measure ((l : L) → Ω l.1) from
          (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
            (pullbackToSubtypeSupport (Ω := Ω) L)
    let μsub : (m : ℕ) → Measure ((j : prefixSupport e m) → Ω j.1) :=
      fun m ↦ Psub (prefixSupport e m)
    let μord : (m : ℕ) → Measure ((i : Finset.Iic m) → Ω ((e i).1)) :=
      fun m ↦ (μsub m).map (prefixSupportMeasurableEquiv (Ω := Ω) e m)
    (μord (n + 1)).map
        (Preorder.frestrictLe₂ (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n)) = μord n := by
  let Psub : ∀ L : Finset J, Measure ((l : L) → Ω l.1) :=
    fun L ↦
      show Measure ((l : L) → Ω l.1) from
        (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
          (pullbackToSubtypeSupport (Ω := Ω) L)
  let μsub : (m : ℕ) → Measure ((j : prefixSupport e m) → Ω j.1) :=
    fun m ↦ Psub (prefixSupport e m)
  let μord : (m : ℕ) → Measure ((i : Finset.Iic m) → Ω ((e i).1)) :=
    fun m ↦ (μsub m).map (prefixSupportMeasurableEquiv (Ω := Ω) e m)
  have hPsub :
      IsProjectiveMeasureFamily (α := fun j : J ↦ Ω j.1) Psub :=
    subtypeProjectiveFamily_of_ambientProjective (Ω := Ω) P hP
  have hprefix :
      μsub n = (μsub (n + 1)).map
        (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) (prefixSupport_mono e n)) := by
    simpa [μsub] using
      hPsub (prefixSupport e (n + 1)) (prefixSupport e n) (prefixSupport_mono e n)
  -- Proof comment: commute the ordered-prefix reindexing with successor restriction and then
  -- apply projectivity of the subtype companion family on the prefix supports.
  calc
    (μord (n + 1)).map
        (Preorder.frestrictLe₂ (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n))
        = (μsub (n + 1)).map
            (Preorder.frestrictLe₂ (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n) ∘
              prefixSupportMeasurableEquiv (Ω := Ω) e (n + 1)) := by
                simpa [μord] using
                  (Measure.map_map
                    (Preorder.measurable_frestrictLe₂ (X := fun i : ℕ ↦ Ω ((e i).1))
                      (Nat.le_succ n))
                    (prefixSupportMeasurableEquiv (Ω := Ω) e (n + 1)).measurable :
                      ((μsub (n + 1)).map
                        (prefixSupportMeasurableEquiv (Ω := Ω) e (n + 1))).map
                          (Preorder.frestrictLe₂
                            (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n)) =
                        _)
    _ = (μsub (n + 1)).map
          (prefixSupportMeasurableEquiv (Ω := Ω) e n ∘
            Finset.restrict₂ (π := fun j : J ↦ Ω j.1) (prefixSupport_mono e n)) := by
              refine Measure.map_congr <| Filter.Eventually.of_forall fun x ↦ ?_
              exact congrFun
                (frestrictLe₂_prefixSupportMeasurableEquiv_succ (Ω := Ω) e n) x
    _ = ((μsub (n + 1)).map
          (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) (prefixSupport_mono e n))).map
          (prefixSupportMeasurableEquiv (Ω := Ω) e n) := by
            simpa using
              (Measure.map_map
                (prefixSupportMeasurableEquiv (Ω := Ω) e n).measurable
                (Finset.measurable_restrict₂ (X := fun j : J ↦ Ω j.1) (prefixSupport_mono e n)) :
                  ((μsub (n + 1)).map
                    (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) (prefixSupport_mono e n))).map
                    (prefixSupportMeasurableEquiv (Ω := Ω) e n) =
                  _).symm
    _ = (μsub n).map (prefixSupportMeasurableEquiv (Ω := Ω) e n) := by
          rw [← hprefix]
    _ = μord n := by
          rfl

/-- Helper for Theorem 14.36: split an ordered successor history into its prefix and last
coordinate. -/
noncomputable def orderedSuccHistoryMeasurableEquiv
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    ((i : Finset.Iic (n + 1)) → X i) ≃ᵐ (((i : Finset.Iic n) → X i) × X (n + 1)) :=
  (MeasurableEquiv.IicProdIoc (X := X) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := X) n).symm)

/-- Helper for Theorem 14.36: the successor-history split records the prefix tuple together with
the last coordinate. -/
@[simp] lemma orderedSuccHistoryMeasurableEquiv_apply
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] (n : ℕ)
    (z : (i : Finset.Iic (n + 1)) → X i) :
    orderedSuccHistoryMeasurableEquiv (X := X) n z =
      (Preorder.frestrictLe₂ (π := X) (Nat.le_succ n) z,
        z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: this is the explicit normal form used to compare prefix marginals.
  rfl

/-- Helper for Theorem 14.36: reversing the successor-history split glues the prefix together with
the singleton tail coordinate. -/
@[simp] lemma orderedSuccHistoryMeasurableEquiv_symm_apply
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] (n : ℕ)
    (z : ((i : Finset.Iic n) → X i) × X (n + 1)) :
    (orderedSuccHistoryMeasurableEquiv (X := X) n).symm z =
      _root_.IicProdIoc (X := X) n (n + 1)
        (z.1, (MeasurableEquiv.piSingleton (X := X) n) z.2) := by
  -- Proof comment: the inverse map first inserts the tail as a singleton family and then glues
  -- it to the prefix via `IicProdIoc`.
  rfl

/-- Helper for Theorem 14.36: after splitting the successor law into `(prefix, last)`, its first
marginal is the prescribed prefix law. -/
lemma orderedSuccPairFst_eq_prefix
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (muOrd : (n : ℕ) → Measure ((i : Finset.Iic n) → X i))
    (hCompat : ∀ n,
      (muOrd (n + 1)).map (Preorder.frestrictLe₂ (π := X) (Nat.le_succ n)) = muOrd n)
    (n : ℕ) :
    ((muOrd (n + 1)).map (orderedSuccHistoryMeasurableEquiv (X := X) n)).fst = muOrd n := by
  have hcomp :
      Prod.fst ∘ orderedSuccHistoryMeasurableEquiv (X := X) n =
        Preorder.frestrictLe₂ (π := X) (Nat.le_succ n) := by
    funext z
    simp [Function.comp, orderedSuccHistoryMeasurableEquiv_apply]
  -- Proof comment: the first projection of the split successor law is exactly the stored prefix
  -- restriction, so compatibility gives the desired marginal identity.
  rw [Measure.fst, Measure.map_map measurable_fst
    (orderedSuccHistoryMeasurableEquiv (X := X) n).measurable, hcomp, hCompat n]

/-- Helper for Theorem 14.36: every coordinate space `X n` is nonempty because the ordered prefix
law on `Iic n` is a probability measure. -/
lemma orderedCoordinateNonempty
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (muOrd : (n : ℕ) → Measure ((i : Finset.Iic n) → X i))
    [∀ n, IsProbabilityMeasure (muOrd n)] (n : ℕ) : Nonempty (X n) := by
  by_contra hn
  haveI : IsEmpty (X n) := not_nonempty_iff.mp hn
  let _ : IsEmpty ((i : Finset.Iic n) → X i) := by
    refine ⟨fun x ↦ ?_⟩
    exact isEmptyElim (x ⟨n, Finset.mem_Iic.2 le_rfl⟩)
  have hzero : muOrd n = 0 := by
    simpa using (Measure.eq_zero_of_isEmpty (μ := muOrd n))
  have huniv : muOrd n Set.univ = 1 := by
    simp
  rw [hzero] at huniv
  simp at huniv

/-- Helper for Theorem 14.36: a compatible sequence of ordered prefix marginals on `ℕ` has a
projective limit on the full countable product. -/
lemma existsSequenceProjectiveLimitOfPrefixCompatible
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (muOrd : (n : ℕ) → Measure ((i : Finset.Iic n) → X i))
    [∀ n, IsProbabilityMeasure (muOrd n)]
    (hCompat : ∀ n,
      (muOrd (n + 1)).map (Preorder.frestrictLe₂ (π := X) (Nat.le_succ n)) = muOrd n) :
    ∃ muInf : Measure ((n : ℕ) → X n), ∀ n, muInf.map (Preorder.frestrictLe n) = muOrd n := by
  letI : ∀ n, Nonempty (X n) := fun n ↦ orderedCoordinateNonempty (muOrd := muOrd) n
  let μ0 : Measure (X 0) :=
    (muOrd 0).map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i))
  let ρ : (n : ℕ) → Measure (((i : Finset.Iic n) → X i) × X (n + 1)) :=
    fun n ↦ (muOrd (n + 1)).map (orderedSuccHistoryMeasurableEquiv (X := X) n)
  let κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1)) :=
    fun n ↦ (ρ n).condKernel
  haveI : IsProbabilityMeasure μ0 := by
    -- Proof comment: the initial law is a measurable pushforward of the probability measure
    -- `muOrd 0`, so it is again a probability measure.
    exact Measure.isProbabilityMeasure_map
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable.aemeasurable)
  haveI : ∀ n, IsMarkovKernel (κ n) := fun n ↦ by
    dsimp [κ]
    infer_instance
  have hμ0 :
      μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm = muOrd 0 := by
    -- Proof comment: the initial one-coordinate law is defined by transporting `muOrd 0` through
    -- the unique-index measurable equivalence, so mapping back recovers the original measure.
    calc
      μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm
          = (muOrd 0).map
              ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm ∘
                (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i))) := by
                  simpa [μ0] using
                    (Measure.map_map
                      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm.measurable)
                      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable
                      (μ := muOrd 0))
      _ = (muOrd 0).map id := by
            congr
            funext x
            exact (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm_apply_apply x
      _ = muOrd 0 := by
            rw [Measure.map_id]
  have hstep :
      ∀ n, ProbabilityTheory.Kernel.partialTraj κ n (n + 1) ∘ₘ muOrd n = muOrd (n + 1) := by
    intro n
    have hcompProd :
        muOrd n ⊗ₘ κ n = ρ n := by
      -- Proof comment: disintegrate the split successor law `ρ n`; its first marginal is `muOrd n`
      -- by compatibility, so the composition-product form is exactly `muOrd n ⊗ₘ κ n`.
      rw [← orderedSuccPairFst_eq_prefix (muOrd := muOrd) hCompat n]
      simpa [κ] using (ρ n).disintegrate ((ρ n).condKernel)
    have hcompose :
        _root_.IicProdIoc (X := X) n (n + 1) ∘
            Prod.map id (MeasurableEquiv.piSingleton (X := X) n) =
          (orderedSuccHistoryMeasurableEquiv (X := X) n).symm := by
      funext z
      cases z
      rfl
    -- Proof comment: rewrite the one-step partial trajectory as the split composition-product,
    -- then collapse it back to the original successor law using disintegration of `ρ n`.
    calc
      ProbabilityTheory.Kernel.partialTraj κ n (n + 1) ∘ₘ muOrd n
          = (((Kernel.id ×ₖ ((κ n).map (MeasurableEquiv.piSingleton (X := X) n))).map
                (_root_.IicProdIoc (X := X) n (n + 1))) ∘ₘ muOrd n) := by
              rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
      _ = (((Kernel.id ×ₖ ((κ n).map (MeasurableEquiv.piSingleton (X := X) n))) ∘ₘ
            muOrd n)).map (_root_.IicProdIoc (X := X) n (n + 1)) := by
              rw [← Measure.map_comp (μ := muOrd n)
                (κ := Kernel.id ×ₖ ((κ n).map (MeasurableEquiv.piSingleton (X := X) n)))
                measurable_IicProdIoc]
      _ = (muOrd n ⊗ₘ (κ n).map (MeasurableEquiv.piSingleton (X := X) n)).map
            (_root_.IicProdIoc (X := X) n (n + 1)) := by
              rw [← Measure.compProd_eq_comp_prod]
      _ = ((muOrd n ⊗ₘ κ n).map
            (Prod.map id (MeasurableEquiv.piSingleton (X := X) n))).map
            (_root_.IicProdIoc (X := X) n (n + 1)) := by
              rw [Measure.compProd_map (μ := muOrd n) (κ := κ n)
                (MeasurableEquiv.piSingleton (X := X) n).measurable]
      _ = (muOrd n ⊗ₘ κ n).map ((orderedSuccHistoryMeasurableEquiv (X := X) n).symm) := by
            rw [Measure.map_map measurable_IicProdIoc
              (measurable_id.prodMap
                (MeasurableEquiv.piSingleton (X := X) n).measurable)]
            exact congrArg (fun f ↦ (muOrd n ⊗ₘ κ n).map f) hcompose
      _ = (ρ n).map ((orderedSuccHistoryMeasurableEquiv (X := X) n).symm) := by
            rw [hcompProd]
      _ = muOrd (n + 1) := by
            simpa [ρ] using
              (Measure.map_map
                ((orderedSuccHistoryMeasurableEquiv (X := X) n).symm.measurable)
                (orderedSuccHistoryMeasurableEquiv (X := X) n).measurable
                (μ := muOrd (n + 1)))
  have hpartial :
      ∀ n,
        ProbabilityTheory.Kernel.partialTraj κ 0 n ∘ₘ
          μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm = muOrd n := by
    intro n
    induction n with
    | zero =>
        -- Proof comment: at level `0`, `partialTraj` is the identity kernel, so the claim is
        -- exactly the normalization of the transported initial law.
        rw [ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
        exact hμ0
    | succ n ih =>
        -- Proof comment: factor the successor finite-dimensional law through the one-step
        -- extension at level `n`, then use the already identified one-step measure `hstep n`.
        calc
          ProbabilityTheory.Kernel.partialTraj κ 0 (n + 1) ∘ₘ
              μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm
              = (ProbabilityTheory.Kernel.partialTraj κ n (n + 1) ∘ₖ
                  ProbabilityTheory.Kernel.partialTraj κ 0 n) ∘ₘ
                    μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm := by
                      rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp (κ := κ)
                        (Nat.zero_le n)]
          _ = ProbabilityTheory.Kernel.partialTraj κ n (n + 1) ∘ₘ
                (ProbabilityTheory.Kernel.partialTraj κ 0 n ∘ₘ
                  μ0.map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).symm) := by
                    rw [Measure.comp_assoc]
          _ = ProbabilityTheory.Kernel.partialTraj κ n (n + 1) ∘ₘ muOrd n := by
                rw [ih]
          _ = muOrd (n + 1) := hstep n
  rcases
      ProbabilityTheory.Kernel.existsUnique_probability_measure_with_prescribed_finite_dimensional_marginals
        (X := X) (μ₀ := μ0) (κ := κ) with ⟨muInf, hmuInf, _⟩
  refine ⟨muInf, ?_⟩
  intro n
  exact (hmuInf.2 n).trans (hpartial n)

/-- Helper for Theorem 14.36: every finite subsystem of a countable support is contained in a
sufficiently long enumerated prefix support. -/
lemma subset_prefixSupport_sup_image_symm
    {J : Set I} (e : ℕ ≃ J) (L : Finset J) :
    L ⊆ prefixSupport e ((L.image e.symm).sup (fun m : ℕ ↦ m)) := by
  intro j hj
  -- Proof comment: the index `e.symm j` appears in the image `L.image e.symm`, so the supremum
  -- of that finite set yields a prefix support large enough to contain `j`.
  have hmem : e.symm j ∈ L.image (fun k : J ↦ e.symm k) := by
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  exact Finset.mem_map.2
    ⟨⟨e.symm j, Finset.mem_Iic.2 <| by
        simpa using
          (show e.symm j ≤ (L.image (fun k : J ↦ e.symm k)).sup id from
            Finset.le_sup (f := id) hmem)⟩,
      Finset.mem_univ _, by simpa using e.apply_symm_apply j⟩

/-- Helper for Theorem 14.36: if every countable support carries an ambient owner, then those
owners glue to a global projective limit on the full product space. -/
lemma globalProjectiveLimitOfCountableOwners
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hOwner : ∀ J : Set I, J.Countable →
      ∃ ν : Measure ((i : I) → Ω i), IsCountableAmbientOwner (Ω := Ω) P J ν) :
    ∃ μ : Measure ((i : I) → Ω i), IsProjectiveLimit μ P := by
  classical
  let owner : ∀ J : Set I, J.Countable → Measure ((i : I) → Ω i) :=
    fun J hJ ↦ Classical.choose (hOwner J hJ)
  have howner :
      ∀ J : Set I, ∀ hJ : J.Countable, IsCountableAmbientOwner (Ω := Ω) P J (owner J hJ) := by
    intro J hJ
    exact Classical.choose_spec (hOwner J hJ)
  have owner_eq_of_measurableSupport :
      ∀ {A : Set ((i : I) → Ω i)} {J U : Set I} (hJ : J.Countable) (hU : U.Countable),
        MeasurableSet[cylinderEvents J] A → MeasurableSet[cylinderEvents U] A →
          owner J hJ A = owner U hU A := by
    intro A J U hJ hU hAJ hAU
    let W : Set I := J ∪ U
    have hJW : J ⊆ W := by
      intro i hi
      exact Or.inl hi
    have hUW : U ⊆ W := by
      intro i hi
      exact Or.inr hi
    have hW : W.Countable := hJ.union hU
    have hAWJ : MeasurableSet[cylinderEvents W] A :=
      cylinderEvents_mono hJW A hAJ
    have hAWU : MeasurableSet[cylinderEvents W] A :=
      cylinderEvents_mono hUW A hAU
    calc
      owner J hJ A = owner W hW A := by
        exact (howner J hJ).eq_on_cylinderEvents_of_subset hJW (howner W hW) hAJ
      _ = owner U hU A := by
        symm
        exact (howner U hU).eq_on_cylinderEvents_of_subset hUW (howner W hW) hAU
  let m : (A : Set ((i : I) → Ω i)) → MeasurableSet A → ENNReal :=
    fun A hA ↦
      let data : Set I :=
        Classical.choose (measurableSet_iff_exists_countable_cylinderEvents.mp hA)
      let hdata : data.Countable ∧ MeasurableSet[cylinderEvents data] A :=
        Classical.choose_spec (measurableSet_iff_exists_countable_cylinderEvents.mp hA)
      owner data hdata.1 A
  have hm_eq_owner :
      ∀ {A : Set ((i : I) → Ω i)} (hA : MeasurableSet A) {J : Set I} (hJ : J.Countable),
        MeasurableSet[cylinderEvents J] A → m A hA = owner J hJ A := by
    intro A hA J hJ hAJ
    let data : Set I := Classical.choose (measurableSet_iff_exists_countable_cylinderEvents.mp hA)
    let hdata :
        data.Countable ∧ MeasurableSet[cylinderEvents data] A :=
      Classical.choose_spec (measurableSet_iff_exists_countable_cylinderEvents.mp hA)
    simpa [m, data, hdata] using
      (owner_eq_of_measurableSupport (J := data) (U := J) (hdata.left) hJ (hdata.right) hAJ)
  have hm0 : m ∅ MeasurableSet.empty = 0 := by
    -- Proof comment: evaluate the glued set function on the empty countable support.
    let hEmpty : (∅ : Set I).Countable := by simp
    have hEmptyMeas : MeasurableSet[cylinderEvents (∅ : Set I)] (∅ : Set ((i : I) → Ω i)) := by
      simp
    rw [hm_eq_owner MeasurableSet.empty hEmpty hEmptyMeas]
    simp
  have hmU :
      ∀ ⦃f : ℕ → Set ((i : I) → Ω i)⦄ (hf : ∀ i, MeasurableSet (f i)),
        Pairwise (fun i j ↦ Disjoint (f i) (f j)) →
          m (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, m (f i) (hf i) := by
    intro f hf hDisj
    have hCountableSupport :
        ∀ n, ∃ J : Set I, J.Countable ∧ MeasurableSet[cylinderEvents J] (f n) := by
      intro n
      exact measurableSet_iff_exists_countable_cylinderEvents.mp (hf n)
    rcases exists_countable_cylinderSupport_forall (Ω := Ω) f hCountableSupport with
      ⟨J, hJ, hJmeas⟩
    calc
      m (⋃ n, f n) (MeasurableSet.iUnion hf) = owner J hJ (⋃ n, f n) := by
        exact hm_eq_owner (MeasurableSet.iUnion hf) hJ (MeasurableSet.iUnion hJmeas)
      _ = ∑' n, owner J hJ (f n) := by
        simpa using (MeasureTheory.measure_iUnion (μ := owner J hJ) hDisj hf)
      _ = ∑' n, m (f n) (hf n) := by
        congr with n
        symm
        exact hm_eq_owner (hf n) hJ (hJmeas n)
  refine ⟨Measure.ofMeasurable m hm0 hmU, ?_⟩
  intro K
  ext S hS
  have hCylinder :
      MeasurableSet (cylinder K S) :=
    MeasurableSet.of_mem_measurableCylinders (cylinder_mem_measurableCylinders K S hS)
  have hCylinderSupport :
      MeasurableSet[cylinderEvents (X := Ω) (K : Set I)] (cylinder K S) :=
    measurableSet_cylinderEvents_cylinder (Ω := Ω) K hS
  have hKCountable : ((K : Set I)).Countable := K.countable_toSet
  -- Proof comment: the glued measure agrees with the owner on the finite support `K`, so its
  -- finite marginal on the cylinder is exactly the prescribed measure `P K`.
  rw [Measure.map_apply (Finset.measurable_restrict K) hS]
  calc
    (Measure.ofMeasurable m hm0 hmU) (K.restrict ⁻¹' S) = m (cylinder K S) hCylinder := by
      simpa [MeasureTheory.cylinder] using
        (Measure.ofMeasurable_apply (m := m) (m0 := hm0) (mU := hmU) (cylinder K S) hCylinder)
    _ = owner (K : Set I) hKCountable (cylinder K S) := by
      exact hm_eq_owner hCylinder hKCountable hCylinderSupport
    _ = P K S := by
      simpa using (howner (K : Set I) hKCountable).measure_cylinder (by intro i hi; simpa using hi)
        hS

/-- Helper for Theorem 14.36: every countable subsystem carries an ambient owner. The finite case
comes directly from the prescribed marginal, while the infinite countable case is reduced to the
`ℕ`-indexed projective limit from `existsSequenceProjectiveLimitOfPrefixCompatible`. -/
lemma existsCountableAmbientOwner
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (J : Set I) (hJ : J.Countable) :
    ∃ ν : Measure ((i : I) → Ω i), IsCountableAmbientOwner (Ω := Ω) P J ν := by
  classical
  by_cases hFinite : J.Finite
  · -- Proof comment: the finite-support case is immediate from the single prescribed marginal on
    -- that finite support.
    exact existsFiniteAmbientOwner (Ω := Ω) P hP hFinite
  · -- Route correction: only the infinite countable case still needs the countable-core theorem on
    -- the subsystem product indexed by `J`; the countable-core existence theorem is now available,
    -- so the only remaining work is the transport from the `ℕ`-indexed limit back to finite
    -- subtype marginals and then to the ambient extension on `I`.
    letI : ∀ i, Nonempty (Ω i) := fun i ↦ coordinateNonempty (Ω := Ω) P i
    haveI : Countable J := hJ.to_subtype
    have hJInfinite : J.Infinite := by
      simpa using hFinite
    letI : Infinite J := Set.infinite_coe_iff.mpr hJInfinite
    let e : ℕ ≃ J := Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := J))
    let Psub : ∀ L : Finset J, Measure ((l : L) → Ω l.1) :=
      fun L ↦
        show Measure ((l : L) → Ω l.1) from
          (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
            (pullbackToSubtypeSupport (Ω := Ω) L)
    haveI : ∀ L : Finset J, IsProbabilityMeasure (Psub L) := fun L ↦ by
      exact Measure.isProbabilityMeasure_map
        ((measurable_pullbackToSubtypeSupport (Ω := Ω) L).aemeasurable)
    let μsub : (m : ℕ) → Measure ((j : prefixSupport e m) → Ω j.1) :=
      fun m ↦ Psub (prefixSupport e m)
    haveI : ∀ m, IsProbabilityMeasure (μsub m) := fun m ↦ by
      dsimp [μsub]
      infer_instance
    let μord : (m : ℕ) → Measure ((i : Finset.Iic m) → Ω ((e i).1)) :=
      fun m ↦ (μsub m).map (prefixSupportMeasurableEquiv (Ω := Ω) e m)
    haveI : ∀ m, IsProbabilityMeasure (μord m) := fun m ↦ by
      exact Measure.isProbabilityMeasure_map
        ((prefixSupportMeasurableEquiv (Ω := Ω) e m).measurable.aemeasurable)
    have hμordCompat :
        ∀ n,
          (μord (n + 1)).map
              (Preorder.frestrictLe₂ (π := fun i : ℕ ↦ Ω ((e i).1)) (Nat.le_succ n)) =
            μord n := by
      intro n
      simpa [μsub, μord, Psub] using
        countablePrefixOrderedMeasure_map_frestrictLe (Ω := Ω) P hP e n
    rcases
        existsSequenceProjectiveLimitOfPrefixCompatible
          (X := fun n : ℕ ↦ Ω ((e n).1)) μord hμordCompat with ⟨muInf, hmuInf⟩
    let μJ : Measure ((j : J) → Ω j.1) :=
      muInf.map (countableProductMeasurableEquiv (Ω := Ω) e).symm
    have hPsub :
        IsProjectiveMeasureFamily (α := fun j : J ↦ Ω j.1) Psub :=
      subtypeProjectiveFamily_of_ambientProjective (Ω := Ω) P hP
    have hμJPrefix :
        ∀ n, μJ.map ((prefixSupport e n).restrict) = Psub (prefixSupport e n) := by
      intro n
      -- Proof comment: rewrite the subtype-prefix marginal of `μJ` through the `ℕ`-indexed limit
      -- `muInf`, use the bridge lemma to normalize the transport, and then map back across the
      -- prefix-support measurable equivalence.
      calc
        μJ.map ((prefixSupport e n).restrict)
            = muInf.map
                ((prefixSupport e n).restrict ∘
                  (countableProductMeasurableEquiv (Ω := Ω) e).symm) := by
                simpa [μJ] using
                  (Measure.map_map
                    (Finset.measurable_restrict (prefixSupport e n))
                    ((countableProductMeasurableEquiv (Ω := Ω) e).symm.measurable)
                    (μ := muInf))
        _ = muInf.map
              ((prefixSupportMeasurableEquiv (Ω := Ω) e n).symm ∘
                Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n) := by
              rw [prefixSupportRestrict_comp_countableProductMeasurableEquiv_symm (Ω := Ω) e n]
        _ = (muInf.map (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) n)).map
              (prefixSupportMeasurableEquiv (Ω := Ω) e n).symm := by
              symm
              simpa using
                (Measure.map_map
                  ((prefixSupportMeasurableEquiv (Ω := Ω) e n).symm.measurable)
                  (Preorder.measurable_frestrictLe (X := fun i : ℕ ↦ Ω ((e i).1)) n)
                  (μ := muInf))
        _ = (μord n).map (prefixSupportMeasurableEquiv (Ω := Ω) e n).symm := by
              rw [hmuInf n]
        _ = μsub n := by
              simpa [μord] using
                (Measure.map_map
                  ((prefixSupportMeasurableEquiv (Ω := Ω) e n).symm.measurable)
                  ((prefixSupportMeasurableEquiv (Ω := Ω) e n).measurable)
                  (μ := μsub n))
        _ = Psub (prefixSupport e n) := by
              rfl
    have hμJFinite :
        ∀ L : Finset J, μJ.map L.restrict = Psub L := by
      intro L
      let n : ℕ := (L.image e.symm).sup (fun m : ℕ ↦ m)
      have hL : L ⊆ prefixSupport e n := by
        simpa [n] using subset_prefixSupport_sup_image_symm e L
      let rPrefix : ((j : J) → Ω j.1) → ((j : prefixSupport e n) → Ω j.1) :=
        (prefixSupport e n).restrict
      let rL : ((j : J) → Ω j.1) → ((l : L) → Ω l.1) := L.restrict
      have hrestrict :
          Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hL ∘
              rPrefix =
            rL := by
        funext x
        funext l
        rfl
      -- Proof comment: enlarge `L` to a long enough enumerated prefix, apply the prefix marginal
      -- identity there, and then descend back to `L` by projectivity of `Psub`.
      calc
        μJ.map rL
            = (μJ.map rPrefix).map
                (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hL) := by
                  symm
                  calc
                    (μJ.map rPrefix).map
                        (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hL)
                        = μJ.map
                            (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hL ∘
                              rPrefix) := by
                                simpa using
                                  (Measure.map_map
                                    (Finset.measurable_restrict₂
                                      (X := fun j : J ↦ Ω j.1) hL)
                                    (Finset.measurable_restrict (prefixSupport e n))
                                    (μ := μJ))
                    _ = μJ.map rL := by
                          exact congrArg (fun f ↦ μJ.map f) hrestrict
        _ = (Psub (prefixSupport e n)).map
              (Finset.restrict₂ (π := fun j : J ↦ Ω j.1) hL) := by
              rw [hμJPrefix n]
        _ = Psub L := by
              symm
              exact hPsub (prefixSupport e n) L hL
    haveI : IsProbabilityMeasure muInf := by
      refine ⟨?_⟩
      have hmuInf0 :
          (muInf.map (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) 0)) Set.univ = 1 := by
        calc
          (muInf.map (Preorder.frestrictLe (π := fun i : ℕ ↦ Ω ((e i).1)) 0)) Set.univ
              = (μord 0) Set.univ := by
                  exact congrArg
                    (fun ν : Measure ((i : Finset.Iic 0) → Ω ((e i).1)) ↦ ν Set.univ)
                    (hmuInf 0)
          _ = 1 := by
                simp
      rw [Measure.map_apply
        (Preorder.measurable_frestrictLe (X := fun i : ℕ ↦ Ω ((e i).1)) 0)
        MeasurableSet.univ, Set.preimage_univ] at hmuInf0
      simpa using hmuInf0
    haveI : IsProbabilityMeasure μJ :=
      Measure.isProbabilityMeasure_map
        (((countableProductMeasurableEquiv (Ω := Ω) e).symm.measurable).aemeasurable)
    let ν : Measure ((i : I) → Ω i) :=
      μJ.map (extendCoordinates (Ω := Ω) J)
    refine ⟨ν, ⟨?_, ?_⟩⟩
    · exact Measure.isProbabilityMeasure_map
        ((measurable_extendCoordinates (Ω := Ω) J).aemeasurable)
    · intro K hK
      let L : Finset J := K.preimage Subtype.val Subtype.val_injective.injOn
      have hLmapK : L.map ⟨Subtype.val, Subtype.val_injective⟩ = K := by
        apply Finset.ext
        intro i
        constructor
        · intro hi
          rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
          exact Finset.mem_preimage.1 hj
        · intro hi
          refine Finset.mem_map.2 ?_
          refine ⟨⟨i, hK hi⟩, ?_, rfl⟩
          exact Finset.mem_preimage.2 hi
      have htransport :
          finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L ∘
              (L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1)) =
            (L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict ∘
              extendCoordinates (Ω := Ω) J := by
        exact finiteSubtypeSupportMeasurableEquiv_comp_restrict_extendCoordinates
          (Ω := Ω) L
      have hpull :
          pullbackToSubtypeSupport (Ω := Ω) L =
            (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).symm := by
        funext x
        funext l
        symm
        exact finiteSubtypeSupportMeasurableEquiv_symm_apply (Ω := Ω) L x l
      -- Proof comment: lift the ambient finite support `K` to the subtype support `L`, identify
      -- the ambient restriction of `ν` with the transported subtype restriction of `μJ`, and then
      -- cancel the finite-support measurable equivalence against its inverse in the definition of
      -- `Psub L`.
      rw [← hLmapK]
      calc
        ν.map (L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict
            = ((μJ.map
                (L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1))).map
                  (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L)) := by
                calc
                  ν.map (L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict
                      = μJ.map
                          ((L.map ⟨Subtype.val, Subtype.val_injective⟩).restrict ∘
                            extendCoordinates (Ω := Ω) J) := by
                              simpa [ν] using
                                (Measure.map_map
                                  (Finset.measurable_restrict
                                    (L.map ⟨Subtype.val, Subtype.val_injective⟩))
                                  (measurable_extendCoordinates (Ω := Ω) J)
                                  (μ := μJ))
                  _ = μJ.map
                        (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L ∘
                          (L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1))) := by
                        exact congrArg (fun f ↦ μJ.map f) htransport.symm
                  _ = ((μJ.map
                          (L.restrict : ((j : J) → Ω j.1) → ((l : L) → Ω l.1))).map
                            (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L)) := by
                        symm
                        simpa using
                          (Measure.map_map
                            (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).measurable
                            (Finset.measurable_restrict (X := fun j : J ↦ Ω j.1) L)
                            (μ := μJ))
        _ = (Psub L).map (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L) := by
              rw [hμJFinite L]
        _ = (((P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
              (pullbackToSubtypeSupport (Ω := Ω) L)).map
              (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L)) := by
                rfl
        _ = ((P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
              (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).symm).map
              (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L) := by
                rw [hpull]
        _ = (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map
              (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L ∘
                (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).symm) := by
                rw [Measure.map_map
                  (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).measurable
                  ((finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).symm.measurable)]
        _ = (P (L.map ⟨Subtype.val, Subtype.val_injective⟩)).map id := by
              congr
              funext x
              exact (finiteSubtypeSupportMeasurableEquiv (Ω := Ω) L).apply_symm_apply x
        _ = P (L.map ⟨Subtype.val, Subtype.val_injective⟩) := by
              rw [Measure.map_id]

/-- Theorem 14.36: a projective family of finite-dimensional probability measures admits a
projective limit on the full product space. -/
theorem exists_projectiveLimit_of_isProjectiveMeasureFamily
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure ((i : I) → Ω i), IsProjectiveLimit μ P := by
  -- Route correction: the main theorem now only needs the countable-support owner theorem, because
  -- the gluing step has been isolated into `globalProjectiveLimitOfCountableOwners`.
  exact globalProjectiveLimitOfCountableOwners (Ω := Ω) P
    (fun J hJ ↦ existsCountableAmbientOwner (Ω := Ω) (P := P) hP J hJ)

/-- Theorem 14.36: the projective limit of a projective family of finite-dimensional
probability measures is unique. -/
theorem existsUnique_projectiveLimit_of_isProjectiveMeasureFamily
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j))
    [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃! μ : Measure ((i : I) → Ω i), IsProjectiveLimit μ P := by
  rcases exists_projectiveLimit_of_isProjectiveMeasureFamily (P := P) hP with ⟨μ, hμ⟩
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact (IsProjectiveLimit.unique hμ hν).symm

end
