/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.section05_part1

section Chap07
section Section05

/-- Real-valued version of the textbook Lebesgue measurability predicate on a subset `Ω ⊆ ℝ^n`. -/
def IsLebesgueMeasurableScalarFunction (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (g : Ω → ℝ) : Prop :=
  MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ V : Set ℝ, IsOpen V →
      ∃ E : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet E
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
          Subtype.val '' (g ⁻¹' V) = Ω ∩ E

/-- Helper for Theorem 7.3: every coordinate of a Lebesgue measurable vector map is
Lebesgue measurable as a scalar map. -/
lemma helperForTheorem_7_3_coordinateFunctions_of_isLebesgueMeasurableFunction
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hf : IsLebesgueMeasurableFunction n m Ω f) :
    ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  intro j
  refine ⟨hf.1, ?_⟩
  intro V hV
  let W : Set (EuclideanSpace ℝ (Fin m)) := {x | x j ∈ V}
  have hWOpen : IsOpen W := by
    simpa [W] using hV.preimage (EuclideanSpace.proj j).continuous
  rcases hf.2 W hWOpen with ⟨E, hENull, hEq⟩
  refine ⟨E, hENull, ?_⟩
  simpa [W] using hEq

/-- Helper for Theorem 7.3: in positive codimension, coordinate measurability implies
`Ω` is null measurable. -/
lemma helperForTheorem_7_3_nullMeasurableSet_of_coordinateFunctions
    {n m : ℕ} (hm : 0 < m) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hcoord : ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  exact (hcoord ⟨0, hm⟩).1

/-- Helper for Theorem 7.3: preimages of open coordinate boxes are intersections of
coordinate interval preimages. -/
lemma helperForTheorem_7_3_preimage_openBox_eq_iInter_coordinatePreimages
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (a b : Fin m → ℝ) :
    Subtype.val '' (f ⁻¹' {x : EuclideanSpace ℝ (Fin m) |
      ∀ i : Fin m, a i < x i ∧ x i < b i}) =
      Ω ∩ Set.iInter (fun i : Fin m =>
        Subtype.val '' ((fun x => f x i) ⁻¹' Set.Ioo (a i) (b i))) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨xΩ, hxBox, rfl⟩
    refine ⟨xΩ.2, ?_⟩
    refine (Set.mem_iInter).2 ?_
    intro i
    have hxIoo : f xΩ i ∈ Set.Ioo (a i) (b i) := by
      simpa [Set.mem_Ioo] using hxBox i
    exact ⟨xΩ, hxIoo, rfl⟩
  · intro hx
    rcases hx with ⟨hxΩ, hxCoord⟩
    have hxCoord' :
        ∀ i : Fin m,
          x ∈ Subtype.val '' ((fun x => f x i) ⁻¹' Set.Ioo (a i) (b i)) := by
      exact (Set.mem_iInter).1 hxCoord
    let xΩ : Ω := ⟨x, hxΩ⟩
    refine ⟨xΩ, ?_, rfl⟩
    intro i
    rcases hxCoord' i with ⟨y, hyIoo, hyEq⟩
    have hySubtype : y = xΩ := Subtype.ext hyEq
    have hyIneq : a i < f xΩ i ∧ f xΩ i < b i := by
      simpa [Set.mem_Ioo, hySubtype] using hyIoo
    exact hyIneq

/-- Helper for Theorem 7.3: for `m > 0`, coordinatewise scalar measurability implies
vector-valued measurability. -/
lemma helperForTheorem_7_3_isLebesgueMeasurableFunction_of_coordinateFunctions
    {n m : ℕ} (hm : 0 < m) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hcoord : ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    IsLebesgueMeasurableFunction n m Ω f := by
  have hΩ :
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
    helperForTheorem_7_3_nullMeasurableSet_of_coordinateFunctions hm hcoord
  have hbox :
      ∀ a b : Fin m → ℝ,
        MeasureTheory.NullMeasurableSet
          (Subtype.val '' (f ⁻¹' {x : EuclideanSpace ℝ (Fin m) |
            ∀ i : Fin m, a i < x i ∧ x i < b i}))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a b
    choose E hENull hEEq using
      (fun i : Fin m => (hcoord i).2 (Set.Ioo (a i) (b i)) isOpen_Ioo)
    have hCoordEq :
        Ω ∩ Set.iInter (fun i : Fin m =>
          Subtype.val '' ((fun x => f x i) ⁻¹' Set.Ioo (a i) (b i))) =
          Ω ∩ Set.iInter (fun i : Fin m => E i) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxΩ, hxCoord⟩
        refine ⟨hxΩ, ?_⟩
        refine (Set.mem_iInter).2 ?_
        intro i
        have hxCoord' :
            x ∈ Subtype.val '' ((fun x => f x i) ⁻¹' Set.Ioo (a i) (b i)) :=
          (Set.mem_iInter).1 hxCoord i
        have hxInΩEi : x ∈ Ω ∩ E i := (hEEq i) ▸ hxCoord'
        exact hxInΩEi.2
      · intro hx
        rcases hx with ⟨hxΩ, hxCoord⟩
        refine ⟨hxΩ, ?_⟩
        refine (Set.mem_iInter).2 ?_
        intro i
        have hxCoord' : x ∈ E i := (Set.mem_iInter).1 hxCoord i
        have hxInΩEi : x ∈ Ω ∩ E i := ⟨hxΩ, hxCoord'⟩
        exact (hEEq i).symm ▸ hxInΩEi
    have hInterE :
        MeasureTheory.NullMeasurableSet (Set.iInter (fun i : Fin m => E i))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      MeasureTheory.NullMeasurableSet.iInter hENull
    have hInter :
        MeasureTheory.NullMeasurableSet (Ω ∩ Set.iInter (fun i : Fin m => E i))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      hΩ.inter hInterE
    have hBoxEq :
        Subtype.val '' (f ⁻¹' {x : EuclideanSpace ℝ (Fin m) |
          ∀ i : Fin m, a i < x i ∧ x i < b i}) =
          Ω ∩ Set.iInter (fun i : Fin m => E i) :=
      (helperForTheorem_7_3_preimage_openBox_eq_iInter_coordinatePreimages
        (f := f) a b).trans hCoordEq
    exact hBoxEq ▸ hInter
  exact
    (isLebesgueMeasurableFunction_iff_preimage_openBox_nullMeasurable (Ω := Ω) (f := f) hΩ).2
      hbox

/-- Helper for Theorem 7.3: for positive target dimension, vector measurability is
equivalent to coordinatewise scalar measurability. -/
theorem helperForTheorem_7_3_iff_coordinateFunctions_of_pos
    {n m : ℕ} (hm : 0 < m) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)} :
    IsLebesgueMeasurableFunction n m Ω f ↔
      ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  constructor
  · intro hf
    exact helperForTheorem_7_3_coordinateFunctions_of_isLebesgueMeasurableFunction hf
  · intro hcoord
    exact helperForTheorem_7_3_isLebesgueMeasurableFunction_of_coordinateFunctions hm hcoord

/-- Helper for Theorem 7.3: adding explicit domain null measurability yields the
coordinatewise characterization in all target dimensions, including `m = 0`. -/
theorem helperForTheorem_7_3_iff_coordinateFunctions_with_nullMeasurableSet
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)} :
    IsLebesgueMeasurableFunction n m Ω f ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  constructor
  · intro hf
    exact ⟨hf.1, helperForTheorem_7_3_coordinateFunctions_of_isLebesgueMeasurableFunction hf⟩
  · intro h
    rcases h with ⟨hΩ, hcoord⟩
    by_cases hm : 0 < m
    · exact helperForTheorem_7_3_isLebesgueMeasurableFunction_of_coordinateFunctions hm hcoord
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst hm0
      refine ⟨hΩ, ?_⟩
      intro V _hV
      by_cases h0 : (0 : EuclideanSpace ℝ (Fin 0)) ∈ V
      · refine ⟨Ω, hΩ, ?_⟩
        have hpreimage_univ : f ⁻¹' V = Set.univ := by
          ext x
          constructor
          · intro _hx
            trivial
          · intro _hx
            have hfx : f x = (0 : EuclideanSpace ℝ (Fin 0)) := by
              ext i
              exact Fin.elim0 i
            simpa [hfx] using h0
        have himage_univ : Subtype.val '' (f ⁻¹' V) = Ω := by
          rw [hpreimage_univ]
          ext x
          constructor
          · rintro ⟨xΩ, -, rfl⟩
            exact xΩ.2
          · intro hxΩ
            exact ⟨⟨x, hxΩ⟩, trivial, rfl⟩
        calc
          Subtype.val '' (f ⁻¹' V) = Ω := himage_univ
          _ = Ω ∩ Ω := by simp
      · refine ⟨∅, MeasurableSet.empty.nullMeasurableSet, ?_⟩
        have hpreimage_empty : f ⁻¹' V = ∅ := by
          ext x
          constructor
          · intro hxV
            have hfx : f x = (0 : EuclideanSpace ℝ (Fin 0)) := by
              ext i
              exact Fin.elim0 i
            have hzero : (0 : EuclideanSpace ℝ (Fin 0)) ∈ V := by
              simpa [hfx] using hxV
            exact (h0 hzero).elim
          · intro hxEmpty
            exact False.elim (Set.notMem_empty x hxEmpty)
        calc
          Subtype.val '' (f ⁻¹' V) = ∅ := by
            rw [hpreimage_empty]
            simp
          _ = Ω ∩ ∅ := by simp

/-- Helper for Theorem 7.3: if either `m > 0` or `Ω` is null measurable, then
vector-valued measurability is equivalent to coordinatewise scalar
measurability. -/
theorem isLebesgueMeasurableFunction_iff_coordinateFunctions_of_pos_or_nullMeasurableSet
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)} :
    ((0 < m) ∨
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) →
      (IsLebesgueMeasurableFunction n m Ω f ↔
        ∀ j : Fin m, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) := by
  intro h
  rcases h with hm | hΩ
  · exact helperForTheorem_7_3_iff_coordinateFunctions_of_pos hm
  · constructor
    · intro hf
      exact helperForTheorem_7_3_coordinateFunctions_of_isLebesgueMeasurableFunction hf
    · intro hcoord
      exact
        (helperForTheorem_7_3_iff_coordinateFunctions_with_nullMeasurableSet
          (n := n) (m := m) (Ω := Ω) (f := f)).2 ⟨hΩ, hcoord⟩

/-- Helper for Theorem 7.3: when the codomain has dimension `0`, vector-valued
Lebesgue measurability is equivalent to null measurability of the domain. -/
lemma helperForTheorem_7_3_iff_nullMeasurableSet_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    IsLebesgueMeasurableFunction n 0 Ω f ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa using
    (helperForTheorem_7_3_iff_coordinateFunctions_with_nullMeasurableSet
      (n := n) (m := 0) (Ω := Ω) (f := f))

/-- Helper for Theorem 7.3: when the codomain is `ℝ^0`, the coordinatewise scalar
measurability condition is always satisfied. -/
lemma helperForTheorem_7_3_coordinateFunctions_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  intro j
  exact Fin.elim0 j

/-- Helper for Theorem 7.3: in codimension `0`, the coordinatewise measurability
witness is unique because `Fin 0` is empty. -/
lemma helperForTheorem_7_3_coordinateFunctions_zeroCodomain_subsingleton
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord1 hcoord2 :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    hcoord1 = hcoord2 := by
  funext j
  exact Fin.elim0 j

/-- Helper for Theorem 7.3: when the codomain is `ℝ^0`, the coordinatewise scalar
measurability condition is equivalent to `True`. -/
lemma helperForTheorem_7_3_coordinateFunctions_zeroCodomain_iff_true
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ↔ True := by
  constructor
  · intro _hcoord
    trivial
  · intro _hTrue
    exact helperForTheorem_7_3_coordinateFunctions_zeroCodomain
      (n := n) (Ω := Ω) (f := f)

/-- Helper for Theorem 7.3: in codimension `0`, the theorem's biconditional
reduces to plain vector-valued measurability because the coordinate condition is
vacuous. -/
lemma helperForTheorem_7_3_target_zeroCodomain_iff_isLebesgueMeasurableFunction
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    (IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ↔
      IsLebesgueMeasurableFunction n 0 Ω f := by
  constructor
  · intro hIff
    exact hIff.2
      (helperForTheorem_7_3_coordinateFunctions_zeroCodomain
        (n := n) (Ω := Ω) (f := f))
  · intro hf
    constructor
    · intro _hfMeas
      exact helperForTheorem_7_3_coordinateFunctions_zeroCodomain
        (n := n) (Ω := Ω) (f := f)
    · intro _hcoord
      exact hf

/-- Helper for Theorem 7.3: in codimension `0`, the reverse direction of the
coordinatewise characterization is equivalent to proving domain null measurability
from `True`. -/
lemma helperForTheorem_7_3_reverse_zeroCodomain_reduces_to_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      IsLebesgueMeasurableFunction n 0 Ω f) ↔
      (True →
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  constructor
  · intro h
    intro hTrue
    have hcoord :
        ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) :=
      (helperForTheorem_7_3_coordinateFunctions_zeroCodomain_iff_true
        (n := n) (Ω := Ω) (f := f)).2 hTrue
    have hf : IsLebesgueMeasurableFunction n 0 Ω f := h hcoord
    exact (helperForTheorem_7_3_iff_nullMeasurableSet_zeroCodomain
      (n := n) (Ω := Ω) (f := f)).1 hf
  · intro h
    intro hcoord
    have hTrue : True :=
      (helperForTheorem_7_3_coordinateFunctions_zeroCodomain_iff_true
        (n := n) (Ω := Ω) (f := f)).1 hcoord
    have hΩ :
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      h hTrue
    exact (helperForTheorem_7_3_iff_nullMeasurableSet_zeroCodomain
      (n := n) (Ω := Ω) (f := f)).2 hΩ

/-- Helper for Theorem 7.3: in codimension `0`, domain null measurability is
sufficient to obtain the reverse coordinate implication. -/
lemma helperForTheorem_7_3_reverse_zeroCodomain_of_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      IsLebesgueMeasurableFunction n 0 Ω f := by
  intro _hcoord
  exact (helperForTheorem_7_3_iff_nullMeasurableSet_zeroCodomain
    (n := n) (Ω := Ω) (f := f)).2 hΩ

/-- Helper for Theorem 7.3: in codimension `0`, any proof of the reverse coordinate
implication forces domain null measurability. -/
lemma helperForTheorem_7_3_reverse_zeroCodomain_imp_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hReverse :
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        IsLebesgueMeasurableFunction n 0 Ω f) :
    MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  have hNullFromTrue :
      True →
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      (helperForTheorem_7_3_reverse_zeroCodomain_reduces_to_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f)).1 hReverse
  exact hNullFromTrue trivial

/-- Helper for Theorem 7.3: in codimension `0`, if `Ω` is not null measurable,
then no map `f : Ω → ℝ^0` can be Lebesgue measurable. -/
lemma helperForTheorem_7_3_not_isLebesgueMeasurableFunction_zeroCodomain_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ¬ IsLebesgueMeasurableFunction n 0 Ω f := by
  intro hf
  exact hΩ hf.1

/-- Helper for Theorem 7.3: in codimension `0`, non-null-measurable `Ω` gives a
fixed-map counterexample with vacuous coordinate measurability and failed
vector-valued measurability. -/
lemma helperForTheorem_7_3_coordinatewise_and_not_measurable_zeroCodomain_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ∧
      ¬ IsLebesgueMeasurableFunction n 0 Ω f := by
  refine ⟨?_, ?_⟩
  · exact helperForTheorem_7_3_coordinateFunctions_zeroCodomain
      (n := n) (Ω := Ω) (f := f)
  · exact
      helperForTheorem_7_3_not_isLebesgueMeasurableFunction_zeroCodomain_of_not_nullMeasurableSet
        (n := n) (Ω := Ω) (f := f) hΩ

/-- Helper for Theorem 7.3: in codimension `0`, if `Ω` is not null measurable then
the reverse coordinate implication cannot hold for any fixed map `f : Ω → ℝ^0`. -/
lemma helperForTheorem_7_3_not_reverse_zeroCodomain_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ¬ ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      IsLebesgueMeasurableFunction n 0 Ω f) := by
  intro hReverse
  exact
    helperForTheorem_7_3_not_isLebesgueMeasurableFunction_zeroCodomain_of_not_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hΩ
      (hReverse (helperForTheorem_7_3_coordinateFunctions_zeroCodomain
        (n := n) (Ω := Ω) (f := f)))

/-- Helper for Theorem 7.3: in codimension `0`, if `Ω` is not null measurable then
the reverse coordinate implication is equivalent to `False`. -/
lemma helperForTheorem_7_3_reverse_zeroCodomain_iff_false_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    (((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      IsLebesgueMeasurableFunction n 0 Ω f) ↔ False) := by
  constructor
  · intro hReverse
    exact
      (helperForTheorem_7_3_not_reverse_zeroCodomain_of_not_nullMeasurableSet
        (n := n) (Ω := Ω) (f := f) hΩ) hReverse
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Theorem 7.3: in codimension `0`, a reverse coordinate implication
combined with the vacuous coordinate hypothesis contradicts non-null-measurability
of `Ω`. -/
lemma helperForTheorem_7_3_false_of_reverse_zeroCodomain_and_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))
    (hReverse :
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        IsLebesgueMeasurableFunction n 0 Ω f) :
    False := by
  have hMeas : IsLebesgueMeasurableFunction n 0 Ω f := hReverse hcoord
  exact hΩ hMeas.1

/-- Helper for Theorem 7.3: in codimension `0`, the reverse coordinate implication
is equivalent to domain null measurability. -/
lemma helperForTheorem_7_3_reverse_zeroCodomain_iff_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      IsLebesgueMeasurableFunction n 0 Ω f) ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · intro hReverse
    exact helperForTheorem_7_3_reverse_zeroCodomain_imp_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hReverse
  · intro hΩ
    exact helperForTheorem_7_3_reverse_zeroCodomain_of_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hΩ

/-- Helper for Theorem 7.3: for a fixed codimension-`0` coordinate hypothesis, the
remaining reverse-direction goal is exactly domain null measurability. -/
lemma helperForTheorem_7_3_goal_zeroCodomain_iff_nullMeasurableSet_of_coordinateHypothesis
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    (IsLebesgueMeasurableFunction n 0 Ω f ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  constructor
  · intro hf
    exact hf.1
  · intro hΩ
    exact (helperForTheorem_7_3_reverse_zeroCodomain_of_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hΩ) hcoord

/-- Helper for Theorem 7.3: in codimension `0`, vacuous coordinatewise
measurability cannot by itself force domain null measurability. -/
lemma helperForTheorem_7_3_not_nullMeasurableSet_not_derivable_from_zeroCodomain_coordinates
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ¬ ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro hImp
  have hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) :=
    helperForTheorem_7_3_coordinateFunctions_zeroCodomain (n := n) (Ω := Ω) (f := f)
  exact hΩ (hImp hcoord)

/-- Helper for Theorem 7.3: in codimension `0`, the theorem's full biconditional is
equivalent to null measurability of the domain. -/
lemma helperForTheorem_7_3_target_zeroCodomain_iff_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    (IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  calc
    (IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ↔
        IsLebesgueMeasurableFunction n 0 Ω f :=
      helperForTheorem_7_3_target_zeroCodomain_iff_isLebesgueMeasurableFunction
        (n := n) (Ω := Ω) (f := f)
    _ ↔ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      helperForTheorem_7_3_iff_nullMeasurableSet_zeroCodomain
        (n := n) (Ω := Ω) (f := f)

/-- Helper for Theorem 7.3: in codimension `0`, if `Ω` is not null measurable,
then the theorem's biconditional fails for any `f : Ω → ℝ^0`. -/
lemma helperForTheorem_7_3_target_zeroCodomain_not_iff_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ¬ (IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) := by
  intro hIff
  exact hΩ
    ((helperForTheorem_7_3_target_zeroCodomain_iff_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f)).1 hIff)

/-- Helper for Theorem 7.3: in codimension `0`, failure of the theorem's
biconditional is equivalent to failure of domain null measurability. -/
lemma helperForTheorem_7_3_not_target_zeroCodomain_iff_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    (¬ (IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))) ↔
      ¬ MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · intro hNotIff
    intro hΩ
    apply hNotIff
    exact (helperForTheorem_7_3_target_zeroCodomain_iff_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f)).2 hΩ
  · intro hNotΩ
    exact helperForTheorem_7_3_target_zeroCodomain_not_iff_of_not_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hNotΩ

/-- Helper for Theorem 7.3: in codimension `0`, non-null-measurable `Ω` produces
an explicit counterexample map to the unguarded biconditional. -/
lemma helperForTheorem_7_3_exists_counterexample_zeroCodomain_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ f : Ω → EuclideanSpace ℝ (Fin 0),
      ¬ (IsLebesgueMeasurableFunction n 0 Ω f ↔
        ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) := by
  refine ⟨fun _ => 0, ?_⟩
  exact helperForTheorem_7_3_target_zeroCodomain_not_iff_of_not_nullMeasurableSet
    (n := n) (Ω := Ω) (f := fun _ => 0) hΩ

/-- Helper for Theorem 7.3: in codimension `0`, non-null-measurable `Ω` yields a
specific map whose coordinate functions are vacuously measurable while the map
itself is not Lebesgue measurable. -/
lemma helperForTheorem_7_3_exists_coordinatewise_not_measurable_zeroCodomain_of_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ f : Ω → EuclideanSpace ℝ (Fin 0),
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) ∧
        ¬ IsLebesgueMeasurableFunction n 0 Ω f := by
  refine ⟨fun _ => 0, ?_⟩
  exact
    helperForTheorem_7_3_coordinatewise_and_not_measurable_zeroCodomain_of_not_nullMeasurableSet
      (n := n) (Ω := Ω) (f := fun _ => 0) hΩ

/-- Helper for Theorem 7.3: in codimension `0`, any proof of the theorem's target
biconditional for a fixed map forces domain null measurability. -/
lemma helperForTheorem_7_3_nullMeasurableSet_of_target_zeroCodomain_iff
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hIff : IsLebesgueMeasurableFunction n 0 Ω f ↔
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  exact (helperForTheorem_7_3_target_zeroCodomain_iff_nullMeasurableSet
    (n := n) (Ω := Ω) (f := f)).1 hIff

/-- Helper for Theorem 7.3: in codimension `0`, combining a fixed coordinate
hypothesis with any reverse-direction implication forces domain null
measurability. -/
lemma helperForTheorem_7_3_nullMeasurableSet_of_coordinateHypothesis_and_reverse_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))
    (hReverse :
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        IsLebesgueMeasurableFunction n 0 Ω f) :
    MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  exact (hReverse hcoord).1

/-- Helper for Theorem 7.3: in codimension `0`, if `Ω` is not null measurable
then no reverse-direction implication can hold for a fixed coordinate
hypothesis. -/
lemma helperForTheorem_7_3_false_of_not_nullMeasurableSet_and_coordinateHypothesis_and_reverse_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))
    (hReverse :
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        IsLebesgueMeasurableFunction n 0 Ω f) :
    False := by
  exact hΩ
    (helperForTheorem_7_3_nullMeasurableSet_of_coordinateHypothesis_and_reverse_zeroCodomain
      (n := n) (Ω := Ω) (f := f) hcoord hReverse)

/-- Helper for Theorem 7.3: in codimension `0`, coordinatewise scalar
measurability together with domain null measurability implies vector
measurability. -/
lemma helperForTheorem_7_3_isLebesgueMeasurableFunction_zeroCodomain_of_coordinateHypothesis_and_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))
    (hΩ :
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    IsLebesgueMeasurableFunction n 0 Ω f := by
  exact
    (helperForTheorem_7_3_goal_zeroCodomain_iff_nullMeasurableSet_of_coordinateHypothesis
      (n := n) (Ω := Ω) (f := f) hcoord).2 hΩ

/-- Helper for Theorem 7.3: in codimension `0`, coordinatewise scalar
measurability together with failure of domain null measurability rules out vector
measurability. -/
lemma helperForTheorem_7_3_not_isLebesgueMeasurableFunction_zeroCodomain_of_coordinateHypothesis_and_not_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j))
    (hΩ :
      ¬ MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ¬ IsLebesgueMeasurableFunction n 0 Ω f := by
  intro hf
  have hΩ' :
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
    (helperForTheorem_7_3_goal_zeroCodomain_iff_nullMeasurableSet_of_coordinateHypothesis
      (n := n) (Ω := Ω) (f := f) hcoord).1 hf
  exact hΩ hΩ'

/-- Helper for Theorem 7.3: in codimension `0`, the remaining reverse-direction
subgoal can be reformulated as proving the reverse implication from domain null
measurability, and conversely any such reverse implication forces domain null
measurability for the fixed coordinate hypothesis. -/
lemma helperForTheorem_7_3_nullMeasurableSet_of_coordinateFunctions_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    (MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ↔
      ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        IsLebesgueMeasurableFunction n 0 Ω f) := by
  constructor
  · intro hΩ
    exact helperForTheorem_7_3_reverse_zeroCodomain_of_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f) hΩ
  · intro hReverse
    exact (hReverse hcoord).1

/-- Helper for Theorem 7.3: in codimension `0`, for a fixed coordinatewise
measurability witness, the remaining reverse goal is equivalent to deriving
domain null measurability from that same witness. -/
lemma helperForTheorem_7_3_reverse_goal_zeroCodomain_iff_nullMeasurableSet_from_coordinateHypothesis
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hcoord :
      ∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) :
    IsLebesgueMeasurableFunction n 0 Ω f ↔
      ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  constructor
  · intro hf
    intro _hcoord
    exact hf.1
  · intro hNullFromCoord
    have hΩ :
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      hNullFromCoord hcoord
    exact
      helperForTheorem_7_3_isLebesgueMeasurableFunction_zeroCodomain_of_coordinateHypothesis_and_nullMeasurableSet
        (n := n) (Ω := Ω) (f := f) hcoord hΩ

/-- Helper for Theorem 7.3: in codimension `0`, the reverse-direction subgoal
`(∀ j : Fin 0, ...) → NullMeasurableSet Ω` is equivalent to domain null
measurability itself. -/
lemma helperForTheorem_7_3_reverseSubgoal_zeroCodomain_iff_nullMeasurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)} :
    ((∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ↔
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · intro hReverseSubgoal
    exact hReverseSubgoal
      (helperForTheorem_7_3_coordinateFunctions_zeroCodomain (n := n) (Ω := Ω) (f := f))
  · intro hΩ
    intro _hcoord
    exact hΩ

/-- Helper for Theorem 7.3: in codimension `0`, any proof of the reverse
subgoal `(∀ j : Fin 0, ...) → NullMeasurableSet Ω` immediately yields domain
null measurability. -/
lemma helperForTheorem_7_3_nullMeasurableSet_of_reverseSubgoal_zeroCodomain
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin 0)}
    (hReverseSubgoal :
      (∀ j : Fin 0, IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j)) →
        MeasureTheory.NullMeasurableSet Ω
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  exact
    (helperForTheorem_7_3_reverseSubgoal_zeroCodomain_iff_nullMeasurableSet
      (n := n) (Ω := Ω) (f := f)).1 hReverseSubgoal

/-- Helper for Theorem 7.3: if `Ω` is measurable, then coordinatewise scalar
measurability is equivalent to vector-valued Lebesgue measurability in every
target dimension. -/
lemma helperForTheorem_7_3_iff_coordinateFunctions_of_measurableSet
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hΩ : MeasurableSet Ω) :
    IsLebesgueMeasurableFunction n m Ω f ↔
      ∀ j : Fin m,
        IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  exact
    isLebesgueMeasurableFunction_iff_coordinateFunctions_of_pos_or_nullMeasurableSet
      (n := n) (m := m) (Ω := Ω) (f := f) (Or.inr hΩ.nullMeasurableSet)

/-- Theorem 7.3 (positive target dimension): for a Lebesgue measurable set
`Ω ⊆ ℝ^n` and a map `f : Ω → ℝ^m` with `0 < m`, `f` is Lebesgue measurable if and
only if each coordinate function is Lebesgue measurable. -/
theorem isLebesgueMeasurableFunction_iff_coordinateFunctions
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)} (hm : 0 < m) :
    IsLebesgueMeasurableFunction n m Ω f ↔
      ∀ j : Fin m,
        IsLebesgueMeasurableScalarFunction n Ω (fun x => f x j) := by
  exact helperForTheorem_7_3_iff_coordinateFunctions_of_pos hm

/-- Helper for Theorem 7.4: composing a scalar Lebesgue measurable function with a
continuous scalar map preserves scalar measurability. -/
lemma helperForTheorem_7_4_comp_continuous_scalar
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hf : IsLebesgueMeasurableScalarFunction n Ω f) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => φ (f x)) := by
  refine ⟨hf.1, ?_⟩
  intro V hV
  have hPreOpen : IsOpen (φ ⁻¹' V) := hV.preimage hφ
  rcases hf.2 (φ ⁻¹' V) hPreOpen with ⟨E, hENull, hEq⟩
  refine ⟨E, hENull, ?_⟩
  simpa using hEq

/-- Helper for Theorem 7.4: the absolute value of a scalar Lebesgue measurable
function is scalar Lebesgue measurable. -/
lemma helperForTheorem_7_4_abs_measurable
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ}
    (hf : IsLebesgueMeasurableScalarFunction n Ω f) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => |f x|) := by
  exact
    helperForTheorem_7_4_comp_continuous_scalar
      (φ := fun t => |t|) continuous_abs hf

/-- Helper for Theorem 7.4: the positive and negative truncations `max(f,0)` and
`min(f,0)` of a scalar Lebesgue measurable function are scalar measurable. -/
lemma helperForTheorem_7_4_max_min_zero_measurable
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ}
    (hf : IsLebesgueMeasurableScalarFunction n Ω f) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => max (f x) 0) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => min (f x) 0) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_7_4_comp_continuous_scalar
        (φ := fun t => max t 0) (continuous_id.max continuous_const) hf
  · exact
      helperForTheorem_7_4_comp_continuous_scalar
        (φ := fun t => min t 0) (continuous_id.min continuous_const) hf

/-- Theorem 7.4: if `Ω ⊆ ℝ^n` is measurable and `f : Ω → ℝ` is measurable, then
the pointwise functions `|f|`, `max(f, 0)`, and `min(f, 0)` are measurable on `Ω`. -/
theorem isLebesgueMeasurableScalarFunction_abs_max_min_zero
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ}
    (hf : IsLebesgueMeasurableScalarFunction n Ω f) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => |f x|) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => max (f x) 0) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => min (f x) 0) := by
  refine ⟨helperForTheorem_7_4_abs_measurable hf, ?_⟩
  exact helperForTheorem_7_4_max_min_zero_measurable hf

/-- Helper for Theorem 7.5: two scalar measurable functions form a measurable
`ℝ²`-valued pair map. -/
lemma helperForTheorem_7_5_pair_isLebesgueMeasurableFunction
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u v : Ω → ℝ}
    (hu : IsLebesgueMeasurableScalarFunction n Ω u)
    (hv : IsLebesgueMeasurableScalarFunction n Ω v) :
    IsLebesgueMeasurableFunction n 2 Ω (fun x => !₂[u x, v x]) := by
  have hIff :
      IsLebesgueMeasurableFunction n 2 Ω (fun x => !₂[u x, v x]) ↔
        ∀ j : Fin 2, IsLebesgueMeasurableScalarFunction n Ω (fun x => (!₂[u x, v x]) j) :=
    isLebesgueMeasurableFunction_iff_coordinateFunctions_of_pos_or_nullMeasurableSet
      (n := n) (m := 2) (Ω := Ω) (f := fun x => !₂[u x, v x]) (Or.inl (by decide))
  refine hIff.2 ?_
  intro j
  fin_cases j
  · simpa using hu
  · simpa using hv

/-- Helper for Theorem 7.5: composing a measurable vector map into `ℝ^m` with a
continuous scalar map yields a measurable scalar function. -/
lemma helperForTheorem_7_5_comp_continuous_scalar_of_vector
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {F : Ω → EuclideanSpace ℝ (Fin m)}
    {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF : IsLebesgueMeasurableFunction n m Ω F)
    (hφ : Continuous φ) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => φ (F x)) := by
  refine ⟨hF.1, ?_⟩
  intro V hV
  have hPreOpen : IsOpen (φ ⁻¹' V) := hV.preimage hφ
  rcases hF.2 (φ ⁻¹' V) hPreOpen with ⟨E, hENull, hEq⟩
  refine ⟨E, hENull, ?_⟩
  simpa using hEq

/-- Helper for Theorem 7.5: binary scalar operations induced by a continuous map
`ℝ² → ℝ` preserve scalar Lebesgue measurability. -/
lemma helperForTheorem_7_5_binaryContinuous_measurable
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u v : Ω → ℝ} {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hu : IsLebesgueMeasurableScalarFunction n Ω u)
    (hv : IsLebesgueMeasurableScalarFunction n Ω v)
    (hψ : Continuous ψ) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => ψ (!₂[u x, v x])) := by
  have hPair :
      IsLebesgueMeasurableFunction n 2 Ω (fun x => !₂[u x, v x]) :=
    helperForTheorem_7_5_pair_isLebesgueMeasurableFunction
      (n := n) (Ω := Ω) (u := u) (v := v) hu hv
  exact
    helperForTheorem_7_5_comp_continuous_scalar_of_vector
      (n := n) (m := 2) (Ω := Ω) (F := fun x => !₂[u x, v x]) (φ := ψ) hPair hψ

/-- Helper for Theorem 7.5: composing a scalar measurable function with a
continuous map on an open subtype preserves scalar measurability. -/
lemma helperForTheorem_7_5_comp_continuous_scalar_on_openSubtype
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : Ω → ℝ} {W : Set ℝ} {φ : W → ℝ}
    (hu : IsLebesgueMeasurableScalarFunction n Ω u)
    (_hW : IsOpen W)
    (huW : ∀ x : Ω, u x ∈ W)
    (hφ : Continuous φ) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => φ ⟨u x, huW x⟩) := by
  refine ⟨hu.1, ?_⟩
  intro V hV
  have hPreOpen : IsOpen (φ ⁻¹' V) := hV.preimage hφ
  rcases (isOpen_induced_iff.mp hPreOpen) with ⟨U, hUOpen, hUeq⟩
  rcases hu.2 U hUOpen with ⟨E, hENull, hEq⟩
  refine ⟨E, hENull, ?_⟩
  have hCompPreimage :
      (fun x : Ω => φ ⟨u x, huW x⟩) ⁻¹' V = u ⁻¹' U := by
    ext x
    constructor
    · intro hx
      have hx' : (⟨u x, huW x⟩ : W) ∈ φ ⁻¹' V := hx
      have hx'' : (⟨u x, huW x⟩ : W) ∈ Subtype.val ⁻¹' U := by
        exact hUeq.symm ▸ hx'
      exact hx''
    · intro hx
      have hx' : (⟨u x, huW x⟩ : W) ∈ Subtype.val ⁻¹' U := hx
      have hx'' : (⟨u x, huW x⟩ : W) ∈ φ ⁻¹' V := by
        exact hUeq ▸ hx'
      exact hx''
  calc
    Subtype.val '' ((fun x : Ω => φ ⟨u x, huW x⟩) ⁻¹' V) = Subtype.val '' (u ⁻¹' U) := by
      rw [hCompPreimage]
    _ = Ω ∩ E := hEq

/-- Theorem 7.5: if `Ω ⊆ ℝ^n` is measurable and `f, g : Ω → ℝ` are measurable,
then `f + g`, `f - g`, `f * g`, `max(f, g)`, and `min(f, g)` are measurable on `Ω`.
If additionally `g x ≠ 0` for all `x ∈ Ω`, then `f / g` is measurable on `Ω`. -/
theorem isLebesgueMeasurableScalarFunction_add_sub_mul_max_min_div
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f g : Ω → ℝ}
    (hf : IsLebesgueMeasurableScalarFunction n Ω f)
    (hg : IsLebesgueMeasurableScalarFunction n Ω g) :
    IsLebesgueMeasurableScalarFunction n Ω (fun x => f x + g x) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => f x - g x) ∧
    IsLebesgueMeasurableScalarFunction n Ω (fun x => f x * g x) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => max (f x) (g x)) ∧
      IsLebesgueMeasurableScalarFunction n Ω (fun x => min (f x) (g x)) ∧
      ((∀ x : Ω, g x ≠ 0) →
        IsLebesgueMeasurableScalarFunction n Ω (fun x => f x / g x)) := by
  have hAddCont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) :=
    (EuclideanSpace.proj 0).continuous.add (EuclideanSpace.proj 1).continuous
  have hSubCont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p 0 - p 1) :=
    (EuclideanSpace.proj 0).continuous.sub (EuclideanSpace.proj 1).continuous
  have hMulCont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * p 1) :=
    (EuclideanSpace.proj 0).continuous.mul (EuclideanSpace.proj 1).continuous
  have hMaxCont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => max (p 0) (p 1)) :=
    (EuclideanSpace.proj 0).continuous.max (EuclideanSpace.proj 1).continuous
  have hMinCont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => min (p 0) (p 1)) :=
    (EuclideanSpace.proj 0).continuous.min (EuclideanSpace.proj 1).continuous
  have hAdd :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => f x + g x) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := g) (ψ := fun p => p 0 + p 1)
        hf hg hAddCont)
  have hSub :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => f x - g x) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := g) (ψ := fun p => p 0 - p 1)
        hf hg hSubCont)
  have hMul :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => f x * g x) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := g) (ψ := fun p => p 0 * p 1)
        hf hg hMulCont)
  have hMax :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => max (f x) (g x)) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := g) (ψ := fun p => max (p 0) (p 1))
        hf hg hMaxCont)
  have hMin :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => min (f x) (g x)) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := g) (ψ := fun p => min (p 0) (p 1))
        hf hg hMinCont)
  refine ⟨hAdd, hSub, hMul, hMax, hMin, ?_⟩
  intro hgnz
  have hInv :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => (g x)⁻¹) := by
    have hMemNonzero : ∀ x : Ω, g x ∈ ({t : ℝ | t ≠ 0}) := by
      intro x
      exact hgnz x
    exact
      helperForTheorem_7_5_comp_continuous_scalar_on_openSubtype
        (n := n) (Ω := Ω) (u := g) (W := {t : ℝ | t ≠ 0})
        (φ := fun t : {t : ℝ // t ≠ 0} => (t : ℝ)⁻¹)
        hg isOpen_ne hMemNonzero Real.continuous_inv
  have hMulInv :
      IsLebesgueMeasurableScalarFunction n Ω (fun x => f x * (g x)⁻¹) := by
    simpa using
      (helperForTheorem_7_5_binaryContinuous_measurable
        (n := n) (Ω := Ω) (u := f) (v := fun x => (g x)⁻¹) (ψ := fun p => p 0 * p 1)
        hf hInv hMulCont)
  simpa [div_eq_mul_inv] using hMulInv

end Section05
end Chap07
