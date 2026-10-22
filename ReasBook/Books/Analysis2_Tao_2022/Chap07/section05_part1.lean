/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap07
section Section05

/-- Definition 7.6 (Measurable function): let `n, m ∈ ℕ`, let `Ω ⊆ ℝ^n`, and let
`f : Ω → ℝ^m`. The function `f` is (Lebesgue) measurable if for every open set
`V ⊆ ℝ^m`, there exists a Lebesgue measurable set `E ⊆ ℝ^n` such that the preimage
`{x ∈ Ω | f x ∈ V}` equals `Ω ∩ E` as a subset of `ℝ^n`. -/
def IsLebesgueMeasurableFunction (n m : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ V : Set (EuclideanSpace ℝ (Fin m)), IsOpen V →
      ∃ E : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet E
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
          Subtype.val '' (f ⁻¹' V) = Ω ∩ E

/-- Lemma 7.10: if `Ω ⊆ ℝ^n` is Lebesgue measurable and `f : Ω → ℝ^m` is continuous
for the subspace topology on `Ω`, then for every Borel set `B ⊆ ℝ^m`, the set
`{x ∈ Ω | f x ∈ B}` is Lebesgue measurable in `ℝ^n`. -/
theorem continuous_preimage_borel_nullMeasurable
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    {f : Ω → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) :
    ∀ B : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet B →
      MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' B))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  intro B hB
  exact MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe hΩ
    (hf.measurable hB)

/-- Helper for Lemma 7.11: every coordinate open box in `ℝ^m` is open. -/
lemma helperForLemma_7_11_openBox_isOpen
    {m : ℕ} (a b : Fin m → ℝ) :
    IsOpen ({x : EuclideanSpace ℝ (Fin m) |
      ∀ i : Fin m, a i < x i ∧ x i < b i}) := by
  let T : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
    fun i => {x : EuclideanSpace ℝ (Fin m) | a i < x i ∧ x i < b i}
  have hEq : {x : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, a i < x i ∧ x i < b i} =
      ⋂ i ∈ (Finset.univ : Finset (Fin m)), T i := by
    ext x
    simp [T]
  rw [hEq]
  refine isOpen_biInter_finset ?_
  intro i hi
  have hleft : IsOpen {x : EuclideanSpace ℝ (Fin m) | a i < (EuclideanSpace.proj i) x} := by
    exact isOpen_lt continuous_const (EuclideanSpace.proj i).continuous
  have hright : IsOpen {x : EuclideanSpace ℝ (Fin m) | (EuclideanSpace.proj i) x < b i} := by
    exact isOpen_lt (EuclideanSpace.proj i).continuous continuous_const
  simpa [T, Set.setOf_and, EuclideanSpace.proj] using hleft.inter hright

/-- Helper for Lemma 7.11: `Subtype.val '' (f ⁻¹' V)` is always contained in `Ω`. -/
lemma helperForLemma_7_11_preimageImage_subset
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (V : Set (EuclideanSpace ℝ (Fin m))) :
    Subtype.val '' (f ⁻¹' V) ⊆ Ω := by
  rintro x ⟨xΩ, -, rfl⟩
  exact xΩ.2

/-- Helper for Lemma 7.11: complement rule for `V ↦ Subtype.val '' (f ⁻¹' V)`. -/
lemma helperForLemma_7_11_preimageImage_compl
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (V : Set (EuclideanSpace ℝ (Fin m))) :
    Subtype.val '' (f ⁻¹' Vᶜ) = Ω \ (Subtype.val '' (f ⁻¹' V)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨xΩ, hxVcompl, rfl⟩
    constructor
    · exact xΩ.2
    · intro hxV
      rcases hxV with ⟨y, hyV, hyx⟩
      have hyEq : y = xΩ := Subtype.ext hyx
      exact hxVcompl (hyEq ▸ hyV)
  · intro hx
    rcases hx with ⟨hxΩ, hxnot⟩
    refine ⟨⟨x, hxΩ⟩, ?_, rfl⟩
    intro hxV
    apply hxnot
    exact ⟨⟨x, hxΩ⟩, hxV, rfl⟩

/-- Helper for Lemma 7.11: countable union rule for `V ↦ Subtype.val '' (f ⁻¹' V)`. -/
lemma helperForLemma_7_11_preimageImage_iUnion
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (V : ℕ → Set (EuclideanSpace ℝ (Fin m))) :
    Subtype.val '' (f ⁻¹' (⋃ i, V i)) = ⋃ i, (Subtype.val '' (f ⁻¹' V i)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨xΩ, hxV, rfl⟩
    rcases Set.mem_iUnion.mp hxV with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨xΩ, hxi, rfl⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    rcases hxi with ⟨xΩ, hxVi, rfl⟩
    exact ⟨xΩ, Set.mem_iUnion.mpr ⟨i, hxVi⟩, rfl⟩

/-- Helper for Lemma 7.11: full-coordinate open boxes in `ℝ^m` as a generating family. -/
def helperForLemma_7_11_openBoxFamily (m : ℕ) :
    Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {B : Set (EuclideanSpace ℝ (Fin m)) |
    ∃ a b : Fin m → ℝ, B = {x : EuclideanSpace ℝ (Fin m) |
      ∀ i : Fin m, a i < x i ∧ x i < b i}}

/-- Helper for Lemma 7.11: finite-coordinate open cylinders in `ℝ^m` form a basis family. -/
def helperForLemma_7_11_cylinderOpenFamily (m : ℕ) :
    Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {S : Set (EuclideanSpace ℝ (Fin m)) |
    ∃ U : Fin m → Set ℝ, ∃ F : Finset (Fin m),
      (∀ i, i ∈ F → IsOpen (U i)) ∧
        S = {x : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, i ∈ F → x i ∈ U i}}

/-- Helper for Lemma 7.11: finite-coordinate open cylinders are a topological basis on `ℝ^m`. -/
lemma helperForLemma_7_11_cylinderOpen_isTopologicalBasis
    {m : ℕ} :
    TopologicalSpace.IsTopologicalBasis (helperForLemma_7_11_cylinderOpenFamily m) := by
  classical
  let CylFun : Set (Set (Fin m → ℝ)) :=
    {S : Set (Fin m → ℝ) |
      ∃ U : Fin m → Set ℝ, ∃ F : Finset (Fin m),
        (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set (Fin m)).pi U}
  have hCylFunBasis : TopologicalSpace.IsTopologicalBasis CylFun := by
    simpa [CylFun] using
      (isTopologicalBasis_pi
        (fun _ : Fin m =>
          (TopologicalSpace.isTopologicalBasis_opens :
            TopologicalSpace.IsTopologicalBasis {U : Set ℝ | IsOpen U})))
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro W hW
    rcases hW with ⟨U, F, hU, rfl⟩
    have hEq :
        {x : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, i ∈ F → x i ∈ U i} =
          ⋂ i ∈ F, {x : EuclideanSpace ℝ (Fin m) | x i ∈ U i} := by
      ext x
      simp
    rw [hEq]
    refine isOpen_biInter_finset ?_
    intro i hi
    exact (hU i hi).preimage (EuclideanSpace.proj i).continuous
  · intro x V hx hV
    let e : EuclideanSpace ℝ (Fin m) ≃ₜ (Fin m → ℝ) :=
      (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
    have hxImage : e x ∈ e '' V := ⟨x, hx, rfl⟩
    have hImageOpen : IsOpen (e '' V) := e.isOpenMap V hV
    rcases hCylFunBasis.exists_subset_of_mem_open hxImage hImageOpen with
      ⟨Sfun, hSfun, hxSfun, hSfunSub⟩
    rcases hSfun with ⟨U, F, hU, rfl⟩
    refine ⟨{y : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, i ∈ F → y i ∈ U i}, ?_, ?_, ?_⟩
    · exact ⟨U, F, hU, rfl⟩
    · intro i hi
      have hxCoord : (e x) i ∈ U i := hxSfun i hi
      simpa [e, EuclideanSpace.equiv] using hxCoord
    · intro y hy
      have hyImage : e y ∈ e '' V := by
        apply hSfunSub
        intro i hi
        have hyCoord : y i ∈ U i := hy i hi
        simpa [e, EuclideanSpace.equiv] using hyCoord
      rcases hyImage with ⟨z, hzV, hzEq⟩
      have hzy : z = y := e.injective hzEq
      exact hzy ▸ hzV

/-- Helper for Lemma 7.11: every open cylinder neighborhood contains a full coordinate open box. -/
lemma helperForLemma_7_11_openBox_refines_cylinder
    {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))} {x : EuclideanSpace ℝ (Fin m)}
    (hS : S ∈ helperForLemma_7_11_cylinderOpenFamily m) (hx : x ∈ S) :
    ∃ a b : Fin m → ℝ,
      x ∈ {y : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, a i < y i ∧ y i < b i} ∧
      {y : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, a i < y i ∧ y i < b i} ⊆ S := by
  classical
  rcases hS with ⟨U, F, hUOpen, rfl⟩
  have hxF : ∀ i, i ∈ F → x i ∈ U i := by
    intro i hi
    exact hx i hi
  have hInterval :
      ∀ i, i ∈ F → ∃ l u : ℝ, x i ∈ Set.Ioo l u ∧ Set.Ioo l u ⊆ U i := by
    intro i hi
    have hNhds : U i ∈ nhds (x i) := (hUOpen i hi).mem_nhds (hxF i hi)
    exact mem_nhds_iff_exists_Ioo_subset.mp hNhds
  let l : ∀ i : Fin m, i ∈ F → ℝ := fun i hi => Classical.choose (hInterval i hi)
  let u : ∀ i : Fin m, i ∈ F → ℝ := fun i hi =>
    Classical.choose (Classical.choose_spec (hInterval i hi))
  have hxIoo : ∀ i : Fin m, ∀ hi : i ∈ F, x i ∈ Set.Ioo (l i hi) (u i hi) := by
    intro i hi
    exact (Classical.choose_spec (Classical.choose_spec (hInterval i hi))).1
  have hIooSubset :
      ∀ i : Fin m, ∀ hi : i ∈ F, Set.Ioo (l i hi) (u i hi) ⊆ U i := by
    intro i hi
    exact (Classical.choose_spec (Classical.choose_spec (hInterval i hi))).2
  let a : Fin m → ℝ := fun i => if hi : i ∈ F then l i hi else x i - 1
  let b : Fin m → ℝ := fun i => if hi : i ∈ F then u i hi else x i + 1
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ F
    · have hxi : x i ∈ Set.Ioo (l i hi) (u i hi) := hxIoo i hi
      simpa [a, b, hi, Set.mem_Ioo] using hxi
    · have hlt1 : x i - 1 < x i := by linarith
      have hlt2 : x i < x i + 1 := by linarith
      simpa [a, b, hi] using And.intro hlt1 hlt2
  · intro y hy
    intro i hi
    have hyi : y i ∈ Set.Ioo (a i) (b i) := hy i
    have hyi' : y i ∈ Set.Ioo (l i hi) (u i hi) := by
      simpa [a, b, hi, Set.mem_Ioo] using hyi
    exact hIooSubset i hi hyi'

/-- Helper for Lemma 7.11: full-coordinate open boxes form a topological basis on `ℝ^m`. -/
lemma helperForLemma_7_11_openBox_isTopologicalBasis
    {m : ℕ} :
    TopologicalSpace.IsTopologicalBasis (helperForLemma_7_11_openBoxFamily m) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro W hW
    rcases hW with ⟨a, b, rfl⟩
    exact helperForLemma_7_11_openBox_isOpen a b
  · intro x U hx hU
    have hCylBasis :
        TopologicalSpace.IsTopologicalBasis (helperForLemma_7_11_cylinderOpenFamily m) :=
      helperForLemma_7_11_cylinderOpen_isTopologicalBasis (m := m)
    rcases hCylBasis.exists_subset_of_mem_open hx hU with ⟨S, hS, hxS, hSU⟩
    rcases helperForLemma_7_11_openBox_refines_cylinder (m := m) hS hxS with
      ⟨a, b, hxBox, hBoxS⟩
    refine ⟨{y : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, a i < y i ∧ y i < b i}, ?_, hxBox, ?_⟩
    · exact ⟨a, b, rfl⟩
    · exact hBoxS.trans hSU

/-- Helper for Lemma 7.11: open sets are measurable for the `σ`-algebra generated by open boxes. -/
lemma helperForLemma_7_11_isOpen_measurableSet_generateFrom_openBoxes
    {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hV : IsOpen V) :
    @MeasurableSet (EuclideanSpace ℝ (Fin m))
      (MeasurableSpace.generateFrom
        {B : Set (EuclideanSpace ℝ (Fin m)) |
          ∃ a b : Fin m → ℝ, B = {x : EuclideanSpace ℝ (Fin m) |
            ∀ i : Fin m, a i < x i ∧ x i < b i}}) V := by
  have hBasis :
      TopologicalSpace.IsTopologicalBasis (helperForLemma_7_11_openBoxFamily m) :=
    helperForLemma_7_11_openBox_isTopologicalBasis (m := m)
  have hBorel :
      borel (EuclideanSpace ℝ (Fin m)) =
        MeasurableSpace.generateFrom (helperForLemma_7_11_openBoxFamily m) :=
    hBasis.borel_eq_generateFrom
  have hVMeasBorel :
      @MeasurableSet (EuclideanSpace ℝ (Fin m))
        (borel (EuclideanSpace ℝ (Fin m))) V := by
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin m))]
    exact hV.measurableSet
  have hVMeas :
      @MeasurableSet (EuclideanSpace ℝ (Fin m))
        (MeasurableSpace.generateFrom (helperForLemma_7_11_openBoxFamily m)) V := by
    rw [← hBorel]
    exact hVMeasBorel
  simpa [helperForLemma_7_11_openBoxFamily] using hVMeas

/-- Helper for Lemma 7.11: null measurability of preimages extends from open boxes to generated sets. -/
lemma helperForLemma_7_11_nullMeasurable_preimage_of_generateFrom
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)}
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hbox : ∀ a b : Fin m → ℝ,
      MeasureTheory.NullMeasurableSet
        (Subtype.val '' (f ⁻¹' {x : EuclideanSpace ℝ (Fin m) |
          ∀ i : Fin m, a i < x i ∧ x i < b i}))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ V : Set (EuclideanSpace ℝ (Fin m)),
      @MeasurableSet (EuclideanSpace ℝ (Fin m))
        (MeasurableSpace.generateFrom
          {B : Set (EuclideanSpace ℝ (Fin m)) |
            ∃ a b : Fin m → ℝ, B = {x : EuclideanSpace ℝ (Fin m) |
              ∀ i : Fin m, a i < x i ∧ x i < b i}}) V →
        MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' V))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  let C : Set (Set (EuclideanSpace ℝ (Fin m))) :=
    {B : Set (EuclideanSpace ℝ (Fin m)) |
      ∃ a b : Fin m → ℝ, B = {x : EuclideanSpace ℝ (Fin m) |
        ∀ i : Fin m, a i < x i ∧ x i < b i}}
  intro V hV
  have hInd :
      ∀ W : Set (EuclideanSpace ℝ (Fin m)),
        @MeasurableSet (EuclideanSpace ℝ (Fin m)) (MeasurableSpace.generateFrom C) W →
          MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' W))
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
    intro W hW
    refine MeasurableSpace.generateFrom_induction (C := C)
      (p := fun W _ =>
        MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' W))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
      ?_ ?_ ?_ ?_ W hW
    · intro W hWC hWMeas
      rcases hWC with ⟨a, b, rfl⟩
      exact hbox a b
    · simpa using (MeasureTheory.nullMeasurableSet_empty :
        MeasureTheory.NullMeasurableSet (∅ : Set (EuclideanSpace ℝ (Fin n)))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    · intro W hWMeas hWNull
      rw [helperForLemma_7_11_preimageImage_compl (f := f) W]
      exact hΩ.diff hWNull
    · intro W hWMeas hWNull
      rw [helperForLemma_7_11_preimageImage_iUnion (f := f) W]
      exact MeasureTheory.NullMeasurableSet.iUnion hWNull
  simpa [C] using hInd V hV

/-- Lemma 7.11: for `Ω ⊆ ℝ^n` and `f : Ω → ℝ^m`, if `Ω` is Lebesgue measurable,
then `f` is (Lebesgue) measurable if and only if for every open box
`B = {x | ∀ i, a i < x i ∧ x i < b i} ⊆ ℝ^m`, the set `f⁻¹(B)` is Lebesgue measurable (viewed in `ℝ^n`
as `Subtype.val '' (f ⁻¹' B)`). -/
theorem isLebesgueMeasurableFunction_iff_preimage_openBox_nullMeasurable
    {n m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → EuclideanSpace ℝ (Fin m)} :
    MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) →
      (IsLebesgueMeasurableFunction n m Ω f ↔
        ∀ a b : Fin m → ℝ,
          MeasureTheory.NullMeasurableSet
            (Subtype.val '' (f ⁻¹' {x : EuclideanSpace ℝ (Fin m) |
              ∀ i : Fin m, a i < x i ∧ x i < b i}))
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro hΩ
  constructor
  · intro hf a b
    rcases hf with ⟨hΩf, hOpenPreimage⟩
    have hOpenBox :
        IsOpen ({x : EuclideanSpace ℝ (Fin m) |
          ∀ i : Fin m, a i < x i ∧ x i < b i}) :=
      helperForLemma_7_11_openBox_isOpen a b
    rcases hOpenPreimage
        ({x : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, a i < x i ∧ x i < b i})
        hOpenBox with ⟨E, hE, hEq⟩
    have hInter :
        MeasureTheory.NullMeasurableSet (Ω ∩ E)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      hΩf.inter hE
    exact hEq.symm ▸ hInter
  · intro hbox
    refine ⟨hΩ, ?_⟩
    intro V hV
    let C : Set (Set (EuclideanSpace ℝ (Fin m))) :=
      {B : Set (EuclideanSpace ℝ (Fin m)) |
        ∃ a b : Fin m → ℝ, B = {x : EuclideanSpace ℝ (Fin m) |
          ∀ i : Fin m, a i < x i ∧ x i < b i}}
    have hVMeas : @MeasurableSet (EuclideanSpace ℝ (Fin m)) (MeasurableSpace.generateFrom C) V := by
      simpa [C] using
        (helperForLemma_7_11_isOpen_measurableSet_generateFrom_openBoxes (m := m) hV)
    have hPreNull :
        MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' V))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
      exact helperForLemma_7_11_nullMeasurable_preimage_of_generateFrom hΩ hbox V hVMeas
    refine ⟨Subtype.val '' (f ⁻¹' V), hPreNull, ?_⟩
    have hSubset : Subtype.val '' (f ⁻¹' V) ⊆ Ω :=
      helperForLemma_7_11_preimageImage_subset (f := f) V
    ext x
    constructor
    · intro hx
      exact ⟨hSubset hx, hx⟩
    · intro hx
      exact hx.2


end Section05
end Chap07
