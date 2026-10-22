/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.section05_part2

section Chap07
section Section05

/-- Helper for Lemma 7.12: the image under `Subtype.val` of a continuous preimage
of an open set in the subtype codomain is open in the ambient space. -/
lemma helperForLemma_7_12_isOpen_image_preimage_subtypeVal
    {m p : ℕ} {W : Set (EuclideanSpace ℝ (Fin m))} (hW : IsOpen W)
    {g : W → EuclideanSpace ℝ (Fin p)} (hg : Continuous g)
    {V : Set (EuclideanSpace ℝ (Fin p))} (hV : IsOpen V) :
    IsOpen (Subtype.val '' (g ⁻¹' V)) := by
  have hPreimageOpen : IsOpen (g ⁻¹' V) := hV.preimage hg
  rcases (isOpen_induced_iff.mp hPreimageOpen) with ⟨U, hUOpen, hUeq⟩
  have hImageEq : Subtype.val '' (g ⁻¹' V) = W ∩ U := by
    calc
      Subtype.val '' (g ⁻¹' V) = Subtype.val '' (Subtype.val ⁻¹' U) := by
        rw [← hUeq]
      _ = W ∩ U := by
        simpa using (Subtype.image_preimage_val (s := W) (t := U))
  rw [hImageEq]
  exact hW.inter hUOpen

/-- Helper for Lemma 7.12: the composition preimage can be rewritten into the
preimage form required by `IsLebesgueMeasurableFunction`. -/
lemma helperForLemma_7_12_comp_preimage_eq_coe_preimage_image
    {n m p : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {W : Set (EuclideanSpace ℝ (Fin m))} {f : Ω → W}
    {g : W → EuclideanSpace ℝ (Fin p)}
    (V : Set (EuclideanSpace ℝ (Fin p))) :
    (fun x : Ω => g (f x)) ⁻¹' V =
      (fun x : Ω => ((f x : EuclideanSpace ℝ (Fin m)))) ⁻¹'
        (Subtype.val '' (g ⁻¹' V)) := by
  ext x
  constructor
  · intro hx
    exact ⟨f x, hx, rfl⟩
  · intro hx
    rcases hx with ⟨y, hy, hyEq⟩
    have hySubtype : y = f x := Subtype.ext hyEq
    simpa [hySubtype] using hy

/-- Helper for Lemma 7.12: once the preimage is rewritten, the representing set
identity from `hf` transfers directly to the composition. -/
lemma helperForLemma_7_12_image_preimage_inter_representation
    {n m p : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {W : Set (EuclideanSpace ℝ (Fin m))} {f : Ω → W}
    {g : W → EuclideanSpace ℝ (Fin p)}
    {V : Set (EuclideanSpace ℝ (Fin p))}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    (hEq :
      Subtype.val '' (((fun x : Ω => ((f x : EuclideanSpace ℝ (Fin m)))) ⁻¹'
          (Subtype.val '' (g ⁻¹' V)))) = Ω ∩ E) :
    Subtype.val '' ((fun x : Ω => g (f x)) ⁻¹' V) = Ω ∩ E := by
  calc
    Subtype.val '' ((fun x : Ω => g (f x)) ⁻¹' V) =
        Subtype.val '' (((fun x : Ω => ((f x : EuclideanSpace ℝ (Fin m)))) ⁻¹'
          (Subtype.val '' (g ⁻¹' V)))) := by
          rw [helperForLemma_7_12_comp_preimage_eq_coe_preimage_image
            (f := f) (g := g) V]
    _ = Ω ∩ E := hEq

/-- Lemma 7.12: let `Ω ⊆ ℝ^n` be measurable, let `W ⊆ ℝ^m` be open, and let
`f : Ω → W` be measurable. If `g : W → ℝ^p` is continuous, then the composition
`g ∘ f : Ω → ℝ^p` is measurable. -/
lemma isLebesgueMeasurableFunction_comp_continuous
    {n m p : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {W : Set (EuclideanSpace ℝ (Fin m))} (hW : IsOpen W)
    {f : Ω → W}
    (hf : IsLebesgueMeasurableFunction n m Ω
      (fun x => (f x : EuclideanSpace ℝ (Fin m))))
    {g : W → EuclideanSpace ℝ (Fin p)} (hg : Continuous g) :
    IsLebesgueMeasurableFunction n p Ω (fun x => g (f x)) := by
  refine ⟨hf.1, ?_⟩
  intro V hV
  have hOpenImage :
      IsOpen (Subtype.val '' (g ⁻¹' V)) :=
    helperForLemma_7_12_isOpen_image_preimage_subtypeVal hW hg hV
  rcases hf.2 (Subtype.val '' (g ⁻¹' V)) hOpenImage with ⟨E, hENull, hEq⟩
  refine ⟨E, hENull, ?_⟩
  exact
    helperForLemma_7_12_image_preimage_inter_representation
      (f := f) (g := g) (V := V) (E := E) hEq

/-- Helper for Lemma 7.13: `Subtype.val '' (f ⁻¹' V)` is contained in `Ω`. -/
lemma helperForLemma_7_13_preimageImage_subset
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ} (V : Set ℝ) :
    Subtype.val '' (f ⁻¹' V) ⊆ Ω := by
  rintro x ⟨xΩ, -, rfl⟩
  exact xΩ.2

/-- Helper for Lemma 7.13: complement rule for `V ↦ Subtype.val '' (f ⁻¹' V)`. -/
lemma helperForLemma_7_13_preimageImage_compl
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ} (V : Set ℝ) :
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

/-- Helper for Lemma 7.13: countable union rule for `V ↦ Subtype.val '' (f ⁻¹' V)`. -/
lemma helperForLemma_7_13_preimageImage_iUnion
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ} (V : ℕ → Set ℝ) :
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

/-- Helper for Lemma 7.13: null measurability of all superlevel preimages implies
null measurability of preimages of all Borel sets. -/
lemma helperForLemma_7_13_nullMeasurable_preimage_of_measurableSet
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ}
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hIoi : ∀ a : ℝ,
      MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' Set.Ioi a))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ V : Set ℝ, MeasurableSet V →
      MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' V))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  let C : Set (Set ℝ) := Set.range Set.Ioi
  have hInd :
      ∀ W : Set ℝ,
        @MeasurableSet ℝ (MeasurableSpace.generateFrom C) W →
          MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' W))
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
    intro W hW
    refine MeasurableSpace.generateFrom_induction (C := C)
      (p := fun W _ =>
        MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' W))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
      ?_ ?_ ?_ ?_ W hW
    · intro W hWC hWMeas
      rcases hWC with ⟨a, rfl⟩
      exact hIoi a
    · simpa using (MeasureTheory.nullMeasurableSet_empty :
        MeasureTheory.NullMeasurableSet
          (∅ : Set (EuclideanSpace ℝ (Fin n)))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    · intro W hWMeas hWNull
      rw [helperForLemma_7_13_preimageImage_compl (f := f) W]
      exact hΩ.diff hWNull
    · intro W hWMeas hWNull
      rw [helperForLemma_7_13_preimageImage_iUnion (f := f) W]
      exact MeasureTheory.NullMeasurableSet.iUnion hWNull
  intro V hV
  have hVGen : @MeasurableSet ℝ (MeasurableSpace.generateFrom C) V := by
    have hVborel : @MeasurableSet ℝ (borel ℝ) V := by
      simpa [BorelSpace.measurable_eq] using hV
    rw [borel_eq_generateFrom_Ioi] at hVborel
    simpa [C] using hVborel
  exact hInd V hVGen

/-- Lemma 7.13: let `Ω ⊆ ℝ^n` be Lebesgue measurable and `f : Ω → ℝ`. Then `f` is
Lebesgue measurable if and only if for every `a : ℝ`, the superlevel preimage
`{x ∈ Ω | a < f x}` is Lebesgue measurable in `Ω` (viewed in `ℝ^n` via
`Subtype.val '' (f ⁻¹' Set.Ioi a)`). -/
theorem isLebesgueMeasurableScalarFunction_iff_preimage_Ioi_nullMeasurable
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : Ω → ℝ} :
    MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) →
      (IsLebesgueMeasurableScalarFunction n Ω f ↔
        ∀ a : ℝ,
          MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' Set.Ioi a))
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro hΩ
  constructor
  · intro hf
    intro a
    rcases hf.2 (Set.Ioi a) isOpen_Ioi with ⟨E, hENull, hEq⟩
    have hInter :
        MeasureTheory.NullMeasurableSet (Ω ∩ E)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      hf.1.inter hENull
    exact hEq.symm ▸ hInter
  · intro hIoi
    refine ⟨hΩ, ?_⟩
    intro V hV
    have hPreNull :
        MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' V))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
      helperForLemma_7_13_nullMeasurable_preimage_of_measurableSet
        (f := f) hΩ hIoi V hV.measurableSet
    refine ⟨Subtype.val '' (f ⁻¹' V), hPreNull, ?_⟩
    have hSubset : Subtype.val '' (f ⁻¹' V) ⊆ Ω :=
      helperForLemma_7_13_preimageImage_subset (f := f) V
    ext x
    constructor
    · intro hx
      exact ⟨hSubset hx, hx⟩
    · intro hx
      exact hx.2

/-- Definition 7.7 (Measurable functions in the extended reals): let `Ω ⊆ ℝ^n` be
Lebesgue measurable and let `f : Ω → EReal` (where `EReal = ℝ ∪ {+∞, -∞}`).
Then `f` is measurable if for every `a : ℝ`, the superlevel preimage
`{x ∈ Ω | f x ∈ (a, +∞]}` is Lebesgue measurable in `ℝ^n`. -/
def IsLebesgueMeasurableExtendedRealFunction (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : Ω → EReal) : Prop :=
  MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ a : ℝ,
      MeasureTheory.NullMeasurableSet (Subtype.val '' (f ⁻¹' Set.Ioi (a : EReal)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))

/-- Helper for Lemma 7.14: the superlevel preimage of a pointwise `iSup` is the
union of superlevel preimages. -/
lemma helperForLemma_7_14_preimageImage_iSup_Ioi
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type*} [Countable ι]
    (u : ι → Ω → EReal) (a : ℝ) :
    Subtype.val '' ((fun x : Ω => ⨆ i : ι, u i x) ⁻¹' Set.Ioi (a : EReal)) =
      ⋃ i : ι, Subtype.val '' ((u i) ⁻¹' Set.Ioi (a : EReal)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨xΩ, hxSup, rfl⟩
    change (a : EReal) < ⨆ i : ι, u i xΩ at hxSup
    rcases (lt_iSup_iff.mp hxSup) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨xΩ, hi, rfl⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    rcases hxi with ⟨xΩ, hxi, rfl⟩
    refine ⟨xΩ, ?_, rfl⟩
    exact lt_of_lt_of_le hxi (le_iSup (fun j : ι => u j xΩ) i)

/-- Helper for Lemma 7.14: the superlevel preimage of a pointwise `iInf` can be
written as a countable union over rational thresholds of countable intersections. -/
lemma helperForLemma_7_14_preimageImage_iInf_Ioi_rat
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type*} [Countable ι]
    (u : ι → Ω → EReal) (a : ℝ) :
    Subtype.val '' ((fun x : Ω => ⨅ i : ι, u i x) ⁻¹' Set.Ioi (a : EReal)) =
      ⋃ q : {q : ℚ // (a : EReal) < (((q : ℚ) : ℝ) : EReal)},
        (Ω ∩ ⋂ i : ι,
          Subtype.val '' ((u i) ⁻¹' Set.Ioi ((((q.1 : ℚ) : ℝ) : EReal)))) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨xΩ, hxInf, rfl⟩
    rcases EReal.exists_rat_btwn_of_lt hxInf with ⟨q, haq, hqInf⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨q, haq⟩, ?_⟩
    refine ⟨xΩ.2, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    have hqi : (((q : ℚ) : ℝ) : EReal) < u i xΩ :=
      lt_of_lt_of_le hqInf (iInf_le (fun j : ι => u j xΩ) i)
    exact ⟨xΩ, hqi, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
    rcases hxq with ⟨hxΩ, hxInter⟩
    let xΩ : Ω := ⟨x, hxΩ⟩
    have hqle : ((((q.1 : ℚ) : ℝ) : EReal)) ≤ ⨅ i : ι, u i xΩ := by
      refine le_iInf ?_
      intro i
      have hxi :
          x ∈ Subtype.val '' ((u i) ⁻¹' Set.Ioi ((((q.1 : ℚ) : ℝ) : EReal))) :=
        (Set.mem_iInter.mp hxInter) i
      rcases hxi with ⟨y, hy, hyEq⟩
      have hyEq' : y = xΩ := by
        apply Subtype.ext
        calc
          (y : EuclideanSpace ℝ (Fin n)) = x := hyEq
          _ = xΩ := rfl
      have hy' : ((((q.1 : ℚ) : ℝ) : EReal)) < u i xΩ := by
        simpa [hyEq'] using hy
      exact hy'.le
    refine ⟨xΩ, ?_, rfl⟩
    exact lt_of_lt_of_le q.2 hqle

/-- Helper for Lemma 7.14: closure of extended-real measurability under countable
pointwise `iSup`. -/
lemma helperForLemma_7_14_isLebesgueMeasurable_iSup_of_superlevel
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type*} [Countable ι]
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (u : ι → Ω → EReal)
    (hIoi : ∀ i : ι, ∀ a : ℝ,
      MeasureTheory.NullMeasurableSet (Subtype.val '' ((u i) ⁻¹' Set.Ioi (a : EReal)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨆ i : ι, u i x) := by
  refine ⟨hΩ, ?_⟩
  intro a
  rw [helperForLemma_7_14_preimageImage_iSup_Ioi (u := u) (a := a)]
  exact MeasureTheory.NullMeasurableSet.iUnion (fun i => hIoi i a)

/-- Helper for Lemma 7.14: closure of extended-real measurability under countable
pointwise `iInf`. -/
lemma helperForLemma_7_14_isLebesgueMeasurable_iInf_of_superlevel
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type*} [Countable ι]
    (hΩ : MeasureTheory.NullMeasurableSet Ω
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (u : ι → Ω → EReal)
    (hIoi : ∀ i : ι, ∀ a : ℝ,
      MeasureTheory.NullMeasurableSet (Subtype.val '' ((u i) ⁻¹' Set.Ioi (a : EReal)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨅ i : ι, u i x) := by
  refine ⟨hΩ, ?_⟩
  intro a
  rw [helperForLemma_7_14_preimageImage_iInf_Ioi_rat (u := u) (a := a)]
  refine MeasureTheory.NullMeasurableSet.iUnion ?_
  intro q
  have hInter :
      MeasureTheory.NullMeasurableSet
        (⋂ i : ι, Subtype.val '' ((u i) ⁻¹' Set.Ioi ((((q.1 : ℚ) : ℝ) : EReal))))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
    refine MeasureTheory.NullMeasurableSet.iInter ?_
    intro i
    simpa using hIoi i (q.1 : ℚ)
  exact hΩ.inter hInter

/-- Helper for Lemma 7.14: rewrite `limsup` along `ℕ` as the tail `iInf-iSup`
formula indexed by subtypes. -/
lemma helperForLemma_7_14_limsup_nat_rewrite
    {α : Type*} [CompleteLattice α] (u : ℕ → α) :
    Filter.limsup u Filter.atTop =
      ⨅ N : ℕ, ⨆ k : {m : ℕ // N ≤ m}, u k.1 := by
  simpa [iSup_subtype] using (Filter.limsup_eq_iInf_iSup_of_nat (u := u))

/-- Helper for Lemma 7.14: rewrite `liminf` along `ℕ` as the tail `iSup-iInf`
formula indexed by subtypes. -/
lemma helperForLemma_7_14_liminf_nat_rewrite
    {α : Type*} [CompleteLattice α] (u : ℕ → α) :
    Filter.liminf u Filter.atTop =
      ⨆ N : ℕ, ⨅ k : {m : ℕ // N ≤ m}, u k.1 := by
  simpa [iInf_subtype] using (Filter.liminf_eq_iSup_iInf_of_nat (u := u))

/-- Lemma 7.14 (Limits of measurable functions are measurable): for a measurable
set `Ω ⊆ ℝ^n` and measurable maps `f_k : Ω → EReal`, the pointwise functions
`x ↦ ⨆ k, f_k x`, `x ↦ ⨅ k, f_k x`, `x ↦ ⨅ N, ⨆ k≥N, f_k x`, and
`x ↦ ⨆ N, ⨅ k≥N, f_k x` (cf. (7.u161), (7.u162)) are measurable. In particular,
any pointwise limit `g` of `(f_k)` is measurable. -/
theorem isLebesgueMeasurableExtendedRealFunction_iSup_iInf_limsup_liminf
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : ℕ → Ω → EReal}
    (hf : ∀ k : ℕ, IsLebesgueMeasurableExtendedRealFunction n Ω (f k)) :
    IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨆ k : ℕ, f k x) ∧
      IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨅ k : ℕ, f k x) ∧
      IsLebesgueMeasurableExtendedRealFunction n Ω
        (fun x => ⨅ N : ℕ, ⨆ k : {m : ℕ // N ≤ m}, f k.1 x) ∧
      IsLebesgueMeasurableExtendedRealFunction n Ω
        (fun x => ⨆ N : ℕ, ⨅ k : {m : ℕ // N ≤ m}, f k.1 x) ∧
      ∀ g : Ω → EReal,
        (∀ x : Ω, Filter.Tendsto (fun k : ℕ => f k x) Filter.atTop (nhds (g x))) →
          IsLebesgueMeasurableExtendedRealFunction n Ω g := by
  have hΩ :
      MeasureTheory.NullMeasurableSet Ω
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
    (hf 0).1
  have hSup :
      IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨆ k : ℕ, f k x) :=
    helperForLemma_7_14_isLebesgueMeasurable_iSup_of_superlevel
      (hΩ := hΩ) (u := f) (hIoi := fun k a => (hf k).2 a)
  have hInf :
      IsLebesgueMeasurableExtendedRealFunction n Ω (fun x => ⨅ k : ℕ, f k x) :=
    helperForLemma_7_14_isLebesgueMeasurable_iInf_of_superlevel
      (hΩ := hΩ) (u := f) (hIoi := fun k a => (hf k).2 a)
  have hTailSup :
      ∀ N : ℕ,
        IsLebesgueMeasurableExtendedRealFunction n Ω
          (fun x => ⨆ k : {m : ℕ // N ≤ m}, f k.1 x) := by
    intro N
    exact helperForLemma_7_14_isLebesgueMeasurable_iSup_of_superlevel
      (hΩ := hΩ) (u := fun k : {m : ℕ // N ≤ m} => f k.1)
      (hIoi := fun k a => (hf k.1).2 a)
  have hTailInf :
      ∀ N : ℕ,
        IsLebesgueMeasurableExtendedRealFunction n Ω
          (fun x => ⨅ k : {m : ℕ // N ≤ m}, f k.1 x) := by
    intro N
    exact helperForLemma_7_14_isLebesgueMeasurable_iInf_of_superlevel
      (hΩ := hΩ) (u := fun k : {m : ℕ // N ≤ m} => f k.1)
      (hIoi := fun k a => (hf k.1).2 a)
  have hLimsup :
      IsLebesgueMeasurableExtendedRealFunction n Ω
        (fun x => ⨅ N : ℕ, ⨆ k : {m : ℕ // N ≤ m}, f k.1 x) :=
    helperForLemma_7_14_isLebesgueMeasurable_iInf_of_superlevel
      (hΩ := hΩ)
      (u := fun N : ℕ => fun x : Ω => ⨆ k : {m : ℕ // N ≤ m}, f k.1 x)
      (hIoi := fun N a => (hTailSup N).2 a)
  have hLiminf :
      IsLebesgueMeasurableExtendedRealFunction n Ω
        (fun x => ⨆ N : ℕ, ⨅ k : {m : ℕ // N ≤ m}, f k.1 x) :=
    helperForLemma_7_14_isLebesgueMeasurable_iSup_of_superlevel
      (hΩ := hΩ)
      (u := fun N : ℕ => fun x : Ω => ⨅ k : {m : ℕ // N ≤ m}, f k.1 x)
      (hIoi := fun N a => (hTailInf N).2 a)
  refine ⟨hSup, hInf, hLimsup, hLiminf, ?_⟩
  intro g hlim
  have hEq :
      g = (fun x => ⨅ N : ℕ, ⨆ k : {m : ℕ // N ≤ m}, f k.1 x) := by
    funext x
    have hLimsupEq : Filter.limsup (fun k : ℕ => f k x) Filter.atTop = g x :=
      (hlim x).limsup_eq
    calc
      g x = Filter.limsup (fun k : ℕ => f k x) Filter.atTop := by
        exact hLimsupEq.symm
      _ = ⨅ N : ℕ, ⨆ k : {m : ℕ // N ≤ m}, f k.1 x := by
        simpa using helperForLemma_7_14_limsup_nat_rewrite (u := fun k : ℕ => f k x)
  simpa [hEq] using hLimsup

/-- Proposition 7.17: let `f : ℝ^n → ℝ` be Lebesgue measurable, and let
`g : ℝ^n → ℝ`. If there exists a Lebesgue null set `A ⊆ ℝ^n` such that
`f x = g x` for all `x ∈ ℝ^n \ A`, then `g` is Lebesgue measurable. -/
theorem aemeasurable_of_eq_outside_nullSet
    {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hfg : ∃ A : Set (EuclideanSpace ℝ (Fin n)),
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) A = 0 ∧
        ∀ x : EuclideanSpace ℝ (Fin n), x ∉ A → f x = g x) :
    AEMeasurable g
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) := MeasureTheory.volume
  rcases hfg with ⟨A, hA0, hEqOutside⟩
  have hNotMemA_ae : ∀ᵐ x ∂μ, x ∉ A := by
    rw [MeasureTheory.ae_iff]
    simpa [μ] using hA0
  have hfg_ae : f =ᶠ[MeasureTheory.ae μ] g := by
    refine hNotMemA_ae.mono ?_
    intro x hx
    exact hEqOutside x hx
  have hfμ : AEMeasurable f μ := by
    simpa [μ] using hf
  have hgμ : AEMeasurable g μ := hfμ.congr hfg_ae
  simpa [μ] using hgμ


end Section05
end Chap07
