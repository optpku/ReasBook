module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_14_2
import stacks_project.Chap05.Lemma_5_15_10
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_24_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} {C : Cone F}
variable [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for constructible descent in cofiltered limits of spectral spaces:
- primary domain: constructible subsets, compact opens, and spectral maps in inverse limits of
  spectral spaces;
- sampled owner-level declarations:
  `Topology.IsConstructible.empty_union_induction`,
  `IsSpectralMap.isConstructible_preimage`,
  `compact_open_eq_preimage_of_isLimit`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction: the predicate `Topology.IsConstructible` on subsets, together with the
  canonical `CompactOpens` owner for open constructible subsets and `Closeds` for the closed
  companion case;
- primitive-vs-derived split:
  primitive data: a subset of the limit together with the owner predicate `IsConstructible`;
  derived API: the compact-open and closed refinements of the descended stage subset.

Layer triage:
- `source-facing`: a constructible subset of the limit comes via pullback from some stage;
- `core/canonical`: the owner predicate `Topology.IsConstructible`, together with the chapter-level
  compact-open descent theorem and spectral-limit owner for the ambient spaces;
- `bridge/view`: the open and closed companion forms, which should use `CompactOpens` and
  `Closeds` rather than storing openness or closedness as primitive fields.
-/

/-- Helper for Lemma 5.24.4: a constructible open subset of the limit descends to a compact open
subset on some stage. -/
private lemma exists_stage_compact_open_of_constructible_open
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt} (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  let _ : SpectralSpace C.pt :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (F := F) (C := C) hC
      (fun {j k} a ↦ hF a)
  -- On the compact spectral limit, retrocompactness upgrades constructible openness to compactness.
  have hE_compact : IsCompact E := by
    exact hE.isRetrocompact.isCompact
  let W : CompactOpens C.pt := ⟨⟨E, hE_compact⟩, hE_open⟩
  obtain ⟨i, Ui, hUi⟩ := compact_open_eq_preimage_of_isLimit (C := C) hC W
  have hUi' : E = C.π.app i ⁻¹' (Ui : Set (F.obj i)) := by
    simpa [W] using hUi
  let S : Set (Set (F.obj i)) := {s | IsOpen s ∧ IsCompact s ∧ s ⊆ (Ui : Set (F.obj i))}
  have hUi_eq : (Ui : Set (F.obj i)) = ⋃₀ S := by
    simpa [S, and_left_comm, and_assoc] using
      (PrespectralSpace.isTopologicalBasis (X := F.obj i)).open_eq_sUnion' Ui.isOpen
  let V : {s : Set (F.obj i) // s ∈ S} → CompactOpens (F.obj i) :=
    fun s ↦ ⟨⟨s.1, s.2.2.1⟩, s.2.1⟩
  have hOpen : ∀ s : {s : Set (F.obj i) // s ∈ S},
      IsOpen (C.π.app i ⁻¹' (V s : Set (F.obj i))) := by
    intro s
    exact (V s).isOpen.preimage (C.π.app i).hom.continuous
  have hCover : E ⊆ ⋃ s : {s : Set (F.obj i) // s ∈ S}, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
    intro x hx
    rw [hUi'] at hx
    change C.π.app i x ∈ (Ui : Set (F.obj i)) at hx
    rw [hUi_eq] at hx
    rcases mem_sUnion.1 hx with ⟨s, hsS, hsx⟩
    exact mem_iUnion.2 ⟨⟨s, hsS⟩, hsx⟩
  obtain ⟨t, ht⟩ := hE_compact.elim_finite_subcover
    (fun s : {s : Set (F.obj i) // s ∈ S} ↦ C.π.app i ⁻¹' (V s : Set (F.obj i))) hOpen hCover
  let Ei : CompactOpens (F.obj i) := t.sup V
  refine ⟨i, Ei, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
      simpa [Ei] using hx
    rw [hUi']
    rw [Set.mem_preimage]
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨s, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hs, hsx⟩
    exact s.2.2.2 hsx
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
      have htx := ht hx
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨s, htx⟩
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨hs, hsx⟩
      exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs, hsx⟩⟩
    simpa [Ei] using hx'

/-- Helper for Lemma 5.24.4: two constructible subsets that already descend to stages can be
pulled back to a common refinement stage and united there. -/
private lemma merge_constructible_stage_descents
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E E' : Set C.pt} {i j : J} {Ei : Set (F.obj i)} {Ej : Set (F.obj j)}
    (hEi_constructible : IsConstructible Ei) (hEj_constructible : IsConstructible Ej)
    (hEi : C.π.app i ⁻¹' Ei = E) (hEj : C.π.app j ⁻¹' Ej = E') :
    ∃ (k : J) (Ek : Set (F.obj k)), IsConstructible Ek ∧ C.π.app k ⁻¹' Ek = E ∪ E' := by
  obtain ⟨k, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Ek : Set (F.obj k) := (F.map a) ⁻¹' Ei ∪ (F.map b) ⁻¹' Ej
  refine ⟨k, Ek, ?_, ?_⟩
  · -- Spectral transition maps preserve constructibility, so the common-refinement union stays constructible.
    exact ((hF a).isConstructible_preimage hEi_constructible).union
      ((hF b).isConstructible_preimage hEj_constructible)
  · have hπ {k l : J} (f : k ⟶ l) (x : C.pt) :
        C.π.app l x = F.map f (C.π.app k x) := by
      rw [← CategoryTheory.comp_apply]
      exact congrArg (fun g : C.pt ⟶ F.obj l ↦ g x) (C.w f).symm
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · left
        rw [← hEi]
        change C.π.app i x ∈ Ei
        rw [hπ a x]
        exact hx
      · right
        rw [← hEj]
        change C.π.app j x ∈ Ej
        rw [hπ b x]
        exact hx
    · intro hx
      rcases hx with hx | hx
      · left
        rw [← hEi] at hx
        change C.π.app i x ∈ Ei at hx
        change F.map a (C.π.app k x) ∈ Ei
        rw [← hπ a x]
        exact hx
      · right
        rw [← hEj] at hx
        change C.π.app j x ∈ Ej at hx
        change F.map b (C.π.app k x) ∈ Ej
        rw [← hπ b x]
        exact hx

/-- Helper for Lemma 5.24.4: a constructible closed subset of the limit descends to a closed
constructible subset on some stage. -/
private lemma exists_stage_closed_of_constructible_closed
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt} (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Descend the open complement first, then take the stagewise complement.
  obtain ⟨i, Ui, hUi⟩ :=
    exists_stage_compact_open_of_constructible_open (C := C) hC hF hE.compl hE_closed.isOpen_compl
  have hUi_closed : IsClosed ((Ui : Set (F.obj i))ᶜ) := Ui.isOpen.isClosed_compl
  let Ei : Closeds (F.obj i) := ⟨(Ui : Set (F.obj i))ᶜ, hUi_closed⟩
  refine ⟨i, Ei, ?_, ?_⟩
  · -- Complements of compact opens are constructible on each spectral stage.
    exact (Ui.isCompact.isConstructible Ui.isOpen).compl
  · ext x
    constructor
    · intro hx
      change C.π.app i x ∉ (Ui : Set (F.obj i)) at hx
      by_contra hxE
      have hxE' : x ∈ Eᶜ := hxE
      rw [← hUi] at hxE'
      exact hx (by simpa using hxE')
    · intro hxE
      change C.π.app i x ∉ (Ui : Set (F.obj i))
      intro hxUi
      have hxEcompl : x ∈ Eᶜ := by
        rw [← hUi]
        exact hxUi
      exact hxEcompl hxE

-- Proof sketch: argue first for constructible opens by upgrading them to compact opens on the
-- spectral limit and descending them to a single stage after refining the stagewise open cover by
-- finitely many compact-open basis pieces; then pass to constructible closed sets by complements,
-- and finally use constructible induction with a common-refinement union step.
/-- Lemma 5.24.4: a constructible subset of the limit of a cofiltered diagram of spectral spaces
with spectral transition maps comes by pullback from a constructible subset on some stage. -/
theorem constructible_eq_preimage_of_isLimit
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) :
    ∃ (i : J) (Ei : Set (F.obj i)), IsConstructible Ei ∧ C.π.app i ⁻¹' Ei = E := by
  -- Generate constructible subsets from open retrocompact pieces, unions, and complements.
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hU_open hU_retro =>
      have hU_constructible : IsConstructible U := hU_retro.isConstructible hU_open
      obtain ⟨i, Ei, hEi⟩ :=
        exists_stage_compact_open_of_constructible_open (C := C) hC hF hU_constructible hU_open
      refine ⟨i, Ei, ?_, hEi⟩
      -- Compact opens on spectral spaces are constructible.
      exact Ei.isCompact.isConstructible Ei.isOpen
  | union s hs t ht hs' ht' =>
      rcases hs' with ⟨i, Ei, hEi_constructible, hEi⟩
      rcases ht' with ⟨j, Ej, hEj_constructible, hEj⟩
      -- Merge the two descended pieces on a common refinement stage.
      exact merge_constructible_stage_descents (C := C) hF hEi_constructible hEj_constructible hEi hEj
  | compl s hs hs' =>
      rcases hs' with ⟨i, Ei, hEi_constructible, hEi⟩
      refine ⟨i, Eiᶜ, hEi_constructible.compl, ?_⟩
      -- Complements stay on the same stage because inverse image commutes with complement.
      ext x
      constructor
      · intro hx
        change C.π.app i x ∉ Ei at hx
        intro hsx
        have hsx' : x ∈ C.π.app i ⁻¹' Ei := by
          rw [hEi]
          exact hsx
        exact hx (by simpa using hsx')
      · intro hx
        change C.π.app i x ∉ Ei
        intro hxEi
        apply hx
        rw [← hEi]
        exact hxEi

-- Proof sketch: package the open constructible subset as a compact open on the spectral limit,
-- descend it by the helper above, and return the resulting compact-open stage subset.
/-- If the constructible subset in Lemma 5.24.4 is open, then the descended constructible subset
can be chosen compact open. -/
theorem open_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Reuse the compact-open descent helper proved above.
  simpa using exists_stage_compact_open_of_constructible_open (C := C) hC hF hE hE_open

-- Proof sketch: apply the open descent result to the complement and then complement the stagewise
-- compact open.
/-- If the constructible subset in Lemma 5.24.4 is closed, then the descended constructible subset
can be chosen closed. -/
theorem closed_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Reuse the closed-case helper obtained by complementing the open descent.
  simpa using exists_stage_closed_of_constructible_closed (C := C) hC hF hE hE_closed

end
