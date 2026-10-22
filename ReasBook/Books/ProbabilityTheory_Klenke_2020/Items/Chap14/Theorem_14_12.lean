/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory MeasurableSpace Set

universe u v

variable {I : Type u} {Ω : I → Type v} [mΩ : ∀ i, MeasurableSpace (Ω i)]
variable {E : ∀ i, Set (Set (Ω i))}

/- Semantic recall found `generateFrom_pi`, `generateFrom_eq_pi`, and
`MeasureTheory.generateFrom_squareCylinders`; local verification uses
`MeasurableSpace.pi_eq_generateFrom_projections` while this item keeps Klenke's source-facing
finite-product evaluation-preimage clause and rectangular-cylinder families as the public API over
that verified mathlib owner. -/

/-- A box in a finite product is measurable once each coordinate section is measurable. -/
private theorem measurableSet_piBox {J : Finset I} {A : ∀ j : J, Set (Ω j.1)}
    (hA : ∀ j : J, MeasurableSet (A j)) :
    MeasurableSet (Set.pi univ A) := by
  -- Write the box as the intersection of its coordinate projection preimages.
  rw [univ_pi_eq_iInter]
  refine MeasurableSet.iInter fun j ↦ ?_
  exact (hA j).preimage (measurable_pi_apply j)

-- Route correction: part (iii) needs a genuine mathlib `IsPiSystem` on the restricted-union
-- generator, so the proof below adapts the intersection construction from Lemma 14.11 directly.
omit mΩ in
/-- If each coordinate family `E i` is a `π`-system, then the union of all finite-base restricted
rectangular cylinders is again a `π`-system. -/
private theorem restrictedCylinderUnion_isPiSystem
    (hE_pi : ∀ i, IsPiSystem (E i)) :
    IsPiSystem (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) := by
  classical
  intro s hs t ht hst
  rw [mem_iUnion] at hs ht ⊢
  rcases hs with ⟨J₁, hs⟩
  rcases ht with ⟨J₂, ht⟩
  rcases hs with ⟨A₁, hA₁, rfl⟩
  rcases ht with ⟨A₂, hA₂, rfl⟩
  rcases hst with ⟨x, hx⟩
  have hx₁ : x ∈ cylinder J₁ (Set.pi univ A₁) := hx.1
  have hx₂ : x ∈ cylinder J₂ (Set.pi univ A₂) := hx.2
  rw [mem_cylinder, Set.mem_pi] at hx₁ hx₂
  have hA₁' : ∀ j : J₁, A₁ j ∈ E j.1 := by
    simpa [Set.mem_pi] using hA₁
  have hA₂' : ∀ j : J₂, A₂ j ∈ E j.1 := by
    simpa [Set.mem_pi] using hA₂
  let K : Finset I := J₁ ∪ J₂
  let B : ∀ j : K, Set (Ω j.1) := fun j ↦
    if hj₁ : j.1 ∈ J₁ then
      if hj₂ : j.1 ∈ J₂ then
        A₁ ⟨j.1, hj₁⟩ ∩ A₂ ⟨j.1, hj₂⟩
      else
        A₁ ⟨j.1, hj₁⟩
    else
      A₂ ⟨j.1, by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁⟩
  have hB : B ∈ Set.pi univ (fun j : K ↦ E j.1) := by
    rw [Set.mem_pi]
    intro j _
    dsimp [B]
    by_cases hj₁ : j.1 ∈ J₁
    · by_cases hj₂ : j.1 ∈ J₂
      · have hx₁j : x j.1 ∈ A₁ ⟨j.1, hj₁⟩ := hx₁ ⟨j.1, hj₁⟩ (mem_univ _)
        have hx₂j : x j.1 ∈ A₂ ⟨j.1, hj₂⟩ := hx₂ ⟨j.1, hj₂⟩ (mem_univ _)
        have hne : (A₁ ⟨j.1, hj₁⟩ ∩ A₂ ⟨j.1, hj₂⟩ : Set (Ω j.1)).Nonempty :=
          ⟨x j.1, hx₁j, hx₂j⟩
        simpa [B, hj₁, hj₂] using
          hE_pi j.1 (A₁ ⟨j.1, hj₁⟩) (hA₁' ⟨j.1, hj₁⟩)
            (A₂ ⟨j.1, hj₂⟩) (hA₂' ⟨j.1, hj₂⟩) hne
      · simpa [B, hj₁, hj₂] using hA₁' ⟨j.1, hj₁⟩
    · have hj₂ : j.1 ∈ J₂ := by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁
      simpa [B, hj₁, hj₂] using hA₂' ⟨j.1, hj₂⟩
  refine ⟨K, B, hB, ?_⟩
  -- Compare membership coordinatewise after enlarging the finite base to `K = J₁ ∪ J₂`.
  ext y
  change y ∈ cylinder K (Set.pi univ B) ↔
    y ∈ cylinder J₁ (Set.pi univ A₁) ∩ cylinder J₂ (Set.pi univ A₂)
  constructor
  · intro hy
    rw [mem_cylinder, Set.mem_pi] at hy
    rw [mem_inter_iff, mem_cylinder, mem_cylinder, Set.mem_pi, Set.mem_pi]
    refine ⟨?_, ?_⟩
    · intro j _
      have hyj := hy ⟨j.1, Finset.mem_union.mpr <| Or.inl j.2⟩ (mem_univ _)
      by_cases hj₂ : j.1 ∈ J₂
      · have hyj' : y j.1 ∈ A₁ j ∩ A₂ ⟨j.1, hj₂⟩ := by
          simpa [B, K, j.2, hj₂] using hyj
        exact hyj'.1
      · simpa [B, K, j.2, hj₂] using hyj
    · intro j _
      have hyj := hy ⟨j.1, Finset.mem_union.mpr <| Or.inr j.2⟩ (mem_univ _)
      by_cases hj₁ : j.1 ∈ J₁
      · have hyj' : y j.1 ∈ A₁ ⟨j.1, hj₁⟩ ∩ A₂ j := by
          simpa [B, K, hj₁, j.2] using hyj
        exact hyj'.2
      · simpa [B, K, hj₁, j.2] using hyj
  · intro hy
    rw [mem_cylinder, Set.mem_pi]
    rw [mem_inter_iff, mem_cylinder, mem_cylinder, Set.mem_pi, Set.mem_pi] at hy
    intro j _
    dsimp [B]
    by_cases hj₁ : j.1 ∈ J₁
    · have hy₁ : y j.1 ∈ A₁ ⟨j.1, hj₁⟩ := hy.1 ⟨j.1, hj₁⟩ (mem_univ _)
      by_cases hj₂ : j.1 ∈ J₂
      · have hy₂ : y j.1 ∈ A₂ ⟨j.1, hj₂⟩ := hy.2 ⟨j.1, hj₂⟩ (mem_univ _)
        simpa [B, K, hj₁, hj₂] using And.intro hy₁ hy₂
      · simpa [B, hj₁, hj₂] using hy₁
    · have hj₂ : j.1 ∈ J₂ := by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁
      simpa [B, hj₁, hj₂] using hy.2 ⟨j.1, hj₂⟩ (mem_univ _)

/-- Helper for item (i): the bad finite-box counterexample uses one nontrivial coordinate and one
trivial coordinate. -/
private def finitePiBoxCounterexampleSpace : Bool → Type
  | true => Bool
  | false => PUnit

/-- Helper for item (i): the nontrivial coordinate is generated by `{true}`, while the other
coordinate generator is just `{∅}`. -/
private def finitePiBoxCounterexampleGenerator :
    ∀ i : Bool, Set (Set (finitePiBoxCounterexampleSpace i))
  | true => {({true} : Set Bool)}
  | false => {(∅ : Set PUnit)}

/-- Helper for item (i): each counterexample coordinate carries the `σ`-algebra generated by its
chosen generator family. -/
private abbrev finitePiBoxCounterexampleMeasurableSpace (i : Bool) :
    MeasurableSpace (finitePiBoxCounterexampleSpace i) :=
  generateFrom (finitePiBoxCounterexampleGenerator i)

/-- Helper for item (i): local measurable-space instance for the finite-box counterexample. -/
private instance finitePiBoxCounterexampleInst (i : Bool) :
    MeasurableSpace (finitePiBoxCounterexampleSpace i) :=
  finitePiBoxCounterexampleMeasurableSpace i

/-- Counterexample: the printed source clause `(i)` is source-defective as stated.
Without any `univ ∈ E i` filler hypothesis, the literal finite-box generator formula is false; a
two-coordinate family already gives a counterexample. -/
private theorem finitePiBoxGeneratorCounterexampleAux :
    generateFrom
      ((fun A :
          ∀ j : (Finset.univ : Finset Bool), Set (finitePiBoxCounterexampleSpace j.1) ↦
            Set.pi univ A) ''
        Set.pi univ
          (fun j : (Finset.univ : Finset Bool) ↦ finitePiBoxCounterexampleGenerator j.1)) ≠
      (MeasurableSpace.pi :
        MeasurableSpace ((j : (Finset.univ : Finset Bool)) →
          finitePiBoxCounterexampleSpace j.1)) := by
  classical
  let J : Finset Bool := Finset.univ
  let jFalse : J := ⟨false, by simp [J]⟩
  let jTrue : J := ⟨true, by simp [J]⟩
  let G : Set (Set ((j : J) → finitePiBoxCounterexampleSpace j.1)) :=
    ((fun A : ∀ j : J, Set (finitePiBoxCounterexampleSpace j.1) ↦ Set.pi univ A) ''
      Set.pi univ (fun j : J ↦ finitePiBoxCounterexampleGenerator j.1))
  have hLeft :
      generateFrom G =
        (⊥ : MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1)) := by
    refine le_antisymm ?_ bot_le
    refine MeasurableSpace.generateFrom_le ?_
    intro t ht
    rcases ht with ⟨A, hA, rfl⟩
    rw [Set.mem_pi] at hA
    have hFalse : A jFalse = ∅ := by
      simpa [jFalse, finitePiBoxCounterexampleGenerator] using hA jFalse (mem_univ _)
    -- The `false` coordinate contributes the empty section, so the whole box is empty.
    have hBox : Set.pi univ A = (∅ : Set ((j : J) → finitePiBoxCounterexampleSpace j.1)) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_empty_iff_false]
        rw [Set.mem_pi] at hx
        have hxFalse : x jFalse ∈ A jFalse := hx jFalse (mem_univ _)
        simp [hFalse] at hxFalse
      · intro hx
        simp at hx
    simp [hBox]
  let s : Set ((j : J) → finitePiBoxCounterexampleSpace j.1) :=
    Function.eval jTrue ⁻¹' ({true} : Set Bool)
  have hs_pi :
      MeasurableSet[MeasurableSpace.pi] s := by
    have hTrue :
        MeasurableSet[finitePiBoxCounterexampleMeasurableSpace true]
          ({true} : Set Bool) := by
      exact MeasurableSpace.measurableSet_generateFrom (by exact Set.mem_singleton _)
    -- The first-coordinate singleton stays measurable in the product via the evaluation map.
    exact hTrue.preimage (show Measurable (Function.eval jTrue) from measurable_pi_apply jTrue)
  have hs_not_bot :
      ¬MeasurableSet[(⊥ : MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1))] s := by
    let y : (j : J) → finitePiBoxCounterexampleSpace j.1 := fun j ↦ by
      rcases j with ⟨j, hj⟩
      cases j
      · exact PUnit.unit
      · exact false
    have hx : Function.update y jTrue true ∈ s := by
      change true ∈ ({true} : Set Bool)
      simp
    have hy : y ∉ s := by
      change false ∉ ({true} : Set Bool)
      simp
    -- A set measurable for `⊥` must be either `∅` or `univ`, but this section is neither.
    rw [MeasurableSpace.measurableSet_bot_iff]
    rintro (hEmpty | hUniv)
    · have : False := by
        rw [hEmpty] at hx
        simp at hx
      exact this
    · have : y ∈ s := by
        simp [hUniv]
      exact hy this
  intro hEq
  -- The alleged equality would force the nontrivial product `σ`-algebra to collapse to `⊥`.
  have hPiBot :
      (MeasurableSpace.pi :
        MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1)) =
        (⊥ : MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1)) := by
    calc
      (MeasurableSpace.pi :
          MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1)) =
          generateFrom G := hEq.symm
      _ = ⊥ := hLeft
  have hs_bot :
      MeasurableSet[(⊥ : MeasurableSpace ((j : J) → finitePiBoxCounterexampleSpace j.1))] s := by
    rw [← hPiBot]
    exact hs_pi
  exact hs_not_bot hs_bot

-- The counterexample above already lives on a finite product indexed by `J`; it shows that the
-- literal box family is too small unless the unused coordinates admit `univ` as fillers. The
-- next helpers record the corrected one-coordinate-cylinder bridge and the corresponding literal
-- box consequence under that extra hypothesis.

omit mΩ in
/-- Helper for item (i): a one-coordinate evaluation preimage is the full box with that
section and `univ` elsewhere. -/
private theorem evalPreimage_eq_pi_update {J : Finset I} [DecidableEq J] (j : J)
    (s : Set (Ω j.1)) :
    Function.eval j ⁻¹' s =
      Set.pi univ (Function.update (fun k : J ↦ (univ : Set (Ω k.1))) j s) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_pi]
    intro k _
    by_cases hk : k = j
    · subst hk
      simpa [Function.eval, Function.update] using hx
    · simp [Function.update, hk]
  · intro hx
    rw [Set.mem_pi] at hx
    simpa [Function.eval, Function.update] using hx j (mem_univ _)

-- For a fixed finite product over `J`, the source-facing finite-product generator route is the
-- family of one-coordinate evaluation preimages coming from the factor generators.
/-- Auxiliary finite-product generator bridge for source clause (1). -/
private theorem generateFromEvalPreimagesEqFiniteProduct
    (J : Finset I) (hE : ∀ j : J, generateFrom (E j.1) = mΩ j.1) :
    generateFrom
      (⋃ j : J, (fun s : Set (Ω j.1) ↦ Function.eval j ⁻¹' s) '' E j.1) =
      (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1)) := by
  refine le_antisymm ?_ ?_
  · -- Each factor generator yields a measurable evaluation preimage in the finite product.
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rw [mem_iUnion] at hs
    rcases hs with ⟨j, hs⟩
    rcases hs with ⟨t, ht, rfl⟩
    have ht_meas : MeasurableSet[mΩ j.1] t := by
      rw [← hE j]
      exact measurableSet_generateFrom ht
    exact ht_meas.preimage (measurable_pi_apply j)
  · -- Conversely, the standard projection generators already lie in this generated `σ`-algebra.
    rw [MeasurableSpace.pi_eq_generateFrom_projections]
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases hs with ⟨j, t, ht, rfl⟩
    let ej : ((k : J) → Ω k.1) → Ω j.1 := fun x ↦ x j
    have hcomap :
        MeasurableSpace.comap ej (mΩ j.1) ≤
          generateFrom (⋃ j : J, (fun s : Set (Ω j.1) ↦ Function.eval j ⁻¹' s) '' E j.1) := by
      simpa [ej] using
        (show MeasurableSpace.comap (fun x : ((k : J) → Ω k.1) ↦ x j) (mΩ j.1) ≤
            generateFrom (⋃ j : J, (fun s : Set (Ω j.1) ↦ Function.eval j ⁻¹' s) '' E j.1) from by
          rw [← hE j, MeasurableSpace.comap_generateFrom]
          refine MeasurableSpace.generateFrom_le ?_
          rintro _ ⟨u, hu, rfl⟩
          simpa [Function.eval] using
            measurableSet_generateFrom (Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hu⟩))
    have ht_comap :
        MeasurableSet[MeasurableSpace.comap ej (mΩ j.1)] (ej ⁻¹' t) := by
      exact ht.preimage (comap_measurable ej)
    simpa [ej, Function.eval] using hcomap _ ht_comap

-- Proof sketch: this is the first equality from source item (ii), now stated for the
-- source-facing finite-base rectangular cylinders rather than total square cylinders.
/-- Helper for item (ii), first equality: measurable rectangular cylinders with finite
base generate the ambient product `σ`-algebra. -/
private theorem generateFrom_rectangularCylinderSets_eq_product :
    generateFrom
      (⋃ J : Finset I, rectangularCylinderSetsWithBase J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) := by
  refine le_antisymm ?_ ?_
  · -- Each measurable rectangular cylinder is measurable in the ambient product `σ`-algebra.
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rw [mem_iUnion] at hs
    rcases hs with ⟨J, hsJ⟩
    rcases hsJ with ⟨A, hA, rfl⟩
    have hAmeas : ∀ j : J, MeasurableSet (A j) := by
      simpa [Set.mem_pi] using hA
    have hBox : MeasurableSet (Set.pi univ A) := measurableSet_piBox hAmeas
    simpa [MeasureTheory.cylinder] using hBox.preimage (Finset.measurable_restrict J)
  · -- A one-coordinate measurable preimage already belongs to the singleton-base rectangular
    -- family, so the projection generators suffice.
    rw [MeasurableSpace.pi_eq_generateFrom_projections]
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases hs with ⟨i, t, ht, rfl⟩
    apply measurableSet_generateFrom
    refine Set.mem_iUnion.mpr ⟨({i} : Finset I), ?_⟩
    let A : ∀ j : ({i} : Finset I), Set (Ω j.1) := fun j ↦ by
      rcases j with ⟨j, hj⟩
      have hj' : j = i := by
        simpa using hj
      subst hj'
      exact t
    refine ⟨A, ?_, ?_⟩
    · rw [Set.mem_pi]
      intro j _
      rcases j with ⟨j, hj⟩
      have hj' : j = i := by
        simpa using hj
      subst hj'
      simpa using ht
    · ext x
      constructor
      · intro hx
        rw [MeasureTheory.mem_cylinder, Set.mem_pi] at hx
        simpa [A] using hx ⟨i, by simp⟩ (mem_univ _)
      · intro hx
        rw [MeasureTheory.mem_cylinder, Set.mem_pi]
        intro j _
        rcases j with ⟨j, hj⟩
        have hj' : j = i := by
          simpa using hj
        subst hj'
        simpa [A] using hx

-- Proof sketch: for the second equality in source item (ii), use the finite-base restricted
-- cylinder formulation above on each finite base, then take the union over all finite bases.
/-- Helper for item (ii), second equality: if each `E i` generates the factor
`σ`-algebra, then the restricted rectangular cylinders with finite base also generate the ambient
product `σ`-algebra. -/
private theorem generateFrom_restrictedRectangularCylinderSets_eq_product
    (hE : ∀ i, generateFrom (E i) = mΩ i)
    :
    generateFrom (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) := by
  refine le_antisymm ?_ ?_
  · -- Each restricted rectangular cylinder is measurable in the ambient product `σ`-algebra.
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rw [mem_iUnion] at hs
    rcases hs with ⟨J, hsJ⟩
    rcases hsJ with ⟨A, hA, rfl⟩
    have hA' : ∀ j : J, A j ∈ E j.1 := by
      simpa [Set.mem_pi] using hA
    have hAmeas : ∀ j : J, MeasurableSet (A j) := by
      intro j
      have hAj_meas : @MeasurableSet (Ω j.1) (generateFrom (E j.1)) (A j) :=
        measurableSet_generateFrom (hA' j)
      rwa [hE j.1] at hAj_meas
    have hBox : MeasurableSet (Set.pi univ A) := measurableSet_piBox hAmeas
    simpa [MeasureTheory.cylinder] using hBox.preimage (Finset.measurable_restrict J)
  · -- The one-coordinate `E i`-generators already control the evaluation pullbacks, so the
    -- restricted family generates the full product `σ`-algebra.
    rw [MeasurableSpace.pi_eq_generateFrom_projections]
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases hs with ⟨i, t, ht, rfl⟩
    have hcomap :
        MeasurableSpace.comap (Function.eval i) (mΩ i) ≤
          generateFrom (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) := by
      rw [← hE i, MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨u, hu, rfl⟩
      apply measurableSet_generateFrom
      refine Set.mem_iUnion.mpr ⟨({i} : Finset I), ?_⟩
      let A : ∀ j : ({i} : Finset I), Set (Ω j.1) := fun j ↦ by
        rcases j with ⟨j, hj⟩
        have hj' : j = i := by
          simpa using hj
        subst hj'
        exact u
      refine ⟨A, ?_, ?_⟩
      · rw [Set.mem_pi]
        intro j _
        rcases j with ⟨j, hj⟩
        have hj' : j = i := by
          simpa using hj
        subst hj'
        simpa using hu
      · ext x
        constructor
        · intro hx
          rw [MeasureTheory.mem_cylinder, Set.mem_pi] at hx
          simpa [A] using hx ⟨i, by simp⟩ (mem_univ _)
        · intro hx
          rw [MeasureTheory.mem_cylinder, Set.mem_pi]
          intro j _
          rcases j with ⟨j, hj⟩
          have hj' : j = i := by
            simpa using hj
          subst hj'
          simpa [A] using hx
    have ht' :
        MeasurableSet[MeasurableSpace.comap (Function.eval i) (mΩ i)]
          (Function.eval i ⁻¹' t) := by
      exact ⟨t, ht, rfl⟩
    exact hcomap _ ht'

/-- Auxiliary finite-base cylinder generator bridge for source clause (2). -/
private theorem generateFromRectangularCylinderFamiliesEqProduct
    (hE : ∀ i, generateFrom (E i) = mΩ i) :
    generateFrom
        (⋃ J : Finset I, rectangularCylinderSetsWithBase J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) ∧
    generateFrom
        (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) := by
  constructor
  · -- The unrestricted finite-base rectangular cylinders were handled in the previous helper.
    exact generateFrom_rectangularCylinderSets_eq_product
  · -- The restricted family uses the coordinate generators supplied by `hE`.
    exact generateFrom_restrictedRectangularCylinderSets_eq_product hE

omit mΩ in
/-- Helper: a square cylinder over the finite base `J` is exactly the
corresponding restricted cylinder whose coordinates are indexed by `J`. -/
private theorem squareCylinder_eq_restrictedCylinder (J : Finset I) (A : ∀ i, Set (Ω i)) :
    ((J : Set I).pi A) = cylinder J (Set.pi univ (fun j : J ↦ A j.1)) := by
  -- Unpack both sides to the same coordinatewise membership condition.
  ext x
  simp [MeasureTheory.mem_cylinder, Set.mem_pi]

omit mΩ in
/-- Helper: every square cylinder already belongs to the union of restricted
finite-base cylinder families. -/
private theorem squareCylinders_subset_iUnion_restrictedRectangularCylinderSetsWithBase :
    squareCylinders E ⊆ ⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J := by
  intro s hs
  rcases hs with ⟨J, A, hA, rfl⟩
  have hA' : ∀ i, A i ∈ E i := by
    simpa [Set.mem_pi] using hA
  refine Set.mem_iUnion.mpr ⟨J, ?_⟩
  refine ⟨(fun j : J ↦ A j.1), ?_, ?_⟩
  · -- Restrict the total coordinate family to the chosen finite base.
    rw [Set.mem_pi]
    intro j _
    exact hA' j.1
  · -- The two cylinder presentations are definitionally the same set.
    exact (squareCylinder_eq_restrictedCylinder J A).symm

omit mΩ in
/-- Helper: the empty set is a trivial finite union of restricted cylinders. -/
private theorem empty_mem_finiteUnionRestrictedRectangularCylinderSets :
    (∅ : Set ((i : I) → Ω i)) ∈ finiteUnionRestrictedRectangularCylinderSets E := by
  -- Use the empty finite family as the witness.
  rw [mem_finiteUnionRestrictedRectangularCylinderSets_iff]
  refine ⟨∅, ?_, by simp⟩
  simp

omit mΩ in
/-- Helper: every square cylinder is a singleton finite union of restricted
cylinders. -/
private theorem squareCylinder_mem_finiteUnionRestrictedRectangularCylinderSets
    {s : Set ((i : I) → Ω i)}
    (hs : s ∈ squareCylinders E) :
    s ∈ finiteUnionRestrictedRectangularCylinderSets E := by
  -- A square cylinder is a finite union with one summand.
  rw [mem_finiteUnionRestrictedRectangularCylinderSets_iff]
  refine ⟨{s}, ?_, by simp⟩
  intro t ht
  have hts : t = s := by simpa using ht
  subst hts
  exact hs

omit mΩ in
/-- Helper: a nonempty intersection of a restricted finite-base cylinder with a
square cylinder is itself a square cylinder. -/
private theorem inter_restricted_square_mem_squareCylinders
    (hE_pi : ∀ i, IsPiSystem (E i))
    {J : Finset I} {s t : Set ((i : I) → Ω i)}
    (hs : s ∈ restrictedRectangularCylinderSetsWithBase E J)
    (ht : t ∈ squareCylinders E)
    (hst : (s ∩ t).Nonempty) :
    s ∩ t ∈ squareCylinders E := by
  classical
  rcases hs with ⟨A, hA, rfl⟩
  rcases ht with ⟨K, B, hB, rfl⟩
  have hA' : ∀ j : J, A j ∈ E j.1 := by
    simpa [Set.mem_pi] using hA
  have hB' : ∀ i, B i ∈ E i := by
    simpa [Set.mem_pi] using hB
  obtain ⟨x, hx⟩ := hst
  have hx₁ : x ∈ cylinder J (Set.pi univ A) := hx.1
  have hx₂ : x ∈ (K : Set I).pi B := hx.2
  rw [MeasureTheory.mem_cylinder, Set.mem_pi] at hx₁
  rw [Set.mem_pi] at hx₂
  let L : Finset I := J ∪ K
  let C : ∀ i, Set (Ω i) := fun i ↦
    if hiK : i ∈ K then
      if hiJ : i ∈ J then
        A ⟨i, hiJ⟩ ∩ B i
      else
        B i
    else if hiJ : i ∈ J then
      A ⟨i, hiJ⟩
    else
      B i
  refine ⟨L, C, ?_, ?_⟩
  · -- The full coordinate family stays inside `E`, using `IsPiSystem` on the overlap.
    rw [Set.mem_pi]
    intro i _
    dsimp [C]
    by_cases hiK : i ∈ K
    · by_cases hiJ : i ∈ J
      · have hx₁i : x i ∈ A ⟨i, hiJ⟩ := hx₁ ⟨i, hiJ⟩ (mem_univ _)
        have hx₂i : x i ∈ B i := hx₂ i hiK
        have hne : (A ⟨i, hiJ⟩ ∩ B i : Set (Ω i)).Nonempty := ⟨x i, hx₁i, hx₂i⟩
        simpa [hiK, hiJ] using hE_pi i (A ⟨i, hiJ⟩) (hA' ⟨i, hiJ⟩) (B i) (hB' i) hne
      · simpa [hiK, hiJ] using hB' i
    · by_cases hiJ : i ∈ J
      · simpa [hiK, hiJ] using hA' ⟨i, hiJ⟩
      · simpa [hiK, hiJ] using hB' i
  · -- Compare the intersection and the square cylinder coordinatewise on `L = J ∪ K`.
    ext y
    rw [Set.mem_inter_iff, MeasureTheory.mem_cylinder, Set.mem_pi, Set.mem_pi, Set.mem_pi]
    constructor
    · intro hy i hiL
      dsimp [C]
      by_cases hiK : i ∈ K
      · by_cases hiJ : i ∈ J
        · have hy₁ : y i ∈ A ⟨i, hiJ⟩ := hy.1 ⟨i, hiJ⟩ (mem_univ _)
          have hy₂ : y i ∈ B i := hy.2 i hiK
          simpa [hiK, hiJ] using And.intro hy₁ hy₂
        · simpa [hiK, hiJ] using hy.2 i hiK
      · have hiJ : i ∈ J := (Finset.mem_union.mp hiL).resolve_right hiK
        have hy₁ : y i ∈ A ⟨i, hiJ⟩ := hy.1 ⟨i, hiJ⟩ (mem_univ _)
        simpa [hiK, hiJ] using hy₁
    · intro hy
      refine ⟨?_, ?_⟩
      · intro j _
        have hyL := hy j.1 (Finset.mem_union.mpr <| Or.inl j.2)
        by_cases hjK : j.1 ∈ K
        · have hyLj : y j.1 ∈ A j ∩ B j.1 := by
            simpa [C, L, hjK, j.2] using hyL
          exact hyLj.1
        · simpa [C, L, hjK, j.2] using hyL
      · intro i hiL
        have hyL' : y i ∈ C i := hy i (Finset.mem_union.mpr <| Or.inr hiL)
        dsimp [C] at hyL'
        by_cases hiJ : i ∈ J
        · by_cases hiK : i ∈ K
          · have hyLi : y i ∈ A ⟨i, hiJ⟩ ∩ B i := by
              simpa [hiK, hiJ] using hyL'
            exact hyLi.2
          · exact (hiK hiL).elim
        · by_cases hiK : i ∈ K
          · simpa [hiK, hiJ] using hyL'
          · exact (hiK hiL).elim

omit mΩ in
/-- Helper: intersecting a generator set from the restricted-cylinder union with
 a square cylinder again lands in `𝒵_*^{E,R}`. -/
private theorem
    inter_iUnionRestricted_squareCylinder_mem_finiteUnionRestrictedRectangularCylinderSets
    (hE_pi : ∀ i, IsPiSystem (E i))
    {s t : Set ((i : I) → Ω i)}
    (hs : s ∈ ⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J)
    (ht : t ∈ squareCylinders E) :
    s ∩ t ∈ finiteUnionRestrictedRectangularCylinderSets E := by
  rcases (s ∩ t).eq_empty_or_nonempty with hst | hst
  · -- The empty intersection is covered by the empty finite family.
    simpa [hst] using empty_mem_finiteUnionRestrictedRectangularCylinderSets
  · -- The nonempty intersection is itself a square cylinder, hence a singleton finite union.
    rcases Set.mem_iUnion.mp hs with ⟨J, hsJ⟩
    exact squareCylinder_mem_finiteUnionRestrictedRectangularCylinderSets
      (inter_restricted_square_mem_squareCylinders hE_pi hsJ ht hst)

/- The source states the `σ`-finiteness of `μ` explicitly, so this theorem keeps `[SigmaFinite μ]`
in addition to the spanning sequence used in the proof route. -/
/-- Auxiliary uniqueness clause for source clause (3). -/
private theorem eqOfAgreeOnRestrictedCylinderUnionsAux
    {μ ν : Measure ((i : I) → Ω i)}
    [SigmaFinite μ]
    (hE : ∀ i, generateFrom (E i) = mΩ i)
    (hE_pi : ∀ i, IsPiSystem (E i))
    (B : ℕ → Set ((i : I) → Ω i))
    (hB_mem : ∀ n, B n ∈ squareCylinders E)
    (hB_mono : Monotone B)
    (hB_spanning : (⋃ n, B n) = univ)
    (hB_finite : ∀ n, μ (B n) < ⊤)
    (h_eq : ∀ s ∈ finiteUnionRestrictedRectangularCylinderSets E, μ s = ν s) :
    μ = ν := by
  classical
  let C : Set (Set ((i : I) → Ω i)) :=
    ⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J
  let T : Set (Set ((i : I) → Ω i)) := Set.range B
  let _ := hB_mono
  -- Route correction: the square cylinders only provide the covering family, while the generating
  -- `π`-system is the restricted-cylinder union `C`.
  have h_gen :
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) = generateFrom C := by
    simpa [C] using (generateFrom_restrictedRectangularCylinderSets_eq_product hE).symm
  have hC : IsPiSystem C := by
    simpa [C] using restrictedCylinderUnion_isPiSystem hE_pi
  have hT_countable : T.Countable := by
    simpa [T] using Set.countable_range B
  have hU : ⋃₀ T = univ := by
    simpa [T, Set.sUnion_range] using hB_spanning
  have htop : ∀ t ∈ T, μ t ≠ ⊤ := by
    rintro t ⟨n, rfl⟩
    exact ne_top_of_lt (hB_finite n)
  have hST_eq : ∀ t ∈ T, ∀ s ∈ C, μ (s ∩ t) = ν (s ∩ t) := by
    rintro t ⟨n, rfl⟩ s hs
    -- The intersection stays inside `𝒵_*^{E,R}`, so the hypothesis `h_eq` applies.
    exact h_eq (s ∩ B n)
      (inter_iUnionRestricted_squareCylinder_mem_finiteUnionRestrictedRectangularCylinderSets
        hE_pi hs (hB_mem n))
  have hT_eq : ∀ t ∈ T, μ t = ν t := by
    rintro t ⟨n, rfl⟩
    -- Each cover set is itself a singleton finite union of restricted cylinders.
    exact h_eq (B n)
      (squareCylinder_mem_finiteUnionRestrictedRectangularCylinderSets (hB_mem n))
  exact Measure.ext_of_generateFrom_of_cover h_gen hT_countable hC hU htop hST_eq hT_eq

/- Source repair note for this item: `finitePiBoxGeneratorCounterexample` shows that the literal
finite-box wording for clause `(i)` is false without filler sets `univ` in the unused
coordinates, even on a genuinely finite product. The fallback source proof route instead works
with the one-coordinate evaluation preimages, while the corrected literal-box bridge with explicit
filler hypotheses is kept private below. -/

/-- Auxiliary literal-box bridge: with explicit `univ` fillers in every coordinate family, the
finite product `σ`-algebra is generated by the corresponding literal boxes. -/
private theorem generateFrom_piBoxes_eq_finiteProduct_of_univ_mem_aux
    (J : Finset I)
    (hE : ∀ j : J, generateFrom (E j.1) = mΩ j.1)
    (hE_univ : ∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1) :
    generateFrom
      ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
        Set.pi univ (fun j : J ↦ E j.1)) =
      (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1)) := by
  classical
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases hs with ⟨A, hA, rfl⟩
    rw [Set.mem_pi] at hA
    have hA' : ∀ j : J, A j ∈ E j.1 := fun j ↦ hA j (mem_univ _)
    have hAmeas : ∀ j : J, MeasurableSet (A j) := by
      intro j
      have hAj_meas : @MeasurableSet (Ω j.1) (generateFrom (E j.1)) (A j) :=
        measurableSet_generateFrom (hA' j)
      rwa [hE j] at hAj_meas
    exact measurableSet_piBox hAmeas
  · have hEval :
        generateFrom
          (⋃ j : J, (fun s : Set (Ω j.1) ↦ Function.eval j ⁻¹' s) '' E j.1) ≤
          generateFrom
            ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
              Set.pi univ (fun j : J ↦ E j.1)) := by
      refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      rw [mem_iUnion] at hs
      rcases hs with ⟨j, hs⟩
      rcases hs with ⟨t, ht, rfl⟩
      apply measurableSet_generateFrom
      refine ⟨Function.update (fun k : J ↦ (univ : Set (Ω k.1))) j t, ?_, ?_⟩
      · rw [Set.mem_pi]
        intro k _
        by_cases hk : k = j
        · subst hk
          simpa [Function.update] using ht
        · simpa [Function.update, hk] using hE_univ k
      · simp [evalPreimage_eq_pi_update]
    calc
      (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1)) =
          generateFrom
            (⋃ j : J, (fun s : Set (Ω j.1) ↦ Function.eval j ⁻¹' s) '' E j.1) :=
        (generateFromEvalPreimagesEqFiniteProduct J hE).symm
      _ ≤ generateFrom
            ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
              Set.pi univ (fun j : J ↦ E j.1)) :=
        hEval

/-- Auxiliary literal-box bridge for the repaired clause `(i)`: with explicit `univ` fillers in
every coordinate family, the factor generators induce the finite product `σ`-algebra. -/
private theorem generateFrom_piBoxes_eq_finiteProduct_of_univ_mem
    (hE : ∀ i, generateFrom (E i) = mΩ i) :
    ∀ J : Finset I,
      (∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1) →
        generateFrom
          ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
            Set.pi univ (fun j : J ↦ E j.1)) =
          (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1)) := by
  intro J hE_univ
  exact generateFrom_piBoxes_eq_finiteProduct_of_univ_mem_aux J (fun j ↦ hE j.1) hE_univ

/-- Auxiliary bridge for source clause `(ii)`: measurable rectangular cylinders with finite base
generate the ambient product `σ`-algebra. -/
private theorem generateFrom_iUnion_rectangularCylinderSetsWithBase_eq_product
    (hE : ∀ i, generateFrom (E i) = mΩ i) :
    generateFrom
        (⋃ J : Finset I, rectangularCylinderSetsWithBase J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) := by
  exact (generateFromRectangularCylinderFamiliesEqProduct hE).1

/-- Auxiliary bridge for source clause `(ii)`: the restricted rectangular cylinders with finite
base also generate the ambient product `σ`-algebra. -/
private theorem generateFrom_iUnion_restrictedRectangularCylinderSetsWithBase_eq_product
    (hE : ∀ i, generateFrom (E i) = mΩ i) :
    generateFrom
        (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) =
      (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)) := by
  exact (generateFromRectangularCylinderFamiliesEqProduct hE).2

/-- Auxiliary bridge for source clause `(iii)`: under the source `π`-system and finite-cover
hypotheses, a `σ`-finite measure on the product space is determined by its values on finite
unions of restricted rectangular cylinders. -/
private theorem eq_of_agreeOnRestrictedCylinderUnions
    {μ ν : Measure ((i : I) → Ω i)}
    [SigmaFinite μ]
    (hE : ∀ i, generateFrom (E i) = mΩ i)
    (hE_pi : ∀ i, IsPiSystem (E i))
    (B : ℕ → Set ((i : I) → Ω i))
    (hB_mem : ∀ n, B n ∈ squareCylinders E)
    (hB_mono : Monotone B)
    (hB_spanning : (⋃ n, B n) = univ)
    (hB_finite : ∀ n, μ (B n) < ⊤)
    (h_eq : ∀ s ∈ finiteUnionRestrictedRectangularCylinderSets E, μ s = ν s) :
    μ = ν := by
  -- The auxiliary theorem packages the cover-version extensionality argument.
  exact eqOfAgreeOnRestrictedCylinderUnionsAux
    hE hE_pi B hB_mem hB_mono hB_spanning hB_finite h_eq

-- Source repair note: the checkout has no local `source/` directory, and the available source
-- text for Theorem 14.12 gives a clause `(i)` whose literal finite-box formula is false without
-- extra `univ` fillers. The private counterexample below records that defect, while the public
-- source-facing API packages the repaired clauses into one theorem.

/-- Support theorem: without explicit `univ` fillers on the unused coordinates, the literal
finite-box generator formula is false, and a finite product already gives a counterexample. -/
private theorem finitePiBoxGeneratorCounterexample :
    ∃ (K : Type) (_ : Fintype K) (X : K → Type) (mX : ∀ k, MeasurableSpace (X k))
      (F : ∀ k, Set (Set (X k))),
        (∀ k, generateFrom (F k) = mX k) ∧
          generateFrom
            ((fun A : ∀ k, Set (X k) ↦ Set.pi univ A) '' Set.pi univ F) ≠
            (@MeasurableSpace.pi K X mX : MeasurableSpace ((k : K) → X k)) := by
  refine ⟨↥(Finset.univ : Finset Bool), inferInstance,
    (fun j ↦ finitePiBoxCounterexampleSpace j.1),
    (fun j ↦ finitePiBoxCounterexampleMeasurableSpace j.1),
    (fun j ↦ finitePiBoxCounterexampleGenerator j.1), ?_⟩
  dsimp [finitePiBoxCounterexampleMeasurableSpace]
  constructor
  · intro k
    rfl
  · simpa using finitePiBoxGeneratorCounterexampleAux

/-- Auxiliary bridge for source clause `(i)`: if each `E i` generates the factor `σ`-algebra `mΩ i`,
then for every
finite `J`, the literal box family generates the finite product `σ`-algebra provided the unused
coordinates admit `univ` as fillers.

Source repair note: the printed clause `(i)` is false without the extra filler hypothesis
`∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1`, as witnessed by the private counterexample above. The
public source-facing API records the repaired clause inside one bundled theorem. -/
private theorem finiteProductGenerators
    (hE : ∀ i, generateFrom (E i) = mΩ i) :
    (∀ J : Finset I,
      (∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1) →
        generateFrom
          ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
            Set.pi univ (fun j : J ↦ E j.1)) =
          (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1))) := by
  intro J hE_univ
  -- The repaired clause `(i)` is exactly the literal-box bridge proved just above.
  exact generateFrom_piBoxes_eq_finiteProduct_of_univ_mem hE J hE_univ

/-- Helper for Theorem 14.12: clause `(ii)` bundles the two product-cylinder generator
equalities. -/
private abbrev rectangularCylinderGeneratorClauses
    (E : ∀ i, Set (Set (Ω i))) :
    Prop :=
  (generateFrom
      (⋃ J : Finset I, rectangularCylinderSetsWithBase J) =
    (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i))) ∧
  (generateFrom
      (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase E J) =
    (MeasurableSpace.pi : MeasurableSpace ((i : I) → Ω i)))

/-- Theorem 14.12: if each `E i` generates the factor `σ`-algebra `mΩ i`, then
`(i)` for every finite `J`, the literal box family generates the finite product `σ`-algebra once
the unused coordinates admit `univ` fillers;
`(ii)` the measurable rectangular cylinders and the restricted rectangular cylinders generate the
ambient product `σ`-algebra; and
`(iii)` under the source `π`-system and finite-cover hypotheses, a `σ`-finite measure on the
product space is uniquely determined by its values on the finite unions of restricted rectangular
cylinders.

Source repair note: clause `(i)` needs the explicit filler hypothesis
`∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1`; without it, the literal finite-box formula is false, as
witnessed by the private counterexample above. -/
theorem productGenerators
    (hE : ∀ i, generateFrom (E i) = mΩ i)
    :
    (∀ J : Finset I,
      (∀ j : J, (univ : Set (Ω j.1)) ∈ E j.1) →
        generateFrom
          ((fun A : ∀ j : J, Set (Ω j.1) ↦ Set.pi univ A) ''
            Set.pi univ (fun j : J ↦ E j.1)) =
          (MeasurableSpace.pi : MeasurableSpace ((j : J) → Ω j.1))) ∧
    rectangularCylinderGeneratorClauses E ∧
    (∀ {μ ν : Measure ((i : I) → Ω i)} [SigmaFinite μ],
      (∀ i, IsPiSystem (E i)) →
        (B : ℕ → Set ((i : I) → Ω i)) →
        (∀ n, B n ∈ squareCylinders E) →
        Monotone B →
        (⋃ n, B n) = univ →
        (∀ n, μ (B n) < ⊤) →
        (∀ s ∈ finiteUnionRestrictedRectangularCylinderSets E, μ s = ν s) →
        μ = ν) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Clause `(i)` is the repaired finite-product generator statement proved above.
    exact finiteProductGenerators hE
  · -- Clause `(ii)` is the bundled rectangular-cylinder generator bridge.
    exact generateFromRectangularCylinderFamiliesEqProduct hE
  · intro μ ν _ hE_pi B hB_mem hB_mono hB_spanning hB_finite h_eq
    -- Clause `(iii)` is exactly the packaged uniqueness theorem for restricted cylinders.
    exact eq_of_agreeOnRestrictedCylinderUnions
      hE hE_pi B hB_mem hB_mono hB_spanning hB_finite h_eq
