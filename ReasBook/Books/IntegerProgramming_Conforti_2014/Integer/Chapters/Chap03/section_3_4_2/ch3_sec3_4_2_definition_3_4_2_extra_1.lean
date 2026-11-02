import Mathlib

/-
Definition 3.4.2-extra-1 is an affine-geometry item. The canonical owner declarations in the
domain are:

* `mem_affineSpan_iff_eq_affineCombination`;
* `AffineIndependent.notMem_affineSpan_diff`;
* `AffineIndependent.affineIndependent_of_notMem_span`;
* `affineIndependent_equiv`;
* `AffineSubspace.affineSpan_eq_sInf`.

Items `(1)` and `(3)` below are direct recalls of the first and fourth owners, specialized in the
text to families of points in `ℝ^n`. Item `(2)` is the source-facing bridge theorem relating
affine independence to exclusion from the affine span of the remaining points.
-/

/- Definition 3.4.2-extra-1 (1). A point of `ℝ^n` is an affine combination of finitely many
points exactly when it lies in the affine span of those points. -/
#check mem_affineSpan_iff_eq_affineCombination

section AffineIndependentCriterion

variable {k V P ι : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Definition 3.4.2-extra-1 (2). A finite family of points in an affine space is
affinely independent exactly when no point of the family lies in the affine span
of the others. -/
theorem affineIndependent_iff_not_mem_affineSpan_image_others [Finite ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ i : ι, p i ∉ affineSpan k (p '' {x | x ≠ i}) := by
  classical
  constructor
  · intro ha i
    have hdiff : (Set.univ \ ({i} : Set ι)) = {x | x ≠ i} := by
      ext x
      simp
    simpa [hdiff] using ha.notMem_affineSpan_diff i Set.univ
  · intro h_not_mem
    let _ : Fintype ι := Fintype.ofFinite ι
    exact
      Fintype.induction_empty_option
        (fun α β _ e hα q hq ↦ by
          have hq' :
              ∀ i : α, q (e i) ∉ affineSpan k ((q ∘ e) '' {x | x ≠ i}) := by
            intro i hi
            have hsubset :
                (q ∘ e) '' {x | x ≠ i} ⊆ q '' {x | x ≠ e i} := by
              rintro y ⟨j, hj, rfl⟩
              exact ⟨e j, by simpa using hj, rfl⟩
            exact hq (e i) ((affineSpan_mono k hsubset) hi)
          simpa [Function.comp_def] using (affineIndependent_equiv e).1 (hα (q ∘ e) hq'))
        (fun q _ ↦ affineIndependent_of_subsingleton k q)
        (fun α _ hα q hq ↦ by
          let q' : α → P := q ∘ some
          have hq' : ∀ i : α, q' i ∉ affineSpan k (q' '' {x | x ≠ i}) := by
            intro i hi
            have hsubset :
                q' '' {x | x ≠ i} ⊆ q '' {x | x ≠ some i} := by
              rintro y ⟨j, hj, rfl⟩
              exact ⟨some j, by simpa using hj, rfl⟩
            exact hq (some i) ((affineSpan_mono k hsubset) hi)
          have ha' : AffineIndependent k q' := hα q' hq'
          let e : α ≃ {x : Option α // x ≠ none} :=
            Equiv.optionSubtype none ⟨Equiv.refl _, rfl⟩
          have ha_subtype : AffineIndependent k (fun x : {x : Option α // x ≠ none} ↦ q x) := by
            simpa [q', e, Function.comp_def] using (affineIndependent_equiv e).1 ha'
          exact ha_subtype.affineIndependent_of_notMem_span <| by simpa using hq none)
        ι p h_not_mem

end AffineIndependentCriterion

/- Definition 3.4.2-extra-1 (3). The affine hull of a set of points in `ℝ^n` is the smallest
affine subspace containing that set. -/
#check AffineSubspace.affineSpan_eq_sInf
