/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 1.28 (content): A content on a semiring of sets is the canonical mathlib bundled
object `AddContent ℝ≥0∞ A`, namely a set function on `A` with value `0` on `∅` that is finitely
additive on finite pairwise disjoint unions inside `A`.
-/
recall MeasureTheory.AddContent

open MeasureTheory

open scoped ENNReal

universe u

variable {Ω : Type u} {A : Set (Set Ω)}

namespace AddContent

/-
Definition 1.28 (premeasure): On a semiring of sets, a premeasure is the canonical mathlib
predicate `AddContent.IsSigmaSubadditive` on an additive content.
-/
recall MeasureTheory.AddContent.IsSigmaSubadditive

/-- Helper for Definition 1.28: if a pairwise disjoint family in `supClosure A` has total union
already in `A`, then `μ.supClosure hA` is countably additive on that family. -/
lemma supClosure_iUnion_eq_tsum_of_disjoint_of_union_mem_base (μ : AddContent ℝ≥0∞ A)
    (hA : IsSetSemiring A)
    (hμ : ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ A) →
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) → (⋃ n, s n) ∈ A →
      μ (⋃ n, s n) = ∑' n, μ (s n))
    {s : ℕ → Set Ω} (hs : ∀ n, s n ∈ supClosure A)
    (hdisj : Pairwise (fun i j ↦ Disjoint (s i) (s j))) (hUnion : (⋃ n, s n) ∈ A) :
    μ.supClosure hA (⋃ n, s n) = ∑' n, μ.supClosure hA (s n) := by
  classical
  -- Refine each `s n` by finitely many `A`-atoms, then encode all atoms into a single `ℕ`-family.
  choose P hP using fun n ↦ hA.mem_supClosure_iff.mp (hs n)
  letI : Encodable (Σ n, (P n).parts) := Classical.choice (nonempty_encodable _)
  let t : (Σ n, (P n).parts) → Set Ω := fun a ↦ a.2.1
  have ht_mem : ∀ a : (Σ n, (P n).parts), t a ∈ A := by
    intro a
    exact hP a.1 a.2.2
  have ht_disj : Pairwise (fun a b ↦ Disjoint (t a) (t b)) := by
    intro a b hab
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    dsimp [t]
    by_cases hij : i = j
    · subst hij
      have hab' : a ≠ b := by
        intro h
        apply hab
        cases h
        rfl
      exact (P i).disjoint a.2 b.2 fun habSet ↦ hab' (Subtype.ext habSet)
    · exact (hdisj hij).mono ((P i).le a.2) ((P j).le b.2)
  have ht_iUnion : (⋃ a : (Σ n, (P n).parts), t a) = ⋃ n, s n := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
      exact Set.mem_iUnion.mpr ⟨a.1, (P a.1).le a.2.2 ha⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      have hx' : x ∈ (P n).parts.sup id := by
        rw [(P n).sup_parts]
        exact hn
      have hx'' : x ∈ ⋃ u ∈ (P n).parts, u := by
        simpa [Finset.sup_set_eq_biUnion] using hx'
      rcases (by simpa [Set.mem_iUnion, Finset.mem_coe] using hx'' :
          ∃ u ∈ (P n).parts, x ∈ u) with ⟨u, hu, hxu⟩
      exact Set.mem_iUnion.mpr ⟨⟨n, ⟨u, hu⟩⟩, hxu⟩
  let u : ℕ → Set Ω := fun k ↦ ⋃ a ∈ Encodable.decode₂ (Σ n, (P n).parts) k, t a
  have hu_mem : ∀ k, u k ∈ A := by
    intro k
    -- Every decoded level is either empty or one of the atoms.
    simpa [u] using
      (Encodable.iUnion_decode₂_cases (f := t) (C := fun s ↦ s ∈ A) hA.empty_mem ht_mem (n := k))
  have hu_disj : Pairwise (Function.onFun Disjoint u) := by
    -- Distinct codes decode to disjoint atoms.
    simpa [u] using Encodable.iUnion_decode₂_disjoint_on (f := t) ht_disj
  have hu_iUnion : (⋃ k, u k) = ⋃ n, s n := by
    calc
      (⋃ k, u k) = ⋃ a : (Σ n, (P n).parts), t a := by
        simpa [u] using (Encodable.iUnion_decode₂ (f := t))
      _ = ⋃ n, s n := ht_iUnion
  have hu_tsum : (∑' k, μ (u k)) = ∑' a : (Σ n, (P n).parts), μ (t a) := by
    -- Summing over the decoded `ℕ`-family is the same as summing over the sigma-type of atoms.
    simpa [u] using
      (tsum_iUnion_decode₂ (m := μ) (m0 := addContent_empty) (s := t))
  have hs_supClosure : ∀ n, μ.supClosure hA (s n) = ∑' a : (P n).parts, μ a.1 := by
    intro n
    -- Each `s n` is the finite sum of its partition atoms.
    calc
      μ.supClosure hA (s n) = ∑ a ∈ (P n).parts, μ a := by
        exact μ.supClosure_apply_finpartition hA (hP n)
      _ = ∑ a ∈ (P n).parts.attach, μ a.1 := by
        simpa using (Finset.sum_attach (P n).parts (fun a ↦ μ a)).symm
      _ = ∑' a : (P n).parts, μ a.1 := by
        simpa using (tsum_fintype (f := fun a : (P n).parts ↦ μ a.1)).symm
  -- Apply the textbook hypothesis to the encoded `ℕ`-family and rewrite both sides.
  calc
    μ.supClosure hA (⋃ n, s n) = μ (⋃ n, s n) := by
      exact μ.supClosure_apply_of_mem hA hUnion
    _ = ∑' k, μ (u k) := by
      simpa [hu_iUnion, Function.onFun] using
        hμ hu_mem hu_disj (by simpa [hu_iUnion] using hUnion)
    _ = ∑' a : (Σ n, (P n).parts), μ (t a) := hu_tsum
    _ = ∑' n, ∑' a : (P n).parts, μ a.1 := by
      simpa [t] using (ENNReal.tsum_sigma' (f := fun a : (Σ n, (P n).parts) ↦ μ (t a)))
    _ = ∑' n, μ.supClosure hA (s n) := by
      refine tsum_congr fun n ↦ ?_
      exact (hs_supClosure n).symm

/-- Helper for Definition 1.28: the countable additivity hypothesis on `A` lifts to
`μ.supClosure hA` on pairwise disjoint families in `supClosure A`. -/
lemma supClosure_iUnion_eq_tsum_of_disjoint (μ : AddContent ℝ≥0∞ A) (hA : IsSetSemiring A)
    (hμ : ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ A) →
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) → (⋃ n, s n) ∈ A →
      μ (⋃ n, s n) = ∑' n, μ (s n))
    {s : ℕ → Set Ω} (hs : ∀ n, s n ∈ supClosure A)
    (hdisj : Pairwise (fun i j ↦ Disjoint (s i) (s j))) (hUnion : (⋃ n, s n) ∈ supClosure A) :
    μ.supClosure hA (⋃ n, s n) = ∑' n, μ.supClosure hA (s n) := by
  classical
  obtain ⟨Q, hQ⟩ := hA.mem_supClosure_iff.mp hUnion
  have hs_sub : ∀ n, s n ⊆ ⋃ i, s i := by
    intro n
    exact Set.subset_iUnion _ n
  have hslice :
      ∀ q ∈ Q.parts, μ q = ∑' n, μ.supClosure hA (s n ∩ q) := by
    intro q hq
    have hq_mem : q ∈ A := hQ hq
    have hq_sub : q ⊆ ⋃ i, s i := Q.le hq
    have hsq_mem : ∀ n, s n ∩ q ∈ supClosure A := by
      intro n
      exact hA.isSetRing_supClosure.inter_mem (hs n) (subset_supClosure hq_mem)
    have hsq_disj : Pairwise (fun i j ↦ Disjoint (s i ∩ q) (s j ∩ q)) := by
      intro i j hij
      exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsq_iUnion : (⋃ n, s n ∩ q) = q := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
        exact hxn.2
      · intro hx
        rcases Set.mem_iUnion.mp (hq_sub hx) with ⟨n, hxn⟩
        exact Set.mem_iUnion.mpr ⟨n, ⟨hxn, hx⟩⟩
    -- Reduce the `q`-slice to the previous helper where the total union lies in `A`.
    calc
      μ q = μ.supClosure hA q := by
        symm
        exact μ.supClosure_apply_of_mem hA hq_mem
      _ = μ.supClosure hA (⋃ n, s n ∩ q) := by rw [hsq_iUnion]
      _ = ∑' n, μ.supClosure hA (s n ∩ q) := by
        exact supClosure_iUnion_eq_tsum_of_disjoint_of_union_mem_base μ hA hμ hsq_mem hsq_disj
          (by simpa [hsq_iUnion] using hq_mem)
  have hs_restrict :
      ∀ n, ∑ q ∈ Q.parts, μ.supClosure hA (s n ∩ q) = μ.supClosure hA (s n) := by
    intro n
    let R := Q.restrict (hs_sub n)
    have hrestrict_mem : ↑R.parts ⊆ supClosure A := by
      intro r hr
      change r ∈ ((Q.parts.image fun x ↦ x ∩ s n).erase ∅) at hr
      simp only [Finset.mem_erase, Finset.mem_image] at hr
      rcases hr.2 with ⟨q, hq, hqeq⟩
      rw [← hqeq]
      exact hA.isSetRing_supClosure.inter_mem (subset_supClosure (hQ hq)) (hs n)
    have hR_union : ⋃₀ ↑R.parts = s n := by
      ext x
      simpa [Finset.sup_set_eq_biUnion] using congrArg (fun t : Set Ω ↦ x ∈ t) R.sup_parts
    have hR_sum : μ.supClosure hA (s n) = ∑ r ∈ R.parts, μ.supClosure hA r := by
      -- The restricted partition is still a finite disjoint decomposition of `s n`.
      simpa [hR_union] using
        (MeasureTheory.addContent_sUnion hrestrict_mem R.disjoint
          (by simpa [hR_union] using hs n) :
          μ.supClosure hA (⋃₀ ↑R.parts) = ∑ r ∈ R.parts, μ.supClosure hA r)
    -- Restrict the finite partition of the total union to `s n`.
    calc
      ∑ q ∈ Q.parts, μ.supClosure hA (s n ∩ q) =
          ∑ r ∈ R.parts, μ.supClosure hA r := by
        symm
        simpa [R, Set.inter_comm] using
          (Q.sum_restrict (hs_sub n) (f := μ.supClosure hA) (hf := addContent_empty))
      _ = μ.supClosure hA (s n) := hR_sum.symm
  -- Sum the slice identities over the finite partition of the total union and commute sums.
  calc
    μ.supClosure hA (⋃ n, s n) = ∑ q ∈ Q.parts, μ q := by
      exact μ.supClosure_apply_finpartition hA hQ
    _ = ∑ q ∈ Q.parts, ∑' n, μ.supClosure hA (s n ∩ q) := by
      refine Finset.sum_congr rfl fun q hq ↦ ?_
      exact hslice q hq
    _ = ∑ q : Q.parts, ∑' n, μ.supClosure hA (s n ∩ q.1) := by
      -- Rewrite the finite sum as a sum over the subtype of partition atoms.
      symm
      simpa using
        (Finset.sum_coe_sort Q.parts
          (fun q : Set Ω ↦ ∑' n, μ.supClosure hA (s n ∩ q)))
    _ = ∑' n, ∑ q : Q.parts, μ.supClosure hA (s n ∩ q.1) := by
      -- Commute the countable sum with the finite sum over partition atoms.
      simpa using
        (ENNReal.tsum_comm (f := fun (q : Q.parts) (n : ℕ) ↦
          μ.supClosure hA (s n ∩ (q : Set Ω))))
    _ = ∑' n, ∑ q ∈ Q.parts, μ.supClosure hA (s n ∩ q) := by
      refine tsum_congr fun n ↦ ?_
      simpa using
        (Finset.sum_coe_sort Q.parts
          (fun q : Set Ω ↦ μ.supClosure hA (s n ∩ q)))
    _ = ∑' n, μ.supClosure hA (s n) := by
      refine tsum_congr fun n ↦ ?_
      exact hs_restrict n

/-- Helper for Definition 1.28: sigma-subadditivity of `μ.supClosure hA` restricts back to
sigma-subadditivity of `μ` on the original semiring `A`. -/
lemma isSigmaSubadditive_of_supClosureIsSigmaSubadditive (μ : AddContent ℝ≥0∞ A)
    (hA : IsSetSemiring A) (hμ : (μ.supClosure hA).IsSigmaSubadditive) :
    μ.IsSigmaSubadditive := by
  intro s hs hUnion
  -- Apply sigma-subadditivity in `supClosure A` and then rewrite back on sets of `A`.
  have hsup := hμ (fun n ↦ subset_supClosure (hs n)) (subset_supClosure hUnion)
  simpa [MeasureTheory.AddContent.supClosure_apply_of_mem, hs, hUnion] using hsup

/-- Definition 1.28 (premeasure): On a semiring of sets, the textbook countable additivity clause
for pairwise disjoint unions is equivalent to mathlib's canonical predicate
`AddContent.IsSigmaSubadditive` on an additive content. -/
theorem isSigmaSubadditive_iff_forall_iUnion_eq_tsum (μ : AddContent ℝ≥0∞ A)
    (hA : IsSetSemiring A) :
    μ.IsSigmaSubadditive ↔
      ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ A) →
        Pairwise (fun i j ↦ Disjoint (s i) (s j)) → (⋃ n, s n) ∈ A →
        μ (⋃ n, s n) = ∑' n, μ (s n) := by
  constructor
  · intro hμ s hs hdisj hUnion
    -- The forward implication is the existing semiring theorem in mathlib.
    exact MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive
      hA hμ s hs hUnion hdisj
  · intro hμ
    let ν := μ.supClosure hA
    have hν_iUnion :
        ∀ (s : ℕ → Set Ω), (∀ n, s n ∈ supClosure A) → (⋃ n, s n) ∈ supClosure A →
          Pairwise (Function.onFun Disjoint s) → ν (⋃ n, s n) = ∑' n, ν (s n) := by
      intro s hs hUnion hdisj
      -- Lift the disjoint countable additivity hypothesis from `A` to `supClosure A`.
      exact supClosure_iUnion_eq_tsum_of_disjoint μ hA hμ hs hdisj hUnion
    have hν_sigma : ν.IsSigmaSubadditive := by
      -- On the ring closure, the standard ring theorem turns disjoint countable additivity
      -- into sigma-subadditivity.
      exact MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum
        hA.isSetRing_supClosure hν_iUnion
    -- Restrict the sigma-subadditivity statement back to the original semiring.
    exact isSigmaSubadditive_of_supClosureIsSigmaSubadditive μ hA hν_sigma

end AddContent

/- Definition 1.28 (measure): Once the domain is a `σ`-algebra, the canonical bundled notion of
measure is `Measure Ω` on the corresponding measurable space. -/
recall MeasureTheory.Measure

/- Definition 1.28 (probability measure): A probability measure is the canonical mathlib predicate
`IsProbabilityMeasure μ` on a measure `μ`, i.e. a measure with total mass `1`. -/
recall MeasureTheory.IsProbabilityMeasure
