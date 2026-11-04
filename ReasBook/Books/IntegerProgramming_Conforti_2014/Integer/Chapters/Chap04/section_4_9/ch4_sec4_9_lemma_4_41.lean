/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_theorem_3_11

open scoped BigOperators Matrix Pointwise

-- Domain-style sampling for this refine pass:
-- * primary domain: Balas/Minkowski-Weyl style finite vertex-ray representations of polyhedra
-- * source-facing layer here: the finite decomposition data `V`, `R`, and `h_repr`
-- * core/canonical ambient owners: `convexHull`, `closure`, `PointedCone.hull`,
--   `Finset.univ.biUnion`
-- This lemma therefore keeps only the decomposition data that controls the equality and avoids
-- parallel local wrapper owners.

section Lemma441

variable {n k : ℕ}

/-- Helper for Lemma 4.41: each component vertex family is contained in the global biunion of all
vertex families. -/
lemma subset_biUnion_component
    (F : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    (F i : Set (Fin n → ℝ)) ⊆ (Finset.univ.biUnion F : Set (Fin n → ℝ)) := by
  -- The point belongs to the `i`-th block, so it belongs to the total biunion.
  intro x hx
  change x ∈ Finset.univ.biUnion F
  exact Finset.mem_biUnion.2 ⟨i, by simp, hx⟩

/-- Helper for Lemma 4.41: the `i`-th convex hull of vertices embeds into the global vertex hull. -/
lemma convexHull_subset_biUnion
    (V : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    convexHull ℝ (V i : Set (Fin n → ℝ)) ⊆
      convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) := by
  -- Apply monotonicity of the convex hull to the component-to-global inclusion.
  exact convexHull_mono (subset_biUnion_component V i)

/-- Helper for Lemma 4.41: the `i`-th ray cone embeds into the global cone hull of all rays. -/
lemma coneHull_subset_biUnion
    (R : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
      (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  -- `PointedCone.hull` is a span over nonnegative scalars, so span monotonicity gives the result.
  exact Submodule.span_mono (subset_biUnion_component R i)

/-- Helper for Lemma 4.41: each individual polyhedron lies in the global vertex-hull plus global
ray-cone. -/
lemma component_subset_global_vertexCone_sum
    (P : Fin k → Set (Fin n → ℝ))
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (i : Fin k) :
    P i ⊆
      convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ)) := by
  -- Unpack the component representation and map both summands into the global ones.
  intro x hx
  rw [h_repr i] at hx
  rcases hx with ⟨v, hv, r, hr, rfl⟩
  exact ⟨v, convexHull_subset_biUnion V i hv, r, coneHull_subset_biUnion R i hr, rfl⟩

/-- Helper for Lemma 4.41: the whole union of input polyhedra lies in the global vertex-hull plus
global ray-cone. -/
lemma iUnion_subset_global_vertexCone_sum
    (P : Fin k → Set (Fin n → ℝ))
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    (⋃ i : Fin k, P i) ⊆
      convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ)) := by
  -- Reduce union membership to membership in one component, then apply the component lemma.
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  exact component_subset_global_vertexCone_sum P V R h_repr i hxi

/-- Helper for Lemma 4.41: the global vertex-hull plus global ray-cone is convex. -/
lemma global_vertexCone_sum_convex
    (V R : Fin k → Finset (Fin n → ℝ)) :
    Convex ℝ
      (convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ))) := by
  -- Both summands are convex, so their Minkowski sum is convex.
  exact (convex_convexHull ℝ _).add (PointedCone.convex _)

/-- Helper for Lemma 4.41: nonemptiness of each input polyhedron gives a point in the corresponding
vertex hull. -/
lemma local_vertex_hull_nonempty
    (P : Fin k → Set (Fin n → ℝ))
    (hP_nonempty : ∀ i : Fin k, (P i).Nonempty)
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (i : Fin k) :
    ∃ v0 : Fin n → ℝ, v0 ∈ convexHull ℝ (V i : Set (Fin n → ℝ)) := by
  -- Unpack one point of `P i`; its convex-hull component is the required witness.
  rcases hP_nonempty i with ⟨x, hx⟩
  rw [h_repr i] at hx
  rcases hx with ⟨v0, hv0, r, hr, hxr⟩
  exact ⟨v0, hv0⟩

/-- Helper for Lemma 4.41: regrouping a finite family by its owner index recovers the original
sum. -/
lemma owner_partitioned_sum_eq
    {α M : Type*} [AddCommMonoid M]
    (s : Finset α)
    (owner : α → Fin k)
    (f : α → M) :
    Finset.sum Finset.univ (fun i : Fin k ↦ Finset.sum (s.filter (fun a ↦ owner a = i)) f) =
      Finset.sum s f := by
  -- Sum the fibers of the owner map over all indices; `Finset.univ` captures every owner.
  simpa using Finset.sum_fiberwise_eq_sum_filter s Finset.univ owner f

/-- Helper for Lemma 4.41: multiplying a positive-weight center of mass by its total weight
recovers the original weighted sum. -/
lemma smul_centerMass_eq_sum_smul
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι)
    (w : ι → ℝ)
    (z : ι → E)
    (hsum_ne : ∑ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, w i) • s.centerMass w z = ∑ i ∈ s, w i • z i := by
  -- Unfold the center of mass once and cancel the nonzero total weight.
  rw [Finset.centerMass, smul_smul]
  simp [hsum_ne]

/-- Helper for Lemma 4.41: a point in the global vertex hull can be regrouped into one local
convex-hull point for each block. -/
lemma exists_indexed_convex_decomposition_of_mem_convexHull_biUnion
    (P : Fin k → Set (Fin n → ℝ))
    (hP_nonempty : ∀ i : Fin k, (P i).Nonempty)
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    {q : Fin n → ℝ}
    (hq : q ∈ convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ))) :
    ∃ coeff : Fin k → ℝ, ∃ v : Fin k → Fin n → ℝ,
      (∀ i, 0 ≤ coeff i) ∧
      (∑ i, coeff i = 1) ∧
      (∀ i, v i ∈ convexHull ℝ (V i : Set (Fin n → ℝ))) ∧
      q = ∑ i, coeff i • v i := by
  classical
  by_cases hk : k = 0
  · subst hk
    have : False := by
      simpa [convexHull_empty] using hq
    exact False.elim this
  · let S : Finset (Fin n → ℝ) := Finset.univ.biUnion V
    have hqS : q ∈ convexHull ℝ (S : Set (Fin n → ℝ)) := by
      simpa [S] using hq
    rcases (Finset.mem_convexHull').1 hqS with ⟨w, hw_nonneg, hw_sum, hw_q⟩
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    let i0 : Fin k := ⟨0, hk_pos⟩
    have howner_exists : ∀ y ∈ S, ∃ i : Fin k, y ∈ V i := by
      intro y hy
      have hy' : ∃ i : Fin k, i ∈ Finset.univ ∧ y ∈ V i := by
        simpa [S] using hy
      rcases hy' with ⟨i, -, hyi⟩
      exact ⟨i, hyi⟩
    let owner : (Fin n → ℝ) → Fin k := fun y ↦
      if hy : y ∈ S then Classical.choose (howner_exists y hy) else i0
    have howner_mem : ∀ {y}, y ∈ S → y ∈ V (owner y) := by
      intro y hy
      have hy_owner : y ∈ V (Classical.choose (howner_exists y hy)) :=
        Classical.choose_spec (howner_exists y hy)
      simpa [owner, hy] using hy_owner
    let fiber : Fin k → Finset (Fin n → ℝ) := fun i ↦ S.filter (fun y ↦ owner y = i)
    let coeff : Fin k → ℝ := fun i ↦ ∑ y ∈ fiber i, w y
    have hcoeff_nonneg : ∀ i, 0 ≤ coeff i := by
      intro i
      -- Each regrouped coefficient is a sum of nonnegative original weights.
      exact Finset.sum_nonneg fun y hy ↦ hw_nonneg y (Finset.mem_filter.1 hy).1
    have hcoeff_sum : ∑ i, coeff i = 1 := by
      -- Summing the owner fibers recovers the original convex weights.
      calc
        ∑ i : Fin k, coeff i = ∑ i : Fin k, ∑ y ∈ fiber i, w y := by
          simp [coeff]
        _ = ∑ y ∈ S, w y := by
          simpa [fiber] using owner_partitioned_sum_eq S owner w
        _ = 1 := hw_sum
    have hv_exists :
        ∀ i : Fin k, ∃ v0 : Fin n → ℝ, v0 ∈ convexHull ℝ (V i : Set (Fin n → ℝ)) := by
      intro i
      exact local_vertex_hull_nonempty P hP_nonempty V R h_repr i
    choose v0 hv0 using hv_exists
    let v : Fin k → Fin n → ℝ := fun i ↦
      if hci : coeff i = 0 then v0 i else (fiber i).centerMass w id
    have hv_mem : ∀ i, v i ∈ convexHull ℝ (V i : Set (Fin n → ℝ)) := by
      intro i
      by_cases hci : coeff i = 0
      · -- Zero-mass fibers use the fixed local witness from `P i`.
        simpa [v, hci] using hv0 i
      · -- Positive-mass fibers use the center of mass of the local owner fiber.
        have hcoeff_pos : 0 < coeff i :=
          lt_of_le_of_ne (hcoeff_nonneg i) (by simpa [eq_comm] using hci)
        have hfiber_pos : 0 < ∑ y ∈ fiber i, w y := by
          simpa [coeff] using hcoeff_pos
        have hfiber_mem : ∀ y ∈ fiber i, y ∈ (V i : Set (Fin n → ℝ)) := by
          intro y hy
          have hyS : y ∈ S := (Finset.mem_filter.1 hy).1
          have hyOwner : owner y = i := (Finset.mem_filter.1 hy).2
          simpa [hyOwner] using howner_mem hyS
        have hcenter_mem :
            (fiber i).centerMass w id ∈ convexHull ℝ (V i : Set (Fin n → ℝ)) := by
          -- The positive owner fiber is a convex combination inside the `i`-th vertex family.
          exact Finset.centerMass_mem_convexHull (t := fiber i) (w := w)
            (fun y hy ↦ hw_nonneg y (Finset.mem_filter.1 hy).1) hfiber_pos hfiber_mem
        simpa [v, hci] using hcenter_mem
    have hfiber_term :
        ∀ i, coeff i • v i = ∑ y ∈ fiber i, w y • y := by
      intro i
      by_cases hci : coeff i = 0
      · have hzero_weights : ∀ y ∈ fiber i, w y = 0 := by
          intro y hy
          have hsum_zero : ∑ y ∈ fiber i, w y = 0 := by
            simpa [coeff] using hci
          exact ((Finset.sum_eq_zero_iff_of_nonneg
            (fun z hz ↦ hw_nonneg z (Finset.mem_filter.1 hz).1)).1 hsum_zero) y hy
        have hsum_smul_zero : ∑ y ∈ fiber i, w y • y = 0 := by
          refine Finset.sum_eq_zero ?_
          intro y hy
          simp [hzero_weights y hy]
        -- Zero-mass fibers contribute nothing to the regrouped sum.
        simpa [coeff, v, hci, hsum_smul_zero]
      · have hsum_ne : ∑ y ∈ fiber i, w y ≠ 0 := by
          simpa [coeff] using hci
        -- Positive-mass fibers are rewritten through the center-of-mass identity.
        simpa [coeff, v, hci] using
          smul_centerMass_eq_sum_smul (s := fiber i) (w := w) (z := id) hsum_ne
    refine ⟨coeff, v, hcoeff_nonneg, hcoeff_sum, hv_mem, ?_⟩
    -- Summing the fiber contributions recovers the original convex-hull witness for `q`.
    calc
      q = ∑ y ∈ S, w y • y := hw_q.symm
      _ = ∑ i : Fin k, ∑ y ∈ fiber i, w y • y := by
        symm
        simpa [fiber] using owner_partitioned_sum_eq S owner (fun y ↦ w y • y)
      _ = ∑ i : Fin k, coeff i • v i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hfiber_term i).symm

/-- Helper for Lemma 4.41: a conic combination from the global ray biunion can be regrouped into
one local cone-hull vector for each block. -/
lemma exists_indexed_cone_decomposition_of_mem_coneHull_biUnion
    (R : Fin k → Finset (Fin n → ℝ))
    {c : Fin n → ℝ}
    (hc : c ∈ (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
      Set (Fin n → ℝ))) :
    ∃ r : Fin k → Fin n → ℝ,
      (∀ i, r i ∈ (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) ∧
      c = ∑ i, r i := by
  classical
  by_cases hk : k = 0
  · subst hk
    simpa using hc
  · rcases PointedCone.mem_hull_set.mp hc with ⟨coeff, hcoeff_support, hcoeff_nonneg, hcoeff_sum⟩
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    let i0 : Fin k := ⟨0, hk_pos⟩
    have howner_exists : ∀ y ∈ coeff.support, ∃ i : Fin k, y ∈ R i := by
      intro y hy
      rcases Finset.mem_biUnion.1 (hcoeff_support hy) with ⟨i, -, hyi⟩
      exact ⟨i, hyi⟩
    let owner : (Fin n → ℝ) → Fin k := fun y ↦
      if hy : y ∈ coeff.support then Classical.choose (howner_exists y hy) else i0
    have howner_mem : ∀ {y}, y ∈ coeff.support → y ∈ R (owner y) := by
      intro y hy
      have hyne : coeff y ≠ 0 := Finsupp.mem_support_iff.1 hy
      simp [owner, hyne, Classical.choose_spec (howner_exists y hy)]
    let r : Fin k → Fin n → ℝ := fun i ↦
      (coeff.filter (fun y ↦ owner y = i)).sum fun y a ↦ a • y
    have hr_mem :
        ∀ i, r i ∈ (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      intro i
      -- Each filtered witness remains supported on the `i`-th ray family with nonnegative weights.
      refine PointedCone.mem_hull_set.mpr ?_
      refine ⟨coeff.filter (fun y ↦ owner y = i), ?_, ?_, rfl⟩
      · intro y hy
        have hy' : y ∈ coeff.support.filter (fun z ↦ owner z = i) := by
          simpa [Finsupp.support_filter] using hy
        have hySupport : y ∈ coeff.support := (Finset.mem_filter.1 hy').1
        have hyOwner : owner y = i := (Finset.mem_filter.1 hy').2
        simpa [hyOwner] using howner_mem hySupport
      · intro y
        by_cases hy : owner y = i
        · simp [Finsupp.filter_apply, hy, hcoeff_nonneg y]
        · simp [Finsupp.filter_apply, hy]
    have hr_eq :
        ∀ i, r i = Finset.sum (coeff.support.filter (fun y ↦ owner y = i))
          (fun y ↦ coeff y • y) := by
      intro i
      unfold r
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      have hyOwner : owner y = i := (Finset.mem_filter.1 hy).2
      simp [hyOwner]
    refine ⟨r, hr_mem, ?_⟩
    -- Summing the owner fibers recovers the original conic witness.
    calc
      c = coeff.sum (fun y a ↦ a • y) := hcoeff_sum.symm
      _ = Finset.sum coeff.support (fun y ↦ coeff y • y) := by simp [Finsupp.sum]
      _ =
          Finset.sum Finset.univ
            (fun i : Fin k ↦ Finset.sum (coeff.support.filter (fun y ↦ owner y = i))
              (fun y ↦ coeff y • y)) := by
        symm
        exact owner_partitioned_sum_eq coeff.support owner (fun y ↦ coeff y • y)
      _ = ∑ i : Fin k, r i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hr_eq i).symm

/-- Helper for Lemma 4.41: the source epsilon-approximant coefficients are nonnegative and still
form a convex combination after adding the `k` uniform epsilon blocks. -/
lemma source_approximant_coefficients_nonneg_sum
    {coeff : Fin k → ℝ}
    {η : ℝ}
    (I : Finset (Fin k))
    (hI : I = Finset.univ.filter (fun i ↦ 0 < coeff i))
    (hcoeff_nonneg : ∀ i, 0 ≤ coeff i)
    (hcoeff_sum : ∑ i, coeff i = 1)
    (hI_nonempty : I.Nonempty)
    (hsmall : ∀ i ∈ I, ((k : ℝ) / (I.card : ℝ)) * η ≤ coeff i) :
    let α : Fin k → ℝ := fun i ↦
      if i ∈ I then coeff i - ((k : ℝ) / (I.card : ℝ)) * η else 0
    (∀ i, 0 ≤ α i) ∧
      (∑ i, α i) + ∑ i : Fin k, η = 1 := by
  let α : Fin k → ℝ := fun i ↦
    if i ∈ I then coeff i - ((k : ℝ) / (I.card : ℝ)) * η else 0
  have hα_nonneg : ∀ i, 0 ≤ α i := by
    -- On `I` we remove at most the prescribed block mass; off `I` the approximant weight is `0`.
    intro i
    by_cases hi : i ∈ I
    · simp [α, hi, sub_nonneg, hsmall i hi]
    · simp [α, hi]
  have hcoeff_zero_off : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ 0 < coeff i), coeff i = 0 := by
    -- Outside the positive-weight set, nonnegativity forces the original coefficient to vanish.
    intro i hi
    have hnotpos : ¬ 0 < coeff i := (Finset.mem_filter.1 hi).2
    exact le_antisymm (le_of_not_gt hnotpos) (hcoeff_nonneg i)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun i : Fin k ↦ 0 < coeff i) coeff
  have hzero := Finset.sum_eq_zero hcoeff_zero_off
  have hsum_I : Finset.sum I coeff = 1 := by
    -- Splitting `∑ coeff i` into the positive and nonpositive blocks leaves only the positive part.
    rw [hI]
    linarith [hsplit, hzero, hcoeff_sum]
  have hIcard_ne : (I.card : ℝ) ≠ 0 := by
    -- The source proof uses `|I|` in the denominator, so we record that `I` is nonempty.
    exact_mod_cast Finset.card_ne_zero.mpr hI_nonempty
  have hsum_alpha : ∑ i, α i = 1 - (k : ℝ) * η := by
    -- The new coefficients are the original positive coefficients with exactly `k * η` removed.
    calc
      ∑ i, α i = Finset.sum I (fun i ↦ coeff i - ((k : ℝ) / (I.card : ℝ)) * η) := by
        simp [α]
      _ = Finset.sum I coeff - Finset.sum I (fun _ ↦ ((k : ℝ) / (I.card : ℝ)) * η) := by
        rw [Finset.sum_tsub_distrib]
        intro i hi
        exact hsmall i hi
      _ = 1 - Finset.sum I (fun _ ↦ ((k : ℝ) / (I.card : ℝ)) * η) := by
        rw [hsum_I]
      _ = 1 - (I.card : ℝ) * (((k : ℝ) / (I.card : ℝ)) * η) := by
        simp
      _ = 1 - (k : ℝ) * η := by
        field_simp [hIcard_ne]
  constructor
  · exact hα_nonneg
  · -- Adding back the `k` uniform epsilon blocks restores total mass `1`.
    calc
      (∑ i, α i) + ∑ i : Fin k, η = (1 - (k : ℝ) * η) + (k : ℝ) * η := by
        rw [hsum_alpha]
        simp
      _ = 1 := by
        ring

/-- Helper for Lemma 4.41: once the source coefficients are admissible, the textbook
epsilon-approximant is a convex combination of points from `⋃ i, P i`. -/
lemma source_approximant_mem_convexHull_iUnion
    (P : Fin k → Set (Fin n → ℝ))
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    {α : Fin k → ℝ}
    {v r : Fin k → Fin n → ℝ}
    {η : ℝ}
    (hη : 0 < η)
    (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_sum : (∑ i, α i) + ∑ i : Fin k, η = 1)
    (hv_mem : ∀ i, v i ∈ convexHull ℝ (V i : Set (Fin n → ℝ)))
    (hr_mem : ∀ i, r i ∈ (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    ((∑ i, α i • v i) + ∑ i, η • (v i + (1 / η) • r i)) ∈
      convexHull ℝ (⋃ i : Fin k, P i) := by
  let w : Fin k ⊕ Fin k → ℝ := Sum.elim α (fun _ ↦ η)
  let z : Fin k ⊕ Fin k → Fin n → ℝ :=
    Sum.elim v (fun i ↦ v i + (1 / η) • r i)
  have hz_mem : ∀ s, z s ∈ ⋃ i : Fin k, P i := by
    intro s
    cases s with
    | inl i =>
        -- The unscaled local vertex point is already in `P i` by adding the zero cone element.
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        rw [h_repr i]
        refine ⟨v i, hv_mem i, 0, ?_, by simpa [z]⟩
        simpa using (show (0 : Fin n → ℝ) ∈
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) from zero_mem _)
    | inr i =>
        -- The scaled ray correction remains in the same local cone because `η > 0`.
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        rw [h_repr i]
        have hscaled_mem :
            (1 / η) • r i ∈ (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
          have hscalar_nonneg : 0 ≤ 1 / η := one_div_nonneg.mpr hη.le
          simpa using
            (Submodule.smul_mem (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)))
              ⟨1 / η, hscalar_nonneg⟩ (hr_mem i))
        exact ⟨v i, hv_mem i, (1 / η) • r i, hscaled_mem, rfl⟩
  have hw_nonneg : ∀ s, 0 ≤ w s := by
    intro s
    cases s with
    | inl i =>
        simpa [w] using hα_nonneg i
    | inr i =>
        simpa [w] using hη.le
  -- Package the two source families into one finite convex combination indexed by `Fin k ⊕ Fin k`.
  refine mem_convexHull_of_exists_fintype w z hw_nonneg ?_ hz_mem ?_
  · simpa [w, Fintype.sum_sum_type] using hα_sum
  · simpa [w, z, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 4.41: the positive support of the coefficient vector has a uniform positive
lower bound. -/
lemma exists_pos_coeff_lower_bound_on_positive_support
    {coeff : Fin k → ℝ}
    (I : Finset (Fin k))
    (hI : I = Finset.univ.filter (fun i ↦ 0 < coeff i))
    (hI_nonempty : I.Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ I, δ ≤ coeff i := by
  let values : Finset ℝ := I.image coeff
  have hvalues_nonempty : values.Nonempty := hI_nonempty.image coeff
  refine ⟨values.min' hvalues_nonempty, ?_, ?_⟩
  · -- Every value on the positive support is positive, so the finite minimum stays positive.
    rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨i, hiI, hmin⟩
    have hi_filter : i ∈ Finset.univ.filter (fun j : Fin k ↦ 0 < coeff j) := by
      simpa [hI] using hiI
    have hi_pos : 0 < coeff i := (Finset.mem_filter.1 hi_filter).2
    rwa [← hmin]
  · -- Membership in the image lets `Finset.min'_le` bound every positive coefficient below.
    intro i hi
    exact Finset.min'_le values _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- Helper for Lemma 4.41: the textbook epsilon-approximant differs from the target point by a
single scalar multiple of the fixed drift vector. -/
lemma source_approximant_error_eq_smul_drift
    {coeff : Fin k → ℝ}
    {v r : Fin k → Fin n → ℝ}
    {η : ℝ}
    (I : Finset (Fin k))
    (hI : I = Finset.univ.filter (fun i ↦ 0 < coeff i))
    (hcoeff_nonneg : ∀ i, 0 ≤ coeff i)
    (hη : 0 < η) :
    let α : Fin k → ℝ := fun i ↦
      if i ∈ I then coeff i - ((k : ℝ) / (I.card : ℝ)) * η else 0
    let d : Fin n → ℝ :=
      (∑ i : Fin k, v i) -
        Finset.sum I (fun i ↦ (((k : ℝ) / (I.card : ℝ)) • v i))
    ((∑ i, α i • v i) + ∑ i, η • (v i + (1 / η) • r i)) -
        ((∑ i, coeff i • v i) + ∑ i, r i) = η • d := by
  let κ : ℝ := (k : ℝ) / (I.card : ℝ)
  let α : Fin k → ℝ := fun i ↦ if i ∈ I then coeff i - κ * η else 0
  let d : Fin n → ℝ := (∑ i : Fin k, v i) - Finset.sum I (fun i ↦ κ • v i)
  have hcoeff_zero_off : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ 0 < coeff i), coeff i = 0 := by
    -- Outside the positive support, nonnegativity forces the coefficient to vanish.
    intro i hi
    have hnotpos : ¬ 0 < coeff i := (Finset.mem_filter.1 hi).2
    exact le_antisymm (le_of_not_gt hnotpos) (hcoeff_nonneg i)
  have hcoeff_sum_on_I :
      ∑ i : Fin k, coeff i • v i = Finset.sum I (fun i ↦ coeff i • v i) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun i : Fin k ↦ 0 < coeff i) (f := fun i ↦ coeff i • v i)
    have hzero :
        Finset.sum (Finset.univ.filter (fun i ↦ ¬ 0 < coeff i)) (fun i ↦ coeff i • v i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hcoeff_zero_off i hi]
    rw [hzero, add_zero] at hsplit
    simpa [hI] using hsplit.symm
  have halpha_sum :
      ∑ i : Fin k, α i • v i = Finset.sum I (fun i ↦ (coeff i - κ * η) • v i) := by
    -- Off the positive support the approximant uses coefficient `0`.
    simp [α]
  have hscaled_sum :
      ∑ i : Fin k, η • (v i + (1 / η) • r i) = η • ∑ i : Fin k, v i + ∑ i : Fin k, r i := by
    -- Pull the common scalar `η` through the sum and cancel the `1 / η` factor on the rays.
    calc
      ∑ i : Fin k, η • (v i + (1 / η) • r i)
          = ∑ i : Fin k, (η • v i + r i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_add, smul_smul, hη.ne']
      _ = (∑ i : Fin k, η • v i) + ∑ i : Fin k, r i := by
        rw [Finset.sum_add_distrib]
      _ = η • ∑ i : Fin k, v i + ∑ i : Fin k, r i := by
        simp [Finset.smul_sum]
  have hkappa_sum :
      Finset.sum I (fun i ↦ ((κ * η) • v i)) = η • Finset.sum I (fun i ↦ κ • v i) := by
    -- The fixed drift can be factored as one scalar `η` times a single vector sum.
    calc
      Finset.sum I (fun i ↦ ((κ * η) • v i)) = Finset.sum I (fun i ↦ η • (κ • v i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [smul_smul, mul_comm]
      _ = η • Finset.sum I (fun i ↦ κ • v i) := by
        simp [Finset.smul_sum]
  have hmain :
      ((∑ i : Fin k, α i • v i) + ∑ i : Fin k, η • (v i + (1 / η) • r i)) -
          ((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i) =
        η • d := by
    -- First cancel the ray sum, then isolate the coefficient correction over the positive support.
    calc
      ((∑ i : Fin k, α i • v i) + ∑ i : Fin k, η • (v i + (1 / η) • r i)) -
          ((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i)
          = (∑ i : Fin k, α i • v i) + η • ∑ i : Fin k, v i - ∑ i : Fin k, coeff i • v i := by
              rw [hscaled_sum]
              abel
      _ = Finset.sum I (fun i ↦ (coeff i - κ * η) • v i) + η • ∑ i : Fin k, v i -
            Finset.sum I (fun i ↦ coeff i • v i) := by
              rw [halpha_sum, hcoeff_sum_on_I]
      _ = η • ∑ i : Fin k, v i - Finset.sum I (fun i ↦ ((κ * η) • v i)) := by
            simp_rw [sub_smul]
            rw [Finset.sum_sub_distrib]
            abel
      _ = η • ∑ i : Fin k, v i - η • Finset.sum I (fun i ↦ κ • v i) := by
            rw [hkappa_sum]
      _ = η • ((∑ i : Fin k, v i) - Finset.sum I (fun i ↦ κ • v i)) := by
            rw [smul_sub]
      _ = η • d := by
            rfl
  simpa [α, d, κ] using hmain

/-- Helper for Lemma 4.41: the cone generated by a finite ray family is closed. -/
lemma isClosed_pointedCone_hull_finset
    (s : Finset (Fin n → ℝ)) :
    IsClosed ((PointedCone.hull ℝ (s : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  let C : PointedCone ℝ (Fin n → ℝ) := PointedCone.hull ℝ (s : Set (Fin n → ℝ))
  have hC_fg : C.FG := by
    -- A cone hull over a finite set is finitely generated by construction.
    simpa [C] using Submodule.fg_span (Finset.finite_toSet s)
  have hC_polyhedral : is_polyhedral_cone (C : Set (Fin n → ℝ)) := by
    -- Convert finite generation to the project's polyhedral-cone owner.
    exact (is_finitely_generated_cone_iff_is_polyhedral_cone).mp hC_fg
  rcases hC_polyhedral with ⟨K, hK_dualfg, hK_eq⟩
  rcases hK_dualfg with ⟨t, ht⟩
  have hK_closed : IsClosed (K : Set (Fin n → ℝ)) := by
    -- A cone that is the dual of a finite set is closed by the dual-cone topology API.
    simpa [ht] using
      PointedCone.isClosed_dual
        (p := dotProductBilin ℝ ℝ)
        (s := (t : Set (Fin n → ℝ)))
        (fun x ↦ by fun_prop)
  simpa [C] using hK_eq ▸ hK_closed

/-- Helper for Lemma 4.41: the global vertex-hull plus global ray-cone is closed. -/
lemma isClosed_convexHull_biUnion_add_coneHull
    (V R : Fin k → Finset (Fin n → ℝ)) :
    IsClosed
      (convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ))) := by
  let Q := convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ))
  let C := (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
    Set (Fin n → ℝ))
  have hQ_compact : IsCompact Q := by
    -- The convex hull of finitely many vertices is compact.
    simpa [Q] using
      (Finset.finite_toSet (Finset.univ.biUnion V)).isCompact_convexHull ℝ
  have hC_closed : IsClosed C := by
    -- The global ray cone is generated by finitely many rays, so it is closed.
    simpa [C] using isClosed_pointedCone_hull_finset (Finset.univ.biUnion R)
  -- A compact set plus a closed set is closed in the ambient finite-dimensional additive group.
  simpa [Q, C] using hC_closed.add_left_of_isCompact hQ_compact

/-- Lemma 4.41. Let `P i ⊆ ℝ^n` for `i = 1, ..., k` be nonempty polyhedra, and let `V i` and
`R i` be finite sets such that `P i = conv(V i) + cone(R i)`. Then the closure of the convex hull
of `⋃ i, P i` is the Minkowski sum of the convex hull of `⋃ i, V i` and the cone generated by
`⋃ i, R i`. -/
theorem closure_convexHull_iUnion_polyhedra_eq_convexHull_biUnion_add_coneHull
    (P : Fin k → Set (Fin n → ℝ))
    (hP_nonempty : ∀ i : Fin k, (P i).Nonempty)
    (V R : Fin k → Finset (Fin n → ℝ))
    (h_repr :
      ∀ i : Fin k,
        P i = convexHull ℝ (V i : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    closure (convexHull ℝ (⋃ i : Fin k, P i)) =
      convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ)) := by
  let Q := convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ))
  let C := (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
    Set (Fin n → ℝ))
  have hUnionSubset : (⋃ i : Fin k, P i) ⊆ Q + C := by
    -- First place every component polyhedron inside the common global sum.
    simpa [Q, C] using iUnion_subset_global_vertexCone_sum P V R h_repr
  have hGlobalConvex : Convex ℝ (Q + C) := by
    -- The right-hand side is convex because it is a sum of two convex sets.
    simpa [Q, C] using global_vertexCone_sum_convex V R
  have hConvexHullSubset : convexHull ℝ (⋃ i : Fin k, P i) ⊆ Q + C := by
    -- The convex hull is the smallest convex set containing the union.
    exact convexHull_min hUnionSubset hGlobalConvex
  have hForward : closure (convexHull ℝ (⋃ i : Fin k, P i)) ⊆ Q + C := by
    -- Route correction: the easy inclusion is reduced to proving that the global sum is closed.
    have hClosed : IsClosed (Q + C) := by
      -- The closedness package is proved once in the dedicated helper above.
      simpa [Q, C] using isClosed_convexHull_biUnion_add_coneHull V R
    exact closure_minimal hConvexHullSubset hClosed
  have hReverse : Q + C ⊆ closure (convexHull ℝ (⋃ i : Fin k, P i)) := by
    intro x hx
    rcases hx with ⟨q, hq, c, hc, rfl⟩
    rcases exists_indexed_convex_decomposition_of_mem_convexHull_biUnion
        P hP_nonempty V R h_repr hq with
      ⟨coeff, v, hcoeff_nonneg, hcoeff_sum, hv_mem, hq_eq⟩
    rcases exists_indexed_cone_decomposition_of_mem_coneHull_biUnion R hc with
      ⟨r, hr_mem, hc_eq⟩
    -- Route correction: both global pieces are now reduced to indexed source data.
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    let I : Finset (Fin k) := Finset.univ.filter (fun i ↦ 0 < coeff i)
    have hI_nonempty : I.Nonempty := by
      by_contra hI_empty
      have hI_eq : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI_empty
      have hcoeff_zero : ∀ i, coeff i = 0 := by
        intro i
        have hi_not : i ∉ I := by simpa [hI_eq]
        have hnotpos : ¬ 0 < coeff i := by
          simpa [I] using hi_not
        exact le_antisymm (le_of_not_gt hnotpos) (hcoeff_nonneg i)
      have : (∑ i, coeff i) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact hcoeff_zero i
      linarith [hcoeff_sum, this]
    have hI : I = Finset.univ.filter (fun i ↦ 0 < coeff i) := by
      rfl
    rcases exists_pos_coeff_lower_bound_on_positive_support I hI hI_nonempty with
      ⟨δ, hδ_pos, hδ_le⟩
    have hIcard_nat_pos : 0 < I.card := Finset.card_pos.mpr hI_nonempty
    have hIcard_pos : 0 < (I.card : ℝ) := by
      exact_mod_cast hIcard_nat_pos
    have hIcard_ne : (I.card : ℝ) ≠ 0 := ne_of_gt hIcard_pos
    have hIcard_le_k : I.card ≤ k := by
      simpa [I] using Finset.card_filter_le (Finset.univ) (fun i : Fin k ↦ 0 < coeff i)
    have hk_nat_pos : 0 < k := lt_of_lt_of_le hIcard_nat_pos hIcard_le_k
    have hk_pos : 0 < (k : ℝ) := by
      exact_mod_cast hk_nat_pos
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    let d : Fin n → ℝ :=
      (∑ i : Fin k, v i) -
        Finset.sum I (fun i ↦ (((k : ℝ) / (I.card : ℝ)) • v i))
    let M : ℝ := ‖d‖ + 1
    have hM_pos : 0 < M := by
      -- The metric-control denominator is strictly positive by construction.
      dsimp [M]
      linarith [norm_nonneg d]
    let η : ℝ := min (δ * (I.card : ℝ) / (2 * (k : ℝ))) (ε / (2 * M))
    have hη_pos : 0 < η := by
      -- The explicit minimum simultaneously preserves positive coefficients and the distance bound.
      have hcoeff_branch_pos : 0 < δ * (I.card : ℝ) / (2 * (k : ℝ)) := by
        exact div_pos (mul_pos hδ_pos hIcard_pos) (by positivity)
      have hmetric_branch_pos : 0 < ε / (2 * M) := by
        exact div_pos hε (by positivity)
      dsimp [η]
      exact lt_min hcoeff_branch_pos hmetric_branch_pos
    let α : Fin k → ℝ := fun i ↦
      if i ∈ I then coeff i - ((k : ℝ) / (I.card : ℝ)) * η else 0
    have hsmall : ∀ i ∈ I, ((k : ℝ) / (I.card : ℝ)) * η ≤ coeff i := by
      intro i hi
      have hη_le : η ≤ δ * (I.card : ℝ) / (2 * (k : ℝ)) := by
        dsimp [η]
        exact min_le_left _ _
      have hratio_nonneg : 0 ≤ (k : ℝ) / (I.card : ℝ) := by
        exact div_nonneg hk_pos.le hIcard_pos.le
      have hscaled :=
        mul_le_mul_of_nonneg_left hη_le hratio_nonneg
      have hhalf :
          ((k : ℝ) / (I.card : ℝ)) * η ≤ δ / 2 := by
        have hcalc :
            ((k : ℝ) / (I.card : ℝ)) * (δ * (I.card : ℝ) / (2 * (k : ℝ))) = δ / 2 := by
          field_simp [hIcard_ne, hk_ne]
        rwa [hcalc] at hscaled
      linarith [hhalf, hδ_le i hi]
    have hα_data :
        (∀ i, 0 ≤ α i) ∧ ((∑ i, α i) + ∑ i : Fin k, η = 1) := by
      -- The modified coefficients remain nonnegative and still add to total mass `1`.
      simpa [α] using
        source_approximant_coefficients_nonneg_sum
          (coeff := coeff) (η := η) I hI hcoeff_nonneg hcoeff_sum hI_nonempty hsmall
    rcases hα_data with ⟨hα_nonneg, hα_sum⟩
    let xη : Fin n → ℝ :=
      ((∑ i, α i • v i) + ∑ i, η • (v i + (1 / η) • r i))
    have hxη_mem : xη ∈ convexHull ℝ (⋃ i : Fin k, P i) := by
      -- The textbook approximant is a convex combination of points from the original union.
      simpa [xη] using
        source_approximant_mem_convexHull_iUnion
          P V R h_repr hη_pos hα_nonneg hα_sum hv_mem hr_mem
    have herror : xη - ((∑ i, coeff i • v i) + ∑ i, r i) = η • d := by
      -- All dependence on `η` is isolated into one scalar times the fixed drift vector.
      simpa [xη, α, d] using
        source_approximant_error_eq_smul_drift
          (coeff := coeff) (v := v) (r := r) (η := η) I hI hcoeff_nonneg hη_pos
    have hdist :
        dist ((∑ i, coeff i • v i) + ∑ i, r i) xη < ε := by
      have hη_nonneg : 0 ≤ η := hη_pos.le
      have hnorm_le_M : ‖d‖ ≤ M := by
        dsimp [M]
        linarith [norm_nonneg d]
      have hη_le_metric : η ≤ ε / (2 * M) := by
        dsimp [η]
        exact min_le_right _ _
      have hηM_le_half : η * M ≤ ε / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hη_le_metric hM_pos.le
        have hcalc : (ε / (2 * M)) * M = ε / 2 := by
          field_simp [ne_of_gt hM_pos]
        rwa [hcalc] at hmul
      have hηM_lt : η * M < ε := by
        have hhalf_lt : ε / 2 < ε := by
          linarith
        exact lt_of_le_of_lt hηM_le_half hhalf_lt
      -- The distance estimate is now a direct norm bound on the fixed drift vector.
      rw [dist_eq_norm]
      have hsub :
          ((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i) - xη =
            -(xη - ((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i)) := by
        abel
      calc
        ‖((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i) - xη‖
            = ‖xη - ((∑ i : Fin k, coeff i • v i) + ∑ i : Fin k, r i)‖ := by
                rw [hsub, norm_neg]
        _ = ‖η • d‖ := by
              rw [herror]
        _ = η * ‖d‖ := by
              rw [norm_smul]
              simp [Real.norm_eq_abs, abs_of_nonneg hη_nonneg]
        _ ≤ η * M := by
              exact mul_le_mul_of_nonneg_left hnorm_le_M hη_nonneg
        _ < ε := hηM_lt
    refine ⟨xη, hxη_mem, ?_⟩
    -- Rewriting the target point back to `q + c` closes the source-faithful closure argument.
    simpa [hq_eq, hc_eq] using hdist
  exact Set.Subset.antisymm
    (by
      -- The easy inclusion is already the closedness argument proved above.
      simpa [Q, C] using hForward)
    (by
      -- The hard inclusion is now reduced to the source epsilon-approximant closure step.
      simpa [Q, C] using hReverse)

end Lemma441
