/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_definition_3_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2

open scoped BigOperators Matrix Pointwise

-- Domain-style sampling for this refine pass:
-- * source-facing owner file: `ch4_sec4_9_theorem_4_39`
-- * source-facing Balas owners reused directly here:
--   `balas_nonempty_family`, `balas_lifted_polyhedron`, `balas_x_projection`
-- * core/canonical ambient owners: `polyhedron_le_set`, `convexHull`, `closure`,
--   `PointedCone.hull`
-- This file now reuses the upstream guarded-family owner directly; it does not keep a parallel
-- local ray-family wrapper.

section Theorem442

variable {n k : ℕ}

/-- Helper for Theorem 4.42: each component finite family sits inside the global finite biunion. -/
lemma subset_biUnion_component
    (F : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    (F i : Set (Fin n → ℝ)) ⊆ (Finset.univ.biUnion F : Set (Fin n → ℝ)) := by
  -- A point in the `i`-th block is automatically in the total finite biunion.
  intro x hx
  change x ∈ Finset.univ.biUnion F
  exact Finset.mem_biUnion.2 ⟨i, by simp, hx⟩

/-- Helper for Theorem 4.42: the `i`-th vertex hull embeds into the global vertex hull. -/
lemma convexHull_subset_biUnion
    (V : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    convexHull ℝ (V i : Set (Fin n → ℝ)) ⊆
      convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) := by
  -- Monotonicity of `convexHull` reduces the claim to component-to-global set inclusion.
  exact convexHull_mono (subset_biUnion_component V i)

/-- Helper for Theorem 4.42: the `i`-th ray cone embeds into the global cone hull. -/
lemma coneHull_subset_biUnion
    (R : Fin k → Finset (Fin n → ℝ)) (i : Fin k) :
    (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
      (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  -- `PointedCone.hull` is monotone with respect to the generating set.
  exact Submodule.span_mono (subset_biUnion_component R i)

/-- Helper for Theorem 4.42: each input polyhedron lies in the common global vertex-hull plus
global ray-cone. -/
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
  -- Rewrite the component decomposition and move each summand into the global owner.
  intro x hx
  rw [h_repr i] at hx
  rcases hx with ⟨v, hv, r, hr, rfl⟩
  exact ⟨v, convexHull_subset_biUnion V i hv, r, coneHull_subset_biUnion R i hr, rfl⟩

/-- Helper for Theorem 4.42: the whole family union lies in the global vertex-hull plus
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
  -- Reduce union membership to one component and then use the component inclusion.
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  exact component_subset_global_vertexCone_sum P V R h_repr i hxi

/-- Helper for Theorem 4.42: the global vertex-hull plus global ray-cone is convex. -/
lemma global_vertexCone_sum_convex
    (V R : Fin k → Finset (Fin n → ℝ)) :
    Convex ℝ
      (convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ))) := by
  -- Both summands are convex, so their Minkowski sum is convex.
  exact (convex_convexHull ℝ _).add (PointedCone.convex _)

/-- Helper for Theorem 4.42: nonemptiness of each input polyhedron yields a point in the
corresponding local vertex hull. -/
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
  -- Unpack a point of `P i` and retain its convex-hull part.
  rcases hP_nonempty i with ⟨x, hx⟩
  rw [h_repr i] at hx
  rcases hx with ⟨v0, hv0, r, hr, hxr⟩
  exact ⟨v0, hv0⟩

/-- Helper for Theorem 4.42: summing a finite family by owner fibers recovers the original sum. -/
lemma owner_partitioned_sum_eq
    {α M : Type*} [AddCommMonoid M]
    (s : Finset α)
    (owner : α → Fin k)
    (f : α → M) :
    Finset.sum Finset.univ (fun i : Fin k ↦ Finset.sum (s.filter (fun a ↦ owner a = i)) f) =
      Finset.sum s f := by
  -- `Finset.univ` enumerates every owner fiber exactly once.
  simpa using Finset.sum_fiberwise_eq_sum_filter s Finset.univ owner f

/-- Helper for Theorem 4.42: scaling a positive-weight center of mass recovers the original
weighted sum. -/
lemma smul_centerMass_eq_sum_smul
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι)
    (w : ι → ℝ)
    (z : ι → E)
    (hsum_ne : ∑ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, w i) • s.centerMass w z = ∑ i ∈ s, w i • z i := by
  -- Expand `centerMass` once and cancel the nonzero total weight.
  rw [Finset.centerMass, smul_smul]
  simp [hsum_ne]

/-- Helper for Theorem 4.42: a point in the global vertex hull can be regrouped into one
local convex-hull point for each block. -/
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
      -- Summing all owner fibers recovers the original convex coefficients.
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
      · -- Zero-mass fibers use the fixed local witness.
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
          -- The owner fiber gives a convex combination supported inside `V i`.
          exact Finset.centerMass_mem_convexHull (fiber i)
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
        -- Zero-mass fibers contribute the zero vector.
        simpa [coeff, v, hci, hsum_smul_zero]
      · have hsum_ne : ∑ y ∈ fiber i, w y ≠ 0 := by
          simpa [coeff] using hci
        -- Positive-mass fibers are rewritten through the center-of-mass identity.
        simpa [coeff, v, hci] using
          smul_centerMass_eq_sum_smul (fiber i) w id hsum_ne
    refine ⟨coeff, v, hcoeff_nonneg, hcoeff_sum, hv_mem, ?_⟩
    -- Summing the regrouped fiber terms recovers the original witness for `q`.
    calc
      q = ∑ y ∈ S, w y • y := hw_q.symm
      _ = ∑ i : Fin k, ∑ y ∈ fiber i, w y • y := by
        symm
        simpa [fiber] using owner_partitioned_sum_eq S owner (fun y ↦ w y • y)
      _ = ∑ i : Fin k, coeff i • v i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hfiber_term i).symm

/-- Helper for Theorem 4.42: a conic combination from the global ray biunion can be regrouped
into one local cone-hull vector for each block. -/
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
      -- Each filtered sum is a nonnegative combination of rays from the `i`-th block.
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
    -- Summing all owner fibers reconstructs the original conic witness.
    calc
      c = coeff.sum (fun y a ↦ a • y) := hcoeff_sum.symm
      _ = Finset.sum coeff.support (fun y ↦ coeff y • y) := by
        simp [Finsupp.sum]
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

/-- Helper for Theorem 4.42: the source epsilon-approximant coefficients stay nonnegative and
their total mass remains `1` after adding the uniform correction blocks. -/
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
    -- On the positive-support set we subtract at most the available mass; off it we use `0`.
    intro i
    by_cases hi : i ∈ I
    · simp [α, hi, sub_nonneg, hsmall i hi]
    · simp [α, hi]
  have hcoeff_zero_off : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ 0 < coeff i), coeff i = 0 := by
    -- Outside the positive-support set, nonnegativity forces the original coefficient to vanish.
    intro i hi
    have hnotpos : ¬ 0 < coeff i := (Finset.mem_filter.1 hi).2
    exact le_antisymm (le_of_not_gt hnotpos) (hcoeff_nonneg i)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin k ↦ 0 < coeff i) coeff
  have hzero := Finset.sum_eq_zero hcoeff_zero_off
  have hsum_I : Finset.sum I coeff = 1 := by
    -- Splitting the sum along positive and nonpositive coefficients leaves only the positive part.
    rw [hI]
    linarith [hsplit, hzero, hcoeff_sum]
  have hIcard_ne : (I.card : ℝ) ≠ 0 := by
    -- The denominator `|I|` is nonzero because the positive-support set is nonempty.
    exact_mod_cast Finset.card_ne_zero.mpr hI_nonempty
  have hsum_alpha : ∑ i, α i = 1 - (k : ℝ) * η := by
    -- The new coefficients remove exactly `k * η` total mass from the positive-support block.
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

/-- Helper for Theorem 4.42: the textbook epsilon-approximant is a convex combination of source
points from `⋃ i, P i`. -/
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
        -- The ray correction stays in the same local cone because `η > 0`.
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
  -- Package the two source families into one finite convex combination.
  refine mem_convexHull_of_exists_fintype w z hw_nonneg ?_ hz_mem ?_
  · simpa [w, Fintype.sum_sum_type] using hα_sum
  · simpa [w, z, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 4.42: the positive-support set of a coefficient family has a uniform
positive lower bound. -/
lemma exists_pos_coeff_lower_bound_on_positive_support
    {coeff : Fin k → ℝ}
    (I : Finset (Fin k))
    (hI : I = Finset.univ.filter (fun i ↦ 0 < coeff i))
    (hI_nonempty : I.Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ I, δ ≤ coeff i := by
  let values : Finset ℝ := I.image coeff
  have hvalues_nonempty : values.Nonempty := hI_nonempty.image coeff
  refine ⟨values.min' hvalues_nonempty, ?_, ?_⟩
  · -- Every element of the positive-support image is positive, so the finite minimum is positive.
    rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨i, hiI, hmin⟩
    have hi_filter : i ∈ Finset.univ.filter (fun j : Fin k ↦ 0 < coeff j) := by
      simpa [hI] using hiI
    have hi_pos : 0 < coeff i := (Finset.mem_filter.1 hi_filter).2
    rwa [← hmin]
  · -- Every positive-support coefficient appears in the image, so it is bounded below by the minimum.
    intro i hi
    exact Finset.min'_le values _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- Helper for Theorem 4.42: the epsilon-approximant differs from the target point by one scalar
multiple of the fixed drift vector. -/
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
    -- Outside the positive-support set, nonnegativity forces the coefficient to vanish.
    intro i hi
    have hnotpos : ¬ 0 < coeff i := (Finset.mem_filter.1 hi).2
    exact le_antisymm (le_of_not_gt hnotpos) (hcoeff_nonneg i)
  have hcoeff_sum_on_I :
      ∑ i : Fin k, coeff i • v i = Finset.sum I (fun i ↦ coeff i • v i) := by
    -- Off the positive-support set, the coefficient terms vanish.
    have hsplit := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i : Fin k ↦ 0 < coeff i) (fun i ↦ coeff i • v i)
    have hzero :
        Finset.sum (Finset.univ.filter (fun i ↦ ¬ 0 < coeff i)) (fun i ↦ coeff i • v i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hcoeff_zero_off i hi]
    rw [hzero, add_zero] at hsplit
    simpa [hI] using hsplit.symm
  have halpha_sum :
      ∑ i : Fin k, α i • v i = Finset.sum I (fun i ↦ (coeff i - κ * η) • v i) := by
    -- Off the positive-support set the approximant uses coefficient `0`.
    simp [α]
  have hscaled_sum :
      ∑ i : Fin k, η • (v i + (1 / η) • r i) = η • ∑ i : Fin k, v i + ∑ i : Fin k, r i := by
    -- Distribute the common scalar `η` and cancel the reciprocal factor on the ray term.
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
    -- Factor the fixed drift as one scalar multiple of a single vector sum.
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
    -- First cancel the ray sum and then isolate the coefficient correction on the positive support.
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
      _ = η • ((∑ i : Fin k, v i) - Finset.sum I (fun i ↦ κ • v i)) := by
            rw [hkappa_sum, smul_sub]
      _ = η • d := by
            rfl
  simpa [α, d, κ] using hmain

/-- Helper for Theorem 4.42: the source-facing finite generated cone agrees with the canonical
matrix-column cone on the same rays. -/
lemma finitely_generated_cone_eq_matrix_cone
    {n q : ℕ} (rays : Fin q → Fin n → ℝ) :
    finitely_generated_cone rays =
      (((matrix_cone (fun i j ↦ rays j i)) : PointedCone ℝ (Fin n → ℝ)) :
        Set (Fin n → ℝ)) := by
  -- The source-facing cone is definitionally the matrix-column cone on the same finite family.
  rfl

/-- Helper for Theorem 4.42: membership in `finitely_generated_cone rays` is exactly a
nonnegative finite linear combination of the rays. -/
lemma mem_finitely_generated_cone_iff
    {n q : ℕ} {rays : Fin q → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ finitely_generated_cone rays ↔
      ∃ μ : Fin q → ℝ, (∀ i : Fin q, 0 ≤ μ i) ∧ x = ∑ i, μ i • rays i := by
  -- Rewrite to the canonical matrix-column owner and then unpack its coefficient witness.
  rw [finitely_generated_cone_eq_matrix_cone rays]
  constructor
  · intro hx
    rcases mem_matrix_cone_iff.mp hx with ⟨μ, hμ_nonneg, hmul⟩
    refine ⟨μ, hμ_nonneg, ?_⟩
    ext i
    have hcoord := congrArg (fun v ↦ v i) hmul
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm] using hcoord.symm
  · rintro ⟨μ, hμ_nonneg, hsum⟩
    refine mem_matrix_cone_iff.mpr ⟨μ, hμ_nonneg, ?_⟩
    ext i
    rw [hsum]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm]

/-- Helper for Theorem 4.42: adjoining one extra generator splits membership into one
nonnegative multiple of the new ray plus a point in the old cone. -/
lemma mem_matrix_cone_cons_iff
    {n q : ℕ} (r : Fin n → ℝ) (rays : Fin q → Fin n → ℝ) {x : Fin n → ℝ} :
    x ∈ (((matrix_cone
      (fun i j ↦ ((Fin.cons r rays : Fin (q + 1) → Fin n → ℝ) j) i)) :
        PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
      ∃ a : ℝ, 0 ≤ a ∧
        ∃ y : Fin n → ℝ,
          y ∈ (((matrix_cone (fun i j ↦ rays j i)) : PointedCone ℝ (Fin n → ℝ)) :
            Set (Fin n → ℝ)) ∧
            x = a • r + y := by
  -- Split the head coefficient from the tail coefficients before the closure argument.
  rw [← finitely_generated_cone_eq_matrix_cone (Fin.cons r rays)]
  rw [mem_finitely_generated_cone_iff]
  constructor
  · rintro ⟨μ, hμ_nonneg, hsum⟩
    refine ⟨μ 0, hμ_nonneg 0, ∑ i : Fin q, μ i.succ • rays i, ?_, ?_⟩
    · -- The tail coefficients still witness membership in the old cone.
      rw [← finitely_generated_cone_eq_matrix_cone rays]
      refine mem_finitely_generated_cone_iff.mpr ⟨fun i ↦ μ i.succ, ?_, rfl⟩
      intro i
      exact hμ_nonneg i.succ
    · -- Splitting the finite sum isolates the new generator.
      calc
        x = ∑ j : Fin (q + 1), μ j • Fin.cons r rays j := hsum
        _ = μ 0 • r + ∑ i : Fin q, μ i.succ • rays i := by
              rw [Fin.sum_univ_succ]
              simp
  · rintro ⟨a, ha, y, hy, rfl⟩
    rw [← finitely_generated_cone_eq_matrix_cone rays] at hy
    rcases mem_finitely_generated_cone_iff.mp hy with ⟨μ, hμ_nonneg, rfl⟩
    refine ⟨Fin.cons a μ, ?_, ?_⟩
    · -- Reassembling the head coefficient preserves nonnegativity.
      intro j
      cases j using Fin.cases with
      | zero =>
          simpa using ha
      | succ j =>
          simpa using hμ_nonneg j
    · -- The reassembled coefficients recover the sum in the larger cone.
      rw [Fin.sum_univ_succ]
      simp

/-- Helper for Theorem 4.42: the cone generated by a single ray is closed because it is the image
of `Set.Ici 0` under scalar multiplication by that ray. -/
lemma isClosed_matrix_cone_singleton
    {n : ℕ} (rays : Fin 1 → Fin n → ℝ) :
    IsClosed
      ((((matrix_cone (fun i j ↦ rays j i)) : PointedCone ℝ (Fin n → ℝ)) :
        Set (Fin n → ℝ))) := by
  let r : Fin n → ℝ := rays 0
  have hrays : rays = Fin.cons r Fin.elim0 := by
    ext j i
    fin_cases j
    rfl
  have himage :
      ((((matrix_cone (fun i j ↦ rays j i)) : PointedCone ℝ (Fin n → ℝ)) :
        Set (Fin n → ℝ))) =
        (fun a : ℝ ↦ a • r) '' Set.Ici 0 := by
    rw [hrays]
    ext x
    constructor
    · intro hx
      have hx' :
          x ∈ (((matrix_cone
            (fun i j ↦ ((Fin.cons r Fin.elim0 : Fin 1 → Fin n → ℝ) j) i)) :
              PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
        simpa using hx
      rcases mem_matrix_cone_iff.mp hx' with ⟨μ, hμ_nonneg, hsum⟩
      -- Read the unique coefficient as the scalar multiplying the unique ray.
      refine ⟨μ 0, hμ_nonneg 0, ?_⟩
      ext i
      have hcoord := congrArg (fun v ↦ v i) hsum
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm] using hcoord
    · rintro ⟨a, ha, rfl⟩
      -- The singleton coefficient family rebuilds the same nonnegative multiple.
      have hx' :
          a • r ∈ (((matrix_cone
            (fun i j ↦ ((Fin.cons r Fin.elim0 : Fin 1 → Fin n → ℝ) j) i)) :
              PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
        refine mem_matrix_cone_iff.mpr ⟨fun _ ↦ a, ?_, ?_⟩
        · intro j
          fin_cases j
          simpa using ha
        · ext i
          simp [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm]
      simpa using hx'
  -- Closedness transfers from the closed-map image of the closed ray parameter interval.
  rw [himage]
  exact (isClosedMap_smul_left r) _ isClosed_Ici
namespace Theorem442Local

abbrev matrix_polyhedral_cone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A 0

/-- Membership in `matrix_polyhedral_cone A` is exactly the homogeneous inequality system
`A *ᵥ x ≤ 0`. -/
theorem mem_matrix_polyhedral_cone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrix_polyhedral_cone A ↔ A *ᵥ x ≤ 0 := by
  rfl

/-- Helper for Theorem 3.11: membership in the cone generated by the rows of `A` is exactly a
nonnegative row combination of `A`. -/
lemma transpose_matrix_cone_mem_iff_vecMul
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {y : Fin n → ℝ} :
    y ∈ matrix_cone A.transpose ↔
      ∃ ν : Fin m → ℝ, (∀ i, 0 ≤ ν i) ∧ ν ᵥ* A = y := by
  constructor
  · intro hy
    -- Rewrite column-cone membership for `Aᵀ`, then identify `Aᵀ *ᵥ ν` with `ν ᵥ* A`.
    rcases mem_matrix_cone_iff.mp hy with ⟨ν, hν_nonneg, hνy⟩
    refine ⟨ν, hν_nonneg, ?_⟩
    simpa [Matrix.mulVec_transpose] using hνy
  · rintro ⟨ν, hν_nonneg, hνy⟩
    -- Convert the row-combination identity back to the standard column-cone witness for `Aᵀ`.
    refine mem_matrix_cone_iff.mpr ⟨ν, hν_nonneg, ?_⟩
    simpa [Matrix.mulVec_transpose] using hνy

/-- Helper for Theorem 3.11: each row of `A` lies in the cone generated by the rows of `A`. -/
lemma matrix_row_mem_transpose_matrix_cone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    (fun j : Fin n ↦ A i j) ∈ matrix_cone A.transpose := by
  -- Select the `i`-th row by the singleton coefficient vector.
  refine mem_matrix_cone_iff.mpr ?_
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · intro t
    by_cases ht : t = i
    · subst ht
      simp [Pi.single]
    · simp [Pi.single, ht]
  · ext j
    -- `Aᵀ *ᵥ eᵢ` is the `i`-th row of `A`.
    exact congrFun (Matrix.mulVec_single_one A.transpose i) j

/-- Helper for Theorem 3.11: once the dual row cone of `A` has a homogeneous matrix presentation
`B *ᵥ y ≤ 0`, every nonnegative combination of the rows of `B` satisfies `A *ᵥ x ≤ 0`. -/
lemma matrix_cone_transpose_subset_matrix_polyhedral_of_dual_presentation
    {m n k : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {B : Matrix (Fin k) (Fin n) ℝ}
    (hdual : (matrix_cone A.transpose : Set (Fin n → ℝ)) = matrix_polyhedral_cone B) :
    (matrix_cone B.transpose : Set (Fin n → ℝ)) ⊆ matrix_polyhedral_cone A := by
  intro x hx
  rcases transpose_matrix_cone_mem_iff_vecMul.mp hx with ⟨μ, hμ_nonneg, rfl⟩
  refine (mem_matrix_polyhedral_cone A _).2 ?_
  have hAB_nonpos : ∀ i : Fin m, ∀ j : Fin k, (A * B.transpose) i j ≤ 0 := by
    intro i j
    -- The `i`-th row of `A` belongs to the dual row cone, so it satisfies all inequalities of `B`.
    have hrow_mem : (fun t : Fin n ↦ A i t) ∈ matrix_cone A.transpose :=
      matrix_row_mem_transpose_matrix_cone A i
    have hrow_poly : (fun t : Fin n ↦ A i t) ∈ matrix_polyhedral_cone B := by
      rw [← hdual]
      exact hrow_mem
    have hrow_nonpos : B *ᵥ (fun t : Fin n ↦ A i t) ≤ 0 :=
      (mem_matrix_polyhedral_cone B _).mp hrow_poly
    -- The matrix entry `(A * Bᵀ) i j` is the `j`-th inequality evaluated on the `i`-th row.
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using hrow_nonpos j
  intro i
  -- Compose the matrix-vector products and sum nonpositive entries against nonnegative weights.
  rw [Matrix.mulVec_vecMul]
  change ∑ j : Fin k, (A * B.transpose) i j * μ j ≤ 0
  refine Finset.sum_nonpos ?_
  intro j hj
  exact mul_nonpos_of_nonpos_of_nonneg (hAB_nonpos i j) (hμ_nonneg j)

/-- Helper for Theorem 3.11: if the dual row cone of `A` is presented by `B *ᵥ y ≤ 0`, then every
point satisfying `A *ᵥ x ≤ 0` is a nonnegative combination of the rows of `B`. -/
lemma matrix_polyhedral_cone_subset_matrix_cone_transpose_of_dual_presentation
    {m n k : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {B : Matrix (Fin k) (Fin n) ℝ}
    (hdual : (matrix_cone A.transpose : Set (Fin n → ℝ)) = matrix_polyhedral_cone B) :
    matrix_polyhedral_cone A ⊆ (matrix_cone B.transpose : Set (Fin n → ℝ)) := by
  intro x hx
  by_contra hx_not_mem
  -- If `x` is outside the cone generated by the rows of `B`, Theorem 3.5 gives a separator.
  have h_infeasible : ¬ ∃ μ : Fin k → ℝ, B.transpose *ᵥ μ = x ∧ 0 ≤ μ := by
    intro hμ
    rcases hμ with ⟨μ, hμx, hμ_nonneg⟩
    apply hx_not_mem
    refine mem_matrix_cone_iff.mpr ⟨μ, hμ_nonneg, hμx⟩
  have h_separating :
      ∃ y : Fin n → ℝ, y ᵥ* B.transpose ≤ 0 ∧ ¬ y ⬝ᵥ x ≤ 0 := by
    classical
    have h_farkas :
        (∃ μ : Fin k → ℝ, B.transpose *ᵥ μ = x ∧ 0 ≤ μ) ↔
          ∀ y : Fin n → ℝ, y ᵥ* B.transpose ≤ 0 → y ⬝ᵥ x ≤ 0 := by
      simpa [and_left_comm, and_assoc] using
        feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers B.transpose x
    have h_not_all : ¬ ∀ y : Fin n → ℝ, y ᵥ* B.transpose ≤ 0 → y ⬝ᵥ x ≤ 0 := by
      intro h_all
      exact h_infeasible (h_farkas.mpr h_all)
    rw [not_forall] at h_not_all
    rcases h_not_all with ⟨y, hy⟩
    exact ⟨y, by simpa [Classical.not_imp] using hy⟩
  rcases h_separating with ⟨y, hyB_nonpos, hyx_pos⟩
  have hy_poly : y ∈ matrix_polyhedral_cone B := by
    -- Rewrite the row-multiplier condition as the homogeneous inequalities defining the dual cone.
    refine (mem_matrix_polyhedral_cone B y).2 ?_
    simpa [Matrix.vecMul_transpose] using hyB_nonpos
  have hy_cone : y ∈ matrix_cone A.transpose := by
    have hy_poly' : y ∈ (matrix_polyhedral_cone B : Set (Fin n → ℝ)) := hy_poly
    rw [← hdual] at hy_poly'
    exact hy_poly'
  rcases transpose_matrix_cone_mem_iff_vecMul.mp hy_cone with ⟨ν, hν_nonneg, hνA⟩
  have hyx_nonpos : y ⬝ᵥ x ≤ 0 := by
    -- Express `y` as a nonnegative row combination of `A` and pair it with `A *ᵥ x ≤ 0`.
    have hxA_nonpos : A *ᵥ x ≤ 0 := (mem_matrix_polyhedral_cone A x).mp hx
    calc
      y ⬝ᵥ x = ν ⬝ᵥ (A *ᵥ x) := by rw [← hνA, Matrix.dotProduct_mulVec]
      _ ≤ 0 := by
        simpa [dotProduct] using
          Finset.sum_nonpos fun i _ ↦
            mul_nonpos_of_nonneg_of_nonpos (hν_nonneg i) (hxA_nonpos i)
  exact hyx_pos hyx_nonpos

/-- Helper for Theorem 3.11: the sum-indexed block matrix for the lifted homogeneous system before
reindexing rows and columns back to `Fin`. -/
private def liftedConeMatrixBase
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin k)) (Fin n ⊕ Fin k) ℝ :=
  Matrix.fromRows
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) ℝ) (-R))
    (Matrix.fromRows
      (Matrix.fromCols (-(1 : Matrix (Fin n) (Fin n) ℝ)) R)
      (Matrix.fromCols (0 : Matrix (Fin k) (Fin n) ℝ) (-(1 : Matrix (Fin k) (Fin k) ℝ))))

/-- Helper for Theorem 3.11: the canonical row equivalence that identifies the three row blocks of
the lifted homogeneous system with a single `Fin` index family. -/
private abbrev liftedConeMatrixRowEquiv
    {n k : ℕ} : Fin (n + (n + k)) ≃ Fin n ⊕ (Fin n ⊕ Fin k) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)

/-- Helper for Theorem 3.11: the canonical column equivalence that splits the lifted variables into
the `x`-coordinates and the trailing coefficient coordinates. -/
private abbrev liftedConeMatrixColEquiv
    {n k : ℕ} : Fin (n + k) ≃ Fin n ⊕ Fin k :=
  finSumFinEquiv.symm

/-- Helper for Theorem 3.11: the homogeneous lifted system whose rows encode `x - Rμ ≤ 0`,
`-x + Rμ ≤ 0`, and `-μ ≤ 0`, with the coefficient variables placed in the trailing coordinates. -/
def liftedConeMatrix
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin (n + (n + k))) (Fin (n + k)) ℝ :=
  (liftedConeMatrixBase R).submatrix liftedConeMatrixRowEquiv liftedConeMatrixColEquiv

/-- Helper for Theorem 3.11: the first block of the lifted system is exactly `x - R *ᵥ μ`. -/
lemma liftedConeMatrix_first_block
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (μ : Fin k → ℝ) (i : Fin n) :
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.castAdd (n + k) i) =
      x i - (R *ᵥ μ) i := by
  -- Reindex to the block matrix, then read off the first block.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (liftedConeMatrixBase R) (Fin.append x μ)
      liftedConeMatrixRowEquiv liftedConeMatrixColEquiv
  have happend : Fin.append x μ ∘ liftedConeMatrixColEquiv.symm = Sum.elim x μ := by
    simpa [liftedConeMatrixColEquiv] using
      (Fin.append_comp_sumElim :
        Fin.append x μ ∘ Sum.elim (Fin.castAdd k) (Fin.natAdd n) = Sum.elim x μ)
  have hrow :
      (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.castAdd (n + k) i) =
        (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inl i) := by
    have hrow' := congrFun hmul (Fin.castAdd (n + k) i)
    rw [happend] at hrow'
    simpa [liftedConeMatrix, liftedConeMatrixRowEquiv, finSumFinEquiv_symm_apply_castAdd] using
      hrow'
  calc
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.castAdd (n + k) i)
        = (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inl i) := hrow
    _ = x i - (R *ᵥ μ) i := by
      simp [liftedConeMatrixBase, Matrix.neg_mulVec, sub_eq_add_neg]

/-- Helper for Theorem 3.11: the second block of the lifted system is exactly `-x + R *ᵥ μ`. -/
lemma liftedConeMatrix_second_block
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (μ : Fin k → ℝ) (i : Fin n) :
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.castAdd k i)) =
      -x i + (R *ᵥ μ) i := by
  -- Reindex to the block matrix, then read off the second block.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (liftedConeMatrixBase R) (Fin.append x μ)
      liftedConeMatrixRowEquiv liftedConeMatrixColEquiv
  have happend : Fin.append x μ ∘ liftedConeMatrixColEquiv.symm = Sum.elim x μ := by
    simpa [liftedConeMatrixColEquiv] using
      (Fin.append_comp_sumElim :
        Fin.append x μ ∘ Sum.elim (Fin.castAdd k) (Fin.natAdd n) = Sum.elim x μ)
  have hrow :
      (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.castAdd k i)) =
        (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inr (Sum.inl i)) := by
    have hrow' := congrFun hmul (Fin.natAdd n (Fin.castAdd k i))
    rw [happend] at hrow'
    simpa [liftedConeMatrix, liftedConeMatrixRowEquiv, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd] using hrow'
  calc
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.castAdd k i))
        = (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inr (Sum.inl i)) := hrow
    _ = -x i + (R *ᵥ μ) i := by
      have hblock :=
        Matrix.fromBlocks_mulVec (-(1 : Matrix (Fin n) (Fin n) ℝ)) R
          (0 : Matrix (Fin k) (Fin n) ℝ) (-(1 : Matrix (Fin k) (Fin k) ℝ)) (Sum.elim x μ)
      simpa [Matrix.neg_mulVec] using congrFun hblock (Sum.inl i)

/-- Helper for Theorem 3.11: the final block of the lifted system is exactly `-μ ≤ 0`. -/
lemma liftedConeMatrix_third_block
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (μ : Fin k → ℝ) (l : Fin k) :
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.natAdd n l)) =
      -μ l := by
  -- Reindex to the block matrix, then read off the nonnegativity block.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (liftedConeMatrixBase R) (Fin.append x μ)
      liftedConeMatrixRowEquiv liftedConeMatrixColEquiv
  have happend : Fin.append x μ ∘ liftedConeMatrixColEquiv.symm = Sum.elim x μ := by
    simpa [liftedConeMatrixColEquiv] using
      (Fin.append_comp_sumElim :
        Fin.append x μ ∘ Sum.elim (Fin.castAdd k) (Fin.natAdd n) = Sum.elim x μ)
  have hrow :
      (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.natAdd n l)) =
        (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inr (Sum.inr l)) := by
    have hrow' := congrFun hmul (Fin.natAdd n (Fin.natAdd n l))
    rw [happend] at hrow'
    simpa [liftedConeMatrix, liftedConeMatrixRowEquiv, finSumFinEquiv_symm_apply_natAdd] using
      hrow'
  calc
    (liftedConeMatrix R *ᵥ Fin.append x μ) (Fin.natAdd n (Fin.natAdd n l))
        = (liftedConeMatrixBase R *ᵥ Sum.elim x μ) (Sum.inr (Sum.inr l)) := hrow
    _ = -μ l := by
      have hblock :=
        Matrix.fromBlocks_mulVec (-(1 : Matrix (Fin n) (Fin n) ℝ)) R
          (0 : Matrix (Fin k) (Fin n) ℝ) (-(1 : Matrix (Fin k) (Fin k) ℝ)) (Sum.elim x μ)
      simpa [Matrix.neg_mulVec] using congrFun hblock (Sum.inr l)

/-- Helper for Theorem 3.11: the lifted homogeneous system is equivalent to the textbook cone
membership data `R *ᵥ μ = x` together with `μ ≥ 0`. -/
lemma lifted_matrix_cone_system_iff
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) (μ : Fin k → ℝ) :
    liftedConeMatrix R *ᵥ Fin.append x μ ≤ 0 ↔ R *ᵥ μ = x ∧ 0 ≤ μ := by
  constructor
  · intro hLifted
    refine ⟨?_, ?_⟩
    · -- The two `x ± Rμ` row blocks force equality coordinatewise.
      ext i
      have h₁ : x i - (R *ᵥ μ) i ≤ 0 := by
        simpa [liftedConeMatrix_first_block] using hLifted (Fin.castAdd (n + k) i)
      have h₂ : -x i + (R *ᵥ μ) i ≤ 0 := by
        simpa [liftedConeMatrix_second_block] using hLifted (Fin.natAdd n (Fin.castAdd k i))
      linarith
    · -- The trailing block is precisely the nonnegativity condition on `μ`.
      intro l
      have hμ : -μ l ≤ 0 := by
        simpa [liftedConeMatrix_third_block] using hLifted (Fin.natAdd n (Fin.natAdd n l))
      exact neg_nonpos.mp hμ
  · rintro ⟨hEq, hμ_nonneg⟩
    intro s
    -- Check the three row blocks separately against the equality `R *ᵥ μ = x`.
    cases s using Fin.addCases with
    | left i =>
        have hi : x i - (R *ᵥ μ) i = 0 := by
          simp [hEq]
        simp [liftedConeMatrix_first_block, hi]
    | right s =>
        cases s using Fin.addCases with
        | left i =>
            have hi : -x i + (R *ᵥ μ) i = 0 := by
              simp [hEq]
            simp [liftedConeMatrix_second_block, hi]
        | right l =>
            have hμ : -μ l ≤ 0 := by
              exact neg_nonpos.mpr (hμ_nonneg l)
            simpa [liftedConeMatrix_third_block] using hμ

/-- Helper for Theorem 4.42: the local stage-data package for iterated Fourier-Motzkin
elimination. -/
private structure FourierStageMatrixData (n : ℕ) where
  Row : Type
  [fintype_Row : Fintype Row]
  matrix : Matrix Row (Fin n) ℝ

attribute [instance] FourierStageMatrixData.fintype_Row

/-- Helper for Theorem 4.42: stage `0` keeps the original matrix and row index family. -/
private def initialFourierStageMatrixData {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    FourierStageMatrixData n where
  Row := Fin m
  matrix := A

/-- Helper for Theorem 4.42: one elimination step packages the explicit Fourier-step matrix. -/
private noncomputable def fourierStepMatrixData {n : ℕ}
    (S : FourierStageMatrixData (n + 1)) : FourierStageMatrixData n where
  Row := FourierStepIndex S.matrix
  matrix := fourier_step_matrix S.matrix

/-- Helper for Theorem 4.42: advancing the local stage package either freezes dimension `0` or
applies one Fourier-Motzkin elimination step. -/
private noncomputable def nextFourierStageMatrixData :
    (Σ n : ℕ, FourierStageMatrixData n) → Σ n : ℕ, FourierStageMatrixData n
  | ⟨0, S⟩ => ⟨0, S⟩
  | ⟨n + 1, S⟩ => ⟨n, fourierStepMatrixData S⟩

/-- Helper for Theorem 4.42: iterating `nextFourierStageMatrixData` gives the entire local
Fourier-stage owner surface needed below. -/
private noncomputable def fourier_stage_matrix_data {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℕ → Σ r : ℕ, FourierStageMatrixData r
  | 0 => ⟨n, initialFourierStageMatrixData A⟩
  | k + 1 => nextFourierStageMatrixData (fourier_stage_matrix_data A k)

/-- Helper for Theorem 4.42: the ambient dimension of the `k`-th local Fourier stage. -/
noncomputable abbrev fourier_stage_dim {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℕ :=
  (fourier_stage_matrix_data A k).1

/-- Helper for Theorem 4.42: the row-index family of the `k`-th local Fourier stage. -/
noncomputable abbrev fourier_stage_row {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Type :=
  (fourier_stage_matrix_data A k).2.Row

/-- Helper for Theorem 4.42: the local Fourier stage row type is finite. -/
noncomputable instance fourier_stage_row_fintype {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Fintype (fourier_stage_row A k) :=
  (fourier_stage_matrix_data A k).2.fintype_Row

/-- Helper for Theorem 4.42: the coefficient matrix of the `k`-th local Fourier stage. -/
noncomputable abbrev fourier_stage_matrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Matrix (fourier_stage_row A k) (Fin (fourier_stage_dim A k)) ℝ :=
  (fourier_stage_matrix_data A k).2.matrix

/-- Helper for Theorem 4.42: the row count of the `k`-th local Fourier stage. -/
noncomputable abbrev fourier_stage_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℕ :=
  Fintype.card (fourier_stage_row A k)

/-- Helper for Theorem 4.42: one step of right-hand-side transport along the local stage-data
package. -/
private noncomputable def nextFourierStageRhs
    (S : Σ r : ℕ, FourierStageMatrixData r) (rhs : S.2.Row → ℝ) :
    (nextFourierStageMatrixData S).2.Row → ℝ :=
  match S with
  | ⟨0, _⟩ => rhs
  | ⟨_ + 1, T⟩ => fourier_step_rhs T.matrix rhs

/-- Helper for Theorem 4.42: the iterated local Fourier-stage right-hand sides. -/
private noncomputable def fourier_stage_rhs_data {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (k : ℕ) → (fourier_stage_matrix_data A k).2.Row → ℝ
  | 0 => b
  | k + 1 => nextFourierStageRhs (fourier_stage_matrix_data A k) (fourier_stage_rhs_data A b k)

/-- Helper for Theorem 4.42: the public right-hand side at the `k`-th local Fourier stage. -/
noncomputable abbrev fourier_stage_rhs {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : ℕ) :
    fourier_stage_row A k → ℝ :=
  fourier_stage_rhs_data A b k

/-- Helper for Theorem 4.42: one local stage advance lowers the ambient dimension by one unless
it is already `0`. -/
private theorem nextFourierStageMatrixDataDim
    (S : Σ n : ℕ, FourierStageMatrixData n) :
    (nextFourierStageMatrixData S).1 = S.1 - 1 := by
  -- Unfold the local stage-data package once and inspect the ambient dimension.
  rcases S with ⟨n, S⟩
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

/-- Helper for Theorem 4.42: advancing one local Fourier stage lowers the ambient dimension by
one. -/
theorem fourier_stage_dim_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    fourier_stage_dim A (k + 1) = fourier_stage_dim A k - 1 := by
  -- The iterated stage-data package changes exactly by `nextFourierStageMatrixData`.
  exact (nextFourierStageMatrixDataDim (fourier_stage_matrix_data A k)).trans <|
    by simp [fourier_stage_dim]

/-- Helper for Theorem 4.42: for an explicit successor-dimensional stage package, the next-stage
feasibility proposition is definitionally the ordinary one-step Fourier-Motzkin feasibility
condition. -/
private theorem nextFourierStageFeasibilityIff
    {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData d)
    (rhs : S.2.Row → ℝ)
    (h : S.1 = r + 1)
    (hNext : (nextFourierStageMatrixData S).1 = r)
    (x : Fin r → ℝ) :
    let Ak : Matrix S.2.Row (Fin (r + 1)) ℝ :=
      cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) ℝ) h) S.2.matrix
    let xNext : Fin ((nextFourierStageMatrixData S).1) → ℝ :=
      cast (congrArg (fun d ↦ Fin d → ℝ) hNext.symm) x
    (nextFourierStageMatrixData S).2.matrix *ᵥ xNext ≤ nextFourierStageRhs S rhs ↔
      fourier_step_matrix Ak *ᵥ x ≤ fourier_step_rhs Ak rhs := by
  -- Unfold the sigma package once so the successor stage becomes the literal one-step system.
  cases S with
  | mk dim T =>
      dsimp at h hNext ⊢
      cases dim with
      | zero =>
          cases h
      | succ dim =>
          cases h
          cases hNext
          rfl

/-- Helper for Theorem 4.42: if the current local stage still has one last coordinate to
eliminate, then successor-stage feasibility is exactly the ordinary one-step Fourier-Motzkin
condition after the canonical column cast. -/
theorem fourier_stage_succ_feasibility_iff
    {m n r k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h : fourier_stage_dim A k = r + 1)
    (hNext : fourier_stage_dim A (k + 1) = r)
    (x : Fin r → ℝ) :
    let Ak : Matrix (fourier_stage_row A k) (Fin (r + 1)) ℝ :=
      cast
        (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) ℝ) h)
        (fourier_stage_matrix A k)
    let xNext : Fin (fourier_stage_dim A (k + 1)) → ℝ :=
      cast (congrArg (fun d ↦ Fin d → ℝ) hNext.symm) x
    fourier_stage_matrix A (k + 1) *ᵥ xNext ≤ fourier_stage_rhs A b (k + 1) ↔
      fourier_step_matrix Ak *ᵥ x ≤ fourier_step_rhs Ak (fourier_stage_rhs A b k) := by
  let S : Σ d : ℕ, FourierStageMatrixData d := fourier_stage_matrix_data A k
  have hS : S.1 = r + 1 := h
  have hNextS : (nextFourierStageMatrixData S).1 = r := by
    simpa [S, fourier_stage_dim, fourier_stage_matrix_data] using hNext
  -- Instantiate the explicit stage-data lemma with the owner-stage sigma package at step `k`.
  simpa [S, fourier_stage_dim, fourier_stage_matrix, fourier_stage_rhs, fourier_stage_matrix_data,
    fourier_stage_rhs_data]
    using nextFourierStageFeasibilityIff S (fourier_stage_rhs A b k) hS hNextS x

/-- Helper for Theorem 4.42: after `k` eliminations, the local Fourier-stage ambient dimension is
the original one minus `k`. -/
theorem fourier_stage_dim_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    fourier_stage_dim A k = n - k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      -- Combine the one-step dimension drop with the induction hypothesis.
      calc
        fourier_stage_dim A (k + 1) = fourier_stage_dim A k - 1 := fourier_stage_dim_succ A k
        _ = (n - k) - 1 := by rw [ih]
        _ = n - (k + 1) := by omega

/-- Helper for Theorem 4.42: transporting a fixed-column matrix across a dimension equality is
equivalent to transporting the test vector back across the inverse equality. -/
lemma cast_matrix_feasibility_iff
    {ι : Type*}
    {p q : ℕ}
    (h : p = q)
    (A : Matrix ι (Fin p) ℝ)
    (b : ι → ℝ)
    (x : Fin q → ℝ) :
    cast (congrArg (fun t ↦ Matrix ι (Fin t) ℝ) h) A *ᵥ x ≤ b ↔
      A *ᵥ cast (congrArg (fun t ↦ Fin t → ℝ) h.symm) x ≤ b := by
  -- Both feasibility propositions are definitionally identical after eliminating the cast.
  cases h
  rfl

/-- Helper for Theorem 4.42: a tuple is recovered by appending its last coordinate to its tail. -/
lemma fin_snoc_castSucc_last_eq_self
    {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    Fin.snoc (fun i : Fin n ↦ x i.castSucc) (x (Fin.last n)) = x := by
  -- Check the last coordinate and the cast-succ coordinates separately.
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

/-- Helper for Theorem 3.11: after `t` Fourier eliminations on the lifted homogeneous system,
exactly the `n` visible coordinates and the remaining `k - t` coefficient coordinates survive. -/
lemma lifted_fourier_stage_dim_eq_tail
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) (t : ℕ) (ht : t ≤ k) :
    fourier_stage_dim (liftedConeMatrix R) t = n + (k - t) := by
  -- The lifted system starts with `n + k` variables, and each elimination step removes one of the
  -- trailing coefficient coordinates.
  calc
    fourier_stage_dim (liftedConeMatrix R) t = (n + k) - t := by
      simpa using fourier_stage_dim_eq (liftedConeMatrix R) t
    _ = n + (k - t) := by
      omega

/-- Helper for Theorem 3.11: if fewer than `k` coefficient coordinates have been eliminated, then
the current lifted stage still has one trailing coefficient that can be removed next. -/
lemma lifted_fourier_stage_dim_tail_succ
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) {t : ℕ} (ht : t < k) :
    fourier_stage_dim (liftedConeMatrix R) t = (n + (k - (t + 1))) + 1 ∧
      fourier_stage_dim (liftedConeMatrix R) (t + 1) = n + (k - (t + 1)) := by
  constructor
  · -- Normalize the current stage into the successor shape required by one-step elimination.
    rw [lifted_fourier_stage_dim_eq_tail R t (Nat.le_of_lt ht)]
    omega
  · -- The next stage has exactly one fewer trailing coefficient coordinate.
    rw [lifted_fourier_stage_dim_eq_tail R (t + 1) (Nat.succ_le_of_lt ht)]

/-- Helper for Theorem 3.11: after all `k` eliminations, only the visible `x`-coordinates remain
in the lifted system. -/
lemma lifted_fourier_stage_dim_terminal
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) :
    fourier_stage_dim (liftedConeMatrix R) k = n := by
  -- Specialize the general stage-dimension formula to the terminal elimination stage.
  simpa using lifted_fourier_stage_dim_eq_tail R k le_rfl

/-- Helper for Theorem 3.11: a point lies in the matrix cone exactly when it admits a feasible
extension to the lifted homogeneous system. -/
lemma mem_matrix_cone_iff_exists_lifted_feasible
    {n k : ℕ} {R : Matrix (Fin n) (Fin k) ℝ} {x : Fin n → ℝ} :
    x ∈ matrix_cone R ↔ ∃ μ : Fin k → ℝ, liftedConeMatrix R *ᵥ Fin.append x μ ≤ 0 := by
  constructor
  · intro hx
    -- Unpack matrix-cone membership into the textbook witness `μ ≥ 0` with `R *ᵥ μ = x`.
    rcases mem_matrix_cone_iff.mp hx with ⟨μ, hμ_nonneg, hμx⟩
    refine ⟨μ, ?_⟩
    exact (lifted_matrix_cone_system_iff R x μ).2 ⟨hμx, hμ_nonneg⟩
  · rintro ⟨μ, hμ⟩
    -- Conversely, any feasible lifted witness gives the nonnegative coefficient vector for `x`.
    rcases (lifted_matrix_cone_system_iff R x μ).1 hμ with ⟨hμx, hμ_nonneg⟩
    exact mem_matrix_cone_iff.mpr ⟨μ, hμ_nonneg, hμx⟩

/-- Helper for Theorem 3.11: when a Fourier stage still has one trailing coordinate left, the
successor-stage feasibility proposition is exactly the ordinary one-step Fourier-Motzkin
feasibility proposition after transporting the stage matrix and right-hand side across the public
`HEq` API. -/
lemma fourier_stage_succ_feasibility_prop_cast
    {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin m → ℝ)
    (k r : ℕ)
    (h : fourier_stage_dim M k = r + 1)
    (h' : fourier_stage_dim M (k + 1) = r)
    (x : Fin r → ℝ) :
    let xNext : Fin (fourier_stage_dim M (k + 1)) → ℝ :=
      cast (congrArg (fun t ↦ Fin t → ℝ) h'.symm) x
    let Mk : Matrix (fourier_stage_row M k) (Fin (r + 1)) ℝ :=
      cast
        (congrArg (fun t ↦ Matrix (fourier_stage_row M k) (Fin t) ℝ) h)
        (fourier_stage_matrix M k)
    fourier_stage_matrix M (k + 1) *ᵥ xNext ≤ fourier_stage_rhs M d (k + 1) ↔
      fourier_step_matrix Mk *ᵥ x ≤ fourier_step_rhs Mk (fourier_stage_rhs M d k) := by
  -- Route correction: the transport step now lives in the Section 3.1 owner file, so this local
  -- theorem is just the source-facing alias used by the lifted-system proof below.
  simpa using fourier_stage_succ_feasibility_iff M d h h' x

/-- Helper for Theorem 3.11: one Fourier elimination step on the lifted homogeneous system removes
exactly the last surviving coefficient coordinate. -/
lemma lifted_fourier_stage_succ_iff_exists_last
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℝ)
    {t : ℕ}
    (ht : t < k)
    (z : Fin (n + (k - (t + 1))) → ℝ) :
    fourier_stage_matrix (liftedConeMatrix R) (t + 1) *ᵥ
        cast
          (congrArg (fun q ↦ Fin q → ℝ) (lifted_fourier_stage_dim_tail_succ R ht).2.symm)
          z ≤
      fourier_stage_rhs (liftedConeMatrix R) 0 (t + 1) ↔
      ∃ last : ℝ,
        fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_tail_succ R ht).1.symm)
              (Fin.snoc z last) ≤
          fourier_stage_rhs (liftedConeMatrix R) 0 t := by
  rcases lifted_fourier_stage_dim_tail_succ R ht with ⟨hDim, hNext⟩
  let Mk : Matrix (fourier_stage_row (liftedConeMatrix R) t)
      (Fin ((n + (k - (t + 1))) + 1)) ℝ :=
    cast
      (congrArg
        (fun q ↦
          Matrix (fourier_stage_row (liftedConeMatrix R) t) (Fin q) ℝ)
        hDim)
      (fourier_stage_matrix (liftedConeMatrix R) t)
  -- First transport the stage-`t+1` feasibility proposition to the canonical one-step system.
  calc
    fourier_stage_matrix (liftedConeMatrix R) (t + 1) *ᵥ
        cast (congrArg (fun q ↦ Fin q → ℝ) hNext.symm) z ≤
          fourier_stage_rhs (liftedConeMatrix R) 0 (t + 1)
      ↔ fourier_step_matrix Mk *ᵥ z ≤
          fourier_step_rhs Mk (fourier_stage_rhs (liftedConeMatrix R) 0 t) := by
            simpa [Mk] using
              fourier_stage_succ_feasibility_prop_cast
                (liftedConeMatrix R)
                0
                t
                (n + (k - (t + 1)))
                hDim
                hNext
                z
    _ ↔ ∃ last : ℝ, Mk *ᵥ Fin.snoc z last ≤ fourier_stage_rhs (liftedConeMatrix R) 0 t := by
          simpa [satisfies_fourier_motzkin_step] using
            fourier_motzkin_step_iff_exists_last_coordinate
              Mk
              (fourier_stage_rhs (liftedConeMatrix R) 0 t)
              z
    _ ↔ ∃ last : ℝ,
          fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
              cast
                (congrArg (fun q ↦ Fin q → ℝ) hDim.symm)
                (Fin.snoc z last) ≤
            fourier_stage_rhs (liftedConeMatrix R) 0 t := by
          -- Undo the column transport on the stage-`t` matrix once the last coordinate is restored.
          refine exists_congr ?_
          intro last
          simpa [Mk] using
            cast_matrix_feasibility_iff
              hDim
              (fourier_stage_matrix (liftedConeMatrix R) t)
              (fourier_stage_rhs (liftedConeMatrix R) 0 t)
              (Fin.snoc z last)

/-- Helper for Theorem 3.11: casting a `Fin`-indexed function across a dimension equality is the
same as precomposing with the inverse `Fin.cast`. -/
lemma cast_fin_fn_eq_comp
    {α : Sort*} {p q : ℕ} (h : p = q) (x : Fin p → α) :
    cast (congrArg (fun t ↦ Fin t → α) h) x = x ∘ Fin.cast h.symm := by
  -- Eliminate the equality proof so that the cast becomes definitional.
  cases h
  rfl

/-- Helper for Theorem 3.11: when one more coefficient coordinate remains, its tail length is the
previous tail length minus one. -/
lemma lifted_tail_succ_eq
    {k t : ℕ} (ht : t < k) :
    k - t = (k - (t + 1)) + 1 := by
  -- This is the arithmetic normalization needed to decompose the stage-`t` witness by `Fin.snoc`.
  omega

/-- Helper for Theorem 3.11: rewriting the stage-`t` feasibility witness by decomposing the
surviving coefficient block as a casted `Fin.snoc`. -/
lemma append_snoc_stage_feasibility_iff
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℝ)
    {ht : t < k}
    (x : Fin n → ℝ)
    (z : Fin (k - (t + 1)) → ℝ)
    (last : ℝ) :
    fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_eq_tail R t (Nat.le_of_lt ht)).symm)
          (Fin.append x
            (cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq ht).symm)
              (Fin.snoc z last))) ≤
      fourier_stage_rhs (liftedConeMatrix R) 0 t
    ↔
    fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_tail_succ R ht).1.symm)
          (Fin.snoc (Fin.append x z) last) ≤
      fourier_stage_rhs (liftedConeMatrix R) 0 t := by
  have hvec :
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_eq_tail R t (Nat.le_of_lt ht)).symm)
          (Fin.append x
            (cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq ht).symm)
              (Fin.snoc z last))) =
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_tail_succ R ht).1.symm)
          (Fin.snoc (Fin.append x z) last) := by
    let hEqTail :=
      lifted_fourier_stage_dim_eq_tail R t (Nat.le_of_lt ht)
    let htail : k - t = (k - (t + 1)) + 1 :=
      lifted_tail_succ_eq ht
    let hsum : n + (k - t) = (n + (k - (t + 1))) + 1 := by
      simp [htail, Nat.add_assoc]
    let hDim := (lifted_fourier_stage_dim_tail_succ R ht).1
    have hDimEq : hDim = hEqTail.trans hsum := by
      -- The two public dimension equalities describe the same arithmetic normalization.
      apply Subsingleton.elim
    -- Normalize both casts to `Fin.cast` composition and then use `Fin.append_snoc`.
    calc
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x
            (cast
                (congrArg (fun q ↦ Fin q → ℝ) htail.symm)
                (Fin.snoc z last)))
          = (Fin.append x
              (cast
                (congrArg (fun q ↦ Fin q → ℝ) htail.symm)
                (Fin.snoc z last))) ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp hEqTail.symm]
      _ = (Fin.append x (Fin.snoc z last) ∘ Fin.cast (by rw [htail])) ∘ Fin.cast hEqTail := by
            simp [cast_fin_fn_eq_comp, htail, Fin.append_cast_right]
      _ = Fin.snoc (Fin.append x z) last ∘ Fin.cast (hEqTail.trans hsum) := by
            ext i
            simp [Function.comp, Fin.append_snoc, Fin.cast_cast]
      _ = Fin.snoc (Fin.append x z) last ∘ Fin.cast hDim := by
            rw [hDimEq]
      _ = cast
            (congrArg
              (fun q ↦ Fin q → ℝ)
              hDim.symm)
            (Fin.snoc (Fin.append x z) last) := by
            symm
            rw [cast_fin_fn_eq_comp hDim.symm]
  constructor
  · intro h
    -- Rewrite the casted witness into the `Fin.snoc` form expected by one elimination step.
    rw [hvec] at h
    exact h
  · intro h
    -- Undo the same cast normalization when rebuilding the stage-`t` witness.
    rw [hvec]
    exact h

/-- Helper for Theorem 3.11: the type `Fin (k - k)` is empty. -/
lemma fin_sub_self_false
    {k : ℕ} (i : Fin (k - k)) : False := by
  -- The defining inequality for `i` simplifies to a contradiction.
  simpa using i.2

/-- Helper for Theorem 3.11: after eliminating `t` coefficient coordinates from the lifted cone
system, the remaining feasibility problem keeps the visible vector `x` fixed in the first `n`
coordinates and remembers only the surviving coefficient coordinates. -/
lemma matrix_cone_iff_exists_stage_feasible
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ)
    (ht : t ≤ k) :
    x ∈ matrix_cone R ↔
      ∃ z : Fin (k - t) → ℝ,
        fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_eq_tail R t ht).symm)
              (Fin.append x z) ≤
          fourier_stage_rhs (liftedConeMatrix R) 0 t := by
  induction t generalizing x with
  | zero =>
      -- Stage `0` is exactly the original lifted feasibility formulation of cone membership.
      simpa using (@mem_matrix_cone_iff_exists_lifted_feasible n k R x)
  | succ t ih =>
      have htlt : t < k := Nat.lt_of_succ_le ht
      have htle : t ≤ k := Nat.le_of_lt htlt
      constructor
      · intro hx
        rcases (ih x htle).mp hx with ⟨w, hw⟩
        let w' : Fin ((k - (t + 1)) + 1) → ℝ :=
          cast (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt)) w
        let z : Fin (k - (t + 1)) → ℝ := fun i ↦ w' i.castSucc
        let last : ℝ := w' (Fin.last (k - (t + 1)))
        have hsnoc : Fin.snoc z last = w' := by
          -- Decompose the casted stage-`t` tail witness into its tail and last coordinate.
          simpa [z, last] using fin_snoc_castSucc_last_eq_self w'
        have hw_tail :
            cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt).symm)
              (Fin.snoc z last) = w := by
          -- Casting the reconstructed `Fin.snoc` tuple back recovers the original witness `w`.
          simpa [w'] using congrArg
            (cast (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt).symm))
            hsnoc
        have hw_cast :
            fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_eq_tail R t htle).symm)
                  (Fin.append x
                    (cast
                      (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt).symm)
                      (Fin.snoc z last))) ≤
              fourier_stage_rhs (liftedConeMatrix R) 0 t := by
          -- Rewrite the old witness `w` into the casted `Fin.snoc` form needed for the step lemma.
          simpa [hw_tail] using hw
        have hw_snoc :
            fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ R htlt).1.symm)
                  (Fin.snoc (Fin.append x z) last) ≤
              fourier_stage_rhs (liftedConeMatrix R) 0 t := by
          -- The adapter removes the remaining cast mismatch between `Fin.append` and `Fin.snoc`.
          exact (@append_snoc_stage_feasibility_iff n k t R htlt x z last).mp hw_cast
        have hnext :
            fourier_stage_matrix (liftedConeMatrix R) (t + 1) *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ R htlt).2.symm)
                  (Fin.append x z) ≤
              fourier_stage_rhs (liftedConeMatrix R) 0 (t + 1) := by
          -- One Fourier-Motzkin elimination step removes the last surviving coefficient coordinate.
          exact
            (lifted_fourier_stage_succ_iff_exists_last
              R htlt (Fin.append x z)).2 ⟨last, hw_snoc⟩
        refine ⟨z, ?_⟩
        simpa using hnext
      · rintro ⟨z, hz⟩
        have hz' :
            fourier_stage_matrix (liftedConeMatrix R) (t + 1) *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ R htlt).2.symm)
                  (Fin.append x z) ≤
              fourier_stage_rhs (liftedConeMatrix R) 0 (t + 1) := by
          -- Reexpress the successor-stage feasibility proposition in the public step-lemma shape.
          simpa using hz
        rcases (lifted_fourier_stage_succ_iff_exists_last
          R htlt (Fin.append x z)).1 hz' with ⟨last, hlast⟩
        have hw_cast :
            fourier_stage_matrix (liftedConeMatrix R) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_eq_tail R t htle).symm)
                  (Fin.append x
                    (cast
                      (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt).symm)
                      (Fin.snoc z last))) ≤
              fourier_stage_rhs (liftedConeMatrix R) 0 t := by
          -- Undo the adapter to recover the stage-`t` witness in the theorem statement.
          exact (@append_snoc_stage_feasibility_iff n k t R htlt x z last).mpr hlast
        refine (ih x htle).mpr ?_
        refine ⟨
          cast
            (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq htlt).symm)
            (Fin.snoc z last),
          ?_⟩
        simpa using hw_cast

/-- Helper for Theorem 3.11: after all coefficient coordinates are eliminated, cone membership is
exactly feasibility of the terminal lifted Fourier stage. -/
lemma matrix_cone_iff_terminal_lifted_feasible
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin n → ℝ) :
    x ∈ matrix_cone R ↔
      fourier_stage_matrix (liftedConeMatrix R) k *ᵥ
          cast
            (congrArg
              (fun q ↦ Fin q → ℝ)
              (lifted_fourier_stage_dim_terminal R).symm)
            x ≤
        fourier_stage_rhs (liftedConeMatrix R) 0 k := by
  constructor
  · intro hx
    rcases (@matrix_cone_iff_exists_stage_feasible n k k R x le_rfl).mp hx with
      ⟨z, hz⟩
    let hEqTail := lifted_fourier_stage_dim_eq_tail R k le_rfl
    let hZero : n + (k - k) = n := by
      simp
    let hTerminal := lifted_fourier_stage_dim_terminal R
    have happend : Fin.append x z = x ∘ Fin.cast hZero := by
      -- The terminal coefficient block is indexed by `Fin (k - k)`, so it has no coordinates.
      ext i
      cases i using Fin.addCases with
      | left i =>
          have hi : Fin.cast hZero (Fin.castAdd (k - k) i) = i := by
            ext
            simp
          simpa [Function.comp, hi]
      | right i =>
          exfalso
          exact fin_sub_self_false i
    have hTerminalEq : hTerminal = hEqTail.trans hZero := by
      -- The terminal-stage dimension equality is the stage-tail equality with `k - k = 0`.
      apply Subsingleton.elim
    have hcast :
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z) =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hTerminal.symm)
          x := by
      -- Rewrite the unique terminal witness away and identify the two public dimension casts.
      calc
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z)
            = Fin.append x z ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp hEqTail.symm]
        _ = (x ∘ Fin.cast hZero) ∘ Fin.cast hEqTail := by
              rw [happend]
        _ = x ∘ Fin.cast (hEqTail.trans hZero) := by
              ext i
              simp [Function.comp, Fin.cast_cast]
        _ = x ∘ Fin.cast hTerminal := by
              rw [hTerminalEq]
        _ = cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                hTerminal.symm)
              x := by
              symm
              rw [cast_fin_fn_eq_comp hTerminal.symm]
    rw [hcast] at hz
    exact hz
  · intro hx
    refine (@matrix_cone_iff_exists_stage_feasible n k k R x le_rfl).mpr ?_
    let z0 : Fin (k - k) → ℝ := fun i ↦ False.elim (fin_sub_self_false i)
    refine ⟨z0, ?_⟩
    let hEqTail := lifted_fourier_stage_dim_eq_tail R k le_rfl
    let hZero : n + (k - k) = n := by
      simp
    let hTerminal := lifted_fourier_stage_dim_terminal R
    have happend : Fin.append x z0 = x ∘ Fin.cast hZero := by
      -- Use the unique `Fin 0` witness in the reverse direction as well.
      ext i
      cases i using Fin.addCases with
      | left i =>
          have hi : Fin.cast hZero (Fin.castAdd (k - k) i) = i := by
            ext
            simp
          simpa [Function.comp, hi]
      | right i =>
          exfalso
          exact fin_sub_self_false i
    have hTerminalEq : hTerminal = hEqTail.trans hZero := by
      apply Subsingleton.elim
    have hcast :
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z0) =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hTerminal.symm)
          x := by
      -- The same terminal cast normalization works for the canonical empty witness.
      calc
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z0)
            = Fin.append x z0 ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp hEqTail.symm]
        _ = (x ∘ Fin.cast hZero) ∘ Fin.cast hEqTail := by
              rw [happend]
        _ = x ∘ Fin.cast (hEqTail.trans hZero) := by
              ext i
              simp [Function.comp, Fin.cast_cast]
        _ = x ∘ Fin.cast hTerminal := by
              rw [hTerminalEq]
        _ = cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                hTerminal.symm)
              x := by
              symm
              rw [cast_fin_fn_eq_comp hTerminal.symm]
    rwa [hcast]

/-- Helper for Theorem 3.11: one Fourier-Motzkin elimination step preserves a pointwise zero
right-hand side. -/
lemma fourier_step_rhs_zero_of_pointwise_zero
    {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin (n + 1)) ℝ)
    {b : ι → ℝ}
    (hb : ∀ i, b i = 0) :
    ∀ s : FourierStepIndex A, fourier_step_rhs A b s = 0 := by
  intro s
  -- Split the new inequality row according to the explicit Fourier-step rhs formula.
  rcases s with ⟨i, k⟩ | i
  · simp [fourier_step_rhs, hb i.1, hb k.1]
  · simp [fourier_step_rhs, hb i.1]

/-- Helper for Theorem 4.42: for an explicit successor-dimensional local stage package, a
pointwise-zero right-hand side stays pointwise zero after one Fourier-Motzkin step. -/
private theorem nextFourierStageRhsZero
    {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData d)
    (rhs : S.2.Row → ℝ)
    (h : S.1 = r + 1)
    (hZero : ∀ j, rhs j = 0) :
    ∀ i : (nextFourierStageMatrixData S).2.Row, nextFourierStageRhs S rhs i = 0 := by
  -- Unfold the sigma package once so the successor-stage right-hand side is literally
  -- `fourier_step_rhs`.
  cases S with
  | mk dim T =>
      dsimp at h hZero ⊢
      cases dim with
      | zero =>
          cases h
      | succ dim =>
          cases h
          intro i
          exact fourier_step_rhs_zero_of_pointwise_zero T.matrix hZero i

/-- Helper for Theorem 4.42: if the previous lifted Fourier stage has zero right-hand side,
then so does the successor stage. -/
lemma fourierStageSuccRhsEqZero
    {m n r t : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (hDim : fourier_stage_dim M t = r + 1)
    (hPrev : ∀ j : fourier_stage_row M t, fourier_stage_rhs M 0 t j = 0) :
    ∀ i : fourier_stage_row M (t + 1), fourier_stage_rhs M 0 (t + 1) i = 0 := by
  let S : Σ d : ℕ, FourierStageMatrixData d := fourier_stage_matrix_data M t
  have hS : S.1 = r + 1 := by
    simpa [S, fourier_stage_dim, fourier_stage_matrix_data] using hDim
  have hPrevS : ∀ j : S.2.Row, fourier_stage_rhs_data M 0 t j = 0 := by
    simpa [S, fourier_stage_row, fourier_stage_rhs, fourier_stage_matrix_data] using hPrev
  -- Route correction: unfold the local stage-data owner instead of transporting through the
  -- imported heterogeneous-equality API.
  simpa [S, fourier_stage_row, fourier_stage_rhs, fourier_stage_matrix_data,
    fourier_stage_rhs_data] using
    nextFourierStageRhsZero S (fourier_stage_rhs_data M 0 t) hS hPrevS

/-- Helper for Theorem 4.42: the iterated Fourier-Motzkin right-hand side stays identically zero
on the lifted homogeneous cone system. -/
lemma lifted_fourier_stage_rhs_eq_zero
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℝ)
    (ht : t ≤ k) :
    ∀ i : fourier_stage_row (liftedConeMatrix R) t,
      fourier_stage_rhs (liftedConeMatrix R) 0 t i = 0 := by
  induction t with
  | zero =>
      intro i
      -- At stage `0` the right-hand side is literally the zero function.
      rfl
  | succ t ih =>
      intro i
      let M : Matrix (Fin (n + (n + k))) (Fin (n + k)) ℝ := liftedConeMatrix R
      have htlt : t < k := Nat.lt_of_succ_le ht
      have htle : t ≤ k := Nat.le_of_lt htlt
      let r : ℕ := n + (k - (t + 1))
      have hDim : fourier_stage_dim M t = r + 1 := by
        -- Normalize the predecessor stage to the public successor-shape used by one elimination step.
        simpa [M, r] using (lifted_fourier_stage_dim_tail_succ R htlt).1
      let Mk : Matrix (fourier_stage_row M t) (Fin (r + 1)) ℝ :=
        cast
          (congrArg (fun q ↦ Matrix (fourier_stage_row M t) (Fin q) ℝ) hDim)
          (fourier_stage_matrix M t)
      have hPrev : ∀ j : fourier_stage_row M t, fourier_stage_rhs M 0 t j = 0 := by
        -- The induction hypothesis already gives pointwise-zero rhs on the previous stage.
        simpa [M] using ih htle
      have hSuccZero :
          ∀ j : fourier_stage_row M (t + 1), fourier_stage_rhs M 0 (t + 1) j = 0 := by
        -- Apply the function-level successor-stage zero-rhs bridge before fixing the row.
        simpa [M, Mk] using fourierStageSuccRhsEqZero M hDim hPrev
      -- Evaluate the successor-stage pointwise-zero statement at the requested row.
      exact hSuccZero i

/-- Helper for Theorem 3.11: every cone generated by finitely many columns is polyhedral. -/
theorem matrixCone_isPolyhedralCone
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) :
    is_polyhedral_cone (matrix_cone R : Set (Fin n → ℝ)) := by
  -- Route correction: the concrete lifted encoding is now isolated in
  -- `lifted_matrix_cone_system_iff`; the remaining work is exactly the textbook `k`-step Fourier
  -- elimination argument on the trailing coefficient coordinates.
  refine (is_polyhedral_cone_iff).2 ?_
  let rowEquiv :
      fourier_stage_row (liftedConeMatrix R) k ≃
        Fin (fourier_stage_rows (liftedConeMatrix R) k) :=
    Fintype.equivFin (fourier_stage_row (liftedConeMatrix R) k)
  let colEquiv :
      Fin (fourier_stage_dim (liftedConeMatrix R) k) ≃ Fin n :=
    Equiv.cast (congrArg Fin (lifted_fourier_stage_dim_terminal R))
  let A : Matrix (Fin (fourier_stage_rows (liftedConeMatrix R) k)) (Fin n) ℝ :=
    (fourier_stage_matrix (liftedConeMatrix R) k).reindex rowEquiv colEquiv
  refine ⟨fourier_stage_rows (liftedConeMatrix R) k, A, ?_⟩
  ext x
  have hcastVec :
      x ∘ colEquiv =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_terminal R).symm)
          x := by
    -- The terminal column equivalence is the same `Fin.cast` transport as the visible cast.
    have hcol :
        (colEquiv : Fin (fourier_stage_dim (liftedConeMatrix R) k) → Fin n) =
          Fin.cast (lifted_fourier_stage_dim_terminal R) := by
      simpa [colEquiv] using
        (Fin.cast_eq_cast' (congrArg Fin (lifted_fourier_stage_dim_terminal R)))
    rw [hcol]
    rw [cast_fin_fn_eq_comp (lifted_fourier_stage_dim_terminal R).symm]
  have hmul :
      A *ᵥ x =
        (fourier_stage_matrix (liftedConeMatrix R) k *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_terminal R).symm)
              x) ∘
          rowEquiv.symm := by
    -- Reindexing the terminal Fourier stage only renames rows and transports the visible columns.
    calc
      A *ᵥ x =
          (fourier_stage_matrix (liftedConeMatrix R) k *ᵥ (x ∘ colEquiv)) ∘ rowEquiv.symm := by
            simpa [A, colEquiv] using
              (Matrix.submatrix_mulVec_equiv
                (fourier_stage_matrix (liftedConeMatrix R) k)
                x
                rowEquiv.symm
                colEquiv.symm)
      _ =
          (fourier_stage_matrix (liftedConeMatrix R) k *ᵥ
              cast
                (congrArg
                  (fun q ↦ Fin q → ℝ)
                  (lifted_fourier_stage_dim_terminal R).symm)
                x) ∘
            rowEquiv.symm := by
              rw [hcastVec]
  constructor
  · intro hx
    have hxStage := (@matrix_cone_iff_terminal_lifted_feasible n k R x).1 hx
    refine (mem_matrix_polyhedral_cone A x).2 ?_
    intro i
    -- Evaluate the terminal-stage feasibility inequality on the corresponding reindexed row.
    rw [hmul]
    have hzero :
        fourier_stage_rhs (liftedConeMatrix R) 0 k (rowEquiv.symm i) = 0 :=
      (@lifted_fourier_stage_rhs_eq_zero n k k R le_rfl) (rowEquiv.symm i)
    have hstage := hxStage (rowEquiv.symm i)
    rw [hzero] at hstage
    exact hstage
  · intro hx
    refine (@matrix_cone_iff_terminal_lifted_feasible n k R x).2 ?_
    intro i
    have hxi : (A *ᵥ x) (rowEquiv i) ≤ 0 := (mem_matrix_polyhedral_cone A x).1 hx (rowEquiv i)
    -- Read the reindexed inequality back on the original terminal-stage row.
    rw [hmul] at hxi
    have happly : rowEquiv.symm (rowEquiv i) = i := rowEquiv.symm_apply_apply i
    have hxi' :
        (fourier_stage_matrix (liftedConeMatrix R) k *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_terminal R).symm)
              x) i ≤
          0 := by
      simpa [Function.comp, happly] using hxi
    have hzero :
        fourier_stage_rhs (liftedConeMatrix R) 0 k i = 0 :=
      (@lifted_fourier_stage_rhs_eq_zero n k k R le_rfl) i
    rw [hzero]
    exact hxi'

/-- Helper for Theorem 4.42: a finitely generated pointed cone is polyhedral once it is rewritten
through a finite matrix-cone presentation. -/
theorem fgPointedCone_isPolyhedralCone
    {n : ℕ} {C : PointedCone ℝ (Fin n → ℝ)}
    (hC_fg : C.FG) :
    is_polyhedral_cone (C : Set (Fin n → ℝ)) := by
  rcases fg_iff_exists_matrix_cone.mp hC_fg with ⟨k, R, hR⟩
  have hRset :
      (C : Set (Fin n → ℝ)) =
        (((matrix_cone R : PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    exact congrArg (fun K : PointedCone ℝ (Fin n → ℝ) ↦ (K : Set (Fin n → ℝ))) hR
  -- Transfer the forward matrix-cone theorem along the pointed-cone carrier equality.
  simpa [hRset] using matrixCone_isPolyhedralCone R

/-- Helper for Theorem 4.42: the missing local Chapter 3.11 owner converts a polyhedral cone into
a finite matrix-cone presentation. -/
theorem exists_matrixCone_eq_of_isPolyhedralCone
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : is_polyhedral_cone C) :
    ∃ k : ℕ, ∃ R : Matrix (Fin n) (Fin k) ℝ, C = (matrix_cone R : Set (Fin n → ℝ)) := by
  rcases (is_polyhedral_cone_iff.mp hC) with ⟨m, A, rfl⟩
  -- Route correction: use the localized forward Fourier owner for the row cone of `A`, then apply
  -- the already-stable dual-presentation inclusions to identify `polyhedron_le_set A 0`.
  rcases (is_polyhedral_cone_iff.mp (matrixCone_isPolyhedralCone A.transpose)) with ⟨k, B, hdual⟩
  refine ⟨k, B.transpose, ?_⟩
  ext x
  constructor
  · intro hx
    exact matrix_polyhedral_cone_subset_matrix_cone_transpose_of_dual_presentation hdual hx
  · intro hx
    exact matrix_cone_transpose_subset_matrix_polyhedral_of_dual_presentation hdual hx

/-- Helper for Theorem 4.42: a pointed cone is finitely generated exactly when its underlying set
is polyhedral. -/
theorem isFinitelyGeneratedCone_iff_isPolyhedralCone
    {n : ℕ} {C : PointedCone ℝ (Fin n → ℝ)} :
    C.FG ↔ is_polyhedral_cone (C : Set (Fin n → ℝ)) := by
  constructor
  · intro hC_fg
    exact fgPointedCone_isPolyhedralCone hC_fg
  · intro hC_polyhedral
    rcases exists_matrixCone_eq_of_isPolyhedralCone hC_polyhedral with ⟨k, R, hR⟩
    refine fg_iff_exists_matrix_cone.mpr ?_
    refine ⟨k, R, ?_⟩
    ext x
    change x ∈ (C : Set (Fin n → ℝ)) ↔
      x ∈ (((matrix_cone R : PointedCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))
    simpa [hR]

/-- Helper for Theorem 4.42: multiplying the homogenized matrix by `(x,y)` produces the rowwise
slacks `A *ᵥ x - y • b` together with the final coordinate `-y`. -/
def homogenized_polyhedron_matrix
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  fun i ↦
    Fin.lastCases
      (Fin.snoc (fun _ : Fin n ↦ (0 : ℝ)) (-1))
      (fun i' ↦ Fin.snoc (A i') (-b i'))
      i

/-- Helper for Theorem 4.42: multiplying the homogenized matrix by `(x,y)` expands rowwise to the
visible slacks and the final coordinate `-y`. -/
lemma homogenized_polyhedron_matrix_mulVec_snoc
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (y : ℝ) :
    homogenized_polyhedron_matrix A b *ᵥ Fin.snoc x y =
      Fin.snoc (fun i ↦ (A *ᵥ x) i - y * b i) (-y) := by
  -- Evaluate the homogenized system row by row.
  ext i
  cases i using Fin.lastCases with
  | last =>
      -- The final row is exactly the constraint `-y ≤ 0`.
      simp [homogenized_polyhedron_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  | cast i =>
      -- Each original row becomes `(A i, -b i) · (x, y) = (A *ᵥ x) i - y * b i`.
      simp [homogenized_polyhedron_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, mul_comm]

/-- Helper for Theorem 4.42: membership in the homogenized cone is equivalent to the visible
inequalities `A *ᵥ x ≤ y • b` together with `0 ≤ y`. -/
lemma mem_homogenized_polyhedron_cone_iff_general
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (y : ℝ) :
    Fin.snoc x y ∈ polyhedron_le_set (homogenized_polyhedron_matrix A b) 0 ↔
      (A *ᵥ x ≤ fun i ↦ y * b i) ∧ 0 ≤ y := by
  -- Expand the homogenized inequalities and separate the visible and final coordinates.
  change homogenized_polyhedron_matrix A b *ᵥ Fin.snoc x y ≤ 0 ↔
    (A *ᵥ x ≤ fun i ↦ y * b i) ∧ 0 ≤ y
  rw [homogenized_polyhedron_matrix_mulVec_snoc]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      have hi := hx i.castSucc
      exact sub_nonpos.mp (by simpa using hi)
    · have hlast := hx (Fin.last m)
      exact neg_nonpos.mp (by simpa using hlast)
  · rintro ⟨hx, hy⟩
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa using neg_nonpos.mpr hy
    · have hi := hx i
      simpa using sub_nonpos.mpr hi

/-- Helper for Theorem 4.42: the `y = 1` slice of the homogenized cone is exactly the original
polyhedron. -/
lemma mem_homogenized_polyhedron_cone_iff
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin.snoc x 1 ∈ polyhedron_le_set (homogenized_polyhedron_matrix A b) 0 ↔
      x ∈ polyhedron_le_set A b := by
  -- Rewrite the homogeneous inequalities and read off the non-last coordinates.
  simpa using
    (mem_homogenized_polyhedron_cone_iff_general A b x (1 : ℝ))

/-- Helper for Theorem 4.42: every matrix column belongs to the cone generated by all columns. -/
lemma matrix_column_mem_matrix_cone
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) (j : Fin k) :
    (fun i : Fin n ↦ R i j) ∈ matrix_cone R := by
  -- Select the `j`-th column by the singleton coefficient vector.
  refine mem_matrix_cone_iff.mpr ?_
  refine ⟨Pi.single j 1, ?_, ?_⟩
  · intro t
    by_cases ht : t = j
    · subst ht
      simp [Pi.single]
    · simp [Pi.single, ht]
  · ext i
    exact congrFun (Matrix.mulVec_single_one R j) i

/-- Helper for Theorem 4.42: a point of `convexHull ℝ (Set.range v)` is exactly a barycentric
combination of the finite family `v`. -/
lemma mem_convexHull_range_iff_exists_barycentric_weights
    {n p : ℕ} {v : Fin p → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ lam : Fin p → ℝ, (∀ i : Fin p, 0 ≤ lam i) ∧
        (∑ i, lam i = 1) ∧ x = ∑ i, lam i • v i := by
  constructor
  · intro hx
    -- Convert the finite-support affine-combination witness into full `Fin p` barycentric
    -- coordinates by extending the weights with `0` off the support.
    rw [convexHull_range_eq_exists_affineCombination] at hx
    rcases hx with ⟨s, w, hw_nonneg, hw_sum, hx⟩
    let lam : Fin p → ℝ := Set.indicator (↑s) w
    have hlam_nonneg : 0 ≤ lam := by
      intro j
      by_cases hj : j ∈ s
      · simp [lam, hj, hw_nonneg j hj]
      · simp [lam, hj]
    have hlam_sum : ∑ i : Fin p, lam i = 1 := by
      classical
      have hsum' : ∑ i : Fin p, lam i = s.sum w := by
        simpa [lam] using
          (Finset.sum_indicator_subset w (by simp : s ⊆ Finset.univ))
      rw [hsum']
      exact hw_sum
    have hx' : ∑ i : Fin p, lam i • v i = x := by
      have hsub : s ⊆ Finset.univ := by
        intro i hi
        simp
      have hs :
          s.affineCombination ℝ v w =
            Finset.univ.affineCombination ℝ v lam := by
        classical
        simpa [lam] using
          (Finset.affineCombination_indicator_subset
            w v hsub)
      calc
        ∑ i : Fin p, lam i • v i = Finset.univ.affineCombination ℝ v lam := by
          symm
          exact Finset.affineCombination_eq_linear_combination Finset.univ v lam hlam_sum
        _ = s.affineCombination ℝ v w := hs.symm
        _ = x := hx
    exact ⟨lam, fun i ↦ hlam_nonneg i, hlam_sum, hx'.symm⟩
  · rintro ⟨lam, hlam_nonneg, hlam_sum, hlamx⟩
    -- Package the full-index barycentric coordinates directly as a convex-hull witness.
    exact
      mem_convexHull_of_exists_fintype lam v hlam_nonneg hlam_sum
        (fun i ↦ Set.mem_range_self i) (by simpa using hlamx.symm)

/-- Helper for Theorem 4.42: the same barycentric-coordinate description works for any finite
index type after reindexing to `Fin`. -/
lemma mem_convexHull_range_iff_exists_barycentric_weights_fintype
    {ι : Type*} [Fintype ι] {n : ℕ} {v : ι → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
        (∑ i, lam i = 1) ∧ x = ∑ i, lam i • v i := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let v' : Fin (Fintype.card ι) → Fin n → ℝ := fun i ↦ v (e.symm i)
  have hrange : Set.range v' = Set.range v := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [v']⟩
  constructor
  · intro hx
    have hx' : x ∈ convexHull ℝ (Set.range v') := by
      simpa [v', hrange] using hx
    rcases mem_convexHull_range_iff_exists_barycentric_weights.mp hx' with
      ⟨lam', hlam'_nonneg, hlam'_sum, hrepr⟩
    refine ⟨fun i ↦ lam' (e i), ?_, ?_, ?_⟩
    · intro i
      exact hlam'_nonneg (e i)
    · have hsum_reindex :
          ∑ i : ι, lam' (e i) = ∑ j : Fin (Fintype.card ι), lam' j := by
        exact
          Fintype.sum_equiv e
            (fun i : ι ↦ lam' (e i))
            (fun j : Fin (Fintype.card ι) ↦ lam' j)
            (fun i ↦ rfl)
      exact hsum_reindex.trans hlam'_sum
    · calc
        x = ∑ j : Fin (Fintype.card ι), lam' j • v' j := hrepr
        _ = ∑ i : ι, lam' (e i) • v i := by
              exact
                (Fintype.sum_equiv e
                  (fun i : ι ↦ lam' (e i) • v i)
                  (fun j : Fin (Fintype.card ι) ↦ lam' j • v' j)
                  (fun i ↦ by simp [v'])).symm
  · rintro ⟨lam, hlam_nonneg, hlam_sum, hrepr⟩
    have hx' : x ∈ convexHull ℝ (Set.range v') := by
      refine mem_convexHull_range_iff_exists_barycentric_weights.mpr ?_
      refine ⟨fun j ↦ lam (e.symm j), ?_, ?_, ?_⟩
      · intro j
        exact hlam_nonneg (e.symm j)
      · calc
          ∑ j : Fin (Fintype.card ι), lam (e.symm j) = ∑ i : ι, lam i := by
            exact
              (Fintype.sum_equiv e
                (fun i : ι ↦ lam i)
                (fun j : Fin (Fintype.card ι) ↦ lam (e.symm j))
                (fun i ↦ by simp)).symm
          _ = 1 := hlam_sum
      · calc
          x = ∑ i : ι, lam i • v i := hrepr
          _ = ∑ j : Fin (Fintype.card ι), lam (e.symm j) • v' j := by
                exact
                  Fintype.sum_equiv e
                    (fun i : ι ↦ lam i • v i)
                    (fun j : Fin (Fintype.card ι) ↦ lam (e.symm j) • v' j)
                    (fun i ↦ by simp [v'])
    simpa [v', hrange] using hx'

/-- Helper for Theorem 4.42: a finite nonnegative weighted sum belongs to the cone generated by
the same indexed family. -/
lemma finite_weighted_sum_mem_cone_range
    {ι : Type*} [Fintype ι] {n : ℕ}
    (r : ι → Fin n → ℝ)
    (u : ι → ℝ)
    (hu_nonneg : ∀ i, 0 ≤ u i) :
    (fun t : Fin n ↦ ∑ i : ι, u i * r i t) ∈ cone (Set.range r) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- Reindex the finite family once so the cone witness uses the canonical `Fin` index type.
  refine (mem_cone_iff).2 ?_
  refine ⟨Fintype.card ι, fun j ↦ r (e.symm j), ?_, ?_⟩
  · intro j
    exact Set.mem_range_self (e.symm j)
  · refine ⟨fun j ↦ u (e.symm j), ?_, ?_⟩
    · intro j
      exact hu_nonneg (e.symm j)
    · ext t
      calc
        (fun t : Fin n ↦ ∑ i : ι, u i * r i t) t = ∑ i : ι, u i * r i t := by
          rfl
        _ = ∑ j : Fin (Fintype.card ι), u (e.symm j) * r (e.symm j) t := by
              exact
                Fintype.sum_equiv e
                  (fun i : ι ↦ u i * r i t)
                  (fun j : Fin (Fintype.card ι) ↦ u (e.symm j) * r (e.symm j) t)
                  (fun i ↦ by simp)
        _ = (∑ j : Fin (Fintype.card ι), u (e.symm j) • r (e.symm j)) t := by
              simp [smul_eq_mul]

/-- Helper for Theorem 4.42: cone membership for a finite indexed family can be written using
nonnegative coefficients on the original index type. -/
lemma mem_cone_range_iff_exists_weights
    {ι : Type*} [Fintype ι] {n : ℕ} {r : ι → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ cone (Set.range r) ↔
      ∃ u : ι → ℝ, (∀ i : ι, 0 ≤ u i) ∧ x = ∑ i, u i • r i := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let r' : Fin (Fintype.card ι) → Fin n → ℝ := fun i ↦ r (e.symm i)
  have hrange : Set.range r' = Set.range r := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [r']⟩
  constructor
  · intro hx
    have hx' : x ∈ finitely_generated_cone r' := by
      simpa [finitely_generated_cone, r', hrange] using hx
    rcases mem_finitely_generated_cone_iff.mp hx' with ⟨u', hu'_nonneg, hrepr⟩
    refine ⟨fun i ↦ u' (e i), ?_, ?_⟩
    · intro i
      exact hu'_nonneg (e i)
    · calc
        x = ∑ j : Fin (Fintype.card ι), u' j • r' j := hrepr
        _ = ∑ i : ι, u' (e i) • r i := by
              exact
                (Fintype.sum_equiv e
                  (fun i : ι ↦ u' (e i) • r i)
                  (fun j : Fin (Fintype.card ι) ↦ u' j • r' j)
                  (fun i ↦ by simp [r'])).symm
  · rintro ⟨u, hu_nonneg, hrepr⟩
    have hx' : x ∈ finitely_generated_cone r' := by
      refine mem_finitely_generated_cone_iff.mpr ?_
      refine ⟨fun j ↦ u (e.symm j), ?_, ?_⟩
      · intro j
        exact hu_nonneg (e.symm j)
      · calc
          x = ∑ i : ι, u i • r i := hrepr
          _ = ∑ j : Fin (Fintype.card ι), u (e.symm j) • r' j := by
                exact
                  Fintype.sum_equiv e
                    (fun i : ι ↦ u i • r i)
                    (fun j : Fin (Fintype.card ι) ↦ u (e.symm j) • r' j)
                    (fun i ↦ by simp [r'])
    simpa [finitely_generated_cone, r', hrange] using hx'

/-- Helper for Theorem 4.42: after splitting columns by last-coordinate sign, the `y = 1` slice of
the matrix cone is the convex hull of normalized positive-height columns plus the cone of
zero-height columns. -/
lemma mem_slice_one_matrix_cone_iff_mem_convexHull_add_cone_of_nonnegative_heights
    {n k : ℕ} (R : Matrix (Fin (n + 1)) (Fin k) ℝ)
    (hlast : ∀ j : Fin k, 0 ≤ R (Fin.last n) j)
    {x : Fin n → ℝ} :
    let J₁ : Type := {j : Fin k // 0 < R (Fin.last n) j}
    let J₀ : Type := {j : Fin k // R (Fin.last n) j = 0}
    let v : J₁ → Fin n → ℝ := fun a i ↦ R i.castSucc a.1 / R (Fin.last n) a.1
    let r : J₀ → Fin n → ℝ := fun b i ↦ R i.castSucc b.1
    (Fin.snoc x (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
      PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) ↔
      x ∈ convexHull ℝ (Set.range v) + cone (Set.range r) := by
  dsimp
  let J₁ : Type := {j : Fin k // 0 < R (Fin.last n) j}
  let J₀ : Type := {j : Fin k // R (Fin.last n) j = 0}
  let v : J₁ → Fin n → ℝ := fun a i ↦ R i.castSucc a.1 / R (Fin.last n) a.1
  let r : J₀ → Fin n → ℝ := fun b i ↦ R i.castSucc b.1
  constructor
  · intro hx
    rcases mem_matrix_cone_iff.mp hx with ⟨ξ, hξ_nonneg, hξx⟩
    let lam : J₁ → ℝ := fun a ↦ ξ a.1 * R (Fin.last n) a.1
    let μ : J₀ → ℝ := fun b ↦ ξ b.1
    have hlam_nonneg : ∀ a : J₁, 0 ≤ lam a := by
      intro a
      exact mul_nonneg (hξ_nonneg a.1) (hlast a.1)
    have hμ_nonneg : ∀ b : J₀, 0 ≤ μ b := by
      intro b
      exact hξ_nonneg b.1
    have hnot_pos_iff_zero : ∀ j : Fin k, (¬ 0 < R (Fin.last n) j) ↔ R (Fin.last n) j = 0 := by
      intro j
      constructor
      · intro hj
        exact le_antisymm (not_lt.mp hj) (hlast j)
      · intro hj
        simp [hj]
    have hle_iff_zero : ∀ j : Fin k, (R (Fin.last n) j ≤ 0) ↔ R (Fin.last n) j = 0 := by
      intro j
      constructor
      · intro hj
        exact le_antisymm hj (hlast j)
      · intro hj
        simp [hj]
    have hlast_sum :
        (1 : ℝ) = ∑ j : Fin k, ξ j * R (Fin.last n) j := by
      -- The last coordinate of `R *ᵥ ξ` records the total positive height.
      have hcoord := congrFun hξx (Fin.last n)
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hcoord.symm
    have hzero_last :
        Finset.sum (Finset.univ.filter (fun j : Fin k ↦ ¬ 0 < R (Fin.last n) j))
            (fun j : Fin k ↦ ξ j * R (Fin.last n) j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hj' : ¬ 0 < R (Fin.last n) j := (Finset.mem_filter.mp hj).2
      have hzero : R (Fin.last n) j = 0 := (hnot_pos_iff_zero j).mp hj'
      simp [hzero]
    have hlam_sum : ∑ a : J₁, lam a = 1 := by
      -- Split the last-coordinate sum into positive-height and zero-height columns.
      have hsplit :
          ∑ j : Fin k, ξ j * R (Fin.last n) j =
            ∑ a : J₁, ξ a.1 * R (Fin.last n) a.1 := by
        calc
          ∑ j : Fin k, ξ j * R (Fin.last n) j
              = Finset.sum (Finset.univ.filter (fun j : Fin k ↦ 0 < R (Fin.last n) j))
                    (fun j : Fin k ↦ ξ j * R (Fin.last n) j)
                  + Finset.sum (Finset.univ.filter (fun j : Fin k ↦ ¬ 0 < R (Fin.last n) j))
                  (fun j : Fin k ↦ ξ j * R (Fin.last n) j) := by
                    symm
                    exact
                      Finset.sum_filter_add_sum_filter_not Finset.univ
                        (fun j : Fin k ↦ 0 < R (Fin.last n) j)
                        (fun j : Fin k ↦ ξ j * R (Fin.last n) j)
          _ = Finset.sum (Finset.univ.filter (fun j : Fin k ↦ 0 < R (Fin.last n) j))
                (fun j : Fin k ↦ ξ j * R (Fin.last n) j) := by
                  rw [hzero_last, add_zero]
          _ = ∑ a : J₁, ξ a.1 * R (Fin.last n) a.1 := by
                simpa [J₁] using
                  (@Finset.sum_subtype_eq_sum_filter
                    (Fin k)
                    ℝ
                    Finset.univ
                    inferInstance
                    (fun j : Fin k ↦ ξ j * R (Fin.last n) j)
                    (fun j : Fin k ↦ 0 < R (Fin.last n) j)
                    inferInstance).symm
      have : (1 : ℝ) = ∑ a : J₁, lam a := by
        simpa [lam] using hlast_sum.trans hsplit
      simpa using this.symm
    have hrepr :
        x = ∑ a : J₁, lam a • v a + ∑ b : J₀, μ b • r b := by
      -- Split each visible coordinate into its positive-height and zero-height contributions.
      ext i
      have hcoord : x i = ∑ j : Fin k, ξ j * R i.castSucc j := by
        have hi := congrFun hξx i.castSucc
        simpa [Matrix.mulVec, dotProduct, mul_comm] using hi.symm
      have hpos :
          Finset.sum (Finset.univ.filter (fun j : Fin k ↦ 0 < R (Fin.last n) j))
              (fun j : Fin k ↦ ξ j * R i.castSucc j)
            = ∑ a : J₁, lam a • v a i := by
        calc
          Finset.sum (Finset.univ.filter (fun j : Fin k ↦ 0 < R (Fin.last n) j))
                (fun j : Fin k ↦ ξ j * R i.castSucc j)
              = ∑ a : J₁, ξ a.1 * R i.castSucc a.1 := by
                  simpa [J₁] using
                    (@Finset.sum_subtype_eq_sum_filter
                      (Fin k)
                      ℝ
                      Finset.univ
                      inferInstance
                      (fun j : Fin k ↦ ξ j * R i.castSucc j)
                      (fun j : Fin k ↦ 0 < R (Fin.last n) j)
                      inferInstance).symm
          _ = ∑ a : J₁, lam a • v a i := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                have hne : R (Fin.last n) a.1 ≠ 0 := ne_of_gt a.2
                dsimp [lam, v]
                field_simp [hne]
      have hzero :
          Finset.sum (Finset.univ.filter (fun j : Fin k ↦ ¬ 0 < R (Fin.last n) j))
              (fun j : Fin k ↦ ξ j * R i.castSucc j)
            = ∑ b : J₀, μ b • r b i := by
        calc
          Finset.sum (Finset.univ.filter (fun j : Fin k ↦ ¬ 0 < R (Fin.last n) j))
                (fun j : Fin k ↦ ξ j * R i.castSucc j)
              = Finset.sum (Finset.univ.filter (fun j : Fin k ↦ R (Fin.last n) j = 0))
                  (fun j : Fin k ↦ ξ j * R i.castSucc j) := by
                    refine Finset.sum_congr ?_ ?_
                    · ext j
                      simp [hle_iff_zero j]
                    · intro j hj
                      rfl
          _ = ∑ b : J₀, ξ b.1 * R i.castSucc b.1 := by
                simpa [J₀] using
                  (@Finset.sum_subtype_eq_sum_filter
                    (Fin k)
                    ℝ
                    Finset.univ
                    inferInstance
                    (fun j : Fin k ↦ ξ j * R i.castSucc j)
                    (fun j : Fin k ↦ R (Fin.last n) j = 0)
                    inferInstance).symm
          _ = ∑ b : J₀, μ b • r b i := by
                refine Finset.sum_congr rfl ?_
                intro b hb
                rfl
      calc
        x i = ∑ j : Fin k, ξ j * R i.castSucc j := hcoord
        _ = Finset.sum (Finset.univ.filter (fun j : Fin k ↦ 0 < R (Fin.last n) j))
              (fun j : Fin k ↦ ξ j * R i.castSucc j)
              + Finset.sum (Finset.univ.filter (fun j : Fin k ↦ ¬ 0 < R (Fin.last n) j))
                  (fun j : Fin k ↦ ξ j * R i.castSucc j) := by
                    symm
                    exact
                      Finset.sum_filter_add_sum_filter_not Finset.univ
                        (fun j : Fin k ↦ 0 < R (Fin.last n) j)
                        (fun j : Fin k ↦ ξ j * R i.castSucc j)
        _ = ∑ a : J₁, lam a • v a i + ∑ b : J₀, μ b • r b i := by
              rw [hpos, hzero]
        _ = (∑ a : J₁, lam a • v a + ∑ b : J₀, μ b • r b) i := by
              simp
    refine ⟨∑ a : J₁, lam a • v a, ?_, ∑ b : J₀, μ b • r b, ?_, ?_⟩
    · -- The positive-height coefficients are barycentric weights on the normalized columns.
      exact
        mem_convexHull_range_iff_exists_barycentric_weights_fintype.mpr
          ⟨lam, hlam_nonneg, hlam_sum, rfl⟩
    · -- The zero-height coefficients give a conic combination of the zero-height columns.
      convert finite_weighted_sum_mem_cone_range r μ hμ_nonneg using 1
      ext t
      simp [smul_eq_mul]
    · simp [hrepr]
  · rintro ⟨xQ, hxQ, xR, hxR, rfl⟩
    rcases mem_convexHull_range_iff_exists_barycentric_weights_fintype.mp hxQ with
      ⟨lam, hlam_nonneg, hlam_sum, hQrepr⟩
    rcases mem_cone_range_iff_exists_weights.mp hxR with ⟨μ, hμ_nonneg, hRrepr⟩
    have hpos_col : ∀ a : J₁, (Fin.snoc (v a) (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
        PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
      intro a
      have hcol : (fun i : Fin (n + 1) ↦ R i a.1) ∈ ((matrix_cone R :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) :=
        matrix_column_mem_matrix_cone R a.1
      have hinv_nonneg : 0 ≤ (R (Fin.last n) a.1)⁻¹ := by
        exact inv_nonneg.mpr (hlast a.1)
      have hscaled :
          (R (Fin.last n) a.1)⁻¹ • (fun i : Fin (n + 1) ↦ R i a.1) ∈ ((matrix_cone R :
            PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) :=
        PointedCone.smul_mem (matrix_cone R) hinv_nonneg hcol
      -- Normalize the positive-height generator so its last coordinate becomes `1`.
      convert hscaled using 1
      ext i
      cases i using Fin.lastCases with
      | last =>
          simp [smul_eq_mul, v, ne_of_gt a.2]
      | cast i =>
          simp [smul_eq_mul, v, div_eq_mul_inv, mul_comm]
    have hzero_col : ∀ b : J₀, (Fin.snoc (r b) (0 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
        PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
      intro b
      have hcol : (fun i : Fin (n + 1) ↦ R i b.1) ∈ ((matrix_cone R :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) :=
        matrix_column_mem_matrix_cone R b.1
      -- Zero-height generators are already ray generators of the slice.
      convert hcol using 1
      ext i
      cases i using Fin.lastCases with
      | last =>
          simp [r, b.2]
      | cast i =>
          simp [r]
    have hQmem :
        (Fin.snoc (∑ a : J₁, lam a • v a) (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
      have hsum_mem :
          ∑ a : J₁, lam a • (Fin.snoc (v a) (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
            PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
        exact
          Submodule.sum_mem (matrix_cone R) (fun a _ ↦
            PointedCone.smul_mem (matrix_cone R) (hlam_nonneg a) (hpos_col a))
      have hsum_eq :
          ∑ a : J₁, lam a • (Fin.snoc (v a) (1 : ℝ) : Fin (n + 1) → ℝ) =
            (Fin.snoc (∑ a : J₁, lam a • v a) (1 : ℝ) : Fin (n + 1) → ℝ) := by
        ext i
        cases i using Fin.lastCases with
        | last =>
            simpa [hlam_sum]
        | cast i =>
            simp
      simpa [hsum_eq] using hsum_mem
    have hRmem :
        (Fin.snoc (∑ b : J₀, μ b • r b) (0 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
      have hsum_mem :
          ∑ b : J₀, μ b • (Fin.snoc (r b) (0 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
            PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
        exact
          Submodule.sum_mem (matrix_cone R) (fun b _ ↦
            PointedCone.smul_mem (matrix_cone R) (hμ_nonneg b) (hzero_col b))
      have hsum_eq :
          ∑ b : J₀, μ b • (Fin.snoc (r b) (0 : ℝ) : Fin (n + 1) → ℝ) =
            (Fin.snoc (∑ b : J₀, μ b • r b) (0 : ℝ) : Fin (n + 1) → ℝ) := by
        ext i
        cases i using Fin.lastCases with
        | last =>
            simp
        | cast i =>
            simp
      simpa [hsum_eq] using hsum_mem
    have hadd :
        (Fin.snoc (∑ a : J₁, lam a • v a + ∑ b : J₀, μ b • r b) (1 : ℝ) :
          Fin (n + 1) → ℝ) ∈
          ((matrix_cone R : PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
      have hsum_mem :
          (Fin.snoc (∑ a : J₁, lam a • v a) (1 : ℝ) : Fin (n + 1) → ℝ) +
            (Fin.snoc (∑ b : J₀, μ b • r b) (0 : ℝ) : Fin (n + 1) → ℝ) ∈
              ((matrix_cone R : PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) :=
        Submodule.add_mem (matrix_cone R) hQmem hRmem
      have hsnoc_add :
          (Fin.snoc (∑ a : J₁, lam a • v a) (1 : ℝ) : Fin (n + 1) → ℝ) +
              (Fin.snoc (∑ b : J₀, μ b • r b) (0 : ℝ) : Fin (n + 1) → ℝ) =
            (Fin.snoc
              (∑ a : J₁, lam a • v a + ∑ b : J₀, μ b • r b) (1 : ℝ) :
              Fin (n + 1) → ℝ) := by
        ext i
        cases i using Fin.lastCases with
        | last =>
            simp
        | cast i =>
            simp
      simpa [hsnoc_add] using hsum_mem
    simpa [hQrepr, hRrepr] using hadd

end Theorem442Local

/-- Helper for Theorem 4.42: a polytope can be reindexed onto a `Fin`-indexed family of vertices. -/
lemma exists_convexHull_range_eq_of_isPolytope
    {k : ℕ} {Q : Set (Fin k → ℝ)}
    (hQ_polytope : Q.IsPolytope ℝ) :
    ∃ p : ℕ, ∃ vertices : Fin p → Fin k → ℝ, Q = convexHull ℝ (Set.range vertices) := by
  rcases hQ_polytope with ⟨V, hV_finite, hQ_eq⟩
  let s : Finset (Fin k → ℝ) := hV_finite.toFinset
  let vertices : Fin s.card → Fin k → ℝ := fun i ↦ ((Finset.equivFin s).symm i).1
  have hV_range : Set.range vertices = V := by
    -- Reindex the finite vertex set onto a canonical `Fin` family.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hi_mem : (((Finset.equivFin s).symm i).1) ∈ (s : Set (Fin k → ℝ)) :=
        ((Finset.equivFin s).symm i).2
      simpa [vertices, s] using hi_mem
    · intro hx
      have hx' : x ∈ (s : Set (Fin k → ℝ)) := by
        simpa [s] using hx
      refine ⟨(Finset.equivFin s) ⟨x, hx'⟩, ?_⟩
      simp [vertices]
  exact ⟨s.card, vertices, by rw [hQ_eq, ← hV_range]⟩

/-- Helper for Theorem 4.42: the range of a finite family is the same set as the image of
`Finset.univ` under that family. -/
lemma range_eq_image_univ
    {α : Type*} [Fintype α] {β : Type*} [DecidableEq β] (f : α → β) :
    Set.range f = (Finset.univ.image f : Set β) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.2 ⟨x, by simp, rfl⟩
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Theorem 4.42: the finitely generated cone of a finite family is exactly the pointed
cone hull of its range. -/
lemma finitely_generated_cone_eq_pointedConeHull_range
    {n q : ℕ} (rays : Fin q → Fin n → ℝ) :
    finitely_generated_cone rays =
      (PointedCone.hull ℝ (Set.range rays) : Set (Fin n → ℝ)) := by
  rfl

/-- Helper for Theorem 4.42: every matrix polyhedron is the Minkowski sum of a polytope and a
finitely generated cone. -/
lemma matrixPolyhedron_eq_polytope_add_finitelyGeneratedCone
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    ∃ Q : Set (Fin n → ℝ),
      Q.IsPolytope ℝ ∧
        ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℝ,
          polyhedron_le_set A b = Q + finitely_generated_cone rays := by
  let C : Set (Fin (n + 1) → ℝ) :=
    polyhedron_le_set (Theorem442Local.homogenized_polyhedron_matrix A b) 0
  have hC_polyhedral : is_polyhedral_cone C := by
    -- The homogenized system is already homogeneous, so it is a polyhedral cone by definition.
    refine (is_polyhedral_cone_iff).2 ?_
    exact ⟨m + 1, Theorem442Local.homogenized_polyhedron_matrix A b, rfl⟩
  rcases Theorem442Local.exists_matrixCone_eq_of_isPolyhedralCone hC_polyhedral with
    ⟨k, R, hR⟩
  have hlast_nonneg : ∀ j : Fin k, 0 ≤ R (Fin.last n) j := by
    intro j
    have hj_cone :
        (fun i : Fin (n + 1) ↦ R i j) ∈ ((matrix_cone R :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) :=
      Theorem442Local.matrix_column_mem_matrix_cone R j
    have hj_hom : (fun i : Fin (n + 1) ↦ R i j) ∈ C := by
      rw [hR]
      exact hj_cone
    have hj_hom' :
        Fin.snoc (fun i : Fin n ↦ R i.castSucc j) (R (Fin.last n) j) ∈ C := by
      convert hj_hom using 1
      ext i
      cases i using Fin.lastCases with
      | last =>
          simp [Fin.snoc_last]
      | cast i =>
          simp [Fin.snoc_castSucc]
    exact
      (Theorem442Local.mem_homogenized_polyhedron_cone_iff_general A b
        (fun i : Fin n ↦ R i.castSucc j) (R (Fin.last n) j)).1 hj_hom' |>.2
  let J₁ : Type := {j : Fin k // 0 < R (Fin.last n) j}
  let J₀ : Type := {j : Fin k // R (Fin.last n) j = 0}
  let v : J₁ → Fin n → ℝ := fun a i ↦ R i.castSucc a.1 / R (Fin.last n) a.1
  let r : J₀ → Fin n → ℝ := fun b' i ↦ R i.castSucc b'.1
  let Q : Set (Fin n → ℝ) := convexHull ℝ (Set.range v)
  let q : ℕ := Fintype.card J₀
  let e : Fin q ≃ J₀ := (Fintype.equivFin J₀).symm
  let rays : Fin q → Fin n → ℝ := fun i ↦ r (e i)
  have hrange_rays : Set.range rays = Set.range r := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by simp [rays]⟩
  refine ⟨Q, ?_, q, rays, ?_⟩
  · exact ⟨Set.range v, Set.finite_range v, rfl⟩
  · ext x
    constructor
    · intro hx
      have hx_hom :
          (Fin.snoc x (1 : ℝ) : Fin (n + 1) → ℝ) ∈ C := by
        simpa [C] using (Theorem442Local.mem_homogenized_polyhedron_cone_iff A b x).2 hx
      have hx_matrix :
          (Fin.snoc x (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
            PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
        simpa [hR] using hx_hom
      have hx_slice : x ∈ Q + cone (Set.range r) := by
        simpa [Q, J₁, J₀, v, r] using
          (@Theorem442Local.mem_slice_one_matrix_cone_iff_mem_convexHull_add_cone_of_nonnegative_heights
            n k R hlast_nonneg x).1 hx_matrix
      simpa [Q, finitely_generated_cone, hrange_rays] using hx_slice
    · intro hx
      have hx_slice : x ∈ Q + cone (Set.range r) := by
        simpa [Q, finitely_generated_cone, hrange_rays] using hx
      have hx_matrix :
          (Fin.snoc x (1 : ℝ) : Fin (n + 1) → ℝ) ∈ ((matrix_cone R :
            PointedCone ℝ (Fin (n + 1) → ℝ)) : Set _) := by
        simpa [Q, J₁, J₀, v, r] using
          (@Theorem442Local.mem_slice_one_matrix_cone_iff_mem_convexHull_add_cone_of_nonnegative_heights
            n k R hlast_nonneg x).2 hx_slice
      have hx_hom :
          (Fin.snoc x (1 : ℝ) : Fin (n + 1) → ℝ) ∈ C := by
        simpa [hR] using hx_matrix
      simpa [C] using (Theorem442Local.mem_homogenized_polyhedron_cone_iff A b x).1 hx_hom

/-- Helper for Theorem 4.42: the cone generated by a finite ray family is closed. -/
lemma isClosed_pointedCone_hull_finset
    {n : ℕ} (s : Finset (Fin n → ℝ)) :
    IsClosed ((PointedCone.hull ℝ (s : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  let C : PointedCone ℝ (Fin n → ℝ) := PointedCone.hull ℝ (s : Set (Fin n → ℝ))
  have hC_fg : C.FG := by
    -- A cone hull over a finite set is finitely generated by construction.
    simpa [C] using Submodule.fg_span (Finset.finite_toSet s)
  have hC_polyhedral : is_polyhedral_cone (C : Set (Fin n → ℝ)) := by
    -- Convert finite generation to the local polyhedral-cone interface.
    exact (Theorem442Local.isFinitelyGeneratedCone_iff_isPolyhedralCone).mp hC_fg
  rcases hC_polyhedral with ⟨K, hK_dualfg, hK_eq⟩
  rcases hK_dualfg with ⟨t, ht⟩
  have hK_closed : IsClosed (K : Set (Fin n → ℝ)) := by
    -- A cone that is the dual of a finite set is closed by the dual-cone topology API.
    have hdual_closed :
        IsClosed (PointedCone.dual (dotProductBilin ℝ ℝ) (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
      PointedCone.isClosed_dual (fun x ↦ by fun_prop)
    simpa [ht] using
      hdual_closed
  simpa [C] using hK_eq ▸ hK_closed

/-- Helper for Theorem 4.42: the global vertex hull plus global ray cone is closed. -/
lemma isClosed_convexHull_biUnion_add_coneHull
    {n k : ℕ}
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

/-- Helper for Theorem 4.42: the closure of the convex hull of a nonempty finite union of
polyhedra equals the global vertex hull plus the global ray cone. -/
theorem closure_convexHull_iUnion_polyhedra_eq_convexHull_biUnion_add_coneHull
    {n k : ℕ}
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
    -- Reduce the easy inclusion to closedness of the global sum.
    have hClosed : IsClosed (Q + C) := by
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
    -- Reduce both global pieces to indexed source data and use the source epsilon-approximant.
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
      have hscaled := mul_le_mul_of_nonneg_left hη_le hratio_nonneg
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
          I hI hcoeff_nonneg hcoeff_sum hI_nonempty hsmall
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
          I hI hcoeff_nonneg hη_pos
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

/-- Helper for Theorem 4.42: the recession cone of a finite convex hull plus a finite ray hull is
exactly that ray hull. -/
lemma recessionCone_convexHull_add_pointedConeHull_finset_local
    {n : ℕ}
    (s t : Finset (Fin n → ℝ))
    (hs : s.Nonempty) :
    recessionCone
        (convexHull ℝ (s : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) =
      (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  let K : Set (Fin n → ℝ) := convexHull ℝ (s : Set (Fin n → ℝ))
  let C : Set (Fin n → ℝ) := (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))
  have hK_bounded : Bornology.IsBounded K := by
    dsimp [K]
    exact (isBounded_convexHull).2 (Finset.finite_toSet s).isBounded
  have hC_closed : IsClosed C := by
    simpa [C] using isClosed_pointedCone_hull_finset t
  rcases hs with ⟨x0, hx0s⟩
  have hx0K : x0 ∈ K := by
    exact subset_convexHull ℝ (s : Set (Fin n → ℝ)) hx0s
  have hzeroC : (0 : Fin n → ℝ) ∈ C := by
    exact Submodule.zero_mem _
  have hx0KC : x0 ∈ K + C := by
    exact Set.mem_add.mpr ⟨x0, hx0K, 0, hzeroC, by simp⟩
  ext r
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    have hdecomp :
        ∀ l : ℕ,
          ∃ y z,
            y ∈ K ∧ z ∈ C ∧ y + z = x0 + (((l : ℝ) + 1) • r) := by
      intro l
      have hxl : x0 + (((l : ℝ) + 1) • r) ∈ K + C := by
        exact hr hx0KC (((l : ℝ) + 1)) (by positivity)
      rcases Set.mem_add.mp hxl with ⟨y, hy, z, hz, hsum⟩
      exact ⟨y, z, hy, hz, hsum⟩
    choose y z hyK hzC hsum using hdecomp
    let δ : ℕ → ℝ := fun l ↦ (((l : ℝ) + 1)⁻¹)
    let u : ℕ → Fin n → ℝ := fun l ↦ δ l • z l
    have hδ_nonneg : ∀ l : ℕ, 0 ≤ δ l := by
      intro l
      dsimp [δ]
      positivity
    have hu_mem : ∀ l : ℕ, u l ∈ C := by
      intro l
      exact IsCone.smul_mem' (hzC l) (hδ_nonneg l)
    have hu_eq :
        ∀ l : ℕ, u l = r + δ l • (x0 - y l) := by
      intro l
      have hscale_ne : ((l : ℝ) + 1) ≠ 0 := by positivity
      have hz_eq : z l = x0 + (((l : ℝ) + 1) • r) - y l := by
        exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum l)
      calc
        u l = δ l • (x0 + (((l : ℝ) + 1) • r) - y l) := by
          dsimp [u]
          rw [hz_eq]
        _ = δ l • (x0 + (((l : ℝ) + 1) • r)) - δ l • y l := by
              rw [smul_sub]
        _ = (δ l • x0 + δ l • (((l : ℝ) + 1) • r)) - δ l • y l := by
              rw [smul_add]
        _ = (δ l • x0 + r) - δ l • y l := by
              congr 1
              rw [smul_smul, inv_mul_cancel₀ hscale_ne, one_smul]
        _ = r + (δ l • x0 - δ l • y l) := by
              simp [sub_eq_add_neg, add_assoc, add_comm]
        _ = r + δ l • (x0 - y l) := by
              rw [smul_sub]
    have hdiff_bounded : Bornology.IsBounded (Set.range fun l : ℕ ↦ x0 - y l) := by
      refine
        (isBounded_sub
          (show Bornology.IsBounded ({x0} : Set (Fin n → ℝ)) from Bornology.isBounded_singleton)
          hK_bounded).subset ?_
      intro v hv
      rcases hv with ⟨l, rfl⟩
      exact Set.sub_mem_sub (by simp) (hyK l)
    have hnorm_bounded :
        Filter.IsBoundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ)
          (norm ∘ fun l : ℕ ↦ x0 - y l) := by
      obtain ⟨R, hR⟩ := hdiff_bounded.subset_closedBall (0 : Fin n → ℝ)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, ?_⟩
      intro l
      have hmem : x0 - y l ∈ Set.range (fun j : ℕ ↦ x0 - y j) := Set.mem_range_self l
      have hball : x0 - y l ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hmem
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hδ_tendsto : Filter.Tendsto δ (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [δ, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun l : ℕ ↦ 1 / ((l : ℝ) + 1)) (Filter.atTop : Filter ℕ) (nhds 0))
    have herr_tendsto :
        Filter.Tendsto (fun l : ℕ ↦ δ l • (x0 - y l))
          (Filter.atTop : Filter ℕ) (nhds 0) :=
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hδ_tendsto hnorm_bounded
    have hu_tendsto : Filter.Tendsto u (Filter.atTop : Filter ℕ) (nhds r) := by
      have htarget :
          Filter.Tendsto (fun l : ℕ ↦ r + δ l • (x0 - y l))
            (Filter.atTop : Filter ℕ) (nhds r) := by
        simpa using (tendsto_const_nhds.add herr_tendsto)
      refine Filter.Tendsto.congr' ?_ htarget
      exact Filter.Eventually.of_forall fun l ↦ (hu_eq l).symm
    exact hC_closed.mem_of_tendsto hu_tendsto (Filter.Eventually.of_forall hu_mem)
  · intro hr
    rw [mem_recessionCone_iff]
    intro x hx a ha
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
    have hz' : z + a • r ∈ C := by
      exact add_mem hz (IsCone.smul_mem' hr ha)
    exact Set.mem_add.mpr
      ⟨y, hy, z + a • r, hz', by
        simpa [C, add_assoc] using congrArg (fun w ↦ w + a • r) hsum⟩

/-- Helper for Theorem 4.42: the recession cone of a nonempty matrix polyhedron is the
homogeneous solution set `polyhedron_le_set A 0`. -/
theorem polyhedron_recessionCone_eq_homogeneous_solution_set
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    recessionCone (polyhedron_le_set A b) = {r : Fin n → ℝ | A *ᵥ r ≤ 0} := by
  ext r
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    rcases h_nonempty with ⟨x₀, hx₀⟩
    -- Test the recession condition at one feasible base point to force every row nonpositive.
    change A *ᵥ r ≤ 0
    intro i
    by_contra h_not_le
    have hpos : 0 < (A *ᵥ r) i := lt_of_not_ge h_not_le
    let a : ℝ := (b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i
    have hx₀_le : (A *ᵥ x₀) i ≤ b i := hx₀ i
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      refine div_nonneg ?_ hpos.le
      linarith
    have hxa : x₀ + a • r ∈ polyhedron_le_set A b := hr hx₀ a ha_nonneg
    have hrow : (A *ᵥ x₀) i + a * (A *ᵥ r) i ≤ b i := by
      simpa [polyhedron_le_set, Matrix.mulVec_add, Matrix.mulVec_smul] using hxa i
    have ha_mul : a * (A *ᵥ r) i = b i - (A *ᵥ x₀) i + 1 := by
      dsimp [a]
      field_simp [hpos.ne']
    linarith
  · intro hr
    rw [mem_recessionCone_iff]
    intro x hx a ha
    -- Homogeneous feasibility is preserved under translation by a nonnegative multiple of `r`.
    change A *ᵥ (x + a • r) ≤ b
    intro i
    have hx_le : (A *ᵥ x) i ≤ b i := hx i
    have hr_le : (A *ᵥ r) i ≤ 0 := hr i
    have hmul : a * (A *ᵥ r) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hr_le
    have hsum : (A *ᵥ x) i + a * (A *ᵥ r) i ≤ b i := by
      linarith
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hsum

/-- Helper for Theorem 4.42: for a nonempty matrix polyhedron, the recession cone matches the
prescribed ray hull once the homogeneous system is identified with that hull. -/
lemma polyhedron_recessionCone_eq_givenRayHull
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (R : Fin k → Finset (Fin n → ℝ))
    (hR :
      ∀ i : Fin k,
        polyhedron_le_set (A i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)))
    {i : Fin k}
    (hPi : (polyhedron_le_set (A i) (b i)).Nonempty) :
    recessionCone (polyhedron_le_set (A i) (b i)) =
      (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
        Set (Fin n → ℝ)) := by
  -- Route correction: normalize the recession cone through the homogeneous system first, then
  -- rewrite that homogeneous system via the prescribed ray family `R i`.
  calc
    recessionCone (polyhedron_le_set (A i) (b i))
        = polyhedron_le_set (A i) 0 := by
            -- The nonempty matrix polyhedron and its homogeneous system have the same recession
            -- directions.
            simpa using
              polyhedron_recessionCone_eq_homogeneous_solution_set
                (A i) (b i) hPi
    _ = (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
          Set (Fin n → ℝ)) := hR i

/-- Helper for Theorem 4.42: every nonempty matrix polyhedron admits a finite vertex family whose
Minkowski-Weyl decomposition uses the prescribed ray family `R i`. -/
lemma matrixPolyhedron_eq_convexHull_add_givenRayHull_of_nonempty
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (R : Fin k → Finset (Fin n → ℝ))
    (hR :
      ∀ i : Fin k,
        polyhedron_le_set (A i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)))
    {i : Fin k}
    (hPi : (polyhedron_le_set (A i) (b i)).Nonempty) :
    ∃ Vi : Finset (Fin n → ℝ),
      polyhedron_le_set (A i) (b i) =
        convexHull ℝ (Vi : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
  rcases matrixPolyhedron_eq_polytope_add_finitelyGeneratedCone (A i) (b i) with
    ⟨Q, hQ_polytope, q, rays, h_repr⟩
  rcases exists_convexHull_range_eq_of_isPolytope hQ_polytope with
    ⟨p, vertices, hQ_vertices⟩
  let Vi : Finset (Fin n → ℝ) := Finset.univ.image vertices
  let t : Finset (Fin n → ℝ) := Finset.univ.image rays
  have hrepr_finset :
      polyhedron_le_set (A i) (b i) =
        convexHull ℝ (Vi : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- Rewrite the generic Chapter 3.13 decomposition through finite vertex and ray families.
    calc
      polyhedron_le_set (A i) (b i) = Q + finitely_generated_cone rays := h_repr
      _ = convexHull ℝ (Vi : Set (Fin n → ℝ)) + finitely_generated_cone rays := by
            rw [hQ_vertices]
            rw [show Set.range vertices = (Vi : Set (Fin n → ℝ)) by
              rw [range_eq_image_univ vertices]]
      _ = convexHull ℝ (Vi : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Set.range rays) : Set (Fin n → ℝ)) := by
              rw [finitely_generated_cone_eq_pointedConeHull_range rays]
      _ = convexHull ℝ (Vi : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
              rw [range_eq_image_univ rays]
  have hVi_nonempty : Vi.Nonempty := by
    -- Nonemptiness of the original polyhedron forces nonemptiness of the polytope part.
    rcases hPi with ⟨x, hx⟩
    rw [hrepr_finset] at hx
    rcases hx with ⟨v, hv, r, hr, hvr⟩
    have hv_nonempty : (convexHull ℝ (Vi : Set (Fin n → ℝ))).Nonempty := ⟨v, hv⟩
    by_contra hVi_empty
    have hconv_empty : convexHull ℝ (Vi : Set (Fin n → ℝ)) = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty.mp hVi_empty, convexHull_empty]
    exact hv_nonempty.ne_empty hconv_empty
  have hrec_t :
      recessionCone (polyhedron_le_set (A i) (b i)) =
        (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- The finite convex-hull plus finite ray-hull presentation determines the recession cone.
    calc
      recessionCone (polyhedron_le_set (A i) (b i))
          = recessionCone
              (convexHull ℝ (Vi : Set (Fin n → ℝ)) +
                (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
                  rw [hrepr_finset]
      _ = (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            exact recessionCone_convexHull_add_pointedConeHull_finset_local Vi t hVi_nonempty
  have hcone_eq :
      (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- Compare the two cone presentations through the common recession cone of the polyhedron.
    calc
      (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))
          = recessionCone (polyhedron_le_set (A i) (b i)) := by
              symm
              exact hrec_t
      _ = (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            exact polyhedron_recessionCone_eq_givenRayHull m A b R hR hPi
  refine ⟨Vi, ?_⟩
  -- Replace the generic finite ray family by the prescribed ray hull after the recession-cone
  -- comparison.
  calc
    polyhedron_le_set (A i) (b i) = convexHull ℝ (Vi : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := hrepr_finset
    _ = convexHull ℝ (Vi : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
          rw [hcone_eq]

/-- Helper for Theorem 4.42: equality of the global ray cone and the active ray cone is exactly
the source theorem's local-cone containment condition. -/
lemma globalRayHull_eq_activeRayHull_iff_localConeSubset
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (R : Fin k → Finset (Fin n → ℝ))
    (hR :
      ∀ i : Fin k,
        polyhedron_le_set (A i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ))) :
    (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) =
        (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) ↔
      ∀ j : Fin k,
        polyhedron_le_set (A j) 0 ⊆
          (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) := by
  constructor
  · intro hEq j
    -- Rewrite the local recession cone via `hR` and then use the global-to-local inclusion.
    rw [hR j]
    exact hEq ▸ local_ray_hull_subset_global_ray_hull R j
  · intro hSubset
    apply le_antisymm
    · -- Every global generator lies in some local cone, which is assumed active.
      exact Submodule.span_le.2 <| by
        intro x hx
        rcases hx with ⟨i, hxi⟩
        have hxCone : x ∈ polyhedron_le_set (A i) 0 := by
          rw [hR i]
          exact Submodule.subset_span hxi
        exact hSubset i hxCone
    · -- Every active ray is already one of the global rays.
      exact Submodule.span_le.2 <| by
        intro x hx
        rcases (mem_balas_nonempty_family_iff m A b R x).1 hx with ⟨i, -, hxi⟩
        exact Submodule.subset_span ⟨i, hxi⟩

/-- Helper for Theorem 4.42: the recession cone of a finite convex hull plus a finite generated
cone is exactly that cone. -/
lemma recessionCone_convexHull_add_pointedConeHull_finset
    {n : ℕ}
    (s t : Finset (Fin n → ℝ))
    (hs : s.Nonempty) :
    recessionCone
        (convexHull ℝ (s : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) =
      (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  let K : Set (Fin n → ℝ) := convexHull ℝ (s : Set (Fin n → ℝ))
  let C : Set (Fin n → ℝ) := (PointedCone.hull ℝ (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ))
  have hK_bounded : Bornology.IsBounded K := by
    -- The convex hull of finitely many points is bounded.
    dsimp [K]
    exact (isBounded_convexHull).2 (Finset.finite_toSet s).isBounded
  have hC_closed : IsClosed C := by
    -- The finite ray cone is closed by the earlier Chapter 4.9 helper.
    simpa [C] using isClosed_pointedCone_hull_finset t
  rcases hs with ⟨x0, hx0s⟩
  have hx0K : x0 ∈ K := by
    -- Any vertex of the finite family lies in its convex hull.
    exact subset_convexHull ℝ (s : Set (Fin n → ℝ)) hx0s
  have hzeroC : (0 : Fin n → ℝ) ∈ C := by
    exact Submodule.zero_mem _
  have hx0KC : x0 ∈ K + C := by
    -- Use the zero cone element to lift the chosen vertex into the Minkowski sum.
    exact Set.mem_add.mpr ⟨x0, hx0K, 0, hzeroC, by simp⟩
  ext r
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    -- Route correction: normalize `x0 + (n+1) • r`, divide the cone part by `n+1`, and use
    -- closedness of the cone to pass to the limit.
    have hdecomp :
        ∀ l : ℕ,
          ∃ y z,
            y ∈ K ∧ z ∈ C ∧ y + z = x0 + (((l : ℝ) + 1) • r) := by
      intro l
      have hxl : x0 + (((l : ℝ) + 1) • r) ∈ K + C := by
        exact hr hx0KC (((l : ℝ) + 1)) (by positivity)
      rcases Set.mem_add.mp hxl with ⟨y, hy, z, hz, hsum⟩
      exact ⟨y, z, hy, hz, hsum⟩
    choose y z hyK hzC hsum using hdecomp
    let δ : ℕ → ℝ := fun l ↦ (((l : ℝ) + 1)⁻¹)
    let u : ℕ → Fin n → ℝ := fun l ↦ δ l • z l
    have hδ_nonneg : ∀ l : ℕ, 0 ≤ δ l := by
      intro l
      dsimp [δ]
      positivity
    have hu_mem : ∀ l : ℕ, u l ∈ C := by
      intro l
      -- Positive scalar multiples of cone elements stay in the cone.
      exact IsCone.smul_mem' (hzC l) (hδ_nonneg l)
    have hu_eq :
        ∀ l : ℕ, u l = r + δ l • (x0 - y l) := by
      intro l
      have hscale_ne : ((l : ℝ) + 1) ≠ 0 := by positivity
      have hz_eq : z l = x0 + (((l : ℝ) + 1) • r) - y l := by
        exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum l)
      calc
        u l = δ l • (x0 + (((l : ℝ) + 1) • r) - y l) := by
          dsimp [u]
          rw [hz_eq]
        _ = δ l • (x0 + (((l : ℝ) + 1) • r)) - δ l • y l := by
              rw [smul_sub]
        _ = (δ l • x0 + δ l • (((l : ℝ) + 1) • r)) - δ l • y l := by
              rw [smul_add]
        _ = (δ l • x0 + r) - δ l • y l := by
              congr 1
              rw [smul_smul, inv_mul_cancel₀ hscale_ne, one_smul]
        _ = r + (δ l • x0 - δ l • y l) := by
              simp [sub_eq_add_neg, add_assoc, add_comm]
        _ = r + δ l • (x0 - y l) := by
              rw [smul_sub]
    have hdiff_bounded : Bornology.IsBounded (Set.range fun l : ℕ ↦ x0 - y l) := by
      -- The normalized error terms stay in the difference of a singleton and a bounded set.
      refine
        (isBounded_sub
          (show Bornology.IsBounded ({x0} : Set (Fin n → ℝ)) from Bornology.isBounded_singleton)
          hK_bounded).subset ?_
      intro v hv
      rcases hv with ⟨l, rfl⟩
      exact Set.sub_mem_sub (by simp) (hyK l)
    have hnorm_bounded :
        Filter.IsBoundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ)
          (norm ∘ fun l : ℕ ↦ x0 - y l) := by
      obtain ⟨R, hR⟩ := hdiff_bounded.subset_closedBall (0 : Fin n → ℝ)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, ?_⟩
      intro l
      have hmem : x0 - y l ∈ Set.range (fun j : ℕ ↦ x0 - y j) := Set.mem_range_self l
      have hball : x0 - y l ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hmem
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hδ_tendsto : Filter.Tendsto δ (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [δ, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun l : ℕ ↦ 1 / ((l : ℝ) + 1)) (Filter.atTop : Filter ℕ) (nhds 0))
    have herr_tendsto :
        Filter.Tendsto (fun l : ℕ ↦ δ l • (x0 - y l))
          (Filter.atTop : Filter ℕ) (nhds 0) :=
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hδ_tendsto hnorm_bounded
    have hu_tendsto : Filter.Tendsto u (Filter.atTop : Filter ℕ) (nhds r) := by
      have htarget :
          Filter.Tendsto (fun l : ℕ ↦ r + δ l • (x0 - y l))
            (Filter.atTop : Filter ℕ) (nhds r) := by
        simpa using (tendsto_const_nhds.add herr_tendsto)
      refine Filter.Tendsto.congr' ?_ htarget
      exact Filter.Eventually.of_forall fun l ↦ (hu_eq l).symm
    exact hC_closed.mem_of_tendsto hu_tendsto (Filter.Eventually.of_forall hu_mem)
  · intro hr
    rw [mem_recessionCone_iff]
    intro x hx a ha
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
    have hz' : z + a • r ∈ C := by
      -- Keep the bounded part fixed and absorb the translated direction into the cone summand.
      exact add_mem hz (IsCone.smul_mem' hr ha)
    exact Set.mem_add.mpr
      ⟨y, hy, z + a • r, hz', by
        simpa [C, add_assoc] using congrArg (fun w ↦ w + a • r) hsum⟩

/-- Theorem 4.42 (Balas [24,26]). Let `Pᵢ = {x ∈ ℝ^n | Aᵢ x ≤ bⁱ}` be `k` polyhedra such that
`⋃ i, Pᵢ` is nonempty, let `Y` be the lifted Balas polyhedron from Theorem 4.39, let
`Cᵢ = {x | Aᵢ x ≤ 0}`, and let each `Rⁱ` be a finite ray family with `Cᵢ = cone(Rⁱ)`. Then the
closure of the convex hull of `⋃ i, Pᵢ` is the `x`-projection of `Y` if and only if every
`Cⱼ` is contained in the cone generated by the ray families coming from the nonempty `Pᵢ`. -/
theorem closure_convexHull_iUnion_matrix_polyhedra_eq_balas_x_projection_iff
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (R : Fin k → Finset (Fin n → ℝ))
    (h_nonempty : (⋃ i : Fin k, polyhedron_le_set (A i) (b i)).Nonempty)
    (hR :
      ∀ i : Fin k,
        polyhedron_le_set (A i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ))) :
    closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) =
        balas_x_projection m A b ↔
      ∀ j : Fin k,
        polyhedron_le_set (A j) 0 ⊆
          (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) := by
  classical
  let V : Fin k → Finset (Fin n → ℝ) := fun i ↦
    if hPi : (polyhedron_le_set (A i) (b i)).Nonempty then
      Classical.choose
        (matrixPolyhedron_eq_convexHull_add_givenRayHull_of_nonempty m A b R hR hPi)
    else ∅
  have hV :
      ∀ i : Fin k,
        polyhedron_le_set (A i) (b i) ≠ ∅ →
          polyhedron_le_set (A i) (b i) =
            convexHull ℝ (V i : Set (Fin n → ℝ)) +
              (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) :
                Set (Fin n → ℝ)) := by
    intro i hPi
    have hPi_nonempty : (polyhedron_le_set (A i) (b i)).Nonempty := by
      by_contra hEmpty
      exact hPi (Set.not_nonempty_iff_eq_empty.mp hEmpty)
    -- Unfold the chosen witness only on the nonempty branch that the theorem may use.
    simpa [V, hPi_nonempty] using
      Classical.choose_spec
        (matrixPolyhedron_eq_convexHull_add_givenRayHull_of_nonempty m A b R hR hPi_nonempty)
  let t : Finset (Fin k) := Finset.univ.filter fun i ↦ (polyhedron_le_set (A i) (b i)).Nonempty
  have ht_nonempty : t.Nonempty := by
    -- The source hypothesis gives one active polyhedron, hence one active index in `t`.
    rcases h_nonempty with ⟨x, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact ⟨i, Finset.mem_filter.2 ⟨by simp, ⟨x, hxi⟩⟩⟩
  let e : Fin t.card ≃ ↥t := (Finset.equivFin t).symm
  let Pactive : Fin t.card → Set (Fin n → ℝ) := fun j ↦ polyhedron_le_set (A (e j).1) (b (e j).1)
  let Vactive : Fin t.card → Finset (Fin n → ℝ) := fun j ↦ V (e j).1
  let Ractive : Fin t.card → Finset (Fin n → ℝ) := fun j ↦ R (e j).1
  have hPactive_nonempty : ∀ j : Fin t.card, (Pactive j).Nonempty := by
    intro j
    simpa [Pactive] using (Finset.mem_filter.1 (e j).2).2
  have hPactive_repr :
      ∀ j : Fin t.card,
        Pactive j = convexHull ℝ (Vactive j : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (Ractive j : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
    intro j
    -- Every active polyhedron uses the chosen vertex family together with its prescribed rays.
    simpa [Pactive, Vactive, Ractive] using
      hV (e j).1 (hPactive_nonempty j).ne_empty
  have hUnion_active :
      (⋃ j : Fin t.card, Pactive j) = ⋃ i : Fin k, polyhedron_le_set (A i) (b i) := by
    -- Reindex the active subfamily along the equivalence `e`.
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
      exact Set.mem_iUnion.2 ⟨(e j).1, by simpa [Pactive] using hxj⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      have hi : i ∈ t := Finset.mem_filter.2 ⟨by simp, ⟨x, hxi⟩⟩
      have hidx : (e (e.symm ⟨i, hi⟩)).1 = i := by
        simp
      exact Set.mem_iUnion.2 ⟨e.symm ⟨i, hi⟩, by
        change x ∈ polyhedron_le_set (A ((e (e.symm ⟨i, hi⟩)).1)) (b ((e (e.symm ⟨i, hi⟩)).1))
        rw [hidx]
        exact hxi⟩
  have hVactive_eq :
      (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) = balas_nonempty_family m A b V := by
    -- The reindexed active vertex biunion is exactly Balas' nonempty-family owner.
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.1 hx with ⟨j, -, hxj⟩
      rw [mem_balas_nonempty_family_iff]
      exact ⟨(e j).1, (hPactive_nonempty j).ne_empty, by simpa [Vactive] using hxj⟩
    · intro hx
      rcases (mem_balas_nonempty_family_iff m A b V x).1 hx with ⟨i, hPi, hxi⟩
      have hPi_nonempty : (polyhedron_le_set (A i) (b i)).Nonempty := by
        by_contra hEmpty
        exact hPi (Set.not_nonempty_iff_eq_empty.mp hEmpty)
      have hi : i ∈ t := Finset.mem_filter.2 ⟨by simp, hPi_nonempty⟩
      exact Finset.mem_biUnion.2 ⟨e.symm ⟨i, hi⟩, by simp, by simpa [Vactive] using hxi⟩
  have hRactive_eq :
      (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) = balas_nonempty_family m A b R := by
    -- The same reindexing identifies the active ray family with Balas' guarded-ray owner.
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.1 hx with ⟨j, -, hxj⟩
      rw [mem_balas_nonempty_family_iff]
      exact ⟨(e j).1, (hPactive_nonempty j).ne_empty, by simpa [Ractive] using hxj⟩
    · intro hx
      rcases (mem_balas_nonempty_family_iff m A b R x).1 hx with ⟨i, hPi, hxi⟩
      have hPi_nonempty : (polyhedron_le_set (A i) (b i)).Nonempty := by
        by_contra hEmpty
        exact hPi (Set.not_nonempty_iff_eq_empty.mp hEmpty)
      have hi : i ∈ t := Finset.mem_filter.2 ⟨by simp, hPi_nonempty⟩
      exact Finset.mem_biUnion.2 ⟨e.symm ⟨i, hi⟩, by simp, by simpa [Ractive] using hxi⟩
  have hRayFamily_eq :
      balas_ray_family R = (Finset.univ.biUnion R : Set (Fin n → ℝ)) := by
    -- The global Balas ray family is just the finite biunion of all local ray families.
    ext x
    constructor
    · rintro ⟨i, hxi⟩
      exact Finset.mem_biUnion.2 ⟨i, by simp, hxi⟩
    · intro hx
      rcases Finset.mem_biUnion.1 hx with ⟨i, -, hxi⟩
      exact ⟨i, hxi⟩
  have hclosure_finset :
      closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) =
        convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
    -- Lemma 4.41 computes the closure after restricting to the nonempty subfamily.
    calc
      closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) =
          closure (convexHull ℝ (⋃ j : Fin t.card, Pactive j)) := by
            rw [hUnion_active]
      _ = convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
            exact
              closure_convexHull_iUnion_polyhedra_eq_convexHull_biUnion_add_coneHull
                Pactive hPactive_nonempty Vactive Ractive hPactive_repr
  have hproj_finset :
      balas_x_projection m A b =
        convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
    -- Theorem 4.39 gives the same active vertex hull, but keeps all local ray families.
    calc
      balas_x_projection m A b =
          convexHull ℝ (balas_nonempty_family m A b V) +
            (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) := by
              simpa [balas_union_polyhedron] using
                (balas_union_polyhedron_eq_x_projection m A b V R hR hV).symm
      _ = convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) := by
              rw [← hVactive_eq]
      _ = convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
              rw [hRayFamily_eq]
  have hVertex_nonempty : (Finset.univ.biUnion Vactive).Nonempty := by
    let j0 : Fin t.card := ⟨0, Finset.card_pos.mpr ht_nonempty⟩
    rcases hPactive_nonempty j0 with ⟨x, hx⟩
    rw [hPactive_repr j0] at hx
    rcases hx with ⟨v, hv, r, hr, _⟩
    have hVj0_nonempty : (Vactive j0).Nonempty := by
      by_contra hEmpty
      have hHullEmpty : convexHull ℝ (Vactive j0 : Set (Fin n → ℝ)) = ∅ := by
        simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty]
      rw [hHullEmpty] at hv
      simpa using hv
    rcases hVj0_nonempty with ⟨v0, hv0⟩
    exact ⟨v0, Finset.mem_biUnion.2 ⟨j0, by simp, hv0⟩⟩
  constructor
  · intro hEq
    have hnormalized :
        convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) =
          convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
      -- Normalize both sides of the target equality to the same finite-vertex presentation.
      calc
        convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) =
            closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) := by
              symm
              exact hclosure_finset
        _ = balas_x_projection m A b := hEq
        _ = convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
              (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
                Set (Fin n → ℝ)) := hproj_finset
    have hcone_finset :
        (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) =
          (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
      -- Apply `recessionCone` after both sides are in the common 'finite hull + finite cone' form.
      calc
        (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) =
            recessionCone
              (convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
                (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
                  Set (Fin n → ℝ))) := by
                    symm
                    exact recessionCone_convexHull_add_pointedConeHull_finset
                      (Finset.univ.biUnion Vactive) (Finset.univ.biUnion Ractive) hVertex_nonempty
        _ =
            recessionCone
              (convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
                (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
                  Set (Fin n → ℝ))) := by
                    exact congrArg recessionCone hnormalized
        _ = (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
                    exact recessionCone_convexHull_add_pointedConeHull_finset
                      (Finset.univ.biUnion Vactive) (Finset.univ.biUnion R) hVertex_nonempty
    have hcone :
        (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) =
          (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) := by
      -- Translate the normalized cone equality back to the Balas owner names.
      calc
        (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) =
            (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
                rw [hRayFamily_eq]
        _ = (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := hcone_finset.symm
        _ = (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) := by
              rw [hRactive_eq]
    exact
      (globalRayHull_eq_activeRayHull_iff_localConeSubset m A b R hR).1 hcone
  · intro hSubset
    have hcone :
        (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) =
          (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) :=
      (globalRayHull_eq_activeRayHull_iff_localConeSubset m A b R hR).2 hSubset
    have hcone_finset :
        (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) =
          (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
      -- Rewrite the cone-equality criterion into the normalized finite-biunion language.
      calc
        (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) =
          (PointedCone.hull ℝ (balas_nonempty_family m A b R) : Set (Fin n → ℝ)) := by
            rw [hRactive_eq]
        _ = (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) := hcone.symm
        _ = (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
              rw [hRayFamily_eq]
    -- With the ray cones identified, Theorem 4.39 and Lemma 4.41 give the same normalized set.
    calc
      closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) =
          convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion Ractive : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := hclosure_finset
      _ = convexHull ℝ (Finset.univ.biUnion Vactive : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (Finset.univ.biUnion R : Set (Fin n → ℝ)) :
              Set (Fin n → ℝ)) := by
            rw [hcone_finset]
      _ = balas_x_projection m A b := hproj_finset.symm

end Theorem442
