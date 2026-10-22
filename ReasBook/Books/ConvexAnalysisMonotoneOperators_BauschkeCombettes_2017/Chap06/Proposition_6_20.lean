/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_19

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Pointwise

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The intersection of the sets preceding the `(i + 2)`-nd term of a finite family. -/
def previousIntersection (n : ℕ) (C : Fin (n + 2) → Set H) (i : Fin (n + 1)) : Set H :=
  ⋂ j : Fin i.1.succ, C (Fin.castLT j (Nat.lt_trans j.2 i.succ.isLt))

/-- The successive difference `C_{i+2} - ⋂_{j=1}^{i+1} C_j` from Proposition 6,20. -/
def successiveDifference (n : ℕ) (C : Fin (n + 2) → Set H) (i : Fin (n + 1)) : Set H :=
  C i.succ - previousIntersection n C i

/-- The intersection of the strong relative interiors of the successive differences. -/
def successiveStrongRelativeInteriorIntersection
    (n : ℕ) (C : Fin (n + 2) → Set H) : Set H :=
  ⋂ i : Fin (n + 1), sri (successiveDifference n C i)

/-- The four regularity hypotheses appearing in Proposition 6,20. -/
def successiveDifferenceRegularity (n : ℕ) (C : Fin (n + 2) → Set H) : Prop :=
  (∀ i : Fin (n + 1),
      ∃ V : Submodule ℝ H,
        IsClosed (V : Set H) ∧ successiveDifference n C i = (V : Set H)) ∨
    (((∀ i : Fin (n + 2), ∃ V : Submodule ℝ H, C i = (V : Set H)) ∧
        ∀ i : Fin (n + 1), IsClosed (C i.succ + previousIntersection n C i)) ∨
      ((C (Fin.last (n + 1)) ∩ ⋂ i : Fin (n + 1), interior (C (Fin.castSucc i))).Nonempty ∨
        (FiniteDimensional ℝ H ∧ (⋂ i : Fin (n + 2), ri (C i)).Nonempty)))

/-- Helper for Proposition 6,20: the first prefix intersection is just the first set. -/
private theorem previousIntersection_zero (n : ℕ) (C : Fin (n + 2) → Set H) :
    previousIntersection n C 0 = C 0 := by
  -- The `Fin 1` intersection contains only the index `0`.
  ext x
  constructor
  · intro hx
    exact Set.mem_iInter.mp hx 0
  · intro hx
    rw [previousIntersection, Set.mem_iInter]
    intro j
    have hj : j = 0 := Fin.eq_zero j
    simpa [hj] using hx

/-- Helper for Proposition 6,20: each longer prefix intersection is obtained by adjoining the next
set to the previous prefix. -/
private theorem previousIntersection_succ (n : ℕ) (C : Fin (n + 2) → Set H) (i : Fin n) :
    previousIntersection n C i.succ =
      previousIntersection n C i.castSucc ∩ C i.castSucc.succ := by
  -- Split the larger finite intersection into the old prefix and the new final factor.
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [previousIntersection, Set.mem_iInter]
      intro j
      exact Set.mem_iInter.mp hx j.castSucc
    · simpa [previousIntersection] using Set.mem_iInter.mp hx (Fin.last _)
  · rintro ⟨hxprev, hxi⟩
    rw [previousIntersection, Set.mem_iInter] at hxprev ⊢
    intro j
    rcases j.eq_castSucc_or_eq_last with ⟨k, rfl⟩ | rfl
    · exact hxprev k
    · simpa using hxi

/-- Helper for Proposition 6,20: every prefix intersection stays convex when the whole family is
convex. -/
private theorem previousIntersection_convex (n : ℕ) (C : Fin (n + 2) → Set H)
    (hC_convex : ∀ k, Convex ℝ (C k)) (i : Fin (n + 1)) :
    Convex ℝ (previousIntersection n C i) := by
  -- Convexity is preserved under finite intersections.
  rw [previousIntersection]
  exact convex_iInter fun j => hC_convex _

/-- Helper for Proposition 6,20: in the subspace branch, each prefix intersection is itself the
underlying set of a submodule. -/
private theorem previousIntersection_eq_iInf_submodule (n : ℕ) (C : Fin (n + 2) → Set H)
    (hsub : ∀ k : Fin (n + 2), ∃ V : Submodule ℝ H, C k = (V : Set H))
    (i : Fin (n + 1)) :
    ∃ V : Submodule ℝ H, previousIntersection n C i = (V : Set H) := by
  classical
  choose V hV using hsub
  -- The prefix intersection is the infimum of the corresponding family of submodules.
  refine ⟨⨅ j : Fin i.1.succ, V (Fin.castLT j (Nat.lt_trans j.2 i.succ.isLt)), ?_⟩
  rw [previousIntersection]
  simp [hV, Submodule.coe_iInf]

/-- Helper for Proposition 6,20: a point lying in the interior of every earlier set also lies in
the interior of each prefix intersection. -/
private theorem mem_interior_previousIntersection_of_common_interior (n : ℕ)
    (C : Fin (n + 2) → Set H) {x : H}
    (hx : x ∈ ⋂ j : Fin (n + 1), interior (C (Fin.castSucc j))) (i : Fin (n + 1)) :
    x ∈ interior (previousIntersection n C i) := by
  -- Rewrite the prefix interior as the interior of a finite intersection and read off each factor.
  rw [previousIntersection, interior_iInter_of_finite, Set.mem_iInter]
  intro j
  have hxj :=
    Set.mem_iInter.mp hx (Fin.castLT j (Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)))
  simpa using hxj

/-- Helper for Proposition 6,20: in finite dimension, common relative-interior membership passes to
every prefix intersection. -/
private theorem mem_relativeInterior_previousIntersection_of_common_relativeInterior (n : ℕ)
    (C : Fin (n + 2) → Set H) [FiniteDimensional ℝ H]
    (hC_convex : ∀ k, Convex ℝ (C k)) {x : H} (hx : x ∈ ⋂ k : Fin (n + 2), ri (C k))
    (i : Fin (n + 1)) :
    x ∈ ri (previousIntersection n C i) := by
  -- Build the relative interior of each prefix by adjoining one convex set at a time.
  induction i using Fin.induction with
  | zero =>
      simpa [previousIntersection_zero] using Set.mem_iInter.mp hx 0
  | succ i ih =>
      have hxi : x ∈ ri (C i.castSucc.succ) := Set.mem_iInter.mp hx i.castSucc.succ
      have hri_nonempty :
          (ri (previousIntersection n C i.castSucc) ∩ ri (C i.castSucc.succ)).Nonempty :=
        ⟨x, ih, hxi⟩
      have hri_eq :
          ri (previousIntersection n C i.castSucc ∩ C i.castSucc.succ) =
            ri (previousIntersection n C i.castSucc) ∩ ri (C i.castSucc.succ) := by
        exact relativeInterior_inter_eq_inter_relativeInterior_of_nonempty
          (previousIntersection_convex n C hC_convex i.castSucc)
          (hC_convex i.castSucc.succ)
          hri_nonempty
      rw [previousIntersection_succ, hri_eq]
      exact ⟨ih, hxi⟩

/-- Helper for Proposition 6,20: each individual successive difference contains the origin in its
strong relative interior once the matching Proposition 6.19 branch is instantiated. -/
private theorem zero_mem_sri_successiveDifference_at_index_of_regularity (n : ℕ)
    (C : Fin (n + 2) → Set H) (hC_convex : ∀ k, Convex ℝ (C k))
    (hreg : successiveDifferenceRegularity n C) (i : Fin (n + 1)) :
    (0 : H) ∈ sri (successiveDifference n C i) := by
  have hprev_convex : Convex ℝ (previousIntersection n C i) :=
    previousIntersection_convex n C hC_convex i
  rcases hreg with hclosed | hreg
  · rcases hclosed i with ⟨V, hV_closed, hV_eq⟩
    -- Clause (i): the current difference is already a closed linear subspace.
    have hprev_nonempty : (previousIntersection n C i).Nonempty := by
      have hzero : (0 : H) ∈ successiveDifference n C i := by
        simpa [hV_eq] using V.zero_mem
      rcases Set.mem_sub.mp hzero with ⟨x, -, y, hy, _⟩
      exact ⟨y, hy⟩
    have hcurr_nonempty : (C i.succ).Nonempty := by
      have hzero : (0 : H) ∈ successiveDifference n C i := by
        simpa [hV_eq] using V.zero_mem
      rcases Set.mem_sub.mp hzero with ⟨x, hx, y, -, _⟩
      exact ⟨x, hx⟩
    have hreg19 :
        strongRelativeInteriorSubImageRegularity (previousIntersection n C i) (C i.succ)
          (ContinuousLinearMap.id ℝ H) := by
      have hS_eq :
          successiveDifference n C i =
            ((Submodule.span ℝ (successiveDifference n C i) : Submodule ℝ H) : Set H) := by
        simpa [hV_eq, Submodule.span_eq] using hV_eq
      have hS_closed :
          IsClosed
            (((Submodule.span ℝ (successiveDifference n C i) : Submodule ℝ H) : Set H)) := by
        simpa [hV_eq, Submodule.span_eq] using hV_closed
      -- Feed Proposition 6.19 with its clause `(i)`.
      dsimp [strongRelativeInteriorSubImageRegularity]
      exact Or.inl <| by
        simpa [successiveDifference] using And.intro hS_eq hS_closed
    simpa [successiveDifference] using
      zero_mem_strongRelativeInterior_sub_image_of_regularity
        hprev_nonempty hcurr_nonempty hprev_convex (hC_convex i.succ)
        (ContinuousLinearMap.id ℝ H) hreg19
  · rcases hreg with hsub | hreg
    · rcases hsub with ⟨hsub, hclosed⟩
      rcases hsub i.succ with ⟨Vcurr, hcurr_eq⟩
      rcases previousIntersection_eq_iInf_submodule n C hsub i with ⟨Vprev, hprev_eq⟩
      -- Clause (ii): rewrite both sets as submodules and use the closed-sum hypothesis.
      have hprev_nonempty : (previousIntersection n C i).Nonempty := by
        refine ⟨0, ?_⟩
        simpa [hprev_eq] using Vprev.zero_mem
      have hcurr_nonempty : (C i.succ).Nonempty := by
        refine ⟨0, ?_⟩
        simpa [hcurr_eq] using Vcurr.zero_mem
      have hsum_closed :
          IsClosed
            (((Vcurr ⊔ Vprev.map (ContinuousLinearMap.id ℝ H).toLinearMap : Submodule ℝ H) :
                Set H)) := by
        simpa [hcurr_eq, hprev_eq, Submodule.coe_sup, Submodule.map_id] using hclosed i
      have hprev_span_eq :
          previousIntersection n C i =
            ((Submodule.span ℝ (previousIntersection n C i) : Submodule ℝ H) : Set H) := by
        simpa [hprev_eq, Submodule.span_eq] using hprev_eq
      have hcurr_span_eq :
          C i.succ = ((Submodule.span ℝ (C i.succ) : Submodule ℝ H) : Set H) := by
        simpa [hcurr_eq, Submodule.span_eq] using hcurr_eq
      have hspan_sum_closed :
          IsClosed
            ((((Submodule.span ℝ (C i.succ)) ⊔
                (Submodule.span ℝ (previousIntersection n C i)).map
                  (ContinuousLinearMap.id ℝ H).toLinearMap : Submodule ℝ H) : Set H)) := by
        simpa [hcurr_eq, hprev_eq, Submodule.span_eq, Submodule.coe_sup, Submodule.map_id] using
          hsum_closed
      have hreg19 :
          strongRelativeInteriorSubImageRegularity (previousIntersection n C i) (C i.succ)
            (ContinuousLinearMap.id ℝ H) := by
        dsimp [strongRelativeInteriorSubImageRegularity]
        exact Or.inr <| Or.inl <| ⟨hprev_span_eq, hcurr_span_eq, Or.inl hspan_sum_closed⟩
      simpa [successiveDifference] using
        zero_mem_strongRelativeInterior_sub_image_of_regularity
          hprev_nonempty hcurr_nonempty hprev_convex (hC_convex i.succ)
          (ContinuousLinearMap.id ℝ H) hreg19
    · rcases hreg with hinter | hfd
      · rcases hinter with ⟨x, hxlast, hxcommon⟩
        have hxprev_int : x ∈ interior (previousIntersection n C i) :=
          mem_interior_previousIntersection_of_common_interior n C hxcommon i
        by_cases hi : i = Fin.last n
        · subst hi
          -- Clause (iii), last index: use `C_m ∩ interior (previous prefix)`.
          have hprev_nonempty : (previousIntersection n C (Fin.last n)).Nonempty :=
            ⟨x, interior_subset hxprev_int⟩
          have hcurr_nonempty : (C (Fin.last (n + 1))).Nonempty := ⟨x, hxlast⟩
          have hbranch :
              ((C (Fin.last (n + 1)) ∩
                  interior ((ContinuousLinearMap.id ℝ H) ''
                    previousIntersection n C (Fin.last n))).Nonempty ∨
                (((ContinuousLinearMap.id ℝ H) '' previousIntersection n C (Fin.last n)) ∩
                    interior (C (Fin.last (n + 1)))).Nonempty) := by
            left
            refine ⟨x, hxlast, ?_⟩
            simpa using hxprev_int
          have hreg19 :
              strongRelativeInteriorSubImageRegularity (previousIntersection n C (Fin.last n))
                (C (Fin.last (n + 1))) (ContinuousLinearMap.id ℝ H) := by
            dsimp [strongRelativeInteriorSubImageRegularity]
            exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hbranch
          simpa [successiveDifference] using
            zero_mem_strongRelativeInterior_sub_image_of_regularity
              hprev_nonempty hcurr_nonempty
              (previousIntersection_convex n C hC_convex (Fin.last n))
              (hC_convex (Fin.last (n + 1))) (ContinuousLinearMap.id ℝ H) hreg19
        · -- Clause (iii), non-last index: use `(previous prefix) ∩ interior (next set)`.
          have hi_succ_ne_last : i.succ ≠ Fin.last (n + 1) := by
            intro hi_succ
            apply hi
            apply Fin.ext
            exact Nat.succ.inj (by simpa using congrArg Fin.val hi_succ)
          rcases Fin.eq_castSucc_of_ne_last hi_succ_ne_last with ⟨j, hj⟩
          have hcurr_int : x ∈ interior (C i.succ) := by
            have hxj := Set.mem_iInter.mp hxcommon j
            simpa [hj] using hxj
          have hprev_nonempty : (previousIntersection n C i).Nonempty :=
            ⟨x, interior_subset hxprev_int⟩
          have hcurr_nonempty : (C i.succ).Nonempty := ⟨x, interior_subset hcurr_int⟩
          have hbranch :
              ((C i.succ ∩ interior ((ContinuousLinearMap.id ℝ H) ''
                  previousIntersection n C i)).Nonempty ∨
                (((ContinuousLinearMap.id ℝ H) '' previousIntersection n C i) ∩
                    interior (C i.succ)).Nonempty) := by
            right
            refine ⟨x, ?_, hcurr_int⟩
            exact ⟨x, interior_subset hxprev_int, rfl⟩
          have hreg19 :
              strongRelativeInteriorSubImageRegularity (previousIntersection n C i) (C i.succ)
                (ContinuousLinearMap.id ℝ H) := by
            dsimp [strongRelativeInteriorSubImageRegularity]
            exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hbranch
          simpa [successiveDifference] using
            zero_mem_strongRelativeInterior_sub_image_of_regularity
              hprev_nonempty hcurr_nonempty hprev_convex (hC_convex i.succ)
              (ContinuousLinearMap.id ℝ H) hreg19
      · letI : FiniteDimensional ℝ H := hfd.1
        rcases hfd.2 with ⟨x, hxri⟩
        -- Clause (iv): finite-dimensionality plus common relative-interior membership.
        have hxprev_ri : x ∈ ri (previousIntersection n C i) :=
          mem_relativeInterior_previousIntersection_of_common_relativeInterior n C hC_convex hxri i
        have hcurr_ri : x ∈ ri (C i.succ) := Set.mem_iInter.mp hxri i.succ
        have hprev_nonempty : (previousIntersection n C i).Nonempty :=
          ⟨x, (Set.mem_relativeInterior_iff.mp hxprev_ri).1⟩
        have hcurr_nonempty : (C i.succ).Nonempty :=
          ⟨x, (Set.mem_relativeInterior_iff.mp hcurr_ri).1⟩
        have hbranch :
            (FiniteDimensional ℝ H ∧
              (ri (C i.succ) ∩
                ri ((ContinuousLinearMap.id ℝ H) '' previousIntersection n C i)).Nonempty) := by
          refine ⟨hfd.1, ?_⟩
          refine ⟨x, hcurr_ri, ?_⟩
          simpa using hxprev_ri
        have hreg19 :
            strongRelativeInteriorSubImageRegularity (previousIntersection n C i) (C i.succ)
              (ContinuousLinearMap.id ℝ H) := by
          dsimp [strongRelativeInteriorSubImageRegularity]
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            hbranch
        simpa [successiveDifference] using
          zero_mem_strongRelativeInterior_sub_image_of_regularity
            hprev_nonempty hcurr_nonempty hprev_convex (hC_convex i.succ)
            (ContinuousLinearMap.id ℝ H) hreg19

-- Proof sketch: apply Proposition 6.19 to each pair consisting of `C i.succ` and the prefix
-- intersection of the preceding sets, with `L = ContinuousLinearMap.id ℝ H`. Clause (i) uses
-- Proposition 6.19(i), clause (ii) uses Proposition 6.19(ii)(a), clause (iii) uses
-- Proposition 6.19(vii), and clause (iv) uses Proposition 6.19(viii) together with
-- Fact 6.14(5); then intersect the resulting conclusions over all `i`.
/-- Proposition 6,20: if a finite family of convex sets satisfies one of the four regularity
hypotheses from the text, then the origin belongs to the strong relative interior of each
successive difference `C_{i+2} - ⋂_{j=1}^{i+1} C_j`. -/
theorem zero_mem_successiveStrongRelativeInteriorIntersection_of_regularity
    (n : ℕ) (C : Fin (n + 2) → Set H) (hC_convex : ∀ i, Convex ℝ (C i))
    (hreg : successiveDifferenceRegularity n C) :
    (0 : H) ∈ successiveStrongRelativeInteriorIntersection n C := by
  -- Prove the Proposition 6.19 conclusion pointwise and then intersect over the finite index set.
  rw [successiveStrongRelativeInteriorIntersection, Set.mem_iInter]
  intro i
  exact zero_mem_sri_successiveDifference_at_index_of_regularity n C hC_convex hreg i

end
