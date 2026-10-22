/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Corollary_6_15

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Pointwise

universe u v

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The regularity hypotheses from Proposition 6.19, packaged as a source-facing predicate on the
difference `D - L '' C`. Clauses `(ii)(b)`, `(ii)(c)`, and `(iv)` explicitly record the closedness
needed in the finite-codimensional and difference-span cases. -/
def strongRelativeInteriorSubImageRegularity (C : Set H) (D : Set K) (L : H →L[ℝ] K) : Prop :=
  let VC : Submodule ℝ H := Submodule.span ℝ C
  let VD : Submodule ℝ K := Submodule.span ℝ D
  let S : Set K := D - L '' C
  let T : Set K := D - cone (L '' C)
  (S = (Submodule.span ℝ S : Set K) ∧
      IsClosed (((Submodule.span ℝ S : Submodule ℝ K) : Set K))) ∨
    (C = (VC : Set H) ∧
      D = (VD : Set K) ∧
        (IsClosed (((VD ⊔ VC.map L.toLinearMap : Submodule ℝ K) : Set K)) ∨
          (IsClosed (VD : Set K) ∧
            (FiniteDimensional ℝ (VC.map L.toLinearMap) ∨
              (IsClosed (((VC.map L.toLinearMap : Submodule ℝ K) : Set K)) ∧
                FiniteDimensional ℝ ((VC.map L.toLinearMap)ᗮ)))) ∨
          ((FiniteDimensional ℝ VD ∨
              (IsClosed (VD : Set K) ∧ FiniteDimensional ℝ (VDᗮ))) ∧
            IsClosed (((VC.map L.toLinearMap : Submodule ℝ K) : Set K))))) ∨
    (IsCone D ∧
      T = (Submodule.span ℝ T : Set K) ∧
        IsClosed (((Submodule.span ℝ T : Submodule ℝ K) : Set K))) ∨
    (D = L '' C ∧ IsClosed (((Submodule.span ℝ (D - D) : Submodule ℝ K) : Set K))) ∨
    ((0 : K) ∈ core (D - L '' C)) ∨
    ((0 : K) ∈ interior (D - L '' C)) ∨
    ((D ∩ interior (L '' C)).Nonempty ∨ ((L '' C) ∩ interior D).Nonempty) ∨
    (FiniteDimensional ℝ K ∧ (ri D ∩ ri (L '' C)).Nonempty) ∨
    (FiniteDimensional ℝ K ∧ (ri D ∩ (L '' qri C)).Nonempty) ∨
    (FiniteDimensional ℝ H ∧ FiniteDimensional ℝ K ∧ (ri D ∩ (L '' ri C)).Nonempty)

/-- Helper for Proposition 6.19: subtracting `{0}` from a set containing `0` does not change the
set. -/
private theorem sub_singleton_zero_eq_self {S : Set K} (h0 : (0 : K) ∈ S) :
    S - ({(0 : K)} : Set K) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    have hy0 : y - (0 : K) ∈ S := by simpa using hy
    exact hyz ▸ hy0
  · intro hx
    exact Set.mem_sub.mpr ⟨x, hx, 0, by simp, by simp⟩

/-- Helper for Proposition 6.19: every point of the source-facing cone already lies in the closed
linear span of the generating set. -/
private theorem cone_subset_closedSpan_of_set (S : Set K) :
    cone S ⊆ (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) := by
  intro x hx
  -- Compare the cone hull with the closed linear span viewed as a convex cone.
  exact ConvexCone.hull_min
    (C := ((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K).toConvexCone)
    (fun y hy ↦
      Submodule.le_topologicalClosure (Submodule.span ℝ S) (Submodule.subset_span hy))
    hx

/-- Helper for Proposition 6.19: a closed linear subspace contains the origin in its strong
relative interior. -/
private theorem zero_mem_strongRelativeInterior_of_closed_submodule (V : Submodule ℝ K)
    (hV_closed : IsClosed (V : Set K)) :
    (0 : K) ∈ sri (V : Set K) := by
  -- At the origin, the translated set is still `V`, whose cone and closed span both equal `V`.
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨Submodule.zero_mem V, ?_⟩
  rw [sub_singleton_zero_eq_self (S := (V : Set K)) (Submodule.zero_mem V)]
  rw [cone_eq_self_of_submodule V, Submodule.span_eq V]
  simpa [hV_closed.submodule_topologicalClosure_eq]

/-- Helper for Proposition 6.19: if a nonempty convex set has cone equal to its closed span, then
the origin lies in its strong relative interior. -/
private theorem zero_mem_strongRelativeInterior_of_cone_eq_closedSpan {S : Set K}
    (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (hcone_eq :
      cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K)) :
    (0 : K) ∈ sri S := by
  rcases hS_nonempty with ⟨y, hy⟩
  have hy_closed :
      y ∈ (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) :=
    Submodule.le_topologicalClosure (Submodule.span ℝ S) (Submodule.subset_span hy)
  have hneg_cone : -y ∈ cone S := by
    rw [hcone_eq]
    exact Submodule.neg_mem _ hy_closed
  rw [cone_eq_toCone_of_convex_aux hS_convex] at hneg_cone
  have hzero_mem : (0 : K) ∈ S := by
    rcases (Convex.mem_toCone hS_convex).mp hneg_cone with ⟨c, hc, s, hs, hcs⟩
    by_cases hc_zero : c = 0
    · have hy_zero : y = 0 := by
        have hneg_zero : -y = 0 := by simpa [hc_zero] using hcs
        simpa using congrArg Neg.neg hneg_zero
      simpa [hy_zero] using hy
    · have hden_ne : c + 1 ≠ 0 := by positivity
      have ha : 0 ≤ c / (c + 1) := by positivity
      have hb : 0 ≤ 1 / (c + 1) := by positivity
      have hab : c / (c + 1) + 1 / (c + 1) = (1 : ℝ) := by
        field_simp [hden_ne]
      have hcombo :
          (c / (c + 1)) • s + (1 / (c + 1)) • y ∈ S :=
        hS_convex hs hy ha hb hab
      have hzero :
          (c / (c + 1)) • s + (1 / (c + 1)) • y = (0 : K) := by
        calc
          (c / (c + 1)) • s + (1 / (c + 1)) • y
              = (1 / (c + 1)) • (c • s) + (1 / (c + 1)) • y := by
                  rw [div_eq_mul_inv, one_div, smul_smul, mul_comm c ((c + 1)⁻¹)]
          _ = (1 / (c + 1)) • (c • s + y) := by rw [smul_add]
          _ = (0 : K) := by rw [hcs, neg_add_cancel, smul_zero]
      exact hzero ▸ hcombo
  -- Once the origin lies in `S`, the defining equality for `sri S` is the assumed cone identity.
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨hzero_mem, ?_⟩
  rw [sub_singleton_zero_eq_self (S := S) hzero_mem]
  exact hcone_eq

/-- Helper for Proposition 6.19: if `C` and `D` are linear subspaces, then the Minkowski
difference `D - L '' C` is exactly the submodule sum `D ⊔ L(C)`. -/
private theorem sub_eq_sup_of_submodule_image {C : Set H} {D : Set K} {L : H →L[ℝ] K}
    {VC : Submodule ℝ H} {VD : Submodule ℝ K} (hC : C = (VC : Set H)) (hD : D = (VD : Set K)) :
    D - L '' C = ((VD ⊔ VC.map L.toLinearMap : Submodule ℝ K) : Set K) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, ⟨c, hc, rfl⟩, huv⟩
    rw [hD] at hu
    rw [hC] at hc
    have hu' : u ∈ VD ⊔ VC.map L.toLinearMap := by
      exact Submodule.mem_sup.mpr ⟨u, hu, 0, by simp, by simp⟩
    have hneg' : -L c ∈ VD ⊔ VC.map L.toLinearMap := by
      refine Submodule.mem_sup.mpr ?_
      refine ⟨0, by simp, -L c, ?_, by simp⟩
      exact Submodule.neg_mem _ ⟨c, hc, rfl⟩
    have hx' : x = u + -L c := by
      simpa [sub_eq_add_neg] using huv.symm
    exact hx' ▸ (VD ⊔ VC.map L.toLinearMap).add_mem hu' hneg'
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, huv⟩
    rcases hv with ⟨c, hc, rfl⟩
    refine Set.mem_sub.mpr ?_
    refine ⟨u, ?_, L (-c), ?_, ?_⟩
    · rw [hD]
      exact hu
    · rw [hC]
      exact ⟨-c, Submodule.neg_mem _ hc, rfl⟩
    · simpa [sub_eq_add_neg] using huv

/-- Helper for Proposition 6.19: replacing `A` by `cone A` only enlarges the second term of the
Minkowski difference. -/
private theorem sub_image_subset_sub_cone_image {A D : Set K} (hA_convex : Convex ℝ A) :
    D - A ⊆ D - cone A := by
  intro x hx
  rcases hx with ⟨d, hd, a, ha, rfl⟩
  -- A point of `A` is already a point of its cone through the unit dilation.
  refine Set.mem_sub.mpr ⟨d, hd, a, ?_, rfl⟩
  exact (mem_cone_iff_exists_pos_smul_mem hA_convex).2 ⟨1, by norm_num, by simpa⟩

/-- Helper for Proposition 6.19: a cone is stable under strictly positive dilations. -/
private theorem smul_mem_of_mem_cone {D : Set K} (hD_cone : IsCone D) {x : K} (hx : x ∈ D)
    {a : ℝ} (ha : 0 < a) :
    a • x ∈ D := by
  rw [isCone_iff] at hD_cone
  rw [hD_cone]
  exact Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩

/-- Helper for Proposition 6.19: a convex cone is closed under addition. -/
private theorem add_mem_of_mem_convex_cone {D : Set K} (hD_cone : IsCone D) (hD_convex : Convex ℝ D)
    {x y : K} (hx : x ∈ D) (hy : y ∈ D) :
    x + y ∈ D := by
  -- Convexity gives the midpoint, and the cone law rescales it back to the sum.
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ D := by
    exact (convex_iff_add_mem.1 hD_convex) hx hy (by positivity) (by positivity) (by norm_num)
  have hsum : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ D := by
    exact smul_mem_of_mem_cone hD_cone hmid (by positivity)
  simpa [smul_add, smul_smul] using hsum

/-- Helper for Proposition 6.19: subtracting the cone over a convex set from a convex cone lands
inside the cone of the original Minkowski difference. -/
private theorem sub_cone_subset_cone_sub_of_isCone {A D : Set K} (hA_convex : Convex ℝ A)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D) :
    D - cone A ⊆ cone (D - A) := by
  let S : Set K := D - A
  have hS_convex : Convex ℝ S := by
    simpa [S] using hD_convex.sub hA_convex
  intro x hx
  rcases hx with ⟨d, hd, y, hy, rfl⟩
  rcases (mem_cone_iff_exists_pos_smul_mem hA_convex).1 hy with ⟨a, ha, ha_mem⟩
  rcases Set.mem_smul_set.mp ha_mem with ⟨u, hu, rfl⟩
  have hscaled_d : a⁻¹ • d ∈ D := by
    exact smul_mem_of_mem_cone hD_cone hd (inv_pos.mpr ha)
  have hsub_mem : a⁻¹ • d - u ∈ S := by
    exact Set.mem_sub.mpr ⟨a⁻¹ • d, hscaled_d, u, hu, rfl⟩
  -- Rescaling the translated witness recovers the original point in the cone of `D - A`.
  refine (mem_cone_iff_exists_pos_smul_mem hS_convex).2 ⟨a, ha, ?_⟩
  refine Set.mem_smul_set.mpr ⟨a⁻¹ • d - u, hsub_mem, ?_⟩
  calc
    a • (a⁻¹ • d - u)
        = a • (a⁻¹ • d) - a • u := by rw [smul_sub]
    _ = (a * a⁻¹) • d - a • u := by rw [smul_smul]
    _ = d - a • u := by simp [ha.ne']

/-- Helper for Proposition 6.19: branch `(iii)` closes once `D - cone A` is a closed linear
subspace, because the textbook inclusion chain identifies `cone (D - A)` with the closed span of
`D - A`. -/
private theorem zero_mem_strongRelativeInterior_of_closed_subspace_sub_cone_image {A D : Set K}
    (hA_nonempty : A.Nonempty) (hD_nonempty : D.Nonempty)
    (hA_convex : Convex ℝ A) (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hT_eq : D - cone A = (Submodule.span ℝ (D - cone A) : Set K))
    (hT_closed : IsClosed (((Submodule.span ℝ (D - cone A) : Submodule ℝ K) : Set K))) :
    (0 : K) ∈ sri (D - A) := by
  let S : Set K := D - A
  let V : Submodule ℝ K := Submodule.span ℝ (D - cone A)
  have hS_nonempty : S.Nonempty := by
    rcases hD_nonempty with ⟨d, hd⟩
    rcases hA_nonempty with ⟨a, ha⟩
    refine ⟨d - a, ?_⟩
    simpa [S] using Set.mem_sub.mpr ⟨d, hd, a, ha, rfl⟩
  have hS_convex : Convex ℝ S := by
    simpa [S] using hD_convex.sub hA_convex
  have hS_subset_T : S ⊆ D - cone A := by
    simpa [S] using sub_image_subset_sub_cone_image (D := D) hA_convex
  have hclosedSpan_subset_T :
      (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) ⊆ D - cone A := by
    have hspan_le : Submodule.span ℝ S ≤ V := by
      refine Submodule.span_le.2 ?_
      intro x hx
      simpa [V] using (Submodule.subset_span (hS_subset_T hx))
    have hV_closed : IsClosed (V : Set K) := by
      simpa [V] using hT_closed
    have hclosure_le : (Submodule.span ℝ S).topologicalClosure ≤ V := by
      exact Submodule.topologicalClosure_minimal (Submodule.span ℝ S) hspan_le hV_closed
    intro x hx
    have hxV : x ∈ (V : Set K) := hclosure_le hx
    rw [hT_eq]
    simpa [V] using hxV
  have hT_subset_cone : D - cone A ⊆ cone S := by
    simpa [S] using sub_cone_subset_cone_sub_of_isCone hA_convex hD_convex hD_cone
  have hcone_eq :
      cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) := by
    apply Set.Subset.antisymm
    · exact cone_subset_closedSpan_of_set S
    · intro x hx
      exact hT_subset_cone (hclosedSpan_subset_T hx)
  -- The branch now reduces to the generic origin-in-`sri` criterion used earlier in the proof.
  exact zero_mem_strongRelativeInterior_of_cone_eq_closedSpan hS_nonempty hS_convex hcone_eq

/-- Helper for Proposition 6.19: if a convex set contains a point whose opposite already lies in
its cone, then the set contains the origin. -/
private theorem zero_mem_of_mem_and_neg_mem_cone {A : Set K} (hA_convex : Convex ℝ A) {a : K}
    (ha : a ∈ A) (hneg : -a ∈ cone A) :
    (0 : K) ∈ A := by
  rw [cone_eq_toCone_of_convex_aux hA_convex] at hneg
  rcases (Convex.mem_toCone hA_convex).mp hneg with ⟨t, ht, b, hb, htb⟩
  by_cases ht_zero : t = 0
  · have hneg_zero : -a = (0 : K) := by simpa [ht_zero] using htb
    have ha_zero : a = 0 := by simpa using congrArg Neg.neg hneg_zero
    simpa [ha_zero] using ha
  · have hta : t / (t + 1) + 1 / (t + 1) = (1 : ℝ) := by
      field_simp [ht_zero]
    have hcombo :
        (t / (t + 1)) • b + (1 / (t + 1)) • a ∈ A :=
      hA_convex hb ha (by positivity) (by positivity) hta
    have hzero :
        (t / (t + 1)) • b + (1 / (t + 1)) • a = (0 : K) := by
      have hden_ne : t + 1 ≠ 0 := by positivity
      calc
        (t / (t + 1)) • b + (1 / (t + 1)) • a
            = (1 / (t + 1)) • (t • b) + (1 / (t + 1)) • a := by
                rw [div_eq_mul_inv, one_div, smul_smul, mul_comm t ((t + 1)⁻¹)]
        _ = (1 / (t + 1)) • (t • b + a) := by rw [smul_add]
        _ = (0 : K) := by
              rw [htb, neg_add_cancel, smul_zero]
    exact hzero ▸ hcombo

/-- Helper for Proposition 6.19: interior membership at the right endpoint yields an interior
neighborhood of the origin in the Minkowski difference. -/
private theorem zero_mem_interior_sub_of_mem_left_mem_interior_right {A D : Set K} {y : K}
    (hyD : y ∈ D) (hyA : y ∈ interior A) :
    (0 : K) ∈ interior (D - A) := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyA) with ⟨ε, hε, hball⟩
  have hsubset : Metric.ball (0 : K) ε ⊆ D - A := by
    intro z hz
    refine Set.mem_sub.mpr ?_
    refine ⟨y, hyD, y - z, hball ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, norm_neg] using hz
    · abel
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : K) hε) hsubset

/-- Helper for Proposition 6.19: interior membership at the left endpoint yields an interior
neighborhood of the origin in the Minkowski difference. -/
private theorem zero_mem_interior_sub_of_mem_interior_left_mem_right {A D : Set K} {y : K}
    (hyD : y ∈ interior D) (hyA : y ∈ A) :
    (0 : K) ∈ interior (D - A) := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyD) with ⟨ε, hε, hball⟩
  have hsubset : Metric.ball (0 : K) ε ⊆ D - A := by
    intro z hz
    refine Set.mem_sub.mpr ?_
    refine ⟨y + z, hball ?_, y, hyA, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, dist_comm, sub_eq_add_neg, add_assoc] using hz
    · abel
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : K) hε) hsubset

/-- Helper for Proposition 6.19: in a finite-dimensional target space, a witness in
`ri D ∩ ri A` yields `0 ∈ sri (D - A)`. -/
private theorem zero_mem_strongRelativeInterior_of_nonempty_relativeInterior_inter {A D : Set K}
    [FiniteDimensional ℝ K] (hA_nonempty : A.Nonempty) (hD_nonempty : D.Nonempty)
    (hA_convex : Convex ℝ A) (hD_convex : Convex ℝ D)
    (hri_nonempty : (ri D ∩ ri A).Nonempty) :
    (0 : K) ∈ sri (D - A) := by
  have hsub_convex : Convex ℝ (D - A) := hD_convex.sub hA_convex
  rw [strongRelativeInterior_eq_relativeInterior_of_finiteDimensional hsub_convex]
  rw [relativeInterior_sub_eq_sub_relativeInterior_of_finiteDimensional D A
    hD_nonempty hA_nonempty hD_convex hA_convex]
  rcases hri_nonempty with ⟨y, hyD, hyA⟩
  exact Set.mem_sub.mpr ⟨y, hyD, y, hyA, sub_self y⟩

-- Proof sketch: choose the branch corresponding to clause (vi) in the defining disjunction.
/-- If the origin lies in the interior of `D - L '' C`, then the Proposition 6.19 regularity
predicate holds. -/
theorem strongRelativeInteriorSubImageRegularity_of_zero_mem_interior {C : Set H} {D : Set K}
    (L : H →L[ℝ] K) (h : (0 : K) ∈ interior (D - L '' C)) :
    strongRelativeInteriorSubImageRegularity C D L := by
  -- Clause (vi) is one of the explicit disjuncts in the packaged regularity predicate.
  dsimp [strongRelativeInteriorSubImageRegularity]
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

-- Proof sketch: follow the textbook case split on the packaged regularity predicate. The linear
-- subspace branches are reduced to closed-submodule strong-relative-interior facts, the
-- interior/relative-interior branches use the imported Chapter 6 API directly, and the remaining
-- cone-transport branches are isolated as the only structural blockers.
-- Route correction: besides clause `(ii)(c)`, clause `(ii)(b)` also needs an explicit closedness
-- hypothesis in its finite-codimensional subspace encoding. Without that repair, a dense proper
-- image subspace with finite-dimensional orthogonal complement would still satisfy the old clause
-- but would force `cone (D - L '' C) ≠ closedSpan (D - L '' C)`.
-- Route correction: clause `(iv)` also needs closedness of `span (D - D)`, not just `span D`.
-- Otherwise affine translates of dense proper subspaces satisfy the old hypothesis while
-- `D - D` itself remains a dense nonclosed subspace, so the conclusion fails.
/-- Proposition 6.19: if `C` and `D` are nonempty convex subsets of real Hilbert spaces and one of
the regularity conditions (i) through (x) from the text holds for the continuous linear image
`L '' C`, then the origin belongs to the strong relative interior of `D - L '' C`. -/
theorem zero_mem_strongRelativeInterior_sub_image_of_regularity
    {C : Set H} {D : Set K} (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D) (L : H →L[ℝ] K)
    (h : strongRelativeInteriorSubImageRegularity C D L) :
    (0 : K) ∈ sri (D - L '' C) := by
  let A : Set K := L '' C
  let S : Set K := D - A
  have hA_nonempty : A.Nonempty := by
    simpa [A] using Set.Nonempty.image L hC_nonempty
  have hA_convex : Convex ℝ A := by
    simpa [A] using hC_convex.linear_image L.toLinearMap
  have hS_nonempty : S.Nonempty := by
    rcases hD_nonempty with ⟨d, hd⟩
    rcases hC_nonempty with ⟨c, hc⟩
    refine ⟨d - L c, ?_⟩
    exact Set.mem_sub.mpr ⟨d, hd, L c, ⟨c, hc, rfl⟩, rfl⟩
  have hS_convex : Convex ℝ S := by
    simpa [S, A] using hD_convex.sub hA_convex
  change (0 : K) ∈ sri S
  dsimp [strongRelativeInteriorSubImageRegularity] at h
  rcases h with h1 | h
  · let V : Submodule ℝ K := Submodule.span ℝ S
    -- Branch (i): the difference is already a closed linear subspace.
    have hS_eq : S = (V : Set K) := by
      simpa [S, A, V] using h1.1
    rw [hS_eq]
    exact zero_mem_strongRelativeInterior_of_closed_submodule (V := V) h1.2
  rcases h with h2 | h
  · rcases h2 with ⟨hC_sub, hD_sub, h2⟩
    have hW_eq :
        S =
          (((Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap : Submodule ℝ K) :
            Set K) := by
      exact sub_eq_sup_of_submodule_image
        (C := C) (D := D) (L := L) (VC := Submodule.span ℝ C) (VD := Submodule.span ℝ D)
        hC_sub hD_sub
    rcases h2 with h2a | h2
    · -- Branch (ii)(a): the submodule sum is closed by assumption.
      rw [hW_eq]
      exact zero_mem_strongRelativeInterior_of_closed_submodule
        (V := (Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap) h2a
    rcases h2 with h2b | h2c
    · rcases h2b with ⟨hVD_closed, hImageFinite⟩
      -- Branch (ii)(b): closedness of `D` plus finite-dimensionality/finite-codimensionality of
      -- `L(C)` makes the submodule sum closed by Fact 2.28.
      have hImage_closed :
          IsClosed ((((Submodule.span ℝ C).map L.toLinearMap : Submodule ℝ K) : Set K)) := by
        rcases hImageFinite with hfinite | ⟨hclosed, _⟩
        · letI : FiniteDimensional ℝ ((Submodule.span ℝ C).map L.toLinearMap) := hfinite
          exact Submodule.closed_of_finiteDimensional _
        · exact hclosed
      have hImage_finite_or_perp :
          FiniteDimensional ℝ ((Submodule.span ℝ C).map L.toLinearMap) ∨
            FiniteDimensional ℝ (((Submodule.span ℝ C).map L.toLinearMap)ᗮ) := by
        rcases hImageFinite with hfinite | ⟨_, hfinite_perp⟩
        · exact Or.inl hfinite
        · exact Or.inr hfinite_perp
      have hW_closed :
          IsClosed
            ((((Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap :
                Submodule ℝ K) : Set K)) :=
        isClosed_sup_of_isClosed_of_finiteDimensional_or_finiteDimensional_orthogonal
          hVD_closed hImage_closed hImage_finite_or_perp
      rw [hW_eq]
      exact zero_mem_strongRelativeInterior_of_closed_submodule
        (V := (Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap) hW_closed
    · rcases h2c with ⟨hVDFinite, hImage_closed⟩
      -- Branch (ii)(c): after repairing the finite-codimensional clause, we again reduce to
      -- closedness of the submodule sum via Fact 2.28.
      have hVD_closed : IsClosed (((Submodule.span ℝ D : Submodule ℝ K) : Set K)) := by
        rcases hVDFinite with hfinite | ⟨hclosed, _⟩
        · letI : FiniteDimensional ℝ (Submodule.span ℝ D) := hfinite
          exact Submodule.closed_of_finiteDimensional _
        · exact hclosed
      have hVD_finite_or_perp :
          FiniteDimensional ℝ (Submodule.span ℝ D) ∨
            FiniteDimensional ℝ ((Submodule.span ℝ D)ᗮ) := by
        rcases hVDFinite with hfinite | ⟨_, hfinite_perp⟩
        · exact Or.inl hfinite
        · exact Or.inr hfinite_perp
      have hW_closed_aux :
          IsClosed
            ((((Submodule.span ℝ C).map L.toLinearMap) ⊔ (Submodule.span ℝ D) :
                Submodule ℝ K) : Set K) :=
        isClosed_sup_of_isClosed_of_finiteDimensional_or_finiteDimensional_orthogonal
          hImage_closed hVD_closed hVD_finite_or_perp
      have hW_closed :
          IsClosed
            ((((Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap :
                Submodule ℝ K) : Set K)) := by
        simpa [sup_comm] using hW_closed_aux
      rw [hW_eq]
      exact zero_mem_strongRelativeInterior_of_closed_submodule
        (V := (Submodule.span ℝ D) ⊔ (Submodule.span ℝ C).map L.toLinearMap) hW_closed
  rcases h with h3 | h
  · -- TODO for Proposition 6.19 branch (iii): prove the cone transport identity
    -- Route correction: the source proof only needs the containment chain
    -- `closedSpan S ⊆ D - cone A ⊆ cone S ⊆ closedSpan S`, not a brittle extensional equality.
    rcases h3 with ⟨hD_cone, hT_eq, hT_closed⟩
    exact zero_mem_strongRelativeInterior_of_closed_subspace_sub_cone_image
      (A := A) (D := D) hA_nonempty hD_nonempty hA_convex hD_convex hD_cone
      (by simpa [A] using hT_eq) (by simpa [A] using hT_closed)
  rcases h with h4 | h
  · rcases h4 with ⟨hDA, hspan_closed⟩
    have hS_eq : S = D - D := by
      simpa [S, A] using congrArg (fun T : Set K => D - T) hDA.symm
    have hS_symm : S = -S := by
      rw [hS_eq]
      ext x
      constructor
      · rintro ⟨u, hu, v, hv, rfl⟩
        rw [Set.mem_neg]
        exact Set.mem_sub.mpr
          ⟨v, hv, u, hu, by simp [sub_eq_add_neg]⟩
      · intro hx
        rw [Set.mem_neg] at hx
        rcases hx with ⟨u, hu, v, hv, huv⟩
        exact Set.mem_sub.mpr ⟨v, hv, u, hu, by simpa using congrArg Neg.neg huv⟩
    have hcone_eq_span : cone S = (Submodule.span ℝ S : Set K) := by
      -- Symmetry turns the cone generated by `S` into its full linear span.
      rw [cone_eq_toCone_of_convex_aux hS_convex]
      exact (span_eq_cone_of_eq_neg hS_nonempty hS_convex hS_symm).symm
    have hcone_eq :
        cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) := by
      -- The repaired clause `(iv)` gives exactly the closedness needed to identify the closed span.
      rw [hcone_eq_span]
      have hspan_closed' : IsClosed (((Submodule.span ℝ S : Submodule ℝ K) : Set K)) := by
        simpa [hS_eq] using hspan_closed
      simpa [hspan_closed'.submodule_topologicalClosure_eq]
    exact zero_mem_strongRelativeInterior_of_cone_eq_closedSpan
      (S := S) hS_nonempty hS_convex hcone_eq
  rcases h with h5 | h
  · -- Branch (v): `0 ∈ core S` forces `cone S = univ`, hence also `closedSpan S = univ`.
    rcases Set.mem_core_iff.mp h5 with ⟨h0S, hcone_univ⟩
    have hconeS_univ : cone S = (univ : Set K) := by
      simpa [S, A, sub_singleton_zero_eq_self (S := S) h0S] using hcone_univ
    have hclosedSpan_eq :
        (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) = (univ : Set K) := by
      rw [Set.eq_univ_iff_forall]
      intro x
      have hx_cone : x ∈ cone S := by simpa [hconeS_univ]
      exact cone_subset_closedSpan_of_set S hx_cone
    have hcone_eq :
        cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) := by
      rw [hconeS_univ, hclosedSpan_eq]
    simpa using
      zero_mem_strongRelativeInterior_of_cone_eq_closedSpan (S := S) ⟨0, h0S⟩ hS_convex hcone_eq
  rcases h with h6 | h
  · -- Branch (vi): nonempty interior identifies `sri` with the ordinary interior.
    have h0 : (0 : K) ∈ interior S := by simpa [S, A] using h6
    rw [← interior_eq_strongRelativeInterior_of_convex_nonempty_interior hS_convex ⟨0, h0⟩]
    simpa [S, A] using h0
  rcases h with h7 | h
  · rcases h7 with hleft | hright
    · rcases hleft with ⟨y, hyD, hyA⟩
      -- Branch (vii), first alternative: a common point of `D` and `int A` translates a ball to
      -- the origin inside `D - A`.
      have h0 : (0 : K) ∈ interior S := by
        exact zero_mem_interior_sub_of_mem_left_mem_interior_right hyD hyA
      rw [← interior_eq_strongRelativeInterior_of_convex_nonempty_interior hS_convex ⟨0, h0⟩]
      simpa [S, A] using h0
    · rcases hright with ⟨y, hyA, hyD⟩
      -- Branch (vii), second alternative: the symmetric interior argument uses the left endpoint.
      have h0 : (0 : K) ∈ interior S := by
        exact zero_mem_interior_sub_of_mem_interior_left_mem_right hyD hyA
      rw [← interior_eq_strongRelativeInterior_of_convex_nonempty_interior hS_convex ⟨0, h0⟩]
      simpa [S, A] using h0
  rcases h with h8 | h
  · rcases h8 with ⟨hK_finite, hri_nonempty⟩
    letI : FiniteDimensional ℝ K := hK_finite
    -- Branch (viii): in finite dimension, `ri (D - A) = ri D - ri A` and `sri = ri`.
    simpa using
      zero_mem_strongRelativeInterior_of_nonempty_relativeInterior_inter
        (A := A) hA_nonempty hD_nonempty hA_convex hD_convex hri_nonempty
  rcases h with h9 | h10
  · rcases h9 with ⟨hK_finite, hri_qri_nonempty⟩
    letI : FiniteDimensional ℝ K := hK_finite
    -- Branch (ix): rewrite `ri (L '' C)` as `L '' qri C`, then return to branch (viii).
    have hqri_nonempty : (qri C).Nonempty := by
      rcases hri_qri_nonempty with ⟨y, _, hyqri⟩
      rcases hyqri with ⟨x, hxqri, rfl⟩
      exact ⟨x, hxqri⟩
    have hri_image : ri A = L '' qri C := by
      simpa [A] using relativeInterior_image_eq_image_quasiRelativeInterior
        (L := L) hC_convex hqri_nonempty
    have hri_nonempty : (ri D ∩ ri A).Nonempty := by
      rcases hri_qri_nonempty with ⟨y, hyD, hyA⟩
      refine ⟨y, hyD, ?_⟩
      rw [hri_image]
      simpa [A] using hyA
    simpa using
      zero_mem_strongRelativeInterior_of_nonempty_relativeInterior_inter
        (A := A) hA_nonempty hD_nonempty hA_convex hD_convex hri_nonempty
  · rcases h10 with ⟨hH_finite, hK_finite, hri_nonempty⟩
    letI : FiniteDimensional ℝ H := hH_finite
    letI : FiniteDimensional ℝ K := hK_finite
    -- Branch (x): rewrite `ri (L '' C)` as `L '' ri C`, then reuse branch (viii).
    have hri_image : ri A = L '' ri C := by
      simpa [A] using
        relativeInterior_image_eq_image_relativeInterior_of_finiteDimensional
          (L := L) C hC_nonempty hC_convex
    have hri_nonempty' : (ri D ∩ ri A).Nonempty := by
      rcases hri_nonempty with ⟨y, hyD, hyA⟩
      refine ⟨y, hyD, ?_⟩
      rw [hri_image]
      simpa [A] using hyA
    simpa using
      zero_mem_strongRelativeInterior_of_nonempty_relativeInterior_inter
        (A := A) hA_nonempty hD_nonempty hA_convex hD_convex hri_nonempty'

end
