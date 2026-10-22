/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part3

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Corollary 20.3.1: convert the textbook hypothesis
`C₁ ∩ C₂ = ∅` into disjointness. -/
lemma helperForCorollary_20_3_1_disjoint_of_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ))) :
    Disjoint C₁ C₂ := by
  simpa [Set.disjoint_iff_inter_eq_empty] using hinter

/-- Helper for Corollary 20.3.1: rewrite disjointness of `C₁` and `C₂` as
`C₁ ∩ C₂ = ∅`. -/
lemma helperForCorollary_20_3_1_inter_eq_empty_of_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hdisj : Disjoint C₁ C₂) :
    C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) := by
  simpa [Set.disjoint_iff_inter_eq_empty] using hdisj

/-- Helper for Corollary 20.3.1: disjointness and empty intersection are
equivalent for two sets in finite-dimensional Euclidean coordinates. -/
lemma helperForCorollary_20_3_1_disjoint_iff_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    Disjoint C₁ C₂ ↔ C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) := by
  constructor
  · exact helperForCorollary_20_3_1_inter_eq_empty_of_disjoint
  · exact helperForCorollary_20_3_1_disjoint_of_inter_eq_empty

/-- Helper for Corollary 20.3.1: disjointness is symmetric in the two sets. -/
lemma helperForCorollary_20_3_1_disjoint_comm
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    Disjoint C₁ C₂ ↔ Disjoint C₂ C₁ := by
  constructor
  · intro hdisj
    exact hdisj.symm
  · intro hdisj
    exact hdisj.symm

/-- Helper for Corollary 20.3.1: disjoint sets have no common point. -/
lemma helperForCorollary_20_3_1_no_common_point_of_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hdisj : Disjoint C₁ C₂) :
    ¬ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂ := by
  intro hcommon
  rcases hcommon with ⟨x, hxC₁, hxC₂⟩
  exact (Set.disjoint_left.mp hdisj) hxC₁ hxC₂

/-- Helper for Corollary 20.3.1: if two sets share no point, they are disjoint. -/
lemma helperForCorollary_20_3_1_disjoint_of_no_common_point
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hnoCommon : ¬ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂) :
    Disjoint C₁ C₂ := by
  refine Set.disjoint_left.2 ?_
  intro x hxC₁ hxC₂
  exact hnoCommon ⟨x, hxC₁, hxC₂⟩

/-- Helper for Corollary 20.3.1: disjointness is equivalent to absence of common
points. -/
lemma helperForCorollary_20_3_1_disjoint_iff_no_common_point
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    Disjoint C₁ C₂ ↔ ¬ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂ := by
  constructor
  · exact helperForCorollary_20_3_1_no_common_point_of_disjoint
  · exact helperForCorollary_20_3_1_disjoint_of_no_common_point

/-- Helper for Corollary 20.3.1: "no common point" is equivalent to
`C₁ ∩ C₂ = ∅`. -/
lemma helperForCorollary_20_3_1_no_common_point_iff_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (¬ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂) ↔
      C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) := by
  constructor
  · intro hnoCommon
    exact helperForCorollary_20_3_1_inter_eq_empty_of_disjoint
      (helperForCorollary_20_3_1_disjoint_of_no_common_point hnoCommon)
  · intro hinter
    exact helperForCorollary_20_3_1_no_common_point_of_disjoint
      (helperForCorollary_20_3_1_disjoint_of_inter_eq_empty hinter)

/-- Helper for Corollary 20.3.1: emptiness of the intersection is symmetric. -/
lemma helperForCorollary_20_3_1_inter_eq_empty_comm
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) ↔
      C₂ ∩ C₁ = (∅ : Set (Fin n → ℝ)) := by
  constructor
  · intro hinter
    have hdisj12 : Disjoint C₁ C₂ :=
      helperForCorollary_20_3_1_disjoint_of_inter_eq_empty hinter
    have hdisj21 : Disjoint C₂ C₁ :=
      (helperForCorollary_20_3_1_disjoint_comm).1 hdisj12
    exact helperForCorollary_20_3_1_inter_eq_empty_of_disjoint hdisj21
  · intro hinter
    have hdisj21 : Disjoint C₂ C₁ :=
      helperForCorollary_20_3_1_disjoint_of_inter_eq_empty hinter
    have hdisj12 : Disjoint C₁ C₂ :=
      (helperForCorollary_20_3_1_disjoint_comm).2 hdisj21
    exact helperForCorollary_20_3_1_inter_eq_empty_of_disjoint hdisj12

/-- Helper for Corollary 20.3.1: from `C₁ ∩ C₂ = ∅`, both orderings have no common
point witness. -/
lemma helperForCorollary_20_3_1_no_common_point_comm_of_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ))) :
    (¬ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂) ∧
      (¬ ∃ x : Fin n → ℝ, x ∈ C₂ ∧ x ∈ C₁) := by
  constructor
  · exact (helperForCorollary_20_3_1_no_common_point_iff_inter_eq_empty).2 hinter
  · exact
      (helperForCorollary_20_3_1_no_common_point_iff_inter_eq_empty).2
        ((helperForCorollary_20_3_1_inter_eq_empty_comm).1 hinter)

/-- Helper for Corollary 20.3.1: nonempty intersection is equivalent to existence
of a common point witness. -/
lemma helperForCorollary_20_3_1_inter_nonempty_iff_exists_common_point
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (C₁ ∩ C₂).Nonempty ↔ ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂ := by
  constructor
  · rintro ⟨x, hxInInter⟩
    exact ⟨x, hxInInter.1, hxInInter.2⟩
  · rintro ⟨x, hxInC₁, hxInC₂⟩
    exact ⟨x, ⟨hxInC₁, hxInC₂⟩⟩

/-- Helper for Corollary 20.3.1: a common-point witness rules out disjointness. -/
lemma helperForCorollary_20_3_1_not_disjoint_of_exists_common_point
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hcommon : ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂) :
    ¬ Disjoint C₁ C₂ := by
  intro hdisj
  exact (helperForCorollary_20_3_1_no_common_point_of_disjoint hdisj) hcommon

/-- Helper for Corollary 20.3.1: non-disjointness produces a common-point
witness. -/
lemma helperForCorollary_20_3_1_exists_common_point_of_not_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hnotDisj : ¬ Disjoint C₁ C₂) :
    ∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂ := by
  classical
  by_contra hnoCommon
  exact hnotDisj (helperForCorollary_20_3_1_disjoint_of_no_common_point hnoCommon)

/-- Helper for Corollary 20.3.1: disjointness is equivalent to absence of
intersection witnesses. -/
lemma helperForCorollary_20_3_1_exists_common_point_iff_not_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (∃ x : Fin n → ℝ, x ∈ C₁ ∧ x ∈ C₂) ↔ ¬ Disjoint C₁ C₂ := by
  constructor
  · exact helperForCorollary_20_3_1_not_disjoint_of_exists_common_point
  · exact helperForCorollary_20_3_1_exists_common_point_of_not_disjoint

/-- Helper for Corollary 20.3.1: nonempty intersection is equivalent to
non-disjointness. -/
lemma helperForCorollary_20_3_1_inter_nonempty_iff_not_disjoint
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (C₁ ∩ C₂).Nonempty ↔ ¬ Disjoint C₁ C₂ := by
  constructor
  · intro hinterNonempty
    exact helperForCorollary_20_3_1_not_disjoint_of_exists_common_point
      ((helperForCorollary_20_3_1_inter_nonempty_iff_exists_common_point).1 hinterNonempty)
  · intro hnotDisj
    exact (helperForCorollary_20_3_1_inter_nonempty_iff_exists_common_point).2
      (helperForCorollary_20_3_1_exists_common_point_of_not_disjoint hnotDisj)

/-- Helper for Corollary 20.3.1: empty intersection is equivalent to
non-nonemptiness of the intersection set. -/
lemma helperForCorollary_20_3_1_inter_eq_empty_iff_not_nonempty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) ↔ ¬ (C₁ ∩ C₂).Nonempty := by
  constructor
  · intro hinter
    exact (Set.not_nonempty_iff_eq_empty).2 hinter
  · intro hnotNonempty
    exact (Set.not_nonempty_iff_eq_empty).1 hnotNonempty

/-- Helper for Corollary 20.3.1: if `C₁ ∩ C₂ = ∅`, then every point of `C₁`
lies outside `C₂`. -/
lemma helperForCorollary_20_3_1_not_mem_right_of_mem_left_of_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)))
    (hxC₁ : x ∈ C₁) :
    x ∉ C₂ := by
  intro hxC₂
  have hdisj : Disjoint C₁ C₂ :=
    helperForCorollary_20_3_1_disjoint_of_inter_eq_empty hinter
  exact (Set.disjoint_left.mp hdisj) hxC₁ hxC₂

/-- Helper for Corollary 20.3.1: if `C₁ ∩ C₂ = ∅`, then every point of `C₂`
lies outside `C₁`. -/
lemma helperForCorollary_20_3_1_not_mem_left_of_mem_right_of_inter_eq_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)))
    (hxC₂ : x ∈ C₂) :
    x ∉ C₁ := by
  intro hxC₁
  have hdisj : Disjoint C₂ C₁ :=
    helperForCorollary_20_3_1_disjoint_of_inter_eq_empty
      ((helperForCorollary_20_3_1_inter_eq_empty_comm).1 hinter)
  exact (Set.disjoint_left.mp hdisj) hxC₂ hxC₁

/-- Helper for Corollary 20.3.1: disjointness is equivalent to saying the
intersection is not nonempty. -/
lemma helperForCorollary_20_3_1_disjoint_iff_not_inter_nonempty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    Disjoint C₁ C₂ ↔ ¬ (C₁ ∩ C₂).Nonempty := by
  constructor
  · intro hdisj hinterNonempty
    exact ((helperForCorollary_20_3_1_inter_nonempty_iff_not_disjoint).1 hinterNonempty) hdisj
  · intro hnotInterNonempty
    exact
      helperForCorollary_20_3_1_disjoint_of_inter_eq_empty
        ((helperForCorollary_20_3_1_inter_eq_empty_iff_not_nonempty).2 hnotInterNonempty)

/-- Helper for Corollary 20.3.1: a pointwise exclusion condition from `C₁` into
the complement of `C₂` implies empty intersection. -/
lemma helperForCorollary_20_3_1_inter_eq_empty_of_forall_not_mem_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hseparate : ∀ x : Fin n → ℝ, x ∈ C₁ → x ∉ C₂) :
    C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)) := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hxInter
  exact (hseparate x hxInter.1) hxInter.2

/-- Helper for Corollary 20.3.1: a polyhedral set in `Fin n → ℝ` is convex and closed. -/
lemma helperForCorollary_20_3_1_convex_and_closed_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    Convex ℝ C ∧ IsClosed C := by
  exact ⟨
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly,
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C) hCpoly
  ⟩

/-- Helper for Corollary 20.3.1: any common recession direction of `C₁` and `C₂`
is killed by a projection whose kernel is the lineality space of `C₂`. -/
lemma helperForCorollary_20_3_1_commonRec_projects_to_zero
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hcommonRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂)
    {L : Submodule ℝ (Fin n → ℝ)}
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂) :
    ∀ y : Fin n → ℝ,
      y ∈ Set.recessionCone C₁ →
      y ∈ Set.recessionCone C₂ →
      π y = 0 := by
  intro y hyC₁ hyC₂
  have hyLineal : y ∈ linealitySpace_fin C₂ := by
    simpa [linealitySpace_fin] using hcommonRecLinear y hyC₁ hyC₂
  have hyL : y ∈ L := by
    have hyLset : y ∈ (L : Set (Fin n → ℝ)) := by
      simpa [hL] using hyLineal
    exact hyLset
  have hyKer : y ∈ LinearMap.ker π := by
    simpa [hker] using hyL
  exact (LinearMap.mem_ker).1 hyKer

/-- Helper for Corollary 20.3.1: projection along the lineality kernel rewrites
the original difference as a preimage of projected differences. -/
lemma helperForCorollary_20_3_1_projection_preimage_sub_eq_projected_sub
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₂conv : Convex ℝ C₂)
    {L : Submodule ℝ (Fin n → ℝ)}
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂) :
    C₁ - C₂ = π ⁻¹' ((π '' C₁) - (π '' C₂)) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sub.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    refine Set.mem_preimage.2 ?_
    refine Set.mem_sub.2 ?_
    refine ⟨π x₁, ⟨x₁, hx₁, rfl⟩, π x₂, ⟨x₂, hx₂, rfl⟩, ?_⟩
    simp
  · intro hx
    rcases Set.mem_sub.1 (Set.mem_preimage.1 hx) with ⟨u, hu, v, hv, huv⟩
    rcases hu with ⟨x₁, hx₁, rfl⟩
    rcases hv with ⟨x₂, hx₂, rfl⟩
    have hkerMem : x - (x₁ - x₂) ∈ LinearMap.ker π := by
      apply (LinearMap.mem_ker).2
      calc
        π (x - (x₁ - x₂)) = π x - π (x₁ - x₂) := by simp
        _ = (π x₁ - π x₂) - (π x₁ - π x₂) := by simpa [huv]
        _ = 0 := sub_self _
    have hlinealMem : x - (x₁ - x₂) ∈ linealitySpace_fin C₂ := by
      have hLMem : x - (x₁ - x₂) ∈ L := by
        simpa [hker] using hkerMem
      simpa [← hL] using hLMem
    have hx₂Shift : x₂ - (x - (x₁ - x₂)) ∈ C₂ := by
      exact
        (helperForTheorem_19_1_add_sub_mem_of_mem_linealitySpace_fin
          (n := n) (C := C₂) hC₂conv hlinealMem hx₂).2
    refine Set.mem_sub.2 ?_
    refine ⟨x₁, hx₁, x₂ - (x - (x₁ - x₂)), hx₂Shift, ?_⟩
    abel

/-- Helper for Corollary 20.3.1: the projection image of `C₂` is closed when the
projection kernel is the lineality space of `C₂`. -/
lemma helperForCorollary_20_3_1_projection_image_closed_right
    {n : ℕ} {C₂ : Set (Fin n → ℝ)}
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂) (hC₂closed : IsClosed C₂)
    {L : Submodule ℝ (Fin n → ℝ)}
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂) :
    IsClosed (π '' C₂) := by
  let e := euclideanEquiv n
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C₂
  let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (e.symm.toLinearMap).comp (π.comp e.toLinearMap)
  have hC₂ne' : C'.Nonempty := by
    rcases hC₂ne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    exact ⟨x, hx, by simp⟩
  have hC₂conv' : Convex ℝ C' := hC₂conv.linear_image e.symm.toLinearMap
  let hhome := (e.symm.toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hC₂closed' : IsClosed C' := by
    have hclosed' :
        IsClosed ((hhome : _ → _) '' C₂) :=
      (hhome.isClosed_image (s := C₂)).2 hC₂closed
    simpa [C', hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hC₂cl : closure C' = C' := hC₂closed'.closure_eq
  have hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C') → A z = 0 →
        z ∈ Set.linealitySpace (closure C') := by
    intro z _hz0 _hzrec hzA
    have hzAeq : e (A z) = π (e z) := by
      simp [A]
    have hzA0 : e (A z) = 0 := by
      have hzA' := congrArg e hzA
      simpa using hzA'
    have hzAker : π (e z) = 0 := by
      simpa [hzAeq] using hzA0
    have hzker : e z ∈ LinearMap.ker π := by
      exact (LinearMap.mem_ker).2 hzAker
    have hzL : e z ∈ L := by
      simpa [hker] using hzker
    have hzlinealC₂ : e z ∈ linealitySpace_fin C₂ := by
      rw [← hL]
      exact hzL
    have hzrecC₂ : e z ∈ Set.recessionCone C₂ := hzlinealC₂.2
    have hznegC₂ : -e z ∈ Set.recessionCone C₂ := by
      simpa using hzlinealC₂.1
    have hrecC₂' :
        Set.recessionCone C' = e.symm '' Set.recessionCone C₂ := by
      simpa [C'] using
        (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C₂))
    have hzrecC₂' : z ∈ Set.recessionCone C' := by
      have hzmem : z ∈ e.symm '' Set.recessionCone C₂ := by
        refine ⟨e z, hzrecC₂, ?_⟩
        simp
      simpa [hrecC₂'] using hzmem
    have hznegC₂' : -z ∈ Set.recessionCone C' := by
      have hzmem : -z ∈ e.symm '' Set.recessionCone C₂ := by
        refine ⟨-e z, hznegC₂, ?_⟩
        simp
      simpa [hrecC₂'] using hzmem
    have hzneg' : z ∈ -Set.recessionCone C' := by
      simpa using hznegC₂'
    have hzlinealC₂' :
        z ∈ Set.linealitySpace C' := by
      have : z ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' :=
        ⟨hzneg', hzrecC₂'⟩
      simpa [Set.linealitySpace] using this
    simpa [hC₂cl] using hzlinealC₂'
  have hclosure :
      closure (A '' C') = A '' closure C' :=
    (linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
      (n := n) (m := n) (C := C') hC₂ne' hC₂conv' A hlineal).1
  have hclosedA : IsClosed (A '' C') := by
    have hcl' : closure (A '' C') = A '' C' := by
      simpa [hC₂cl] using hclosure
    exact (closure_eq_iff_isClosed).1 hcl'
  have hAeq : A '' C' = e.symm '' (π '' C₂) := by
    ext y
    constructor
    · rintro ⟨x, hxC', rfl⟩
      rcases hxC' with ⟨x₀, hx₀C, hx₀eq⟩
      have hx₀ : x = e.symm x₀ := hx₀eq.symm
      have hAx : A x = e.symm (π x₀) := by
        simp [A, hx₀]
      have hxK : π x₀ ∈ π '' C₂ := by
        exact ⟨x₀, hx₀C, rfl⟩
      refine ⟨π x₀, hxK, ?_⟩
      exact hAx.symm
    · rintro ⟨y₀, hy₀K, rfl⟩
      rcases hy₀K with ⟨x₀, hx₀C, rfl⟩
      refine ⟨e.symm x₀, ?_, ?_⟩
      · exact ⟨x₀, hx₀C, rfl⟩
      · simp [A]
  have hclosedK' : IsClosed (e.symm '' (π '' C₂)) := by
    simpa [hAeq] using hclosedA
  let hhome' := (e.toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosedK :
      IsClosed (π '' C₂) := by
    have hclosedK'' :
        IsClosed ((hhome' : _ → _) '' (e.symm '' (π '' C₂))) :=
      (hhome'.isClosed_image (s := e.symm '' (π '' C₂))).2 hclosedK'
    simpa [hhome', AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosedK''
  exact hclosedK

/-- Helper for Corollary 20.3.1: for a polyhedral left set, every projected recession
direction lifts to an original recession direction. -/
lemma helperForCorollary_20_3_1_recessionLift_leftProjection_of_polyhedral
    {n : ℕ} {C₁ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₁conv : Convex ℝ C₁)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} :
    ∀ z : Fin n → ℝ,
      z ∈ Set.recessionCone (π '' C₁) →
      ∃ y : Fin n → ℝ, y ∈ Set.recessionCone C₁ ∧ π y = z := by
  classical
  have hTFAE :
      [IsPolyhedralConvexSet n C₁,
        (IsClosed C₁ ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C₁ C'}.Finite),
        IsFinitelyGeneratedConvexSet n C₁].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C₁) hC₁conv
  have hCfg : IsFinitelyGeneratedConvexSet n C₁ := (hTFAE.out 0 2).1 hC₁poly
  rcases hCfg with ⟨S₀, S₁, hS₀finite, hS₁finite, hEqC₁⟩
  let I₀ : Type := {x : Fin n → ℝ // x ∈ S₀}
  let I₁ : Type := {x : Fin n → ℝ // x ∈ S₁}
  letI : Fintype I₀ := hS₀finite.fintype
  letI : Fintype I₁ := hS₁finite.fintype
  let e₀ : I₀ ≃ Fin (Fintype.card I₀) := Fintype.equivFin I₀
  let e₁ : I₁ ≃ Fin (Fintype.card I₁) := Fintype.equivFin I₁
  let pointGen : Fin (Fintype.card I₀) → Fin n → ℝ := fun i => (e₀.symm i).1
  let dirGen : Fin (Fintype.card I₁) → Fin n → ℝ := fun j => (e₁.symm j).1
  have hRangePoint : Set.range pointGen = S₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e₀.symm i).2
    · intro hx
      refine ⟨e₀ ⟨x, hx⟩, ?_⟩
      simp [pointGen]
  have hRangeDir : Set.range dirGen = S₁ := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e₁.symm j).2
    · intro hx
      refine ⟨e₁ ⟨x, hx⟩, ?_⟩
      simp [dirGen]
  have hEqC₁' :
      C₁ = mixedConvexHull (n := n) (Set.range pointGen) (Set.range dirGen) := by
    simpa [hRangePoint, hRangeDir] using hEqC₁
  have hImageEq :
      π '' C₁ =
        mixedConvexHull (n := n)
          (Set.range (fun i => π (pointGen i)))
          (Set.range (fun j => π (dirGen j))) := by
    calc
      π '' C₁ =
          π '' mixedConvexHull (n := n) (Set.range pointGen) (Set.range dirGen) := by
            simpa [hEqC₁']
      _ =
          mixedConvexHull (n := n)
            (Set.range (fun i => π (pointGen i)))
            (Set.range (fun j => π (dirGen j))) :=
          helperForCorollary_19_1_2_linearImage_mixedConvexHull_range
            (n := n) (p := n) (k := Fintype.card I₀) (m := Fintype.card I₁)
            π pointGen dirGen
  have hRecC₁Eq :
      Set.recessionCone C₁ =
        mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) (Set.range dirGen) := by
    have hpolyData :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n) (C := C₁) hC₁ne hC₁poly
    exact
      hpolyData.2.2 (Set.range pointGen) (Set.range dirGen)
        (Set.finite_range pointGen) (Set.finite_range dirGen) hEqC₁'
  have hC₁projNe : (π '' C₁).Nonempty := by
    rcases hC₁ne with ⟨x, hx⟩
    exact ⟨π x, ⟨x, hx, rfl⟩⟩
  have hC₁projPoly : IsPolyhedralConvexSet n (π '' C₁) :=
    (polyhedralConvexSet_image_preimage_linear n n π).1 C₁ hC₁poly
  have hRecProjEq :
      Set.recessionCone (π '' C₁) =
        mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ))
          (Set.range (fun j => π (dirGen j))) := by
    have hpolyDataProj :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n) (C := π '' C₁) hC₁projNe hC₁projPoly
    exact
      hpolyDataProj.2.2
        (Set.range (fun i => π (pointGen i)))
        (Set.range (fun j => π (dirGen j)))
        (Set.finite_range (fun i => π (pointGen i)))
        (Set.finite_range (fun j => π (dirGen j)))
        hImageEq
  let pointGenZero : Fin 1 → Fin n → ℝ := fun _ => 0
  have hRangeZero :
      Set.range pointGenZero = ({0} : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, rfl⟩
      simp [pointGenZero]
    · intro hx
      simpa [pointGenZero] using hx
  have hRangeZeroProj :
      Set.range (fun i : Fin 1 => π (pointGenZero i)) = ({0} : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, rfl⟩
      simp [pointGenZero]
    · intro hx
      simpa [pointGenZero] using hx
  have hRecC₁EqRange :
      Set.recessionCone C₁ =
        mixedConvexHull (n := n) (Set.range pointGenZero) (Set.range dirGen) := by
    simpa [hRangeZero] using hRecC₁Eq
  have hImageRecEq :
      π '' Set.recessionCone C₁ =
        mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ))
          (Set.range (fun j => π (dirGen j))) := by
    have hImageRecEqRange :
        π '' Set.recessionCone C₁ =
          mixedConvexHull (n := n)
            (Set.range (fun i : Fin 1 => π (pointGenZero i)))
            (Set.range (fun j => π (dirGen j))) := by
      calc
        π '' Set.recessionCone C₁ =
            π '' mixedConvexHull (n := n) (Set.range pointGenZero) (Set.range dirGen) := by
              simpa [hRecC₁EqRange]
        _ =
            mixedConvexHull (n := n)
              (Set.range (fun i : Fin 1 => π (pointGenZero i)))
              (Set.range (fun j => π (dirGen j))) :=
            helperForCorollary_19_1_2_linearImage_mixedConvexHull_range
              (n := n) (p := n) (k := 1) (m := Fintype.card I₁) π pointGenZero dirGen
    simpa [hRangeZeroProj] using hImageRecEqRange
  intro z hz
  have hzMix :
      z ∈ mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ))
        (Set.range (fun j => π (dirGen j))) := by
    simpa [hRecProjEq] using hz
  have hzImage : z ∈ π '' Set.recessionCone C₁ := by
    simpa [hImageRecEq] using hzMix
  rcases hzImage with ⟨y, hyRec, hyEq⟩
  exact ⟨y, hyRec, hyEq⟩

/-- Helper for Corollary 20.3.1: under the lineality-kernel projection setup for `C₂`,
projected recession directions lift to recession directions of `C₂`. -/
lemma helperForCorollary_20_3_1_recessionLift_rightProjection_of_linealityKernel
    {n : ℕ} {C₂ : Set (Fin n → ℝ)}
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂)
    {L W : Submodule ℝ (Fin n → ℝ)} (hWL : IsCompl W L)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hrange : LinearMap.range π = W)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂) :
    ∀ z : Fin n → ℝ,
      z ∈ Set.recessionCone (π '' C₂) →
      ∃ y : Fin n → ℝ, y ∈ Set.recessionCone C₂ ∧ π y = z := by
  let K : Set (Fin n → ℝ) := π '' C₂
  have hpre :
      C₂ = π ⁻¹' K ∧ K ⊆ (W : Set (Fin n → ℝ)) ∧ K.Nonempty := by
    simpa [K] using
      (helperForTheorem_19_1_projection_preimage_image_eq_of_linealityKernel
        (n := n) (C := C₂) hC₂conv hC₂ne (L := L) (W := W) hWL (π := π) hker hrange hL)
  have hC₂pre : C₂ = π ⁻¹' K := hpre.1
  have hKsubset : K ⊆ (W : Set (Fin n → ℝ)) := hpre.2.1
  have hKne : K.Nonempty := hpre.2.2
  intro z hz
  have hzW : z ∈ (W : Set (Fin n → ℝ)) :=
    (helperForTheorem_19_1_recessionCone_subset_submodule
      (n := n) (K := K) (W := W) hKsubset hKne) hz
  have hzRange : z ∈ LinearMap.range π := by
    simpa [hrange] using hzW
  rcases hzRange with ⟨y, hyEq⟩
  have hyRecC₂ : y ∈ Set.recessionCone C₂ := by
    intro x hx t ht
    have hxK : π x ∈ K := by
      exact ⟨x, hx, rfl⟩
    have hxtK : π x + t • z ∈ K := hz hxK ht
    have hpi : π (x + t • y) = π x + t • z := by
      simp [hyEq]
    have hpreMem : x + t • y ∈ π ⁻¹' K := by
      simpa [hpi] using hxtK
    simpa [hC₂pre] using hpreMem
  exact ⟨y, hyRecC₂, hyEq⟩

/-- Helper for Corollary 20.3.1: combining left/right recession lifts with the
common-recession projection condition rules out nonzero common projected directions. -/
lemma helperForCorollary_20_3_1_projection_noCommonRecession_from_lifts
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₁conv : Convex ℝ C₁)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂)
    {L W : Submodule ℝ (Fin n → ℝ)} (hWL : IsCompl W L)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hrange : LinearMap.range π = W)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂)
    (hcommonProjZero :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone C₂ →
        π y = 0) :
    ∀ z : Fin n → ℝ,
      z ≠ 0 →
      z ∈ Set.recessionCone (π '' C₁) →
      z ∈ Set.recessionCone (π '' C₂) →
      False := by
  intro z hz0 hzC₁ hzC₂
  rcases
      helperForCorollary_20_3_1_recessionLift_leftProjection_of_polyhedral
        (C₁ := C₁) hC₁ne hC₁conv hC₁poly (π := π) z hzC₁ with
    ⟨y₁, hy₁Rec, hy₁Proj⟩
  rcases
      helperForCorollary_20_3_1_recessionLift_rightProjection_of_linealityKernel
        (C₂ := C₂) hC₂ne hC₂conv (L := L) (W := W) hWL
        (π := π) hker hrange hL z hzC₂ with
    ⟨y₂, hy₂Rec, hy₂Proj⟩
  have hdiffKer : y₁ - y₂ ∈ LinearMap.ker π := by
    apply (LinearMap.mem_ker).2
    calc
      π (y₁ - y₂) = π y₁ - π y₂ := by simp
      _ = z - z := by simp [hy₁Proj, hy₂Proj]
      _ = 0 := sub_self z
  have hdiffLineal : y₁ - y₂ ∈ linealitySpace_fin C₂ := by
    have hdiffL : y₁ - y₂ ∈ L := by
      simpa [hker] using hdiffKer
    have hdiffSet : y₁ - y₂ ∈ (L : Set (Fin n → ℝ)) := hdiffL
    simpa [hL] using hdiffSet
  have hy₁RecC₂ : y₁ ∈ Set.recessionCone C₂ := by
    intro x hx t ht
    have hxShift : x + t • y₂ ∈ C₂ := hy₂Rec hx ht
    rcases
        helperForTheorem_19_1_linealitySpace_isSubmodule
          (n := n) (C := C₂) hC₂conv with
      ⟨L₂, hL₂⟩
    have hdiffL₂ : y₁ - y₂ ∈ L₂ := by
      have hdiffSet : y₁ - y₂ ∈ (L₂ : Set (Fin n → ℝ)) := by
        simpa [hL₂] using hdiffLineal
      exact hdiffSet
    have hscaledLineal : t • (y₁ - y₂) ∈ linealitySpace_fin C₂ := by
      have hscaledL₂ : t • (y₁ - y₂) ∈ L₂ := by
        exact L₂.smul_mem t hdiffL₂
      have hscaledSet : t • (y₁ - y₂) ∈ (L₂ : Set (Fin n → ℝ)) := hscaledL₂
      simpa [hL₂] using hscaledSet
    have hsumMem : (x + t • y₂) + t • (y₁ - y₂) ∈ C₂ := by
      exact
        (helperForTheorem_19_1_add_sub_mem_of_mem_linealitySpace_fin
          (n := n) (C := C₂) hC₂conv hscaledLineal hxShift).1
    have hsum :
        (x + t • y₂) + t • (y₁ - y₂) = x + t • y₁ := by
      calc
        (x + t • y₂) + t • (y₁ - y₂)
            = x + (t • y₂ + t • (y₁ - y₂)) := by abel
        _ = x + (t • y₂ + (t • y₁ - t • y₂)) := by
              simp [smul_sub]
        _ = x + t • y₁ := by
              abel
    simpa [hsum] using hsumMem
  have hy₁Zero : π y₁ = 0 :=
    hcommonProjZero y₁ hy₁Rec hy₁RecC₂
  have hzEqZero : z = 0 := by
    simpa [hy₁Proj] using hy₁Zero
  exact hz0 hzEqZero

/-- Helper for Corollary 20.3.1: if the projected sets have no nonzero common
recession direction, then the original difference is closed by projection/pullback. -/
lemma helperForCorollary_20_3_1_projectionBridge_isClosed_sub
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂closed : IsClosed C₂)
    {L : Submodule ℝ (Fin n → ℝ)}
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hker : LinearMap.ker π = L)
    (hL : (L : Set (Fin n → ℝ)) = linealitySpace_fin C₂)
    (hNoCommonProj :
      ∀ z : Fin n → ℝ,
        z ≠ 0 →
        z ∈ Set.recessionCone (π '' C₁) →
        z ∈ Set.recessionCone (π '' C₂) →
        False) :
    IsClosed (C₁ - C₂) := by
  have hC₁projPoly : IsPolyhedralConvexSet n (π '' C₁) :=
    (polyhedralConvexSet_image_preimage_linear n n π).1 C₁ hC₁poly
  have hC₁projClosed : IsClosed (π '' C₁) :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := π '' C₁) hC₁projPoly
  have hC₂projClosed : IsClosed (π '' C₂) :=
    helperForCorollary_20_3_1_projection_image_closed_right
      (C₂ := C₂) hC₂ne hC₂conv hC₂closed hker hL
  have hC₁projConv : Convex ℝ (π '' C₁) := hC₁conv.linear_image π
  have hC₂projConv : Convex ℝ (π '' C₂) := hC₂conv.linear_image π
  have hC₁projNe : (π '' C₁).Nonempty := by
    rcases hC₁ne with ⟨x, hx⟩
    exact ⟨π x, ⟨x, hx, rfl⟩⟩
  have hC₂projNe : (π '' C₂).Nonempty := by
    rcases hC₂ne with ⟨x, hx⟩
    exact ⟨π x, ⟨x, hx, rfl⟩⟩
  have hProjSubClosed : IsClosed ((π '' C₁) - (π '' C₂)) :=
    isClosed_sub_of_noCommonRecessionDirections n (π '' C₁) (π '' C₂)
      hC₁projNe hC₂projNe hC₁projClosed hC₂projClosed hC₁projConv hC₂projConv
      hNoCommonProj
  have hPreimageEq :
      C₁ - C₂ = π ⁻¹' ((π '' C₁) - (π '' C₂)) :=
    helperForCorollary_20_3_1_projection_preimage_sub_eq_projected_sub
      (C₁ := C₁) (C₂ := C₂) hC₂conv hker hL
  have hPreClosed : IsClosed (π ⁻¹' ((π '' C₁) - (π '' C₂))) :=
    hProjSubClosed.preimage π.continuous_of_finiteDimensional
  simpa [hPreimageEq] using hPreClosed

/-- Helper for Corollary 20.3.1: under the polyhedral/closed hypotheses and the
common-recession-lineality condition, the difference `C₁ - C₂` is closed. -/
lemma helperForCorollary_20_3_1_isClosed_sub_of_polyhedral_closed_commonRecLinear
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂closed : IsClosed C₂)
    (hcommonRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂) :
    IsClosed (C₁ - C₂) := by
  have hC₁closed : IsClosed C₁ :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C₁) hC₁poly
  rcases
      helperForTheorem_19_1_linealitySplit_projection_setup
        (n := n) (C := C₂) hC₂conv hC₂ne with
    ⟨L, hL, W, hWL, π, hker, hrange, hprojW, hprojL⟩
  have hcommonProjZero :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone C₂ →
        π y = 0 :=
    helperForCorollary_20_3_1_commonRec_projects_to_zero
      (C₁ := C₁) (C₂ := C₂) hcommonRecLinear hker hL
  have hNoCommonProj :
      ∀ z : Fin n → ℝ,
        z ≠ 0 →
        z ∈ Set.recessionCone (π '' C₁) →
        z ∈ Set.recessionCone (π '' C₂) →
        False := by
    exact
      helperForCorollary_20_3_1_projection_noCommonRecession_from_lifts
        (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₁conv hC₁poly hC₂ne hC₂conv
        hWL hker hrange hL hcommonProjZero
  exact
    helperForCorollary_20_3_1_projectionBridge_isClosed_sub
      (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₁conv hC₂conv hC₁poly hC₂closed hker hL hNoCommonProj

/-- Helper for Corollary 20.3.1: once `C₁ - C₂` is closed, disjointness implies
`0 ∉ closure (C₁ - C₂)`. -/
lemma helperForCorollary_20_3_1_zero_not_mem_closure_sub_of_commonRecLinear
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)))
    (hSubClosed : IsClosed (C₁ - C₂)) :
    (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) := by
  have hdisj : Disjoint C₁ C₂ :=
    helperForCorollary_20_3_1_disjoint_of_inter_eq_empty hinter
  exact
    helperForCorollary_19_3_3_zero_not_mem_closure_sub
      (n := n) (C₁ := C₁) (C₂ := C₂) hdisj hSubClosed

/-- Helper for Theorem 20.3: convert the opposite-recession hypothesis on `C₂` into
the common-recession-lineality hypothesis for the negated right set `-C₂`. -/
lemma helperForTheorem_20_3_commonRecLinear_for_negRight
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hcommonOppRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        -y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂) :
    ∀ y : Fin n → ℝ,
      y ∈ Set.recessionCone C₁ →
      y ∈ Set.recessionCone (-C₂) →
      y ∈ (-Set.recessionCone (-C₂)) ∩ Set.recessionCone (-C₂) := by
  intro y hyRecC₁ hyRecNegC₂
  have hyNegRecC₂ : -y ∈ Set.recessionCone C₂ :=
    (recessionCone_neg_set_iff (C := C₂) (y := y)).1 hyRecNegC₂
  have hyLinealC₂ :
      y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂ :=
    hcommonOppRecLinear y hyRecC₁ hyNegRecC₂
  have hyRecC₂ : y ∈ Set.recessionCone C₂ := hyLinealC₂.2
  have hyNegRecNegC₂ : y ∈ -Set.recessionCone (-C₂) := by
    have hnegMem : -y ∈ Set.recessionCone (-C₂) :=
      (recessionCone_neg_set_iff (C := C₂) (y := -y)).2 (by simpa using hyRecC₂)
    simpa [Set.mem_neg] using hnegMem
  exact ⟨hyNegRecNegC₂, hyRecNegC₂⟩

/-- Helper for Theorem 20.3: basic structural hypotheses are preserved under
negating the right-hand set. -/
lemma helperForTheorem_20_3_negRight_basicHypotheses
    {n : ℕ} {C₂ : Set (Fin n → ℝ)}
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂) (hC₂closed : IsClosed C₂) :
    (-C₂).Nonempty ∧ Convex ℝ (-C₂) ∧ IsClosed (-C₂) := by
  refine ⟨hC₂ne.neg, hC₂conv.neg, ?_⟩
  simpa using hC₂closed.neg

/-- Helper for Theorem 20.3: instantiate the closed-difference criterion with
right set `-C₂`. -/
lemma helperForTheorem_20_3_isClosed_sub_negRight
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂closed : IsClosed C₂)
    (hcommonOppRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        -y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂) :
    IsClosed (C₁ - (-C₂)) := by
  have hNegBasics :
      (-C₂).Nonempty ∧ Convex ℝ (-C₂) ∧ IsClosed (-C₂) :=
    helperForTheorem_20_3_negRight_basicHypotheses hC₂ne hC₂conv hC₂closed
  rcases hNegBasics with ⟨hNegNe, hNegConv, hNegClosed⟩
  have hCommonRecNegRight :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone (-C₂) →
        y ∈ (-Set.recessionCone (-C₂)) ∩ Set.recessionCone (-C₂) :=
    helperForTheorem_20_3_commonRecLinear_for_negRight
      (C₁ := C₁) (C₂ := C₂) hcommonOppRecLinear
  exact
    helperForCorollary_20_3_1_isClosed_sub_of_polyhedral_closed_commonRecLinear
      n C₁ (-C₂) hC₁ne hNegNe hC₁conv hNegConv hC₁poly hNegClosed hCommonRecNegRight

/-- Theorem 20.3: let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` with `C₁`
polyhedral and `C₂` closed. If every recession direction of `C₁` whose opposite is a
recession direction of `C₂` is a lineality direction of `C₂`, then `C₁ + C₂` is closed. -/
theorem Theorem_20_3
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂closed : IsClosed C₂)
    (hcommonOppRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        -y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂) :
    IsClosed (C₁ + C₂) := by
  have hSubClosed : IsClosed (C₁ - (-C₂)) :=
    helperForTheorem_20_3_isClosed_sub_negRight
      n C₁ C₂ hC₁ne hC₂ne hC₁conv hC₂conv hC₁poly hC₂closed hcommonOppRecLinear
  simpa [set_sub_eq_add_neg] using hSubClosed

/-- Corollary 20.3.1. Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` such that
`C₁` is polyhedral, `C₂` is closed, and `C₁ ∩ C₂ = ∅`. Suppose `C₁` and `C₂` have no
common directions of recession except directions in which `C₂` is linear. Then there exists
a hyperplane separating `C₁` and `C₂` strongly. -/
theorem Corollary_20_3_1
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂closed : IsClosed C₂)
    (hinter : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)))
    (hcommonRecLinear :
      ∀ y : Fin n → ℝ,
        y ∈ Set.recessionCone C₁ →
        y ∈ Set.recessionCone C₂ →
        y ∈ (-Set.recessionCone C₂) ∩ Set.recessionCone C₂) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := by
  have hSubClosed : IsClosed (C₁ - C₂) :=
    helperForCorollary_20_3_1_isClosed_sub_of_polyhedral_closed_commonRecLinear
      n C₁ C₂ hC₁ne hC₂ne hC₁conv hC₂conv hC₁poly hC₂closed hcommonRecLinear
  have h0notClosure : (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) :=
    helperForCorollary_20_3_1_zero_not_mem_closure_sub_of_commonRecLinear
      (C₁ := C₁) (C₂ := C₂) hinter hSubClosed
  exact
    helperForCorollary_19_3_3_apply_strongSeparation_iff
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₁conv hC₂conv h0notClosure


end Section20
end Chap04
