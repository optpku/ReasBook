/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part5

section Chap04
section Section21

set_option linter.unnecessarySimpa false

/-- Helper for Text 21.3.3: finite intersections of closed sets are closed in the
`{x | ∀ i ∈ J, x ∈ C i}` presentation. -/
lemma helperForText_21_3_3_isClosed_finiteIntersection
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hCclosed : ∀ i : I, IsClosed (C i))
    (J : Finset I) :
    IsClosed ({x : Fin n → ℝ | ∀ i ∈ J, x ∈ C i}) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      -- For the empty index family the intersection is `univ`.
      simpa using (isClosed_univ : IsClosed (Set.univ : Set (Fin n → ℝ)))
  | @insert i J hi hJclosed =>
      -- Split the inserted constraint into an intersection with the old finite intersection.
      have hset :
          {x : Fin n → ℝ | ∀ j ∈ insert i J, x ∈ C j} =
            C i ∩ {x : Fin n → ℝ | ∀ j ∈ J, x ∈ C j} := by
        ext x
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · exact hx i (by simp)
          · intro j hj
            exact hx j (by simp [hj])
        · intro hx j hj
          rcases hx with ⟨hxi, hxJ⟩
          rcases Finset.mem_insert.mp hj with hji | hjJ
          · simpa [hji] using hxi
          · exact hxJ j hjJ
      simpa [hset] using (hCclosed i).inter hJclosed

/-- Helper for Text 21.3.3: finite intersections of convex sets are convex in the
`{x | ∀ i ∈ J, x ∈ C i}` presentation. -/
lemma helperForText_21_3_3_convex_finiteIntersection
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hCconv : ∀ i : I, Convex ℝ (C i))
    (J : Finset I) :
    Convex ℝ ({x : Fin n → ℝ | ∀ i ∈ J, x ∈ C i}) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      -- For the empty index family the intersection is `univ`.
      simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ)))
  | @insert i J hi hJconv =>
      -- Split the inserted constraint into an intersection with the old finite intersection.
      have hset :
          {x : Fin n → ℝ | ∀ j ∈ insert i J, x ∈ C j} =
            C i ∩ {x : Fin n → ℝ | ∀ j ∈ J, x ∈ C j} := by
        ext x
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · exact hx i (by simp)
          · intro j hj
            exact hx j (by simp [hj])
        · intro hx j hj
          rcases hx with ⟨hxi, hxJ⟩
          rcases Finset.mem_insert.mp hj with hji | hjJ
          · simpa [hji] using hxi
          · exact hxJ j hjJ
      simpa [hset] using (hCconv i).inter hJconv

/-- Helper for Text 21.3.3: transport closedness of recession cones from Euclidean-space
coordinates to the `Fin n → ℝ` model. -/
lemma helperForText_21_3_3_recessionCone_isClosed_fin
    {n : ℕ}
    (S : Set (Fin n → ℝ))
    (hSclosed : IsClosed S) :
    IsClosed (Set.recessionCone S) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let S' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' S
  have hS'closed : IsClosed S' := by
    simpa [S'] using (Homeomorph.isClosed_image e.symm.toHomeomorph).2 hSclosed
  have hRecS'closed : IsClosed (Set.recessionCone S') :=
    recessionCone_isClosed_of_closed (C := S') hS'closed
  have hImageS : e '' S' = S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      rcases hy with ⟨z, hz, hyz⟩
      have hzEq : z = x := by
        calc
          z = e (e.symm z) := by simp
          _ = e y := by simpa [hyz]
          _ = x := hyx
      simpa [hzEq] using hz
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨x, hx, by simp⟩
      · simp
  have hRecEq : Set.recessionCone S = e '' Set.recessionCone S' := by
    have hEq := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := S')
    simpa [hImageS] using hEq
  have hImageClosed : IsClosed (e '' Set.recessionCone S') := by
    exact (Homeomorph.isClosed_image e.toHomeomorph).2 hRecS'closed
  simpa [hRecEq] using hImageClosed

/-- Helper for Text 21.3.3: transport `recessionCone_iInter_eq_iInter` from Euclidean-space
coordinates to the `Fin n → ℝ` model. -/
lemma helperForText_21_3_3_recessionCone_iInter_eq_iInter_fin
    {n : ℕ} {ι : Type*}
    (C : ι → Set (Fin n → ℝ))
    (hCclosed : ∀ i : ι, IsClosed (C i))
    (hCconv : ∀ i : ι, Convex ℝ (C i))
    (hCne : (⋂ i : ι, C i).Nonempty) :
    Set.recessionCone (⋂ i : ι, C i) = ⋂ i : ι, Set.recessionCone (C i) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let C' : ι → Set (EuclideanSpace ℝ (Fin n)) := fun i => e.symm '' C i
  have hC'closed : ∀ i : ι, IsClosed (C' i) := by
    intro i
    simpa [C'] using (Homeomorph.isClosed_image e.symm.toHomeomorph).2 (hCclosed i)
  have hC'conv : ∀ i : ι, Convex ℝ (C' i) := by
    intro i
    simpa [C'] using
      (Convex.linear_image (hCconv i)
        (e.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  have hC'ne : (⋂ i : ι, C' i).Nonempty := by
    rcases hCne with ⟨x, hx⟩
    have hxAll : ∀ i : ι, x ∈ C i := by
      simpa [Set.mem_iInter] using hx
    refine ⟨e.symm x, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    exact ⟨x, hxAll i, by simp⟩
  have hRecEuclid :
      Set.recessionCone (⋂ i : ι, C' i) = ⋂ i : ι, Set.recessionCone (C' i) :=
    recessionCone_iInter_eq_iInter (C := C') hC'closed hC'conv hC'ne
  have hImageInter :
      e '' (⋂ i : ι, C' i) = ⋂ i : ι, C i := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyAll : ∀ i : ι, y ∈ C' i := by
        simpa [Set.mem_iInter] using hy
      refine Set.mem_iInter.mpr ?_
      intro i
      rcases hyAll i with ⟨z, hz, hyz⟩
      have hzEq : z = x := by
        calc
          z = e (e.symm z) := by simp
          _ = e y := by simpa [hyz]
          _ = x := hyx
      simpa [hzEq] using hz
    · intro hx
      have hxAll : ∀ i : ι, x ∈ C i := by
        simpa [Set.mem_iInter] using hx
      refine ⟨e.symm x, ?_, ?_⟩
      · refine Set.mem_iInter.mpr ?_
        intro i
        exact ⟨x, hxAll i, by simp⟩
      · simp
  have hRecImage :
      Set.recessionCone (⋂ i : ι, C i) = e '' Set.recessionCone (⋂ i : ι, C' i) := by
    have hEq := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := (⋂ i : ι, C' i))
    simpa [hImageInter] using hEq
  have hImageInterRec :
      e '' (⋂ i : ι, Set.recessionCone (C' i)) = ⋂ i : ι, Set.recessionCone (C i) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyAll : ∀ i : ι, y ∈ Set.recessionCone (C' i) := by
        simpa [Set.mem_iInter] using hy
      refine Set.mem_iInter.mpr ?_
      intro i
      have hyi : y ∈ Set.recessionCone (C' i) := hyAll i
      have hRecImage_i :
          Set.recessionCone (C i) = e '' Set.recessionCone (C' i) := by
        have hEq_i := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C' i)
        have hImage_i : e '' C' i = C i := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨w, hw, hwz⟩
            rcases hw with ⟨u, hu, hwu⟩
            have huEq : u = z := by
              calc
                u = e (e.symm u) := by simp
                _ = e w := by simpa [hwu]
                _ = z := hwz
            simpa [huEq] using hu
          · intro hz
            refine ⟨e.symm z, ?_, ?_⟩
            · exact ⟨z, hz, by simp⟩
            · simp
        simpa [hImage_i] using hEq_i
      have hxInImage : x ∈ e '' Set.recessionCone (C' i) := ⟨y, hyi, hyx⟩
      simpa [hRecImage_i] using hxInImage
    · intro hx
      have hxAll : ∀ i : ι, x ∈ Set.recessionCone (C i) := by
        simpa [Set.mem_iInter] using hx
      refine ⟨e.symm x, ?_, ?_⟩
      · refine Set.mem_iInter.mpr ?_
        intro i
        have hRecImageSymm_i :
            Set.recessionCone (C' i) = e.symm '' Set.recessionCone (C i) := by
          simpa [C'] using
            (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C i))
        have hxInImage : e.symm x ∈ e.symm '' Set.recessionCone (C i) :=
          ⟨x, hxAll i, by simp⟩
        simpa [hRecImageSymm_i] using hxInImage
      · simp
  -- Route correction: finish the Fin-model theorem by transporting both sides of the
  -- Euclidean `iInter` identity through the same linear equivalence.
  calc
    Set.recessionCone (⋂ i : ι, C i) = e '' Set.recessionCone (⋂ i : ι, C' i) := hRecImage
    _ = e '' (⋂ i : ι, Set.recessionCone (C' i)) := by simp [hRecEuclid]
    _ = ⋂ i : ι, Set.recessionCone (C i) := hImageInterRec


end Section21
end Chap04
