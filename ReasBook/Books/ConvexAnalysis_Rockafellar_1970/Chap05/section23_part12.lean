/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11

section Chap05
section Section23

/-- Helper for Corollary 23.7.1: for a bounded closed convex set away from the origin, the closure
of its cone hull is already the generated convex cone. -/
lemma helperForCorollary_23_7_1_closure_convexConeHull_eq_convexConeGenerated {n : ℕ}
    {S : Set (Fin n → ℝ)} (hSne : Set.Nonempty S) (hSclosed : IsClosed S)
    (hSbdd : Bornology.IsBounded S) (hSconv : Convex ℝ S) (h0 : (0 : Fin n → ℝ) ∉ S) :
    closure ↑(ConvexCone.hull ℝ S) = convexConeGenerated n S := by
  -- The generated cone is closed by Corollary 9.6.1, so it remains to show that adjoining `0`
  -- does not change the closure of the cone hull when `S` is nonempty.
  have hclosedCone : IsClosed (convexConeGenerated n S) :=
    closed_convexConeGenerated_of_bounded hSne hSclosed hSbdd hSconv h0
  have hzero_mem_closure_hull :
      (0 : Fin n → ℝ) ∈ closure ((ConvexCone.hull ℝ S : Set (Fin n → ℝ))) := by
    rcases hSne with ⟨x, hxS⟩
    have hxHull : x ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) :=
      ConvexCone.subset_hull (R := ℝ) (s := S) hxS
    have hx0 : x ≠ 0 := by
      intro hx0
      exact h0 (hx0 ▸ hxS)
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    have hnormpos : 0 < ‖x‖ := by
      simpa using (norm_pos_iff.mpr hx0)
    have hnormne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hnormpos
    let t : ℝ := ε / (2 * ‖x‖)
    have htpos : 0 < t := by
      have hdenpos : 0 < (2 * ‖x‖) := by
        nlinarith [hnormpos]
      exact div_pos hε hdenpos
    have htxHull : t • x ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) :=
      ConvexCone.smul_mem (C := ConvexCone.hull ℝ S) htpos hxHull
    refine ⟨t • x, htxHull, ?_⟩
    have hnorm : ‖t • x‖ = ε / 2 := by
      calc
        ‖t • x‖ = ‖t‖ * ‖x‖ := by
          simpa using (norm_smul t x)
        _ = t * ‖x‖ := by
          have htabs : ‖t‖ = t := by
            simp [Real.norm_eq_abs, abs_of_pos htpos]
          simp [htabs]
        _ = ε / 2 := by
          have hcalc : t * ‖x‖ * 2 = ε := by
            dsimp [t]
            field_simp [hnormne, mul_comm, mul_left_comm, mul_assoc]
          linarith
    have hhalf : ε / 2 < ε := by
      linarith
    simpa [dist_eq_norm, hnorm] using hhalf
  have hclosureGenerated :
      closure (convexConeGenerated n S) = closure ((ConvexCone.hull ℝ S : Set (Fin n → ℝ))) := by
    have hKdef :
        convexConeGenerated n S =
          ({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        have hx' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
          simpa [convexConeGenerated, Set.mem_insert_iff] using hx
        rcases hx' with hx0 | hxHull
        · left
          simpa [Set.mem_singleton_iff] using hx0
        · right
          exact hxHull
      · intro hx
        rcases hx with hx0 | hxHull
        · have hx0' : x = 0 := by
            simpa [Set.mem_singleton_iff] using hx0
          exact (Set.mem_insert_iff).2 (Or.inl hx0')
        · exact (Set.mem_insert_iff).2 (Or.inr hxHull)
    calc
      closure (convexConeGenerated n S) =
          closure (({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ S : Set (Fin n → ℝ))) := by
            simp [hKdef]
      _ =
          closure ({0} : Set (Fin n → ℝ)) ∪
            closure ((ConvexCone.hull ℝ S : Set (Fin n → ℝ))) := by
            simpa using
              (closure_union
                (s := ({0} : Set (Fin n → ℝ)))
                (t := (ConvexCone.hull ℝ S : Set (Fin n → ℝ))))
      _ = closure ((ConvexCone.hull ℝ S : Set (Fin n → ℝ))) := by
            apply Set.union_eq_right.mpr
            intro x hx
            have hx0 : x = 0 := by
              have hx' : x ∈ ({0} : Set (Fin n → ℝ)) := by
                simpa [closure_singleton] using hx
              simpa [Set.mem_singleton_iff] using hx'
            simpa [hx0] using hzero_mem_closure_hull
  calc
    closure ↑(ConvexCone.hull ℝ S) = closure (convexConeGenerated n S) := by
      simpa using hclosureGenerated.symm
    _ = convexConeGenerated n S := by
      exact (closure_eq_iff_isClosed (s := convexConeGenerated n S)).2 hclosedCone

/-- Helper for Corollary 23.7.1: membership in the generated cone of a nonempty convex set is
equivalent to being a nonnegative scalar multiple of some point of the set. -/
lemma helperForCorollary_23_7_1_mem_convexConeGenerated_iff_exists_nonneg_smul {n : ℕ}
    {S : Set (Fin n → ℝ)} (hSconv : Convex ℝ S) (hSne : Set.Nonempty S) {v : Fin n → ℝ} :
    v ∈ convexConeGenerated n S ↔ ∃ a : ℝ, 0 ≤ a ∧ ∃ y ∈ S, v = a • y := by
  constructor
  · intro hv
    have hv' : v = 0 ∨ v ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hv
    rcases hv' with rfl | hvHull
    · rcases hSne with ⟨y, hyS⟩
      -- The zero vector is the zero multiple of any point of a nonempty set.
      exact ⟨0, le_rfl, y, hyS, by simp⟩
    · rcases (ConvexCone.mem_hull_of_convex (s := S) hSconv).1 hvHull with ⟨a, ha_pos, haS⟩
      rcases haS with ⟨y, hyS, rfl⟩
      exact ⟨a, le_of_lt ha_pos, y, hyS, rfl⟩
  · rintro ⟨a, ha_nonneg, y, hyS, rfl⟩
    by_cases ha0 : a = 0
    · -- The degenerate coefficient gives the origin, which is built into `convexConeGenerated`.
      have hv0 : a • y = (0 : Fin n → ℝ) := by simp [ha0]
      have hmem0 : (0 : Fin n → ℝ) ∈ convexConeGenerated n S := by
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa [hv0]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using ha0)
      have hyHull : y ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) :=
        ConvexCone.subset_hull (R := ℝ) (s := S) hyS
      have hayHull : a • y ∈ (ConvexCone.hull ℝ S : Set (Fin n → ℝ)) :=
        ConvexCone.smul_mem (C := ConvexCone.hull ℝ S) ha_pos hyHull
      -- Positive multiples already lie in the cone hull, hence in the generated cone.
      have hmem : a • y ∈ convexConeGenerated n S := by
        exact (Set.mem_insert_iff).2 (Or.inr hayHull)
      simpa

/-- Corollary 23.7.1: Let `f` be a proper convex function, and let `x` be an interior point of
`dom f` such that `f x` is not the minimum value of `f`. If
`C = {z | f z ≤ f x}`, then a vector `xStar` belongs to the Euclidean realization of the
normal cone of `C` at `x` if and only if there exists `λ ≥ 0` and a Euclidean subgradient
`y ∈ ∂f(x)` such that `xStar = λ • y`. -/
theorem mem_euclideanNormalCone_sublevelSet_iff_exists_nonneg_smul_mem_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hnotmin : ∃ z, f z < f x) :
    xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z : Fin n → ℝ | f z ≤ f x} x) ↔
      ∃ a : ℝ, 0 ≤ a ∧
        ∃ y ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x), xStar = a • y := by
  let S : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hsub_bdd :
      Set.Nonempty (subdifferentialAt f x) ∧ Bornology.IsBounded S := by
    -- The interior-point clause in Theorem 23.4 gives both subdifferentiability and boundedness.
    simpa [S] using
      (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x).2.2.1.2 hx
  have hsub : Set.Nonempty (subdifferentialAt f x) := hsub_bdd.1
  have hSbdd : Bornology.IsBounded S := hsub_bdd.2
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :
      f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite (0 : Module.Dual ℝ (Fin n → ℝ))
  have hSclosed : IsClosed S := by
    -- Theorem 23.2 identifies the vectorized subdifferential as a closed set.
    simpa [S] using h23_2.2.1
  have hSconv : Convex ℝ S := by
    -- The same theorem also gives convexity.
    simpa [S] using h23_2.2.2.1
  have hSnonempty : Set.Nonempty S := by
    rcases hsub with ⟨g, hg⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
    simpa [S] using hg
  have h0 : (0 : Fin n → ℝ) ∉ S := by
    -- A non-minimizer cannot have the zero vector as a subgradient.
    simpa [S] using helperForCorollary_23_7_1_zero_not_mem_vectorizedSubdifferential f x hnotmin
  -- Rewrite the normal cone using Theorem 23.7, remove the closure by Corollary 9.6.1,
  -- and then unpack the cone membership into an explicit nonnegative scalar multiple.
  rw [normalCone_sublevelSet_eq_closure_convexConeHull_subdifferential f hproper x hsub hnotmin]
  rw [helperForCorollary_23_7_1_closure_convexConeHull_eq_convexConeGenerated
    (n := n) (S := S) hSnonempty hSclosed hSbdd hSconv h0]
  simpa [S] using
    (helperForCorollary_23_7_1_mem_convexConeGenerated_iff_exists_nonneg_smul
      (n := n) (S := S) hSconv hSnonempty (v := xStar))

end Section23
end Chap05
