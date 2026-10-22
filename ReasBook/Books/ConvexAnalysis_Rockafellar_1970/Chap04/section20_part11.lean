/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section01_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part14

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Theorem 20.2: from the left-`ri` emptiness hypothesis, extract a
right point in `ri(C₂)` that is outside `C₁`. -/
lemma helperForTheorem_20_2_exists_ri_right_point_outside_left_of_left_ri_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ))) :
    ∃ xR : Fin n → ℝ, xR ∈ intrinsicInterior ℝ C₂ ∧ xR ∉ C₁ := by
  rcases Set.Nonempty.intrinsicInterior hC₂conv hC₂ne with ⟨xR, hxRri⟩
  have hxRnotC₁ : xR ∉ C₁ := by
    intro hxRC₁
    have hxInter : xR ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hxRC₁, hxRri⟩
    have hxEmpty : xR ∈ (∅ : Set (Fin n → ℝ)) := by
      simpa [hleftRiEmpty] using hxInter
    exact hxEmpty.elim
  exact ⟨xR, hxRri, hxRnotC₁⟩

/-- Helper for Theorem 20.2: a strongly separating hyperplane yields a proper
separator that does not contain the right set. -/
lemma helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hStrong : ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂) :
    ∃ H : Set (Fin n → ℝ),
      HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  rcases hStrong with ⟨H, hHstrong⟩
  rcases hHstrong with ⟨hC₁ne, hC₂ne, b, β, hb0, hHdef, ε, hεpos, hcases⟩
  have hC₂neKeep : C₂.Nonempty := hC₂ne
  let B : Set (Fin n → ℝ) := {x : Fin n → ℝ | ‖x‖ ≤ (1 : ℝ)}
  have hcases' :
      ((C₁ + (ε • B) ⊆ {x : Fin n → ℝ | x ⬝ᵥ b < β} ∧
            C₂ + (ε • B) ⊆ {x : Fin n → ℝ | β < x ⬝ᵥ b}) ∨
        (C₂ + (ε • B) ⊆ {x : Fin n → ℝ | x ⬝ᵥ b < β} ∧
            C₁ + (ε • B) ⊆ {x : Fin n → ℝ | β < x ⬝ᵥ b})) := by
    simpa [B] using hcases
  have h0B : (0 : Fin n → ℝ) ∈ B := by
    simp [B]
  have h0EpsB : (0 : Fin n → ℝ) ∈ ε • B := by
    exact ⟨0, h0B, by simp⟩
  rcases hC₂ne with ⟨yC₂, hyC₂⟩
  have hyC₂Thick : yC₂ ∈ C₂ + (ε • B) := by
    refine ⟨yC₂, hyC₂, 0, h0EpsB, by simp⟩
  cases hcases' with
  | inl hSepSides =>
      rcases hSepSides with ⟨hC₁ThickLt, hC₂ThickGt⟩
      have hC₁Le : C₁ ⊆ {x : Fin n → ℝ | x ⬝ᵥ b ≤ β} := by
        intro x hxC₁
        have hxThick : x ∈ C₁ + (ε • B) := ⟨x, hxC₁, 0, h0EpsB, by simp⟩
        have hxLt : x ⬝ᵥ b < β := by
          simpa using (hC₁ThickLt hxThick)
        exact le_of_lt hxLt
      have hC₂Ge : C₂ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ b} := by
        intro y hyC₂
        have hyThick : y ∈ C₂ + (ε • B) := ⟨y, hyC₂, 0, h0EpsB, by simp⟩
        have hyGt : β < y ⬝ᵥ b := by
          simpa using (hC₂ThickGt hyThick)
        exact le_of_lt hyGt
      have hSep : HyperplaneSeparates n H C₁ C₂ := by
        exact ⟨hC₁ne, hC₂neKeep, b, β, hb0, hHdef, Or.inl ⟨hC₁Le, hC₂Ge⟩⟩
      have hC₂notSubsetH : ¬ C₂ ⊆ H := by
        intro hC₂subsetH
        have hyH : yC₂ ∈ H := hC₂subsetH hyC₂
        have hyEq : yC₂ ⬝ᵥ b = β := by
          simpa [hHdef] using hyH
        have hyGt : β < yC₂ ⬝ᵥ b := hC₂ThickGt hyC₂Thick
        exact (lt_irrefl β) (by simpa [hyEq] using hyGt)
      exact ⟨H, ⟨hSep, by
        intro hBoth
        exact hC₂notSubsetH hBoth.2⟩, hC₂notSubsetH⟩
  | inr hSepSides =>
      rcases hSepSides with ⟨hC₂ThickLt, hC₁ThickGt⟩
      have hC₂Le : C₂ ⊆ {x : Fin n → ℝ | x ⬝ᵥ b ≤ β} := by
        intro y hyC₂
        have hyThick : y ∈ C₂ + (ε • B) := ⟨y, hyC₂, 0, h0EpsB, by simp⟩
        have hyLt : y ⬝ᵥ b < β := by
          simpa using (hC₂ThickLt hyThick)
        exact le_of_lt hyLt
      have hC₁Ge : C₁ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ b} := by
        intro x hxC₁
        have hxThick : x ∈ C₁ + (ε • B) := ⟨x, hxC₁, 0, h0EpsB, by simp⟩
        have hxGt : β < x ⬝ᵥ b := by
          simpa using (hC₁ThickGt hxThick)
        exact le_of_lt hxGt
      have hSep : HyperplaneSeparates n H C₁ C₂ := by
        exact ⟨hC₁ne, hC₂neKeep, b, β, hb0, hHdef, Or.inr ⟨hC₂Le, hC₁Ge⟩⟩
      have hC₂notSubsetH : ¬ C₂ ⊆ H := by
        intro hC₂subsetH
        have hyH : yC₂ ∈ H := hC₂subsetH hyC₂
        have hyEq : yC₂ ⬝ᵥ b = β := by
          simpa [hHdef] using hyH
        have hyLt : yC₂ ⬝ᵥ b < β := hC₂ThickLt hyC₂Thick
        exact (lt_irrefl β) (by simpa [hyEq] using hyLt)
      exact ⟨H, ⟨hSep, by
        intro hBoth
        exact hC₂notSubsetH hBoth.2⟩, hC₂notSubsetH⟩

/-- Helper for Theorem 20.2: `C₁ ∩ C₂` is convex under polyhedral-left and convex-right
hypotheses. -/
lemma helperForTheorem_20_2_convex_leftInterRight_of_polyLeft_convexRight
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁) (hC₂conv : Convex ℝ C₂) :
    Convex ℝ (C₁ ∩ C₂) := by
  have hC₁conv : Convex ℝ C₁ :=
    helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
  exact hC₁conv.inter hC₂conv

/-- Helper for Theorem 20.2: the intersection set is contained in the right set. -/
lemma helperForTheorem_20_2_leftInterRight_subset_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)} :
    (C₁ ∩ C₂ : Set (Fin n → ℝ)) ⊆ C₂ := by
  intro x hx
  exact hx.2

/-- Helper for Theorem 20.2: from `C₁ ∩ ri(C₂) = ∅`, deduce
`(C₁ ∩ C₂) ∩ ri(C₂) = ∅` in disjointness form. -/
lemma helperForTheorem_20_2_disjoint_leftInterRight_intrinsicInterior_right_of_left_ri_empty
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ))) :
    Disjoint (C₁ ∩ C₂) (intrinsicInterior ℝ C₂) := by
  refine Set.disjoint_left.2 ?_
  intro x hxInter hxri
  have hxC₁ : x ∈ C₁ := hxInter.1
  have hxLeftRi : x ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hxC₁, hxri⟩
  have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
    simpa [hleftRiEmpty] using hxLeftRi
  exact hxEmpty.elim

/-- Helper for Theorem 20.2: if `C₁` lies in the closed half-space
`β ≤ x ⬝ᵥ b`, then the level intersection `C₁ ∩ {x | x ⬝ᵥ b = β}` is a face of
`C₁`. -/
lemma helperForTheorem_20_2_isFace_level_intersection_of_left_ge
    {n : ℕ} {C₁ : Set (Fin n → ℝ)} {b : Fin n → ℝ} {β : ℝ}
    (hC₁ge : C₁ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ b})
    (hC₁conv : Convex ℝ C₁) :
    IsFace (𝕜 := ℝ) C₁ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) := by
  have hC₁leNeg : C₁ ⊆ closedHalfSpaceLE n (-b) (-β) := by
    intro x hxC₁
    have hxGe : β ≤ x ⬝ᵥ b := hC₁ge hxC₁
    have hxLeNeg : -(x ⬝ᵥ b) ≤ -β := neg_le_neg hxGe
    simpa [closedHalfSpaceLE, dotProduct_neg] using hxLeNeg
  have hFaceNeg :
      IsFace (𝕜 := ℝ) C₁ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ (-b) = -β}) :=
    helperForTheorem_19_1_isFace_of_tightConstraint
      (C := C₁) (b := -b) (β := -β) hC₁leNeg hC₁conv
  simpa [dotProduct_neg] using hFaceNeg

/-- Helper for Theorem 20.2: if a proper separator contains `C₂` and is represented by
`x ⬝ᵥ b = β`, then `C₁` is not entirely contained in that level set. -/
lemma helperForTheorem_20_2_not_subset_level_of_proper_with_right_subset_level
    {n : ℕ} {C₁ C₂ H : Set (Fin n → ℝ)}
    (hHproper : HyperplaneSeparatesProperly n H C₁ C₂)
    {b : Fin n → ℝ} {β : ℝ}
    (hHdef : H = {x : Fin n → ℝ | x ⬝ᵥ b = β})
    (hC₂subsetH : C₂ ⊆ H) :
    ¬ C₁ ⊆ {x : Fin n → ℝ | x ⬝ᵥ b = β} := by
  intro hC₁subsetLevel
  have hC₁subsetH : C₁ ⊆ H := by
    simpa [hHdef] using hC₁subsetLevel
  exact hHproper.2 ⟨hC₁subsetH, hC₂subsetH⟩

/-- Helper for Theorem 20.2: the level-face induced by a supporting inequality of a
polyhedral left set is itself polyhedral. -/
lemma helperForTheorem_20_2_polyhedral_level_face_of_left_ge
    {n : ℕ} {C₁ : Set (Fin n → ℝ)} {b : Fin n → ℝ} {β : ℝ}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₁ge : C₁ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ b})
    (hC₁conv : Convex ℝ C₁) :
    IsPolyhedralConvexSet n (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) := by
  have hFace : IsFace (𝕜 := ℝ) C₁ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) :=
    helperForTheorem_20_2_isFace_level_intersection_of_left_ge
      (C₁ := C₁) (b := b) (β := β) hC₁ge hC₁conv
  have hFconv : Convex ℝ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) := by
    refine hC₁conv.inter ?_
    intro x hx y hy a c ha hc hac
    have hxEq : x ⬝ᵥ b = β := hx
    have hyEq : y ⬝ᵥ b = β := hy
    refine ?_
    calc
      (a • x + c • y) ⬝ᵥ b = a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) := by
        simp [smul_dotProduct, add_dotProduct]
      _ = a * β + c * β := by
        simp [hxEq, hyEq]
      _ = (a + c) * β := by ring
      _ = β := by simpa [hac]
  exact
    polyhedralConvexSet_face (n := n)
      (C := C₁) (F := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) hC₁poly hFace hFconv

/-- D-route entry point for Theorem 20.2:
if `D := C₁ ∩ aff C₂` is nonempty, Theorem 11.3 gives oriented proper-separator
data between `D` and `C₂`, and this separator cannot contain all of `C₂`. -/
lemma helperForTheorem_20_2_droute_oriented_data_of_nonempty_left_inter_affineSpan
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hDne : (C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))).Nonempty) :
    ∃ c : Fin n → ℝ, ∃ γ : ℝ,
      c ≠ 0 ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ c < γ) ∧
        (∀ x : Fin n → ℝ,
          x ∈ (C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))) → γ ≤ x ⬝ᵥ c) := by
  let D : Set (Fin n → ℝ) := C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))
  have hC₁conv : Convex ℝ C₁ :=
    helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
  have hDconv : Convex ℝ D := by
    exact hC₁conv.inter (AffineSubspace.convex (Q := affineSpan ℝ C₂))
  have hDriDisj : Disjoint (intrinsicInterior ℝ D) (intrinsicInterior ℝ C₂) := by
    refine Set.disjoint_left.2 ?_
    intro x hxriD hxriC₂
    have hxD : x ∈ D := intrinsicInterior_subset hxriD
    have hxInter : x ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hxD.1, hxriC₂⟩
    have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
      simpa [hleftRiEmpty] using hxInter
    exact hxEmpty.elim
  rcases
      (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior
        n D C₂ hDne hC₂ne hDconv hC₂conv).2 hDriDisj with
    ⟨H, hHproper⟩
  rcases hyperplaneSeparatesProperly_oriented n H D C₂ hHproper with
    ⟨c, γ, hc0, hHdef, hDge, hC₂le, _hnotBoth⟩
  have hC₂notSubsetH : ¬ C₂ ⊆ H := by
    intro hC₂subsetH
    have hHaff : IsAffineSet n H := by
      simpa [hHdef] using dotProduct_levelset_isAffine n γ c
    have hAffC₂SubsetH : (affineSpan ℝ C₂ : Set (Fin n → ℝ)) ⊆ H := by
      simpa [affineHull] using
        affineHull_subset_of_affineSet (n := n) (S := C₂) (M := H) hHaff hC₂subsetH
    have hDsubsetH : D ⊆ H := by
      intro x hxD
      exact hAffC₂SubsetH hxD.2
    exact hHproper.2 ⟨hDsubsetH, hC₂subsetH⟩
  have hyRstrict : ∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ c < γ := by
    rcases Set.not_subset.mp hC₂notSubsetH with ⟨yR, hyRC₂, hyRnotH⟩
    have hyRne : yR ⬝ᵥ c ≠ γ := by
      intro hyReq
      apply hyRnotH
      simpa [hHdef, hyReq]
    have hyRle : yR ⬝ᵥ c ≤ γ := hC₂le yR hyRC₂
    exact ⟨yR, hyRC₂, lt_of_le_of_ne hyRle hyRne⟩
  exact ⟨c, γ, hc0, hC₂le, hyRstrict, by simpa [D] using hDge⟩

/-- Affine subsets of `ℝ^n` are polyhedral convex sets. -/
lemma helperForTheorem_20_2_affineSet_polyhedral
    {n : ℕ} {M : Set (Fin n → ℝ)}
    (hMaff : IsAffineSet n M) :
    IsPolyhedralConvexSet n M := by
  rcases (affineSet_iff_eq_mulVec (m := 0) (n := n) (b := (0 : Fin 0 → ℝ)) (B := 0)).2
      M hMaff with
    ⟨m, b, B, hMrepr⟩
  have hFiberEq :
      {x : Fin n → ℝ | B.mulVec x = b} =
        {x : Fin n → ℝ | ∀ i : Fin m, x ⬝ᵥ B i = b i} := by
    ext x
    constructor
    · intro hx i
      have hxi := congrArg (fun f : Fin m → ℝ => f i) hx
      simpa [Matrix.mulVec, dotProduct_comm] using hxi
    · intro hx
      ext i
      simpa [Matrix.mulVec, dotProduct_comm] using hx i
  have hFiberPoly :
      IsPolyhedralConvexSet n {x : Fin n → ℝ | B.mulVec x = b} := by
    have hEqPoly :
        IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin m, x ⬝ᵥ B i = b i} := by
      simpa using
        (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
          n m 0 (fun i : Fin m => B i) b
          (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
    simpa [hFiberEq] using hEqPoly
  simpa [hMrepr] using hFiberPoly

/-- The affine span of any subset of `ℝ^n` is polyhedral convex. -/
lemma helperForTheorem_20_2_affineSpan_polyhedral
    {n : ℕ} (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n (affineSpan ℝ C : Set (Fin n → ℝ)) := by
  exact
    helperForTheorem_20_2_affineSet_polyhedral
      (n := n)
      ((isAffineSet_iff_affineSubspace n (affineSpan ℝ C : Set (Fin n → ℝ))).2
        ⟨affineSpan ℝ C, rfl⟩)

/-- D-route empty-intersection branch for Theorem 20.2:
if `C₁ ∩ aff C₂ = ∅`, strongly separate `C₁` from `aff C₂`, then restrict to `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_empty_left_inter_affineSpan
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hDempty : C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ)) = (∅ : Set (Fin n → ℝ))) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  let A : Set (Fin n → ℝ) := (affineSpan ℝ C₂ : Set (Fin n → ℝ))
  have hApoly : IsPolyhedralConvexSet n A := by
    simpa [A] using helperForTheorem_20_2_affineSpan_polyhedral (n := n) C₂
  have hAne : A.Nonempty := by
    simpa [A] using (affineSpan_nonempty (k := ℝ) (s := C₂)).2 hC₂ne
  have hC₁disjA : Disjoint C₁ A := by
    refine Set.disjoint_left.2 ?_
    intro x hxC₁ hxA
    have hxD : x ∈ C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ)) := ⟨hxC₁, by simpa [A] using hxA⟩
    have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
      rw [← hDempty]
      exact hxD
    exact hxEmpty.elim
  have hStrongC₁A : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ A := by
    exact
      exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
        (n := n) (C₁ := C₁) (C₂ := A)
        hC₁ne hAne hC₁disjA hC₁poly hApoly
  have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
    rcases hStrongC₁A with ⟨Hs, hHs⟩
    refine ⟨Hs, ?_⟩
    exact
      hyperplaneSeparatesStrongly_mono_sets
        (hH := hHs)
        (hB₁ := by intro x hx; exact hx)
        (hB₂ := by
          intro y hyC₂
          exact subset_affineSpan (k := ℝ) (s := C₂) hyC₂)
        hC₁ne hC₂ne
  exact
    helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
      (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂

/-- Helper for Theorem 20.2: singleton sets in `ℝ^n` are polyhedral convex. -/
lemma helperForTheorem_20_2_singleton_polyhedral
    {n : ℕ} (xR : Fin n → ℝ) :
    IsPolyhedralConvexSet n ({xR} : Set (Fin n → ℝ)) := by
  let a : Fin n → Fin n → ℝ := fun i => Pi.single i (1 : ℝ)
  let α : Fin n → ℝ := fun i => xR i
  have hpolySystem :
      IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin n, x ⬝ᵥ a i = α i} := by
    simpa using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        n n 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
  have hEq :
      {x : Fin n → ℝ | ∀ i : Fin n, x ⬝ᵥ a i = α i}
        = ({xR} : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      have hxcoord : ∀ i : Fin n, x i = xR i := by
        intro i
        have hxi : x ⬝ᵥ a i = α i := hx i
        simpa [a, α] using hxi
      exact Set.mem_singleton_iff.mpr (funext hxcoord)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      intro i
      simp [a, α]
  simpa [hEq] using hpolySystem

/-- Helper for Theorem 20.2: orient a proper separator between a boundary face
and a singleton point into usable `(c, γ)` data. -/
lemma helperForTheorem_20_2_face_point_oriented_data_of_proper_not_contain_singleton
    {n : ℕ} {C₁ : Set (Fin n → ℝ)}
    {b0 : Fin n → ℝ} {β0 : ℝ} {x0 : Fin n → ℝ}
    (hFacePointProperNotContain :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesProperly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({x0} : Set (Fin n → ℝ)) ∧
        ¬ ({x0} : Set (Fin n → ℝ)) ⊆ Hs) :
    ∃ c : Fin n → ℝ, ∃ γ : ℝ,
      c ≠ 0 ∧
        (∀ x : Fin n → ℝ,
          x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c) ∧
        x0 ⬝ᵥ c < γ := by
  rcases hFacePointProperNotContain with ⟨Hs, hHsproper, hSingletonNotSubsetHs⟩
  have hx0notHs : x0 ∉ Hs := by
    intro hx0inHs
    apply hSingletonNotSubsetHs
    intro z hzSingleton
    have hzEq : z = x0 := by
      simpa [Set.mem_singleton_iff] using hzSingleton
    simpa [hzEq] using hx0inHs
  rcases
      hyperplaneSeparatesProperly_oriented n Hs
        (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
        ({x0} : Set (Fin n → ℝ))
        hHsproper with
    ⟨c, γ, hc0, hHsdef, hFace_ge, hSingleton_le, _hnotBothHs⟩
  have hx0le : x0 ⬝ᵥ c ≤ γ := hSingleton_le x0 (by simp)
  have hx0ne : x0 ⬝ᵥ c ≠ γ := by
    intro hxEq
    apply hx0notHs
    simpa [hHsdef, hxEq]
  have hx0lt : x0 ⬝ᵥ c < γ := lt_of_le_of_ne hx0le hx0ne
  exact ⟨c, γ, hc0, hFace_ge, hx0lt⟩

/-- Helper for Theorem 20.2: from oriented contains-right separator data, extract
the boundary-face branch split used by the Section 20 bridge:
either the level face is empty, or it strongly separates from a right intrinsic-interior
point outside `C₁`. -/
lemma helperForTheorem_20_2_boundary_face_case_split_of_oriented_contains_right_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂ne : C₂.Nonempty) (hC₂conv : Convex ℝ C₂)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    {b : Fin n → ℝ} {β : ℝ}
    (hC₁ge : C₁ ⊆ {x : Fin n → ℝ | β ≤ x ⬝ᵥ b}) :
    ∃ xR : Fin n → ℝ,
      xR ∈ intrinsicInterior ℝ C₂ ∧
      xR ∉ C₁ ∧
      ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) = (∅ : Set (Fin n → ℝ)) ∨
        ∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesStrongly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β})
            ({xR} : Set (Fin n → ℝ))) := by
  rcases
      helperForTheorem_20_2_exists_ri_right_point_outside_left_of_left_ri_empty
        (n := n) (C₁ := C₁) (C₂ := C₂) hC₂ne hC₂conv hleftRiEmpty with
    ⟨xR, hxRri, hxRnotC₁⟩
  by_cases hFempty : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) = (∅ : Set (Fin n → ℝ))
  · exact ⟨xR, hxRri, hxRnotC₁, Or.inl hFempty⟩
  · have hFne : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hFempty
    have hC₁conv : Convex ℝ C₁ :=
      helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
    have hFpoly :
        IsPolyhedralConvexSet n (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) :=
      helperForTheorem_20_2_polyhedral_level_face_of_left_ge
        (n := n) (C₁ := C₁) (b := b) (β := β) hC₁poly hC₁ge hC₁conv
    have hxRnotF : xR ∉ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) := by
      intro hxRF
      exact hxRnotC₁ hxRF.1
    have hFdisj : Disjoint (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β}) ({xR} : Set (Fin n → ℝ)) := by
      refine Set.disjoint_singleton_right.mpr ?_
      exact hxRnotF
    have hStrongFace :
        ∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesStrongly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β})
            ({xR} : Set (Fin n → ℝ)) := by
      exact
        exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
          (n := n)
          (C₁ := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b = β})
          (C₂ := ({xR} : Set (Fin n → ℝ)))
          hFne
          (Set.singleton_nonempty xR)
          hFdisj
          hFpoly
          (helperForTheorem_20_2_singleton_polyhedral (n := n) xR)
    exact ⟨xR, hxRri, hxRnotC₁, Or.inr hStrongFace⟩

/-- Case-2 geometry helper: if a half-space boundary contains all points of `M`,
and one positive-ray point `m0 + t0 • v` with `t0 > 0` also lies in the half-space,
then every nonnegative-ray point `m + t • v` with `m ∈ M`, `t ≥ 0` lies in it. -/
lemma helperForTheorem_20_2_halfspace_contains_nonneg_ray_bundle_of_contains_boundary_and_one_pos_point
    {n : ℕ} {M : Set (Fin n → ℝ)}
    {a v m0 : Fin n → ℝ} {t0 : ℝ}
    (hMzero : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = 0)
    (hm0M : m0 ∈ M) (ht0pos : 0 < t0)
    (hyLe : (m0 + t0 • v) ⬝ᵥ a ≤ 0) :
    ∀ m (t : ℝ), m ∈ M → 0 ≤ t → (m + t • v) ⬝ᵥ a ≤ 0 := by
  have hvLe : v ⬝ᵥ a ≤ 0 := by
    have hm0zero : m0 ⬝ᵥ a = 0 := hMzero m0 hm0M
    have hyEq : (m0 + t0 • v) ⬝ᵥ a = t0 * (v ⬝ᵥ a) := by
      calc
        (m0 + t0 • v) ⬝ᵥ a = m0 ⬝ᵥ a + (t0 • v) ⬝ᵥ a := by
          simp [add_dotProduct]
        _ = m0 ⬝ᵥ a + t0 * (v ⬝ᵥ a) := by
          simp [smul_dotProduct]
        _ = t0 * (v ⬝ᵥ a) := by
          simpa [hm0zero]
    have hmulLe : t0 * (v ⬝ᵥ a) ≤ 0 := by
      simpa [hyEq] using hyLe
    nlinarith
  intro m t hmM ht
  have hmzero : m ⬝ᵥ a = 0 := hMzero m hmM
  have hxEq : (m + t • v) ⬝ᵥ a = t * (v ⬝ᵥ a) := by
    calc
      (m + t • v) ⬝ᵥ a = m ⬝ᵥ a + (t • v) ⬝ᵥ a := by
        simp [add_dotProduct]
      _ = m ⬝ᵥ a + t * (v ⬝ᵥ a) := by
        simp [smul_dotProduct]
      _ = t * (v ⬝ᵥ a) := by
        simpa [hmzero]
  nlinarith [hxEq, hvLe, ht]

/-- Bundle-form corollary of the previous helper. -/
lemma helperForTheorem_20_2_subset_halfspace_of_nonneg_ray_bundle
    {n : ℕ} {M Cbundle : Set (Fin n → ℝ)}
    {a v m0 : Fin n → ℝ} {t0 : ℝ}
    (hBundle :
      Cbundle =
        {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • v})
    (hMzero : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = 0)
    (hm0M : m0 ∈ M) (ht0pos : 0 < t0)
    (hyLe : (m0 + t0 • v) ⬝ᵥ a ≤ 0) :
    Cbundle ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
  intro x hx
  rcases (show x ∈ {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • v} by
      simpa [hBundle] using hx) with ⟨m, hmM, t, ht, hxEq⟩
  subst hxEq
  exact
    helperForTheorem_20_2_halfspace_contains_nonneg_ray_bundle_of_contains_boundary_and_one_pos_point
      (n := n) (M := M) (a := a) (v := v) (m0 := m0) (t0 := t0)
      hMzero hm0M ht0pos hyLe m t hmM ht

/-- `γ`-level variant of the nonnegative-ray containment helper. -/
lemma helperForTheorem_20_2_level_halfspace_contains_nonneg_ray_bundle_of_contains_boundary_and_one_pos_point
    {n : ℕ} {M : Set (Fin n → ℝ)}
    {a v m0 : Fin n → ℝ} {t0 γ : ℝ}
    (hMlevel : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = γ)
    (hm0M : m0 ∈ M) (ht0pos : 0 < t0)
    (hyLe : (m0 + t0 • v) ⬝ᵥ a ≤ γ) :
    ∀ m (t : ℝ), m ∈ M → 0 ≤ t → (m + t • v) ⬝ᵥ a ≤ γ := by
  have hvLe : v ⬝ᵥ a ≤ 0 := by
    have hm0level : m0 ⬝ᵥ a = γ := hMlevel m0 hm0M
    have hyEq : (m0 + t0 • v) ⬝ᵥ a = γ + t0 * (v ⬝ᵥ a) := by
      calc
        (m0 + t0 • v) ⬝ᵥ a = m0 ⬝ᵥ a + (t0 • v) ⬝ᵥ a := by
          simp [add_dotProduct]
        _ = m0 ⬝ᵥ a + t0 * (v ⬝ᵥ a) := by
          simp [smul_dotProduct]
        _ = γ + t0 * (v ⬝ᵥ a) := by simpa [hm0level]
    have hmulLe : t0 * (v ⬝ᵥ a) ≤ 0 := by
      have : γ + t0 * (v ⬝ᵥ a) ≤ γ := by simpa [hyEq] using hyLe
      linarith
    nlinarith
  intro m t hmM ht
  have hmlevel : m ⬝ᵥ a = γ := hMlevel m hmM
  have hxEq : (m + t • v) ⬝ᵥ a = γ + t * (v ⬝ᵥ a) := by
    calc
      (m + t • v) ⬝ᵥ a = m ⬝ᵥ a + (t • v) ⬝ᵥ a := by
        simp [add_dotProduct]
      _ = m ⬝ᵥ a + t * (v ⬝ᵥ a) := by
        simp [smul_dotProduct]
      _ = γ + t * (v ⬝ᵥ a) := by simpa [hmlevel]
  have htvLe : t * (v ⬝ᵥ a) ≤ 0 := by nlinarith [hvLe, ht]
  linarith [hxEq, htvLe]

/-- Bundle-form corollary of the `γ`-level variant. -/
lemma helperForTheorem_20_2_subset_level_halfspace_of_nonneg_ray_bundle
    {n : ℕ} {M Cbundle : Set (Fin n → ℝ)}
    {a v m0 : Fin n → ℝ} {t0 γ : ℝ}
    (hBundle :
      Cbundle =
        {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • v})
    (hMlevel : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = γ)
    (hm0M : m0 ∈ M) (ht0pos : 0 < t0)
    (hyLe : (m0 + t0 • v) ⬝ᵥ a ≤ γ) :
    Cbundle ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ γ} := by
  intro x hx
  rcases (show x ∈ {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • v} by
      simpa [hBundle] using hx) with ⟨m, hmM, t, ht, hxEq⟩
  subst hxEq
  exact
    helperForTheorem_20_2_level_halfspace_contains_nonneg_ray_bundle_of_contains_boundary_and_one_pos_point
      (n := n) (M := M) (a := a) (v := v) (m0 := m0) (t0 := t0) (γ := γ)
      hMlevel hm0M ht0pos hyLe m t hmM ht

/-- Decompose a point along a codimension-one split generated by `v`:
`x = m + t • v`, with `m` on the level hyperplane `m ⬝ᵥ b = 0` and
`t = x ⬝ᵥ b`, assuming `v ⬝ᵥ b = 1`. -/
lemma helperForTheorem_20_2_decompose_along_level_hyperplane
    {n : ℕ} {b v x : Fin n → ℝ}
    (hv : v ⬝ᵥ b = (1 : ℝ)) :
    ∃ m : Fin n → ℝ, ∃ t : ℝ,
      m ⬝ᵥ b = 0 ∧ t = x ⬝ᵥ b ∧ x = m + t • v := by
  refine ⟨x - (x ⬝ᵥ b) • v, x ⬝ᵥ b, ?_, rfl, ?_⟩
  · calc
      (x - (x ⬝ᵥ b) • v) ⬝ᵥ b
          = x ⬝ᵥ b - ((x ⬝ᵥ b) • v) ⬝ᵥ b := by
              simp [sub_eq_add_neg, add_dotProduct]
      _ = x ⬝ᵥ b - (x ⬝ᵥ b) * (v ⬝ᵥ b) := by
            simp [smul_dotProduct]
      _ = x ⬝ᵥ b - (x ⬝ᵥ b) * 1 := by simpa [hv]
      _ = 0 := by ring
  · abel

/-- In a linear subspace `A`, a nonzero direction `v` with `v ⬝ᵥ c < 0` normalizes the
closed half `A ∩ {x | x ⬝ᵥ c ≤ 0}` into a nonnegative ray bundle over the boundary slice
`A ∩ {x | x ⬝ᵥ c = 0}`. -/
lemma helperForTheorem_20_2_closed_half_subspace_eq_nonneg_ray_bundle
    {n : ℕ} {A : Submodule ℝ (Fin n → ℝ)} {c v : Fin n → ℝ}
    (hvA : v ∈ A) (hvcLt : v ⬝ᵥ c < 0) :
    let u : Fin n → ℝ := (1 / (-(v ⬝ᵥ c))) • v
    {z : Fin n → ℝ | z ∈ (A : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c ≤ 0} =
      {z : Fin n → ℝ |
        ∃ m : Fin n → ℝ,
          m ∈ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c = 0} ∧
          ∃ t : ℝ, 0 ≤ t ∧ z = m + t • u} := by
  let u : Fin n → ℝ := (1 / (-(v ⬝ᵥ c))) • v
  have hvc_ne : v ⬝ᵥ c ≠ 0 := by
    linarith
  have huA : u ∈ A := by
    dsimp [u]
    exact A.smul_mem (1 / (-(v ⬝ᵥ c))) hvA
  have hu_negc : u ⬝ᵥ (-c) = (1 : ℝ) := by
    dsimp [u]
    calc
      ((1 / (-(v ⬝ᵥ c))) • v) ⬝ᵥ (-c)
          = (1 / (-(v ⬝ᵥ c))) * (v ⬝ᵥ (-c)) := by
              simp [smul_dotProduct]
      _ = (1 / (-(v ⬝ᵥ c))) * (-(v ⬝ᵥ c)) := by
            simp [dotProduct_neg]
      _ = 1 := by
            field_simp [hvc_ne]
  have hu_c : u ⬝ᵥ c = -1 := by
    have : u ⬝ᵥ (-c) = -(u ⬝ᵥ c) := by
      simp [dotProduct_neg]
    linarith [hu_negc, this]
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzA, hzLe⟩
    rcases
        helperForTheorem_20_2_decompose_along_level_hyperplane
          (n := n) (b := -c) (v := u) (x := z) hu_negc with
      ⟨m, t, hmLevel, htEq, hzEq⟩
    have ht_nonneg : 0 ≤ t := by
      have hzNegNonneg : 0 ≤ z ⬝ᵥ (-c) := by
        simpa [dotProduct_neg] using hzLe
      linarith [htEq, hzNegNonneg]
    have hmA : m ∈ A := by
      have hmEq : m = z - t • u := by
        calc
          m = m + t • u - t • u := by abel
          _ = z - t • u := by simpa [hzEq]
      rw [hmEq]
      exact A.sub_mem hzA (A.smul_mem t huA)
    have hmLevelC : m ⬝ᵥ c = 0 := by
      have hmNeg : m ⬝ᵥ (-c) = 0 := hmLevel
      simpa [dotProduct_neg] using hmNeg
    refine ⟨m, ⟨hmA, hmLevelC⟩, t, ht_nonneg, ?_⟩
    simpa [u] using hzEq
  · rintro ⟨m, hmM, t, ht, rfl⟩
    rcases hmM with ⟨hmA, hmLevelC⟩
    constructor
    · exact A.add_mem hmA (A.smul_mem t huA)
    · calc
        (m + t • u) ⬝ᵥ c = m ⬝ᵥ c + t * (u ⬝ᵥ c) := by
          simp [add_dotProduct, smul_dotProduct]
        _ = -t := by simp [hmLevelC, hu_c]
        _ ≤ 0 := by linarith

/-- In a linear subspace `A`, the corresponding strict half `A ∩ {x | x ⬝ᵥ c < 0}` is the
positive ray bundle over the same boundary slice. -/
lemma helperForTheorem_20_2_strict_half_subspace_eq_pos_ray_bundle
    {n : ℕ} {A : Submodule ℝ (Fin n → ℝ)} {c v : Fin n → ℝ}
    (hvA : v ∈ A) (hvcLt : v ⬝ᵥ c < 0) :
    let u : Fin n → ℝ := (1 / (-(v ⬝ᵥ c))) • v
    {z : Fin n → ℝ | z ∈ (A : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c < 0} =
      {z : Fin n → ℝ |
        ∃ m : Fin n → ℝ,
          m ∈ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c = 0} ∧
          ∃ t : ℝ, 0 < t ∧ z = m + t • u} := by
  let u : Fin n → ℝ := (1 / (-(v ⬝ᵥ c))) • v
  have hvc_ne : v ⬝ᵥ c ≠ 0 := by
    linarith
  have huA : u ∈ A := by
    dsimp [u]
    exact A.smul_mem (1 / (-(v ⬝ᵥ c))) hvA
  have hu_negc : u ⬝ᵥ (-c) = (1 : ℝ) := by
    dsimp [u]
    calc
      ((1 / (-(v ⬝ᵥ c))) • v) ⬝ᵥ (-c)
          = (1 / (-(v ⬝ᵥ c))) * (v ⬝ᵥ (-c)) := by
              simp [smul_dotProduct]
      _ = (1 / (-(v ⬝ᵥ c))) * (-(v ⬝ᵥ c)) := by
            simp [dotProduct_neg]
      _ = 1 := by
            field_simp [hvc_ne]
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzA, hzLt⟩
    rcases
        helperForTheorem_20_2_decompose_along_level_hyperplane
          (n := n) (b := -c) (v := u) (x := z) hu_negc with
      ⟨m, t, hmLevel, htEq, hzEq⟩
    have ht_pos : 0 < t := by
      have hzNegPos : 0 < z ⬝ᵥ (-c) := by
        simpa [dotProduct_neg] using hzLt
      linarith [htEq, hzNegPos]
    have hmA : m ∈ A := by
      have hmEq : m = z - t • u := by
        calc
          m = m + t • u - t • u := by abel
          _ = z - t • u := by simpa [hzEq]
      rw [hmEq]
      exact A.sub_mem hzA (A.smul_mem t huA)
    have hmLevelC : m ⬝ᵥ c = 0 := by
      have hmNeg : m ⬝ᵥ (-c) = 0 := hmLevel
      simpa [dotProduct_neg] using hmNeg
    refine ⟨m, ⟨hmA, hmLevelC⟩, t, ht_pos, ?_⟩
    simpa [u] using hzEq
  · rintro ⟨m, hmM, t, ht, rfl⟩
    rcases hmM with ⟨hmA, hmLevelC⟩
    constructor
    · exact A.add_mem hmA (A.smul_mem t huA)
    · have hu_c : u ⬝ᵥ c = -1 := by
        have : u ⬝ᵥ (-c) = -(u ⬝ᵥ c) := by
          simp [dotProduct_neg]
        linarith [hu_negc, this]
      calc
        (m + t • u) ⬝ᵥ c = m ⬝ᵥ c + t * (u ⬝ᵥ c) := by
          simp [add_dotProduct, smul_dotProduct]
        _ = -t := by simp [hmLevelC, hu_c]
        _ < 0 := by linarith

/-- Case-2 geometric sublemma (closed-half two-sides + same-side criterion):
if a closed ray-bundle half `Cclosed` has boundary level `m ⬝ᵥ a = γ` on `M`,
and one positive-ray point lies in the closed half-space `x ⬝ᵥ a ≤ γ`,
then all of `Cclosed` lies in `x ⬝ᵥ a ≤ γ`. -/
lemma helperForTheorem_20_2_closed_half_two_sides_same_side_contains_all
    {n : ℕ} {M Cclosed : Set (Fin n → ℝ)}
    {a v : Fin n → ℝ} {γ : ℝ}
    (hClosed :
      Cclosed =
        {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • v})
    (hBoundaryLevel : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = γ)
    (hRiPoint :
      ∃ m0 : Fin n → ℝ, ∃ _hm0 : m0 ∈ M, ∃ t0 : ℝ, 0 < t0 ∧ (m0 + t0 • v) ⬝ᵥ a ≤ γ) :
    Cclosed ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ γ} := by
  rcases hRiPoint with ⟨m0, hm0, t0, ht0pos, hyLe⟩
  exact
    helperForTheorem_20_2_subset_level_halfspace_of_nonneg_ray_bundle
      (n := n) (M := M) (Cbundle := Cclosed) (a := a) (v := v)
      (m0 := m0) (t0 := t0) (γ := γ)
      hClosed hBoundaryLevel hm0 ht0pos hyLe

/-- If a closed half of a linear subspace is written as
`A ∩ {x | x ⬝ᵥ c ≤ 0}` and a closed half-space with normal `a` contains its boundary slice
`A ∩ {x | x ⬝ᵥ c = 0}` together with one strict-half point, then it contains the whole closed half. -/
lemma helperForTheorem_20_2_halfspace_contains_closed_half_subspace_of_boundary_and_strict_meet
    {n : ℕ} {A : Submodule ℝ (Fin n → ℝ)} {a c v z0 : Fin n → ℝ}
    (hvA : v ∈ A) (hvcLt : v ⬝ᵥ c < 0)
    (hBoundary :
      ∀ m : Fin n → ℝ,
        m ∈ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c = 0} →
          m ⬝ᵥ a = 0)
    (hz0 :
      z0 ∈ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c < 0})
    (hz0Le : z0 ⬝ᵥ a ≤ 0) :
    {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c ≤ 0} ⊆
      {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
  let M : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c = 0}
  let Cclosed : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c ≤ 0}
  let u : Fin n → ℝ := (1 / (-(v ⬝ᵥ c))) • v
  have hClosedBundle :
      Cclosed =
        {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 ≤ t ∧ x = m + t • u} := by
    simpa [M, Cclosed, u] using
      helperForTheorem_20_2_closed_half_subspace_eq_nonneg_ray_bundle
        (A := A) (c := c) (v := v) hvA hvcLt
  have hStrictBundle :
      {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c < 0} =
        {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 < t ∧ x = m + t • u} := by
    simpa [M, u] using
      helperForTheorem_20_2_strict_half_subspace_eq_pos_ray_bundle
        (A := A) (c := c) (v := v) hvA hvcLt
  have hz0Bundle :
      z0 ∈ {x : Fin n → ℝ | ∃ m : Fin n → ℝ, m ∈ M ∧ ∃ t : ℝ, 0 < t ∧ x = m + t • u} := by
    rw [← hStrictBundle]
    exact hz0
  rcases hz0Bundle with
    ⟨m0, hm0M, t0, ht0pos, hz0Eq⟩
  have hBoundaryLevel : ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = 0 := by
    intro m hmM
    exact hBoundary m hmM
  have hz0LeBundle : (m0 + t0 • u) ⬝ᵥ a ≤ 0 := by
    simpa [hz0Eq] using hz0Le
  simpa [Cclosed] using
    helperForTheorem_20_2_closed_half_two_sides_same_side_contains_all
      (n := n) (M := M) (Cclosed := Cclosed) (a := a) (v := u) (γ := 0)
      hClosedBundle hBoundaryLevel ⟨m0, hm0M, t0, ht0pos, hz0LeBundle⟩

/-- Case-2 combinatorial core (second sentence in the textbook argument):
if `Ri` is not contained in an intersection `C' = ⋂ i, H i`, and each `H i`
that meets `Ri` must contain all of `Ri`, then some `H i` is disjoint from `Ri`. -/
lemma helperForTheorem_20_2_exists_disjoint_factor_of_not_subset_iInter_and_meet_implies_contains_all
    {n : ℕ} {ι : Type*}
    {Ri C' : Set (Fin n → ℝ)} {H : ι → Set (Fin n → ℝ)}
    (hC' : C' = ⋂ i, H i)
    (hRiNotSubset : ¬ Ri ⊆ C')
    (hMeetImpliesContainsAll :
      ∀ i, (∃ x : Fin n → ℝ, x ∈ Ri ∧ x ∈ H i) → Ri ⊆ H i) :
    ∃ i, Disjoint (H i) Ri := by
  rcases Set.not_subset.mp hRiNotSubset with ⟨y, hyRi, hyNotC'⟩
  have hyNotInter : y ∉ ⋂ i, H i := by
    simpa [hC'] using hyNotC'
  have hNotForall : ¬ ∀ i, y ∈ H i := by
    simpa [Set.mem_iInter] using hyNotInter
  rcases not_forall.mp hNotForall with ⟨i, hyNotHi⟩
  refine ⟨i, Set.disjoint_left.2 ?_⟩
  intro x hxHi hxRi
  have hRiSubsetHi : Ri ⊆ H i :=
    hMeetImpliesContainsAll i ⟨x, hxRi, hxHi⟩
  have hyHi : y ∈ H i := hRiSubsetHi hyRi
  exact hyNotHi hyHi

/-- Case-2 local algebra helper (translated/through-origin form):
if `M` is centrally symmetric (`m ∈ M → -m ∈ M`) and `M` lies in a closed
homogeneous half-space `x ⬝ᵥ a ≤ 0`, then every `m ∈ M` lies on its boundary
`m ⬝ᵥ a = 0`. -/
lemma helperForTheorem_20_2_boundary_eq_zero_of_neg_closed_subset_halfspace_zero
    {n : ℕ} {M : Set (Fin n → ℝ)} {a : Fin n → ℝ}
    (hMneg : ∀ m : Fin n → ℝ, m ∈ M → -m ∈ M)
    (hMsubset : M ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ (0 : ℝ)}) :
    ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = (0 : ℝ) := by
  intro m hmM
  have hmLe : m ⬝ᵥ a ≤ (0 : ℝ) := hMsubset hmM
  have hnegmLe : (-m) ⬝ᵥ a ≤ (0 : ℝ) := hMsubset (hMneg m hmM)
  have hmGe : (0 : ℝ) ≤ m ⬝ᵥ a := by
    have hnegLe : -(m ⬝ᵥ a) ≤ (0 : ℝ) := by
      simpa [dotProduct_neg] using hnegmLe
    linarith
  exact le_antisymm hmLe hmGe

/-- Polyhedral-cone factor extraction for the final step of the D-route shell:
if `C'` is a nonempty polyhedral convex cone, `Ri` is not contained in `C'`, and every
homogeneous closed half-space containing `C'` that meets `Ri` must contain all of `Ri`,
then some homogeneous factor half-space containing `C'` is disjoint from `Ri`. -/
lemma helperForTheorem_20_2_exists_homogeneous_factor_disjoint_of_not_subset_polyhedralCone
    {n : ℕ} {C' Ri : Set (Fin n → ℝ)}
    (hC'ne : C'.Nonempty)
    (hC'poly : IsPolyhedralConvexSet n C')
    (hC'cone : IsConeSet n C')
    (hRiNotSubset : ¬ Ri ⊆ C')
    (hMeetImpliesContainsAll :
      ∀ {a : Fin n → ℝ},
        a ≠ 0 →
        C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} →
        (∃ x : Fin n → ℝ, x ∈ Ri ∧ x ⬝ᵥ a ≤ 0) →
        Ri ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0}) :
    ∃ a : Fin n → ℝ,
      a ≠ 0 ∧
        C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} ∧
        Disjoint ({x : Fin n → ℝ | x ⬝ᵥ a ≤ 0}) Ri := by
  let ι : Type := {a : Fin n → ℝ // a ≠ 0 ∧ C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0}}
  let H : ι → Set (Fin n → ℝ) := fun i => {x : Fin n → ℝ | x ⬝ᵥ i.1 ≤ 0}
  have hC'conv : Convex ℝ C' :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C') hC'poly
  have hC'closed : IsClosed C' :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C') hC'poly
  have hC'convCone : IsConvexCone n C' := ⟨hC'cone, hC'conv⟩
  have hEqSigma :
      (⋂ i : ι, H i) = C' := by
    calc
      (⋂ i : ι, H i)
          =
            ⋂ (a : Fin n → ℝ) (_ha : a ≠ 0)
              (_hCa : C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0}),
                {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
                  ext x
                  constructor
                  · intro hx
                    refine Set.mem_iInter.2 ?_
                    intro a
                    refine Set.mem_iInter.2 ?_
                    intro ha
                    refine Set.mem_iInter.2 ?_
                    intro hCa
                    exact (Set.mem_iInter.mp hx) ⟨a, ha, hCa⟩
                  · intro hx
                    refine Set.mem_iInter.2 ?_
                    intro i
                    have hxi₁ :
                        x ∈
                          ⋂ (_ha : i.1 ≠ 0)
                            (_hCa : C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ i.1 ≤ 0}),
                              {x : Fin n → ℝ | x ⬝ᵥ i.1 ≤ 0} :=
                      (Set.mem_iInter.mp hx) i.1
                    have hxi₂ :
                        x ∈
                          ⋂ (_hCa : C' ⊆ {x : Fin n → ℝ | x ⬝ᵥ i.1 ≤ 0}),
                            {x : Fin n → ℝ | x ⬝ᵥ i.1 ≤ 0} :=
                      (Set.mem_iInter.mp hxi₁) i.2.1
                    exact (Set.mem_iInter.mp hxi₂) i.2.2
      _ = C' := by
            simpa using
              isClosed_convexCone_eq_iInter_homogeneous_closedHalfspaces
                (n := n) (K := C') hC'ne hC'closed hC'convCone
  have hMeetImpliesContainsAllSigma :
      ∀ i : ι, (∃ x : Fin n → ℝ, x ∈ Ri ∧ x ∈ H i) → Ri ⊆ H i := by
    intro i hMeet
    exact hMeetImpliesContainsAll i.2.1 i.2.2
      (by
        rcases hMeet with ⟨x, hxRi, hxHi⟩
        exact ⟨x, hxRi, hxHi⟩)
  rcases
      helperForTheorem_20_2_exists_disjoint_factor_of_not_subset_iInter_and_meet_implies_contains_all
        (Ri := Ri) (C' := C') (H := H) hEqSigma.symm hRiNotSubset hMeetImpliesContainsAllSigma with
    ⟨i, hHiDisj⟩
  exact ⟨i.1, i.2.1, i.2.2, hHiDisj⟩

/-- Case-2 local logic helper:
if `A` and `B` are disjoint and `B` is nonempty, then `B` is not a subset of `A`. -/
lemma helperForTheorem_20_2_not_subset_of_disjoint_and_nonempty
    {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hDisj : Disjoint A B) (hBne : B.Nonempty) :
    ¬ B ⊆ A := by
  intro hBsubA
  rcases hBne with ⟨x, hxB⟩
  have hxA : x ∈ A := hBsubA hxB
  exact hDisj.le_bot ⟨hxA, hxB⟩

/-- Case-2 C-step helper:
if a set `Ri` is stable under subtraction by all boundary directions in `M`,
and the cone part `K` is disjoint from `Ri`, then `Ri` cannot be contained in
the Minkowski sum `K + M`. This is the abstract form of the
`ri(C₂') ⊄ C₁' = K + M` step from `thm20.2C.md`. -/
lemma helperForTheorem_20_2_not_subset_sum_of_disjoint_and_sub_closed
    {n : ℕ} {K M Ri : Set (Fin n → ℝ)}
    (hRine : Ri.Nonempty)
    (hSubClosed :
      ∀ x : Fin n → ℝ, x ∈ Ri → ∀ m : Fin n → ℝ, m ∈ M → x - m ∈ Ri)
    (hDisj : Disjoint K Ri) :
    ¬ Ri ⊆ K + M := by
  intro hRiSub
  rcases hRine with ⟨x, hxRi⟩
  rcases hRiSub hxRi with ⟨k, hkK, m, hmM, hxEq⟩
  subst hxEq
  have hkRi : k ∈ Ri := by
    have hkSub : (k + m) - m ∈ Ri := hSubClosed (k + m) hxRi m hmM
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hkSub
  exact hDisj.le_bot ⟨hkK, hkRi⟩

/-- Case-2 shift helper:
shifting the membership condition for a Minkowski sum `K + M` by a base point
`mBase` rewrites it as a sum with the translated boundary-direction set
`{z | z + mBase ∈ M}`. -/
lemma helperForTheorem_20_2_shift_preimage_add_eq_add_shift_preimage
    {n : ℕ} {K M : Set (Fin n → ℝ)} {mBase : Fin n → ℝ} :
    {z : Fin n → ℝ | z + mBase ∈ K + M} =
      K + {z : Fin n → ℝ | z + mBase ∈ M} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨k, hkK, m, hmM, hzEq⟩
    refine ⟨k, hkK, m - mBase, ?_, ?_⟩
    · change (m - mBase) + mBase ∈ M
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmM
    · calc
        k + (m - mBase) = (k + m) - mBase := by abel
        _ = (z + mBase) - mBase := by simpa [hzEq]
        _ = z := by abel
  · intro hz
    rcases hz with ⟨k, hkK, m, hmShift, hzEq⟩
    refine ⟨k, hkK, m + mBase, ?_, ?_⟩
    · simpa using hmShift
    · calc
        k + (m + mBase) = (k + m) + mBase := by abel
        _ = z + mBase := by simpa [hzEq]

/-- Translating the carrier of a polyhedral convex set preserves polyhedrality. -/
lemma helperForTheorem_20_2_polyhedral_preimage_add_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsPolyhedralConvexSet n C)
    (a : Fin n → ℝ) :
    IsPolyhedralConvexSet n {z : Fin n → ℝ | z + a ∈ C} := by
  rcases hC with ⟨ι, hιfin, b, β, hCeq⟩
  refine ⟨ι, hιfin, b, fun i => β i - a ⬝ᵥ b i, ?_⟩
  ext z
  constructor
  · intro hz
    have hzC : z + a ∈ C := hz
    have hzIInter : z + a ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      simpa [hCeq] using hzC
    refine Set.mem_iInter.2 ?_
    intro i
    have hziMem : z + a ∈ closedHalfSpaceLE n (b i) (β i) :=
      (Set.mem_iInter.mp hzIInter) i
    have hziLe : (z + a) ⬝ᵥ b i ≤ β i := by
      simpa [closedHalfSpaceLE] using hziMem
    have hziShift : z ⬝ᵥ b i ≤ β i - a ⬝ᵥ b i := by
      have hdot : (z + a) ⬝ᵥ b i = z ⬝ᵥ b i + a ⬝ᵥ b i := by
        simp [add_dotProduct]
      linarith [hziLe, hdot]
    simpa [closedHalfSpaceLE] using hziShift
  · intro hz
    have hzIInter :
        z ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i - a ⬝ᵥ b i) := by
      simpa using hz
    have hzShiftIInter : z + a ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      refine Set.mem_iInter.2 ?_
      intro i
      have hziMem : z ∈ closedHalfSpaceLE n (b i) (β i - a ⬝ᵥ b i) :=
        (Set.mem_iInter.mp hzIInter) i
      have hziLe : z ⬝ᵥ b i ≤ β i - a ⬝ᵥ b i := by
        simpa [closedHalfSpaceLE] using hziMem
      have hziShift : (z + a) ⬝ᵥ b i ≤ β i := by
        have hdot : (z + a) ⬝ᵥ b i = z ⬝ᵥ b i + a ⬝ᵥ b i := by
          simp [add_dotProduct]
        linarith [hziLe, hdot]
      simpa [closedHalfSpaceLE] using hziShift
    have hzC : z + a ∈ C := by
      simpa [hCeq] using hzShiftIInter
    exact hzC

/-- Case-2 shift helper:
subtracting a boundary direction (zero `u`-level and zero `v`-level) preserves
membership in the strict translated half `{x | x ⬝ᵥ u = 0 ∧ x ⬝ᵥ v < 0}`. -/
lemma helperForTheorem_20_2_sub_preserves_zero_eq_strict_lt_levels
    {n : ℕ} {u v x m : Fin n → ℝ}
    (hx : x ⬝ᵥ u = 0 ∧ x ⬝ᵥ v < 0)
    (hm : m ⬝ᵥ u = 0 ∧ m ⬝ᵥ v = 0) :
    (x - m) ⬝ᵥ u = 0 ∧ (x - m) ⬝ᵥ v < 0 := by
  constructor
  · calc
      (x - m) ⬝ᵥ u = x ⬝ᵥ u - m ⬝ᵥ u := by
        simp [sub_eq_add_neg, add_dotProduct]
      _ = 0 := by simpa [hx.1, hm.1]
  · calc
      (x - m) ⬝ᵥ v = x ⬝ᵥ v - m ⬝ᵥ v := by
        simp [sub_eq_add_neg, add_dotProduct]
      _ = x ⬝ᵥ v := by simpa [hm.2]
      _ < 0 := hx.2

/-- If `0 ∈ C`, `Ri` is stable under positive rescaling, and `C` is disjoint from `Ri`,
then the closed convex cone generated by `C` is also disjoint from `Ri`. -/
lemma helperForTheorem_20_2_disjoint_closure_convexConeGenerated_of_zero_mem_disjoint_posScale
    {n : ℕ} {C Ri : Set (Fin n → ℝ)}
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hCpoly : IsPolyhedralConvexSet n C)
    (hRiPosScale :
      ∀ z : Fin n → ℝ, z ∈ Ri → ∀ lam : ℝ, 0 < lam → lam • z ∈ Ri)
    (hDisj : Disjoint C Ri) :
    Disjoint (closure (convexConeGenerated n C)) Ri := by
  have hCne : C.Nonempty := ⟨0, h0C⟩
  have hConeData :
      IsPolyhedralConvexSet n (closure (convexConeGenerated n C)) ∧
        IsConeSet n (closure (convexConeGenerated n C)) ∧
        closure (convexConeGenerated n C) =
          (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C :=
    polyhedralConvexCone_closure_convexConeGenerated
      (n := n) (C := C) hCne hCpoly
  have hConeEq :
      closure (convexConeGenerated n C) =
        (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C :=
    hConeData.2.2
  refine Set.disjoint_left.2 ?_
  intro k hkCone hkRi
  have hkCases :
      k ∈ (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∨
        k ∈ Set.recessionCone C := by
    rw [hConeEq] at hkCone
    simpa [Set.mem_union] using hkCone
  cases hkCases with
  | inl hkScaled =>
      rcases Set.mem_iUnion.mp hkScaled with ⟨lam, hkLam⟩
      rcases hkLam with ⟨z, hzC, rfl⟩
      have hlam_ne : (lam : ℝ) ≠ 0 := by
        linarith [lam.2]
      have hzRiScaled : (1 / (lam : ℝ)) • ((lam : ℝ) • z) ∈ Ri := by
        exact hRiPosScale ((lam : ℝ) • z) hkRi (1 / (lam : ℝ)) (one_div_pos.mpr lam.2)
      have hzRi : z ∈ Ri := by
        simpa [smul_smul, hlam_ne] using hzRiScaled
      exact hDisj.le_bot ⟨hzC, hzRi⟩
  | inr hkRec =>
      have hkC : k ∈ C := by
        have hkStep : (0 : Fin n → ℝ) + (1 : ℝ) • k ∈ C := hkRec h0C (by norm_num)
        simpa using hkStep
      exact hDisj.le_bot ⟨hkC, hkRi⟩

/-- If `mBase ∈ C ∩ A`, and `C` is disjoint from the strict affine half
`A ∩ {x | x ⬝ᵥ c < γ}`, then after translating by `mBase`, the closed convex cone
generated by `C - mBase` is disjoint from the strict linear half
`A.direction ∩ {z | z ⬝ᵥ c < 0}`. -/
lemma helperForTheorem_20_2_disjoint_shifted_cone_of_affine_strict_half_data
    {n : ℕ} {C : Set (Fin n → ℝ)} {A : AffineSubspace ℝ (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C)
    {mBase c : Fin n → ℝ} {γ : ℝ}
    (hmBaseC : mBase ∈ C)
    (hmBaseA : mBase ∈ A)
    (hmBasec : mBase ⬝ᵥ c = γ)
    (hDisj :
      Disjoint C {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c < γ}) :
    Disjoint
      (closure (convexConeGenerated n {z : Fin n → ℝ | z + mBase ∈ C}))
      {z : Fin n → ℝ | z ∈ (A.direction : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c < 0} := by
  let Cshift : Set (Fin n → ℝ) := {z : Fin n → ℝ | z + mBase ∈ C}
  let RiShift : Set (Fin n → ℝ) :=
    {z : Fin n → ℝ | z ∈ (A.direction : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c < 0}
  have h0Cshift : (0 : Fin n → ℝ) ∈ Cshift := by
    dsimp [Cshift]
    simpa using hmBaseC
  have hCshiftPoly : IsPolyhedralConvexSet n Cshift := by
    exact
      helperForTheorem_20_2_polyhedral_preimage_add_of_polyhedral
        (n := n) (C := C) hCpoly mBase
  have hRiShiftPosScale :
      ∀ z : Fin n → ℝ, z ∈ RiShift → ∀ lam : ℝ, 0 < lam → lam • z ∈ RiShift := by
    intro z hz lam hlamPos
    rcases hz with ⟨hzDir, hzcLt⟩
    constructor
    · exact A.direction.smul_mem lam hzDir
    · calc
        (lam • z) ⬝ᵥ c = lam * (z ⬝ᵥ c) := by
          simp [smul_dotProduct]
        _ < 0 := by
          exact mul_neg_of_pos_of_neg hlamPos hzcLt
  have hCshiftDisjRiShift : Disjoint Cshift RiShift := by
    refine Set.disjoint_left.2 ?_
    intro z hzCshift hzRiShift
    rcases hzRiShift with ⟨hzDir, hzcLt⟩
    have hzA : z + mBase ∈ A := by
      have hzVsub : z + mBase -ᵥ mBase ∈ A.direction := by
        simpa [vsub_eq_sub] using hzDir
      exact
        (AffineSubspace.vsub_right_mem_direction_iff_mem (s := A) hmBaseA (z + mBase)).1 hzVsub
    have hzStrict : (z + mBase) ⬝ᵥ c < γ := by
      calc
        (z + mBase) ⬝ᵥ c = z ⬝ᵥ c + mBase ⬝ᵥ c := by
          simp [add_dotProduct]
        _ < γ := by linarith [hzcLt, hmBasec]
    have hzBad : z + mBase ∈ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c < γ} :=
      ⟨hzA, hzStrict⟩
    exact hDisj.le_bot ⟨hzCshift, hzBad⟩
  exact
    helperForTheorem_20_2_disjoint_closure_convexConeGenerated_of_zero_mem_disjoint_posScale
      (n := n) (C := Cshift) (Ri := RiShift)
      h0Cshift hCshiftPoly hRiShiftPosScale hCshiftDisjRiShift

/-- Shifted-cone disjointness helper for the Section 20 Case-2 shell:
if `mBase` lies on the boundary level pair `(β0, γ)` and `xFace ∈ C₁` also lies on the
`b0`-boundary, then the translated left set
`C₁ - mBase = {z | z + mBase ∈ C₁}` generates no cone point with
zero `b0`-level and strictly negative `c`-level. -/
lemma helperForTheorem_20_2_disjoint_shifted_cone_of_boundary_face_data
    {n : ℕ} {C₁ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₁poly : IsPolyhedralConvexSet n C₁)
    {b0 c mBase xFace : Fin n → ℝ} {β0 γ : ℝ}
    (hxFace : xFace ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}))
    (hmBaseb0 : mBase ⬝ᵥ b0 = β0) (hmBasec : mBase ⬝ᵥ c = γ)
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c) :
    Disjoint
      (closure (convexConeGenerated n {z : Fin n → ℝ | z + mBase ∈ C₁}))
      {z : Fin n → ℝ | z ⬝ᵥ b0 = 0 ∧ z ⬝ᵥ c < 0} := by
  let Cshift : Set (Fin n → ℝ) := {z : Fin n → ℝ | z + mBase ∈ C₁}
  have hCshiftNe : Cshift.Nonempty := by
    rcases hC₁ne with ⟨x, hxC₁⟩
    refine ⟨x - mBase, ?_⟩
    change (x - mBase) + mBase ∈ C₁
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxC₁
  have hCshiftPoly : IsPolyhedralConvexSet n Cshift := by
    exact
      helperForTheorem_20_2_polyhedral_preimage_add_of_polyhedral
        (n := n) (C := C₁) hC₁poly mBase
  have hConeData :
      IsPolyhedralConvexSet n (closure (convexConeGenerated n Cshift)) ∧
        IsConeSet n (closure (convexConeGenerated n Cshift)) ∧
        closure (convexConeGenerated n Cshift) =
          (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • Cshift) ∪ Set.recessionCone Cshift :=
    polyhedralConvexCone_closure_convexConeGenerated
      (n := n) (C := Cshift) hCshiftNe hCshiftPoly
  have hConeEq :
      closure (convexConeGenerated n Cshift) =
        (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • Cshift) ∪ Set.recessionCone Cshift :=
    hConeData.2.2
  refine Set.disjoint_left.2 ?_
  intro k hkCone hkStrict
  have hkCases :
      k ∈ (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • Cshift) ∨
        k ∈ Set.recessionCone Cshift := by
    rw [hConeEq] at hkCone
    simpa [Set.mem_union] using hkCone
  rcases hkStrict with ⟨hkb0, hkcLt⟩
  rcases hxFace with ⟨hxFaceC₁, hxFaceb0⟩
  have hxFaceb0Eq : xFace ⬝ᵥ b0 = β0 := hxFaceb0
  have hxFacec_ge : γ ≤ xFace ⬝ᵥ c := hFace_ge xFace ⟨hxFaceC₁, hxFaceb0⟩
  cases hkCases with
  | inl hkScaled =>
      rcases Set.mem_iUnion.mp hkScaled with ⟨lam, hkLam⟩
      rcases hkLam with ⟨z, hzShift, rfl⟩
      have hlamPos : 0 < (lam : ℝ) := lam.2
      have hlamNe : (lam : ℝ) ≠ 0 := by linarith
      have hzC₁ : z + mBase ∈ C₁ := hzShift
      have hzb0 : z ⬝ᵥ b0 = 0 := by
        have hkEq : (lam : ℝ) * (z ⬝ᵥ b0) = 0 := by
          simpa [smul_dotProduct] using hkb0
        exact (mul_eq_zero.mp hkEq).resolve_left hlamNe
      have hzcLt : z ⬝ᵥ c < 0 := by
        have hkEq : ((lam : ℝ) * (z ⬝ᵥ c)) < 0 := by
          simpa [smul_dotProduct] using hkcLt
        by_contra hzcNotLt
        have hzcNonneg : 0 ≤ z ⬝ᵥ c := le_of_not_gt hzcNotLt
        have : 0 ≤ (lam : ℝ) * (z ⬝ᵥ c) := mul_nonneg (le_of_lt hlamPos) hzcNonneg
        exact (not_lt_of_ge this) hkEq
      have hFaceMem : z + mBase ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) := by
        refine ⟨hzC₁, ?_⟩
        calc
          (z + mBase) ⬝ᵥ b0 = z ⬝ᵥ b0 + mBase ⬝ᵥ b0 := by
            simp [add_dotProduct]
          _ = β0 := by simpa [hzb0, hmBaseb0]
      have hzmc_ge : γ ≤ (z + mBase) ⬝ᵥ c := hFace_ge (z + mBase) hFaceMem
      have hzc_ge : 0 ≤ z ⬝ᵥ c := by
        calc
          z ⬝ᵥ c = (z + mBase) ⬝ᵥ c - mBase ⬝ᵥ c := by
            simp [add_dotProduct]
          _ ≥ γ - γ := by linarith [hzmc_ge, hmBasec]
          _ = 0 := by ring
      exact (not_lt_of_ge hzc_ge) hzcLt
  | inr hkRec =>
      let zFace : Fin n → ℝ := xFace - mBase
      have hzFaceShift : zFace ∈ Cshift := by
        change zFace + mBase ∈ C₁
        dsimp [zFace, Cshift]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxFaceC₁
      have hzFaceb0 : zFace ⬝ᵥ b0 = 0 := by
        dsimp [zFace]
        calc
          (xFace - mBase) ⬝ᵥ b0 = xFace ⬝ᵥ b0 - mBase ⬝ᵥ b0 := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ = 0 := by linarith [hxFaceb0Eq, hmBaseb0]
      have hzFacec_ge : 0 ≤ zFace ⬝ᵥ c := by
        dsimp [zFace]
        calc
          (xFace - mBase) ⬝ᵥ c = xFace ⬝ᵥ c - mBase ⬝ᵥ c := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ ≥ 0 := by linarith [hxFacec_ge, hmBasec]
      have hkRecStep :
          ∀ t : ℝ, 0 ≤ t → zFace + t • k ∈ Cshift := by
        intro t ht
        exact hkRec hzFaceShift ht
      have hkc_nonneg : 0 ≤ k ⬝ᵥ c := by
        by_contra hkcNeg
        have hkcLt' : k ⬝ᵥ c < 0 := lt_of_not_ge hkcNeg
        let t : ℝ := (zFace ⬝ᵥ c + 1) / (-(k ⬝ᵥ c))
        have ht_nonneg : 0 ≤ t := by
          have hnum_nonneg : 0 ≤ zFace ⬝ᵥ c + 1 := by linarith [hzFacec_ge]
          have hden_nonneg : 0 ≤ -(k ⬝ᵥ c) := by linarith [hkcLt']
          exact div_nonneg hnum_nonneg hden_nonneg
        have hzStepShift : zFace + t • k ∈ Cshift := hkRecStep t ht_nonneg
        have hzStepC₁ : zFace + t • k + mBase ∈ C₁ := hzStepShift
        have hzStepb0 : (zFace + t • k + mBase) ⬝ᵥ b0 = β0 := by
          calc
            (zFace + t • k + mBase) ⬝ᵥ b0
                = zFace ⬝ᵥ b0 + t * (k ⬝ᵥ b0) + mBase ⬝ᵥ b0 := by
                    simp [add_dotProduct, smul_dotProduct]
            _ = β0 := by simpa [hzFaceb0, hkb0, hmBaseb0]
        have hzStepFace :
            zFace + t • k + mBase ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) :=
          ⟨hzStepC₁, hzStepb0⟩
        have hzStepc_ge : γ ≤ (zFace + t • k + mBase) ⬝ᵥ c :=
          hFace_ge (zFace + t • k + mBase) hzStepFace
        have hden_ne : (-(k ⬝ᵥ c)) ≠ 0 := by linarith [hkcLt']
        have ht_mul : t * (k ⬝ᵥ c) = -(zFace ⬝ᵥ c + 1) := by
          have hkc_ne : k ⬝ᵥ c ≠ 0 := by linarith [hkcLt']
          calc
            t * (k ⬝ᵥ c)
                = ((zFace ⬝ᵥ c + 1) / (-(k ⬝ᵥ c))) * (k ⬝ᵥ c) := by
                    rfl
            _ = (zFace ⬝ᵥ c + 1) * (-1) := by
                  field_simp [hden_ne, hkc_ne]
            _ = -(zFace ⬝ᵥ c + 1) := by ring
        have hzStepcEq : (zFace + t • k) ⬝ᵥ c = -1 := by
          calc
            (zFace + t • k) ⬝ᵥ c = zFace ⬝ᵥ c + t * (k ⬝ᵥ c) := by
              simp [add_dotProduct, smul_dotProduct]
            _ = -1 := by linarith [ht_mul]
        have hzStepcLtγ : (zFace + t • k + mBase) ⬝ᵥ c < γ := by
          calc
            (zFace + t • k + mBase) ⬝ᵥ c
                = (zFace + t • k) ⬝ᵥ c + mBase ⬝ᵥ c := by
                    simp [add_dotProduct]
            _ < γ := by linarith [hzStepcEq, hmBasec]
        exact (not_lt_of_ge hzStepc_ge) hzStepcLtγ
      exact (not_lt_of_ge hkc_nonneg) hkcLt

/-- Case-2 local geometry helper:
if `M` is closed under reflection about `m0` and lies in the closed half-space
`x ⬝ᵥ a ≤ β`, while `m0` is on the boundary `m0 ⬝ᵥ a = β`, then every point of
`M` lies on that boundary. -/
lemma helperForTheorem_20_2_boundary_eq_of_reflective_subset_halfspace
    {n : ℕ} {M : Set (Fin n → ℝ)} {a m0 : Fin n → ℝ} {β : ℝ}
    (hm0M : m0 ∈ M)
    (hMreflect : ∀ m : Fin n → ℝ, m ∈ M → (2 : ℝ) • m0 - m ∈ M)
    (hMsubset : M ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ β})
    (hm0Boundary : m0 ⬝ᵥ a = β) :
    ∀ m : Fin n → ℝ, m ∈ M → m ⬝ᵥ a = β := by
  intro m hmM
  have hmLe : m ⬝ᵥ a ≤ β := hMsubset hmM
  have hreflectLe : ((2 : ℝ) • m0 - m) ⬝ᵥ a ≤ β :=
    hMsubset (hMreflect m hmM)
  have hmGe : β ≤ m ⬝ᵥ a := by
    have hreflectEq : ((2 : ℝ) • m0 - m) ⬝ᵥ a = (2 : ℝ) * β - m ⬝ᵥ a := by
      calc
        ((2 : ℝ) • m0 - m) ⬝ᵥ a
            = (2 : ℝ) * (m0 ⬝ᵥ a) - m ⬝ᵥ a := by
                simp [sub_eq_add_neg, add_dotProduct, smul_dotProduct]
        _ = (2 : ℝ) * β - m ⬝ᵥ a := by simpa [hm0Boundary]
    have hcalc : (2 : ℝ) * β - m ⬝ᵥ a ≤ β := by
      simpa [hreflectEq] using hreflectLe
    linarith
  exact le_antisymm hmLe hmGe

/-- Case-2 local affine-line helper:
the intersection of two affine level sets is stable under affine combinations
of the form `m1 + t • (m2 - m1)`. -/
lemma helperForTheorem_20_2_mem_inter_level_of_affine_combo
    {n : ℕ} {u v m1 m2 : Fin n → ℝ} {α β t : ℝ}
    (hm1 : m1 ⬝ᵥ u = α ∧ m1 ⬝ᵥ v = β)
    (hm2 : m2 ⬝ᵥ u = α ∧ m2 ⬝ᵥ v = β) :
    (m1 + t • (m2 - m1)) ⬝ᵥ u = α ∧
      (m1 + t • (m2 - m1)) ⬝ᵥ v = β := by
  constructor
  · calc
      (m1 + t • (m2 - m1)) ⬝ᵥ u
          = m1 ⬝ᵥ u + t * ((m2 - m1) ⬝ᵥ u) := by
              simp [add_dotProduct, smul_dotProduct]
      _ = α + t * (α - α) := by
            simpa [sub_eq_add_neg, add_dotProduct, hm1.1, hm2.1]
      _ = α := by ring
  · calc
      (m1 + t • (m2 - m1)) ⬝ᵥ v
          = m1 ⬝ᵥ v + t * ((m2 - m1) ⬝ᵥ v) := by
              simp [add_dotProduct, smul_dotProduct]
      _ = β + t * (β - β) := by
            simpa [sub_eq_add_neg, add_dotProduct, hm1.2, hm2.2]
      _ = β := by ring

/-- Case-2 crossing helper:
from two right points on opposite sides of the level `x ⬝ᵥ c = γ`, construct the
unique affine-combination point on that level, still inside the convex right set
and still on the ambient `b0`-level. -/
lemma helperForTheorem_20_2_crossing_point_on_level_of_convex_and_level
    {n : ℕ} {C₂ : Set (Fin n → ℝ)}
    (hC₂conv : Convex ℝ C₂)
    {b0 c x0 y : Fin n → ℝ} {β0 γ : ℝ}
    (hC₂eqLevel0 : C₂ ⊆ {z : Fin n → ℝ | z ⬝ᵥ b0 = β0})
    (hx0C₂ : x0 ∈ C₂) (hyC₂ : y ∈ C₂)
    (hx0lt : x0 ⬝ᵥ c < γ) (hyGt : γ < y ⬝ᵥ c) :
    ∃ m : Fin n → ℝ, m ∈ C₂ ∧
      m ⬝ᵥ b0 = β0 ∧
      m ⬝ᵥ c = γ ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ m = x0 + t • (y - x0) := by
  let t : ℝ := (γ - x0 ⬝ᵥ c) / (y ⬝ᵥ c - x0 ⬝ᵥ c)
  let m : Fin n → ℝ := x0 + t • (y - x0)
  have hden_pos : 0 < y ⬝ᵥ c - x0 ⬝ᵥ c := by
    linarith [hx0lt, hyGt]
  have hden_ne : y ⬝ᵥ c - x0 ⬝ᵥ c ≠ 0 := by
    linarith [hden_pos]
  have hnum_pos : 0 < γ - x0 ⬝ᵥ c := by
    linarith [hx0lt]
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos hnum_pos hden_pos
  have htlt : t < 1 := by
    have hnum_lt_den : γ - x0 ⬝ᵥ c < y ⬝ᵥ c - x0 ⬝ᵥ c := by
      linarith [hyGt]
    have ht_mul : t * (y ⬝ᵥ c - x0 ⬝ᵥ c) = γ - x0 ⬝ᵥ c := by
      calc
        t * (y ⬝ᵥ c - x0 ⬝ᵥ c)
            = ((γ - x0 ⬝ᵥ c) / (y ⬝ᵥ c - x0 ⬝ᵥ c)) * (y ⬝ᵥ c - x0 ⬝ᵥ c) := by
                rfl
        _ = γ - x0 ⬝ᵥ c := by
              field_simp [hden_ne]
    have ht_lt_mul : t * (y ⬝ᵥ c - x0 ⬝ᵥ c) < y ⬝ᵥ c - x0 ⬝ᵥ c := by
      simpa [ht_mul] using hnum_lt_den
    by_contra htNotLt
    have htge : 1 ≤ t := le_of_not_gt htNotLt
    have hmul_ge : y ⬝ᵥ c - x0 ⬝ᵥ c ≤ t * (y ⬝ᵥ c - x0 ⬝ᵥ c) := by
      nlinarith [hden_pos, htge]
    linarith [hmul_ge, ht_lt_mul]
  have hmC₂ : m ∈ C₂ := by
    exact hC₂conv.add_smul_sub_mem hx0C₂ hyC₂ ⟨le_of_lt htpos, le_of_lt htlt⟩
  have hx0b0 : x0 ⬝ᵥ b0 = β0 := hC₂eqLevel0 hx0C₂
  have hyb0 : y ⬝ᵥ b0 = β0 := hC₂eqLevel0 hyC₂
  have hmb0 : m ⬝ᵥ b0 = β0 := by
    calc
      m ⬝ᵥ b0 = x0 ⬝ᵥ b0 + t * ((y - x0) ⬝ᵥ b0) := by
        simp [m, add_dotProduct, smul_dotProduct]
      _ = β0 + t * (β0 - β0) := by
        simp [sub_eq_add_neg, add_dotProduct, hx0b0, hyb0]
      _ = β0 := by ring
  have hmc : m ⬝ᵥ c = γ := by
    calc
      m ⬝ᵥ c = x0 ⬝ᵥ c + t * ((y - x0) ⬝ᵥ c) := by
        simp [m, add_dotProduct, smul_dotProduct]
      _ = x0 ⬝ᵥ c + t * (y ⬝ᵥ c - x0 ⬝ᵥ c) := by
        simp [sub_eq_add_neg, add_dotProduct]
      _ = γ := by
        dsimp [t]
        field_simp [hden_ne]
        ring
  exact ⟨m, hmC₂, hmb0, hmc, t, htpos, htlt, rfl⟩

/-- Case-2 local affine reflection helper:
for points in the intersection of two level sets, reflection about any base point
stays in that intersection. -/
lemma helperForTheorem_20_2_mem_inter_level_of_reflection
    {n : ℕ} {u v m0 m : Fin n → ℝ} {α β : ℝ}
    (hm0 : m0 ⬝ᵥ u = α ∧ m0 ⬝ᵥ v = β)
    (hm : m ⬝ᵥ u = α ∧ m ⬝ᵥ v = β) :
    ((2 : ℝ) • m0 - m) ⬝ᵥ u = α ∧
      ((2 : ℝ) • m0 - m) ⬝ᵥ v = β := by
  have hcombo :
      (m0 + (-1 : ℝ) • (m - m0)) ⬝ᵥ u = α ∧
        (m0 + (-1 : ℝ) • (m - m0)) ⬝ᵥ v = β :=
    helperForTheorem_20_2_mem_inter_level_of_affine_combo
      (n := n) (u := u) (v := v) (m1 := m0) (m2 := m)
      (α := α) (β := β) (t := (-1 : ℝ)) hm0 hm
  have hcomboU : (2 : ℝ) * (m0 ⬝ᵥ u) - m ⬝ᵥ u = α := by
    linarith [hcombo.1]
  have hcomboV : (2 : ℝ) * (m0 ⬝ᵥ v) - m ⬝ᵥ v = β := by
    linarith [hcombo.2]
  constructor
  · calc
      ((2 : ℝ) • m0 - m) ⬝ᵥ u
          = (2 : ℝ) * (m0 ⬝ᵥ u) - m ⬝ᵥ u := by
              simp [sub_eq_add_neg, add_dotProduct, smul_dotProduct]
      _ = α := hcomboU
  · calc
      ((2 : ℝ) • m0 - m) ⬝ᵥ v
          = (2 : ℝ) * (m0 ⬝ᵥ v) - m ⬝ᵥ v := by
              simp [sub_eq_add_neg, add_dotProduct, smul_dotProduct]
      _ = β := hcomboV

/-- Case-2 bottleneck (isolated): choose a tilt parameter `ε > 0` that keeps the
tilted support inequality on all of `C₁` and keeps a nonzero tilted normal. -/
lemma helperForTheorem_20_2_case2_chain_choose_tilt_epsilon
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    {xR : Fin n → ℝ}
    (hxRlt : xR ⬝ᵥ c < γ)
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    ∃ ε : ℝ, 0 < ε ∧
      b0 + ε • c ≠ 0 ∧
      (∀ x : Fin n → ℝ, x ∈ C₁ → β0 + ε * γ ≤ x ⬝ᵥ (b0 + ε • c)) := by
  by_cases hFempty : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ))
  · let L : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
    have hLpoly : IsPolyhedralConvexSet n L := by
      let a : Fin 1 → Fin n → ℝ := fun _ => b0
      let α : Fin 1 → ℝ := fun _ => β0
      have hpolySystem :
          IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} := by
        simpa using
          (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
            n 1 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
      have hEq : {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} = L := by
        ext x
        constructor
        · intro hx
          have hx0 : x ⬝ᵥ a 0 = α 0 := hx 0
          simpa [L, a, α] using hx0
        · intro hx i
          have hi0 : i = 0 := Subsingleton.elim i 0
          subst hi0
          simpa [L, a, α] using hx
      simpa [hEq] using hpolySystem
    have hLne : L.Nonempty := by
      rcases hC₂ne with ⟨y, hyC₂⟩
      exact ⟨y, hC₂eqLevel0 hyC₂⟩
    have hC₁disjL : Disjoint C₁ L := by
      refine Set.disjoint_left.2 ?_
      intro x hxC₁ hxL
      have hxFace : x ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} := ⟨hxC₁, hxL⟩
      have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
        simpa [hFempty] using hxFace
      exact hxEmpty.elim
    have hStrongC₁L : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ L := by
      exact
        exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
          (n := n) (C₁ := C₁) (C₂ := L)
          hC₁ne hLne hC₁disjL hC₁poly hLpoly
    have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
      rcases hStrongC₁L with ⟨Hs, hHs⟩
      refine ⟨Hs, ?_⟩
      exact
        hyperplaneSeparatesStrongly_mono_sets
          (hH := hHs)
          (hB₁ := by intro x hx; exact hx)
          (hB₂ := by
            intro y hyC₂
            exact hC₂eqLevel0 hyC₂)
          hC₁ne hC₂ne
    have hSepExists :
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
      helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
        (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
    exact False.elim (hNoNoncontainment hSepExists)
  · -- Main unresolved subcase: nonempty boundary face, epsilon-tilting on all of `C₁`.
    have hFaceNonempty : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hFempty
    rcases hFaceNonempty with ⟨xF, hxF⟩
    have hC₁conv : Convex ℝ C₁ :=
      helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
    have hTFAE :
        [IsPolyhedralConvexSet n C₁,
            (IsClosed C₁ ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C₁ C'}.Finite),
          IsFinitelyGeneratedConvexSet n C₁].TFAE :=
      polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C₁) hC₁conv
    have hC₁fg : IsFinitelyGeneratedConvexSet n C₁ := (hTFAE.out 0 2).1 hC₁poly
    rcases hC₁fg with ⟨S₀, S₁, hS₀fin, hS₁fin, hC₁eqMixed⟩
    have hS₀subsetC₁ : S₀ ⊆ C₁ := by
      intro x hxS₀
      have hxAdd : x ∈ S₀ + ray n S₁ := by
        refine ⟨x, hxS₀, 0, ?_, by simp⟩
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      have hxMixed : x ∈ mixedConvexHull (n := n) S₀ S₁ :=
        (add_ray_subset_mixedConvexHull (n := n) S₀ S₁) hxAdd
      simpa [hC₁eqMixed] using hxMixed
    have hS₁recedesC₁ :
        ∀ d : Fin n → ℝ, d ∈ S₁ →
          ∀ x : Fin n → ℝ, x ∈ C₁ → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C₁ := by
      intro d hd x hx t ht
      have hxMixed : x ∈ mixedConvexHull (n := n) S₀ S₁ := by
        simpa [hC₁eqMixed] using hx
      have hxStep :
          x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ :=
        helperForTheorem_19_1_mixedConvexHull_recedes
          (n := n) (S₀ := S₀) (S₁ := S₁) (d := d) (x := x) hd hxMixed t ht
      simpa [hC₁eqMixed] using hxStep
    have hS₀_b0_ge : ∀ p : Fin n → ℝ, p ∈ S₀ → β0 ≤ p ⬝ᵥ b0 := by
      intro p hpS₀
      exact hC₁ge0 p (hS₀subsetC₁ hpS₀)
    have hS₀_face_c_ge :
        ∀ p : Fin n → ℝ, p ∈ S₀ → p ⬝ᵥ b0 = β0 → γ ≤ p ⬝ᵥ c := by
      intro p hpS₀ hpb
      exact hFace_ge p ⟨hS₀subsetC₁ hpS₀, hpb⟩
    have hS₁_b0_nonneg : ∀ d : Fin n → ℝ, d ∈ S₁ → 0 ≤ d ⬝ᵥ b0 := by
      intro d hdS₁
      by_contra hdb0
      have hdb0lt : d ⬝ᵥ b0 < 0 := lt_of_not_ge hdb0
      rcases hC₁ne with ⟨x0, hx0C₁⟩
      let t : ℝ := (x0 ⬝ᵥ b0 - β0 + 1) / (-(d ⬝ᵥ b0))
      have ht_nonneg : 0 ≤ t := by
        have hnum : 0 ≤ x0 ⬝ᵥ b0 - β0 + 1 := by linarith [hC₁ge0 x0 hx0C₁]
        have hden : 0 ≤ -(d ⬝ᵥ b0) := by linarith [hdb0lt]
        exact div_nonneg hnum hden
      have hxStep : x0 + t • d ∈ C₁ := hS₁recedesC₁ d hdS₁ x0 hx0C₁ t ht_nonneg
      have hStep_ge : β0 ≤ (x0 + t • d) ⬝ᵥ b0 := hC₁ge0 (x0 + t • d) hxStep
      have hden_ne : (-(d ⬝ᵥ b0)) ≠ 0 := by linarith [hdb0lt]
      have ht_mul : t * (d ⬝ᵥ b0) = β0 - x0 ⬝ᵥ b0 - 1 := by
        have hdot_ne : (d ⬝ᵥ b0) ≠ 0 := by linarith [hdb0lt]
        calc
          t * (d ⬝ᵥ b0) = ((x0 ⬝ᵥ b0 - β0 + 1) / (-(d ⬝ᵥ b0))) * (d ⬝ᵥ b0) := by
            rfl
          _ = (x0 ⬝ᵥ b0 - β0 + 1) * (((d ⬝ᵥ b0) / (-(d ⬝ᵥ b0)))) := by ring
          _ = (x0 ⬝ᵥ b0 - β0 + 1) * (-1) := by
            field_simp [hden_ne, hdot_ne]
          _ = β0 - x0 ⬝ᵥ b0 - 1 := by ring
      have hcalc : (x0 + t • d) ⬝ᵥ b0 = β0 - 1 := by
        calc
          (x0 + t • d) ⬝ᵥ b0 = x0 ⬝ᵥ b0 + t * (d ⬝ᵥ b0) := by
            simp [add_dotProduct, smul_dotProduct]
          _ = β0 - 1 := by linarith [ht_mul]
      linarith [hStep_ge, hcalc]
    have hS₁_c_nonneg_if_b0_eq0 :
        ∀ d : Fin n → ℝ, d ∈ S₁ → d ⬝ᵥ b0 = 0 → 0 ≤ d ⬝ᵥ c := by
      intro d hdS₁ hdb0eq
      by_contra hdc
      have hdc_lt : d ⬝ᵥ c < 0 := lt_of_not_ge hdc
      let t : ℝ := (xF ⬝ᵥ c - γ + 1) / (-(d ⬝ᵥ c))
      have ht_nonneg : 0 ≤ t := by
        have hnum : 0 ≤ xF ⬝ᵥ c - γ + 1 := by
          have hxF_ge : γ ≤ xF ⬝ᵥ c := hFace_ge xF hxF
          linarith [hxF_ge]
        have hden : 0 ≤ -(d ⬝ᵥ c) := by linarith [hdc_lt]
        exact div_nonneg hnum hden
      have hxStep : xF + t • d ∈ C₁ := hS₁recedesC₁ d hdS₁ xF hxF.1 t ht_nonneg
      have hxLevel : (xF + t • d) ⬝ᵥ b0 = β0 := by
        calc
          (xF + t • d) ⬝ᵥ b0 = xF ⬝ᵥ b0 + t * (d ⬝ᵥ b0) := by
            simp [add_dotProduct, smul_dotProduct]
          _ = xF ⬝ᵥ b0 := by simp [hdb0eq]
          _ = β0 := hxF.2
      have hxFaceStep : xF + t • d ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} :=
        ⟨hxStep, hxLevel⟩
      have hgeStep : γ ≤ (xF + t • d) ⬝ᵥ c := hFace_ge (xF + t • d) hxFaceStep
      have hden_ne : (-(d ⬝ᵥ c)) ≠ 0 := by linarith [hdc_lt]
      have ht_mul : t * (d ⬝ᵥ c) = γ - xF ⬝ᵥ c - 1 := by
        have hdot_ne : (d ⬝ᵥ c) ≠ 0 := by linarith [hdc_lt]
        calc
          t * (d ⬝ᵥ c) = ((xF ⬝ᵥ c - γ + 1) / (-(d ⬝ᵥ c))) * (d ⬝ᵥ c) := by
            rfl
          _ = (xF ⬝ᵥ c - γ + 1) * (((d ⬝ᵥ c) / (-(d ⬝ᵥ c)))) := by ring
          _ = (xF ⬝ᵥ c - γ + 1) * (-1) := by
            field_simp [hden_ne, hdot_ne]
          _ = γ - xF ⬝ᵥ c - 1 := by ring
      have hcalc : (xF + t • d) ⬝ᵥ c = γ - 1 := by
        calc
          (xF + t • d) ⬝ᵥ c = xF ⬝ᵥ c + t * (d ⬝ᵥ c) := by
            simp [add_dotProduct, smul_dotProduct]
          _ = γ - 1 := by linarith [ht_mul]
      linarith [hgeStep, hcalc]
    set Pbad : Set (Fin n → ℝ) := {p : Fin n → ℝ | p ∈ S₀ ∧ p ⬝ᵥ c < γ}
    set Dbad : Set (Fin n → ℝ) := {d : Fin n → ℝ | d ∈ S₁ ∧ d ⬝ᵥ c < 0}
    let ubP : (Fin n → ℝ) → ℝ := fun p => (p ⬝ᵥ b0 - β0) / (γ - p ⬝ᵥ c)
    let ubD : (Fin n → ℝ) → ℝ := fun d => (d ⬝ᵥ b0) / (-(d ⬝ᵥ c))
    have hPbadFin : Pbad.Finite := by
      refine hS₀fin.subset ?_
      intro p hpP
      simpa [Pbad] using hpP.1
    have hDbadFin : Dbad.Finite := by
      refine hS₁fin.subset ?_
      intro d hdD
      simpa [Dbad] using hdD.1
    have hChooseEpsP :
        ∃ εP : ℝ, 0 < εP ∧ ∀ p : Fin n → ℝ, p ∈ Pbad → εP ≤ ubP p := by
      by_cases hPne : Pbad.Nonempty
      · rcases Set.exists_min_image Pbad ubP hPbadFin hPne with
          ⟨pMin, hpMinP, hpMinLe⟩
        have hpMinS₀ : pMin ∈ S₀ := by
          simpa [Pbad] using hpMinP.1
        have hpMinBad : pMin ⬝ᵥ c < γ := by
          simpa [Pbad] using hpMinP.2
        have hnum_nonneg : 0 ≤ pMin ⬝ᵥ b0 - β0 := by
          linarith [hS₀_b0_ge pMin hpMinS₀]
        have hnum_ne : pMin ⬝ᵥ b0 - β0 ≠ 0 := by
          intro hzero
          have hpbEq : pMin ⬝ᵥ b0 = β0 := by linarith
          have hfaceGe : γ ≤ pMin ⬝ᵥ c := hS₀_face_c_ge pMin hpMinS₀ hpbEq
          linarith
        have hnum_pos : 0 < pMin ⬝ᵥ b0 - β0 := by
          exact lt_of_le_of_ne hnum_nonneg (by simpa using hnum_ne.symm)
        have hden_pos : 0 < γ - pMin ⬝ᵥ c := by linarith
        refine ⟨ubP pMin / 2, ?_, ?_⟩
        · have hub_pos : 0 < ubP pMin := by
            dsimp [ubP]
            exact div_pos hnum_pos hden_pos
          linarith
        · intro p hpP
          have hmin_le : ubP pMin ≤ ubP p := hpMinLe p hpP
          have hub_pos : 0 < ubP pMin := by
            dsimp [ubP]
            exact div_pos hnum_pos hden_pos
          have hhalf_le : ubP pMin / 2 ≤ ubP pMin := by nlinarith [le_of_lt hub_pos]
          exact le_trans hhalf_le hmin_le
      · refine ⟨1, by norm_num, ?_⟩
        intro p hpP
        exact (hPne ⟨p, hpP⟩).elim
    have hChooseEpsD :
        ∃ εD : ℝ, 0 < εD ∧ ∀ d : Fin n → ℝ, d ∈ Dbad → εD ≤ ubD d := by
      by_cases hDne : Dbad.Nonempty
      · rcases Set.exists_min_image Dbad ubD hDbadFin hDne with
          ⟨dMin, hdMinD, hdMinLe⟩
        have hdMinS₁ : dMin ∈ S₁ := by
          simpa [Dbad] using hdMinD.1
        have hdMinBad : dMin ⬝ᵥ c < 0 := by
          simpa [Dbad] using hdMinD.2
        have hnum_nonneg : 0 ≤ dMin ⬝ᵥ b0 := hS₁_b0_nonneg dMin hdMinS₁
        have hnum_ne : dMin ⬝ᵥ b0 ≠ 0 := by
          intro hzero
          have hdc_nonneg : 0 ≤ dMin ⬝ᵥ c :=
            hS₁_c_nonneg_if_b0_eq0 dMin hdMinS₁ hzero
          linarith
        have hnum_pos : 0 < dMin ⬝ᵥ b0 := by
          exact lt_of_le_of_ne hnum_nonneg (by simpa using hnum_ne.symm)
        have hden_pos : 0 < -(dMin ⬝ᵥ c) := by linarith
        refine ⟨ubD dMin / 2, ?_, ?_⟩
        · have hub_pos : 0 < ubD dMin := by
            dsimp [ubD]
            exact div_pos hnum_pos hden_pos
          linarith
        · intro d hdD
          have hmin_le : ubD dMin ≤ ubD d := hdMinLe d hdD
          have hub_pos : 0 < ubD dMin := by
            dsimp [ubD]
            exact div_pos hnum_pos hden_pos
          have hhalf_le : ubD dMin / 2 ≤ ubD dMin := by nlinarith [le_of_lt hub_pos]
          exact le_trans hhalf_le hmin_le
      · refine ⟨1, by norm_num, ?_⟩
        intro d hdD
        exact (hDne ⟨d, hdD⟩).elim
    rcases hChooseEpsP with ⟨εP, hεPpos, hεP_le⟩
    rcases hChooseEpsD with ⟨εD, hεDpos, hεD_le⟩
    let ε0 : ℝ := min εP εD
    have hε0pos : 0 < ε0 := by
      dsimp [ε0]
      exact lt_min hεPpos hεDpos
    have hε0_leP : ∀ p : Fin n → ℝ, p ∈ Pbad → ε0 ≤ ubP p := by
      intro p hpP
      exact le_trans (min_le_left εP εD) (hεP_le p hpP)
    have hε0_leD : ∀ d : Fin n → ℝ, d ∈ Dbad → ε0 ≤ ubD d := by
      intro d hdD
      exact le_trans (min_le_right εP εD) (hεD_le d hdD)
    have hC₁_for_delta :
        ∀ δ : ℝ, 0 < δ → δ ≤ ε0 →
          ∀ x : Fin n → ℝ, x ∈ C₁ → β0 + δ * γ ≤ x ⬝ᵥ (b0 + δ • c) := by
      intro δ hδpos hδle x hxC₁
      have hxMixed : x ∈ mixedConvexHull (n := n) S₀ S₁ := by
        simpa [hC₁eqMixed] using hxC₁
      let u : Fin n → ℝ := b0 + δ • c
      let rhs : ℝ := β0 + δ * γ
      let Ccand : Set (Fin n → ℝ) := {z : Fin n → ℝ | z ⬝ᵥ (-u) ≤ -rhs}
      have hCconv : Convex ℝ Ccand := by
        dsimp [Ccand, u, rhs]
        simpa using
          (convex_dotProduct_le (n := n) (b := -(b0 + δ • c)) (β := -(β0 + δ * γ)))
      have hS₀sub : S₀ ⊆ Ccand := by
        intro p hpS₀
        have hpIneq : β0 + δ * γ ≤ p ⬝ᵥ (b0 + δ • c) := by
          by_cases hpbad : p ⬝ᵥ c < γ
          · have hpPbad : p ∈ Pbad := by
              exact ⟨hpS₀, hpbad⟩
            have hδub : δ ≤ ubP p := le_trans hδle (hε0_leP p hpPbad)
            have hden_pos : 0 < γ - p ⬝ᵥ c := by linarith
            have hden_ne : γ - p ⬝ᵥ c ≠ 0 := by linarith
            have hmul_raw :
                δ * (γ - p ⬝ᵥ c) ≤ ubP p * (γ - p ⬝ᵥ c) :=
              mul_le_mul_of_nonneg_right hδub (le_of_lt hden_pos)
            have hub_mul : ubP p * (γ - p ⬝ᵥ c) = p ⬝ᵥ b0 - β0 := by
              dsimp [ubP]
              field_simp [hden_ne]
            have hmul :
                δ * (γ - p ⬝ᵥ c) ≤ p ⬝ᵥ b0 - β0 := by
              simpa [hub_mul] using hmul_raw
            have hlin : β0 + δ * γ ≤ p ⬝ᵥ b0 + δ * (p ⬝ᵥ c) := by
              linarith
            simpa [add_dotProduct, smul_dotProduct] using hlin
          · have hpc_ge : γ ≤ p ⬝ᵥ c := le_of_not_gt hpbad
            have hpb_ge : β0 ≤ p ⬝ᵥ b0 := hS₀_b0_ge p hpS₀
            have hlin : β0 + δ * γ ≤ p ⬝ᵥ b0 + δ * (p ⬝ᵥ c) := by
              nlinarith [hpb_ge, hpc_ge, hδpos]
            simpa [add_dotProduct, smul_dotProduct] using hlin
        dsimp [Ccand, u, rhs]
        have hneg_eq : p ⬝ᵥ (-(b0 + δ • c)) = -(p ⬝ᵥ (b0 + δ • c)) := by simp
        nlinarith [hpIneq, hneg_eq]
      have hRec :
          ∀ d ∈ S₁, ∀ z ∈ Ccand, ∀ t : ℝ, 0 ≤ t → z + t • d ∈ Ccand := by
        intro d hdS₁ z hz t ht
        have hdNonneg : 0 ≤ d ⬝ᵥ (b0 + δ • c) := by
          by_cases hdbad : d ⬝ᵥ c < 0
          · have hdDbad : d ∈ Dbad := by exact ⟨hdS₁, hdbad⟩
            have hδub : δ ≤ ubD d := le_trans hδle (hε0_leD d hdDbad)
            have hden_pos : 0 < -(d ⬝ᵥ c) := by linarith
            have hden_ne : (-(d ⬝ᵥ c)) ≠ 0 := by linarith
            have hmul_raw :
                δ * (-(d ⬝ᵥ c)) ≤ ubD d * (-(d ⬝ᵥ c)) :=
              mul_le_mul_of_nonneg_right hδub (le_of_lt hden_pos)
            have hub_mul : ubD d * (-(d ⬝ᵥ c)) = d ⬝ᵥ b0 := by
              have hdc_ne : d ⬝ᵥ c ≠ 0 := by linarith [hdbad]
              dsimp [ubD]
              calc
                (d ⬝ᵥ b0 / (-(d ⬝ᵥ c))) * (-(d ⬝ᵥ c))
                    = d ⬝ᵥ b0 * (d ⬝ᵥ c) / (d ⬝ᵥ c) := by ring
                _ = d ⬝ᵥ b0 := by field_simp [hdc_ne]
            have hmul : δ * (-(d ⬝ᵥ c)) ≤ d ⬝ᵥ b0 := by
              simpa [hub_mul] using hmul_raw
            have hlin : 0 ≤ d ⬝ᵥ b0 + δ * (d ⬝ᵥ c) := by
              linarith
            simpa [add_dotProduct, smul_dotProduct] using hlin
          · have hdc_nonneg : 0 ≤ d ⬝ᵥ c := le_of_not_gt hdbad
            have hdb0_nonneg : 0 ≤ d ⬝ᵥ b0 := hS₁_b0_nonneg d hdS₁
            have hlin : 0 ≤ d ⬝ᵥ b0 + δ * (d ⬝ᵥ c) := by
              nlinarith [hdb0_nonneg, hdc_nonneg, hδpos]
            simpa [add_dotProduct, smul_dotProduct] using hlin
        dsimp [Ccand, u, rhs] at hz ⊢
        have hneg_eq : d ⬝ᵥ (-(b0 + δ • c)) = -(d ⬝ᵥ (b0 + δ • c)) := by simp
        have hneg : d ⬝ᵥ (-(b0 + δ • c)) ≤ 0 := by
          nlinarith [hdNonneg, hneg_eq]
        have hstep :
            z ⬝ᵥ (-(b0 + δ • c)) + t * (d ⬝ᵥ (-(b0 + δ • c))) ≤ -(β0 + δ * γ) := by
          nlinarith [hz, hneg, ht]
        calc
          (z + t • d) ⬝ᵥ (-(b0 + δ • c))
              = z ⬝ᵥ (-(b0 + δ • c)) + t * (d ⬝ᵥ (-(b0 + δ • c))) := by
                  simp [add_dotProduct, smul_dotProduct]
                  ring
          _ ≤ -(β0 + δ * γ) := hstep
      have hMixedSub : mixedConvexHull (n := n) S₀ S₁ ⊆ Ccand :=
        mixedConvexHull_subset_of_convex_of_subset_of_recedes
          (n := n) (S₀ := S₀) (S₁ := S₁) (Ccand := Ccand)
          hCconv hS₀sub hRec
      have hxCand : x ∈ Ccand := hMixedSub hxMixed
      dsimp [Ccand, u, rhs] at hxCand
      have hneg_eqx : x ⬝ᵥ (-(b0 + δ • c)) = -(x ⬝ᵥ (b0 + δ • c)) := by simp
      nlinarith [hxCand, hneg_eqx]
    by_cases hzero : b0 + ε0 • c = 0
    · let ε : ℝ := ε0 / 2
      have hεpos : 0 < ε := by
        dsimp [ε]
        linarith [hε0pos]
      have hεle : ε ≤ ε0 := by
        dsimp [ε]
        linarith
      have hC₁geε :
          ∀ x : Fin n → ℝ, x ∈ C₁ → β0 + ε * γ ≤ x ⬝ᵥ (b0 + ε • c) :=
        hC₁_for_delta ε hεpos hεle
      have hnonzero : b0 + ε • c ≠ 0 := by
        intro hzeroHalf
        have hzeroHalf' : b0 + (ε0 / 2) • c = 0 := by
          simpa [ε] using hzeroHalf
        have hxR_full : xR ⬝ᵥ b0 + ε0 * (xR ⬝ᵥ c) = 0 := by
          have hxR_full_eq : xR ⬝ᵥ (b0 + ε0 • c) = 0 := by
            simpa using congrArg (fun v : Fin n → ℝ => xR ⬝ᵥ v) hzero
          simpa [add_dotProduct, smul_dotProduct] using hxR_full_eq
        have hxR_half : xR ⬝ᵥ b0 + (ε0 / 2) * (xR ⬝ᵥ c) = 0 := by
          have hxR_half_eq : xR ⬝ᵥ (b0 + (ε0 / 2) • c) = 0 := by
            simpa using congrArg (fun v : Fin n → ℝ => xR ⬝ᵥ v) hzeroHalf'
          simpa [add_dotProduct, smul_dotProduct] using hxR_half_eq
        have hxR_mul_zero : (ε0 / 2) * (xR ⬝ᵥ c) = 0 := by
          linarith [hxR_full, hxR_half]
        have hε0half_ne : (ε0 / 2 : ℝ) ≠ 0 := by
          linarith [hε0pos]
        have hxR_c_zero : xR ⬝ᵥ c = 0 := by
          exact (mul_eq_zero.mp hxR_mul_zero).resolve_left hε0half_ne
        have hxF_full : xF ⬝ᵥ b0 + ε0 * (xF ⬝ᵥ c) = 0 := by
          have hxF_full_eq : xF ⬝ᵥ (b0 + ε0 • c) = 0 := by
            simpa using congrArg (fun v : Fin n → ℝ => xF ⬝ᵥ v) hzero
          simpa [add_dotProduct, smul_dotProduct] using hxF_full_eq
        have hxF_half : xF ⬝ᵥ b0 + (ε0 / 2) * (xF ⬝ᵥ c) = 0 := by
          have hxF_half_eq : xF ⬝ᵥ (b0 + (ε0 / 2) • c) = 0 := by
            simpa using congrArg (fun v : Fin n → ℝ => xF ⬝ᵥ v) hzeroHalf'
          simpa [add_dotProduct, smul_dotProduct] using hxF_half_eq
        have hxF_mul_zero : (ε0 / 2) * (xF ⬝ᵥ c) = 0 := by
          linarith [hxF_full, hxF_half]
        have hxF_c_zero : xF ⬝ᵥ c = 0 := by
          exact (mul_eq_zero.mp hxF_mul_zero).resolve_left hε0half_ne
        have hxF_ge : γ ≤ xF ⬝ᵥ c := hFace_ge xF hxF
        have hγpos : 0 < γ := by linarith [hxRlt, hxR_c_zero]
        have hγnonpos : γ ≤ 0 := by linarith [hxF_ge, hxF_c_zero]
        exact (not_lt_of_ge hγnonpos) hγpos
      exact ⟨ε, hεpos, hnonzero, hC₁geε⟩
    · exact ⟨ε0, hε0pos, hzero, hC₁_for_delta ε0 hε0pos (le_rfl)⟩

/-- D-route nonempty-intersection branch for Theorem 20.2:
if `D := C₁ ∩ aff C₂` is nonempty, then one can build a proper separator of
`C₁` and `C₂` that does not contain all of `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_nonempty_left_inter_affineSpan
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hDne : (C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))).Nonempty) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  let A : AffineSubspace ℝ (Fin n → ℝ) := affineSpan ℝ C₂
  let D : Set (Fin n → ℝ) := C₁ ∩ (A : Set (Fin n → ℝ))
  rcases
      helperForTheorem_20_2_droute_oriented_data_of_nonempty_left_inter_affineSpan
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hDne with
    ⟨c, γ, hc0, hC₂le, hyRstrict, hDge⟩
  let C₂closed : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c ≤ γ}
  have hApoly : IsPolyhedralConvexSet n (A : Set (Fin n → ℝ)) := by
    simpa [A] using helperForTheorem_20_2_affineSpan_polyhedral (n := n) C₂
  have hHalfPoly : IsPolyhedralConvexSet n {x : Fin n → ℝ | x ⬝ᵥ c ≤ γ} := by
    let b : Fin 1 → Fin n → ℝ := fun _ => c
    let β : Fin 1 → ℝ := fun _ => γ
    have hpoly :
        IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ b i ≤ β i} := by
      simpa using
        (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
          n 0 1 (fun i : Fin 0 => (0 : Fin n → ℝ)) (fun i : Fin 0 => (0 : ℝ)) b β)
    have hEq :
        {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ b i ≤ β i} =
          {x : Fin n → ℝ | x ⬝ᵥ c ≤ γ} := by
      ext x
      constructor
      · intro hx
        have hx0 : x ⬝ᵥ b 0 ≤ β 0 := hx 0
        simpa [b, β] using hx0
      · intro hx i
        have hi0 : i = 0 := Subsingleton.elim i 0
        subst hi0
        simpa [b, β] using hx
    simpa [hEq] using hpoly
  have hC₂closedPoly : IsPolyhedralConvexSet n C₂closed := by
    dsimp [C₂closed]
    exact helperForTheorem_19_1_polyhedral_inter hApoly hHalfPoly
  have hC₂closedNe : C₂closed.Nonempty := by
    rcases hyRstrict with ⟨yR, hyRC₂, hyRlt⟩
    refine ⟨yR, ?_⟩
    exact ⟨subset_affineSpan (k := ℝ) (s := C₂) hyRC₂, le_of_lt hyRlt⟩
  have hC₂subsetClosed : C₂ ⊆ C₂closed := by
    intro y hyC₂
    exact ⟨subset_affineSpan (k := ℝ) (s := C₂) hyC₂, hC₂le y hyC₂⟩
  by_cases hClosedInter :
      (C₁ ∩ C₂closed : Set (Fin n → ℝ)) = (∅ : Set (Fin n → ℝ))
  · have hC₁disjC₂closed : Disjoint C₁ C₂closed := by
      refine Set.disjoint_left.2 ?_
      intro x hxC₁ hxC₂closed
      have hxInter : x ∈ C₁ ∩ C₂closed := ⟨hxC₁, hxC₂closed⟩
      have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
        simpa [hClosedInter] using hxInter
      exact hxEmpty.elim
    have hStrongC₁C₂closed :
        ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂closed := by
      exact
        exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
          (n := n) (C₁ := C₁) (C₂ := C₂closed)
          hC₁ne hC₂closedNe hC₁disjC₂closed hC₁poly hC₂closedPoly
    have hStrongC₁C₂ :
        ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
      rcases hStrongC₁C₂closed with ⟨Hs, hHs⟩
      refine ⟨Hs, ?_⟩
      exact
        hyperplaneSeparatesStrongly_mono_sets
          (hH := hHs)
          (hB₁ := by intro x hx; exact hx)
          (hB₂ := hC₂subsetClosed)
          hC₁ne hC₂ne
    exact
      helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
        (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
  · have hClosedInterNe : (C₁ ∩ C₂closed : Set (Fin n → ℝ)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hClosedInter
    rcases hClosedInterNe with ⟨mBase, hmBaseC₁, hmBaseClosed⟩
    have hmBaseA : mBase ∈ (A : Set (Fin n → ℝ)) := hmBaseClosed.1
    have hmBaseD : mBase ∈ D := ⟨hmBaseC₁, hmBaseA⟩
    have hmBaseEq : mBase ⬝ᵥ c = γ := by
      have hmBaseGe : γ ≤ mBase ⬝ᵥ c := hDge mBase hmBaseD
      have hmBaseLe : mBase ⬝ᵥ c ≤ γ := hmBaseClosed.2
      exact le_antisymm hmBaseLe hmBaseGe
    have hStrictDisj :
        Disjoint C₁ {x : Fin n → ℝ | x ∈ (A : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c < γ} := by
      refine Set.disjoint_left.2 ?_
      intro x hxC₁ hxStrict
      have hxD : x ∈ D := ⟨hxC₁, hxStrict.1⟩
      have hxcGe : γ ≤ x ⬝ᵥ c := hDge x hxD
      exact (not_lt_of_ge hxcGe) hxStrict.2
    let Cshift : Set (Fin n → ℝ) := {z : Fin n → ℝ | z + mBase ∈ C₁}
    let K : Set (Fin n → ℝ) := closure (convexConeGenerated n Cshift)
    let RiShift : Set (Fin n → ℝ) :=
      {z : Fin n → ℝ | z ∈ (A.direction : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c < 0}
    let Mshift : Set (Fin n → ℝ) :=
      {z : Fin n → ℝ | z ∈ (A.direction : Set (Fin n → ℝ)) ∧ z ⬝ᵥ c = 0}
    let C1prime : Set (Fin n → ℝ) := K + Mshift
    have hKDisjRi :
        Disjoint K RiShift := by
      dsimp [K, Cshift, RiShift]
      exact
        helperForTheorem_20_2_disjoint_shifted_cone_of_affine_strict_half_data
          (n := n) (C := C₁) (A := A) hC₁poly
          (mBase := mBase) (c := c) (γ := γ)
          hmBaseC₁ hmBaseA hmBaseEq hStrictDisj
    rcases hyRstrict with ⟨yR, hyRC₂, hyRlt⟩
    have hRiShiftNe : RiShift.Nonempty := by
      refine ⟨yR - mBase, ?_⟩
      constructor
      · have hyRA : yR ∈ (A : Set (Fin n → ℝ)) := subset_affineSpan (k := ℝ) (s := C₂) hyRC₂
        simpa [vsub_eq_sub] using A.vsub_mem_direction hyRA hmBaseA
      · calc
          (yR - mBase) ⬝ᵥ c = yR ⬝ᵥ c - mBase ⬝ᵥ c := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ < 0 := by linarith [hyRlt, hmBaseEq]
    have hRiShiftSubClosed :
        ∀ x : Fin n → ℝ, x ∈ RiShift →
          ∀ m : Fin n → ℝ, m ∈ Mshift → x - m ∈ RiShift := by
      intro x hx m hm
      rcases hx with ⟨hxDir, hxcLt⟩
      rcases hm with ⟨hmDir, hmcEq⟩
      constructor
      · exact A.direction.sub_mem hxDir hmDir
      · calc
          (x - m) ⬝ᵥ c = x ⬝ᵥ c - m ⬝ᵥ c := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ = x ⬝ᵥ c := by simp [hmcEq]
          _ < 0 := hxcLt
    have hRiNotSubsetC1prime : ¬ RiShift ⊆ C1prime := by
      exact
        helperForTheorem_20_2_not_subset_sum_of_disjoint_and_sub_closed
          (n := n) (K := K) (M := Mshift) (Ri := RiShift)
          hRiShiftNe hRiShiftSubClosed hKDisjRi
    have hCshiftPoly : IsPolyhedralConvexSet n Cshift := by
      exact
        helperForTheorem_20_2_polyhedral_preimage_add_of_polyhedral
          (n := n) (C := C₁) hC₁poly mBase
    have hKdata :
        IsPolyhedralConvexSet n K ∧
          IsConeSet n K ∧
          K =
            (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • Cshift) ∪
              Set.recessionCone Cshift :=
      polyhedralConvexCone_closure_convexConeGenerated
        (n := n) (C := Cshift) ⟨0, by
          dsimp [Cshift]
          simpa using hmBaseC₁⟩ hCshiftPoly
    have hKpoly : IsPolyhedralConvexSet n K := hKdata.1
    have hKcone : IsConeSet n K := hKdata.2.1
    have hAshiftPoly :
        IsPolyhedralConvexSet n {z : Fin n → ℝ | z + mBase ∈ (A : Set (Fin n → ℝ))} := by
      exact
        helperForTheorem_20_2_polyhedral_preimage_add_of_polyhedral
          (n := n) (C := (A : Set (Fin n → ℝ))) hApoly mBase
    have hAshiftEq :
        {z : Fin n → ℝ | z + mBase ∈ (A : Set (Fin n → ℝ))} =
          (A.direction : Set (Fin n → ℝ)) := by
      ext z
      constructor
      · intro hz
        have hzDir : z + mBase -ᵥ mBase ∈ A.direction := A.vsub_mem_direction hz hmBaseA
        simpa [vsub_eq_sub] using hzDir
      · intro hzDir
        have hzVsub : z + mBase -ᵥ mBase ∈ A.direction := by
          simpa [vsub_eq_sub] using hzDir
        exact
          (AffineSubspace.vsub_right_mem_direction_iff_mem (s := A) hmBaseA (z + mBase)).1
            hzVsub
    have hLevelZeroPoly : IsPolyhedralConvexSet n {z : Fin n → ℝ | z ⬝ᵥ c = 0} := by
      let a : Fin 1 → Fin n → ℝ := fun _ => c
      let α : Fin 1 → ℝ := fun _ => 0
      have hpoly :
          IsPolyhedralConvexSet n {z : Fin n → ℝ | ∀ i : Fin 1, z ⬝ᵥ a i = α i} := by
        simpa using
          (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
            n 1 0 a α (fun i : Fin 0 => (0 : Fin n → ℝ)) (fun i : Fin 0 => (0 : ℝ)))
      have hEq :
          {z : Fin n → ℝ | ∀ i : Fin 1, z ⬝ᵥ a i = α i} =
            {z : Fin n → ℝ | z ⬝ᵥ c = 0} := by
        ext z
        constructor
        · intro hz
          have hz0 : z ⬝ᵥ a 0 = α 0 := hz 0
          simpa [a, α] using hz0
        · intro hz i
          have hi0 : i = 0 := Subsingleton.elim i 0
          subst hi0
          simpa [a, α] using hz
      simpa [hEq] using hpoly
    have hMshiftPoly : IsPolyhedralConvexSet n Mshift := by
      have hDirPoly : IsPolyhedralConvexSet n (A.direction : Set (Fin n → ℝ)) := by
        rw [← hAshiftEq]
        exact hAshiftPoly
      dsimp [Mshift]
      exact helperForTheorem_19_1_polyhedral_inter hDirPoly hLevelZeroPoly
    have hC1primePoly : IsPolyhedralConvexSet n C1prime := by
      exact polyhedral_convexSet_add n K Mshift hKpoly hMshiftPoly
    have hC1primeCone : IsConeSet n C1prime := by
      intro z hz t ht
      rcases hz with ⟨k, hkK, m, hmM, rfl⟩
      refine ⟨t • k, hKcone k hkK t ht, t • m, ?_, by simp [smul_add]⟩
      rcases hmM with ⟨hmDir, hmcEq⟩
      constructor
      · exact A.direction.smul_mem t hmDir
      · calc
          (t • m) ⬝ᵥ c = t * (m ⬝ᵥ c) := by
            simp [smul_dotProduct]
          _ = 0 := by simp [hmcEq]
    have h0Conv : (0 : Fin n → ℝ) ∈ convexConeGenerated n Cshift := by
      have h0 :
          (0 : Fin n → ℝ) ∈
            Set.insert 0 (ConvexCone.hull ℝ Cshift : Set (Fin n → ℝ)) :=
        (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa [convexConeGenerated] using h0
    have h0K : (0 : Fin n → ℝ) ∈ K := subset_closure h0Conv
    have h0Mshift : (0 : Fin n → ℝ) ∈ Mshift := by
      constructor
      · exact A.direction.zero_mem
      · simp
    have hC1primeNe : C1prime.Nonempty := by
      refine ⟨0, ?_⟩
      exact ⟨0, h0K, 0, h0Mshift, by simp [C1prime]⟩
    have hMeetImpliesContainsAll :
        ∀ {a : Fin n → ℝ},
          a ≠ 0 →
          C1prime ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} →
          (∃ x : Fin n → ℝ, x ∈ RiShift ∧ x ⬝ᵥ a ≤ 0) →
          RiShift ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
      intro a ha0 hC1primeSub hMeet
      have hMshiftNeg :
          ∀ m : Fin n → ℝ, m ∈ Mshift → -m ∈ Mshift := by
        intro m hm
        rcases hm with ⟨hmDir, hmcEq⟩
        constructor
        · exact A.direction.neg_mem hmDir
        · simp [dotProduct_neg, hmcEq]
      have hMshiftSub :
          Mshift ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
        intro m hmM
        have hmPrime : m ∈ C1prime := by
          exact ⟨0, h0K, m, hmM, by simp [C1prime]⟩
        exact hC1primeSub hmPrime
      have hBoundaryEq :
          ∀ m : Fin n → ℝ, m ∈ Mshift → m ⬝ᵥ a = 0 :=
        helperForTheorem_20_2_boundary_eq_zero_of_neg_closed_subset_halfspace_zero
          (n := n) (M := Mshift) (a := a) hMshiftNeg hMshiftSub
      rcases hMeet with ⟨z0, hz0Ri, hz0Le⟩
      have hClosedHalfSub :
          {x : Fin n → ℝ | x ∈ (A.direction : Set (Fin n → ℝ)) ∧ x ⬝ᵥ c ≤ 0} ⊆
            {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
        exact
          helperForTheorem_20_2_halfspace_contains_closed_half_subspace_of_boundary_and_strict_meet
            (A := A.direction) (a := a) (c := c) (v := z0) (z0 := z0)
            hz0Ri.1 hz0Ri.2
            (by
              intro m hmM
              exact hBoundaryEq m hmM)
            hz0Ri hz0Le
      intro z hzRi
      exact hClosedHalfSub ⟨hzRi.1, le_of_lt hzRi.2⟩
    rcases
        helperForTheorem_20_2_exists_homogeneous_factor_disjoint_of_not_subset_polyhedralCone
          (n := n) (C' := C1prime) (Ri := RiShift)
          hC1primeNe hC1primePoly hC1primeCone hRiNotSubsetC1prime
          hMeetImpliesContainsAll with
      ⟨a, ha0, hC1primeSub, hHalfDisj⟩
    have hMshiftNegA :
        ∀ m : Fin n → ℝ, m ∈ Mshift → -m ∈ Mshift := by
      intro m hm
      rcases hm with ⟨hmDir, hmcEq⟩
      constructor
      · exact A.direction.neg_mem hmDir
      · simp [dotProduct_neg, hmcEq]
    have hMshiftSubA :
        Mshift ⊆ {x : Fin n → ℝ | x ⬝ᵥ a ≤ 0} := by
      intro m hmM
      have hmPrime : m ∈ C1prime := by
        exact ⟨0, h0K, m, hmM, by simp [C1prime]⟩
      exact hC1primeSub hmPrime
    have hBoundaryZeroMshift :
        ∀ m : Fin n → ℝ, m ∈ Mshift → m ⬝ᵥ a = 0 :=
      helperForTheorem_20_2_boundary_eq_zero_of_neg_closed_subset_halfspace_zero
        (n := n) (M := Mshift) (a := a) hMshiftNegA hMshiftSubA
    let H : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ a = mBase ⬝ᵥ a}
    have hC₁leH :
        ∀ x : Fin n → ℝ, x ∈ C₁ → x ⬝ᵥ a ≤ mBase ⬝ᵥ a := by
      intro x hxC₁
      have hxShift : x - mBase ∈ Cshift := by
        dsimp [Cshift]
        change (x - mBase) + mBase ∈ C₁
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxC₁
      have hxConv : x - mBase ∈ convexConeGenerated n Cshift := by
        exact
          rayNonneg_subset_convexConeGenerated n Cshift
            ⟨x - mBase, hxShift, 1, by norm_num, by simp⟩
      have hxK : x - mBase ∈ K := subset_closure hxConv
      have hxPrime : x - mBase ∈ C1prime := by
        exact ⟨x - mBase, hxK, 0, h0Mshift, by simp [C1prime]⟩
      have hxLe0 : (x - mBase) ⬝ᵥ a ≤ 0 := hC1primeSub hxPrime
      calc
        x ⬝ᵥ a = (x - mBase) ⬝ᵥ a + mBase ⬝ᵥ a := by
          simp [sub_eq_add_neg, add_dotProduct]
        _ ≤ mBase ⬝ᵥ a := by linarith [hxLe0]
    have hC₂geH :
        ∀ y : Fin n → ℝ, y ∈ C₂ → mBase ⬝ᵥ a ≤ y ⬝ᵥ a := by
      intro y hyC₂
      have hyA : y ∈ (A : Set (Fin n → ℝ)) := subset_affineSpan (k := ℝ) (s := C₂) hyC₂
      have hyShiftDir : y - mBase ∈ A.direction := by
        simpa [vsub_eq_sub] using A.vsub_mem_direction hyA hmBaseA
      have hyShiftLe : (y - mBase) ⬝ᵥ c ≤ 0 := by
        calc
          (y - mBase) ⬝ᵥ c = y ⬝ᵥ c - mBase ⬝ᵥ c := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ ≤ 0 := by linarith [hC₂le y hyC₂, hmBaseEq]
      by_cases hyStrict : (y - mBase) ⬝ᵥ c < 0
      · have hyRi : y - mBase ∈ RiShift := ⟨hyShiftDir, hyStrict⟩
        have hyNotLe : ¬ (y - mBase) ⬝ᵥ a ≤ 0 := by
          intro hyLe
          exact hHalfDisj.le_bot ⟨hyLe, hyRi⟩
        have hyPos : 0 < (y - mBase) ⬝ᵥ a := lt_of_not_ge hyNotLe
        exact le_of_lt <| calc
          mBase ⬝ᵥ a < (y - mBase) ⬝ᵥ a + mBase ⬝ᵥ a := by linarith
          _ = y ⬝ᵥ a := by
                simp [sub_eq_add_neg, add_dotProduct]
      · have hyEq : (y - mBase) ⬝ᵥ c = 0 := by
          linarith [hyShiftLe]
        have hyM : y - mBase ∈ Mshift := ⟨hyShiftDir, hyEq⟩
        have hyEqA : (y - mBase) ⬝ᵥ a = 0 := hBoundaryZeroMshift (y - mBase) hyM
        exact le_of_eq <| calc
          mBase ⬝ᵥ a = (y - mBase) ⬝ᵥ a + mBase ⬝ᵥ a := by simp [hyEqA]
          _ = y ⬝ᵥ a := by
                simp [sub_eq_add_neg, add_dotProduct]
    have hSepH : HyperplaneSeparates n H C₁ C₂ := by
      refine ⟨hC₁ne, hC₂ne, a, mBase ⬝ᵥ a, ha0, rfl, Or.inl ?_⟩
      refine ⟨?_, ?_⟩
      · intro x hxC₁
        exact hC₁leH x hxC₁
      · intro y hyC₂
        exact hC₂geH y hyC₂
    have hyRnotH : yR ∉ H := by
      have hyRA : yR ∈ (A : Set (Fin n → ℝ)) := subset_affineSpan (k := ℝ) (s := C₂) hyRC₂
      have hyRShiftDir : yR - mBase ∈ A.direction := by
        simpa [vsub_eq_sub] using A.vsub_mem_direction hyRA hmBaseA
      have hyRShiftStrict : (yR - mBase) ⬝ᵥ c < 0 := by
        calc
          (yR - mBase) ⬝ᵥ c = yR ⬝ᵥ c - mBase ⬝ᵥ c := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ < 0 := by linarith [hyRlt, hmBaseEq]
      have hyRri : yR - mBase ∈ RiShift := ⟨hyRShiftDir, hyRShiftStrict⟩
      have hyRnotLe : ¬ (yR - mBase) ⬝ᵥ a ≤ 0 := by
        intro hyLe
        exact hHalfDisj.le_bot ⟨hyLe, hyRri⟩
      have hyRpos : 0 < (yR - mBase) ⬝ᵥ a := lt_of_not_ge hyRnotLe
      intro hyRH
      have hyReq : yR ⬝ᵥ a = mBase ⬝ᵥ a := by
        simpa [H] using hyRH
      have hyRzero : (yR - mBase) ⬝ᵥ a = 0 := by
        calc
          (yR - mBase) ⬝ᵥ a = yR ⬝ᵥ a - mBase ⬝ᵥ a := by
            simp [sub_eq_add_neg, add_dotProduct]
          _ = 0 := by simp [hyReq]
      linarith
    have hC₂notSubsetH : ¬ C₂ ⊆ H := by
      intro hC₂subH
      exact hyRnotH (hC₂subH hyRC₂)
    refine ⟨H, ?_, hC₂notSubsetH⟩
    refine ⟨hSepH, ?_⟩
    intro hBoth
    exact hC₂notSubsetH hBoth.2

/-- Case-2 local contradiction bottleneck:
under active noncontainment-negation, plus face-vs-point strong separation and
a crossing witness `γ < y ⬝ᵥ c`, derive contradiction. -/
lemma helperForTheorem_20_2_case2_face_point_c2_side_contradiction
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    {x0 : Fin n → ℝ}
    (hx0ri : x0 ∈ intrinsicInterior ℝ C₂)
    (hx0lt : x0 ⬝ᵥ c < γ)
    (hStrongFace :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesStrongly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({x0} : Set (Fin n → ℝ)))
    {y : Fin n → ℝ}
    (hyC₂ : y ∈ C₂)
    (hyGt : γ < y ⬝ᵥ c) :
    False := by
  let D : Set (Fin n → ℝ) := C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))
  by_cases hDne : D.Nonempty
  · have hSepExists :
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
      helperForTheorem_20_2_noncontainment_separator_of_nonempty_left_inter_affineSpan
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty (by simpa [D] using hDne)
    exact hNoNoncontainment hSepExists
  · have hDempty : D = (∅ : Set (Fin n → ℝ)) := Set.not_nonempty_iff_eq_empty.mp hDne
    have hSepExists :
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
      helperForTheorem_20_2_noncontainment_separator_of_empty_left_inter_affineSpan
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₁poly (by simpa [D] using hDempty)
    exact hNoNoncontainment hSepExists

/-- Early reusable Case-2 separator-data core:
from explicit `C₂`-side control and a strict right witness in `C₂`,
construct global separator data with a strict right witness. -/
lemma helperForTheorem_20_2_case2_chain_to_global_separator_data_core
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    (hC₂_le : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ)
    {xR : Fin n → ℝ}
    (hxRC₂ : xR ∈ C₂)
    (hxRlt : xR ⬝ᵥ c < γ) :
    ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
      cτ ≠ 0 ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
        (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · rcases hSep with ⟨H, hHproper, hC₂notSubsetH⟩
    rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hHproper with
      ⟨cτ, γτ, hcτ0, hHdef, hC₁geτ, hC₂leτ, _hnotBoth⟩
    have hyRstrictτ : ∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ := by
      rcases Set.not_subset.mp hC₂notSubsetH with ⟨yR, hyRC₂, hyRnotH⟩
      have hyRne : yR ⬝ᵥ cτ ≠ γτ := by
        intro hyReq
        apply hyRnotH
        simpa [hHdef, hyReq]
      have hyRle : yR ⬝ᵥ cτ ≤ γτ := hC₂leτ yR hyRC₂
      exact ⟨yR, hyRC₂, lt_of_le_of_ne hyRle hyRne⟩
    exact ⟨cτ, γτ, hcτ0, hC₂leτ, hyRstrictτ, hC₁geτ⟩
  · have hBuildFromEps :
        ∀ ε : ℝ,
          0 < ε →
          b0 + ε • c ≠ 0 →
          (∀ x : Fin n → ℝ, x ∈ C₁ → β0 + ε * γ ≤ x ⬝ᵥ (b0 + ε • c)) →
          ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
            cτ ≠ 0 ∧
              (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
              (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
              (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
      intro ε hεpos hcτ0 hC₁geτ
      refine ⟨b0 + ε • c, β0 + ε * γ, hcτ0, ?_, ?_, hC₁geτ⟩
      · intro y hyC₂
        have hyb0 : y ⬝ᵥ b0 = β0 := hC₂eqLevel0 hyC₂
        have hycLe : y ⬝ᵥ c ≤ γ := hC₂_le y hyC₂
        calc
          y ⬝ᵥ (b0 + ε • c) = y ⬝ᵥ b0 + ε * (y ⬝ᵥ c) := by
            simp [add_dotProduct, smul_dotProduct]
          _ ≤ β0 + ε * γ := by
            nlinarith [hyb0, hycLe, hεpos]
      · refine ⟨xR, hxRC₂, ?_⟩
        have hxRb0 : xR ⬝ᵥ b0 = β0 := hC₂eqLevel0 hxRC₂
        calc
          xR ⬝ᵥ (b0 + ε • c) = xR ⬝ᵥ b0 + ε * (xR ⬝ᵥ c) := by
            simp [add_dotProduct, smul_dotProduct]
          _ < β0 + ε * γ := by
            nlinarith [hxRb0, hxRlt, hεpos]
    have hChooseEps :
        ∃ ε : ℝ, 0 < ε ∧
          b0 + ε • c ≠ 0 ∧
          (∀ x : Fin n → ℝ, x ∈ C₁ → β0 + ε * γ ≤ x ⬝ᵥ (b0 + ε • c)) :=
      helperForTheorem_20_2_case2_chain_choose_tilt_epsilon
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₁poly
        hC₁ge0 hC₂eqLevel0 hFace_ge hxRlt hSep
    rcases hChooseEps with ⟨ε, hεpos, hcτ0, hC₁geτ⟩
    exact hBuildFromEps ε hεpos hcτ0 hC₁geτ

/-- Case-2 bridge (isolated final jump):
upgrade face-vs-point proper separation on the boundary level face into a
global proper separator of `C₁` and `C₂` that does not contain `C₂`. -/
lemma helperForTheorem_20_2_case2_face_point_to_global_noncontainment_core
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    {x0 : Fin n → ℝ}
    (hx0ri : x0 ∈ intrinsicInterior ℝ C₂)
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    (hx0lt : x0 ⬝ᵥ c < γ) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · exact hSep
  · have hGlobalSeparatorData :
        ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
          cτ ≠ 0 ∧
            (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
            (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
            (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
      have hC₂le : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ := by
        intro y hyC₂
        by_contra hyNotLe
        have hyGt : γ < y ⬝ᵥ c := lt_of_not_ge hyNotLe
        let F : Set (Fin n → ℝ) := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
        have hC₁conv : Convex ℝ C₁ :=
          helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
        have hFpoly : IsPolyhedralConvexSet n F := by
          simpa [F] using
            helperForTheorem_20_2_polyhedral_level_face_of_left_ge
              (n := n) (C₁ := C₁) (b := b0) (β := β0) hC₁poly hC₁ge0 hC₁conv
        have hx0notC₁ : x0 ∉ C₁ := by
          intro hx0C₁
          have hxInter : x0 ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hx0C₁, hx0ri⟩
          have hxEmpty : x0 ∈ (∅ : Set (Fin n → ℝ)) := by
            simpa [hleftRiEmpty] using hxInter
          exact hxEmpty.elim
        have hx0notF : x0 ∉ F := by
          intro hx0F
          exact hx0notC₁ hx0F.1
        by_cases hFempty : F = (∅ : Set (Fin n → ℝ))
        · let L : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
          have hLpoly : IsPolyhedralConvexSet n L := by
            let a : Fin 1 → Fin n → ℝ := fun _ => b0
            let α : Fin 1 → ℝ := fun _ => β0
            have hpolySystem :
                IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} := by
              simpa using
                (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
                  n 1 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
            have hEq : {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} = L := by
              ext x
              constructor
              · intro hx
                have hx0 : x ⬝ᵥ a 0 = α 0 := hx 0
                simpa [L, a, α] using hx0
              · intro hx i
                have hi0 : i = 0 := Subsingleton.elim i 0
                subst hi0
                simpa [L, a, α] using hx
            simpa [hEq] using hpolySystem
          have hLne : L.Nonempty := by
            rcases hC₂ne with ⟨u, huC₂⟩
            exact ⟨u, hC₂eqLevel0 huC₂⟩
          have hC₁disjL : Disjoint C₁ L := by
            refine Set.disjoint_left.2 ?_
            intro x hxC₁ hxL
            have hxFace : x ∈ F := ⟨hxC₁, hxL⟩
            have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
              simpa [hFempty] using hxFace
            exact hxEmpty.elim
          have hStrongC₁L : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ L := by
            exact
              exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
                (n := n) (C₁ := C₁) (C₂ := L)
                hC₁ne hLne hC₁disjL hC₁poly hLpoly
          have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
            rcases hStrongC₁L with ⟨Hs, hHs⟩
            refine ⟨Hs, ?_⟩
            exact
              hyperplaneSeparatesStrongly_mono_sets
                (hH := hHs)
                (hB₁ := by intro x hx; exact hx)
                (hB₂ := by
                  intro u huC₂
                  exact hC₂eqLevel0 huC₂)
                hC₁ne hC₂ne
          have hSepExists :
              ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
            helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
              (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
          exact False.elim (hSep hSepExists)
        · have hFne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hFempty
          have hFdisj :
              Disjoint F ({x0} : Set (Fin n → ℝ)) := by
            exact Set.disjoint_singleton_right.2 hx0notF
          have hStrongFaceF :
              ∃ Hs : Set (Fin n → ℝ),
                HyperplaneSeparatesStrongly n Hs F ({x0} : Set (Fin n → ℝ)) := by
            exact
              exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
                (n := n) (C₁ := F) (C₂ := ({x0} : Set (Fin n → ℝ)))
                hFne (Set.singleton_nonempty x0) hFdisj hFpoly
                (helperForTheorem_20_2_singleton_polyhedral (n := n) x0)
          have hStrongFace :
              ∃ Hs : Set (Fin n → ℝ),
                HyperplaneSeparatesStrongly n Hs
                  (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
                  ({x0} : Set (Fin n → ℝ)) := by
            simpa [F] using hStrongFaceF
          exact
            helperForTheorem_20_2_case2_face_point_c2_side_contradiction
              (n := n) (C₁ := C₁) (C₂ := C₂)
              hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight
              hSep hC₁ge0 hC₂eqLevel0 hFace_ge hx0ri hx0lt hStrongFace hyC₂ hyGt
      exact
        helperForTheorem_20_2_case2_chain_to_global_separator_data_core
          (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₁poly
          hC₁ge0 hC₂eqLevel0 hFace_ge hC₂le (intrinsicInterior_subset hx0ri) hx0lt
    rcases hGlobalSeparatorData with
      ⟨cτ, γτ, hcτ0, hC₂leτ, hyRstrictτ, hC₁geτ⟩
    rcases hyRstrictτ with ⟨yR, hyRC₂, hyRltτ⟩
    let Hτ : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ cτ = γτ}
    have hSepτ : HyperplaneSeparates n Hτ C₁ C₂ := by
      refine ⟨hC₁ne, hC₂ne, cτ, γτ, hcτ0, rfl, Or.inr ?_⟩
      refine ⟨?_, ?_⟩
      · intro y hyC₂
        exact hC₂leτ y hyC₂
      · intro x hxC₁
        exact hC₁geτ x hxC₁
    have hC₂notSubsetHτ : ¬ C₂ ⊆ Hτ := by
      intro hC₂subsetHτ
      have hyRHτ : yR ∈ Hτ := hC₂subsetHτ hyRC₂
      have hyReqτ : yR ⬝ᵥ cτ = γτ := by
        simpa [Hτ] using hyRHτ
      exact (lt_irrefl γτ) (by simpa [hyReqτ] using hyRltτ)
    have hProperτ : HyperplaneSeparatesProperly n Hτ C₁ C₂ := by
      refine ⟨hSepτ, ?_⟩
      intro hBoth
      exact hC₂notSubsetHτ hBoth.2
    exact ⟨Hτ, hProperτ, hC₂notSubsetHτ⟩

/-- Case-2 bridge (isolated final jump):
upgrade face-vs-point proper separation on the boundary level face into a
global proper separator of `C₁` and `C₂` that does not contain `C₂`. -/
lemma helperForTheorem_20_2_case2_face_point_to_global_noncontainment_bridge
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    {b0 : Fin n → ℝ} {β0 : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    {x0 : Fin n → ℝ}
    (hx0ri : x0 ∈ intrinsicInterior ℝ C₂)
    (hFacePointProperNotContain :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesProperly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({x0} : Set (Fin n → ℝ)) ∧
        ¬ ({x0} : Set (Fin n → ℝ)) ⊆ Hs) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · exact hSep
  · rcases
        helperForTheorem_20_2_face_point_oriented_data_of_proper_not_contain_singleton
          (C₁ := C₁) (b0 := b0) (β0 := β0) (x0 := x0)
          hFacePointProperNotContain with
      ⟨c, γ, _hc0, hFace_ge, hx0lt⟩
    have hSepExists :
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
      exact
        helperForTheorem_20_2_case2_face_point_to_global_noncontainment_core
          (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight
          hC₁ge0 hC₂eqLevel0 hx0ri
          hFace_ge
          hx0lt
    exact (False.elim (hSep hSepExists))

/-- Legacy crossing-point bottleneck (isolated):
from a right-side crossing witness `γ < y ⬝ᵥ c` under the active
`¬ ∃`-noncontainment branch, extract a noncontainment proper separator. -/
lemma helperForTheorem_20_2_case2_chain_legacy_separator_of_crossing
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    {xR : Fin n → ℝ}
    (hxRri : xR ∈ intrinsicInterior ℝ C₂)
    (hxRlt : xR ⬝ᵥ c < γ)
    (hStrongFace :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesStrongly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({xR} : Set (Fin n → ℝ)))
    {y : Fin n → ℝ}
    (hyC₂ : y ∈ C₂)
    (hyGt : γ < y ⬝ᵥ c) :
    False := by
  exact
    helperForTheorem_20_2_case2_face_point_c2_side_contradiction
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight
      hNoNoncontainment hC₁ge0 hC₂eqLevel0 hFace_ge hxRri hxRlt hStrongFace hyC₂ hyGt

/-- Legacy singleton-face bottleneck (isolated):
under the active `¬ ∃`-noncontainment branch, upgrade singleton strong-face
data to whole-`C₂` side control for the chosen `(c, γ)` pair. -/
lemma helperForTheorem_20_2_case2_chain_legacy_c2_side_control
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    {xR : Fin n → ℝ}
    (hxRri : xR ∈ intrinsicInterior ℝ C₂)
    (hxRlt : xR ⬝ᵥ c < γ)
    (hStrongFace :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesStrongly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({xR} : Set (Fin n → ℝ))) :
    ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ := by
  intro y hyC₂
  by_contra hyNotLe
  have hyGt : γ < y ⬝ᵥ c := lt_of_not_ge hyNotLe
  have hFalse : False :=
    helperForTheorem_20_2_case2_chain_legacy_separator_of_crossing
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight hNoNoncontainment
      hC₁ge0 hC₂eqLevel0 hFace_ge hxRri hxRlt hStrongFace hyC₂ hyGt
  exact hFalse.elim

/-- Isolated Case-2 chain bottleneck for Theorem 20.2 :
from contains-right and boundary-face separation inputs, construct global
separator data with a strict right witness. -/
lemma helperForTheorem_20_2_case2_chain_to_global_separator_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    (hC₂_le : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ)
    {xR : Fin n → ℝ}
    (hxRri : xR ∈ intrinsicInterior ℝ C₂)
    (hxRlt : xR ⬝ᵥ c < γ) :
    ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
      cτ ≠ 0 ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
        (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
  exact
    helperForTheorem_20_2_case2_chain_to_global_separator_data_core
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₁poly
      hC₁ge0 hC₂eqLevel0 hFace_ge hC₂_le (intrinsicInterior_subset hxRri) hxRlt

/-- Legacy singleton-strong-face bridge (temporary compatibility wrapper while
downstream still supplies singleton strong-separation data instead of explicit
`hC₂_le`, and runs under the active `¬ ∃`-noncontainment branch). -/
lemma helperForTheorem_20_2_case2_chain_to_global_separator_data_legacy
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H)
    {b0 c : Fin n → ℝ} {β0 γ : ℝ}
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hFace_ge :
      ∀ x : Fin n → ℝ,
        x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c)
    {xR : Fin n → ℝ}
    (hxRri : xR ∈ intrinsicInterior ℝ C₂)
    (hxRlt : xR ⬝ᵥ c < γ)
    (hStrongFace :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesStrongly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({xR} : Set (Fin n → ℝ))) :
    ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
      cτ ≠ 0 ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
        (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
  have hC₂_le : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ :=
    helperForTheorem_20_2_case2_chain_legacy_c2_side_control
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
      hContainsRight hNoNoncontainment
      hC₁ge0 hC₂eqLevel0 hFace_ge hxRri hxRlt hStrongFace
  exact
    helperForTheorem_20_2_case2_chain_to_global_separator_data
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
      hContainsRight hC₁ge0 hC₂eqLevel0 hFace_ge hC₂_le hxRri hxRlt

/-- Helper for Theorem 20.2: nonempty-level-face strong branch under oriented
contains-right data.

Given a strong separator between the boundary face
`C₁ ∩ {x | x ⬝ᵥ b0 = β0}` and an intrinsic-interior point `xR ∈ ri(C₂)`, plus a
Case-2 local-to-global bridge hypothesis (`hCase2Bridge`), produce a proper
separator of `C₁` and `C₂` that does not contain `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_contains_right_nonempty_face_strong_case
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    {b0 : Fin n → ℝ} {β0 : ℝ}
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    {xR : Fin n → ℝ}
    (hxRri : xR ∈ intrinsicInterior ℝ C₂)
    (hStrongFace :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesStrongly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({xR} : Set (Fin n → ℝ)))
    (hCase2C₂Side :
      ∀ {c : Fin n → ℝ} {γ : ℝ},
        (∀ x : Fin n → ℝ,
          x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c) →
        xR ⬝ᵥ c < γ →
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ))
    (hCase2Bridge :
      ∀ {c : Fin n → ℝ} {γ : ℝ},
        (∀ x : Fin n → ℝ,
          x ∈ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) → γ ≤ x ⬝ᵥ c) →
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ) →
        xR ⬝ᵥ c < γ →
        (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) →
        ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
          cτ ≠ 0 ∧
            (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
            (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ)) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  have hFaceProperNotContainSingleton :
      ∃ Hs : Set (Fin n → ℝ),
        HyperplaneSeparatesProperly n Hs
          (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          ({xR} : Set (Fin n → ℝ)) ∧
        ¬ ({xR} : Set (Fin n → ℝ)) ⊆ Hs := by
    exact
      helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
        (n := n)
        (C₁ := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
        (C₂ := ({xR} : Set (Fin n → ℝ)))
        hStrongFace
  rcases
      helperForTheorem_20_2_face_point_oriented_data_of_proper_not_contain_singleton
        (C₁ := C₁) (b0 := b0) (β0 := β0) (x0 := xR)
        hFaceProperNotContainSingleton with
    ⟨c, γ, _hc0, hFace_ge, hxRlt⟩
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · exact hSep
  · by_cases hNoContainsRight :
        ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H
    · have hSepExists :
          ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
        helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
          (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoContainsRight
      exact False.elim (hSep hSepExists)
    · have hContainsRight :
          ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H :=
        helperForTheorem_20_2_exists_contains_right_separator_of_not_no_contains_right
          (n := n) (C₁ := C₁) (C₂ := C₂) hNoContainsRight
      have hC₂le : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ c ≤ γ :=
        hCase2C₂Side hFace_ge hxRlt
      rcases hCase2Bridge hFace_ge hC₂le hxRlt hContainsRight with
        ⟨cτ, γτ, hcτ0, hC₂leτ, hyRstrictτ, hC₁geτ⟩
      rcases hyRstrictτ with ⟨yR, hyRC₂, hyRltτ⟩
      let Hτ : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ cτ = γτ}
      have hSepτ : HyperplaneSeparates n Hτ C₁ C₂ := by
        refine ⟨hC₁ne, hC₂ne, cτ, γτ, hcτ0, rfl, Or.inr ?_⟩
        refine ⟨?_, ?_⟩
        · intro y hyC₂
          exact hC₂leτ y hyC₂
        · intro x hxC₁
          exact hC₁geτ x hxC₁
      have hC₂notSubsetHτ : ¬ C₂ ⊆ Hτ := by
        intro hC₂subsetHτ
        have hyRHτ : yR ∈ Hτ := hC₂subsetHτ hyRC₂
        have hyReqτ : yR ⬝ᵥ cτ = γτ := by
          simpa [Hτ] using hyRHτ
        exact (lt_irrefl γτ) (by simpa [hyReqτ] using hyRltτ)
      have hProperτ : HyperplaneSeparatesProperly n Hτ C₁ C₂ := by
        refine ⟨hSepτ, ?_⟩
        intro hBoth
        exact hC₂notSubsetHτ hBoth.2
      exact ⟨Hτ, hProperτ, hC₂notSubsetHτ⟩

/-- Helper for Theorem 20.2: minimal contains-right bridge core under the main
left-`ri`-empty/polyhedral-left hypotheses.

This isolates the exact unresolved frontier:
from a contains-right proper separator witness, produce a proper separator that
does not contain `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_contains_right_under_left_ri_empty_polyLeft_core
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · exact hSep
  · rcases hContainsRight with ⟨H0, hH0proper, hC₂subsetH0⟩
    rcases hyperplaneSeparatesProperly_oriented n H0 C₁ C₂ hH0proper with
      ⟨b0, β0, hb0, hH0def, hC₁ge0, hC₂le0, _hnotBoth0⟩
    have hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0} := by
      intro y hyC₂
      have hyH0 : y ∈ H0 := hC₂subsetH0 hyC₂
      simpa [hH0def] using hyH0
    have hBoundaryCase :
        ∃ xR : Fin n → ℝ,
          xR ∈ intrinsicInterior ℝ C₂ ∧
          xR ∉ C₁ ∧
          ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ)) ∨
            ∃ Hs : Set (Fin n → ℝ),
              HyperplaneSeparatesStrongly n Hs
                (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
                ({xR} : Set (Fin n → ℝ))) :=
      helperForTheorem_20_2_boundary_face_case_split_of_oriented_contains_right_data
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁poly hC₂ne hC₂conv hleftRiEmpty (b := b0) (β := β0) hC₁ge0
    rcases hBoundaryCase with ⟨xR, hxRri, hxRnotC₁, hFaceCase⟩
    cases hFaceCase with
    | inl hFempty =>
        let L : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
        have hLpoly : IsPolyhedralConvexSet n L := by
          let a : Fin 1 → Fin n → ℝ := fun _ => b0
          let α : Fin 1 → ℝ := fun _ => β0
          have hpolySystem :
              IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} := by
            simpa using
              (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
                n 1 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
          have hEq : {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} = L := by
            ext x
            constructor
            · intro hx
              have hx0 : x ⬝ᵥ a 0 = α 0 := hx 0
              simpa [L, a, α] using hx0
            · intro hx i
              have hi0 : i = 0 := Subsingleton.elim i 0
              subst hi0
              simpa [L, a, α] using hx
          simpa [hEq] using hpolySystem
        have hLne : L.Nonempty := by
          rcases hC₂ne with ⟨y, hyC₂⟩
          exact ⟨y, hC₂eqLevel0 hyC₂⟩
        have hC₁disjL : Disjoint C₁ L := by
          refine Set.disjoint_left.2 ?_
          intro x hxC₁ hxL
          have hxFace : x ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} := ⟨hxC₁, hxL⟩
          have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
            simpa [hFempty] using hxFace
          exact hxEmpty.elim
        have hStrongC₁L : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ L := by
          exact
            exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
              (n := n) (C₁ := C₁) (C₂ := L)
              hC₁ne hLne hC₁disjL hC₁poly hLpoly
        have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
          rcases hStrongC₁L with ⟨Hs, hHs⟩
          refine ⟨Hs, ?_⟩
          exact
            hyperplaneSeparatesStrongly_mono_sets
              (hH := hHs)
              (hB₁ := by intro x hx; exact hx)
              (hB₂ := by
                intro y hyC₂
                exact hC₂eqLevel0 hyC₂)
              hC₁ne hC₂ne
        have hSepExists :
            ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
          helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
            (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
        exact (False.elim (hSep hSepExists))
    | inr hStrongFace =>
        have hSepExists :
            ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
          exact
            helperForTheorem_20_2_noncontainment_separator_of_contains_right_nonempty_face_strong_case
              (n := n) (C₁ := C₁) (C₂ := C₂)
              hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
              hC₂eqLevel0 hxRri hStrongFace
              (hCase2C₂Side := by
                intro c γ hFace_ge hxRlt
                exact
                  helperForTheorem_20_2_case2_chain_legacy_c2_side_control
                    (n := n) (C₁ := C₁) (C₂ := C₂)
                    hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
                    ⟨H0, hH0proper, hC₂subsetH0⟩ hSep hC₁ge0 hC₂eqLevel0
                    hFace_ge hxRri hxRlt hStrongFace)
              (hCase2Bridge := by
                intro c γ hFace_ge hC₂_le hxRlt hContainsRight
                exact
                  helperForTheorem_20_2_case2_chain_to_global_separator_data
                    (n := n) (C₁ := C₁) (C₂ := C₂)
                    hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
                    hContainsRight hC₁ge0 hC₂eqLevel0
                    hFace_ge hC₂_le hxRri hxRlt)
        exact False.elim (hSep hSepExists)

/-- Helper for Theorem 20.2: core nonempty-boundary-face bridge.

Given face-level inequality data on
`C₁ ∩ {x | x ⬝ᵥ b0 = β0}` and a strict right witness `xR ∈ ri(C₂)`,
promote it to global oriented separator inequalities on `C₁` and `C₂`. -/
lemma helperForTheorem_20_2_nonempty_boundary_face_global_separator_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {b0 c : Fin n → ℝ} {β0 γ : ℝ} {xR : Fin n → ℝ}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂conv : Convex ℝ C₂)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hC₁ge0 : ∀ x : Fin n → ℝ, x ∈ C₁ → β0 ≤ x ⬝ᵥ b0)
    (hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0})
    (hxRri : xR ∈ intrinsicInterior ℝ C₂):
    ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
      cτ ≠ 0 ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
        (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
        (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) := by
  by_cases hSep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · rcases hSep with ⟨H, hHproper, hC₂notSubsetH⟩
    rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hHproper with
      ⟨cτ, γτ, hcτ0, hHdef, hC₁geτ, hC₂leτ, _hnotBoth⟩
    have hyRstrictτ : ∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ := by
      rcases Set.not_subset.mp hC₂notSubsetH with ⟨yR, hyRC₂, hyRnotH⟩
      have hyRne : yR ⬝ᵥ cτ ≠ γτ := by
        intro hyReq
        apply hyRnotH
        simpa [hHdef, hyReq]
      have hyRle : yR ⬝ᵥ cτ ≤ γτ := hC₂leτ yR hyRC₂
      exact ⟨yR, hyRC₂, lt_of_le_of_ne hyRle hyRne⟩
    exact ⟨cτ, γτ, hcτ0, hC₂leτ, hyRstrictτ, hC₁geτ⟩
  · -- Core nonempty-boundary-face contradiction branch.
    by_cases hFempty : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ))
    · let L : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
      have hLpoly : IsPolyhedralConvexSet n L := by
        let a : Fin 1 → Fin n → ℝ := fun _ => b0
        let α : Fin 1 → ℝ := fun _ => β0
        have hpolySystem :
            IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} := by
          simpa using
            (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
              n 1 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
        have hEq : {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} = L := by
          ext x
          constructor
          · intro hx
            have hx0 : x ⬝ᵥ a 0 = α 0 := hx 0
            simpa [L, a, α] using hx0
          · intro hx i
            have hi0 : i = 0 := Subsingleton.elim i 0
            subst hi0
            simpa [L, a, α] using hx
        simpa [hEq] using hpolySystem
      have hLne : L.Nonempty := by
        rcases hC₂ne with ⟨y, hyC₂⟩
        exact ⟨y, hC₂eqLevel0 hyC₂⟩
      have hC₁disjL : Disjoint C₁ L := by
        refine Set.disjoint_left.2 ?_
        intro x hxC₁ hxL
        have hxFace : x ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} := ⟨hxC₁, hxL⟩
        have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
          simpa [hFempty] using hxFace
        exact hxEmpty.elim
      have hStrongC₁L : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ L := by
        exact
          exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
            (n := n) (C₁ := C₁) (C₂ := L)
            hC₁ne hLne hC₁disjL hC₁poly hLpoly
      have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
        rcases hStrongC₁L with ⟨Hs, hHs⟩
        refine ⟨Hs, ?_⟩
        exact
          hyperplaneSeparatesStrongly_mono_sets
            (hH := hHs)
            (hB₁ := by intro x hx; exact hx)
            (hB₂ := by
              intro y hyC₂
              exact hC₂eqLevel0 hyC₂)
            hC₁ne hC₂ne
      have hSepExists :
          ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
        helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
          (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
      exact (False.elim (hSep hSepExists))
    · -- From the face-level data (`hFace_ge`, `hxRlt`) and `hleftRiEmpty`,
      -- derive a noncontainment separator and contradict `hSep`.
      by_cases hNoContainsRight :
          ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H
      · have hSepExists :
            ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
          helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
            (n := n) (C₁ := C₁) (C₂ := C₂)
            hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoContainsRight
        exact (False.elim (hSep hSepExists))
      · have hContainsRight :
            ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H :=
          helperForTheorem_20_2_exists_contains_right_separator_of_not_no_contains_right
            (n := n) (C₁ := C₁) (C₂ := C₂) hNoContainsRight
        have hFne : (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hFempty
        have hC₁conv : Convex ℝ C₁ :=
          helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
        have hFpoly :
            IsPolyhedralConvexSet n (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) :=
          helperForTheorem_20_2_polyhedral_level_face_of_left_ge
            (n := n) (C₁ := C₁) (b := b0) (β := β0) hC₁poly hC₁ge0 hC₁conv
        have hxRnotC₁ : xR ∉ C₁ := by
          intro hxRC₁
          have hxInter : xR ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hxRC₁, hxRri⟩
          have hxEmpty : xR ∈ (∅ : Set (Fin n → ℝ)) := by
            simpa [hleftRiEmpty] using hxInter
          exact hxEmpty.elim
        have hxRnotF : xR ∉ (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) := by
          intro hxRF
          exact hxRnotC₁ hxRF.1
        have hFdisj :
            Disjoint (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) ({xR} : Set (Fin n → ℝ)) := by
          refine Set.disjoint_singleton_right.mpr ?_
          exact hxRnotF
        have hStrongFace :
            ∃ Hs : Set (Fin n → ℝ),
              HyperplaneSeparatesStrongly n Hs
                (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
                ({xR} : Set (Fin n → ℝ)) := by
          exact
            exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
              (n := n)
              (C₁ := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
              (C₂ := ({xR} : Set (Fin n → ℝ)))
              hFne
              (Set.singleton_nonempty xR)
              hFdisj
              hFpoly
              (helperForTheorem_20_2_singleton_polyhedral (n := n) xR)
        have hSepExists :
            ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
          helperForTheorem_20_2_noncontainment_separator_of_contains_right_nonempty_face_strong_case
            (n := n) (C₁ := C₁) (C₂ := C₂)
            hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
            hC₂eqLevel0 hxRri hStrongFace
            (hCase2C₂Side := by
              intro c γ hFace_ge hxRlt
              exact
                helperForTheorem_20_2_case2_chain_legacy_c2_side_control
                  (n := n) (C₁ := C₁) (C₂ := C₂)
                  hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
                  hContainsRight hSep hC₁ge0 hC₂eqLevel0
                  hFace_ge hxRri hxRlt hStrongFace)
            (hCase2Bridge := by
              intro c γ hFace_ge hC₂_le hxRlt hContainsRight
              exact
                helperForTheorem_20_2_case2_chain_to_global_separator_data
                  (n := n) (C₁ := C₁) (C₂ := C₂)
                  hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty
                  hContainsRight hC₁ge0 hC₂eqLevel0
                  hFace_ge hC₂_le hxRri hxRlt)
        exact (False.elim (hSep hSepExists))

/-- Helper for Theorem 20.2: unresolved contains-right branch upgrade.

This isolates the remaining frontier in the Section 20 bridge:
from contains-right separation data plus oriented level information, produce a
proper separator not containing `C₂`. -/
lemma helperForTheorem_20_2_containsRight_to_noncontainment_bridge_from_oriented_level_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    {b : Fin n → ℝ} {β : ℝ}
    (hb0 : b ≠ 0)
    (hC₂subsetLevel : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β})
    (hC₁notSubsetLevel : ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β})
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  rcases hContainsRight with ⟨H0, hH0proper, hC₂subsetH0⟩
  rcases hyperplaneSeparatesProperly_oriented n H0 C₁ C₂ hH0proper with
    ⟨b0, β0, hb0', hH0def, hC₁ge0, hC₂le0, _hnotBoth0⟩
  have hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0} := by
    intro y hyC₂
    have hyH0 : y ∈ H0 := hC₂subsetH0 hyC₂
    simpa [hH0def] using hyH0
  have hBoundaryCase :
      ∃ xR : Fin n → ℝ,
        xR ∈ intrinsicInterior ℝ C₂ ∧
        xR ∉ C₁ ∧
        ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ)) ∨
          ∃ Hs : Set (Fin n → ℝ),
            HyperplaneSeparatesStrongly n Hs
              (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
              ({xR} : Set (Fin n → ℝ))) :=
    helperForTheorem_20_2_boundary_face_case_split_of_oriented_contains_right_data
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁poly hC₂ne hC₂conv hleftRiEmpty (b := b0) (β := β0) hC₁ge0
  rcases hBoundaryCase with ⟨xR, hxRri, hxRnotC₁, hFaceCase⟩
  have hxRC₂ : xR ∈ C₂ := intrinsicInterior_subset hxRri
  have hxRH0 : xR ∈ H0 := hC₂subsetH0 hxRC₂
  have hxReq0 : xR ⬝ᵥ b0 = β0 := by
    simpa [hH0def] using hxRH0
  have hC₁notSubsetH0 : ¬ C₁ ⊆ H0 := by
    intro hC₁subsetH0
    exact hH0proper.2 ⟨hC₁subsetH0, hC₂subsetH0⟩
  have hxLeftWitness :
      ∃ xL : Fin n → ℝ, xL ∈ C₁ ∧ β0 < xL ⬝ᵥ b0 := by
    rcases Set.not_subset.mp hC₁notSubsetH0 with ⟨xL, hxLC₁, hxLnotH0⟩
    have hxLne : xL ⬝ᵥ b0 ≠ β0 := by
      intro hxEq
      apply hxLnotH0
      simpa [hH0def, hxEq]
    have hxLgt : β0 < xL ⬝ᵥ b0 := by
      exact lt_of_le_of_ne (hC₁ge0 xL hxLC₁) (by simpa [eq_comm] using hxLne)
    exact ⟨xL, hxLC₁, hxLgt⟩
  have hFaceCasePrepared :
      ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ)) →
          (∀ x : Fin n → ℝ, x ∈ C₁ → β0 < x ⬝ᵥ b0))
        ∧
      ((∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesStrongly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
            ({xR} : Set (Fin n → ℝ))) →
        ∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesProperly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
            ({xR} : Set (Fin n → ℝ)) ∧
          ¬ ({xR} : Set (Fin n → ℝ)) ⊆ Hs) := by
    constructor
    · intro hFempty
      intro x hxC₁
      have hxGe : β0 ≤ x ⬝ᵥ b0 := hC₁ge0 x hxC₁
      have hxNe : x ⬝ᵥ b0 ≠ β0 := by
        intro hxEq
        have hxFace : x ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} := ⟨hxC₁, hxEq⟩
        have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
          simpa [hFempty] using hxFace
        exact hxEmpty.elim
      exact lt_of_le_of_ne hxGe (by simpa [eq_comm] using hxNe)
    · intro hStrongFace
      exact
        helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
          (n := n)
          (C₁ := C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
          (C₂ := ({xR} : Set (Fin n → ℝ)))
          hStrongFace
  have _hb0 : b ≠ 0 := hb0
  have _hC₂subsetLevel : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} := hC₂subsetLevel
  have _hC₁notSubsetLevel : ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} := hC₁notSubsetLevel
  have _hC₂eqLevel0 : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b0 = β0} := hC₂eqLevel0
  have _hb0' : b0 ≠ 0 := hb0'
  have _hC₂le0 : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b0 ≤ β0 := hC₂le0
  have _hBoundaryCase :
      xR ∈ intrinsicInterior ℝ C₂ ∧
        xR ∉ C₁ ∧
          ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ)) ∨
            ∃ Hs : Set (Fin n → ℝ),
              HyperplaneSeparatesStrongly n Hs
                (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
                ({xR} : Set (Fin n → ℝ))) := ⟨hxRri, hxRnotC₁, hFaceCase⟩
  have _hxReq0 : xR ⬝ᵥ b0 = β0 := hxReq0
  have _hxLeftWitness : ∃ xL : Fin n → ℝ, xL ∈ C₁ ∧ β0 < xL ⬝ᵥ b0 := hxLeftWitness
  have _hFaceCasePrepared :
      ((C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}) = (∅ : Set (Fin n → ℝ)) →
          (∀ x : Fin n → ℝ, x ∈ C₁ → β0 < x ⬝ᵥ b0))
        ∧
      ((∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesStrongly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
            ({xR} : Set (Fin n → ℝ))) →
        ∃ Hs : Set (Fin n → ℝ),
          HyperplaneSeparatesProperly n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
            ({xR} : Set (Fin n → ℝ)) ∧
          ¬ ({xR} : Set (Fin n → ℝ)) ⊆ Hs) := hFaceCasePrepared
  cases hFaceCase with
  | inl hFempty =>
      let L : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ b0 = β0}
      have hLpoly : IsPolyhedralConvexSet n L := by
        let a : Fin 1 → Fin n → ℝ := fun _ => b0
        let α : Fin 1 → ℝ := fun _ => β0
        have hpolySystem :
            IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} := by
          simpa using
            (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
              n 1 0 a α (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
        have hEq : {x : Fin n → ℝ | ∀ i : Fin 1, x ⬝ᵥ a i = α i} = L := by
          ext x
          constructor
          · intro hx
            have hx0 : x ⬝ᵥ a 0 = α 0 := hx 0
            simpa [L, a, α] using hx0
          · intro hx
            intro i
            have hi0 : i = 0 := Subsingleton.elim i 0
            subst hi0
            simpa [L, a, α] using hx
        simpa [hEq] using hpolySystem
      have hLne : L.Nonempty := by
        rcases hC₂ne with ⟨y, hyC₂⟩
        exact ⟨y, hC₂eqLevel0 hyC₂⟩
      have hC₁disjL : Disjoint C₁ L := by
        refine Set.disjoint_left.2 ?_
        intro x hxC₁ hxL
        have hxFace : x ∈ C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0} := ⟨hxC₁, hxL⟩
        have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
          simpa [hFempty] using hxFace
        exact hxEmpty.elim
      have hStrongC₁L : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ L := by
        exact
          exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
            (n := n) (C₁ := C₁) (C₂ := L)
            hC₁ne hLne hC₁disjL hC₁poly hLpoly
      have hStrongC₁C₂ : ∃ Hs : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n Hs C₁ C₂ := by
        rcases hStrongC₁L with ⟨Hs, hHs⟩
        refine ⟨Hs, ?_⟩
        exact
          hyperplaneSeparatesStrongly_mono_sets
            (hH := hHs)
            (hB₁ := by intro x hx; exact hx)
            (hB₂ := by
              intro y hyC₂
              exact hC₂eqLevel0 hyC₂)
            hC₁ne hC₂ne
      exact
        helperForTheorem_20_2_proper_and_not_containing_of_strong_separator
          (n := n) (C₁ := C₁) (C₂ := C₂) hStrongC₁C₂
  | inr hStrongFace =>
      have hFaceProperNotContainSingleton :
          ∃ Hs : Set (Fin n → ℝ),
            HyperplaneSeparatesProperly n Hs
              (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
              ({xR} : Set (Fin n → ℝ)) ∧
            ¬ ({xR} : Set (Fin n → ℝ)) ⊆ Hs :=
        (hFaceCasePrepared.2 hStrongFace)
      rcases hFaceProperNotContainSingleton with ⟨Hs, hHsproper, hSingletonNotSubsetHs⟩
      have hxRnotHs : xR ∉ Hs := by
        intro hxRinHs
        apply hSingletonNotSubsetHs
        intro z hzSingleton
        have hzEq : z = xR := by
          simpa [Set.mem_singleton_iff] using hzSingleton
        simpa [hzEq] using hxRinHs
      rcases
          hyperplaneSeparatesProperly_oriented n Hs
            (C₁ ∩ {x : Fin n → ℝ | x ⬝ᵥ b0 = β0})
            ({xR} : Set (Fin n → ℝ))
            hHsproper with
        ⟨c, γ, hc0, hHsdef, hFace_ge, hSingleton_le, _hnotBothHs⟩
      have hxRle : xR ⬝ᵥ c ≤ γ := hSingleton_le xR (by simp)
      have hxRne : xR ⬝ᵥ c ≠ γ := by
        intro hxReq
        apply hxRnotHs
        simpa [hHsdef, hxReq]
      have hxRlt : xR ⬝ᵥ c < γ := lt_of_le_of_ne hxRle hxRne
      have hGlobalSeparatorData :
          ∃ cτ : Fin n → ℝ, ∃ γτ : ℝ,
            cτ ≠ 0 ∧
              (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ cτ ≤ γτ) ∧
              (∃ yR : Fin n → ℝ, yR ∈ C₂ ∧ yR ⬝ᵥ cτ < γτ) ∧
              (∀ x : Fin n → ℝ, x ∈ C₁ → γτ ≤ x ⬝ᵥ cτ) :=
        helperForTheorem_20_2_nonempty_boundary_face_global_separator_data
          (C₁ := C₁) (C₂ := C₂) (b0 := b0) (c := c) (β0 := β0) (γ := γ) (xR := xR)
          hC₁ne hC₂ne hC₁poly hC₂conv hleftRiEmpty hC₁ge0 hC₂eqLevel0 hxRri
      rcases hGlobalSeparatorData with
        ⟨cτ, γτ, hcτ0, hC₂leτ, hyRstrictτ, hC₁geτ⟩
      rcases hyRstrictτ with ⟨yR, hyRC₂, hyRltτ⟩
      let Hτ : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ cτ = γτ}
      have hSepτ : HyperplaneSeparates n Hτ C₁ C₂ := by
        refine ⟨hC₁ne, hC₂ne, cτ, γτ, hcτ0, rfl, Or.inr ?_⟩
        refine ⟨?_, ?_⟩
        · intro y hyC₂
          exact hC₂leτ y hyC₂
        · intro x hxC₁
          exact hC₁geτ x hxC₁
      have hC₂notSubsetHτ : ¬ C₂ ⊆ Hτ := by
        intro hC₂subsetHτ
        have hyRHτ : yR ∈ Hτ := hC₂subsetHτ hyRC₂
        have hyReqτ : yR ⬝ᵥ cτ = γτ := by
          simpa [Hτ] using hyRHτ
        exact (lt_irrefl γτ) (by simpa [hyReqτ] using hyRltτ)
      have hProperτ : HyperplaneSeparatesProperly n Hτ C₁ C₂ := by
        refine ⟨hSepτ, ?_⟩
        intro hBoth
        exact hC₂notSubsetHτ hBoth.2
      exact ⟨Hτ, hProperτ, hC₂notSubsetHτ⟩

/-- Helper for Theorem 20.2: reduce oriented contains-right witness data to the
core contains-right-branch upgrade under the main left-`ri` emptiness and
polyhedral-left assumptions. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_oriented_full_data_under_left_ri_empty_polyLeft
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    {b : Fin n → ℝ} {β : ℝ}
    (hb0 : b ≠ 0)
    (hData :
      (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β)) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  have hContainsRightBridge :
      (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) →
        (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) := by
    intro hContainsRight
    exact
      helperForTheorem_20_2_noncontainment_separator_of_contains_right_under_left_ri_empty_polyLeft_core
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight
  exact
    helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_contains_right_bridge
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRightBridge

/-- Helper for Theorem 20.2: dependency-closed oriented-data bridge from a
contains-right separator witness to a separator explicitly not containing `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_oriented_contains_right_data_dependency_closed
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    {b : Fin n → ℝ} {β : ℝ}
    (hb0 : b ≠ 0)
    (hData :
      (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
      (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β)) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  exact
    helperForTheorem_20_2_noncontainment_separator_of_oriented_full_data_under_left_ri_empty_polyLeft
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hb0 hData

/-- Helper for Theorem 20.2: contains-right branch reducing the remaining
noncontainment upgrade to an upstream prerequisite. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_contains_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  exact
    helperForTheorem_20_2_noncontainment_separator_of_contains_right_under_left_ri_empty_polyLeft_core
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight

/-- Helper for Theorem 20.2: prerequisite bridge upgrading
`C₁ ∩ intrinsicInterior ℝ C₂ = ∅` (with nonempty convex `C₂` and polyhedral `C₁`)
to a proper separator that does not contain `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ))) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  by_cases hDne : (C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ))).Nonempty
  · by_cases hNoContainsRight :
        ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H
    · exact
        helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
          (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoContainsRight
    · have hContainsRight :
          ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H :=
        helperForTheorem_20_2_exists_contains_right_separator_of_not_no_contains_right
          (n := n) (C₁ := C₁) (C₂ := C₂) hNoContainsRight
      exact
        helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_contains_right
          (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hContainsRight
  · have hDempty : C₁ ∩ (affineSpan ℝ C₂ : Set (Fin n → ℝ)) = (∅ : Set (Fin n → ℝ)) :=
        Set.not_nonempty_iff_eq_empty.mp hDne
    exact
      helperForTheorem_20_2_noncontainment_separator_of_empty_left_inter_affineSpan
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₁poly hDempty

/-- Helper for Theorem 20.2: reverse bridge from `C₁ ∩ intrinsicInterior ℝ C₂ = ∅`
to a proper separator not containing `C₂` under polyhedral-left hypotheses. -/
lemma helperForTheorem_20_2_exists_separator_not_subset_right_of_inter_empty_polyLeft
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ))) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  exact
    helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty

/-- Theorem 20.2: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` with `C₁`
polyhedral. There exists a hyperplane separating `C₁` and `C₂` properly and not
containing `C₂` if and only if `C₁ ∩ ri(C₂) = ∅` (with `ri` formalized as
`intrinsicInterior`). -/
theorem exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) :
    (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) ↔
      C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) := by
  constructor
  · intro hsep
    exact
      helperForTheorem_20_2_inter_empty_of_exists_separator_not_subset_right
        (C₂ := C₂) (hC₂conv := hC₂conv) hsep
  · intro hleftRiEmpty
    exact
      helperForTheorem_20_2_exists_separator_not_subset_right_of_inter_empty_polyLeft
        hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty

end Section20
end Chap04
