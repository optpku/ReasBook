/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part6

section Chap04
section Section22

/-- A vector `z⋆` separates a family of real sets positively if every admissible choice of
coordinates from those sets has strictly positive pairing with `z⋆`. -/
def PositivelySeparatesIntervalFamily {N : ℕ}
    (I : Fin N → Set ℝ) (zStar : Fin N → ℝ) : Prop :=
  ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 < dotProduct zStar z

/-- The orthogonal complement of a subspace of `ℝ^N`, encoded using the standard dot product on
`Fin N → ℝ`. -/
def dotProductOrthogonalComplement {N : ℕ}
    (L : Submodule ℝ (Fin N → ℝ)) : Submodule ℝ (Fin N → ℝ) :=
  ⨅ z : L, LinearMap.ker ((dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) z.1)

/-- Helper for Theorem 22.6: the ad hoc dot-product orthogonal complement agrees with the
standard bilinear-form orthogonal complement for `dotProductBilin`. -/
lemma helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) :
    dotProductOrthogonalComplement L =
      LinearMap.BilinForm.orthogonal
        (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) L := by
  -- Unfold both sides so membership becomes the same family of dot-product vanishing conditions.
  ext x
  simp [dotProductOrthogonalComplement, LinearMap.BilinForm.orthogonal,
    LinearMap.BilinForm.IsOrtho]

/-- Helper for Theorem 22.6: the coordinate dot-product bilinear form is reflexive. -/
lemma helperForTheorem_22_6_dotProductBilin_isRefl
    {N : ℕ} :
    (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)).IsRefl := by
  -- Symmetry of the coordinate dot product is exactly the reflexivity hypothesis needed for
  -- double-orthogonal arguments.
  intro x y hxy
  simpa [dotProduct_comm] using hxy

/-- Helper for Theorem 22.6: the coordinate dot-product bilinear form is nondegenerate. -/
lemma helperForTheorem_22_6_dotProductBilin_nondegenerate
    {N : ℕ} :
    LinearMap.BilinForm.Nondegenerate
      (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) := by
  -- Test the candidate vector against itself; positive-definiteness forces vanishing.
  intro x hx
  by_contra hx_ne
  have hxx : dotProduct x x = 0 := hx x
  exact hx_ne ((dotProduct_self_eq_zero (v := x)).1 hxx)

/-- Helper for Theorem 22.6: vanishing on a basis of the dot-product orthogonal complement is
equivalent to belonging to the original subspace. -/
lemma helperForTheorem_22_6_annihilates_orthogonalBasis_iff_mem_subspace
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ))
    {ι : Type*} (b : Module.Basis ι ℝ (dotProductOrthogonalComplement L))
    (x : Fin N → ℝ) :
    x ∈ L ↔ ∀ i, dotProduct (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ)) x = 0 := by
  constructor
  · intro hx i
    -- A basis vector of `L⊥` is orthogonal to every vector of `L`, so in particular to `x`.
    have hbi :
        (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ)) ∈
          dotProductOrthogonalComplement L :=
      (b i).2
    have hbi' :
        ∀ y ∈ L, dotProduct y (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ)) = 0 := by
      simpa [helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal L,
        LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho] using hbi
    have hzero :
        dotProduct x (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ)) = 0 :=
      hbi' x hx
    simpa [dotProduct_comm] using hzero
  · intro hx
    -- Vanishing on the basis extends by linearity to vanishing on every vector of `L⊥`.
    have hxorth :
        x ∈ LinearMap.BilinForm.orthogonal
          (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
          (dotProductOrthogonalComplement L) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      rcases (Module.Basis.mem_submodule_iff (b := b)).1 hy with ⟨c, rfl⟩
      calc
        dotProduct (c.sum fun i a => a • (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) x
            = Finset.sum c.support (fun i =>
                dotProduct (c i • (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) x) := by
              simpa [Finsupp.sum] using
                (sum_dotProduct (s := c.support)
                  (u := fun i => c i • (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ)))
                  (v := x))
        _ = Finset.sum c.support (fun i =>
              c i * dotProduct ((((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) x) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                dotProduct (c i • (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) x
                    = dotProduct x (c i • (((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) := by
                        simp [dotProduct_comm]
                _ = c i * dotProduct x ((((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) := by
                        simp [dotProduct_smul, smul_eq_mul]
                _ = c i * dotProduct ((((b i : dotProductOrthogonalComplement L) : Fin N → ℝ))) x := by
                        simp [dotProduct_comm]
        _ = 0 := by
              refine Finset.sum_eq_zero ?_
              intro i hi
              simp [hx i]
    -- Double orthogonality for the nondegenerate dot product returns to the original subspace.
    have hdouble :
        x ∈ LinearMap.BilinForm.orthogonal
          (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
          (LinearMap.BilinForm.orthogonal
            (dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) L) := by
      simpa [helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal L] using hxorth
    have hEq :=
      LinearMap.BilinForm.orthogonal_orthogonal
        (V := Fin N → ℝ) (K := ℝ)
        (B := dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
        (helperForTheorem_22_6_dotProductBilin_nondegenerate (N := N))
        (helperForTheorem_22_6_dotProductBilin_isRefl (N := N)) L
    -- Rewriting the double orthogonal equality finishes the membership claim.
    simpa [hEq] using hdouble

/-- Helper for Theorem 22.6: an orthogonal separator excludes every interval-feasible point of
the subspace. -/
lemma helperForTheorem_22_6_orthogonal_separator_excludes_primal
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    {z zStar : Fin N → ℝ}
    (hzL : z ∈ L)
    (hzStarOrth : zStar ∈ dotProductOrthogonalComplement L)
    (hzI : ∀ j, z j ∈ I j)
    (hSep : PositivelySeparatesIntervalFamily I zStar) :
    False := by
  -- Evaluate orthogonality at the feasible vector `z`.
  have hzKer :
      zStar ∈ LinearMap.ker
        ((dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N)) z) := by
    rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hzStarOrth
    exact hzStarOrth ⟨z, hzL⟩
  have hdot_zero : dotProduct z zStar = 0 := by
    simpa [LinearMap.mem_ker] using hzKer
  -- Positive separation forces the same dot product to be strictly positive.
  have hdot_pos : 0 < dotProduct zStar z := hSep z hzI
  have hdot_zero' : dotProduct zStar z = 0 := by
    simpa [dotProduct, mul_comm] using hdot_zero
  linarith

/-- Helper for Theorem 22.6: the interval box cut out by the coordinate sets `I j` is nonempty
and convex as soon as every `I j` is a nonempty interval. -/
lemma helperForTheorem_22_6_intervalBox_convex_nonempty
    {N : ℕ} (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty) :
    ({z : Fin N → ℝ | ∀ j, z j ∈ I j}).Nonempty ∧
      Convex ℝ {z : Fin N → ℝ | ∀ j, z j ∈ I j} := by
  classical
  constructor
  · -- Choose one coordinate from each nonempty interval to build a point of the box.
    refine ⟨fun j => Classical.choose (hI_nonempty j), ?_⟩
    intro j
    exact Classical.choose_spec (hI_nonempty j)
  · -- Convex combinations stay in the box because each coordinate interval is convex.
    intro x hx y hy a b ha hb hab
    intro j
    exact (hI_interval j).convex (hx j) (hy j) ha hb hab

/-- Helper for Theorem 22.6: a linear subspace of `ℝ^N` is polyhedral once it is reinterpreted
as an affine set. -/
lemma helperForTheorem_22_6_subspaceSet_isPolyhedral
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) :
    IsPolyhedralConvexSet N (L : Set (Fin N → ℝ)) := by
  -- Reinterpret the subspace as an affine set and appeal to the Chapter 20 affine-set lemma.
  exact helperForTheorem_20_2_affineSet_polyhedral
    (n := N) (M := (L : Set (Fin N → ℝ))) (isAffineSet_of_submodule N L)

/-- Helper for Theorem 22.6: if the interval box misses the subspace, one still needs a direct
separator in the orthogonal complement. -/
lemma helperForTheorem_22_6_zero_face_point_not_mem_subspace
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    {c z : Fin N → ℝ}
    (hcOrth : c ∈ dotProductOrthogonalComplement L)
    (hNoPrimal : ¬ ∃ w : Fin N → ℝ, w ∈ L ∧ ∀ j, w j ∈ I j)
    (hzI : ∀ j, z j ∈ I j)
    (hzZero : dotProduct c z = 0) :
    z ∉ L := by
  let _ := hcOrth
  let _ := hzZero
  intro hzL
  -- A point of `L` already lying in the interval box would contradict the infeasibility
  -- hypothesis, regardless of the zero-level equation.
  exact hNoPrimal ⟨z, hzL, hzI⟩

/-- Helper for Theorem 22.6: once every actual point of the zero face is excluded from `L`,
its intrinsic interior is also disjoint from `L`. -/
lemma helperForTheorem_22_6_zeroFace_intrinsicInterior_disjoint_subspace
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    {c : Fin N → ℝ}
    (hcOrth : c ∈ dotProductOrthogonalComplement L)
    (hNoPrimal : ¬ ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j) :
    (L : Set (Fin N → ℝ)) ∩
        intrinsicInterior ℝ
          ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩ {z : Fin N → ℝ | dotProduct c z = 0}) =
      (∅ : Set (Fin N → ℝ)) := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro z hz
  -- Any intrinsic-interior point of the zero face is still an actual zero-face point.
  have hzFace :
      z ∈ ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
          {z : Fin N → ℝ | dotProduct c z = 0}) :=
    intrinsicInterior_subset hz.2
  have hzNotL : z ∉ (L : Set (Fin N → ℝ)) :=
    helperForTheorem_22_6_zero_face_point_not_mem_subspace
      (L := L) (I := I) hcOrth hNoPrimal hzFace.1 hzFace.2
  exact hzNotL hz.1

/-- Helper for Theorem 22.6: the zero-level set of a box-nonnegative functional is a face of
the interval box. -/
lemma helperForTheorem_22_6_zeroLevelFace_is_intervalBoxFace
    {N : ℕ} (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    {c : Fin N → ℝ}
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z) :
    IsFace (𝕜 := ℝ)
      {z : Fin N → ℝ | ∀ j, z j ∈ I j}
      ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩ {z : Fin N → ℝ | dotProduct c z = 0}) := by
  let B : Set (Fin N → ℝ) := {z : Fin N → ℝ | ∀ j, z j ∈ I j}
  have hBoxConvex : Convex ℝ B :=
    (helperForTheorem_22_6_intervalBox_convex_nonempty I hI_interval hI_nonempty).2
  have hBoxLe : B ⊆ closedHalfSpaceLE N (-c) 0 := by
    intro z hzB
    -- Rewriting against `-c` converts box nonnegativity into the half-space condition needed
    -- for the tight-constraint face lemma.
    have hzNonneg : 0 ≤ dotProduct c z := hNonnegOnBox z hzB
    have hzLe : dotProduct z (-c) ≤ 0 := by
      simpa [dotProduct, mul_comm] using (neg_nonpos.mpr hzNonneg)
    simpa [B, closedHalfSpaceLE, dotProduct, mul_comm] using hzLe
  -- The zero-level slice is exactly the tight face cut out by the half-space supporting `B`.
  simpa [B, dotProduct, mul_comm] using
    helperForTheorem_19_1_isFace_of_tightConstraint
      (n := N) (C := B) (b := -c) (β := 0) hBoxLe hBoxConvex

/-- Helper for Theorem 22.6: a nonempty zero face admits an orthogonal direction that is
nonnegative on that face and strictly positive somewhere on it. -/
lemma helperForTheorem_22_6_zeroFace_boundary_separator
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    {c : Fin N → ℝ}
    (hZeroFaceRiEmpty :
      (L : Set (Fin N → ℝ)) ∩
          intrinsicInterior ℝ
            ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
              {z : Fin N → ℝ | dotProduct c z = 0}) =
        (∅ : Set (Fin N → ℝ)))
    (hFne :
      ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
        {z : Fin N → ℝ | dotProduct c z = 0}).Nonempty) :
    ∃ d : Fin N → ℝ,
      d ∈ dotProductOrthogonalComplement L ∧
        (∀ z : Fin N → ℝ,
          z ∈ ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
            {z : Fin N → ℝ | dotProduct c z = 0}) →
          0 ≤ dotProduct d z) ∧
        ∃ z : Fin N → ℝ,
          z ∈ ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
            {z : Fin N → ℝ | dotProduct c z = 0}) ∧
            0 < dotProduct d z := by
  let B : Set (Fin N → ℝ) := {z : Fin N → ℝ | ∀ j, z j ∈ I j}
  let F : Set (Fin N → ℝ) := B ∩ {z : Fin N → ℝ | dotProduct c z = 0}
  have hBconv : Convex ℝ B :=
    (helperForTheorem_22_6_intervalBox_convex_nonempty I hI_interval hI_nonempty).2
  have hFconv : Convex ℝ F := by
    intro x hx y hy a b ha hb hab
    refine ⟨hBconv hx.1 hy.1 ha hb hab, ?_⟩
    -- The zero-level condition is preserved under convex combinations by linearity.
    calc
      dotProduct c (a • x + b • y)
          = a * dotProduct c x + b * dotProduct c y := by
              simp [dotProduct_add, dotProduct_smul, smul_eq_mul, add_comm, add_left_comm,
                add_assoc, mul_comm, mul_left_comm, mul_assoc]
      _ = 0 := by rw [hx.2, hy.2]; ring
  have hLpoly : IsPolyhedralConvexSet N (L : Set (Fin N → ℝ)) :=
    helperForTheorem_22_6_subspaceSet_isPolyhedral L
  have hProperSep :
      ∃ H : Set (Fin N → ℝ),
        HyperplaneSeparatesProperly N H (L : Set (Fin N → ℝ)) F ∧ ¬ F ⊆ H := by
    -- Apply the left-polyhedral/right-convex separator theorem directly to the zero face.
    exact
      (exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
        N (L : Set (Fin N → ℝ)) F ⟨0, L.zero_mem⟩ hFne hFconv hLpoly).2 hZeroFaceRiEmpty
  rcases hProperSep with ⟨H, hHproper, hFnotSubsetH⟩
  rcases hyperplaneSeparatesProperly_oriented N H (L : Set (Fin N → ℝ)) F hHproper with
    ⟨b, β, hb0, hHdef, hLge, hFle, _hnotBoth⟩
  have hOrthB : ∀ x : Fin N → ℝ, x ∈ L → dotProduct x b = 0 := by
    intro x hxL
    by_contra hxb_ne
    let t : ℝ := (β - 1) / dotProduct x b
    have htL : t • x ∈ L := L.smul_mem t hxL
    have htGe : β ≤ dotProduct (t • x) b := hLge (t • x) htL
    have htEval : t * dotProduct x b = β - 1 := by
      simpa [t] using (div_mul_cancel₀ (β - 1) hxb_ne)
    have htDot : dotProduct (t • x) b = β - 1 := by
      calc
        dotProduct (t • x) b = t * dotProduct x b := by
          simp [smul_eq_mul]
        _ = β - 1 := htEval
    have : β ≤ β - 1 := by
      simpa [htDot] using htGe
    linarith
  have hBetaNonpos : β ≤ 0 := by
    simpa using hLge 0 L.zero_mem
  have hOrth : -b ∈ dotProductOrthogonalComplement L := by
    -- The oriented separator annihilates `L`, hence so does its negation.
    rw [dotProductOrthogonalComplement, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker]
    simpa [dotProduct, mul_comm] using congrArg Neg.neg (hOrthB x.1 x.2)
  have hNonnegOnF : ∀ z : Fin N → ℝ, z ∈ F → 0 ≤ dotProduct (-b) z := by
    intro z hzF
    have hzLe : dotProduct z b ≤ β := hFle z hzF
    have hzNonpos : dotProduct z b ≤ 0 := le_trans hzLe hBetaNonpos
    have : 0 ≤ -dotProduct z b := by linarith
    simpa [dotProduct, mul_comm] using this
  have hStrictSome : ∃ z : Fin N → ℝ, z ∈ F ∧ 0 < dotProduct (-b) z := by
    rcases Set.not_subset.mp hFnotSubsetH with ⟨z, hzF, hzNotH⟩
    have hzNe : dotProduct z b ≠ β := by
      intro hzEq
      exact hzNotH (by simpa [hHdef, hzEq])
    have hzLtBeta : dotProduct z b < β := lt_of_le_of_ne (hFle z hzF) hzNe
    have hzLtZero : dotProduct z b < 0 := lt_of_lt_of_le hzLtBeta hBetaNonpos
    have hzPos : 0 < dotProduct (-b) z := by
      have : 0 < -dotProduct z b := by linarith
      simpa [dotProduct, mul_comm] using this
    exact ⟨z, hzF, hzPos⟩
  exact ⟨-b, hOrth, hNonnegOnF, hStrictSome⟩

/-- Helper for Theorem 22.6: a point on the zero face of a box-nonnegative functional is pinned
to the lower endpoint along positive coordinates and to the upper endpoint along negative
coordinates. -/
lemma helperForTheorem_22_6_zeroFace_coordinate_sign_control
    {N : ℕ} (I : Fin N → Set ℝ)
    {c xF : Fin N → ℝ}
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z)
    (hxF : (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0) :
    (∀ j, 0 < c j → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → xF j ≤ z j) ∧
      (∀ j, c j < 0 → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → z j ≤ xF j) ∧
      (∀ j, ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → 0 ≤ c j * (z j - xF j)) := by
  have hPosCoord :
      ∀ j, 0 < c j → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → xF j ≤ z j := by
    intro j hjPos z hzI
    by_contra hlt
    let z' : Fin N → ℝ := Function.update xF j (z j)
    have hz'I : ∀ k, z' k ∈ I k := by
      intro k
      by_cases hk : k = j
      · have hz'k : z' k = z j := by
          simp [z', Function.update, hk]
        rw [hz'k]
        simpa [hk] using hzI j
      · simpa [z', Function.update, hk] using hxF.1 k
    have hz'decomp : z' = xF + Pi.single j (z j - xF j) := by
      ext k
      by_cases hk : k = j
      · simp [z', Function.update, hk, Pi.single, sub_eq_add_neg]
      · simp [z', Function.update, hk, Pi.single, sub_eq_add_neg]
    have hz'nonneg : 0 ≤ dotProduct c z' := hNonnegOnBox z' hz'I
    have hz'eq : dotProduct c z' = c j * (z j - xF j) := by
      calc
        dotProduct c z' = dotProduct c (xF + Pi.single j (z j - xF j)) := by
          rw [hz'decomp]
        _ = dotProduct c xF + c j * (z j - xF j) := by
          rw [dotProduct_add, dotProduct_single]
        _ = c j * (z j - xF j) := by simp [hxF.2]
    have hz'prod_nonneg : 0 ≤ c j * (z j - xF j) := by
      simpa [hz'eq] using hz'nonneg
    have hz'prod_neg : c j * (z j - xF j) < 0 := by
      exact mul_neg_of_pos_of_neg hjPos (sub_neg.mpr (lt_of_not_ge hlt))
    linarith
  have hNegCoord :
      ∀ j, c j < 0 → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → z j ≤ xF j := by
    intro j hjNeg z hzI
    by_contra hgt
    let z' : Fin N → ℝ := Function.update xF j (z j)
    have hz'I : ∀ k, z' k ∈ I k := by
      intro k
      by_cases hk : k = j
      · have hz'k : z' k = z j := by
          simp [z', Function.update, hk]
        rw [hz'k]
        simpa [hk] using hzI j
      · simpa [z', Function.update, hk] using hxF.1 k
    have hz'decomp : z' = xF + Pi.single j (z j - xF j) := by
      ext k
      by_cases hk : k = j
      · simp [z', Function.update, hk, Pi.single, sub_eq_add_neg]
      · simp [z', Function.update, hk, Pi.single, sub_eq_add_neg]
    have hz'nonneg : 0 ≤ dotProduct c z' := hNonnegOnBox z' hz'I
    have hz'eq : dotProduct c z' = c j * (z j - xF j) := by
      calc
        dotProduct c z' = dotProduct c (xF + Pi.single j (z j - xF j)) := by
          rw [hz'decomp]
        _ = dotProduct c xF + c j * (z j - xF j) := by
          rw [dotProduct_add, dotProduct_single]
        _ = c j * (z j - xF j) := by simp [hxF.2]
    have hz'prod_nonneg : 0 ≤ c j * (z j - xF j) := by
      simpa [hz'eq] using hz'nonneg
    have hz'prod_neg : c j * (z j - xF j) < 0 := by
      exact mul_neg_of_neg_of_pos hjNeg (sub_pos.mpr (lt_of_not_ge hgt))
    linarith
  refine ⟨hPosCoord, hNegCoord, ?_⟩
  intro j z hzI
  by_cases hjPos : 0 < c j
  · -- Positive coordinates can only move upward away from a zero-face point.
    exact mul_nonneg (le_of_lt hjPos) (sub_nonneg.mpr (hPosCoord j hjPos z hzI))
  · by_cases hjNeg : c j < 0
    · -- Negative coordinates can only move downward away from a zero-face point.
      exact mul_nonneg_of_nonpos_of_nonpos
        (le_of_lt hjNeg) (sub_nonpos.mpr (hNegCoord j hjNeg z hzI))
    · -- The zero coefficient contributes nothing.
      have hjZero : c j = 0 := by linarith
      simp [hjZero]

/-- Helper for Theorem 22.6: replacing every active coordinate of a box point by the
corresponding coordinate of a zero-face point lands back in the zero face, and the discarded
active-coordinate part has nonnegative `c`-pairing. -/
lemma helperForTheorem_22_6_zeroFace_projection_to_pinnedFace
    {N : ℕ} (I : Fin N → Set ℝ)
    {c xF z : Fin N → ℝ}
    (hNonnegOnBox : ∀ w : Fin N → ℝ, (∀ j, w j ∈ I j) → 0 ≤ dotProduct c w)
    (hxF : (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0)
    (hzI : ∀ j, z j ∈ I j) :
    let π : Fin N → ℝ := fun j => if c j = 0 then z j else xF j
    (∀ j, π j ∈ I j) ∧ dotProduct c π = 0 ∧ 0 ≤ dotProduct c (z - π) := by
  classical
  let π : Fin N → ℝ := fun j => if c j = 0 then z j else xF j
  have hCoordSignControl :
      (∀ j, 0 < c j → ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → xF j ≤ w j) ∧
        (∀ j, c j < 0 → ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → w j ≤ xF j) ∧
        (∀ j, ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → 0 ≤ c j * (w j - xF j)) :=
    helperForTheorem_22_6_zeroFace_coordinate_sign_control
      (I := I) (c := c) (xF := xF) hNonnegOnBox hxF
  refine ⟨?_, ?_, ?_⟩
  · -- The projection only swaps coordinates between two known points of the interval box.
    intro j
    by_cases hj : c j = 0
    · simp [π, hj, hzI j]
    · simp [π, hj, hxF.1 j]
  · -- Zero coordinates keep the old value, while active coordinates are pinned to `xF`.
    calc
      dotProduct c π = ∑ j : Fin N, c j * π j := by
        rfl
      _ = ∑ j : Fin N, c j * xF j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        by_cases hjc : c j = 0
        · simp [π, hjc]
        · simp [π, hjc]
      _ = dotProduct c xF := by
        rfl
      _ = 0 := hxF.2
  · -- Each coordinate contribution to the discarded active part is nonnegative.
    have hTermNonneg :
        ∀ j : Fin N, 0 ≤ c j * ((z - π) j) := by
      intro j
      by_cases hj : c j = 0
      · simp [π, hj]
      · have hzCoord : 0 ≤ c j * (z j - xF j) := hCoordSignControl.2.2 j z hzI
        simpa [π, hj, sub_eq_add_neg] using hzCoord
    calc
      0 ≤ ∑ j : Fin N, c j * ((z - π) j) := by
        exact Finset.sum_nonneg (by intro j hj; exact hTermNonneg j)
      _ = dotProduct c (z - π) := by
        rfl

/-- Helper for Theorem 22.6: pin the active coordinates of `c` to the chosen zero-face point
`xF` and leave the inactive coordinates equal to the original interval family. -/
def helperForTheorem_22_6_zeroFacePinnedIntervalFamily
    {N : ℕ} (I : Fin N → Set ℝ) (c xF : Fin N → ℝ) : Fin N → Set ℝ :=
  fun j => if c j = 0 then I j else {xF j}

/-- Helper for Theorem 22.6: the zero face through `xF` is exactly the interval box obtained by
pinning the active coordinates of `c` to `xF`. -/
lemma helperForTheorem_22_6_zeroFace_asPinnedIntervalBox
    {N : ℕ} (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    {c xF : Fin N → ℝ}
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z)
    (hxF : (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0) :
    let IFace := helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF
    (∀ j, Set.OrdConnected (IFace j)) ∧
      (∀ j, (IFace j).Nonempty) ∧
      ({z : Fin N → ℝ | ∀ j, z j ∈ IFace j} =
        ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
          {z : Fin N → ℝ | dotProduct c z = 0})) := by
  classical
  let IFace := helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF
  have hCoordSignControl :
      (∀ j, 0 < c j → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → xF j ≤ z j) ∧
        (∀ j, c j < 0 → ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → z j ≤ xF j) ∧
        (∀ j, ∀ z : Fin N → ℝ, (∀ k, z k ∈ I k) → 0 ≤ c j * (z j - xF j)) :=
    helperForTheorem_22_6_zeroFace_coordinate_sign_control
      (I := I) (c := c) (xF := xF) hNonnegOnBox hxF
  refine ⟨?_, ?_, ?_⟩
  · intro j
    -- The pinned family is either the original interval or a singleton coordinate slice.
    by_cases hj : c j = 0
    · simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hI_interval j
    · simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using
        (Set.ordConnected_singleton : Set.OrdConnected ({xF j} : Set ℝ))
  · intro j
    -- Nonemptiness comes from either the original interval or the pinned face point itself.
    by_cases hj : c j = 0
    · exact ⟨xF j, by simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hxF.1 j⟩
    · exact ⟨xF j, by simp [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj]⟩
  · -- Compare the pinned box with the literal zero face in both directions.
    ext z
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : c j = 0
        · simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hz j
        · have hzj : z j = xF j := by
            simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hz j
          rw [hzj]
          exact hxF.1 j
      · calc
          dotProduct c z = ∑ j : Fin N, c j * z j := by
            rfl
          _ = ∑ j : Fin N, c j * xF j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hjc : c j = 0
            · simp [hjc]
            · have hzj : z j = xF j := by
                simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hjc] using hz j
              simp [hzj]
          _ = dotProduct c xF := by
            rfl
          _ = 0 := hxF.2
    · rintro ⟨hzI, hzZero⟩
      intro j
      by_cases hj : c j = 0
      · simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hzI j
      · have hTermsNonneg :
          ∀ k : Fin N, 0 ≤ c k * (z k - xF k) := by
            intro k
            exact hCoordSignControl.2.2 k z hzI
        have hSumZero :
            ∑ k : Fin N, c k * (z k - xF k) = 0 := by
          have hDiffZero : dotProduct c (z - xF) = 0 := by
            have hzZeroEq : dotProduct c z = 0 := hzZero
            calc
              dotProduct c (z - xF) = dotProduct c z - dotProduct c xF := by
                simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
              _ = 0 := by simp [hzZeroEq, hxF.2]
          simpa [dotProduct] using hDiffZero
        have hAllZero :
            ∀ k ∈ Finset.univ, c k * (z k - xF k) = 0 := by
          exact
            (Finset.sum_eq_zero_iff_of_nonneg
              (s := Finset.univ)
              (f := fun k : Fin N => c k * (z k - xF k))
              (by intro k hk; exact hTermsNonneg k)).1 hSumZero
        have hTermZero : c j * (z j - xF j) = 0 := hAllZero j (by simp)
        have hzj : z j = xF j := by
          have hDiffZero : z j - xF j = 0 := by
            exact (mul_eq_zero.mp hTermZero).resolve_left hj
          linarith
        simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj, hzj]

/-- Helper for Theorem 22.6: if a weak separator is strictly positive somewhere on the box,
then some active coordinate was not already forced to a singleton interval. -/
lemma helperForTheorem_22_6_zeroFace_has_active_nonSubsingleton_coordinate
    {N : ℕ} (I : Fin N → Set ℝ)
    {c xF : Fin N → ℝ}
    (hxF : (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0)
    (hStrictSome : ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ 0 < dotProduct c z) :
    ∃ j : Fin N, c j ≠ 0 ∧ ¬ Set.Subsingleton (I j) := by
  rcases hStrictSome with ⟨z, hzI, hzPos⟩
  by_contra hNoCoord
  have hPinnedActive :
      ∀ j : Fin N, c j ≠ 0 → z j = xF j := by
    intro j hj
    by_contra hzjxF
    have hNotSub : ¬ Set.Subsingleton (I j) := by
      intro hSub
      exact hzjxF (hSub (hzI j) (hxF.1 j))
    exact hNoCoord ⟨j, hj, hNotSub⟩
  have hDotEq :
      dotProduct c z = dotProduct c xF := by
    calc
      dotProduct c z = ∑ j : Fin N, c j * z j := by
        rfl
      _ = ∑ j : Fin N, c j * xF j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        by_cases hjc : c j = 0
        · simp [hjc]
        · simp [hPinnedActive j hjc]
      _ = dotProduct c xF := by
        rfl
  have : 0 < dotProduct c xF := by simpa [hDotEq] using hzPos
  linarith [hxF.2]

/-- Helper for Theorem 22.6: count the coordinates whose interval is not already forced to a
singleton. -/
noncomputable def helperForTheorem_22_6_freeCoordCount {N : ℕ} (I : Fin N → Set ℝ) : ℕ :=
  (@Finset.filter (Fin N) (fun j => ¬ Set.Subsingleton (I j)) (Classical.decPred _)
    Finset.univ).card

/-- Helper for Theorem 22.6: pinning an active coordinate to the zero-face point strictly lowers
the number of non-singleton coordinates. -/
lemma helperForTheorem_22_6_pinnedIntervalFamily_freeCoordCount_lt
    {N : ℕ} (I : Fin N → Set ℝ) {c xF : Fin N → ℝ}
    {j : Fin N} (hjc : c j ≠ 0) (hjfree : ¬ Set.Subsingleton (I j)) :
    helperForTheorem_22_6_freeCoordCount
        (helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF) <
      helperForTheorem_22_6_freeCoordCount I := by
  classical
  let IFace := helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF
  let s : Finset (Fin N) := Finset.univ.filter fun k => ¬ Set.Subsingleton (I k)
  let sFace : Finset (Fin N) := Finset.univ.filter fun k => ¬ Set.Subsingleton (IFace k)
  have hsFace_subset : sFace ⊆ s := by
    intro k hk
    have hkFace : ¬ Set.Subsingleton (IFace k) := (Finset.mem_filter.mp hk).2
    by_cases hkc : c k = 0
    · have hkI : ¬ Set.Subsingleton (I k) := by
        simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hkc] using hkFace
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkI⟩
    · have hkSingleton : Set.Subsingleton (IFace k) := by
        simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hkc] using
          (Set.subsingleton_singleton : Set.Subsingleton ({xF k} : Set ℝ))
      exact (hkFace hkSingleton).elim
  have hj_mem_s : j ∈ s := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjfree⟩
  have hj_not_mem_sFace : j ∉ sFace := by
    have hjSingleton : Set.Subsingleton (IFace j) := by
      simpa [IFace, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hjc] using
        (Set.subsingleton_singleton : Set.Subsingleton ({xF j} : Set ℝ))
    intro hjMem
    exact (Finset.mem_filter.mp hjMem).2 hjSingleton
  have hsFace_ssubset : sFace ⊂ s := by
    refine ⟨hsFace_subset, ?_⟩
    intro hsSubset
    exact hj_not_mem_sFace (hsSubset hj_mem_s)
  simpa [helperForTheorem_22_6_freeCoordCount, IFace, s, sFace] using
    Finset.card_lt_card hsFace_ssubset

/-- Helper for Theorem 22.6: if a box-nonnegative separator never vanishes on the box, then it
is already strictly positive on every box point. -/
lemma helperForTheorem_22_6_weakSeparator_without_zeroFace_is_strict
    {N : ℕ} (I : Fin N → Set ℝ) {c : Fin N → ℝ}
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z)
    (hNoZeroFace : ¬ ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ dotProduct c z = 0) :
    PositivelySeparatesIntervalFamily I c := by
  intro z hzI
  -- Nonnegativity is given; the only excluded case is equality to zero on the box.
  have hNonneg : 0 ≤ dotProduct c z := hNonnegOnBox z hzI
  have hNe : dotProduct c z ≠ 0 := by
    intro hzZero
    exact hNoZeroFace ⟨z, hzI, hzZero⟩
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Helper for Theorem 22.6: a strict separator on the pinned zero face can be perturbed back to
the original box by keeping the active coefficients of `c` dominant. -/
lemma helperForTheorem_22_6_smallPerturbation_from_pinnedFaceStrictSeparator
    {N : ℕ} (I : Fin N → Set ℝ)
    {c xF d : Fin N → ℝ}
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z)
    (hxF : (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0)
    (hSepFace :
      PositivelySeparatesIntervalFamily
        (helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF) d) :
    ∃ ε : ℝ, 0 < ε ∧ PositivelySeparatesIntervalFamily I (c + ε • d) := by
  classical
  -- Route correction: a compactness argument is unnecessary here; a finite coordinatewise ratio
  -- bound already controls the active deviation from the pinned face.
  let R : ℝ := ∑ j : Fin N, |if c j = 0 then 0 else d j / c j|
  have hRnonneg : 0 ≤ R := by
    -- Every summand is an absolute value, so the whole finite sum is nonnegative.
    exact Finset.sum_nonneg (by
      intro j hj
      exact abs_nonneg _)
  let ε : ℝ := (R + 1)⁻¹
  have hεpos : 0 < ε := by
    -- The denominator is strictly positive because `R ≥ 0`.
    exact inv_pos.mpr (by linarith [hRnonneg])
  refine ⟨ε, hεpos, ?_⟩
  intro z hzI
  let π : Fin N → ℝ := fun j => if c j = 0 then z j else xF j
  have hProj :
      (∀ j, π j ∈ I j) ∧ dotProduct c π = 0 ∧ 0 ≤ dotProduct c (z - π) :=
    helperForTheorem_22_6_zeroFace_projection_to_pinnedFace
      (I := I) (c := c) (xF := xF) (z := z) hNonnegOnBox hxF hzI
  have hπI : ∀ j, π j ∈ I j := hProj.1
  have hπZero : dotProduct c π = 0 := hProj.2.1
  have hDiffCoordNonneg : ∀ j : Fin N, 0 ≤ c j * ((z - π) j) := by
    intro j
    by_cases hj : c j = 0
    · -- Inactive coordinates are unchanged by the projection, so their contribution vanishes.
      simp [π, hj]
    · -- Active coordinates keep the same sign pattern as `c` by the zero-face pinning lemma.
      have hCoord :
          (∀ j, 0 < c j → ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → xF j ≤ w j) ∧
            (∀ j, c j < 0 → ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → w j ≤ xF j) ∧
            (∀ j, ∀ w : Fin N → ℝ, (∀ k, w k ∈ I k) → 0 ≤ c j * (w j - xF j)) :=
        helperForTheorem_22_6_zeroFace_coordinate_sign_control
          (I := I) (c := c) (xF := xF) hNonnegOnBox hxF
      simpa [π, hj, sub_eq_add_neg] using hCoord.2.2 j z hzI
  have hDiffLowerBound :
      -R * dotProduct c (z - π) ≤ dotProduct d (z - π) := by
    have hTermBound :
        ∀ j : Fin N, -R * (c j * ((z - π) j)) ≤ d j * ((z - π) j) := by
      intro j
      by_cases hj : c j = 0
      · -- Zero coordinates contribute nothing to either side.
        simp [π, hj]
      · have hAbsLe :
          |d j / c j| ≤ R := by
          have hSingle :
              |if c j = 0 then 0 else d j / c j| ≤
                ∑ k : Fin N, |if c k = 0 then 0 else d k / c k| := by
            simpa [R] using
              (Finset.single_le_sum
                (fun k hk => abs_nonneg (if c k = 0 then 0 else d k / c k))
                (by simp : j ∈ (Finset.univ : Finset (Fin N))))
          simpa [hj, R] using hSingle
        have hRatioLe : -(d j / c j) ≤ R := by
          exact le_trans (neg_le_abs (d j / c j)) hAbsLe
        have hMulLe :
            (-(d j / c j)) * (c j * ((z - π) j)) ≤
              R * (c j * ((z - π) j)) := by
          exact mul_le_mul_of_nonneg_right hRatioLe (hDiffCoordNonneg j)
        have hCancel :
            (-(d j / c j)) * (c j * ((z - π) j)) = -(d j * ((z - π) j)) := by
          field_simp [hj]
        have hTarget :
            -(d j * ((z - π) j)) ≤ R * (c j * ((z - π) j)) := by
          rw [← hCancel]
          exact hMulLe
        linarith
    have hSumLe :
        ∑ j : Fin N, (-R * (c j * ((z - π) j))) ≤
          ∑ j : Fin N, d j * ((z - π) j) := by
      exact Finset.sum_le_sum (by
        intro j hj
        exact hTermBound j)
    have hLeft :
        ∑ j : Fin N, (-R * (c j * ((z - π) j))) = -R * dotProduct c (z - π) := by
      rw [dotProduct, ← Finset.mul_sum]
    have hRight :
        ∑ j : Fin N, d j * ((z - π) j) = dotProduct d (z - π) := by
      rfl
    rw [hLeft, hRight] at hSumLe
    simpa using hSumLe
  have hπFace :
      ∀ j, π j ∈ helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF j := by
    intro j
    by_cases hj : c j = 0
    · simpa [π, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj] using hzI j
    · simp [π, helperForTheorem_22_6_zeroFacePinnedIntervalFamily, hj]
  have hπPos : 0 < dotProduct d π := hSepFace π hπFace
  have hCoeffNonneg : 0 ≤ 1 - ε * R := by
    have hEq : 1 - ε * R = ε := by
      have hDenom : R + 1 ≠ 0 := by linarith [hRnonneg]
      calc
        1 - ε * R = 1 - (R + 1)⁻¹ * R := by rfl
        _ = (R + 1)⁻¹ := by
          field_simp [hDenom]
          ring
    simpa [hEq] using le_of_lt hεpos
  have hExpand :
      dotProduct (c + ε • d) z =
        dotProduct c (z - π) + ε * dotProduct d (z - π) + ε * dotProduct d π := by
    -- Split `z` into the pinned face point plus its active deviation.
    have hzDecomp : z = (z - π) + π := by
      ext j
      simp [sub_eq_add_neg]
    have hSplit :
        dotProduct (c + ε • d) z =
          dotProduct (c + ε • d) (z - π) + dotProduct (c + ε • d) π := by
      have hArg :
          dotProduct (c + ε • d) z =
            dotProduct (c + ε • d) ((z - π) + π) := by
        exact congrArg (fun w => dotProduct (c + ε • d) w) hzDecomp
      calc
        dotProduct (c + ε • d) z = dotProduct (c + ε • d) ((z - π) + π) := hArg
        _ = dotProduct (c + ε • d) (z - π) + dotProduct (c + ε • d) π := by
          rw [dotProduct_add]
    calc
      dotProduct (c + ε • d) z
          = dotProduct (c + ε • d) (z - π) + dotProduct (c + ε • d) π := hSplit
      _ = (dotProduct c (z - π) + dotProduct (ε • d) (z - π)) +
            (dotProduct c π + dotProduct (ε • d) π) := by
            rw [add_dotProduct, add_dotProduct]
      _ = dotProduct c (z - π) + ε • (dotProduct d (z - π)) + ε • (dotProduct d π) := by
            rw [smul_dotProduct, smul_dotProduct, hπZero]
            ring
      _ = dotProduct c (z - π) + ε * dotProduct d (z - π) + ε * dotProduct d π := by
            simp [smul_eq_mul]
  have hNonnegPart :
      0 ≤ dotProduct c (z - π) + ε * dotProduct d (z - π) := by
    have hMain :
        0 ≤ (1 - ε * R) * dotProduct c (z - π) := by
      exact mul_nonneg hCoeffNonneg hProj.2.2
    have hLower :
        (1 - ε * R) * dotProduct c (z - π) ≤
          dotProduct c (z - π) + ε * dotProduct d (z - π) := by
      have hScaled := mul_le_mul_of_nonneg_left hDiffLowerBound (le_of_lt hεpos)
      linarith
    exact le_trans hMain hLower
  -- The dominant `c`-part is nonnegative, while `d` is strictly positive on the pinned face.
  rw [hExpand]
  linarith [hNonnegPart, mul_pos hεpos hπPos]

/-- Helper for Theorem 22.6: recurse on the number of non-singleton coordinates to upgrade a
weak interval-box separator to a strict one. -/
lemma helperForTheorem_22_6_intervalBox_nonnegative_separator_upgrade_aux
    {N : ℕ} (n : ℕ) :
    ∀ (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ),
      helperForTheorem_22_6_freeCoordCount I ≤ n →
      (∀ j, Set.OrdConnected (I j)) →
      (∀ j, (I j).Nonempty) →
      ∀ {c : Fin N → ℝ},
        c ∈ dotProductOrthogonalComplement L →
        (¬ ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j) →
        (∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z) →
        (∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ 0 < dotProduct c z) →
        ∃ c' : Fin N → ℝ,
          c' ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I c' := by
  induction' n with n ih
  · intro L I hCount hI_interval hI_nonempty c hcOrth hNoPrimal hNonnegOnBox hStrictSome
    by_cases hNoZeroFace : ¬ ∃ xF : Fin N → ℝ, (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0
    · -- If the weak separator never vanishes on the box, it is already strict.
      exact ⟨c, hcOrth,
        helperForTheorem_22_6_weakSeparator_without_zeroFace_is_strict
          (I := I) hNonnegOnBox hNoZeroFace⟩
    · exfalso
      rcases not_not.mp hNoZeroFace with ⟨xF, hxFI, hxFZero⟩
      have hActive :
          ∃ j : Fin N, c j ≠ 0 ∧ ¬ Set.Subsingleton (I j) := by
        exact helperForTheorem_22_6_zeroFace_has_active_nonSubsingleton_coordinate
          (I := I) (c := c) (xF := xF) ⟨hxFI, hxFZero⟩ hStrictSome
      rcases hActive with ⟨j, hjc, hjfree⟩
      have hCountLt :
          helperForTheorem_22_6_freeCoordCount
              (helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF) <
            helperForTheorem_22_6_freeCoordCount I :=
        helperForTheorem_22_6_pinnedIntervalFamily_freeCoordCount_lt
          (I := I) (c := c) (xF := xF) hjc hjfree
      have hCountFaceLe :
          helperForTheorem_22_6_freeCoordCount
              (helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF) < 0 := by
        exact lt_of_lt_of_le hCountLt hCount
      exact (Nat.not_lt_zero _ hCountFaceLe).elim
  · intro L I hCount hI_interval hI_nonempty c hcOrth hNoPrimal hNonnegOnBox hStrictSome
    by_cases hNoZeroFace : ¬ ∃ xF : Fin N → ℝ, (∀ j, xF j ∈ I j) ∧ dotProduct c xF = 0
    · -- Once the zero face is empty, the current weak separator is already strictly positive.
      exact ⟨c, hcOrth,
        helperForTheorem_22_6_weakSeparator_without_zeroFace_is_strict
          (I := I) hNonnegOnBox hNoZeroFace⟩
    · rcases not_not.mp hNoZeroFace with ⟨xF, hxFI, hxFZero⟩
      let IFace := helperForTheorem_22_6_zeroFacePinnedIntervalFamily I c xF
      have hFaceEqData :
          (∀ j, Set.OrdConnected (IFace j)) ∧
            (∀ j, (IFace j).Nonempty) ∧
            ({z : Fin N → ℝ | ∀ j, z j ∈ IFace j} =
              ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
                {z : Fin N → ℝ | dotProduct c z = 0})) :=
        helperForTheorem_22_6_zeroFace_asPinnedIntervalBox
          (I := I) (c := c) (xF := xF) hI_interval hNonnegOnBox ⟨hxFI, hxFZero⟩
      have hZeroFaceRiEmpty :
          (L : Set (Fin N → ℝ)) ∩
              intrinsicInterior ℝ
                ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
                  {z : Fin N → ℝ | dotProduct c z = 0}) =
            (∅ : Set (Fin N → ℝ)) :=
        helperForTheorem_22_6_zeroFace_intrinsicInterior_disjoint_subspace
          (L := L) (I := I) (c := c) hcOrth hNoPrimal
      have hZeroFaceNonempty :
          ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
            {z : Fin N → ℝ | dotProduct c z = 0}).Nonempty := by
        exact ⟨xF, hxFI, hxFZero⟩
      rcases helperForTheorem_22_6_zeroFace_boundary_separator
          (L := L) (I := I) (c := c) hI_interval hI_nonempty
          hZeroFaceRiEmpty hZeroFaceNonempty with
        ⟨d, hdOrth, hNonnegFace, hStrictSomeFace⟩
      have hIFace_interval : ∀ j, Set.OrdConnected (IFace j) := hFaceEqData.1
      have hIFace_nonempty : ∀ j, (IFace j).Nonempty := hFaceEqData.2.1
      have hFaceEq :
          {z : Fin N → ℝ | ∀ j, z j ∈ IFace j} =
            ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
              {z : Fin N → ℝ | dotProduct c z = 0}) := hFaceEqData.2.2
      have hNoPrimalFace : ¬ ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ IFace j := by
        intro hFacePoint
        rcases hFacePoint with ⟨z, hzL, hzIFace⟩
        have hzFace : z ∈ ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
            {z : Fin N → ℝ | dotProduct c z = 0}) := by
          rw [← hFaceEq]
          exact hzIFace
        exact hNoPrimal ⟨z, hzL, hzFace.1⟩
      have hNonnegOnIFace :
          ∀ z : Fin N → ℝ, (∀ j, z j ∈ IFace j) → 0 ≤ dotProduct d z := by
        intro z hzIFace
        have hzFace : z ∈ ({z : Fin N → ℝ | ∀ j, z j ∈ I j} ∩
            {z : Fin N → ℝ | dotProduct c z = 0}) := by
          rw [← hFaceEq]
          exact hzIFace
        exact hNonnegFace z hzFace
      have hStrictSomeIFace :
          ∃ z : Fin N → ℝ, (∀ j, z j ∈ IFace j) ∧ 0 < dotProduct d z := by
        rcases hStrictSomeFace with ⟨z, hzFace, hzPos⟩
        have hzIFace : z ∈ {z : Fin N → ℝ | ∀ j, z j ∈ IFace j} := by
          rw [hFaceEq]
          exact hzFace
        exact ⟨z, hzIFace, hzPos⟩
      have hActive :
          ∃ j : Fin N, c j ≠ 0 ∧ ¬ Set.Subsingleton (I j) := by
        exact helperForTheorem_22_6_zeroFace_has_active_nonSubsingleton_coordinate
          (I := I) (c := c) (xF := xF) ⟨hxFI, hxFZero⟩ hStrictSome
      rcases hActive with ⟨j, hjc, hjfree⟩
      have hCountFaceLt :
          helperForTheorem_22_6_freeCoordCount IFace <
            helperForTheorem_22_6_freeCoordCount I := by
        simpa [IFace] using
          helperForTheorem_22_6_pinnedIntervalFamily_freeCoordCount_lt
            (I := I) (c := c) (xF := xF) hjc hjfree
      have hCountFaceLe :
          helperForTheorem_22_6_freeCoordCount IFace ≤ n := by
        exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hCountFaceLt hCount)
      rcases ih L IFace hCountFaceLe hIFace_interval hIFace_nonempty hdOrth
          hNoPrimalFace hNonnegOnIFace hStrictSomeIFace with
        ⟨d', hd'Orth, hd'Pos⟩
      rcases helperForTheorem_22_6_smallPerturbation_from_pinnedFaceStrictSeparator
          (I := I) (c := c) (xF := xF) (d := d')
          hNonnegOnBox ⟨hxFI, hxFZero⟩ hd'Pos with
        ⟨ε, hεpos, hPos⟩
      -- The perturbed separator stays in the orthogonal complement because that space is a
      -- submodule closed under addition and scalar multiplication.
      refine ⟨c + ε • d', ?_, hPos⟩
      exact (dotProductOrthogonalComplement L).add_mem hcOrth
        ((dotProductOrthogonalComplement L).smul_mem ε hd'Orth)

/-- Helper for Theorem 22.6: if the interval box misses the subspace, one still needs a direct
separator in the orthogonal complement. -/
lemma helperForTheorem_22_6_intervalBox_nonnegative_separator_upgrade
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    {c : Fin N → ℝ}
    (hcOrth : c ∈ dotProductOrthogonalComplement L)
    (hNoPrimal : ¬ ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j)
    (hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct c z)
    (hStrictSome : ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ 0 < dotProduct c z) :
    ∃ c' : Fin N → ℝ,
      c' ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I c' := by
  -- Route correction: the public upgrade theorem is now just the outer wrapper around the
  -- finite-descent auxiliary on pinned zero faces.
  exact
    helperForTheorem_22_6_intervalBox_nonnegative_separator_upgrade_aux
      (n := helperForTheorem_22_6_freeCoordCount I)
      L I (le_rfl : helperForTheorem_22_6_freeCoordCount I ≤ helperForTheorem_22_6_freeCoordCount I)
      hI_interval hI_nonempty hcOrth hNoPrimal hNonnegOnBox hStrictSome

/-- Helper for Theorem 22.6: if the interval box misses the subspace, one still needs a direct
separator in the orthogonal complement. -/
lemma helperForTheorem_22_6_infeasible_interval_box_yields_orthogonal_separator
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty)
    (hNoPrimal : ¬ ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j) :
    ∃ zStar : Fin N → ℝ,
      zStar ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I zStar := by
  let B : Set (Fin N → ℝ) := {z : Fin N → ℝ | ∀ j, z j ∈ I j}
  -- Route correction: the orthogonal-complement bookkeeping is now isolated in dedicated helpers,
  -- so the remaining gap is now the upgrade from a proper hyperplane separator of the box to a
  -- separator that is strictly positive on every point of the box.
  have hBox :
      B.Nonempty ∧ Convex ℝ B :=
    helperForTheorem_22_6_intervalBox_convex_nonempty I hI_interval hI_nonempty
  have hLpoly : IsPolyhedralConvexSet N (L : Set (Fin N → ℝ)) :=
    helperForTheorem_22_6_subspaceSet_isPolyhedral L
  have hInterEmpty : (L : Set (Fin N → ℝ)) ∩ intrinsicInterior ℝ B = (∅ : Set (Fin N → ℝ)) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro z hz
    exact hNoPrimal ⟨z, hz.1, intrinsicInterior_subset hz.2⟩
  have hProperSep :
      ∃ H : Set (Fin N → ℝ),
        HyperplaneSeparatesProperly N H (L : Set (Fin N → ℝ)) B ∧ ¬ B ⊆ H := by
    exact
      (exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
        N (L : Set (Fin N → ℝ)) B ⟨0, L.zero_mem⟩ hBox.1 hBox.2 hLpoly).2 hInterEmpty
  rcases hProperSep with ⟨H, hHproper, hBnotSubsetH⟩
  rcases hyperplaneSeparatesProperly_oriented N H (L : Set (Fin N → ℝ)) B hHproper with
    ⟨b, β, hb0, hHdef, hLge, hBle, _hnotBoth⟩
  have hBetaNonpos : β ≤ 0 := by
    simpa using hLge 0 L.zero_mem
  have hOrthB : ∀ x : Fin N → ℝ, x ∈ L → dotProduct x b = 0 := by
    intro x hxL
    by_contra hxb_ne
    let t : ℝ := (β - 1) / dotProduct x b
    have htL : t • x ∈ L := L.smul_mem t hxL
    have htGe : β ≤ dotProduct (t • x) b := hLge (t • x) htL
    have htEval : t * dotProduct x b = β - 1 := by
      simpa [t] using (div_mul_cancel₀ (β - 1) hxb_ne)
    have htDot : dotProduct (t • x) b = β - 1 := by
      calc
        dotProduct (t • x) b = t * dotProduct x b := by
          simp [smul_eq_mul]
        _ = β - 1 := htEval
    have : β ≤ β - 1 := by
      simpa [htDot] using htGe
    linarith
  have hOrth : b ∈ dotProductOrthogonalComplement L := by
    rw [dotProductOrthogonalComplement, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker]
    exact hOrthB x.1 x.2
  have hNonnegOnBox : ∀ z : Fin N → ℝ, (∀ j, z j ∈ I j) → 0 ≤ dotProduct (-b) z := by
    intro z hzI
    have hzBle : dotProduct z b ≤ β := hBle z hzI
    have hzNonpos : dotProduct z b ≤ 0 := le_trans hzBle hBetaNonpos
    have : 0 ≤ -dotProduct z b := by linarith
    simpa [dotProduct, mul_comm] using this
  have hStrictSome : ∃ z : Fin N → ℝ, (∀ j, z j ∈ I j) ∧ 0 < dotProduct (-b) z := by
    rcases Set.not_subset.mp hBnotSubsetH with ⟨z, hzB, hzNotH⟩
    have hzNe : dotProduct z b ≠ β := by
      intro hzEq
      exact hzNotH (by simpa [hHdef, hzEq])
    have hzLtBeta : dotProduct z b < β := lt_of_le_of_ne (hBle z hzB) hzNe
    have hzLtZero : dotProduct z b < 0 := lt_of_lt_of_le hzLtBeta hBetaNonpos
    have hzPos : 0 < dotProduct (-b) z := by
      have : 0 < -dotProduct z b := by linarith
      simpa [dotProduct, mul_comm] using this
    exact ⟨z, hzB, hzPos⟩
  have hNegOrth : -b ∈ dotProductOrthogonalComplement L := by
    -- Negating an orthogonal direction stays inside the orthogonal-complement submodule.
    exact (dotProductOrthogonalComplement L).neg_mem hOrth
  -- The remaining work has been isolated into a dedicated upgrade lemma for weak box separators.
  exact helperForTheorem_22_6_intervalBox_nonnegative_separator_upgrade
    (L := L) (I := I) (c := -b) hI_interval hI_nonempty hNegOrth hNoPrimal
    hNonnegOnBox hStrictSome


end Section22
end Chap04
