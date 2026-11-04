/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_last_coordinate_lifting

open scoped BigOperators Matrix

section Proposition72

variable {n : ℕ}

/-- Specializing the Chapter 5 owner `zero_one_points` to `Set.univ` recovers the binary vectors
in `ℝ^n`. -/
theorem mem_zero_one_points_univ_iff {x : Fin n → ℝ} :
    x ∈ zero_one_points (Nat.le_refl n) Set.univ ↔
      ∀ i : Fin n, x i = 0 ∨ x i = 1 := by
  simp [mem_zero_one_points_iff]

/-- Helper for Proposition 7.2: the ambient binary set `zero_one_points (Nat.le_refl (n + 1))
Set.univ` is finite. -/
private lemma zeroOnePointsUniv_finite :
    Set.Finite
      (zero_one_points
        (Nat.le_refl (n + 1))
        (Set.univ : Set (Fin (n + 1) → ℝ))) := by
  let binaryBox : Set (Fin (n + 1) → ℝ) :=
    {x | ∀ i : Fin (n + 1), x i ∈ ({(0 : ℝ), 1} : Set ℝ)}
  have hbinaryBoxFinite : binaryBox.Finite := by
    -- Enumerate the two coordinate choices independently.
    simpa [binaryBox, Set.pi] using
      (Set.Finite.pi' (t := fun _ : Fin (n + 1) ↦ ({(0 : ℝ), 1} : Set ℝ))
        fun _ ↦ by simp)
  -- Rephrase `zero_one_points` as the coordinatewise `{0, 1}` box.
  refine hbinaryBoxFinite.subset ?_
  intro x hx
  rw [mem_zero_one_points_univ_iff] at hx
  intro i
  specialize hx i
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx

/-- Helper for Proposition 7.2: the partial objective attains its maximum on the nonempty
`x_last = 1` slice of a binary set. -/
private lemma lastCoordinateSliceValues_isGreatest
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1)) :
    IsGreatest
      (last_coordinate_slice_values S α 1)
      (sSup (last_coordinate_slice_values S α 1)) := by
  have hSfinite : S.Finite := zeroOnePointsUniv_finite.subset hS_binary
  have honeSliceFinite : (S ∩ last_coordinate_eq_set n 1).Finite := by
    -- The relevant slice is a subset of the finite binary set `S`.
    refine hSfinite.subset ?_
    intro x hx
    exact hx.1
  have hvaluesFinite : (last_coordinate_slice_values S α 1).Finite := by
    -- The slice-value set is the image of the finite slice under the partial objective.
    simpa [last_coordinate_slice_values] using honeSliceFinite.image (partial_lifting_value α)
  have hvaluesNonempty : (last_coordinate_slice_values S α 1).Nonempty := by
    rcases hone_slice_nonempty with ⟨x, hx⟩
    refine ⟨partial_lifting_value α x, ?_⟩
    exact mem_last_coordinate_slice_values_iff.mpr
      ⟨x, hx.1, mem_last_coordinate_eq_set_iff.mp hx.2, rfl⟩
  -- Finite nonempty subsets of `ℝ` contain their supremum.
  refine ⟨hvaluesNonempty.csSup_mem hvaluesFinite, ?_⟩
  intro t ht
  exact le_csSup hvaluesFinite.bddAbove ht

/-- Helper for Proposition 7.2: the maximizing `x_last = 1` slice point yields equality in the
lifted inequality. -/
private lemma existsTightPointOnOneSlice
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1)) :
    ∃ x : Fin (n + 1) → ℝ,
      x ∈ S ∧
        x (Fin.last n) = 1 ∧
          Fin.snoc α (last_coordinate_lifting_coefficient S α β) ⬝ᵥ x = β := by
  have hGreatest := lastCoordinateSliceValues_isGreatest S α hS_binary hone_slice_nonempty
  rcases mem_last_coordinate_slice_values_iff.mp hGreatest.1 with ⟨x, hxS, hxlast, hxvalue⟩
  refine ⟨x, hxS, hxlast, ?_⟩
  -- Substituting the maximizing slice value into the lifting formula makes the inequality tight.
  calc
    Fin.snoc α (last_coordinate_lifting_coefficient S α β) ⬝ᵥ x
        = partial_lifting_value α x +
            last_coordinate_lifting_coefficient S α β * x (Fin.last n) := by
            rw [dotProduct_last_coordinate_lifting_coeffs]
    _ = sSup (last_coordinate_slice_values S α 1) +
          (β - sSup (last_coordinate_slice_values S α 1)) * 1 := by
          rw [hxvalue, last_coordinate_lifting_coefficient_eq, hxlast]
    _ = β := by ring

/-- Helper for Proposition 7.2: affine combinations of points with last coordinate `0` still have
last coordinate `0`. -/
private lemma affineSpan_subset_lastCoordinateEqZero
    (T : Set (Fin (n + 1) → ℝ))
    (hT : T ⊆ last_coordinate_eq_set n 0) :
    (affineSpan ℝ T : Set (Fin (n + 1) → ℝ)) ⊆ last_coordinate_eq_set n 0 := by
  have hhyperplane :
      T ⊆ {x : Fin (n + 1) → ℝ | Pi.single (Fin.last n) (1 : ℝ) ⬝ᵥ x = 0} := by
    intro x hxT
    have hxlast : x (Fin.last n) = 0 := mem_last_coordinate_eq_set_iff.mp (hT hxT)
    simp [dotProduct, Pi.single_apply, hxlast]
  have hAff :=
    affineSpan_subset_hyperplane_of_subset
      (S := T)
      (c := Pi.single (Fin.last n) (1 : ℝ))
      (δ := 0)
      hhyperplane
  intro x hx
  rw [mem_last_coordinate_eq_set_iff]
  simpa [dotProduct, Pi.single_apply] using hAff hx

/-- Maximality statement from Proposition 7.2 (1). Let `S ⊆ {0,1}^(n+1)` and assume the inequality
`∑_{i < n} αᵢ xᵢ ≤ β` is valid on the slice `S ∩ {x_last = 0}` and that the slice
`S ∩ {x_last = 1}` is nonempty. Then the coefficient
`β - max {∑_{i < n} αᵢ xᵢ | x ∈ S, x_last = 1}` is the greatest last-coordinate coefficient for
which the lifted inequality is valid on `S`. -/
theorem binary_last_coordinate_lifting_maximal
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hvalid_zero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set n 0)
        (Fin.snoc α 0)
        β)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1)) :
    IsGreatest
      (valid_last_coordinate_lifting_coefficients S α β)
      (last_coordinate_lifting_coefficient S α β) := by
  have hGreatest :=
    lastCoordinateSliceValues_isGreatest S α hS_binary hone_slice_nonempty
  refine ⟨?_, ?_⟩
  · -- First show that the canonical coefficient yields a valid lifted inequality on all of `S`.
    rw [mem_valid_last_coordinate_lifting_coefficients_iff]
    intro x hxS
    have hxlast_binary :
        x (Fin.last n) = 0 ∨ x (Fin.last n) = 1 :=
      (mem_zero_one_points_univ_iff.mp (hS_binary hxS)) (Fin.last n)
    rcases hxlast_binary with hxlast0 | hxlast1
    · have hzero_valid :
          Fin.snoc α 0 ⬝ᵥ x ≤ β := by
        exact hvalid_zero ⟨hxS, mem_last_coordinate_eq_set_iff.mpr hxlast0⟩
      -- On the zero slice, the new last coefficient disappears.
      calc
        Fin.snoc α (last_coordinate_lifting_coefficient S α β) ⬝ᵥ x
            = Fin.snoc α 0 ⬝ᵥ x := by
                simp [dotProduct_last_coordinate_lifting_coeffs, hxlast0]
        _ ≤ β := hzero_valid
    · have hxslice :
          partial_lifting_value α x ∈ last_coordinate_slice_values S α 1 := by
        exact mem_last_coordinate_slice_values_iff.mpr ⟨x, hxS, hxlast1, rfl⟩
      have hpartial_le :
          partial_lifting_value α x ≤ sSup (last_coordinate_slice_values S α 1) :=
        hGreatest.2 hxslice
      -- On the one slice, the supremum bound is exactly the amount subtracted in the lift.
      have hbound :
          partial_lifting_value α x +
              (β - sSup (last_coordinate_slice_values S α 1)) ≤
            β := by
        linarith
      simpa [dotProduct_last_coordinate_lifting_coeffs, last_coordinate_lifting_coefficient_eq,
        hxlast1] using hbound
  · intro αn hαn
    have hvalidαn :
        is_valid_inequality S (Fin.snoc α αn) β :=
      (mem_valid_last_coordinate_lifting_coefficients_iff.mp hαn)
    rcases existsTightPointOnOneSlice S α β hS_binary hone_slice_nonempty with
      ⟨x, hxS, hxlast, hxtight⟩
    have hαn_bound :
        partial_lifting_value α x + αn ≤ β := by
      simpa [dotProduct_last_coordinate_lifting_coeffs, hxlast] using hvalidαn hxS
    have hcoeff_eq :
        partial_lifting_value α x + last_coordinate_lifting_coefficient S α β = β := by
      simpa [dotProduct_last_coordinate_lifting_coeffs, hxlast] using hxtight
    -- Evaluating any valid lift at a tight slice maximizer bounds its last coefficient.
    linarith

/-- Validity consequence of `binary_last_coordinate_lifting_maximal`: the coefficient produced by
`last_coordinate_lifting_coefficient S α β` yields a valid lifted inequality on `S`. -/
theorem binary_last_coordinate_lifting_is_valid
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hvalid_zero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set n 0)
        (Fin.snoc α 0)
        β)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1)) :
    is_valid_inequality
      S
      (Fin.snoc α (last_coordinate_lifting_coefficient S α β))
      β := by
  -- Validity is the membership half of the maximality statement.
  simpa [mem_valid_last_coordinate_lifting_coefficients_iff] using
    (binary_last_coordinate_lifting_maximal S α β hS_binary hvalid_zero hone_slice_nonempty).1

/-- Upper-bound consequence of `binary_last_coordinate_lifting_maximal`: every valid lifted
last-coordinate coefficient is bounded above by `last_coordinate_lifting_coefficient S α β`. -/
theorem binary_last_coordinate_lifting_upper_bound
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hvalid_zero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set n 0)
        (Fin.snoc α 0)
        β)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1))
    {αn : ℝ}
    (hvalid : is_valid_inequality S (Fin.snoc α αn) β) :
    αn ≤ last_coordinate_lifting_coefficient S α β := by
  -- The order part of maximality bounds every other valid last-coordinate coefficient.
  exact
    (binary_last_coordinate_lifting_maximal S α β hS_binary hvalid_zero hone_slice_nonempty).2
      ((mem_valid_last_coordinate_lifting_coefficients_iff).2 hvalid)

/-- Proposition 7.2 (2). Under the same hypotheses, if
`∑_{i < n} αᵢ xᵢ ≤ β` defines a nonempty `d`-dimensional face of
`conv(S) ∩ {x_last = 0}`, then the lifted inequality defines a face of `conv(S)` of dimension at
least `d + 1`. -/
theorem binary_last_coordinate_lifting_face_dimension_lower_bound
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (d : ℕ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) Set.univ)
    (hvalid_zero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set n 0)
        (Fin.snoc α 0)
        β)
    (hone_slice_nonempty :
      Set.Nonempty (S ∩ last_coordinate_eq_set n 1))
    (hzero_slice_face_nonempty :
      Set.Nonempty
        (face_set
          (convexHull ℝ S ∩ last_coordinate_eq_set n 0)
          (Fin.snoc α 0)
          β))
    (hzero_slice_face_dim :
      Module.finrank ℝ
          (affineSpan ℝ
            (face_set
              (convexHull ℝ S ∩ last_coordinate_eq_set n 0)
              (Fin.snoc α 0)
              β)).direction =
        d) :
    IsExposed ℝ
      (convexHull ℝ S)
      (face_set
        (convexHull ℝ S)
        (Fin.snoc α (last_coordinate_lifting_coefficient S α β))
        β) ∧
      d + 1 ≤
        Module.finrank ℝ
          (affineSpan ℝ
            (face_set
              (convexHull ℝ S)
              (Fin.snoc α (last_coordinate_lifting_coefficient S α β))
              β)).direction := by
  let coeff := last_coordinate_lifting_coefficient S α β
  let F0 : Set (Fin (n + 1) → ℝ) :=
    face_set
      (convexHull ℝ S ∩ last_coordinate_eq_set n 0)
      (Fin.snoc α 0)
      β
  let F : Set (Fin (n + 1) → ℝ) :=
    face_set
      (convexHull ℝ S)
      (Fin.snoc α coeff)
      β
  have hvalid :
      is_valid_inequality S (Fin.snoc α coeff) β :=
    binary_last_coordinate_lifting_is_valid S α β hS_binary hvalid_zero hone_slice_nonempty
  have hvalidHull :
      is_valid_inequality (convexHull ℝ S) (Fin.snoc α coeff) β :=
    (is_valid_inequality_convexHull_iff).2 hvalid
  have hF_exposed : IsExposed ℝ (convexHull ℝ S) F := by
    -- The lifted face is exposed because the lifted inequality is valid on the hull.
    simpa [F] using isExposed_face_set_of_valid_inequality hvalidHull
  have hF0_nonempty : F0.Nonempty := by
    simpa [F0] using hzero_slice_face_nonempty
  have hF0_dim :
      Module.finrank ℝ (affineSpan ℝ F0).direction = d := by
    simpa [F0] using hzero_slice_face_dim
  have hF0_subset_zero : F0 ⊆ last_coordinate_eq_set n 0 := by
    intro x hx
    exact (mem_face_set_iff.mp hx).1.2
  have hAffF0_subset_zero :
      (affineSpan ℝ F0 : Set (Fin (n + 1) → ℝ)) ⊆ last_coordinate_eq_set n 0 :=
    affineSpan_subset_lastCoordinateEqZero (T := F0) hF0_subset_zero
  have hF0_subset_F : F0 ⊆ F := by
    intro x hx
    rcases mem_face_set_iff.mp hx with ⟨hxbase, hxeq⟩
    rcases hxbase with ⟨hxHull, hxlast0Set⟩
    have hxlast0 : x (Fin.last n) = 0 := mem_last_coordinate_eq_set_iff.mp hxlast0Set
    refine (mem_face_set_iff).2 ⟨hxHull, ?_⟩
    -- Points on the zero slice satisfy the lifted equation exactly when they satisfy the old one.
    calc
      Fin.snoc α coeff ⬝ᵥ x = Fin.snoc α 0 ⬝ᵥ x := by
        simp [dotProduct_last_coordinate_lifting_coeffs, hxlast0]
      _ = β := hxeq
  rcases existsTightPointOnOneSlice S α β hS_binary hone_slice_nonempty with
    ⟨xbar, hxbarS, hxbarlast, hxbarEq⟩
  have hxbarF : xbar ∈ F := by
    -- The maximizing `x_last = 1` point lies on the lifted face of `conv(S)`.
    refine (mem_face_set_iff).2 ⟨subset_convexHull ℝ S hxbarS, ?_⟩
    simpa [coeff] using hxbarEq
  have hxbar_not_mem_affF0 : xbar ∉ affineSpan ℝ F0 := by
    intro hxbarAff
    have hxbarlast0 : xbar (Fin.last n) = 0 := by
      exact mem_last_coordinate_eq_set_iff.mp (hAffF0_subset_zero hxbarAff)
    linarith
  have hAff_lt : affineSpan ℝ F0 < affineSpan ℝ F := by
    -- The zero-slice face spans a proper affine subspace because `xbar` lies in `F` but not in
    -- the zero-slice hyperplane containing `affineSpan ℝ F0`.
    refine SetLike.lt_iff_le_and_exists.mpr ?_
    refine ⟨affineSpan_mono ℝ hF0_subset_F, xbar, ?_, hxbar_not_mem_affF0⟩
    exact subset_affineSpan ℝ F hxbarF
  have hAffF0_nonempty :
      ((affineSpan ℝ F0 : AffineSubspace ℝ (Fin (n + 1) → ℝ)) :
        Set (Fin (n + 1) → ℝ)).Nonempty := by
    rcases hF0_nonempty with ⟨x, hx⟩
    exact ⟨x, subset_affineSpan ℝ F0 hx⟩
  have hDir_lt :
      (affineSpan ℝ F0).direction < (affineSpan ℝ F).direction :=
    AffineSubspace.direction_lt_of_nonempty
      (k := ℝ)
      (V := Fin (n + 1) → ℝ)
      (P := Fin (n + 1) → ℝ)
      (s₁ := affineSpan ℝ F0)
      (s₂ := affineSpan ℝ F)
      hAff_lt
      hAffF0_nonempty
  have hFinrank_lt :
      Module.finrank ℝ (affineSpan ℝ F0).direction <
        Module.finrank ℝ (affineSpan ℝ F).direction :=
    Submodule.finrank_lt_finrank_of_lt (K := ℝ) (V := Fin (n + 1) → ℝ) hDir_lt
  have hdim_lower :
      d + 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    have hdlt : d < Module.finrank ℝ (affineSpan ℝ F).direction := by
      rw [← hF0_dim]
      exact hFinrank_lt
    exact Nat.succ_le_of_lt hdlt
  exact ⟨by simpa [F, coeff] using hF_exposed, by simpa [F, coeff] using hdim_lower⟩

end Proposition72
