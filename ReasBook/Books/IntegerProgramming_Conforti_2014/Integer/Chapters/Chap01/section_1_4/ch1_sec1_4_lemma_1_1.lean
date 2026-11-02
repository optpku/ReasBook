module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Real.Archimedean
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

open scoped BigOperators Matrix

public section

variable {n : ℕ}
variable {S : Set (Fin n → ℝ)} {c : Fin n → ℝ}

/-- Applying the linear objective `x ↦ c ⬝ᵥ x` to `convexHull ℝ S` is the same as taking the
convex hull of the objective-value image of `S`. This is the source-facing bridge to the canonical
linear-map fact `LinearMap.image_convexHull`. -/
theorem dotProduct_image_convexHull :
    ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) =
      convexHull ℝ ((fun x ↦ c ⬝ᵥ x) '' S) := by
  -- Rewrite the objective as the canonical linear map `dotProductBilin`.
  simpa using (LinearMap.image_convexHull (dotProductBilin ℝ ℝ c) S)

/-- Helper for Lemma 1.1: taking the convex hull of a set of reals does not change its upper
bounds. -/
private lemma upperBounds_convexHull_eq (T : Set ℝ) :
    upperBounds (convexHull ℝ T) = upperBounds T := by
  ext z
  constructor
  · -- Every upper bound for the convex hull is already an upper bound on the generating set.
    intro hz y hy
    exact hz (subset_convexHull ℝ T hy)
  · -- The half-line `(-∞, z]` is convex, so it contains the convex hull once it contains `T`.
    intro hz y hy
    have hsubset : convexHull ℝ T ⊆ Set.Iic z :=
      convexHull_min (fun x hx ↦ hz hx) (convex_Iic z)
    simpa using hsubset hy

/-- Helper for Lemma 1.1: if an upper bound of a real set lies in its convex hull, then that upper
endpoint already belongs to the original set. -/
private lemma mem_of_mem_convexHull_of_mem_upperBounds {T : Set ℝ} {z : ℝ}
    (hzHull : z ∈ convexHull ℝ T) (hzUpper : z ∈ upperBounds T) : z ∈ T := by
  classical
  rcases (mem_convexHull_iff_exists_fintype).1 hzHull with ⟨ι, _, w, x, hw₀, hw₁, hxT, hz⟩
  let s : Finset ι := Finset.univ
  -- The barycentric relation forces the index set to be nonempty.
  have hs : s.Nonempty := by
    by_contra hsEmpty
    have hsEq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsEmpty
    have : (0 : ℝ) = 1 := by
      calc
        (0 : ℝ) = ∑ i ∈ s, w i := by simp [s, hsEq]
        _ = ∑ i, w i := by simp [s]
        _ = 1 := hw₁
    exact zero_ne_one this
  have hw₁' : ∑ i ∈ s, w i = 1 := by
    simpa [s] using hw₁
  have hzCenter : s.centerMass w x = z := by
    -- Converting the witness to a center-of-mass form lets us use `centerMass_le_sup`.
    rw [s.centerMass_eq_of_sum_1 x hw₁']
    simpa [s] using hz
  have hsumPos : 0 < ∑ i ∈ s, w i := by
    rw [hw₁']
    norm_num
  have hz_le_sup : z ≤ s.sup' hs x := by
    rw [← hzCenter]
    exact Finset.centerMass_le_sup (fun i _ ↦ hw₀ i) hsumPos
  have hsup_le_z : s.sup' hs x ≤ z :=
    Finset.sup'_le hs x (fun i _ ↦ hzUpper (hxT i))
  have hsup_eq : s.sup' hs x = z := le_antisymm hsup_le_z hz_le_sup
  rcases Finset.exists_mem_eq_sup' hs x with ⟨i, hi, hmax⟩
  -- The maximum objective value in the finite support equals `z`, so one support point realizes it.
  have hxi_eq : x i = z := by
    calc
      x i = s.sup' hs x := hmax.symm
      _ = z := hsup_eq
  simpa [hxi_eq] using hxT i

/-- The image of a linear objective on `S` is bounded above exactly when its image on
`convexHull ℝ S` is bounded above. -/
theorem dotProduct_bddAbove_image_iff_convexHull :
    BddAbove ((fun x ↦ c ⬝ᵥ x) '' S) ↔
      BddAbove ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) := by
  rw [dotProduct_image_convexHull]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rwa [upperBounds_convexHull_eq]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [upperBounds_convexHull_eq] using hz

/-- The image of a linear objective on `S` has the same least-upper-bound witnesses as its image on
`convexHull ℝ S`. -/
theorem dotProduct_isLUB_image_convexHull_iff
    (z : ℝ) :
    IsLUB ((fun x ↦ c ⬝ᵥ x) '' S) z ↔
      IsLUB ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) z := by
  -- Rewrite the convex-hull image through the linear objective and compare upper bounds.
  rw [dotProduct_image_convexHull]
  simp [IsLUB, upperBounds_convexHull_eq]

/-- Lemma 1.1 (1): for a linear objective `c ⬝ᵥ x`, the supremum over `S` agrees with the supremum
over `convexHull ℝ S` under the bounded-above hypothesis used to control `sSup`. -/
theorem dotProduct_sSup_image_eq_sSup_image_convexHull
    (hBdd : BddAbove ((fun x ↦ c ⬝ᵥ x) '' S)) :
    sSup ((fun x ↦ c ⬝ᵥ x) '' S) =
      sSup ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) := by
  by_cases hS : S = ∅
  · -- In the empty-set case both image sets are empty, so both `sSup` values are `0`.
    subst hS
    simp
  · obtain ⟨x, hxS⟩ := Set.nonempty_iff_ne_empty.mpr hS
    have hImageNonempty : (((fun x ↦ c ⬝ᵥ x) '' S) : Set ℝ).Nonempty :=
      ⟨c ⬝ᵥ x, ⟨x, hxS, rfl⟩⟩
    have hHullImageNonempty : (((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) : Set ℝ).Nonempty :=
      ⟨c ⬝ᵥ x, ⟨x, subset_convexHull ℝ S hxS, rfl⟩⟩
    have hLub :
        IsLUB ((fun x ↦ c ⬝ᵥ x) '' S) (sSup ((fun x ↦ c ⬝ᵥ x) '' S)) :=
      Real.isLUB_sSup hImageNonempty hBdd
    -- Transport the `IsLUB` witness across the convex-hull image equivalence.
    have hHullLub :
        IsLUB ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) (sSup ((fun x ↦ c ⬝ᵥ x) '' S)) :=
      (dotProduct_isLUB_image_convexHull_iff (sSup ((fun x ↦ c ⬝ᵥ x) '' S))).1 hLub
    exact (hHullLub.csSup_eq hHullImageNonempty).symm

/-- Attainment of a linear objective on `S` is equivalent to attainment on `convexHull ℝ S` at the
level of greatest elements of the image set. -/
theorem dotProduct_isGreatest_image_convexHull_iff
    (z : ℝ) :
    IsGreatest ((fun x ↦ c ⬝ᵥ x) '' S) z ↔
      IsGreatest ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) z := by
  rw [dotProduct_image_convexHull]
  constructor
  · intro hz
    refine ⟨subset_convexHull ℝ _ hz.1, ?_⟩
    -- A greatest element of the original image is still an upper bound after taking convex hull.
    have hzUpperHull : z ∈ upperBounds (convexHull ℝ ((fun x ↦ c ⬝ᵥ x) '' S)) := by
      rw [upperBounds_convexHull_eq]
      exact hz.2
    intro y hy
    exact hzUpperHull hy
  · intro hz
    refine ⟨?_, ?_⟩
    · -- The reverse direction uses the real endpoint lemma for convex hulls.
      have hzUpper : z ∈ upperBounds ((fun x ↦ c ⬝ᵥ x) '' S) := by
        intro y hy
        exact hz.2 (subset_convexHull ℝ _ hy)
      exact mem_of_mem_convexHull_of_mem_upperBounds hz.1 hzUpper
    · -- Any original image value stays in the convex hull.
      -- That makes the upper-bound inequality descend immediately.
      intro y hy
      exact hz.2 (subset_convexHull ℝ _ hy)

/-- Lemma 1.1 (2): the linear objective `c ⬝ᵥ x` attains its supremum on `S` if and only if it
attains its supremum on `convexHull ℝ S`, under the same bounded-above hypothesis used to form the
literal `sSup` expressions. -/
theorem dotProduct_attainsSup_iff_convexHull
    (hBdd : BddAbove ((fun x ↦ c ⬝ᵥ x) '' S)) :
    (∃ x ∈ S, c ⬝ᵥ x = sSup ((fun x ↦ c ⬝ᵥ x) '' S)) ↔
      ∃ x ∈ convexHull ℝ S, c ⬝ᵥ x = sSup ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) := by
  have hBddHull : BddAbove ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) :=
    dotProduct_bddAbove_image_iff_convexHull.1 hBdd
  constructor
  · rintro ⟨x, hxS, hxEq⟩
    have hxGreatest : IsGreatest ((fun x ↦ c ⬝ᵥ x) '' S) (c ⬝ᵥ x) := by
      refine ⟨⟨x, hxS, rfl⟩, ?_⟩
      -- Equality with `sSup` upgrades the witness to a greatest element.
      intro y hy
      rw [hxEq]
      exact le_csSup hBdd hy
    have hxHullGreatest :=
      (dotProduct_isGreatest_image_convexHull_iff (c ⬝ᵥ x)).1 hxGreatest
    rcases hxHullGreatest.1 with ⟨xBar, hxBar, hxBarEq⟩
    -- Unpack the greatest-element witness on the convex hull back to a point witness.
    refine ⟨xBar, hxBar, ?_⟩
    rw [hxHullGreatest.csSup_eq]
    exact hxBarEq
  · rintro ⟨xBar, hxBar, hxBarEq⟩
    have hxHullGreatest : IsGreatest ((fun x ↦ c ⬝ᵥ x) '' convexHull ℝ S) (c ⬝ᵥ xBar) := by
      refine ⟨⟨xBar, hxBar, rfl⟩, ?_⟩
      -- The bounded-above hypothesis on the convex-hull image closes the supremum inequality.
      intro y hy
      rw [hxBarEq]
      exact le_csSup hBddHull hy
    have hxGreatest :=
      (dotProduct_isGreatest_image_convexHull_iff (c ⬝ᵥ xBar)).2 hxHullGreatest
    rcases hxGreatest.1 with ⟨x, hxS, hxEq⟩
    -- Pull the image witness back to `S` and rewrite the greatest value as the supremum.
    refine ⟨x, hxS, ?_⟩
    rw [hxGreatest.csSup_eq]
    exact hxEq

end
