import Mathlib

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

/-- The signed coordinate sum attached to a subset of coordinates. -/
def signed_coordinate_sum {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  S.sum (fun i ↦ x i) - (Finset.univ \ S).sum fun i ↦ x i

/-- The `n`-dimensional octahedron, written in its intrinsic `ℓ¹`-ball form. -/
def octahedron (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i : Fin n, |x i| ≤ 1}

/-- Membership in `octahedron n` is exactly the `ℓ¹` inequality `∑ i |x i| ≤ 1`. -/
theorem mem_octahedron_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ octahedron n ↔ ∑ i : Fin n, |x i| ≤ 1 := by
  rfl

/-- The first `n` lifted coordinates, viewed as the positive block. -/
def octahedron_extension_pos {n : ℕ} (z : Fin (n + n) → ℝ) : Fin n → ℝ :=
  fun i ↦ z (Fin.castAdd n i)

/-- The second `n` lifted coordinates, viewed as the negative block. -/
def octahedron_extension_neg {n : ℕ} (z : Fin (n + n) → ℝ) : Fin n → ℝ :=
  fun i ↦ z (Fin.natAdd n i)

@[simp] theorem octahedron_extension_pos_addCases {n : ℕ} (u v : Fin n → ℝ) :
    octahedron_extension_pos (Fin.addCases u v) = u := by
  funext i
  simp [octahedron_extension_pos]

@[simp] theorem octahedron_extension_neg_addCases {n : ℕ} (u v : Fin n → ℝ) :
    octahedron_extension_neg (Fin.addCases u v) = v := by
  funext i
  simpa [Fin.append, octahedron_extension_neg] using (Fin.append_right u v i)

/-- The lifted polyhedron whose `x`-projection gives the octahedron, written through the positive
and negative coordinate blocks of the `2n` lifted variables. -/
def octahedron_extension (n : ℕ) : Set ((Fin n → ℝ) × (Fin (n + n) → ℝ)) :=
  {xz |
    xz.1 = octahedron_extension_pos xz.2 - octahedron_extension_neg xz.2 ∧
      ((∑ i : Fin n, (octahedron_extension_pos xz.2 i + octahedron_extension_neg xz.2 i)) = 1) ∧
      (∀ i : Fin n, 0 ≤ octahedron_extension_pos xz.2 i) ∧
      ∀ i : Fin n, 0 ≤ octahedron_extension_neg xz.2 i}

/-- Membership in `octahedron_extension n` is the positive-negative-part form of the textbook
lifted system. -/
theorem mem_octahedron_extension_iff
    {n : ℕ} {x : Fin n → ℝ} {z : Fin (n + n) → ℝ} :
    (x, z) ∈ octahedron_extension n ↔
      x = octahedron_extension_pos z - octahedron_extension_neg z ∧
        ((∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i)) = 1) ∧
        (∀ i : Fin n, 0 ≤ octahedron_extension_pos z i) ∧
        ∀ i : Fin n, 0 ≤ octahedron_extension_neg z i := by
  rfl

/-- Any signed subset sum is bounded above by the `ℓ¹` norm. -/
theorem signed_coordinate_sum_le_sum_abs
    {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    signed_coordinate_sum S x ≤ ∑ i : Fin n, |x i| := by
  have hpartition :
      S.sum (fun i ↦ |x i|) + (Finset.univ \ S).sum (fun i ↦ |x i|) =
        ∑ i : Fin n, |x i| := by
    have hdisj : Disjoint S (Finset.univ \ S) := by
      refine Finset.disjoint_left.2 ?_
      intro i hiS hiComp
      exact (Finset.mem_sdiff.mp hiComp).2 hiS
    calc
      S.sum (fun i ↦ |x i|) + (Finset.univ \ S).sum (fun i ↦ |x i|)
          = (S ∪ (Finset.univ \ S)).sum (fun i ↦ |x i|) := by
              symm
              exact Finset.sum_union hdisj
      _ = ∑ i : Fin n, |x i| := by
            rw [Finset.union_sdiff_of_subset (by simp)]
  calc
    signed_coordinate_sum S x
        = S.sum (fun i ↦ x i) + (Finset.univ \ S).sum (fun i ↦ -x i) := by
            rw [signed_coordinate_sum, sub_eq_add_neg, Finset.sum_neg_distrib]
    _ ≤ S.sum (fun i ↦ |x i|) + (Finset.univ \ S).sum (fun i ↦ |x i|) := by
          refine add_le_add ?_ ?_
          · exact Finset.sum_le_sum fun i hi ↦ le_abs_self (x i)
          · exact Finset.sum_le_sum fun i hi ↦ by
              simpa [abs_neg] using neg_le_abs (x i)
    _ = ∑ i : Fin n, |x i| := hpartition

/-- Choosing the nonnegative coordinates as the positive-sign subset turns the signed coordinate
sum into the `ℓ¹` norm. -/
theorem signed_coordinate_sum_filter_nonneg_eq_sum_abs
    {n : ℕ} (x : Fin n → ℝ) :
    signed_coordinate_sum (Finset.univ.filter fun i : Fin n ↦ 0 ≤ x i) x =
      ∑ i : Fin n, |x i| := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ 0 ≤ x i
  have hpos :
      S.sum (fun i ↦ x i) = S.sum (fun i ↦ |x i|) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hxi : 0 ≤ x i := by
      simpa [S] using hi
    simp [abs_of_nonneg hxi]
  have hneg :
      -((Finset.univ \ S).sum fun i ↦ x i) = (Finset.univ \ S).sum fun i ↦ |x i| := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hxi : ¬ 0 ≤ x i := by
      simpa [S] using hi
    have hlt : x i < 0 := lt_of_not_ge hxi
    simp [abs_of_neg hlt]
  have hsplit :
      S.sum (fun i ↦ |x i|) + (Finset.univ \ S).sum (fun i ↦ |x i|) = ∑ i : Fin n, |x i| := by
    rw [show (Finset.univ \ S) = Finset.univ.filter (fun i : Fin n ↦ ¬ 0 ≤ x i) by
      ext i
      simp [S]]
    simpa [S] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n ↦ 0 ≤ x i) (fun i ↦ |x i|))
  calc
    signed_coordinate_sum (Finset.univ.filter fun i : Fin n ↦ 0 ≤ x i) x
        = S.sum (fun i ↦ x i) - (Finset.univ \ S).sum fun i ↦ x i := by
            simp [signed_coordinate_sum, S]
    _ = S.sum (fun i ↦ |x i|) + (Finset.univ \ S).sum fun i ↦ |x i| := by
          rw [sub_eq_add_neg, hpos, hneg]
    _ = ∑ i : Fin n, |x i| := hsplit

/-- The intrinsic `ℓ¹`-ball description of `octahedron n` is equivalent to the signed-facet
description from the text. -/
theorem mem_octahedron_iff_forall_signed_coordinate_sum_le_one
    {n : ℕ} {x : Fin n → ℝ} :
    x ∈ octahedron n ↔ ∀ S : Finset (Fin n), signed_coordinate_sum S x ≤ 1 := by
  rw [mem_octahedron_iff]
  constructor
  · intro hx S
    exact (signed_coordinate_sum_le_sum_abs S x).trans hx
  · intro hx
    simpa [signed_coordinate_sum_filter_nonneg_eq_sum_abs x] using
      hx (Finset.univ.filter fun i : Fin n ↦ 0 ≤ x i)

/-- Any point in the lifted formulation lies in the octahedron. -/
theorem mem_octahedron_of_extension
    {n : ℕ} {x : Fin n → ℝ} {z : Fin (n + n) → ℝ}
    (hx : x = octahedron_extension_pos z - octahedron_extension_neg z)
    (hsum : (∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i)) = 1)
    (hz_pos : ∀ i : Fin n, 0 ≤ octahedron_extension_pos z i)
    (hz_neg : ∀ i : Fin n, 0 ≤ octahedron_extension_neg z i) :
    x ∈ octahedron n := by
  rw [mem_octahedron_iff]
  calc
    ∑ i : Fin n, |x i|
        = ∑ i : Fin n, |octahedron_extension_pos z i - octahedron_extension_neg z i| := by
            simp [hx]
    _ ≤ ∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          exact (abs_sub _ _).trans <| by
            rw [abs_of_nonneg (hz_pos i), abs_of_nonneg (hz_neg i)]
    _ = 1 := hsum

/-- The lifted formulation implies every signed facet inequality as a derived consequence. -/
theorem signed_coordinate_sum_le_one_of_extension
    {n : ℕ} {x : Fin n → ℝ} {z : Fin (n + n) → ℝ}
    (hx : x = octahedron_extension_pos z - octahedron_extension_neg z)
    (hsum : (∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i)) = 1)
    (hz_pos : ∀ i : Fin n, 0 ≤ octahedron_extension_pos z i)
    (hz_neg : ∀ i : Fin n, 0 ≤ octahedron_extension_neg z i) :
    ∀ S : Finset (Fin n), signed_coordinate_sum S x ≤ 1 := by
  exact (mem_octahedron_iff_forall_signed_coordinate_sum_le_one.1 <|
    mem_octahedron_of_extension hx hsum hz_pos hz_neg)

/-- An `ℓ¹`-bounded point admits a lifted representation by its positive and negative parts
together with one symmetric slack pair. -/
theorem exists_mem_octahedron_extension_of_sum_abs_le_one
    {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : ∑ i : Fin n, |x i| ≤ 1) :
    ∃ z : Fin (n + n) → ℝ, (x, z) ∈ octahedron_extension n := by
  let i0 : Fin n := ⟨0, hn⟩
  let slack : ℝ := (1 - ∑ i : Fin n, |x i|) / 2
  let pos : Fin n → ℝ := fun i ↦ max (x i) 0 + if i = i0 then slack else 0
  let neg : Fin n → ℝ := fun i ↦ max (-x i) 0 + if i = i0 then slack else 0
  let z : Fin (n + n) → ℝ := Fin.addCases pos neg
  have hslack_nonneg : 0 ≤ slack := by
    dsimp [slack]
    linarith
  have hcoord : x = octahedron_extension_pos z - octahedron_extension_neg z := by
    ext i
    simp [z, pos, neg, slack, max_zero_sub_max_neg_zero_eq_self]
  have hsum :
      (∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i)) = 1 := by
    calc
      (∑ i : Fin n, (octahedron_extension_pos z i + octahedron_extension_neg z i))
          = Finset.univ.sum (fun i : Fin n ↦ pos i + neg i) := by
              simp [z]
      _ = (∑ i : Fin n, |x i|) + (slack + slack) := by
            calc
              Finset.univ.sum (fun i : Fin n ↦ pos i + neg i)
                  = Finset.univ.sum fun i : Fin n ↦
                      (max (x i) 0 + max (-x i) 0) +
                        ((if i = i0 then slack else 0) + (if i = i0 then slack else 0)) := by
                          refine Finset.sum_congr rfl ?_
                          intro i hi
                          dsimp [pos, neg]
                          ring
              _ = (∑ i : Fin n, (max (x i) 0 + max (-x i) 0)) +
                    Finset.univ.sum
                      (fun i : Fin n ↦
                        (if i = i0 then slack else 0) + (if i = i0 then slack else 0)) := by
                      rw [Finset.sum_add_distrib]
              _ = (∑ i : Fin n, |x i|) +
                    Finset.univ.sum
                      (fun i : Fin n ↦
                        (if i = i0 then slack else 0) + (if i = i0 then slack else 0)) := by
                      congr 1
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simp [max_zero_add_max_neg_zero_eq_abs_self]
              _ = (∑ i : Fin n, |x i|) + (slack + slack) := by
                    rw [Finset.sum_add_distrib]
                    simp
      _ = 1 := by
            dsimp [slack]
            linarith
  have hz_pos : ∀ i : Fin n, 0 ≤ octahedron_extension_pos z i := by
    intro i
    by_cases hi : i = i0
    · subst hi
      have hmax : 0 ≤ max (x i0) 0 := le_max_right _ _
      simp [z, pos]
      linarith
    · simp [z, pos, hi]
  have hz_neg : ∀ i : Fin n, 0 ≤ octahedron_extension_neg z i := by
    intro i
    by_cases hi : i = i0
    · subst hi
      have hmax : 0 ≤ max (-x i0) 0 := le_max_right _ _
      simp [z, neg]
      linarith
    · simp [z, neg, hi]
  exact ⟨z, mem_octahedron_extension_iff.2 ⟨hcoord, hsum, hz_pos, hz_neg⟩⟩

/-- Example 3.45. For a positive integer `n`, the projection onto the `x`-coordinates of the
lifted polyhedron with variables `z₁, …, z_{2n}` is the octahedron `oct_n`. -/
theorem image_fst_octahedron_extension_eq_octahedron {n : ℕ} (hn : 0 < n) :
    Prod.fst '' octahedron_extension n = octahedron n := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_image] at hx
    rcases hx with ⟨xz, hz, hxz⟩
    rcases xz with ⟨x', z⟩
    have hx' : x' = x := by
      simpa using hxz
    subst x'
    rcases mem_octahedron_extension_iff.1 hz with ⟨hxcoord, hsum, hz_pos, hz_neg⟩
    exact mem_octahedron_of_extension hxcoord hsum hz_pos hz_neg
  · intro hx
    have hsum_abs : ∑ i : Fin n, |x i| ≤ 1 := mem_octahedron_iff.1 hx
    rcases exists_mem_octahedron_extension_of_sum_abs_le_one hn hsum_abs with ⟨z, hz⟩
    rw [Set.mem_image]
    exact ⟨(x, z), hz, rfl⟩
