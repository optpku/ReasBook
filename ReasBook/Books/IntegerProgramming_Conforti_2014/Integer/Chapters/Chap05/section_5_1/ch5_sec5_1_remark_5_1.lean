/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

-- This file reuses the Chapter 5 split owners `split_hull` and `split_closure` from
-- `ch5_sec5_1_definition_5_1_extra_1` and adds only the source-facing primitive-split facts.

section Remark51

variable {n : ℕ}

/-- Helper for Remark 5.1: the split hull cut out by the zero vector is just the convex hull of
`P`, because one of the two zero branches is all of `P`. -/
lemma zero_split_hull_eq_convexHull
    (P : Set (Fin n → ℝ))
    (π0 : ℤ) :
    split_hull P (fun _ : Fin n ↦ 0) π0 = convexHull ℝ P := by
  -- The two zero branches cover `P`, since either `0 ≤ π₀` or `π₀ + 1 ≤ 0`.
  have hbranches :
      split_branch_lower P (fun _ : Fin n ↦ 0) π0 ∪
          split_branch_upper P (fun _ : Fin n ↦ 0) π0 =
        P := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact (mem_split_branch_lower_iff.mp hx).1
      · exact (mem_split_branch_upper_iff.mp hx).1
    · intro hxP
      have hdot : split_dot (fun _ : Fin n ↦ 0) x = 0 := by
        rw [split_dot_eq_sum]
        simp
      by_cases hπ0 : 0 ≤ π0
      · left
        refine (mem_split_branch_lower_iff).2 ?_
        constructor
        · exact hxP
        · rw [hdot]
          exact_mod_cast hπ0
      · right
        have hπ0' : π0 + 1 ≤ 0 := by
          omega
        refine (mem_split_branch_upper_iff).2 ?_
        constructor
        · exact hxP
        · rw [hdot]
          exact_mod_cast hπ0'
  -- Rewriting the union gives the desired split-hull identity.
  simp [split_hull, hbranches]

/-- Helper for Remark 5.1: a nonzero integer vector has a coordinate that is nonzero. -/
lemma exists_nonzero_coordinate
    (π : Fin n → ℤ)
    (hπ : π ≠ 0) :
    ∃ i : Fin n, π i ≠ 0 := by
  classical
  -- A vector with no nonzero coordinate would be the zero function.
  by_contra hcoord
  apply hπ
  ext i
  by_contra hi
  exact hcoord ⟨i, hi⟩

/-- Helper for Remark 5.1: the gcd of the coordinate absolute values of a nonzero integer vector
is positive. -/
lemma coordinate_gcd_pos
    (π : Fin n → ℤ)
    (hπ : π ≠ 0) :
    0 < Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i)) := by
  -- Use a nonzero coordinate to force the coordinate gcd away from zero.
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate π hπ
  have hg_dvd :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (π j)) ∣ Int.natAbs (π i) := by
    exact Finset.gcd_dvd (by simp)
  have hnatabs_ne : Int.natAbs (π i) ≠ 0 := by
    simpa using hi
  have hg_ne :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (π j)) ≠ 0 := by
    intro hg_zero
    rw [hg_zero] at hg_dvd
    exact hnatabs_ne (by simpa using hg_dvd)
  exact Nat.pos_of_ne_zero hg_ne

/-- Helper for Remark 5.1: taking the `Finset.gcd` after coercing a natural-valued family to `ℤ`
agrees with coercing the `Finset.gcd` in `ℕ`. -/
lemma finset_gcd_int_cast_eq_nat_gcd
    (s : Finset (Fin n))
    (f : Fin n → ℕ) :
    s.gcd (fun i ↦ (f i : ℤ)) = ((Finset.gcd s f : ℕ) : ℤ) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.gcd_insert, Finset.gcd_insert, hs]
    exact congrArg (fun z : ℕ => (z : ℤ)) (Int.gcd_natCast_natCast (f a) (Finset.gcd s f))

/-- Helper for Remark 5.1: the gcd of the coefficient absolute values computed in `ℤ` is the
integer cast of the gcd of their natural absolute values. -/
lemma coordinate_gcd_int_cast_eq_nat_gcd_natAbs
    (π : Fin n → ℤ) :
    Finset.univ.gcd (fun i : Fin n ↦ ((π i).natAbs : ℤ)) =
      ((Finset.gcd Finset.univ (fun i : Fin n ↦ Int.natAbs (π i)) : ℕ) : ℤ) := by
  simpa using
    finset_gcd_int_cast_eq_nat_gcd (n := n) Finset.univ (fun i : Fin n ↦ Int.natAbs (π i))

/-- Helper for Remark 5.1: after dividing a nonzero split vector by the gcd of its coordinates,
the original split functional is the gcd times the normalized split functional. -/
lemma normalized_split_dot_eq_gcd_mul
    (π : Fin n → ℤ)
    (_hπ : π ≠ 0)
    (x : Fin n → ℝ) :
    let g : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i))
    split_dot π x = (g : ℝ) * split_dot (fun j : Fin n ↦ π j / g) x := by
  -- Route correction: keep the gcd on its raw Nat surface so every division term elaborates to
  -- the same coercion-normal form.
  set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i))
  with hgN
  have hg_dvd : ∀ j : Fin n, (gN : ℤ) ∣ π j := by
    intro j
    rw [Int.natCast_dvd]
    simpa [hgN] using (Finset.gcd_dvd (b := j) (f := fun i : Fin n ↦ Int.natAbs (π i)) (by simp))
  -- Rewrite each coefficient as the gcd times its normalized quotient, then factor the gcd out.
  simpa [hgN] using
    calc
    split_dot π x = ∑ j : Fin n, (π j : ℝ) * x j := by
      rw [split_dot_eq_sum]
    _ = ∑ j : Fin n, ((((gN : ℤ) * (π j / gN)) : ℤ) : ℝ) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Int.mul_ediv_cancel' (hg_dvd j)]
    _ = ∑ j : Fin n, ((gN : ℝ) * ((π j / gN : ℤ) : ℝ)) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Int.cast_mul]
      norm_num
    _ = ∑ j : Fin n, (gN : ℝ) * (((π j / gN : ℤ) : ℝ) * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_assoc]
    _ = (gN : ℝ) * ∑ j : Fin n, ((π j / gN : ℤ) : ℝ) * x j := by
      rw [Finset.mul_sum]
    _ = (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / gN) x := by
      rw [split_dot_eq_sum]

/-- Helper for Remark 5.1: the floor window obtained by dividing `π₀` by a positive gcd sits
inside the original split window after rescaling. -/
lemma normalized_split_floor_window_bounds
    {g : ℕ}
    (hg : 0 < g)
    (π0 : ℤ) :
    ((g : ℤ) * (π0 / g) ≤ π0) ∧ (π0 + 1 ≤ (g : ℤ) * (π0 / g + 1)) := by
  have hg_pos : (0 : ℤ) < g := by
    exact_mod_cast hg
  have hg_ne : (g : ℤ) ≠ 0 := by
    exact ne_of_gt hg_pos
  have hrem_nonneg : 0 ≤ π0 % g := Int.emod_nonneg _ hg_ne
  have hrem_lt : π0 % g < g := Int.emod_lt_of_pos _ hg_pos
  constructor
  · -- The remainder term is nonnegative, so removing it can only decrease the value.
    calc
      (g : ℤ) * (π0 / g) ≤ (g : ℤ) * (π0 / g) + π0 % g := by
        exact le_add_of_nonneg_right hrem_nonneg
      _ = π0 := by
        simpa using (Int.mul_ediv_add_emod π0 (g : ℤ))
  · -- The remainder is strictly smaller than `g`, so adding one still fits in the next block.
    have hstep : π0 % g + 1 ≤ g := by
      omega
    have hdecomp : (g : ℤ) * (π0 / g) + π0 % g = π0 := by
      simpa using (Int.mul_ediv_add_emod π0 (g : ℤ))
    have hbound : π0 + 1 ≤ (g : ℤ) * (π0 / g) + g := by
      omega
    calc
      π0 + 1 ≤ (g : ℤ) * (π0 / g) + g := hbound
      _ = (g : ℤ) * (π0 / g + 1) := by
        ring

/-- Helper for Remark 5.1: dividing a nonzero split vector by the gcd of its coordinates produces
a primitive coefficient vector. -/
lemma normalized_split_vector_gcd_eq_one
    (π : Fin n → ℤ)
    (hπ : π ≠ 0) :
    Finset.univ.gcd
        (fun i : Fin n ↦
          Int.natAbs (π i / Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (π j)))) = 1 := by
  -- Route correction: prove primitiveness directly on the raw Nat-gcd surface.
  set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i))
  with hgN
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate π hπ
  have hg_dvd : ∀ j : Fin n, (gN : ℤ) ∣ π j := by
    intro j
    rw [Int.natCast_dvd]
    simpa [hgN] using (Finset.gcd_dvd (b := j) (f := fun k : Fin n ↦ Int.natAbs (π k)) (by simp))
  have hgcd_one :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (π j) / gN) = 1 := by
    -- `Finset.gcd_div_eq_one` applies because one coordinate absolute value is nonzero.
    exact Finset.gcd_div_eq_one (i := i) (by simp) (by simpa using hi)
  -- Rewrite the target gcd pointwise using exact divisibility of each coordinate by the gcd.
  refine (Finset.gcd_congr rfl ?_).trans hgcd_one
  intro j hj
  rw [Int.natAbs_ediv_of_dvd (hg_dvd j)]
  simp

/-- Remark 5.1 (1). For an integral split vector `π`, let
`g = Finset.univ.gcd (fun i ↦ Int.natAbs (π i))`, let `π'_j = π_j / g`, and let
`π₀' = π₀ / g`. When `π ≠ 0`, this is the usual primitive normalization of the split data.
Then the normalized split hull is contained in the original split hull:
`P^(π', π₀') ⊆ P^(π, π₀)`. -/
theorem primitive_split_hull_subset
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    let g : ℤ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i))
    split_hull P (fun j : Fin n ↦ π j / g) (π0 / g) ⊆ split_hull P π π0 := by
  dsimp
  by_cases hπ : π = 0
  · -- In the zero-vector case both split hulls collapse to the same convex hull.
    subst hπ
    have hzero_vec :
        (fun j : Fin n ↦
          (0 : Fin n → ℤ) j /
            Finset.univ.gcd (fun i : Fin n ↦ (((0 : Fin n → ℤ) i).natAbs : ℤ))) =
          (fun _ : Fin n ↦ (0 : ℤ)) := by
      ext j
      simp
    have hleft :
        split_hull P
            (fun j : Fin n ↦
              (0 : Fin n → ℤ) j /
                Finset.univ.gcd (fun i : Fin n ↦ (((0 : Fin n → ℤ) i).natAbs : ℤ)))
            (π0 / Finset.univ.gcd (fun i : Fin n ↦ (((0 : Fin n → ℤ) i).natAbs : ℤ))) =
          convexHull ℝ P := by
      rw [hzero_vec]
      exact zero_split_hull_eq_convexHull P _
    have hright0 : split_hull P (fun _ : Fin n ↦ (0 : ℤ)) π0 = convexHull ℝ P := by
      exact zero_split_hull_eq_convexHull P π0
    intro x hx
    have hx' : x ∈ convexHull ℝ P := by
      rw [hleft] at hx
      exact hx
    change x ∈ split_hull P (fun _ : Fin n ↦ (0 : ℤ)) π0
    rw [hright0]
    exact hx'
  · -- In the nonzero case, normalize by the positive coordinate gcd.
    set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i))
    with hgN
    have hg_pos : 0 < gN := by
      simpa [hgN] using coordinate_gcd_pos π hπ
    have hlower :
        split_branch_lower P (fun j : Fin n ↦ π j / (gN : ℤ)) (π0 / (gN : ℤ)) ⊆
          split_branch_lower P π π0 := by
      intro x hx
      rcases (mem_split_branch_lower_iff.mp hx) with ⟨hxP, hxlower⟩
      refine (mem_split_branch_lower_iff).2 ?_
      constructor
      · exact hxP
      · -- Rescale the normalized inequality and compare the right endpoint via the floor window.
        have hscale := normalized_split_dot_eq_gcd_mul π hπ x
        have hscaled_lower :
            (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x ≤
              (gN : ℝ) * ((π0 / (gN : ℤ) : ℤ) : ℝ) := by
          have hg_nonneg : 0 ≤ (gN : ℝ) := by
            exact_mod_cast (Nat.zero_le gN)
          exact mul_le_mul_of_nonneg_left hxlower hg_nonneg
        have hwindow_real_gN :
            (gN : ℝ) * ((π0 / (gN : ℤ) : ℤ) : ℝ) ≤ (π0 : ℝ) := by
          exact_mod_cast (normalized_split_floor_window_bounds hg_pos π0).1
        have hscale' :
            split_dot π x =
              (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x := by
          simpa [hgN] using hscale
        calc
          split_dot π x =
              (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x := hscale'
          _ ≤ (gN : ℝ) * ((π0 / (gN : ℤ) : ℤ) : ℝ) := hscaled_lower
          _ ≤ (π0 : ℝ) := hwindow_real_gN
    have hupper :
        split_branch_upper P (fun j : Fin n ↦ π j / (gN : ℤ)) (π0 / (gN : ℤ)) ⊆
          split_branch_upper P π π0 := by
      intro x hx
      rcases (mem_split_branch_upper_iff.mp hx) with ⟨hxP, hxupper⟩
      refine (mem_split_branch_upper_iff).2 ?_
      constructor
      · exact hxP
      · -- The normalized upper inequality rescales to the original upper branch.
        have hscale := normalized_split_dot_eq_gcd_mul π hπ x
        have hscaled_upper :
            (gN : ℝ) * (((π0 / (gN : ℤ) : ℤ) : ℝ) + 1) ≤
              (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x := by
          have hg_nonneg : 0 ≤ (gN : ℝ) := by
            exact_mod_cast (Nat.zero_le gN)
          exact mul_le_mul_of_nonneg_left hxupper hg_nonneg
        have hwindow_real_gN :
            (π0 : ℝ) + 1 ≤ (gN : ℝ) * ((((π0 / (gN : ℤ) : ℤ) : ℝ) + 1)) := by
          exact_mod_cast (normalized_split_floor_window_bounds hg_pos π0).2
        have hscale' :
            split_dot π x =
              (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x := by
          simpa [hgN] using hscale
        calc
          (π0 : ℝ) + 1 ≤ (gN : ℝ) * ((((π0 / (gN : ℤ) : ℤ) : ℝ) + 1)) :=
            hwindow_real_gN
          _ ≤ (gN : ℝ) * split_dot (fun j : Fin n ↦ π j / (gN : ℤ)) x :=
            hscaled_upper
          _ = split_dot π x := by
            simpa using hscale'.symm
    have hlower' :
        split_branch_lower
            P
            (fun j : Fin n ↦ π j / Finset.univ.gcd (fun i : Fin n ↦ ((π i).natAbs : ℤ)))
            (π0 / Finset.univ.gcd (fun i : Fin n ↦ ((π i).natAbs : ℤ))) ⊆
          split_branch_lower P π π0 := by
      have hlower' := hlower
      rw [hgN, ← coordinate_gcd_int_cast_eq_nat_gcd_natAbs] at hlower'
      exact hlower'
    have hupper' :
        split_branch_upper
            P
            (fun j : Fin n ↦ π j / Finset.univ.gcd (fun i : Fin n ↦ ((π i).natAbs : ℤ)))
            (π0 / Finset.univ.gcd (fun i : Fin n ↦ ((π i).natAbs : ℤ))) ⊆
          split_branch_upper P π π0 := by
      have hupper' := hupper
      rw [hgN, ← coordinate_gcd_int_cast_eq_nat_gcd_natAbs] at hupper'
      exact hupper'
    -- Once each branch is contained in the corresponding original branch, convex hull monotonicity
    -- gives the split-hull inclusion.
    rw [split_hull, split_hull]
    apply convexHull_mono
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hlower' hx)
    · exact Or.inr (hupper' hx)

/-- Remark 5.1 (2). The split closure is unchanged if one intersects only over primitive
integral split vectors, i.e. those whose coordinate gcd is `1`. -/
theorem split_closure_eq_iInter_primitive_split_hulls
    (P : Set (Fin n → ℝ)) :
    split_closure P =
      ⋂ π : {π : Fin n → ℤ //
          Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i)) = 1},
        ⋂ π0 : ℤ, split_hull P π.1 π0 := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro π
    refine Set.mem_iInter.mpr ?_
    intro π0
    -- A primitive vector cannot be the zero vector, so the split-closure membership applies.
    have hπ_nonzero : π.1 ≠ 0 := by
      intro hzero
      have hgcd_zero :
          Finset.univ.gcd (fun i : Fin _ ↦ Int.natAbs (π.1 i)) = 0 := by
        apply Finset.gcd_eq_zero_iff.mpr
        intro i hi
        simp [hzero]
      have hprimitive_zero := π.2
      rw [hgcd_zero] at hprimitive_zero
      norm_num at hprimitive_zero
    have hx_all := Set.mem_iInter.mp hx
    have hxπ : x ∈ ⋂ π0 : ℤ, split_hull P π.1 π0 := by
      exact hx_all ⟨π.1, hπ_nonzero⟩
    exact Set.mem_iInter.mp hxπ π0
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro π
    refine Set.mem_iInter.mpr ?_
    intro π0
    -- Normalize the current nonzero split vector to a primitive one, then push back through the
    -- hull inclusion from the first part of the remark.
    have hprimitive :
        Finset.univ.gcd
            (fun i : Fin n ↦
              Int.natAbs (π.1 i / Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (π.1 j)))) = 1 := by
      exact normalized_split_vector_gcd_eq_one π.1 π.2
    let πprimitive :
        {π : Fin n → ℤ //
          Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π i)) = 1} :=
      ⟨fun j : Fin n ↦ π.1 j / Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π.1 i)),
        hprimitive⟩
    have hxprimitive : x ∈ ⋂ π0 : ℤ, split_hull P πprimitive.1 π0 := by
      exact Set.mem_iInter.mp hx πprimitive
    have hnormalized :
        x ∈ split_hull P πprimitive.1
          (π0 / Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π.1 i))) := by
      exact Set.mem_iInter.mp hxprimitive
        (π0 / Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π.1 i)))
    have hsubset :
        split_hull P πprimitive.1
            (π0 / Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (π.1 i))) ⊆
          split_hull P π.1 π0 := by
      have hsubset' := primitive_split_hull_subset P π.1 π0
      dsimp at hsubset'
      rw [coordinate_gcd_int_cast_eq_nat_gcd_natAbs] at hsubset'
      simpa [πprimitive] using hsubset'
    exact hsubset hnormalized

end Remark51
